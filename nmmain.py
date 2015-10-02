""" 
Author: Justin Cappos
  Modified by Brent Couvrette to make use of circular logging.
  Modified by Eric Kimbrel to add NAT traversal

Start date: September 3rd, 2008

This is the node manager for Seattle.   It ensures that sandboxes are correctly
assigned to users and users can manipulate those sandboxes safely.

The design goals of this version are to be secure, simple, and reliable (in 
that order).

The node manager has several different threads.

* An advertisement thread (nmadvertise) inserts entries 
  (owner/user public key: node IP address) into Seattle's advertise 
  services so that users and owners can locate their vessels.
* A status thread (nmstatusmonitor) checks the status of vessels and 
  updates statuses in the table used by the API.
* An accepter (nmconnectionmanager) listens for connections (preventing
  simple attacks) and puts them into a list.
* A worker thread (used in the nmconnectionmanager, nmrequesthandler, nmapi)
  handles enacting the appropriate actions given requests from the user.
* The main thread initializes the other threads and monitors them to ensure
  they do not terminate prematurely (restarting them as necessary).
"""

# Nodemanager version information / identification
version = "0.2-alpha-20140714-1434"


# Let's make sure the version of python is supported
import checkpythonversion
checkpythonversion.ensure_python_version_is_supported()

import os
import sys
import daemon
import optparse

# runonce relies on tempfile, whose components utilize the abc library.
# Since we clobber built-ins in repyV2, we have to be sure that any
# python libraries that require the built-ins intact be initialized
# before we import repy code.  See #1273 for more information.
import runonce

from repyportability import *
add_dy_support(locals())


# needed to log OS type / Python version
import platform


# Armon: Prevent all warnings
import warnings
# Ignores all warnings
warnings.simplefilter("ignore")


import time

# Used for the advertise, status, accepter, and worker threads
import threading
import nmadvertise
import nmstatusmonitor
import nmapi
import nmconnectionmanager

# need to initialize the name, key and version (for when we return information
# about us).   Also we need the dictionary of vessel state so that the threads
# can update / read it.
import nmrequesthandler

# For reading in the nodemanager config
import persist

# For getruntime and ostype
import nonportable

# for harshexit
import harshexit

import traceback

import servicelogger


# Armon: To handle user preferrences with respect to IP's and Interfaces
# I will re-use the code repy uses in emulcomm
import emulcomm


from repyportability import *
_context = locals()
add_dy_support(_context)


rsa = dy_import_module("rsa.r2py")

# XXX Can't do a proper module-level dy_import as we import Python's `sha` 
# XXX later. (Whether that import is required is a different question.)
dy_import_module_symbols("sha.r2py")

# XXX advertise.r2py appears unused.
dy_import_module_symbols("advertise.r2py")

sockettimeout = dy_import_module("sockettimeout.r2py")



# Overwrite log() so that Affix debug messages end up in the nodemanager's 
# log file (nodemanager.old or .new in the service vessel directory)
def log(*args):
  chunks = []
  for arg in args:
    chunks.append(str(arg))
  logstring = " ".join(chunks)

  # servicelogger.log will add a trailing newline to the string,
  # remove the existing one (if any).
  if logstring.endswith("\n"):
    servicelogger.log(logstring[:-1])
  else:
    servicelogger.log(logstring)


affix_stack = dy_import_module("affix_stack.r2py")
advertisepipe = dy_import_module("advertisepipe.r2py")



# JAC: Fix for #1000: This needs to be after ALL repyhhelper calls to prevent 
# sha from being replaced
warnings.simplefilter('ignore')
import sha    # Required for the code safety check
warnings.resetwarnings()



# One problem we need to tackle is should we wait to restart a failed service
# or should we constantly restart it.   For advertisement and status threads, 
# I've chosen to wait before restarting...   For worker and accepter, I think
# it's essential to keep restarting them as often as we can...
#
# these variables help us to track when we've started and whether or not we
# should restart

# Store the runtime of the nodemanager when a thread was started last.
# Format: {thread id: start time}
thread_starttime = {}

# thread_waittime is the time to wait before checking a thread's 
# liveliness against the actual list of active threads.
# Format: {thread id: wait time}.
# 
# Within the waittime, the thread check in should_restart_waitable_thread 
# always asserts that the thread does not yet need to be (re)started; 
# every check further increases the waittime (from minwaittime up to 
# maxwaittime) by a constant factor (wait_exponent).
#
# If the thread is eventually found in the list of active threads, 
# and it has been running for a reasonable amount of time 
# (reasonableruntime), the waittime is gradually reduced again 
# by a constant amount (decreaseamount), down to minwaittime.
# This makes it that in case a restart is required sometime later, the 
# new thread instance will see less of a waittime before an actual 
# liveliness check is performed.
thread_waittime = {}

maxwaittime = 300.0
minwaittime = 2.0
wait_exponent = 1.5
reasonableruntime = 30
decreaseamount = .5


# Global variable to store the accepter thread
accepter_thread = None


# Log a liveness message after this many iterations of the main loop
LOG_AFTER_THIS_MANY_ITERATIONS = 600  # every 10 minutes


# Our settings, to be updated from nodeman.cfg
# BUG: what if the data on disk is corrupt?   How do I recover?   What is the
# "right thing"?   I could run nminit again...   Is this the "right thing"?
configuration = {}


# Lock and condition to determine if the accepter thread has started
accepter_state = {'lock': createlock(), 'started': False}


# If TEST_NM is true, then the nodemanager won't worry about another nmmain
# running already.
FOREGROUND = False
TEST_NM = False


# Dict to hold up-to-date nodename and boolean flags to track when to reset
# advertisement and accepter threads (IP mobility)
#   If not behind NAT, name is node's IP:port
#   If behind a NAT, name is a string of the form NAT$UNIQUE_ID:port
node_reset_config = {
  'name': None,
  'reset_advert': False,
  'reset_accepter': False
  }


# We can enable or disable Debug mode in order to get more
# verbose output and raise errors.
DEBUG_MODE = False



def initialize_ip_interface_restrictions(configuration):
  """Initializes emulcomm with network restriction information."""
  # Armon: If networking restrictions are enabled, appropriately 
  # generate the list of usable IP's.
  # If any of our expected entries are missing, assume that 
  # restrictions are not enabled.
  if ('networkrestrictions' in configuration and 
      'nm_restricted' in configuration['networkrestrictions'] and 
      configuration['networkrestrictions']['nm_restricted'] and 
      'nm_user_preference' in configuration['networkrestrictions']):
    # Setup emulcomm to generate an IP list for us, setup the flags
    emulcomm.user_ip_interface_preferences = True
    
    # Add the specified IPs/Interfaces
    emulcomm.user_specified_ip_interface_list = configuration['networkrestrictions']['nm_user_preference']



def should_start_waitable_thread(threadid, threadname):
  """
  <Purpose>
    Determine if a thread (identified by its ID and name) should be 
    started, or if we think it is running already. There are two 
    indications for finding the running status of a thread:
    Its `threadid` should exist as key in the `thread_starttime` and 
    `thread_waittime` dicts (i.e. our bookkeeping in this function), 
    and its `threadname`, set when the thread was `__init__`'ed, is 
    found in the list of Thread objects per `threading.enumerate()`.

  <Arguments>
    threadid: A shorthand identifier for a thread. E.g., "advert", "status".
    threadname: The Pyhton thread's name, as set in the respective 
      implementation of the Thread class, e.g. nmadvertise.advertthread.

  <Exceptions>
    None.

  <Side Effects>
    For any threads that we think have not been started, the thread status 
    dicts are modified.
    When asked about the advert thread in particular, the node_reset_config 
    dict is modified to turn off the "reset needed" flag.

  <Returns>
    True if we think the thread at question should be started by our caller.
    False if we don't think the thread should be started.
  """
  if threadid not in thread_starttime:
    # The threadid missing from the starttime dict indicates the thread 
    # isn't running yet. Init the thread's starttime and waittime entries.
    # Note that we initialize the starttime to 0.0 just so that this 
    # threadid exists as a key in the dict; the actual starttime 
    # is set later by our caller after they have called the actual 
    # `thread.start()` method. (See `start_advert_thread` for example.)
    thread_waittime[threadid] = minwaittime
    thread_starttime[threadid] = 0.0

  # If asking about advert thread and node_reset_config specifies to reset 
  # it, clear the reset_advert flag and then tell our caller to start the 
  # advert thread.
  if threadid == 'advert' and node_reset_config['reset_advert'] is True:
    node_reset_config['reset_advert'] = False
    return True

  # Don't bother to check the actual list of running threads unless 
  # the thread has already had its starttime updated, and has been 
  # running for more than its prescribed waittime.
  # Just return False to say it shouldn't be restarted just yet.
  thread_runtime = nonportable.getruntime() - thread_starttime[threadid] 
  if thread_starttime[threadid] and thread_runtime < thread_waittime[threadid]:
    return False

  # OK, the thread appears to have run "long enough" now. See if we find 
  # `threadname` among the list of all living Thread objects.
  if is_thread_started(threadname):
    # Yes, our thread is running now. If it has been running for a 
    # reasonable time, let's reduce the wait time.
    if thread_runtime > reasonableruntime:
      thread_waittime[threadid] = max(minwaittime, thread_waittime[threadid]-decreaseamount)
    # Anyway, we definitley need not (re)start this thread.
    return False
  else:
    # Our `threadname` was not among the Thread objects. Our caller 
    # needs to start it.
    return True



def started_waitable_thread(threadid):
  """
  <Purpose>
    Update a thread's status information in the `thread_starttime` and 
    `thread_waittime` dicts. This should be done after the thread's 
    `start()` method has been called, so that `should_start_waitable_thread` 
    can obtain current status info.

  <Arguments>
    threadid: A shorthand identifier for a thread. E.g., "advert", "status".

  <Exceptions>
    None.

  <Side Effects>
    Updates thread status info dicts.

  <Returns>
    None.
  """
  # Set the thread starttime, so as to indicate that the actual 
  # `thread.start()` method has been called by our caller.
  thread_starttime[threadid] = nonportable.getruntime()

  # Also increase the waittime if we happen to check for this thread's 
  # liveliness again very soon.
  thread_waittime[threadid] = min(maxwaittime, thread_waittime[threadid] ** wait_exponent)



# Set the accepter thread
def set_accepter(accepter):
  global accepter_thread
  accepter_state['lock'].acquire(True)
  accepter_thread = accepter

  if DEBUG_MODE:
    servicelogger.log("[DEBUG] Accepter Thread has been set...")
  accepter_state['lock'].release()


  
# Has the accepter thread started?
def is_accepter_started():
  accepter_state['lock'].acquire(True)
  result = accepter_thread is not None and accepter_thread.isAlive()
  accepter_state['lock'].release()
  return result



# Flags for whether to use Affix
affix_enabled = True


# Store the original Repy API calls.
old_getmyip = getmyip
old_listenforconnection = listenforconnection
old_timeout_listenforconnection = sockettimeout.timeout_listenforconnection


def enable_affix(affix_string):
  """
  <Purpose>
    Overload the listenforconnection() and getmyip() API call 
    if Affix is enabled.

  <Arguments>
    None

  <SideEffects>
    Original listenforconnection() and getmyip() gets overwritten.

  <Exceptions>
    None
  """
  # If Affix is not enabled, we just return.
  if not affix_enabled:
    return

  global timeout_listenforconnection
  global getmyip

  # Create my affix object and overwrite the listenforconnection
  # and the getmyip call.
  nodemanager_affix = affix_stack.AffixStack(affix_string)

  # Create a new timeout_listenforconnection that wraps a normal
  # Affix socket with timeout_server_socket.
  def new_timeout_listenforconnection(localip, localport, timeout):
    sockobj = nodemanager_affix.listenforconnection(localip, localport)
    return sockettimeout.timeout_server_socket(sockobj, timeout)

  # Overload the two functionalities with Affix functionalities
  # that will be used later on.
  timeout_listenforconnection = new_timeout_listenforconnection
  getmyip = nodemanager_affix.getmyip

  servicelogger.log('[INFO] Nodemanager now using Affix string: ' + affix_string)



def start_accepter():
  global accepter_thread

  # do this until we get the accepter started...
  while True:
    if not node_reset_config['reset_accepter'] and is_accepter_started():
      # we're done, return the name!
      return myname_port
    else:
      # If we came here because a reset was initiated, kill the old 
      # accepter thread server socket before starting a new one.
      try:
        accepter_thread.close_serversocket()
        servicelogger.log("Closed previous accepter thread server socket.")
      except:
        # There was no accepter_thread, or it couldn't .close_serversocket().
        # No problem -- this means nothing will be in the way of the new 
        # serversocket.
        pass

      # Use getmyip() to find the IP address the nodemanager should 
      # listen on for incoming connections. This will work correctly 
      # if IP/interface preferences have been set.
      # We only want to call getmyip() once rather than in the loop 
      # since this potentially avoids rebuilding the allowed IP 
      # cache for each possible port
      bind_ip = getmyip()

      # Attempt to have the nodemanager listen on an available port.
      # Once it is able to listen, create a new thread and pass it the socket.
      # That new thread will be responsible for handling all of the incoming connections.     
      for possibleport in configuration['ports']:
        try:
          # Use a Repy socket for listening. This lets us override 
          # the listenforconnection function with a version using an 
          # Affix stack easily; furthermore, we can transparently use 
          # the Repy sockettimeout library to protect against malicious 
          # clients that feed us endless data (or no data) to tie up 
          # the connection.
          try:
            serversocket = timeout_listenforconnection(bind_ip, possibleport, 10)
          except (AlreadyListeningError, DuplicateTupleError), e:
            # These are rather dull errors that will result in us 
            # trying a different port. Don't print a stack trace.
            servicelogger.log("[ERROR]: listenforconnection for address " + 
                bind_ip + ":" + str(possibleport) + " failed with error '" + 
                repr(e) + "'. Retrying.")
            continue

          # Assign the nodemanager name.
          # We re-retrieve our address using getmyip as we may now be using
          # a zenodotus name instead.
          myname_port = str(getmyip()) + ":" + str(possibleport)

          # If there is no error, we were able to successfully start listening.
          # Create the thread, and start it up!
          accepter = nmconnectionmanager.AccepterThread(serversocket)
          accepter.start()
          
          # Now that we created an accepter, let's use it!          
          set_accepter(accepter)

          # MOSHE: Is this thread safe!?          
          # Now that waitforconn has been called, unset the accepter reset flag
          node_reset_config['reset_accepter'] = False
        except Exception, e:
          # print bind_ip, port, e
          servicelogger.log("[ERROR] setting up nodemanager serversocket " + 
              "on address " + bind_ip + ":" + str(possibleport) + ": " + 
              repr(e))
          servicelogger.log_last_exception()
        else:
          break

      else:
        # We exhausted the list of possibleport's to no avail. 
        # Pause to avoid busy-waiting for the problem to go away.
        servicelogger.log("[ERROR]: Could not create serversocket. Sleeping for 30 seconds.")
        time.sleep(30)

    # check infrequently
    time.sleep(configuration['pollfrequency'])



def is_thread_started(threadname):
  """Check if `threadname` is in the list of active Thread objects;
  return True if so, and False otherwise."""
  for thread in threading.enumerate():
    if threadname in str(thread):
      return True
  else:
    return False



def start_worker_thread(sleeptime):
  if not is_thread_started(nmconnectionmanager.worker_thread_name):
    # start the WorkerThread and set it to a daemon.   I think the daemon 
    # setting is unnecessary since I'll clobber on restart...
    workerthread = nmconnectionmanager.WorkerThread(sleeptime)
    workerthread.setDaemon(True)
    workerthread.start()



def start_advert_thread(vesseldict, myname, nodekey):
  if should_start_waitable_thread('advert', nmadvertise.thread_name):
    # start the AdvertThread and set it to a daemon.   I think the daemon 
    # setting is unnecessary since I'll clobber on restart...
    advertthread = nmadvertise.advertthread(vesseldict, nodekey)
    nmadvertise.myname = myname
    advertthread.setDaemon(True)
    advertthread.start()
    started_waitable_thread('advert')



def start_status_thread(vesseldict, sleeptime):
  if should_start_waitable_thread('status', nmstatusmonitor.thread_name):
    # start the StatusThread and set it to a daemon.   I think the daemon 
    # setting is unnecessary since I'll clobber on restart...
    statusthread = nmstatusmonitor.statusthread(vesseldict, sleeptime, nmapi)
    statusthread.setDaemon(True)
    statusthread.start()
    started_waitable_thread('status')



def write_out_nmmain_pid_for_test_mode():
  """If in test mode, write out our PID to a file so that our caller 
  knows how to stop us when the tests are over."""
  nodemanager_pid = os.getpid()
  servicelogger.log("[INFO]: Running nodemanager in test mode with PID " + str(nodemanager_pid))
  nodeman_pid_file = open(os.path.join(os.getcwd(), 'nodemanager.pid'), 'w')
  
  try:
    nodeman_pid_file.write(str(nodemanager_pid))
  finally:
    nodeman_pid_file.close()



def log_seattle_version_and_platform_info():
  """Log information about the version of Seattle, and what 
  OS and platform we are running on."""

  servicelogger.log('[INFO]: This is Seattle release "' + version + "'") 

  # Feature add for #1031: Log information about the system in the nm log...
  servicelogger.log('[INFO]:platform.python_version(): "' + 
      str(platform.python_version())+'"')
  servicelogger.log('[INFO]:platform.platform(): "' + 
      str(platform.platform())+'"')

  uname_logstring_prefix = '[INFO]:platform.uname(): '
  # uname on Android only yields 'Linux', let's be more specific.
  try:
    import android
    uname_logstring += 'Android / ' 
  except ImportError:
    pass
  servicelogger.log(uname_logstring_prefix + '"' + str(platform.uname()) + '"')




# lots of little things need to be initialized...   
def main():
  global configuration

  if not FOREGROUND:
    # Background ourselves.
    daemon.daemonize()

  if TEST_NM:
    # In test mode, store our PID in a file for our caller
    write_out_nmmain_pid_for_test_mode()
  else:
    # Ensure that only one nodemanager instance is running at a time.
    # Depending on the lock state and OS/platform, `gotlock` may be 
    # an integer PID, True, or False.
    gotlock = runonce.getprocesslock("seattlenodemanager")

    if gotlock == True:
      # I got the lock.   All is well...
      pass
    else:
      if gotlock:
        servicelogger.log("[ERROR]:Another node manager process (pid: " + 
            str(gotlock) + ") is running")
      else:
        servicelogger.log("[ERROR]:Another node manager process is running")
      return

  log_seattle_version_and_platform_info()

  # I'll grab the necessary information first...
  servicelogger.log("[INFO]:Loading config")
  # BUG: Do this better?   Is this the right way to engineer this?
  configuration = persist.restore_object("nodeman.cfg")
  
  # Armon: initialize the network restrictions
  initialize_ip_interface_restrictions(configuration)

  # Enable Affix and overload various Repy network API calls 
  # with Affix-enabled calls.
  # Use the node's publickey to generate a name for our node.
  mypubkey = rsa.rsa_publickey_to_string(configuration['publickey']).replace(" ", "")
  affix_stack_name = sha_hexhash(mypubkey)

  enable_affix('(CoordinationAffix)(MakeMeHearAffix)(NamingAndResolverAffix,' + 
      affix_stack_name + ')')

  # get the external IP address...
  myip = None
  while True:
    try:
      # Try to find our external IP.
      myip = emulcomm.getmyip()
    except Exception, e: # Replace with InternetConnectivityError ?
      # If we aren't connected to the internet, emulcomm.getmyip() raises this:
      if len(e.args) >= 1 and e.args[0] == "Cannot detect a connection to the Internet.":
        # So we try again.
        pass
      else:
        # It wasn't emulcomm.getmyip()'s exception. re-raise.
        raise
    else:
      # We succeeded in getting our external IP. Leave the loop.
      break
    time.sleep(0.1)

  vesseldict = nmrequesthandler.initialize(myip, configuration['publickey'], version)

  # Start accepter, store current node name
  node_reset_config['name'] = start_accepter()
  
  #send our advertised name to the log
  servicelogger.log('myname = ' + node_reset_config['name'])

  # Start worker thread...
  start_worker_thread(configuration['pollfrequency'])

  # Start advert thread...
  start_advert_thread(vesseldict, node_reset_config['name'], configuration['publickey'])

  # Start status thread...
  start_status_thread(vesseldict, configuration['pollfrequency'])


  # we should be all set up now.   

  servicelogger.log("[INFO]:Started")

  # I will count my iterations through the loop so that I can log a message
  # periodically.   This makes it clear I am alive.
  times_through_the_loop = 0


  # BUG: Need to exit all when we're being upgraded
  while True:

    if not is_accepter_started():
      servicelogger.log("[WARN]:Accepter thread requires restart.")
      node_reset_config['reset_accepter'] = True
 
    if not is_thread_started(nmconnectionmanager.worker_thread_name):
      servicelogger.log("[WARN]:Worker thread requires restart.")
      start_worker_thread(configuration['pollfrequency'])

    if should_start_waitable_thread('advert', nmadvertise.thread_name):
      servicelogger.log("[WARN]:Advert thread requires restart.")
      start_advert_thread(vesseldict, node_reset_config['name'], configuration['publickey'])

    if should_start_waitable_thread('status', nmstatusmonitor.thread_name):
      servicelogger.log("[WARN]:Status monitoring thread requires restart.")
      start_status_thread(vesseldict, configuration['pollfrequency'])

    if not TEST_NM and not runonce.stillhaveprocesslock("seattlenodemanager"):
      servicelogger.log("[ERROR]:The node manager lost the process lock...")
      harshexit.harshexit(55)

    # Check for IP address changes.
    # When using Affix, the NamingAndResolverAffix takes over this.
    if not affix_enabled:
      current_ip = None
      while True:
        try:
          current_ip = emulcomm.getmyip()
        except Exception, e:
          # If we aren't connected to the internet, emulcomm.getmyip() raises this:
          if len(e.args) >= 1 and e.args[0] == "Cannot detect a connection to the Internet.":
            # So we try again.
            pass
          else:
            # It wasn't emulcomm.getmyip()'s exception. re-raise.
            raise
        else:
          # We succeeded in getting our external IP. Leave the loop.
          break
      time.sleep(0.1)

      # If ip has changed, then restart the advertisement and accepter threads.
      if current_ip != myip:
        servicelogger.log('[WARN]:Node IP has changed from ' + str(myip) +
          ' to ' + str(current_ip) + '.')
        myip = current_ip

        # Restart the accepter thread and update nodename in node_reset_config
        node_reset_config['reset_accepter'] = True

        # Restart the advertisement thread
        node_reset_config['reset_advert'] = True
        start_advert_thread(vesseldict, node_reset_config['name'], configuration['publickey'])


    
    # If the reset accepter flag has been turned on, we call start_accepter
    # and update our name. 
    if node_reset_config['reset_accepter']:
      node_reset_config['name'] = start_accepter()


    time.sleep(configuration['pollfrequency'])

    # if I've been through the loop enough times, log this...
    times_through_the_loop += 1
    if times_through_the_loop % LOG_AFTER_THIS_MANY_ITERATIONS == 0:
      servicelogger.log("[INFO]: node manager is alive...")



def parse_arguments():
  """
  Parse all the arguments passed in through the command
  line for the nodemanager. This way in the future it
  will be easy to add and remove options from the
  nodemanager.
  """

  # Create the option parser
  parser = optparse.OptionParser(version="Seattle " + version)

  # Add the --foreground option.
  parser.add_option('--foreground', dest='foreground',
      action='store_true', default=False,
      help="Run the nodemanager in foreground instead of daemonizing it.")


  # Add the --test-mode option.
  parser.add_option('--test-mode', dest='test_mode',
      action='store_true', default=False,
      help="Run the nodemanager in test mode.")
                    
  # Parse the argumetns.
  options, args = parser.parse_args()

  # Set some global variables.
  global FOREGROUND
  global TEST_NM


  # Analyze the options
  if options.foreground:
    FOREGROUND = True

  if options.test_mode:
    TEST_NM = True
    


if __name__ == '__main__':
  """
  Start up the nodemanager. We are going to setup the servicelogger,
  then parse the arguments and then start everything up.
  """

  # Initialize the service logger.   We need to do this before calling main
  # because we want to print exceptions in main to the service log
  servicelogger.init('nodemanager')

  # Parse the arguments passed in the command line to set
  # different variables.
  parse_arguments()


  # Armon: Add some logging in case there is an uncaught exception
  try:
    main()
  except Exception, e:
    # If the servicelogger is not yet initialized, this will not be logged.
    servicelogger.log_last_exception()

    # Since the main thread has died, this is a fatal exception,
    # so we need to forcefully exit
    harshexit.harshexit(15)

