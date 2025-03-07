type Process(==)

datatype ControlState = 
  | Thinking
  | Hungry
  | Eating

class TicketSystem
{
  var nextTicket: int
  var serving: int 
  var controlStates: map<Process, ControlState>
  var tickets: map<Process, int>

  const processes: set<Process>

  predicate Valid()
    reads this
  {
    controlStates.Keys == tickets.Keys == processes
  }

  constructor (processes: set<Process>)
    ensures Valid()
  {
    this.processes := processes;
    nextTicket, serving := 0, 0;
    controlStates := map p | p in processes :: Thinking;
    tickets := map p | p in processes :: 0;
  }

  method Request(p: Process)
    requires Valid()
    requires p in processes && controlStates[p] == Thinking
    ensures Valid()
    modifies this
  {
    tickets, nextTicket := tickets[p := nextTicket], nextTicket + 1;
    controlStates := controlStates[p := Hungry];
  }

  method Enter(p: Process)
    requires Valid()
    requires p in processes && controlStates[p] == Hungry
    ensures Valid()
    modifies this
  {
    if tickets[p] == serving {
      controlStates := controlStates[p := Eating];
    }
  }

  method Leave(p: Process)
    requires Valid()
    requires p in processes && controlStates[p] == Eating
    ensures Valid()
    modifies this
  {
    controlStates := controlStates[p := Thinking];
    nextTicket := nextTicket + 1;
  }

  // If two processes are both "eating", then they must be the 
  // same process
  lemma MutualExlusion(p: Process, q: Process)
    requires Valid()
    requires p in processes && q in processes 
    requires controlStates[p] == controlStates[q] == Eating
    ensures p == q 
  {
    
  }
}