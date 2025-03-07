type Process(==) = int

datatype ControlState = 
  | Thinking
  | Hungry
  | Eating

datatype State = State(nextTicket: int, serving: int, controlStates: map<Process, ControlState>, tickets: map<Process, int>)

const processes: set<Process>

ghost predicate Valid(s: State)
{
  && s.controlStates.Keys == s.tickets.Keys == processes
  && (forall p, q :: 
       p in processes && q in processes && p != q && s.controlStates[p] != Thinking && s.controlStates[q] != Thinking 
       ==> s.tickets[p] != s.tickets[q])
  && s.nextTicket >= s.serving
  && (forall p :: p in processes && s.controlStates[p] != Thinking ==> s.serving <= s.tickets[p] < s.nextTicket)
  && (forall p :: p in processes && s.controlStates[p] == Eating ==> s.tickets[p] == s.serving)
}