type Process(==) = int

datatype ControlState = 
  | Thinking
  | Hungry
  | Eating

datatype State = State(nextTicket: int, serving: int, controlStates: map<Process, ControlState>, tickets: map<Process, int>)

const processes: set<Process>

predicate Valid(s: State)
{
  && s.controlStates.Keys == s.tickets.Keys == processes
  && (forall p, q :: 
       p in processes && q in processes && p != q && s.controlStates[p] != Thinking && s.controlStates[q] != Thinking 
       ==> s.tickets[p] != s.tickets[q])
  && s.nextTicket >= s.serving
  && (forall p :: p in processes && s.controlStates[p] != Thinking ==> s.serving <= s.tickets[p] < s.nextTicket)
  && (forall p :: p in processes && s.controlStates[p] == Eating ==> s.tickets[p] == s.serving)
}

lemma MutualExlusion(s: State, p: Process, q: Process)
  requires Valid(s)
  requires p in processes && q in processes 
  requires s.controlStates[p] == s.controlStates[q] == Eating
  ensures p == q 
{
}

predicate Init(s: State)
{
  && s.controlStates.Keys == s.tickets.Keys == processes
  && s.nextTicket == s.serving
  && (forall p :: p in processes ==> s.controlStates[p] == Thinking)
}

predicate Next(s: State, s': State)
{
  && Valid(s)
  && exists p :: p in processes && NextP(s, p, s')
}

lemma Invariance(s: State, s': State)
  ensures Init(s) ==> Valid(s)
  ensures Valid(s) && Next(s, s') ==> Valid(s')
{
}

predicate NextP(s: State, p: Process, s': State)
  requires Valid(s) && p in processes
{
  || Request(s, p, s')
  || Enter(s, p, s')
  || Leave(s, p, s')
}

predicate Request(s: State, p: Process, s': State)
  requires Valid(s) && p in processes
{
  && s.controlStates[p] == Thinking
  && s'.nextTicket == s.nextTicket + 1
  && s'.tickets == s.tickets[p := s.nextTicket] 
  && s'.serving == s.serving
  && s'.controlStates == s.controlStates[p := Hungry]
}

predicate Enter(s: State, p: Process, s': State)
  requires Valid(s) && p in processes
{
  && s.controlStates[p] == Hungry 
  && s.tickets[p] == s.serving
  && s'.tickets == s.tickets 
  && s'.nextTicket == s.nextTicket
  && s'.serving == s.serving
  && ((s.tickets[p] == s.serving && s'.controlStates == s.controlStates[p := Eating]) ||
      (s.tickets[p] != s.serving && s'.controlStates == s.controlStates))
}

predicate Leave(s: State, p: Process, s': State)
  requires Valid(s) && p in processes
{
  && s.controlStates[p] == Eating
  && s'.nextTicket == s.nextTicket
  && s'.tickets == s.tickets 
  && s'.serving == s.serving + 1
  && s'.controlStates == s.controlStates[p := Thinking]
}