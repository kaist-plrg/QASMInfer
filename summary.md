## Research Problem
Quantum computing has been rapidly gaining attention, and so too has its
simulation on classical computers. However, one of the challenges we face today
is ensuring the physically consistent simulational execution of quantum circuits
on classical computers. 'Physically consistent' refers to the simulator's
ability to consistently follow the laws of physics.  Any inconsistency could
lead to incorrect results, which in turn might impact the validity of real-world
applications and research of quantum computing.  This is particularly
significant because a large portion of quantum computing research and
development is currently conducted via simulations, emphasizing the necessity of
their physical consistency.


## Research Approach
Our research seeks to confront the challenge of ensuring physically consistent
execution of quantum circuits through a unique approach.I have developed and
implemented a Quantum Assembly Language (QASM) interpreter, which functions as a
simulator of quantum circuits.
The physical consistency of this interpreter has
been verified using the Coq proof assistant. This verification was accomplished
by proving that the core logic of our implementation strictly follows all the
postulates of quantum physics as outlined in the textbook _"Mathematics of
Quantum Computing: an Introduction"_[1]. This verification ensures the physical
consistency of our approach.

However, quantum circuits in QASM do not merely involve quantum qubit states;
they also incorporate states with classical bits. This necessitates defining the
behavior of the classical program state of the QASM interpreter using the
results of the core logic of quantum physics. A crucial aspect of our research
involves implementing the interaction between classical bits and quantum bits
(i.e., measurement) utilizing the Many-Worlds Interpretation (MWI) of quantum
physics. MWI, proposed by physicist Hugh Everett, posits that
every possible outcome of a quantum measurement actualizes in some "world" or
universe. Essentially, each quantum measurement results in the universe
"splitting" into multiple worlds, each representing a potential outcome[2].

Within our QASM interpreter, we adopt the MWI to manage the measurement of
quantum states. When a measurement is taken on a quantum state, the classical
program state divides into two, thereby creating two parallel "worlds". Each of these
worlds corresponds to a distinct measurement outcome, effectively representing
the inherently probabilistic nature of quantum measurements within our
implementation.

The physical consistency of the core logic, coupled with the incorporation of
the MWI into our QASM interpreter, ensures the overall physical consistency of
our QASM interpreter.


## Value of the Research
The true novelty of our research resides in its verified link between quantum
physics and the execution of quantum circuits. Currently, such a connection is
non-existent, and our research significantly fills this void.

Moreover, our QASM interpreter is equipped to execute both primary operations in
quantum computing - unitary operations and measurements - without any
restrictions. Existing theoretical simulators (excluding shot-based simulators)
either cannot conduct mid-circuit measurements[3] or cannot simulate dynamic
circuits[4]; only permit circuits if the measurement results do not influence the
control flow[5]. Our implementation, however, is free from such constraints.
This means it is the only theoretical simulator capable of executing arbitrary
QASM programs, marking a significant advancement in the field.

## Evaluation
The success of our research can be evaluated by comparing the execution results of certain circuits using existing theoretical simulators (i.e., simulators based on full vector states or density matrices), shot-based simulators, and our own implementation. Theoretical simulators often have constraints, such as the inability to execute dynamic circuits or circuits that contain intermediate measurements.

Shot-based simulators, on the other hand, produce statistical results that are
non-deterministic. In quantum computing, a "shot" refers to a single execution
of a quantum circuit. A shot-based simulator, therefore, runs the quantum
circuit a certain number of times (shots) and provides a statistical result
based on the outcomes of those multiple runs. Hence it is challenging to
pinpoint the expected probability of the circuit due to the inherent randomness
of each run.

Therefore, a comparison between these existing simulators and our own QASM
interpreter will offer a comprehensive understanding of its broad applicability
and superior capabilities in handling executions of diverse quantum circuits.


## Relevance to Existing Work
In the broader context of quantum computing research, an established work known
as QWIRE[6] stands out. QWIRE is a language specifically designed for the
verification of quantum circuits (quantum programs). Its primary focus is on
verifying the circuits or quantum programs themselves, with the goal of proving
certain properties of those circuits.

However, our research stands apart in its focus and objectives. Rather than
verifying the circuits or programs themselves, our work concentrates on the
development of a QASM interpreter with verified physical consistency. This
involves ensuring that the simulation of quantum circuits satisfies the
fundamental postulates of quantum physics. In essence, while QWIRE verifies the
behavior of quantum programs, our research verifies the physical accuracy of the
environment in which these programs are executed.

## Reference
[1] _Mathematics of Quantum Computing: an Introduction_, Wolfgang Scherer, 2019

[2] _The origin of the Everettian heresy_, Stefano Osnaghi, 2009

[3]
  > "statevector": A dense statevector simulation that can sample measurement
  outcomes from ideal circuits with all measurements at end of the circuit. For
  noisy simulations each shot samples a randomly sampled noisy circuit from the
  noise model.

  > "density_matrix": A dense density matrix simulation that may sample
  measurement outcomes from noisy circuits with all measurements at end of the
  circuit.

  > "unitary": A dense unitary matrix simulation of an ideal circuit. This
  simulates the unitary matrix of the circuit itself rather than the evolution
  of an initial quantum state. This method can only simulate gates, it does not
  support measurement, reset, or noise.

  > "superop": A dense superoperator matrix simulation of an ideal or noisy
  circuit. This simulates the superoperator matrix of the circuit itself rather
  than the evolution of an initial quantum state. This method can simulate ideal
  and noisy gates, and reset, but does not support measurement.

  https://qiskit.org/ecosystem/aer/stubs/qiskit_aer.AerSimulator.html

[4] https://quantum-computing.ibm.com/services/programs/docs/runtime/manage/systems/dynamic-circuits/Introduction-To-Dynamic-Circuits

[5]
  > Currently, you can't submit quantum programs that apply operations on qubits
  that have been measured in No Control Flow targets, even if you don't use the
  results to control the program flow. That is, No Control Flow targets don't
  allow mid-circuit measurements.

  https://learn.microsoft.com/en-us/azure/quantum/quantum-computing-target-profiles

[6] _QWIRE: a core language for quantum circuits_, Jennifer Paykin et al, 2017.