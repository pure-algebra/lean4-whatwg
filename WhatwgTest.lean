import Gates
import WhatwgTest.Url.InventoryContract
import WhatwgTest.Url.Counterexamples.Inventory
import WhatwgTest.Url.CensusContract
import WhatwgTest.Url.CensusInputContract
import WhatwgTest.Url.Counterexamples.Census
import WhatwgTest.Url.Counterexamples.CensusInput
import WhatwgTest.Infra.Counterexamples.CommaSplit
import WhatwgTest.Infra.ScalarConstructiveContract
import WhatwgTest.Infra.IntegerConstructiveContract
import WhatwgTest.Streams.Counterexamples.Data.Queue
import WhatwgTest.Streams.Counterexamples.Infra.Split
import WhatwgTest.Streams.Data.QueueContract
import WhatwgTest.Streams.Data.QueueAxiomReport
import WhatwgTest.Streams.Counterexamples.Readable.Default
import WhatwgTest.Streams.Readable.DefaultContract
import WhatwgTest.Streams.Readable.DefaultAxiomReport
import WhatwgTest.Streams.Counterexamples.Writable.Default
import WhatwgTest.Streams.Writable.DefaultContract
import WhatwgTest.Streams.Writable.DefaultLaws
import WhatwgTest.Streams.Writable.DefaultAxiomReport
import WhatwgTest.Streams.Writable.LifecycleContract
import WhatwgTest.Streams.Writable.LifecycleAxiomReport
import WhatwgTest.Streams.Writable.InFlightExactContract
import WhatwgTest.Streams.Writable.InFlightExactAxiomReport
import WhatwgTest.Streams.Counterexamples.Writable.InFlightPrecedence
import WhatwgTest.Streams.Counterexamples.Transform.Backpressure
import WhatwgTest.Streams.Transform.BackpressureContract
import WhatwgTest.Streams.Transform.BackpressureLaws
import WhatwgTest.Streams.Transform.BackpressureAxiomReport
import WhatwgTest.Streams.Counterexamples.Piping.Shutdown
import WhatwgTest.Streams.Piping.ShutdownContract
import WhatwgTest.Streams.Piping.ShutdownLaws
import WhatwgTest.Streams.Piping.ShutdownRuns
import WhatwgTest.Streams.Piping.ShutdownAxiomReport
import WhatwgTest.Html.DecideBenchmark
import WhatwgTest.Html.Lattice
import WhatwgTest.Html.Builders
import WhatwgTest.Html.Breakers
import WhatwgTest.Html.Print
import WhatwgTest.Audit.SpecCoverage
import WhatwgTest.Audit.Infra.SpecCoverageRows
import WhatwgTest.Audit.CensusProfileIdentity
import WhatwgTest.Audit.WebIdl.CensusContract
import WhatwgTest.Audit.Ecma262.CensusContract
import WhatwgTest.Audit.AxiomGate

/-!
# Whatwg test battery

The default Lake build imports every admitted contract, attack, and kernel
dependency report through this root. A test file not reachable here is not a
passing gate. The gate command below runs last and inspects the whole
compiled environment.
-/

#whatwg_streams_axiom_gate
