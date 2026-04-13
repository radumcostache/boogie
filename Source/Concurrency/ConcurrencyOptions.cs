namespace Microsoft.Boogie;

public interface ConcurrencyOptions : CoreOptions
{
  bool InferMoverTypes { get; }
  bool InferMoverTypesBruteForce { get; }
  bool TrustMoverTypes { get; }
  bool TrustSequentialization { get; }
  int TrustLayersDownto { get; }
  int TrustLayersUpto { get; }
  bool TrustNoninterference { get; }
  bool TrustRefinement { get; }
  bool TrustInvariants { get; }
  bool WarnNotEliminatedVars { get; }
}