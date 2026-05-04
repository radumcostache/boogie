using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
  public class CivlRewriter
  {
    public static void Transform(ConcurrencyOptions options, CivlTypeChecker civlTypeChecker)
    {
      var linearTypeChecker = civlTypeChecker.linearTypeChecker;
      Program program = linearTypeChecker.program;

      // Store the original declarations that should be removed after desugaring below.
      var origActionDecls = program.TopLevelDeclarations.OfType<ActionDecl>();
      var origActionImpls = program.TopLevelDeclarations.OfType<Implementation>()
        .Where(impl => impl.Proc is ActionDecl);
      var origYieldProcs = program.TopLevelDeclarations.OfType<YieldProcedureDecl>();
      var origYieldImpls = program.TopLevelDeclarations.OfType<Implementation>()
        .Where(impl => impl.Proc is YieldProcedureDecl);
      var origYieldInvariants = program.TopLevelDeclarations.OfType<YieldInvariantDecl>();
      var originalDecls = origActionDecls.Union<Declaration>(origActionImpls).Union(origYieldProcs)
        .Union(origYieldImpls).Union(origYieldInvariants).ToHashSet();

      var decls = new List<Declaration>();

      // Gate sufficiency checks
      Action.AddGateSufficiencyCheckers(civlTypeChecker, decls);

      civlTypeChecker.originalImpls.ForEach(x =>
      {
          decls.AddRange(new Declaration[] { x });

      });

      // Commutativity checks
      if (!options.TrustMoverTypes)
      {
        MoverCheck.AddCheckers(civlTypeChecker, decls);
      }

      decls.AddRange(civlTypeChecker.precomputedCheckers);
      
      // Remove original declarations and add new checkers generated above
      program.RemoveTopLevelDeclarations(x => originalDecls.Contains(x));
      program.AddTopLevelDeclarations(decls);
      
      linearTypeChecker.EraseLinearAnnotations();
    }
  }
}