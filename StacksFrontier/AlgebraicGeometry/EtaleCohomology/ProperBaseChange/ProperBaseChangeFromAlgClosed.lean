module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Proper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineInjectiveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingAbsolute

/-!
# The proper base change theorem from Tag 03Q9 and the algebraically closed case for curves

The proof of the proper base change theorem ([Stacks, Tag 095T]) in
`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isProper_of_inputs` consumes
two results: [Stacks, Tag 03Q9] in all degrees, and [Stacks, Tag 0A5E] (extending a separably
closed ground field does not change the cohomology of a torsion sheaf on a proper curve). The
latter follows from its algebraically closed case, statement (7) of [Stacks, Tag 03SC]
(`Stacks.EtaleCohomology.ProperBaseChangeOverAlgClosed`), by topological invariance of the
étale site ([Stacks, Tag 03SI]), which is
`Stacks.EtaleCohomology.etaleCohomologyBaseChangeMap_bijective_of_isSepClosed_of`.

This file records that composite, so that the proper base change theorem and, through it,
[Stacks, Tag 095U] depend on exactly two named inputs.

## Main results

* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper_of_algClosed`
* `Stacks.EtaleCohomology.properDirectImageVanishingStatement_of_algClosed`: [Stacks, Tag 095U]
  from Tag 03Q9, statement (7) of Tag 03SC and the vanishing above degree `2` on proper curves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The proper base change theorem ([Stacks, Tag 095T]) from Tag 03Q9 and statement (7) of
Tag 03SC.** For a proper morphism `f`, cohomology commutes with base change, granted
[Stacks, Tag 03Q9] in all degrees (`h03Q9`) and the algebraically closed case of
[Stacks, Tag 0A5E] (`habc`, Theorem 03SC part (7)); Tag 0A5E itself is obtained from `habc` by
topological invariance. -/
theorem cohomologyCommutesWithBaseChange_of_isProper_of_algClosed
    (h03Q9 : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      (s : GeometricPoint Y) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso ((derivedPushforwardStalkToStrictHenselizationSections (BigEtaleSite.containing Y)
        (BigEtaleSite.contains_containing Y) f s).app ((DerivedCategory.singleFunctor _ 0).obj G)))
    (habc : ProperBaseChangeOverAlgClosed.{u, 0})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    CohomologyCommutesWithBaseChange.{u, 0} f :=
  isIso_etaleAbelianSheafDerivedBaseChange_of_isProper_of_inputs h03Q9
    (fun k k' _ _ _ _ _ _ f _ hdim F hF q ↦
      etaleCohomologyBaseChangeMap_bijective_of_isSepClosed_of habc k k' f hdim F hF q) f

/-- **[Stacks, Tag 095U] from Tag 03Q9 and Tag 03SC.** For every proper morphism whose fibres
have dimension at most `n` and every torsion abelian sheaf, `R^q f_* F = 0` for `q > 2n`, granted
[Stacks, Tag 03Q9] in all degrees (`h03Q9`), statement (7) of [Stacks, Tag 03SC] (`habc`) and
statement (1) of Tag 03SC, the vanishing above degree `2` on proper curves over algebraically
closed fields (`hcurve`): the proper base change theorem is
`cohomologyCommutesWithBaseChange_of_isProper_of_algClosed`, and the induction is
`properDirectImageVanishingStatement_of_curve`. -/
theorem properDirectImageVanishingStatement_of_algClosed
    (h03Q9 : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      (s : GeometricPoint Y) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso ((derivedPushforwardStalkToStrictHenselizationSections (BigEtaleSite.containing Y)
        (BigEtaleSite.contains_containing Y) f s).app ((DerivedCategory.singleFunctor _ 0).obj G)))
    (habc : ProperBaseChangeOverAlgClosed.{u, 0})
    (hcurve : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      (π : X ⟶ Spec (.of k)) [IsProper π], topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞) →
      ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
        ∀ q : ℕ, 2 * 1 < q →
          letI := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
          letI := IsGrothendieckAbelian.hasExt.{u + 1}
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          Subsingleton (Sheaf.H.{u + 1} G q)) :
    ProperDirectImageVanishingStatement.{u} :=
  properDirectImageVanishingStatement_of_curve
    (fun _ _ p _ ↦ cohomologyCommutesWithBaseChange_of_isProper_of_algClosed h03Q9 habc p) hcurve

end Stacks.EtaleCohomology

end
