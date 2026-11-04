module
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.Localization.SimultaneousTrivialization

/-!
# CurveConstantCoefficientsUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients`, stated
as separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp

/-- **A finite constant abelian sheaf is constructible.** Transported to the small étale site of
Tag 021B it is again the constant sheaf (`CategoryTheory.equivCommuteConstant'`), whose restriction
to every object is the constant sheaf there with the same finite value, so it is finite locally
constant, hence constructible. -/
theorem isConstructibleEtaleAbelianSheaf_constantSheaf_general (X : Scheme.{u})
    (A : AddCommGrpCat.{max (u + 1) r}) [Finite A] :
    _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, r}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj A) := by
  let B := BigEtaleSite.containing X
  let hX := BigEtaleSite.contains_containing X
  let J := SmallEtale.topology B X hX
  have hlim : ∀ T : (X.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow T (SmallEtale.toEtaleSite B X hX).op) AddCommGrpCat.{max (u + 1) r} :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have hT : IsTerminal ((SmallEtale.toEtaleSite B X hX).obj (SmallEtale.final B X hX)) :=
    have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
      ⟨fun _ => inferInstance⟩
    MorphismProperty.Over.mkIdTerminal _ _
  let e : (SmallEtale.sheafEquiv B X hX AddCommGrpCat.{max (u + 1) r}).inverse.obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj A) ≅
      (constantSheaf J AddCommGrpCat.{max (u + 1) r}).obj A :=
    ((equivCommuteConstant' J AddCommGrpCat.{max (u + 1) r} X.smallEtaleTopology
      (SmallEtale.toEtaleSite B X hX) (SmallEtale.finalIsTerminal B X hX) hT).app A).symm
  have hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant J
      ((constantSheaf J AddCommGrpCat.{max (u + 1) r}).obj A) :=
    ⟨fun U => ⟨PUnit, fun _ => U, fun _ => 𝟙 U, Stacks.ConstantSheaf.sieve_ofArrows_id_mem J U,
      fun _ => ⟨A, inferInstance, ⟨(Stacks.ConstantSheaf.overPullbackConstantSheafIso J
        AddCommGrpCat.{max (u + 1) r} U).app A⟩⟩⟩⟩
  have hF' : Stacks.ConstantSheaf.IsFiniteLocallyConstant J
      ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{max (u + 1) r}).inverse.obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj A)) :=
    Stacks.ConstantSheaf.IsFiniteLocallyConstant.of_iso J e.symm hF
  exact isConstructibleAbelianSheaf_of_isFiniteLocallyConstant B _ _

/-- **The eight statements of Situation 0A52 for one abelian sheaf** ([Stacks, Tag 0A52],
statements 0A53 to 0A5A), on Mathlib's small étale site with coefficients in
`AddCommGrpCat.{max (u + 1) r}` and cohomology Mathlib's `Sheaf.H`. For a scheme `X` with
structure morphism `π : X ⟶ Spec k` to the spectrum of a field and an abelian sheaf `F` on
`X_étale`, "statements (0A53) -- (0A5A) hold for `F`" is the conjunction of

1. `H^q(X, F) = 0` for `q > 2`;
2. `H^q(X, F) = 0` for `q > 1` if `X` is affine;
3. `H^q(X, F) = 0` for `q > 1` if `p = char(k) > 0` and `F` is `p`-power torsion;
4. `H^q(X, F)` is finite if `F` is constructible and torsion prime to `char(k)`;
5. `H^q(X, F)` is finite if `X` is proper and `F` is constructible;
6. `H^q(X, F) ⟶ H^q(X_{k'}, F|_{X_{k'}})` is bijective for every extension `k'/k` of
   algebraically closed fields if `F` is torsion prime to `char(k)`;
7. the same map is bijective for every such `k'` if `X` is proper;
8. `H^2(X, F) ⟶ H^2(U, F)` is surjective for every open `U ⊆ X`.

The source states these in Situation 0A52, for `k` algebraically closed, `X` separated of finite
type over `k` of dimension at most one and `F` torsion; those standing hypotheses are those of the
results that conclude this predicate, not part of it. "Torsion prime to `char(k)`" is read with
the exponential characteristic, so that it is no condition in characteristic zero, and
constructibility is `_root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf` (Tag 03RW
part (2)). -/
def CurveTorsionStatementsGeneral {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) : Prop :=
  (∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H.{max (u + 1) r} F q)) ∧
    (IsAffine X → ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{max (u + 1) r} F q)) ∧
    (0 < ringChar k →
      Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology (ringChar k) F →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{max (u + 1) r} F q)) ∧
    (_root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, r} F →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
      ∀ q : ℕ, Finite (Sheaf.H.{max (u + 1) r} F q)) ∧
    (_root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, r} F → IsProper π →
      ∀ q : ℕ, Finite (Sheaf.H.{max (u + 1) r} F q)) ∧
    (∀ (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'],
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) F →
      ∀ q : ℕ, Function.Bijective (etaleCohomologyRestrictionMap.{u, r, max (u + 1) r}
        (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k k')))) F q)) ∧
    (IsProper π → ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'],
      ∀ q : ℕ, Function.Bijective (etaleCohomologyRestrictionMap.{u, r, max (u + 1) r}
        (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k k')))) F q)) ∧
    (∀ U : X.Opens, Function.Surjective
      (etaleCohomologyRestrictionMap.{u, r, max (u + 1) r} U.ι F 2))

namespace TorsionModules

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

end TorsionModules

end Stacks.EtaleCohomology
