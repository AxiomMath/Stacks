module

public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence
import StacksCore.Tactic.StacksAttribute

/-!
# Convergence of the truncation tower over an acyclic covering class

Let `(C, O)` be a ringed site and `E` an object of the unbounded derived category of `O`-modules.
Suppose a class `B` of objects of `C` is large enough to cover every object, and that every
cohomology sheaf of `E` has vanishing higher cohomology on every member of `B`. Then the
canonical map from `E` to the derived limit of its truncation tower `n ↦ τ_{≥ -n} E` is an
isomorphism.

This is Tag 0D6P with `d = 0`, at independent site, ring and module universes, deduced directly
from Tag 0D6M.

The cofinal system of coverings of `V ∈ B` is all coverings whose members lie in `B`; it is
cofinal because any covering is refined by binding it with `B`-coverings of its own members,
whose generated sieve covers by transitivity of the topology. The degree bound of Tag 0D6M is
taken to be identically `0`, so its vanishing hypothesis asks exactly for cohomology in positive
degrees, which is the hypothesis here.

## Main results

* `Stacks.Cohomology.AcyclicCover.exists_preZeroHypercover_of_hasEnoughObjects`: a site with
  enough `B`-objects has, over every object, a `B`-covering presented as a `PreZeroHypercover`
  indexed in the maximum of the two site universes.
* `Stacks.Cohomology.AcyclicCover.exists_cover_nonempty_hom_of_hasEnoughObjects`: on such a site
  the `B`-coverings of an object are cofinal — every covering family of it is refined by one
  whose members have `B`.
* `Stacks.Cohomology.CofinalCoveringSystem.ofHasEnoughObjects`: that cofinality packaged as a
  `Stacks.Cohomology.CofinalCoveringSystem`.
* `Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic`: the
  convergence criterion.

## Implementation notes

A covering family is represented by a `PreZeroHypercover`, which is a covering exactly when the
sieve it generates lies in the topology, as in Tag 0D6M. `GrothendieckTopology.HasEnoughObjects`
indexes its coverings in the morphism universe `v` of the site alone, whereas Tag 0D6M asks for
`max u v`; the bridge is `CategoryTheory.PreZeroHypercover.reindex` along `Equiv.ulift`, which
leaves the generated presieve unchanged.

The vanishing hypothesis is phrased with `CategoryTheory.Functor.rightDerived` of evaluation;
`Stacks.Cohomology.moduleCohomology`, the form Tag 0D6M uses, is definitionally that, the
additivity instance being a proposition.

Because the predicate "`L` is a derived limit" does not remember the first arrow of its
distinguished triangle, the statement is given for a presentation of that triangle together with
a map whose composites with all product projections are the canonical truncation maps; this pins
down the canonical map of the source. This matches Tag 0D6M exactly.

## References

* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.AcyclicCover

universe u v wRing wModule

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A site with enough `B`-objects has, over every object, a covering by `B`-objects presented as
a `PreZeroHypercover` indexed in `max u v`. -/
lemma exists_preZeroHypercover_of_hasEnoughObjects {B : ObjectProperty C}
    (hB : J.HasEnoughObjects B) (U : C) :
    ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J U ∧ ∀ i, B (𝒰.X i) := by
  obtain ⟨I, Ui, f, hf, hBi⟩ := hB U
  refine ⟨PreZeroHypercover.reindex ⟨I, Ui, f⟩ (Equiv.ulift (α := I)), ?_, fun i => hBi _⟩
  rw [PreZeroHypercover.sieve₀_reindex]
  exact hf

/-- **On a site with enough `B`-objects the `B`-coverings of an object are cofinal.** Every
covering family `𝒰` of `V` is refined by a covering family of `V` all of whose members have `B`:
cover each `𝒰.X i` by `B`-objects and bind, the bound family refining `𝒰` by the covering
morphisms of the chosen covers and covering `V` by transitivity of the topology. -/
lemma exists_cover_nonempty_hom_of_hasEnoughObjects {B : ObjectProperty C}
    (hB : J.HasEnoughObjects B) {V : C} (𝒰 : PreZeroHypercover.{max u v} V)
    (h𝒰 : 𝒰.sieve₀ ∈ J V) :
    ∃ 𝒱 : PreZeroHypercover.{max u v} V,
      (𝒱.sieve₀ ∈ J V ∧ ∀ i, B (𝒱.X i)) ∧ Nonempty (𝒱.Hom 𝒰) := by
  classical
  choose F hF using fun i : 𝒰.I₀ =>
    exists_preZeroHypercover_of_hasEnoughObjects hB (𝒰.X i)
  refine ⟨𝒰.bind F, ⟨?_, fun ij => (hF ij.1).2 ij.2⟩,
    ⟨fun ij => ij.1, fun ij => (F ij.1).f ij.2, fun ij => rfl⟩⟩
  have hbind : Sieve.generate
      (Presieve.bindOfArrows 𝒰.X 𝒰.f (fun i => (F i).presieve₀)) ∈ J V :=
    J.bindOfArrows h𝒰 (fun i => by
      simpa [PreZeroHypercover.presieve₀] using (hF i).1)
  simpa [PreZeroHypercover.bind, PreZeroHypercover.sieve₀,
    Presieve.bindOfArrows_ofArrows] using hbind

variable (O : Sheaf J RingCat.{wRing})
  [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [EnoughInjectives (SheafOfModules.{wModule} O)]

omit [EnoughInjectives (SheafOfModules.{wModule} O)] [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}] in
/-- Evaluation of sheaves of `O`-modules at an object of the site is additive. -/
lemma evaluation_additive (V : C) :
    (SheafOfModules.evaluation O (.op V) :
      SheafOfModules.{wModule} O ⥤ ModuleCat.{wModule} (O.obj.obj (.op V))).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

attribute [local instance] evaluation_additive

/-- **Stacks Project, Tag 0D6P with `d = 0`.** If the cohomology sheaves of `E` have no higher
cohomology on the members of a class of objects covering the site, then the canonical map from
`E` to every derived limit of its truncation tower from below is an isomorphism. -/
theorem isIso_to_isDerivedLimit_truncGETower_of_acyclic
    (E : DerivedCategory (SheafOfModules.{wModule} O))
    (B : ObjectProperty C)
    (hB : J.HasEnoughObjects B)
    (hvan : ∀ V : C, B V → ∀ p : ℕ, 0 < p → ∀ q : ℤ,
      IsZero (((SheafOfModules.evaluation O (.op V)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).obj E)))
    [HasProduct fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩]
    (L : DerivedCategory (SheafOfModules.{wModule} O))
    (c : E ⟶ L)
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk p (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).map
            (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{wModule} O)))
    (hc : ∀ n : ℕ, c ≫ p ≫
      Pi.π (fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} O) E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  classical
  refine isIso_to_isDerivedLimit_truncationGETower
    O E B (exists_preZeroHypercover_of_hasEnoughObjects hB) (fun _ _ _ => 0)
    (fun V _ => {𝒰 | 𝒰.sieve₀ ∈ J V ∧ ∀ i, B (𝒰.X i)})
    (fun _ _ _ h𝒰 => h𝒰.1) ?_
    (by
      intro V _ 𝒰 h𝒰 i r m hm
      exact hvan (𝒰.X i) (h𝒰.2 i) r (by exact_mod_cast hm) (m - (r : ℤ)))
    L c p δ hL hc
  intro V _ 𝒰 h𝒰
  exact exists_cover_nonempty_hom_of_hasEnoughObjects hB 𝒰 h𝒰

end Stacks.Cohomology.AcyclicCover

namespace Stacks.Cohomology.CofinalCoveringSystem

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **A site with enough `B`-objects carries a cofinal system of `B`-coverings over every
object**: the distinguished coverings of `V` are those covering families of `V` whose members all
have `B`, and they are cofinal by
`Stacks.Cohomology.AcyclicCover.exists_cover_nonempty_hom_of_hasEnoughObjects`. -/
def ofHasEnoughObjects {B : ObjectProperty C} (hB : J.HasEnoughObjects B) (V : C) :
    CofinalCoveringSystem J V where
  cov := {𝒰 | 𝒰.sieve₀ ∈ J V ∧ ∀ i, B (𝒰.X i)}
  isCover _ h := h.1
  cofinal 𝒰 h𝒰 := AcyclicCover.exists_cover_nonempty_hom_of_hasEnoughObjects hB 𝒰 h𝒰

end Stacks.Cohomology.CofinalCoveringSystem

end
