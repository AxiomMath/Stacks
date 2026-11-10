module

public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.MittagLefflerCohomology.StableImagesACC
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.QuotientTowers
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Mittag-Leffler cohomology from ACC on the whole graded module

The ascending chain condition for the whole graded module `⨁ₙ Hᵖ⁺¹(X, Iⁿ𝓕ₙ₊₁)` implies it for
the graded submodule of stable images, so the conclusions of `StableImagesACC` hold under this
stronger hypothesis.

## Main results

* `stableImagesHaveGradedACC_of_powerCohomologyGradedACC` passes from ACC for the whole graded
  module to ACC for the stable images.
* `cohomology_transitionImage_stable_uniformly_of_powerCohomologyGradedACC` and
  `isMittagLeffler_cohomology_of_powerCohomologyGradedACC` are the uniform stabilization and
  the Mittag-Leffler criterion under ACC for the whole graded module.

## References

* [Stacks Project, Tag 0GYK](https://stacks.math.columbia.edu/tag/0GYK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CategoryTheory.Pretriangulated
open Stacks.Cohomology.QuotientTowers

attribute [local instance] HasDerivedCategory.standard

/- The Grothendieck abelianness of modules and of module sheaves, and the additivity of global
sections, are established in `QuotientTowers` as file-local instances; they are re-activated
here rather than restated. They are deliberately not global: as global instances they enter
every instance search that mentions a module category. -/
attribute [local instance] Stacks.Cohomology.QuotientTowers.moduleFiltered
  Stacks.Cohomology.QuotientTowers.moduleGrothendieck
  Stacks.Cohomology.QuotientTowers.moduleFilteredSmall
  Stacks.Cohomology.QuotientTowers.sheafGrothendieck
  Stacks.Cohomology.QuotientTowers.sections_additive

attribute [local implicit_reducible] CategoryTheory.SingleFunctors.lift
  DerivedCategory.Plus.singleFunctors
attribute [local implicit_reducible] DerivedCategory.Plus.homologyFunctor
attribute [local implicit_reducible] HomologicalComplex.homologyFunctor
attribute [local implicit_reducible] ComplexShape.embeddingUpNat
attribute [local implicit_reducible] CategoryTheory.InjectiveResolution.cochainComplex
attribute [local implicit_reducible] CategoryTheory.Functor.rightDerivedPlus

universe u v w

namespace Stacks.Cohomology.MittagLefflerCohomology

variable {A : Type u} [CommRing A]

variable {X : Type w} [TopologicalSpace X]

/-! ### The ascending chain condition on the whole graded module

The source's Lemma 20.35.1 assumes the ascending chain condition for the direct sum
`⨁ₙ Hᵖ⁺¹(X, Iⁿ𝓕ₙ₊₁)` of all the cohomology modules, whereas Lemma 20.35.2 assumes it only
for the direct sum of the stable images inside them. The first hypothesis implies the
second: the stable images form a graded submodule, as the source's own proof of Lemma
20.35.2 observes, and a submodule of a Noetherian module is Noetherian.
-/

section PowerCohomologyACC

variable [Small.{v} A] [UnivLE.{max w v, v}]

/-- The direct sum `⨁ₙ Hᵖ(X, Iⁿ𝓕ₙ₊₁)` of the cohomology modules of the ideal-power
subsheaves: the graded module whose ascending chain condition the source assumes. -/
abbrev PowerCohomologySum (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ) :=
  DirectSum ℕ (fun n => ((cohomology p).obj (powerSheaf I n (F.obj (op n)))))

/-- The canonical action of `gr_I(A)` on `⨁ₙ Hᵖ(X, Iⁿ𝓕ₙ₊₁)`, specified on homogeneous
representatives by the source's diagram: lift `x ∈ Hᵖ(X, Iⁿ𝓕ₙ₊₁)` to `Hᵖ(X, Iⁿ𝓕ₖ₊ₙ₊₁)`
and multiply there by `a ∈ Iᵏ`. This is the same prescription as
`IsCanonicalStableImageAction`, imposed on all of `Hᵖ(X, Iⁿ𝓕ₙ₊₁)` rather than only on the
stable image; it constrains the action exactly at those `x` that admit a lift. -/
def IsCanonicalPowerCohomologyAction (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (PowerCohomologySum I F p)] : Prop :=
  ∀ (k n : ℕ) (a : ↥(I ^ k))
    (x : (cohomology p).obj (powerSheaf I n (F.obj (op n))))
    (y : (cohomology p).obj (powerSheaf I n (F.obj (op (k + n))))),
    ((cohomology p).map (powerSheafMap I n
      (F.map (homOfLE (Nat.le_add_left n k)).op))).hom y = x →
    DirectSum.of (fun i => AssociatedGraded.piece (M := A) I i) k
        (AssociatedGraded.mk I k
          ⟨a.1, by simpa only [AssociatedGraded.ring_power_eq] using a.2⟩) •
      DirectSum.of (fun i => (cohomology p).obj (powerSheaf I i (F.obj (op i)))) n x =
    DirectSum.of (fun i => (cohomology p).obj (powerSheaf I i (F.obj (op i)))) (k + n)
      (((cohomology p).map (powerSheafSMul I k n a (F.obj (op (k + n))))).hom y)

/-- ACC for the whole graded module `⨁ₙ Hᵖ(X, Iⁿ𝓕ₙ₊₁)` over the actual associated graded
ring. As in `StableImagesHaveGradedACC`, the existential packages the canonical action
rather than letting the caller supply an arbitrary graded ring. For a nonnegatively graded
module, ACC on graded submodules is equivalent to the Noetherian condition. -/
def PowerCohomologyHaveGradedACC (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ) :
    Prop :=
  ∃ action : Module (AssociatedGraded.gradedRing I) (PowerCohomologySum I F p),
    letI := action
    IsCanonicalPowerCohomologyAction I F p ∧
      IsNoetherian (AssociatedGraded.gradedRing I) (PowerCohomologySum I F p)

/-- The power-ideal subsheaf construction is functorial in the sheaf. -/
private theorem powerSheafMap_comp (I : Ideal A) (n : ℕ)
    {F G H : ModuleSheaf.{u, v, w} A X} (f : F ⟶ G) (g : G ⟶ H) :
    powerSheafMap I n (f ≫ g) = powerSheafMap I n f ≫ powerSheafMap I n g := by
  rw [powerSheafMap, powerSheafMap, powerSheafMap, ← Functor.map_comp]
  congr 1

/-- Multiplication by a homogeneous scalar is natural in the sheaf. -/
private theorem powerSheafSMul_comp_powerSheafMap (I : Ideal A) (k n : ℕ) (a : ↥(I ^ k))
    {F G : ModuleSheaf.{u, v, w} A X} (f : F ⟶ G) :
    powerSheafSMul I k n a F ≫ powerSheafMap I (k + n) f =
      powerSheafMap I n f ≫ powerSheafSMul I k n a G := by
  rw [powerSheafSMul, powerSheafMap, powerSheafMap, powerSheafSMul,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext U x
  exact Subtype.ext ((f.hom.app U).hom.map_smul a.1 x.1)

/-- The inclusion of the stable images takes a homogeneous element to a homogeneous one. -/
private theorem stableImageSumι_of (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p n : ℕ)
    (x : stableImage I F p n) :
    stableImageSumι I F p (DirectSum.of (fun i => stableImage I F p i) n x) =
      DirectSum.of (fun i => (cohomology p).obj (powerSheaf I i (F.obj (op i)))) n x.1 := by
  apply DFinsupp.ext
  intro m
  rw [stableImageSumι_apply]
  by_cases h : n = m
  · subst h
    rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
    rfl

/-- An element lies in the stable image iff it lifts to every higher level. -/
private theorem mem_stableImage_iff (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p n : ℕ)
    (x : (cohomology p).obj (powerSheaf I n (F.obj (op n)))) :
    x ∈ stableImage I F p n ↔ ∀ (m : ℕ) (h : n ≤ m), ∃ z : (cohomology p).obj
      (powerSheaf I n (F.obj (op m))),
      ((cohomology p).map (powerSheafMap I n (F.map (homOfLE h).op))).hom z = x := by
  simp only [stableImage, Submodule.mem_iInf, LinearMap.mem_range]

/-- The stable images are stable under the canonical action: the source's argument that
`⨁ Nₙ` is a graded submodule of `⨁ Hᵖ(X, Iⁿ𝓕ₙ₊₁)`. A lift of `x` to level `m` multiplies
to a lift of `a • x`, and the canonical prescription makes `a • x` independent of which
lift is used. -/
private theorem smul_mem_stableImage (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (PowerCohomologySum I F p)]
    (hcanonical : IsCanonicalPowerCohomologyAction I F p)
    (k n : ℕ) (a : ↥(I ^ k)) (x : stableImage I F p n)
    (y : (cohomology p).obj (powerSheaf I n (F.obj (op (k + n)))))
    (hy : ((cohomology p).map (powerSheafMap I n
      (F.map (homOfLE (Nat.le_add_left n k)).op))).hom y = x.1) :
    ((cohomology p).map (powerSheafSMul I k n a (F.obj (op (k + n))))).hom y ∈
      stableImage I F p (k + n) := by
  let H := cohomology.{u, v, w} (A := A) (X := X) p
  rw [mem_stableImage_iff]
  intro m hm
  obtain ⟨z, hz⟩ := (mem_stableImage_iff I F p n x.1).mp x.2 m ((Nat.le_add_left n k).trans hm)
  refine ⟨(H.map (powerSheafSMul I k n a (F.obj (op m)))).hom z, ?_⟩
  set y' := (H.map (powerSheafMap I n (F.map (homOfLE hm).op))).hom z with hy'def
  have hy' : (H.map (powerSheafMap I n
      (F.map (homOfLE (Nat.le_add_left n k)).op))).hom y' = x.1 := by
    rw [hy'def]
    change (H.map (powerSheafMap I n (F.map (homOfLE hm).op)) ≫
      H.map (powerSheafMap I n (F.map (homOfLE (Nat.le_add_left n k)).op))).hom z = _
    rw [← H.map_comp, ← powerSheafMap_comp, ← F.map_comp, ← hz]
    rfl
  have hcomp := (hcanonical k n a x.1 y hy).symm.trans (hcanonical k n a x.1 y' hy')
  have hval := congrArg (fun t => t (k + n)) hcomp
  simp only [DirectSum.of_eq_same] at hval
  rw [hval, hy'def]
  change (H.map (powerSheafSMul I k n a (F.obj (op m))) ≫
    H.map (powerSheafMap I (k + n) (F.map (homOfLE hm).op))).hom z = _
  rw [← H.map_comp, powerSheafSMul_comp_powerSheafMap, H.map_comp]
  rfl

/-- The image of the stable-image sum is a `gr_I(A)`-submodule of the whole graded module. -/
private theorem exists_stableImage_smul (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (PowerCohomologySum I F p)]
    (hcanonical : IsCanonicalPowerCohomologyAction I F p)
    (r : AssociatedGraded.gradedRing I) (v : StableImageSum I F p) :
    ∃ v' : StableImageSum I F p,
      stableImageSumι I F p v' = r • stableImageSumι I F p v := by
  induction r using DirectSum.induction_on with
  | zero => exact ⟨0, by rw [map_zero, zero_smul]⟩
  | add r r' hr hr' =>
    obtain ⟨v₁, h₁⟩ := hr
    obtain ⟨v₂, h₂⟩ := hr'
    exact ⟨v₁ + v₂, by rw [map_add, h₁, h₂, add_smul]⟩
  | of k c =>
    induction c using Quotient.inductionOn with
    | h a =>
      let a' : ↥(I ^ k) := ⟨a.1, by simpa only [AssociatedGraded.ring_power_eq] using a.2⟩
      have hmk : (⟦a⟧ : AssociatedGraded.piece (M := A) I k) =
          AssociatedGraded.mk I k ⟨a'.1, by
            simpa only [AssociatedGraded.ring_power_eq] using a'.2⟩ := rfl
      rw [hmk]
      induction v using DirectSum.induction_on with
      | zero => exact ⟨0, by rw [map_zero, smul_zero]⟩
      | add v v' hv hv' =>
        obtain ⟨v₁, h₁⟩ := hv
        obtain ⟨v₂, h₂⟩ := hv'
        exact ⟨v₁ + v₂, by rw [map_add, h₁, h₂, map_add, smul_add]⟩
      | of n x =>
        obtain ⟨y, hy⟩ := (mem_stableImage_iff I F p n x.1).mp x.2 (k + n) (Nat.le_add_left n k)
        refine ⟨DirectSum.of (fun i => stableImage I F p i) (k + n)
          ⟨_, smul_mem_stableImage I F p hcanonical k n a' x y hy⟩, ?_⟩
        rw [stableImageSumι_of, stableImageSumι_of]
        exact (hcanonical k n a' x.1 y hy).symm

/-- A module structure transported along an injective additive map whose image is stable
under the action. -/
@[instance_reducible]
private def moduleOfInjective {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R N] [SMul R M] (f : M →+ N) (hf : Function.Injective f)
    (hs : ∀ (r : R) (m : M), f (r • m) = r • f m) : Module R M where
  smul := (· • ·)
  one_smul m := hf (by rw [hs, one_smul])
  mul_smul r s m := hf (by rw [hs, hs, hs, mul_smul])
  smul_zero r := hf (by rw [hs, map_zero, smul_zero])
  smul_add r m m' := hf (by rw [hs, map_add, map_add, hs, hs, smul_add])
  add_smul r s m := hf (by rw [hs, map_add, hs, hs, add_smul])
  zero_smul m := hf (by rw [hs, zero_smul, map_zero])

/-- The action of `gr_I(A)` on the stable-image sum obtained by restricting the action on
the whole graded module. The scalar multiple is the unique preimage under the injection
`stableImageSumι`. -/
@[instance_reducible]
private noncomputable def stableImageSMul
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (PowerCohomologySum I F p)]
    (hcanonical : IsCanonicalPowerCohomologyAction I F p) :
    SMul (AssociatedGraded.gradedRing I) (StableImageSum I F p) :=
  ⟨fun r v => (exists_stableImage_smul I F p hcanonical r v).choose⟩

private theorem stableImageSMul_ι (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (PowerCohomologySum I F p)]
    (hcanonical : IsCanonicalPowerCohomologyAction I F p)
    (r : AssociatedGraded.gradedRing I) (v : StableImageSum I F p) :
    stableImageSumι I F p (@SMul.smul _ _ (stableImageSMul I F p hcanonical) r v) =
      r • stableImageSumι I F p v :=
  (exists_stableImage_smul I F p hcanonical r v).choose_spec

/-- The stable-image sum as a `gr_I(A)`-module, with the action restricted from the whole
graded module. -/
@[instance_reducible]
private noncomputable def stableImageModule
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (PowerCohomologySum I F p)]
    (hcanonical : IsCanonicalPowerCohomologyAction I F p) :
    Module (AssociatedGraded.gradedRing I) (StableImageSum I F p) :=
  letI := stableImageSMul I F p hcanonical
  moduleOfInjective (stableImageSumι I F p).toAddMonoidHom
    (stableImageSumι_injective I F p) (stableImageSMul_ι I F p hcanonical)

/-- ACC for the whole graded module `⨁ₙ Hᵖ(X, Iⁿ𝓕ₙ₊₁)` implies ACC for the graded module
of its stable images. The restricted action is canonical because the restriction of the
prescription is the prescription, and it is Noetherian because `stableImageSumι` is an
injection of `gr_I(A)`-modules. -/
public theorem stableImagesHaveGradedACC_of_powerCohomologyGradedACC
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hACC : PowerCohomologyHaveGradedACC.{u, v, w} I F p) :
    StableImagesHaveGradedACC.{u, v, w} I F p := by
  obtain ⟨action, hcanonical, hnoetherian⟩ := hACC
  let := action
  let := hnoetherian
  let md := stableImageModule I F p hcanonical
  refine ⟨md, ?_, ?_⟩
  · intro k n a x y hy
    refine Eq.trans (stableImageSMul_ι I F p hcanonical _ _) ?_
    rw [stableImageSumι_of]
    exact hcanonical k n a x.1 y hy
  · exact isNoetherian_of_injective
      ({ toFun := fun v => stableImageSumι I F p v
         map_add' := fun v v' => map_add _ v v'
         map_smul' := fun r v => stableImageSMul_ι I F p hcanonical r v } :
        StableImageSum I F p →ₗ[AssociatedGraded.gradedRing I] PowerCohomologySum I F p)
      (stableImageSumι_injective I F p)

/-- If the whole graded module `⨁ₙ Hᵖ⁺¹(X, Iⁿ𝓕ₙ₊₁)` satisfies graded ACC, there is a single
lag `c` such that, for every `i`, the image of `Hᵖ(F_(i+c+1)) → Hᵖ(F_(i+1))` is already the
stable image. -/
@[stacks 0GYK "uniform stabilization (footnote)"]
public theorem cohomology_transitionImage_stable_uniformly_of_powerCohomologyGradedACC
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower.{u, v, w} I F)
    (hACC : PowerCohomologyHaveGradedACC.{u, v, w} I F (p + 1)) :
    ∃ c : ℕ, ∀ (i m : ℕ) (h : i + c ≤ m),
      transitionImage (F ⋙ cohomology.{u, v, w} (A := A) (X := X) p)
        i m ((Nat.le_add_right i c).trans h) =
      transitionImage (F ⋙ cohomology.{u, v, w} (A := A) (X := X) p)
        i (i + c) (Nat.le_add_right i c) :=
  cohomology_transitionImage_stable_uniformly I F p hquotient
    (stableImagesHaveGradedACC_of_powerCohomologyGradedACC I F (p + 1) hACC)

/-- If the whole graded module `⨁ₙ Hᵖ⁺¹(X, Iⁿ𝓕ₙ₊₁)` satisfies graded ACC, the degree-`p`
cohomology tower of an ideal-power quotient system satisfies the Mittag-Leffler condition. -/
@[stacks 0GYK "Mittag-Leffler condition"]
public theorem isMittagLeffler_cohomology_of_powerCohomologyGradedACC
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower.{u, v, w} I F)
    (hACC : PowerCohomologyHaveGradedACC.{u, v, w} I F (p + 1)) :
    IsMittagLefflerCategorical
      (F ⋙ cohomology.{u, v, w} (A := A) (X := X) p) :=
  isMittagLeffler_cohomology_of_stableImagesGradedACC I F p hquotient
    (stableImagesHaveGradedACC_of_powerCohomologyGradedACC I F (p + 1) hACC)

end PowerCohomologyACC

end Stacks.Cohomology.MittagLefflerCohomology

end
