module

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
# Mittag-Leffler cohomology from ACC on the stable images

Let `I` be an ideal in a commutative ring and let an inverse system of sheaves of modules have
transitions given by quotienting by the corresponding powers of `I`. If the graded module formed
from the stable images in degree `p + 1` satisfies the ascending chain condition, its degree-`p`
cohomology tower stabilizes with a uniform lag and is therefore Mittag-Leffler.

The proof builds the short exact sequences of the tower whose kernels are its ideal-power
subsheaves, the connecting map of the derived functors of global sections and its
identification with sheaf cohomology, and shows that the boundaries of the tower land in
the stable images compatibly with multiplication by homogeneous scalars; the ascending chain
condition then bounds the correction needed to reach the stable image.

## Main results

* `cohomology_transitionImage_stable_uniformly` gives the uniform stabilization asserted in
  the source's footnote.
* `isMittagLeffler_cohomology_of_stableImagesGradedACC` gives the Mittag-Leffler criterion.

## References

* [Stacks Project, Tag 0GYL](https://stacks.math.columbia.edu/tag/0GYL)
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
attribute [local implicit_reducible] DerivedCategory.Plus.Qh
attribute [local implicit_reducible] DerivedCategory.Plus.homologyFunctor
attribute [local implicit_reducible] HomologicalComplex.homologyFunctor
attribute [local implicit_reducible] ComplexShape.embeddingUpNat
attribute [local implicit_reducible] CategoryTheory.InjectiveResolution.cochainComplex
attribute [local implicit_reducible] CategoryTheory.Functor.rightDerivedPlus

universe u v w

namespace Stacks.Cohomology.MittagLefflerCohomology

variable {A : Type u} [CommRing A]

variable {X : Type w} [TopologicalSpace X]

private theorem idealMultiple_map_epi (J : Ideal A)
    {P Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} A} (α : P ⟶ Q) [Epi α] :
    Epi (Functor.whiskerRight α (idealMultipleFunctor J)) := by
  let β := Functor.whiskerRight α (idealMultipleFunctor J)
  let : ∀ U, Epi (β.app U) := by
    intro U
    refine (ModuleCat.epi_iff_surjective _).2 fun y => ?_
    let f := (α.app U).hom
    have hf : Function.Surjective f := ModuleCat.epi_iff_surjective _ |>.mp inferInstance
    have hmap : (J • (⊤ : Submodule A (P.obj U))).map f =
        J • (⊤ : Submodule A (Q.obj U)) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    have hy : y.1 ∈ (J • (⊤ : Submodule A (P.obj U))).map f := by
      rw [hmap]
      exact y.2
    obtain ⟨x, hx, hfx⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  exact NatTrans.epi_of_epi_app β

private def idealMultipleInclusion
    {A : Type u} [CommRing A] (J K : Ideal A) (h : J ≤ K) :
    idealMultipleFunctor.{u, v} J ⟶ idealMultipleFunctor K where
  app M := ModuleCat.ofHom (Submodule.inclusion (Submodule.smul_mono_left h))
  naturality := by
    intro M N f
    ext x
    rfl

private def powerSheafCompare
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (n m : ℕ) (hnm : n ≤ m)
    (F : ModuleSheaf.{u, v, w} A X) :
    powerSheaf I m F ⟶ powerSheaf I n F :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{v} A)).map
    (Functor.whiskerLeft F.obj
      (idealMultipleInclusion (I ^ m) (I ^ n) (Ideal.pow_le_pow_right hnm)))

private theorem idealMultipleInclusion_ι
    {A : Type u} [CommRing A] (J K : Ideal A) (h : J ≤ K) :
    idealMultipleInclusion J K h ≫ idealMultipleι K =
      idealMultipleι J := by
  ext M x
  rfl

private theorem powerSheafCompare_ι
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (n m : ℕ) (hnm : n ≤ m)
    (F : ModuleSheaf.{u, v, w} A X) :
    powerSheafCompare I n m hnm F ≫ powerSheafι I n F =
      powerSheafι I m F := by
  let J := Opens.grothendieckTopology X
  let adj := sheafificationAdjunction J (ModuleCat.{v} A)
  let β := Functor.whiskerLeft F.obj
    (idealMultipleInclusion (I ^ m) (I ^ n) (Ideal.pow_le_pow_right hnm))
  let αn := Functor.whiskerLeft F.obj (idealMultipleι (I ^ n))
  let αm := Functor.whiskerLeft F.obj (idealMultipleι (I ^ m))
  show (presheafToSheaf J (ModuleCat.{v} A)).map β ≫
      (adj.homEquiv _ F).symm αn = (adj.homEquiv _ F).symm αm
  apply (adj.homEquiv _ F).injective
  simp only [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  show (Functor.whiskerLeft F.obj
      (idealMultipleInclusion (I ^ m) (I ^ n) (Ideal.pow_le_pow_right hnm)) ≫
        Functor.whiskerLeft F.obj (idealMultipleι (I ^ n))) =
      Functor.whiskerLeft F.obj (idealMultipleι (I ^ m))
  rw [← Functor.whiskerLeft_comp, idealMultipleInclusion_ι]

/-- A functor on `ℕᵒᵖ` sends the composite of two transition maps to the composite of images. -/
private lemma map_homOfLE_trans {C : Type*} [Category C] (F : ℕᵒᵖ ⥤ C) {a b c : ℕ}
    (h₁ : a ≤ b) (h₂ : b ≤ c) :
    F.map (homOfLE (h₁.trans h₂)).op = F.map (homOfLE h₂).op ≫ F.map (homOfLE h₁).op := by
  rw [← F.map_comp]
  rfl

section

variable [Small.{v} A] [UnivLE.{max w v, v}]

private lemma quotientTowerStep_epi (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n : ℕ) :
    Epi (F.map (homOfLE (Nat.le_succ n)).op) := by
  obtain ⟨e, he⟩ := hF n
  rw [← he]
  infer_instance

private lemma quotientTower_smul_id (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n : ℕ) (a : A) (ha : a ∈ I ^ (n + 1)) :
    a • 𝟙 (F.obj (op n)) = 0 := by
  let q := F.map (homOfLE (Nat.le_succ n)).op
  have : Epi q := quotientTowerStep_epi I F hF n
  apply (cancel_epi q).mp
  rw [Linear.comp_smul, Category.comp_id, comp_zero]
  apply (powerSheafι_comp_eq_zero_iff I (n + 1) q).mp _ a ha
  obtain ⟨e, he⟩ := hF n
  dsimp [q]
  rw [← he, ← Category.assoc, cokernel.condition, zero_comp]

private lemma quotientTower_smul_map (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n m : ℕ) (h : n ≤ m) (a : A) (ha : a ∈ I ^ (n + 1)) :
    a • F.map (homOfLE h).op = 0 := by
  rw [← Category.comp_id (F.map _), ← Linear.comp_smul,
    quotientTower_smul_id I F hF n a ha, comp_zero]

private lemma quotientTower_desc (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n m : ℕ) (hnm : n ≤ m)
    (G : ModuleSheaf.{u, v, w} A X) (f : F.obj (op m) ⟶ G)
    (hf : ∀ a ∈ I ^ (n + 1), a • f = 0) :
    ∃ g : F.obj (op n) ⟶ G, F.map (homOfLE hnm).op ≫ g = f := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨f, by simp⟩
  | succ m h ih =>
    obtain ⟨e, he⟩ := hF m
    have hzero : powerSheafι I (m + 1) (F.obj (op (m + 1))) ≫ f = 0 :=
      (powerSheafι_comp_eq_zero_iff I (m + 1) f).mpr fun a ha =>
        hf a (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1) ha)
    let g := e.inv ≫ cokernel.desc _ f hzero
    have hg : F.map (homOfLE (Nat.le_succ m)).op ≫ g = f := by
      rw [← he]
      simp [g]
    have hgf : ∀ a ∈ I ^ (n + 1), a • g = 0 := by
      intro a ha
      have := quotientTowerStep_epi I F hF m
      apply (cancel_epi (F.map (homOfLE (Nat.le_succ m)).op)).mp
      rw [Linear.comp_smul, hg, comp_zero]
      exact hf a ha
    obtain ⟨g', hg'⟩ := ih g hgf
    refine ⟨g', ?_⟩
    rw [map_homOfLE_trans F h (Nat.le_succ m), Category.assoc, hg', hg]

private lemma quotientTower_epi (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n m : ℕ) (h : n ≤ m) :
    Epi (F.map (homOfLE h).op) := by
  induction m, h using Nat.le_induction with
  | base => simpa using (inferInstance : Epi (𝟙 (F.obj (op n))))
  | succ m h ih =>
    have := quotientTowerStep_epi I F hF m
    rw [map_homOfLE_trans F h (Nat.le_succ m)]
    infer_instance

private lemma quotientTower_power_comp_eq_zero (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n m : ℕ) (h : n ≤ m) :
    powerSheafι I (n + 1) (F.obj (op m)) ≫
      F.map (homOfLE h).op = 0 := by
  exact (powerSheafι_comp_eq_zero_iff I (n + 1) _).mpr (quotientTower_smul_map I F hF n m h)

private noncomputable def quotientTowerCokernel (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n m : ℕ) (h : n ≤ m) :
    IsColimit (CokernelCofork.ofπ (F.map (homOfLE h).op)
      (quotientTower_power_comp_eq_zero I F hF n m h)) := by
  have := quotientTower_epi I F hF n m h
  apply CokernelCofork.IsColimit.ofπ'
  intro G g hg
  exact ⟨Classical.choose (quotientTower_desc I F hF n m h G g
    ((powerSheafι_comp_eq_zero_iff I (n + 1) g).mp hg)),
    Classical.choose_spec (quotientTower_desc I F hF n m h G g
    ((powerSheafι_comp_eq_zero_iff I (n + 1) g).mp hg))⟩

private lemma quotientTower_exists_scalar_lift (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n m : ℕ) (h : n ≤ m)
    (a : A) (ha : a ∈ I ^ (m - n)) :
    ∃ g : F.obj (op n) ⟶ F.obj (op m),
      F.map (homOfLE h).op ≫ g = a • 𝟙 (F.obj (op m)) := by
  apply quotientTower_desc I F hF n m h
  intro b hb
  rw [smul_smul]
  apply quotientTower_smul_id I F hF m
  have hh : n + 1 + (m - n) = m + 1 := by omega
  rw [← hh, pow_add]
  exact Ideal.mul_mem_mul hb ha

private lemma quotientTower_scalar_lift_comp_eq_zero (I : Ideal A)
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n m i : ℕ) (hnm : n ≤ m) (him : i ≤ m)
    (a : A) (ha : a ∈ I ^ (i + 1))
    (g : F.obj (op n) ⟶ F.obj (op m))
    (hg : F.map (homOfLE hnm).op ≫ g = a • 𝟙 (F.obj (op m))) :
    g ≫ F.map (homOfLE him).op = 0 := by
  have := quotientTower_epi I F hF n m hnm
  apply (cancel_epi (F.map (homOfLE hnm).op)).mp
  rw [← Category.assoc, hg, Linear.smul_comp, Category.id_comp, comp_zero]
  exact quotientTower_smul_map I F hF i m him a ha

end

private noncomputable def quotientShortComplex
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (n : ℕ) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) :
    ShortComplex (ModuleSheaf.{u, v, w} A X) := by
  let f := powerSheafι I (n + 1) (F.obj (op (n + 1)))
  exact ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

private theorem quotientShortComplex_shortExact
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (n : ℕ) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) :
    (quotientShortComplex I n F).ShortExact :=
  .mk' (ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel (powerSheafι I (n + 1) (F.obj (op (n + 1))))))
    (powerSheafι_mono I (n + 1) (F.obj (op (n + 1))))
    (inferInstanceAs (Epi (cokernel.π (powerSheafι I (n + 1) (F.obj (op (n + 1)))))))

private noncomputable def quotientTowerStep
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (n : ℕ) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) :
    ShortComplex (ModuleSheaf.{u, v, w} A X) := by
  let f := powerSheafι I (n + 1) (F.obj (op (n + 1)))
  let e := Classical.choose (hquotient n)
  have he := Classical.choose_spec (hquotient n)
  exact ShortComplex.mk f (F.map (homOfLE (Nat.le_succ n)).op) (by
    rw [← he, ← Category.assoc, cokernel.condition, zero_comp])

private theorem quotientTowerStep_shortExact
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (n : ℕ) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) :
    (quotientTowerStep I n F hquotient).ShortExact := by
  let e := Classical.choose (hquotient n)
  have he := Classical.choose_spec (hquotient n)
  let S := quotientShortComplex I n F
  let T := quotientTowerStep I n F hquotient
  have hST : S ≅ T := by
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e ?_ ?_
    · rfl
    · simpa [S, T, quotientShortComplex, quotientTowerStep] using he.symm
  exact ShortComplex.shortExact_of_iso hST (quotientShortComplex_shortExact I n F)

private abbrev quotientTowerInterval
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n m : ℕ) (h : n ≤ m) :
    ShortComplex (ModuleSheaf.{u, v, w} A X) :=
  ShortComplex.mk (powerSheafι I (n + 1) (F.obj (op m)))
    (F.map (homOfLE h).op) (quotientTower_power_comp_eq_zero I F hF n m h)

private lemma quotientTowerInterval_shortExact
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n m : ℕ) (h : n ≤ m) :
    (quotientTowerInterval I F hF n m h).ShortExact :=
  .mk' (ShortComplex.exact_of_g_is_cokernel _ (quotientTowerCokernel I F hF n m h))
    (powerSheafι_mono I (n + 1) (F.obj (op m))) (quotientTower_epi I F hF n m h)

private def quotientTowerIntervalMap
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (n k m : ℕ) (hnk : n ≤ k) (hkm : k ≤ m) :
    quotientTowerInterval I F hF n m (hnk.trans hkm) ⟶
      quotientTowerInterval I F hF n k hnk :=
  { τ₁ := powerSheafMap I (n + 1) (F.map (homOfLE hkm).op)
    τ₂ := F.map (homOfLE hkm).op
    τ₃ := 𝟙 _
    comm₁₂ := powerSheafMap_ι I (n + 1) _
    comm₂₃ := by
      change F.map _ ≫ F.map _ = F.map _ ≫ 𝟙 _
      rw [Category.comp_id, ← F.map_comp]
      rfl }

/-- The boundary of a longer interval maps to the boundary of a shorter one. -/
private lemma quotientBoundary_map_eq
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (p : ℕ)
    (δ : ∀ (S : ShortComplex (ModuleSheaf.{u, v, w} A X)), S.ShortExact →
      ((cohomology p).obj S.X₃ ⟶ (cohomology (p + 1)).obj S.X₁))
    (hδ : ∀ (S T : ShortComplex (ModuleSheaf.{u, v, w} A X))
      (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T),
      (cohomology p).map f.τ₃ ≫ δ T hT =
        δ S hS ≫ (cohomology (p + 1)).map f.τ₁)
    (n k m : ℕ) (hnk : n ≤ k) (hkm : k ≤ m) (x : (cohomology p).obj (F.obj (op n))) :
    ((cohomology (p + 1)).map (powerSheafMap I (n + 1) (F.map (homOfLE hkm).op))).hom
        ((δ (quotientTowerInterval I F hF n m (hnk.trans hkm))
          (quotientTowerInterval_shortExact I F hF n m (hnk.trans hkm))).hom x) =
      (δ (quotientTowerInterval I F hF n k hnk)
        (quotientTowerInterval_shortExact I F hF n k hnk)).hom x := by
  have hh := hδ _ _ (quotientTowerInterval_shortExact I F hF n m (hnk.trans hkm))
    (quotientTowerInterval_shortExact I F hF n k hnk)
    (quotientTowerIntervalMap I F hF n k m hnk hkm)
  change (cohomology p).map (𝟙 _) ≫ _ = _ at hh
  rw [(cohomology p).map_id, Category.id_comp] at hh
  exact (congrArg (fun f => f.hom x) hh).symm

private lemma quotientBoundary_mem_stableImage
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (p : ℕ)
    (δ : ∀ (S : ShortComplex (ModuleSheaf.{u, v, w} A X)), S.ShortExact →
      ((cohomology p).obj S.X₃ ⟶ (cohomology (p + 1)).obj S.X₁))
    (hδ : ∀ (S T : ShortComplex (ModuleSheaf.{u, v, w} A X))
      (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T),
      (cohomology p).map f.τ₃ ≫ δ T hT =
        δ S hS ≫ (cohomology (p + 1)).map f.τ₁)
    (n : ℕ) (x : (cohomology p).obj (F.obj (op n))) :
    (δ (quotientTowerInterval I F hF n (n + 1) (Nat.le_succ n))
      (quotientTowerInterval_shortExact I F hF n (n + 1) (Nat.le_succ n))).hom x ∈
        stableImage I F (p + 1) (n + 1) := by
  simp only [stableImage, Submodule.mem_iInf]
  intro m hm
  exact ⟨_, quotientBoundary_map_eq I F hF p δ hδ n (n + 1) m (Nat.le_succ n) hm x⟩

private def quotientScalarIntervalMap
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (j k : ℕ) (a : ↥(I ^ k))
    (g : F.obj (op j) ⟶ F.obj (op (k + j)))
    (hg : F.map (homOfLE (Nat.le_add_left j k)).op ≫ g =
      a.1 • 𝟙 (F.obj (op (k + j)))) :
    quotientTowerInterval I F hF j (k + j + 1)
        ((Nat.le_add_left j k).trans (Nat.le_succ (k + j))) ⟶
      quotientTowerInterval I F hF (k + j) (k + j + 1) (Nat.le_succ _) := by
  let h := (Nat.le_add_left j k).trans (Nat.le_succ (k + j))
  exact
    { τ₁ := powerSheafSMul I k (j + 1) a (F.obj (op (k + j + 1)))
      τ₂ := a.1 • 𝟙 _
      τ₃ := g
      comm₁₂ := powerSheafSMul_ι I k (j + 1) a _
      comm₂₃ := by
        symm
        change F.map (homOfLE h).op ≫ g = (a.1 • 𝟙 _) ≫ F.map _
        rw [map_homOfLE_trans F (Nat.le_add_left j k) (Nat.le_succ (k + j)), Category.assoc, hg,
          Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp] }

-- Elaborating the lifted boundary diagram requires additional reduction of sheafification maps.
private lemma quotientBoundary_smul
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (p : ℕ)
    (δ : ∀ (S : ShortComplex (ModuleSheaf.{u, v, w} A X)), S.ShortExact →
      ((cohomology p).obj S.X₃ ⟶ (cohomology (p + 1)).obj S.X₁))
    (hδ : ∀ (S T : ShortComplex (ModuleSheaf.{u, v, w} A X))
      (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T),
      (cohomology p).map f.τ₃ ≫ δ T hT =
        δ S hS ≫ (cohomology (p + 1)).map f.τ₁)
    [Module (AssociatedGraded.gradedRing I) (StableImageSum I F (p + 1))]
    (haction : IsCanonicalStableImageAction I F (p + 1))
    (j k : ℕ) (a : ↥(I ^ k))
    (x : (cohomology p).obj (F.obj (op j)))
    (g : F.obj (op j) ⟶ F.obj (op (k + j)))
    (hg : F.map (homOfLE (Nat.le_add_left j k)).op ≫ g =
      a.1 • 𝟙 (F.obj (op (k + j)))) :
    stableImageSumι I F (p + 1)
      (DirectSum.of (fun i => AssociatedGraded.piece (M := A) I i) k
        (AssociatedGraded.mk I k
          ⟨a.1, by simpa only [AssociatedGraded.ring_power_eq] using a.2⟩) •
        DirectSum.of (fun i => stableImage I F (p + 1) i) (j + 1)
          ⟨(δ (quotientTowerInterval I F hF j (j + 1) (Nat.le_succ j))
            (quotientTowerInterval_shortExact I F hF j (j + 1) (Nat.le_succ j))).hom x,
            quotientBoundary_mem_stableImage I F hF p δ hδ j x⟩) =
      DirectSum.of (fun i => (cohomology (p + 1)).obj
        (powerSheaf I i (F.obj (op i)))) (k + j + 1)
        ((δ (quotientTowerInterval I F hF (k + j) (k + j + 1) (Nat.le_succ _))
          (quotientTowerInterval_shortExact I F hF (k + j) (k + j + 1)
            (Nat.le_succ _))).hom ((cohomology p).map g |>.hom <| x)) := by
  let h := (Nat.le_add_left j k).trans (Nat.le_succ (k + j))
  let S := quotientTowerInterval I F hF j (k + j + 1) h
  let T := quotientTowerInterval I F hF (k + j) (k + j + 1) (Nat.le_succ _)
  let hS := quotientTowerInterval_shortExact I F hF j (k + j + 1) h
  let hT := quotientTowerInterval_shortExact I F hF (k + j) (k + j + 1) (Nat.le_succ _)
  have hlift : ((cohomology (p + 1)).map
      (powerSheafMap I (j + 1)
        (F.map (homOfLE (Nat.le_add_left (j + 1) k)).op))).hom ((δ S hS).hom x) =
      (δ (quotientTowerInterval I F hF j (j + 1) (Nat.le_succ j))
        (quotientTowerInterval_shortExact I F hF j (j + 1) (Nat.le_succ j))).hom x := by
    exact quotientBoundary_map_eq I F hF p δ hδ j (j + 1) (k + j + 1) (Nat.le_succ j)
      (by omega) x
  have hact := haction k (j + 1) a
    ⟨(δ (quotientTowerInterval I F hF j (j + 1) (Nat.le_succ j))
      (quotientTowerInterval_shortExact I F hF j (j + 1) (Nat.le_succ j))).hom x,
      quotientBoundary_mem_stableImage I F hF p δ hδ j x⟩ ((δ S hS).hom x) hlift
  exact hact.trans (congrArg (DirectSum.of _ (k + j + 1))
    (congrArg (fun f => f.hom x) (hδ S T hS hT (quotientScalarIntervalMap I F hF j k a g hg))).symm)

private noncomputable def singleTrianglePlusMap
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (φ : S₁ ⟶ S₂) : TriangleMorphism (singleTrianglePlus h₁) (singleTrianglePlus h₂) where
  hom₁ := (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁
  hom₂ := (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₂
  hom₃ := (DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃
  comm₁ := by
    simpa only [singleTrianglePlus, Triangle.mk_mor₁, Functor.map_comp] using
      (congrArg ((DerivedCategory.Plus.singleFunctor C 0).map) φ.comm₁₂).symm
  comm₂ := by
    simpa only [singleTrianglePlus, Triangle.mk_mor₂, Functor.map_comp] using
      (congrArg ((DerivedCategory.Plus.singleFunctor C 0).map) φ.comm₂₃).symm
  comm₃ := (singleFunctorPlusDelta (C := C)).δ_naturality h₁ h₂ φ

private noncomputable def derivedCohomologyBoundary
    {A : Type u} [CommRing A]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (G : C ⥤ ModuleCat.{v} A) [G.Additive] [EnoughInjectives C]
    {S : ShortComplex C} (hS : S.ShortExact) (p : ℕ) :
    (G.rightDerivedPlus (p : ℤ)).obj S.X₃ ⟶
      (G.rightDerivedPlus ((p + 1 : ℕ) : ℤ)).obj S.X₁ := by
  letI : G.rightDerivedFunctorPlus.CommShift ℤ :=
    Functor.IsRightDerivedFunctor.commShift _ G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso C) ℤ
  letI : NatTrans.CommShift G.rightDerivedFunctorPlusUnit ℤ :=
    Functor.IsRightDerivedFunctor.natTrans_commShift _ G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso C) ℤ
  letI : G.rightDerivedFunctorPlus.IsTriangulated :=
    Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus
      G _ G.rightDerivedFunctorPlusUnit
  let d := (singleFunctorPlusDelta (C := C)).comp G.rightDerivedFunctorPlus
  let T := Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0 ⋙
      G.rightDerivedFunctorPlus).map S.f)
    ((DerivedCategory.Plus.singleFunctor C 0 ⋙ G.rightDerivedFunctorPlus).map S.g) (d.δ hS)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} A) 0
  exact H.homologySequenceδ T (p : ℤ) ((p + 1 : ℕ) : ℤ) (by omega)

/-- The connecting maps `derivedCohomologyBoundary` give exact sequences and are natural. -/
private theorem derivedCohomologyBoundary_exact_and_naturality
    {A : Type u} [CommRing A]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (G : C ⥤ ModuleCat.{v} A) [G.Additive] [EnoughInjectives C] :
    (∀ {S : ShortComplex C} (hS : S.ShortExact) (p : ℕ),
      ∃ hz : (G.rightDerivedPlus (p : ℤ)).map S.g ≫ derivedCohomologyBoundary G hS p = 0,
        (ShortComplex.mk _ _ hz).Exact) ∧
    ∀ {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
      (φ : S₁ ⟶ S₂) (p : ℕ),
      (G.rightDerivedPlus (p : ℤ)).map φ.τ₃ ≫ derivedCohomologyBoundary G h₂ p =
        derivedCohomologyBoundary G h₁ p ≫
          (G.rightDerivedPlus ((p + 1 : ℕ) : ℤ)).map φ.τ₁ := by
  let RF := G.rightDerivedFunctorPlus
  let : G.rightDerivedFunctorPlus.CommShift ℤ :=
    Functor.IsRightDerivedFunctor.commShift _ G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso C) ℤ
  let : NatTrans.CommShift G.rightDerivedFunctorPlusUnit ℤ :=
    Functor.IsRightDerivedFunctor.natTrans_commShift _ G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso C) ℤ
  let : G.rightDerivedFunctorPlus.IsTriangulated :=
    Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus
      G _ G.rightDerivedFunctorPlusUnit
  let d := (singleFunctorPlusDelta (C := C)).comp RF
  let δ : ∀ {T : ShortComplex C}, T.ShortExact → ∀ i : ℕ,
      (G.rightDerivedPlus (i : ℤ)).obj T.X₃ ⟶
        (G.rightDerivedPlus ((i + 1 : ℕ) : ℤ)).obj T.X₁ :=
    fun {T} hT i =>
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
        (Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0 ⋙ RF).map T.f)
          ((DerivedCategory.Plus.singleFunctor C 0 ⋙ RF).map T.g) (d.δ hT))
        (i : ℤ) ((i + 1 : ℕ) : ℤ) rfl
  have hdelta := Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal G d δ
    (by intro T hT i; rfl)
  obtain ⟨_, _, _, hex, _, hnat⟩ := hdelta.1
  exact ⟨fun hS p => by simpa only [derivedCohomologyBoundary] using hex hS p,
    fun h₁ h₂ φ p => by
      simpa [derivedCohomologyBoundary, RF, δ, d, Functor.rightDerivedPlus,
        Functor.comp_map] using hnat h₁ h₂ φ p⟩

private abbrev resolutionPlus {C : Type*} [Category C] [Abelian C]
    {M : C} (I : InjectiveResolution M) : HomotopyCategory.Plus C :=
  (HomotopyCategory.Plus.quotient C).obj ⟨I.cochainComplex, ⟨0, inferInstance⟩⟩

private def resolutionQhIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {M : C} (I : InjectiveResolution M) :
    DerivedCategory.Q.obj I.cochainComplex ≅
      DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Qh.obj (resolutionPlus I)) :=
  ((DerivedCategory.quotientCompQhIso C).app I.cochainComplex).symm

private def resolutionSingleIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {M : C} (I : InjectiveResolution M) :
    (DerivedCategory.Plus.singleFunctor C 0).obj M ≅
      DerivedCategory.Plus.Qh.obj (resolutionPlus I) :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
      asIso (DerivedCategory.Q.map I.ι') ≪≫ resolutionQhIso I)

private abbrev resolutionPlusMap {C : Type*} [Category C] [Abelian C]
    {M N : C} {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : I.Hom J f) : resolutionPlus I ⟶ resolutionPlus J :=
  (HomotopyCategory.Plus.quotient C).map (ObjectProperty.homMk φ.hom')

private lemma singleFunctorIsoCompQ_naturality_assoc' {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {M N : C} (f : M ⟶ N) {Z : DerivedCategory C}
    (g : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj N) ⟶ Z) :
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app N).hom ≫ g =
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app M).hom ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map f) ≫ g :=
  (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality_assoc f g

private lemma resolutionQhIso_naturality {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {M N : C} {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : I.Hom J f) :
    DerivedCategory.Q.map φ.hom' ≫ (resolutionQhIso J).hom =
      (resolutionQhIso I).hom ≫
        DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map (resolutionPlusMap φ)) :=
  (DerivedCategory.quotientCompQhIso C).inv.naturality φ.hom'

private lemma resolutionSingleIso_naturality {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {M N : C} {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : I.Hom J f) :
    (DerivedCategory.Plus.singleFunctor C 0).map f ≫ (resolutionSingleIso J).hom =
      (resolutionSingleIso I).hom ≫ DerivedCategory.Plus.Qh.map (resolutionPlusMap φ) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, resolutionSingleIso, Functor.preimageIso_hom, Functor.map_preimage,
    Iso.trans_hom]
  simp only [Category.assoc, asIso_hom]
  rw [singleFunctorIsoCompQ_naturality_assoc' (C := C) f, ← Functor.map_comp_assoc,
    ← φ.ι'_comp_hom', Functor.map_comp, Category.assoc, resolutionQhIso_naturality φ]

private def resolutionDerivedIso
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive]
    {M : C} (I : InjectiveResolution M) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M) ≅
      DerivedCategory.Plus.Qh.obj ((F.mapHomotopyCategoryPlus).obj (resolutionPlus I)) := by
  have : ∀ n : ℤ, Injective ((resolutionPlus I).obj.as.X n) := fun n =>
    inferInstanceAs (Injective (I.cochainComplex.X n))
  have : IsIso (F.rightDerivedFunctorPlusUnit.app (resolutionPlus I)) := inferInstance
  exact F.rightDerivedFunctorPlus.mapIso (resolutionSingleIso I) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app (resolutionPlus I))).symm

private lemma resolutionDerivedIso_naturality
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive]
    {M N : C} {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : I.Hom J f) :
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
        (resolutionDerivedIso F J).hom =
      (resolutionDerivedIso F I).hom ≫
        DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map (resolutionPlusMap φ)) := by
  have : ∀ n : ℤ, Injective ((resolutionPlus J).obj.as.X n) := fun n =>
    inferInstanceAs (Injective (J.cochainComplex.X n))
  have : IsIso (F.rightDerivedFunctorPlusUnit.app (resolutionPlus J)) := inferInstance
  dsimp only [resolutionDerivedIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    asIso_inv]
  rw [← Category.assoc, ← Functor.map_comp, resolutionSingleIso_naturality φ,
    Functor.map_comp]
  simp only [Category.assoc]
  apply congrArg (fun t => F.rightDerivedFunctorPlus.map (resolutionSingleIso I).hom ≫ t)
  apply (cancel_mono (F.rightDerivedFunctorPlusUnit.app (resolutionPlus J))).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hnat := F.rightDerivedFunctorPlusUnit.naturality (resolutionPlusMap φ)
  change DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map (resolutionPlusMap φ)) ≫
    F.rightDerivedFunctorPlusUnit.app (resolutionPlus J) =
      F.rightDerivedFunctorPlusUnit.app (resolutionPlus I) ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (resolutionPlusMap φ)) at hnat
  rw [hnat]
  simp

private lemma mapExtendIso_naturality'
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] {M N : C}
    {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : I.Hom J f) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom' ≫
        (Stacks.DerivedIndexing.mapExtendIsoSymm F ComplexShape.embeddingUpNat J.cocomplex).hom =
      (Stacks.DerivedIndexing.mapExtendIsoSymm F ComplexShape.embeddingUpNat I.cocomplex).hom ≫
        HomologicalComplex.extendMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom)
          ComplexShape.embeddingUpNat :=
  Stacks.DerivedIndexing.mapExtendIsoSymm_naturality F ComplexShape.embeddingUpNat φ.hom

private lemma extendHomologyTail_naturality
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] {M N : C}
    {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : I.Hom J f) (p : ℕ) :
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (p : ℤ)).map
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom') ≫
        ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (p : ℤ)).mapIso
            (Stacks.DerivedIndexing.mapExtendIsoSymm F ComplexShape.embeddingUpNat
              J.cocomplex) ≪≫
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (j := p) (j' := (p : ℤ)) rfl).hom =
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (p : ℤ)).mapIso
            (Stacks.DerivedIndexing.mapExtendIsoSymm F ComplexShape.embeddingUpNat
              I.cocomplex) ≪≫
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (j := p) (j' := (p : ℤ)) rfl).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) p := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp, mapExtendIso_naturality' F φ, Functor.map_comp,
    Category.assoc]
  congr 1
  exact HomologicalComplex.extendHomologyIso_hom_naturality
    ((F.mapHomologicalComplex _).map φ.hom) ComplexShape.embeddingUpNat (j := p) (j' := (p : ℤ)) rfl

private lemma quotientCompQhIso_app_naturality {D : Type*} [Category D] [Abelian D]
    [HasDerivedCategory D] {K L : CochainComplex D ℤ} (g : K ⟶ L) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map g) ≫
        ((DerivedCategory.quotientCompQhIso D).app L).hom =
      ((DerivedCategory.quotientCompQhIso D).app K).hom ≫ DerivedCategory.Q.map g :=
  (DerivedCategory.quotientCompQhIso D).hom.naturality g

private lemma homologyFunctorFactors_app_naturality_assoc {D : Type*} [Category D] [Abelian D]
    [HasDerivedCategory D] (p : ℤ) {K L : CochainComplex D ℤ} (g : K ⟶ L) {Z : D}
    (h : (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) p).obj L ⟶ Z) :
    (DerivedCategory.homologyFunctor D p).map (DerivedCategory.Q.map g) ≫
        ((DerivedCategory.homologyFunctorFactors D p).app L).hom ≫ h =
      ((DerivedCategory.homologyFunctorFactors D p).app K).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) p).map g ≫ h :=
  (DerivedCategory.homologyFunctorFactors D p).hom.naturality_assoc g h

private def mappedResolutionQuotientIso
    {C D : Type*} [Category C] [Abelian C]
    [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] {M : C} (I : InjectiveResolution M) :
    (HomotopyCategory.Plus.ι D).obj (F.mapHomotopyCategoryPlus.obj (resolutionPlus I)) ≅
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex) :=
  (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I.cochainComplex

private lemma mappedResolutionQuotientIso_naturality
    {C D : Type*} [Category C] [Abelian C]
    [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] {M N : C}
    {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : I.Hom J f) :
    (HomotopyCategory.Plus.ι D).map (F.mapHomotopyCategoryPlus.map (resolutionPlusMap φ)) ≫
        (mappedResolutionQuotientIso F J).hom =
      (mappedResolutionQuotientIso F I).hom ≫
        (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom') :=
  (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.naturality φ.hom'

private def mappedResolutionHomologyIso
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] {M : C} (I : InjectiveResolution M) (p : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D (p : ℤ)).obj
        (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj (resolutionPlus I))) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology p :=
  (DerivedCategory.homologyFunctor D (p : ℤ)).mapIso
    (DerivedCategory.Qh.mapIso (mappedResolutionQuotientIso F I) ≪≫
      (DerivedCategory.quotientCompQhIso D).app _) ≪≫
    (DerivedCategory.homologyFunctorFactors D (p : ℤ)).app _ ≪≫
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (p : ℤ)).mapIso
      (Stacks.DerivedIndexing.mapExtendIsoSymm F ComplexShape.embeddingUpNat I.cocomplex) ≪≫
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (j := p) (j' := (p : ℤ)) rfl)

private lemma mappedResolutionHomologyIso_naturality
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] {M N : C}
    {I : InjectiveResolution M} {J : InjectiveResolution N}
    {f : M ⟶ N} (φ : I.Hom J f) (p : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D (p : ℤ)).map
        (DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map (resolutionPlusMap φ))) ≫
        (mappedResolutionHomologyIso F J p).hom =
      (mappedResolutionHomologyIso F I p).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ.hom) p := by
  dsimp only [mappedResolutionHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  show (DerivedCategory.homologyFunctor D (p : ℤ)).map
    (DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι D).map
      (F.mapHomotopyCategoryPlus.map (resolutionPlusMap φ)))) ≫ _ = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, mappedResolutionQuotientIso_naturality F φ,
    Functor.map_comp, Functor.map_comp, Category.assoc]
  congr 1
  rw [← Functor.map_comp_assoc, quotientCompQhIso_app_naturality]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [homologyFunctorFactors_app_naturality_assoc (p : ℤ)]
  congr 1
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
    extendHomologyTail_naturality F φ p

private def cohomologyComparisonObj
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (M : C) (p : ℕ) :
    (F.rightDerivedPlus (p : ℤ)).obj M ≅ (F.rightDerived p).obj M :=
  (DerivedCategory.Plus.homologyFunctor D (p : ℤ)).mapIso
      (resolutionDerivedIso F (InjectiveResolution.of M)) ≪≫
    mappedResolutionHomologyIso F (InjectiveResolution.of M) p ≪≫
    ((InjectiveResolution.of M).isoRightDerivedObj F p).symm

private lemma isoRightDerivedObj_inv_naturality'
    {C D : Type*} [Category C] [Abelian C] [EnoughInjectives C] [Category D] [Abelian D]
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (ψ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (I.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map f =
      HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) n ≫
        (J.isoRightDerivedObj F n).inv :=
  InjectiveResolution.isoRightDerivedObj_inv_naturality f I J ψ comm F n

private def cohomologyComparison
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (p : ℕ) :
    F.rightDerivedPlus (p : ℤ) ≅ F.rightDerived p :=
  NatIso.ofComponents (fun M => cohomologyComparisonObj F M p) (by
    intro M N f
    let I := InjectiveResolution.of M
    let J := InjectiveResolution.of N
    let φ : I.Hom J f :=
      { hom := InjectiveResolution.desc f J I
        ι_f_zero_comp_hom_f_zero :=
          (InjectiveResolution.desc_commutes_zero f J I).trans (by simp) }
    dsimp only [cohomologyComparisonObj, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    change (DerivedCategory.Plus.homologyFunctor D (p : ℤ)).map
      (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) ≫ _ = _
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      resolutionDerivedIso_naturality F φ, Functor.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (mappedResolutionHomologyIso_naturality F φ p)]
    rw [← isoRightDerivedObj_inv_naturality' f I J φ.hom
      (φ.ι_f_zero_comp_hom_f_zero.trans (by simp)) F p])


private def cohomologyBoundary
    {A : Type u} [CommRing A]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (G : C ⥤ ModuleCat.{v} A) [G.Additive] [EnoughInjectives C]
    {S : ShortComplex C} (hS : S.ShortExact) (p : ℕ) :
    (G.rightDerived p).obj S.X₃ ⟶ (G.rightDerived (p + 1)).obj S.X₁ :=
  (cohomologyComparison G p).inv.app S.X₃ ≫ derivedCohomologyBoundary G hS p ≫
    (cohomologyComparison G (p + 1)).hom.app S.X₁

private lemma cohomologyBoundary_naturality
    {A : Type u} [CommRing A]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (G : C ⥤ ModuleCat.{v} A) [G.Additive] [EnoughInjectives C]
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (f : S ⟶ T) (p : ℕ) :
    (G.rightDerived p).map f.τ₃ ≫ cohomologyBoundary G hT p =
      cohomologyBoundary G hS p ≫ (G.rightDerived (p + 1)).map f.τ₁ := by
  dsimp only [cohomologyBoundary]
  simp only [Category.assoc]
  rw [(cohomologyComparison G p).inv.naturality_assoc,
    reassoc_of% ((derivedCohomologyBoundary_exact_and_naturality G).2 hS hT f p),
    (cohomologyComparison G (p + 1)).hom.naturality]

private lemma cohomologyBoundary_range_eq_ker
    {A : Type u} [CommRing A]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (G : C ⥤ ModuleCat.{v} A) [G.Additive] [EnoughInjectives C]
    {S : ShortComplex C} (hS : S.ShortExact) (p : ℕ) :
    LinearMap.range ((G.rightDerived p).map S.g).hom =
      LinearMap.ker (cohomologyBoundary G hS p).hom := by
  obtain ⟨hz, hex⟩ := (derivedCohomologyBoundary_exact_and_naturality G).1 hS p
  have hz' : (G.rightDerived p).map S.g ≫ cohomologyBoundary G hS p = 0 := by
    dsimp only [cohomologyBoundary]
    rw [(cohomologyComparison G p).inv.naturality_assoc, ← Category.assoc
      ((G.rightDerivedPlus (p : ℤ)).map S.g), hz, zero_comp, comp_zero]
  apply ShortComplex.Exact.moduleCat_range_eq_ker (S := ShortComplex.mk _ _ hz')
  apply ShortComplex.exact_of_iso _ hex
  refine ShortComplex.isoMk ((cohomologyComparison G p).app S.X₂)
    ((cohomologyComparison G p).app S.X₃)
    ((cohomologyComparison G (p + 1)).app S.X₁) ?_ ?_
  · exact ((cohomologyComparison G p).hom.naturality S.g).symm
  · dsimp only [cohomologyBoundary]
    simp


private theorem exists_exact_cohomologyPlus
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (S : ShortComplex (ModuleSheaf.{u, v, w} A X))
    (hS : S.ShortExact) (p : ℕ) :
    ∃ δ : (((sheafSections (Opens.grothendieckTopology X)
        (ModuleCat.{v} A)).obj (op ⊤)).rightDerivedPlus (p : ℤ)).obj S.X₃ ⟶
        (((sheafSections (Opens.grothendieckTopology X)
        (ModuleCat.{v} A)).obj (op ⊤)).rightDerivedPlus ((p + 1 : ℕ) : ℤ)).obj S.X₁,
      ∃ hδ : (((sheafSections (Opens.grothendieckTopology X)
          (ModuleCat.{v} A)).obj (op ⊤)).rightDerivedPlus (p : ℤ)).map S.g ≫ δ = 0,
        (ShortComplex.mk _ δ hδ).Exact := by
  let G := (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{v} A)).obj (op ⊤)
  obtain ⟨hz, hex⟩ := (derivedCohomologyBoundary_exact_and_naturality G).1 hS p
  exact ⟨derivedCohomologyBoundary G hS p, hz, hex⟩

private theorem exists_exact_cohomologyPlus_quotientStep
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) (n p : ℕ) :
    ∃ δ : (((sheafSections (Opens.grothendieckTopology X)
        (ModuleCat.{v} A)).obj (op ⊤)).rightDerivedPlus (p : ℤ)).obj
          (F.obj (op n)) ⟶
        (((sheafSections (Opens.grothendieckTopology X)
        (ModuleCat.{v} A)).obj (op ⊤)).rightDerivedPlus ((p + 1 : ℕ) : ℤ)).obj
          (powerSheaf I (n + 1) (F.obj (op (n + 1)))),
      ∃ hδ : (((sheafSections (Opens.grothendieckTopology X)
          (ModuleCat.{v} A)).obj (op ⊤)).rightDerivedPlus (p : ℤ)).map
          (F.map (homOfLE (Nat.le_succ n)).op) ≫ δ = 0,
        (ShortComplex.mk _ δ hδ).Exact :=
  exists_exact_cohomologyPlus (quotientTowerStep I n F hquotient)
    (quotientTowerStep_shortExact I n F hquotient) p

/-- Exactness of the derived connecting sequence identifies the image of the
cohomology transition with the kernel of its boundary map. -/
private theorem exists_cohomologyTransition_range_eq_boundary_ker
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) (n p : ℕ) :
    ∃ δ : (((sheafSections (Opens.grothendieckTopology X)
        (ModuleCat.{v} A)).obj (op ⊤)).rightDerivedPlus (p : ℤ)).obj
          (F.obj (op n)) ⟶
        (((sheafSections (Opens.grothendieckTopology X)
        (ModuleCat.{v} A)).obj (op ⊤)).rightDerivedPlus ((p + 1 : ℕ) : ℤ)).obj
          (powerSheaf I (n + 1) (F.obj (op (n + 1)))),
      (((sheafSections (Opens.grothendieckTopology X)
          (ModuleCat.{v} A)).obj (op ⊤)).rightDerivedPlus (p : ℤ)).map
          (F.map (homOfLE (Nat.le_succ n)).op) ≫ δ = 0 ∧
        LinearMap.range
            ((((sheafSections (Opens.grothendieckTopology X)
              (ModuleCat.{v} A)).obj (op ⊤)).rightDerivedPlus (p : ℤ)).map
              (F.map (homOfLE (Nat.le_succ n)).op)).hom =
          LinearMap.ker δ.hom := by
  obtain ⟨δ, hδ, hex⟩ := exists_exact_cohomologyPlus_quotientStep I F hquotient n p
  exact ⟨δ, hδ, ShortComplex.Exact.moduleCat_range_eq_ker hex⟩

private lemma exists_bounded_span {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [IsNoetherian R M] (s : ℕ → Set M) :
    ∃ c : ℕ, Submodule.span R (⋃ n, s n) = Submodule.span R (⋃ n ≤ c, s n) := by
  classical
  obtain ⟨t, ht, he⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (⋃ n, s n)).mp
    (IsNoetherian.noetherian (Submodule.span R (⋃ n, s n)))
  have h : ∀ x : M, ∃ n, x ∈ t → x ∈ s n := by
    intro x
    by_cases hx : x ∈ t
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (ht hx)
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose f hf using h
  let c := t.sup f
  refine ⟨c, le_antisymm ?_ (Submodule.span_mono ?_)⟩
  · rw [he]
    exact Submodule.span_mono fun x hx =>
      Set.mem_iUnion.mpr ⟨f x, Set.mem_iUnion.mpr ⟨Finset.le_sup hx, hf x hx⟩⟩
  · intro x hx
    obtain ⟨n, hn, hx⟩ := Set.mem_iUnion.mp hx |>.imp fun n hn => Set.mem_iUnion.mp hn
    exact Set.mem_iUnion.mpr ⟨n, hx⟩

private lemma mem_of_mem_span_of_smul_mem
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] (f : M →+ N) (K : AddSubmonoid N) {s : Set M}
    (h : ∀ x ∈ s, ∀ a : R, f (a • x) ∈ K) {x : M}
    (hx : x ∈ Submodule.span R s) : f x ∈ K := by
  have hh : ∀ a : R, f (a • x) ∈ K := by
    induction hx using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => intro a; simp
    | add y z hy hz hy' hz' =>
      intro a
      simpa only [smul_add, map_add] using K.add_mem (hy' a) (hz' a)
    | smul a y hy hy' =>
      intro b
      simpa only [smul_smul] using hy' (b * a)
  simpa only [one_smul] using hh 1

private lemma exists_uniform_boundary_correction
    {A R C : Type*} [Semiring A] [Semiring R]
    [AddCommMonoid C] [Module R C] [IsNoetherian R C]
    (M N : ℕ → Type*) [∀ n, AddCommMonoid (M n)] [∀ n, Module A (M n)]
    [∀ n, AddCommMonoid (N n)] [∀ n, Module A (N n)]
    (δ : ∀ n, M n →ₗ[A] N n) (ι : ∀ n, N n →+ C) (π : ∀ n, C →+ N n)
    (hπι : ∀ n x, π n (ι n x) = x)
    (K : ∀ _i n, Submodule A (M n))
    (hkill : ∀ (c i n j : ℕ), c + i + 1 ≤ n → j ≤ c →
      ∀ (x : M j) (a : R), π n (a • ι j (δ j x)) ∈ (K i n).map (δ n)) :
    ∃ c : ℕ, ∀ i n, c + i + 1 ≤ n → ∀ x : M n,
      ∃ y ∈ K i n, δ n y = δ n x := by
  classical
  let s : ℕ → Set C := fun n => Set.range fun x : M n => ι n (δ n x)
  obtain ⟨c, hc⟩ := exists_bounded_span (R := R) s
  refine ⟨c, fun i n hn x => ?_⟩
  have hx : ι n (δ n x) ∈ Submodule.span R (⋃ j ≤ c, s j) := by
    rw [← hc]
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨n, ⟨x, rfl⟩⟩)
  have h : π n (ι n (δ n x)) ∈ (K i n).map (δ n) := by
    apply mem_of_mem_span_of_smul_mem (π n) ((K i n).map (δ n)).toAddSubmonoid
      (s := ⋃ j ≤ c, s j) _ hx
    intro z hz a
    obtain ⟨j, hjc, y, rfl⟩ := Set.mem_iUnion₂.mp hz
    exact hkill c i n j hn hjc y a
  rw [hπι] at h
  exact Submodule.mem_map.mp h

private lemma tower_range_eq_of_boundary_correction
    {A : Type*} [Ring A] (M : ℕᵒᵖ ⥤ ModuleCat A)
    (N : ℕ → Type*) [∀ n, AddCommGroup (N n)] [∀ n, Module A (N n)]
    (δ : ∀ n, M.obj (op n) →ₗ[A] N n)
    (hex : ∀ n, LinearMap.range (M.map (homOfLE (Nat.le_succ n)).op).hom =
      LinearMap.ker (δ n)) (c : ℕ)
    (hc : ∀ i n (h : i + c ≤ n) (x : M.obj (op n)),
      ∃ y : M.obj (op n),
        (M.map (homOfLE ((Nat.le_add_right i c).trans h)).op).hom y = 0 ∧
        δ n y = δ n x) :
    ∀ i m (h : i + c ≤ m),
      LinearMap.range (M.map (homOfLE ((Nat.le_add_right i c).trans h)).op).hom =
      LinearMap.range (M.map (homOfLE (Nat.le_add_right i c)).op).hom := by
  intro i m h
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← ih]
    let t := (M.map (homOfLE (Nat.le_succ n)).op).hom
    let g := (M.map (homOfLE ((Nat.le_add_right i c).trans hn)).op).hom
    have he : (M.map (homOfLE ((Nat.le_add_right i c).trans
        (Nat.le.step hn))).op).hom = g.comp t := by
      rw [map_homOfLE_trans M ((Nat.le_add_right i c).trans hn) (Nat.le_succ n)]
      rfl
    rw [he]
    apply le_antisymm (LinearMap.range_comp_le_range _ _)
    rintro z ⟨x, rfl⟩
    obtain ⟨y, hy, hδ⟩ := hc i n hn x
    have hx : x - y ∈ LinearMap.range t := by
      rw [hex]
      show δ n (x - y) = 0
      rw [map_sub, hδ, sub_self]
    obtain ⟨w, hw⟩ := hx
    refine ⟨w, ?_⟩
    show g (t w) = g x
    rw [hw, map_sub]
    show g x - (M.map _).hom y = g x
    rw [hy, sub_zero]

private lemma rightDerived_map_zero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [EnoughInjectives C] (G : C ⥤ D) [G.Additive] (p : ℕ) (M N : C) :
    (G.rightDerived p).map (0 : M ⟶ N) = 0 := by
  rw [G.rightDerived_map_eq p 0
    (0 : (InjectiveResolution.of M).cocomplex ⟶ (InjectiveResolution.of N).cocomplex)
    (by simp)]
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_zero,
    HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_zero,
    Preadditive.IsIso.comp_left_eq_zero]
  exact zero_comp

private lemma uniform_correction_of_boundary
    {A : Type u} [CommRing A] [Small.{v} A]
    {X : Type w} [TopologicalSpace X] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hF : IsQuotientTower I F) (p : ℕ)
    (δ : ∀ (S : ShortComplex (ModuleSheaf.{u, v, w} A X)), S.ShortExact →
      ((cohomology p).obj S.X₃ ⟶ (cohomology (p + 1)).obj S.X₁))
    (hδ : ∀ (S T : ShortComplex (ModuleSheaf.{u, v, w} A X))
      (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T),
      (cohomology p).map f.τ₃ ≫ δ T hT =
        δ S hS ≫ (cohomology (p + 1)).map f.τ₁)
    (hACC : StableImagesHaveGradedACC I F (p + 1)) :
    ∃ c : ℕ, ∀ i n (h : i + c ≤ n)
      (x : (cohomology p).obj (F.obj (op n))),
      ∃ y : (cohomology p).obj (F.obj (op n)),
        ((cohomology p).map
          (F.map (homOfLE ((Nat.le_add_right i c).trans h)).op)).hom y = 0 ∧
        (δ (quotientTowerInterval I F hF n (n + 1) (Nat.le_succ n))
          (quotientTowerInterval_shortExact I F hF n (n + 1) (Nat.le_succ n))).hom y =
        (δ (quotientTowerInterval I F hF n (n + 1) (Nat.le_succ n))
          (quotientTowerInterval_shortExact I F hF n (n + 1) (Nat.le_succ n))).hom x := by
  classical
  obtain ⟨action, haction, hnoeth⟩ := hACC
  let := action
  let := hnoeth
  let H := cohomology (A := A) (X := X) p
  let M := fun n => H.obj (F.obj (op n))
  let N := fun n => stableImage I F (p + 1) (n + 1)
  let b := fun n => (δ (quotientTowerInterval I F hF n (n + 1) (Nat.le_succ n))
    (quotientTowerInterval_shortExact I F hF n (n + 1) (Nat.le_succ n))).hom
  let d : ∀ n, M n →ₗ[A] N n := fun n => (b n).codRestrict (N n)
    (quotientBoundary_mem_stableImage I F hF p δ hδ n)
  let C := StableImageSum I F (p + 1)
  let ι : ∀ n, N n →+ C := fun n =>
    DirectSum.of (fun i => stableImage I F (p + 1) i) (n + 1)
  let π : ∀ n, C →+ N n := fun n => (DirectSum.component A ℕ _ (n + 1)).toAddMonoidHom
  let K : ∀ i n, Submodule A (M n) := fun i n =>
    if h : i ≤ n then LinearMap.ker (H.map (F.map (homOfLE h).op)).hom else ⊤
  have hπι : ∀ n x, π n (ι n x) = x := by
    intro n x
    show (DirectSum.of (fun i => stableImage I F (p + 1) i) (n + 1) x) (n + 1) = x
    exact DirectSum.of_eq_same _ _
  have hkill : ∀ (c i n j : ℕ), c + i + 1 ≤ n → j ≤ c →
      ∀ (x : M j) (a : AssociatedGraded.gradedRing I),
        π n (a • ι j (d j x)) ∈ (K i n).map (d n) := by
    intro c i n j hn hj x a
    induction a using DirectSum.induction_on with
    | zero =>
      rw [show (0 : AssociatedGraded.gradedRing I) • ι j (d j x) = 0 from
        Module.zero_smul (R := AssociatedGraded.gradedRing I) (ι j (d j x)), map_zero]
      exact Submodule.zero_mem _
    | add a a' ha ha' =>
      rw [show (a + a') • ι j (d j x) = a • ι j (d j x) + a' • ι j (d j x)
        from add_smul _ _ _, map_add]
      exact Submodule.add_mem _ ha ha'
    | of k a =>
      induction a using Quotient.inductionOn with
      | h a =>
        let a' : ↥(I ^ k) := ⟨a.1, by simpa only [AssociatedGraded.ring_power_eq] using a.2⟩
        obtain ⟨g, hg⟩ := quotientTower_exists_scalar_lift I F hF j (k + j)
          (Nat.le_add_left j k) a'.1 (by simp)
        have he := quotientBoundary_smul I F hF p δ hδ haction j k a' x g hg
        have heval := congrArg (fun z => z (n + 1)) he
        rw [stableImageSumι_apply] at heval
        change (π n (DirectSum.of _ k (AssociatedGraded.mk I k a) • ι j (d j x))).1 =
          (DirectSum.of (fun i => (cohomology (p + 1)).obj
            (powerSheaf I i (F.obj (op i)))) (k + j + 1)
              (b (k + j) ((H.map g).hom x))) (n + 1) at heval
        by_cases hkn : k + j = n
        · subst n
          refine Submodule.mem_map.mpr ⟨(H.map g).hom x, ?_, ?_⟩
          · dsimp only [K]
            rw [dite_eq_left (by omega)]
            show (H.map (F.map (homOfLE (show i ≤ k + j by omega)).op)).hom
              ((H.map g).hom x) = 0
            have hz := quotientTower_scalar_lift_comp_eq_zero I F hF j (k + j) i
              (Nat.le_add_left j k) (by omega) a'.1
              (Ideal.pow_le_pow_right (by omega : i + 1 ≤ k) a'.2) g hg
            show (H.map g ≫ H.map (F.map (homOfLE (show i ≤ k + j by omega)).op)).hom x = 0
            rw [← H.map_comp, hz]
            have hz' : H.map (0 : F.obj (op j) ⟶ F.obj (op i)) = 0 :=
              rightDerived_map_zero ((sheafSections (Opens.grothendieckTopology X)
                (ModuleCat.{v} A)).obj (op ⊤)) p _ _
            exact congrArg (fun t => t.hom x) hz'
          · apply Subtype.ext
            show b (k + j) ((H.map g).hom x) =
              (π (k + j) (DirectSum.of _ k (AssociatedGraded.mk I k a) • ι j (d j x))).1
            simpa only [DirectSum.of_eq_same] using heval.symm
        · have hz : π n (DirectSum.of _ k (AssociatedGraded.mk I k a) • ι j (d j x)) = 0 := by
            apply Subtype.ext
            show (π n (DirectSum.of _ k (AssociatedGraded.mk I k a) • ι j (d j x))).1 = 0
            simpa [DirectSum.of_apply, hkn] using heval
          rw [show (⟦a⟧ : AssociatedGraded.piece (M := A) I k) =
            AssociatedGraded.mk I k a from rfl, hz]
          exact Submodule.zero_mem _
  obtain ⟨c, hc⟩ :=
    exists_uniform_boundary_correction (fun n => M n) (fun n => N n) d ι π hπι K hkill
  refine ⟨c + 1, fun i n h x => ?_⟩
  obtain ⟨y, hy, hd⟩ := hc i n (by omega) x
  refine ⟨y, ?_, congrArg Subtype.val hd⟩
  simpa only [K, dite_eq_left (show i ≤ n by omega), LinearMap.mem_ker] using hy


private lemma image_eq_of_range_eq {R : Type*} [Ring R]
    {L M N : ModuleCat R} (f : L ⟶ N) (g : M ⟶ N)
    (h : LinearMap.range f.hom = LinearMap.range g.hom) :
    Subobject.mk (image.ι f) = Subobject.mk (image.ι g) := by
  have hf : Subobject.mk (image.ι f) =
      Subobject.mk (ModuleCat.ofHom (LinearMap.range f.hom).subtype) :=
    Subobject.mk_eq_mk_of_comm _ _ (ModuleCat.imageIsoRange f)
      (ModuleCat.imageIsoRange_hom_subtype f)
  have hg : Subobject.mk (image.ι g) =
      Subobject.mk (ModuleCat.ofHom (LinearMap.range g.hom).subtype) :=
    Subobject.mk_eq_mk_of_comm _ _ (ModuleCat.imageIsoRange g)
      (ModuleCat.imageIsoRange_hom_subtype g)
  rw [hf, hg, h]

/-- Under the same hypotheses, there is a single lag `c` such that, for every
`i`, the image of `Hᵖ(F_(i+c+1)) → Hᵖ(F_(i+1))` is already the stable image. -/
@[stacks 0GYL "uniform stabilization (footnote)"]
public theorem cohomology_transitionImage_stable_uniformly
    {A : Type u} [CommRing A] [Small.{v} A] (I : Ideal A)
    {X : Type w} [TopologicalSpace X]
    [UnivLE.{max w v, v}]
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower.{u, v, w} I F)
    (hACC : StableImagesHaveGradedACC.{u, v, w} I F (p + 1)) :
    ∃ c : ℕ, ∀ (i m : ℕ) (h : i + c ≤ m),
      transitionImage (F ⋙ cohomology.{u, v, w} (A := A) (X := X) p)
        i m ((Nat.le_add_right i c).trans h) =
      transitionImage (F ⋙ cohomology.{u, v, w} (A := A) (X := X) p)
        i (i + c) (Nat.le_add_right i c) := by
  let G := (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{v} A)).obj (op ⊤)
  let δ := fun (S : ShortComplex (ModuleSheaf.{u, v, w} A X))
    (hS : S.ShortExact) => cohomologyBoundary G hS p
  have hδ : ∀ (S T : ShortComplex (ModuleSheaf.{u, v, w} A X))
      (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T),
      (cohomology p).map f.τ₃ ≫ δ T hT =
        δ S hS ≫ (cohomology (p + 1)).map f.τ₁ :=
    fun S T hS hT f => cohomologyBoundary_naturality G hS hT f p
  let M := F ⋙ cohomology (A := A) (X := X) p
  let N : ℕ → Type v := fun n => (cohomology (A := A) (X := X) (p + 1)).obj
    (powerSheaf I (n + 1) (F.obj (op (n + 1))))
  let b : ∀ n, M.obj (op n) →ₗ[A] N n := fun n =>
    (δ (quotientTowerInterval I F hquotient n (n + 1) (Nat.le_succ n))
      (quotientTowerInterval_shortExact I F hquotient n (n + 1) (Nat.le_succ n))).hom
  have hex : ∀ n, LinearMap.range (M.map (homOfLE (Nat.le_succ n)).op).hom =
      LinearMap.ker (b n) := fun n => cohomologyBoundary_range_eq_ker G
        (quotientTowerInterval_shortExact I F hquotient n (n + 1) (Nat.le_succ n)) p
  obtain ⟨c, hc⟩ := uniform_correction_of_boundary I F hquotient p δ hδ hACC
  refine ⟨c, fun i m h => ?_⟩
  apply image_eq_of_range_eq
  exact tower_range_eq_of_boundary_correction M N b hex c hc i m h

/-- If the stable images in degree `p + 1` satisfy graded ACC, the
degree-`p` cohomology tower of an ideal-power quotient system satisfies the
Mittag-Leffler condition. -/
@[stacks 0GYL "Mittag-Leffler condition"]
public theorem isMittagLeffler_cohomology_of_stableImagesGradedACC
    {A : Type u} [CommRing A] [Small.{v} A] (I : Ideal A)
    {X : Type w} [TopologicalSpace X]
    [UnivLE.{max w v, v}]
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower.{u, v, w} I F)
    (hACC : StableImagesHaveGradedACC.{u, v, w} I F (p + 1)) :
    IsMittagLefflerCategorical
      (F ⋙ cohomology.{u, v, w} (A := A) (X := X) p) := by
  obtain ⟨c, hc⟩ := cohomology_transitionImage_stable_uniformly I F p hquotient hACC
  intro i
  refine ⟨i + c, Nat.le_add_right i c, ?_⟩
  intro k hck
  exact hc i k hck

end Stacks.Cohomology.MittagLefflerCohomology

end
