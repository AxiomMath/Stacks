module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import StacksFrontier.CategoryTheory.Sites.Continuous.ContinuousDefs
import StacksCore.Tactic.StacksAttribute

/-! # Covering pullbacks of a functor of sites

A site in the sense of Stacks 00VH has, for every covering arrow `f : V ⟶ U` and every arrow
`g : W ⟶ U`, the fibre product `V ×_U W`; and a continuous functor of sites in the sense of
Stacks 00WV preserves those fibre products. Mathlib's `GrothendieckTopology` records neither:
a topology is a collection of sieves, and `Functor.IsContinuous` records only that the functor
takes sheaves to sheaves. The class below records exactly the missing data — covering families,
cofinal in the topology, whose arrows admit those pullbacks and whose pullbacks the functor
preserves — without demanding all pullbacks in the source category or preservation of all
fibre products.

What makes the condition usable is that it gives all the *iterated* fibre products
`V_{i_0} ×_U … ×_U V_{i_n}` of such a family, and their preservation: these are products in
the over-category `Over U`, they are built from the binary ones by induction, and the functor
`Over.post u` preserves them. That is the shape in which the Čech machinery of Chapter 21 and
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero` (Stacks 03F9) ask for them.

## Main definitions

* `Stacks.Sites.PreservesCoveringPullbacks`: the covering-pullback clause of Stacks continuity,
  expressed on a cofinal family of coverings of a Grothendieck topology.

## Main results

* `Stacks.Sites.hasBinaryProduct_over_of_hasPullback`: one pullback in the base gives one
  binary product in the over-category.
* `Stacks.Sites.preservesLimit_pair_overPost`: if `u` preserves one pullback square then
  `Over.post u` preserves the corresponding binary product.
* `Stacks.Sites.hasProduct_over_fin` and `Stacks.Sites.preservesLimit_discrete_overPost_fin`:
  the same for a finite nonempty family, by induction on its length.
* `Stacks.Sites.hasProduct_fibreProducts` and
  `Stacks.Sites.preservesLimit_fibreProducts_overPost`: the iterated fibre products of a
  covering family, in the form the Čech complex of Stacks 03AM takes them.
* `Stacks.Sites.exists_preZeroHypercover_le`: every covering sieve is refined by a covering
  family with those pullbacks, so the families form a cofinal system.

## Implementation notes

The one-element case of the induction is `CategoryTheory.Limits.hasProduct_unique`, and every
functor preserves such a product because the single projection is an isomorphism
(`preservesLimit_discrete_of_unique`); this avoids having to carry a terminal object of
`Over U`. The inductive step is Mathlib's `extendFan`/`extendFanIsLimit` together with
`CategoryTheory.Limits.pullbackConeEquivBinaryFan`, which is the per-pullback form of
"products in `Over U` are wide pullbacks in `C`".

Because `Presieve.preZeroHypercover` indexes a presieve by its own arrows, the covering
families produced by `exists_preZeroHypercover_le` have index type in `max u₁ v₁`.

## References

* [Stacks Project, Tag 00VH](https://stacks.math.columbia.edu/tag/00VH)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

universe w v₁ u₁ v₂ u₂

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-! ### Products in an over-category from single pullbacks -/

/-- A single pullback in the base gives a single binary product in the over-category. This is
the per-pullback form of `CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback`,
which assumes all pullbacks in the base. -/
theorem hasBinaryProduct_over_of_hasPullback {U : C} (Y Z : Over U)
    (hpb : HasPullback Y.hom Z.hom) : HasBinaryProduct Y Z :=
  have := hpb
  HasLimit.mk ⟨pullbackConeEquivBinaryFan.functor.obj (pullback.cone Y.hom Z.hom),
    (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor⟩

/-- If `u` preserves one pullback square, then `Over.post u` preserves the corresponding
binary product in the over-category. -/
theorem preservesLimit_pair_overPost {U : C} (u : C ⥤ D) (Y Z : Over U)
    (hpb : HasPullback Y.hom Z.hom) (hpr : PreservesLimit (cospan Y.hom Z.hom) u) :
    PreservesLimit (pair Y Z) (Over.post u) := by
  have := hpb
  have := hpr
  refine preservesLimit_of_preserves_limit_cone
    ((pullback.isLimit Y.hom Z.hom).pullbackConeEquivBinaryFanFunctor) ?_
  refine (isLimitMapConeBinaryFanEquiv (Over.post u) _ _).symm ?_
  refine IsLimit.ofIsoLimit (IsLimit.pullbackConeEquivBinaryFanFunctor
      (isLimitOfHasPullbackOfPreservesLimit u Y.hom Z.hom)) (BinaryFan.ext ?_ ?_ ?_)
  · exact Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (u.map_comp _ _))
  · exact Over.OverMorphism.ext (Category.id_comp _).symm
  · exact Over.OverMorphism.ext (Category.id_comp _).symm

/-- Any functor preserves a product indexed by a type with exactly one element: the single
projection out of such a product is an isomorphism, hence so is the comparison map. -/
theorem preservesLimit_discrete_of_unique {β : Type*} [Unique β]
    {A : Type*} [Category A] {B : Type*} [Category B] (f : β → A) (F : A ⥤ B) :
    PreservesLimit (Discrete.functor f) F := by
  have : IsIso (Pi.π f default) := by
    rw [← productUniqueIso_hom]; infer_instance
  have : IsIso (Pi.π (fun j => F.obj (f j)) default) := by
    rw [← productUniqueIso_hom]; infer_instance
  have : IsIso (piComparison F f ≫ Pi.π (fun j => F.obj (f j)) default) := by
    rw [piComparison_comp_π]; infer_instance
  have : IsIso (piComparison F f) :=
    IsIso.of_isIso_comp_right (piComparison F f) (Pi.π (fun j => F.obj (f j)) default)
  exact PreservesProduct.of_iso_comparison F f

/-- The head of a family in an over-category has a binary product with the product of its tail,
provided the head's structure morphism admits pullbacks. -/
private theorem hasBinaryProduct_head_tail {U : C} {n : ℕ} (A : Fin (n + 2) → Over U)
    (_ : HasProduct fun i : Fin (n + 1) => A i.succ)
    (h : ∀ (a : Fin (n + 2)) ⦃W : C⦄ (g : W ⟶ U), HasPullback (A a).hom g) :
    HasBinaryProduct (A 0) (∏ᶜ fun i : Fin (n + 1) => A i.succ) :=
  hasBinaryProduct_over_of_hasPullback _ _ (h 0 _)

/-- Products of a finite nonempty family in an over-category exist as soon as the structure
morphisms of the family admit pullbacks against arbitrary morphisms to the base. -/
theorem hasProduct_over_fin {U : C} :
    ∀ (n : ℕ) (A : Fin (n + 1) → Over U),
      (∀ (a : Fin (n + 1)) ⦃W : C⦄ (g : W ⟶ U), HasPullback (A a).hom g) →
      HasProduct A := by
  intro n
  induction n with
  | zero =>
    intro A _
    have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    exact hasProduct_unique A
  | succ n ih =>
    intro A h
    have hprod : HasProduct (fun i : Fin (n + 1) => A i.succ) :=
      ih _ (fun a _ g => h a.succ g)
    have hbp := hasBinaryProduct_head_tail A hprod h
    have hP := prodIsProd (A 0) (∏ᶜ fun i : Fin (n + 1) => A i.succ)
    exact HasLimit.mk ⟨_, extendFanIsLimit A (productIsProduct _) hP⟩

/-- If `u` preserves the pullbacks of the structure morphisms of a finite nonempty family in an
over-category against arbitrary morphisms to the base, then `Over.post u` preserves the product
of that family. -/
theorem preservesLimit_discrete_overPost_fin {U : C} (u : C ⥤ D) :
    ∀ (n : ℕ) (A : Fin (n + 1) → Over U)
      (_ : ∀ (a : Fin (n + 1)) ⦃W : C⦄ (g : W ⟶ U), HasPullback (A a).hom g)
      (_ : ∀ (a : Fin (n + 1)) ⦃W : C⦄ (g : W ⟶ U), PreservesLimit (cospan (A a).hom g) u),
      PreservesLimit (Discrete.functor A) (Over.post u) := by
  intro n
  induction n with
  | zero =>
    intro A _ _
    have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    exact preservesLimit_discrete_of_unique A (Over.post u)
  | succ n ih =>
    intro A h hp
    have hprod : HasProduct (fun i : Fin (n + 1) => A i.succ) :=
      hasProduct_over_fin n _ (fun a _ g => h a.succ g)
    have hbp := hasBinaryProduct_head_tail A hprod h
    have ihP : PreservesLimit (Discrete.functor (fun i : Fin (n + 1) => A i.succ))
        (Over.post u) :=
      ih _ (fun a _ g => h a.succ g) (fun a _ g => hp a.succ g)
    have hpair := preservesLimit_pair_overPost u (A 0) (∏ᶜ fun i : Fin (n + 1) => A i.succ)
      (h 0 _) (hp 0 _)
    have hP := prodIsProd (A 0) (∏ᶜ fun i : Fin (n + 1) => A i.succ)
    refine preservesLimit_of_preserves_limit_cone
      (extendFanIsLimit A (productIsProduct _) hP) ?_
    refine (isLimitMapConeFanMkEquiv (Over.post u) A _).symm ?_
    have t₁' := isLimitOfHasProductOfPreservesLimit (Over.post u)
      (fun i : Fin (n + 1) => A i.succ)
    have t₂' := isLimitMapConeBinaryFanEquiv (Over.post u) _ _
      (isLimitOfPreserves (Over.post u) hP)
    refine IsLimit.ofIsoLimit (extendFanIsLimit (fun a => (Over.post u).obj (A a)) t₁' t₂')
      (Cone.ext (Iso.refl _) ?_)
    rintro ⟨j⟩
    induction j using Fin.cases with
    | zero => exact (Category.id_comp _).symm
    | succ i =>
      apply Over.OverMorphism.ext
      exact ((u.map_comp _ _).symm.trans (Category.id_comp _).symm)

/-! ### The covering-pullback condition on a functor of sites -/

/-- The covering-pullback clause of Stacks continuity (Stacks 00VH and 00WV). Every covering
sieve contains a covering family whose arrows admit pullback along every arrow to the same
base, and these pullbacks are preserved by `u`. The cofinal formulation depends only on the
Grothendieck topology, rather than on a choice of covering families presenting it, and it
demands neither all pullbacks in `C` nor preservation of all fibre products by `u`. -/
class PreservesCoveringPullbacks (J : GrothendieckTopology C) (u : C ⥤ D) : Prop where
  /-- Cofinal coverings with the pullbacks required by Stacks 00VH and 00WV. -/
  exists_cover : ∀ (U : C) (S : Sieve U), S ∈ J U →
    ∃ (R : Presieve U), Sieve.generate R ∈ J U ∧ R ≤ S.arrows ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), R f → ∀ ⦃W : C⦄ (g : W ⟶ U),
        HasPullback f g ∧ PreservesLimit (cospan f g) u

/-- Preservation of all pullbacks supplies the covering-pullback clause of continuity. -/
instance (J : GrothendieckTopology C) (u : C ⥤ D)
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    PreservesCoveringPullbacks J u where
  exists_cover U S hS := ⟨S.arrows, by simpa using hS, le_rfl,
    fun _ _ _ _ _ => ⟨inferInstance, inferInstance⟩⟩

/-- The project's pretopological definition of Stacks continuity (Stacks 00WV) supplies the
covering pullbacks used here. -/
theorem preservesCoveringPullbacks_of_isContinuous [HasPullbacks C] [HasPullbacks D]
    (P : Pretopology C) (Q : Pretopology D) (u : C ⥤ D)
    (h : StacksContinuousFunctor.IsContinuous u P Q) :
    PreservesCoveringPullbacks P.toGrothendieck u := by
  refine ⟨fun U S hS => ?_⟩
  obtain ⟨R, hR, hRS⟩ := hS
  refine ⟨R, ⟨R, hR, Sieve.le_generate R⟩, hRS, fun _ f hf _ g => ⟨inferInstance, ?_⟩⟩
  have := h.pullback_iso hR hf g
  have : PreservesLimit (cospan g f) u := PreservesPullback.of_iso_comparison u
  exact preservesPullback_symmetry u g f

/-! ### The iterated fibre products of a covering family -/

variable {U : C}

/-- The iterated fibre products of a covering family all of whose arrows admit pullbacks
against arbitrary morphisms to the base exist. This is the instance argument that the Čech
complex of Stacks 03AM and the criterion of Stacks 03F9 take as a hypothesis. -/
theorem hasProduct_fibreProducts (E : PreZeroHypercover.{w} U)
    (h : ∀ (j : E.I₀) ⦃W : C⦄ (g : W ⟶ U), HasPullback (E.f j) g)
    (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    HasProduct (fun a ↦ Over.mk (E.f (i a))) :=
  hasProduct_over_fin n _ (fun a _ g => h (i a) g)

/-- `Over.post u` preserves the iterated fibre products of a covering family whose binary
covering pullbacks `u` preserves. This is what identifies the Čech complex of a restricted
presheaf along `u` with the Čech complex of the image family. -/
theorem preservesLimit_fibreProducts_overPost (u : C ⥤ D) (E : PreZeroHypercover.{w} U)
    (h : ∀ (j : E.I₀) ⦃W : C⦄ (g : W ⟶ U), HasPullback (E.f j) g)
    (hp : ∀ (j : E.I₀) ⦃W : C⦄ (g : W ⟶ U), PreservesLimit (cospan (E.f j) g) u)
    (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.f (i a)))) (Over.post u) :=
  preservesLimit_discrete_overPost_fin u n _ (fun a _ g => h (i a) g) (fun a _ g => hp (i a) g)

/-- Under the covering-pullback condition, every covering sieve is refined by a covering family
whose arrows admit pullbacks against arbitrary morphisms to the base, preserved by `u`. So
those families form a cofinal system of coverings, which is the hypothesis `hCovCofinal` of
Stacks 03F9. -/
theorem exists_preZeroHypercover_le (J : GrothendieckTopology C) (u : C ⥤ D)
    [PreservesCoveringPullbacks J u] (S : Sieve U) (hS : S ∈ J U) :
    ∃ E : PreZeroHypercover.{max u₁ v₁} U, E.sieve₀ ∈ J U ∧ E.sieve₀ ≤ S ∧
      (∀ (j : E.I₀) ⦃W : C⦄ (g : W ⟶ U), HasPullback (E.f j) g) ∧
      (∀ (j : E.I₀) ⦃W : C⦄ (g : W ⟶ U), PreservesLimit (cospan (E.f j) g) u) := by
  obtain ⟨R, hRJ, hRS, hpb⟩ := PreservesCoveringPullbacks.exists_cover (u := u) U S hS
  have hRmem : ∀ j : R.preZeroHypercover.I₀, R (R.preZeroHypercover.f j) := fun j => j.2
  have hsieve : R.preZeroHypercover.sieve₀ = Sieve.generate R := by
    rw [show R.preZeroHypercover.sieve₀ = Sieve.generate R.preZeroHypercover.presieve₀ from rfl,
      Presieve.presieve₀_preZeroHypercover]
  refine ⟨R.preZeroHypercover, hsieve ▸ hRJ, ?_, fun j _ g => (hpb _ (hRmem j) g).1,
    fun j _ g => (hpb _ (hRmem j) g).2⟩
  rwa [hsieve, Sieve.generate_le_iff]

end Stacks.Sites

end
