module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.TensorProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finitely presented modules over a filtered colimit of rings

Let `G : K ⥤ CommRingCat` be a filtered diagram of commutative rings with a colimit cocone
`d`.  This file proves that every finitely presented `d.pt`-module is the base change of a
finitely presented `G.obj k`-module for some `k`.

## Main definitions

* `Stacks.RingFilteredColimits.img`: the image of a leg of a cocone of commutative rings, as
  a subring of the apex.
* `Stacks.ModuleDescent.relA` and `Stacks.ModuleDescent.relB`: a finite family of relations
  `w₀ : Fin m → (Fin n → A)` spans a submodule of `Fin n → A`, and its image spans a submodule
  of `Fin n → B`.
* `Stacks.ModuleDescent.descentEquiv`: the resulting comparison
  `B ⊗[A] ((Fin n → A) ⧸ relA w₀) ≃ₗ[B] (Fin n → B) ⧸ relB B w₀`.

## Main results

* `Stacks.RingFilteredColimits.exists_mem_range_of_isColimit`: the legs of a colimit cocone of a
  filtered diagram of commutative rings are jointly surjective.
* `Stacks.RingFilteredColimits.exists_forall_mem_img`: finitely many elements of the colimit
  all come from a single stage.
* `Stacks.ModuleDescent.exists_extendScalars_iso_of_isColimit`: a finitely presented module over a
  filtered colimit of rings is the extension of scalars of a finitely presented module at
  some stage.

## Implementation notes

No statement here is about a *constructed* colimit, so the index category need not be small:
its objects and morphisms live in universes unrelated to the universe of the rings.  For such a
shape `K` Mathlib records neither `HasColimitsOfShape K CommRingCat.{u}` nor
`PreservesColimitsOfShape K (forget CommRingCat.{u})`.

Consequently joint surjectivity is proved through the universal property rather than through a
description of the underlying set of the colimit: the legs corestrict to the supremum of their
images, which is a second cocone, so the universal property retracts the inclusion of that
supremum.  Filteredness makes the images directed, and `Subring.mem_iSup_of_directed` turns the
supremum back into the union.

The comparison `descentEquiv` is built by hand from the two maps `theta` and `psibar` rather
than from `TensorProduct.lTensor.equiv`, because the latter is only linear over the base ring
`A` while the statement needs an isomorphism of `B`-modules.  Both composites are checked on
the generators `Pi.single k 1`, the only computation being
`psi_algebraMap`: the image under `psi` of a tuple of elements of `A` is `1 ⊗ₜ` its class.

## References

* [Stacks Project, Tag 05N7](https://stacks.math.columbia.edu/tag/05N7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe v u w

namespace Stacks

/-! ### Joint surjectivity of a filtered colimit of commutative rings -/

namespace RingFilteredColimits

variable {K : Type w} [Category.{v} K] {G : K ⥤ CommRingCat.{u}}

/-- The image of the leg of a cocone of commutative rings, as a subring of the apex. -/
def img (d : Cocone G) (k : K) : Subring d.pt := (d.ι.app k).hom.range

/-- The image of an element under the leg `d.ι.app k` lies in `img d k`. -/
lemma mem_img (d : Cocone G) (k : K) (y : G.obj k) : d.ι.app k y ∈ img d k := ⟨y, rfl⟩

/-- A leg of a cocone is compatible with the transition maps of the diagram, elementwise. -/
private lemma app_map_apply (d : Cocone G) {k l : K} (f : k ⟶ l) (y : G.obj k) :
    d.ι.app l (G.map f y) = d.ι.app k y := by
  rw [← ConcreteCategory.comp_apply, d.w]

/-- The leg of a cocone, corestricted to the supremum of the images of all the legs. -/
def legRange (d : Cocone G) (k : K) :
    G.obj k ⟶ CommRingCat.of (⨆ k, img d k : Subring d.pt) :=
  CommRingCat.ofHom
    { toFun y := ⟨d.ι.app k y, le_iSup (img d) k (mem_img d k y)⟩
      map_one' := by apply Subtype.ext; exact map_one _
      map_mul' _ _ := by apply Subtype.ext; exact map_mul _ _ _
      map_zero' := by apply Subtype.ext; exact map_zero _
      map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _ }

/-- The corestricted legs `legRange d` are compatible with the transition maps of `G`. -/
lemma legRange_naturality (d : Cocone G) {k l : K} (f : k ⟶ l) :
    G.map f ≫ legRange d l = legRange d k := by
  ext y
  exact app_map_apply d f y

/-- The cocone whose apex is the supremum of the images of the legs of `d`. -/
def coconeRange (d : Cocone G) : Cocone G where
  pt := CommRingCat.of (⨆ k, img d k : Subring d.pt)
  ι :=
    { app := legRange d
      naturality := fun _ _ f => by simpa using legRange_naturality d f }

/-- The inclusion of the supremum of the images of the legs of `d` into the apex of `d`. -/
def inclRange (d : Cocone G) : (coconeRange d).pt ⟶ d.pt :=
  CommRingCat.ofHom (⨆ k, img d k : Subring d.pt).subtype

/-- The legs of a colimit cocone of commutative rings are jointly surjective. -/
lemma iSup_img_eq_top {d : Cocone G} (hd : IsColimit d) :
    (⨆ k, img d k) = (⊤ : Subring d.pt) := by
  have key : hd.desc (coconeRange d) ≫ inclRange d = CategoryStruct.id d.pt := by
    refine hd.hom_ext fun k => ?_
    rw [← Category.assoc, hd.fac, Category.comp_id]
    rfl
  rw [eq_top_iff]
  intro x _
  have h := ConcreteCategory.congr_hom key x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
  exact h ▸ (hd.desc (coconeRange d) x).2

variable [IsFiltered K]

/-- Over a filtered index category, the images of the legs of a cocone form a directed family
of subrings. -/
lemma directed_img (d : Cocone G) : Directed (· ≤ ·) (img d) := by
  intro k l
  refine ⟨IsFiltered.max k l, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨G.map (IsFiltered.leftToMax k l) y, app_map_apply d _ y⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨G.map (IsFiltered.rightToMax k l) y, app_map_apply d _ y⟩

/-- Every element of a filtered colimit of commutative rings lies in the image of some leg. -/
private lemma exists_mem_img {d : Cocone G} (hd : IsColimit d) (x : d.pt) :
    ∃ k : K, x ∈ img d k := by
  have : Nonempty K := IsFiltered.nonempty
  have hx : x ∈ (⨆ k, img d k) := by rw [iSup_img_eq_top hd]; trivial
  exact (Subring.mem_iSup_of_directed (directed_img d)).1 hx

/-- Every element of a filtered colimit of commutative rings comes from some stage. -/
lemma exists_mem_range_of_isColimit {d : Cocone G} (hd : IsColimit d) (x : d.pt) :
    ∃ (k : K) (y : G.obj k), d.ι.app k y = x :=
  (exists_mem_img hd x).imp fun _ hk => hk

/-- Finitely many elements of a filtered colimit of commutative rings all come from a single
stage. -/
lemma exists_forall_mem_img {κ : Type*} [Finite κ] {d : Cocone G} (hd : IsColimit d)
    (x : κ → d.pt) : ∃ k : K, ∀ j, x j ∈ img d k := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  choose kk hkk using fun j => exists_mem_img hd (x j)
  obtain ⟨m, hm⟩ := IsFiltered.sup_objs_exists (Finset.image kk Finset.univ)
  have f : ∀ j : κ, kk j ⟶ m := fun j =>
    (hm (Finset.mem_image_of_mem kk (Finset.mem_univ j))).some
  refine ⟨m, fun j => ?_⟩
  obtain ⟨y, hy⟩ := hkk j
  exact ⟨G.map (f j) y, by rw [app_map_apply, hy]⟩

end RingFilteredColimits

/-! ### Base change of a presentation by a finite family of relations -/

namespace ModuleDescent

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
variable {n m : ℕ} (w₀ : Fin m → (Fin n → A))

/-- The submodule of `Fin n → A` spanned by a finite family of relations. -/
def relA : Submodule A (Fin n → A) := Submodule.span A (Set.range w₀)

/-- The submodule of `Fin n → B` spanned by the image of a finite family of relations. -/
def relB : Submodule B (Fin n → B) :=
  Submodule.span B (Set.range fun (j : Fin m) (k : Fin n) => algebraMap A B (w₀ j k))

/-- The `B`-linear map `(Fin n → B) → B ⊗[A] ((Fin n → A) ⧸ relA w₀)` sending `b` to
`∑ k, b k ⊗ₜ [Pi.single k 1]`. -/
noncomputable def psi : (Fin n → B) →ₗ[B] B ⊗[A] ((Fin n → A) ⧸ relA w₀) where
  toFun b := ∑ k, b k ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single k 1) : ((Fin n → A) ⧸ relA w₀))
  map_add' x y := by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum, TensorProduct.smul_tmul']

/-- The class of `a` in a quotient of `Fin n → R` is `∑ k, a k • [Pi.single k 1]`. -/
lemma mkQ_eq_sum_single {R : Type*} [CommRing R] (p : Submodule R (Fin n → R))
    (a : Fin n → R) : p.mkQ a = ∑ k, a k • p.mkQ (Pi.single k 1) := by
  simp only [← map_smul, ← map_sum]
  congr 1
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

/-- `psi` sends the image in `Fin n → B` of a tuple `a : Fin n → A` to `1 ⊗ₜ [a]`. -/
lemma psi_algebraMap (a : Fin n → A) :
    psi B w₀ (fun k => algebraMap A B (a k)) = 1 ⊗ₜ[A] ((relA w₀).mkQ a) := by
  change ∑ k, (algebraMap A B (a k)) ⊗ₜ[A]
    (Submodule.Quotient.mk (Pi.single k 1) : ((Fin n → A) ⧸ relA w₀)) = _
  rw [mkQ_eq_sum_single (relA w₀) a, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  rfl

/-- The `A`-linear map `(Fin n → A) ⧸ relA w₀ → (Fin n → B) ⧸ relB B w₀`. -/
noncomputable def l0 : ((Fin n → A) ⧸ relA w₀) →ₗ[A] ((Fin n → B) ⧸ relB B w₀) := by
  refine Submodule.liftQ _
    ((relB B w₀).mkQ.restrictScalars A ∘ₗ ((Algebra.linearMap A B).compLeft (Fin n))) ?_
  rw [relA, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply]
  change (relB B w₀).mkQ _ = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨j, rfl⟩

/-- `l0` sends the class of `a : Fin n → A` to the class of its image in `Fin n → B`. -/
lemma l0_mkQ (a : Fin n → A) :
    l0 B w₀ ((relA w₀).mkQ a) = (relB B w₀).mkQ (fun k => algebraMap A B (a k)) := rfl

/-- The comparison map `B ⊗[A] ((Fin n → A) ⧸ relA w₀) → (Fin n → B) ⧸ relB B w₀`. -/
noncomputable def theta : B ⊗[A] ((Fin n → A) ⧸ relA w₀) →ₗ[B] ((Fin n → B) ⧸ relB B w₀) :=
  (l0 B w₀).liftBaseChange B

/-- The relations `relB B w₀` lie in the kernel of `psi`. -/
lemma relB_le_ker_psi : relB B w₀ ≤ LinearMap.ker (psi B w₀) := by
  rw [relB, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  have h0 : (relA w₀).mkQ (w₀ j) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, relA]
    exact Submodule.subset_span ⟨j, rfl⟩
  change psi B w₀ (fun k => algebraMap A B (w₀ j k)) = 0
  rw [psi_algebraMap B w₀ (w₀ j), h0, TensorProduct.tmul_zero]

/-- The `B`-linear map `(Fin n → B) ⧸ relB B w₀ → B ⊗[A] ((Fin n → A) ⧸ relA w₀)` induced by
`psi`. -/
noncomputable def psibar :
    ((Fin n → B) ⧸ relB B w₀) →ₗ[B] B ⊗[A] ((Fin n → A) ⧸ relA w₀) :=
  Submodule.liftQ _ (psi B w₀) (relB_le_ker_psi B w₀)

/-- `psibar` is a right inverse of `theta`. -/
lemma theta_psibar : (theta B w₀).comp (psibar B w₀) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change theta B w₀ (psi B w₀ b) = _
  change theta B w₀ (∑ k, b k ⊗ₜ[A]
    (Submodule.Quotient.mk (Pi.single k 1) : ((Fin n → A) ⧸ relA w₀))) = _
  rw [map_sum]
  have key : ∀ k : Fin n, theta B w₀ (b k ⊗ₜ[A]
      (Submodule.Quotient.mk (Pi.single k 1) : ((Fin n → A) ⧸ relA w₀)))
      = b k • (relB B w₀).mkQ (Pi.single k (1 : B)) := by
    intro k
    rw [theta, LinearMap.liftBaseChange_tmul]
    congr 1
    rw [show (Submodule.Quotient.mk (Pi.single k 1) : ((Fin n → A) ⧸ relA w₀))
        = (relA w₀).mkQ (Pi.single k 1) from rfl, l0_mkQ]
    congr 1
    ext k'
    simp [Pi.single_apply]
  rw [Finset.sum_congr rfl fun k _ => key k, ← mkQ_eq_sum_single (relB B w₀) b]
  rfl

/-- `psibar` is a left inverse of `theta`. -/
lemma psibar_theta : (psibar B w₀).comp (theta B w₀) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  induction x using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add] at hu hv ⊢; rw [hu, hv]
  | tmul b y =>
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [theta, LinearMap.liftBaseChange_tmul]
      rw [show (Submodule.Quotient.mk a : ((Fin n → A) ⧸ relA w₀)) = (relA w₀).mkQ a from rfl,
        l0_mkQ, map_smul]
      change b • psi B w₀ (fun k => algebraMap A B (a k)) = _
      rw [psi_algebraMap B w₀ a, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Base change of a presentation by a finite family of relations:
`B ⊗[A] ((Fin n → A) ⧸ relA w₀) ≅ (Fin n → B) ⧸ relB B w₀`. -/
noncomputable def descentEquiv :
    B ⊗[A] ((Fin n → A) ⧸ relA w₀) ≃ₗ[B] ((Fin n → B) ⧸ relB B w₀) :=
  LinearEquiv.ofLinearMap (theta B w₀) (psibar B w₀) (theta_psibar B w₀) (psibar_theta B w₀)

/-- A quotient of `Fin n → A` by finitely many relations is finitely presented over `A`. -/
instance finitePresentation_quotient_relA :
    Module.FinitePresentation A ((Fin n → A) ⧸ relA w₀) := by
  refine Module.finitePresentation_of_surjective (relA w₀).mkQ
    (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ, relA]
  exact Submodule.fg_span (Set.finite_range _)

/-! ### Descent of a finitely presented module along a filtered colimit of rings -/

open Stacks.RingFilteredColimits in
/-- A finitely presented module over a filtered colimit of commutative rings is the extension
of scalars of a finitely presented module at some stage.  This is the module-theoretic content
of [Stacks Project, Tag 05N7] (1), stated for a colimit cocone of a filtered diagram rather
than for a directed system. -/
@[ega "IV 5.13.7.1" "more general"]
theorem exists_extendScalars_iso_of_isColimit {K : Type w} [Category.{v} K] [IsFiltered K]
    {G : K ⥤ CommRingCat.{u}} {d : Cocone G} (hd : IsColimit d)
    (M : ModuleCat.{u} d.pt) [Module.FinitePresentation (d.pt) M] :
    ∃ (k : K) (M₀ : ModuleCat.{u} (G.obj k)), Module.FinitePresentation (G.obj k) M₀ ∧
      Nonempty ((ModuleCat.extendScalars (d.ι.app k).hom).obj M₀ ≅ M) := by
  classical
  obtain ⟨n, P, e, hP⟩ := Module.FinitePresentation.exists_fin (d.pt) M
  obtain ⟨m, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hP
  obtain ⟨k, hk⟩ := exists_forall_mem_img hd (fun p : Fin m × Fin n => w p.1 p.2)
  simp only [img, RingHom.mem_range] at hk
  choose y hy using hk
  let _ : Algebra (G.obj k) (d.pt) := (d.ι.app k).hom.toAlgebra
  set w₀ : Fin m → (Fin n → G.obj k) := fun j l => y (j, l) with hw₀
  have halg : (fun (j : Fin m) (l : Fin n) => algebraMap (G.obj k) (d.pt) (w₀ j l)) = w := by
    funext j l
    exact hy (j, l)
  obtain rfl : P = relB (d.pt) w₀ := by rw [← hw, relB, halg]
  refine ⟨k, ModuleCat.of (G.obj k) ((Fin n → G.obj k) ⧸ relA w₀), inferInstance,
    ⟨LinearEquiv.toModuleIso (descentEquiv (d.pt) w₀ ≪≫ₗ e.symm)⟩⟩

end ModuleDescent

end Stacks

end
