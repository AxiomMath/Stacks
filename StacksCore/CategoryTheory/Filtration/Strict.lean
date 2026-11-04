module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import StacksCore.CategoryTheory.Abelian.Images
public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksCore.CategoryTheory.Filtration.Basic
public import StacksCore.CategoryTheory.Filtration.Limits
public import StacksCore.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import StacksCore.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq
public import StacksCore.CategoryTheory.Preadditive.Biproducts
import StacksCore.Tactic.StacksAttribute

/-! # Strict morphisms of filtered objects

Stacks 0123 calls a morphism `f : A ⟶ B` of filtered objects of an abelian category *strict*
if `f(F^iA) = f(A) ∩ F^iB` for all `i`; the remark after the definition gives the equivalent
condition `f⁻¹(F^iB) = F^iA + Ker(f)`. Mathlib's `FilteredObject.IsStrictHom f` is a
different, stronger condition: every square `F^iA ⟶ F^iB, A ⟶ B` is a pullback, that is
`F^iA = f⁻¹(F^iB)` (the filtration on `A` is induced from `B` along `f`). This file defines
Stacks' notion and relates the two.

* `FilteredObject.IsStrict` is Stacks' definition, for filtered objects of any category with
  images and pullbacks (`isStrict_iff_exists_eq` restates it with the image functor
  `Subobject.exists f.hom`).
* `isStrictHom_iff`: `IsStrictHom f ↔ ∀ i, f⁻¹(F^iB) = F^iA`, and
  `isStrictHom_iff_subobject_eq_pullback` says the same with `Filtration.pullback`.
* `isStrict_iff_pullback_eq_sup`: the remark after 0123,
  `IsStrict f ↔ ∀ i, f⁻¹(F^iB) = F^iA ⊔ Ker f`.
* `isStrictHom_iff_isStrict_and_kernelSubobject_le`:
  `IsStrictHom f ↔ IsStrict f ∧ ∀ i, Ker f ≤ F^iA`. So Mathlib's strict morphisms are
  Stacks-strict (`IsStrictHom.isStrict`), and the two notions agree for monomorphisms
  (`isStrict_iff_isStrictHom_of_mono`) but not in general: an epimorphism
  `f : A ⟶ B` that is not a monomorphism, with `F^iA = 0` and `F^iB = 0` for all `i`, is
  Stacks-strict (`f(0) = 0 = f(A) ∩ 0`) but not cartesian (`f⁻¹(0) = Ker f ≠ 0 = F^iA`).
* Stacks 0124: a monomorphism is strict iff the filtration on its source is the induced one
  (`isStrict_iff_subobject_eq_pullback_of_mono`, for any category with images and pullbacks),
  and an epimorphism is strict iff the filtration on its target is the quotient one
  (`isStrict_iff_subobject_eq_pushforward_of_epi`, for any balanced category with images and
  pullbacks). `isoPullbackObjOfIsStrict` and `isoPushforwardObjOfIsStrict` are the corresponding
  isomorphisms `A ≅ pullbackObj B u.hom` and `B ≅ pushforwardObj A u.hom` in `Fil(𝒜)`.
* Kernels and cokernels in `Fil(𝒜)` are strict: a subobject with the induced filtration,
  `pullbackHom A m` for a monomorphism `m`, is a strict monomorphism (`isStrict_pullbackHom`),
  and `pushforwardHom A e` is strict for any `e` (`isStrict_pushforwardHom`; for an epimorphism
  `e`: a quotient with the quotient filtration is a strict epimorphism). Hence `kernel.ι f` and
  `cokernel.π f` computed in `Fil(𝒜)` are strict (`isStrict_kernel_ι`, `isStrict_cokernel_π`).
  These two instances are the strictness of `X → A`, `Y → A` and `Y → Y/X` in Stacks 0129
  (`StacksCore.CategoryTheory.Filtration.Subquotient`); `isoPullbackObj_hom_hom` and
  `isoPullbackObj_inv_hom` record that `isoPullbackObj f` is the identity on underlying objects.
* Stacks 05SI, `isStrict_iff_isIso_coimageImageComparison`: in an abelian category, `f` is strict
  if and only if the canonical morphism `Coim(f) ⟶ Im(f)` of Stacks 0107
  (`Abelian.coimageImageComparison f`, computed in `Fil(𝒜)`) is an isomorphism.
  `coimageImageComparisonObj f` is that morphism transported to the explicit models
  `coimageObj f ⟶ imageObj f` of `StacksCore.CategoryTheory.Filtration.Limits`; its underlying
  morphism is the comparison of `f.hom`, an isomorphism of `𝒜`, so by `isIso_iff_isStrictHom`
  the statement reduces to the filtration steps: `π(F^iA) = ι⁻¹(F^iB)` in
  `Coim(f.hom) ≅ Im(f.hom)`, which is `Subobject.exists_comp_eq_inf_iff`.
  Independently of strictness, the underlying morphism of `Abelian.coimageImageComparison f`
  itself is an isomorphism (`isIso_coimageImageComparison_hom`): the forgetful functor, a left and
  a right adjoint, preserves the kernels and cokernels involved. Hence a strict morphism factors
  as a strict epimorphism `A ⟶ Coim f ≅ Im f` followed by the strict monomorphism `Im f ⟶ B`
  (`exists_isStrict_epi_comp_isStrict_mono`).
* Strictness on the steps: `f` is strict iff on every step the image of `F^iA ⟶ F^iB` is the
  induced subobject `F^iB ∩ f(A)`, the preimage of `Im f` in `F^iB`
  (`isStrict_iff_imageSubobject_natTrans_app_eq`), and a strict epimorphism is an epimorphism
  on every step (`epi_natTrans_app_of_isStrict_of_epi`, in a balanced category with images,
  pullbacks and strong epi images).
* Stacks 05SK, `IsStrict.biprod_lift` and `isStrict_and_mono_biprod_lift`: if `f : A ⟶ B` is a
  strict monomorphism and `g : A ⟶ D` is any morphism, then `(f, g) : A ⟶ B ⊕ D` is a strict
  monomorphism. This is the cartesian statement `isStrictHom_biprod_lift`, which holds for any
  cartesian `f` in `Fil(𝒜)` over an additive `𝒜` (a pullback square stays a pullback after
  pairing, `IsPullback.biprod_lift`), read through 0124; so 05SK itself is stated for any
  additive `𝒜` with images and pullbacks, no abelian hypothesis.
* `isStrict`, the morphism property of strict morphisms, respects isomorphisms
  (`isStrict_isIso_comp_iff`, `isStrict_comp_isIso_iff` and the `RespectsIso` instance, for any
  category with images and pullbacks).
* Stacks 05SL, `IsStrict.biprod_desc` and `isStrict_and_epi_biprod_desc`: if `f : B ⟶ A` is a
  strict epimorphism and `g : D ⟶ A` is any morphism, then `f ⊕ g : B ⊕ D ⟶ A` is a strict
  epimorphism, for any balanced additive `𝒜` with images and pullbacks. Unlike 05SK
  this is not a cartesian statement: `isStrictHom_biprod_desc_id_iff` shows that the fold map
  `𝟙 ⊕ 𝟙 : A ⊕ A ⟶ A` is cartesian exactly when every step of `A` is all of `A`, although `𝟙 A`
  is a cartesian epimorphism. The proof goes through the 0124 description of strict
  epimorphisms: `(f ⊕ g)(F^iB ⊕ F^iD) = F^iA` because already `f(F^iB) = F^iA`.
* Stacks 05SJ, `isStrict_comp_iff_of_mono` and `isStrict_comp_iff_of_epi`: if `g` is a strict
  monomorphism then `f ≫ g` is strict iff `f` is (any category with images and pullbacks), and if
  `f` is a strict epimorphism then `f ≫ g` is strict iff `g` is (any balanced category with images
  and pullbacks). In particular the composite of two strict morphisms is strict when the second
  is a monomorphism or the first is an epimorphism (`IsStrict.comp_of_mono`,
  `IsStrict.comp_of_epi`), which are parts (2) and (3) of 05SJ. Part (1), that the composite of
  two strict morphisms is not strict in general, is a counterexample and is not formalized:
  Stacks takes the vector space `B = k e₁ ⊕ k e₂` filtered by `F^nB = B` for `n < 0`,
  `F⁰B = k e₁` and `F^nB = 0` for `n > 0`, the subobject `A = k(e₁ + e₂)` with the induced
  filtration (`F⁰A = 0`) and the quotient `C = B / k e₂` with the quotient filtration
  (`F⁰C = C`); both maps are strict by 0124, but the nonzero composite `A ⟶ C` is not. It has no
  consumers, and a `ModuleCat` witness would be bookkeeping that nothing would call.
* A morphism of filtered objects which is a (strong) epimorphism on every step is strict,
  `u(F^iX) = F^iY = u(X) ∩ F^iY` since `F^iY = u(F^iX) ⊆ u(X)`, with no hypothesis on `u.hom`
  (`isStrict_of_forall_strongEpi_natTrans_app`, `isStrict_of_forall_epi_natTrans_app`, for any
  category with pullbacks and strong epi-mono factorisations, resp. any such strong-epi
  category); this is the strictness input of Stacks 05QH.

The lattice-theoretic input is the image/preimage calculus of `Subobject.exists` and
`Subobject.pullback` in an abelian category, `Abelian.Subobject.pullback_exists_eq_sup`
(`f⁻¹(f(X')) = X' ⊔ Ker f`) and `Abelian.Subobject.exists_pullback_eq_inf`
(`f(f⁻¹(Y')) = Y' ⊓ Im f`), ported from mathlib#41769 in
`StacksCore.CategoryTheory.Abelian.Subobject`, together with `Subobject.exists_comp_eq_inf_iff` in
`StacksCore.CategoryTheory.Subobject.Limits`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {I : Type*} [Category* I]

namespace FilteredObject

variable {A B : FilteredObject C I}

section Pullback

variable [HasPullbacks C]

/-- Mathlib's `IsStrictHom` is exactly the condition `f⁻¹(F^iB) = F^iA` for all `i`. -/
theorem isStrictHom_iff (f : A ⟶ B) :
    IsStrictHom f ↔ ∀ i, (Subobject.pullback f.hom).obj (B.subobject i) = A.subobject i := by
  refine ⟨fun h i => Subobject.pullback_obj_mk (h.isPullback i), fun h => ⟨fun i => ?_⟩⟩
  have hP := Subobject.isPullback f.hom (B.subobject i)
  refine hP.of_iso (Subobject.isoOfEqMk _ _ (h i)) (Subobject.underlyingIso _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (B.filtration.ι.app i), Category.assoc, Category.assoc,
      Subobject.underlyingIso_hom_comp_eq_mk, hP.w, Hom.comm, Subobject.isoOfEqMk_hom,
      ← Category.assoc, Subobject.ofLEMk_comp]
  all_goals simp [Subobject.underlyingIso_hom_comp_eq_mk]

/-- Mathlib's `IsStrictHom f` says that the filtration on `A` is the one induced from `B`
along `f`. -/
theorem isStrictHom_iff_subobject_eq_pullback (f : A ⟶ B) :
    IsStrictHom f ↔ ∀ i, A.subobject i = (B.filtration.pullback f.hom).subobject i := by
  rw [isStrictHom_iff]
  refine forall_congr' fun i => ?_
  rw [Filtration.subobject_pullback]
  exact eq_comm

/-- A cartesian morphism identifies its source with the pullback filtration on it, over `B`. -/
noncomputable def isoPullbackObj (f : A ⟶ B) [IsStrictHom f] : A ≅ pullbackObj B f.hom :=
  isoMk (Iso.refl _) (fun i => (IsStrictHom.isPullback f i).isoPullback)
    (fun _ => (IsPullback.isoPullback_hom_snd _).trans (Category.comp_id _).symm)

/-- The isomorphism `isoPullbackObj f` followed by the projection of the pullback filtration is
`f`. -/
@[reassoc (attr := simp)]
lemma isoPullbackObj_hom_pullbackHom (f : A ⟶ B) [IsStrictHom f] :
    (isoPullbackObj f).hom ≫ pullbackHom B f.hom = f :=
  hom_ext (Category.id_comp _)

/-- The underlying morphism of `isoPullbackObj f` is the identity. -/
@[simp] lemma isoPullbackObj_hom_hom (f : A ⟶ B) [IsStrictHom f] :
    (isoPullbackObj f).hom.hom = 𝟙 _ := rfl

/-- The underlying morphism of the inverse of `isoPullbackObj f` is the identity. -/
@[simp] lemma isoPullbackObj_inv_hom (f : A ⟶ B) [IsStrictHom f] :
    (isoPullbackObj f).inv.hom = 𝟙 _ := rfl

variable [HasZeroMorphisms C] [HasKernels C] in
/-- Mathlib's cartesian condition forces `Ker(f) ⊆ F^iA` for all `i`: `Ker f ≤ f⁻¹(F^iB) = F^iA`.
This needs no abelian hypothesis. -/
lemma kernelSubobject_le_of_isStrictHom (f : A ⟶ B) [IsStrictHom f] (i : I) :
    kernelSubobject f.hom ≤ A.subobject i := by
  rw [← (isStrictHom_iff f).1 ‹_› i]
  exact Subobject.le_pullback_of_comm f.hom 0 (by simp)

end Pullback

section Image

variable [HasImages C]

/-- `f(F^iA)` as the image functor `Subobject.exists f.hom` applied to `F^iA`. -/
lemma imageSubobject_ι_comp_eq_exists (f : A ⟶ B) (i : I) :
    imageSubobject (A.filtration.ι.app i ≫ f.hom) =
      (Subobject.exists f.hom).obj (A.subobject i) :=
  (Subobject.exists_mk_eq_imageSubobject (A.filtration.ι.app i) f.hom).symm

end Image

section IsStrict

variable [HasImages C] [HasPullbacks C]

/-- Stacks 0123: a morphism `f : A ⟶ B` of filtered objects is *strict* if
`f(F^iA) = f(A) ∩ F^iB` for all `i`. -/
@[stacks 0123 "for filtered objects of any category with images and pullbacks"]
class IsStrict (f : A ⟶ B) : Prop where
  imageSubobject_eq (i : I) :
    imageSubobject (A.filtration.ι.app i ≫ f.hom) = imageSubobject f.hom ⊓ B.subobject i

/-- Strictness in terms of the image functor `Subobject.exists f.hom`. -/
lemma isStrict_iff_exists_eq (f : A ⟶ B) :
    IsStrict f ↔
      ∀ i, (Subobject.exists f.hom).obj (A.subobject i) = imageSubobject f.hom ⊓ B.subobject i :=
  ⟨fun h i => by rw [← imageSubobject_ι_comp_eq_exists]; exact h.imageSubobject_eq i,
    fun h => ⟨fun i => by rw [imageSubobject_ι_comp_eq_exists]; exact h i⟩⟩

/-- Stacks-strictness in terms of the level maps: `f : A ⟶ B` is strict if and only if for
every `i` the image of `F^iA ⟶ F^iB` is the induced subobject `F^iB ∩ f(A)` of `F^iB`, that is
the preimage of `Im f` under `F^iB ⟶ B`. -/
theorem isStrict_iff_imageSubobject_natTrans_app_eq (f : A ⟶ B) :
    IsStrict f ↔ ∀ i, imageSubobject (f.natTrans.app i) =
      (Subobject.pullback (B.filtration.ι.app i)).obj (imageSubobject f.hom) := by
  have h₁ (i : I) : (Subobject.map (B.filtration.ι.app i)).obj
      (imageSubobject (f.natTrans.app i)) = imageSubobject (A.filtration.ι.app i ≫ f.hom) := by
    rw [← f.comm i, Subobject.imageSubobject_comp_eq_exists, Subobject.exists_iso_map]
  have h₂ (i : I) : (Subobject.map (B.filtration.ι.app i)).obj
      ((Subobject.pullback (B.filtration.ι.app i)).obj (imageSubobject f.hom)) =
      imageSubobject f.hom ⊓ B.subobject i := by
    rw [← Subobject.exists_iso_map, Subobject.exists_pullback_eq_inf_of_mono]
  exact ⟨fun h i => Subobject.map_obj_injective _ (by rw [h₁, h₂, h.imageSubobject_eq]),
    fun h => ⟨fun i => by rw [← h₁, h i, h₂]⟩⟩

variable (C I) in
/-- Stacks-strictness as a morphism property of `Fil(𝒜)`. -/
abbrev isStrict : MorphismProperty (FilteredObject C I) := fun _ _ f => IsStrict f

/-- An isomorphism of filtered objects maps each step onto the corresponding step. -/
lemma exists_obj_subobject_eq_of_isIso (φ : A ⟶ B) [IsIso φ] (i : I) :
    (Subobject.exists φ.hom).obj (A.subobject i) = B.subobject i := by
  have := isIso_hom_of_isIso φ
  rw [← (isStrictHom_iff φ).1 inferInstance i, Subobject.exists_pullback_eq_inf_of_mono,
    Subobject.mk_eq_top_of_isIso, inf_top_eq]

/-- Strictness is invariant under precomposition with an isomorphism. -/
lemma isStrict_isIso_comp_iff {X : FilteredObject C I} (φ : X ⟶ A) [IsIso φ] (u : A ⟶ B) :
    IsStrict (φ ≫ u) ↔ IsStrict u := by
  have := isIso_hom_of_isIso φ
  simp [isStrict_iff_exists_eq, comp_hom, Subobject.exists_comp, exists_obj_subobject_eq_of_isIso,
    Subobject.imageSubobject_iso_comp']

/-- Strictness is invariant under postcomposition with an isomorphism. -/
lemma isStrict_comp_isIso_iff {Z : FilteredObject C I} (u : A ⟶ B) (φ : B ⟶ Z) [IsIso φ] :
    IsStrict (u ≫ φ) ↔ IsStrict u := by
  have := isIso_hom_of_isIso φ
  simp [isStrict_iff_exists_eq, comp_hom, Subobject.exists_comp,
    Subobject.imageSubobject_comp_eq_exists, ← exists_obj_subobject_eq_of_isIso φ,
    ← Subobject.exists_obj_inf_of_isIso, Subobject.exists_obj_eq_exists_obj_iff_of_mono]

/-- Strictness respects isomorphisms. -/
instance : (isStrict C I).RespectsIso :=
  MorphismProperty.RespectsIso.mk _ (fun e f hf => (isStrict_isIso_comp_iff e.hom f).2 hf)
    (fun e f hf => (isStrict_comp_isIso_iff f e.hom).2 hf)

/-- For a monomorphism of filtered objects, Stacks-strictness and Mathlib's cartesian
condition coincide. -/
theorem isStrict_iff_isStrictHom_of_mono (f : A ⟶ B) [Mono f.hom] :
    IsStrict f ↔ IsStrictHom f := by
  rw [isStrictHom_iff]
  have key : ∀ i, imageSubobject (A.filtration.ι.app i ≫ f.hom) =
      imageSubobject f.hom ⊓ B.subobject i ↔
      (Subobject.pullback f.hom).obj (B.subobject i) = A.subobject i := fun i => by
    rw [← Subobject.exists_mk_eq_imageSubobject, imageSubobject_mono, inf_comm,
      ← Subobject.exists_pullback_eq_inf_of_mono, eq_comm]
    exact Subobject.exists_obj_eq_exists_obj_iff_of_mono _ _ _
  exact ⟨fun h i => (key i).1 (h.imageSubobject_eq i), fun h => ⟨fun i => (key i).2 (h i)⟩⟩

/-- Stacks 0124, the injective case: a monomorphism `u : A ⟶ B` of filtered objects is strict
if and only if the filtration on `A` is the induced filtration `F^iA = A ∩ F^iB`. This holds in
any category with images and pullbacks. -/
@[stacks 0124 "the injective case: `u` is strict iff the filtration on `A` is the induced one"]
theorem isStrict_iff_subobject_eq_pullback_of_mono (f : A ⟶ B) [Mono f.hom] :
    IsStrict f ↔ ∀ i, A.subobject i = (B.filtration.pullback f.hom).subobject i := by
  rw [isStrict_iff_isStrictHom_of_mono, isStrictHom_iff_subobject_eq_pullback]

/-- Stacks 0124, the injective case, as an isomorphism over `B`: a strict monomorphism is a
subobject with the induced filtration. -/
noncomputable def isoPullbackObjOfIsStrict (f : A ⟶ B) [IsStrict f] [Mono f.hom] :
    A ≅ pullbackObj B f.hom :=
  have : IsStrictHom f := (isStrict_iff_isStrictHom_of_mono f).1 ‹_›
  isoPullbackObj f

/-- Stacks 05SJ (2), as an equivalence: if `g : B ⟶ D` is a strict monomorphism, then `f ≫ g` is
strict if and only if `f` is. Indeed `g` preserves intersections, so
`g(f(F^iA)) = g(f(A)) ∩ F^iD` unwinds to `g(f(F^iA)) = g(f(A) ∩ F^iB)`, and `g` is injective on
subobjects. This holds in any category with images and pullbacks. -/
@[stacks 05SJ "(2) as an equivalence: for a strict monomorphism `g`, `f ≫ g` is strict iff `f` is"]
theorem isStrict_comp_iff_of_mono {D : FilteredObject C I} (f : A ⟶ B) (g : B ⟶ D) [IsStrict g]
    [Mono g.hom] : IsStrict (f ≫ g) ↔ IsStrict f := by
  have key (i : I) : imageSubobject (f.hom ≫ g.hom) ⊓ D.subobject i =
      (Subobject.exists g.hom).obj (imageSubobject f.hom ⊓ B.subobject i) := by
    rw [Subobject.exists_iso_map, Subobject.inf_map, ← Subobject.exists_iso_map,
      ← Subobject.imageSubobject_comp_eq_exists, (isStrict_iff_exists_eq g).1 ‹_› i, ← inf_assoc,
      inf_eq_left.2 (imageSubobject_comp_le f.hom g.hom)]
  rw [isStrict_iff_exists_eq, isStrict_iff_exists_eq]
  simp [Subobject.exists_comp, key, Subobject.exists_obj_eq_exists_obj_iff_of_mono]

/-- Stacks 05SJ (2): the composite of two strict morphisms is strict when the second one is a
monomorphism. -/
@[stacks 05SJ "(2): `g ∘ f` is strict for strict `f`, `g` with `g` a monomorphism"]
instance IsStrict.comp_of_mono {D : FilteredObject C I} (f : A ⟶ B) (g : B ⟶ D) [IsStrict f]
    [IsStrict g] [Mono g.hom] : IsStrict (f ≫ g) :=
  (isStrict_comp_iff_of_mono f g).2 ‹_›

end IsStrict

section StrictOfEpi

variable [HasPullbacks C] [HasStrongEpiMonoFactorisations C]

/-- A morphism of filtered objects which is a strong epimorphism on every step is strict:
`u(F^iX) = F^iY`, and `F^iY = u(F^iX) ⊆ u(X)` forces `u(X) ∩ F^iY = F^iY`. No hypothesis on
`u.hom`. This needs only pullbacks and strong epi-mono factorisations in `C`. -/
theorem isStrict_of_forall_strongEpi_natTrans_app {X Y : FilteredObject C I} (u : X ⟶ Y)
    (h : ∀ i, StrongEpi (u.natTrans.app i)) : IsStrict u where
  imageSubobject_eq i := by
    have := h i
    have key : imageSubobject (X.filtration.ι.app i ≫ u.hom) = Y.subobject i := by
      rw [← u.comm i, imageSubobject_comp_of_strongEpi, imageSubobject_mono]
    rw [key, eq_comm, inf_eq_right, ← key]
    exact imageSubobject_comp_le _ _

variable [StrongEpiCategory C]

/-- A morphism of filtered objects which is an epimorphism on every step is strict, in any
strong-epi category (for instance any abelian category) with pullbacks and strong epi-mono
factorisations. No hypothesis on `u.hom`. -/
theorem isStrict_of_forall_epi_natTrans_app {X Y : FilteredObject C I} (u : X ⟶ Y)
    (h : ∀ i, Epi (u.natTrans.app i)) : IsStrict u :=
  isStrict_of_forall_strongEpi_natTrans_app u fun i => have := h i; strongEpi_of_epi _

end StrictOfEpi

section Biproducts

variable [Preadditive C] [HasBinaryBiproducts C] {D : FilteredObject C I}

/-- Cartesian morphisms are stable under pairing into the explicit direct sum `biprodObj B D`. -/
instance isStrictHom_biprodObjLift (f : A ⟶ B) (g : A ⟶ D) [IsStrictHom f] :
    IsStrictHom (biprodObjLift f g) where
  isPullback i := (IsStrictHom.isPullback f i).biprod_lift (g.comm i)

/-- Cartesian morphisms are stable under pairing: if `f : A ⟶ B` is cartesian, then so is
`(f, g) : A ⟶ B ⊕ D` for every `g : A ⟶ D`. -/
instance isStrictHom_biprod_lift (f : A ⟶ B) (g : A ⟶ D) [IsStrictHom f] :
    IsStrictHom (biprod.lift f g) := by
  rw [biprod_lift_eq]; infer_instance

/-- The cartesian analogue of Stacks 05SL fails: `𝟙 A` is a cartesian epimorphism, but the fold
map `𝟙 ⊕ 𝟙 : A ⊕ A ⟶ A` (out of the explicit direct sum) is cartesian if and only if every step
of `A` is all of `A`. -/
theorem isStrictHom_biprodObjDesc_id_iff (A : FilteredObject C I) :
    IsStrictHom (biprodObjDesc (𝟙 A) (𝟙 A)) ↔ ∀ i, IsIso (A.filtration.ι.app i) :=
  ⟨fun _ i => (isPullback_biprod_desc_id_iff _).1
      (IsStrictHom.isPullback (biprodObjDesc (𝟙 A) (𝟙 A)) i),
    fun h => ⟨fun i => (isPullback_biprod_desc_id_iff (A.filtration.ι.app i)).2 (h i)⟩⟩

/-- The cartesian analogue of Stacks 05SL fails for Mathlib's `biprod.desc (𝟙 A) (𝟙 A)`: it is
cartesian if and only if every step of `A` is all of `A`. -/
theorem isStrictHom_biprod_desc_id_iff (A : FilteredObject C I) :
    IsStrictHom (biprod.desc (𝟙 A) (𝟙 A)) ↔ ∀ i, A.subobject i = ⊤ := by
  have key : IsStrictHom (biprod.desc (𝟙 A) (𝟙 A)) ↔
      IsStrictHom (biprodObjDesc (𝟙 A) (𝟙 A)) :=
    ⟨fun _ => by
      rw [← (Iso.inv_comp_eq _).2 (biprod_desc_eq (𝟙 A) (𝟙 A))]
      infer_instance,
    fun _ => by
      rw [biprod_desc_eq]
      infer_instance⟩
  rw [key, isStrictHom_biprodObjDesc_id_iff]
  exact forall_congr' fun i => Subobject.isIso_iff_mk_eq_top _

end Biproducts

section StrictBiproducts

variable [Preadditive C] [HasBinaryBiproducts C] [HasImages C] [HasPullbacks C]
  {D : FilteredObject C I}

/-- Stacks 05SK, strictness: if `f : A ⟶ B` is a strict monomorphism of filtered objects and
`g : A ⟶ D` is any morphism of filtered objects, then `(f, g) : A ⟶ B ⊕ D` is strict. For a
monomorphism, strictness is the cartesian condition (0124), which is stable under pairing
(`isStrictHom_biprod_lift`); this needs only preadditivity, binary biproducts, images and pullbacks
in `𝒜`. -/
@[stacks 05SK "`(f, g)` is strict, for any additive `𝒜` with images and pullbacks and any `I`"]
instance IsStrict.biprod_lift (f : A ⟶ B) (g : A ⟶ D) [Mono f.hom] [IsStrict f] :
    IsStrict (biprod.lift f g) :=
  have : IsStrictHom f := (isStrict_iff_isStrictHom_of_mono f).1 ‹_›
  have : Mono (biprod.lift f g).hom :=
    mono_of_mono_fac (show (biprod.lift f g).hom ≫ (biprod.fst : B ⊞ D ⟶ B).hom = f.hom from
      congrArg Hom.hom (biprod.lift_fst f g))
  (isStrict_iff_isStrictHom_of_mono _).2 inferInstance

/-- Stacks 05SK: if `f : A ⟶ B` is a strict monomorphism of filtered objects and `g : A ⟶ D` is
any morphism of filtered objects, then `(f, g) : A ⟶ B ⊕ D` is a strict monomorphism. -/
@[stacks 05SK "for any additive `𝒜` with images and pullbacks, and any index category `I`"]
theorem isStrict_and_mono_biprod_lift (f : A ⟶ B) (g : A ⟶ D) [Mono f.hom] [IsStrict f] :
    IsStrict (biprod.lift f g) ∧ Mono (biprod.lift f g) :=
  ⟨inferInstance, have := mono_of_mono_hom f; inferInstance⟩

end StrictBiproducts

section Balanced

variable [HasImages C] [HasPullbacks C] [Balanced C]

/-- Stacks 0124, the surjective case: an epimorphism `u : A ⟶ B` of filtered objects is strict
if and only if the filtration on `B` is the quotient filtration `F^iB = u(F^iA)`. This holds in
any balanced category with images and pullbacks. -/
@[stacks 0124 "the surjective case: `u` is strict iff the filtration on `B` is the quotient one"]
theorem isStrict_iff_subobject_eq_pushforward_of_epi (f : A ⟶ B) [Epi f.hom] :
    IsStrict f ↔ ∀ i, B.subobject i = (A.filtration.pushforward f.hom).subobject i := by
  rw [isStrict_iff_exists_eq]
  refine forall_congr' fun i => ?_
  rw [Filtration.subobject_pushforward, Subobject.imageSubobject_eq_top_of_epi, top_inf_eq]
  exact eq_comm

/-- Stacks 0124, the surjective case, as an isomorphism under `A`: a strict epimorphism is a
quotient with the quotient filtration. -/
noncomputable def isoPushforwardObjOfIsStrict (f : A ⟶ B) [IsStrict f] [Epi f.hom] :
    B ≅ pushforwardObj A f.hom :=
  isoMk (Iso.refl _)
    (fun i => Subobject.isoOfMkEqMk _ _
      ((isStrict_iff_subobject_eq_pushforward_of_epi f).1 ‹_› i))
    (fun i => by
      rw [Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp, Iso.refl_hom]
      exact (Category.comp_id _).symm)

/-- The morphism `f` followed by the isomorphism `isoPushforwardObjOfIsStrict f` is the canonical
morphism `A ⟶ pushforwardObj A f.hom`. -/
@[reassoc (attr := simp)]
lemma comp_isoPushforwardObjOfIsStrict_hom (f : A ⟶ B) [IsStrict f] [Epi f.hom] :
    f ≫ (isoPushforwardObjOfIsStrict f).hom = pushforwardHom A f.hom :=
  hom_ext (Category.comp_id _)

/-- A strict epimorphism of filtered objects is an epimorphism on every step, in any balanced
category with images, pullbacks and strong epi images. -/
theorem epi_natTrans_app_of_isStrict_of_epi [HasStrongEpiImages C] (e : B ⟶ A) [IsStrict e]
    [Epi e.hom] (i : I) :
    Epi (e.natTrans.app i) := by
  have : Epi ((pushforwardHom B e.hom).natTrans.app i) :=
    inferInstanceAs (Epi (factorThruImage (B.filtration.ι.app i ≫ e.hom)))
  have : IsIso ((isoPushforwardObjOfIsStrict e).inv.natTrans.app i) :=
    ((isIso_iff _).1 inferInstance).2 i
  rw [(Iso.eq_comp_inv _).2 (comp_isoPushforwardObjOfIsStrict_hom e), comp_natTrans,
    NatTrans.comp_app]
  infer_instance

/-- Stacks 05SJ (3), as an equivalence: if `f : A ⟶ B` is a strict epimorphism, then `f ≫ g` is
strict if and only if `g` is. Indeed `f(F^iA) = F^iB` and `g(f(A)) = g(B)`. This holds in any
balanced category with images and pullbacks. -/
@[stacks 05SJ "(3) as an equivalence: for a strict epimorphism `f`, `f ≫ g` is strict iff `g` is"]
theorem isStrict_comp_iff_of_epi {D : FilteredObject C I} (f : A ⟶ B) (g : B ⟶ D) [IsStrict f]
    [Epi f.hom] : IsStrict (f ≫ g) ↔ IsStrict g := by
  rw [isStrict_iff_exists_eq, isStrict_iff_exists_eq]
  simp [Subobject.exists_comp, (isStrict_iff_exists_eq f).1 ‹_›,
    Subobject.imageSubobject_eq_top_of_epi f.hom,
    Subobject.imageSubobject_comp_eq_exists f.hom g.hom, Subobject.exists_obj_top]

/-- Stacks 05SJ (3): the composite of two strict morphisms is strict when the first one is an
epimorphism. -/
@[stacks 05SJ "(3): `g ∘ f` is strict for strict `f`, `g` with `f` an epimorphism"]
instance IsStrict.comp_of_epi {D : FilteredObject C I} (f : A ⟶ B) (g : B ⟶ D) [IsStrict f]
    [IsStrict g] [Epi f.hom] : IsStrict (f ≫ g) :=
  (isStrict_comp_iff_of_epi f g).2 ‹_›

variable [Preadditive C] [HasBinaryBiproducts C]

/-- If `f : B ⟶ A` is a strict epimorphism and `g : D ⟶ A` is any morphism, then `f ⊕ g` out of
the explicit direct sum `biprodObj B D` is strict: by 0124 it suffices that
`(f ⊕ g)(F^iB ⊕ F^iD) = F^iA`, and already `f(F^iB) = F^iA`. -/
instance isStrict_biprodObjDesc {D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A) [Epi f.hom]
    [IsStrict f] : IsStrict (biprodObjDesc f g) := by
  have : Epi (biprodObjDesc f g).hom := inferInstanceAs (Epi (biprod.desc f.hom g.hom))
  refine (isStrict_iff_subobject_eq_pushforward_of_epi _).2 fun i => ?_
  rw [Filtration.subobject_pushforward]
  refine le_antisymm ?_ (exists_subobject_le (biprodObjDesc f g) i)
  rw [(isStrict_iff_subobject_eq_pushforward_of_epi f).1 ‹_› i, Filtration.subobject_pushforward,
    ← biprod.inl_desc f.hom g.hom, Subobject.exists_comp]
  exact (Subobject.exists _).monotone (exists_subobject_le (biprodBicone B D).inl i)

/-- Stacks 05SL, strictness: if `f : B ⟶ A` is a strict epimorphism of filtered objects and
`g : D ⟶ A` is any morphism of filtered objects, then `f ⊕ g : B ⊕ D ⟶ A` is strict. This needs
only a balanced additive `𝒜` with images and pullbacks. -/
@[stacks 05SL "`f ⊕ g` is strict, for any balanced additive `𝒜` with images and pullbacks"]
instance IsStrict.biprod_desc {D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A) [Epi f.hom]
    [IsStrict f] : IsStrict (biprod.desc f g) := by
  rw [biprod_desc_eq, isStrict_isIso_comp_iff]; infer_instance

/-- Stacks 05SL: if `f : B ⟶ A` is a strict epimorphism of filtered objects and `g : D ⟶ A` is any
morphism of filtered objects, then `f ⊕ g : B ⊕ D ⟶ A` is a strict epimorphism. -/
@[stacks 05SL "for any balanced additive `𝒜` with images and pullbacks, and any `I`"]
theorem isStrict_and_epi_biprod_desc {D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A) [Epi f.hom]
    [IsStrict f] : IsStrict (biprod.desc f g) ∧ Epi (biprod.desc f g) :=
  ⟨inferInstance, have := epi_of_epi_hom f; inferInstance⟩

end Balanced

section InducedQuotient

/-- A subobject with the induced filtration is a strict monomorphism. -/
@[stacks 0129 "`X → A`, `Y → A`: a subobject with the induced filtration is strict"]
instance isStrict_pullbackHom [HasPullbacks C] [HasImages C] (A : FilteredObject C I) {Y : C}
    (m : Y ⟶ A.X) [Mono m] : IsStrict (pullbackHom A m) :=
  have : Mono (pullbackHom A m).hom := inferInstanceAs (Mono m)
  (isStrict_iff_isStrictHom_of_mono _).2 inferInstance

/-- The image filtration makes `e` a strict morphism, for any `e`: `e(F^iA) ⊆ e(A)`. For an
epimorphism `e` this says that a quotient with the quotient filtration is a strict epimorphism. -/
@[stacks 0129 "`Y → Y/X`: a quotient with the quotient filtration is strict"]
instance isStrict_pushforwardHom [HasPullbacks C] [HasImages C] (A : FilteredObject C I)
    {Z : C} (e : A.X ⟶ Z) : IsStrict (pushforwardHom A e) where
  imageSubobject_eq _ := (inf_eq_right.2 (imageSubobject_comp_le _ _)).symm

end InducedQuotient

section KernelCokernel

variable [HasZeroMorphisms C] [HasImages C] [HasPullbacks C]

/-- Kernels in `Fil(𝒜)` are strict monomorphisms: `Ker f` carries the induced filtration. -/
instance isStrict_kernel_ι [HasKernels C] (f : A ⟶ B) : IsStrict (kernel.ι f) := by
  rw [← kernelIsoKernelObj_hom_kernelι, isStrict_isIso_comp_iff]
  exact inferInstanceAs (IsStrict (pullbackHom A (kernel.ι f.hom)))

/-- Cokernels in `Fil(𝒜)` are strict epimorphisms: `Coker f` carries the quotient filtration. -/
instance isStrict_cokernel_π [HasCokernels C] [HasStrongEpiImages C] (f : A ⟶ B) :
    IsStrict (cokernel.π f) := by
  rw [← cokernelπ_cokernelIsoCokernelObj_inv, isStrict_comp_isIso_iff]
  exact inferInstanceAs (IsStrict (pushforwardHom B (cokernel.π f.hom)))

end KernelCokernel

section Abelian

variable [Abelian C]

/-- The remark after Stacks 0123: `f` is strict if and only if `f⁻¹(F^iB) = F^iA + Ker(f)`
for all `i`. -/
@[stacks 0123 "the equivalent condition `f⁻¹(F^iB) = F^iA + Ker(f)` of the following remark"]
theorem isStrict_iff_pullback_eq_sup (f : A ⟶ B) :
    IsStrict f ↔ ∀ i, (Subobject.pullback f.hom).obj (B.subobject i) =
      A.subobject i ⊔ kernelSubobject f.hom := by
  rw [isStrict_iff_exists_eq]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Abelian.Subobject.pullback_exists_eq_sup f.hom, h, Subobject.inf_pullback,
      Subobject.pullback_imageSubobject_eq_top, top_inf_eq]
  · rw [← sup_bot_eq ((Subobject.exists f.hom).obj (A.subobject i)),
      ← Subobject.exists_kernelSubobject f.hom, ← (Subobject.existsPullbackAdj f.hom).gc.l_sup,
      ← h, Abelian.Subobject.exists_pullback_eq_inf, inf_comm]

/-- Mathlib's strict (cartesian) morphisms are strict in the sense of Stacks 0123. -/
instance IsStrictHom.isStrict (f : A ⟶ B) [IsStrictHom f] : IsStrict f := by
  rw [isStrict_iff_pullback_eq_sup]
  intro i
  rw [(isStrictHom_iff f).1 ‹_› i, sup_eq_left.2 (kernelSubobject_le_of_isStrictHom f i)]

/-- Mathlib's cartesian condition `IsStrictHom f` is Stacks-strictness together with
`Ker(f) ⊆ F^iA` for all `i`. -/
theorem isStrictHom_iff_isStrict_and_kernelSubobject_le (f : A ⟶ B) :
    IsStrictHom f ↔ IsStrict f ∧ ∀ i, kernelSubobject f.hom ≤ A.subobject i := by
  refine ⟨fun _ => ⟨inferInstance, kernelSubobject_le_of_isStrictHom f⟩, fun ⟨h, hK⟩ => ?_⟩
  rw [isStrict_iff_pullback_eq_sup] at h
  exact (isStrictHom_iff f).2 fun i => by rw [h i, sup_eq_left.2 (hK i)]

/-- The comparison `Coim(f) ⟶ Im(f)` of Stacks 0107, computed in `Fil(𝒜)` and transported along
`coimageIso` and `imageIso` to the explicit models `coimageObj f` and `imageObj f`. Its
underlying morphism is the comparison of `f.hom` (`coimageImageComparisonObj_hom`). -/
noncomputable def coimageImageComparisonObj (f : A ⟶ B) : coimageObj f ⟶ imageObj f :=
  (coimageIso f).inv ≫ Abelian.coimageImageComparison f ≫ (imageIso f).hom

/-- The underlying morphism of `coimageImageComparisonObj f` is the coimage-image comparison of
`f.hom` in `𝒜`. -/
@[simp]
lemma coimageImageComparisonObj_hom (f : A ⟶ B) :
    (coimageImageComparisonObj f).hom = Abelian.coimageImageComparison f.hom := by
  have h : cokernelπ (kernelι f) ≫ coimageImageComparisonObj f ≫ kernelι (cokernelπ f) = f := by
    simp only [coimageImageComparisonObj, Category.assoc, imageIso_hom_kernelι,
      cokernelπ_coimageIso_inv_assoc]
    exact Abelian.coimage_image_factorisation f
  exact unique_factorThru f.hom _ (by simpa using congrArg Hom.hom h)

/-- The underlying morphism of the comparison is an isomorphism, `𝒜` being abelian. -/
instance isIso_coimageImageComparisonObj_hom (f : A ⟶ B) :
    IsIso (coimageImageComparisonObj f).hom := by
  rw [coimageImageComparisonObj_hom]; infer_instance

/-- Whether the comparison `Coim(f) ⟶ Im(f)` in `Fil(𝒜)` is an isomorphism can be tested on the
explicit models. -/
lemma isIso_coimageImageComparison_iff (f : A ⟶ B) :
    IsIso (Abelian.coimageImageComparison f) ↔ IsIso (coimageImageComparisonObj f) := by
  refine ⟨fun _ => by unfold coimageImageComparisonObj; infer_instance, fun _ => ?_⟩
  have : Abelian.coimageImageComparison f =
      (coimageIso f).hom ≫ coimageImageComparisonObj f ≫ (imageIso f).inv := by
    simp [coimageImageComparisonObj]
  rw [this]; infer_instance

/-- Stacks 05SI: a morphism `f : A ⟶ B` of filtered objects of an abelian category is strict if
and only if the canonical morphism `Coim(f) ⟶ Im(f)` of Stacks 0107, computed in `Fil(𝒜)`, is an
isomorphism. The comparison is always an isomorphism in `𝒜`; the content is that the quotient
filtration on `Coim(f)` and the induced filtration on `Im(f)` agree. -/
@[stacks 05SI "for an arbitrary index category `I`"]
theorem isStrict_iff_isIso_coimageImageComparison (f : A ⟶ B) :
    IsStrict f ↔ IsIso (Abelian.coimageImageComparison f) := by
  rw [isIso_coimageImageComparison_iff, isIso_iff_isStrictHom,
    and_iff_right (isIso_coimageImageComparisonObj_hom f), isStrictHom_iff, isStrict_iff_exists_eq]
  refine forall_congr' fun i => ?_
  rw [imageObj_subobject, coimageObj_subobject, ← Subobject.pullback_comp,
    coimageImageComparisonObj_hom, Abelian.coimageImageComparison_comp_image_ι]
  have := Subobject.exists_comp_eq_inf_iff (Abelian.coimage.π f.hom)
    (Abelian.factorThruCoimage f.hom) (A.subobject i) (B.subobject i)
  rw [Abelian.coimage.fac] at this
  exact this.trans eq_comm

/-- The underlying morphism of the comparison `Coim f ⟶ Im f` computed in `Fil(𝒜)` is an
isomorphism. -/
instance isIso_coimageImageComparison_hom (f : A ⟶ B) :
    IsIso (Abelian.coimageImageComparison f).hom :=
  (Arrow.isIso_iff_isIso_of_isIso
    (Abelian.PreservesCoimageImageComparison.iso (forget (C := C) (I := I)) f).hom).2 inferInstance

/-- A strict morphism `f : A ⟶ B` of filtered objects factors as a strict epimorphism
`e : A ⟶ Im f` followed by a strict monomorphism `m : Im f ⟶ B`, namely
`e = coimage.π f ≫ coimageImageComparison f` and `m = image.ι f`, computed in `Fil(𝒜)`. -/
theorem exists_isStrict_epi_comp_isStrict_mono (f : A ⟶ B) [IsStrict f] :
    ∃ (M : FilteredObject C I) (e : A ⟶ M) (m : M ⟶ B),
      IsStrict e ∧ Epi e.hom ∧ IsStrict m ∧ Mono m.hom ∧ e ≫ m = f := by
  have := (isStrict_iff_isIso_coimageImageComparison f).1 ‹_›
  have : Epi (Abelian.coimage.π f).hom := (forget (C := C) (I := I)).map_epi _
  refine ⟨_, Abelian.coimage.π f ≫ Abelian.coimageImageComparison f, Abelian.image.ι f,
    (isStrict_comp_isIso_iff _ _).2 inferInstance, ?_, inferInstance,
    (forget (C := C) (I := I)).map_mono _, ?_⟩
  · rw [comp_hom]; infer_instance
  · rw [Category.assoc]; exact Abelian.coimage_image_factorisation f

end Abelian

end FilteredObject

end CategoryTheory
