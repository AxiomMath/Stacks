module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparison

/-!
# The canonical tensor map of [Stacks, Tag 0EX3] (b), read on sections

`TensorComparison.lean` states the canonicity condition
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.IsHigherDirectImageTensorMap` that conclusion (b)
of [Stacks, Tag 0EX3] asks of a map

`R^n f_* F ⊗_{𝒪_Y} G ⟶ R^n f_*(F ⊗_{𝒪_X} f^* G)`,

and proves that at most one map satisfies it.  What is missing is a map.  By the sheafification
adjunction of [Stacks, Tag 01CB] a map out of the tensor sheaf is a bilinear family on sections,
so what has to be produced is, over every open `U` of `Y`, a biadditive and bilinear

`Γ(R^n f_* F, U) × Γ(G, U) ⟶ Γ(R^n f_*(F ⊗ f^* G), U)`,

compatible with shrinking `U`.  This file writes that family down — it is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorSection` read at the top
open of `U` — and proves the part of its bilinearity that is a statement about one open.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImage` and `...topDirectImageTensor`:
  the two sheaves conclusion (b) compares.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topReading`: a morphism of modules over an open
  subscheme `U`, read as a map of sections over `U`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorTopSection`: the candidate value of the
  canonical map on sections over an open `U`, for a section `s` of `G` over `U`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.additive_rightDerivedPlus`: **the `ℤ`-indexed
  right derived functors of an additive functor are additive.**  Mathlib has this for
  `CategoryTheory.Functor.rightDerived` only.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorSectionLinear_add`,
  `...tensorLocalSectionApp_add` and `...tensorLocalSection_add`: **tensoring with a local
  section is additive in the section**, on sections, componentwise and as a morphism of sheaves;
  `...tensorLocalSection_unit_add` is the same statement for the pullback of a section of a
  module on the target, which is the form the canonical map consumes.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topReading_add`, `...topReading_add_hom` and
  `...tensorTopSection_add`: the reading at the top open is additive in the section and in the
  morphism.

## Implementation notes

The value over `U` is read at the top open of the open subscheme `U`, whose image in `Y` is `U`
but only propositionally so (`AlgebraicGeometry.Scheme.Opens.ι_image_top`), so the two
restriction maps along that equality of opens appear in `topReading`, and
`presheaf_map_ι_image_top_cancel` is what cancels them.

`topReading` writes out the comparison
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` rather than leaving it to definitional
unfolding.  The two spellings `Γ(M.restrict U.ι, ⊤)` and `Γ(M, U.ι ''ᵁ ⊤)` of its sections agree
as abelian groups by `rfl`, but their *module* structures differ by the comparison
`AlgebraicGeometry.Scheme.Hom.appIso` of the two structure sheaves, whose inverse this module
system does not expose; a rewrite inside a goal that crosses the two spellings is then reported
as not type-correct at `implicit` transparency.  With the comparison explicit every rewrite below
happens inside one spelling.

For the same reason nothing here is stated as a composite of three morphisms of `Ab`: the kernel
does not finish checking `(g ≫ h) a = h (g a)` when the objects are right-derived-functor
objects.  `comp_map_add_comp` is stated for abstract preadditive categories so that the
additivity instance enters a term as an argument instead of being unfolded by a rewrite.

## What is not here, named precisely

The bilinear family exists.  All three of its inputs are
proved, and the map they build is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorMap` in
`TensorComparisonCanonical.lean`, which satisfies the canonicity condition of
[Stacks, Tag 0EX3] (b) for an arbitrary morphism of schemes, arbitrary modules and an arbitrary
degree.  The three are:

*Additivity in the section of `G`* — `higherDirectImageTensorSection_add`, in
`TensorComparisonBilinear.lean`, whose witness is `additive_rightDerivedPlus_natDegree`.

*Linearity in the section of `G`* — `tensorTopSection_smul`, in `TensorComparisonScalar.lean`.
It is the `𝒪`-linearity of a right derived functor,
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage`
`.rightDerivedPlus_pushforward_map_baseScalar_toSpecΓ` applied to `f ∣_ U`, and what connects it
to `tensorLocalSection` is `appTop_morphismRestrict_eq`, the identification of `(f ∣_ U)^♯` with
`f^♯` on `U`.

*Naturality — compatibility with shrinking the open* — `tensorTopSection_presheaf_map`, in
`TensorComparisonOpen.lean`.  This is the substantive one.  It rests on the middle
comparison of the nested-opens cocycle being natural in the modules over `f ⁻¹ᵁ V`,
`Stacks.AlgebraicGeometry.SchemeRestrictionSmallerOpen`
`.rightDerivedPlusRestrictionOfLEObjIso_hom_naturality`, on its identification with the cocycle's
by `...rightDerivedPlusRestrictObjIso_ofLE_eq`, and on the scheme-level cocycle
`Stacks.AlgebraicGeometry.SchemeRestrictionCocycle.rightDerivedPlusRestrictObjIso_ofLE`, which
now holds in **every** degree and not only in a positive one.

What conclusion (b) still waits on is invertibility of that map, which is a separate statement and
the only one left; see the note of `TensorComparisonCanonical.lean`.

*The spelling of a restriction.* `topReading` takes its morphism in the
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling, the one
`higherDirectImageTensorSection` is declared in.  It used to take it in the `_.restrict U.ι`
spelling, and the measurement that forced the change is that a declaration pairing the two
spellings of one right-derived-functor object more than once exceeds the kernel's budget: the
applications of `topReading_add_hom_of_eq` and of `PresheafOfModules.tensorMk` in
`TensorComparisonCanonical.lean` would each pair three.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] moduleOfPresheafRing

/-- The module structure of the sections of the tensor sheaf of [Stacks, Tag 01CB] over `W`,
read over the `CommRingCat` spelling `X.presheaf.obj W` of the section ring.  The sections are
an object of `ModuleCat` over that ring by definition (this is how `toTensorSheafLinear` is
typed); instance synthesis does not see through `SheafOfModules.val` to find it, so it is
named once here, as `moduleOfPresheafRing` is for a module on `X`. -/
@[instance_reducible]
def moduleOfTensorSections {X : Scheme.{u}} (F G : X.Modules) (W : (Opens X.carrier)ᵒᵖ) :
    Module ↑(X.presheaf.obj W) ↑((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).val.obj W) :=
  inferInstanceAs (Module ↑(X.presheaf.obj W)
    ↥(show ModuleCat.{u} (X.presheaf.obj W) from
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).val.obj W))

attribute [local instance] moduleOfTensorSections

/-- **Tensoring a morphism on the left by `A`, on the image of a pure tensor.**  It acts on the
second factor and leaves the first alone.  This is the case `φ = 𝟙 A` of
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection`, in the
spelling `((sheafTensor _).obj A).map ψ` of tensoring on the left. -/
theorem sheafTensor_obj_map_toTensorSheafSection {Z : Scheme.{u}} (A : Z.Modules)
    {B B' : Z.Modules} (ψ : B ⟶ B') (W : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj W)
    (b : B.val.obj W) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj A).map ψ).val.app W).hom
        (toTensorSheafSection Z.toRingedSpace A B W (a ⊗ₜ[Z.presheaf.obj W] b)) =
      toTensorSheafSection Z.toRingedSpace A B' W
        (a ⊗ₜ[Z.presheaf.obj W] (ψ.val.app W).hom b) := by
  have e : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩)).map
        ((𝟙 A, ψ) : (A, B) ⟶ (A, B')) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj A).map ψ :=
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ (𝟙 A) ψ).trans
      (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map _ A ψ).symm
  rw [← e]
  exact tensorSheafMap_app_toTensorSheafSection Z.toRingedSpace A B A B' (𝟙 A) ψ W.unop a b

/-- **The `ℤ`-indexed right derived functors of an additive functor are additive.**  Mathlib
has this for `CategoryTheory.Functor.rightDerived`; for
`CategoryTheory.Functor.rightDerivedPlus` it is the additivity of the triangulated derived
functor, whose triangulated structure has to be installed first. -/
theorem additive_rightDerivedPlus {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C] (i : ℤ) :
    (F.rightDerivedPlus i).Additive := by
  dsimp [Functor.rightDerivedPlus]
  infer_instance

/-- An additive functor applied to a sum of morphisms, conjugated by a morphism on either
side.  Stated for abstract preadditive categories: the instance witnessing additivity then
enters the term as an argument rather than being unfolded by a rewrite, which is what keeps the
kernel from having to reduce it inside `CategoryTheory.Functor.map` of a right derived
functor. -/
theorem comp_map_add_comp {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (R : C ⥤ D) [R.Additive] {A B : C} (α β : A ⟶ B) {P Q : D}
    (u : P ⟶ R.obj A) (v : R.obj B ⟶ Q) :
    u ≫ R.map (α + β) ≫ v = (u ≫ R.map α ≫ v) + (u ≫ R.map β ≫ v) := by
  rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- **The map `x ↦ x ⊗ t` on sections is additive in `t`.** -/
theorem tensorSectionLinear_add {Z : Scheme.{u}} (A B : Z.Modules)
    (W : (Opens Z.carrier)ᵒᵖ) (t t' : B.val.obj W) :
    tensorSectionLinear Z A B W (t + t') =
      tensorSectionLinear Z A B W t + tensorSectionLinear Z A B W t' := by
  refine DFunLike.ext _ _ fun x => ?_
  exact (congrArg (toTensorSheafLinear Z A B W)
    (TensorProduct.tmul_add (R := ↑(Z.presheaf.obj W)) x t t')).trans
      (map_add (toTensorSheafLinear Z A B W) _ _)

/-- The components of `tensorLocalSection` are additive in the local section. -/
theorem tensorLocalSectionApp_add {Z : Scheme.{u}} (A B : Z.Modules) (V : Z.Opens)
    (t t' : Γ(B, V)) (W : (Opens ↥V)ᵒᵖ) :
    tensorLocalSectionApp Z A B V (t + t') W =
      tensorLocalSectionApp Z A B V t W + tensorLocalSectionApp Z A B V t' W := by
  have h : tensorSectionLinear Z A B (op (V.ι ''ᵁ W.unop))
        (B.presheaf.map (homOfLE (V.ι_image_le W.unop)).op (t + t')) =
      tensorSectionLinear Z A B (op (V.ι ''ᵁ W.unop))
          (B.presheaf.map (homOfLE (V.ι_image_le W.unop)).op t) +
        tensorSectionLinear Z A B (op (V.ι ''ᵁ W.unop))
          (B.presheaf.map (homOfLE (V.ι_image_le W.unop)).op t') := by
    rw [map_add]
    exact tensorSectionLinear_add A B _ _ _
  show (ModuleCat.restrictScalars (V.ι.appIso W.unop).inv.hom).map (ModuleCat.ofHom
      (tensorSectionLinear Z A B (op (V.ι ''ᵁ W.unop))
        (B.presheaf.map (homOfLE (V.ι_image_le W.unop)).op (t + t')))) = _
  rw [h, ModuleCat.ofHom_add, Functor.map_add]
  rfl

/-- **Tensoring with a local section is additive in the section.**  On sections it is
`x ↦ x ⊗ s`, and the pure tensor is additive in its right factor. -/
theorem tensorLocalSection_add {Z : Scheme.{u}} (A B : Z.Modules) (V : Z.Opens)
    (t t' : Γ(B, V)) :
    tensorLocalSection Z A B V (t + t') =
      tensorLocalSection Z A B V t + tensorLocalSection Z A B V t' :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext
    (fun W => tensorLocalSectionApp_add A B V t t' W))

variable {X Y : Scheme.{u}}

/-! ### Reading a morphism over an open subscheme at its top open -/

/-- The restriction maps along the equality `U.ι ''ᵁ ⊤ = U` of opens cancel. -/
theorem presheaf_map_ι_image_top_cancel {M : Y.Modules} (U : Y.Opens) (x : Γ(M, U)) :
    M.presheaf.map (eqToHom U.ι_image_top.symm).op
        (M.presheaf.map (eqToHom U.ι_image_top).op x) = x := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp, ← op_comp]
  simp

/-- **A morphism of modules over the open subscheme `U`, read on sections over `U`.**  Its
component at the top open of `U` is a map of sections over `U.ι ''ᵁ ⊤`, which is `U` but only
propositionally, so the two restriction maps along that equality of opens conjugate it into a map
of sections over `U`.

The comparison `AlgebraicGeometry.Scheme.Modules.restrictAppIso` is written out rather than left
to definitional unfolding: the two spellings of the sections agree as abelian groups by `rfl`,
but their *module* structures differ by the comparison `AlgebraicGeometry.Scheme.Hom.appIso` of
the two structure sheaves, whose inverse is not exposed, so a rewrite inside a goal that crosses
the two spellings is reported as not type-correct. -/
def topReading {M N : Y.Modules} (U : Y.Opens)
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N) (a : Γ(M, U)) :
    Γ(N, U) :=
  N.presheaf.map (eqToHom U.ι_image_top.symm).op
    ((N.restrictAppIso U.ι ⊤).hom
      (φ.app ⊤ ((M.restrictAppIso U.ι ⊤).inv
        (M.presheaf.map (eqToHom U.ι_image_top).op a))))

/-- `topReading` is additive in the section. -/
theorem topReading_add {M N : Y.Modules} (U : Y.Opens)
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N) (a a' : Γ(M, U)) :
    topReading U φ (a + a') = topReading U φ a + topReading U φ a' := by
  rw [topReading, topReading, topReading, map_add, map_add, map_add]
  exact map_add _ _ _

/-- `topReading` is additive in the morphism. -/
theorem topReading_add_hom {M N : Y.Modules} (U : Y.Opens)
    (φ ψ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N) (a : Γ(M, U)) :
    topReading U (φ + ψ) a = topReading U φ a + topReading U ψ a := by
  rw [topReading, topReading, topReading, Scheme.Modules.Hom.add_app]
  exact map_add _ _ _

/-! ### The candidate value of the canonical map -/

variable (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) (n : ℕ)

/-- The source sheaf of conclusion (b): `R^n f_* F`. -/
abbrev topDirectImage : Y.Modules :=
  ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F

/-- The target sheaf of conclusion (b): `R^n f_*(F ⊗ f^* G)`. -/
abbrev topDirectImageTensor : Y.Modules :=
  ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
        ((Scheme.Modules.pullback f).obj G)))

/-- Tensoring with the pullback of a local section is additive in that section. -/
theorem tensorLocalSection_unit_add (U : Y.Opens) (s s' : Γ(G, U)) :
    tensorLocalSection X F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app U (s + s')) =
      tensorLocalSection X F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app U s) +
        tensorLocalSection X F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app U s') := by
  have hu : (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app U) (s + s') =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app U) s +
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app U) s' :=
    map_add _ _ _
  rw [hu]
  exact tensorLocalSection_add F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U) _ _

/-- **The candidate value of the canonical map of [Stacks, Tag 0EX3] (b) on sections over `U`.**
It is `higherDirectImageTensorSection` — the higher direct image of `x ↦ x ⊗ f^* s` — read at the
top open of `U`, whose image in `Y` is `U` itself. -/
def tensorTopSection (U : Y.Opens) (s : Γ(G, U)) (a : Γ(topDirectImage f F n, U)) :
    Γ(topDirectImageTensor f F G n, U) :=
  topReading U (higherDirectImageTensorSection f F G n U s) a

/-- **`tensorTopSection` is additive in the module of sections.** -/
theorem tensorTopSection_add (U : Y.Opens) (s : Γ(G, U))
    (a a' : Γ(topDirectImage f F n, U)) :
    tensorTopSection f F G n U s (a + a') =
      tensorTopSection f F G n U s a + tensorTopSection f F G n U s a' :=
  topReading_add U (higherDirectImageTensorSection f F G n U s) a a'

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
