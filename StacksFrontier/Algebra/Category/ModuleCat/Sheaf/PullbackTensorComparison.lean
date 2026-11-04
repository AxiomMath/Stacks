module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback and the tensor product of sheaves of modules on a ringed space

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `A`, `B` be sheaves of
`𝒪_Y`-modules.  Stacks 01CD asserts `f^*(A ⊗_{𝒪_Y} B) = f^*A ⊗_{𝒪_X} f^*B`, functorially in
`A` and `B`.  This file constructs the canonical comparison morphism

`f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B`,

in the only direction the pullback adjunction supplies it, shows that it is natural in both
module arguments, computes it on the images of pure tensors, and shows that that computation
determines it uniquely.

## Main definitions

* `Stacks.RingedSpace.structureRingSheaf`: the structure sheaf of a ringed space read as a
  sheaf of (not necessarily commutative) rings, spelled so that its underlying presheaf is
  syntactically a composite with `forget₂ CommRingCat RingCat`, and
  `Stacks.RingedSpace.pullbackFunctor`, `pushforwardFunctor`, `pullbackAdjunction`: the
  ringed-space pullback, pushforward and adjunction `f^* ⊣ f_*` in that spelling, and
  `Stacks.RingedSpace.pullbackFunctor_additive`: additivity of the pullback functor.
* `Stacks.SheafOfModules.Tensor.sheafTensor`: the canonical tensor product, used through
  `Functor.uncurry.obj` for product-category APIs. The generic sheafification adjunction
  supplies its unit on the objectwise tensor product of the underlying presheaves.
* `Stacks.RingedSpace.sharp`: the action of the structure morphism of `f` on a scalar, and
  `Stacks.RingedSpace.pullbackUnit`: a local section of `A`, carried into `f^*A` by the unit
  of the adjunction `f^* ⊣ f_*`.
* `Stacks.RingedSpace.comparisonApp`: the bilinear map on local sections `(x, y) ↦ η x ⊗ η y`
  out of which the comparison is built, and `Stacks.RingedSpace.comparisonBilinear` its
  descent to the objectwise tensor product presheaf.
* `Stacks.RingedSpace.comparisonTranspose`: the adjoint transpose
  `A ⊗_{𝒪_Y} B ⟶ f_*(f^*A ⊗_{𝒪_X} f^*B)` of the comparison, and
  `Stacks.RingedSpace.comparison` the comparison morphism itself.
* `Stacks.RingedSpace.comparisonNatTrans`: the comparison as a morphism of bifunctors, so that
  naturality in both module arguments is part of the datum.

## Main results

* `Stacks.RingedSpace.homEquiv_val_app`: the adjoint transpose of a morphism out of a pullback,
  read on sections — it is the original morphism applied to the pullback-unit image.
* `Stacks.RingedSpace.comparison_homEquiv_unit_tmul` computes the adjoint transpose of the
  comparison on the sheafification-unit image of a pure tensor: it is the image, under the
  corresponding unit on `X`, of the tensor of the two pullback-unit images.  This is the
  canonicality clause of Stacks 01CD, and
  `Stacks.RingedSpace.comparisonNatTrans_homEquiv_unit_tmul` restates it over
  `structureSheafRing` and `RingedSpaceModuleAdjunction.modulePullback`.
* `Stacks.RingedSpace.comparison_unique`: that computation determines the comparison.  Any
  morphism `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` whose transpose has this effect on the unit images of
  pure tensors is the comparison.
* `Stacks.RingedSpace.comparisonTranspose_naturality` and
  `Stacks.RingedSpace.comparisonNatTrans`: the comparison is natural in `A` and in `B`.
* `Stacks.RingedSpace.comparisonIso`: Stacks 01CD, given that its components are invertible.
  That hypothesis is discharged in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso`
  (`Stacks.RingedSpace.comparisonNatTrans_app_isIso`), so `comparisonIso` is unconditional
  for anything importing that file; `Stacks.RingedSpace.comparisonBifunctorIso` there is the
  resulting isomorphism, stated with no hypotheses and carrying the tag.  By
  `comparison_unique` the comparison is the only candidate for the isomorphism of the
  source.

## Implementation notes

What is constructed here is a morphism rather than an isomorphism, and that is a division of
labour rather than the state of the mathematics: the comparison *is* an isomorphism, but not by
anything available in this file.  The *easy* direction is the one an adjunction gives: a
morphism out of `f^*(A ⊗ B)` is a morphism `A ⊗ B ⟶ f_*(f^*A ⊗ f^*B)`, hence by the universal
property of the tensor product a bilinear map on local sections of `A` and `B`, and
`(x, y) ↦ η x ⊗ η y` is such a map.  Inverting it needs either a bilinear map on local sections
of `f^*A` and `f^*B` or a computation of the stalks, and the pullback functor available here,
`RingedSpaceModuleAdjunction.modulePullback`, is defined as `(modulePushforward f).leftAdjoint`,
so nothing in this file describes its sections at all.  Both of those routes are run elsewhere;
see the final section below.

Every statement is placed over `CategoryTheory.Sheaf.toRingCat`, through the abbreviation
`structureRingSheaf`, rather than over `structureSheafRing`.  The two are
definitionally equal (`structureRingSheaf_eq_ringSheaf`) but not interchangeable for instance
resolution: `structureSheafRing` is a semireducible definition, so
`(structureSheafRing X).obj.obj U` does not
reduce to `(𝒪_X ⋙ forget₂ CommRingCat RingCat).obj U` at reducible transparency, which is the
spelling the objectwise tensor product uses for its ring of scalars.
With `structureSheafRing` in the
statements, a pulled-back section and a pure tensor of pulled-back sections carry two
syntactically different `Module` structures over definitionally equal rings, and no rewrite by
a `TensorProduct` lemma matches.  For the same reason `pullbackFunctor`, `pushforwardFunctor`
and `pullbackAdjunction` are reducible abbreviations re-typing the ringed-space pullback,
pushforward and adjunction over `structureRingSheaf`.

The two scalar-extraction steps are done by `map_smul_tmul` and `map_tmul_smul`, stated for a
linear map out of a tensor product of plain types with a single `[CommRing R]` instance.  This
is the discipline of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor` and for the same reason: a
ring of sections of a presheaf of commutative rings, read through `forget₂ CommRingCat RingCat`,
carries two definitionally equal `Semiring` structures, and mixing them is what forces
transparency workarounds elsewhere.

The tensor product used here is the canonical `Stacks.SheafOfModules.Tensor.sheafTensor`
applied to the existing commutative structure sheaf `X.sheaf`. Product-category APIs use
`Functor.uncurry.obj` directly, and the generic sheafification adjunction supplies the unit,
including its identity restriction of scalars. No alternative tensor construction is introduced.

Universes are not narrowed: everything is stated for `RingedSpace.{u, u}` and
`SheafOfModules.{u}`, which is what `RingedSpaceModuleAdjunction.modulePullback` is stated for,
and that restriction is forced by Mathlib's `PresheafOfModules.instIsRightAdjointPushforward`
rather than chosen here.

### Where the invertibility of `comparison` is proved

Invertibility of `comparison` is the remaining content of Stacks 01CD, and it is **not** proved
in this file: it needs a description of the sections or the stalks of a pullback, and
`modulePullback f` is an abstract left adjoint.  It is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso`, stalkwise,
from `RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` — the stalk of a
pullback is the extension of scalars `(f^*A)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} A_{f x}` — together with
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` for the stalk of a tensor product,
`TensorProduct.AlgebraTensorModule.distribBaseChange` for the compatibility of base change with
the tensor product, and `ExtensionByZeroModules.isIso_of_stalk_isIso` for recognising an
isomorphism of sheaves of modules on stalks.

It is also proved, independently and by the other route, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIso` and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCanonical`: there the sections of
the pullback are described, as the filtered colimit `colim R(U) ⊗_{R(FV)} N(V)` of
`Stacks.PullbackColimit.pullbackIso`, which yields an isomorphism of the right type
`Stacks.PullbackTensor.pullbackTensorSheafObjIso`, and
`Stacks.PullbackTensor.pullbackTensorSheafObjIso_hom_eq_comparison` identifies it with
`comparison` through `comparison_unique`.  Either file on its own discharges the hypothesis of
`comparisonIso`.

One might expect an *obstruction* to invertibility here, on the ground that
`modulePullback f` is an abstract left adjoint, so that no description of its sections is
available for the first route, and that
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` yields the existence of a
pointwise linear equivalence rather than a chosen natural one for the second.  Neither applies,
each by one of the two files above.  The sections of the
presheaf-level pullback are described by `Stacks.PullbackColimit.pullbackIso`; and naturality
is not needed on the stalk route, because `ExtensionByZeroModules.isIso_of_stalk_isIso` detects
an isomorphism from the stalk maps of the *already-natural* `comparison` — the chosen
equivalence is only used to identify those maps.  Moreover,
`StacksFrontier/Topology/Sheaves/RingedSpace/ModulePullbackStalkAdjunction.lean` is option-free
and importable.

`comparison_unique` is stated so that whichever route supplies invertibility, the isomorphism
it produces is forced to be this comparison; it is what identifies the isomorphism of either
of those files with the comparison constructed here.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.RingedSpace

attribute [local implicit_reducible] TopCat.Sheaf

open RingedSpaceModuleAdjunction PresheafOfModules CategoryTheory.Sheaf

section Aux

variable {R : Type u} [CommRing R] {M N P : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A linear map out of a tensor product carries a scalar out of the first factor. -/
lemma map_smul_tmul (g : (M ⊗[R] N) →ₗ[R] P) (r : R) (m : M) (n : N) :
    g ((r • m) ⊗ₜ[R] n) = r • g (m ⊗ₜ[R] n) := by
  rw [← TensorProduct.smul_tmul', map_smul]

/-- A linear map out of a tensor product carries a scalar out of the second factor. -/
lemma map_tmul_smul (g : (M ⊗[R] N) →ₗ[R] P) (r : R) (m : M) (n : N) :
    g (m ⊗ₜ[R] (r • n)) = r • g (m ⊗ₜ[R] n) := by
  rw [TensorProduct.tmul_smul, map_smul]

end Aux

/-- The structure sheaf of a ringed space, read as a sheaf of (not necessarily commutative)
rings.  This is `structureSheafRing`, spelled through the reducible
abbreviation `CategoryTheory.Sheaf.toRingCat` so that its underlying presheaf of rings is
syntactically `𝒪_X ⋙ forget₂ CommRingCat RingCat`. -/
abbrev structureRingSheaf (X : RingedSpace.{u, u}) :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} :=
  toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf

/-- `structureRingSheaf X` is definitionally `structureSheafRing X`. -/
lemma structureRingSheaf_eq_ringSheaf (X : RingedSpace.{u, u}) :
    structureRingSheaf X = structureSheafRing X := rfl

section

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The pullback functor `f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)`, typed over `structureRingSheaf`. -/
noncomputable abbrev pullbackFunctor :
    SheafOfModules.{u} (structureRingSheaf Y) ⥤ SheafOfModules.{u} (structureRingSheaf X) :=
  modulePullback f

/-- The pushforward functor `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)`, typed over `structureRingSheaf`. -/
noncomputable abbrev pushforwardFunctor :
    SheafOfModules.{u} (structureRingSheaf X) ⥤ SheafOfModules.{u} (structureRingSheaf Y) :=
  modulePushforward f

/-- The adjunction `f^* ⊣ f_*`, typed over `structureRingSheaf`. -/
noncomputable abbrev pullbackAdjunction : pullbackFunctor f ⊣ pushforwardFunctor f :=
  modulePullbackPushforwardAdjunction f

/-- The pullback functor is additive, `modulePullback_additive` at the `structureRingSheaf`
spelling, where instance search does not find it. -/
noncomputable instance pullbackFunctor_additive : (pullbackFunctor f).Additive :=
  modulePullback_additive f

/-- The image of a scalar of `𝒪_Y(U)` in `𝒪_X(f⁻¹U)` under the structure morphism of `f`. -/
noncomputable def sharp (U : (Opens Y.carrier)ᵒᵖ) (r : (structureRingSheaf Y).obj.obj U) :
    (structureRingSheaf X).obj.obj ((opensMap f).op.obj U) :=
  (structureSheafHom f).hom.app U r

/-- A local section of a sheaf of `𝒪_Y`-modules `A` over `U`, carried to a local section of
`f^*A` over `f⁻¹U` by the unit of the adjunction `f^* ⊣ f_*`. -/
noncomputable def pullbackUnit (A : SheafOfModules.{u} (structureRingSheaf Y))
    (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U) :
    ((pullbackFunctor f).obj A).val.obj ((opensMap f).op.obj U) :=
  ((pullbackAdjunction f).unit.app A).val.app U x

/-- The pullback-unit map is additive. -/
lemma pullbackUnit_add (A : SheafOfModules.{u} (structureRingSheaf Y))
    (U : (Opens Y.carrier)ᵒᵖ) (x y : A.val.obj U) :
    pullbackUnit f A U (x + y) = pullbackUnit f A U x + pullbackUnit f A U y :=
  map_add _ _ _

/-- The pullback-unit map is semilinear along `sharp f U`. -/
lemma pullbackUnit_smul (A : SheafOfModules.{u} (structureRingSheaf Y))
    (U : (Opens Y.carrier)ᵒᵖ) (r : (structureRingSheaf Y).obj.obj U) (x : A.val.obj U) :
    pullbackUnit f A U (r • x) = sharp f U r • pullbackUnit f A U x := by
  change (((pullbackAdjunction f).unit.app A).val.app U) (r • x) = _
  rw [map_smul]
  rfl

/-- The pullback-unit map commutes with restriction of sections. -/
lemma pullbackUnit_restrict (A : SheafOfModules.{u} (structureRingSheaf Y))
    {U V : (Opens Y.carrier)ᵒᵖ} (g : U ⟶ V) (x : A.val.obj U) :
    ((pullbackFunctor f).obj A).val.restrictₛₗ ((opensMap f).op.map g)
        (pullbackUnit f A U x) =
      pullbackUnit f A V (A.val.restrictₛₗ g x) :=
  (restrictₛₗ_naturality_apply ((pullbackAdjunction f).unit.app A).val g x).symm

/-- Naturality of the pullback-unit map in the sheaf of modules. -/
lemma pullbackUnit_naturality {A A' : SheafOfModules.{u} (structureRingSheaf Y)} (φ : A ⟶ A')
    (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U) :
    Hom.app ((pullbackFunctor f).map φ).val ((opensMap f).op.obj U) (pullbackUnit f A U x) =
      pullbackUnit f A' U (Hom.app φ.val U x) :=
  (hom_congr_apply' (congrArg (fun h ↦ SheafOfModules.Hom.val h)
    ((pullbackAdjunction f).unit.naturality φ)) U x).symm

/-- The adjoint transpose of a morphism out of a pullback, read on sections: it is the original
morphism applied to the pullback-unit image of the section. -/
lemma homEquiv_val_app (M : SheafOfModules.{u} (structureRingSheaf Y))
    (N : SheafOfModules.{u} (structureRingSheaf X))
    (g : (pullbackFunctor f).obj M ⟶ N) (U : (Opens Y.carrier)ᵒᵖ) (z : M.val.obj U) :
    Hom.app ((pullbackAdjunction f).homEquiv M N g).val U z =
      Hom.app g.val ((opensMap f).op.obj U) (pullbackUnit f M U z) := by
  rw [Adjunction.homEquiv_unit]
  rfl

variable (A B : SheafOfModules.{u} (structureRingSheaf Y))

/-- The value on a pair of local sections of the bilinear map defining the comparison
morphism: the image of the tensor of the two pullback-unit images under the unit exhibiting
the tensor product on `X` as a sheafification. -/
noncomputable def comparisonApp (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩)).obj
        ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B)).val.obj
      ((opensMap f).op.obj U) :=
  Hom.app ((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
    (PresheafOfModules.tensorObj (O := X.sheaf.obj) ((pullbackFunctor f).obj A).val
      ((pullbackFunctor f).obj B).val))
    ((opensMap f).op.obj U) (pullbackUnit f A U x ⊗ₜ pullbackUnit f B U y)

/-- `comparisonApp` is additive in the first section. -/
lemma comparisonApp_add_left (U : (Opens Y.carrier)ᵒᵖ) (x x' : A.val.obj U) (y : B.val.obj U) :
    comparisonApp f A B U (x + x') y =
      comparisonApp f A B U x y + comparisonApp f A B U x' y := by
  simp only [comparisonApp, pullbackUnit_add, TensorProduct.add_tmul]
  exact map_add _ _ _

/-- `comparisonApp` is additive in the second section. -/
lemma comparisonApp_add_right (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U) (y y' : B.val.obj U) :
    comparisonApp f A B U x (y + y') =
      comparisonApp f A B U x y + comparisonApp f A B U x y' := by
  simp only [comparisonApp, pullbackUnit_add, TensorProduct.tmul_add]
  exact map_add _ _ _

/-- `comparisonApp` carries a scalar out of either section, through `sharp f U`. -/
private lemma comparisonApp_smul_left_and_right (U : (Opens Y.carrier)ᵒᵖ)
    (r : (structureRingSheaf Y).obj.obj U) (x : A.val.obj U) (y : B.val.obj U) :
    comparisonApp f A B U (r • x) y =
      SMul.smul (M := (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.presheaf, X.IsSheaf⟩).obj.obj ((opensMap f).op.obj U))
        (sharp f U r) (comparisonApp f A B U x y) ∧
    comparisonApp f A B U x (r • y) =
      SMul.smul (M := (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.presheaf, X.IsSheaf⟩).obj.obj ((opensMap f).op.obj U))
        (sharp f U r) (comparisonApp f A B U x y) := by
  simp only [comparisonApp]
  rw [pullbackUnit_smul, pullbackUnit_smul]
  let g := (((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
      (PresheafOfModules.tensorObj (O := X.sheaf.obj)
        ((pullbackFunctor f).obj A).val ((pullbackFunctor f).obj B).val)).app
          ((opensMap f).op.obj U)).hom
  exact ⟨map_smul_tmul g _ _ _, map_tmul_smul g _ _ _⟩

/-- `comparisonApp` carries a scalar out of the first section, through `sharp f U`. -/
lemma comparisonApp_smul_left (U : (Opens Y.carrier)ᵒᵖ)
    (r : (structureRingSheaf Y).obj.obj U) (x : A.val.obj U) (y : B.val.obj U) :
    comparisonApp f A B U (r • x) y =
      SMul.smul (M := (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.presheaf, X.IsSheaf⟩).obj.obj ((opensMap f).op.obj U))
        (sharp f U r) (comparisonApp f A B U x y) :=
  (comparisonApp_smul_left_and_right f A B U r x y).1

/-- `comparisonApp` carries a scalar out of the second section, through `sharp f U`. -/
lemma comparisonApp_smul_right (U : (Opens Y.carrier)ᵒᵖ)
    (r : (structureRingSheaf Y).obj.obj U) (x : A.val.obj U) (y : B.val.obj U) :
    comparisonApp f A B U x (r • y) =
      SMul.smul (M := (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨X.presheaf, X.IsSheaf⟩).obj.obj ((opensMap f).op.obj U))
        (sharp f U r) (comparisonApp f A B U x y) :=
  (comparisonApp_smul_left_and_right f A B U r x y).2


/-- The underlying presheaf of a tensor product of sheaves of modules, read as the
sheafification of the objectwise tensor product of the underlying presheaves. -/
lemma tensorSheaf_obj_val (Z : RingedSpace.{u, u})
    (A' B' : SheafOfModules.{u} (structureRingSheaf Z)) :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(Z).presheaf, (Z).IsSheaf⟩)).obj
        (A', B')).val =
      (PresheafOfModules.sheafification (𝟙 (structureRingSheaf Z).obj) ⋙
          SheafOfModules.forget (structureRingSheaf Z) ⋙
          restrictScalars (𝟙 (structureRingSheaf Z).obj)).obj
        (tensorObj A'.val B'.val) := rfl

/-- `comparisonApp` commutes with restriction of sections. -/
lemma comparisonApp_restrict {U V : (Opens Y.carrier)ᵒᵖ} (g : U ⟶ V) (x : A.val.obj U)
    (y : B.val.obj U) :
    comparisonApp f A B V (A.val.restrictₛₗ g x) (B.val.restrictₛₗ g y) =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩)).obj
          ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B)).val.restrictₛₗ
        ((opensMap f).op.map g) (comparisonApp f A B U x y) := by
  rw [comparisonApp, ← pullbackUnit_restrict f A g x, ← pullbackUnit_restrict f B g y,
    ← tensorObj_restrictₛₗ_tmul, comparisonApp]
  exact restrictₛₗ_naturality_apply
    ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
      (PresheafOfModules.tensorObj (O := X.sheaf.obj) ((pullbackFunctor f).obj A).val
        ((pullbackFunctor f).obj B).val))
    ((opensMap f).op.map g) (pullbackUnit f A U x ⊗ₜ pullbackUnit f B U y)

/-- The bilinear map `(x, y) ↦ η x ⊗ η y` of the comparison morphism, descended to the
objectwise tensor product of the underlying presheaves of `A` and `B`. -/
noncomputable def comparisonBilinear :
    tensorObj (O := Y.sheaf.obj) A.val B.val ⟶
      (SheafOfModules.forget (structureRingSheaf Y) ⋙
          restrictScalars (𝟙 (structureRingSheaf Y).obj)).obj
        ((pushforwardFunctor f).obj ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            ⟨(X).presheaf, (X).IsSheaf⟩)).obj
          ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B))) :=
  tensorMk (comparisonApp f A B) (comparisonApp_add_left f A B) (comparisonApp_smul_left f A B)
    (comparisonApp_add_right f A B) (comparisonApp_smul_right f A B)
    (fun {_ _} g x y ↦ (comparisonApp_restrict f A B g x y).symm)

/-- `comparisonBilinear` sends a pure tensor `x ⊗ₜ y` to `comparisonApp f A B U x y`. -/
lemma comparisonBilinear_tmul (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    Hom.app (comparisonBilinear f A B) U (x ⊗ₜ y) = comparisonApp f A B U x y :=
  tensorMk_tmul _ _ _ _ _ _ _ _ _

/-- The adjoint transpose `A ⊗ B ⟶ f_*(f^*A ⊗ f^*B)` of the comparison morphism: the descent
of the bilinear map `(x, y) ↦ η x ⊗ η y` along the unit exhibiting `A ⊗ B` as the
sheafification of the objectwise tensor product. -/
noncomputable def comparisonTranspose :
    (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩)).obj
        (A, B) ⟶
      (pushforwardFunctor f).obj ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩)).obj
        ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B)) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureRingSheaf Y).obj)).homEquiv (tensorObj A.val B.val) _).symm
      (comparisonBilinear f A B)

/-- `comparisonTranspose` sends the sheafification-unit image of a pure tensor `x ⊗ₜ y` to
`comparisonApp f A B U x y`. -/
lemma comparisonTranspose_unit_tmul (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U)
    (y : B.val.obj U) :
    Hom.app (comparisonTranspose f A B).val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj (O := Y.sheaf.obj) A.val
            B.val)) U (x ⊗ₜ y)) = comparisonApp f A B U x y :=
  hom_congr_apply (sheafificationAdjunction_unit_comp_homEquiv_symm
    (𝟙 (structureRingSheaf Y).obj) (comparisonBilinear f A B)) U (x ⊗ₜ y)

/-- **The canonical comparison morphism of Stacks 01CD**,
`f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B`: the adjoint transpose of `comparisonTranspose`. -/
noncomputable def comparison :
    (pullbackFunctor f).obj ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩)).obj
        (A, B)) ⟶
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩)).obj
          ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B) :=
  ((pullbackAdjunction f).homEquiv _ _).symm (comparisonTranspose f A B)

/-- The adjoint transpose of `comparison` is `comparisonTranspose`. -/
@[simp]
lemma homEquiv_comparison :
    (pullbackAdjunction f).homEquiv ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩)).obj
        (A, B))
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            ⟨(X).presheaf, (X).IsSheaf⟩)).obj
            ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B))
        (comparison f A B) = comparisonTranspose f A B :=
  Equiv.apply_symm_apply _ _

/-- The comparison morphism, computed through the adjunction on the sheafification-unit image
of a pure tensor: it carries it to the image, under the corresponding unit on `X`, of the
tensor of the two pullback-unit images.  This is the canonicality clause of Stacks 01CD; the
tag for it sits on the restatement for the hypothesis-free isomorphism,
`Stacks.RingedSpace.comparisonBifunctorIso_hom_homEquiv_unit_tmul`, whose proof is this
lemma. -/
lemma comparison_homEquiv_unit_tmul (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U)
    (y : B.val.obj U) :
    Hom.app ((pullbackAdjunction f).homEquiv ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩)).obj
        (A, B))
          ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
              ⟨(X).presheaf, (X).IsSheaf⟩)).obj
              ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B)) (comparison f A B)).val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj (O := Y.sheaf.obj) A.val B.val)) U (x ⊗ₜ y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.sheaf.obj) ((pullbackFunctor f).obj A).val
          ((pullbackFunctor f).obj B).val))
        ((opensMap f).op.obj U) (pullbackUnit f A U x ⊗ₜ pullbackUnit f B U y) := by
  rw [homEquiv_comparison]
  exact comparisonTranspose_unit_tmul f A B U x y

/-- The computation of `comparison_homEquiv_unit_tmul` determines the comparison morphism. -/
lemma comparison_unique
    (θ : (pullbackFunctor f).obj ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩)).obj
        (A, B)) ⟶
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩)).obj
          ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B))
    (hθ : ∀ (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U),
      Hom.app ((pullbackAdjunction f).homEquiv ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩)).obj
          (A, B))
            ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                ⟨(X).presheaf, (X).IsSheaf⟩)).obj
                ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B)) θ).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := Y.sheaf.obj) A.val B.val)) U (x ⊗ₜ y)) =
        Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj (O := X.sheaf.obj) ((pullbackFunctor f).obj A).val
            ((pullbackFunctor f).obj B).val))
          ((opensMap f).op.obj U) (pullbackUnit f A U x ⊗ₜ pullbackUnit f B U y)) :
    θ = comparison f A B := by
  refine ((pullbackAdjunction f).homEquiv _ _).injective ?_
  rw [homEquiv_comparison]
  refine sheafification_hom_ext (tensorObj_hom_ext fun U x y ↦ ?_)
  exact (hθ U x y).trans (comparisonTranspose_unit_tmul f A B U x y).symm

end

section

variable (Z : RingedSpace.{u, u})

/-- The tensor product of two morphisms of sheaves of modules, on the sheafification-unit
image of a pure tensor. -/
lemma tensorSheaf_map_unit_tmul {A₁ A₂ B₁ B₂ : SheafOfModules.{u} (structureRingSheaf Z)}
    (u : A₁ ⟶ A₂) (v : B₁ ⟶ B₂) (U : (Opens Z.carrier)ᵒᵖ) (x : A₁.val.obj U)
    (y : B₁.val.obj U) :
    Hom.app ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(Z).presheaf, (Z).IsSheaf⟩)).map
        ((u, v) : ((A₁, B₁) : _ × _) ⟶ (A₂, B₂))).val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj (O := Z.sheaf.obj) A₁.val B₁.val)) U (x ⊗ₜ y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).obj)).unit.app
        (PresheafOfModules.tensorObj (O := Z.sheaf.obj) A₂.val
          B₂.val)) U (Hom.app u.val U x ⊗ₜ Hom.app v.val U y) := by
  have mapEquality := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Z.sheaf u v
  have evaluatedEquality := hom_congr_apply'
    (congrArg (fun morphism => SheafOfModules.Hom.val morphism) mapEquality) U
    (Hom.app ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).obj)).unit.app
        (PresheafOfModules.tensorObj (O := Z.sheaf.obj) A₁.val B₁.val)) U (x ⊗ₜ y))
  refine evaluatedEquality.trans ?_
  exact (unit_naturality_apply (α := 𝟙 (structureRingSheaf Z).obj)
    (tensorHom (O := Z.sheaf.obj) u.val v.val) U (x ⊗ₜ y)).trans
    (by rw [tensorHom_tmul]; rfl)

end

section

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The adjoint transpose of the comparison morphism is natural in both module arguments. -/
lemma comparisonTranspose_naturality
    {A₁ A₂ B₁ B₂ : SheafOfModules.{u} (structureRingSheaf Y)} (u : A₁ ⟶ A₂) (v : B₁ ⟶ B₂) :
    (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩)).map
        ((u, v) : ((A₁, B₁) : _ × _) ⟶ (A₂, B₂)) ≫
        comparisonTranspose f A₂ B₂ =
      comparisonTranspose f A₁ B₁ ≫ (pushforwardFunctor f).map
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            ⟨(X).presheaf, (X).IsSheaf⟩)).map
            (((pullbackFunctor f).map u, (pullbackFunctor f).map v) :
          (((pullbackFunctor f).obj A₁, (pullbackFunctor f).obj B₁) : _ × _) ⟶
            ((pullbackFunctor f).obj A₂, (pullbackFunctor f).obj B₂))) := by
  refine sheafification_hom_ext (tensorObj_hom_ext fun U x y ↦ ?_)
  have key : ∀ (x : A₁.val.obj U) (y : B₁.val.obj U),
      Hom.app (comparisonTranspose f A₂ B₂).val U
        (Hom.app ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            ⟨(Y).presheaf, (Y).IsSheaf⟩)).map
            ((u, v) : ((A₁, B₁) : _ × _) ⟶ (A₂, B₂))).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := Y.sheaf.obj) A₁.val B₁.val)) U (x ⊗ₜ y))) =
      Hom.app ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩)).map
          (((pullbackFunctor f).map u, (pullbackFunctor f).map v) :
          (((pullbackFunctor f).obj A₁, (pullbackFunctor f).obj B₁) : _ × _) ⟶
            ((pullbackFunctor f).obj A₂, (pullbackFunctor f).obj B₂))).val
        ((opensMap f).op.obj U)
        (Hom.app (comparisonTranspose f A₁ B₁).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj (O := Y.sheaf.obj) A₁.val B₁.val)) U (x ⊗ₜ y))) := by
    intro x y
    rw [tensorSheaf_map_unit_tmul, comparisonTranspose_unit_tmul,
      comparisonTranspose_unit_tmul, comparisonApp, comparisonApp,
      tensorSheaf_map_unit_tmul, pullbackUnit_naturality, pullbackUnit_naturality]
  exact key x y

/-- **Stacks 01CD**, functoriality: the comparison morphism as a morphism of bifunctors, so
that naturality in both module arguments is part of the datum. -/
noncomputable def comparisonNatTrans :
    Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨(Y).presheaf, (Y).IsSheaf⟩) ⋙ pullbackFunctor f ⟶
      Functor.prod (pullbackFunctor f) (pullbackFunctor f) ⋙ Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩) where
  app P := comparison f P.1 P.2
  naturality P Q uv := by
    have h : (pullbackFunctor f).map ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(Y).presheaf, (Y).IsSheaf⟩)).map
            ((uv.1, uv.2) : ((P.1, P.2) : _ × _) ⟶ (Q.1, Q.2))) ≫ comparison f Q.1 Q.2 =
        comparison f P.1 P.2 ≫ (Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            ⟨(X).presheaf, (X).IsSheaf⟩)).map
          (((pullbackFunctor f).map uv.1, (pullbackFunctor f).map uv.2) :
            (((pullbackFunctor f).obj P.1, (pullbackFunctor f).obj P.2) : _ × _) ⟶
              ((pullbackFunctor f).obj Q.1, (pullbackFunctor f).obj Q.2)) := by
      have leftNaturality := (pullbackAdjunction f).homEquiv_naturality_left_symm
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            ⟨Y.presheaf, Y.IsSheaf⟩)).map uv)
        (comparisonTranspose f Q.1 Q.2)
      have rightNaturality := (pullbackAdjunction f).homEquiv_naturality_right_symm
        (comparisonTranspose f P.1 P.2)
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩)).map
              (((pullbackFunctor f).map uv.1, (pullbackFunctor f).map uv.2) :
                ((pullbackFunctor f).obj P.1, (pullbackFunctor f).obj P.2) ⟶
                  ((pullbackFunctor f).obj Q.1, (pullbackFunctor f).obj Q.2)))
      exact leftNaturality.symm.trans
        ((congrArg ((pullbackAdjunction f).homEquiv _ _).symm
          (comparisonTranspose_naturality f uv.1 uv.2)).trans rightNaturality)
    exact h

/-- The component of `comparisonNatTrans` at `(A, B)` is `comparison f A B`. -/
lemma comparisonNatTrans_app (A B : SheafOfModules.{u} (structureRingSheaf Y)) :
    (comparisonNatTrans f).app (A, B) = comparison f A B := rfl

end

section Consequences

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- `comparison_homEquiv_unit_tmul`, restated over
`structureSheafRing` and `RingedSpaceModuleAdjunction.modulePullback`:
the adjoint transpose of the component of `comparisonNatTrans` at `(F, G)` carries the
sheafification-unit image of a pure tensor to the image, under the corresponding unit on `X`,
of the tensor of the two pullback-unit images. -/
lemma comparisonNatTrans_homEquiv_unit_tmul (F G : SheafOfModules.{u} (structureSheafRing Y))
    (U : (Opens Y.carrier)ᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) :
    ((modulePullbackPushforwardAdjunction f).homEquiv
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            ⟨(Y).presheaf, (Y).IsSheaf⟩)).obj (F, G))
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            ⟨(X).presheaf, (X).IsSheaf⟩)).obj
            ((modulePullback f).obj F, (modulePullback f).obj G))
        ((comparisonNatTrans f).app (F, G))).val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
        (PresheafOfModules.tensorObj (O := Y.sheaf.obj) F.val G.val)).app U
        (x ⊗ₜ[Y.sheaf.obj.obj U] y)) =
    ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
      (PresheafOfModules.tensorObj (O := X.sheaf.obj) ((modulePullback f).obj F).val
        ((modulePullback f).obj G).val)).app ((opensMap f).op.obj U)
      (((modulePullbackPushforwardAdjunction f).unit.app F).val.app U x ⊗ₜ[
          X.sheaf.obj.obj ((opensMap f).op.obj U)]
        ((modulePullbackPushforwardAdjunction f).unit.app G).val.app U y) :=
  comparison_homEquiv_unit_tmul f F G U x y

/-- **Stacks 01CD** reduces exactly to invertibility of the components of the comparison: as
soon as every component is an isomorphism, the comparison is an isomorphism of bifunctors, and
by `comparison_unique` it is the only candidate.  The instance argument is supplied by
`Stacks.RingedSpace.comparisonNatTrans_app_isIso`. -/
noncomputable def comparisonIso
    [∀ P : SheafOfModules.{u} (structureRingSheaf Y) ×
        SheafOfModules.{u} (structureRingSheaf Y), IsIso ((comparisonNatTrans f).app P)] :
    Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨(Y).presheaf, (Y).IsSheaf⟩) ⋙ pullbackFunctor f ≅
      Functor.prod (pullbackFunctor f) (pullbackFunctor f) ⋙ Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩) :=
  letI : ∀ modulePair :
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩) ×
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩),
      IsIso ((comparisonNatTrans f).app modulePair) :=
    (inferInstance : ∀ modulePair : SheafOfModules.{u} (structureRingSheaf Y) ×
      SheafOfModules.{u} (structureRingSheaf Y), IsIso ((comparisonNatTrans f).app modulePair))
  haveI : IsIso (comparisonNatTrans f) := NatIso.isIso_of_isIso_app _
  asIso (comparisonNatTrans f)

/-- The forward morphism of `comparisonIso` is `comparisonNatTrans`. -/
lemma comparisonIso_hom
    [∀ P : SheafOfModules.{u} (structureRingSheaf Y) ×
        SheafOfModules.{u} (structureRingSheaf Y), IsIso ((comparisonNatTrans f).app P)] :
    (comparisonIso f).hom = comparisonNatTrans f := rfl

end Consequences

end Stacks.RingedSpace
