module

public import Mathlib.Tactic.TermCongr
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# The underlying module of an algebra sheaf is functorial

Let `X` be a scheme.  `Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` sends a sheaf of
commutative `𝒪_X`-algebras to the `𝒪_X`-module obtained by restricting scalars along its
structure morphism.  This file makes that assignment a functor
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleFunctor` on morphisms of algebra sheaves, and
deduces that quasi-coherence of an algebra sheaf depends only on its isomorphism class.

That last statement was the standing blocker on both Stacks Tag 05JT and Stacks Tag 0817: any
construction of a quasi-coherent subalgebra produces a concrete monomorphism, and the property
then has to be moved to whatever representative `CategoryTheory.Subobject.mk` chooses.  The
three other conditions in play (integrality, finiteness, finite presentation) already transport,
by `Stacks.RelativeSpec.AlgebraSheaf.isIntegral_of_iso` and its two companions, and finite type
transports by `Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_iso`, because all
four are conditions on the structure morphism alone.  Quasi-coherence is not: it is a condition
on the restriction of scalars of a different object.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.ringSheafMap`: the morphism of sheaves of rings underlying a
  morphism of algebra sheaves.
* `Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap` and
  `Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleFunctor`: the induced morphism of underlying
  `𝒪_X`-modules, and the functor `AlgebraSheaf X ⥤ X.Modules` it assembles into.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.structureMap_comp_ringSheafMap`: a morphism of algebra
  sheaves is a morphism over the structure sheaf.
* `Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_of_iso`: quasi-coherence of an algebra sheaf
  depends only on its isomorphism class.

## Implementation notes

The functoriality that `Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean` is missing
is naturality of `SheafOfModules.restrictScalars` in the ring morphism: there is no comparison
between `restrictScalars α` and `restrictScalars α'` for two morphisms of sheaves of rings out
of the same base.  That generality is not needed here, and asking for it is what made the
transport look blocked.  In the situation at hand the base is fixed and the module is the
algebra itself, so the comparison map is just the morphism of algebras: a morphism
`f : A ⟶ B` of algebra sheaves is `𝒪_X`-linear for the two restricted actions because
`f (φ_A r · a) = f (φ_A r) · f a = φ_B r · f a`, the middle step being that `f` is a ring map and
the last being `structureMap_comp_ringSheafMap`.  So the whole construction is sectionwise and
needs nothing about `X`.

Three mechanical points:

* `Stacks.RelativeSpec.AlgebraSheaf.ringSheaf` is a semireducible `def` occupying the *type* of
  the composite in `structureMap_comp_ringSheafMap`, so `rw` fails there -- `rw` elaborates its
  congruence motive at `implicit` transparency and reports the goal as not type-correct.  That
  proof is therefore in term mode, out of `CategoryTheory.Functor.map_comp` and
  `CategoryTheory.Under.w`.
* The sectionwise linear map cannot be written with `ModuleCat.ofHom`: its source and target are
  `ModuleCat.restrictScalars` objects, whose `Module` instance lives in the bundled object and
  is invisible to instance search once the carrier type is unfolded.  `ConcreteCategory.ofHom`
  takes the two `ModuleCat` objects themselves and is immune.
* For the same reason the semilinearity computation is a separate lemma,
  `ringSheafMap_app_mul_structureMap_app`, stated purely about sections of the sheaves of rings;
  writing it inline forces the scalar action and the ring multiplication into one `HMul`
  instance search, which fails on two defeq but syntactically different carrier types.  Stated
  separately it is accepted at the restricted-module goal by a defeq check, since the restricted
  action is `Module.compHom` and unfolds to the multiplication.

## References

* [The Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [The Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}}

/-- Post-composition of sheaves of commutative rings with the forgetful functor to rings. -/
private abbrev forgetRingSheaf (X : Scheme.{u}) :=
  sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)

/-- The morphism of sheaves of rings underlying a morphism of algebra sheaves. -/
def ringSheafMap {A B : AlgebraSheaf X} (f : A ⟶ B) : ringSheaf A ⟶ ringSheaf B :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).map f.right

/-- `ringSheafMap` sends the identity to the identity. -/
@[simp]
theorem ringSheafMap_id (A : AlgebraSheaf X) : ringSheafMap (𝟙 A) = 𝟙 (ringSheaf A) :=
  (forgetRingSheaf X).map_id A.right

/-- `ringSheafMap` is compatible with composition. -/
@[simp]
theorem ringSheafMap_comp {A B C : AlgebraSheaf X} (f : A ⟶ B) (g : B ⟶ C) :
    ringSheafMap (f ≫ g) = ringSheafMap f ≫ ringSheafMap g :=
  (forgetRingSheaf X).map_comp f.right g.right

/-- **A morphism of algebra sheaves is a morphism over the structure sheaf.**  This is
`CategoryTheory.Under.w` pushed through the forgetful functor to sheaves of rings, and it is
the only input to the `𝒪_X`-linearity of `underlyingModuleMap`. -/
theorem structureMap_comp_ringSheafMap {A B : AlgebraSheaf X} (f : A ⟶ B) :
    structureMap A ≫ ringSheafMap f = structureMap B :=
  ((forgetRingSheaf X).map_comp A.hom f.right).symm.trans
    (congrArg _ (Under.w f))

/-- Sectionwise form of `structureMap_comp_ringSheafMap`. -/
theorem ringSheafMap_app_structureMap_app {A B : AlgebraSheaf X} (f : A ⟶ B)
    (U : (X.Opens)ᵒᵖ) (r : (X.ringCatSheaf.obj.obj U : Type u)) :
    (ringSheafMap f).hom.app U ((structureMap A).hom.app U r) =
      (structureMap B).hom.app U r :=
  have h : (structureMap A).hom.app U ≫ (ringSheafMap f).hom.app U =
      (structureMap B).hom.app U :=
    congrArg (fun φ : X.ringCatSheaf ⟶ ringSheaf B => φ.hom.app U)
      (structureMap_comp_ringSheafMap f)
  congr($(h).hom r)

/-- Sectionwise `𝒪_X`-linearity of `ringSheafMap`, written out as a statement about the
multiplication of the sheaves of rings rather than about the restricted scalar actions.  Stating
it this way is what makes it usable: the two restricted actions unfold to these two
multiplications, but written inline the goal forces an `HMul` instance search across two defeq
but syntactically distinct carrier types. -/
theorem ringSheafMap_app_mul_structureMap_app {A B : AlgebraSheaf X} (f : A ⟶ B)
    (U : (X.Opens)ᵒᵖ) (r : (X.ringCatSheaf.obj.obj U : Type u))
    (x : ((ringSheaf A).obj.obj U : Type u)) :
    (ringSheafMap f).hom.app U (((structureMap A).hom.app U).hom r * x) =
      ((structureMap B).hom.app U).hom r * (ringSheafMap f).hom.app U x := by
  rw [map_mul, ringSheafMap_app_structureMap_app]

/-- Sectionwise naturality of `ringSheafMap`. -/
theorem ringSheafMap_app_map {A B : AlgebraSheaf X} (f : A ⟶ B) {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V)
    (x : ((ringSheaf A).obj.obj U : Type u)) :
    (ringSheafMap f).hom.app V ((ringSheaf A).obj.map i x) =
      (ringSheaf B).obj.map i ((ringSheafMap f).hom.app U x) :=
  congrArg (fun φ : (ringSheaf A).obj.obj U ⟶ (ringSheaf B).obj.obj V => φ.hom x)
    ((ringSheafMap f).hom.naturality i)

/-- The sections of a morphism of algebra sheaves over an open, as an `𝒪_X(U)`-linear map
between the sections of the underlying modules. -/
def underlyingModuleLinear {A B : AlgebraSheaf X} (f : A ⟶ B) (U : (X.Opens)ᵒᵖ) :
    (underlyingModule A).val.obj U →ₗ[X.ringCatSheaf.obj.obj U]
      (underlyingModule B).val.obj U where
  toFun x := (ringSheafMap f).hom.app U x
  map_add' x y := map_add ((ringSheafMap f).hom.app U).hom x y
  map_smul' r x := ringSheafMap_app_mul_structureMap_app f U r x

/-- The morphism of underlying presheaves of modules induced by a morphism of algebra sheaves:
sectionwise `underlyingModuleLinear`, natural by naturality of the morphism of sheaves of
rings. -/
def underlyingModuleValMap {A B : AlgebraSheaf X} (f : A ⟶ B) :
    (underlyingModule A).val ⟶ (underlyingModule B).val where
  app U := ConcreteCategory.ofHom (C := ModuleCat (X.ringCatSheaf.obj.obj U))
    (underlyingModuleLinear f U)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => ?_
    exact ringSheafMap_app_map f i x

/-- On sections, the morphism of underlying modules is the morphism of sheaves of rings. -/
@[simp]
theorem underlyingModuleValMap_app_apply {A B : AlgebraSheaf X} (f : A ⟶ B) (U : (X.Opens)ᵒᵖ)
    (x : ((underlyingModule A).val.obj U : Type u)) :
    (underlyingModuleValMap f).app U x = (ringSheafMap f).hom.app U x :=
  rfl

/-- The morphism of underlying `𝒪_X`-modules induced by a morphism of algebra sheaves. -/
def underlyingModuleMap {A B : AlgebraSheaf X} (f : A ⟶ B) :
    underlyingModule A ⟶ underlyingModule B :=
  show SheafOfModules.Hom _ _ from { val := underlyingModuleValMap f }

/-- **The underlying `𝒪_X`-module of an algebra sheaf, as a functor.**  This is the naturality
that `Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean` does not provide for
`SheafOfModules.restrictScalars`, in the only generality the two colimit tags need. -/
def underlyingModuleFunctor (X : Scheme.{u}) : AlgebraSheaf X ⥤ X.Modules where
  obj A := underlyingModule A
  map f := underlyingModuleMap f
  map_id A := by
    apply SheafOfModules.hom_ext
    refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (ringSheafMap (𝟙 A)).hom.app U x = x
    rw [ringSheafMap_id]
    rfl
  map_comp {A B C} f g := by
    apply SheafOfModules.hom_ext
    refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (ringSheafMap (f ≫ g)).hom.app U x =
      (ringSheafMap g).hom.app U ((ringSheafMap f).hom.app U x)
    rw [ringSheafMap_comp]
    rfl

/-- **Quasi-coherence of an algebra sheaf only depends on its isomorphism class.**  The
counterpart for the four conditions on the structure morphism is
`Stacks.RelativeSpec.AlgebraSheaf.isIntegral_of_iso`,
`Stacks.RelativeSpec.AlgebraSheaf.isFinite_of_iso`,
`Stacks.RelativeSpec.AlgebraSheaf.isFinitePresentation_of_iso` and
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_iso`; this is the fifth, and the
one that was missing.  Quasi-coherence is closed under isomorphism as an
`CategoryTheory.ObjectProperty` of sheaves of modules, so the only content is the isomorphism of
underlying modules, which `underlyingModuleFunctor` supplies. -/
theorem isQuasicoherent_of_iso {A B : AlgebraSheaf X} (e : A ≅ B) (hA : A.IsQuasicoherent) :
    B.IsQuasicoherent :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    ((underlyingModuleFunctor X).mapIso e) hA

end Stacks.RelativeSpec.AlgebraSheaf
