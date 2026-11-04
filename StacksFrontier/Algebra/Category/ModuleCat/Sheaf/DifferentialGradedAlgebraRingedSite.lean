module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackConstruction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of sheaves of differential graded algebras at a morphism of ringed sites

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraFunctoriality` proves the
three parts of the Stacks remark on functoriality of sheaves of differential graded algebras for
an *abstract* adjunction `L ⊣ G` between categories of sheaves of modules with `L` additive
strong monoidal and `G` additive lax monoidal. This file **instantiates that machinery at the
inverse image `f^*` and the direct image `f_*` of a morphism of ringed sites**, which is the
situation the remark is stated in:

* `f_*` carries a sheaf of differential graded `O_X`-algebras `A` to the sheaf of differential
  graded `O_Y`-algebras `(f_*A, f_*d)`, functorially — part (1);
* `f^*` carries a sheaf of differential graded `O_Y`-algebras `B` to `(f^*B, f^*d)`,
  functorially — part (2);
* the two are adjoint, so homomorphisms `f^*B ⟶ A` of sheaves of differential graded
  `O_X`-algebras correspond bijectively to homomorphisms `B ⟶ f_*A` of sheaves of differential
  graded `O_Y`-algebras — part (3).

A morphism of ringed sites `f : X ⟶ Y` is `AlgebraicGeometry.RingedSite.Hom`: a functor
`u : Y.C ⥤ X.C` in the opposite direction which is a morphism of sites, together with the
structure map `f^♯ : O_Y ⟶ f_*O_X`. The inverse image of sheaves of modules along it is
`Stacks.DifferentialGradedInverseImage.inverseImageModules`, additive by
`Stacks.PullbackMonoidalSite.pullback_additive` and strong monoidal by
`Stacks.DifferentialGradedInverseImage.inverseImageMonoidal`; the direct image is
`CategoryTheory.SheafOfModules.pushforward`, additive by
`Stacks.DifferentialGradedPullbackConstruction.pushforward_additive` and lax monoidal by
`Stacks.DifferentialGradedPullbackConstruction.pushforwardLaxMonoidal`.

## Main definitions

* `Stacks.DifferentialGradedRingedSite.pushforwardAlgebraFunctor`: **the direct image functor on
  sheaves of differential graded algebras**, for a continuous functor of sites together with a
  structure map. Its value at `A` is
  `Stacks.DifferentialGradedPullbackConstruction.pushforwardAlgebra`.
* `Stacks.DifferentialGradedRingedSite.inverseImagePushforwardAlgebraAdjunction`: **the inverse
  image functor is left adjoint to the direct image functor** on sheaves of differential graded
  algebras.
* `AlgebraicGeometry.RingedSite.Hom.dgaPushforward`,
  `AlgebraicGeometry.RingedSite.Hom.dgaPullback` and
  `AlgebraicGeometry.RingedSite.Hom.dgaAdjunction`: the same three for a morphism of ringed
  sites, with the structure map read off the morphism.

## Main results

* `Stacks.DifferentialGradedRingedSite.inverseImagePushforwardAlgebraAdjunction_homEquiv`: the
  hom-set bijection of the adjunction is
  `Stacks.DifferentialGradedPullbackConstruction.structureMapEquiv`, the bijection
  `(f^*B ⟶ A) ≃ (B ⟶ f_*A)` already used to produce the structure map of a pullback of modules.
* `AlgebraicGeometry.RingedSite.Hom.dgaHomEquiv`: that bijection at a morphism of ringed sites,
  which is part (3) of the remark verbatim.
* `AlgebraicGeometry.RingedSite.Hom.dgaPushforward_obj_complex` and
  `AlgebraicGeometry.RingedSite.Hom.dgaPullback_obj_complex`: the differentials of `f_*A` and
  `f^*B` are `f_*d` and `f^*d`, the cochain complexes being the direct and inverse image of
  those of `A` and `B` degreewise.
* `AlgebraicGeometry.RingedSite.Hom.dgaPushforward_obj_toGradedAlgebra` and
  `AlgebraicGeometry.RingedSite.Hom.dgaPullback_obj_toGradedAlgebra`: the underlying sheaves of
  graded algebras are the direct and inverse image of Tag 0FQX, so the two objects of parts (1)
  and (2) are the ones the remark names.

## Implementation notes

**What the instantiation supplies, and what was already there.** The object-level parts are in
place: `Stacks.DifferentialGradedInverseImage.inverseImageAlgebraFunctor` is part (2) at a
continuous functor of sites, and
`Stacks.DifferentialGradedPullbackConstruction.pushforwardAlgebra` and `structureMapEquiv` are
the direct image of one algebra and the bijection of part (3). What is added here is the direct
image as a **functor** and the bijection as an **adjunction between the two functors of parts
(1) and (2)**, and then all three at a morphism of ringed sites rather than at an unpackaged
functor-plus-structure-map.

**The monoidal-adjunction compatibility of part (3) needs no new argument.**
`CategoryTheory.Adjunction.IsMonoidal` — the compatibility of the tensorator of `f^*` with that
of `f_*` which `differentialGradedAlgebraAdjunction` consumes — holds for free once the lax
monoidal structure on `f_*` is taken to be `CategoryTheory.Adjunction.rightAdjointLaxMonoidal` of
the adjunction `f^* ⊣ f_*` itself, by Mathlib's instance to that effect. That is exactly how
`Stacks.DifferentialGradedPullbackConstruction.pushforwardLaxMonoidal` is defined, so the
compatibility is already available at the ringed-site level and nothing here has to build it.

**Hypotheses beyond being a morphism of ringed sites.** `[RepresentablyFlat]` and `[Final]` on
the functor of sites, the two `HasSheafCompose`, `WEqualsLocallyBijective` and `HasSheafify`
hypotheses, the two sheaf conditions on the structure presheaves of rings, and the adjointness of
the direct image are carried unchanged from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInverseImage`, where they are
what makes `f^*` strong monoidal for the tensor product of Tag 01CA. They restrict which
morphisms of ringed sites the three parts are available for; they do not weaken any of the three
conclusions.

**Universes.** A single universe `u`, as in the imported site-level files: the monoidality of
`f^*` rests on `Stacks.PullbackTensor.pullbackTensorIso`, stated for small sites with the modules
in the same universe. So the ringed sites here are `AlgebraicGeometry.RingedSite.{u, u, u}`.

## References

* [Stacks Project, Tag 0FRG](https://stacks.math.columbia.edu/tag/0FRG) — functoriality of
  sheaves of differential graded algebras for a morphism of ringed topoi.
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX) — functoriality of
  sheaves of graded algebras.
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD) — ringed sites and their
  morphisms.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf Functor
open Stacks.SheafOfModules.TensorSheafification Stacks.PullbackMonoidalSite
open Stacks.DifferentialGradedInverseImage Stacks.DifferentialGradedPullbackConstruction

universe u

namespace Stacks.DifferentialGradedRingedSite

/-! ### The direct image functor and the adjunction, at a functor of sites with a structure map -/

section Site

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [Functor.IsContinuous F J K] [RepresentablyFlat F] [F.Final]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}} {Psharp : Sheaf K CommRingCat.{u}}
  (α : Osharp.obj ⟶ F.op ⋙ Psharp.obj)
  (hO : Presheaf.IsSheaf J (structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K (structureRingPresheaf Psharp.obj))
  [radj : (SheafOfModules.pushforward.{u} (sheafRingHom α hO hP)).IsRightAdjoint]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
attribute [local instance] inverseImageMonoidal
attribute [local instance] pushforward_additive
attribute [local instance] pushforwardLaxMonoidal

/-- **The direct image functor on sheaves of differential graded algebras.** Its value at `A` is
the sheaf of differential graded algebras `f_*A` of
`Stacks.DifferentialGradedPullbackConstruction.pushforwardAlgebra`, whose cochain complex is the
direct image of that of `A` degreewise and whose differential is `f_*d`; on a homomorphism it is
the direct image degreewise. -/
noncomputable def pushforwardAlgebraFunctor :
    SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp) ⥤
      SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp) :=
  SheafOfModules.DifferentialGradedAlgebra.pushforwardDifferentialGradedAlgebra
    (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)) hP hO

/-- The direct image functor sends `A` to the sheaf of differential graded algebras
`Stacks.DifferentialGradedPullbackConstruction.pushforwardAlgebra α hO hP A`. -/
@[simp]
theorem pushforwardAlgebraFunctor_obj
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)) :
    (pushforwardAlgebraFunctor α hO hP).obj A = pushforwardAlgebra α hO hP A :=
  rfl

/-- In each degree `n`, the direct image of a homomorphism `φ` of sheaves of differential graded
algebras is the direct image of the degree `n` component of `φ`. -/
@[simp]
theorem pushforwardAlgebraFunctor_map_f
    {A B : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)} (φ : A ⟶ B)
    (n : ℤ) :
    ((pushforwardAlgebraFunctor α hO hP).map φ).toHomologicalComplex.f n =
      (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
        (φ.toHomologicalComplex.f n) :=
  rfl

/-- The underlying sheaf of graded algebras of `f_*A` is the direct image of that of `A` in the
sense of the functoriality of sheaves of graded algebras: its homogeneous pieces are the direct
images of those of `A`. -/
theorem pushforwardAlgebraFunctor_obj_toGradedAlgebra
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)) :
    ((pushforwardAlgebraFunctor α hO hP).obj A).toGradedAlgebra =
      SheafOfModules.GradedAlgebra.transport
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)) A.toGradedAlgebra hP hO :=
  rfl

/-- The underlying sheaf of graded algebras of `f^*B` is the inverse image of that of `B` in the
sense of the functoriality of sheaves of graded algebras. -/
theorem inverseImageAlgebraFunctor_obj_toGradedAlgebra
    (B : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)) :
    ((inverseImageAlgebraFunctor α hO hP).obj B).toGradedAlgebra =
      SheafOfModules.GradedAlgebra.transport
        (inverseImageModules α hO hP) B.toGradedAlgebra hO hP :=
  rfl

/-- **The inverse image functor on sheaves of differential graded algebras is left adjoint to the
direct image functor.** The two functors are
`Stacks.DifferentialGradedInverseImage.inverseImageAlgebraFunctor` and
`pushforwardAlgebraFunctor`, not functors merely asserted to exist. -/
noncomputable def inverseImagePushforwardAlgebraAdjunction :
    inverseImageAlgebraFunctor α hO hP ⊣ pushforwardAlgebraFunctor α hO hP :=
  SheafOfModules.DifferentialGradedAlgebra.differentialGradedAlgebraAdjunction
    (inverseImageAdjunction α hO hP) hP hO

/-- The hom-set bijection of the adjunction is
`Stacks.DifferentialGradedPullbackConstruction.structureMapEquiv`: a homomorphism `f^*B ⟶ A` of
sheaves of differential graded algebras is a homomorphism `B ⟶ f_*A`. -/
theorem inverseImagePushforwardAlgebraAdjunction_homEquiv
    (B : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp))
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (toRingCat K Psharp)) :
    (inverseImagePushforwardAlgebraAdjunction α hO hP).homEquiv B A =
      structureMapEquiv α hO hP B A :=
  congrFun (congrFun
    (SheafOfModules.DifferentialGradedAlgebra.differentialGradedAlgebraAdjunction_homEquiv
      (inverseImageAdjunction α hO hP) hP hO) B) A

end Site

end Stacks.DifferentialGradedRingedSite

/-! ### The three parts at a morphism of ringed sites -/

namespace AlgebraicGeometry.RingedSite.Hom

open Stacks.DifferentialGradedRingedSite

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- The structure map `f^♯ : O_Y ⟶ f_*O_X` of a morphism of ringed sites, read as a morphism of
the underlying presheaves of commutative rings, which is the datum the inverse image and direct
image of sheaves of modules consume. -/
def structureMapPresheaf : Y.O.obj ⟶ f.u.op ⋙ X.O.obj :=
  f.fsharp.hom

section

variable [RepresentablyFlat f.u] [f.u.Final]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [CategoryTheory.HasSheafify Y.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [CategoryTheory.HasSheafify X.J AddCommGrpCat.{u}]
  (hY : Presheaf.IsSheaf Y.J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Y.O.obj))
  (hX : Presheaf.IsSheaf X.J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.O.obj))
  [(SheafOfModules.pushforward.{u}
    (Stacks.PullbackMonoidalSite.sheafRingHom (structureMapPresheaf f) hY hX)).IsRightAdjoint]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
attribute [local instance] Stacks.DifferentialGradedInverseImage.inverseImageMonoidal
attribute [local instance] Stacks.DifferentialGradedPullbackConstruction.pushforward_additive
attribute [local instance] Stacks.DifferentialGradedPullbackConstruction.pushforwardLaxMonoidal

/-- **The direct image of a sheaf of differential graded algebras along a morphism of ringed
sites.** Its underlying sheaf of graded algebras is the direct image of that of `A` and its
differential is `f_*d`; this is part (1) of the functoriality of sheaves of differential graded
algebras. -/
@[stacks 0FRG "part (1) at a morphism of ringed sites: `(f_*A, f_*d)`, functorially"]
noncomputable def dgaPushforward :
    SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat X.J X.O) ⥤
      SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat Y.J Y.O) :=
  pushforwardAlgebraFunctor (structureMapPresheaf f) hY hX

/-- **The inverse image of a sheaf of differential graded algebras along a morphism of ringed
sites.** Its underlying sheaf of graded algebras is the inverse image of that of `B` and its
differential is `f^*d`; this is part (2) of the functoriality of sheaves of differential graded
algebras. -/
@[stacks 0FRG "part (2) at a morphism of ringed sites: `(f^*B, f^*d)`, functorially"]
noncomputable def dgaPullback :
    SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat Y.J Y.O) ⥤
      SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat X.J X.O) :=
  Stacks.DifferentialGradedInverseImage.inverseImageAlgebraFunctor
    (structureMapPresheaf f) hY hX

/-- The direct image of `A` along a morphism of ringed sites is the sheaf of differential graded
algebras `Stacks.DifferentialGradedPullbackConstruction.pushforwardAlgebra` of `A`. -/
@[simp]
theorem dgaPushforward_obj
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat X.J X.O)) :
    (dgaPushforward f hY hX).obj A =
      Stacks.DifferentialGradedPullbackConstruction.pushforwardAlgebra
        (structureMapPresheaf f) hY hX A :=
  rfl

/-- The inverse image of `B` along a morphism of ringed sites is the sheaf of differential graded
algebras `Stacks.DifferentialGradedInverseImage.inverseImageAlgebra` of `B`. -/
@[simp]
theorem dgaPullback_obj
    (B : SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat Y.J Y.O)) :
    (dgaPullback f hY hX).obj B =
      Stacks.DifferentialGradedInverseImage.inverseImageAlgebra
        (structureMapPresheaf f) hY hX B :=
  rfl

/-- **The differential of `f_*A` is `f_*d`**: its cochain complex is the direct image of the
cochain complex of `A` degreewise. -/
@[stacks 0FRG "part (1) at a morphism of ringed sites: `(f_*A, f_*d)`, functorially"]
theorem dgaPushforward_obj_complex
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat X.J X.O)) :
    ((dgaPushforward f hY hX).obj A).complex =
      ((SheafOfModules.pushforward.{u} (Stacks.DifferentialGradedInverseImage.inverseImageRingHom
            (structureMapPresheaf f) hY hX)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        A.complex :=
  rfl

/-- **The differential of `f^*B` is `f^*d`**: its cochain complex is the inverse image of the
cochain complex of `B` degreewise. -/
@[stacks 0FRG "part (2) at a morphism of ringed sites: `(f^*B, f^*d)`, functorially"]
theorem dgaPullback_obj_complex
    (B : SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat Y.J Y.O)) :
    ((dgaPullback f hY hX).obj B).complex =
      ((Stacks.DifferentialGradedInverseImage.inverseImageModules
          (structureMapPresheaf f) hY hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        B.complex :=
  rfl

/-- **The underlying sheaf of graded algebras of `f_*A` is the direct image of that of `A`**, in
the sense of the functoriality of sheaves of graded algebras: so `f_*A` really is the sheaf of
graded algebras of that remark, equipped with the differential `f_*d`. -/
@[stacks 0FRG "part (1) at a morphism of ringed sites: `(f_*A, f_*d)`, functorially"]
theorem dgaPushforward_obj_toGradedAlgebra
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat X.J X.O)) :
    ((dgaPushforward f hY hX).obj A).toGradedAlgebra =
      SheafOfModules.GradedAlgebra.transport
        (SheafOfModules.pushforward.{u} (Stacks.DifferentialGradedInverseImage.inverseImageRingHom
          (structureMapPresheaf f) hY hX)) A.toGradedAlgebra hX hY :=
  pushforwardAlgebraFunctor_obj_toGradedAlgebra (structureMapPresheaf f) hY hX A

/-- **The underlying sheaf of graded algebras of `f^*B` is the inverse image of that of `B`**, in
the sense of the functoriality of sheaves of graded algebras: so `f^*B` really is the sheaf of
graded algebras of that remark, equipped with the differential `f^*d`. -/
@[stacks 0FRG "part (2) at a morphism of ringed sites: `(f^*B, f^*d)`, functorially"]
theorem dgaPullback_obj_toGradedAlgebra
    (B : SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat Y.J Y.O)) :
    ((dgaPullback f hY hX).obj B).toGradedAlgebra =
      SheafOfModules.GradedAlgebra.transport
        (Stacks.DifferentialGradedInverseImage.inverseImageModules
          (structureMapPresheaf f) hY hX) B.toGradedAlgebra hY hX :=
  inverseImageAlgebraFunctor_obj_toGradedAlgebra (structureMapPresheaf f) hY hX B

/-- **The inverse image of sheaves of differential graded algebras along a morphism of ringed
sites is left adjoint to the direct image.** This is part (3) of the functoriality of sheaves of
differential graded algebras, its two functors being those of parts (2) and (1). -/
@[stacks 0FRG "part (3) at a morphism of ringed sites: `(f^*B ⟶ A) ≃ (B ⟶ f_*A)`"]
noncomputable def dgaAdjunction : dgaPullback f hY hX ⊣ dgaPushforward f hY hX :=
  inverseImagePushforwardAlgebraAdjunction (structureMapPresheaf f) hY hX

/-- **Homomorphisms `f^*B ⟶ A` of sheaves of differential graded `O_X`-algebras are in
bijection with homomorphisms `B ⟶ f_*A` of sheaves of differential graded `O_Y`-algebras**, the
bijection being the hom-set bijection of `dgaAdjunction`. -/
noncomputable def dgaHomEquiv
    (B : SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat Y.J Y.O))
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat X.J X.O)) :
    ((dgaPullback f hY hX).obj B ⟶ A) ≃ (B ⟶ (dgaPushforward f hY hX).obj A) :=
  (dgaAdjunction f hY hX).homEquiv B A

/-- The bijection of part (3) is
`Stacks.DifferentialGradedPullbackConstruction.structureMapEquiv`, the bijection along which the
pullback of a differential graded module extends scalars. -/
theorem dgaHomEquiv_eq
    (B : SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat Y.J Y.O))
    (A : SheafOfModules.DifferentialGradedAlgebra.{u, u} (Sheaf.toRingCat X.J X.O)) :
    dgaHomEquiv f hY hX B A =
      Stacks.DifferentialGradedPullbackConstruction.structureMapEquiv
        (structureMapPresheaf f) hY hX B A :=
  inverseImagePushforwardAlgebraAdjunction_homEquiv (structureMapPresheaf f) hY hX B A

end

end AlgebraicGeometry.RingedSite.Hom

end
