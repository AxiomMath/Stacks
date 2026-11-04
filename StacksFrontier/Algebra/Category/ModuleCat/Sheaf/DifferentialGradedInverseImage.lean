module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSite

/-!
# Inverse image of sheaves of differential graded algebras and modules

Let `F : C ⥤ D` be a continuous functor of sites and `α : O ⟶ F.op ⋙ P` a morphism of presheaves
of commutative rings over it. The inverse image of sheaves of modules
`CategoryTheory.SheafOfModules.pullback` along `α` is additive and strong monoidal for the tensor
product of Tag 01CA — `Stacks.PullbackMonoidalSite.pullback_additive` and
`Stacks.PullbackMonoidalSite.pullbackMonoidalStrict` — so the transports of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraFunctoriality` and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleTransport` apply to it: a
sheaf of differential graded `O`-algebras `A` has an inverse image, a sheaf of differential
graded `P`-algebras whose cochain complex is the inverse image of that of `A` degreewise, and a
right differential graded `A`-module has an inverse image, a right differential graded module
over that algebra.

## Main definitions

* `Stacks.DifferentialGradedInverseImage.inverseImageModules`: the inverse image of sheaves of
  modules along `α`, with `inverseImageMonoidal` its strong monoidal structure.
* `Stacks.DifferentialGradedInverseImage.inverseImageAlgebra`: **the inverse image of a sheaf of
  differential graded algebras**, and `inverseImageAlgebraFunctor` the induced functor, which is
  part (2) of Tag 0FRG at a continuous functor of sites.
* `Stacks.DifferentialGradedInverseImage.inverseImageModule`: **the inverse image of a right
  differential graded `A`-module**, a right differential graded `inverseImageAlgebra A`-module,
  and `inverseImageFunctor` the induced functor.

## Main results

* `Stacks.DifferentialGradedInverseImage.inverseImageAlgebra_complex` and
  `inverseImageModule_complex`: both cochain complexes are the inverse image applied degreewise.
* `Stacks.DifferentialGradedInverseImage.smulSheaf_inverseImageModule`: the morphism-level action
  of the inverse image module is the action of the module conjugated by the tensorator.

## Implementation notes

**Universes: what is forced and by what.** The two sites are small in one universe `u`; the
sheaf of rings, the homogeneous pieces of the algebra and the sections of the modules are at a
free universe `w` with `[UnivLE.{u, w}]`, so they may live in any universe at least as large as
the sites'. Each identification that remains has a single cause.

* `w` is the *one* universe of the rings, of the algebra pieces and of the module sections,
  because the whole file is the transport of one functor
  `inverseImageModules : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w}
  (toRingCat K Psharp)` along the algebra and along the module, and that functor is monoidal
  for `Stacks.TensorSheafWorld.monoidalCategory`, whose sheaf of rings and whose sheaves of
  modules share a universe.
* `UnivLE.{u, w}` and the smallness of the two sites come from
  `Stacks.PullbackMonoidalSite.pullbackMonoidalStrict`, hence from
  `Stacks.PullbackTensor.pullbackTensorIso`, the comparison of Tag 01CD, and from
  `Stacks.PullbackColimit`'s model of the pullback which computes it: the colimit is indexed by
  `CostructuredArrow F.op U`, which is `u`-small and must be small relative to `w`.
* The two sites share `u` for the reason `Stacks.PullbackColimit` records, which is a limitation
  of instance resolution rather than of the mathematics. The differential graded transports
  themselves keep the two sites at independent universes.

`[CategoryTheory.Functor.RepresentablyFlat F]` and `[F.Final]` are the hypotheses that make the
tensorator and the unit of the oplax monoidal structure invertible; neither is a universe
condition.

**Two spellings of the ring sheaf.** `Stacks.SheafOfModules.TensorSheafification.structureSheaf
O hO`, which `Stacks.PullbackMonoidalSite.sheafRingHom` produces, and
`CategoryTheory.Sheaf.toRingCat J O♯` are equal by `rfl`, but a regular definition is not
unfolded by instance search, so an instance found at one spelling is invisible at the other, and
only the second is a key at which `Stacks.TensorSheafWorld.monoidalCategory` — the monoidal
structure the graded machinery consumes — is found. So `inverseImageRingHom` names the morphism
of ring sheaves at the `toRingCat` spelling, `isRightAdjointPushforward` restates the
adjointness hypothesis there, and `inverseImageMonoidal` carries
`Stacks.PullbackMonoidalSite.pullbackMonoidalStrict` across the equality of the two monoidal
structures. Additivity needs none of this: `Stacks.PullbackMonoidalSite.pullback_additive` is an
instance for an arbitrary morphism of sheaves of rings.

## References

* [Stacks Project, Tag 0FRG](https://stacks.math.columbia.edu/tag/0FRG) — functoriality of
  sheaves of differential graded algebras.
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI) — sheaves of
  differential graded modules.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf Functor
open Stacks.SheafOfModules.TensorSheafification Stacks.PullbackMonoidalSite

universe w u

namespace Stacks.DifferentialGradedInverseImage

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [Functor.IsContinuous F J K] [RepresentablyFlat F] [F.Final]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  {Osharp : Sheaf J CommRingCat.{w}} {Psharp : Sheaf K CommRingCat.{w}}
  (α : Osharp.obj ⟶ F.op ⋙ Psharp.obj)
  (hO : Presheaf.IsSheaf J (structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K (structureRingPresheaf Psharp.obj))
  [radj : (SheafOfModules.pushforward.{w} (sheafRingHom α hO hP)).IsRightAdjoint]
  [hUL : UnivLE.{u, w}]

include hUL

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- `α`, read as a morphism of sheaves of not necessarily commutative rings `O ⟶ F_* P`, at the
`CategoryTheory.Sheaf.toRingCat` spelling of the two ring sheaves. -/
noncomputable abbrev inverseImageRingHom :
    toRingCat J Osharp ⟶
      (F.sheafPushforwardContinuous RingCat.{w} J K).obj (toRingCat K Psharp) :=
  sheafRingHom α hO hP

/-- The pushforward of sheaves of modules along `α` is a right adjoint, at the
`CategoryTheory.Sheaf.toRingCat` spelling of the two ring sheaves. -/
instance isRightAdjointPushforward :
    (SheafOfModules.pushforward.{w} (inverseImageRingHom α hO hP)).IsRightAdjoint :=
  radj

/-- The inverse image of sheaves of modules along a continuous functor of sites, at the
`CategoryTheory.Sheaf.toRingCat` spelling of the two ring sheaves. -/
noncomputable abbrev inverseImageModules :
    SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp) :=
  SheafOfModules.pullback.{w} (inverseImageRingHom α hO hP)

/-- **The inverse image of sheaves of modules is strong monoidal** for the monoidal structure of
Tag 01CA, whose tensor product is the tensor product sheaf on the nose. -/
@[instance_reducible]
noncomputable def inverseImageMonoidal : (inverseImageModules α hO hP).Monoidal :=
  pullbackMonoidalStrict α hO hP

attribute [local instance] inverseImageMonoidal

/-- **The inverse image of a sheaf of differential graded algebras** along a continuous functor
of sites: its cochain complex is the inverse image of that of `A` degreewise, and its
multiplication is the multiplication of `A` conjugated by the tensorator. -/
noncomputable def inverseImageAlgebra
    (A : SheafOfModules.DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) :
    SheafOfModules.DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp) :=
  SheafOfModules.DifferentialGradedAlgebra.transport (inverseImageModules α hO hP) hO hP A

/-- The cochain complex of the inverse image of a sheaf of differential graded algebras is the
inverse image of its cochain complex, degreewise. -/
theorem inverseImageAlgebra_complex
    (A : SheafOfModules.DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) :
    (inverseImageAlgebra α hO hP A).complex =
      ((inverseImageModules α hO hP).mapHomologicalComplex (ComplexShape.up ℤ)).obj A.complex :=
  rfl

/-- **The inverse image functor on sheaves of differential graded algebras**, which is part (2)
of the functoriality of sheaves of differential graded algebras at a continuous functor of
sites. -/
noncomputable def inverseImageAlgebraFunctor :
    SheafOfModules.DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp) ⥤
      SheafOfModules.DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp) :=
  SheafOfModules.DifferentialGradedAlgebra.pullbackDifferentialGradedAlgebra
    (inverseImageModules α hO hP) hO hP

/-- The inverse image functor on sheaves of differential graded algebras sends `A` to
`inverseImageAlgebra α hO hP A`. -/
@[simp]
theorem inverseImageAlgebraFunctor_obj
    (A : SheafOfModules.DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) :
    (inverseImageAlgebraFunctor α hO hP).obj A = inverseImageAlgebra α hO hP A :=
  rfl

/-- In each degree `n`, the inverse image of a morphism of sheaves of differential graded algebras
is the inverse image of its degree `n` component. -/
@[simp]
theorem inverseImageAlgebraFunctor_map_f
    {A B : SheafOfModules.DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B)
    (n : ℤ) :
    ((inverseImageAlgebraFunctor α hO hP).map φ).toHomologicalComplex.f n =
      (inverseImageModules α hO hP).map (φ.toHomologicalComplex.f n) :=
  rfl

variable {A : SheafOfModules.DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}

/-- **The inverse image of a right differential graded `A`-module**, a right differential graded
module over the inverse image of `A`: its cochain complex is the inverse image of that of `M`
degreewise, and its action is the action of `M` conjugated by the tensorator. -/
noncomputable def inverseImageModule
    (M : SheafOfModules.DifferentialGradedModule.{w, w, w} A) :
    SheafOfModules.DifferentialGradedModule.{w, w, w} (inverseImageAlgebra α hO hP A) :=
  SheafOfModules.DifferentialGradedModule.transport (inverseImageModules α hO hP) M hO hP

/-- The cochain complex of the inverse image of a right differential graded module is the inverse
image of its cochain complex, degreewise. -/
theorem inverseImageModule_complex (M : SheafOfModules.DifferentialGradedModule.{w, w, w} A) :
    (inverseImageModule α hO hP M).complex =
      ((inverseImageModules α hO hP).mapHomologicalComplex (ComplexShape.up ℤ)).obj M.complex :=
  SheafOfModules.DifferentialGradedModule.transport_complex (inverseImageModules α hO hP) M hO hP

/-- **The morphism-level action of the inverse image module** is the action of `M` conjugated by
the tensorator of the inverse image. -/
@[simp]
theorem smulSheaf_inverseImageModule (M : SheafOfModules.DifferentialGradedModule.{w, w, w} A)
    (n i : ℤ) :
    SheafOfModules.DifferentialGradedModule.smulSheaf (inverseImageModule α hO hP M) n i =
      SheafOfModules.DifferentialGradedModule.transportedSmul (inverseImageModules α hO hP) M
        n i :=
  SheafOfModules.DifferentialGradedModule.smulSheaf_transport (inverseImageModules α hO hP) M
    hO hP n i

/-- **The inverse image functor on right differential graded modules**, from right differential
graded `A`-modules to right differential graded modules over the inverse image of `A`. -/
noncomputable def inverseImageFunctor :
    SheafOfModules.DifferentialGradedModule.{w, w, w} A ⥤
      SheafOfModules.DifferentialGradedModule.{w, w, w} (inverseImageAlgebra α hO hP A) :=
  SheafOfModules.DifferentialGradedModule.transportFunctor (inverseImageModules α hO hP) hO hP

/-- The inverse image functor on right differential graded modules sends `M` to
`inverseImageModule α hO hP M`. -/
@[simp]
theorem inverseImageFunctor_obj (M : SheafOfModules.DifferentialGradedModule.{w, w, w} A) :
    (inverseImageFunctor α hO hP).obj M = inverseImageModule α hO hP M :=
  rfl

/-- In each degree `n`, the inverse image of a morphism of right differential graded modules is
the inverse image of its degree `n` component. -/
@[simp]
theorem inverseImageFunctor_map_f
    {M N : SheafOfModules.DifferentialGradedModule.{w, w, w} A} (φ : M ⟶ N) (n : ℤ) :
    ((inverseImageFunctor α hO hP).map φ).toHomologicalComplex.f n =
      (inverseImageModules α hO hP).map (φ.toHomologicalComplex.f n) :=
  rfl

end Stacks.DifferentialGradedInverseImage

end
