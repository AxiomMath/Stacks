module

public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointSheafStalkCounit

/-!
# The topological stalk of the termwise base change of a complex of sheaves of modules

Let `X` be a topological space, `x` a point of it, and `b : B ⟶ C` a morphism of sheaves of
commutative rings on `X`.  `Stacks.SheafOfModules.towerExtendScalarsComplexes` is extension of
scalars along `b` applied termwise to complexes of sheaves of modules; applied to the naive
cotangent complex it produces `NL_{B/A} ⊗_B C`, the source of the canonical map
`Stacks.SheafOfModules.baseChangeNaiveCotangentMap` of Stacks 0E1Y.

This file computes the stalk at `x` of that complex.  In each degree the stalk of
`(towerExtendScalarsComplexes J B C b).obj K` is

`Cₓ ⊗_{Bₓ} (K.X i)ₓ`,

the identification being `Opens.extendScalarsStalkFunctorIso` — the interchange of extension of
scalars with taking topological stalks — read at the term `K.X i`.  The identification is
compatible with the differential and natural in the complex, so the stalk of the base-changed
complex is the two-term complex obtained by base-changing the stalk of `K`.

Together with `Opens.stalkFunctor_map_towerCounit_eq`, which computes the stalk of the counit
`Stacks.SheafOfModules.towerCounit`, this computes the stalk of
`Stacks.SheafOfModules.baseChangeNaiveCotangentMap`, which is the composite of the map
`Stacks.SheafOfModules.towerExtendScalarsComplexes.map` of the square of Stacks 08TX with that
counit.

## The three scalar rings

Three mutually isomorphic rings are available at `x`, and the choice between them is forced:

* `Stacks.ringFiber (Opens.pointGrothendieckTopology x) C.obj`, the `CommRingCat`-valued fibre of
  `C` at the point of the site of opens attached to `x`.  **This is the ring the statements below
  are over**, because it is the ring `Opens.extendScalarsStalkFunctorIso` is stated over and
  hence the ring over which `ModuleCat.extendScalars` — the `Cₓ ⊗_{Bₓ} -` of the statement — is
  taken.
* `TopCat.Presheaf.stalk (C := RingCat) (Stacks.SheafOfModules.Tensor.ringSheaf
  C).obj x`, the `RingCat`-valued stalk, which is the ring
  `AlgebraicGeometry.SheafOfModules.stalkFunctor` is a functor to modules over, and the ring the
  two linear legs
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` and
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegZeroLinear`, and the linear form
  `Stacks.SheafOfModules.naiveCotangentStalk_eq_naiveCotangentComplexStalk_linear` of Stacks 0D09,
  are stated over.  It appears here as the inner functor of every composite below, and the two
  spellings are reconciled by the restriction of scalars along `Opens.commRingFiberStalkHom`,
  which is built into the statements: a map that is linear over the `RingCat`-valued stalk is
  linear over the fibre after that restriction of scalars, which is exactly what makes the legs
  composable with the identification proved here.  The semilinearity of the identification over
  the `RingCat`-valued stalk is recorded as
  `Opens.stalkTowerExtendScalarsXAddEquiv_smul`.
* the `CommRingCat`-valued stalk of `C`.  **This one is unusable as a scalar ring** on the stalk
  of a term of a naive cotangent complex: instance search for its action reaches the action of
  the stalk of the source sheaf of rings on the same stalk and then has to decide whether the two
  sheaves of rings agree — for `NL_{B/A}` a sheafification — which exceeds
  `synthInstance.maxHeartbeats`.  See the discussion in
  `StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentStalkLinear`.  It does not occur below.

## Main definitions

* `Opens.stalkTowerExtendScalarsXIso`: **the stalk of the termwise base change of a complex,
  degreewise.**  The stalk at `x` of the degree-`i` term of
  `(towerExtendScalarsComplexes J B C b).obj K` is `Cₓ ⊗_{Bₓ} (K.X i)ₓ`.
* `Opens.stalkTowerExtendScalarsXLinearEquiv` and
  `Opens.stalkTowerExtendScalarsXAddEquiv`: the same identification as a linear equivalence over
  the fibre of `C` and as an additive equivalence.

## Main results

* `Opens.stalkTowerExtendScalars_d` and `Opens.stalkTowerExtendScalars_d_apply`: **the degreewise
  identification is compatible with the differential**; the stalk of the differential of
  `(towerExtendScalarsComplexes J B C b).obj K` is the base change of the stalk of the
  differential of `K`.
* `Opens.stalkTowerExtendScalars_map` and `Opens.stalkTowerExtendScalars_map_apply`:
  **functoriality.**  The stalk of `(towerExtendScalarsComplexes J B C b).map φ` in degree `i` is
  `LinearMap.baseChange Cₓ` of the stalk of `φ.f i`.
* `Opens.stalkTowerExtendScalarsXAddEquiv_smul`: the degreewise identification is semilinear
  along `Opens.commRingFiberStalkHom`, which is the form in which it meets a statement made over
  the `RingCat`-valued stalk.

## Implementation notes

`Stacks.SheafOfModules.towerExtendScalarsComplexes` is
`Stacks.SheafOfModules.towerExtendScalars.mapHomologicalComplex`, whose object has
`X i = F.obj (K.X i)` and `d i j = F.map (K.d i j)`, and whose map has
`f i = F.map (φ.f i)`; and `Stacks.SheafOfModules.towerExtendScalars` on the site of opens of a
space is `Stacks.Sheaves.RingedToposModules.extendScalars` along `b.hom`, exactly as for the
adjunction in `Opens.towerExtendRestrictAdjunction_counit_app`.  So all three statements are the
naturality square of `Opens.extendScalarsStalkFunctorIso`, at `K.d i j` and at `φ.f i`
respectively, and no transport is needed.

`ModuleCat.extendScalars` sends a morphism to `LinearMap.baseChange` by definition
(`ModuleCat.ExtendScalars.map'`), which is what the `_apply` forms record; the `Algebra`
instance on the fibre of `C` over the fibre of `B` is the one attached to
`Stacks.SitePointBaseChange.stalkRingHom`, supplied by `letI` rather than declared, since a
global instance on a stalk ring makes the pre-existing actions on these stalks expensive to find.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sheaves.RingedToposModules

universe u

noncomputable section

namespace Opens

variable {X : TopCat.{u}} (x : X)
  [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (B C : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (b : B ⟶ C)
  (K : CochainComplex (SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf B)) ℤ)

/-! ### The degreewise identification -/

/-- **The stalk of the termwise base change of a complex of sheaves of modules, degreewise.**
The stalk at `x` of the degree-`i` term of `(towerExtendScalarsComplexes J B C b).obj K` is
`Cₓ ⊗_{Bₓ} (K.X i)ₓ`.

The degree-`i` term of the termwise extension of scalars is the extension of scalars of the
degree-`i` term, so this is `Opens.extendScalarsStalkFunctorIso` — the interchange of extension of
scalars with taking topological stalks — read at `K.X i`.  Both sides are modules over the fibre
of `C` at the point of the site of opens attached to `x`; see the module docstring for why that
and not the `CommRingCat`-valued stalk. -/
def stalkTowerExtendScalarsXIso (i : ℤ) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u}
            (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
            (commRingFiberStalkHom x C).hom).obj
        (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
          (Opens.grothendieckTopology X) B C b).obj K).X i) ≅
      (ModuleCat.extendScalars
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf B) x ⋙
            ModuleCat.restrictScalars.{u}
              (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
              (commRingFiberStalkHom x B).hom).obj (K.X i)) :=
  (extendScalarsStalkFunctorIso x B C b).app (K.X i)

/-- `Opens.stalkTowerExtendScalarsXIso` as a linear equivalence over the fibre of `C`. -/
def stalkTowerExtendScalarsXLinearEquiv (i : ℤ) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u}
            (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
            (commRingFiberStalkHom x C).hom).obj
        (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
          (Opens.grothendieckTopology X) B C b).obj K).X i) ≃ₗ[
        Stacks.ringFiber (pointGrothendieckTopology x) C.obj]
      (ModuleCat.extendScalars
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf B) x ⋙
            ModuleCat.restrictScalars.{u}
              (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
              (commRingFiberStalkHom x B).hom).obj (K.X i)) :=
  (stalkTowerExtendScalarsXIso x B C b K i).toLinearEquiv

/-- `Opens.stalkTowerExtendScalarsXIso` as an additive equivalence. -/
def stalkTowerExtendScalarsXAddEquiv (i : ℤ) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u}
            (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
            (commRingFiberStalkHom x C).hom).obj
        (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
          (Opens.grothendieckTopology X) B C b).obj K).X i) ≃+
      (ModuleCat.extendScalars
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf B) x ⋙
            ModuleCat.restrictScalars.{u}
              (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
              (commRingFiberStalkHom x B).hom).obj (K.X i)) :=
  (stalkTowerExtendScalarsXLinearEquiv x B C b K i).toAddEquiv

/-- `Opens.stalkTowerExtendScalarsXAddEquiv` sends an element to its image under the forward
morphism of `Opens.stalkTowerExtendScalarsXIso`. -/
theorem stalkTowerExtendScalarsXAddEquiv_apply (i : ℤ)
    (ξ : (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.commRingSheafToRingSheaf C) x ⋙
        ModuleCat.restrictScalars.{u}
          (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
          (commRingFiberStalkHom x C).hom).obj
      (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
        (Opens.grothendieckTopology X) B C b).obj K).X i)) :
    stalkTowerExtendScalarsXAddEquiv x B C b K i ξ =
      (stalkTowerExtendScalarsXIso x B C b K i).hom ξ := rfl

/-- **The degreewise identification is semilinear along `Opens.commRingFiberStalkHom`.**  A
scalar is taken in the `RingCat`-valued stalk of the sheaf of rings underlying `C` — the ring the
linear legs of the naive cotangent complex are stated over — and lands in the fibre of `C`, the
ring the tensor product on the right is taken over.  This is the restriction of scalars built into
`Opens.stalkTowerExtendScalarsXIso` read on elements. -/
theorem stalkTowerExtendScalarsXAddEquiv_smul (i : ℤ)
    (r : Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
    (ξ : (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.commRingSheafToRingSheaf C) x).obj
      (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
        (Opens.grothendieckTopology X) B C b).obj K).X i)) :
    stalkTowerExtendScalarsXAddEquiv x B C b K i
        ((commRingFiberStalkHom x C).hom r • ξ) =
      r • stalkTowerExtendScalarsXAddEquiv x B C b K i ξ :=
  (stalkTowerExtendScalarsXLinearEquiv x B C b K i).map_smul r ξ

/-! ### Compatibility with the differential -/

/-- **The degreewise identification is compatible with the differential.**  The stalk at `x` of
the differential of `(towerExtendScalarsComplexes J B C b).obj K`, read through
`Opens.stalkTowerExtendScalarsXIso` in the two degrees, is the extension of scalars along the
stalk of `b` of the stalk of the differential of `K`.

With `Opens.stalkTowerExtendScalarsXIso` this says that the stalk of the termwise base change of
`K` is the termwise base change of the stalk of `K`, as a complex and not merely degreewise. -/
theorem stalkTowerExtendScalars_d (i j : ℤ) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u}
            (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
            (commRingFiberStalkHom x C).hom).map
          (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
            (Opens.grothendieckTopology X) B C b).obj K).d i j) ≫
        (stalkTowerExtendScalarsXIso x B C b K j).hom =
      (stalkTowerExtendScalarsXIso x B C b K i).hom ≫
        (ModuleCat.extendScalars
              (Stacks.SitePointBaseChange.stalkRingHom b.hom
                (pointGrothendieckTopology x))).map
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.commRingSheafToRingSheaf B) x ⋙
              ModuleCat.restrictScalars.{u}
                (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
                (commRingFiberStalkHom x B).hom).map (K.d i j)) :=
  (extendScalarsStalkFunctorIso x B C b).hom.naturality (K.d i j)

/-- `Opens.stalkTowerExtendScalars_d` on elements, with the extension of scalars spelled out as
`LinearMap.baseChange`. -/
theorem stalkTowerExtendScalars_d_apply (i j : ℤ)
    (ξ : (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.commRingSheafToRingSheaf C) x ⋙
        ModuleCat.restrictScalars.{u}
          (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
          (commRingFiberStalkHom x C).hom).obj
      (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
        (Opens.grothendieckTopology X) B C b).obj K).X i)) :
    letI := (Stacks.SitePointBaseChange.stalkRingHom b.hom
      (pointGrothendieckTopology x)).toAlgebra
    (stalkTowerExtendScalarsXIso x B C b K j).hom
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf C) x ⋙
            ModuleCat.restrictScalars.{u}
              (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
              (commRingFiberStalkHom x C).hom).map
            (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
              (Opens.grothendieckTopology X) B C b).obj K).d i j) ξ) =
      LinearMap.baseChange (Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf B) x ⋙
            ModuleCat.restrictScalars.{u}
              (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
              (commRingFiberStalkHom x B).hom).map (K.d i j)).hom
        ((stalkTowerExtendScalarsXIso x B C b K i).hom ξ) := by
  exact ConcreteCategory.congr_hom (stalkTowerExtendScalars_d ..) ξ

/-! ### Functoriality -/

/-- **Functoriality: the stalk of the termwise base change of a chain map is the base change of
its stalk.**  In degree `i` the stalk at `x` of
`(towerExtendScalarsComplexes J B C b).map φ`, read through
`Opens.stalkTowerExtendScalarsXIso`, is the extension of scalars along the stalk of `b` of the
stalk of `φ.f i`. -/
theorem stalkTowerExtendScalars_map
    (L : CochainComplex (SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf B)) ℤ)
    (φ : K ⟶ L) (i : ℤ) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u}
            (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
            (commRingFiberStalkHom x C).hom).map
          (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
            (Opens.grothendieckTopology X) B C b).map φ).f i) ≫
        (stalkTowerExtendScalarsXIso x B C b L i).hom =
      (stalkTowerExtendScalarsXIso x B C b K i).hom ≫
        (ModuleCat.extendScalars
              (Stacks.SitePointBaseChange.stalkRingHom b.hom
                (pointGrothendieckTopology x))).map
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.commRingSheafToRingSheaf B) x ⋙
              ModuleCat.restrictScalars.{u}
                (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
                (commRingFiberStalkHom x B).hom).map (φ.f i)) :=
  (extendScalarsStalkFunctorIso x B C b).hom.naturality (φ.f i)

/-- **`Opens.stalkTowerExtendScalars_map` with the base change spelled out:** the stalk of
`(towerExtendScalarsComplexes J B C b).map φ` in degree `i` is
`LinearMap.baseChange Cₓ` of the stalk of `φ.f i`.  The `Algebra` structure of the fibre of `C`
over the fibre of `B` is the one attached to the stalk of `b`. -/
theorem stalkTowerExtendScalars_map_apply
    (L : CochainComplex (SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf B)) ℤ)
    (φ : K ⟶ L) (i : ℤ)
    (ξ : (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.commRingSheafToRingSheaf C) x ⋙
        ModuleCat.restrictScalars.{u}
          (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
          (commRingFiberStalkHom x C).hom).obj
      (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
        (Opens.grothendieckTopology X) B C b).obj K).X i)) :
    letI := (Stacks.SitePointBaseChange.stalkRingHom b.hom
      (pointGrothendieckTopology x)).toAlgebra
    (stalkTowerExtendScalarsXIso x B C b L i).hom
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf C) x ⋙
            ModuleCat.restrictScalars.{u}
              (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
              (commRingFiberStalkHom x C).hom).map
            (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
              (Opens.grothendieckTopology X) B C b).map φ).f i) ξ) =
      LinearMap.baseChange (Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf B) x ⋙
            ModuleCat.restrictScalars.{u}
              (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
              (commRingFiberStalkHom x B).hom).map (φ.f i)).hom
        ((stalkTowerExtendScalarsXIso x B C b K i).hom ξ) := by
  exact ConcreteCategory.congr_hom (stalkTowerExtendScalars_map ..) ξ

/-! ### Functoriality at a single morphism

The two statements above are about a chain map, because that is the shape in which the stalk of
the canonical map of Stacks 0E1Y consumes them.  The *null homotopy* inside that canonical map is
not a chain map: its single nonzero component is a bare morphism out of the degree `0` term, and
the extension of scalars applied to it is `Stacks.SheafOfModules.towerExtendScalars.map` of that
bare morphism.  The statements below are the same naturality square of
`Opens.extendScalarsStalkFunctorIso` read at one morphism of sheaves of `B`-modules, which is
what the homotopy needs. -/

/-- The degreewise identification of `Opens.stalkTowerExtendScalarsXIso`, read at an arbitrary
sheaf of `B`-modules rather than at a term of a complex. -/
def stalkTowerExtendScalarsObjIso (M : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf B)) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u}
            (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
            (commRingFiberStalkHom x C).hom).obj
        ((Stacks.SheafOfModules.towerExtendScalars.{u, u, u}
          (Opens.grothendieckTopology X) B C b).obj M) ≅
      (ModuleCat.extendScalars
            (Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x))).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.commRingSheafToRingSheaf B) x ⋙
            ModuleCat.restrictScalars.{u}
              (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
              (commRingFiberStalkHom x B).hom).obj M) :=
  (extendScalarsStalkFunctorIso x B C b).app M

/-- The degreewise identification of a complex is the identification of its degree-`i` term:
`Opens.stalkTowerExtendScalarsXIso` is `Opens.stalkTowerExtendScalarsObjIso` at `K.X i`. -/
theorem stalkTowerExtendScalarsXIso_eq (i : ℤ) :
    stalkTowerExtendScalarsXIso x B C b K i =
      stalkTowerExtendScalarsObjIso x B C b (K.X i) :=
  rfl

/-- **Functoriality at a single morphism: the stalk of the extension of scalars of a morphism of
sheaves of `B`-modules is the base change of its stalk.**  This is the naturality square of
`Opens.extendScalarsStalkFunctorIso` at `ψ`, and `Opens.stalkTowerExtendScalars_map` is this
statement at `ψ = φ.f i`. -/
theorem stalkTowerExtendScalarsObj_map
    (M N : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf B)) (ψ : M ⟶ N) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u}
            (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
            (commRingFiberStalkHom x C).hom).map
          ((Stacks.SheafOfModules.towerExtendScalars.{u, u, u}
            (Opens.grothendieckTopology X) B C b).map ψ) ≫
        (stalkTowerExtendScalarsObjIso x B C b N).hom =
      (stalkTowerExtendScalarsObjIso x B C b M).hom ≫
        (ModuleCat.extendScalars
              (Stacks.SitePointBaseChange.stalkRingHom b.hom
                (pointGrothendieckTopology x))).map
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.commRingSheafToRingSheaf B) x ⋙
              ModuleCat.restrictScalars.{u}
                (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
                (commRingFiberStalkHom x B).hom).map ψ) :=
  (extendScalarsStalkFunctorIso x B C b).hom.naturality ψ

open scoped ChangeOfRings in
/-- **The stalk of the extension of scalars of a morphism, on a pure tensor.**  The stalk of
`(towerExtendScalars J B C b).map ψ` carries the image under
`Opens.stalkTowerExtendScalarsObjIso` of `c ⊗ ω` to the image of `c ⊗ ψₓ ω`.

This is `Opens.stalkTowerExtendScalarsObj_map` with the identification cancelled against its
inverse on both sides; it is the shape the stalk of a null homotopy is computed in. -/
theorem stalkTowerExtendScalarsObj_map_inv_tmul
    (M N : SheafOfModules.{u} (Stacks.commRingSheafToRingSheaf B)) (ψ : M ⟶ N)
    (c : ToType (Stacks.ringFiber (pointGrothendieckTopology x) C.obj))
    (ω : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.commRingSheafToRingSheaf B) x ⋙
        ModuleCat.restrictScalars.{u}
          (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
          (commRingFiberStalkHom x B).hom).obj M)) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.commRingSheafToRingSheaf C) x ⋙
          ModuleCat.restrictScalars.{u}
            (R := Stacks.ringFiber (pointGrothendieckTopology x) C.obj)
            (commRingFiberStalkHom x C).hom).map
          ((Stacks.SheafOfModules.towerExtendScalars.{u, u, u}
            (Opens.grothendieckTopology X) B C b).map ψ)
        ((stalkTowerExtendScalarsObjIso x B C b M).inv
          (c ⊗ₜ[ToType (Stacks.ringFiber (pointGrothendieckTopology x) B.obj),
            Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x)] ω)) =
      (stalkTowerExtendScalarsObjIso x B C b N).inv
        (c ⊗ₜ[ToType (Stacks.ringFiber (pointGrothendieckTopology x) B.obj),
            Stacks.SitePointBaseChange.stalkRingHom b.hom
              (pointGrothendieckTopology x)]
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.commRingSheafToRingSheaf B) x ⋙
              ModuleCat.restrictScalars.{u}
                (R := Stacks.ringFiber (pointGrothendieckTopology x) B.obj)
                (commRingFiberStalkHom x B).hom).map ψ ω)) := by
  refine Eq.trans (Iso.hom_inv_id_apply (stalkTowerExtendScalarsObjIso x B C b N) _).symm
    (congrArg _ ?_)
  exact (ConcreteCategory.congr_hom (stalkTowerExtendScalarsObj_map x B C b M N ψ) _).trans
    (congrArg _ (Iso.inv_hom_id_apply (stalkTowerExtendScalarsObjIso x B C b M) _))

end Opens

end

end
