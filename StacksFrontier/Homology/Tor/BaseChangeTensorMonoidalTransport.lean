module

public import StacksFrontier.Homology.Tor.BaseChangeExtendScalarsLift
public import StacksFrontier.Homology.Tor.BaseChangeTensorScalarLift

/-!
# The monoidality comparison of [stacks 068I] transported across the scalar lift

`CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom`
identifies the standard tensor base-change isomorphism of total complexes with the monoidality
isomorphism `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` of degreewise extension of
scalars -- but only where the two rings and all their modules share one universe, because that is
the generality in which the monoidality isomorphism is defined.

The keystone of Chapter 47 needs the identification at *independent* ring universes.  Its
[stacks 068I] side carries the standard comparison over `f : R → A` itself, produced by
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj`; its [stacks 0E1W] side carries
`extendScalarsMonoidalIso` over the *lifted* ring map `f' : ULift R → ULift A`, where one
universe does hold everything.  Nothing in the library transported one to the other.

This file builds the transport.  It is the commuting square

`(c_K ⊗ c_L) ≫ ρ ≫ ρ_A(e) = m' ≫ (A' ⊗_{R'} ·)(ρ) ≫ c_{K ⊗ L}`

whose vertical comparisons `c` are
`CochainComplex.DerivedTensor.extendScalarsLiftChainIso`, the comparison of "lift, then extend"
with "extend, then lift"; whose `ρ`'s are
`CochainComplex.DerivedTensor.restrictScalarsTensorComplexIso`, the comparison of restriction of
scalars along a ring isomorphism with the total tensor product; and whose two horizontal maps are
the standard comparison `e` over `f` and the monoidality isomorphism `m'` over `f'`.

Everything is checked on the antidiagonal summand of a bidegree, where the four summand formulas
-- `CochainComplex.ExtendScalars.ι_extendScalarsMonoidalIso_hom`,
`CochainComplex.DerivedTensor.ι_restrictScalarsTensorComplexIso_hom` on both sides, and the
defining property of `CochainComplex.DerivedTensor.IsTensorBaseChangeIso` -- reduce the square to
its module-level counterpart
`CochainComplex.DerivedTensor.extendScalarsLiftNatIso_monoidal`.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the two
monoidality comparisons the keystone at a K-flat pair carries -- one at independent ring
universes, one over the lifted ring map -- are now related by a proved square.

## Main results

* `CochainComplex.DerivedTensor.isTensorBaseChangeIso_transport` -- **the transport**: every
  standard tensor base-change isomorphism of total complexes over `f` agrees, after the two
  scalar-lift comparisons, with the monoidality isomorphism of degreewise extension of scalars
  over the lifted ring map.
* `CochainComplex.DerivedTensor.isTensorBaseChangeIso_transport_inv` -- the same with the
  monoidality isomorphism inverted, which is the direction it occurs in in the chain-level map of
  [stacks 0E1W].
* `CochainComplex.DerivedTensor.transportedMonoidalInv` and
  `CochainComplex.DerivedTensor.extendScalarsMonoidalIso_inv_eq_transport` -- that inverse in
  closed form, the three remaining isomorphisms inverted, under a name of its own.

## Implementation notes

The summand chase is performed by three `private` lemmas stated over variable categories --
`CochainComplex.DerivedTensor.chaseMapComp`, `CochainComplex.DerivedTensor.chaseTensorComp` and
`CochainComplex.DerivedTensor.compAssocTail` -- taking the four summand formulas as data.  That
is deliberate: the two spellings `tensorComplex X Y` and `X ⊗ Y` of the total tensor product of
complexes over a ring in one universe are definitionally but not syntactically equal, so the
concrete goal is not type-correct at the transparency `rw` and `simp` work at, and every rewrite
in it fails.  An abstract lemma has no such spelling, and instantiating it with `exact` checks at
default transparency, where the two spellings do agree.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars

universe w₁ w₂ w₃ w₄ uR uA v

namespace CochainComplex.DerivedTensor

section Chase

/-- The chase on the [stacks 0E1W] side, over variable categories: a morphism out of a summand
composed with the image of a factorization, with a naturality square at the end. -/
private theorem chaseMapComp {C : Type w₁} {D : Type w₂} [Category.{w₃} C] [Category.{w₄} D]
    (E : C ⥤ D) {A₀ A₁ A₂ A₃ : C} (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (r : A₀ ⟶ A₃) (s : A₃ ⟶ A₂)
    {T P V V₂ : D} (i : T ⟶ P) (m : P ⟶ E.obj A₁) (u : T ⟶ E.obj A₀)
    (c : E.obj A₂ ⟶ V) (c₂ : E.obj A₃ ⟶ V₂) (t : V₂ ⟶ V)
    (h1 : i ≫ m = u ≫ E.map a) (h2 : a ≫ b = r ≫ s) (h3 : E.map s ≫ c = c₂ ≫ t) :
    i ≫ (m ≫ E.map b ≫ c) = u ≫ E.map r ≫ c₂ ≫ t := by
  rw [← Category.assoc, h1, Category.assoc, ← Functor.map_comp_assoc, h2, Functor.map_comp,
    Category.assoc, h3]

/-- The chase on the [stacks 068I] side, over variable categories: a morphism out of a summand
composed with a comparison and the image of a factorization. -/
private theorem chaseTensorComp {C : Type w₁} {D : Type w₂} [Category.{w₃} C] [Category.{w₄} D]
    (G : C ⥤ D) {B₀ B₁ B₂ B₃ : C} (a₁ : B₀ ⟶ B₁) (a₂ : B₁ ⟶ B₂) (d : B₀ ⟶ B₃) (a₃ : B₃ ⟶ B₂)
    {T P P' V : D} (i : T ⟶ P) (m : P ⟶ P') (j : V ⟶ P') (vv : T ⟶ V)
    (b : P' ⟶ G.obj B₁) (ww : V ⟶ G.obj B₀)
    (h1 : i ≫ m = vv ≫ j) (h2 : j ≫ b = ww ≫ G.map a₁) (h3 : a₁ ≫ a₂ = d ≫ a₃) :
    i ≫ (m ≫ b ≫ G.map a₂) = vv ≫ ww ≫ G.map d ≫ G.map a₃ := by
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc j, h2, Category.assoc,
    ← Functor.map_comp, h3, Functor.map_comp]

/-- Append a common tail to an equation between threefold composites. -/
private theorem compAssocTail {D : Type w₂} [Category.{w₄} D] {P Q₁ Q₂ Q₁' Q₂' V W : D}
    {x : P ⟶ Q₁} {y : Q₁ ⟶ Q₂} {z : Q₂ ⟶ V} {x' : P ⟶ Q₁'} {y' : Q₁' ⟶ Q₂'} {z' : Q₂' ⟶ V}
    (hxyz : x ≫ y ≫ z = x' ≫ y' ≫ z') (τ : V ⟶ W) :
    x ≫ y ≫ z ≫ τ = x' ≫ y' ≫ z' ≫ τ := by
  have key : (x ≫ y ≫ z) ≫ τ = (x' ≫ y' ≫ z') ≫ τ := congrArg (· ≫ τ) hxyz
  simpa only [Category.assoc] using key

/-- Solve for the first factor of a composite whose remaining three factors are invertible. -/
private theorem eqCompInvOfCompEq {D : Type w₂} [Category.{w₄} D] {X Y Z₁ Z₂ Z₃ : D}
    (g : X ⟶ Y) (α : Y ≅ Z₁) (β : Z₁ ≅ Z₂) (γ : Z₂ ≅ Z₃) (δ : X ⟶ Z₃)
    (hg : g ≫ α.hom ≫ β.hom ≫ γ.hom = δ) :
    g = δ ≫ γ.inv ≫ β.inv ≫ α.inv := by
  rw [← hg]
  simp

/-- Replace the head of a composite. -/
private theorem compCongrHead {D : Type w₂} [Category.{w₄} D] {P Q V : D} {x x' : P ⟶ Q}
    (hx : x = x') (y : Q ⟶ V) : x ≫ y = x' ≫ y := congrArg (· ≫ y) hx

end Chase

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The transport of the monoidality comparison across the scalar lift.**

Every standard tensor base-change isomorphism `e` of total complexes over `f` -- in particular
the one `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` supplies for the [stacks 068I] candidate at
a K-flat pair -- fits into a commuting square with
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` over the lifted ring map, at the pair of
scalar lifts.  The vertical comparisons are
`CochainComplex.DerivedTensor.extendScalarsLiftChainIso` and
`CochainComplex.DerivedTensor.restrictScalarsTensorComplexIso`.

This is the identification the keystone of Chapter 47 needs: `e` is what the [stacks 068I] side
of the keystone carries, at independent ring universes; the monoidality isomorphism over the
lifted ring map is what the [stacks 0E1W] side carries, and
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom`, which
would relate them directly, is available only in a single universe. -/
public theorem isTensorBaseChangeIso_transport
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    {e : tensorComplex.{uA, max uR v}
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, v} f).obj (tensorComplex.{uR, max uA v} K L)}
    (he : IsTensorBaseChangeIso.{uR, uA, v} f K L e) :
    ((extendScalarsLiftChainIso.{uR, uA, v} f K).hom ⊗ₘ
          (extendScalarsLiftChainIso.{uR, uA, v} f L).hom) ≫
        (restrictScalarsTensorComplexIso
            (ULift.ringEquiv : ULift.{max uR uA v} A ≃+* A)
            ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
            ((extensionOfScalarsCochain.{uR, uA, v} f).obj L)).hom ≫
          ((scalarLiftFunctor.{uA, max uR v} A).mapHomologicalComplex
            (ComplexShape.up ℤ)).map e.hom =
      (extendScalarsMonoidalIso (liftRingHom.{uR, uA, v} f)
            (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)
            (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L)).hom ≫
        (mapCochainComplex (liftRingHom.{uR, uA, v} f)).map
            (restrictScalarsTensorComplexIso
              (ULift.ringEquiv : ULift.{max uR uA v} R ≃+* R) K L).hom ≫
          (extendScalarsLiftChainIso.{uR, uA, v} f (tensorComplex.{uR, max uA v} K L)).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have h1 := HomologicalComplex.ι_mapBifunctorMap
    (extendScalarsLiftChainIso.{uR, uA, v} f K).hom
    (extendScalarsLiftChainIso.{uR, uA, v} f L).hom
    (curriedTensor (ModuleCat.{max uR uA v} (ULift.{max uR uA v} A)))
    (ComplexShape.up ℤ) p q n h
  have h1' := h1.trans (Category.assoc _ _ _).symm
  have h2 := ι_restrictScalarsTensorComplexIso_hom
    (ULift.ringEquiv : ULift.{max uR uA v} A ≃+* A)
    ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
    ((extensionOfScalarsCochain.{uR, uA, v} f).obj L) p q n h
  have hL := chaseTensorComp (scalarLiftFunctor.{uA, max uR v} A) _ _ _ _ _ _ _ _ _ _
    h1' h2 (he p q n h)
  have k1 := ι_extendScalarsMonoidalIso_hom (liftRingHom.{uR, uA, v} f)
    (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    n p q h
  have k2 := ι_restrictScalarsTensorComplexIso_hom
    (ULift.ringEquiv : ULift.{max uR uA v} R ≃+* R) K L p q n h
  have k3 := (extendScalarsLiftNatIso.{uR, uA, v} f).hom.naturality
    (HomologicalComplex.ιMapBifunctor K L (moduleTensor.{uR, max uA v} R)
      (ComplexShape.up ℤ) p q n h)
  have hR := chaseMapComp
    (ModuleCat.extendScalars.{max uR uA v, max uR uA v, max uR uA v}
      (liftRingHom.{uR, uA, v} f)) _ _ _ _ _ _ _ _ _ _ k1 k2 k3
  have hM := compAssocTail (extendScalarsLiftNatIso_monoidal.{uR, uA, v} f (K.X p) (L.X q))
    ((scalarLiftFunctor.{uA, max uR v} A).map
      ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).map
        (HomologicalComplex.ιMapBifunctor K L (moduleTensor.{uR, max uA v} R)
          (ComplexShape.up ℤ) p q n h)))
  have hbridge : (((curriedTensor (ModuleCat.{max uR uA v} (ULift.{max uR uA v} A))).map
            ((extendScalarsLiftNatIso.{uR, uA, v} f).hom.app (K.X p))).app
          ((((ModuleCat.extendScalars.{max uR uA v, max uR uA v, max uR uA v}
            (liftRingHom.{uR, uA, v} f)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L)).X q) ≫
        ((curriedTensor (ModuleCat.{max uR uA v} (ULift.{max uR uA v} A))).obj
              ((((scalarLiftFunctor.{uA, max uR v} A).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
                ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)).X p)).map
          ((extendScalarsLiftNatIso.{uR, uA, v} f).hom.app (L.X q))) =
      ((extendScalarsLiftNatIso.{uR, uA, v} f).hom.app (K.X p) ⊗ₘ
        (extendScalarsLiftNatIso.{uR, uA, v} f).hom.app (L.X q)) :=
    (MonoidalCategory.tensorHom_def _ _).symm
  exact (hL.trans (compCongrHead hbridge _)).trans (hM.symm.trans hR.symm)

/-- **The transport with the monoidality isomorphism inverted.**

`CochainComplex.DerivedTensor.isTensorBaseChangeIso_transport` with the monoidality isomorphism
moved across the equation.  That is the direction in which it occurs in the closed form
`Stacks.DerivedHom.BaseChangeIso.uncurry_homComplexChangeOfRingsMap` of the chain-level map of
[stacks 0E1W], and hence in the keystone. -/
public theorem isTensorBaseChangeIso_transport_inv
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    {e : tensorComplex.{uA, max uR v}
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, v} f).obj (tensorComplex.{uR, max uA v} K L)}
    (he : IsTensorBaseChangeIso.{uR, uA, v} f K L e) :
    (extendScalarsMonoidalIso (liftRingHom.{uR, uA, v} f)
            (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)
            (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj L)).inv ≫
        ((extendScalarsLiftChainIso.{uR, uA, v} f K).hom ⊗ₘ
            (extendScalarsLiftChainIso.{uR, uA, v} f L).hom) ≫
          (restrictScalarsTensorComplexIso
              (ULift.ringEquiv : ULift.{max uR uA v} A ≃+* A)
              ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
              ((extensionOfScalarsCochain.{uR, uA, v} f).obj L)).hom ≫
            ((scalarLiftFunctor.{uA, max uR v} A).mapHomologicalComplex
              (ComplexShape.up ℤ)).map e.hom =
      (mapCochainComplex (liftRingHom.{uR, uA, v} f)).map
          (restrictScalarsTensorComplexIso
            (ULift.ringEquiv : ULift.{max uR uA v} R ≃+* R) K L).hom ≫
        (extendScalarsLiftChainIso.{uR, uA, v} f (tensorComplex.{uR, max uA v} K L)).hom := by
  rw [isTensorBaseChangeIso_transport.{uR, uA, v} f K L he]
  exact Iso.inv_hom_id_assoc _ _

/-- **The transported inverse of the monoidality isomorphism.**  The closed form of
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` over the lifted ring map, inverted: the
extension of the comparison of restriction of scalars with the total tensor product, the
scalar-lift comparison at the total tensor complex, and the three remaining comparisons inverted.

It is given a name of its own so that a consumer composing it with a chain map does not have to
unify the five nested comparisons; the declared signature makes that unification immediate. -/
public def transportedMonoidalInv (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (e : tensorComplex.{uA, max uR v}
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, v} f).obj (tensorComplex.{uR, max uA v} K L)) :
    (mapCochainComplex (liftRingHom.{uR, uA, v} f)).obj
        ((((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ⊗
          (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L)) ⟶
      (mapCochainComplex (liftRingHom.{uR, uA, v} f)).obj
          (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ⊗
        (mapCochainComplex (liftRingHom.{uR, uA, v} f)).obj
          (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) :=
  ((mapCochainComplex (liftRingHom.{uR, uA, v} f)).map
        (restrictScalarsTensorComplexIso
          (ULift.ringEquiv : ULift.{max uR uA v} R ≃+* R) K L).hom ≫
      (extendScalarsLiftChainIso.{uR, uA, v} f (tensorComplex.{uR, max uA v} K L)).hom) ≫
    (((scalarLiftFunctor.{uA, max uR v} A).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso e).inv ≫
      (restrictScalarsTensorComplexIso
          (ULift.ringEquiv : ULift.{max uR uA v} A ≃+* A)
          ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
          ((extensionOfScalarsCochain.{uR, uA, v} f).obj L)).inv ≫
        (MonoidalCategory.tensorIso (extendScalarsLiftChainIso.{uR, uA, v} f K)
          (extendScalarsLiftChainIso.{uR, uA, v} f L)).inv

/-- **The inverse of the monoidality isomorphism over the lifted ring map, in closed form.**

`CochainComplex.DerivedTensor.isTensorBaseChangeIso_transport_inv` with the three remaining
isomorphisms of the equation inverted, so that the inverse of
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` over the lifted ring map is expressed
entirely in the scalar-lift comparisons and the standard tensor base-change isomorphism of total
complexes over `f`.

That inverse is the factor the keystone of Chapter 47 carries: by
`Dualizing.tensorBaseChangeMor_eq_of_monoidal_chain_level` the [stacks 0GMT] side of the keystone
at a K-flat pair is the degreewise unit of extension of scalars followed by the restriction of
this inverse composed with the uncurried transpose of the prefix. -/
public theorem extendScalarsMonoidalIso_inv_eq_transport
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    {e : tensorComplex.{uA, max uR v}
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, v} f).obj (tensorComplex.{uR, max uA v} K L)}
    (he : IsTensorBaseChangeIso.{uR, uA, v} f K L e) :
    (extendScalarsMonoidalIso (liftRingHom.{uR, uA, v} f)
          (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
          (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L)).inv =
      transportedMonoidalInv.{uR, uA, v} f K L e :=
  eqCompInvOfCompEq _
    (MonoidalCategory.tensorIso (extendScalarsLiftChainIso.{uR, uA, v} f K)
      (extendScalarsLiftChainIso.{uR, uA, v} f L))
    (restrictScalarsTensorComplexIso
      (ULift.ringEquiv : ULift.{max uR uA v} A ≃+* A)
      ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
      ((extensionOfScalarsCochain.{uR, uA, v} f).obj L))
    (((scalarLiftFunctor.{uA, max uR v} A).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso e) _
    (isTensorBaseChangeIso_transport_inv.{uR, uA, v} f K L he)

end CochainComplex.DerivedTensor

end
