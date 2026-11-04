module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.Pi
public import StacksFrontier.Deformation.Examples.Geometric.Localization
public import StacksFrontier.Deformation.Examples.Geometric.RingDeformationFiberIso
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceInjection

/-!
# Deformations of a finite product of algebras

The chain of **Stacks 0DZF** has for its terms the *products of the deformation categories*
`∏ 𝓓_{R i}` of a finite family of `k`-algebras, while the results the proof transports along
the decompositions `P^∧ = ∏ P^∧_{𝔪 i}` and `P^h = ∏ P^h_{𝔪 i}` land in the deformation
category `𝓓_{∏ R i}` of the *product ring*. The source identifies the two without comment.

This file builds the comparison functor `∏ 𝓓_{R i} ⟶ 𝓓_{∏ R i}` in that direction: a family of
deformations `Q i` of `R i` over one common Artinian base `A` has for its product `∏ Q i` a flat
`A`-algebra whose special fibre is `∏ R i`, because a finite product of flat modules is flat and
tensoring commutes with finite products.

## Main definitions

* `Deformation.Examples.flatAlgebraPi`: the product of a finite family of flat algebras over a
  common Artinian base.
* `Deformation.Examples.piDeformation`: the product of a family of deformations over a common
  base, as a deformation of `∏ R i`.
* `Deformation.Examples.piDeformationFunctor`: the based functor
  `∏ 𝓓_{R i} ⟶ 𝓓_{∏ R i}` over `𝒞_Λ`.

## Main results

* `Deformation.Examples.isPushout_pi`: a finite product of pushout squares of commutative rings
  with a common left-hand vertical side is a pushout square.

## Implementation notes

The index type is required to live in the universe `w` of the algebras, because `∀ i, R i` must
again be a `k`-algebra in `Type w` for `Deformation.Examples.ringDeformationBasedCategory` to
accept it. Reindexing an arbitrary finite family into that universe is
`Deformation.piReindex`.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 0DY1](https://stacks.math.columbia.edu/tag/0DY1)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace Deformation.Examples

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Products of pushout squares of rings -/

/-- **A finite product of pushout squares of commutative rings sharing their left-hand vertical
side is a pushout square.** Base change along `A → B` commutes with finite products of
`A`-algebras, which is `IsBaseChange.pi`. -/
public theorem isPushout_pi
    {ι : Type w} [Finite ι] {A B : Type w} [CommRing A] [CommRing B]
    {X Y : ι → Type w} [∀ i, CommRing (X i)] [∀ i, CommRing (Y i)]
    (f : A →+* B) (p : ∀ i, A →+* X i) (q : ∀ i, X i →+* Y i)
    (r : ∀ i, B →+* Y i)
    (h : ∀ i, IsPushout (CommRingCat.ofHom (p i)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (q i)) (CommRingCat.ofHom (r i))) :
    IsPushout (CommRingCat.ofHom (RingHom.pi p)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (RingHom.pi fun i => (q i).comp (Pi.evalRingHom X i)))
      (CommRingCat.ofHom (RingHom.pi r)) := by
  let : Algebra A B := f.toAlgebra
  let (i : ι) : Algebra A (X i) := (p i).toAlgebra
  let (i : ι) : Algebra B (Y i) := (r i).toAlgebra
  let (i : ι) : Algebra A (Y i) := ((r i).comp f).toAlgebra
  let (i : ι) : Algebra (X i) (Y i) := (q i).toAlgebra
  let (i : ι) : IsScalarTower A B (Y i) := .of_algebraMap_eq' rfl
  let (i : ι) : IsScalarTower A (X i) (Y i) :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (h i).w).symm
  let : IsScalarTower A (∀ i, X i) (∀ i, Y i) :=
    .of_algebraMap_eq' (by
      ext a i
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (h i).w).symm a)
  let : IsScalarTower A B (∀ i, Y i) := .of_algebraMap_eq' (by ext a i; rfl)
  have key : Algebra.IsPushout A (∀ i, X i) B (∀ i, Y i) :=
    (Algebra.IsPushout.symm
      ⟨IsBaseChange.pi (fun i => (IsScalarTower.toAlgHom A (X i) (Y i)).toLinearMap)
        fun i => (Algebra.IsPushout.symm (CommRingCat.isPushout_iff_isPushout.mp (h i))).out⟩)
  exact CommRingCat.isPushout_iff_isPushout.mpr key

/-! ### The product of a family of flat algebras over one base -/

/-- **The product of a finite family of flat algebras over a common Artinian base.** Flatness of
the product is flatness of a finite direct sum of flat modules. -/
public noncomputable def flatAlgebraPi
    {ι : Type w} [Finite ι]
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (X : ι → FlatAlgebraCategory.{u, w} Λ k) (h : ∀ i, (X i).base = A) :
    FlatAlgebraCategory.{u, w} Λ k := by
  classical
  letI := Fintype.ofFinite ι
  let Y i := flatAlgebraWithBase A (X i) (h i)
  letI (i : ι) : Algebra A (Y i).fiber := (Y i).algebra
  letI (i : ι) : Module.Flat A (Y i).fiber := (Y i).flat
  exact
    { base := A
      fiber := ∀ i, (Y i).fiber
      flat := Module.Flat.of_linearEquiv
        (DFinsupp.linearEquivFunOnFintype (R := A)).symm }

/-! ### The product of a family of deformations -/

/-- **The product of a family of deformations of the `R i` over a common Artinian base**, as a
deformation of `∀ i, R i`. Its flat algebra is the product of the flat algebras and its
reduction is the product of the reductions; the pushout condition is
`Deformation.Examples.isPushout_pi`. -/
public noncomputable def piDeformation
    {ι : Type w} [Finite ι]
    (R : ι → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (X : ∀ i, (ringDeformationBasedCategory Λ k (R i)).p.Fiber A) :
    ringDeformationCategory (Λ := Λ) (k := k) (∀ i, R i) := by
  classical
  let Q := flatAlgebraPi A (fun i => (X i).val.left) (fun i => (X i).property)
  let f := residueFieldBaseMap A (∀ i, R i)
  let p (i : ι) : A →+* (X i).val.left.fiber :=
    @algebraMap A (X i).val.left.fiber _ _
      (flatAlgebraWithBase A (X i).val.left (X i).property).algebra
  refine Over.mk (Y := Q)
    { base := f
      map := CommRingCat.ofHom (RingHom.pi fun i => (X i).val.hom.map.hom.comp
        (Pi.evalRingHom (fun i => (X i).val.left.fiber) i))
      cartesian := ?_ }
  exact isPushout_pi f.hom.toRingHom p (fun i => (X i).val.hom.map.hom)
    (fun i => algebraMap k (R i))
    (fun i => specialFiber_pushout_with_base A (X i).val (X i).property f)

/-- **The product of a family of morphisms of deformations.** -/
public noncomputable def piDeformationMap
    {ι : Type w} [Finite ι]
    (R : ι → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    {X Y : PiOver (fun i => (ringDeformationBasedCategory Λ k (R i)).p)}
    (f : X ⟶ Y) :
    piDeformation R X.base (fun i => ⟨X.x i, X.hx i⟩) ⟶
      piDeformation R Y.base (fun i => ⟨Y.x i, Y.hx i⟩) := by
  let g := RingHom.pi (fun i => (f.component i).left.map.hom.comp
    (Pi.evalRingHom (fun i => (X.x i).left.fiber) i))
  let h : (piDeformation R X.base (fun i => ⟨X.x i, X.hx i⟩)).left ⟶
      (piDeformation R Y.base (fun i => ⟨Y.x i, Y.hx i⟩)).left :=
    { base := f.hbase
      map := CommRingCat.ofHom g
      cartesian := by
        apply isPushout_pi f.hbase.hom.toRingHom
          (fun i => @algebraMap X.base (X.x i).left.fiber _ _
            (flatAlgebraWithBase X.base (X.x i).left (X.hx i)).algebra)
          (fun i => (f.component i).left.map.hom)
          (fun i => @algebraMap Y.base (Y.x i).left.fiber _ _
            (flatAlgebraWithBase Y.base (Y.x i).left (Y.hx i)).algebra)
        intro i
        apply flatAlgebraHom_cartesian_with_base (X.hx i) (Y.hx i)
        let := f.hcomponent i
        exact IsHomLift.fac' (ringDeformationBasedCategory Λ k (R i)).p
          f.hbase (f.component i) }
  refine Over.homMk h ?_
  apply FlatAlgebraCategory.Hom.ext
  · exact deformationBaseMap_unique _ _
  · ext z
    funext i
    exact deformationMorphism_map_comm (f.component i) (z i)

/-- **The comparison functor from the product of the deformation categories to the deformation
category of the product ring**, over `𝒞_Λ`. -/
public noncomputable def piDeformationFunctor
    {ι : Type w} [Finite ι]
    (R : ι → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)] :
    BasedFunctor (piBasedCategory fun i => ringDeformationBasedCategory Λ k (R i))
      (ringDeformationBasedCategory Λ k (∀ i, R i)) where
  toFunctor :=
    { obj X := piDeformation R X.base (fun i => ⟨X.x i, X.hx i⟩)
      map f := piDeformationMap R f
      map_id X := by
        apply Over.OverMorphism.ext
        apply FlatAlgebraCategory.Hom.ext
        · rfl
        · ext z
          rfl
      map_comp f g := by
        apply Over.OverMorphism.ext
        apply FlatAlgebraCategory.Hom.ext
        · rfl
        · ext z
          rfl }
  w := rfl

end Deformation.Examples
