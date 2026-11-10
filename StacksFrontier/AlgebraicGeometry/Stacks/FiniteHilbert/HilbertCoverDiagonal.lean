module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.AbsoluteOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverVertHom
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheafFiberIso

/-!
# The diagonal of the category of degree-`d` covers is representable by algebraic spaces

Let `S` be a scheme contained in a big fppf site and let `d` be a natural number. The category
`ℋ_d` of degree-`d` finite locally free covers (`AlgebraicGeometry.Stack.finiteCoverCategory`) is
fibred in groupoids over the big fppf site of `S`, and this file proves that its diagonal is
representable by algebraic spaces.

By criterion (2) of Stacks 045G it suffices that every isomorphism sheaf of a fibre of `ℋ_d` is an
algebraic space over the scheme the fibre sits over. For two degree-`d` covers `Z₁ ⟶ U` and
`Z₂ ⟶ U` the isomorphism sheaf of Stacks 02ZB is `Isom_U(Z₁, Z₂)`, which is the presheaf of
morphisms into an object of the site over `U`.

## Main results

* `AlgebraicGeometry.Stack.exists_siteObject_isomPresheafIso`: the isomorphism sheaf of a fibre
  of `ℋ_d` is the presheaf of morphisms into an object of the site over the base.
* `AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_finiteCoverFibered`: criterion (2) of
  Stacks 045G for `ℋ_d`.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_finiteCoverFibered`: the diagonal of `ℋ_d`
  is representable by algebraic spaces.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 02ZB](https://stacks.math.columbia.edu/tag/02ZB)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe u

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] finiteCoverPointObj finiteCoverProjection
  CategoryTheory.Functor.Fiber

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}

/-- The structure morphism of an object of the fibre of `ℋ_d` over `U`, read as a morphism to
`U`. -/
abbrev fiberCoverHom {U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) :
    x.1.Z ⟶ U :=
  x.1.q ≫ eqToHom x.2

/-- The structure morphism of an object of the fibre of `ℋ_d` over `U` is finite locally free of
degree `d`. -/
theorem isFiniteLocallyFreeOfRank_fiberCoverHom {U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map (fiberCoverHom x)) d := by
  obtain ⟨P, hP⟩ := x
  subst hP
  simpa using P.finiteLocallyFree

/-- **The base change of an object of a fibre of `ℋ_d` along an object of the slice maps to that
object.** Its base component is the structure morphism of the slice object and its cover
component is the first projection of the fibre product. -/
def fiberPointHom {U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) (A : Over U) :
    finiteCoverPointObj (fiberCoverHom x) (isFiniteLocallyFreeOfRank_fiberCoverHom x) A ⟶
      x.1 where
  f := A.hom ≫ eqToHom x.2.symm
  g := pullback.fst (fiberCoverHom x) A.hom
  square :=
    (IsPullback.of_hasPullback (fiberCoverHom x) A.hom).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (eqToIso x.2.symm)
      (by simp) (by exact (Category.id_comp _).symm) (by simp) (by simp)

/-- The base component of `fiberPointHom x A` is the structure morphism of `A`. -/
@[simp]
theorem fiberPointHom_f {U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) (A : Over U) :
    (fiberPointHom x A).f = A.hom ≫ eqToHom x.2.symm :=
  rfl

/-- The cover component of `fiberPointHom x A` is the first projection of the fibre product. -/
@[simp]
theorem fiberPointHom_g {U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) (A : Over U) :
    (fiberPointHom x A).g = pullback.fst (fiberCoverHom x) A.hom :=
  rfl

/-- The underlying morphism of `ℋ_d` of the comparison between the value of the base-change
1-morphism at the terminal object and the given object of the fibre: its base component is the
structure morphism of the terminal object and its cover component is the first projection of
the fibre product. This is `AlgebraicGeometry.Stack.fiberPointHom` at the terminal object of the
slice. -/
abbrev fiberSliceValueHom {U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) :
    finiteCoverPointObj (fiberCoverHom x) (isFiniteLocallyFreeOfRank_fiberCoverHom x)
        ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left))) ⟶ x.1 :=
  fiberPointHom x ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left)))

/-- `fiberSliceValueHom x` lies over the identity of `U`. -/
theorem isHomLift_fiberSliceValueHom {U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift (𝟙 U)
      (fiberSliceValueHom x) := by
  have hA : ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left))).hom =
      eqToHom (Functor.overMap_obj_mkId U) := by
    refine Over.OverMorphism.ext ?_
    change 𝟙 U.left = _
    simp
  refine CategoryTheory.IsHomLift.of_fac' _ (𝟙 U) (fiberSliceValueHom x)
    (Functor.overMap_obj_mkId U) x.2 ?_
  change ((Over.iteratedSliceBackward U).obj (Over.mk (𝟙 U.left))).hom ≫ eqToHom x.2.symm =
    eqToHom (Functor.overMap_obj_mkId U) ≫ 𝟙 U ≫ eqToHom x.2.symm
  rw [Category.id_comp]
  exact congrArg (fun k => k ≫ eqToHom x.2.symm) hA

/-- **The value of the base-change 1-morphism at the terminal object is the given cover.** The
base change of the structure morphism of an object `x` of the fibre of `ℋ_d` over `U` along the
terminal object of the slice at `U.left` is isomorphic to `x` in that fibre. -/
def fiberSliceValueIso {U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) :
    Functor.sliceValue (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) U
        (Over.iteratedSliceBackward U ⋙ finiteCoverPointFunctor (fiberCoverHom x)
          (isFiniteLocallyFreeOfRank_fiberCoverHom x))
        (finiteCoverPointFunctor_backward_comp (fiberCoverHom x)
          (isFiniteLocallyFreeOfRank_fiberCoverHom x)) ≅ x :=
  haveI : IsGroupoid ((finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) :=
    (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS)
      (d := d)).fiber_isGroupoid U
  haveI := isHomLift_fiberSliceValueHom x
  asIso (⟨fiberSliceValueHom x, isHomLift_fiberSliceValueHom x⟩ :
    Functor.sliceValue (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) U
        (Over.iteratedSliceBackward U ⋙ finiteCoverPointFunctor (fiberCoverHom x)
          (isFiniteLocallyFreeOfRank_fiberCoverHom x))
        (finiteCoverPointFunctor_backward_comp (fiberCoverHom x)
          (isFiniteLocallyFreeOfRank_fiberCoverHom x)) ⟶ x)

/-- **The isomorphism sheaf of a fibre of `ℋ_d` is represented by an object of the site.** For
two objects of the fibre of `ℋ_d` over `U`, the isomorphism presheaf of **Stacks 02ZB**, read on
the slice of the site at the scheme underlying `U`, is the presheaf of morphisms into the object
of the site representing `Isom_U(Z₁, Z₂)`. -/
theorem exists_siteObject_isomPresheafIso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (d : ℕ) (U : BigFppfOver B S hS) :
    letI : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsFibered :=
      (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS)
        (d := d)).isFibered
    ∀ x y : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U,
      ∃ I : BigFppfOver B U.left.1 U.left.2,
        Nonempty ((Over.iteratedSliceBackward U).op ⋙
          (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).isomPresheaf x y ≅
            yoneda.obj I) := by
  intro x y
  have : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsFibered :=
    (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS)
      (d := d)).isFibered
  obtain ⟨I, ⟨iso⟩⟩ := exists_siteObject_vertHomPresheafIso (fiberCoverHom x) (fiberCoverHom y)
    (isFiniteLocallyFreeOfRank_fiberCoverHom x) (isFiniteLocallyFreeOfRank_fiberCoverHom y)
  refine ⟨I, ⟨?_⟩⟩
  have pointIso := Functor.vertHomPresheafIsoIsomPresheafOfPoint
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
    isFiberedInGroupoids_finiteCoverProjection U
    (pairFunctor
      (finiteCoverPointFunctor_backward_comp (fiberCoverHom x)
        (isFiniteLocallyFreeOfRank_fiberCoverHom x))
      (finiteCoverPointFunctor_backward_comp (fiberCoverHom y)
        (isFiniteLocallyFreeOfRank_fiberCoverHom y)))
    (pairFunctor_comp _ _)
  have fibIso := Functor.backwardIsomPresheafIsoOfIso
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
    isFiberedInGroupoids_finiteCoverProjection U
    (fiberSliceValueIso x) (fiberSliceValueIso y)
  exact (pointIso.trans fibIso).symm.trans iso

/-- **Criterion (2) of Stacks 045G holds for the category of degree-`d` finite locally free
covers.** Every isomorphism sheaf of a fibre of `ℋ_d` is an algebraic space over the scheme the
fibre sits over, namely the one represented by the object of the site representing
`Isom_U(Z₁, Z₂)`. -/
theorem isAlgebraicSpaceIsomPresheaf_finiteCoverFibered (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (d : ℕ) :
    IsAlgebraicSpaceIsomPresheaf B S hS (finiteCoverFibered B S hS d) := by
  dsimp only [IsAlgebraicSpaceIsomPresheaf]
  intro U x y
  obtain ⟨I, ⟨total⟩⟩ := exists_siteObject_isomPresheafIso B S hS d U x y
  exact ⟨yoneda.obj I, isAlgebraicSpace_yoneda B U.left.1 U.left.2 I,
    ⟨Functor.isoWhiskerRight total.symm uliftFunctor.{u, u}⟩⟩

/-- **The diagonal of the category of degree-`d` finite locally free covers is representable by
algebraic spaces.** -/
theorem hasRepresentableDiagonal_finiteCoverFibered (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (d : ℕ) :
    HasRepresentableDiagonal B S hS (finiteCoverFibered B S hS d) :=
  (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
      (finiteCoverFibered B S hS d)).mpr
    (isAlgebraicSpaceIsomPresheaf_finiteCoverFibered B S hS d)

end AlgebraicGeometry.Stack

end
