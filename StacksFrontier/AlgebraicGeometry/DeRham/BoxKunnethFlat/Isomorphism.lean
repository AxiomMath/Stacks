module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.Relative
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.GlobalCupProductAffine
import StacksCore.Tactic.StacksAttribute

/-!
# The cup product of a box product is an isomorphism

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and let `𝓕^•`, `𝓖^•` be complexes of
quasi-coherent modules with differentials differential operators of finite order on `X/S` and on
`Y/S`. [Stacks, Tag 0FLT] says that the cup product of [Stacks, Tag 0FLR]

`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`

is an isomorphism in `D(A)` when `S = Spec A` is affine, `X` and `Y` are quasi-compact with affine
diagonal, `𝓕^•` is bounded, `𝓖^•` is bounded below and all terms are flat over `S`.

## Main results

* `Stacks.Cohomology.BoxKunnethFlat.isIso_globalBoxCupProduct_of_isFlatOver`: [Stacks, Tag 0FLT].

## Implementation notes

The cup product is `Stacks.Cohomology.BoxKunneth.globalBoxCupProduct`, the map of
[Stacks, Tag 0FLR] built from the canonical global cup product, with no auxiliary bounds. By
`Stacks.Cohomology.BoxKunnethFlat.globalBoxCupProduct_eq_relative` it is the Leray isomorphisms,
the global cup product on `S` at `Ra_*𝓕^•` and `Rb_*𝓖^•`, and derived global sections over `S` of
the relative map `Stacks.Cohomology.BoxKunnethFlat.relativeBoxMap`. The global cup product is
invertible over the affine `S` because both direct images have quasi-coherent cohomology
(`Stacks.Cohomology.BoxKunnethFlat.isQuasicoherent_homology_leftComplex`,
`Stacks.Cohomology.BoxKunnethFlat.isQuasicoherent_homology_rightComplex_of_isStrictlyGE`, by
[Stacks, Tag 0FML] (2)), and the relative map is invertible by
`Stacks.Cohomology.BoxKunnethFlat.isIso_relativeBoxMap_of_isStrictlyGE`, which is the dévissage
and truncation argument of the source down to [Stacks, Tag 0FU4].

## References

* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth
open Stacks.DeRhamDirectImage
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open Stacks.Cohomology.BoxKunneth
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.BoxKunnethFlat

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- A composite of five arrows, of which the first two, the composite of the middle two, and the
last are isomorphisms, is an isomorphism. -/
private theorem isIso_comp_five {E : Type*} [Category E] {v w x y z t : E} (A : v ⟶ w)
    (B : w ⟶ x) (C : x ⟶ y) (D : y ⟶ z) (F : z ⟶ t) (hA : IsIso A) (hB : IsIso B)
    (hCD : IsIso (C ≫ D)) (hF : IsIso F) : IsIso (A ≫ B ≫ C ≫ D ≫ F) := by
  rw [← Category.assoc C]
  infer_instance

/-- Derived global sections over `S` of the two factors of the relative map. -/
theorem isIso_baseSections_relativeBoxMap
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (h : IsIso (relativeBoxMap a b K L)) :
    IsIso ((baseSections S.toRingedSpace).map
          (Stacks.Cohomology.DerivedKunneth.kunnethMap (inverseImageBaseProjection a)
            (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
            (inverseImageBaseProjection (pullback.fst a b ≫ a))
            (fstProjection_comp a b) (sndProjection_comp a b)
            (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L))) ≫
        (baseSections S.toRingedSpace).map
          ((derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
            (boxTotalComplexDerivedComparison a b K L))) := by
  have h' := Functor.map_isIso (baseSections S.toRingedSpace) (relativeBoxMap a b K L)
  rw [relativeBoxMap, CategoryTheory.Functor.map_comp] at h'
  exact h'

/-- The tensor product over `A` of the inverses of the two Leray isomorphisms. -/
theorem isIso_tensorBase_lerayIso_inv
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    IsIso ((Functor.uncurry.obj (tensorBase S.toRingedSpace)).map
          ((lerayIso (inverseImageBaseProjection a)).inv.app
              (DerivedCategory.Q.obj (leftComplex a K)) ×ₘ
            (lerayIso (inverseImageBaseProjection b)).inv.app
              (DerivedCategory.Q.obj (rightComplex b L)))) := by
  have : IsIso ((lerayIso (inverseImageBaseProjection a)).inv.app
      (DerivedCategory.Q.obj (leftComplex a K)) ×ₘ
    (lerayIso (inverseImageBaseProjection b)).inv.app
      (DerivedCategory.Q.obj (rightComplex b L))) :=
    (isIso_prod_iff (C := DerivedCategory (ModuleCat.{u} (baseRing S.toRingedSpace)))
      (D := DerivedCategory (ModuleCat.{u} (baseRing S.toRingedSpace)))).2
      ⟨inferInstance, inferInstance⟩
  infer_instance

/-- **Stacks Project, Tag 0FLT.** Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and
let `𝓕^•` and `𝓖^•` be complexes of quasi-coherent `𝒪_X`-, respectively `𝒪_Y`-modules whose
differentials are differential operators of finite order on `X/S` and on `Y/S`. The cup product
`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))` of [Stacks, Tag 0FLR] is an
isomorphism in `D(A)` if

1. `S = Spec(A)` is affine,
2. `X` and `Y` are quasi-compact with affine diagonal,
3. `𝓕^•` is bounded,
4. `𝓖^•` is bounded below,
5. every `𝓕^n` is `S`-flat, and
6. every `𝓖^m` is `S`-flat.

Here the cup product is `Stacks.Cohomology.BoxKunneth.globalBoxCupProduct`, built from the
canonical global cup product, with `A` the ring of global sections of `S`. -/
@[stacks 0FLT "the whole statement under exactly the source's hypotheses: S affine; X, Y \
quasi-compact with affine diagonal; F^• bounded (terms vanish outside some [m₁, m₂]); G^• bounded \
below (terms vanish below some n); every term of F^• and of G^• flat over S. The cup product is \
the parameter-free map of Tag 0FLR built from the canonical global cup product; nothing the \
source proves is assumed"]
theorem isIso_globalBoxCupProduct_of_isFlatOver [IsAffine S] [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (hK : ∃ m₁ m₂ : ℤ, K.IsStrictlyGE m₁ ∧ K.IsStrictlyLE m₂)
    (hL : ∃ n : ℤ, L.IsStrictlyGE n)
    (hKflat : ∀ n, IsFlatOver a.toLRSHom.toShHom (K.X n).module)
    (hLflat : ∀ n, IsFlatOver b.toLRSHom.toShHom (L.X n).module) :
    IsIso (globalBoxCupProduct a b K L) := by
  obtain ⟨m₁, m₂, hK₁, hK₂⟩ := hK
  obtain ⟨n₀, hL₀⟩ := hL
  have : QuasiSeparatedSpace X := (quasiSeparatedSpace_iff_quasiSeparated X).2 ⟨inferInstance⟩
  have : QuasiSeparatedSpace Y := (quasiSeparatedSpace_iff_quasiSeparated Y).2 ⟨inferInstance⟩
  have hfin : {i : ℤ | ¬ IsZero (K.X i)}.Finite :=
    (Set.finite_Icc m₁ m₂).subset fun i hi => ⟨by
      by_contra h
      exact hi (K.isZero_of_isStrictlyGE m₁ i (by omega)), by
      by_contra h
      exact hi (K.isZero_of_isStrictlyLE m₂ i (by omega))⟩
  have hκ := AlgebraicGeometry.FlatKunneth.isIso_globalCupProductCanonical_app S
    ((derivedPushforward (inverseImageBaseProjection a)).obj
      (DerivedCategory.Q.obj (leftComplex a K)))
    ((derivedPushforward (inverseImageBaseProjection b)).obj
      (DerivedCategory.Q.obj (rightComplex b L)))
    (isQuasicoherent_homology_leftComplex a K hfin)
    (isQuasicoherent_homology_rightComplex_of_isStrictlyGE b L n₀)
  have hrel := isIso_baseSections_relativeBoxMap a b K L
    (isIso_relativeBoxMap_of_isStrictlyGE a b K hfin m₁ hKflat L n₀ hLflat)
  rw [globalBoxCupProduct_eq_relative]
  exact isIso_comp_five _ _ _ _ _ (isIso_tensorBase_lerayIso_inv a b K L) hκ hrel inferInstance

end Stacks.Cohomology.BoxKunnethFlat

end
