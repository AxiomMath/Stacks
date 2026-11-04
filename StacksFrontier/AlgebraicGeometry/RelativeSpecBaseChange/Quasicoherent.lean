module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Reduction
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafIsomorphism

/-!
# The base-change comparison of algebra sheaves, and quasi-coherence of the base change

Let `g : T ⟶ S` be a morphism of schemes and let `X` be a scheme over `S`.  The canonical
morphism of `𝒪_T`-algebras
```
baseChangeAlgebraHom g X :
  g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ (X ×_S T ⟶ T) _* 𝒪_{X ×_S T}
```
is constructed in `StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.BaseChange`.  The
base-change assertion of Stacks Tag 01SA is that it is an isomorphism when `X` is affine over
`S`, and the `algebraPullback_isQuasicoherent` clause of that tag is that the left-hand side is
quasi-coherent for every quasi-coherent algebra sheaf.

This file proves that those two assertions are *equivalent*, and proves unconditionally the
half of the first one which does not need any description of the sections of the pushout: for
`X` affine over `S`, composition with `baseChangeAlgebraHom g X` is a bijection onto the
morphisms out of the pushout into *any* pushed-forward structure sheaf.  Equivalently, the
pushout receives from `(X ×_S T ⟶ T) _* 𝒪_{X ×_S T}` a universal map to every algebra of the
form `q _* 𝒪_W`; what is not proved is that the pushout is itself of that form.

## Main definitions

* `Stacks.AffineAlgebraEquivalence.baseChangeAlgebraNatTrans` packages
  `baseChangeAlgebraHom` as a morphism of functors `(Over S)ᵒᵖ ⥤ AlgebraSheaf T`, so that its
  naturality in the scheme over `S` is part of the datum.
* `Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHomEquiv` is the bijection between the
  morphisms of `𝒪_T`-algebras `(X ×_S T ⟶ T) _* 𝒪_{X ×_S T} ⟶ W.hom _* 𝒪_W` and the morphisms
  `g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ W.hom _* 𝒪_W`, given by composition with
  `baseChangeAlgebraHom g X`.

## Main results

* `Stacks.AffineAlgebraEquivalence.bijective_comp_baseChangeAlgebraHom`: for `X` affine over
  `S`, composition with `baseChangeAlgebraHom g X` is a bijection on morphisms into any
  pushed-forward structure sheaf.  This is the Yoneda half of the base-change assertion.
* `Stacks.AffineAlgebraEquivalence.isIso_baseChangeAlgebraHom_iff`: for `X` affine over `S`,
  `baseChangeAlgebraHom g X` is an isomorphism if and only if
  `g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T` is quasi-coherent.
* `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_iff`: for an arbitrary
  quasi-coherent `𝒪_S`-algebra `A`, the algebra `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is quasi-coherent if and
  only if `baseChangeAlgebraHom g` is an isomorphism at the relative spectrum of `A`.  This is
  the `algebraPullback_isQuasicoherent` clause of Stacks Tag 01SA, reduced to the base-change
  assertion of the same tag.
* `Stacks.AffineAlgebraEquivalence.algebraPushforward_map_pushforwardAlgebraMap_overMap`: the
  direct image of algebra sheaves along `g` carries the canonical map of a morphism over `T` to
  the canonical map of the same morphism read over `S`.

## Implementation notes

The bijection `baseChangeAlgebraHomEquiv` is the composite of four bijections, but it is not
written as a composite: the four categories involved spell the same objects differently —
`(algebraPushforward g).obj (q _* 𝒪_W)` and `(q ≫ g) _* 𝒪_W` are equal by `rfl` but not
syntactically, so `Equiv.trans` of the four is type-correct only up to unfolding and no
rewrite can then be performed underneath it.  The bijection is therefore given with
composition with `baseChangeAlgebraHom g X` as its forward map, and the two round trips are
checked against the explicit inverse.

The computation that drives both round trips is `homEquiv_baseChangeAlgebraHom_comp`: the
adjunct of `baseChangeAlgebraHom g X ≫ q _* 𝒪_W` is the canonical map of the composite
`W ⟶ X ×_S T ⟶ X`, read over `S`.  It is this statement, and not the pushout property, which
makes the base-change morphism computable: `baseChangeAlgebraHom` is *defined* as an adjunct,
so the adjunction's naturality in the target reduces it to the functoriality of
`pushforwardAlgebraMap`, for which the only new input is
`algebraPushforward_map_pushforwardAlgebraMap_overMap`.  The remaining bijections are the universal
property `overHomEquivAlgebraHom` of the relative spectrum, applied twice — over `S` with
target `X` and over `T` with target `X ×_S T`, both affine — and the adjunction
`CategoryTheory.Over.mapPullbackAdj`, whose counit is the fibre-product projection
`baseChangeProjection`.

What that bijection does *not* give is an inverse to `baseChangeAlgebraHom g X`: producing one
requires surjectivity of composition on morphisms into the pushout itself, and the pushout is
not known to be a pushed-forward structure sheaf.  That is exactly the content of
`isIso_baseChangeAlgebraHom_iff`, whose remaining direction rests on the essential surjectivity
`pushforwardAlgebraIso` of `X ↦ X.hom _* 𝒪_X`: once the pushout is quasi-coherent it *is* a
pushed-forward structure sheaf, the bijection applies to it, and the resulting section of
`baseChangeAlgebraHom g X` is a two-sided inverse because composition is also injective.

The residual statement is Stacks Tag 01LX part (2), that `S' ×_S Spec_S(A) = Spec_{S'}(g^*A)`;
parts (1) and (3) of that tag are `isAffineOpen_preimage_relativeSpecToBase` and
`pushforwardAlgebraIso`.  Proving it means computing the sections of a pushout of sheaves of
commutative rings on an affine open, which no part of Mathlib at this revision addresses:
there is no extension of scalars for (pre)sheaves of modules, `SheafOfModules.pullback` is
defined as a left adjoint with no objectwise description, and nothing relates a colimit of
sheaves of rings to base change of the underlying modules.

Several proofs are in term mode.  `TopCat.Sheaf CommRingCat X` is a category of sheaves on an
`InducedCategory`, and `pushforwardAlgebra` unfolds through a left Kan extension whose
`getLimitCone` is not exposed; a `rw` whose motive mentions either of these fails with a
non-type-correct motive, and `rfl` on an equality of two morphisms of pushed-forward algebras
exhausts the heartbeat budget in `whnf`.  Both are avoided by computing on sections, through
`pushforwardAlgebraMap_app`, or by `Eq.trans`/`congrArg` chains, which are checked at default
transparency.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- The base change along `g` of a scheme affine over `S` is affine over `T`. -/
public instance isAffineHom_overPullback_hom (X : Over S) [IsAffineHom X.hom] :
    IsAffineHom ((Over.pullback g).obj X).hom :=
  isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback X.hom g) ‹_›

/-! ### Direct image of algebra sheaves and the canonical maps -/

/-- The sections over an open `U` of `S` of the direct image along `g` of a morphism of
`𝒪_T`-algebras are its sections over `g⁻¹U`. -/
public theorem algebraPushforward_map_right_app {B B' : Stacks.RelativeSpec.AlgebraSheaf T}
    (ψ : B ⟶ B') (U : S.Opens) :
    ((algebraPushforward g).map ψ).right.hom.app (op U) =
      ψ.right.hom.app (op (g ⁻¹ᵁ U)) := rfl

/-- The direct image along `g` of the canonical map on pushed-forward structure sheaves of a
morphism over `T` is the canonical map of the same morphism read as a morphism over `S`.

The morphism over `S` is written as `(Over.map g).map w`, which is the form the adjunction
`CategoryTheory.Over.mapPullbackAdj` produces;
`Stacks.AffineAlgebraEquivalence.algebraPushforward_map_pushforwardAlgebraMap` is the statement
for a morphism over `S` base-changed to `T` and read back through
`Stacks.AffineAlgebraEquivalence.baseChangeOverMap`. -/
public theorem algebraPushforward_map_pushforwardAlgebraMap_overMap {W V : Over T} (w : W ⟶ V) :
    ((algebraPushforward g).map (pushforwardAlgebraMap w) :
        pushforwardAlgebra ((Over.map g).obj V).hom ⟶
          pushforwardAlgebra ((Over.map g).obj W).hom) =
      pushforwardAlgebraMap ((Over.map g).map w) := by
  ext1
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun Uop => ?_)
  obtain ⟨U⟩ := Uop
  rw [algebraPushforward_map_right_app,
    pushforwardAlgebraMap_app w (g ⁻¹ᵁ U) (preimage_le_preimage_preimage _ _),
    pushforwardAlgebraMap_app ((Over.map g).map w) U (preimage_le_preimage_preimage _ _)]
  rfl

/-- The inverse of the bijection of `CategoryTheory.Over.mapPullbackAdj` sends a morphism
`W ⟶ X ×_S T` over `T` to its composite with the fibre-product projection, read over `S`. -/
public theorem mapPullbackAdj_homEquiv_symm_eq (X : Over S) (W : Over T)
    (w : W ⟶ (Over.pullback g).obj X) :
    ((Over.mapPullbackAdj g).homEquiv W X).symm w =
      (Over.map g).map w ≫ baseChangeProjection g X := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- The bijection of `CategoryTheory.Over.mapPullbackAdj` recovers a morphism
`W ⟶ X ×_S T` over `T` from its composite with the fibre-product projection. -/
public theorem mapPullbackAdj_homEquiv_eq (X : Over S) (W : Over T)
    (w : W ⟶ (Over.pullback g).obj X) :
    (Over.mapPullbackAdj g).homEquiv W X
        ((Over.map g).map w ≫ baseChangeProjection g X) = w :=
  ((((Over.mapPullbackAdj g).homEquiv W X).symm_apply_eq).mp
    (mapPullbackAdj_homEquiv_symm_eq g X W w)).symm

/-! ### The adjunct of the base-change morphism -/

/-- **The adjunct of the base-change morphism.** For a morphism `w : W ⟶ X ×_S T` of schemes
over `T`, the morphism of `𝒪_S`-algebras adjoint to
`baseChangeAlgebraHom g X ≫ pushforwardAlgebraMap w` is the canonical map on pushed-forward
structure sheaves of the composite `W ⟶ X ×_S T ⟶ X`, read as a morphism over `S`. -/
public theorem homEquiv_baseChangeAlgebraHom_comp (X : Over S) {W : Over T}
    (w : W ⟶ (Over.pullback g).obj X) :
    (algebraPullbackPushforwardAdjunction g).homEquiv (pushforwardAlgebra X.hom)
        (pushforwardAlgebra W.hom) (baseChangeAlgebraHom g X ≫ pushforwardAlgebraMap w) =
      pushforwardAlgebraMap ((Over.map g).map w ≫ baseChangeProjection g X) := by
  refine Eq.trans (Adjunction.homEquiv_naturality_right _ _ _) (Eq.trans
    (congrArg (fun k => k ≫ (algebraPushforward g).map (pushforwardAlgebraMap w))
      (((algebraPullbackPushforwardAdjunction g).homEquiv (pushforwardAlgebra X.hom)
        (pushforwardAlgebra (Over.mk (pullback.snd X.hom g)).hom)).apply_symm_apply
          (pushforwardAlgebraMap (baseChangeProjection g X)))) ?_)
  exact Eq.trans (congrArg (fun k => pushforwardAlgebraMap (baseChangeProjection g X) ≫ k)
      (algebraPushforward_map_pushforwardAlgebraMap_overMap g w))
    (pushforwardAlgebraMap_comp ((Over.map g).map w) (baseChangeProjection g X)).symm

/-! ### Naturality of the base-change morphism -/

/-- The fibre-product projections are natural: the projection from `X ×_S T` followed by a
morphism `X ⟶ Y` over `S` is the base change of that morphism followed by the projection from
`Y ×_S T`.

The base-changed morphism is written as `(Over.map g).map ((Over.pullback g).map k)`;
`Stacks.AffineAlgebraEquivalence.baseChangeProjection_comp` is the same square with it written
as `Stacks.AffineAlgebraEquivalence.baseChangeOverMap`. -/
public theorem baseChangeProjection_comp_overMap (X Y : Over S) (k : X ⟶ Y) :
    baseChangeProjection g X ≫ k =
      (Over.map g).map ((Over.pullback g).map k) ≫ baseChangeProjection g Y :=
  Over.OverMorphism.ext (by
    show pullback.fst X.hom g ≫ k.left =
      ((Over.pullback g).map k).left ≫ pullback.fst Y.hom g
    simp [Over.pullback, pullback.lift_fst])

/-- The base-change morphism of algebra sheaves as a morphism of functors
`(Over S)ᵒᵖ ⥤ AlgebraSheaf T`, from the base change of `X ↦ X.hom _* 𝒪_X` to the pushed-forward
structure sheaf of the base-changed scheme. -/
public noncomputable def baseChangeAlgebraNatTrans :
    pushforwardAlgebraFunctor S ⋙ algebraPullback g ⟶
      (Over.pullback g).op ⋙ pushforwardAlgebraFunctor T where
  app X := baseChangeAlgebraHom g X.unop
  naturality _ _ f := baseChangeAlgebraHom_naturality g f.unop

/-! ### The Yoneda half of the base-change assertion -/

/-- The inverse of the universal property of the relative spectrum undoes the canonical map on
pushed-forward structure sheaves. -/
public theorem overHomEquivAlgebraHom_symm_pushforwardAlgebraMap {X Y : Over S}
    [IsAffineHom Y.hom] (u : X ⟶ Y) :
    (overHomEquivAlgebraHom X Y).symm (pushforwardAlgebraMap u) = u :=
  (overHomEquivAlgebraHom X Y).symm_apply_eq.mpr (overHomEquivAlgebraHom_apply u).symm

/-- **Composition with the base-change morphism is a bijection onto the morphisms into a
pushed-forward structure sheaf.** For `X` affine over `S` and `W` an arbitrary scheme over `T`,
a morphism of `𝒪_T`-algebras `g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ W.hom _* 𝒪_W` is the same
thing as a morphism `(X ×_S T ⟶ T) _* 𝒪_{X ×_S T} ⟶ W.hom _* 𝒪_W`. -/
public noncomputable def baseChangeAlgebraHomEquiv (X : Over S) [IsAffineHom X.hom]
    (W : Over T) :
    (pushforwardAlgebra ((Over.pullback g).obj X).hom ⟶ pushforwardAlgebra W.hom) ≃
      ((algebraPullback g).obj (pushforwardAlgebra X.hom) ⟶ pushforwardAlgebra W.hom) where
  toFun u := baseChangeAlgebraHom g X ≫ u
  invFun v := pushforwardAlgebraMap ((Over.mapPullbackAdj g).homEquiv W X
      ((overHomEquivAlgebraHom ((Over.map g).obj W) X).symm
        ((algebraPullbackPushforwardAdjunction g).homEquiv (pushforwardAlgebra X.hom)
          (pushforwardAlgebra W.hom) v)))
  left_inv u := by
    obtain ⟨w, rfl⟩ := (overHomEquivAlgebraHom W ((Over.pullback g).obj X)).surjective u
    rw [overHomEquivAlgebraHom_apply]
    refine Eq.trans (congrArg (fun z => pushforwardAlgebraMap
        ((Over.mapPullbackAdj g).homEquiv W X
          ((overHomEquivAlgebraHom ((Over.map g).obj W) X).symm z)))
      (homEquiv_baseChangeAlgebraHom_comp g X w)) ?_
    refine Eq.trans (congrArg (fun z => pushforwardAlgebraMap
        ((Over.mapPullbackAdj g).homEquiv W X z))
      (overHomEquivAlgebraHom_symm_pushforwardAlgebraMap
        ((Over.map g).map w ≫ baseChangeProjection g X))) ?_
    exact congrArg pushforwardAlgebraMap (mapPullbackAdj_homEquiv_eq g X W w)
  right_inv v := by
    refine ((algebraPullbackPushforwardAdjunction g).homEquiv (pushforwardAlgebra X.hom)
      (pushforwardAlgebra W.hom)).injective ?_
    refine Eq.trans (homEquiv_baseChangeAlgebraHom_comp g X _) ?_
    refine Eq.trans (congrArg pushforwardAlgebraMap
      (Eq.trans (mapPullbackAdj_homEquiv_symm_eq g X W _).symm
        (((Over.mapPullbackAdj g).homEquiv W X).symm_apply_apply _))) ?_
    exact (overHomEquivAlgebraHom_apply _).symm.trans
      ((overHomEquivAlgebraHom ((Over.map g).obj W) X).apply_symm_apply _)

/-- Composition with the base-change morphism is a bijection on morphisms into any
pushed-forward structure sheaf. -/
public theorem bijective_comp_baseChangeAlgebraHom (X : Over S) [IsAffineHom X.hom]
    (W : Over T) :
    Function.Bijective (fun u : pushforwardAlgebra ((Over.pullback g).obj X).hom ⟶
        pushforwardAlgebra W.hom => baseChangeAlgebraHom g X ≫ u) :=
  (baseChangeAlgebraHomEquiv g X W).bijective

/-! ### Quasi-coherence of the base change and the base-change assertion -/

/-- If the base change `g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T` of a scheme affine over `S` is
quasi-coherent, then the base-change morphism is an isomorphism.  Quasi-coherence makes the
source a pushed-forward structure sheaf, by the essential surjectivity
`pushforwardAlgebraIso`, so `bijective_comp_baseChangeAlgebraHom` applies to it and produces a
section; the section is a two-sided inverse because composition is also injective. -/
public theorem isIso_baseChangeAlgebraHom_of_isQuasicoherent (X : Over S) [IsAffineHom X.hom]
    (h : Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      ((algebraPullback g).obj (pushforwardAlgebra X.hom))) :
    IsIso (baseChangeAlgebraHom g X) := by
  have := h
  let e := pushforwardAlgebraIso ((algebraPullback g).obj (pushforwardAlgebra X.hom))
  obtain ⟨u, hu⟩ : ∃ u, baseChangeAlgebraHom g X ≫ u = e.inv :=
    (bijective_comp_baseChangeAlgebraHom g X (Over.mk (relativeSpecToBase
      ((algebraPullback g).obj (pushforwardAlgebra X.hom))))).surjective e.inv
  refine ⟨u ≫ e.hom, ?_, ?_⟩
  · rw [← Category.assoc, hu, Iso.inv_hom_id]
  · refine (bijective_comp_baseChangeAlgebraHom g X ((Over.pullback g).obj X)).injective ?_
    rw [Category.comp_id, ← Category.assoc, ← Category.assoc, hu, Iso.inv_hom_id,
      Category.id_comp]

/-- If the base-change morphism at a scheme affine over `S` is an isomorphism, then the base
change `g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T` is quasi-coherent, being then isomorphic to the
pushed-forward structure sheaf of a scheme affine over `T`. -/
public theorem isQuasicoherent_algebraPullback_pushforwardAlgebra (X : Over S)
    [IsAffineHom X.hom] (h : IsIso (baseChangeAlgebraHom g X)) :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
      ((algebraPullback g).obj (pushforwardAlgebra X.hom)) :=
  Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_of_iso (@asIso _ _ _ _ _ h).symm
    (isQuasicoherent_pushforwardAlgebra ((Over.pullback g).obj X).hom)

/-- **The base-change assertion of Stacks Tag 01SA and its quasi-coherence clause are
equivalent.** For `X` affine over `S`, the base-change morphism is an isomorphism if and only
if the base change `g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T` is quasi-coherent. -/
public theorem isIso_baseChangeAlgebraHom_iff (X : Over S) [IsAffineHom X.hom] :
    IsIso (baseChangeAlgebraHom g X) ↔
      Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent
        ((algebraPullback g).obj (pushforwardAlgebra X.hom)) :=
  ⟨isQuasicoherent_algebraPullback_pushforwardAlgebra g X,
    isIso_baseChangeAlgebraHom_of_isQuasicoherent g X⟩

/-- For a quasi-coherent `𝒪_S`-algebra `A`, the base change `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is
quasi-coherent if and only if the base-change morphism is an isomorphism at the relative
spectrum of `A`. -/
private theorem isQuasicoherent_algebraPullback_iff_isIso
    (A : Stacks.RelativeSpec.AlgebraSheaf S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) ↔
      IsIso (baseChangeAlgebraHom g (Over.mk (relativeSpecToBase A))) := by
  have : IsAffineHom (Over.mk (relativeSpecToBase A)).hom := isAffineHom_relativeSpecToBase A
  exact ⟨fun h => isIso_baseChangeAlgebraHom_of_isQuasicoherent g
      (Over.mk (relativeSpecToBase A))
      (Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_of_iso
        ((algebraPullback g).mapIso (pushforwardAlgebraIso A)).symm h),
    fun h => Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_of_iso
      ((algebraPullback g).mapIso (pushforwardAlgebraIso A))
      (isQuasicoherent_algebraPullback_pushforwardAlgebra g (Over.mk (relativeSpecToBase A)) h)⟩

/-- The base change `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` of a quasi-coherent `𝒪_S`-algebra `A` is
quasi-coherent, provided the base-change morphism is an isomorphism at the relative spectrum of
`A`.  This is the `algebraPullback_isQuasicoherent` clause of Stacks Tag 01SA. -/
public theorem isQuasicoherent_algebraPullback (A : Stacks.RelativeSpec.AlgebraSheaf S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]
    (h : IsIso (baseChangeAlgebraHom g (Over.mk (relativeSpecToBase A)))) :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  (isQuasicoherent_algebraPullback_iff_isIso g A).mpr h

/-- For a quasi-coherent `𝒪_S`-algebra `A`, the base change `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is
quasi-coherent if and only if the base-change morphism is an isomorphism at the relative
spectrum of `A`. -/
public theorem isQuasicoherent_algebraPullback_iff (A : Stacks.RelativeSpec.AlgebraSheaf S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) ↔
      IsIso (baseChangeAlgebraHom g (Over.mk (relativeSpecToBase A))) :=
  isQuasicoherent_algebraPullback_iff_isIso g A

end Stacks.AffineAlgebraEquivalence

end
