module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.AffineAlgebraHom
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Quasicoherent

/-!
# The base-change assertion of Stacks Tag 01SA for a morphism of affine schemes

Let `h : T ⟶ S` be a morphism of *affine* schemes and let `X` be a scheme affine over `S`.  This
file proves that the base-change comparison
```
baseChangeAlgebraHom h X : h⁻¹(X.hom _* 𝒪_X) ⊗_{h⁻¹𝒪_S} 𝒪_T ⟶ (X ×_S T ⟶ T) _* 𝒪_{X ×_S T}
```
is an isomorphism, and consequently that the base change along `h` of a quasi-coherent
`𝒪_S`-algebra is quasi-coherent, which is Stacks Tag 01LX part (2) for a morphism of affine
schemes.

The content is that the *target* of the comparison has the universal property of the pushout
which defines its source.  Testing that universal property means mapping out of the target into
an arbitrary sheaf of commutative rings on `T`, and the tool for that is the universal property
of the relative spectrum over an affine base in its form for an arbitrary target algebra sheaf,
`Stacks.RelativeSpec.AlgebraSheaf.homEquivUnitTopHom`.

## Main definitions

* `Stacks.AffineAlgebraEquivalence.affineDescRingHom` is the ring map on global sections
  obtained from a cocone, and `Stacks.AffineAlgebraEquivalence.affineDescHom` is the morphism of
  algebra sheaves it determines.
* `Stacks.AffineAlgebraEquivalence.algebraPullbackComp` is the pseudofunctoriality of base change
  of algebra sheaves, which is the step by which the general case of the tag reduces to the
  affine case proved here.

## Main results

* `Stacks.AffineAlgebraEquivalence.isPushout_pushforwardBaseChangeMap`: for `h` a morphism of
  affine schemes and `X` affine over `S`, the pushed-forward structure sheaf of `X ×_S T` is the
  pushout of `h⁻¹(X.hom _* 𝒪_X)` and `𝒪_T` over `h⁻¹𝒪_S`.
* `Stacks.AffineAlgebraEquivalence.isIso_baseChangeAlgebraHom_of_isAffine`: the base-change
  comparison is an isomorphism.
* `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_isAffine`: **Stacks Tag
  01LX part (2) for a morphism of affine schemes.**  The base change of a quasi-coherent
  `𝒪_S`-algebra along a morphism of affine schemes is quasi-coherent.

## Implementation notes

Three inputs meet here, and each is used exactly once.

The ring-theoretic input is `AlgebraicGeometry.isPushout_appTop_of_isPullback`: the global
sections of a fibre product of affine schemes are the pushout of the global sections, so
`Γ(X ×_S T, ⊤) = Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(T, ⊤)` as commutative rings.  This is where the
affineness of `S`, of `T` and of `X` is consumed, the last being automatic from
`IsAffineHom X.hom` over an affine base.

The sheaf-theoretic input on the target side is the universal property of the relative spectrum
over an affine base, which converts a morphism of algebra sheaves out of a quasi-coherent
algebra into a ring map on global sections and back.  It is applied over `T` to the target
`(X ×_S T ⟶ T) _* 𝒪_{X ×_S T}`, which is quasi-coherent because `X ×_S T ⟶ T` is affine, and
over `S` to `X.hom _* 𝒪_X`.

The adjunction input is `TopCat.Sheaf.pullbackPushforwardAdjunction`, which turns the
compatibility condition of a cocone into the statement that its adjunct is a morphism of algebra
sheaves `X.hom _* 𝒪_X ⟶ h_* B`, and turns the left-hand factorization condition into an
equation between morphisms of algebra sheaves on `S`.  The equation
`unit_comp_map_inverseImageStructureMap` is what identifies the structure map of `h_* B` with the
adjunct of the structural map `h⁻¹𝒪_S ⟶ 𝒪_T`, and it is the only place where the specific
construction of `inverseImageStructureMap` is used.

The commutation of the square whose colimit is being checked is not proved directly: it is
`algebraPullback_isPushout` composed with the two factorization identities of
`baseChangeAlgebraHom`, namely `algebraPullbackMap_comp_baseChangeAlgebraHom` on the left and
`CategoryTheory.Under.w` on the right.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.RelativeSpec.AlgebraSheaf

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {T S : Scheme.{u}} (h : T ⟶ S)

/-! ### Global sections of the direct image -/

/-- The component on global sections of the direct image of a morphism of sheaves of rings. -/
public theorem pushforward_map_app_top {B B' : TopCat.Sheaf CommRingCat.{u} T} (k : B ⟶ B') :
    ((TopCat.Sheaf.pushforward CommRingCat h.base).map k).hom.app (op (⊤ : S.Opens)) =
      k.hom.app (op ⊤) :=
  rfl

/-- The structure map on global sections of the direct image of an algebra sheaf. -/
public theorem algebraPushforward_unitTop (B : Stacks.RelativeSpec.AlgebraSheaf.{u} T) :
    ((algebraPushforward h).obj B).unitTop = h.appTop ≫ B.unitTop :=
  rfl

/-- The tip of a cocone of sheaves of commutative rings on `T` under `𝒪_T`, read as a sheaf of
`𝒪_T`-algebras through the right-hand leg of the cocone. -/
public noncomputable abbrev coconeAlgebra {B : TopCat.Sheaf CommRingCat.{u} T}
    (v : T.sheaf ⟶ B) : Stacks.RelativeSpec.AlgebraSheaf.{u} T :=
  Under.mk v

/-! ### The adjunct of a cocone and of the base-change comparison -/

section

variable (X : Over S)

/-- The component on global sections of the canonical map attached to the fibre-product
projection is the action of the projection on global sections. -/
public theorem pushforwardAlgebraMap_baseChangeProjection_app_top :
    (pushforwardAlgebraMap (baseChangeProjection h X)).right.hom.app (op ⊤) =
      (pullback.fst X.hom h).appTop := by
  rw [pushforwardAlgebraMap_app (baseChangeProjection h X) ⊤
    (preimage_le_preimage_preimage _ _)]
  exact (pullback.fst X.hom h).appLE_eq_app

/-- The adjunct of the base-change comparison is the canonical map attached to the fibre-product
projection; this is how the comparison was defined. -/
public theorem homEquiv_pushforwardBaseChangeMap :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat h.base).homEquiv
        (pushforwardAlgebra X.hom).right
        (pushforwardAlgebra ((Over.pullback h).obj X).hom).right
        (pushforwardBaseChangeMap h X) =
      (pushforwardAlgebraMap (baseChangeProjection h X)).right :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat h.base).homEquiv _ _).apply_symm_apply _

variable {B : TopCat.Sheaf CommRingCat.{u} T}
  (u : (TopCat.Sheaf.pullback CommRingCat h.base).obj (pushforwardAlgebra X.hom).right ⟶ B)

/-- The adjunct of the left-hand leg of a cocone: a morphism of sheaves of rings
`X.hom _* 𝒪_X ⟶ h_* B` on `S`. -/
public noncomputable def coconeAdjunct :
    (pushforwardAlgebra X.hom).right ⟶ (TopCat.Sheaf.pushforward CommRingCat h.base).obj B :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat h.base).homEquiv
    (pushforwardAlgebra X.hom).right B u

/-- The cocone condition, read through the adjunction: the adjunct of the left-hand leg is a
morphism of algebra sheaves into the direct image of the tip, with the algebra structure given
by the right-hand leg. -/
public theorem hom_comp_coconeAdjunct (v : T.sheaf ⟶ B)
    (huv : (TopCat.Sheaf.pullback CommRingCat h.base).map (pushforwardAlgebra X.hom).hom ≫ u =
      inverseImageStructureMap h ≫ v) :
    (pushforwardAlgebra X.hom).hom ≫ coconeAdjunct h X u =
      ((algebraPushforward h).obj (coconeAlgebra v)).hom := by
  refine Eq.trans (Adjunction.homEquiv_naturality_left
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat h.base)
    (pushforwardAlgebra X.hom).hom u).symm ?_
  refine Eq.trans (congrArg
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat h.base).homEquiv S.sheaf B) huv) ?_
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    unit_comp_map_inverseImageStructureMap h]
  rfl

/-- The condition on global sections satisfied by the two legs of a cocone. -/
public theorem appTop_comp_coconeAdjunct (v : T.sheaf ⟶ B)
    (huv : (TopCat.Sheaf.pullback CommRingCat h.base).map (pushforwardAlgebra X.hom).hom ≫ u =
      inverseImageStructureMap h ≫ v) :
    X.hom.appTop ≫ (coconeAdjunct h X u).hom.app (op ⊤) =
      h.appTop ≫ (coconeAlgebra v).unitTop :=
  congrArg (fun k : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat h.base).obj B ↦
    k.hom.app (op ⊤)) (hom_comp_coconeAdjunct h X u v huv)

/-- The adjunct of the composite of the base-change comparison with a morphism out of the
pushed-forward structure sheaf of `X ×_S T`. -/
public theorem homEquiv_pushforwardBaseChangeMap_comp
    (m : (pushforwardAlgebra ((Over.pullback h).obj X).hom).right ⟶ B) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat h.base).homEquiv
        (pushforwardAlgebra X.hom).right B (pushforwardBaseChangeMap h X ≫ m) =
      (pushforwardAlgebraMap (baseChangeProjection h X)).right ≫
        (TopCat.Sheaf.pushforward CommRingCat h.base).map m :=
  Eq.trans (Adjunction.homEquiv_naturality_right
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat h.base)
      (pushforwardBaseChangeMap h X) m)
    (congrArg (fun k ↦ k ≫ (TopCat.Sheaf.pushforward CommRingCat h.base).map m)
      (homEquiv_pushforwardBaseChangeMap h X))

/-- The left-hand factorization condition implies one equation of ring maps on global
sections. -/
public theorem appTop_of_pushforwardBaseChangeMap_comp_eq
    (m : (pushforwardAlgebra ((Over.pullback h).obj X).hom).right ⟶ B)
    (hm : pushforwardBaseChangeMap h X ≫ m = u) :
    (pullback.fst X.hom h).appTop ≫ m.hom.app (op ⊤) =
      (coconeAdjunct h X u).hom.app (op ⊤) := by
  have key : (pushforwardAlgebraMap (baseChangeProjection h X)).right ≫
      (TopCat.Sheaf.pushforward CommRingCat h.base).map m = coconeAdjunct h X u :=
    Eq.trans (homEquiv_pushforwardBaseChangeMap_comp h X m).symm
      (congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat h.base).homEquiv
        (pushforwardAlgebra X.hom).right B) hm)
  refine Eq.trans ?_ (congrArg (fun k : (pushforwardAlgebra X.hom).right ⟶
    (TopCat.Sheaf.pushforward CommRingCat h.base).obj B ↦ k.hom.app (op ⊤)) key)
  exact congrArg (fun k ↦ k ≫ m.hom.app (op ⊤))
    (pushforwardAlgebraMap_baseChangeProjection_app_top h X).symm

/-- The equation of ring maps on global sections implies the left-hand factorization condition,
because a morphism out of the quasi-coherent algebra `X.hom _* 𝒪_X` over the affine base `S` is
determined by its component on global sections. -/
public theorem pushforwardBaseChangeMap_comp_eq_of_appTop [IsAffine S] [IsAffineHom X.hom]
    (m : (pushforwardAlgebra ((Over.pullback h).obj X).hom).right ⟶ B)
    (hm : (pullback.fst X.hom h).appTop ≫ m.hom.app (op ⊤) =
      (coconeAdjunct h X u).hom.app (op ⊤)) :
    pushforwardBaseChangeMap h X ≫ m = u := by
  have := isQuasicoherent_pushforwardAlgebra X.hom
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat h.base).homEquiv
    (pushforwardAlgebra X.hom).right B).injective ?_
  refine Eq.trans (homEquiv_pushforwardBaseChangeMap_comp h X m)
    (Sheaf.hom_ext (hom_ext_app_top (pushforwardAlgebra X.hom) ?_))
  exact Eq.trans (congrArg (fun k ↦ k ≫ m.hom.app (op ⊤))
    (pushforwardAlgebraMap_baseChangeProjection_app_top h X)) hm

end

/-! ### The pushout property of the base change -/

section

variable [IsAffine S] [IsAffine T] (X : Over S) [IsAffineHom X.hom]

/-- The global sections of the fibre product `X ×_S T` are the pushout of the global sections of
`X` and of `T` over those of `S`. -/
public theorem isPushout_appTop_pullback :
    IsPushout X.hom.appTop h.appTop (pullback.fst X.hom h).appTop
      (pullback.snd X.hom h).appTop :=
  have := isAffine_of_isAffineHom X.hom
  isPushout_appTop_of_isPullback (IsPullback.of_hasPullback X.hom h)

section

variable {B : TopCat.Sheaf CommRingCat.{u} T}
  (u : (TopCat.Sheaf.pullback CommRingCat h.base).obj (pushforwardAlgebra X.hom).right ⟶ B)
  (v : T.sheaf ⟶ B)
  (huv : (TopCat.Sheaf.pullback CommRingCat h.base).map (pushforwardAlgebra X.hom).hom ≫ u =
    inverseImageStructureMap h ≫ v)

/-- The ring map on global sections out of `Γ(X ×_S T, ⊤)` determined by a cocone, through the
pushout property of the global sections of a fibre product of affine schemes. -/
public noncomputable def affineDescRingHom :
    (pushforwardAlgebra ((Over.pullback h).obj X).hom).sections ⊤ ⟶
      (coconeAlgebra v).sections ⊤ :=
  (isPushout_appTop_pullback h X).desc ((coconeAdjunct h X u).hom.app (op ⊤))
    ((coconeAlgebra v).unitTop) (appTop_comp_coconeAdjunct h X u v huv)

/-- The ring map of `affineDescRingHom` is compatible with the structure maps on global
sections. -/
public theorem unitTop_comp_affineDescRingHom :
    (pushforwardAlgebra ((Over.pullback h).obj X).hom).unitTop ≫
        affineDescRingHom h X u v huv = (coconeAlgebra v).unitTop :=
  (isPushout_appTop_pullback h X).inr_desc _ _ _

/-- The morphism of algebra sheaves out of the pushed-forward structure sheaf of `X ×_S T`
determined by a cocone. -/
public noncomputable def affineDescHom :
    pushforwardAlgebra ((Over.pullback h).obj X).hom ⟶ coconeAlgebra v :=
  haveI := isQuasicoherent_pushforwardAlgebra ((Over.pullback h).obj X).hom
  algebraHom (pushforwardAlgebra ((Over.pullback h).obj X).hom) (coconeAlgebra v)
    (unitTop_comp_affineDescRingHom h X u v huv)

/-- The component on global sections of `affineDescHom` is `affineDescRingHom`. -/
public theorem affineDescHom_right_app_top :
    (affineDescHom h X u v huv).right.hom.app (op ⊤) = affineDescRingHom h X u v huv :=
  have := isQuasicoherent_pushforwardAlgebra ((Over.pullback h).obj X).hom
  algebraHom_right_app_top (pushforwardAlgebra ((Over.pullback h).obj X).hom) (coconeAlgebra v)
    (unitTop_comp_affineDescRingHom h X u v huv)

end

/-- **The pushed-forward structure sheaf of `X ×_S T` is the base change of that of `X`.** For a
morphism `h : T ⟶ S` of affine schemes and `X` affine over `S`, the sheaf of rings
`(X ×_S T ⟶ T) _* 𝒪_{X ×_S T}` is the pushout of `h⁻¹(X.hom _* 𝒪_X)` and `𝒪_T` over
`h⁻¹𝒪_S`. -/
public theorem isPushout_pushforwardBaseChangeMap :
    IsPushout ((TopCat.Sheaf.pullback CommRingCat h.base).map (pushforwardAlgebra X.hom).hom)
      (inverseImageStructureMap h) (pushforwardBaseChangeMap h X)
      (pushforwardAlgebra ((Over.pullback h).obj X).hom).hom := by
  have hw : (TopCat.Sheaf.pullback CommRingCat h.base).map (pushforwardAlgebra X.hom).hom ≫
      pushforwardBaseChangeMap h X = inverseImageStructureMap h ≫
        (pushforwardAlgebra ((Over.pullback h).obj X).hom).hom := by
    refine Eq.trans (congrArg (fun k ↦ (TopCat.Sheaf.pullback CommRingCat h.base).map
      (pushforwardAlgebra X.hom).hom ≫ k)
      (algebraPullbackMap_comp_baseChangeAlgebraHom h X).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k ↦ k ≫ (baseChangeAlgebraHom h X).right)
      (algebraPullback_isPushout h (pushforwardAlgebra X.hom)).w) ?_
    exact Eq.trans (Category.assoc _ _ _) (congrArg (fun k ↦ inverseImageStructureMap h ≫ k)
      (Under.w (baseChangeAlgebraHom h X)))
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk hw
    (fun s ↦ (affineDescHom h X s.inl s.inr s.condition).right) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m hl hr ↦ ?_))
  · refine pushforwardBaseChangeMap_comp_eq_of_appTop h X s.inl _ ?_
    exact Eq.trans (congrArg (fun k ↦ (pullback.fst X.hom h).appTop ≫ k)
      (affineDescHom_right_app_top h X s.inl s.inr s.condition))
      ((isPushout_appTop_pullback h X).inl_desc _ _ _)
  · exact Under.w (affineDescHom h X s.inl s.inr s.condition)
  · have := isQuasicoherent_pushforwardAlgebra ((Over.pullback h).obj X).hom
    refine Sheaf.hom_ext (hom_ext_app_top
      (pushforwardAlgebra ((Over.pullback h).obj X).hom) ?_)
    refine Eq.trans ?_ (affineDescHom_right_app_top h X s.inl s.inr s.condition).symm
    refine (isPushout_appTop_pullback h X).hom_ext ?_ ?_
    · exact Eq.trans (appTop_of_pushforwardBaseChangeMap_comp_eq h X s.inl m hl)
        ((isPushout_appTop_pullback h X).inl_desc _ _ _).symm
    · refine Eq.trans (congrArg (fun k : T.sheaf ⟶ s.pt ↦ k.hom.app (op ⊤)) hr) ?_
      exact ((isPushout_appTop_pullback h X).inr_desc _ _ _).symm

/-! ### The base-change comparison is an isomorphism -/

/-- The inverse of the base-change comparison, as a morphism of sheaves of rings: the map out of
the pushout `(X ×_S T ⟶ T) _* 𝒪_{X ×_S T}` determined by the two legs of the defining pushout
square of the source. -/
public noncomputable def baseChangeAlgebraInv :
    (pushforwardAlgebra ((Over.pullback h).obj X).hom).right ⟶
      ((algebraPullback h).obj (pushforwardAlgebra X.hom)).right :=
  (isPushout_pushforwardBaseChangeMap h X).desc
    ((algebraPullbackMap h).app (pushforwardAlgebra X.hom))
    ((algebraPullback h).obj (pushforwardAlgebra X.hom)).hom
    (algebraPullback_isPushout h (pushforwardAlgebra X.hom)).w

/-- If `w ≫ f = g` and `g ≫ i = w`, then `w ≫ f ≫ i = w ≫ 𝟙 _`. -/
private theorem comp_comp_eq_comp_id {C : Type*} [Category C] {X Y Z : C} (w : X ⟶ Y)
    (f : Y ⟶ Z) (i : Z ⟶ Y) {g : X ⟶ Z} (h₁ : w ≫ f = g) (h₂ : g ≫ i = w) :
    w ≫ f ≫ i = w ≫ 𝟙 Y := by
  rw [← Category.assoc, h₁, h₂, Category.comp_id]

/-- **The base-change assertion of Stacks Tag 01SA for a morphism of affine schemes.** For
`h : T ⟶ S` a morphism of affine schemes and `X` affine over `S`, the base-change comparison is
an isomorphism. -/
public theorem isIso_baseChangeAlgebraHom_of_isAffine : IsIso (baseChangeAlgebraHom h X) := by
  have hl : pushforwardBaseChangeMap h X ≫ baseChangeAlgebraInv h X =
      (algebraPullbackMap h).app (pushforwardAlgebra X.hom) :=
    (isPushout_pushforwardBaseChangeMap h X).inl_desc _ _ _
  have hr : (pushforwardAlgebra ((Over.pullback h).obj X).hom).hom ≫
      baseChangeAlgebraInv h X = ((algebraPullback h).obj (pushforwardAlgebra X.hom)).hom :=
    (isPushout_pushforwardBaseChangeMap h X).inr_desc _ _ _
  refine ⟨Under.homMk (baseChangeAlgebraInv h X) hr, Under.UnderMorphism.ext ?_,
    Under.UnderMorphism.ext ?_⟩
  · show (baseChangeAlgebraHom h X).right ≫ baseChangeAlgebraInv h X = 𝟙 _
    refine (algebraPullback_isPushout h (pushforwardAlgebra X.hom)).hom_ext ?_ ?_
    · exact comp_comp_eq_comp_id _ _ _ (algebraPullbackMap_comp_baseChangeAlgebraHom h X) hl
    · exact comp_comp_eq_comp_id _ _ _ (Under.w (baseChangeAlgebraHom h X)) hr
  · show baseChangeAlgebraInv h X ≫ (baseChangeAlgebraHom h X).right = 𝟙 _
    refine (isPushout_pushforwardBaseChangeMap h X).hom_ext ?_ ?_
    · exact comp_comp_eq_comp_id _ _ _ hl (algebraPullbackMap_comp_baseChangeAlgebraHom h X)
    · exact comp_comp_eq_comp_id _ _ _ hr (Under.w (baseChangeAlgebraHom h X))

end

/-! ### Base change of algebras is pseudofunctorial -/

/-- **Base change of algebra sheaves is pseudofunctorial.** For `j : U ⟶ T` and `g : T ⟶ S` the
base change along `j ≫ g` is the base change along `g` followed by the base change along `j`.

Both functors are left adjoint to the same functor: direct image of algebra sheaves is
*equal* on the nose to its composite, `algebraPushforward j ⋙ algebraPushforward g =
algebraPushforward (j ≫ g)`, because the direct image of sheaves of rings is precomposition
with the inverse image of opens and the comorphism of a composite is the composite of the
comorphisms.  No pushout is computed.

This is recorded here because it is the step by which the general case of Stacks Tag 01LX part
(2) reduces to the case of a morphism of affine schemes proved above: for `j` the inclusion of an
affine open of `T` whose image lies in an affine open `ι : V ⟶ S` of `S`, writing `j ≫ g` also as
`g' ≫ ι` identifies the restriction to `U` of the base change along `g` with the base change
along the morphism of affine schemes `g' : U ⟶ V` of the restriction of the algebra to `V`. -/
public noncomputable def algebraPullbackComp {U T S : Scheme.{u}} (j : U ⟶ T) (g : T ⟶ S) :
    algebraPullback (j ≫ g) ≅ algebraPullback g ⋙ algebraPullback j :=
  Adjunction.leftAdjointUniq (algebraPullbackPushforwardAdjunction (j ≫ g))
    ((algebraPullbackPushforwardAdjunction g).comp (algebraPullbackPushforwardAdjunction j))

/-- **Stacks Tag 01LX part (2) for a morphism of affine schemes.** The base change along a
morphism of affine schemes of a quasi-coherent sheaf of commutative `𝒪_S`-algebras is a
quasi-coherent sheaf of commutative `𝒪_T`-algebras. -/
public theorem isQuasicoherent_algebraPullback_of_isAffine [IsAffine S] [IsAffine T]
    (A : Stacks.RelativeSpec.AlgebraSheaf.{u} S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent ((algebraPullback h).obj A) :=
  have : IsAffineHom (Over.mk (relativeSpecToBase A)).hom := isAffineHom_relativeSpecToBase A
  isQuasicoherent_algebraPullback h A
    (isIso_baseChangeAlgebraHom_of_isAffine h (Over.mk (relativeSpecToBase A)))

end Stacks.AffineAlgebraEquivalence

end
