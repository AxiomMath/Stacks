module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestrictionComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestrictionComposition

/-!
# The direct-image comparison maps under the identification of Stacks 075D (3), at any universe

Let `G : 𝒴 ⥤ 𝒳` be a strictly presented 1-morphism of categories fibred in groupoids over the big
fppf category of `S`, let `F` be an étale sheaf of sets on `𝒳` and `ψ : y' ⟶ y` an arrow of `𝒴`.
**Stacks 075D** part (3) identifies the restriction at `y` of `G^{-1}F` with the restriction of
`F` at `G y` (`AlgebraicGeometry.Stack.restrictToSmallEtaleInverseImageIso`, for sheaves with
values in any `Type t`), and part (4) says the comparison maps match under that identification
(`AlgebraicGeometry.Stack.restrictionInverseImageComparison_comp_inverseImageIso`).

Part (4) is stated for the comparison maps of **Stacks 06W3**, out of the inverse image of
sheaves, which are only formed for sheaves with values in `Type (max (u + 1) t)`. This file
proves the corresponding statement for the comparison maps of **Stacks 06W2**, into the direct
image, for sheaves with values in an arbitrary universe `Type t`: this is the form needed for
sheaves of modules whose sections live in the universe of the schemes.

## Main results

* `AlgebraicGeometry.Stack.restrictionPushforwardComparison_comp`: the comparison map of
  **Stacks 06W2** commutes with postcomposition by any functor.
* `AlgebraicGeometry.Stack.restrictToSmallEtaleInverseImageIso_hom_uliftFunctor`: the
  identification of **Stacks 075D** part (3) commutes with lifting the universe of the values.
* `AlgebraicGeometry.Stack.inverseImageIso_hom_comp_restrictionPushforwardComparison`: the
  direct-image comparison maps of `G^{-1}F` at `ψ` and of `F` at `G ψ` match under the
  identification of **Stacks 075D** part (3), for sheaves of sets in any universe.

## Implementation notes

The last statement is the direct-image transpose of **Stacks 075D** part (4). It is deduced from
that part, applied to the universe lift `F ⋙ uliftFunctor.{u + 1}` of `F`: transposing both
sides of part (4) along the inverse image–direct image adjunction of the small étale sites gives
the direct-image square for the lift, and the two lemmas above identify that square with the
lift of the square for `F`, from which the square for `F` follows because `ULift.down` is
injective.

## References

* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
* [Stacks Project, Tag 06W3](https://stacks.math.columbia.edu/tag/06W3)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w v' w' t s t' s'

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison map of **Stacks 06W2** commutes with postcomposition by a functor `K`: on each
small étale object both are restriction of the presheaf along the same arrow of `𝒳`. -/
theorem restrictionPushforwardComparison_comp {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    {A : Type t} [Category.{s} A] {A' : Type t'} [Category.{s'} A'] (F : 𝒳ᵒᵖ ⥤ A)
    (K : A ⥤ A') :
    restrictionPushforwardComparison B E h S hS p hp φ (F ⋙ K) =
      Functor.whiskerRight (restrictionPushforwardComparison B E h S hS p hp φ F) K := by
  ext W
  induction W with | op W => ?_
  obtain ⟨φ', hfac, hproj⟩ := exists_restrictionComparisonLift B E h S hS p hp φ W
  rw [Functor.whiskerRight_app,
    restrictionPushforwardComparison_app B E h S hS p hp φ (F ⋙ K) W φ' hfac hproj,
    restrictionPushforwardComparison_app B E h S hS p hp φ F W φ' hfac hproj]
  rfl

/-- The identification of **Stacks 075D** part (3) commutes with lifting the universe of the values
of the sheaf: on each small étale object both are restriction along the unique comparison arrow of
`AlgebraicGeometry.Stack.existsUnique_inverseImageComparisonLift`. -/
theorem restrictToSmallEtaleInverseImageIso_hom_uliftFunctor {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {𝒴 : Type v'} [Category.{w'} 𝒴] (G : 𝒴 ⥤ 𝒳) (hGp : (G ⋙ p).IsFiberedInGroupoids)
    (hG : (G ⋙ p).IsFibredOneMorphism p G) (y : 𝒴)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type t)) :
    (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y
        ((sheafCompose (associatedTopology B S hS p (etaleTopology B))
          uliftFunctor.{t', t}).obj F)).hom =
      Functor.whiskerRight (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y F).hom
        uliftFunctor.{t', t} := by
  ext W
  induction W with | op W => ?_
  obtain ⟨φ, ⟨hcart, hbase⟩, -⟩ :=
    existsUnique_inverseImageComparisonLift B E h S hS p hp G hGp y W
  rw [Functor.whiskerRight_app,
    restrictToSmallEtaleInverseImageIso_app B E h S hS p hp G hGp hG y _ W φ hcart hbase,
    restrictToSmallEtaleInverseImageIso_app B E h S hS p hp G hGp hG y F W φ hcart hbase]
  rfl

/-- **The direct-image comparison maps match under the identification of Stacks 075D (3)**, for
an étale sheaf of sets in any universe: for an arrow `ψ : y' ⟶ y` of `𝒴`, the comparison map of
**Stacks 06W2** for `F` at `G ψ`, preceded by the identification at `y`, is the comparison map for
`G^{-1}F` at `ψ` followed by the identification at `y'`.

This is the direct-image transpose of **Stacks 075D** part (4),
`AlgebraicGeometry.Stack.restrictionInverseImageComparison_comp_inverseImageIso`, which is stated
for sheaves with values in `Type (max (u + 1) t)` only. It is deduced from that statement applied
to the universe lift of `F`; see the implementation notes of this file. -/
theorem inverseImageIso_hom_comp_restrictionPushforwardComparison
    {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {𝒴 : Type v'} [Category.{w'} 𝒴] (G : 𝒴 ⥤ 𝒳) (hGp : (G ⋙ p).IsFiberedInGroupoids)
    (hG : (G ⋙ p).IsFibredOneMorphism p G) {y' y : 𝒴} (ψ : y' ⟶ y)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type t)) :
    letI : (G ⋙ p).IsFibered := hGp.isFibered
    letI : p.IsFibered := hp.isFibered
    letI := (hG.isContinuous_and_isCocontinuous_inheritedTopology
      ((etaleTopology B).over (B.obj hS))).1
    (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y F).hom ≫
        restrictionPushforwardComparison B E h S hS p hp (G.map ψ) F.obj =
      restrictionPushforwardComparison B E h S hS (G ⋙ p) hGp ψ
          ((G.sheafPushforwardContinuous (Type t)
            (associatedTopology B S hS (G ⋙ p) (etaleTopology B))
            (associatedTopology B S hS p (etaleTopology B))).obj F).obj ≫
        Functor.whiskerLeft
          (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS (G ⋙ p) ψ)).op
          (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y' F).hom := by
  let : (G ⋙ p).IsFibered := hGp.isFibered
  let : p.IsFibered := hp.isFibered
  let := (hG.isContinuous_and_isCocontinuous_inheritedTopology
    ((etaleTopology B).over (B.obj hS))).1
  let F₁ := (sheafCompose (associatedTopology B S hS p (etaleTopology B))
    uliftFunctor.{u + 1, t}).obj F
  have hbase := restrictionInverseImageComparison_comp_inverseImageIso B E h S hS p hp G hGp hG
    ψ F₁
  let b := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p (G.map ψ))
  let Jy := SmallEtale.topology E (p.obj (G.obj y)).left.1 (contains_base B E h S hS p (G.obj y))
  let Jy' := SmallEtale.topology E (p.obj (G.obj y')).left.1
    (contains_base B E h S hS p (G.obj y'))
  let adj := b.sheafAdjunctionContinuous (Type (max (u + 1) t)) Jy Jy'
  let F₁' := (G.sheafPushforwardContinuous (Type (max (u + 1) t))
    (associatedTopology B S hS (G ⋙ p) (etaleTopology B))
    (associatedTopology B S hS p (etaleTopology B))).obj F₁
  let Iy := restrictToSmallEtaleSheaf B E h S hS (G ⋙ p) hGp y F₁'
  let Iy' := restrictToSmallEtaleSheaf B E h S hS (G ⋙ p) hGp y' F₁'
  let Fy := restrictToSmallEtaleSheaf B E h S hS p hp (G.obj y) F₁
  let Fy' := restrictToSmallEtaleSheaf B E h S hS p hp (G.obj y') F₁
  let iy := restrictToSmallEtaleSheafInverseImageIso B E h S hS p hp G hGp hG y F₁
  let iy' := restrictToSmallEtaleSheafInverseImageIso B E h S hS p hp G hGp hG y' F₁
  let cX : Fy ⟶ (b.sheafPushforwardContinuous (Type (max (u + 1) t)) Jy Jy').obj Fy' :=
    Sheaf.homEquiv.symm (restrictionPushforwardComparison B E h S hS p hp (G.map ψ) F₁.obj)
  let cI : Iy ⟶ (b.sheafPushforwardContinuous (Type (max (u + 1) t)) Jy Jy').obj Iy' :=
    Sheaf.homEquiv.symm (restrictionPushforwardComparison B E h S hS (G ⋙ p) hGp ψ F₁'.obj)
  have h1 : (adj.homEquiv Iy Fy')
        ((b.sheafPullback (Type (max (u + 1) t)) Jy Jy').map iy.hom ≫
          (adj.homEquiv Fy Fy').symm cX) =
      (adj.homEquiv Iy Fy') ((adj.homEquiv Iy Iy').symm cI ≫ iy'.hom) :=
    congrArg (adj.homEquiv Iy Fy') hbase
  rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply, adj.homEquiv_naturality_right,
    Equiv.apply_symm_apply] at h1
  have h2 := congrArg (sheafToPresheaf Jy (Type (max (u + 1) t))).map h1
  simp only [Functor.map_comp] at h2
  have e : ∀ y₀ : 𝒴, (sheafToPresheaf (SmallEtale.topology E (p.obj (G.obj y₀)).left.1
        (contains_base B E h S hS p (G.obj y₀))) _).map
        (restrictToSmallEtaleSheafInverseImageIso B E h S hS p hp G hGp hG y₀ F₁).hom =
      Functor.whiskerRight (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y₀ F).hom
        uliftFunctor.{u + 1, t} := fun y₀ =>
    ((fullyFaithfulSheafToPresheaf _ _).map_preimage _).trans
      (restrictToSmallEtaleInverseImageIso_hom_uliftFunctor B E h S hS p hp G hGp hG y₀ F)
  have e2 : (sheafToPresheaf Jy (Type (max (u + 1) t))).map cX =
      Functor.whiskerRight (restrictionPushforwardComparison B E h S hS p hp (G.map ψ) F.obj)
        uliftFunctor.{u + 1, t} :=
    ((fullyFaithfulSheafToPresheaf _ _).map_preimage _).trans
      (restrictionPushforwardComparison_comp B E h S hS p hp (G.map ψ) F.obj
        uliftFunctor.{u + 1, t})
  have e3 : (sheafToPresheaf Jy (Type (max (u + 1) t))).map cI =
      Functor.whiskerRight (restrictionPushforwardComparison B E h S hS (G ⋙ p) hGp ψ
          ((G.sheafPushforwardContinuous (Type t)
            (associatedTopology B S hS (G ⋙ p) (etaleTopology B))
            (associatedTopology B S hS p (etaleTopology B))).obj F).obj)
        uliftFunctor.{u + 1, t} :=
    ((fullyFaithfulSheafToPresheaf _ _).map_preimage _).trans
      (restrictionPushforwardComparison_comp B E h S hS (G ⋙ p) hGp ψ (G.op ⋙ F.obj)
        uliftFunctor.{u + 1, t})
  have e4 : (sheafToPresheaf _ _).map ((b.sheafPushforwardContinuous _ Jy Jy').map iy'.hom) =
      _ :=
    congrArg (Functor.whiskerLeft b.op) (e y')
  rw [e y, e2, e3, e4] at h2
  ext W x
  exact congrArg (fun k => (k.app W (ULift.up.{u + 1} x)).down) h2

end AlgebraicGeometry.Stack

end
