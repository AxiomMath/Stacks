module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftDerivationAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# Infinitesimal deformations of maps of algebraic spaces and étale localization

Let `S` be a scheme. Consider a commutative diagram of first order thickenings of algebraic
spaces over `S`
```
(T₂ ⊂ T₂') --(a₂, a₂')--> (X₂ ⊂ X₂')        X₂' --> B₂
   |                          |               |       |
 (h, h')                   (f, f')            v       v
   v                          v              X₁' --> B₁
(T₁ ⊂ T₁') --(a₁, a₁')--> (X₁ ⊂ X₁')
```
together with the commutative square of structure morphisms on the right, and assume
`X₂ ⟶ X₁` and `B₂ ⟶ B₁` are étale. [Stacks Project, Tag 0CK8] transports an `𝒪_{T₁}`-linear
map `θ₁ : a₁^*Ω_{X₁/B₁} ⟶ 𝒞_{T₁/T₁'}` to the composite
```
θ₂ : a₂^*Ω_{X₂/B₂} = h^*a₁^*Ω_{X₁/B₁} --h^*θ₁--> h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}
```
and asserts that the square
```
θ₂ ⬝ a₂' : T₂' ⟶ X₂'      and     θ₁ ⬝ a₁' : T₁' ⟶ X₁'
```
commutes against `h'` and `f'`, that is `(θ₂ ⬝ a₂') ≫ f' = h' ≫ (θ₁ ⬝ a₁')`, the two actions
being those of [Stacks Project, Tag 0CK6].

This file constructs pieces of that statement in the vocabulary in which
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftDerivationAction.lean` carries Tag 0CK6:
the lifts of `a` over an object of the spaces-étale site are
`AlgebraicGeometry.Space.liftSections`, the sheaf (061B) of [Stacks Project, Tag 061A], and the
action `θ ⬝ a'` is `AlgebraicGeometry.Space.LiftDerivationAction.addAction`, whose datum is the
difference of two lifts as a section of an abstract sheaf of abelian groups. The tag itself is
proved as `AlgebraicGeometry.Space.derivationMove_comp_of_etale` in
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftEtaleCompatibility.lean`.

## Main definitions

* `AlgebraicGeometry.Space.pushLiftSections`: the map on lifts induced by `(f, f')`, sending a
  lift `b' : U' ⟶ X₂'` of `a₂` to the lift `b' ≫ f' : U' ⟶ X₁'` of `a₂ ≫ f`.
* `AlgebraicGeometry.Space.pullLiftSections`: the map on lifts induced by `(h, h')`, sending a
  lift `c' : T₁' ⟶ X₁'` of `a₁` to the lift `h' ≫ c' : T₂' ⟶ X₁'` of `a₂ ≫ f = h ≫ a₁`.
* `AlgebraicGeometry.Space.localizedLiftDerivation`: the transported datum `θ₂` of the source,
  *constructed* from `θ₁` as `φsec (ψ θ₁)`, where `ψ` is the source's `h^*(-)` followed by the
  conormal transport and `φsec` is a right inverse of the identification `φ` of
  [Stacks Project, Tag 04CU] read on the acting groups.

## Main results

* `AlgebraicGeometry.Space.isLiftOver_comp_of_thickeningHom`: composing a lift of `a₂` with
  `f'` is a lift of `a₂ ≫ f`. This is the content of the right-hand square of the source
  together with the square of base structure morphisms.
* `AlgebraicGeometry.Space.isLiftOver_precomp_of_thickeningHom`: precomposing a lift of `a₁`
  with a morphism over `h'` is a lift of `a₂ ≫ f`. This is the content of the left-hand square
  of the source together with `a₂ ≫ f = h ≫ a₁`.

## Duplicate spellings

`IsThickening` has several unrelated declarations in this development: this file uses
`AlgebraicGeometry.Space.IsThickening`, the predicate on a closed subfunctor of an *algebraic
space* of [Stacks Project, Tag 05ZK], not `StacksDraft.Stacks.Thickenings.IsThickening` for
schemes, nor `AlgebraicGeometry.Space.IsThickeningHom` for a morphism of algebraic spaces, nor
the ringed-space and ringed-topos predicates of the same name. Likewise the terminal object of
the spaces-étale site is spelled `AlgebraicGeometry.Space.SpacesEtale.idObj`; the other
spelling, `AlgebraicGeometry.Space.SpacesEtale.final`, is the same object.

## References

* [Stacks Project, Tag 0CK8](https://stacks.math.columbia.edu/tag/0CK8)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 04BY](https://stacks.math.columbia.edu/tag/04BY)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

section EtaleLocalization

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
  {T₁' T₂' X₁' X₂' B₁ B₂ : AlgebraicSpaces C S hS}
  {GT₁ : Subfunctor T₁'.obj} {GT₂ : Subfunctor T₂'.obj}
  {GX₁ : Subfunctor X₁'.obj} {GX₂ : Subfunctor X₂'.obj}

/-! ### Pushing a lift forward along the right-hand square -/

/-- **Composing a lift with `f'` is a lift.** Let `(f, f') : (X₂ ⊂ X₂') ⟶ (X₁ ⊂ X₁')` be a
morphism of thickenings, let `q₁ : X₁' ⟶ B₁`, `q₂ : X₂' ⟶ B₂` and `ε : B₂ ⟶ B₁` form a
commutative square with `f'`, and let `rT₁ : T₁' ⟶ B₁`, `rT₂ : T₂' ⟶ B₂` be structure
morphisms with `rT₂ ≫ ε = h' ≫ rT₁`. Then for an algebraic space `U'` étale over `T₂'`, a
morphism `b' : U' ⟶ X₂'` which is a lift of `a₂` over `B₂` composes with `f'` to a lift of
`a₂ ≫ f` over `B₁`, taken along `h' ≫ rT₁`. -/
theorem isLiftOver_comp_of_thickeningHom (hT₂ : IsThickening C S hS T₂' GT₂)
    (hX₁ : IsThickening C S hS X₁' GX₁) (hX₂ : IsThickening C S hS X₂' GX₂)
    (h' : T₂' ⟶ T₁') (f : IsThickening.space C S hS hX₂ ⟶ IsThickening.space C S hS hX₁)
    (f' : X₂' ⟶ X₁') (a₂ : IsThickening.space C S hS hT₂ ⟶ IsThickening.space C S hS hX₂)
    (q₁ : X₁' ⟶ B₁) (q₂ : X₂' ⟶ B₂) (ε : B₂ ⟶ B₁) (rT₁ : T₁' ⟶ B₁) (rT₂ : T₂' ⟶ B₂)
    (cX : IsThickening.inclusion C S hS hX₂ ≫ f' = f ≫ IsThickening.inclusion C S hS hX₁)
    (cB : f' ≫ q₁ = q₂ ≫ ε) (cr : rT₂ ≫ ε = h' ≫ rT₁)
    (U' : SpacesEtale C S hS T₂')
    (b' : (SpacesEtale.toSpaces C S hS T₂').obj U' ⟶ X₂')
    (hb' : IsLiftOver C S hS hT₂ hX₂ rT₂ q₂ a₂ U' b') :
    IsLiftOver C S hS hT₂ hX₁ (h' ≫ rT₁) q₁ (a₂ ≫ f) U' (b' ≫ f') := by
  obtain ⟨h1, h2⟩ := hb'
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, cB, ← Category.assoc, h1, Category.assoc, cr]
  · rw [← Category.assoc, h2]
    simp only [Category.assoc]
    rw [cX]

/-- **The map on lifts induced by `(f, f')`.** A lift of `a₂` over an algebraic space `U'`
étale over `T₂'` is sent to the lift `b' ≫ f'` of `a₂ ≫ f`, by
`AlgebraicGeometry.Space.isLiftOver_comp_of_thickeningHom`. This is the left-hand vertical map
of the conclusion of [Stacks Project, Tag 0CK8], read on sections of the sheaf (061B). -/
noncomputable def pushLiftSections (hT₂ : IsThickening C S hS T₂' GT₂)
    (hX₁ : IsThickening C S hS X₁' GX₁) (hX₂ : IsThickening C S hS X₂' GX₂)
    (h' : T₂' ⟶ T₁') (f : IsThickening.space C S hS hX₂ ⟶ IsThickening.space C S hS hX₁)
    (f' : X₂' ⟶ X₁') (a₂ : IsThickening.space C S hS hT₂ ⟶ IsThickening.space C S hS hX₂)
    (q₁ : X₁' ⟶ B₁) (q₂ : X₂' ⟶ B₂) (ε : B₂ ⟶ B₁) (rT₁ : T₁' ⟶ B₁) (rT₂ : T₂' ⟶ B₂)
    (cX : IsThickening.inclusion C S hS hX₂ ≫ f' = f ≫ IsThickening.inclusion C S hS hX₁)
    (cB : f' ≫ q₁ = q₂ ≫ ε) (cr : rT₂ ≫ ε = h' ≫ rT₁)
    (U' : (SpacesEtale C S hS T₂')ᵒᵖ)
    (x : liftSections C S hS hT₂ hX₂ rT₂ q₂ a₂ U') :
    liftSections C S hS hT₂ hX₁ (h' ≫ rT₁) q₁ (a₂ ≫ f) U' :=
  ⟨x.1 ≫ f',
    isLiftOver_comp_of_thickeningHom C S hS hT₂ hX₁ hX₂ h' f f' a₂ q₁ q₂ ε rT₁ rT₂ cX cB cr
      (unop U') _ x.2⟩

/-! ### Pulling a lift back along the left-hand square -/

/-- **Precomposing a lift with a morphism over `h'` is a lift.** Let
`(h, h') : (T₂ ⊂ T₂') ⟶ (T₁ ⊂ T₁')` be a morphism of thickenings, let `a₁`, `a₂` and `f`
satisfy `a₂ ≫ f = h ≫ a₁`, and let `W₁`, `W₂` be objects of the spaces-étale sites of `T₁'`
and of `T₂'` joined by a morphism `w` over `h'`. Then a morphism
`c' : W₁ ⟶ X₁'` which is a lift of `a₁` over `B₁` precomposes with `w` to a lift of `a₂ ≫ f`
over `B₁`, taken along `h' ≫ rT₁`. -/
theorem isLiftOver_precomp_of_thickeningHom (hT₁ : IsThickening C S hS T₁' GT₁)
    (hT₂ : IsThickening C S hS T₂' GT₂) (hX₁ : IsThickening C S hS X₁' GX₁)
    (hX₂ : IsThickening C S hS X₂' GX₂)
    (h : IsThickening.space C S hS hT₂ ⟶ IsThickening.space C S hS hT₁) (h' : T₂' ⟶ T₁')
    (f : IsThickening.space C S hS hX₂ ⟶ IsThickening.space C S hS hX₁)
    (a₁ : IsThickening.space C S hS hT₁ ⟶ IsThickening.space C S hS hX₁)
    (a₂ : IsThickening.space C S hS hT₂ ⟶ IsThickening.space C S hS hX₂)
    (q₁ : X₁' ⟶ B₁) (rT₁ : T₁' ⟶ B₁)
    (cT : IsThickening.inclusion C S hS hT₂ ≫ h' = h ≫ IsThickening.inclusion C S hS hT₁)
    (ca : a₂ ≫ f = h ≫ a₁)
    (W₁ : SpacesEtale C S hS T₁') (W₂ : SpacesEtale C S hS T₂')
    (w : (SpacesEtale.toSpaces C S hS T₂').obj W₂ ⟶ (SpacesEtale.toSpaces C S hS T₁').obj W₁)
    (cw : w ≫ W₁.1.hom = W₂.1.hom ≫ h')
    (c' : (SpacesEtale.toSpaces C S hS T₁').obj W₁ ⟶ X₁')
    (hc' : IsLiftOver C S hS hT₁ hX₁ rT₁ q₁ a₁ W₁ c') :
    IsLiftOver C S hS hT₂ hX₁ (h' ≫ rT₁) q₁ (a₂ ≫ f) W₂ (w ≫ c') := by
  obtain ⟨h1, h2⟩ := hc'
  have sq₁ := (spacesBaseChange C S hS (IsThickening.inclusion C S hS hT₁)).isPullback W₁
  have sq₂ := (spacesBaseChange C S hS (IsThickening.inclusion C S hS hT₂)).isPullback W₂
  have h1' : c' ≫ q₁ = W₁.1.hom ≫ rT₁ := h1
  have h2' :
      (spacesBaseChange C S hS (IsThickening.inclusion C S hS hT₁)).projection.app W₁ ≫ c' =
        ((spacesBaseChange C S hS (IsThickening.inclusion C S hS hT₁)).functor.obj W₁).1.hom ≫
          a₁ ≫ IsThickening.inclusion C S hS hX₁ := h2
  refine ⟨?_, ?_⟩
  · change (w ≫ c') ≫ q₁ = W₂.1.hom ≫ h' ≫ rT₁
    rw [Category.assoc, h1', ← Category.assoc, cw, Category.assoc]
  · change (spacesBaseChange C S hS (IsThickening.inclusion C S hS hT₂)).projection.app W₂ ≫
        (w ≫ c') =
      ((spacesBaseChange C S hS (IsThickening.inclusion C S hS hT₂)).functor.obj W₂).1.hom ≫
        (a₂ ≫ f) ≫ IsThickening.inclusion C S hS hX₁
    have hv : ((spacesBaseChange C S hS (IsThickening.inclusion C S hS hT₂)).projection.app W₂ ≫
          w) ≫ W₁.1.hom =
        (((spacesBaseChange C S hS (IsThickening.inclusion C S hS hT₂)).functor.obj W₂).1.hom ≫
          h) ≫ IsThickening.inclusion C S hS hT₁ := by
      rw [Category.assoc, cw, ← Category.assoc, sq₂.w, Category.assoc, cT, Category.assoc]
    have hfst := sq₁.lift_fst _ _ hv
    have hsnd := sq₁.lift_snd _ _ hv
    rw [← Category.assoc, ← hfst, Category.assoc, h2', ← Category.assoc, hsnd, ca]
    simp only [Category.assoc]

/-- **The map on lifts induced by `(h, h')`.** A lift of `a₁` over `W₁` is sent to the lift
`w ≫ c'` of `a₂ ≫ f` over `W₂`, by
`AlgebraicGeometry.Space.isLiftOver_precomp_of_thickeningHom`. This is the right-hand vertical
map of the conclusion of [Stacks Project, Tag 0CK8], read on sections of the sheaf (061B). -/
noncomputable def pullLiftSections (hT₁ : IsThickening C S hS T₁' GT₁)
    (hT₂ : IsThickening C S hS T₂' GT₂) (hX₁ : IsThickening C S hS X₁' GX₁)
    (hX₂ : IsThickening C S hS X₂' GX₂)
    (h : IsThickening.space C S hS hT₂ ⟶ IsThickening.space C S hS hT₁) (h' : T₂' ⟶ T₁')
    (f : IsThickening.space C S hS hX₂ ⟶ IsThickening.space C S hS hX₁)
    (a₁ : IsThickening.space C S hS hT₁ ⟶ IsThickening.space C S hS hX₁)
    (a₂ : IsThickening.space C S hS hT₂ ⟶ IsThickening.space C S hS hX₂)
    (q₁ : X₁' ⟶ B₁) (rT₁ : T₁' ⟶ B₁)
    (cT : IsThickening.inclusion C S hS hT₂ ≫ h' = h ≫ IsThickening.inclusion C S hS hT₁)
    (ca : a₂ ≫ f = h ≫ a₁)
    (W₁ : SpacesEtale C S hS T₁') (W₂ : SpacesEtale C S hS T₂')
    (w : (SpacesEtale.toSpaces C S hS T₂').obj W₂ ⟶ (SpacesEtale.toSpaces C S hS T₁').obj W₁)
    (cw : w ≫ W₁.1.hom = W₂.1.hom ≫ h')
    (x : liftSections C S hS hT₁ hX₁ rT₁ q₁ a₁ (op W₁)) :
    liftSections C S hS hT₂ hX₁ (h' ≫ rT₁) q₁ (a₂ ≫ f) (op W₂) :=
  ⟨w ≫ x.1,
    isLiftOver_precomp_of_thickeningHom C S hS hT₁ hT₂ hX₁ hX₂ h h' f a₁ a₂ q₁ rT₁ cT ca
      W₁ W₂ w cw _ x.2⟩

/-- The identity of an algebraic space, as the structure morphism of the terminal object of its
spaces-étale site, commutes with any morphism: the datum needed to read a morphism `h'` of
algebraic spaces as a morphism of terminal objects over it. -/
theorem comm_idObj_hom (h' : T₂' ⟶ T₁') :
    h' ≫ (SpacesEtale.idObj C S hS T₁').1.hom =
      (SpacesEtale.idObj C S hS T₂').1.hom ≫ h' := by
  change h' ≫ 𝟙 T₁' = 𝟙 T₂' ≫ h'
  simp

/-! ### The transported derivation datum -/

/-- **The transported datum `θ₂` of [Stacks Project, Tag 0CK8].** The source defines `θ₂` as
the composite
`a₂^*Ω_{X₂/B₂} = h^*a₁^*Ω_{X₁/B₁} --h^*θ₁--> h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}`. Read on the acting
groups, `ψ` is that composite out of `θ₁` and `φ` is the equality sign, the identification of
[Stacks Project, Tag 04CU]; `θ₂` is the unique preimage of `ψ θ₁` under `φ`, computed through a
section `φsec` of `φ`. -/
noncomputable def localizedLiftDerivation
    (Θ₁ : (SpacesEtale C S hS T₁')ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (Θ₂ Θ₃ : (SpacesEtale C S hS T₂')ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (W₁ : (SpacesEtale C S hS T₁')ᵒᵖ) (W₂ : (SpacesEtale C S hS T₂')ᵒᵖ)
    (φsec : Θ₃.obj W₂ ⟶ Θ₂.obj W₂) (ψ : Θ₁.obj W₁ ⟶ Θ₃.obj W₂) (θ₁ : Θ₁.obj W₁) :
    Θ₂.obj W₂ :=
  φsec.hom (ψ.hom θ₁)

/-! ### Equivariance of the two maps on lifts -/

section Equivariance

variable (hT₁ : IsThickening C S hS T₁' GT₁) (hT₂ : IsThickening C S hS T₂' GT₂)
  (hX₁ : IsThickening C S hS X₁' GX₁) (hX₂ : IsThickening C S hS X₂' GX₂)
  (h : IsThickening.space C S hS hT₂ ⟶ IsThickening.space C S hS hT₁) (h' : T₂' ⟶ T₁')
  (f : IsThickening.space C S hS hX₂ ⟶ IsThickening.space C S hS hX₁) (f' : X₂' ⟶ X₁')
  (a₁ : IsThickening.space C S hS hT₁ ⟶ IsThickening.space C S hS hX₁)
  (a₂ : IsThickening.space C S hS hT₂ ⟶ IsThickening.space C S hS hX₂)
  (q₁ : X₁' ⟶ B₁) (q₂ : X₂' ⟶ B₂) (ε : B₂ ⟶ B₁) (rT₁ : T₁' ⟶ B₁) (rT₂ : T₂' ⟶ B₂)
  (Θ₁ : (SpacesEtale C S hS T₁')ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  (Θ₂ Θ₃ : (SpacesEtale C S hS T₂')ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- **The map on lifts induced by `(f, f')` is equivariant.** If the difference of two lifts is
natural in that map, with comparison `φ` of the acting groups, then translating by `θ` and
pushing forward agree with pushing forward and translating by `φ θ`.

This is `Deformation.map_vadd_of_natural_difference` applied to
`AlgebraicGeometry.Space.pushLiftSections`; the simple transitivity of the action in the mixed
situation is what makes the deduction possible. -/
theorem vadd_pushLiftSections
    (cX : IsThickening.inclusion C S hS hX₂ ≫ f' = f ≫ IsThickening.inclusion C S hS hX₁)
    (cB : f' ≫ q₁ = q₂ ≫ ε) (cr : rT₂ ≫ ε = h' ≫ rT₁)
    (act₂ : LiftDerivationAction C S hS hT₂ hX₂ rT₂ q₂ a₂ Θ₂)
    (act₃ : LiftDerivationAction C S hS hT₂ hX₁ (h' ≫ rT₁) q₁ (a₂ ≫ f) Θ₃)
    (U' : (SpacesEtale C S hS T₂')ᵒᵖ) (φ : Θ₂.obj U' ⟶ Θ₃.obj U')
    (hφ : ∀ x y : liftSections C S hS hT₂ hX₂ rT₂ q₂ a₂ U',
      act₃.diff U'
          (pushLiftSections C S hS hT₂ hX₁ hX₂ h' f f' a₂ q₁ q₂ ε rT₁ rT₂ cX cB cr U' x)
          (pushLiftSections C S hS hT₂ hX₁ hX₂ h' f f' a₂ q₁ q₂ ε rT₁ rT₂ cX cB cr U' y) =
        φ.hom (act₂.diff U' x y))
    (x : liftSections C S hS hT₂ hX₂ rT₂ q₂ a₂ U') (θ : Θ₂.obj U') :
    letI := act₂.addAction U'
    letI := act₃.addAction U'
    pushLiftSections C S hS hT₂ hX₁ hX₂ h' f f' a₂ q₁ q₂ ε rT₁ rT₂ cX cB cr U' (θ +ᵥ x) =
      φ.hom θ +ᵥ
        pushLiftSections C S hS hT₂ hX₁ hX₂ h' f f' a₂ q₁ q₂ ε rT₁ rT₂ cX cB cr U' x :=
  let := act₂.addAction U'
  let := act₃.addAction U'
  Deformation.map_vadd_of_natural_difference (act₂.diff U') (act₃.diff U') (act₂.diff_vadd U')
    (act₃.diff_vadd U') (act₃.vadd_bijective U')
    (pushLiftSections C S hS hT₂ hX₁ hX₂ h' f f' a₂ q₁ q₂ ε rT₁ rT₂ cX cB cr U')
    (fun t => φ.hom t) hφ x θ

/-- **The map on lifts induced by `(h, h')` is equivariant.** If the difference of two lifts is
natural in that map, with comparison `ψ` of the acting groups, then translating by `θ` and
pulling back agree with pulling back and translating by `ψ θ`.

This is `Deformation.map_vadd_of_natural_difference` applied to
`AlgebraicGeometry.Space.pullLiftSections`. -/
theorem vadd_pullLiftSections
    (cT : IsThickening.inclusion C S hS hT₂ ≫ h' = h ≫ IsThickening.inclusion C S hS hT₁)
    (ca : a₂ ≫ f = h ≫ a₁)
    (act₁ : LiftDerivationAction C S hS hT₁ hX₁ rT₁ q₁ a₁ Θ₁)
    (act₃ : LiftDerivationAction C S hS hT₂ hX₁ (h' ≫ rT₁) q₁ (a₂ ≫ f) Θ₃)
    (W₁ : SpacesEtale C S hS T₁') (W₂ : SpacesEtale C S hS T₂')
    (w : (SpacesEtale.toSpaces C S hS T₂').obj W₂ ⟶ (SpacesEtale.toSpaces C S hS T₁').obj W₁)
    (cw : w ≫ W₁.1.hom = W₂.1.hom ≫ h')
    (ψ : Θ₁.obj (op W₁) ⟶ Θ₃.obj (op W₂))
    (hψ : ∀ x y : liftSections C S hS hT₁ hX₁ rT₁ q₁ a₁ (op W₁),
      act₃.diff (op W₂)
          (pullLiftSections C S hS hT₁ hT₂ hX₁ hX₂ h h' f a₁ a₂ q₁ rT₁ cT ca W₁ W₂ w cw x)
          (pullLiftSections C S hS hT₁ hT₂ hX₁ hX₂ h h' f a₁ a₂ q₁ rT₁ cT ca W₁ W₂ w cw y) =
        ψ.hom (act₁.diff (op W₁) x y))
    (x : liftSections C S hS hT₁ hX₁ rT₁ q₁ a₁ (op W₁)) (θ : Θ₁.obj (op W₁)) :
    letI := act₁.addAction (op W₁)
    letI := act₃.addAction (op W₂)
    pullLiftSections C S hS hT₁ hT₂ hX₁ hX₂ h h' f a₁ a₂ q₁ rT₁ cT ca W₁ W₂ w cw (θ +ᵥ x) =
      ψ.hom θ +ᵥ
        pullLiftSections C S hS hT₁ hT₂ hX₁ hX₂ h h' f a₁ a₂ q₁ rT₁ cT ca W₁ W₂ w cw x :=
  let := act₁.addAction (op W₁)
  let := act₃.addAction (op W₂)
  Deformation.map_vadd_of_natural_difference (act₁.diff (op W₁)) (act₃.diff (op W₂))
    (act₁.diff_vadd (op W₁)) (act₃.diff_vadd (op W₂)) (act₃.vadd_bijective (op W₂))
    (pullLiftSections C S hS hT₁ hT₂ hX₁ hX₂ h h' f a₁ a₂ q₁ rT₁ cT ca W₁ W₂ w cw)
    (fun t => ψ.hom t) hψ x θ

end Equivariance

end EtaleLocalization

end AlgebraicGeometry.Space

end
