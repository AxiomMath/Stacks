module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateOfNatIsoLeft
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPullRestrictionTransition
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Restricting the push-pull of a morphism of topoi further along a factorization

Let `f : X → Z`, `g : Y → Z` and `h : Y → X` be morphisms of topoi and let
`θ : h_* f_* ≅ g_*` be an isomorphism exhibiting `g` as `f ∘ h` up to isomorphism. The unit of
the adjunction of `h` then produces a canonical transformation of the two push-pull
endofunctors of `Z`,

`f⁻¹ f_* ⟶ g⁻¹ g_*`,

which restricts a section further along `h`. It depends on the pair `(f, g)` only through `θ`,
and the point of this file is the resulting transport: replacing `f` and `g` by morphisms of
topoi with isomorphic direct images carries the transition for `(f, g, θ)` to the transition for
`(f', g', θ')`, provided `θ` and `θ'` are compatible with the two isomorphisms of direct images.

## Main definitions

* `CategoryTheory.MorphismOfTopoi.pushPullTransition`: the transition `f⁻¹ f_* ⟶ g⁻¹ g_*`, an
  instance of `Stacks.CategoryTheory.restrictionTransition` for the triangle of adjunctions of
  `f`, `g` and `h`.
* `CategoryTheory.MorphismOfTopoi.inverseImageIsoOfPushforwardIso`: the comparison
  `f⁻¹ ≅ f'⁻¹` of the inverse images of two morphisms of topoi with the same target whose
  direct images are isomorphic, by uniqueness of a left adjoint.

## Main results

* `MorphismOfTopoi.isoWhiskerRight_inverseImageIsoOfPushforwardIso_leftAdjointCompIso`, in the
  `CategoryTheory` namespace, is **the transport of the comparison of inverse images.** It says
  that the comparisons `f⁻¹ ≅ f'⁻¹` and `g⁻¹ ≅ g'⁻¹` identify the two isomorphisms
  `f⁻¹ h⁻¹ ≅ g⁻¹` and `f'⁻¹ h⁻¹ ≅ g'⁻¹` that `θ` and `θ'` produce.
* `CategoryTheory.MorphismOfTopoi.pushPullTransition_congr`: **the transport of the
  transition.** The transition for `(f, g, θ)` and the transition for `(f', g', θ')` agree under
  the isomorphisms of push-pull functors that `α` and `β` induce.
* `Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_inv`: the piece of conjugate calculus
  the transport needs besides `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_right`, namely
  that the inverse of the comparison of two left adjoints of the same functor conjugates to the
  identity.
* `Stacks.CategoryTheory.rightAdjointUniq_ofNatIsoLeft_leftAdjointCompIso_inv`: for a triangle
  of adjunctions whose comparison of left adjoints is the one
  `CategoryTheory.Adjunction.leftAdjointCompIso` builds from an isomorphism `e` of the composite
  right adjoints, the companion comparison of right adjoints is `e` itself. This is what puts
  `θ` back into a formula written through `CategoryTheory.Adjunction.rightAdjointUniq`.
* `Stacks.CategoryTheory.leftAdjointCompIso_congr_middle` and
  `Stacks.CategoryTheory.restrictionTransition_congr_middle`: **the transition does not depend on
  which left adjoint of the relocalization is used.** Replacing the middle adjunction of the
  triangle by another one with the same right adjoint changes
  `CategoryTheory.Adjunction.leftAdjointCompIso` by the comparison of the two left adjoints, and
  leaves `Stacks.CategoryTheory.restrictionTransition` unchanged.

## Implementation notes

Everything is mate calculus. The general construction of the transition is
`Stacks.CategoryTheory.restrictionTransition` and is not repeated here: `pushPullTransition` is
that construction for the triangle of adjunctions of `f`, `g` and `h`, with the comparison of
left adjoints taken to be the one Mathlib's
`CategoryTheory.Adjunction.leftAdjointCompIso` builds from `θ`. Everything below goes through
`CategoryTheory.MorphismOfTopoi.pushPullTransition_app`, which is the only place the definition
is unfolded.

The transport of the comparison of inverse images is proved by applying the injective map
`CategoryTheory.conjugateEquiv` to the inverses of the two isomorphisms. Both sides then split
by `CategoryTheory.conjugateEquiv_comp`, and the four resulting factors are computed by
`CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv`,
`CategoryTheory.conjugateEquiv_whiskerRight` and the two conjugation formulas for
`CategoryTheory.Adjunction.leftAdjointUniq` recorded at the head of this file; the compatibility
hypothesis is exactly what remains.

The transport of the transition itself is then a componentwise computation: the naturality of the
unit of `h`, of `α` and of `θ`, the compatibility hypothesis, and the transport of the comparison
of inverse images, in that order.

The independence of the transition from the middle adjunction is what reconciles
`pushPullTransition` with `CategoryTheory.SemiRepresentable.pushPullRestrictionTransition`: a
morphism of topoi carries the adjunction of Stacks 00XO, whose inverse image is the sheafified
restriction, while the push-pull restriction transition of a morphism of semi-representable
objects is written with `CategoryTheory.Functor.sheafAdjunctionCocontinuous`, whose left adjoint
is plain restriction. The two left adjoints are different functors with the same right adjoint,
so `restrictionTransition_congr_middle` applies. Its proof is the mate characterisation
`Stacks.CategoryTheory.restrictionTransition_eq_of_mate`, which mentions neither adjunction, plus
the naturality of the comparison of the two left adjoints.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

section Conjugates

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The conjugate, with respect to two adjunctions with the same right adjoint `R`, of the
*inverse* of the canonical comparison of their left adjoints is the identity of `R`.

This is `Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom` with the two adjunctions
exchanged, the inverse of `CategoryTheory.Adjunction.leftAdjointUniq adj₁ adj₂` being the
comparison `CategoryTheory.Adjunction.leftAdjointUniq adj₂ adj₁` by definition. -/
theorem conjugateEquiv_leftAdjointUniq_inv {L₁ L₂ : C ⥤ D} {R : D ⥤ C}
    (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) :
    conjugateEquiv adj₁ adj₂ (Adjunction.leftAdjointUniq adj₁ adj₂).inv = 𝟙 R :=
  conjugateEquiv_leftAdjointUniq_hom adj₂ adj₁

/-- Changing the right adjoint of the *second* adjunction of a conjugate along an isomorphism
`e : R₂ ≅ R₂'` appends `e` to the conjugate.

This is the one-sided form of `Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight`, which
transports both adjunctions at once and therefore does not apply when the first adjunction is
given untransported. -/
theorem conjugateEquiv_ofNatIsoRight_right' {L₁ L₂ : C ⥤ D} {R₁ R₂ R₂' : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₂ ≅ R₂') (τ : L₂ ⟶ L₁) :
    conjugateEquiv adj₁ (adj₂.ofNatIsoRight e) τ = conjugateEquiv adj₁ adj₂ τ ≫ e.hom := by
  ext W
  rw [NatTrans.comp_app, conjugateEquiv_app_eq, Adjunction.homEquiv_ofNatIsoRight_apply,
    ← conjugateEquiv_app_eq]

end Conjugates

section Triangle

variable {A : Type u₁} {B : Type u₂} {D : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} D]
  {P : A ⥤ B} {Q : B ⥤ A} {P' : A ⥤ D} {Q' : D ⥤ A} {R : B ⥤ D} {S : D ⥤ B}

/-- **The companion comparison of right adjoints of a `leftAdjointCompIso` triangle is the
isomorphism it was built from.** Let `adj : P ⊣ Q`, `adj' : P' ⊣ Q'` and `radj : R ⊣ S` be
adjunctions and `e : S ⋙ Q ≅ Q'` an isomorphism of the two right adjoints of `P'`. Transporting
`adj.comp radj` along the comparison of left adjoints that
`CategoryTheory.Adjunction.leftAdjointCompIso` builds from `e` makes `Q'` and `S ⋙ Q` two right
adjoints of `P'`, hence compared by `CategoryTheory.Adjunction.rightAdjointUniq`; that
comparison is the inverse of `e`.

This is what puts `e` itself back into a formula written through `rightAdjointUniq`. -/
theorem rightAdjointUniq_ofNatIsoLeft_leftAdjointCompIso_inv (adj : P ⊣ Q) (adj' : P' ⊣ Q')
    (radj : R ⊣ S) (e : S ⋙ Q ≅ Q') :
    (Adjunction.rightAdjointUniq adj'
        ((adj.comp radj).ofNatIsoLeft
          (Adjunction.leftAdjointCompIso adj radj adj' e))).inv = e.hom := by
  have hunfold : (Adjunction.rightAdjointUniq adj'
        ((adj.comp radj).ofNatIsoLeft
          (Adjunction.leftAdjointCompIso adj radj adj' e))).inv =
      conjugateEquiv ((adj.comp radj).ofNatIsoLeft
        (Adjunction.leftAdjointCompIso adj radj adj' e)) adj' (𝟙 P') := rfl
  rw [hunfold, conjugateEquiv_ofNatIsoLeft_left, Category.id_comp,
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv]

/-- **Changing the middle adjunction of a triangle changes `leftAdjointCompIso` by the comparison
of the two left adjoints.** Let `radj : R ⊣ S` and `radj' : R' ⊣ S` be two adjunctions with the
same right adjoint. The comparisons `P ⋙ R ≅ P'` and `P ⋙ R' ≅ P'` that
`CategoryTheory.Adjunction.leftAdjointCompIso` builds from one isomorphism `e : S ⋙ Q ≅ Q'`
differ by `CategoryTheory.Adjunction.leftAdjointUniq radj radj'`, whiskered by `P`.

Both sides are determined by their conjugates, and `e.hom` is the conjugate of either: the
comparison of the two left adjoints conjugates to the identity
(`conjugateEquiv_leftAdjointUniq_inv`), and whiskering commutes with conjugation
(`CategoryTheory.conjugateEquiv_whiskerLeft`). -/
theorem leftAdjointCompIso_congr_middle {R' : B ⥤ D} (adj : P ⊣ Q) (radj : R ⊣ S)
    (radj' : R' ⊣ S) (adj' : P' ⊣ Q') (e : S ⋙ Q ≅ Q') :
    Adjunction.leftAdjointCompIso adj radj adj' e =
      Functor.isoWhiskerLeft P (Adjunction.leftAdjointUniq radj radj') ≪≫
        Adjunction.leftAdjointCompIso adj radj' adj' e := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).1 ?_)
  apply (conjugateEquiv (adj.comp radj) adj').injective
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv,
    ← conjugateEquiv_comp (adj.comp radj) (adj.comp radj') adj'
      (Functor.whiskerLeft P (Adjunction.leftAdjointUniq radj radj').inv)
      (Adjunction.leftAdjointCompIso adj radj' adj' e).inv,
    conjugateEquiv_whiskerLeft radj radj' adj, conjugateEquiv_leftAdjointUniq_inv,
    Functor.whiskerRight_id', Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
    Category.id_comp]

/-- **The restriction transition does not depend on which left adjoint of the relocalization is
used.** If `eL : P ⋙ R ≅ P'` and `eL' : P ⋙ R' ≅ P'` differ by an isomorphism `ρ : R ≅ R'`
whiskered by `P`, then the two triangles have the same restriction transition, whatever
adjunctions `radj : R ⊣ S` and `radj' : R' ⊣ S'` are used.

The transition is characterised by its mate
(`Stacks.CategoryTheory.restrictionTransition_eq_of_mate`), and the mate formula mentions the
relocalization only through `R` and `eL`; the two mates agree by the naturality of `ρ` at the
counit. -/
theorem restrictionTransition_congr_middle {R' : B ⥤ D} {S' : D ⥤ B} (adj : P ⊣ Q)
    (adj' : P' ⊣ Q') (radj : R ⊣ S) (radj' : R' ⊣ S') (eL : P ⋙ R ≅ P') (eL' : P ⋙ R' ≅ P')
    (ρ : R ≅ R') (h : eL = Functor.isoWhiskerLeft P ρ ≪≫ eL') :
    restrictionTransition adj adj' radj eL = restrictionTransition adj adj' radj' eL' := by
  refine restrictionTransition_eq_of_mate adj adj' radj' eL' _ (fun X => ?_)
  rw [restrictionTransition_mate adj adj' radj eL X, h]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  have hnat : R.map (adj.counit.app (P.obj X)) ≫ ρ.hom.app (P.obj X) =
      ρ.hom.app (P.obj (Q.obj (P.obj X))) ≫ R'.map (adj.counit.app (P.obj X)) :=
    ρ.hom.naturality (adj.counit.app (P.obj X))
  rw [← Category.assoc (R.map (adj.counit.app (P.obj X))) (ρ.hom.app (P.obj X)), hnat,
    Category.assoc, ← Category.assoc (ρ.inv.app (P.obj (Q.obj (P.obj X)))),
    Iso.inv_hom_id_app, Category.id_comp]

end Triangle

end Stacks.CategoryTheory

namespace CategoryTheory.MorphismOfTopoi

open Stacks.CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
  {Z : Type u₃} [Category.{v₃} Z]

/-- **The push-pull transition of a factorization of a morphism of topoi.** Let
`f : X → Z`, `g : Y → Z` and `h : Y → X` be morphisms of topoi and let
`θ : h_* f_* ≅ g_*` exhibit `g` as `f ∘ h` up to isomorphism. Then `θ` also compares the inverse
images, by `CategoryTheory.Adjunction.leftAdjointCompIso`, and the unit of the adjunction of `h`
produces a canonical transformation `f⁻¹ f_* ⟶ g⁻¹ g_*` of the push-pull endofunctors of `Z`,
namely `Stacks.CategoryTheory.restrictionTransition` of that triangle of adjunctions. -/
def pushPullTransition (f : MorphismOfTopoi X Z) (g : MorphismOfTopoi Y Z)
    (h : MorphismOfTopoi Y X) (θ : h.pushforward ⋙ f.pushforward ≅ g.pushforward) :
    f.inverseImage ⋙ f.pushforward ⟶ g.inverseImage ⋙ g.pushforward :=
  restrictionTransition f.adj g.adj h.adj (Adjunction.leftAdjointCompIso f.adj h.adj g.adj θ)

/-- The component of `CategoryTheory.MorphismOfTopoi.pushPullTransition` at an object: the unit
of `h`, the comparison of inverse images, and `θ`. The companion comparison of right adjoints
that `Stacks.CategoryTheory.restrictionTransition` is written with is `θ` itself, by
`Stacks.CategoryTheory.rightAdjointUniq_ofNatIsoLeft_leftAdjointCompIso_inv`. -/
theorem pushPullTransition_app (f : MorphismOfTopoi X Z) (g : MorphismOfTopoi Y Z)
    (h : MorphismOfTopoi Y X) (θ : h.pushforward ⋙ f.pushforward ≅ g.pushforward) (M : Z) :
    (pushPullTransition f g h θ).app M =
      f.pushforward.map (h.adj.unit.app (f.inverseImage.obj M)) ≫
        f.pushforward.map (h.pushforward.map
            ((Adjunction.leftAdjointCompIso f.adj h.adj g.adj θ).hom.app M)) ≫
          θ.hom.app (g.inverseImage.obj M) := by
  rw [pushPullTransition, restrictionTransition_app, restrictionRightAdjointIso,
    rightAdjointUniq_ofNatIsoLeft_leftAdjointCompIso_inv]

/-- **The comparison of the inverse images of two morphisms of topoi with isomorphic direct
images.** If `f` and `f'` are morphisms of topoi `X → Z` and `α : f_* ≅ f'_*`, then `f⁻¹` and
`f'⁻¹` are both left adjoint to `f_*`, the second after transporting its adjunction along `α`,
so they are canonically isomorphic. -/
def inverseImageIsoOfPushforwardIso (f f' : MorphismOfTopoi X Z)
    (α : f.pushforward ≅ f'.pushforward) : f.inverseImage ≅ f'.inverseImage :=
  Adjunction.leftAdjointUniq f.adj (f'.adj.ofNatIsoRight α.symm)

/-- The defining property of `CategoryTheory.MorphismOfTopoi.inverseImageIsoOfPushforwardIso`:
read through the adjunction of `f'` transported along `α`, its inverse conjugates to the
identity. -/
theorem conjugateEquiv_inverseImageIsoOfPushforwardIso_inv_self (f f' : MorphismOfTopoi X Z)
    (α : f.pushforward ≅ f'.pushforward) :
    conjugateEquiv f.adj (f'.adj.ofNatIsoRight α.symm)
        (inverseImageIsoOfPushforwardIso f f' α).inv =
      𝟙 f.pushforward :=
  conjugateEquiv_leftAdjointUniq_inv f.adj (f'.adj.ofNatIsoRight α.symm)

/-- Read through the untransported adjunctions of `f` and `f'`, the inverse of
`CategoryTheory.MorphismOfTopoi.inverseImageIsoOfPushforwardIso` conjugates to `α`. -/
theorem conjugateEquiv_inverseImageIsoOfPushforwardIso_inv (f f' : MorphismOfTopoi X Z)
    (α : f.pushforward ≅ f'.pushforward) :
    conjugateEquiv f.adj f'.adj (inverseImageIsoOfPushforwardIso f f' α).inv = α.hom := by
  have key := conjugateEquiv_inverseImageIsoOfPushforwardIso_inv_self f f' α
  rw [conjugateEquiv_ofNatIsoRight_right, Iso.symm_hom] at key
  simpa using (Iso.comp_inv_eq α).1 key

/-- **The transport of the comparison of inverse images.** Let `α : f_* ≅ f'_*` and
`β : g_* ≅ g'_*` be isomorphisms of direct images compatible with the two factorization
isomorphisms `θ` and `θ'`. Then the comparisons of inverse images that `α` and `β` induce carry
the comparison `f⁻¹ h⁻¹ ≅ g⁻¹` coming from `θ` to the comparison `f'⁻¹ h⁻¹ ≅ g'⁻¹` coming from
`θ'`. -/
theorem isoWhiskerRight_inverseImageIsoOfPushforwardIso_leftAdjointCompIso
    (f f' : MorphismOfTopoi X Z) (g g' : MorphismOfTopoi Y Z) (h : MorphismOfTopoi Y X)
    (θ : h.pushforward ⋙ f.pushforward ≅ g.pushforward)
    (θ' : h.pushforward ⋙ f'.pushforward ≅ g'.pushforward)
    (α : f.pushforward ≅ f'.pushforward) (β : g.pushforward ≅ g'.pushforward)
    (hcompat : Functor.isoWhiskerLeft h.pushforward α ≪≫ θ' = θ ≪≫ β) :
    Functor.isoWhiskerRight (inverseImageIsoOfPushforwardIso f f' α) h.inverseImage ≪≫
        Adjunction.leftAdjointCompIso f'.adj h.adj g'.adj θ' =
      Adjunction.leftAdjointCompIso f.adj h.adj g.adj θ ≪≫
        inverseImageIsoOfPushforwardIso g g' β := by
  have hcompat' : Functor.whiskerLeft h.pushforward α.hom ≫ θ'.hom = θ.hom ≫ β.hom := by
    simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom] using congrArg Iso.hom hcompat
  refine Iso.ext ((Iso.inv_eq_inv _ _).1 ?_)
  apply (conjugateEquiv (f.adj.comp h.adj) (g'.adj.ofNatIsoRight β.symm)).injective
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv]
  rw [← conjugateEquiv_comp (f.adj.comp h.adj) (f'.adj.comp h.adj)
        (g'.adj.ofNatIsoRight β.symm)
        (Functor.whiskerRight (inverseImageIsoOfPushforwardIso f f' α).inv h.inverseImage)
        (Adjunction.leftAdjointCompIso f'.adj h.adj g'.adj θ').inv,
    ← conjugateEquiv_comp (f.adj.comp h.adj) g.adj (g'.adj.ofNatIsoRight β.symm)
        (Adjunction.leftAdjointCompIso f.adj h.adj g.adj θ).inv
        (inverseImageIsoOfPushforwardIso g g' β).inv,
    conjugateEquiv_whiskerRight f.adj f'.adj h.adj,
    conjugateEquiv_inverseImageIsoOfPushforwardIso_inv,
    conjugateEquiv_ofNatIsoRight_right (f'.adj.comp h.adj) g'.adj β.symm,
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
    conjugateEquiv_inverseImageIsoOfPushforwardIso_inv_self, Category.comp_id, Iso.symm_hom,
    ← Category.assoc, hcompat', Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The transport of the push-pull transition.** Let `α : f_* ≅ f'_*` and `β : g_* ≅ g'_*` be
isomorphisms of direct images compatible with the two factorization isomorphisms `θ` and `θ'`.
Then the push-pull transition of `(f, g, θ)` and the push-pull transition of `(f', g', θ')` agree
under the isomorphisms of push-pull functors induced by `α` and `β`; so the transition depends on
the factorization only through `θ`. -/
theorem pushPullTransition_congr (f f' : MorphismOfTopoi X Z) (g g' : MorphismOfTopoi Y Z)
    (h : MorphismOfTopoi Y X)
    (θ : h.pushforward ⋙ f.pushforward ≅ g.pushforward)
    (θ' : h.pushforward ⋙ f'.pushforward ≅ g'.pushforward)
    (α : f.pushforward ≅ f'.pushforward) (β : g.pushforward ≅ g'.pushforward)
    (hcompat : Functor.isoWhiskerLeft h.pushforward α ≪≫ θ' = θ ≪≫ β) :
    pushPullTransition f g h θ ≫
        (Functor.isoWhiskerRight (inverseImageIsoOfPushforwardIso g g' β) g.pushforward ≪≫
          Functor.isoWhiskerLeft g'.inverseImage β).hom =
      (Functor.isoWhiskerRight (inverseImageIsoOfPushforwardIso f f' α) f.pushforward ≪≫
          Functor.isoWhiskerLeft f'.inverseImage α).hom ≫
        pushPullTransition f' g' h θ' := by
  have hiso := isoWhiskerRight_inverseImageIsoOfPushforwardIso_leftAdjointCompIso
    f f' g g' h θ θ' α β hcompat
  refine NatTrans.ext (funext fun M => ?_)
  have hΦ : h.inverseImage.map ((inverseImageIsoOfPushforwardIso f f' α).hom.app M) ≫
      (Adjunction.leftAdjointCompIso f'.adj h.adj g'.adj θ').hom.app M =
      (Adjunction.leftAdjointCompIso f.adj h.adj g.adj θ).hom.app M ≫
        (inverseImageIsoOfPushforwardIso g g' β).hom.app M := by
    simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerRight_app] using NatTrans.congr_app (congrArg Iso.hom hiso) M
  have hβθ : α.hom.app (h.pushforward.obj (g'.inverseImage.obj M)) ≫
      θ'.hom.app (g'.inverseImage.obj M) =
      θ.hom.app (g'.inverseImage.obj M) ≫ β.hom.app (g'.inverseImage.obj M) := by
    simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app] using
      NatTrans.congr_app (congrArg Iso.hom hcompat) (g'.inverseImage.obj M)
  have hα : α.hom.app (f'.inverseImage.obj M) ≫
      f'.pushforward.map (h.adj.unit.app (f'.inverseImage.obj M) ≫
        h.pushforward.map
          ((Adjunction.leftAdjointCompIso f'.adj h.adj g'.adj θ').hom.app M)) =
      f.pushforward.map (h.adj.unit.app (f'.inverseImage.obj M) ≫
          h.pushforward.map
            ((Adjunction.leftAdjointCompIso f'.adj h.adj g'.adj θ').hom.app M)) ≫
        α.hom.app (h.pushforward.obj (g'.inverseImage.obj M)) :=
    (α.hom.naturality _).symm
  have hθ : f.pushforward.map
      (h.pushforward.map ((inverseImageIsoOfPushforwardIso g g' β).hom.app M)) ≫
      θ.hom.app (g'.inverseImage.obj M) =
      θ.hom.app (g.inverseImage.obj M) ≫
        g.pushforward.map ((inverseImageIsoOfPushforwardIso g g' β).hom.app M) :=
    θ.hom.naturality _
  simp only [NatTrans.comp_app, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    pushPullTransition_app, Category.assoc]
  rw [← Functor.map_comp_assoc f'.pushforward, reassoc_of% hα, hβθ,
    ← Functor.map_comp_assoc f.pushforward, ← Functor.map_comp_assoc f.pushforward,
    ← Adjunction.unit_naturality_assoc, ← Functor.map_comp h.pushforward, hΦ,
    ← reassoc_of% hθ, ← Functor.map_comp_assoc f.pushforward, Category.assoc,
    ← Functor.map_comp h.pushforward]

end CategoryTheory.MorphismOfTopoi

end
