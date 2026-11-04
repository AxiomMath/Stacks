module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizationLift
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism

/-!
# The inverse-image form of a 2-isomorphism of ringed topoi, and rigidity

A 2-isomorphism of morphisms of ringed topoi `p, q : (Sh(C), O_C) ⟶ (Sh(D), O_D)` is by
definition an isomorphism `p_* ≅ q_*` of the direct images compatible with the two structure maps
in their direct-image form.  `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` builds
one out of an isomorphism `q⁻¹ ≅ p⁻¹` of the inverse images compatible with the two structure maps
in their inverse-image form.  This file supplies the other direction and shows that the two
passages are mutually inverse: a 2-isomorphism *is* the same thing as a compatible isomorphism of
the inverse images.

That matters because the inverse images are the functors whose values are sheaves on the
*source*, so they are the ones a chartwise comparison on the source localizes, while the
direct-image form is the one the structure of a 2-isomorphism is stated in.

The file also records that rigidity transports: if a morphism of ringed topoi has no non-trivial
2-endomorphisms then neither does any morphism 2-isomorphic to it, and consequently any two
2-isomorphisms with a rigid target are equal.

## Main definitions

No new definitions are introduced.  The isomorphism `q⁻¹ ≅ p⁻¹` underlying a 2-isomorphism
`p ≅ q` — the conjugate of its isomorphism of direct images — is
`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIso` of
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/LocalizationLift.lean`, imported here.

## Main results

* `AlgebraicGeometry.RingedToposHom.inverseImage_compat_iff` — **the two compatibility
  conditions are the same condition.**  An isomorphism of inverse images is compatible with the
  inverse-image forms of the structure maps exactly when its conjugate is compatible with the
  direct-image forms.
* `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso_inverseImageIso` — together with
  `AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIso_ofInverseImageIso` of
  `StacksFrontier/CategoryTheory/Sites/Modules/Localization/LocalizationLift.lean`, the two passages
  are mutually inverse.
* `AlgebraicGeometry.RingedToposHom.TwoIso.eq_of_inverseImageIso_eq` — a 2-isomorphism is
  determined by its inverse-image form.
* `AlgebraicGeometry.RingedToposHom.TwoMorphism.eq_id_of_twoIso` — **rigidity transports along a
  2-isomorphism.**
* `AlgebraicGeometry.RingedToposHom.TwoIso.eq_of_rigid` and
  `AlgebraicGeometry.RingedToposHom.TwoIso.eq_of_rigid_of_twoIso` — any two 2-isomorphisms into a
  rigid morphism, or into one 2-isomorphic to a rigid morphism, are equal.

## Implementation notes

The whole content of the compatibility equivalence is one application of
`Stacks.CategoryTheory.homEquiv_conjugate`: transposing the inverse-image compatibility along
`q⁻¹ ⊣ q_*` turns it into the direct-image compatibility, because the inverse-image form of a
structure map is the adjunct of its direct-image form
(`AlgebraicGeometry.RingedToposHom.forgetFSharp_eq_homEquiv`).  Since the transpose is a
bijection, the implication runs both ways, which is what
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` proves in only one direction.

Rigidity transports by conjugation: a 2-endomorphism of `f` is carried to one of `g` by a
2-isomorphism `w : f ≅ g`, and the conjugation is injective because `w.e` is invertible.  Both
statements are about the underlying natural transformations only, so both go through
`AlgebraicGeometry.RingedToposHom.TwoMorphism.ext`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₂}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₂})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- **The inverse-image and direct-image forms of the structure-map compatibility are the same
condition.**  An isomorphism `α : q⁻¹ ≅ p⁻¹` of the inverse images of two morphisms of ringed
topoi carries the inverse-image form of the structure map of `p` to that of `q` exactly when its
conjugate `p_* ≅ q_*` carries the direct-image form of the structure map of `p` to that of
`q`. -/
theorem inverseImage_compat_iff {p q : RingedToposHom A B}
    (α : q.toToposHom.inverseImage ≅ p.toToposHom.inverseImage) :
    (α.hom.app (B.forgetRing.obj B.O) ≫ A.forgetRing.map p.fSharpInverseImage =
        A.forgetRing.map q.fSharpInverseImage) ↔
      forgetFSharp p ≫
          (conjugateIsoEquiv p.toToposHom.adj q.toToposHom.adj α).hom.app
            (A.forgetRing.obj A.O) = forgetFSharp q := by
  have ht : q.toToposHom.adj.homEquiv (B.forgetRing.obj B.O) (A.forgetRing.obj A.O)
        (α.hom.app (B.forgetRing.obj B.O) ≫ A.forgetRing.map p.fSharpInverseImage) =
      forgetFSharp p ≫
        (conjugateIsoEquiv p.toToposHom.adj q.toToposHom.adj α).hom.app
          (A.forgetRing.obj A.O) := by
    have h0 := Stacks.CategoryTheory.homEquiv_conjugate p.toToposHom.adj q.toToposHom.adj
      (conjugateEquiv p.toToposHom.adj q.toToposHom.adj α.hom)
      (A.forgetRing.map p.fSharpInverseImage)
    rw [Equiv.symm_apply_apply] at h0
    exact h0.trans (congrArg
      (fun z => z ≫ (conjugateIsoEquiv p.toToposHom.adj q.toToposHom.adj α).hom.app
        (A.forgetRing.obj A.O))
      (forgetFSharp_eq_homEquiv p).symm)
  have hq : q.toToposHom.adj.homEquiv (B.forgetRing.obj B.O) (A.forgetRing.obj A.O)
      (A.forgetRing.map q.fSharpInverseImage) = forgetFSharp q :=
    (forgetFSharp_eq_homEquiv q).symm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← ht, h, hq]
  · exact (q.toToposHom.adj.homEquiv (B.forgetRing.obj B.O)
      (A.forgetRing.obj A.O)).injective (ht.trans (h.trans hq.symm))

/-- The conjugate of the inverse-image form of a 2-isomorphism is the 2-isomorphism's own
isomorphism of direct images. -/
theorem TwoIso.conjugateIsoEquiv_inverseImageIso {p q : RingedToposHom A B} (s : TwoIso p q) :
    conjugateIsoEquiv p.toToposHom.adj q.toToposHom.adj s.inverseImageIso = s.e :=
  Equiv.apply_symm_apply _ _

/-- A 2-isomorphism of ringed topoi is recovered from its inverse-image form. -/
theorem TwoIso.ofInverseImageIso_inverseImageIso {p q : RingedToposHom A B} (s : TwoIso p q) :
    TwoIso.ofInverseImageIso s.inverseImageIso s.inverseImageIso_fSharpInverseImage = s :=
  TwoIso.ext s.conjugateIsoEquiv_inverseImageIso

/-- **A 2-isomorphism of ringed topoi is determined by its inverse-image form.** -/
theorem TwoIso.eq_of_inverseImageIso_eq {p q : RingedToposHom A B} {s s' : TwoIso p q}
    (h : s.inverseImageIso = s'.inverseImageIso) : s = s' :=
  TwoIso.ext ((conjugateIsoEquiv p.toToposHom.adj q.toToposHom.adj).symm.injective h)

/-- In a rigid target, a round trip `g ⟶ f ⟶ g` of 2-morphisms has identity underlying
transformation. -/
private theorem comp_eq_id_of_rigid {f g : RingedToposHom A B}
    (hg : ∀ t : TwoMorphism g g, t = TwoMorphism.id g) (x : TwoMorphism g f)
    (y : TwoMorphism f g) : x.t ≫ y.t = 𝟙 _ :=
  congrArg TwoMorphism.t (hg (x.vcomp y))

/-- **Rigidity of a morphism of ringed topoi transports along a 2-isomorphism.**  If every
2-endomorphism of `g` is the identity and `f` is 2-isomorphic to `g`, then every 2-endomorphism
of `f` is the identity: conjugating by the 2-isomorphism is injective. -/
theorem TwoMorphism.eq_id_of_twoIso {f g : RingedToposHom A B} (w : TwoIso f g)
    (hg : ∀ t : TwoMorphism g g, t = TwoMorphism.id g) (t : TwoMorphism f f) :
    t = TwoMorphism.id f := by
  refine TwoMorphism.ext ?_
  have h := w.e.inv_comp_eq.1 (comp_eq_id_of_rigid hg w.symm.toTwoMorphism
    (t.vcomp w.toTwoMorphism))
  exact (cancel_mono w.e.hom).1 (h.trans ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- **Two 2-isomorphisms into a rigid morphism of ringed topoi are equal.** -/
theorem TwoIso.eq_of_rigid {f g : RingedToposHom A B}
    (hg : ∀ t : TwoMorphism g g, t = TwoMorphism.id g) (s s' : TwoIso f g) : s = s' :=
  TwoIso.ext (Iso.ext ((cancel_epi s'.e.inv).1
    ((comp_eq_id_of_rigid hg s'.symm.toTwoMorphism s.toTwoMorphism).trans
      s'.e.inv_hom_id.symm)))

/-- **Two 2-isomorphisms into a morphism of ringed topoi that is itself 2-isomorphic to a rigid
one are equal.**  This is the form a chartwise uniqueness statement takes: the rigidity available
is that of the morphism of ringed topoi of a morphism of algebraic spaces, and the target of the
chartwise 2-isomorphism is a *composite* of such, 2-isomorphic to it. -/
theorem TwoIso.eq_of_rigid_of_twoIso {f g h : RingedToposHom A B} (w : TwoIso g h)
    (hh : ∀ t : TwoMorphism h h, t = TwoMorphism.id h) (s s' : TwoIso f g) : s = s' :=
  TwoIso.eq_of_rigid (fun t => TwoMorphism.eq_id_of_twoIso w hh t) s s'

end AlgebraicGeometry.RingedToposHom

end
