module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology

/-!
# The torsor dictionary under a change of site

Tag 03AJ reads a class in `H¹(H)` as the isomorphism class of a torsor under the abelian sheaf
`H`, and `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_naturality` says that reading is
natural in `H` — on one fixed site. This file supplies the missing half: naturality under a
**change of site**.

Let `Φ : Sheaf J AddCommGrpCat ⥤ Sheaf K AddCommGrpCat` be an exact additive functor between the
abelian sheaf categories of two *different* sites `(C, J)` and `(D, K)`, together with an
identification `e` of the inverse image of the constant sheaf `ℤ` with the constant sheaf `ℤ`.
Such a `Φ` and `e` induce a map `H¹(H) ⟶ H¹(Φ H)` — this is exactly the shape of the étale
restriction map of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction`. What is proved here is
that the induced map carries the class of a torsor to the class of a torsor, and *which* one:
the fibre of the image of the torsor's own extension over the section one.

The route avoids the obvious obstruction. One might expect to have to show that `Φ` commutes
with the construction of `Stacks.Cohomology.Torsors.torsorPushoutComplex` — with the free
abelian sheaf on the underlying sheaf of sets, with the augmentation kernel and with the pushout
— which would need the comparison of `Φ` with the free abelian sheaf functor and a long
diagram chase. None of that is needed. The class of a torsor is characterized among *all* short
exact sequences by `Stacks.Cohomology.Torsors.torsorPushout_extClass_eq_boundary`: a torsor
embedded equivariantly in the middle term of a short exact sequence, over a prescribed section
of its third term, has that section's boundary as its class. Applying this to the *image* under
`Φ` of the torsor's extension, which is short exact because `Φ` is exact, identifies the image
class on the nose. Mathlib's `CategoryTheory.Abelian.Ext.mapExactFunctor_extClass` — an exact
functor carries the class of a short exact sequence to the class of its image — is the only
other ingredient.

## Main definitions

* `Stacks.Cohomology.Torsors.siteChangeH1` — the map `H¹(H) ⟶ H¹(Φ H)` induced on first
  cohomology by an exact functor between the abelian sheaf categories of two sites and an
  identification of the constant sheaves `ℤ`.

## Main results

* `Stacks.Cohomology.Torsors.siteChangeH1_torsorPushoutClass_of_embedding` — **the bridge.** If a
  torsor `G` under `Φ H` sits equivariantly inside `Φ` of the middle term of the extension of a
  torsor `F` under `H`, over the section one, then the image of the class of `F` is the class of
  `G`. This is the working form: to compute the image of a torsor class under a change of site,
  exhibit the target torsor inside the image extension.
* `Stacks.Cohomology.Torsors.siteChangeH1_torsorPushoutClass` — the canonical instance of the
  bridge, with no hypothesis to supply: the image of the class of `F` is the class of the fibre
  torsor of the image extension over the section one.
* `Stacks.Cohomology.Torsors.siteChangeH1_torsorIsoClassesEquivH1` — the same statement read
  through the bijection of Tag 03AJ.
* `Stacks.Cohomology.Torsors.torsorPushoutClass_eq_zero_iff` — a torsor's class vanishes exactly
  when it has a global section.
* `Stacks.Cohomology.Torsors.siteChangeH1_torsorPushoutClass_eq_zero_iff` — the image of a
  torsor class vanishes exactly when the fibre torsor of the image extension has a global
  section. This is the form in which injectivity of a restriction map on `H¹` is proved.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_torsorPushoutClass` — the bridge for the
  étale inverse image along a morphism of schemes, which is the change of site that restriction
  of étale cohomology to a closed fibre is built from.

## Implementation notes

The identification `e` of the two constant sheaves is a hypothesis rather than a construction:
on the small étale site it is
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`, which is available because both
constant-sheaf functors are left adjoint to evaluation at the final object, but no such
adjunction is assumed of a general `Φ`. The section of the third term of the image extension
that the fibre is taken over is `e.inv` read as a map out of the constant *presheaf* `ℤ`
through the sheafification adjunction; `Equiv.symm_apply_apply` is what matches it against the
boundary map of `torsorPushout_extClass_eq_boundary`.

The two sites are allowed to have unrelated object and morphism universes, but the coefficient
universe `t` is shared: `Φ` is a functor between the two sheaf categories, so it has to be.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w t v u v' u'

namespace Stacks.Cohomology.Torsors

section FixedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})]

/-- **A torsor has class zero exactly when it has a global section.** The class of the trivial
torsor is zero, and two torsors have the same class exactly when they are isomorphic, so this is
`Stacks.Cohomology.Torsors.torsor_class_eq_trivial_iff` read through the bijection of Tag
03AJ. -/
public lemma torsorPushoutClass_eq_zero_iff (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) :
    torsorPushoutClass H F = 0 ↔ Nonempty (GlobalSections F.1.presheaf) := by
  rw [← torsor_class_eq_trivial_iff H F]
  exact ⟨fun h => (torsorIsoClassesEquivH1 H).injective
      ((torsorIsoClassesEquivH1_trivial H).trans h.symm),
    fun h => ((torsorIsoClassesEquivH1_trivial H).symm.trans
      (congrArg (torsorIsoClassesEquivH1 H) h)).symm⟩

end FixedSite

section SiteChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] [HasExt.{w} (Sheaf K AddCommGrpCat.{t})]
  (Φ : Sheaf J AddCommGrpCat.{t} ⥤ Sheaf K AddCommGrpCat.{t})
  [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (e : Φ.obj ((presheafToSheaf J AddCommGrpCat.{t}).obj
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))) ≅
      (presheafToSheaf K AddCommGrpCat.{t}).obj
        ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))))

/-- **First cohomology under a change of site.** An exact functor `Φ` between the abelian sheaf
categories of two sites acts on `Ext` out of the constant sheaf `ℤ`; composing with the
identification `e` of the image of that constant sheaf with the constant sheaf on the target
site gives a map `H¹(H) ⟶ H¹(Φ H)`.

This is the shape of every restriction map on sheaf cohomology with constant coefficients; for
the small étale site and the étale inverse image it is
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`. -/
public def siteChangeH1 (H : Sheaf J AddCommGrpCat.{t}) :
    Sheaf.H.{w} H 1 →+ Sheaf.H.{w} (Φ.obj H) 1 :=
  ((Abelian.Ext.mk₀ e.inv).precomp (Φ.obj H) (Nat.zero_add 1)).comp
    (Φ.mapExtAddHom.{w, w} _ H 1)

/-- The defining formula for `Stacks.Cohomology.Torsors.siteChangeH1`: apply the exact functor to
the `Ext` class, then compose with the constant-sheaf identification. -/
public lemma siteChangeH1_apply (H : Sheaf J AddCommGrpCat.{t}) (x : Sheaf.H.{w} H 1) :
    siteChangeH1 Φ e H x =
      (Abelian.Ext.mk₀ e.inv).comp (x.mapExactFunctor Φ) (Nat.zero_add 1) := rfl

/-- The global section of the third term of the image extension that the fibre torsor is taken
over: the constant-sheaf identification, read as a map out of the constant presheaf `ℤ` through
the sheafification adjunction. -/
public def siteChangeUnit :
    (Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶
      (Φ.obj ((presheafToSheaf J AddCommGrpCat.{t}).obj
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))))).obj :=
  (sheafificationAdjunction K AddCommGrpCat.{t}).homEquiv _ _ e.inv

/-- **The site-change bridge for the dictionary of Tag 03AJ.** Let `F` be a torsor under `H` on
`(C, J)` and let `G` be a torsor under `Φ H` on `(D, K)`. If `G` embeds in the image under `Φ` of
the middle term of the extension attached to `F`, equivariantly for the inclusion of `Φ H` and
with image exactly the fibre over the section one, then the change-of-site map on first
cohomology carries the class of `F` to the class of `G`.

This is the form in which the bridge is used: the consumer exhibits the torsor it believes the
image class to be — in the geometric situation, the pullback of `F` — together with the
equivariant embedding, and reads off the equality of classes. No comparison of `Φ` with the free
abelian sheaf functor, the augmentation kernel or the pushout is needed, because the class of a
torsor is characterized among all short exact sequences by
`Stacks.Cohomology.Torsors.torsorPushout_extClass_eq_boundary`. -/
public lemma siteChangeH1_torsorPushoutClass_of_embedding
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) (G : AbelianTorsor (Φ.obj H))
    (i : G.1.presheaf ⟶ (Φ.obj (torsorPushoutMiddle H F)).obj ⋙ forget AddCommGrpCat.{t})
    (hi : ∀ (U : Dᵒᵖ) (h : (Φ.obj H).obj.obj U) (s : G.1.presheaf.obj U),
      let iU : G.1.presheaf.obj U → (Φ.obj (torsorPushoutMiddle H F)).obj.obj U := i.app U
      iU (G.1.act U (Multiplicative.ofAdd h) s) =
        (Φ.map (torsorPushoutComplex H F).f).hom.app U h + iU s)
    (hiFiber : ∀ (U : Dᵒᵖ) (s : G.1.presheaf.obj U),
      (Φ.map (torsorPushoutComplex H F).g).hom.app U (i.app U s) =
        (siteChangeUnit Φ e).app U ⟨1⟩) :
    siteChangeH1 Φ e H (torsorPushoutClass H F) = torsorPushoutClass (Φ.obj H) G := by
  have hbdry := torsorPushout_extClass_eq_boundary ((torsorPushoutComplex H F).map Φ)
    ((torsorPushoutComplex_shortExact H F).map_of_exact Φ)
    ((sheafificationAdjunction K AddCommGrpCat.{t}).homEquiv _ _ e.inv) G i hi hiFiber
  rw [Equiv.symm_apply_apply] at hbdry
  change (Abelian.Ext.mk₀ e.inv).comp
      ((torsorPushoutComplex_shortExact H F).extClass.mapExactFunctor Φ) (Nat.zero_add 1) =
    (torsorPushoutComplex_shortExact (Φ.obj H) G).extClass
  rw [Abelian.Ext.mapExactFunctor_extClass Φ (torsorPushoutComplex_shortExact H F), hbdry]

/-- **The canonical instance of the site-change bridge.** The change-of-site map on first
cohomology carries the class of a torsor `F` under `H` to the class of the fibre, over the
section one, of the image under `Φ` of the extension attached to `F`.

Unlike `Stacks.Cohomology.Torsors.siteChangeH1_torsorPushoutClass_of_embedding` this has no
hypothesis to supply: the fibre torsor is the tautological choice of target, and it is a torsor
because the image extension is short exact. -/
public lemma siteChangeH1_torsorPushoutClass
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    siteChangeH1 Φ e H (torsorPushoutClass H F) =
      torsorPushoutClass (Φ.obj H)
        (fiberTorsor ((torsorPushoutComplex H F).map Φ)
          ((torsorPushoutComplex_shortExact H F).map_of_exact Φ) (siteChangeUnit Φ e)) :=
  siteChangeH1_torsorPushoutClass_of_embedding Φ e H F _
    (fiberInclusion ((torsorPushoutComplex H F).map Φ) (siteChangeUnit Φ e))
    (fiberInclusion_spec ((torsorPushoutComplex H F).map Φ)
      ((torsorPushoutComplex_shortExact H F).map_of_exact Φ) (siteChangeUnit Φ e)).1
    (fun _ s => s.2)

/-- **The site-change bridge through the bijection of Tag 03AJ.** The change-of-site map on first
cohomology, read on both sides as a map of isomorphism classes of torsors, sends the class of `F`
to the class of the fibre of the image extension. -/
public lemma siteChangeH1_torsorIsoClassesEquivH1
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    siteChangeH1 Φ e H (torsorIsoClassesEquivH1 H (Quotient.mk (torsorSetoid H) F)) =
      torsorIsoClassesEquivH1 (Φ.obj H) (Quotient.mk (torsorSetoid (Φ.obj H))
        (fiberTorsor ((torsorPushoutComplex H F).map Φ)
          ((torsorPushoutComplex_shortExact H F).map_of_exact Φ) (siteChangeUnit Φ e))) :=
  siteChangeH1_torsorPushoutClass Φ e H F

/-- **The vanishing criterion for a transported torsor class.** The change-of-site map kills the
class of a torsor `F` exactly when the fibre of the image extension over the section one has a
global section.

This is the shape in which injectivity of a restriction map on `H¹` is established: a class is
in the kernel exactly when a specific, explicitly given torsor on the target site is trivial. -/
public lemma siteChangeH1_torsorPushoutClass_eq_zero_iff
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    siteChangeH1 Φ e H (torsorPushoutClass H F) = 0 ↔
      Nonempty (GlobalSections
        (fiberTorsor ((torsorPushoutComplex H F).map Φ)
          ((torsorPushoutComplex_shortExact H F).map_of_exact Φ)
          (siteChangeUnit Φ e)).1.presheaf) := by
  rw [siteChangeH1_torsorPushoutClass, torsorPushoutClass_eq_zero_iff]

end SiteChange

end Stacks.Cohomology.Torsors

namespace Stacks.EtaleCohomology

open Stacks.Cohomology.Torsors

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **The site-change bridge for the étale inverse image.** Restriction on étale cohomology
along a morphism of schemes carries the class of a torsor `F` under an abelian étale sheaf `H` on
`X` to the class of the fibre, over the section one, of the image under étale inverse image of
the extension attached to `F`.

The change of site here is the one that
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` is built from, and the identification of
the two constant sheaves is `Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`, so
this is the degree-one torsor reading of restriction of étale cohomology with constant
coefficients. -/
public lemma etaleCohomologyRestrictionMap_torsorPushoutClass
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (F : AbelianTorsor H) :
    etaleCohomologyRestrictionMap.{u, v, w} i H 1 (torsorPushoutClass H F) =
      torsorPushoutClass ((etaleAbelianInverseImage.{u, v} i).obj H)
        (fiberTorsor ((torsorPushoutComplex H F).map (etaleAbelianInverseImage.{u, v} i))
          ((torsorPushoutComplex_shortExact H F).map_of_exact
            (etaleAbelianInverseImage.{u, v} i))
          (siteChangeUnit (etaleAbelianInverseImage.{u, v} i)
            ((etaleAbelianInverseImageConstantIso.{u, v} i).app
              (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))))) :=
  siteChangeH1_torsorPushoutClass (etaleAbelianInverseImage.{u, v} i)
    ((etaleAbelianInverseImageConstantIso.{u, v} i).app
      (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) H F

end Stacks.EtaleCohomology

end
