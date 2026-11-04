module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation

/-!
# A weak-ideal presentation is a quotient system (Stacks 0AIC and 0AIF)

`AlgebraicGeometry.FormalSpace.SpectrumPresentation` shows that the datum which *builds* a
formal spectrum, `AlgebraicGeometry.FormalSpace.QuotientSystem`, is also a datum which
*recognises* one: a quotient system is a weak-ideal colimit presentation of the formal spectrum
it builds. This file goes the other way. A weak-ideal colimit presentation of a sheaf `X` by a
topological ring `A` — condition (1) of Stacks 0AIC — contains a quotient system for `A`, and
`X` is then isomorphic to the formal spectrum of Stacks 0AIF that quotient system builds.

So the two structures carry the same information, and a consumer may move between them freely.
In particular a McQuillan affine formal algebraic space *is* a formal spectrum, up to
isomorphism, rather than merely being a colimit of quotient spectra; this is the form the
library's other results about formal spectra want their input in, for instance the
hypotheses of
`StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization`, which quantify over
a quotient system together with an isomorphism to its formal spectrum.

## Main definitions

* `AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.quotientSystem`: the quotient
  system extracted from a weak-ideal colimit presentation.

## Main results

* `AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.diagramIso`: the diagram of the
  extracted quotient system is the diagram of the presentation.
* `AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.isoFormalSpectrum`: a sheaf with a
  weak-ideal colimit presentation by `A` is isomorphic to the formal spectrum of the extracted
  quotient system.
* `AlgebraicGeometry.FormalSpace.exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing`:
  consequently a sheaf presented by `A` is a formal spectrum of `A`, up to isomorphism.

## Implementation notes

The three fields of a quotient system are read off the presentation as follows. Containment in
the site is the size bound carried by the stage of the presentation, transported along the
identification of that stage with the quotient spectrum; `AlgebraicGeometry.Scheme.size` is an
isomorphism invariant, so nothing is lost. The structure morphism to `S` is the one the stage
carries as an object of the big affine fppf category over `S`, read through the same
identification. Compatibility with the quotient maps is the naturality field of the
presentation together with the fact that a morphism of the big fppf category over `S` commutes
with the structure morphisms.

The index of a quotient system is the subtype of weak ideals of definition and the index of a
presentation is its order dual, so each field is read at `OrderDual.toDual` of its argument.

The extracted quotient system rebuilds its stages as the quotient spectra themselves rather
than reusing the stages of the presentation, which are only isomorphic to them. The comparison
of the two diagrams is therefore not the identity; it is
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.diagramIso`, assembled from the
presentation's own `quotientIso`.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A] {X : FppfSheaf B S hS}

namespace WeakIdealColimitPresentation

/-- The quotient spectrum of a weak ideal of definition lies in the chosen big fppf site: the
corresponding stage of the presentation does, and the two are isomorphic. -/
theorem contains_quotient (P : WeakIdealColimitPresentation B S hS A X)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    B.Contains (Spec (.of (A ⧸ J.1))) := by
  have h : ((BigAffineFppf.toScheme B S hS).obj
      (P.diagram.obj (OrderDual.toDual J))).size < B.cutoff :=
    (P.diagram.obj (OrderDual.toDual J)).1.left.property
  rwa [Scheme.size_congr (P.quotientIso (OrderDual.toDual J))] at h

/-- The structure morphism of a quotient spectrum over `S`: the one its stage in the
presentation carries, read through the identification of the stage with the quotient
spectrum. -/
def overS (P : WeakIdealColimitPresentation B S hS A X)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    Spec (.of (A ⧸ J.1)) ⟶ S :=
  (P.quotientIso (OrderDual.toDual J)).inv ≫
    B.inclusion.map (P.diagram.obj (OrderDual.toDual J)).1.hom

/-- **The quotient system of a weak-ideal colimit presentation.** A presentation of a sheaf by
the quotients of `A` by its weak ideals of definition contains exactly the datum needed to form
the formal spectrum of `A` in the sense of Stacks 0AIF: each quotient spectrum lies in the site
and carries a structure morphism to `S`, compatibly with the quotient maps. -/
def quotientSystem' (P : WeakIdealColimitPresentation B S hS A X) :
    QuotientSystem B S hS A where
  inSite := P.contains_quotient
  overS := P.overS
  compatible J L h := by
    let f : (OrderDual.toDual L : WeakIdeals A) ⟶ OrderDual.toDual J := homOfLE h
    have hover : (BigAffineFppf.toScheme B S hS).map (P.diagram.map f) ≫
          B.inclusion.map (P.diagram.obj (OrderDual.toDual J)).1.hom =
        B.inclusion.map (P.diagram.obj (OrderDual.toDual L)).1.hom :=
      (B.inclusion.map_comp (P.diagram.map f).1.left
          (P.diagram.obj (OrderDual.toDual J)).1.hom).symm.trans
        (congrArg B.inclusion.map (Over.w (P.diagram.map f).1))
    refine (cancel_epi (P.quotientIso (OrderDual.toDual L)).hom).mp ?_
    calc (P.quotientIso (OrderDual.toDual L)).hom ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ P.overS J
        = ((P.quotientIso (OrderDual.toDual L)).hom ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫ P.overS J :=
          (Category.assoc _ _ _).symm
      _ = ((BigAffineFppf.toScheme B S hS).map (P.diagram.map f) ≫
            (P.quotientIso (OrderDual.toDual J)).hom) ≫ P.overS J :=
          congrArg (· ≫ P.overS J) (P.quotientIso_natural f).symm
      _ = (BigAffineFppf.toScheme B S hS).map (P.diagram.map f) ≫
            B.inclusion.map (P.diagram.obj (OrderDual.toDual J)).1.hom :=
          (Category.assoc _ _ _).trans
            (congrArg (((BigAffineFppf.toScheme B S hS).map (P.diagram.map f)) ≫ ·)
              (Iso.hom_inv_id_assoc (P.quotientIso (OrderDual.toDual J)) _))
      _ = B.inclusion.map (P.diagram.obj (OrderDual.toDual L)).1.hom := hover
      _ = (P.quotientIso (OrderDual.toDual L)).hom ≫ P.overS L :=
          (Iso.hom_inv_id_assoc (P.quotientIso (OrderDual.toDual L)) _).symm

/-- The diagram of the extracted quotient system is the diagram of the presentation: its stages
are the quotient spectra, which the presentation identifies with its own stages. -/
def diagramIso' (P : WeakIdealColimitPresentation B S hS A X) :
    P.quotientSystem'.diagram ≅ P.diagram :=
  NatIso.ofComponents
    (fun J ↦ ObjectProperty.isoMk _ (Over.isoMk
      (ObjectProperty.isoMk _ (P.quotientIso J).symm) (by
        apply ObjectProperty.hom_ext
        change (P.quotientIso J).inv ≫
          B.inclusion.map (P.diagram.obj J).1.hom = P.overS (OrderDual.ofDual J)
        rfl)))
    (fun {J K} f ↦ by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change (BigAffineFppf.toScheme B S hS).map (P.quotientSystem'.diagram.map f) ≫
          (P.quotientIso K).inv =
        (P.quotientIso J).inv ≫ (BigAffineFppf.toScheme B S hS).map (P.diagram.map f)
      refine (Iso.comp_inv_eq (P.quotientIso K)).mpr ?_
      exact ((Category.assoc (P.quotientIso J).inv
            ((BigAffineFppf.toScheme B S hS).map (P.diagram.map f))
            (P.quotientIso K).hom).trans
          ((congrArg ((P.quotientIso J).inv ≫ ·) (P.quotientIso_natural f)).trans
            (Iso.inv_hom_id_assoc (P.quotientIso J) _))).symm)

/-- A sheaf with a weak-ideal colimit presentation by `A` is isomorphic to the formal spectrum
of the quotient system that presentation contains. This is the sense in which a McQuillan affine
formal algebraic space *is* a formal spectrum. -/
def isoFormalSpectrum (P : WeakIdealColimitPresentation B S hS A X) :
    X ≅ formalSpectrum P.quotientSystem' :=
  P.colimitIso ≪≫ (HasColimit.isoOfNatIso (Functor.isoWhiskerRight P.diagramIso'
    (BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))).symm

end WeakIdealColimitPresentation

/-- A sheaf presented by a weakly admissible topological ring `A`, in the sense of condition (1)
of Stacks 0AIC, is isomorphic to the formal spectrum of a quotient system for `A`. This is the
shape in which the library's results about formal spectra take their input. -/
theorem exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing
    [IsTopologicalRing A] [IsLinearTopology A A] (h : IsPresentingRing B S hS A X) :
    ∃ D : QuotientSystem B S hS A, Nonempty (X ≅ formalSpectrum D) :=
  h.2.elim fun P ↦ ⟨P.quotientSystem', ⟨P.isoFormalSpectrum⟩⟩

end AlgebraicGeometry.FormalSpace

end
