module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Proper
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseFormalSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseProper

/-!
# Formal spectra, properness and rig-étaleness over a smaller base

Let `g : V ⟶ S` be a morphism of a big fppf site `B`. A quotient system of a topological ring over
`V` (the data of Stacks 0AIF) is one over `S` by composing with `g`, and the formal spectrum over
`V` is attached, by `AlgebraicGeometry.FormalSpace.smallerBaseSheafFunctor`, to the formal spectrum
over `S` of the composite system. This file proves that, and deduces that properness (Stacks
0AM6) and rig-étaleness (Stacks 0AQM) of morphisms of fppf sheaves descend along the change of
base.

## Main definitions

* `AlgebraicGeometry.FormalSpace.smallerBaseQuotientSystem`: a quotient system over `V` viewed over
  `S`.
* `AlgebraicGeometry.FormalSpace.smallerBaseContinuousHom`: a continuous homomorphism of quotient
  systems over `V` viewed over `S`.
* `AlgebraicGeometry.FormalSpace.smallerBaseFormalSpectrumIso`: the attached sheaf of the formal
  spectrum over `V` is the formal spectrum over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.smallerBaseFormalSpectrumIso_naturality`: compatibility with the
  maps of formal spectra.
* `AlgebraicGeometry.FormalSpace.isProper_of_smallerBaseSheafFunctor`.
* `AlgebraicGeometry.FormalSpace.isRigEtale_of_smallerBaseSheafFunctor`.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AM6](https://stacks.math.columbia.edu/tag/0AM6)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

attribute [local instance] bigFppfOver_subcanonical

/-! ### Quotient systems and formal spectra -/

section QuotientSystem

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [CommRing C] [TopologicalSpace C]

/-- A quotient system over `V` viewed over `S`, by composing with `g`. -/
def smallerBaseQuotientSystem (D : QuotientSystem B V hV A) : QuotientSystem B S hS A where
  inSite := D.inSite
  overS J := D.overS J ≫ g.hom
  compatible J L h := by rw [← Category.assoc, D.compatible J L h]

/-- The diagram of quotient spectra of the composite system is the diagram over `V` viewed over
`S`. -/
theorem smallerBaseQuotientSystem_diagram (D : QuotientSystem B V hV A) :
    (smallerBaseQuotientSystem B V S hV hS g D).diagram =
      D.diagram ⋙ smallerBaseAffineFunctor B V S hV hS g :=
  rfl

/-- A continuous homomorphism of quotient systems over `V` is one of the composite systems. -/
def smallerBaseContinuousHom {D : QuotientSystem B V hV A} {E : QuotientSystem B V hV C}
    (f : ContinuousHom D E) :
    ContinuousHom (smallerBaseQuotientSystem B V S hV hS g D)
      (smallerBaseQuotientSystem B V S hV hS g E) where
  toRingHom := f.toRingHom
  continuous := f.continuous
  overS J K h := by
    change _ ≫ D.overS J ≫ g.hom = E.overS K ≫ g.hom
    rw [← Category.assoc, f.overS J K h]

/-- **The formal spectrum does not see the change of base.** The attached sheaf of the formal
spectrum over `V` of a quotient system is the formal spectrum over `S` of the composite system. -/
def smallerBaseFormalSpectrumIso (D : QuotientSystem B V hV A) :
    (smallerBaseSheafFunctor B V S hV hS g).obj (formalSpectrum D) ≅
      formalSpectrum (smallerBaseQuotientSystem B V S hV hS g D) :=
  preservesColimitIso (smallerBaseSheafFunctor B V S hV hS g) (formalSpectrumDiagram D) ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (D.diagram ⋙ BigAffineFppf.inclusion B V hV)
      (smallerBaseSheafifiedYonedaIso B V S hV hS g))

/-- The comparison `AlgebraicGeometry.FormalSpace.smallerBaseFormalSpectrumIso` on the quotient
stages. -/
@[reassoc]
theorem smallerBaseFormalSpectrumIso_ι (D : QuotientSystem B V hV A)
    (J : OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (smallerBaseSheafFunctor B V S hV hS g).map (formalSpectrumInclusion D J) ≫
        (smallerBaseFormalSpectrumIso B V S hV hS g D).hom =
      (smallerBaseSheafifiedYonedaIso B V S hV hS g).hom.app
          ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)) ≫
        formalSpectrumInclusion (smallerBaseQuotientSystem B V S hV hS g D) J := by
  simp only [smallerBaseFormalSpectrumIso]
  exact (ι_preservesColimitIso_hom_assoc _ _ J _).trans (HasColimit.isoOfNatIso_ι_hom _ J)

/-- The comparison `AlgebraicGeometry.FormalSpace.smallerBaseFormalSpectrumIso` is compatible with
the maps of formal spectra. -/
theorem smallerBaseFormalSpectrumIso_naturality [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B V hV A}
    {E : QuotientSystem B V hV C} (f : ContinuousHom D E) :
    (smallerBaseSheafFunctor B V S hV hS g).map (formalSpectrumMap hA f) ≫
        (smallerBaseFormalSpectrumIso B V S hV hS g D).hom =
      (smallerBaseFormalSpectrumIso B V S hV hS g E).hom ≫
        formalSpectrumMap hA (smallerBaseContinuousHom B V S hV hS g f) := by
  apply (isColimitOfPreserves (smallerBaseSheafFunctor B V S hV hS g)
    (colimit.isColimit (formalSpectrumDiagram E))).hom_ext
  intro K
  obtain ⟨I, hI⟩ := hA.1
  let K' := OrderDual.ofDual K
  let J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨I ⊓ Ideal.comap f.toRingHom K'.1,
      hI.1.inter (K'.2.1.preimage f.continuous), fun x hx => hI.2 x (Ideal.mem_inf.mp hx).1⟩
  have hJK : J.1 ≤ Ideal.comap f.toRingHom K'.1 := inf_le_right
  let Ψ := smallerBaseSheafFunctor B V S hV hS g
  have h1 := ((Ψ.map_comp _ _).symm.trans
    (congrArg Ψ.map (formalSpectrumMap_spec hA f J K' hJK))).trans (Ψ.map_comp _ _)
  have hN := (smallerBaseSheafifiedYonedaIso B V S hV hS g).hom.naturality
    ((BigAffineFppf.inclusion B V hV).map (f.stageMap J K' hJK))
  have h2 := formalSpectrumMap_spec hA (smallerBaseContinuousHom B V S hV hS g f) J K' hJK
  have hD := smallerBaseFormalSpectrumIso_ι B V S hV hS g D (OrderDual.toDual J)
  have hE := smallerBaseFormalSpectrumIso_ι B V S hV hS g E K
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (smallerBaseFormalSpectrumIso B V S hV hS g D).hom) h1).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hD).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hN).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) h2.symm).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hE.symm).trans (Category.assoc _ _ _)

/-- The attached morphism of a map of formal spectra over `V` is the map of formal spectra over
`S` of the composite systems. -/
theorem smallerBaseSheafFunctor_map_formalSpectrumMap [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem B V hV A} {E : QuotientSystem B V hV C} (f : ContinuousHom D E) :
    (smallerBaseSheafFunctor B V S hV hS g).map (formalSpectrumMap hA f) =
      (smallerBaseFormalSpectrumIso B V S hV hS g E).hom ≫
        formalSpectrumMap hA (smallerBaseContinuousHom B V S hV hS g f) ≫
          (smallerBaseFormalSpectrumIso B V S hV hS g D).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv, smallerBaseFormalSpectrumIso_naturality]

end QuotientSystem

/-! ### Properness -/

/-- **Properness (Stacks 0AM6) does not see the change of base.** -/
theorem isProper_smallerBaseSheafFunctor_map_iff {G G' : FppfSheaf B V hV} (f : G ⟶ G') :
    IsProper B S hS ((smallerBaseSheafFunctor B V S hV hS g).map f) ↔ IsProper B V hV f :=
  representableProper_smallerBaseULiftMap_iff B V S hV hS g f.hom

/-- Properness is unchanged by composing with isomorphisms on both sides. -/
theorem isProper_of_arrowIso {X Y X' Y' : FppfSheaf B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (w : f ≫ eY.hom = eX.hom ≫ f') (h : IsProper B S hS f') :
    IsProper B S hS f :=
  IsProper.of_isPullback B S hS (IsPullback.of_vert_isIso (fst := f) (snd := eX.hom)
    (f := eY.hom) (g := f') ⟨w⟩) h

/-- **Properness descends along the change of base.** -/
theorem isProper_of_smallerBaseSheafFunctor {G G' : FppfSheaf B V hV} (f : G ⟶ G')
    {X Y : FppfSheaf B S hS} (f' : X ⟶ Y) (eX : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅ X)
    (eY : (smallerBaseSheafFunctor B V S hV hS g).obj G' ≅ Y)
    (w : (smallerBaseSheafFunctor B V S hV hS g).map f ≫ eY.hom = eX.hom ≫ f')
    (h : IsProper B S hS f') : IsProper B V hV f :=
  (isProper_smallerBaseSheafFunctor_map_iff B V S hV hS g f).mp
    (isProper_of_arrowIso B S hS _ f' eX eY w h)

/-! ### Rig-étaleness -/

/-- An attached morphism is representable étale exactly when the morphism over `V` is. -/
theorem isRepresentableEtale_smallerBaseSheafFunctor_map_iff {G G' : FppfSheaf B V hV}
    (f : G ⟶ G') :
    IsRepresentableEtale B S hS ((smallerBaseSheafFunctor B V S hV hS g).map f) ↔
      IsRepresentableEtale B V hV f :=
  representableEtale_smallerBaseULiftMap_iff B V S hV hS g f.hom

/-- An attached morphism composed with an isomorphism is representable étale if the morphism over
`V` is. -/
private theorem isRepresentableEtale_map_comp_hom {G G' : FppfSheaf B V hV}
    {Y : FppfSheaf B S hS} (f : G ⟶ G') (e : (smallerBaseSheafFunctor B V S hV hS g).obj G' ≅ Y)
    (hf : IsRepresentableEtale B V hV f) :
    IsRepresentableEtale B S hS ((smallerBaseSheafFunctor B V S hV hS g).map f ≫ e.hom) :=
  IsRepresentableEtale.comp B S hS
    ((isRepresentableEtale_smallerBaseSheafFunctor_map_iff B V S hV hS g f).mpr hf)
    (isRepresentableEtale_of_isIso B S hS _)

/-- **Rig-étaleness (Stacks 0AQM) descends along the change of base.** If a morphism over `S`
isomorphic to the attached morphism of `f` is rig-étale, then `f` is rig-étale over `V`: a
morphism of affine étale charts of `f`, presented by formal spectra over `V`, is attached to a
morphism of affine étale charts over `S`, presented by the composite quotient systems, with the
same homomorphism of rings. -/
theorem isRigEtale_of_smallerBaseSheafFunctor {G G' : FppfSheaf B V hV} (f : G ⟶ G')
    {X Y : FppfSheaf B S hS} (f' : X ⟶ Y) (eX : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅ X)
    (eY : (smallerBaseSheafFunctor B V S hV hS g).obj G' ≅ Y)
    (w : (smallerBaseSheafFunctor B V S hV hS g).map f ≫ eY.hom = eX.hom ≫ f')
    (h : IsRigEtale B S hS f') : IsRigEtale B V hV f := by
  let Ψ := smallerBaseSheafFunctor B V S hV hS g
  intro U U' hU hU' a b t ha hb hae hbe hcomm A C _ _ _ _ _ _ _ _ _ _ hAadic hCadic hA D E eU eU'
    k hk
  have ha' := isRepresentableEtale_map_comp_hom B V S hV hS g a eX ⟨ha, hae⟩
  have hb' := isRepresentableEtale_map_comp_hom B V S hV hS g b eY ⟨hb, hbe⟩
  refine h (Ψ.obj U) (Ψ.obj U')
    ((isAffineFormalAlgebraicSpace_smallerBaseSheafFunctor_iff B V S hV hS g U).mpr hU)
    ((isAffineFormalAlgebraicSpace_smallerBaseSheafFunctor_iff B V S hV hS g U').mpr hU')
    (Ψ.map a ≫ eX.hom) (Ψ.map b ≫ eY.hom) (Ψ.map t) ha'.1 hb'.1 ha'.2 hb'.2 ?_ A C hAadic hCadic
    hA (smallerBaseQuotientSystem B V S hV hS g D) (smallerBaseQuotientSystem B V S hV hS g E)
    (Ψ.mapIso eU ≪≫ smallerBaseFormalSpectrumIso B V S hV hS g E)
    (Ψ.mapIso eU' ≪≫ smallerBaseFormalSpectrumIso B V S hV hS g D)
    (smallerBaseContinuousHom B V S hV hS g k) ?_
  · rw [Category.assoc, ← w, ← Category.assoc, ← Functor.map_comp, hcomm, Functor.map_comp,
      Category.assoc]
  · rw [hk, Functor.map_comp, Functor.map_comp]
    simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Category.assoc]
    rw [smallerBaseSheafFunctor_map_formalSpectrumMap B V S hV hS g hA k]
    simp only [Category.assoc]

end AlgebraicGeometry.FormalSpace

end
