module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseModification

/-!
# Formal modifications are carried to a smaller base

Let `g : V ⟶ S` be a morphism of a big fppf site `B`, and let
`AlgebraicGeometry.FormalSpace.smallerBaseSheafFunctor` attach to an fppf sheaf on the big fppf
site of `V` the fppf sheaf on the big fppf site of `S` with the same sections (the change of base
of Stacks 04SG). `StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseModification` shows that
being a formal modification (Stacks 0GDK) of the attached morphism over `S` implies being one over
`V`. This file proves the converse direction: the attached morphism of a formal modification over
`V` is a formal modification over `S`. Together, being a formal modification does not see the
change of base.

Every test object of a condition over `S` that maps to an attached sheaf is itself attached, up to
isomorphism, to a test object over `V`
(`AlgebraicGeometry.FormalSpace.exists_smallerBaseSheafFunctor_lift`),
and a quotient system over `S` presenting an attached sheaf comes from one over `V`
(`AlgebraicGeometry.FormalSpace.exists_quotientSystem_iso_of_smallerBaseSheafFunctor`). The
conditions over `S` are thereby read off the conditions over `V`.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_smallerBaseSheafFunctor`: locally Noetherian
  formal algebraic spaces (Stacks 0AKY).
* `AlgebraicGeometry.FormalSpace.isRigEtale_smallerBaseSheafFunctor`: rig-étale morphisms
  (Stacks 0AQM).
* `AlgebraicGeometry.FormalSpace.isRigSurjective_smallerBaseSheafFunctor`: rig-surjective
  morphisms (Stacks 0AQQ).
* `AlgebraicGeometry.FormalSpace.isFormalModification_smallerBaseSheafFunctor`: formal
  modifications (Stacks 0GDK).

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

attribute [local instance] bigFppfOver_subcanonical

local notation "Ψ" => smallerBaseSheafFunctor B V S hV hS g

/-! ### Locally Noetherian formal algebraic spaces -/

/-- An affine étale atlas over `V` is carried to an affine étale atlas of the attached sheaf, and
a property of its members is carried along when the property over `V` implies the property of
the attached sheaves. -/
theorem hasAffineEtaleAtlasWithProperty_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (P' : FppfSheaf B V hV → Prop) (P : FppfSheaf B S hS → Prop)
    (hP : ∀ G' : FppfSheaf B V hV, P' G' → P ((smallerBaseSheafFunctor B V S hV hS g).obj G'))
    (h : HasAffineEtaleAtlasWithProperty B V hV G P') :
    HasAffineEtaleAtlasWithProperty B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G) P := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B V hV) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Xi, f, haff, het, hsurj, hPi⟩ := h
  refine ⟨I, fun i => (Ψ).obj (Xi i), fun i => (Ψ).map (f i), fun i => ?_, fun i => ?_, ?_,
    fun i => hP _ (hPi i)⟩
  · exact (isAffineFormalAlgebraicSpace_smallerBaseSheafFunctor_iff B V S hV hS g _).mpr (haff i)
  · exact (isRepresentableEtale_smallerBaseSheafFunctor_map_iff B V S hV hS g (f i)).mpr (het i)
  · have : Epi (Sigma.desc f) := (Sheaf.isLocallySurjective_iff_epi _).mp hsurj
    have h1 : sigmaComparison Ψ Xi ≫ (Ψ).map (Sigma.desc f) = Sigma.desc fun i => (Ψ).map (f i) :=
      sigmaComparison_map_desc Ψ Xi G f
    rw [Sheaf.isLocallySurjective_iff_epi, ← h1]
    infer_instance

/-- **Formal algebraic spaces are carried to the smaller base.** The sheaf on the big fppf site of
`S` attached to a formal algebraic space over `V` (Stacks 0AIM) is a formal algebraic space over
`S`. -/
theorem isFormalAlgebraicSpace_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (h : IsFormalAlgebraicSpace B V hV G) :
    IsFormalAlgebraicSpace B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G) := by
  obtain ⟨hset, I, Xi, f, haff, het, hsurj⟩ := h
  obtain ⟨I', Xi', f', haff', het', hsurj', -⟩ :=
    hasAffineEtaleAtlasWithProperty_smallerBaseSheafFunctor B V S hV hS g G (fun _ => True)
      (fun _ => True) (fun _ _ => trivial) ⟨I, Xi, f, haff, het, hsurj, fun _ => trivial⟩
  exact ⟨(satisfiesSetTheoreticCondition_smallerBaseSheafFunctor_iff B V S hV hS g G).mpr hset,
    I', Xi', f', haff', het', hsurj'⟩

/-- **Surjective presentations (Stacks 0AIC (4)) are carried to the smaller base.** -/
theorem hasSomeSurjectivePresentation_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (h : HasSomeSurjectivePresentation B V hV G) :
    HasSomeSurjectivePresentation B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G) := by
  obtain ⟨hAff, I, pre, hne, hdir, D, hD, ⟨eX⟩, hsurj⟩ := h
  let := pre
  exact ⟨(isAffineFormalAlgebraicSpace_smallerBaseSheafFunctor_iff B V S hV hS g G).mpr hAff, I,
    pre, hne, hdir, D ⋙ smallerBaseAffineFunctor B V S hV hS g, fun _ _ f => hD f,
    ⟨smallerBaseColimitIso B V S hV hS g D G eX⟩, hsurj⟩

/-- **Presenting rings are carried to the smaller base.** A weakly admissible topological ring
presenting `G` presents the attached sheaf of `G`, by the same quotients. -/
theorem isPresentingRing_smallerBaseSheafFunctor (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (G : FppfSheaf B V hV)
    (h : IsPresentingRing B V hV A G) :
    IsPresentingRing B S hS A ((smallerBaseSheafFunctor B V S hV hS g).obj G) := by
  obtain ⟨hwa, ⟨P⟩⟩ := h
  exact ⟨hwa, ⟨{ diagram := P.diagram ⋙ smallerBaseAffineFunctor B V S hV hS g
                 quotientIso := P.quotientIso
                 quotientIso_natural := P.quotientIso_natural
                 colimitIso := smallerBaseColimitIso B V S hV hS g P.diagram G P.colimitIso }⟩⟩

/-- **Noetherian affine formal algebraic spaces (Stacks 0AID (5)) are carried to the smaller
base.** -/
theorem isNoetherian_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (h : IsNoetherian B V hV G) :
    IsNoetherian B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G) := by
  obtain ⟨hpres, A, instCR, instTS, instTR, instLT, hpr, hN, hA⟩ := h
  exact ⟨hasSomeSurjectivePresentation_smallerBaseSheafFunctor B V S hV hS g G hpres, A,
    instCR, instTS, instTR, instLT, isPresentingRing_smallerBaseSheafFunctor B V S hV hS g A G hpr,
    hN, hA⟩

/-- **Locally Noetherian formal algebraic spaces (Stacks 0AKY) are carried to the smaller
base.** -/
theorem isLocallyNoetherian_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (h : IsLocallyNoetherian B V hV G) :
    IsLocallyNoetherian B S hS ((smallerBaseSheafFunctor B V S hV hS g).obj G) :=
  ⟨isFormalAlgebraicSpace_smallerBaseSheafFunctor B V S hV hS g G h.1,
    hasAffineEtaleAtlasWithProperty_smallerBaseSheafFunctor B V S hV hS g G _ _
      (isNoetherian_smallerBaseSheafFunctor B V S hV hS g) h.2⟩

/-! ### Quotient systems presenting attached sheaves -/

section QuotientSystem

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [CommRing C] [TopologicalSpace C]

/-- The isomorphism of an fppf sheaf over `V` with a formal spectrum over `V`, read from an
isomorphism of attached sheaves with structure morphisms. -/
private theorem smallerBaseSheafFunctor_map_smallerBaseLiftIso_hom {G G' : FppfSheaf B V hV}
    (e : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅
      (smallerBaseSheafFunctor B V S hV hS g).obj G')
    (he : e.hom ≫ smallerBaseStr B V S hV hS g G' = smallerBaseStr B V S hV hS g G) :
    (smallerBaseSheafFunctor B V S hV hS g).map (smallerBaseLiftIso B V S hV hS g e he).hom =
      e.hom := by
  change ((smallerBaseOverEquivalence B V S hV hS g).functor.map
    ((smallerBaseOverEquivalence B V S hV hS g).fullyFaithfulFunctor.preimage
      (Over.isoMk e he).hom)).left = e.hom
  rw [Functor.FullyFaithful.map_preimage]
  rfl

/-- The inverse of an isomorphism with a formal spectrum over `V`, whose attached morphism is read
from an isomorphism of attached sheaves, is read from the inverse isomorphism. -/
private theorem smallerBaseSheafFunctor_map_inv_of_formalSpectrum {G : FppfSheaf B V hV}
    {A : Type u} [CommRing A] [TopologicalSpace A] {D : QuotientSystem B S hS A}
    {D₀ : QuotientSystem B V hV A} (hD₀ : ∀ J, D₀.overS J ≫ g.hom = D.overS J)
    (e : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅ formalSpectrum D)
    (e₀ : G ≅ formalSpectrum D₀)
    (he₀ : (smallerBaseSheafFunctor B V S hV hS g).map e₀.hom =
      e.hom ≫ (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D₀ D hD₀).inv) :
    (smallerBaseSheafFunctor B V S hV hS g).map e₀.inv =
      (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D₀ D hD₀).hom ≫ e.inv := by
  rw [← cancel_epi ((Ψ).map e₀.hom), ← (Ψ).map_comp, Iso.hom_inv_id, (Ψ).map_id, he₀]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]

/-- The structure morphism of a formal spectrum over `V` presenting an attached sheaf agrees, via
the comparison of formal spectra, with that of the sheaf. -/
private theorem smallerBaseFormalSpectrumIsoOfCompatible_inv_str_of_iso {G : FppfSheaf B V hV}
    {A : Type u} [CommRing A] [TopologicalSpace A] {D : QuotientSystem B S hS A}
    {D₀ : QuotientSystem B V hV A} (hD₀ : ∀ J, D₀.overS J ≫ g.hom = D.overS J)
    (e : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅ formalSpectrum D)
    (e₀ : G ≅ formalSpectrum D₀)
    (he₀ : (smallerBaseSheafFunctor B V S hV hS g).map e₀.hom =
      e.hom ≫ (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D₀ D hD₀).inv) :
    (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D₀ D hD₀).inv ≫
      smallerBaseStr B V S hV hS g (formalSpectrum D₀) =
      e.inv ≫ smallerBaseStr B V S hV hS g G := by
  rw [← smallerBaseSheafFunctor_map_comp_str B V S hV hS g e₀.hom, he₀]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **A quotient system presenting an attached sheaf comes from the larger base.** If the sheaf
on the big fppf site of `S` attached to `G` is the formal spectrum over `S` of a quotient system
`D`, then the structure morphism of `G` to `V` makes `D` a quotient system over `V` whose formal
spectrum is `G`, compatibly with the comparison of formal spectra. -/
theorem exists_quotientSystem_iso_of_smallerBaseSheafFunctor (G : FppfSheaf B V hV)
    (D : QuotientSystem B S hS A)
    (e : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅ formalSpectrum D) :
    ∃ (D₀ : QuotientSystem B V hV A) (hD₀ : ∀ J, D₀.overS J ≫ g.hom = D.overS J)
      (e₀ : G ≅ formalSpectrum D₀),
      (smallerBaseSheafFunctor B V S hV hS g).map e₀.hom =
        e.hom ≫ (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D₀ D hD₀).inv := by
  obtain ⟨ψ, hψ, hψx⟩ := exists_smallerBaseHom_of_colimit B V S hV hS g
    (D.diagram ⋙ BigAffineFppf.inclusion B S hS) (e.inv ≫ smallerBaseStr B V S hV hS g G)
  let D₀ : QuotientSystem B V hV A :=
    { inSite := D.inSite
      overS := fun J => (ψ (OrderDual.toDual J)).left.hom
      compatible := fun J L hJL => congrArg (fun k => k.left.hom)
        (hψ (homOfLE hJL : OrderDual.toDual L ⟶ OrderDual.toDual J)) }
  have hD₀ : ∀ J, D₀.overS J ≫ g.hom = D.overS J := fun J =>
    congrArg (fun k => k.hom) (Over.w (ψ (OrderDual.toDual J)))
  let iD := smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D₀ D hD₀
  have hK : ∀ K, ψ K = (BigAffineFppf.inclusion B S hS).map
        (smallerBaseStageIso B V S hV hS g D₀ D hD₀ (OrderDual.ofDual K)).inv ≫
      (Over.homMk ((BigAffineFppf.inclusion B V hV).obj (D₀.diagram.obj K)).hom rfl :
        (Over.map g).obj ((BigAffineFppf.inclusion B V hV).obj (D₀.diagram.obj K)) ⟶
          Over.mk g) := by
    intro K
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change (ψ K).left.hom = 𝟙 _ ≫ (ψ K).left.hom
    rw [Category.id_comp]
  have hstr : e.inv ≫ smallerBaseStr B V S hV hS g G =
      iD.inv ≫ smallerBaseStr B V S hV hS g (formalSpectrum D₀) :=
    colimit.hom_ext fun K => (hψx K).trans <|
      (congrArg (fun k => (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
        ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app
          (Over.mk g)).inv) (hK K)).trans
      (formalSpectrumInclusion_smallerBaseFormalSpectrumIsoOfCompatible_inv_str B V S hV hS g D₀
        D hD₀ K).symm
  have he : (e ≪≫ iD.symm).hom ≫ smallerBaseStr B V S hV hS g (formalSpectrum D₀) =
      smallerBaseStr B V S hV hS g G := by
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hstr, Iso.hom_inv_id_assoc]
  exact ⟨D₀, hD₀, smallerBaseLiftIso B V S hV hS g (e ≪≫ iD.symm) he,
    smallerBaseSheafFunctor_map_smallerBaseLiftIso_hom B V S hV hS g _ he⟩

/-- The comparisons of quotient stages over `V` and over `S` of compatible quotient systems are
compatible with the stage maps of continuous homomorphisms with the same ring map. -/
theorem smallerBaseStageIso_hom_naturality {D : QuotientSystem B V hV A}
    {D' : QuotientSystem B S hS A} (hD : ∀ J, D.overS J ≫ g.hom = D'.overS J)
    {E : QuotientSystem B V hV C} {E' : QuotientSystem B S hS C}
    (hE : ∀ J, E.overS J ≫ g.hom = E'.overS J) (fV : ContinuousHom D E)
    (f : ContinuousHom D' E') (hf : f.toRingHom = fV.toRingHom)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
    (hJK : J.1 ≤ Ideal.comap fV.toRingHom K.1) (hJK' : J.1 ≤ Ideal.comap f.toRingHom K.1) :
    (Over.map g).map ((BigAffineFppf.inclusion B V hV).map (fV.stageMap J K hJK)) ≫
        (BigAffineFppf.inclusion B S hS).map (smallerBaseStageIso B V S hV hS g D D' hD J).hom =
      (BigAffineFppf.inclusion B S hS).map (smallerBaseStageIso B V S hV hS g E E' hE K).hom ≫
        (BigAffineFppf.inclusion B S hS).map (f.stageMap J K hJK') := by
  have hq : ∀ (φ₁ φ₂ : A →+* C) (_ : φ₁ = φ₂) (h₁ : J.1 ≤ Ideal.comap φ₁ K.1)
      (h₂ : J.1 ≤ Ideal.comap φ₂ K.1),
      Ideal.quotientMap K.1 φ₁ h₁ = Ideal.quotientMap K.1 φ₂ h₂ := by
    rintro _ _ rfl _ _
    rfl
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map _ ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map _
  rw [Category.comp_id, Category.id_comp, hq _ _ hf.symm]

/-- The comparisons of formal spectra over `V` and over `S` of compatible quotient systems are
compatible with the maps of formal spectra. -/
theorem smallerBaseFormalSpectrumIsoOfCompatible_naturality_of_compatible
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B V hV A}
    {D' : QuotientSystem B S hS A} (hD : ∀ J, D.overS J ≫ g.hom = D'.overS J)
    {E : QuotientSystem B V hV C} {E' : QuotientSystem B S hS C}
    (hE : ∀ J, E.overS J ≫ g.hom = E'.overS J) (fV : ContinuousHom D E)
    (f : ContinuousHom D' E') (hf : f.toRingHom = fV.toRingHom) :
    (smallerBaseSheafFunctor B V S hV hS g).map (formalSpectrumMap hA fV) ≫
        (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D D' hD).hom =
      (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g E E' hE).hom ≫
        formalSpectrumMap hA f := by
  apply (isColimitOfPreserves (smallerBaseSheafFunctor B V S hV hS g)
    (colimit.isColimit (formalSpectrumDiagram E))).hom_ext
  intro K
  obtain ⟨I, hI⟩ := hA.1
  let K' := OrderDual.ofDual K
  let J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨I ⊓ Ideal.comap fV.toRingHom K'.1, ⟨by
      change IsOpen ((I : Set A) ∩ fV.toRingHom ⁻¹' (K'.1 : Set C))
      exact hI.1.inter (K'.2.1.preimage fV.continuous),
      fun x hx => hI.2 x (Ideal.mem_inf.mp hx).1⟩⟩
  have hJK : J.1 ≤ Ideal.comap fV.toRingHom K'.1 := inf_le_right
  have hJK' : J.1 ≤ Ideal.comap f.toRingHom K'.1 := by rwa [hf]
  let m := (BigAffineFppf.inclusion B V hV).map (fV.stageMap J K' hJK)
  let N := (smallerBaseSheafifiedYonedaIso B V S hV hS g).hom
  let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have h1 := (((Ψ).map_comp _ _).symm.trans
    (congrArg (Ψ).map (formalSpectrumMap_spec hA fV J K' hJK))).trans ((Ψ).map_comp _ _)
  have hN := N.naturality m
  have h2 := formalSpectrumMap_spec hA f J K' hJK'
  have hD' := smallerBaseFormalSpectrumIsoOfCompatible_ι B V S hV hS g D D' hD (OrderDual.toDual J)
  have hE' := smallerBaseFormalSpectrumIsoOfCompatible_ι B V S hV hS g E E' hE K
  have h3 : sY.map ((Over.map g).map m) ≫ sY.map ((BigAffineFppf.inclusion B S hS).map
      (smallerBaseStageIso B V S hV hS g D D' hD J).hom) =
      sY.map ((BigAffineFppf.inclusion B S hS).map
        (smallerBaseStageIso B V S hV hS g E E' hE K').hom) ≫
        sY.map ((BigAffineFppf.inclusion B S hS).map (f.stageMap J K' hJK')) :=
    (sY.map_comp _ _).symm.trans ((congrArg sY.map
      (smallerBaseStageIso_hom_naturality B V S hV hS g hD hE fV f hf J K' hJK hJK')).trans
        (sY.map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D D' hD).hom)
      h1).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hD').trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hN).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h3).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2.symm))))).trans <|
    (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hE'.symm).trans
      (Category.assoc _ _ _)

/-- A continuous homomorphism of quotient systems over `S` whose formal spectrum map respects the
structure morphisms of the formal spectra of compatible quotient systems over `V` respects the
quotient systems over `V`. -/
theorem quotientMap_comp_overS_of_formalSpectrumMap [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} {D₀ : QuotientSystem B V hV A} {E₀ : QuotientSystem B V hV C}
    (hD₀ : ∀ J, D₀.overS J ≫ g.hom = D.overS J) (hE₀ : ∀ J, E₀.overS J ≫ g.hom = E.overS J)
    (k : ContinuousHom D E)
    (hk : formalSpectrumMap hA k ≫
        (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D₀ D hD₀).inv ≫
          smallerBaseStr B V S hV hS g (formalSpectrum D₀) =
      (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g E₀ E hE₀).inv ≫
        smallerBaseStr B V S hV hS g (formalSpectrum E₀))
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
    (hJK : J.1 ≤ Ideal.comap k.toRingHom K.1) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 k.toRingHom hJK)) ≫ D₀.overS J =
      E₀.overS K := by
  have e2 : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (k.stageMap J K hJK)) ≫
      formalSpectrumInclusion D (OrderDual.toDual J) ≫
        (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D₀ D hD₀).inv ≫
        smallerBaseStr B V S hV hS g (formalSpectrum D₀) =
      formalSpectrumInclusion E (OrderDual.toDual K) ≫
        (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g E₀ E hE₀).inv ≫
        smallerBaseStr B V S hV hS g (formalSpectrum E₀) :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (formalSpectrumMap_spec hA k J K hJK).symm).trans <|
      (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hk)
  have e3 : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (k.stageMap J K hJK) ≫
        ((BigAffineFppf.inclusion B S hS).map
          (smallerBaseStageIso B V S hV hS g D₀ D hD₀ J).inv ≫
        (Over.homMk ((BigAffineFppf.inclusion B V hV).obj (D₀.diagram.obj
          (OrderDual.toDual J))).hom rfl :
          (Over.map g).obj ((BigAffineFppf.inclusion B V hV).obj
            (D₀.diagram.obj (OrderDual.toDual J))) ⟶ Over.mk g))) ≫
        ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app
          (Over.mk g)).inv =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map
          (smallerBaseStageIso B V S hV hS g E₀ E hE₀ K).inv ≫
        (Over.homMk ((BigAffineFppf.inclusion B V hV).obj (E₀.diagram.obj
          (OrderDual.toDual K))).hom rfl :
          (Over.map g).obj ((BigAffineFppf.inclusion B V hV).obj
            (E₀.diagram.obj (OrderDual.toDual K))) ⟶ Over.mk g)) ≫
        ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app
          (Over.mk g)).inv :=
    (congrArg (· ≫ ((Sheaf.uliftYonedaIsoSheafifiedYoneda
        (BigFppfOver.topology B S hS)).app (Over.mk g)).inv)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _)).trans <|
      (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
        (formalSpectrumInclusion_smallerBaseFormalSpectrumIsoOfCompatible_inv_str B V S hV hS g
          D₀ D hD₀ (OrderDual.toDual J)).symm).trans (e2.trans
        (formalSpectrumInclusion_smallerBaseFormalSpectrumIsoOfCompatible_inv_str B V S hV hS g
          E₀ E hE₀ (OrderDual.toDual K)))
  have e4 := (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_injective
    ((cancel_mono ((Sheaf.uliftYonedaIsoSheafifiedYoneda
      (BigFppfOver.topology B S hS)).app (Over.mk g)).inv).mp e3)
  have e5 : Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 k.toRingHom hJK)) ≫
      (𝟙 _ ≫ D₀.overS J) = 𝟙 _ ≫ E₀.overS K := congrArg (fun k => k.left.hom) e4
  simpa using e5

/-- **A formal spectrum map of attached sheaves comes from the larger base.** A morphism over `V`
whose attached morphism is the formal spectrum map of a continuous homomorphism of quotient
systems over `S` is the formal spectrum map of a continuous homomorphism, with the same ring map,
of quotient systems over `V`. -/
theorem exists_formalSpectrumMap_of_smallerBaseSheafFunctor [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A) {U₀ U₀' : FppfSheaf B V hV}
    (t₀ : U₀ ⟶ U₀') {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (eU : (smallerBaseSheafFunctor B V S hV hS g).obj U₀ ≅ formalSpectrum E)
    (eU' : (smallerBaseSheafFunctor B V S hV hS g).obj U₀' ≅ formalSpectrum D)
    (k : ContinuousHom D E)
    (hk : (smallerBaseSheafFunctor B V S hV hS g).map t₀ =
      eU.hom ≫ formalSpectrumMap hA k ≫ eU'.inv) :
    ∃ (D₀ : QuotientSystem B V hV A) (E₀ : QuotientSystem B V hV C)
      (eU₀ : U₀ ≅ formalSpectrum E₀) (eU₀' : U₀' ≅ formalSpectrum D₀) (k₀ : ContinuousHom D₀ E₀),
      k₀.toRingHom = k.toRingHom ∧ t₀ = eU₀.hom ≫ formalSpectrumMap hA k₀ ≫ eU₀'.inv := by
  obtain ⟨E₀, hE₀, eU₀, heU₀⟩ :=
    exists_quotientSystem_iso_of_smallerBaseSheafFunctor B V S hV hS g U₀ E eU
  obtain ⟨D₀, hD₀, eU₀', heU₀'⟩ :=
    exists_quotientSystem_iso_of_smallerBaseSheafFunctor B V S hV hS g U₀' D eU'
  have hD := smallerBaseFormalSpectrumIsoOfCompatible_inv_str_of_iso B V S hV hS g hD₀ eU' eU₀'
    heU₀'
  have hE := smallerBaseFormalSpectrumIsoOfCompatible_inv_str_of_iso B V S hV hS g hE₀ eU eU₀ heU₀
  have ht : formalSpectrumMap hA k ≫ eU'.inv ≫ smallerBaseStr B V S hV hS g U₀' =
      eU.inv ≫ smallerBaseStr B V S hV hS g U₀ := by
    rw [← smallerBaseSheafFunctor_map_comp_str B V S hV hS g t₀, hk]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  let k₀ : ContinuousHom D₀ E₀ :=
    { toRingHom := k.toRingHom
      continuous := k.continuous
      overS := quotientMap_comp_overS_of_formalSpectrumMap B V S hV hS g hA hD₀ hE₀ k
        (by rw [hD, hE, ht]) }
  have hinv := smallerBaseSheafFunctor_map_inv_of_formalSpectrum B V S hV hS g hD₀ eU' eU₀' heU₀'
  refine ⟨D₀, E₀, eU₀, eU₀', k₀, rfl, (Ψ).map_injective ?_⟩
  rw [(Ψ).map_comp, (Ψ).map_comp, heU₀, hinv, hk, ← (Iso.inv_comp_eq _).mpr
    (smallerBaseFormalSpectrumIsoOfCompatible_naturality_of_compatible B V S hV hS g hA hD₀ hE₀ k₀
      k rfl)]
  simp only [Category.assoc]

end QuotientSystem

/-! ### Rig-étale and rig-surjective morphisms -/

/-- **Rig-étaleness (Stacks 0AQM) is carried to the smaller base.** A morphism of affine étale
charts of the attached morphism, presented by formal spectra over `S`, is attached to a morphism
of affine étale charts over `V`: the charts are attached sheaves
(`AlgebraicGeometry.FormalSpace.exists_smallerBaseSheafFunctor_lift`), their presenting quotient
systems come from quotient systems over `V`
(`AlgebraicGeometry.FormalSpace.exists_quotientSystem_iso_of_smallerBaseSheafFunctor`), and the
continuous homomorphism of the presentations is one over `V`, with the same ring map. -/
theorem isRigEtale_smallerBaseSheafFunctor {G G' : FppfSheaf B V hV} (f : G ⟶ G')
    (h : IsRigEtale B V hV f) :
    IsRigEtale B S hS ((smallerBaseSheafFunctor B V S hV hS g).map f) := by
  intro U U' hU hU' a b t ha hb hae hbe hcomm A C _ _ _ _ _ _ _ _ _ _ hAadic hCadic hA D E eU eU'
    k hk
  obtain ⟨U₀, a₀, εU, ha₀⟩ := exists_smallerBaseSheafFunctor_lift B V S hV hS g G a
  obtain ⟨U₀', b₀, εU', hb₀⟩ := exists_smallerBaseSheafFunctor_lift B V S hV hS g G' b
  have hstr : (εU.hom ≫ t ≫ εU'.inv) ≫ smallerBaseStr B V S hV hS g U₀' =
      smallerBaseStr B V S hV hS g U₀ := by
    rw [← smallerBaseSheafFunctor_map_comp_str B V S hV hS g b₀,
      ← smallerBaseSheafFunctor_map_comp_str B V S hV hS g a₀, hb₀, ha₀,
      ← smallerBaseSheafFunctor_map_comp_str B V S hV hS g f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc a, hcomm, Category.assoc]
  let t₀ : U₀ ⟶ U₀' := smallerBaseLift B V S hV hS g (εU.hom ≫ t ≫ εU'.inv) hstr
  have ht₀ : (Ψ).map t₀ = εU.hom ≫ t ≫ εU'.inv :=
    smallerBaseSheafFunctor_map_smallerBaseLift B V S hV hS g _ hstr
  have hU₀ : IsAffineFormalAlgebraicSpace B V hV U₀ :=
    (isAffineFormalAlgebraicSpace_smallerBaseSheafFunctor_iff B V S hV hS g U₀).mp
      (isAffineFormalAlgebraicSpace_of_iso B S hS εU.symm hU)
  have hU₀' : IsAffineFormalAlgebraicSpace B V hV U₀' :=
    (isAffineFormalAlgebraicSpace_smallerBaseSheafFunctor_iff B V S hV hS g U₀').mp
      (isAffineFormalAlgebraicSpace_of_iso B S hS εU'.symm hU')
  have ha₀' : IsRepresentableEtale B V hV a₀ := by
    refine (isRepresentableEtale_smallerBaseSheafFunctor_map_iff B V S hV hS g a₀).mp ?_
    rw [ha₀]
    exact IsRepresentableEtale.comp B S hS (isRepresentableEtale_of_isIso B S hS εU.hom) ⟨ha, hae⟩
  have hb₀' : IsRepresentableEtale B V hV b₀ := by
    refine (isRepresentableEtale_smallerBaseSheafFunctor_map_iff B V S hV hS g b₀).mp ?_
    rw [hb₀]
    exact IsRepresentableEtale.comp B S hS (isRepresentableEtale_of_isIso B S hS εU'.hom) ⟨hb, hbe⟩
  have hcomm₀ : a₀ ≫ f = t₀ ≫ b₀ := by
    apply (Ψ).map_injective
    rw [(Ψ).map_comp, (Ψ).map_comp, ha₀, ht₀, hb₀]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (εU.hom ≫ ·) hcomm
  obtain ⟨D₀, E₀, eU₀, eU₀', k₀, hk₀, ht₀'⟩ :=
    exists_formalSpectrumMap_of_smallerBaseSheafFunctor B V S hV hS g hA t₀ (εU ≪≫ eU)
      (εU' ≪≫ eU') k (by rw [ht₀, hk]; simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc])
  rw [← hk₀]
  exact h U₀ U₀' hU₀ hU₀' a₀ b₀ t₀ ha₀'.1 hb₀'.1 ha₀'.2 hb₀'.2 hcomm₀ A C hAadic hCadic hA D₀
    E₀ eU₀ eU₀' k₀ ht₀'

/-- **Rig-surjectivity (Stacks 0AQQ) is carried to the smaller base.** An adic point
`Spf R ⟶ Y` over `S` of the attached target is attached to an adic point over `V`, presented by a
quotient system over `V`; a lift of that point over `V` along an extension `R ⊂ R'` gives a lift
over `S`, along the composite quotient system of `R'`. -/
theorem isRigSurjective_smallerBaseSheafFunctor {G G' : FppfSheaf B V hV} (f : G ⟶ G')
    (h : IsRigSurjective B V hV f) :
    IsRigSurjective B S hS ((smallerBaseSheafFunctor B V S hV hS g).map f) := by
  intro R _ _ _ _ _ _ hadic hcomp hR D p hp
  obtain ⟨G₀, p₀, ε, hp₀⟩ := exists_smallerBaseSheafFunctor_lift B V S hV hS g G' p
  obtain ⟨D₀, hD₀, e₀, he₀⟩ :=
    exists_quotientSystem_iso_of_smallerBaseSheafFunctor B V S hV hS g G₀ D ε
  have hinv := smallerBaseSheafFunctor_map_inv_of_formalSpectrum B V S hV hS g hD₀ ε e₀ he₀
  let p₁ : formalSpectrum D₀ ⟶ G' := e₀.inv ≫ p₀
  have hp₁ : (Ψ).map p₁ =
      (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D₀ D hD₀).hom ≫ p := by
    rw [(Ψ).map_comp, hinv, hp₀]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B V hV p₁.hom := by
    refine (isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff B V S hV hS g
      p₁.hom).mp ?_
    rw [← smallerBaseSheafFunctor_map_hom, hp₁]
    exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
      (isRepresentableEtale_of_isIso B S hS
        (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D₀ D hD₀).hom).1 hp
  obtain ⟨R', i1, i2, i3, i4, i5, i6, i7, i8, hadic', hcomp', D'₀, e, x, he, hx⟩ :=
    h R hadic hcomp hR D₀ p₁ hrep
  let eS : ContinuousHom D (smallerBaseQuotientSystem B V S hV hS g D'₀) :=
    { toRingHom := e.toRingHom
      continuous := e.continuous
      overS := fun J K hJK => by
        change _ ≫ D.overS J = D'₀.overS K ≫ g.hom
        rw [← e.overS J K hJK, Category.assoc, hD₀] }
  have hnat := smallerBaseFormalSpectrumIsoOfCompatible_naturality_of_compatible B V S hV hS g hR
    hD₀ (fun _ => rfl) e eS rfl
  refine ⟨R', i1, i2, i3, i4, i5, i6, i7, i8, hadic', hcomp',
    smallerBaseQuotientSystem B V S hV hS g D'₀, eS,
    (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D'₀
      (smallerBaseQuotientSystem B V S hV hS g D'₀) (fun _ => rfl)).inv ≫ (Ψ).map x, he, ?_⟩
  rw [Category.assoc, ← (Ψ).map_comp, hx, (Ψ).map_comp, hp₁]
  exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) hnat).trans
    (Category.assoc _ _ _)))).trans (Iso.inv_hom_id_assoc _ _)

/-! ### Formal modifications -/

/-- **Formal modifications (Stacks 0GDK) are carried to the smaller base.** The attached
morphism over `S` of a formal modification over `V` is a formal modification over `S`. -/
theorem isFormalModification_smallerBaseSheafFunctor {G G' : FppfSheaf B V hV} (f : G ⟶ G')
    (h : IsFormalModification B V hV f) :
    IsFormalModification B S hS ((smallerBaseSheafFunctor B V S hV hS g).map f) where
  isLocallyNoetherian_source :=
    isLocallyNoetherian_smallerBaseSheafFunctor B V S hV hS g G h.isLocallyNoetherian_source
  isLocallyNoetherian_target :=
    isLocallyNoetherian_smallerBaseSheafFunctor B V S hV hS g G' h.isLocallyNoetherian_target
  isProper := (isProper_smallerBaseSheafFunctor_map_iff B V S hV hS g f).mpr h.isProper
  isRigEtale := isRigEtale_smallerBaseSheafFunctor B V S hV hS g f h.isRigEtale
  isRigSurjective := isRigSurjective_smallerBaseSheafFunctor B V S hV hS g f h.isRigSurjective
  isRigSurjective_diagonal := by
    have hd := smallerBaseSheafFunctor_map_diagonal B V S hV hS g f ((Ψ).map f) (Iso.refl _)
      (Iso.refl _) (by simp)
    have hd' : pullback.diagonal ((Ψ).map f) = (Ψ).map (pullback.diagonal f) ≫
        (PreservesPullback.iso (Ψ) f f ≪≫ asIso (pullback.map ((Ψ).map f) ((Ψ).map f)
          ((Ψ).map f) ((Ψ).map f) (Iso.refl ((Ψ).obj G)).hom (Iso.refl ((Ψ).obj G)).hom
          (Iso.refl ((Ψ).obj G')).hom (by simp) (by simp))).hom :=
      (hd.trans (Category.id_comp _)).symm
    rw [hd']
    exact IsRigSurjective.comp_isIso _ _
      (isRigSurjective_smallerBaseSheafFunctor B V S hV hS g (pullback.diagonal f)
        h.isRigSurjective_diagonal)

end AlgebraicGeometry.FormalSpace

end
