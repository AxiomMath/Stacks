module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonalRigSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseFormalSpectrum

/-!
# Rig-surjectivity and formal modifications over a smaller base

Let `g : V ⟶ S` be a morphism of a big fppf site `B`. This file shows that rig-surjectivity
(Stacks 0AQQ) and being a formal modification (Stacks 0GDK) descend along the change of base
`AlgebraicGeometry.FormalSpace.smallerBaseSheafFunctor` from fppf sheaves on the big fppf site of
`V` to fppf sheaves on the big fppf site of `S`.

A lift of an adic point over `S` is along a formal spectrum `Spf R'` presented by a quotient
system over `S`; the lift itself maps `Spf R'` to `V`, which makes the quotient system one over
`V` (`AlgebraicGeometry.FormalSpace.exists_smallerBaseHom_of_colimit`), and the formal spectrum
over `V` of that system is attached to `Spf R'`
(`AlgebraicGeometry.FormalSpace.smallerBaseFormalSpectrumIsoOfCompatible`).

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSurjective_of_smallerBaseSheafFunctor`.
* `AlgebraicGeometry.FormalSpace.isFormalModification_of_smallerBaseSheafFunctor`.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

attribute [local instance] bigFppfOver_subcanonical

/-! ### Structure morphisms -/

/-- A morphism from a colimit of sheafified representable sheaves over `S` to the representable
sheaf of `g` is given by compatible morphisms of the indices to `V`. -/
theorem exists_smallerBaseHom_of_colimit {I : Type w} [Category.{w'} I]
    [HasColimitsOfShape I (FppfSheaf B S hS)] (F : I ⥤ BigFppfOver B S hS)
    (c : colimit (F ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ⟶
      smallerBaseTarget B V S hV hS g) :
    ∃ (ψ : ∀ i, F.obj i ⟶ Over.mk g) (_ : ∀ ⦃i j : I⦄ (f : i ⟶ j), F.map f ≫ ψ j = ψ i),
      ∀ i, colimit.ι (F ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ c =
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (ψ i) ≫
          ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app
            (Over.mk g)).inv := by
  let rS := (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}
  let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let ι := Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)
  let ψ : ∀ i, F.obj i ⟶ Over.mk g := fun i =>
    rS.preimage ((ι.app (F.obj i)).hom ≫ colimit.ι (F ⋙ sY) i ≫ c)
  have hψ : ∀ i, rS.map (ψ i) = (ι.app (F.obj i)).hom ≫ colimit.ι (F ⋙ sY) i ≫ c :=
    fun i => rS.map_preimage _
  have key : ∀ i, colimit.ι (F ⋙ sY) i ≫ c = sY.map (ψ i) ≫ (ι.app (Over.mk g)).inv := by
    intro i
    rw [← NatIso.naturality_1 ι (ψ i), hψ, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, Iso.app_hom, Iso.app_inv, Iso.hom_inv_id_app, Category.comp_id,
      Iso.inv_hom_id_app_assoc]
  refine ⟨ψ, fun i j f => sY.map_injective ?_, key⟩
  rw [← cancel_mono (ι.app (Over.mk g)).inv, sY.map_comp, Category.assoc, ← key, ← key]
  exact colimit.w_assoc (F ⋙ sY) f c

/-- The structural morphism of a sheafified representable sheaf over `V`, read through the
comparison `AlgebraicGeometry.FormalSpace.smallerBaseSheafifiedYonedaIso`. -/
theorem smallerBaseSheafifiedYonedaIso_hom_app_comp (T : BigFppfOver B V hV) :
    (smallerBaseSheafifiedYonedaIso B V S hV hS g).hom.app T ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (Over.homMk T.hom rfl : (Over.map g).obj T ⟶ Over.mk g) =
      smallerBaseStr B V S hV hS g ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B V hV)).obj T) ≫
        ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app
          (Over.mk g)).hom := by
  have h1 : ((smallerBaseSheafFunctorYonedaIso B V S hV hS g).app T).hom ≫
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map
        (Over.homMk T.hom rfl : (Over.map g).obj T ⟶ Over.mk g) =
      smallerBaseStr B V S hV hS g ((BigFppfOver.topology B V hV).uliftYoneda.{u + 1}.obj T) := by
    ext W p
    exact ULift.ext (Over.OverMorphism.ext (Over.w p.2.down))
  have h2 := (Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).hom.naturality
    (Over.homMk T.hom rfl : (Over.map g).obj T ⟶ Over.mk g)
  have h3 := smallerBaseSheafFunctor_map_comp_str B V S hV hS g
    ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B V hV)).inv.app T)
  exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h2.symm).trans (Category.assoc _ _ _).symm))).trans <|
    (congrArg (_ ≫ · ≫ _) h1).trans <| (Category.assoc _ _ _).symm.trans <|
    congrArg (· ≫ _) h3

/-! ### Formal spectra of compatible quotient systems -/

section QuotientSystem

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [CommRing C] [TopologicalSpace C]

/-- The quotient stages of a system over `V` and of a system over `S` with the same quotient
spectra and compatible structure morphisms are isomorphic over `S`. -/
def smallerBaseStageIso (D : QuotientSystem B V hV A) (D' : QuotientSystem B S hS A)
    (hD : ∀ J, D.overS J ≫ g.hom = D'.overS J)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (smallerBaseAffineFunctor B V S hV hS g).obj (D.stage J) ≅ D'.stage J :=
  (ObjectProperty.fullyFaithfulι _).preimageIso (Over.isoMk (Iso.refl _) (by
    apply ObjectProperty.hom_ext
    change 𝟙 _ ≫ D'.overS J = D.overS J ≫ g.hom
    rw [Category.id_comp, hD]))

/-- The diagrams of quotient stages of compatible systems over `V` and over `S` are
isomorphic. -/
def smallerBaseDiagramIso (D : QuotientSystem B V hV A) (D' : QuotientSystem B S hS A)
    (hD : ∀ J, D.overS J ≫ g.hom = D'.overS J) :
    D.diagram ⋙ smallerBaseAffineFunctor B V S hV hS g ≅ D'.diagram :=
  NatIso.ofComponents (fun J => smallerBaseStageIso B V S hV hS g D D' hD (OrderDual.ofDual J))
    (by
      intro J L f
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change Spec.map _ ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map _
      rw [Category.comp_id, Category.id_comp])

/-- The attached sheaf of the formal spectrum over `V` of a quotient system is the formal spectrum
over `S` of any compatible system. -/
def smallerBaseFormalSpectrumIsoOfCompatible (D : QuotientSystem B V hV A)
    (D' : QuotientSystem B S hS A)
    (hD : ∀ J, D.overS J ≫ g.hom = D'.overS J) :
    (smallerBaseSheafFunctor B V S hV hS g).obj (formalSpectrum D) ≅ formalSpectrum D' :=
  preservesColimitIso (smallerBaseSheafFunctor B V S hV hS g) (formalSpectrumDiagram D) ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (D.diagram ⋙ BigAffineFppf.inclusion B V hV)
      (smallerBaseSheafifiedYonedaIso B V S hV hS g) ≪≫
      Functor.isoWhiskerRight (smallerBaseDiagramIso B V S hV hS g D D' hD)
        (BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))

/-- On the image of the inclusion of a quotient stage, the comparison
`smallerBaseFormalSpectrumIsoOfCompatible` is the sheafified Yoneda comparison followed by the
isomorphism of stages `smallerBaseStageIso` and the inclusion of the stage over `S`. -/
@[reassoc]
theorem smallerBaseFormalSpectrumIsoOfCompatible_ι (D : QuotientSystem B V hV A)
    (D' : QuotientSystem B S hS A) (hD : ∀ J, D.overS J ≫ g.hom = D'.overS J)
    (J : OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (smallerBaseSheafFunctor B V S hV hS g).map (formalSpectrumInclusion D J) ≫
        (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D D' hD).hom =
      (smallerBaseSheafifiedYonedaIso B V S hV hS g).hom.app
          ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)) ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (smallerBaseStageIso B V S hV hS g D D' hD (OrderDual.ofDual J)).hom) ≫
        formalSpectrumInclusion D' J :=
  (ι_preservesColimitIso_hom_assoc _ _ J _).trans
    ((HasColimit.ι_isoOfNatIso_hom _ J).trans (Category.assoc _ _ _))

/-- The comparisons of formal spectra are compatible with the maps of formal spectra. -/
theorem smallerBaseFormalSpectrumIsoOfCompatible_naturality [IsTopologicalRing A]
    [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B V hV A}
    {E : QuotientSystem B V hV C} {E' : QuotientSystem B S hS C}
    (hE : ∀ J, E.overS J ≫ g.hom = E'.overS J) (fV : ContinuousHom D E)
    (f : ContinuousHom (smallerBaseQuotientSystem B V S hV hS g D) E')
    (hf : f.toRingHom = fV.toRingHom) :
    (smallerBaseSheafFunctor B V S hV hS g).map (formalSpectrumMap hA fV) ≫
        (smallerBaseFormalSpectrumIso B V S hV hS g D).hom =
      (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g E E' hE).hom ≫
        formalSpectrumMap hA f := by
  refine (isColimitOfPreserves (smallerBaseSheafFunctor B V S hV hS g)
    (colimit.isColimit (formalSpectrumDiagram E))).hom_ext fun K => ?_
  obtain ⟨I, hI⟩ := hA.1
  let K' := OrderDual.ofDual K
  let J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨I ⊓ Ideal.comap fV.toRingHom K'.1, hI.1.inter (K'.2.1.preimage fV.continuous),
      fun x hx => hI.2 x (Ideal.mem_inf.mp hx).1⟩
  have hJK : J.1 ≤ Ideal.comap fV.toRingHom K'.1 := inf_le_right
  have hJK' : J.1 ≤ Ideal.comap f.toRingHom K'.1 := by rwa [hf]
  let m := (BigAffineFppf.inclusion B V hV).map (fV.stageMap J K' hJK)
  let Ψ := smallerBaseSheafFunctor B V S hV hS g
  let N := (smallerBaseSheafifiedYonedaIso B V S hV hS g).hom
  let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have h1 := ((Ψ.map_comp _ _).symm.trans
    (congrArg Ψ.map (formalSpectrumMap_spec hA fV J K' hJK))).trans (Ψ.map_comp _ _)
  have hN := N.naturality m
  have h2 := formalSpectrumMap_spec hA f J K' hJK'
  have hD := smallerBaseFormalSpectrumIso_ι B V S hV hS g D (OrderDual.toDual J)
  have hE' := smallerBaseFormalSpectrumIsoOfCompatible_ι B V S hV hS g E E' hE K
  have hq : ∀ (φ₁ φ₂ : A →+* C) (_ : φ₁ = φ₂) (h₁ : J.1 ≤ Ideal.comap φ₁ K'.1)
      (h₂ : J.1 ≤ Ideal.comap φ₂ K'.1),
      Ideal.quotientMap K'.1 φ₁ h₁ = Ideal.quotientMap K'.1 φ₂ h₂ := by
    rintro _ _ rfl _ _
    rfl
  have hm : (Over.map g).map m = (BigAffineFppf.inclusion B S hS).map
      (smallerBaseStageIso B V S hV hS g E E' hE K').hom ≫
        (BigAffineFppf.inclusion B S hS).map (f.stageMap J K' hJK') := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map _ = 𝟙 _ ≫ Spec.map _
    rw [Category.id_comp, hq _ _ hf.symm]
  have h3 : sY.map ((Over.map g).map m) = sY.map ((BigAffineFppf.inclusion B S hS).map
      (smallerBaseStageIso B V S hV hS g E E' hE K').hom) ≫
        sY.map ((BigAffineFppf.inclusion B S hS).map (f.stageMap J K' hJK')) :=
    (congrArg sY.map hm).trans (sY.map_comp _ _)
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (smallerBaseFormalSpectrumIso B V S hV hS g D).hom) h1).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hD).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hN).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ · ≫ _) h3).trans <|
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2.symm))).trans <|
    (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans <|
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hE'.symm).trans
      (Category.assoc _ _ _)

/-- The structural morphism of the attached sheaf of the formal spectrum over `V`, read on a
quotient stage through `AlgebraicGeometry.FormalSpace.smallerBaseSheafifiedYonedaIso`. -/
private theorem smallerBaseSheafifiedYonedaIso_inv_comp_map_inclusion_comp_str
    {A : Type u} [CommRing A] [TopologicalSpace A] (D : QuotientSystem B V hV A)
    (J : OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    ((smallerBaseSheafifiedYonedaIso B V S hV hS g).app
          ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J))).inv ≫
        (smallerBaseSheafFunctor B V S hV hS g).map (formalSpectrumInclusion D J) ≫
          smallerBaseStr B V S hV hS g (formalSpectrum D) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (Over.homMk ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)).hom rfl :
            (Over.map g).obj ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)) ⟶
              Over.mk g) ≫
        ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app
          (Over.mk g)).inv := by
  have h2 := smallerBaseSheafFunctor_map_comp_str B V S hV hS g (formalSpectrumInclusion D J)
  have h4 := (Iso.comp_inv_eq _).mpr (smallerBaseSheafifiedYonedaIso_hom_app_comp B V S hV hS g
    ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)))
  exact (congrArg (_ ≫ ·) (h2.trans h4.symm)).trans <|
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (Iso.inv_hom_id_assoc _ _)

/-- The structural morphism of the attached sheaf of a formal spectrum over `V`, read on the
quotient stages of the formal spectrum over `S` of the composite system. -/
theorem formalSpectrumInclusion_smallerBaseFormalSpectrumIso_inv_str
    (D : QuotientSystem B V hV A)
    (J : OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    formalSpectrumInclusion (smallerBaseQuotientSystem B V S hV hS g D) J ≫
        (smallerBaseFormalSpectrumIso B V S hV hS g D).inv ≫
          smallerBaseStr B V S hV hS g (formalSpectrum D) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (Over.homMk ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)).hom rfl :
            (Over.map g).obj ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)) ⟶
              Over.mk g) ≫
        ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app
          (Over.mk g)).inv := by
  let T := (BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)
  let N := (smallerBaseSheafifiedYonedaIso B V S hV hS g).app T
  have h1 : formalSpectrumInclusion (smallerBaseQuotientSystem B V S hV hS g D) J ≫
      (smallerBaseFormalSpectrumIso B V S hV hS g D).inv =
      N.inv ≫ (smallerBaseSheafFunctor B V S hV hS g).map (formalSpectrumInclusion D J) :=
    (Iso.comp_inv_eq _).mpr ((Category.assoc _ _ _).trans
      ((congrArg (N.inv ≫ ·) (smallerBaseFormalSpectrumIso_ι B V S hV hS g D J)).trans
        (N.inv_hom_id_assoc _))).symm
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h1).trans <|
    (Category.assoc _ _ _).trans
      (smallerBaseSheafifiedYonedaIso_inv_comp_map_inclusion_comp_str B V S hV hS g D J)

/-- The analogue of
`AlgebraicGeometry.FormalSpace.formalSpectrumInclusion_smallerBaseFormalSpectrumIso_inv_str` for
the comparison with a compatible system over `S`. -/
theorem formalSpectrumInclusion_smallerBaseFormalSpectrumIsoOfCompatible_inv_str
    (D : QuotientSystem B V hV A) (D' : QuotientSystem B S hS A)
    (hD : ∀ J, D.overS J ≫ g.hom = D'.overS J)
    (J : OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    formalSpectrumInclusion D' J ≫
        (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D D' hD).inv ≫
          smallerBaseStr B V S hV hS g (formalSpectrum D) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (smallerBaseStageIso B V S hV hS g D D' hD (OrderDual.ofDual J)).inv ≫
          (Over.homMk ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)).hom rfl :
            (Over.map g).obj ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)) ⟶
              Over.mk g)) ≫
        ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app
          (Over.mk g)).inv := by
  let T := (BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)
  let N := (smallerBaseSheafifiedYonedaIso B V S hV hS g).app T
  let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let iso := sY.mapIso ((BigAffineFppf.inclusion B S hS).mapIso
    (smallerBaseStageIso B V S hV hS g D D' hD (OrderDual.ofDual J)))
  let σ := (Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app (Over.mk g)
  have h1 : formalSpectrumInclusion D' J ≫
      (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D D' hD).inv =
      iso.inv ≫ N.inv ≫ (smallerBaseSheafFunctor B V S hV hS g).map (formalSpectrumInclusion D J) :=
    (Iso.comp_inv_eq _).mpr ((Category.assoc _ _ _).trans <| (congrArg (iso.inv ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (N.inv ≫ ·)
        (smallerBaseFormalSpectrumIsoOfCompatible_ι B V S hV hS g D D' hD J)).trans
        (N.inv_hom_id_assoc _)))).trans (iso.inv_hom_id_assoc _)).symm
  have h5 : sY.map ((BigAffineFppf.inclusion B S hS).map
            (smallerBaseStageIso B V S hV hS g D D' hD (OrderDual.ofDual J)).inv ≫
          (Over.homMk ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)).hom rfl :
            (Over.map g).obj ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj J)) ⟶
              Over.mk g)) = iso.inv ≫ sY.map (Over.homMk T.hom rfl :
            (Over.map g).obj T ⟶ Over.mk g) := sY.map_comp _ _
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h1).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (iso.inv ≫ ·) ((Category.assoc _ _ _).trans
      (smallerBaseSheafifiedYonedaIso_inv_comp_map_inclusion_comp_str B V S hV hS g D J))).trans <|
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h5.symm)

/-- A morphism from the formal spectrum of a quotient system over `S` to `V` makes the system
one over `V`, whose formal spectrum is attached to the given one compatibly with the morphism. -/
theorem exists_quotientSystem_of_hom_smallerBaseTarget (D' : QuotientSystem B S hS C)
    (c : formalSpectrum D' ⟶ smallerBaseTarget B V S hV hS g) :
    ∃ (D'V : QuotientSystem B V hV C) (hD'V : ∀ J, D'V.overS J ≫ g.hom = D'.overS J),
      c = (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D'V D' hD'V).inv ≫
        smallerBaseStr B V S hV hS g (formalSpectrum D'V) := by
  obtain ⟨ψ, hψ, hψc⟩ := exists_smallerBaseHom_of_colimit B V S hV hS g
    (D'.diagram ⋙ BigAffineFppf.inclusion B S hS) c
  let D'V : QuotientSystem B V hV C :=
    { inSite := D'.inSite
      overS := fun J => (ψ (OrderDual.toDual J)).left.hom
      compatible := fun J L hJL => congrArg (fun k => k.left.hom)
        (hψ (homOfLE hJL : OrderDual.toDual L ⟶ OrderDual.toDual J)) }
  have hD'V : ∀ J, D'V.overS J ≫ g.hom = D'.overS J := fun J =>
    congrArg (fun k => k.hom) (Over.w (ψ (OrderDual.toDual J)))
  have hK : ∀ K, ψ K = (BigAffineFppf.inclusion B S hS).map
        (smallerBaseStageIso B V S hV hS g D'V D' hD'V (OrderDual.ofDual K)).inv ≫
      (Over.homMk ((BigAffineFppf.inclusion B V hV).obj (D'V.diagram.obj K)).hom rfl :
        (Over.map g).obj ((BigAffineFppf.inclusion B V hV).obj (D'V.diagram.obj K)) ⟶
          Over.mk g) := by
    intro K
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change (ψ K).left.hom = 𝟙 _ ≫ (ψ K).left.hom
    rw [Category.id_comp]
  exact ⟨D'V, hD'V, colimit.hom_ext fun K => (hψc K).trans <| (congrArg (fun k =>
    (Sheaf.sheafifiedYoneda _).map k ≫
      ((Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app (Over.mk g)).inv)
      (hK K)).trans (formalSpectrumInclusion_smallerBaseFormalSpectrumIsoOfCompatible_inv_str
        B V S hV hS g D'V D' hD'V K).symm⟩

/-- A continuous map into a system over `S` that is compatible with the morphisms of formal
spectra to `V` is a continuous map over `V`. -/
theorem quotientMap_overS_eq_of_smallerBaseStr [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B V hV A}
    {D' : QuotientSystem B S hS C} {D'V : QuotientSystem B V hV C}
    (hD'V : ∀ J, D'V.overS J ≫ g.hom = D'.overS J)
    (e : ContinuousHom (smallerBaseQuotientSystem B V S hV hS g D) D')
    (hc : (smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D'V D' hD'V).inv ≫
        smallerBaseStr B V S hV hS g (formalSpectrum D'V) =
      formalSpectrumMap hA e ≫ (smallerBaseFormalSpectrumIso B V S hV hS g D).inv ≫
        smallerBaseStr B V S hV hS g (formalSpectrum D))
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
    (hJK : J.1 ≤ Ideal.comap e.toRingHom K.1) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 e.toRingHom hJK)) ≫ D.overS J =
      D'V.overS K := by
  let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let σ := (Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)).app (Over.mk g)
  let τ : (Over.map g).obj ((BigAffineFppf.inclusion B V hV).obj
      (D.diagram.obj (OrderDual.toDual J))) ⟶ Over.mk g :=
    Over.homMk ((BigAffineFppf.inclusion B V hV).obj (D.diagram.obj (OrderDual.toDual J))).hom rfl
  have h' : sY.map ((BigAffineFppf.inclusion B S hS).map
        (smallerBaseStageIso B V S hV hS g D'V D' hD'V K).inv ≫
      (Over.homMk ((BigAffineFppf.inclusion B V hV).obj
          (D'V.diagram.obj (OrderDual.toDual K))).hom rfl :
        (Over.map g).obj ((BigAffineFppf.inclusion B V hV).obj
          (D'V.diagram.obj (OrderDual.toDual K))) ⟶ Over.mk g)) ≫ σ.inv =
      sY.map ((BigAffineFppf.inclusion B S hS).map (e.stageMap J K hJK) ≫ τ) ≫ σ.inv :=
    (formalSpectrumInclusion_smallerBaseFormalSpectrumIsoOfCompatible_inv_str B V S hV hS g D'V D'
      hD'V (OrderDual.toDual K)).symm.trans <|
      (congrArg (formalSpectrumInclusion D' (OrderDual.toDual K) ≫ ·) hc).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (formalSpectrumMap_spec hA e J K hJK)).trans <|
      (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
        (formalSpectrumInclusion_smallerBaseFormalSpectrumIso_inv_str B V S hV hS g D
          (OrderDual.toDual J))).trans <|
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ σ.inv) (sY.map_comp _ _).symm)
  exact (congrArg (fun k => k.left.hom)
    (sY.map_injective ((cancel_mono σ.inv).mp h'))).symm.trans (Category.id_comp _)

end QuotientSystem

/-! ### Rig-surjectivity -/

/-- **Rig-surjectivity (Stacks 0AQQ) descends along the change of base.** If a morphism over `S`
isomorphic to the attached morphism of `f` is rig-surjective, then `f` is rig-surjective over
`V`: an adic point `Spf R ⟶ Y` over `V` gives one over `S`, and a lift over `S` along an
extension `R ⊂ R'` maps `Spf R'` to `V`, which makes its quotient system one over `V` and the lift
one over `V`. -/
theorem isRigSurjective_of_smallerBaseSheafFunctor {G G' : FppfSheaf B V hV} (f : G ⟶ G')
    {X Y : FppfSheaf B S hS} (f' : X ⟶ Y) (eX : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅ X)
    (eY : (smallerBaseSheafFunctor B V S hV hS g).obj G' ≅ Y)
    (w : (smallerBaseSheafFunctor B V S hV hS g).map f ≫ eY.hom = eX.hom ≫ f')
    (h : IsRigSurjective B S hS f') : IsRigSurjective B V hV f := by
  intro R _ _ _ _ _ _ hadic hcomp hR D p hp
  let Ψ := smallerBaseSheafFunctor B V S hV hS g
  let iD := smallerBaseFormalSpectrumIso B V S hV hS g D
  have hpS : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (iD.inv ≫ Ψ.map p ≫ eY.hom).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
      (isRepresentableEtale_of_isIso B S hS iD.inv).1
      (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
        ((isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff B V S hV hS g p.hom).mpr
          hp)
        (isRepresentableEtale_of_isIso B S hS eY.hom).1)
  obtain ⟨R', i1, i2, i3, i4, i5, i6, i7, i8, hadic', hcomp', D', e, x, he, hx⟩ :=
    h R hadic hcomp hR (smallerBaseQuotientSystem B V S hV hS g D) (iD.inv ≫ Ψ.map p ≫ eY.hom) hpS
  obtain ⟨D'V, hD'V, hxV'⟩ := exists_quotientSystem_of_hom_smallerBaseTarget B V S hV hS g D'
    (x ≫ eX.inv ≫ smallerBaseStr B V S hV hS g G)
  let iD' := smallerBaseFormalSpectrumIsoOfCompatible B V S hV hS g D'V D' hD'V
  have hw' : eX.inv ≫ Ψ.map f = f' ≫ eY.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have s1 : eX.inv ≫ smallerBaseStr B V S hV hS g G =
      f' ≫ eY.inv ≫ smallerBaseStr B V S hV hS g G' := by
    rw [← smallerBaseSheafFunctor_map_comp_str B V S hV hS g f, reassoc_of% hw']
  have s2 : x ≫ eX.inv ≫ smallerBaseStr B V S hV hS g G =
      formalSpectrumMap hR e ≫ iD.inv ≫ smallerBaseStr B V S hV hS g (formalSpectrum D) := by
    rw [s1, reassoc_of% hx]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (formalSpectrumMap hR e ≫ iD.inv ≫ ·)
      (smallerBaseSheafFunctor_map_comp_str B V S hV hS g p)
  let eV : ContinuousHom D D'V :=
    { toRingHom := e.toRingHom
      continuous := e.continuous
      overS :=
        quotientMap_overS_eq_of_smallerBaseStr B V S hV hS g hR hD'V e (hxV'.symm.trans s2) }
  have hxV : (iD'.hom ≫ x ≫ eX.inv) ≫ smallerBaseStr B V S hV hS g G =
      smallerBaseStr B V S hV hS g (formalSpectrum D'V) := by
    simp only [Category.assoc]
    rw [hxV', Iso.hom_inv_id_assoc]
  refine ⟨R', i1, i2, i3, i4, i5, i6, i7, i8, hadic', hcomp', D'V, eV,
    smallerBaseLift B V S hV hS g _ hxV, he, ?_⟩
  apply Ψ.map_injective
  have e1 := smallerBaseSheafFunctor_map_smallerBaseLift B V S hV hS g _ hxV
  have e2 : Ψ.map (formalSpectrumMap hR eV) = (iD'.hom ≫ formalSpectrumMap hR e) ≫ iD.inv :=
    (Iso.eq_comp_inv _).mpr
      (smallerBaseFormalSpectrumIsoOfCompatible_naturality B V S hV hS g hR hD'V eV e rfl)
  have m : (iD'.hom ≫ x ≫ eX.inv) ≫ Ψ.map f =
      ((iD'.hom ≫ formalSpectrumMap hR e) ≫ iD.inv) ≫ Ψ.map p := by
    simp only [Category.assoc]
    rw [hw', ← Category.assoc x, hx]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (Ψ.map_comp _ _).trans <| (congrArg (· ≫ Ψ.map f) e1).trans <| m.trans <|
    (congrArg (· ≫ Ψ.map p) e2.symm).trans (Ψ.map_comp _ _).symm

/-! ### Formal modifications -/

/-- The attached morphism of a relative diagonal is the relative diagonal of the attached
morphism, up to the isomorphisms induced on sources and fibre products. -/
theorem smallerBaseSheafFunctor_map_diagonal {G G' : FppfSheaf B V hV} (f : G ⟶ G')
    {X Y : FppfSheaf B S hS} (f' : X ⟶ Y) (eX : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅ X)
    (eY : (smallerBaseSheafFunctor B V S hV hS g).obj G' ≅ Y)
    (w : (smallerBaseSheafFunctor B V S hV hS g).map f ≫ eY.hom = eX.hom ≫ f') :
    (smallerBaseSheafFunctor B V S hV hS g).map (pullback.diagonal f) ≫
        (PreservesPullback.iso (smallerBaseSheafFunctor B V S hV hS g) f f ≪≫
          asIso (pullback.map _ _ f' f' eX.hom eX.hom eY.hom w w)).hom =
      eX.hom ≫ pullback.diagonal f' := by
  apply pullback.hom_ext <;>
    simp only [Iso.trans_hom, asIso_hom, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      PreservesPullback.iso_hom_fst_assoc, PreservesPullback.iso_hom_snd_assoc,
      pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, ← Functor.map_comp_assoc,
      CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Formal modifications (Stacks 0GDK) descend along the change of base.** If a morphism over
`S` isomorphic to the attached morphism of `f` is a formal modification, then `f` is a formal
modification over `V`. -/
theorem isFormalModification_of_smallerBaseSheafFunctor {G G' : FppfSheaf B V hV} (f : G ⟶ G')
    {X Y : FppfSheaf B S hS} (f' : X ⟶ Y) (eX : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅ X)
    (eY : (smallerBaseSheafFunctor B V S hV hS g).obj G' ≅ Y)
    (w : (smallerBaseSheafFunctor B V S hV hS g).map f ≫ eY.hom = eX.hom ≫ f')
    (h : IsFormalModification B S hS f') : IsFormalModification B V hV f where
  isLocallyNoetherian_source :=
    isLocallyNoetherian_of_smallerBaseSheafFunctor B V S hV hS g G eX h.isLocallyNoetherian_source
  isLocallyNoetherian_target :=
    isLocallyNoetherian_of_smallerBaseSheafFunctor B V S hV hS g G' eY h.isLocallyNoetherian_target
  isProper := isProper_of_smallerBaseSheafFunctor B V S hV hS g f f' eX eY w h.isProper
  isRigEtale := isRigEtale_of_smallerBaseSheafFunctor B V S hV hS g f f' eX eY w h.isRigEtale
  isRigSurjective :=
    isRigSurjective_of_smallerBaseSheafFunctor B V S hV hS g f f' eX eY w h.isRigSurjective
  isRigSurjective_diagonal :=
    isRigSurjective_of_smallerBaseSheafFunctor B V S hV hS g (pullback.diagonal f)
      (pullback.diagonal f') eX _
      (smallerBaseSheafFunctor_map_diagonal B V S hV hS g f f' eX eY w) h.isRigSurjective_diagonal

end AlgebraicGeometry.FormalSpace

end
