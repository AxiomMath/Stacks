module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification.SystemStages
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The colimit functor on finite type algebra systems

This file defines the functor sending a finite type algebra system to the colimit of the spectra
of its stages over the base formal space, proves that it is fully faithful, identifies its
essential image with the finite type morphisms from affine formal algebraic spaces, and shows
that its values are finite type morphisms. It is part of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open CartesianColimit

universe u v w

namespace FiniteTypeAlgebraSystem

attribute [local instance] bigFppfOver_subcanonical Sheaf.sheafifiedYoneda_full
  Sheaf.sheafifiedYoneda_faithful

/-- Composing a morphism of systems with the structure maps gives the structure maps, on spectra. -/
private theorem spec_map_comp_algebraMap
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    {P R : FiniteTypeAlgebraSystem A I J} (f : P ⟶ R) (i : I) :
    Spec.map (f.nat.app (Opposite.op i)) ≫ Spec.map (CommRingCat.ofHom (P.algebraMap i)) =
      Spec.map (CommRingCat.ofHom (R.algebraMap i)) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (f.base i))

theorem systemHom_base
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    {P R : FiniteTypeAlgebraSystem A I J}
    (Q : WeakIdealColimitPresentation B S hS A X)
    (f : P ⟶ R) (i : I) :
    Spec.map (f.nat.app (Opposite.op i)) ≫ systemStageBaseMap B S hS A P Q i =
      systemStageBaseMap B S hS A R Q i := by
  dsimp [systemStageBaseMap]
  rw [← Category.assoc, spec_map_comp_algebraMap]

noncomputable def systemDiagramMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    {P R : FiniteTypeAlgebraSystem A I J}
    (Q : WeakIdealColimitPresentation B S hS A X)
    (f : P ⟶ R) :
    systemDiagram B S hS A R Q ⟶ systemDiagram B S hS A P Q where
  app i := ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (Spec.map (f.nat.app (Opposite.op i)))) (by
      apply ObjectProperty.hom_ext
      exact systemHom_base B S hS A Q f i))
  naturality i j g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (R.B.map g.op) ≫ Spec.map (f.nat.app (Opposite.op j)) =
      Spec.map (f.nat.app (Opposite.op i)) ≫ Spec.map (P.B.map g.op)
    rw [← Spec.map_comp, ← Spec.map_comp, f.nat.naturality g.op]

theorem systemDiagramMap_over
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    {P R : FiniteTypeAlgebraSystem A I J}
    (Q : WeakIdealColimitPresentation B S hS A X)
    (f : P ⟶ R) :
    systemDiagramMap B S hS A Q f ≫ systemDiagramToBase B S hS A P Q =
      systemDiagramToBase B S hS A R Q := by
  apply NatTrans.ext
  funext i
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (f.nat.app (Opposite.op i)) ≫
    (Spec.map (CommRingCat.ofHom (P.algebraMap i)) ≫ _) =
      Spec.map (CommRingCat.ofHom (R.algebraMap i)) ≫ _
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (spec_map_comp_algebraMap f i))

/-- The spectra construction is contravariant and respects the morphism to
the base diagram. -/
noncomputable def systemOverDiagramFunctor
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] (J : IdealBasis A I)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    (FiniteTypeAlgebraSystem A I J)ᵒᵖ ⥤ Over (idealBasisFunctor J ⋙ Q.diagram) where
  obj P := Over.mk (systemDiagramToBase B S hS A P.unop Q)
  map f := Over.homMk (systemDiagramMap B S hS A Q f.unop)
    (systemDiagramMap_over B S hS A Q f.unop)
  map_id P := by
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext i
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (𝟙 _) = 𝟙 _
    exact Spec.map_id _
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext i
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (g.unop.nat.app (Opposite.op i) ≫ f.unop.nat.app (Opposite.op i)) = _
    exact Spec.map_comp _ _

theorem algebraSystemHom_ext
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    {P R : FiniteTypeAlgebraSystem A I J} {f g : P ⟶ R}
    (h : f.nat = g.nat) : f = g :=
  Hom.ext_nat (P := P) (Q := R) h

private theorem systemOverDiagramFunctor_faithful
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] (J : IdealBasis A I)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    (systemOverDiagramFunctor B S hS A J Q).Faithful where
  map_injective {P R} f g h := by
    apply Quiver.Hom.unop_inj
    apply algebraSystemHom_ext
    apply NatTrans.ext
    funext i
    have hs := congrArg
      (fun k => (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (k.left.app i.unop)) h
    change Spec.map (f.unop.nat.app i) = Spec.map (g.unop.nat.app i) at hs
    exact Quiver.Hom.op_inj (Scheme.Spec.map_injective hs)

private noncomputable def systemDiagramHomPreimage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    {P R : FiniteTypeAlgebraSystem A I J}
    (Q : WeakIdealColimitPresentation B S hS A X)
    (f : systemDiagram B S hS A P Q ⟶ systemDiagram B S hS A R Q)
    (hf : f ≫ systemDiagramToBase B S hS A R Q =
      systemDiagramToBase B S hS A P Q) : R ⟶ P where
  nat :=
    { app := fun i => (Scheme.Spec.preimage
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (f.app i.unop))).unop
      naturality := fun i j g => by
        apply Quiver.Hom.op_inj
        apply Scheme.Spec.map_injective
        have hmp (k : I) : Scheme.Spec.map (Scheme.Spec.preimage
            ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (f.app k))) =
            (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (f.app k) :=
          Scheme.Spec.map_preimage _
        simp only [op_comp, Scheme.Spec.map_comp, Quiver.Hom.op_unop]
        rw [hmp, hmp]
        have h := congrArg (fun k =>
          (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map k) (f.naturality g.unop)
        have hg : (homOfLE g.unop.le).op = g := Subsingleton.elim _ _
        simp only [Functor.map_comp] at h
        change Spec.map (P.B.map (homOfLE g.unop.le).op) ≫
            (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (f.app i.unop) =
          (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (f.app j.unop) ≫
            Spec.map (R.B.map (homOfLE g.unop.le).op) at h
        rw [hg] at h
        exact h.symm }
  base i := by
    change (CommRingCat.ofHom (R.algebraMap i) ≫
      (Scheme.Spec.preimage
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (f.app i))).unop).hom =
      (CommRingCat.ofHom (P.algebraMap i)).hom
    apply congrArg CommRingCat.Hom.hom
    apply Quiver.Hom.op_inj
    apply Scheme.Spec.map_injective
    have hmp : Scheme.Spec.map (Scheme.Spec.preimage
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (f.app i))) =
        (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (f.app i) :=
      Scheme.Spec.map_preimage _
    simp only [op_comp, Scheme.Spec.map_comp, Quiver.Hom.op_unop]
    rw [hmp]
    have hi := congrArg (fun k => (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
      (k.app i)) hf
    dsimp only [NatTrans.comp_app] at hi
    rw [Functor.map_comp] at hi
    change _ ≫ (Spec.map (CommRingCat.ofHom (R.algebraMap i)) ≫ _) =
      Spec.map (CommRingCat.ofHom (P.algebraMap i)) ≫ _ at hi
    exact (cancel_mono (Q.quotientIso (idealBasisIndex J i)).inv).mp
      ((Category.assoc _ _ _).trans hi)

private theorem systemDiagramHomPreimage_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    {P R : FiniteTypeAlgebraSystem A I J}
    (Q : WeakIdealColimitPresentation B S hS A X)
    (f : systemDiagram B S hS A P Q ⟶ systemDiagram B S hS A R Q)
    (hf : f ≫ systemDiagramToBase B S hS A R Q =
      systemDiagramToBase B S hS A P Q) :
    systemDiagramMap B S hS A Q (systemDiagramHomPreimage B S hS A Q f hf) = f := by
  apply NatTrans.ext
  funext i
  apply (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map_injective
  show Scheme.Spec.map (Scheme.Spec.preimage _) = _
  exact Scheme.Spec.map_preimage _

private theorem systemOverDiagramFunctor_full
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] (J : IdealBasis A I)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    (systemOverDiagramFunctor B S hS A J Q).Full where
  map_surjective f := ⟨(systemDiagramHomPreimage B S hS A Q f.left (Over.w f)).op,
    Over.OverMorphism.ext (systemDiagramHomPreimage_map B S hS A Q f.left (Over.w f))⟩

/-- Taking the colimit of the spectra is functorial over `X`. -/
noncomputable def systemColimitFunctor
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type (u + 1)} [Preorder I] [IsDirected I (· ≤ ·)] (J : IdealBasis A I)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    (FiniteTypeAlgebraSystem A I J)ᵒᵖ ⥤ Over X :=
  systemOverDiagramFunctor B S hS A J Q ⋙
    Over.post ((Functor.whiskeringRight I _ _).obj
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS))) ⋙
    Over.post colim ⋙ Over.map (basisColimitIso B S hS A J Q).hom

/-- The stagewise squares of the colimit of spectra are pullbacks. -/
private theorem systemColimit_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (J : IdealBasis A I)
    (Q : WeakIdealColimitPresentation B S hS A X)
    (R : (FiniteTypeAlgebraSystem A I J)ᵒᵖ) (i : I) :
    IsPullback (colimit.ι ((systemOverDiagramFunctor B S hS A J Q ⋙
      Over.post ((Functor.whiskeringRight I _ _).obj
        (AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)))).obj R).left i)
      (((systemOverDiagramFunctor B S hS A J Q ⋙
        Over.post ((Functor.whiskeringRight I _ _).obj
          (AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)))).obj R).hom.app
        i)
      (colim.map ((systemOverDiagramFunctor B S hS A J Q ⋙
      Over.post ((Functor.whiskeringRight I _ _).obj
        (AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)))).obj R).hom)
      (colimit.ι _ i) := by
  have : IsConnected (Under i) := IsFiltered.isConnected _
  exact equifibered_colimit_isPullback (systemSheafMap B S hS A R.unop Q)
    (systemSheafMap_equifibered B S hS A R.unop Q) i

theorem systemColimitFunctor_full
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (J : IdealBasis A I)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    (systemColimitFunctor B S hS A J Q).Full := by
  let K := AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)
  let T := systemOverDiagramFunctor B S hS A J Q ⋙
    Over.post ((Functor.whiskeringRight I _ _).obj K)
  have : (systemOverDiagramFunctor B S hS A J Q).Full :=
    systemOverDiagramFunctor_full B S hS A J Q
  have : (systemOverDiagramFunctor B S hS A J Q).Faithful :=
    systemOverDiagramFunctor_faithful B S hS A J Q
  have : ((Functor.whiskeringRight I _ _).obj K).Full := inferInstance
  have : ((Functor.whiskeringRight I _ _).obj K).Faithful := inferInstance
  have : T.Full := by dsimp only [T]; infer_instance
  have : (T ⋙ Over.post colim).Full := by
    exact overColimit_comp_full _ (systemColimit_isPullback B S hS A J Q)
  show ((T ⋙ Over.post colim) ⋙ Over.map (basisColimitIso B S hS A J Q).hom).Full
  infer_instance

theorem systemColimitFunctor_faithful
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (J : IdealBasis A I)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    (systemColimitFunctor B S hS A J Q).Faithful := by
  let K := AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)
  let T := systemOverDiagramFunctor B S hS A J Q ⋙
    Over.post ((Functor.whiskeringRight I _ _).obj K)
  have : (systemOverDiagramFunctor B S hS A J Q).Faithful :=
    systemOverDiagramFunctor_faithful B S hS A J Q
  have : ((Functor.whiskeringRight I _ _).obj K).Faithful := inferInstance
  have : T.Faithful := by dsimp only [T]; infer_instance
  have : (T ⋙ Over.post colim).Faithful := by
    exact overColimit_comp_faithful _ (systemColimit_isPullback B S hS A J Q)
  show ((T ⋙ Over.post colim) ⋙ Over.map (basisColimitIso B S hS A J Q).hom).Faithful
  infer_instance

private theorem systemColimitFunctor_obj_hom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type (u + 1)} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (Q : WeakIdealColimitPresentation B S hS A X)
    (P : FiniteTypeAlgebraSystem A I J) :
    ((systemColimitFunctor B S hS A J Q).obj (Opposite.op P)).hom =
      systemColimitMap B S hS A P Q := rfl

private theorem etale_relative_identity
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative
        (uliftYoneda.{u + 1}) (𝟙 ((uliftYoneda.{u + 1}).obj U)) := by
  let L := uliftYoneda.{u + 1} (C := AlgebraicGeometry.BigFppfOver B S hS)
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  have : E.IsStableUnderBaseChange := ⟨fun h hg =>
    Etale.etale_isStableUnderBaseChange.of_isPullback (h.map T) hg⟩
  rw [← L.map_id]
  apply MorphismProperty.relative_map (P := E)
  show Etale (T.map (𝟙 U))
  infer_instance

private theorem locallyFiniteType_of_formal_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (q : U ⟶ V)
    (p : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj U ⟶ X)
    (g : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj V ⟶ Y)
    (hp : IsPullback p
      ((Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).map q) f g) :
    LocallyOfFiniteType ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) := by
  obtain ⟨hrep, hprop⟩ := hf
  let K := sheafToPresheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))
  let L := uliftYoneda.{u + 1} (C := AlgebraicGeometry.BigFppfOver B S hS)
  let e := sheafifiedYonedaToUliftPresheafIso B S hS
  let p' := (e.app U).inv ≫ p.hom
  let g' := (e.app V).inv ≫ g.hom
  have hs : IsPullback p' (L.map q) f.hom g' := by
    apply (hp.map K).of_iso (e.app U) (Iso.refl _) (e.app V) (Iso.refl _)
    · rw [Iso.refl_hom, Category.comp_id]
      exact (Iso.hom_inv_id_assoc (e.app U) p.hom).symm
    · exact e.hom.naturality q
    · simp [K]
    · rw [Iso.refl_hom, Category.comp_id]
      exact (Iso.hom_inv_id_assoc (e.app V) g.hom).symm
  let r := hs.flip.isoPullback
  have hr : r.hom ≫ pullback.fst g' f.hom = L.map q := hs.flip.isoPullback_hom_fst
  let E := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative L
  have he : E r.hom := by
    have h := etale_relative_identity B S hS U
    simpa using MorphismProperty.RespectsIso.postcomp E r.hom (𝟙 (L.obj U)) h
  have hlft : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (pullback.fst g' f.hom) :=
    hprop V g'
  exact hlft U V r.hom (𝟙 _) q he
    (etale_relative_identity B S hS V) (by simpa using hr.symm)

private theorem exists_algebraSystem_of_affineDiagram
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] (J : IdealBasis A I)
    (Q : WeakIdealColimitPresentation B S hS A X)
    (D : I ⥤ AlgebraicGeometry.BigAffineFppf B S hS)
    (ψ : D ⟶ idealBasisFunctor J ⋙ Q.diagram)
    (hψ : (Functor.whiskerRight ψ (AlgebraicGeometry.BigAffineFppf.toScheme B S hS)).Equifibered)
    (hft : ∀ i, LocallyOfFiniteType
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (ψ.app i))) :
    ∃ P : FiniteTypeAlgebraSystem A I J,
      Nonempty ((systemOverDiagramFunctor B S hS A J Q).obj (Opposite.op P) ≅
        Over.mk ψ) := by
  let T := AlgebraicGeometry.BigAffineFppf.toScheme B S hS
  let Ds := D ⋙ T
  let (i : I) : IsAffine (Ds.obj i) := (D.obj i).property
  let a (i : I) := T.map (ψ.app i) ≫ (Q.quotientIso (idealBasisIndex J i)).hom
  have ha (i : I) : LocallyOfFiniteType (a i) := by
    have h1 : LocallyOfFiniteType (T.map (ψ.app i)) := hft i
    have h2 : LocallyOfFiniteType (Q.quotientIso (idealBasisIndex J i)).hom := inferInstance
    exact MorphismProperty.comp_mem _ _ _ h1 h2
  have hc {i j : I} (h : i ≤ j) :
      IsPullback (a i) (Ds.map (homOfLE h))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (J.antitone h)))) (a j) := by
    apply (hψ (homOfLE h)).flip.of_iso (Iso.refl _)
      (Q.quotientIso (idealBasisIndex J i)) (Iso.refl _)
      (Q.quotientIso (idealBasisIndex J j))
    · simp [a, T]
    · simp [Ds, T]
    · exact Q.quotientIso_natural ((idealBasisFunctor J).map (homOfLE h))
    · simp [a, T]
  let P := algebraSystemOfAffineSchemeDiagram J Ds (fun i => (D.obj i).property) a ha
    (fun {i j} h => hc h)
  have hb (i : I) : Spec.map (CommRingCat.ofHom (P.algebraMap i)) =
      (Ds.obj i).isoSpec.inv ≫ a i := Scheme.Spec.map_preimage _
  let K := systemDiagram B S hS A P Q
  have hs (i : I) : T.map ((systemDiagramToBase B S hS A P Q).app i) =
      (Ds.obj i).isoSpec.inv ≫ T.map (ψ.app i) := by
    show Spec.map (CommRingCat.ofHom (P.algebraMap i)) ≫
      (Q.quotientIso (idealBasisIndex J i)).inv = _
    rw [hb]
    exact (Iso.comp_inv_eq _).mpr (Category.assoc _ _ _).symm
  let e (i : I) : K.obj i ≅ D.obj i :=
    ObjectProperty.isoMk _ (Over.isoMk
      (ObjectProperty.isoMk _ (Ds.obj i).isoSpec.symm) (by
        apply ObjectProperty.hom_ext
        show (Ds.obj i).isoSpec.inv ≫ (D.obj i).obj.hom.hom = _
        have hw := congrArg (fun k => k.hom) (Over.w (ψ.app i).hom)
        change T.map (ψ.app i) ≫ (Q.diagram.obj (idealBasisIndex J i)).obj.hom.hom =
          (D.obj i).obj.hom.hom at hw
        rw [← hw]
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ (Q.diagram.obj (idealBasisIndex J i)).obj.hom.hom)
            (hs i).symm)))
  let eD : K ≅ D := NatIso.ofComponents e (by
    intro i j g
    apply T.map_injective
    show Spec.map (Ds.map g).appTop ≫ (Ds.obj j).isoSpec.inv =
      (Ds.obj i).isoSpec.inv ≫ Ds.map g
    exact Scheme.isoSpec_inv_naturality (Ds.map g))
  refine ⟨P, ⟨Over.isoMk eD ?_⟩⟩
  apply NatTrans.ext
  funext i
  apply T.map_injective
  show (Ds.obj i).isoSpec.inv ≫ T.map (ψ.app i) =
    T.map ((systemDiagramToBase B S hS A P Q).app i)
  exact (hs i).symm

theorem systemColimitFunctor_essImage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))} (f : Y ⟶ X)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS X)
    (hY : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (J : IdealBasis A I)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    (systemColimitFunctor B S hS A J Q).essImage (Over.mk f) := by
  classical
  let G := Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)
  let V := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let K := V ⋙ G
  let H := idealBasisFunctor J ⋙ Q.diagram
  let c : Cocone (H ⋙ K) := (colimit.cocone (H ⋙ K)).extend
    (basisColimitIso B S hS A J Q).hom
  have hc : IsColimit c := (colimit.isColimit (H ⋙ K)).extendIso _
  let F := pullback c.ι ((Functor.const I).map f)
  let α : F ⟶ H ⋙ K := pullback.fst _ _
  let β : F ⟶ (Functor.const I).obj Y := pullback.snd _ _
  have hα : α.Equifibered := pullbackCocone_equifibered c f
  have hp (i : I) : IsPullback (α.app i) (β.app i) (c.ι.app i) f :=
    (IsPullback.of_hasPullback c.ι ((Functor.const I).map f)).map
      ((evaluation I _).obj i)
  obtain ⟨hfrep, -⟩ := id hf
  have hF (i : I) : K.essImage (F.obj i) := by
    obtain ⟨W, pW, qW, hpbW, hWaff, -⟩ :=
      exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces B S hS f hY hX hfrep
        (V.obj (H.obj i)) (H.obj i).property (c.ι.app i)
    exact ⟨⟨W, hWaff⟩, ⟨hpbW.flip.isoIsPullback _ _ (hp i)⟩⟩
  let D := Functor.essImage.liftFunctor F K hF
  let e := Functor.essImage.liftFunctorCompIso F K hF
  let W := (Functor.whiskeringRight I _ _).obj K
  let ψ : D ⟶ H := W.preimage (e.hom ≫ α)
  have hψ : W.map ψ = e.hom ≫ α := W.map_preimage _
  have hψcart : (Functor.whiskerRight ψ K).Equifibered := by
    show (W.map ψ).Equifibered
    rw [hψ]
    exact (NatTrans.Equifibered.of_isIso e.hom).comp hα
  have hψscheme : (Functor.whiskerRight ψ (V ⋙ T)).Equifibered := by
    intro i j g
    exact (IsPullback.of_map_of_faithful G (hψcart g)).map T
  let p (i : I) : K.obj (D.obj i) ⟶ Y := (e.app i).hom ≫ β.app i
  have hpi (i : I) : IsPullback (p i) (K.map (ψ.app i)) f (c.ι.app i) := by
    have hi : K.map (ψ.app i) = (e.app i).hom ≫ α.app i := NatTrans.congr_app hψ i
    rw [hi]
    exact (hp i).flip.of_iso (e.app i).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [p]) (by simp) (by simp) (by simp)
  have hft (i : I) : LocallyOfFiniteType ((V ⋙ T).map (ψ.app i)) :=
    locallyFiniteType_of_formal_pullback B S hS f hf (V.map (ψ.app i))
      (p i) (c.ι.app i) (hpi i)
  obtain ⟨P, ⟨eP⟩⟩ := exists_algebraSystem_of_affineDiagram B S hS A J Q D ψ
    hψscheme hft
  have : IsConnected I := IsFiltered.isConnected I
  let ec : colimit F ≅ Y := (colimit.isColimit F).coconePointUniqueUpToIso
    (hc.pullbackOfHasExactColimitsOfShape f)
  have hec (i : I) : colimit.ι F i ≫ ec.hom = β.app i :=
    colimit.comp_coconePointUniqueUpToIso_hom
      (hc.pullbackOfHasExactColimitsOfShape f) i
  let ed : colimit (D ⋙ K) ≅ Y := (colim.mapIso e) ≪≫ ec
  have hd : ed.hom ≫ f = colim.map (Functor.whiskerRight ψ K) ≫
      (basisColimitIso B S hS A J Q).hom := by
    apply colimit.hom_ext
    intro i
    simp only [ed, Iso.trans_hom, Functor.mapIso_hom, colimit.ι_map_assoc,
      Category.assoc]
    rw [reassoc_of% (hec i), ← (hp i).w]
    have hi := NatTrans.congr_app hψ i
    change K.map (ψ.app i) = (e.app i).hom ≫ α.app i at hi
    show e.hom.app i ≫ α.app i ≫ c.ι.app i =
      K.map (ψ.app i) ≫ colimit.ι (H ⋙ K) i ≫ (basisColimitIso B S hS A J Q).hom
    rw [hi]
    simp [c, Category.assoc]
  let L : Over H ⥤ Over X := Over.post W ⋙ Over.post colim ⋙
    Over.map (basisColimitIso B S hS A J Q).hom
  exact ⟨Opposite.op P, ⟨L.mapIso eP ≪≫ Over.isoMk ed hd⟩⟩

theorem systemColimitMap_affineBaseChange
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {J : IdealBasis A I} (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U))
    (ξ : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj U ⟶ X) :
    ∃ (V : AlgebraicGeometry.BigFppfOver B S hS)
      (p : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj V ⟶
        colimit (systemDiagram B S hS A P Q ⋙
          AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)))
      (q : V ⟶ U),
      IsPullback p
        ((Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).map q)
        (systemColimitMap B S hS A P Q) ξ ∧
      IsAffineHom ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) ∧
      LocallyOfFiniteType ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) := by
  let G := Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)
  let D := idealBasisFunctor J ⋙ Q.diagram
  have hD : ∀ ⦃i j : I⦄ (g : i ⟶ j), Stacks.Thickenings.IsThickening
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (D.map g)) :=
    fun _ _ g => quotientPresentation_isThickening B S hS A Q ((idealBasisFunctor J).map g)
  have hqc := AlgebraicGeometry.Space.isQuasiCompact_yoneda_of_compact B S hS U
    (by let := hU; infer_instance)
  obtain ⟨i, g, hg⟩ := AlgebraicGeometry.exists_factor_through_thickening B S hS I D hD X
    (basisColimitIso B S hS A J Q).symm (yoneda.obj U)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hqc ξ
  obtain ⟨V, p, q, hp, hqa, hqt⟩ :=
    systemColimitMap_baseChange_stage B S hS A P Q i U (G.preimage g)
  refine ⟨V, p, q, ?_, hqa, hqt⟩
  have hg' : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).map
      (G.preimage g) = g := G.map_preimage g
  have hξ : ξ = (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).map
      (G.preimage g) ≫ colimit.ι (idealBasisFunctor J ⋙ Q.diagram ⋙
        AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) i ≫
          (basisColimitIso B S hS A J Q).hom :=
    hg.symm.trans (congrArg (fun k => k ≫ _) hg'.symm)
  rw [hξ]
  exact hp

lemma systemColimit_small
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS X)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {J : IdealBasis A I} (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    FunctorToTypes.Small.{u}
      (colimit (systemDiagram B S hS A P Q ⋙ AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS))).obj := by
  let G := Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)
  let T := AlgebraicGeometry.BigFppfOver.topology B S hS
  let := small_of_setTheoreticCondition B S hS X hX.1
  apply small_sections_of_affine B S hS
  intro U hU
  have : Small.{u} (G.obj U ⟶ X) :=
    small_of_injective (Sheaf.sectionEquiv T (X := U) (F := X)).injective
  have : Small.{u} (G.obj U ⟶ _) := small_hom_of_represented_fibers.{u} G
    (systemColimitMap B S hS A P Q) U (fun ξ => by
      obtain ⟨V, p, q, hp, _⟩ := systemColimitMap_affineBaseChange B S hS A P Q U hU ξ
      exact ⟨V, p, q, hp⟩)
  exact small_of_surjective (Sheaf.sectionEquiv T (X := U)).surjective

theorem affineFiniteType_relative_of_affineBaseChanges
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : Y ⟶ X) [FunctorToTypes.Small.{u} Y.obj]
    (hf : ∀ U : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) →
      ∀ ξ : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj U ⟶ X,
      ∃ (V : AlgebraicGeometry.BigFppfOver B S hS)
        (p : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj V ⟶ Y)
        (q : V ⟶ U), IsPullback p
          ((Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).map q) f ξ ∧
        IsAffineHom ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) ∧
        LocallyOfFiniteType ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q)) :
    (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) f := by
  have hisoA : MorphismProperty.RespectsIso (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hisoT : MorphismProperty.RespectsIso
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hisoP : MorphismProperty.RespectsIso
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u}) :=
    MorphismProperty.RespectsIso.inf _ _
  have hzlA : IsZariskiLocalAtTarget (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  have hzlT : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  refine CartesianColimit.relative_of_affineBaseChanges B S hS _
    (MorphismProperty.IsLocalAtTarget.inf _ _) f (κ := 0)
    (lt_of_lt_of_le Cardinal.aleph0_pos B.aleph0_lt_cutoff.le) fun U hU ξ => ?_
  obtain ⟨V, p, q, hq, hqa, hqt⟩ := hf U hU ξ
  refine ⟨V, p, q, hq, ⟨hqa, hqt⟩, ?_⟩
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have : IsAffine (T.obj U) := hU
  have : IsAffineHom (T.map q) := hqa
  have : IsAffine (T.obj V) := isAffine_of_isAffineHom (T.map q)
  have : LocallyOfFiniteType (T.map q) := hqt
  exact (Scheme.size_le_of_locallyOfFiniteType (T.map q)).trans (le_max_right _ _)

private theorem relative_ulift_of_relative_sheaf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicGeometry.BigFppfOver B S hS)) [P.RespectsIso]
    {X Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : Y ⟶ X)
    (hf : P.relative (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) f) :
    P.relative (uliftYoneda.{u + 1}) f.hom := by
  let K := sheafToPresheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))
  let G := Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)
  let e := sheafifiedYonedaToUliftPresheafIso B S hS
  apply MorphismProperty.relative.of_exists
  intro U ξ
  let ξ' : G.obj U ⟶ X := K.preimage ((e.app U).hom ≫ ξ)
  have hξ : K.map ξ' = (e.app U).hom ≫ ξ := K.map_preimage _
  let V := hf.rep.pullback ξ'
  let p := hf.rep.fst ξ'
  let q := hf.rep.snd ξ'
  refine ⟨V, (e.app V).inv ≫ K.map p, q, ?_, hf.property_snd ξ'⟩
  apply ((hf.rep.isPullback ξ').map K).of_iso (e.app V) (Iso.refl _)
    (e.app U) (Iso.refl _)
  · rw [Iso.refl_hom, Category.comp_id]
    exact (Iso.hom_inv_id_assoc (e.app V) (K.map p)).symm
  · exact e.hom.naturality q
  · simp [K]
  · exact (Category.comp_id _).trans hξ

private theorem locallyFiniteTypeULift_of_relative_to_scheme
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {T : AlgebraicGeometry.BigFppfOver B S hS}
    (f : F ⟶ (uliftYoneda.{u + 1}).obj T)
    (hf : (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) f) :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS f := by
  let L := uliftYoneda.{u + 1} (C := AlgebraicGeometry.BigFppfOver B S hS)
  let K := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@LocallyOfFiniteType.{u}) K
  intro U V a b h ha hb hh
  have hmono : (MorphismProperty.inverseImage (@Etale.{u}) K) ≤ P := by
    intro U V q hq
    let : Etale (K.map q) := hq
    exact inferInstanceAs (LocallyOfFiniteType (K.map q))
  have hPcomp : (MorphismProperty.inverseImage
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have hrel : MorphismProperty.IsStableUnderComposition (P.relative L) := inferInstance
  have haf := (P.relative L).comp_mem a f
    (MorphismProperty.relative_monotone (F := L) hmono _ ha) hf
  obtain ⟨b', rfl⟩ := L.map_surjective b
  rw [← hh, ← L.map_comp] at haf
  have hcomp : LocallyOfFiniteType (K.map h ≫ K.map b') := by
    have hP : P (h ≫ b') := MorphismProperty.of_relative_map haf
    change LocallyOfFiniteType (K.map (h ≫ b')) at hP
    simpa only [K.map_comp] using hP
  exact locallyOfFiniteType_of_comp (K.map h) (K.map b')

private theorem formalLocallyFiniteType_of_relative
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))} (f : Y ⟶ X)
    (hf : (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) f) :
    IsLocallyOfFiniteType B S hS f := by
  let L := uliftYoneda.{u + 1} (C := AlgebraicGeometry.BigFppfOver B S hS)
  let P := MorphismProperty.inverseImage (@LocallyOfFiniteType.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have hlftIso : MorphismProperty.RespectsIso
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hPIso : MorphismProperty.RespectsIso P :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hf' := relative_ulift_of_relative_sheaf B S hS P f hf
  refine ⟨?_, ?_⟩
  · intro U ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS (hf'.rep.isPullback ξ).flip.isoPullback
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS _)
  · intro U ξ
    exact locallyFiniteTypeULift_of_relative_to_scheme B S hS (pullback.fst ξ f.hom)
      ((MorphismProperty.relative_isStableUnderBaseChange (F := L) P).of_isPullback
        (IsPullback.of_hasPullback ξ f.hom).flip hf')

/-- A morphism of finite type is locally of finite type: the condition on each base change
along a scheme-valued point of the target is a conjunction whose first half it is. -/
theorem isLocallyOfFiniteType_of_isFiniteType
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))} {f : X ⟶ Y}
    (hf : IsFiniteType B S hS f) : IsLocallyOfFiniteType B S hS f := by
  obtain ⟨hrep, hprop⟩ := hf
  exact ⟨hrep, fun U ξ ↦ (hprop U ξ).1⟩

/-- Affineness of a morphism of schemes is invariant under isomorphism, being stable under base
change, and hence so is its inverse image along the structure functor of the site. -/
private theorem respectsIso_inverseImage_isAffineHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) :=
  have : MorphismProperty.RespectsIso (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  MorphismProperty.RespectsIso.inverseImage
    (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)

theorem formalFiniteType_of_relative
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))} (f : Y ⟶ X)
    (hf : (MorphismProperty.inverseImage
      ((@IsAffineHom.{u} : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) f) :
    IsFiniteType B S hS f := by
  let G := Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let L := uliftYoneda.{u + 1} (C := AlgebraicGeometry.BigFppfOver B S hS)
  have ha : (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) T).relative G f :=
    MorphismProperty.relative_monotone (F := G) (fun _ _ _ h ↦ h.1) _ hf
  have ha' := @relative_ulift_of_relative_sheaf B S hS
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) T)
    (respectsIso_inverseImage_isAffineHom B S hS) _ _ f ha
  obtain ⟨hrep, hlft⟩ := formalLocallyFiniteType_of_relative B S hS f
    (MorphismProperty.relative_monotone (F := G) (fun _ _ _ h ↦ h.2) _ hf)
  refine ⟨hrep, fun U ξ ↦ ⟨hlft U ξ, ?_⟩⟩
  have haff : IsAffineHom (T.map (ha'.rep.snd ξ)) := ha'.property_snd ξ
  have hqc : Space.IsQuasiCompactULift.{u + 1} B S hS (L.map (ha'.rep.snd ξ)) :=
    Space.isQuasiCompactULift_uliftYoneda_map B S hS (ha'.rep.snd ξ) inferInstance
  have hfst : (ha'.rep.isPullback ξ).flip.isoPullback.hom ≫ pullback.fst ξ f.hom =
      L.map (ha'.rep.snd ξ) := (ha'.rep.isPullback ξ).flip.isoPullback_hom_fst
  have h2 : Space.IsQuasiCompactULift.{u + 1} B S hS
      ((ha'.rep.isPullback ξ).flip.isoPullback.inv ≫ L.map (ha'.rep.snd ξ)) :=
    Space.isQuasiCompactULift_precomp B S hS
      (ha'.rep.isPullback ξ).flip.isoPullback.symm (L.map (ha'.rep.snd ξ)) hqc
  rwa [(Iso.inv_comp_eq _).mpr hfst.symm] at h2

end FiniteTypeAlgebraSystem

end AlgebraicGeometry.FormalSpace

end
