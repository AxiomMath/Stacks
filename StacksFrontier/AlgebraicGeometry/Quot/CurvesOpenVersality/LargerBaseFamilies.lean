module

public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesOverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.Openness
import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
import StacksFrontier.AlgebraicGeometry.Spaces.StronglyCartesian
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.Relocalization
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.ProperFlatFamilies
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.OverIntegers
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.Relocalization

/-!
# Families of algebraic spaces over a larger base

Local finite presentation, local finite type, flatness, quasi-compactness, finite presentation,
properness and relative dimension bounds of morphisms of algebraic spaces over a larger base,
their invariance under isomorphisms of arrows, and the family of algebraic spaces over a larger
base attached to a family over a smaller one, with its finite presentation, flatness and
properness.
-/

@[expose] public section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Deformation.Artin

universe u

namespace CurvesVersality

attribute [local instance] schemeCutoff_isClosedUnderIsomorphisms
attribute [local instance] schemeCutoff_isClosedUnderPullbacks
attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes
attribute [local instance] MorphismProperty.IsMultiplicative.toContainsIdentities
attribute [local instance] relocalizePreservesPullbacks

private theorem locallyFinitePresentation_of_largerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S' hS'
      ((smallerBaseEquivalenceData
        B S S' hS hS' g).1.functor.map f).hom.left) :
    AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS f.hom :=
  holdsOnEveryEtaleChart_of_largerBase B S S' hS hS' g
    (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) f hf

private theorem locallyFiniteType_of_largerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.IsLocallyOfFiniteType B S' hS'
      ((smallerBaseEquivalenceData
        B S S' hS hS' g).1.functor.map f).hom.left) :
    Space.IsLocallyOfFiniteType B S hS f.hom :=
  holdsOnEveryEtaleChart_of_largerBase B S S' hS hS' g
    (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) f hf

private theorem flat_of_largerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.IsFlat B S' hS'
      ((smallerBaseEquivalenceData
        B S S' hS hS' g).1.functor.map f).hom.left) :
    Space.IsFlat B S hS f.hom :=
  holdsOnEveryEtaleChart_of_largerBase B S S' hS hS' g
    (@Flat : MorphismProperty Scheme.{u}) f hf

private theorem quasiCompact_precomp_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) {f : G ⟶ H}
    (hf : AlgebraicGeometry.Space.IsQuasiCompact B S hS f) :
    AlgebraicGeometry.Space.IsQuasiCompact B S hS (e.hom ≫ f) := by
  intro Z hZ hZqc g
  let h₁ := IsPullback.of_hasPullback g f
  let h₂ := IsPullback.of_hasPullback g (e.hom ≫ f)
  have h₁' : IsPullback (pullback.fst g f) (pullback.snd g f ≫ e.inv)
      g (e.hom ≫ f) := by
    refine h₁.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_
    all_goals simp
  let ePB := h₁'.isoIsPullback _ _ h₂
  exact Space.isQuasiCompactSpace_of_iso B S hS ePB (hf Z hZ hZqc g)

private theorem quasiCompact_postcomp_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} (e : G ≅ H)
    (hf : AlgebraicGeometry.Space.IsQuasiCompact B S hS f) :
    AlgebraicGeometry.Space.IsQuasiCompact B S hS (f ≫ e.hom) := by
  intro Z hZ hZqc k
  let k' := k ≫ e.inv
  have hbase := hf Z hZ hZqc k'
  let h₁ := IsPullback.of_hasPullback k' f
  let h₂ := IsPullback.of_hasPullback k (f ≫ e.hom)
  have h₁' : IsPullback (pullback.fst k' f) (pullback.snd k' f)
      k (f ≫ e.hom) := by
    refine h₁.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
    all_goals simp [k']
  let ePB := h₁'.isoIsPullback _ _ h₂
  exact Space.isQuasiCompactSpace_of_iso B S hS ePB hbase

private theorem quasiCompact_of_largerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : AlgebraicGeometry.Space.IsQuasiCompact B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom)) :
    AlgebraicGeometry.Space.IsQuasiCompact B S hS f.hom := by
  intro Z hZ hZqc a
  let R := OverShriek.relocalizePresheafFunctor g
  have hZ' := AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g Z hZ
  have hZqc' : AlgebraicGeometry.Space.IsQuasiCompactSpace B S' hS' (R.obj Z) :=
    (isQuasiCompact_relocalize_iff B S S' hS hS' g ⟨Z, hZ⟩).mpr hZqc
  have h := hf (R.obj Z) hZ' hZqc' (R.map a)
  let e := (IsPullback.of_hasPullback a f.hom).map R |>.isoPullback
  have h' : AlgebraicGeometry.Space.IsQuasiCompactSpace B S' hS' (R.obj (pullback a f.hom)) :=
    Space.isQuasiCompactSpace_of_iso B S' hS' e.symm h
  let hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS a f.hom hZ F.property G.property
  exact (isQuasiCompact_relocalize_iff B S S' hS hS' g
    ⟨pullback a f.hom, hP⟩).mp h'

/-- The comparison of `f` under the smaller base equivalence with its relocalization. -/
private noncomputable def smallerBase_relocalize_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    Arrow.mk ((smallerBaseEquivalenceData B S S' hS hS' g).1.functor.map f).hom.left ≅
      Arrow.mk ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
  let d := smallerBaseEquivalenceData B S S' hS hS' g
  Arrow.isoMk (d.2.app X) (d.2.app Y) (d.2.hom.naturality f).symm

private theorem property_relocalize_of_equiv
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (P : MorphismProperty
      ((AlgebraicGeometry.BigFppfOver B S' hS')ᵒᵖ ⥤ Type u))
    [P.RespectsIso]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : P ((smallerBaseEquivalenceData
      B S S' hS hS' g).1.functor.map f).hom.left) :
    P ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
  (P.arrow_mk_iso_iff (smallerBase_relocalize_arrowIso B S S' hS hS' g f)).mp hf

private theorem property_equiv_of_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (P : MorphismProperty
      ((AlgebraicGeometry.BigFppfOver B S' hS')ᵒᵖ ⥤ Type u))
    [P.RespectsIso]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : P ((OverShriek.relocalizePresheafFunctor g).map f.hom)) :
    P ((smallerBaseEquivalenceData
      B S S' hS hS' g).1.functor.map f).hom.left :=
  (P.arrow_mk_iso_iff (smallerBase_relocalize_arrowIso B S S' hS hS' g f)).mpr hf

/-- Etaleness of a map of presheaves is preserved by postcomposing with an isomorphism. -/
private theorem etale_presheaf_comp_isIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : X ⟶ Y) [IsIso i]
    (a : P ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (a ≫ i) :=
  MorphismProperty.RespectsIso.postcomp _ i a ha

/-- A commuting square over `f` gives a commuting square over `f'` for an isomorphism of arrows. -/
private theorem comm_comp_arrowIso
    {C : Type*} [Category C] {F G F' G' P Q : C} {f : F ⟶ G} {f' : F' ⟶ G'}
    (e : Arrow.mk f ≅ Arrow.mk f') (u : P ⟶ Q) (a : P ⟶ F) (b : Q ⟶ G)
    (hw : u ≫ b = a ≫ f) : u ≫ (b ≫ e.hom.right) = (a ≫ e.hom.left) ≫ f' := by
  have he : e.hom.left ≫ f' = f ≫ e.hom.right := e.hom.w
  rw [← Category.assoc, hw, Category.assoc, Category.assoc, ← he]

private theorem holdsOnEveryEtaleChart_of_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    {F G F' G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {f' : F' ⟶ G'}
    (e : Arrow.mk f ≅ Arrow.mk f')
    (hf' : Space.HoldsOnEveryEtaleChart B S hS P f') :
    Space.HoldsOnEveryEtaleChart B S hS P f := by
  intro U V a b h ha hb hw
  exact hf' U V _ _ h (etale_presheaf_comp_isIso B S hS e.hom.left a ha)
    (etale_presheaf_comp_isIso B S hS e.hom.right b hb) (comm_comp_arrowIso e _ a b hw)

private theorem quasiCompact_of_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {f' : F' ⟶ G'}
    (e : Arrow.mk f ≅ Arrow.mk f')
    (hf' : AlgebraicGeometry.Space.IsQuasiCompact B S hS f') :
    AlgebraicGeometry.Space.IsQuasiCompact B S hS f := by
  let l := Arrow.leftFunc.mapIso e
  let r := Arrow.rightFunc.mapIso e
  have h := quasiCompact_postcomp_iso B S hS r.symm
    (quasiCompact_precomp_iso B S hS l hf')
  have he : e.hom.left ≫ f' ≫ e.inv.right = f := by
    have hr : e.hom.right ≫ e.inv.right = 𝟙 G :=
      congrArg Arrow.Hom.right e.hom_inv_id
    calc
      e.hom.left ≫ f' ≫ e.inv.right = (f ≫ e.hom.right) ≫ e.inv.right :=
        congrArg (fun k => k ≫ e.inv.right) e.hom.w
      _ = f ≫ (e.hom.right ≫ e.inv.right) := Category.assoc _ _ _
      _ = f ≫ 𝟙 G := by rw [hr]
      _ = f := Category.comp_id _
  change AlgebraicGeometry.Space.IsQuasiCompact B S hS
    (e.hom.left ≫ f' ≫ e.inv.right) at h
  rwa [he] at h

private noncomputable def diagonal_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {f' : F' ⟶ G'}
    (e : Arrow.mk f ≅ Arrow.mk f') :
    Arrow.mk (pullback.diagonal f) ≅ Arrow.mk (pullback.diagonal f') := by
  let l := Arrow.leftFunc.mapIso e
  let r := Arrow.rightFunc.mapIso e
  letI : IsIso e.hom.left := by change IsIso l.hom; infer_instance
  letI : IsIso e.hom.right := by change IsIso r.hom; infer_instance
  let p : pullback f f ≅ pullback f' f' :=
    asIso (pullback.map f f f' f' e.hom.left e.hom.left e.hom.right
      e.hom.w.symm e.hom.w.symm)
  have hp : pullback.diagonal f ≫ p.hom =
      e.hom.left ≫ pullback.diagonal f' := by
    apply pullback.hom_ext
    · change (pullback.diagonal f ≫
        pullback.map f f f' f' e.hom.left e.hom.left e.hom.right
          e.hom.w.symm e.hom.w.symm) ≫ pullback.fst f' f' =
          (e.hom.left ≫ pullback.diagonal f') ≫ pullback.fst f' f'
      dsimp only [pullback.map]
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        pullback.diagonal_fst, Category.id_comp,
        Category.assoc, pullback.diagonal_fst]
      simp only [Category.comp_id]
    · change (pullback.diagonal f ≫
        pullback.map f f f' f' e.hom.left e.hom.left e.hom.right
          e.hom.w.symm e.hom.w.symm) ≫ pullback.snd f' f' =
          (e.hom.left ≫ pullback.diagonal f') ≫ pullback.snd f' f'
      dsimp only [pullback.map]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
        pullback.diagonal_snd, Category.id_comp,
        Category.assoc, pullback.diagonal_snd]
      simp only [Category.comp_id]
  exact Arrow.isoMk l p hp.symm

private theorem quasiSeparated_of_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {f' : F' ⟶ G'}
    (e : Arrow.mk f ≅ Arrow.mk f')
    (hf' : AlgebraicGeometry.Space.IsQuasiSeparated B S hS f') :
    AlgebraicGeometry.Space.IsQuasiSeparated B S hS f :=
  quasiCompact_of_arrowIso B S hS (diagonal_arrowIso B S hS e) hf'

private theorem separated_of_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {f' : F' ⟶ G'}
    (e : Arrow.mk f ≅ Arrow.mk f')
    (hf' : AlgebraicGeometry.Space.IsSeparated B S hS f') :
    AlgebraicGeometry.Space.IsSeparated B S hS f := by
  let Q := (MorphismProperty.inverseImage
    (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
  let : Q.RespectsIso := inferInstance
  exact (Q.arrow_mk_iso_iff (diagonal_arrowIso B S hS e)).mpr hf'

private theorem finitePresentation_of_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {f' : F' ⟶ G'}
    (e : Arrow.mk f ≅ Arrow.mk f')
    (hf' : AlgebraicGeometry.Space.IsFinitePresentation B S hS f') :
    AlgebraicGeometry.Space.IsFinitePresentation B S hS f :=
  ⟨holdsOnEveryEtaleChart_of_arrowIso B S hS
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) e hf'.1,
    quasiCompact_of_arrowIso B S hS e hf'.2.1,
    quasiSeparated_of_arrowIso B S hS e hf'.2.2⟩

private theorem universallyClosed_of_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {f' : F' ⟶ G'}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hF' : AlgebraicGeometry.IsAlgebraicSpace B S hS F')
    (hG' : AlgebraicGeometry.IsAlgebraicSpace B S hS G')
    (e : Arrow.mk f ≅ Arrow.mk f')
    (hf' : spaceUniversallyClosed B S hS hF' hG' f') :
    spaceUniversallyClosed B S hS hF hG f := by
  intro Z hZ a
  let a' := a ≫ e.hom.right
  let : IsIso e.hom.left := by
    show IsIso (Arrow.leftFunc.mapIso e).hom
    infer_instance
  let : IsIso e.hom.right := by
    show IsIso (Arrow.rightFunc.mapIso e).hom
    infer_instance
  let p : pullback a f ≅ pullback a' f' :=
    asIso (pullback.map a f a' f' (𝟙 Z) e.hom.left e.hom.right
      (by simp [a']) e.hom.w.symm)
  have hp : p.hom ≫ pullback.fst a' f' = pullback.fst a f := by
    show (pullback.map a f a' f' (𝟙 Z) e.hom.left e.hom.right
      (by simp [a']) e.hom.w.symm) ≫ pullback.fst a' f' = pullback.fst a f
    dsimp only [pullback.map]
    rw [pullback.lift_fst, Category.comp_id]
  have hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS a f hZ hF hG
  have hP' := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS a' f' hZ hF' hG'
  have h := isClosed_precomp_iso B S hS hP hP' hZ p
    (pullback.fst a' f') (hf' Z hZ a')
  rwa [hp] at h

private theorem proper_of_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {f' : F' ⟶ G'}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hF' : AlgebraicGeometry.IsAlgebraicSpace B S hS F')
    (hG' : AlgebraicGeometry.IsAlgebraicSpace B S hS G')
    (e : Arrow.mk f ≅ Arrow.mk f')
    (hf' : spaceIsProper B S hS hF' hG' f') :
    spaceIsProper B S hS hF hG f :=
  ⟨separated_of_arrowIso B S hS e hf'.1,
    ⟨holdsOnEveryEtaleChart_of_arrowIso B S hS
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) e hf'.2.1.1,
      quasiCompact_of_arrowIso B S hS e hf'.2.1.2⟩,
    universallyClosed_of_arrowIso B S hS hF hG hF' hG' e hf'.2.2⟩

private theorem relativeDimensionLE_of_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {f' : F' ⟶ G'}
    (e : Arrow.mk f ≅ Arrow.mk f')
    (hf' : Space.HasRelativeDimensionLE 1 B S hS f') :
    Space.HasRelativeDimensionLE 1 B S hS f := by
  intro x
  obtain ⟨d, hd, hdim⟩ := hf' (Space.pointsMap B S hS F e.hom.left x)
  refine ⟨d, hd, ?_⟩
  intro c
  let c' : Space.EtaleChartAtPoint B S hS f'
      (Space.pointsMap B S hS F e.hom.left x) := {
    U := c.U
    V := c.V
    a := c.a ≫ e.hom.left
    b := c.b ≫ e.hom.right
    h := c.h
    a_etale := etale_presheaf_comp_isIso B S hS e.hom.left c.a c.a_etale
    b_etale := etale_presheaf_comp_isIso B S hS e.hom.right c.b c.b_etale
    comm := comm_comp_arrowIso e _ c.a c.b c.comm
    representative := c.representative
    point := c.point
    maps_to := by
      rw [Space.pointsMap_comp_apply B S hS c.a e.hom.left _, c.maps_to]
  }
  simpa only [Space.EtaleChartAtPoint.sourcePoint] using hdim c'

private theorem relativeDimensionLE_of_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.HasRelativeDimensionLE 1 B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom)) :
    Space.HasRelativeDimensionLE 1 B S hS f.hom := by
  intro x
  let R := OverShriek.relocalizePresheafFunctor g
  let ex := pointsOverLargerBaseEquiv B S S' hS hS' g X.obj
  obtain ⟨d, hd, hdim⟩ := hf (ex x)
  refine ⟨d, hd, ?_⟩
  intro c
  let a' := (relocalizedYonedaIso g c.U).hom ≫ R.map c.a
  let b' := (relocalizedYonedaIso g c.V).hom ≫ R.map c.b
  let h' := (Over.map g).map c.h
  let p' := fieldPointSchemeOverLargerBase B S S' hS hS' g c.U c.representative
  have ha' : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf a' :=
    (presheaf_property_relocalize_iff B S S' hS hS' g (@Etale.{u})
      c.U X c.a).mpr c.a_etale
  have hb' : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf b' :=
    (presheaf_property_relocalize_iff B S S' hS hS' g (@Etale.{u})
      c.V Y c.b).mpr c.b_etale
  have hc' : yoneda.map h' ≫ b' = a' ≫ R.map f.hom := by
    dsimp [a', b', h', R]
    rw [← Category.assoc, relocalizedYonedaIso_naturality]
    simp only [Category.assoc, ← Functor.map_comp, c.comm]
  have hm' : Space.pointsMap B S' hS' _ a'
      (p'.class B S' hS' _) = ex x := by
    let p := c.representative.class B S hS (yoneda.obj c.U)
    have hp : Space.pointsMap B S' hS' _ (relocalizedYonedaIso g c.U).hom
        (p'.class B S' hS' _) =
        pointsOverLargerBaseEquiv B S S' hS hS' g (yoneda.obj c.U) p := by
      have h := pointsSchemeBaseEquiv_class B S S' hS hS' g c.U c.representative
      change Space.pointsMap B S' hS' _ (relocalizedYonedaIso g c.U).inv
        (pointsOverLargerBaseEquiv B S S' hS hS' g (yoneda.obj c.U) p) =
          p'.class B S' hS' _ at h
      rw [← h, ← Space.pointsMap_comp_apply, Iso.inv_hom_id, Space.pointsMap_id_apply]
    show Space.pointsMap B S' hS' _
      ((relocalizedYonedaIso g c.U).hom ≫ R.map c.a)
      (p'.class B S' hS' _) = ex x
    rw [Space.pointsMap_comp_apply, hp]
    show Space.pointsMap B S' hS' _ (R.map c.a)
      (pointsOverLargerBaseEquiv B S S' hS hS' g (yoneda.obj c.U) p) = ex x
    rw [← pointsOverLargerBaseEquiv_naturality, c.maps_to]
  let c' : Space.EtaleChartAtPoint B S' hS' (R.map f.hom) (ex x) := {
    U := (Over.map g).obj c.U
    V := (Over.map g).obj c.V
    a := a'
    b := b'
    h := h'
    a_etale := ha'
    b_etale := hb'
    comm := hc'
    representative := p'
    point := c.point
    maps_to := hm'
  }
  simpa [c', h', p', fieldPointSchemeOverLargerBase,
    Space.EtaleChartAtPoint.sourcePoint,
    AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget] using hdim c'

private theorem finitePresentation_of_largerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : AlgebraicGeometry.Space.IsFinitePresentation B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom))
    (hlfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS f.hom) :
    AlgebraicGeometry.Space.IsFinitePresentation B S hS f.hom := by
  let R := OverShriek.relocalizePresheafFunctor g
  refine ⟨hlfp, quasiCompact_of_largerBase B S S' hS hS' g f hf.2.1, ?_⟩
  let hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f.hom f.hom
    F.property F.property G.property
  let e := (IsPullback.of_hasPullback f.hom f.hom).map R |>.isoPullback
  have he : R.map (pullback.diagonal f.hom) ≫ e.hom =
      pullback.diagonal (R.map f.hom) := by
    apply pullback.hom_ext <;> simp [e, ← R.map_comp]
  have hqc : AlgebraicGeometry.Space.IsQuasiCompact B S' hS'
      (R.map (pullback.diagonal f.hom)) := by
    have h := quasiCompact_postcomp_iso B S' hS' e.symm hf.2.2
    have he' : pullback.diagonal (R.map f.hom) ≫ e.inv =
        R.map (pullback.diagonal f.hom) := by
      rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
    rw [← he']
    simpa only [Iso.symm_hom] using h
  exact quasiCompact_of_largerBase B S S' hS hS' g
    (ObjectProperty.homMk (pullback.diagonal f.hom) :
      F ⟶ (⟨pullback f.hom f.hom, hP⟩ : AlgebraicSpaces B S hS)) hqc

private theorem proper_of_largerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : spaceIsProper B S' hS'
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g F.obj F.property)
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g G.obj G.property)
      ((OverShriek.relocalizePresheafFunctor g).map f.hom))
    (hfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS f.hom) :
    spaceIsProper B S hS F.property G.property f.hom := by
  refine ⟨separated_of_relocalize B S S' hS hS' g f hf.1,
    ⟨?_, hfp.2.1⟩,
    universallyClosed_of_relocalize B S S' hS hS' g f hf.2.2⟩
  intro U V a b i ha hb hi
  let : LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i) :=
    hfp.1 U V a b i ha hb hi
  infer_instance

private theorem finitePresentation_of_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : AlgebraicGeometry.Space.IsFinitePresentation B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom)) :
    AlgebraicGeometry.Space.IsFinitePresentation B S hS f.hom := by
  have hlfp' : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S' hS'
      ((smallerBaseEquivalenceData B S S' hS hS' g).1.functor.map f).hom.left :=
    holdsOnEveryEtaleChart_of_arrowIso B S' hS'
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (smallerBase_relocalize_arrowIso B S S' hS hS' g f) hf.1
  exact finitePresentation_of_largerBase B S S' hS hS' g f hf
    (locallyFinitePresentation_of_largerBase B S S' hS hS' g f hlfp')

private theorem flat_of_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : Space.IsFlat B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom)) :
    Space.IsFlat B S hS f.hom := by
  exact flat_of_largerBase B S S' hS hS' g f
    (holdsOnEveryEtaleChart_of_arrowIso B S' hS'
      (@Flat : MorphismProperty Scheme.{u})
      (smallerBase_relocalize_arrowIso B S S' hS hS' g f) hf)

private theorem equivalence_map_inverse_map_comp_unitInv
    {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    {X : D} {Y : C} (f : X ⟶ e.functor.obj Y) :
    e.functor.map (e.inverse.map f ≫ e.unitIso.inv.app Y) =
      e.counitIso.hom.app X ≫ f := by
  rw [Functor.map_comp, e.fun_inv_map]
  simp only [Category.assoc, e.counitIso_functor_comp, Category.comp_id]

private noncomputable def spaceFamilyOfLargerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (Z : SpacesOverSmallerBase B S S' hS hS' g)
    (a : Z ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T) :
    spaceFamilies B S hS := by
  let e := (smallerBaseEquivalenceData
    B S S' hS hS' g).1
  let b := a ≫ (schemeSpaceOverLargerBaseIso B S S' hS hS' g T).hom
  let t := e.inverse.map b ≫ e.unitIso.inv.app (schemeSpace_ T)
  exact ⟨e.inverse.obj Z, T, t.hom⟩

private noncomputable def spaceFamilyOfLargerBase_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (Z : SpacesOverSmallerBase B S S' hS hS' g)
    (a : Z ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T) :
    Arrow.mk ((OverShriek.relocalizePresheafFunctor g).map
      (spaceFamilyOfLargerBase B S S' hS hS' g T Z a).hom) ≅
      Arrow.mk a.hom.left := by
  let d := smallerBaseEquivalenceData B S S' hS hS' g
  let e := d.1
  let R := OverShriek.relocalizePresheafFunctor g
  let U := schemeSpace_ T
  let H := ObjectProperty.ι (fun Y : Over (yoneda.obj (Over.mk g)) =>
    AlgebraicGeometry.IsAlgebraicSpace B S' hS' Y.left) ⋙
      Over.forget (yoneda.obj (Over.mk g))
  let b := a ≫ (schemeSpaceOverLargerBaseIso B S S' hS hS' g T).hom
  let X := e.inverse.obj Z
  let t := e.inverse.map b ≫ e.unitIso.inv.app U
  let ex : R.obj X.obj ≅ Z.obj.left :=
    (d.2.app X).symm ≪≫ H.mapIso (e.counitIso.app Z)
  let ey := (relocalizedYonedaIso g T).symm
  refine Arrow.isoMk ex ey ?_
  change ex.hom ≫ a.hom.left = R.map t.hom ≫ ey.hom
  suffices hmain : ex.hom ≫ a.hom.left ≫
      (relocalizedYonedaIso g T).hom = R.map t.hom by
    rw [← hmain]
    simp only [ey, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ht := equivalence_map_inverse_map_comp_unitInv e b
  have hn := d.2.hom.naturality t
  change (e.functor.map t).hom.left ≫ (d.2.app U).hom =
    (d.2.app X).hom ≫ R.map t.hom at hn
  rw [ht] at hn
  have hh := congrArg (fun k => (d.2.app X).inv ≫ k) hn
  simp only [Iso.inv_hom_id_assoc] at hh
  change (d.2.app X).inv ≫
      ((e.counitIso.hom.app Z).hom.left ≫ b.hom.left) ≫
        (d.2.app U).hom = R.map t.hom at hh
  rw [← hh]
  dsimp [ex, b]
  have hH : H.map (e.counitIso.hom.app Z) =
      (e.counitIso.hom.app Z).hom.left := rfl
  rw [hH]
  have hiso :
      (schemeSpaceOverLargerBaseIso B S S' hS hS' g T).hom.hom.left ≫
        (d.2.app U).hom = (relocalizedYonedaIso g T).hom := by
    change ((relocalizedYonedaIso g T).hom ≫ (d.2.app U).inv) ≫
      (d.2.app U).hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (by
    simpa only [Category.assoc, Functor.comp_obj, ObjectProperty.ι_obj,
      Iso.app_inv, Iso.app_hom,
      U, schemeSpace_] using
      (congrArg (fun k => (d.2.app X).inv ≫
        (e.counitIso.hom.app Z).hom.left ≫ a.hom.left ≫ k) hiso).symm)

private theorem spaceFamilyOfLargerBase_finitePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (Z : SpacesOverSmallerBase B S S' hS hS' g)
    (a : Z ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T)
    (ha : AlgebraicGeometry.Space.IsFinitePresentation B S' hS' a.hom.left) :
    AlgebraicGeometry.Space.IsFinitePresentation B S hS
      (spaceFamilyOfLargerBase B S S' hS hS' g T Z a).hom := by
  let C := spaceFamilyOfLargerBase B S S' hS hS' g T Z a
  let f : C.left ⟶ schemeSpace_ C.right := ObjectProperty.homMk C.hom
  have hR : AlgebraicGeometry.Space.IsFinitePresentation B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
    finitePresentation_of_arrowIso B S' hS'
      (spaceFamilyOfLargerBase_arrowIso B S S' hS hS' g T Z a) ha
  exact finitePresentation_of_relocalize B S S' hS hS' g f hR

private theorem spaceFamilyOfLargerBase_flat
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (Z : SpacesOverSmallerBase B S S' hS hS' g)
    (a : Z ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T)
    (ha : Space.IsFlat B S' hS' a.hom.left) :
    Space.IsFlat B S hS
      (spaceFamilyOfLargerBase B S S' hS hS' g T Z a).hom := by
  let C := spaceFamilyOfLargerBase B S S' hS hS' g T Z a
  let f : C.left ⟶ schemeSpace_ C.right := ObjectProperty.homMk C.hom
  have hR : Space.IsFlat B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
    holdsOnEveryEtaleChart_of_arrowIso B S' hS'
      (@Flat : MorphismProperty Scheme.{u})
      (spaceFamilyOfLargerBase_arrowIso B S S' hS hS' g T Z a) ha
  exact flat_of_relocalize B S S' hS hS' g f hR

private theorem spaceFamilyOfLargerBase_proper
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (Z : SpacesOverSmallerBase B S S' hS hS' g)
    (a : Z ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T)
    (ha : spaceIsProper B S' hS' Z.property
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S' hS' ((Over.map g).obj T))
      a.hom.left)
    (hfp : AlgebraicGeometry.Space.IsFinitePresentation B S' hS' a.hom.left) :
    spaceIsProper B S hS
      (spaceFamilyOfLargerBase B S S' hS hS' g T Z a).left.property
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
      (spaceFamilyOfLargerBase B S S' hS hS' g T Z a).hom := by
  let C := spaceFamilyOfLargerBase B S S' hS hS' g T Z a
  let f : C.left ⟶ schemeSpace_ C.right := ObjectProperty.homMk C.hom
  let e := spaceFamilyOfLargerBase_arrowIso B S S' hS hS' g T Z a
  have hR : spaceIsProper B S' hS'
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g
        C.left.obj C.left.property)
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g
        (schemeSpace_ C.right).obj (schemeSpace_ C.right).property)
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
    proper_of_arrowIso B S' hS' _ _ Z.property
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S' hS' ((Over.map g).obj T)) e ha
  exact proper_of_largerBase B S S' hS hS' g f hR
    (spaceFamilyOfLargerBase_finitePresentation B S S' hS hS' g T Z a hfp)

private noncomputable def spaceFamilyOfLargerBaseMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (b : T ⟶ T')
    {Z Z' : SpacesOverSmallerBase B S S' hS hS' g}
    (a : Z ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T)
    (a' : Z' ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T')
    (m : Z ⟶ Z')
    (hm : m ≫ a' = a ≫ schemeSpaceOverLargerBaseMap B S S' hS hS' g b) :
    spaceFamilyOfLargerBase B S S' hS hS' g T Z a ⟶
      spaceFamilyOfLargerBase B S S' hS hS' g T' Z' a' := by
  let e := (smallerBaseEquivalenceData
    B S S' hS hS' g).1
  let U := schemeSpace_ T
  let U' := schemeSpace_ T'
  let I := schemeSpaceOverLargerBaseIso B S S' hS hS' g T
  let I' := schemeSpaceOverLargerBaseIso B S S' hS hS' g T'
  let c := schemeSpaceMap_ b
  let t := a ≫ I.hom
  let t' := a' ≫ I'.hom
  have hbase : m ≫ t' = t ≫ e.functor.map c := by
    calc
      m ≫ t' = (m ≫ a') ≫ I'.hom := by simp [t', Category.assoc]
      _ = (a ≫ schemeSpaceOverLargerBaseMap B S S' hS hS' g b) ≫
          I'.hom := by rw [hm]
      _ = t ≫ e.functor.map c := by
        change (a ≫ (I.hom ≫ e.functor.map c ≫ I'.inv)) ≫ I'.hom =
          (a ≫ I.hom) ≫ e.functor.map c
        simp [Category.assoc]
  have hunit := e.unitIso.inv.naturality c
  have hmap := congrArg e.inverse.map hbase
  have hw : e.inverse.map m ≫
      (e.inverse.map t' ≫ e.unitIso.inv.app U') =
      (e.inverse.map t ≫ e.unitIso.inv.app U) ≫ c := by
    calc
      e.inverse.map m ≫ (e.inverse.map t' ≫ e.unitIso.inv.app U') =
          e.inverse.map (m ≫ t') ≫ e.unitIso.inv.app U' := by
            simp only [Functor.map_comp, Category.assoc]
      _ = e.inverse.map (t ≫ e.functor.map c) ≫
          e.unitIso.inv.app U' := by rw [hbase]
      _ = (e.inverse.map t ≫ e.inverse.map (e.functor.map c)) ≫
          e.unitIso.inv.app U' := by rw [Functor.map_comp]
      _ = (e.inverse.map t ≫ e.unitIso.inv.app U) ≫ c := by
            change e.inverse.map (e.functor.map c) ≫ e.unitIso.inv.app U' =
              e.unitIso.inv.app U ≫ c at hunit
            simpa only [Category.assoc] using
              congrArg (fun k => e.inverse.map t ≫ k) hunit
  refine {
    left := e.inverse.map m
    right := b
    w := ?_
  }
  have hh := congrArg (fun k => k.hom) hw
  change (e.inverse.map m).hom ≫
      (e.inverse.map t' ≫ e.unitIso.inv.app U').hom =
    (e.inverse.map t ≫ e.unitIso.inv.app U).hom ≫ c.hom at hh
  change (e.inverse.map m).hom ≫
      (spaceFamilyOfLargerBase B S S' hS hS' g T' Z' a').hom =
    (spaceFamilyOfLargerBase B S S' hS hS' g T Z a).hom ≫
      yoneda.map b
  simpa only [spaceFamilyOfLargerBase, c, schemeSpaceMap_,
    ObjectProperty.homMk_hom] using hh

end CurvesVersality

end AlgebraicGeometry

end
