module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedStageColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedQuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSchemeStack

/-!
# Presenting a quasi-compact quasi-separated formal algebraic space by thickenings

Let `S` be a scheme contained in a big fppf site `B`. A formal algebraic space `X` over `S` which
is quasi-compact and quasi-separated is a directed colimit `X = colim X_λ` of algebraic spaces
`X_λ` over `S` in which every transition morphism `f_{λμ} : X_λ ⟶ X_μ` is a thickening.

## Main results

* `AlgebraicGeometry.FormalSpace.isThickeningHom_yonedaSpace_map`: a morphism of the big fppf
  site whose underlying morphism of schemes is a thickening induces a thickening of the
  algebraic spaces represented by its source and target.
* `AlgebraicGeometry.FormalSpace.exists_colimit_presentation_of_isAffineFormalAlgebraicSpace`: an
  affine formal algebraic space over `S` is a directed colimit of algebraic spaces over `S` along
  thickenings.
* `AlgebraicGeometry.FormalSpace.isThickeningHom_of_isRepresentableThickeningULift`: a morphism
  of algebraic spaces over `S` whose universe lift is, up to isomorphism, a representable
  thickening surjective on points, is a thickening.
* `AlgebraicGeometry.FormalSpace.exists_colimit_presentation_of_quasiCompact_quasiSeparated`: a
  quasi-compact quasi-separated formal algebraic space over `S` is a directed colimit of algebraic
  spaces over `S` along thickenings.

## References

* [Stacks Project, Tag 0AJE](https://stacks.math.columbia.edu/tag/0AJE)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0AJ5](https://stacks.math.columbia.edu/tag/0AJ5)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A thickening of schemes of the site is a thickening of algebraic spaces -/

/-- If the underlying morphism of schemes of `i : U ⟶ V` is a thickening, a closed immersion
which is surjective on points, then the induced morphism of the algebraic spaces represented by
`U` and `V` is a thickening: it is an isomorphism onto its range, and that range is a closed
subspace of `yoneda.obj V` with the same points. -/
theorem isThickeningHom_yonedaSpace_map {U V : BigFppfOver B S hS} (i : U ⟶ V)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i)) :
    Space.IsThickeningHom B S hS ((schemeSpaceFunctor B S hS).map i) := by
  classical
  have hclosed : Space.IsClosedImmersion B S hS (yoneda.map i) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) i).2 hi.1
  have hsub : Space.IsClosedSubspace B S hS (Subfunctor.range (yoneda.map i)) :=
    Space.isClosedSubspace_range_yoneda_map B S hS i hi.1
  have hPmono : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ≤
      MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
    intro A A' g hg
    have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g) := hg
    exact ⟨fun g₁ g₂ hgg => Functor.map_injective (BigFppfOver.toScheme B S hS)
      ((cancel_mono ((BigFppfOver.toScheme B S hS).map g)).1
        (congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) hgg))⟩
  have hmono : Mono (yoneda.map i) :=
    MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
      (MorphismProperty.relative_monotone hPmono _ hclosed)
  have hiso : IsIso (Subfunctor.toRange (yoneda.map i)) := inferInstance
  have heq : (asIso (Subfunctor.toRange (yoneda.map i))).inv ≫ yoneda.map i =
      (Subfunctor.range (yoneda.map i)).ι :=
    (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι (yoneda.map i)).symm
  have hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.Surjective.{u}) i).2 ⟨hi.2⟩
  have hrange : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (Subfunctor.range (yoneda.map i)).ι := by
    have h := MorphismProperty.RespectsIso.precomp
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (asIso (Subfunctor.toRange (yoneda.map i))).inv (yoneda.map i) hsurj
    rwa [heq] at h
  have hpts : Function.Surjective (Space.pointsMap B S hS
      (Subfunctor.range (yoneda.map i)).toFunctor (Subfunctor.range (yoneda.map i)).ι) :=
    (Space.surjective_iff_pointsMap_surjective B S hS hsub.1
      (isAlgebraicSpace_yoneda B S hS V) _ hsub.2.rep).1 hrange
  exact ⟨hiso, hsub, hpts⟩

/-- An affine formal algebraic space over `S` is a directed colimit of algebraic spaces over `S`
along thickenings. -/
@[stacks 0AJE "the conclusion for an AFFINE formal algebraic space only; the general \
quasi-compact quasi-separated case is not proved here, see the implementation notes"]
public theorem exists_colimit_presentation_of_isAffineFormalAlgebraicSpace
    (X : FppfSheaf B S hS) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (Λ : Type (u + 1)) (pre : Preorder Λ),
      letI : Preorder Λ := pre
      Nonempty Λ ∧ IsDirected Λ (· ≤ ·) ∧
        ∃ D : Λ ⥤ AlgebraicSpaces B S hS,
          (∀ ⦃i j : Λ⦄ (f : i ⟶ j), Space.IsThickeningHom B S hS (D.map f)) ∧
          Nonempty (X ≅ colimit (D ⋙ liftSheafFunctor B S hS)) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, I, pre, hne, hdir, D, hthick, ⟨e⟩⟩ := hX
  refine ⟨I, pre, hne, hdir,
    D ⋙ BigAffineFppf.inclusion B S hS ⋙ schemeSpaceFunctor B S hS, ?_, ?_⟩
  · intro i j f
    exact isThickeningHom_yonedaSpace_map B S hS _ (hthick f)
  · exact ⟨e ≪≫ (HasColimit.isoOfNatIso
      (Functor.isoWhiskerLeft (D ⋙ BigAffineFppf.inclusion B S hS)
        (yonedaSpaceCompLiftSheafFunctorIsoSheafifiedYoneda B S hS))).symm⟩

/-! ### Stacks 0AJE -/

/-- A morphism of algebraic spaces whose universe lift is, up to isomorphism, a representable
thickening surjective on points, is a thickening. -/
theorem isThickeningHom_of_isRepresentableThickeningULift
    {Wi Wj : AlgebraicSpaces B S hS} (f : Wi ⟶ Wj)
    {Ti Tj : FppfSheaf B S hS} (ei : (liftSheafFunctor B S hS).obj Wi ≅ Ti)
    (ej : (liftSheafFunctor B S hS).obj Wj ≅ Tj) (τ : Ti ⟶ Tj)
    (hcomm : (liftSheafFunctor B S hS).map f ≫ ej.hom = ei.hom ≫ τ)
    (hth : Space.IsRepresentableThickeningULift.{u + 1} B S hS τ.hom)
    (hpts : Function.Surjective (Space.pointsMapULift.{u + 1} B S hS Ti.obj τ.hom)) :
    Space.IsThickeningHom B S hS f := by
  classical
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS))
    (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS))
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have hf : (liftSheafFunctor B S hS).map f = ei.hom ≫ τ ≫ ej.inv := by
    rw [← Category.assoc, ← hcomm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hfhom : ((liftSheafFunctor B S hS).map f).hom =
      ei.hom.hom ≫ τ.hom ≫ ej.inv.hom :=
    congrArg (fun k : (liftSheafFunctor B S hS).obj Wi ⟶ (liftSheafFunctor B S hS).obj Wj =>
      k.hom) hf
  have hiei : IsIso ei.hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
      ei.hom))
  have hiej : IsIso ej.inv.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
      ej.inv))
  have hthf : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      ((liftSheafFunctor B S hS).map f).hom := by
    rw [hfhom]
    exact MorphismProperty.RespectsIso.precomp _ ei.hom.hom _
      (MorphismProperty.RespectsIso.postcomp _ ej.inv.hom τ.hom hth)
  have hclf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
      (Functor.whiskerRight f.hom uliftFunctor.{u + 1}) := by
    exact MorphismProperty.relative_monotone (fun _ _ k hk ↦ hk.1) _ hthf
  refine Space.isThickeningHom_of_isClosedImmersion_of_surjective_pointsMap B S hS f
    ((Space.relative_uliftYoneda_whiskerRight_iff' B S hS _ f.hom).mp hclf) ?_
  have hcomp := Space.pointsMapULift_whiskerRight_pointsULiftEquiv.{u + 1} B S hS f.hom
  have hsurj : Function.Surjective (Space.pointsMapULift.{u + 1} B S hS
      ((liftSheafFunctor B S hS).obj Wi).obj
      (Functor.whiskerRight f.hom uliftFunctor.{u + 1})) := by
    change Function.Surjective (Space.pointsMapULift.{u + 1} B S hS _
      ((liftSheafFunctor B S hS).map f).hom)
    rw [hfhom, Space.pointsMapULift_comp, Space.pointsMapULift_comp]
    refine Function.Surjective.comp (Function.Surjective.comp ?_ hpts) ?_
    · simpa only [asIso_hom] using
        (Space.bijective_pointsMapULift_of_iso.{u + 1} B S hS (asIso ej.inv.hom)).2
    · simpa only [asIso_hom] using
        (Space.bijective_pointsMapULift_of_iso.{u + 1} B S hS (asIso ei.hom.hom)).2
  intro p
  obtain ⟨q, hq⟩ := hsurj (Space.pointsULiftEquiv.{u + 1} B S hS Wj.obj p)
  obtain ⟨q', rfl⟩ := (Space.pointsULiftEquiv.{u + 1} B S hS Wi.obj).surjective q
  refine ⟨q', ?_⟩
  apply (Space.pointsULiftEquiv.{u + 1} B S hS Wj.obj).injective
  have h := congrFun hcomp q'
  simp only [Function.comp_apply] at h
  rwa [← h]

/-- Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S` which is quasi-compact and quasi-separated. Then `X` is a directed colimit of algebraic
spaces over `S` all of whose transition morphisms are thickenings. -/
@[stacks 0AJE]
theorem exists_colimit_presentation_of_quasiCompact_quasiSeparated
    (X : FppfSheaf B S hS) (_hX : IsFormalAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsQuasiSeparated B S hS X) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (Λ : Type (u + 1)) (pre : Preorder Λ),
      letI : Preorder Λ := pre
      Nonempty Λ ∧ IsDirected Λ (· ≤ ·) ∧
        ∃ D : Λ ⥤ AlgebraicSpaces B S hS,
          (∀ ⦃i j : Λ⦄ (f : i ⟶ j), Space.IsThickeningHom B S hS (D.map f)) ∧
          Nonempty (X ≅ colimit (D ⋙ liftSheafFunctor B S hS)) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hset, A, c, hA, ⟨hcrep, hcetU⟩, hcs⟩ := hqc
  have hc : (fppfYoneda B S hS).relativelyRepresentable c :=
    relativelyRepresentable_sheafifiedYoneda_of_isAffineFormalAlgebraicSpace B S hS c hA
      (small_of_satisfiesSetTheoreticCondition B S hS hset) hcrep hcetU
  have hcet : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) c.hom :=
    relative_etaleOnSite_of_isRepresentableEtale B S hS c hc ⟨hcrep, hcetU⟩
  have hcsurj : (Space.surjectiveOnSite B S hS).relative (uliftYoneda.{u + 1}) c.hom :=
    relative_surjectiveOnSite_of_isLocallySurjective B S hS c
      ((relativelyRepresentable_sheafifiedYoneda_iff_uliftYoneda B S hS c).mp hc) hcs
  obtain ⟨-, Ix, pre, hne, hdir, Dg, hDg, ⟨e⟩⟩ := hA
  let : Preorder Ix := pre
  let : Nonempty Ix := hne
  let : IsDirected Ix (· ≤ ·) := hdir
  obtain ⟨Z, z, hzth, hzfac, hzmon, hzinv⟩ :=
    exists_invariantStageSystem B S hS Dg hDg e c hc hqs hcet
  have hzpmono (i : Ix) : Mono (uliftYonedaHom B S hS (z i)) :=
    Space.mono_of_relative_isClosedImmersion B S hS _
      (MorphismProperty.relative_monotone (fun _ _ k hk ↦ hk.1) _ (hzth i))
  have hle : ∀ ⦃i j : Ix⦄, (i ⟶ j) →
      (Subfunctor.range (z i ≫ c).hom).sheafify (BigFppfOver.topology B S hS) ≤
        (Subfunctor.range (z j ≫ c).hom).sheafify (BigFppfOver.topology B S hS) := by
    intro i j g
    obtain ⟨w, hw⟩ := hzmon g
    exact sheafifyRange_le_of_factor B S hS c (z i) (z j) w hw
  set E := stageSubsheafDiagram B S hS c Z z hle
  have hEimg : ∀ i, (liftSheafFunctor B S hS).essImage (E.obj i) := by
    intro i
    obtain ⟨R, t, r, hinv⟩ := hzinv i
    obtain ⟨W, hW, ⟨eW⟩⟩ := Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS
      (isAlgebraicSpaceULift_image_of_invariant B S hS c (z i) (hzpmono i) t r hinv
        hcsurj hcet)
    exact ⟨⟨W, hW⟩, ⟨(sheafToPresheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).preimageIso eW⟩⟩
  have hcomp := Functor.essImage.liftFunctorCompIso E (liftSheafFunctor B S hS) hEimg
  refine ⟨Ix, pre, hne, hdir,
    Functor.essImage.liftFunctor E (liftSheafFunctor B S hS) hEimg, ?_, ?_⟩
  · intro i j g
    obtain ⟨w, hw⟩ := hzmon g
    obtain ⟨Ri, ti, ri, hinvi⟩ := hzinv i
    obtain ⟨Rj, tj, rj, hinvj⟩ := hzinv j
    have hEmap : E.map g = imageTransition B S hS c (z i) (z j) w hw := rfl
    refine isThickeningHom_of_isRepresentableThickeningULift B S hS _
      (hcomp.app i) (hcomp.app j) (E.map g) (hcomp.hom.naturality g) ?_ ?_
    · rw [hEmap]
      exact isRepresentableThickening_imageTransition B S hS c (z i) (z j) w hw
        (hzpmono i) (hzpmono j) ti ri tj rj hinvi hinvj hcet (hzth i)
    · rw [hEmap]
      exact surjective_pointsMapULift_imageTransition B S hS c (z i) (z j) w hw
        ⟨(isThickening_transition B S hS (z i) (z j) w hw (hzth i) (hzpmono j)).2⟩
  · exact (nonempty_iso_colimit_stageSubsheafDiagram B S hS Dg hDg e c Z z hle hcs hzfac).map
      (· ≪≫ (HasColimit.isoOfNatIso hcomp).symm)

end AlgebraicGeometry.FormalSpace

end
