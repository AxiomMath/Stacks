module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType

/-!
# Separatedness and local finite type over the base under a change of base scheme

Let `g : S ⟶ S'` be a morphism of base schemes of a big fppf site. If the structure morphism of an
algebraic space over `S'` is separated, or locally of finite type, then so is the structure
morphism of its base change along `g`, over `S`.

## Main results

* `AlgebraicGeometry.presheaf_inverseImage_relocalizeRestrict_map`: a relative property coming
  from a property of morphisms of schemes is preserved by base change.
* `AlgebraicGeometry.Space.isSeparated_relocalizeRestrict_map`: **base change preserves
  separatedness.**
* `AlgebraicGeometry.Space.isSeparated_toBase_relocalizeRestrict` and
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_toBase_relocalizeRestrict`: **the structure
  morphism of the base change is separated and locally of finite type.**

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **A relative property of morphisms of presheaves coming from a property of morphisms of
schemes is preserved by base change along a morphism of base schemes.** -/
theorem presheaf_inverseImage_relocalizeRestrict_map (Q : MorphismProperty Scheme.{u})
    (hQ : MorphismProperty.RespectsIso Q)
    {A G : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} {h : A ⟶ G}
    (hh : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S' hS')).presheaf h) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      ((OverShriek.relocalizeRestrict g).map h) :=
  let _ := hQ
  let _ : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  OverShriek.relative_relocalizeRestrict_map g
    (fun s hs => inverseImage_restrictReindexSnd B S S' hS hS' g Q s hs) hh

/-- The identity of a representable presheaf has, relatively, every property of morphisms of
schemes that holds for all isomorphisms. -/
theorem presheaf_inverseImage_id_yoneda (P : MorphismProperty Scheme.{u})
    (hP : ∀ {V W : Scheme.{u}} (q : V ⟶ W), IsIso q → P q) (U : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (𝟙 (yoneda.obj U)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro a b q fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  exact hP _ (Functor.map_isIso (BigFppfOver.toScheme B S hS) snd)

/-- Every object of the big fppf site over `S` maps to the base `S` itself. -/
private theorem exists_hom_to_base (T : Scheme.{u}) (hT : B.Contains T) (U : BigFppfOver B T hT) :
    ∃ p : U ⟶ (Over.mk (𝟙 (B.obj hT)) : BigFppfOver B T hT),
      (BigFppfOver.toScheme B T hT).map p = B.inclusion.map U.hom :=
  ⟨Over.homMk U.hom (Category.comp_id _), rfl⟩

/-- The identity of a representable presheaf is relatively étale. -/
private theorem presheaf_inverseImage_etale_id_yoneda (U : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj U)) :=
  presheaf_inverseImage_id_yoneda B S hS (@_root_.AlgebraicGeometry.Etale.{u})
    (fun _ hq => have := hq; inferInstance) U

namespace Space

/-- Pullbacks of presheaves on a big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_structureMorphismBaseChange
    {T : Scheme.{u}} {hT : B.Contains T} {X Y Z : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {X Y : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}

/-- **Base change along a morphism of base schemes preserves separatedness.** -/
theorem isSeparated_relocalizeRestrict_map (f : X ⟶ Y)
    (hf : IsSeparated B S' hS' f) :
    IsSeparated B S hS ((OverShriek.relocalizeRestrict g).map f) := by
  have hdiag : (OverShriek.relocalizeRestrict g).map (pullback.diagonal f) ≫
      (PreservesPullback.iso (OverShriek.relocalizeRestrict g) f f).hom =
    pullback.diagonal ((OverShriek.relocalizeRestrict g).map f) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp,
        pullback.diagonal_fst, CategoryTheory.Functor.map_id, pullback.diagonal_fst]
    · rw [Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp,
        pullback.diagonal_snd, CategoryTheory.Functor.map_id, pullback.diagonal_snd]
  unfold IsSeparated
  have h1 := presheaf_inverseImage_relocalizeRestrict_map B S S' hS hS' g
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    inferInstance hf
  rw [← hdiag]
  exact MorphismProperty.RespectsIso.postcomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
    (PreservesPullback.iso (OverShriek.relocalizeRestrict g) f f).hom _
    h1

/-- The base, read as an algebraic space over itself, is the terminal presheaf on the big fppf
site. -/
noncomputable def baseYoneda_isTerminal :
    IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS)) :=
  yonedaMkIdTerminal B S hS

/-- **Base change along a morphism of base schemes preserves separatedness over the base.** -/
theorem isSeparated_toBase_relocalizeRestrict
    (z : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS')) : BigFppfOver B S' hS'))
    (hz : IsSeparated B S' hS' z) :
    IsSeparated B S hS
      ((baseYoneda_isTerminal B S hS).from ((OverShriek.relocalizeRestrict g).obj X)) := by
  have hterm : IsTerminal ((OverShriek.relocalizeRestrict g).obj
      (yoneda.obj (Over.mk (𝟙 (B.obj hS')) : BigFppfOver B S' hS'))) :=
    (baseYoneda_isTerminal B S' hS').isTerminalObj (OverShriek.relocalizeRestrict g) _
  exact (isSeparated_arrow_mk_iso_iff B S hS
    (Arrow.isoMk (Iso.refl ((OverShriek.relocalizeRestrict g).obj X))
      (hterm.uniqueUpToIso (baseYoneda_isTerminal B S hS))
      ((baseYoneda_isTerminal B S hS).hom_ext _ _) :
      Arrow.mk ((OverShriek.relocalizeRestrict g).map z) ≅
        Arrow.mk ((baseYoneda_isTerminal B S hS).from
          ((OverShriek.relocalizeRestrict g).obj X)))).1
    (isSeparated_relocalizeRestrict_map B S S' hS hS' g z hz)

/-- **Base change along a morphism of base schemes preserves local finite type over the base.** -/
theorem isLocallyOfFiniteType_toBase_relocalizeRestrict
    (hX : IsAlgebraicSpace B S' hS' X)
    (z : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS')) : BigFppfOver B S' hS'))
    (hz : IsLocallyOfFiniteType B S' hS' z) :
    IsLocallyOfFiniteType B S hS
      ((baseYoneda_isTerminal B S hS).from ((OverShriek.relocalizeRestrict g).obj X)) := by
  obtain ⟨U, a, hasurj, haetale⟩ := hX.exists_atlas
  obtain ⟨pU, hpU⟩ := exists_hom_to_base B S' hS' U
  have hUlft : _root_.AlgebraicGeometry.LocallyOfFiniteType (B.inclusion.map U.hom) := by
    rw [← hpU]
    exact hz U (Over.mk (𝟙 (B.obj hS'))) a (𝟙 _) pU haetale
      (presheaf_inverseImage_etale_id_yoneda B S' hS' _)
      ((baseYoneda_isTerminal B S' hS').hom_ext _ _)
  obtain ⟨pU', hpU'⟩ := exists_hom_to_base B S hS ((Over.pullback g).obj U)
  have key : ∀ {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
      {h : yoneda.obj U ⟶ X}, (MorphismProperty.inverseImage Q
        (BigFppfOver.toScheme B S' hS')).presheaf h →
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
        ((OverShriek.restrictYonedaIso g U).hom ≫ (OverShriek.relocalizeRestrict g).map h) :=
    fun hh => MorphismProperty.RespectsIso.precomp _ (OverShriek.restrictYonedaIso g U).hom _
      (presheaf_inverseImage_relocalizeRestrict_map B S S' hS hS' g _ inferInstance hh)
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_relocalizeRestrict B S S' hS hS' g X hX)
    (isAlgebraicSpace_yoneda B S hS _) _).2 ?_
  refine ⟨(Over.pullback g).obj U, Over.mk (𝟙 (B.obj hS)),
    (OverShriek.restrictYonedaIso g U).hom ≫ (OverShriek.relocalizeRestrict g).map a,
    𝟙 _, pU', ?_, ?_, ?_, ?_, ?_⟩
  · exact key haetale
  · exact presheaf_inverseImage_etale_id_yoneda B S hS _
  · exact key hasurj
  · exact (baseYoneda_isTerminal B S hS).hom_ext _ _
  · rw [hpU']
    exact MorphismProperty.of_isPullback
      (IsPullback.map B.inclusion (IsPullback.of_hasPullback U.hom g)) hUlft

end Space

end AlgebraicGeometry

end
