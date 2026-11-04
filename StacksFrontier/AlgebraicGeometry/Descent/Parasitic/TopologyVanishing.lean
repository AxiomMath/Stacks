module

public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatVanishing
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.CohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.Defs
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.Torsor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiPrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Stability
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a module parasitic for a topology

A sheaf of modules on one of the five standard big sites of a scheme `S` whose sections vanish
on the members of every covering of `S` itself has vanishing cohomology at every object of the
site whose structure morphism has the property defining the topology — open immersion, étale,
smooth, syntomic, or flat and locally of finite presentation respectively.

The hypothesis is the pointwise expansion of `AlgebraicGeometry.IsParasiticFor`, for a sheaf of
modules over an arbitrary sheaf of rings on the site.

## Main results

* `AlgebraicGeometry.cohomology_isZero_of_isParasiticFor_zariski`: vanishing at objects open over
  `S` in the big Zariski site.
* `AlgebraicGeometry.cohomology_isZero_of_isParasiticFor_etale`: vanishing at objects étale over
  `S` in the big étale site.
* `AlgebraicGeometry.cohomology_isZero_of_isParasiticFor_smooth`: vanishing at objects smooth
  over `S` in the big smooth site.
* `AlgebraicGeometry.cohomology_isZero_of_isParasiticFor_syntomic`: vanishing at objects
  syntomic over `S` in the big syntomic site.
* `AlgebraicGeometry.cohomology_isZero_of_isParasiticFor_fppf`: vanishing at objects flat and
  locally of finite presentation over `S` in the big fppf site.

## References

* [Stacks Project, Tag 0755](https://stacks.math.columbia.edu/tag/0755)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w u'

namespace AlgebraicGeometry

private lemma presieve_uncurry {C : Type (u + 1)} [Category.{u} C] {X : C}
    (R : Presieve X) :
    (⟨R.uncurry, fun i ↦ i.1.1, fun i ↦ i.1.2⟩ : PreZeroHypercover.{u + 1} X).presieve₀ = R := by
  funext Y f
  exact propext ⟨fun ⟨i⟩ ↦ i.2, fun hf ↦ Presieve.ofArrows.mk (⟨⟨Y, f⟩, hf⟩ : R.uncurry)⟩

private noncomputable def overFiniteProductObj
    {C : Type u'} [Category.{u} C] [HasPullbacks C] {U : C} {n : ℕ}
    (f : Fin n → C) (g : ∀ i, f i ⟶ U) : Over U := by
  let : HasBinaryProducts (Over U) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let : HasFiniteProducts (Over U) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact piObj (fun i ↦ Over.mk (g i))

private lemma finiteOverProduct_hom_property
    {C : Type u'} [Category.{u} C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.ContainsIdentities] [P.RespectsIso]
    {U : C} : ∀ (n : ℕ) (X : Fin n → C) (f : ∀ i, X i ⟶ U),
      (∀ i, P (f i)) →
        P ((overFiniteProductObj X f).hom) := by
  intro n
  induction n with
  | zero =>
      intro X f hf
      let : HasTerminal (Over U) := Over.over_hasTerminal U
      let : HasBinaryProducts (Over U) :=
        Over.ConstructProducts.over_binaryProduct_of_pullback
      let : HasFiniteProducts (Over U) :=
        hasFiniteProducts_of_has_binary_and_terminal
      change P ((piObj (fun i ↦ Over.mk (f i) : Fin 0 → Over U)).hom)
      let F : Discrete (Fin 0) ⥤ Over U := Discrete.functor (fun i ↦ Over.mk (f i))
      have hT : IsTerminal (piObj (fun i ↦ Over.mk (f i) : Fin 0 → Over U)) :=
        (isLimitEquivIsTerminalOfIsEmpty (Over U) (F := F) (limit.cone F)).1
          (limit.isLimit F)
      have hId : IsTerminal (Over.mk (𝟙 U)) := Over.mkIdTerminal
      let e := hT.uniqueUpToIso hId
      have heq :
          (piObj (fun i ↦ Over.mk (f i) : Fin 0 → Over U)).hom = e.hom.left := by
        simpa using e.hom.w.symm
      rw [heq]
      have : IsIso e.hom.left := Functor.map_isIso (Over.forget U) e.hom
      exact MorphismProperty.of_isIso P _
  | succ n ih =>
      intro X f hf
      let : HasTerminal (Over U) := Over.over_hasTerminal U
      let : HasBinaryProducts (Over U) :=
        Over.ConstructProducts.over_binaryProduct_of_pullback
      let : HasFiniteProducts (Over U) :=
        hasFiniteProducts_of_has_binary_and_terminal
      let F₀ : Discrete (Fin n) ⥤ Over U :=
        Discrete.functor (fun i ↦ Over.mk (f i.succ))
      let c₁ : Fan (fun i : Fin n ↦ Over.mk (f i.succ)) := limit.cone F₀
      have hc₁ : IsLimit c₁ := limit.isLimit F₀
      let c₂ : BinaryFan (Over.mk (f 0)) c₁.pt :=
        BinaryFan.mk Limits.prod.fst Limits.prod.snd
      have hc₂ : IsLimit c₂ := prodIsProd _ _
      have hfull : IsLimit (extendFan c₁ c₂) :=
        extendFanIsLimit (fun i : Fin (n + 1) ↦ Over.mk (f i)) hc₁ hc₂
      let F : Discrete (Fin (n + 1)) ⥤ Over U :=
        Discrete.functor (fun i ↦ Over.mk (f i))
      let e := IsLimit.conePointUniqueUpToIso (limit.isLimit F) hfull
      have htail := ih (fun i ↦ X i.succ) (fun i ↦ f i.succ) (fun i ↦ hf i.succ)
      have hfst : P c₂.fst.left := by
        let e₀ := Over.prodLeftIsoPullback (Over.mk (f 0)) c₁.pt
        have he : e₀.hom ≫ pullback.fst (f 0) c₁.pt.hom = c₂.fst.left := by
          simpa [c₂, e₀] using
            (Over.prodLeftIsoPullback_hom_fst (Over.mk (f 0)) c₁.pt)
        rw [← he]
        exact MorphismProperty.RespectsIso.precomp P _ _
          (P.pullback_fst _ _ htail)
      have hprod : P c₂.pt.hom := by
        have hcomp : c₂.fst.left ≫ (Over.mk (f 0)).hom = c₂.pt.hom := c₂.fst.w
        rw [← hcomp]
        exact P.comp_mem _ _ hfst (hf 0)
      have : IsIso e.hom.left := Functor.map_isIso (Over.forget U) e.hom
      have heq :
          (piObj (fun i ↦ Over.mk (f i) : Fin (n + 1) → Over U)).hom =
            e.hom.left ≫ c₂.pt.hom :=
        e.hom.w.symm
      change P ((piObj (fun i ↦ Over.mk (f i) : Fin (n + 1) → Over U)).hom)
      rw [heq]
      exact MorphismProperty.RespectsIso.precomp P e.hom.left c₂.pt.hom hprod

private abbrev overCoverOfFamily {C : Type (u + 1)} [Category.{u} C] {S : C}
    (E : PreZeroHypercover.{u + 1} S) :
    PreZeroHypercover.{u + 1} (Over.mk (𝟙 S)) :=
  ⟨E.I₀, fun i ↦ Over.mk (E.f i), fun i ↦ Over.homMk (E.f i) (by simp)⟩

private lemma identity_add_mem_precoverage
    {C : Type (u + 1)} [Category.{u} C] (I : C ⥤ Scheme.{u})
    (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities]
    {S : C} (U : Over S) (hU : P (I.map U.hom)) :
    (((PreZeroHypercover.singleton (𝟙 S)).add U.hom).map I).presieve₀ ∈
      Scheme.precoverage P (I.obj S) := by
  rw [Scheme.ofArrows_mem_precoverage_iff]
  constructor
  · intro x
    refine ⟨some PUnit.unit, x, ?_⟩
    change (I.map (𝟙 S)) x = x
    rw [I.map_id]
    rfl
  · rintro (i | ⟨⟩)
    · exact hU
    · change P (I.map (𝟙 S))
      rw [I.map_id]
      exact MorphismProperty.id_mem P _

private alias syntomic_identity := AlgebraicGeometry.syntomic_id

private lemma subsingleton_of_isIso_map {C : Type (u + 1)} [Category.{u} C]
    (F : C ⥤ AddCommGrpCat.{u}) {X Y : C} (f : X ⟶ Y) [IsIso f]
    (hX : Subsingleton (F.obj X)) : Subsingleton (F.obj Y) := by
  let φ := F.map f
  constructor
  intro x y
  have h := hX.elim (inv φ x) (inv φ y)
  have hh := congrArg φ h
  simpa only [← CategoryTheory.comp_apply, IsIso.inv_hom_id, CategoryTheory.id_apply] using hh

private lemma subsingleton_over_of_eq {C : Type (u + 1)} [Category.{u} C]
    {S : C} (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}) {U V : Over S}
    (h : U.left = V.left) (hf : eqToHom h ≫ V.hom = U.hom)
    (hV : Subsingleton (F.obj (Opposite.op V))) :
    Subsingleton (F.obj (Opposite.op U)) := by
  let g : U ⟶ V := Over.homMk (eqToHom h) hf
  have : IsIso ((Over.forget S).map g) := by
    change IsIso (eqToHom h)
    infer_instance
  have : IsIso g := isIso_of_reflects_iso g (Over.forget S)
  exact subsingleton_of_isIso_map F g.op hV

private lemma subsingleton_of_add_representative
    {C : Type (u + 1)} [Category.{u} C] {S : C}
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Over S)
    (E' : PreZeroHypercover.{u + 1} S)
    (hComb : PreZeroHypercover.CombinatoriallyEquivalent
      ((PreZeroHypercover.singleton (𝟙 S)).add U.hom) E')
    (hZero : ∀ i, Subsingleton (F.obj (Opposite.op (Over.mk (E'.f i))))) :
    Subsingleton (F.obj (Opposite.op U)) := by
  obtain ⟨α, hX, hF⟩ := hComb.1
  let iU : ((PreZeroHypercover.singleton (𝟙 S)).add U.hom).I₀ := none
  have hsource : U.left = E'.X (α iU) := by
    simpa [iU, PreZeroHypercover.add_X_none] using hX iU
  have hcomm : eqToHom hsource ≫ E'.f (α iU) = U.hom := by
    have hf := hF iU
    change U.hom = eqToHom hsource ≫ E'.f (α iU) at hf
    exact hf.symm
  exact subsingleton_over_of_eq F hsource hcomm (hZero (α iU))

/-- Sections over `U` vanish when they vanish on the members of a chosen covering of the base
combinatorially equivalent to `U` together with the identity. -/
private lemma subsingleton_of_covering_representative
    {C : Type (u + 1)} [Category.{u} C] {D : Type*} [Category D] (I : C ⥤ D) {S : C}
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Over S) (IsCov : Covering.{u + 1, u, u + 1} C → Prop)
    (hF : ∀ E : Covering (Over S), IsIso (((Over.post I).obj E.1).hom) →
      IsCov ⟨E.1.left, E.2.map (Over.forget S)⟩ →
      ∀ i : E.2.I₀, Subsingleton (F.obj (Opposite.op (E.2.X i))))
    (hrep : ∃ 𝒰' : Covering.{u + 1, u, u + 1} C, IsCov 𝒰' ∧
      Covering.CombEquiv ⟨S, (PreZeroHypercover.singleton (𝟙 S)).add U.hom⟩ 𝒰') :
    Subsingleton (F.obj (Opposite.op U)) := by
  obtain ⟨⟨T, E'⟩, hE', hTargetEq, hComb⟩ := hrep
  cases hTargetEq
  have : IsIso (((Over.post I).obj (Over.mk (𝟙 S))).hom) := by
    change IsIso (I.map (𝟙 S))
    infer_instance
  exact subsingleton_of_add_representative F U E' hComb
    (hF ⟨Over.mk (𝟙 S), overCoverOfFamily E'⟩ this hE')

private lemma zariski_section_subsingleton
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒪 : Sheaf (AlgebraicGeometry.BigZariskiOver.topology B S hS) RingCat.{u}}
    (G : SheafOfModules.{u} 𝒪)
    (hG : ∀ E : Covering (AlgebraicGeometry.BigZariskiOver B S hS),
      IsIso (((Over.post B.inclusion).obj E.1).hom) →
      AlgebraicGeometry.BigZariskiOver.IsCovering B S hS E →
      ∀ i : E.2.I₀, Subsingleton (G.val.obj (Opposite.op (E.2.X i))))
    (U : AlgebraicGeometry.BigZariskiOver B S hS)
    (hU : IsOpenImmersion ((Over.post B.inclusion).obj U).hom) :
    Subsingleton (G.val.obj (Opposite.op U)) := by
  let S₀ : B.Schemes := ⟨S, hS⟩
  let E₁ : PreZeroHypercover.{u + 1} S₀ := PreZeroHypercover.singleton (𝟙 S₀)
  let E : PreZeroHypercover.{u + 1} S₀ := E₁.add U.hom
  have hE : AlgebraicGeometry.IsZariskiCovering ⟨S₀, E⟩ := by
    change (E.map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology S
    change (E.map B.inclusion).presieve₀ ∈ Scheme.precoverage (@IsOpenImmersion) S
    exact identity_add_mem_precoverage B.inclusion IsOpenImmersion U hU
  exact subsingleton_of_covering_representative _ G.val.presheaf U _ hG
    (B.covering_representative ⟨S₀, E⟩ hE)

private lemma etale_section_subsingleton
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒪 : Sheaf (AlgebraicGeometry.BigEtaleOver.topology B S hS) RingCat.{u}}
    (G : SheafOfModules.{u} 𝒪)
    (hG : ∀ E : Covering (AlgebraicGeometry.BigEtaleOver B S hS),
      IsIso (((Over.post B.inclusion).obj E.1).hom) →
      AlgebraicGeometry.BigEtaleOver.IsCovering B S hS E →
      ∀ i : E.2.I₀, Subsingleton (G.val.obj (Opposite.op (E.2.X i))))
    (U : AlgebraicGeometry.BigEtaleOver B S hS)
    (hU : Etale ((Over.post B.inclusion).obj U).hom) :
    Subsingleton (G.val.obj (Opposite.op U)) := by
  let S₀ : B.Scheme := ⟨S, hS⟩
  let E₁ : PreZeroHypercover.{u + 1} S₀ := PreZeroHypercover.singleton (𝟙 S₀)
  let E : PreZeroHypercover.{u + 1} S₀ := E₁.add U.hom
  have hE : AlgebraicGeometry.IsEtaleCovering ⟨S₀, E⟩ := by
    change (E.map B.inclusion).presieve₀ ∈ Scheme.etalePretopology S
    change (E.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (@Etale : MorphismProperty Scheme.{u}) S
    let : MorphismProperty.ContainsIdentities
        (@Etale : MorphismProperty Scheme.{u}) := ⟨fun X ↦ by infer_instance⟩
    exact identity_add_mem_precoverage B.inclusion (@Etale) U hU
  exact subsingleton_of_covering_representative _ G.val.presheaf U _ hG
    (B.exists_covering_rep ⟨S₀, E⟩ hE)

private lemma smooth_section_subsingleton
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    {𝒪 : Sheaf (AlgebraicGeometry.BigSmoothOver.topology B S hS) RingCat.{u}}
    (G : SheafOfModules.{u} 𝒪)
    (hG : ∀ E : Covering (AlgebraicGeometry.BigSmoothOver B S hS),
      IsIso (((Over.post (ObjectProperty.ι _)).obj E.1).hom) →
      AlgebraicGeometry.BigSmoothOver.IsCovering B S hS E →
      ∀ i : E.2.I₀, Subsingleton (G.val.obj (Opposite.op (E.2.X i))))
    (U : AlgebraicGeometry.BigSmoothOver B S hS)
    (hU : Smooth ((Over.post (ObjectProperty.ι _)).obj U).hom) :
    Subsingleton (G.val.obj (Opposite.op U)) := by
  let I := ObjectProperty.ι (fun X : Scheme.{u} ↦ X.size < B.cutoff)
  let S₀ : B.category := ⟨S, hS⟩
  let E₁ : PreZeroHypercover.{u + 1} S₀ := PreZeroHypercover.singleton (𝟙 S₀)
  let E : PreZeroHypercover.{u + 1} S₀ := E₁.add U.hom
  have hE : AlgebraicGeometry.SmoothCovering B.cutoff ⟨S₀, E⟩ := by
    change (E.map I).presieve₀ ∈ Scheme.precoverage
      (@Smooth : MorphismProperty Scheme.{u}) S
    let : MorphismProperty.ContainsIdentities
        (@Smooth : MorphismProperty Scheme.{u}) := ⟨fun X ↦ by infer_instance⟩
    exact identity_add_mem_precoverage I (@Smooth) U hU
  exact subsingleton_of_covering_representative _ G.val.presheaf U _ hG
    (B.has_coveringRepresentative ⟨S₀, E⟩ hE)

private lemma syntomic_section_subsingleton
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒪 : Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B S hS) RingCat.{u}}
    (G : SheafOfModules.{u} 𝒪)
    (hG : ∀ E : Covering (AlgebraicGeometry.BigSyntomicOver B S hS),
      IsIso (((Over.post B.inclusion).obj E.1).hom) →
      AlgebraicGeometry.BigSyntomicOver.IsCovering B S hS E →
      ∀ i : E.2.I₀, Subsingleton (G.val.obj (Opposite.op (E.2.X i))))
    (U : AlgebraicGeometry.BigSyntomicOver B S hS)
    (hU : Syntomic ((Over.post B.inclusion).obj U).hom) :
    Subsingleton (G.val.obj (Opposite.op U)) := by
  let S₀ : B.category := ⟨S, hS⟩
  let E₁ : PreZeroHypercover.{u + 1} S₀ := PreZeroHypercover.singleton (𝟙 S₀)
  let E : PreZeroHypercover.{u + 1} S₀ := E₁.add U.hom
  have hE : AlgebraicGeometry.SyntomicCovering B.cutoff ⟨S₀, E⟩ := by
    let P : MorphismProperty Scheme.{u} := @Syntomic
    let : P.ContainsIdentities := ⟨syntomic_identity⟩
    have hmem := identity_add_mem_precoverage B.inclusion P U hU
    have hparts := (Scheme.ofArrows_mem_precoverage_iff P).mp hmem
    change AlgebraicGeometry.IsSyntomicCovering
      (fun i ↦ (E.map B.inclusion).X i) (fun i ↦ (E.map B.inclusion).f i)
    refine ⟨hparts.2, ?_⟩
    refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
    obtain ⟨i, hi⟩ := hparts.1 x
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr hi⟩
  exact subsingleton_of_covering_representative _ G.val.presheaf U _ hG
    (B.has_coveringRepresentative ⟨S₀, E⟩ hE)

private lemma fppf_section_subsingleton
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒪 : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) RingCat.{u}}
    (G : SheafOfModules.{u} 𝒪)
    (hG : ∀ E : Covering (AlgebraicGeometry.BigFppfOver B S hS),
      IsIso (((Over.post B.inclusion).obj E.1).hom) →
      AlgebraicGeometry.BigFppfOver.IsCovering B S hS E →
      ∀ i : E.2.I₀, Subsingleton (G.val.obj (Opposite.op (E.2.X i))))
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom ∧
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj U).hom) :
    Subsingleton (G.val.obj (Opposite.op U)) := by
  let S₀ : B.Schemes := ⟨S, hS⟩
  let E₁ : PreZeroHypercover.{u + 1} S₀ := PreZeroHypercover.singleton (𝟙 S₀)
  let E : PreZeroHypercover.{u + 1} S₀ := E₁.add U.hom
  have hE : AlgebraicGeometry.IsFppfCovering ⟨S₀, E⟩ := by
    unfold AlgebraicGeometry.IsFppfCovering
    rw [Precoverage.mem_comap_iff]
    change E.presieve₀.map B.inclusion ∈ Scheme.fppfPrecoverage S
    rw [← PreZeroHypercover.presieve₀_map, Scheme.fppfPrecoverage_eq_inf]
    let : MorphismProperty.ContainsIdentities
        (@Flat : MorphismProperty Scheme.{u}) := ⟨fun X ↦ by infer_instance⟩
    let : MorphismProperty.ContainsIdentities
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
      ⟨fun X ↦ by infer_instance⟩
    exact ⟨identity_add_mem_precoverage B.inclusion (@Flat) U hU.1,
      identity_add_mem_precoverage B.inclusion (@LocallyOfFinitePresentation) U hU.2⟩
  exact subsingleton_of_covering_representative _ G.val.presheaf U _ hG
    (B.fppf_has_representative ⟨S₀, E⟩ hE)

private theorem sheaf_cohomology_vanishes_on_stable_family
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C]
    [HasPullbacks C]
    (J : GrothendieckTopology C) (K : Pretopology C)
    (hK : K.toGrothendieck = J)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    (F : Sheaf J AddCommGrpCat.{u})
    (D : Set C)
    (hF : ∀ V : C, V ∈ D → Subsingleton (F.obj.obj (Opposite.op V)))
    (hD : ∀ (V : C), V ∈ D →
      ∀ (E : PreZeroHypercover.{u + 1} V), E.presieve₀ ∈ K V →
        (∀ i, E.X i ∈ D) ∧
          ∀ (n : ℕ) (s : Fin (n + 1) → E.I₀),
            Stacks.CechSite.iteratedFiberProduct E s ∈ D)
    (U : C) (hU : U ∈ D) (p : ℕ) : IsZero (F.H' p U) := by
  subst J
  refine Stacks.CechSite.cohomology_isZero_of_isZero_on_covering_fiberProducts K D F
    (fun V hV ↦ ?_) hD U hU p
  let := hF V hV
  exact AddCommGrpCat.isZero_of_subsingleton _

@[instance_reducible]
private noncomputable instance cutoff_createsPullbacks (κ : Cardinal.{u}) :
    CreatesLimitsOfShape WalkingCospan
      (ObjectProperty.ι (fun X : Scheme.{u} ↦ X.size < κ)) where
  CreatesLimit := fun {F} ↦ by
    let I := ObjectProperty.ι (fun X : Scheme.{u} ↦ X.size < κ)
    let D := F ⋙ I
    let t := pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    exact createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm (limit.isLimit _))
      (Scheme.size_pullback_lt _ _ (F.obj .left).property (F.obj .right).property)

private instance cutoff_hasPullbacks (κ : Cardinal.{u}) :
    HasPullbacks (ObjectProperty.FullSubcategory (fun X : Scheme.{u} ↦ X.size < κ)) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (ObjectProperty.ι _)

private instance cutoff_preservesPullbacks (κ : Cardinal.{u}) :
    PreservesLimitsOfShape WalkingCospan
      (ObjectProperty.ι (fun X : Scheme.{u} ↦ X.size < κ)) :=
  inferInstance

private theorem cohomology_isZero_over_of_sections_subsingleton
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C]
    [HasPullbacks C]
    (I : C ⥤ Scheme.{u}) [I.Faithful]
    [PreservesLimitsOfShape WalkingCospan I]
    (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities] [P.RespectsIso]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    (S : C) (J : GrothendieckTopology (Over S))
    (hJ : ((Scheme.precoverage P).comap (Over.forget S ⋙ I)).toGrothendieck = J)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    (F : Sheaf J AddCommGrpCat.{u})
    (hF : ∀ V : Over S, P (I.map V.hom) →
      Subsingleton (F.obj.obj (Opposite.op V)))
    (U : Over S) (hU : P (I.map U.hom)) (p : ℕ) : IsZero (F.H' p U) := by
  let := schemePrecoverage_stableUnderBaseChange P
  let K := ((Scheme.precoverage P).comap (Over.forget S ⋙ I)).toPretopology
  have hK : K.toGrothendieck = J :=
    Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.trans hJ
  let Q := P.inverseImage I
  let R := Q.inverseImage (Over.forget S)
  let D : Set (Over S) := {V | Q V.hom}
  let : Q.IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange I P
  let : R.IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange (Over.forget S) Q
  let : EssentiallySmall.{u} (Over S) :=
    CategoryTheory.essentiallySmall_over S
  apply sheaf_cohomology_vanishes_on_stable_family J K hK F D hF _ U hU p
  intro V hV E hE
  have hlegs : ∀ i, R (E.f i) := by
    have hmem : (E.map (Over.forget S ⋙ I)).presieve₀ ∈
        Scheme.precoverage P ((Over.forget S ⋙ I).obj V) := by
      rw [PreZeroHypercover.presieve₀_map]
      exact (Precoverage.mem_comap_iff).mp hE
    exact ((Scheme.ofArrows_mem_precoverage_iff P).mp hmem).2
  constructor
  · intro i
    change Q (E.X i).hom
    rw [← Over.w (E.f i)]
    exact Q.comp_mem _ _ (hlegs i) hV
  · intro n s
    let X : Fin (n + 1) → Over S := fun a ↦ E.X (s a)
    let f : ∀ a, X a ⟶ V := fun a ↦ E.f (s a)
    have hp : R ((overFiniteProductObj X f).hom) :=
      finiteOverProduct_hom_property R (n + 1) X f (fun a ↦ hlegs (s a))
    change Q (Stacks.CechSite.iteratedFiberProduct E s).hom
    have heq : (overFiniteProductObj X f).hom.left ≫ V.hom =
        (Stacks.CechSite.iteratedFiberProduct E s).hom := by
      rw [Over.w ((overFiniteProductObj X f).hom)]
      rfl
    rw [← heq]
    exact Q.comp_mem _ _ hp hV

private theorem over_precoverage_toGrothendieck
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    (I : C ⥤ Scheme.{u}) [I.Faithful]
    [PreservesLimitsOfShape WalkingCospan I]
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (K : Precoverage C) (hK : K = (Scheme.precoverage P).comap I) (S : C) :
    ((Scheme.precoverage P).comap (Over.forget S ⋙ I)).toGrothendieck =
      K.toGrothendieck.over S := by
  let := schemePrecoverage_stableUnderBaseChange P
  subst K
  rw [over_toGrothendieck_eq_toGrothendieck_comap_forget, Precoverage.comap_comp]

/-- Vanishing on objects open over the base in the big Zariski site. -/
@[stacks 0755 "topology_parasitic_vanishing"]
public theorem cohomology_isZero_of_isParasiticFor_zariski
    (B : AlgebraicGeometry.BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigZariskiOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigZariskiOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigZariskiOver.topology B S hS) RingCat.{u}}
    (G : SheafOfModules.{u} 𝒪)
    (hG : ∀ E : Covering (AlgebraicGeometry.BigZariskiOver B S hS),
      IsIso (((Over.post B.inclusion).obj E.1).hom) →
      AlgebraicGeometry.BigZariskiOver.IsCovering B S hS E →
      ∀ i : E.2.I₀, Subsingleton (G.val.obj (Opposite.op (E.2.X i))))
    (U : AlgebraicGeometry.BigZariskiOver B S hS)
    (hU : IsOpenImmersion ((Over.post B.inclusion).obj U).hom)
    (p : ℕ) :
    IsZero (((SheafOfModules.toSheaf _).obj G).H' p U) := by
  let S₀ : B.Schemes := ⟨S, hS⟩
  let P : MorphismProperty Scheme.{u} := @IsOpenImmersion
  let : P.IsStableUnderComposition :=
    (inferInstance : P.IsMultiplicative).toIsStableUnderComposition
  have hpre : AlgebraicGeometry.BigZariskiOver.precoverage B S hS =
      (Scheme.precoverage P).comap (Over.forget S₀ ⋙ B.inclusion) := by
    rw [AlgebraicGeometry.BigZariskiOver.precoverage_eq_comap B S₀,
      AlgebraicGeometry.BigZariskiSite.precoverage_eq_comap B,
      Precoverage.comap_comp]
    rfl
  let : EssentiallySmall.{u} B.Schemes := by
    change EssentiallySmall.{u} (AlgebraicGeometry.SchemeBelow B.schemeCardinal)
    exact AlgebraicGeometry.essentiallySmall_schemeBelow B.schemeCardinal
  exact cohomology_isZero_over_of_sections_subsingleton B.inclusion P S₀
    (AlgebraicGeometry.BigZariskiOver.topology B S hS)
    (congrArg Precoverage.toGrothendieck hpre.symm)
    ((SheafOfModules.toSheaf _).obj G)
    (zariski_section_subsingleton B S hS G hG) U hU p

/-- Vanishing on objects étale over the base in the big étale site. -/
@[stacks 0755 "topology_parasitic_vanishing"]
public theorem cohomology_isZero_of_isParasiticFor_etale
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigEtaleOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigEtaleOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigEtaleOver.topology B S hS) RingCat.{u}}
    (G : SheafOfModules.{u} 𝒪)
    (hG : ∀ E : Covering (AlgebraicGeometry.BigEtaleOver B S hS),
      IsIso (((Over.post B.inclusion).obj E.1).hom) →
      AlgebraicGeometry.BigEtaleOver.IsCovering B S hS E →
      ∀ i : E.2.I₀, Subsingleton (G.val.obj (Opposite.op (E.2.X i))))
    (U : AlgebraicGeometry.BigEtaleOver B S hS)
    (hU : Etale ((Over.post B.inclusion).obj U).hom)
    (p : ℕ) :
    IsZero (((SheafOfModules.toSheaf _).obj G).H' p U) := by
  let S₀ : B.Scheme := ⟨S, hS⟩
  let P : MorphismProperty Scheme.{u} := @Etale
  let : P.IsStableUnderComposition :=
    (inferInstance : P.IsMultiplicative).toIsStableUnderComposition
  have hpre : AlgebraicGeometry.BigEtaleOver.precoverage B S hS =
      (Scheme.precoverage P).comap (Over.forget S₀ ⋙ B.inclusion) := by
    rw [AlgebraicGeometry.bigEtaleOver_precoverage_eq_comap B S hS,
      AlgebraicGeometry.bigEtalePrecoverage_eq_comap B,
      Precoverage.comap_comp]
    rfl
  let : EssentiallySmall.{u} B.Scheme :=
    AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  exact cohomology_isZero_over_of_sections_subsingleton B.inclusion P S₀
    (AlgebraicGeometry.BigEtaleOver.topology B S hS)
    (congrArg Precoverage.toGrothendieck hpre.symm)
    ((SheafOfModules.toSheaf _).obj G)
    (etale_section_subsingleton B S hS G hG) U hU p

/-- Vanishing on objects smooth over the base in the big smooth site. -/
@[stacks 0755 "topology_parasitic_vanishing"]
public theorem cohomology_isZero_of_isParasiticFor_smooth
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    [HasSheafify (AlgebraicGeometry.BigSmoothOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigSmoothOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigSmoothOver.topology B S hS) RingCat.{u}}
    (G : SheafOfModules.{u} 𝒪)
    (hG : ∀ E : Covering (AlgebraicGeometry.BigSmoothOver B S hS),
      IsIso (((Over.post (ObjectProperty.ι _)).obj E.1).hom) →
      AlgebraicGeometry.BigSmoothOver.IsCovering B S hS E →
      ∀ i : E.2.I₀, Subsingleton (G.val.obj (Opposite.op (E.2.X i))))
    (U : AlgebraicGeometry.BigSmoothOver B S hS)
    (hU : Smooth ((Over.post (ObjectProperty.ι _)).obj U).hom)
    (p : ℕ) :
    IsZero (((SheafOfModules.toSheaf _).obj G).H' p U) := by
  let I := ObjectProperty.ι (fun X : Scheme.{u} ↦ X.size < B.cutoff)
  let S₀ : B.category := ⟨S, hS⟩
  let P : MorphismProperty Scheme.{u} := @Smooth
  let : P.ContainsIdentities := ⟨fun X ↦ by infer_instance⟩
  let : P.IsStableUnderComposition := ⟨fun f g hf hg ↦ by
    let : Smooth f := hf
    let : Smooth g := hg
    exact smooth_comp f g⟩
  let : EssentiallySmall.{u} B.category := by
    change EssentiallySmall.{u} (AlgebraicGeometry.SchemeBelow B.cutoff)
    exact AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  exact cohomology_isZero_over_of_sections_subsingleton I P S₀
    (AlgebraicGeometry.BigSmoothOver.topology B S hS)
    (over_precoverage_toGrothendieck I P B.precoverage
      (bigSmoothPrecoverage_eq_comap B) S₀)
    ((SheafOfModules.toSheaf _).obj G)
    (smooth_section_subsingleton B S hS G hG) U hU p

/-- Vanishing on objects syntomic over the base in the big syntomic site. -/
@[stacks 0755 "topology_parasitic_vanishing"]
public theorem cohomology_isZero_of_isParasiticFor_syntomic
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigSyntomicOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigSyntomicOver.topology B S hS) RingCat.{u}}
    (G : SheafOfModules.{u} 𝒪)
    (hG : ∀ E : Covering (AlgebraicGeometry.BigSyntomicOver B S hS),
      IsIso (((Over.post B.inclusion).obj E.1).hom) →
      AlgebraicGeometry.BigSyntomicOver.IsCovering B S hS E →
      ∀ i : E.2.I₀, Subsingleton (G.val.obj (Opposite.op (E.2.X i))))
    (U : AlgebraicGeometry.BigSyntomicOver B S hS)
    (hU : Syntomic ((Over.post B.inclusion).obj U).hom)
    (p : ℕ) :
    IsZero (((SheafOfModules.toSheaf _).obj G).H' p U) := by
  let P : MorphismProperty Scheme.{u} := @Syntomic
  let S₀ : B.category := ⟨S, hS⟩
  let : P.ContainsIdentities := ⟨syntomic_identity⟩
  let : EssentiallySmall.{u} B.category := by
    change EssentiallySmall.{u} (AlgebraicGeometry.SchemeBelow B.cutoff)
    exact AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  exact cohomology_isZero_over_of_sections_subsingleton B.inclusion P S₀
    (AlgebraicGeometry.BigSyntomicOver.topology B S hS)
    (over_precoverage_toGrothendieck B.inclusion P B.precoverage
      (bigSyntomicPrecoverage_eq_comap B) S₀)
    ((SheafOfModules.toSheaf _).obj G)
    (syntomic_section_subsingleton B S hS G hG) U hU p

/-- Vanishing on objects flat and locally of finite presentation over the
base in the big fppf site. -/
@[stacks 0755 "topology_parasitic_vanishing"]
public theorem cohomology_isZero_of_isParasiticFor_fppf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})]
    {𝒪 : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) RingCat.{u}}
    (G : SheafOfModules.{u} 𝒪)
    (hG : ∀ E : Covering (AlgebraicGeometry.BigFppfOver B S hS),
      IsIso (((Over.post B.inclusion).obj E.1).hom) →
      AlgebraicGeometry.BigFppfOver.IsCovering B S hS E →
      ∀ i : E.2.I₀, Subsingleton (G.val.obj (Opposite.op (E.2.X i))))
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom ∧
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj U).hom)
    (p : ℕ) :
    IsZero (((SheafOfModules.toSheaf _).obj G).H' p U) := by
  let P : MorphismProperty Scheme.{u} := @Flat ⊓ @LocallyOfFinitePresentation
  let S₀ : B.Schemes := ⟨S, hS⟩
  let : P.ContainsIdentities := ⟨fun X ↦ ⟨inferInstance, inferInstance⟩⟩
  let : P.IsStableUnderComposition := ⟨fun f g hf hg ↦ by
    let : Flat f := hf.1
    let : Flat g := hg.1
    let : LocallyOfFinitePresentation f := hf.2
    let : LocallyOfFinitePresentation g := hg.2
    exact ⟨inferInstance, inferInstance⟩⟩
  let : P.IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have hpre : B.precoverage = (Scheme.precoverage P).comap B.inclusion := by
    rw [bigFppf_precoverage_eq]
    rfl
  let : EssentiallySmall.{u} B.Schemes :=
    AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  exact cohomology_isZero_over_of_sections_subsingleton B.inclusion P S₀
    (AlgebraicGeometry.BigFppfOver.topology B S hS)
    (over_precoverage_toGrothendieck B.inclusion P B.precoverage hpre S₀)
    ((SheafOfModules.toSheaf _).obj G)
    (fppf_section_subsingleton B S hS G hG) U hU p

end AlgebraicGeometry

end
