module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.EtaleOfOpenIdentity
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.SubgroupoidDivision
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineQuotient
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CohenMacaulayQuotientUnchanged
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivalenceRelationGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingAffineLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PreEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Presheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Sheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictedQuotientOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.ChartRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafSpaceCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.RestrictionComparison
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The bootstrap theorem (Stacks 04S6, conditions (1) and (2))

This file proves that the fppf quotient sheaf of a flat, locally finitely presented equivalence
relation is an algebraic space: condition (2) of [Stacks, Tag 04S6] for a relation of schemes
and condition (1) for a relation of algebraic spaces.

The argument is the source's.

* *The case of an open identity.* If the identity of a groupoid scheme is an open immersion and
  its source is flat and locally of finite presentation, then source and target are étale
  (`Stacks.Groupoids.GroupoidScheme.etale_source_of_isOpenImmersion_identity`), and the quotient
  is an algebraic space by Stacks 02WW.
* *The quasi-split affine case.* If the object scheme `U` is affine, `s, t` are flat, locally of
  finite presentation and locally quasi-finite, and `R` is quasi-split over a point, then
  dividing out the quasi-splitting (Stacks 04S4) produces a groupoid on an affine `Ū` with an
  open identity, of which the given groupoid is the restriction; the two quotient sheaves agree
  (Stacks 045Z, along the fppf covering `U ⟶ Ū`).
* *The affine case.* Over an étale neighbourhood of each point the relation becomes quasi-split
  (Stacks 04S0); the quotients over these neighbourhoods are open subspaces of `U/R`
  (Stacks 02WU), finitely many of them cover it, and the glued sheaf is an algebraic space
  (Stacks 02WQ, Stacks 02WR).
* *The locally quasi-finite case.* Cover `U` by its affine opens and glue in the same way.
* *Condition (2).* Stacks 0489 replaces the relation by a locally quasi-finite one with the same
  quotient sheaf.
* *Condition (1).* Restricting along an étale atlas of `U` (Stacks 046P) makes the arrow space
  `U₀ ×_U R ×_U U₀` a separated, locally quasi-finite algebraic space over the scheme
  `U₀ ×_S U₀`, hence a scheme by Stacks 03XX, and condition (2) applies.

The sizes of all the schemes produced are tracked, so that every scheme the argument glues
lies in the chosen big fppf site.

## Main results

* `AlgebraicGeometry.Bootstrap04S6.isAlgebraicSpace_quotientSheaf_of_flat_preRelation` and
  `AlgebraicGeometry.Bootstrap04S6.isAlgebraicSpace_quotientSheaf_groupoidScheme`:
  **Stacks 04S6, condition (2)**.
* `AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`: **Stacks 04S6, condition (1)**, in the
  shape `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf` in which the library states it.

## References

* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
* [Stacks Project, Tag 045Z](https://stacks.math.columbia.edu/tag/045Z)
* [Stacks Project, Tag 046P](https://stacks.math.columbia.edu/tag/046P)
* [Stacks Project, Tag 04S0](https://stacks.math.columbia.edu/tag/04S0)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Bootstrap04S6

private noncomputable def pointsYonedaIso
    {C : Type v} [Category.{u} C] {S : Scheme.{u}} (F : C ⥤ Over S)
    [F.Full] [F.Faithful] (U : C) : Stacks.Groupoids.points F (F.obj U) ≅ yoneda.obj U := by
  let hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  refine NatIso.ofComponents (fun X => Equiv.toIso (hF.homEquiv.symm)) ?_
  intro X Y f
  ext g
  simp [Stacks.Groupoids.points, hF, Functor.FullyFaithful.homEquiv,
    Functor.FullyFaithful.ofFullyFaithful]

private theorem cofan_desc_eq_sigma_desc
    {D : Type v} [Category.{w} D] {I : Type u} (X : I → D)
    [HasCoproduct X] {A : D} (f : ∀ i, X i ⟶ A) :
    Cofan.IsColimit.desc (coproductIsCoproduct X) f = Sigma.desc f := by
  apply Sigma.hom_ext
  intro i
  calc
    Sigma.ι X i ≫ Cofan.IsColimit.desc (coproductIsCoproduct X) f = f i :=
      Cofan.IsColimit.fac (coproductIsCoproduct X) f i
    _ = Sigma.ι X i ≫ Sigma.desc f := by rw [Sigma.ι_desc]

private theorem schemeBelowClosedIso (site : AlgebraicGeometry.BigFppfSite.{u}) :
    (AlgebraicGeometry.schemeSizeBelow site.cutoff).IsClosedUnderIsomorphisms :=
  ⟨by
    intro X Y e h
    show Y.size < site.cutoff
    rwa [← Scheme.size_congr e]⟩

attribute [local instance] schemeBelowClosedIso

private theorem schemeBelowClosedCospan (site : AlgebraicGeometry.BigFppfSite.{u}) :
    (AlgebraicGeometry.schemeSizeBelow site.cutoff).IsClosedUnderLimitsOfShape WalkingCospan :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    show (limit F).size < site.cutoff
    rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
    exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))

attribute [local instance] schemeBelowClosedCospan

private theorem schemeBelowPreservesCospan (site : AlgebraicGeometry.BigFppfSite.{u}) :
    PreservesLimitsOfShape WalkingCospan site.inclusion := inferInstance

attribute [local instance] schemeBelowPreservesCospan

private theorem bigFppfOverHasPullbacks (site : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : site.Contains S) :
    HasPullbacks (AlgebraicGeometry.BigFppfOver site S hS) := inferInstance

attribute [local instance] bigFppfOverHasPullbacks

private theorem bigFppfOverHasBinaryProducts (site : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : site.Contains S) :
    HasBinaryProducts (AlgebraicGeometry.BigFppfOver site S hS) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

attribute [local instance] bigFppfOverHasBinaryProducts

private theorem bigFppfOverToSchemePreservesPullbacks
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S) :
    PreservesLimitsOfShape WalkingCospan (AlgebraicGeometry.BigFppfOver.toScheme site S hS) := by
  apply comp_preservesLimitsOfShape

attribute [local instance] bigFppfOverToSchemePreservesPullbacks

private theorem chartProperty_precomp_iso
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (P : MorphismProperty Scheme.{u})
    {X X' Y : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (e : X' ≅ X) (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P f) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P (e.hom ≫ f) := by
  intro U V a b k ha hb hw
  apply hf U V (a ≫ e.hom) b k
    (MorphismProperty.RespectsIso.postcomp _ e.hom a ha) hb
  simpa only [Category.assoc] using hw

private theorem mk_scheme_le_two_power_size (Y : Scheme.{u}) :
    #Y ≤ 2 ^ Y.size := by
  let f : Y → Set Y.affineOpens := fun y => {V | y ∈ V.1}
  have hf : Function.Injective f := by
    intro x y h
    apply Y.isBasis_affineOpens.eq_iff.mpr
    rintro _ ⟨V, hV, rfl⟩
    exact Set.ext_iff.mp h (⟨V, hV⟩ : Y.affineOpens)
  calc
    #Y ≤ #(Set Y.affineOpens) := mk_le_of_injective hf
    _ = 2 ^ #Y.affineOpens := mk_set
    _ ≤ 2 ^ Y.size := power_le_power_left two_ne_zero Y.mk_affineOpens_le_size

private theorem size_le_two_power_of_injective_locallyOfFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : Function.Injective f) : X.size ≤ 2 ^ Y.size := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · let : CompactSpace X := inferInstance
    exact (Scheme.size_le_of_locallyOfFiniteType f).trans (Cardinal.cantor _).le
  · have hV : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 := by
      intro x
      obtain ⟨V, hV, hx, _⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact ⟨⟨V, hV⟩, hx⟩
    choose V hV using hV
    have hcov : (⨆ x, (V x).1) = ⊤ := top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hV x⟩
    apply (Scheme.size_le_of_iSup_eq_top (fun x => (V x).1) hcov).trans
    refine max_le ((mk_le_of_injective hf).trans (mk_scheme_le_two_power_size Y)) ?_
    apply ciSup_le'
    intro x
    let : IsAffine ((V x).1 : Scheme) := (V x).2
    exact (Scheme.size_le_of_locallyOfFiniteType ((V x).1.ι ≫ f)).trans
      (Cardinal.cantor _).le

private theorem size_lt_of_injective_locallyOfFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : Function.Injective f) {κ : Cardinal.{u}} (hκ : IsStrongPrelimit κ)
    (hY : Y.size < κ) : X.size < κ :=
  (size_le_two_power_of_injective_locallyOfFiniteType f hf).trans_lt (hκ hY)

private theorem size_le_of_flat_surjective_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    [Flat f] [Surjective f] : Y.size ≤ X.size := by
  let : Epi f := Flat.epi_of_flat_of_surjective f
  have : Mono (Scheme.Γ.map f.op) := inferInstance
  rw [Scheme.size_of_isAffine X, Scheme.size_of_isAffine Y]
  exact max_le_max_left _ (Cardinal.mk_le_of_injective
    (ConcreteCategory.injective_of_mono_of_preservesPullback (Scheme.Γ.map f.op)))

private theorem groupoid_arrows_mem_site
    (site : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (hU : site.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation G).target
      (AlgebraicGeometry.groupoidPreRelation G).source)
    [LocallyOfFiniteType G.source.left] : site.Contains G.arrows.left := by
  let j := AlgebraicGeometry.groupoidPreRelation G
  let : Mono j := ((Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    j).mp hrel).1
  have hj : j.left ≫ (prod.snd : G.objects ⨯ G.objects ⟶ G.objects).left =
      G.source.left := by
    show (j ≫ prod.snd).left = G.source.left
    simp only [j, AlgebraicGeometry.groupoidPreRelation, prod.lift_snd]
  let : LocallyOfFiniteType (j.left ≫
      (prod.snd : G.objects ⨯ G.objects ⟶ G.objects).left) := hj.symm ▸ inferInstance
  let : LocallyOfFiniteType j.left := locallyOfFiniteType_of_comp j.left
    (prod.snd : G.objects ⨯ G.objects ⟶ G.objects).left
  apply size_lt_of_injective_locallyOfFiniteType j.left j.left.injective
    site.cutoff_isStrongPrelimit
  rw [Scheme.size_congr (Over.prodLeftIsoPullback G.objects G.objects)]
  exact Scheme.size_pullback_lt _ _ hU hU

private lemma jointlyMono_of_relation {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (hrel : IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation G).target
      (AlgebraicGeometry.groupoidPreRelation G).source) : JointlyMono₂ G.target G.source := by
  have : IsEquivalenceRelation G.target G.source := by
    simpa only [AlgebraicGeometry.groupoidPreRelation, Stacks.Groupoids.PreRelation.target,
      Stacks.Groupoids.PreRelation.source, prod.lift_fst, prod.lift_snd] using hrel
  exact IsEquivalenceRelation.nonempty_equivalenceRelation.some.toJointlyMono₂

private lemma sourceDiagonal_isOpenImmersion {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [JointlyMono₂ G.target G.source]
    [IsOpenImmersion G.identity.left] : IsOpenImmersion (pullback.diagonal G.source.left) := by
  let P := pullback G.source G.source
  let d : P ⟶ G.arrows := pullback.lift (pullback.fst G.source G.source)
    (pullback.snd G.source G.source ≫ G.inverse) (by
      rw [Category.assoc, G.target_inverse, pullback.condition]) ≫ G.comp
  have hdt : d ≫ G.target = pullback.fst G.source G.source ≫ G.target := by
    simp only [d, Category.assoc, G.target_comp, pullback.lift_fst_assoc]
  have hds : d ≫ G.source = pullback.snd G.source G.source ≫ G.target := by
    simp only [d, Category.assoc, G.source_comp, pullback.lift_snd_assoc,
      G.source_inverse]
  have hd : pullback.diagonal G.source ≫ d = G.target ≫ G.identity := by
    apply JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source)
    · simp only [Category.assoc, hdt, pullback.diagonal_fst_assoc,
        G.target_identity, Category.comp_id]
    · simp only [Category.assoc, hds, pullback.diagonal_snd_assoc,
        G.source_identity, Category.comp_id]
  have hp : IsPullback (pullback.diagonal G.source) G.target d G.identity := by
    apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hd)
    apply PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ pullback.fst G.source G.source)
    · intro c
      have ht : c.fst ≫ pullback.fst G.source G.source ≫ G.target = c.snd := by
        rw [← hdt, ← Category.assoc, c.condition, Category.assoc, G.target_identity,
          Category.comp_id]
      have hs : c.fst ≫ pullback.snd G.source G.source ≫ G.target = c.snd := by
        rw [← hds, ← Category.assoc, c.condition, Category.assoc, G.source_identity,
          Category.comp_id]
      have heq : c.fst ≫ pullback.fst G.source G.source =
          c.fst ≫ pullback.snd G.source G.source := by
        apply JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source)
        · simpa only [Category.assoc] using ht.trans hs.symm
        · simp only [Category.assoc, pullback.condition]
      apply pullback.hom_ext
      · simp
      · simpa using heq
    · intro c
      rw [Category.assoc, ← hdt, ← Category.assoc, c.condition,
        Category.assoc, G.target_identity, Category.comp_id]
    · intro c m hm _
      simpa using congrArg (fun f => f ≫ pullback.fst G.source G.source) hm
  have he : IsOpenImmersion (pullback.diagonal G.source).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsOpenImmersion) (hp.map (Over.forget S)).flip
      (inferInstance : IsOpenImmersion G.identity.left)
  let q := (IsPullback.of_hasPullback G.source G.source).map (Over.forget S)
  have hc : (pullback.diagonal G.source).left ≫ q.isoPullback.hom =
      pullback.diagonal G.source.left := by
    apply pullback.hom_ext <;> simp [← Over.comp_left]
  rw [← hc]
  infer_instance

private lemma etale_source_of_open_identity {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [JointlyMono₂ G.target G.source]
    [IsOpenImmersion G.identity.left] [Flat G.source.left]
    [LocallyOfFinitePresentation G.source.left] : Etale G.source.left := by
  have := sourceDiagonal_isOpenImmersion G
  exact Etale.of_formallyUnramified_of_flat _

private lemma inverse_isIso_of_jointlyMono {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [JointlyMono₂ G.target G.source] :
    IsIso G.inverse := by
  have h : G.inverse ≫ G.inverse = 𝟙 G.arrows := by
    apply JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source) <;>
      simp [Category.assoc, G.source_inverse, G.target_inverse]
  exact ⟨⟨G.inverse, h, h⟩⟩

private lemma etale_target_of_open_identity {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [JointlyMono₂ G.target G.source]
    [IsOpenImmersion G.identity.left] [Flat G.source.left]
    [LocallyOfFinitePresentation G.source.left] : Etale G.target.left := by
  have := inverse_isIso_of_jointlyMono G
  have := etale_source_of_open_identity G
  let : IsIso G.inverse.left := (Over.forget S).map_isIso G.inverse
  have h : G.target.left = G.inverse.left ≫ G.source.left :=
    congrArg Over.Hom.left G.source_inverse.symm
  rw [h]
  exact Etale.etale_comp _ _

private theorem isAlgebraicSpace_of_iso
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hG : AlgebraicGeometry.IsAlgebraicSpace site S hS G) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS F := by
  refine ⟨(Presheaf.isSheaf_of_iso_iff
    (J := AlgebraicGeometry.BigFppfOver.topology site S hS) e).mpr hG.isSheaf, ?_, ?_⟩
  · exact (MorphismProperty.cancel_right_of_respectsIso (P := yoneda.relativelyRepresentable)
      (diag F) (prod.map e.hom e.hom)).mp (by simpa only [prod.diag_map] using
      ((MorphismProperty.cancel_left_of_respectsIso (P := yoneda.relativelyRepresentable)
      e.hom (diag G)).mpr hG.diagonal_representable))
  · obtain ⟨U, f, hfs, hfe⟩ := hG.exists_atlas
    exact ⟨U, f ≫ e.inv,
      MorphismProperty.RespectsIso.postcomp _ e.inv f hfs,
      MorphismProperty.RespectsIso.postcomp _ e.inv f hfe⟩

private theorem isPullback_of_fullyFaithful_groupoid
    {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
    (i : G.Hom H) (hi : ∀ T, Nonempty (i.evaluation T).FullyFaithful) :
    IsPullback (prod.lift G.target G.source) i.mapArrows
      (prod.map i.mapObjects i.mapObjects) (prod.lift H.target H.source) := by
  classical
  refine IsPullback.mk' ?_ ?_ ?_
  · apply prod.hom_ext <;> simp [i.map_source, i.map_target]
  · intro T a b hp hiab
    have hs : a ≫ G.source = b ≫ G.source := by
      simpa using congrArg (fun f => f ≫ prod.snd) hp
    have ht : a ≫ G.target = b ≫ G.target := by
      simpa using congrArg (fun f => f ≫ prod.fst) hp
    let a' : G.EvaluationHom (a ≫ G.source) (a ≫ G.target) :=
      ⟨a, rfl, rfl⟩
    let b' : G.EvaluationHom (a ≫ G.source) (a ≫ G.target) :=
      ⟨b, hs.symm, ht.symm⟩
    exact congrArg Stacks.Groupoids.GroupoidScheme.EvaluationHom.arrow
      ((hi T).some.map_injective (f := a') (g := b')
        (Stacks.Groupoids.GroupoidScheme.EvaluationHom.ext hiab))
  · intro T p r hp
    let x : G.Evaluation T := p ≫ prod.snd
    let y : G.Evaluation T := p ≫ prod.fst
    let r' : (i.evaluation T).obj x ⟶ (i.evaluation T).obj y :=
      { arrow := r
        source_eq := by
          simpa [Stacks.Groupoids.GroupoidScheme.Hom.evaluation, x] using
            (congrArg (fun f => f ≫ prod.snd) hp).symm
        target_eq := by
          simpa [Stacks.Groupoids.GroupoidScheme.Hom.evaluation, y] using
            (congrArg (fun f => f ≫ prod.fst) hp).symm }
    let a := (hi T).some.preimage r'
    refine ⟨a.arrow, ?_, ?_⟩
    · apply prod.hom_ext
      · simpa [Stacks.Groupoids.GroupoidScheme.Hom.evaluation, y] using a.target_eq
      · simpa [Stacks.Groupoids.GroupoidScheme.Hom.evaluation, x] using a.source_eq
    · exact congrArg Stacks.Groupoids.GroupoidScheme.EvaluationHom.arrow
        ((hi T).some.map_preimage r')

/-- A morphism property is unchanged by precomposing with the canonical isomorphism attached
to an equality of objects of an over category. -/
private theorem property_eqToHom_comp {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {X X' Y : Over S} (h : X = X') (f : X' ⟶ Y) (hf : P f.left) :
    P (eqToHom h ≫ f).left := by
  subst h
  simpa only [eqToHom_refl, Category.id_comp] using hf

/-- Any morphism property is unchanged by composing with the canonical isomorphism attached to
an equality of objects of an over category: the equality may be substituted away, after which
the isomorphism is the identity. -/
private theorem property_comp_eqToHom {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {X Y Y' : Over S} (f : X ⟶ Y) (h : Y = Y') (hf : P f.left) :
    P (f ≫ eqToHom h).left := by
  subst h
  simpa only [eqToHom_refl, Category.comp_id] using hf

private theorem property_restrictionSource
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.RespectsIso]
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (hs : P G.source.left) (hg : P g.left) :
    P (AlgebraicGeometry.restrictionSource G g).left := by
  have h₁ : P (pullback.snd g G.target).left :=
    P.of_isPullback ((IsPullback.of_hasPullback g G.target).map (Over.forget S)) hg
  have h₂ : P (pullback.snd (pullback.snd g G.target)
      (pullback.fst G.source g)).left :=
    P.of_isPullback ((IsPullback.of_hasPullback _ _).map (Over.forget S)) h₁
  have h₃ : P (pullback.snd G.source g).left :=
    P.of_isPullback ((IsPullback.of_hasPullback G.source g).map (Over.forget S)) hs
  exact P.comp_mem _ _ h₂ h₃

private theorem property_restrictionTarget
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.RespectsIso]
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (ht : P G.target.left) (hg : P g.left) :
    P (AlgebraicGeometry.restrictionTarget G g).left := by
  have h₁ : P (pullback.fst G.source g).left :=
    P.of_isPullback ((IsPullback.of_hasPullback G.source g).map (Over.forget S)).flip hg
  have h₂ : P (pullback.fst (pullback.snd g G.target)
      (pullback.fst G.source g)).left :=
    P.of_isPullback ((IsPullback.of_hasPullback _ _).map (Over.forget S)).flip h₁
  have h₃ : P (pullback.fst g G.target).left :=
    P.of_isPullback ((IsPullback.of_hasPullback g G.target).map (Over.forget S)).flip ht
  exact P.comp_mem _ _ h₂ h₃

private theorem property_restrict_source
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.RespectsIso]
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (hs : P G.source.left) (hg : P g.left) :
    P (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.source.left := by
  rw [(AlgebraicGeometry.GroupoidScheme.restrict G g).source_eq]
  exact property_eqToHom_comp P _ _
    (property_comp_eqToHom P _ _ (property_restrictionSource P G g hs hg))

private theorem property_restrict_target
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.RespectsIso]
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (ht : P G.target.left) (hg : P g.left) :
    P (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.target.left := by
  rw [(AlgebraicGeometry.GroupoidScheme.restrict G g).target_eq]
  exact property_eqToHom_comp P _ _
    (property_comp_eqToHom P _ _ (property_restrictionTarget P G g ht hg))

/-- **Stacks 0489**, with the bound on the refined object scheme that the bootstrap argument
needs: the refinement `G''` of a flat, locally finitely presented equivalence relation `G` whose
object and arrow schemes lie in the site has its object scheme in the site again. -/
private theorem exists_locallyQuasiFinite_groupoid_quotientSheaf_iso_of_contains
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    (G : Stacks.Groupoids.GroupoidScheme S) [IsEquivalenceRelation G.target G.source]
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left] [LocallyOfFinitePresentation G.target.left]
    (hU : site.Contains G.objects.left) (hR : site.Contains G.arrows.left) :
    ∃ G'' : Stacks.Groupoids.GroupoidScheme S, site.Contains G''.objects.left ∧
      IsEquivalenceRelation G''.target G''.source ∧
      Flat G''.source.left ∧ LocallyOfFinitePresentation G''.source.left ∧
      LocallyQuasiFinite G''.source.left ∧
      Flat G''.target.left ∧ LocallyOfFinitePresentation G''.target.left ∧
      LocallyQuasiFinite G''.target.left ∧
      Nonempty (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
          (Over.post (X := site.obj hS) site.inclusion)
          (AlgebraicGeometry.groupoidPreRelation G'') ≅
        Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
          (Over.post (X := site.obj hS) site.inclusion)
          (AlgebraicGeometry.groupoidPreRelation G)) := by
  classical
  let J := AlgebraicGeometry.BigFppfOver.topology site S hS
  let F : AlgebraicGeometry.BigFppfOver site S hS ⥤ Over S :=
    Over.post (X := site.obj hS) site.inclusion
  set W := AlgebraicGeometry.cohenMacaulayOpen G with hW
  set gW : Over.mk (W.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk W.ι with hgW
  set G₁ := (AlgebraicGeometry.GroupoidScheme.restrict G gW).groupoid with hG₁
  have : IsEquivalenceRelation G₁.target G₁.source :=
    AlgebraicGeometry.isEquivalenceRelation_cohenMacaulayRestriction G
  have h₁ := AlgebraicGeometry.isIso_restrictionQuotientMap_cohenMacaulayOpen site S hS G hU hR
    (AlgebraicGeometry.GroupoidScheme.restrict G gW)
  obtain ⟨N⟩ := AlgebraicGeometry.exists_quasiFiniteRefinement_cohenMacaulayRestriction
    site S hS G hU
  let R'' := AlgebraicGeometry.GroupoidScheme.restrict G₁ N.projection
  have hiso := AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_reach_cover
    (AlgebraicGeometry.BigFppfOver.topology site S hS) (Over.post (X := site.obj hS) site.inclusion)
    inferInstance G₁ N.projection R'' N.siteSource N.siteTarget N.siteSourceIso N.siteTargetIso
    N.cover N.cover_spec N.cover_mem
  have hlfp := N.reach_locallyOfFinitePresentation
  -- the refined object scheme lies in the site
  have hgW : IsOpenImmersion gW.left := by
    show IsOpenImmersion W.ι; infer_instance
  have : MorphismProperty.RespectsIso (@Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Flat G₁.target.left :=
    property_restrict_target (@Flat.{u}) G gW inferInstance inferInstance
  have : Surjective G₁.target.left := by
    have h := Stacks.Groupoids.identity_left_comp_target_left G₁
    exact ⟨fun x => ⟨G₁.identity.left x, by
      rw [← Scheme.Hom.comp_apply, h]; rfl⟩⟩
  have hpb := (IsPullback.of_hasPullback N.projection G₁.target).map (Over.forget S)
  have : Flat (pullback.fst N.projection G₁.target).left :=
    MorphismProperty.of_isPullback (P := @Flat) hpb.flip (inferInstance : Flat G₁.target.left)
  have : Surjective (pullback.fst N.projection G₁.target).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb.flip
      (inferInstance : Surjective G₁.target.left)
  have hsrc : site.Contains (pullback N.projection G₁.target).left :=
    (Scheme.size_congr ((Over.forget S).mapIso N.siteSourceIso)).symm.trans_lt
      N.siteSource.left.property
  have hobj : site.Contains R''.groupoid.objects.left := by
    rw [R''.objects_eq]
    exact Scheme.size_lt_of_flat_of_surjective_of_isStrongPrelimit site.cutoff_isStrongPrelimit
      (pullback.fst N.projection G₁.target).left hsrc
  refine ⟨R''.groupoid, hobj,
    AlgebraicGeometry.restriction_isEquivalenceRelation G₁ N.projection R'',
    AlgebraicGeometry.restriction_source_mem G₁ N.projection R'' @Flat N.reach_flat,
    AlgebraicGeometry.restriction_source_mem G₁ N.projection R'' @LocallyOfFinitePresentation hlfp,
    AlgebraicGeometry.restriction_source_mem G₁ N.projection R'' @LocallyQuasiFinite
      N.reach_locallyQuasiFinite,
    AlgebraicGeometry.restriction_target_mem G₁ N.projection R'' @Flat N.reach_flat,
    AlgebraicGeometry.restriction_target_mem G₁ N.projection R'' @LocallyOfFinitePresentation hlfp,
    AlgebraicGeometry.restriction_target_mem G₁ N.projection R'' @LocallyQuasiFinite
      N.reach_locallyQuasiFinite, ⟨?_⟩⟩
  exact (@asIso _ _ _ _ _ hiso).trans (@asIso _ _ _ _ _ h₁)

private theorem isAlgebraicSpace_quotient_groupoidScheme_of_locallyQuasiFinite_case
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    (hquot : ∀ {R U : AlgebraicGeometry.BigFppfOver site S hS}
      (j : Stacks.Groupoids.PreRelation ((Over.post site.inclusion).obj R)
        ((Over.post site.inclusion).obj U))
      [IsEquivalenceRelation j.target j.source]
      [Flat j.source.left] [LocallyOfFinitePresentation j.source.left]
      [LocallyQuasiFinite j.source.left]
      [Flat j.target.left] [LocallyOfFinitePresentation j.target.left]
      [LocallyQuasiFinite j.target.left],
      AlgebraicGeometry.IsAlgebraicSpace site S hS
        (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
          (Over.post site.inclusion) j).obj)
    (G : Stacks.Groupoids.GroupoidScheme S) (hU : site.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation G).target
      (AlgebraicGeometry.groupoidPreRelation G).source)
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) (AlgebraicGeometry.groupoidPreRelation G)).obj := by
  have hR := groupoid_arrows_mem_site site G hU hrel
  have hs : (AlgebraicGeometry.groupoidPreRelation G).source = G.source := prod.lift_snd _ _
  have ht : (AlgebraicGeometry.groupoidPreRelation G).target = G.target := prod.lift_fst _ _
  have : IsEquivalenceRelation G.target G.source := by rwa [← hs, ← ht]
  obtain ⟨G'', hU'', hrel'', hsf, hsl, hsq, htf, htl, htq, ⟨e⟩⟩ :=
    exists_locallyQuasiFinite_groupoid_quotientSheaf_iso_of_contains site S hS G hU hR
  have hlft'' : LocallyOfFiniteType G''.source.left := inferInstance
  have hs'' : (AlgebraicGeometry.groupoidPreRelation G'').source = G''.source :=
    prod.lift_snd _ _
  have ht'' : (AlgebraicGeometry.groupoidPreRelation G'').target = G''.target :=
    prod.lift_fst _ _
  have hrelj : IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation G'').target
      (AlgebraicGeometry.groupoidPreRelation G'').source := by rwa [hs'', ht'']
  have hR'' := groupoid_arrows_mem_site site G'' hU'' hrelj
  let U : AlgebraicGeometry.BigFppfOver site S hS :=
    Over.mk (ObjectProperty.homMk G''.objects.hom : site.obj hU'' ⟶ site.obj hS)
  let R : AlgebraicGeometry.BigFppfOver site S hS :=
    Over.mk (ObjectProperty.homMk G''.arrows.hom : site.obj hR'' ⟶ site.obj hS)
  let j : Stacks.Groupoids.PreRelation ((Over.post site.inclusion).obj R)
      ((Over.post site.inclusion).obj U) := AlgebraicGeometry.groupoidPreRelation G''
  have hjs : j.source = G''.source := prod.lift_snd _ _
  have hjt : j.target = G''.target := prod.lift_fst _ _
  let : IsEquivalenceRelation j.target j.source := hrelj
  let : Flat j.source.left := by rwa [hjs]
  let : Flat j.target.left := by rwa [hjt]
  let : LocallyOfFinitePresentation j.source.left := by rwa [hjs]
  let : LocallyOfFinitePresentation j.target.left := by rwa [hjt]
  let : LocallyQuasiFinite j.source.left := by rwa [hjs]
  let : LocallyQuasiFinite j.target.left := by rwa [hjt]
  exact isAlgebraicSpace_of_iso site S hS ((sheafToPresheaf _ _).mapIso e).symm (hquot j)

private theorem isPullback_sourceFactor_of_fullyFaithful_groupoid
    {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
    (i : G.Hom H) (hi : ∀ T, Nonempty (i.evaluation T).FullyFaithful) :
    IsPullback G.target
      (pullback.lift (f := H.source) (g := i.mapObjects) i.mapArrows G.source
        i.map_source)
      i.mapObjects (pullback.fst H.source i.mapObjects ≫ H.target) := by
  have hp := isPullback_of_fullyFaithful_groupoid i hi
  refine IsPullback.mk' ?_ ?_ ?_
  · simp only [pullback.lift_fst_assoc, i.map_target]
  · intro T a b ht hab
    have hs : a ≫ G.source = b ≫ G.source := by
      have h := congrArg (fun f => f ≫ pullback.snd H.source i.mapObjects) hab
      simp only [Category.assoc] at h
      rwa [pullback.lift_snd] at h
    have hr : a ≫ i.mapArrows = b ≫ i.mapArrows := by
      have h := congrArg (fun f => f ≫ pullback.fst H.source i.mapObjects) hab
      simp only [Category.assoc] at h
      rwa [pullback.lift_fst] at h
    apply hp.hom_ext ?_ hr
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using ht
    · simpa only [Category.assoc, prod.lift_snd] using hs
  · intro T t v htv
    have hw : prod.lift t (v ≫ pullback.snd H.source i.mapObjects) ≫
        prod.map i.mapObjects i.mapObjects =
        (v ≫ pullback.fst H.source i.mapObjects) ≫ prod.lift H.target H.source := by
      apply prod.hom_ext
      · simpa using htv
      · simp only [Category.assoc, prod.map_snd, prod.lift_snd_assoc,
          prod.lift_snd, pullback.condition]
    let a := hp.lift (prod.lift t (v ≫ pullback.snd H.source i.mapObjects))
      (v ≫ pullback.fst H.source i.mapObjects) hw
    have hat : a ≫ G.target = t := by
      have h := congrArg (fun f => f ≫ prod.fst) (hp.lift_fst
        (prod.lift t (v ≫ pullback.snd H.source i.mapObjects))
        (v ≫ pullback.fst H.source i.mapObjects) hw)
      simpa [a] using h
    have has : a ≫ G.source = v ≫ pullback.snd H.source i.mapObjects := by
      have h := congrArg (fun f => f ≫ prod.snd) (hp.lift_fst
        (prod.lift t (v ≫ pullback.snd H.source i.mapObjects))
        (v ≫ pullback.fst H.source i.mapObjects) hw)
      simpa [a] using h
    refine ⟨a, hat, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact hp.lift_snd _ _ hw
    · rw [Category.assoc, pullback.lift_snd]
      exact has

private theorem property_source_of_fppf_fullyFaithful_groupoid
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.fppfPrecoverage]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
    (i : G.Hom H) (hi : ∀ T, Nonempty (i.evaluation T).FullyFaithful)
    [Surjective i.mapObjects.left] [Flat i.mapObjects.left]
    [LocallyOfFinitePresentation i.mapObjects.left]
    (hs : P G.source.left) : P H.source.left := by
  let a := pullback.lift (f := H.source) (g := i.mapObjects) i.mapArrows G.source i.map_source
  have ha := (isPullback_sourceFactor_of_fullyFaithful_groupoid i hi).map (Over.forget S)
  let : Surjective a.left := MorphismProperty.of_isPullback (P := @Surjective) ha
    (inferInstance : Surjective i.mapObjects.left)
  let : Flat a.left := MorphismProperty.of_isPullback (P := @Flat) ha
    (inferInstance : Flat i.mapObjects.left)
  let : LocallyOfFinitePresentation a.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) ha
      (inferInstance : LocallyOfFinitePresentation i.mapObjects.left)
  have hlocal : P (pullback.snd H.source i.mapObjects).left := by
    apply MorphismProperty.IsLocalAtSource.of_forall_comp
      (P := P) a.left.singleton_mem_fppfPrecoverage
    rintro _ _ ⟨⟩
    show P ((a ≫ pullback.snd H.source i.mapObjects).left)
    simpa only [a, pullback.lift_snd] using hs
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := P) i.mapObjects.left.singleton_mem_fppfPrecoverage
  rintro _ _ _ ⟨⟩
  have hpb : IsPullback (pullback.fst H.source i.mapObjects).left
      (pullback.snd H.source i.mapObjects).left H.source.left i.mapObjects.left :=
    (IsPullback.of_hasPullback H.source i.mapObjects).map (Over.forget S)
  rw [← hpb.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp P hpb.isoPullback.inv _ hlocal

private theorem property_arrows_of_fullyFaithful_groupoid
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition]
    {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
    (i : G.Hom H) (hi : ∀ T, Nonempty (i.evaluation T).FullyFaithful)
    (h : P i.mapObjects.left) : P i.mapArrows.left := by
  let a := pullback.lift (f := H.source) (g := i.mapObjects)
    i.mapArrows G.source i.map_source
  have ha : P a.left := P.of_isPullback
    ((isPullback_sourceFactor_of_fullyFaithful_groupoid i hi).map (Over.forget S)) h
  have hb : P (pullback.fst H.source i.mapObjects).left :=
    P.of_isPullback ((IsPullback.of_hasPullback H.source i.mapObjects).map
      (Over.forget S)).flip h
  have he : a.left ≫ (pullback.fst H.source i.mapObjects).left = i.mapArrows.left :=
    congrArg Over.Hom.left (pullback.lift_fst _ _ _)
  exact he ▸ P.comp_mem _ _ ha hb

private theorem isPullback_identity_of_fullyFaithful_groupoid
    {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
    [JointlyMono₂ G.target G.source]
    (i : G.Hom H) (hi : ∀ T, Nonempty (i.evaluation T).FullyFaithful)
    {R : Over S} (q : R ⟶ G.arrows) (t s : R ⟶ G.objects)
    (hqt : q ≫ G.target = t) (hqs : q ≫ G.source = s)
    (hp : IsPullback t s i.mapObjects i.mapObjects) :
    IsPullback q (s ≫ i.mapObjects) i.mapArrows H.identity := by
  classical
  have hw : q ≫ i.mapArrows = (s ≫ i.mapObjects) ≫ H.identity := by
    let r : H.EvaluationHom ((i.evaluation R).obj s) ((i.evaluation R).obj t) :=
      { arrow := (s ≫ i.mapObjects) ≫ H.identity
        source_eq := by
          show (s ≫ i.mapObjects) ≫ H.identity ≫ H.source = s ≫ i.mapObjects
          simp only [H.source_identity, Category.comp_id]
        target_eq := by
          show (s ≫ i.mapObjects) ≫ H.identity ≫ H.target = t ≫ i.mapObjects
          simpa only [H.target_identity, Category.comp_id] using hp.w.symm }
    let a := (hi R).some.preimage r
    have he : a.arrow = q := by
      apply JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source)
      exacts [a.target_eq.trans hqt.symm, a.source_eq.trans hqs.symm]
    rw [← he]
    exact congrArg Stacks.Groupoids.GroupoidScheme.EvaluationHom.arrow
      ((hi R).some.map_preimage r)
  refine IsPullback.mk' hw ?_ ?_
  · intro T a b h _
    apply hp.hom_ext
    · rw [← hqt, ← Category.assoc, ← Category.assoc, h]
    · rw [← hqs, ← Category.assoc, ← Category.assoc, h]
  · intro T r u hru
    have hs : (r ≫ G.source) ≫ i.mapObjects = u := by
      rw [Category.assoc, ← i.map_source, ← Category.assoc, hru,
        Category.assoc, H.source_identity, Category.comp_id]
    have ht : (r ≫ G.target) ≫ i.mapObjects = u := by
      rw [Category.assoc, ← i.map_target, ← Category.assoc, hru,
        Category.assoc, H.target_identity, Category.comp_id]
    let a := hp.lift (r ≫ G.target) (r ≫ G.source) (ht.trans hs.symm)
    refine ⟨a, ?_, ?_⟩
    · apply JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source)
      · rw [Category.assoc, hqt]
        exact hp.lift_fst _ _ _
      · rw [Category.assoc, hqs]
        exact hp.lift_snd _ _ _
    · rw [← Category.assoc, show a ≫ s = r ≫ G.source from hp.lift_snd _ _ _]
      exact hs

private theorem isOpenImmersion_identity_of_fppf_fullyFaithful_groupoid
    {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
    [JointlyMono₂ G.target G.source]
    (i : G.Hom H) (hi : ∀ T, Nonempty (i.evaluation T).FullyFaithful)
    [Surjective i.mapObjects.left] [Flat i.mapObjects.left] [QuasiCompact i.mapObjects.left]
    {R : Over S} (q : R ⟶ G.arrows) (t s : R ⟶ G.objects)
    (hqt : q ≫ G.target = t) (hqs : q ≫ G.source = s)
    (hp : IsPullback t s i.mapObjects i.mapObjects) [IsOpenImmersion q.left] :
    IsOpenImmersion H.identity.left := by
  let : MorphismProperty.IsStableUnderComposition
      (@Surjective : MorphismProperty Scheme.{u}) := ⟨fun _ _ _ _ => inferInstance⟩
  have hsurj : Surjective i.mapArrows.left :=
    property_arrows_of_fullyFaithful_groupoid (@Surjective) i hi inferInstance
  have hflat : Flat i.mapArrows.left :=
    property_arrows_of_fullyFaithful_groupoid (@Flat) i hi inferInstance
  have hqc : QuasiCompact i.mapArrows.left :=
    property_arrows_of_fullyFaithful_groupoid (@QuasiCompact) i hi inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((isPullback_identity_of_fullyFaithful_groupoid i hi q t s hqt hqs hp).map
      (Over.forget S)) ⟨⟨hsurj, hflat⟩, hqc⟩ (show IsOpenImmersion q.left from inferInstance)

private theorem isAlgebraicSpace_quotient_of_open_identity
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    (G : Stacks.Groupoids.GroupoidScheme S) (hU : site.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation G).target
      (AlgebraicGeometry.groupoidPreRelation G).source)
    [IsOpenImmersion G.identity.left] [Flat G.source.left]
    [LocallyOfFinitePresentation G.source.left] :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) (AlgebraicGeometry.groupoidPreRelation G)).obj := by
  let := jointlyMono_of_relation G hrel
  have hs := etale_source_of_open_identity G
  have ht := etale_target_of_open_identity G
  have hR := groupoid_arrows_mem_site site G hU hrel
  let U : AlgebraicGeometry.BigFppfOver site S hS :=
    Over.mk (ObjectProperty.homMk G.objects.hom : site.obj hU ⟶ site.obj hS)
  let R : AlgebraicGeometry.BigFppfOver site S hS :=
    Over.mk (ObjectProperty.homMk G.arrows.hom : site.obj hR ⟶ site.obj hS)
  let s : R ⟶ U := Over.homMk (ObjectProperty.homMk G.source.left)
    (by ext; exact G.source.w)
  let t : R ⟶ U := Over.homMk (ObjectProperty.homMk G.target.left)
    (by ext; exact G.target.w)
  let j := AlgebraicGeometry.Space.relation site S hS s t
  have hj : j = AlgebraicGeometry.groupoidPreRelation G := rfl
  have hjs : j.source = G.source := prod.lift_snd _ _
  have hjt : j.target = G.target := prod.lift_fst _ _
  let : Stacks.Groupoids.IsEtaleEquivalenceRelation j :=
    { isEquivalenceRelation := hj.symm ▸ hrel
      etale_source := hjs.symm ▸ hs
      etale_target := hjt.symm ▸ ht }
  exact AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional site S hS s t

/-- The atlas refinement of `isAlgebraicSpace_quotient_of_open_identity`: if the identity of
a groupoid scheme is an open immersion then its source and target are étale, so the object
scheme itself is a surjective étale atlas of the quotient sheaf and the atlas may be chosen
without increasing the size. -/
private theorem exists_atlas_quotient_of_open_identity
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    (G : Stacks.Groupoids.GroupoidScheme S) (hU : site.Contains G.objects.left)
    (hrel : IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation G).target
      (AlgebraicGeometry.groupoidPreRelation G).source)
    [IsOpenImmersion G.identity.left] [Flat G.source.left]
    [LocallyOfFinitePresentation G.source.left] :
    ∃ (W : AlgebraicGeometry.BigFppfOver site S hS)
      (a : yoneda.obj W ⟶
        (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
          (Over.post site.inclusion) (AlgebraicGeometry.groupoidPreRelation G)).obj),
      AlgebraicGeometry.IsAlgebraicSpace site S hS
          (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
            (Over.post site.inclusion) (AlgebraicGeometry.groupoidPreRelation G)).obj ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj W).size ≤
          G.objects.left.size := by
  let := jointlyMono_of_relation G hrel
  have hs := etale_source_of_open_identity G
  have ht := etale_target_of_open_identity G
  have hR := groupoid_arrows_mem_site site G hU hrel
  let U : AlgebraicGeometry.BigFppfOver site S hS :=
    Over.mk (ObjectProperty.homMk G.objects.hom : site.obj hU ⟶ site.obj hS)
  let R : AlgebraicGeometry.BigFppfOver site S hS :=
    Over.mk (ObjectProperty.homMk G.arrows.hom : site.obj hR ⟶ site.obj hS)
  let s : R ⟶ U := Over.homMk (ObjectProperty.homMk G.source.left)
    (by ext; exact G.source.w)
  let t : R ⟶ U := Over.homMk (ObjectProperty.homMk G.target.left)
    (by ext; exact G.target.w)
  let j := AlgebraicGeometry.Space.relation site S hS s t
  have hj : j = AlgebraicGeometry.groupoidPreRelation G := rfl
  have hjs : j.source = G.source := prod.lift_snd _ _
  have hjt : j.target = G.target := prod.lift_fst _ _
  let : Stacks.Groupoids.IsEtaleEquivalenceRelation j :=
    { isEquivalenceRelation := hj.symm ▸ hrel
      etale_source := hjs.symm ▸ hs
      etale_target := hjt.symm ▸ ht }
  exact ⟨U, AlgebraicGeometry.Space.quotientMap site S hS s t,
    AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional site S hS s t,
    AlgebraicGeometry.Space.quotientMap_surjective_unconditional site S hS s t,
    AlgebraicGeometry.Space.quotientMap_etale_unconditional site S hS s t, le_rfl⟩

private theorem jointlyMono_of_flat_surjective_fullyFaithful_groupoid
    {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
    [JointlyMono₂ G.target G.source]
    (i : G.Hom H) (hi : ∀ T, Nonempty (i.evaluation T).FullyFaithful)
    [Surjective i.mapObjects.left] [Flat i.mapObjects.left] :
    JointlyMono₂ H.target H.source := by
  classical
  constructor
  intro T r₁ r₂ ht hs
  let X := pullback i.mapObjects (r₁ ≫ H.source)
  let f : X ⟶ T := pullback.snd i.mapObjects (r₁ ≫ H.source)
  let Z := pullback i.mapObjects (f ≫ r₁ ≫ H.target)
  let g : Z ⟶ X := pullback.snd i.mapObjects (f ≫ r₁ ≫ H.target)
  let c : Z ⟶ T := g ≫ f
  let x : G.Evaluation Z := g ≫ pullback.fst i.mapObjects (r₁ ≫ H.source)
  let y : G.Evaluation Z := pullback.fst i.mapObjects (f ≫ r₁ ≫ H.target)
  have hx : x ≫ i.mapObjects = c ≫ r₁ ≫ H.source := by
    simp only [x, c, f, Category.assoc, pullback.condition]
  have hy : y ≫ i.mapObjects = c ≫ r₁ ≫ H.target := by
    simpa only [y, c, g, Category.assoc] using
      (pullback.condition (f := i.mapObjects) (g := f ≫ r₁ ≫ H.target))
  let a : H.EvaluationHom ((i.evaluation Z).obj x) ((i.evaluation Z).obj y) :=
    { arrow := c ≫ r₁
      source_eq := by
        show (c ≫ r₁) ≫ H.source = x ≫ i.mapObjects
        simpa only [Category.assoc] using hx.symm
      target_eq := by
        show (c ≫ r₁) ≫ H.target = y ≫ i.mapObjects
        simpa only [Category.assoc] using hy.symm }
  let b : H.EvaluationHom ((i.evaluation Z).obj x) ((i.evaluation Z).obj y) :=
    { arrow := c ≫ r₂
      source_eq := by
        show (c ≫ r₂) ≫ H.source = x ≫ i.mapObjects
        rw [Category.assoc, ← hs, hx]
      target_eq := by
        show (c ≫ r₂) ≫ H.target = y ≫ i.mapObjects
        rw [Category.assoc, ← ht, hy] }
  have he : (hi Z).some.preimage a = (hi Z).some.preimage b := by
    apply Stacks.Groupoids.GroupoidScheme.EvaluationHom.ext
    apply JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source)
    · exact ((hi Z).some.preimage a).target_eq.trans
        ((hi Z).some.preimage b).target_eq.symm
    · exact ((hi Z).some.preimage a).source_eq.trans
        ((hi Z).some.preimage b).source_eq.symm
  have he' : a = b := by
    rw [← (hi Z).some.map_preimage a, ← (hi Z).some.map_preimage b, he]
  have heq : c ≫ r₁ = c ≫ r₂ :=
    congrArg Stacks.Groupoids.GroupoidScheme.EvaluationHom.arrow he'
  have hfflat : Flat f.left := MorphismProperty.of_isPullback (P := @Flat)
    ((IsPullback.of_hasPullback i.mapObjects (r₁ ≫ H.source)).map (Over.forget S))
    (show Flat i.mapObjects.left from inferInstance)
  have hfsurj : Surjective f.left := MorphismProperty.of_isPullback (P := @Surjective)
    ((IsPullback.of_hasPullback i.mapObjects (r₁ ≫ H.source)).map (Over.forget S))
    (show Surjective i.mapObjects.left from inferInstance)
  have hgflat : Flat g.left := MorphismProperty.of_isPullback (P := @Flat)
    ((IsPullback.of_hasPullback i.mapObjects (f ≫ r₁ ≫ H.target)).map (Over.forget S))
    (show Flat i.mapObjects.left from inferInstance)
  have hgsurj : Surjective g.left := MorphismProperty.of_isPullback (P := @Surjective)
    ((IsPullback.of_hasPullback i.mapObjects (f ≫ r₁ ≫ H.target)).map (Over.forget S))
    (show Surjective i.mapObjects.left from inferInstance)
  have hcf : Flat c.left := @Flat.comp _ _ _ g.left f.left hgflat hfflat
  have hcs : Surjective c.left := ⟨hfsurj.surj.comp hgsurj.surj⟩
  have : Epi c.left := @Flat.epi_of_flat_of_surjective _ _ c.left hcf hcs
  exact Over.OverMorphism.ext ((cancel_epi c.left).mp (congrArg Over.Hom.left heq))

private theorem isEquivalenceRelation_of_jointlyMono_groupoid
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [JointlyMono₂ G.target G.source] :
    IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation G).target
      (AlgebraicGeometry.groupoidPreRelation G).source := by
  apply (Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation _).mpr
  refine ⟨?_, AlgebraicGeometry.groupoidPreRelation_isPreEquivalenceRelation G⟩
  constructor
  intro T a b h
  apply JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source)
  · simpa only [AlgebraicGeometry.groupoidPreRelation, Category.assoc, prod.lift_fst] using
      congrArg (fun f => f ≫ prod.fst) h
  · simpa only [AlgebraicGeometry.groupoidPreRelation, Category.assoc, prod.lift_snd] using
      congrArg (fun f => f ≫ prod.snd) h

/-- The atlas refinement of `isAlgebraicSpace_quotient_of_open_kernelPair`: the quotient sheaf
of the ambient groupoid has a surjective étale atlas whose object is the ambient object
scheme, so the atlas may be chosen without increasing the size. -/
private theorem exists_atlas_quotient_of_open_kernelPair
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {G H : Stacks.Groupoids.GroupoidScheme S}
    (hU : site.Contains H.objects.left)
    (hrel : IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation G).target
      (AlgebraicGeometry.groupoidPreRelation G).source)
    (i : G.Hom H) (hi : ∀ T, Nonempty (i.evaluation T).FullyFaithful)
    [Surjective i.mapObjects.left] [Flat i.mapObjects.left]
    [QuasiCompact i.mapObjects.left] [LocallyOfFinitePresentation i.mapObjects.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    {R : Over S} (q : R ⟶ G.arrows) (t s : R ⟶ G.objects)
    (hqt : q ≫ G.target = t) (hqs : q ≫ G.source = s)
    (hp : IsPullback t s i.mapObjects i.mapObjects) [IsOpenImmersion q.left] :
    ∃ (W : AlgebraicGeometry.BigFppfOver site S hS)
      (a : yoneda.obj W ⟶
        (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
          (Over.post site.inclusion) (AlgebraicGeometry.groupoidPreRelation H)).obj),
      AlgebraicGeometry.IsAlgebraicSpace site S hS
          (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
            (Over.post site.inclusion) (AlgebraicGeometry.groupoidPreRelation H)).obj ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj W).size ≤
          H.objects.left.size := by
  let : JointlyMono₂ G.target G.source := jointlyMono_of_relation G hrel
  let : JointlyMono₂ H.target H.source :=
    jointlyMono_of_flat_surjective_fullyFaithful_groupoid i hi
  let : IsOpenImmersion H.identity.left :=
    isOpenImmersion_identity_of_fppf_fullyFaithful_groupoid i hi q t s hqt hqs hp
  let : MorphismProperty.IsLocalAtSource (@Flat : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtSource.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  let : MorphismProperty.IsLocalAtTarget (@Flat : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  let : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  let : Flat H.source.left :=
    property_source_of_fppf_fullyFaithful_groupoid (@Flat) i hi
      (show Flat G.source.left from inferInstance)
  let : LocallyOfFinitePresentation H.source.left :=
    property_source_of_fppf_fullyFaithful_groupoid (@LocallyOfFinitePresentation) i hi
      (show LocallyOfFinitePresentation G.source.left from inferInstance)
  exact exists_atlas_quotient_of_open_identity site S hS H hU
    (isEquivalenceRelation_of_jointlyMono_groupoid H)

private noncomputable def coequalizerIsoOfIso {C : Type*} [Category* C]
    {X Y X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y')
    [HasCoequalizer f g] [HasCoequalizer f' g']
    (eX : X ≅ X') (eY : Y ≅ Y')
    (hf : f ≫ eY.hom = eX.hom ≫ f') (hg : g ≫ eY.hom = eX.hom ≫ g') :
    coequalizer f g ≅ coequalizer f' g' :=
  HasColimit.isoOfNatIso (parallelPair.ext eX eY hf hg)

private noncomputable def coequalizerSwapIso {C : Type*} [Category* C]
    {X Y : C} (f g : X ⟶ Y) [HasCoequalizer f g] [HasCoequalizer g f] :
    coequalizer f g ≅ coequalizer g f where
  hom := coequalizer.desc (coequalizer.π g f) (coequalizer.condition g f).symm
  inv := coequalizer.desc (coequalizer.π f g) (coequalizer.condition f g).symm
  hom_inv_id := by apply coequalizer.hom_ext; simp
  inv_hom_id := by apply coequalizer.hom_ext; simp

private noncomputable def postPointsIso
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (Z : AlgebraicGeometry.BigFppfOver site S hS) :
    Stacks.Groupoids.points (Over.post site.inclusion)
        ((Over.post site.inclusion).obj Z) ≅ yoneda.obj Z where
  hom :=
    { app := fun T => ↾ fun g =>
        (Over.post site.inclusion).preimage (X := T.unop) (Y := Z) g
      naturality := by
        intro T T' u
        ext g
        change (Over.post site.inclusion).preimage
            ((Over.post site.inclusion).map u.unop ≫ g) =
          u.unop ≫ (Over.post site.inclusion).preimage g
        rw [Functor.preimage_comp, Functor.preimage_map] }
  inv :=
    { app := fun T => ↾ fun f =>
        (Over.post site.inclusion).map (X := T.unop) (Y := Z) f
      naturality := by
        intro T T' u
        ext f
        exact (Over.post site.inclusion).map_comp u.unop f }
  hom_inv_id := by
    ext T g
    exact (Over.post site.inclusion).map_preimage g
  inv_hom_id := by
    ext T f
    exact (Over.post site.inclusion).preimage_map f

private theorem locallySurjective_of_surjectiveEtale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) f := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  refine ⟨?_⟩
  intro T x
  let g : yoneda.obj T ⟶ F := yonedaEquiv.symm x
  let hrep := MorphismProperty.relative.rep hs
  let V := hrep.pullback g
  let q := hrep.snd g
  have hcover : Sieve.generate (Presieve.singleton q) ∈ J T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    apply B.topology.superset_covering (Sieve.generate_mono ?_)
      (AlgebraicGeometry.Space.singleton_mem_bigFppf_topology B q.left
        (hs.property g (hrep.fst g) q (hrep.isPullback g))
        (he.property g (hrep.fst g) q (hrep.isPullback g)))
    exact (Presieve.singleton_le_iff q.left).2
      ⟨V, q, 𝟙 _, Presieve.singleton_self q, by simp⟩
  have hq : Presheaf.imageSieve f x q := by
    refine ⟨yonedaEquiv (yoneda.map (hrep.fst' g)), ?_⟩
    have h : yoneda.map (hrep.fst' g) ≫ f = yoneda.map q ≫ g := by
      simpa only [hrep.map_fst' g] using hrep.w g
    show f.app (Opposite.op V) (yonedaEquiv (yoneda.map (hrep.fst' g))) =
      F.map q.op x
    rw [yonedaEquiv_yoneda_map]
    exact congrArg (fun k => k.app (Opposite.op V) (𝟙 V)) h
  apply J.superset_covering ?_ hcover
  rw [Sieve.generate_le_iff]
  rintro W k ⟨⟩
  exact hq

private theorem mono_left_of_mono_over {C : Type*} [Category* C] {B : C}
    {X Y : Over B} (f : X ⟶ Y) [Mono f] : Mono f.left := by
  constructor
  intro Z a b hab
  have hw : b ≫ X.hom = a ≫ X.hom := by
    rw [← Over.w f, ← Category.assoc, ← Category.assoc, hab]
  have h : (Over.homMk a : Over.mk (a ≫ X.hom) ⟶ X) = Over.homMk b hw :=
    (cancel_mono f).mp (Over.OverMorphism.ext hab)
  exact congrArg Over.Hom.left h

private theorem over_prod_left_hom_ext {C : Type*} [Category* C] {B : C}
    [HasBinaryProducts (Over B)] {X Y : Over B} {Z : C}
    {a b : Z ⟶ (X ⨯ Y : Over B).left}
    (h₁ : a ≫ (prod.fst : (X ⨯ Y : Over B) ⟶ X).left =
      b ≫ (prod.fst : (X ⨯ Y : Over B) ⟶ X).left)
    (h₂ : a ≫ (prod.snd : (X ⨯ Y : Over B) ⟶ Y).left =
      b ≫ (prod.snd : (X ⨯ Y : Over B) ⟶ Y).left) : a = b := by
  have e := Over.w (prod.fst : (X ⨯ Y : Over B) ⟶ X)
  have hw : b ≫ (X ⨯ Y : Over B).hom = a ≫ (X ⨯ Y : Over B).hom := by
    calc b ≫ (X ⨯ Y : Over B).hom
        = b ≫ (prod.fst : (X ⨯ Y : Over B) ⟶ X).left ≫ X.hom := by rw [e]
      _ = a ≫ (prod.fst : (X ⨯ Y : Over B) ⟶ X).left ≫ X.hom := by
          rw [← Category.assoc, ← h₁, Category.assoc]
      _ = a ≫ (X ⨯ Y : Over B).hom := by rw [e]
  have h : (Over.homMk a : Over.mk (a ≫ (X ⨯ Y : Over B).hom) ⟶ (X ⨯ Y : Over B)) =
      Over.homMk b hw := by
    apply prod.hom_ext <;> apply Over.OverMorphism.ext
    exacts [h₁, h₂]
  exact congrArg Over.Hom.left h

/-- The underlying square of the two product projections in a slice category is a
pullback square. -/
private theorem isPullback_over_prod {C : Type*} [Category* C] {B : C}
    [HasBinaryProducts (Over B)] (X Y : Over B) :
    IsPullback (prod.fst : (X ⨯ Y : Over B) ⟶ X).left
      (prod.snd : (X ⨯ Y : Over B) ⟶ Y).left X.hom Y.hom := by
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [Over.w, Over.w]
  · intro T a b h₁ h₂
    exact over_prod_left_hom_ext h₁ h₂
  · intro T a b h
    refine ⟨(prod.lift (Over.homMk a : Over.mk (a ≫ X.hom) ⟶ X)
      (Over.homMk b h.symm : Over.mk (a ≫ X.hom) ⟶ Y)).left, ?_, ?_⟩
    · exact congrArg Over.Hom.left (prod.lift_fst _ _)
    · exact congrArg Over.Hom.left (prod.lift_snd _ _)

private theorem mono_map_of_preservesPullback {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [Mono f] [PreservesLimit (cospan f f) F] :
    Mono (F.map f) := by
  have h : IsKernelPair (F.map f) (F.map (𝟙 X)) (F.map (𝟙 X)) :=
    (IsKernelPair.id_of_mono f).map F
  have : IsIso (F.map (𝟙 X)) := by
    rw [F.map_id]
    infer_instance
  exact h.mono_of_isIso_fst

private theorem jointlyMono_of_mono_prodLift {C : Type*} [Category* C] {R X : C}
    [HasBinaryProduct X X] {p₁ p₂ : R ⟶ X} (h : Mono (prod.lift p₁ p₂)) :
    JointlyMono₂ p₁ p₂ := by
  constructor
  intro Y f g h₁ h₂
  refine (cancel_mono (prod.lift p₁ p₂)).mp (prod.hom_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc, prod.lift_fst, h₁]
  · rw [Category.assoc, Category.assoc, prod.lift_snd, h₂]

private theorem mono_prodLift_of_jointlyMono {C : Type*} [Category* C] {R X : C}
    [HasBinaryProduct X X] (p₁ p₂ : R ⟶ X) [JointlyMono₂ p₁ p₂] :
    Mono (prod.lift p₁ p₂) := by
  constructor
  intro Z f g h
  refine JointlyMono₂.right_cancellation (p₁ := p₁) (p₂ := p₂) f g ?_ ?_
  · simpa only [Category.assoc, prod.lift_fst] using congrArg (fun k => k ≫ prod.fst) h
  · simpa only [Category.assoc, prod.lift_snd] using congrArg (fun k => k ≫ prod.snd) h

/-- A morphism of a slice category factoring a jointly monic pair through retractions
is a monomorphism on underlying objects. -/
private theorem mono_of_jointlyMono_factor {C : Type*} [Category* C] {B : C}
    {RR UU : Over B} (t s : RR ⟶ UU) [JointlyMono₂ t s] {T : C}
    (q : RR.left ⟶ T) (q₁ q₂ : T ⟶ UU.left)
    (h₁ : q ≫ q₁ = t.left) (h₂ : q ≫ q₂ = s.left) : Mono q := by
  constructor
  intro Z x y hxy
  have hx₁ : x ≫ t.left = y ≫ t.left := by
    rw [← h₁, ← Category.assoc, hxy, Category.assoc]
  have hx₂ : x ≫ s.left = y ≫ s.left := by
    rw [← h₂, ← Category.assoc, hxy, Category.assoc]
  have hw : y ≫ RR.hom = x ≫ RR.hom := by
    rw [← Over.w t, ← Category.assoc, ← hx₁, Category.assoc, Over.w t]
  have hxy' : (Over.homMk x : Over.mk (x ≫ RR.hom) ⟶ RR) = Over.homMk y hw :=
    JointlyMono₂.right_cancellation (p₁ := t) (p₂ := s) _ _
      (Over.OverMorphism.ext hx₁) (Over.OverMorphism.ext hx₂)
  exact congrArg Over.Hom.left hxy'

/-- `Over.post` preserves any connected limit that the base functor preserves. -/
private theorem overPost_preservesLimitsOfShape {C D : Type*} [Category* C] [Category* D]
    {J : Type*} [Category* J] [IsConnected J] (F : C ⥤ D) (X : C)
    [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J (Over.post (X := X) F) := by
  have e : Over.post (X := X) F ⋙ Over.forget (F.obj X) ≅ Over.forget X ⋙ F :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [Over.post])
  have h : PreservesLimitsOfShape J (Over.post (X := X) F ⋙ Over.forget (F.obj X)) :=
    preservesLimitsOfShape_of_natIso e.symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget (F.obj X))

/-- The generic base-change square exhibiting one projection of a restricted
pre-relation as a base change. -/
private theorem isPullback_restrict_proj {C : Type*} [Category* C]
    {U U' R P P' : C} (g : U' ⟶ U) (gg : P' ⟶ P) (j : R ⟶ P)
    (p₁ p₂ : P ⟶ U) (q₁ q₂ : P' ⟶ U')
    (lft : {T : C} → (T ⟶ U') → (T ⟶ U') → (T ⟶ P'))
    (hl₁ : ∀ {T : C} (a b : T ⟶ U'), lft a b ≫ q₁ = a)
    (hl₂ : ∀ {T : C} (a b : T ⟶ U'), lft a b ≫ q₂ = b)
    (hext : ∀ {T : C} (a b : T ⟶ P'), a ≫ q₁ = b ≫ q₁ → a ≫ q₂ = b ≫ q₂ → a = b)
    (hextP : ∀ {T : C} (a b : T ⟶ P), a ≫ p₁ = b ≫ p₁ → a ≫ p₂ = b ≫ p₂ → a = b)
    (hq₁ : gg ≫ p₁ = q₁ ≫ g) (hq₂ : gg ≫ p₂ = q₂ ≫ g)
    [HasPullback gg j] [HasPullback (j ≫ p₁) g]
    (k : pullback gg j ⟶ pullback (j ≫ p₁) g)
    (hk₁ : k ≫ pullback.fst (j ≫ p₁) g = pullback.snd gg j)
    (hk₂ : k ≫ pullback.snd (j ≫ p₁) g = pullback.fst gg j ≫ q₁) :
    IsPullback k (pullback.fst gg j ≫ q₂)
      (pullback.fst (j ≫ p₁) g ≫ j ≫ p₂) g := by
  have hcond : pullback.fst gg j ≫ gg = pullback.snd gg j ≫ j := pullback.condition
  have hcondA : pullback.fst (j ≫ p₁) g ≫ j ≫ p₁ =
      pullback.snd (j ≫ p₁) g ≫ g := by
    simpa only [Category.assoc] using (pullback.condition (f := j ≫ p₁) (g := g))
  refine IsPullback.mk' ?_ ?_ ?_
  · calc k ≫ pullback.fst (j ≫ p₁) g ≫ j ≫ p₂
        = (k ≫ pullback.fst (j ≫ p₁) g) ≫ j ≫ p₂ := by simp only [Category.assoc]
      _ = pullback.snd gg j ≫ j ≫ p₂ := by rw [hk₁]
      _ = (pullback.fst gg j ≫ gg) ≫ p₂ := by rw [hcond, Category.assoc]
      _ = (pullback.fst gg j ≫ q₂) ≫ g := by simp only [Category.assoc, hq₂]
  · intro T φ φ' h₁ h₂
    apply pullback.hom_ext
    · refine hext _ _ ?_ ?_
      · calc (φ ≫ pullback.fst gg j) ≫ q₁
            = (φ ≫ k) ≫ pullback.snd (j ≫ p₁) g := by simp only [Category.assoc, hk₂]
          _ = (φ' ≫ k) ≫ pullback.snd (j ≫ p₁) g := by rw [h₁]
          _ = (φ' ≫ pullback.fst gg j) ≫ q₁ := by simp only [Category.assoc, hk₂]
      · simpa only [Category.assoc] using h₂
    · calc φ ≫ pullback.snd gg j
          = (φ ≫ k) ≫ pullback.fst (j ≫ p₁) g := by simp only [Category.assoc, hk₁]
        _ = (φ' ≫ k) ≫ pullback.fst (j ≫ p₁) g := by rw [h₁]
        _ = φ' ≫ pullback.snd gg j := by simp only [Category.assoc, hk₁]
  · intro T x y hxy
    have hxab : x ≫ pullback.fst (j ≫ p₁) g ≫ j ≫ p₁ =
        x ≫ pullback.snd (j ≫ p₁) g ≫ g := by rw [hcondA]
    have hz : lft (x ≫ pullback.snd (j ≫ p₁) g) y ≫ gg =
        (x ≫ pullback.fst (j ≫ p₁) g) ≫ j := by
      refine hextP _ _ ?_ ?_
      · calc (lft (x ≫ pullback.snd (j ≫ p₁) g) y ≫ gg) ≫ p₁
            = (lft (x ≫ pullback.snd (j ≫ p₁) g) y ≫ q₁) ≫ g := by
              simp only [Category.assoc, hq₁]
          _ = x ≫ pullback.snd (j ≫ p₁) g ≫ g := by
              rw [hl₁]; simp only [Category.assoc]
          _ = x ≫ pullback.fst (j ≫ p₁) g ≫ j ≫ p₁ := hxab.symm
          _ = ((x ≫ pullback.fst (j ≫ p₁) g) ≫ j) ≫ p₁ := by simp only [Category.assoc]
      · calc (lft (x ≫ pullback.snd (j ≫ p₁) g) y ≫ gg) ≫ p₂
            = (lft (x ≫ pullback.snd (j ≫ p₁) g) y ≫ q₂) ≫ g := by
              simp only [Category.assoc, hq₂]
          _ = y ≫ g := by rw [hl₂]
          _ = x ≫ pullback.fst (j ≫ p₁) g ≫ j ≫ p₂ := by
              simpa only [Category.assoc] using hxy.symm
          _ = ((x ≫ pullback.fst (j ≫ p₁) g) ≫ j) ≫ p₂ := by simp only [Category.assoc]
    refine ⟨pullback.lift (lft (x ≫ pullback.snd (j ≫ p₁) g) y)
      (x ≫ pullback.fst (j ≫ p₁) g) hz, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hk₁, pullback.lift_snd]
      · rw [Category.assoc, hk₂, ← Category.assoc, pullback.lift_fst, hl₁]
    · rw [← Category.assoc, pullback.lift_fst, hl₂]

private theorem isPullback_restrict_source {C : Type*} [Category* C]
    [HasBinaryProducts C] [HasPullbacks C] {R U U' : C}
    (j : R ⟶ U ⨯ U) (g : U' ⟶ U) :
    ∃ k, IsPullback k (pullback.fst (prod.map g g) j ≫ prod.snd)
      (pullback.fst (j ≫ prod.fst) g ≫ j ≫ prod.snd) g := by
  have hk : pullback.snd (prod.map g g) j ≫ (j ≫ prod.fst) =
      (pullback.fst (prod.map g g) j ≫ prod.fst) ≫ g := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, prod.map_fst,
      ← Category.assoc]
  exact ⟨_, isPullback_restrict_proj g (prod.map g g) j prod.fst prod.snd prod.fst prod.snd
    (fun a b => prod.lift a b) (fun a b => prod.lift_fst a b)
    (fun a b => prod.lift_snd a b) (fun _ _ h₁ h₂ => prod.hom_ext h₁ h₂)
    (fun _ _ h₁ h₂ => prod.hom_ext h₁ h₂) (prod.map_fst g g) (prod.map_snd g g)
    (pullback.lift _ _ hk) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩

private theorem isPullback_restrict_target {C : Type*} [Category* C]
    [HasBinaryProducts C] [HasPullbacks C] {R U U' : C}
    (j : R ⟶ U ⨯ U) (g : U' ⟶ U) :
    ∃ k, IsPullback k (pullback.fst (prod.map g g) j ≫ prod.fst)
      (pullback.fst (j ≫ prod.snd) g ≫ j ≫ prod.fst) g := by
  have hk : pullback.snd (prod.map g g) j ≫ (j ≫ prod.snd) =
      (pullback.fst (prod.map g g) j ≫ prod.snd) ≫ g := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, prod.map_snd,
      ← Category.assoc]
  exact ⟨_, isPullback_restrict_proj g (prod.map g g) j prod.snd prod.fst prod.snd prod.fst
    (fun a b => prod.lift b a) (fun a b => prod.lift_snd b a)
    (fun a b => prod.lift_fst b a) (fun _ _ h₁ h₂ => prod.hom_ext h₂ h₁)
    (fun _ _ h₁ h₂ => prod.hom_ext h₂ h₁) (prod.map_snd g g) (prod.map_fst g g)
    (pullback.lift _ _ hk) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩

private theorem comp_inv_eq_inv_comp {C : Type*} [Category* C] {X Y X' Y' : C}
    {A : X' ⟶ Y'} {B : X ⟶ Y} {eX : X ≅ X'} {eY : Y ≅ Y'}
    (h : B ≫ eY.hom = eX.hom ≫ A) : A ≫ eY.inv = eX.inv ≫ B := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

private theorem postPointsIso_hom_naturality
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {X Y : AlgebraicGeometry.BigFppfOver site S hS} (f : X ⟶ Y) :
    (Over.post site.inclusion).op.whiskerLeft
        (yoneda.map ((Over.post site.inclusion).map f)) ≫
      (postPointsIso site S hS Y).hom =
      (postPointsIso site S hS X).hom ≫ yoneda.map f := by
  ext T g
  show (Over.post site.inclusion).preimage (g ≫ (Over.post site.inclusion).map f) =
    (Over.post site.inclusion).preimage g ≫ f
  rw [Functor.preimage_comp, Functor.preimage_map]

/-- An étale, representable map of presheaves satisfies every étale-local property
containing the étale morphisms. -/
private theorem chartProperty_of_etale_presheaf
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hle : ∀ {X Y : Scheme.{u}} (k : X ⟶ Y), Etale k → P k)
    {F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    {V : AlgebraicGeometry.BigFppfOver site S hS} (f : yoneda.obj V ⟶ F)
    (hF : AlgebraicGeometry.IsAlgebraicSpace site S hS F)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) f) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P f := by
  refine (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative site S hS P hP
    (AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS V) hF f he.rep).mpr ?_
  exact ⟨he.rep, fun _ _ gg fst snd BC => hle _ (he.property gg fst snd BC)⟩

private theorem toSheafify_isLocallySurjective
    {D : Type*} [Category* D] (J : GrothendieckTopology D)
    [HasSheafify J (Type u)] (P : Dᵒᵖ ⥤ Type u) :
    Presheaf.IsLocallySurjective J (toSheafify J P) := by
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  set G := Subfunctor.sheafify J (Subfunctor.range (toSheafify J P)) with hG
  have hPsheaf : Presheaf.IsSheaf J (sheafify J P) :=
    ((presheafToSheaf J (Type u)).obj P).property
  have hGsheaf : Presheaf.IsSheaf J G.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      ((Subfunctor.range (toSheafify J P)).sheafify_isSheaf
        ((isSheaf_iff_isSheaf_of_type J _).mp hPsheaf))
  have hfac : Subfunctor.toRangeSheafify J (toSheafify J P) ≫ G.ι =
      toSheafify J P := by
    ext X x
    rfl
  rw [Subfunctor.eq_top_iff_isIso]
  have hsplit : IsSplitEpi G.ι := by
    refine IsSplitEpi.mk ⟨⟨sheafifyLift J
      (Subfunctor.toRangeSheafify J (toSheafify J P)) hGsheaf, ?_⟩⟩
    refine sheafify_hom_ext J _ _ hPsheaf ?_
    rw [Category.comp_id, ← Category.assoc, toSheafify_sheafifyLift, hfac]
  exact isIso_of_mono_of_isSplitEpi G.ι

private theorem quotientPoint_locallySurjective
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] {S : Scheme.{u}} (F : C ⥤ Over S)
    {R U : Over S} (j : Stacks.Groupoids.PreRelation R U) :
    Presheaf.IsLocallySurjective J (Stacks.Groupoids.toQuotientSheaf J F j) := by
  have hπ : Presheaf.IsLocallySurjective J (Stacks.Groupoids.toQuotientPresheaf F j) := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro X
    have hEpi : Epi (Stacks.Groupoids.toQuotientPresheaf F j) := by
      unfold Stacks.Groupoids.toQuotientPresheaf
      infer_instance
    exact (CategoryTheory.epi_iff_surjective _).1
      ((NatTrans.epi_iff_epi_app _).1 hEpi X)
  have hsh : Presheaf.IsLocallySurjective J
      (toSheafify J (Stacks.Groupoids.quotientPresheaf F j)) :=
    toSheafify_isLocallySurjective J (Stacks.Groupoids.quotientPresheaf F j)
  show Presheaf.IsLocallySurjective J
    (Stacks.Groupoids.toQuotientPresheaf F j ≫
      toSheafify J (Stacks.Groupoids.quotientPresheaf F j))
  exact Presheaf.isLocallySurjective_comp J _ _

/-- A property stable under base change and composition passes to the composite of the base
change of a map `g` along any map `f` with a map `s` having the property. -/
private theorem property_pullback_fst_comp
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition]
    {S : Scheme.{u}} {X Y Z W : Over S} (f : X ⟶ Z) (g : Y ⟶ Z) (s : X ⟶ W)
    (hg : P g.left) (hs : P s.left) : P (pullback.fst f g ≫ s).left := by
  rw [Over.comp_left]
  exact P.comp_mem _ _
    (P.of_isPullback ((IsPullback.of_hasPullback f g).flip.map (Over.forget S)) hg) hs

/-- A property stable under base change and composition passes from the source map of a
pre-relation of schemes, and the restricting morphism, to the source map of the restricted
pre-relation. -/
private theorem property_preRelation_restrict_source
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition]
    {S : Scheme.{u}} {R U U' : Over S} (j : Stacks.Groupoids.PreRelation R U) (g : U' ⟶ U)
    (hs : P j.source.left) (hg : P g.left) :
    P (AlgebraicGeometry.PreRelation.restrict j g).source.left := by
  obtain ⟨k, hk⟩ := isPullback_restrict_source j g
  exact P.of_isPullback (hk.map (Over.forget S))
    (property_pullback_fst_comp P _ g _ hg hs)

/-- The analogue of `property_preRelation_restrict_source` for the target map. -/
private theorem property_preRelation_restrict_target
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition]
    {S : Scheme.{u}} {R U U' : Over S} (j : Stacks.Groupoids.PreRelation R U) (g : U' ⟶ U)
    (ht : P j.target.left) (hg : P g.left) :
    P (AlgebraicGeometry.PreRelation.restrict j g).target.left := by
  obtain ⟨k, hk⟩ := isPullback_restrict_target j g
  exact P.of_isPullback (hk.map (Over.forget S))
    (property_pullback_fst_comp P _ g _ hg ht)

/-- A covering of the big fppf site which is an fppf covering of schemes generates a covering
sieve. -/
private theorem generate_presieve₀_mem_bigFppf_topology
    (B : AlgebraicGeometry.BigFppfSite.{u}) (E : Covering B.Schemes)
    (hE : AlgebraicGeometry.IsFppfCovering E) :
    Sieve.generate E.2.presieve₀ ∈ B.topology E.1 := by
  obtain ⟨⟨X', E'⟩, hE', hEquiv⟩ := B.fppf_has_representative E hE
  have hpre : E.2.presieve₀ ∈ B.precoverage E.1 := by
    obtain ⟨hX', hComb⟩ := hEquiv
    dsimp only at hX'
    subst X'
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E', rfl, hE'⟩
  exact Precoverage.generate_mem_toGrothendieck hpre

/-- A surjective, flat, locally finitely presented morphism of site objects generates a
covering sieve of the big fppf site. This is the flat analogue of
`AlgebraicGeometry.singleton_mem_bigFppf_topology`, whose property is étaleness. -/
private theorem singleton_mem_bigFppf_topology_flat
    (B : AlgebraicGeometry.BigFppfSite.{u}) {X Y : B.Schemes} (g : Y ⟶ X)
    (hs : Surjective (B.inclusion.map g)) (hf : Flat (B.inclusion.map g))
    (hl : LocallyOfFinitePresentation (B.inclusion.map g)) :
    Sieve.generate (Presieve.singleton g) ∈ B.topology X := by
  let g' := B.inclusion.map g
  have hFppf : Presieve.singleton g' ∈
      Scheme.fppfPrecoverage (B.inclusion.obj X) := by
    let : Surjective g' := hs
    rw [Scheme.fppfPrecoverage, Scheme.singleton_mem_precoverage_iff]
    exact ⟨Scheme.Hom.surjective g', hf, hl⟩
  let E : Covering B.Schemes := ⟨X, PreZeroHypercover.singleton g⟩
  have hE : AlgebraicGeometry.IsFppfCovering E := by
    show (PreZeroHypercover.singleton g).presieve₀.map B.inclusion ∈
      Scheme.fppfPrecoverage (B.inclusion.obj X)
    simpa only [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton] using hFppf
  simpa [E, PreZeroHypercover.presieve₀_singleton] using
    generate_presieve₀_mem_bigFppf_topology B E hE

/-- The flat analogue of `locallySurjective_of_surjectiveEtale`: a morphism from a
representable which is representable by surjective, flat, locally finitely presented
morphisms of schemes is locally surjective. -/
private theorem locallySurjective_of_surjectiveFlatLfp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f)
    (hfl : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Flat.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) f := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  refine ⟨?_⟩
  intro T x
  let g : yoneda.obj T ⟶ F := yonedaEquiv.symm x
  let hrep := MorphismProperty.relative.rep hs
  let V := hrep.pullback g
  let q := hrep.snd g
  have hcover : Sieve.generate (Presieve.singleton q) ∈ J T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    apply B.topology.superset_covering (Sieve.generate_mono ?_)
      (singleton_mem_bigFppf_topology_flat B q.left
        (hs.property g (hrep.fst g) q (hrep.isPullback g))
        (hfl.property g (hrep.fst g) q (hrep.isPullback g))
        (hlfp.property g (hrep.fst g) q (hrep.isPullback g)))
    exact (Presieve.singleton_le_iff q.left).2
      ⟨V, q, 𝟙 _, Presieve.singleton_self q, by simp⟩
  have hq : Presheaf.imageSieve f x q := by
    refine ⟨yonedaEquiv (yoneda.map (hrep.fst' g)), ?_⟩
    have h : yoneda.map (hrep.fst' g) ≫ f = yoneda.map q ≫ g := by
      simpa only [hrep.map_fst' g] using hrep.w g
    show f.app (Opposite.op V) (yonedaEquiv (yoneda.map (hrep.fst' g))) =
      F.map q.op x
    rw [yonedaEquiv_yoneda_map]
    exact congrArg (fun k => k.app (Opposite.op V) (𝟙 V)) h
  apply J.superset_covering ?_ hcover
  rw [Sieve.generate_le_iff]
  rintro W k ⟨⟩
  exact hq

/-- A property of schemes stable under base change passes from a morphism of site objects
to the induced morphism of functors of points, in the relative sense. -/
private theorem presheaf_of_property_yonedaMap
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {X Y : AlgebraicGeometry.BigFppfOver site S hS} (f : X ⟶ Y)
    (hf : P ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map f)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) (yoneda.map f) := by
  let Q := MorphismProperty.inverseImage P (AlgebraicGeometry.BigFppfOver.toScheme site S hS)
  let : Q.IsStableUnderBaseChange := by
    refine ⟨?_⟩
    intro A B' B'' T a b a' b' hp hb
    change P ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map b) at hb
    show P ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map b')
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
      (hp.map (AlgebraicGeometry.BigFppfOver.toScheme site S hS)) hb
  exact MorphismProperty.relative_map (F := yoneda) hf

/-- The local surjectivity hypothesis of `Stacks.Groupoids.restrictQuotientSheafMap_isIso`, in the
shape it is stated in, for a surjective, flat, locally finitely presented morphism of site
objects. -/
private theorem locallySurjective_postWhisker_of_flat
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {U' U : AlgebraicGeometry.BigFppfOver site S hS} (g : U' ⟶ U)
    (hs : Surjective ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map g))
    (hf : Flat ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map g))
    (hl : LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map g)) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology site S hS)
      ((Over.post site.inclusion).op.whiskerLeft
        (yoneda.map ((Over.post site.inclusion).map g))) := by
  let J := AlgebraicGeometry.BigFppfOver.topology site S hS
  have hy : Presheaf.IsLocallySurjective J (yoneda.map g) :=
    locallySurjective_of_surjectiveFlatLfp site S hS (yoneda.map g)
      (presheaf_of_property_yonedaMap (@Surjective.{u}) site S hS g hs)
      (presheaf_of_property_yonedaMap (@Flat.{u}) site S hS g hf)
      (presheaf_of_property_yonedaMap (@LocallyOfFinitePresentation.{u}) site S hS g hl)
  have hA : (Over.post site.inclusion).op.whiskerLeft
      (yoneda.map ((Over.post site.inclusion).map g)) =
      (postPointsIso site S hS U').hom ≫ yoneda.map g ≫
        (postPointsIso site S hS U).inv := by
    rw [← Category.assoc, ← postPointsIso_hom_naturality site S hS g, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [hA]
  let : Presheaf.IsLocallySurjective J (yoneda.map g) := hy
  infer_instance

/-- `LocallyOfFiniteType` passes from the source leg of a relation to `R ⟶ U ⨯ U`. -/
private theorem locallyOfFiniteType_prodLift {S : Scheme.{u}} {R U : Over S}
    (t s : R ⟶ U) [LocallyOfFiniteType s.left] :
    LocallyOfFiniteType (prod.lift t s : R ⟶ (U ⨯ U : Over S)).left := by
  have h : (prod.lift t s : R ⟶ (U ⨯ U : Over S)).left ≫
      (prod.snd : (U ⨯ U : Over S) ⟶ U).left = s.left := by
    rw [← Over.comp_left, prod.lift_snd]
  let : LocallyOfFiniteType ((prod.lift t s : R ⟶ (U ⨯ U : Over S)).left ≫
      (prod.snd : (U ⨯ U : Over S) ⟶ U).left) := h ▸ inferInstance
  exact locallyOfFiniteType_of_comp (prod.lift t s : R ⟶ (U ⨯ U : Over S)).left
    (prod.snd : (U ⨯ U : Over S) ⟶ U).left

/-- `LocallyQuasiFinite` passes from the source leg of a relation to `R ⟶ U ⨯ U`. -/
private theorem locallyQuasiFinite_prodLift {S : Scheme.{u}} {R U : Over S}
    (t s : R ⟶ U) [LocallyQuasiFinite s.left] :
    LocallyQuasiFinite (prod.lift t s : R ⟶ (U ⨯ U : Over S)).left := by
  have h : (prod.lift t s : R ⟶ (U ⨯ U : Over S)).left ≫
      (prod.snd : (U ⨯ U : Over S) ⟶ U).left = s.left := by
    rw [← Over.comp_left, prod.lift_snd]
  let : LocallyQuasiFinite ((prod.lift t s : R ⟶ (U ⨯ U : Over S)).left ≫
      (prod.snd : (U ⨯ U : Over S) ⟶ U).left) := h ▸ inferInstance
  exact LocallyQuasiFinite.of_comp (prod.lift t s : R ⟶ (U ⨯ U : Over S)).left
    (prod.snd : (U ⨯ U : Over S) ⟶ U).left

/-- A morphism out of a separated scheme is separated, applied to `R ⟶ U ⨯ U`. -/
private theorem isSeparated_prodLift_of_isSeparated {S : Scheme.{u}} {R U : Over S}
    (t s : R ⟶ U) (hR : R.left.IsSeparated) :
    IsSeparated (prod.lift t s : R ⟶ (U ⨯ U : Over S)).left := by
  let : R.left.IsSeparated := hR
  infer_instance

/-- A finite locally free morphism is flat, locally of finite presentation and finite. -/
private theorem flat_lfp_isFinite_of_isFiniteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : Stacks.Morphisms.IsFiniteLocallyFree f) :
    Flat f ∧ LocallyOfFinitePresentation f ∧ IsFinite f := by
  obtain ⟨h₁, h₂, h₃⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp h
  exact ⟨h₂, h₃, h₁⟩

/-- The object scheme of a pre-relation over an affine object scheme is a separated
scheme. -/
private theorem isSeparated_relation_of_isAffine
    {S : Scheme.{u}} {R U : Over S} [IsAffine U.left]
    (j : Stacks.Groupoids.PreRelation R U) [Mono j] : R.left.IsSeparated := by
  have hU : IsSeparated U.hom := inferInstance
  have hsnd : IsSeparated (prod.snd : (U ⨯ U : Over S) ⟶ U).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_over_prod U U) hU
  have hprod : (U ⨯ U : Over S).left.IsSeparated := by
    constructor
    have h : terminal.from ((U ⨯ U : Over S).left) =
        (prod.snd : (U ⨯ U : Over S) ⟶ U).left ≫ terminal.from U.left :=
      terminal.hom_ext _ _
    rw [h]
    let : IsSeparated (prod.snd : (U ⨯ U : Over S) ⟶ U).left := hsnd
    infer_instance
  constructor
  have h : terminal.from R.left = j.left ≫ terminal.from ((U ⨯ U : Over S).left) :=
    terminal.hom_ext _ _
  rw [h]
  let : Mono j.left := mono_left_of_mono_over j
  let : (U ⨯ U : Over S).left.IsSeparated := hprod
  infer_instance

/-- Both legs of a pre-relation over an affine object scheme are separated morphisms. -/
private theorem isSeparated_source_of_isAffine
    {S : Scheme.{u}} {R U : Over S} [IsAffine U.left]
    (j : Stacks.Groupoids.PreRelation R U) [Mono j] :
    IsSeparated j.source.left ∧ IsSeparated j.target.left := by
  let : R.left.IsSeparated := isSeparated_relation_of_isAffine j
  exact ⟨inferInstance, inferInstance⟩

/-- Local finite presentation and local quasi-finiteness give quasi-finiteness at every
point. -/
private theorem quasiFiniteAt_of_lfp_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    [LocallyQuasiFinite f] (x : X) : AlgebraicGeometry.quasiFiniteAt f x :=
  (AlgebraicGeometry.forall_quasiFiniteAt_iff f).mpr ⟨inferInstance, inferInstance⟩ x

/-- The quasi-splitting situation of Tag 04RV, built from a groupoid scheme whose object
scheme is affine and whose source and target are locally of finite presentation and
locally quasi-finite, at an arbitrary chosen point. -/
private noncomputable def quasiSplittingSituation
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsAffine G.objects.left]
    [Mono (AlgebraicGeometry.groupoidPreRelation G)]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left]
    [LocallyQuasiFinite G.source.left]
    (u : G.objects.left) : AlgebraicGeometry.Space.QuasiSplittingSituation.{u} :=
  let j : Stacks.Groupoids.PreRelation G.arrows G.objects := AlgebraicGeometry.groupoidPreRelation G
  have hs : j.source = G.source := prod.lift_snd _ _
  have ht : j.target = G.target := prod.lift_fst _ _
  have hsep := isSeparated_source_of_isAffine j
  { S := S
    groupoid := G
    u := u
    sourceSeparated := hs ▸ hsep.1
    targetSeparated := ht ▸ hsep.2
    sourceLocallyOfFiniteType := inferInstance
    targetLocallyOfFiniteType := inferInstance
    sourceQuasiFiniteAtIdentity :=
      quasiFiniteAt_of_lfp_of_locallyQuasiFinite G.source.left (G.identity.left u) }

/-- The mirror of `exists_atlas_quotient_of_restrict`: the same interface transports from
the quotient by a pre-equivalence relation to the quotient by its restriction along a
locally surjective morphism, again with the atlas object unchanged. -/
private theorem exists_atlas_quotient_restrict_of_quotient
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {R U U' : Over S} (j : Stacks.Groupoids.PreRelation R U) (g : U' ⟶ U)
    (hj : Stacks.Groupoids.IsPreEquivalenceRelation j)
    (hg : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology site S hS)
      ((Over.post site.inclusion).op.whiskerLeft (yoneda.map g)))
    {W : AlgebraicGeometry.BigFppfOver site S hS}
    (a : yoneda.obj W ⟶
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) j).obj)
    (hasurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a)
    (haetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a)
    (h : AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) j).obj) :
    ∃ a' : yoneda.obj W ⟶
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) (AlgebraicGeometry.PreRelation.restrict j g)).obj,
      AlgebraicGeometry.IsAlgebraicSpace site S hS
          (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
            (Over.post site.inclusion) (AlgebraicGeometry.PreRelation.restrict j g)).obj ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a' ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a' := by
  let q := Stacks.Groupoids.restrictQuotientSheafMap
    (AlgebraicGeometry.BigFppfOver.topology site S hS) (Over.post site.inclusion) j g
  let : IsIso q := Stacks.Groupoids.restrictQuotientSheafMap_isIso
    (AlgebraicGeometry.BigFppfOver.topology site S hS) (Over.post site.inclusion) j g hj hg
  let : IsIso q.hom := by
    show IsIso
      ((sheafToPresheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)).map q)
    infer_instance
  refine ⟨a ≫ inv q.hom, isAlgebraicSpace_of_iso site S hS
    ((sheafToPresheaf _ _).mapIso (asIso q)) h, ?_, ?_⟩
  · exact MorphismProperty.RespectsIso.postcomp _ (inv q.hom) a hasurj
  · exact MorphismProperty.RespectsIso.postcomp _ (inv q.hom) a haetale

/-- A fully faithful morphism of groupoid schemes exhibits the source groupoid as the
restriction of the target groupoid along the induced map of object schemes: the arrow scheme
of the source *is* the restricted arrow scheme by
`isPullback_of_fullyFaithful_groupoid`, so the two pre-relations have isomorphic quotient
presheaves. -/
private noncomputable def quotientPresheafIsoRestrictOfFullyFaithful
    {S : Scheme.{u}} {C : Type*} [Category* C] (F : C ⥤ Over S)
    {G H : Stacks.Groupoids.GroupoidScheme S}
    (i : G.Hom H) (hi : ∀ T, Nonempty (i.evaluation T).FullyFaithful) :
    Stacks.Groupoids.quotientPresheaf F (AlgebraicGeometry.groupoidPreRelation G) ≅
      Stacks.Groupoids.quotientPresheaf F
        (AlgebraicGeometry.PreRelation.restrict (AlgebraicGeometry.groupoidPreRelation H)
          i.mapObjects) := by
  have hpb := isPullback_of_fullyFaithful_groupoid i hi
  have hfst : hpb.isoPullback.hom ≫
      pullback.fst (prod.map i.mapObjects i.mapObjects)
        (AlgebraicGeometry.groupoidPreRelation H) =
      AlgebraicGeometry.groupoidPreRelation G := hpb.isoPullback_hom_fst
  have hsrc : hpb.isoPullback.hom ≫
      (AlgebraicGeometry.PreRelation.restrict (AlgebraicGeometry.groupoidPreRelation H)
        i.mapObjects).source = (AlgebraicGeometry.groupoidPreRelation G).source := by
    change hpb.isoPullback.hom ≫
      pullback.fst (prod.map i.mapObjects i.mapObjects)
        (AlgebraicGeometry.groupoidPreRelation H) ≫ prod.snd = _
    rw [← Category.assoc, hfst]
  have htgt : hpb.isoPullback.hom ≫
      (AlgebraicGeometry.PreRelation.restrict (AlgebraicGeometry.groupoidPreRelation H)
        i.mapObjects).target = (AlgebraicGeometry.groupoidPreRelation G).target := by
    change hpb.isoPullback.hom ≫
      pullback.fst (prod.map i.mapObjects i.mapObjects)
        (AlgebraicGeometry.groupoidPreRelation H) ≫ prod.fst = _
    rw [← Category.assoc, hfst]
  refine coequalizerIsoOfIso _ _ _ _
    (Functor.isoWhiskerLeft F.op (yoneda.mapIso hpb.isoPullback)) (Iso.refl _) ?_ ?_
  · change Functor.whiskerLeft F.op
        (yoneda.map (AlgebraicGeometry.groupoidPreRelation G).source) ≫ 𝟙 _ =
      Functor.whiskerLeft F.op (yoneda.map hpb.isoPullback.hom) ≫
        Functor.whiskerLeft F.op (yoneda.map
          (AlgebraicGeometry.PreRelation.restrict (AlgebraicGeometry.groupoidPreRelation H)
            i.mapObjects).source)
    rw [Category.comp_id, ← Functor.whiskerLeft_comp, ← Functor.map_comp, hsrc]
  · change Functor.whiskerLeft F.op
        (yoneda.map (AlgebraicGeometry.groupoidPreRelation G).target) ≫ 𝟙 _ =
      Functor.whiskerLeft F.op (yoneda.map hpb.isoPullback.hom) ≫
        Functor.whiskerLeft F.op (yoneda.map
          (AlgebraicGeometry.PreRelation.restrict (AlgebraicGeometry.groupoidPreRelation H)
            i.mapObjects).target)
    rw [Category.comp_id, ← Functor.whiskerLeft_comp, ← Functor.map_comp, htgt]

/-- The affine-case interface transports along an isomorphism of quotient presheaves, with the
atlas object, hence its size, unchanged. -/
private theorem exists_atlas_quotient_of_quotientPresheaf_iso
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {R U R' U' : Over S} (j : Stacks.Groupoids.PreRelation R U)
    (j' : Stacks.Groupoids.PreRelation R' U')
    (e : Stacks.Groupoids.quotientPresheaf (Over.post (X := site.obj hS) site.inclusion) j ≅
      Stacks.Groupoids.quotientPresheaf (Over.post (X := site.obj hS) site.inclusion) j')
    {W : AlgebraicGeometry.BigFppfOver site S hS}
    (a : yoneda.obj W ⟶
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) j').obj)
    (hasurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a)
    (haetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a)
    (h : AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) j').obj) :
    ∃ a' : yoneda.obj W ⟶
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) j).obj,
      AlgebraicGeometry.IsAlgebraicSpace site S hS
          (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
            (Over.post site.inclusion) j).obj ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a' ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a' := by
  refine ⟨a ≫ ((sheafToPresheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)).mapIso
      ((presheafToSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)).mapIso e)).inv,
    isAlgebraicSpace_of_iso site S hS
      ((sheafToPresheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)).mapIso
        ((presheafToSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)).mapIso e)) h,
    ?_, ?_⟩
  · exact MorphismProperty.RespectsIso.postcomp _ _ a hasurj
  · exact MorphismProperty.RespectsIso.postcomp _ _ a haetale

/-- The output of Stacks 04S4 in the shape the bootstrap argument consumes: the affine quotient
`Ū = U/P` of the object scheme by an open finite locally free subgroupoid `P`, the finite
locally free surjective quotient map `U ⟶ Ū` whose kernel pair is `P`, and the groupoid on `Ū`
of which the given groupoid is the restriction. -/
private structure Division {S : Scheme.{u}} (G H : Stacks.Groupoids.GroupoidScheme S)
    (i : Stacks.Groupoids.GroupoidScheme.Hom H G) (hobj : H.objects = G.objects) where
  /-- The affine quotient of the object scheme. -/
  quotient : Over S
  quotient_affine : IsAffine quotient.left
  /-- The quotient morphism. -/
  projection : G.objects ⟶ quotient
  projection_finiteLocallyFree : Stacks.Morphisms.IsFiniteLocallyFree projection.left
  projection_surjective : Surjective projection.left
  /-- The subgroupoid is the kernel pair of the quotient map. -/
  subgroupoid_isPullback :
    IsPullback (H.target ≫ eqToHom hobj) (H.source ≫ eqToHom hobj)
      projection projection
  /-- The descended groupoid on the quotient. -/
  descended : Stacks.Groupoids.GroupoidScheme S
  descended_objects : descended.objects = quotient
  /-- The original groupoid maps to the descended groupoid. -/
  descend : Stacks.Groupoids.GroupoidScheme.Hom G descended
  descend_objects : descend.mapObjects = projection ≫ eqToHom descended_objects.symm
  /-- The original groupoid is the restriction of the descended groupoid. -/
  descend_fullyFaithful : ∀ T : Over S, Nonempty (descend.evaluation T).FullyFaithful

/-- **Stacks 04S4**, read as a `Division`: a finite locally free open subgroupoid of a
groupoid scheme with affine object scheme and separated, locally quasi-finite pre-relation can
be divided out. -/
private theorem exists_division {S : Scheme.{u}} (G H : Stacks.Groupoids.GroupoidScheme S)
    (i : Stacks.Groupoids.GroupoidScheme.Hom H G) (hobj : H.objects = G.objects)
    (hiobj : i.mapObjects = eqToHom hobj)
    [Stacks.Morphisms.IsFiniteLocallyFree H.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree H.target.left]
    [Mono (prod.lift H.target H.source)]
    [IsAffine G.objects.left]
    [IsSeparated (prod.lift G.target G.source).left]
    [LocallyOfFiniteType (prod.lift G.target G.source).left]
    [LocallyQuasiFinite (prod.lift G.target G.source).left] :
    Nonempty (Division G H i hobj) := by
  have : IsIso i.mapObjects := by rw [hiobj]; infer_instance
  have : Mono (AlgebraicGeometry.groupoidPreRelation H) :=
    inferInstanceAs (Mono (prod.lift H.target H.source))
  have : IsSeparated (AlgebraicGeometry.groupoidPreRelation G).left :=
    inferInstanceAs (IsSeparated (prod.lift G.target G.source).left)
  have : LocallyOfFiniteType (AlgebraicGeometry.groupoidPreRelation G).left :=
    inferInstanceAs (LocallyOfFiniteType (prod.lift G.target G.source).left)
  have : LocallyQuasiFinite (AlgebraicGeometry.groupoidPreRelation G).left :=
    inferInstanceAs (LocallyQuasiFinite (prod.lift G.target G.source).left)
  obtain ⟨Q, hQ, K, he, F, hF, -, hFF⟩ :=
    AlgebraicGeometry.exists_finiteFlatQuotient_isAffine_of_mono_groupoidPreRelation G H i
  have hinv : inv i.mapObjects = eqToHom hobj.symm :=
    IsIso.inv_eq_of_hom_inv_id (by rw [hiobj]; simp)
  have := Q.finiteLocallyFree
  have := Q.surjective
  have : IsIso (inv i.mapObjects).left := (Over.forget S).map_isIso (inv i.mapObjects)
  have : Stacks.Morphisms.IsFiniteLocallyFree (inv i.mapObjects).left :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  refine ⟨{ quotient := Q.space
            quotient_affine := hQ
            projection := inv i.mapObjects ≫ Q.quotientMap
            projection_finiteLocallyFree := ?_
            projection_surjective := ?_
            subgroupoid_isPullback := ?_
            descended := K
            descended_objects := he
            descend := F
            descend_objects := hF
            descend_fullyFaithful := hFF }⟩
  · rw [Over.comp_left]
    exact Stacks.Morphisms.isFiniteLocallyFree_comp _ _
  · rw [Over.comp_left]; infer_instance
  · refine IsPullback.of_iso Q.kernelPair (Iso.refl _) (eqToIso hobj) (eqToIso hobj) (Iso.refl _)
      ?_ ?_ ?_ ?_ <;> simp [hinv]

/-- Step (C) of Tag 04S6.  A division of a groupoid scheme by a finite locally free open
subgroupoid gives the affine-case interface: the quotient `Ū` of the object scheme is affine
and no larger than the object scheme, the descended groupoid has an open identity because the
subgroupoid is the kernel pair of `U ⟶ Ū`, so `Ū` is itself a surjective étale atlas of
`Ū/R̄`, and `U/R` is `Ū/R̄` because the original groupoid is the restriction of the descended
one along `U ⟶ Ū`. -/
private theorem exists_atlas_quotient_of_division
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {G H : Stacks.Groupoids.GroupoidScheme S} (i : Stacks.Groupoids.GroupoidScheme.Hom H G)
    (hobj : H.objects = G.objects) (hiobj : i.mapObjects = eqToHom hobj)
    (D : Division G H i hobj)
    (hU : site.Contains G.objects.left) [IsAffine G.objects.left]
    (hrel : IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation G).target
      (AlgebraicGeometry.groupoidPreRelation G).source)
    [IsOpenImmersion i.mapArrows.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left] :
    ∃ (W : AlgebraicGeometry.BigFppfOver site S hS)
      (a : yoneda.obj W ⟶
        (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
          (Over.post site.inclusion) (AlgebraicGeometry.groupoidPreRelation G)).obj),
      AlgebraicGeometry.IsAlgebraicSpace site S hS
          (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
            (Over.post site.inclusion) (AlgebraicGeometry.groupoidPreRelation G)).obj ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj W).size ≤
          G.objects.left.size := by
  classical
  have hdesc : D.descend.mapObjects =
      D.projection ≫ eqToHom D.descended_objects.symm := D.descend_objects
  have hprop : ∀ (P : MorphismProperty Scheme.{u}),
      P D.projection.left → P D.descend.mapObjects.left := by
    intro P hp
    rw [hdesc]
    exact property_comp_eqToHom P D.projection D.descended_objects.symm hp
  obtain ⟨hflat, hlfp, hfin⟩ :=
    flat_lfp_isFinite_of_isFiniteLocallyFree D.projection.left
      D.projection_finiteLocallyFree
  let : Flat D.descend.mapObjects.left := hprop (@Flat) hflat
  let : LocallyOfFinitePresentation D.descend.mapObjects.left :=
    hprop (@LocallyOfFinitePresentation) hlfp
  let : Surjective D.descend.mapObjects.left :=
    hprop (@Surjective) D.projection_surjective
  let : IsFinite D.descend.mapObjects.left := hprop (@IsFinite) hfin
  let : QuasiCompact D.descend.mapObjects.left := inferInstance
  have hbaraff : IsAffine D.descended.objects.left := by
    rw [D.descended_objects]
    exact D.quotient_affine
  let := hbaraff
  have hsize : D.descended.objects.left.size ≤ G.objects.left.size :=
    size_le_of_flat_surjective_affine D.descend.mapObjects.left
  have hUbar : site.Contains D.descended.objects.left := lt_of_le_of_lt hsize hU
  have hqt : i.mapArrows ≫ G.target = H.target ≫ eqToHom hobj := by
    rw [i.map_target, hiobj]
  have hqs : i.mapArrows ≫ G.source = H.source ≫ eqToHom hobj := by
    rw [i.map_source, hiobj]
  have hbot : IsPullback D.projection (𝟙 G.objects)
      (eqToHom D.descended_objects.symm : D.quotient ⟶ D.descended.objects)
      (D.projection ≫ eqToHom D.descended_objects.symm) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hp : IsPullback (H.target ≫ eqToHom hobj) (H.source ≫ eqToHom hobj)
      D.descend.mapObjects D.descend.mapObjects := by
    rw [hdesc]
    simpa only [Category.comp_id] using D.subgroupoid_isPullback.paste_vert hbot
  obtain ⟨W, a, halg, hasurj, haetale, hWsize⟩ :=
    exists_atlas_quotient_of_open_kernelPair site S hS hUbar hrel D.descend
      D.descend_fullyFaithful i.mapArrows (H.target ≫ eqToHom hobj)
      (H.source ≫ eqToHom hobj) hqt hqs hp
  let Uobj : AlgebraicGeometry.BigFppfOver site S hS :=
    Over.mk (ObjectProperty.homMk G.objects.hom : site.obj hU ⟶ site.obj hS)
  let Ubar : AlgebraicGeometry.BigFppfOver site S hS :=
    Over.mk (ObjectProperty.homMk D.descended.objects.hom :
      site.obj hUbar ⟶ site.obj hS)
  let pg : Uobj ⟶ Ubar :=
    Over.homMk (ObjectProperty.homMk D.descend.mapObjects.left)
      (by ext; exact D.descend.mapObjects.w)
  have hpgsurj : Surjective ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map pg) := by
    show Surjective D.descend.mapObjects.left
    infer_instance
  have hpgflat : Flat ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map pg) := by
    show Flat D.descend.mapObjects.left
    infer_instance
  have hpglfp : LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map pg) := by
    show LocallyOfFinitePresentation D.descend.mapObjects.left
    infer_instance
  have hg : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology site S hS)
      ((Over.post site.inclusion).op.whiskerLeft
        (yoneda.map D.descend.mapObjects)) :=
    locallySurjective_postWhisker_of_flat site S hS pg hpgsurj hpgflat hpglfp
  obtain ⟨a', halg', hasurj', haetale'⟩ :=
    exists_atlas_quotient_restrict_of_quotient site S hS
      (AlgebraicGeometry.groupoidPreRelation D.descended) D.descend.mapObjects
      (AlgebraicGeometry.groupoidPreRelation_isPreEquivalenceRelation D.descended)
      hg a hasurj haetale halg
  obtain ⟨a'', halg'', hasurj'', haetale''⟩ :=
    exists_atlas_quotient_of_quotientPresheaf_iso site S hS
      (AlgebraicGeometry.groupoidPreRelation G)
      (AlgebraicGeometry.PreRelation.restrict (AlgebraicGeometry.groupoidPreRelation D.descended)
        D.descend.mapObjects)
      (quotientPresheafIsoRestrictOfFullyFaithful
        (Over.post (X := site.obj hS) site.inclusion) D.descend
        D.descend_fullyFaithful)
      a' hasurj' haetale' halg'
  exact ⟨W, a'', halg'', hasurj'', haetale'', hWsize.trans hsize⟩

/-- If the arrow map of a morphism of groupoid schemes is a monomorphism and the relation
map of the target groupoid is a monomorphism, then so is the relation map of the source
groupoid. -/
private theorem mono_prodLift_of_mono_mapArrows
    {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
    (i : Stacks.Groupoids.GroupoidScheme.Hom H G) [Mono i.mapArrows]
    [Mono (prod.lift G.target G.source)] :
    Mono (prod.lift H.target H.source) := by
  have key : i.mapArrows ≫ prod.lift G.target G.source =
      prod.lift H.target H.source ≫ prod.map i.mapObjects i.mapObjects := by
    rw [prod.comp_lift, i.map_target, i.map_source, prod.lift_map]
  constructor
  intro T a b hab
  apply (cancel_mono i.mapArrows).mp
  apply (cancel_mono (prod.lift G.target G.source)).mp
  calc (a ≫ i.mapArrows) ≫ prod.lift G.target G.source
      = (a ≫ prod.lift H.target H.source) ≫ prod.map i.mapObjects i.mapObjects := by
        rw [Category.assoc, key, ← Category.assoc]
    _ = (b ≫ prod.lift H.target H.source) ≫ prod.map i.mapObjects i.mapObjects := by
        rw [hab]
    _ = (b ≫ i.mapArrows) ≫ prod.lift G.target G.source := by
        rw [Category.assoc, ← key, ← Category.assoc]

/-- A groupoid scheme mapping fully faithfully to a groupoid scheme whose relation map is a
monomorphism has monomorphic relation map.  In particular the restriction of an equivalence
relation along any morphism is again an equivalence relation. -/
private theorem mono_prodLift_of_fullyFaithful_groupoid
    {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
    (i : Stacks.Groupoids.GroupoidScheme.Hom G H)
    (hi : ∀ T, Nonempty (i.evaluation T).FullyFaithful)
    [Mono (prod.lift H.target H.source)] :
    Mono (prod.lift G.target G.source) := by
  have hpb := isPullback_of_fullyFaithful_groupoid i hi
  constructor
  intro T a b hab
  refine hpb.hom_ext hab ?_
  apply (cancel_mono (prod.lift H.target H.source)).mp
  calc (a ≫ i.mapArrows) ≫ prod.lift H.target H.source
      = (a ≫ prod.lift G.target G.source) ≫ prod.map i.mapObjects i.mapObjects := by
        rw [Category.assoc, ← hpb.w, ← Category.assoc]
    _ = (b ≫ prod.lift G.target G.source) ≫ prod.map i.mapObjects i.mapObjects := by
        rw [hab]
    _ = (b ≫ i.mapArrows) ≫ prod.lift H.target H.source := by
        rw [Category.assoc, hpb.w, ← Category.assoc]

/-- **Stacks 04S0**, in the shape the bootstrap argument consumes. In Situation 04RV with `U`
affine and `s, t` flat and locally of finite presentation, there are an affine scheme `U'`, an
étale morphism `g : U' ⟶ U` and a point `u'` over `u` such that the restriction `R|_{U'}` has an

open subgroupoid whose source and target are finite locally free. -/
private theorem exists_affineEtale_finiteLocallyFree_subgroupoid
    (D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u})
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    [Flat D.groupoid.source.left] [Flat D.groupoid.target.left]
    [LocallyOfFinitePresentation D.groupoid.source.left]
    [LocallyOfFinitePresentation D.groupoid.target.left]
    [IsAffine D.groupoid.objects.left] :
    ∃ (U' : Over D.S) (g : U' ⟶ D.groupoid.objects) (u' : U'.left),
      IsAffine U'.left ∧ Etale g.left ∧ g.left u' = D.u ∧
      ∃ (H : Stacks.Groupoids.GroupoidScheme D.S)
        (i : Stacks.Groupoids.GroupoidScheme.Hom H
          (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid g).groupoid)
        (hobj : H.objects =
          (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid g).groupoid.objects),
        i.mapObjects = eqToHom hobj ∧ Mono i.mapArrows ∧
        IsOpenImmersion i.mapArrows.left ∧
        Stacks.Morphisms.IsFiniteLocallyFree H.source.left ∧
        Stacks.Morphisms.IsFiniteLocallyFree H.target.left := by
  obtain ⟨U', gp, R', U'', j, u'', -, -, haff, -, het, hbase, -, -, hqs⟩ :=
    Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation
      D C hS hU hR hP hK
  let g : U'' ⟶ D.groupoid.objects := j ≫ R'.hom.mapObjects
  let Rg := AlgebraicGeometry.GroupoidScheme.restrict D.groupoid g
  obtain ⟨P⟩ := hqs Rg
  have : Etale g.left := het
  have : MorphismProperty.RespectsIso (@Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Flat Rg.groupoid.source.left :=
    property_restrict_source (@Flat.{u}) D.groupoid g inferInstance inferInstance
  have : LocallyOfFinitePresentation Rg.groupoid.source.left :=
    property_restrict_source (@LocallyOfFinitePresentation.{u}) D.groupoid g inferInstance
      inferInstance
  have : Flat Rg.groupoid.target.left :=
    property_restrict_target (@Flat.{u}) D.groupoid g inferInstance inferInstance
  have : LocallyOfFinitePresentation Rg.groupoid.target.left :=
    property_restrict_target (@LocallyOfFinitePresentation.{u}) D.groupoid g inferInstance
      inferInstance
  have hopen := P.arrows_open
  have hsf := P.source_finite
  have htf := P.target_finite
  have hio : IsIso P.inclusion.mapObjects := by rw [P.mapObjects_eq]; infer_instance
  have hio' : IsIso P.inclusion.mapObjects.left := (Over.forget _).map_isIso _
  have hsrc : P.subgroupoid.source.left = P.inclusion.mapArrows.left ≫
      Rg.groupoid.source.left ≫ inv P.inclusion.mapObjects.left := by
    rw [← Category.assoc, P.inclusion.map_source_left, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have htgt : P.subgroupoid.target.left = P.inclusion.mapArrows.left ≫
      Rg.groupoid.target.left ≫ inv P.inclusion.mapObjects.left := by
    rw [← Category.assoc, P.inclusion.map_target_left, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  refine ⟨U'', g, u'', haff, het, hbase, P.subgroupoid, P.inclusion, P.objects_eq,
    P.mapObjects_eq, ?_, hopen, ?_, ?_⟩
  · have : Mono P.inclusion.mapArrows.left := inferInstance
    exact (Over.forget _).mono_of_mono_map this
  · rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
    refine ⟨hsf, ?_, ?_⟩ <;> rw [hsrc] <;> infer_instance
  · rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
    refine ⟨htf, ?_, ?_⟩ <;> rw [htgt] <;> infer_instance

/-- Step (B) of Tag 04S6, the geometric input: in the quasi-splitting situation with affine
object scheme, monomorphic relation map, and flat, locally finitely presented and locally
quasi-finite source, the chosen point has an affine étale neighborhood over which the
restricted groupoid scheme can be divided by a finite locally free open subgroupoid in the
sense of Tag 04S4. -/
private theorem exists_affineEtale_division
    (D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u})
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    [Flat D.groupoid.source.left] [Flat D.groupoid.target.left]
    [LocallyOfFinitePresentation D.groupoid.source.left]
    [LocallyOfFinitePresentation D.groupoid.target.left]
    [LocallyQuasiFinite D.groupoid.source.left]
    [IsAffine D.groupoid.objects.left]
    [Mono (AlgebraicGeometry.groupoidPreRelation D.groupoid)] :
    ∃ (U' : Over D.S) (g : U' ⟶ D.groupoid.objects) (u' : U'.left),
      IsAffine U'.left ∧ Etale g.left ∧ g.left u' = D.u ∧
      ∃ (H : Stacks.Groupoids.GroupoidScheme D.S)
        (i : Stacks.Groupoids.GroupoidScheme.Hom H
          (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid g).groupoid)
        (hobj : H.objects =
          (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid g).groupoid.objects),
        i.mapObjects = eqToHom hobj ∧ IsOpenImmersion i.mapArrows.left ∧
          Nonempty (Division
            (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid g).groupoid H i hobj) := by
  classical
  obtain ⟨U', g, u', haff, het, hpt, H, i, hobj, hiobj, hmono, hopen, hsflf, htflf⟩ :=
    exists_affineEtale_finiteLocallyFree_subgroupoid D C hS hU hR hP hK
  refine ⟨U', g, u', haff, het, hpt, H, i, hobj, hiobj, hopen, ?_⟩
  let R' := AlgebraicGeometry.GroupoidScheme.restrict D.groupoid g
  let : Etale g.left := het
  let : IsAffine U'.left := haff
  let : LocallyQuasiFinite g.left := inferInstance
  have hobjaff : IsAffine R'.groupoid.objects.left := by
    rw [R'.objects_eq]
    exact haff
  let := hobjaff
  have : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hlfpR : LocallyOfFinitePresentation R'.groupoid.source.left :=
    property_restrict_source (@LocallyOfFinitePresentation.{u}) D.groupoid g
      inferInstance inferInstance
  have hlqfR : LocallyQuasiFinite R'.groupoid.source.left :=
    property_restrict_source (@LocallyQuasiFinite.{u}) D.groupoid g
      inferInstance inferInstance
  let := hlfpR
  let := hlqfR
  have hmonoR : Mono (AlgebraicGeometry.groupoidPreRelation R'.groupoid) :=
    mono_prodLift_of_fullyFaithful_groupoid R'.hom R'.evaluation_fullyFaithful
  let := hmonoR
  have hsepR : R'.groupoid.arrows.left.IsSeparated :=
    isSeparated_relation_of_isAffine (AlgebraicGeometry.groupoidPreRelation R'.groupoid)
  let : IsSeparated (prod.lift R'.groupoid.target R'.groupoid.source).left :=
    isSeparated_prodLift_of_isSeparated R'.groupoid.target R'.groupoid.source hsepR
  let : LocallyOfFiniteType (prod.lift R'.groupoid.target R'.groupoid.source).left :=
    locallyOfFiniteType_prodLift R'.groupoid.target R'.groupoid.source
  let : LocallyQuasiFinite (prod.lift R'.groupoid.target R'.groupoid.source).left :=
    locallyQuasiFinite_prodLift R'.groupoid.target R'.groupoid.source
  let := hmono
  let := hsflf
  let := htflf
  let : Mono (prod.lift H.target H.source) := mono_prodLift_of_mono_mapArrows i
  exact exists_division R'.groupoid H i hobj hiobj


/-! ### Subcanonicity -/

private theorem bigFppf_subcanonical (B : AlgebraicGeometry.BigFppfSite.{u}) :
    B.topology.Subcanonical := by
  let Q := Scheme.fppfPrecoverage.comap B.inclusion
  have htop : B.topology ≤ Q.toGrothendieck := by
    apply Precoverage.toGrothendieck_mono
    intro X R hR
    rcases hR with ⟨E, hR, hE⟩
    subst R
    exact B.isFppfCovering_of_isCovering hE
  let : B.inclusion.IsContinuous Q.toGrothendieck Scheme.fppfTopology :=
    Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
      (F := B.inclusion) (J := Q) (K := Scheme.fppfPrecoverage) (by
        intro X R hR
        exact hR)
  let : Q.toGrothendieck.Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful B.inclusion
      Q.toGrothendieck Scheme.fppfTopology
  exact GrothendieckTopology.Subcanonical.of_le htop

private theorem bigFppfOver_subcanonical (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (AlgebraicGeometry.BigFppfOver.topology B S hS).Subcanonical := by
  let : B.topology.Subcanonical := bigFppf_subcanonical B
  infer_instance

/-! ### Open covers of the base site are covering sieves -/

private theorem open_cover_mem_bigFppf_topology
    (B : AlgebraicGeometry.BigFppfSite.{u}) (X : B.Schemes)
    {I : Type u} (Y : I → B.Schemes) (f : ∀ i, Y i ⟶ X)
    (hopen : ∀ i, IsOpenImmersion (B.inclusion.map (f i)))
    (hsurj : ∀ x : B.inclusion.obj X, ∃ i y, (B.inclusion.map (f i)).base y = x) :
    Sieve.generate (Presieve.ofArrows Y f) ∈ B.topology X := by
  let E₀ : PreZeroHypercover.{u} X := ⟨I, Y, f⟩
  let E : Covering.{u + 1, u, u + 1} B.Schemes :=
    ⟨X, E₀.reindex Equiv.ulift.{u + 1, u}⟩
  have hz : (E.2.map B.inclusion).presieve₀ ∈
      Scheme.zariskiPrecoverage (B.inclusion.obj E.1) := by
    rw [Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)]
    refine ⟨?_, fun i => hopen i.down⟩
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨ULift.up i, y, hy⟩
  have hfp : AlgebraicGeometry.IsFppfCovering E := by
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      ← PreZeroHypercover.presieve₀_map]
    exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hz
  simpa only [E, PreZeroHypercover.presieve₀_reindex] using
    generate_presieve₀_mem_bigFppf_topology B E hfp

/-- A jointly surjective family of flat, locally finitely presented morphisms of the big fppf
site generates a covering sieve.  This is the flat analogue of
`open_cover_mem_bigFppf_topology`. -/
private theorem flat_cover_mem_bigFppf_topology
    (B : AlgebraicGeometry.BigFppfSite.{u}) (X : B.Schemes)
    {I : Type u} (Y : I → B.Schemes) (f : ∀ i, Y i ⟶ X)
    (hflat : ∀ i, Flat (B.inclusion.map (f i)))
    (hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (f i)))
    (hsurj : ∀ x : B.inclusion.obj X, ∃ i y, (B.inclusion.map (f i)).base y = x) :
    Sieve.generate (Presieve.ofArrows Y f) ∈ B.topology X := by
  let E₀ : PreZeroHypercover.{u} X := ⟨I, Y, f⟩
  let E : Covering.{u + 1, u, u + 1} B.Schemes :=
    ⟨X, E₀.reindex Equiv.ulift.{u + 1, u}⟩
  have hfp : AlgebraicGeometry.IsFppfCovering E := by
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      ← PreZeroHypercover.presieve₀_map]
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun i => ⟨hflat i.down, hlfp i.down⟩⟩
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨ULift.up i, y, hy⟩
  simpa only [E, PreZeroHypercover.presieve₀_reindex] using
    generate_presieve₀_mem_bigFppf_topology B E hfp

/-- The over-site form of `flat_cover_mem_bigFppf_topology`. -/
private theorem flat_cover_mem_bigFppfOver_topology
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} {U : AlgebraicGeometry.BigFppfOver B S hS}
    (Ui : I → AlgebraicGeometry.BigFppfOver B S hS) (gi : ∀ i, Ui i ⟶ U)
    (hflat : ∀ i, Flat ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (gi i)))
    (hlfp : ∀ i, LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (gi i)))
    (hsurj : ∀ x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U, ∃ i y,
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (gi i)).base y = x) :
    Sieve.ofArrows Ui gi ∈ AlgebraicGeometry.BigFppfOver.topology B S hS U := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact flat_cover_mem_bigFppf_topology B U.left (fun i => (Ui i).left)
    (fun i => (gi i).left) hflat hlfp hsurj

/-! ### The empty object -/

private theorem contains_empty (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) : B.Contains (∅ : Scheme.{u}) :=
  Scheme.size_lt_of_isOpenImmersion (AlgebraicGeometry.emptyIsInitial.to S) hS

private noncomputable def emptyObj (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) : AlgebraicGeometry.BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (AlgebraicGeometry.emptyIsInitial.to S) :
    B.obj (contains_empty B S hS) ⟶ B.obj hS)

/-- An object of the big fppf over-site with empty underlying scheme is initial. -/
private noncomputable def isInitialOfIsEmpty (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (Y : AlgebraicGeometry.BigFppfOver B S hS)
    (hY : IsEmpty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Y)) : IsInitial Y := by
  haveI : IsEmpty (↥(Y.left.obj)) := hY
  have hinit : IsInitial Y.left.obj := AlgebraicGeometry.isInitialOfIsEmpty
  refine IsInitial.ofUniqueHom
    (fun Z => Over.homMk (ObjectProperty.homMk (hinit.to Z.left.obj)) ?_) ?_
  · apply ObjectProperty.hom_ext
    exact hinit.hom_ext _ _
  · intro Z m
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hinit.hom_ext _ _

private theorem isEmpty_of_isInitial (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (Y : AlgebraicGeometry.BigFppfOver B S hS)
    (hY : IsInitial Y) : IsEmpty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Y) := by
  let k : Y ⟶ emptyObj B S hS := hY.to _
  have : IsEmpty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (emptyObj B S hS)) :=
    show IsEmpty (∅ : Scheme.{u}) from inferInstance
  exact ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map k).base.hom.1.isEmpty

private theorem bot_mem_topology_of_isEmpty (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (Y : AlgebraicGeometry.BigFppfOver B S hS)
    [hY : IsEmpty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Y)] :
    ⊥ ∈ (AlgebraicGeometry.BigFppfOver.topology B S hS) Y := by
  rw [GrothendieckTopology.mem_over_iff, map_bot]
  have h : Sieve.generate (Presieve.ofArrows (fun _ : PEmpty.{u + 1} => Y.left)
      (fun i => i.elim)) ∈ B.topology Y.left := by
    refine open_cover_mem_bigFppf_topology B Y.left _ _ (fun i => i.elim) ?_
    intro x
    exact (hY.false x).elim
  convert h using 1
  ext Z g
  simp only [Sieve.bot_apply, false_iff]
  rintro ⟨W, a, b, ⟨i⟩, -⟩
  exact i.elim

/-! ### The coproduct cofan of the over-site is sent to a coproduct of sheaves -/

private noncomputable def isColimit_yonedaSheaf_cofan
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} (W : I → AlgebraicGeometry.BigFppfOver B S hS)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (jV : ∀ i, W i ⟶ V)
    (hopen : ∀ i, IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (jV i)))
    (hsurj : ∀ x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V, ∃ i y,
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (jV i)).base y = x)
    (hdisj : ∀ {i j : I}, i ≠ j → ∀ {Z : AlgebraicGeometry.BigFppfOver B S hS}
      (a : Z ⟶ W i) (b : Z ⟶ W j), a ≫ jV i = b ≫ jV j →
      IsEmpty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Z))
    [(AlgebraicGeometry.BigFppfOver.topology B S hS).Subcanonical] :
    IsColimit (Cofan.mk ((AlgebraicGeometry.BigFppfOver.topology B S hS).yoneda.obj V)
      (fun i => (AlgebraicGeometry.BigFppfOver.topology B S hS).yoneda.map (jV i))) := by
  have hmono (i : I) : Mono (jV i) := by
    have : Mono ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (jV i)) := by
      let := hopen i
      infer_instance
    exact Functor.mono_of_mono_map (AlgebraicGeometry.BigFppfOver.toScheme B S hS) this
  letI : ∀ i, Mono ((Cofan.mk V jV).inj i) := hmono
  have hcov : Sieve.ofArrows W jV ∈ (AlgebraicGeometry.BigFppfOver.topology B S hS) V := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact open_cover_mem_bigFppf_topology B V.left (fun i => (W i).left)
      (fun i => (jV i).left) hopen hsurj
  exact GrothendieckTopology.isColimitCofanMkYoneda _ W (c := Cofan.mk V jV) hcov
    (fun Y hYi => by
      let := isEmpty_of_isInitial B S hS Y hYi
      exact bot_mem_topology_of_isEmpty B S hS Y)
    (fun {i j} hij Y a b hab => ⟨isInitialOfIsEmpty B S hS Y (hdisj hij a b hab)⟩)

/-- Every morphism from a representable presheaf to an algebraic space is representable. -/
private theorem relativelyRepresentable_of_isAlgebraicSpace
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    {V : AlgebraicGeometry.BigFppfOver B S hS} (b : yoneda.obj V ⟶ F) :
    yoneda.relativelyRepresentable b :=
  Functor.relativelyRepresentable.of_diag hF.diagonal_representable b

/-- A property that is Zariski-local at the source may be checked on the members of an open
cover of the source of a representable morphism of presheaves. -/
private theorem presheaf_property_of_openCover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : AlgebraicGeometry.BigFppfOver B S hS} (b : yoneda.obj V ⟶ F)
    (hrep : yoneda.relativelyRepresentable b)
    {I : Type u} (W : I → AlgebraicGeometry.BigFppfOver B S hS) (jV : ∀ i, W i ⟶ V)
    (hopen : ∀ i, IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (jV i)))
    (hcov : ⨆ i, ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (jV i)).opensRange = ⊤)
    (hb : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) (yoneda.map (jV i) ≫ b)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) b := by
  let T₀ := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : (MorphismProperty.inverseImage P T₀).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative_of_snd hrep
  intro T g
  let Z := hrep.pullback g
  let f₀ : Z ⟶ V := yoneda.preimage (hrep.fst g)
  have hf₀ : yoneda.map f₀ = hrep.fst g := yoneda.map_preimage _
  have hpb : IsPullback (yoneda.map f₀) (yoneda.map (hrep.snd g)) b g := by
    rw [hf₀]; exact hrep.isPullback g
  have hpbC (i : I) : IsPullback (CategoryTheory.Limits.pullback.fst f₀ (jV i))
      (CategoryTheory.Limits.pullback.snd f₀ (jV i)) f₀ (jV i) :=
    IsPullback.of_hasPullback _ _
  have hopen' (i : I) :
      IsOpenImmersion (T₀.map (CategoryTheory.Limits.pullback.fst f₀ (jV i))) :=
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsOpenImmersion.{u}) ((hpbC i).flip.map T₀) (hopen i))
  have hmem : Presieve.ofArrows (fun i => T₀.obj (CategoryTheory.Limits.pullback f₀ (jV i)))
      (fun i => T₀.map (CategoryTheory.Limits.pullback.fst f₀ (jV i))) ∈
      Scheme.zariskiPrecoverage (T₀.obj Z) := by
    rw [Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)]
    refine ⟨?_, fun i => hopen' i⟩
    intro x
    have hx : (T₀.map f₀).base x ∈ (⊤ : (T₀.obj V).Opens) := trivial
    rw [← hcov] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨y, hy⟩ := hi
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := T₀.map f₀) (g := T₀.map (jV i)) x y hy.symm
    refine ⟨i, ((hpbC i).map T₀).isoPullback.inv.base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ((hpbC i).map T₀).isoPullback_inv_fst]
    exact hz
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hmem ?_
  rintro U k ⟨i⟩
  have hsq : IsPullback (yoneda.map (CategoryTheory.Limits.pullback.snd f₀ (jV i)))
      (yoneda.map (CategoryTheory.Limits.pullback.fst f₀ (jV i) ≫ hrep.snd g))
      (yoneda.map (jV i) ≫ b) g := by
    rw [Functor.map_comp]
    exact ((hpbC i).flip.map yoneda).paste_vert hpb
  have h2 : P ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (CategoryTheory.Limits.pullback.fst f₀ (jV i) ≫ hrep.snd g)) :=
    (hb i).property g (yoneda.map (CategoryTheory.Limits.pullback.snd f₀ (jV i)))
      (CategoryTheory.Limits.pullback.fst f₀ (jV i) ≫ hrep.snd g) hsq
  rw [Functor.map_comp] at h2
  exact h2

/-- A section of a sheaf coproduct locally factors through one of the summands. -/
private lemma coproduct_locally_factors
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {I : Type*} (Fi : I → Sheaf J (Type u)) (G : Sheaf J (Type u))
    (ι : ∀ i, Fi i ⟶ G) (hc : IsColimit (Cofan.mk G ι))
    {T : C} (x : G.obj.obj (Opposite.op T)) :
    ∃ (R : Sieve T), R ∈ J T ∧ ∀ ⦃V : C⦄ (f : V ⟶ T), R f →
      ∃ (i : I) (y : (Fi i).obj.obj (Opposite.op V)),
        (ι i).hom.app (Opposite.op V) y = G.obj.map f.op x := by
  classical
  let A : Subfunctor G.obj := ⨆ i, Subfunctor.range (ι i).hom
  let Ash := A.sheafify J
  let Z : Sheaf J (Type u) := ⟨Ash.toFunctor,
    (isSheaf_iff_isSheaf_of_type J _).mpr
      (A.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type J _).mp G.property))⟩
  let inc : Z ⟶ G := ⟨Ash.ι⟩
  have hle (i : I) : Subfunctor.range (ι i).hom ≤ Ash :=
    le_trans (le_iSup (fun j => Subfunctor.range (ι j).hom) i) (A.le_sheafify J)
  let f (i : I) : Fi i ⟶ Z :=
    ⟨Subfunctor.lift (ι i).hom (hle i)⟩
  have hfac (i : I) : f i ≫ inc = ι i := by
    apply Sheaf.hom_ext
    ext V y
    rfl
  let d : G ⟶ Z := Cofan.IsColimit.desc hc (Cofan.mk Z f).inj
  have hdinc : d ≫ inc = 𝟙 G := by
    apply Cofan.IsColimit.hom_ext hc
    intro i
    calc
      (Cofan.mk G ι).inj i ≫ d ≫ inc = f i ≫ inc := by
        have hd : (Cofan.mk G ι).inj i ≫ d = f i := by
          show (Cofan.mk G ι).inj i ≫
            Cofan.IsColimit.desc hc (Cofan.mk Z f).inj = f i
          exact Cofan.IsColimit.fac hc (Cofan.mk Z f).inj i
        rw [← Category.assoc, hd]
      _ = ι i := hfac i
      _ = (Cofan.mk G ι).inj i ≫ 𝟙 G := by simp
  have hx : x ∈ Ash.obj (Opposite.op T) := by
    have hval : inc.hom.app (Opposite.op T) (d.hom.app (Opposite.op T) x) = x := by
      have := congrArg (fun φ : G ⟶ G => φ.hom.app (Opposite.op T) x) hdinc
      simpa using this
    rw [← hval]
    exact (d.hom.app (Opposite.op T) x).property
  change A.sieveOfSection x ∈ J T at hx
  refine ⟨A.sieveOfSection x, hx, ?_⟩
  intro V f hf
  change G.obj.map f.op x ∈ A.obj (Opposite.op V) at hf
  rw [Subfunctor.iSup_obj] at hf
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hf
  simp only [Subfunctor.range_obj, Set.mem_range] at hi
  exact ⟨i, hi⟩

/-- A point of an object of the big fppf over-site is in the image of a member of any
covering sieve. -/
private theorem exists_preimage_of_covering_sieve
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : AlgebraicGeometry.BigFppfOver B S hS} {R : Sieve T}
    (hR : R ∈ AlgebraicGeometry.BigFppfOver.topology B S hS T)
    (x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T) :
    ∃ (V : AlgebraicGeometry.BigFppfOver B S hS) (a : V ⟶ T), R a ∧
      x ∈ Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a) := by
  have hbase : (Sieve.overEquiv T) R ∈ B.topology T.left :=
    (B.topology.mem_over_iff R).1 hR
  obtain ⟨E, hE, hle⟩ := exists_covering_refining_sieve B hbase
  have hEfp : (E.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T.left) := by
    simpa [AlgebraicGeometry.IsFppfCovering, PreZeroHypercover.presieve₀_map] using
      B.isFppfCovering_of_isCovering hE
  let : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    unfold Scheme.fppfPrecoverage
    infer_instance
  obtain ⟨V, a, ⟨i⟩, hx⟩ := Scheme.JointlySurjective.exists_eq _ hEfp x
  let W : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (E.f i ≫ T.hom)
  let b : W ⟶ T := Over.homMk (E.f i)
  exact ⟨W, b, (Sieve.overEquiv_iff R (E.f i)).1 (hle _ _ ⟨i⟩), hx⟩

/-- A representable, locally surjective morphism of presheaves is surjective after every
representable base change. -/
private theorem surjective_of_representable_locallySurjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hrep : yoneda.relativelyRepresentable f)
    (hloc : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) f) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f := by
  let := hloc
  let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative_of_snd (P := P) hrep
  intro T g
  constructor
  intro x
  obtain ⟨V, a, ha, v, hv⟩ := exists_preimage_of_covering_sieve B S hS
    (Presheaf.imageSieve_mem (AlgebraicGeometry.BigFppfOver.topology B S hS) f (yonedaEquiv g)) x
  obtain ⟨z, hz⟩ := ha
  let b : yoneda.obj V ⟶ F := yonedaEquiv.symm z
  have hb : b ≫ f = yoneda.map a ≫ g := by
    apply yonedaEquiv.injective
    simpa [b, yonedaEquiv_comp, yonedaEquiv_naturality] using hz
  refine ⟨((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (hrep.lift b a hb)) v, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hrep.lift_snd]
  exact hv

/-- The atlas glued from atlases of the summands of a sheaf coproduct mapping locally
surjectively onto a sheaf is itself locally surjective. -/
private theorem isLocallySurjective_glued
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u}
    {Q : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)}
    (Fi : I → Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u))
    (G : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fi i ⟶ G) (hcG : IsColimit (Cofan.mk G ι)) (g : G ⟶ Q)
    (hgloc : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) g.hom)
    {W : I → AlgebraicGeometry.BigFppfOver B S hS} {V : AlgebraicGeometry.BigFppfOver B S hS}
    (jV : ∀ i, W i ⟶ V)
    (a : ∀ i, yoneda.obj (W i) ⟶ (Fi i).obj)
    (haloc : ∀ i, Presheaf.IsLocallySurjective
      (AlgebraicGeometry.BigFppfOver.topology B S hS) (a i))
    (b : yoneda.obj V ⟶ Q.obj)
    (hfac : ∀ i, yoneda.map (jV i) ≫ b = a i ≫ (ι i).hom ≫ g.hom) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) b := by
  classical
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let := hgloc
  refine ⟨?_⟩
  intro T x
  refine J.transitive (Presheaf.imageSieve_mem J g.hom x) _ ?_
  rintro T₁ f₁ ⟨y, hy⟩
  obtain ⟨R₂, hR₂, hR₂'⟩ := coproduct_locally_factors Fi G ι hcG y
  refine J.transitive hR₂ _ ?_
  intro T₂ f₂ hf₂
  obtain ⟨i, z, hz⟩ := hR₂' f₂ hf₂
  let := haloc i
  refine J.transitive (Presheaf.imageSieve_mem J (a i) z) _ ?_
  rintro T₃ f₃ ⟨w, hw⟩
  refine J.covering_of_eq_top ?_
  rw [← Sieve.id_mem_iff_eq_top]
  refine ⟨(w ≫ jV i : T₃ ⟶ V), ?_⟩
  have hbw : b.app (Opposite.op T₃) (w ≫ jV i) =
      g.hom.app (Opposite.op T₃) ((ι i).hom.app (Opposite.op T₃)
        (a i |>.app (Opposite.op T₃) w)) := by
    have := congrArg (fun φ => φ.app (Opposite.op T₃) w) (hfac i)
    simpa using this
  rw [Category.id_comp, hbw, hw]
  have h1 : (ι i).hom.app (Opposite.op T₃) ((Fi i).obj.map f₃.op z) =
      G.obj.map f₃.op ((ι i).hom.app (Opposite.op T₂) z) :=
    NatTrans.naturality_apply (ι i).hom f₃.op z
  rw [h1, hz]
  have h2 : G.obj.map f₃.op (G.obj.map f₂.op y) = G.obj.map (f₃ ≫ f₂).op y := by
    rw [op_comp, G.obj.map_comp]; rfl
  rw [h2]
  have h3 : g.hom.app (Opposite.op T₃) (G.obj.map (f₃ ≫ f₂).op y) =
      Q.obj.map (f₃ ≫ f₂).op (g.hom.app (Opposite.op T₁) y) :=
    NatTrans.naturality_apply g.hom (f₃ ≫ f₂).op y
  rw [h3, hy, ← ConcreteCategory.comp_apply, ← Q.obj.map_comp, ← op_comp]


/-! ### (B3): the glued atlas -/

/-- **Step (B3) of Tag 04S6.**  Let `Q` be an algebraic space covered by a family of
subsheaves `Fi` whose sheaf coproduct `G` maps locally surjectively onto `Q` by a map that
is étale after every representable base change.  Given a surjective étale atlas `W i` of
each `Fi` and an object `V` of the site exhibited as the disjoint union of the `W i` by

open immersions, `V` is a surjective étale atlas of `Q`. -/
private theorem exists_atlas_of_openSubfunctorCover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u}
    (Q : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u))
    (hQ : AlgebraicGeometry.IsAlgebraicSpace B S hS Q.obj)
    (Fi : I → Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u))
    (G : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fi i ⟶ G) (hcG : IsColimit (Cofan.mk G ι))
    (g : G ⟶ Q)
    (hgloc : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) g.hom)
    (hιet : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) ((ι i).hom ≫ g.hom))
    (W : I → AlgebraicGeometry.BigFppfOver B S hS)
    (a : ∀ i, yoneda.obj (W i) ⟶ (Fi i).obj)
    (hasurj : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) (a i))
    (haet : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) (a i))
    (V : AlgebraicGeometry.BigFppfOver B S hS) (jV : ∀ i, W i ⟶ V)
    (hopen : ∀ i, IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (jV i)))
    (hcovpt : ∀ x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj V, ∃ i y,
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (jV i)).base y = x)
    (hcovop : ⨆ i, ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (jV i)).opensRange = ⊤)
    (hdisj : ∀ {i j : I}, i ≠ j → ∀ {Z : AlgebraicGeometry.BigFppfOver B S hS}
      (p : Z ⟶ W i) (q : Z ⟶ W j), p ≫ jV i = q ≫ jV j →
      IsEmpty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Z)) :
    ∃ b : yoneda.obj V ⟶ Q.obj,
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) b ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) b := by
  let : (AlgebraicGeometry.BigFppfOver.topology B S hS).Subcanonical :=
    bigFppfOver_subcanonical B S hS
  let : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).IsStableUnderComposition := by
    refine ⟨fun {X Y Z} f g hf hg => ?_⟩
    show Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (f ≫ g))
    rw [Functor.map_comp]
    have : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f) := hf
    have : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) := hg
    infer_instance
  have hc := isColimit_yonedaSheaf_cofan B S hS W V jV hopen hcovpt hdisj
  let β : ∀ i, (AlgebraicGeometry.BigFppfOver.topology B S hS).yoneda.obj (W i) ⟶ Q :=
    fun i => ⟨a i ≫ (ι i).hom ≫ g.hom⟩
  let bS : (AlgebraicGeometry.BigFppfOver.topology B S hS).yoneda.obj V ⟶ Q :=
    Cofan.IsColimit.desc hc β
  have hfac (i : I) : yoneda.map (jV i) ≫ bS.hom = a i ≫ (ι i).hom ≫ g.hom :=
    congrArg (fun k : (AlgebraicGeometry.BigFppfOver.topology B S hS).yoneda.obj (W i) ⟶ Q => k.hom)
      (Cofan.IsColimit.fac hc β i)
  have hrep := relativelyRepresentable_of_isAlgebraicSpace B S hS hQ bS.hom
  have hEt : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) bS.hom := by
    let : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
    refine presheaf_property_of_openCover B S hS (@Etale.{u}) bS.hom hrep W jV hopen
      hcovop ?_
    intro i
    rw [hfac i]
    exact MorphismProperty.comp_mem _ _ _ (haet i) (hιet i)
  have hloc : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) bS.hom :=
    isLocallySurjective_glued B S hS Fi G ι hcG g hgloc jV a
      (fun i => locallySurjective_of_surjectiveEtale B S hS (a i) (hasurj i) (haet i))
      bS.hom hfac
  exact ⟨bS.hom,
    surjective_of_representable_locallySurjective B S hS bS.hom hrep hloc, hEt⟩

/-- A covering family `gᵢ : Uᵢ ⟶ U` of the big fppf site induces a locally surjective map
from the coproduct of the representable presheaves `yoneda.obj Uᵢ` to `yoneda.obj U`. -/
private theorem isLocallySurjective_sigmaDesc_yoneda_of_mem
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {U : AlgebraicGeometry.BigFppfOver site S hS} {I : Type u}
    (Ui : I → AlgebraicGeometry.BigFppfOver site S hS) (gi : ∀ i, Ui i ⟶ U)
    (hcov : Sieve.ofArrows Ui gi ∈ AlgebraicGeometry.BigFppfOver.topology site S hS U) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology site S hS)
      (Sigma.desc (fun i ↦ yoneda.map (gi i))) := by
  let C := AlgebraicGeometry.BigFppfOver site S hS
  let J := AlgebraicGeometry.BigFppfOver.topology site S hS
  let c := coproductIsCoproduct (fun i : I ↦ shrinkYoneda.{u}.obj (Ui i))
  have hs : Presheaf.IsLocallySurjective J
      (Cofan.IsColimit.desc c (fun i ↦ shrinkYoneda.{u}.map (gi i))) :=
    (J.ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map
      (fun i ↦ gi i) c).mp hcov
  let e := Sigma.mapIso (fun i ↦ (shrinkYonedaIsoYoneda.{u} (C := C)).app (Ui i))
  have he : e.hom ≫ Sigma.desc (fun i ↦ yoneda.map (gi i)) =
      Sigma.desc (fun i ↦ shrinkYoneda.{u}.map (gi i)) ≫
        ((shrinkYonedaIsoYoneda.{u} (C := C)).app U).hom := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_mapIso_hom]
    calc
      _ = ((shrinkYonedaIsoYoneda.{u} (C := C)).app (Ui i)).hom ≫
          yoneda.map (gi i) := by rw [Category.assoc, Sigma.ι_desc]
      _ = shrinkYoneda.{u}.map (gi i) ≫
          ((shrinkYonedaIsoYoneda.{u} (C := C)).app U).hom :=
        ((shrinkYonedaIsoYoneda.{u} (C := C)).hom.naturality (gi i)).symm
      _ = (Sigma.ι (fun i ↦ shrinkYoneda.{u}.obj (Ui i)) i ≫
          Sigma.desc (fun i ↦ shrinkYoneda.{u}.map (gi i))) ≫
          ((shrinkYonedaIsoYoneda.{u} (C := C)).app U).hom := by
        rw [Sigma.ι_desc]
  let : Presheaf.IsLocallySurjective J
      (Sigma.desc (fun i ↦ shrinkYoneda.{u}.map (gi i))) := by
    rw [← cofan_desc_eq_sigma_desc]
    exact hs
  have hcomp : Presheaf.IsLocallySurjective J
      (e.hom ≫ Sigma.desc (fun i ↦ yoneda.map (gi i))) := by
    rw [he]
    exact Presheaf.isLocallySurjective_comp J
      (Sigma.desc (fun i ↦ shrinkYoneda.{u}.map (gi i))) _
  let : Presheaf.IsLocallySurjective J
      (e.hom ≫ Sigma.desc (fun i ↦ yoneda.map (gi i))) := hcomp
  rw [← cofan_desc_eq_sigma_desc]
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J he

/-- The cover-and-glue step of condition (2) of Tag 04S6.  If a pre-relation on an object
scheme `U` of the site restricts, along a covering family of flat, locally finitely
presented morphisms `gᵢ : Uᵢ ⟶ U`, to pre-relations whose quotient sheaves are algebraic
spaces admitting surjective étale atlases `Wᵢ` whose coproduct `V` lies in the site and is
exhibited as their disjoint union by open immersions, then the quotient sheaf of the
pre-relation is itself an algebraic space and `V` is a surjective étale atlas of it. -/
private theorem exists_atlas_quotient_of_siteCover
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {R : Over S} {U : AlgebraicGeometry.BigFppfOver site S hS}
    (j : Stacks.Groupoids.PreRelation R ((Over.post site.inclusion).obj U))
    [IsEquivalenceRelation j.target j.source]
    [Flat j.source.left] [Flat j.target.left]
    [LocallyOfFinitePresentation j.source.left]
    [LocallyOfFinitePresentation j.target.left]
    {I : Type u} (Ui : I → AlgebraicGeometry.BigFppfOver site S hS)
    (gi : ∀ i, Ui i ⟶ U)
    (hgflat : ∀ i, Flat ((Over.post site.inclusion).map (gi i)).left)
    (hglfp : ∀ i, LocallyOfFinitePresentation
      ((Over.post site.inclusion).map (gi i)).left)
    (hcov : Sieve.ofArrows Ui gi ∈ AlgebraicGeometry.BigFppfOver.topology site S hS U)
    (hFi : ∀ i, AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion)
        (AlgebraicGeometry.PreRelation.restrict j
          ((Over.post site.inclusion).map (gi i)))).obj)
    (Wi : I → AlgebraicGeometry.BigFppfOver site S hS)
    (ai : ∀ i, yoneda.obj (Wi i) ⟶
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion)
        (AlgebraicGeometry.PreRelation.restrict j
          ((Over.post site.inclusion).map (gi i)))).obj)
    (hasurj : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) (ai i))
    (haetale : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) (ai i))
    (V : AlgebraicGeometry.BigFppfOver site S hS) (jV : ∀ i, Wi i ⟶ V)
    (hV : IsColimit (Cofan.mk V jV))
    (hVopen : ∀ i, IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map (jV i)))
    (hVpt : ∀ x : (AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj V, ∃ i y,
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map (jV i)).base y = x)
    (hVrange : ⨆ i, ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map (jV i)).opensRange = ⊤)
    (hVdisj : ∀ {i i' : I}, i ≠ i' → ∀ {Z : AlgebraicGeometry.BigFppfOver site S hS}
      (p : Z ⟶ Wi i) (q : Z ⟶ Wi i'), p ≫ jV i = q ≫ jV i' →
      IsEmpty ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj Z)) :
    ∃ b : yoneda.obj V ⟶
        (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
          (Over.post site.inclusion) j).obj,
      AlgebraicGeometry.IsAlgebraicSpace site S hS
          (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
            (Over.post site.inclusion) j).obj ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) b ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) b := by
  classical
  let C := AlgebraicGeometry.BigFppfOver site S hS
  let J := AlgebraicGeometry.BigFppfOver.topology site S hS
  let F : C ⥤ Over S := Over.post (X := site.obj hS) site.inclusion
  let : F.Full := by
    show (Over.post (X := site.obj hS) site.inclusion).Full
    infer_instance
  let : F.Faithful := by
    show (Over.post (X := site.obj hS) site.inclusion).Faithful
    infer_instance
  have hEquiv : IsEquivalenceRelation j.target j.source := inferInstance
  obtain ⟨er⟩ := hEquiv.nonempty_equivalenceRelation
  have hsourceSurj : Surjective j.source.left := by
    have h : er.r.left ≫ j.source.left = 𝟙 _ := by
      rw [← Over.comp_left, er.reflexivity₂]
      rfl
    let : Surjective (er.r.left ≫ j.source.left) := by
      rw [h]; infer_instance
    exact Surjective.of_comp (f := er.r.left) (g := j.source.left)
  have htargetSurj : Surjective j.target.left := by
    have h : er.r.left ≫ j.target.left = 𝟙 _ := by
      rw [← Over.comp_left, er.reflexivity₁]
      rfl
    let : Surjective (er.r.left ≫ j.target.left) := by
      rw [h]; infer_instance
    exact Surjective.of_comp (f := er.r.left) (g := j.target.left)
  let Q := Stacks.Groupoids.quotientSheaf J F j
  let ji (i : I) : Stacks.Groupoids.PreRelation
      (AlgebraicGeometry.PreRelation.restriction j (F.map (gi i))) (F.obj (Ui i)) :=
    AlgebraicGeometry.PreRelation.restrict j (F.map (gi i))
  let Fi (i : I) : Sheaf J (Type u) := Stacks.Groupoids.quotientSheaf J F (ji i)
  let ιF (i : I) : Fi i ⟶ Q :=
    Stacks.Groupoids.restrictQuotientSheafMap J F j (F.map (gi i))
  have hopen (i : I) : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) (ιF i).hom := by
    let : IsEquivalenceRelation j.target j.source := hEquiv
    exact AlgebraicGeometry.Space.isOpenImmersion_restrictedQuotientMap site hS j (F.map (gi i))
      hsourceSurj htargetSurj inferInstance inferInstance inferInstance
      inferInstance (hgflat i) (hglfp i)
  let pUi (i : I) : yoneda.obj (Ui i) ⟶ (Fi i).obj :=
    yonedaEquiv.symm ((Stacks.Groupoids.toQuotientSheaf J F (ji i)).app
      (Opposite.op (Ui i)) (𝟙 (F.obj (Ui i))))
  let : HasColimitsOfShape (Discrete I) (Cᵒᵖ ⥤ Type u) := inferInstance
  let Fcop : Discrete I ⥤ Sheaf J (Type u) := Discrete.functor Fi
  let Ecop : Cocone (Fcop ⋙ sheafToPresheaf J (Type u)) :=
    colimit.cocone (Fcop ⋙ sheafToPresheaf J (Type u))
  let G : Sheaf J (Type u) :=
    (CategoryTheory.Sheaf.sheafifyCocone (J := J) (D := Type u)
      (F := Fcop) Ecop).pt
  let ι (i : I) : Fi i ⟶ G :=
    (CategoryTheory.Sheaf.sheafifyCocone (J := J) (D := Type u)
      (F := Fcop) Ecop).ι.app (Discrete.mk i)
  have hcG : IsColimit (Cofan.mk G ι) := by
    show IsColimit (CategoryTheory.Sheaf.sheafifyCocone
      (J := J) (D := Type u) (F := Fcop) Ecop)
    exact CategoryTheory.Sheaf.isColimitSheafifyCocone (F := Fcop) Ecop
      (colimit.isColimit (Fcop ⋙ sheafToPresheaf J (Type u)))
  have hGalg : AlgebraicGeometry.IsAlgebraicSpace site S hS G.obj :=
    AlgebraicGeometry.isAlgebraicSpace_coproduct site S hS (fun i ↦ (Fi i).obj)
      hFi G ι hcG Wi ai hasurj haetale V jV hV
  let q : yoneda.obj U ⟶ Q.obj :=
    (yonedaEquiv (F := Stacks.Groupoids.points F (F.obj U))).symm (𝟙 (F.obj U)) ≫
      Stacks.Groupoids.toQuotientSheaf J F j
  let g : G ⟶ Q := Cofan.IsColimit.desc hcG ιF
  have hq : Presheaf.IsLocallySurjective J q := by
    let e := pointsYonedaIso F U
    have he0 : (yonedaEquiv (F := Stacks.Groupoids.points F (F.obj U))).symm
        (𝟙 (F.obj U)) = e.inv := by
      apply (yonedaEquiv (F := Stacks.Groupoids.points F (F.obj U))).injective
      simp [e, pointsYonedaIso, Stacks.Groupoids.points,
        Functor.FullyFaithful.homEquiv, Functor.FullyFaithful.ofFullyFaithful,
        yonedaEquiv]
    have he : q = e.inv ≫ Stacks.Groupoids.toQuotientSheaf J F j := by
      show (yonedaEquiv (F := Stacks.Groupoids.points F (F.obj U))).symm
          (𝟙 (F.obj U)) ≫ Stacks.Groupoids.toQuotientSheaf J F j =
        e.inv ≫ Stacks.Groupoids.toQuotientSheaf J F j
      rw [he0]
    rw [he]
    let : Presheaf.IsLocallySurjective J
        (Stacks.Groupoids.toQuotientSheaf J F j) := quotientPoint_locallySurjective J F j
    exact Presheaf.isLocallySurjective_comp J e.inv
      (Stacks.Groupoids.toQuotientSheaf J F j)
  have hqfac (i : I) : pUi i ≫ (ιF i).hom = yoneda.map (gi i) ≫ q := by
    apply (yonedaEquiv (F := Q.obj)).injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simp only [pUi, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    have hpoint := Stacks.Groupoids.toQuotientSheaf_comp_quotientSheafMap J F
      (ji i) j (pullback.snd (prod.map (F.map (gi i)) (F.map (gi i))) j)
      (F.map (gi i)) (by
        show pullback.snd (prod.map (F.map (gi i)) (F.map (gi i))) j ≫
            j ≫ prod.snd =
          pullback.fst (prod.map (F.map (gi i)) (F.map (gi i))) j ≫
            prod.snd ≫ F.map (gi i)
        rw [← Category.assoc, ← pullback.condition]
        rw [Category.assoc, prod.map_snd, ← Category.assoc]) (by
        show pullback.snd (prod.map (F.map (gi i)) (F.map (gi i))) j ≫
            j ≫ prod.fst =
          pullback.fst (prod.map (F.map (gi i)) (F.map (gi i))) j ≫
            prod.fst ≫ F.map (gi i)
        rw [← Category.assoc, ← pullback.condition]
        rw [Category.assoc, prod.map_fst, ← Category.assoc])
    have hpoint' := congrArg
      (fun f => f.app (Opposite.op (Ui i)) (𝟙 (F.obj (Ui i)))) hpoint
    have heval :
        ((yonedaEquiv (F := Stacks.Groupoids.points F (F.obj U)).symm
          (𝟙 (F.obj U))).app (Opposite.op (Ui i))) (gi i) =
          F.map (gi i) := by
      rfl
    have hqval : q.app (Opposite.op (Ui i)) (gi i) =
        (Stacks.Groupoids.toQuotientSheaf J F j).app (Opposite.op (Ui i))
          (F.map (gi i)) := by
      dsimp [q]
      show (Stacks.Groupoids.toQuotientSheaf J F j).app (Opposite.op (Ui i))
        ((yonedaEquiv (F := Stacks.Groupoids.points F (F.obj U)).symm
          (𝟙 (F.obj U))).app (Opposite.op (Ui i)) (gi i)) = _
      rw [heval]
      rfl
    have hmapid :
        ((F.op.whiskerLeft (yoneda.map (F.map (gi i)))).app
          (Opposite.op (Ui i))) (𝟙 (F.obj (Ui i))) = F.map (gi i) := by
      simp
    rw [hqval]
    simpa only [NatTrans.comp_app, pUi, ιF,
      Stacks.Groupoids.restrictQuotientSheafMap, Equiv.apply_symm_apply,
      types_comp_apply, hmapid, Stacks.Groupoids.points] using hpoint'
  let α : (∐ fun i : I ↦ yoneda.obj (Ui i)) ⟶ G.obj :=
    Sigma.desc (fun i ↦ pUi i ≫ (ι i).hom)
  have hfac : α ≫ g.hom =
      Sigma.desc (fun i ↦ yoneda.map (gi i)) ≫ q := by
    apply Sigma.hom_ext
    intro i
    dsimp [α]
    have hι : (ι i).hom ≫ g.hom = (ιF i).hom :=
      congrArg (fun f : Fi i ⟶ Q => f.hom) (Cofan.IsColimit.fac hcG ιF i)
    calc
      (Sigma.ι (fun i ↦ yoneda.obj (Ui i)) i ≫
          Sigma.desc (fun i ↦ pUi i ≫ (ι i).hom)) ≫ g.hom =
        (pUi i ≫ (ι i).hom) ≫ g.hom := by rw [Sigma.ι_desc]
      _ = pUi i ≫ (ιF i).hom := by rw [Category.assoc, hι]
      _ = yoneda.map (gi i) ≫ q := hqfac i
      _ = (Sigma.ι (fun i ↦ yoneda.obj (Ui i)) i ≫
          Sigma.desc (fun i ↦ yoneda.map (gi i))) ≫ q := by rw [Sigma.ι_desc]
  let : Presheaf.IsLocallySurjective J q := hq
  let : Presheaf.IsLocallySurjective J (Sigma.desc (fun i ↦ yoneda.map (gi i))) :=
    isLocallySurjective_sigmaDesc_yoneda_of_mem site S hS Ui gi hcov
  have hlocal : Presheaf.IsLocallySurjective J (α ≫ g.hom) := by
    rw [hfac]
    exact Presheaf.isLocallySurjective_comp J _ _
  let : Presheaf.IsLocallySurjective J (α ≫ g.hom) := hlocal
  have hg : Presheaf.IsLocallySurjective J g.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  have hopen' (i : I) : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) ((ι i).hom ≫ g.hom) := by
    have hι : (ι i).hom ≫ g.hom = (ιF i).hom :=
      congrArg (fun f : Fi i ⟶ Q => f.hom) (Cofan.IsColimit.fac hcG ιF i)
    rw [hι]
    exact hopen i
  have hQ : AlgebraicGeometry.IsAlgebraicSpace site S hS Q.obj :=
    AlgebraicGeometry.isAlgebraicSpace_of_open_cover site S hS Q.obj Q.property
      I Fi hFi G ι hcG g.hom hopen' hg hGalg
  have hle : (MorphismProperty.inverseImage (@IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (AlgebraicGeometry.BigFppfOver.toScheme site S hS)) ≤
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme site S hS)) := by
    intro A A' k hk
    have : IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map k) := hk
    exact inferInstanceAs (Etale _)
  obtain ⟨b, hbsurj, hbet⟩ := exists_atlas_of_openSubfunctorCover site S hS Q hQ Fi G ι
    hcG g hg (fun i => MorphismProperty.relative_monotone hle _ (hopen' i))
    Wi ai hasurj haetale V jV hVopen hVpt hVrange hVdisj
  exact ⟨b, hQ, hbsurj, hbet⟩

/-- The disjoint union of a family of atlases of the restricted quotients, along a covering
family of flat, locally finitely presented morphisms `gᵢ : Uᵢ ⟶ U`, lies in the site and is a
surjective étale atlas of the quotient sheaf of the whole pre-relation, of no greater size
than the object scheme. -/
private theorem exists_atlas_quotient_of_coveringAtlases
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {R : Over S} {U : AlgebraicGeometry.BigFppfOver site S hS}
    (j : Stacks.Groupoids.PreRelation R ((Over.post site.inclusion).obj U))
    [IsEquivalenceRelation j.target j.source]
    [Flat j.source.left] [Flat j.target.left]
    [LocallyOfFinitePresentation j.source.left]
    [LocallyOfFinitePresentation j.target.left]
    {I : Type u} (Ui : I → AlgebraicGeometry.BigFppfOver site S hS)
    (gi : ∀ i, Ui i ⟶ U)
    (hgflat : ∀ i, Flat ((Over.post site.inclusion).map (gi i)).left)
    (hglfp : ∀ i, LocallyOfFinitePresentation
      ((Over.post site.inclusion).map (gi i)).left)
    (hcov : Sieve.ofArrows Ui gi ∈ AlgebraicGeometry.BigFppfOver.topology site S hS U)
    (hFi : ∀ i, AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion)
        (AlgebraicGeometry.PreRelation.restrict j
          ((Over.post site.inclusion).map (gi i)))).obj)
    (Wi : I → AlgebraicGeometry.BigFppfOver site S hS)
    (ai : ∀ i, yoneda.obj (Wi i) ⟶
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion)
        (AlgebraicGeometry.PreRelation.restrict j
          ((Over.post site.inclusion).map (gi i)))).obj)
    (hasurj : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) (ai i))
    (haetale : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) (ai i))
    (hI : Cardinal.mk I ≤ ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U).size)
    (hsizeW : ∀ i, ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj (Wi i)).size ≤
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U).size) :
    ∃ (W : AlgebraicGeometry.BigFppfOver site S hS)
      (a : yoneda.obj W ⟶
        (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
          (Over.post site.inclusion) j).obj),
      AlgebraicGeometry.IsAlgebraicSpace site S hS
          (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
            (Over.post site.inclusion) j).obj ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj W).size ≤
          ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U).size := by
  classical
  let C := AlgebraicGeometry.BigFppfOver site S hS
  let J := AlgebraicGeometry.BigFppfOver.topology site S hS
  let F : C ⥤ Over S := Over.post (X := site.obj hS) site.inclusion
  let X : Scheme.{u} := (AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U
  -- the coproduct of the atlases lies in the site
  let Y (i : I) : Scheme.{u} := (AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj (Wi i)
  have hVle : (∐ Y).size ≤ X.size :=
    schemeSize_coproduct_le Y X.size X.aleph0_le_size hI hsizeW
  have hVsize : (∐ Y).size < site.cutoff := hVle.trans_lt U.left.property
  let hVObj : site.Contains (∐ Y) := hVsize
  let Vbase : site.obj hVObj ⟶ site.obj hS :=
    site.inclusion.preimage (show site.inclusion.obj (site.obj hVObj) ⟶
      site.inclusion.obj (site.obj hS) from Sigma.desc (fun i ↦
        site.inclusion.map (Wi i).hom))
  let V : C := Over.mk Vbase
  let baseι (i : I) : (Wi i).left ⟶ site.obj hVObj :=
    site.inclusion.preimage (show site.inclusion.obj (Wi i).left ⟶
      site.inclusion.obj (site.obj hVObj) from Sigma.ι Y i)
  let jV (i : I) : Wi i ⟶ V := Over.homMk (baseι i) (by
    apply site.inclusion.map_injective
    have hmap : site.inclusion.map (baseι i ≫ Vbase) =
        site.inclusion.map (Wi i).hom := by
      rw [Functor.map_comp, site.inclusion.map_preimage, site.inclusion.map_preimage]
      simp
    exact hmap)
  let cV : Cofan (fun i ↦ Wi i) := Cofan.mk V jV
  let cSite : Cofan (fun i : I ↦ (Wi i).left) := Cofan.mk (site.obj hVObj) baseι
  have hcSite : IsColimit cSite := by
    apply isColimitOfReflects site.inclusion
    apply (Cofan.isColimitMapCoconeEquiv site.inclusion _ cSite).2
    let d : Cofan Y := Cofan.mk (site.inclusion.obj (site.obj hVObj))
      (fun i ↦ site.inclusion.map (baseι i))
    let c : Cofan Y := Cofan.mk (∐ Y) (Sigma.ι Y)
    have he : d ≅ c := Cofan.ext (Iso.refl _) (fun i ↦ by
      show site.inclusion.map (baseι i) = Sigma.ι Y i
      simp only [baseι, site.inclusion.map_preimage])
    exact IsColimit.ofIsoColimit (coproductIsCoproduct Y) he.symm
  have hcV : IsColimit cV :=
    isColimitOfReflects (Over.forget (site.obj hS))
      ((Cofan.isColimitMapCoconeEquiv (Over.forget (site.obj hS)) _ cV).symm (by
        show IsColimit cSite
        exact hcSite))
  have hjVmap (i : I) : (AlgebraicGeometry.BigFppfOver.toScheme site S hS).map (jV i) =
      Sigma.ι Y i := by
    show site.inclusion.map (baseι i) = Sigma.ι Y i
    simp only [baseι, site.inclusion.map_preimage]
  have hVopen (i : I) : IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map (jV i)) := by
    rw [hjVmap i]
    exact (AlgebraicGeometry.sigmaOpenCover Y).map_prop i
  have hVpt : ∀ x : (AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj V, ∃ i y,
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map (jV i)).base y = x := by
    intro x
    have hx : ∃ (i : I) (y : Y i), (Sigma.ι Y i).base y = (x : (∐ Y : Scheme.{u})) := by
      obtain ⟨y, hy⟩ := (AlgebraicGeometry.sigmaOpenCover Y).covers
        (show (∐ Y : Scheme.{u}) from x)
      exact ⟨_, y, hy⟩
    obtain ⟨i, y, hy⟩ := hx
    refine ⟨i, y, ?_⟩
    exact (congrArg (fun f : Y i ⟶ (∐ Y) => f.base y) (hjVmap i)).trans hy
  have hVrange : ⨆ i, ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map
      (jV i)).opensRange = ⊤ := by
    have h : ∀ i, ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map (jV i)).opensRange =
        (Sigma.ι Y i).opensRange := by
      intro i
      refine TopologicalSpace.Opens.ext ?_
      rw [Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange]
      exact congrArg (fun f : Y i ⟶ (∐ Y) => Set.range f.base) (hjVmap i)
    simp only [h]
    exact (AlgebraicGeometry.sigmaOpenCover Y).iSup_opensRange
  have hVdisj : ∀ {i i' : I}, i ≠ i' → ∀ {Z : AlgebraicGeometry.BigFppfOver site S hS}
      (p : Z ⟶ Wi i) (q : Z ⟶ Wi i'), p ≫ jV i = q ≫ jV i' →
      IsEmpty ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj Z) := by
    intro i i' hii' Z p q hpq
    refine isEmpty_of_commSq_sigmaι_of_ne (g := Y) (i := i) (j := i')
      (a := (AlgebraicGeometry.BigFppfOver.toScheme site S hS).map p)
      (b := (AlgebraicGeometry.BigFppfOver.toScheme site S hS).map q) ⟨?_⟩ hii'
    rw [← hjVmap i, ← hjVmap i', ← Functor.map_comp, ← Functor.map_comp, hpq]
  obtain ⟨b, hQ, hbsurj, hbet⟩ := exists_atlas_quotient_of_siteCover site S hS j Ui gi
    hgflat hglfp hcov hFi Wi ai hasurj haetale V jV hcV hVopen hVpt hVrange hVdisj
  exact ⟨V, b, hQ, hbsurj, hbet, hVle⟩

/-- The division step of Tag 04S6 at a point, stated for a groupoid scheme rather than for a
quasi-splitting situation: every point of the affine object scheme has an affine étale
neighbourhood over which the restricted groupoid can be divided by a finite locally free open
subgroupoid. -/
private theorem exists_affineEtale_division_of_groupoid
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains S)
    (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left)
    [IsAffine G.objects.left] [Mono (AlgebraicGeometry.groupoidPreRelation G)]
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left]
    [LocallyQuasiFinite G.source.left]
    (u : G.objects.left) (hK : C.Contains (Spec (G.objects.left.residueField u))) :
    ∃ (U' : Over S) (g : U' ⟶ G.objects) (u' : U'.left),
      IsAffine U'.left ∧ Etale g.left ∧ g.left u' = u ∧
      ∃ (H : Stacks.Groupoids.GroupoidScheme S)
        (i : Stacks.Groupoids.GroupoidScheme.Hom H
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid)
        (hobj : H.objects =
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.objects),
        i.mapObjects = eqToHom hobj ∧ IsOpenImmersion i.mapArrows.left ∧
          Nonempty (Division
            (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid H i hobj) := by
  let D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u} := quasiSplittingSituation G u
  let : Flat D.groupoid.source.left := inferInstanceAs (Flat G.source.left)
  let : Flat D.groupoid.target.left := inferInstanceAs (Flat G.target.left)
  let : LocallyOfFinitePresentation D.groupoid.source.left :=
    inferInstanceAs (LocallyOfFinitePresentation G.source.left)
  let : LocallyOfFinitePresentation D.groupoid.target.left :=
    inferInstanceAs (LocallyOfFinitePresentation G.target.left)
  let : LocallyQuasiFinite D.groupoid.source.left :=
    inferInstanceAs (LocallyQuasiFinite G.source.left)
  let : IsAffine D.groupoid.objects.left := inferInstanceAs (IsAffine G.objects.left)
  let : Mono (AlgebraicGeometry.groupoidPreRelation D.groupoid) :=
    inferInstanceAs (Mono (AlgebraicGeometry.groupoidPreRelation G))
  obtain ⟨U', g, u', haff, het, hpt, H, i, hobj, hiobj, hopen, hDiv⟩ :=
    exists_affineEtale_division D C hS hU hR hP hK
  exact ⟨U', g, u', haff, het, hpt, H, i, hobj, hiobj, hopen, hDiv⟩

/-- Precomposing with the canonical isomorphism attached to an equality of objects of an over
category does not change the image of a morphism. -/
private theorem exists_preimage_eqToHom_comp {S : Scheme.{u}} {X X' Y : Over S}
    (h : X = X') (f : X' ⟶ Y) {y : Y.left} (hy : ∃ x, f.left.base x = y) :
    ∃ x, (eqToHom h ≫ f).left.base x = y := by
  subst h
  simpa only [eqToHom_refl, Category.id_comp] using hy

/-- **Step (B) of Tag 04S6 at one point.**  A point of the affine object scheme of a flat,
locally finitely presented, locally quasi-finite equivalence relation has an étale
neighbourhood `Uᵢ ⟶ U` in the site, no larger than `U`, over which the restricted
pre-relation has an algebraic quotient sheaf carrying a surjective étale atlas of no greater
size than `Uᵢ`. -/
private theorem exists_atlas_quotient_affine_at_point
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    (U : AlgebraicGeometry.BigFppfOver site S hS)
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U)]
    {R : Over S}
    (j : Stacks.Groupoids.PreRelation R ((Over.post site.inclusion).obj U))
    [IsEquivalenceRelation j.target j.source]
    [Flat j.source.left] [LocallyOfFinitePresentation j.source.left]
    [LocallyQuasiFinite j.source.left]
    [Flat j.target.left] [LocallyOfFinitePresentation j.target.left]
    [LocallyQuasiFinite j.target.left]
    (u : (AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U) :
    ∃ (Ui : AlgebraicGeometry.BigFppfOver site S hS) (gi : Ui ⟶ U),
      Etale ((Over.post site.inclusion).map gi).left ∧
      (∃ y, ((Over.post site.inclusion).map gi).left.base y = u) ∧
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj Ui).size ≤
        ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U).size ∧
      ∃ (W : AlgebraicGeometry.BigFppfOver site S hS)
        (a : yoneda.obj W ⟶
          (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
            (Over.post site.inclusion)
            (AlgebraicGeometry.PreRelation.restrict j
              ((Over.post site.inclusion).map gi))).obj),
        AlgebraicGeometry.IsAlgebraicSpace site S hS
            (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
              (Over.post site.inclusion)
              (AlgebraicGeometry.PreRelation.restrict j
                ((Over.post site.inclusion).map gi))).obj ∧
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Etale.{u} : MorphismProperty Scheme.{u})
            (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
          ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj W).size ≤
            ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj Ui).size := by
  classical
  let F : AlgebraicGeometry.BigFppfOver site S hS ⥤ Over S :=
    Over.post (X := site.obj hS) site.inclusion
  -- the groupoid scheme extending the equivalence relation `j`
  obtain ⟨H0, hH0, -⟩ := AlgebraicGeometry.existsUnique_groupoidScheme_of_isEquivalenceRelation j
  rcases H0 with ⟨objects, arrows, source, target, comp, identity, inverse,
    hsid, htid, hsinv, htinv, hsc, htc, li, ri, linv, rinv, assoc'⟩
  rcases hH0 with ⟨hob, har, hsrc, htgt⟩
  dsimp only at hob har
  subst hob har
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsrc htgt
  subst hsrc htgt
  let H : Stacks.Groupoids.GroupoidScheme S :=
    ⟨F.obj U, arrows, j.source, j.target, comp, identity, inverse,
      hsid, htid, hsinv, htinv, hsc, htc, li, ri, linv, rinv, assoc'⟩
  have hj : AlgebraicGeometry.groupoidPreRelation H = j :=
    prod.hom_ext (prod.lift_fst _ _) (prod.lift_snd _ _)
  obtain ⟨er⟩ := (inferInstance :
    IsEquivalenceRelation j.target j.source).nonempty_equivalenceRelation
  let : JointlyMono₂ j.target j.source := ⟨er.right_cancellation⟩
  let hmonoH : Mono (AlgebraicGeometry.groupoidPreRelation H) :=
    mono_prodLift_of_jointlyMono j.target j.source
  let := hmonoH
  let : IsAffine H.objects.left :=
    inferInstanceAs (IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U))
  let : Flat H.source.left := inferInstanceAs (Flat j.source.left)
  let : Flat H.target.left := inferInstanceAs (Flat j.target.left)
  let : LocallyOfFinitePresentation H.source.left :=
    inferInstanceAs (LocallyOfFinitePresentation j.source.left)
  let : LocallyOfFinitePresentation H.target.left :=
    inferInstanceAs (LocallyOfFinitePresentation j.target.left)
  let : LocallyQuasiFinite H.source.left :=
    inferInstanceAs (LocallyQuasiFinite j.source.left)
  -- the affine étale neighbourhood of `u` and the division over it
  have hUH : site.Contains H.objects.left := U.left.property
  have hrelH : IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation H).target
      (AlgebraicGeometry.groupoidPreRelation H).source := by
    rw [hj]; infer_instance
  have hRH : site.Contains H.arrows.left := groupoid_arrows_mem_site site H hUH hrelH
  have hPH : site.Contains (pullback H.source H.target).left :=
    (Scheme.size_congr (PreservesPullback.iso (Over.forget S) H.source H.target)).trans_lt
      (Scheme.size_pullback_lt _ _ hRH hRH)
  let u₀ : H.objects.left := u
  have hKH : site.Contains (Spec (H.objects.left.residueField u₀)) :=
    (Scheme.size_le_of_mono_quasiCompact
      (H.objects.left.fromSpecResidueField u₀)).trans_lt hUH
  obtain ⟨U', g, u', haff, het, hpt, H', i, hobj, hiobj, hopenArr, ⟨Dv⟩⟩ :=
    exists_affineEtale_division_of_groupoid H site hS hUH hRH hPH u₀ hKH
  let Gr := AlgebraicGeometry.GroupoidScheme.restrict H g
  let g₀ : Gr.groupoid.objects ⟶ H.objects := Gr.hom.mapObjects
  have hg₀ : g₀ = eqToHom Gr.objects_eq ≫ g := Gr.mapObjects_eq
  have hGraff : IsAffine Gr.groupoid.objects.left := by
    rwa [Gr.objects_eq]
  let := hGraff
  have hEt0 : Etale g₀.left := by
    rw [hg₀]
    exact property_eqToHom_comp (@Etale.{u}) Gr.objects_eq g het
  let := hEt0
  let : Flat g₀.left := (Etale.iff_flat_and_formallyUnramified.mp hEt0).1
  let : LocallyOfFinitePresentation g₀.left :=
    (Etale.iff_flat_and_formallyUnramified.mp hEt0).2.2
  have hpt0 : ∃ y, g₀.left.base y = u := by
    rw [hg₀]
    exact exists_preimage_eqToHom_comp Gr.objects_eq g ⟨u', hpt⟩
  have hGrsize : Gr.groupoid.objects.left.size ≤
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U).size := by
    have h1 : LocallyOfFiniteType g₀.left := inferInstance
    have h2 : CompactSpace (Gr.groupoid.objects.left : Scheme.{u}) := inferInstance
    exact @Scheme.size_le_of_locallyOfFiniteType _ _ g₀.left h1 h2
  have hGrcontains : site.Contains Gr.groupoid.objects.left :=
    hGrsize.trans_lt U.left.property
  -- the atlas of the quotient of the restricted groupoid
  let : JointlyMono₂ Gr.groupoid.target Gr.groupoid.source :=
    jointlyMono_of_mono_prodLift
      (mono_prodLift_of_fullyFaithful_groupoid Gr.hom Gr.evaluation_fullyFaithful)
  have hrelGr : IsEquivalenceRelation
      (AlgebraicGeometry.groupoidPreRelation Gr.groupoid).target
      (AlgebraicGeometry.groupoidPreRelation Gr.groupoid).source :=
    isEquivalenceRelation_of_jointlyMono_groupoid Gr.groupoid
  let := hopenArr
  let : Flat g.left := (Etale.iff_flat_and_formallyUnramified.mp het).1
  let : LocallyOfFinitePresentation g.left :=
    (Etale.iff_flat_and_formallyUnramified.mp het).2.2
  have : MorphismProperty.RespectsIso (@Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : Flat Gr.groupoid.source.left :=
    property_restrict_source (@Flat.{u}) H g inferInstance inferInstance
  let : LocallyOfFinitePresentation Gr.groupoid.source.left :=
    property_restrict_source (@LocallyOfFinitePresentation.{u}) H g inferInstance
      inferInstance
  obtain ⟨W, a, halg, hasurj, haet, hWsize⟩ :=
    exists_atlas_quotient_of_division site S hS i hobj hiobj Dv hGrcontains hrelGr
  -- transport the atlas to the restriction of `j`
  have hpre : Stacks.Groupoids.quotientPresheaf F
        (AlgebraicGeometry.PreRelation.restrict (AlgebraicGeometry.groupoidPreRelation H) g₀) =
      Stacks.Groupoids.quotientPresheaf F (AlgebraicGeometry.PreRelation.restrict j g₀) :=
    congrArg (fun k : Stacks.Groupoids.PreRelation arrows (F.obj U) =>
      Stacks.Groupoids.quotientPresheaf F (AlgebraicGeometry.PreRelation.restrict k g₀)) hj
  let e : Stacks.Groupoids.quotientPresheaf F (AlgebraicGeometry.PreRelation.restrict j g₀) ≅
      Stacks.Groupoids.quotientPresheaf F (AlgebraicGeometry.groupoidPreRelation Gr.groupoid) :=
    ((quotientPresheafIsoRestrictOfFullyFaithful F Gr.hom
      Gr.evaluation_fullyFaithful).trans (eqToIso hpre)).symm
  obtain ⟨a', halg', hasurj', haet'⟩ :=
    exists_atlas_quotient_of_quotientPresheaf_iso site S hS
      (AlgebraicGeometry.PreRelation.restrict j g₀)
      (AlgebraicGeometry.groupoidPreRelation Gr.groupoid) e a hasurj haet halg
  -- package `g₀` as a morphism of the site
  let Ui : AlgebraicGeometry.BigFppfOver site S hS :=
    Over.mk (ObjectProperty.homMk Gr.groupoid.objects.hom :
      site.obj hGrcontains ⟶ site.obj hS)
  let gi : Ui ⟶ U :=
    Over.homMk (ObjectProperty.homMk g₀.left) (by ext; exact g₀.w)
  exact ⟨Ui, gi, hEt0, hpt0, hGrsize, W, a', halg', hasurj', haet', hWsize⟩

/-- The affine case of condition (2) of Tag 04S6, together with an étale atlas of the
quotient whose size is bounded by that of the object scheme. -/
private theorem exists_atlas_quotient_affine
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    (U : AlgebraicGeometry.BigFppfOver site S hS)
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U)]
    {R : Over S}
    (j : Stacks.Groupoids.PreRelation R ((Over.post site.inclusion).obj U))
    [IsEquivalenceRelation j.target j.source]
    [Flat j.source.left] [LocallyOfFinitePresentation j.source.left]
    [LocallyQuasiFinite j.source.left]
    [Flat j.target.left] [LocallyOfFinitePresentation j.target.left]
    [LocallyQuasiFinite j.target.left] :
    ∃ (W : AlgebraicGeometry.BigFppfOver site S hS)
      (a : yoneda.obj W ⟶
        (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
          (Over.post site.inclusion) j).obj),
      AlgebraicGeometry.IsAlgebraicSpace site S hS
          (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
            (Over.post site.inclusion) j).obj ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj W).size ≤
          ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U).size := by
  classical
  let F : AlgebraicGeometry.BigFppfOver site S hS ⥤ Over S :=
    Over.post (X := site.obj hS) site.inclusion
  let X : Scheme.{u} := (AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U
  have key : ∀ u : X, ∃ (Ui : AlgebraicGeometry.BigFppfOver site S hS) (gi : Ui ⟶ U),
      Etale (F.map gi).left ∧ (∃ y, (F.map gi).left.base y = u) ∧
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj Ui).size ≤ X.size ∧
      ∃ (W : AlgebraicGeometry.BigFppfOver site S hS)
        (a : yoneda.obj W ⟶
          (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
            (Over.post site.inclusion)
            (AlgebraicGeometry.PreRelation.restrict j
              ((Over.post site.inclusion).map gi))).obj),
        AlgebraicGeometry.IsAlgebraicSpace site S hS
            (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
              (Over.post site.inclusion)
              (AlgebraicGeometry.PreRelation.restrict j
                ((Over.post site.inclusion).map gi))).obj ∧
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Etale.{u} : MorphismProperty Scheme.{u})
            (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
          ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj W).size ≤
            ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj Ui).size :=
    fun u => exists_atlas_quotient_affine_at_point site S hS U j u
  choose Ui gi hgiet hgipt hgisize Wi ai hFi hasurj haetale hsizeW using key
  -- each member of the family is flat, locally of finite presentation and open
  have hflat (u : X) : Flat (F.map (gi u)).left :=
    (Etale.iff_flat_and_formallyUnramified.mp (hgiet u)).1
  have hlfp (u : X) : LocallyOfFinitePresentation (F.map (gi u)).left :=
    (Etale.iff_flat_and_formallyUnramified.mp (hgiet u)).2.2
  have hopenmap (u : X) : IsOpenMap (F.map (gi u)).left.base := by
    let := hflat u
    let := hlfp u
    exact Scheme.Hom.isOpenMap (F.map (gi u)).left
  -- the images cover the quasi-compact `X`, so finitely many of them do
  have hcovset : (Set.univ : Set X) ⊆ ⋃ u : X, Set.range (F.map (gi u)).left.base := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hgipt x⟩
  obtain ⟨t, ht⟩ := (CompactSpace.isCompact_univ (X := X)).elim_finite_subcover
    (fun u : X => Set.range (F.map (gi u)).left.base)
    (fun u => (hopenmap u).isOpen_range) hcovset
  let I : Type u := {x : X // x ∈ t}
  have hsurj : ∀ x : X, ∃ (i : I) (y : _),
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map (gi i.1)).base y = x := by
    intro x
    obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    obtain ⟨y, hy⟩ := hxu
    exact ⟨⟨u, hu⟩, y, hy⟩
  have hcov : Sieve.ofArrows (fun i : I => Ui i.1) (fun i : I => gi i.1) ∈
      AlgebraicGeometry.BigFppfOver.topology site S hS U :=
    flat_cover_mem_bigFppfOver_topology site S hS (fun i : I => Ui i.1)
      (fun i : I => gi i.1) (fun i => hflat i.1) (fun i => hlfp i.1) hsurj
  have hI : Cardinal.mk I ≤ X.size :=
    Cardinal.mk_le_aleph0.trans X.aleph0_le_size
  have hsizeW' (i : I) :
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj (Wi i.1)).size ≤ X.size :=
    (hsizeW i.1).trans (hgisize i.1)
  exact exists_atlas_quotient_of_coveringAtlases site S hS j (fun i : I => Ui i.1)
    (fun i : I => gi i.1) (fun i => hflat i.1) (fun i => hlfp i.1) hcov
    (fun i => hFi i.1) (fun i => Wi i.1) (fun i => ai i.1) (fun i => hasurj i.1)
    (fun i => haetale i.1) hI hsizeW'

open Cardinal in
/-- Reduction of condition (2) of Tag 04S6 to the case of an affine object scheme: cover
the object scheme by its affine opens, restrict the relation to each, and glue. -/
private theorem isAlgebraicSpace_quotient_locallyQuasiFinite
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {R : Over S} {U : AlgebraicGeometry.BigFppfOver site S hS}
    (j : Stacks.Groupoids.PreRelation R ((Over.post site.inclusion).obj U))
    [IsEquivalenceRelation j.target j.source]
    [Flat j.source.left] [LocallyOfFinitePresentation j.source.left]
    [LocallyQuasiFinite j.source.left]
    [Flat j.target.left] [LocallyOfFinitePresentation j.target.left]
    [LocallyQuasiFinite j.target.left] :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) j).obj := by
  classical
  let C := AlgebraicGeometry.BigFppfOver site S hS
  let J := AlgebraicGeometry.BigFppfOver.topology site S hS
  let F : C ⥤ Over S := Over.post (X := site.obj hS) site.inclusion
  let X : Scheme.{u} := (AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj U
  let I := X.affineOpens
  let hUi (i : I) : site.Contains (i.1 : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι U.left.property
  let fUi (i : I) : site.obj (hUi i) ⟶ U.left :=
    site.inclusion.preimage (show
      site.inclusion.obj (site.obj (hUi i)) ⟶ site.inclusion.obj U.left from i.1.ι)
  let Ui (i : I) : C := Over.mk (fUi i ≫ U.hom)
  let gi (i : I) : Ui i ⟶ U := Over.homMk (fUi i) (by simp [Ui])
  have hgiOpen (i : I) : IsOpenImmersion (F.map (gi i)).left := by
    show IsOpenImmersion (site.inclusion.map (fUi i))
    rw [site.inclusion.map_preimage]
    infer_instance
  have hUiAffine (i : I) : IsAffine
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj (Ui i)) := by
    show IsAffine (i.1 : Scheme.{u})
    exact i.2
  have hgflat (i : I) : Flat (F.map (gi i)).left := by
    let := hgiOpen i
    infer_instance
  have hglfp (i : I) : LocallyOfFinitePresentation (F.map (gi i)).left := by
    let := hgiOpen i
    infer_instance
  have hglqf (i : I) : LocallyQuasiFinite (F.map (gi i)).left := by
    let := hgiOpen i
    infer_instance
  have key : ∀ i : I, ∃ (W : C)
      (a : yoneda.obj W ⟶
        (Stacks.Groupoids.quotientSheaf J F
          (AlgebraicGeometry.PreRelation.restrict j (F.map (gi i)))).obj),
      AlgebraicGeometry.IsAlgebraicSpace site S hS
          (Stacks.Groupoids.quotientSheaf J F
            (AlgebraicGeometry.PreRelation.restrict j (F.map (gi i)))).obj ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) a ∧
        ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj W).size ≤
          ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj (Ui i)).size := by
    intro i
    let := hUiAffine i
    let : Flat (AlgebraicGeometry.PreRelation.restrict j (F.map (gi i))).source.left :=
      property_preRelation_restrict_source (@Flat.{u}) j (F.map (gi i))
        inferInstance (hgflat i)
    let : Flat (AlgebraicGeometry.PreRelation.restrict j (F.map (gi i))).target.left :=
      property_preRelation_restrict_target (@Flat.{u}) j (F.map (gi i))
        inferInstance (hgflat i)
    let : LocallyOfFinitePresentation
        (AlgebraicGeometry.PreRelation.restrict j (F.map (gi i))).source.left :=
      property_preRelation_restrict_source (@LocallyOfFinitePresentation.{u}) j
        (F.map (gi i)) inferInstance (hglfp i)
    let : LocallyOfFinitePresentation
        (AlgebraicGeometry.PreRelation.restrict j (F.map (gi i))).target.left :=
      property_preRelation_restrict_target (@LocallyOfFinitePresentation.{u}) j
        (F.map (gi i)) inferInstance (hglfp i)
    let : LocallyQuasiFinite
        (AlgebraicGeometry.PreRelation.restrict j (F.map (gi i))).source.left :=
      property_preRelation_restrict_source (@LocallyQuasiFinite.{u}) j
        (F.map (gi i)) inferInstance (hglqf i)
    let : LocallyQuasiFinite
        (AlgebraicGeometry.PreRelation.restrict j (F.map (gi i))).target.left :=
      property_preRelation_restrict_target (@LocallyQuasiFinite.{u}) j
        (F.map (gi i)) inferInstance (hglqf i)
    exact exists_atlas_quotient_affine site S hS (Ui i)
      (AlgebraicGeometry.PreRelation.restrict j (F.map (gi i)))
  choose Wi ai hFi hasurj haetale hsizeW using key
  -- the affine opens form a covering sieve
  have hCoverI : Sieve.ofArrows Ui gi ∈ J U := by
    refine flat_cover_mem_bigFppfOver_topology site S hS Ui gi
      (fun i => hgflat i) (fun i => hglfp i) ?_
    intro x
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
    refine ⟨i, ⟨x, hxi⟩, ?_⟩
    show (site.inclusion.map (fUi i)) ⟨x, hxi⟩ = x
    rw [site.inclusion.map_preimage _]
    rfl
  have hI : Cardinal.mk I ≤ X.size := Scheme.mk_affineOpens_le_size X
  have hsizeW' (i : I) : ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).obj (Wi i)).size ≤
      X.size := by
    refine (hsizeW i).trans ?_
    show ((i.1 : Scheme.{u})).size ≤ X.size
    exact Scheme.size_coe_opens_le X i.1
  obtain ⟨-, -, hres, -, -, -⟩ := exists_atlas_quotient_of_coveringAtlases site S hS j Ui gi
    hgflat hglfp hCoverI hFi Wi ai hasurj haetale hI hsizeW'
  exact hres

private theorem isAlgebraicSpace_quotient_groupoidScheme_aux
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    (G : Stacks.Groupoids.GroupoidScheme S)
    (hU : site.Contains G.objects.left)
    (hrel : CategoryTheory.IsEquivalenceRelation
      (AlgebraicGeometry.groupoidPreRelation G).target
      (AlgebraicGeometry.groupoidPreRelation G).source)
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) (AlgebraicGeometry.groupoidPreRelation G)).obj := by
  by_cases he : IsOpenImmersion G.identity.left
  · let : IsOpenImmersion G.identity.left := he
    exact isAlgebraicSpace_quotient_of_open_identity site S hS G hU hrel
  · refine isAlgebraicSpace_quotient_groupoidScheme_of_locallyQuasiFinite_case
      site S hS ?_ G hU hrel
    intro R' U' j hjrel hjsflat hjslfp hjsqf hjtflat hjtlfp hjtqf
    let := hjrel
    let := hjsflat
    let := hjslfp
    let := hjsqf
    let := hjtflat
    let := hjtlfp
    let := hjtqf
    exact isAlgebraicSpace_quotient_locallyQuasiFinite site S hS j

/-- An étale-chart property of a representable morphism is the corresponding scheme
property of that morphism. -/
private theorem property_of_chartProperty_yoneda
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {X Y : AlgebraicGeometry.BigFppfOver site S hS} (h : X ⟶ Y)
    (hf : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P (yoneda.map h)) :
    P ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map h) :=
  MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage P (AlgebraicGeometry.BigFppfOver.toScheme site S hS))
    (F := yoneda) (f := h)
    ((AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative site S hS P hP
      (AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS X)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS Y) (yoneda.map h)
      (Functor.relativelyRepresentable.map yoneda h)).mp hf)

private theorem flat_of_chartProperty_yoneda
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {X Y : AlgebraicGeometry.BigFppfOver site S hS} (h : X ⟶ Y)
    (hf : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS
      (@Flat.{u} : MorphismProperty Scheme.{u}) (yoneda.map h)) :
    Flat ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map h) := by
  let : MorphismProperty.IsLocalAtTarget (@Flat : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact property_of_chartProperty_yoneda site S hS _
    AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget h hf

private theorem lfp_of_chartProperty_yoneda
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {X Y : AlgebraicGeometry.BigFppfOver site S hS} (h : X ⟶ Y)
    (hf : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (yoneda.map h)) :
    LocallyOfFinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map h) := by
  let : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
  exact property_of_chartProperty_yoneda site S hS _ hP h hf


/-- **Stacks 04S6, condition (2)**, for a relation on an object of the site. Let `U` be an
object of the big fppf site of `S` and let `j : R ⟶ U ×_S U` be an equivalence relation of
schemes over `S` whose source and target are flat and locally of finite presentation. Then the
fppf quotient sheaf `U/R` is an algebraic space. -/
theorem isAlgebraicSpace_quotientSheaf_of_flat_preRelation
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {R : Over S} {U : AlgebraicGeometry.BigFppfOver site S hS}
    (j : Stacks.Groupoids.PreRelation R ((Over.post site.inclusion).obj U))
    [IsEquivalenceRelation j.target j.source]
    [Flat j.source.left] [LocallyOfFinitePresentation j.source.left]
    [Flat j.target.left] [LocallyOfFinitePresentation j.target.left] :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) j).obj := by
  let F : AlgebraicGeometry.BigFppfOver site S hS ⥤ Over S :=
    Over.post (X := site.obj hS) site.inclusion
  obtain ⟨H0, hH0, -⟩ := AlgebraicGeometry.existsUnique_groupoidScheme_of_isEquivalenceRelation j
  rcases H0 with ⟨objects, arrows, source, target, comp, identity, inverse,
    hsid, htid, hsinv, htinv, hsc, htc, li, ri, linv, rinv, assoc'⟩
  rcases hH0 with ⟨hob, har, hsrc, htgt⟩
  dsimp only at hob har
  subst hob har
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsrc htgt
  subst hsrc htgt
  let H : Stacks.Groupoids.GroupoidScheme S :=
    ⟨F.obj U, arrows, j.source, j.target, comp, identity, inverse,
      hsid, htid, hsinv, htinv, hsc, htc, li, ri, linv, rinv, assoc'⟩
  have hj : AlgebraicGeometry.groupoidPreRelation H = j :=
    prod.hom_ext (prod.lift_fst _ _) (prod.lift_snd _ _)
  let : Flat H.source.left := inferInstanceAs (Flat j.source.left)
  let : Flat H.target.left := inferInstanceAs (Flat j.target.left)
  let : LocallyOfFinitePresentation H.source.left :=
    inferInstanceAs (LocallyOfFinitePresentation j.source.left)
  let : LocallyOfFinitePresentation H.target.left :=
    inferInstanceAs (LocallyOfFinitePresentation j.target.left)
  have hrelH : IsEquivalenceRelation (AlgebraicGeometry.groupoidPreRelation H).target
      (AlgebraicGeometry.groupoidPreRelation H).source := by
    rw [hj]; infer_instance
  have h := isAlgebraicSpace_quotient_groupoidScheme_aux site S hS H U.left.property hrelH
  rwa [hj] at h

/-- **Stacks 04S6, condition (2).** Let `(U, R, s, t, c)` be a groupoid scheme over `S` whose
object scheme belongs to the big fppf site, such that `s, t` are flat and locally of finite
presentation and `j = (t, s) : R ⟶ U ×_S U` is an equivalence relation. Then the fppf quotient
sheaf `U/R` is an algebraic space. -/
@[stacks 04S6 "condition (2): the quotient of a scheme by a flat, locally finitely presented \
equivalence relation groupoid scheme is an algebraic space"]
theorem isAlgebraicSpace_quotientSheaf_groupoidScheme
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    (G : Stacks.Groupoids.GroupoidScheme S) (hU : site.Contains G.objects.left)
    [IsEquivalenceRelation G.target G.source]
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion) (AlgebraicGeometry.groupoidPreRelation G)).obj := by
  have hs : (AlgebraicGeometry.groupoidPreRelation G).source = G.source := prod.lift_snd _ _
  have ht : (AlgebraicGeometry.groupoidPreRelation G).target = G.target := prod.lift_fst _ _
  refine isAlgebraicSpace_quotient_groupoidScheme_aux site S hS G hU ?_
  rw [hs, ht]; infer_instance

/-- A morphism of algebraic spaces which is representable and étale after every represented base
change satisfies every étale-local property containing the étale morphisms. -/
private theorem holdsOnEveryEtaleChart_of_etale_presheaf
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (hle : ∀ {X Y : Scheme.{u}} (k : X ⟶ Y), Etale k → P k)
    {F G : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : AlgebraicGeometry.IsAlgebraicSpace site S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace site S hS G)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) f) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P f :=
  (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative site S hS P hP hF hG f
    he.rep).mpr ⟨he.rep, fun _ _ gg fst snd BC => hle _ (he.property gg fst snd BC)⟩

/-- Flatness of a representable étale morphism of algebraic spaces. -/
private theorem isFlat_of_etale_presheaf'
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : AlgebraicGeometry.IsAlgebraicSpace site S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace site S hS G)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) f) :
    AlgebraicGeometry.Space.IsFlat site S hS f := by
  let : MorphismProperty.IsLocalAtTarget (@Flat : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact holdsOnEveryEtaleChart_of_etale_presheaf site S hS _
    AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget (fun k _ => inferInstance) f hF hG he

/-- Local finite presentation of a representable étale morphism of algebraic spaces. -/
private theorem isLocallyOfFinitePresentation_of_etale_presheaf'
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : AlgebraicGeometry.IsAlgebraicSpace site S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace site S hS G)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) f) :
    AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS f := by
  let : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact holdsOnEveryEtaleChart_of_etale_presheaf site S hS _
    AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    (fun k _ => inferInstance) f hF hG he

end AlgebraicGeometry.Bootstrap04S6

namespace AlgebraicGeometry.Space

open Bootstrap04S6

/-- For a jointly monic pair `t, s : R ⟶ U` and `a : X ⟶ U`, the iterated fibre product
`X ×_{a, U, t} R ×_{s, U, a} X` is a subobject of `X ⨯ X`. -/
theorem mono_prodLift_pullback_of_jointlyMono {C : Type*} [Category* C] {X U R : C}
    (a : X ⟶ U) {t s : R ⟶ U} (h : JointlyMono₂ t s) [HasPullback a t] [HasPullback s a]
    [HasPullback (pullback.snd a t) (pullback.fst s a)] [HasBinaryProduct X X] :
    Mono (prod.lift (pullback.fst (pullback.snd a t) (pullback.fst s a) ≫ pullback.fst a t)
      (pullback.snd (pullback.snd a t) (pullback.fst s a) ≫ pullback.snd s a)) := by
  constructor
  intro W f₁ f₂ hf
  let p₁ := pullback.fst (pullback.snd a t) (pullback.fst s a)
  let p₂ := pullback.snd (pullback.snd a t) (pullback.fst s a)
  have h₁ : f₁ ≫ p₁ ≫ pullback.fst a t = f₂ ≫ p₁ ≫ pullback.fst a t := by
    simpa using congrArg (· ≫ prod.fst) hf
  have h₂ : f₁ ≫ p₂ ≫ pullback.snd s a = f₂ ≫ p₂ ≫ pullback.snd s a := by
    simpa using congrArg (· ≫ prod.snd) hf
  have e₁ : ∀ f : W ⟶ pullback (pullback.snd a t) (pullback.fst s a),
      (f ≫ p₁ ≫ pullback.snd a t) ≫ t = (f ≫ p₁ ≫ pullback.fst a t) ≫ a := by
    intro f
    simp only [Category.assoc]
    rw [pullback.condition (f := a) (g := t)]
  have e₂ : ∀ f : W ⟶ pullback (pullback.snd a t) (pullback.fst s a),
      (f ≫ p₁ ≫ pullback.snd a t) ≫ s = (f ≫ p₂ ≫ pullback.snd s a) ≫ a := by
    intro f
    simp only [Category.assoc, p₁, p₂]
    rw [pullback.condition_assoc (f := pullback.snd a t) (g := pullback.fst s a),
      pullback.condition (f := s) (g := a)]
  have hr : f₁ ≫ p₁ ≫ pullback.snd a t = f₂ ≫ p₁ ≫ pullback.snd a t :=
    h.right_cancellation _ _ (by rw [e₁, e₁, h₁]) (by rw [e₂, e₂, h₂])
  have hr' : f₁ ≫ p₂ ≫ pullback.fst s a = f₂ ≫ p₂ ≫ pullback.fst s a := by
    have hw : p₁ ≫ pullback.snd a t = p₂ ≫ pullback.fst s a := pullback.condition
    rwa [← hw]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h₁
    · simpa only [Category.assoc] using hr
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using hr'
    · simpa only [Category.assoc] using h₂

/-- **Stacks 04S6, condition (1).** Let `j : R ⟶ U ×_Z U` be an equivalence relation of
algebraic spaces over a presheaf `Z` on the big fppf site of `S`, whose target and source
`t, s : R ⟶ U` are flat and locally of finite presentation. Then the fppf quotient sheaf `U/R`
is an algebraic space.

The proof is the source's: `U` is replaced by an étale atlas `h_{U₀} ⟶ U` (Groupoids in Spaces,
Lemma 046P, `AlgebraicGeometry.Space.isIso_restrictQuotientSheafMap_chartInSliceMap`); the
restricted relation `R₀ = U₀ ×_U R ×_U U₀` is then an algebraic space with a monomorphism,
locally of finite type, to `U₀ ×_S U₀`, hence representable by Morphisms of Spaces,
Proposition 03XX; and the resulting relation of schemes in the site is condition (2),
`AlgebraicGeometry.Bootstrap04S6.isAlgebraicSpace_quotientSheaf_of_flat_preRelation`. -/
@[stacks 04S6 "condition (1): the quotient of an algebraic space by a flat, locally finitely \
presented equivalence relation of algebraic spaces is an algebraic space"]
theorem bootstrap04S6QuotientSheaf (site : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : site.Contains S) : Bootstrap04S6QuotientSheaf site S hS := by
  intro Z R U j hR hU hrel htF htL hsF hsL
  let : HasSheafify (BigFppfOver.topology site S hS) (Type u) := hasSheafify_bigFppfOver site S hS
  have _ : HasFiniteLimits site.Schemes := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have _ : PreservesFiniteLimits site.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks site.inclusion
  have _ : HasBinaryProducts (BigFppfOver site S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let F : BigFppfOver site S hS ⥤ Over S := Over.post (X := site.obj hS) site.inclusion
  obtain ⟨Us, a, hasurj, haet⟩ := hU.exists_atlas
  let g : chartInSlice U a ⟶ U := chartInSliceMap U a
  have hj : IsPreEquivalenceRelation j :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).1 hrel).2
  have hiso := isIso_restrictQuotientSheafMap_chartInSliceMap j hj hU.isSheaf a hasurj haet
  refine AlgebraicGeometry.isAlgebraicSpace_of_iso site S hS
    ((sheafToPresheaf (BigFppfOver.topology site S hS) (Type u)).mapIso
      (asIso (restrictQuotientSheafMap j g))).symm ?_
  -- the restricted relation as an iterated fibre product of algebraic spaces
  let t := j.target.left
  let s := j.source.left
  have hpA := IsPullback.of_hasPullback a t
  have hpD := IsPullback.of_hasPullback s a
  have hpP := IsPullback.of_hasPullback (pullback.snd a t) (pullback.fst s a)
  let P := pullback (pullback.snd a t) (pullback.fst s a)
  let p₁ : P ⟶ pullback a t := pullback.fst _ _
  let p₂ : P ⟶ pullback s a := pullback.snd _ _
  let tP : P ⟶ yoneda.obj Us := p₁ ≫ pullback.fst a t
  let sP : P ⟶ yoneda.obj Us := p₂ ≫ pullback.snd s a
  have hyU := isAlgebraicSpace_yoneda site S hS Us
  have hA : IsAlgebraicSpace site S hS (pullback a t) :=
    isAlgebraicSpace_pullback site S hS a t hyU hR hU
  have hD : IsAlgebraicSpace site S hS (pullback s a) :=
    isAlgebraicSpace_pullback site S hS s a hR hyU hU
  have hP : IsAlgebraicSpace site S hS P := isAlgebraicSpace_pullback site S hS _ _ hA hD hR
  -- the restricted relation in the slice over `Z`
  have hRt : t ≫ U.hom = R.hom := Over.w j.target
  have hRs : s ≫ U.hom = R.hom := Over.w j.source
  let AO : Over Z := Over.mk (pullback.fst a t ≫ a ≫ U.hom)
  let DO : Over Z := Over.mk (pullback.snd s a ≫ a ≫ U.hom)
  let PO : Over Z := Over.mk (tP ≫ a ≫ U.hom)
  have hAw : pullback.snd a t ≫ R.hom = pullback.fst a t ≫ a ≫ U.hom := by
    rw [← hRt, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hDw : pullback.fst s a ≫ R.hom = pullback.snd s a ≫ a ≫ U.hom := by
    rw [← hRs, ← Category.assoc, pullback.condition, Category.assoc]
  let a₁ : AO ⟶ chartInSlice U a := Over.homMk (pullback.fst a t) rfl
  let a₂ : AO ⟶ R := Over.homMk (pullback.snd a t) hAw
  let d₁ : DO ⟶ R := Over.homMk (pullback.fst s a) hDw
  let d₂ : DO ⟶ chartInSlice U a := Over.homMk (pullback.snd s a) rfl
  let o₁ : PO ⟶ AO := Over.homMk p₁ rfl
  let o₂ : PO ⟶ DO := Over.homMk p₂ (by
    show p₂ ≫ pullback.snd s a ≫ a ≫ U.hom = (p₁ ≫ pullback.fst a t) ≫ a ≫ U.hom
    rw [← hDw, ← Category.assoc, ← pullback.condition, Category.assoc, hAw, Category.assoc])
  have ha' : IsPullback a₁ a₂ g j.target := IsPullback.of_map_of_faithful (Over.forget Z) hpA
  have hd' : IsPullback d₁ d₂ j.source g := IsPullback.of_map_of_faithful (Over.forget Z) hpD
  have hp' : IsPullback o₁ o₂ a₂ d₁ := IsPullback.of_map_of_faithful (Over.forget Z) hpP
  have hfin : IsPullback (prod.lift (o₁ ≫ a₁) (o₂ ≫ d₂)) (o₁ ≫ a₂) (prod.map g g) j := by
    have h := isPullback_prodLift_of_isPullback ha' hd' hp'
    have hjj : (prod.lift j.target j.source : R ⟶ U ⨯ U) = j :=
      prod.hom_ext (by simp) (by simp)
    rwa [hjj] at h
  let iso := hfin.isoIsPullback _ _ (IsPullback.of_hasPullback (prod.map g g) j)
  have hfst : iso.hom ≫ PreRelation.restrict j g = prod.lift (o₁ ≫ a₁) (o₂ ≫ d₂) :=
    IsPullback.isoIsPullback_hom_fst _ _ hfin (IsPullback.of_hasPullback _ _)
  have htgtO : (PreRelation.restrict j g).target.left = iso.inv.left ≫ tP := by
    have h : iso.hom ≫ (PreRelation.restrict j g).target = o₁ ≫ a₁ := by
      rw [PreRelation.target, ← Category.assoc, hfst, prod.lift_fst]
    have h2 : (PreRelation.restrict j g).target = iso.inv ≫ o₁ ≫ a₁ := by
      rw [← h, Iso.inv_hom_id_assoc]
    exact (congrArg Over.Hom.left h2).trans rfl
  have hsrcO : (PreRelation.restrict j g).source.left = iso.inv.left ≫ sP := by
    have h : iso.hom ≫ (PreRelation.restrict j g).source = o₂ ≫ d₂ := by
      rw [PreRelation.source, ← Category.assoc, hfst, prod.lift_snd]
    have h2 : (PreRelation.restrict j g).source = iso.inv ≫ o₂ ≫ d₂ := by
      rw [← h, Iso.inv_hom_id_assoc]
    exact (congrArg Over.Hom.left h2).trans rfl
  -- étaleness, flatness and local finite presentation of the pieces
  have hEtComp : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme site S hS))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hea₂ := hEtComp.of_isPullback hpA haet
  have hed₁ := hEtComp.of_isPullback hpD.flip haet
  have hep₁ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme site S hS))) p₁ :=
    hEtComp.of_isPullback hpP.flip hed₁
  have hep₂ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme site S hS))) p₂ :=
    hEtComp.of_isPullback hpP hea₂
  have hFa₁ : IsFlat site S hS (pullback.fst a t) :=
    holdsOnEveryEtaleChart_of_isPullback site S hS hpA haet htF
  have hFd₂ : IsFlat site S hS (pullback.snd s a) :=
    holdsOnEveryEtaleChart_of_isPullback site S hS hpD.flip haet hsF
  have hLa₁ : IsLocallyOfFinitePresentation site S hS (pullback.fst a t) :=
    holdsOnEveryEtaleChart_of_isPullback site S hS hpA haet htL
  have hLd₂ : IsLocallyOfFinitePresentation site S hS (pullback.snd s a) :=
    holdsOnEveryEtaleChart_of_isPullback site S hS hpD.flip haet hsL
  have hFtP : IsFlat site S hS tP := isFlat_comp site S hS hP hA hyU _ _
    (isFlat_of_etale_presheaf' site S hS p₁ hP hA hep₁) hFa₁
  have hFsP : IsFlat site S hS sP := isFlat_comp site S hS hP hD hyU _ _
    (isFlat_of_etale_presheaf' site S hS p₂ hP hD hep₂) hFd₂
  have hLtP : IsLocallyOfFinitePresentation site S hS tP :=
    isLocallyOfFinitePresentation_comp site S hS hP hA hyU _ _
      (isLocallyOfFinitePresentation_of_etale_presheaf' site S hS p₁ hP hA hep₁) hLa₁
  have hLsP : IsLocallyOfFinitePresentation site S hS sP :=
    isLocallyOfFinitePresentation_comp site S hS hP hD hyU _ _
      (isLocallyOfFinitePresentation_of_etale_presheaf' site S hS p₂ hP hD hep₂) hLd₂
  -- `P` is representable, by Stacks 03XX
  have hrelL : IsEquivalenceRelation t s := isEquivalenceRelation_left _ _ hrel
  obtain ⟨erL⟩ := hrelL.nonempty_equivalenceRelation
  have hmonoP : Mono (prod.lift tP sP) :=
    mono_prodLift_pullback_of_jointlyMono a erL.toJointlyMono₂
  let py : yoneda.obj (Us ⨯ Us) ≅ yoneda.obj Us ⨯ yoneda.obj Us :=
    PreservesLimitPair.iso yoneda Us Us
  let q : P ⟶ yoneda.obj (Us ⨯ Us) := prod.lift tP sP ≫ py.inv
  have hmonoq : Mono q := mono_comp _ _
  have hqsnd : q ≫ yoneda.map (prod.snd : Us ⨯ Us ⟶ Us) = sP := by
    simp [q, py]
  have hT := isAlgebraicSpace_yoneda site S hS (Us ⨯ Us)
  have hlft : IsLocallyOfFiniteType site S hS q := by
    refine isLocallyOfFiniteType_of_comp site S hS hP hT hyU q
      (yoneda.map (prod.snd : Us ⨯ Us ⟶ Us)) ?_
    rw [hqsnd]
    exact isLocallyOfFiniteType_of_isLocallyOfFinitePresentation site S hS hLsP
  have : P.IsRepresentable :=
    isRepresentable_of_locallyQuasiFinite_separated site S hS P (yoneda.obj (Us ⨯ Us)) hP hT q
      inferInstance (isLocallyQuasiFinite_of_mono site S hS hP hT q hmonoq hlft)
      (isSeparated_of_mono site S hS q hmonoq)
  -- the relation of objects of the site
  let Rs := P.reprX
  let eR : P ≅ yoneda.obj Rs := P.reprW.symm
  let ts : Rs ⟶ Us := yoneda.preimage (eR.inv ≫ tP)
  let ss : Rs ⟶ Us := yoneda.preimage (eR.inv ≫ sP)
  have hts : yoneda.map ts = eR.inv ≫ tP := Functor.map_preimage _ _
  have hss : yoneda.map ss = eR.inv ≫ sP := Functor.map_preimage _ _
  let i : (PreRelation.restriction j g).left ≅ yoneda.obj Rs :=
    (Over.forget Z).mapIso iso.symm ≪≫ eR
  have htgt : (PreRelation.restrict j g).target.left = i.hom ≫ yoneda.map ts := by
    rw [hts, htgtO]
    simp [i]
  have hsrc : (PreRelation.restrict j g).source.left = i.hom ≫ yoneda.map ss := by
    rw [hss, hsrcO]
    simp [i]
  have hrelR : IsEquivalenceRelation (i.hom ≫ yoneda.map ts) (i.hom ≫ yoneda.map ss) := by
    rw [← htgt, ← hsrc]
    exact isEquivalenceRelation_left _ _ inferInstance
  have hsite : IsEquivalenceRelation ts ss :=
    isEquivalenceRelation_of_map_of_iso yoneda i ts ss hrelR
  have htarget : (relation site S hS ss ts).target =
      (Over.post (X := site.obj hS) site.inclusion).map ts := prod.lift_fst _ _
  have hsource : (relation site S hS ss ts).source =
      (Over.post (X := site.obj hS) site.inclusion).map ss := prod.lift_snd _ _
  have : IsEquivalenceRelation (relation site S hS ss ts).target
      (relation site S hS ss ts).source := by
    rw [htarget, hsource]
    exact isEquivalenceRelation_map (Over.post (X := site.obj hS) site.inclusion) ts ss hsite
  have hFs : HoldsOnEveryEtaleChart site S hS (@Flat.{u} : MorphismProperty Scheme.{u})
      (yoneda.map ss) := by
    rw [hss]
    exact chartProperty_precomp_iso site S hS _ eR.symm _ hFsP
  have hFt : HoldsOnEveryEtaleChart site S hS (@Flat.{u} : MorphismProperty Scheme.{u})
      (yoneda.map ts) := by
    rw [hts]
    exact chartProperty_precomp_iso site S hS _ eR.symm _ hFtP
  have hLs : HoldsOnEveryEtaleChart site S hS
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (yoneda.map ss) := by
    rw [hss]
    exact chartProperty_precomp_iso site S hS _ eR.symm _ hLsP
  have hLt : HoldsOnEveryEtaleChart site S hS
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (yoneda.map ts) := by
    rw [hts]
    exact chartProperty_precomp_iso site S hS _ eR.symm _ hLtP
  have : Flat (relation site S hS ss ts).source.left := by
    rw [hsource]
    exact flat_of_chartProperty_yoneda site S hS ss hFs
  have : Flat (relation site S hS ss ts).target.left := by
    rw [htarget]
    exact flat_of_chartProperty_yoneda site S hS ts hFt
  have : LocallyOfFinitePresentation (relation site S hS ss ts).source.left := by
    rw [hsource]
    exact lfp_of_chartProperty_yoneda site S hS ss hLs
  have : LocallyOfFinitePresentation (relation site S hS ss ts).target.left := by
    rw [htarget]
    exact lfp_of_chartProperty_yoneda site S hS ts hLt
  have halg := isAlgebraicSpace_quotientSheaf_of_flat_preRelation site S hS
    (relation site S hS ss ts)
  have hpre := quotientPresheafIsoPoints site S hS (PreRelation.restrict j g) ss ts i htgt hsrc
  exact AlgebraicGeometry.isAlgebraicSpace_of_iso site S hS
    ((sheafToPresheaf (BigFppfOver.topology site S hS) (Type u)).mapIso
      ((presheafToSheaf (BigFppfOver.topology site S hS) (Type u)).mapIso hpre)).symm halg

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Bootstrap04S6

end AlgebraicGeometry.Bootstrap04S6

end
