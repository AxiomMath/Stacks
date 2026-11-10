module

public import StacksCore.Tactic.StacksAttribute
public import StacksCore.CategoryTheory.Pullback
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SchemeSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite
public import StacksFrontier.CategoryTheory.Limits.PullbackChartPasting

/-!
# Glueing algebraic spaces along open subspaces

Stacks 02WR: an fppf sheaf `F` on the big fppf site over `S` covered by a family of
algebraic-space subfunctors through relatively representable open immersions is an algebraic
space, provided the sheaf coproduct of the family is an algebraic space.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_of_open_cover` is Tag 02WR.

## Implementation notes

The two clauses of `AlgebraicGeometry.IsAlgebraicSpace` which are not hypotheses are obtained
as in the source.

*The atlas.* An atlas `f : yoneda.obj U ⟶ G` of the coproduct `G` is decomposed by
`AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan` into open subobjects
`Uᵢ ⊆ U` over which the tautological section of `G` comes from the `i`-th member; that is Tag
02WO in the only form this proof needs, and
`AlgebraicGeometry.isPullback_yoneda_clopen_piece` upgrades it to the statement that
`yoneda.obj (Uᵢ i)` *is* the fibre product `Fᵢ i ×_G U`. The composite `f ≫ g` is then
surjective because it is locally surjective and relatively representable
(`AlgebraicGeometry.Space.presheafSurjective_of_relativelyRepresentable`), and étale because
its base change along any `yoneda.obj T ⟶ F` is covered by the base changes of the
`Uᵢ i ⟶ Fᵢ i`, each of which is étale.

*The diagonal.* Representability of `diag F` reduces to representability of
`yoneda.obj T ×_F yoneda.obj T'` for two objects of the site over `F`. The charts of that
fibre product are the `Vᵢ ×_{Fᵢ} V'ᵢ`, where `Vᵢ = Fᵢ ×_F T`; they are representable because
`Fᵢ i` is an algebraic space, they are open subobjects, and they cover. The glueing is
`AlgebraicGeometry.isRepresentable_of_openCharts`, and its two size hypotheses are met as
follows: the charts are *reindexed by the points of `T`*
(`AlgebraicGeometry.exists_chart_index_of_openCover`), whose number is below the cutoff
because the cutoff is a strong limit; and each chart admits a monomorphism to the single
object `T ⨯ T'` of the site, so `AlgebraicGeometry.Scheme.size_le_of_mono` bounds all of them
by `μ = max (2 ^ #(T ⨯ T')) (size (T ⨯ T'))`, which is below the cutoff by
`AlgebraicGeometry.Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit`.

The unconditional monomorphism bound is what this proof needs: the chart
`Vᵢ ×_{Fᵢ} V'ᵢ ⟶ T ⨯ T'` is a monomorphism, being a base change of the diagonal of `Fᵢ i`
composed with a product of open immersions, but it is only locally of finite *type*, so
neither `AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact` nor
`AlgebraicGeometry.Scheme.size_le_of_mono_locallyOfFinitePresentation` applies — and the bound
`size X ≤ size Y` for a monomorphism is false (Stacks 04VA).

## References

* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 04VA](https://stacks.math.columbia.edu/tag/04VA)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points of an object of the site are fewer than the cutoff -/

/-- An object of the big fppf site over `S` has fewer points than the cutoff of the site.

The cutoff is a strong limit and the points of a scheme number at most `2 ^ size`, by
`AlgebraicGeometry.Scheme.mk_le_two_pow_size`. -/
alias BigFppfOver.mk_lt_cutoff := AlgebraicGeometry.Space.mk_points_lt_cutoff

/-! ### Surjectivity and local surjectivity -/

variable {B S hS}

/-- If a section `t` of the target pulled back along `a` lifts to the source of a relatively
representable `f`, every point hit by `a` lies in the range of the base change of `f`. -/
private theorem mem_range_snd_of_lift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hrep : yoneda.relativelyRepresentable f) {T V : BigFppfOver B S hS}
    (t : yoneda.obj T ⟶ G) (a : V ⟶ T) (w : F.obj (op V))
    (hw : f.app (op V) w = G.map a.op (yonedaEquiv t))
    (z : (BigFppfOver.toScheme B S hS).obj V) (x : (BigFppfOver.toScheme B S hS).obj T)
    (hz : (BigFppfOver.toScheme B S hS).map a z = x) :
    x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (hrep.snd t)) := by
  have hb : yonedaEquiv.symm w ≫ f = yoneda.map a ≫ t := by
    refine yonedaEquiv.injective ?_
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_naturality] using hw
  refine ⟨(BigFppfOver.toScheme B S hS).map (hrep.lift (yonedaEquiv.symm w) a hb) z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hrep.lift_snd]
  exact hz

/-- A relatively representable morphism of presheaves on the big fppf site over `S` which is
locally surjective for the fppf topology is surjective after every represented base change.

Every covering sieve is jointly surjective on points
(`AlgebraicGeometry.BigFppfOver.exists_mem_arrows_mem_range`), so a point of a represented
base change of the target is hit by a member of the covering sieve on which the section lifts,
and the lift factors through the base change. -/
theorem Space.presheafSurjective_of_relativelyRepresentable
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hrep : yoneda.relativelyRepresentable f)
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  have _ := hloc
  have _ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd hrep fun T g => ⟨fun x => ?_⟩
  obtain ⟨V, a, ⟨z, hz⟩, v, hv⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS
    (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) f (yonedaEquiv g)) x
  exact mem_range_snd_of_lift hrep g a z hz v x hv

/-- A morphism of presheaves on the big fppf site over `S` which is surjective and étale after
every represented base change is locally surjective for the fppf topology.

The represented base change along the morphism determined by a section of the target is a
surjective étale morphism of the site, hence generates a covering sieve by
`AlgebraicGeometry.singleton_mem_bigFppf_topology`, and the section lifts over it. -/
theorem Space.isLocallySurjective_of_presheafSurjective_etale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f := by
  refine ⟨fun {T} y => ?_⟩
  set ξ : yoneda.obj T ⟶ G := yonedaEquiv.symm y with hξ
  set q := hs.rep.snd ξ with hq
  have hbase : Sieve.generate (Presieve.singleton q.left) ∈ B.topology T.left :=
    singleton_mem_bigFppf_topology B q.left (hs.property_snd ξ)
      (he.property ξ (hs.rep.fst ξ) q (hs.rep.isPullback ξ))
  have hcover : Sieve.generate (Presieve.singleton q) ∈ BigFppfOver.topology B S hS T := by
    change Sieve.generate (Presieve.singleton q) ∈ B.topology.over (B.obj hS) T
    rw [B.topology.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
      Presieve.map_singleton]
    exact hbase
  refine (BigFppfOver.topology B S hS).superset_covering
    ((Sieve.generate_le_iff _ _).mpr ?_) hcover
  rintro _ _ ⟨⟩
  refine ⟨yonedaEquiv (hs.rep.fst ξ), ?_⟩
  have hw := congrArg yonedaEquiv (hs.rep.isPullback ξ).w
  rw [← yonedaEquiv_naturality ξ q] at hw
  simpa only [hξ, yonedaEquiv_comp, Equiv.apply_symm_apply] using hw

/-! ### The open charts of a test object cover it -/

section Cover

variable {I : Type v} {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, Fᵢ i ⟶ G)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : G.obj ⟶ F)

/-- Every point of an object of the site over `F` lies in the image of one of the open charts
cut out by the members of the covering family.

The section of `F` determined by `t` lifts locally to `G`, and locally in `G` it lies in the
image of one of the legs `ι i`; so it lies in the image of one of the `(ι i).hom ≫ g` over a
covering sieve of `T`, and every covering sieve of the big fppf site over `S` is jointly
surjective on points. -/
theorem exists_mem_range_snd_of_openCover (hG : IsColimit (Cofan.mk G ι))
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g)
    (hrep : ∀ i, yoneda.relativelyRepresentable ((ι i).hom ≫ g))
    {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ F)
    (x : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hrep i).snd t)) := by
  have _ := hloc
  have hA : (⨆ i, Subfunctor.range ((ι i).hom ≫ g)).sieveOfSection (yonedaEquiv t) ∈
      BigFppfOver.topology B S hS T := by
    refine (BigFppfOver.topology B S hS).transitive
      (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) g (yonedaEquiv t)) _ ?_
    rintro V a ⟨z, hz⟩
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (CategoryTheory.Sheaf.sieveOfSection_iSup_range_mem
        (BigFppfOver.topology B S hS) ι hG (op V) z)
    intro W b hb
    have hb' : G.obj.map b.op z ∈ (⨆ i, Subfunctor.range (ι i).hom).obj (op W) := hb
    rw [Subfunctor.iSup_obj, Set.mem_iUnion] at hb'
    obtain ⟨i, w, hw⟩ := hb'
    change F.map (b ≫ a).op (yonedaEquiv t) ∈
      (⨆ i, Subfunctor.range ((ι i).hom ≫ g)).obj (op W)
    rw [Subfunctor.iSup_obj, Set.mem_iUnion]
    refine ⟨i, w, ?_⟩
    change g.app _ ((ι i).hom.app _ w) = _
    rw [hw, NatTrans.naturality_apply, hz, ← Functor.map_comp_apply, ← op_comp]
  obtain ⟨V, a, ha, z, hz⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS hA x
  have ha' : F.map a.op (yonedaEquiv t) ∈
    (⨆ i, Subfunctor.range ((ι i).hom ≫ g)).obj (op V) := ha
  rw [Subfunctor.iSup_obj, Set.mem_iUnion] at ha'
  obtain ⟨i, w, hw⟩ := ha'
  exact ⟨i, mem_range_snd_of_lift (hrep i) t a w hw z x hz⟩

/-- The open charts of a test object over `F`, reindexed by the points of that object: a
choice, for each point, of a member of the covering family whose chart contains it.

This is what makes the index type of the charts small enough for
`AlgebraicGeometry.isRepresentable_of_openCharts`: the index type `I` of the covering family
is arbitrary, but the points of an object of the site number fewer than the cutoff. -/
theorem exists_chart_index_of_openCover (hG : IsColimit (Cofan.mk G ι))
    (hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g)
    (hrep : ∀ i, yoneda.relativelyRepresentable ((ι i).hom ≫ g))
    (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ F) :
    ∃ idx : (BigFppfOver.toScheme B S hS).obj T → I, ∀ x,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hrep (idx x)).snd t)) := by
  classical
  choose idx hidx using fun x =>
    exists_mem_range_snd_of_openCover ι g hG hloc hrep t x
  exact ⟨idx, hidx⟩

end Cover

/-! ### A clopen piece of an atlas represents the fibre product -/

/-- The piece of an object `U` of the site on which a section of a coproduct `G = ∐ Fᵢ` comes
from the `i`-th member *represents* the fibre product `Fᵢ i ×_G U`.

This is the form in which Tag 02WO enters Tag 02WR. The decomposition of
`AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan` supplies `W`, the open
immersion `q : W ⟶ U`, the lifted section `z` and the universal property `huniv`; this lemma
reads them as the universal property of a fibre product. Injectivity of the comparison is
`q` being a monomorphism, and surjectivity is `huniv` together with injectivity on sections of
the monomorphism `ι i` (`AlgebraicGeometry.Sheaf.mono_cofan_inj_bigFppfOver` and
`CategoryTheory.Sheaf.injective_app_of_mono`). -/
theorem isPullback_yoneda_clopen_piece {I : Type v}
    {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, Fᵢ i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) {U W : BigFppfOver B S hS} {i : I} (q : W ⟶ U)
    (hq : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map q))
    (x : G.obj.obj (op U)) (z : (Fᵢ i).obj.obj (op W))
    (hz : (ι i).hom.app (op W) z = G.obj.map q.op x)
    (huniv : ∀ (T : BigFppfOver B S hS) (t : T ⟶ U),
      (∃ y : (Fᵢ i).obj.obj (op T), (ι i).hom.app (op T) y = G.obj.map t.op x) →
      ∃ t' : T ⟶ W, t' ≫ q = t) :
    IsPullback (yoneda.map q) (yonedaEquiv.symm z) (yonedaEquiv.symm x) (ι i).hom := by
  have hqmono : Mono q := by
    have _ := hq
    exact Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS) (f := q) (IsOpenImmersion.mono _)
  have hιmono : Mono (ι i) := Sheaf.mono_cofan_inj_bigFppfOver ι hG i
  have hinj : ∀ T : BigFppfOver B S hS, Function.Injective ((ι i).hom.app (op T)) :=
    fun T => CategoryTheory.Sheaf.injective_app_of_mono (ι i) T
  have hw : yoneda.map q ≫ yonedaEquiv.symm x = yonedaEquiv.symm z ≫ (ι i).hom := by
    refine yonedaEquiv.injective ?_
    rw [← yonedaEquiv_naturality, yonedaEquiv_comp]
    simp only [Equiv.apply_symm_apply]
    exact hz.symm
  refine IsPullback.of_forall_isPullback_app fun V => ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun m : yoneda.obj W ⟶ G.obj => m.app V) hw, ?_, ?_⟩
  · rintro t₁ t₂ ⟨h₁, -⟩
    exact (cancel_mono q).1 h₁
  · intro t y hty
    have hxy : G.obj.map t.op x = (ι i).hom.app (op V.unop) y := hty
    obtain ⟨t', ht'⟩ := huniv V.unop t ⟨y, hxy.symm⟩
    refine ⟨t', ht', ?_⟩
    have key : (Fᵢ i).obj.map t'.op z = y := by
      refine hinj V.unop ?_
      rw [NatTrans.naturality_apply (ι i).hom t'.op z, hz, ← Functor.map_comp_apply,
        ← op_comp, ht']
      exact hxy
    exact key

/-! ### Two auxiliary representability facts -/

/-- A represented base change of a relatively representable open immersion into `F` from an
algebraic space is again relatively representable *over `F`*.

The chart `ha.rep.snd t : V ⟶ T` of `a` along `t` composes with `t` to the morphism
`ha.rep.fst t ≫ a`, and that is relatively representable because `ha.rep.fst t` is — the
diagonal of `F₀` is representable — and `a` is. -/
theorem relativelyRepresentable_yoneda_map_snd_comp
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {F₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF₀ : IsAlgebraicSpace B S hS F₀)
    (a : F₀ ⟶ F) (ha : (openImmersionOver B S hS).presheaf a)
    (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ F) :
    yoneda.relativelyRepresentable (yoneda.map (ha.rep.snd t) ≫ t) := by
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have h₁ : yoneda.relativelyRepresentable (ha.rep.fst t) :=
    Functor.relativelyRepresentable.of_diag hF₀.diagonal_representable _
  have h₂ : yoneda.relativelyRepresentable (ha.rep.fst t ≫ a) :=
    yoneda.relativelyRepresentable.comp_mem _ _ h₁ ha.rep
  simpa only [(ha.rep.w t).symm] using h₂

/-! ### Tag 02WR -/

/-- **Stacks 02WR.** An fppf sheaf with a jointly surjective family of representable open
algebraic-space subfunctors is an algebraic space, when the coproduct of the family is itself
an algebraic space. -/
@[stacks 02WR]
theorem isAlgebraicSpace_of_open_cover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (I : Type v)
    (Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (hFᵢ : ∀ i, IsAlgebraicSpace B S hS (Fᵢ i).obj)
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, Fᵢ i ⟶ G)
    (hcoprod : IsColimit (Cofan.mk G ι))
    (g : G.obj ⟶ F)
    (hopen : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ((ι i).hom ≫ g))
    (hsurj : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B S hS) g)
    (hG : IsAlgebraicSpace B S hS G.obj) :
    IsAlgebraicSpace B S hS F := by
  classical
  let J := BigFppfOver.topology B S hS
  let Tfun := BigFppfOver.toScheme B S hS
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have _ : PreservesLimitsOfShape WalkingCospan Tfun := comp_preservesLimitsOfShape _ _
  -- the atlas of the coproduct, decomposed over the members
  obtain ⟨U, f, hfSurj, hfEtale⟩ := hG.exists_atlas
  obtain ⟨Uᵢ, q, hqOpen, hqSec, -, hqCov, hqUniv⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι hcoprod U (yonedaEquiv f)
  choose z hz using hqSec
  let fᵢ : ∀ i, yoneda.obj (Uᵢ i) ⟶ (Fᵢ i).obj := fun i => yonedaEquiv.symm (z i)
  have hUi : ∀ i, IsPullback (yoneda.map (q i)) (fᵢ i) f (ι i).hom := fun i => by
    simpa only [Equiv.symm_apply_apply] using
      isPullback_yoneda_clopen_piece ι hcoprod (q i) (hqOpen i) (yonedaEquiv f) (z i) (hz i)
        (hqUniv i)
  -- the pieces of the atlas are surjective étale charts of the members
  have hfiEtale : ∀ i, (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).presheaf (fᵢ i) := fun i => by
    have _ : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (hUi i) hfEtale
  -- and the composite with the inclusion of the member is étale over `F`
  have hlocalEtale : ∀ i, (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).presheaf
      (yoneda.map (q i) ≫ f ≫ g) := fun i => by
    have hcomp : fᵢ i ≫ (ι i).hom ≫ g = yoneda.map (q i) ≫ f ≫ g := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ g) (hUi i).w.symm
    rw [← hcomp]
    have ho : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).presheaf ((ι i).hom ≫ g) :=
      MorphismProperty.relative_monotone (fun _ _ k hk => by
        have _ : IsOpenImmersion (Tfun.map k) := hk
        exact (inferInstance : Etale (Tfun.map k))) _ (hopen i)
    have _ : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).IsStableUnderComposition := by
      refine ⟨fun {_ _ _} a b ha hb => ?_⟩
      change Etale (Tfun.map (a ≫ b))
      rw [Functor.map_comp]
      have _ : Etale (Tfun.map a) := ha
      have _ : Etale (Tfun.map b) := hb
      infer_instance
    have _ : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        Tfun).presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    exact MorphismProperty.comp_mem _ _ _ (hfiEtale i) ho
  -- `f ≫ g` is locally surjective
  have hfgLoc : Presheaf.IsLocallySurjective J (f ≫ g) := by
    have _ := Space.isLocallySurjective_of_presheafSurjective_etale f hfSurj hfEtale
    have _ := hsurj
    infer_instance
  -- the diagonal
  have hdiag : yoneda.relativelyRepresentable (diag F) := by
    rw [Functor.relativelyRepresentable.diag_iff]
    intro T t
    rw [yoneda_relativelyRepresentable_iff_pullback_representable]
    intro T' ξ
    set t' : yoneda.obj T' ⟶ F := yonedaEquiv.symm ξ with ht'def
    have hp : IsPullback (pullback.snd t' t) (pullback.fst t' t) t t' :=
      (IsPullback.of_hasPullback t' t).flip
    let HH : Sheaf J (Type u) := ⟨pullback t' t,
      Presheaf.isSheaf_pullback J t' t
        (BigFppfOver.isSheaf_yoneda_obj B S hS T') (BigFppfOver.isSheaf_yoneda_obj B S hS T) hF⟩
    obtain ⟨idx, hidx⟩ := exists_chart_index_of_openCover ι g hcoprod hsurj
      (fun i => (hopen i).rep) T t
    let Xc : Tfun.obj T → BigFppfOver B S hS := fun x => (hopen (idx x)).rep.pullback t
    let k : ∀ x : Tfun.obj T, Xc x ⟶ T := fun x => (hopen (idx x)).rep.snd t
    have hvRep : ∀ x, yoneda.relativelyRepresentable (yoneda.map (k x) ≫ t) := fun x =>
      relativelyRepresentable_yoneda_map_snd_comp (hFᵢ (idx x)) ((ι (idx x)).hom ≫ g)
        (hopen (idx x)) T t
    let Wc : Tfun.obj T → BigFppfOver B S hS := fun x => (hvRep x).pullback t'
    let w : ∀ x, yoneda.obj (Wc x) ⟶ HH.obj := fun x =>
      hp.flip.lift (yoneda.map ((hvRep x).snd t')) ((hvRep x).fst t' ≫ yoneda.map (k x))
        (by simpa only [Category.assoc] using ((hvRep x).isPullback t').w.symm)
    have hw : ∀ x, IsPullback ((hvRep x).fst t') (w x) (yoneda.map (k x))
        (pullback.snd t' t) := fun x =>
      isPullback_chart_into_pullback ((hvRep x).isPullback t') hp
    -- the charts of the fibre product are open subobjects
    have _ : (openImmersionOver B S hS).IsStableUnderBaseChange := by
      refine ⟨fun {_ _ _ _} a b a' b' hs ha => ?_⟩
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsOpenImmersion.{u}) (hs.map Tfun) ha
    have _ : (openImmersionOver B S hS).presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    have hwOpen : ∀ x, (openImmersionOver B S hS).presheaf (w x) := fun x =>
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (hw x)
        (MorphismProperty.relative_map ((hopen (idx x)).property_snd t))
    -- each chart admits a monomorphism to the single object `T ⨯ T'`
    let m : ∀ x, Wc x ⟶ T ⨯ T' := fun x =>
      prod.lift (yoneda.preimage ((hvRep x).fst t') ≫ k x) ((hvRep x).snd t')
    have hmMono : ∀ x, Mono (m x) := fun x => by
      have hkMono : Mono (k x) := by
        have _ : IsOpenImmersion (Tfun.map (k x)) := (hopen (idx x)).property_snd t
        exact Tfun.mono_of_mono_map (IsOpenImmersion.mono _)
      refine ⟨fun {Z} a b hab => ?_⟩
      have hfst : a ≫ yoneda.preimage ((hvRep x).fst t') =
          b ≫ yoneda.preimage ((hvRep x).fst t') := by
        refine (cancel_mono (k x)).mp ?_
        simpa only [m, Category.assoc, prod.lift_fst] using
          congrArg (fun y => y ≫ prod.fst) hab
      have hsnd : a ≫ (hvRep x).snd t' = b ≫ (hvRep x).snd t' := by
        simpa only [m, Category.assoc, prod.lift_snd] using
          congrArg (fun y => y ≫ prod.snd) hab
      refine yoneda.map_injective (((hvRep x).isPullback t').hom_ext ?_ ?_)
      · simpa only [Functor.map_comp, Functor.map_preimage] using
          congrArg (fun y => yoneda.map y) hfst
      · simpa only [Functor.map_comp] using congrArg (fun y => yoneda.map y) hsnd
    have hμ : max (2 ^ #(Tfun.obj (T ⨯ T') : Type u)) (Tfun.obj (T ⨯ T')).size < B.cutoff :=
      Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit
        (T ⨯ T').left.property
    have hWSize : ∀ x, (Tfun.obj (Wc x)).size ≤
        max (2 ^ #(Tfun.obj (T ⨯ T') : Type u)) (Tfun.obj (T ⨯ T')).size := fun x => by
      have _ : Mono (m x) := hmMono x
      have _ : Mono (Tfun.map (m x)) := inferInstance
      exact Scheme.size_le_of_mono (Tfun.map (m x))
    -- and the charts cover
    have hcoverT : Sieve.ofArrows Xc k ∈ J T :=
      BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS k
        (fun x => (hopen (idx x)).property_snd t) (fun x => ⟨x, hidx x⟩)
    have hWLoc : Presheaf.IsLocallySurjective J (Sigma.desc w) := by
      refine ⟨fun {V} ζ => ?_⟩
      set α : V ⟶ T := yoneda.preimage (yonedaEquiv.symm ζ ≫ pullback.snd t' t) with hα
      refine J.superset_covering ?_ (J.pullback_stable α hcoverT)
      rintro V' β ⟨-, b, -, ⟨x⟩, fac⟩
      have hc : yoneda.map b ≫ yoneda.map (k x) =
          (yoneda.map β ≫ yonedaEquiv.symm ζ) ≫ pullback.snd t' t := by
        calc yoneda.map b ≫ yoneda.map (k x) = yoneda.map (b ≫ k x) := by
              rw [Functor.map_comp]
          _ = yoneda.map (β ≫ α) := congrArg yoneda.map fac
          _ = (yoneda.map β ≫ yonedaEquiv.symm ζ) ≫ pullback.snd t' t := by
              simp only [hα, Functor.map_comp, Functor.map_preimage, Category.assoc]
      refine ⟨(Sigma.ι (fun y => yoneda.obj (Wc y)) x).app (op V')
        (yoneda.preimage ((hw x).lift (yoneda.map b)
          (yoneda.map β ≫ yonedaEquiv.symm ζ) hc)), ?_⟩
      change ((Sigma.ι (fun y => yoneda.obj (Wc y)) x ≫ Sigma.desc w).app (op V')) _ = _
      rw [Sigma.ι_comp_desc]
      have hzz : yoneda.map (yoneda.preimage ((hw x).lift (yoneda.map b)
          (yoneda.map β ≫ yonedaEquiv.symm ζ) hc)) ≫ w x =
          yoneda.map β ≫ yonedaEquiv.symm ζ := by
        simpa only [Functor.map_preimage] using
          (hw x).lift_snd (yoneda.map b) (yoneda.map β ≫ yonedaEquiv.symm ζ) hc
      have hzz' := congrArg yonedaEquiv hzz
      rw [← yonedaEquiv_naturality (yonedaEquiv.symm ζ) β] at hzz'
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map,
        Equiv.apply_symm_apply] using hzz'
    exact isRepresentable_of_openCharts HH Wc w hwOpen (BigFppfOver.mk_lt_cutoff B S hS T)
      hμ hWSize hWLoc
  -- assemble
  have hfgRep : yoneda.relativelyRepresentable (f ≫ g) :=
    Functor.relativelyRepresentable.of_diag hdiag _
  refine ⟨hF, hdiag, U, f ≫ g, ?_, ?_⟩
  · exact Space.presheafSurjective_of_relativelyRepresentable (f ≫ g) hfgRep hfgLoc
  · have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have _ : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) Tfun).RespectsIso :=
      MorphismProperty.RespectsIso.inverseImage _ _
    refine MorphismProperty.relative_of_snd hfgRep fun T t => ?_
    set V := hfgRep.pullback t with hV
    set p : V ⟶ T := hfgRep.snd t with hp
    set r : V ⟶ U := yoneda.preimage (hfgRep.fst t) with hr
    have hrp : IsPullback (yoneda.map r) (yoneda.map p) (f ≫ g) t := by
      simpa only [hr, hp, Functor.map_preimage] using hfgRep.isPullback t
    have hsq : ∀ i, IsPullback (Tfun.map (pullback.fst (q i) r))
        (Tfun.map (pullback.snd (q i) r)) (Tfun.map (q i)) (Tfun.map r) := fun i =>
      (IsPullback.of_hasPullback (q i) r).map Tfun
    have hbOpen : ∀ i, IsOpenImmersion (Tfun.map (pullback.snd (q i) r)) := fun i =>
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsOpenImmersion.{u}) (hsq i) (hqOpen i)
    have hbEtale : ∀ i, Etale (Tfun.map (pullback.snd (q i) r ≫ p)) := fun i => by
      have hpb : IsPullback (yoneda.map (pullback.fst (q i) r))
          (yoneda.map (pullback.snd (q i) r) ≫ yoneda.map p)
          (yoneda.map (q i) ≫ (f ≫ g)) t :=
        ((IsPullback.of_hasPullback (q i) r).map yoneda).paste_vert hrp
      exact (hlocalEtale i).property t (yoneda.map (pullback.fst (q i) r))
        (pullback.snd (q i) r ≫ p)
        (by simpa only [Functor.map_comp, Category.assoc] using hpb)
    have hbCover : iSup (fun i : I => (Tfun.map (pullback.snd (q i) r)).opensRange) = ⊤ := by
      refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
      rw [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion]
      obtain ⟨i, y, hy⟩ := hqCov (Tfun.map r x)
      obtain ⟨c, hc⟩ : x ∈ Set.range (pullback.snd (Tfun.map (q i)) (Tfun.map r)) :=
        (IsOpenImmersion.range_pullbackSnd (Tfun.map (q i)) (Tfun.map r)).ge ⟨y, hy⟩
      refine ⟨i, (hsq i).isoPullback.inv c, ?_⟩
      calc (Tfun.map (pullback.snd (q i) r)) ((hsq i).isoPullback.inv c)
          = (pullback.snd (Tfun.map (q i)) (Tfun.map r))
            ((hsq i).isoPullback.hom ((hsq i).isoPullback.inv c)) := by
            simpa only [← Scheme.Hom.comp_apply, Category.assoc] using
              congrArg (fun φ : Tfun.obj (pullback (q i) r) ⟶ Tfun.obj V =>
                φ ((hsq i).isoPullback.inv c)) (hsq i).isoPullback_hom_snd.symm
        _ = (pullback.snd (Tfun.map (q i)) (Tfun.map r)) c := by simp
        _ = x := hc
    have _ : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_iSup_eq_top
      (fun i : I => (Tfun.map (pullback.snd (q i) r)).opensRange) hbCover fun i => ?_
    set e : ((Tfun.map (pullback.snd (q i) r)).opensRange).toScheme ≅
        Tfun.obj (pullback (q i) r) :=
      IsOpenImmersion.isoOfRangeEq ((Tfun.map (pullback.snd (q i) r)).opensRange).ι
        (Tfun.map (pullback.snd (q i) r)) (by simp) with he
    have hfac : e.hom ≫ Tfun.map (pullback.snd (q i) r ≫ p) =
        ((Tfun.map (pullback.snd (q i) r)).opensRange).ι ≫ Tfun.map p := by
      rw [Functor.map_comp, ← Category.assoc]
      exact congrArg (fun y => y ≫ Tfun.map p)
        (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _)
    have hcomp : Etale (e.hom ≫ Tfun.map (pullback.snd (q i) r ≫ p)) := by
      have _ := hbEtale i
      infer_instance
    rw [hfac] at hcomp
    exact hcomp

end AlgebraicGeometry

end
