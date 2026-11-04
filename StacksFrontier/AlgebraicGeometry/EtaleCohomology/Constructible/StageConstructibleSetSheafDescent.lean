module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleQuasiCompact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDisjointUnionRepresentable
public import StacksFrontier.AlgebraicGeometry.Limits.EtaleChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQcqs
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfSheafifiedYoneda
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructible sheaves of sets on a limit of schemes come from a finite stage

Let `X = lim X_i` be the limit of a cofiltered inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms. This file proves the essential
surjectivity assertion of Tag 09YU, clause (1): every constructible sheaf of sets on `X_étale`
is the inverse image of a constructible sheaf of sets on `(X_i)_étale` for some `i`.

## The source's argument

Tag 09Y9 writes a constructible sheaf of sets `F` on `X_étale` as a coequalizer of two maps
between finite coproducts of sheaves represented by quasi-compact and quasi-separated objects of
`X_étale`. A finite coproduct of such representable sheaves is itself represented — by the
disjoint union of the objects, `Stacks.EtaleCohomology.disjointUnionObj` — so the two maps of the
presentation are, the small étale topology being subcanonical, a parallel pair of *morphisms of
the site* between two quasi-compact quasi-separated objects. Such a parallel pair descends to a
stage: the two objects are base changes of étale charts of a stage by Tag 01ZM part (1) together
with Tag 07RP, and the two morphisms come from a later stage by Tag 01ZC. The coequalizer of the
descended pair of representable sheaves is constructible at that stage by Tag 03RZ and Tag 03S8
part (1), and inverse image, being a left adjoint which commutes with the sheafified Yoneda
embedding, carries it back to `F`.

## Main results

* `AlgebraicGeometry.exists_stage_isPullback_etale_parallelPair` — **a parallel pair of
  morphisms of étale charts of the limit comes from a stage**, for a cofiltered system of
  quasi-compact quasi-separated schemes with affine transition morphisms. This is Tag 01ZC in the
  shape the descent of a diagram, rather than of a single morphism, needs.
* `AlgebraicGeometry.exists_stage_smallEtaleModel_parallelPair_of_qcqs` — the same statement for
  the small étale site of a big étale site: a parallel pair of morphisms between quasi-compact
  and quasi-separated objects of `X_étale` is the small étale base change of a parallel pair at
  a stage, compatibly with the identification of the two objects with base changes.
* `AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleSetSheaf` — **Tag 09YU, clause (1),
  the essential surjectivity assertion.**

## Implementation notes

Tag 01ZC is available as `AlgebraicGeometry.exists_stage_hom_of_hom`, which descends *one*
morphism out of the limit. Both morphisms of the presentation are descended to a *single* stage
by applying it once to the induced morphism into the fibre square of the target chart with
itself: a pair of morphisms `V ⟶ U` over `X_i` is one morphism `V ⟶ U ×_{X_i} U`, and the target
is again étale, hence locally of finite presentation, over `X_i`. This avoids descending the two
morphisms separately and then transporting one of them along a further transition.

The two étale charts are descended separately, by
`AlgebraicGeometry.exists_isPullback_etale_of_etale`, and moved to a common stage by
`AlgebraicGeometry.isPullback_stage_of_isPullback` before the morphisms are descended. The
descended objects are presented as *chosen* fibre products, in the two orders the two cited
results produce them; the comparison of a chosen fibre product with the object of the site it is
isomorphic to is made once, inside the proof, from the uniqueness of a fibre product, so the
isomorphisms `εV` and `εU` of the conclusion are part of the existential statement rather than
canonical maps. That is all the consumer needs: the colimit assertion of Tag 09YU asks for a
sheaf at a stage and *an* isomorphism of its inverse image with the given sheaf.

The note in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/StageColimitCompletion.lean`
saying that essential surjectivity is out of reach is superseded: it was written when Tag 09Y9
was available only with three explicit inputs and before finite coproducts of representables on
the small étale site were identified with representables of disjoint unions. Tag 09Y9 is used
here in its unconditional form,
`isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional`.

Only the essential surjectivity assertion of clause (1) is proved here; its faithfulness
assertion is
`AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleSetSheaf`. Fullness is not proved:
the argument above descends the *presentation* of one sheaf, whereas fullness has to descend a
map between the inverse images of two sheaves already given at a stage, and the comparison of a
map of coequalizers with a map of the presenting coproducts is not supplied by it.

## References

* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

section Charts

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c)

include hc in
/-- **A parallel pair of morphisms of étale charts of the limit comes from a stage.** Let
`X = lim X_i` be the limit of a cofiltered inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, let `V` and `U` be the base changes to `X` of
quasi-compact and quasi-separated schemes `V₀` and `U₀` étale over a stage `X_{i₀}`, and let
`a, b : V ⟶ U` be two morphisms over `X`. Then there are a stage `X_j`, quasi-compact and
quasi-separated schemes `V_j` and `U_j` étale over it whose base changes to `X` are `V` and `U`,
and two morphisms `V_j ⟶ U_j` over `X_j` whose base changes to `X` are `a` and `b`.

This is [Stacks, Tag 01ZC], in the form `AlgebraicGeometry.exists_stage_hom_of_hom`, applied
once to the single morphism `V ⟶ U ×_{X_{i₀}} U` determined by the pair, so that both morphisms
are descended to one and the same stage. The fibre square `U₀ ×_{X_{i₀}} U₀` is again étale over
`X_{i₀}`, hence locally of finite presentation over it, which is what Tag 01ZC asks of its
target. -/
public theorem exists_stage_isPullback_etale_parallelPair (i₀ : I)
    {Vs Us V₀ U₀ : Scheme.{u}} {v : Vs ⟶ c.pt} {u : Us ⟶ c.pt}
    (v₀ : V₀ ⟶ D.obj i₀) (u₀ : U₀ ⟶ D.obj i₀) [Etale v₀] [Etale u₀]
    [CompactSpace V₀] [QuasiSeparatedSpace V₀] [CompactSpace U₀] [QuasiSeparatedSpace U₀]
    {θV : Vs ⟶ V₀} {θU : Us ⟶ U₀}
    (hV : IsPullback θV v v₀ (c.π.app i₀)) (hU : IsPullback θU u u₀ (c.π.app i₀))
    (as bs : Vs ⟶ Us) (has : as ≫ u = v) (hbs : bs ≫ u = v) :
    ∃ (j : I) (Vj Uj : Scheme.{u}) (vj : Vj ⟶ D.obj j) (uj : Uj ⟶ D.obj j)
      (ψa ψb : Vj ⟶ Uj) (κV : Vs ⟶ Vj) (κU : Us ⟶ Uj),
      Etale vj ∧ Etale uj ∧ CompactSpace Vj ∧ QuasiSeparatedSpace Vj ∧
        CompactSpace Uj ∧ QuasiSeparatedSpace Uj ∧
        IsPullback κV v vj (c.π.app j) ∧ IsPullback κU u uj (c.π.app j) ∧
        ψa ≫ uj = vj ∧ ψb ≫ uj = vj ∧
        κV ≫ ψa = as ≫ κU ∧ κV ≫ ψb = bs ≫ κU := by
  have : QuasiCompact v₀ := quasiCompact_of_compactSpace v₀
  have : QuasiSeparated v₀ := QuasiSeparated.of_quasiSeparatedSpace v₀
  have : QuasiCompact u₀ := quasiCompact_of_compactSpace u₀
  have : QuasiSeparated u₀ := QuasiSeparated.of_quasiSeparatedSpace u₀
  have : Etale (pullback.fst u₀ u₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback u₀ u₀).flip ‹Etale u₀›
  have : Etale (pullback.fst u₀ u₀ ≫ u₀) := inferInstance
  have : LocallyOfFinitePresentation (pullback.fst u₀ u₀ ≫ u₀) := inferInstance
  -- the comparison `Vs ≅ X ×_{X_{i₀}} V₀`
  have heVfst : hV.flip.isoPullback.hom ≫ pullback.fst (c.π.app i₀) v₀ = v :=
    hV.flip.isoPullback_hom_fst
  have heVsnd : hV.flip.isoPullback.hom ≫ pullback.snd (c.π.app i₀) v₀ = θV :=
    hV.flip.isoPullback_hom_snd
  have heVinv : hV.flip.isoPullback.inv ≫ v = pullback.fst (c.π.app i₀) v₀ :=
    (congrArg (hV.flip.isoPullback.inv ≫ ·) heVfst).symm.trans (Iso.inv_hom_id_assoc _ _)
  -- the two morphisms, read as a single morphism to the fibre square of `u₀` with itself
  have key : ∀ ws : Vs ⟶ Us, ws ≫ u = v →
      (hV.flip.isoPullback.inv ≫ ws ≫ θU) ≫ u₀ =
        pullback.fst (c.π.app i₀) v₀ ≫ c.π.app i₀ := by
    intro ws hws
    have h1 : (hV.flip.isoPullback.inv ≫ ws ≫ θU) ≫ u₀ =
        hV.flip.isoPullback.inv ≫ ws ≫ θU ≫ u₀ := by simp only [Category.assoc]
    rw [h1, hU.w, ← Category.assoc ws u (c.π.app i₀), hws, ← Category.assoc, heVinv]
  have hab := (key as has).trans (key bs hbs).symm
  have hφ : pullback.lift (hV.flip.isoPullback.inv ≫ as ≫ θU)
        (hV.flip.isoPullback.inv ≫ bs ≫ θU) hab ≫ (pullback.fst u₀ u₀ ≫ u₀) =
      pullback.snd (c.π.app i₀) v₀ ≫ v₀ ≫ 𝟙 (D.obj i₀) := by
    rw [Category.comp_id, ← Category.assoc, pullback.lift_fst, key as has]
    exact pullback.condition
  obtain ⟨k, e, ψ, hψw, hψc⟩ := exists_stage_hom_of_hom D c hc i₀ v₀ (𝟙 (D.obj i₀))
    (pullback.fst u₀ u₀ ≫ u₀) _ hφ
  rw [Category.comp_id] at hψw
  have hcmpfst : stageBaseChangeComparison D c e v₀ ≫ pullback.fst (D.map e) v₀ =
      pullback.fst (c.π.app i₀) v₀ ≫ c.π.app k := pullback.lift_fst _ _ _
  have hcmpsnd : stageBaseChangeComparison D c e v₀ ≫ pullback.snd (D.map e) v₀ =
      pullback.snd (c.π.app i₀) v₀ := pullback.lift_snd _ _ _
  -- the descended parallel pair
  have hwa : (ψ ≫ pullback.fst u₀ u₀) ≫ u₀ = pullback.fst (D.map e) v₀ ≫ D.map e := by
    rw [Category.assoc, hψw, pullback.condition]
  have hwb : (ψ ≫ pullback.snd u₀ u₀) ≫ u₀ = pullback.fst (D.map e) v₀ ≫ D.map e := by
    rw [Category.assoc, ← pullback.condition, hψw, pullback.condition]
  -- the comparisons of the given charts with the base changes of the descended ones
  have hcV : (v ≫ c.π.app k) ≫ D.map e = θV ≫ v₀ := by
    rw [Category.assoc, c.w e, hV.w]
  have hcU : θU ≫ u₀ = (u ≫ c.π.app k) ≫ D.map e := by
    rw [Category.assoc, c.w e, hU.w]
  have hκV : IsPullback (pullback.lift (v ≫ c.π.app k) θV hcV) v
      (pullback.fst (D.map e) v₀) (c.π.app k) := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (D.map e) v₀).flip
    rw [pullback.lift_snd, c.w e]
    exact hV
  have hκU : IsPullback (pullback.lift θU (u ≫ c.π.app k) hcU) u
      (pullback.snd u₀ (D.map e)) (c.π.app k) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback u₀ (D.map e))
    rw [pullback.lift_fst, c.w e]
    exact hU
  have hκVcmp : pullback.lift (v ≫ c.π.app k) θV hcV =
      hV.flip.isoPullback.hom ≫ stageBaseChangeComparison D c e v₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hcmpfst, ← Category.assoc, heVfst]
    · rw [pullback.lift_snd, Category.assoc, hcmpsnd, heVsnd]
  refine ⟨k, pullback (D.map e) v₀, pullback u₀ (D.map e), pullback.fst (D.map e) v₀,
    pullback.snd u₀ (D.map e),
    pullback.lift (ψ ≫ pullback.fst u₀ u₀) (pullback.fst (D.map e) v₀) hwa,
    pullback.lift (ψ ≫ pullback.snd u₀ u₀) (pullback.fst (D.map e) v₀) hwb,
    pullback.lift (v ≫ c.π.app k) θV hcV, pullback.lift θU (u ≫ c.π.app k) hcU,
    inferInstance, inferInstance, inferInstance,
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map e) v₀),
    inferInstance, quasiSeparatedSpace_of_quasiSeparated (pullback.snd u₀ (D.map e)),
    hκV, hκU, pullback.lift_snd _ _ _, pullback.lift_snd _ _ _, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [hκVcmp, Category.assoc, reassoc_of% hψc, pullback.lift_fst, Iso.hom_inv_id_assoc]
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
      rw [← Category.assoc, has]
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [hκVcmp, Category.assoc, reassoc_of% hψc, pullback.lift_snd, Iso.hom_inv_id_assoc]
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
      rw [← Category.assoc, hbs]

end Charts

section SmallEtaleCharts

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- **A parallel pair of morphisms of quasi-compact quasi-separated objects of the small étale
site of the limit comes from a stage.** Let `X = lim X_i` be the limit of a directed inverse
system of quasi-compact and quasi-separated schemes with affine transition morphisms inside a big
étale site, and let `a, b : V ⟶ U` be two morphisms between quasi-compact and quasi-separated
objects of `X_étale`. Then there are a stage `i`, quasi-compact and quasi-separated objects `V_i`
and `U_i` of `(X_i)_étale`, two morphisms `V_i ⟶ U_i` of that site, and isomorphisms of the small
étale base changes of `V_i` and `U_i` with `V` and `U`, through which the base changes of the two
morphisms are `a` and `b`.

This is `AlgebraicGeometry.exists_stage_isPullback_etale_parallelPair` carried over to the small
étale site: the underlying schemes of `V` and `U` are descended by
`AlgebraicGeometry.exists_isPullback_etale_of_etale` — Tag 01ZM part (1) followed by Tag 07RP —
and moved to a common stage by `AlgebraicGeometry.isPullback_stage_of_isPullback`, the descended
schemes lie in the big étale site by Tag 000R (5), and a morphism of the site is determined by
its underlying morphism of schemes. -/
public theorem exists_stage_smallEtaleModel_parallelPair_of_qcqs (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (Vx Ux : SmallEtale B c.pt hX)
    (hVc : CompactSpace Vx.obj.left.obj) (hVq : QuasiSeparatedSpace Vx.obj.left.obj)
    (hUc : CompactSpace Ux.obj.left.obj) (hUq : QuasiSeparatedSpace Ux.obj.left.obj)
    (a b : Vx ⟶ Ux) :
    ∃ (j : I) (Vj Uj : SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
      (ψa ψb : Vj ⟶ Uj)
      (εV : (smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj Vj ≅ Vx)
      (εU : (smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj Uj ≅ Ux),
      CompactSpace Vj.obj.left.obj ∧ QuasiSeparatedSpace Vj.obj.left.obj ∧
        CompactSpace Uj.obj.left.obj ∧ QuasiSeparatedSpace Uj.obj.left.obj ∧
        (smallEtaleBaseChange B (coneStageHom B Dg c hX j)).map ψa =
          εV.hom ≫ a ≫ εU.inv ∧
        (smallEtaleBaseChange B (coneStageHom B Dg c hX j)).map ψb =
          εV.hom ≫ b ≫ εU.inv := by
  classical
  have : IsCofiltered Iᵒᵖ := inferInstance
  have haff' : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) :=
    fun e => haff e
  have hqc' : ∀ p : Iᵒᵖ, CompactSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqc p.unop
  have hqs' : ∀ p : Iᵒᵖ, QuasiSeparatedSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqs p.unop
  have : Etale (B.inclusion.map Vx.obj.hom) := Vx.property
  have : Etale (B.inclusion.map Ux.obj.hom) := Ux.property
  have : CompactSpace (B.inclusion.obj Vx.obj.left) := hVc
  have : QuasiSeparatedSpace (B.inclusion.obj Vx.obj.left) := hVq
  have : CompactSpace (B.inclusion.obj Ux.obj.left) := hUc
  have : QuasiSeparatedSpace (B.inclusion.obj Ux.obj.left) := hUq
  obtain ⟨p₁, U₁, u₁, θU₁, hu₁e, hU₁c, hU₁q, hU₁pb⟩ :=
    exists_isPullback_etale_of_etale (Dg ⋙ B.inclusion) c hc (B.inclusion.map Ux.obj.hom)
  obtain ⟨p₂, V₁, v₁, θV₁, hv₁e, hV₁c, hV₁q, hV₁pb⟩ :=
    exists_isPullback_etale_of_etale (Dg ⋙ B.inclusion) c hc (B.inclusion.map Vx.obj.hom)
  have := hu₁e; have := hU₁c; have := hU₁q
  have := hv₁e; have := hV₁c; have := hV₁q
  have : QuasiCompact u₁ := quasiCompact_of_compactSpace u₁
  have : QuasiSeparated u₁ := QuasiSeparated.of_quasiSeparatedSpace u₁
  have : QuasiCompact v₁ := quasiCompact_of_compactSpace v₁
  have : QuasiSeparated v₁ := QuasiSeparated.of_quasiSeparatedSpace v₁
  obtain ⟨i, h₁, h₂⟩ := directed_of (· ≤ ·) p₁.unop p₂.unop
  have : CompactSpace ((Dg ⋙ B.inclusion).obj (op i)) := hqc' (op i)
  have : QuasiSeparatedSpace ((Dg ⋙ B.inclusion).obj (op i)) := hqs' (op i)
  -- move the two charts to the common stage `i`
  have : QuasiSeparatedSpace
      (pullback u₁ ((Dg ⋙ B.inclusion).map ((homOfLE h₁).op : op i ⟶ p₁)) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd u₁ _)
  have : QuasiSeparatedSpace
      (pullback v₁ ((Dg ⋙ B.inclusion).map ((homOfLE h₂).op : op i ⟶ p₂)) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd v₁ _)
  have hU₂ := isPullback_stage_of_isPullback (Dg ⋙ B.inclusion) c
    ((homOfLE h₁).op : op i ⟶ p₁) hU₁pb
  have hV₂ := isPullback_stage_of_isPullback (Dg ⋙ B.inclusion) c
    ((homOfLE h₂).op : op i ⟶ p₂) hV₁pb
  -- descend the parallel pair
  obtain ⟨k, Vj, Uj, vj, uj, ψa, ψb, κV, κU, hvj, huj, hVjc, hVjq, hUjc, hUjq,
      hκV, hκU, hψauj, hψbuj, hea, heb⟩ :=
    exists_stage_isPullback_etale_parallelPair (Dg ⋙ B.inclusion) c hc (op i)
      (pullback.snd v₁ ((Dg ⋙ B.inclusion).map ((homOfLE h₂).op : op i ⟶ p₂)))
      (pullback.snd u₁ ((Dg ⋙ B.inclusion).map ((homOfLE h₁).op : op i ⟶ p₁)))
      hV₂ hU₂ ((SmallEtale.toScheme B c.pt hX).map a)
      ((SmallEtale.toScheme B c.pt hX).map b)
      (toScheme_map_comp_hom B hX a) (toScheme_map_comp_hom B hX b)
  have := hvj; have := huj; have := hVjc; have := hVjq; have := hUjc; have := hUjq
  have : QuasiCompact vj := quasiCompact_of_compactSpace vj
  have : QuasiCompact uj := quasiCompact_of_compactSpace uj
  -- read the descended charts as objects of the small étale site of the stage
  have hVjB : B.Contains Vj :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact vj (Dg.obj k).property
  have hUjB : B.Contains Uj :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact uj (Dg.obj k).property
  set Vo : SmallEtale B (Dg.obj k).obj (Dg.obj k).property :=
    mkObj B (Dg.obj k).property Vj vj hVjB hvj with hVo
  set Uo : SmallEtale B (Dg.obj k).obj (Dg.obj k).property :=
    mkObj B (Dg.obj k).property Uj uj hUjB huj with hUo
  set pk : B.obj c.pt hX ⟶ Dg.obj k := coneStageHom B Dg c hX k.unop with hpk
  -- the base-change squares of the small étale site, on underlying schemes
  have hsqV : IsPullback (B.inclusion.map (pullback.fst Vo.obj.hom pk))
      (B.inclusion.map ((smallEtaleBaseChange B pk).obj Vo).obj.hom)
      (B.inclusion.map Vo.obj.hom) (B.inclusion.map pk) :=
    (IsPullback.of_hasPullback Vo.obj.hom pk).map B.inclusion
  have hsqU : IsPullback (B.inclusion.map (pullback.fst Uo.obj.hom pk))
      (B.inclusion.map ((smallEtaleBaseChange B pk).obj Uo).obj.hom)
      (B.inclusion.map Uo.obj.hom) (B.inclusion.map pk) :=
    (IsPullback.of_hasPullback Uo.obj.hom pk).map B.inclusion
  have hκV' : IsPullback κV (B.inclusion.map Vx.obj.hom) (B.inclusion.map Vo.obj.hom)
      (B.inclusion.map pk) := hκV
  have hκU' : IsPullback κU (B.inclusion.map Ux.obj.hom) (B.inclusion.map Uo.obj.hom)
      (B.inclusion.map pk) := hκU
  -- the comparison isomorphisms, built from uniqueness of a fibre product
  set e₀V := hsqV.isoIsPullback _ _ hκV' with he₀V
  set e₀U := hsqU.isoIsPullback _ _ hκU' with he₀U
  have he₀Vhom : e₀V.hom ≫ κV = B.inclusion.map (pullback.fst Vo.obj.hom pk) :=
    hsqV.isoIsPullback_hom_fst _ _ hκV'
  have he₀Uinv : e₀U.inv ≫ B.inclusion.map (pullback.fst Uo.obj.hom pk) = κU :=
    hsqU.isoIsPullback_inv_fst _ _ hκU'
  have he₀Vsnd : e₀V.hom ≫ B.inclusion.map Vx.obj.hom =
      B.inclusion.map ((smallEtaleBaseChange B pk).obj Vo).obj.hom :=
    hsqV.isoIsPullback_hom_snd _ _ hκV'
  have he₀Usnd : e₀U.hom ≫ B.inclusion.map Ux.obj.hom =
      B.inclusion.map ((smallEtaleBaseChange B pk).obj Uo).obj.hom :=
    hsqU.isoIsPullback_hom_snd _ _ hκU'
  -- an object of the small étale site presented by a cartesian square is the base change
  have mkIso : ∀ (W : SmallEtale B (Dg.obj k).obj (Dg.obj k).property)
      (Z : SmallEtale B c.pt hX)
      (e₀ : B.inclusion.obj ((smallEtaleBaseChange B pk).obj W).obj.left ≅
        B.inclusion.obj Z.obj.left),
      e₀.hom ≫ B.inclusion.map Z.obj.hom =
        B.inclusion.map ((smallEtaleBaseChange B pk).obj W).obj.hom →
      ∃ ε : (smallEtaleBaseChange B pk).obj W ≅ Z,
        (SmallEtale.toScheme B c.pt hX).map ε.hom = e₀.hom ∧
          (SmallEtale.toScheme B c.pt hX).map ε.inv = e₀.inv := by
    intro W Z e₀ hw
    have hpre : B.inclusion.map (B.inclusion.preimageIso e₀).hom = e₀.hom :=
      B.inclusion.map_preimage _
    have hpreinv : B.inclusion.map (B.inclusion.preimageIso e₀).inv = e₀.inv :=
      B.inclusion.map_preimage _
    have hw' : (B.inclusion.preimageIso e₀).hom ≫ Z.obj.hom =
        ((smallEtaleBaseChange B pk).obj W).obj.hom :=
      B.inclusion.map_injective <| (B.inclusion.map_comp _ _).trans
        ((congrArg (· ≫ B.inclusion.map Z.obj.hom) hpre).trans hw)
    refine ⟨(SmallEtale.inclusion B c.pt hX).preimageIso
      (Over.isoMk (B.inclusion.preimageIso e₀) hw'), ?_, ?_⟩
    · refine Eq.trans ?_ hpre
      exact congrArg (fun t : ((smallEtaleBaseChange B pk).obj W).obj ⟶ Z.obj =>
        B.inclusion.map t.left)
        ((SmallEtale.inclusion B c.pt hX).map_preimage
          (X := (smallEtaleBaseChange B pk).obj W) (Y := Z)
          (Over.isoMk (B.inclusion.preimageIso e₀) hw').hom)
    · refine Eq.trans ?_ hpreinv
      exact congrArg (fun t : Z.obj ⟶ ((smallEtaleBaseChange B pk).obj W).obj =>
        B.inclusion.map t.left)
        ((SmallEtale.inclusion B c.pt hX).map_preimage
          (X := Z) (Y := (smallEtaleBaseChange B pk).obj W)
          (Over.isoMk (B.inclusion.preimageIso e₀) hw').inv)
  obtain ⟨εV, hεVmap, -⟩ := mkIso Vo Vx e₀V he₀Vsnd
  obtain ⟨εU, -, hεUmap⟩ := mkIso Uo Ux e₀U he₀Usnd
  -- base change of a morphism, on underlying schemes
  have hbcfst : ∀ (W W' : SmallEtale B (Dg.obj k).obj (Dg.obj k).property) (g : W ⟶ W'),
      (SmallEtale.toScheme B c.pt hX).map ((smallEtaleBaseChange B pk).map g) ≫
          B.inclusion.map (pullback.fst W'.obj.hom pk) =
        B.inclusion.map (pullback.fst W.obj.hom pk) ≫
          (SmallEtale.toScheme B (Dg.obj k).obj (Dg.obj k).property).map g := by
    intro W W' g
    show B.inclusion.map (((Over.pullback pk).map g.hom).left) ≫
        B.inclusion.map (pullback.fst W'.obj.hom pk) =
      B.inclusion.map (pullback.fst W.obj.hom pk) ≫ B.inclusion.map g.hom.left
    rw [← B.inclusion.map_comp, ← B.inclusion.map_comp]
    refine congrArg B.inclusion.map ?_
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have hmain : ∀ (w : Vx ⟶ Ux) (ws : Vj ⟶ Uj) (hws : ws ≫ uj = vj),
      κV ≫ ws = (SmallEtale.toScheme B c.pt hX).map w ≫ κU →
      (smallEtaleBaseChange B pk).map
          (mkHom B (Dg.obj k).property (V := Vo) (W := Uo) ws hws) =
        εV.hom ≫ w ≫ εU.inv := by
    intro w ws hws hcompat
    refine Stacks.EtaleCohomology.hom_ext B hX (hsqU.hom_ext ?_ ?_)
    · have hlhs : (SmallEtale.toScheme B c.pt hX).map
          ((smallEtaleBaseChange B pk).map
            (mkHom B (Dg.obj k).property (V := Vo) (W := Uo) ws hws)) ≫
            B.inclusion.map (pullback.fst Uo.obj.hom pk) =
          e₀V.hom ≫ (SmallEtale.toScheme B c.pt hX).map w ≫ κU := by
        rw [hbcfst Vo Uo (mkHom B (Dg.obj k).property (V := Vo) (W := Uo) ws hws)]
        show B.inclusion.map (pullback.fst Vo.obj.hom pk) ≫ ws =
          e₀V.hom ≫ (SmallEtale.toScheme B c.pt hX).map w ≫ κU
        calc B.inclusion.map (pullback.fst Vo.obj.hom pk) ≫ ws
            = (e₀V.hom ≫ κV) ≫ ws := congrArg (· ≫ ws) he₀Vhom.symm
          _ = e₀V.hom ≫ κV ≫ ws := Category.assoc _ _ _
          _ = e₀V.hom ≫ (SmallEtale.toScheme B c.pt hX).map w ≫ κU := by rw [hcompat]
      have hrhs : (SmallEtale.toScheme B c.pt hX).map (εV.hom ≫ w ≫ εU.inv) ≫
            B.inclusion.map (pullback.fst Uo.obj.hom pk) =
          e₀V.hom ≫ (SmallEtale.toScheme B c.pt hX).map w ≫ κU := by
        rw [Functor.map_comp, Functor.map_comp, hεVmap, hεUmap, Category.assoc,
          Category.assoc]
        exact congrArg (fun t => e₀V.hom ≫ (SmallEtale.toScheme B c.pt hX).map w ≫ t) he₀Uinv
      exact hlhs.trans hrhs.symm
    · exact (toScheme_map_comp_hom B hX _).trans (toScheme_map_comp_hom B hX _).symm
  exact ⟨k.unop, Vo, Uo, mkHom B (Dg.obj k).property (V := Vo) (W := Uo) ψa hψauj,
    mkHom B (Dg.obj k).property (V := Vo) (W := Uo) ψb hψbuj, εV, εU, hVjc, hVjq, hUjc, hUjq,
    hmain a ψa hψauj hea, hmain b ψb hψbuj heb⟩

end SmallEtaleCharts

section EssSurj

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- **Stacks 09YU, clause (1), the essential surjectivity assertion.** Let `X = lim X_i` be the
limit of a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms inside a big étale site. Every constructible sheaf of sets on `X_étale` is
isomorphic to the inverse image of a constructible sheaf of sets on `(X_i)_étale` for some `i`.

Tag 09Y9 presents the sheaf as a coequalizer of two maps between finite coproducts of sheaves
represented by quasi-compact and quasi-separated objects; those coproducts are represented by the
disjoint unions of the objects, so the two maps are a parallel pair of morphisms of the site,
which descends to a stage by
`AlgebraicGeometry.exists_stage_smallEtaleModel_parallelPair_of_qcqs`. The coequalizer of the
descended pair of representable sheaves is constructible at that stage by Tag 03RZ and Tag 03S8
part (1), and inverse image, a left adjoint commuting with the sheafified Yoneda embedding,
carries it to the given sheaf. -/
@[stacks 09YU "clause (1), the essential surjectivity assertion",
  sga "4 IX 2.7.4" "partial, special case"]
public theorem smallEtaleStagesEssSurj_isConstructibleSetSheaf (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B (Type (u + 1)) Dg c hX
      (fun X => IsConstructibleSetSheaf B X) := by
  classical
  have haff' : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) :=
    fun e => haff e
  have hqc' : ∀ p : Iᵒᵖ, CompactSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqc p.unop
  have hqs' : ∀ p : Iᵒᵖ, QuasiSeparatedSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqs p.unop
  have : IsCofiltered Iᵒᵖ := inferInstance
  obtain ⟨hcpt, hqpt⟩ := compactSpace_and_quasiSeparatedSpace_pt (Dg ⋙ B.inclusion) c hc
  have := hcpt
  have := hqpt
  intro F hF
  let : HasFiniteColimits (Sheaf (SmallEtale.topology B c.pt hX) (Type (u + 1))) :=
    CategoryTheory.Sheaf.instHasFiniteColimits
  have hcolx : ∀ p : ℕ, HasColimitsOfShape (Discrete (Fin p))
      (Sheaf (SmallEtale.topology B c.pt hX) (Type (u + 1))) :=
    fun _ => HasFiniteColimits.out _
  have : HasColimitsOfShape WalkingParallelPair
      (Sheaf (SmallEtale.topology B c.pt hX) (Type (u + 1))) := HasFiniteColimits.out _
  -- Stacks 09Y9: a coequalizer presentation by finite coproducts of qcqs representables
  obtain ⟨n, m, Ufam, Vfam, hUfam, hVfam, f, g, ⟨co⟩⟩ :=
    (isConstructibleSetSheaf_iff_hasFiniteQCSRepresentableCoequalizerPresentation_unconditional
      B (B.obj c.pt hX) F).mp hF
  have : ∀ i, CompactSpace ((SmallEtale.toScheme B c.pt hX).obj (Ufam i)) :=
    fun i => (hUfam i).1
  have : ∀ i, QuasiSeparatedSpace ((SmallEtale.toScheme B c.pt hX).obj (Ufam i)) :=
    fun i => (hUfam i).2
  have : ∀ j, CompactSpace ((SmallEtale.toScheme B c.pt hX).obj (Vfam j)) :=
    fun j => (hVfam j).1
  have : ∀ j, QuasiSeparatedSpace ((SmallEtale.toScheme B c.pt hX).obj (Vfam j)) :=
    fun j => (hVfam j).2
  -- the two maps of the presentation are morphisms of the site between disjoint unions
  obtain ⟨aa, haa, -⟩ :=
    Stacks.EtaleCohomology.existsUnique_hom_disjointUnionObj_of_hom_sigma B hX Ufam Vfam f
  obtain ⟨bb, hbb, -⟩ :=
    Stacks.EtaleCohomology.existsUnique_hom_disjointUnionObj_of_hom_sigma B hX Ufam Vfam g
  have hUxc : CompactSpace
      ((SmallEtale.toScheme B c.pt hX).obj (Stacks.EtaleCohomology.disjointUnionObj B hX Ufam)) :=
    compactSpace_sigmaObj _
  have hUxq : QuasiSeparatedSpace
      ((SmallEtale.toScheme B c.pt hX).obj (Stacks.EtaleCohomology.disjointUnionObj B hX Ufam)) :=
    quasiSeparatedSpace_sigmaObj _
  have hVxc : CompactSpace
      ((SmallEtale.toScheme B c.pt hX).obj (Stacks.EtaleCohomology.disjointUnionObj B hX Vfam)) :=
    compactSpace_sigmaObj _
  have hVxq : QuasiSeparatedSpace
      ((SmallEtale.toScheme B c.pt hX).obj (Stacks.EtaleCohomology.disjointUnionObj B hX Vfam)) :=
    quasiSeparatedSpace_sigmaObj _
  -- descend the parallel pair to a stage
  obtain ⟨k, Vj, Uj, ψa, ψb, εV, εU, hVjc, hVjq, hUjc, hUjq, hea, heb⟩ :=
    exists_stage_smallEtaleModel_parallelPair_of_qcqs B Dg c hX hc haff hqc hqs
      (Stacks.EtaleCohomology.disjointUnionObj B hX Vfam)
      (Stacks.EtaleCohomology.disjointUnionObj B hX Ufam)
      hVxc hVxq hUxc hUxq aa bb
  have := hVjc; have := hVjq; have := hUjc; have := hUjq
  have : CompactSpace (Dg.obj (op k)).obj := hqc k
  have : QuasiSeparatedSpace (Dg.obj (op k)).obj := hqs k
  set Jk := SmallEtale.topology B (Dg.obj (op k)).obj (Dg.obj (op k)).property with hJk
  set Jx := SmallEtale.topology B c.pt hX with hJx
  let : HasFiniteColimits (Sheaf Jk (Type (u + 1))) :=
    CategoryTheory.Sheaf.instHasFiniteColimits
  have : HasColimitsOfShape WalkingParallelPair (Sheaf Jk (Type (u + 1))) :=
    HasFiniteColimits.out _
  set hk := Sheaf.sheafifiedYoneda Jk with hhk
  set hx := Sheaf.sheafifiedYoneda Jx with hhx
  set P := smallEtaleSheafPullback B (Type (u + 1)) (coneStageHom B Dg c hX k) with hP
  set ρ := Sheaf.sheafifiedYonedaCompSheafPullbackIso
    (smallEtaleBaseChange B (coneStageHom B Dg c hX k)) Jk Jx with hρ
  have : PreservesColimits P :=
    ((smallEtaleBaseChange B (coneStageHom B Dg c hX k)).sheafAdjunctionContinuous (Type (u + 1)) Jk
      Jx).leftAdjoint_preservesColimits
  -- the stage sheaf
  refine ⟨k, coequalizer (hk.map ψa) (hk.map ψb), ?_, ?_⟩
  · refine isConstructibleSetSheaf_colimit B (Dg.obj (op k))
      (parallelPair (hk.map ψa) (hk.map ψb)) ?_
    intro i
    cases i with
    | zero => exact isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B (Dg.obj (op k)) Vj
    | one => exact isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B (Dg.obj (op k)) Uj
  -- the inverse image of the stage sheaf is the given sheaf
  obtain ⟨ηV, hηVhom⟩ : ∃ ηV : P.obj (hk.obj Vj) ≅ (∐ fun j => hx.obj (Vfam j)),
      ηV.hom = (ρ.app Vj).hom ≫ hx.map εV.hom ≫
        (Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion B hX Vfam).inv :=
    ⟨ρ.app Vj ≪≫ hx.mapIso εV ≪≫
      (Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion B hX Vfam).symm, rfl⟩
  obtain ⟨ηU, hηUhom⟩ : ∃ ηU : P.obj (hk.obj Uj) ≅ (∐ fun i => hx.obj (Ufam i)),
      ηU.hom = (ρ.app Uj).hom ≫ hx.map εU.hom ≫
        (Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion B hX Ufam).inv :=
    ⟨ρ.app Uj ≪≫ hx.mapIso εU ≪≫
      (Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion B hX Ufam).symm, rfl⟩
  have comm : ∀ (w : Stacks.EtaleCohomology.disjointUnionObj B hX Vfam ⟶
        Stacks.EtaleCohomology.disjointUnionObj B hX Ufam) (ψ : Vj ⟶ Uj),
      (smallEtaleBaseChange B (coneStageHom B Dg c hX k)).map ψ = εV.hom ≫ w ≫ εU.inv →
      ∀ φ : (∐ fun j => hx.obj (Vfam j)) ⟶ (∐ fun i => hx.obj (Ufam i)),
        hx.map w = (Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion
            B hX Vfam).inv ≫ φ ≫
          (Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion B hX Ufam).hom →
        ηV.hom ≫ φ = P.map (hk.map ψ) ≫ ηU.hom := by
    intro w ψ hψ φ hw
    have hnat : P.map (hk.map ψ) ≫ (ρ.app Uj).hom =
        (ρ.app Vj).hom ≫
          hx.map ((smallEtaleBaseChange B (coneStageHom B Dg c hX k)).map ψ) :=
      ρ.hom.naturality ψ
    have h1 : hx.map ((smallEtaleBaseChange B (coneStageHom B Dg c hX k)).map ψ) ≫ hx.map εU.hom =
        hx.map εV.hom ≫ hx.map w := by
      rw [← hx.map_comp, ← hx.map_comp, hψ]
      refine congrArg hx.map ?_
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hηVhom, hηUhom, ← Category.assoc (P.map (hk.map ψ)), hnat]
    simp only [Category.assoc]
    rw [reassoc_of% h1, hw]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- transport the coequalizer along the comparison isomorphisms
  have hcolim : IsColimit (Cofork.ofπ (P.map (coequalizer.π (hk.map ψa) (hk.map ψb)))
      (by rw [← P.map_comp, ← P.map_comp, coequalizer.condition]) :
      Cofork (P.map (hk.map ψa)) (P.map (hk.map ψb))) :=
    isColimitCoforkMapOfIsColimit P (coequalizer.condition (hk.map ψa) (hk.map ψb))
      (coequalizerIsCoequalizer (hk.map ψa) (hk.map ψb))
  have hη : ∀ (φ : (∐ fun j => hx.obj (Vfam j)) ⟶ (∐ fun i => hx.obj (Ufam i))) (ψ : Vj ⟶ Uj),
      ηV.hom ≫ φ = P.map (hk.map ψ) ≫ ηU.hom → φ ≫ ηU.inv = ηV.inv ≫ P.map (hk.map ψ) := by
    intro φ ψ h
    rw [← cancel_epi ηV.hom, ← Category.assoc, h]
    simp
  have hcond : f ≫ ηU.inv ≫ P.map (coequalizer.π (hk.map ψa) (hk.map ψb)) =
      g ≫ ηU.inv ≫ P.map (coequalizer.π (hk.map ψa) (hk.map ψb)) := by
    rw [← Category.assoc, ← Category.assoc, hη f ψa (comm aa ψa hea f haa),
      hη g ψb (comm bb ψb heb g hbb), Category.assoc, Category.assoc, ← P.map_comp, ← P.map_comp,
      coequalizer.condition]
  exact ⟨(IsColimit.coconePointUniqueUpToIso (colimit.isColimit (parallelPair f g))
    (Cofork.isColimitOfIsos _ hcolim
      (Cofork.ofπ (ηU.inv ≫ P.map (coequalizer.π (hk.map ψa) (hk.map ψb))) hcond)
      ηV ηU (Iso.refl _) (comm aa ψa hea f haa) (comm bb ψb heb g hbb)
      (by rw [Cofork.π_ofπ, Cofork.π_ofπ, Iso.refl_hom, Category.comp_id]))).symm ≪≫ co⟩

end EssSurj

end AlgebraicGeometry

end
