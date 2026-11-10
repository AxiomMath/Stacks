module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.ChartRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts

/-!
# An affine étale cover on which an object comes from an affine étale piece of a chart

Let `a : (Sch/U₀) ⟶ 𝒳` be a chart of a category fibred in groupoids, representable by algebraic
spaces with surjective smooth base changes (the chart of an algebraic stack, Stacks 026O), and let
`x` be an object of `𝒳` over an affine `T`. Then there are an affine `c` surjective and étale over
`T` by `g`, an affine `W` étale over `U₀` by `s`, a morphism `m : c ⟶ W` and a morphism
`a(s ∘ m) ⟶ x` over `g`.

The base change of `a` along `x` gives a smooth surjective `T₁ ⟶ T` over which `x` comes from `a`
(Stacks 06XH); Stacks 055V refines it by an étale covering, finitely many members of which cover
the quasi-compact `T`; their coproduct is refined by an affine one factoring through affine opens
of `U₀` (`AlgebraicGeometry.BigFppfOver.exists_affine_surjective_etale_refinement_factor`).

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.exists_affine_etale_chart_cover`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A smooth surjective morphism onto an affine is refined by a surjective étale one from a
finite coproduct of objects of the site** (Stacks 055V and quasi-compactness). -/
theorem exists_etale_surjective_factor_of_smooth {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) {T₁ : B.Schemes} (m : T₁ ⟶ T.left)
    (hsm : Smooth (B.inclusion.map m)) (hsurj : Surjective (B.inclusion.map m)) :
    ∃ (c : BigFppfOver B S hS) (d : c ⟶ (Over.mk (m ≫ T.hom) : BigFppfOver B S hS)),
      Surjective ((BigFppfOver.toScheme B S hS).map (d ≫ Over.homMk m rfl)) ∧
        Etale ((BigFppfOver.toScheme B S hS).map (d ≫ Over.homMk m rfl)) := by
  classical
  obtain ⟨I, W, e, hetale, hjs, hfacs⟩ := exists_etaleRefinement_of_smooth_surjective B m hsm hsurj
  choose cc hcc using hfacs
  have hopen : ∀ i, IsOpen (Set.range (B.inclusion.map (e i))) := fun i => by
    have := hetale i
    exact (B.inclusion.map (e i)).isOpenMap.isOpen_range
  have hsub : (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj T)) ⊆
      ⋃ i, Set.range (B.inclusion.map (e i)) := fun t _ => Set.mem_iUnion.2 (hjs t)
  obtain ⟨t, ht⟩ := (CompactSpace.isCompact_univ
    (X := ((BigFppfOver.toScheme B S hS).obj T))).elim_finite_subcover _ hopen hsub
  let idx : ULift.{u} (Fin t.card) → I := fun k => (t.equivFin.symm k.down).1
  let W' : ULift.{u} (Fin t.card) → BigFppfOver B S hS := fun k => Over.mk (e (idx k) ≫ T.hom)
  obtain ⟨c, inj, eiso, he, hdesc⟩ :=
    BigFppfOver.exists_coproduct_of_mk_le_aleph0 (σ := ULift.{u} (Fin t.card))
      Cardinal.mk_le_aleph0 W'
  obtain ⟨d, hd⟩ := hdesc (M := (Over.mk (m ≫ T.hom) : BigFppfOver B S hS))
    (fun k => Over.homMk (cc (idx k)) (by
      change cc (idx k) ≫ m ≫ T.hom = e (idx k) ≫ T.hom
      rw [← Category.assoc, hcc]))
  refine ⟨c, d, ?_⟩
  have key : eiso.hom ≫ (BigFppfOver.toScheme B S hS).map (d ≫ Over.homMk m rfl) =
      Sigma.desc fun k => B.inclusion.map (e (idx k)) := by
    refine Sigma.hom_ext _ _ fun k => ?_
    rw [← Category.assoc, he k, Sigma.ι_comp_desc, ← Functor.map_comp, ← Category.assoc, hd k]
    change B.inclusion.map (cc (idx k) ≫ m) = _
    rw [hcc]
  have _ : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  constructor
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Surjective.{u}) eiso.hom, key]
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_univ_subset ?_)
    refine ht.trans (Set.iUnion₂_subset fun i hi => ?_)
    exact Set.subset_iUnion_of_subset (ULift.up (t.equivFin ⟨i, hi⟩))
      (fun y hy => by
        change y ∈ Set.range (B.inclusion.map (e (t.equivFin.symm (t.equivFin ⟨i, hi⟩)).1))
        rw [Equiv.symm_apply_apply]
        exact hy)
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Etale.{u}) eiso.hom, key]
    exact IsZariskiLocalAtSource.sigmaDesc fun k => hetale (idx k)

/-- **An object over an affine comes, on an affine étale cover, from an affine étale piece of a
chart.** -/
theorem exists_affine_etale_chart_cover
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
      (_hyv : yv ⋙ 𝒳.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) (schemeFibredCategory B S hS U₀).val.p
          𝒳.val.p yv (CatFiberedInGroupoids.homFunctor a))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = T) :
    ∃ (c W : BigFppfOver B S hS) (g : c ⟶ T) (s : W ⟶ U₀) (m : c ⟶ W)
      (θ : (CatFiberedInGroupoids.homFunctor a).obj (Over.mk (m ≫ s)) ⟶ x),
      IsAffine ((BigFppfOver.toScheme B S hS).obj c) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map g) ∧
      Etale ((BigFppfOver.toScheme B S hS).map g) ∧
      Etale ((BigFppfOver.toScheme B S hS).map s) ∧ 𝒳.val.p.IsHomLift g θ := by
  obtain ⟨T₁, m, hmsm, hmsurj, z, φ, hφ⟩ :=
    exists_scheme_lift_of_representable_isSurjective_isSmooth B S hS a hrep hprop T ⟨x, hx⟩
  have hz : z.left = (Over.mk (m ≫ T.hom) : BigFppfOver B S hS) :=
    (BasedFunctor.w_obj a.hom z).symm.trans (IsHomLift.domain_eq 𝒳.val.p (Over.homMk m rfl :
      (Over.mk (m ≫ T.hom) : BigFppfOver B S hS) ⟶ T) φ)
  obtain ⟨L, ⟨⟨⟩⟩, zh⟩ := z
  change L = _ at hz
  subst hz
  obtain ⟨c, d, hds, hde⟩ := exists_etale_surjective_factor_of_smooth hT m hmsm hmsurj
  obtain ⟨c', W, r, s, m', hc', hW, hrs, hre, hse, hms⟩ :=
    BigFppfOver.exists_affine_surjective_etale_refinement_factor hT (d ≫ Over.homMk m rfl)
      hds hde (d ≫ zh)
  let β : (Over.mk (m' ≫ s) : Over U₀) ⟶ Over.mk zh :=
    Over.homMk (r ≫ d) (by
      rw [hms, Category.assoc]
      rfl)
  have hβ : (schemeFibredCategory B S hS U₀).val.p.IsHomLift (r ≫ d) β :=
    IsHomLift.map (Over.forget U₀) β
  have hβ' : 𝒳.val.p.IsHomLift (r ≫ d) ((CatFiberedInGroupoids.homFunctor a).map β) :=
    BasedFunctor.preserves_isHomLift a.hom (r ≫ d) β
  refine ⟨c', W, r ≫ d ≫ Over.homMk m rfl, s, m', (CatFiberedInGroupoids.homFunctor a).map β ≫ φ,
    hc', hW, hrs, hre, hse, ?_⟩
  simpa only [Category.assoc] using IsHomLift.comp 𝒳.val.p (r ≫ d) (Over.homMk m rfl :
    (Over.mk (m ≫ T.hom) : BigFppfOver B S hS) ⟶ T) ((CatFiberedInGroupoids.homFunctor a).map β) φ

end AlgebraicGeometry.Stack.GroupoidLift

end
