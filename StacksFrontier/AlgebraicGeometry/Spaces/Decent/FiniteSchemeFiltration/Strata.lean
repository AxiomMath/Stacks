module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration.DegreeFiltration
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ResidueDegreeBound

/-!
# Filtrations of a quasi-compact algebraic space by scheme strata

A quasi-compact algebraic space admits a descending filtration by open subspaces
whose reduced strata have separated scheme étale neighborhoods that are
isomorphisms over the strata; in particular those strata are schemes. Every point
represented by a quasi-compact morphism from the spectrum of a field lies in one
of the strata. When the space is in addition reasonable the filtration reaches
the empty subspace after finitely many steps, and when it is quasi-compact and
quasi-separated the neighborhoods may be taken quasi-compact as well.

The open subspaces are indexed from zero, so `U 0` is the whole space. Each stratum is the
reduced closed subspace of `U p` with support the complement of `U (p + 1)`, and the
isomorphism over the stratum is the canonical projection from its pullback along the étale
neighborhood. When the affine étale chart has universally bounded fibres, the degree
filtration reaches a member with no points.

This is the last part of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration`.

## Main results

* `AlgebraicGeometry.Space.exists_schemeStratification_quasiCompactPoint_mem_stratum`
  gives the filtration, the étale scheme neighborhoods of its strata and the
  membership of quasi-compact field-valued points in the strata, for a
  quasi-compact space.
* `AlgebraicGeometry.Space.exists_finiteFiltration_of_isQuasiCompactSpace`
  gives the filtration and the quasi-compact étale scheme neighborhoods, for a
  quasi-compact quasi-separated space.
* `AlgebraicGeometry.Space.exists_finiteFiltration_of_isReasonableSpace`
  gives the filtration and the étale scheme neighborhoods, for a quasi-compact
  reasonable space.
* `AlgebraicGeometry.Space.exists_finiteFiltration_isRepresentable_strata`
  gives the filtration and the representability of its strata, for a
  quasi-compact reasonable space.

## References

* [Stacks Project, Tag 0BBN](https://stacks.math.columbia.edu/tag/0BBN)
* [Stacks Project, Tag 07S9](https://stacks.math.columbia.edu/tag/07S9)
* [Stacks Project, Tag 07SA](https://stacks.math.columbia.edu/tag/07SA)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
* [GruRay, Proposition 5.7.8]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁

namespace AlgebraicGeometry.Space

/-- A cone over a pullback square in presheaves with a representable corner and a
representable second leg is induced by a morphism of the representing objects. -/
private theorem exists_comp_eq_of_isPullback_yoneda {C : Type u₁} [Category.{v₁} C]
    {F H : Cᵒᵖ ⥤ Type v₁} {R T W : C} {fst : yoneda.obj R ⟶ F} {snd : R ⟶ T}
    {f : F ⟶ H} {g : yoneda.obj T ⟶ H} (hpb : IsPullback fst (yoneda.map snd) f g)
    (u : yoneda.obj W ⟶ F) (v : W ⟶ T) (h : u ≫ f = yoneda.map v ≫ g) :
    ∃ s : W ⟶ R, yoneda.map s ≫ fst = u ∧ s ≫ snd = v :=
  ⟨yoneda.preimage (hpb.lift u (yoneda.map v) h),
    by rw [Functor.map_preimage, hpb.lift_fst],
    yoneda.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hpb.lift_snd])⟩

/-- A chain with the degree property of
`AlgebraicGeometry.Space.HasDistinctChartPoints` relative to a chart whose fibres are
universally bounded in the sense of Stacks 03JL reaches a member with no points. -/
private theorem exists_pos_isEmpty_points_of_hasUniversallyBoundedFibers
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A : AlgebraicGeometry.BigFppfOver B S hS} (a : yoneda.obj A ⟶ X)
    (hBounded : AlgebraicGeometry.Space.HasUniversallyBoundedFibers B S hS A a)
    (D : ℕ → Subfunctor X) (hD : HasDistinctChartPoints B S hS a D) :
    ∃ n : ℕ, 0 < n ∧
      IsEmpty (AlgebraicGeometry.Space.points B S hS (D n).toFunctor) := by
  obtain ⟨N, hN⟩ := hBounded
  refine ⟨N.toNat + 1, Nat.succ_pos _, ⟨?_⟩⟩
  intro y
  let q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨z, hz⟩ := Quot.exists_rep (AlgebraicGeometry.Space.pointsMap B S hS
    (D (N.toNat + 1)).toFunctor (D (N.toNat + 1)).ι y)
  obtain ⟨r, e, c, hre, hcinj, hca⟩ := hD (N.toNat + 1) _ ⟨y, rfl⟩ z hz
  let T := r.siteObject B S hS X
  obtain ⟨R, pr, ι, rk, hrkN, hrk, hpb⟩ :=
    hN r.carrier T (Iso.refl _) (AlgebraicGeometry.Space.fieldMorphism B S hS X r)
  choose s hs₁ hs₂ using fun j : Fin (N.toNat + 1 + 1) ↦
    exists_comp_eq_of_isPullback_yoneda hpb (yoneda.map (c j)) (𝟙 T)
      (by rw [hca j, yoneda.map_id, Category.id_comp])
  have hs : Function.Injective (fun j ↦ q.map (s j)) := by
    intro j k hjk
    apply hcinj
    apply yoneda.map_injective
    rw [← hs₁ j, ← hs₁ k, q.map_injective hjk]
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (q.map pr) rk := hrk
  have hcard := card_sections_le_rank (q.map pr) rk
    (fun j ↦ q.map (s j)) hs (fun j ↦ by rw [← q.map_comp, hs₂, q.map_id]; rfl)
  omega

/-- The degree filtration of a quasi-compact algebraic space whose fixed affine étale
atlas has universally bounded fibres, together with the separated symmetric-power étale
covers of its steps and the index at which it reaches the empty open subspace. -/
private theorem exists_degreeFiltration_symmetricPower_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (A : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj A ⟶ X)
    (hA : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A))
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : AlgebraicGeometry.Space.IsEtale B S hS a)
    (hBounded : AlgebraicGeometry.Space.HasUniversallyBoundedFibers B S hS A a) :
    ∃ (n : ℕ) (D : ℕ → Subfunctor X)
      (V : ℕ → AlgebraicGeometry.BigFppfOver B S hS)
      (h : ∀ p, yoneda.obj (V p) ⟶ (D p).toFunctor),
      0 < n ∧
      D 0 = ⊤ ∧
      D n = (⊥ : Subfunctor X).sheafify
        (AlgebraicGeometry.BigFppfOver.topology B S hS) ∧
      (∀ p, D (p + 1) ≤ D p) ∧
      (∀ p, AlgebraicGeometry.Space.IsOpenSubspace B S hS (D p)) ∧
      (AlgebraicGeometry.Space.IsQuasiCompact B S hS a →
        ∀ p, CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (V p))) ∧
      (∀ p, Scheme.IsSeparated
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (V p))) ∧
      (∀ p, (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (h p)) ∧
      (∀ p, AlgebraicGeometry.Space.IsEtale B S hS (h p)) ∧
      (∀ (p : ℕ) (Z : Subfunctor (D p).toFunctor),
        AlgebraicGeometry.Space.IsClosedSubspace B S hS Z →
        AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS Z.toFunctor
          (fun Y : Scheme.{u} => IsReduced Y) →
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS Z.toFunctor (Z.ι ≫ (D p).ι)) =
          Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι) \
            Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D (p + 1)).toFunctor
              (D (p + 1)).ι) →
        IsIso (pullback.fst Z.ι (h p))) := by
  obtain ⟨D, V, h, hDzero, hDmono, hDopen, hVcompact, hVsep, hsurj, hetale, hiso, hdeg⟩ :=
    exists_degreeFiltration_symmetricPower_cover_of_quasiCompact B S hS X hX A a hA
      haSurj haEtale
  obtain ⟨n, hn, hempty⟩ :=
    exists_pos_isEmpty_points_of_hasUniversallyBoundedFibers B S hS a hBounded D hdeg
  exact ⟨n, D, V, h, hn, hDzero,
    subfunctor_eq_sheafify_bot_of_isEmpty_points B S hS hX (D n) (hDopen n).1 hempty,
    hDmono, hDopen, hVcompact, hVsep, hsurj, hetale, hiso⟩

/-- The reduced strata of a descending chain of open subspaces of an algebraic
space: for each `p` the reduced closed subspace of the `p`-th step supported on
the points of that step which are not points of the next one. -/
private theorem exists_reducedClosedStrata
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (D : ℕ → Subfunctor X)
    (hDopen : ∀ p, AlgebraicGeometry.Space.IsOpenSubspace B S hS (D p)) :
    ∃ T : ∀ p : ℕ, Subfunctor (D p).toFunctor, ∀ p : ℕ,
      AlgebraicGeometry.Space.IsClosedSubspace B S hS (T p) ∧
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (T p).toFunctor
          ((T p).ι ≫ (D p).ι)) =
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι) \
          Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D (p + 1)).toFunctor
            (D (p + 1)).ι) ∧
      AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (T p).toFunctor
        (fun Y : Scheme.{u} => IsReduced Y) := by
  classical
  let _ : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
    AlgebraicGeometry.Space.pointTopology B S hS X
  let str : ℕ → Set (AlgebraicGeometry.Space.points B S hS X) := fun p ↦
    Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι) \
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D (p + 1)).toFunctor (D (p + 1)).ι)
  have hclosed : ∀ p : ℕ,
      @IsClosed _ (AlgebraicGeometry.Space.pointTopology B S hS (D p).toFunctor)
        (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι ⁻¹' str p) := by
    intro p
    let _ : TopologicalSpace (AlgebraicGeometry.Space.points B S hS (D p).toFunctor) :=
      AlgebraicGeometry.Space.pointTopology B S hS (D p).toFunctor
    have hpre : AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι ⁻¹' str p =
        (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι ⁻¹'
          Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D (p + 1)).toFunctor
            (D (p + 1)).ι))ᶜ := by
      ext z
      simp only [str, Set.mem_preimage, Set.mem_sdiff, Set.mem_compl_iff,
        Set.mem_range]
      exact ⟨fun hz hcon ↦ hz.2 hcon, fun hz ↦ ⟨⟨z, rfl⟩, hz⟩⟩
    rw [hpre]
    refine IsOpen.isClosed_compl ?_
    refine IsOpen.preimage ?_ (isOpen_range_pointsMap_of_openSubspace B S hS hX
      (D (p + 1)) (hDopen (p + 1)))
    exact (AlgebraicGeometry.Space.pointTopologyFamily B S hS).continuous (hDopen p).1 hX (D p).ι
  let T : ∀ p : ℕ, Subfunctor (D p).toFunctor := fun p ↦
    AlgebraicGeometry.Space.reducedClosedSubspace B S hS (D p).toFunctor (hDopen p).1
      (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι ⁻¹' str p)
      (hclosed p)
  have hTspec : ∀ p : ℕ,
      AlgebraicGeometry.Space.IsClosedSubspace B S hS (T p) ∧
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (T p).toFunctor (T p).ι) =
          (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι ⁻¹' str p) ∧
        AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (T p).toFunctor
          (fun Y : Scheme.{u} ↦ IsReduced Y) := fun p ↦
    ⟨AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace B S hS
        (D p).toFunctor (hDopen p).1 _ (hclosed p),
      AlgebraicGeometry.Space.range_pointsMap_ι_reducedClosedSubspace B S hS
        (D p).toFunctor (hDopen p).1 _ (hclosed p),
      AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS
        (D p).toFunctor (hDopen p).1 _ (hclosed p)⟩
  have hTrange : ∀ p : ℕ,
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (T p).toFunctor
        ((T p).ι ≫ (D p).ι)) = str p := by
    intro p
    rw [AlgebraicGeometry.Space.pointsMap_comp B S hS (T p).toFunctor (T p).ι (D p).ι,
      Set.range_comp,
      (hTspec p).2.1, Set.image_preimage_eq_inter_range]
    have hsub : str p ⊆
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D p).toFunctor (D p).ι) :=
      fun y hy ↦ hy.1
    exact Set.inter_eq_self_of_subset_left hsub
  exact ⟨T, fun p ↦ ⟨(hTspec p).1, hTrange p, (hTspec p).2.2⟩⟩

/-- A chain with the degree property of
`AlgebraicGeometry.Space.HasDistinctChartPoints` relative to an affine étale chart has a
member avoiding any given point which a quasi-compact morphism from the spectrum of a
field represents. -/
private theorem exists_notMem_range_pointsMap_of_isQuasiCompact_fieldMorphism
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A : AlgebraicGeometry.BigFppfOver B S hS} (a : yoneda.obj A ⟶ X)
    (hA : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A))
    (haEtale : AlgebraicGeometry.Space.IsEtale B S hS a)
    (D : ℕ → Subfunctor X) (hD : HasDistinctChartPoints B S hS a D)
    (z : AlgebraicGeometry.Space.FieldValuedPoint B S hS X)
    (hz : AlgebraicGeometry.Space.IsQuasiCompact B S hS
      (AlgebraicGeometry.Space.fieldMorphism B S hS X z)) :
    ∃ n : ℕ, z.class B S hS X ∉
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D n).toFunctor (D n).ι) := by
  let q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : IsAffine (q.obj A) := hA
  have hap := AlgebraicGeometry.Space.presheaf_etale_of_isEtale B S hS haEtale
  let ψ := AlgebraicGeometry.Space.fieldMorphism B S hS X z
  have hpb := hap.rep.isPullback ψ
  let : Etale (q.map (hap.rep.snd ψ)) := hap.property_snd ψ
  let : CompactSpace (q.obj (hap.rep.pullback ψ)) :=
    AlgebraicGeometry.Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (AlgebraicGeometry.Space.isQuasiCompactSpace_of_iso B S hS
        ((IsPullback.of_hasPullback a ψ).isoIsPullback _ _ hpb)
        (hz (yoneda.obj A) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A)
          (AlgebraicGeometry.Space.isQuasiCompactSpace_yoneda_obj B S hS
            (Scheme.compactSpace_of_isAffine _)) a))
  let : Subsingleton (q.obj (z.siteObject B S hS X)) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of z.carrier)))
  let : Finite (q.obj (hap.rep.pullback ψ)) :=
    AlgebraicGeometry.finite_of_etale_of_subsingleton (q.map (hap.rep.snd ψ))
  let := ((Scheme.ΓSpecIso (.of z.carrier)).inv ≫
    (q.map (hap.rep.snd ψ)).appTop).hom.toAlgebra
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (q.map (hap.rep.snd ψ))
      (Module.finrank z.carrier Γ(q.obj (hap.rep.pullback ψ), ⊤)) :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_of_etale_of_finite z.carrier
      (q.map (hap.rep.snd ψ))
  refine ⟨Module.finrank z.carrier Γ(q.obj (hap.rep.pullback ψ), ⊤), fun hmem ↦ ?_⟩
  obtain ⟨r, e, c, hre, hcinj, hca⟩ := hD _ _ hmem z rfl
  choose d hd₁ hd₂ using
    fun j : Fin (Module.finrank z.carrier Γ(q.obj (hap.rep.pullback ψ), ⊤) + 1) ↦
    exists_comp_eq_of_isPullback_yoneda hpb (yoneda.map (c j)) e (by rw [hca j, hre])
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.snd (q.map (hap.rep.snd ψ)) (q.map e))
      (Module.finrank z.carrier Γ(q.obj (hap.rep.pullback ψ), ⊤)) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback (q.map (hap.rep.snd ψ)) (q.map e))
  let s (j : Fin (Module.finrank z.carrier Γ(q.obj (hap.rep.pullback ψ), ⊤) + 1)) :
      q.obj (r.siteObject B S hS X) ⟶ pullback (q.map (hap.rep.snd ψ)) (q.map e) :=
    pullback.lift (q.map (d j)) (𝟙 _) (by rw [← q.map_comp, hd₂, Category.id_comp])
  have hs : Function.Injective s := by
    intro j k hjk
    apply hcinj
    apply yoneda.map_injective
    rw [← hd₁ j, ← hd₁ k]
    refine congrArg (fun t ↦ yoneda.map t ≫ hap.rep.fst ψ) (q.map_injective ?_)
    have := congrArg (fun t ↦ t ≫ pullback.fst (q.map (hap.rep.snd ψ)) (q.map e)) hjk
    simpa only [s, pullback.lift_fst] using this
  have hcard := card_sections_le_rank
    (pullback.snd (q.map (hap.rep.snd ψ)) (q.map e))
    (Module.finrank z.carrier Γ(q.obj (hap.rep.pullback ψ), ⊤)) s hs
    (fun j ↦ pullback.lift_snd _ _ _)
  omega

/-- A quasi-compact algebraic space `X` over `S` carries a descending
chain of open subspaces starting at `X` whose reduced strata, the differences of
consecutive members, each receive an isomorphism from the part lying over them of a
separated scheme surjective and étale over the corresponding member; and every point of
`|X|` represented by a quasi-compact morphism from the spectrum of a field lies in one of
those strata. -/
@[stacks 0BBN]
public theorem exists_schemeStratification_quasiCompactPoint_mem_stratum
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X) :
    ∃ strat : AlgebraicGeometry.Space.SchemeStratification B S hS X,
      ∀ (x : AlgebraicGeometry.Space.points B S hS X)
        (z : AlgebraicGeometry.Space.FieldValuedPoint B S hS X),
        z.class B S hS X = x →
        AlgebraicGeometry.Space.IsQuasiCompact B S hS
          (AlgebraicGeometry.Space.fieldMorphism B S hS X z) →
        ∃ p : ℕ, x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS
          (strat.stratum p).toFunctor ((strat.stratum p).ι ≫ (strat.openPart p).ι)) := by
  classical
  obtain ⟨A, a, hA, haSurj, haEtale⟩ :=
    exists_affine_etale_atlas_of_quasiCompact B S hS X hX hqc
  obtain ⟨D, V, h, hDzero, hDmono, hDopen, hVcompact, hVsep, hsurj, hetale, hiso, hdeg⟩ :=
    exists_degreeFiltration_symmetricPower_cover_of_quasiCompact B S hS X hX A a hA
      haSurj haEtale
  obtain ⟨T, hT⟩ := exists_reducedClosedStrata B S hS hX D hDopen
  refine ⟨{ openPart := D
            stratum := T
            chart := V
            chartHom := h
            openPart_zero := hDzero
            openPart_succ_le := hDmono
            isOpenSubspace_openPart := hDopen
            isClosedSubspace_stratum := fun p ↦ (hT p).1
            isReduced_stratum := fun p ↦ (hT p).2.2
            range_stratum := fun p ↦ (hT p).2.1
            isSeparated_chart := hVsep
            surjective_chartHom := hsurj
            isEtale_chartHom := hetale
            isIso_pullback_stratum := fun p ↦
              hiso p (T p) (hT p).1 (hT p).2.2 (hT p).2.1 }, ?_⟩
  intro x z hzx hzqc
  have hzero : x ∈
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D 0).toFunctor (D 0).ι) := by
    let : IsIso (D 0).ι := (Subfunctor.eq_top_iff_isIso _).mp hDzero
    exact mem_range_pointsMap_of_isIso B S hS (D 0).ι x
  have hex : ∃ n : ℕ, x ∉
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D n).toFunctor (D n).ι) := by
    obtain ⟨n, hn⟩ := exists_notMem_range_pointsMap_of_isQuasiCompact_fieldMorphism
      B S hS a hA haEtale D hdeg z hzqc
    exact ⟨n, hzx ▸ hn⟩
  obtain ⟨k, hk, hk'⟩ : ∃ k : ℕ,
      x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS (D k).toFunctor (D k).ι) ∧
      x ∉ Set.range (AlgebraicGeometry.Space.pointsMap B S hS
        (D (k + 1)).toFunctor (D (k + 1)).ι) := by
    have hfind := Nat.find_spec hex
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hzeroIdx | hpos
    · rw [hzeroIdx] at hfind
      exact absurd hzero hfind
    · refine ⟨Nat.find hex - 1, not_not.mp (Nat.find_min hex (by omega)), ?_⟩
      have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rw [heq]
      exact hfind
  refine ⟨k, ?_⟩
  change x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS (T k).toFunctor
    ((T k).ι ≫ (D k).ι))
  rw [(hT k).2.1]
  exact ⟨hk, hk'⟩

/-- The degree filtration of a quasi-compact algebraic space with universally
bounded atlas fibres, together with its reduced strata and the separated
symmetric-power étale neighborhoods of those strata. -/
private theorem exists_finiteFiltration_of_hasUniversallyBoundedFibers
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (A : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj A ⟶ X)
    (hA : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj A))
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : AlgebraicGeometry.Space.IsEtale B S hS a)
    (hBounded : AlgebraicGeometry.Space.HasUniversallyBoundedFibers B S hS A a) :
    ∃ (n : ℕ) (U : ℕ → Subfunctor X),
      0 < n ∧
      U 0 = ⊤ ∧
      U n = (⊥ : Subfunctor X).sheafify
        (AlgebraicGeometry.BigFppfOver.topology B S hS) ∧
      (∀ p ≤ n, AlgebraicGeometry.Space.IsOpenSubspace B S hS (U p)) ∧
      (∀ p < n, U (p + 1) ≤ U p) ∧
      ∃ (T : (p : Fin n) → Subfunctor (U p.val).toFunctor)
        (V : Fin n → AlgebraicGeometry.BigFppfOver B S hS)
        (f : ∀ p : Fin n, yoneda.obj (V p) ⟶ (U p.val).toFunctor),
        ∀ p : Fin n,
          (AlgebraicGeometry.Space.IsClosedSubspace B S hS (T p)) ∧
          (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (T p).toFunctor
            ((T p).ι ≫ (U p.val).ι)) =
              Set.range (AlgebraicGeometry.Space.pointsMap B S hS (U p.val).toFunctor
                (U p.val).ι) \
              Set.range (AlgebraicGeometry.Space.pointsMap B S hS (U (p.val + 1)).toFunctor
                (U (p.val + 1)).ι)) ∧
          (AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (T p).toFunctor
            (fun Y : Scheme.{u} => IsReduced Y)) ∧
          (AlgebraicGeometry.Space.IsQuasiCompact B S hS a →
            CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (V p))) ∧
          Scheme.IsSeparated ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (V p)) ∧
          (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (f p) ∧
          AlgebraicGeometry.Space.IsEtale B S hS (f p) ∧
          IsIso (pullback.fst (T p).ι (f p)) := by
  classical
  obtain ⟨n, D, V, h, hn, hD0, hDn, hDmono, hDopen, hVcompact, hVsep, hsurj,
      hetale, hiso⟩ :=
    exists_degreeFiltration_symmetricPower_cover B S hS X hX A a hA haSurj haEtale hBounded
  obtain ⟨T, hT⟩ := exists_reducedClosedStrata B S hS hX D hDopen
  refine ⟨n, D, hn, hD0, hDn, fun p _ ↦ hDopen p, fun p _ ↦ hDmono p,
    fun p ↦ T p.val, fun p ↦ V p.val, fun p ↦ h p.val, fun p ↦ ?_⟩
  exact ⟨(hT p.val).1, (hT p.val).2.1, (hT p.val).2.2,
    fun haQuasiCompact ↦ hVcompact haQuasiCompact p.val,
    hVsep p.val, hsurj p.val, hetale p.val,
    hiso p.val (T p.val) (hT p.val).1 (hT p.val).2.2 (hT p.val).2.1⟩

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- A quasi-compact quasi-separated algebraic space has a finite filtration
by open subspaces such that every reduced stratum has a quasi-compact
separated scheme as an étale neighborhood, isomorphic above the stratum. -/
@[stacks 07ST]
public theorem exists_finiteFiltration_of_isQuasiCompactSpace
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X)
    (hqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X) :
    ∃ (n : ℕ) (U : ℕ → Subfunctor X),
      0 < n ∧
      U 0 = ⊤ ∧
      U n = (⊥ : Subfunctor X).sheafify
        (AlgebraicGeometry.BigFppfOver.topology B S hS) ∧
      (∀ p ≤ n, AlgebraicGeometry.Space.IsOpenSubspace B S hS (U p)) ∧
      (∀ p < n, U (p + 1) ≤ U p) ∧
      ∃ (T : (p : Fin n) → Subfunctor (U p.val).toFunctor)
        (V : Fin n → AlgebraicGeometry.BigFppfOver B S hS)
        (f : ∀ p : Fin n, yoneda.obj (V p) ⟶ (U p.val).toFunctor),
        ∀ p : Fin n,
          (AlgebraicGeometry.Space.IsClosedSubspace B S hS (T p)) ∧
          (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (T p).toFunctor
            ((T p).ι ≫ (U p.val).ι)) =
              Set.range (AlgebraicGeometry.Space.pointsMap B S hS (U p.val).toFunctor
                (U p.val).ι) \
              Set.range (AlgebraicGeometry.Space.pointsMap B S hS (U (p.val + 1)).toFunctor
                (U (p.val + 1)).ι)) ∧
          (AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (T p).toFunctor
            (fun Y : Scheme.{u} => IsReduced Y)) ∧
          CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (V p)) ∧
          Scheme.IsSeparated ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (V p)) ∧
          (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (f p) ∧
          AlgebraicGeometry.Space.IsEtale B S hS (f p) ∧
          IsIso (pullback.fst (T p).ι (f p)) := by
  classical
  obtain ⟨A, a, hA, haSurj, haEtale⟩ :=
    exists_affine_etale_atlas_of_quasiCompact B S hS X hX hqc
  have haQuasiCompact :=
    AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace
      B S hS hZ hX hqs (isQuasiCompact_yoneda_of_compact B S hS A
        (Scheme.compactSpace_of_isAffine _)) a
  obtain ⟨n, U, hn, hU0, hUn, hUopen, hUmono, T, V, f, hdata⟩ :=
    exists_finiteFiltration_of_hasUniversallyBoundedFibers B S hS X hX A a hA haSurj haEtale
      (reasonable_of_quasiSeparated B S hS hZ X hX hqs A hA a
        ((isEtale_iff_presheaf_of_yoneda B S hS a).1 haEtale))
  refine ⟨n, U, hn, hU0, hUn, hUopen, hUmono, T, V, f, fun p ↦ ?_⟩
  exact ⟨(hdata p).1, (hdata p).2.1, (hdata p).2.2.1, (hdata p).2.2.2.1 haQuasiCompact,
    (hdata p).2.2.2.2.1, (hdata p).2.2.2.2.2.1, (hdata p).2.2.2.2.2.2.1,
    (hdata p).2.2.2.2.2.2.2⟩

/-- A quasi-compact reasonable algebraic space has a finite filtration by open
subspaces such that every reduced stratum has a separated scheme as an étale
neighborhood, isomorphic above the stratum. -/
@[stacks 07S9]
public theorem exists_finiteFiltration_of_isReasonableSpace
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X)
    (hr : AlgebraicGeometry.Space.IsReasonableSpace B S hS X) :
    ∃ (n : ℕ) (U : ℕ → Subfunctor X),
      0 < n ∧
      U 0 = ⊤ ∧
      U n = (⊥ : Subfunctor X).sheafify
        (AlgebraicGeometry.BigFppfOver.topology B S hS) ∧
      (∀ p ≤ n, AlgebraicGeometry.Space.IsOpenSubspace B S hS (U p)) ∧
      (∀ p < n, U (p + 1) ≤ U p) ∧
      ∃ (T : (p : Fin n) → Subfunctor (U p.val).toFunctor)
        (V : Fin n → AlgebraicGeometry.BigFppfOver B S hS)
        (f : ∀ p : Fin n, yoneda.obj (V p) ⟶ (U p.val).toFunctor),
        ∀ p : Fin n,
          (AlgebraicGeometry.Space.IsClosedSubspace B S hS (T p)) ∧
          (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (T p).toFunctor
            ((T p).ι ≫ (U p.val).ι)) =
              Set.range (AlgebraicGeometry.Space.pointsMap B S hS (U p.val).toFunctor
                (U p.val).ι) \
              Set.range (AlgebraicGeometry.Space.pointsMap B S hS (U (p.val + 1)).toFunctor
                (U (p.val + 1)).ι)) ∧
          (AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (T p).toFunctor
            (fun Y : Scheme.{u} => IsReduced Y)) ∧
          Scheme.IsSeparated ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (V p)) ∧
          (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (f p) ∧
          AlgebraicGeometry.Space.IsEtale B S hS (f p) ∧
          IsIso (pullback.fst (T p).ι (f p)) := by
  classical
  obtain ⟨A, a, hA, haSurj, haEtale⟩ :=
    exists_affine_etale_atlas_of_quasiCompact B S hS X hX hqc
  obtain ⟨n, U, hn, hU0, hUn, hUopen, hUmono, T, V, f, hdata⟩ :=
    exists_finiteFiltration_of_hasUniversallyBoundedFibers B S hS X hX A a hA haSurj haEtale
      (hr A hA a ((isEtale_iff_presheaf_of_yoneda B S hS a).1 haEtale))
  refine ⟨n, U, hn, hU0, hUn, hUopen, hUmono, T, V, f, fun p ↦ ?_⟩
  exact ⟨(hdata p).1, (hdata p).2.1, (hdata p).2.2.1, (hdata p).2.2.2.2.1,
    (hdata p).2.2.2.2.2.1, (hdata p).2.2.2.2.2.2.1, (hdata p).2.2.2.2.2.2.2⟩

/-- A quasi-compact reasonable algebraic space has a finite filtration by open
subspaces whose reduced strata are schemes. -/
@[stacks 07SA]
public theorem exists_finiteFiltration_isRepresentable_strata
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X)
    (hr : AlgebraicGeometry.Space.IsReasonableSpace B S hS X) :
    ∃ (n : ℕ) (U : ℕ → Subfunctor X),
      0 < n ∧
      U 0 = ⊤ ∧
      U n = (⊥ : Subfunctor X).sheafify
        (AlgebraicGeometry.BigFppfOver.topology B S hS) ∧
      (∀ p ≤ n, AlgebraicGeometry.Space.IsOpenSubspace B S hS (U p)) ∧
      (∀ p < n, U (p + 1) ≤ U p) ∧
      ∃ T : (p : Fin n) → Subfunctor (U p.val).toFunctor,
        ∀ p : Fin n,
          (AlgebraicGeometry.Space.IsClosedSubspace B S hS (T p)) ∧
          (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (T p).toFunctor
            ((T p).ι ≫ (U p.val).ι)) =
              Set.range (AlgebraicGeometry.Space.pointsMap B S hS (U p.val).toFunctor
                (U p.val).ι) \
              Set.range (AlgebraicGeometry.Space.pointsMap B S hS (U (p.val + 1)).toFunctor
                (U (p.val + 1)).ι)) ∧
          (AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (T p).toFunctor
            (fun Y : Scheme.{u} => IsReduced Y)) ∧
          (T p).toFunctor.IsRepresentable := by
  obtain ⟨n, U, hn, hU0, hUn, hUopen, hUmono, T, V, f, hdata⟩ :=
    exists_finiteFiltration_of_isReasonableSpace B S hS X hX hqc hr
  refine ⟨n, U, hn, hU0, hUn, hUopen, hUmono, T, fun p ↦ ?_⟩
  exact ⟨(hdata p).1, (hdata p).2.1, (hdata p).2.2.1,
    isRepresentable_of_isIso_pullback_fst B S hS (hdata p).1 (f p)
      (hdata p).2.2.2.2.2.2⟩

end AlgebraicGeometry.Space

end
