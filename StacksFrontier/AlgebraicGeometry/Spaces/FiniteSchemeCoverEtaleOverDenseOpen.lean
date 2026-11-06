module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceAgreementOverOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget

/-!
# Stacks 0GUN: a finite and finitely presented scheme cover, finite étale over a dense open

Stacks 0GUN asserts, for a quasi-compact and quasi-separated algebraic space `X` over a scheme `S`
whose space of points `|X|` has finitely many irreducible components, that

1. there is a surjective finite morphism `f : Y ⟶ X` of finite presentation, with `Y` a scheme,
   which is finite étale over a quasi-compact dense open `U ⊆ X`, and
2. given a surjective étale `V ⟶ X`, `Y` can be chosen so that every point of `Y` has an open
   neighbourhood `W ⊆ Y` such that `W ⟶ X` factors through `V`.

## Main definitions

* `AlgebraicGeometry.Space.IsFiniteSchemeCoverFiniteEtaleOverDenseOpen`: the conclusion of
  clause (1) for a named cover and a named open subspace.

## Main results

* `AlgebraicGeometry.Space.exists_finiteSchemeCover_of_closedSubspace`: a closed subspace `C` of
  a finite and finitely presented `P ⟶ X`, surjective onto `X`, finite étale over `U`, and
  factoring locally through an étale chart from an affine scheme, lies in a closed subspace of
  finite presentation which is a cover as in the tag.

## References

* [Stacks Project, Tag 0GUN](https://stacks.math.columbia.edu/tag/0GUN)
* [Stacks Project, Tag 0GUL](https://stacks.math.columbia.edu/tag/0GUL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **The conclusion of clause (1) of Stacks 0GUN for a named cover.** The morphism
`f : h_Y ⟶ X` from the presheaf represented by an object `Y` of the big fppf site — a scheme over
`S` — is surjective, finite and of finite presentation, and `U` is a quasi-compact open subspace
of `X` whose point set is dense in `|X|`, over which `f` is finite and étale. -/
def IsFiniteSchemeCoverFiniteEtaleOverDenseOpen {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X) (U : Subfunctor X) : Prop :=
  IsSurjective B S hS f ∧ IsFinite B S hS f ∧ IsFinitePresentation B S hS f ∧
    IsOpenSubspace B S hS U ∧ IsQuasiCompactSpace B S hS U.toFunctor ∧
    Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∧
    IsFinite B S hS (pullback.fst U.ι f) ∧ IsEtale B S hS (pullback.fst U.ι f)

/-- **From a closed subspace with étale section charts to the cover of the tag.** Let
`q : P ⟶ X` be finite and of finite presentation over a quasi-compact quasi-separated `X`, let
`g_k : h_{Γ_k} ⟶ P` be finitely many étale charts from quasi-compact schemes over which `P ⟶ X`
factors through `p : h_V ⟶ X`, and let `C ⊆ P` be a closed subspace on which the `g_k` are
monomorphisms covering it (`AlgebraicGeometry.Space.IsEtaleSectionClosed`), such that `C ⟶ X` is
surjective and finite étale over the quasi-compact dense open `U`. Then a closed subspace of
finite presentation `T ⊇ C` of `P` is a scheme `Y`, and `Y ⟶ X` is a cover as in clause (1) of
Stacks 0GUN, over the same `U`, factoring Zariski locally through `p`. -/
theorem exists_finiteSchemeCover_of_isEtaleSectionClosed (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (P : AlgebraicSpaces B S hS) (q : P.1 ⟶ X) (hqa : IsAffineHom B S hS q)
    (hqfp : IsFinitePresentation B S hS q) {V : BigFppfOver B S hS} (p : yoneda.obj V ⟶ X)
    {n : ℕ} {Γ : Fin n → BigFppfOver B S hS}
    (hΓ : ∀ k, CompactSpace ((BigFppfOver.toScheme B S hS).obj (Γ k)))
    (g : ∀ k, yoneda.obj (Γ k) ⟶ P.1) (hg : ∀ k, IsEtale B S hS (g k))
    (h : ∀ k, yoneda.obj (Γ k) ⟶ yoneda.obj V) (hgh : ∀ k, g k ≫ q = h k ≫ p)
    (C : ClosedSubspaces B S hS P.1) (hC : IsEtaleSectionClosed B S hS g C.1)
    (hCsurj : IsSurjective B S hS (C.1.ι ≫ q))
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hUdense : Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)))
    (hCUfin : IsFinite B S hS (pullback.fst U.ι (C.1.ι ≫ q)))
    (hCUet : IsEtale B S hS (pullback.fst U.ι (C.1.ι ≫ q)))
    {Zt : BigFppfOver B S hS} [CompactSpace ((BigFppfOver.toScheme B S hS).obj Zt)]
    (ψ : yoneda.obj Zt ⟶ P.1)
    (hψ : MorphismProperty.presheaf (MorphismProperty.inverseImage @Etale
      (BigFppfOver.toScheme B S hS)) ψ)
    (Jt : ((BigFppfOver.toScheme B S hS).obj Zt).IdealSheafData) (hJt : Jt.IsFiniteType)
    (hJtC : Jt ≤ chartKer B S hS P C ψ)
    (hfinT : ∀ T : ClosedSubspaces B S hS P.1, Jt ≤ chartKer B S hS P T ψ →
      IsFinite B S hS (T.1.ι ≫ q)) :
    ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X),
      IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y f U ∧
        FactorsZariskiLocallyThrough B S hS p Y f := by
  -- `P` is quasi-compact and quasi-separated.
  have hPqc : IsQuasiCompactSpace B S hS P.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hX hXqc hqfp.2.1
  have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ P.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ P.2 hXqs hqfp.2.2
  -- The chart over `U`, and the ideal of `C` on it.
  obtain ⟨U₀, Ũ, u₀, π, φ, hφΩ, -, hŨaff, hπ, -, hsq, hφ, hloc⟩ :=
    exists_chart_over_openSubspace B S hS hX P q hqa hqfp.1 U hU hUqc
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Ũ) := hŨaff
  have hJ : (chartKer B S hS P C φ).IsFiniteType :=
    isFiniteType_chartKer_of_isEtale_pullback_fst B S hS hX P q U hU u₀ π φ hπ hsq C hCUet
  -- Two chart conditions: agreement with `C` over `U`, and the finiteness certificate.
  let Uc : Fin 2 → BigFppfOver B S hS := Fin.cons Ũ fun _ => Zt
  have : ∀ i, CompactSpace ((BigFppfOver.toScheme B S hS).obj (Uc i)) := fun i =>
    Fin.cases (inferInstanceAs (CompactSpace ((BigFppfOver.toScheme B S hS).obj Ũ)))
      (fun _ => inferInstanceAs (CompactSpace ((BigFppfOver.toScheme B S hS).obj Zt))) i
  let φc : ∀ i, yoneda.obj (Uc i) ⟶ P.1 := Fin.cons φ fun _ => ψ
  let Jc : ∀ i, ((BigFppfOver.toScheme B S hS).obj (Uc i)).IdealSheafData :=
    Fin.cons (chartKer B S hS P C φ) fun _ => Jt
  obtain ⟨T, hTfp, hCT, hT, hJT⟩ := exists_isFinitePresentation_isEtaleSectionClosed B S hS hZ P
    hPqc hPqs hΓ g hg C hC (U := Uc) φc
    (Fin.cons ((isEtale_iff_presheaf_of_yoneda B S hS φ).1 hφ) fun _ => hψ) Jc
    (Fin.cons hJ fun _ => hJt) (Fin.cons le_rfl fun _ => hJtC)
  obtain ⟨Y, e, hY⟩ := exists_iso_yoneda_of_isEtaleSectionClosed B S hS P g hg T hT
  have hYfac : FactorsZariskiLocallyThrough B S hS p Y (e.hom ≫ T.1.ι ≫ q) := by
    intro y
    obtain ⟨j, W, hW, hWrep, hy, c, hc⟩ := hY y
    refine ⟨W, hW, hWrep, hy, c ≫ h j, ?_⟩
    rw [← Category.assoc, ← Category.assoc, Category.assoc W.ι, hc, Category.assoc, hgh,
      Category.assoc]
  -- `T` agrees with `C` over `U`.
  have hTC : T.1.preimage φ ≤ C.1.preimage φ := by
    have hle := (le_chartKer_iff B S hS P T φ _).1 (hJT 0)
    rwa [show Jc 0 = chartKer B S hS P C φ from rfl, chartKer_eq, idealPoints_ker_rep_snd C.2.2]
      at hle
  obtain ⟨hTUfin, hTUet⟩ := isFinite_isEtale_pullback_fst_of_inf_le B S hS q U T.1 C.1 hCT
    (inf_le_of_preimage_le B S hS P T C (U.preimage q) φ hφΩ hloc hTC) hCUfin hCUet
  -- The cover.
  let g' : T.1.toFunctor ⟶ X := T.1.ι ≫ q
  have hYalg := isAlgebraicSpace_yoneda B S hS Y
  have hTfin : IsFinite B S hS g' := hfinT T (hJT 1)
  refine ⟨Y, e.hom ≫ g', ⟨?_, ?_, ?_, hU, hUqc, hUdense, ?_⟩, hYfac⟩
  · -- surjective
    intro x
    obtain ⟨c, hc⟩ := hCsurj x
    obtain ⟨y, hy⟩ := (bijective_pointsMap_of_isIso B S hS e.hom).2
      (pointsMap B S hS _ (Subfunctor.homOfLe hCT) c)
    refine ⟨y, ?_⟩
    rw [pointsMap_comp_apply, hy, ← pointsMap_comp_apply, ← hc]
    show pointsMap B S hS _ (Subfunctor.homOfLe hCT ≫ T.1.ι ≫ q) c = _
    rw [← Category.assoc, Subfunctor.homOfLe_ι]
  · exact isFinite_comp B S hS (isFinite_of_isIso B S hS _) hTfin
  · refine isFinitePresentation_comp B S hS hYalg T.2.1 hX _ _
      ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS _),
        isQuasiCompact_of_isIso B S hS _, isQuasiSeparated_of_mono B S hS e.hom
          ⟨fun g h w => by simpa using w =≫ e.inv⟩⟩
      (isFinitePresentation_comp B S hS T.2.1 P.2 hX _ _ hTfp hqfp)
  · -- finite étale over `U`
    let m := pullback.map U.ι (e.hom ≫ g') U.ι g' (𝟙 _) e.hom (𝟙 _) (by simp) (by simp)
    have hm : pullback.fst U.ι (e.hom ≫ g') = m ≫ pullback.fst U.ι g' :=
      (pullback.lift_fst _ _ _).symm
    rw [hm]
    exact ⟨isFinite_comp B S hS (isFinite_of_isIso B S hS m) hTUfin,
      isEtale_comp B S hS (isEtale_of_isIso B S hS m) hTUet⟩

/-- **From a closed subspace of a finite and finitely presented space to the cover of the tag.**
Let `q : P ⟶ X` be finite and of finite presentation over a quasi-compact quasi-separated `X`,
`p : h_V ⟶ X` étale from an affine scheme, and `C ⊆ P` a closed subspace such that `C ⟶ X` is
surjective, finite étale over the quasi-compact dense open `U`, and factors through `p` on an open
neighbourhood of every point of `C`. Then a closed subspace of finite presentation `T ⊇ C` of `P`
is a scheme `Y`, and `Y ⟶ X` is a cover as in clause (1) of Stacks 0GUN, over the same `U`,
factoring Zariski locally through `p`. -/
theorem exists_finiteSchemeCover_of_closedSubspace (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (P : AlgebraicSpaces B S hS) (q : P.1 ⟶ X) (hq : IsFinite B S hS q)
    (hqfp : IsFinitePresentation B S hS q)
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (p : yoneda.obj V ⟶ X) (hp : IsEtale B S hS p) (C : ClosedSubspaces B S hS P.1)
    (hCsurj : IsSurjective B S hS (C.1.ι ≫ q))
    (hfac : ∀ x : points B S hS C.1.toFunctor, ∃ W : Subfunctor C.1.toFunctor,
      IsOpenSubspace B S hS W ∧ x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
      ∃ c : W.toFunctor ⟶ yoneda.obj V, W.ι ≫ C.1.ι ≫ q = c ≫ p)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hUdense : Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)))
    (hCUfin : IsFinite B S hS (pullback.fst U.ι (C.1.ι ≫ q)))
    (hCUet : IsEtale B S hS (pullback.fst U.ι (C.1.ι ≫ q))) :
    ∃ (Y : BigFppfOver B S hS) (f : yoneda.obj Y ⟶ X),
      IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y f U ∧
        FactorsZariskiLocallyThrough B S hS p Y f := by
  classical
  obtain ⟨E, πE, iE, -, -, hEsq⟩ := hq V hV p
  have _ : CompactSpace (points B S hS P.1) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ P.2).1
      (isQuasiCompactSpace_source_of_isQuasiCompact B S hS hX hXqc hqfp.2.1)
  -- A graph chart at every point of `C`.
  have hloc : ∀ x : points B S hS C.1.toFunctor, ∃ (Γ : BigFppfOver B S hS)
      (g : yoneda.obj Γ ⟶ P.1) (h : yoneda.obj Γ ⟶ yoneda.obj V),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj Γ) ∧ IsEtale B S hS g ∧ g ≫ q = h ≫ p ∧
      pointsMap B S hS _ C.1.ι x ∈ Set.range (pointsMap B S hS _ g) ∧
      ∀ (Z : BigFppfOver B S hS) (a b : yoneda.obj Z ⟶ yoneda.obj Γ), a ≫ g = b ≫ g →
        (∃ t : yoneda.obj Z ⟶ C.1.toFunctor, t ≫ C.1.ι = a ≫ g) → a = b := by
    intro x
    obtain ⟨W, hW, ⟨w, rfl⟩, c, hc⟩ := hfac x
    obtain ⟨Γ, g, h, h1, h2, h3, h4, h5⟩ := exists_etaleChart_mono_over_closedSubspace B S hS hX
      P q p hp ⟨E, πE, iE, hEsq⟩ C W hW c hc w
    exact ⟨Γ, g, h, h1, h2, h3, by rwa [← pointsMap_comp_apply], h5⟩
  choose Γ g h hΓ hg hgh hx hmono using hloc
  -- Finitely many of them cover `|C|`.
  have hCcpt : IsCompact (Set.range (pointsMap B S hS C.1.toFunctor C.1.ι)) :=
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS P.2 C.1.ι C.2.2).isCompact
  obtain ⟨t, ht⟩ := hCcpt.elim_finite_subcover
    (fun x => Set.range (pointsMap B S hS _ (g x)))
    (fun x => isOpen_range_pointsMap_of_isEtale B S hS (g x) (isAlgebraicSpace_yoneda B S hS _)
      P.2 (hg x))
    (Set.range_subset_iff.2 fun x => Set.mem_iUnion.2 ⟨x, hx x⟩)
  let σ : Fin t.card → points B S hS C.1.toFunctor := fun j => (t.equivFin.symm j).1
  have hC : IsEtaleSectionClosed B S hS (fun j => g (σ j)) C.1 := by
    refine ⟨fun j => preimage_le_range_diagonal_of_forall B S hS _ C.1 (hmono (σ j)), ?_⟩
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
    have hσ : σ (t.equivFin ⟨x, hxt⟩) = x := by simp only [σ, Equiv.symm_apply_apply]
    show y ∈ Set.range (pointsMap B S hS _ (g (σ (t.equivFin ⟨x, hxt⟩))))
    rw [hσ]
    exact hyx
  obtain ⟨Vt, ψt, hVtaff, -, hψte⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS P.1 P.2).1
      (isQuasiCompactSpace_source_of_isQuasiCompact B S hS hX hXqc hqfp.2.1)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Vt) := hVtaff
  exact exists_finiteSchemeCover_of_isEtaleSectionClosed B S hS hZ hX hXqc hXqs P q
    hq.isAffineHom hqfp p
    (fun j => hΓ (σ j)) (fun j => g (σ j)) (fun j => hg (σ j)) (fun j => h (σ j))
    (fun j => hgh (σ j)) C hC hCsurj U hU hUqc hUdense hCUfin hCUet ψt
    ((isEtale_iff_presheaf_of_yoneda B S hS ψt).1 hψte) ⊥
    Stacks.FiniteTypeIdealSheaf.isFiniteType_bot bot_le
    (fun T _ => isFinite_comp B S hS (isFinite_of_isClosedImmersion B S hS _ T.2.2) hq)

end AlgebraicGeometry.Space

end
