module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverEtaleOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart

/-!
# Basic opens of the chart of a cover which lie in the graphs of its local factorizations

Let `π : h_Y ⟶ X` be a morphism from a scheme to an algebraic space, representable, and let
`p : h_V ⟶ X` be étale, such that `π` factors through `p` Zariski locally on `Y`. If the base
change `W = Y ×_X V` is an affine scheme, then finitely many basic opens `D(q_k) ⊆ W` map
isomorphically onto open subschemes of `Y` which cover `Y`: around every point the graph of a local
factorization is an open subscheme of `W`, and basic opens form a basis of the topology of `W`.

These are the opens which, in the proof of Stacks 0GUN, are cut out on the chart of a space
affine over `X` by finitely many functions.

## Main results

* `AlgebraicGeometry.Space.exists_basicOpens_mono_of_factorsZariskiLocallyThrough`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- A point of the scheme underlying an object of the site lying in an open subscheme is the
image of a point of that open subscheme, read as an object of the site. -/
theorem exists_points_openSub_of_mem (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens) {x : (BigFppfOver.toScheme B S hS).obj A}
    (hx : x ∈ O) : ∃ z : points B S hS (yoneda.obj (openSub A O)),
      pointsMap B S hS _ (yoneda.map (openSubHom A O)) z =
        (schemePointsHomeomorph B S hS A).symm x := by
  refine ⟨(schemePointsHomeomorph B S hS (openSub A O)).symm
    (show (BigFppfOver.toScheme B S hS).obj (openSub A O) from ⟨x, hx⟩), ?_⟩
  rw [schemePointsHomeomorph_symm_naturality, toScheme_map_openSubHom]
  rfl

/-- The points of an open subscheme of an object of the site map into the open. -/
theorem mem_of_points_openSub (A : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj A).Opens)
    (z : points B S hS (yoneda.obj (openSub A O))) :
    schemePointsHomeomorph B S hS A (pointsMap B S hS _ (yoneda.map (openSubHom A O)) z) ∈ O := by
  rw [schemePointsHomeomorph_apply, pointsToScheme_pointsMap, toScheme_map_openSubHom]
  exact (pointsToScheme B S hS (openSub A O) z).2

/-- **Basic opens of the chart lying in the graphs of the local factorizations.** -/
theorem exists_basicOpens_mono_of_factorsZariskiLocallyThrough
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {Y V : BigFppfOver B S hS} (π : yoneda.obj Y ⟶ X) (hπ : yoneda.relativelyRepresentable π)
    (hYqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj Y))
    (p : yoneda.obj V ⟶ X) (hp : IsEtale B S hS p)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj (hπ.pullback p)))
    (hfac : FactorsZariskiLocallyThrough B S hS p Y π) :
    ∃ (n : ℕ) (q : Fin n → Γ((BigFppfOver.toScheme B S hS).obj (hπ.pullback p), ⊤)),
      (∀ k, ∀ O : ((BigFppfOver.toScheme B S hS).obj (hπ.pullback p)).Opens,
        O ≤ ((BigFppfOver.toScheme B S hS).obj (hπ.pullback p)).basicOpen (q k) →
          Mono (yoneda.map (openSubHom _ O) ≫ hπ.fst p)) ∧
      ∀ y : points B S hS (yoneda.obj Y), ∃ k, ∃ w : (BigFppfOver.toScheme B S hS).obj
          (hπ.pullback p),
        w ∈ ((BigFppfOver.toScheme B S hS).obj (hπ.pullback p)).basicOpen (q k) ∧
          pointsMap B S hS _ (hπ.fst p) ((schemePointsHomeomorph B S hS _).symm w) = y := by
  classical
  set W := hπ.pullback p
  set Ws := (BigFppfOver.toScheme B S hS).obj W
  have hWalg := isAlgebraicSpace_yoneda B S hS W
  have hYalg := isAlgebraicSpace_yoneda B S hS Y
  have hsq := hπ.isPullback p
  have hfst : IsEtale B S hS (hπ.fst p) :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsq hWalg hYalg
      (isAlgebraicSpace_yoneda B S hS V) hX hp
  -- Around every point, a basic open inside the graph of a local factorization.
  have hloc : ∀ y : points B S hS (yoneda.obj Y), ∃ q : Γ(Ws, ⊤),
      (∀ O : Ws.Opens, O ≤ Ws.basicOpen q → Mono (yoneda.map (openSubHom W O) ≫ hπ.fst p)) ∧
      ∃ w : Ws, w ∈ Ws.basicOpen q ∧
        pointsMap B S hS _ (hπ.fst p) ((schemePointsHomeomorph B S hS W).symm w) = y := by
    intro y
    obtain ⟨Ws', hWs', -, ⟨y', rfl⟩, c, hc⟩ := hfac y
    let γ : Ws'.toFunctor ⟶ yoneda.obj W := hsq.lift Ws'.ι c hc
    have hγ : γ ≫ hπ.fst p = Ws'.ι := hsq.lift_fst _ _ _
    have hγmono : Mono γ := mono_of_mono_fac hγ
    have hγet : IsEtale B S hS γ :=
      isEtale_of_isEtale_over B S hS hWs'.1 hWalg hYalg γ Ws'.ι (hπ.fst p)
        (isEtale_ι_of_isOpenSubspace hWs') hfst hγ
    have hγoi : IsOpenImmersion B S hS γ :=
      isOpenImmersion_of_isEtale_of_mono B S hS γ hWs'.1 hWalg hγet hγmono
    let R : Subfunctor (yoneda.obj W) := Subfunctor.range γ
    have hR : IsOpenSubspace B S hS R :=
      isOpenSubspace_range_of_isAlgebraicSpace B S hS hWs'.1 γ hγoi
    have hRpts : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.range (pointsMap B S hS _ γ) :=
      range_pointsMap_ι_range B S hS γ
    set O₀ : Set Ws := schemePointsHomeomorph B S hS W '' Set.range (pointsMap B S hS _ γ)
    have hO₀ : IsOpen O₀ := (schemePointsHomeomorph B S hS W).isOpenMap _
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS γ hγoi)
    set x₀ := schemePointsHomeomorph B S hS W (pointsMap B S hS _ γ y')
    have hx₀ : x₀ ∈ O₀ := ⟨_, ⟨y', rfl⟩, rfl⟩
    have : IsAffine Ws := hW
    obtain ⟨q, hqO, hxq⟩ := (isAffineOpen_top Ws).exists_basicOpen_le
      (V := ⟨O₀, hO₀⟩) ⟨x₀, hx₀⟩ trivial
    refine ⟨q, fun O hO => ?_, x₀, hxq, ?_⟩
    · -- an open inside the basic open factors through the graph
      have hmono : Mono (yoneda.map (openSubHom W O)) :=
        mono_of_isOpenImmersion B S hS _ (isOpenImmersion_yoneda_map_openSubHom W O)
      have hle : Subfunctor.range (yoneda.map (openSubHom W O)) ≤ R := by
        refine le_of_range_pointsMap_ι_subset B S hS hR ?_
        rw [range_pointsMap_ι_range, hRpts]
        rintro _ ⟨z, rfl⟩
        have hz : schemePointsHomeomorph B S hS W
            (pointsMap B S hS _ (yoneda.map (openSubHom W O)) z) ∈ O₀ :=
          hqO (hO (mem_of_points_openSub B S hS W O z))
        obtain ⟨v, hv, hveq⟩ := hz
        rw [← (schemePointsHomeomorph B S hS W).injective hveq]
        exact hv
      let j' : yoneda.obj (openSub W O) ⟶ R.toFunctor := Subfunctor.lift _ hle
      have hj' : j' ≫ R.ι = yoneda.map (openSubHom W O) := Subfunctor.lift_ι _ _
      have hinv : inv (Subfunctor.toRange γ) ≫ γ = R.ι :=
        (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι γ).symm
      have hfac' : yoneda.map (openSubHom W O) ≫ hπ.fst p =
          (j' ≫ inv (Subfunctor.toRange γ)) ≫ Ws'.ι := by
        rw [← hj', ← hinv, ← hγ]
        simp only [Category.assoc]
      have : Mono (j' ≫ inv (Subfunctor.toRange γ)) := by
        have : Mono j' := mono_of_mono_fac hj'
        exact mono_comp _ _
      rw [hfac']
      exact mono_comp _ _
    · rw [Homeomorph.symm_apply_apply, ← pointsMap_comp_apply, hγ]
  choose q hqmono w hwq hwy using hloc
  -- Finitely many cover `Y`.
  have hcpt : CompactSpace (points B S hS (yoneda.obj Y)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hYalg).1
      (isQuasiCompactSpace_yoneda B S hS Y hYqc)
  let N : points B S hS (yoneda.obj Y) → Set (points B S hS (yoneda.obj Y)) := fun y =>
    Set.range (pointsMap B S hS _ (yoneda.map (openSubHom W (Ws.basicOpen (q y))) ≫ hπ.fst p))
  have hNo : ∀ y, IsOpen (N y) := fun y =>
    isOpen_range_pointsMap_of_isEtale B S hS _ (isAlgebraicSpace_yoneda B S hS _) hYalg
      (isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS
        (isOpenImmersion_yoneda_map_openSubHom W _)) hfst)
  have hyN : ∀ y, y ∈ N y := by
    intro y
    obtain ⟨z, hz⟩ := exists_points_openSub_of_mem B S hS W (Ws.basicOpen (q y)) (hwq y)
    refine ⟨z, ?_⟩
    rw [pointsMap_comp_apply, hz, hwy y]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hyN y⟩)
  let σ : Fin t.card → points B S hS (yoneda.obj Y) := fun j => (t.equivFin.symm j).1
  refine ⟨t.card, fun j => q (σ j), fun j => hqmono (σ j), fun y => ?_⟩
  obtain ⟨y₀, hy₀t, hyy₀⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  obtain ⟨z, rfl⟩ := hyy₀
  refine ⟨t.equivFin ⟨y₀, hy₀t⟩, ?_⟩
  have hσ : σ (t.equivFin ⟨y₀, hy₀t⟩) = y₀ := by simp only [σ, Equiv.symm_apply_apply]
  show ∃ w, w ∈ Ws.basicOpen (q (σ (t.equivFin ⟨y₀, hy₀t⟩))) ∧ _
  rw [hσ]
  refine ⟨schemePointsHomeomorph B S hS W (pointsMap B S hS _ (yoneda.map (openSubHom W _)) z),
    mem_of_points_openSub B S hS W _ z, ?_⟩
  rw [Homeomorph.symm_apply_apply, ← pointsMap_comp_apply]

end AlgebraicGeometry.Space

end
