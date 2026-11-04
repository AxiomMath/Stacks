module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeStageInduction

/-!
# The flat case of the proof of Stacks 0CQ7

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to a quasi-compact
quasi-separated algebraic space, all of whose values lie in a quasi-compact open `W ⊆ Y`, such
that the corestriction `𝒳 ⟶ W` is surjective, flat and locally of finite presentation. Let
`V ⊆ W` be a quasi-compact open over which `𝒳` is a gerbe. This is the situation the source
reaches after flattening ("the image of `|f|` is an open `W`").

Stacks 0CQ6 gives a finite surjective `g : Y' ⟶ Y` such that `g⁻¹(W) ⟶ W` factors Zariski locally
through `𝒳 ⟶ W`. As `g⁻¹(W)` is quasi-compact, finitely many quasi-compact opens inside the
pieces of that factorisation cover it, and the factorisation restricted to them gives the stage
data of situation (b) over `g`, with `V' = g⁻¹(V)`. The induction on the number of opens then
gives a section cover of the image of `V'`, which is `|V|` since `g` is surjective, and so the
conclusion of [Stacks, Tag 0CQ7].

## Main results

* `ChowGerbeLocalIsos.hasProperCompactifiableCover_of_corestrict`: the conclusion of
  [Stacks, Tag 0CQ7] in the flat case above.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 0CQ6](https://stacks.math.columbia.edu/tag/0CQ6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos

open ChowGerbeMerge ChowGerbeSectionCover

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}

/-- Along a morphism `g` surjective on points, every point of `V` lifts to `g⁻¹(V)`. -/
theorem exists_pointsMap_preimage_comp_eq_of_isSurjective {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g : Y' ⟶ Y} (hg : Space.IsSurjective B S hS g) (V : Subfunctor Y) :
    ∀ v ∈ Set.range (Space.pointsMap B S hS V.toFunctor V.ι), ∃ y : Space.points B S hS
      (V.preimage g).toFunctor, Space.pointsMap B S hS _ ((V.preimage g).ι ≫ g) y = v := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨y, hy⟩ := hg (Space.pointsMap B S hS _ V.ι v)
  obtain ⟨z, rfl⟩ : y ∈ Set.range (Space.pointsMap B S hS (V.preimage g).toFunctor
      (V.preimage g).ι) := by
    rw [Space.range_pointsMap_preimage_ι]
    exact ⟨v, hy.symm⟩
  exact ⟨z, by rw [Space.pointsMap_comp_apply, hy]⟩

/-- If open immersions `ι j` cover the points of `Y'` lying over `W`, every point of `g⁻¹(W)` has
a quasi-compact open neighbourhood inside the range of one of them. -/
theorem exists_isQuasiCompactSpace_le_range_of_cover {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : IsAlgebraicSpace B S hS Y') {g : Y' ⟶ Y} {W : Subfunctor Y} {J : Type u}
    {O : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hO : ∀ j, IsAlgebraicSpace B S hS (O j))
    {ι : ∀ j, O j ⟶ Y'} (hι : ∀ j, Space.IsOpenImmersion B S hS (ι j))
    (hcov : ∀ y : Space.points B S hS Y',
      Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS W.toFunctor W.ι) →
        ∃ j, y ∈ Set.range (Space.pointsMap B S hS (O j) (ι j)))
    (y : Space.points B S hS (W.preimage g).toFunctor) :
    ∃ (N : Subfunctor Y') (_ : Space.IsOpenSubspace B S hS N),
      Space.IsQuasiCompactSpace B S hS N.toFunctor ∧
      Space.pointsMap B S hS _ (W.preimage g).ι y ∈
        Set.range (Space.pointsMap B S hS N.toFunctor N.ι) ∧
      ∃ j, N ≤ Subfunctor.range (ι j) := by
  have : ∀ j, Mono (ι j) := fun j => Space.mono_of_isOpenImmersion B S hS (ι j) (hι j)
  have hy : Space.pointsMap B S hS Y' g (Space.pointsMap B S hS _ (W.preimage g).ι y) ∈
      Set.range (Space.pointsMap B S hS W.toFunctor W.ι) := by
    rw [← Set.mem_preimage, ← Space.range_pointsMap_preimage_ι]
    exact ⟨y, rfl⟩
  obtain ⟨j, hj⟩ := hcov _ hy
  obtain ⟨N, hN, hNqc, hyN, hNU⟩ :=
    Space.exists_isQuasiCompactSpace_isOpenSubspace_range_subset B S hS hY'
      (Set.range (Space.pointsMap B S hS (O j) (ι j)))
      (Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS (ι j) (hι j)) _ hj
  exact ⟨N, hN, hNqc, hyN, j, Space.le_of_range_pointsMap_ι_subset B S hS
    (Space.isOpenSubspace_range_of_open B S hS (ι j) (hO j) (hι j))
    (by rwa [range_pointsMap_range_ι])⟩

/-- If open immersions `ι j` cover the points of `Y'` lying over `W`, and `g⁻¹(W)` is
quasi-compact and nonempty, then finitely many quasi-compact opens `N k`, each factoring through
some `ι (j k)`, cover the points of `g⁻¹(W)`. -/
theorem exists_finite_isQuasiCompactSpace_cover_of_cover {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : IsAlgebraicSpace B S hS Y') {g : Y' ⟶ Y} {W : Subfunctor Y} {J : Type u}
    {O : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hO : ∀ j, IsAlgebraicSpace B S hS (O j))
    {ι : ∀ j, O j ⟶ Y'} (hι : ∀ j, Space.IsOpenImmersion B S hS (ι j))
    (hcov : ∀ y : Space.points B S hS Y',
      Space.pointsMap B S hS Y' g y ∈ Set.range (Space.pointsMap B S hS W.toFunctor W.ι) →
        ∃ j, y ∈ Set.range (Space.pointsMap B S hS (O j) (ι j)))
    [CompactSpace (Space.points B S hS (W.preimage g).toFunctor)]
    [Nonempty (Space.points B S hS (W.preimage g).toFunctor)] :
    ∃ (m : ℕ) (N : ℕ → Subfunctor Y') (_ : ∀ k, Space.IsOpenSubspace B S hS (N k)),
      (∀ k, Space.IsQuasiCompactSpace B S hS (N k).toFunctor) ∧
      ∃ (j : ℕ → J) (c : ∀ k, (N k).toFunctor ⟶ O (j k)), (∀ k, c k ≫ ι (j k) = (N k).ι) ∧
        Set.range (Space.pointsMap B S hS (W.preimage g).toFunctor (W.preimage g).ι) ⊆
          ⋃ k : Fin (m + 1), Set.range (Space.pointsMap B S hS (N k).toFunctor (N k).ι) := by
  classical
  choose N hN hNqc hyN j hNj using exists_isQuasiCompactSpace_le_range_of_cover hY' hO hι hcov
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y => Space.pointsMap B S hS _ (W.preimage g).ι ⁻¹'
      Set.range (Space.pointsMap B S hS (N y).toFunctor (N y).ι))
    (fun y => (Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS (N y).ι (hN y).2).preimage
      (Space.continuous_pointsMap B S hS _))
    (fun y _ => Set.mem_iUnion.2 ⟨y, hyN y⟩)
  have hcover (y) := by simpa using ht (Set.mem_univ y)
  obtain ⟨m, hm⟩ : ∃ m, t.card = m + 1 := by
    obtain ⟨y⟩ := ‹Nonempty (Space.points B S hS (W.preimage g).toFunctor)›
    obtain ⟨i, hi, -⟩ := hcover y
    exact Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero_of_mem hi)
  have : ∀ j, Mono (ι j) := fun j => Space.mono_of_isOpenImmersion B S hS (ι j) (hι j)
  have hinv : ∀ j', inv (Subfunctor.toRange (ι j')) ≫ ι j' = (Subfunctor.range (ι j')).ι :=
    fun j' => by rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
  let vs : ℕ → Space.points B S hS (W.preimage g).toFunctor := fun k =>
    (t.equivFin.symm ⟨min k m, by omega⟩).1
  refine ⟨m, fun k => N (vs k), fun k => hN (vs k), fun k => hNqc (vs k), fun k => j (vs k),
    fun k => Subfunctor.homOfLe (hNj (vs k)) ≫ inv (Subfunctor.toRange (ι (j (vs k)))),
    fun k => by simp only [Category.assoc, hinv, Subfunctor.homOfLe_ι], ?_⟩
  rintro _ ⟨y, rfl⟩
  obtain ⟨i, hi, hyi⟩ := hcover y
  let k := t.equivFin ⟨i, hi⟩
  have hk1 : (k : ℕ) ≤ m := by have := k.2; omega
  have hk : vs k = i := by
    simp only [vs, Nat.min_eq_left hk1, Fin.eta, k, Equiv.symm_apply_apply]
  refine Set.mem_iUnion.2 ⟨⟨k, by omega⟩, ?_⟩
  show _ ∈ Set.range (Space.pointsMap B S hS (N (vs k)).toFunctor (N (vs k)).ι)
  rw [hk]
  exact hyi

/-- If `f` factors through `fZ` and `ι`, `q` agree over `Y`, a section `x` with `x ≫ fZ ≅ q`,
restricted along `c` with `c ≫ ι = n`, has composite with `f` the map `n ≫ g`. -/
theorem nonempty_algebraicSpaceStackMap_comp_iso_of_factorization
    {Y' Z O N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : Y' ⟶ Y} {z : Z ⟶ Y}
    (hZ : IsAlgebraicSpace B S hS Z) (hO : IsAlgebraicSpace B S hS O)
    (hN : IsAlgebraicSpace B S hS N) {fZ : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Z hZ}
    (hfZ : fZ ≫ algebraicSpaceStackMap.{u, w} B S hS hZ hY z = f) {ι : O ⟶ Y'} {q : O ⟶ Z}
    (hιg : ι ≫ g = q ≫ z) {x : algebraicSpaceStack.{u, w} B S hS O hO ⟶ 𝒳}
    (he : Nonempty (x ≫ fZ ≅ algebraicSpaceStackMap.{u, w} B S hS hO hZ q))
    {n : N ⟶ Y'} (c : N ⟶ O) (hc : c ≫ ι = n) :
    Nonempty ((algebraicSpaceStackMap.{u, w} B S hS hN hO c ≫ x) ≫ f ≅
      algebraicSpaceStackMap.{u, w} B S hS hN hY (n ≫ g)) := by
  obtain ⟨e⟩ := he
  refine ⟨eqToIso (by rw [← hfZ]) ≪≫ (Bicategory.associator _ _ _).symm ≪≫
    Bicategory.whiskerRightIso (Bicategory.associator _ _ _ ≪≫
      Bicategory.whiskerLeftIso _ e) _ ≪≫ Bicategory.associator _ _ _ ≪≫
    eqToIso ?_⟩
  rw [← algebraicSpaceStackMap_comp B S hS hO hZ hY q z,
    ← algebraicSpaceStackMap_comp B S hS hN hO hY c (q ≫ z), ← hιg, ← Category.assoc, hc]

/-- **The flat case of the proof of [Stacks, Tag 0CQ7].** Let `f : 𝒳 ⟶ Y` be separated, `Y`
quasi-compact and quasi-separated, `W ⊆ Y` a quasi-compact open containing all values of `f`
such that the corestriction `𝒳 ⟶ W` is surjective, flat and locally of finite presentation, and
`V ⊆ W` a quasi-compact open with `𝒳_V ⟶ V` a gerbe. Then the conclusion of Stacks 0CQ7 holds for
`(f, V)`. -/
theorem hasProperCompactifiableCover_of_corestrict
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hf : IsSeparated B S hS f) {W : Subfunctor Y} (hW : Space.IsOpenSubspace B S hS W)
    (hWqc : Space.IsQuasiCompactSpace B S hS W.toFunctor)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
    (hs : IsSurjective B S hS (corestrictAlgebraicSpaceStack f W hW.1 hfW))
    (hfl : AlgebraicStacks.IsFlat B S hS (corestrictAlgebraicSpaceStack f W hW.1 hfW))
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (corestrictAlgebraicSpaceStack f W hW.1 hfW))
    {V : Subfunctor Y} (hV : Space.IsOpenSubspace B S hS V)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor) (hVW : V ≤ W)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  -- Stacks 0CQ6
  obtain ⟨Y', hY', g, hgf, hgs, J, O, hO, ι, q, x, hι, hιg, hcov, hx⟩ :=
    exists_finite_surjective_zariskiLocal_factorization B S hS
      hY hYqc hYqs W hW hWqc _ hs hfl hlfp
  have hg : Space.IsProper B S hS g :=
    (Space.isProper_and_isLocallyQuasiFinite_of_isFinite B S hS hY' hY g hgf).1
  have hY'qc : Space.IsQuasiCompactSpace B S hS Y' :=
    Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hg.2.1.2
  have hVWg : V.preimage g ≤ W.preimage g := fun T _ hz => hVW T hz
  have : CompactSpace (Space.points B S hS (W.preimage g).toFunctor) :=
    (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS _
      (Space.isOpenSubspace_preimage B S hS g W hY hY' hW).1).1 <|
      Space.isQuasiCompactSpace_preimage_toFunctor B S hS B.contains_terminal hY hYqs hY' hY'qc
        W hWqc g
  rcases isEmpty_or_nonempty (Space.points B S hS (W.preimage g).toFunctor) with hE | _
  · refine SectionCover.hasProperCompactifiableCover hf hW hfW V
      ((SectionCover.iUnion hW (K := PEmpty.{u + 1}) (fun _ => ∅) (fun k => k.elim)).mono ?_)
    intro v hv
    obtain ⟨z, -⟩ := exists_pointsMap_preimage_comp_eq_of_isSurjective hgs V v hv
    exact (hE.false (Space.pointsMap B S hS _ (Subfunctor.homOfLe hVWg) z)).elim
  obtain ⟨m, N, hN, hNqc, j, c, hc, hNcov⟩ :=
    exists_finite_isQuasiCompactSpace_cover_of_cover hY' hO hι hcov
  let D : StageData hY f W V (m + 1) :=
    { Y' := ⟨Y', hY'⟩
      qc := hY'qc
      qs := Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hY'
        hYqs (Space.isQuasiSeparated_of_isSeparated B S hS hg.1)
      p := g
      hp := hg
      V' := ⟨V.preimage g, Space.isOpenSubspace_preimage B S hS g V hY hY' hV⟩
      hV'qc := Space.isQuasiCompactSpace_preimage_toFunctor B S hS B.contains_terminal hY hYqs
        hY' hY'qc V hVqc g
      hV'V := le_rfl
      hV'W := hVWg
      Wi := fun k => ⟨N k, hN k⟩
      hWiqc := hNqc
      hcov := hNcov
      x := fun k => algebraicSpaceStackMap.{u, w} B S hS (hN k).1 (hO _) (c k) ≫ x _
      hx := fun k => nonempty_algebraicSpaceStackMap_comp_iso_of_factorization hW.1 (hO _)
        (hN k).1 (corestrictAlgebraicSpaceStack_comp f W hW.1 hfW) (hιg _) (hx _) (c k) (hc k) }
  exact SectionCover.hasProperCompactifiableCover hf hW hfW V
    ((D.sectionCover hf hW hV hG).mono fun v hv =>
      exists_pointsMap_preimage_comp_eq_of_isSurjective hgs V v hv)

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos

end
