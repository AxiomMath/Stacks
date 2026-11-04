module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusNondegeneracy

/-!
# Nondegenerate F-crystals of bounded rank

Let `(E, F_E)` be an `F`-crystal on `CRIS(X/S)` relative to `σ` (`Crystalline.FCrystal`) whose
rank is bounded by `rmax`: every object of the big crystalline site has a covering on each member
of which `E` is a direct sum of at most `rmax` copies of `𝒪_{X/S}`
(`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE`).  If `V : E ⟶ (F_X)_cris^* E`
satisfies `V ∘ F_E = p ^ i • id` and `N ≥ rmax * i`, then `V' = p ^ N • V` satisfies
`V' ∘ F_E = p ^ (N + i) • id` and `F_E ∘ V' = p ^ (N + i) • id`.  Consequently a nondegenerate
`F`-crystal of bounded rank has both properties that are often required of an `F`-crystal in the
literature: a map `V'` with `V' ∘ F_E = F_E ∘ V' = p ^ n • id`, and an integer `j ≥ 0` such that
`p ^ j` kills the kernel and the cokernel of `F_E`.  The rank of `E` is bounded as soon as `X` is
quasi-compact.

## Main results

* `Crystalline.FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_rankLE` — the second-sided identity
  `F_E ∘ (p ^ N • V) = p ^ (N + i) • id`.
* `Crystalline.FCrystal.nsmul_two_sided_of_rankLE` — both identities for `V' = p ^ N • V`.
* `Crystalline.FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero_of_rankLE` — the cokernel of
  `F_E` is killed by `p ^ (N + i)`.
* `Crystalline.FCrystal.exists_nsmul_two_sided_of_rankLE` — a two-sided quasi-inverse of `F_E`.
* `Crystalline.FCrystal.exists_pow_nsmul_kernel_cokernel_eq_zero_of_rankLE` — one power of `p`
  kills the kernel and the cokernel of `F_E`.
* `Crystalline.FCrystal.nondegenerate_conditions_of_rankLE` — both conditions at once.
* `Crystalline.GlobalCrystallineSituation.Thickening.exists_mem_restrictOpenHom_of_mem_topology` —
  a covering sieve of an object of `CRIS(X/S)` contains its restriction to a neighbourhood of each
  point of its ambient scheme.
* `Crystalline.GlobalCrystallineSituation.exists_isFiniteLocallyFreeOfRankLE_of_compactSpace` —
  on a quasi-compact `X`, every finite locally free sheaf of `𝒪_{X/S}`-modules has bounded rank.
* `Crystalline.FCrystal.exists_isFiniteLocallyFreeOfRankLE_of_compactSpace` — so does every
  `F`-crystal, and `Crystalline.FCrystal.exists_hasBoundedCommonLocalRank_of_compactSpace` gives
  the common local rank with its Frobenius pullback.

## Implementation notes

The source reads `F_E` and `V` over an object of the site as two `r × r` matrices for a single
`r`, which presupposes that `E` and `(F_X)_cris^* E` have the same local rank.  That is proved, not
assumed: `Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rankLE` derives it from the bound on
the rank of `E` alone, comparing the two ranks on the Frobenius twist of a trivial thickening,
which maps to the trivial thickening itself by the absolute Frobenius.

The kernel and the cokernel of `F_E` are described by their universal properties: `Ker(F_E)` is
killed by `p ^ j` when every map into `(F_X)_cris^* E` which `F_E` sends to zero is killed by
`p ^ j`, and `Coker(F_E)` is killed by `p ^ j` when every map out of `E` which kills the image of
`F_E` is killed by `p ^ j`.

The source's `N > i · rank(E)` is relaxed to `rmax * i ≤ N`, which is all the computation uses,
and the exponent `rmax * i + i` serves every object of the site at once.

## References

* [Stacks Project, Tag 07N4](https://stacks.math.columbia.edu/tag/07N4)
* [Stacks Project, Tag 07N3](https://stacks.math.columbia.edu/tag/07N3)
* [Stacks Project, Tag 07IB](https://stacks.math.columbia.edu/tag/07IB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Crystalline

open GlobalCrystallineSituation

variable {T : FCrystalSituation.{u}} (E : FCrystal T) {rmax i N : ℕ}

/-- **The second-sided identity for an `F`-crystal of bounded rank.**  Let `(E, F_E)` be an
`F`-crystal whose rank is bounded by `rmax`, let `V` satisfy `F_E ≫ V = p ^ i • 𝟙`, that is
`V ∘ F_E = p ^ i • id`, and let `N ≥ rmax * i`.  Then `(p ^ N • V) ≫ F_E = p ^ (N + i) • 𝟙`,
that is `F_E ∘ V' = p ^ (N + i) • id` for `V' = p ^ N • V`. -/
theorem FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_rankLE
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE
      (crystallineRingedSite T.global) E.crystal rmax)
    {V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal}
    (hV : E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.frobeniusModulePullback.obj E.crystal))
    (hN : rmax * i ≤ N) :
    ((T.global.p ^ N) • V) ≫ E.frobenius = (T.global.p ^ (N + i)) • 𝟙 E.crystal :=
  FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_boundedCommonLocalRank E
    (FCrystal.hasBoundedCommonLocalRank_of_rankLE E hE) hV hN

/-- **The last sentence of [Stacks, Tag 07N4].**  Let `(E, F_E)` be an `F`-crystal whose rank is
bounded by `rmax`, and let `V` be as in [Stacks, Tag 07N3], `F_E ≫ V = p ^ i • 𝟙`, that is
`V ∘ F_E = p ^ i • id`.  Setting `V' = p ^ N • V` with `N ≥ rmax * i` gives both
`V' ∘ F_E = p ^ (N + i) • id` and `F_E ∘ V' = p ^ (N + i) • id`; in diagrammatic order these are
`F_E ≫ V' = p ^ (N + i) • 𝟙` and `V' ≫ F_E = p ^ (N + i) • 𝟙`. -/
@[stacks 07N4 "for an F-crystal (E, F) whose rank is bounded by rmax and V as in Definition \
07N3 with V ∘ F = p ^ i id, the map V' = p ^ N V with N ≥ rmax * i satisfies V' ∘ F = \
p ^ (N + i) id and F ∘ V' = p ^ (N + i) id"]
theorem FCrystal.nsmul_two_sided_of_rankLE
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE
      (crystallineRingedSite T.global) E.crystal rmax)
    {V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal}
    (hV : E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.frobeniusModulePullback.obj E.crystal))
    (hN : rmax * i ≤ N) :
    E.frobenius ≫ ((T.global.p ^ N) • V) =
        (T.global.p ^ (N + i)) • 𝟙 (T.frobeniusModulePullback.obj E.crystal) ∧
      ((T.global.p ^ N) • V) ≫ E.frobenius = (T.global.p ^ (N + i)) • 𝟙 E.crystal :=
  ⟨FCrystal.frobenius_comp_nsmul E hV,
    FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_rankLE E hE hV hN⟩

/-- **The cokernel of the Frobenius structure map of an `F`-crystal of bounded rank is killed by
a power of `p`.**  If the rank of `E` is bounded by `rmax`, `F_E ≫ V = p ^ i • 𝟙` and
`N ≥ rmax * i`, then every map out of `E` which kills the image of `F_E` is killed by
`p ^ (N + i)`. -/
theorem FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero_of_rankLE
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE
      (crystallineRingedSite T.global) E.crystal rmax)
    {V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal}
    (hV : E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.frobeniusModulePullback.obj E.crystal))
    (hN : rmax * i ≤ N)
    {Q : SheafOfModules.{u} (crystallineStructureSheaf T.global)} (q : E.crystal ⟶ Q)
    (hq : E.frobenius ≫ q = 0) : (T.global.p ^ (N + i)) • q = 0 :=
  FCrystal.nsmul_eq_zero_of_frobenius_comp_eq_zero E
    (FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_rankLE E hE hV hN) q hq

/-- **A nondegenerate `F`-crystal of bounded rank has a two-sided quasi-inverse of its Frobenius
structure map.**  There are an integer `n` and a map `V' : E ⟶ (F_X)_cris^* E` with
`V' ∘ F_E = p ^ n • id` and `F_E ∘ V' = p ^ n • id`; one may take `n = rmax * i + i` and
`V' = p ^ (rmax * i) • V` for `V` and `i` as in the nondegeneracy condition. -/
theorem FCrystal.exists_nsmul_two_sided_of_rankLE
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE
      (crystallineRingedSite T.global) E.crystal rmax) (hnd : E.Nondegenerate) :
    ∃ (n : ℕ) (V' : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal),
      E.frobenius ≫ V' = (T.global.p ^ n) • 𝟙 (T.frobeniusModulePullback.obj E.crystal) ∧
        V' ≫ E.frobenius = (T.global.p ^ n) • 𝟙 E.crystal := by
  obtain ⟨i, V, hV⟩ := hnd
  exact ⟨rmax * i + i, (T.global.p ^ (rmax * i)) • V,
    FCrystal.nsmul_two_sided_of_rankLE E hE hV le_rfl⟩

/-- **One power of `p` kills the kernel and the cokernel of the Frobenius structure map of a
nondegenerate `F`-crystal of bounded rank.**  There is an integer `j ≥ 0` such that every map into
`(F_X)_cris^* E` which `F_E` sends to zero, and every map out of `E` which kills the image of
`F_E`, is killed by `p ^ j`; one may take `j = rmax * i + i`. -/
theorem FCrystal.exists_pow_nsmul_kernel_cokernel_eq_zero_of_rankLE
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE
      (crystallineRingedSite T.global) E.crystal rmax) (hnd : E.Nondegenerate) :
    ∃ j : ℕ,
      (∀ (Q : SheafOfModules.{u} (crystallineStructureSheaf T.global))
        (q : Q ⟶ T.frobeniusModulePullback.obj E.crystal),
        q ≫ E.frobenius = 0 → (T.global.p ^ j) • q = 0) ∧
      (∀ (Q : SheafOfModules.{u} (crystallineStructureSheaf T.global))
        (q : E.crystal ⟶ Q), E.frobenius ≫ q = 0 → (T.global.p ^ j) • q = 0) :=
  FCrystal.exists_pow_nsmul_kernel_cokernel_eq_zero_of_boundedCommonLocalRank E
    (FCrystal.hasBoundedCommonLocalRank_of_rankLE E hE) hnd

/-- **[Stacks, Tag 07N4]: for an `F`-crystal of bounded rank, both conditions follow from
nondegeneracy.**  Let `(E, F)` be an `F`-crystal as in [Stacks, Tag 07N3] whose rank is bounded
by `rmax`.  If `E` is nondegenerate, that is `V ∘ F = p ^ i • id` for some `i ≥ 0` and some
`V : E ⟶ (F_X)_cris^* E`, then

* there are `n` and `V'` with `V' ∘ F = p ^ n • id` and `F ∘ V' = p ^ n • id`, the condition
  often assumed in the literature, and
* there is an integer `j ≥ 0` such that `Ker(F)` and `Coker(F)` are killed by `p ^ j`, the
  condition needed for [Stacks, Tag 07N5].

The kernel and the cokernel are described by their universal properties: every map into
`(F_X)_cris^* E` which `F` sends to zero, and every map out of `E` which kills the image of `F`,
is killed by `p ^ j`. -/
@[stacks 07N4 "if the rank of E is bounded, both conditions follow from the nondegeneracy \
condition of Definition 07N3: there is V' with V' ∘ F = p ^ n id and F ∘ V' = p ^ n id, and there \
is j ≥ 0 such that Ker(F) and Coker(F) are killed by p ^ j"]
theorem FCrystal.nondegenerate_conditions_of_rankLE
    (hE : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE
      (crystallineRingedSite T.global) E.crystal rmax) (hnd : E.Nondegenerate) :
    (∃ (n : ℕ) (V' : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal),
        E.frobenius ≫ V' = (T.global.p ^ n) • 𝟙 (T.frobeniusModulePullback.obj E.crystal) ∧
          V' ≫ E.frobenius = (T.global.p ^ n) • 𝟙 E.crystal) ∧
      ∃ j : ℕ,
        (∀ (Q : SheafOfModules.{u} (crystallineStructureSheaf T.global))
          (q : Q ⟶ T.frobeniusModulePullback.obj E.crystal),
          q ≫ E.frobenius = 0 → (T.global.p ^ j) • q = 0) ∧
        (∀ (Q : SheafOfModules.{u} (crystallineStructureSheaf T.global))
          (q : E.crystal ⟶ Q), E.frobenius ≫ q = 0 → (T.global.p ^ j) • q = 0) :=
  ⟨FCrystal.exists_nsmul_two_sided_of_rankLE E hE hnd,
    FCrystal.exists_pow_nsmul_kernel_cokernel_eq_zero_of_rankLE E hE hnd⟩

namespace GlobalCrystallineSituation

namespace Thickening

variable {S : GlobalCrystallineSituation.{u}}

/-- **A restriction factors through a Cartesian open immersion near any point of its image.**  If
`q : B ⟶ A` is Cartesian and an open immersion on ambient schemes, then for every point `x` of the
image of `q` on ambient schemes there is an open `V ∋ x` of the ambient scheme of `A` such that the
restriction `A|_V ⟶ A` factors through `q`. -/
theorem exists_restrictOpenHom_eq_comp {A B : Thickening S} (q : B ⟶ A) (hq : IsCartesian q)
    [IsOpenImmersion q.targetHom.hom] {x : A.thickening.target.scheme}
    (hx : x ∈ Set.range q.targetHom.hom.base) :
    ∃ (V : A.thickening.target.scheme.Opens) (g : A.restrictOpen V ⟶ B),
      x ∈ V ∧ g ≫ q = A.restrictOpenHom V := by
  obtain ⟨y, hy⟩ := hx
  exact ⟨pullbackOpen q (𝟙 A), pullbackLiftHom q (𝟙 A) hq, ⟨y, hy⟩, by
    rw [pullbackLiftHom_comp, Category.comp_id]⟩

/-- **A covering sieve of an object of `CRIS(X/S)` contains a restriction to a neighbourhood of
each point.**  For a covering sieve `R` of `A` and a point `x` of the ambient scheme of `A`, there
is an open `V ∋ x` of that ambient scheme such that the restriction `A|_V ⟶ A` belongs to `R`.
The proof is an induction over the saturation generating the topology from the Zariski covering
families. -/
theorem exists_mem_restrictOpenHom_of_mem_topology {A : Thickening S} {R : Sieve A}
    (hR : R ∈ topology S A) (x : A.thickening.target.scheme) :
    ∃ V : A.thickening.target.scheme.Opens, x ∈ V ∧ R (A.restrictOpenHom V) := by
  rw [topology_eq_coverage_toGrothendieck] at hR
  suffices key : ∀ (B : Thickening S) (R : Sieve B), Coverage.Saturate (coverage S) B R →
      ∀ x : B.thickening.target.scheme,
        ∃ V : B.thickening.target.scheme.Opens, x ∈ V ∧ R (B.restrictOpenHom V) from
    key A R (Coverage.mem_toGrothendieck.mp hR) x
  intro B R hR
  induction hR with
  | of B P hP =>
    intro x
    obtain ⟨E, rfl, hE⟩ := hP
    have hE' : (∀ x, ∃ i, x ∈ Set.range ((E.f i).targetHom.hom).base) ∧
        ∀ i, IsOpenImmersion (E.f i).targetHom.hom := by
      simpa [targetPresieve] using hE.2
    obtain ⟨i, hi⟩ := hE'.1 x
    have := hE'.2 i
    obtain ⟨V, g, hxV, hg⟩ := exists_restrictOpenHom_eq_comp (E.f i) (hE.1 i) hi
    exact ⟨V, hxV, ⟨E.X i, g, E.f i, ⟨i⟩, hg⟩⟩
  | top B => exact fun _ => ⟨⊤, trivial, trivial⟩
  | transitive B R₁ R₂ _ _ ih₁ ih₂ =>
    intro x
    obtain ⟨V, hxV, hV⟩ := ih₁ x
    obtain ⟨W, hyW, hW⟩ := ih₂ hV (⟨x, hxV⟩ : V.toScheme)
    let q := (B.restrictOpen V).restrictOpenHom W ≫ B.restrictOpenHom V
    have hq : IsCartesian q :=
      (isCartesian_restrictOpenHom (B.restrictOpen V) W).paste_horiz
        (isCartesian_restrictOpenHom B V)
    have h₁ : IsOpenImmersion ((B.restrictOpen V).restrictOpenHom W).targetHom.hom :=
      inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι W))
    have h₂ : IsOpenImmersion (B.restrictOpenHom V).targetHom.hom :=
      inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι V))
    have : IsOpenImmersion q.targetHom.hom :=
      IsOpenImmersion.comp ((B.restrictOpen V).restrictOpenHom W).targetHom.hom
        (B.restrictOpenHom V).targetHom.hom
    obtain ⟨V', g, hxV', hg⟩ :=
      exists_restrictOpenHom_eq_comp q hq (x := x) ⟨⟨⟨x, hxV⟩, hyW⟩, rfl⟩
    exact ⟨V', hxV', hg ▸ R₂.downward_closed hW g⟩

end Thickening

end GlobalCrystallineSituation

/-- **On a quasi-compact `X`, a finite locally free sheaf of `𝒪_{X/S}`-modules has bounded
rank.**  The trivial thickening `(X, X, ∅)` is an object of `CRIS(X/S)`; a covering on whose
members `M` is free restricts, near each point of `X`, to a neighbourhood `O ⊆ X` over which `M`
is free of some rank, and finitely many such neighbourhoods cover `X`.  Let `rmax` be the largest
of their ranks.  Over a member `V` of any trivialising covering of any object, with `M` free of
rank `s` over `V`, either the ring of sections over `V` is zero, and then `M` is free of rank `0`
over `V`, or the thickened scheme of `V` has a point, lying over a point of some `O`, and then the
trivial thickening of a neighbourhood of that point maps both to `V` and to `(O, O, ∅)`, has
nontrivial ring of sections, and so `s` is the rank of `M` over `O`. -/
theorem GlobalCrystallineSituation.exists_isFiniteLocallyFreeOfRankLE_of_compactSpace
    (S : GlobalCrystallineSituation.{u}) [CompactSpace S.X]
    (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    ∃ rmax : ℕ, AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE
      (crystallineRingedSite S) M rmax := by
  classical
  rw [SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit] at hM
  let X₀ : Thickening S := (free S).obj (Over.mk (𝟙 S.X))
  obtain ⟨I, V, f, hcov, hfree⟩ := hM X₀
  choose n ιn hιn using hfree
  have hpt : ∀ x : S.X, ∃ (O : S.X.Opens) (i : I), x ∈ O ∧ Nonempty (X₀.restrictOpen O ⟶ V i) := by
    intro x
    obtain ⟨O, hxO, hO⟩ := Thickening.exists_mem_restrictOpenHom_of_mem_topology hcov x
    obtain ⟨i, a, -⟩ := Sieve.ofArrows.exists hO
    exact ⟨O, i, hxO, ⟨a⟩⟩
  choose O i hxO a using hpt
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (O x : Set S.X))
    (fun x => (O x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxO x⟩)
  refine ⟨t.sup (fun x => n (i x)), fun U => ?_⟩
  obtain ⟨J', V', f', hcov', hfree'⟩ := hM U
  refine ⟨J', V', f', hcov', fun j => ?_⟩
  obtain ⟨s, ιs, ⟨hs⟩⟩ := hfree' j
  by_cases hnt : Nontrivial ((crystallineStructureSheaf S).obj.obj (Opposite.op (V' j)))
  · have : Nontrivial Γ((V' j).thickening.target.scheme, ⊤) := hnt
    obtain ⟨u⟩ := (V' j).nonempty_source
    obtain ⟨k, hk, hxk⟩ : ∃ k ∈ t, (V' j).toX.base u ∈ O k := by
      simpa using ht (Set.mem_univ ((V' j).toX.base u))
    let O' : (V' j).thickening.source.Opens := (V' j).toX ⁻¹ᵁ O k
    let Y : Over S.X := Over.mk (O'.ι ≫ (V' j).toX)
    let b : (free S).obj Y ⟶ V' j :=
      ((freeForgetAdjunction S).homEquiv Y (V' j)).symm (Over.homMk O'.ι rfl)
    let c : (free S).obj Y ⟶ X₀.restrictOpen (O k) :=
      ((freeForgetAdjunction S).homEquiv Y (X₀.restrictOpen (O k))).symm
        (Over.homMk ((V' j).toX.resLE ((𝟙 S.X) ⁻¹ᵁ O k) O' fun _ h => h) (by
          show (V' j).toX.resLE ((𝟙 S.X) ⁻¹ᵁ O k) O' (fun _ h => h) ≫
              ((𝟙 S.X) ⁻¹ᵁ O k).ι ≫ 𝟙 S.X = O'.ι ≫ (V' j).toX
          rw [Category.comp_id]
          exact Scheme.Hom.resLE_comp_ι _ _))
    have hY : Nontrivial ((crystallineStructureSheaf S).obj.obj (Opposite.op ((free S).obj Y))) :=
      have : Nonempty (⊤ : O'.toScheme.Opens) := ⟨⟨⟨u, hxk⟩, trivial⟩⟩
      (inferInstance : Nontrivial Γ(O'.toScheme, ⊤))
    have hsn : s = n (i k) := _root_.SheafOfModules.eq_of_isColimit_cofan_unit (ιn (i k))
      (hιn (i k)).some ιs hs (c ≫ (a k).some) b (crystallineStructureSheaf_mul_comm S _) hY
    exact ⟨s, hsn ▸ Finset.le_sup (f := fun x => n (i x)) hk, ιs, ⟨hs⟩⟩
  · exact ⟨0, Nat.zero_le _, Fin.elim0,
      _root_.SheafOfModules.nonempty_isColimit_cofan_fin_zero M (V' j)
        (not_nontrivial_iff_subsingleton.mp hnt) _⟩

/-- If `X` is quasi-compact, there is an integer `rmax` such that every object of `CRIS(X/S)` has a
covering on each member of which `E` is a direct sum of at most `rmax` copies of `𝒪_{X/S}`. -/
@[stacks 07N4 "the rank of E is bounded if X is quasi-compact"]
theorem FCrystal.exists_isFiniteLocallyFreeOfRankLE_of_compactSpace [CompactSpace T.global.X] :
    ∃ rmax : ℕ, AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRankLE
      (crystallineRingedSite T.global) E.crystal rmax :=
  T.global.exists_isFiniteLocallyFreeOfRankLE_of_compactSpace E.crystal
    E.isFiniteLocallyFreeQuasicoherentCrystal.isFiniteLocallyFree

/-- An `F`-crystal on a quasi-compact `X` has a bounded common local rank with its Frobenius
pullback. -/
theorem FCrystal.exists_hasBoundedCommonLocalRank_of_compactSpace [CompactSpace T.global.X] :
    ∃ rmax : ℕ, E.HasBoundedCommonLocalRank rmax :=
  E.exists_isFiniteLocallyFreeOfRankLE_of_compactSpace.imp
    fun _ => E.hasBoundedCommonLocalRank_of_rankLE

end Crystalline

end
