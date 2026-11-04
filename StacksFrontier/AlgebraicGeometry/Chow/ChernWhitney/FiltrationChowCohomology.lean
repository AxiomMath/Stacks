module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.WhitneyChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassBivariant
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf

/-!
# The total Chern class of a filtration with invertible quotients

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let
`ℒ_1, …, ℒ_r` be invertible `𝒪_X`-modules and let `ℰ` be an `𝒪_X`-module with a filtration

  `0 = ℰ_0 ⊂ ℰ_1 ⊂ ℰ_2 ⊂ … ⊂ ℰ_r = ℰ`,   `ℰ_i/ℰ_{i-1} ≅ ℒ_i`.

Then `ℰ` is finite locally free of rank `r`, and with `x_i = c_1(ℒ_i)` the total Chern class is

  `c(ℰ) = ∏_{i=1}^r (1 + x_i)`   in `A^*(X)`,

which is [Stacks, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ). Here `A^*(X)` is the
Chow cohomology ring of Stacks 0B7E, `c(ℰ)` is the total Chern class of
`Stacks.Chow.totalChernClassCohomology` and `x_i ∈ A^1(X)` is the first Chern class of Stacks
0B77, `Stacks.Chow.GenuineChern.firstChernClass`. The product is taken in the order
`(1 + x_1)(1 + x_2) ⋯ (1 + x_r)`.

The proof is the source's: induction along the filtration, applying the Whitney formula of
Stacks 02UI (`Stacks.Chow.totalChernClassCohomology_eq_mul_of_shortExact_of_rank`) to the short
exact sequences `0 ⟶ ℰ_{i-1} ⟶ ℰ_i ⟶ ℒ_i ⟶ 0`. Its two ends are the total Chern classes of a
zero module, which is `1`, and of an invertible module `ℒ`, which is `1 + c_1(ℒ)`.

## Main results

* `Stacks.Chow.isFiniteLocallyFreeOfRank_zero_of_isZero` — a zero module is finite locally free
  of rank `0`.
* `Stacks.Chow.totalChernClassCohomology_of_rank_zero` — `c(ℱ) = 1` in rank `0`.
* `Stacks.Chow.totalChernClassCohomology_of_isInvertible` — `c(ℒ) = 1 + c_1(ℒ)`.
* `Stacks.Chow.totalChernClassCohomology_eq_of_iso` — isomorphic modules have the same total
  Chern class.
* `Stacks.Chow.totalChernClassCohomology_eq_prod_of_chain` — the product formula for a chain of
  short exact sequences `0 ⟶ G_i ⟶ G_{i+1} ⟶ L_i ⟶ 0` starting at a zero module.
* `Stacks.Chow.totalChernClassCohomology_eq_prod_of_filtration` — **Stacks 02UJ**.

## References

* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject

universe u

namespace Stacks.Chow

/-! ### Modules of rank zero -/

/-- **A zero module is finite locally free of rank `0`**: over the whole scheme it is isomorphic
to the free module on the empty type, both being zero. -/
theorem isFiniteLocallyFreeOfRank_zero_of_isZero {X : Scheme.{u}} {M : X.Modules}
    (hM : IsZero M) : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 0 :=
  (Scheme.Modules.isFiniteLocallyFreeOfRank_iff M 0).mp fun _ ↦
    ⟨⊤, trivial, ⟨(Functor.map_isZero (Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι) hM).iso
      (_root_.SheafOfModules.isZero_free_of_isEmpty _)⟩⟩

/-! ### A filtration with invertible quotients, as a chain of short exact sequences -/

section Chain

variable {X : Scheme.{u}}

/-- **The members of a chain with invertible quotients are finite locally free.** Given modules
`G_0, …, G_n` with `G_0 = 0` and short exact sequences `0 ⟶ G_i ⟶ G_{i+1} ⟶ L_i ⟶ 0` with `L_i`
invertible, the module `G_n` is finite locally free of rank `n`. -/
theorem isFiniteLocallyFreeOfRank_of_chain : ∀ (n : ℕ) (G : Fin (n + 1) → X.Modules)
    (L : Fin n → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L i)]
    (ι : ∀ i : Fin n, G i.castSucc ⟶ G i.succ) (π : ∀ i : Fin n, G i.succ ⟶ L i)
    (w : ∀ i, ι i ≫ π i = 0) (_ : ∀ i, (ShortComplex.mk (ι i) (π i) (w i)).ShortExact)
    (_ : IsZero (G 0)),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (G (Fin.last n)) n
  | 0, _, _, _, _, _, _, _, h0 => isFiniteLocallyFreeOfRank_zero_of_isZero h0
  | n + 1, G, L, _, ι, π, w, hS, h0 => by
      have hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (G (Fin.last n).castSucc) n :=
        isFiniteLocallyFreeOfRank_of_chain n (fun j ↦ G j.castSucc) (fun j ↦ L j.castSucc)
          (fun i ↦ ι i.castSucc) (fun i ↦ π i.castSucc) (fun i ↦ w i.castSucc)
          (fun i ↦ hS i.castSucc) (by rwa [Fin.castSucc_zero])
      exact GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ (hS (Fin.last n)) n 1 hG
        (GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible (L (Fin.last n)))

end Chain

/-! ### The total Chern classes of the ends -/

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **`c_0(ℱ) = 1` in `A^*(Y)`**: the degree-`0` component of the total Chern class of a finite
locally free module, placed in `A^*(Y)`, is the unit. -/
theorem of_totalChern_zero (F : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    letI := chowCohomologyRingOfInvertible C sY
    DirectSum.of (fun p ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
      ((0 : ℕ) : ℤ) (totalChern C sY F r 0) = 1 := by
  let := chowCohomologyRingOfInvertible C sY
  rw [totalChern_apply_zero, TotalChowClass.one_apply_zero, of_bivariantClassDegreeCongr]
  rfl

/-- **The total Chern class of a module of rank `0` is `1`.** -/
theorem totalChernClassCohomology_of_rank_zero (F : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 0] :
    letI := chowCohomologyRingOfInvertible C sY
    totalChernClassCohomology C sY F 0 = 1 := by
  rw [totalChernClassCohomology_eq_toChowCohomology, TotalChowClass.toChowCohomology,
    Finset.sum_range_one]
  exact of_totalChern_zero C sY F 0

/-- **The total Chern class of an invertible module.** For an invertible module `ℒ`, which is
finite locally free of rank one, `c(ℒ) = 1 + c_1(ℒ)` in `A^*(Y)`, with `c_1(ℒ) ∈ A^1(Y)` the first
Chern class of Stacks 0B77. -/
theorem totalChernClassCohomology_of_isInvertible (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    letI := chowCohomologyRingOfInvertible C sY
    haveI := GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible L
    totalChernClassCohomology C sY L 1 =
      1 + DirectSum.of (fun p ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) 1
        (GenuineChern.firstChernClass C sY L) := by
  let := chowCohomologyRingOfInvertible C sY
  have := GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible L
  rw [totalChernClassCohomology_eq_toChowCohomology, TotalChowClass.toChowCohomology,
    Finset.sum_range_succ, Finset.sum_range_one, of_totalChern_zero,
    totalChern_apply C sY L 1 ⟨1, by omega⟩]
  rfl

/-- **The total Chern class depends only on the isomorphism class.** This is the Whitney formula
of Stacks 02UI for the short exact sequence `0 ⟶ 0 ⟶ ℱ ⟶ 𝒢 ⟶ 0` given by an isomorphism. -/
theorem totalChernClassCohomology_eq_of_iso {F G : Y.Modules} (e : F ≅ G) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G r] :
    totalChernClassCohomology C sY F r = totalChernClassCohomology C sY G r := by
  let := chowCohomologyRingOfInvertible C sY
  let S : ShortComplex Y.Modules := ShortComplex.mk (0 : (0 : Y.Modules) ⟶ F) e.hom zero_comp
  have hS : S.ShortExact :=
    { exact := (S.exact_iff_mono rfl).mpr (inferInstanceAs (Mono e.hom))
      mono_f := mono_of_source_iso_zero _ (Iso.refl _)
      epi_g := inferInstanceAs (Epi e.hom) }
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ 0 :=
    isFiniteLocallyFreeOfRank_zero_of_isZero (isZero_zero _)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r :=
    ‹AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r›
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r :=
    ‹AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G r›
  have h := totalChernClassCohomology_eq_mul_of_shortExact_of_rank C sY S hS 0 r r
  rwa [totalChernClassCohomology_of_rank_zero, one_mul] at h

/-! ### The product formula -/

/-- **The product formula along a chain.** Given modules `G_0, …, G_n` with `G_0 = 0` and short
exact sequences `0 ⟶ G_i ⟶ G_{i+1} ⟶ L_i ⟶ 0` with `L_i` invertible, the total Chern class of
`G_n`, which is finite locally free of rank `n`, is

  `c(G_n) = (1 + c_1(L_0)) (1 + c_1(L_1)) ⋯ (1 + c_1(L_{n-1}))`   in `A^*(Y)`. -/
theorem totalChernClassCohomology_eq_prod_of_chain : ∀ (n : ℕ) (G : Fin (n + 1) → Y.Modules)
    (L : Fin n → Y.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property (L i)]
    (ι : ∀ i : Fin n, G i.castSucc ⟶ G i.succ) (π : ∀ i : Fin n, G i.succ ⟶ L i)
    (w : ∀ i, ι i ≫ π i = 0) (hS : ∀ i, (ShortComplex.mk (ι i) (π i) (w i)).ShortExact)
    (h0 : IsZero (G 0)),
    letI := chowCohomologyRingOfInvertible C sY
    haveI := isFiniteLocallyFreeOfRank_of_chain n G L ι π w hS h0
    totalChernClassCohomology C sY (G (Fin.last n)) n =
      (List.ofFn fun i ↦ 1 + DirectSum.of
        (fun p ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) 1
          (GenuineChern.firstChernClass C sY (L i))).prod
  | 0, G, _, _, _, _, _, _, h0 => by
      have := isFiniteLocallyFreeOfRank_zero_of_isZero h0
      exact totalChernClassCohomology_of_rank_zero C sY (G 0)
  | n + 1, G, L, _, ι, π, w, hS, h0 => by
      let := chowCohomologyRingOfInvertible C sY
      have h0' : IsZero (G (Fin.castSucc 0)) := by rwa [Fin.castSucc_zero]
      have hI := totalChernClassCohomology_eq_prod_of_chain n (fun j ↦ G j.castSucc)
        (fun j ↦ L j.castSucc) (fun i ↦ ι i.castSucc) (fun i ↦ π i.castSucc)
        (fun i ↦ w i.castSucc) (fun i ↦ hS i.castSucc) h0'
      have := isFiniteLocallyFreeOfRank_of_chain n (fun j ↦ G j.castSucc) (fun j ↦ L j.castSucc)
        (fun i ↦ ι i.castSucc) (fun i ↦ π i.castSucc) (fun i ↦ w i.castSucc)
        (fun i ↦ hS i.castSucc) h0'
      have := GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible (L (Fin.last n))
      let S := ShortComplex.mk (ι (Fin.last n)) (π (Fin.last n)) (w (Fin.last n))
      have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (n + 1) :=
        isFiniteLocallyFreeOfRank_of_chain (n + 1) G L ι π w hS h0
      rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
      exact (totalChernClassCohomology_eq_mul_of_shortExact_of_rank C sY S (hS (Fin.last n))
        n (n + 1) 1).trans
        (congrArg₂ (· * ·) hI (totalChernClassCohomology_of_isInvertible C sY (L (Fin.last n))))

/-- A subobject equal to `⊥` is a zero module. -/
private theorem isZero_of_eq_bot {E : Y.Modules} {A : Subobject E} (h : A = ⊥) :
    IsZero (A : Y.Modules) :=
  (isZero_zero Y.Modules).of_iso (Subobject.isoOfEq _ _ h ≪≫ Subobject.botCoeIsoZero)

/-- The members of a filtration `0 = ℰ_0 ⊂ ℰ_1 ⊂ … ⊂ ℰ_r` of `ℰ` with `ℰ_i/ℰ_{i-1} ≅ ℒ_i` form
a chain of short exact sequences `0 ⟶ ℰ_{i-1} ⟶ ℰ_i ⟶ ℒ_i ⟶ 0`. -/
theorem shortExact_ofLE_cokernel {E : Y.Modules} {A B : Subobject E} (h : A ≤ B) {L : Y.Modules}
    (e : cokernel (Subobject.ofLE A B h) ≅ L) :
    (ShortComplex.mk (Subobject.ofLE A B h) (cokernel.π _ ≫ e.hom)
      (by rw [cokernel.condition_assoc, zero_comp])).ShortExact where
  exact := ShortComplex.exact_of_iso
    (S₁ := ShortComplex.mk (Subobject.ofLE A B h) (cokernel.π _) (cokernel.condition _))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simp))
    (ShortComplex.exact_cokernel (Subobject.ofLE A B h))

/-- **A module with a filtration with invertible quotients is finite locally free.** If `ℰ` has a
filtration `0 = ℰ_0 ⊂ ℰ_1 ⊂ … ⊂ ℰ_r = ℰ` with `ℰ_i/ℰ_{i-1} ≅ ℒ_i` invertible, then `ℰ` is finite
locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_filtration {r : ℕ} (E : Y.Modules) (L : Fin r → Y.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property (L i)]
    (F : Fin (r + 1) → Subobject E) (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r,
      cokernel (Subobject.ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (@asIso _ _ _ _ (F (Fin.last r)).arrow ((Subobject.isIso_arrow_iff_eq_top _).mpr hr))
    (isFiniteLocallyFreeOfRank_of_chain r (fun i ↦ (F i : Y.Modules)) L
      (fun i ↦ Subobject.ofLE _ _ (hF i.castSucc_le_succ)) (fun i ↦ cokernel.π _ ≫ (e i).hom) _
      (fun i ↦ shortExact_ofLE_cokernel _ (e i))
      (isZero_of_eq_bot h0))

/-- **Stacks 02UJ.** Let `X` be locally of finite type over the base, let `ℒ_1, …, ℒ_r` be
invertible `𝒪_X`-modules and let `ℰ` be an `𝒪_X`-module with a filtration by submodules

  `0 = ℰ_0 ⊂ ℰ_1 ⊂ ℰ_2 ⊂ … ⊂ ℰ_r = ℰ`   such that   `ℰ_i/ℰ_{i-1} ≅ ℒ_i`.

Then `ℰ` is finite locally free of rank `r`
(`Stacks.Chow.isFiniteLocallyFreeOfRank_of_filtration`), and, setting `x_i = c_1(ℒ_i)`,

  `c(ℰ) = ∏_{i=1}^r (1 + x_i)`   in `A^*(X)`.

The filtration is indexed by `Fin (r + 1)` and the invertible modules by `Fin r`, so that `ℒ i` is
the quotient `ℰ_{i+1}/ℰ_i`; the product is `(1 + x_1)(1 + x_2) ⋯ (1 + x_r)` in this order. -/
@[stacks 02UJ "c(E) = prod_{i=1}^r (1 + c_1(L_i)) in the Chow cohomology ring A^*(X) of Stacks \
  0B7E, for E with a filtration 0 = E_0 ⊂ E_1 ⊂ ... ⊂ E_r = E by subobjects with \
  E_i/E_{i-1} ≅ L_i invertible, on X locally of finite type over the base; c_1(L_i) is the class \
  of Stacks 0B77 and E is shown to be finite locally free of rank r"]
theorem totalChernClassCohomology_eq_prod_of_filtration (r : ℕ) (E : Y.Modules)
    (L : Fin r → Y.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property (L i)]
    (F : Fin (r + 1) → Subobject E) (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r,
      cokernel (Subobject.ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    letI := chowCohomologyRingOfInvertible C sY
    haveI := isFiniteLocallyFreeOfRank_of_filtration E L F hF h0 hr e
    totalChernClassCohomology C sY E r =
      (List.ofFn fun i ↦ 1 + DirectSum.of
        (fun p ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) 1
          (GenuineChern.firstChernClass C sY (L i))).prod := by
  let := chowCohomologyRingOfInvertible C sY
  have hz := isZero_of_eq_bot h0
  have := isFiniteLocallyFreeOfRank_of_filtration E L F hF h0 hr e
  have := isFiniteLocallyFreeOfRank_of_chain r (fun i ↦ (F i : Y.Modules)) L
    (fun i ↦ Subobject.ofLE _ _ (hF i.castSucc_le_succ)) (fun i ↦ cokernel.π _ ≫ (e i).hom) _
    (fun i ↦ shortExact_ofLE_cokernel _ (e i)) hz
  rw [← totalChernClassCohomology_eq_of_iso C sY
    (@asIso _ _ _ _ (F (Fin.last r)).arrow ((Subobject.isIso_arrow_iff_eq_top _).mpr hr)) r]
  exact totalChernClassCohomology_eq_prod_of_chain C sY r (fun i ↦ (F i : Y.Modules)) L
    (fun i ↦ Subobject.ofLE _ _ (hF i.castSucc_le_succ)) (fun i ↦ cokernel.π _ ≫ (e i).hom) _
    (fun i ↦ shortExact_ofLE_cokernel _ (e i)) hz

end Stacks.Chow

end
