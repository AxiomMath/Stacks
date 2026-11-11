module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassBivariantComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.TotalChernClassFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackMonoInvertibleCokernel

/-!
# Stacks 0ESA: the total Chern class of a module with a filtration with invertible quotients

In Situation 0EDT let `X/B` be good, let `ℒ_1, …, ℒ_r` be invertible `𝒪_X`-modules and let `ℰ`
be a finite locally free `𝒪_X`-module of rank `r` with a filtration

  `0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ`,   `ℰ_i / ℰ_{i-1} ≅ ℒ_i`.

With `x_i = c₁(ℒ_i)`, **Stacks 0ESA** asserts `c(ℰ) = ∏_{i=1}^r (1 + x_i)` in `A^*(X)`.

The classes are those of Stacks 0ERZ: `c_j(ℰ) ∈ A^j(X)` is `AlgebraicGeometry.Space.chernClass`,
the bivariant class whose cap operation on a good test space `g : X' ⟶ X` is the map
`c_j(ℰ) ∩ - : CH_k(X') ⟶ CH_{k-j}(X')` of Stacks 0ERY (`AlgebraicGeometry.Space.chernCap`, read on
`X ×_X X' ≅ X'` by `AlgebraicGeometry.Space.chernClass_cap`), and
`c(ℰ) = c_0(ℰ) + ⋯ + c_r(ℰ)` is `AlgebraicGeometry.Space.totalChernClass`. The product of
`A^*(X)` is composition of bivariant classes (Stacks 0ERK), and a class is determined by its cap
operations (Stacks 0ERJ). So the identity in `A^*(X)` is the identity

  `c(ℰ) ∩ - = (1 + c₁(ℒ_1) ∩ -) ∘ ⋯ ∘ (1 + c₁(ℒ_r) ∩ -)`

of operations on `⨁_k CH_k(X')`, for every good test space `g : X' ⟶ X`, which is what is
stated here (`AlgebraicGeometry.Space.chernCapGraded` is `c_j(ℰ) ∩ -` on `⨁_k CH_k(X')`).

## Main definitions

* `AlgebraicGeometry.Space.chernCapGraded`: the cap operation `c_j(ℰ) ∩ -` of Stacks 0ERY on
  `⨁_k CH_k(X')`, for a good test space `X' ⟶ X`.
* `AlgebraicGeometry.Space.totalChernCapGraded`: `c(ℰ) ∩ - = ∑_j c_j(ℰ) ∩ -` there.

## Main results

* `AlgebraicGeometry.Space.totalChernCapGraded_eq_prod_one_add_chernCapGraded`: **Stacks 0ESA.**

## Implementation notes

The proof is the source's, induction along the filtration with Stacks 0ES8, carried out on every
test space `X'`: the inverse image of the filtration along `g` is a filtration of `g^*ℰ` with
invertible quotients `g^*ℒ_i` (`AlgebraicGeometry.Space.exists_filtration_modulePullback`), the
product formula holds for it on `CH_*(X')`
(`AlgebraicGeometry.Space.PrivateChern.totalChernCap_eq_prod_one_add_chernCap_one`), and the cap
operations of Stacks 0ERY on `X'` are the Chern classes of `g^*ℰ` on `CH_*(X')`
(`AlgebraicGeometry.Space.chowGroupCanonicalToChowHomology_chernCap`), the Chow groups of
Stacks 0EQ6 being identified with the summands of `CH_*(X')` by
`AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup`.

## References

* [Stacks Project, Tag 0ESA](https://stacks.math.columbia.edu/tag/0ESA)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

universe u

namespace AlgebraicGeometry.Space

open PrivateChern

/-! ### The cap operations on the graded Chow group of a test space -/

section Graded

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)

/-- **The cap operation `c_j(ℰ) ∩ -` of Stacks 0ERY on `⨁_k CH_k(X')`**, for a good test space
`g : X' ⟶ X`: on `CH_k(X')` it is `AlgebraicGeometry.Space.chernCap`, with values in
`CH_{k-j}(X')`. It is the cap operation of `c_j(ℰ) ∈ A^j(X)` (Stacks 0ERZ,
`AlgebraicGeometry.Space.chernClass_cap`). -/
def chernCapGraded (r : ℕ) (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (j : Fin (r + 1)) :
    AddMonoid.End (DirectSum ℤ fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) :=
  DirectSum.toAddMonoid fun k =>
    (DirectSum.of (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (k - ((j : ℕ) : ℤ))).comp
      (Space.chernCap D sX hX E r hE g hY j k)

/-- **The cap operation `c(ℰ) ∩ -` of the total Chern class** `c(ℰ) = c_0(ℰ) + ⋯ + c_r(ℰ)`
(Stacks 0ERZ, `AlgebraicGeometry.Space.totalChernClass`) on `⨁_k CH_k(X')`, for a good test
space `g : X' ⟶ X`. -/
def totalChernCapGraded (r : ℕ) (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    AddMonoid.End (DirectSum ℤ fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) :=
  ∑ j : Fin (r + 1), chernCapGraded D sX hX E r hE g hY j

/-- On the summand `CH_k(X')`, `chernCapGraded` is `c_j(ℰ) ∩ - : CH_k(X') ⟶ CH_{k-j}(X')`. -/
theorem chernCapGraded_of (r : ℕ) (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (j : Fin (r + 1)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    chernCapGraded D sX hX E r hE g hY j
        (DirectSum.of (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) k α) =
      DirectSum.of (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (k - ((j : ℕ) : ℤ))
        (Space.chernCap D sX hX E r hE g hY j k α) :=
  DirectSum.toAddMonoid_of _ _ _

end Graded

/-! ### The comparison with Chow homology -/

section Comparison

variable (D : BaseSpaceDimensionSituation.{u})

/-- The identification of `⨁_k CH_k(X)` (the Chow groups of Stacks 0EQ6) with the Chow homology
`CH_*(X)`, summand by summand through `AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup`. -/
def chowGroupCanonicalGradedToChowHomology {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) :
    (DirectSum ℤ fun m => chowGroupCanonical.{u + 1} D sX hX m) →+
      chowHomology.{u, u + 1} D sX hX :=
  DirectSum.toAddMonoid fun k => chowGroupCanonicalToChowHomology D sX hX k

/-- The identification of `⨁_k CH_k(X)` with `CH_*(X)` is injective. -/
theorem injective_chowGroupCanonicalGradedToChowHomology {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) :
    Function.Injective (chowGroupCanonicalGradedToChowHomology D sX hX) := by
  let Ψ : chowHomology.{u, u + 1} D sX hX →+
      DirectSum ℤ fun m => chowGroupCanonical.{u + 1} D sX hX m :=
    DirectSum.toAddMonoid fun k =>
      (DirectSum.of (fun m => chowGroupCanonical.{u + 1} D sX hX m) k).comp
        (chowGroupCanonicalEquivChowGroup.{u + 1} D sX hX k).symm.toAddMonoidHom
  have hΨ : Ψ.comp (chowGroupCanonicalGradedToChowHomology D sX hX) = AddMonoidHom.id _ := by
    refine DirectSum.addHom_ext fun k a => ?_
    simp [Ψ, chowGroupCanonicalGradedToChowHomology, chowGroupCanonicalToChowHomology]
  intro x y hxy
  have h := congrArg Ψ hxy
  rwa [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply, hΨ] at h

/-- On the summand `CH_k(X)` the identification is `chowGroupCanonicalToChowHomology`. -/
theorem chowGroupCanonicalGradedToChowHomology_of {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) (α : chowGroupCanonical.{u + 1} D sX hX k) :
    chowGroupCanonicalGradedToChowHomology D sX hX
        (DirectSum.of (fun m => chowGroupCanonical.{u + 1} D sX hX m) k α) =
      chowGroupCanonicalToChowHomology D sX hX k α :=
  DirectSum.toAddMonoid_of _ _ _

variable {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)

/-- **`c_j(ℰ) ∩ -` on `⨁_k CH_k(X')` is the Chern class `c_j(g^*ℰ)` on `CH_*(X')`.** -/
theorem chowGroupCanonicalGradedToChowHomology_chernCapGraded (r : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hrY : PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY
      ((spaceModulePullback D hX.1 hY.1 g).obj E) r) (j : Fin (r + 1))
    (x : DirectSum ℤ fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) :
    chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY (chernCapGraded D sX hX E r hE g hY j x) =
      PrivateChern.chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 g).obj E) r
        hrY j (chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY x) := by
  refine DFunLike.congr_fun (DirectSum.addHom_ext (f :=
    (chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY).comp
      (chernCapGraded D sX hX E r hE g hY j))
    (g := (PrivateChern.chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 g).obj E)
      r hrY j).comp (chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY)) fun k α => ?_) x
  change chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY
      (chernCapGraded D sX hX E r hE g hY j (DirectSum.of _ k α)) =
    PrivateChern.chernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 g).obj E) r hrY j
      (chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY (DirectSum.of _ k α))
  rw [chernCapGraded_of, chowGroupCanonicalGradedToChowHomology_of,
    chowGroupCanonicalGradedToChowHomology_of, chowGroupCanonicalToChowHomology_chernCap]

/-- **`c(ℰ) ∩ -` on `⨁_k CH_k(X')` is the total Chern class `c(g^*ℰ)` on `CH_*(X')`.** -/
theorem chowGroupCanonicalGradedToChowHomology_totalChernCapGraded (r : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (hrY : PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY
      ((spaceModulePullback D hX.1 hY.1 g).obj E) r)
    (x : DirectSum ℤ fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) :
    chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY
        (totalChernCapGraded D sX hX E r hE g hY x) =
      PrivateChern.totalChernCap.{u, u + 1} (hX := hY) ((spaceModulePullback D hX.1 hY.1 g).obj E)
        r hrY (chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY x) := by
  rw [totalChernCapGraded, PrivateChern.end_finsetSum_apply, map_sum, PrivateChern.totalChernCap,
    PrivateChern.end_finsetSum_apply, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ =>
    chowGroupCanonicalGradedToChowHomology_chernCapGraded D sX hX E r hE g hY hrY j x

end Comparison

/-- A homomorphism intertwining two families of endomorphisms intertwines the products of their
lists. -/
theorem _root_.AddMonoidHom.map_list_ofFn_prod_apply_of_intertwines {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] (φ : M →+ N) : ∀ {r : ℕ} (a : Fin r → AddMonoid.End M)
    (b : Fin r → AddMonoid.End N), (∀ i x, φ (a i x) = b i (φ x)) →
      ∀ x, φ ((List.ofFn a).prod x) = (List.ofFn b).prod (φ x)
  | 0, _, _, _, x => rfl
  | r + 1, a, b, h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, AddMonoid.End.coe_mul,
      Function.comp_apply, h, AddMonoid.End.coe_mul, Function.comp_apply,
      AddMonoidHom.map_list_ofFn_prod_apply_of_intertwines φ (fun i => a i.succ)
        (fun i => b i.succ) (fun i => h i.succ)]

/-! ### Stacks 0ESA -/

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **Stacks 0ESA, the total Chern class of a module with a filtration with invertible
quotients.** In Situation 0EDT let `X/B` be good, let `ℒ_1, …, ℒ_r` be invertible `𝒪_X`-modules
and let `ℰ` be a finite locally free `𝒪_X`-module of rank `r` with a filtration
`0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ` such that `ℰ_i / ℰ_{i-1} ≅ ℒ_i` (a monotone family `F` of
subobjects of `ℰ` with `F 0 = ⊥`, `F r = ⊤` and identifications `e i` of the successive
quotients). With `x_i = c₁(ℒ_i)`, `c(ℰ) = ∏_{i=1}^r (1 + x_i)` in `A^*(X)`.

The classes are those of Stacks 0ERZ, `c_j(ℰ) ∈ A^j(X)` (`AlgebraicGeometry.Space.chernClass`)
and `c(ℰ) = ∑_j c_j(ℰ)` (`AlgebraicGeometry.Space.totalChernClass`), with `x_i = c₁(ℒ_i)` the
class `c_1` of the module `ℒ_i` of rank one. The product of `A^*(X)` is composition (Stacks
0ERK) and a bivariant class is determined by its cap operations on the good test spaces
`g : X' ⟶ X` (Stacks 0ERJ), the cap operation of `c_j(ℰ)` on `X'` being `c_j(ℰ) ∩ -` of
Stacks 0ERY (`AlgebraicGeometry.Space.chernClass_cap`). The identity is stated as that of the
cap operations on `⨁_k CH_k(X')` for every good `g : X' ⟶ X`: `c(ℰ) ∩ -` is
`totalChernCapGraded` and `c₁(ℒ_i) ∩ -` is `chernCapGraded` at `j = 1`. -/
@[stacks 0ESA "c(E) = ∏ (1 + c_1(L_i)) in A^*(X) for the Chern classes of Definition 0ERZ \
(chernClass, totalChernClass), as the identity of their cap operations c(E) ∩ - and \
∏ (1 + c_1(L_i) ∩ -) of Lemma 0ERY on ⊕_k CH_k(X') for every good test space X' → X"]
theorem totalChernCapGraded_eq_prod_one_add_chernCapGraded {r : ℕ}
    (L : Fin r → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : ∀ i, IsInvertibleModule (goodSpace hX) (L i))
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX E r)
    (F : Fin (r + 1) → Subobject E) (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r, cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    totalChernCapGraded D sX hX E r hE g hY = (List.ofFn fun i => 1 +
      chernCapGraded D sX hX (L i) 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) (hL i)) g hY
          1).prod := by
  let a : (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩ :=
    ObjectProperty.homMk g
  obtain ⟨F', hF', h0', hr', e'⟩ := exists_filtration_modulePullback D.site D.base D.base_mem a L
    hL F hF h0 hr e
  have hL' : ∀ i, IsInvertibleModule (goodSpace hY)
      ((spaceModulePullback D hX.1 hY.1 g).obj (L i)) := fun i =>
    modulePullbackInvertible a (L i) (hL i)
  have hrY : PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY
      ((spaceModulePullback D hX.1 hY.1 g).obj E) r :=
    PrivateChern.isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem a hE
  have hY0 := PrivateChern.totalChernCap_eq_prod_one_add_chernCap_one (hX := hY)
    (fun i => (spaceModulePullback D hX.1 hY.1 g).obj (L i)) hL'
    ((spaceModulePullback D hX.1 hY.1 g).obj E) hrY F' hF' h0' hr' (fun i => (e' i).some)
  have hint : ∀ (i : Fin r) (y : DirectSum ℤ fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m),
      chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY ((1 + chernCapGraded D sX hX (L i) 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) (hL i)) g hY 1) y) =
      (1 + PrivateChern.chernCap.{u, u + 1} ((spaceModulePullback D hX.1 hY.1 g).obj (L i)) 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hY) (hL' i)) 1)
        (chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY y) := fun i y => by
    change chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY (y + chernCapGraded D sX hX (L i) 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) (hL i)) g hY 1 y) =
      chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY y +
        PrivateChern.chernCap.{u, u + 1} ((spaceModulePullback D hX.1 hY.1 g).obj (L i)) 1
          (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hY) (hL' i)) 1
          (chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY y)
    rw [map_add, chowGroupCanonicalGradedToChowHomology_chernCapGraded D sX hX (L i) 1 _ g hY
      (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hY) (hL' i)), Fin.val_one]
  refine AddMonoidHom.ext fun x => injective_chowGroupCanonicalGradedToChowHomology D (g ≫ sX)
    hY ?_
  have h1 := chowGroupCanonicalGradedToChowHomology_totalChernCapGraded D sX hX E r hE g hY hrY x
  have h2 := AddMonoidHom.map_list_ofFn_prod_apply_of_intertwines
    (chowGroupCanonicalGradedToChowHomology D (g ≫ sX) hY) _ _ hint x
  rw [hY0] at h1
  exact h1.trans h2.symm

end AlgebraicGeometry.Space

end
