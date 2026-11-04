module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapPow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupMapOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackSquareCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinFirstChernCap

/-!
# The relation of Stacks 0ERY under proper pushforward, flat pullback and Gysin maps

Let `π : P → Y` be a flat morphism of good algebraic spaces over the base, of relative dimension
`n`, and let `ℒ` be an invertible `𝒪_P`-module. For a family `b_j ∈ CH_{k-j}(Y)`, `j = 0, …, r`,
the left-hand side of the relation of Stacks 0ERY is

`∑_{i = 0}^{r} (-1)^i c₁(ℒ)^i ∩ π^*(b_{r - i}) ∈ CH_{k - r + n}(P)`

(`AlgebraicGeometry.Space.bundleRelationSumAt`). This expression is carried to the corresponding
one by the three operations a bivariant class commutes with, and is invariant under an isomorphism
of bundles:

* proper pushforward along the base change `P₂ → P₁` of a proper `h : Y₂ → Y₁`, by Stacks 0EQT
  (iterated) and Stacks 0EPD;
* flat pullback along a flat `P₂ → P₁` over a flat `h : Y₂ → Y₁`, by Stacks 0EQR (iterated) and
  Stacks 0EPA;
* the Gysin map of a section of an invertible sheaf on `Y` and of its pullback to `P`, by
  Stacks 0ERB (iterated) and Stacks 0ER6.

## Main definitions

* `AlgebraicGeometry.Space.bundleRelationPull`: the flat pullback `π^* : CH_m(Y) → CH_N(P)`,
  `m + e = N`, for any spelling `e` of the relative dimension.
* `AlgebraicGeometry.Space.bundleRelationSumAt`: the left-hand side of the relation.

## Main results

* `AlgebraicGeometry.Space.chowClassCanonical_properCyclePushforward_firstChernCapPowCycleMap`:
  `q_*(c₁(q^*ℒ)^s ∩ α) = c₁(ℒ)^s ∩ q_*α` (Stacks 0EQT, iterated).
* `AlgebraicGeometry.Space.chowClassCanonical_gysinCycleMap_firstChernCapPowCycleMap`:
  `i^*(c₁(𝒩)^s ∩ α) = c₁(i^*𝒩)^s ∩ i^*α` (Stacks 0ERB, iterated).
* `AlgebraicGeometry.Space.properPushforward_bundleRelationSumAt`,
  `AlgebraicGeometry.Space.flatPullback_bundleRelationSumAt`,
  `AlgebraicGeometry.Space.gysin_bundleRelationSumAt`,
  `AlgebraicGeometry.Space.bundleRelationSumAt_of_isIso`: the four compatibilities.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0ERB](https://stacks.math.columbia.edu/tag/0ERB)
* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Powers of the cap product against proper pushforward and Gysin maps -/

section ProperPower

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (q : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)
    (hqB : q.hom ≫ sY = sX) (hq : IsProper D.site D.base D.base_mem q.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **Stacks 0EQT for the `s`-fold cap product**: `q_*(c₁(q^*ℒ)^s ∩ α) = c₁(ℒ)^s ∩ q_*α` in
`CH_m(Y)` for `α ∈ Z_{m+s}(X)` and `q` proper. -/
theorem chowClassCanonical_properCyclePushforward_firstChernCapPowCycleMap (s : ℕ) :
    ∀ (m : ℤ) (α : CycleGroup D sX (m + s)),
      chowClassCanonical.{u + 1} D sY hY m
          (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 m
            (firstChernCapPowCycleMap D sX hX ((modulePullback D.site D.base D.base_mem q).obj L)
              (modulePullbackInvertible q L hL) s m α)) =
        chowClassCanonical.{u + 1} D sY hY m
          (firstChernCapPowCycleMap D sY hY L hL s m
            (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 (m + s) α)) := by
  induction s with
  | zero =>
    intro m α
    congr 1
  | succ s ih =>
    intro m α
    simp only [firstChernCapPowCycleMap, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [chowClassCanonical_properPushforward_canonicalFirstChernCap_of_component D hX hY q hqB hq
      L hL m (fun β hβ => isRationallyEquivalentToZeroCanonical_properCyclePushforward D sX hX sY
        hY hqB hq m β hβ)]
    show canonicalFirstChernCapCanonical.{u + 1} D sY hY L hL m _ =
      canonicalFirstChernCapCanonical.{u + 1} D sY hY L hL m _
    rw [← canonicalFirstChernCapCanonicalChowMap_chowClassCanonical,
      ← canonicalFirstChernCapCanonicalChowMap_chowClassCanonical, ih (m + 1)]
    congr 2

end ProperPower

section GysinPower

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleSheaf D sX hX L) (s : L.sections)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- The Gysin map of cycles only depends on the underlying cycle and the degree. -/
theorem coe_gysinCycleMap_sectionGysinRule_congr {m m' : ℤ} (hm : m = m')
    (α : CycleGroup D sX (m + 1)) (α' : CycleGroup D sX (m' + 1)) (hα : α.1 = α'.1) :
    (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) m
        (sectionGysinRule D sX hX L s m hL) α).1 =
      (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) m'
        (sectionGysinRule D sX hX L s m' hL) α').1 := by
  subst hm
  rw [Subtype.ext hα]

/-- **Stacks 0ERB for the `s`-fold cap product**: `i^*(c₁(𝒩)^t ∩ α) = c₁(i^*𝒩)^t ∩ i^*α` in
`CH_m(E)`, `E = Z(s)`, for `α ∈ Z_{m+1+t}(X)`. -/
theorem chowClassCanonical_gysinCycleMap_firstChernCapPowCycleMap (t : ℕ) :
    ∀ (m : ℤ) (α : CycleGroup D sX (m + 1 + t)),
      chowClassCanonical.{u + 1} D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) m
          (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) m
            (sectionGysinRule D sX hX L s m hL)
            (firstChernCapPowCycleMap D sX hX N hN t (m + 1) α)) =
        chowClassCanonical.{u + 1} D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) m
          (firstChernCapPowCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
            (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) t m
            (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
              (m + t) (sectionGysinRule D sX hX L s (m + t) hL)
              (cycleGroupCast D sX (by ring) α))) := by
  induction t with
  | zero =>
    intro m α
    congr 1
    refine Subtype.ext ?_
    exact coe_gysinCycleMap_sectionGysinRule_congr D sX hX L hL s (by simp) _ _ rfl
  | succ t ih =>
    intro m α
    simp only [firstChernCapPowCycleMap, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [chowClassCanonical_gysinCycleMap_firstChernCapCycleMap.{u, u + 1} D sX hX L hL s N hN m]
    show canonicalFirstChernCapCanonical.{u + 1} D _ _ _ _ m _ =
      canonicalFirstChernCapCanonical.{u + 1} D _ _ _ _ m _
    rw [← canonicalFirstChernCapCanonicalChowMap_chowClassCanonical,
      ← canonicalFirstChernCapCanonicalChowMap_chowClassCanonical, ih (m + 1)]
    congr 2
    refine Subtype.ext (coe_firstChernCapPowCycleMap_congr D _ _ _ _ rfl rfl _ _ ?_)
    rw [cycleGroupCast_coe]
    exact coe_gysinCycleMap_sectionGysinRule_congr D sX hX L hL s (by push_cast; ring) _ _ rfl

end GysinPower

/-! ### The left-hand side of the relation for a bundle datum -/

section Relation

variable (D : BaseSpaceDimensionSituation.{u})
    {Y P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ Y) (hπB : π ≫ sY = sP) (n : ℕ) (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- The flat pullback `π^* : CH_m(Y) → CH_N(P)`, `m + e = N`, for any spelling `e` of the
relative dimension `n` of `π`. -/
def bundleRelationPull (e : ℤ) (he : (n : ℤ) = e) (m N : ℤ) (h : m + e = N) :
    chowGroupCanonical.{u + 1} D sY hY m →+ chowGroupCanonical.{u + 1} D sP hP N :=
  bundleFormulaPull D sY hY sP hP π hπB n hflat hrel m N (by rw [he]; exact h)

/-- **The left-hand side of the relation of Stacks 0ERY** for the datum `(π, ℒ)` and a family
`b_j ∈ CH_{k-j}(Y)`, `j = 0, …, r`: `∑_{i=0}^{r} (-1)^i c₁(ℒ)^i ∩ π^*(b_{r-i}) ∈ CH_{k-r+e}(P)`. -/
abbrev bundleRelationSumAt (e : ℤ) (he : (n : ℤ) = e) (r : ℕ) (k : ℤ)
    (b : ∀ j : Fin (r + 1), chowGroupCanonical.{u + 1} D sY hY (k - ((j : ℕ) : ℤ))) :
    chowGroupCanonical.{u + 1} D sP hP (k - r + e) :=
  ProjectiveBundleRelation.relationSumAt (A := fun m => chowGroupCanonical.{u + 1} D sY hY m)
    (P := fun m => chowGroupCanonical.{u + 1} D sP hP m) e
    (bundleRelationPull D sY hY sP hP π hπB n hflat hrel e he) (bundleFormulaCap D sP hP L hL) r k
    b

/-- The flat pullback of a class, in the shape of `AlgebraicGeometry.Space.bundleRelationPull`. -/
theorem bundleRelationPull_chowClassCanonical (e : ℤ) (he : (n : ℤ) = e) (m N : ℤ)
    (h : m + e = N) (ξ : CycleGroup D sY m) :
    bundleRelationPull D sY hY sP hP π hπB n hflat hrel e he m N h
        (chowClassCanonical.{u + 1} D sY hY m ξ) =
      chowClassCanonical.{u + 1} D sP hP N
        (flatPullbackMap D sP hP sY hY π hπB n hflat hrel m N (by rw [he]; exact h) ξ) :=
  rfl

/-- The cap power of a class, in the shape of `AlgebraicGeometry.Space.bundleFormulaCap`. -/
theorem bundleFormulaCap_chowClassCanonical (s : ℕ) (M N : ℤ) (h : M = N + s)
    (ξ : CycleGroup D sP M) :
    bundleFormulaCap D sP hP L hL s M N h (chowClassCanonical.{u + 1} D sP hP M ξ) =
      chowClassCanonical.{u + 1} D sP hP N
        (firstChernCapPowCycleMap D sP hP L hL s N (cycleGroupCast D sP h ξ)) :=
  rfl

end Relation

/-! ### Proper pushforward -/

section Proper

variable (D : BaseSpaceDimensionSituation.{u})
    {Y₁ Y₂ P₁ P₂ : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sY₁ : Y₁ ⟶ D.space) (hY₁ : D.IsGood sY₁) (sY₂ : Y₂ ⟶ D.space) (hY₂ : D.IsGood sY₂)
    (sP₁ : P₁ ⟶ D.space) (hP₁ : D.IsGood sP₁) (sP₂ : P₂ ⟶ D.space) (hP₂ : D.IsGood sP₂)
    (π₁ : P₁ ⟶ Y₁) (hπ₁ : π₁ ≫ sY₁ = sP₁) (π₂ : P₂ ⟶ Y₂) (hπ₂ : π₂ ≫ sY₂ = sP₂) (n : ℕ)
    (hflat₁ : IsFlat D.site D.base D.base_mem π₁)
    (hrel₁ : HasRelativeDimension n D.site D.base D.base_mem π₁)
    (hflat₂ : IsFlat D.site D.base D.base_mem π₂)
    (hrel₂ : HasRelativeDimension n D.site D.base D.base_mem π₂)
    (L₁ : Modules.{u, u} D.site D.base D.base_mem P₁ hP₁.1)
    (hL₁ : IsInvertibleModule (⟨P₁, hP₁.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L₁)
    (L₂ : Modules.{u, u} D.site D.base D.base_mem P₂ hP₂.1)
    (hL₂ : IsInvertibleModule (⟨P₂, hP₂.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L₂)
    (h : Y₂ ⟶ Y₁) (hhB : h ≫ sY₁ = sY₂) (hh : IsProper D.site D.base D.base_mem h)
    (hP : P₂ ⟶ P₁) (hPB : hP ≫ sP₁ = sP₂) (hPp : IsProper D.site D.base D.base_mem hP)
    (sq : IsPullback π₂ hP h π₁)
    (eL : (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk hP : (⟨P₂, hP₂.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨P₁, hP₁.1⟩)).obj L₁ ≅ L₂)

include sq eL in
/-- **A summand of the relation under proper pushforward**: for the base change `h_P : P₂ → P₁`
of a proper `h : Y₂ → Y₁`, `h_{P*}(c₁(ℒ₂)^s ∩ π₂^*x) = c₁(ℒ₁)^s ∩ π₁^*(h_*x)` when
`h_P^*ℒ₁ ≅ ℒ₂`; Stacks 0EQT (iterated) and Stacks 0EPD. -/
theorem properPushforward_bundleFormulaCap_bundleRelationPull (e : ℤ) (he : (n : ℤ) = e)
    (s : ℕ) (a M N : ℤ) (hMN : M = N + s) (haM : a + e = M)
    (x : chowGroupCanonical.{u + 1} D sY₂ hY₂ a) :
    chowGroupCanonicalProperPushforward.{u + 1} D sP₂ hP₂ sP₁ hP₁ hPB hPp N
        (bundleFormulaCap D sP₂ hP₂ L₂ hL₂ s M N hMN
          (bundleRelationPull D sY₂ hY₂ sP₂ hP₂ π₂ hπ₂ n hflat₂ hrel₂ e he a M haM x)) =
      bundleFormulaCap D sP₁ hP₁ L₁ hL₁ s M N hMN
        (bundleRelationPull D sY₁ hY₁ sP₁ hP₁ π₁ hπ₁ n hflat₁ hrel₁ e he a M haM
          (chowGroupCanonicalProperPushforward.{u + 1} D sY₂ hY₂ sY₁ hY₁ hhB hh a x)) := by
  subst hMN he
  obtain ⟨ξ, rfl⟩ : ∃ ξ, chowClassCanonical.{u + 1} D sY₂ hY₂ a ξ = x :=
    QuotientAddGroup.mk'_surjective _ x
  have hiso := chowClassCanonical_firstChernCapPowCycleMap_congr_iso D sP₂ hP₂ _ L₂
    (modulePullbackInvertible
      (ObjectProperty.homMk hP : (⟨P₂, hP₂.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨P₁, hP₁.1⟩) L₁ hL₁) hL₂ eL
  rw [bundleRelationPull_chowClassCanonical, bundleFormulaCap_chowClassCanonical, ← hiso,
    chowGroupCanonicalProperPushforward_chowClassCanonical,
    chowClassCanonical_properCyclePushforward_firstChernCapPowCycleMap D sP₂ hP₂ sP₁ hP₁
      (ObjectProperty.homMk hP : (⟨P₂, hP₂.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨P₁, hP₁.1⟩) hPB hPp L₁ hL₁ s N,
    chowGroupCanonicalProperPushforward_chowClassCanonical, bundleRelationPull_chowClassCanonical,
    bundleFormulaCap_chowClassCanonical]
  have h0EPD := flatPullback_properPushforward_unconditional D sP₂ hP₂ sY₂ hY₂ sP₁ hP₁ sY₁ hY₁
    hπ₂ hPB hhB hπ₁ n hflat₁ hrel₁ sq hh a (N + s) haM ξ
  have hcyc : properCyclePushforward D sP₂ hP₂ sP₁ hP₁ hPB hPp.2.1.2 (N + s)
        (cycleGroupCast D sP₂ rfl
          (flatPullbackMap D sP₂ hP₂ sY₂ hY₂ π₂ hπ₂ n hflat₂ hrel₂ a (N + s) haM ξ)) =
      cycleGroupCast D sP₁ rfl
        (flatPullbackMap D sP₁ hP₁ sY₁ hY₁ π₁ hπ₁ n hflat₁ hrel₁ a (N + s) haM
          (properCyclePushforward D sY₂ hY₂ sY₁ hY₁ hhB hh.2.1.2 a ξ)) := by
    refine Subtype.ext ?_
    rw [cycleGroupCast_coe, h0EPD]
    exact coe_properCyclePushforward_congr D sP₁ hP₁ sP₂ hP₂ hP hPB _ rfl _ _ rfl
  rw [hcyc]

include sq eL in
/-- **The relation of Stacks 0ERY under proper pushforward**: for the base change
`h_P : P₂ → P₁` of a proper `h : Y₂ → Y₁` with `h_P^*ℒ₁ ≅ ℒ₂`,
`h_{P*}(∑ (-1)^i c₁(ℒ₂)^i ∩ π₂^* b_{r-i}) = ∑ (-1)^i c₁(ℒ₁)^i ∩ π₁^*(h_* b_{r-i})`. -/
theorem properPushforward_bundleRelationSumAt (e : ℤ) (he : (n : ℤ) = e) (r : ℕ) (k : ℤ)
    (b : ∀ j : Fin (r + 1), chowGroupCanonical.{u + 1} D sY₂ hY₂ (k - ((j : ℕ) : ℤ))) :
    chowGroupCanonicalProperPushforward.{u + 1} D sP₂ hP₂ sP₁ hP₁ hPB hPp (k - r + e)
        (bundleRelationSumAt D sY₂ hY₂ sP₂ hP₂ π₂ hπ₂ n hflat₂ hrel₂ L₂ hL₂ e he r k b) =
      bundleRelationSumAt D sY₁ hY₁ sP₁ hP₁ π₁ hπ₁ n hflat₁ hrel₁ L₁ hL₁ e he r k
        (fun j => chowGroupCanonicalProperPushforward.{u + 1} D sY₂ hY₂ sY₁ hY₁ hhB hh _
          (b j)) := by
  simp only [bundleRelationSumAt, ProjectiveBundleRelation.relationSumAt,
    ProjectiveBundleRelation.relationTerm, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [properPushforward_bundleFormulaCap_bundleRelationPull D sY₁ hY₁ sY₂ hY₂ sP₁ hP₁ sP₂ hP₂ π₁
    hπ₁ π₂ hπ₂ n hflat₁ hrel₁ hflat₂ hrel₂ L₁ hL₁ L₂ hL₂ h hhB hh hP hPB hPp sq eL]

end Proper

/-! ### Flat pullback -/

section Flat

variable (D : BaseSpaceDimensionSituation.{u})
    {Y₁ Y₂ P₁ P₂ : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sY₁ : Y₁ ⟶ D.space) (hY₁ : D.IsGood sY₁) (sY₂ : Y₂ ⟶ D.space) (hY₂ : D.IsGood sY₂)
    (sP₁ : P₁ ⟶ D.space) (hP₁ : D.IsGood sP₁) (sP₂ : P₂ ⟶ D.space) (hP₂ : D.IsGood sP₂)
    (π₁ : P₁ ⟶ Y₁) (hπ₁ : π₁ ≫ sY₁ = sP₁) (π₂ : P₂ ⟶ Y₂) (hπ₂ : π₂ ≫ sY₂ = sP₂) (n : ℕ)
    (hflat₁ : IsFlat D.site D.base D.base_mem π₁)
    (hrel₁ : HasRelativeDimension n D.site D.base D.base_mem π₁)
    (hflat₂ : IsFlat D.site D.base D.base_mem π₂)
    (hrel₂ : HasRelativeDimension n D.site D.base D.base_mem π₂)
    (L₁ : Modules.{u, u} D.site D.base D.base_mem P₁ hP₁.1)
    (hL₁ : IsInvertibleModule (⟨P₁, hP₁.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L₁)
    (L₂ : Modules.{u, u} D.site D.base D.base_mem P₂ hP₂.1)
    (hL₂ : IsInvertibleModule (⟨P₂, hP₂.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L₂)
    (h : Y₂ ⟶ Y₁) (hhB : h ≫ sY₁ = sY₂) (m : ℕ) (hhf : IsFlat D.site D.base D.base_mem h)
    (hhr : HasRelativeDimension m D.site D.base D.base_mem h)
    (hP : P₂ ⟶ P₁) (hPB : hP ≫ sP₁ = sP₂) (hPf : IsFlat D.site D.base D.base_mem hP)
    (hPr : HasRelativeDimension m D.site D.base D.base_mem hP)
    (w : hP ≫ π₁ = π₂ ≫ h)
    (eL : (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk hP : (⟨P₂, hP₂.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨P₁, hP₁.1⟩)).obj L₁ ≅ L₂)

include w in
/-- `h_P^* π₁^* = π₂^* h^*` on cycles, both being the flat pullback along the common composite
(Stacks 0EPA). -/
theorem flatPullbackMap_flatPullbackMap_of_comm (a a' M M' : ℤ) (ha : a + (m : ℤ) = a')
    (hM : M + (m : ℤ) = M') (haM : a + (n : ℤ) = M) (haM' : a' + (n : ℤ) = M')
    (ξ : CycleGroup D sY₁ a) :
    flatPullbackMap D sP₂ hP₂ sP₁ hP₁ hP hPB m hPf hPr M M' hM
        (flatPullbackMap D sP₁ hP₁ sY₁ hY₁ π₁ hπ₁ n hflat₁ hrel₁ a M haM ξ) =
      flatPullbackMap D sP₂ hP₂ sY₂ hY₂ π₂ hπ₂ n hflat₂ hrel₂ a' M' haM'
        (flatPullbackMap D sY₂ hY₂ sY₁ hY₁ h hhB m hhf hhr a a' ha ξ) := by
  subst ha hM haM
  have h1 := congrArg (fun ψ => (ψ ξ).1)
    (flatPullbackMap_comp D sP₂ hP₂ sP₁ hP₁ sY₁ hY₁ hP π₁ hPB hπ₁ m n hPf hPr hflat₁ hrel₁ a
      (a + n + m) (by push_cast; omega))
  have h2 := congrArg (fun ψ => (ψ ξ).1)
    (flatPullbackMap_comp D sP₂ hP₂ sY₂ hY₂ sY₁ hY₁ π₂ h hπ₂ hhB n m hflat₂ hrel₂ hhf hhr a
      (a + n + m) (by push_cast; omega))
  exact Subtype.ext (h1.symm.trans ((flatPullbackMap_coe_congr D sP₂ hP₂ sY₁ hY₁ w _ _
    (Nat.add_comm m n) _ _ _ _ a (a + n + m) a (a + n + m) _ _ ξ ξ rfl).trans h2))

include w eL in
/-- **A summand of the relation under flat pullback**: for `h_P : P₂ → P₁` over a flat
`h : Y₂ → Y₁`, both flat of relative dimension `m`, with `h_P^*ℒ₁ ≅ ℒ₂`,
`h_P^*(c₁(ℒ₁)^s ∩ π₁^*x) = c₁(ℒ₂)^s ∩ π₂^*(h^*x)`; Stacks 0EQR (iterated) and Stacks 0EPA. -/
theorem flatPullback_bundleFormulaCap_bundleRelationPull (e : ℤ) (he : (n : ℤ) = e)
    (s : ℕ) (a a' M M' N N' : ℤ) (ha : a + (m : ℤ) = a') (hN : N + (m : ℤ) = N')
    (hMN : M = N + s) (hMN' : M' = N' + s) (haM : a + e = M) (haM' : a' + e = M')
    (x : chowGroupCanonical.{u + 1} D sY₁ hY₁ a) :
    flatPullbackChowMapCanonical.{u + 1} D sP₂ hP₂ sP₁ hP₁ hP hPB m hPf hPr N N' hN
        (bundleFormulaCap D sP₁ hP₁ L₁ hL₁ s M N hMN
          (bundleRelationPull D sY₁ hY₁ sP₁ hP₁ π₁ hπ₁ n hflat₁ hrel₁ e he a M haM x)) =
      bundleFormulaCap D sP₂ hP₂ L₂ hL₂ s M' N' hMN'
        (bundleRelationPull D sY₂ hY₂ sP₂ hP₂ π₂ hπ₂ n hflat₂ hrel₂ e he a' M' haM'
          (flatPullbackChowMapCanonical.{u + 1} D sY₂ hY₂ sY₁ hY₁ h hhB m hhf hhr a a' ha x)) := by
  subst hMN hMN' he hN
  obtain ⟨ξ, rfl⟩ : ∃ ξ, chowClassCanonical.{u + 1} D sY₁ hY₁ a ξ = x :=
    QuotientAddGroup.mk'_surjective _ x
  rw [bundleRelationPull_chowClassCanonical, bundleFormulaCap_chowClassCanonical,
    flatPullbackChowMapCanonical_chowClassCanonical,
    chowClassCanonical_flatPullbackMap_firstChernCapPowCycleMap_modulePullback
        D sP₂ hP₂ sP₁ hP₁ hP hPB m hPf
      hPr L₁ hL₁ s N (N + m) rfl (by ring),
    chowClassCanonical_firstChernCapPowCycleMap_congr_iso D sP₂ hP₂ _ L₂
      (modulePullbackInvertible
        (ObjectProperty.homMk hP : (⟨P₂, hP₂.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
          ⟨P₁, hP₁.1⟩) L₁ hL₁) hL₂ eL,
    flatPullbackChowMapCanonical_chowClassCanonical, bundleRelationPull_chowClassCanonical,
    bundleFormulaCap_chowClassCanonical]
  have hcyc : flatPullbackMap D sP₂ hP₂ sP₁ hP₁ hP hPB m hPf hPr (N + s) (N + m + s)
        (by ring)
        (cycleGroupCast D sP₁ rfl
          (flatPullbackMap D sP₁ hP₁ sY₁ hY₁ π₁ hπ₁ n hflat₁ hrel₁ a (N + s) haM ξ)) =
      cycleGroupCast D sP₂ rfl
        (flatPullbackMap D sP₂ hP₂ sY₂ hY₂ π₂ hπ₂ n hflat₂ hrel₂ a' (N + m + s) haM'
          (flatPullbackMap D sY₂ hY₂ sY₁ hY₁ h hhB m hhf hhr a a' ha ξ)) := by
    refine Subtype.ext ?_
    rw [cycleGroupCast_coe, ← flatPullbackMap_flatPullbackMap_of_comm D sY₁ hY₁ sY₂ hY₂ sP₁ hP₁
      sP₂ hP₂ π₁ hπ₁ π₂ hπ₂ n hflat₁ hrel₁ hflat₂ hrel₂ h hhB m hhf hhr hP hPB hPf hPr w a a'
      (N + s) (N + m + s) ha (by ring) haM haM' ξ]
    exact coe_flatPullbackMap_congr D sP₁ hP₁ sP₂ hP₂ hP hPB m hPf hPr rfl rfl _ _ _ _ rfl
  rw [hcyc]

include w eL in
/-- **The relation of Stacks 0ERY under flat pullback**: for `h_P : P₂ → P₁` over a flat
`h : Y₂ → Y₁`, both flat of relative dimension `m`, with `h_P^*ℒ₁ ≅ ℒ₂`,
`h_P^*(∑ (-1)^i c₁(ℒ₁)^i ∩ π₁^* b_{r-i}) = ∑ (-1)^i c₁(ℒ₂)^i ∩ π₂^*(h^* b_{r-i})`. -/
theorem flatPullback_bundleRelationSumAt (e : ℤ) (he : (n : ℤ) = e) (r : ℕ) (k : ℤ)
    (b : ∀ j : Fin (r + 1), chowGroupCanonical.{u + 1} D sY₁ hY₁ (k - ((j : ℕ) : ℤ))) :
    flatPullbackChowMapCanonical.{u + 1} D sP₂ hP₂ sP₁ hP₁ hP hPB m hPf hPr (k - r + e)
        (k + m - r + e) (by ring)
        (bundleRelationSumAt D sY₁ hY₁ sP₁ hP₁ π₁ hπ₁ n hflat₁ hrel₁ L₁ hL₁ e he r k b) =
      bundleRelationSumAt D sY₂ hY₂ sP₂ hP₂ π₂ hπ₂ n hflat₂ hrel₂ L₂ hL₂ e he r (k + m)
        (fun j => flatPullbackChowMapCanonical.{u + 1} D sY₂ hY₂ sY₁ hY₁ h hhB m hhf hhr _ _
          (by ring) (b j)) := by
  simp only [bundleRelationSumAt, ProjectiveBundleRelation.relationSumAt,
    ProjectiveBundleRelation.relationTerm, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [flatPullback_bundleFormulaCap_bundleRelationPull D sY₁ hY₁ sY₂ hY₂ sP₁ hP₁ sP₂ hP₂ π₁
    hπ₁ π₂ hπ₂ n hflat₁ hrel₁ hflat₂ hrel₂ L₁ hL₁ L₂ hL₂ h hhB m hhf hhr hP hPB hPf hPr w eL e he
    i _ (k + m - ((Fin.rev i : ℕ) : ℤ)) _ (k + m - r + e + (i : ℕ)) _ (k + m - r + e) (by ring)
    (by ring) rfl rfl _ (ProjectiveBundleRelation.relationTerm_degree e r (k + m) i)]

end Flat

/-! ### The Gysin map of a section -/

section Gysin

variable (D : BaseSpaceDimensionSituation.{u})
    {Y P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ Y) (hπB : π ≫ sY = sP) (n : ℕ) (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (t : M.sections)
    (hM : IsInvertibleSheaf D sY hY M)
    {g₀ : (vanishingLocus D sP hP (pullbackSheaf D sY hY sP hP (ObjectProperty.homMk π) M)
        (pullbackGlobalSection D sY hY sP hP (ObjectProperty.homMk π) M t)).1.toFunctor ⟶
      (vanishingLocus D sY hY M t).1.toFunctor}
    (hsq : IsPullback g₀ (vanishingLocus D sP hP (pullbackSheaf D sY hY sP hP
        (ObjectProperty.homMk π) M)
        (pullbackGlobalSection D sY hY sP hP (ObjectProperty.homMk π) M t)).1.ι
      (vanishingLocus D sY hY M t).1.ι π)

local notation "ℤ'" => vanishingLocus D sP hP (pullbackSheaf D sY hY sP hP
  (ObjectProperty.homMk π) M) (pullbackGlobalSection D sY hY sP hP (ObjectProperty.homMk π) M t)
local notation "hℤ'" => isGood_vanishingLocus D sP hP (pullbackSheaf D sY hY sP hP
  (ObjectProperty.homMk π) M) (pullbackGlobalSection D sY hY sP hP (ObjectProperty.homMk π) M t)
local notation "hM'" => isInvertibleSheaf_pullbackSheaf D sY hY sP hP (ObjectProperty.homMk π) M hM
local notation "Lℤ" => Functor.obj (modulePullback D.site D.base D.base_mem
  (vanishingLocusInclusion D sP hP (pullbackSheaf D sY hY sP hP (ObjectProperty.homMk π) M)
  (pullbackGlobalSection D sY hY sP hP (ObjectProperty.homMk π) M t))) L
local notation "hLℤ" => modulePullbackInvertible (vanishingLocusInclusion D sP hP
  (pullbackSheaf D sY hY sP hP (ObjectProperty.homMk π) M)
  (pullbackGlobalSection D sY hY sP hP (ObjectProperty.homMk π) M t)) L hL
local notation "hgfr" => isFlat_and_hasRelativeDimension_gysinPullbackProjection D sY hY sP hP
  hπB n hflat hrel M t hsq
local notation "hgbase" => comp_structure_of_isPullback D sY sP hπB hsq

include hM hsq in
/-- **A summand of the relation under the Gysin map**: for `(ℳ, t)` on `Y` with `D' = Z(t)` and
`Z = Z(π^*t) = P ×_Y D'`, `i_Z^*(c₁(ℒ)^s ∩ π^*x) = c₁(ℒ|_Z)^s ∩ g₀^*(i^*x)`; Stacks 0ERB
(iterated) and Stacks 0ER6. -/
theorem gysin_bundleFormulaCap_bundleRelationPull (e : ℤ) (he : (n : ℤ) = e) (s : ℕ)
    (a a₀ M₁ M₀ N N₁ : ℤ) (hN₁ : N₁ = N + 1) (ha : a = a₀ + 1) (hMN : M₁ = N₁ + s)
    (hM₀ : M₀ = N + s) (haM : a + e = M₁) (haM₀ : a₀ + e = M₀)
    (x : chowGroupCanonical.{u + 1} D sY hY a) :
    sectionGysinChowGroupMap D sP hP _ _ hM' N
        (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sP hP m) hN₁
          (bundleFormulaCap D sP hP L hL s M₁ N₁ hMN
            (bundleRelationPull D sY hY sP hP π hπB n hflat hrel e he a M₁ haM x))) =
      bundleFormulaCap D ((ℤ').1.ι ≫ sP) hℤ' Lℤ hLℤ s M₀ N hM₀
        (bundleRelationPull D ((vanishingLocus D sY hY M t).1.ι ≫ sY)
          (isGood_vanishingLocus D sY hY M t) ((ℤ').1.ι ≫ sP) hℤ' g₀ hgbase n (hgfr).1 (hgfr).2
          e he a₀ M₀ haM₀
          (sectionGysinChowGroupMap D sY hY M t hM a₀
            (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sY hY m)
              ha x))) := by
  subst hN₁ ha hMN hM₀ he
  obtain ⟨ξ, rfl⟩ : ∃ ξ, chowClassCanonical.{u + 1} D sY hY (a₀ + 1) ξ = x :=
    QuotientAddGroup.mk'_surjective _ x
  rw [ProjectiveBundleRelation.degreeCast_rfl, ProjectiveBundleRelation.degreeCast_rfl,
    bundleRelationPull_chowClassCanonical, bundleFormulaCap_chowClassCanonical,
    sectionGysinChowGroupMap_chowClassCanonical,
    chowClassCanonical_gysinCycleMap_firstChernCapPowCycleMap D sP hP _ hM' _ L hL s N,
    sectionGysinChowGroupMap_chowClassCanonical, bundleRelationPull_chowClassCanonical,
    bundleFormulaCap_chowClassCanonical, ← firstChernCapPowChowMap_chowClassCanonical,
    ← firstChernCapPowChowMap_chowClassCanonical]
  congr 1
  have hk1 : a₀ + 1 + (n : ℤ) = N + s + 1 := by omega
  have h6 := chowClassCanonical_gysinCycleMap_flatPullbackMap_of_isPullback D sY hY sP hP hπB n
    hflat hrel M t hM hsq a₀ (N + s) haM₀ hk1 ξ
  have hcyc : gysinCycleMap D sP (ℤ') hℤ' (N + s) (sectionGysinRule D sP hP _ _ (N + s) hM')
        (cycleGroupCast D sP (by ring) (cycleGroupCast D sP rfl
          (flatPullbackMap D sP hP sY hY π hπB n hflat hrel (a₀ + 1) (N + 1 + s) haM ξ))) =
      gysinCycleMap D sP (ℤ') hℤ' (N + s) (sectionGysinRule D sP hP _ _ (N + s) hM')
        (flatPullbackMap D sP hP sY hY π hπB n hflat hrel (a₀ + 1) (N + s + 1) hk1 ξ) :=
    Subtype.ext (coe_gysinCycleMap_sectionGysinRule_congr D sP hP _ hM' _ rfl _ _
      (coe_flatPullbackMap_congr D sY hY sP hP π hπB n hflat hrel rfl (by ring) haM hk1 ξ ξ rfl))
  rw [hcyc, h6]
  rfl

include hM hsq in
/-- **The relation of Stacks 0ERY under the Gysin map** of a section `t` of an invertible `ℳ` on
`Y`, `D' = Z(t)`, and of its pullback to `P`, `Z = Z(π^*t) = P ×_Y D'`:
`i_Z^*(∑ (-1)^i c₁(ℒ)^i ∩ π^* b_{r-i}) = ∑ (-1)^i c₁(ℒ|_Z)^i ∩ g₀^*(i^* b_{r-i})`. -/
theorem gysin_bundleRelationSumAt (e : ℤ) (he : (n : ℤ) = e) (r : ℕ) (k : ℤ)
    (b : ∀ j : Fin (r + 1), chowGroupCanonical.{u + 1} D sY hY (k + 1 - ((j : ℕ) : ℤ))) :
    sectionGysinChowGroupMap D sP hP _ _ hM' (k - r + e)
        (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sP hP m)
          (by ring) (bundleRelationSumAt D sY hY sP hP π hπB n hflat hrel L hL e he r (k + 1) b)) =
      bundleRelationSumAt D ((vanishingLocus D sY hY M t).1.ι ≫ sY)
        (isGood_vanishingLocus D sY hY M t) ((ℤ').1.ι ≫ sP) hℤ' g₀ hgbase n (hgfr).1 (hgfr).2
        Lℤ hLℤ e he r k
        (fun j => sectionGysinChowGroupMap D sY hY M t hM (k - ((j : ℕ) : ℤ))
          (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D sY hY m)
            (by ring) (b j))) := by
  simp only [bundleRelationSumAt, ProjectiveBundleRelation.relationSumAt,
    ProjectiveBundleRelation.relationTerm, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gysin_bundleFormulaCap_bundleRelationPull D sY hY sP hP π hπB n hflat hrel L hL M t hM hsq
    e he i (k + 1 - ((Fin.rev i : ℕ) : ℤ)) (k - ((Fin.rev i : ℕ) : ℤ))
    (k + 1 - r + e + (i : ℕ)) (k - r + e + (i : ℕ)) (k - r + e) (k + 1 - r + e) (by ring)
    (by ring) rfl rfl _ (ProjectiveBundleRelation.relationTerm_degree e r k i)]

end Gysin

/-! ### An isomorphism of bundles -/

section Iso

variable (D : BaseSpaceDimensionSituation.{u})
    {X P P' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (sP' : P' ⟶ D.space) (hP' : D.IsGood sP')
    (π : P ⟶ X) (hπB : π ≫ sX = sP) (π' : P' ⟶ X) (hπB' : π' ≫ sX = sP') (n : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension n D.site D.base D.base_mem π)
    (hflat' : IsFlat D.site D.base D.base_mem π')
    (hrel' : HasRelativeDimension n D.site D.base D.base_mem π')
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (L' : Modules.{u, u} D.site D.base D.base_mem P' hP'.1)
    (hL' : IsInvertibleModule (⟨P', hP'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L')
    (φ : P' ⟶ P) [IsIso φ] (hφB : φ ≫ sP = sP') (hφπ : φ ≫ π = π')
    (eL : (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk φ : (⟨P', hP'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨P, hP.1⟩)).obj L ≅ L')

include hφπ eL in
/-- **The relation of Stacks 0ERY along an isomorphism of bundles**: for `φ : P' ≅ P` over `X`
with `φ^*ℒ ≅ ℒ'`, the relation for `(π', ℒ')` is the flat pullback along `φ` of the one for
`(π, ℒ)`. -/
theorem bundleRelationSumAt_of_isIso (e : ℤ) (he : (n : ℤ) = e) (r : ℕ) (k : ℤ)
    (b : ∀ j : Fin (r + 1), chowGroupCanonical.{u + 1} D sX hX (k - ((j : ℕ) : ℤ))) :
    bundleRelationSumAt D sX hX sP' hP' π' hπB' n hflat' hrel' L' hL' e he r k b =
      flatPullbackChowMapCanonical.{u + 1} D sP' hP' sP hP φ hφB 0
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).1
        (isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP' hP' φ).2 _ _ (by simp)
        (bundleRelationSumAt D sX hX sP hP π hπB n hflat hrel L hL e he r k b) := by
  subst he
  simp only [bundleRelationSumAt, ProjectiveBundleRelation.relationSumAt,
    ProjectiveBundleRelation.relationTerm, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨ξ, hξ⟩ : ∃ ξ, chowClassCanonical.{u + 1} D sX hX _ ξ = b (Fin.rev i) :=
    QuotientAddGroup.mk'_surjective _ _
  rw [← hξ]
  exact congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
    (bundleFormulaCap_bundleFormulaPull_of_isIso D sX hX sP hP sP' hP' π hπB π' hπB' n hflat hrel
      hflat' hrel' L hL L' hL' φ hφB hφπ eL i _ _
      (ProjectiveBundleRelation.relationTerm_degree (n : ℤ) r k i) ξ)

end Iso

end AlgebraicGeometry.Space

end
