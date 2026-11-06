module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.ZeroFibreDegeneration.ProjectionFormula

/-!
# The intersection product along the zero fibre of a family over `𝐏¹`

Let `X ⟶ P` be a closed immersion of nonsingular varieties over an algebraically closed field
`K`, and let `C' ⊆ P × 𝐏¹` be a closed subvariety of dimension `r + 1` whose zero fibre
`C = C'_0` has dimension `r`. If `C'` meets `X × 𝐏¹` properly and `[C]_r` meets `X` properly,
then `α = [C]_r · X` and `β = C' · X × 𝐏¹`, read as cycles on `X` and on `X × 𝐏¹`, satisfy

`α = pr_{X,*}(β · X × 0)`.

This is Tag 0B1M.

## Main results

* `Stacks.Intersection.intersectionProduct_zeroFibre_eq_properPushforward_zeroSection` —
  **Tag 0B1M**.
* `Stacks.Intersection.eq_properPushforward_product_zeroSection` — the identity in a
  nonnegative expected dimension.
* `Stacks.Intersection.relativeDimension_add_le_of_mem_zeroFiber` — the zero fibre of `C'` meets
  `X` in the expected dimension.

## Implementation notes

The source's proof combines the projection formula for the flat morphism `P × 𝐏¹ ⟶ P`
(Tag 0B10), Tag 0B07 and associativity (Tag 0B1L). Here the projection formula is only needed for
cycles supported on `P × 0`, and it is proved directly: for a closed subvariety `Z ⊆ P`,
`Z × 0 = (Z × 𝐏¹) · (P × 0)` by Tag 0B07, so `(Z × 0) · (X × 𝐏¹)` is
`((Z × 𝐏¹) · (X × 𝐏¹)) · (P × 0)` by Tag 0B1L, which is `pr^*(Z · X) · (P × 0)` by Tag 0B0Z, and
`pr_*(pr^* a · (P × 0)) = a` by Tag 0B07. Then `[C]_r = pr_*(C' · P × 0)` by Tag 0B07 and Tag
0B1L exchanges `P × 0` and `X × 𝐏¹`.

The phrase "viewed as a cycle on `X`" is formalized by proving that the intersection products,
computed on `P` and on `P × 𝐏¹`, are pushforwards of cycles on `X` and on `X × 𝐏¹`, and stating
the identity for every such pair of cycles; pushforward along a closed immersion is injective, so
the two cycles are unique. That `β` and `X × 0` intersect properly, which the source uses
implicitly, is part of the conclusion.

## References

* [Stacks Project, Tag 0B1M](https://stacks.math.columbia.edu/tag/0B1M)
* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0B1L](https://stacks.math.columbia.edu/tag/0B1L)
* [Stacks Project, Tag 0B0Z](https://stacks.math.columbia.edu/tag/0B0Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.TorFormula Stacks.Chow

universe u

namespace Stacks.Intersection

variable (K : Type u) [Field K]

/-- The closure of the generic point of `C'` is its support. -/
private theorem closure_genericPoint_subschemeι_eq_support {P : Scheme.{u}}
    (sP : P ⟶ Spec (.of K)) (C' : (projectiveLineProduct sP).IdealSheafData)
    [IsIntegral C'.subscheme] :
    closure ({C'.subschemeι.base (genericPoint C'.subscheme)} :
      Set (projectiveLineProduct sP)) = (C'.support : Set (projectiveLineProduct sP)) :=
  (support_eq_closure_genericPointOf C' ‹_›).symm

/-- The base change of `ι` maps the zero section of `X × 𝐏¹` to that of `P × 𝐏¹`. -/
private theorem familyBaseChange_zeroSection_apply {X P : Scheme.{u}}
    (sP : P ⟶ Spec (.of K)) (ι : X ⟶ P) (u : X) :
    (familyBaseChange sP ι).base ((zeroSection (ι ≫ sP)).base u) =
      (zeroSection sP).base (ι.base u) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun f : X ⟶ projectiveLineProduct sP => f.base u)
    (constantSection_comp_familyBaseChange sP ι integralZeroSection)

section ZeroFibre

variable {K} [IsAlgClosed K] {X P : Scheme.{u}} (sP : P ⟶ Spec (.of K)) [IsVariety K sP]
  (ι : X ⟶ P) [IsClosedImmersion ι] [IsVariety K (ι ≫ sP)]
  (C' : (projectiveLineProduct sP).IdealSheafData) [IsIntegral C'.subscheme]

open scoped Classical in
/-- **The zero fibre of `C'` meets `X` in the expected dimension.** Let `C' ⊆ P × 𝐏¹` be an
integral closed subscheme of dimension `r + 1` not contained in `P × 0`, and assume that the
cycle `[C'_0]_r` of its zero fibre meets `X` properly. Then every point `t` of `C'_0 ∩ X`
satisfies `δ(t) + dim P ≤ r + dim X`: the zero fibre is an effective Cartier divisor on `C'`, so
each of its irreducible components has dimension `r` (Tag 02RK) and is a component of `[C'_0]_r`
(its multiplicity is positive), which meets `X` properly. -/
theorem relativeDimension_add_le_of_mem_zeroFiber (d p r : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (hp : topologicalKrullDim P = (p : WithBot ℕ∞))
    (hC'r : schemeDeltaDimension (fieldChowSituation K) (familyBase sP C') = ((r + 1 : ℤ) : EInt))
    (hnot : ¬ Set.range C'.subschemeι.base ⊆ Set.range (zeroSection sP).base)
    (h3 : AlgebraicCycle.IntersectProperly
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
        (zeroFiber sP C').subschemeι (r : ℤ)).1
      (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) (1 : ℤ)))
    (t : P) (ht : t ∈ ((zeroFiber sP C').support : Set P)) (htX : t ∈ Set.range ι.base) :
    relativeDimension (fieldChowSituation K).dimensionFunction sP t + p ≤ r + d := by
  classical
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  set D := zeroDivisor sP C'
  have hD := zeroDivisor_isEffectiveCartierDivisor sP C' hnot
  set ψ := D.subschemeι ≫ fibreBaseProjection sP C'
  have hker : ψ.ker = zeroFiber sP C' := ker_zeroDivisor_subschemeι_comp sP C'
  have hrange : Set.range ψ.base = ((zeroFiber sP C').support : Set P) := by
    rw [← hker, Scheme.Hom.support_ker, ψ.isClosedEmbedding.isClosed_range.closure_eq]
  rw [← hrange] at ht
  obtain ⟨s, rfl⟩ := ht
  obtain ⟨Z, hZ, hsZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({s} : Set D.subscheme)) isIrreducible_singleton.closure
  set ξ : D.subscheme := (genericPoints.ofComponent ⟨Z, hZ⟩).1
  have hξ : IsGenericPoint ξ Z := genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩
  have hξgen : ξ ∈ genericPoints D.subscheme := (genericPoints.ofComponent ⟨Z, hZ⟩).2
  -- the component has dimension `r`
  have hdelta := deltaDimension_irreducibleComponent_isEffectiveCartierDivisor
    (fieldChowSituation K) (familyBase sP C') D hD ⟨Z, hZ⟩
  rw [hC'r, deltaDimension] at hdelta
  have hgenZ : (⟨Z, (⟨Z, hZ⟩ : irreducibleComponents D.subscheme).2.1,
      isClosed_of_mem_irreducibleComponents (Z : Set D.subscheme) hZ⟩ :
        IrreducibleCloseds D.subscheme).isIrreducible.genericPoint = ξ :=
    ((hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)).eq hξ)
  rw [hgenZ] at hdelta
  have hrelξ : relativeDimension (fieldChowSituation K).dimensionFunction
      (D.subschemeι ≫ familyBase sP C') ξ = r := by
    have h' : ((relativeDimension (fieldChowSituation K).dimensionFunction
        (D.subschemeι ≫ familyBase sP C') ξ : ℤ) : EInt) = ((r : ℤ) : EInt) := by
      rw [hdelta, ← coe_add_coe_eq_coe_add]; congr 1; ring
    exact WithBotTop.coe_injective h'
  have hψs : ψ ≫ sP = D.subschemeι ≫ familyBase sP C' := by
    rw [Category.assoc, fibreBaseProjection_comp]
  have hrelψ : relativeDimension (fieldChowSituation K).dimensionFunction sP (ψ.base ξ) = r := by
    rw [← relativeDimension_comp_closedImmersion, hψs, hrelξ]
  -- it occurs in `[C'_0]_r`
  have hcoef : (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
      (zeroFiber sP C').subschemeι (r : ℤ)).1 (ψ.base ξ) ≠ 0 := by
    have hcyc : cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
        (zeroFiber sP C').subschemeι (r : ℤ) =
        cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP ψ (r : ℤ) := by
      rw [cycleAssociatedToClosedSubscheme_ker (fieldChowSituation K) sP ψ, hker]
    rw [hcyc, cycleAssociatedToClosedSubscheme_apply (fieldChowSituation K) sP ψ r ⟨ξ, hξgen⟩
      hrelψ]
    have : IsLocallyNoetherian D.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (ψ ≫ sP)
    exact componentMultiplicity_ne_zero ψ ⟨ξ, hξgen⟩
  have hprop := h3 ⟨closure {ψ.base ξ}, isIrreducible_singleton.closure, isClosed_closure⟩
    ⟨closure {ι.base (genericPoint X)}, isIrreducible_singleton.closure, isClosed_closure⟩
    (by rw [genericPoint_closure_singleton]; exact hcoef)
    (by rw [genericPoint_closure_singleton, Function.locallyFinsuppWithin.single_apply,
      if_pos rfl]; exact one_ne_zero)
  rw [AlgebraicGeometry.intersectProperly_iff] at hprop
  change topologicalKrullDim (↥(closure ({ψ.base ξ} : Set P) ∩ closure {ι.base (genericPoint X)}))
      + topologicalKrullDim P ≤ topologicalKrullDim (closure ({ψ.base ξ} : Set P)) +
        topologicalKrullDim (closure ({ι.base (genericPoint X)} : Set P)) at hprop
  rw [hp, topologicalKrullDim_closure_singleton_eq K sP, hrelψ,
    topologicalKrullDim_closure_image_genericPoint, hd] at hprop
  have hmem : ψ.base s ∈ closure ({ψ.base ξ} : Set P) ∩ closure {ι.base (genericPoint X)} := by
    refine ⟨?_, ?_⟩
    · have hsξ : s ∈ closure ({ξ} : Set D.subscheme) := by
        rw [hξ.def]; exact hsZ (subset_closure rfl)
      have h2 := image_closure_subset_closure_image ψ.continuous ⟨s, hsξ, rfl⟩
      rwa [Set.image_singleton] at h2
    · rw [← range_eq_closure_singleton]; exact htX
  have := ReductionToDiagonal.relativeDimension_add_le_of_topologicalKrullDim_add_le
    K sP (isClosed_closure.inter isClosed_closure) (N := r + d) (by exact_mod_cast hprop) hmem
  exact_mod_cast this

/-- The generic point of `C'` has relative dimension `dim C'`. -/
theorem relativeDimension_genericPoint_of_topologicalKrullDim (r : ℕ)
    (hC' : topologicalKrullDim (C'.support : Set (projectiveLineProduct sP)) =
      ((r + 1 : ℕ) : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation K).dimensionFunction
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
      (C'.subschemeι.base (genericPoint C'.subscheme)) = r + 1 := by
  have hc'cl := closure_genericPoint_subschemeι_eq_support K sP C'
  have h := hC'
  rw [← hc'cl, topologicalKrullDim_closure_singleton_eq K
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)] at h
  have h' := relativeDimension_fieldChowSituation_nonneg K
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
    (C'.subschemeι.base (genericPoint C'.subscheme))
  have h'' : (relativeDimension (fieldChowSituation K).dimensionFunction
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
      (C'.subschemeι.base (genericPoint C'.subscheme))).toNat = r + 1 := by exact_mod_cast h
  omega

/-- `C'` has delta-dimension `dim C'`. -/
theorem schemeDeltaDimension_familyBase_of_topologicalKrullDim (r : ℕ)
    (hC' : topologicalKrullDim (C'.support : Set (projectiveLineProduct sP)) =
      ((r + 1 : ℕ) : WithBot ℕ∞)) :
    schemeDeltaDimension (fieldChowSituation K) (familyBase sP C') = ((r + 1 : ℤ) : EInt) := by
  rw [schemeDeltaDimension_eq_genericPoint, familyBase, relativeDimension_comp_closedImmersion,
    relativeDimension_genericPoint_of_topologicalKrullDim sP C' r hC']

/-- If the zero fibre of `C'` has smaller dimension than `C'`, then `C'` is not contained in
`P × 0`. -/
theorem not_range_subset_zeroSection_of_topologicalKrullDim (r : ℕ)
    (hC' : topologicalKrullDim (C'.support : Set (projectiveLineProduct sP)) =
      ((r + 1 : ℕ) : WithBot ℕ∞))
    (h1 : topologicalKrullDim ((zeroFiber sP C').support : Set P) = (r : WithBot ℕ∞)) :
    ¬ Set.range C'.subschemeι.base ⊆ Set.range (zeroSection sP).base := by
  intro h
  have hsub : (C'.support : Set (projectiveLineProduct sP)) =
      (zeroSection sP).base '' ((zeroFiber sP C').support : Set P) := by
    rw [image_support_zeroFiber, Set.inter_eq_left.mpr]
    rwa [← Scheme.IdealSheafData.range_subschemeι]
  have h' := hC'
  rw [hsub, topologicalKrullDim_image_zeroSection, h1] at h'
  have : r = r + 1 := by exact_mod_cast h'
  omega

open scoped Classical in
/-- **The part of `X × 0` meeting a closed subset of `C' ∩ (X × 𝐏¹)` has small dimension.** Let
`e` be a point of `X × 𝐏¹` whose image in `P × 𝐏¹` lies on `C'`. Then every point `t` of
`closure {e}` lying on `X × 0` satisfies `δ(t) + dim P ≤ r + dim X`. -/
theorem relativeDimension_add_le_of_mem_closure_zeroSection (d p r : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (hp : topologicalKrullDim P = (p : WithBot ℕ∞))
    (hC' : topologicalKrullDim (C'.support : Set (projectiveLineProduct sP)) =
      ((r + 1 : ℕ) : WithBot ℕ∞))
    (h1 : topologicalKrullDim ((zeroFiber sP C').support : Set P) = (r : WithBot ℕ∞))
    (h3 : AlgebraicCycle.IntersectProperly
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
        (zeroFiber sP C').subschemeι (r : ℤ)).1
      (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) (1 : ℤ)))
    (e : projectiveLineProduct (ι ≫ sP))
    (he : (familyBaseChange sP ι).base e ∈ (C'.support : Set (projectiveLineProduct sP)))
    (t : projectiveLineProduct (ι ≫ sP)) (ht : t ∈ closure ({e} : Set _))
    (htσ : t ∈ Set.range (zeroSection (ι ≫ sP)).base) :
    relativeDimension (fieldChowSituation K).dimensionFunction
        (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
        t + p ≤ r + d := by
  obtain ⟨u, rfl⟩ := htσ
  have hmem : (zeroSection sP).base (ι.base u) ∈ (C'.support : Set (projectiveLineProduct sP)) := by
    rw [← familyBaseChange_zeroSection_apply]
    have h1' := image_closure_subset_closure_image (familyBaseChange sP ι).continuous
      ⟨_, ht, rfl⟩
    rw [Set.image_singleton] at h1'
    exact closure_minimal (Set.singleton_subset_iff.mpr he) C'.support.isClosed h1'
  have hu : ι.base u ∈ ((zeroFiber sP C').support : Set P) := by
    rw [coe_support_zeroFiber]; exact hmem
  have hEQ := relativeDimension_add_le_of_mem_zeroFiber sP ι C' d p r hd hp
    (schemeDeltaDimension_familyBase_of_topologicalKrullDim sP C' r hC')
    (not_range_subset_zeroSection_of_topologicalKrullDim sP C' r hC' h1) h3 _ hu ⟨u, rfl⟩
  rw [relativeDimension_zeroSection (ι ≫ sP) u, relativeDimension_comp_closedImmersion]
  exact hEQ

open scoped Classical in
/-- The zero fibre of `C'` meets `X` in dimension at most the expected dimension `n`. -/
theorem topologicalKrullDim_support_zeroFiber_inter_range_le (d p r n : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (hp : topologicalKrullDim P = (p : WithBot ℕ∞))
    (hrn : r + d = p + n)
    (hC' : topologicalKrullDim (C'.support : Set (projectiveLineProduct sP)) =
      ((r + 1 : ℕ) : WithBot ℕ∞))
    (h1 : topologicalKrullDim ((zeroFiber sP C').support : Set P) = (r : WithBot ℕ∞))
    (h3 : AlgebraicCycle.IntersectProperly
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
        (zeroFiber sP C').subschemeι (r : ℤ)).1
      (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) (1 : ℤ))) :
    topologicalKrullDim (↥(((zeroFiber sP C').support : Set P) ∩ Set.range ι.base)) ≤
      (n : WithBot ℕ∞) := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  refine ProjectionFormula.topologicalKrullDim_le_of_forall_relativeDimension_le K sP _
    ((zeroFiber sP C').support.isClosed.inter ι.isClosedEmbedding.isClosed_range) n
    fun t ht => ?_
  have := relativeDimension_add_le_of_mem_zeroFiber sP ι C' d p r hd hp
    (schemeDeltaDimension_familyBase_of_topologicalKrullDim sP C' r hC')
    (not_range_subset_zeroSection_of_topologicalKrullDim sP C' r hC' h1) h3 t ht.1 ht.2
  omega

open scoped Classical in
/-- The closures of the generic points of `C'`, `P × 0` and `X × 𝐏¹` meet in dimension at most
`dim C' + dim P + dim (X × 𝐏¹) - 2 dim (P × 𝐏¹)`. -/
theorem topologicalKrullDim_inter_zeroSection_familyBaseChange_add_le (d p r n : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (hp : topologicalKrullDim P = (p : WithBot ℕ∞))
    (hrn : r + d = p + n)
    (hC' : topologicalKrullDim (C'.support : Set (projectiveLineProduct sP)) =
      ((r + 1 : ℕ) : WithBot ℕ∞))
    (h1 : topologicalKrullDim ((zeroFiber sP C').support : Set P) = (r : WithBot ℕ∞))
    (h3 : AlgebraicCycle.IntersectProperly
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
        (zeroFiber sP C').subschemeι (r : ℤ)).1
      (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) (1 : ℤ))) :
    topologicalKrullDim
      (↥(closure ({C'.subschemeι.base (genericPoint C'.subscheme)} :
        Set (projectiveLineProduct sP)) ∩ closure {(zeroSection sP).base (genericPoint P)} ∩
          closure {(familyBaseChange sP ι).base
                    (genericPoint (projectiveLineProduct (ι ≫ sP)))})) +
        ((2 * (p + 1) : ℕ) : WithBot ℕ∞) ≤ ((r + 1 + p + (d + 1) : ℕ) : WithBot ℕ∞) := by
  have hc'cl := closure_genericPoint_subschemeι_eq_support K sP C'
  have hset : closure ({C'.subschemeι.base (genericPoint C'.subscheme)} :
      Set (projectiveLineProduct sP)) ∩ closure {(zeroSection sP).base (genericPoint P)} ∩
        closure {(familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))} =
      (zeroSection sP).base '' (((zeroFiber sP C').support : Set P) ∩ Set.range ι.base) := by
    rw [hc'cl, closure_zeroSection_genericPoint,
      ← range_eq_closure_singleton (familyBaseChange sP ι), range_familyBaseChange,
      Set.inter_assoc, range_zeroSection_inter_preimage, coe_support_zeroFiber, Set.inter_comm,
      ← Set.image_inter_preimage, Set.inter_comm]
  rw [hset, topologicalKrullDim_image_zeroSection]
  calc topologicalKrullDim (↥(((zeroFiber sP C').support : Set P) ∩ Set.range ι.base)) +
        ((2 * (p + 1) : ℕ) : WithBot ℕ∞)
      ≤ (n : WithBot ℕ∞) + ((2 * (p + 1) : ℕ) : WithBot ℕ∞) :=
        add_le_add (topologicalKrullDim_support_zeroFiber_inter_range_le sP ι C' d p r n hd hp
          hrn hC' h1 h3) le_rfl
    _ = ((r + 1 + p + (d + 1) : ℕ) : WithBot ℕ∞) := by
      rw [← Nat.cast_add]
      congr 1
      omega

open scoped Classical in
/-- **The core identity of Tag 0B1M, in nonnegative expected dimension `n`.** -/
theorem eq_properPushforward_product_zeroSection (hX : IsRegular X) (hP : IsRegular P)
    (d p r n : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hp : topologicalKrullDim P = (p : WithBot ℕ∞)) (hrn : r + d = p + n)
    (hC' : topologicalKrullDim (C'.support : Set (projectiveLineProduct sP)) =
      ((r + 1 : ℕ) : WithBot ℕ∞))
    (h1 : topologicalKrullDim ((zeroFiber sP C').support : Set P) = (r : WithBot ℕ∞))
    (h2 : topologicalKrullDim ↥((C'.support : Set (projectiveLineProduct sP)) ∩
          Set.range (familyBaseChange sP ι).base) +
        topologicalKrullDim (projectiveLineProduct sP) ≤
      topologicalKrullDim (C'.support : Set (projectiveLineProduct sP)) +
        topologicalKrullDim (Set.range (familyBaseChange sP ι).base))
    (h3 : AlgebraicCycle.IntersectProperly
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
        (zeroFiber sP C').subschemeι (r : ℤ)).1
      (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) (1 : ℤ)))
    (α : CycleGroup (fieldChowSituation K) (ι ≫ sP) (n : ℤ))
    (β : CycleGroup (fieldChowSituation K)
      (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
      ((n : ℤ) + 1))
    (hβ1 : ∀ e, β.1 e ≠ 0 → ¬ Set.range (integralComponentAt e).subschemeι.base ⊆
      Set.range (zeroSection (ι ≫ sP)).base)
    (hβ2 : ∀ e, β.1 e ≠ 0 → ¬ Set.range
      (integralComponentAt ((familyBaseChange sP ι).base e)).subschemeι.base ⊆
        Set.range (zeroSection sP).base) :
    letI : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
    letI : IsLocallyNoetherian (projectiveLineProduct sP) :=
      isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct sP hP)
    letI : IsLocallyNoetherian (projectiveLineProduct (ι ≫ sP)) :=
      isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct (ι ≫ sP) hX)
    (properPushforward (fieldChowSituation K) (ι ≫ sP) sP ι rfl _ α).1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP (n : ℤ)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
            (zeroFiber sP C').subschemeι (r : ℤ)).1
          (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) 1) →
      (properPushforward (fieldChowSituation K) _
          (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
          (familyBaseChange sP ι) (familyBaseChange_comp_structure K sP ι) _ β).1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation K)
          (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
          (isRegular_projectiveLineProduct sP hP) ((n : ℤ) + 1)
          (Function.locallyFinsuppWithin.single
            (C'.subschemeι.base (genericPoint C'.subscheme)) 1)
          (Function.locallyFinsuppWithin.single
            ((familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))) 1) →
      α = properPushforward (fieldChowSituation K)
        (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
        (ι ≫ sP) (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)))
        rfl (n : ℤ)
        ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K)
            (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫
              ι ≫ sP)
            (isRegular_projectiveLineProduct (ι ≫ sP) hX) (n : ℤ) β.1
            (Function.locallyFinsuppWithin.single
              ((zeroSection (ι ≫ sP)).base (genericPoint X)) 1),
          torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ := by
  intro hα hβ
  let : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
  let : IsLocallyNoetherian (projectiveLineProduct sP) :=
    isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct sP hP)
  let : IsLocallyNoetherian (projectiveLineProduct (ι ≫ sP)) :=
    isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct (ι ≫ sP) hX)
  have : CompactSpace (projectiveLineProduct sP) := QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
  have hQ := isRegular_projectiveLineProduct sP hP
  have hc'cl := closure_genericPoint_subschemeι_eq_support K sP C'
  have hIc' : integralComponentAt (C'.subschemeι.base (genericPoint C'.subscheme)) = C' := by
    rw [← ker_eq_integralComponentAt, Scheme.IdealSheafData.ker_subschemeι]
  have hdQ : topologicalKrullDim (projectiveLineProduct sP) = ((p + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_projectiveLineProduct, hp]; push_cast; rfl
  have hc'dim : topologicalKrullDim (closure ({C'.subschemeι.base (genericPoint C'.subscheme)} :
      Set (projectiveLineProduct sP))) = ((r + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hc'cl, hC']
  have hrelc' := relativeDimension_genericPoint_of_topologicalKrullDim sP C' r hC'
  have hnot' : ¬ Set.range (integralComponentAt
      (C'.subschemeι.base (genericPoint C'.subscheme))).subschemeι.base ⊆
        Set.range (zeroSection sP).base := by
    rw [hIc']
    exact not_range_subset_zeroSection_of_topologicalKrullDim sP C' r hC' h1
  have hpushγ := properPushforward_eq_zeroFiberCycle_of_coe_eq_single sP hQ
    (C'.subschemeι.base (genericPoint C'.subscheme)) r (by rw [hrelc']) hnot'
    ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K)
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) hQ r
      (Function.locallyFinsuppWithin.single (C'.subschemeι.base (genericPoint C'.subscheme)) 1)
      (Function.locallyFinsuppWithin.single ((zeroSection sP).base (genericPoint P)) 1),
      torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ rfl
  rw [hIc'] at hpushγ
  have hγsupp : ∀ q, torFormulaCycleIntersectionProduct (fieldChowSituation K)
      (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) hQ r
      (Function.locallyFinsuppWithin.single (C'.subschemeι.base (genericPoint C'.subscheme)) 1)
      (Function.locallyFinsuppWithin.single ((zeroSection sP).base (genericPoint P)) 1) q ≠ 0 →
      q ∈ Set.range (zeroSection sP).base := fun q hq => by
    rw [← closure_zeroSection_genericPoint sP]
    exact mem_closure_of_torFormula_single_right_ne_zero K _ hQ hdQ r _ _ q hq
  have hG := torFormula_properPushforward_eq_properPushforward_zeroSection sP ι hP d p r n hd hp
    hrn _ hγsupp (by rw [hpushγ]; exact h3)
  rw [hpushγ] at hG
  have hcy : closure ({
      (familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))} :
        Set (projectiveLineProduct sP)) =
      Set.range (familyBaseChange sP ι).base :=
    (range_eq_closure_singleton (familyBaseChange sP ι)).symm
  have hδ : topologicalKrullDim (closure ({(zeroSection sP).base (genericPoint P)} :
      Set (projectiveLineProduct sP))) = (p : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_image_genericPoint, hp]
  have hy : topologicalKrullDim (closure ({
      (familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))} :
        Set (projectiveLineProduct sP))) =
      ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_closure_familyBaseChange_genericPoint, hd]; push_cast; rfl
  have hrangeι : topologicalKrullDim (Set.range ι.base) = (d : WithBot ℕ∞) := by
    rw [range_eq_closure_singleton, topologicalKrullDim_closure_image_genericPoint, hd]
  have hc'δ : AlgebraicGeometry.IntersectProperly
      ⟨closure {C'.subschemeι.base (genericPoint C'.subscheme)}, isIrreducible_singleton.closure,
        isClosed_closure⟩
      ⟨closure {(zeroSection sP).base (genericPoint P)}, isIrreducible_singleton.closure,
        isClosed_closure⟩ := by
    rw [intersectProperly_closure_singleton_iff, hc'dim, hδ, hc'cl,
      closure_zeroSection_genericPoint, ← image_support_zeroFiber,
      topologicalKrullDim_image_zeroSection, h1, hdQ]
    exact_mod_cast (by omega : r + (p + 1) ≤ r + 1 + p)
  have hδy : AlgebraicGeometry.IntersectProperly
      ⟨closure {(zeroSection sP).base (genericPoint P)}, isIrreducible_singleton.closure,
        isClosed_closure⟩
      ⟨closure {(familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))},
        isIrreducible_singleton.closure, isClosed_closure⟩ := by
    rw [intersectProperly_closure_singleton_iff, hδ, hy, closure_zeroSection_genericPoint, hcy,
      range_familyBaseChange, range_zeroSection_inter_preimage,
      topologicalKrullDim_image_zeroSection, hrangeι, hdQ]
    exact_mod_cast (by omega : d + (p + 1) ≤ p + (d + 1))
  have hc'y : AlgebraicGeometry.IntersectProperly
      ⟨closure {C'.subschemeι.base (genericPoint C'.subscheme)}, isIrreducible_singleton.closure,
        isClosed_closure⟩
      ⟨closure {(familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))},
        isIrreducible_singleton.closure, isClosed_closure⟩ := by
    rwa [intersectProperly_closure_singleton_iff, hc'cl, hcy]
  have htriple := topologicalKrullDim_inter_zeroSection_familyBaseChange_add_le sP ι C' d p r n
    hd hp hrn hC' h1 h3
  -- `(C' · P × 0) · X × 𝐏¹ = (C' · X × 𝐏¹) · P × 0` (Tag 0B1L)
  have hswap := torFormula_single_single_swap K
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) hQ
    (C'.subschemeι.base (genericPoint C'.subscheme)) ((zeroSection sP).base (genericPoint P))
    ((familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP))))
    (p + 1) (r + 1) p (d + 1) hdQ hc'dim hδ hy hc'δ hδy hc'y htriple
  have e1 : (((r + 1 : ℕ) : ℤ) + (p : ℤ) - ((p + 1 : ℕ) : ℤ)) = (r : ℤ) := by push_cast; ring
  have e2 : (((r + 1 : ℕ) : ℤ) + (p : ℤ) + ((d + 1 : ℕ) : ℤ) - 2 * ((p + 1 : ℕ) : ℤ)) =
      (n : ℤ) := by push_cast; omega
  have e3 : (((r + 1 : ℕ) : ℤ) + ((d + 1 : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by
    push_cast; omega
  rw [e1, e2, e3] at hswap
  have hM4 := properPushforward_properPushforward_product_zeroSection sP ι hX hP (n : ℤ) β hβ1 hβ2
  apply properPushforward_injective_of_isClosedImmersion (fieldChowSituation K) (ι ≫ sP) sP ι rfl
  apply Subtype.ext
  rw [hα, hG, hM4, hβ]
  exact congrArg (fun c => (properPushforward (fieldChowSituation K)
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) sP
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))) rfl (n : ℤ) c).1)
    (Subtype.ext hswap)

end ZeroFibre

open scoped Classical in
/-- **Stacks Project, Tag 0B1M.** Let `X ⟶ P` be a closed immersion of nonsingular varieties over
an algebraically closed field `K`, of dimensions `d` and `p`, and let `C' ⊆ P × 𝐏¹` be a closed
subvariety of dimension `r + 1` such that

1. the zero fibre `C = C'_0` (the scheme-theoretic fibre `zeroFiber sP C'`) has dimension `r`,
2. `C'` intersects `X × 𝐏¹` properly,
3. `[C]_r` intersects `X` properly.

Then `[C]_r · X`, an `(r + d - p)`-cycle on `P`, is the pushforward of a cycle `α` on `X`, and
`C' · X × 𝐏¹`, an `(r + d - p + 1)`-cycle on `P × 𝐏¹`, is the pushforward of a cycle `β` on
`X × 𝐏¹`; and for any such `α` and `β`, the cycle `β` intersects `X × 0` properly and

`α = pr_{X,*}(β · X × 0)`.

The intersection products are those of Tag 0B08, `X × 𝐏¹ ⟶ P × 𝐏¹` is the base change of `ι`,
`X × 0` is the image of the zero section, and `pr_X` is the first projection. -/
@[stacks 0B1M "the whole lemma, for a closed immersion of nonsingular varieties over an \
algebraically closed field and a closed subvariety `C'` of `P × 𝐏¹` presented as an integral \
closed subscheme: clause (1) is the dimension of the scheme-theoretic zero fibre, clause (2) the \
Tag 0AZQ inequality for `C'` and `X × 𝐏¹`, clause (3) proper intersection of the cycles `[C]_r` \
and `[X]`. The conclusion states that the two products are pushforwards of cycles `α` on `X` and \
`β` on `X × 𝐏¹`, that `β` and `X × 0` intersect properly, and that `α = pr_{X,*}(β · X × 0)` \
for every such `α` and `β`."]
theorem intersectionProduct_zeroFibre_eq_properPushforward_zeroSection
    [IsAlgClosed K] {X P : Scheme.{u}} (sP : P ⟶ Spec (.of K)) [IsVariety K sP]
    (ι : X ⟶ P) [IsClosedImmersion ι] [IsVariety K (ι ≫ sP)] (hX : IsRegular X)
    (hP : IsRegular P) (d p r : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hp : topologicalKrullDim P = (p : WithBot ℕ∞))
    (C' : (projectiveLineProduct sP).IdealSheafData) [IsIntegral C'.subscheme]
    (hC' : topologicalKrullDim (C'.support : Set (projectiveLineProduct sP)) =
      ((r + 1 : ℕ) : WithBot ℕ∞))
    (h1 : topologicalKrullDim ((zeroFiber sP C').support : Set P) = (r : WithBot ℕ∞))
    (h2 : topologicalKrullDim ↥((C'.support : Set (projectiveLineProduct sP)) ∩
          Set.range (familyBaseChange sP ι).base) +
        topologicalKrullDim (projectiveLineProduct sP) ≤
      topologicalKrullDim (C'.support : Set (projectiveLineProduct sP)) +
        topologicalKrullDim (Set.range (familyBaseChange sP ι).base))
    (h3 : AlgebraicCycle.IntersectProperly
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
        (zeroFiber sP C').subschemeι (r : ℤ)).1
      (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) (1 : ℤ))) :
    letI : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
    letI : IsLocallyNoetherian (projectiveLineProduct sP) :=
      isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct sP hP)
    letI : IsLocallyNoetherian (projectiveLineProduct (ι ≫ sP)) :=
      isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct (ι ≫ sP) hX)
    (∃ α : CycleGroup (fieldChowSituation K) (ι ≫ sP) ((r : ℤ) + d - p),
        (properPushforward (fieldChowSituation K) (ι ≫ sP) sP ι rfl _ α).1 =
          torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP ((r : ℤ) + d - p)
            (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
              (zeroFiber sP C').subschemeι (r : ℤ)).1
            (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) 1)) ∧
      (∃ β : CycleGroup (fieldChowSituation K)
          (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
          ((r : ℤ) + d - p + 1),
        (properPushforward (fieldChowSituation K) _
            (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
            (familyBaseChange sP ι) (familyBaseChange_comp_structure K sP ι) _ β).1 =
          torFormulaCycleIntersectionProduct (fieldChowSituation K)
            (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
            (isRegular_projectiveLineProduct sP hP) ((r : ℤ) + d - p + 1)
            (Function.locallyFinsuppWithin.single
              (C'.subschemeι.base (genericPoint C'.subscheme)) 1)
            (Function.locallyFinsuppWithin.single
              ((familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))) 1))
        ∧
      ∀ (α : CycleGroup (fieldChowSituation K) (ι ≫ sP) ((r : ℤ) + d - p))
        (β : CycleGroup (fieldChowSituation K)
          (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
          ((r : ℤ) + d - p + 1)),
        (properPushforward (fieldChowSituation K) (ι ≫ sP) sP ι rfl _ α).1 =
          torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP ((r : ℤ) + d - p)
            (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP
              (zeroFiber sP C').subschemeι (r : ℤ)).1
            (Function.locallyFinsuppWithin.single (ι.base (genericPoint X)) 1) →
        (properPushforward (fieldChowSituation K) _
            (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
            (familyBaseChange sP ι) (familyBaseChange_comp_structure K sP ι) _ β).1 =
          torFormulaCycleIntersectionProduct (fieldChowSituation K)
            (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
            (isRegular_projectiveLineProduct sP hP) ((r : ℤ) + d - p + 1)
            (Function.locallyFinsuppWithin.single
              (C'.subschemeι.base (genericPoint C'.subscheme)) 1)
            (Function.locallyFinsuppWithin.single
              ((familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))) 1) →
        AlgebraicCycle.IntersectProperly β.1
            (Function.locallyFinsuppWithin.single
              ((zeroSection (ι ≫ sP)).base (genericPoint X)) 1) ∧
          α = properPushforward (fieldChowSituation K)
            (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
            (ι ≫ sP) (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)))
            rfl ((r : ℤ) + d - p)
            ⟨torFormulaCycleIntersectionProduct (fieldChowSituation K)
                (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫
                  ι ≫ sP)
                (isRegular_projectiveLineProduct (ι ≫ sP) hX) ((r : ℤ) + d - p) β.1
                (Function.locallyFinsuppWithin.single
                  ((zeroSection (ι ≫ sP)).base (genericPoint X)) 1),
              torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _⟩ := by
  let : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
  let : IsLocallyNoetherian (projectiveLineProduct sP) :=
    isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct sP hP)
  let : IsLocallyNoetherian (projectiveLineProduct (ι ≫ sP)) :=
    isLocallyNoetherian_of_isRegular (isRegular_projectiveLineProduct (ι ≫ sP) hX)
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace sP
  have : CompactSpace (projectiveLineProduct sP) := QuasiCompact.compactSpace_of_compactSpace
    (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP)
  have hQ := isRegular_projectiveLineProduct sP hP
  have hdQ : topologicalKrullDim (projectiveLineProduct sP) = ((p + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_projectiveLineProduct, hp]; push_cast; rfl
  have hcx : closure ({ι.base (genericPoint X)} : Set P) = Set.range ι.base :=
    (range_eq_closure_singleton ι).symm
  have hcy : closure ({
      (familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))} :
        Set (projectiveLineProduct sP)) =
      Set.range (familyBaseChange sP ι).base :=
    (range_eq_closure_singleton (familyBaseChange sP ι)).symm
  have hc'cl := closure_genericPoint_subschemeι_eq_support K sP C'
  refine ⟨?_, ?_, ?_⟩
  · refine exists_properPushforward_eq_of_support_subset K sP (ι ≫ sP) ι rfl _ _
      (torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _) fun z hz => ?_
    refine subset_closure ?_
    rw [← hcx]
    exact mem_closure_of_torFormula_single_right_ne_zero K sP hP hp _ _ _ z hz
  · refine exists_properPushforward_eq_of_support_subset K _ _ (familyBaseChange sP ι)
      (familyBaseChange_comp_structure K sP ι) _ _
      (torFormulaCycleIntersectionProduct_mem_cyclesOfDimension _ _ _ _ _ _) fun z hz => ?_
    refine subset_closure ?_
    rw [← hcy]
    exact mem_closure_of_torFormula_single_right_ne_zero K _ hQ hdQ _ _ _ z hz
  generalize hm : (r : ℤ) + d - p = m
  intro α β hα hβ
  -- the components of `β`
  have hrelβ : ∀ e, β.1 e ≠ 0 → relativeDimension (fieldChowSituation K).dimensionFunction
      (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
      e = m + 1 := fun e he =>
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) _ _ β.1).1 β.2 e he
  have hcomp : ∀ e, β.1 e ≠ 0 →
      (familyBaseChange sP ι).base e ∈ (C'.support : Set (projectiveLineProduct sP)) := by
    intro e he
    have hBe : torFormulaCycleIntersectionProduct (fieldChowSituation K)
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ sP) hQ (m + 1)
        (Function.locallyFinsuppWithin.single (C'.subschemeι.base (genericPoint C'.subscheme)) 1)
        (Function.locallyFinsuppWithin.single
          ((familyBaseChange sP ι).base (genericPoint (projectiveLineProduct (ι ≫ sP)))) 1)
        ((familyBaseChange sP ι).base e) ≠ 0 := by
      rw [← hβ, properPushforward_apply_image_of_isClosedImmersion]; exact he
    rw [← hc'cl]
    exact (mem_inter_of_torFormula_single_single_ne_zero K _ hQ hdQ _ _ _ _ hBe).1.1
  have hsmall : ∀ e, β.1 e ≠ 0 → ∀ t ∈ closure ({e} : Set (projectiveLineProduct (ι ≫ sP))),
      t ∈ Set.range (zeroSection (ι ≫ sP)).base →
      relativeDimension (fieldChowSituation K).dimensionFunction
        (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
        t + p ≤ r + d := fun e he t ht htσ =>
    relativeDimension_add_le_of_mem_closure_zeroSection sP ι C' d p r hd hp hC' h1 h3 e
      (hcomp e he) t ht htσ
  have hβ0 : ∀ e, β.1 e ≠ 0 → e ∉ Set.range (zeroSection (ι ≫ sP)).base := by
    intro e he hee
    have := hsmall e he e (subset_closure rfl) hee
    rw [hrelβ e he] at this
    omega
  have hmemc : ∀ {Y : Scheme.{u}} [IsLocallyNoetherian Y] (e : Y),
      e ∈ Set.range (integralComponentAt e).subschemeι.base := fun e => by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
    exact subset_closure rfl
  have hβ1 : ∀ e, β.1 e ≠ 0 → ¬ Set.range (integralComponentAt e).subschemeι.base ⊆
      Set.range (zeroSection (ι ≫ sP)).base :=
    fun e he hsub => hβ0 e he (hsub (hmemc e))
  have hβ2 : ∀ e, β.1 e ≠ 0 → ¬ Set.range
      (integralComponentAt ((familyBaseChange sP ι).base e)).subschemeι.base ⊆
        Set.range (zeroSection sP).base := by
    intro e he hsub
    obtain ⟨v, hv⟩ := hsub (hmemc _)
    set u := (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base e
    have hvu : v = ι.base u := by
      have h := congrArg
        (pullback.fst sP (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K))).base hv
      rw [← Scheme.Hom.comp_apply, zeroSection_comp_fst, ← Scheme.Hom.comp_apply,
        familyBaseChange_comp_fst, Scheme.Hom.comp_apply] at h
      exact h
    have hj : (familyBaseChange sP ι).base ((zeroSection (ι ≫ sP)).base u) =
        (familyBaseChange sP ι).base e := by
      rw [familyBaseChange_zeroSection_apply, ← hvu, hv]
    exact hβ0 e he ⟨u, (familyBaseChange sP ι).isClosedEmbedding.injective hj⟩
  refine ⟨?_, ?_⟩
  · -- `β` and `X × 0` intersect properly
    intro W V hW hV
    have hVg : V.isIrreducible.genericPoint = (zeroSection (ι ≫ sP)).base (genericPoint X) := by
      by_contra h
      rw [Function.locallyFinsuppWithin.single_apply, if_neg h] at hV
      exact hV rfl
    rw [AlgebraicGeometry.intersectProperly_iff,
      ReductionToDiagonal.coe_irreducibleCloseds_eq_closure_genericPoint W,
      ReductionToDiagonal.coe_irreducibleCloseds_eq_closure_genericPoint V, hVg,
      topologicalKrullDim_closure_image_genericPoint, topologicalKrullDim_projectiveLineProduct, hd,
      topologicalKrullDim_closure_singleton_eq K
        (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP),
      ← range_eq_closure_singleton (zeroSection (ι ≫ sP)), hrelβ _ hW]
    by_cases hne : (closure ({W.isIrreducible.genericPoint} :
        Set (projectiveLineProduct (ι ≫ sP))) ∩ Set.range (zeroSection (ι ≫ sP)).base).Nonempty
    · obtain ⟨t, ht1, ht2⟩ := hne
      have h0 := hsmall _ hW t ht1 ht2
      have h0' := relativeDimension_fieldChowSituation_nonneg K
        (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP) t
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, by omega⟩
      have hT : topologicalKrullDim (↥(closure ({W.isIrreducible.genericPoint} :
          Set (projectiveLineProduct (ι ≫ sP))) ∩ Set.range (zeroSection (ι ≫ sP)).base)) ≤
          (n : WithBot ℕ∞) := by
        refine ProjectionFormula.topologicalKrullDim_le_of_forall_relativeDimension_le K
          (pullback.fst (ι ≫ sP) (relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) ≫ ι ≫ sP)
          _ (isClosed_closure.inter (zeroSection (ι ≫ sP)).isClosedEmbedding.isClosed_range) n
          fun t' ht' => ?_
        have := hsmall _ hW t' ht'.1 ht'.2
        omega
      have htn : ((n : ℤ) + 1).toNat = n + 1 := by omega
      rw [htn]
      calc _ ≤ (n : WithBot ℕ∞) + ((d : WithBot ℕ∞) + 1) := add_le_add hT le_rfl
        _ = (((n + 1 : ℕ)) : WithBot ℕ∞) + (d : WithBot ℕ∞) := by
          rw [← Nat.cast_one (R := WithBot ℕ∞), ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
          congr 1
          omega
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      have hbot : topologicalKrullDim (↥(∅ : Set (projectiveLineProduct (ι ≫ sP)))) = ⊥ := by
        have : IsEmpty (IrreducibleCloseds (↥(∅ : Set (projectiveLineProduct (ι ≫ sP))))) :=
          ⟨fun Z => by obtain ⟨⟨x, hx⟩, _⟩ := Z.isIrreducible.nonempty; exact hx⟩
        exact Order.krullDim_eq_bot
      rw [hbot, WithBot.bot_add]
      exact bot_le
  · by_cases hm0 : 0 ≤ m
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, by omega⟩
      exact eq_properPushforward_product_zeroSection sP ι C' hX hP d p r n hd hp (by omega) hC' h1
        h2 h3 α β hβ1 hβ2 hα hβ
    · rw [cycleGroup_eq_zero_of_neg K _ (by omega) α,
        cycleGroup_eq_zero_of_neg K _ (by omega) (properPushforward _ _ _ _ _ _ _)]

end Stacks.Intersection

end
