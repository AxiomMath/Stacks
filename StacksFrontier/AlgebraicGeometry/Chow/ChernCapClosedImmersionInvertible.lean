module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponentModuleIso
public import StacksFrontier.AlgebraicGeometry.Chow.InvertibleChernSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective

/-!
# Proper pushforward along a closed immersion and the first Chern class cap product

Let `p : X ⟶ Y` be a closed immersion of schemes locally of finite type over the base scheme `S`
of chapter 42 of the Stacks Project and let `ℒ` be an invertible `𝒪_Y`-module. This file proves
the projection formula

  `p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`  in  `A_k(Y)`,  for `α ∈ Z_{k+1}(X)`,

for the cap product `Stacks.Chow.firstChernClassCapOfInvertible` of an invertible module, with no
hypothesis beyond `p` being a closed immersion over the base.

## The two halves of the proof

`Stacks.Chow.pullbackComponentRule` transports the component rule of `ℒ` from `Y` to `X` along
the isomorphism of an integral closed subscheme `W ⊆ X` with its scheme-theoretic image
`W.map p`, and `Stacks.Chow.properChowPushforward_firstChernClassCap_pullbackComponentRule` proves
the projection formula for that transported rule outright. What remains is to compare the
transported rule with the component rule of `p^*ℒ`, and the two differ: each picks its own
meromorphic section, on `W` and on `W.map p`, by an independent choice. So they agree only in
the Chow group of `W`, and `Stacks.Chow.firstChernClassCap_congr` is what turns that into equality
of the cap products.

The comparison on one component is the composite of three steps. The chosen section on `W.map p`
pulls back along the component isomorphism to a nonzero section of the pullback module
(Stacks 02ST, first displayed equation, which identifies the pushforward of its divisor with the
divisor of the original section, the degree of the extension of function fields being one); the
pullback module is isomorphic to the restriction of `p^*ℒ`, which moves the divisor cycle not at
all (`Stacks.Chow.chernComponentCycle_mapStalkLinearMap`); and the divisor cycles of two nonzero
sections of one module are rationally equivalent, which is Stacks 02SJ (2).

## Main results

* `Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule` — the
  component rule of `p^*ℒ` and the transported rule of `ℒ` agree in the Chow group of each
  integral component.
* `Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible` — **Stacks 02SU for a
  closed immersion.**

## Implementation notes

The module isomorphism is built from Mathlib's `AlgebraicGeometry.Scheme.Modules.pullbackComp`
and `AlgebraicGeometry.Scheme.Modules.pullbackCongr`, the two factorizations
`W ⟶ W.map p ⟶ Y` and `W ⟶ X ⟶ Y` of one morphism being equal by
`Stacks.Chow.imageIsoOfIsClosedImmersion_hom_subschemeι`.

Stacks 02ST is stated for `Stacks.Chow.meromorphicDivisorCycle`, graded as a cycle of
delta-dimension `n - 1` on a scheme of delta-dimension `n`, while the component rule of
Stacks 02SO uses `Stacks.Chow.chernComponentCycle`, graded as a `k`-cycle on a scheme of
delta-dimension `k + 1`. The two have the same underlying algebraic cycle, and proper pushforward
reads only that, so the two gradings are crossed by `Subtype.ext` rather than by a cast.

## References

* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

/-- A stalk basis of a module whose stalk is not the zero module is nonzero: multiplication by
the zero element is the zero map, which is not surjective onto a nonzero module. -/
theorem IsStalkBasis.ne_zero {X : Scheme.{u}} {L : X.Modules} {x : X}
    {m : L.presheaf.stalk x} (hm : IsStalkBasis L x m)
    (h : ∃ n : L.presheaf.stalk x, n ≠ 0) : m ≠ 0 := by
  rintro rfl
  obtain ⟨n, hn⟩ := h
  obtain ⟨r, hr⟩ := hm.surjective n
  exact hn (by rw [← hr]; exact smul_zero r)

end Stacks.Divisors

namespace Stacks.Chow

open Stacks.Divisors

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsClosedImmersion p] (hp : p ≫ sY = sX)
  (k : ℤ) (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [IsClosedImmersion p]
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] in
/-- The divisor cycle of Stacks 02SJ (1) and the component cycle of Stacks 02SO have the same
underlying algebraic cycle: both are specified by the order of vanishing at the generic point of
each prime divisor and by zero at every other point. The two live in different cycle groups, the
first graded `n - 1` from `dim_δ = n` and the second graded `k` from `dim_δ = k + 1`. -/
theorem val_meromorphicDivisorCycle_eq_chernComponentCycle {V : Scheme.{u}} (q : V ⟶ C.S)
    [LocallyOfFiniteType q] [IsIntegral V] [IsLocallyNoetherian V] {m : ℤ}
    (hm : schemeDeltaDimension C q = ((m + 1 : ℤ) : EInt)) {M : V.Modules}
    (hM : ∀ x : V, IsTrivializedNear M x) (s : M.presheaf.stalk (genericPoint V)) :
    ((meromorphicDivisorCycle C q hm hM s).val : AlgebraicCycle V ℤ) =
      ((chernComponentCycle C q hm hM s : CycleGroup C q m) : AlgebraicCycle V ℤ) := by
  refine Function.locallyFinsuppWithin.ext fun x => ?_
  by_cases hx : ∃ Z : Stacks.Divisors.PrimeDivisor V, Z.genericPoint = x
  · obtain ⟨Z, rfl⟩ := hx
    rw [meromorphicDivisorCycle_genericPoint, chernComponentCycle_genericPoint]
  · have hne : ∀ Z : Stacks.Divisors.PrimeDivisor V, Z.genericPoint ≠ x := fun Z hZ => hx ⟨Z, hZ⟩
    rw [meromorphicDivisorCycle_eq_zero C q hm hM s x hne,
      chernComponentCycle_eq_zero C q hm hM s x hne]

omit [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] in
/-- Proper pushforward reads only the underlying algebraic cycle, so two cycles with the same
underlying cycle — possibly in different gradings — push forward to cycles with the same
underlying cycle. -/
theorem val_properPushforward_eq_of_val_eq {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (g : A ⟶ B) [IsProper g]
    (hg : g ≫ sB = sA) {m m' : ℤ} (c : CycleGroup C sA m) (c' : CycleGroup C sA m')
    (h : (c : AlgebraicCycle A ℤ) = (c' : AlgebraicCycle A ℤ)) :
    ((properPushforward C sA sB g hg m c : CycleGroup C sB m) : AlgebraicCycle B ℤ) =
      ((properPushforward C sA sB g hg m' c' : CycleGroup C sB m') : AlgebraicCycle B ℤ) := by
  refine Function.locallyFinsuppWithin.ext fun z => ?_
  rw [properPushforward_apply_eq_map C sA sB g hg m c z,
    properPushforward_apply_eq_map C sA sB g hg m' c' z, h]

include hp

/-- The restriction of `ℒ` to the scheme-theoretic image, pulled back along the component
isomorphism, is isomorphic to the restriction of `p^*ℒ`: both are the pullback of `ℒ` along the
one morphism `W ⟶ Y`, written through its two factorizations. -/
def imageModuleIso (W : X.IdealSheafData) :
    (Scheme.Modules.pullback (imageIsoOfIsClosedImmersion p W).hom).obj
        ((Scheme.Modules.pullback (W.map p).subschemeι).obj L) ≅
      (Scheme.Modules.pullback W.subschemeι).obj ((Scheme.Modules.pullback p).obj L) :=
  (Scheme.Modules.pullbackComp (imageIsoOfIsClosedImmersion p W).hom
      (W.map p).subschemeι).app L ≪≫
    (Scheme.Modules.pullbackCongr (imageIsoOfIsClosedImmersion_hom_subschemeι p W)).app L ≪≫
    ((Scheme.Modules.pullbackComp W.subschemeι p).app L).symm

/-- **The component rule of `p^*ℒ` and the transported component rule of `ℒ` agree in the Chow
group of each integral component.**

The chosen section on the image component pulls back to a nonzero section of the pullback
module, whose divisor cycle pushes forward to the chosen one by Stacks 02ST; the pullback module
is isomorphic to the restriction of `p^*ℒ`, which does not move the divisor cycle; and the
divisor cycles of two nonzero sections of one module have the same class, by Stacks 02SJ (2). -/
theorem rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt)) :
    RationallyEquivalent C (W.subschemeι ≫ sX) k
      (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L) W hW hDim)
      (pullbackComponentRule C sX sY p hp k (firstChernComponentCycleRule C sY k L) W hW hDim) := by
  classical
  -- the two components and the isomorphism between them
  have hWi : IsIntegral W.subscheme := hW
  have hVi : IsIntegral (W.map p).subscheme := isIntegral_subscheme_map p W hW
  have _ : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sX)
  have hDim' : schemeDeltaDimension C ((W.map p).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt) :=
    schemeDeltaDimension_subscheme_map C sX sY p hp k W hW hDim
  have _ : IsLocallyNoetherian (W.map p).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((W.map p).subschemeι ≫ sY)
  set r := (imageIsoOfIsClosedImmersion p W).hom with hrdef
  have hr : r ≫ ((W.map p).subschemeι ≫ sY) = W.subschemeι ≫ sX :=
    imageIsoOfIsClosedImmersion_hom_comp_base C sX sY p hp W
  -- the two modules
  set N : (W.map p).subscheme.Modules :=
    (Scheme.Modules.pullback (W.map p).subschemeι).obj L with hNdef
  have hNinv : AlgebraicGeometry.SheafOfModules.IsInvertible (W.map p).subscheme.presheaf
      (W.map p).subscheme.ringCatSheaf.2 N := isInvertible_presheaf_modulePullback L _
  have hNinv' : AlgebraicGeometry.SheafOfModules.IsInvertible (W.map p).subscheme.sheaf.obj
      (W.map p).subscheme.ringCatSheaf.property N := hNinv
  have hMinv : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.presheaf
      W.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback W.subschemeι).obj ((Scheme.Modules.pullback p).obj L)) :=
    isInvertible_presheaf_modulePullback ((Scheme.Modules.pullback p).obj L) _
  -- the section chosen on the image component, and its pullback
  set σ := (exists_ne_zero_genericStalk
    (isTrivializedNear_of_isInvertible N (genericPoint (W.map p).subscheme))).choose with hσdef
  have hσ : σ ≠ 0 := (exists_ne_zero_genericStalk
    (isTrivializedNear_of_isInvertible N (genericPoint (W.map p).subscheme))).choose_spec
  have hσbasis : IsStalkBasis N (genericPoint (W.map p).subscheme) σ :=
    isStalkBasis_genericPoint_of_ne_zero (W.map p).subscheme N hσ
  set τ := genericStalkPullback r N σ with hτdef
  have hτbasis : IsStalkBasis ((Scheme.Modules.pullback r).obj N)
      (genericPoint W.subscheme) τ := hσbasis.genericStalkPullback
  have hRinv : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.presheaf
      W.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback r).obj N) :=
    isInvertible_presheaf_modulePullback N r
  have hτ : τ ≠ 0 :=
    hτbasis.ne_zero
      (exists_ne_zero_genericStalk_of_isInvertible ((Scheme.Modules.pullback r).obj N))
  -- the transported section of the restriction of `p^*ℒ`
  set e := imageModuleIso p L W with hedef
  set t := stalkLinearMap ((Scheme.Modules.pullback r).obj N)
    ((Scheme.Modules.pullback W.subschemeι).obj ((Scheme.Modules.pullback p).obj L)) e.hom
    (genericPoint W.subscheme) τ with htdef
  have ht : t ≠ 0 := fun h =>
    hτ ((bijective_stalkLinearMap _ _ e.hom (genericPoint W.subscheme)).1
      (h.trans (map_zero _).symm))
  -- Step 1: Stacks 02SJ (2) — the rule's class is the class of the divisor of `t`
  have hstep1 : (QuotientAddGroup.mk
        (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L) W hW hDim) :
      chowGroup C (W.subschemeι ≫ sX) k) =
      QuotientAddGroup.mk (chernComponentCycle C (W.subschemeι ≫ sX) hDim
        (fun x => isTrivializedNear_of_isInvertible _ x) t) :=
    (firstChernComponentClass_eq_mk C sX k ((Scheme.Modules.pullback p).obj L) W hW
      hDim).symm.trans
      (firstChernComponentClass_eq_mk_of_ne_zero C sX k ((Scheme.Modules.pullback p).obj L) W
        hDim ht)
  -- Step 2: the module isomorphism does not move the divisor cycle
  have hstep2 : chernComponentCycle C (W.subschemeι ≫ sX) hDim
        (fun x => isTrivializedNear_of_isInvertible _ x) t =
      chernComponentCycle C (W.subschemeι ≫ sX) hDim
        (fun x => isTrivializedNear_of_isInvertible _ x) τ :=
    chernComponentCycle_mapStalkLinearMap C (W.subschemeι ≫ sX) hDim _ _ e.hom
      (fun x => isTrivializedNear_of_isInvertible _ x)
      (fun x => isTrivializedNear_of_isInvertible _ x) τ
  -- Step 3: Stacks 02ST — the divisor of `τ` pushes forward to the divisor of `σ`
  have hstep3 : chernComponentCycle C (W.subschemeι ≫ sX) hDim
        (fun x => isTrivializedNear_of_isInvertible _ x) τ =
      pullbackComponentRule C sX sY p hp k (firstChernComponentCycleRule C sY k L) W hW hDim := by
    let _ : Algebra (W.map p).subscheme.functionField W.subscheme.functionField :=
      (dominantFunctionFieldMap r).toAlgebra
    have hdeg :
        Module.finrank (W.map p).subscheme.functionField W.subscheme.functionField = 1 :=
      (finrank_functionField_eq_residueDegree r).trans
        (residueDegree_eq_one_of_isClosedImmersion r _)
    have h02ST := properPushforward_meromorphicDivisorCycleOfInvertible C (W.subschemeι ≫ sX)
      ((W.map p).subschemeι ≫ sY) hDim hDim' r hr N σ hσ
    rw [hdeg, Nat.cast_one, one_smul] at h02ST
    -- proper pushforward sees only the underlying algebraic cycle, which the two gradings share
    have key : properPushforward C (W.subschemeι ≫ sX) ((W.map p).subschemeι ≫ sY) r hr k
          (chernComponentCycle C (W.subschemeι ≫ sX) hDim
            (fun x => isTrivializedNear_of_isInvertible _ x) τ) =
        chernComponentCycle C ((W.map p).subschemeι ≫ sY) hDim'
          (fun x => isTrivializedNear_of_isInvertible _ x) σ :=
      Subtype.ext <|
        (val_properPushforward_eq_of_val_eq C _ _ r hr _ _
          (val_meromorphicDivisorCycle_eq_chernComponentCycle C _ hDim _ τ).symm).trans <|
        (congrArg Subtype.val h02ST).trans
          (val_meromorphicDivisorCycle_eq_chernComponentCycle C _ hDim' _ σ)
    have hid := congrFun (properPushforward_comp C (W.subschemeι ≫ sX)
      ((W.map p).subschemeι ≫ sY) (W.subschemeι ≫ sX) r (imageIsoOfIsClosedImmersion p W).inv hr
      (imageIsoOfIsClosedImmersion_inv_comp_base C sX sY p hp W) k)
      (chernComponentCycle C (W.subschemeι ≫ sX) hDim
        (fun x => isTrivializedNear_of_isInvertible _ x) τ)
    rw [properPushforward_congr C (W.subschemeι ≫ sX) (W.subschemeι ≫ sX)
      (r ≫ (imageIsoOfIsClosedImmersion p W).inv) (𝟙 W.subscheme)
      (imageIsoOfIsClosedImmersion p W).hom_inv_id _ (Category.id_comp _) k,
      properPushforward_id, Function.comp_apply, key] at hid
    exact hid.symm
  exact QuotientAddGroup.eq_iff_sub_mem.1
    (hstep1.trans (congrArg QuotientAddGroup.mk (hstep2.trans hstep3)))

/-- **Stacks 02SU for a closed immersion.** Let `p : X ⟶ Y` be a closed immersion of schemes
locally of finite type over the base scheme of chapter 42, and let `ℒ` be an invertible
`𝒪_Y`-module. Then for every `(k+1)`-cycle `α` on `X`

  `p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`  in  `A_k(Y)`.

No hypothesis is carried: the component rules on both sides are those of the invertible modules
themselves, and the instance of Stacks 02S2 that `Stacks.Chow.properChowPushforward` requires is
discharged, `p` being a closed immersion.

The cap product is built from a component rule which chooses a meromorphic section on each
integral component, and the rules of `p^*ℒ` on `X` and of `ℒ` on `Y` choose independently, so
they are *not* compatible as cycles. They are compatible in the Chow group of each component, by
Stacks 02SJ (2), and `Stacks.Chow.firstChernClassCap_congr` propagates that to the cap
products. -/
theorem properChowPushforward_firstChernClassCapOfInvertible (α : CycleGroup C sX (k + 1)) :
    letI := isInvertible_presheaf_modulePullback L p
    properChowPushforward C sX sY p hp k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion p C sX sY hp k)
        (firstChernClassCapOfInvertible C sX k ((Scheme.Modules.pullback p).obj L) α) =
      firstChernClassCapOfInvertible C sY k L
        (properPushforward C sX sY p hp (k + 1) α) := by
  have hcongr := firstChernClassCap_congr C sX k
    (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L))
    (pullbackComponentRule C sX sY p hp k (firstChernComponentCycleRule C sY k L))
    (fun W hW hDim =>
      rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule C sX sY p hp k L
        W hW hDim) α
  rw [show firstChernClassCapOfInvertible C sX k ((Scheme.Modules.pullback p).obj L) α =
      firstChernClassCap C sX k
        (firstChernComponentCycleRule C sX k ((Scheme.Modules.pullback p).obj L)) α from rfl,
    hcongr]
  exact properChowPushforward_firstChernClassCap_pullbackComponentRule C sX sY p hp k
    (firstChernComponentCycleRule C sY k L) α

end Stacks.Chow

end
