module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationDimensionBounds
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointSplittingConstruction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivityClosed
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExactMiddle
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplement
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.WeaklyAssociatedLocallyFinite
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.EssentiallyFiniteType
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Connectedness of the formal locus

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let
`T = V(I) ∖ V(𝔞)`, the formal locus inside `U`. Stacks 0EG5 asserts that `T` is empty or
connected as soon as `A` is `I`-adically complete with a dualizing complex, a dimension bound
holds along the components of `Spec(A)` not inside `V(I)`, and every nonempty open of `Spec(A)`
containing `T` is connected.

The source's proof reduces to the case of a reduced ring and then applies Stacks 0EG2 to the
structure sheaf of `U`: that proposition identifies the sections of `𝒪_U` on arbitrarily small
neighbourhoods of `T` with the formal sections of `𝒪_U` along `T`. A disconnection of `T` would
produce a nontrivial idempotent among the formal sections, hence a nonconstant function on some
neighbourhood of `T`, hence a disconnection of that neighbourhood.

## Main definitions

* `Stacks.Algebraization.ConnectednessComparisonInput` — the one hypothesis that
  `Stacks.Algebraization.isIso_comparisonMap` (Stacks 0EG2) still carries, quantified over every
  Noetherian ring and every pair of ideals so that it survives the reduction step.

## Main results

* `Stacks.Algebraization.eq_empty_or_isConnected_zeroLocus_sdiff` — **Stacks 0EG5**.
* `Stacks.Algebraization.isAdicComplete_map_quotient` — a quotient of an `I`-adically complete
  Noetherian ring is `I`-adically complete.
* `Stacks.Algebraization.exists_isDualizingComplex_quotient` — Stacks 0A7K for a quotient.

## Implementation notes

The dimension `dim((A/𝔭)_𝔮)` of hypothesis (2) is written as the Krull dimension of
`(A_𝔮)/(𝔭 A_𝔮)`, the spelling the rest of this subtree uses; a private order isomorphism
identifies it with `Stacks.Algebraization.closureLocalDimension`, the interval of primes between
`𝔭` and `𝔮`, which is the spelling condition (2) of Stacks 0EG2 is phrased with. "Minimal prime"
is `minimalPrimes A`.

The idempotent of the source's proof is realized concretely: a disconnection `T ⊆ P ∪ Q` gives
the two opens `U₁ = (T ∖ P)ᶜ` and `U₂ = (T ∖ Q)ᶜ` of `U`, which cover `U` and whose
intersection misses `T`. The quotient `𝒪_U / Iⁿ 𝒪_U` has no nonzero sections off the support of
`I · 𝒪_U`, so the section `1` on `U₁` and the section `0` on `U₂` agree on the overlap and glue;
the resulting formal section is the idempotent. Realizing it on a neighbourhood `V` of `T`
produces `e ∈ Γ(V, 𝒪)` whose germ along `T` is `1` on `P` and `0` on `Q`, by Krull's
intersection theorem, and the two opens where the germ of `e` is `1` and where it is `0`
disconnect a neighbourhood of `T`.

The single field of `Stacks.Algebraization.ConnectednessComparisonInput` is the one hypothesis
Stacks 0EG2 still carries, and it is neither this conclusion nor that of Stacks 0EG2: Stacks
0EIF applies only to a module satisfying its third condition. It is quantified over all
Noetherian rings because the proof below applies Stacks 0EG2 to the reduction of `A`, not to
`A`. The two other hypotheses of Stacks 0EG2 are supplied here, not assumed: the middle clause
of Stacks 0H48 is `Stacks.Algebraization.middleComparisonOfShortExact`, and the short exact
sequence isolating one associated point off `V(I)` is
`Stacks.Algebraization.associatedPointSplitting`.

The dualizing complex `K` lives in the standard model of the derived category,
`CategoryTheory.HasDerivedCategory.standard`, which is made a local instance at a raised
priority. Another `HasDerivedCategory` instance, whose model has its morphisms one universe
lower, is reachable through these imports and wins at the default priority; the raised priority
is what keeps `K` in the same model as `Stacks.Algebraization.BootstrapHypotheses` and as
Stacks 0A7K (`Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType`), which the
reduction step applies to it.

## References

* [Stacks Project, Tag 0EG5](https://stacks.math.columbia.edu/tag/0EG5)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA)
* [Stacks Project, Tag 0A7K](https://stacks.math.columbia.edu/tag/0A7K)
* [Stacks Project, Tag 0EME](https://stacks.math.columbia.edu/tag/0EME)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.Ample (unitModule)

open Stacks.LocalCohomology

/-! ### The structure sheaf as a module over itself -/

private instance isCoherent_unitModule (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (unitModule X).IsCoherent :=
  Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit

/-! ### Krull's intersection theorem for the structure sheaf -/

/-- **Krull's intersection theorem along the support of an ideal sheaf.** A function on an affine
open of a locally Noetherian scheme which lies in every power of a quasi-coherent ideal sheaf has
vanishing germ at every point of the support of that ideal sheaf.

By `Ideal.mem_iInf_smul_pow_eq_bot_iff` the function is fixed by some `r` in the ideal; at a point
of the support `r` lies in the maximal ideal of the local ring, so `1 - r` is a unit there and
kills the germ. -/
private lemma germ_eq_zero_of_forall_mem_pow_smul {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (W : X.affineOpens) (s : Γ(X, W.1))
    (hs : ∀ n : ℕ, s ∈ (J.ideal W) ^ n • (⊤ : Submodule Γ(X, W.1) Γ(X, W.1)))
    {x : X} (hx : x ∈ W.1) (hxJ : x ∈ J.support) :
    X.presheaf.germ W.1 x hx s = 0 := by
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (J.ideal W) s).mp
    ((Submodule.mem_iInf _).mpr hs)
  have hnr : ¬ IsUnit (X.presheaf.germ W.1 x hx r.1) := by
    have h := (J.mem_support_iff_of_mem (U := W) hx).mp hxJ
    intro hu
    exact (X.mem_zeroLocus_iff _ x).mp h r.1 r.2 ((X.mem_basicOpen _ x hx).mpr hu)
  have hunit : IsUnit (1 - X.presheaf.germ W.1 x hx r.1) :=
    (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left hnr
  have heq : (1 - X.presheaf.germ W.1 x hx r.1) * X.presheaf.germ W.1 x hx s = 0 := by
    rw [sub_mul, one_mul, ← map_mul]
    show X.presheaf.germ W.1 x hx s - X.presheaf.germ W.1 x hx (r.1 • s) = 0
    rw [hr, sub_self]
  exact hunit.mul_left_cancel (by simpa using heq :
    (1 - X.presheaf.germ W.1 x hx r.1) * X.presheaf.germ W.1 x hx s =
      (1 - X.presheaf.germ W.1 x hx r.1) * 0)

/-- A function on an affine open killed by `𝒪 ⟶ 𝒪 / Jⁿ 𝒪` for every `n` lies in every power of
the ideal sheaf there. -/
private lemma mem_pow_smul_of_adicProj_app_eq_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (W : X.affineOpens) (s : ToType Γ(unitModule X, W.1))
    (hs : ∀ n : ℕ, (adicProj J (unitModule X) (op n)).app W.1 s = 0) (n : ℕ) :
    (s : Γ(X, W.1)) ∈ (J.ideal W) ^ n • (⊤ : Submodule Γ(X, W.1) Γ(X, W.1)) := by
  have h := hs n
  rw [adicProj_app_apply_eq_zero_iff, idealPowerMultiple_toSubmodule_obj_affine] at h
  exact h

/-- Restriction of the unit function is the unit function. This is not formal: the restriction
maps of `Stacks.Algebraization.unitModule` are only additive, and it is their identification with
the ring restriction maps that preserves `1`. -/
private lemma unitModule_map_one {X : Scheme.{u}} {U V : X.Opens} (i : U ⟶ V) :
    (unitModule X).presheaf.map i.op (1 : Γ(X, V)) = (1 : Γ(X, U)) := by
  have h : X.presheaf.map i.op (1 : Γ(X, V)) = (1 : Γ(X, U)) := map_one _
  exact h

/-! ### Comparing germs through the adic quotients -/

/-- The locus where two sections of the structure sheaf have equal germ is open. -/
private lemma isOpen_germ_eq {X : Scheme.{u}} (V : X.Opens) (s t : Γ(X, V)) :
    IsOpen {x : X | ∃ hx : x ∈ V,
      X.presheaf.germ V x hx s = X.presheaf.germ V x hx t} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨hx, hst⟩
  obtain ⟨W, hxW, i, j, heq⟩ := X.presheaf.germ_eq x hx hx s t hst
  refine ⟨W, ?_, W.2, hxW⟩
  intro y hy
  refine ⟨(leOfHom i) hy, ?_⟩
  have h := congrArg (X.presheaf.germ W y hy) heq
  simpa only [TopCat.Presheaf.germ_res_apply] using h

/-- Restriction commutes with a morphism of modules. -/
private lemma map_app {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) {U V : X.Opens}
    (i : U ⟶ V) (s : ToType Γ(M, V)) :
    N.presheaf.map i.op (f.app V s) = f.app U (M.presheaf.map i.op s) :=
  (congrArg (fun g => g s) (f.mapPresheaf.naturality i.op)).symm

/-- Iterated restriction is restriction. -/
private lemma map_map {X : TopCat.{u}} (P : TopCat.Presheaf Ab.{u} X)
    {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) (s : ToType (P.obj (op W))) :
    P.map (homOfLE hUV).op (P.map (homOfLE hVW).op s) =
      P.map (homOfLE (hUV.trans hVW)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Two sections of the structure sheaf with the same image in `𝒪 / Jⁿ 𝒪` for every `n` have the
same germ at every point of the support of `J`. -/
private lemma germ_eq_of_forall_adicProj_app_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (W : X.affineOpens) (s t : Γ(X, W.1))
    (h : ∀ n : ℕ, (adicProj J (unitModule X) (op n)).app W.1 s =
      (adicProj J (unitModule X) (op n)).app W.1 t)
    {x : X} (hx : x ∈ W.1) (hxJ : x ∈ J.support) :
    X.presheaf.germ W.1 x hx s = X.presheaf.germ W.1 x hx t := by
  have hz : ∀ n : ℕ, (adicProj J (unitModule X) (op n)).app W.1 (s - t) = 0 := by
    intro n
    have hms : (adicProj J (unitModule X) (op n)).app W.1 (s - t) =
        (adicProj J (unitModule X) (op n)).app W.1 s -
          (adicProj J (unitModule X) (op n)).app W.1 t :=
      map_sub (ConcreteCategory.hom ((adicProj J (unitModule X) (op n)).app W.1))
        (s : ToType Γ(unitModule X, W.1)) (t : ToType Γ(unitModule X, W.1))
    rw [hms, h n, sub_self]
  have hg := germ_eq_zero_of_forall_mem_pow_smul J W (s - t)
    (mem_pow_smul_of_adicProj_app_eq_zero J W (s - t) hz) hx hxJ
  rw [← sub_eq_zero, ← map_sub]
  exact hg

/-- Two sections of the structure sheaf defined on two opens, both induced by one compatible
family of sections of the quotients `𝒪 / Jⁿ 𝒪` on the whole space, have the same germ at every
common point of the support of `J`. -/
private lemma germ_eq_of_forall_res_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData)
    (f : ∀ n : ℕᵒᵖ, ToType Γ((adicQuotientSystem J (unitModule X)).obj n, ⊤))
    (V₁ V₂ : X.Opens) (s₁ : Γ(X, V₁)) (s₂ : Γ(X, V₂))
    (h₁ : ∀ n : ℕᵒᵖ,
      ((adicQuotientSystem J (unitModule X)).obj n).presheaf.map
        (homOfLE (le_top (a := V₁))).op (f n) = (adicProj J (unitModule X) n).app V₁ s₁)
    (h₂ : ∀ n : ℕᵒᵖ,
      ((adicQuotientSystem J (unitModule X)).obj n).presheaf.map
        (homOfLE (le_top (a := V₂))).op (f n) = (adicProj J (unitModule X) n).app V₂ s₂)
    {x : X} (hx₁ : x ∈ V₁) (hx₂ : x ∈ V₂) (hxJ : x ∈ J.support) :
    X.presheaf.germ V₁ x hx₁ s₁ = X.presheaf.germ V₂ x hx₂ s₂ := by
  obtain ⟨W, hW, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V₁ ⊓ V₂ from ⟨hx₁, hx₂⟩)
  have hW₁ : W ≤ V₁ := hWle.trans inf_le_left
  have hW₂ : W ≤ V₂ := hWle.trans inf_le_right
  have hside : ∀ (V : X.Opens) (hWV : W ≤ V) (s : Γ(X, V)),
      (∀ n : ℕᵒᵖ, ((adicQuotientSystem J (unitModule X)).obj n).presheaf.map
        (homOfLE (le_top (a := V))).op (f n) = (adicProj J (unitModule X) n).app V s) →
      ∀ n : ℕ, (adicProj J (unitModule X) (op n)).app W
          ((unitModule X).presheaf.map (homOfLE hWV).op s) =
        ((adicQuotientSystem J (unitModule X)).obj (op n)).presheaf.map
          (homOfLE (le_top (a := W))).op (f (op n)) := by
    intro V hWV s h n
    calc _ = ((adicQuotientSystem J (unitModule X)).obj (op n)).presheaf.map (homOfLE hWV).op
            ((adicProj J (unitModule X) (op n)).app V s) := (map_app _ _ _).symm
      _ = ((adicQuotientSystem J (unitModule X)).obj (op n)).presheaf.map (homOfLE hWV).op
            (((adicQuotientSystem J (unitModule X)).obj (op n)).presheaf.map
              (homOfLE (le_top (a := V))).op (f (op n))) := congrArg _ (h (op n)).symm
      _ = _ := map_map _ _ _ _
  have hq := fun n => (hside V₁ hW₁ s₁ h₁ n).trans (hside V₂ hW₂ s₂ h₂ n).symm
  have hg := germ_eq_of_forall_adicProj_app_eq J ⟨W, hW⟩
    (X.presheaf.map (homOfLE hW₁).op s₁) (X.presheaf.map (homOfLE hW₂).op s₂) hq hxW hxJ
  simpa only [TopCat.Presheaf.germ_res_apply] using hg

/-! ### Gluing the idempotent -/

/-- The section `1` of `𝒪 / Jⁿ 𝒪` over an open disjoint from the support of `J` is zero: that
quotient has no nonzero sections there at all. -/
private lemma adicProj_app_one_eq_zero_of_disjoint_support {X : Scheme.{u}}
    (J : X.IdealSheafData) (n : ℕ) {V : X.Opens}
    (hV : Disjoint (V : Set X) (J.support : Set X)) :
    (adicProj J (unitModule X) (op n)).app V (1 : Γ(X, V)) = 0 :=
  (subsingleton_adicQuotientSystem_sections_of_le_compl_support J (unitModule X) n
    (fun _ hx => Set.disjoint_left.mp hV hx)).elim _ _

/-- **The idempotent of the source's proof, over a two-open cover.** If `V₁ ⊔ V₂` is everything
and `1` dies in `𝒪 / Jⁿ 𝒪` over `V₁ ⊓ V₂`, the section `1` over `V₁` and the section `0` over
`V₂` glue to a unique global section of `𝒪 / Jⁿ 𝒪`. -/
private lemma existsUnique_glue_one_zero {X : Scheme.{u}} {Q : X.Modules}
    (q : unitModule X ⟶ Q) (V₁ V₂ : X.Opens) (hcover : V₁ ⊔ V₂ = ⊤)
    (hq : q.app (V₁ ⊓ V₂) (1 : Γ(X, V₁ ⊓ V₂)) = 0) :
    ∃! s : ToType Γ(Q, ⊤),
      Q.presheaf.map (homOfLE (le_top (a := V₁))).op s = q.app V₁ (1 : Γ(X, V₁)) ∧
      Q.presheaf.map (homOfLE (le_top (a := V₂))).op s = 0 := by
  classical
  let W : Bool → X.Opens := fun b => if b then V₁ else V₂
  let sf : ∀ b, ToType Γ(Q, W b) := fun b =>
    if h : b = true then q.app (W b) (1 : Γ(X, W b)) else 0
  have hW : iSup W = ⊤ := by simpa [W, iSup_bool_eq, sup_comm] using hcover
  have hcompat : TopCat.Presheaf.IsCompatible Q.presheaf W sf := by
    intro b c
    cases b <;> cases c
    · rfl
    · dsimp [sf, W]
      calc _ = 0 := map_zero _
        _ = q.app (V₂ ⊓ V₁) (1 : Γ(X, V₂ ⊓ V₁)) := by rw [inf_comm V₂ V₁]; exact hq.symm
        _ = _ := by
            simpa only [unitModule_map_one] using
              (map_app q (Opens.infLERight V₂ V₁) (1 : Γ(X, V₁))).symm
    · dsimp [sf, W]
      calc _ = q.app (V₁ ⊓ V₂) (1 : Γ(X, V₁ ⊓ V₂)) := by
            simpa only [unitModule_map_one] using
              map_app q (Opens.infLELeft V₁ V₂) (1 : Γ(X, V₁))
        _ = 0 := hq
        _ = _ := (map_zero _).symm
    · rfl
  let sh : TopCat.Sheaf Ab X := ⟨Q.presheaf, Scheme.Modules.isSheaf Q⟩
  obtain ⟨s, hs, huniq⟩ := sh.existsUnique_gluing' W ⊤ (fun _ => homOfLE le_top)
    hW.symm.le sf hcompat
  refine ⟨s, ⟨?_, ?_⟩, ?_⟩
  · simpa [W, sf] using hs true
  · simpa [W, sf] using hs false
  · rintro t ⟨htV₁, htV₂⟩
    refine huniq t fun b => ?_
    cases b
    · simpa [W, sf] using htV₂
    · simpa [W, sf] using htV₁

/-- **The formal separator.** For a two-open cover `V₁ ⊔ V₂ = ⊤` whose overlap misses the
support of `J`, the sections `1` on `V₁` and `0` on `V₂` glue, compatibly in `n`, to a
compatible family of sections of the quotients `𝒪 / Jⁿ 𝒪` on the whole space. -/
private lemma exists_formal_separator {X : Scheme.{u}} (J : X.IdealSheafData)
    (V₁ V₂ : X.Opens) (hcover : V₁ ⊔ V₂ = ⊤)
    (hdisj : Disjoint ((V₁ ⊓ V₂ : X.Opens) : Set X) (J.support : Set X)) :
    ∃ f : ∀ n : ℕᵒᵖ, ToType Γ((adicQuotientSystem J (unitModule X)).obj n, ⊤),
      (∀ (m n : ℕᵒᵖ) (h : m ⟶ n),
        ((adicQuotientSystem J (unitModule X)).map h).app ⊤ (f m) = f n) ∧
      ∀ n : ℕᵒᵖ,
        (((adicQuotientSystem J (unitModule X)).obj n).presheaf.map
            (homOfLE (le_top (a := V₁))).op (f n) =
          (adicProj J (unitModule X) n).app V₁ (1 : Γ(X, V₁))) ∧
        ((adicQuotientSystem J (unitModule X)).obj n).presheaf.map
            (homOfLE (le_top (a := V₂))).op (f n) = 0 := by
  classical
  have hex (n : ℕᵒᵖ) := existsUnique_glue_one_zero (adicProj J (unitModule X) n) V₁ V₂ hcover
    (adicProj_app_one_eq_zero_of_disjoint_support J n.unop hdisj)
  choose f hf huniq using hex
  refine ⟨f, ?_, hf⟩
  intro m n h
  refine huniq n _ ⟨?_, ?_⟩
  · rw [map_app, (hf m).1]
    exact congrArg (fun φ : unitModule X ⟶ (adicQuotientSystem J (unitModule X)).obj n =>
      φ.app V₁ (1 : Γ(X, V₁))) (adicProj_comp_map J (unitModule X) h)
  · rw [map_app, (hf m).2, map_zero]

/-! ### The connectedness criterion -/

/-- **The geometric heart of Stacks 0EG5.** Let `J` be a quasi-coherent ideal sheaf on a locally
Noetherian scheme `X`. Suppose every compatible family of sections of the quotients
`𝒪 / Jⁿ 𝒪` on `X` is, on some open neighbourhood `V` of the support of `J`, the reduction of an
honest function on `V`; and suppose every open neighbourhood of that support is preconnected.
Then the support of `J` is preconnected.

This is the "nontrivial idempotent" paragraph of the source. A disconnection of the support
produces, by `Stacks.Algebraization.exists_formal_separator`, a compatible family which is `1`
on one side and `0` on the other; realizing it as a function `e` on a neighbourhood `V` of the
support, Krull's intersection theorem forces the germ of `e` along the support to be the germ of
`1` on one side and the germ of `0` on the other, and the two opens where those germs are
attained disconnect a neighbourhood of the support. -/
private lemma isPreconnected_support_of_realizable {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData)
    (halg : ∀ f : ∀ n : ℕᵒᵖ, ToType Γ((adicQuotientSystem J (unitModule X)).obj n, ⊤),
      (∀ (m n : ℕᵒᵖ) (h : m ⟶ n),
        ((adicQuotientSystem J (unitModule X)).map h).app ⊤ (f m) = f n) →
      ∃ (V : X.Opens) (e : ToType Γ(unitModule X, V)), (J.support : Set X) ⊆ (V : Set X) ∧
        ∀ n : ℕᵒᵖ,
          ((adicQuotientSystem J (unitModule X)).obj n).presheaf.map
              (homOfLE (le_top (a := V))).op (f n) =
            (adicProj J (unitModule X) n).app V e)
    (hopen : ∀ V : X.Opens, (J.support : Set X) ⊆ (V : Set X) →
      _root_.IsPreconnected (V : Set X)) :
    _root_.IsPreconnected (J.support : Set X) := by
  classical
  by_contra hT
  unfold _root_.IsPreconnected at hT
  push Not at hT
  obtain ⟨P, Q, hP, hQ, hcover, hPne, hQne, hPQ⟩ := hT
  let V₁ : X.Opens := ⟨((J.support : Set X) \ P)ᶜ,
    (J.support.2.inter hP.isClosed_compl).isOpen_compl⟩
  let V₂ : X.Opens := ⟨((J.support : Set X) \ Q)ᶜ,
    (J.support.2.inter hQ.isClosed_compl).isOpen_compl⟩
  have hkey : ∀ (R : Set X) {x : X}, x ∈ (J.support : Set X) →
      (x ∉ (J.support : Set X) \ R ↔ x ∈ R) := fun R _ hx => by simp [hx]
  have hV : V₁ ⊔ V₂ = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    have hc := @hcover x
    show x ∉ (J.support : Set X) \ P ∨ x ∉ (J.support : Set X) \ Q
    simp only [Set.mem_sdiff, Set.mem_union] at hc ⊢
    tauto
  have hdisj : Disjoint ((V₁ ⊓ V₂ : X.Opens) : Set X) (J.support : Set X) := by
    refine Set.disjoint_left.mpr fun x hx hxJ => ?_
    have hxP : x ∈ P := (hkey P hxJ).mp hx.1
    have hxQ : x ∈ Q := (hkey Q hxJ).mp hx.2
    have hx' : x ∈ (J.support : Set X) ∩ (P ∩ Q) := ⟨hxJ, hxP, hxQ⟩
    simp only [hPQ, Set.mem_empty_iff_false] at hx'
  obtain ⟨f, hfnat, hf⟩ := exists_formal_separator J V₁ V₂ hV hdisj
  obtain ⟨V, e, hJV, he⟩ := halg f hfnat
  let E₁ : X.Opens := ⟨{x : X | ∃ hx : x ∈ V,
    X.presheaf.germ V x hx (e : Γ(X, V)) = X.presheaf.germ V x hx (1 : Γ(X, V))},
    isOpen_germ_eq V (e : Γ(X, V)) 1⟩
  let E₀ : X.Opens := ⟨{x : X | ∃ hx : x ∈ V,
    X.presheaf.germ V x hx (e : Γ(X, V)) = X.presheaf.germ V x hx (0 : Γ(X, V))},
    isOpen_germ_eq V (e : Γ(X, V)) 0⟩
  have h₁ : ∀ x : X, x ∈ J.support → x ∈ V₁ → x ∈ E₁ := by
    intro x hxJ hxV₁
    refine ⟨hJV hxJ, ?_⟩
    simpa only [map_one] using germ_eq_of_forall_res_eq J f V V₁ e (1 : Γ(X, V₁)) he
      (fun n => (hf n).1) (hJV hxJ) hxV₁ hxJ
  have h₀ : ∀ x : X, x ∈ J.support → x ∈ V₂ → x ∈ E₀ := by
    intro x hxJ hxV₂
    refine ⟨hJV hxJ, ?_⟩
    have hz : ∀ n : ℕᵒᵖ,
        ((adicQuotientSystem J (unitModule X)).obj n).presheaf.map
            (homOfLE (le_top (a := V₂))).op (f n) =
          (adicProj J (unitModule X) n).app V₂ (0 : Γ(X, V₂)) :=
      fun n => (hf n).2.trans (map_zero _).symm
    simpa only [map_zero] using
      germ_eq_of_forall_res_eq J f V V₂ e (0 : Γ(X, V₂)) he hz (hJV hxJ) hxV₂ hxJ
  have hJE : (J.support : Set X) ⊆ ((E₁ ⊔ E₀ : X.Opens) : Set X) := by
    intro x hx
    have hxu : x ∈ V₁ ⊔ V₂ := by rw [hV]; trivial
    exact (hxu : x ∈ V₁ ∨ x ∈ V₂).elim (fun h => Or.inl (h₁ x hx h)) fun h => Or.inr (h₀ x hx h)
  have hEdisj : Disjoint (E₁ : Set X) (E₀ : Set X) := by
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨hx, hxe⟩ ⟨_, hxe'⟩
    exact one_ne_zero (by simpa only [map_one, map_zero] using hxe.symm.trans hxe' :
      (1 : X.presheaf.stalk x) = 0)
  obtain ⟨x, hxJ, hxP⟩ := hPne
  obtain ⟨y, hyJ, hyQ⟩ := hQne
  have hxV₁ : x ∈ V₁ := (hkey P hxJ).mpr hxP
  have hyV₂ : y ∈ V₂ := (hkey Q hyJ).mpr hyQ
  obtain ⟨z, _, hz₁, hz₀⟩ := hopen (E₁ ⊔ E₀) hJE E₁ E₀ E₁.2 E₀.2 (by rfl)
    ⟨x, Or.inl (h₁ x hxJ hxV₁), h₁ x hxJ hxV₁⟩ ⟨y, Or.inr (h₀ y hyJ hyV₂), h₀ y hyJ hyV₂⟩
  exact Set.disjoint_left.mp hEdisj hz₁ hz₀

/-! ### The realization hypothesis from Stacks 0EG2 -/

/-- When the comparison map of Stacks 0EG2 is an isomorphism, every compatible family of
sections of `F / Iⁿ F` on `U` is realized by a function on a single neighbourhood of the formal
locus: the index category of those neighbourhoods is filtered, so every element of the colimit
is a section over one of them. -/
private lemma exists_realization_of_isIso_comparisonMap (A : Type u) [CommRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) [IsIso (comparisonMap A I a F)]
    (f : ∀ n : ℕᵒᵖ, ToType ((formalSections A I a F).obj n))
    (hf : ∀ (m n : ℕᵒᵖ) (h : m ⟶ n), (formalSections A I a F).map h (f m) = f n) :
    ∃ (V : OpensNearVanishing A I a) (e : ToType ((sectionsNearVanishing A I a F).obj V)),
      ∀ n : ℕ,
        ((quotientSystemNearVanishing A I a F).obj (op n)).presheaf.map
            (homOfLE (show V.openSet ≤ ⊤ from le_top)).op (f (op n)) =
          (adicProj (idealSheafNearVanishing A I a) F (op n)).app V.openSet e := by
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget Ab.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  let D := formalSections A I a F
  let t : (D ⋙ forget Ab).sections := ⟨f, fun {m n} h => hf m n h⟩
  let E := Types.isLimitEquivSections (isLimitOfPreserves (forget Ab) (limit.isLimit D))
  let z : ToType (limit D) := E.symm t
  have hz : ∀ n : ℕᵒᵖ, limit.π D n z = f n := fun n =>
    congrArg (fun t : (D ⋙ forget Ab).sections => t.1 n) (E.apply_symm_apply t)
  let g := comparisonMap A I a F
  obtain ⟨V, e, he⟩ := Concrete.colimit_exists_rep (sectionsNearVanishing A I a F) (inv g z)
  have hg : g (colimit.ι (sectionsNearVanishing A I a F) V e) = z := by
    rw [he]
    exact congrArg (fun φ => φ z) (IsIso.inv_hom_id g)
  refine ⟨V, e, fun n => ?_⟩
  have hn := congrArg (fun φ => φ e) (comparisonMap_restrict A I a F V n)
  change ((quotientSystemNearVanishing A I a F).obj (op n)).presheaf.map
    (homOfLE (show V.openSet ≤ ⊤ from le_top)).op (limit.π D (op n)
      (g (colimit.ι (sectionsNearVanishing A I a F) V e))) = _ at hn
  rwa [hg, hz] at hn

/-! ### Transporting the dimension hypothesis -/

/-- The dimension `dim((A/𝔭)_𝔮)` of hypothesis (2) of Stacks 0EG5 is
`Stacks.Algebraization.closureLocalDimension`, the dimension of the interval of primes between
`𝔭` and `𝔮`, which is the invariant condition (2) of Stacks 0EG2 is phrased with. -/
private lemma closureLocalDimension_eq_ringKrullDim_localizedQuotient {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) :
    closureLocalDimension A p q =
      ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) :=
  (Order.krullDim_eq_of_orderIso (primeSpectrumLocalizedQuotientOrderIso p q)).symm

/-- **The dimension of the interval of primes between `𝔭` and `𝔮` is the Krull dimension of the
localized quotient `(A_𝔮)/𝔭A_𝔮`.** The primes of that quotient are exactly the primes of `A`
between `𝔭` and `𝔮`, so both sides are the dimension of one and the same poset. This is the
invariant that condition (2) of Stacks 0EG2 is phrased with, read as a ring dimension. -/
public alias closureLocalDimension_eq_ringKrullDim_quotient_localizationAtPrime :=
  closureLocalDimension_eq_ringKrullDim_localizedQuotient

/-- The interval of primes between two primes is unchanged by passing to the reduction. -/
private lemma closureLocalDimension_quotientMk {A : Type u} [CommRing A]
    (e : PrimeSpectrum (A ⧸ nilradical A) ≃o PrimeSpectrum A)
    (he : ∀ r : PrimeSpectrum (A ⧸ nilradical A),
      (e r).asIdeal = r.asIdeal.comap (Ideal.Quotient.mk (nilradical A)))
    (p q : PrimeSpectrum (A ⧸ nilradical A)) :
    closureLocalDimension (A ⧸ nilradical A) p q = closureLocalDimension A (e p) (e q) := by
  have hmono : ∀ r s : PrimeSpectrum (A ⧸ nilradical A),
      r.asIdeal ≤ s.asIdeal ↔ (e r).asIdeal ≤ (e s).asIdeal := by
    intro r s
    rw [he, he]
    exact (Ideal.comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective _ _).symm
  let e' : {r : PrimeSpectrum (A ⧸ nilradical A) //
        p.asIdeal ≤ r.asIdeal ∧ r.asIdeal ≤ q.asIdeal} ≃o
      {r : PrimeSpectrum A // (e p).asIdeal ≤ r.asIdeal ∧ r.asIdeal ≤ (e q).asIdeal} :=
    { toFun := fun r => ⟨e r.1, (hmono p r.1).mp r.2.1, (hmono r.1 q).mp r.2.2⟩
      invFun := fun r => ⟨e.symm r.1, by
          refine ⟨(hmono p (e.symm r.1)).mpr ?_, (hmono (e.symm r.1) q).mpr ?_⟩
          · simpa only [e.apply_symm_apply] using r.2.1
          · simpa only [e.apply_symm_apply] using r.2.2⟩
      left_inv := fun r => Subtype.ext (e.symm_apply_apply r.1)
      right_inv := fun r => Subtype.ext (e.apply_symm_apply r.1)
      map_rel_iff' := by
        intro r s
        show e r.1 ≤ e s.1 ↔ r.1 ≤ s.1
        exact e.le_iff_le }
  exact Order.krullDim_eq_of_orderIso e'

/-! ### Reduction to a reduced ring -/

/-- **A quotient of an `I`-adically complete Noetherian ring is `I`-adically complete.** The
ideal `I` lies in the Jacobson radical, so Krull's intersection theorem makes the cyclic module
`A/J` separated for the `I`-adic topology, and a finite separated module over a complete ring is
complete. -/
@[ega "0 7.3.6" "Cyclic modules A/J",
  ega "0 7.8.1" "special case",
  ega "IV 18.5.16" "quotient algebras A/K"]
public lemma isAdicComplete_map_quotient (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) [IsAdicComplete I A] :
    IsAdicComplete (I.map (algebraMap A (A ⧸ J))) (A ⧸ J) := by
  have hI : I ≤ Ideal.jacobson (⊥ : Ideal A) := IsAdicComplete.le_jacobson_bot I
  have hsep : (⨅ n : ℕ, I ^ n • (⊤ : Submodule A (A ⧸ J))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hI
  have hmod : IsAdicComplete I (A ⧸ J) := isAdicComplete_of_iInf_smul_eq_bot I hsep
  exact (IsAdicComplete.map_algebraMap_iff (R := A) (S := A ⧸ J) (M := A ⧸ J) I).mpr hmod

/-- **Stacks 0A7K for a quotient.** A quotient of a Noetherian ring with a dualizing complex has
a dualizing complex: it is essentially of finite type. -/
public lemma exists_isDualizingComplex_quotient (A : Type u) [CommRing A]
    [IsNoetherianRing A] (J : Ideal A) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsDualizingComplex K) :
    ∃ L : DerivedCategory (ModuleCat.{u} (A ⧸ J)), Dualizing.IsDualizingComplex L := by
  have hft : IsEssentiallyOfFiniteType A (A ⧸ J) (algebraMap A (A ⧸ J)) :=
    ⟨A ⧸ J, inferInstance, inferInstance, inferInstance, ⊥,
      Algebra.id (A ⧸ J), IsScalarTower.right, IsLocalization.self bot_le⟩
  obtain ⟨_, L, hL⟩ :=
    Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType hft K hK
  exact ⟨L, hL⟩

/-- The reduction of an `I`-adically complete Noetherian ring is `I`-adically complete. -/
private lemma isAdicComplete_quotient_nilradical (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] :
    IsAdicComplete (I.map (algebraMap A (A ⧸ nilradical A))) (A ⧸ nilradical A) :=
  isAdicComplete_map_quotient A I (nilradical A)

/-- **Stacks 0A7K for the reduction.** The reduction of a Noetherian ring with a dualizing
complex has a dualizing complex: it is a quotient, hence essentially of finite type. -/
private lemma exists_isDualizingComplex_quotient_nilradical (A : Type u) [CommRing A]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsDualizingComplex K) :
    ∃ L : DerivedCategory (ModuleCat.{u} (A ⧸ nilradical A)), Dualizing.IsDualizingComplex L :=
  exists_isDualizingComplex_quotient A (nilradical A) K hK

/-- A generic point of `Spec(A)` is a minimal prime: its closure is an irreducible component,
so no smaller prime can have a strictly larger closure. -/
private lemma mem_minimalPrimes_of_mem_genericPoints (A : Type u) [CommRing A]
    (p : Spec (CommRingCat.of A)) (hp : p ∈ genericPoints (Spec (CommRingCat.of A))) :
    p.asIdeal ∈ minimalPrimes A := by
  refine PrimeSpectrum.isMin_iff.mp fun q hq => ?_
  have hspec : q ⤳ p := (PrimeSpectrum.le_iff_specializes q p).mp hq
  have h1 : closure ({p} : Set (Spec (CommRingCat.of A))) ⊆ closure {q} :=
    closure_minimal (Set.singleton_subset_iff.mpr hspec.mem_closure) isClosed_closure
  have h2 := hp.2 isIrreducible_singleton.closure h1
  have h3 : q ∈ closure ({p} : Set (Spec (CommRingCat.of A))) := h2 (subset_closure rfl)
  exact (PrimeSpectrum.le_iff_specializes p q).mpr (specializes_iff_mem_closure.mpr h3)

/-- On a reduced Noetherian ring the associated points of the structure sheaf of
`U = Spec(A) ∖ V(𝔞)` are minimal primes: by Stacks 05AR they are its weakly associated points,
those are weakly associated points of `Spec(A)` because `U` is an open subscheme, and by
Stacks 0EME the weakly associated points of the reduced scheme `Spec(A)` are the generic points
of its irreducible components. -/
@[ega "IV 3.2.1" "Concluding assertion"]
private lemma mem_minimalPrimes_of_mem_associatedPoints_unitModule (A : Type u) [CommRing A]
    [IsNoetherianRing A] [_root_.IsReduced A] (a : Ideal A)
    (x : (complementZeroLocus A a : Scheme))
    (hx : x ∈ Stacks.Divisors.associatedPoints (unitModule (complementZeroLocus A a : Scheme))) :
    x.1.asIdeal ∈ minimalPrimes A := by
  have hw : x ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints
      (complementZeroLocus A a : Scheme) := by
    rwa [AlgebraicGeometry.associatedPoints_eq_weaklyAssociatedPoints] at hx
  have hwA := AlgebraicGeometry.schemeWeaklyAssociatedPoints_map_of_isOpenImmersion
    (complementZeroLocus A a).ι hw
  rw [AlgebraicGeometry.weaklyAssociatedPointsOfScheme_eq_genericPoints] at hwA
  exact mem_minimalPrimes_of_mem_genericPoints A _ hwA

/-! ### The hypothesis Stacks 0EG2 carries -/

/-- **The one hypothesis of `Stacks.Algebraization.isIso_comparisonMap` (Stacks 0EG2) that
remains**, quantified over every Noetherian ring and every pair of ideals.

Stacks 0EG5 applies Stacks 0EG2 to the reduction of `A`, not to `A` itself, so the carried
hypothesis has to be available for every ring. It is not the conclusion of Stacks 0EG2 or of
Stacks 0EG5: `Stacks.Algebraization.SerreOneAlternativeComparison` is Stacks 0EIF, which
applies only to a module satisfying its third condition.

The other two hypotheses of Stacks 0EG2 are supplied rather than assumed: the middle clause of
Stacks 0H48 is `Stacks.Algebraization.middleComparisonOfShortExact` and the short exact
sequence is `Stacks.Algebraization.associatedPointSplitting`, so neither is a field here. -/
public structure ConnectednessComparisonInput : Prop where
  /-- Stacks 0EIF, the comparison under its own three conditions. -/
  serreOneAlternative : SerreOneAlternativeComparison.{u}

/-! ### The reduced case -/

/-- The support of `I · 𝒪_U` inside `U = Spec(A) ∖ V(𝔞)` is exactly `V(I) ∖ V(𝔞)`. -/
private lemma image_support_idealSheafNearVanishing (A : Type u) [CommRing A] (I a : Ideal A) :
    Subtype.val '' ((idealSheafNearVanishing A I a).support :
        Set (complementZeroLocus A a : Scheme)) =
      PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨support_baseIdealSheaf_le I (complementZeroLocus A a).ι hx, x.2⟩
  · rintro ⟨hpI, hpa⟩
    exact ⟨⟨p, hpa⟩, mem_support_baseIdealSheaf I (complementZeroLocus A a).ι hpI, rfl⟩

/-- **Stacks 0EG5 for a reduced ring, the preconnectedness half.** Once the comparison map of
Stacks 0EG2 for the structure sheaf of `U = Spec(A) ∖ V(𝔞)` is an isomorphism, `V(I) ∖ V(𝔞)` is
preconnected. -/
private lemma isPreconnected_zeroLocus_sdiff_of_isIso (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I a : Ideal A)
    [IsIso (comparisonMap A I a (unitModule (complementZeroLocus A a : Scheme)))]
    (hconn : ∀ V : Set (PrimeSpectrum A), IsOpen V → V.Nonempty →
      PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) ⊆ V →
      _root_.IsConnected V) :
    _root_.IsPreconnected
      (PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A)) := by
  have himage := image_support_idealSheafNearVanishing A I a
  have hpre : _root_.IsPreconnected ((idealSheafNearVanishing A I a).support :
      Set (complementZeroLocus A a : Scheme)) := by
    refine isPreconnected_support_of_realizable (idealSheafNearVanishing A I a) ?_ ?_
    · intro f hf
      obtain ⟨V, e, he⟩ := exists_realization_of_isIso_comparisonMap A I a
        (unitModule (complementZeroLocus A a : Scheme)) f hf
      exact ⟨V.openSet, e, fun x hx => V.contains_vanishing x
        (support_baseIdealSheaf_le I (complementZeroLocus A a).ι hx), fun n => he n.unop⟩
    · intro V hJV
      refine (complementZeroLocus A a).isOpenEmbedding'.isInducing.isPreconnected_image.mp ?_
      by_cases hne : (Subtype.val '' (V : Set (complementZeroLocus A a : Scheme))).Nonempty
      · refine (hconn (Subtype.val '' (V : Set (complementZeroLocus A a : Scheme)))
          ((complementZeroLocus A a).isOpenEmbedding'.isOpenMap _ V.2) hne ?_).2
        rw [← himage]
        exact Set.image_mono hJV
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]
        exact isPreconnected_empty
  rw [← himage]
  exact hpre.image Subtype.val continuous_subtype_val.continuousOn

/-- **Stacks 0EG5 for a reduced ring.** For a reduced Noetherian ring the dimension hypothesis
at the minimal primes is exactly condition (2) of Stacks 0EG2 for the structure sheaf of
`U = Spec(A) ∖ V(𝔞)`, because on a reduced scheme the associated points of the structure sheaf
are the generic points. -/
private lemma isPreconnected_zeroLocus_sdiff_of_isReduced (A : Type u) [CommRing A]
    [IsNoetherianRing A] [_root_.IsReduced A] (I a : Ideal A) (hIa : I ≤ a) [IsAdicComplete I A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : Dualizing.IsDualizingComplex K)
    (hdim : ∀ p q : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A → ¬ I ≤ p.asIdeal →
      p.asIdeal ≤ q.asIdeal → a ≤ q.asIdeal →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (closureLocalDimension A p q))
    (hconn : ∀ V : Set (PrimeSpectrum A), IsOpen V → V.Nonempty →
      PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) ⊆ V →
      _root_.IsConnected V)
    (hcmp : ConnectednessComparisonInput.{u}) :
    _root_.IsPreconnected
      (PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A)) := by
  have hboot : BootstrapHypotheses A I a (unitModule (complementZeroLocus A a : Scheme)) :=
    ⟨hIa, inferInstance, ⟨K, hK⟩, fun x hx hxI _ z hxz haz =>
      hdim x.1 z (mem_minimalPrimes_of_mem_associatedPoints_unitModule A a x hx) hxI hxz haz⟩
  have _ : IsIso (comparisonMap A I a (unitModule (complementZeroLocus A a : Scheme))) :=
    isIso_comparisonMap A I a _ hboot hcmp.serreOneAlternative middleComparisonOfShortExact
      (associatedPointSplitting A I a)
  exact isPreconnected_zeroLocus_sdiff_of_isIso A I a hconn

/-! ### Stacks 0EG5 -/

/-- **Stacks Project, Tag 0EG5.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`. Assume

1. `A` is `I`-adically complete and has a dualizing complex `K`,
2. if `𝔭` is a minimal prime of `A` not contained in `V(I)` and `𝔮 ∈ V(𝔭) ∩ V(𝔞)`, then
   `dim((A/𝔭)_𝔮) > cd(A, I) + 1`, and
3. every nonempty open `V ⊆ Spec(A)` containing `V(I) ∖ V(𝔞)` is connected.

Then `V(I) ∖ V(𝔞)` is either empty or connected.

The proof replaces `A` by its reduction, where the inequality in (2) holds at every associated
point of the structure sheaf of `U = Spec(A) ∖ V(𝔞)`, and applies Stacks 0EG2 to that structure
sheaf. A disconnection of `V(I) ∖ V(𝔞)` is turned into a compatible family of sections of
`𝒪_U / Iⁿ 𝒪_U` which is `1` on one piece and `0` on the other — the nontrivial idempotent of the
source — and Stacks 0EG2 realizes it as a function on a single open neighbourhood `V` of
`V(I) ∖ V(𝔞)`, whose germs along that locus take the two values `1` and `0`; the two opens where
they are attained disconnect a neighbourhood of `V(I) ∖ V(𝔞)`, contradicting (3).

The hypothesis `hcmp` carries the one input Stacks 0EG2 still needs, quantified over every
Noetherian ring and every pair of ideals, because the reduction step applies Stacks 0EG2 to the
reduction of `A` rather than to `A`. Its only field is Stacks 0EIF (`serreOneAlternative`),
which is neither this conclusion nor the conclusion of Stacks 0EG2. The middle clause of Stacks
0H48, which Stacks 0EG2 also consumes, is supplied by
`Stacks.Algebraization.middleComparisonOfShortExact`, and the short exact sequence by
`Stacks.Algebraization.associatedPointSplitting`.
Everything this adds over Stacks 0EG2 is proved here: the reduction to the reduced
case, that minimal primes give condition (2) of Stacks 0EG2, the construction of the
idempotent, and the passage from a realized idempotent to a disconnection of a neighbourhood. -/
@[stacks 0EG5 "V(I) minus V(a) is empty or connected; hcmp carries 0EIF, the one hypothesis \
0EG2 still has"]
public theorem eq_empty_or_isConnected_zeroLocus_sdiff (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I a : Ideal A) (hIa : I ≤ a) [IsAdicComplete I A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : Dualizing.IsDualizingComplex K)
    (hdim : ∀ p q : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A → ¬ I ≤ p.asIdeal →
      p.asIdeal ≤ q.asIdeal → a ≤ q.asIdeal →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))))
    (hconn : ∀ V : Set (PrimeSpectrum A), IsOpen V → V.Nonempty →
      PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) ⊆ V →
      _root_.IsConnected V)
    (hcmp : ConnectednessComparisonInput.{u}) :
    PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) = ∅ ∨
      _root_.IsConnected
        (PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A)) := by
  classical
  let B := A ⧸ nilradical A
  let φ : A →+* B := Ideal.Quotient.mk (nilradical A)
  have hφ : (algebraMap A B) = φ := rfl
  have hbij := PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
    (show nilradical A ≤ nilradical A from le_rfl)
  let H : PrimeSpectrum B ≃ₜ PrimeSpectrum A :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective B φ
      Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorphOfSurjective hbij.surjective
  let e : PrimeSpectrum B ≃o PrimeSpectrum A :=
    { toEquiv := Equiv.ofBijective (PrimeSpectrum.comap φ) hbij
      map_rel_iff' := fun {r s} =>
        Ideal.comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective _ _ }
  have he : ∀ r : PrimeSpectrum B, (e r).asIdeal = r.asIdeal.comap φ := fun _ => rfl
  have hmem : ∀ p : PrimeSpectrum B,
      p ∈ PrimeSpectrum.zeroLocus ((I.map φ : Ideal B) : Set B) \
          PrimeSpectrum.zeroLocus ((a.map φ : Ideal B) : Set B) ↔
        H p ∈ PrimeSpectrum.zeroLocus (I : Set A) \
          PrimeSpectrum.zeroLocus (a : Set A) := by
    intro p
    show (I.map φ ≤ p.asIdeal ∧ ¬ a.map φ ≤ p.asIdeal) ↔
      (I ≤ p.asIdeal.comap φ ∧ ¬ a ≤ p.asIdeal.comap φ)
    simp only [Ideal.map_le_iff_le_comap]
  have himage : H '' (PrimeSpectrum.zeroLocus ((I.map φ : Ideal B) : Set B) \
      PrimeSpectrum.zeroLocus ((a.map φ : Ideal B) : Set B)) =
      PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) := by
    ext p
    obtain ⟨q, rfl⟩ := H.surjective p
    exact H.injective.mem_set_image.trans (hmem q)
  have hconn' : ∀ V : Set (PrimeSpectrum B), IsOpen V → V.Nonempty →
      PrimeSpectrum.zeroLocus ((I.map φ : Ideal B) : Set B) \
        PrimeSpectrum.zeroLocus ((a.map φ : Ideal B) : Set B) ⊆ V → _root_.IsConnected V := by
    intro V hV hne hsub
    refine H.isConnected_image.mp (hconn (H '' V) (H.isOpenMap _ hV) (hne.image H) ?_)
    rw [← himage]
    exact Set.image_mono hsub
  have hdim' : ∀ p q : PrimeSpectrum B, p.asIdeal ∈ minimalPrimes B → ¬ I.map φ ≤ p.asIdeal →
      p.asIdeal ≤ q.asIdeal → a.map φ ≤ q.asIdeal →
      ((cohomologicalDimension B (I.map φ) (I.fg_of_isNoetherianRing.map φ) + 1 : ℤ) : EInt) <
        krullDimToEInt (closureLocalDimension B p q) := by
    intro p q hp hpI hpq haq
    have hpA : (e p).asIdeal ∈ minimalPrimes A := by
      refine PrimeSpectrum.isMin_iff.mp fun r hr => ?_
      have hrp : e.symm r ≤ p := by
        simpa only [e.symm_apply_apply] using e.symm.monotone hr
      have h := e.monotone (PrimeSpectrum.isMin_iff.mpr hp hrp)
      simpa only [e.apply_symm_apply] using h
    have hpIA : ¬ I ≤ (e p).asIdeal := fun h => hpI (Ideal.map_le_iff_le_comap.mpr h)
    have hpqA : (e p).asIdeal ≤ (e q).asIdeal := e.monotone hpq
    have haqA : a ≤ (e q).asIdeal := Ideal.map_le_iff_le_comap.mp haq
    have hd := hdim (e p) (e q) hpA hpIA hpqA haqA
    rw [← closureLocalDimension_eq_ringKrullDim_localizedQuotient (e p) (e q)] at hd
    have hcd := cohomologicalDimension_map_le φ I I.fg_of_isNoetherianRing
    calc ((cohomologicalDimension B (I.map φ) (I.fg_of_isNoetherianRing.map φ) + 1 : ℤ) : EInt)
        ≤ ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) := by
          simp only [WithBotTop.coe, Function.comp_apply, WithBot.coe_le_coe,
            WithTop.coe_le_coe]
          omega
      _ < krullDimToEInt (closureLocalDimension A (e p) (e q)) := hd
      _ = krullDimToEInt (closureLocalDimension B p q) := by
          rw [closureLocalDimension_quotientMk e he p q]
  have _ : _root_.IsReduced B :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  have _ : IsAdicComplete (I.map φ) B := hφ ▸ isAdicComplete_quotient_nilradical A I
  obtain ⟨L, hL⟩ := exists_isDualizingComplex_quotient_nilradical A K hK
  have hpre := isPreconnected_zeroLocus_sdiff_of_isReduced B (I.map φ) (a.map φ)
    (Ideal.map_mono hIa) L hL hdim' hconn' hcmp
  have hpreA := hpre.image H H.continuous.continuousOn
  rw [himage] at hpreA
  exact (Set.eq_empty_or_nonempty _).imp id fun hne => ⟨hne, hpreA⟩

end Stacks.Algebraization

end
