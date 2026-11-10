module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedComparisonOfLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateComparisonOfLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Envelope
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDifferentialsDual
public import StacksFrontier.AlgebraicGeometry.Crystalline.ThetaMonomialFamily
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceSectionsLevelQuotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderComparisonOfCoordinates
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTaylorLevels

/-!
# The functor of [Stacks, Lemma 60.17.3, Tag 07JG]

In Situation [Stacks, Tag 07MD], with `X = Spec(C)` and `S = Spec(A)`, [Stacks, Section 60.17,
Tag 07J7] chooses a polynomial presentation `P = A[x_i] → C` with kernel `J`, lets `D` be the
`p`-adically completed divided power envelope of `J` (equation (07J8)), `Ω_D` its `p`-adically
completed module of divided power differentials (equation (07J9)) and `d : D → Ω_D` the induced
derivation (equation (07JA)), and considers the pairs `(M, ∇)` of a `p`-adically complete
`D`-module (07JB) with a connection `∇ : M → M ⊗̂_D Ω_D` (07JC) which is integrable (07JD) and
topologically quasi-nilpotent (07JE).  [Stacks, Lemma 60.17.3, Tag 07JG] is the functor

`{crystals in quasi-coherent 𝒪_{X/S}-modules on Cris(X/S)} ⟶ {pairs (M, ∇) satisfying (07JB),
(07JC), (07JD) and (07JE)}`,

and this module constructs it: `...SmallSite.crystalPairFunctor`.  Its source is
`...SmallSite.QuasiCoherentCrystal`, the full subcategory of the sheaves of `𝒪_{X/S}`-modules
on the small crystalline site cut out by quasi-coherence and the crystal condition; its target is
`Crystalline.Pair`, the category of pairs satisfying the four items, with the horizontal maps.

The presentation is any surjective polynomial presentation `P = A[x_i : i ∈ ι] → C`, as the
source allows: it is the instance `...SmallSite.WholeSpacePresentation S hp` the system of
thickenings `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] (`...SmallSite.wholeSpaceSystem`) is built
from, by default the tautological `A[x_c : c ∈ C] → C` of `Crystalline.canonicalPresentation`;
`D` is `Crystalline.completedTensorPowerDividedPowerRing` in degree `0`, `Ω_D` is
`Crystalline.completedTensorPowerDifferentials` and `d` is `Crystalline.tensorPowerDerivation`.

## The construction, following the source's proof

* **The module** `M = lim_e Γ((X, T_e, δ̄), ℱ)` is `...SmallSite.wholeSpaceSections`; it is a
  `D`-module, `M_e = M/p^{N+e}M` (`...SmallSite.ker_pairComponent`), so it is `p`-adically
  complete, which is item (07JB) (`...SmallSite.isPAdicallyComplete_pair`).
* **The Taylor expansion.**  Since `ℱ` is a crystal, `Γ(T(1)_e, ℱ) = D(1)_e ⊗_{D_e, p₀} M_e`, and
  `D(1)_e` is free over `D_e` on the divided power monomials `ξ^{[K]}`, `ξ_c = x_c ⊗ 1 - 1 ⊗ x_c`
  ([Stacks, Tag 07L2]); so `p₁^* m = ∑_K ξ^{[K]} · p₀^* θ_K(m)` for unique `θ_K(m)`, a finite sum
  at each level (`...SmallSite.levelTaylorExpansion`, `...SmallSite.crystalTheta`).  The cocycle
  condition over `D(2)` gives `θ_L ∘ θ_K = θ_{K+L}`, that is `θ_K = ∏ θ_c^{k_c}`
  (`...SmallSite.crystalTheta_crystalTheta`), and the diagonal gives `θ_0 = id`.
* **The connection** (07JC) is the image of the Taylor expansion under `D(1) → D ⊕ Ω_D`,
  `ξ_c ↦ -d x_c`, assembled over the levels: `...SmallSite.pairConnection`, with coordinate
  expansion `∇(m) = ∑_c (-θ_c(m)) ⊗ d x_c` (`...SmallSite.isCoordinateExpansion_pairConnection`).
  Its Leibniz rule comes from the Leibniz rule of the `θ_c` and Taylor's formula
  `d f = - ∑_c δ_c(f) d x_c` for the coefficients of `p₁(f)` (`...SmallSite.pairLevel_leibniz`).
* **Integrability** (07JD) and **topological quasi-nilpotence** (07JE) are read off
  `θ_K = ∏ θ_c^{k_c}` and the finiteness of the Taylor expansion at the first level
  (`...SmallSite.isIntegrable_pairConnection`,
  `...SmallSite.isTopologicallyQuasiNilpotent_pairConnection`), through the coordinate functionals
  `...SmallSite.pairCoord` of `Ω_D`, which exist although `Ω_D` is not free on the `d x_c`.
* **A morphism of crystals** induces the map of the limits, which is horizontal
  (`...SmallSite.pairConnection_naturality`).
* **The connection is the canonical connection of [Stacks, Tag 07J6] evaluated on the `T_e`**,
  as the statement of the tag says: restricting the Taylor expansion along the morphism from the
  first-order thickening `T'_e` of [Stacks, Tag 07J2] to `T(1)_e` gives
  `p₁^* m - p₀^* m = - ∑_c d x_c · p₀^* θ_c(m)`.  This is proved downstream, in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalPairConnection07J6.lean`
  (`...SmallSite.pairTensorLevel_crystalPairFunctor_nabla`).

## Main definitions

* `...SmallSite.pairRing`, `...SmallSite.pairForms`, `...SmallSite.pairDerivation`,
  `...SmallSite.pairDx` — `D`, `Ω_D`, `d` and the `d x_c`.
* `...SmallSite.crystalPair` — the pair attached to a crystal.
* `...SmallSite.crystalPairFunctor` — **the functor of [Stacks, Tag 07JG].**

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Section 60.17, Tag 07J7](https://stacks.math.columbia.edu/tag/07J7)
* [Stacks Project, Lemma 60.17.5, Tag 07L2](https://stacks.math.columbia.edu/tag/07L2)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-! ### The ring `D`, the module `Ω_D` and the derivation `d` -/

/-- **The ring `D` of [Stacks, Tag 07J8]**: the `p`-adically completed divided power envelope of
the kernel of the presentation `P = A[x_i : i ∈ ι] → C`, with its divided powers. -/
abbrev pairRing : DividedPowerRing.{u} :=
  completedTensorPowerDividedPowerRing (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) 0

/-- **The module `Ω_D` of [Stacks, Tag 07J9]**: the `p`-adic completion of the module of divided
power differentials. -/
abbrev pairForms : Type u :=
  completedTensorPowerDifferentials (affineSituation S hp)
    (wholeSpacePresentation S hp) 0

/-- The right action of `D` on `Ω_D`, equal to the left one; it is what makes `D ⊕ Ω_D` a
ring. -/
instance : Module (pairRing hp)ᵐᵒᵖ (pairForms hp) :=
  Module.compHom (pairForms hp) (RingEquiv.toOpposite (pairRing hp)).symm.toRingHom

/-- The two actions of `D` on `Ω_D` agree. -/
instance : IsCentralScalar (pairRing hp) (pairForms hp) := ⟨fun _ _ ↦ rfl⟩

/-- **The derivation `d : D → Ω_D` of [Stacks, Tag 07JA].** -/
abbrev pairDerivation :=
  tensorPowerDerivation (affineSituation S hp) (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) 0

/-- The differential `d x_c ∈ Ω_D` of the variable `x_c` of `P`. -/
def pairDx (c : wholeSpaceIndex S hp) : pairForms hp :=
  pairDerivation hp (wsCompletionMap hp 0
    ((tensorPowerEnvelope (affineSituation S hp)
      (wholeSpacePresentation S hp) 0).algebraMap.toRingHom
        (MvPolynomial.X ((0 : Fin 1), c))))

/-! ### The module `M = lim_e Γ(T_e, ℱ)` and its levels, over `D` -/

section Modules

variable (Fc : QuasiCoherentCrystal S)

/-- `M = lim_e Γ(T_e, ℱ)` is a `D`-module. -/
instance pairSectionsModule : Module (pairRing hp) (wholeSpaceSections hp Fc ⦋0⦌) :=
  wholeSpaceSectionsModule hp Fc ⦋0⦌

/-- The sections `Γ(T_e, ℱ)` over the level `e`, as a `D`-module through the reduction
`D → Γ(T_e, 𝒪)`.  A type synonym, so that the `D`-module structure does not compete with the
`Γ(T_e, 𝒪)`-module structure. -/
def pairLevel (e : ℕ) : Type u := Fc.obj.val.obj (op (levelObj hp 0 e))

/-- The additive group of the sections over the level `e`. -/
instance (e : ℕ) : AddCommGroup (pairLevel hp Fc e) :=
  inferInstanceAs (AddCommGroup (Fc.obj.val.obj (op (levelObj hp 0 e))))

/-- `D` acts on the sections over the level `e` through the reduction `D → Γ(T_e, 𝒪)`. -/
instance pairLevelModule (e : ℕ) : Module (pairRing hp) (pairLevel hp Fc e) :=
  Module.compHom (Fc.obj.val.obj (op (levelObj hp 0 e))) (levelSectionsScalars hp ⦋0⦌ e)

/-- The action of `D` on the sections over the level `e` is that of its reduction. -/
theorem pairLevel_smul (e : ℕ) (a : pairRing hp) (x : pairLevel hp Fc e) :
    a • x = (show Fc.obj.val.obj (op (levelObj hp 0 e)) from
      levelSectionsScalars hp ⦋0⦌ e a • (show Fc.obj.val.obj (op (levelObj hp 0 e)) from x)) :=
  rfl

/-- The component `M → Γ(T_e, ℱ)`, as a `D`-linear map. -/
def pairComponent (e : ℕ) : wholeSpaceSections hp Fc ⦋0⦌ →ₗ[pairRing hp] pairLevel hp Fc e where
  toFun m := wholeSpaceSectionsVal hp Fc m e
  map_add' x y := wholeSpaceSectionsVal_add hp Fc x y e
  map_smul' a m := wholeSpaceSectionsVal_smul hp Fc a m e

/-- The component of `m ∈ M` at the level `e`. -/
@[simp] theorem pairComponent_apply (e : ℕ) (m : wholeSpaceSections hp Fc ⦋0⦌) :
    pairComponent hp Fc e m = wholeSpaceSectionsVal hp Fc m e := rfl

/-- The scalars of the levels are compatible with the restrictions between the levels. -/
theorem levelSectionsScalars_levelMap (n : ℕ) {e e' : ℕ} (h : e ⟶ e')
    (a : ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) :
    crysSheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map h).hom
        (levelSectionsScalars hp ⦋n⦌ e' a) = levelSectionsScalars hp ⦋n⦌ e a := by
  rw [levelSectionsScalars_eq_envelopeLevelRingLimitEquiv,
    levelSectionsScalars_eq_envelopeLevelRingLimitEquiv]
  exact (envelopeLevelRingLimitEquiv hp n
    ((wholeSpaceSystemEnvelopeRingEquiv hp n).symm _)).property h

/-- The restriction `Γ(T_{e+1}, ℱ) → Γ(T_e, ℱ)`, as a `D`-linear map. -/
def pairRestrict (e : ℕ) : pairLevel hp Fc (e + 1) →ₗ[pairRing hp] pairLevel hp Fc e where
  toFun x := crysRestrict Fc.obj (levelDrop hp 0 e) x
  map_add' x y := map_add _ x y
  map_smul' a x :=
    (map_smulₛₗ (crysRestrict Fc.obj (levelDrop hp 0 e)) (levelSectionsScalars hp ⦋0⦌ (e + 1) a)
      (x : Fc.obj.val.obj (op (levelObj hp 0 (e + 1))))).trans
    (congrArg (fun r ↦ r • crysRestrict Fc.obj (levelDrop hp 0 e) x)
      (levelSectionsScalars_levelMap hp 0 (homOfLE (Nat.le_succ e)) a))

/-- `...SmallSite.pairRestrict` is the restriction of sections. -/
theorem pairRestrict_apply (e : ℕ) (x : pairLevel hp Fc (e + 1)) :
    pairRestrict hp Fc e x = crysRestrict Fc.obj (levelDrop hp 0 e) x := rfl

/-- The components of `M` are compatible with the restrictions between the levels. -/
theorem pairRestrict_comp_pairComponent (e : ℕ) :
    pairRestrict hp Fc e ∘ₗ pairComponent hp Fc (e + 1) = pairComponent hp Fc e :=
  LinearMap.ext fun m ↦ wholeSpaceSectionsVal_restrict hp Fc m (homOfLE (Nat.le_succ e))

/-- The component `M → Γ(T_e, ℱ)` is surjective. -/
theorem surjective_pairComponent (e : ℕ) : Function.Surjective (pairComponent hp Fc e) :=
  surjective_wholeSpaceSectionsVal hp Fc
    (isSurjectiveComparison_of_isSheafCrystal Fc.property.2) 0 e

/-- **The kernel of the component at the level `e` is `p^{N+e} M`**, the crystal level-quotient
relation `M_e = M/p^{N+e} M` of the source's proof. -/
theorem ker_pairComponent (e : ℕ) :
    LinearMap.ker (pairComponent hp Fc e) =
      DividedPowers.pAdicIdeal (A := (pairRing hp : Type u)) S.p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) •
      (⊤ : Submodule (pairRing hp) (wholeSpaceSections hp Fc ⦋0⦌)) := by
  ext x
  rw [LinearMap.mem_ker, pairComponent_apply]
  exact (mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero hp Fc
    (isSurjectiveComparison_of_isSheafCrystal Fc.property.2) 0 e x).symm

end Modules

/-! ### The comparison datum of a crystal at a level -/

section LevelComparison

variable (Fc : QuasiCoherentCrystal S) (e : ℕ)

/-- The first-order thickening `D ⊕ Ω_D`. -/
abbrev pairExt : Type u := firstOrderExtension (pairRing hp) (pairForms hp)

/-- The ring `D` is the degree `0` of `...SmallSite.wholeSpaceEnvelopeRing`; the identity. -/
def pairToEnv : pairRing hp ≃+* ((wholeSpaceEnvelopeRing hp).obj ⦋0⦌ : Type u) :=
  RingEquiv.refl _

/-- The map `E(0) → D` to the completion. -/
def pairOf : (wsEnvelope hp 0 : Type u) →+* pairRing hp :=
  (pairToEnv hp).symm.toRingHom.comp (wsCompletionMap hp 0)

/-- The reduction `D → Γ(T_e, 𝒪)` through which `D` acts on the sections over the level `e`. -/
def pairLss : pairRing hp →+* crysSheafRing S (levelObj hp 0 e).obj :=
  (levelSectionsScalars hp ⦋0⦌ e).comp (pairToEnv hp).toRingHom

/-- The reduction of the image of `y ∈ E(0)` in `D` is the reduction of `y` to the level `e`. -/
theorem pairLss_pairOf (y : wsEnvelope hp 0) : pairLss hp e (pairOf hp y) = envLevelMap hp 0 e y :=
  rfl

/-- The reduction `D → Γ(T_e, 𝒪)` is the quotient map followed by the level identification. -/
theorem pairLss_apply (a : pairRing hp) :
    pairLss hp e a = (wholeSpaceEnvelopeRingLevelEquiv hp 0 e).symm
      (Ideal.Quotient.mk _ (pairToEnv hp a)) := rfl

/-- `D` acts on the sections over the level `e` through `...SmallSite.pairLss`. -/
theorem pairLevel_smul_eq (a : pairRing hp) (x : pairLevel hp Fc e) :
    a • x = (show pairLevel hp Fc e from
      pairLss hp e a • (show Fc.obj.val.obj (op (levelObj hp 0 e)) from x)) :=
  rfl

/-- Two scalars of `D` with the same reduction to the level `e` differ by a multiple of
`p^{N+e}`. -/
theorem exists_eq_add_of_pairLss_eq {a b : pairRing hp} (h : pairLss hp e a = pairLss hp e b) :
    ∃ t : pairRing hp, a = b +
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) : pairRing hp) *
        t := by
  rw [pairLss_apply, pairLss_apply] at h
  have h' := (wholeSpaceEnvelopeRingLevelEquiv hp 0 e).symm.injective h
  rw [Ideal.Quotient.eq, DividedPowers.pAdicIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at h'
  obtain ⟨t, ht⟩ := h'
  refine ⟨(pairToEnv hp).symm t, ?_⟩
  apply (pairToEnv hp).injective
  rw [map_add, map_mul, map_natCast, RingEquiv.apply_symm_apply, mul_comm _ t, Nat.cast_pow]
  exact eq_add_of_sub_eq' ht.symm

/-- `p^{N+e}` kills the sections over the level `e`. -/
theorem pow_smul_pairLevel (t : pairRing hp) (x : pairLevel hp Fc e) :
    (((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      pairRing hp) * t) • x = 0 := by
  rw [mul_smul, pairLevel_smul_eq hp Fc e _ (t • x)]
  have h0 : pairLss hp e
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) : pairRing hp) =
      0 := by
    rw [map_natCast, ← map_natCast (envLevelMap hp 0 e), envLevelMap_pow]
  rw [h0, zero_smul]
  rfl

/-- The scalars of `D` move across the tensor product from the square-zero summand. -/
theorem inr_smul_tmul (r : pairRing hp) (ω : pairForms hp) (x : pairLevel hp Fc e) :
    (TrivSqZeroExt.inr (r • ω) : pairExt hp) ⊗ₜ[pairRing hp] x =
      (TrivSqZeroExt.inr ω : pairExt hp) ⊗ₜ[pairRing hp] (r • x) := by
  rw [← TensorProduct.smul_tmul]
  congr 1
  refine TrivSqZeroExt.ext ?_ ?_
  · exact (mul_zero r).symm
  · rfl

/-- `d` of a multiple of `p^{N+e}`, tensored with a section over the level `e`, vanishes. -/
theorem inr_pairDerivation_pow_mul_tmul (t : pairRing hp) (x : pairLevel hp Fc e) :
    (TrivSqZeroExt.inr (pairDerivation hp
      (((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        pairRing hp) * t)) : pairExt hp) ⊗ₜ[pairRing hp] x = 0 := by
  have hp0 : pairDerivation hp
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) : pairRing hp) =
      0 := by
    rw [← map_natCast (algebraMap ((affineSituation S hp).A : Type u)
      (pAdicCompletedTensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp) 0))]
    exact (pairDerivation hp).map_ringHom _
  have hpx : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      pairRing hp) • x = 0 := by
    simpa only [mul_one] using pow_smul_pairLevel hp Fc e 1 x
  have hl : pairDerivation hp
      (((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        pairRing hp) * t) =
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        pairRing hp) • pairDerivation hp t := by
    have h1 := (pairDerivation hp).leibniz
      (((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        pairRing hp)) t
    rwa [hp0, smul_zero, add_zero] at h1
  rw [hl, inr_smul_tmul, hpx, TensorProduct.tmul_zero]

/-- Scalars of `D` differing by a multiple of `p^{N+e}` have the same `d`, as far as the sections
over the level `e` can see. -/
theorem inr_pairDerivation_tmul_eq {a b t : pairRing hp}
    (h : a = b + ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      pairRing hp) * t) (x : pairLevel hp Fc e) :
    (TrivSqZeroExt.inr (pairDerivation hp a) : pairExt hp) ⊗ₜ[pairRing hp] x =
      (TrivSqZeroExt.inr (pairDerivation hp b) : pairExt hp) ⊗ₜ[pairRing hp] x := by
  subst h
  have h2 := inr_pairDerivation_pow_mul_tmul hp Fc e t x
  simp only [map_add, TrivSqZeroExt.inr_add, TensorProduct.add_tmul, h2, add_zero]

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **Taylor's formula for `d` on `D`, at the image of the envelope**:
`d y = - ∑_c δ_c(y) d x_c`. -/
theorem pairDerivation_pairOf (y : wsEnvelope hp 0) (T : Finset (wholeSpaceIndex S hp))
    (hT : ∀ c ∉ T, envelopeTaylorCoeff _ _ y (Finsupp.single c 1) = 0) :
    pairDerivation hp (pairOf hp y) =
      -∑ c ∈ T, pairOf hp (envelopeTaylorCoeff _ _ y (Finsupp.single c 1)) • pairDx hp c := by
  have h0 := tensorPowerDerivation_of (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) 0 y
  have h1 := dividedPowerDifferential_eq_neg_sum_envelopeTaylorCoeff (affineSituation S hp)
    (wholeSpacePresentation S hp) y T hT
  refine h0.trans ?_
  rw [h1, map_neg, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [map_smul]
  refine (algebraMap_smul (pairRing hp) _ _).symm.trans ?_
  congr 1
  exact (tensorPowerDerivation_of (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) 0 _).symm

/-- The first-order Taylor coefficients on the sections over the level `e`, as an additive map. -/
def pairFirstOrderHom : pairLevel hp Fc e →+ (wholeSpaceIndex S hp →₀ pairLevel hp Fc e) :=
  (levelTaylorExpansion hp Fc e).firstOrderCoeffs

/-- The coefficient of index `c` of the first-order Taylor coefficients of `x` is `θ_c(x)`. -/
theorem pairFirstOrderHom_apply (x : pairLevel hp Fc e) (c : wholeSpaceIndex S hp) :
    pairFirstOrderHom hp Fc e x c = levelTheta hp Fc e (Finsupp.single c 1) x := rfl

/-- **The Leibniz rule for the first-order Taylor coefficients, with Taylor's formula for `d`**:
for some `δ`, `θ_c(a x) = a θ_c(x) + δ_c x` for every `c` and `d a ⊗ x = - ∑_c d x_c ⊗ δ_c x`;
the input of `Crystalline.coordinateComparison`. -/
theorem pairLevel_leibniz (a : pairRing hp) (x : pairLevel hp Fc e) :
    ∃ δ : wholeSpaceIndex S hp →₀ pairRing hp,
      (∀ c, pairFirstOrderHom hp Fc e (a • x) c =
        a • pairFirstOrderHom hp Fc e x c + δ c • x) ∧
      (TrivSqZeroExt.inr (pairDerivation hp a) : pairExt hp) ⊗ₜ[pairRing hp] x =
        -δ.sum fun c b ↦ (TrivSqZeroExt.inr (pairDx hp c) : pairExt hp) ⊗ₜ (b • x) := by
  classical
  obtain ⟨y, hy⟩ := surjective_envLevelMap hp 0 e (pairLss hp e a)
  let δ₀ := (envelopeTaylorExpansion (affineSituation S hp)
    (wholeSpacePresentation S hp)).firstOrderCoeffs y
  refine ⟨δ₀.mapRange (pairOf hp) (map_zero _), fun c ↦ ?_, ?_⟩
  · rw [Finsupp.mapRange_apply]
    have h := levelTheta_single_smul hp Fc e y c x
    rwa [hy] at h
  · obtain ⟨t, ht⟩ := exists_eq_add_of_pairLss_eq hp e (hy.symm.trans (pairLss_pairOf hp e y).symm)
    refine (inr_pairDerivation_tmul_eq hp Fc e ht x).trans ?_
    have hT : ∀ c ∉ δ₀.support, envelopeTaylorCoeff _ _ y (Finsupp.single c 1) = 0 :=
      fun c hc ↦ (Finsupp.notMem_support_iff.mp hc : _)
    refine (congrArg (fun ω ↦ (TrivSqZeroExt.inr ω : pairExt hp) ⊗ₜ[pairRing hp] x)
      (pairDerivation_pairOf hp y δ₀.support hT)).trans ?_
    refine (inr_neg_sum_smul_tmul (pairRing hp) (pairForms hp) (pairDx hp) δ₀.support _ x).trans ?_
    congr 1
    rw [Finsupp.sum_of_support_subset _ (Finsupp.support_mapRange) _
      (fun c _ ↦ by rw [zero_smul, TensorProduct.tmul_zero])]
    rfl

/-- **The first-order comparison datum of the crystal at the level `e`**:
`x ↦ 1 ⊗ x - ∑_c d x_c ⊗ θ_c(x)`, the image in `(D ⊕ Ω_D) ⊗_D Γ(T_e, ℱ)` of the Taylor expansion
`p₁^* x = ∑_K ξ^{[K]} · p₀^* θ_K(x)` under `D(1) → D ⊕ Ω_D`, `ξ_c ↦ - d x_c`. -/
def pairLevelComparison :
    FirstOrderComparison ((affineSituation S hp).A : Type u) (pairRing hp)
      (algebraMap ((affineSituation S hp).A : Type u)
        (pAdicCompletedTensorPowerEnvelope (affineSituation S hp)
          (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) 0))
      (pairForms hp) (pairDerivation hp) (pairLevel hp Fc e) :=
  coordinateComparison (pairRing hp) (pairForms hp) (pairDerivation hp) (pairDx hp)
    (pairFirstOrderHom hp Fc e) (pairLevel_leibniz hp Fc e)

end LevelComparison

/-! ### The completed comparison datum and the connection -/

section Connection

variable (Fc : QuasiCoherentCrystal S)

/-- The first-order Taylor coefficients commute with the restrictions between the levels. -/
theorem pairFirstOrderHom_pairRestrict (e : ℕ) (x : pairLevel hp Fc (e + 1)) :
    pairFirstOrderHom hp Fc e (pairRestrict hp Fc e x) =
      (pairFirstOrderHom hp Fc (e + 1) x).mapRange (pairRestrict hp Fc e) (map_zero _) :=
  Finsupp.ext fun _ ↦ levelTheta_levelRestrict hp Fc (homOfLE (Nat.le_succ e)) _ x

/-- The comparison data of the levels are compatible with the restrictions. -/
theorem pairLevelComparison_restrict (e : ℕ) (x : pairLevel hp Fc (e + 1)) :
    LinearMap.lTensor (firstOrderExtension (pairRing hp) (pairForms hp)) (pairRestrict hp Fc e)
        (pairLevelComparison hp Fc (e + 1) x) =
      pairLevelComparison hp Fc e (pairRestrict hp Fc e x) :=
  lTensor_coordinateComparisonFun (pairRing hp) (pairForms hp) (pairDx hp)
    (pairFirstOrderHom hp Fc (e + 1)) (pairFirstOrderHom hp Fc e) (pairRestrict hp Fc e)
    (pairFirstOrderHom_pairRestrict hp Fc e) x

/-- **The completed comparison datum of the crystal on `M = lim_e Γ(T_e, ℱ)`**, over the
completed base change `(D ⊕ Ω_D) ⊗̂_D M`. -/
def pairComparison :
    CompletedFirstOrderComparison ((affineSituation S hp).A : Type u) (pairRing hp)
      (algebraMap ((affineSituation S hp).A : Type u)
        (pAdicCompletedTensorPowerEnvelope (affineSituation S hp)
          (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) 0))
      (pairForms hp) (pairDerivation hp) S.p (wholeSpaceSections hp Fc ⦋0⦌) :=
  CompletedFirstOrderComparison.ofLevels (wholeSpaceSections hp Fc ⦋0⦌) (pairLevel hp Fc)
    (pairRestrict hp Fc) (_root_.Crystalline.uniformLevel (affineSituation S hp))
    (pairComponent hp Fc) (surjective_pairComponent hp Fc) (ker_pairComponent hp Fc)
    (pairRestrict_comp_pairComponent hp Fc) (pairLevelComparison hp Fc)
    (pairLevelComparison_restrict hp Fc)

/-- **The connection `∇ : M → M ⊗̂_D Ω_D` of [Stacks, Tag 07JG]**, item (07JC). -/
def pairConnection :
    CompletedConnection S.p (pairRing hp) (pairForms hp)
      (derivationFun ((affineSituation S hp).A : Type u) (pairRing hp) _ (pairForms hp)
        (pairDerivation hp)) (wholeSpaceSections hp Fc ⦋0⦌) :=
  (pairComparison hp Fc).completedConnection

end Connection

/-! ### The coordinates of `Ω_D` -/

section Coordinates

/-- The envelope `E(0)` as an algebra over the base. -/
abbrev wsEnvelopeAlgebra : Algebra ((affineSituation S hp).A : Type u) (wsEnvelope hp 0) :=
  tensorPowerEnvelopeAlgebraInstance (affineSituation S hp)
    (wholeSpacePresentation S hp) 0

/-- **The divided power differentials of `E(0)` are free on the `d x_c`** ([Stacks, Tag 07HW]:
they are the base change of the Kähler differentials of `P`). -/
def envelopeFormsBasis :
    letI := wsEnvelopeAlgebra hp
    Module.Basis (wholeSpaceIndex S hp) (wsEnvelope hp 0)
      (dividedPowerDifferentials (A := ((affineSituation S hp).A : Type u))
        (wsEnvelope hp 0).dividedPowers) :=
  (tensorPowerDifferentialsBasis (affineSituation S hp)
    (wholeSpacePresentation S hp) 0).reindex
      (@Equiv.uniqueProd _ (Fin (0 + 1)) Fin.instUnique)

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The basis vector of index `c` is the divided power differential of `x_c`. -/
theorem envelopeFormsBasis_apply (c : wholeSpaceIndex S hp) :
    letI := wsEnvelopeAlgebra hp
    envelopeFormsBasis hp c = dividedPowerDifferential (A := ((affineSituation S hp).A : Type u))
      (wsEnvelope hp 0).dividedPowers
      ((tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 0).algebraMap.toRingHom
          (MvPolynomial.X ((0 : Fin 1), c))) := by
  rw [envelopeFormsBasis, Module.Basis.reindex_apply]
  exact tensorPowerDifferentialsBasis_apply (affineSituation S hp)
    (wholeSpacePresentation S hp) 0 _

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- `d x_c` is the completion of the basis vector of index `c`. -/
theorem pairDx_eq (c : wholeSpaceIndex S hp) :
    pairDx hp c = AdicCompletion.of _ _ (envelopeFormsBasis hp c) := by
  rw [envelopeFormsBasis_apply]
  exact tensorPowerDerivation_of (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) 0 _

end Coordinates

/-! ### The pair `(M, ∇)` attached to a crystal -/

section PairObject

variable (Fc : QuasiCoherentCrystal S)

/-- **The coordinate functionals of `Ω_D`**: the completions of the coordinates of the basis
`d x_c` of the divided power differentials of the envelope.  They exist although `Ω_D` is not free
on the `d x_c` when there are infinitely many coordinates. -/
def pairCoord (c : wholeSpaceIndex S hp) : pairForms hp →ₗ[pairRing hp] pairRing hp :=
  adicDualFamily (DividedPowers.pAdicIdeal (A := wsEnvelope hp 0) (affineSituation S hp).p)
    (envelopeFormsBasis hp) c

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The coordinate functionals are dual to the `d x_c`. -/
theorem isCoordinateDual_pairDx : IsCoordinateDual (pairDx hp) (pairCoord hp) :=
  isCoordinateDual_adicDualFamily _ (envelopeFormsBasis hp) (pairDx_eq hp)

/-- **The coordinate expansion of the connection**: `∇ m = ∑_c (-θ_c(m)) ⊗ d x_c`, the sum
converging `p`-adically, with `θ_c = θ_{e_c}` the first-order Taylor operators of the crystal. -/
theorem isCoordinateExpansion_pairConnection :
    IsCoordinateExpansion S.p (pairRing hp) (pairForms hp) (pairDx hp) (pairConnection hp Fc)
      (fun c m ↦ -crystalTheta hp Fc (Finsupp.single c 1) m) :=
  isCoordinateExpansion_ofLevels (wholeSpaceSections hp Fc ⦋0⦌) (pairLevel hp Fc)
    (pairRestrict hp Fc) (_root_.Crystalline.uniformLevel (affineSituation S hp))
    (pairComponent hp Fc) (surjective_pairComponent hp Fc) (ker_pairComponent hp Fc)
    (pairRestrict_comp_pairComponent hp Fc) (pairDx hp) (pairFirstOrderHom hp Fc)
    (pairLevel_leibniz hp Fc) (pairFirstOrderHom_pairRestrict hp Fc)
    (fun c m ↦ crystalTheta hp Fc (Finsupp.single c 1) m) (fun _ _ _ ↦ rfl)

/-- The composite operators `±θ_K` of the coordinate operators `-θ_c`. -/
def pairThetaPow (K : wholeSpaceIndex S hp →₀ ℕ) (m : wholeSpaceSections hp Fc ⦋0⦌) :
    wholeSpaceSections hp Fc ⦋0⦌ :=
  ((-1 : ℤ) ^ K.degree) • crystalTheta hp Fc K m

/-- **The identity `θ_K = ∏ θ_i^{k_i}` of [Stacks, Tag 07JG]**, for the coordinate operators of
the connection. -/
theorem isThetaMonomialFamily_pairThetaPow :
    IsThetaMonomialFamily (wholeSpaceSections hp Fc ⦋0⦌)
      (fun c m ↦ -crystalTheta hp Fc (Finsupp.single c 1) m) (pairThetaPow hp Fc) := by
  refine ⟨funext fun m ↦ ?_, fun i k ↦ funext fun m ↦ ?_⟩
  · rw [pairThetaPow, map_zero, pow_zero, one_smul, crystalTheta_zero]
    rfl
  · rw [Function.comp_apply, pairThetaPow, pairThetaPow]
    change _ = -(crystalTheta hp Fc (Finsupp.single i 1)) (((-1 : ℤ) ^ k.degree) • _)
    rw [map_zsmul, crystalTheta_crystalTheta, map_add, Finsupp.degree_single, pow_succ,
      mul_neg_one, neg_smul]

/-- **Item (07JB)**: `M = lim_e Γ(T_e, ℱ)` is `p`-adically complete. -/
theorem isPAdicallyComplete_pair :
    IsPAdicallyComplete S.p (pairRing hp) (wholeSpaceSections hp Fc ⦋0⦌) :=
  wholeSpaceSectionsIsAdicComplete hp Fc ⦋0⦌

/-- The operators `θ_K(m)` lie in `p M` for all but finitely many `K`: the Taylor expansion over
`T(1)_1` is a finite sum. -/
theorem finite_pairThetaPow_notMem (m : wholeSpaceSections hp Fc ⦋0⦌) :
    {K | pairThetaPow hp Fc K m ∉
      pSmul S.p (pairRing hp) (wholeSpaceSections hp Fc ⦋0⦌)}.Finite := by
  refine (finite_crystalTheta_ne_zero hp Fc m 1).subset fun K hK ↦ ?_
  intro h0
  apply hK
  have hmem : crystalTheta hp Fc K m ∈ LinearMap.ker (pairComponent hp Fc 1) := h0
  rw [ker_pairComponent] at hmem
  have hle : DividedPowers.pAdicIdeal (A := (pairRing hp : Type u)) S.p ^
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + 1) •
        (⊤ : Submodule (pairRing hp) (wholeSpaceSections hp Fc ⦋0⦌)) ≤
      pSmul S.p (pairRing hp) (wholeSpaceSections hp Fc ⦋0⦌) :=
    Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero _))
  exact Submodule.smul_of_tower_mem _ _ (hle hmem)

/-- **Item (07JD)**: the connection is integrable. -/
theorem isIntegrable_pairConnection :
    IsIntegrable S.p (pairRing hp) (pairForms hp) (pairDx hp) (pairConnection hp Fc) :=
  isIntegrable_of_isThetaMonomialFamily_adicCompletion _ (envelopeFormsBasis hp) (pairDx_eq hp)
    S.p (wholeSpaceSections hp Fc ⦋0⦌) (isThetaMonomialFamily_pairThetaPow hp Fc)
    (isCoordinateExpansion_pairConnection hp Fc)
    (isPAdicallyComplete_pair hp Fc).toIsHausdorff

/-- **Item (07JE)**: the connection is topologically quasi-nilpotent. -/
theorem isTopologicallyQuasiNilpotent_pairConnection :
    IsTopologicallyQuasiNilpotent S.p (pairRing hp) (pairForms hp) (pairDx hp)
      (pairConnection hp Fc) :=
  isTopologicallyQuasiNilpotent_of_isThetaMonomialFamily_adicCompletion _ (envelopeFormsBasis hp)
    (pairDx_eq hp) S.p (wholeSpaceSections hp Fc ⦋0⦌) (isThetaMonomialFamily_pairThetaPow hp Fc)
    (isCoordinateExpansion_pairConnection hp Fc)
    (isPAdicallyComplete_pair hp Fc).toIsHausdorff (finite_pairThetaPow_notMem hp Fc)

/-- **The pair `(M, ∇)` of [Stacks, Lemma 60.17.3, Tag 07JG] attached to a crystal**:
`M = lim_e Γ(T_e, ℱ)` over `D`, with the connection read off the Taylor expansion of the crystal
over `D(1)`; it satisfies (07JB), (07JC), (07JD) and (07JE). -/
def crystalPair :
    Pair.{u, u, u, u} S.p (pairRing hp) (pairForms hp) (pairDx hp)
      (derivationFun ((affineSituation S hp).A : Type u) (pairRing hp) _ (pairForms hp)
        (pairDerivation hp)) where
  carrier := wholeSpaceSections hp Fc ⦋0⦌
  isPAdicallyComplete := isPAdicallyComplete_pair hp Fc
  nabla := pairConnection hp Fc
  hasCoordinateOperators := ⟨_, isCoordinateExpansion_pairConnection hp Fc⟩
  isIntegrable := isIntegrable_pairConnection hp Fc
  isTopologicallyQuasiNilpotent := isTopologicallyQuasiNilpotent_pairConnection hp Fc

end PairObject

/-! ### Morphisms of crystals -/

section Morphisms

variable {Fc Gc : QuasiCoherentCrystal S}

/-- **The `D`-linear map `M_ℱ → M_𝒢` induced by a morphism of crystals**: the map of the limits of
the level sections, `...SmallSite.LevelScalars07JG.sectionsMap`. -/
def pairSectionsMap (psi : Fc ⟶ Gc) :
    wholeSpaceSections hp Fc ⦋0⦌ →ₗ[pairRing hp] wholeSpaceSections hp Gc ⦋0⦌ where
  toFun := (wholeSpaceLevelScalars hp 0).sectionsMap psi
  map_add' := map_add _
  map_smul' a m :=
    map_smul ((wholeSpaceLevelScalars hp 0).sectionsMap psi)
      ((wholeSpaceSystemEnvelopeRingEquiv hp 0).symm a)
      (show (wholeSpaceLevelScalars hp 0).sections Fc from m)

/-- `...SmallSite.pairSectionsMap` is the map of the limits of the level sections. -/
theorem pairSectionsMap_apply (psi : Fc ⟶ Gc) (m : wholeSpaceSections hp Fc ⦋0⦌) :
    pairSectionsMap hp psi m = (wholeSpaceLevelScalars hp 0).sectionsMap psi m := rfl

/-- The map of the sections over the level `e` induced by a morphism of crystals. -/
def pairLevelMap (psi : Fc ⟶ Gc) (e : ℕ) : pairLevel hp Fc e →ₗ[pairRing hp] pairLevel hp Gc e where
  toFun := crystalSectionsHom psi (levelObj hp 0 e)
  map_add' := map_add _
  map_smul' a x :=
    map_smul (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
      (op (levelObj hp 0 e))).hom (pairLss hp e a)
      (show Fc.obj.val.obj (op (levelObj hp 0 e)) from x)

/-- The first-order Taylor coefficients are natural in the crystal. -/
theorem pairFirstOrderHom_pairLevelMap (psi : Fc ⟶ Gc) (e : ℕ) (x : pairLevel hp Fc e) :
    pairFirstOrderHom hp Gc e (pairLevelMap hp psi e x) =
      (pairFirstOrderHom hp Fc e x).mapRange (pairLevelMap hp psi e) (map_zero _) :=
  Finsupp.ext fun _ ↦ levelTheta_naturality hp psi e _ x

/-- **The comparison data are natural in the crystal.** -/
theorem pairComparison_naturality (psi : Fc ⟶ Gc) (m : wholeSpaceSections hp Fc ⦋0⦌) :
    pairComparison hp Gc (pairSectionsMap hp psi m) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (pairRing hp : Type u)) S.p)
        (LinearMap.lTensor (firstOrderExtension (pairRing hp) (pairForms hp))
          (pairSectionsMap hp psi)) (pairComparison hp Fc m) :=
  completedLevelComparisonFun_naturality (wholeSpaceSections hp Fc ⦋0⦌)
    (wholeSpaceSections hp Gc ⦋0⦌) (pairLevel hp Fc) (pairRestrict hp Fc) (pairLevel hp Gc)
    (pairRestrict hp Gc) (_root_.Crystalline.uniformLevel (affineSituation S hp))
    (pairComponent hp Fc) (pairComponent hp Gc) (surjective_pairComponent hp Fc)
    (ker_pairComponent hp Fc) (pairRestrict_comp_pairComponent hp Fc)
    (surjective_pairComponent hp Gc) (ker_pairComponent hp Gc)
    (pairRestrict_comp_pairComponent hp Gc) (pairSectionsMap hp psi) (pairLevelMap hp psi)
    (fun _ ↦ LinearMap.ext fun _ ↦ rfl) (pairLevelComparison hp Fc)
    (pairLevelComparison_restrict hp Fc) (pairLevelComparison hp Gc)
    (pairLevelComparison_restrict hp Gc)
    (fun e x ↦ (lTensor_coordinateComparisonFun (pairRing hp) (pairForms hp) (pairDx hp)
      (pairFirstOrderHom hp Fc e) (pairFirstOrderHom hp Gc e) (pairLevelMap hp psi e)
      (pairFirstOrderHom_pairLevelMap hp psi e) x).symm) m

/-- **A morphism of crystals is horizontal for the connections.** -/
theorem pairConnection_naturality (psi : Fc ⟶ Gc) (m : wholeSpaceSections hp Fc ⦋0⦌) :
    pairConnection hp Gc (pairSectionsMap hp psi m) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (pairRing hp : Type u)) S.p)
        (TensorProduct.map (pairSectionsMap hp psi)
          (LinearMap.id (R := (pairRing hp : Type u)) (M := pairForms hp)))
        (pairConnection hp Fc m) := by
  change AdicCompletion.map (DividedPowers.pAdicIdeal (A := (pairRing hp : Type u)) S.p)
      (firstOrderDifferentialComm (pairRing hp) (pairForms hp) (wholeSpaceSections hp Gc ⦋0⦌))
      (pairComparison hp Gc (pairSectionsMap hp psi m)) = _
  refine (congrArg (AdicCompletion.map _ _) (pairComparison_naturality hp psi m)).trans ?_
  refine (AdicCompletion.map_comp_apply _ _ _ _).trans ?_
  refine (congrArg (fun φ ↦ AdicCompletion.map _ φ (pairComparison hp Fc m))
    (firstOrderDifferentialComm_comp_lTensor (pairRing hp) (pairForms hp)
      (wholeSpaceSections hp Fc ⦋0⦌) (pairSectionsMap hp psi))).trans ?_
  exact (AdicCompletion.map_comp_apply _ _ _ _).symm

end Morphisms

/-! ### The functor -/

/-- **[Stacks, Lemma 60.17.3, Tag 07JG]: the functor**

`{crystals in quasi-coherent 𝒪_{X/S}-modules on Cris(X/S)} ⟶ {pairs (M, ∇) satisfying (07JB),
(07JC), (07JD) and (07JE)}`,

in the situation of [Stacks, Section 60.17, Tag 07J7]: `X = Spec(C)`, `S = Spec(A)` affine with
`p` nilpotent on `C`, `P = A[x_i : i ∈ ι] → C` any surjective polynomial presentation (the
instance `...SmallSite.WholeSpacePresentation S hp` the system of thickenings is built from; by
default `A[x_c : c ∈ C] → C`), `D` the `p`-adically completed divided power envelope (07J8),
`Ω_D` its completed module of divided power differentials (07J9) and `d : D → Ω_D` (07JA).  It
sends a crystal `ℱ` to `M = lim_e Γ((X, T_e, δ̄), ℱ)` with the connection read off the crystal's
Taylor expansion over `D(1)`, and a morphism of crystals to the induced map of the limits.  That
this connection is the canonical connection of [Stacks, Tag 07J6] evaluated on the finite
thickenings `(X, T_e, δ̄)` is `...SmallSite.pairTensorLevel_crystalPairFunctor_nabla` and
`...SmallSite.firstOrderTensorInclusion_crystalConnection_crystalPairFunctor`. -/
@[stacks 07JG "the functor from the crystals in quasi-coherent O_{X/S}-modules on Cris(X/S) to \
the pairs (M, ∇) satisfying (07JB), (07JC), (07JD) and (07JE), for any surjective polynomial \
presentation g : P = A[x_i : i ∈ ι] → C, supplied as the WholeSpacePresentation instance (the \
default instance is the tautological one): M = lim_e Γ(T_e, F), \
∇ read off the Taylor expansion of the crystal over D(1); that ∇ is the 07J6 connection \
evaluated on the T_e is pairTensorLevel_crystalPairFunctor_nabla"]
def crystalPairFunctor :
    QuasiCoherentCrystal S ⥤ Pair.{u, u, u, u} S.p (pairRing hp) (pairForms hp) (pairDx hp)
      (derivationFun ((affineSituation S hp).A : Type u) (pairRing hp) _ (pairForms hp)
        (pairDerivation hp)) where
  obj Fc := crystalPair hp Fc
  map psi := { toLinearMap := pairSectionsMap hp psi
               horizontal := pairConnection_naturality hp psi }
  map_id Fc := PairHom.ext <| LinearMap.ext fun m ↦ LinearMap.congr_fun
    ((wholeSpaceLevelScalars hp 0).sectionsMap_id Fc) m
  map_comp psi chi := PairHom.ext <| LinearMap.ext fun m ↦ LinearMap.congr_fun
    ((wholeSpaceLevelScalars hp 0).sectionsMap_comp psi chi) m

/-- The module of the pair attached to `ℱ` is `M = lim_e Γ(T_e, ℱ)`. -/
@[simp] theorem crystalPairFunctor_obj_carrier (Fc : QuasiCoherentCrystal S) :
    ((crystalPairFunctor hp).obj Fc).carrier = wholeSpaceSections hp Fc ⦋0⦌ := rfl

/-- The connection of the pair attached to `ℱ` is `...SmallSite.pairConnection`. -/
theorem crystalPairFunctor_obj_nabla (Fc : QuasiCoherentCrystal S) :
    ((crystalPairFunctor hp).obj Fc).nabla = pairConnection hp Fc := rfl

/-- The map of pairs induced by a morphism of crystals is `...SmallSite.pairSectionsMap`. -/
theorem crystalPairFunctor_map_toLinearMap {Fc Gc : QuasiCoherentCrystal S} (psi : Fc ⟶ Gc) :
    ((crystalPairFunctor hp).map psi).toLinearMap = pairSectionsMap hp psi := rfl

end Crystalline.GlobalCrystallineSituation.SmallSite

end
