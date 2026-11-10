module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.KoszulContraction
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal

/-!
# The Koszul contraction of the exterior-power filtration of the Euler sequence

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree and write `X = ℙⁿ_R`,
`E = 𝒪_X(-1)^{⊕ (n+1)}` and `Ω = Ω_{X/R}`. The Euler sequence

`0 ⟶ Ω ⟶ E --g--> 𝒪_X ⟶ 0`

exhibits `Ω` as a subsheaf of `E` with invertible quotient, and
`StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltration` proves that the induced
two-step filtration

`0 ⟶ ⋀^{p+1} Ω ⟶ ⋀^{p+1} E ⟶ ⋀^p Ω ⟶ 0`

of each exterior power is short exact *at every stalk*, where it splits, while recording that no
global third arrow was available: the value of a morphism `⋀^{p+1} E ⟶ ⋀^p Ω` on a wedge of
local sections needs a splitting of the Euler sequence, which exists only locally.

**This file supplies the global morphism that replaces it, and computes its stalks.** The
morphism available globally is the *Koszul contraction* against `g`,

`ι_g : ⋀^{p+1} E ⟶ ⋀^p E`,

of `StacksFrontier.AlgebraicGeometry.ProjEulerSequence.KoszulContraction`, whose value on a wedge is
the alternating sum `∑ k, (-1)ᵏ g(sₖ) · (s₀ ∧ ⋯ ∧ ŝₖ ∧ ⋯ ∧ s_{p+1})` — a formula needing no
splitting. Its stalk is computed here, in two stages.

First, for an arbitrary sheaf of modules `M` on a topological space with a morphism
`φ : M ⟶ 𝒪` into the unit sheaf of modules, the stalk of `SheafOfModules.exteriorContraction` is
the module-level contraction `exteriorPower.contraction` against the functional on the stalk whose
value on a germ is the germ of the value of `φ`, under the comparison isomorphism
`(⋀ᵐ M)ₓ ≅ ⋀ᵐ(Mₓ)` of Stacks Tag 01CH. This is the identity the implementation notes of
`KoszulContraction` left open, and it is proved where the comparison is pinned down: on germs of
wedges of local sections, where both sides are the same alternating sum of germs.

Second, for the Euler sequence, the splitting `E_x ≅ Ω_x × 𝒪_x` of the stalk turns that
module-level contraction into something visibly in the image of `⋀^p` of the first arrow:
contraction against the projection to `𝒪_x` kills the first summand of
`⋀^{p+1}(Ω_x × 𝒪_x) ≅ ⋀^{p+1}(Ω_x) × ⋀^p(Ω_x)` and recovers the second, so the value of the
contraction at `x` is the image, under `⋀^p` of the first arrow, of the stalkwise projection
`eulerWedgeStalkProj` of the filtration. That is the stalkwise factorization which a global
factorization of `ι_g` through the monomorphism `⋀^p Ω ⟶ ⋀^p E` is read off.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkDual`: **the functional on the stalk of
  `E`** attached to the Euler surjection — the second component of the product decomposition
  `eulerStalkProdRingEquiv` of that stalk.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeContraction`: **the Koszul contraction
  `⋀^{p+1} E ⟶ ⋀^p E`** against the Euler surjection, for the chosen exterior algebra of `E` on
  the scheme `ℙⁿ_R`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerWedgeStalkEquivSelf`: the comparison
  isomorphism `(⋀^p E)ₓ ≅ ⋀^p(E_x)` of Tag 01CH for the middle term of the Euler sequence.

## Main results

* `exteriorPower.map_comp_contraction`: **contraction is natural in the module**,
  `⋀ᵖg ∘ ι_{ξ∘g} = ι_ξ ∘ ⋀^{p+1}g`.
* `exteriorPower.contraction_snd_prodRightEquiv_symm` and
  `exteriorPower.contraction_snd_eq_map_inl`: **contraction against the projection `M × S → S`
  lands in the image of `M → M × S`**, with value the second component of the splitting of
  `⋀^{p+1}(M × S)`.
* `SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_exteriorContraction`: **the stalk of the
  Koszul contraction on the exterior powers of a sheaf of modules is the module-level Koszul
  contraction of the stalk.** Its germ-level form is
  `SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_exteriorContraction_germ_ιMulti`.
* `SheafOfModules.exteriorPowerStalkEquiv_germ_extPowCmp_ιMulti`: the comparison isomorphism of
  Tag 01CH on the germ of a wedge of local sections, written with the comparison morphism of Tag
  01CG rather than with the ordered product in the graded algebra.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv_germ`: the identification of the
  stalk of the unit sheaf of modules with the stalk of the sheaf of rings carries a germ to the
  germ of the same section.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkDual_germ`: the value of the functional of
  the Euler surjection on a germ is the germ of the value of the Euler surjection.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.contraction_eulerStalkDual`: the module-level
  contraction against that functional, computed in the product decomposition of the stalk.
* `eulerWedgeStalkEquivSelf_stalkMapL_eulerWedgeContraction`, in the same namespace: **the
  stalk of the Koszul contraction is the stalkwise projection of the filtration**, pushed into
  `⋀^p E` along `⋀^p` of the first arrow of the Euler sequence.

## Implementation notes

**Why the scalars are moved one map at a time.** The germ-level identity is checked on the germ of
a wedge of local sections, where the contraction is an alternating sum with coefficients in the
ring of sections `𝒪(U)`. Three maps carry that sum into the stalk — the comparison morphism of
Tag 01CG, which is `𝒪(U)`-linear; the germ map, which is semilinear along `𝒪(U) → 𝒪ₓ`; and the
comparison isomorphism of Tag 01CH, which is `𝒪ₓ`-linear — so no single `map_sum` applies to the
composite. `SheafOfModules.germ_smul_sum_extPowCmp` moves the coefficients out one map at a time,
using `PresheafOfModules.germₛₗ` for the middle step, where `map_smulₛₗ` is available.

**This is the route the implementation notes of `KoszulContraction` prescribe, and the reason is
unchanged.** The natural proof — base change along the germ maps, `extPowStalkL_germ`, followed by
`Koszul.mapₛₗ_contraction` — compares the `CommRingCat` and `RingCat` spellings of the ring of
sections inside a single `ExteriorAlgebra`, which unfolds the Clifford quotient and does not
elaborate. Everything below instead stays at one spelling: the sectionwise formula
`SheafOfModules.extPowCmp_app_exteriorContraction_ιMulti` and
`Stacks.RegularSequence.koszulD_ιMulti` are both at the `RingCat` spelling, the passage to the
stalk is the germ map, and `exteriorPower.contraction_eq_koszulD` bridges the two module-level
spellings of the contraction at the end.

**`rw` is unusable on the module-level steps as well, for a different reason.** Rewriting with
`exteriorPower.map_comp` inside a goal about exterior powers of a stalk exhausts the heartbeat
budget while the unifier matches `⋀ᵖg ∘ₗ ⋀ᵖf`, in a declaration where only one ring is in play;
this is unification, not a spelling mismatch, and the cure is to apply `exteriorPower.map_comp` to
its arguments and use `DFunLike.congr_fun`. `contraction_eulerStalkDual` is written that way,
and it had to be split off from `eulerWedgeStalkEquivSelf_stalkMapL_eulerWedgeContraction`, which
exceeds the budget as a single declaration; `eulerWedgeStalkProj_eq`, which is `rfl`, is split
off for the same reason.

**A declaration binder may not reuse the name of a section variable**, so the degree and the point
are binders of each declaration below rather than section variables, in the order `(p, x)` that
`WedgeFiltration` uses.

**The germ formula for the stalk of the unit sheaf of modules is imported, not reproved.** It is
`LocallyFreeRank.unitStalkLEquiv_germ`, the germ formula of `LocallyFreeRank.unitStalkLEquiv`,
stated next to it; it is what turns the stalk of the Euler surjection into a functional with a
germ formula.

**No `@[stacks]` attribute.** Tag 062K is the definition of the Koszul complex, whose derivation
`KoszulContraction` already constructs, and Tag 01CH is the comparison isomorphism, already
carried elsewhere; the stalk of the contraction is a compatibility between the two and not an
assertion of either, so choosing a covering set is a judgement for the integrator.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf TopologicalSpace Opposite
open AlgebraicGeometry

universe u

/-! ### Contraction and functoriality of exterior powers of modules -/

namespace exteriorPower

section Naturality

variable {S : Type u} [CommRing S] {M N : Type u} [AddCommGroup M] [Module S M]
  [AddCommGroup N] [Module S N]

/-- **Contraction is natural in the module.** For `g : M ⟶ N` and a functional `ξ` on `N`,
pushing forward along `g` after contracting against `ξ ∘ g` is contracting against `ξ` after
pushing forward: both send a wedge `m₀ ∧ ⋯ ∧ mₚ` to
`∑ i, (-1)ⁱ ξ(g mᵢ) · (g m₀ ∧ ⋯ ∧ ĝ mᵢ ∧ ⋯ ∧ g mₚ)`. -/
theorem map_comp_contraction (ξ : N →ₗ[S] S) (g : M →ₗ[S] N) (m : ℕ) :
    map m g ∘ₗ contraction (ξ ∘ₗ g) m = contraction ξ m ∘ₗ map (m + 1) g := by
  refine linearMap_ext (AlternatingMap.ext fun v => ?_)
  simp only [LinearMap.compAlternatingMap_apply, Function.comp_apply, map_apply_ιMulti,
    contraction_ιMulti, map_sum, map_zsmul, LinearMap.map_smul_of_tower, LinearMap.comp_apply]
  rfl

end Naturality

section Prod

variable {S : Type u} [CommRing S] {M : Type u} [AddCommGroup M] [Module S M]

/-- **Contraction against the projection, read through the splitting of `⋀^{p+1}(M × S)`.** The
first summand of the splitting is killed by the contraction and the second is recovered from it,
so the contraction of `(prodRightEquiv S M p).symm (u, v)` is the image of `v` under
`M → M × S`. -/
theorem contraction_snd_prodRightEquiv_symm (m : ℕ) (z : ⋀[S]^(m + 1) M × ⋀[S]^m M) :
    contraction (LinearMap.snd S M S) m ((prodRightEquiv S M m).symm z) =
      map m (LinearMap.inl S M S) z.2 := by
  have hsi : LinearMap.snd S M S ∘ₗ LinearMap.inl S M S = 0 := LinearMap.ext fun _ => rfl
  have h1 : contraction (LinearMap.snd S M S) m (map (m + 1) (LinearMap.inl S M S) z.1) = 0 := by
    rw [← LinearMap.comp_apply, contraction_comp_map _ _ hsi m, LinearMap.zero_apply]
  have h2 : contraction (LinearMap.snd S M S) m
      (wedgeLeft ((0, 1) : M × S) m (map m (LinearMap.inl S M S) z.2)) =
      map m (LinearMap.inl S M S) z.2 := by
    simpa only [LinearMap.coe_comp, Function.comp_apply] using DFunLike.congr_fun
      (contraction_comp_wedgeLeft_comp_map (LinearMap.snd S M S) (LinearMap.inl S M S)
        ((0, 1) : M × S) rfl hsi m) z.2
  change contraction (LinearMap.snd S M S) m
    (map (m + 1) (LinearMap.inl S M S) z.1 +
      wedgeLeft ((0, 1) : M × S) m (map m (LinearMap.inl S M S) z.2)) = _
  rw [map_add, h1, h2, zero_add]

/-- **Contraction against the projection lands in the image of the first factor**, and its value
there is the second component of the splitting. -/
theorem contraction_snd_eq_map_inl (m : ℕ) (t : ⋀[S]^(m + 1) (M × S)) :
    contraction (LinearMap.snd S M S) m t =
      map m (LinearMap.inl S M S) (prodRightEquiv S M m t).2 := by
  simpa only [LinearEquiv.symm_apply_apply] using
    contraction_snd_prodRightEquiv_symm m (prodRightEquiv S M m t)

end Prod

end exteriorPower

/-! ### The stalk of the Koszul contraction on exterior powers of a sheaf of modules -/

namespace SheafOfModules

section ContractionStalk

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (gen : M ⟶ A.piece 1) (hA : GradedAlgebra.IsExteriorAlgebra A gen)

/-- **The comparison isomorphism of Tag 01CH on the germ of a wedge of local sections**, written
with the comparison morphism of Tag 01CG rather than with the ordered product in `A`. This is
`SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd` read through
`Stacks.GradedAlgebra.extCmpSections_ιMulti`. -/
theorem exteriorPowerStalkEquiv_germ_extPowCmp_ιMulti (m : ℕ) (x : ↥X) (U : Opens ↥X)
    (hx : x ∈ U) (s : Fin m → M.val.obj (op U)) :
    exteriorPowerStalkEquiv A gen hA m x
        (TopCat.Presheaf.germ (A.piece (m : ℤ)).val.presheaf U x hx
          ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property)
              gen hA.1 m).app (op U)
            (exteriorPower.ιMulti
              ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m s))) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) m
        fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) := by
  refine Eq.trans (congrArg (fun z => exteriorPowerStalkEquiv A gen hA m x
      (TopCat.Presheaf.germ (A.piece (m : ℤ)).val.presheaf U x hx z))
    (Stacks.GradedAlgebra.extCmpSections_ιMulti A.toPresheafGradedAlgebra gen.val
      (fun Y y => hA.1 Y y) m (op U) s)) ?_
  exact exteriorPowerStalkEquiv_germ_homogeneousProd A gen hA m x U hx s

variable (φ : M ⟶ SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp))

/-- A germ of a finite `O(U)`-linear combination of local sections of `⋀ᵐ M`, read through the
comparison of Tag 01CH, is the combination of the germs with the germs of the coefficients. The
three maps involved are linear, semilinear and linear over three different rings, so the
coefficients are moved out one map at a time. -/
theorem germ_smul_sum_extPowCmp (m : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (a : Fin (m + 1) → ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)))
    (w : Fin (m + 1) → (PresheafOfModules.extPow m M.val).obj (op U)) :
    exteriorPowerStalkEquiv A gen hA m x
        (TopCat.Presheaf.germ (A.piece (m : ℤ)).val.presheaf U x hx
          ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property)
              gen hA.1 m).app (op U) (∑ k, a k • w k))) =
      ∑ k, TopCat.Presheaf.germ Osharp.obj U x hx (a k) •
        exteriorPowerStalkEquiv A gen hA m x
          (TopCat.Presheaf.germ (A.piece (m : ℤ)).val.presheaf U x hx
            ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property)
                gen hA.1 m).app (op U) (w k))) := by
  change exteriorPowerStalkEquiv A gen hA m x
    (PresheafOfModules.germₛₗ (A.piece (m : ℤ)).val x U hx _) = _
  simp only [map_sum, map_smul, map_smulₛₗ]
  rfl

/-- The germ of a signed value of the sectionwise functional of `φ` is the signed value of a
functional on the stalk whose values on germs are the germs of the values. -/
theorem germ_sign_mul_unitDualApp (x : ↥X) (U : Opens ↥X) (hx : x ∈ U) (k : ℕ)
    (ψ : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk Osharp.obj x))
    (hψ : ∀ (V : Opens ↥X) (hv : x ∈ V) (t : M.val.obj (op V)),
      ψ (TopCat.Presheaf.germ M.val.presheaf V x hv t) =
        TopCat.Presheaf.germ Osharp.obj V x hv (unitDualApp φ (op V) t))
    (t : M.val.obj (op U)) :
    TopCat.Presheaf.germ Osharp.obj U x hx
        ((-1 : (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) ^ k *
          unitDualApp φ (op U) t) =
      (-1 : ↑(TopCat.Presheaf.stalk Osharp.obj x)) ^ k *
        ψ (TopCat.Presheaf.germ M.val.presheaf U x hx t) := by
  simp only [map_mul, map_pow, map_neg, map_one, hψ U hx t]

/-- **The stalk of the Koszul contraction on the germ of a wedge of local sections** is the
module-level contraction of the wedge of the germs. Both sides are the alternating sum
`∑ k, (-1)ᵏ ψ(sₖ) · (s₀ ∧ ⋯ ∧ ŝₖ ∧ ⋯ ∧ sₘ)` of germs. -/
theorem exteriorPowerStalkEquiv_stalkMapL_exteriorContraction_germ_ιMulti (m : ℕ) (x : ↥X)
    (ψ : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk Osharp.obj x))
    (hψ : ∀ (V : Opens ↥X) (hv : x ∈ V) (t : M.val.obj (op V)),
      ψ (TopCat.Presheaf.germ M.val.presheaf V x hv t) =
        TopCat.Presheaf.germ Osharp.obj V x hv (unitDualApp φ (op V) t))
    (U : Opens ↥X) (hx : x ∈ U) (s : Fin (m + 1) → M.val.obj (op U)) :
    exteriorPowerStalkEquiv A gen hA m x
        (PresheafOfModules.stalkMapL x (exteriorContraction M A gen hA φ m).val
          (TopCat.Presheaf.germ (A.piece ((m + 1 : ℕ) : ℤ)).val.presheaf U x hx
            ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property)
                gen hA.1 (m + 1)).app (op U)
              (exteriorPower.ιMulti
                ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (m + 1) s)))) =
      exteriorPower.contraction ψ m
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (m + 1)
          fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i)) := by
  have hterm : ∀ k : Fin (m + 1),
      TopCat.Presheaf.germ Osharp.obj U x hx
          ((-1 : (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) ^ (k : ℕ) *
            unitDualApp φ (op U) (s k)) •
          exteriorPowerStalkEquiv A gen hA m x
            (TopCat.Presheaf.germ (A.piece (m : ℤ)).val.presheaf U x hx
              ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property)
                  gen hA.1 m).app (op U)
                (exteriorPower.ιMulti
                  ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m
                  fun j => s (k.succAbove j)))) =
        ((-1 : ↑(TopCat.Presheaf.stalk Osharp.obj x)) ^ (k : ℕ) *
            ψ (TopCat.Presheaf.germ M.val.presheaf U x hx (s k))) •
          exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) m
            fun j => TopCat.Presheaf.germ M.val.presheaf U x hx (s (k.succAbove j)) := fun k =>
    congrArg₂ (· • ·) (germ_sign_mul_unitDualApp φ x U hx (k : ℕ) ψ hψ (s k))
      (exteriorPowerStalkEquiv_germ_extPowCmp_ιMulti A gen hA m x U hx fun j => s (k.succAbove j))
  refine Eq.trans (congrArg (exteriorPowerStalkEquiv A gen hA m x)
    (PresheafOfModules.stalkMapL_germ x (exteriorContraction M A gen hA φ m).val U hx _)) ?_
  refine Eq.trans (congrArg (fun z => exteriorPowerStalkEquiv A gen hA m x
      (TopCat.Presheaf.germ (A.piece (m : ℤ)).val.presheaf U x hx z))
    (extPowCmp_app_exteriorContraction_ιMulti M A gen hA φ m (op U) s)) ?_
  refine Eq.trans (germ_smul_sum_extPowCmp A gen hA m x U hx
    (fun k => (-1 : (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) ^ (k : ℕ) *
      unitDualApp φ (op U) (s k))
    (fun k => exteriorPower.ιMulti
      ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) m
      fun j => s (k.succAbove j))) ?_
  refine Eq.trans (Finset.sum_congr rfl fun k _ => hterm k) ?_
  exact Eq.trans
    (Stacks.RegularSequence.koszulD_ιMulti ψ m
      (fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i))).symm
    (DFunLike.congr_fun (exteriorPower.contraction_eq_koszulD ψ m) _).symm

/-- `SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_exteriorContraction` read on the inverse of
the comparison of Tag 01CH on the source. Both sides are linear and wedges of vectors span an
exterior power, so it suffices to check this on a wedge of germs; a finite family of germs is a
family of germs of sections over one neighbourhood. -/
theorem exteriorPowerStalkEquiv_stalkMapL_exteriorContraction_symm (m : ℕ) (x : ↥X)
    (ψ : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk Osharp.obj x))
    (hψ : ∀ (V : Opens ↥X) (hv : x ∈ V) (t : M.val.obj (op V)),
      ψ (TopCat.Presheaf.germ M.val.presheaf V x hv t) =
        TopCat.Presheaf.germ Osharp.obj V x hv (unitDualApp φ (op V) t))
    (w : ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(m + 1)
      ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    exteriorPowerStalkEquiv A gen hA m x
        (PresheafOfModules.stalkMapL x (exteriorContraction M A gen hA φ m).val
          ((exteriorPowerStalkEquiv A gen hA (m + 1) x).symm w)) =
      exteriorPower.contraction ψ m w := by
  have hgen : ∀ v : Fin (m + 1) → ↑(TopCat.Presheaf.stalk M.val.presheaf x),
      exteriorPowerStalkEquiv A gen hA m x
          (PresheafOfModules.stalkMapL x (exteriorContraction M A gen hA φ m).val
            ((exteriorPowerStalkEquiv A gen hA (m + 1) x).symm
              (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (m + 1) v))) =
        exteriorPower.contraction ψ m
          (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (m + 1) v) := by
    intro v
    refine (exists_germ_eq_family M x (m + 1) v).elim fun U h1 => h1.elim fun hx h2 =>
      h2.elim fun s hs => ?_
    have hv : v = fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) :=
      funext fun i => (hs i).symm
    subst hv
    have hsymm : (exteriorPowerStalkEquiv A gen hA (m + 1) x).symm
          (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (m + 1)
            fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i)) =
        TopCat.Presheaf.germ (A.piece ((m + 1 : ℕ) : ℤ)).val.presheaf U x hx
          ((A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property)
              gen hA.1 (m + 1)).app (op U)
            (exteriorPower.ιMulti
              ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) (m + 1) s)) :=
      (LinearEquiv.symm_apply_eq _).2
        (exteriorPowerStalkEquiv_germ_extPowCmp_ιMulti A gen hA (m + 1) x U hx s).symm
    refine Eq.trans (congrArg (fun y => exteriorPowerStalkEquiv A gen hA m x
      (PresheafOfModules.stalkMapL x (exteriorContraction M A gen hA φ m).val y)) hsymm) ?_
    exact exteriorPowerStalkEquiv_stalkMapL_exteriorContraction_germ_ιMulti A gen hA φ m x ψ hψ
      U hx s
  have hL : (exteriorPowerStalkEquiv A gen hA m x).toLinearMap ∘ₗ
        (PresheafOfModules.stalkMapL x (exteriorContraction M A gen hA φ m).val ∘ₗ
          (exteriorPowerStalkEquiv A gen hA (m + 1) x).symm.toLinearMap) =
      exteriorPower.contraction ψ m :=
    LinearMap.ext_on_range (exteriorPower.ιMulti_span _ (m + 1) _) hgen
  exact DFunLike.congr_fun hL w

/-- **The stalk of the Koszul contraction is the Koszul contraction of the stalk.** For a
morphism `φ : M ⟶ 𝒪` into the unit sheaf of modules and a functional `ψ` on the stalk whose
value on a germ is the germ of the value of `φ`, the stalk at `x` of
`SheafOfModules.exteriorContraction` is `exteriorPower.contraction ψ`, under the comparison
isomorphism `(⋀ᵐ M)ₓ ≅ ⋀ᵐ(Mₓ)` of Tag 01CH. -/
theorem exteriorPowerStalkEquiv_stalkMapL_exteriorContraction (m : ℕ) (x : ↥X)
    (ψ : ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk Osharp.obj x))
    (hψ : ∀ (V : Opens ↥X) (hv : x ∈ V) (t : M.val.obj (op V)),
      ψ (TopCat.Presheaf.germ M.val.presheaf V x hv t) =
        TopCat.Presheaf.germ Osharp.obj V x hv (unitDualApp φ (op V) t))
    (t : ↑(TopCat.Presheaf.stalk (A.piece ((m + 1 : ℕ) : ℤ)).val.presheaf x)) :
    exteriorPowerStalkEquiv A gen hA m x
        (PresheafOfModules.stalkMapL x (exteriorContraction M A gen hA φ m).val t) =
      exteriorPower.contraction ψ m (exteriorPowerStalkEquiv A gen hA (m + 1) x t) := by
  simpa only [LinearEquiv.symm_apply_apply] using
    exteriorPowerStalkEquiv_stalkMapL_exteriorContraction_symm A gen hA φ m x ψ hψ
      (exteriorPowerStalkEquiv A gen hA (m + 1) x t)

end ContractionStalk

end SheafOfModules

/-! ### The quotient arrow of the filtration -/

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! #### The stalk of the unit sheaf of modules, on germs -/

section UnitGerm

variable {X : TopCat.{u}} (Oc : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}) (x : ↥X)

/-- **The identification of the stalk of the unit sheaf of modules with the stalk of the sheaf of
rings carries a germ to the germ of the same section.** This is the germ formula of
`LocallyFreeRank.unitStalkLEquiv` composed with that of
`SemilinearStalk.commStalkRingEquiv`, the two identifications
`Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv` is built from. -/
theorem unitStalkCommEquiv_germ (U : Opens ↥X) (hx : x ∈ U)
    (r : (SheafOfModules.unit (ringSheafOfComm Oc)).val.obj (op U)) :
    unitStalkCommEquiv Oc x
        (TopCat.Presheaf.germ (SheafOfModules.unit (ringSheafOfComm Oc)).val.presheaf U x hx r) =
      TopCat.Presheaf.germ Oc.obj U x hx r :=
  Eq.trans (congrArg (SemilinearStalk.commStalkRingEquiv Oc.obj x)
      (LocallyFreeRank.unitStalkLEquiv_germ
        (Oc.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x U hx r))
    (SemilinearStalk.commStalkRingEquiv_germ Oc.obj x U hx r)

end UnitGerm

/-! #### The contraction against the second arrow of the Euler sequence -/

section Euler

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **The functional on the stalk of `𝒪_X(-1)^{⊕ (n+1)}` attached to the second arrow of the
Euler sequence**: the second component of the product decomposition
`Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkProdRingEquiv`, which is the stalk of the
Euler surjection with its target read as the local ring. -/
def eulerStalkDual (x : ProjectiveSpectrum.top (polyGrading R n)) :=
  LinearMap.snd _ _ _ ∘ₗ (eulerStalkProdRingEquiv R n x).toLinearMap

/-- The value of `eulerStalkDual` on a germ is the germ of the value of the Euler surjection.
This is the hypothesis `SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_exteriorContraction`
takes. -/
theorem eulerStalkDual_germ (x : ProjectiveSpectrum.top (polyGrading R n))
    (V : Opens (ProjectiveSpectrum.top (polyGrading R n))) (hv : x ∈ V)
    (t : (twistMinusOneSum R n).val.obj (op V)) :
    eulerStalkDual R n x (TopCat.Presheaf.germ (twistMinusOneSum R n).val.presheaf V x hv t) =
      TopCat.Presheaf.germ
        (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj V x hv
        (SheafOfModules.unitDualApp (eulerSurjection R n) (op V) t) := by
  refine Eq.trans (congrArg (unitStalkCommEquiv
      (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)) x)
    (PresheafOfModules.stalkMapL_germ x (eulerSurjection R n).val V hv t)) ?_
  exact unitStalkCommEquiv_germ
    (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)) x V hv _

/-- **The Koszul contraction `⋀^{p+1}(𝒪_X(-1)^{⊕ (n+1)}) ⟶ ⋀^p(𝒪_X(-1)^{⊕ (n+1)})` against the
second arrow of the Euler sequence.** This is `SheafOfModules.exteriorContraction` of the Euler
surjection, for the chosen exterior algebra of `𝒪_X(-1)^{⊕ (n+1)}` on the scheme `ℙⁿ_R`. -/
def eulerWedgeContraction (p : ℕ) :=
  SheafOfModules.exteriorContraction
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (twistMinusOneSum R n)
    (Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n))
    (eulerSurjection R n) p

/-- **The stalk of `⋀^p(𝒪_X(-1)^{⊕ (n+1)})` is `⋀^p` of the stalk**: the comparison isomorphism
of Tag 01CH in degree `p` for the middle term of the Euler sequence. -/
def eulerWedgeStalkEquivSelf (p : ℕ) (x : ProjectiveSpectrum.top (polyGrading R n)) :=
  SheafOfModules.exteriorPowerStalkEquiv
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n))
    p x

/-- The functional of the Euler surjection, read through the product decomposition of the stalk,
is the projection onto the second factor. -/
theorem eulerStalkDual_comp_eulerStalkProdRingEquiv_symm
    (x : ProjectiveSpectrum.top (polyGrading R n)) :
    eulerStalkDual R n x ∘ₗ (eulerStalkProdRingEquiv R n x).symm.toLinearMap =
      LinearMap.snd _ _ _ :=
  LinearMap.ext fun y => congrArg Prod.snd ((eulerStalkProdRingEquiv R n x).apply_symm_apply y)

/-- The product decomposition of the stalk carries the inclusion of the first factor to the stalk
of the first arrow of the Euler sequence. -/
theorem eulerStalkProdRingEquiv_symm_comp_inl
    (x : ProjectiveSpectrum.top (polyGrading R n)) :
    (eulerStalkProdRingEquiv R n x).symm.toLinearMap ∘ₗ LinearMap.inl _ _ _ =
      PresheafOfModules.stalkMapL x (eulerFirstArrow R n).val :=
  LinearMap.ext fun z => ((eulerStalkProdRingEquiv R n x).symm_apply_eq).2
    (eulerStalkProdRingEquiv_stalkMapL R n x z).symm

/-- **The module-level contraction against the functional of the Euler surjection**, computed in
the product decomposition of the stalk: it is the second component of the splitting of
`⋀^{p+1}(Ω_x × 𝒪_x)`, pushed into `⋀^p` of the stalk of `𝒪_X(-1)^{⊕ (n+1)}` along the stalk of
the first arrow of the Euler sequence. -/
theorem contraction_eulerStalkDual (p : ℕ)
    (x : ProjectiveSpectrum.top (polyGrading R n))
    (u : ⋀[projStalkRing R n x]^(p + 1)
      ↑(TopCat.Presheaf.stalk (twistMinusOneSum R n).val.presheaf x)) :
    exteriorPower.contraction (eulerStalkDual R n x) p u =
      exteriorPower.map p (PresheafOfModules.stalkMapL x (eulerFirstArrow R n).val)
        (exteriorPower.prodRightEquiv _ _ p
          (exteriorPower.map (p + 1) (eulerStalkProdRingEquiv R n x).toLinearMap u)).2 := by
  have hid : (eulerStalkProdRingEquiv R n x).symm.toLinearMap ∘ₗ
      (eulerStalkProdRingEquiv R n x).toLinearMap = LinearMap.id :=
    LinearMap.ext fun y => (eulerStalkProdRingEquiv R n x).symm_apply_apply y
  have hround : exteriorPower.map (p + 1) (eulerStalkProdRingEquiv R n x).symm.toLinearMap
        (exteriorPower.map (p + 1) (eulerStalkProdRingEquiv R n x).toLinearMap u) = u :=
    Eq.trans (DFunLike.congr_fun (exteriorPower.map_comp (n := p + 1)
        (eulerStalkProdRingEquiv R n x).toLinearMap
        (eulerStalkProdRingEquiv R n x).symm.toLinearMap) u).symm
      (Eq.trans (congrArg (fun L => exteriorPower.map (p + 1) L u) hid)
        (DFunLike.congr_fun exteriorPower.map_id u))
  refine Eq.trans (congrArg (exteriorPower.contraction (eulerStalkDual R n x) p) hround.symm) ?_
  refine Eq.trans (DFunLike.congr_fun (exteriorPower.map_comp_contraction
    (eulerStalkDual R n x) (eulerStalkProdRingEquiv R n x).symm.toLinearMap p)
      (exteriorPower.map (p + 1) (eulerStalkProdRingEquiv R n x).toLinearMap u)).symm ?_
  refine Eq.trans (congrArg (fun L => exteriorPower.map p
      (eulerStalkProdRingEquiv R n x).symm.toLinearMap (exteriorPower.contraction L p
        (exteriorPower.map (p + 1) (eulerStalkProdRingEquiv R n x).toLinearMap u)))
    (eulerStalkDual_comp_eulerStalkProdRingEquiv_symm R n x)) ?_
  refine Eq.trans (congrArg (exteriorPower.map p
      (eulerStalkProdRingEquiv R n x).symm.toLinearMap)
    (exteriorPower.contraction_snd_eq_map_inl p
      (exteriorPower.map (p + 1) (eulerStalkProdRingEquiv R n x).toLinearMap u))) ?_
  refine Eq.trans (DFunLike.congr_fun (exteriorPower.map_comp (n := p)
      (LinearMap.inl _ _ _) (eulerStalkProdRingEquiv R n x).symm.toLinearMap)
    (exteriorPower.prodRightEquiv _ _ p
      (exteriorPower.map (p + 1) (eulerStalkProdRingEquiv R n x).toLinearMap u)).2).symm ?_
  exact congrArg (fun L => exteriorPower.map p L
      (exteriorPower.prodRightEquiv _ _ p
        (exteriorPower.map (p + 1) (eulerStalkProdRingEquiv R n x).toLinearMap u)).2)
    (eulerStalkProdRingEquiv_symm_comp_inl R n x)

/-- The stalkwise projection of the filtration, written out as the second component of the
splitting of `⋀^{p+1}` of the product decomposition of the stalk. -/
theorem eulerWedgeStalkProj_eq (p : ℕ)
    (x : ProjectiveSpectrum.top (polyGrading R n))
    (w : eulerWedgeGerm R n x ((p + 1 : ℕ) : ℤ)) :
    eulerWedgeStalkProj R n p x w =
      (exteriorPower.prodRightEquiv _ _ p
        (exteriorPower.map (p + 1) (eulerStalkProdRingEquiv R n x).toLinearMap
          (eulerWedgeStalkEquivSelf R n (p + 1) x w))).2 := rfl

/-- **The stalk of the Koszul contraction is the stalkwise projection of the filtration, pushed
into `⋀^p(𝒪_X(-1)^{⊕ (n+1)})` along `⋀^p` of the first arrow of the Euler sequence.**

This is the computation that makes the contraction factor through `⋀^p Ω_{X/R}`: the stalk of the
contraction is `exteriorPower.contraction` against the functional of the Euler surjection, and in
the product decomposition of the stalk that contraction is the inclusion of the first factor
applied to the second component, which is the stalkwise projection. -/
theorem eulerWedgeStalkEquivSelf_stalkMapL_eulerWedgeContraction (p : ℕ)
    (x : ProjectiveSpectrum.top (polyGrading R n))
    (w : eulerWedgeGerm R n x ((p + 1 : ℕ) : ℤ)) :
    eulerWedgeStalkEquivSelf R n p x
        (PresheafOfModules.stalkMapL x (eulerWedgeContraction R n p).val w) =
      exteriorPower.map p (PresheafOfModules.stalkMapL x (eulerFirstArrow R n).val)
        (eulerWedgeStalkProj R n p x w) := by
  refine Eq.trans (SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_exteriorContraction
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (Scheme.Modules.exteriorAlgebra (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.exteriorGenerator (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n))
    (eulerSurjection R n) p x (eulerStalkDual R n x) (eulerStalkDual_germ R n x) w) ?_
  refine Eq.trans (contraction_eulerStalkDual R n p x
    (eulerWedgeStalkEquivSelf R n (p + 1) x w)) ?_
  exact congrArg (exteriorPower.map p
    (PresheafOfModules.stalkMapL x (eulerFirstArrow R n).val))
    (eulerWedgeStalkProj_eq R n p x w).symm

end Euler

end Stacks.AlgebraicGeometry.ProjEulerSequence

end

