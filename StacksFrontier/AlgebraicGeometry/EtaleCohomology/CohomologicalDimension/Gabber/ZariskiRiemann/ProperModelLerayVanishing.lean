module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ProperStrictlyHenselianFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.TrdegSupportTwiceVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.LerayVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage

/-!
# The Leray step of Gabber's Zariski–Riemann argument, at one proper model

Let `B` be a strictly henselian local ring, `f : Y ⟶ Spec B` a proper morphism (in the source, a
proper birational modification of `Spec B`), `x : Spec Ω ⟶ Spec B` a geometric point over the
closed point, with geometric closed fibre `Y_Ω = Y ×_{Spec B} Spec Ω`, and `j : η ⟶ Y` an
arbitrary morphism (in the source, the inclusion of the generic point `η = Spec (Frac B)`). For
an abelian sheaf `F` on `η_étale` killed by `n > 0`, the Leray spectral sequence of `j` and the
identification `H^p(Y, -) = H^p(Y_Ω, -|_{Y_Ω})` on torsion sheaves give a spectral sequence

`E₂^{p,q} = H^p(Y_Ω, (R^q j_* F)|_{Y_Ω}) ⟹ H^{p+q}(η, F)`,

the finite-level form of the spectral sequence of Travaux de Gabber, Exposé XVIII-A, last remark
of §2 ("we have by proper base change a spectral sequence `H^p(Y₀, i^* R^q j_* F) ⟹
H^{p+q}(η, F)`"). This file proves the antidiagonal vanishing it yields, and combines it with
Gabber's `δ`-bound on the finite type `Ω`-scheme `Y_Ω`
(`AlgebraicGeometry.subsingleton_H_of_forall_mem_smallEtaleSupport_two_mul_lt`): if for every
`q ≤ m` every point `y` of the support of `(R^q j_* F)|_{Y_Ω}` has `2 trdeg_Ω κ(y) < m - q`, then
`H^m(η, F) = 0`.

In the source the hypothesis is verified only after passing to the limit over all proper
birational `Y`, where the support of the `q`-th direct image has transcendence degree at most
`min(d - 1, d - q)`; at one model it is a hypothesis.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_of_forall_geometricClosedFibre_rightDerived` — the
  antidiagonal vanishing: `H^m(η, F) = 0` if `H^{m-q}(Y_Ω, (R^q j_* F)|_{Y_Ω}) = 0` for all
  `q ≤ m`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_forall_geometricClosedFibre_support` — the same
  from the transcendence degrees of the supports.
* `Stacks.EtaleCohomology.isTorsionVanishingBound_of_forall_geometricClosedFibre_support` — the
  bound `cd_n(η) ≤ N` if, for every `F` killed by `n` and every `q`, every point of the support of
  `(R^q j_* F)|_{Y_Ω}` has `2 trdeg_Ω κ(y) + q ≤ N`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

variable {B : Type u} [CommRing B] [StrictlyHenselianLocalRing B] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (.of B)) [IsProper f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ Spec (.of B)) (hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint B)
  {η : Scheme.{u}} (j : η ⟶ Y)

/-- The higher direct images of a sheaf killed by `n > 0` are torsion. -/
theorem torsionSheafProperty_rightDerived_smallEtaleDirectImageAb_of_nsmul_eq_zero
    (F : Sheaf η.smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ} (hn : 0 < n)
    (hF : ∀ (T : η.Etale) (s : F.obj.obj (op T)), n • s = 0) (q : ℕ) :
    Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology
      (((smallEtaleDirectImageAb.{u + 1} j).rightDerived q).obj F) :=
  torsionSheafProperty_of_forall_nsmul_eq_zero hn
    ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero _).2
      (nsmul_id_obj_eq_zero _ ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero F).1 hF)))

include hx in
/-- **The antidiagonal vanishing of the spectral sequence
`H^p(Y_Ω, (R^q j_* F)|_{Y_Ω}) ⟹ H^{p+q}(η, F)`.** For `f : Y ⟶ Spec B` proper over a strictly
henselian local ring, a geometric point `x` over the closed point, `j : η ⟶ Y` arbitrary and `F`
killed by `n > 0`: `H^m(η, F) = 0` as soon as `H^{m-q}(Y_Ω, (R^q j_* F)|_{Y_Ω}) = 0` for every
`q ≤ m`. This is the Leray vanishing criterion (Stacks 0732) for `j`, with
`H^{m-q}(Y, R^q j_* F) = H^{m-q}(Y_Ω, (R^q j_* F)|_{Y_Ω})` by proper base change. -/
theorem subsingleton_sheafH_of_forall_geometricClosedFibre_rightDerived
    (F : Sheaf η.smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ} (hn : 0 < n)
    (hF : ∀ (T : η.Etale) (s : F.obj.obj (op T)), n • s = 0) (m : ℕ)
    (h : ∀ q : ℕ, q ≤ m → Subsingleton (Sheaf.H.{u + 1}
      ((etaleAbelianInverseImage.{u, 0} (pullback.fst f x)).obj
        (((smallEtaleDirectImageAb.{u + 1} j).rightDerived q).obj F)) (m - q))) :
    Subsingleton (Sheaf.H.{u + 1} F m) := by
  refine LerayVanishing.subsingleton_sheafH_of_forall_subsingleton_sheafH_rightDerived j F m
    fun q hq ↦ ?_
  have ht := torsionSheafProperty_rightDerived_smallEtaleDirectImageAb_of_nsmul_eq_zero j F hn hF q
  exact (subsingleton_sheafH_iff_geometricClosedFibre_of_isProper f x hx _ ht (m - q)).2 (h q hq)

include hx in
/-- **The Leray step with Gabber's `δ`-bound.** In the situation of
`Stacks.EtaleCohomology.subsingleton_sheafH_of_forall_geometricClosedFibre_rightDerived`, if for
every `q ≤ m` every point `y` of the support of `(R^q j_* F)|_{Y_Ω}` has
`2 trdeg_Ω κ(y) < m - q`, then `H^m(η, F) = 0`. -/
theorem subsingleton_sheafH_of_forall_geometricClosedFibre_support
    (F : Sheaf η.smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ} (hn : 0 < n)
    (hF : ∀ (T : η.Etale) (s : F.obj.obj (op T)), n • s = 0) (m : ℕ)
    (h : ∀ q : ℕ, q ≤ m → ∀ y ∈ smallEtaleSupport
      ((etaleAbelianInverseImage.{u, 0} (pullback.fst f x)).obj
        (((smallEtaleDirectImageAb.{u + 1} j).rightDerived q).obj F)),
      ∃ a : ℕ, 2 * a < m - q ∧ y ∈ Scheme.trdegLESet Ω (pullback.snd f x) a) :
    Subsingleton (Sheaf.H.{u + 1} F m) :=
  subsingleton_sheafH_of_forall_geometricClosedFibre_rightDerived f x hx j F hn hF m
    fun q hq ↦ subsingleton_H_of_forall_mem_smallEtaleSupport_two_mul_lt Ω (pullback.snd f x) _
      (torsionSheafProperty_etaleAbelianInverseImage.{u, 0} (pullback.fst f x) _
        (torsionSheafProperty_rightDerived_smallEtaleDirectImageAb_of_nsmul_eq_zero j F hn hF q))
      (m - q) (h q hq)

include hx in
/-- **A cohomological dimension bound from the supports on the geometric closed fibre.** If for
every abelian sheaf `F` on `η_étale` killed by `n > 0` and every `q`, every point `y` of the
support of `(R^q j_* F)|_{Y_Ω}` has `2 trdeg_Ω κ(y) + q ≤ N`, then `cd_n(η) ≤ N`. In Gabber's
argument (in the limit over all models) the support of the `q`-th direct image has transcendence
degree at most `min(d - 1, d - q)`, and `2 min(d - 1, d - q) + q ≤ 2d - 1`. -/
theorem isTorsionVanishingBound_of_forall_geometricClosedFibre_support {n : ℕ} (hn : 0 < n)
    (N : ℕ)
    (h : ∀ F : Sheaf η.smallEtaleTopology AddCommGrpCat.{u + 1},
      (∀ (T : η.Etale) (s : F.obj.obj (op T)), n • s = 0) → ∀ q : ℕ,
        ∀ y ∈ smallEtaleSupport ((etaleAbelianInverseImage.{u, 0} (pullback.fst f x)).obj
          (((smallEtaleDirectImageAb.{u + 1} j).rightDerived q).obj F)),
        ∃ a : ℕ, 2 * a + q ≤ N ∧ y ∈ Scheme.trdegLESet Ω (pullback.snd f x) a) :
    IsTorsionVanishingBound η n (N : WithBot ℕ∞) := by
  intro F hF m hm
  have hm' : N < m := by exact_mod_cast hm
  refine subsingleton_sheafH_of_forall_geometricClosedFibre_support f x hx j F hn hF m
    fun q _ y hy ↦ ?_
  obtain ⟨a, ha, hya⟩ := h F hF q y hy
  exact ⟨a, by omega, hya⟩

end Stacks.EtaleCohomology

end
