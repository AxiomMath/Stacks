module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumCompletedSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumMilnorTriangleComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationMaximalIdeal
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZero
public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZeroConsequences
public import StacksFrontier.RingTheory.LocalCohomology.PuncturedSpectrumDescendingChain

/-!
# The first derived inverse limit of the local cohomologies of the adic quotients

Let `A` be a commutative ring, `T ⊆ Spec(A)` a subset, `I ⊆ A` an ideal and `M` an `A`-module.
Write `Bₙ = H^s_T(M/IⁿM)` for the inverse system of local cohomology modules of the adic
quotients of `M`. This module carries out the last paragraph of the proof of [Stacks, Tag 0EFY]:
it constructs the subsystem that paragraph uses, computes the images of its transition maps, and
deduces part (7) of the tag — that `I^{m₀}` annihilates the first derived inverse limit
`R¹lim Bₙ` — from the Mittag-Leffler condition for that subsystem.

The first derived inverse limit of a tower is the cokernel of its Milnor difference
`(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))` on the product of its terms, by Tag 07KW.

## The argument

Fix `m₀` and let `Aₙ ⊆ Bₙ` be the kernel of the transition map `Bₙ → B_{m₀}` for `n ≥ m₀`, and
the zero submodule for `n < m₀`. Three facts about it are proved here.

*It is a subsystem.* The transition `Bₚ → B_q` carries `Aₚ` into `A_q`: for `m₀ ≤ q` because
`Bₚ → B_q → B_{m₀}` is `Bₚ → B_{m₀}`, and for `q < m₀ ≤ p` because then `Bₚ → B_q` itself
factors through `B_{m₀}`, on which `Aₚ` dies.

*Multiplication by `a ∈ I^{m₀}` carries `Bₙ` into `Aₙ`.* For `n ≥ m₀` because `a` annihilates
`B_{m₀} = H^s_T(M/I^{m₀}M)`, that module being a local cohomology module of a module killed by
`I^{m₀}`; for `n < m₀` because then `a ∈ I^{m₀} ⊆ Iⁿ` annihilates `Bₙ` itself, so the image is
zero, which is what `Aₙ` is there. So multiplication by `a` is a map of towers `B ⟶ A` whose
composite with the inclusion `A ⟶ B` is `a` times the identity.

*Its transition images are cut out by those of `B`.* For `m₀ ≤ i ≤ k` the image of `A_k → Aᵢ` is
the part of the image of `B_k → Bᵢ` lying in `Aᵢ`: if `x ∈ Aᵢ` is the image of some `w ∈ B_k`
then `w` dies in `B_{m₀}`, because `Bᵢ → B_{m₀}` and `B_k → Bᵢ → B_{m₀}` are the same map, so
`w` already lies in `A_k`.

The first two give part (7) from the Mittag-Leffler condition for `A`, without touching an
element of a product: that condition makes the Milnor difference `d_A` an epimorphism, so the
composite `∏ Aₙ ⟶ ∏ Bₙ ⟶ R¹lim B` — which `d_A` annihilates — vanishes; multiplication by `a`
on `∏ Bₙ` factors through `∏ Aₙ`, so `a` times the projection `∏ Bₙ ⟶ R¹lim B` is zero, and
that projection is an epimorphism. The third is the computation on which a proof of the
Mittag-Leffler condition for `A` would rest.

## Main definitions

* `Stacks.LocalCohomology.firstDerivedLimitLocalCohomologyAdicTower` — the first derived inverse
  limit `R¹lim H^s_T(M/IⁿM)`, as the cokernel of the Milnor difference of the tower.
* `Stacks.LocalCohomology.adicTowerCollapseKernel` and
  `Stacks.LocalCohomology.adicTowerCollapseKernelTower` — the subsystem `Aₙ` above, with its
  inclusion `Stacks.LocalCohomology.adicTowerCollapseKernelι` into the tower and the
  multiplication map `Stacks.LocalCohomology.adicTowerCollapseKernelσ` into it.

## Main results

* `Stacks.LocalCohomology.smul_mem_adicTowerCollapseKernel` — an element of `I^{m₀}` carries the
  tower into the subsystem.
* `Stacks.LocalCohomology.range_adicTowerCollapseKernelTower_map_eq` — the images of the
  transition maps of the subsystem, as the part of the images of those of the tower lying in it.
* `smul_id_firstDerivedLimitLocalCohomologyAdicTower_eq_zero_of_isMittagLeffler`
  — part (7) of [Stacks, Tag 0EFY] from the Mittag-Leffler condition for the subsystem.
* `Stacks.LocalCohomology.smul_id_firstDerivedLimitLocalCohomologyAdicTower_eq_zero_closedPoint`
  — **part (7) of [Stacks, Tag 0EFY] at `T = {𝔪}` over a Noetherian local ring**, with that
  condition discharged, and with it the whole part: there `{H^s_𝔪(M/IⁿM)}` is itself
  Mittag-Leffler, by `isArtinian_localCohomologyWithSupportIn_closedPoint` and
  `isMittagLefflerCategorical_localCohomologyAdicTower_closedPoint` of
  `EssentiallyConstantConsequences.lean`, so the first derived limit vanishes outright.

## Implementation notes

The subsystem is cut out by the transition map down to the fixed index `m₀` rather than, as in
the source, as the image of `H^s_T(I^{m₀}M/IⁿM) → H^s_T(M/IⁿM)`. The two agree, by the long
exact sequence of `0 → I^{m₀}M/IⁿM → M/IⁿM → M/I^{m₀}M → 0`, but the kernel description needs
neither that sequence nor the tower `n ↦ H^s_T(I^{m₀}M/IⁿM)`.

Because the submodule is defined by a case distinction on `m₀ ≤ n`, and the target `B_{m₀}` of
the defining map does not vary with `n`, the definition involves no transport along an equality
of indices.

*Where the general locus is.* Part (7) is registered here at `T = {𝔪}` over a Noetherian local
ring, where the Mittag-Leffler condition is a theorem. At a general specialization-stable `T` the
hypothesis of the main result — that `{Aₙ}` satisfies the Mittag-Leffler condition — is proved in
`StacksFrontier/AlgebraicGeometry/Algebraization/BootstrapFirstDerivedLimitAnnihilation.lean`
directly from the stable-image assertion of [Stacks, Tag 0EFX], by the kernel description of
`{Aₙ}` together with the long exact sequence; so neither the truncated tower
`n ↦ H^s_T(I^{m₀}M/IⁿM)` nor its identification with `{Aₙ}` is needed, and the source's appeal to
part (3) and to Homology Lemma 12.31.3 is replaced. Part (7) at that locus is
`Stacks.Algebraization.exists_smul_id_firstDerivedLimitLocalCohomologyAdicTower_eq_zero`.

The hypothesis is deliberately *not* the Mittag-Leffler condition for `{H^s_T(M/IⁿM)}` itself.
Part (2) of the tag asserts that condition only in degrees `i < s`, and part (3) asserts it in
degrees `i ≤ s` only for the truncated system; in degree exactly `s` the system `{H^s_T(M/IⁿM)}`
is not asserted to satisfy it, and assuming it would make part (7) vacuous, a Mittag-Leffler
tower having vanishing first derived limit outright.

## References

* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

variable (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{max u v} A) (s : ℤ) (m₀ : ℕ)

/-! ### The first derived inverse limit of the tower -/

/-- The Milnor difference `(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))` of the tower `{H^i_T(M/IⁿM)}`, the
endomorphism of the product of its terms whose cokernel is its first derived inverse limit. -/
def milnorDifferenceLocalCohomologyAdicTower :
    (∏ᶜ fun n : ℕ ↦ (localCohomologyAdicTower.{u, v} A T I s M).obj (op n)) ⟶
      ∏ᶜ fun n : ℕ ↦ (localCohomologyAdicTower.{u, v} A T I s M).obj (op n) :=
  Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ (localCohomologyAdicTower.{u, v} A T I s M).obj (op n)) n -
      Pi.π (fun n : ℕ ↦ (localCohomologyAdicTower.{u, v} A T I s M).obj (op n)) (n + 1) ≫
        (localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE (Nat.le_succ n)).op

/-- **The first derived inverse limit `R¹lim H^i_T(M/IⁿM)`**, as the cokernel of the Milnor
difference of the tower. That this computes the first right derived functor of the inverse limit
is [Stacks, Tag 07KW]. -/
def firstDerivedLimitLocalCohomologyAdicTower : ModuleCat.{max u v} A :=
  cokernel (milnorDifferenceLocalCohomologyAdicTower.{u, v} T I M s)

/-! ### The subsystem cut out by the transition map to level `m₀` -/

/-- The kernel of the transition map `H^s_T(M/IⁿM) → H^s_T(M/I^{m₀}M)` for `n ≥ m₀`, and the
zero submodule for `n < m₀`. By the long exact sequence of
`0 → I^{m₀}M/IⁿM → M/IⁿM → M/I^{m₀}M → 0` this is the image of
`H^s_T(I^{m₀}M/IⁿM) → H^s_T(M/IⁿM)`, which is the subsystem the source uses. -/
def adicTowerCollapseKernel (n : ℕ) :
    Submodule A ((localCohomologyAdicTower.{u, v} A T I s M).obj (op n)) :=
  if h : m₀ ≤ n then
    LinearMap.ker ((localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE h).op).hom
  else ⊥

/-- Above level `m₀` the subsystem is the kernel of the transition map down to level `m₀`. -/
theorem mem_adicTowerCollapseKernel_iff {n : ℕ} (h : m₀ ≤ n)
    (x : (localCohomologyAdicTower.{u, v} A T I s M).obj (op n)) :
    x ∈ adicTowerCollapseKernel.{u, v} T I M s m₀ n ↔
      ((localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE h).op).hom x = 0 := by
  rw [adicTowerCollapseKernel, dif_pos h]
  exact LinearMap.mem_ker

/-- Below level `m₀` the subsystem is zero. -/
theorem adicTowerCollapseKernel_of_lt {n : ℕ} (h : ¬ m₀ ≤ n) :
    adicTowerCollapseKernel.{u, v} T I M s m₀ n = ⊥ := by
  rw [adicTowerCollapseKernel, dif_neg h]

/-- Two consecutive transition maps of the tower compose to the transition map between the
extreme indices. -/
private theorem localCohomologyAdicTower_map_comp_map {p q r : ℕ} (hqp : q ≤ p) (hrq : r ≤ q) :
    (localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE hqp).op ≫
        (localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE hrq).op =
      (localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE (hrq.trans hqp)).op := by
  rw [← Functor.map_comp]
  exact congrArg (localCohomologyAdicTower.{u, v} A T I s M).map (Subsingleton.elim _ _)

/-- The transition maps of the tower carry the subsystem into itself. -/
theorem adicTowerCollapseKernel_map_mem {p q : ℕ} (hqp : q ≤ p)
    {x : (localCohomologyAdicTower.{u, v} A T I s M).obj (op p)}
    (hx : x ∈ adicTowerCollapseKernel.{u, v} T I M s m₀ p) :
    ((localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE hqp).op).hom x ∈
      adicTowerCollapseKernel.{u, v} T I M s m₀ q := by
  by_cases hq : m₀ ≤ q
  · have hp : m₀ ≤ p := hq.trans hqp
    rw [mem_adicTowerCollapseKernel_iff.{u, v} T I M s m₀ hq]
    have hfac := localCohomologyAdicTower_map_comp_map.{u, v} T I M s hqp hq
    have := congrArg (fun φ : (localCohomologyAdicTower.{u, v} A T I s M).obj (op p) ⟶
      (localCohomologyAdicTower.{u, v} A T I s M).obj (op m₀) ↦ φ.hom x) hfac
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
    rw [this]
    have hxp : ((localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE hp).op).hom x = 0 :=
      (mem_adicTowerCollapseKernel_iff.{u, v} T I M s m₀ hp x).mp hx
    have hrw : (homOfLE (hq.trans hqp) : (m₀ : ℕ) ⟶ p) = homOfLE hp := Subsingleton.elim _ _
    rw [hrw, hxp]
  · rw [adicTowerCollapseKernel_of_lt.{u, v} T I M s m₀ hq, Submodule.mem_bot]
    by_cases hp : m₀ ≤ p
    · have hqm : q ≤ m₀ := le_of_not_ge hq
      have hfac := localCohomologyAdicTower_map_comp_map.{u, v} T I M s hp hqm
      have hxp : ((localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE hp).op).hom x = 0 :=
        (mem_adicTowerCollapseKernel_iff.{u, v} T I M s m₀ hp x).mp hx
      have hcomp := congrArg (fun φ : (localCohomologyAdicTower.{u, v} A T I s M).obj (op p) ⟶
        (localCohomologyAdicTower.{u, v} A T I s M).obj (op q) ↦ φ.hom x) hfac
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hcomp
      rw [hxp, map_zero] at hcomp
      have hrw : (homOfLE hqp : q ⟶ p) = homOfLE (hqm.trans hp) := Subsingleton.elim _ _
      rw [hrw, ← hcomp]
    · rw [adicTowerCollapseKernel_of_lt.{u, v} T I M s m₀ hp, Submodule.mem_bot] at hx
      rw [hx, map_zero]

/-- The transition maps of the tower carry the subsystem into itself, for an arbitrary morphism
of the index category. -/
theorem adicTowerCollapseKernel_map_mem' {p q : ℕᵒᵖ} (f : p ⟶ q)
    {x : (localCohomologyAdicTower.{u, v} A T I s M).obj p}
    (hx : x ∈ adicTowerCollapseKernel.{u, v} T I M s m₀ p.unop) :
    ((localCohomologyAdicTower.{u, v} A T I s M).map f).hom x ∈
      adicTowerCollapseKernel.{u, v} T I M s m₀ q.unop := by
  have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
  rw [hf]
  exact adicTowerCollapseKernel_map_mem.{u, v} T I M s m₀ (leOfHom f.unop) hx

/-- **The subsystem `Aₙ`**, as a tower of `A`-modules: the kernel of the transition map
`H^s_T(M/IⁿM) → H^s_T(M/I^{m₀}M)` above level `m₀`, and zero below it. -/
def adicTowerCollapseKernelTower : ℕᵒᵖ ⥤ ModuleCat.{max u v} A where
  obj n := ModuleCat.of A ↥(adicTowerCollapseKernel.{u, v} T I M s m₀ n.unop)
  map {p q} f := ModuleCat.ofHom
    (LinearMap.restrict ((localCohomologyAdicTower.{u, v} A T I s M).map f).hom
      (fun _ hx ↦ adicTowerCollapseKernel_map_mem'.{u, v} T I M s m₀ f hx))
  map_id n := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp

/-- The inclusion of the subsystem into the tower. -/
def adicTowerCollapseKernelι :
    adicTowerCollapseKernelTower.{u, v} T I M s m₀ ⟶ localCohomologyAdicTower.{u, v} A T I s M where
  app n := ModuleCat.ofHom (adicTowerCollapseKernel.{u, v} T I M s m₀ n.unop).subtype
  naturality _ _ _ := rfl

/-! ### Multiplication by an element of `I^{m₀}` lands in the subsystem -/

/-- An element of `I^{m₀}` carries `H^s_T(M/IⁿM)` into the subsystem: above level `m₀` because it
annihilates `H^s_T(M/I^{m₀}M)`, below level `m₀` because it then annihilates `H^s_T(M/IⁿM)`
itself. -/
theorem smul_mem_adicTowerCollapseKernel {a : A} (ha : a ∈ I ^ m₀) (n : ℕ)
    (x : (localCohomologyAdicTower.{u, v} A T I s M).obj (op n)) :
    a • x ∈ adicTowerCollapseKernel.{u, v} T I M s m₀ n := by
  by_cases hn : m₀ ≤ n
  · rw [mem_adicTowerCollapseKernel_iff.{u, v} T I M s m₀ hn, map_smul]
    exact smul_eq_zero_localCohomologyAdicTower.{u, v} T I s M m₀ ha _
  · rw [adicTowerCollapseKernel_of_lt.{u, v} T I M s m₀ hn, Submodule.mem_bot]
    have han : a ∈ I ^ n := Ideal.pow_le_pow_right (le_of_not_ge hn) ha
    exact smul_eq_zero_localCohomologyAdicTower.{u, v} T I s M n han x

/-- Multiplication by an element of `I^{m₀}`, read as a map of towers from `{H^s_T(M/IⁿM)}` to
the subsystem. -/
def adicTowerCollapseKernelσ {a : A} (ha : a ∈ I ^ m₀) :
    localCohomologyAdicTower.{u, v} A T I s M ⟶ adicTowerCollapseKernelTower.{u, v} T I M s m₀ where
  app n := ModuleCat.ofHom
    (LinearMap.codRestrict (adicTowerCollapseKernel.{u, v} T I M s m₀ n.unop)
      (a • LinearMap.id (R := A) (M := (localCohomologyAdicTower.{u, v} A T I s M).obj n))
      (smul_mem_adicTowerCollapseKernel.{u, v} T I M s m₀ ha n.unop))
  naturality p q f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (map_smul ((localCohomologyAdicTower.{u, v} A T I s M).map f).hom a x).symm

/-- Multiplication by `a ∈ I^{m₀}` on the tower factors through the subsystem, read at one
level of the index category. -/
theorem adicTowerCollapseKernelσ_comp_ι_app {a : A} (ha : a ∈ I ^ m₀) (n : ℕᵒᵖ) :
    (adicTowerCollapseKernelσ.{u, v} T I M s m₀ ha).app n ≫
        (adicTowerCollapseKernelι.{u, v} T I M s m₀).app n =
      a • 𝟙 ((localCohomologyAdicTower.{u, v} A T I s M).obj n) :=
  rfl

/-! ### The subsystem is Mittag-Leffler -/

/-- Above level `m₀`, an element of the subsystem at level `i` lies in the image of the subsystem
at level `k` exactly when it lies in the image of the tower at level `k`: a preimage in
`H^s_T(M/IᵏM)` automatically dies in `H^s_T(M/I^{m₀}M)`. -/
theorem range_adicTowerCollapseKernelTower_map_eq {i k : ℕ} (hm₀i : m₀ ≤ i) (hik : i ≤ k) :
    LinearMap.range
        ((adicTowerCollapseKernelTower.{u, v} T I M s m₀).map (homOfLE hik).op).hom =
      Submodule.comap (adicTowerCollapseKernel.{u, v} T I M s m₀ i).subtype
        (LinearMap.range
          ((localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE hik).op).hom) := by
  have hm₀k : m₀ ≤ k := hm₀i.trans hik
  apply le_antisymm
  · rintro x ⟨w, rfl⟩
    exact ⟨w.val, rfl⟩
  · rintro x ⟨w, hw⟩
    have hwker :
        ((localCohomologyAdicTower.{u, v} A T I s M).map (homOfLE hm₀k).op).hom w = 0 := by
      have hfac := localCohomologyAdicTower_map_comp_map.{u, v} T I M s hik hm₀i
      have hrw : (homOfLE (hm₀i.trans hik) : (m₀ : ℕ) ⟶ k) = homOfLE hm₀k :=
        Subsingleton.elim _ _
      rw [hrw] at hfac
      have hcomp := congrArg (fun φ : (localCohomologyAdicTower.{u, v} A T I s M).obj (op k) ⟶
        (localCohomologyAdicTower.{u, v} A T I s M).obj (op m₀) ↦ φ.hom w) hfac
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hcomp
      rw [← hcomp, hw]
      exact (mem_adicTowerCollapseKernel_iff.{u, v} T I M s m₀ hm₀i x.val).mp x.property
    exact ⟨⟨w, (mem_adicTowerCollapseKernel_iff.{u, v} T I M s m₀ hm₀k w).mpr hwker⟩,
      Subtype.ext hw⟩

/-! ### Part (7) of Tag 0EFY -/

/-- The Milnor difference of a tower of `A`-modules is natural in the tower. -/
private theorem milnorDifference_naturality {F G : ℕᵒᵖ ⥤ ModuleCat.{max u v} A} (φ : F ⟶ G) :
    (Limits.Pi.lift fun n : ℕ ↦ Limits.Pi.π (fun n : ℕ ↦ F.obj (op n)) n -
          Limits.Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1) ≫
            F.map (homOfLE (Nat.le_succ n)).op) ≫
        Limits.Pi.map (fun n : ℕ ↦ φ.app (op n)) =
      Limits.Pi.map (fun n : ℕ ↦ φ.app (op n)) ≫
        Limits.Pi.lift fun n : ℕ ↦ Limits.Pi.π (fun n : ℕ ↦ G.obj (op n)) n -
          Limits.Pi.π (fun n : ℕ ↦ G.obj (op n)) (n + 1) ≫
            G.map (homOfLE (Nat.le_succ n)).op := by
  refine Limits.Pi.hom_ext _ _ fun n ↦ ?_
  simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π, Preadditive.sub_comp,
    Preadditive.comp_sub, Limits.Pi.lift_π_assoc, Limits.Pi.map_π_assoc, NatTrans.naturality]

/-- Multiplication by `a ∈ I^{m₀}` on the product of the terms of the tower factors through the
product of the terms of the subsystem. -/
private theorem pi_map_σ_comp_pi_map_ι {a : A} (ha : a ∈ I ^ m₀) :
    (Limits.Pi.map fun n : ℕ ↦ (adicTowerCollapseKernelσ.{u, v} T I M s m₀ ha).app (op n)) ≫
        (Limits.Pi.map fun n : ℕ ↦ (adicTowerCollapseKernelι.{u, v} T I M s m₀).app (op n)) =
      a • 𝟙 (∏ᶜ fun n : ℕ ↦ (localCohomologyAdicTower.{u, v} A T I s M).obj (op n)) := by
  refine Limits.Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc,
    adicTowerCollapseKernelσ_comp_ι_app.{u, v} T I M s m₀ ha (op n), Linear.comp_smul,
    Category.comp_id, Linear.smul_comp, Category.id_comp]

/-- **Part (7) of [Stacks, Tag 0EFY], reduced to the Mittag-Leffler condition for the
subsystem.** `I^{m₀}` annihilates the first derived inverse limit `R¹lim H^s_T(M/IⁿM)` as soon as
the subsystem `Aₙ = ker(H^s_T(M/IⁿM) → H^s_T(M/I^{m₀}M))` satisfies the Mittag-Leffler condition.

This is the source's own last paragraph. `Aₙ` being Mittag-Leffler, its Milnor difference is an
epimorphism, so the composite `∏ Aₙ ⟶ ∏ H^s_T(M/IⁿM) ⟶ R¹lim` — which that difference
annihilates — vanishes; multiplication by `a ∈ I^{m₀}` factors through `∏ Aₙ`, so `a` times the
projection onto `R¹lim` is zero, and that projection is an epimorphism.

The hypothesis is about the subsystem and not about `{H^s_T(M/IⁿM)}` itself, and that is not a
matter of economy. Part (2) of the tag asserts the Mittag-Leffler condition for
`{H^i_T(M/IⁿM)}` only in degrees `i < s`, and part (3) asserts it in degrees `i ≤ s` for the
truncated system `{H^s_T(I^{m₀}M/IⁿM)}`; the system `{H^s_T(M/IⁿM)}` in degree exactly `s` is
not asserted to satisfy it, and could not be without making this part vacuous — a Mittag-Leffler
tower has vanishing first derived limit outright, by
`Stacks.Algebraization.epi_milnorDifference_of_isMittagLefflerCategorical`, so annihilation by
`I^{m₀}` would say nothing. -/
theorem smul_id_firstDerivedLimitLocalCohomologyAdicTower_eq_zero_of_isMittagLeffler
    (hML : IsMittagLefflerCategorical (adicTowerCollapseKernelTower.{u, v} T I M s m₀))
    {a : A} (ha : a ∈ I ^ m₀) :
    a • 𝟙 (firstDerivedLimitLocalCohomologyAdicTower.{u, v} T I M s) = 0 := by
  show a • 𝟙 (cokernel (milnorDifferenceLocalCohomologyAdicTower.{u, v} T I M s)) = 0
  have hepi : Epi (Limits.Pi.lift fun n : ℕ ↦
      Limits.Pi.π
          (fun n : ℕ ↦ (adicTowerCollapseKernelTower.{u, v} T I M s m₀).obj (op n)) n -
        Limits.Pi.π
            (fun n : ℕ ↦ (adicTowerCollapseKernelTower.{u, v} T I M s m₀).obj (op n)) (n + 1) ≫
          (adicTowerCollapseKernelTower.{u, v} T I M s m₀).map
            (homOfLE (Nat.le_succ n)).op) :=
    Stacks.Algebraization.epi_milnorDifference_moduleCat_of_isMittagLefflerCategorical _ hML
  have hzero :
      (Limits.Pi.map fun n : ℕ ↦ (adicTowerCollapseKernelι.{u, v} T I M s m₀).app (op n)) ≫
        cokernel.π (milnorDifferenceLocalCohomologyAdicTower.{u, v} T I M s) = 0 := by
    refine hepi.left_cancellation _ _ ?_
    rw [comp_zero, ← Category.assoc,
      milnorDifference_naturality.{u, v} (adicTowerCollapseKernelι.{u, v} T I M s m₀),
      Category.assoc]
    exact congrArg _ (cokernel.condition _)
  have hcancel : cokernel.π (milnorDifferenceLocalCohomologyAdicTower.{u, v} T I M s) ≫
      (a • 𝟙 (cokernel (milnorDifferenceLocalCohomologyAdicTower.{u, v} T I M s))) = 0 := by
    rw [Linear.comp_smul, Category.comp_id,
      show a • cokernel.π (milnorDifferenceLocalCohomologyAdicTower.{u, v} T I M s) =
        (a • 𝟙 (∏ᶜ fun n : ℕ ↦ (localCohomologyAdicTower.{u, v} A T I s M).obj (op n))) ≫
          cokernel.π (milnorDifferenceLocalCohomologyAdicTower.{u, v} T I M s) by
        rw [Linear.smul_comp, Category.id_comp],
      ← pi_map_σ_comp_pi_map_ι.{u, v} T I M s m₀ ha, Category.assoc, hzero, comp_zero]
  rw [← cancel_epi (cokernel.π (milnorDifferenceLocalCohomologyAdicTower.{u, v} T I M s)),
    hcancel, comp_zero]

/-! ### Part (7) at `T = {𝔪}` over a Noetherian local ring -/

section ClosedPoint

/-- **Part (7) of [Stacks, Tag 0EFY] at `T = {𝔪}` over a Noetherian local ring.** Every element
of `I^{m₀}` annihilates `R¹lim H^s_𝔪(M/IⁿM)`, for every `m₀` and every degree `s`.

The system `{H^s_𝔪(M/IⁿM)}` is itself Mittag-Leffler here, by
`isMittagLefflerCategorical_localCohomologyAdicTower_closedPoint`, so its Milnor difference is an
epimorphism and the first derived inverse limit — the cokernel of that difference — vanishes
outright; annihilation by `I^{m₀}` follows for every `m₀`, and the degree plays no role either.

That is a stronger conclusion than the part asserts, and it is available only because of the
locus: over a Noetherian local ring with `T = {𝔪}` the modules `H^s_𝔪(M/IⁿM)` are Artinian. At a
general specialization-stable `T` they are neither finite nor Artinian, the source obtains the
Mittag-Leffler condition only for the subsystem `Aₙ` of part (3), and the content of part (7) is
then genuinely the annihilation and not a vanishing; that route is
`smul_id_firstDerivedLimitLocalCohomologyAdicTower_eq_zero_of_isMittagLeffler` above, run on
`Stacks.LocalCohomology.isMittagLefflerCategorical_adicTowerCollapseKernelTower_of_stableImage`. -/
@[stacks 0EFY "part (7) at T = {𝔪} over a Noetherian local ring: I^{m₀} annihilates \
R¹lim Hˢ_𝔪(M/IⁿM), for every m₀ and in every degree"]
theorem smul_id_firstDerivedLimitLocalCohomologyAdicTower_eq_zero_closedPoint (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (J : Ideal A) (N : ModuleCat.{u} A)
    [Module.Finite A N] (i : ℤ) (m₀ : ℕ) {a : A} (ha : a ∈ J ^ m₀) :
    a • 𝟙 (firstDerivedLimitLocalCohomologyAdicTower.{u, u}
      {IsLocalRing.closedPoint A} J N i) = 0 := by
  have hepi : Epi (milnorDifferenceLocalCohomologyAdicTower.{u, u}
      {IsLocalRing.closedPoint A} J N i) :=
    Stacks.Algebraization.epi_milnorDifference_of_isMittagLefflerCategorical _
      (isMittagLefflerCategorical_localCohomologyAdicTower_closedPoint A J i N)
  have hπ : cokernel.π (milnorDifferenceLocalCohomologyAdicTower.{u, u}
      {IsLocalRing.closedPoint A} J N i) = 0 :=
    hepi.left_cancellation _ _ (by rw [cokernel.condition, comp_zero])
  have hid : 𝟙 (firstDerivedLimitLocalCohomologyAdicTower.{u, u}
      {IsLocalRing.closedPoint A} J N i) = 0 := by
    show 𝟙 (cokernel (milnorDifferenceLocalCohomologyAdicTower.{u, u}
      {IsLocalRing.closedPoint A} J N i)) = 0
    rw [← cancel_epi (cokernel.π (milnorDifferenceLocalCohomologyAdicTower.{u, u}
      {IsLocalRing.closedPoint A} J N i)), Category.comp_id, comp_zero, hπ]
  rw [hid, smul_zero]

end ClosedPoint

end Stacks.LocalCohomology

end
