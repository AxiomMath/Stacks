module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The maximal prime-to-`p` quotient of a topological group

Let `G` be a topological group and `p` a natural number. A finite continuous quotient of `G` is a
quotient `G ⧸ N` by an open normal subgroup `N`; such a quotient is finite exactly when `N` has
finite index. The maximal prime-to-`p` quotient of `G` is the largest quotient of `G` through
which every finite continuous quotient of order prime to `p` factors: the quotient by the
intersection of the open normal subgroups `N ≤ G` with `¬ p ∣ N.index`.

For `p` a prime the condition `¬ p ∣ N.index` says that `N.index` is finite and prime to `p`. For
`p = 0` it says that `N.index ≠ 0`, that is, that the quotient is finite.

For `G` the étale fundamental group of a connected scheme `X` and `p` the characteristic of a
residue field, `PrimeToP p G` is the group written `π'_1(X)` in the literature.

## Main definitions

* `Stacks.FundamentalGroup.primeToPSubgroups`: the open normal subgroups of index prime to `p`.
* `Stacks.FundamentalGroup.primeToPKernel`: their intersection.
* `Stacks.FundamentalGroup.PrimeToP`: the quotient of `G` by that intersection, the maximal
  prime-to-`p` quotient.
* `Stacks.FundamentalGroup.primeToPMap`: the homomorphism of maximal prime-to-`p` quotients
  induced by a continuous homomorphism.
* `Stacks.FundamentalGroup.IsProP`: every finite continuous quotient of the group is a
  `p`-group.

## Main results

* `Stacks.FundamentalGroup.mem_primeToPKernel_iff`: membership in the kernel is membership in
  every open normal subgroup of index prime to `p`.
* `Stacks.FundamentalGroup.isClosed_primeToPKernel`: the kernel is closed, so `PrimeToP p G` is
  Hausdorff (`Stacks.FundamentalGroup.t2Space_primeToP`).
* `Stacks.FundamentalGroup.primeToPKernel_le_comap`: functoriality — a continuous homomorphism
  carries the kernel into the kernel.
* `Stacks.FundamentalGroup.surjective_primeToPMap`: a surjection induces a surjection.
* `Stacks.FundamentalGroup.primeToPKernel_comap_le_of_forall_lift`: the injectivity
  criterion. If every open normal subgroup of `G` of index prime to `p` is the preimage of an
  open normal subgroup of `H`, then the preimage of the kernel of `H` is contained in the kernel
  of `G`, hence `primeToPMap` is injective
  (`Stacks.FundamentalGroup.injective_primeToPMap_of_forall_lift`).
* `Stacks.FundamentalGroup.exists_continuousMulEquiv_primeToP`: a continuous surjection from a
  compact group `G` along which every prime-to-`p` finite continuous quotient of `G` descends
  induces an isomorphism of topological groups `PrimeToP p G ≃ₜ* PrimeToP p H`, commuting with the
  quotient maps.
* `Stacks.FundamentalGroup.eq_top_of_isProP`: a pro-`p` group has no proper open normal subgroup
  of index prime to `p`, for `p` prime.
* `Stacks.FundamentalGroup.ker_le_of_isProP`: hence a pro-`p` kernel lies in every open normal
  subgroup of index prime to `p`.
* `Stacks.FundamentalGroup.forall_lift_of_isProP_ker`: hence a continuous surjection of a compact
  group onto a Hausdorff one whose kernel is pro-`p` satisfies the descent hypothesis, so it
  induces an isomorphism of maximal prime-to-`p` quotients.
-/

@[expose] public section

namespace Stacks.FundamentalGroup

universe u

section Defs

variable (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G]

/-- The open normal subgroups of `G` whose index is prime to `p`.

For `p` prime these are the kernels of the continuous surjections of `G` onto finite groups of
order prime to `p`. For `p = 0` the condition `¬ p ∣ N.index` says exactly that `N.index ≠ 0`, so
every open normal subgroup of finite index qualifies. -/
def primeToPSubgroups : Set (Subgroup G) :=
  {N | N.Normal ∧ IsOpen (N : Set G) ∧ ¬ p ∣ N.index}

/-- The intersection of the open normal subgroups of `G` of index prime to `p`.

This is the kernel of the map from `G` to its maximal prime-to-`p` quotient. -/
@[sga "1 X 3.9"]
def primeToPKernel : Subgroup G :=
  sInf (primeToPSubgroups p G)

variable {p G}

/-- `N` is an open normal subgroup of index prime to `p` exactly when it is normal, open and
`¬ p ∣ N.index`. -/
theorem mem_primeToPSubgroups_iff {N : Subgroup G} :
    N ∈ primeToPSubgroups p G ↔ N.Normal ∧ IsOpen (N : Set G) ∧ ¬ p ∣ N.index :=
  Iff.rfl

/-- Membership in `primeToPKernel p G` is membership in every open normal subgroup of index
prime to `p`. -/
theorem mem_primeToPKernel_iff {x : G} :
    x ∈ primeToPKernel p G ↔
      ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → ¬ p ∣ N.index → x ∈ N := by
  rw [primeToPKernel, Subgroup.mem_sInf]
  exact ⟨fun h N hn ho hi => h N ⟨hn, ho, hi⟩, fun h N hN => h N hN.1 hN.2.1 hN.2.2⟩

/-- Each open normal subgroup of index prime to `p` contains `primeToPKernel p G`. -/
theorem primeToPKernel_le {N : Subgroup G} (hnorm : N.Normal) (hopen : IsOpen (N : Set G))
    (hindex : ¬ p ∣ N.index) : primeToPKernel p G ≤ N :=
  fun _ hx => mem_primeToPKernel_iff.mp hx N hnorm hopen hindex

variable (p G)

/-- `primeToPKernel p G` is a normal subgroup. -/
instance primeToPKernel_normal : (primeToPKernel p G).Normal where
  conj_mem n hn g := by
    rw [mem_primeToPKernel_iff] at hn ⊢
    exact fun N hnorm hopen hindex => hnorm.conj_mem n (hn N hnorm hopen hindex) g

/-- **The maximal prime-to-`p` quotient of a topological group.** The quotient of `G` by the
intersection of its open normal subgroups of index prime to `p`: the largest quotient of `G`
through which every finite continuous quotient of order prime to `p` factors.

For the étale fundamental group of a connected scheme this is the group written `π'_1`. -/
@[sga "1 X 3.9", sga "1 XIII 2.13", sga "7 I 5.2"]
def PrimeToP : Type _ := G ⧸ primeToPKernel p G

/-- The group structure on `PrimeToP p G`, that of the quotient group. -/
instance : Group (PrimeToP p G) :=
  inferInstanceAs (Group (G ⧸ primeToPKernel p G))

/-- The topology on `PrimeToP p G`, the quotient topology. -/
instance : TopologicalSpace (PrimeToP p G) :=
  inferInstanceAs (TopologicalSpace (G ⧸ primeToPKernel p G))

/-- The projection of `G` onto its maximal prime-to-`p` quotient. -/
@[sga "1 X 3.9", sga "1 XIII 2.13" "more general", sga "7 I 5.2"]
def primeToPMk : G → PrimeToP p G :=
  QuotientGroup.mk (s := primeToPKernel p G)

variable {p G}

/-- Two elements of `G` have the same image in `PrimeToP p G` exactly when `a⁻¹ * b` lies in
`primeToPKernel p G`. -/
theorem primeToPMk_eq_primeToPMk {a b : G} :
    primeToPMk p G a = primeToPMk p G b ↔ a⁻¹ * b ∈ primeToPKernel p G :=
  QuotientGroup.eq

/-- The projection onto the maximal prime-to-`p` quotient is surjective. -/
theorem surjective_primeToPMk : Function.Surjective (primeToPMk p G) :=
  Quotient.mk''_surjective

/-- The projection onto the maximal prime-to-`p` quotient is continuous. -/
theorem continuous_primeToPMk : Continuous (primeToPMk p G) :=
  QuotientGroup.continuous_mk

/-- The projection onto the maximal prime-to-`p` quotient is multiplicative. -/
@[simp]
theorem primeToPMk_mul (a b : G) :
    primeToPMk p G (a * b) = primeToPMk p G a * primeToPMk p G b :=
  rfl

/-- The projection onto the maximal prime-to-`p` quotient sends `1` to `1`. -/
@[simp]
theorem primeToPMk_one : primeToPMk p G 1 = 1 := rfl

/-- `primeToPMk` as a monoid homomorphism. -/
def primeToPMkHom : G →* PrimeToP p G where
  toFun := primeToPMk p G
  map_one' := primeToPMk_one
  map_mul' := primeToPMk_mul

/-- `primeToPMkHom` applied to `a` is `primeToPMk p G a`. -/
@[simp]
theorem primeToPMkHom_apply (a : G) : primeToPMkHom (p := p) (G := G) a = primeToPMk p G a := rfl

/-- Induction on the maximal prime-to-`p` quotient: a property holding on the image of every
element of `G` holds everywhere. -/
theorem induction_on {C : PrimeToP p G → Prop} (x : PrimeToP p G)
    (h : ∀ g : G, C (primeToPMk p G g)) : C x :=
  QuotientGroup.induction_on x h

end Defs

section Topology

variable (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The maximal prime-to-`p` quotient of a topological group is a topological group. -/
instance : IsTopologicalGroup (PrimeToP p G) :=
  inferInstanceAs (IsTopologicalGroup (G ⧸ primeToPKernel p G))

/-- `primeToPKernel p G` is a closed subset of `G`. -/
theorem isClosed_primeToPKernel : IsClosed (primeToPKernel p G : Set G) := by
  rw [primeToPKernel, Subgroup.coe_sInf]
  refine isClosed_biInter fun N hN => ?_
  exact ({ toSubgroup := N, isOpen' := hN.2.1 } : OpenSubgroup G).isClosed

/-- The maximal prime-to-`p` quotient of a topological group is Hausdorff. -/
theorem t2Space_primeToP : T2Space (PrimeToP p G) := by
  have : IsClosed (primeToPKernel p G : Set G) := isClosed_primeToPKernel p G
  exact inferInstanceAs (T2Space (G ⧸ primeToPKernel p G))

omit [IsTopologicalGroup G] in
/-- The maximal prime-to-`p` quotient of a compact topological group is compact. -/
theorem compactSpace_primeToP [CompactSpace G] : CompactSpace (PrimeToP p G) :=
  Quotient.compactSpace

end Topology

section Functoriality

variable {p : ℕ} {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- The preimage along a continuous homomorphism of an open normal subgroup of index prime to
`p` is an open normal subgroup of index prime to `p`. -/
theorem mem_primeToPSubgroups_comap (φ : G →ₜ* H) {M : Subgroup H}
    (hM : M ∈ primeToPSubgroups p H) :
    M.comap φ.toMonoidHom ∈ primeToPSubgroups p G := by
  obtain ⟨hnorm, hopen, hindex⟩ := hM
  have _ : M.Normal := hnorm
  refine ⟨hnorm.comap _, φ.continuous.isOpen_preimage _ hopen, fun hdvd => hindex ?_⟩
  rw [Subgroup.index_comap] at hdvd
  exact hdvd.trans (Subgroup.relIndex_dvd_index_of_normal M φ.toMonoidHom.range)

/-- **Functoriality of the prime-to-`p` kernel.** A continuous homomorphism carries
`primeToPKernel p G` into `primeToPKernel p H`. -/
theorem primeToPKernel_le_comap (φ : G →ₜ* H) :
    primeToPKernel p G ≤ (primeToPKernel p H).comap φ.toMonoidHom := by
  intro x hx
  rw [Subgroup.mem_comap, mem_primeToPKernel_iff]
  intro M hnorm hopen hindex
  obtain ⟨h₁, h₂, h₃⟩ := mem_primeToPSubgroups_comap φ ⟨hnorm, hopen, hindex⟩
  exact primeToPKernel_le h₁ h₂ h₃ hx

/-- **The homomorphism of maximal prime-to-`p` quotients induced by a continuous
homomorphism.** -/
def primeToPMap (p : ℕ) (φ : G →ₜ* H) : PrimeToP p G →* PrimeToP p H :=
  QuotientGroup.map _ _ φ.toMonoidHom (primeToPKernel_le_comap φ)

/-- `primeToPMap p φ` sends the image of `g` to the image of `φ g`. -/
@[simp]
theorem primeToPMap_primeToPMk (φ : G →ₜ* H) (g : G) :
    primeToPMap p φ (primeToPMk p G g) = primeToPMk p H (φ g) :=
  rfl

/-- The homomorphism of maximal prime-to-`p` quotients induced by a continuous homomorphism is
continuous. -/
theorem continuous_primeToPMap [IsTopologicalGroup G] (φ : G →ₜ* H) :
    Continuous (primeToPMap p φ) :=
  continuous_quot_lift _ (continuous_primeToPMk.comp φ.continuous)

/-- A continuous surjection induces a surjection of maximal prime-to-`p` quotients. -/
@[sga "1 XIII 2.13" "more general"]
theorem surjective_primeToPMap (φ : G →ₜ* H) (hφ : Function.Surjective φ) :
    Function.Surjective (primeToPMap p φ) := by
  intro y
  induction y using induction_on with
  | _ h =>
    obtain ⟨g, rfl⟩ := hφ h
    exact ⟨primeToPMk p G g, rfl⟩

/-- **The injectivity criterion.** Suppose every open normal subgroup `N ≤ G` of index prime to
`p` is the preimage along `φ` of an open normal subgroup of `H`. Then the preimage of
`primeToPKernel p H` is contained in `primeToPKernel p G`. -/
theorem primeToPKernel_comap_le_of_forall_lift (φ : G →ₜ* H) (hφ : Function.Surjective φ)
    (hlift : ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → ¬ p ∣ N.index →
      ∃ M : Subgroup H, M.Normal ∧ IsOpen (M : Set H) ∧ M.comap φ.toMonoidHom = N) :
    (primeToPKernel p H).comap φ.toMonoidHom ≤ primeToPKernel p G := by
  intro x hx
  rw [Subgroup.mem_comap] at hx
  rw [mem_primeToPKernel_iff]
  intro N hnorm hopen hindex
  obtain ⟨M, hMnorm, hMopen, rfl⟩ := hlift N hnorm hopen hindex
  exact mem_primeToPKernel_iff.mp hx M hMnorm hMopen
    (by rwa [← Subgroup.index_comap_of_surjective M hφ])

/-- The prime-to-`p` kernel is exactly the preimage of the prime-to-`p` kernel, under the
hypothesis of `Stacks.FundamentalGroup.primeToPKernel_comap_le_of_forall_lift`. -/
theorem primeToPKernel_eq_comap_of_forall_lift (φ : G →ₜ* H) (hφ : Function.Surjective φ)
    (hlift : ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → ¬ p ∣ N.index →
      ∃ M : Subgroup H, M.Normal ∧ IsOpen (M : Set H) ∧ M.comap φ.toMonoidHom = N) :
    (primeToPKernel p H).comap φ.toMonoidHom = primeToPKernel p G :=
  le_antisymm (primeToPKernel_comap_le_of_forall_lift φ hφ hlift) (primeToPKernel_le_comap φ)

/-- **Injectivity of the induced map on maximal prime-to-`p` quotients.** -/
theorem injective_primeToPMap_of_forall_lift (φ : G →ₜ* H) (hφ : Function.Surjective φ)
    (hlift : ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → ¬ p ∣ N.index →
      ∃ M : Subgroup H, M.Normal ∧ IsOpen (M : Set H) ∧ M.comap φ.toMonoidHom = N) :
    Function.Injective (primeToPMap p φ) := by
  intro a b hab
  induction a using induction_on with
  | _ x =>
  induction b using induction_on with
  | _ y =>
  rw [primeToPMap_primeToPMk, primeToPMap_primeToPMk, primeToPMk_eq_primeToPMk] at hab
  rw [primeToPMk_eq_primeToPMk]
  refine primeToPKernel_comap_le_of_forall_lift φ hφ hlift ?_
  change φ.toMonoidHom (x⁻¹ * y) ∈ primeToPKernel p H
  rwa [map_mul, map_inv]

end Functoriality

section Equiv

variable {p : ℕ} {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace G]

/-- **A surjection along which the prime-to-`p` finite quotients descend induces an isomorphism
of maximal prime-to-`p` quotients.**

Let `φ : G →ₜ* H` be a continuous surjection of topological groups with `G` compact, and suppose
every open normal subgroup of `G` of index prime to `p` is the preimage along `φ` of an open
normal subgroup of `H`. Then `φ` induces an isomorphism of topological groups
`PrimeToP p G ≃ₜ* PrimeToP p H` commuting with the projections. -/
theorem exists_continuousMulEquiv_primeToP (φ : G →ₜ* H) (hφ : Function.Surjective φ)
    (hlift : ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → ¬ p ∣ N.index →
      ∃ M : Subgroup H, M.Normal ∧ IsOpen (M : Set H) ∧ M.comap φ.toMonoidHom = N) :
    ∃ e : PrimeToP p G ≃ₜ* PrimeToP p H,
      ∀ g : G, e (primeToPMk p G g) = primeToPMk p H (φ g) := by
  have : CompactSpace (PrimeToP p G) := compactSpace_primeToP p G
  have : T2Space (PrimeToP p H) := t2Space_primeToP p H
  have hbij : Function.Bijective (primeToPMap p φ) :=
    ⟨injective_primeToPMap_of_forall_lift φ hφ hlift, surjective_primeToPMap φ hφ⟩
  have hcont : Continuous (primeToPMap p φ) := continuous_primeToPMap φ
  let eh : PrimeToP p G ≃ₜ PrimeToP p H :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij) hcont
  refine ⟨{ toMulEquiv := MulEquiv.ofBijective (primeToPMap p φ) hbij
            continuous_toFun := hcont
            continuous_invFun := eh.continuous_invFun }, fun g => rfl⟩

end Equiv

section ProP

variable (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G]

/-- **`G` is pro-`p`**: every finite continuous quotient of `G` is a `p`-group.

A continuous quotient of `G` is a quotient by an open normal subgroup, and it is finite exactly
when that subgroup has nonzero index. -/
def IsProP : Prop :=
  ∀ (N : Subgroup G) [N.Normal], IsOpen (N : Set G) → N.index ≠ 0 → IsPGroup p (G ⧸ N)

variable {p G}

/-- **A pro-`p` group has no nontrivial finite quotient of order prime to `p`.** If every finite
continuous quotient of `G` is a `p`-group, then every open normal subgroup of `G` of index prime
to `p` is already all of `G`. -/
theorem eq_top_of_isProP (hp : p.Prime) (hG : IsProP p G) {N : Subgroup G} [N.Normal]
    (hopen : IsOpen (N : Set G)) (hindex : ¬ p ∣ N.index) : N = ⊤ := by
  have hne : N.index ≠ 0 := fun h => hindex (h ▸ dvd_zero p)
  have _ : Finite (G ⧸ N) := Nat.finite_of_card_ne_zero hne
  have hcop : Nat.Coprime p N.index := (Nat.Prime.coprime_iff_not_dvd hp).mpr hindex
  refine Subgroup.eq_top_iff' N |>.mpr fun g => ?_
  obtain ⟨j, hj⟩ := hG N hopen hne (QuotientGroup.mk g)
  have hord : orderOf (QuotientGroup.mk g : G ⧸ N) ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj
  have hcard : orderOf (QuotientGroup.mk g : G ⧸ N) ∣ N.index :=
    Subgroup.index_eq_card N ▸ orderOf_dvd_natCard _
  have hcop' : Nat.gcd (p ^ j) N.index = 1 := Nat.Coprime.pow_left j hcop
  have hd : orderOf (QuotientGroup.mk g : G ⧸ N) ∣ 1 := hcop' ▸ Nat.dvd_gcd hord hcard
  rw [← QuotientGroup.eq_one_iff]
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

end ProP

section ProPKer

variable {p : ℕ} {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- **A pro-`p` kernel is contained in every open normal subgroup of index prime to `p`.** -/
theorem ker_le_of_isProP (hp : p.Prime) (φ : G →ₜ* H)
    (hker : IsProP p ↥(MonoidHom.ker φ.toMonoidHom)) {N : Subgroup G} (hnorm : N.Normal)
    (hopen : IsOpen (N : Set G)) (hindex : ¬ p ∣ N.index) :
    MonoidHom.ker φ.toMonoidHom ≤ N := by
  set K := MonoidHom.ker φ.toMonoidHom with hK
  have _ : N.Normal := hnorm
  have _ : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf
  have hdvdrel : (N.subgroupOf K).index ∣ N.index :=
    Subgroup.relIndex_dvd_index_of_normal N K
  have hsubtop : N.subgroupOf K = ⊤ :=
    eq_top_of_isProP hp hker
      (continuous_subtype_val.isOpen_preimage _ hopen)
      fun hdvd => hindex (hdvd.trans hdvdrel)
  intro x hx
  exact (Subgroup.mem_subgroupOf (H := N) (K := K) (h := ⟨x, hx⟩)).mp
    (hsubtop ▸ Subgroup.mem_top (⟨x, hx⟩ : K))

/-- **A pro-`p` kernel makes the descent hypothesis of
`Stacks.FundamentalGroup.primeToPKernel_comap_le_of_forall_lift` automatic.** Let `φ` be a
continuous surjection of a compact group onto a Hausdorff group whose kernel is pro-`p`, for `p`
prime. Then every open normal subgroup of `G` of index prime to `p` is the preimage along `φ` of
an open normal subgroup of `H`. -/
theorem forall_lift_of_isProP_ker [CompactSpace G] [T2Space H] (hp : p.Prime) (φ : G →ₜ* H)
    (hφ : Function.Surjective φ) (hker : IsProP p ↥(MonoidHom.ker φ.toMonoidHom)) :
    ∀ N : Subgroup G, N.Normal → IsOpen (N : Set G) → ¬ p ∣ N.index →
      ∃ M : Subgroup H, M.Normal ∧ IsOpen (M : Set H) ∧ M.comap φ.toMonoidHom = N := by
  intro N hnorm hopen hindex
  have hkerle : MonoidHom.ker φ.toMonoidHom ≤ N := ker_le_of_isProP hp φ hker hnorm hopen hindex
  have hcm : (N.map φ.toMonoidHom).comap φ.toMonoidHom = N := by
    rw [Subgroup.comap_map_eq]
    exact sup_eq_left.mpr hkerle
  have hq : Topology.IsQuotientMap φ :=
    Topology.IsQuotientMap.of_surjective_continuous hφ φ.continuous
  refine ⟨N.map φ.toMonoidHom, hnorm.map _ hφ, ?_, hcm⟩
  rw [← hq.isOpen_preimage]
  change IsOpen (φ.toMonoidHom ⁻¹' (N.map φ.toMonoidHom : Set H))
  rwa [← Subgroup.coe_comap, hcm]

end ProPKer

end Stacks.FundamentalGroup

end
