module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Nonvanishing loci of an invertible module as a basis for the topology

For an invertible module `L` on a scheme `X`, write `X_s` for the nonvanishing locus of a global
section `s` of a positive tensor power of `L`. This file defines the conditions that the opens
`X_s` form a basis for the topology of `X`, and that the affine ones among them do, and compares
them with ampleness of `L`.

## Main definitions

* `Stacks.AmpleTheory.powNonvanishingOpen X L n s`: `X_s` as an open subset, for `s` a global
  section of `L ^⊗ n`.
* `Stacks.AmpleTheory.IsBasisNonvanishing`: the opens `X_s` form a basis for the topology.
* `Stacks.AmpleTheory.IsBasisAffineNonvanishing`: the affine opens `X_s` form a basis for the
  topology.
* `Stacks.AmpleTheory.nonvanishingOpens`, `Stacks.AmpleTheory.affineNonvanishingOpens`: the two
  families of opens, as sets of opens.
* `Stacks.AmpleTheory.IsAffineOfLeAffine`: every `X_s` contained in an affine open is affine.

## Main results

* `Stacks.AmpleTheory.isBasis_nonvanishingOpens_iff`,
  `Stacks.AmpleTheory.isBasis_affineNonvanishingOpens_iff`: the two conditions say exactly that
  the corresponding family is a basis for the topology, as `TopologicalSpace.Opens.IsBasis`.
* `Stacks.AmpleTheory.IsBasisAffineNonvanishing.isBasisNonvanishing`: if the affine `X_s` form a
  basis, then the `X_s` form a basis.
* `Stacks.AmpleTheory.isAmple_of_isBasisAffineNonvanishing`: on a quasi-compact scheme, if the
  affine `X_s` form a basis, then `L` is ample.
* `Stacks.AmpleTheory.isAmple_iff_forall_affine_nonvanishingOpen`: `L` is ample if and only if `X`
  is quasi-compact and every point of `X` lies in an affine `X_s`.
* `Stacks.AmpleTheory.isAffineOpen_nonvanishingOpen_inf`: for `V` affine carrying a sectionwise
  trivialization of `M`, the open `X_s ⊓ V` is affine.
* `Stacks.AmpleTheory.exists_affineOpen_trivialization`: an invertible module is sectionwise
  trivial on a basis of affine opens.
* `Stacks.AmpleTheory.isBasisAffineNonvanishing_of_isBasisNonvanishing`: under
  `Stacks.AmpleTheory.IsAffineOfLeAffine`, if the `X_s` form a basis, then the affine `X_s` do.
* `Stacks.AmpleTheory.isBasisAffineNonvanishing_of_isAmple` and
  `Stacks.AmpleTheory.isAmple_iff_isBasisAffineNonvanishing`: for an invertible module with a
  nowhere-vanishing global basis in every tensor degree, `L` is ample if and only if `X` is
  quasi-compact and the affine `X_s` form a basis.
* `Stacks.AmpleTheory.isBasisAffineNonvanishing_unitModule`,
  `Stacks.AmpleTheory.isBasisNonvanishing_unitModule` and
  `Stacks.AmpleTheory.isAmple_unitModule_iff_isBasisAffineNonvanishing`: the same for the
  structure sheaf, with no hypothesis.

## References

* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PX](https://stacks.math.columbia.edu/tag/01PX)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [EGA II, Proposition 4.5.2]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.NonvanishingOpen

universe u

namespace Stacks.AmpleTheory

/-! ### Nonvanishing loci on trivializing affine opens -/

section Local

variable {X : Scheme.{u}}

/-- **An invertible `𝒪_X`-module is sectionwise trivial on a basis of affine opens.** -/
theorem exists_affineOpen_trivialization (M : X.Modules) [IsInvertibleModule X M] {x : X}
    {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧
      Nonempty (Stacks.SheafDescent.Trivialization X.presheaf M.val V) := by
  obtain ⟨W, hxW, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at M x
  obtain ⟨V, hV, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)
    (show x ∈ U ⊓ W from ⟨hx, hxW⟩)
  exact ⟨V, hV, hxV, hVle.trans inf_le_left,
    ⟨t.comp (homOfLE (hVle.trans inf_le_right))⟩⟩

variable {M : X.Modules} [IsInvertibleModule X M] {V : X.Opens}

/-- If `V` is affine and carries a sectionwise trivialization of `M`, then `X_s ⊓ V` is affine
for every global section `s` of `M`. -/
theorem isAffineOpen_nonvanishingOpen_inf (hV : IsAffineOpen V)
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) (s : Γ(M, ⊤)) :
    IsAffineOpen (nonvanishingOpen X M s ⊓ V) := by
  rw [show nonvanishingOpen X M s ⊓ V = X.basicOpen (trivTop t s) from Opens.ext <| by
    rw [Opens.coe_inf, coe_nonvanishingOpen]; exact nonvanishingLocus_inter t s]
  exact hV.basicOpen _

/-- A nonvanishing locus contained in a trivializing affine open is affine. -/
theorem isAffineOpen_nonvanishingOpen_of_le (hV : IsAffineOpen V)
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) (s : Γ(M, ⊤))
    (hle : nonvanishingOpen X M s ≤ V) : IsAffineOpen (nonvanishingOpen X M s) := by
  rw [← inf_eq_left.mpr hle]
  exact isAffineOpen_nonvanishingOpen_inf hV t s

/-- On an affine scheme, every nonvanishing locus of a global section of a module with a
nowhere-vanishing global basis is affine. -/
theorem isAffineOpen_nonvanishingOpen_of_nonvanishingBasis [IsAffine X] (b : NonvanishingBasis M)
    (s : Γ(M, ⊤)) : IsAffineOpen (nonvanishingOpen X M s) := by
  obtain ⟨r, hr⟩ := b.exists_basicOpen_eq s
  rw [show nonvanishingOpen X M s = X.basicOpen r from Opens.ext hr]
  exact (isAffineOpen_top X).basicOpen r

end Local

/-! ### The two basis clauses -/

variable (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]

/-- `X_s` as an open subset of `X`, for `s` a global section of the `n`-th tensor power of an
invertible `𝒪_X`-module. -/
noncomputable def powNonvanishingOpen (n : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) : X.Opens :=
  nonvanishingOpen X (tensorPowModule X L (n : ℤ)) s

/-- The underlying set of `Stacks.AmpleTheory.powNonvanishingOpen X L n s` is the nonvanishing
locus of `s`. -/
@[simp] theorem coe_powNonvanishingOpen (n : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) :
    (powNonvanishingOpen X L n s : Set X) = nonvanishingLocus (tensorPowModule X L (n : ℤ)) s :=
  rfl

/-- The open sets `X_s`, for `s` a global section of a positive tensor power of `L`, form a
basis for the topology of `X`: every open neighbourhood of a point contains an `X_s` containing
the point. -/
def IsBasisNonvanishing : Prop :=
  ∀ (x : X) (U : X.Opens), x ∈ U → ∃ n : ℕ, 1 ≤ n ∧
    ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
      x ∈ powNonvanishingOpen X L n s ∧ powNonvanishingOpen X L n s ≤ U

/-- The open sets `X_s` which are affine, for `s` a global section of a positive tensor power of
`L`, form a basis for the topology of `X`. -/
def IsBasisAffineNonvanishing : Prop :=
  ∀ (x : X) (U : X.Opens), x ∈ U → ∃ n : ℕ, 1 ≤ n ∧
    ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
      IsAffineOpen (powNonvanishingOpen X L n s) ∧
        x ∈ powNonvanishingOpen X L n s ∧ powNonvanishingOpen X L n s ≤ U

/-- If the affine `X_s` form a basis for the topology, then the `X_s` form a basis. -/
theorem IsBasisAffineNonvanishing.isBasisNonvanishing (h : IsBasisAffineNonvanishing X L) :
    IsBasisNonvanishing X L := fun x U hx ↦ by
  obtain ⟨n, hn, s, -, hxs, hsU⟩ := h x U hx
  exact ⟨n, hn, s, hxs, hsU⟩

/-- The open sets `X_s`, for `s` a global section of a positive tensor power of `L`. -/
def nonvanishingOpens : Set X.Opens :=
  {V | ∃ (n : ℕ) (_ : 1 ≤ n) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)),
    powNonvanishingOpen X L n s = V}

/-- The affine open sets `X_s`, for `s` a global section of a positive tensor power of `L`. -/
def affineNonvanishingOpens : Set X.Opens :=
  {V | ∃ (n : ℕ) (_ : 1 ≤ n) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)),
    IsAffineOpen (powNonvanishingOpen X L n s) ∧ powNonvanishingOpen X L n s = V}

/-- **`Stacks.AmpleTheory.IsBasisNonvanishing` says that the `X_s` form a basis for the
topology.** -/
theorem isBasis_nonvanishingOpens_iff :
    Opens.IsBasis (nonvanishingOpens X L) ↔ IsBasisNonvanishing X L := by
  rw [Opens.isBasis_iff_nbhd]
  constructor
  · intro h x U hx
    obtain ⟨V, ⟨n, hn, s, rfl⟩, hxV, hVU⟩ := h hx
    exact ⟨n, hn, s, hxV, hVU⟩
  · intro h U x hx
    obtain ⟨n, hn, s, hxs, hsU⟩ := h x U hx
    exact ⟨_, ⟨n, hn, s, rfl⟩, hxs, hsU⟩

/-- **`Stacks.AmpleTheory.IsBasisAffineNonvanishing` says that the affine `X_s` form a basis for
the topology.** -/
theorem isBasis_affineNonvanishingOpens_iff :
    Opens.IsBasis (affineNonvanishingOpens X L) ↔ IsBasisAffineNonvanishing X L := by
  rw [Opens.isBasis_iff_nbhd]
  constructor
  · intro h x U hx
    obtain ⟨V, ⟨n, hn, s, haff, rfl⟩, hxV, hVU⟩ := h hx
    exact ⟨n, hn, s, haff, hxV, hVU⟩
  · intro h U x hx
    obtain ⟨n, hn, s, haff, hxs, hsU⟩ := h x U hx
    exact ⟨_, ⟨n, hn, s, haff, rfl⟩, hxs, hsU⟩

/-! ### Affine nonvanishing loci and ampleness -/

/-- **If the affine `X_s` form a basis for the topology of a quasi-compact scheme `X`, then `L`
is ample.** -/
theorem isAmple_of_isBasisAffineNonvanishing (hc : CompactSpace X)
    (h : IsBasisAffineNonvanishing X L) : IsAmple X L :=
  (isAmple_iff X L).mpr <| (isAmpleForPowers_iff X _).mpr ⟨hc, fun x ↦ by
    obtain ⟨n, hn, s, haff, hxs, -⟩ := h x ⊤ (Opens.mem_top x)
    exact ⟨n, hn, s, powNonvanishingOpen X L n s, rfl, hxs, haff⟩⟩

/-- **`L` is ample if and only if `X` is quasi-compact and every point of `X` lies in an affine
`X_s`.** -/
theorem isAmple_iff_forall_affine_nonvanishingOpen : IsAmple X L ↔ CompactSpace X ∧
    ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
      IsAffineOpen (powNonvanishingOpen X L n s) ∧ x ∈ powNonvanishingOpen X L n s := by
  rw [isAmple_iff_nonvanishingOpen X L]
  exact and_congr_right fun _ ↦ forall_congr' fun x ↦ exists_congr fun n ↦
    and_congr_right fun _ ↦ exists_congr fun s ↦ and_comm

/-- Every point of a scheme with an ample invertible module lies in an affine `X_s`. -/
theorem IsAmple.exists_affine_nonvanishingOpen (h : IsAmple X L) (x : X) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
      IsAffineOpen (powNonvanishingOpen X L n s) ∧ x ∈ powNonvanishingOpen X L n s :=
  ((isAmple_iff_forall_affine_nonvanishingOpen X L).mp h).2 x

/-! ### Affine nonvanishing loci from nonvanishing loci -/

/-- Every nonvanishing locus of a global section of a positive tensor power of `L` that is
contained in an affine open is itself affine. -/
def IsAffineOfLeAffine : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) (U : X.Opens), IsAffineOpen U →
    powNonvanishingOpen X L n s ≤ U → IsAffineOpen (powNonvanishingOpen X L n s)

/-- Under `Stacks.AmpleTheory.IsAffineOfLeAffine`, if the opens `X_s` form a basis for the
topology, then the affine ones among them do. -/
theorem isBasisAffineNonvanishing_of_isBasisNonvanishing (h : IsBasisNonvanishing X L)
    (hPV : IsAffineOfLeAffine X L) : IsBasisAffineNonvanishing X L := fun x U hx ↦ by
  obtain ⟨A, hA, hxA, hAU⟩ := Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X) hx
  obtain ⟨n, hn, s, hxs, hsA⟩ := h x A hxA
  exact ⟨n, hn, s, hPV n hn s A hA hsA, hxs, hsA.trans hAU⟩

/-- `Stacks.AmpleTheory.IsAffineOfLeAffine` holds on an affine scheme when every positive tensor
power of `L` has a nowhere-vanishing global basis. -/
theorem isAffineOfLeAffine_of_nonvanishingBasis [IsAffine X]
    (b : ∀ n : ℕ, NonvanishingBasis (tensorPowModule X L (n : ℤ))) : IsAffineOfLeAffine X L :=
  fun n _ s _ _ _ ↦ isAffineOpen_nonvanishingOpen_of_nonvanishingBasis (b n) s

/-! ### Globally trivial modules -/

/-- **On a quasi-affine scheme, if `L` has a nowhere-vanishing global basis in degree one, then
the affine `X_s` form a basis for the topology.** -/
theorem isBasisAffineNonvanishing_of_isQuasiAffine [X.IsQuasiAffine]
    (b : NonvanishingBasis (tensorPowModule X L ((1 : ℕ) : ℤ))) :
    IsBasisAffineNonvanishing X L := fun x U hx ↦ by
  obtain ⟨V, ⟨r, hr, rfl⟩, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp (Scheme.IsQuasiAffine.isBasis_basicOpen X) hx
  have e : powNonvanishingOpen X L 1 (r • b.gen) = X.basicOpen r :=
    Opens.ext (b.nonvanishingLocus_smul_gen r)
  exact ⟨1, le_rfl, r • b.gen, e ▸ hr, e ▸ hxV, e ▸ hVU⟩

/-- **If `L` is ample and has a nowhere-vanishing global basis in every tensor degree, then the
affine `X_s` form a basis for the topology.** -/
theorem isBasisAffineNonvanishing_of_isAmple
    (b : ∀ n : ℤ, NonvanishingBasis (tensorPowModule X L n)) (h : IsAmple X L) :
    IsBasisAffineNonvanishing X L := by
  have : X.IsQuasiAffine := (isQuasiAffine_iff_isAmpleForPowers X _ b).mpr ((isAmple_iff X L).mp h)
  exact isBasisAffineNonvanishing_of_isQuasiAffine X L (b _)

/-- **If `L` has a nowhere-vanishing global basis in every tensor degree, then `L` is ample if and
only if `X` is quasi-compact and the affine `X_s` form a basis for the topology.** -/
theorem isAmple_iff_isBasisAffineNonvanishing
    (b : ∀ n : ℤ, NonvanishingBasis (tensorPowModule X L n)) :
    IsAmple X L ↔ CompactSpace X ∧ IsBasisAffineNonvanishing X L :=
  ⟨fun h ↦ ⟨h.1, isBasisAffineNonvanishing_of_isAmple X L b h⟩,
    fun h ↦ isAmple_of_isBasisAffineNonvanishing X L h.1 h.2⟩

/-! ### The structure sheaf -/

/-- **On a quasi-affine scheme, the affine nonvanishing loci of global sections of the tensor
powers of the structure sheaf form a basis for the topology.** -/
@[ega "II 5.1.2" "a) ⇒ d'), a) ⇒ d)", ega "II 6.6.13" "EGA II 5.1.2"]
theorem isBasisAffineNonvanishing_unitModule (X : Scheme.{u}) [X.IsQuasiAffine] :
    IsBasisAffineNonvanishing X (unitModule X) :=
  isBasisAffineNonvanishing_of_isQuasiAffine X _ (unitTensorPowBasis X _)

/-- **On a quasi-affine scheme, the nonvanishing loci of global sections of the tensor powers of
the structure sheaf form a basis for the topology.** -/
@[ega "II 5.1.2" "a) ⇒ d)"]
theorem isBasisNonvanishing_unitModule (X : Scheme.{u}) [X.IsQuasiAffine] :
    IsBasisNonvanishing X (unitModule X) :=
  (isBasisAffineNonvanishing_unitModule X).isBasisNonvanishing

/-- **The structure sheaf is ample if and only if `X` is quasi-compact and the affine nonvanishing
loci of global sections of its tensor powers form a basis for the topology.** -/
theorem isAmple_unitModule_iff_isBasisAffineNonvanishing (X : Scheme.{u}) :
    IsAmple X (unitModule X) ↔
      CompactSpace X ∧ IsBasisAffineNonvanishing X (unitModule X) :=
  isAmple_iff_isBasisAffineNonvanishing X _ (unitTensorPowBasis X)

end Stacks.AmpleTheory

end
