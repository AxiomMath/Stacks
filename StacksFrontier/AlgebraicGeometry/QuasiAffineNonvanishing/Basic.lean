module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic

/-!
# Nonvanishing loci of sections of an invertible module on a quasi-affine scheme

Let `X` be a quasi-affine scheme and `L` an invertible `𝒪_X`-module. Given a finite set of
points `E` inside an open `W ⊆ X`, [Stacks, Tag 0F20] produces a global section `s` of `L`
whose nonvanishing locus `X_s` is affine and satisfies `E ⊆ X_s ⊆ W`. This file proves the two
*inclusions* of that statement, from the global generation of `L` taken as a hypothesis.

## Main definitions

* `Stacks.SheafOfModules.sectionsOfTop`: an element of `Γ(X, L)` read as a global section in the
  sense of `PresheafOfModules.sections`, by restricting it to every open.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_sections_finite_subset_nonvanishingOpen`: the two
  inclusions of [Stacks, Tag 0F20] for a quasi-affine scheme, with the global generation of `L`
  as a hypothesis.
* `AlgebraicGeometry.Scheme.Modules.exists_sections_finite_subset_nonvanishingOpen_of_isTrivial`:
  the same conclusion with no hypothesis beyond a global trivialization of `L`, for which global
  generation is automatic.
* `Stacks.SheafOfModules.exists_notMem_maximalIdeal_smul_top_of_isInvertible`: an invertible
  module has a nonvanishing section on some neighbourhood of every point. This is the *local*
  form of the global generation hypothesis, and the gap between the two is exactly the extension
  of a section from a basic open.
* `AlgebraicGeometry.Scheme.exists_basicOpen_subset_of_finite` and
  `AlgebraicGeometry.Scheme.exists_basicOpen_subset_of_finite_of_isQuasiAffine`: prime avoidance
  in `Γ(X, ⊤)`. A finite set inside an open `W` lies in a single basic open of a global section
  that is still contained in `W`, whenever such basic opens form a basis around the points of
  the set — in particular on a quasi-affine scheme.
* `AlgebraicGeometry.Scheme.exists_mem_basicOpen_notMem_of_not_specializes`: on a quasi-affine
  scheme, a basic open of a global section separates two points neither of which specializes to
  the other.
* `Stacks.SheafOfModules.mem_nonvanishingLocus_sectionsOfTop_smul` and
  `Stacks.SheafOfModules.mem_nonvanishingLocus_sectionsOfTop_sum`: the two computations with
  nonvanishing loci that the avoidance argument runs on — multiplying a section by a global
  function intersects its nonvanishing locus with the function's basic open, and a sum of
  sections is nonvanishing at a point where exactly one summand's coefficient is nonvanishing
  there.
* `Stacks.SheafOfModules.smul_notMem_maximalIdeal_smul_top_iff`: the local-algebra core of those
  two computations. Over a local ring, `r • m` escapes `𝔪 M` exactly when `r` is a unit and `m`
  escapes `𝔪 M`.
* `Topology.exists_maximal_specializes`: in a finite subset of a T0 space, every point
  specializes to a point of that subset which is maximal for the specialization order.

## Implementation notes

The Stacks proof of Tag 0F20 is an induction on `#E` which, at each step, adds a section
vanishing on the closure of the points already handled. The proof here is the same argument
assembled in one step: after reducing `E` to its specialization-maximal points `E'`
(`Topology.exists_maximal_specializes`; a nonvanishing locus is open, so a point of `E` is
covered as soon as one of its specializations in `E'` is), the sections are combined as
`g • ∑_{y ∈ E'} e_y • m_y`, where `m_y` is nonvanishing at `y`, where `e_y` is a global function
nonvanishing at `y` and vanishing at every other point of `E'`, and where `g` cuts the
nonvanishing locus down into `W`. The functions `e_y` are products of functions separating `y`
from the other points of `E'`, which exist because the basic opens of global sections form a
basis on a quasi-affine scheme (`AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen`), and
the function `g` comes from prime avoidance in `Γ(X, ⊤)`.

What is **not** proved here is the affineness of `X_s`, which is [Stacks, Tag 01PV], nor the
global generation hypothesis, which on a quasi-affine scheme is
[Stacks, Tag 01QE] together with [Stacks, Tag 01Q3]; neither tag is in the library, so the
`@[stacks 0F20]` tag is **not** placed.

The invertibility predicate is `Stacks.SheafOfModules.IsInvertible`, the one that
`Stacks.SheafOfModules.nonvanishingOpen` keys on; it enters only through the openness of the
nonvanishing locus.

## References

* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk ringGerm grpGerm grpStalk)

universe u

namespace Topology

/-- In a finite subset of a T0 space, every point specializes to a point that is maximal for the
specialization order inside that subset. -/
theorem exists_maximal_specializes {X : Type u} [TopologicalSpace X] [T0Space X]
    {E : Set X} (hE : E.Finite) {x : X} (hx : x ∈ E) :
    ∃ y ∈ E, x ⤳ y ∧ ∀ z ∈ E, y ⤳ z → z = y := by
  classical
  have mem : ∀ w v, v ∈ hE.toFinset.filter (fun v => w ⤳ v) ↔ v ∈ E ∧ w ⤳ v := fun w v => by
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  obtain ⟨y, hyT, hymin⟩ := (hE.toFinset.filter (fun v => x ⤳ v)).exists_min_image
    (fun w => (hE.toFinset.filter (fun v => w ⤳ v)).card)
    ⟨x, (mem x x).2 ⟨hx, specializes_rfl⟩⟩
  rw [mem] at hyT
  refine ⟨y, hyT.1, hyT.2, fun z hz hyz => ?_⟩
  have heq := Finset.eq_of_subset_of_card_le
    (fun v hv => (mem y v).2 ⟨((mem z v).1 hv).1, hyz.trans ((mem z v).1 hv).2⟩)
    (hymin z ((mem x z).2 ⟨hz, hyT.2.trans hyz⟩))
  have hyz' : z ⤳ y := by
    refine ((mem z y).1 ?_).2
    rw [heq]
    exact (mem y y).2 ⟨hyT.1, specializes_rfl⟩
  exact ((hyz.antisymm hyz').eq).symm

end Topology

namespace Stacks.SheafOfModules

section LocalAlgebra

variable {R : Type u} [CommRing R] [IsLocalRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- Over a local ring, `r • m` escapes `𝔪 M` exactly when `r` is a unit and `m` escapes
`𝔪 M`. -/
theorem smul_notMem_maximalIdeal_smul_top_iff (r : R) (m : M) :
    r • m ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔
      IsUnit r ∧ m ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
  constructor
  · intro h
    refine ⟨IsLocalRing.notMem_maximalIdeal.mp fun hr => h ?_,
      fun hm => h (Submodule.smul_mem _ r hm)⟩
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rintro ⟨⟨u, rfl⟩, hm⟩ h
    exact hm (by simpa [smul_smul] using Submodule.smul_mem _ ((u⁻¹ : Rˣ) : R) h)

/-- Adding an element of `𝔪 M` does not move a point out of the complement of `𝔪 M`. -/
theorem notMem_maximalIdeal_smul_top_add (a b : M)
    (ha : a ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
    (hb : b ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :
    a + b ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := fun h => by
  refine ha ?_
  have hab : a = (a + b) - b := by abel
  rw [hab]
  exact Submodule.sub_mem _ h hb

end LocalAlgebra

section AnyRingSheaf

variable {T : TopCat.{u}}
  {R : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
  (M : SheafOfModules.{u} R)

/-- A global element of a sheaf of modules over *any* sheaf of rings on a space, read as a
global section: restrict it to every open. The open `⊤` is terminal, so the restrictions of one
element over `⊤` are automatically compatible and no sheaf condition is used.

`Stacks.SheafOfModules.sectionsOfTop` is this construction for a module over the structure sheaf
of a ringed space, which is the spelling most of the development works in. The two are kept
apart deliberately: making the ring sheaf an implicit argument of the specialised name changes
how it is inferred at a call site, which breaks a `rw` whose pattern and target then differ only
in that argument. -/
noncomputable def sectionsOfTopOfRingSheaf (m : M.val.obj (op ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun W => (M.val.presheaf.map (homOfLE (le_top (a := W.unop))).op) m)
    (fun {W₁ _} f =>
      (Functor.map_comp_apply M.val.presheaf (homOfLE (le_top (a := W₁.unop))).op f m).symm)

/-- The section built from a global element `m` takes the value `m` over `⊤`. -/
@[simp]
theorem sectionsOfTopOfRingSheaf_eval_top (m : M.val.obj (op ⊤)) :
    (sectionsOfTopOfRingSheaf M m).eval (op ⊤) = m :=
  Functor.map_id_apply M.val.presheaf (op ⊤) m

/-- A global section of a sheaf of modules is determined by its value over `⊤`, every other
value being a restriction of it. -/
theorem sections_ext_of_eval_top {s t : M.sections} (h : s.eval (op ⊤) = t.eval (op ⊤)) :
    s = t :=
  PresheafOfModules.sections_ext _ _ fun W => by
    rw [← PresheafOfModules.sections_property s (homOfLE (le_top (a := W.unop))).op,
      ← PresheafOfModules.sections_property t (homOfLE (le_top (a := W.unop))).op]
    exact congrArg _ h

end AnyRingSheaf

variable {X : RingedSpace.{u, u}} (L : SheafOfModules.{u} (structureSheafRing X))

/-- A global element of `L` read as a global section: restrict it to every open. -/
noncomputable def sectionsOfTop (m : L.val.obj (op ⊤)) : L.sections :=
  sectionsOfTopOfRingSheaf L m

/-- The section built from a global element `m` takes the value `m` over `⊤`. -/
@[simp]
theorem sectionsOfTop_eval_top (m : L.val.obj (op ⊤)) :
    (sectionsOfTop L m).eval (op ⊤) = m :=
  sectionsOfTopOfRingSheaf_eval_top L m

/-- A point lies in the basic open of a section exactly when the ring germ of the section there
is a unit. -/
theorem isUnit_ringGerm_iff_mem_basicOpen {U : Opens X.carrier} (g : X.presheaf.obj (op U))
    (x : X.carrier) (hx : x ∈ U) :
    IsUnit (ringGerm X x U hx g) ↔ x ∈ X.basicOpen g :=
  (X.mem_basicOpen g x hx).symm

/-- A point lies in the basic open of a finite product exactly when it lies in the basic open of
every factor. -/
theorem mem_basicOpen_prod_iff {U : Opens X.carrier} {ι : Type*} (s : Finset ι)
    (f : ι → X.presheaf.obj (op U)) (x : X.carrier) (hx : x ∈ U) :
    x ∈ X.basicOpen (∏ i ∈ s, f i) ↔ ∀ i ∈ s, x ∈ X.basicOpen (f i) := by
  rw [← isUnit_ringGerm_iff_mem_basicOpen _ x hx, map_prod]
  refine ⟨fun h i hi => (isUnit_ringGerm_iff_mem_basicOpen (f i) x hx).mp
      (isUnit_of_dvd_unit
        (Finset.dvd_prod_of_mem (fun j => ringGerm X x U hx (f j)) hi) h), fun h => ?_⟩
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i hi => ?_
  exact (isUnit_ringGerm_iff_mem_basicOpen (f i) x hx).mpr (h i hi)

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- The nonvanishing locus of a global section depends only on its value over `⊤`. -/
theorem nonvanishingLocus_sectionsOfTop_eval (s : L.sections) :
    nonvanishingLocus L (sectionsOfTop L (s.eval (op ⊤))) = nonvanishingLocus L s := by
  unfold nonvanishingLocus
  rw [sectionsOfTop_eval_top]

/-- A point lies in the nonvanishing locus of the section built from a global element `m`
exactly when the germ of `m` at `x` escapes `𝔪ₓ Lₓ`. -/
theorem mem_nonvanishingLocus_sectionsOfTop_iff (m : L.val.obj (op ⊤)) (x : X.carrier) :
    x ∈ nonvanishingLocus L (sectionsOfTop L m) ↔
      grpGerm X L.val x ⊤ (Opens.mem_top x) m ∉
        IsLocalRing.maximalIdeal (ringStalk X x) •
          (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x)) := by
  rw [show x ∈ nonvanishingLocus L (sectionsOfTop L m) ↔
      grpGerm X L.val x ⊤ (Opens.mem_top x) ((sectionsOfTop L m).eval (op ⊤)) ∉
        IsLocalRing.maximalIdeal (ringStalk X x) •
          (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x)) from Iff.rfl,
    sectionsOfTop_eval_top]

/-- Multiplying a global section by a global function intersects its nonvanishing locus with the
basic open of that function. -/
theorem mem_nonvanishingLocus_sectionsOfTop_smul (g : X.presheaf.obj (op ⊤))
    (m : L.val.obj (op ⊤)) (x : X.carrier) :
    x ∈ nonvanishingLocus L (sectionsOfTop L (g • m)) ↔
      x ∈ X.basicOpen g ∧ x ∈ nonvanishingLocus L (sectionsOfTop L m) := by
  rw [mem_nonvanishingLocus_sectionsOfTop_iff, mem_nonvanishingLocus_sectionsOfTop_iff,
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul X L.val x ⊤ (Opens.mem_top x)
      g m,
    smul_notMem_maximalIdeal_smul_top_iff]
  exact and_congr_left' (isUnit_ringGerm_iff_mem_basicOpen g x (Opens.mem_top x))

/-- A sum `∑ eᵢ • mᵢ` of global sections is nonvanishing at `x` as soon as one index `j`
contributes a section nonvanishing at `x` and every other coefficient `eᵢ` vanishes at `x`. -/
theorem mem_nonvanishingLocus_sectionsOfTop_sum {ι : Type*} (s : Finset ι)
    (e : ι → X.presheaf.obj (op ⊤)) (m : ι → L.val.obj (op ⊤)) (x : X.carrier) {j : ι}
    (hj : j ∈ s) (hxj : x ∈ nonvanishingLocus L (sectionsOfTop L (e j • m j)))
    (hother : ∀ i ∈ s, i ≠ j → x ∉ X.basicOpen (e i)) :
    x ∈ nonvanishingLocus L (sectionsOfTop L (∑ i ∈ s, e i • m i)) := by
  classical
  rw [mem_nonvanishingLocus_sectionsOfTop_iff] at hxj ⊢
  rw [← Finset.add_sum_erase s _ hj, map_add]
  refine notMem_maximalIdeal_smul_top_add _ _ hxj ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul X L.val x ⊤ (Opens.mem_top
    x) (e i) (m i)]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  by_contra hu
  exact hother i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
    ((isUnit_ringGerm_iff_mem_basicOpen (e i) x (Opens.mem_top x)).mp
      (IsLocalRing.notMem_maximalIdeal.mp hu))

/-- **An invertible module has a local nonvanishing section at every point.** This is the
local statement whose global counterpart — a section over `⊤` — is the global generation
hypothesis of `exists_sections_finite_subset_nonvanishingOpen`; the two differ exactly by the
extension of a section from a basic open to the whole of an affine scheme. -/
theorem exists_notMem_maximalIdeal_smul_top_of_isInvertible
    [IsInvertible X.presheaf (structureSheafRing X).property L] (x : X.carrier) :
    ∃ (W : Opens X.carrier) (hx : x ∈ W) (a : L.val.obj (op W)),
      grpGerm X L.val x W hx a ∉
        IsLocalRing.maximalIdeal (ringStalk X x) •
          (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x)) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  obtain ⟨W, hxW, a, b, hab⟩ := exists_tensorPairing_eq_unitSection ψ x
  exact ⟨W, hxW, a, notMem_smul_of_tmul_eq_one (stalkPairing ψ x) _ _
    (bijective_smul_germ_of_tensorPairing_eq_unitSection ψ a b hab x hxW).1⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- A point of a scheme lies in the basic open of a global section exactly when that section is
outside the prime of `Γ(X, ⊤)` corresponding to the point. -/
theorem mem_basicOpen_iff_notMem_toSpecΓ (X : Scheme.{u}) (r : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen r ↔ r ∉ (X.toSpecΓ.base x).asIdeal := by
  rw [← X.toSpecΓ_preimage_basicOpen r]
  exact PrimeSpectrum.mem_basicOpen r _

/-- **Prime avoidance for basic opens.** If every point of a finite set `E ⊆ W` has a basic open
of a global section around it inside `W`, then a *single* basic open of a global section
contains `E` and is contained in `W`. -/
theorem exists_basicOpen_subset_of_finite {X : Scheme.{u}} {E : Set X} (hE : E.Finite)
    (W : X.Opens)
    (hb : ∀ x ∈ E, ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧ X.basicOpen r ≤ W) :
    ∃ g : Γ(X, ⊤), E ⊆ X.basicOpen g ∧ X.basicOpen g ≤ W := by
  classical
  have hb' : ∀ x : X, ∃ r : Γ(X, ⊤), x ∈ E → (x ∈ X.basicOpen r ∧ X.basicOpen r ≤ W) := by
    intro x
    by_cases hx : x ∈ E
    · obtain ⟨r, hr⟩ := hb x hx
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose r hr using hb'
  rcases Set.eq_empty_or_nonempty E with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, by simp, by simp⟩
  set I : Ideal Γ(X, ⊤) := Ideal.span (r '' E) with hI
  have hmem : ∀ x ∈ E, r x ∈ I := fun x hx => Ideal.subset_span ⟨x, hx, rfl⟩
  have hnot : ¬ ((I : Set Γ(X, ⊤)) ⊆
      ⋃ i ∈ (hE.toFinset : Set X), ((X.toSpecΓ.base i).asIdeal : Set Γ(X, ⊤))) := by
    rw [Ideal.subset_union_prime x₀ x₀ (fun i _ _ _ => (X.toSpecΓ.base i).isPrime)]
    rintro ⟨i, hi, hle⟩
    rw [Set.Finite.mem_toFinset] at hi
    exact ((X.mem_basicOpen_iff_notMem_toSpecΓ _ _).mp (hr i hi).1) (hle (hmem i hi))
  obtain ⟨g, hgI, hgnot⟩ := Set.not_subset.mp hnot
  refine ⟨g, fun x hx => ?_, fun y hy => ?_⟩
  · change x ∈ X.basicOpen g
    rw [X.mem_basicOpen_iff_notMem_toSpecΓ]
    intro hcon
    exact hgnot (Set.mem_biUnion (by simpa using hx) hcon)
  · replace hy : y ∈ X.basicOpen g := hy
    rw [X.mem_basicOpen_iff_notMem_toSpecΓ] at hy
    change y ∈ W
    by_contra hyW
    refine hy (Ideal.span_le.mpr ?_ hgI)
    rintro _ ⟨x, hx, rfl⟩
    by_contra hcon
    exact hyW ((hr x hx).2 ((X.mem_basicOpen_iff_notMem_toSpecΓ _ _).mpr hcon))

/-- On a quasi-affine scheme a finite set inside an open `W` lies in a basic open of a global
section contained in `W`. -/
theorem exists_basicOpen_subset_of_finite_of_isQuasiAffine (X : Scheme.{u}) [X.IsQuasiAffine]
    {E : Set X} (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ W) :
    ∃ g : Γ(X, ⊤), E ⊆ X.basicOpen g ∧ X.basicOpen g ≤ W :=
  exists_basicOpen_subset_of_finite hE W fun x hx => by
    obtain ⟨_, ⟨rx, _, rfl⟩, hxr, hrW⟩ :=
      Opens.isBasis_iff_nbhd.mp (IsQuasiAffine.isBasis_basicOpen X) (hEW hx)
    exact ⟨rx, hxr, hrW⟩

/-- On a quasi-affine scheme, two points neither of which specializes to the other are separated
by a basic open of a global section. -/
theorem exists_mem_basicOpen_notMem_of_not_specializes (X : Scheme.{u}) [X.IsQuasiAffine]
    {x y : X} (h : ¬ y ⤳ x) :
    ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧ y ∉ X.basicOpen r := by
  have hx : x ∈ (⟨(closure {y})ᶜ, isClosed_closure.isOpen_compl⟩ : X.Opens) := by
    simpa [specializes_iff_mem_closure] using h
  obtain ⟨_, ⟨r, _, rfl⟩, hxr, hrU⟩ :=
    Opens.isBasis_iff_nbhd.mp (IsQuasiAffine.isBasis_basicOpen X) hx
  refine ⟨r, hxr, fun hy => ?_⟩
  exact (hrU hy) (subset_closure rfl)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules

variable (Y : Scheme.{u})

/-- **The two inclusions of Stacks Project, Tag 0F20.** Let `L` be an invertible module on a
quasi-affine scheme `Y` which is generated by its global sections, in the weak sense that every
point lies in the nonvanishing locus of some global section. Then a finite set `E` inside an
open `W` lies in the nonvanishing locus of a single global section of `L`, and that locus is
contained in `W`.

Affineness of the nonvanishing locus, the third assertion of Tag 0F20, is Tag 01PV and is not
proved here; the global generation hypothesis is Tag 01QE together with Tag 01Q3 and is not
proved here either. -/
theorem exists_sections_finite_subset_nonvanishingOpen [Y.IsQuasiAffine]
    (L : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L]
    (hgen : ∀ y : Y, ∃ s : L.sections, y ∈ nonvanishingLocus (X := Y.toRingedSpace) L s)
    {E : Set Y} (hE : E.Finite) (W : Y.Opens) (hEW : E ⊆ W) :
    ∃ s : L.sections,
      E ⊆ nonvanishingOpen (X := Y.toRingedSpace) L s ∧
      nonvanishingOpen (X := Y.toRingedSpace) L s ≤ W := by
  classical
  obtain ⟨g, hEg, hgW⟩ := Y.exists_basicOpen_subset_of_finite_of_isQuasiAffine hE W hEW
  set E' : Set Y := {y | y ∈ E ∧ ∀ z ∈ E, y ⤳ z → z = y} with hE'def
  have hE'fin : E'.Finite := hE.subset fun _ hy => hy.1
  set T : Finset Y := hE'fin.toFinset with hTdef
  have hmemT : ∀ y : Y, y ∈ T ↔ (y ∈ E ∧ ∀ z ∈ E, y ⤳ z → z = y) := by
    intro y
    rw [hTdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  -- separating functions: for distinct points of `E'`, a global function nonvanishing at the
  -- first and vanishing at the second
  have hsep : ∀ p : Y × Y, ∃ r : Γ(Y, ⊤),
      p.1 ∈ T → p.2 ∈ T → p.2 ≠ p.1 → (p.1 ∈ Y.basicOpen r ∧ p.2 ∉ Y.basicOpen r) := by
    rintro ⟨y, z⟩
    by_cases h : y ∈ T ∧ z ∈ T ∧ z ≠ y
    · obtain ⟨hy, hz, hzy⟩ := h
      obtain ⟨r, hr⟩ := Y.exists_mem_basicOpen_notMem_of_not_specializes (x := y) (y := z)
        fun hsp => hzy (((hmemT z).mp hz).2 y ((hmemT y).mp hy).1 hsp).symm
      exact ⟨r, fun _ _ _ => hr⟩
    · exact ⟨1, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose rsep hrsep using hsep
  set e : Y → Y.toRingedSpace.presheaf.obj (op ⊤) :=
    fun y => ∏ z ∈ T.erase y, rsep (y, z) with hedef
  have he_mem : ∀ y ∈ T, y ∈ Y.basicOpen (e y) := by
    intro y hy
    refine (Stacks.SheafOfModules.mem_basicOpen_prod_iff (X := Y.toRingedSpace) _ _ y
      (Opens.mem_top y)).mpr fun z hz => ?_
    exact (hrsep (y, z) hy (Finset.mem_of_mem_erase hz)
      (Finset.ne_of_mem_erase hz)).1
  have he_notMem : ∀ y ∈ T, ∀ z ∈ T, z ≠ y → z ∉ Y.basicOpen (e y) := by
    intro y hy z hz hzy hmem
    have hze : z ∈ T.erase y := Finset.mem_erase.mpr ⟨hzy, hz⟩
    exact (hrsep (y, z) hy hz hzy).2
      ((Stacks.SheafOfModules.mem_basicOpen_prod_iff (X := Y.toRingedSpace) _ _ z
        (Opens.mem_top z)).mp hmem z hze)
  have hgen' : ∀ y : Y, ∃ m : L.val.obj (op ⊤),
      y ∈ nonvanishingLocus (X := Y.toRingedSpace) L (sectionsOfTop L m) := by
    intro y
    obtain ⟨s, hs⟩ := hgen y
    exact ⟨s.eval (op ⊤), by
      rw [nonvanishingLocus_sectionsOfTop_eval (X := Y.toRingedSpace)]; exact hs⟩
  choose mm hmm using hgen'
  set g₀ : Y.toRingedSpace.presheaf.obj (op ⊤) := g with hg₀
  refine ⟨sectionsOfTop L (g₀ • ∑ y ∈ T, e y • mm y), fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hyE, hxy, hymax⟩ := Topology.exists_maximal_specializes hE hx
    have hyT : y ∈ T := (hmemT y).mpr ⟨hyE, hymax⟩
    have hykey : y ∈ nonvanishingLocus (X := Y.toRingedSpace) L
        (sectionsOfTop L (g₀ • ∑ z ∈ T, e z • mm z)) := by
      refine (mem_nonvanishingLocus_sectionsOfTop_smul (X := Y.toRingedSpace) L g₀ _ y).mpr
        ⟨hEg hyE, ?_⟩
      refine mem_nonvanishingLocus_sectionsOfTop_sum (X := Y.toRingedSpace) L T e mm y hyT
        ((mem_nonvanishingLocus_sectionsOfTop_smul (X := Y.toRingedSpace) L (e y) (mm y) y).mpr
          ⟨he_mem y hyT, hmm y⟩) fun z hz hzy => he_notMem z hz y hyT hzy.symm
    exact hxy.mem_open (Stacks.SheafOfModules.isOpen_nonvanishingLocus (X := Y.toRingedSpace) L _)
      hykey
  · exact hgW ((mem_nonvanishingLocus_sectionsOfTop_smul (X := Y.toRingedSpace) L g₀ _ x).mp hx).1

/-- **The two inclusions of Stacks Project, Tag 0F20 for a globally trivial invertible
module.** A module isomorphic to the structure sheaf is generated by its global sections, so the
global generation hypothesis of `exists_sections_finite_subset_nonvanishingOpen` is automatic. -/
theorem exists_sections_finite_subset_nonvanishingOpen_of_isTrivial [Y.IsQuasiAffine]
    (L : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L]
    (eL : SheafOfModules.unit (structureSheafRing Y.toRingedSpace) ≅ L)
    {E : Set Y} (hE : E.Finite) (W : Y.Opens) (hEW : E ⊆ W) :
    ∃ s : L.sections,
      E ⊆ nonvanishingOpen (X := Y.toRingedSpace) L s ∧
      nonvanishingOpen (X := Y.toRingedSpace) L s ≤ W := by
  refine exists_sections_finite_subset_nonvanishingOpen Y L (fun y => ?_) hE W hEW
  refine ⟨SheafOfModules.sectionsMap eL.hom (unitSections Y.toRingedSpace), ?_⟩
  rw [nonvanishingLocus_sectionsMap Y.toRingedSpace eL (unitSections Y.toRingedSpace),
    nonvanishingLocus_unitSections]
  exact Set.mem_univ y

end AlgebraicGeometry.Scheme.Modules
