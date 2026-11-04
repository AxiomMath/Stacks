module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Scheme

/-!
# Criteria for divided powers and for ideal subsheaves, checked on a family

This file collects the three "check it on a family" lemmas used to build divided power structures
on a quasi-coherent ideal subsheaf of a scheme, together with the sheaf of types underlying such
an ideal subsheaf.

A divided power structure on an ideal `I` of a ring `R` may be specified by a candidate operation
`d : ℕ → R → R` together with a family of ring maps `f i : R →+* A i` which separates the elements
of `R` and detects membership in `I`, provided each `A i` carries divided powers compatible with
`d`; this is `dividedPowersOfSeparatingFamily`. The geometric counterpart is a basis of opens:
two sections of the structure sheaf agree as soon as they agree on every basis open contained in
their domain (`section_ext_basis`), and a section lies in an ideal subsheaf as soon as all of its
restrictions to basis opens do (`mem_ideal_basis`).

## Main definitions

* `Crystalline.DividedPowerScheme.dividedPowersOfSeparatingFamily` — divided powers on an ideal,
  built from a candidate operation checked through a separating family of ring maps.
* `Crystalline.DividedPowerScheme.idealTypeSheaf` — an ideal subsheaf of the structure sheaf,
  regarded as a sheaf of types.

## Main results

* `Crystalline.DividedPowerScheme.section_ext_basis` — sections of the structure sheaf are
  determined by their restrictions to a basis of opens.
* `Crystalline.DividedPowerScheme.mem_ideal_basis` — membership in an ideal subsheaf may be
  checked on a basis of opens.

## What is and is not proved

No tag attribute is placed in this file: these are auxiliary criteria, used by the construction of
the divided power structure of `Spec` of a divided power ring and by the divided power fibre
product, and none of them is a numbered statement of the Stacks project.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Crystalline.DividedPowerScheme

/-- Divided power identities may be checked by a family of ring maps which
separates elements and detects membership in the ideal. -/
def dividedPowersOfSeparatingFamily
    {R : Type*} [CommSemiring R] (I : Ideal R)
    {ι : Type*} {A : ι → Type*} [∀ i, CommSemiring (A i)]
    (J : ∀ i, Ideal (A i)) (γ : ∀ i, DividedPowers (J i))
    (f : ∀ i, R →+* A i)
    (hf : ∀ x y, (∀ i, f i x = f i y) → x = y)
    (hI : ∀ x, x ∈ I ↔ ∀ i, f i x ∈ J i)
    (d : ℕ → R → R) (hd : ∀ n x, x ∉ I → d n x = 0)
    (hdmap : ∀ n x, x ∈ I → ∀ i, f i (d n x) = (γ i).dpow n (f i x)) :
    DividedPowers I where
  dpow := d
  dpow_null {n x} := hd n x
  dpow_zero {x} hx := hf _ _ fun i => by
    rw [hdmap _ _ hx, (γ i).dpow_zero ((hI x).mp hx i), map_one]
  dpow_one {x} hx := hf _ _ fun i => by
    rw [hdmap _ _ hx, (γ i).dpow_one ((hI x).mp hx i)]
  dpow_mem {n x} hn hx := (hI _).mpr fun i => by
    rw [hdmap _ _ hx]
    exact (γ i).dpow_mem hn ((hI x).mp hx i)
  dpow_add {n x y} hx hy := hf _ _ fun i => by
    rw [hdmap _ _ (I.add_mem hx hy), map_add,
      (γ i).dpow_add ((hI x).mp hx i) ((hI y).mp hy i), map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hdmap _ _ hx, hdmap _ _ hy]
  dpow_mul {n a x} hx := hf _ _ fun i => by
    rw [hdmap _ _ (I.mul_mem_left a hx), map_mul,
      (γ i).dpow_mul ((hI x).mp hx i), map_mul, map_pow, hdmap _ _ hx]
  mul_dpow {m n x} hx := hf _ _ fun i => by
    rw [map_mul, hdmap _ _ hx, hdmap _ _ hx,
      (γ i).mul_dpow ((hI x).mp hx i), map_mul, map_natCast, hdmap _ _ hx]
  dpow_comp {m n x} hn hx := hf _ _ fun i => by
    have hdx : d n x ∈ I := (hI _).mpr fun j => by
      rw [hdmap _ _ hx]
      exact (γ j).dpow_mem hn ((hI x).mp hx j)
    rw [hdmap _ _ hdx, hdmap _ _ hx,
      (γ i).dpow_comp hn ((hI x).mp hx i), map_mul, map_natCast, hdmap _ _ hx]

/-- An ideal subsheaf, regarded as a sheaf of types. -/
noncomputable def idealTypeSheaf (X : Scheme.{u})
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule) :
    TopCat.Sheaf (Type u) X :=
  ⟨I.toSubfunctor.toFunctor, (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget AddCommGrpCat) I.toSheafOfModules.val.presheaf).mp I.toSheafOfModules.isSheaf⟩

/-- Sections of a sheaf are determined by their restrictions to basis opens. -/
theorem section_ext_basis (X : Scheme.{u})
    {ι : Type*} (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    {U : X.Opens} {x y : Γ(X, U)}
    (h : ∀ k (hk : B k ≤ U),
      X.presheaf.map (homOfLE hk).op x = X.presheaf.map (homOfLE hk).op y) : x = y := by
  refine TopCat.Presheaf.IsSheaf.section_ext X.sheaf.property fun z hz => ?_
  obtain ⟨V, ⟨k, rfl⟩, hzV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hz
  exact ⟨B k, hVU, hzV, h k hVU⟩

/-- Membership in an ideal subsheaf can be checked on a basis. -/
theorem mem_ideal_basis (X : Scheme.{u})
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    {ι : Type*} (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    {U : X.Opens} (x : Γ(X, U)) :
    x ∈ I.obj (op U) ↔ ∀ k (hk : B k ≤ U),
      X.presheaf.map (homOfLE hk).op x ∈ I.obj (op (B k)) := by
  refine ⟨fun hx k hk => I.map_mem (homOfLE hk).op hx, fun hx => I.isSheaf x fun z hz => ?_⟩
  obtain ⟨V, ⟨k, rfl⟩, hzV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hz
  exact ⟨B k, homOfLE hVU, hx k hVU, hzV⟩

end Crystalline.DividedPowerScheme
