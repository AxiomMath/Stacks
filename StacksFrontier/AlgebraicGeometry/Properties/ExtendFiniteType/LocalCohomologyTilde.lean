module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.RingTheory.LocalCohomology.ModulesSupportedIn
public import StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport
public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyZero
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections with support on the spectrum, algebraically and geometrically

Let `A` be a commutative ring, `M` an `A`-module and `T` a subset of the prime spectrum of `A`.
There are two notions of a section of `M` with support in `T`: the algebraic one, the submodule
`Stacks.LocalCohomology.sectionsWithSupportIn`, and the geometric one, the global sections of the
sheaf `M̃` on `Spec A` all of whose germs outside `T` vanish. This module identifies them along
the canonical
isomorphism `M ≅ Γ(Spec A, M̃)`.

## Main results

* `Stacks.LocalCohomologyTilde.germ_toOpen_eq_zero_iff`: the germ at a prime of the global
  section of `M̃` attached to an element of `M` vanishes exactly when that prime is outside the
  zero locus of the annihilator of the element.
* `Stacks.LocalCohomologyTilde.mem_sectionsWithSupportIn_iff`: an element of `M` is an algebraic
  section with support in `T` exactly when the corresponding global section of `M̃` is a
  geometric section with support in `T`.
* `Stacks.LocalCohomologyTilde.image_sectionsWithSupportIn`: the canonical isomorphism
  `M ≅ Γ(Spec A, M̃)` carries the algebraic sections with support in `T` onto the geometric ones.
* `Stacks.LocalCohomologyTilde.image_primaryComponent`: for a finitely generated ideal `I` and
  `Z = V(I)`, it carries the `I`-power-torsion submodule onto the geometric sections with support
  in `Z`; this is the degree-zero case of Tag 0A6T.
* `Stacks.LocalCohomologyTilde.bijOn_primaryComponent`: the same statement as a bijection.

## Implementation notes

The geometric side is `AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule`, whose local
sections are characterized by the vanishing of germs off the subset, and the algebraic side is
characterized by `Stacks.LocalCohomology.mem_sectionsWithSupportIn_iff` through the zero locus
of the annihilator of an element. So the whole comparison reduces to one germ computation, and
both sides are
quantified over the same primes; no closedness of the subset and no finite generation are needed
for the comparison itself. Finite generation enters only to rewrite the algebraic side as the
`I`-power-torsion submodule, which is where Tag 0A6T states it.

The germ computation is `Mathlib`'s: the germ at a prime `x` of the global section of `M̃`
attached to `m` is definitionally `AlgebraicGeometry.tilde.toStalk M x m`, and that map
exhibits the stalk as the localization of `M` at `x`, so the germ vanishes exactly when some
element outside `x` annihilates `m`.

Membership in the geometric submodule is rewritten in term mode rather than by `rw`: the ring
sheaf of a scheme is not syntactically a sheaf of rings for the Grothendieck topology of opens,
so the statement of `mem_supportedSectionsSubmodule_iff` is not a rewrite target here.

## References

* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry PrimeSpectrum
open AlgebraicGeometry.Scheme.Modules
open Stacks.LocalCohomology

universe u

namespace Stacks.LocalCohomologyTilde

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- The image of an element of `M` in the stalk of `M̃` at a prime `x` vanishes exactly when `x`
lies outside the zero locus of the annihilator of the element. -/
theorem toStalk_eq_zero_iff (m : M) (x : PrimeSpectrum R) :
    (tilde.toStalk M x).hom m = 0 ↔ x ∉ zeroLocus (Ideal.torsionOf R M m : Set R) :=
  (IsLocalizedModule.eq_zero_iff x.asIdeal.primeCompl (tilde.toStalk M x).hom).trans <| by
    rw [mem_zeroLocus]
    constructor
    · rintro ⟨⟨s, hs⟩, hsm⟩ hsub
      exact hs (hsub ((Ideal.mem_torsionOf_iff m s).mpr hsm))
    · intro h
      obtain ⟨a, ha, hax⟩ := Set.not_subset.mp h
      exact ⟨⟨a, hax⟩, (Ideal.mem_torsionOf_iff m a).mp ha⟩

/-- The germ at a prime `x` of the global section of `M̃` attached to an element of `M` vanishes
exactly when `x` lies outside the zero locus of the annihilator of the element. -/
theorem germ_toOpen_eq_zero_iff (m : M) (x : PrimeSpectrum R) :
    (TopCat.Presheaf.germ (tilde M).val.presheaf ⊤ x trivial) ((tilde.toOpen M ⊤) m) = 0 ↔
      x ∉ zeroLocus (Ideal.torsionOf R M m : Set R) :=
  toStalk_eq_zero_iff M m x

/-- **Stacks 0A6T in degree zero.** An element of `M` is an algebraic section with support in a
subset `T` of the spectrum exactly when the corresponding global section of `M̃` has all its
germs outside `T` equal to zero. -/
@[stacks 0A6T "degree zero"]
theorem mem_sectionsWithSupportIn_iff (T : Set (PrimeSpectrum R)) (m : M) :
    m ∈ Stacks.LocalCohomology.sectionsWithSupportIn R T M ↔
      (tilde.toOpen M ⊤) m ∈ (supportedSectionsSubmodule T (tilde M)).obj (op ⊤) := by
  rw [Stacks.LocalCohomology.mem_sectionsWithSupportIn_iff]
  refine Iff.trans ?_ (mem_supportedSectionsSubmodule_iff T (tilde M) ⊤ _).symm
  constructor
  · intro h x _ hxT
    exact (germ_toOpen_eq_zero_iff M m x).mpr fun hx ↦ hxT (h hx)
  · intro h x hx
    by_contra hxT
    exact ((germ_toOpen_eq_zero_iff M m x).mp (h x trivial hxT)) hx

/-- The canonical map from `M` to the global sections of `M̃` is bijective. -/
theorem bijective_toOpen_top : Function.Bijective (tilde.toOpen M ⊤).hom :=
  (ConcreteCategory.isIso_iff_bijective (tilde.toOpen M ⊤)).mp tilde.isIso_toOpen_top

/-- **Stacks 0A6T in degree zero.** The canonical isomorphism from `M` to the global sections of
`M̃` carries the algebraic sections with support in `T` onto the geometric ones. -/
@[stacks 0A6T "degree zero"]
theorem image_sectionsWithSupportIn (T : Set (PrimeSpectrum R)) :
    (tilde.toOpen M ⊤).hom '' (Stacks.LocalCohomology.sectionsWithSupportIn R T M : Set M) =
      ((supportedSectionsSubmodule T (tilde M)).obj (op ⊤) :
        Set ((tilde M).val.obj (op ⊤))) := by
  ext s
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact (mem_sectionsWithSupportIn_iff M T m).mp hm
  · intro hs
    obtain ⟨m, rfl⟩ := (bijective_toOpen_top M).2 s
    exact ⟨m, (mem_sectionsWithSupportIn_iff M T m).mpr hs, rfl⟩

variable {I : Ideal R} (hI : I.FG)

include hI

/-- An element of `M` is `I`-power-torsion exactly when the corresponding global section of `M̃`
has all its germs outside `V(I)` equal to zero, for a finitely generated ideal `I`. -/
theorem mem_primaryComponent_iff (m : M) :
    m ∈ I.primaryComponent M ↔
      (tilde.toOpen M ⊤) m ∈
        (supportedSectionsSubmodule (zeroLocus (I : Set R)) (tilde M)).obj (op ⊤) := by
  rw [← Module.sectionsWithSupportIn_zeroLocus R hI M]
  exact mem_sectionsWithSupportIn_iff M _ m

/-- **Stacks 0A6T in degree zero.** For a finitely generated ideal `I` and `Z = V(I)`, the
canonical isomorphism from `M` to the global sections of `M̃` carries the degree-zero local
cohomology `H⁰_Z(M)`, namely the `I`-power-torsion submodule, onto the global sections of `M̃`
with support in `Z`. -/
@[stacks 0A6T "degree zero"]
theorem image_primaryComponent :
    (tilde.toOpen M ⊤).hom '' (I.primaryComponent M : Set M) =
      ((supportedSectionsSubmodule (zeroLocus (I : Set R)) (tilde M)).obj (op ⊤) :
        Set ((tilde M).val.obj (op ⊤))) := by
  rw [← Module.sectionsWithSupportIn_zeroLocus R hI M]
  exact image_sectionsWithSupportIn M _

/-- The canonical isomorphism from `M` to the global sections of `M̃` restricts to a bijection
from the `I`-power-torsion submodule onto the global sections of `M̃` with support in `V(I)`. -/
theorem bijOn_primaryComponent :
    Set.BijOn (tilde.toOpen M ⊤).hom (I.primaryComponent M : Set M)
      ((supportedSectionsSubmodule (zeroLocus (I : Set R)) (tilde M)).obj (op ⊤) :
        Set ((tilde M).val.obj (op ⊤))) :=
  ⟨Set.mapsTo_iff_image_subset.mpr (image_primaryComponent M hI).le,
    (bijective_toOpen_top M).1.injOn,
    (image_primaryComponent M hI).ge⟩

end Stacks.LocalCohomologyTilde

end
