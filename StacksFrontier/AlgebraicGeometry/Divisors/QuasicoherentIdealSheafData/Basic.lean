module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# A quasi-coherent ideal subsheaf of `𝒪_X` is an ideal sheaf datum

Mathlib records a closed subscheme of a scheme `X` as an
`AlgebraicGeometry.Scheme.IdealSheafData`: an ideal `I(U) ⊆ Γ(X, U)` for every *affine* open `U`,
subject to the compatibility `I(D(f)) = I(U)_f` on basic opens. A quasi-coherent sheaf of ideals,
on the other hand, is naturally presented as a submodule `J` of the unit sheaf of modules
`𝒪_X`, which assigns an ideal `J(V) ⊆ Γ(X, V)` to *every* open `V` and is only required to be
stable under restriction. Nothing connected the two presentations.

This file supplies the missing comparison. For a quasi-coherent `J`, an affine open `U` and a
section `f : Γ(X, U)`, the ideal cut out on the basic open `D(f)` is the localization of the one
cut out on `U` (`Stacks.Divisors.map_ideal_basicOpen_of_isQuasicoherent`), so the family of ideals
`U ↦ J(U)` on affine opens is an ideal sheaf datum
(`Stacks.Divisors.idealSheafDataOfSubmodule`). Feeding that into Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme` produces the closed subscheme cut out by `J`,
which is the implication (2) ⇒ (3) of Stacks Tag 01QQ.

## Main definitions

* `Stacks.Divisors.idealSheafDataOfSubmodule`: the ideal sheaf datum of a quasi-coherent ideal
  subsheaf of `𝒪_X`.

## Main results

* `Stacks.Divisors.map_ideal_basicOpen_of_isQuasicoherent`: for `U` affine and `f : Γ(X, U)`, the
  image of `J(U)` in `Γ(X, D(f))` generates `J(D(f))`.
* `Stacks.Divisors.subschemeι_app_eq_zero_iff_mem` and
  `Stacks.Divisors.subschemeι_app_eq_zero_of_mem`: over an affine open the sections killed by the
  closed immersion are exactly the sections of `J`, and over an arbitrary open every section of
  `J` is killed.
* `Stacks.Divisors.exists_isClosedImmersion_ker_eq`: Stacks Tag 01QQ, the implication (2) ⇒ (3).

## Implementation notes

The whole content of the basic-open comparison is
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`: the sections of a
quasi-coherent module over `D(f)` are the localization away from `f` of its sections over `U`.
Applied to `J.toSheafOfModules`, whose sections over `V` are by construction the ideal `J(V)`, it
produces for every `y ∈ J(D(f))` an `x ∈ J(U)` and an `n` with `f^n|_{D(f)} · y = x|_{D(f)}`; as
`f|_{D(f)}` is a unit, `y` already lies in the image of `J(U)`. The reverse inclusion is just
stability of `J` under restriction.

The ideals `J.obj (op V)` are literally `Ideal Γ(X, V)` — the spelling
`Crystalline.sectionIdeal X.sheaf J (op V)` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Scheme.lean` is the same term — but the type as
inferred by Lean is `Submodule ↑(X.ringCatSheaf.obj.obj (op V)) ↑((SheafOfModules.unit _).val.obj
(op V))`, so dot notation on them resolves to `Submodule.map` rather than `Ideal.map`. The
statements below therefore write `Ideal.map res (J.obj (op U))` in prefix form, which fixes the
ring from the homomorphism; inside the `IdealSheafData` constructor the expected type already
does that.

The passage from affine opens to arbitrary opens is the sheaf axiom on the closed subscheme: the
affine opens contained in `V` cover `V`, so a section of `𝒪_X` over `V` lying in `J(V)` is killed
by the closed immersion as soon as each of its restrictions to those affine opens is, and that is
the affine case together with stability of `J` under restriction.

## References

* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (J : (SheafOfModules.unit X.ringCatSheaf).Submodule)
  [(J.toSheafOfModules : X.Modules).IsQuasicoherent]

/-- **The affine-local content of Stacks Tags 01IN and 01QQ.** For a quasi-coherent ideal
subsheaf `J` of `𝒪_X`, an affine open `U` and a section `f : Γ(X, U)`, the ideal that `J` cuts out
on the basic open `D(f)` is the localization at `f` of the ideal it cuts out on `U`: the image of
`J(U)` under the restriction map generates `J(D(f))`. -/
theorem map_ideal_basicOpen_of_isQuasicoherent {U : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) :
    Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (J.obj (op U)) =
      J.obj (op (X.basicOpen f)) := by
  set M : X.Modules := J.toSheafOfModules
  set res := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom with hres
  let _ := moduleOfLE M (X.basicOpen_le f)
  have hloc : IsLocalizedModule.Away f (restrictₗ M (X.basicOpen_le f)) :=
    isLocalizedModule_restrictₗ M hU f rfl (X.basicOpen_le f)
  have hpow : Submonoid.powers f ≤ (IsUnit.submonoid Γ(X, X.basicOpen f)).comap res := by
    rw [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff, hres]
    exact X.toRingedSpace.isUnit_res_basicOpen f
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) fun y hy => ?_
  · exact J.map_mem (homOfLE (X.basicOpen_le f)).op hx
  · obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalizedModule.surj (Submonoid.powers f)
      (restrictₗ M (X.basicOpen_le f)) (⟨y, hy⟩ : Γ(M, X.basicOpen f))
    have key : res (s : Γ(X, U)) * y = res x.val := congrArg Subtype.val hxs
    rw [← Ideal.unit_mul_mem_iff_mem _ (hpow s.2), key]
    exact Ideal.mem_map_of_mem _ x.2

/-- **The ideal sheaf datum of a quasi-coherent ideal subsheaf of `𝒪_X`.** Its ideal on an affine
open `U` is the ideal `J(U)` of sections of `J` over `U`; the compatibility on basic opens is
`Stacks.Divisors.map_ideal_basicOpen_of_isQuasicoherent`. -/
def idealSheafDataOfSubmodule : X.IdealSheafData where
  ideal U := J.obj (op U.1)
  map_ideal_basicOpen U f := map_ideal_basicOpen_of_isQuasicoherent J U.2 f

/-- The ideal of `idealSheafDataOfSubmodule J` on an affine open `U` is `J(U)`. -/
@[simp]
lemma ideal_idealSheafDataOfSubmodule (U : X.affineOpens) :
    (idealSheafDataOfSubmodule J).ideal U = J.obj (op U.1) :=
  rfl

/-- **Over an affine open, the closed subscheme cut out by `J` kills exactly the sections of
`J`.** -/
theorem subschemeι_app_eq_zero_iff_mem (U : X.affineOpens) (s : Γ(X, U.1)) :
    (idealSheafDataOfSubmodule J).subschemeι.app U.1 s = 0 ↔ s ∈ J.obj (op U.1) := by
  rw [← RingHom.mem_ker, (idealSheafDataOfSubmodule J).ker_subschemeι_app U]
  rfl

/-- **Over an arbitrary open, every section of `J` dies on the closed subscheme cut out by `J`.**
The affine opens contained in the given open cover it, so this follows from the affine case
`Stacks.Divisors.subschemeι_app_eq_zero_iff_mem` by the sheaf axiom on the closed subscheme. -/
theorem subschemeι_app_eq_zero_of_mem (V : X.Opens) (s : Γ(X, V)) (hs : s ∈ J.obj (op V)) :
    (idealSheafDataOfSubmodule J).subschemeι.app V s = 0 := by
  set I : X.IdealSheafData := idealSheafDataOfSubmodule J
  set i := I.subschemeι
  choose W hW hxW hWV using fun x : V =>
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := V) (x := x.1) x.2
  refine TopCat.Sheaf.eq_of_locally_eq' I.subscheme.sheaf
    (fun x : V => i ⁻¹ᵁ W x) (i ⁻¹ᵁ V)
    (fun x => (Opens.map i.base).map (homOfLE (hWV x))) (fun z hz => ?_) (i.app V s) 0 fun x => ?_
  · exact Opens.mem_iSup.2 ⟨⟨i.base z, hz⟩, hxW ⟨i.base z, hz⟩⟩
  · have hnat := ConcreteCategory.congr_hom (i.naturality (homOfLE (hWV x)).op) s
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hnat
    have hvan : i.app (W x) (X.presheaf.map (homOfLE (hWV x)).op s) = 0 :=
      (subschemeι_app_eq_zero_iff_mem J ⟨W x, hW x⟩ _).2 (J.map_mem (homOfLE (hWV x)).op hs)
    exact (hnat.symm.trans hvan).trans (map_zero _).symm

/-- **Stacks Project, Tag 01QQ, the implication (2) ⇒ (3).** A quasi-coherent sheaf of ideals
`J ⊆ 𝒪_X` on a scheme is the sheaf of ideals of a closed immersion of schemes: the closed
subscheme cut out by `Stacks.Divisors.idealSheafDataOfSubmodule` has, on every affine open, kernel
exactly `J`.

The two remaining implications are proved in
`StacksFrontier/AlgebraicGeometry/Divisors/QuasicoherentIdealSheafData/Equivalence.lean`, where
`Stacks.Divisors.isQuasicoherent_ideal_tfae` assembles the whole tag: (1) ⇔ (2) is
`Stacks.ClosedImmersion.isQuasicoherent_iff_localGenerators`, the sheaf-of-ideals half of Stacks
Tag 01IN, and (3) ⇒ (2) is `Stacks.Divisors.isQuasicoherent_of_ker_app_eq`. Note that the latter
is *not* just quasi-coherence of the kernel of a closed immersion, the other half of Tag 01IN:
that statement is about the categorical kernel of `𝒪_X ⟶ i_* 𝒪_Z`, and the step it leaves open is
the identification of a submodule `J` whose sections agree with the kernel's *with* that kernel.

The equality of ideals below is recorded over affine opens only;
`Stacks.Divisors.subschemeι_app_eq_zero_iff_mem_of_isQuasicoherent` upgrades it to every open,
which is what the statement `Ker(i^♯) = 𝓘` of the tag asks for. -/
@[stacks 01QQ "(2) implies (3), with the equality Ker(i^♯) = J recorded over affine opens only"]
theorem exists_isClosedImmersion_ker_eq :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      ∀ U : X.affineOpens, RingHom.ker (i.app U.1).hom = J.obj (op U.1) :=
  ⟨(idealSheafDataOfSubmodule J).subscheme, (idealSheafDataOfSubmodule J).subschemeι,
    inferInstance, (idealSheafDataOfSubmodule J).ker_subschemeι_app⟩

end Stacks.Divisors

end
