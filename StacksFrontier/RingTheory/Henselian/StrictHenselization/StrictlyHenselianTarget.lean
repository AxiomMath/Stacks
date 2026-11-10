module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.StrictHenselization

/-!
# Mapping a strict henselization into a strictly henselian local algebra

Let `A` be a local ring, let `κ_A ⊆ κ^sep` be a separable algebraic closure of its residue field
and let `R` be a strict henselization of `A` with respect to that closure, in the sense of
`Stacks.StrictHenselization.IsStrictHenselization`. This file records the universal property of
`R` in the form in which the *target* is an arbitrary henselian local `A`-algebra rather than a
second strict henselization: a ring map `χ : κ^sep → κ(C)` compatible with the two maps out of `A`
determines exactly one local `A`-algebra map `R → C` inducing it, and when `κ(C)` is separably
closed such a `χ` always exists, so a strictly henselian local `A`-algebra always receives a local
`A`-algebra map from `R`.

The underlying universal property is Lemma 04GU, available as
`HenselianLocalRing.indEtaleAlgHomOfResidue` and its three companions. What is added here is the
translation between the two residue-field conventions that separate 04GU from
`IsStrictHenselization`, and the construction of `χ` from separable closedness alone.

## Main definitions

* `Stacks.StrictHenselization.IsStrictHenselization.residueFieldHom`: the chosen identification of
  the residue field of a strict henselization with `κ^sep`, read as a ring map out of
  `IsLocalRing.ResidueField R` — the convention Lemma 04GU is phrased in — rather than out of
  `(maximalIdeal R).ResidueField`, the convention `IsStrictHenselization` is phrased in.

## Main results

* `Stacks.StrictHenselization.IsStrictHenselization.bijective_residueFieldHom`: that
  identification is bijective, so nothing is lost in passing between the two conventions.
* `Stacks.StrictHenselization.IsStrictHenselization.existsUnique_algHom`: for a henselian local
  `A`-algebra `C` and a ring map `χ : κ^sep → κ(C)` compatible with the residue maps out of `A`,
  there is exactly one local `A`-algebra map `R → C` whose induced map on residue fields is `χ`.
  This is Lemma 04GU with `C` in place of the source's second strict henselization.
* `Stacks.StrictHenselization.IsStrictHenselization.exists_algHom_of_isSepClosed`: a henselian
  local `A`-algebra whose residue field is separably closed receives a local `A`-algebra map from
  `R`. Here no residue datum has to be supplied: `κ^sep` is separable over `κ_A` and `κ(C)` is
  separably closed over it, so `IsSepClosed.lift` produces one.

## Implementation notes

*Why `C` is not assumed to be a strict henselization.* Lemma 04GU asks only that the target be
henselian local, and the chain of reasoning this file is written for — identifying a local ring of
an absolute integral closure with a strict henselization — has a target which is known to be
strictly henselian (by Lemma 0DCS) long before it is known to be a strict henselization of
anything. `StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapFunctoriality`
contains the special case in which `C` is a second strict henselization, as a private lemma.

*The two residue-field conventions.* `IsStrictHenselization` identifies `κ^sep` with
`(maximalIdeal R).ResidueField`, the residue field of the localization of `R` at its maximal
ideal, while Lemma 04GU's residue datum is a map out of `IsLocalRing.ResidueField R = R ⧸ 𝔪_R`.
The canonical map `R ⧸ 𝔪_R → (maximalIdeal R).ResidueField` is a bijection, and
`residueFieldHom` composes it with the inverse of the chosen identification. Only the forward
direction of that bijection is used to *build* the datum, so `bijective_residueFieldHom` is
recorded for the reader rather than needed by the proofs.

*Where the hypothesis `IsLocalHom (algebraMap A C)` comes from.* It is not a restriction: a local
`A`-algebra map `R → C` composed with the local map `A → R` is local, so the conclusion of
`exists_algHom_of_isSepClosed` implies it. It appears as a hypothesis only because the residue map
`κ_A → κ(C)` out of which `χ` is built cannot be written down without it.

## References

* [StacksProject 04GU](https://stacks.math.columbia.edu/tag/04GU), the universal property used
* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP), existence of `A → A^sh`
* [StacksProject 0DCS](https://stacks.math.columbia.edu/tag/0DCS), the source of strictly
  henselian targets this file is written for
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v

namespace Stacks.StrictHenselization

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {κsep : Type*} [Field κsep] [Algebra (maximalIdeal A).ResidueField κsep]
    [IsSepClosure (maximalIdeal A).ResidueField κsep]
  {R : Type v} [CommRing R] [IsLocalRing R] [Algebra A R]

/-- The chosen identification of the residue field of a strict henselization `R` of `A` with the
separable algebraic closure `κ^sep`, read as a ring map out of `IsLocalRing.ResidueField R`.

`IsStrictHenselization` carries the identification as a ring isomorphism
`κ^sep ≃+* (maximalIdeal R).ResidueField`; this composes its inverse with the canonical map
`IsLocalRing.ResidueField R → (maximalIdeal R).ResidueField`. It is bijective, by
`bijective_residueFieldHom`. -/
noncomputable def IsStrictHenselization.residueFieldHom
    (hR : IsStrictHenselization A κsep R) : ResidueField R →+* κsep :=
  hR.residueFieldEquiv.symm.toRingHom.comp
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)

/-- `residueFieldHom` sends `x` to the image under `residueFieldEquiv.symm` of the canonical image
of `x` in `(maximalIdeal R).ResidueField`. -/
theorem IsStrictHenselization.residueFieldHom_apply (hR : IsStrictHenselization A κsep R)
    (x : ResidueField R) :
    hR.residueFieldHom x
      = hR.residueFieldEquiv.symm (algebraMap (ResidueField R) (maximalIdeal R).ResidueField x) :=
  rfl

/-- The canonical map `ResidueField R → (maximalIdeal R).ResidueField` sends `residue R x` to the
image of `x`. -/
private theorem algebraMap_residue_eq (x : R) :
    algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R x)
      = algebraMap R (maximalIdeal R).ResidueField x :=
  (IsScalarTower.algebraMap_apply R (ResidueField R) (maximalIdeal R).ResidueField x).symm

/-- The identification of the residue field of a strict henselization with `κ^sep` is bijective:
the canonical map `R ⧸ 𝔪_R → (maximalIdeal R).ResidueField` is injective because its source is a
field, and surjective because `R → (maximalIdeal R).ResidueField` already is. -/
theorem IsStrictHenselization.bijective_residueFieldHom (hR : IsStrictHenselization A κsep R) :
    Function.Bijective hR.residueFieldHom := by
  have hsurj : Function.Surjective
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField) := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal R) y
    exact ⟨residue R x, (algebraMap_residue_eq x).trans hx⟩
  exact hR.residueFieldEquiv.symm.bijective.comp
    ⟨RingHom.injective (algebraMap (ResidueField R) (maximalIdeal R).ResidueField), hsurj⟩

/-- The identification of the residue field of a strict henselization with `κ^sep` carries the
residue of the image of `a : A` to the image of the residue of `a`: this is the compatibility
clause `IsStrictHenselization.residueFieldEquiv_comp`, transported to the
`IsLocalRing.ResidueField` convention. -/
theorem IsStrictHenselization.residueFieldHom_residue_algebraMap
    (hR : IsStrictHenselization A κsep R) (a : A) :
    hR.residueFieldHom (residue R (algebraMap A R a))
      = algebraMap (maximalIdeal A).ResidueField κsep
          (algebraMap A (maximalIdeal A).ResidueField a) := by
  have := hR.isLocalHom
  apply hR.residueFieldEquiv.injective
  rw [hR.residueFieldHom_apply, RingEquiv.apply_symm_apply,
    algebraMap_residue_eq,
    show hR.residueFieldEquiv (algebraMap (maximalIdeal A).ResidueField κsep
          (algebraMap A (maximalIdeal A).ResidueField a))
        = Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal R) (algebraMap A R)
            (maximalIdeal_comap (algebraMap A R)).symm
            (algebraMap A (maximalIdeal A).ResidueField a) from
      DFunLike.congr_fun hR.residueFieldEquiv_comp _,
    Ideal.ResidueField.map_algebraMap]

/-- **The universal property of the strict henselization against a henselian local algebra**
(Stacks 04GU). Let `A` be a local ring, let `κ^sep` be a separable algebraic closure of its
residue field and let `R` be a strict henselization of `A` with respect to it. Let `C` be a
henselian local `A`-algebra, and let `χ : κ^sep → κ(C)` be a ring map compatible with the residue
maps of `A → R` and `A → C` (the square of fields of the source). Then there is exactly one local
`A`-algebra map `R → C` inducing `χ` on residue fields.

The source states this for `C` a strict henselization of a local ring `S` receiving a local map
from `A`; Lemma 04GU uses of `C` only that it is a henselian local `A`-algebra, and that is the
form taken here, since the target that this is applied to is known to be strictly henselian before
it is known to be a strict henselization. -/
@[stacks 04GU "The universal property read off `IsStrictHenselization`: the residue datum is a map
out of the chosen separable closure `κ^sep` rather than out of `IsLocalRing.ResidueField R`, the
convention `HenselianLocalRing.indEtaleAlgHomOfResidue` is phrased in, and the target is an
arbitrary henselian local `A`-algebra as there. Existence and uniqueness among local `A`-algebra
maps are the source's two assertions.",
  ega "IV 18.8.8" "more general",
  ega "IV 18.8.9" "special case", sga "4 VIII 4.4" "more general"]
theorem IsStrictHenselization.existsUnique_algHom (hR : IsStrictHenselization A κsep R)
    {C : Type*} [CommRing C] [HenselianLocalRing C] [Algebra A C]
    (χ : κsep →+* ResidueField C)
    (hχ : ∀ a : A, χ (algebraMap (maximalIdeal A).ResidueField κsep
        (algebraMap A (maximalIdeal A).ResidueField a))
      = residue C (algebraMap A C a)) :
    ∃! f : R →ₐ[A] C, IsLocalHom f ∧
      (residue C).comp (f : R →+* C) = (χ.comp hR.residueFieldHom).comp (residue R) := by
  have hφ : (χ.comp hR.residueFieldHom).comp ((residue R).comp (algebraMap A R))
      = (residue C).comp (algebraMap A C) := by
    ext a
    simpa only [RingHom.comp_apply, hR.residueFieldHom_residue_algebraMap a] using hχ a
  refine ⟨HenselianLocalRing.indEtaleAlgHomOfResidue hR.isFilteredColimitEtale _ hφ,
    ⟨HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue hR.isFilteredColimitEtale _ hφ,
      HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue hR.isFilteredColimitEtale _ hφ⟩,
    fun g hg => HenselianLocalRing.indEtaleAlgHomOfResidue_unique hR.isFilteredColimitEtale _ hφ
      g hg.1 hg.2⟩

/-- **A strictly henselian local algebra receives a local map from the strict henselization.**
Let `A` be a local ring, let `κ^sep` be a separable algebraic closure of its residue field and let
`R` be a strict henselization of `A` with respect to it. Let `C` be a henselian local `A`-algebra
with separably closed residue field whose structure map is local. Then there is a local
`A`-algebra map `R → C`.

No residue datum has to be supplied: `κ^sep` is separable over `κ_A` and `κ(C)` is a separably
closed field over `κ_A` through the residue map of `A → C`, so `IsSepClosed.lift` produces one,
and `existsUnique_algHom` turns it into the map. Uniqueness is *not* asserted, and genuinely
fails: the local maps `R → C` over `A` are permuted by the automorphisms of `κ^sep` over `κ_A`,
and it is the residue datum that singles one out. -/
@[stacks 04GU "The source's map, in the case where the target's residue field is only known to be
separably closed rather than identified with a chosen separable closure: the residue datum is then
not part of the input but produced by `IsSepClosed.lift`, and only existence survives.",
  ega "IV 18.8.8" "(ii)"]
theorem IsStrictHenselization.exists_algHom_of_isSepClosed (hR : IsStrictHenselization A κsep R)
    (C : Type*) [CommRing C] [HenselianLocalRing C] [Algebra A C]
    [IsLocalHom (algebraMap A C)] (hC : IsSepClosed (ResidueField C)) :
    ∃ f : R →ₐ[A] C, IsLocalHom f := by
  -- The residue map of `A → C`, as a map of residue fields of prime ideals: the maximal ideal of
  -- `A` is the preimage of `(0)` under `A → C → κ(C)`.
  have hbot : maximalIdeal A
      = (⊥ : Ideal (ResidueField C)).comap ((residue C).comp (algebraMap A C)) := by
    rw [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, ker_residue,
      maximalIdeal_comap (algebraMap A C)]
  -- `κ(C)` is the residue field of the zero ideal of `κ(C)`, so that map is a ring map
  -- `κ_A → κ(C)`.
  let : Algebra (maximalIdeal A).ResidueField (ResidueField C) :=
    (((Ideal.algEquivResidueFieldOfField (⊥ : Ideal (ResidueField C))).symm :
          (⊥ : Ideal (ResidueField C)).ResidueField →+* ResidueField C).comp
        (Ideal.ResidueField.map (maximalIdeal A) (⊥ : Ideal (ResidueField C))
          ((residue C).comp (algebraMap A C)) hbot)).toAlgebra
  have halg : ∀ a : A, algebraMap (maximalIdeal A).ResidueField (ResidueField C)
      (algebraMap A (maximalIdeal A).ResidueField a) = residue C (algebraMap A C a) := by
    intro a
    change (Ideal.algEquivResidueFieldOfField (⊥ : Ideal (ResidueField C))).symm
        (Ideal.ResidueField.map (maximalIdeal A) (⊥ : Ideal (ResidueField C))
          ((residue C).comp (algebraMap A C)) hbot
          (algebraMap A (maximalIdeal A).ResidueField a)) = _
    rw [Ideal.ResidueField.map_algebraMap,
      show algebraMap (ResidueField C) (⊥ : Ideal (ResidueField C)).ResidueField
          (((residue C).comp (algebraMap A C)) a)
        = Ideal.algEquivResidueFieldOfField (⊥ : Ideal (ResidueField C))
            (((residue C).comp (algebraMap A C)) a) from rfl,
      AlgEquiv.symm_apply_apply]
    rfl
  have := hC
  have : Algebra.IsSeparable (maximalIdeal A).ResidueField κsep := IsSepClosure.separable
  let χ : κsep →ₐ[(maximalIdeal A).ResidueField] ResidueField C := IsSepClosed.lift
  obtain ⟨f, hf, -⟩ := hR.existsUnique_algHom (C := C) (χ : κsep →+* ResidueField C) fun a => by
    rw [show ((χ : κsep →+* ResidueField C)) (algebraMap (maximalIdeal A).ResidueField κsep
        (algebraMap A (maximalIdeal A).ResidueField a))
      = algebraMap (maximalIdeal A).ResidueField (ResidueField C)
        (algebraMap A (maximalIdeal A).ResidueField a) from χ.commutes _, halg]
  exact ⟨f, hf.1⟩

end Stacks.StrictHenselization

end
