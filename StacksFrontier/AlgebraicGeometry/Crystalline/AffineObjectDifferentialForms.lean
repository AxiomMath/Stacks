module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.DeRhamComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf

/-!
# The crystalline differential forms of an affine object

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `(U, T, δ)` of the
crystalline category whose ambient scheme `T` is affine and whose structure morphism `T ⟶ S`
factors through an affine open `V ⊆ S`.
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso` — [Stacks, Tag 07J0] —
identifies the sections of `Ω_{X/S}` there with the module `Ω¹_{Γ(T,𝒪_T)/Γ(V,𝒪_S),δ}` of divided
power differentials.  This file carries that identification up the exterior powers, so that the
sections of `Ω^i_{X/S}` over the object are `Crystalline.dividedPowerDifferentialForms` of the
divided powers of `Γ(T, 𝒪_T)`.

Both exterior powers are taken over one and the same ring `Γ(T, 𝒪_T)`, so the comparison is the
plain `exteriorPowerCongr` of the degree-one identification; no base change and no semilinearity
enter, and the hypotheses are exactly those of [Stacks, Tag 07J0].

`Crystalline.dpDifferentials` is by construction `Crystalline.dividedPowerDifferentials` of the
algebra underlying a morphism of commutative rings, so its exterior powers are the divided power
differential forms on the nose: this is `Crystalline.extPow_dpDifferentials_eq`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.crysFormSectionsTop` — the sections of `Ω^i_{X/S}` at an
  object as an exterior power, with the ring written as `Γ(T, 𝒪_T)` rather than as a value of the
  presheaf of rings.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso` — **the identification
  of [Stacks, Tag 07J0] in every degree**: the sections of `Ω^i_{X/S}` at an affine object are
  `Ω^i_{Γ(T,𝒪_T)/Γ(V,𝒪_S),δ}`.

## Main results

* `Crystalline.extPow_dpDifferentials_eq` — the exterior powers of the divided power
  differentials of a morphism of commutative rings are the divided power differential forms.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialForms_eq` — the target of the
  identification is `Crystalline.dividedPowerDifferentialForms` of the divided powers of the
  thickening's ring, relative to the sections of the base over `V`.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso_ιMulti_d` — the
  identification carries a wedge `d b₁ ∧ ⋯ ∧ d bᵢ` of universal `S`-derivations to the wedge of
  the universal divided power differentials of the same sections.
* `Crystalline.GlobalCrystallineSituation.smallSite_crysDifferentialForms_obj` — the sections of
  the small-site `Ω^i_{X/S}` over an object are the big-site sections over the same object.

## Implementation notes

`crysFormSectionsTop` names the passage between the two spellings of the ring of sections.
`PresheafOfModules.extPowSections` states the exterior power over
`((structureRingCatPresheaf S).obj (op A) : Type u)`, while the module of divided power
differentials of an affine object is a `ModuleCat.{u} Γ(T, 𝒪_T)`.  The two rings are equal by
`rfl`, and so are the two exterior powers, but they are different `DiscrTree` keys: a `Module`
instance declared at one is invisible at the other, so `LinearEquiv.trans` cannot bridge them
inside unification.  Naming the renaming once, as a definition whose body is the term itself,
removes the problem.

`affineCrysDifferentialForms_eq` applies `Crystalline.dividedPowerDifferentialForms` with all of
its arguments explicit, the algebra instance included.  Written with the instance left to be
synthesized, the statement does not elaborate: the ring `Γ(T, 𝒪_T)` reaches the instance problem
through the ideal of `Crystalline.GlobalCrystallineSituation.crysDividedPowers`, in the unfolded
spelling of the sections of a scheme's structure sheaf, and the algebra given by the structure
morphism is keyed at the folded one.  Supplying it positionally asks for a definitional check
instead of a search, and that check is immediate.

## References

* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Crystalline

/-- **The exterior powers of the divided power differentials of a morphism of commutative rings
are the divided power differential forms.** -/
theorem extPow_dpDifferentials_eq {A B : CommRingCat.{u}} {J : Ideal B} (f : A ⟶ B)
    (hJ : DividedPowers J) (i : ℕ) :
    ⋀[B]^i ↥(dpDifferentials f hJ) =
      letI := f.hom.toAlgebra
      dividedPowerDifferentialForms (A := A) hJ i := rfl

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (A : Thickening S) {V : S.S.scheme.Opens}
  (hVA : (⊤ : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ V)

/-- **The sections of `Ω^i_{X/S}` at an object of `CRIS(X/S)` as an exterior power**, with the
ring of scalars written as the global sections `Γ(T, 𝒪_T)` of the ambient scheme rather than as
the value of the presheaf of rings there.  The two rings are equal by `rfl`. -/
noncomputable def crysFormSectionsTop (i : ℕ) :
    ((crysDifferentialForms S i).obj (op A) : Type u) ≃ₗ[Γ(A.thickening.target.scheme, ⊤)]
      ⋀[Γ(A.thickening.target.scheme, ⊤)]^i ↥(crysDifferentialsObj S A) :=
  crysFormSections S i A

/-- **[Stacks, Tag 07J0] in every degree.**  For an affine object `(U, T, δ)` of `CRIS(X/S)` whose
structure morphism factors through an affine open `V ⊆ S`, the sections of `Ω^i_{X/S}` over it are
the divided power differential forms `Ω^i_{Γ(T,𝒪_T)/Γ(V,𝒪_S),δ}`.

It is `crysFormSectionsTop` — the sections of `Ω^i_{X/S}` are the `i`-th exterior power of the
sections of `Ω_{X/S}` — followed by `exteriorPowerCongr` of
`...affineCrysDifferentialsIso`, the degree-one identification. -/
noncomputable def affineCrysDifferentialFormsIso [IsAffine A.thickening.target.scheme]
    (hV : IsAffineOpen V) (i : ℕ) :
    ((crysDifferentialForms S i).obj (op A) : Type u) ≃ₗ[Γ(A.thickening.target.scheme, ⊤)]
      ⋀[Γ(A.thickening.target.scheme, ⊤)]^i ↥(affineCrysDifferentialsObj S A hVA) :=
  (crysFormSectionsTop S A i).trans
    (exteriorPowerCongr i (affineCrysDifferentialsIso S A hVA hV).toLinearEquiv)

/-- **The target of the identification is the module of divided power differential forms.**  The
`i`-th exterior power of `...affineCrysDifferentialsObj` is
`Crystalline.dividedPowerDifferentialForms` of the divided powers of `Γ(T, 𝒪_T)` over the sections
of the divided power base on `V`. -/
theorem affineCrysDifferentialForms_eq (i : ℕ) :
    ⋀[Γ(A.thickening.target.scheme, ⊤)]^i ↥(affineCrysDifferentialsObj S A hVA) =
      @dividedPowerDifferentialForms (Γ(S.S.scheme, V) : Type u)
        (Γ(A.thickening.target.scheme, ⊤) : Type u) _ _
        (affineBaseAppLE S A hVA).hom.toAlgebra _ (crysDividedPowers S A) i :=
  extPow_dpDifferentials_eq (affineBaseAppLE S A hVA) (crysDividedPowers S A) i

/-- **The identification carries a wedge of sections of `Ω_{X/S}` to the wedge of their
images.** -/
theorem affineCrysDifferentialFormsIso_ιMulti [IsAffine A.thickening.target.scheme]
    (hV : IsAffineOpen V) (i : ℕ) (z : Fin i → ↥(crysDifferentialsObj S A)) :
    affineCrysDifferentialFormsIso S A hVA hV i
        ((crysFormSectionsTop S A i).symm
          (exteriorPower.ιMulti Γ(A.thickening.target.scheme, ⊤) i z)) =
      exteriorPower.ιMulti Γ(A.thickening.target.scheme, ⊤) i fun j ↦
        (affineCrysDifferentialsIso S A hVA hV).hom (z j) := by
  rw [affineCrysDifferentialFormsIso, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact Stacks.exteriorPowerCongr_ιMulti i _ z

/-- **The identification carries `d b₁ ∧ ⋯ ∧ d bᵢ` to `d b₁ ∧ ⋯ ∧ d bᵢ`**: a wedge of universal
`S`-derivations of sections of `𝒪_T` goes to the wedge of the universal divided power
differentials of the same sections.  Those wedges span the sections of `Ω^i_{X/S}`, so this
equation determines the identification. -/
theorem affineCrysDifferentialFormsIso_ιMulti_d [IsAffine A.thickening.target.scheme]
    (hV : IsAffineOpen V) (i : ℕ) (b : Fin i → Γ(A.thickening.target.scheme, ⊤)) :
    affineCrysDifferentialFormsIso S A hVA hV i
        ((crysFormSectionsTop S A i).symm
          (exteriorPower.ιMulti Γ(A.thickening.target.scheme, ⊤) i fun j ↦
            (crysDifferentialsD S A).d (b j))) =
      exteriorPower.ιMulti Γ(A.thickening.target.scheme, ⊤) i fun j ↦
        dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A) (b j) := by
  rw [affineCrysDifferentialFormsIso_ιMulti]
  exact congrArg _ (funext fun j ↦ affineCrysDifferentialsHom_d S A hVA hV (b j))

/-- **The sections of the small-site `Ω^i_{X/S}` over an object are the big-site sections over the
same object of `CRIS(X/S)`.**  The small-site presheaf is the restriction of the big-site one
along the inclusion of `Cris(X/S)` in `CRIS(X/S)`. -/
theorem smallSite_crysDifferentialForms_obj (i : ℕ) (A' : CrystallineThickening S) :
    (SmallSite.crysDifferentialForms S i).obj (op A') =
      (crysDifferentialForms S i).obj (op A'.obj) := rfl

end GlobalCrystallineSituation

end Crystalline

end
