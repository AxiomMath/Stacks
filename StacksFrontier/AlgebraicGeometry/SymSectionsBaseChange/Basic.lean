module

public import StacksFrontier.AlgebraicGeometry.SymSectionsBaseChange.SectionRing
public import StacksFrontier.LinearAlgebra.SymmetricPower.BaseChange
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of the graded ring of sections of `Sym(E)`

Let `g : X' ⟶ X` be a morphism of schemes, `E` a quasi-coherent `𝒪_X`-module, `E'` a
quasi-coherent `𝒪_{X'}`-module, `U` an affine open of `X` and `W` an affine open of `X'` with
`W ≤ g ⁻¹ᵁ U`. **This file proves the graded-ring isomorphism that Tag 0B3V's sixth label needs
at the chart level:**

`Γ(W, Sym(E')) ≅ Γ(X', W) ⊗_{Γ(X, U)} Γ(U, Sym(E))`,

as an isomorphism of `Γ(X', W)`-algebras, from the identification of the sections of `E'` over
`W` with the base change of the sections of `E` over `U`.

## Main definitions

* `Stacks.SymSectionsBaseChange.baseAlgebra`: the `Γ(X, U)`-algebra structure on `Γ(X', W)`,
  through `AlgebraicGeometry.Scheme.Hom.appLE`. Both sides of the main result are stated over it.
* `Stacks.SymSectionsBaseChange.symAlgCongr`: the symmetric algebra of a linear equivalence, as
  an algebra equivalence. `SymPow.symAlgMap` is the functorial algebra homomorphism; nothing
  recorded that it is invertible on an invertible map.
* `Stacks.SymSectionsBaseChange.symSectionTensorEquiv`: the isomorphism with
  `Γ(X', W) ⊗_{Γ(X, U)} Sym_{Γ(X, U)}(Γ(E, U))`, which is the graded form.
* `Stacks.SymSectionsBaseChange.symSectionRingBaseChangeEquiv`: **the graded-ring isomorphism**,
  with `Γ(U, Sym(E))` on the right as the statement of Tag 0B3V spells it.

## Main results

* `Stacks.SymSectionsBaseChange.mem_symmetricPower_symAlgCongr` and
  `mem_baseChange_symAlgBaseChangeEquiv_symm`: the two submodule identities
  (`SymPow.symAlgMap_mapsTo` and `SymPow.map_symAlgBaseChangeEquiv_baseChange`) in the
  membership-equivalence form the grading statement consumes.
* `Stacks.SymSectionsBaseChange.symSectionTensorEquiv_grading`: the isomorphism carries a
  homogeneous section of degree `n` to the base change of the `n`-th symmetric power, so it is an
  isomorphism of **graded** rings.

## The one hypothesis, and why it is a hypothesis

The sections comparison

`hsec : Γ(X', W) ⊗_{Γ(X, U)} Γ(E, U) ≃ₗ[Γ(X', W)] Γ(E', W)`

is **not** an extra assumption in the mathematics: for `E' ≅ g^* E` it is proved in this
repository and public, as `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`
(`StacksFrontier/AlgebraicGeometry/PullbackSections/Affine.lean`), normalised on `1 ⊗ a` by
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul` and natural in the module by
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_natural`. Its helper
`AlgebraicGeometry.affineSectionsLinearEquiv` — `Γ(F|_{Spec Γ(X,U)}, ⊤) ≃ₗ Γ(F, U)` — is public
too, in `StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/AffineSections.lean`.

Taking it as a hypothesis is nevertheless the faithful thing to do: it keeps the *new* content —
the assembly of the degreewise identification, the symmetric-algebra base change and the graded
ring of sections into one graded-ring isomorphism — independent of the affine-chart comparison
it is instantiated with, so that a consumer holding `hsec` for some other reason may use this
file. `Stacks.SymSectionsBaseChangeDischarge.sectionsBaseChangeEquiv` discharges the hypothesis
from that comparison, in exactly the shape asked for here. The affine case of that input,
for a morphism of affine *schemes* rather than of affine opens, is public as well:
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.pullbackΓIso`.

**Every other hypothesis the proof consumes is in the signature**: affineness of `U` and of `W`,
quasi-coherence of `E` and `E'`, the quasi-coherence of the homogeneous pieces of both symmetric
algebras, and `W ≤ g ⁻¹ᵁ U`, which is what makes `Γ(X', W)` a `Γ(X, U)`-algebra at all. The
comparison `E' ≅ g^* E` of Tag 0B3V does *not* appear: it is consumed only in producing `hsec`,
and a consumer that has `hsec` for some other reason may use this.

## Implementation notes

**The composite, left to right.** With `A = Sym(E)`, `A' = Sym(E')`, `R = Γ(X, U)` and
`S = Γ(X', W)`:

1. `Γ(W, A') ≅ Sym_S(Γ(E', W))`, the sibling file's `symSectionAlgEquiv` at `X'`, `W`;
2. `Sym_S(Γ(E', W)) ≅ Sym_S(S ⊗_R Γ(E, U))`, the symmetric algebra of `hsec.symm`;
3. `Sym_S(S ⊗_R Γ(E, U)) ≅ S ⊗_R Sym_R(Γ(E, U))`, the `SymPow.symAlgBaseChangeEquiv`
   — already an `AlgEquiv`, which is why no step of this file touches a symmetric *power*;
4. `S ⊗_R Sym_R(Γ(E, U)) ≅ S ⊗_R Γ(U, A)`, `Algebra.TensorProduct.congr` of the identity with
   the sibling file's `symSectionAlgEquiv` at `X`, `U`, inverted. That version of `congr` is the
   one whose left factor is an `S`-algebra equivalence, so the result is an equivalence of
   `S`-algebras and not merely of `R`-algebras.

**The grading is stated for steps 1-3 and not for the full composite.** After step 3 the
degree-`n` part of the target is `Submodule.baseChange S (Sym^n_R(Γ(E, U)))` on the nose, which
is the grading `Stacks.AlgebraicGeometry.ProjChartBaseChange` puts on a base-changed graded
algebra and therefore what a Proj-level consumer wants; step 4 would replace it by its image
under `Algebra.TensorProduct.congr`, which says nothing more. So
`symSectionTensorEquiv_grading` is stated at `symSectionTensorEquiv`, and
`symSectionRingBaseChangeEquiv` is the spelling of Tag 0B3V for the same isomorphism.

**The grading statement is a membership equivalence, not an equation of submodules**, because the
degree-`n` part of the source is a homogeneous summand of a direct sum and the degree-`n` part of
the target is a submodule of a tensor product: relating them by `AddSubgroup.map` would need both
to be subobjects of one ring, which they are not until the isomorphism is applied.

**The `Γ(X, U)`-algebra structure on a graded ring of sections cannot be
`(A.strHom U).toAlgebra`, and this statement is where that is forced.** The direct sum
`⨁ n, Γ(A.piece n, U)` already carries a pointwise `Γ(X, U)`-module structure, and that is the
one `· ⊗[Γ(X, U)] ·` picks; the module underlying `(A.strHom U).toAlgebra` is a different term,
so with the latter in scope `Γ(X', W) ⊗[Γ(X, U)] A.sectionRing U` has **no `Semiring` instance**
and `symSectionRingBaseChangeEquiv` is not statable at all. The sibling file's
`Stacks.SymGraded.AffinePieces.sectionRingAlgebra` builds it with `Algebra.ofModule'` instead,
keeping the pointwise module; see its docstring.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)

## Not done here

**No tag of 0B3V is attached.** The relevant assertion of Tag 0B3V, the base change of the
projective bundle over the base, is a statement about a global morphism of schemes; this file is
one chart of one of its inputs, and it carries the hypothesis `hsec`, which the tag does not
have.

**Nothing here is at the level of `Proj`.** Turning this into the chart isomorphism of projective
bundles is `Stacks.AlgebraicGeometry.ProjChartBaseChange.isPullback_map_toSpecZero`, which is
proved for an arbitrary graded algebra and an arbitrary base change of its degree-zero part, and
is stated for a grading by `Submodule R A`; the graded ring of sections is graded by
`AddSubgroup`, so a consumer has that translation still to do.

**And the chart isomorphisms do not assemble.**
`Stacks.AlgebraicGeometry.RelativeProjDescent.ChartFamily`, which
`Stacks.ProjBundleBaseChangeReduction.exists_iso_pullback_of_chartFamily` consumes, demands a
chart over *every* affine open of `X'`, while this file gives one only for a `W` lying inside
`g ⁻¹ᵁ U` for an affine `U` — a basis of `X'`, not all of its affine opens. That gap is
independent of everything here and is recorded at `Stacks.ProjBundleBaseChangeReduction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open scoped TensorProduct DirectSum

namespace Stacks.SymSectionsBaseChange

universe u

/-! ### The symmetric algebra of a linear equivalence -/

variable {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **The symmetric algebra of a linear equivalence.** `SymPow.symAlgMap` is the functorial
algebra homomorphism of a linear map; this is the equivalence it is on an equivalence, with the
inverse equivalence's map as inverse. -/
def symAlgCongr (e : M ≃ₗ[R] N) : SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N :=
  AlgEquiv.ofAlgHom (SymPow.symAlgMap e.toLinearMap) (SymPow.symAlgMap e.symm.toLinearMap)
    (SymmetricAlgebra.algHom_ext (LinearMap.ext fun n => by
      change SymPow.symAlgMap e.toLinearMap (SymPow.symAlgMap e.symm.toLinearMap
        (SymmetricAlgebra.ι R N n)) = SymmetricAlgebra.ι R N n
      rw [SymPow.symAlgMap_ι, SymPow.symAlgMap_ι]
      exact congrArg _ (e.apply_symm_apply n)))
    (SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => by
      change SymPow.symAlgMap e.symm.toLinearMap (SymPow.symAlgMap e.toLinearMap
        (SymmetricAlgebra.ι R M m)) = SymmetricAlgebra.ι R M m
      rw [SymPow.symAlgMap_ι, SymPow.symAlgMap_ι]
      exact congrArg _ (e.symm_apply_apply m)))

/-- `symAlgCongr e` sends the generator `ι m` to `ι (e m)`. -/
@[simp]
theorem symAlgCongr_ι (e : M ≃ₗ[R] N) (m : M) :
    symAlgCongr e (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (e m) :=
  SymPow.symAlgMap_ι e.toLinearMap m

/-- **The symmetric algebra of a linear equivalence preserves homogeneity**: a section of the
symmetric algebra lies in the `n`-th symmetric power exactly when its image does. -/
theorem mem_symmetricPower_symAlgCongr (e : M ≃ₗ[R] N) (n : ℕ) (x : SymmetricAlgebra R M) :
    symAlgCongr e x ∈ SymPow.symmetricPower n R N ↔ x ∈ SymPow.symmetricPower n R M := by
  constructor
  · intro h
    have hx := SymPow.symAlgMap_mapsTo n e.symm.toLinearMap _ h
    have heq : (SymPow.symAlgMap e.symm.toLinearMap).toLinearMap (symAlgCongr e x) = x :=
      (symAlgCongr e).symm_apply_apply x
    rwa [heq] at hx
  · exact fun h => SymPow.symAlgMap_mapsTo n e.toLinearMap _ h

/-- **The base change of symmetric algebras preserves homogeneity**, in the direction a consumer
of `SymPow.map_symAlgBaseChangeEquiv_baseChange` needs: a section of `Sym_B(B ⊗_A M)` lies in the
`n`-th symmetric power exactly when its preimage lies in the base change of the `n`-th symmetric
power of `M`. -/
theorem mem_baseChange_symAlgBaseChangeEquiv_symm {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (M : Type u) [AddCommGroup M] [Module A M] (n : ℕ)
    (y : SymmetricAlgebra B (B ⊗[A] M)) :
    (SymPow.symAlgBaseChangeEquiv B M).symm y ∈
        Submodule.baseChange B (SymPow.symmetricPower n A M) ↔
      y ∈ SymPow.symmetricPower n B (B ⊗[A] M) := by
  rw [← SymPow.map_symAlgBaseChangeEquiv_baseChange B M n]
  exact (Submodule.mem_map_equiv (e := (SymPow.symAlgBaseChangeEquiv B M).toLinearEquiv) _).symm

/-! ### The base change of the graded ring of sections -/

open Stacks.SymGraded Stacks.SymGraded.AffinePieces

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {U : X.Opens} {W : X'.Opens}
  (hWU : W ≤ g ⁻¹ᵁ U)

/-- The `Γ(X, U)`-algebra structure on `Γ(X', W)` for `W` inside `g ⁻¹ᵁ U`: the restriction of
`g` on sections. This is the ring over which both sides of the main results are tensored. -/
@[instance_reducible]
def baseAlgebra : Algebra Γ(X, U) Γ(X', W) := (g.appLE U W hWU).hom.toAlgebra

variable (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)
  (E' : X'.Modules) [E'.IsQuasicoherent] (hqc' : IsQuasicoherentPieces E')
  (hU : IsAffineOpen U) (hW : IsAffineOpen W)

/-- **The graded ring of sections of `Sym(E')` over `W` is the base change of the symmetric
algebra of the sections of `E` over `U`**, as `Γ(X', W)`-algebras:

`Γ(W, Sym(E')) ≅ Γ(X', W) ⊗_{Γ(X, U)} Sym_{Γ(X, U)}(Γ(E, U))`.

This is the form whose grading is pinned down — see
`Stacks.SymSectionsBaseChange.symSectionTensorEquiv_grading` — because the right-hand side is
graded by `Submodule.baseChange` of the symmetric powers, which is the grading
`Stacks.AlgebraicGeometry.ProjChartBaseChange` puts on a base-changed graded algebra.
`Stacks.SymSectionsBaseChange.symSectionRingBaseChangeEquiv` composes it with the identification
of `Sym_{Γ(X, U)}(Γ(E, U))` with `Γ(U, Sym(E))`. -/
def symSectionTensorEquiv
    (hsec : letI := baseAlgebra g hWU
      (Γ(X', W) ⊗[Γ(X, U)] Γ(E, U)) ≃ₗ[Γ(X', W)] Γ(E', W)) :
    letI := baseAlgebra g hWU
    letI := sectionAlgebra E' hqc' (V := W)
    (schemeSheafGradedAlgebra E' hqc').sectionRing W ≃ₐ[Γ(X', W)]
      (Γ(X', W) ⊗[Γ(X, U)] SymmetricAlgebra Γ(X, U) Γ(E, U)) :=
  letI := baseAlgebra g hWU
  letI := sectionAlgebra E' hqc' (V := W)
  (symSectionAlgEquiv E' hW hqc').trans
    ((symAlgCongr hsec.symm).trans
      (SymPow.symAlgBaseChangeEquiv (A := Γ(X, U)) Γ(X', W) Γ(E, U)).symm)

omit [E.IsQuasicoherent] in
/-- **The isomorphism is one of graded rings.** A section of `Sym(E')` over `W` is homogeneous of
degree `n` exactly when its image lies in the base change of the `n`-th symmetric power of
`Γ(E, U)`. -/
theorem symSectionTensorEquiv_grading
    (hsec : letI := baseAlgebra g hWU
      (Γ(X', W) ⊗[Γ(X, U)] Γ(E, U)) ≃ₗ[Γ(X', W)] Γ(E', W))
    (n : ℕ) (x : (schemeSheafGradedAlgebra E' hqc').sectionRing W) :
    letI := baseAlgebra g hWU
    letI := sectionAlgebra E' hqc' (V := W)
    x ∈ (schemeSheafGradedAlgebra E' hqc').grading W n ↔
      symSectionTensorEquiv g hWU E E' hqc' hW hsec x ∈
        Submodule.baseChange Γ(X', W) (SymPow.symmetricPower n Γ(X, U) Γ(E, U)) := by
  let _ := baseAlgebra g hWU
  let _ := sectionAlgebra E' hqc' (V := W)
  rw [← mem_symmetricPower_symSectionRingEquiv E' hW hqc' n x]
  refine Iff.symm (Iff.trans ?_ (mem_symmetricPower_symAlgCongr hsec.symm n
    (symSectionRingEquiv E' hW hqc' x)))
  exact mem_baseChange_symAlgBaseChangeEquiv_symm Γ(E, U) n
    (symAlgCongr hsec.symm (symSectionRingEquiv E' hW hqc' x))

/-- **The graded ring of sections of `Sym(E')` over `W` is the base change of the graded ring of
sections of `Sym(E)` over `U`.**

For `U` an affine open of `X`, `W` an affine open of `X'` inside `g ⁻¹ᵁ U`, and `hsec` the
identification of the sections of `E'` over `W` with the base change of the sections of `E` over
`U`, this is an isomorphism of `Γ(X', W)`-algebras

`Γ(W, Sym(E')) ≅ Γ(X', W) ⊗_{Γ(X, U)} Γ(U, Sym(E))`.

It is `Stacks.SymSectionsBaseChange.symSectionTensorEquiv` composed with the sibling file's
identification of `Γ(U, Sym(E))` with `Sym_{Γ(X, U)}(Γ(E, U))`, and that is where its grading is
recorded. -/
def symSectionRingBaseChangeEquiv
    (hsec : letI := baseAlgebra g hWU
      (Γ(X', W) ⊗[Γ(X, U)] Γ(E, U)) ≃ₗ[Γ(X', W)] Γ(E', W)) :
    letI := baseAlgebra g hWU
    letI := sectionAlgebra E hqc (V := U)
    letI := sectionAlgebra E' hqc' (V := W)
    (schemeSheafGradedAlgebra E' hqc').sectionRing W ≃ₐ[Γ(X', W)]
      (Γ(X', W) ⊗[Γ(X, U)] (schemeSheafGradedAlgebra E hqc).sectionRing U) :=
  letI := baseAlgebra g hWU
  letI := sectionAlgebra E hqc (V := U)
  letI := sectionAlgebra E' hqc' (V := W)
  (symSectionTensorEquiv g hWU E E' hqc' hW hsec).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := Γ(X', W)) (A₁ := Γ(X', W)))
      (symSectionAlgEquiv E hU hqc).symm)

end Stacks.SymSectionsBaseChange

end
