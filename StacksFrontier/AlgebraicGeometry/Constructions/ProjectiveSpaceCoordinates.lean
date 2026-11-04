module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjRegrading
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModule
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.LinearAlgebra.SymmetricPower.FreePresentation

/-!
# Homogeneous coordinates on the projective space of a module

The projective space `𝐏(V) = Proj (Sym_k V)` of a module `V` over a commutative ring `k` is
projective `n`-space over `k` as soon as `V` has a basis indexed by `n + 1` elements: a basis
identifies the symmetric algebra with a polynomial ring in `n + 1` variables, compatibly with
the grading, and `Proj` of a graded ring isomorphism is an isomorphism of schemes.

Through that identification a linear system generating an invertible module gets a morphism to
`𝐏(V)`: if `ψ : V → Γ(X, ℒ)` is such that the images `sᵢ = ψ(vᵢ)` of a basis generate `ℒ`, then
the morphism `φ_{(ℒ, (s₀, …, sₙ))} : X ⟶ ℙⁿ_k` of [Stacks, Tag 01ND] composed with the
coordinate isomorphism is the morphism `φ_{ℒ,ψ} : X ⟶ 𝐏(V)` of the source.

## Main definitions

* `AlgebraicGeometry.projectiveSpaceOfModuleIsoProjMvPolynomial`: a basis of `V` indexed by
  `Fin (n + 1)` identifies `𝐏(V)` with `Proj k[T₀, …, Tₙ]`.
* `AlgebraicGeometry.basisProjectiveSpaceOfModuleIso`: **a basis of `V` indexed by
  `Fin (n + 1)` identifies `𝐏(V)` with `ℙⁿ_{Spec k}`, as schemes over `Spec k`.**
* `AlgebraicGeometry.basisProjectiveSpaceIso`: the same isomorphism with the structure
  morphisms forgotten.
* `AlgebraicGeometry.toProjectiveSpaceOfModule`: **the morphism `φ_{ℒ,ψ} : X ⟶ 𝐏(V)` attached
  to a linear system generating an invertible module, in a basis of `V`.**
* `AlgebraicGeometry.basisChangeProjectiveSpaceIso`: **the automorphism of `𝐏(V)` attached to a
  change of basis of `V`**, one coordinate isomorphism inverted and followed by the other.
* `AlgebraicGeometry.finrankProjectiveSpaceOfModuleIso`: the same identification for a vector
  space of dimension `n + 1` over a field, which is the hypothesis the source states.

## Main results

* `AlgebraicGeometry.projectiveSpaceOfModuleIsoProjMvPolynomial_hom_comp_toSpecZero`: the
  identification with the polynomial model is a morphism over `Spec k`.
* `AlgebraicGeometry.toProjectiveSpaceOfModule_comp_toSpec`: `φ_{ℒ,ψ}` is a morphism over `k`.
* `AlgebraicGeometry.toProjectiveSpaceOfModule_comp_basisProjectiveSpaceIso_inv`: the square
  displayed at the end of the source, comparing `φ_{ℒ,ψ}` with `φ_{(ℒ, (s₀, …, sₙ))}`.
* `AlgebraicGeometry.isImmersion_toProjectiveSpaceOfModule_iff`: `φ_{ℒ,ψ}` is an immersion
  exactly when `φ_{(ℒ, (s₀, …, sₙ))}` is.
* `AlgebraicGeometry.toProjectiveSpaceOfModule_comp_basisChangeProjectiveSpaceIso` and
  `AlgebraicGeometry.isImmersion_toProjectiveSpaceOfModule_congr_basis`: **for a fixed generating
  family the basis enters `φ_{ℒ,ψ}` only up to the change-of-basis automorphism of `𝐏(V)`**, so
  being an immersion does not depend on which basis coordinatizes `𝐏(V)`. This is the
  coordinate-isomorphism half of the basis dependence; the other half — the family itself being
  the image of the basis — is discussed at
  `AlgebraicGeometry.isImmersion_toProjectiveSpaceOfModule_congr_basis`.

## What of Tag 0FCY is not proved

The source characterises `φ_{ℒ,ψ}` by an isomorphism `θ : φ^* 𝒪_{𝐏(V)}(1) ≅ ℒ` through which
`ψ` factors. That is not proved here: it needs the identification of `ℒ` with the pullback of
the hyperplane module, the input that [Stacks, Tag 01ND] is itself registered without. The
source's clause that a `k`-valued point of `𝐏(V)` is a one-dimensional quotient of `V` is not
treated in this file either.

## Implementation notes

The graded half of the comparison is `SymPow.gradedMvPolynomialHom` and its inverse
`SymPow.gradedMvPolynomialInv`, which bundle Mathlib's `SymmetricAlgebra.equivMvPolynomial`
together with `SymPow.map_symmetricPower` into mutually inverse homomorphisms of graded rings.
`AlgebraicGeometry.Proj.isIso_map` turns that into an isomorphism of schemes, with the two
irrelevant-ideal hypotheses supplied by
`Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id` — a graded ring homomorphism with a
section satisfies them.

`AlgebraicGeometry.Proj.map` is contravariant, so the isomorphism `𝐏(V) ≅ Proj k[T]` is `Proj`
of the homomorphism `SymPow.gradedMvPolynomialInv` going the other way.

The passage from `Proj k[T₀, …, Tₙ]` to the base-change model
`AlgebraicGeometry.projectiveSpaceOverRing n k`, which is how `ℙⁿ` is defined in this
repository, is `Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`; the only thing
this file adds on that side is the identification of the two spellings of the structure
morphism, which is `Stacks.ProjBaseChange.projZeroRingHom'_comp_algebraMap`.

The source states the comparison for a vector space over a field of dimension `n + 1`. A basis
indexed by `Fin (n + 1)` is what the proof uses, and it is available for a module over a
commutative ring, so the statement is given in that generality; the field case follows by
choosing a basis.

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CommRingCat
open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart

namespace AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k V : Type u} [CommRing k] [AddCommGroup V] [Module k V] {n : ℕ}
  (b : Module.Basis (Fin (n + 1)) k V)

/-- The irrelevant ideal of `k[T₀, …, Tₙ]` is covered by that of `Sym_k V` along a basis, so the
basis induces a morphism `𝐏(V) ⟶ Proj k[T₀, …, Tₙ]`. This is Tag 0FCY. -/
theorem irrelevant_le_map_gradedMvPolynomialHom :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) ≤
      (HomogeneousIdeal.irrelevant (fun i : ℕ => SymPow.symmetricPower i k V)).map
        (SymPow.gradedMvPolynomialHom b) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
    (SymPow.gradedMvPolynomialHom_comp_inv b)

/-- The irrelevant ideal of `Sym_k V` is covered by that of `k[T₀, …, Tₙ]` along a basis, so the
basis induces a morphism `Proj k[T₀, …, Tₙ] ⟶ 𝐏(V)`. This is Tag 0FCY. -/
theorem irrelevant_le_map_gradedMvPolynomialInv :
    HomogeneousIdeal.irrelevant (fun i : ℕ => SymPow.symmetricPower i k V) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).map
        (SymPow.gradedMvPolynomialInv b) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
    (SymPow.gradedMvPolynomialInv_comp_hom b)

/-- **A basis of `V` indexed by `Fin (n + 1)` identifies `𝐏(V)` with `Proj k[T₀, …, Tₙ]`.** This
is the half of Tag 0FCY that reads the symmetric algebra of a module with a finite basis as a
polynomial ring. -/
def projectiveSpaceOfModuleIsoProjMvPolynomial :
    projectiveSpaceOfModule k V ≅
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) :=
  haveI : IsIso (Proj.map (SymPow.gradedMvPolynomialInv b)
      (irrelevant_le_map_gradedMvPolynomialInv b)) :=
    Proj.isIso_map (irrelevant_le_map_gradedMvPolynomialInv b)
      (irrelevant_le_map_gradedMvPolynomialHom b)
      (SymPow.gradedMvPolynomialHom_comp_inv b) (SymPow.gradedMvPolynomialInv_comp_hom b)
  asIso (Proj.map (SymPow.gradedMvPolynomialInv b)
    (irrelevant_le_map_gradedMvPolynomialInv b))

/-- The forward map of `AlgebraicGeometry.projectiveSpaceOfModuleIsoProjMvPolynomial` is
`Proj.map` of the graded homomorphism `SymPow.gradedMvPolynomialInv b : k[T₀, …, Tₙ] → Sym_k V`
of the basis. -/
@[simp]
theorem projectiveSpaceOfModuleIsoProjMvPolynomial_hom :
    (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom =
      Proj.map (SymPow.gradedMvPolynomialInv b)
        (irrelevant_le_map_gradedMvPolynomialInv b) :=
  rfl

/-- The degree-zero part of the comparison: a basis carries the structure map of
`k[T₀, …, Tₙ]` to the structure map of `Sym_k V`, because the underlying algebra isomorphism is
`k`-linear. This is Tag 0FCY. -/
theorem gradedZeroRingHom_gradedMvPolynomialInv_comp_algebraMap :
    (SymPow.gradedMvPolynomialInv b).gradedZeroRingHom.comp
        (algebraMap k ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)) =
      algebraMap k ↥(SymPow.symmetricPower 0 k V) :=
  RingHom.ext fun r => Subtype.ext
    ((SymmetricAlgebra.equivMvPolynomial b).symm.commutes r)

/-- **The identification of `𝐏(V)` with the polynomial model is a morphism over `Spec k`.**
This is Tag 0FCY. -/
theorem projectiveSpaceOfModuleIsoProjMvPolynomial_hom_comp_toSpecZero :
    (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom ≫
        Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) ≫
        Spec.map (ofHom (algebraMap k
          ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0))) =
      projectiveSpaceOfModuleToSpec k V := by
  rw [projectiveSpaceOfModuleIsoProjMvPolynomial_hom, ← Category.assoc,
    Proj.map_toSpecZero, Category.assoc, ← Spec.map_comp, ← ofHom_comp,
    gradedZeroRingHom_gradedMvPolynomialInv_comp_algebraMap]
  rfl

/-- **A basis of `V` indexed by `Fin (n + 1)` identifies the projective space of `V` with
projective `n`-space over `k`, as schemes over `Spec k`.**

This is the assertion of Tag 0FCY that `𝐏(V) ≅ ℙⁿ_k` when `V` has dimension `n + 1`, because
the symmetric algebra on `V` is then a polynomial ring in `n + 1` variables. The isomorphism is
taken in `Over (Spec k)`, so it records compatibility with both structure morphisms and not
only an isomorphism of the underlying schemes. -/
def basisProjectiveSpaceOfModuleIso :
    (projectiveSpaceOfModule k V).asOver (Spec (.of k)) ≅
      (projectiveSpaceOverRing n (.of k)).asOver (Spec (.of k)) := by
  letI c := polynomialComparison k n
  letI e := projectiveSpaceOfModuleIsoProjMvPolynomial b ≪≫ c.iso.symm
  letI : HomIsOver e.hom (Spec (.of k)) := by
    refine ⟨?_⟩
    calc
      e.hom ≫ pullback.fst _ _
          = (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom ≫ c.iso.symm.hom ≫
              c.iso.hom ≫ Proj.toSpecZero (polyGrading k n) ≫
              Spec.map (ofHom (algebraMap k ↥(polyGrading k n 0))) := by
            rw [← Stacks.ProjBaseChange.projZeroRingHom'_comp_algebraMap, c.toBase]; rfl
      _ = (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom ≫
            Proj.toSpecZero (polyGrading k n) ≫
            Spec.map (ofHom (algebraMap k ↥(polyGrading k n 0))) := by
            rw [← Category.assoc c.iso.symm.hom, Iso.symm_hom, Iso.inv_hom_id,
              Category.id_comp]
      _ = projectiveSpaceOfModuleToSpec k V :=
            projectiveSpaceOfModuleIsoProjMvPolynomial_hom_comp_toSpecZero b
  exact e.asOver (Spec (.of k))

section GeneratingSystem

open Stacks.ProjectiveFromSections

/-- **The coordinate isomorphism `ℙⁿ_k ≅ 𝐏(V)` of a basis, as an isomorphism of schemes**:
`AlgebraicGeometry.basisProjectiveSpaceOfModuleIso` with its structure morphisms forgotten. -/
def basisProjectiveSpaceIso :
    projectiveSpaceOverRing n (.of k) ≅ projectiveSpaceOfModule k V :=
  (Over.forget (Spec (.of k))).mapIso (basisProjectiveSpaceOfModuleIso b).symm

/-- The coordinate isomorphism commutes with the two structure morphisms to `Spec k`. -/
theorem basisProjectiveSpaceIso_hom_comp_toSpec :
    (basisProjectiveSpaceIso b).hom ≫ projectiveSpaceOfModuleToSpec k V =
      pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
  Over.w (basisProjectiveSpaceOfModuleIso b).inv

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s) (f : X ⟶ Spec (.of k))

/-- **The morphism `φ_{ℒ,ψ} : X ⟶ 𝐏(V)` of a linear system generating an invertible module.**
Let `v₀, …, vₙ` be a basis of `V` and let `sᵢ = ψ(vᵢ)` be the images under `ψ : V → Γ(X, ℒ)` of
its members, generating `ℒ`. Composing the morphism `φ_{(ℒ, (s₀, …, sₙ))} : X ⟶ ℙⁿ_k` of
[Stacks, Tag 01ND] with the coordinate isomorphism `ℙⁿ_k ≅ 𝐏(V)` of the basis gives the
morphism to `𝐏(V)` itself.

The source speaks of *the* canonical morphism, which is basis free; this construction chooses a
basis, and the square below is the source's own comparison of the two presentations. -/
def toProjectiveSpaceOfModule : X ⟶ projectiveSpaceOfModule k V :=
  toProjectiveSpaceOver s hs f ≫ (basisProjectiveSpaceIso b).hom

/-- **`φ_{ℒ,ψ}` is a morphism of schemes over `k`**: the coordinate isomorphism is one, and
`φ_{(ℒ, (s₀, …, sₙ))}` lies over the structure morphism of `X`. -/
theorem toProjectiveSpaceOfModule_comp_toSpec :
    toProjectiveSpaceOfModule b s hs f ≫ projectiveSpaceOfModuleToSpec k V = f := by
  rw [toProjectiveSpaceOfModule, Category.assoc, basisProjectiveSpaceIso_hom_comp_toSpec]
  exact toProjectiveSpaceOver_fst s hs f

/-- **The square displayed at the end of [Stacks, Tag 0FCY]**: read through the coordinate
isomorphism of the basis, the morphism `φ_{ℒ,ψ} : X ⟶ 𝐏(V)` is the morphism
`φ_{(ℒ, (s₀, …, sₙ))} : X ⟶ ℙⁿ_k` attached to the images of the basis.

The remaining assertion of the source about `φ_{ℒ,ψ}` — that there is an isomorphism
`θ : φ^* 𝒪_{𝐏(V)}(1) ≅ ℒ` through which `ψ` factors as
`V → Γ(𝐏(V), 𝒪(1)) → Γ(X, φ^* 𝒪(1)) → Γ(X, ℒ)` — is **not** proved here. It needs the
identification of `ℒ` with the pullback of the hyperplane module, which is the same input that
[Stacks, Tag 01ND] is registered without; see the tag comment on
`Stacks.ProjectiveFromSections.toProjectiveSpaceOver`. -/
theorem toProjectiveSpaceOfModule_comp_basisProjectiveSpaceIso_inv :
    toProjectiveSpaceOfModule b s hs f ≫ (basisProjectiveSpaceIso b).inv =
      toProjectiveSpaceOver s hs f := by
  rw [toProjectiveSpaceOfModule, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **`φ_{ℒ,ψ}` restricted to the `i`-th standard chart**, read through the coordinate
isomorphism and the integral model: it is the morphism attached to the ratios `sₖ / sᵢ`.
Together with the nonvanishing cover this pins the morphism down. -/
theorem ι_toProjectiveSpaceOfModule (i : Fin (n + 1)) :
    (nvCover s i).ι ≫ toProjectiveSpaceOfModule b s hs f ≫ (basisProjectiveSpaceIso b).inv ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) = chartHom s i := by
  rw [← Category.assoc (toProjectiveSpaceOfModule b s hs f),
    toProjectiveSpaceOfModule_comp_basisProjectiveSpaceIso_inv]
  exact ι_toProjectiveSpaceOver s hs f i

/-- **Being an immersion does not depend on the coordinate presentation**: `φ_{ℒ,ψ}` is an
immersion exactly when `φ_{(ℒ, (s₀, …, sₙ))}` is, because the two differ by an isomorphism. -/
theorem isImmersion_toProjectiveSpaceOfModule_iff :
    IsImmersion (toProjectiveSpaceOfModule b s hs f) ↔
      IsImmersion (toProjectiveSpaceOver s hs f) := by
  rw [toProjectiveSpaceOfModule]
  exact IsImmersion.comp_iff _ _

/-- **The automorphism of `𝐏(V)` attached to a change of basis of `V`**: the coordinate
isomorphism of one basis inverted and followed by the coordinate isomorphism of the other. Under
it the morphism `φ_{ℒ,ψ}` of a fixed generating family read in the first basis becomes the same
morphism read in the second
(`AlgebraicGeometry.toProjectiveSpaceOfModule_comp_basisChangeProjectiveSpaceIso`). -/
def basisChangeProjectiveSpaceIso (b' : Module.Basis (Fin (n + 1)) k V) :
    projectiveSpaceOfModule k V ≅ projectiveSpaceOfModule k V :=
  (basisProjectiveSpaceIso b).symm ≪≫ basisProjectiveSpaceIso b'

/-- **The change-of-basis automorphism of `𝐏(V)` is an automorphism over `Spec k`.** -/
theorem basisChangeProjectiveSpaceIso_hom_comp_toSpec (b' : Module.Basis (Fin (n + 1)) k V) :
    (basisChangeProjectiveSpaceIso b b').hom ≫ projectiveSpaceOfModuleToSpec k V =
      projectiveSpaceOfModuleToSpec k V := by
  rw [basisChangeProjectiveSpaceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    basisProjectiveSpaceIso_hom_comp_toSpec, ← basisProjectiveSpaceIso_hom_comp_toSpec b,
    Iso.inv_hom_id_assoc]

/-- **The basis enters `φ_{ℒ,ψ}` only through the generating family it is paired with.** For a
*fixed* family `s₀, …, sₙ` generating `ℒ`, the morphisms to `𝐏(V)` built in two bases of `V`
differ by the change-of-basis automorphism of `𝐏(V)`. -/
theorem toProjectiveSpaceOfModule_comp_basisChangeProjectiveSpaceIso
    (b' : Module.Basis (Fin (n + 1)) k V) :
    toProjectiveSpaceOfModule b s hs f ≫ (basisChangeProjectiveSpaceIso b b').hom =
      toProjectiveSpaceOfModule b' s hs f := by
  rw [basisChangeProjectiveSpaceIso, Iso.trans_hom, Iso.symm_hom, toProjectiveSpaceOfModule,
    Category.assoc, Iso.hom_inv_id_assoc, toProjectiveSpaceOfModule]

/-- **Being an immersion does not depend on which basis coordinatizes `𝐏(V)`**, the generating
family being held fixed: the two morphisms differ by the change-of-basis automorphism of `𝐏(V)`.

This is *not* the basis-independence of hypothesis (3) of [Stacks, Tag 0FD6]. There the family
is the image `sᵢ = ψ(vᵢ)` of the basis under the linear system, so changing the basis changes the
family too, and the comparison of `φ_{ℒ,ψ}` for two families related by an invertible `k`-linear
substitution is not available here; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniImmersionCondition`. -/
theorem isImmersion_toProjectiveSpaceOfModule_congr_basis
    (b' : Module.Basis (Fin (n + 1)) k V) :
    IsImmersion (toProjectiveSpaceOfModule b s hs f) ↔
      IsImmersion (toProjectiveSpaceOfModule b' s hs f) := by
  rw [isImmersion_toProjectiveSpaceOfModule_iff, isImmersion_toProjectiveSpaceOfModule_iff]

end GeneratingSystem
/-- **A vector space of dimension `n + 1` over a field has projective space `ℙⁿ`.**

This is the form in which Tag 0FCY states the coordinate isomorphism: the hypothesis is the
dimension of `V`, and a basis indexed by `Fin (n + 1)` is then chosen. -/
def finrankProjectiveSpaceOfModuleIso {K W : Type u} [Field K] [AddCommGroup W] [Module K W]
    {m : ℕ} (hdim : Module.finrank K W = m + 1) :
    (projectiveSpaceOfModule K W).asOver (Spec (.of K)) ≅
      (projectiveSpaceOverRing m (.of K)).asOver (Spec (.of K)) :=
  haveI : Module.Finite K W := Module.finite_of_finrank_eq_succ hdim
  basisProjectiveSpaceOfModuleIso (Module.finBasisOfFinrankEq K W hdim)

end AlgebraicGeometry

end
