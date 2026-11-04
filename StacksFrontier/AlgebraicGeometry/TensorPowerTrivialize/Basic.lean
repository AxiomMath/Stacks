module

public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic

/-!
# Trivializing a tensor power on a local open, with a named generator

The gluing argument of Stacks Tag 01PW — Properties of Schemes, Lemma 28.18.2 — opens by
choosing a finite affine open cover `X = U_1 ∪ … ∪ U_r` on which the relevant tensor powers of
an invertible `𝒪_X`-module `L` are free of rank one, and on each member it needs a **named**
generator: a section `q_j` of `L ^⊗ d` over `U_j` such that the global section `s` of `L ^⊗ d`
being inverted reads `s|_{U_j} = f_j · q_j`, and such that the generators in the successive
degrees `d, 2d, 3d, …` are the successive powers of that one `q_j`.

Two things are proved here, and the second is the one with content.

**Trivializing a tensor power is free.** `Stacks.Ample.isInvertibleModule_tensorPowModule` says a
tensor power of an invertible module is invertible, and clause 2 of Stacks Tag 0B8M
(`Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible`) trivializes an invertible
module on an open cover. Composing the two trivializes `L ^⊗ n` on an open cover with nothing to
prove, and refining along `Stacks.SheafDescent.Trivialization.comp` puts the trivializing open
inside an affine one. So there is no separate "trivialization of a tensor power" to build: the
statements in the first section below are the two existing theorems applied, and they are
recorded only so that a consumer need not rediscover that they compose.

**A generator that is the restriction of a global section.** What the trivializations produced
that way do *not* carry is a name for the generator: the basis section of
`Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible` is whatever the construction
chose, independently in each degree, so nothing relates the generator in degree `n` to the
generator in degree `2n`. The trivializations built here do carry such a name. Given a global
section `u` of an invertible module `M` and any open `V` inside the nonvanishing open `X_u`, the
map `a ↦ a · u|_W` is bijective for every `W ≤ V` — this is the trivialization clause of Stacks
Tag 01CY, available as `Stacks.NonvanishingSpelling.bijective_smul` — and assembling those
bijections into a `Stacks.SheafDescent.Trivialization` gives a trivialization of `M` over `V`
whose basis section is `u|_V` **on the nose**.

That is what makes the multiplicative family of
`StacksFrontier/AlgebraicGeometry/TensorPowerTrivialize/Power.lean` possible: the powers of a
*global* section are again global sections, multiplication by one of them is a morphism of
sheaves of modules (`Stacks.GradedSections.mulMap`), and so the relation between the generator in
degree `n` and the generator in degree `2n` is an identity between global objects rather than a
fact about two unrelated local choices.

## Main definitions

* `Stacks.TensorPowerTrivialize.resTop`: the restriction of a global section of an `𝒪_X`-module
  to an open subset. A spelling device; it is the shape that
  `Stacks.NonvanishingSpelling.bijective_smul` and `Stacks.NonvanishingOpen.trivTop` both use.
* `Stacks.TensorPowerTrivialize.smulSpan`: multiplication by `u|_W`, as a `Γ(X, W)`-linear map
  `Γ(X, W) →ₗ Γ(M, W)`.
* `Stacks.TensorPowerTrivialize.trivEquiv`: the same map as a linear equivalence, over an open
  inside `X_u`. This is the trivialization clause of Stacks Tag 01CY packaged as a `≃ₗ`.
* `Stacks.TensorPowerTrivialize.trivializationOfSection`: **the trivialization with a named
  generator.** A `Stacks.SheafDescent.Trivialization` of `M` over any open inside `X_u`, whose
  basis section is the restriction of `u`.

## Main results

* `Stacks.TensorPowerTrivialize.basis_trivializationOfSection`: the basis section of that
  trivialization is `u|_V`. This is the whole point of the construction, and it is what lets the
  existing consequences of a trivialization be read as statements about `u`.
* `Stacks.TensorPowerTrivialize.nonvanishingLocus_inter_eq_basicOpen`: on an open `V ≤ X_u`, the
  nonvanishing locus of any global section `s` of `M` meets `V` in the basic open of the ratio
  `s/u`. This is `Stacks.NonvanishingOpen.nonvanishingLocus_inter` with the generator named, and
  it is the step "`X_s ∩ U_j = D(f_j)`" of Tag 01PW's proof.
* `Stacks.TensorPowerTrivialize.exists_isAffineOpen_trivialization`: an **affine** trivializing
  open through every point, by refining an arbitrary one along the affine basis.
* `Stacks.TensorPowerTrivialize.exists_isAffineOpen_trivialization_tensorPowModule`: the same
  for every integer tensor power of an invertible module. The "wall" that a tensor power has no
  local trivialization is not a wall; this is a two-line consequence of theorems already
  in the library. The sibling file does the same for the nonnegative family
  `Stacks.TensorPowers.natTensorPow`, which cannot be named here because stating it needs the
  monoidal structure on `X.Modules` as a local instance.

## Implementation notes

**The scalar spellings do not match syntactically, and `rw` is therefore unusable in the
naturality proof.** A `Stacks.SheafDescent.Trivialization` carries its isomorphisms as
`LinearEquiv`s whose scalar ring is
  `(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf).obj (op W)`
and whose restriction maps are that functor's, while everything proved about `Γ(M, W)` in this
repository and in Mathlib is spelled with `X.presheaf` and `Γ(X, W)`. The two agree
definitionally — the first is the second composed with `forget₂ CommRingCat RingCat` — and not
as terms, so `rw [Scheme.Modules.map_smul]` on a goal produced by the structure fails with "did
not find an occurrence of the pattern". The naturality proof therefore moves to the `X.presheaf`
spelling with a single `change`, does its two rewrites there, and finishes with `congrArg`: the
last step cannot be a `rw` either, because the scalar action inside it is at the other instance
and the rewrite is reported as not type-correct under implicit transparency. This is the gotcha
already recorded in `StacksFrontier/AlgebraicGeometry/NonvanishingOpen/Basic.lean`, met from the
construction side rather than the consumption side.

**`trivEquiv` is `LinearEquiv.ofBijective` of a named linear map, not an ad hoc `Equiv`.** The
`Trivialization` structure asks for `≃ₗ`, and the inverse of `a ↦ a · u|_W` has no formula; going
through `Stacks.NonvanishingSpelling.bijective_smul` and `LinearEquiv.ofBijective` means the
linearity of the inverse is inherited rather than proved.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)

## What is not done

No Stacks attribute is attached to anything in this file. Tag 01CY's trivialization clause is
already carried by `Stacks.NonvanishingTrivialize.isIso_over_nonvanishingOpen`, and what is
proved here is a repackaging of it together with Tag 0B8M; neither tag's statement is the
statement of any declaration below. Tag 01PW itself is *not* proved here, and the remaining
input it needs is identified in the sibling file.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace Stacks.TensorPowerTrivialize

variable {X : Scheme.{u}} (M : X.Modules)

/-! ### Restriction of a global section -/

/-- The restriction of a global section of an `𝒪_X`-module to an open subset. This is the shape
in which `Stacks.NonvanishingSpelling.bijective_smul` and `Stacks.NonvanishingOpen.trivTop`
speak of a global section, written once. -/
noncomputable abbrev resTop (u : Γ(M, ⊤)) (W : X.Opens) : Γ(M, W) :=
  M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u

/-- Restricting the restriction of a global section is restricting it. -/
theorem res_resTop (u : Γ(M, ⊤)) {W W' : X.Opens} (h : W' ⟶ W) :
    M.presheaf.map h.op (resTop M u W) = resTop M u W' := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction is semilinear over restriction of scalars, specialized to a multiple of the
restriction of a global section. The form the naturality of `trivializationOfSection` needs. -/
theorem map_smul_resTop (u : Γ(M, ⊤)) {W W' : X.Opens} (h : W' ⟶ W) (a : Γ(X, W)) :
    M.presheaf.map h.op (a • resTop M u W) = X.presheaf.map h.op a • resTop M u W' := by
  rw [Scheme.Modules.map_smul, res_resTop]

/-! ### Multiplication by a global section -/

/-- **Multiplication by the restriction of a global section**, as a `Γ(X, W)`-linear map. -/
noncomputable def smulSpan (u : Γ(M, ⊤)) (W : X.Opens) : Γ(X, W) →ₗ[Γ(X, W)] Γ(M, W) :=
  LinearMap.toSpanSingleton _ _ (resTop M u W)

/-- `smulSpan M u W` sends `a` to `a` times the restriction of `u` to `W`. -/
@[simp] theorem smulSpan_apply (u : Γ(M, ⊤)) (W : X.Opens) (a : Γ(X, W)) :
    smulSpan M u W a = a • resTop M u W := rfl

variable [Stacks.Ample.IsInvertibleModule X M]

/-- **The trivialization clause of Stacks Tag 01CY as a linear equivalence.** Over an open inside
the nonvanishing open of a global section `u` of an invertible `𝒪_X`-module, multiplication by
`u` is an isomorphism `Γ(X, W) ≃ₗ Γ(M, W)`. -/
noncomputable def trivEquiv (u : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M u) :
    Γ(X, W) ≃ₗ[Γ(X, W)] Γ(M, W) :=
  LinearEquiv.ofBijective (smulSpan M u W)
    (Stacks.NonvanishingSpelling.bijective_smul X M u hW)

/-- `trivEquiv M u hW` sends `a` to `a` times the restriction of `u` to `W`. -/
@[simp] theorem trivEquiv_apply (u : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M u) (a : Γ(X, W)) :
    trivEquiv M u hW a = a • resTop M u W := rfl

/-- The ratio `m/u` of a section by the generator, multiplied back by the generator, is the
section. -/
theorem trivEquiv_symm_smul (u : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M u) (m : Γ(M, W)) :
    (trivEquiv M u hW).symm m • resTop M u W = m :=
  (trivEquiv M u hW).apply_symm_apply m

/-! ### The trivialization with a named generator -/

/-- **A sectionwise trivialization whose basis section is the restriction of a prescribed global
section.** For `u` a global section of an invertible `𝒪_X`-module `M` and `V` any open inside the
nonvanishing open `X_u`, the bijections `Γ(X, W) ≃ Γ(M, W)`, `a ↦ a · u|_W`, for `W ≤ V` assemble
into a `Stacks.SheafDescent.Trivialization` of `M` over `V`.

This is the trivialization that Stacks Tag 01PW's gluing argument needs on each member of its
affine cover: unlike the one produced by clause 2 of Stacks Tag 0B8M, its basis section is a
named global object (`Stacks.TensorPowerTrivialize.basis_trivializationOfSection`), so the
generators in different tensor degrees can be compared. -/
noncomputable def trivializationOfSection (u : Γ(M, ⊤)) {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M u) :
    Stacks.SheafDescent.Trivialization X.presheaf M.val V where
  θ W h := (trivEquiv M u (h.le.trans hV)).symm
  θ_naturality h h' m := by
    refine (LinearEquiv.symm_apply_eq _).mpr ?_
    change M.presheaf.map h'.op m
        = X.presheaf.map h'.op ((trivEquiv M u (h.le.trans hV)).symm m) • resTop M u _
    rw [← map_smul_resTop]
    exact (congrArg _ (trivEquiv_symm_smul M u (h.le.trans hV) m)).symm

/-- The trivializing map of `trivializationOfSection` is division by `u`. -/
theorem triv_trivializationOfSection (u : Γ(M, ⊤)) {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M u) {W : X.Opens} (h : W ⟶ V)
    (m : Γ(M, W)) :
    Stacks.NonvanishingOpen.triv (trivializationOfSection M u hV) h m
      = (trivEquiv M u (h.le.trans hV)).symm m := rfl

/-- **The basis section of `trivializationOfSection` is the restriction of `u`.** -/
theorem basis_trivializationOfSection (u : Γ(M, ⊤)) {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M u) :
    Stacks.NonvanishingOpen.basis (trivializationOfSection M u hV) = resTop M u V := by
  show (trivEquiv M u ((𝟙 V).le.trans hV)).symm.symm 1 = resTop M u V
  rw [LinearEquiv.symm_symm, trivEquiv_apply, one_smul]

/-- **The ratio of a global section by the generator**, and the identity that defines it:
`s|_V = (s/u) · u|_V`. For `V` inside `X_u` this is the unique such scalar. -/
theorem resTop_eq_ratio_smul (u s : Γ(M, ⊤)) {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M u) :
    resTop M s V
      = Stacks.NonvanishingOpen.trivTop (trivializationOfSection M u hV) s • resTop M u V :=
  (trivEquiv_symm_smul M u ((𝟙 V).le.trans hV) (resTop M s V)).symm

/-- **`X_s ∩ V` is the basic open of the ratio `s/u`**, for `V` inside `X_u`. This is
`Stacks.NonvanishingOpen.nonvanishingLocus_inter` at the trivialization whose generator is named,
and it is the step "`X_s ∩ U_j = D(f_j)`" that opens the proof of Stacks Tag 01PW. -/
theorem nonvanishingLocus_inter_eq_basicOpen (u s : Γ(M, ⊤)) {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M u) :
    Stacks.Ample.nonvanishingLocus M s ∩ (V : Set X)
      = (X.basicOpen (Stacks.NonvanishingOpen.trivTop
          (trivializationOfSection M u hV) s) : Set X) :=
  Stacks.NonvanishingOpen.nonvanishingLocus_inter (trivializationOfSection M u hV) s

/-! ### Affine trivializing opens, and tensor powers -/

/-- **An affine trivializing open through every point.** Refine the trivializing open of
`Stacks.SectionProduct.exists_trivialization_at` along the basis of affine opens, and restrict
the trivialization with `Stacks.SheafDescent.Trivialization.comp`. -/
theorem exists_isAffineOpen_trivialization (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧
      Nonempty (Stacks.SheafDescent.Trivialization X.presheaf M.val V) := by
  obtain ⟨V, hxV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at M x
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hVV'⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.2
  exact ⟨V', hxV', hV', ⟨t.comp (homOfLE hVV')⟩⟩

section Powers

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **Every integer tensor power of an invertible `𝒪_X`-module is sectionwise trivial on an
affine open through every point**, at the power family of Stacks Tag 01CU that the ampleness
theory uses. There is nothing to prove: the power is invertible by
`Stacks.Ample.isInvertibleModule_tensorPowModule`, and an invertible module is trivialized on an
affine open by `exists_isAffineOpen_trivialization`. -/
theorem exists_isAffineOpen_trivialization_tensorPowModule (n : ℤ) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧
      Nonempty (Stacks.SheafDescent.Trivialization X.presheaf
        (Stacks.Ample.tensorPowModule X L n).val V) :=
  exists_isAffineOpen_trivialization (Stacks.Ample.tensorPowModule X L n) x

end Powers

end Stacks.TensorPowerTrivialize

end
