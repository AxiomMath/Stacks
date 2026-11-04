module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# The degree of a closed subscheme is unchanged by extension of the ground field

Let `k` be a field, let `f : X ⟶ Spec k` be a scheme over `k`, and let `I` be an ideal sheaf on
`X`, cutting out a closed subscheme `C ⊆ X`.  The *degree* of `C` is `h⁰(C, 𝒪_C)`, the dimension
over `k` of the degree-zero cohomology of its structure sheaf; this is the quantity the curve
files of this directory call the degree of an intersection, and
`Stacks.Curves.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_eq_sum` is an
example of a statement about it.

For a field extension `K/k` the inverse image `C_K ⊆ X_K` of `C` in the base change is cut out by
`AlgebraicGeometry.Scheme.IdealSheafData.comap`, and its degree over `K` is the degree of `C` over
`k`:

`h⁰(C_K, 𝒪_{C_K}) = h⁰(C, 𝒪_C)`.

## Main results

* `AlgebraicGeometry.finrank_structureSheafCohomology_zero_eq_finrank_globalSections`: **`h⁰` is
  the dimension of the ring of global functions**, for the `k`-algebra structure the structure
  morphism induces.  This is the bridge between the two presentations of `h⁰` in the tree, and is
  what lets a statement about `AlgebraicGeometry.structureSheafCohomology` be proved from one
  about `Γ(X, ⊤)`.
* `AlgebraicGeometry.finrank_structureSheafCohomology_zero_comap_baseChange`: **the degree of a
  closed subscheme is invariant under extension of the ground field**, stated for the inverse
  image `Scheme.IdealSheafData.comap` of the closed subscheme along the projection of the base
  change, and in terms of `AlgebraicGeometry.structureSheafCohomology`.

## Implementation notes

The content is already available for global sections:
`AlgebraicGeometry.finrank_globalSections_baseChange` says that
`dim_K Γ(X_K, 𝒪_{X_K}) = dim_k Γ(X, 𝒪_X)` for a quasi-compact quasi-separated `X` over `k`.
Two things are needed to reach the statement above.

*Changing presentation.* `AlgebraicGeometry.structureSheafCohomology` in degree zero has the same
dimension as the ring of global functions, by
`AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField` followed by
`AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections`.  This is the
lemma `finrank_structureSheafCohomology_zero_eq_finrank_globalSections` below, applied
once over `k` and once over `K`.  The `k`-module structure on `Γ(X, ⊤)` in play throughout is the
one the structure morphism induces, `((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra`,
introduced by `letI` inside the statements exactly as the consumed lemmas introduce it; matching
those instances syntactically is the only friction in the argument.

*Producing the square.* `AlgebraicGeometry.finrank_globalSections_baseChange` is applied not to
the base-change square of `X` but to the base-change square of `C`, which has to be built.
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso` exhibits `C_K` as `X_K ×_X C`, so
`(I.comap p).subschemeι` is a pullback of `I.subschemeι` along `p`; pasting that square
vertically onto the base-change square of `X` with `CategoryTheory.IsPullback.paste_vert` turns
the comparison morphism `C_K ⟶ C` into a pullback of `I.subschemeι ≫ f` along `Spec K ⟶ Spec k`,
which is the input the global-sections statement wants.

Quasi-compactness and quasi-separatedness are hypothesised on the composite
`I.subschemeι ≫ f` — that is, on `C` over `k`, not on `X` over `k` — because that is the morphism
the global-sections statement is applied to.  No properness and no finiteness: if the degree of
`C` is infinite both sides are `0` by the convention of `Module.finrank`, and the equality still
holds.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **`h⁰` is the dimension of the ring of global functions.**  The degree-zero
`AlgebraicGeometry.structureSheafCohomology` of a scheme over a field has the same dimension as
its ring of global functions, for the algebra structure the structure morphism induces.

This is `AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField` in degree zero composed
with `AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections`. -/
theorem finrank_structureSheafCohomology_zero_eq_finrank_globalSections
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Module.finrank k (structureSheafCohomology f 0) = Module.finrank k Γ(X, ⊤) :=
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  ((structureSheafCohomologyIsoCohomologyOverField k f 0).toLinearEquiv.finrank_eq).trans
    (finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k f)

/-- **The degree of a closed subscheme of a scheme over a field is unchanged by extension of the
ground field.**  Let `f : X ⟶ Spec k` be a scheme over a field `k`, let `K/k` be a field
extension, and let `p : Y ⟶ X`, `q : Y ⟶ Spec K` exhibit `Y` as the base change `X_K`.  For an
ideal sheaf `I` on `X`, cutting out a closed subscheme `C ⊆ X` whose structure morphism
`I.subschemeι ≫ f` is quasi-compact and quasi-separated, the inverse image `I.comap p` cuts out
the base change `C_K ⊆ X_K`, and

`h⁰(C_K, 𝒪_{C_K}) = h⁰(C, 𝒪_C)`,

the degrees being taken over `K` and over `k` respectively.

Taken on a curve this is invariance of the degree of an intersection under extension of the ground
field; the degree here is the `h⁰` of `AlgebraicGeometry.structureSheafCohomology` used throughout
the curve files, so it composes directly with the additivity statements there. -/
theorem finrank_structureSheafCohomology_zero_comap_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (p : Y ⟶ X) (q : Y ⟶ Spec (.of K))
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (I : X.IdealSheafData)
    [QuasiCompact (I.subschemeι ≫ f)] [QuasiSeparated (I.subschemeι ≫ f)] :
    Module.finrank K (structureSheafCohomology ((I.comap p).subschemeι ≫ q) 0)
      = Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) 0) := by
  -- The comparison morphism `C_K ⟶ C`, and the square exhibiting it as a pullback.
  have hcomm : (I.comap p).subschemeι ≫ p =
      ((I.comapIso p).hom ≫ pullback.snd p I.subschemeι) ≫ I.subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst I p, Category.assoc, Category.assoc,
      pullback.condition]
  have hcomap : IsPullback (I.comap p).subschemeι
      ((I.comapIso p).hom ≫ pullback.snd p I.subschemeι) p I.subschemeι :=
    IsPullback.of_iso_pullback ⟨hcomm⟩ (I.comapIso p)
      (Scheme.IdealSheafData.comapIso_hom_fst I p) rfl
  -- Pasting it onto the base-change square of `X` makes `C_K` the base change of `C`.
  have htot : IsPullback ((I.comapIso p).hom ≫ pullback.snd p I.subschemeι)
      ((I.comap p).subschemeι ≫ q) (I.subschemeι ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    hcomap.flip.paste_vert h
  let : Algebra k Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ f).appTop).hom.toAlgebra
  let : Algebra K Γ((I.comap p).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ ((I.comap p).subschemeι ≫ q).appTop).hom.toAlgebra
  rw [finrank_structureSheafCohomology_zero_eq_finrank_globalSections K,
    finrank_structureSheafCohomology_zero_eq_finrank_globalSections k]
  exact finrank_globalSections_baseChange k K (I.subschemeι ≫ f)
    ((I.comapIso p).hom ≫ pullback.snd p I.subschemeι) ((I.comap p).subschemeι ≫ q) htot

end AlgebraicGeometry

end
