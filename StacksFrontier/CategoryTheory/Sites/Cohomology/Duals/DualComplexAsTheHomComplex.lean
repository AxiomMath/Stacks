module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictClosed
public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.TermsOfADualComplexOfModules

/-!
# The left dual of a complex of modules is the Hom complex into the structure sheaf

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules admitting a left dual
`𝒢^•` in the monoidal category of complexes of `𝒪`-modules, the tensor product being the total
complex of the tensor product of [Stacks, Tag 01CA]. Then

`𝒢^• ≅ SheafHom^•(ℱ^•, 𝒪)`,

the internal Hom complex into the unit — the structure sheaf in degree zero. This is the last
assertion of [Stacks, Tag 0FPA]: the left dual is the complex constructed in
[Stacks, Tag 0FP9].

The argument is uniqueness of right adjoints, not the construction of [Stacks, Tag 0FP9]. Both
`- ⊗ 𝒢^•` and `SheafHom^•(ℱ^•, -)` are right adjoint to `- ⊗ ℱ^•`: the first because of the
exact pairing, the second because the monoidal category of complexes is closed
(`Stacks.SheafOfModules.Strict.monoidalClosedCochainComplex`) and symmetric. So the two agree,
and the isomorphism at the unit is the statement. In particular no decomposition of the
coevaluation into its degreewise components is used, and so the *local* finiteness of that
decomposition — all that is available over a site — is not needed.

Degreewise the dual is the dual sheaf of [Stacks, Tag 0FNY]: in degree `-n` it is
`SheafHom(ℱ^n, 𝒪)`.

## Main definitions

* `Stacks.SheafOfModules.Strict.dualIsoHomComplex`: the identification
  `𝒢^• ≅ SheafHom^•(ℱ^•, 𝒪)`.
* `Stacks.SheafOfModules.Strict.unitXZeroIso`: the degree-zero term of the unit is `𝒪`.

## Main results

* `Stacks.SheafOfModules.Strict.homComplexUnit_X`: the degree-`n` term of `SheafHom^•(ℱ^•, 𝒪)`
  is the product over `p` of the internal homs out of `ℱ^p` into the degree-`p + n` term of the
  unit.
* `Stacks.SheafOfModules.Strict.isZero_unitX`: the unit vanishes outside degree zero. Together
  with `unitXZeroIso` this says that the second argument of the Hom complex is the structure
  sheaf placed in degree zero.
* `Stacks.SheafOfModules.Strict.homComplexUnitIsoDualSheafX`: because the unit is concentrated
  in degree zero, the degree-`-n` term of `SheafHom^•(ℱ^•, 𝒪)` is the single dual sheaf
  `SheafHom(ℱ^n, 𝒪)`.

## Implementation notes

The ambient monoidal structure is `monoidalCategoryCochainComplex`, the same one in which the
local boundedness of [Stacks, Tag 0FPA] and the local finite-freeness of its terms are stated,
so the three assertions of that tag are about one hypothesis. Its closed and symmetric
structures are not instances — complexes carry several of each — so they are seated by `let`
and the abstract statement is applied with them in scope.

`homComplexUnitIsoDualSheafX` is obtained by composing the identification of the complexes with
the degreewise identification `Stacks.SheafOfModules.Strict.dualSheafIsoX_of_complex`, rather
than by collapsing the product of `homComplexUnit_X` factor by factor. The two routes give the
same sheaf, and the composite needs nothing beyond what is already proved, whereas the collapse
would need the internal hom into a zero object to be a zero object and a product with one
surviving factor to be that factor. It does pay for the composite with the local hypotheses of
`dualSheafIsoX_of_complex`, which the identification of the complexes itself does not need.

## References

* [Stacks Project, Tag 0FPA](https://stacks.math.columbia.edu/tag/0FPA)
* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FFR](https://stacks.math.columbia.edu/tag/0FFR)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v}) (K L : CochainComplex (Mod R) ℤ)

/-- **The left dual is the Hom complex into the structure sheaf** — the last assertion of
[Stacks, Tag 0FPA]. If `L` is a left dual of `K` in the monoidal category of complexes of
`𝒪`-modules, then `L` is canonically isomorphic to `SheafHom^•(K, 𝒪)`, the internal Hom complex
into the unit.

The Hom complex is the internal hom `CochainComplex.internalHomComplex` of the closed structure
on complexes: in degree `n` the product over `p` of `SheafHom(ℱ^p, 𝒪^{p+n})`, with the
Hom-complex differential. It is not the realisation
`AlgebraicGeometry.RingedSite.sheafHomComplex` of [Stacks, Tag 0A8X], characterised by its
complexes of sections, and the two are unrelated in this development. -/
def dualIsoHomComplex (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) :
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    L ≅ (ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ)) :=
  let := monoidalCategoryCochainComplex R
  let := symmetricCategoryCochainComplex R
  let := monoidalClosedCochainComplex R
  let := p
  rightDualIsoIhomUnit K L

/-- The degree-`n` term of `SheafHom^•(K, 𝒪)` is the product over `p` of the internal homs out
of `K^p` into the degree-`p + n` term of the unit. -/
theorem homComplexUnit_X (n : ℤ) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := strictMonoidalClosed R
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ))).X n =
      ∏ᶜ fun p : ℤ =>
        (ihom (K.X p)).obj ((𝟙_ (CochainComplex (Mod R) ℤ)).X (p + n)) :=
  rfl

/-- The unit of the monoidal category of complexes is the structure sheaf in degree zero: its
degree-zero term is the unit `𝒪` of `Mod(𝒪)`. -/
def unitXZeroIso :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := monoidalCategoryCochainComplex R
    (𝟙_ (CochainComplex (Mod R) ℤ)).X 0 ≅ 𝟙_ (Mod R) :=
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI := monoidalCategoryCochainComplex R
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (Mod R))

/-- The unit of the monoidal category of complexes vanishes outside degree zero. -/
theorem isZero_unitX (n : ℤ) (hn : n ≠ 0) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := monoidalCategoryCochainComplex R
    IsZero ((𝟙_ (CochainComplex (Mod R) ℤ)).X n) :=
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let := monoidalCategoryCochainComplex R
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (𝟙_ (Mod R)) n hn

variable [HasSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The unit is concentrated in degree zero, so the degree-`-n` term of `SheafHom^•(K, 𝒪)` is
the single dual sheaf `SheafHom(K^n, 𝒪)` of [Stacks, Tag 0FNY]. -/
def homComplexUnitIsoDualSheafX
    (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) (n : ℤ) :
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ))).X (-n) ≅
      dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n) :=
  letI := monoidalCategoryCochainComplex R
  letI := monoidalClosedCochainComplex R
  ((HomologicalComplex.Hom.isoApp (dualIsoHomComplex R K L p) (-n)).symm).trans
    (dualSheafIsoX_of_complex R K L p n)

end Stacks.SheafOfModules.Strict

end

end
