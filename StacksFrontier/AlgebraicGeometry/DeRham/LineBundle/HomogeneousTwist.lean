module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.GradedForms

/-!
# Twisting the graded forms of the complement of the zero section by a homogeneous function

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `L^⋆ ⟶ X` the
complement of the zero section of the associated line bundle, the relative spectrum of
`⨁_{n ∈ ℤ} L^{⊗ n}`. Multiplying a relative differential form on `L^⋆` by a function of degree
`m` raises its degree by `m`. This file proves that for the homogeneous generators of
`Stacks.LineBundle.Situation.gradedLaurentForms`, which is the degree bookkeeping behind the
comparison `Ω^p_{L^⋆/S, n} = Ω^p_{L^⋆/S, 0} ⊗ L^{⊗ n}` of Tag 0FUH.

A homogeneous function of `Stacks.LineBundle.Situation.laurentFunction` is available only over
an *affine* open of `X`, the identification of the functions on the inverse image of an open
with the sections of the Laurent algebra being a chart of the relative spectrum. The first
section of this file removes that restriction: the universal map `A ⟶ π_* 𝒪` of Tag 01LX(3)
attaches a function on the inverse image of *any* open of `X` to a section of `L^{⊗ n}` over
it, and over an affine open it is the chart.

## Main definitions

* `Stacks.LineBundle.Situation.laurentFunctionHom`: the universal map
  `⨁_{n ∈ ℤ} L^{⊗ n}(U) ⟶ 𝒪_{L^⋆}(π⁻¹U)` over an open `U` of `X`.
* `Stacks.LineBundle.Situation.laurentFunctionOfOpen`: **a homogeneous function on `L^⋆` over
  the inverse image of an arbitrary open of `X`**, attached to a local section of `L^{⊗ n}`.
* `Stacks.LineBundle.Situation.laurentPreimageHom`: the inverse image in `L^⋆` of an inclusion
  of opens of `X`.

## Main results

* `Stacks.LineBundle.Situation.laurentFunctionOfOpen_affine`: **over an affine open of `X` the
  homogeneous function is the one of `Stacks.LineBundle.Situation.laurentFunction`**, so the
  homogeneous generators of the graded pieces are unchanged.
* `Stacks.LineBundle.Situation.laurentFunctionOfOpen_mul` and
  `Situation.laurentFunctionOfOpen_one`: the homogeneous functions over an arbitrary open
  multiply by adding degrees and carry the algebra unit to `1`.
* `Stacks.LineBundle.Situation.isHomogeneousLaurentForm_smul`: **multiplying a homogeneous form
  of degree `n` by a homogeneous function of degree `m` gives a homogeneous form of degree
  `m + n`.**
* `Stacks.LineBundle.Situation.smul_mem_gradedLaurentForms`: the resulting section of the
  pushed-forward de Rham forms is a section of `Ω^p_{L^⋆/S, m + n}`.
* `Stacks.LineBundle.Situation.isHomogeneousLaurentForm_of_smul`: **the converse, when the
  homogeneous function has a homogeneous inverse.**
* `Stacks.LineBundle.Situation.isHomogeneousLaurentForm_map`: **a homogeneous form of degree `n`
  restricts to a homogeneous form of degree `n`** along an inclusion of affine opens of `X`,
  resting on the naturality of each ingredient of a homogeneous form:
  `Situation.laurentAlgebraSheafIncl_map`, `Situation.laurentFunctionOfOpen_map` and its affine
  form `Situation.laurentFunction_map`, and `Situation.laurentDifferential_map`.
* `Stacks.LineBundle.Situation.laurentFunctionOfOpen_smul` and
  `Situation.laurentFunctionOfOpen_add`: **the homogeneous function is `𝒪_X(U)`-linear and
  additive in the section it is attached to.**
* `Stacks.LineBundle.Situation.laurentSmul`: **multiplication of a section of the pushforward by
  a function on the inverse image**, with `Situation.smul_eq_laurentSmul` identifying the
  `𝒪_X`-action on the pushforward with multiplication by the pullback of the function, and
  `Situation.laurentSmul_add`, `Situation.add_laurentSmul`, `Situation.laurentSmul_smul` and
  `Situation.laurentSmul_map` its additivity, `𝒪_X`-linearity and naturality.

## Implementation notes

The degree computation is an induction on the number of wedge factors, following the recursion
defining `Stacks.LineBundle.Situation.IsHomogeneousLaurentForm`. With no factors the statement
is multiplicativity of the homogeneous functions,
`Stacks.LineBundle.Situation.laurentFunction_mul`; in the inductive step the scalar passes
through the wedge product by linearity of the graded multiplication in its first variable, and
a form of degree `i + j` becomes one of degree `(m + i) + j`.

The converse is stated for a pair of homogeneous functions multiplying to `1` rather than for a
trivialization of `L^{⊗ m}`: what the argument uses is only that multiplication by the function
has a two-sided inverse which is again multiplication by a homogeneous function.

The scalar multiplications of this file are written through `Situation.laurentSmul` rather than
directly, for the reason the next paragraph records at the level of forms: the action of a
function on `L^⋆` on a section of the pushforward is available only at the
`D.laurentFormsAlgebra.piece p` indexing, while a tensor product on `X` needs it at the
pushforward's, and `id (α := ·)` is what moves a term between two indexings that are equal by
`rfl` but not interchangeable for instance search — a type ascription is not, since instance
search reads the term's inferred type and not the ascription.

The restriction of a homogeneous form is proved by the same induction, each step being the
naturality of one ingredient: of the sheafification unit of the ungraded Laurent algebra for the
homogeneous sections, of the universal map of Tag 01LX(3) for the homogeneous functions, of the
universal relative derivation and the exterior generator for `d`, and of the graded
multiplication for the wedge product. Its statement is therefore in the
`D.laurentFormsAlgebra.piece p` spelling: at the `D.laurentForms p` spelling the rewrites by the
multiplication's naturality do not fire, for the reason recorded in the next paragraph.

Sections of `Ω^p_{L^⋆/S}` are written here as sections of `D.laurentFormsAlgebra.piece p`
rather than of the definitionally equal `D.laurentForms p`. Only at the former spelling does
instance search find the multiplication of a form by a function on `L^⋆`: the algebra is
indexed by `Stacks.RingedSpace.structureRingSheaf` of the underlying ringed space, whose
sections over an open are the functions on it, while the sheaf of relative differential forms
is indexed by a spelling in which they are not syntactically the scalars.

## What the global clause still needs

Clause (1) of Tag 0FUH is an identification of quasi-coherent `𝒪_X`-modules,
`Ω^p_{L^⋆/S, n} = Ω^p_{L^⋆/S, 0} ⊗_{𝒪_X} L^{⊗ n}`, for an arbitrary invertible `𝒪_X`-module on
an arbitrary scheme over `S`. **That identification is not proved here**; what is proved above is
its degree bookkeeping on the homogeneous generators over one affine open of `X`. It is proved as
an isomorphism of sheaves of `𝒪_X`-modules by `Stacks.LineBundle.Situation.gradedTwistIso`
(`StacksFrontier/AlgebraicGeometry/DeRham/LineBundle/HomogeneousTwistComparison.lean:372`), whose
file records what the printed clause's quasi-coherence qualifier still asks for beyond that.
Both of the sides are available — the graded piece is
`Stacks.LineBundle.Situation.gradedLaurentForms`
(`StacksFrontier/AlgebraicGeometry/DeRham/LineBundle/GradedForms.lean:301`) and the tensor power is
`Stacks.LineBundle.Situation.tensorPower`
(`StacksFrontier/AlgebraicGeometry/DeRham/LineBundle/Laurent.lean:144`).

What it does *not* need is a description of the graded piece over a chart in terms of the
Laurent polynomial algebra. The degree of a product can be settled by the induction principle
`Stacks.LineBundle.Situation.gradedLaurentForms_le_iff` (`GradedForms.lean:322`) applied to the
sub-`𝒪_X`-module sheaf of sections whose product with a fixed homogeneous function lands in
`Ω^p_{L^⋆/S, n}` after restriction: membership in it is local because `SheafOfModules.Submodule`
carries the locality of membership as a field, in
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Submodule.lean`,
so the inclusion is checked on the homogeneous generators over affine opens, where
`Situation.laurentFunctionOfOpen_affine` above makes the twisting functions the ones
`Situation.smul_mem_gradedLaurentForms` accepts, and where
`Situation.isHomogeneousLaurentForm_map` above moves a homogeneous generator to a smaller
affine open. Two inputs are missing:

* **The multiplication out of the tensor product.** The map
  `(L^⋆ → X)_* Ω^p_{L^⋆/S} ⊗_{𝒪_X} L^{⊗ n} ⟶ (L^⋆ → X)_* Ω^p_{L^⋆/S}` carrying `ω ⊗ x` to
  `Stacks.LineBundle.Situation.laurentFunctionOfOpen n U x • ω`. Its bilinear datum is above —
  `Situation.laurentSmul` with its additivity, `𝒪_X`-linearity and naturality — so what is left
  is `TensorProduct.lift` of that datum over each open and the sheafification adjunction out of
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`. One obstacle to that:
  `PresheafOfModules D.X.ringCatSheaf.obj` carries no `MonoidalCategoryStruct` instance,
  Mathlib's being indexed by a presheaf of *commutative* rings, so both factors have to be read
  at the `TensorSheafification.structureSheaf D.X.sheaf.obj D.X.ringCatSheaf.property` spelling
  before `⊗` elaborates at all. Invertibility of the map is then local, by
  `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`
  (`StacksFrontier/AlgebraicGeometry/AffineBaseChange/Basic.lean:85`) or
  `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop`
  (`StacksFrontier/AlgebraicGeometry/QcohRestrictEquiv/IsoLocality.lean:155`), over the cover
  `Situation.exists_affine_trivializing_cover_over_affine` (`GradedForms.lean:354`).
* **An invertible pair of homogeneous sections.** Over an open trivializing `L` the twisting
  function must be a unit, which asks for sections of `L^{⊗ n}` and of `L^{⊗ -n}` pairing to the
  unit section under `Stacks.SheafOfModules.TensorPower.tensorPowerMulIso`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerMultiplication.lean:379`); that pair
  is the datum `Situation.isHomogeneousLaurentForm_of_smul` above consumes.

Clauses (2) and (3) of the tag are statements about `Ω^p_{L/S, n}`, the degree-`n` part of
`(L → X)_* Ω^p_{L/S}` for the total space itself; the development has the graded pieces of `L^⋆`
only, so those two clauses have no subject to be about yet. Clause (3) compares the two spectra
in positive degree, where no twisting function mediates, so beyond that subject it also needs
each graded piece described over a trivializing affine — for `L^⋆` by
`LaurentDeRham.weightComponent` and for the total space by `PolynomialDeRham.weightComponent`,
the two sides of `PolynomialDeRham.laurentWeightEquiv`
(`StacksFrontier/RingTheory/DeRham/WeightComparison.lean:910`).

## References

* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH), clause (1); what is
  proved here is the degree bookkeeping of its omitted local calculation
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9), the grading of the de
  Rham complex of a graded algebra
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### Homogeneous functions over an arbitrary open of the base -/

/-- The universal map `⨁_{n ∈ ℤ} L^{⊗ n}(U) ⟶ 𝒪_{L^⋆}(π⁻¹U)` of Tag 01LX(3) over an open `U` of
`X`, from the sections of the Laurent algebra over `U` to the functions on the inverse image of
`U` in `L^⋆`. Over an affine open it is the chart of the relative spectrum. -/
def Situation.laurentFunctionHom (U : D.X.Opens) :
    Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U ⟶
      D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) :=
  (Stacks.RelativeSpec.universalAlgebraMap D.laurentRelativeSpecSituation).right.app (op U)

/-- **A homogeneous function on `L^⋆` over the inverse image of an arbitrary open of `X`**: the
function attached to a local section of the `n`th tensor power of the line bundle, with no
affineness hypothesis on the open. -/
def Situation.laurentFunctionOfOpen (n : ℤ) (U : D.X.Opens)
    (x : (D.laurentAlgebra.piece n).val.obj (op U)) :
    D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) :=
  (D.laurentFunctionHom U).hom (D.laurentAlgebraSheafIncl n U x)

/-- Over an affine open of `X` the universal map is the comparison of the affine local model of
`L^⋆`. -/
theorem Situation.laurentFunctionHom_affine (U : D.X.affineOpens) :
    D.laurentFunctionHom U.1 = (D.laurentSectionsIso U).hom :=
  Stacks.RelativeSpec.universalAlgebraMap_app D.laurentRelativeSpecSituation U

/-- **Over an affine open of `X` the homogeneous function over an arbitrary open is the
homogeneous function of the affine local model**, so the two agree wherever both are defined
and the homogeneous generators of `Ω^p_{L^⋆/S, n}` are unchanged. -/
theorem Situation.laurentFunctionOfOpen_affine (n : ℤ) (U : D.X.affineOpens)
    (x : (D.laurentAlgebra.piece n).val.obj (op U.1)) :
    D.laurentFunctionOfOpen n U.1 x = D.laurentFunction n U x := by
  rw [Situation.laurentFunctionOfOpen, D.laurentFunctionHom_affine U]
  rfl

/-- **The homogeneous functions over an arbitrary open multiply by adding degrees.** -/
theorem Situation.laurentFunctionOfOpen_mul (n m : ℤ) (U : D.X.Opens)
    (x : (D.laurentAlgebra.piece n).val.obj (op U))
    (y : (D.laurentAlgebra.piece m).val.obj (op U)) :
    D.laurentFunctionOfOpen n U x * D.laurentFunctionOfOpen m U y =
      D.laurentFunctionOfOpen (n + m) U ((D.laurentAlgebra.mul n m).app (op U) x y) :=
  (map_mul (D.laurentFunctionHom U).hom (D.laurentAlgebraSheafIncl n U x)
      (D.laurentAlgebraSheafIncl m U y)).symm.trans
    (congrArg (D.laurentFunctionHom U).hom (D.laurentAlgebraSheafIncl_mul n m U x y))

/-- **The unit of the Laurent algebra is the constant function `1`** over an arbitrary open. -/
theorem Situation.laurentFunctionOfOpen_one (U : D.X.Opens) :
    D.laurentFunctionOfOpen 0 U (D.laurentAlgebra.one.eval (op U)) = 1 :=
  (congrArg (D.laurentFunctionHom U).hom (D.laurentAlgebraSheafIncl_one U)).trans
    (map_one (D.laurentFunctionHom U).hom)

/-! ### The twist of a homogeneous form by a homogeneous function -/

/-- **Multiplying a homogeneous form of degree `n` by a homogeneous function of degree `m` gives
a homogeneous form of degree `m + n`.** The induction follows the recursion defining the
homogeneous forms: with no wedge factors the two functions multiply by adding degrees, and each
further factor lets the scalar pass by linearity of the graded multiplication. -/
theorem Situation.isHomogeneousLaurentForm_smul (U : D.X.affineOpens) (m : ℤ)
    (y : (D.laurentAlgebra.piece m).val.obj (op U.1)) :
    ∀ (p : ℕ) (n : ℤ)
      (ω : (D.laurentFormsAlgebra.piece (p : ℤ)).val.obj
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1))),
      D.IsHomogeneousLaurentForm U p n ω →
        D.IsHomogeneousLaurentForm U p (m + n) (D.laurentFunction m U y • ω) := by
  intro p
  induction p with
  | zero =>
      rintro n ω ⟨x, rfl⟩
      refine ⟨(D.laurentAlgebra.mul m n).app (op U.1) y x, ?_⟩
      rw [← mul_smul, D.laurentFunction_mul m n U y x]
  | succ q ih =>
      rintro n ω ⟨i, j, hij, η, x, hη, rfl⟩
      refine ⟨m + i, j, by omega, _, x, ih i η hη, ?_⟩
      exact ((D.laurentFormsAlgebra.mul (q : ℤ) 1).map_smul_left
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1)) (D.laurentFunction m U y) η _).symm

/-- **A homogeneous form of degree `n` multiplied by a homogeneous function of degree `m` is a
section of `Ω^p_{L^⋆/S, m + n}`** over the affine open of `X` it is defined on. -/
theorem Situation.smul_mem_gradedLaurentForms {p : ℕ} {n : ℤ} (U : D.X.affineOpens) (m : ℤ)
    (y : (D.laurentAlgebra.piece m).val.obj (op U.1))
    {ω : (D.laurentFormsAlgebra.piece (p : ℤ)).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1))}
    (hω : D.IsHomogeneousLaurentForm U p n ω) :
    D.laurentFunction m U y • ω ∈ (D.gradedLaurentForms p (m + n)).obj (op U.1) :=
  D.mem_gradedLaurentForms U (D.isHomogeneousLaurentForm_smul U m y p n ω hω)

/-- **A form whose product with a homogeneous function of degree `m` is homogeneous of degree
`m + n` is itself homogeneous of degree `n`**, provided that function has an inverse which is
again a homogeneous function. Over an open of `X` trivializing `L` the degree-`m` functions
contain such a pair, which is why the twist of clause (1) of Tag 0FUH is invertible there. -/
theorem Situation.isHomogeneousLaurentForm_of_smul {p : ℕ} {n : ℤ} (U : D.X.affineOpens) (m : ℤ)
    (y : (D.laurentAlgebra.piece m).val.obj (op U.1))
    (y' : (D.laurentAlgebra.piece (-m)).val.obj (op U.1))
    (hy : D.laurentFunction (-m) U y' * D.laurentFunction m U y = 1)
    {ω : (D.laurentFormsAlgebra.piece (p : ℤ)).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1))}
    (hω : D.IsHomogeneousLaurentForm U p (m + n) (D.laurentFunction m U y • ω)) :
    D.IsHomogeneousLaurentForm U p n ω := by
  have h := D.isHomogeneousLaurentForm_smul U (-m) y' p (m + n) _ hω
  rwa [← mul_smul, hy, one_smul, show -m + (m + n) = n by omega] at h

/-! ### Restriction to a smaller affine open -/

section Restrict

/-- The inverse image in `L^⋆` of an inclusion of opens of `X`. -/
def Situation.laurentPreimageHom {U U' : D.X.Opens} (h : U' ≤ U) :
    (D.laurentSpectrumToBase ⁻¹ᵁ U') ⟶ (D.laurentSpectrumToBase ⁻¹ᵁ U) :=
  (Opens.map D.laurentSpectrumToBase.base).map (homOfLE h)

/-- **Restriction carries the homogeneous section of the Laurent algebra sheaf attached to a
local section of `L^{⊗ n}` to the one attached to the restriction of that section.** -/
theorem Situation.laurentAlgebraSheafIncl_map (n : ℤ) {U U' : D.X.Opens} (h : U' ≤ U)
    (x : (D.laurentAlgebra.piece n).val.obj (op U)) :
    (D.laurentAlgebraSheaf.right.obj.map (homOfLE h).op).hom
        (D.laurentAlgebraSheafIncl n U x) =
      D.laurentAlgebraSheafIncl n U' ((D.laurentAlgebra.piece n).val.map (homOfLE h).op x) := by
  refine Eq.trans (NatTrans.naturality_apply
    ((CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology (D.X : TopCat))
      CommRingCat.{u}).unit.app
        (Stacks.RelativeSpec.ungradedCommPresheaf D.X D.laurentAlgebra
          D.laurentAlgebra_mul_comm)) (homOfLE h).op
    (D.laurentAlgebra.toPresheafGradedAlgebra.incl n x)).symm ?_
  exact congrArg (Stacks.RelativeSpec.ungradedCommUnit D.X D.laurentAlgebra
      D.laurentAlgebra_mul_comm U').hom
    (D.laurentAlgebra.toPresheafGradedAlgebra.totalRestrict_incl (homOfLE h).op n x)

/-- **Restricting a homogeneous function on `L^⋆` gives the homogeneous function of the
restricted section**: the homogeneous functions of `Situation.laurentFunctionOfOpen` are natural
in the open of `X`. -/
theorem Situation.laurentFunctionOfOpen_map (n : ℤ) {U U' : D.X.Opens} (h : U' ≤ U)
    (x : (D.laurentAlgebra.piece n).val.obj (op U)) :
    (D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom h).op).hom
        (D.laurentFunctionOfOpen n U x) =
      D.laurentFunctionOfOpen n U' ((D.laurentAlgebra.piece n).val.map (homOfLE h).op x) := by
  refine Eq.trans (NatTrans.naturality_apply
    (Stacks.RelativeSpec.universalAlgebraMap D.laurentRelativeSpecSituation).right
      (homOfLE h).op (D.laurentAlgebraSheafIncl n U x)).symm ?_
  exact congrArg (D.laurentFunctionHom U').hom (D.laurentAlgebraSheafIncl_map n h x)

/-- **Restricting a homogeneous function attached to an affine open gives the homogeneous
function of the restricted section**, the two descriptions agreeing over an affine open. -/
theorem Situation.laurentFunction_map (n : ℤ) {U U' : D.X.affineOpens} (h : U'.1 ≤ U.1)
    (x : (D.laurentAlgebra.piece n).val.obj (op U.1)) :
    (D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom h).op).hom
        (D.laurentFunction n U x) =
      D.laurentFunction n U' ((D.laurentAlgebra.piece n).val.map (homOfLE h).op x) := by
  rw [← D.laurentFunctionOfOpen_affine n U x,
    ← D.laurentFunctionOfOpen_affine n U' ((D.laurentAlgebra.piece n).val.map (homOfLE h).op x)]
  exact D.laurentFunctionOfOpen_map n h x

/-- **The relative de Rham differential of a function on `L^⋆` commutes with restriction.** -/
theorem Situation.laurentDifferential_map {V V' : D.laurentSpectrum.Opens} (g : V' ⟶ V)
    (b : D.laurentSpectrum.sheaf.obj.obj (op V)) :
    (D.laurentForms 1).val.map g.op (D.laurentDifferential V b) =
      D.laurentDifferential V' ((D.laurentSpectrum.sheaf.obj.map g.op).hom b) := by
  refine Eq.trans (PresheafOfModules.naturality_apply
    (Scheme.Modules.exteriorGenerator
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentials D.laurentToBase)).val
      g.op _).symm ?_
  exact congrArg _
    (((AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation D.laurentToBase).d_map
      g.op b).symm)

/-- **A homogeneous form of degree `n` restricts to a homogeneous form of degree `n`** along an
inclusion of affine opens of `X`. This is what makes the degree-`n` part of the pushed-forward
forms readable over a trivializing open: the homogeneous generators of
`Situation.gradedLaurentForms` over one affine open restrict to homogeneous generators over any
smaller one. -/
theorem Situation.isHomogeneousLaurentForm_map {U U' : D.X.affineOpens} (h : U'.1 ≤ U.1) :
    ∀ (p : ℕ) (n : ℤ) (ω : (D.laurentFormsAlgebra.piece (p : ℤ)).val.obj
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1))),
      D.IsHomogeneousLaurentForm U p n ω →
        D.IsHomogeneousLaurentForm U' p n
          ((D.laurentFormsAlgebra.piece (p : ℤ)).val.map (D.laurentPreimageHom h).op ω) := by
  intro p
  induction p with
  | zero =>
      rintro n ω ⟨x, rfl⟩
      refine ⟨(D.laurentAlgebra.piece n).val.map (homOfLE h).op x, ?_⟩
      refine Eq.trans ((D.laurentFormsAlgebra.piece (0 : ℤ)).val.map_smul
        (D.laurentPreimageHom h).op (D.laurentFunction n U x)
        (D.laurentFormsAlgebra.one.eval (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1)))) ?_
      exact congr_arg₂ (· • ·) (D.laurentFunction_map n h x)
        (PresheafOfModules.sections_property D.laurentFormsAlgebra.one
          (D.laurentPreimageHom h).op)
  | succ q ih =>
      rintro n ω ⟨i, j, hij, η, x, hη, rfl⟩
      refine ⟨i, j, hij, _, (D.laurentAlgebra.piece j).val.map (homOfLE h).op x,
        ih i η hη, ?_⟩
      refine Eq.trans ((D.laurentFormsAlgebra.mul (q : ℤ) 1).naturality
        (D.laurentPreimageHom h).op η
        (D.laurentDifferential _ (D.laurentFunction j U x))) ?_
      exact congrArg _ ((D.laurentDifferential_map (D.laurentPreimageHom h) _).trans
        (congrArg (D.laurentDifferential _) (D.laurentFunction_map j h x)))

/-- The function on the inverse image of an open `U` of `X` attached to a function on `U`: the
comorphism of the projection `L^⋆ ⟶ X`, read at the spelling in which the functions on
`π⁻¹U` are the scalars acting on the forms there. -/
def Situation.laurentPullbackFunction (U : D.X.Opens)
    (r : D.X.ringCatSheaf.obj.obj (op U)) :
    D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) :=
  (D.laurentSpectrumToBase.c.app (op U)).hom r

/-- **A homogeneous function on `L^⋆` is `𝒪_X(U)`-linear in the section it is attached to**:
the function of `r • x` is the pullback of `r` along the projection times the function of `x`.
The grading of the Laurent algebra is by `𝒪_X`-submodules and the universal map of Tag 01LX(3)
is a map of `𝒪_X`-algebras, so multiplication of a form by a homogeneous function is bilinear
over `𝒪_X` — which is what lets it be read on a tensor product with `L^{⊗ n}`. -/
theorem Situation.laurentFunctionOfOpen_smul (n : ℤ) (U : D.X.Opens)
    (r : D.X.ringCatSheaf.obj.obj (op U))
    (x : (D.laurentAlgebra.piece n).val.obj (op U)) :
    D.laurentFunctionOfOpen n U (r • x) =
      D.laurentPullbackFunction U r * D.laurentFunctionOfOpen n U x := by
  have hincl : D.laurentAlgebra.toPresheafGradedAlgebra.incl n (r • x) =
      D.laurentAlgebra.toPresheafGradedAlgebra.structureMap (op U) r *
        D.laurentAlgebra.toPresheafGradedAlgebra.incl n x := by
    rw [Stacks.GradedAlgebra.incl_smul]
    exact ((D.laurentAlgebra.toPresheafGradedAlgebra.smul_mul_eq r 1
      (D.laurentAlgebra.toPresheafGradedAlgebra.incl n x)).trans
        (congrArg _ (one_mul _))).symm
  have hA : D.laurentAlgebraSheafIncl n U (r • x) =
      (D.laurentAlgebraSheaf.hom.hom.app (op U)).hom r * D.laurentAlgebraSheafIncl n U x :=
    (congrArg (Stacks.RelativeSpec.ungradedCommUnit D.X D.laurentAlgebra
      D.laurentAlgebra_mul_comm U).hom hincl).trans
      (map_mul (Stacks.RelativeSpec.ungradedCommUnit D.X D.laurentAlgebra
        D.laurentAlgebra_mul_comm U).hom _ _)
  have htri : (D.laurentFunctionHom U).hom
        ((D.laurentAlgebraSheaf.hom.hom.app (op U)).hom r) =
      D.laurentPullbackFunction U r :=
    congrArg (fun m : CategoryTheory.NatTrans D.X.sheaf.obj
        (Under.mk (Stacks.RelativeSpec.gluedSpectrum
          D.laurentRelativeSpecSituation).toBase.c).right =>
      (m.app (op U)).hom r)
      (Under.w (Stacks.RelativeSpec.universalAlgebraMap D.laurentRelativeSpecSituation))
  exact ((congrArg (D.laurentFunctionHom U).hom hA).trans
    (map_mul (D.laurentFunctionHom U).hom _ _)).trans (congrArg (· * _) htri)

/-! ### Multiplying a section of the pushforward by a homogeneous function -/

/-- **Multiplication of a section of `(L^⋆ → X)_* Ω^p_{L^⋆/S}` by a function on the inverse
image of the open it lives over.** The two sides of the scalar multiplication are the same
operation as the one on the forms of `L^⋆`; what this definition adds is the spelling, the
action being available only at the `D.laurentFormsAlgebra.piece p` indexing of the forms and
needed at the pushforward's. -/
def Situation.laurentSmul (p : ℤ) (U : D.X.Opens)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω : (D.laurentFormsPushforward p).val.obj (op U)) :
    (D.laurentFormsPushforward p).val.obj (op U) :=
  id (α := (D.laurentFormsPushforward p).val.obj (op U))
    (f • id (α := (D.laurentFormsAlgebra.piece p).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) ω)

/-- **The `𝒪_X`-action on the pushforward is multiplication by the pullback of the function**:
the module structure of `(L^⋆ → X)_* Ω^p_{L^⋆/S}` over `𝒪_X` is the one restricted along the
comorphism of the projection. -/
theorem Situation.smul_eq_laurentSmul (p : ℤ) (U : D.X.Opens)
    (r : D.X.ringCatSheaf.obj.obj (op U))
    (ω : (D.laurentFormsPushforward p).val.obj (op U)) :
    r • ω = D.laurentSmul p U (D.laurentPullbackFunction U r) ω :=
  rfl

/-- Multiplication by a function is additive in the form. -/
theorem Situation.laurentSmul_add (p : ℤ) (U : D.X.Opens)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω η : (D.laurentFormsPushforward p).val.obj (op U)) :
    D.laurentSmul p U f (ω + η) = D.laurentSmul p U f ω + D.laurentSmul p U f η :=
  smul_add f
    (id (α := (D.laurentFormsAlgebra.piece p).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) ω)
    (id (α := (D.laurentFormsAlgebra.piece p).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) η)

/-- Multiplication by a sum of functions is the sum of the multiplications. -/
theorem Situation.add_laurentSmul (p : ℤ) (U : D.X.Opens)
    (f g : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω : (D.laurentFormsPushforward p).val.obj (op U)) :
    D.laurentSmul p U (f + g) ω = D.laurentSmul p U f ω + D.laurentSmul p U g ω :=
  add_smul f g
    (id (α := (D.laurentFormsAlgebra.piece p).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) ω)

/-- **Multiplication by a function is `𝒪_X(U)`-linear in the form**, the two multiplications
being by functions on the inverse image and those commuting. -/
theorem Situation.laurentSmul_smul (p : ℤ) (U : D.X.Opens)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (r : D.X.ringCatSheaf.obj.obj (op U))
    (ω : (D.laurentFormsPushforward p).val.obj (op U)) :
    D.laurentSmul p U f (r • ω) = r • D.laurentSmul p U f ω := by
  rw [D.smul_eq_laurentSmul p U r ω, D.smul_eq_laurentSmul p U r (D.laurentSmul p U f ω)]
  exact ((smul_smul f (D.laurentPullbackFunction U r) _).trans
    (congrArg (· • id (α := (D.laurentFormsAlgebra.piece p).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) ω) (mul_comm f (D.laurentPullbackFunction U r)))).trans
    (smul_smul (D.laurentPullbackFunction U r) f _).symm

/-- **The homogeneous function is additive in its section.** -/
theorem Situation.laurentFunctionOfOpen_add (n : ℤ) (U : D.X.Opens)
    (x y : (D.laurentAlgebra.piece n).val.obj (op U)) :
    D.laurentFunctionOfOpen n U (x + y) =
      D.laurentFunctionOfOpen n U x + D.laurentFunctionOfOpen n U y :=
  (congrArg (D.laurentFunctionHom U).hom
      ((congrArg (Stacks.RelativeSpec.ungradedCommUnit D.X D.laurentAlgebra
          D.laurentAlgebra_mul_comm U).hom
        (D.laurentAlgebra.toPresheafGradedAlgebra.incl_add n x y)).trans
        (map_add (Stacks.RelativeSpec.ungradedCommUnit D.X D.laurentAlgebra
          D.laurentAlgebra_mul_comm U).hom _ _))).trans
    (map_add (D.laurentFunctionHom U).hom _ _)

/-- **Multiplying by a homogeneous function commutes with restriction**, by the naturality of
the function and of the scalar multiplication. -/
theorem Situation.laurentSmul_map (p : ℤ) {U U' : D.X.Opens} (h : U' ≤ U)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω : (D.laurentFormsPushforward p).val.obj (op U)) :
    (D.laurentFormsPushforward p).val.map (homOfLE h).op (D.laurentSmul p U f ω) =
      D.laurentSmul p U'
        ((D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom h).op).hom f)
        ((D.laurentFormsPushforward p).val.map (homOfLE h).op ω) :=
  (D.laurentFormsAlgebra.piece p).val.map_smul (D.laurentPreimageHom h).op f
    (id (α := (D.laurentFormsAlgebra.piece p).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) ω)

end Restrict


end Stacks.LineBundle

end
