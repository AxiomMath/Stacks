module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DifferentialFormsLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ExteriorPowerComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorRestrictionVanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorSheafGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiDirectImage
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiDirectImageLocalVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc

/-!
# The de Rham complex of `𝒪_{X/S}`, its truncation, and the derivation of [Stacks, Tag 07LM]

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF].
[Stacks, Proposition 60.23.1, Tag 07LM] asserts, for `F` a crystal in quasi-coherent
`𝒪_{X/S}`-modules, that the truncation map of complexes

`(F → F ⊗_{𝒪_{X/S}} Ω¹_{X/S} → F ⊗_{𝒪_{X/S}} Ω²_{X/S} → ⋯) ⟶ F[0]`

becomes a quasi-isomorphism after `Ru_{X/S, *}`, and that `Ru_{X/S, *}(F ⊗ Ω^i_{X/S}) = 0` for
`i > 0`.  The proposition is proved, in the generality of a crystal in quasi-coherent modules, as
`...SmallSite.stacks07LM` of `SmallSite/Proposition07LM.lean`, which carries the tag; the de Rham
complex of a general crystal, with the differentials of its canonical connection of
[Stacks, Tag 07J6], is built in `SmallSite/CrystalDeRhamDifferentials.lean`.  This module supplies
three ingredients of that proof and the case `F = 𝒪_{X/S}` written on presheaves.

## What this module contains

**The vanishing clause, stated.**  `...SmallSite.Vanishing07LM` writes the vanishing at the
generality [Stacks, Tag 07LN] gives it — for every sheaf of `𝒪_{X/S}`-modules satisfying conditions
(1) and (2) of [Stacks, Tag 07JN] — and
`...SmallSite.vanishing07LM_of_isZero_rightDerived_zariskiDirectImageSections` reduces it, by the
local-to-global criterion [Stacks, Tag 072W] for `u_{X/S}`
(`...SmallSite.isZero_derivedZariskiDirectImage_of_locallyIsZero`) and the covering family
`...SmallSite.isCoveringFamily_isAffineOverAffine`, to one affine open of `X` over an affine open
of `S`.  The clause is proved as `...SmallSite.vanishing07LM` of
`SmallSite/Vanishing07LMProof.lean`.

**Leray's acyclicity lemma for `Ru_{X/S, *}`**,
`...SmallSite.isZero_derivedZariskiDirectImageFunctor_obj_of_termwise`: `Ru_{X/S, *}` kills a
bounded below complex of abelian sheaves all of whose terms it kills.  Its two
inputs are `...SmallSite.rightAcyclic_zariskiDirectImage_of_isZero` and
`...SmallSite.isZero_zariskiDirectImage_of_isZero`.  This is the step that carries the vanishing
clause to the leading assertion.

**The complex and the truncation map at `F = 𝒪_{X/S}`**, on presheaves:
`crysDeRhamCochainComplex`, the de Rham complex `𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯` of
[Stacks, Tag 07J4] as a complex of abelian presheaves on `Cris(X/S)`, and `crysDeRhamTruncation`,
its truncation map to `𝒪_{X/S}[0]`; `𝒪_{X/S} ⊗ Ω^i_{X/S} = Ω^i_{X/S}` is
`tensorDifferentialFormsUnitIso`.  `...SmallSite.crysDeRhamSheafComplexFunctor` sheafifies them
termwise, and `...SmallSite.isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamTruncation`
derives from the vanishing clause that `Ru_{X/S, *}` carries the truncation map to an isomorphism:
the truncation map sits in a degreewise split short exact sequence
`0 ⟶ σ^{≥1}K ⟶ K ⟶ K⁰[0] ⟶ 0` (`...SmallSite.crysDeRhamShortComplex`), hence in a distinguished
triangle of `K⁺(Ab(Cris(X/S)))` (`...SmallSite.crysDeRhamTrianglePlus_distinguished`), whose first
vertex `Ru_{X/S, *}(σ^{≥1}K)` vanishes by Leray's lemma.  The same argument, for an arbitrary
complex of abelian sheaves, is
`...SmallSite.isIso_derivedZariskiDirectImageFunctor_map_sheafPlusTruncation` of
`SmallSite/TruncationQuasiIsoSheaf.lean`, and that is the form the proof of the proposition
uses.  None of these declarations carries the tag: they are the case `F = 𝒪_{X/S}` and the steps of
the proof, and the proposition itself is `...SmallSite.stacks07LM`.

The complexes are complexes of abelian presheaves and sheaves, not of `𝒪_{X/S}`-modules: the de
Rham differential is not `𝒪_{X/S}`-linear — already the Leibniz rule in degree zero forbids that.

[Stacks, Tag 07LN] remarks that the vanishing clause holds for any `𝒪_{X/S}`-module satisfying
conditions (1) and (2) of [Stacks, Tag 07JN], and lists two families of non-crystals to which it
therefore applies: `Ω^i_{X/S}` for all `i`, and the sheaf attached to a quasi-coherent
`𝒪_X`-module.  The remark is formalized in `SmallSite/Vanishing07LMProof.lean` (the general
statement, `...SmallSite.isZero_derivedZariskiDirectImage_of_vanishingHypotheses`) and
`SmallSite/Remark07LN.lean` (the two families, `...SmallSite.crysFormsSheaf_vanishing`,
`...SmallSite.underlineModules_vanishing` and `...SmallSite.underlineStructure_vanishing`).  What
is proved here, `crysDifferentialForms_satisfiesVanishingHypotheses`, is the two conditions for the
*presheaf* `Ω^i_{X/S}`, read on its restrictions; the conditions for the sheaf `Ω^i_{X/S}` are
derived from it in `SmallSite/DifferentialFormsSheaf.lean`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.modulePresheaf` and
  `...SmallSite.ofSections` — the abelian presheaf underlying a presheaf of `𝒪_{X/S}`-modules on
  `Cris(X/S)`, and a morphism of such presheaves built from additive maps on sections.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamPresheafHom` — the de Rham
  differential `Ω^i_{X/S} ⟶ Ω^{i+1}_{X/S}` as a morphism of abelian presheaves.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamCochainComplex` — **the complex of
  [Stacks, Tag 07LM] at `F = 𝒪_{X/S}`**, as a `CochainComplex` of abelian presheaves on
  `Cris(X/S)`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamTruncation` — **the truncation map
  of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}`**, to the complex concentrated in degree zero.
* `Crystalline.GlobalCrystallineSituation.SmallSite.Vanishing07LM` — **the vanishing clause of
  [Stacks, Tag 07LM] at the generality of [Stacks, Tag 07LN]**, as a proposition; proved as
  `...SmallSite.vanishing07LM` of `SmallSite/Vanishing07LMProof.lean`.
* `...SmallSite.vanishing07LM_of_isZero_rightDerived_zariskiDirectImageSections` — **the source's
  own reduction of that clause to one affine open**: it holds as soon as every right derived
  functor of `ℋ ↦ Γ(V, u_{X/S, *}ℋ)` kills `F ⊗ Ω^i_{X/S}` for every affine open `V` of `X`
  mapping into an affine open of `S`.  The two site-theoretic inputs, [Stacks, Tag 072W] for
  `u_{X/S}` and the covering family of such opens, are
  `...SmallSite.isZero_derivedZariskiDirectImage_of_locallyIsZero` and
  `...SmallSite.isCoveringFamily_isAffineOverAffine` of
  `SmallSite/ZariskiDirectImageLocalVanishing.lean`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.Vanishing07LMForms` — the same clause at
  `F = 𝒪_{X/S}`, which is the hypothesis of the leading assertion; a specialisation of the
  previous one by `...SmallSite.vanishing07LMForms_of_vanishing07LM` of
  `SmallSite/Vanishing07LMAffineReduction.lean`, and so a theorem as well,
  `...SmallSite.vanishing07LMForms` of `SmallSite/Vanishing07LMProof.lean`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.tensorDifferentialFormsUnitIso` —
  `𝒪_{X/S} ⊗_{𝒪_{X/S}} Ω^i_{X/S} = Ω^i_{X/S}`, which is why the complex below is the complex of
  the proposition at `F = 𝒪_{X/S}`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamSheafComplexFunctor` — the passage
  from an `ℕ`-indexed complex of abelian presheaves to a bounded below complex of abelian
  sheaves, under which `crysDeRhamSheafComplex` and `crysDeRhamSheafTruncation` are the images of
  `crysDeRhamCochainComplex` and `crysDeRhamTruncation`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamShortComplex` and
  `...SmallSite.crysDeRhamTrianglePlus` — the short exact sequence
  `0 ⟶ σ^{≥1}K ⟶ K ⟶ K⁰[0] ⟶ 0` of the truncation map, and the triangle of `K⁺` it generates.

## Main results

* `...SmallSite.isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamTruncation` — **the source's
  derivation of the leading assertion of [Stacks, Tag 07LM] from the tag's own vanishing clause,
  at `F = 𝒪_{X/S}`**: once that clause holds, the truncation map becomes a quasi-isomorphism after
  `Ru_{X/S, *}`.  Its hypothesis-free form is
  `...SmallSite.isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamPlusTruncation` of
  `SmallSite/Vanishing07LMProof.lean`.
* `...SmallSite.crysDeRhamSplitting` and `...SmallSite.crysDeRhamTrianglePlus_distinguished` —
  that short exact sequence is degreewise split, and its triangle is distinguished.
* `...SmallSite.isZero_derivedZariskiDirectImageFunctor_obj_of_termwise` — **Leray's acyclicity
  lemma for `Ru_{X/S, *}`**: it kills a bounded below complex of abelian sheaves all of whose
  terms it kills.  This is the step that carries the vanishing clause of [Stacks, Tag 07LM] to
  its leading assertion.
* `Crystalline.GlobalCrystallineSituation.SmallSite.rightAcyclic_zariskiDirectImage_of_isZero`
  and `...SmallSite.isZero_zariskiDirectImage_of_isZero` — its two inputs.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamDifferential_smul` — the Leibniz
  rule `d (c · ω) = c · d ω + d c ∧ ω` for the de Rham differential on `Cris(X/S)`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamPresheafHom_comp` — consecutive
  differentials compose to zero, so the displayed sequence is a complex.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamCochainComplex_X` and
  `...crysDeRhamCochainComplex_d` — the degree-`i` term is `Ω^i_{X/S}` and the differential is the
  de Rham differential.
* `Crystalline.GlobalCrystallineSituation.crysDifferentialForms_satisfiesVanishingHypotheses` —
  conditions (1) and (2) of [Stacks, Tag 07JN] for the presheaf `Ω^i_{X/S}`, every `i`, read on
  its restrictions to the ambient schemes.
* `Crystalline.GlobalCrystallineSituation.crysDifferentials_satisfiesVanishingHypotheses` — the
  same in degree one, on the big crystalline category.

## References

* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07LN](https://stacks.math.columbia.edu/tag/07LN)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

namespace SmallSite

/-! ### Abelian presheaves on `Cris(X/S)` -/

/-- **The abelian presheaf underlying a presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)`.**  The de
Rham differential is additive but not `𝒪_{X/S}`-linear, so the de Rham complex lives here and not
in presheaves of modules. -/
abbrev modulePresheaf
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) :
    (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (PresheafOfModules.toPresheaf _).obj M

/-- **A morphism of abelian presheaves on `Cris(X/S)` built from additive maps on sections.**  The
hypothesis is compatibility with the transition maps of the site, in the shape the sectionwise
statements of this tree are given in. -/
def ofSections
    {M N : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)}
    (φ : ∀ A : CrystallineThickening S, M.obj (op A) →+ N.obj (op A))
    (hφ : ∀ {A B : CrystallineThickening S} (k : A ⟶ B) (x : M.obj (op B)),
      N.map k.op (φ B x) = φ A (M.map k.op x)) :
    modulePresheaf S M ⟶ modulePresheaf S N where
  app A := AddCommGrpCat.ofHom (φ A.unop)
  naturality _ _ f := by
    ext x
    exact (hφ f.unop x).symm

/-- The section of `ofSections S φ hφ` at `A` is `φ A`. -/
@[simp]
theorem ofSections_app_apply
    {M N : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)}
    (φ : ∀ A : CrystallineThickening S, M.obj (op A) →+ N.obj (op A))
    (hφ : ∀ {A B : CrystallineThickening S} (k : A ⟶ B) (x : M.obj (op B)),
      N.map k.op (φ B x) = φ A (M.map k.op x))
    (A : CrystallineThickening S) (x : M.obj (op A)) :
    (ofSections S φ hφ).app (op A) x = φ A x := rfl

/-! ### `𝒪_{X/S} ⊗ Ω^i_{X/S} = Ω^i_{X/S}` -/

/-- **`𝒪_{X/S} ⊗_{𝒪_{X/S}} Ω^i_{X/S} = Ω^i_{X/S}`**, the left unitor of the tensor product of
presheaves of modules.  This is what makes the complex below the complex of [Stacks, Tag 07LM] at
`F = 𝒪_{X/S}`: the degree-`i` term of that complex is `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`, which for
`F = 𝒪_{X/S}` is `Ω^i_{X/S}`. -/
def tensorDifferentialFormsUnitIso (i : ℕ) :
    tensorDifferentialForms
        (PresheafOfModules.unit (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i ≅
      crysDifferentialForms S i :=
  λ_ (crysDifferentialForms S i)

/-! ### The Leibniz rule of the de Rham differential on `Cris(X/S)` -/

/-- **The Leibniz rule for the de Rham differential on the small crystalline site**:
`d (c · ω) = c · d ω + d c ∧ ω`, with the exact one-form on the left of the wedge.  It is this
identity, and not `𝒪_{X/S}`-linearity, that the differential satisfies.

This is `Crystalline.GlobalCrystallineSituation.CrysDeRhamComplex.differential_smul` read at an
object of `Cris(X/S)`.  It is recorded here because it is exactly the input that makes the
differential of the de Rham complex of a *general* crystal well defined on the tensor product: the
candidate rule `d (s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω` is balanced over `𝒪_{X/S}` precisely because this
Leibniz rule and the one for the connection, [Stacks, Tag 07J6], cancel when a scalar is moved
across the tensor sign.  That is the shape of the argument carried out at the level of a single
ring in `Crystalline.connectionFormPair_balance`; see the module documentation for what is still
missing before it can be run over the site. -/
theorem crysDeRhamDifferential_smul (i : ℕ) (A : CrystallineThickening S)
    (c : crysFormRing S A)
    (ω : ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A))) :
    crysDeRhamDifferential S i A (c • ω) =
      c • crysDeRhamDifferential S i A ω + leftWedge i (crysD S A c) ω :=
  GlobalCrystallineSituation.CrysDeRhamComplex.differential_smul S
    (GlobalCrystallineSituation.crysDeRhamComplex S) i A.obj c ω

/-! ### The de Rham complex of `𝒪_{X/S}` on `Cris(X/S)` -/

/-- **The de Rham differential `Ω^i_{X/S} ⟶ Ω^{i+1}_{X/S}` as a morphism of abelian presheaves on
`Cris(X/S)`.**  Its sectionwise value is the differential of [Stacks, Tag 07J4] and the
compatibility with the transition maps of the site is
`Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamDifferential_naturality`. -/
def crysDeRhamPresheafHom (i : ℕ) :
    modulePresheaf S (crysDifferentialForms S i) ⟶
      modulePresheaf S (crysDifferentialForms S (i + 1)) :=
  ofSections S (fun A ↦ crysDeRhamDifferential S i A)
    (fun k x ↦ crysDeRhamDifferential_naturality S i k x)

/-- On sections over `A`, `crysDeRhamPresheafHom S i` is the de Rham differential
`crysDeRhamDifferential S i A`. -/
@[simp]
theorem crysDeRhamPresheafHom_app_apply (i : ℕ) (A : CrystallineThickening S)
    (ω : (crysDifferentialForms S i).obj (op A)) :
    (crysDeRhamPresheafHom S i).app (op A) ω = crysDeRhamDifferential S i A ω := rfl

/-- **Consecutive de Rham differentials compose to zero**, so the de Rham sequence of
`𝒪_{X/S}` is a complex of abelian presheaves.  This is
`Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamDifferential_squared`, object by
object. -/
theorem crysDeRhamPresheafHom_comp (i : ℕ) :
    crysDeRhamPresheafHom S i ≫ crysDeRhamPresheafHom S (i + 1) = 0 := by
  ext A x
  exact crysDeRhamDifferential_squared S i A.unop x

/-- **The de Rham complex of `𝒪_{X/S}` on `Cris(X/S)`**, the complex

`𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯`

as an honest `CochainComplex` of abelian presheaves on `Cris(X/S)`.  Its degree-`i` term is
`Ω^i_{X/S}`, which by `tensorDifferentialFormsUnitIso` is `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` for
`F = 𝒪_{X/S}`, and its differential is the de Rham differential of [Stacks, Tag 07J4]; that it is
a complex is `crysDeRhamPresheafHom_comp`, which rests on the square-zero property of that
differential and not on any hypothesis.

This is the complex of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}`, written on presheaves; the complex of a
general crystal in quasi-coherent modules, with the differentials of its canonical connection of
[Stacks, Tag 07J6], is `...SmallSite.crystalDeRhamSheafData` of
`SmallSite/CrystalDeRhamDifferentials.lean`. -/
def crysDeRhamCochainComplex :
    CochainComplex ((CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (fun i ↦ modulePresheaf S (crysDifferentialForms S i))
    (fun i ↦ crysDeRhamPresheafHom S i) (fun i ↦ crysDeRhamPresheafHom_comp S i)

/-- The degree-`i` term of the de Rham complex of `𝒪_{X/S}` is `Ω^i_{X/S}`. -/
theorem crysDeRhamCochainComplex_X (i : ℕ) :
    (crysDeRhamCochainComplex S).X i = modulePresheaf S (crysDifferentialForms S i) := rfl

/-- The differential of the de Rham complex of `𝒪_{X/S}` is the de Rham differential. -/
theorem crysDeRhamCochainComplex_d (i : ℕ) :
    (crysDeRhamCochainComplex S).d i (i + 1) = crysDeRhamPresheafHom S i :=
  CochainComplex.of_d (fun i ↦ modulePresheaf S (crysDifferentialForms S i))
    (fun i ↦ crysDeRhamPresheafHom S i) i

/-- **The truncation map of the de Rham complex of `𝒪_{X/S}`**, the map of complexes

`(𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯) ⟶ 𝒪_{X/S}[0]`:

the identity in degree zero, through
`Crystalline.GlobalCrystallineSituation.SmallSite.crysFormsZeroIso`, and zero in every positive
degree.  Nothing has to be checked in positive degrees — a map of `ℕ`-indexed cochain complexes
into a complex concentrated in degree zero is exactly a map out of the degree-zero term, which is
`CochainComplex.toSingle₀Equiv`.

`...SmallSite.isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamPlusTruncation` of
`SmallSite/Vanishing07LMProof.lean` proves that `Ru_{X/S, *}` carries it, read on abelian sheaves,
to an isomorphism. -/
def crysDeRhamTruncation :
    crysDeRhamCochainComplex S ⟶
      (CochainComplex.single₀ ((CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
        (modulePresheaf S
          (PresheafOfModules.unit (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))) :=
  (CochainComplex.toSingle₀Equiv _ _).symm
    ((PresheafOfModules.toPresheaf _).map (crysFormsZeroIso S).inv)

/-- The truncation map is, in degree zero, the degree-zero identification
`Ω^0_{X/S} = 𝒪_{X/S}`. -/
theorem crysDeRhamTruncation_f_zero :
    (crysDeRhamTruncation S).f 0 = (PresheafOfModules.toPresheaf _).map (crysFormsZeroIso S).inv :=
  rfl

/-! ### The vanishing clause of [Stacks, Tag 07LM], at the generality of [Stacks, Tag 07LN] -/

section Vanishing

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- **The vanishing clause of [Stacks, Tag 07LM], at the generality [Stacks, Tag 07LN] gives
it.**  For a sheaf of `𝒪_{X/S}`-modules `F` on the small crystalline site satisfying conditions
(1) and (2) of [Stacks, Tag 07JN] — locally quasi-coherent, and with locally surjective comparison
morphisms along closed immersions — and for every `i > 0`,

`Ru_{X/S, *}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`.

[Stacks, Tag 07LM] states this for `F` a crystal in quasi-coherent modules; [Stacks, Tag 07LN]
observes that the proof uses only (1) and (2), and that is the form written here.  A crystal in
quasi-coherent modules satisfies both by [Stacks, Tag 07IT].  The remark's non-crystals are
covered by the same statement once they are presented as sheaves of modules, which is done in
`SmallSite/Remark07LN.lean`: for the sheaf `Ω^i_{X/S}` (`...SmallSite.crysFormsSheaf`, built from
the presheaf in `SmallSite/DifferentialFormsSheaf.lean`) and for the sheaves `F̲` of
`SmallSite/UnderlineSheaf.lean`.

This is a proposition here rather than a theorem, and nothing in *this file* either proves or
consumes it — the derivation of the leading assertion below is stated against `Vanishing07LMForms`
instead.  `...SmallSite.vanishing07LM` of `SmallSite/Vanishing07LMProof.lean`
proves it with the global crystalline situation as its only hypothesis, and the two specialisations
in `SmallSite/Vanishing07LMAffineReduction.lean` consume it — to a crystal in quasi-coherent
modules, which is the "in fact" clause of [Stacks, Tag 07LM], and to `F = 𝒪_{X/S}`.

Its content over an affine base is [Stacks, Tag 07LF], and **that is a theorem**:
`...SmallSite.vanishing07LF` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelFormsCosimplicialIso.lean` proves
`Vanishing07LF` outright and carries the `@[stacks 07LF]` attribute.  The passage from that
statement about cohomology *groups* over an affine base to the vanishing of the derived direct
image is reduced, by `vanishing07LM_of_isZero_rightDerived_zariskiDirectImageSections` below, to
one statement about one affine open of `X` mapping into an affine open of `S`: the local-to-global
half of it — [Stacks, Tag 072W] for `u_{X/S}` and the covering family of such opens — is proved in
`SmallSite/ZariskiDirectImageLocalVanishing.lean`, and the identification of the pieces with the
cohomology of the restricted site is proved in `SmallSite/RestrictedSiteSections.lean`.  The
fourth step is the transport of the coefficients along that restriction,
`...SmallSite.Transport07LMForms` of `SmallSite/Vanishing07LMAffineReduction.lean`, from which
`...SmallSite.vanishing07LM_of_transport07LMForms` derives this proposition; that step is proved
as `...SmallSite.transport07LMForms` of
`SmallSite/Vanishing07LMProof.lean`.
**No tag attribute is placed here**: this is the statement of the clause, and the tag sits on the
theorem that asserts it, in `SmallSite/Vanishing07LMProof.lean`. -/
def Vanishing07LM : Prop :=
  ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
    CohomologyRestriction.IsSurjectiveComparison F.val → ∀ i : ℕ, 0 < i →
      IsZero ((derivedZariskiDirectImage S).obj (tensorDifferentialFormsSheaf F i))

/-- **`Vanishing07LM` is the affine-local vanishing of the sections functors of `u_{X/S, *}`.**
This is the reduction the source's proof performs: it passes to an affine open `V ⊆ X` mapping into
an affine open of `S`, where the whole situation is affine and [Stacks, Tag 07LF] applies.

The two site-theoretic inputs are the ones proved in
`SmallSite/ZariskiDirectImageLocalVanishing.lean`:
`...SmallSite.isZero_derivedZariskiDirectImage_of_locallyIsZero`, which is [Stacks, Tag 072W] for
`u_{X/S}` as a vanishing criterion, and `...SmallSite.isCoveringFamily_isAffineOverAffine`, which
says the opens in question cover `X`.  The hypothesis here is therefore exactly the per-open
statement, with no site theory left in it. -/
theorem vanishing07LM_of_isZero_rightDerived_zariskiDirectImageSections
    (h : ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
      CohomologyRestriction.IsSurjectiveComparison F.val → ∀ i : ℕ, 0 < i → ∀ p : ℕ,
        ∀ V : S.X.Opens, IsAffineOverAffine S V →
          IsZero (((zariskiDirectImageSections S V).rightDerived p).obj
            (tensorDifferentialFormsSheaf F i))) :
    Vanishing07LM S := by
  intro F hqc hsurj i hi
  refine isZero_derivedZariskiDirectImage_of_locallyIsZero S _ fun p V ↦ ?_
  obtain ⟨R, hR, hRaff⟩ := isCoveringFamily_isAffineOverAffine S V
  exact ⟨R, hR, fun _ _ hf ↦ h F hqc hsurj i hi p _ (hRaff hf)⟩

/-- **An abelian sheaf killed by `Ru_{X/S, *}` is `u_{X/S, *}`-acyclic.**  Part (2) of
[Stacks, Tag 015C] characterises acyclicity by the vanishing of `R^i u_{X/S, *}` in positive
degrees, `u_{X/S, *}` being left exact; and those are the positive cohomology sheaves of
`Ru_{X/S, *}`, which vanish along with it. -/
theorem rightAcyclic_zariskiDirectImage_of_isZero
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (h : IsZero ((derivedZariskiDirectImage S).obj G)) :
    (zariskiDirectImage S).rightAcyclic G :=
  ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus (zariskiDirectImage S) G).2
    inferInstance).2 fun i _ ↦
      Functor.map_isZero (DerivedCategory.Plus.homologyFunctor _ i) h

/-- **An abelian sheaf killed by `Ru_{X/S, *}` is killed by `u_{X/S, *}`.**  The underived direct
image is the degree-zero cohomology sheaf of the derived one,
`higherZariskiDirectImageZeroIso`. -/
theorem isZero_zariskiDirectImage_of_isZero
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (h : IsZero ((derivedZariskiDirectImage S).obj G)) :
    IsZero ((zariskiDirectImage S).obj G) :=
  IsZero.of_iso (Functor.map_isZero (DerivedCategory.Plus.homologyFunctor _ 0) h)
    ((higherZariskiDirectImageZeroIso S).symm.app G)

/-- **`Ru_{X/S, *}` kills a bounded below complex of abelian sheaves all of whose terms it
kills.**  This is Leray's acyclicity lemma, [Stacks, Tag 015E]: each term is `u_{X/S, *}`-acyclic
by `rightAcyclic_zariskiDirectImage_of_isZero`, so the canonical map
`u_{X/S, *}K ⟶ Ru_{X/S, *}K` is an isomorphism; and `u_{X/S, *}K` is the zero complex, each of
its terms being zero by `isZero_zariskiDirectImage_of_isZero`.

It is this lemma, and not a spectral sequence, that carries the vanishing clause of
[Stacks, Tag 07LM] to its leading assertion: the terms of the de Rham complex in positive degrees
are the `F ⊗ Ω^i_{X/S}` with `i > 0`, and the vanishing clause says exactly that `Ru_{X/S, *}`
kills them. -/
theorem isZero_derivedZariskiDirectImageFunctor_obj_of_termwise
    (K : CochainComplex.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}))
    (hzero : ∀ n : ℤ, IsZero ((derivedZariskiDirectImage S).obj (K.obj.X n))) :
    IsZero ((derivedZariskiDirectImageFunctor S).obj
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj K))) := by
  have hunit : IsIso ((zariskiDirectImage S).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient _).obj K)) :=
    Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic (zariskiDirectImage S) K.obj
      K.property fun n ↦ rightAcyclic_zariskiDirectImage_of_isZero S (hzero n)
  have hmap : IsZero (((zariskiDirectImage S).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj) := by
    rw [IsZero.iff_id_eq_zero]
    exact HomologicalComplex.hom_ext _ _ fun n ↦
      (isZero_zariskiDirectImage_of_isZero S (hzero n)).eq_of_src _ _
  have hplus : IsZero ((zariskiDirectImage S).mapCochainComplexPlus.obj K) := by
    rw [IsZero.iff_id_eq_zero]
    exact (CochainComplex.Plus.ι _).map_injective <| (IsZero.iff_id_eq_zero _).1
      (IsZero.of_iso hmap ((Functor.mapCochainComplexPlusCompι (zariskiDirectImage S)).app K))
  have : (HomotopyCategory.Plus.quotient
      (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  exact IsZero.of_iso
    (Functor.map_isZero DerivedCategory.Plus.Qh
      (Functor.map_isZero (HomotopyCategory.Plus.quotient _) hplus))
    (asIso ((zariskiDirectImage S).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient _).obj K))).symm

/-! ### The leading assertion of [Stacks, Tag 07LM] -/

section LeadingAssertion

open Pretriangulated

/-- **Sheafification of abelian presheaves on `Cris(X/S)`**, at the coefficient universe `u + 1`
in which the cohomology of the site lives: lift the sections along `AddCommGrpCat.uliftFunctor`
and sheafify.  On a single presheaf of modules this is the construction behind
`tensorDifferentialFormsSheaf`; what is wanted here is that it is a *functor*, and an additive
one, so that it carries the de Rham complex of abelian presheaves to a complex of abelian
sheaves. -/
def crysAbelianSheafification :
    ((CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
    presheafToSheaf (smallTopology S) AddCommGrpCat.{u + 1}

/-- The sheafification functor `crysAbelianSheafification S` is additive. -/
instance crysAbelianSheafification_additive : (crysAbelianSheafification S).Additive := by
  dsimp only [crysAbelianSheafification]
  infer_instance

/-- **From an `ℕ`-indexed complex of abelian presheaves to a bounded below complex of abelian
sheaves**: sheafify termwise and extend by zero into the negative degrees.  Both steps are
additive, so this is the identity on the mathematics; it is what puts the de Rham complex in the
category `Ru_{X/S, *}` is defined on. -/
def crysDeRhamSheafComplexFunctor :
    CochainComplex ((CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ ⥤
      CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ :=
  (crysAbelianSheafification S).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor _

/-- **The de Rham complex of `𝒪_{X/S}` as a bounded below complex of abelian sheaves**, the
image of `crysDeRhamCochainComplex` under `crysDeRhamSheafComplexFunctor`. -/
def crysDeRhamSheafComplex :
    CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ :=
  (crysDeRhamSheafComplexFunctor S).obj (crysDeRhamCochainComplex S)

/-- **`𝒪_{X/S}` placed in degree zero**, as a bounded below complex of abelian sheaves: the
target of the truncation map of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}`. -/
def crysDeRhamStructureSheafComplex :
    CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ :=
  (crysDeRhamSheafComplexFunctor S).obj
    ((CochainComplex.single₀ ((CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
      (modulePresheaf S
        (PresheafOfModules.unit (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))))

/-- **The truncation map of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}`, on abelian sheaves**: the image
of `crysDeRhamTruncation` under `crysDeRhamSheafComplexFunctor`.  It is the same map; only the
category it is read in has changed. -/
def crysDeRhamSheafTruncation :
    crysDeRhamSheafComplex S ⟶ crysDeRhamStructureSheafComplex S :=
  (crysDeRhamSheafComplexFunctor S).map (crysDeRhamTruncation S)

/-- The de Rham complex of abelian sheaves vanishes in negative degrees. -/
instance crysDeRhamSheafComplex_isStrictlyGE : (crysDeRhamSheafComplex S).IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    ((((crysAbelianSheafification S).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (crysDeRhamCochainComplex S)).extend
        ComplexShape.embeddingUpNat) 0)

/-- The complex `𝒪_{X/S}[0]` of abelian sheaves vanishes in negative degrees. -/
instance crysDeRhamStructureSheafComplex_isStrictlyGE :
    (crysDeRhamStructureSheafComplex S).IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    ((((crysAbelianSheafification S).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ ((CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
        (modulePresheaf S
          (PresheafOfModules.unit (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))))).extend
      ComplexShape.embeddingUpNat) 0)

/-- In degree `i ≥ 0` the de Rham complex of abelian sheaves has the sheaf generated by
`Ω^i_{X/S}` as its term. -/
def crysDeRhamSheafComplexXIso (i : ℕ) :
    (crysDeRhamSheafComplex S).X (i : ℤ) ≅
      (crysAbelianSheafification S).obj (modulePresheaf S (crysDifferentialForms S i)) :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := i) (by simp)

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] in
/-- Outside degree zero the complex `𝒪_{X/S}[0]` of abelian sheaves vanishes. -/
theorem isZero_crysDeRhamStructureSheafComplex_X (n : ℤ) (hn : n ≠ 0) :
    IsZero ((crysDeRhamStructureSheafComplex S).X n) := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat n
      (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega)
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h.le
    refine IsZero.of_iso ?_
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := k) (by simp))
    exact Functor.map_isZero (crysAbelianSheafification S)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 _ k (by omega))

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] in
/-- In degree zero the truncation map of abelian sheaves is an isomorphism: it is the
identification `Ω^0_{X/S} = 𝒪_{X/S}`, sheafified. -/
theorem isIso_crysDeRhamSheafTruncation_f_zero :
    IsIso ((crysDeRhamSheafTruncation S).f 0) := by
  have : IsIso ((crysDeRhamTruncation S).f 0) := by
    rw [crysDeRhamTruncation_f_zero]
    exact inferInstanceAs (IsIso ((PresheafOfModules.toPresheaf
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)).mapIso (crysFormsZeroIso S)).inv)
  rw [show (crysDeRhamSheafTruncation S).f 0 = _ from
    HomologicalComplex.extendMap_f
      (((crysAbelianSheafification S).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (crysDeRhamTruncation S)) ComplexShape.embeddingUpNat (i := 0) (by simp),
    Functor.mapHomologicalComplex_map_f]
  exact IsIso.comp_isIso' (Iso.isIso_hom _)
    (IsIso.comp_isIso' (Functor.map_isIso _ _) (Iso.isIso_inv _))

/-- **The brutal truncation `σ^{≥1}` of the de Rham complex of abelian sheaves**: the complex
`F ⊗ Ω¹_{X/S} → F ⊗ Ω²_{X/S} → ⋯` at `F = 𝒪_{X/S}`, placed in degrees `≥ 1`.  It is the third
vertex of the triangle of the truncation map, and the vanishing clause of [Stacks, Tag 07LM] is
exactly the statement that `Ru_{X/S, *}` kills each of its terms. -/
def crysDeRhamSheafTruncGE :
    CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ :=
  (crysDeRhamSheafComplex S).stupidTrunc (ComplexShape.embeddingUpIntGE 1)

/-- The brutal truncation `σ^{≥1}` of the de Rham complex vanishes in degrees `< 1`. -/
instance crysDeRhamSheafTruncGE_isStrictlyGE : (crysDeRhamSheafTruncGE S).IsStrictlyGE 1 :=
  inferInstanceAs (((crysDeRhamSheafComplex S).stupidTrunc
    (ComplexShape.embeddingUpIntGE 1)).IsStrictlySupported (ComplexShape.embeddingUpIntGE 1))

/-- **The short complex `0 ⟶ σ^{≥1}K ⟶ K ⟶ K⁰[0] ⟶ 0`** of the de Rham complex of abelian
sheaves, whose second map is the truncation map of [Stacks, Tag 07LM].  It is degreewise split,
`crysDeRhamSplitting`. -/
def crysDeRhamShortComplex :
    ShortComplex (CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ) :=
  ShortComplex.mk
    (HomologicalComplex.ιStupidTrunc (crysDeRhamSheafComplex S)
      (ComplexShape.embeddingUpIntGE 1))
    (crysDeRhamSheafTruncation S) (by
      refine HomologicalComplex.hom_ext _ _ fun n => ?_
      rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
      rcases eq_or_ne n 0 with rfl | hn
      · exact (CochainComplex.isZero_of_isStrictlyGE (crysDeRhamSheafTruncGE S) 1 0
          (by omega)).eq_of_src _ _
      · exact (isZero_crysDeRhamStructureSheafComplex_X S n hn).eq_of_tgt _ _)

/-- **The short complex of the truncation map is degreewise split.**  In degree zero its first
term vanishes and its second map is the identification `Ω^0_{X/S} = 𝒪_{X/S}`; in a degree `≥ 1`
its first map is the identity of `F ⊗ Ω^n_{X/S}` and its last term vanishes; in a negative degree
everything vanishes. -/
noncomputable def crysDeRhamSplitting (n : ℤ) :
    ((crysDeRhamShortComplex S).map
      (HomologicalComplex.eval _ _ n)).Splitting := by
  by_cases hn : n = 0
  · subst hn
    exact ShortComplex.Splitting.ofIsZeroOfIsIso _
      (CochainComplex.isZero_of_isStrictlyGE (crysDeRhamSheafTruncGE S) 1 0 (by omega))
      (isIso_crysDeRhamSheafTruncation_f_zero S)
  · refine ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_
      (isZero_crysDeRhamStructureSheafComplex_X S n hn)
    by_cases hn1 : (1 : ℤ) ≤ n
    · exact HomologicalComplex.isIso_ιStupidTrunc_f _ _ (i := (n - 1).toNat)
        (by change (1 : ℤ) + ((n - 1).toNat : ℤ) = n; omega)
    · exact IsZero.isIso
        (CochainComplex.isZero_of_isStrictlyGE (crysDeRhamSheafTruncGE S) 1 n (by omega))
        (CochainComplex.isZero_of_isStrictlyGE (crysDeRhamSheafComplex S) 0 n (by omega)) _

/-! #### The distinguished triangle of the truncation map -/

/-- `σ^{≥1}` of the de Rham complex of abelian sheaves, read as a bounded below complex. -/
def crysDeRhamPlusTruncGE :
    CochainComplex.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  ⟨crysDeRhamSheafTruncGE S, ⟨1, inferInstance⟩⟩

/-- The de Rham complex of abelian sheaves, read as a bounded below complex. -/
def crysDeRhamPlusComplex :
    CochainComplex.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  ⟨crysDeRhamSheafComplex S, ⟨0, inferInstance⟩⟩

/-- `𝒪_{X/S}[0]`, read as a bounded below complex of abelian sheaves. -/
def crysDeRhamStructureSheafPlusComplex :
    CochainComplex.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  ⟨crysDeRhamStructureSheafComplex S, ⟨0, inferInstance⟩⟩

/-- **The truncation map of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}`, in `C⁺(Ab(Cris(X/S)))`.** -/
def crysDeRhamPlusTruncation :
    crysDeRhamPlusComplex S ⟶ crysDeRhamStructureSheafPlusComplex S :=
  ObjectProperty.homMk (crysDeRhamSheafTruncation S)

/-- The inclusion `σ^{≥1}K ⟶ K`, in `C⁺(Ab(Cris(X/S)))`. -/
def crysDeRhamPlusIota : crysDeRhamPlusTruncGE S ⟶ crysDeRhamPlusComplex S :=
  ObjectProperty.homMk (HomologicalComplex.ιStupidTrunc (crysDeRhamSheafComplex S)
    (ComplexShape.embeddingUpIntGE 1))

/-- **The triangle `σ^{≥1}K ⟶ K ⟶ K⁰[0] ⟶ (σ^{≥1}K)⟦1⟧` of `K⁺(Ab(Cris(X/S)))`** attached to
the degreewise split short exact sequence `crysDeRhamShortComplex`.  Its second map is the
truncation map of [Stacks, Tag 07LM]; its first vertex is the brutal truncation whose terms the
vanishing clause of the tag kills. -/
noncomputable def crysDeRhamTrianglePlus :
    Triangle (HomotopyCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) :=
  Triangle.mk
    ((HomotopyCategory.Plus.quotient _).map (crysDeRhamPlusIota S))
    ((HomotopyCategory.Plus.quotient _).map (crysDeRhamPlusTruncation S))
    (ObjectProperty.homMk
      ((CochainComplex.trianglehOfDegreewiseSplit (crysDeRhamShortComplex S)
          (crysDeRhamSplitting S)).mor₃ ≫
        ((HomotopyCategory.Plus.ι _).commShiftIso (1 : ℤ)).inv.app
          ((HomotopyCategory.Plus.quotient _).obj (crysDeRhamPlusTruncGE S))))

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] in
/-- **The triangle of the truncation map is distinguished in `K⁺`.**  It is distinguished in
`K(Ab(Cris(X/S)))` by [Stacks, Tag 0118] — a degreewise split short exact sequence of complexes
gives a distinguished triangle of the homotopy category — and the inclusion `K⁺ ⥤ K` is fully
faithful and triangulated. -/
theorem crysDeRhamTrianglePlus_distinguished :
    crysDeRhamTrianglePlus S ∈
      distTriang (HomotopyCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) := by
  rw [← Functor.map_distinguished_iff (HomotopyCategory.Plus.ι _)]
  refine isomorphic_distinguished _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished (crysDeRhamShortComplex S)
      (crysDeRhamSplitting S)) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  iterate 2 exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have h : (CategoryTheory.shiftFunctor
        (HomotopyCategory (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
          (ComplexShape.up ℤ)) (1 : ℤ)).map
          (Iso.refl ((HomotopyCategory.Plus.ι _).mapTriangle.obj
            (crysDeRhamTrianglePlus S)).obj₁).hom = 𝟙 _ := by simp
    have h₂ : ((CochainComplex.trianglehOfDegreewiseSplit (crysDeRhamShortComplex S)
          (crysDeRhamSplitting S)).mor₃ ≫
        ((HomotopyCategory.Plus.ι _).commShiftIso (1 : ℤ)).inv.app
          ((HomotopyCategory.Plus.quotient _).obj (crysDeRhamPlusTruncGE S))) ≫
        ((HomotopyCategory.Plus.ι _).commShiftIso (1 : ℤ)).hom.app
          ((HomotopyCategory.Plus.quotient _).obj (crysDeRhamPlusTruncGE S)) =
        (CochainComplex.trianglehOfDegreewiseSplit (crysDeRhamShortComplex S)
          (crysDeRhamSplitting S)).mor₃ :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun g => (CochainComplex.trianglehOfDegreewiseSplit
            (crysDeRhamShortComplex S) (crysDeRhamSplitting S)).mor₃ ≫ g)
          (Iso.inv_hom_id_app ((HomotopyCategory.Plus.ι _).commShiftIso (1 : ℤ))
            ((HomotopyCategory.Plus.quotient _).obj
              (crysDeRhamPlusTruncGE S)))).trans (Category.comp_id _))
    exact (congrArg (fun g => ((HomotopyCategory.Plus.ι _).mapTriangle.obj
        (crysDeRhamTrianglePlus S)).mor₃ ≫ g) h).trans
      ((Category.comp_id _).trans (h₂.trans (Category.id_comp _).symm))

/-! #### `Ru_{X/S, *}` is an exact functor of triangulated categories -/

/-- `Ru_{X/S, *}` commutes with the shift, by the universal property of the right derived
functor.  This is `Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus` read at
`u_{X/S, *}`; it is named rather than anonymous so that nothing else can collide with it. -/
local instance crysCommShiftDerivedZariskiDirectImageFunctor :
    (derivedZariskiDirectImageFunctor S).CommShift ℤ :=
  Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus (zariskiDirectImage S)

/-- **`Ru_{X/S, *} : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(X_Zar))` is exact**, [Stacks, Tag 0159]: the
bounded below right derived functor of an additive functor is triangulated.  This is what lets
the triangle of the truncation map be pushed through it. -/
local instance crysIsTriangulatedDerivedZariskiDirectImageFunctor :
    (derivedZariskiDirectImageFunctor S).IsTriangulated :=
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus (zariskiDirectImage S)

/-- `Ru_{X/S, *}` on a single abelian sheaf is additive, being the composite of the single
functor with the triangulated functor above; in particular it kills a zero sheaf. -/
local instance crysAdditiveDerivedZariskiDirectImage :
    (derivedZariskiDirectImage S).Additive :=
  inferInstanceAs (Functor.Additive
    (DerivedCategory.Plus.singleFunctor
      (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0 ⋙
        derivedZariskiDirectImageFunctor S))

/-! #### The leading assertion -/

/-- **The vanishing clause of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}`**: for every `i > 0`,

`Ru_{X/S, *}(𝒪_{X/S} ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = Ru_{X/S, *}(Ω^i_{X/S}) = 0`,

the sheaf meant being the one `Ω^i_{X/S}` generates on `Cris(X/S)`.  It is the clause
`Vanishing07LM` read at `F = 𝒪_{X/S}`, where `F ⊗_{𝒪_{X/S}} Ω^i_{X/S} = Ω^i_{X/S}` by
`tensorDifferentialFormsUnitIso`.  It is written out separately because the leading assertion
below is stated against it, but it **does** follow from `Vanishing07LM` by specialisation:
`...SmallSite.vanishing07LMForms_of_vanishing07LM` of
`SmallSite/Vanishing07LMAffineReduction.lean`.

Like `Vanishing07LM` it is a proposition here and not a theorem: nothing in this file proves it.
`...SmallSite.vanishing07LMForms` of `SmallSite/Vanishing07LMProof.lean` proves it, through
`...SmallSite.transport07LMForms` of that file and the two specialisation steps of
`SmallSite/Vanishing07LMAffineReduction.lean`.  Over an affine base its content is
[Stacks, Tag 07LF], which **is** proved, as `...SmallSite.vanishing07LF`, and the local-to-global
passage to the derived direct image is proved as well.

Because this is a clause of [Stacks, Tag 07LM] itself, the theorem below that takes it as a
hypothesis carries no `@[stacks 07LM]` attribute, even though the clause is
available: the theorem below is the implication, and it is read with the hypothesis supplied in
`...SmallSite.isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamPlusTruncation` of
`SmallSite/Vanishing07LMProof.lean`. -/
def Vanishing07LMForms : Prop :=
  ∀ i : ℕ, 0 < i → IsZero ((derivedZariskiDirectImage S).obj
    ((crysAbelianSheafification S).obj (modulePresheaf S (crysDifferentialForms S i))))

/-- Under the vanishing clause, `Ru_{X/S, *}` kills every term of `σ^{≥1}` of the de Rham
complex: in a degree `≥ 1` the term is the sheaf generated by `Ω^i_{X/S}`, which the clause
kills, and in every other degree it is zero. -/
theorem isZero_derivedZariskiDirectImage_crysDeRhamSheafTruncGE_X
    (hV : Vanishing07LMForms S) (n : ℤ) :
    IsZero ((derivedZariskiDirectImage S).obj ((crysDeRhamSheafTruncGE S).X n)) := by
  by_cases hn : (1 : ℤ) ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
    refine IsZero.of_iso (hV k (by omega)) ((derivedZariskiDirectImage S).mapIso ?_)
    exact HomologicalComplex.stupidTruncXIso (crysDeRhamSheafComplex S)
        (ComplexShape.embeddingUpIntGE 1) (i := k - 1)
        (by change (1 : ℤ) + ((k - 1 : ℕ) : ℤ) = (k : ℤ); omega) ≪≫
      crysDeRhamSheafComplexXIso S k
  · exact Functor.map_isZero _ (CochainComplex.isZero_of_isStrictlyGE
      (crysDeRhamSheafTruncGE S) 1 n (by omega))

/-- **Stacks Project, Tag 07LM, the leading assertion, at `F = 𝒪_{X/S}`.**  The truncation map

`(𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯) ⟶ 𝒪_{X/S}[0]`

of `crysDeRhamTruncation` becomes an isomorphism in `D⁺(Ab(X_Zar))` after `Ru_{X/S, *}` — that
is, it becomes a quasi-isomorphism — as soon as the vanishing clause of the same tag holds.

The proof is the one the source gives.  The truncation map sits in the degreewise split short
exact sequence `0 ⟶ σ^{≥1}K ⟶ K ⟶ K⁰[0] ⟶ 0` (`crysDeRhamShortComplex`,
`crysDeRhamSplitting`), hence in a distinguished triangle of `K⁺(Ab(Cris(X/S)))`
(`crysDeRhamTrianglePlus_distinguished`), which `Qh` and the exact functor `Ru_{X/S, *}` carry
to a distinguished triangle of `D⁺(Ab(X_Zar))`.  Its first vertex is `Ru_{X/S, *}(σ^{≥1}K)`,
which vanishes: the terms of `σ^{≥1}K` are the `Ω^i_{X/S}` with `i > 0`, the vanishing clause
kills each of them, and Leray's acyclicity lemma
`isZero_derivedZariskiDirectImageFunctor_obj_of_termwise` carries that to the complex.  A
distinguished triangle whose first vertex is zero has an invertible second map,
`Triangle.isZero₁_iff_isIso₂`.

The hypothesis `hV` is the vanishing clause at `F = 𝒪_{X/S}`; it is a theorem,
`...SmallSite.vanishing07LMForms`, and the statement with it supplied is
`...SmallSite.isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamPlusTruncation` of
`SmallSite/Vanishing07LMProof.lean`.  The proposition for a general crystal in quasi-coherent
modules is `...SmallSite.stacks07LM` of `SmallSite/Proposition07LM.lean`. -/
theorem isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamTruncation
    (hV : Vanishing07LMForms S) :
    IsIso ((derivedZariskiDirectImageFunctor S).map
      (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient _).map (crysDeRhamPlusTruncation S)))) := by
  have hT := (derivedZariskiDirectImageFunctor S).map_distinguished _
    (DerivedCategory.Plus.Qh.map_distinguished _ (crysDeRhamTrianglePlus_distinguished S))
  exact (Triangle.isZero₁_iff_isIso₂ _ hT).1
    (isZero_derivedZariskiDirectImageFunctor_obj_of_termwise S (crysDeRhamPlusTruncGE S)
      (isZero_derivedZariskiDirectImage_crysDeRhamSheafTruncGE_X S hV))

end LeadingAssertion

end Vanishing

end SmallSite

/-! ### The presheaf `Ω^i_{X/S}` satisfies the hypotheses of [Stacks, Tag 07JN] -/

/-- **Conditions (1) and (2) of [Stacks, Tag 07JN] for `Ω^1_{X/S} = Ω_{X/S}`, on the big
crystalline category.**

The first conjunct is condition (1), local quasi-coherence: the restriction `(Ω_{X/S})_T` is a
quasi-coherent module over the structure sheaf of the ambient scheme of every object.  The second
is condition (2): the comparison morphism `c_f : f^*(Ω_{X/S})_{T'} ⟶ (Ω_{X/S})_T` is surjective
for every morphism whose map on ambient schemes is a closed immersion.  The two are the two
clauses of [Stacks, Tag 07KM], proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/DifferentialsLocallyQuasicoherent.lean` and
`StacksFrontier/AlgebraicGeometry/Crystalline/DifferentialsComparison.lean`; what this statement adds
is the conjunction [Stacks, Tag 07LN] asserts, that the two together are what the vanishing needs.

**No tag attribute is placed**: the claim [Stacks, Tag 07LN] makes is about the sheaf
`Ω^i_{X/S}` for *every* `i`, and that is `...SmallSite.crysFormsSheaf_vanishing` of
`SmallSite/Remark07LN.lean`.  This statement is the degree-one case of
`crysDifferentialForms_satisfiesVanishingHypotheses` read on the big crystalline category, and it
is kept because the two clauses of [Stacks, Tag 07KM] are tagged there. -/
theorem crysDifferentials_satisfiesVanishingHypotheses :
    (∀ A : Thickening S, (crysDifferentialsRestrictionSheaf S A).IsQuasicoherentOnSite) ∧
      ∀ {A B : Thickening S} (g : A ⟶ B), IsClosedImmersion g.targetHom.hom →
        Presheaf.IsLocallySurjective
          (Opens.grothendieckTopology A.thickening.target.scheme)
          ((PresheafOfModules.toPresheaf (Thickening.ringRestriction A)).map
            (Thickening.moduleComparison (crysDifferentials S) g)) :=
  ⟨fun A ↦ crysDifferentials_isLocallyQuasiCoherent S A,
    fun g _hg ↦ isLocallySurjective_moduleComparison S g⟩

/-- **Conditions (1) and (2) of [Stacks, Tag 07JN] for the presheaf `Ω^i_{X/S}`, in every
degree `i`.**  For every `i`, the presheaf `Ω^i_{X/S} = ⋀^i Ω_{X/S}` of crystalline `i`-forms
satisfies both conditions, read on its restrictions to the ambient schemes.

The first conjunct is condition (1), local quasi-coherence: the sheaf associated with the
restriction `(Ω^i_{X/S})_T` is a quasi-coherent module over the structure sheaf of the ambient
scheme of every object.  The second is condition (2) in the form [Stacks, Tag 07JN] itself
consumes it, `...SmallSite.CohomologyRestriction.IsSurjectiveComparison`: the comparison morphism
`c_f : f^*(Ω^i_{X/S})_{T'} ⟶ (Ω^i_{X/S})_T` is locally surjective for every morphism of
`Cris(X/S)` whose map on ambient schemes is a closed immersion.  Both are [Stacks, Tag 07KM] for
the `i`-th exterior power, and both hold with no hypothesis whatever —
`...crysDifferentialForms_isLocallyQuasiCoherent` and
`...SmallSite.CohomologyRestriction.isSurjectiveComparison_crysDifferentialForms`.

The degree-one statement on the big crystalline category is
`crysDifferentials_satisfiesVanishingHypotheses`.

**No tag attribute is placed**: the remark [Stacks, Tag 07LN] speaks of the *sheaf* `Ω^i_{X/S}`,
and its claim for that sheaf — conditions (1) and (2) and the vanishing
`Ru_{X/S, *}(Ω^i_{X/S} ⊗ Ω^k_{X/S}) = 0` for `k > 0` — is `...SmallSite.crysFormsSheaf_vanishing`
of `SmallSite/Remark07LN.lean`, which carries the tag.  The sheaf is built from this presheaf in
`SmallSite/DifferentialFormsSheaf.lean`, and its two conditions are derived from the two proved
here. -/
theorem crysDifferentialForms_satisfiesVanishingHypotheses (i : ℕ) :
    (∀ A : Thickening S, (crysDifferentialFormsRestrictionSheaf S A i).IsQuasicoherentOnSite) ∧
      SmallSite.CohomologyRestriction.IsSurjectiveComparison
        (SmallSite.crysDifferentialForms S i) :=
  ⟨fun A ↦ crysDifferentialForms_isLocallyQuasiCoherent S A i,
    SmallSite.CohomologyRestriction.isSurjectiveComparison_crysDifferentialForms i⟩

end Crystalline.GlobalCrystallineSituation

end

end
