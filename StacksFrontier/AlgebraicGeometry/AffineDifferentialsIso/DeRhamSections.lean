module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.SpecComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExteriorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The differential forms of a morphism of affine schemes, in the coordinate rings

Let `φ : R ⟶ A` be a morphism of commutative rings and let `Spec φ : Spec A ⟶ Spec R` be the
induced morphism of affine schemes. The sheaf of relative differentials of `Spec φ` is the
quasi-coherent sheaf attached to the Kähler differentials `Ω[A⁄R]`; this file carries that
identification up the exterior powers, so that for every `p` the sheaf `Ω^p_{Spec A/Spec R}` of
relative differential `p`-forms is the quasi-coherent sheaf attached to `⋀^p_A Ω[A⁄R]`, and its
global sections are `⋀^p_A Ω[A⁄R]` itself.

In degree one the comparison is pinned down by the universal derivations, and the first
differential of the relative de Rham complex of `Spec φ`, read on global sections, is the
universal differential `d : A → Ω[A⁄R]`.

## Main definitions

* `differentialFormsTildeIso` identifies `Ω^p_{Spec A/Spec R}` with the quasi-coherent sheaf
  attached to the `p`-th exterior power of the Kähler differentials of `φ`.
* `differentialFormsSectionsIso` is the resulting comparison of `A`-modules
  `⋀^p_A Ω[A⁄R] ≅ Γ(Spec A, Ω^p_{Spec A/Spec R})`.
* `zeroFormsSectionsIso` is its degree-zero form, with the exterior power spelled as `A`.
* `oneFormsSectionsIso` is the degree-one comparison `Ω[A⁄R] ≅ Γ(Spec A, Ω^1_{Spec A/Spec R})`
  obtained from the degree-one identification of the exterior algebra.

## Main results

* `oneFormsSectionsIso_d`: the degree-one comparison carries the universal differential of
  `a : A` to the degree-one form attached to the universal relative differential of the global
  section of `𝒪_{Spec A}` corresponding to `a`.
* `existsUnique_oneFormsSectionsIso`: that compatibility determines the degree-one comparison
  uniquely.
* `deRhamComplex_d_zero_one_apply`: **the first differential of the relative de Rham complex of
  `Spec φ`, read on global sections, is the universal derivation.** On the degree-zero form
  attached to a global section `b` of `𝒪_{Spec A}` it is the universal differential of the
  element of `A` corresponding to `b`.

## Implementation notes

The comparison in degree `p` is a composite of three identifications, none of which is an
exterior-power statement about `Spec φ` itself.

* The sheaf of relative differentials of `Spec φ` is the quasi-coherent sheaf of `Ω[A⁄R]`; that
  is `Stacks.AlgebraicGeometry.AffineDifferentialsIso.tildeKaehlerIso`, the sheaf form of
  [Stacks Project, Tag 01UT] in the coordinate rings.
* Exterior powers commute with the associated-sheaf functor on an affine scheme:
  `AlgebraicGeometry.tildeExteriorPowerIso`, which rests on exterior powers commuting with base
  change. This is what makes *every* degree available; the degree-one identification of an
  exterior algebra would only give `p = 1`.
* The exterior power in a fixed degree is a functor in the module argument
  (`AlgebraicGeometry.Scheme.Modules.exteriorPowerFunctor`), so the first identification can be
  pushed through it.

Global sections are then the unit `AlgebraicGeometry.tilde.toTildeΓNatIso` of the adjunction
between the associated-sheaf functor and global sections, which is an isomorphism; this is the
same spelling of the sections of a quasi-coherent sheaf on `Spec A`
(`AlgebraicGeometry.moduleSpecΓFunctor`) that `sectionsIso` is stated in.

The degree-one comparison `oneFormsSectionsIso` is *not* `differentialFormsSectionsIso` at
`p = 1`: it is built from `sectionsIso` and the degree-one identification
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorGeneratorIso` of the exterior algebra,
which is why it can be compared with the universal derivations, and it is the one the de Rham
differential is read against. Identifying the two needs the compatibility recorded as missing
below.

The terms of the relative de Rham complex are sheaves of `(Spec φ)^{-1}𝒪_{Spec R}`-modules, not
of `𝒪_{Spec A}`-modules, because the de Rham differential is only linear over the base; the two
have the same local sections, so `deRhamComplex_d_zero_one_apply` reads the differential on the
sections of `Ω^p_{Spec A/Spec R}` directly. For the same reason the global section `b` of
`𝒪_{Spec A}` is written in the spelling `(Spec A).sheaf.obj.obj (op ⊤)` in which the
exterior-algebra action on degree-zero forms is available.

## The `@[stacks 0FLW]` attributes

[Stacks Project, Tag 0FLW] asserts, for a morphism of affine schemes `Spec φ`, that
`RΓ(Spec A, Ω^•_{Spec A/Spec R})` is the algebraic de Rham complex `Ω^•_{A/R}` in `D(R)`, and
that de Rham cohomology is the cohomology of `Ω^•_{A/R}`. **Neither assertion is proved here**;
both are proved in `StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamDerived`, by
`derivedDeRhamSectionsIso` and `deRhamCohomologyIsoInt`. What is proved here is the comparison
the tag's proof starts from, and the attribute is placed on exactly the two pieces of it that
are complete and unconditional.

* `differentialFormsSectionsIso` carries the **degreewise** comparison: the terms of the two
  complexes agree, as `A`-modules, in every degree. It says nothing about any differential, and
  its clause reads `degreewise only`.
* `deRhamComplex_d_zero_one_apply` carries the **degree-zero differential square**, which is the
  only square of the two complexes that is matched; it is read against `oneFormsSectionsIso`,
  and its clause says `only` for the same reason.

No declaration here claims the cochain complex, the object of `D(R)`, or the cohomology — the
two clauses are deliberately partial, and what follows is what separates them from the tag.

**The three steps from here to the tag**, each proved elsewhere.

* *The differentials in positive degree.* The de Rham rule of
  `AlgebraicGeometry.SheafOfModules.DeRhamDifferential.generator` is transported across
  `differentialFormsSectionsIso` in
  `StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamWedgeSections`, which is what
  identifies `Γ(Spec A, Ω^•_{Spec A/Spec R})` with `KaehlerDifferential.deRhamComplex R A`
  above degree zero. Its input is that `AlgebraicGeometry.tildeExteriorPowerIso` carries the
  global section `m₁ ∧ ⋯ ∧ m_p` of the associated sheaf of `⋀^p_R M` to the ordered product of
  the degree-one generators of the `m_i`, which is
  `AlgebraicGeometry.tildeExteriorPowerIso_hom_ιMulti` in
  `StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.TildeExteriorProduct`. The same
  compatibility is what identifies `oneFormsSectionsIso` with `differentialFormsSectionsIso` at
  `p = 1`, which is why `deRhamComplex_d_zero_one_apply` is stated against
  `oneFormsSectionsIso` and not against the degreewise comparison, and why the two attributes
  here are two clauses rather than one.
* *Global sections of the complex, as a complex of `R`-modules.* This is
  `Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamSectionsComplexIso` in
  `StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamComplexComparison`, the scalars
  being transported to the base ring `R` along
  `AlgebraicGeometry.Scheme.Hom.affineBaseRingMap` of
  `StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamComplexSections`.
* *The derived statement.* Even given a complex of `R`-modules, `Γ` is not `RΓ`. The passage
  needs the affine acyclicity of a quasi-coherent sheaf together with Leray's acyclicity lemma,
  which are the inputs the tag's own proof cites; both are assembled in
  `StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamDerived`, whose
  `derivedDeRhamSectionsIso` and `deRhamCohomologyIsoInt` carry the tag's two assertions.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.AffineDifferentialsIso

section DeRhamSections

variable {R A : CommRingCat.{u}} (φ : R ⟶ A)

/-! ### The sheaves of differential forms -/

/-- **The sheaf `Ω^p_{Spec A/Spec R}` of relative differential `p`-forms of a morphism of affine
schemes is the quasi-coherent sheaf attached to `⋀^p_A Ω[A⁄R]`.** The sheaf of relative
differentials is the quasi-coherent sheaf of `Ω[A⁄R]`, exterior powers commute with the
associated-sheaf functor on an affine scheme, and the exterior power in a fixed degree is a
functor in the module argument. -/
@[ega "IV 16.6.1"]
noncomputable def differentialFormsTildeIso (p : ℕ) :
    (tilde.functor A).obj
        (ModuleCat.of ↥A ↥(⋀[↥A]^p ↥(CommRingCat.KaehlerDifferential φ))) ≅
      Scheme.Hom.relativeDifferentialForms (Spec.map φ) (p : ℤ) :=
  tildeExteriorPowerIso A (CommRingCat.KaehlerDifferential φ) p ≪≫
    (Scheme.Modules.exteriorPowerFunctor (Spec A) (p : ℤ)).mapIso (tildeKaehlerIso φ)

/-! ### The global differential forms -/

/-- **The global relative differential `p`-forms of `Spec φ : Spec A ⟶ Spec R` are
`⋀^p_A Ω[A⁄R]`, as `A`-modules.** The sheaf of relative differential `p`-forms is the
quasi-coherent sheaf attached to that module, and the unit of the adjunction between the
associated-sheaf functor and global sections recovers a module from its quasi-coherent sheaf.

This is the degreewise half of [Stacks Project, Tag 0FLW]: it matches the terms of the two
complexes the tag compares, in every degree, and no differential. -/
@[stacks 0FLW "degreewise only: `⋀^p_A Ω[A⁄R] ≅ Γ(Spec A, Ω^p)` for every `p`; no differential"]
noncomputable def differentialFormsSectionsIso (p : ℕ) :
    ModuleCat.of ↥A ↥(⋀[↥A]^p ↥(CommRingCat.KaehlerDifferential φ)) ≅
      moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentialForms (Spec.map φ) (p : ℤ)) :=
  tilde.toTildeΓNatIso.app
      (ModuleCat.of ↥A ↥(⋀[↥A]^p ↥(CommRingCat.KaehlerDifferential φ))) ≪≫
    moduleSpecΓFunctor.mapIso (differentialFormsTildeIso φ p)

/-- The comparison of global differential forms is the comparison of sheaves, read on global
sections and composed with the unit of the adjunction. -/
theorem differentialFormsSectionsIso_hom (p : ℕ) :
    (differentialFormsSectionsIso φ p).hom =
      tilde.toTildeΓNatIso.hom.app
          (ModuleCat.of ↥A ↥(⋀[↥A]^p ↥(CommRingCat.KaehlerDifferential φ))) ≫
        moduleSpecΓFunctor.map (differentialFormsTildeIso φ p).hom :=
  rfl

/-- The degree-zero case, with the exterior power spelled as `A`: the global relative
differential `0`-forms of `Spec φ` are the coordinate ring `A`. -/
@[ega "IV 16.6.1" "Ω^0_{X/S} = O_X"]
noncomputable def zeroFormsSectionsIso :
    ModuleCat.of ↥A ↥A ≅
      moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentialForms (Spec.map φ) 0) :=
  (exteriorPower.zeroEquiv ↥A ↥(CommRingCat.KaehlerDifferential φ)).toModuleIso.symm ≪≫
    differentialFormsSectionsIso φ 0

/-! ### Degree one and the first differential -/

/-- **The global relative differential `1`-forms of `Spec φ` are the Kähler differentials
`Ω[A⁄R]`**, by [Stacks Project, Tag 01UT] in the coordinate rings together with the degree-one
identification of the exterior algebra. -/
noncomputable def oneFormsSectionsIso :
    CommRingCat.KaehlerDifferential φ ≅
      moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentialForms (Spec.map φ) 1) :=
  sectionsIso φ ≪≫
    moduleSpecΓFunctor.mapIso (Scheme.Hom.deRhamAlgebras (Spec.map φ)).exteriorGeneratorIso

/-- **The degree-one comparison is compatible with the universal derivations.** It carries the
universal differential of `a : A` to the degree-one form attached to the universal relative
differential of the global section of `𝒪_{Spec A}` corresponding to `a`. -/
theorem oneFormsSectionsIso_d (a : ↥A) :
    (oneFormsSectionsIso φ).hom.hom (CommRingCat.KaehlerDifferential.d a) =
      (Scheme.Hom.deRhamAlgebras (Spec.map φ)).exteriorGenerator.val.app (op ⊤)
        (((Scheme.Hom.universalRelativeDerivation (Spec.map φ)).app (op ⊤)).d
          ((Scheme.ΓSpecIso A).inv a)) := by
  refine Eq.trans ?_ (congrArg
    ((Scheme.Hom.deRhamAlgebras (Spec.map φ)).exteriorGenerator.val.app (op ⊤))
    (sectionsIso_d φ a))
  exact congrArg
    (fun g : Scheme.Hom.relativeDifferentials (Spec.map φ) ⟶
        (Scheme.Hom.deRhamAlgebras (Spec.map φ)).exterior.piece 1 =>
      g.val.app (op ⊤) ((sectionsIso φ).hom.hom (CommRingCat.KaehlerDifferential.d a)))
    (Scheme.Hom.deRhamAlgebras (Spec.map φ)).exteriorGeneratorIso_hom

/-- **Uniqueness of the degree-one comparison.** There is exactly one isomorphism of `A`-modules
from `Ω[A⁄R]` to the global relative differential `1`-forms of `Spec φ` compatible with the
universal derivations. -/
theorem existsUnique_oneFormsSectionsIso :
    ∃! e : CommRingCat.KaehlerDifferential φ ≅
        moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentialForms (Spec.map φ) 1),
      ∀ a : ↥A, e.hom.hom (CommRingCat.KaehlerDifferential.d a) =
        (Scheme.Hom.deRhamAlgebras (Spec.map φ)).exteriorGenerator.val.app (op ⊤)
          (((Scheme.Hom.universalRelativeDerivation (Spec.map φ)).app (op ⊤)).d
            ((Scheme.ΓSpecIso A).inv a)) := by
  refine ⟨oneFormsSectionsIso φ, oneFormsSectionsIso_d φ, fun e he => Iso.ext ?_⟩
  refine CommRingCat.KaehlerDifferential.ext fun a => ?_
  exact (he a).trans (oneFormsSectionsIso_d φ a).symm

/-- **The first differential of the relative de Rham complex of `Spec φ`, read on global
sections, is the universal derivation of `A` over `R`.** On the degree-zero form `b · 1` attached
to a global section `b` of `𝒪_{Spec A}` it is the universal differential of the element of `A`
corresponding to `b`, viewed in the global differential `1`-forms through the degree-one
comparison.

This is the one square of [Stacks Project, Tag 0FLW] that is matched; the differential in
positive degree is not. -/
@[stacks 0FLW "the degree-zero differential square only; no differential in positive degree"]
theorem deRhamComplex_d_zero_one_apply (b : ↥((Spec A).sheaf.obj.obj (op ⊤))) :
    (((Spec.map φ).deRhamComplex).d 0 1).val.app (op ⊤)
        (b • (Scheme.Hom.deRhamAlgebras (Spec.map φ)).exterior.one.eval (op ⊤)) =
      (oneFormsSectionsIso φ).hom.hom
        (CommRingCat.KaehlerDifferential.d ((Scheme.ΓSpecIso A).hom b)) := by
  refine (eq_of_heq (Scheme.Hom.deRhamComplex_degreeZero (Spec.map φ) (op ⊤) b)).trans ?_
  refine Eq.trans ?_ (oneFormsSectionsIso_d φ ((Scheme.ΓSpecIso A).hom b)).symm
  exact congrArg
    (fun c => (Scheme.Hom.deRhamAlgebras (Spec.map φ)).exteriorGenerator.val.app (op ⊤)
      (((Scheme.Hom.universalRelativeDerivation (Spec.map φ)).app (op ⊤)).d c))
    ((Scheme.ΓSpecIso A).hom_inv_id_apply b).symm

end DeRhamSections

end Stacks.AlgebraicGeometry.AffineDifferentialsIso

end
