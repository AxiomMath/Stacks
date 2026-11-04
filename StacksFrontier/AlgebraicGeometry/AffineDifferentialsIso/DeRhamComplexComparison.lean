module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamComplexSections
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamWedgeSections
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.RingTheory.DeRham.Complex

/-!
# The de Rham complex of a morphism of affine schemes, on global sections

Let `φ : R ⟶ A` be a morphism of commutative rings. The relative de Rham complex
`Ω^•_{Spec A/Spec R}` of `Spec φ` is a complex of sheaves of `(Spec φ)^{-1}𝒪_{Spec R}`-modules on
`Spec A`; reading it on global sections and restricting scalars to `R` along
`AlgebraicGeometry.Scheme.Hom.affineBaseRingMap` gives a cochain complex of `R`-modules. This
file identifies that complex with the algebraic de Rham complex
`Ω^•_{A/R} = (⋀^•_A Ω[A⁄R], d)` of `KaehlerDifferential.deRhamComplex`, **as a cochain
complex**: the degreewise comparison of
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.differentialFormsSectionsIso` commutes with the
de Rham differential in every degree.

## Main definitions

* `ringDeRhamComplex`: the algebraic de Rham complex `Ω^•_{A/R}` of a morphism of commutative
  rings, i.e. `KaehlerDifferential.deRhamComplex` with the algebra structure read off `φ`.
* `deRhamSectionsFunctor`: global sections of a sheaf of `(Spec φ)^{-1}𝒪_{Spec R}`-modules on
  `Spec A`, as an `R`-module.
* `deRhamSectionsComplex`: `Γ(Spec A, Ω^•_{Spec A/Spec R})`, a cochain complex of `R`-modules.
* `deRhamSectionsComplexTermIso`: the degreewise comparison of
  `differentialFormsSectionsIso`, read as an isomorphism of `R`-modules.

## Main results

* `affineBaseRingMap_comp_structureMap`: the base ring map `R ⟶ Γ(Spec A, (Spec φ)^{-1}𝒪)`
  followed by the structural map to `𝒪_{Spec A}` is `φ` followed by `R ≅ Γ(Spec R, 𝒪)`. This is
  the triangle identity of `(Spec φ)^{-1} ⊣ (Spec φ)_*` together with the naturality of
  `Scheme.ΓSpecIso`, and it is what makes the degreewise comparison `R`-linear.
* `deRhamSectionsComplexIso`: **`Γ(Spec A, Ω^•_{Spec A/Spec R}) ≅ Ω^•_{A/R}` as a cochain complex
  of `R`-modules** — the degreewise comparison commutes with the de Rham differential in every
  degree.
* `deRhamSectionsComplexIso_hom_f_apply`: its components are the degreewise comparison, so the
  complex-level isomorphism is the one already carrying the degreewise `@[stacks 0FLW]`
  attribute and not a second comparison.

## Implementation notes

The commuting square in degree `p` is checked on the `R`-module generators
`a₀ · (d a₁ ∧ ⋯ ∧ d a_p)` of `⋀^p_A Ω[A⁄R]`, which span it by
`Crystalline.span_range_smul_ιMulti_eq_top`. On such a generator the de Rham differential of the
sheaf complex is computed by
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamComplex_d_sectionsIso` and the de Rham
differential of the ring complex by `KaehlerDifferential.deRhamComplex_d_smul_ιMulti_D`; both
produce `d a₀ ∧ d a₁ ∧ ⋯ ∧ d a_p`, which is the square.

**Why the terms are `R`-modules and the comparison has to be transported.** The de Rham
differential is only linear over the base, so the sheaf complex is a complex of
`(Spec φ)^{-1}𝒪_{Spec R}`-modules and its global sections are modules over
`Γ(Spec A, (Spec φ)^{-1}𝒪_{Spec R})`, not over `A`. The degreewise comparison
`differentialFormsSectionsIso` is an isomorphism of `A`-modules, with the `A`-action on sections
of a quasi-coherent sheaf on `Spec A` taken through `Scheme.ΓSpecIso`; so making it `R`-linear
for the complex's own scalars is exactly the content of
`affineBaseRingMap_comp_structureMap`, and nothing else about the two scalar actions is used.

Global sections are taken with `SheafOfModules.evaluation` at the *concrete* ringed space
`AlgebraicGeometry.RingedSpace.inverseImage (Spec R) (Spec φ)`, whose structure sheaf is
`(Spec φ)^{-1}𝒪_{Spec R}`. Instantiating `SheafOfModules.evaluation` at an `Opens`-site with the
ring sheaf left to unification reports `stuck at solving universe constraint`, for the reason
recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamComplexSections`; naming the ringed
space pins every universe to `u` and the constraint does not arise.

`ringDeRhamComplex` is a spelling of `KaehlerDifferential.deRhamComplex` and not a second
notion: it only moves the `Algebra ↥R ↥A` instance induced by `φ` out of the statement, the same
way `CommRingCat.KaehlerDifferential` does for the module of differentials.

## References

* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 0FKF](https://stacks.math.columbia.edu/tag/0FKF)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineDifferentialsIso

section Comparison

variable {R A : CommRingCat.{u}} (φ : R ⟶ A)

/-! ### The two complexes -/

/-- **The algebraic de Rham complex `Ω^•_{A/R}` of a morphism of commutative rings**, as a
cochain complex of `R`-modules: `KaehlerDifferential.deRhamComplex` for the algebra structure
`φ` puts on `A`. -/
def ringDeRhamComplex : CochainComplex (ModuleCat.{u} ↥R) ℕ :=
  letI := φ.hom.toAlgebra
  KaehlerDifferential.deRhamComplex ↥R ↥A

/-- The degree-`p` term of the algebraic de Rham complex of `φ` carries `⋀^p_A Ω[A⁄R]`. -/
theorem ringDeRhamComplex_X_carrier (p : ℕ) :
    (↥((ringDeRhamComplex φ).X p) : Type u) =
      ↥(⋀[↥A]^p ↥(CommRingCat.KaehlerDifferential φ)) :=
  rfl

/-- **Global sections of a sheaf of `(Spec φ)^{-1}𝒪_{Spec R}`-modules on `Spec A`, as an
`R`-module**: sections over the whole space, with scalars restricted along the base ring map
`R ⟶ Γ(Spec A, (Spec φ)^{-1}𝒪_{Spec R})`. This is the functor in which the relative de Rham
complex of `Spec φ` becomes a complex of `R`-modules. -/
def deRhamSectionsFunctor :
    _root_.SheafOfModules.{u} (structureSheafRing
        (RingedSpace.inverseImage (Spec R).toRingedSpace (Spec.map φ).base)) ⥤
      ModuleCat.{u} ↥R :=
  _root_.SheafOfModules.evaluation (structureSheafRing
      (RingedSpace.inverseImage (Spec R).toRingedSpace (Spec.map φ).base)) (op ⊤) ⋙
    ModuleCat.restrictScalars (Scheme.Hom.affineBaseRingMap φ).hom

/-- Global sections form an additive functor: addition of sections of a sheaf of modules is
computed open by open, and restriction of scalars does not change it. -/
instance deRhamSectionsFunctor_additive : (deRhamSectionsFunctor φ).Additive where
  map_add := rfl

/-- **`Γ(Spec A, Ω^•_{Spec A/Spec R})`, as a cochain complex of `R`-modules**: the relative de
Rham complex of `Spec φ`, read on global sections degree by degree. -/
def deRhamSectionsComplex : CochainComplex (ModuleCat.{u} ↥R) ℕ :=
  ((deRhamSectionsFunctor φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((Spec.map φ).deRhamComplex)

/-- The degree-`p` term of the complex of global sections carries the global relative
differential `p`-forms of `Spec φ`. -/
theorem deRhamSectionsComplex_X_carrier (p : ℕ) :
    (↥((deRhamSectionsComplex φ).X p) : Type u) =
      ↥((Scheme.Hom.relativeDifferentialForms (Spec.map φ) (p : ℤ)).val.obj (op ⊤)) :=
  rfl

/-- The arrows of the complex of global sections are the de Rham differentials of
`Ω^•_{Spec A/Spec R}`, read on global sections. -/
theorem deRhamSectionsComplex_d_apply (p q : ℕ) (x : (deRhamSectionsComplex φ).X p) :
    ((deRhamSectionsComplex φ).d p q).hom x =
      (((Spec.map φ).deRhamComplex.d p q).val.app (op ⊤) x) :=
  rfl

/-! ### The base ring acting on global sections -/

/-- **The triangle identity of `(Spec φ)^{-1} ⊣ (Spec φ)_*`, on global sections.** The unit
`Γ(Spec R, 𝒪) ⟶ Γ(Spec A, (Spec φ)^{-1}𝒪_{Spec R})` followed by the structural map to
`𝒪_{Spec A}` is the map induced by `Spec φ` on global functions. -/
theorem inverseImageSectionsMap_comp_structureMap :
    Scheme.Hom.inverseImageSectionsMap (Spec.map φ) ≫
        (inverseImageStructureMap (Spec.map φ)).hom.app (op ⊤) =
      (Spec.map φ).appTop := by
  have h := (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (Spec.map φ).base).homEquiv (Spec R).sheaf (Spec A).sheaf)).apply_symm_apply
    (⟨(Spec.map φ).c⟩ : (Spec R).sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (Spec.map φ).base).obj (Spec A).sheaf)
  rw [Adjunction.homEquiv_apply] at h
  exact congrArg (fun t => t.hom.app (op ⊤)) h

/-- **The base ring map, followed by the structural map, is `φ`.** The comparison
`R ⟶ Γ(Spec A, (Spec φ)^{-1}𝒪_{Spec R})` composed with `(Spec φ)^{-1}𝒪_{Spec R} ⟶ 𝒪_{Spec A}` on
global sections is `φ` followed by `R ≅ Γ(Spec R, 𝒪)`.

This is the one compatibility of scalars the complex-level comparison needs: it says that the
`R`-action on global sections of the relative de Rham complex, which goes through
`(Spec φ)^{-1}𝒪_{Spec R}`, agrees with the `R`-action through `A` on the global differential
forms. -/
theorem affineBaseRingMap_comp_structureMap :
    Scheme.Hom.affineBaseRingMap φ ≫
        (inverseImageStructureMap (Spec.map φ)).hom.app (op ⊤) =
      φ ≫ (Scheme.ΓSpecIso A).inv :=
  ((Category.assoc (Scheme.ΓSpecIso R).inv (Scheme.Hom.inverseImageSectionsMap (Spec.map φ))
        ((inverseImageStructureMap (Spec.map φ)).hom.app (op ⊤))).trans
      (congrArg (fun t : (Spec R).sheaf.obj.obj (op ⊤) ⟶ (Spec A).sheaf.obj.obj (op ⊤) =>
        (Scheme.ΓSpecIso R).inv ≫ t) (inverseImageSectionsMap_comp_structureMap φ))).trans
    (Scheme.ΓSpecIso_inv_naturality φ).symm

/-- `affineBaseRingMap_comp_structureMap`, read on an element of `R`. -/
theorem affineBaseRingMap_structureMap_apply (r : ↥R) :
    ((inverseImageStructureMap (Spec.map φ)).hom.app (op ⊤)).hom
        ((Scheme.Hom.affineBaseRingMap φ).hom r) =
      (Scheme.ΓSpecIso A).inv.hom (φ.hom r) :=
  congrArg (fun t : R ⟶ (Spec A).sheaf.obj.obj (op ⊤) => t.hom r)
    (affineBaseRingMap_comp_structureMap φ)

/-- Equal global functions act equally on global differential forms. This is `congrArg` at the
one spelling of the scalar action in which the instance is available. -/
theorem smul_relativeDifferentialForms_congr
    {s t : ↥((_root_.AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
      (Spec A).sheaf).obj.obj (op ⊤))} (h : s = t) (p : ℕ)
    (y : ↥((Scheme.Hom.relativeDifferentialForms (Spec.map φ) (p : ℤ)).val.obj (op ⊤))) :
    s • y = t • y :=
  congrArg (fun z => z • y) h

/-! ### The comparison of complexes -/

/-- **The degreewise comparison of differential forms, as a map of `R`-modules.** Its underlying
function is `differentialFormsSectionsIso`; the `R`-linearity is
`affineBaseRingMap_comp_structureMap`. -/
def deRhamSectionsComplexTermMap (p : ℕ) :
    (ringDeRhamComplex φ).X p ⟶ (deRhamSectionsComplex φ).X p :=
  letI := φ.hom.toAlgebra
  ModuleCat.ofHom (Y := (deRhamSectionsComplex φ).X p)
    { toFun := fun x => (differentialFormsSectionsIso φ p).hom.hom x
      map_add' := fun x y => (differentialFormsSectionsIso φ p).hom.hom.map_add x y
      map_smul' := fun r x =>
        ((congrArg (differentialFormsSectionsIso φ p).hom.hom
              (algebraMap_smul ↥A r x).symm).trans
            ((differentialFormsSectionsIso φ p).hom.hom.map_smul (φ.hom r) x)).trans
          (smul_relativeDifferentialForms_congr φ
            (affineBaseRingMap_structureMap_apply φ r).symm p _) }

/-- The degreewise comparison of `R`-modules is the degreewise comparison of `A`-modules, read on
an element. -/
theorem deRhamSectionsComplexTermMap_apply (p : ℕ) (x : (ringDeRhamComplex φ).X p) :
    (deRhamSectionsComplexTermMap φ p).hom x =
      (differentialFormsSectionsIso φ p).hom.hom x :=
  rfl

/-- The degreewise comparison of differential forms is an isomorphism of `R`-modules. -/
instance isIso_deRhamSectionsComplexTermMap (p : ℕ) :
    IsIso (deRhamSectionsComplexTermMap φ p) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (differentialFormsSectionsIso φ p).toLinearEquiv.bijective

/-- **The degreewise comparison of differential forms, as an isomorphism of `R`-modules.** -/
def deRhamSectionsComplexTermIso (p : ℕ) :
    (ringDeRhamComplex φ).X p ≅ (deRhamSectionsComplex φ).X p :=
  asIso (deRhamSectionsComplexTermMap φ p)

/-- **The degree-`p` square of [Stacks Project, Tag 0FLW], for every `p`.** The degreewise
comparison of differential forms carries the algebraic de Rham differential to the de Rham
differential of `Ω^•_{Spec A/Spec R}`, read on global sections.

The `R`-module generators `a₀ · (d a₁ ∧ ⋯ ∧ d a_p)` span `⋀^p_A Ω[A⁄R]`, and on such a generator
both differentials produce `d a₀ ∧ d a₁ ∧ ⋯ ∧ d a_p`. -/
theorem deRhamSectionsComplexTermMap_comm (p : ℕ) :
    deRhamSectionsComplexTermMap φ p ≫ (deRhamSectionsComplex φ).d p (p + 1) =
      (ringDeRhamComplex φ).d p (p + 1) ≫ deRhamSectionsComplexTermMap φ (p + 1) := by
  let := φ.hom.toAlgebra
  refine ModuleCat.hom_ext (LinearMap.ext_on
    (Crystalline.span_range_smul_ιMulti_eq_top (R := ↥R) (KaehlerDifferential.D ↥R ↥A)
      (KaehlerDifferential.span_range_derivation ↥R ↥A) p) ?_)
  rintro _ ⟨a, rfl⟩
  refine Eq.trans (deRhamSectionsComplex_d_apply φ p (p + 1) _) ?_
  refine Eq.trans (deRhamComplex_d_sectionsIso φ p a) ?_
  exact congrArg (differentialFormsSectionsIso φ (p + 1)).hom.hom
    (KaehlerDifferential.deRhamComplex_d_smul_ιMulti_D p a).symm

/-- **[Stacks Project, Tag 0FLW] at the level of complexes.** For a morphism of affine schemes
`Spec φ : Spec A ⟶ Spec R`, the global relative differential forms of `Spec φ` are the algebraic
de Rham complex `Ω^•_{A/R} = (⋀^•_A Ω[A⁄R], d)` **as a cochain complex of `R`-modules**: the
degreewise comparison of
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.differentialFormsSectionsIso` commutes with the
de Rham differential in every degree, not only in degree zero.

This is the comparison the tag's proof starts from, complete as a statement about complexes.
The tag's two assertions — that `RΓ(Spec A, Ω^•_{Spec A/Spec R})` is `Ω^•_{A/R}` in `D(R)`, and
the resulting statement about de Rham cohomology — are *not* proved here, since `Γ` is not `RΓ`;
the passage needs the affine acyclicity of a quasi-coherent sheaf together with Leray's
acyclicity lemma, and it is carried out in
`StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamDerived`, where
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.derivedDeRhamSectionsIso` and
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamCohomologyIsoInt` take this
isomorphism as their starting point. -/
@[stacks 0FLW "Γ(Spec A, Ω^•) ≅ Ω^•_{A/R} as a cochain complex of R-modules; not derived"]
def deRhamSectionsComplexIso : ringDeRhamComplex φ ≅ deRhamSectionsComplex φ :=
  HomologicalComplex.Hom.isoOfComponents (deRhamSectionsComplexTermIso φ) (by
    rintro i j rfl
    exact deRhamSectionsComplexTermMap_comm φ i)

/-- **The complex-level comparison is the degreewise comparison in each degree**, so it is the
isomorphism already recorded degreewise and not a second comparison of differential forms. -/
theorem deRhamSectionsComplexIso_hom_f_apply (p : ℕ) (x : (ringDeRhamComplex φ).X p) :
    ((deRhamSectionsComplexIso φ).hom.f p).hom x =
      (differentialFormsSectionsIso φ p).hom.hom x :=
  rfl

end Comparison

end Stacks.AlgebraicGeometry.AffineDifferentialsIso

end
