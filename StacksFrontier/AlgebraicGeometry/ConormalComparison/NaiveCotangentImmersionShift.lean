module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.SitesConormalComparison
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentTrivialPresentation
public import StacksFrontier.Homology.DoubleHomology

/-!
# The naive cotangent complex of an immersion is the shifted conormal sheaf

Let `i : Z ⟶ X` be an immersion of schemes.  This file proves that the naive cotangent complex
`NL_{Z/X}` is quasi-isomorphic to `𝒞_{Z/X}[1]`, the complex with the conormal sheaf of `Z` in
`X` placed in degree `-1`, which is the assertion of [Stacks Project, Tag 0FV2].

The degree `0` clause — `H⁰(NL_{Z/X}) = 0` — is
`AlgebraicGeometry.Scheme.isZero_homology_zero_naiveCotangentComplex_of_isImmersion` and is not
repeated here.  What this file adds is the degree `-1` identification and the shift itself.

## Route

`NL_{Z/X}` is built from the *canonical polynomial* presentation `(i^{-1}𝒪_X)[𝒪_Z] ⟶ 𝒪_Z`, so
its degree `-1` term is the conormal sheaf of that presentation, not of the structural
homomorphism `i^{-1}𝒪_X ⟶ 𝒪_Z` itself.  Three steps bridge the gap.

* The structural homomorphism is locally surjective
  (`Stacks.Conormal.Sites.isLocallySurjective_structHom`), so it is itself a presentation of
  `𝒪_Z` over `i^{-1}𝒪_X` — the *trivial* one.  Stacks 08TL for the trivial presentation,
  `Stacks.SheafOfModules.quasiIso_trivialNaiveCotangentComplexComparison`, says that the
  comparison `NL(a) ⟶ NL_{Z/X}` is a quasi-isomorphism.
* `NL(a)` is `I/I² ⟶ 0`: its degree `0` term is `𝒪_Z ⊗ Ω[(i^{-1}𝒪_X)/(i^{-1}𝒪_X)]`, a zero
  object (`Stacks.SheafOfModules.isZero_trivialConormalSequence_X₂`).  So
  `H^{-1}(NL(a))` is the kernel of a map into a zero object, that is `I/I²`.
* `Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf` identifies the sites-level `I/I²`
  with the geometric conormal sheaf `𝒞_{Z/X}` of [Stacks, Tag 01R2].

## Main definitions

* `Stacks.Conormal.Sites.immersionTrivialComplex` and
  `Stacks.Conormal.Sites.immersionTrivialComparison`: the naive cotangent complex of the
  trivial presentation of `𝒪_Z` over `i^{-1}𝒪_X` and its comparison with `NL_{Z/X}`.
* `Stacks.Conormal.Sites.conormalShiftComplex`: the complex `𝒞_{Z/X}[1]`.
* `Stacks.Conormal.Sites.conormalShiftComparison`: the chain map `𝒞_{Z/X}[1] ⟶ NL_{Z/X}`.

## Main results

* `Stacks.Conormal.Sites.homologyNegOneIsoConormalSheaf`: **the degree `-1` clause of
  [Stacks Project, Tag 0FV2]** — `H^{-1}(NL_{Z/X}) ≅ 𝒞_{Z/X}`.
* `Stacks.Conormal.Sites.quasiIso_conormalShiftComparison`: **the shift clause of
  [Stacks Project, Tag 0FV2]** — the chain map `𝒞_{Z/X}[1] ⟶ NL_{Z/X}` is a
  quasi-isomorphism.

## Implementation notes

The two spellings of the category of sheaves of `𝒪_Z`-modules — the one the naive cotangent
complex of a morphism of schemes lands in and the one `AlgebraicGeometry.Scheme.Modules` uses —
are definitionally equal but not syntactically so, and instance search for the zero object does
not see through the difference.  `Stacks.Conormal.Sites.modulesOfSite` fixes the first spelling
and `Stacks.Conormal.Sites.conormalSheafOfSite` re-declares the geometric conormal sheaf at it,
so that `𝒞_{Z/X}[1]` is formed in one category throughout.

For the same reason the degree `-1` component of the shift comparison is packaged as an
isomorphism, `Stacks.Conormal.Sites.conormalShiftXNegOneIso`, before being used: instance
search finds `IsIso` of an `Iso.hom` but not of a composite whose factors live at the other
spelling.

## References

* [Stacks Project, Tag 0FV2](https://stacks.math.columbia.edu/tag/0FV2)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2), the conormal sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open ZeroObject

universe u

noncomputable section

namespace CategoryTheory.Limits

/-- A morphism between two zero objects is an isomorphism. -/
theorem isIso_of_isZero_of_isZero {C : Type*} [Category C] [HasZeroObject C] {A B : C}
    (hA : IsZero A) (hB : IsZero B) (f : A ⟶ B) : IsIso f := by
  have h : f = (hA.isoZero ≪≫ hB.isoZero.symm).hom := hA.eq_of_src _ _
  rw [h]
  infer_instance

end CategoryTheory.Limits

namespace Stacks.Conormal.Sites

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The category of sheaves of `𝒪_Z`-modules, at the spelling the naive cotangent complex of a
morphism out of `Z` uses. -/
abbrev modulesOfSite (Z : Scheme.{u}) := _root_.SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (J := siteJ Z) (structSheaf Z))

/-- `HasZeroObject` for the category of sheaves of `𝒪_Z`-modules. -/
instance hasZeroObject_modules : HasZeroObject (modulesOfSite Z) :=
  hasZeroObject_of_hasTerminal_object

/-- `NL(a)` of the trivial presentation `i^{-1}𝒪_X ⟶ 𝒪_Z`. -/
abbrev immersionTrivialComplex :=
  Stacks.SheafOfModules.trivialNaiveCotangentComplex (invSheaf i) (structSheaf Z) (structHom i)

/-- The comparison `NL(a) ⟶ NL_{Z/X}`. -/
abbrev immersionTrivialComparison :
    immersionTrivialComplex i ⟶ AlgebraicGeometry.Scheme.naiveCotangentComplex i :=
  Stacks.SheafOfModules.trivialNaiveCotangentComplexComparison
    (invSheaf i) (structSheaf Z) (structHom i)


/-- **Stacks 08TL for the structural homomorphism of an immersion.** -/
theorem quasiIso_immersionTrivialComparison : QuasiIso (immersionTrivialComparison i) :=
  Stacks.SheafOfModules.quasiIso_trivialNaiveCotangentComplexComparison
    (invSheaf i) (structSheaf Z) (structHom i)

/-- The comparison is an isomorphism on degree `-1` cohomology, being a quasi-isomorphism. -/
instance isIso_homologyMap_immersionTrivialComparison :
    IsIso (HomologicalComplex.homologyMap (immersionTrivialComparison i) (-1)) :=
  (quasiIsoAt_iff_isIso_homologyMap (immersionTrivialComparison i) (-1)).mp
    ((quasiIso_immersionTrivialComparison i).quasiIsoAt (-1))

/-- `H^{-1}(NL(a)) ≅ I/I²`. -/
def trivialHomologyNegOneIso :
    (immersionTrivialComplex i).homology (-1) ≅ sitesConormalSheaf i :=
  (HomologicalComplex.doubleHomologyIsoKernel
      (Stacks.SheafOfModules.trivialConormalSequence
        (invSheaf i) (structSheaf Z) (structHom i)).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)) ≪≫
    kernelIsoOfEq (Stacks.SheafOfModules.trivialConormalSequence_f_eq_zero
      (invSheaf i) (structSheaf Z) (structHom i)) ≪≫
    kernelZeroIsoSource

/-- **Stacks 0FV2, degree `-1` clause.**  For an immersion of schemes `i : Z ⟶ X` the degree
`-1` cohomology sheaf of the naive cotangent complex `NL_{Z/X}` is the conormal sheaf
`𝒞_{Z/X}` of `Z` in `X`.

Three identifications are composed.  `NL_{Z/X}` is the naive cotangent complex of the
*canonical polynomial* presentation of `𝒪_Z` over `i^{-1}𝒪_X`, so its degree `-1` term is the
conormal sheaf of that presentation and not of `i^{-1}𝒪_X ⟶ 𝒪_Z` itself; Stacks 08TL for the
trivial presentation (`Stacks.SheafOfModules.quasiIso_trivialNaiveCotangentComplexComparison`)
identifies the cohomology of the two complexes.  The complex of the trivial presentation is
`I/I² ⟶ 0`, so its degree `-1` cohomology is `I/I²` on the nose
(`Stacks.Conormal.Sites.trivialHomologyNegOneIso`).  Finally
`Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf` identifies that sites-level `I/I²`
with the geometric conormal sheaf `𝒞_{Z/X}`. -/
@[stacks 0FV2 "degree -1 clause: H^{-1}(NL_{Z/X}) is the conormal sheaf C_{Z/X}"]
def homologyNegOneIsoConormalSheaf :
    (AlgebraicGeometry.Scheme.naiveCotangentComplex i).homology (-1) ≅
      (Stacks.Conormal.conormalSheaf i : Z.Modules) :=
  (asIso (HomologicalComplex.homologyMap (immersionTrivialComparison i) (-1))).symm ≪≫
    trivialHomologyNegOneIso i ≪≫ sitesConormalSheafIsoConormalSheaf i

/-! ### The shift -/

/-- The geometric conormal sheaf `𝒞_{Z/X}`, with its type declared at the spelling the naive
cotangent complex of `i` uses. -/
def conormalSheafOfSite : modulesOfSite Z := Stacks.Conormal.conormalSheaf i

/-- The complex `𝒞_{Z/X}[1]`. -/
def conormalShiftComplex : CochainComplex (modulesOfSite Z) ℤ :=
  HomologicalComplex.double (0 : conormalSheafOfSite i ⟶ 0)
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)

/-- `𝒞_{Z/X}[1]` is concentrated in degree `-1`. -/
theorem isZero_conormalShiftComplex_X_of_ne (k : ℤ) (h : k ≠ -1) :
    IsZero ((conormalShiftComplex i).X k) := by
  by_cases h0 : k = 0
  · subst h0
    exact IsZero.of_iso (isZero_zero _) (HomologicalComplex.doubleXIso₁
      (0 : conormalSheafOfSite i ⟶ 0)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide))
  · exact HomologicalComplex.isZero_double_X _ _ k h h0

/-- The chain map `𝒞_{Z/X}[1] ⟶ NL(a)`. -/
def conormalShiftToTrivial : conormalShiftComplex i ⟶ immersionTrivialComplex i :=
  HomologicalComplex.mkHomFromDouble
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    ((conormalComparisonIso i).hom ≫ (HomologicalComplex.doubleXIso₀
      (Stacks.SheafOfModules.trivialConormalSequence
        (invSheaf i) (structSheaf Z) (structHom i)).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).inv)
    (0 : (0 : modulesOfSite Z) ⟶ (immersionTrivialComplex i).X 0)
    ((Stacks.SheafOfModules.isZero_trivialNaiveCotangentComplex_X_of_ne
      (invSheaf i) (structSheaf Z) (structHom i) 0 (by decide)).eq_of_tgt _ _)
    (fun k _ ↦ Limits.zero_comp)

/-- The chain map `𝒞_{Z/X}[1] ⟶ NL_{Z/X}`. -/
def conormalShiftComparison :
    conormalShiftComplex i ⟶ AlgebraicGeometry.Scheme.naiveCotangentComplex i :=
  conormalShiftToTrivial i ≫ immersionTrivialComparison i


/-- The degree `-1` terms of `𝒞_{Z/X}[1]` and of `NL(a)` are isomorphic, by the conormal
comparison. -/
def conormalShiftXNegOneIso :
    (conormalShiftComplex i).X (-1) ≅ (immersionTrivialComplex i).X (-1) :=
  HomologicalComplex.doubleXIso₀ (0 : conormalSheafOfSite i ⟶ 0)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) ≪≫
    conormalComparisonIso i ≪≫
    (HomologicalComplex.doubleXIso₀
      (Stacks.SheafOfModules.trivialConormalSequence
        (invSheaf i) (structSheaf Z) (structHom i)).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).symm

/-- In degree `-1` the chain map is the conormal comparison. -/
theorem conormalShiftToTrivial_f_negOne :
    (conormalShiftToTrivial i).f (-1) = (conormalShiftXNegOneIso i).hom :=
  HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _

/-- Every component of the chain map `𝒞_{Z/X}[1] ⟶ NL(a)` is an isomorphism: in degree `-1` it
is the conormal comparison, and in every other degree both terms are zero objects. -/
instance isIso_conormalShiftToTrivial_f (k : ℤ) : IsIso ((conormalShiftToTrivial i).f k) := by
  by_cases h1 : k = -1
  · subst h1
    rw [conormalShiftToTrivial_f_negOne]
    infer_instance
  · exact CategoryTheory.Limits.isIso_of_isZero_of_isZero
      (isZero_conormalShiftComplex_X_of_ne i k h1)
      (Stacks.SheafOfModules.isZero_trivialNaiveCotangentComplex_X_of_ne
        (invSheaf i) (structSheaf Z) (structHom i) k h1) _

/-- **`𝒞_{Z/X}[1]` is isomorphic to `NL(a)` as a complex**, all components of the chain map
between them being isomorphisms. -/
instance isIso_conormalShiftToTrivial : IsIso (conormalShiftToTrivial i) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- **Stacks 0FV2, the shift.**  For an immersion of schemes `i : Z ⟶ X` the canonical chain
map from `𝒞_{Z/X}[1]` — the cochain complex with the conormal sheaf of `Z` in `X` in degree
`-1` and zero in every other degree — to the naive cotangent complex `NL_{Z/X}` is a
quasi-isomorphism.

The source states the conclusion as an isomorphism `NL_{Z/X} ≅ 𝒞_{Z/X}[1]` in `D(𝒪_Z)`.  A
quasi-isomorphism of cochain complexes of sheaves of `𝒪_Z`-modules is the scheme-level content
of that statement: it is a map of honest complexes which the localisation functor to the derived
category inverts.  The statement is given in that form, and the clause label says so. -/
@[stacks 0FV2 "shift clause as a quasi-isomorphism of complexes C_{Z/X}[1] ⟶ NL_{Z/X}"]
theorem quasiIso_conormalShiftComparison : QuasiIso (conormalShiftComparison i) := by
  have := quasiIso_immersionTrivialComparison i
  exact inferInstanceAs
    (QuasiIso (conormalShiftToTrivial i ≫ immersionTrivialComparison i))

end Stacks.Conormal.Sites

end

end
