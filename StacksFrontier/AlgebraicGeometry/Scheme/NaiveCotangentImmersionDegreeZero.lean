module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentHomologyZero
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.CategoryTheory.Sites.Modules.CorepresentingConormalSequence
public import StacksFrontier.Homology.DoubleHomology
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The degree-zero cohomology sheaf of the naive cotangent complex of an immersion

Let `i : Z ⟶ X` be an immersion of schemes.  This file proves that the degree `0` cohomology
sheaf of the naive cotangent complex `NL_{Z/X}` vanishes.

Together with the vanishing outside degrees `-1` and `0` already recorded for a general
morphism, this says that `NL_{Z/X}` is concentrated in degree `-1`; it is the degreewise form
of one half of the assertion of [Stacks Project, Tag 0FV2] that `NL_{Z/X}` is isomorphic to
`C_{Z/X}[1]` in `D(𝒪_Z)`.

## Main results

* `Stacks.NaiveCotangentDegreeZero.isZero_moduleOfDifferentialsOfSite`: the sheaf of relative
  differentials `Ω_{O₂/O₁}` of a *locally surjective* homomorphism of sheaves of commutative
  rings on a site is zero.  A relative derivation kills the image of `O₁`, hence vanishes
  locally, hence vanishes; so the functor it corepresents is constant and its corepresenting
  object has zero identity.
* `Stacks.NaiveCotangentDegreeZero.isZero_homology_zero_naiveCotangentComplex`: for a locally
  surjective homomorphism `a : A ⟶ B` of sheaves of commutative rings on a site,
  `H⁰(NL_{B/A}) = 0`.
* `Stacks.NaiveCotangentDegreeZero.isLocallySurjective_inverseImageStructureMap`: for a
  morphism of schemes that is surjective on stalks, `i^{-1}𝒪_X ⟶ 𝒪_Z` is locally surjective.
* `AlgebraicGeometry.Scheme.isZero_homology_zero_naiveCotangentComplex_of_isImmersion`:
  **the degree `0` clause of [Stacks Project, Tag 0FV2].**

## Implementation notes

The identification of `H⁰(NL_{B/A})` with `Ω_{B/A}` is rebuilt here rather than imported: it is
the composite of the degree-`0` homology of a `HomologicalComplex.double`
(`HomologicalComplex.doubleHomologyIsoCokernel`), the right exactness of the conormal sequence
(`Stacks.Sites.Conormal.conormalSequence_exact` together with
`Stacks.Sites.Conormal.conormalSequence_epi`), and the comparison of the image-presheaf model
of the differentials with the corepresenting sheaf
(`Stacks.Sites.Conormal.imageDifferentialsIso`).

**What is not proved here.**  The other half of Tag 0FV2, the identification of
`H⁻¹(NL_{Z/X})` with the conormal sheaf `C_{Z/X}` of `Stacks.Conormal.conormalSheaf`, is not
proved here.  The attribute below names the clause that is proved.

It *is* proved elsewhere in the library, so do not rebuild it: it is
`Stacks.Conormal.Sites.homologyNegOneIsoConormalSheaf` of
`StacksFrontier/AlgebraicGeometry/ConormalComparison/NaiveCotangentImmersionShift.lean`, an
isomorphism `(AlgebraicGeometry.Scheme.naiveCotangentComplex i).homology (-1) ≅
Stacks.Conormal.conormalSheaf i` carrying `@[stacks 0FV2 "degree -1 clause"]`, and the shift
statement itself is `Stacks.Conormal.Sites.quasiIso_conormalShiftComparison` in the same file.
That file reaches them through the comparison with the trivial presentation
(`immersionTrivialComparison`) rather than through a morphism built directly out of the
algebra-level input of [Stacks Project, Tag 07BP], which is indeed formalized only as the
identification of `H₁` of the naive cotangent complex of a surjection with its conormal module
and not at the complex level.

## References

* [Stacks Project, Tag 0FV2](https://stacks.math.columbia.edu/tag/0FV2)
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J), the cohomology sheaves
  of the naive cotangent complex of a morphism of schemes.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the degree-`0`
  cohomology sheaf of `NL(α)` is `Ω_{B/A}` for every polynomial presentation `α`.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), corepresentability of
  the functor of relative derivations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u w z

namespace Stacks.NaiveCotangentDegreeZero

open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite universalDerivationOfSite)

/-! ### Derivations along a locally surjective homomorphism -/

section Derivations

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {S' R : Cᵒᵖ ⥤ CommRingCat.{w}} (φ : S' ⟶ R) [Presheaf.IsLocallySurjective J φ]

/-- A relative derivation with values in a *sheaf* of modules along a locally surjective
homomorphism of sheaves of rings vanishes: every section of the target is locally the image of
a section of the source, the derivation kills those, and a section of a sheaf vanishing locally
vanishes. -/
theorem derivation_d_eq_zero {M : PresheafOfModules.{z} (R ⋙ forget₂ CommRingCat RingCat)}
    (hM : Presheaf.IsSheaf J M.presheaf) (d : PresheafOfModulesOfCommRing.Derivation' M φ)
    {U : Cᵒᵖ} (b : ToType (R.obj U)) : d.d b = 0 :=
  hM.isSeparated U.unop _ (Presheaf.imageSieve_mem J φ b) (d.d b) 0 fun V g hg => by
    have h1 : (ConcreteCategory.hom (M.map g.op)) (d.d b) = 0 := by
      rw [← d.d_map g.op b, ← Presheaf.app_localPreimage φ b g hg, d.d_app]
      rfl
    exact h1.trans (map_zero _).symm

/-- Along a locally surjective homomorphism of sheaves of rings there is exactly one relative
derivation with values in a sheaf of modules, the zero one. -/
theorem derivation_eq {M : PresheafOfModules.{z} (R ⋙ forget₂ CommRingCat RingCat)}
    (hM : Presheaf.IsSheaf J M.presheaf) (d d' : PresheafOfModulesOfCommRing.Derivation' M φ) : d = d' := by
  refine PresheafOfModulesOfCommRing.Derivation.ext ?_
  funext U
  ext b
  rw [derivation_d_eq_zero φ hM d b, derivation_d_eq_zero φ hM d' b]

end Derivations

/-! ### The sheaf of differentials of a locally surjective homomorphism -/

section Differentials

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (O₁ O₂ : Sheaf J CommRingCat.{w}) (φ : O₁ ⟶ O₂)

/-- **The sheaf of relative differentials of a locally surjective homomorphism of sheaves of
commutative rings is zero.**  It corepresents the functor of relative derivations, and by
`Stacks.NaiveCotangentDegreeZero.derivation_eq` that functor takes only one value; so the
identity of the corepresenting object coincides with the zero morphism. -/
theorem isZero_moduleOfDifferentialsOfSite [Presheaf.IsLocallySurjective J φ.hom] :
    IsZero (moduleOfDifferentialsOfSite.{v, u, w, z} O₁ O₂ φ) := by
  rw [IsZero.iff_id_eq_zero]
  obtain ⟨f, -, huniq⟩ :=
    AlgebraicGeometry.SheafOfModules.existsUnique_descDerivation.{v, u, w, z} O₁ O₂ φ
      (moduleOfDifferentialsOfSite.{v, u, w, z} O₁ O₂ φ)
      (universalDerivationOfSite.{v, u, w, z} O₁ O₂ φ)
  have key (g) := huniq g (derivation_eq φ.hom
    (moduleOfDifferentialsOfSite.{v, u, w, z} O₁ O₂ φ).isSheaf _ _)
  exact (key _).trans (key _).symm

end Differentials

/-! ### The degree-zero cohomology sheaf of `NL_{B/A}` -/

section Homology

open Stacks.SheafOfModules Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-- **`H⁰(NL_{B/A}) = 0` for a locally surjective homomorphism of sheaves of commutative
rings.**  Its degree `0` cohomology sheaf is `Ω_{B/A}`, which vanishes. -/
theorem isZero_homology_zero_naiveCotangentComplex
    [Presheaf.IsLocallySurjective J a.hom] :
    IsZero ((naiveCotangentComplex.{v, u, w, z} J A B a).homology 0) :=
  (isZero_moduleOfDifferentialsOfSite.{v, u, w, z} A B a).of_iso
    (Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso.{v, u, w, z} J A B a)

end Homology

/-! ### The structural homomorphism of a morphism of schemes surjective on stalks -/

section Schemes

open AlgebraicGeometry

/-- For a morphism of schemes that is surjective on stalks, the structural homomorphism
`i^{-1}𝒪_X ⟶ 𝒪_Z` is locally surjective.  Its stalk at `z` is, up to the canonical
identification of the stalk of the inverse image sheaf, the stalk map of `i`. -/
theorem isLocallySurjective_inverseImageStructureMap {Z X : Scheme.{u}} (i : Z ⟶ X)
    [SurjectiveOnStalks i] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z.toRingedSpace.carrier)
      (AlgebraicGeometry.inverseImageStructureMap i).hom := by
  refine (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
    (AlgebraicGeometry.inverseImageStructureMap i).hom).mpr fun z => ?_
  intro y
  obtain ⟨x, hx⟩ := i.stalkMap_surjective z y
  refine ⟨(ConcreteCategory.hom
    (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso i z).inv) x, ?_⟩
  rw [← hx, Stacks.SheafifyStalk.stalkMap_eq_stalkInverseImageStructureSheafIso_hom_comp i z]
  exact (ConcreteCategory.comp_apply _ _ x).symm

end Schemes

end Stacks.NaiveCotangentDegreeZero

namespace AlgebraicGeometry.Scheme

open Stacks.NaiveCotangentDegreeZero

/-- **Stacks 0FV2, degree `0` clause.**  Let `i : Z ⟶ X` be an immersion of schemes.  Then the
degree `0` cohomology sheaf of the naive cotangent complex `NL_{Z/X}` vanishes.

The source states that `NL_{Z/X}` is isomorphic to `C_{Z/X}[1]` in `D(𝒪_Z)`, with `C_{Z/X}` the
conormal sheaf of `Z` in `X`.  Since both sides are complexes concentrated in one degree, that
assertion is the conjunction of the two degreewise statements `H⁻¹(NL_{Z/X}) ≅ C_{Z/X}` and
`H⁰(NL_{Z/X}) = 0`.  The second is what is proved here; the first is not proved, here or
anywhere in this library, and the attribute is scoped accordingly. -/
@[stacks 0FV2 "degreewise form of the shift statement, degree 0 clause only: \
H^0(NL_{Z/X}) = 0; NOT the identification of H^{-1}(NL_{Z/X}) with the conormal sheaf"]
theorem isZero_homology_zero_naiveCotangentComplex_of_isImmersion {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] :
    Limits.IsZero ((naiveCotangentComplex i).homology 0) := by
  have : CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology Z.toRingedSpace.carrier)
      (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap
        i.toLRSHom.toShHom).hom :=
    isLocallySurjective_inverseImageStructureMap i
  exact isZero_homology_zero_naiveCotangentComplex.{u, u, u, u}
    (Opens.grothendieckTopology Z.toRingedSpace.carrier)
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf i.toLRSHom.toShHom)
    Z.toRingedSpace.sheaf
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap i.toLRSHom.toShHom)

end AlgebraicGeometry.Scheme

end
