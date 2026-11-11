module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.Algebra.Homology.DerivedCategory.QuasiIsoMapOfRightDerivedVanishing
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishingAbelian
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelAmbientDeterminacy
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Equation07LP
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.CategoryTheory.Limits.ThinEqualizers
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness

/-!
# Sections over an affine open of `T` of the restriction of the de Rham complex

Fix a global crystalline situation `(p, (S, I, γ), X)`, an object `A = (U, T, δ)` of `Cris(X/S)`,
and write `G ↦ G_T` for the restriction of abelian sheaves on `Cris(X/S)` to the Zariski site of
`T` (`...SmallSite.CrystallineThickening.abelianAmbientRestriction`). Let `F` be a locally
quasi-coherent sheaf of `𝒪_{X/S}`-modules (for instance a crystal in quasi-coherent modules, by
`...SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`) and `K = F ⊗ Ω^•_{X/S}` its de
Rham complex. This file proves, for every affine open `V` of `T`:

1. `G ↦ G_T` carries injective abelian sheaves to injective abelian sheaves, so `I_T` is acyclic
   for `Γ(V, -)` for every injective abelian sheaf `I` and every open `V`;
2. `Hʲ(V, (F ⊗ Ω^a_{X/S})_T) = Hʲ(V, F_T ⊗ Ω^a_{T/S,δ}) = 0` for `j > 0`, because
   `F_T ⊗ Ω^a_{T/S,δ}` is a quasi-coherent `𝒪_T`-module (Serre vanishing, [Stacks, Tag 01XB]);
3. hence for a quasi-isomorphism `K ⟶ J` into a bounded below complex of injective abelian
   sheaves, the induced map `Γ(V, K_T) ⟶ Γ(V, J_T)` of complexes of abelian groups is a
   quasi-isomorphism.

This is the affine acyclicity step in the proof of part (3) of [Stacks, Tag 07MW]: it lets the
restriction `u_*J ⟶ h_*J_T` be tested on sections over affine opens through the de Rham complex.

Restriction preserves injectives because its left adjoint, the lower shriek along the functor
`W ↦ A|_W` from the opens of `T` to `Cris(X/S)`, is exact ([Stacks, Tag 04BH]): the opens of `T`
have fibre products and equalizers, which `W ↦ A|_W` preserves; then [Stacks, Tag 015Z] applies.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `CrystallineThickening.preservesInjectiveObjects_abelianAmbientRestriction`: `G ↦ G_T`
  preserves injective objects.
* `CrystallineThickening.isZero_rightDerived_sections_abelianAmbientRestriction_of_injective`:
  part 1, `Hʲ(V, I_T) = 0` for `j > 0`, `I` injective, `V` any open of `T`.
* `isQuasicoherent_ambientTensorForms`: `F_T ⊗ Ω^a_{T/S,δ}` is quasi-coherent for a locally
  quasi-coherent `F`.
* `isZero_rightDerived_sections_ambientTensorFormsAbelian` and
  `isZero_rightDerived_sections_restrictTensorDifferentialFormsSheaf`: part 2, for
  `F_T ⊗ Ω^a_{T/S,δ}` and for `(F ⊗ Ω^a_{X/S})_T`.
* `CrystallineThickening.quasiIso_map_sections_abelianAmbientRestriction_of_isZero`: part 3 for
  any bounded below complex whose restricted terms are `Γ(V, -)`-acyclic.
* `CrystalDeRhamSheafData.quasiIso_map_sections_abelianAmbientRestriction`: part 3 for the de Rham
  complex `K = F ⊗ Ω^•_{X/S}`.

## What is and is not proved

Everything above is proved in full; the only hypothesis on `F` is local quasi-coherence, and the
differentials of the de Rham complex are arbitrary (`...SmallSite.CrystalDeRhamSheafData`), so
part 3 holds in particular for `...SmallSite.crystalDeRhamSheafData`. No tag attribute is placed:
these are steps of the proof of [Stacks, Tag 07MW] part (3), not statements of the source.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Restriction to `T` preserves injective objects -/

namespace CrystallineThickening

attribute [local instance] restrictOpenFunctor_isContinuous restrictOpenFunctor_isCocontinuous

variable {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S)

/-- The functor `W ↦ A|_W` from the opens of the ambient scheme to `Cris(X/S)` preserves
equalizers, its source being a partial order. -/
instance preservesLimitsOfShape_walkingParallelPair_restrictOpenFunctor :
    PreservesLimitsOfShape WalkingParallelPair (restrictOpenFunctor A) :=
  preservesLimitsOfShape_walkingParallelPair_of_isThin _

/-- **The left adjoint of `G ↦ G_T` is exact**: the lower shriek of abelian sheaves along
`W ↦ A|_W` preserves finite limits, by [Stacks, Tag 04BH], the opens of `T` having fibre products
and equalizers which `W ↦ A|_W` preserves. -/
theorem preservesFiniteLimits_abelianAmbientLowerShriek :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback (restrictOpenFunctor A)
      AddCommGrpCat.{u + 1} (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (smallTopology S)) :=
  Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1} _ _ _

/-- **`G ↦ G_T` carries injective abelian sheaves to injective abelian sheaves**
([Stacks, Tag 015Z]): it is right adjoint to an exact functor. -/
instance preservesInjectiveObjects_abelianAmbientRestriction :
    (abelianAmbientRestriction A).PreservesInjectiveObjects :=
  have := preservesFiniteLimits_abelianAmbientLowerShriek A
  have : (Functor.sheafPullbackConstruction.sheafPullback (restrictOpenFunctor A)
      AddCommGrpCat.{u + 1} (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (smallTopology S)).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (restrictOpenFunctor A)
      AddCommGrpCat.{u + 1} (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (smallTopology S))

/-- **Part 1: `Hʲ(V, I_T) = 0` for `j > 0`**, for every injective abelian sheaf `I` on
`Cris(X/S)` and every open `V` of `T`: `I_T` is injective. -/
theorem isZero_rightDerived_sections_abelianAmbientRestriction_of_injective
    (I : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) [Injective I]
    (V : A.obj.thickening.target.scheme.Opens) (p : ℕ) (hp : 0 < p) :
    IsZero ((((sheafSections (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}).obj (op V)).rightDerived p).obj
        ((abelianAmbientRestriction A).obj I)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hp
  exact Functor.isZero_rightDerived_obj_injective_succ _ _ _

end CrystallineThickening

/-! ### `F_T ⊗ Ω^a_{T/S,δ}` is acyclic on affine opens -/

variable {S : GlobalCrystallineSituation.{u}} {F : SheafOfModules.{u} (structureSheaf S)}

/-- **`F_T ⊗_{𝒪_T} Ω^a_{T/S,δ}` is quasi-coherent** for a locally quasi-coherent `F`: a tensor
product of the quasi-coherent `F_T` with an exterior power of the quasi-coherent `Ω_{T/S,δ}`. -/
theorem isQuasicoherent_ambientTensorForms (hF : IsLocallyQuasiCoherent F)
    (A : CrystallineThickening S) (a : ℕ) : (ambientTensorForms F A a).IsQuasicoherent :=
  have := isQuasicoherent_ambientModuleRestriction hF A
  Scheme.Modules.isQuasicoherent_tensorObj _ _ this inferInstance

/-- **Part 2: `Hʲ(V, F_T ⊗ Ω^a_{T/S,δ}) = 0` for `j > 0`** and `V` an affine open of `T`, for a
locally quasi-coherent `F`: Serre vanishing for the quasi-coherent module
`F_T ⊗ Ω^a_{T/S,δ}`, read on its underlying abelian sheaf at the coefficient universe `u + 1`. -/
theorem isZero_rightDerived_sections_ambientTensorFormsAbelian (hF : IsLocallyQuasiCoherent F)
    (A : CrystallineThickening S) (a : ℕ) (V : A.obj.thickening.target.scheme.Opens)
    (hV : IsAffineOpen V) (p : ℕ) (hp : 0 < p) :
    IsZero ((((sheafSections (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}).obj (op V)).rightDerived p).obj (ambientTensorFormsAbelian F A a)) :=
  have := isQuasicoherent_ambientTensorForms hF A a
  Stacks.Cohomology.Cech.isZero_rightDerived_sheafSections_uliftToSheaf_of_isAffineOpen _
    (ambientTensorForms F A a) V hV p hp

/-- **Part 2 for `(F ⊗ Ω^a_{X/S})_T`: `Hʲ(V, (F ⊗ Ω^a_{X/S})_T) = 0` for `j > 0`** and `V` an
affine open of `T`, through `(F ⊗ Ω^a_{X/S})_T ≅ F_T ⊗ Ω^a_{T/S,δ}`
(`restrictTensorDifferentialFormsSheafIso`). -/
theorem isZero_rightDerived_sections_restrictTensorDifferentialFormsSheaf
    (hF : IsLocallyQuasiCoherent F) (A : CrystallineThickening S) (a : ℕ)
    (V : A.obj.thickening.target.scheme.Opens) (hV : IsAffineOpen V) (p : ℕ) (hp : 0 < p) :
    IsZero ((((sheafSections (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}).obj (op V)).rightDerived p).obj
        ((CrystallineThickening.abelianAmbientRestriction A).obj
          (tensorDifferentialFormsSheaf F a))) :=
  (isZero_rightDerived_sections_ambientTensorFormsAbelian hF A a V hV p hp).of_iso
    ((Functor.mapIso _ (restrictTensorDifferentialFormsSheafIso F A a)))

/-! ### Part 3: the sections over an affine open of a resolution -/

namespace CrystallineThickening

variable (A : CrystallineThickening S)

/-- **Part 3, for a general complex.** Let `φ : K ⟶ J` be a quasi-isomorphism of bounded below
complexes of abelian sheaves on `Cris(X/S)` with `J` termwise injective, and `V` an open of `T`
such that every `(Kⁿ)_T` is acyclic for `Γ(V, -)`. Then `Γ(V, K_T) ⟶ Γ(V, J_T)` is a
quasi-isomorphism of complexes of abelian groups. -/
theorem quasiIso_map_sections_abelianAmbientRestriction_of_isZero
    {K J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ} (φ : K ⟶ J)
    [QuasiIso φ] (hK : CochainComplex.plus _ K) (hJ : CochainComplex.plus _ J)
    [∀ n, Injective (J.X n)] (V : A.obj.thickening.target.scheme.Opens)
    (hKac : ∀ n p, 0 < p → IsZero ((((sheafSections
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1}).obj
        (op V)).rightDerived p).obj ((abelianAmbientRestriction A).obj (K.X n)))) :
    QuasiIso ((((sheafSections (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((abelianAmbientRestriction A).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :=
  have : (abelianAmbientRestriction A).PreservesHomology := Functor.preservesHomologyOfExact _
  Functor.quasiIso_mapHomologicalComplex_of_isZero_rightDerived _ _
    (CochainComplex.plus_mapHomologicalComplex_obj _ hK)
    (CochainComplex.plus_mapHomologicalComplex_obj _ hJ) hKac
    (fun n p hp ↦ isZero_rightDerived_sections_abelianAmbientRestriction_of_injective A
      (J.X n) V p hp)

end CrystallineThickening

namespace CrystalDeRhamSheafData

variable (data : CrystalDeRhamSheafData S F) (A : CrystallineThickening S)

/-- **`Hʲ(V, (Kⁿ)_T) = 0` for `j > 0`** for every term of the de Rham complex `K = F ⊗ Ω^•_{X/S}`
of a locally quasi-coherent `F`, and `V` an affine open of `T`. -/
theorem isZero_rightDerived_sections_abelianAmbientRestriction_complex_X
    (hF : IsLocallyQuasiCoherent F) (V : A.obj.thickening.target.scheme.Opens)
    (hV : IsAffineOpen V) (n : ℤ) (p : ℕ) (hp : 0 < p) :
    IsZero ((((sheafSections (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}).obj (op V)).rightDerived p).obj
        ((CrystallineThickening.abelianAmbientRestriction A).obj (data.complex.X n))) := by
  by_cases hn : ∃ a : ℕ, ComplexShape.embeddingUpNat.f a = n
  · obtain ⟨a, ha⟩ := hn
    exact (isZero_rightDerived_sections_restrictTensorDifferentialFormsSheaf hF A a V hV p
      hp).of_iso (Functor.mapIso _ (Functor.mapIso _
        (data.natComplex.extendXIso ComplexShape.embeddingUpNat ha)))
  · simp only [not_exists] at hn
    exact Functor.map_isZero _ (Functor.map_isZero _
      (data.natComplex.isZero_extend_X ComplexShape.embeddingUpNat n hn))

/-- **Part 3: `Γ(V, K_T) ⟶ Γ(V, J_T)` is a quasi-isomorphism** for the de Rham complex
`K = F ⊗ Ω^•_{X/S}` of a locally quasi-coherent `F`, a quasi-isomorphism `K ⟶ J` into a bounded
below complex of injective abelian sheaves on `Cris(X/S)`, and `V` an affine open of `T`. -/
theorem quasiIso_map_sections_abelianAmbientRestriction (hF : IsLocallyQuasiCoherent F)
    {J : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ}
    (φ : data.complex ⟶ J) [QuasiIso φ] (hJ : CochainComplex.plus _ J)
    [∀ n, Injective (J.X n)] (V : A.obj.thickening.target.scheme.Opens) (hV : IsAffineOpen V) :
    QuasiIso ((((sheafSections (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((CrystallineThickening.abelianAmbientRestriction A).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ)) :=
  CrystallineThickening.quasiIso_map_sections_abelianAmbientRestriction_of_isZero A φ
    data.complexPlus.2 hJ V
    (data.isZero_rightDerived_sections_abelianAmbientRestriction_complex_X A hF V hV)

end CrystalDeRhamSheafData

end Crystalline.GlobalCrystallineSituation.SmallSite
