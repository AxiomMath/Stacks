module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Assembly.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDuality
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.LaurentChartDictionary
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsLinear
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.FiberRankIsomorphismInvariant
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.FlatPullbackTensorSingle
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorExact
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularConstantRank
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Duality.SmoothProperDiagonalTensor
public import StacksFrontier.AlgebraicGeometry.F6Rank136.SmoothIsNodal
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation

/-!
# Clauses (5) and (6) of [Stacks, Tag 0BS2] for the constructed dualizing sheaf

Let `k` be a field and `f : X ⟶ Spec k` proper. The dualizing complex of [Stacks, Tag 0BS2] is the
twisted inverse image `ω_X^• = f^×(𝒪_{Spec k})`, `Stacks.Duality.dualizingComplexOverField f`, and
the dualizing sheaf is `ω_X = H^{-1}(ω_X^•)`, `Stacks.Duality.dualizingSheafOverField f`.

* Clause (5): for `X` of dimension at most one there are isomorphisms
  `Hom(ℱ, ω_X) = Hom_k(H¹(X, ℱ), k)` for quasi-coherent `ℱ`, functorial in `ℱ`. They are
  `Stacks.Duality.clauseFiveAddEquiv` and `Stacks.Duality.clauseFiveAddEquiv_naturality`
  (`Curves/VanishingResults/DualizingSheafClauseFive.lean`);
  `Stacks.Duality.exists_natural_addEquiv_hom_dualizingSheafOverField` states the clause as one
  proposition with additive isomorphisms, and
  `Stacks.Duality.exists_natural_linearEquiv_hom_dualizingSheafOverField` with isomorphisms of
  `k`-vector spaces (`Stacks.Duality.clauseFiveLinearEquiv`), for the `k`-structure
  `AlgebraicGeometry.Scheme.linearOver f` on `X.Modules`.
* Clause (6): if `f` is smooth of relative dimension one, then `ω_X ≅ Ω_{X/k}`:
  `Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials`.

## The proof of clause (6)

The source derives it from [Stacks, Tag 0BRT], `∧^d Ω_{X/S}[d] ≅ a(𝒪_S)` for a smooth proper
morphism of relative dimension `d`; here `d = 1` and the proof of that tag is run at `d = 1`.
With `Δ : X ⟶ X ×_k X` the diagonal and `c` its twisted inverse image:

1. `ω_X^• ⊗ᴸ c(𝒪_{X ×_k X}) ≅ 𝒪_X`, the first three steps of the proof of [Stacks, Tag 0BRT]
   (`Stacks.Duality.nonempty_tensor_twistedInverseImage_diagonal_iso`: equation (0E2Q) of
   [Stacks, Tag 0E2P], then [Stacks, Tag 0A9U] for the perfect proper morphism `Δ`);
2. `c(𝒪_{X ×_k X}) ≅ 𝒩[-1]`, `𝒩` the normal sheaf of `Δ`: [Stacks, Tag 0BR0], the normal sheaf
   having rank one (`Stacks.Duality.normalRank_diagonal_eq_one`, from [Stacks, Tags 08S2, 02G1]);
3. `𝒩 ⊗ Ω_{X/k} ≅ 𝒪_X`, the evaluation pairing of the invertible conormal sheaf
   `𝒞_Δ ≅ Ω_{X/k}` ([Stacks, Tag 08S2]) with its dual `𝒩`; so `c(𝒪) ⊗ᴸ Ω_{X/k}[0] ≅ 𝒪_X[1]`,
   `Ω_{X/k}` being flat;
4. hence `ω_X^•[-1] ≅ ω_X^• ⊗ᴸ (c(𝒪) ⊗ᴸ Ω_{X/k}[0]) ≅ (ω_X^• ⊗ᴸ c(𝒪)) ⊗ᴸ Ω_{X/k}[0] ≅
   Ω_{X/k}[0]`, and taking `H⁰` gives `ω_X = H^{-1}(ω_X^•) ≅ Ω_{X/k}`.

The dimension bound of the tag's standing hypothesis is not used by clause (6): it follows from
smoothness of relative dimension one.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BRT](https://stacks.math.columbia.edu/tag/0BRT)
* [Stacks Project, Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality

open Stacks.AlgebraicGeometry.RegularIdealSheaf AlgebraicGeometry.Scheme.Modules KoszulRegular

/-- The normal sheaf of the diagonal of a morphism smooth of relative dimension one has rank
one. -/
theorem normalRank_diagonal_eq_one {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (hi : IsKoszulRegularImmersion (pullback.diagonal f)) (x : X) :
    normalRank (pullback.diagonal f) hi x = 1 := by
  have := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials f
  calc normalRank (pullback.diagonal f) hi x =
        fiberRank (Stacks.Divisors.normalSheaf (pullback.diagonal f)) x :=
        (@Stacks.Chow.fiberRank_eq_moduleRank X (Stacks.Divisors.normalSheaf (pullback.diagonal f))
          (isFiniteLocallyFree_normalSheaf _ hi) x).symm
    _ = fiberRank (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) x :=
        fiberRank_dualSheaf _
          (isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion _
            (isQuasiRegularImmersion_of_isH1RegularImmersion _
              (isH1RegularImmersion_of_isKoszulRegularImmersion _ hi))) x
    _ = fiberRank (Scheme.Hom.relativeDifferentials f) x :=
        fiberRank_eq_of_iso
          (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f).symm x
    _ = 1 := fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank _ 1 x

/-- For a morphism smooth of relative dimension one, the normal sheaf of the diagonal pairs with
the relative differentials to the structure sheaf: `𝒩 ⊗ Ω_{X/S} ≅ 𝒪_X`. -/
theorem nonempty_normalSheaf_tensor_relativeDifferentials_iso_unit {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] :
    Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
      (Stacks.Divisors.normalSheaf (pullback.diagonal f))).obj
        (Scheme.Hom.relativeDifferentials f) ≅ SheafOfModules.unit X.ringCatSheaf) := by
  let C : X.Modules := Stacks.Conormal.conormalSheaf (pullback.diagonal f)
  have hC : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} C 1 :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f)
      (Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials f)
  have := Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace C
  exact ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X.toRingedSpace.sheaf).obj _).mapIso
        (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f) ≪≫
      Stacks.SheafOfModules.Scheme.evaluationIso X C⟩

/-- In the derived category, `H^{-1}(K) ≅ H⁰(K[-1])`. -/
theorem nonempty_homologyFunctor_neg_one_iso_shift {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory C) :
    Nonempty ((DerivedCategory.homologyFunctor C (-1)).obj K ≅
      (DerivedCategory.homologyFunctor C 0).obj (K⟦(-1 : ℤ)⟧)) := by
  have h := (((DerivedCategory.homologyFunctor C 0).shiftIso (-1) 0 (-1)
    (by norm_num)).app K).symm
  rw [DerivedCategory.shift_homologyFunctor, Functor.comp_obj,
    DerivedCategory.shift_homologyFunctor] at h
  exact ⟨h⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **Clause (5) of [Stacks, Tag 0BS2]** for the constructed dualizing sheaf
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))`: for `X` proper of dimension at most one over `k` there are
isomorphisms `Hom(ℱ, ω_X) = Hom_k(H¹(X, ℱ), k)` for `ℱ` quasi-coherent, functorial in `ℱ`. The
isomorphisms are `Stacks.Duality.clauseFiveAddEquiv`, and their functoriality is
`Stacks.Duality.clauseFiveAddEquiv_naturality`. The isomorphisms as `k`-vector spaces are
`Stacks.Duality.exists_natural_linearEquiv_hom_dualizingSheafOverField`. -/
theorem exists_natural_addEquiv_hom_dualizingSheafOverField [IsProper f]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    ∃ e : ∀ F : X.Modules, F.IsQuasicoherent →
        ((F ⟶ dualizingSheafOverField f) ≃+ (cohomologyOverField k f F 1 →ₗ[k] k)),
      ∀ (F G : X.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (u : F ⟶ G)
        (φ : G ⟶ dualizingSheafOverField f),
        e F hF (u ≫ φ) = (e G hG φ).comp (cohomologyOverFieldMap k f u 1).hom :=
  ⟨clauseFiveAddEquiv f hdim, clauseFiveAddEquiv_naturality f hdim⟩

/-- **Clause (5) of [Stacks, Tag 0BS2]** for the constructed dualizing sheaf
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))`: for `X` proper of dimension at most one over `k` there are
isomorphisms of `k`-vector spaces `Hom(ℱ, ω_X) = Hom_k(H¹(X, ℱ), k)` for `ℱ` quasi-coherent,
functorial in `ℱ`. The `k`-structure on `Hom(ℱ, ω_X)` is the one `X.Modules` carries over `k`,
`AlgebraicGeometry.Scheme.linearOver f`. The isomorphisms are
`Stacks.Duality.clauseFiveLinearEquiv`, and their functoriality is
`Stacks.Duality.clauseFiveAddEquiv_naturality`. -/
@[stacks 0BS2 "clause (5): functorial isomorphisms of k-vector spaces Hom(F, ω_X) = \
Hom_k(H^1(X, F), k) for F quasi-coherent, at the constructed ω_X = H^{-1}(f^× O_{Spec k})"]
theorem exists_natural_linearEquiv_hom_dualizingSheafOverField [IsProper f]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    letI := Scheme.linearOver f
    ∃ e : ∀ F : X.Modules, F.IsQuasicoherent →
        ((F ⟶ dualizingSheafOverField f) ≃ₗ[k] (cohomologyOverField k f F 1 →ₗ[k] k)),
      ∀ (F G : X.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (u : F ⟶ G)
        (φ : G ⟶ dualizingSheafOverField f),
        e F hF (u ≫ φ) = (e G hG φ).comp (cohomologyOverFieldMap k f u 1).hom := by
  let := Scheme.linearOver f
  let : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linearOver f
  exact ⟨clauseFiveLinearEquiv f hdim, clauseFiveAddEquiv_naturality f hdim⟩

/-- For `f : X ⟶ Spec k` proper and smooth of relative dimension one, the twisted inverse image
of the structure sheaf along the diagonal is the normal sheaf in degree one: `c(𝒪) ≅ 𝒩[-1]`. -/
theorem nonempty_twistedInverseImage_diagonal_iso_normalSheaf [IsProper f]
    [SmoothOfRelativeDimension 1 f] :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
    haveI := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
    Nonempty (((twistedInverseImage (pullback.diagonal f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
        (DerivedPushforward.derivedStructureSheaf (pullback f f))).obj ≅
      (DerivedCategory.singleFunctor X.Modules 1).obj
        (Stacks.Divisors.normalSheaf (pullback.diagonal f))) := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := quasiSeparatedSpace_of_quasiSeparated f
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
  have := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
  have hi := isKoszulRegularImmersion_diagonal_of_smooth f
  obtain ⟨β₀⟩ := nonempty_normalExteriorComplex_iso_rightAdjoint_structureSheaf
    (pullback.diagonal f) hi _
    (twistedInverseImageAdjunction (pullback.diagonal f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f)))
  exact ⟨β₀.symm ≪≫ DerivedCategory.Q.mapIso
      (normalExteriorComplexIsoSingle (pullback.diagonal f) hi 1
        (normalRank_diagonal_eq_one f hi)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 1).app _).symm ≪≫
      (DerivedCategory.singleFunctor X.Modules 1).mapIso (exteriorGeneratorIsoSelf _).symm⟩

/-- **Clause (6) of [Stacks, Tag 0BS2]**: if `f : X ⟶ Spec k` is proper and smooth of relative
dimension one, the dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` is isomorphic to the sheaf of
relative differentials `Ω_{X/k}`.

The proof is that of [Stacks, Tag 0BRT] at `d = 1`; see the module documentation. -/
@[stacks 0BS2 "clause (6): ω_X ≅ Ω_{X/k} when X → Spec k is smooth of relative dimension 1, \
at the constructed ω_X = H^{-1}(f^× O_{Spec k})"]
theorem nonempty_dualizingSheafOverField_iso_relativeDifferentials [IsProper f]
    [SmoothOfRelativeDimension 1 f] :
    Nonempty (dualizingSheafOverField f ≅ Scheme.Hom.relativeDifferentials f) := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := quasiSeparatedSpace_of_quasiSeparated f
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
  have := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
  obtain ⟨α⟩ := nonempty_tensor_twistedInverseImage_diagonal_iso f
  obtain ⟨β⟩ := nonempty_twistedInverseImage_diagonal_iso_normalSheaf f
  obtain ⟨pairing⟩ := nonempty_normalSheaf_tensor_relativeDifferentials_iso_unit f
  let N : X.Modules := Stacks.Divisors.normalSheaf (pullback.diagonal f)
  let Ω : X.Modules := Scheme.Hom.relativeDifferentials f
  let Eo := ((twistedInverseImage (pullback.diagonal f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
        (DerivedPushforward.derivedStructureSheaf (pullback f f))).obj
  let ωo := (dualizingComplexOverField f).obj
  let Go := (DerivedCategory.singleFunctor X.Modules 0).obj Ω
  let U := (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)
  let T := derivedTensor X
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) Ω :=
    ⟨(Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f).exists_isFiniteLocallyFreeData⟩
  have γ : (T.obj Eo).obj Go ≅ U⟦(-1 : ℤ)⟧ :=
    (T.mapIso (β ≪≫ (((DerivedCategory.singleFunctors X.Modules).shiftIso
        (-1) 1 0 (by norm_num)).app N).symm)).app Go ≪≫
      (let := commShiftDerivedTensorFlipObj X Go
       ((T.flip.obj Go).commShiftIso (-1 : ℤ)).app _) ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso
        (derivedTensorSingleSingleIsoOfFlat N Ω (isFlat_of_isFiniteLocallyFree Ω) 0 ≪≫
          (DerivedCategory.singleFunctor X.Modules 0).mapIso pairing)
  have α' : (T.obj ωo).obj Eo ≅ U := (ObjectProperty.ι _).mapIso α
  let M : MonoidalCategory (DerivedCategory X.Modules) := Scheme.Modules.canonicalDerivedMonoidal X
  have hT : ∀ A B : DerivedCategory X.Modules, A ⊗ B = (T.obj A).obj B := fun A B => by
    change _ = ((derivedTensor X).obj A).obj B
    rw [← curriedTensor_canonicalDerivedMonoidal_eq]
    rfl
  have hU : 𝟙_ (DerivedCategory X.Modules) = U := tensorUnit_canonicalDerivedMonoidal_eq X
  have sh : (T.obj ωo).obj (U⟦(-1 : ℤ)⟧) ≅ ωo⟦(-1 : ℤ)⟧ :=
    let hcs : (T.obj ωo).CommShift ℤ :=
      (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).commShift_right ωo
    (Functor.commShiftIso (self := hcs) (T.obj ωo) (-1 : ℤ)).app U ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso (eqToIso (by rw [← hT, ← hU]) ≪≫ ρ_ ωo)
  have e : ωo⟦(-1 : ℤ)⟧ ≅ Go :=
    sh.symm ≪≫ (T.obj ωo).mapIso γ.symm ≪≫ eqToIso (by rw [← hT, ← hT]) ≪≫
      (α_ ωo Eo Go).symm ≪≫ eqToIso (by
        rw [hT ωo Eo]
        exact hT _ _) ≪≫
      (T.flip.obj Go).mapIso α' ≪≫ eqToIso (by
        change (T.obj U).obj Go = 𝟙_ (DerivedCategory X.Modules) ⊗ Go
        rw [hU, hT]) ≪≫ λ_ Go
  obtain ⟨h1⟩ := nonempty_homologyFunctor_neg_one_iso_shift ωo
  exact ⟨h1 ≪≫ (DerivedCategory.homologyFunctor X.Modules 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app Ω⟩

end Stacks.Duality
