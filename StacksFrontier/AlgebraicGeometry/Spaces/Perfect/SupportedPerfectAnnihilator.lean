module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedSheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompactQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.QcqsUnitCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.EtaleAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.UnitLeftIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsTriangulatedSubcategory
public import StacksFrontier.CategoryTheory.Triangulated.LocallySmallCompactFactorization
import StacksCore.Tactic.StacksAttribute

/-!
# A perfect complex annihilating a morphism into an object supported on a closed subset

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, `T ⊆ |X|` a
closed subset with quasi-compact complement `U`, and `α : P ⟶ E` a morphism of `D_QCoh(𝒪_X)` with
`E` supported on `T`, where either `P` is perfect, or `P` is pseudo-coherent and `E` is bounded
below. Stacks 0AEE says that there is a perfect complex `I` with a map `I ⟶ 𝒪_X[0]` such that
`I ⊗^L P ⟶ 𝒪_X[0] ⊗^L P = P ⟶ E` is zero and `I|_U ⟶ 𝒪_U[0]` is an isomorphism.

## The proof

This is the source's proof. `K = R𝓗om(P, E)` lies in `D_QCoh(𝒪_X)` (Stacks 0A8A) and is supported
on `T`: for `P` perfect, `K ≅ P^∨ ⊗^L E` (Stacks 08JJ) and its restriction to `U` is
`P^∨|_U ⊗^L E|_U = 0` (Stacks 07A4); for `P` pseudo-coherent and `E` with no cohomology below `b`,
the `n`-th cohomology sheaf of `K` is that of `R𝓗om(Q, E)` for a perfect `Q ⟶ P` approximating
`P` above degree `b - n - 1` (Stacks 08HP), and the perfect case applies to `Q`. By the tensor–Hom
adjunction (Stacks 08J8) `α` is a morphism `α' : 𝒪_X[0] ⟶ K`.

Let `G` be a perfect generator of `D_{QCoh,T}(𝒪_X)` (Stacks 0AEC). It is compact in `D_QCoh(𝒪_X)`
(Stacks 09M8), and `D_{QCoh,T}(𝒪_X)` is the kernel of the restriction `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_U)`,
an exact left adjoint. The categorical core
`CategoryTheory.Pretriangulated.exists_distTriang_comp_eq_zero_of_isZero_of_locallySmall` (Stacks
09SN, 094A and 09SP, through Neeman's factorization) applied to the compact object `𝒪_X[0]` gives a
distinguished triangle `I ⟶ 𝒪_X[0] ⟶ Q ⟶ I[1]` with `Q` compact and zero on `U` and `I ⟶ K` zero.
Then `I` is compact, hence perfect (Stacks 09M8), `I|_U ⟶ 𝒪_U[0]` is an isomorphism, and
`I ⊗^L P ⟶ E` is zero, being the transpose of `I ⟶ K`.

## Main results

* `AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedSheafHom_of_isPerfect` and
  `AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedSheafHom_of_isPseudoCoherent`:
  `R𝓗om(P, E)` is supported on `T`.
* `AlgebraicGeometry.Space.exists_isPerfect_comp_tensor_eq_zero_of_cohomologySupportedOn`:
  **Stacks 0AEE**.

## References

* [Stacks Project, Tag 0AEE](https://stacks.math.columbia.edu/tag/0AEE)
* [Stacks Project, Tag 0A8A](https://stacks.math.columbia.edu/tag/0A8A)
* [Stacks Project, Tag 0AEC](https://stacks.math.columbia.edu/tag/0AEC)
* [Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
* [Stacks Project, Tag 094A](https://stacks.math.columbia.edu/tag/094A)
* [Stacks Project, Tag 09SP](https://stacks.math.columbia.edu/tag/09SP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] pointTopology

/-- **The left unit constraint of the derived tensor product of an algebraic space**:
`𝒪_X[0] ⊗^L P ≅ P`. -/
def smallEtaleDerivedTensorUnitLeftIso (X : AlgebraicSpaces B S hS)
    (P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (((smallEtaleDerivedTensorProduct B S hS X).tensor).obj (unitDerived X)).obj P ≅ P :=
  (smallEtaleDerivedTensorProduct B S hS X).unitLeftIso P

/-- Restricting to the open subspace with points `Tᶜ` kills `E` iff `E` is supported on `T`. -/
private theorem isZero_etaleModulePullback_openSubspaceHom_iff (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsZero ((etaleModulePullback.{u, u} B S hS
        (openSubspaceHom B S hS
          ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1
          ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).2)
        (isEtale_openSubspaceHom B S hS _ _)).mapDerivedCategory.obj E) ↔
      CohomologySupportedOn B S hS X.1 X.2 T E := by
  let G := (openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
  have hrange : Set.range (pointsMap B S hS (openSubspaceSpace B S hS G.1 G.2).1
      (openSubspaceHom B S hS G.1 G.2).hom) = Tᶜ :=
    range_openSubspacesOrderIso_symm B S hS X.1 X.2 T hT
  refine ⟨fun h => ?_, fun h => isZero_etaleModulePullback_mapDerivedCategory_of_disjoint B S hS _ _
    T E h (by rw [hrange]; exact disjoint_compl_left)⟩
  have h' := cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback B S hS _ _ _ h
  rwa [hrange, compl_compl] at h'

/-- **`R𝓗om(P, E)` is supported on `T` when `P` is perfect and `E` is supported on `T`.** -/
theorem cohomologySupportedOn_smallEtaleDerivedSheafHom_of_isPerfect (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (P E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P)
    (hE : CohomologySupportedOn B S hS X.1 X.2 T E) :
    CohomologySupportedOn B S hS X.1 X.2 T
      (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E) := by
  let G := (openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
  let j := openSubspaceHom B S hS G.1 G.2
  have hj : IsEtale B S hS j.hom := isEtale_openSubspaceHom B S hS G.1 G.2
  have hiff := isZero_etaleModulePullback_openSubspaceHom_iff B S hS X T hT
  let Lj := smallEtaleDerivedModulePullback B S hS j
  let ej := smallEtaleDerivedModulePullbackIsoEtale B S hS j hj
  have hE0 : IsZero (Lj.obj E) :=
    ((hiff E).2 hE).of_iso (ej.app E)
  have hz : ∀ (A Z : DerivedCategory (Modules.{u, u} B S hS (openSubspaceSpace B S hS G.1 G.2).1
      (openSubspaceSpace B S hS G.1 G.2).2)), IsZero Z →
      IsZero (((smallEtaleDerivedTensorProduct B S hS (openSubspaceSpace B S hS G.1 G.2)).tensor.obj
        A).obj Z) := fun A Z hZ => Functor.map_isZero _ hZ
  have hT0 : IsZero (Lj.obj (((smallEtaleDerivedTensor B S hS X).obj
      (smallEtaleDerivedDual B S hS X P)).obj E)) :=
    IsZero.of_iso (hz _ _ hE0) ((smallEtaleDerivedPullbackTensorIso j).app
      (smallEtaleDerivedDual B S hS X P, E))
  have hK0 : IsZero ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj
      (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E)) :=
    hT0.of_iso ((ej.app _).symm ≪≫
      Lj.mapIso (smallEtaleDerivedSheafHomIsoTensorDual B S hS X P E hP))
  exact (hiff _).1 hK0

/-- **`R𝓗om(P, E)` is supported on `T` when `P` is pseudo-coherent and `E` is bounded below and
supported on `T`**, on a quasi-compact and quasi-separated algebraic space: here `E` has no
cohomology below `b`. -/
theorem cohomologySupportedOn_smallEtaleDerivedSheafHom_of_isPseudoCoherent
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (P E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hPq : QcohDerived B S hS X P)
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent P)
    (hE : CohomologySupportedOn B S hS X.1 X.2 T E) (b : ℤ) (hb : E.IsGE b) :
    CohomologySupportedOn B S hS X.1 X.2 T
      (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E) := by
  intro n
  let G := (openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Set.univᶜ, isClosed_univ.isOpen_compl⟩
  have hGqc : IsQuasiCompactSpace B S hS G.1.toFunctor :=
    isQuasiCompactSpace_of_isCompact_range B S hS X.2 G.2 (by
      rw [range_openSubspacesOrderIso_symm B S hS X.1 X.2 Set.univ isClosed_univ,
        Set.compl_univ]
      exact isCompact_empty)
  have hG : IsQuasiCompact B S hS G.1.ι :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal X.2 hXqs hGqc G.1.ι
  obtain ⟨r, hr⟩ := approximationByPerfectComplexes_of_qcqs B S hS B.contains_terminal X.1 X.2
    hXqc hXqs Set.univ isClosed_univ hG
  have hPm : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom P (b - n - 1 - r) := by
    obtain ⟨K, hK, e⟩ := hP
    exact ⟨K, hK (b - n - 1 - r), e⟩
  obtain ⟨Q, hQ, -, a, hiso, hepi⟩ := hr ⟨P, hPq⟩ (b - n - 1) hPm
    (fun _ _ => Set.subset_univ _)
  have hn := isIso_homologyMap_smallEtaleDerivedSheafHom_map_of_approximation X a
    (b - n - 1) hiso hepi E b n hb (by omega)
  exact (supportOfSheaf_eq_of_iso B S hS X (@asIso _ _ _ _ _ hn)).le.trans
    (cohomologySupportedOn_smallEtaleDerivedSheafHom_of_isPerfect B S hS X T hT Q E hQ hE n)

/-- **Stacks 0AEE.** Let `S` be a scheme, `X` a quasi-compact and quasi-separated algebraic space
over `S`, and `T ⊆ |X|` a closed subset whose complement `U` is quasi-compact. Let `α : P ⟶ E` be a
morphism of `D_QCoh(𝒪_X)` with `E` supported on `T`, where either (1) `P` is perfect, or (2) `P`
is pseudo-coherent and `E` is bounded below. Then there are a perfect complex `I` of
`𝒪_X`-modules and a map `u : I ⟶ 𝒪_X[0]` such that `u|_U : I|_U ⟶ 𝒪_U[0]` is an isomorphism and
`I ⊗^L P ⟶ 𝒪_X[0] ⊗^L P ≅ P ⟶ E` is zero.

`U` is the open subspace of `X` with `|U| = |X| ∖ T`, and `(-)|_U` the restriction along its
inclusion; `E` supported on `T` means that every cohomology sheaf of `E` is supported on `T`
(`AlgebraicGeometry.Space.CohomologySupportedOn`, Stacks 08GF); `E` bounded below means that its
cohomology sheaves vanish in all sufficiently negative degrees. -/
@[stacks 0AEE]
theorem exists_isPerfect_comp_tensor_eq_zero_of_cohomologySupportedOn
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    {P E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    (hPq : QcohDerived B S hS X P) (hEq : QcohDerived B S hS X E) (α : P ⟶ E)
    (hEs : CohomologySupportedOn B S hS X.1 X.2 T E)
    (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P ∨
      ((smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent P ∧
        DerivedCategoryB.IsBoundedBelow E)) :
    ∃ (I : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (u : I ⟶ unitDerived X),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect I ∧
      IsIso ((etaleModulePullback.{u, u} B S hS
          (openSubspaceHom B S hS
            ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1
            ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).2)
          (isEtale_openSubspaceHom B S hS _ _)).mapDerivedCategory.map u) ∧
      ((smallEtaleDerivedTensorProduct B S hS X).tensor.map u).app P ≫
        (smallEtaleDerivedTensorUnitLeftIso B S hS X P).hom ≫ α = 0 := by
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X.1 X.2
  let G := (openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
  let j := openSubspaceHom B S hS G.1 G.2
  have hj : IsEtale B S hS j.hom := isEtale_openSubspaceHom B S hS G.1 G.2
  have hiff := isZero_etaleModulePullback_openSubspaceHom_iff B S hS X T hT
  have hGqc : IsQuasiCompactSpace B S hS G.1.toFunctor :=
    isQuasiCompactSpace_of_isCompact_range B S hS X.2 G.2 (by
      rw [range_openSubspacesOrderIso_symm B S hS X.1 X.2 T hT]; exact hTc)
  have hjqc : IsQuasiCompact B S hS j.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal X.2 hXqs hGqc G.1.ι
  have hjqs : IsQuasiSeparated B S hS j.hom :=
    isQuasiSeparated_of_mono B S hS G.1.ι inferInstance
  let L := quasicoherentDerivedEtalePullback B S hS j hj
  have : L.IsLeftAdjoint :=
    (quasicoherentDerivedEtaleAdjunction B S hS j hj hjqc hjqs).isLeftAdjoint
  let ι := ObjectProperty.ι (QcohDerived B S hS X)
  have hι : ι.FullyFaithful := ObjectProperty.fullyFaithfulι _
  obtain ⟨P₀, hP₀, hP₀q, hP₀s, hdet⟩ :=
    exists_isPerfect_generator_of_supported B S hS X hXqc hXqs T hT hTc
  let G₀ : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 := ⟨P₀, hP₀q⟩
  have hG₀c : IsCompactObject.{u} G₀ := isCompactObject_of_isPerfect X hXqc hXqs G₀ hP₀
  have hLG₀ : IsZero (L.obj G₀) :=
    IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ ((hiff P₀).2 hP₀s)
  have hdet' : ∀ E' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2, IsZero (L.obj E') →
      (∀ (n : ℤ) (g : G₀⟦n⟧ ⟶ E'), g = 0) → IsZero E' := by
    intro E' hE' hG
    refine IsZero.of_full_of_faithful_of_isZero ι _ ((hdet E'
      ((hiff E'.obj).1 ((ObjectProperty.ι _).map_isZero hE'))).2 fun n g => ?_)
    have h0 := hG n (hι.preimage ((ι.commShiftIso n).hom.app G₀ ≫ g))
    have h1 : (ι.commShiftIso n).hom.app G₀ ≫ g = 0 := by
      rw [← hι.map_preimage ((ι.commShiftIso n).hom.app G₀ ≫ g), h0, Functor.map_zero]
    rwa [← cancel_epi ((ι.commShiftIso n).hom.app G₀), comp_zero]
  let K : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
    ⟨((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj E, by
      rcases h with hP | ⟨hP, hb⟩
      · exact qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect X P E hP hEq
      · exact qcohDerived_smallEtaleDerivedSheafHom_of_isPseudoCoherent X P E hP
          ⟨hb, hEq⟩⟩
  have hKs : CohomologySupportedOn B S hS X.1 X.2 T K.obj := by
    rcases h with hP | ⟨hP, ⟨b, hb⟩⟩
    · exact cohomologySupportedOn_smallEtaleDerivedSheafHom_of_isPerfect B S hS X T hT P E hP hEs
    · exact cohomologySupportedOn_smallEtaleDerivedSheafHom_of_isPseudoCoherent B S hS X hXqc
        hXqs T hT P E hPq hP hEs b ((DerivedCategory.isGE_iff E b).2 fun i hi => hb i hi)
  have hLK : IsZero (L.obj K) :=
    IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ ((hiff K.obj).2 hKs)
  let adj := smallEtaleDerivedTensorSheafHomAdjunction B S hS X P
  let α₀ : unitDerived X ⟶ K.obj :=
    adj.homEquiv _ _ ((smallEtaleDerivedTensorUnitLeftIso B S hS X P).hom ≫ α)
  let c : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 := unitQuasicoherent X.2
  have hc : IsCompactObject.{u} c :=
    isCompactObject_unitQuasicoherent_of_qcqs B.contains_terminal X hXqc hXqs
  obtain ⟨I, Z, u, v, w, hTr, hZc, hZL, hu⟩ :=
    exists_distTriang_comp_eq_zero_of_isZero_of_locallySmall L G₀ hG₀c hLG₀ hdet' hc hLK
      (ObjectProperty.homMk α₀ : c ⟶ K)
  have hIc : IsCompactObject.{u} I := by
    have h1 : IsCompactObject.{u} (I⟦(1 : ℤ)⟧) :=
      isCompactObject_obj₃ _ (rot_of_distTriang _ hTr) hc hZc
    exact isCompactObject_of_iso ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).app I).symm
      (isCompactObject_shift h1 (-1))
  refine ⟨I.obj, u.hom, isPerfect_of_isCompactObject X hXqs I hIc, ?_, ?_⟩
  · have hLu : IsIso (L.map u) :=
      (Triangle.isZero₃_iff_isIso₁ _ (L.map_distinguished _ hTr)).1 hZL
    exact (inferInstance : IsIso ((ObjectProperty.ι _).map (L.map u)))
  · have h0 : u.hom ≫ α₀ = (0 : I.obj ⟶ I.obj) ≫ (0 : I.obj ⟶ K.obj) := by
      rw [comp_zero]
      exact congrArg (fun f => f.hom) hu
    have hF0 : ((smallEtaleDerivedTensorProduct B S hS X).tensor.flip.obj P).map
        (0 : I.obj ⟶ I.obj) = 0 := by
      let := (smallEtaleDerivedTensorProduct B S hS X).commShift₂.commShiftFlipObj P
      have := (smallEtaleDerivedTensorProduct B S hS X).exact_left P
      exact Functor.map_zero _ _ _
    have hα : (adj.homEquiv _ _).symm α₀ =
        (smallEtaleDerivedTensorUnitLeftIso B S hS X P).hom ≫ α :=
      Equiv.symm_apply_apply _ _
    rw [← hα]
    exact (adj.homEquiv_naturality_left_symm u.hom α₀).symm.trans <|
      (congrArg (adj.homEquiv _ _).symm h0).trans <|
        (adj.homEquiv_naturality_left_symm _ _).trans <|
          (congrArg (· ≫ (adj.homEquiv _ _).symm (0 : I.obj ⟶ K.obj)) hF0).trans zero_comp

end AlgebraicGeometry.Space

end
