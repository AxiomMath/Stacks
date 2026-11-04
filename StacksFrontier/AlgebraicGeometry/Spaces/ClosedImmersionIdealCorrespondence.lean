module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspaceAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact

/-!
# Closed immersions of algebraic spaces and quasi-coherent sheaves of ideals

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Stacks 03MB
asserts:

* for every closed immersion `i : Z ⟶ X` the direct image `i_*𝒪_Z` is a quasi-coherent
  `𝒪_X`-module, the map `i♯ : 𝒪_X ⟶ i_*𝒪_Z` is surjective, and its kernel is a quasi-coherent
  sheaf of ideals;
* the rule `Z ↦ Ker(𝒪_X ⟶ i_*𝒪_Z)` is an inclusion-reversing bijection from the closed subspaces
  of `X` onto the quasi-coherent sheaves of ideals of `𝒪_X`;
* if `Z` corresponds to `𝓘`, a morphism `h : Y ⟶ X` of algebraic spaces factors through `Z`
  exactly when `h^*𝓘 ⟶ h^*𝒪_X = 𝒪_Y` is zero.

`AlgebraicGeometry.Space.closedImmersion_quasicoherentIdeal_correspondence` states all of it.

The first two assertions are assembled from the library: quasi-coherence of `i_*𝒪_Z` is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_structureSheafPushforward`, surjectivity of `i♯`
is `AlgebraicGeometry.Space.isLocallySurjective_structureSharp`, the kernel is the kernel ideal
sheaf of `i` (`AlgebraicGeometry.Space.ker_pushforwardStructureProjection`), quasi-coherent
because a closed immersion is quasi-compact, and the bijection is the defining ideal sheaf of
`AlgebraicGeometry.Space.definingIdealSheaf` together with
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite`.

What is proved here is the factorization criterion with the inverse image of modules of
Stacks 03LU.  It has two halves.

* *Factorization is containment in the kernel of `h♯`*: `h` factors through `Z` exactly when the
  defining ideal sheaf of `Z` is contained in the kernel of `h♯ : 𝒪_X ⟶ h_*𝒪_Y`
  (`AlgebraicGeometry.Space.exists_comp_eq_iff_definingIdealSheaf_le_kernelIdealSheaf`).  One
  direction is `AlgebraicGeometry.Space.definingIdealSheaf_le_kernelIdealSheaf_of_comp_eq`; the
  other is the affine-chart criterion
  `AlgebraicGeometry.Space.exists_comp_eq_iff_forall_isAffine_definingIdealAt_le`, whose
  hypothesis a function killed by `h♯` satisfies by
  `AlgebraicGeometry.Space.kernelIdealSheaf_le_ker_of_lift`.
* *Vanishing after pullback is vanishing of `h♯`*: for a morphism `φ : 𝓜 ⟶ 𝒪_X`, the composite
  `h^*𝓜 ⟶ h^*𝒪_X ≅ 𝒪_Y` is zero exactly when `φ ≫ h♯` is
  (`AlgebraicGeometry.Space.modulePullback_map_comp_modulePullbackUnitIso_hom_eq_zero_iff`).
  The transpose of a composite along the adjunction `h^* ⊣ h_*` of Stacks 03D7 is the composite
  with the transpose, and the transpose of the identification `h^*𝒪_X ≅ 𝒪_Y` is the structure
  map `𝒪_X ⟶ h_*𝒪_Y` (`AlgebraicGeometry.Space.homEquiv_modulePullbackUnitIso_hom`).

## Main results

* `AlgebraicGeometry.Space.homEquiv_modulePullbackUnitIso_hom`: the transpose of
  `h^*𝒪_X ≅ 𝒪_Y` along `h^* ⊣ h_*` is the structure map `𝒪_X ⟶ h_*𝒪_Y`.
* `AlgebraicGeometry.Space.modulePullback_map_comp_modulePullbackUnitIso_hom_eq_zero_iff` and its
  pointwise form `..._eq_zero_iff_forall`.
* `AlgebraicGeometry.Space.exists_comp_eq_iff_definingIdealSheaf_le_kernelIdealSheaf` and
  `AlgebraicGeometry.Space.exists_comp_eq_iff_modulePullback_map_comp_eq_zero`: the factorization
  criterion, in the kernel form and in the form of Stacks 03MB.
* `AlgebraicGeometry.Space.closedImmersion_quasicoherentIdeal_correspondence`: **Stacks 03MB.**

## Implementation notes

The transpose of `h^*𝒪_X ≅ 𝒪_Y` is identified through the chartwise universal property of the
direct image (`AlgebraicGeometry.Space.modulePushforwardHomEquiv`): both sides are linear maps of
sections along `h`, semilinear over pullback of regular functions, so each is determined by its
value on the unit function, and both send it to the unit function.  For the transpose that is
`AlgebraicGeometry.Space.modulePullbackUnitIso_hom_val_app_modulePullbackChartSection`; for the
structure map it is `AlgebraicGeometry.Space.moduleChartProjection_app_structureSharp`.

Zero morphisms into `i_*𝒪_Z` are compared through composites rather than written with a
`⟶`-typed ascription: instance search does not find the zero morphism of an explicitly written
hom type into `AlgebraicGeometry.Space.structureSheafPushforward`, while the type of a composite
carries the category instance it needs.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transpose

variable {X Y : AlgebraicSpaces B S hS} (h : Y ⟶ X)

/-- **The transpose of `h^*𝒪_X ≅ 𝒪_Y` is the structure map.**  For a morphism `h : Y ⟶ X` of
algebraic spaces, the identification `h^*𝒪_X ≅ 𝒪_Y` of Stacks 03LU corresponds, under the
adjunction `h^* ⊣ h_*` of Stacks 03D7, to the structure map `𝒪_X ⟶ h_*𝒪_Y` of `h` read as a
map of `𝒪_X`-modules. -/
theorem homEquiv_modulePullbackUnitIso_hom :
    (modulePullbackAdjunction B S hS h).homEquiv _ _ (modulePullbackUnitIso B S hS h).hom =
      pushforwardStructureProjection B S hS h := by
  apply (modulePushforwardHomEquiv B S hS h _ _).injective
  refine ModuleFMap.ext B S hS (funext fun d => funext fun s => ?_)
  let ξ := modulePullbackHomFMap B S hS h
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (SheafOfModules.unit (structureRingSheaf B S hS Y)) (modulePullbackUnitIso B S hS h).hom
  have h1 : ξ.app d (1 : (structureRingSheaf B S hS X).obj.obj (op d.V)) =
      (1 : (structureRingSheaf B S hS Y).obj.obj (op d.U)) :=
    (modulePullbackHomFMap_app B S hS h _ _ _ d _).trans
      ((congrArg (fun z => (modulePullbackUnitIso B S hS h).hom.val.app (op d.U) z)
        (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS h _ d _)).trans
      (modulePullbackUnitIso_hom_val_app_modulePullbackChartSection B S hS h d))
  let r : (structureRingSheaf B S hS X).obj.obj (op d.V) := s
  let one : (SheafOfModules.unit (structureRingSheaf B S hS X)).val.obj (op d.V) :=
    (1 : (structureRingSheaf B S hS X).obj.obj (op d.V))
  have hr : r • one = s := mul_one r
  have h2 : ξ.app d s = chartDiagramPullback B S hS h d r :=
    (congrArg (ξ.app d) hr.symm).trans ((ξ.map_smul d r one).trans
      ((congrArg (fun z => chartDiagramPullback B S hS h d r • z) h1).trans
        (mul_one ((chartDiagramPullback B S hS h d).hom r))))
  exact h2.trans ((moduleChartProjection_app_structureSharp B S hS h d.V _ r).trans
    (chartPullback_indexOfChartDiagram B S hS h d r)).symm

/-- **A map into `𝒪_X` vanishes after pullback exactly when it is killed by `h♯`.**  For a
morphism `h : Y ⟶ X` of algebraic spaces and a morphism `φ : 𝓜 ⟶ 𝒪_X` of `𝒪_X`-modules, the
composite `h^*𝓜 ⟶ h^*𝒪_X ≅ 𝒪_Y` is zero exactly when `φ` followed by `𝒪_X ⟶ h_*𝒪_Y` is. -/
theorem modulePullback_map_comp_modulePullbackUnitIso_hom_eq_zero_iff
    {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ SheafOfModules.unit (structureRingSheaf B S hS X)) :
    (modulePullback B S hS h).map φ ≫ (modulePullbackUnitIso B S hS h).hom = 0 ↔
      φ ≫ pushforwardStructureProjection B S hS h = 0 := by
  let N : Modules.{u, u} B S hS Y.1 Y.2 := SheafOfModules.unit (structureRingSheaf B S hS Y)
  let e := (modulePullbackAdjunction B S hS h).homEquiv M N
  have h0 : (modulePullbackAdjunction B S hS h).homEquiv M N 0 = 0 := by
    rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  have hn := (Adjunction.homEquiv_naturality_left (modulePullbackAdjunction B S hS h) φ
    (modulePullbackUnitIso B S hS h).hom).trans
    (congrArg (fun t => φ ≫ t) (homEquiv_modulePullbackUnitIso_hom B S hS h))
  exact ⟨fun H => hn.symm.trans ((congrArg e H).trans h0),
    fun H => e.injective (hn.trans (H.trans h0.symm))⟩

/-- **A map into `𝒪_X` vanishes after pullback exactly when its values are killed by `h♯`**, on
the sections over every étale chart of `X`. -/
theorem modulePullback_map_comp_modulePullbackUnitIso_hom_eq_zero_iff_forall
    {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ SheafOfModules.unit (structureRingSheaf B S hS X)) :
    (modulePullback B S hS h).map φ ≫ (modulePullbackUnitIso B S hS h).hom = 0 ↔
      ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : M.val.obj U),
        (structureSharp B S hS h).hom.app U (φ.val.app U x) = 0 := by
  rw [modulePullback_map_comp_modulePullbackUnitIso_hom_eq_zero_iff]
  exact ⟨fun H U x =>
    (congrArg (fun m : M ⟶ structureSheafPushforward B S hS h => m.val.app U x) H).trans rfl,
    fun H => by ext U x; exact H U x⟩

end Transpose

section Factorization

variable (X : AlgebraicSpaces B S hS)

/-- **A morphism factors through a closed subspace exactly when the defining ideal is killed
by its structure map.**  A morphism `h : Y ⟶ X` of algebraic spaces factors through a closed
subspace `Z ⊆ X` exactly when the defining ideal sheaf of `Z` is contained in the kernel of
`h♯ : 𝒪_X ⟶ h_*𝒪_Y`. -/
theorem exists_comp_eq_iff_definingIdealSheaf_le_kernelIdealSheaf
    (Z : ClosedSubspaces B S hS X.1) {Y : AlgebraicSpaces B S hS} (h : Y ⟶ X) :
    (∃ g : Y ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
        g ≫ ObjectProperty.homMk Z.1.ι = h) ↔
      definingIdealSheaf B S hS X Z ≤ kernelIdealSheaf B S hS h := by
  refine ⟨fun ⟨g, hg⟩ => definingIdealSheaf_le_kernelIdealSheaf_of_comp_eq B S hS h Z g hg,
    fun hle => (exists_comp_eq_iff_forall_isAffine_definingIdealAt_le B S hS X Y Z h).2 ?_⟩
  intro U _ a k y hy s hs
  rw [← definingIdealSheaf_obj] at hs
  exact kernelIdealSheaf_le_ker_of_lift B S hS h U k y hy (hle _ hs)

/-- **The factorization criterion of Stacks 03MB.**  A morphism `h : Y ⟶ X` of algebraic spaces
factors through a closed subspace `Z ⊆ X` with defining ideal sheaf `𝓘` exactly when the map
`h^*𝓘 ⟶ h^*𝒪_X ≅ 𝒪_Y` is zero. -/
theorem exists_comp_eq_iff_modulePullback_map_comp_eq_zero
    (Z : ClosedSubspaces B S hS X.1) {Y : AlgebraicSpaces B S hS} (h : Y ⟶ X) :
    (∃ g : Y ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
        g ≫ ObjectProperty.homMk Z.1.ι = h) ↔
      (modulePullback B S hS h).map (definingIdealSheaf B S hS X Z).ι ≫
        (modulePullbackUnitIso B S hS h).hom = 0 := by
  refine (exists_comp_eq_iff_definingIdealSheaf_le_kernelIdealSheaf B S hS X Z h).trans
    (Iff.trans ?_ (modulePullback_map_comp_modulePullbackUnitIso_hom_eq_zero_iff_forall B S hS h
      (M := (definingIdealSheaf B S hS X Z).toSheafOfModules)
      (definingIdealSheaf B S hS X Z).ι).symm)
  exact ⟨fun hle U x => hle U x.2, fun H U s hs => H U ⟨s, hs⟩⟩

end Factorization

section Tag03MB

variable (X : AlgebraicSpaces B S hS)

/-- **Stacks 03MB.**  Let `X` be an algebraic space over `S`.

1. For every closed immersion `i : Z ⟶ X` of algebraic spaces the direct image `i_*𝒪_Z` is a
   quasi-coherent `𝒪_X`-module, the map `i♯ : 𝒪_X ⟶ i_*𝒪_Z` is surjective — locally surjective as
   a map of sheaves of rings, and an epimorphism of `𝒪_X`-modules — and its kernel is a
   quasi-coherent sheaf of ideals.
2. The rule `Z ↦ 𝓘_Z = Ker(𝒪_X ⟶ i_*𝒪_Z)`, with `i` the inclusion of `Z`, is an
   inclusion-reversing bijection from the closed subspaces of `X` onto the quasi-coherent sheaves
   of ideals of `𝒪_X`.
3. If `Z` corresponds to `𝓘 = 𝓘_Z`, a morphism `h : Y ⟶ X` of algebraic spaces factors through
   `Z` if and only if the map `h^*𝓘 ⟶ h^*𝒪_X = 𝒪_Y` is zero. -/
@[stacks 03MB]
theorem closedImmersion_quasicoherentIdeal_correspondence :
    (∀ {Z : AlgebraicSpaces B S hS} (i : Z ⟶ X), IsClosedImmersion B S hS i.hom →
      (structureSheafPushforward B S hS i).IsQuasicoherentOnSite ∧
        Sheaf.IsLocallySurjective (structureSharp B S hS i) ∧
        Epi (pushforwardStructureProjection B S hS i) ∧
        (SheafOfModules.Submodule.ker
          (pushforwardStructureProjection B S hS i)).toSheafOfModules.IsQuasicoherentOnSite) ∧
    (∀ Z : ClosedSubspaces B S hS X.1,
      definingIdealSheaf B S hS X Z = SheafOfModules.Submodule.ker
        (pushforwardStructureProjection B S hS (ObjectProperty.homMk Z.1.ι :
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X))) ∧
    Set.BijOn (definingIdealSheaf B S hS X) Set.univ
      {I | I.toSheafOfModules.IsQuasicoherentOnSite} ∧
    (∀ Z W : ClosedSubspaces B S hS X.1,
      Z ≤ W ↔ definingIdealSheaf B S hS X W ≤ definingIdealSheaf B S hS X Z) ∧
    ∀ (Z : ClosedSubspaces B S hS X.1) {Y : AlgebraicSpaces B S hS} (h : Y ⟶ X),
      (∃ g : Y ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
          g ≫ ObjectProperty.homMk Z.1.ι = h) ↔
        (modulePullback B S hS h).map (definingIdealSheaf B S hS X Z).ι ≫
          (modulePullbackUnitIso B S hS h).hom = 0 := by
  refine ⟨fun i hi => ⟨isQuasicoherentOnSite_structureSheafPushforward B S hS i hi,
      isLocallySurjective_structureSharp B S hS i hi,
      epi_pushforwardStructureProjection B S hS i hi,
      ?_⟩, fun Z => (ker_pushforwardStructureProjection B S hS _).symm,
    ⟨fun Z _ => isQuasicoherentOnSite_definingIdealSheaf B S hS X Z,
      fun Z _ W _ hZW => definingIdealSheaf_injective B S hS X hZW,
      fun I hI => (exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X I hI).imp
        fun Z hZ => ⟨Set.mem_univ Z, hZ⟩⟩,
    fun Z W => ⟨fun hZW => definingIdealSheaf_antitone B S hS X Z W (Subtype.coe_le_coe.2 hZW),
      fun hle => Subtype.coe_le_coe.1 (le_of_definingIdealSheaf_le B S hS X Z W hle)⟩,
    fun Z _ h => exists_comp_eq_iff_modulePullback_map_comp_eq_zero B S hS X Z h⟩
  rw [ker_pushforwardStructureProjection]
  exact isQuasicoherentOnSite_kernelIdealSheaf B S hS i
    (isQuasiCompact_of_isClosedImmersion' B S hS hi)

end Tag03MB

end AlgebraicGeometry.Space
