module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineDirectImageFree
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ProductStructureSheafNotQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SmallModelDerivedSheafHomFree
import StacksCore.Tactic.StacksAttribute

/-!
# The coherator cannot be dropped from the trace comparison on algebraic spaces

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated algebraic spaces and `a` the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. [Stacks, Tag 0E58] asserts that for
`L ∈ D_QCoh(𝒪_X)` and `K ∈ D_QCoh(𝒪_Y)` the map of [Stacks, Tag 0E57]

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`

becomes an isomorphism after applying the coherator `DQ_Y`. [Stacks, Tag 0GG3] says that it is
not an isomorphism without `DQ_Y`, referring to the counterexample of [Stacks, Tag 0GEU]: this
file is that counterexample on algebraic spaces.

Take an affine scheme `S` of the big fppf site, `Y = h_S`, `X = h_{𝔸¹_S}`, `f` the structure
morphism, `L = 𝒪_X` and `K = 𝒪_Y`. Then:

1. `X` and `Y` are quasi-compact and quasi-separated, and `Rf_*` preserves `D_QCoh`
   (`f` is affine), so the right adjoint `a` of the restriction makes sense;
2. the left hand side `Rf_*R𝓗om_{𝒪_X}(𝒪_X, M)` lies in `D_QCoh(𝒪_Y)` for every
   `M ∈ D_QCoh(𝒪_X)`, in particular for `M = a(𝒪_Y)`;
3. the zeroth cohomology sheaf of the right hand side `R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)` is
   `∏_{n ≥ 0} 𝒪_Y`, because `Rf_*𝒪_X = f_*𝒪_X = 𝒪_Y^{⊕ ℕ}`;
4. when some `t ∈ Γ(S, 𝒪_S)` satisfies no equation `t^j = t^{j+1} b` — for instance `S = Spec ℤ`
   and `t = 2` — the product `∏_{n ≥ 0} 𝒪_Y` is not quasi-coherent, so the right hand side is
   not in `D_QCoh(𝒪_Y)`, and no morphism from the left hand side to the right hand side, the map
   of [Stacks, Tag 0E57] in particular, is an isomorphism, whatever the right adjoint `a`.

## Main results

* `traceSource_mem`: item (2).
* `nonempty_homology_traceTarget_iso`: item (3).
* `not_isIso_of_adjunction`: item (4).
* `coherator_cannot_be_dropped`: items (1) to (4) together, the counterexample of
  [Stacks, Tag 0GG3].
* `coherator_cannot_be_dropped_int`: the counterexample over `S = Spec ℤ` with `t = 2`.

## Implementation notes

`Rf_*` is an arbitrary total right derived functor `(Rf, α)` of the direct image of `𝒪`-modules
on the small étale sites, and `R𝓗om` is the derived internal Hom of the small étale ringed site,
`AlgebraicGeometry.RingedSite.smallModelDerivedSheafHom`. The statement quantifies over every
right adjoint `a` of the restriction `AlgebraicGeometry.Space.liftQuasicoherentDerived` of `Rf_*`
and over every morphism between the two sides, so it covers the map of [Stacks, Tag 0E57] for
whichever `a` [Stacks, Tag 0E55] provides. The product `∏_{n ≥ 0} 𝒪_Y` is quasi-coherent when
`S` is the spectrum of a field, so the example needs an element `t` with no equation
`t^j = t^{j+1} b`.

## References

* [Stacks Project, Tag 0GG3](https://stacks.math.columbia.edu/tag/0GG3)
* [Stacks Project, Tag 0E58](https://stacks.math.columbia.edu/tag/0E58)
* [Stacks Project, Tag 0E57](https://stacks.math.columbia.edu/tag/0E57)
* [Stacks Project, Tag 0GEU](https://stacks.math.columbia.edu/tag/0GEU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space.UncoheratedTrace

attribute [local instance] spaceModulesHasDerivedCategory
attribute [local instance] enoughInjectives_modules_ringUniverse
attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
attribute [local instance 5000] modulePushforward_additive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The derived internal Hom `R𝓗om_{𝒪_Z}(-, -)` of an algebraic space `Z`**, on its small étale
ringed site. -/
abbrev derivedSheafHom (Z : AlgebraicSpaces B S hS) :
    (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))ᵒᵖ ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) :=
  RingedSite.smallModelDerivedSheafHom (smallEtaleRingedSite B S hS Z.1 Z.2)

/-- The structure sheaf `𝒪_Z` of an algebraic space, placed in degree zero. -/
abbrev structureSheafDerived (Z : AlgebraicSpaces B S hS) :
    DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Z.1 Z.2).O))

/-- `𝒪_Z` in degree zero lies in `D_QCoh(𝒪_Z)`. -/
theorem structureSheafDerived_mem (Z : AlgebraicSpaces B S hS) :
    quasicoherentDerivedProperty Z (structureSheafDerived B S hS Z) := fun i => by
  by_cases hi : i = 0
  · subst hi
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
      (SheafOfModules.isQuasicoherentOnSite_unit _)
  · refine SheafOfModules.IsQuasicoherentOnSite.of_isZero ?_
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 i h
    · exact DerivedCategory.isZero_of_isLE _ 0 i h

variable [IsAffine S]

/-- The direct image of modules along the structure morphism of the affine line is additive,
for the abelian structure on modules used in this file. -/
instance modulePushforward_affineLineMap_additive :
    (modulePushforward B S hS (affineLineMap B S hS)).Additive :=
  modulePushforward_additive B S hS _

variable
  (Rf : DerivedCategory (Modules.{u, u} B S hS (affineLineAlgebraicSpace B S hS).1
    (affineLineAlgebraicSpace B S hS).2) ⥤
    DerivedCategory (Modules.{u, u} B S hS (affineBaseSpace B S hS).1 (affineBaseSpace B S hS).2))
  (α : (modulePushforward B S hS (affineLineMap B S hS)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  [Rf.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS (affineLineAlgebraicSpace B S hS).1
      (affineLineAlgebraicSpace B S hS).2) (ComplexShape.up ℤ))]

/-- The left hand side `Rf_*R𝓗om_{𝒪_X}(𝒪_X, M)` of the trace map, at an object `M` of `D(𝒪_X)` in
place of `a(𝒪_Y)`. -/
abbrev traceSource (M : DerivedCategory
    (Modules.{u, u} B S hS (affineLineAlgebraicSpace B S hS).1
      (affineLineAlgebraicSpace B S hS).2)) :
    DerivedCategory (Modules.{u, u} B S hS (affineBaseSpace B S hS).1 (affineBaseSpace B S hS).2) :=
  Rf.obj (((derivedSheafHom B S hS (affineLineAlgebraicSpace B S hS)).obj
    (op (structureSheafDerived B S hS (affineLineAlgebraicSpace B S hS)))).obj M)

/-- The right hand side `R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)` of the trace map. -/
abbrev traceTarget : DerivedCategory
    (Modules.{u, u} B S hS (affineBaseSpace B S hS).1 (affineBaseSpace B S hS).2) :=
  ((derivedSheafHom B S hS (affineBaseSpace B S hS)).obj
    (op (Rf.obj (structureSheafDerived B S hS (affineLineAlgebraicSpace B S hS))))).obj
    (structureSheafDerived B S hS (affineBaseSpace B S hS))

include α in
/-- **`Rf_*` preserves `D_QCoh`** along the structure morphism of the affine line, which is
affine. -/
theorem preservesQuasicoherentDerived : PreservesQuasicoherentDerived Rf := fun K i =>
  isQuasicoherentOnSite_homologyFunctor_derivedPushforward_of_isAffineHom B S hS
    (affineLineMap B S hS) Rf α
    (isAffineHom_affineLineMap B S hS) K.obj K.2 i

include α in
/-- **The left hand side lies in `D_QCoh(𝒪_Y)`.** For every `M` in `D_QCoh(𝒪_X)` — in particular
for `M = a(𝒪_Y)`, whatever the right adjoint `a` — the object `Rf_*R𝓗om_{𝒪_X}(𝒪_X, M)` lies in
`D_QCoh(𝒪_Y)`. -/
theorem traceSource_mem (M : DerivedCategory
    (Modules.{u, u} B S hS (affineLineAlgebraicSpace B S hS).1 (affineLineAlgebraicSpace B S hS).2))
    (hM : quasicoherentDerivedProperty (affineLineAlgebraicSpace B S hS) M) :
    quasicoherentDerivedProperty (affineBaseSpace B S hS) (traceSource B S hS Rf M) :=
  (quasicoherentDerivedProperty _).prop_of_iso
    (Rf.mapIso
      (RingedSite.smallModelDerivedSheafHomStructureSheafIso
        (smallEtaleRingedSite B S hS (affineLineAlgebraicSpace B S hS).1
          (affineLineAlgebraicSpace B S hS).2) M)).symm
    (preservesQuasicoherentDerived B S hS Rf α ⟨M, hM⟩)

include α in
/-- On a quasi-coherent `𝒪_X`-module placed in degree zero, `Rf_*` is the direct image placed in
degree zero, `f` being affine. -/
def derivedPushforwardSingleIso
    (M : Modules.{u, u} B S hS (affineLineAlgebraicSpace B S hS).1
      (affineLineAlgebraicSpace B S hS).2)
    (hM : M.IsQuasicoherentOnSite) :
    Rf.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((modulePushforward B S hS (affineLineMap B S hS)).obj M) :=
  let K := (CochainComplex.singleFunctor
    (Modules.{u, u} B S hS (affineLineAlgebraicSpace B S hS).1 (affineLineAlgebraicSpace B S hS).2)
    0).obj M
  have := isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite B S hS
    (affineLineMap B S hS)
    (isAffineHom_affineLineMap B S hS) Rf α K
    (isQuasicoherentOnSite_singleFunctor_obj_X B S hS 0 M hM)
  Rf.mapIso (((DerivedCategory.singleFunctorIsoCompQ _ 0).app M) ≪≫
      ((DerivedCategory.quotientCompQhIso _).app K).symm) ≪≫
    (asIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))).symm ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePushforward B S hS (affineLineMap B S hS)) (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (Modules.{u, u} B S hS (affineBaseSpace B S hS).1 (affineBaseSpace B S hS).2) 0).app
      ((modulePushforward B S hS (affineLineMap B S hS)).obj M)).symm

include α in
/-- **`Rf_*𝒪_X ≅ 𝒪_Y^{⊕ ℕ}`**, placed in degree zero. -/
theorem nonempty_derivedPushforward_structureSheaf_iso :
    Nonempty (Rf.obj (structureSheafDerived B S hS (affineLineAlgebraicSpace B S hS)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.free
        (R := Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (affineBaseSpace B S hS).1 (affineBaseSpace B S hS).2).O)
            (ULift.{u} ℕ))) := by
  obtain ⟨e⟩ := nonempty_affineLineDirectImageFreeIso B S hS
  exact ⟨derivedPushforwardSingleIso B S hS Rf α _ (SheafOfModules.isQuasicoherentOnSite_unit _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e⟩

include α in
/-- **The right hand side: `H⁰(R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)) ≅ ∏_{n ≥ 0} 𝒪_Y`.** -/
theorem nonempty_homology_traceTarget_iso :
    Nonempty ((DerivedCategory.homologyFunctor _ 0).obj (traceTarget B S hS Rf) ≅
      piUnit (affineBaseSpace B S hS).2) := by
  obtain ⟨e⟩ := nonempty_derivedPushforward_structureSheaf_iso B S hS Rf α
  exact ⟨(DerivedCategory.homologyFunctor _ 0).mapIso
      (((derivedSheafHom B S hS (affineBaseSpace B S hS)).mapIso e.op).app _).symm ≪≫
    RingedSite.smallModelDerivedSheafHomFreeHomologyIso
      (smallEtaleRingedSite B S hS (affineBaseSpace B S hS).1 (affineBaseSpace B S hS).2)
        (ULift.{u} ℕ)⟩

/-- **`∏_{n ≥ 0} 𝒪_Y` is not quasi-coherent** when some `t ∈ Γ(S, 𝒪_S)` satisfies no equation
`t^j = t^{j+1} b`. -/
theorem not_isQuasicoherentOnSite_piUnit_affineBase (t : Γ(S, ⊤))
    (ht : ∀ (j : ℕ) (b : Γ(S, ⊤)), t ^ j ≠ t ^ (j + 1) * b) :
    ¬ (piUnit (affineBaseSpace B S hS).2).IsQuasicoherentOnSite :=
  not_isQuasicoherentOnSite_piUnit (affineBaseSpace B S hS).2 (affineBaseChart B S hS)
    (isAffineChart_affineBaseChart B S hS) t ht

include α in
/-- **The right hand side is not in `D_QCoh(𝒪_Y)`** under the condition on `S`. -/
theorem traceTarget_not_mem (t : Γ(S, ⊤))
    (ht : ∀ (j : ℕ) (b : Γ(S, ⊤)), t ^ j ≠ t ^ (j + 1) * b) :
    ¬ quasicoherentDerivedProperty (affineBaseSpace B S hS) (traceTarget B S hS Rf) := fun h => by
  obtain ⟨e⟩ := nonempty_homology_traceTarget_iso B S hS Rf α
  exact not_isQuasicoherentOnSite_piUnit_affineBase B S hS t ht
    ((SheafOfModules.isQuasicoherentOnSite _).prop_of_iso e (h 0))

include α in
/-- **No isomorphism between the two sides.** Under the condition on `S`, for no `M` in
`D_QCoh(𝒪_X)` is `Rf_*R𝓗om_{𝒪_X}(𝒪_X, M)` isomorphic to `R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)`. -/
theorem isEmpty_iso (t : Γ(S, ⊤)) (ht : ∀ (j : ℕ) (b : Γ(S, ⊤)), t ^ j ≠ t ^ (j + 1) * b)
    (M : DerivedCategory (Modules.{u, u} B S hS (affineLineAlgebraicSpace B S hS).1
      (affineLineAlgebraicSpace B S hS).2))
    (hM : quasicoherentDerivedProperty (affineLineAlgebraicSpace B S hS) M) :
    IsEmpty (traceSource B S hS Rf M ≅ traceTarget B S hS Rf) :=
  ⟨fun e => traceTarget_not_mem B S hS Rf α t ht
    ((quasicoherentDerivedProperty _).prop_of_iso e (traceSource_mem B S hS Rf α M hM))⟩

include α in
/-- **The trace map without the coherator is not an isomorphism, for every right adjoint.** Let
`a` be any right adjoint of the restriction `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Under the
condition on `S`, no morphism `Rf_*R𝓗om_{𝒪_X}(𝒪_X, a(𝒪_Y)) ⟶ R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)` is an
isomorphism; in particular the map of [Stacks, Tag 0E57] is not. -/
theorem not_isIso_of_adjunction (t : Γ(S, ⊤))
    (ht : ∀ (j : ℕ) (b : Γ(S, ⊤)), t ^ j ≠ t ^ (j + 1) * b)
    {a : QuasicoherentDerivedCategoryOfModel (affineBaseSpace B S hS) ⥤
      QuasicoherentDerivedCategoryOfModel (affineLineAlgebraicSpace B S hS)}
    (_adj : liftQuasicoherentDerived Rf (preservesQuasicoherentDerived B S hS Rf α) ⊣ a)
    (φ : traceSource B S hS Rf
        (a.obj ⟨structureSheafDerived B S hS (affineBaseSpace B S hS),
          structureSheafDerived_mem B S hS (affineBaseSpace B S hS)⟩).obj ⟶
      traceTarget B S hS Rf) :
    ¬ IsIso φ := fun _ =>
  (isEmpty_iso B S hS Rf α t ht _ (a.obj _).2).false (asIso φ)

include α in
/-- The statement of [Stacks, Tag 0E58] is not true without the coherator `DQ_Y`. Let `S` be an
affine scheme of the big fppf site with a regular function `t` admitting no equation
`t^j = t^{j+1} b` (for instance `S = Spec ℤ`, `t = 2`), let `Y = h_S`, `X = h_{𝔸¹_S}`,
`f : X ⟶ Y` the structure morphism, `L = 𝒪_X` and `K = 𝒪_Y`. Then:

1. `X` and `Y` are quasi-compact and quasi-separated algebraic spaces;
2. `Rf_*` sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`, and `L`, `K` lie in `D_QCoh`;
3. the left hand side `Rf_*R𝓗om_{𝒪_X}(L, M)` lies in `D_QCoh(𝒪_Y)` for every `M` in
   `D_QCoh(𝒪_X)`, in particular for `M = a(K)`;
4. the right hand side `R𝓗om_{𝒪_Y}(Rf_*L, K)` has zeroth cohomology sheaf `∏_{n ≥ 0} 𝒪_Y`,
   which is not quasi-coherent, so the right hand side is not in `D_QCoh(𝒪_Y)`;
5. hence, for every right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, no morphism
   `Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)` — the map (0E57) in particular — is an
   isomorphism. -/
@[stacks 0GG3 "the counterexample of 0GEU on algebraic spaces: for f : A^1_S -> S with S affine \
carrying t with no t^j = t^(j+1) b (S = Spec Z, t = 2), L = O_X, K = O_Y, the left side of the \
0E57 map lies in D_QCoh, the right side has H^0 the non-quasi-coherent product of copies of O_Y, \
and no map between them is an isomorphism, for every right adjoint a"]
theorem coherator_cannot_be_dropped (hZ : B.Contains (⊤_ Scheme.{u})) (t : Γ(S, ⊤))
    (ht : ∀ (j : ℕ) (b : Γ(S, ⊤)), t ^ j ≠ t ^ (j + 1) * b) :
    (IsQuasiCompactSpace B S hS (affineLineAlgebraicSpace B S hS).1 ∧
      IsAbsolutelyQuasiSeparated B S hS hZ (affineLineAlgebraicSpace B S hS).1 ∧
      IsQuasiCompactSpace B S hS (affineBaseSpace B S hS).1 ∧
        IsAbsolutelyQuasiSeparated B S hS hZ (affineBaseSpace B S hS).1) ∧
    PreservesQuasicoherentDerived Rf ∧
    quasicoherentDerivedProperty (affineLineAlgebraicSpace B S hS)
      (structureSheafDerived B S hS (affineLineAlgebraicSpace B S hS)) ∧
    quasicoherentDerivedProperty (affineBaseSpace B S hS)
      (structureSheafDerived B S hS (affineBaseSpace B S hS)) ∧
    (∀ M : DerivedCategory (Modules.{u, u} B S hS (affineLineAlgebraicSpace B S hS).1
      (affineLineAlgebraicSpace B S hS).2),
      quasicoherentDerivedProperty (affineLineAlgebraicSpace B S hS) M →
        quasicoherentDerivedProperty (affineBaseSpace B S hS) (traceSource B S hS Rf M)) ∧
    Nonempty ((DerivedCategory.homologyFunctor _ 0).obj (traceTarget B S hS Rf) ≅
      piUnit (affineBaseSpace B S hS).2) ∧
    ¬ (piUnit (affineBaseSpace B S hS).2).IsQuasicoherentOnSite ∧
    ¬ quasicoherentDerivedProperty (affineBaseSpace B S hS) (traceTarget B S hS Rf) ∧
    ∀ (a : QuasicoherentDerivedCategoryOfModel (affineBaseSpace B S hS) ⥤
      QuasicoherentDerivedCategoryOfModel (affineLineAlgebraicSpace B S hS))
      (_ : liftQuasicoherentDerived Rf (preservesQuasicoherentDerived B S hS Rf α) ⊣ a)
      (φ : traceSource B S hS Rf
          (a.obj ⟨structureSheafDerived B S hS (affineBaseSpace B S hS),
            structureSheafDerived_mem B S hS (affineBaseSpace B S hS)⟩).obj ⟶
        traceTarget B S hS Rf),
      ¬ IsIso φ :=
  ⟨⟨isQuasiCompactSpace_yoneda_of_isAffine B S hS _
      (BigFppfOver.isAffine_affineSpace B S hS 1 _ (isAffine_affineBase B S hS)),
    isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
      (isAffineSpace_affineLineAlgebraicSpace B S hS),
    isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (isAffine_affineBase B S hS),
    isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ (isAffineSpace_affineBaseSpace B S hS)⟩,
    preservesQuasicoherentDerived B S hS Rf α,
    structureSheafDerived_mem B S hS (affineLineAlgebraicSpace B S hS),
      structureSheafDerived_mem B S hS (affineBaseSpace B S hS),
    traceSource_mem B S hS Rf α,
    nonempty_homology_traceTarget_iso B S hS Rf α,
    not_isQuasicoherentOnSite_piUnit_affineBase B S hS t ht,
    traceTarget_not_mem B S hS Rf α t ht,
    fun _ adj φ => not_isIso_of_adjunction B S hS Rf α t ht adj φ⟩

/-- In `Γ(Spec ℤ, 𝒪) ≅ ℤ` the element `2` admits no equation `2^j = 2^{j+1} b`. -/
theorem two_pow_ne_two_pow_succ_mul_int (j : ℕ) (b : Γ(Spec (CommRingCat.of ℤ), ⊤)) :
    ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv 2) ^ j ≠
      ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv 2) ^ (j + 1) * b := by
  intro h
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom h
  simp only [map_pow, map_mul, Iso.inv_hom_id_apply] at h'
  set c : ℤ := (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom b
  have h2 : (2 : ℤ) ^ j * (1 - 2 * c) = 0 := by
    rw [pow_succ] at h'
    change (2 : ℤ) ^ j = 2 ^ j * 2 * c at h'
    linear_combination h'
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact pow_ne_zero _ two_ne_zero h3
  · omega

/-- **The coherator cannot be dropped, over `ℤ`.** For `Y = h_{Spec ℤ}` and `X = h_{𝔸¹_ℤ}` the
product `∏_{n ≥ 0} 𝒪_Y` is not quasi-coherent, and for every right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` no morphism
`Rf_*R𝓗om_{𝒪_X}(𝒪_X, a(𝒪_Y)) ⟶ R𝓗om_{𝒪_Y}(Rf_*𝒪_X, 𝒪_Y)` is an isomorphism. -/
theorem coherator_cannot_be_dropped_int {B : BigFppfSite.{0}}
    (hZ : B.Contains (Spec (CommRingCat.of ℤ)))
    (Rf : DerivedCategory (Modules.{0, 0} B _ hZ (affineLineAlgebraicSpace B _ hZ).1
        (affineLineAlgebraicSpace B _ hZ).2) ⥤
      DerivedCategory (Modules.{0, 0} B _ hZ (affineBaseSpace B _ hZ).1
        (affineBaseSpace B _ hZ).2))
    (α : (modulePushforward B _ hZ (affineLineMap B _ hZ)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α (HomotopyCategory.quasiIso (Modules.{0, 0} B _ hZ
      (affineLineAlgebraicSpace B _ hZ).1 (affineLineAlgebraicSpace B _ hZ).2)
        (ComplexShape.up ℤ))] :
    ¬ (piUnit (affineBaseSpace B _ hZ).2).IsQuasicoherentOnSite ∧
    ∀ (a : QuasicoherentDerivedCategoryOfModel (affineBaseSpace B _ hZ) ⥤
        QuasicoherentDerivedCategoryOfModel (affineLineAlgebraicSpace B _ hZ))
      (_ : liftQuasicoherentDerived Rf (preservesQuasicoherentDerived B _ hZ Rf α) ⊣ a)
      (φ : traceSource B _ hZ Rf
          (a.obj ⟨structureSheafDerived B _ hZ (affineBaseSpace B _ hZ),
            structureSheafDerived_mem B _ hZ (affineBaseSpace B _ hZ)⟩).obj ⟶
        traceTarget B _ hZ Rf),
      ¬ IsIso φ :=
  ⟨not_isQuasicoherentOnSite_piUnit_affineBase B _ hZ _ two_pow_ne_two_pow_succ_mul_int,
    fun _ adj φ => not_isIso_of_adjunction B _ hZ Rf α _ two_pow_ne_two_pow_succ_mul_int adj φ⟩

end AlgebraicGeometry.Space.UncoheratedTrace

end
