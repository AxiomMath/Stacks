module

public import StacksFrontier.AlgebraicGeometry.Duality.FiniteTwistedTrace
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleDataOfFinite
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleUniqueness0BVG
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimension
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.Topology.Dimension.IsolatedPoint
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionCharts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `H⁰(f^!𝒪_X)` is the relative dualizing module of a quasi-finite morphism

Let `S` be Noetherian and `f : Y ⟶ X` a locally quasi-finite morphism of schemes separated and of
finite type over `S`. For every compactification `j` defining `f^!`, the degree-zero cohomology
sheaf `H⁰(f^!𝒪_X)` carries the chart data of the relative dualizing module `ω_{Y/X}`: over affine
opens `Spec(B) = V ⊆ Y`, `Spec(A) = U ⊆ X` with `f(V) ⊆ U` its sections are `ω_{B/A}`, compatibly
with restriction. The identification comes from a factorization `f = π ∘ i` with `i` an open
immersion and `π` finite (Zariski's main theorem): `f^! = i^* ∘ a`, and over an affine `U ⊆ X`
the sections of `H⁰(a(𝒪_X))` over `π⁻¹U = Spec(B')` are `Hom_A(B', A)`, a section `s` giving
`b ↦ Tr(b s)` for the trace `π_*H⁰(a(𝒪_X)) ⟶ 𝒪_X`.

## Main definitions

* `Stacks.Duality.upperShriekStructureSheafZeroth`: `H⁰(f^!𝒪_X)`.
* `Stacks.Duality.upperShriekRelativeDualizingModuleData`: the chart data of `ω_{Y/X}` on it.

## Main results

* `Stacks.Duality.existsUnique_upperShriekRelativeDualizingComparison`: the canonical
  identification of `H⁰(f^!𝒪_X)` with any relative dualizing module `ω_{Y/X}` of Tag 0BVG.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DerivedCategory

universe u

namespace Stacks.Duality

open DerivedPushforward Stacks.Discriminant

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)

/-- The underlying morphism of a morphism of `FTS S` is quasi-compact. -/
instance quasiCompact_left_of_fts : QuasiCompact f.left :=
  quasiCompact_of_compactSpace _

/-- `H⁰(f^!𝒪_Y)`, for `f^!` computed at the compactification `j`. -/
abbrev upperShriekStructureSheafZeroth (j : CompactificationOf (Over.mk f.left)) :
    X.left.Modules :=
  (homologyFunctor X.left.Modules 0).obj
    ((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj

/-- A factorization `f = i ≫ π` of a locally quasi-finite morphism of `FTS S` into an open
immersion followed by a finite morphism (Zariski's main theorem). -/
@[ega "IV 18.12.13" "special case"]
theorem exists_isOpenImmersion_isFinite_factorization_left [LocallyQuasiFinite f.left] :
    ∃ (T : Scheme.{u}) (i : X.left ⟶ T) (π : T ⟶ Y.left),
      IsOpenImmersion i ∧ IsFinite π ∧ i ≫ π = f.left := by
  obtain ⟨T, i, π, hi, -, hπ, h⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization f.left
  exact ⟨T, i, π, hi, hπ, h.symm⟩

/-- A factorization `f = i ≫ π` of a morphism of `FTS S` into an open immersion `i` followed by
a finite morphism `π`. -/
structure OpenFiniteFactorization where
  /-- The scheme finite over `Y` through which `f` factors. -/
  space : Scheme.{u}
  /-- The open immersion `X ⟶ T`. -/
  immersion : X.left ⟶ space
  /-- The finite morphism `T ⟶ Y`. -/
  toBase : space ⟶ Y.left
  isOpenImmersion_immersion : IsOpenImmersion immersion := by infer_instance
  isFinite_toBase : IsFinite toBase := by infer_instance
  fac : immersion ≫ toBase = f.left

attribute [instance] OpenFiniteFactorization.isOpenImmersion_immersion
  OpenFiniteFactorization.isFinite_toBase

/-- A finite morphism factors through itself. -/
abbrev OpenFiniteFactorization.ofIsFinite [IsFinite f.left] : OpenFiniteFactorization f where
  space := X.left
  immersion := 𝟙 _
  toBase := f.left
  fac := Category.id_comp _

variable [LocallyQuasiFinite f.left]

/-- The chosen factorization: `f` itself if `f` is finite, otherwise one given by Zariski's main
theorem. -/
def chosenOpenFiniteFactorization : OpenFiniteFactorization f := by
  classical
  exact if h : IsFinite f.left then OpenFiniteFactorization.ofIsFinite f else
    let T := (exists_isOpenImmersion_isFinite_factorization_left f).choose
    let i := (exists_isOpenImmersion_isFinite_factorization_left f).choose_spec.choose
    let π := (exists_isOpenImmersion_isFinite_factorization_left f).choose_spec.choose_spec.choose
    have hp :=
      (exists_isOpenImmersion_isFinite_factorization_left f).choose_spec.choose_spec.choose_spec
    haveI := hp.1
    haveI := hp.2.1
    { space := T, immersion := i, toBase := π, fac := hp.2.2 }

/-- For finite `f`, the chosen factorization is `f` itself. -/
theorem chosenOpenFiniteFactorization_of_isFinite [IsFinite f.left] :
    chosenOpenFiniteFactorization f = OpenFiniteFactorization.ofIsFinite f := by
  rw [chosenOpenFiniteFactorization, dif_pos (inferInstance : IsFinite f.left)]

variable {f} (F : OpenFiniteFactorization f)

/-- The factorization through a scheme finite over `Y` as a compactification of `f`. -/
def OpenFiniteFactorization.compactification : CompactificationOf (Over.mk f.left) :=
  ⟨StructuredArrow.mk (Y := Over.mk F.toBase) (Over.homMk F.immersion F.fac),
    ⟨inferInstanceAs (IsOpenImmersion F.immersion), inferInstanceAs (IsProper F.toBase)⟩⟩

/-- `T` as an object of `FTS S`. -/
abbrev finiteSpaceFTS : FTS S := FTS.mk (F.toBase ≫ Y.hom)

/-- `π : T ⟶ Y` as a morphism of `FTS S`. -/
abbrev finiteToBaseFTS : finiteSpaceFTS F ⟶ Y :=
  MorphismProperty.Over.homMk (F.toBase) rfl trivial

/-- The finite morphism `π : T ⟶ Y` is proper. -/
instance : IsProper (finiteToBaseFTS F).left := inferInstanceAs (IsProper (F.toBase))

/-- The scheme `T` finite over `Y` is Noetherian. -/
instance : IsNoetherian (F.space) :=
  inferInstanceAs (IsNoetherian (finiteSpaceFTS F).left)

/-- The fibres of a locally quasi-finite morphism have dimension `0` at each of their points. -/
theorem topologicalKrullDimAt_fiber_eq_zero {A B : Scheme.{u}} (g : A ⟶ B) [LocallyQuasiFinite g]
    (x : A) : topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) = ((0 : ℕ) : WithBot ℕ∞) := by
  have : DiscreteTopology (g.fiber (g x)) := IsLocallyArtinian.discreteTopology
  exact topologicalKrullDimAt_eq_zero_of_isIsolatedPoint _ (isOpen_discrete _)

/-- `a(𝒪_Y)` has no cohomology in negative degrees, for the finite morphism `π`. -/
instance isGE_twisted_finiteToBase :
    ((FiniteTrace.twisted (F.toBase)).obj (derivedStructureSheaf Y.left)).obj.IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have e := (ObjectProperty.ι _).mapIso ((upperShriekProperIso (finiteToBaseFTS F)).app
    (derivedStructureSheaf Y.left))
  refine IsZero.of_iso ?_ ((homologyFunctor _ i).mapIso e).symm
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun x => ?_
  by_contra hne
  have hnt : Nontrivial (((homologyFunctor (finiteSpaceFTS F).left.Modules i).obj
      ((upperShriek (finiteToBaseFTS F) (properCompactification (finiteToBaseFTS F))).obj
        (derivedStructureSheaf Y.left)).obj).presheaf.stalk x) := by
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    exact hne (@AddCommGrpCat.isZero_of_subsingleton _ hs)
  have := neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek_unconditional (finiteToBaseFTS F)
    (properCompactification (finiteToBaseFTS F)) x 0
    (topologicalKrullDimAt_fiber_eq_zero (F.toBase) x) i hnt
  omega

/-- `H⁰(a(𝒪_Y))` on the scheme `T` finite over `Y`. -/
abbrev finiteZeroTwisted : (F.space).Modules :=
  FiniteTrace.zeroTwisted (F.toBase) (derivedStructureSheaf Y.left)

/-- `H⁰(a(𝒪_Y))` is quasi-coherent. -/
instance : (finiteZeroTwisted F).IsQuasicoherent :=
  ((FiniteTrace.twisted (F.toBase)).obj (derivedStructureSheaf Y.left)).2 0

/-- The trace `π_*H⁰(a(𝒪_Y)) ⟶ 𝒪_Y`. -/
def finiteTrace : (Scheme.Modules.pushforward (F.toBase)).obj (finiteZeroTwisted F) ⟶
    SheafOfModules.unit Y.left.ringCatSheaf :=
  FiniteTrace.trace (g := F.toBase) (derivedStructureSheaf Y.left) ≫
    ((singleFunctorCompHomologyFunctorIso Y.left.Modules 0).app
      (SheafOfModules.unit Y.left.ringCatSheaf)).hom

omit [AlgebraicGeometry.IsNoetherian S] in
/-- For an isomorphism `e : M ≅ N` of `𝒪_Z`-modules, `e.hom` undoes `e.inv` on the sections over
every open `W`. -/
theorem iso_hom_app_inv_app {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (W : Z.Opens)
    (x : Γ(N, W)) : e.hom.app W (e.inv.app W x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]; rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- For an isomorphism `e : M ≅ N` of `𝒪_Z`-modules, `e.hom` is injective on the sections over
every open `W`. -/
theorem iso_hom_app_injective {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (W : Z.Opens) :
    Function.Injective (e.hom.app W) :=
  Function.LeftInverse.injective (g := e.inv.app W) (iso_hom_app_inv_app e.symm W)

omit [LocallyQuasiFinite f.left] in
/-- **The affine duality of the trace**: for `U ⊆ Y` affine, `s ↦ (b ↦ Tr(b s))` identifies the
sections of `H⁰(a(𝒪_Y))` over `π⁻¹U` with `Hom_{Γ(U)}(Γ(π⁻¹U), Γ(U))`. -/
theorem bijective_traceDual_finiteTrace (U : Y.left.affineOpens) :
    Function.Bijective (traceDual (F.toBase) (finiteTrace F) U.1) := by
  let : Algebra Γ(Y.left, U.1) Γ(F.space, F.toBase ⁻¹ᵁ U.1) :=
    ((F.toBase).appLE U.1 (F.toBase ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  let c := (singleFunctorCompHomologyFunctorIso Y.left.Modules 0).app
    (SheafOfModules.unit Y.left.ringCatSheaf)
  have happ : ∀ x, traceApp (F.toBase) (finiteTrace F) U.1 x =
      c.hom.app U.1 ((FiniteTrace.trace (g := F.toBase)
        (derivedStructureSheaf Y.left)).app U.1 x) := fun _ => rfl
  refine ⟨fun s s' h => ?_, fun l => ?_⟩
  · refine FiniteTrace.eq_of_trace_smul_eq (F.toBase) U.1 U.2 s s' fun b =>
      iso_hom_app_injective c U.1 ?_
    have := LinearMap.congr_fun h b
    rwa [traceDual_apply, traceDual_apply, happ, happ] at this
  · let l' : Γ((Scheme.Modules.pushforward (F.toBase)).obj
        (SheafOfModules.unit (F.space).ringCatSheaf), U.1) →ₗ[Γ(Y.left, U.1)]
        Γ((homologyFunctor Y.left.Modules 0).obj (derivedStructureSheaf Y.left).obj, U.1) :=
      (FiniteTrace.appLinear c.inv U.1).comp
        { toFun := fun b => l b
          map_add' := fun b b' => l.map_add b b'
          map_smul' := fun a b => by
            let b' : Γ(F.space, F.toBase ⁻¹ᵁ U.1) := b
            have e : (show Γ(F.space, F.toBase ⁻¹ᵁ U.1) from a • b) = a • b' := by
              rw [Algebra.smul_def]
              show ((F.toBase).app U.1).hom a * _ = _
              rw [← Scheme.Hom.appLE_eq_app (F.toBase)]
              rfl
            rw [RingHom.id_apply]
            exact (congrArg l e).trans (l.map_smul a b') }
    obtain ⟨m, hm⟩ := FiniteTrace.exists_trace_smul_eq (F.toBase) U.1 U.2 l'
    refine ⟨m, LinearMap.ext fun b => ?_⟩
    rw [traceDual_apply, happ, hm b]
    exact iso_hom_app_inv_app c U.1 (l b)

/-- `H⁰(f^!𝒪_Y)` is the restriction of `H⁰(a(𝒪_Y))` to `X`, for every compactification `j`:
`f^!` computed at `j` agrees on `D⁺_QCoh` with `i^* ∘ a` (Tag 0AA0), and `H⁰` commutes with
restriction to an open. -/
def upperShriekStructureSheafZerothIso (j : CompactificationOf (Over.mk f.left)) :
    upperShriekStructureSheafZeroth f j ≅ (finiteZeroTwisted F).restrict (F.immersion) :=
  let O := derivedStructureSheaf Y.left
  let Op : quasiCoherentDerivedCategoryPlusOfModel Y.left :=
    ⟨O, KoszulRegular.isBoundedBelow_singleFunctor_obj _⟩
  let e₁ : (upperShriek f j).obj O ≅ (upperShriek f (F.compactification)).obj O :=
    (ObjectProperty.ι _).mapIso
      ((DominatingCompactification.upperShriekPlusIso f j (F.compactification)).app Op)
  let e₂ : (upperShriek f (F.compactification)).obj O ≅
      (OpenImmersion.restrictedDerivedRestrict (F.immersion)).obj
        ((FiniteTrace.twisted (F.toBase)).obj O) :=
    ((restrictedDerivedRestrictAdjointIso (F.immersion)).app _).symm
  (homologyFunctor X.left.Modules 0).mapIso ((ObjectProperty.ι _).mapIso (e₁ ≪≫ e₂)) ≪≫
    ((Scheme.Modules.restrictFunctor (F.immersion)).mapDerivedCategoryHomologyIso 0).app
      ((FiniteTrace.twisted (F.toBase)).obj O).obj

/-- The chart data of `ω_{X/Y}` on `H⁰(f^!𝒪_Y)` attached to a factorization `f = π ∘ i`. -/
def OpenFiniteFactorization.relativeDualizingModuleData (j : CompactificationOf (Over.mk f.left)) :
    RelativeDualizingModuleData f.left :=
  RelativeDualizingModuleData.ofFiniteTrace F.fac (finiteZeroTwisted F) (finiteTrace F)
    (bijective_traceDual_finiteTrace F) (upperShriekStructureSheafZerothIso F j)

variable (f)

/-- **Stacks Project, Tag 0BUL, first assertion.** Let `f : X ⟶ Y` be a quasi-finite morphism
of schemes separated and of finite type over a Noetherian scheme `S`, and `f^!` the upper shriek
of [Stacks, Tag 0A9Y] at any compactification `j`. Then `H⁰(f^!𝒪_Y)` is a relative dualizing
module for `f` (Tag 0BVG): for affine opens `Spec(B) = V ⊆ X`, `Spec(A) = U ⊆ Y` with
`f(V) ⊆ U` its sections over `V` are identified with `ω_{B/A}`, independently of the
finite-open factorization computing `ω_{B/A}` and compatibly with the restriction maps. -/
@[stacks 0BUL "first assertion: H^0(V, f^! O) = omega_{B/A}, compatible with restriction"]
def upperShriekRelativeDualizingModuleData (j : CompactificationOf (Over.mk f.left)) :
    RelativeDualizingModuleData f.left :=
  (chosenOpenFiniteFactorization f).relativeDualizingModuleData j

/-- For finite `f`, the chart data of `ω_{X/Y}` on `H⁰(f^!𝒪_Y)` is the one attached to the trivial
factorization `f = f ∘ 𝟙`. -/
theorem upperShriekRelativeDualizingModuleData_of_isFinite [IsFinite f.left]
    (j : CompactificationOf (Over.mk f.left)) :
    upperShriekRelativeDualizingModuleData f j =
      (OpenFiniteFactorization.ofIsFinite f).relativeDualizingModuleData j := by
  rw [upperShriekRelativeDualizingModuleData, chosenOpenFiniteFactorization_of_isFinite]

/-- The underlying sheaf of `upperShriekRelativeDualizingModuleData f j` is `H⁰(f^!𝒪_Y)`. -/
@[simp]
theorem upperShriekRelativeDualizingModuleData_sheaf (j : CompactificationOf (Over.mk f.left)) :
    (upperShriekRelativeDualizingModuleData f j).sheaf = upperShriekStructureSheafZeroth f j :=
  rfl

/-- **Stacks Project, Tag 0BUL, first assertion (the canonical isomorphism).** The affine
identifications of `upperShriekRelativeDualizingModuleData` define a canonical isomorphism
`H⁰(f^!𝒪_Y) ≅ ω_{X/Y}` with any relative dualizing module `ω_{X/Y}` of Tag 0BVG: there is exactly
one family of isomorphisms on sections, compatible with restriction, carrying the identification
of `H⁰(V, f^!𝒪_Y)` with `ω_{B/A}` to that of `Γ(V, ω_{X/Y})`. -/
@[stacks 0BUL "first assertion: the canonical isomorphism H^0(f^! O) = omega_{Y/X}"]
theorem existsUnique_upperShriekRelativeDualizingComparison
    (j : CompactificationOf (Over.mk f.left)) (ω : RelativeDualizingModuleData f.left) :
    ∃! E : ∀ W : X.left.Opens,
        Γ(upperShriekStructureSheafZeroth f j, W) ≃ₗ[Γ(X.left, W)] Γ(ω.sheaf, W),
      (∀ (W W' : X.left.Opens) (h : W' ≤ W) (s : Γ(upperShriekStructureSheafZeroth f j, W)),
          E W' (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ _ h s) =
            Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ ω.sheaf h (E W s)) ∧
        ∀ (U : Y.left.affineOpens) (V : X.left.affineOpens) (hVU : V.1 ≤ f.left ⁻¹ᵁ U.1),
          letI : Algebra Γ(Y.left, U.1) Γ(X.left, V.1) := (f.left.appLE U V hVU).hom.toAlgebra
          ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(Y.left, U.1) Γ(X.left, V.1))
            (s : Γ(upperShriekStructureSheafZeroth f j, V.1)),
            ω.localEquiv U V hVU F (E V.1 s) =
              (upperShriekRelativeDualizingModuleData f j).localEquiv U V hVU F s :=
  existsUnique_relativeDualizingComparison (upperShriekRelativeDualizingModuleData f j) ω

end Stacks.Duality
