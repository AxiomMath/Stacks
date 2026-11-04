module

public import StacksFrontier.AlgebraicGeometry.Discriminant.PushforwardTrace
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeTraceSection
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeDualizingModule
public import StacksFrontier.RingTheory.TraceElement.FiniteFlat

/-!
# The trace of a finite flat morphism as a section of `f^!𝒪_Y`

Let `f : X ⟶ Y` be a finite flat morphism of `FTS S`. A morphism `T : f_*𝒪_X ⟶ 𝒪_Y` corresponds,
by the duality `Hom(𝒪_X, H⁰(a(𝒪_Y))) = Hom(f_*𝒪_X, 𝒪_Y)` of the finite morphism `f`, to a global
section of `H⁰(a(𝒪_Y))`, hence of `H⁰(f^!𝒪_Y)`. When `T` is the trace of `f` on affine opens, this
section is the trace element `τ_{X/Y}` of Tag 0BVJ for the identification of Tag 0BUL.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DerivedCategory Opposite

universe u

namespace Stacks.Duality

open DerivedPushforward Stacks.Discriminant

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y) [IsFinite f.left]

/-- The factorization of the finite morphism `f` through itself. -/
abbrev selfFiniteFactorization : OpenFiniteFactorization f := OpenFiniteFactorization.ofIsFinite f

/-- For finite `f`, the complex `a(𝒪_Y)` is concentrated in degrees `≥ 0`. -/
instance isGE_twisted_of_isFinite :
    ((FiniteTrace.twisted f.left).obj (derivedStructureSheaf Y.left)).obj.IsGE 0 :=
  isGE_twisted_finiteToBase (selfFiniteFactorization f)

/-- For finite `f`, the sheaf `H⁰(a(𝒪_Y))` is quasi-coherent. -/
instance isQuasicoherent_zeroTwisted_of_isFinite :
    (FiniteTrace.zeroTwisted f.left (derivedStructureSheaf Y.left)).IsQuasicoherent :=
  ((FiniteTrace.twisted f.left).obj (derivedStructureSheaf Y.left)).2 0

/-- The isomorphism `H⁰(𝒪_Y[0]) ≅ 𝒪_Y`. -/
abbrev unitHomologyIso (Z : Scheme.{u}) :
    (homologyFunctor Z.Modules 0).obj (derivedStructureSheaf Z).obj ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  (singleFunctorCompHomologyFunctorIso Z.Modules 0).app (SheafOfModules.unit Z.ringCatSheaf)

/-- The morphism `𝒪_X ⟶ H⁰(a(𝒪_Y))` corresponding under duality to `T : f_*𝒪_X ⟶ 𝒪_Y`. -/
def dualMorphism (T : (Scheme.Modules.pushforward f.left).obj
      (SheafOfModules.unit X.left.ringCatSheaf) ⟶ SheafOfModules.unit Y.left.ringCatSheaf) :
    (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) ⟶
      FiniteTrace.zeroTwisted f.left (derivedStructureSheaf Y.left) :=
  (Equiv.ofBijective _ (FiniteTrace.bijective_dualityMap (g := f.left)
    (derivedStructureSheaf Y.left) (SheafOfModules.unit X.left.ringCatSheaf))).symm
      (T ≫ (unitHomologyIso Y.left).inv)

/-- The duality map sends the morphism `𝒪_X ⟶ H⁰(a(𝒪_Y))` dual to `T` to `T`, composed with
the isomorphism `𝒪_Y ≅ H⁰(𝒪_Y[0])`. -/
theorem dualityMap_dualMorphism (T : (Scheme.Modules.pushforward f.left).obj
      (SheafOfModules.unit X.left.ringCatSheaf) ⟶ SheafOfModules.unit Y.left.ringCatSheaf) :
    FiniteTrace.dualityMap (g := f.left) (derivedStructureSheaf Y.left) (dualMorphism f T) =
      T ≫ (unitHomologyIso Y.left).inv :=
  (Equiv.ofBijective _ (FiniteTrace.bijective_dualityMap (g := f.left)
    (derivedStructureSheaf Y.left) (SheafOfModules.unit X.left.ringCatSheaf))).apply_symm_apply _

/-- The global section of `H⁰(f^!𝒪_Y)` corresponding to `T : f_*𝒪_X ⟶ 𝒪_Y`: the image of `1`
under the morphism `𝒪_X ⟶ H⁰(a(𝒪_Y))` dual to `T`, read in `H⁰(f^!𝒪_Y)` for the
compactification `j` through the identification of Tag 0AA0. -/
def upperShriekDualSection (T : (Scheme.Modules.pushforward f.left).obj
      (SheafOfModules.unit X.left.ringCatSheaf) ⟶ SheafOfModules.unit Y.left.ringCatSheaf)
    (j : CompactificationOf (Over.mk f.left)) : Γ(upperShriekStructureSheafZeroth f j, ⊤) :=
  chartRestrict (finiteZeroTwisted (selfFiniteFactorization f))
    (upperShriekStructureSheafZerothIso (selfFiniteFactorization f) j)
    (le_top : (⊤ : X.left.Opens) ≤ (𝟙 X.left) ⁻¹ᵁ ⊤)
    (Scheme.Modules.Hom.app (dualMorphism f T) ⊤ (FiniteTrace.unitOne ⊤))

/-- On `f⁻¹U`, the functional `b ↦ t(b · s)` attached to the restriction of the section dual
to `T` is `T` itself. -/
theorem traceDual_dualMorphism (T : (Scheme.Modules.pushforward f.left).obj
      (SheafOfModules.unit X.left.ringCatSheaf) ⟶ SheafOfModules.unit Y.left.ringCatSheaf)
    (U : Y.left.Opens) (b : Γ(X.left, f.left ⁻¹ᵁ U)) :
    traceDual f.left (finiteTrace (selfFiniteFactorization f)) U
        ((finiteZeroTwisted (selfFiniteFactorization f)).presheaf.map
          (homOfLE (le_top : f.left ⁻¹ᵁ U ≤ ⊤)).op
          (Scheme.Modules.Hom.app (dualMorphism f T) ⊤ (FiniteTrace.unitOne ⊤))) b =
      T.app U b := by
  let φ : (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) ⟶
      FiniteTrace.zeroTwisted f.left (derivedStructureSheaf Y.left) := dualMorphism f T
  have hres : (finiteZeroTwisted (selfFiniteFactorization f)).presheaf.map
      (homOfLE (le_top : f.left ⁻¹ᵁ U ≤ ⊤)).op
        (Scheme.Modules.Hom.app φ ⊤ (FiniteTrace.unitOne ⊤)) =
      Scheme.Modules.Hom.app φ (f.left ⁻¹ᵁ U) (FiniteTrace.unitOne _) := by
    have := congrArg (fun χ => χ (FiniteTrace.unitOne (⊤ : X.left.Opens)))
      ((Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE (le_top : f.left ⁻¹ᵁ U ≤ ⊤)).op)
    refine this.symm.trans ?_
    change Scheme.Modules.Hom.app φ (f.left ⁻¹ᵁ U)
      ((X.left.presheaf.map (homOfLE (le_top : f.left ⁻¹ᵁ U ≤ ⊤)).op).hom 1) = _
    rw [map_one]
    rfl
  have h2 := ConcreteCategory.congr_hom
    (congrArg (fun χ => Scheme.Modules.Hom.app χ U) (dualityMap_dualMorphism f T)) b
  refine (traceDual_apply _ _ _ _ _).trans ?_
  rw [hres, ← FiniteTrace.app_eq_smul_app_one φ _ b]
  change (unitHomologyIso Y.left).hom.app U
    ((FiniteTrace.trace (g := f.left) (derivedStructureSheaf Y.left)).app U
      (Scheme.Modules.Hom.app φ _ b)) = _
  rw [← FiniteTrace.dualityMap_app_eq (g := f.left) (U := U) _ φ b, h2]
  exact iso_hom_app_inv_app (unitHomologyIso Y.left) U (T.app U b)

/-- The restriction to `f⁻¹U` of the section of `H⁰(f^!𝒪_Y)` dual to `T` is the image, under
the identification with `H⁰(a(𝒪_Y))` over `f⁻¹U`, of the restriction to `f⁻¹U` of the image of `1`
under the morphism `𝒪_X ⟶ H⁰(a(𝒪_Y))` dual to `T`. -/
theorem upperShriekDualSection_restrict (T : (Scheme.Modules.pushforward f.left).obj
      (SheafOfModules.unit X.left.ringCatSheaf) ⟶ SheafOfModules.unit Y.left.ringCatSheaf)
    (j : CompactificationOf (Over.mk f.left)) (U : Y.left.Opens) :
    (upperShriekStructureSheafZeroth f j).presheaf.map (homOfLE (le_top : f.left ⁻¹ᵁ U ≤ ⊤)).op
        (upperShriekDualSection f T j) =
      chartRestrict (finiteZeroTwisted (selfFiniteFactorization f))
        (upperShriekStructureSheafZerothIso (selfFiniteFactorization f) j)
        (le_preimage_preimage (Category.id_comp f.left) le_rfl)
        ((finiteZeroTwisted (selfFiniteFactorization f)).presheaf.map
          (homOfLE (le_top : f.left ⁻¹ᵁ U ≤ ⊤)).op
          (Scheme.Modules.Hom.app (dualMorphism f T) ⊤ (FiniteTrace.unitOne ⊤))) :=
  (chartRestrict_restrict_source _ _ (le_top : f.left ⁻¹ᵁ U ≤ ⊤) _ _).trans
    (chartRestrict_restrict_target _ _ (le_top : f.left ⁻¹ᵁ U ≤ ⊤) _ _).symm

variable [Flat f.left]

/-- If `T : f_*𝒪_X ⟶ 𝒪_Y` is the trace of `f` on every affine open of `Y`, the section of
`H⁰(f^!𝒪_Y)` dual to `T` is the trace element `τ_{X/Y}` of the relative dualizing module. -/
theorem upperShriekDualSection_eq_relativeTraceSection (T : (Scheme.Modules.pushforward f.left).obj
      (SheafOfModules.unit X.left.ringCatSheaf) ⟶ SheafOfModules.unit Y.left.ringCatSheaf)
    (hT : ∀ (U : Y.left.affineOpens) (b : Γ(X.left, f.left ⁻¹ᵁ U.1)),
      letI : Algebra Γ(Y.left, U.1) Γ(X.left, f.left ⁻¹ᵁ U.1) :=
        (f.left.appLE U.1 (f.left ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
      letI : Module.Finite Γ(Y.left, U.1) Γ(X.left, f.left ⁻¹ᵁ U.1) := by
        have h := f.left.finite_app U.1 U.2
        rwa [Scheme.Hom.app_eq_appLE] at h
      letI : IsNoetherianRing Γ(Y.left, U.1) := IsLocallyNoetherian.component_noetherian U
      haveI : Module.Flat Γ(Y.left, U.1) Γ(X.left, f.left ⁻¹ᵁ U.1) :=
        RingHom.flat_algebraMap_iff.mp (f.left.flat_appLE U.2 (U.2.preimage f.left) le_rfl)
      haveI : Module.FinitePresentation Γ(Y.left, U.1) Γ(X.left, f.left ⁻¹ᵁ U.1) :=
        Module.finitePresentation_of_finite _ _
      haveI : Module.Projective Γ(Y.left, U.1) Γ(X.left, f.left ⁻¹ᵁ U.1) :=
        Module.Flat.projective_of_finitePresentation
      T.app U.1 b = finiteProjectiveTrace Γ(Y.left, U.1) Γ(X.left, f.left ⁻¹ᵁ U.1)
        (Algebra.lmul Γ(Y.left, U.1) Γ(X.left, f.left ⁻¹ᵁ U.1) b))
    (j : CompactificationOf (Over.mk f.left)) :
    upperShriekDualSection f T j =
      relativeTraceSection ((selfFiniteFactorization f).relativeDualizingModuleData j) := by
  let D := (selfFiniteFactorization f).relativeDualizingModuleData j
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨D.sheaf.presheaf, D.sheaf.isSheaf⟩ : TopCat.Sheaf Ab (X.left : TopCat.{u}))
    (fun U : Y.left.affineOpens => f.left ⁻¹ᵁ U.1) ⊤ (fun _ => homOfLE le_top) ?_ _ _
    fun U => ?_
  · intro x _
    have hx : f.left x ∈ (⨆ U : Y.left.affineOpens, (U : Y.left.Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top Y.left]
      trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hU⟩
  let V : X.left.affineOpens := ⟨f.left ⁻¹ᵁ U.1, U.2.preimage f.left⟩
  let : Algebra Γ(Y.left, U.1) Γ(X.left, V.1) := (f.left.appLE U.1 V.1 le_rfl).hom.toAlgebra
  have : Module.Finite Γ(Y.left, U.1) Γ(X.left, V.1) := by
    have h := f.left.finite_app U.1 U.2
    rwa [Scheme.Hom.app_eq_appLE] at h
  have : IsNoetherianRing Γ(Y.left, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X.left, V.1) := IsLocallyNoetherian.component_noetherian V
  have : Module.Flat Γ(Y.left, U.1) Γ(X.left, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.left.flat_appLE U.2 V.2 le_rfl)
  have : Algebra.QuasiFinite Γ(Y.left, U.1) Γ(X.left, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 le_rfl)
  have : Module.FinitePresentation Γ(Y.left, U.1) Γ(X.left, V.1) :=
    Module.finitePresentation_of_finite _ _
  have : Module.Projective Γ(Y.left, U.1) Γ(X.left, V.1) :=
    Module.Flat.projective_of_finitePresentation
  let SF := selfFactorization Γ(Y.left, U.1) Γ(X.left, V.1)
  refine (D.localEquiv U V le_rfl SF).injective ?_
  refine Eq.trans ?_ (localEquiv_relativeTraceSection D U V le_rfl SF).symm
  refine (congrArg (D.localEquiv U V le_rfl SF)
    (upperShriekDualSection_restrict f T j U.1)).trans ?_
  refine (RelativeDualizingModuleData.ofFiniteTrace_localEquiv_selfFactorization _
    (finiteTrace (selfFiniteFactorization f)) (bijective_traceDual_finiteTrace _) _ U _).trans ?_
  have hdual : traceDual f.left (finiteTrace (selfFiniteFactorization f)) U.1
      ((finiteZeroTwisted (selfFiniteFactorization f)).presheaf.map
        (homOfLE (le_top : f.left ⁻¹ᵁ U.1 ≤ ⊤)).op
        (Scheme.Modules.Hom.app (dualMorphism f T) ⊤ (FiniteTrace.unitOne ⊤))) =
      (finiteProjectiveTrace Γ(Y.left, U.1) Γ(X.left, V.1)).comp
        (Algebra.lmul Γ(Y.left, U.1) Γ(X.left, V.1)).toLinearMap :=
    LinearMap.ext fun b => (traceDual_dualMorphism f T U.1 b).trans (hT U b)
  rw [hdual]
  exact (isTraceElement_iff_eq_traceCandidate SF _).1
    (isTraceElement_finiteFlatTraceElement Γ(Y.left, U.1) Γ(X.left, V.1))

/-- **Stacks Project, Tag 0BVI.** Let `f : X ⟶ Y` be a finite flat morphism of schemes separated
and of finite type over a Noetherian scheme `S`, and `f^!` the upper shriek of Tag 0A9Y at any
compactification `j`. The trace `Trace_f : f_*𝒪_X ⟶ 𝒪_Y` of Section 0BVH corresponds under
duality to a global section of `H⁰(f^!𝒪_Y)`; via the identification `H⁰(f^!𝒪_Y) = ω_{X/Y}` of
Tag 0BUL (`upperShriekRelativeDualizingModuleData`), this section is the trace element
`τ_{X/Y}` of Tag 0BVJ. -/
@[stacks 0BVI]
theorem upperShriekDualSection_pushforwardTrace (j : CompactificationOf (Over.mk f.left)) :
    upperShriekDualSection f (pushforwardTrace f.left) j =
      relativeTraceSection (upperShriekRelativeDualizingModuleData f j) := by
  have key : ∀ D : RelativeDualizingModuleData f.left,
      D = (selfFiniteFactorization f).relativeDualizingModuleData j →
        ∀ h : D.sheaf = upperShriekStructureSheafZeroth f j,
          upperShriekDualSection f (pushforwardTrace f.left) j = h ▸ relativeTraceSection D := by
    rintro D rfl h
    exact upperShriekDualSection_eq_relativeTraceSection f _
      (fun U b => pushforwardTrace_app f.left U b) j
  exact key _ (upperShriekRelativeDualizingModuleData_of_isFinite f j) rfl

end Stacks.Duality
