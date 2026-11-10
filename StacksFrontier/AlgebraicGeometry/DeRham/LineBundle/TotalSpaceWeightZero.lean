module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.AffineChart
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceGradedChart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
import StacksCore.Tactic.StacksAttribute

/-!
# The weight-zero de Rham complex of the total space of a line bundle

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `π : 𝕃 ⟶ X` its
total space. The pullback of forms along `π` identifies `Ω^p_{X/S}` with the degree-zero part
`Ω^p_{𝕃/S, 0}` of `π_* Ω^p_{𝕃/S}`, and these identifications form an isomorphism of complexes
`Ω^•_{X/S} ≅ Ω^•_{𝕃/S, 0}`.

## Main definitions

* `Stacks.LineBundle.Situation.formsIsoGradedTotalForms`: The isomorphism
  `Ω^p_{X/S} ≅ Ω^p_{𝕃/S, 0}`.
* `Stacks.LineBundle.Situation.totalWeightZeroComplex`: The weight-zero de Rham complex
  `Ω^•_{𝕃/S, 0}`, in abelian sheaves on `X`.
* `Stacks.LineBundle.Situation.deRhamComplexIsoTotalWeightZero`: The isomorphism of complexes
  `Ω^•_{X/S} ≅ Ω^•_{𝕃/S, 0}`.

## Main results

* `Stacks.LineBundle.Situation.mono_formsPullback`: The pullback of forms along `π` is a
  monomorphism.
* `Stacks.LineBundle.Situation.imageSubmodule_formsPullback`: The image of the pullback of forms
  is `Ω^p_{𝕃/S, 0}`.
* `Stacks.LineBundle.Situation.deRhamComplexIsoTotalWeightZero_hom_ι`: The isomorphism
  `Ω^•_{X/S} ≅ Ω^•_{𝕃/S, 0}` followed by the inclusion is the canonical map
  `Ω^•_{X/S} ⟶ π_* Ω^•_{𝕃/S}`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite Polynomial

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### Charts of the total space -/

/-- The pullback of forms along `π` on sections over an open `U` of `X`, with its value seated at
`Γ(Ω^p_{𝕃/S}, π⁻¹U)`. -/
def Situation.totalPullbackForms (p : ℕ) (U : D.X.Opens)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ U) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections
    D.totalSpaceToBase D.f D.totalToBase (𝟙 D.S) D.totalSpaceToBase_comp p ω

/-- `Situation.totalPullbackForms` is the pullback of forms `Situation.formsPullback` on sections
over `U`. -/
theorem Situation.totalPullbackForms_eq (p : ℕ) (U : D.X.Opens)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    D.totalPullbackForms p U ω = (D.formsPullback p).app U ω :=
  rfl

/-- The pullback of forms on sections is additive. -/
theorem Situation.totalPullbackForms_add (p : ℕ) (U : D.X.Opens)
    (ω χ : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), U)) :
    D.totalPullbackForms p U (ω + χ) = D.totalPullbackForms p U ω + D.totalPullbackForms p U χ :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections_add _ _ _ _ _ p ω χ

/-- **A chart of the total space of the line bundle**: an affine open `U` of `X` lying over an
affine open `V` of `S`, with a trivialization of `L` over `U`. Over a chart the total space is
`Spec Γ(X, U)[X]` over `Spec Γ(S, V)`. -/
structure Situation.TotalChart extends D.AffineChart where
  /-- A trivialization of `L` over `U`. -/
  triv : D.L.over U.1 ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U.1)

namespace Situation.TotalChart

variable {D} (c : D.TotalChart)

/-- The basis of the sections of `L` over `U` given by the trivialization. -/
abbrev basis : Module.Basis PUnit.{u + 1} Γ(D.X, c.U.1) Γ(D.L, c.U.1) :=
  D.trivializationBasis c.U.1 c.triv

/-- The functions on `π⁻¹U`. -/
abbrev B : Type u := Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ c.U.1)

/-- The preimage of `U` under `π` lies in the preimage of `V` under `𝕃 ⟶ S`. -/
theorem preimage_le : D.totalSpaceToBase ⁻¹ᵁ c.U.1 ≤ D.totalToBase ⁻¹ᵁ c.V.1 :=
  Situation.preimage_le_preimage_comp c.le

/-- The preimage `π⁻¹U` of the affine open `U` is affine. -/
theorem isAffineOpen_preimage : IsAffineOpen (D.totalSpaceToBase ⁻¹ᵁ c.U.1) :=
  c.U.2.preimage D.totalSpaceToBase

/-- `Γ(𝕃, π⁻¹U)` as a `Γ(S, V)`-algebra. -/
abbrev algebraRB : Algebra c.R c.B :=
  (D.totalToBase.appLE c.V.1 _ c.preimage_le).hom.toAlgebra

/-- `Γ(𝕃, π⁻¹U)` as a `Γ(X, U)`-algebra, along `π`. -/
abbrev algebraAB : Algebra c.A c.B := (D.totalSpaceToBase.app c.U.1).hom.toAlgebra

attribute [local instance] Situation.AffineChart.algebraRA algebraRB algebraAB

/-- The algebra structures on `Γ(S, V)`, `Γ(X, U)` and `Γ(𝕃, π⁻¹U)` form a scalar tower. -/
theorem isScalarTower : IsScalarTower c.R c.A c.B :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change (D.totalToBase.appLE c.V.1 _ c.preimage_le).hom r =
      (D.totalSpaceToBase.app c.U.1).hom ((D.f.appLE c.V.1 c.U.1 c.le).hom r)
    rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

attribute [local instance] isScalarTower

/-- The Kähler differentials of `Γ(S, V) → Γ(𝕃, π⁻¹U)`. -/
abbrev ΩB : ModuleCat.{u} c.B :=
  CommRingCat.KaehlerDifferential (D.totalToBase.appLE c.V.1 _ c.preimage_le)

/-- The relative forms of `𝕃` over `π⁻¹U`, as Kähler forms. -/
abbrev formsL (p : ℕ) :
    ModuleCat.of c.B Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ c.U.1) ≅
      ModuleCat.of c.B (⋀[c.B]^p c.ΩB) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso D.totalToBase
    c.isAffineOpen_preimage c.V.2 c.preimage_le p

/-- The pullback of forms over a chart is semilinear over `π^♯`. -/
theorem formsL_formsPullback_smul (p : ℕ) (a0 : c.A) (y : ⋀[c.A]^p c.ΩA) :
    (c.formsL p).hom (D.totalPullbackForms p c.U.1 ((c.formsX p).inv (a0 • y : ⋀[c.A]^p c.ΩA))) =
      (D.totalSpaceToBase.app c.U.1).hom a0 •
        (c.formsL p).hom (D.totalPullbackForms p c.U.1 ((c.formsX p).inv y)) := by
  rw [Situation.totalPullbackForms, Situation.totalPullbackForms]
  convert Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_pushforwardSections_smul
    D.totalSpaceToBase D.f D.totalToBase (𝟙 D.S) c.U.2 c.isAffineOpen_preimage c.V.2 c.V.2 c.le
    c.preimage_le D.totalSpaceToBase_comp p a0 y using 1

/-- The pullback of forms over a chart on a wedge of differentials. -/
theorem formsL_formsPullback_ιMulti (p : ℕ) (a : Fin p → c.A) :
    (c.formsL p).hom (D.totalPullbackForms p c.U.1 ((c.formsX p).inv
      (exteriorPower.ιMulti c.A p fun i => CommRingCat.KaehlerDifferential.d (a i) :
        ⋀[c.A]^p c.ΩA))) =
      (exteriorPower.ιMulti c.B p fun i =>
        CommRingCat.KaehlerDifferential.d ((D.totalSpaceToBase.app c.U.1).hom (a i)) :
          ⋀[c.B]^p c.ΩB) := by
  rw [Situation.totalPullbackForms,
    Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections_apply]
  convert AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_deRhamFormsPushforwardHom_ιMulti_d
    D.totalSpaceToBase D.f D.totalToBase (𝟙 D.S) c.U.2 c.isAffineOpen_preimage c.V.2 c.V.2 c.le
    c.preimage_le D.totalSpaceToBase_comp p a using 1

/-- The restriction of Kähler forms along `Γ(X, U) → Γ(𝕃, π⁻¹U)` on a generator. -/
theorem mapExteriorPower_gen (p : ℕ) (a : Fin (p + 1) → c.A) :
    KaehlerDifferential.mapExteriorPower c.R c.A c.B p (a 0 • exteriorPower.ιMulti c.A p fun i =>
        KaehlerDifferential.D c.R c.A (a i.succ)) =
      (D.totalSpaceToBase.app c.U.1).hom (a 0) • exteriorPower.ιMulti c.B p fun i =>
        KaehlerDifferential.D c.R c.B ((D.totalSpaceToBase.app c.U.1).hom (a i.succ)) := by
  rw [LinearMap.map_smul, KaehlerDifferential.mapExteriorPower_ιMulti, ← algebraMap_smul c.B (a 0)]
  exact congrArg (algebraMap c.A c.B (a 0) • ·) (congrArg (exteriorPower.ιMulti c.B p)
    (funext fun i => KaehlerDifferential.map_D c.R c.R c.A c.B (a i.succ)))

/-- **The pullback of forms along `π`, read through the two identifications, is the restriction
of Kähler forms along `Γ(X, U) → Γ(𝕃, π⁻¹U)`.** -/
theorem formsL_formsPullback (p : ℕ) (x : ⋀[c.A]^p c.ΩA) :
    (c.formsL p).hom (D.totalPullbackForms p c.U.1 ((c.formsX p).inv x)) =
      KaehlerDifferential.mapExteriorPower c.R c.A c.B p x := by
  let G' : ⋀[c.A]^p c.ΩA →+ ⋀[c.B]^p c.ΩB :=
    AddMonoidHom.mk' (KaehlerDifferential.mapExteriorPower c.R c.A c.B p) (map_add _)
  let F : ⋀[c.A]^p c.ΩA →+ ⋀[c.B]^p c.ΩB :=
    AddMonoidHom.mk' (fun x => (c.formsL p).hom (D.totalPullbackForms p c.U.1 ((c.formsX p).inv x)))
      fun x y => by rw [map_add, Situation.totalPullbackForms_add, map_add]
  have hD : Submodule.span c.A
      (Set.range fun b : c.A => (CommRingCat.KaehlerDifferential.d b : c.ΩA)) = ⊤ :=
    @KaehlerDifferential.span_range_derivation c.R c.A _ _ c.algebraRA
  have key : F = G' := Stacks.AlgebraicGeometry.AffineOpenDeRham.addMonoidHom_ext_of_span_int_eq_top
    (Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ)
      (fun b : c.A => (CommRingCat.KaehlerDifferential.d b : c.ΩA)) hD p) (by
        rintro _ ⟨a, rfl⟩
        simp only [F, G', AddMonoidHom.mk'_apply]
        rw [c.formsL_formsPullback_smul p (a 0)
          (exteriorPower.ιMulti c.A p fun i => CommRingCat.KaehlerDifferential.d (a i.succ))]
        exact (congrArg (fun z => (D.totalSpaceToBase.app c.U.1).hom (a 0) • z)
          (c.formsL_formsPullback_ιMulti p (fun i => a i.succ))).trans
          (c.mapExteriorPower_gen p a).symm)
  exact DFunLike.congr_fun key x

/-- The polynomial model of the chart. -/
abbrev equiv : c.A[X] ≃ₐ[c.A] c.B := D.polynomialChartAlgEquiv c.U.2 c.basis

/-- **Over a chart the pullback of forms along `π` is injective on sections.** -/
theorem injective_formsPullback (p : ℕ) : Function.Injective ((D.formsPullback p).app c.U.1) := by
  have hinj := PolynomialDeRham.injective_mapExteriorPower_of_algEquiv (R := c.R) c.equiv p
  have key (ω : Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1)) :
      (c.formsL p).hom (D.totalPullbackForms p c.U.1 ω) =
        KaehlerDifferential.mapExteriorPower c.R c.A c.B p ((c.formsX p).hom ω) := by
    rw [← c.formsL_formsPullback, Iso.hom_inv_id_apply]
  intro ω₁ ω₂ h
  have h' : D.totalPullbackForms p c.U.1 ω₁ = D.totalPullbackForms p c.U.1 ω₂ := h
  have h3 := hinj ((key ω₁).symm.trans ((congrArg (c.formsL p).hom.hom h').trans (key ω₂)))
  simpa using congrArg (c.formsX p).inv h3

/-- **The forms of `𝕃` over `π⁻¹U`, read as Kähler forms** `⋀^p Ω[Γ(𝕃, π⁻¹U)⁄Γ(S, V)]`, on the
sections over `U` of the pushed-forward forms. -/
def formsLF (p : ℕ) : (D.totalFormsPushforward p).val.obj (op c.U.1) →+ ⋀[c.B]^p Ω[c.B⁄c.R] :=
  AddMonoidHom.mk' (fun ω => (c.formsL p).hom (D.toForms p c.U.1 ω)) fun ω χ => by
    rw [map_add, map_add]
    rfl

/-- `formsLF` is the Kähler form of the corresponding section of `Ω^p_{𝕃/S}`. -/
theorem formsLF_apply (p : ℕ) (ω : (D.totalFormsPushforward p).val.obj (op c.U.1)) :
    c.formsLF p ω = (c.formsL p).hom (D.toForms p c.U.1 ω) :=
  rfl

/-- `formsLF` is semilinear over `Γ(X, U) → Γ(𝕃, π⁻¹U)`. -/
theorem formsLF_smul (p : ℕ) (r : D.X.ringCatSheaf.obj.obj (op c.U.1))
    (ω : (D.totalFormsPushforward p).val.obj (op c.U.1)) :
    c.formsLF p (r • ω) = algebraMap c.A c.B (id (α := c.A) r) • c.formsLF p ω := by
  rw [formsLF_apply, formsLF_apply, D.toForms_smul, map_smul]
  rfl

/-- **The Kähler form of a homogeneous form of degree `n` over the chart lies in the weight-`n`
component of the polynomial model.** -/
theorem formsLF_mem_of_mem_homogeneousSpan {p n : ℕ}
    {x : (D.totalFormsPushforward p).val.obj (op c.U.1)}
    (hx : x ∈ D.homogeneousSpan p n c.U.1) :
    c.formsLF p x ∈ KaehlerDifferential.gradedDifferentialFormComponent
      (PolynomialDeRham.polyGrading c.R c.A c.B c.equiv) p n := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨deg, a, ha, hn, hy⟩ := hy
      have hmem : ∀ i, a i ∈ PolynomialDeRham.polyGrading c.R c.A c.B c.equiv (deg i) := fun i => by
        obtain ⟨d, hd⟩ := (D.exists_totalFunction_iff c.U c.basis (deg i) (a i)).1 (ha i)
        exact ⟨monomial (deg i) d, ⟨d, rfl⟩, hd⟩
      rw [formsLF_apply, (D.toForms_apply p c.U.1 y).trans hy,
        Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_smul_homogeneousProdLeft
          D.totalToBase c.isAffineOpen_preimage c.V.2 c.preimage_le p (a 0) fun i => a i.succ]
      exact KaehlerDifferential.homogeneousDifferentialForm_mem_gradedDifferentialFormComponent
        _ p deg (fun i => ⟨a i, hmem i⟩) n hn
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
      rw [formsLF_smul]
      exact PolynomialDeRham.algebraMap_smul_mem_polyComponent _ (id (α := c.A) r) hy

/-- The exterior powers of the two spellings of the Kähler differentials of `Γ(S, V) → Γ(𝕃, π⁻¹U)`
are the same module; this is the identity between them. -/
def toΩB (p : ℕ) : ⋀[c.B]^p c.ΩB ≃ₗ[c.B] ⋀[c.B]^p Ω[c.B⁄c.R] :=
  CommRingCat.KaehlerDifferential.exteriorPowerEquiv (D.totalToBase.appLE c.V.1 _ c.preimage_le) p

/-- `toΩB` on a multiple of a wedge of differentials. -/
theorem toΩB_smul_ιMulti (p : ℕ) (a : Fin (p + 1) → c.B) :
    c.toΩB p (a 0 • exteriorPower.ιMulti c.B p fun i =>
      CommRingCat.KaehlerDifferential.d (a i.succ)) =
      a 0 • exteriorPower.ιMulti c.B p fun i => KaehlerDifferential.D c.R c.B (a i.succ) :=
  rfl

/-- **The relative forms of `𝕃` over `π⁻¹U`, as Kähler forms** in Mathlib's spelling of the Kähler
differentials of `Γ(S, V) → Γ(𝕃, π⁻¹U)`. -/
def formsLK (p : ℕ) : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ c.U.1) ≃ₗ[c.B]
    ⋀[c.B]^p Ω[c.B⁄c.R] :=
  (c.formsL p).toLinearEquiv.trans (c.toΩB p)

/-- `formsLK` is `formsL` followed by `toΩB`. -/
theorem formsLK_apply (p : ℕ) (ω : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ c.U.1)) :
    c.formsLK p ω = c.toΩB p ((c.formsL p).hom ω) :=
  rfl

/-- **A weight-`n` Kähler form of the polynomial model is a section of `Ω^p_{𝕃/S, n}`.** -/
theorem formsLK_symm_mem_of_mem {p n : ℕ} {x : ⋀[c.B]^p Ω[c.B⁄c.R]}
    (hx : x ∈ KaehlerDifferential.gradedDifferentialFormComponent
      (PolynomialDeRham.polyGrading c.R c.A c.B c.equiv) p n) :
    D.ofForms p c.U.1 ((c.formsLK p).symm x) ∈ (D.gradedTotalForms p n).obj (op c.U.1) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨deg, a, hn, rfl⟩ := hy
      have ha : ∀ i, ∃ x, D.totalFunction (deg i) c.U.1 x = (a i).1 := fun i => by
        obtain ⟨_, ⟨d, rfl⟩, hd⟩ := (a i).2
        exact (D.exists_totalFunction_iff c.U c.basis (deg i) _).2 ⟨d, hd⟩
      have e : c.formsLK p ((a 0).1 • id (α := Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ c.U.1))
          ((Scheme.Hom.deRhamAlgebras
              D.totalToBase).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
            (op (D.totalSpaceToBase ⁻¹ᵁ c.U.1)) p fun i =>
              SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.totalToBase) _ (a i.succ).1)) =
          (a 0).1 • exteriorPower.ιMulti c.B p fun i =>
            KaehlerDifferential.D c.R c.B (a i.succ).1 := by
        rw [formsLK_apply,
          Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_smul_homogeneousProdLeft
            D.totalToBase c.isAffineOpen_preimage c.V.2 c.preimage_le p (a 0).1
            fun i => (a i.succ).1]
        exact c.toΩB_smul_ιMulti p fun i => (a i).1
      rw [← e, LinearEquiv.symm_apply_apply]
      exact D.mem_gradedTotalForms (W := c.U.1) ⟨deg, fun i => (a i).1, ha, hn, rfl⟩
  | zero =>
      rw [map_zero, map_zero]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
      rw [← algebraMap_smul c.B r y, LinearEquiv.map_smul,
        IsScalarTower.algebraMap_apply c.R c.A c.B r]
      change D.ofForms p c.U.1 ((D.totalSpaceToBase.app c.U.1).hom (algebraMap c.R c.A r) •
        (c.formsLK p).symm y) ∈ _
      rw [D.ofForms_smul]
      exact Submodule.smul_mem _ _ hy

end Situation.TotalChart

/-! ### The pullback of forms is a monomorphism -/

/-- **The pullback of forms along `π` is injective on sections over every open.** -/
theorem Situation.injective_formsPullback_app (p : ℕ) (W : D.X.Opens) :
    Function.Injective ((D.formsPullback p).app W) := by
  intro ω₁ ω₂ h
  rw [← sub_eq_zero]
  have hmem : ω₁ - ω₂ ∈ (_root_.SheafOfModules.Submodule.ker
      (𝟙 (Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)))).obj (op W) := by
    refine D.mem_of_forall_chart _ _ fun U V hUW hU hV e ⟨t⟩ => ?_
    let c : D.TotalChart := ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, e⟩, t⟩
    refine (_root_.SheafOfModules.Submodule.mem_ker _ _ _).2 (c.injective_formsPullback p ?_)
    refine (PresheafOfModules.naturality_apply (D.formsPullback p).val (homOfLE hUW).op
      (ω₁ - ω₂)).trans ?_
    have hz : (D.formsPullback p).val.app (op W) (ω₁ - ω₂) = 0 :=
      (map_sub ((D.formsPullback p).val.app (op W)).hom ω₁ ω₂).trans (sub_eq_zero.2 h)
    exact (congrArg _ hz).trans ((map_zero _).trans (map_zero _).symm)
  exact (_root_.SheafOfModules.Submodule.mem_ker _ _ _).1 hmem

/-- **The pullback of forms along `π` is a monomorphism.** -/
instance Situation.mono_formsPullback (p : ℕ) : Mono (D.formsPullback p) where
  right_cancellation g h H := by
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
    ext z
    exact D.injective_formsPullback_app p U.unop
      (congrArg (fun k => k.val.app U z) H)

/-! ### The image of the pullback of forms is the degree-zero part -/

/-- The pullback of a multiple of an exact wedge of functions on `X`. -/
theorem Situation.formsPullback_smul_homogeneousProdLeft (p : ℕ) (W : D.X.Opens)
    (r₀ : Γ(D.X, W)) (r : Fin p → Γ(D.X, W)) :
    id (α := Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W)) ((D.formsPullback p).app W
      (id (α := D.X.sheaf.obj.obj (op W)) r₀ •
        (Scheme.Hom.deRhamAlgebras D.f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        (op W) p fun i =>
          _root_.AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.f)
            (op W) (r i))) =
      (D.totalSpaceToBase.app W).hom r₀ • id (α := Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W))
        ((Scheme.Hom.deRhamAlgebras
            D.totalToBase).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
          (op (D.totalSpaceToBase ⁻¹ᵁ W)) p fun i =>
            SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.totalToBase) _
              ((D.totalSpaceToBase.app W).hom (r i))) :=
  (Scheme.Hom.deRhamFormsPushforwardHom_smul D.totalSpaceToBase D.f D.totalToBase (𝟙 D.S)
      D.totalSpaceToBase_comp (p : ℤ) (op W) r₀ _).trans
    (congrArg (fun z => (D.totalSpaceToBase.app W).hom r₀ •
        id (α := Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W)) z)
      (Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft D.totalSpaceToBase D.f
        D.totalToBase (𝟙 D.S) D.totalSpaceToBase_comp (op W) p r))

/-- **Every homogeneous form of degree zero is pulled back from `X`.** -/
theorem Situation.exists_formsPullback_eq_of_isHomogeneousTotalForm {p : ℕ} {W : D.X.Opens}
    {ω : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W)} (hω : D.IsHomogeneousTotalForm W p 0 ω) :
    ∃ α, (D.formsPullback p).app W α = ω := by
  obtain ⟨deg, a, ha, hn, rfl⟩ := hω
  obtain rfl : deg = fun _ => 0 :=
    funext fun i => (Finset.sum_eq_zero_iff.1 hn.symm) i (Finset.mem_univ i)
  choose x hx using ha
  choose r hr using fun i => D.exists_totalFunction_zero W (x i)
  obtain rfl : a = fun i => (D.totalSpaceToBase.app W).hom (r i) :=
    funext fun i => (hx i).symm.trans (hr i)
  exact ⟨id (α := D.X.sheaf.obj.obj (op W)) (r 0) •
    (Scheme.Hom.deRhamAlgebras D.f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
    (op W) p fun i => _root_.AlgebraicGeometry.SheafOfModules.exactOne
      (Scheme.Hom.deRhamAlgebras D.f) (op W) (r i.succ),
    D.formsPullback_smul_homogeneousProdLeft p W (r 0) fun i => r i.succ⟩

/-- **The image of the pullback of forms `Ω^p_{X/S} ⟶ π_* Ω^p_{𝕃/S}` is the degree-zero part
`Ω^p_{𝕃/S, 0}`.** -/
theorem Situation.imageSubmodule_formsPullback (p : ℕ) :
    Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (D.formsPullback p) =
      D.gradedTotalForms p 0 := by
  refine le_antisymm (fun X s hs => ?_) ((D.gradedTotalForms_le_iff _).2 fun W ω hω => ?_)
  · refine (D.gradedTotalForms p 0).isSheaf s
      (GrothendieckTopology.superset_covering _ (fun V g hg => ?_) hs)
    obtain ⟨m, hm⟩ := hg
    exact (congrArg (· ∈ (D.gradedTotalForms p 0).obj (op V)) hm).mp
      (D.formsPullback_mem_gradedTotalForms_zero p V m)
  · obtain ⟨α, rfl⟩ := D.exists_formsPullback_eq_of_isHomogeneousTotalForm hω
    exact Stacks.SheafOfModules.ImageSubsheaf.apply_mem_imageSubmodule (D.formsPullback p) α

/-! ### The degreewise identification -/

/-- Equal submodule sheaves have isomorphic sheaves of modules, compatibly with the inclusions. -/
theorem _root_.SheafOfModules.Submodule.eqToHom_ι {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : _root_.SheafOfModules.{u} R}
    {N₁ N₂ : M.Submodule} (h : N₁ = N₂) :
    eqToHom (congrArg _root_.SheafOfModules.Submodule.toSheafOfModules h) ≫ N₂.ι = N₁.ι := by
  subst h
  simp

/-- **The relative `p`-forms of `X` over `S` are the degree-zero part of the pushed-forward
relative `p`-forms of the total space**: `Ω^p_{X/S} ≅ Ω^p_{𝕃/S, 0}`, through the pullback of
forms along `π`. -/
def Situation.formsIsoGradedTotalForms (p : ℕ) :
    Scheme.Hom.relativeDifferentialForms D.f (p : ℤ) ≅ (D.gradedTotalForms p 0).toSheafOfModules :=
  haveI : @Mono (_root_.SheafOfModules.{u} D.X.ringCatSheaf) _ _ _ (D.formsPullback p) :=
    D.mono_formsPullback p
  Stacks.SheafOfModules.ImageSubsheaf.imageIso (D.formsPullback p) ≪≫
    eqToIso (congrArg _root_.SheafOfModules.Submodule.toSheafOfModules
      (D.imageSubmodule_formsPullback p))

/-- **The identification `Ω^p_{X/S} ≅ Ω^p_{𝕃/S, 0}` is the pullback of forms**: followed by the
inclusion of the degree-zero part it is the pullback of forms along `π`. -/
@[reassoc (attr := simp)]
theorem Situation.formsIsoGradedTotalForms_hom_ι (p : ℕ) :
    (D.formsIsoGradedTotalForms p).hom ≫ (D.gradedTotalForms p 0).ι = D.formsPullback p := by
  have h := SheafOfModules.Submodule.eqToHom_ι (D.imageSubmodule_formsPullback p)
  have h' := Stacks.SheafOfModules.ImageSubsheaf.toImage_ι (D.formsPullback p)
  exact (Category.assoc _ _ _).trans ((congrArg
    (fun k => Stacks.SheafOfModules.ImageSubsheaf.toImage (D.formsPullback p) ≫ k) h).trans h')

/-! ### The weight-zero de Rham complex -/

section Complex

/-- The de Rham complex `Ω^•_{X/S}`, in abelian sheaves. -/
abbrev Situation.baseDeRhamComplex :
    CochainComplex (Stacks.Cohomology.Leray.AbelianSheaf D.X.carrier) ℕ :=
  _root_.AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras D.f)
    (_root_.AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))

/-- The pushforward `π_* Ω^•_{𝕃/S}` of the de Rham complex of the total space, in abelian
sheaves on `X`. -/
abbrev Situation.totalDeRhamPushforwardComplex :
    CochainComplex (Stacks.Cohomology.Leray.AbelianSheaf D.X.carrier) ℕ :=
  ((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u}
      D.totalSpaceToBase.base).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (_root_.AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex
      (Scheme.Hom.deRhamAlgebras D.totalToBase)
      (_root_.AlgebraicGeometry.SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras D.totalToBase)))

/-- The underlying abelian sheaf of `Ω^p_{𝕃/S, 0}`. -/
abbrev Situation.totalWeightZeroTerm (p : ℕ) : Stacks.Cohomology.Leray.AbelianSheaf D.X.carrier :=
  (_root_.SheafOfModules.toSheaf (structureSheafRing D.X.toRingedSpace)).obj
    (D.gradedTotalForms p 0).toSheafOfModules

/-- The inclusion `Ω^p_{𝕃/S, 0} ⟶ π_* Ω^p_{𝕃/S}`, in abelian sheaves. -/
def Situation.totalWeightZeroι (p : ℕ) :
    D.totalWeightZeroTerm p ⟶ D.totalDeRhamPushforwardComplex.X p :=
  (_root_.SheafOfModules.toSheaf (structureSheafRing D.X.toRingedSpace)).map
    (D.gradedTotalForms p 0).ι

/-- The inclusion `Ω^p_{𝕃/S, 0} ⟶ π_* Ω^p_{𝕃/S}` is a monomorphism of abelian sheaves. -/
instance Situation.mono_totalWeightZeroι (p : ℕ) : Mono (D.totalWeightZeroι p) :=
  @Functor.map_mono _ _ _ _ (_root_.SheafOfModules.toSheaf (structureSheafRing D.X.toRingedSpace))
    _ _ _ (D.gradedTotalForms p 0).ι
    (_root_.SheafOfModules.Submodule.instMonoι (D.gradedTotalForms p 0))

/-- The identification `Ω^p_{X/S} ≅ Ω^p_{𝕃/S, 0}`, in abelian sheaves. -/
def Situation.totalWeightZeroIsoTerm (p : ℕ) : D.baseDeRhamComplex.X p ≅ D.totalWeightZeroTerm p :=
  (_root_.SheafOfModules.toSheaf (structureSheafRing D.X.toRingedSpace)).mapIso
    (D.formsIsoGradedTotalForms p)

/-- The identification `Ω^p_{X/S} ≅ Ω^p_{𝕃/S, 0}` followed by the inclusion into
`π_* Ω^p_{𝕃/S}` is the degree-`p` component of the canonical map `Ω^•_{X/S} ⟶ π_* Ω^•_{𝕃/S}`. -/
@[reassoc]
theorem Situation.totalWeightZeroIsoTerm_hom_ι (p : ℕ) :
    (D.totalWeightZeroIsoTerm p).hom ≫ D.totalWeightZeroι p = D.deRhamPushforward.f p := by
  refine ((_root_.SheafOfModules.toSheaf
    (structureSheafRing D.X.toRingedSpace)).map_comp _ _).symm.trans ?_
  exact congrArg (_root_.SheafOfModules.toSheaf (structureSheafRing D.X.toRingedSpace)).map
    (D.formsIsoGradedTotalForms_hom_ι p)

/-- The differential of the weight-zero complex: the de Rham differential of `π_*Ω^•_{𝕃/S}`
restricted to `Ω^•_{𝕃/S, 0}` (see `Stacks.LineBundle.Situation.totalWeightZeroD_ι`). -/
def Situation.totalWeightZeroD (p q : ℕ) : D.totalWeightZeroTerm p ⟶ D.totalWeightZeroTerm q :=
  (D.totalWeightZeroIsoTerm p).inv ≫ D.baseDeRhamComplex.d p q ≫ (D.totalWeightZeroIsoTerm q).hom

/-- **The differential of the weight-zero complex is the restriction of the de Rham differential
of `π_*Ω^•_{𝕃/S}`.** -/
@[reassoc]
theorem Situation.totalWeightZeroD_ι (p q : ℕ) :
    D.totalWeightZeroD p q ≫ D.totalWeightZeroι q =
      D.totalWeightZeroι p ≫ D.totalDeRhamPushforwardComplex.d p q := by
  rw [Situation.totalWeightZeroD, Category.assoc, Category.assoc, D.totalWeightZeroIsoTerm_hom_ι]
  refine (congrArg (fun k => (D.totalWeightZeroIsoTerm p).inv ≫ k)
    (D.deRhamPushforward.comm p q).symm).trans ?_
  rw [← D.totalWeightZeroIsoTerm_hom_ι_assoc, Iso.inv_hom_id_assoc]

/-- **The weight-zero de Rham complex `Ω^•_{𝕃/S, 0}`** of the total space of the line bundle,
in abelian sheaves on `X`: the subcomplex of `π_* Ω^•_{𝕃/S}` whose degree-`p` term is the
degree-zero part `Ω^p_{𝕃/S, 0}`. -/
def Situation.totalWeightZeroComplex :
    CochainComplex (Stacks.Cohomology.Leray.AbelianSheaf D.X.carrier) ℕ where
  X := D.totalWeightZeroTerm
  d := D.totalWeightZeroD
  shape p q h := by
    rw [Situation.totalWeightZeroD, D.baseDeRhamComplex.shape p q h, Limits.zero_comp,
      Limits.comp_zero]
  d_comp_d' p q r _ _ := by
    simp only [Situation.totalWeightZeroD, Category.assoc, Iso.hom_inv_id_assoc,
      HomologicalComplex.d_comp_d_assoc, Limits.zero_comp, Limits.comp_zero]

/-- **The inclusion of the weight-zero complex** `Ω^•_{𝕃/S, 0} ⟶ π_* Ω^•_{𝕃/S}`, degreewise the
inclusion of the degree-zero part. -/
def Situation.totalWeightZeroComplexι :
    D.totalWeightZeroComplex ⟶ D.totalDeRhamPushforwardComplex where
  f := D.totalWeightZeroι
  comm' p q _ := (D.totalWeightZeroD_ι p q).symm

/-- The inclusion of the weight-zero complex is a monomorphism in each degree. -/
instance Situation.mono_totalWeightZeroComplexι_f (p : ℕ) : Mono (D.totalWeightZeroComplexι.f p) :=
  D.mono_totalWeightZeroι p

/-- Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `π : 𝕃 ⟶ X`
its total space. Then `Ω^•_{X/S} = Ω^•_{𝕃/S, 0}` as complexes: the de Rham complex of `X` over
`S` is isomorphic to the weight-zero subcomplex of `π_* Ω^•_{𝕃/S}`, through the canonical map
`Stacks.LineBundle.Situation.deRhamPushforward` (see
`Stacks.LineBundle.Situation.deRhamComplexIsoTotalWeightZero_hom_ι`).

The printed statement writes `Ω^•_{L/X, 0}`; the subscript `L/X` is a misprint for `L/S`: the
relative forms of `L` over `X` vanish in degree one in weight zero, and the paragraph before the
lemma as well as its use in the proof of Tag 0FUK (`π_*Ω^a_{L/S} = Ω^a_{P/S} ⊕ ⋯`) concern
`L/S`. -/
@[stacks 0FUH "clause (2): `Ω^•_{X/S} = Ω^•_{L/S, 0}` as complexes (printed `L/X`, a misprint
for `L/S`)"]
def Situation.deRhamComplexIsoTotalWeightZero : D.baseDeRhamComplex ≅ D.totalWeightZeroComplex :=
  HomologicalComplex.Hom.isoOfComponents D.totalWeightZeroIsoTerm fun p q _ => by
    change (D.totalWeightZeroIsoTerm p).hom ≫ D.totalWeightZeroD p q = _
    rw [Situation.totalWeightZeroD, Iso.hom_inv_id_assoc]
    rfl

/-- **The identification of clause (2) is the canonical map**: followed by the inclusion of the
weight-zero complex it is the canonical map `Ω^•_{X/S} ⟶ π_* Ω^•_{𝕃/S}`. -/
theorem Situation.deRhamComplexIsoTotalWeightZero_hom_ι :
    D.deRhamComplexIsoTotalWeightZero.hom ≫ D.totalWeightZeroComplexι = D.deRhamPushforward := by
  ext p : 1
  exact D.totalWeightZeroIsoTerm_hom_ι p

end Complex

end Stacks.LineBundle

end
