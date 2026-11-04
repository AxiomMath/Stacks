module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# The Mayer–Vietoris sequence of two opens, extended by zero

Let `A` and `B` be open subschemes of a scheme `X`, `Λ` a ring and `F` a sheaf of `Λ`-modules
on `X_étale`. Writing `F_V = j_{V!} F|_V` for an open `V`, the sequence

`0 ⟶ F_{A ∩ B} ⟶ F_A ⊕ F_B ⟶ F_{A ∪ B} ⟶ 0`,

with first map `(ι, -ι)` and second map the pair of comparison maps, is short exact. For
`A ∪ B = X` this is `Stacks.EtaleCohomology.shortExact_etaleModuleCoverShortComplex`; here `A ∪ B`
is arbitrary.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleOpensComparison`: the comparison `F_V ⟶ F_{V'}` for opens
  `V ≤ V'`.

## Main results

* `Stacks.EtaleCohomology.mono_etaleModuleExtensionByZeroAdj_counit_app`: `F_V → F` is a
  monomorphism.
* `Stacks.EtaleCohomology.mono_etaleModuleOpensComparison_app`: `F_V ⟶ F_{V'}` is a monomorphism.
* `Stacks.EtaleCohomology.shortExact_etaleModuleOpensShortComplex`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {X : Scheme.{u}}

/-- The geometric point of `X` at `x`, through the separable closure of the residue field. -/
private abbrev gpt (x : X) : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
  residueGeometricPoint X x

private lemma iUnion_range_gpt : ⋃ x : X, Set.range (gpt x).base = Set.univ :=
  Set.eq_univ_of_forall fun x ↦
    Set.mem_iUnion.2 ⟨x, default, residueGeometricPoint_apply X x default⟩

private lemma isIso_map_counit_of_mem (W : X.Opens) {y : X} (hy : y ∈ W)
    (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleInverseImage.{u, r} Λ (gpt y)).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ W.ι).counit.app F)) := by
  have hsub : Set.range (gpt y) ⊆ Set.range W.ι := by
    rintro z ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (gpt y).base t ∈ (W : Set X)
    rw [residueGeometricPoint_apply]
    exact hy
  exact isIso_etaleModuleInverseImage_map_counit_of_factors Λ (gpt y) W.ι
    (IsOpenImmersion.lift W.ι (gpt y) hsub) (IsOpenImmersion.lift_fac _ _ hsub) F

private lemma isZero_map_of_not_mem (W : X.Opens) {y : X} (hy : y ∉ W)
    (F : EtaleModules.{u, r} Λ X) :
    IsZero ((etaleModuleInverseImage.{u, r} Λ (gpt y)).obj
      ((etaleModuleExtensionByZeroOfRestriction.{u, r} Λ W.ι).obj F)) := by
  have hd : Disjoint (Set.range (gpt y).base) (Set.range (W.ι).base) := by
    rw [Set.disjoint_left]
    rintro z ⟨t, rfl⟩ hz
    rw [Scheme.Opens.range_ι] at hz
    rw [show (gpt y).base t = y from residueGeometricPoint_apply X y t] at hz
    exact hy hz
  exact isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ (gpt y) W.ι hd _

private lemma jointlyReflect :
    JointlyReflectIsomorphisms (fun x : X ↦ etaleModuleInverseImage.{u, r} Λ (gpt x)) :=
  ⟨fun γ hγ ↦ isIso_of_isIso_etaleModuleInverseImage_family Λ gpt iUnion_range_gpt γ hγ⟩

/-- **`j_{V!} F|_V ⟶ F` is a monomorphism** for an open `V`. -/
theorem mono_etaleModuleExtensionByZeroAdj_counit_app (W : X.Opens)
    (F : EtaleModules.{u, r} Λ X) :
    Mono ((etaleModuleExtensionByZeroAdj.{u, r} Λ W.ι).counit.app F) := by
  have _ : ∀ x : X, PreservesFiniteLimits (etaleModuleInverseImage.{u, r} Λ (gpt x)) := fun x ↦
    etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ (gpt x)
  have _ : ∀ x : X, Mono ((etaleModuleInverseImage.{u, r} Λ (gpt x)).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ W.ι).counit.app F)) := by
    intro x
    by_cases hx : x ∈ W
    · have := isIso_map_counit_of_mem Λ W hx F
      infer_instance
    · exact (isZero_map_of_not_mem Λ W hx F).mono _
  exact (jointlyReflect Λ).mono _

/-- **`j_{X!} F|_X ⟶ F` is an isomorphism** for the open `⊤`. -/
theorem isIso_etaleModuleExtensionByZeroAdj_counit_app_top (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ (⊤ : X.Opens).ι).counit.app F) := by
  have _ : ∀ x : X, IsIso ((etaleModuleInverseImage.{u, r} Λ (gpt x)).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ (⊤ : X.Opens).ι).counit.app F)) := fun x ↦
    isIso_map_counit_of_mem Λ ⊤ (Set.mem_univ x) F
  exact (jointlyReflect Λ).isIso _

variable (A B : X.Opens)

/-- The comparison `F_V ⟶ F_{V'}` for opens `V ≤ V'`. -/
abbrev etaleModuleOpensComparison {V V' : X.Opens} (h : V ≤ V') :
    etaleModuleExtensionByZeroOfRestriction.{u, r} Λ V.ι ⟶
      etaleModuleExtensionByZeroOfRestriction.{u, r} Λ V'.ι :=
  etaleModuleCoverComparison.{u, r} Λ V.ι V'.ι (X.homOfLE h) (X.homOfLE_ι _)

/-- The comparison maps are compatible with composition: for opens `V ≤ V' ≤ V''`, the
composite `F_V ⟶ F_{V'} ⟶ F_{V''}` is the comparison `F_V ⟶ F_{V''}`. -/
lemma etaleModuleOpensComparison_comp {V V' V'' : X.Opens} (h : V ≤ V') (h' : V' ≤ V'')
    (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleOpensComparison Λ h).app F ≫ (etaleModuleOpensComparison Λ h').app F =
      (etaleModuleOpensComparison Λ (h.trans h')).app F := by
  have := mono_etaleModuleExtensionByZeroAdj_counit_app Λ V'' F
  rw [← cancel_mono ((etaleModuleExtensionByZeroAdj.{u, r} Λ V''.ι).counit.app F),
    Category.assoc, etaleModuleCoverComparison_comp_counit,
    etaleModuleCoverComparison_comp_counit, etaleModuleCoverComparison_comp_counit]

/-- The comparison `F_V ⟶ F_{V'}` for opens `V ≤ V'` is a monomorphism. -/
theorem mono_etaleModuleOpensComparison_app {V V' : X.Opens} (h : V ≤ V')
    (F : EtaleModules.{u, r} Λ X) : Mono ((etaleModuleOpensComparison Λ h).app F) := by
  have := mono_etaleModuleExtensionByZeroAdj_counit_app Λ V F
  exact mono_of_mono_fac (etaleModuleCoverComparison_comp_counit.{u, r} Λ V.ι V'.ι
    (X.homOfLE h) (X.homOfLE_ι _) F)

/-- **The Mayer–Vietoris sequence of two opens, extended by zero**:
`0 ⟶ F_{A ∩ B} ⟶ F_A ⊕ F_B ⟶ F_{A ∪ B} ⟶ 0` is short exact. -/
theorem shortExact_etaleModuleOpensShortComplex (F : EtaleModules.{u, r} Λ X) :
    (ShortComplex.biprodMayerVietoris
      ((etaleModuleOpensComparison Λ (inf_le_left : A ⊓ B ≤ A)).app F)
      ((etaleModuleOpensComparison Λ (inf_le_right : A ⊓ B ≤ B)).app F)
      ((etaleModuleOpensComparison Λ (le_sup_left : A ≤ A ⊔ B)).app F)
      ((etaleModuleOpensComparison Λ (le_sup_right : B ≤ A ⊔ B)).app F)
      (by rw [etaleModuleOpensComparison_comp, etaleModuleOpensComparison_comp])).ShortExact := by
  let Lf : (x : X) → EtaleModules.{u, r} Λ X ⥤
      EtaleModules.{u, r} Λ (Spec (.of (SeparableClosure (X.residueField x)))) :=
    fun x ↦ etaleModuleInverseImage.{u, r} Λ (gpt x)
  have _ : ∀ x, PreservesFiniteLimits (Lf x) := fun x ↦
    etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ (gpt x)
  have _ : ∀ x, PreservesFiniteColimits (Lf x) := fun x ↦
    etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ (gpt x)
  have hcomp : ∀ {V V' : X.Opens} (h : V ≤ V') (x : X), x ∈ V →
      IsIso ((Lf x).map ((etaleModuleOpensComparison Λ h).app F)) := by
    intro V V' h x hx
    have h1 := isIso_map_counit_of_mem Λ V hx F
    have h2 := isIso_map_counit_of_mem Λ V' (h hx) F
    have hfac : (Lf x).map ((etaleModuleOpensComparison Λ h).app F) ≫
        (Lf x).map ((etaleModuleExtensionByZeroAdj.{u, r} Λ V'.ι).counit.app F) =
        (Lf x).map ((etaleModuleExtensionByZeroAdj.{u, r} Λ V.ι).counit.app F) := by
      rw [← Functor.map_comp, etaleModuleCoverComparison_comp_counit]
    exact IsIso.of_isIso_fac_right hfac
  have hzero : ∀ {V V' : X.Opens} (h : V ≤ V') (x : X), x ∉ V' →
      IsIso ((Lf x).map ((etaleModuleOpensComparison Λ h).app F)) := fun h x hx ↦
    (isZero_map_of_not_mem Λ _ (fun hxV ↦ hx (h hxV)) F).isIso
      (isZero_map_of_not_mem Λ _ hx F) _
  refine ((jointlyReflect Λ).shortExact_iff _).2 fun x ↦ ?_
  refine ShortComplex.shortExact_map_biprodMayerVietoris (Lf x) _ _ _ _ _ ?_
  by_cases hxA : x ∈ A
  · have h1 := hcomp (le_sup_left : A ≤ A ⊔ B) x hxA
    by_cases hxB : x ∈ B
    · have h2 := hcomp (inf_le_right : A ⊓ B ≤ B) x ⟨hxA, hxB⟩
      exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_fst _ _ _ _ _
    · have := hzero (inf_le_right : A ⊓ B ≤ B) x hxB
      exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_fst _ _ _ _ _
  · have := hzero (inf_le_left : A ⊓ B ≤ A) x hxA
    by_cases hxB : x ∈ B
    · have h2 := hcomp (le_sup_right : B ≤ A ⊔ B) x hxB
      exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_snd _ _ _ _ _
    · have := hzero (le_sup_right : B ≤ A ⊔ B) x
        fun h ↦ (TopologicalSpace.Opens.mem_sup.1 h).elim hxA hxB
      exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_snd _ _ _ _ _

end Stacks.EtaleCohomology
