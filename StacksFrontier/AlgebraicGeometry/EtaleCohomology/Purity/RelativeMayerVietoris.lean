module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# The Mayer--Vietoris sequence of two opens, relative to their union

Let `X` be a scheme, `U`, `V` opens of `X` and `F` a sheaf of `Λ`-modules on `X_étale`. Writing
`F_W = j_{W!} F|_W` for an open `W`, the sequence
`0 → F_{U ∩ V} → F_U ⊕ F_V → F_{U ∪ V} → 0`,
with maps `(κ, -κ)` and `(κ, κ)` given by the canonical comparisons
`κ : F_W ⟶ F_{W'}` for `W ≤ W'` (`Stacks.EtaleCohomology.Purity.openComparison`), is short exact
(`Stacks.EtaleCohomology.Purity.shortExact_relativeCover`). For `U ∪ V = X` it is the
Mayer--Vietoris sequence `Stacks.EtaleCohomology.shortExact_etaleModuleCoverShortComplex`; here
`U ∪ V` is an arbitrary open of `X`.

Morphisms out of `j_{W!}` into `F_{W'}` are determined by their composite with the counit
`F_{W'} ⟶ F` (`Stacks.EtaleCohomology.Purity.ext_of_comp_counit`), so the comparisons compose
(`Stacks.EtaleCohomology.Purity.openComparison_comp`) and the square of the sequence commutes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology.Purity

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] {X : Scheme.{u}}

/-- The canonical comparison `j_{W!} F|_W ⟶ j_{W'!} F|_{W'}` for opens `W ≤ W'`. -/
abbrev openComparison {W W' : X.Opens} (h : W ≤ W') :
    etaleModuleExtensionByZeroOfRestriction.{u, r} Λ W.ι ⟶
      etaleModuleExtensionByZeroOfRestriction.{u, r} Λ W'.ι :=
  etaleModuleCoverComparison.{u, r} Λ W.ι W'.ι (X.homOfLE h) (X.homOfLE_ι h)

/-- The comparison `F_W ⟶ F_{W'}` followed by the counit `F_{W'} ⟶ F` is the counit `F_W ⟶ F`. -/
theorem openComparison_comp_counit {W W' : X.Opens} (h : W ≤ W') (F : EtaleModules.{u, r} Λ X) :
    (openComparison Λ h).app F ≫ (etaleModuleExtensionByZeroAdj.{u, r} Λ W'.ι).counit.app F =
      (etaleModuleExtensionByZeroAdj.{u, r} Λ W.ι).counit.app F :=
  etaleModuleCoverComparison_comp_counit Λ _ _ _ _ F

/-- **Maps out of an extension by zero from `W` into `j_{W'!} F|_{W'}` are determined by their
composite with the counit**, since the counit becomes invertible after restriction to `W`. -/
theorem ext_of_comp_counit {W W' : X.Opens} (h : W ≤ W') {Y : EtaleModules.{u, r} Λ W}
    {F : EtaleModules.{u, r} Λ X}
    {f g : (etaleModuleExtensionByZero.{u, r} Λ W.ι).obj Y ⟶
      (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ W'.ι).obj F}
    (hfg : f ≫ (etaleModuleExtensionByZeroAdj.{u, r} Λ W'.ι).counit.app F =
      g ≫ (etaleModuleExtensionByZeroAdj.{u, r} Λ W'.ι).counit.app F) : f = g := by
  have hiso : IsIso ((etaleModuleRestriction.{u, r} Λ W.ι).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ W'.ι).counit.app F)) :=
    isIso_etaleModuleRestriction_map_counit_of_factors Λ W.ι W'.ι (X.homOfLE h)
      (X.homOfLE_ι h) F
  apply ((etaleModuleExtensionByZeroAdj.{u, r} Λ W.ι).homEquiv _ _).injective
  rw [← cancel_mono ((etaleModuleRestriction.{u, r} Λ W.ι).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ W'.ι).counit.app F)),
    ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_right, hfg]

/-- **The comparisons compose.** -/
theorem openComparison_comp {W W' W'' : X.Opens} (h₁ : W ≤ W') (h₂ : W' ≤ W'')
    (F : EtaleModules.{u, r} Λ X) :
    (openComparison Λ h₁).app F ≫ (openComparison Λ h₂).app F =
      (openComparison Λ (h₁.trans h₂)).app F := by
  refine ext_of_comp_counit Λ (W := W) (W' := W'') (h₁.trans h₂)
    (Y := (etaleModuleRestriction.{u, r} Λ W.ι).obj F) (F := F) ?_
  rw [Category.assoc, openComparison_comp_counit, openComparison_comp_counit,
    openComparison_comp_counit]

/-- A functor inverting the counits at `W` and `W'` inverts the comparison `F_W ⟶ F_{W'}`. -/
private theorem isIso_map_openComparison_of_isIso_map_counit {D : Type*} [Category D]
    (G : EtaleModules.{u, r} Λ X ⥤ D) {W W' : X.Opens} (h : W ≤ W')
    (F : EtaleModules.{u, r} Λ X)
    (h₁ : IsIso (G.map ((etaleModuleExtensionByZeroAdj.{u, r} Λ W'.ι).counit.app F)))
    (h₂ : IsIso (G.map ((etaleModuleExtensionByZeroAdj.{u, r} Λ W.ι).counit.app F))) :
    IsIso (G.map ((openComparison Λ h).app F)) :=
  IsIso.of_isIso_fac_right
    (show G.map ((openComparison Λ h).app F) ≫
      G.map ((etaleModuleExtensionByZeroAdj.{u, r} Λ W'.ι).counit.app F) = _ by
      rw [← Functor.map_comp, openComparison_comp_counit])

/-- The comparison `F_W ⟶ F_{W'}` becomes invertible after restriction to any open `W'' ≤ W`. -/
theorem isIso_restriction_openComparison {W W' W'' : X.Opens} (h : W ≤ W') (h' : W'' ≤ W)
    (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleRestriction.{u, r} Λ W''.ι).map ((openComparison Λ h).app F)) :=
  isIso_map_openComparison_of_isIso_map_counit Λ _ h F
    (isIso_etaleModuleRestriction_map_counit_of_factors Λ W''.ι W'.ι (X.homOfLE (h'.trans h))
      (X.homOfLE_ι _) F)
    (isIso_etaleModuleRestriction_map_counit_of_factors Λ W''.ι W.ι (X.homOfLE h')
      (X.homOfLE_ι _) F)

/-- **The relative Mayer--Vietoris sequence** `0 → F_{U ∩ V} → F_U ⊕ F_V → F_{U ∪ V} → 0` of two
opens of `X`, with maps `(κ, -κ)` and `(κ, κ)`, is short exact.

Exactness is checked at the geometric points of `X`. At a point of `U ∩ V` all four maps become
invertible; at a point of only one of the two opens the terms belonging to the other open vanish;
at a point outside `U ∪ V` every term vanishes. -/
theorem shortExact_relativeCover (U V : X.Opens) (F : EtaleModules.{u, r} Λ X) :
    (ShortComplex.biprodMayerVietoris ((openComparison Λ (inf_le_left : U ⊓ V ≤ U)).app F)
      ((openComparison Λ (inf_le_right : U ⊓ V ≤ V)).app F)
      ((openComparison Λ (le_sup_left : U ≤ U ⊔ V)).app F)
      ((openComparison Λ (le_sup_right : V ≤ U ⊔ V)).app F)
      (by rw [openComparison_comp, openComparison_comp])).ShortExact := by
  let gp : ∀ x : X, Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    fun x ↦ residueGeometricPoint X x
  have hcov : ⋃ x : X, Set.range (gp x).base = Set.univ :=
    Set.eq_univ_of_forall fun x ↦
      Set.mem_iUnion.2 ⟨x, default, residueGeometricPoint_apply X x default⟩
  have hfac : ∀ (W' : X.Opens) (y : X), y ∈ W' →
      ∃ κ : Spec (.of (SeparableClosure (X.residueField y))) ⟶ (W' : Scheme.{u}),
        κ ≫ W'.ι = gp y := by
    intro W' y hy
    have hsub : Set.range (gp y) ⊆ Set.range W'.ι := by
      rintro z ⟨t, rfl⟩
      rwa [Scheme.Opens.range_ι, residueGeometricPoint_apply]
    exact ⟨IsOpenImmersion.lift W'.ι (gp y) hsub, IsOpenImmersion.lift_fac _ _ hsub⟩
  have hcounit : ∀ (W' : X.Opens) (y : X), y ∈ W' →
      IsIso ((etaleModuleInverseImage.{u, r} Λ (gp y)).map
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ W'.ι).counit.app F)) := by
    intro W' y hy
    obtain ⟨κ, hκ⟩ := hfac W' y hy
    exact isIso_etaleModuleInverseImage_map_counit_of_factors Λ (gp y) W'.ι κ hκ F
  have hzero : ∀ (W' : X.Opens) (y : X), y ∉ W' →
      IsZero ((etaleModuleInverseImage.{u, r} Λ (gp y)).obj
        ((etaleModuleExtensionByZeroOfRestriction.{u, r} Λ W'.ι).obj F)) := by
    intro W' y hy
    have hd : Disjoint (Set.range (gp y).base) (Set.range (W'.ι).base) := by
      rw [Set.disjoint_left]
      rintro z ⟨t, rfl⟩ hz
      rw [Scheme.Opens.range_ι, show (gp y).base t = y from residueGeometricPoint_apply X y t] at hz
      exact hy hz
    exact isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ (gp y) W'.ι hd _
  have hcomp : ∀ {W W' : X.Opens} (h : W ≤ W') (y : X), y ∈ W →
      IsIso ((etaleModuleInverseImage.{u, r} Λ (gp y)).map ((openComparison Λ h).app F)) := by
    intro W W' h y hy
    exact isIso_map_openComparison_of_isIso_map_counit Λ _ h F (hcounit W' y (h hy))
      (hcounit W y hy)
  have hzz : ∀ {W W' : X.Opens} (h : W ≤ W') (y : X), y ∉ W' →
      IsIso ((etaleModuleInverseImage.{u, r} Λ (gp y)).map ((openComparison Λ h).app F)) := by
    intro W W' h y hy
    exact ⟨⟨0, (hzero W y fun hW => hy (h hW)).eq_of_src _ _, (hzero W' y hy).eq_of_src _ _⟩⟩
  let D : X → Type (max (u + 2) (r + 1)) := fun x ↦
    EtaleModules.{u, r} Λ (Spec (.of (SeparableClosure (X.residueField x))))
  let Lf : (x : X) → EtaleModules.{u, r} Λ X ⥤ D x :=
    fun x ↦ etaleModuleInverseImage.{u, r} Λ (gp x)
  have _ : ∀ x, PreservesFiniteLimits (Lf x) := fun x ↦
    etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ (gp x)
  have _ : ∀ x, PreservesFiniteColimits (Lf x) := fun x ↦
    etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ (gp x)
  have hL : JointlyReflectIsomorphisms Lf := by
    constructor
    intro A B γ hγ
    exact isIso_of_isIso_etaleModuleInverseImage_family Λ gp hcov γ hγ
  refine (hL.shortExact_iff _).2 fun x ↦ ?_
  refine ShortComplex.shortExact_map_biprodMayerVietoris (Lf x) _ _ _ _ _ ?_
  by_cases hxU : x ∈ U
  · have _ := hcomp (le_sup_left : U ≤ U ⊔ V) x hxU
    by_cases hxV : x ∈ V
    · have _ := hcomp (inf_le_right : U ⊓ V ≤ V) x ⟨hxU, hxV⟩
      exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_fst _ _ _ _ _
    · have _ := hzz (inf_le_right : U ⊓ V ≤ V) x hxV
      exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_fst _ _ _ _ _
  · have _ := hzz (inf_le_left : U ⊓ V ≤ U) x hxU
    by_cases hxV : x ∈ V
    · have _ := hcomp (le_sup_right : V ≤ U ⊔ V) x hxV
      exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_snd _ _ _ _ _
    · have hxUV : x ∉ U ⊔ V := fun h => (TopologicalSpace.Opens.mem_sup.1 h).elim hxU hxV
      have _ := hzz (le_sup_left : U ≤ U ⊔ V) x hxUV
      have _ := hzz (inf_le_right : U ⊓ V ≤ V) x hxV
      exact ShortComplex.shortExact_biprodMayerVietoris_of_isIso_fst _ _ _ _ _

end Stacks.EtaleCohomology.Purity

end
