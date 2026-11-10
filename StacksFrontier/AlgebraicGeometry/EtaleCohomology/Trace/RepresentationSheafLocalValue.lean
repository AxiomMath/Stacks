module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HomOpComplexStageCochains
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTrivialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.LocalizedGeneralCoefficients
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology

/-!
# The local values of `ℱ_M` are `M`

Let `X` be a connected scheme with a geometric point `x`, `Λ` a finite ring and `M` a finite
`Λ`-module with a continuous action of `π₁(X, x)`. The sheaf `ℱ_M` of Tag 0DV5 becomes the
constant sheaf `M_Y` on a surjective finite étale cover `π : Y ⟶ X`
(`AlgebraicGeometry.exists_finiteEtale_inverseImage_representationSheaf_iso_constant`), with the
value `M` itself. Reading `π^* ℱ_M` as the restriction of `ℱ_M` to the slice of `X_étale` at `Y`,
`ℱ_M` is locally on `X_étale` the constant sheaf on a module isomorphic to `M`: every property
of `M` invariant under isomorphism is a property of the constant values of `ℱ_M`.

## Main results

* `Stacks.EtaleCohomology.constantSheafOverIsoOfInverseImageIso` — for an étale `W ⟶ X`, an
  isomorphism `π^* F ≅ E_W` is an isomorphism `E ≅ F|_W` on the slice site at `W`.
* `Stacks.EtaleCohomology.isLocallyConstantWith_of_inverseImage_iso_constant` — a sheaf which
  becomes constant with value `E` on a surjective étale cover is locally constant with value `E`.
* `AlgebraicGeometry.exists_finiteEtale_inverseImage_representationSheaf_iso_constant_of_iso` —
  the trivialization of `ℱ_M` on a finite étale cover, with value isomorphic to `M`.
* `AlgebraicGeometry.isLocallyConstantWith_representationSheaf` — `ℱ_M` is locally constant with
  values isomorphic to `M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

/-! ### The slice of `X_étale` at an étale `W` is `W_étale`, as a site -/

section OverEtale

variable {X : Scheme.{u}} (W : X.Etale)

/-- `Over W ⥤ W_étale` preserves coverings. -/
theorem overEtaleFunctor_coverPreserving :
    CoverPreserving ((smallEtaleTopology X).over W) (smallEtaleTopology W.left)
      (overEtaleFunctor W) := by
  constructor
  intro V S hS
  obtain ⟨members, Z, g, rfl⟩ := S.exists_eq_ofArrows
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hS
  rw [Sieve.functorPushforward_ofArrows]
  exact (ofArrows_mem_smallEtaleTopology_iff _).mpr
    ((ofArrows_mem_smallEtaleTopology_iff (fun member ↦ (g member).left)).mp hS)

/-- `W_étale ⥤ Over W` preserves coverings. -/
theorem overEtaleInverse_coverPreserving :
    CoverPreserving (smallEtaleTopology W.left) ((smallEtaleTopology X).over W)
      (overEtaleInverse W) := by
  constructor
  intro V S hS
  obtain ⟨members, Z, g, rfl⟩ := S.exists_eq_ofArrows
  rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  exact (ofArrows_mem_smallEtaleTopology_iff _).mpr ((ofArrows_mem_smallEtaleTopology_iff g).mp hS)

/-- The functor `Over W ⥤ W_étale` of the equivalence of sites is cocontinuous. -/
instance overEtaleFunctor_isCocontinuous :
    (overEtaleEquivalence W).functor.IsCocontinuous ((smallEtaleTopology X).over W)
      (smallEtaleTopology W.left) :=
  ((overEtaleEquivalence W).toAdjunction.isCocontinuous_iff_coverPreserving _ _).mpr
    (overEtaleInverse_coverPreserving W)

/-- The inverse `W_étale ⥤ Over W` of the equivalence of sites is cocontinuous. -/
instance overEtaleInverse_isCocontinuous :
    (overEtaleEquivalence W).inverse.IsCocontinuous (smallEtaleTopology W.left)
      ((smallEtaleTopology X).over W) :=
  ((overEtaleEquivalence W).symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mpr
    (overEtaleFunctor_coverPreserving W)

/-- `W_étale ⥤ Over W` is a dense subsite, being an equivalence of sites. -/
instance overEtaleInverse_isDenseSubsite :
    (overEtaleEquivalence W).inverse.IsDenseSubsite (smallEtaleTopology W.left)
      ((smallEtaleTopology X).over W) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

end OverEtale

/-! ### A trivialization on an étale cover is a trivialization on the slice site -/

section Trivialization

variable {X : Scheme.{u}} (Λ : Type) [Ring Λ]

attribute [local instance] moduleCat_hasLimitsOfSize

/-- Sheafification of presheaves of `Λ`-modules on Mathlib's small étale site, at the module
universe `u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_typeZero (Y : Scheme.{u}) :
    HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- Sheafification of presheaves of `Λ`-modules on a slice of Mathlib's small étale site, at the
module universe `u + 1`. -/
local instance (priority := 3000) etaleModules_over_hasSheafify_typeZero (Y : Scheme.{u})
    (V : Y.Etale) : HasSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ) :=
  Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u} Λ Y.smallEtaleTopology V

/-- **A trivialization of `π^* F` is a trivialization of `F` on the slice at `W`.** For an étale
`X`-scheme `W`, an isomorphism `π^* F ≅ E_W` of sheaves of `Λ`-modules on `W_étale`, `π` the
structure morphism, gives `E ≅ F|_W` on the slice site `X_étale/W`: restriction along
`W_étale ≌ X_étale/W` carries `F|_W` to the restriction of `F` along `π`, which is `π^* F`
(`Stacks.EtaleCohomology.etaleModuleInverseImageRestrictionIso`), and the constant sheaf to the
constant sheaf. -/
def constantSheafOverIsoOfInverseImageIso (W : X.Etale) (F : EtaleModules.{u, 0} Λ X)
    (E : ModuleCat.{u + 1} Λ)
    (e : (etaleModuleInverseImage.{u, 0} Λ W.hom).obj F ≅
      (constantSheaf (smallEtaleTopology W.left) (ModuleCat.{u + 1} Λ)).obj E) :
    (constantSheaf ((smallEtaleTopology X).over W) (ModuleCat.{u + 1} Λ)).obj E ≅
      ((smallEtaleTopology X).overPullback (ModuleCat.{u + 1} Λ) W).obj F :=
  ((overEtaleEquivalence W).sheafCongr ((smallEtaleTopology X).over W)
      (smallEtaleTopology W.left) (ModuleCat.{u + 1} Λ)).functor.preimageIso
    ((Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
        (smallEtaleTopology W.left) ((smallEtaleTopology X).over W)
        (overEtaleEquivalence W).inverse (ModuleCat.{u + 1} Λ)).app E ≪≫ e.symm ≪≫
      (etaleModuleInverseImageRestrictionIso.{u, 0} Λ W.hom).app F)

/-- **A sheaf which is constant on a surjective étale cover is locally constant with that
value.** If `π^* F ≅ E_Y` for a surjective étale `π : Y ⟶ X` and `E` satisfies `Q`, then `F` is
locally constant with values satisfying `Q`: the single covering `Y ⟶ X` of the final object of
`X_étale` trivializes `F` with value `E`. -/
theorem isLocallyConstantWith_of_inverseImage_iso_constant {Y : Scheme.{u}} (π : Y ⟶ X)
    [Etale π] [Surjective π] (Q : ModuleCat.{u + 1} Λ → Prop) (F : EtaleModules.{u, 0} Λ X)
    (E : ModuleCat.{u + 1} Λ) (hE : Q E)
    (e : (etaleModuleInverseImage.{u, 0} Λ π).obj F ≅
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q F := by
  let W : X.Etale := MorphismProperty.Over.mk ⊤ π inferInstance
  have hT := etaleSiteTerminalIsTerminal X
  have hcov : Sieve.ofArrows (fun _ : PUnit.{u + 2} ↦ W) (fun _ ↦ hT.from W) ∈
      smallEtaleTopology X (etaleSiteTerminal X) := by
    refine (ofArrows_mem_smallEtaleTopology_iff _).mpr (Set.eq_univ_of_forall fun z ↦ ?_)
    obtain ⟨y, rfl⟩ := π.surjective z
    have h : (hT.from W).left = π :=
      (Category.comp_id _).symm.trans (MorphismProperty.Over.w (hT.from W))
    exact Set.mem_iUnion.mpr ⟨PUnit.unit, y, by rw [h]; rfl⟩
  exact Stacks.ConstantSheaf.Localization.exists_trivializing_cover (smallEtaleTopology X)
    (ModuleCat.{u + 1} Λ) hT F Q hcov
    (fun _ ↦ ⟨E, hE, ⟨constantSheafOverIsoOfInverseImageIso Λ W F E e⟩⟩)

end Trivialization

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

section Trivialization

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [Ring Λ] [Finite Λ]

omit [Finite Λ] in
/-- Moving a module along an equality of base points does not change its underlying module. -/
theorem nonempty_eqRec_V_iso {x x' : GeometricPoint X.1} (h : x = x')
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    Nonempty ((h ▸ M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1 x')).obj.obj.obj.V ≅ M.obj.obj.obj.V) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- **`ℱ_M` becomes constant with value `M` on a surjective finite étale cover.** For a finite
`Λ`-module `M` with continuous `π₁(X, x)`-action there is a surjective finite étale
`π : Y ⟶ X` with `π^* ℱ_M ≅ E_Y` for a module `E ≅ M`: the trivialization of
`AlgebraicGeometry.exists_finiteEtale_inverseImage_representationSheaf_iso_constant`, keeping track
of its value. -/
theorem exists_finiteEtale_inverseImage_representationSheaf_iso_constant_of_iso
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X.1) (_ : IsFinite π) (_ : Etale π) (_ : Surjective π)
      (E : ModuleCat.{u + 1} Λ) (_ : Nonempty (E ≅ M.obj.obj.obj.V)),
      Nonempty ((etaleModuleInverseImage.{u, 0} Λ π).obj
          ((representationSheaf B X x Λ).obj M) ≅
        (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) := by
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  obtain ⟨Hs, -, hHo, hHρ⟩ := exists_isOpen_normal_subgroup_ρ_eq_one_finiteType Λ _ M
  obtain ⟨W, w, htrans, hstab⟩ := exists_finiteEtaleOver_transitive_stabilizer_le x ⟨Hs, hHo⟩
  have : ConnectedSpace W.left := connectedSpace_left_of_exists_smul_eq htrans
  have hf : finiteEtale W.hom := W.prop
  have : IsFinite W.hom := W.prop.1
  have : Etale W.hom := W.prop.2
  let t : GeometricPoint W.left := ⟨x.residueField, w.1⟩
  have ht : x = t.map W.hom := by
    change x = ⟨x.residueField, w.1 ≫ W.hom⟩
    rw [w.2]
  have : ConnectedSpace ((𝟭 Scheme).obj W.left) := inferInstanceAs (ConnectedSpace W.left)
  have : ConnectedSpace ((Functor.fromPUnit X.obj).obj W.right) :=
    inferInstanceAs (ConnectedSpace X.1)
  let Yb : B.Scheme := ⟨W.left, contains_of_locallyOfFiniteType_of_quasiCompact B W.hom X.2⟩
  let g : Yb ⟶ X := ObjectProperty.homMk W.hom
  let M' := (ht ▸ M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
    (EtaleFundamentalGroup X.1 (t.map g.hom)))
  have hM' : ∀ τ : EtaleFundamentalGroup W.left t,
      M'.obj.obj.obj.ρ (etaleFundamentalGroupMap W.hom t τ) = 1 := by
    intro τ
    have hmem : etaleFundamentalGroupMap W.hom t τ ∈
        MulAction.stabilizer (EtaleFundamentalGroup X.1 (t.map W.hom))
          (finiteEtaleOverSourcePoint hf t) := by
      rw [← range_etaleFundamentalGroupMap_eq_stabilizer]
      exact ⟨τ, rfl⟩
    exact rho_eqRec_eq_one_of_smul_eq Λ ht W w (finiteEtaleOverSourcePoint hf t) HEq.rfl M
      (fun σ hσ ↦ hHρ σ (hstab σ hσ)) _ hmem
  let E₀ : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ) :=
    ⟨M'.obj.obj.obj.V, M'.property⟩
  obtain ⟨eV⟩ := nonempty_eqRec_V_iso B X Λ ht M
  refine ⟨W.left, W.hom, inferInstance, inferInstance,
    ⟨fun z ↦ surjective_of_finiteEtale W z⟩, (ModuleCat.uliftFunctor.{0, u + 1} Λ).obj E₀.obj,
    ⟨ULift.moduleEquiv.toModuleIso ≪≫ eV⟩, ⟨?_⟩⟩
  refine eqToIso (congrArg _ (representationSheaf_obj_eqRec B X Λ ht M).symm) ≪≫
    (representationSheafPullbackIso B g Λ t).app M' ≪≫
    (representationSheaf B Yb t Λ).mapIso
      (finiteTypeContinuousModuleTrivialIsoRes Λ (etaleFundamentalGroupMap g.hom t) M' hM').symm ≪≫
    (representationSheafTrivialIsoConstant B Yb t Λ).app E₀

/-- **`ℱ_M` is locally constant with values isomorphic to `M`**: on a covering of every object
of `X_étale` it is the constant sheaf on a module isomorphic to `M`. -/
theorem isLocallyConstantWith_representationSheaf
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.1.smallEtaleTopology
      (fun E ↦ Nonempty (E ≅ M.obj.obj.obj.V)) ((representationSheaf B X x Λ).obj M) := by
  obtain ⟨Y, π, _, _, _, E, hE, ⟨e⟩⟩ :=
    exists_finiteEtale_inverseImage_representationSheaf_iso_constant_of_iso B X x Λ M
  exact isLocallyConstantWith_of_inverseImage_iso_constant Λ π _ _ E hE e

end Trivialization

end AlgebraicGeometry
