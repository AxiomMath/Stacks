module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AssemblyGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators

/-!
# A module of finite type is a quotient of a module of finite presentation

Let `X` be a quasi-compact algebraic space and let `M` be an `𝒪_X`-module of finite type all of
whose sections are locally the image of modules of finite presentation.  Then `M` is a quotient
of a single `𝒪_X`-module of finite presentation.  This is the first step of the source's proof
of Stacks 086Y, where the module of finite presentation is a stage of the filtered presentation
of Stacks 07V9.

The proof is the one sketched in the source for the corresponding step on a scheme.  One affine
étale chart `U` covers `X` (Stacks 03H6); the covering of `U` on whose members `M` is generated
by finitely many sections is refined by finitely many affine charts `V k`
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`); over each `V k` the
finitely many generators are, on a covering of `V k` which may again be taken finite and affine,
images of sections of modules of finite presentation.  The direct sum of these finitely many
modules maps onto `M`: a morphism out of `M` killing all of them kills the generators over each
`V k`, because sheaves are separated, hence vanishes over each `V k`, hence vanishes.

## References

* [Stacks Project, Tag 086Y](https://stacks.math.columbia.edu/tag/086Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open FpAssembly

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The affine charts of a finite affine refinement of a covering of a chart covering the final
object cover the final object. -/
theorem coversTop_of_coversTop_of_ofArrows_mem {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : SmallEtale B S hS X}
    (hU : (SmallEtale.topology B S hS X).CoversTop fun _ : PUnit.{u + 2} => U)
    {κ : Type} {V : κ → SmallEtale B S hS X} {f : ∀ k, V k ⟶ U}
    (hf : Sieve.ofArrows V f ∈ SmallEtale.topology B S hS X U) :
    (SmallEtale.topology B S hS X).CoversTop V := by
  intro T
  refine (SmallEtale.topology B S hS X).transitive (hU T) _ fun T' g hg => ?_
  obtain ⟨-, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff _ _).1 hg
  refine (SmallEtale.topology B S hS X).superset_covering ?_
    ((SmallEtale.topology B S hS X).pullback_stable b hf)
  intro T'' h hh
  obtain ⟨k, c, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  exact (Sieve.mem_ofObjects_iff _ _).2 ⟨k, ⟨c⟩⟩

/-- On an affine chart, a section of a module whose sections are locally images of modules of
finite presentation is such an image on the members of a finite covering family. -/
theorem exists_finite_ofArrows_liftsToFinitePresentation {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {M : Modules.{u, u} B S hS X hX}
    (hM : IsLocallyFpGenerated B S hS hX M) {V : SmallEtale B S hS X}
    (hV : IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj V))
    (x : M.val.obj (op V)) :
    ∃ (μ : Type) (_ : Finite μ) (W : μ → SmallEtale B S hS X) (w : ∀ m, W m ⟶ V),
      Sieve.ofArrows W w ∈ SmallEtale.topology B S hS X V ∧
        ∀ m, LiftsToFinitePresentation B S hS hX M (T := W m) (M.val.map (w m).op x) := by
  obtain ⟨μ, hμ, W, w, -, hle, hcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS X V hV _ (hM V x)
  exact ⟨μ, hμ, W, w, hcov, fun m => hle _ (Sieve.ofArrows_mk W w m)⟩

section Vanishing

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A morphism of sheaves of modules kills a section as soon as it kills its restrictions to the
members of a covering family. -/
theorem app_eq_zero_of_ofArrows_mem {M Z : SheafOfModules.{u} R} (g : M ⟶ Z) {V : C}
    (x : M.val.obj (op V)) {μ : Type*} {W : μ → C} {w : ∀ m, W m ⟶ V}
    (hw : Sieve.ofArrows W w ∈ J V) (h : ∀ m, g.val.app (op (W m)) (M.val.map (w m).op x) = 0) :
    g.val.app (op V) x = 0 := by
  refine eq_zero_of_forall_mem_sieve Z _ hw fun W' e he => ?_
  obtain ⟨m, e, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 he
  refine (PresheafOfModules.map_comp_apply Z.val (w m).op e.op _).trans ?_
  exact (congrArg (Z.val.map e.op)
    ((PresheafOfModules.naturality_apply g.val (w m).op x).symm.trans (h m))).trans (map_zero _)

variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A morphism of sheaves of modules vanishes over `V` as soon as it kills the values over `V` of
a family of generating sections over `V`. -/
theorem over_eq_zero_of_generatingSections {M Z : SheafOfModules.{u} R} {V : C}
    (σ : (M.over V).GeneratingSections) (g : M ⟶ Z)
    (h : ∀ l, g.val.app (op V) ((σ.s l).val (op (Over.mk (𝟙 V)))) = 0) : g.over V = 0 :=
  eq_zero_of_generatingSections σ _ fun l => by
    apply Subtype.ext
    funext Y
    have hs := (σ.s l).property
      (Over.homMk Y.unop.hom (Category.comp_id _) : Y.unop ⟶ Over.mk (𝟙 V)).op
    change g.val.app (op Y.unop.left) ((σ.s l).val Y) = 0
    rw [← hs]
    change g.val.app (op Y.unop.left)
      (M.val.map Y.unop.hom.op ((σ.s l).val (op (Over.mk (𝟙 V))))) = 0
    refine (PresheafOfModules.naturality_apply g.val Y.unop.hom.op _).trans ?_
    exact (congrArg (Z.val.map Y.unop.hom.op) (h l)).trans (map_zero _)

end Vanishing

/-- **A module of finite type all of whose sections are locally the image of modules of finite
presentation is, on a quasi-compact algebraic space, a quotient of a module of finite
presentation.** -/
theorem exists_isFinitePresentation_epi_of_isFiniteTypeOnSite
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (M : Modules.{u, u} B S hS X hX)
    (hM : IsLocallyFpGenerated B S hS hX M) [M.IsFiniteTypeOnSite] :
    ∃ (G : Modules.{u, u} B S hS X hX) (_ : G.IsFinitePresentation) (p : G ⟶ M), Epi p := by
  classical
  let : HasSheafify (smallEtaleRingedSite B S hS X hX).J AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : ∀ U : (smallEtaleRingedSite B S hS X hX).C,
      HasSheafify ((smallEtaleRingedSite B S hS X hX).J.over U) AddCommGrpCat.{u} :=
    fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : ∀ (V W : (smallEtaleRingedSite B S hS X hX).C) (f : W ⟶ V),
      PreservesColimitsOfSize.{u, u} (SheafOfModules.overMap.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) f) :=
    fun _ _ f => Stacks.SheafOfModules.overMap_preservesColimits _ f
  have hft : M.IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite M inferInstance
  obtain ⟨qG, hqG⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  obtain ⟨U, hUaff, hUcov⟩ := SmallEtale.exists_affineObject_coversTop B S hS X hX hqc
  obtain ⟨κ, hκ, V, f, hVaff, hle, hcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS X U hUaff (Sieve.ofObjects qG.X U)
      (qG.coversTop U)
  choose i a using fun k =>
    (Sieve.mem_ofObjects_iff _ _).1 (hle _ (Sieve.ofArrows_mk V f k))
  let V' : κ → (smallEtaleRingedSite B S hS X hX).C := V
  let a' : ∀ k, V' k ⟶ qG.X (i k) := fun k => (a k).some
  let σ : ∀ k, (M.over (V' k)).GeneratingSections := fun k =>
    Stacks.SheafOfModules.LocalKernel.generatingSectionsOver (a' k) (qG.generators (i k))
  have hσ : ∀ k, (σ k).IsFiniteType := fun k => by
    have := hqG.isFiniteType (i k)
    infer_instance
  let x : ∀ k, (σ k).I → M.val.obj (op (V' k)) := fun k l =>
    ((σ k).s l).val (op (Over.mk (𝟙 (V' k))))
  choose μ hμ W w hcovW hL using fun k (l : (σ k).I) =>
    exists_finite_ofArrows_liftsToFinitePresentation B S hS hM (hVaff k) (x k l)
  choose G hG ψ t ht using hL
  let GG : (Σ k : κ, Σ l : (σ k).I, μ k l) → Modules.{u, u} B S hS X hX :=
    fun j => G j.1 j.2.1 j.2.2
  refine ⟨∐ GG, isFinitePresentation_sigma GG fun j => hG _ _ _,
    Sigma.desc fun j => ψ j.1 j.2.1 j.2.2, ?_⟩
  refine Preadditive.epi_of_cancel_zero _ fun {Z} g hg => ?_
  have h1 : ∀ k l m, ψ k l m ≫ g = 0 := fun k l m => by
    simpa using Sigma.ι GG ⟨k, l, m⟩ ≫= hg
  have h2 : ∀ k l, g.val.app (op (V' k)) (x k l) = 0 := fun k l =>
    app_eq_zero_of_ofArrows_mem g _ (hcovW k l) fun m => by
      refine (congrArg (g.val.app _) (ht k l m)).symm.trans ?_
      change (ψ k l m ≫ g).val.app _ (t k l m) = 0
      rw [h1]
      rfl
  exact hom_eq_zero_of_coversTop (Y := V') g
    (coversTop_of_coversTop_of_ofArrows_mem B S hS hUcov hcov) fun k W b =>
      congrArg (fun φ => φ.val.app (op (Over.mk b)))
        (over_eq_zero_of_generatingSections (σ k) g (h2 k))

end AlgebraicGeometry.Space

end
