module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ConstructiblePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.RelativeCurveConstructibility
public import StacksFrontier.CategoryTheory.Sites.FreeModuleSheafSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.LimitStages
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructible sheaves of modules on a limit of schemes come from a finite stage

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, and `Λ` a Noetherian ring. Every constructible sheaf of
`Λ`-modules on `X_étale` is, up to isomorphism, the inverse image of a constructible sheaf of
`Λ`-modules on some `(X_i)_étale`. This is the essential surjectivity assertion of Tag 09YU,
clause (3).

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_freeModuleSheaf` — the free module sheaf on
  the sheafified representable of an affine étale scheme is constructible.
* `Stacks.EtaleCohomology.exists_epi_biproduct_freeModuleSheaf` — Tag 095N in the form used here.
* `Stacks.EtaleCohomology.exists_iso_cokernel_elementaryMatrix` — a constructible sheaf is the
  cokernel of a finite matrix of morphisms induced by morphisms of affine étale schemes.
* `Stacks.EtaleCohomology.exists_stage_affine_etale_models` — finitely many affine étale schemes
  and morphisms over the limit descend to a stage.
* `Stacks.EtaleCohomology.exists_isConstructibleEtaleModule_etaleModuleInverseImage_iso` —
  **Stacks 09YU, the essential-surjectivity assertion**, clause (3).

## Implementation notes

The source's proof of clause (3) is "very similar" to that of clause (1) with Tag 095N in place of
Tag 09Y9. Fullness, which the source invokes in the essential surjectivity step for the morphisms
of the presentation, is avoided: every morphism between the free module sheaves of a Tag 095N
presentation is, locally, a linear combination of morphisms induced by morphisms of étale schemes
(`CategoryTheory.Sheaf.freeModuleSheaf_hom_locally`), and refining the presentation accordingly
makes it a finite amount of geometric data, which descends by Tags 01ZM and 07RP alone. Theorem
Tag 09YQ is therefore not used.

Fullness of clause (3), and clauses (1) and (2) beyond faithfulness, are not proved here; the
faithfulness assertions are `AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleSetSheaf`
and `AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleModuleSheaf`.

## References

* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance] Abelian.hasFiniteBiproducts

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- `etaleModules_hasSheafify` at the universes of this file, stated out so that instance search
does not have to solve `u + 1 = max (u + 1) ?v`. -/
local instance (priority := high) hasSheafify_stageEssentialSurjectivityModules (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, u + 1} Λ X

/-- The free module sheaf on the sheafified representable of an étale scheme `e : W ⟶ X` is the
extension by zero along `e` of the constant sheaf `Λ̲`. -/
def freeModuleSheafIsoExtensionByZero {X W : Scheme.{u}} (e : W ⟶ X) [Etale e] :
    (Sheaf.freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ).obj (Etale.mk e) ≅
      (etaleModuleExtensionByZero.{u, u + 1} Λ e).obj
        ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) := by
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  have hT : IsTerminal (Etale.mk (𝟙 W)) := MorphismProperty.Over.mkIdTerminal _ _
  refine (Sheaf.freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ).mapIso
    (MorphismProperty.Over.isoMk (Iso.refl _) (by simp)) ≪≫
    (Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyFree (Scheme.Etale.smallEtaleCompose e)
      W.smallEtaleTopology X.smallEtaleTopology Λ hT).symm ≪≫
    (etaleModuleExtensionByZero.{u, u + 1} Λ e).mapIso ((constantSheaf _ _).mapIso
      (ULift.moduleEquiv : ULift.{u + 1} Λ ≃ₗ[Λ] Λ).toModuleIso)

variable [IsNoetherianRing Λ]

/-- **The free module sheaf on an affine étale scheme is constructible** (Tag 03S8 for sheaves of
modules), on a quasi-compact and quasi-separated scheme. -/
theorem isConstructibleEtaleModule_freeModuleSheaf {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (W : X.Etale) [IsAffine W.left] :
    IsConstructibleEtaleModule Λ
      ((Sheaf.freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ).obj W) := by
  let e : W.left ⟶ X := W.hom
  have : Etale e := W.prop
  exact (IsConstructibleEtaleModule Λ).prop_of_iso (freeModuleSheafIsoExtensionByZero Λ e).symm
    (isConstructibleEtaleModule_etaleModuleExtensionByZero_of_etale Λ e _
      (isConstructibleEtaleModule_constantSheaf Λ W.left (ModuleCat.of Λ Λ)))

/-- A finite direct sum of free module sheaves on affine étale schemes is constructible. -/
private theorem isConstructibleEtaleModule_biproduct_freeModuleSheaf {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {T : Type} [Finite T] (Z : T → X.Etale)
    (hZ : ∀ t, IsAffine (Z t).left) :
    IsConstructibleEtaleModule Λ (⨁ fun t ↦
      ((Sheaf.freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ).obj (Z t) :
        EtaleModules.{u, u + 1} Λ X)) :=
  (IsConstructibleEtaleModule Λ).prop_of_isLimit_fan (biproduct.isLimit _) fun t ↦ by
    have := hZ t
    exact isConstructibleEtaleModule_freeModuleSheaf Λ (Z t)

/-- **Tag 095N, in the form used here.** A constructible sheaf of `Λ`-modules on a quasi-compact
and quasi-separated scheme is a quotient of a finite direct sum of free module sheaves on
sheafified representables of affine étale schemes. -/
theorem exists_epi_biproduct_freeModuleSheaf {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (F : EtaleModules.{u, u + 1} Λ X)
    (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (n : ℕ) (W : Fin n → X.Etale) (_ : ∀ i, IsAffine (W i).left)
      (p : (⨁ fun i ↦ ((Sheaf.freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ).obj (W i) :
        EtaleModules.{u, u + 1} Λ X)) ⟶ F), Epi p := by
  obtain ⟨n, W, e, he, hW, p, hp⟩ :=
    exists_epi_sigma_etaleModuleExtensionByZero_of_isConstructibleEtaleModule Λ F hF
  exact ⟨n, fun i ↦ Etale.mk (e i), hW, (biproduct.isoCoproduct (C := EtaleModules.{u, u + 1} Λ X)
    fun i ↦ (Sheaf.freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ).obj (Etale.mk (e i))).hom ≫
    (Sigma.mapIso fun i ↦ freeModuleSheafIsoExtensionByZero Λ (e i)).hom ≫ p,
    epi_comp' inferInstance (epi_comp' inferInstance hp)⟩

/-! ### A constructible sheaf is the cokernel of an elementary matrix -/

section Presentation

omit [IsNoetherianRing Λ] in
open Sheaf in
/-- Coverings `W ⟨b, l⟩ ⟶ V b` of each `V b` induce an epimorphism
`⨁_{b, l} Λ_{W ⟨b, l⟩} ⟶ ⨁_b Λ_{V b}`. -/
private theorem epi_biproduct_desc_freeModuleSheaf_map {X : Scheme.{u}} {ι : Type} [Finite ι]
    {κ : ι → Type} [∀ b, Finite (κ b)] {V : ι → X.Etale} {W : (Σ b, κ b) → X.Etale}
    (g : ∀ x, W x ⟶ V x.1)
    (hg : ∀ b, Sieve.ofArrows (fun l : κ b ↦ W ⟨b, l⟩) (fun l ↦ g ⟨b, l⟩) ∈
      X.smallEtaleTopology (V b)) :
    Epi (biproduct.desc fun x ↦ (freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ).map (g x) ≫
      biproduct.ι (fun b ↦ ((freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ).obj (V b) :
        EtaleModules.{u, u + 1} Λ X)) x.1) := by
  refine ⟨fun {G} h₁ h₂ hh ↦ biproduct.hom_ext' _ _ fun b ↦ ?_⟩
  have := epi_sigmaDesc_freeModuleSheaf_map X.smallEtaleTopology Λ _ (hg b)
  rw [← cancel_epi (Limits.Sigma.desc fun l : κ b ↦
    (freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ).map (g ⟨b, l⟩))]
  refine Limits.Sigma.hom_ext _ _ fun l ↦ ?_
  rw [Limits.Sigma.ι_comp_desc_assoc, Limits.Sigma.ι_comp_desc_assoc]
  simpa only [biproduct.ι_desc_assoc, Category.assoc] using
    biproduct.ι _ (⟨b, l⟩ : Σ b, κ b) ≫= hh

open Sheaf in
/-- **A constructible sheaf of modules is the cokernel of an elementary matrix.** On a
quasi-compact and quasi-separated scheme `X`, a constructible sheaf of `Λ`-modules is the cokernel
of a morphism `⨁_s Λ_{V s} ⟶ ⨁_a Λ_{U a}` between finite direct sums of free module sheaves on
affine étale schemes whose components are finite sums `∑_k Λ_{φ} ≫ c` of morphisms induced by
morphisms of étale schemes followed by scalars.

By Tag 095N, twice, `ℱ` is the cokernel of some `⨁ Λ_{V b} ⟶ ⨁ Λ_{U a}`; each component is,
on the members of a covering of `V b`, such a finite sum
(`CategoryTheory.Sheaf.freeModuleSheaf_hom_locally`), and replacing `V b` by finitely many affine
members of a covering (`Stacks.EtaleCohomology.exists_finite_isAffine_covering_le`) changes the
source by an epimorphism (`CategoryTheory.Sheaf.epi_sigmaDesc_freeModuleSheaf_map`), so not the
cokernel. -/
theorem exists_iso_cokernel_elementaryMatrix {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (F : EtaleModules.{u, u + 1} Λ X)
    (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (ι κ : Type) (_ : Finite ι) (_ : Finite κ) (V : ι → X.Etale) (U : κ → X.Etale)
      (_ : ∀ s, IsAffine (V s).left) (_ : ∀ a, IsAffine (U a).left) (N : ι → κ → ℕ)
      (φ : ∀ s a, Fin (N s a) → (V s ⟶ U a)) (c : ∀ s a, Fin (N s a) → Λ),
      Nonempty (cokernel (elementaryMatrix X.smallEtaleTopology Λ V U φ c) ≅ F) := by
  classical
  let P := freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ
  obtain ⟨n, U, hU, p, hp⟩ := exists_epi_biproduct_freeModuleSheaf Λ F hF
  have hK := (IsConstructibleEtaleModule Λ).prop_kernel p
    (isConstructibleEtaleModule_biproduct_freeModuleSheaf Λ U hU) hF
  obtain ⟨n', V, hV, q, hq⟩ := exists_epi_biproduct_freeModuleSheaf Λ (kernel p) hK
  let m := q ≫ kernel.ι p
  let eF : cokernel m ≅ F := cokernelEpiComp q (kernel.ι p) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p))
  -- the components of `m` are locally elementary
  let mc : ∀ b a, P.obj (V b) ⟶ P.obj (U a) := fun b a ↦
    biproduct.ι (fun b ↦ (P.obj (V b) : EtaleModules.{u, u + 1} Λ X)) b ≫ m ≫
      biproduct.π (fun a ↦ (P.obj (U a) : EtaleModules.{u, u + 1} Λ X)) a
  choose S hS hS' using fun b a ↦ freeModuleSheaf_hom_locally X.smallEtaleTopology Λ (mc b a)
  have hSb : ∀ b, (⨅ a, S b a) ∈ X.smallEtaleTopology (V b) := fun b ↦
    Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem _ _ (hS b)
  have hVc : ∀ b, CompactSpace (V b).left := fun b ↦ by
    have := hV b
    infer_instance
  choose E hEfin hEaff hEcov hEle using fun b ↦
    exists_finite_isAffine_covering_le (V b) _ (hSb b)
  -- the refined source
  let k : Fin n' → ℕ := fun b ↦ Nat.card (E b).I₀
  let eqv : ∀ b, Fin (k b) ≃ (E b).I₀ := fun b ↦ (Finite.equivFin _).symm
  let W : (Σ b, Fin (k b)) → X.Etale := fun x ↦ (E x.1).X (eqv x.1 x.2)
  let gx : ∀ x, W x ⟶ V x.1 := fun x ↦ (E x.1).f (eqv x.1 x.2)
  have hmem : ∀ x a, S x.1 a (gx x) := fun x a ↦
    (Stacks.SheafOfModules.FiniteTypeKernel.iInf_apply _ _).1
      (hEle x.1 _ (Sieve.ofArrows_mk _ _ _)) a
  choose N φ c hφ using fun x a ↦ hS' x.1 a (gx x) (hmem x a)
  let Ep : (⨁ fun x ↦ (P.obj (W x) : EtaleModules.{u, u + 1} Λ X)) ⟶
      ⨁ fun b ↦ (P.obj (V b) : EtaleModules.{u, u + 1} Λ X) :=
    biproduct.desc fun x ↦ P.map (gx x) ≫
      biproduct.ι (fun b ↦ (P.obj (V b) : EtaleModules.{u, u + 1} Λ X)) x.1
  have hEp : Epi Ep := epi_biproduct_desc_freeModuleSheaf_map Λ gx fun b ↦ by
    rw [ofArrows_mem_smallEtaleTopology_iff, ← (ofArrows_mem_smallEtaleTopology_iff _).1 (hEcov b)]
    exact (eqv b).surjective.iUnion_comp fun i ↦ Set.range ((E b).f i).left
  have hmat : Ep ≫ m = elementaryMatrix X.smallEtaleTopology Λ W U φ c := by
    refine biproduct.hom_ext' _ _ fun x ↦ biproduct.hom_ext _ _ fun a ↦ ?_
    simp only [elementaryMatrix, Ep, biproduct.ι_desc_assoc, biproduct.ι_matrix_assoc,
      biproduct.lift_π, Category.assoc]
    exact hφ x a
  refine ⟨Σ b, Fin (k b), Fin n, inferInstance, inferInstance, W, U, fun x ↦ hEaff x.1 _, hU, N,
    φ, c, ⟨?_⟩⟩
  rw [← hmat]
  exact cokernelEpiComp Ep m ≪≫ eF

end Presentation

/-! ### Finitely many affine étale schemes and morphisms descend to a stage -/

section Descent

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- The base change of an affine étale scheme over a stage to a later stage is affine and étale. -/
lemma isAffine_etale_overPullback {i j : Iᵒᵖ} (g : j ⟶ i) (B : Over (D.obj i)) [IsAffine B.left]
    [Etale B.hom] : IsAffine ((Over.pullback (D.map g)).obj B).left ∧
      Etale ((Over.pullback (D.map g)).obj B).hom :=
  have : IsAffineHom (pullback.fst B.hom (D.map g)) := inferInstance
  ⟨isAffine_of_isAffineHom (pullback.fst B.hom (D.map g)), by
    change Etale (pullback.snd B.hom (D.map g))
    infer_instance⟩

include hc in
/-- **Finitely many affine étale schemes over the limit, and finitely many morphisms between them,
descend to a stage.** There are a stage `i`, affine étale schemes `B o` over it, isomorphisms of
their base changes to the limit with the given schemes, and morphisms between the `B o` whose base
changes are the given morphisms under these isomorphisms (Tags 01ZM and 07RP). -/
theorem exists_stage_affine_etale_models {O M : Type} [Finite O] [Finite M]
    (A : O → Over c.pt) [∀ o, IsAffine (A o).left] [∀ o, Etale (A o).hom]
    (src tgt : M → O) (φ : ∀ m, A (src m) ⟶ A (tgt m)) :
    ∃ (i : Iᵒᵖ) (B : O → Over (D.obj i)) (e : ∀ o, A o ≅ (Over.pullback (c.π.app i)).obj (B o))
      (ψ : ∀ m, B (src m) ⟶ B (tgt m)),
      (∀ o, IsAffine (B o).left) ∧ (∀ o, Etale (B o).hom) ∧
      ∀ m, φ m ≫ (e (tgt m)).hom = (e (src m)).hom ≫ (Over.pullback (c.π.app i)).map (ψ m) := by
  classical
  have := Fintype.ofFinite O
  have := Fintype.ofFinite M
  have : IsCofiltered Iᵒᵖ := inferInstance
  -- models of the objects
  choose i₀ B₀ hB₀a hB₀e e₀ using fun o ↦ exists_affine_etale_model_of_isLimit D c hc (A o)
  -- a common later stage for the objects
  obtain ⟨j, hj⟩ := Finset.exists_le (Finset.univ.image fun o ↦ (i₀ o).unop)
  have hj' : ∀ o, (i₀ o).unop ≤ j := fun o ↦ hj _ (Finset.mem_image_of_mem _ (Finset.mem_univ o))
  let g : ∀ o, op j ⟶ i₀ o := fun o ↦ (homOfLE (hj' o)).op
  let B₁ : O → Over (D.obj (op j)) := fun o ↦ (Over.pullback (D.map (g o))).obj (B₀ o)
  have hB₁ : ∀ o, IsAffine (B₁ o).left ∧ Etale (B₁ o).hom := fun o ↦ by
    have := hB₀a o
    have := hB₀e o
    exact isAffine_etale_overPullback D (g o) (B₀ o)
  let e₁ : ∀ o, A o ≅ (Over.pullback (c.π.app (op j))).obj (B₁ o) := fun o ↦
    (e₀ o).some ≪≫ (LimitStages.limitIso D c (g o) (B₀ o)).symm
  have hfp : ∀ o, FinitePresentation (B₁ o).hom := fun o ↦ by
    obtain ⟨_, _⟩ := hB₁ o
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  -- models of the morphisms
  choose k v G hG using fun m ↦ LimitStages.exists_hom_limitIso D c hc (op j) (B₁ (src m))
    (B₁ (tgt m)) (hfp _) (hfp _) ((e₁ (src m)).inv ≫ φ m ≫ (e₁ (tgt m)).hom)
  -- a common later stage for the morphisms
  obtain ⟨l, hl⟩ := Finset.exists_le (insert j (Finset.univ.image fun m ↦ (k m).unop))
  have hl' : ∀ m, (k m).unop ≤ l := fun m ↦
    hl _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ m)))
  let w : ∀ m, op l ⟶ k m := fun m ↦ (homOfLE (hl' m)).op
  let h₀ : op l ⟶ op j := (homOfLE (hl _ (Finset.mem_insert_self _ _))).op
  have hwv : ∀ m, w m ≫ v m = h₀ := fun _ ↦ rfl
  refine ⟨op l, fun o ↦ (Over.pullback (D.map h₀)).obj (B₁ o),
    fun o ↦ e₁ o ≪≫ (LimitStages.limitIso D c h₀ (B₁ o)).symm,
    fun m ↦ LimitStages.transportHom D (v m) (w m) h₀ (hwv m) (G m), fun o ↦ ?_, fun o ↦ ?_,
    fun m ↦ ?_⟩
  · obtain ⟨_, _⟩ := hB₁ o
    exact (isAffine_etale_overPullback D h₀ (B₁ o)).1
  · obtain ⟨_, _⟩ := hB₁ o
    exact (isAffine_etale_overPullback D h₀ (B₁ o)).2
  · have key := LimitStages.limitIso_transportHom D c (v m) (w m) h₀ (hwv m)
      ((e₁ (src m)).inv ≫ φ m ≫ (e₁ (tgt m)).hom) (G m) (hG m)
    change φ m ≫ (e₁ (tgt m)).hom ≫ (LimitStages.limitIso D c h₀ (B₁ (tgt m))).inv =
      ((e₁ (src m)).hom ≫ (LimitStages.limitIso D c h₀ (B₁ (src m))).inv) ≫ _
    rw [(Iso.eq_comp_inv _).2 key.symm]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

end Descent

/-! ### Essential surjectivity -/

omit [IsNoetherianRing Λ] in
/-- The inverse image along `f : X ⟶ Y` of the cokernel of an elementary matrix on `Y_étale` is
the cokernel of the elementary matrix on `X_étale` of data isomorphic to the base change of its
data. -/
private theorem nonempty_etaleModuleInverseImage_cokernel_elementaryMatrix_iso {X Y : Scheme.{u}}
    (f : X ⟶ Y) {ι κ : Type} [Finite ι] [Finite κ] {V₀ : ι → Y.Etale} {U₀ : κ → Y.Etale}
    {V : ι → X.Etale} {U : κ → X.Etale} {N : ι → κ → ℕ} (φ₀ : ∀ s a, Fin (N s a) → (V₀ s ⟶ U₀ a))
    (φ : ∀ s a, Fin (N s a) → (V s ⟶ U a)) (cf : ∀ s a, Fin (N s a) → Λ)
    (σ : ∀ s, (smallEtaleBaseChange f).obj (V₀ s) ≅ V s)
    (τ : ∀ a, (smallEtaleBaseChange f).obj (U₀ a) ≅ U a)
    (hστ : ∀ s a k, (smallEtaleBaseChange f).map (φ₀ s a k) ≫ (τ a).hom = (σ s).hom ≫ φ s a k) :
    Nonempty ((etaleModuleInverseImage.{u, u + 1} Λ f).obj
        (cokernel (Sheaf.elementaryMatrix Y.smallEtaleTopology Λ V₀ U₀ φ₀ cf)) ≅
      cokernel (Sheaf.elementaryMatrix X.smallEtaleTopology Λ V U φ cf)) := by
  classical
  let L := etaleModuleInverseImage.{u, u + 1} Λ f
  let β := Sheaf.freeModuleSheafCompSheafPullbackIso Y.smallEtaleTopology
    X.smallEtaleTopology (smallEtaleBaseChange f) Λ
  have hL := Sheaf.map_elementaryMatrix Y.smallEtaleTopology X.smallEtaleTopology
    (smallEtaleBaseChange f) Λ L β
    (Sheaf.sheafPullback_map_smulEnd _ _ (smallEtaleBaseChange f) Λ) V₀ U₀ φ₀ cf
  have hnat := Sheaf.elementaryMatrix_naturality (J := X.smallEtaleTopology) (R := Λ)
    (fun s ↦ (σ s).hom) (fun a ↦ (τ a).hom)
    (fun s a k ↦ (smallEtaleBaseChange f).map (φ₀ s a k)) φ cf hστ
  let M₀ := Sheaf.elementaryMatrix Y.smallEtaleTopology Λ V₀ U₀ φ₀ cf
  let P₀ := Sheaf.freeModuleSheaf.{u, u + 1} Y.smallEtaleTopology Λ
  let P := Sheaf.freeModuleSheaf.{u, u + 1} X.smallEtaleTopology Λ
  let M := Sheaf.elementaryMatrix X.smallEtaleTopology Λ V U φ cf
  let M' := Sheaf.elementaryMatrix X.smallEtaleTopology Λ
    (fun s ↦ (smallEtaleBaseChange f).obj (V₀ s)) (fun a ↦ (smallEtaleBaseChange f).obj (U₀ a))
    (fun s a k ↦ (smallEtaleBaseChange f).map (φ₀ s a k)) cf
  let mS := L.mapBiproduct (fun s ↦ P₀.obj (V₀ s))
  let mT := L.mapBiproduct (fun a ↦ P₀.obj (U₀ a))
  let bS := biproduct.mapIso (fun s ↦ β.app (V₀ s))
  let bT := biproduct.mapIso (fun a ↦ β.app (U₀ a))
  let pS := biproduct.mapIso (fun s ↦ P.mapIso (σ s))
  let pT := biproduct.mapIso (fun a ↦ P.mapIso (τ a))
  have hw : L.map M₀ ≫ (mT ≪≫ bT ≪≫ pT).hom = (mS ≪≫ bS ≪≫ pS).hom ≫ M := by
    have hL' : L.map M₀ ≫ mT.hom = mS.hom ≫ bS.hom ≫ M' ≫ bT.inv :=
      calc L.map M₀ ≫ mT.hom = mS.hom ≫ (mS.inv ≫ L.map M₀ ≫ mT.hom) := by
            rw [Iso.hom_inv_id_assoc]
        _ = mS.hom ≫ bS.hom ≫ M' ≫ bT.inv := by rw [hL]; rfl
    simp only [Iso.trans_hom]
    rw [← Category.assoc, hL']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change mS.hom ≫ bS.hom ≫ M' ≫ biproduct.map (fun a ↦ P.map (τ a).hom) = _
    rw [hnat]
    rfl
  exact ⟨PreservesCokernel.iso L M₀ ≪≫ cokernel.mapIso _ _ _ _ hw⟩

section EssSurj

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- **Stacks 09YU, the essential-surjectivity assertion, clause (3).** Let `X = lim X_i` be the
limit of a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms, and `Λ` a Noetherian ring. Every constructible sheaf of `Λ`-modules on
`X_étale` is isomorphic to the inverse image of a constructible sheaf of `Λ`-modules on some
`(X_i)_étale`.

As in the source, with Tag 095N in place of Tag 09Y9: `ℱ` is the cokernel of an elementary matrix
between finite direct sums of free module sheaves on affine étale schemes
(`Stacks.EtaleCohomology.exists_iso_cokernel_elementaryMatrix`); those finitely many schemes and
morphisms descend to a stage (`Stacks.EtaleCohomology.exists_stage_affine_etale_models`, Tags 01ZM
and 07RP); the elementary matrix they define there has constructible cokernel, and inverse image
commutes with cokernels, direct sums, free module sheaves and scalars. -/
theorem exists_isConstructibleEtaleModule_etaleModuleInverseImage_iso
    (F : EtaleModules.{u, u + 1} Λ c.pt) (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (i : Iᵒᵖ) (F₀ : EtaleModules.{u, u + 1} Λ (D.obj i)), IsConstructibleEtaleModule Λ F₀ ∧
      Nonempty ((etaleModuleInverseImage.{u, u + 1} Λ (c.π.app i)).obj F₀ ≅ F) := by
  classical
  obtain ⟨i₁⟩ := (inferInstance : Nonempty Iᵒᵖ)
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : IsAffineHom (c.π.app i₁) := isAffineHom_π_app D c hc i₁
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₁)
  obtain ⟨ι, κ, _, _, V, U, hV, hU, N, φ, cf, ⟨eF⟩⟩ := exists_iso_cokernel_elementaryMatrix Λ F hF
  -- the data to descend
  let A : ι ⊕ κ → Over c.pt :=
    Sum.elim (fun s ↦ (Etale.forget c.pt).obj (V s)) (fun a ↦ (Etale.forget c.pt).obj (U a))
  have hAa : ∀ o, IsAffine (A o).left := fun | .inl s => hV s | .inr a => hU a
  have hAe : ∀ o, Etale (A o).hom := fun | .inl s => (V s).prop | .inr a => (U a).prop
  let M := Σ (s : ι) (a : κ), Fin (N s a)
  let src : M → ι ⊕ κ := fun m ↦ Sum.inl m.1
  let tgt : M → ι ⊕ κ := fun m ↦ Sum.inr m.2.1
  let φm : ∀ m, A (src m) ⟶ A (tgt m) := fun m ↦ (Etale.forget c.pt).map (φ m.1 m.2.1 m.2.2)
  obtain ⟨i, B, e, ψ, hBa, hBe, hcomp⟩ :=
    exists_stage_affine_etale_models D c hc A src tgt φm
  -- the stage data
  let f := c.π.app i
  let V₀ : ι → (D.obj i).Etale := fun s ↦ MorphismProperty.Over.mk ⊤ (B (Sum.inl s)).hom (hBe _)
  let U₀ : κ → (D.obj i).Etale := fun a ↦ MorphismProperty.Over.mk ⊤ (B (Sum.inr a)).hom (hBe _)
  let φ₀ : ∀ s a, Fin (N s a) → (V₀ s ⟶ U₀ a) := fun s a k ↦
    MorphismProperty.Over.homMk (ψ ⟨s, a, k⟩).left (Over.w (ψ ⟨s, a, k⟩)) trivial
  let M₀ := Sheaf.elementaryMatrix (D.obj i).smallEtaleTopology Λ V₀ U₀ φ₀ cf
  refine ⟨i, cokernel M₀, ?_, ?_⟩
  · exact (IsConstructibleEtaleModule Λ).prop_cokernel _
      (isConstructibleEtaleModule_biproduct_freeModuleSheaf Λ V₀ fun _ ↦ hBa _)
      (isConstructibleEtaleModule_biproduct_freeModuleSheaf Λ U₀ fun _ ↦ hBa _)
  · have hiso : ∀ {Z : c.pt.Etale} {Y : (D.obj i).Etale}
        (ε : (Etale.forget c.pt).obj Z ≅ (Etale.forget c.pt).obj ((smallEtaleBaseChange f).obj Y)),
        ∃ σ : (smallEtaleBaseChange f).obj Y ≅ Z, (Etale.forget c.pt).map σ.hom = ε.inv :=
      fun ε ↦ ⟨((Etale.forgetFullyFaithful c.pt).preimageIso ε).symm,
        (Etale.forgetFullyFaithful c.pt).map_preimage _⟩
    choose σ h₁ using fun s ↦ hiso (Y := V₀ s) (e (Sum.inl s))
    choose τ h₂ using fun a ↦ hiso (Y := U₀ a) (e (Sum.inr a))
    have hστ : ∀ s a k,
        (smallEtaleBaseChange f).map (φ₀ s a k) ≫ (τ a).hom = (σ s).hom ≫ φ s a k := by
      intro s a k
      apply (Etale.forget c.pt).map_injective
      have key : (Over.pullback (c.π.app i)).map (ψ ⟨s, a, k⟩) ≫ (e (tgt ⟨s, a, k⟩)).inv =
          (e (src ⟨s, a, k⟩)).inv ≫ φm ⟨s, a, k⟩ := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← hcomp, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
      rw [Functor.map_comp, Functor.map_comp, h₁ s, h₂ a, forget_map_smallEtaleBaseChange_map]
      exact key
    exact (nonempty_etaleModuleInverseImage_cokernel_elementaryMatrix_iso Λ f φ₀ φ cf σ τ hστ).map
      (· ≪≫ eF)

end EssSurj

end Stacks.EtaleCohomology

end
