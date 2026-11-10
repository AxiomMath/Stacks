module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Objects
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDescentOfLocal
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringLocallyFull
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDescent

/-!
Descent of sheaves along hypercoverings over an object, from local lifts of edges and triangles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.Hypercovering

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasPullbacks C]

variable (P : Pretopology C) {X : C} (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- **Local lifts through a covering morphism.** A morphism from an object of `C/X` to the target
of a covering morphism of semi-representable objects over `X` lifts through it locally. -/
theorem exists_local_lift_of_isCoveringOver_hypercoveringObjectDescentOver
    {U M : FormalCoproduct.{u} (Over X)} (f : U ⟶ M) (hf : IsCoveringOver P f) {V : Over X}
    (μ : (FormalCoproduct.incl _).obj V ⟶ M) :
    ∃ R : Sieve V, R ∈ (P.toGrothendieck.over X) V ∧ ∀ ⦃W : Over X⦄ (g : W ⟶ V), R g →
      ∃ ξ : (FormalCoproduct.incl _).obj W ⟶ U, ξ ≫ f = (FormalCoproduct.incl _).map g ≫ μ := by
  rw [← μ.fromIncl_asSigma]
  generalize μ.asSigma = q
  obtain ⟨j, φ⟩ := q
  have hgen : Sieve.generate (Presieve.ofArrows
      (fun i : { i : U.I // f.f i = j } ↦ (U.obj i.1).left)
      (fun i ↦ (f.φ i.1).left ≫ eqToHom (congrArg (fun k ↦ (M.obj k).left) i.2))) ∈
        P.toGrothendieck (M.obj j).left := ⟨_, hf j, Sieve.le_generate _⟩
  refine ⟨_, P.toGrothendieck.overEquiv_symm_mem_over V _
    (P.toGrothendieck.pullback_stable φ.left hgen), fun W g hg => ?_⟩
  rw [Sieve.overEquiv_symm_iff] at hg
  obtain ⟨Y, p, q, ⟨⟨i, rfl⟩⟩, hcomm⟩ := hg
  simp only [eqToHom_refl, Category.comp_id] at hcomm
  have hw : p ≫ (U.obj i).hom = W.hom := by
    rw [← Over.w (f.φ i), ← Category.assoc, hcomm, Category.assoc, Over.w φ, Over.w g]
  refine ⟨FormalCoproduct.Hom.fromIncl i (Over.homMk p hw),
    FormalCoproduct.hom_ext rfl fun _ => ?_⟩
  change (Over.homMk p hw ≫ f.φ i) ≫ eqToHom rfl = g ≫ φ
  rw [eqToHom_refl, Category.comp_id]
  exact Over.OverMorphism.ext hcomm

/-- Locally, a morphism to the matching object whose faces are the `e i` lifts to a simplex of `K`
whose faces are the `e i`. -/
private theorem exists_local_faces_of_isHypercovering (hK : IsHypercovering P K) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ FormalCoproduct.{u} (Over X),
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    {V : Over X} (e : Fin (n + 2) → ((FormalCoproduct.incl _).obj V ⟶ K _⦋n⦌))
    (μ : (FormalCoproduct.incl _).obj V ⟶ ((SimplicialObject.cosk n).obj K).obj (op ⦋n + 1⦌))
    (he : ∀ i, μ ≫ ((SimplicialObject.cosk n).obj K).map (SimplexCategory.δ i).op ≫
      ((SimplexCategory.Truncated.inclusion n).op.ranCounit.app
        ((SimplicialObject.truncation n).obj K)).app (op ⟨⦋n⦌, le_rfl⟩) = e i) :
    ∃ R : Sieve V, R ∈ (P.toGrothendieck.over X) V ∧ ∀ ⦃W : Over X⦄ (g : W ⟶ V), R g →
      ∃ ξ : (FormalCoproduct.incl _).obj W ⟶ K _⦋n + 1⦌,
        ∀ i, ξ ≫ K.δ i = (FormalCoproduct.incl _).map g ≫ e i := by
  obtain ⟨R, hR, hl⟩ := exists_local_lift_of_isCoveringOver_hypercoveringObjectDescentOver P _
    (hK.2 n) μ
  refine ⟨R, hR, fun W g hg => ?_⟩
  obtain ⟨ξ, hξ⟩ := hl g hg
  exact ⟨ξ, fun i => (comp_δ_eq_of_unit_hypercoveringLocalLifts n ξ i).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hξ).trans
      ((Category.assoc _ _ _).trans (congrArg _ (he i)))))⟩

/-- **Condition (2) of a hypercovering of `X`**: any two vertices are locally the two vertices of
an edge. -/
theorem hasLocalEdges_of_isHypercovering_hypercoveringObjectDescentOver
    (hK : IsHypercovering P K) :
    HasLocalEdgesTotalSiteDescent (P.toGrothendieck.over X) K := by
  intro V a b
  obtain ⟨R, hR, hl⟩ := exists_local_faces_of_isHypercovering P K hK 0 _
    (pairMatchingHomHypercoveringLocalLifts a b) (pairMatchingHom_face_hypercoveringLocalLifts a b)
  refine GrothendieckTopology.superset_covering _ (fun W g hg => ?_) hR
  obtain ⟨ξ, hf⟩ := hl g hg
  exact ⟨ξ, (hf 1).trans (by simp), (hf 0).trans (by simp)⟩

/-- **Condition (3) of a hypercovering of `X` in degree two**: any boundary of a triangle is
locally the boundary of a `2`-simplex. -/
theorem hasLocalTriangles_of_isHypercovering_hypercoveringObjectDescentOver
    (hK : IsHypercovering P K) :
    HasLocalTrianglesTotalSiteDescent (P.toGrothendieck.over X) K := by
  intro V e₀₁ e₀₂ e₁₂ h₀ h₁ h₂
  let e : Fin 3 → ((FormalCoproduct.incl _).obj V ⟶ K _⦋1⦌) := ![e₁₂, e₀₂, e₀₁]
  have he : IsTriangleBoundary K e := ⟨h₂.symm, h₁.symm, h₀.symm⟩
  obtain ⟨R, hR, hl⟩ := exists_local_faces_of_isHypercovering P K hK 1 e _ he.matchingHom_face
  refine GrothendieckTopology.superset_covering _ (fun W g hg => ?_) hR
  obtain ⟨ξ, hf⟩ := hl g hg
  exact ⟨ξ, hf 2, hf 1, hf 0⟩

/-- **Stacks 0D8K (1).** Let `C` be a site with fibre products, `X` an object of `C` and `K` a
hypercovering of `X`. Then `a^{-1} : Sh(C/X) ⥤ Sh((C/K)_total)` is fully faithful with essential
image the cartesian sheaves of sets, and `a_*` is a quasi-inverse: the unit `F ⟶ a_* a^{-1} F` is
invertible for every `F`, and the counit `a^{-1} a_* G ⟶ G` is invertible for every cartesian
`G`. -/
theorem descent_sheaves_of_isHypercovering_over_hypercoveringObjectDescentOver
    (hK : IsHypercovering P K) :
    Nonempty (totalLocalizationMorphism (P.toGrothendieck.over X) K).inverseImage.FullyFaithful ∧
      (∀ F : Sheaf (situation (P.toGrothendieck.over X) K).totalTopology (Type u),
        (totalLocalizationMorphism (P.toGrothendieck.over X) K).inverseImage.essImage F ↔
          (situation (P.toGrothendieck.over X) K).IsCartesianSheaf F) ∧
      IsIso (totalLocalizationMorphism (P.toGrothendieck.over X) K).adj.unit ∧
      ∀ F : Sheaf (situation (P.toGrothendieck.over X) K).totalTopology (Type u),
        (situation (P.toGrothendieck.over X) K).IsCartesianSheaf F →
          IsIso ((totalLocalizationMorphism (P.toGrothendieck.over X) K).adj.counit.app F) :=
  descent_sheaves_of_local_hypercoveringDescentOfLocal (P.toGrothendieck.over X) K
    (isCoverDense_totalForget_over P K hK.1)
    (hasLocalEdges_of_isHypercovering_hypercoveringObjectDescentOver P K hK)
    (hasLocalTriangles_of_isHypercovering_hypercoveringObjectDescentOver P K hK)

/-- **Stacks 0D8K (2).** Let `C` be a site with fibre products, `X` an object of `C` and `K` a
hypercovering of `X`. Then `a^{-1} : Ab(C/X) ⥤ Ab((C/K)_total)` is fully faithful with essential
image the cartesian sheaves of abelian groups, and `a_*` is a quasi-inverse. -/
theorem descent_abelianSheaves_of_isHypercovering_over_hypercoveringObjectDescentOver
    (hK : IsHypercovering P K) :
    Nonempty ((totalForget K).sheafPushforwardContinuous Ab.{u}
        ((situation (P.toGrothendieck.over X) K).totalTopology)
        (P.toGrothendieck.over X)).FullyFaithful ∧
      (∀ F : Sheaf (situation (P.toGrothendieck.over X) K).totalTopology Ab.{u},
        ((totalForget K).sheafPushforwardContinuous Ab.{u}
            ((situation (P.toGrothendieck.over X) K).totalTopology)
            (P.toGrothendieck.over X)).essImage F ↔
          (situation (P.toGrothendieck.over X) K).IsCartesianAbSheaf F) ∧
      IsIso (abelianTotalAdjunction (P.toGrothendieck.over X) K).unit ∧
      ∀ F : Sheaf (situation (P.toGrothendieck.over X) K).totalTopology Ab.{u},
        (situation (P.toGrothendieck.over X) K).IsCartesianAbSheaf F →
          IsIso ((abelianTotalAdjunction (P.toGrothendieck.over X) K).counit.app F) :=
  descent_abelianSheaves_of_local_hypercoveringDescentOfLocal (P.toGrothendieck.over X) K
    (isCoverDense_totalForget_over P K hK.1)
    (hasLocalEdges_of_isHypercovering_hypercoveringObjectDescentOver P K hK)
    (hasLocalTriangles_of_isHypercovering_hypercoveringObjectDescentOver P K hK)

end CategoryTheory.SimplicialSemiRepresentable

end
