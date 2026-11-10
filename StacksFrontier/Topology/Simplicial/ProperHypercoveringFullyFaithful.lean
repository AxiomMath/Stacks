module

public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianAdjunctionForget
public import StacksFrontier.Topology.Simplicial.ProperHypercoveringPoints

/-!
# Inverse image along a proper hypercovering is fully faithful

Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces and
let `a : U ⟶ X` be an augmentation which is a proper hypercovering of `X`. Then the inverse
images

`a^{-1} : Sh(X) ⥤ Sh(U_Zar)` and `a^{-1} : Ab(X) ⥤ Ab(U_Zar)`

along the morphism of topoi `a : Sh(U_Zar) ⟶ Sh(X)` of Tag 09W4 are fully faithful, their
essential images are the cartesian sheaves, and `a_*` is a quasi-inverse on the cartesian
sheaves.

The proof is by descent on stalks. For a cartesian sheaf `G` on `U_Zar` and a point `u ∈ U_0`
over `x ∈ X`, the stalk of `a_* G` at `x` maps bijectively to the stalk of `G_0` at `u`
(`Stacks.Topology.Simplicial.Augmentation.bijective_stalkComparison_π_zero`), which is the
statement that the degree-zero component of the counit `a^{-1} a_* G ⟶ G` is an isomorphism on
stalks; the other components follow by cartesianness. Since `a^{-1} F` is cartesian and
`a_0` is surjective, the unit `F ⟶ a_* a^{-1} F` is then an isomorphism too.

## Main results

* `Stacks.Topology.Simplicial.Augmentation.isIso_counit_app_of_isCartesian` and
  `.isIso_unit_app`: the counit at a cartesian sheaf and the unit are isomorphisms, for any
  augmentation of a simplicial space satisfying
  `Stacks.Topology.Simplicial.Augmentation.DescentConditions`.
* `Stacks.Topology.Simplicial.ProperHypercovering.inverseImage_fullyFaithful_of_isHypercovering`:
  **Stacks 0DAG**, sheaves of sets.
* `abelianInverseImage_fullyFaithful_of_isHypercovering`, in the same namespace:
  **Stacks 0DAG**, sheaves of abelian groups.

## Implementation notes

The source deduces the statement from Tag 0DA8 for the hypercovering of `X` in `LC_qc` which
Tag 09X5 produces, through the comparison diagram of Tag 0DAF. Here the descent is carried out
directly on stalks, using proper base change in degree zero in the form of Tag 09V3; the
point-set input from the hypercovering is collected in
`Stacks.Topology.Simplicial.ProperHypercovering.descentConditions`.

## References

* [Stacks Project, Tag 0DAG](https://stacks.math.columbia.edu/tag/0DAG)
* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TopologicalSpace

universe u

namespace Stacks.Topos.AbelianPushforward

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u)))

/-- The transpose of an identity is the counit. -/
private theorem homEquiv_symm_eq_counit {A : Type*} {B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) (Z : B) (g : R.obj Z ⟶ R.obj Z) (hg : g = 𝟙 _) :
    (adj.homEquiv _ Z).symm g = adj.counit.app Z := by
  subst hg
  simp [Adjunction.homEquiv_counit]

/-- **The counit of the abelian adjunction is the geometric counit.** Forgetting the
abelian-group operations takes the counit of `abelianInverseImageAdjPushforward` to the counit of
the geometric adjunction `f⁻¹ ⊣ f_*`. -/
theorem abelianInverseImageAdjPushforward_counit_forget (G : Sheaf J AddCommGrpCat.{u}) :
    (sheafCompose J (forget AddCommGrpCat.{u})).map
        ((abelianInverseImageAdjPushforward J f).counit.app G) =
      f.adj.counit.app ((sheafCompose J (forget AddCommGrpCat.{u})).obj G) := by
  have h₁ : (abelianInverseImageAdjPushforward J f).counit.app G =
      ((abelianInverseImageAdjPushforward J f).homEquiv _ G).symm (𝟙 _) :=
    (homEquiv_symm_eq_counit _ _ _ rfl).symm
  exact (congrArg (sheafCompose J (forget AddCommGrpCat.{u})).map h₁).trans
    ((abelianInverseImageAdjPushforward_homEquiv_symm_forget J f _ G (𝟙 _)).trans
      (homEquiv_symm_eq_counit f.adj _ _ (CategoryTheory.Functor.map_id _ _)))

end Stacks.Topos.AbelianPushforward

namespace Stacks.Topology.Simplicial

open SimplicialSheafSystem

namespace SimplicialSheafSystem

variable {Z : SimplicialObject TopCat.{u}}

/-- A morphism of simplicial sheaf systems all of whose components are isomorphisms is an
isomorphism. -/
theorem isIso_of_isIso_componentHom {S T : SimplicialSheafSystem Z (Type u)} (σ : S ⟶ T)
    (h : ∀ n, IsIso (σ.componentHom n)) : IsIso σ := by
  refine ⟨⟨{ componentHom := fun n => inv (σ.componentHom n), naturality := ?_ }, ?_, ?_⟩⟩
  · intro n m φ V
    have hn' : Augmentation.systemTransition Z T φ ≫
        (Augmentation.pf (Z.map φ)).map (inv (σ.componentHom n)) =
        inv (σ.componentHom m) ≫ Augmentation.systemTransition Z S φ := by
      rw [IsIso.eq_inv_comp, ← Category.assoc,
        ← ProperHypercovering.systemTransition_naturality Z σ φ, Category.assoc,
        ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
    exact congrArg (fun t => t.hom.app V) hn'
  · exact Hom.ext _ _ fun n => IsIso.hom_inv_id (σ.componentHom n)
  · exact Hom.ext _ _ fun n => IsIso.inv_hom_id (σ.componentHom n)

end SimplicialSheafSystem

namespace Augmentation

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}}
  {a : Y ⟶ (SimplicialObject.const TopCat).obj X}

/-- The component of the counit of the system adjunction of Tag 09W4 in degree `n` is the
adjoint of the projection of the direct image to degree `n`. -/
theorem systemAdjunction_counit_componentHom (S : SimplicialSheafSystem Y (Type u))
    (n : SimplexCategoryᵒᵖ) :
    ((systemAdjunction Y X a).counit.app S).componentHom n =
      ((adj (a.app n)).homEquiv _ _).symm (limit.π (pushforwardDiagram Y X a S) n.unop) :=
  rfl

variable (H : DescentConditions Y X a)
include H

/-- **The counit of the system adjunction is an isomorphism at a cartesian system.** -/
theorem isIso_systemAdjunction_counit_app {S : SimplicialSheafSystem Y (Type u)}
    (hS : S.IsCartesianSystem) : IsIso ((systemAdjunction Y X a).counit.app S) := by
  let σ := (systemAdjunction Y X a).counit.app S
  have h₀ : IsIso (σ.componentHom (op ⦋0⦌)) := by
    rw [systemAdjunction_counit_componentHom]
    exact (Stacks.Sheaves.PullbackUnit.isIso_homEquiv_symm_iff _ _).2
      (bijective_stalkComparison_π_zero H hS)
  refine isIso_of_isIso_componentHom σ fun n => ?_
  let φ : n ⟶ op ⦋0⦌ := (SimplexCategory.const ⦋0⦌ n.unop 0).op
  have hT : IsIso (ProperHypercovering.systemCartesianTransition Y
      ((𝟭 (SimplicialSheafSystem Y (Type u))).obj S) φ) := hS φ
  have hP : IsIso (ProperHypercovering.systemCartesianTransition Y
      (((pushforwardDiagramFunctor Y X a ⋙ lim) ⋙ pullbackSystemFunctor Y X a).obj S) φ) :=
    ProperHypercovering.isIso_systemCartesianTransition_pullbackSystem Y X a _ φ
  have e := ProperHypercovering.systemCartesianTransition_naturality Y σ φ
  have h' : IsIso ((pb (Y.map φ)).map (σ.componentHom (op ⦋0⦌)) ≫
      ProperHypercovering.systemCartesianTransition Y
        ((𝟭 (SimplicialSheafSystem Y (Type u))).obj S) φ) := inferInstance
  rw [e] at h'
  exact IsIso.of_isIso_comp_left (f := ProperHypercovering.systemCartesianTransition Y
    (((pushforwardDiagramFunctor Y X a ⋙ lim) ⋙ pullbackSystemFunctor Y X a).obj S) φ)
    (σ.componentHom n)

/-- **The counit of `a^{-1} ⊣ a_*` is an isomorphism at a cartesian sheaf.** -/
theorem isIso_counit_app_of_isCartesian
    (G : Sheaf (SimplicialOpen.grothendieckTopology Y) (Type u))
    (hG : ProperHypercovering.IsCartesian Y G) :
    IsIso ((augmentationMorphism Y X a).adj.counit.app G) := by
  change IsIso (((systemAdjunction Y X a).comp
    (presentation Y).toEquivalence.symm.toAdjunction).counit.app G)
  rw [Adjunction.comp_counit_app]
  have : IsIso ((systemAdjunction Y X a).counit.app
      ((presentation Y).toEquivalence.symm.inverse.obj G)) :=
    isIso_systemAdjunction_counit_app H hG
  infer_instance

/-- **The unit of `a^{-1} ⊣ a_*` is an isomorphism.** The inverse image of a sheaf is cartesian,
so the counit is invertible there; by a triangle identity the inverse image of the unit is
invertible, and the inverse image reflects isomorphisms, `a_0` being surjective. -/
theorem isIso_unit_app (F : TopCat.Sheaf (Type u) X) :
    IsIso ((augmentationMorphism Y X a).adj.unit.app F) := by
  let Φ := augmentationMorphism Y X a
  let E := (presentation Y).toEquivalence
  have hcart : ProperHypercovering.IsCartesian Y (Φ.inverseImage.obj F) := by
    intro n m φ
    exact ProperHypercovering.isIso_systemCartesianTransition_of_iso Y
      (E.counitIso.app ((pullbackSystemFunctor Y X a).obj F)) φ
      (ProperHypercovering.isIso_systemCartesianTransition_pullbackSystem Y X a F φ)
  have hε := isIso_counit_app_of_isCartesian H _ hcart
  have hL : IsIso (Φ.inverseImage.map (Φ.adj.unit.app F)) := by
    rw [← IsIso.inv_eq_of_inv_hom_id (Φ.adj.left_triangle_components F)]
    infer_instance
  have hP : IsIso ((pullbackSystemFunctor Y X a).map (Φ.adj.unit.app F)) := by
    have : IsIso (E.inverse.map ((pullbackSystemFunctor Y X a).map (Φ.adj.unit.app F))) := hL
    exact isIso_of_reflects_iso _ E.inverse
  have h₀ : IsIso ((pb (a.app (op ⦋0⦌))).map (Φ.adj.unit.app F)) :=
    ProperHypercovering.isIso_componentHom Y
      (asIso ((pullbackSystemFunctor Y X a).map (Φ.adj.unit.app F))) (op ⦋0⦌)
  exact Stacks.Sheaves.PullbackUnit.isIso_of_isIso_pullback_map _ H.surjective₀ _ h₀

end Augmentation

namespace ProperHypercovering

open Augmentation

variable (Y : SimplicialObject LocallyQuasiCompactHausdorff.{u})
  (X : LocallyQuasiCompactHausdorff.{u})
  (a : Y ⟶ (SimplicialObject.const LocallyQuasiCompactHausdorff).obj X)

/-- An adjunction with invertible unit and counit invertible on a predicate `P` containing the
essential image of the left adjoint has fully faithful left adjoint with essential image `P`. -/
private theorem full_faithful_essImage_of_isIso_unit {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) (P : B → Prop) (hP : ∀ G, L.essImage G → P G)
    (hunit : ∀ F, IsIso (adj.unit.app F)) (hcounit : ∀ G, P G → IsIso (adj.counit.app G)) :
    L.Full ∧ L.Faithful ∧ (∀ G, L.essImage G ↔ P G) ∧ (∀ F, IsIso (adj.unit.app F)) ∧
      (∀ G, P G → IsIso (adj.counit.app G)) := by
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  refine ⟨hff.full, hff.faithful, fun G => ⟨hP G, fun hG => ?_⟩, hunit, hcounit⟩
  have := hcounit G hG
  exact ⟨_, ⟨asIso (adj.counit.app G)⟩⟩

/-- **Stacks 0DAG, sheaves of sets.** Let `U` be a simplicial object of `LC` and `a : U ⟶ X` an
augmentation which is a proper hypercovering of `X`. Then `a^{-1} : Sh(X) ⥤ Sh(U_Zar)` is fully
faithful, its essential image consists exactly of the cartesian sheaves, and `a_*` is a
quasi-inverse: the unit of `a^{-1} ⊣ a_*` is invertible, and so is its counit at every
cartesian sheaf. Here `a : Sh(U_Zar) ⟶ Sh(X)` is the morphism of topoi of Tag 09W4. -/
@[stacks 0DAG "sheaves of sets"]
theorem inverseImage_fullyFaithful_of_isHypercovering
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩) :
    (inverseImage Y X a).Full ∧ (inverseImage Y X a).Faithful ∧
      (∀ G, (inverseImage Y X a).essImage G ↔ IsCartesian (U Y) G) ∧
      (∀ F, IsIso ((augmentationTopoi Y X a).adj.unit.app F)) ∧
      (∀ G, IsCartesian (U Y) G → IsIso ((augmentationTopoi Y X a).adj.counit.app G)) := by
  have H := descentConditions hyp
  exact full_faithful_essImage_of_isIso_unit (augmentationTopoi Y X a).adj (IsCartesian (U Y))
    (fun _ hG => isCartesian_of_mem_essImage Y X a hG) (isIso_unit_app H)
    (isIso_counit_app_of_isCartesian H)

/-- **Stacks 0DAG, sheaves of abelian groups.** Let `U` be a simplicial object of `LC` and
`a : U ⟶ X` an augmentation which is a proper hypercovering of `X`. Then
`a^{-1} : Ab(X) ⥤ Ab(U_Zar)` is fully faithful, its essential image consists exactly of the
cartesian abelian sheaves, and `a_*` is a quasi-inverse: the unit of `a^{-1} ⊣ a_*` is
invertible, and so is its counit at every cartesian abelian sheaf. -/
@[stacks 0DAG "sheaves of abelian groups"]
theorem abelianInverseImage_fullyFaithful_of_isHypercovering
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩) :
    (abelianInverseImage Y X a).Full ∧ (abelianInverseImage Y X a).Faithful ∧
      (∀ G, (abelianInverseImage Y X a).essImage G ↔ IsCartesianAb (U Y) G) ∧
      (∀ F, IsIso ((abelianAdjunction Y X a).unit.app F)) ∧
      (∀ G, IsCartesianAb (U Y) G → IsIso ((abelianAdjunction Y X a).counit.app G)) := by
  obtain ⟨-, -, -, hunit, hcounit⟩ := inverseImage_fullyFaithful_of_isHypercovering Y X a hyp
  let Jx := Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj X)
  let JU := SimplicialOpen.grothendieckTopology (U Y)
  have hunitAb : ∀ F, IsIso ((abelianAdjunction Y X a).unit.app F) := by
    intro F
    have : IsIso ((sheafCompose Jx (forget AddCommGrpCat.{u})).map
        ((abelianAdjunction Y X a).unit.app F)) := by
      rw [Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_unit_forget JU
        (augmentationTopoi Y X a) F]
      exact hunit _
    exact isIso_of_reflects_iso _ (sheafCompose Jx (forget AddCommGrpCat.{u}))
  have hcounitAb : ∀ G, IsCartesianAb (U Y) G →
      IsIso ((abelianAdjunction Y X a).counit.app G) := by
    intro G hG
    have : IsIso ((sheafCompose JU (forget AddCommGrpCat.{u})).map
        ((abelianAdjunction Y X a).counit.app G)) := by
      rw [Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_counit_forget JU
        (augmentationTopoi Y X a) G]
      exact hcounit _ hG
    exact isIso_of_reflects_iso _ (sheafCompose JU (forget AddCommGrpCat.{u}))
  exact full_faithful_essImage_of_isIso_unit (abelianAdjunction Y X a) (IsCartesianAb (U Y))
    (fun _ hG => isCartesianAb_of_mem_essImage Y X a hG) hunitAb hcounitAb

end ProperHypercovering

end Stacks.Topology.Simplicial
