module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationAgreement
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationWeilData
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# A realization acts on correspondences of degree zero

Let `G : M_k ⥤ graded F-vector spaces` be a realization (side (2) of Stacks 0FHM,
`Stacks.WeilCohomology.WeilRealization`) and `H^*(X) = G(h(X))` its data (D0)–(D3)
(`Stacks.WeilCohomology.WeilRealization.toWeilData`, Stacks 0FHK). A correspondence
`c ∈ Corr⁰(X, Y)` of degree zero is a morphism `h(X) ⟶ h(Y)` of motives, and `G(c)` is a map
`H^n(X) → H^n(Y)` in every degree. This is a functorial, additive action of correspondences
which is the pullback on graphs (`Stacks.WeilCohomology.WeilRealization.corrAction`); the proof of
Stacks 0FHM compares it with the action `a ↦ pr₂,*(γ(c) ∪ pr₁^*a)` of Stacks 0FHL.

## Main definitions

* `Stacks.WeilCohomology.WeilRealization.corrHom`: `c ∈ Corr⁰(X, Y)` as a morphism of motives
  `h(X) ⟶ h(Y)`.
* `Stacks.WeilCohomology.WeilRealization.corrAction`: the action `c ↦ G(c)`.

## References

* [Stacks Project, Tag 0FHK](https://stacks.math.columbia.edu/tag/0FHK)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CategoryTheory.GradedCategory Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {W : WeilData k F}
  (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

/-- **The action of correspondences of Stacks 0FHL**, `c ↦ (a ↦ pr₂,*(γ(c) ∪ pr₁^*a))`, as an
action of correspondences. -/
def corrFunctorAction : W.CorrAction where
  act f n := corrHomMap hA hB hC f n
  act_comp f g n := corrHomMap_comp hA hB hC f g n
  act_zero X Y n := by
    have h := corrHomMap_add hA hB hC (0 : dz X ⟶ dz Y) 0 n
    rw [add_zero] at h
    exact left_eq_add.1 h
  act_add f g n := corrHomMap_add hA hB hC f g n
  act_graph g f hf n := corrHomMap_of_val_eq_graphHom hA hB hC f g hf n

end Stacks.WeilCohomology.WeilData

namespace Stacks.WeilCohomology.WeilRealization

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (G : WeilRealization k F)

section

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

attribute [local instance] braidedTK monoidalTK

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
    CorrespondenceCategory _)

/-- A correspondence of degree zero `c ∈ Corr⁰(X, Y)` as a morphism of motives
`h(X) = (X, 1, 0) ⟶ h(Y) = (Y, 1, 0)`. -/
def corrHom {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : WeilData.dz X ⟶ WeilData.dz Y) :
    TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⟶ TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) :=
  TwistedKaroubi.ofObjHom (DegreeZero.val f) (DegreeZero.val_mem f)

/-- The underlying correspondence of `corrHom f` is `f`. -/
@[simp]
theorem corrHom_val {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : WeilData.dz X ⟶ WeilData.dz Y) :
    (corrHom f).val = DegreeZero.val f :=
  rfl

/-- `corrHom` sends a composite of correspondences to the composite of motive morphisms. -/
theorem corrHom_comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory}
    (f : WeilData.dz X ⟶ WeilData.dz Y) (g : WeilData.dz Y ⟶ WeilData.dz Z) :
    corrHom (f ≫ g) = corrHom f ≫ corrHom g :=
  TwistedKaroubi.hom_ext rfl

/-- `corrHom` is additive. -/
theorem corrHom_add {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f g : WeilData.dz X ⟶ WeilData.dz Y) :
    corrHom (f + g) = corrHom f + corrHom g :=
  TwistedKaroubi.hom_ext rfl

/-- `corrHom` sends the zero correspondence to the zero morphism. -/
theorem corrHom_zero (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    corrHom (0 : WeilData.dz X ⟶ WeilData.dz Y) = 0 :=
  TwistedKaroubi.hom_ext rfl

/-- If `c` is the graph `[Γ_g]` of `g : Q ⟶ P`, then `corrHom c` is the morphism of motives
`h(P) ⟶ h(Q)` induced by `g`. -/
theorem corrHom_of_val_eq_graphHom {P Q : (SmoothProjectiveScheme k).FullSubcategory} (g : Q ⟶ P)
    (f : WeilData.dz P ⟶ WeilData.dz Q) (hf : DegreeZero.val f = graphHom g) :
    corrHom f = ChowMotiveCat.motMap g :=
  TwistedKaroubi.hom_ext (by rw [corrHom_val, ChowMotiveCat.motMap_val]; exact hf)

/-- `G(c)` on the pieces `G^n(h(X)) → G^n(h(Y))`. -/
def pieceMap {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : WeilData.dz X ⟶ WeilData.dz Y)
    (n : ℤ) :
    (G.cohAlg X).piece n →ₗ[F] (G.cohAlg Y).piece n :=
  (G.functorTK.map (corrHom f) n).hom

/-- `pieceMap` sends a composite of correspondences to the composite of the maps. -/
theorem pieceMap_comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory}
    (f : WeilData.dz X ⟶ WeilData.dz Y) (g : WeilData.dz Y ⟶ WeilData.dz Z) (n : ℤ) :
    G.pieceMap (f ≫ g) n = G.pieceMap g n ∘ₗ G.pieceMap f n := by
  ext a
  simp only [pieceMap, corrHom_comp, Functor.map_comp]
  rfl

/-- `pieceMap` is additive in the correspondence. -/
theorem pieceMap_add {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f g : WeilData.dz X ⟶ WeilData.dz Y) (n : ℤ) :
    G.pieceMap (f + g) n = G.pieceMap f n + G.pieceMap g n := by
  ext a
  simp only [pieceMap, corrHom_add, Functor.map_add]
  rfl

/-- `pieceMap` of the zero correspondence is zero. -/
theorem pieceMap_zero (X Y : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    G.pieceMap (0 : WeilData.dz X ⟶ WeilData.dz Y) n = 0 := by
  ext a
  simp only [pieceMap, corrHom_zero, Functor.map_zero]
  rfl

/-- **`G(c) : H^n(X) → H^n(Y)`** for a correspondence `c ∈ Corr⁰(X, Y)`. -/
def corrMapG {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : WeilData.dz X ⟶ WeilData.dz Y)
    (n : ℤ) :
    (G.cohAlg X).grade n →ₗ[F] (G.cohAlg Y).grade n :=
  ((G.cohAlg Y).gradeEquiv n).symm.toLinearMap ∘ₗ G.pieceMap f n ∘ₗ
    ((G.cohAlg X).gradeEquiv n).toLinearMap

/-- `G(c' ∘ c) = G(c') ∘ G(c)` on `H^n`. -/
theorem corrMapG_comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory}
    (f : WeilData.dz X ⟶ WeilData.dz Y) (g : WeilData.dz Y ⟶ WeilData.dz Z) (n : ℤ) :
    G.corrMapG (f ≫ g) n = G.corrMapG g n ∘ₗ G.corrMapG f n := by
  refine LinearMap.ext fun a ↦ ?_
  simp only [corrMapG, pieceMap_comp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- `G(0) = 0` on `H^n`. -/
theorem corrMapG_zero (X Y : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    G.corrMapG (0 : WeilData.dz X ⟶ WeilData.dz Y) n = 0 := by
  refine LinearMap.ext fun a ↦ ?_
  simp only [corrMapG, pieceMap_zero, LinearMap.comp_apply, LinearMap.zero_apply, map_zero]

/-- `G(c + c') = G(c) + G(c')` on `H^n`. -/
theorem corrMapG_add {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f g : WeilData.dz X ⟶ WeilData.dz Y) (n : ℤ) :
    G.corrMapG (f + g) n = G.corrMapG f n + G.corrMapG g n := by
  refine LinearMap.ext fun a ↦ ?_
  simp only [corrMapG, pieceMap_add, LinearMap.comp_apply, LinearMap.add_apply, map_add,
    LinearEquiv.coe_coe]

/-- In the total cohomology of `Y`, `G(c) x` is the degree-`n` component given by applying
`pieceMap` to the piece of `x`. -/
theorem coe_corrMapG {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : WeilData.dz X ⟶ WeilData.dz Y) (n : ℤ) (x : (G.cohAlg X).grade n) :
    (G.corrMapG f n x : (G.cohAlg Y).Total) =
      DirectSum.of (G.cohAlg Y).piece n (G.pieceMap f n ((G.cohAlg X).gradeEquiv n x)) :=
  ExternallyGradedAlgebra.gradeEquiv_symm_apply_coe _ _ _

/-- An element of `H^n(X)` is, in the total cohomology, the inclusion of its image under
`gradeEquiv` in the degree-`n` piece. -/
theorem coe_eq_of_gradeEquiv {X : (SmoothProjectiveScheme k).FullSubcategory} (n : ℤ)
    (x : (G.cohAlg X).grade n) :
    (x : (G.cohAlg X).Total) =
      DirectSum.of (G.cohAlg X).piece n ((G.cohAlg X).gradeEquiv n x) := by
  conv_lhs => rw [← ((G.cohAlg X).gradeEquiv n).symm_apply_apply x]
  exact ExternallyGradedAlgebra.gradeEquiv_symm_apply_coe _ _ _

/-- On a graph `[Γ_g]`, `G` is the pullback `g^*`. -/
theorem corrMapG_of_val_eq_graphHom {P Q : (SmoothProjectiveScheme k).FullSubcategory} (g : Q ⟶ P)
    (f : WeilData.dz P ⟶ WeilData.dz Q) (hf : DegreeZero.val f = graphHom g) (n : ℤ)
    (x : (G.cohAlg P).grade n) :
    (G.corrMapG f n x : (G.cohAlg Q).Total) = G.cohPull g x := by
  rw [coe_corrMapG, coe_eq_of_gradeEquiv G n x, cohPull, Functor.cohomologyMap_of]
  congr 1
  show (G.functorTK.map (corrHom f) n).hom _ = _
  rw [corrHom_of_val_eq_graphHom g f hf]

/-- **The action of correspondences of a realization**, `c ↦ G(c)`. -/
def corrAction : G.toWeilData.CorrAction where
  act f n := G.corrMapG f n
  act_comp f g n := G.corrMapG_comp f g n
  act_zero X Y n := G.corrMapG_zero X Y n
  act_add f g n := G.corrMapG_add f g n
  act_graph g f hf n :=
    LinearMap.ext fun x ↦ Subtype.ext (G.corrMapG_of_val_eq_graphHom g f hf n x)

end

end Stacks.WeilCohomology.WeilRealization

end
