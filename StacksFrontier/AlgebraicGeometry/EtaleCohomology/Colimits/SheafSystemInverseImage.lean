module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleSheafBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackDiagram
public import StacksFrontier.CategoryTheory.Limits.SystemColimit

/-!
# Inverse images of systems of étale sheaves with arbitrary coefficients

Let `(X_i, f_{i'i})` be an inverse system of schemes over a preordered set and let
`(ℱ_i, φ_{i'i})` be a system of sheaves on it with coefficients in a category `A` ([Stacks,
Tag 0EZL]). For a cone with projections `f_i : X ⟶ X_i`, the inverse images `f_i⁻¹ℱ_i` form a
diagram on the small étale site of `X`, whose maps are the comparisons `f_{i'}⁻¹ ≅ f_i⁻¹f_{i'i}⁻¹`
followed by `f_i⁻¹φ_{i'i}`; the hypothesis `ℱ = colim f_i⁻¹ℱ_i` of [Stacks, Tag 0EYM] is that a
family `ι_i : f_i⁻¹ℱ_i ⟶ ℱ` is a colimit of this diagram.

For a morphism `e : (Y_i) ⟶ (T_i)` of inverse systems, the inverse images `e_i⁻¹ℱ_i` of a system
on `(T_i)` form a system on `(Y_i)`, and for a morphism `e : Y ⟶ T` of the limits compatible with
`e` the inverse image `e⁻¹ℱ` of `ℱ = colim p_i⁻¹ℱ_i` is the colimit `colim q_i⁻¹e_i⁻¹ℱ_i`, as is
used in the proof of [Stacks, Tag 0EZT].

## Main definitions

* `Stacks.EtaleCohomology.EtaleSheafSystem.sheafPullbackDiagramMap`: the maps of the diagram of
  inverse images to the vertex of a cone.
* `Stacks.EtaleCohomology.EtaleSheafSystem.IsSheafPullbackColimitPresentation`: the colimit
  presentation `ℱ = colim f_i⁻¹ℱ_i`.
* `Stacks.EtaleCohomology.EtaleSheafSystem.sheafPullback`: the system `i ↦ e_i⁻¹ℱ_i`.

## Main results

* `Stacks.EtaleCohomology.EtaleSheafSystem.sheafPullbackDiagramMap_comp`: the maps of the diagram
  compose.
* `Stacks.EtaleCohomology.EtaleSheafSystem.isSheafPullbackColimitPresentation_sheafPullback`:
  the inverse image of a colimit presentation is a colimit presentation.

## Implementation notes

The comparisons of inverse images along composites are written on components with iterated
inverse images as sources (`Stacks.EtaleCohomology.smallEtaleSheafPullbackCompApp`), and each
identity between them is deduced from the associativity pentagon and naturality squares by a
rearrangement in an arbitrary category.

## References

* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w w' v u

namespace Stacks.EtaleCohomology

variable (A : Type w) [Category.{w'} A]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (smallEtalePushforward f A).IsRightAdjoint]

local notation "App" => smallEtaleSheafPullbackCompApp

variable {I : Type v} [Preorder I]

/-- The comparison of inverse images along a composite transition of an inverse system of
schemes is the comparison along the named composite. -/
theorem systemPullbackComp_eq_smallEtaleSheafPullbackComp' (D : Iᵒᵖ ⥤ Scheme.{u}) {i j k : Iᵒᵖ}
    (a : i ⟶ j) (b : j ⟶ k) :
    systemPullbackComp D A a b =
      smallEtaleSheafPullbackComp' A (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) :=
  rfl

namespace EtaleSheafSystem

variable {A} {D : Iᵒᵖ ⥤ Scheme.{u}} (F : EtaleSheafSystem D A)

/-- The transition map `f_{i'i}⁻¹ℱ_i ⟶ ℱ_{i'}` of a system of sheaves, with its source written as
the inverse image along the transition morphism. -/
def sheafMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtaleSheafPullback A (D.map a)).obj (F.obj j) ⟶ F.obj i :=
  F.map a

/-- **The cocycle condition**, with the comparison of inverse images along the composite
transition named. -/
theorem sheafMap_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (smallEtaleSheafPullback A (D.map a)).map (F.sheafMap b) ≫ F.sheafMap a =
      (App A (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) (F.obj k)).hom ≫
        F.sheafMap (a ≫ b) := by
  have h := F.map_comp a b
  rw [systemPullbackComp_eq_smallEtaleSheafPullbackComp'] at h
  change _ = (App A (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) (F.obj k)).hom ≫ F.map _
  rw [← h]
  simp only [smallEtaleSheafPullbackCompApp, Iso.app_hom, Iso.hom_inv_id_app_assoc]
  rfl

/-- The cocycle condition `sheafMap_comp` after applying a functor. -/
private theorem map_sheafMap_comp {i j k : Iᵒᵖ} {B : Type*} [Category B]
    (G : Sheaf (smallEtaleTopology (D.obj i)) A ⥤ B) (a : i ⟶ j) (b : j ⟶ k) :
    G.map ((smallEtaleSheafPullback A (D.map a)).map (F.sheafMap b)) ≫ G.map (F.sheafMap a) =
      G.map (App A (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) (F.obj k)).hom ≫
        G.map (F.sheafMap (a ≫ b)) := by
  rw [← Functor.map_comp, F.sheafMap_comp, Functor.map_comp]

variable (c : Cone D)

/-- The map `f_{i'}⁻¹ℱ_{i'} ⟶ f_i⁻¹ℱ_i` of the diagram of inverse images to the vertex of a cone,
for `a : i ⟶ i'` in `Iᵒᵖ`: the comparison `f_{i'}⁻¹ ≅ f_i⁻¹f_{i'i}⁻¹` followed by
`f_i⁻¹φ_{i'i}`. -/
def sheafPullbackDiagramMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtaleSheafPullback A (X := c.pt) (c.π.app j)).obj (F.obj j) ⟶
      (smallEtaleSheafPullback A (X := c.pt) (c.π.app i)).obj (F.obj i) :=
  (App A (X := c.pt) (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm (F.obj j)).inv ≫
    (smallEtaleSheafPullback A (X := c.pt) (c.π.app i)).map (F.sheafMap a)

/-- The maps of the diagram of inverse images in adjoint form. -/
lemma sheafPullbackDiagramMap_eq {i j : Iᵒᵖ} (a : i ⟶ j) :
    F.sheafPullbackDiagramMap c (i := i) (j := j) a =
      ((smallEtaleSheafAdjunction A (X := c.pt) (c.π.app j)).homEquiv _ _).symm
        (F.transition a ≫ (systemPushforward D A a).map
          ((smallEtaleSheafAdjunction A (X := c.pt) (c.π.app i)).unit.app (F.obj i)) ≫
            (smallEtalePushforwardComp' (X := c.pt) (c.π.app i) (D.map a) (c.π.app j)
              (c.w a).symm A).hom.app _) := by
  have h := leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D A a)
    (smallEtaleSheafAdjunction A (X := c.pt) (c.π.app i))
    (smallEtaleSheafAdjunction A (X := c.pt) (c.π.app j))
    (smallEtalePushforwardComp' (X := c.pt) (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm A)
    (F.transition a)
    ((smallEtaleSheafAdjunction A (X := c.pt) (c.π.app i)).unit.app (F.obj i))
  rw [← h, ← EtaleSheafSystem.map_eq_transition]
  simp only [Adjunction.homEquiv_counit, Adjunction.left_triangle_components, Category.comp_id]
  rfl

/-- **The maps of the diagram of inverse images compose**: the cocycle condition of the system,
transported to the vertex through the comparisons of inverse images along the projections. -/
theorem sheafPullbackDiagramMap_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    F.sheafPullbackDiagramMap c (i := i) (j := k) (a ≫ b) =
      F.sheafPullbackDiagramMap c (i := j) (j := k) b ≫
        F.sheafPullbackDiagramMap c (i := i) (j := j) a := by
  have hpent := smallEtaleSheafPullbackCompApp_assoc A (T := c.pt) (c.π.app i) (D.map a) (D.map b)
    (c.π.app j) (c.w a).symm (D.map (a ≫ b)) (D.map_comp a b) (c.π.app k) (c.w b).symm
    (c.w (a ≫ b)).symm (F.obj k)
  have hpent' : (App A (X := c.pt) (c.π.app j) (D.map b) (c.π.app k) (c.w b).symm (F.obj k)).inv ≫
      (App A (X := c.pt) (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm
        ((smallEtaleSheafPullback A (D.map b)).obj (F.obj k))).inv ≫
      (smallEtaleSheafPullback A (X := c.pt) (c.π.app i)).map
        (App A (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) (F.obj k)).hom =
      (App A (X := c.pt) (c.π.app i) (D.map (a ≫ b)) (c.π.app k) (c.w (a ≫ b)).symm
        (F.obj k)).inv := by
    rw [← cancel_mono
      (App A (X := c.pt) (c.π.app i) (D.map (a ≫ b)) (c.π.app k) (c.w (a ≫ b)).symm (F.obj k)).hom]
    simp only [Category.assoc, Iso.inv_hom_id]
    rw [← hpent, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  simp only [sheafPullbackDiagramMap, Category.assoc]
  rw [reassoc_of% (smallEtaleSheafPullbackCompApp_inv_naturality A (X := c.pt) (c.π.app i) (D.map a)
    (c.π.app j) (c.w a).symm (F.sheafMap b)),
    F.map_sheafMap_comp (smallEtaleSheafPullback A (X := c.pt) (c.π.app i)) a b,
    ← reassoc_of% hpent']

/-- The compatibility of a family of maps `ι_i : f_i⁻¹ℱ_i ⟶ ℱ` with the maps of the diagram of
inverse images. -/
abbrev IsSheafPullbackCocone {𝓕 : Sheaf (smallEtaleTopology c.pt) A}
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback A (X := c.pt) (c.π.app i)).obj (F.obj i) ⟶ 𝓕) : Prop :=
  ∀ {i j : Iᵒᵖ} (a : i ⟶ j), F.sheafPullbackDiagramMap c (i := i) (j := j) a ≫ ι i = ι j

/-- **The colimit presentation `𝓕 = colim f_i⁻¹ℱ_i`** of a sheaf on the vertex of a cone, for a
system of sheaves `F` and a family `ι_i : f_i⁻¹ℱ_i ⟶ 𝓕`: every family of maps out of the inverse
images compatible with the maps of the diagram factors uniquely through the `ι_i`. -/
abbrev IsSheafPullbackColimitPresentation (𝓕 : Sheaf (smallEtaleTopology c.pt) A)
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback A (X := c.pt) (c.π.app i)).obj (F.obj i) ⟶ 𝓕) : Prop :=
  IsSystemColimit (fun i => (smallEtaleSheafPullback A (X := c.pt) (c.π.app i)).obj (F.obj i))
    (fun {i j} a => F.sheafPullbackDiagramMap c (i := i) (j := j) a) 𝓕 ι

end EtaleSheafSystem

/-! ### The inverse image of a system along a morphism of inverse systems -/

section MorphismOfSystems

variable {A} {DY DT : Iᵒᵖ ⥤ Scheme.{u}} (e : DY ⟶ DT)

/-- **The comparisons attached to a morphism of inverse systems compose.** Along `i'' ≥ i' ≥ i`,
the comparison `f_{i''i}⁻¹e_i⁻¹ ≅ e_{i''}⁻¹g_{i''i}⁻¹` through the diagonal of the composite
naturality square is the composite of the comparisons of the two naturality squares, read through
the comparisons of inverse images along the two composite transitions. -/
theorem smallEtaleSheafPullbackCompApp_naturality_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    (M : Sheaf (smallEtaleTopology (DT.obj k)) A) :
    (App A (DY.map a) (DY.map b) (DY.map (a ≫ b)) (DY.map_comp a b)
          ((smallEtaleSheafPullback A (e.app k)).obj M)).inv ≫
        (smallEtaleSheafPullback A (DY.map a)).map
          (App A (DY.map b) (e.app k) (DY.map b ≫ e.app k) rfl M).hom ≫
        (smallEtaleSheafPullback A (DY.map a)).map
          (App A (e.app j) (DT.map b) (DY.map b ≫ e.app k) (e.naturality b) M).inv ≫
        (App A (DY.map a) (e.app j) (DY.map a ≫ e.app j) rfl
          ((smallEtaleSheafPullback A (DT.map b)).obj M)).hom ≫
        (App A (e.app i) (DT.map a) (DY.map a ≫ e.app j) (e.naturality a)
          ((smallEtaleSheafPullback A (DT.map b)).obj M)).inv ≫
        (smallEtaleSheafPullback A (e.app i)).map
          (App A (DT.map a) (DT.map b) (DT.map (a ≫ b)) (DT.map_comp a b) M).hom =
      (App A (DY.map (a ≫ b)) (e.app k) (DY.map (a ≫ b) ≫ e.app k) rfl M).hom ≫
        (App A (e.app i) (DT.map (a ≫ b)) (DY.map (a ≫ b) ≫ e.app k) (e.naturality (a ≫ b))
          M).inv := by
  have h₁ : DY.map (a ≫ b) ≫ e.app k = (DY.map a ≫ e.app j) ≫ DT.map b := by
    simp only [Functor.map_comp, Category.assoc, e.naturality b]
  have h₃ : DY.map (a ≫ b) ≫ e.app k = DY.map a ≫ (DY.map b ≫ e.app k) := by
    rw [DY.map_comp, Category.assoc]
  have A₁ := smallEtaleSheafPullbackCompApp_assoc A (e.app i) (DT.map a) (DT.map b)
    (DY.map a ≫ e.app j) (e.naturality a) (DT.map (a ≫ b)) (DT.map_comp a b)
    (DY.map (a ≫ b) ≫ e.app k) h₁ (e.naturality (a ≫ b)) M
  have A₂ := smallEtaleSheafPullbackCompApp_assoc A (DY.map a) (e.app j) (DT.map b)
    (DY.map a ≫ e.app j) rfl (DY.map b ≫ e.app k) (e.naturality b) (DY.map (a ≫ b) ≫ e.app k)
    h₁ h₃ M
  have A₃ := smallEtaleSheafPullbackCompApp_assoc A (DY.map a) (DY.map b) (e.app k)
    (DY.map (a ≫ b)) (DY.map_comp a b) (DY.map b ≫ e.app k) rfl (DY.map (a ≫ b) ≫ e.app k) rfl
    h₃ M
  rw [← cancel_mono (App A (e.app i) (DT.map (a ≫ b)) (DY.map (a ≫ b) ≫ e.app k)
    (e.naturality (a ≫ b)) M).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← A₁, Iso.inv_hom_id_assoc, A₂, Iso.map_inv_hom_id_assoc, ← A₃, Iso.inv_hom_id_assoc]

variable (F : EtaleSheafSystem DT A)

/-- The transition map `f_{i'i}⁻¹e_i⁻¹ℱ_i ⟶ e_{i'}⁻¹ℱ_{i'}` of the inverse image of a system of
sheaves along a morphism of inverse systems: the comparison `f_{i'i}⁻¹e_i⁻¹ ≅ e_{i'}⁻¹g_{i'i}⁻¹`
through the diagonal of the naturality square, followed by `e_{i'}⁻¹φ_{i'i}`. -/
def EtaleSheafSystem.sheafPullbackMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtaleSheafPullback A (DY.map a)).obj
        ((smallEtaleSheafPullback A (e.app j)).obj (F.obj j)) ⟶
      (smallEtaleSheafPullback A (e.app i)).obj (F.obj i) :=
  (App A (DY.map a) (e.app j) (DY.map a ≫ e.app j) rfl (F.obj j)).hom ≫
    (App A (e.app i) (DT.map a) (DY.map a ≫ e.app j) (e.naturality a) (F.obj j)).inv ≫
    (smallEtaleSheafPullback A (e.app i)).map (F.sheafMap a)

/-- **The cocycle condition for the inverse image of a system along a morphism of systems.** -/
theorem EtaleSheafSystem.sheafPullbackMap_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (App A (DY.map a) (DY.map b) (DY.map (a ≫ b)) (DY.map_comp a b)
          ((smallEtaleSheafPullback A (e.app k)).obj (F.obj k))).inv ≫
        (smallEtaleSheafPullback A (DY.map a)).map (F.sheafPullbackMap e b) ≫
          F.sheafPullbackMap e a =
      F.sheafPullbackMap e (a ≫ b) := by
  simp only [EtaleSheafSystem.sheafPullbackMap, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (smallEtaleSheafPullbackCompApp_hom_naturality A (DY.map a) (e.app j)
      (DY.map a ≫ e.app j) rfl (F.sheafMap b)),
    reassoc_of% (smallEtaleSheafPullbackCompApp_inv_naturality A (e.app i) (DT.map a)
      (DY.map a ≫ e.app j) (e.naturality a) (F.sheafMap b)),
    F.map_sheafMap_comp (smallEtaleSheafPullback A (e.app i)) a b,
    reassoc_of% (smallEtaleSheafPullbackCompApp_naturality_comp e a b (F.obj k))]

/-- **The inverse image of a system of sheaves along a morphism of inverse systems of schemes.**
For a morphism `e : (Y_i) ⟶ (T_i)` of inverse systems and a system `(ℱ_i, φ_{i'i})` on `(T_i)`,
the sheaves `e_i⁻¹ℱ_i` form a system on `(Y_i)`, with transition maps
`Stacks.EtaleCohomology.EtaleSheafSystem.sheafPullbackMap`. -/
abbrev EtaleSheafSystem.sheafPullback : EtaleSheafSystem DY A where
  obj i := (smallEtaleSheafPullback A (e.app i)).obj (F.obj i)
  map a := F.sheafPullbackMap e a
  map_comp a b := by
    rw [systemPullbackComp_eq_smallEtaleSheafPullbackComp']
    exact F.sheafPullbackMap_comp e a b

variable {cY : Cone DY} {cT : Cone DT} (eL : cY.pt ⟶ cT.pt)
  (heL : ∀ i, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)

/-- The legs `q_i⁻¹e_i⁻¹ℱ_i ⟶ e⁻¹ℱ` of the inverse image along `e : Y ⟶ T` of a family
`ι_i : p_i⁻¹ℱ_i ⟶ ℱ`: the comparison `q_i⁻¹e_i⁻¹ ≅ e⁻¹p_i⁻¹` through the diagonal of the
projection square `e ≫ p_i = q_i ≫ e_i`, followed by `e⁻¹ι_i`. -/
def EtaleSheafSystem.sheafPullbackLeg {𝓕 : Sheaf (smallEtaleTopology cT.pt) A}
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback A (X := cT.pt) (cT.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (i : Iᵒᵖ) :
    (smallEtaleSheafPullback A (X := cY.pt) (cY.π.app i)).obj
        ((smallEtaleSheafPullback A (e.app i)).obj (F.obj i)) ⟶
      (smallEtaleSheafPullback A eL).obj 𝓕 :=
  (App A (X := cY.pt) (cY.π.app i) (e.app i) (cY.π.app i ≫ e.app i) rfl (F.obj i)).hom ≫
    (App A eL (cT.π.app i) (cY.π.app i ≫ e.app i) (heL i).symm (F.obj i)).inv ≫
    (smallEtaleSheafPullback A eL).map (ι i)

/-- The comparison `e⁻¹p_i⁻¹ℱ_i ≅ q_i⁻¹e_i⁻¹ℱ_i` of the projection square. -/
def EtaleSheafSystem.sheafPullbackLegComparison (i : Iᵒᵖ) :
    (smallEtaleSheafPullback A eL).obj
        ((smallEtaleSheafPullback A (X := cT.pt) (cT.π.app i)).obj (F.obj i)) ≅
      (smallEtaleSheafPullback A (X := cY.pt) (cY.π.app i)).obj
        ((smallEtaleSheafPullback A (e.app i)).obj (F.obj i)) :=
  App A eL (cT.π.app i) (cY.π.app i ≫ e.app i) (heL i).symm (F.obj i) ≪≫
    (App A (X := cY.pt) (cY.π.app i) (e.app i) (cY.π.app i ≫ e.app i) rfl (F.obj i)).symm

/-- The comparison of the projection square followed by the leg is the inverse image of the leg
of the family on `T`. -/
theorem EtaleSheafSystem.sheafPullbackLegComparison_hom_comp_sheafPullbackLeg
    {𝓕 : Sheaf (smallEtaleTopology cT.pt) A}
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback A (X := cT.pt) (cT.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (i : Iᵒᵖ) :
    (F.sheafPullbackLegComparison e eL heL i).hom ≫ F.sheafPullbackLeg e eL heL ι i =
      (smallEtaleSheafPullback A eL).map (ι i) := by
  simp only [EtaleSheafSystem.sheafPullbackLegComparison, EtaleSheafSystem.sheafPullbackLeg,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- The identification of the comparisons of inverse images in the correspondence of the
diagrams. -/
private theorem sheafPullbackDiagram_comparison {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtaleSheafPullback A eL).map
        (App A (X := cT.pt) (cT.π.app i) (DT.map a) (cT.π.app j) (cT.w a).symm (F.obj j)).inv ≫
      (App A eL (cT.π.app i) (cY.π.app i ≫ e.app i) (heL i).symm
        ((smallEtaleSheafPullback A (DT.map a)).obj (F.obj j))).hom ≫
      (App A (X := cY.pt) (cY.π.app i) (e.app i) (cY.π.app i ≫ e.app i) rfl
        ((smallEtaleSheafPullback A (DT.map a)).obj (F.obj j))).inv =
    (App A eL (cT.π.app j) (cY.π.app j ≫ e.app j) (heL j).symm (F.obj j)).hom ≫
      (App A (X := cY.pt) (cY.π.app j) (e.app j) (cY.π.app j ≫ e.app j) rfl (F.obj j)).inv ≫
      (App A (X := cY.pt) (cY.π.app i) (DY.map a) (cY.π.app j) (cY.w a).symm
          ((smallEtaleSheafPullback A (e.app j)).obj (F.obj j))).inv ≫
      (smallEtaleSheafPullback A (X := cY.pt) (cY.π.app i)).map
        (App A (DY.map a) (e.app j) (DY.map a ≫ e.app j) rfl (F.obj j)).hom ≫
      (smallEtaleSheafPullback A (X := cY.pt) (cY.π.app i)).map
        (App A (e.app i) (DT.map a) (DY.map a ≫ e.app j) (e.naturality a) (F.obj j)).inv := by
  have hnat : DY.map a ≫ e.app j = e.app i ≫ DT.map a := e.naturality a
  have hW₁ : cY.π.app j ≫ e.app j = (cY.π.app i ≫ e.app i) ≫ DT.map a := by
    rw [Category.assoc, ← hnat, ← Category.assoc, cY.w a]
  have hW₂ : cY.π.app j ≫ e.app j = cY.π.app i ≫ (DY.map a ≫ e.app j) := by
    rw [← Category.assoc, cY.w a]
  have hW₃ : cY.π.app j ≫ e.app j = eL ≫ cT.π.app j := (heL j).symm
  have A₁ := smallEtaleSheafPullbackCompApp_assoc A (T := cY.pt) (cY.π.app i) (e.app i) (DT.map a)
    (cY.π.app i ≫ e.app i) rfl (DY.map a ≫ e.app j) hnat (cY.π.app j ≫ e.app j) hW₁ hW₂ (F.obj j)
  have A₂ := smallEtaleSheafPullbackCompApp_assoc A eL (cT.π.app i) (DT.map a)
    (cY.π.app i ≫ e.app i) (heL i).symm (cT.π.app j) (cT.w a).symm (cY.π.app j ≫ e.app j) hW₁
    hW₃ (F.obj j)
  have A₃ := smallEtaleSheafPullbackCompApp_assoc A (T := cY.pt) (cY.π.app i) (DY.map a) (e.app j)
    (cY.π.app j) (cY.w a).symm (DY.map a ≫ e.app j) rfl (cY.π.app j ≫ e.app j) rfl hW₂ (F.obj j)
  rw [← cancel_mono ((smallEtaleSheafPullback A (X := cY.pt) (cY.π.app i)).map
      (App A (e.app i) (DT.map a) (DY.map a ≫ e.app j) hnat (F.obj j)).hom ≫
    (App A (X := cY.pt) (cY.π.app i) (DY.map a ≫ e.app j) (cY.π.app j ≫ e.app j) hW₂
      (F.obj j)).hom)]
  simp only [Category.assoc]
  rw [Iso.map_inv_hom_id_assoc, ← A₁, Iso.inv_hom_id_assoc, A₂, Iso.map_inv_hom_id_assoc, ← A₃,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The maps of the two diagrams correspond.** The inverse image along `e` of the maps of the
diagram `p_i⁻¹ℱ_i` are the maps of the diagram `q_i⁻¹e_i⁻¹ℱ_i` of the inverse image system,
under the comparisons of the projection squares. -/
theorem EtaleSheafSystem.map_sheafPullbackDiagramMap_comp {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtaleSheafPullback A eL).map (F.sheafPullbackDiagramMap cT (i := i) (j := j) a) ≫
        (F.sheafPullbackLegComparison e eL heL i).hom =
      (F.sheafPullbackLegComparison e eL heL j).hom ≫
        (F.sheafPullback e).sheafPullbackDiagramMap cY (i := i) (j := j) a := by
  have nE := smallEtaleSheafPullbackCompApp_hom_naturality A eL (cT.π.app i)
    (cY.π.app i ≫ e.app i) (heL i).symm (F.sheafMap a)
  have nQ := smallEtaleSheafPullbackCompApp_inv_naturality A (X := cY.pt) (cY.π.app i) (e.app i)
    (cY.π.app i ≫ e.app i) rfl (F.sheafMap a)
  have hM : (smallEtaleSheafPullback A (X := cY.pt) (cY.π.app i)).map
        ((F.sheafPullback e).sheafMap a) =
      (smallEtaleSheafPullback A (X := cY.pt) (cY.π.app i)).map
          (App A (DY.map a) (e.app j) (DY.map a ≫ e.app j) rfl (F.obj j)).hom ≫
        (smallEtaleSheafPullback A (X := cY.pt) (cY.π.app i)).map
          (App A (e.app i) (DT.map a) (DY.map a ≫ e.app j) (e.naturality a) (F.obj j)).inv ≫
        (smallEtaleSheafPullback A (X := cY.pt) (cY.π.app i)).map
          ((smallEtaleSheafPullback A (e.app i)).map (F.sheafMap a)) := by
    change (smallEtaleSheafPullback A (X := cY.pt) (cY.π.app i)).map (F.sheafPullbackMap e a) = _
    simp only [EtaleSheafSystem.sheafPullbackMap, Functor.map_comp]
  rw [EtaleSheafSystem.sheafPullbackDiagramMap, EtaleSheafSystem.sheafPullbackDiagramMap, hM]
  simp only [EtaleSheafSystem.sheafPullbackLegComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% nE, nQ, ← reassoc_of% (sheafPullbackDiagram_comparison e F eL heL a)]

/-- **The inverse image of a colimit presentation is compatible with the maps of the diagram.** -/
theorem EtaleSheafSystem.isSheafPullbackCocone_sheafPullback
    {𝓕 : Sheaf (smallEtaleTopology cT.pt) A}
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback A (X := cT.pt) (cT.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : F.IsSheafPullbackCocone cT ι) :
    (F.sheafPullback e).IsSheafPullbackCocone cY (F.sheafPullbackLeg e eL heL ι) := by
  intro i j a
  rw [← cancel_epi (F.sheafPullbackLegComparison e eL heL j).hom,
    ← reassoc_of% (F.map_sheafPullbackDiagramMap_comp e eL heL a),
    F.sheafPullbackLegComparison_hom_comp_sheafPullbackLeg,
    F.sheafPullbackLegComparison_hom_comp_sheafPullbackLeg, ← Functor.map_comp, hι a]

/-- **The inverse image of a colimit presentation is a colimit presentation**: inverse image is a
left adjoint, so it preserves the colimit `ℱ = colim p_i⁻¹ℱ_i`, and the comparisons of the
projection squares identify the two diagrams. -/
theorem EtaleSheafSystem.isSheafPullbackColimitPresentation_sheafPullback
    {𝓕 : Sheaf (smallEtaleTopology cT.pt) A}
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback A (X := cT.pt) (cT.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hpres : F.IsSheafPullbackColimitPresentation cT 𝓕 ι) :
    (F.sheafPullback e).IsSheafPullbackColimitPresentation cY
      ((smallEtaleSheafPullback A eL).obj 𝓕) (F.sheafPullbackLeg e eL heL ι) :=
  (hpres.map_of_isLeftAdjoint (smallEtaleSheafAdjunction A eL)).of_isoSystem
    (fun i => F.sheafPullbackLegComparison e eL heL i) (Iso.refl _)
    (fun {i j} a => F.map_sheafPullbackDiagramMap_comp e eL heL (i := i) (j := j) a)
    (fun i => (Category.comp_id _).trans
      (F.sheafPullbackLegComparison_hom_comp_sheafPullbackLeg e eL heL ι i).symm)

end MorphismOfSystems


end Stacks.EtaleCohomology

end
