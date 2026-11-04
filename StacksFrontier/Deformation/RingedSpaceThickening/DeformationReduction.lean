module

public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationLift
public import StacksFrontier.Deformation.RingedSpaceThickening.IdealMapSections
public import StacksFrontier.Deformation.ToposThickening.FirstOrderLiftDiagram
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep
import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionObstruction

/-!
# Stacks 08U8: reduction to one site

Let `D` be the diagram of the four ideal rows of **Stacks 08UA** attached to a commutative cube
of ringed spaces of **Stacks 08U9** whose horizontal arrows are first order thickenings. The
proof of **Stacks 08U8** begins by pulling everything back to `X₂`: the front layer is pulled
back along `g`, the thickened spaces are identified with the reduced ones through their
homeomorphisms, and the morphisms `X'₂ ⟶ X'₁` fitting into the cube compatibly with `ν` become
the homomorphisms `g⁻¹𝒪_{X'₁} ⟶ 𝒪_{X'₂}` fitting into a diagram of sheaves of rings on `X₂`.
This file constructs that diagram,
`AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.toFirstOrderLiftDiagram`, a
`Deformation.ToposThickening.FirstOrderLiftDiagram` on the site of opens of `X₂`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.frontLayer` and
  `backLayer`: the two layers of the cube, on `X₁` and on `X₂`.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationIdealDiagram.toFirstOrderLiftDiagram`:
  **the source's reduced diagram on `X₂`**: the front layer pulled back along `g`, the back
  layer, the comparisons `g`, `gB`, `gB'` induced by the cube, and the comparison `ν` of the
  ideal modules induced by the `g`-map `ν` of the diagram.

## Main results

* `toFirstOrderLiftDiagram_front_O`, `toFirstOrderLiftDiagram_front_OB`,
  `toFirstOrderLiftDiagram_front_f`, `toFirstOrderLiftDiagram_back_O`,
  `toFirstOrderLiftDiagram_g`, `toFirstOrderLiftDiagram_back_G`: the reduced diagram is built
  on `g⁻¹𝒪_{X₁}`, `g⁻¹f₁⁻¹𝒪_{S₁}`, `𝒪_{X₂}`, with the structure maps of the source, and its back
  ideal module is `𝒢₂`.

## Implementation notes

Every comparison morphism between inverse images is defined as an iterated adjoint transpose of
a morphism between direct images, which is a comorphism read on sections. Identities between
such morphisms are proved by transposing back, and identities between sections of inverse
images by `Deformation.ToposThickening.LiftSquare.inverseImage`'s local description: a section
of an inverse image is near every point an induced section.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08U9](https://stacks.math.columbia.edu/tag/08U9)
* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Deformation.ToposThickening
open AlgebraicGeometry.SheafOfModules (inverseImageModule inverseImageModuleUnit
  inverseImageRingHom inverseImageAdjunction)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

section PushEq

variable {A B : TopCat.{u}} {p q : A ⟶ B} (h : p = q)
  (F : Sheaf (Opens.grothendieckTopology A) CommRingCat.{u})

/-- The transport of a direct image of sheaves of commutative rings along an equality of
continuous maps. -/
def pushEq : (ringPushforward p).obj F ⟶ (ringPushforward q).obj F :=
  ObjectProperty.homMk (TopCat.Presheaf.pushforwardEq h F.obj).hom

/-- The transport along an equality of continuous maps is a restriction on sections. -/
theorem pushEq_apply (V : Opens B) (hle : (Opens.map q).obj V ≤ (Opens.map p).obj V)
    (x : F.obj.obj (op ((Opens.map p).obj V))) :
    (pushEq h F).hom.app (op V) x = F.obj.map (homOfLE hle).op x := by
  subst h
  rfl

end PushEq

section Comorphisms

variable {X S : RingedSpace.{u, u}} (f : X ⟶ S)

/-- The structure map of a morphism of ringed spaces on induced sections is its comorphism. -/
theorem structureMap_ringUnit (V : Opens S.carrier) (x : S.presheaf.obj (op V)) :
    (structureMap f).hom.app (op ((Opens.map f.hom.base).obj V))
        (ringUnit f.hom.base (ringOf S) V x) = f.hom.c.app (op V) x :=
  ringAdjunction_homEquiv_symm_ringUnit f.hom.base (ringOf S) (comorphism f) V x

/-- `comp_c_congr` with no restriction on the left. -/
theorem comp_c_congr' {A B B' C : RingedSpace.{u, u}} {α : A ⟶ B} {β : B ⟶ C} {γ : A ⟶ B'}
    {δ : B' ⟶ C} (h : α ≫ β = γ ≫ δ) (W : Opens C.carrier)
    (g₂ : op ((Opens.map γ.hom.base).obj ((Opens.map δ.hom.base).obj W)) ⟶
      op ((Opens.map α.hom.base).obj ((Opens.map β.hom.base).obj W)))
    (a : C.presheaf.obj (op W)) :
    A.presheaf.map g₂ (γ.hom.c.app _ (δ.hom.c.app (op W) a)) =
      α.hom.c.app _ (β.hom.c.app (op W) a) := by
  refine (comp_c_congr h W (𝟙 _) g₂ a).symm.trans ?_
  rw [A.presheaf.map_id]
  rfl

end Comorphisms

section SolutionStructure

variable {X X' S S' : RingedSpace.{u, u}} (i : X ⟶ X') (t : S ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S')
  (comm : i ≫ f' = f ≫ t) (hi : IsThickening i) (ht : IsThickening t)
  (G : SheafOfModules.{u} (structureSheafRing X))
  (κ : AlgebraicGeometry.SheafOfModules.idealSheaf i ≅ (modulePushforward i).obj G)
  (c : (modulePullback f).obj ((modulePullback t).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G)

/-- The inclusion of the ideal of a morphism of ringed spaces commutes with restriction. -/
theorem idealι_naturality {W W' : Opens X'.carrier} (h : W' ≤ W)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj (op W)) :
    idealι i W' (mres _ h j) = X'.presheaf.map (homOfLE h).op (idealι i W j) :=
  PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))).val (homOfLE h).op j

/-- The opens of `X` over which the structure map of a solution is compared with `c`. -/
theorem solution_le (V : Opens S.carrier) :
    (Opens.map i.hom.base).obj ((Opens.map (thickeningHomeo i hi).inv).obj
        ((Opens.map f.hom.base).obj V)) ≤
      (Opens.map f.hom.base).obj ((Opens.map t.hom.base).obj
        ((Opens.map (thickeningHomeo t ht).inv).obj V)) := by
  intro x hx
  change (thickeningHomeo t ht).inv (t.hom.base (f.hom.base x)) ∈ V
  rw [thickeningHomeo_hom_inv_apply]
  change f.hom.base ((thickeningHomeo i hi).inv (i.hom.base x)) ∈ V at hx
  rwa [thickeningHomeo_hom_inv_apply] at hx

include comm in
/-- **The structure map of a solution on its base ideal**: if `f'^♯` carries every section `j` of
the ideal of `t` to the section of `𝒪_{X'}` corresponding to `c(j)`, then so does the structure
map of the layer, read on the reduced spaces. -/
theorem thickeningStructure_idealι
    (hsol : ∀ (W : Opens S'.carrier) (j : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj
        (op W)), f'.hom.c.app (op W) (idealι t W j) =
      layerIdealIncl i G κ ((Opens.map f'.hom.base).obj W)
        (mres G (fun x hx => by
          change t.hom.base (f.hom.base x) ∈ W
          rw [← thickening_comm_apply i t f f' comm x]
          exact hx) ((doubleTranspose f t c).val.app (op W) j)))
    (V : Opens S.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj
      (op ((Opens.map (thickeningHomeo t ht).inv).obj V))) :
    (thickeningStructure i t f f' comm hi ht).hom.app (op V) (idealι t _ j) =
      layerIdealIncl i G κ
          ((Opens.map (thickeningHomeo i hi).inv).obj ((Opens.map f.hom.base).obj V))
        (mres G (solution_le i t f hi ht V)
          ((doubleTranspose f t c).val.app (op ((Opens.map (thickeningHomeo t ht).inv).obj V))
            j)) := by
  refine (thickeningStructure_apply i t f f' comm hi ht V _).trans ?_
  refine (congrArg (fun x => X'.presheaf.map _ x) (hsol _ j)).trans ?_
  refine (layerIdealIncl_naturality i G κ
    (thickening_structure_le i t f f' comm hi ht V) _).symm.trans ?_
  exact congrArg (layerIdealIncl i G κ _) (mres_mres G _ _ _)

/-- A section of `k_*𝒪_{S'}` killed by the reduction of a first order thickening `t` is a
section of the ideal of `t`. -/
theorem exists_idealι_of_reduction (V : Opens S.carrier)
    (σ : (thickenedRing t ht).obj.obj (op V))
    (hσ : (thickeningReduction t ht).hom.app (op V) σ = 0) :
    ∃ j : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj
        (op ((Opens.map (thickeningHomeo t ht).inv).obj V)), idealι t _ j = σ := by
  have hU := thickening_preimage_preimage t ht V
  have ha : t.hom.c.app (op ((Opens.map (thickeningHomeo t ht).inv).obj V)) σ = 0 :=
    presheaf_map_homOfLE_injective S.presheaf hU.ge hU.le (by rw [map_zero]; exact hσ)
  exact exists_kernel_section
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom t)) _ σ ha

end SolutionStructure

/-- A morphism of sheaves of rings carries equal restrictions to equal restrictions. -/
private theorem sheafHom_map_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J CommRingCat.{u}} (φ : F ⟶ G) {U V W : Cᵒᵖ} (h₁ : U ⟶ W) (h₂ : V ⟶ W)
    {a : F.obj.obj U} {b : F.obj.obj V} (e : F.obj.map h₁ a = F.obj.map h₂ b) :
    G.obj.map h₁ (φ.hom.app U a) = G.obj.map h₂ (φ.hom.app V b) := by
  rw [← sheafHom_naturality_apply, e, sheafHom_naturality_apply]

/-- If a section of `p⁻¹T` killed by `p⁻¹` of a morphism `red` is locally the unit image of a
section `σ` of `T`, then `red σ` vanishes near the image point. -/
private theorem exists_reduction_eq_zero_of_ringUnit {X Y : TopCat.{u}} (p : Y ⟶ X)
    {T S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (red : T ⟶ S) {U : Opens Y}
    (a : ((ringPullback p).obj T).obj.obj (op U))
    (ha : ((ringPullback p).map red).hom.app (op U) a = 0) {V : Opens X}
    (σ : T.obj.obj (op V)) {W : Opens Y} (hWU : W ≤ U) (hWV : W ≤ (Opens.map p).obj V)
    (e : ((ringPullback p).obj T).obj.map (homOfLE hWU).op a =
      ((ringPullback p).obj T).obj.map (homOfLE hWV).op (ringUnit p T V σ))
    (y : Y) (hy : y ∈ W) :
    ∃ (V' : Opens X) (_ : p y ∈ V') (hV' : V' ≤ V),
      red.hom.app (op V') (T.obj.map (homOfLE hV').op σ) = 0 := by
  have e0 : ((ringPullback p).obj S).obj.map (homOfLE hWV).op
      (ringUnit p S V (red.hom.app (op V) σ)) =
      ((ringPullback p).obj S).obj.map (homOfLE hWV).op (ringUnit p S V 0) := by
    rw [← ringUnit_naturality, ← sheafHom_naturality_apply, ← e, sheafHom_naturality_apply, ha,
      map_zero, map_zero, map_zero]
  obtain ⟨V', hV', hle, e1⟩ := exists_restrict_eq_of_ringUnit_eq p S _ _ y hy hWV e0
  rw [map_zero, ← sheafHom_naturality_apply] at e1
  exact ⟨V', hV', hle, e1⟩

namespace DeformationIdealDiagram

variable (D : DeformationIdealDiagram.{u})

/-- The front layer of the cube, on `X₁`. -/
abbrev frontLayer : LiftSquare.{u, u, u} (Opens.grothendieckTopology D.cube.X₁.carrier) :=
  thickeningLayer D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm D.i₁_firstOrder
    D.t₁_firstOrder D.G₁ D.kernelIso₁

/-- The back layer of the cube, on `X₂`. -/
abbrev backLayer : LiftSquare.{u, u, u} (Opens.grothendieckTopology D.cube.X₂.carrier) :=
  thickeningLayer D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm D.i₂_firstOrder
    D.t₂_firstOrder D.G₂ D.kernelIso₂

/-- The square of reduced spaces of the cube, on the underlying continuous maps. -/
theorem source_comm_base :
    D.cube.f₂.hom.base ≫ D.cube.h.hom.base = D.cube.g.hom.base ≫ D.cube.f₁.hom.base :=
  congrArg (fun k => k.hom.base) D.cube.source_comm.symm

/-- The comparison `gB` before transposition: the comorphism of `h` followed by the unit of
`f₂⁻¹ ⊣ f₂_*`, a morphism `𝒪_{S₁} ⟶ f₁_*g_*f₂⁻¹𝒪_{S₂}`. -/
def gBTranspose : ringOf D.cube.S₁ ⟶ (ringPushforward D.cube.f₁.hom.base).obj
    ((ringPushforward D.cube.g.hom.base).obj
      ((ringPullback D.cube.f₂.hom.base).obj (ringOf D.cube.S₂))) :=
  comorphism D.cube.h ≫
    (ringPushforward D.cube.h.hom.base).map
      ((ringAdjunction D.cube.f₂.hom.base).unit.app (ringOf D.cube.S₂)) ≫
    pushEq D.source_comm_base _

/-- **The comparison `g⁻¹f₁⁻¹𝒪_{S₁} ⟶ f₂⁻¹𝒪_{S₂}` of the reduced bases.** -/
def gB : (ringPullback D.cube.g.hom.base).obj
      ((ringPullback D.cube.f₁.hom.base).obj (ringOf D.cube.S₁)) ⟶
    (ringPullback D.cube.f₂.hom.base).obj (ringOf D.cube.S₂) :=
  ((ringAdjunction D.cube.g.hom.base).homEquiv _ _).symm
    (((ringAdjunction D.cube.f₁.hom.base).homEquiv _ _).symm D.gBTranspose)

/-- The comparison `gB'` before transposition: the comorphism of `h'` read on the reduced
spaces, followed by the unit of `f₂⁻¹ ⊣ f₂_*`. -/
def gB'Transpose : thickenedRing D.cube.t₁ D.t₁_firstOrder.isThickening ⟶
    (ringPushforward D.cube.f₁.hom.base).obj
      ((ringPushforward D.cube.g.hom.base).obj
        ((ringPullback D.cube.f₂.hom.base).obj
          (thickenedRing D.cube.t₂ D.t₂_firstOrder.isThickening))) :=
  thickeningStructure D.cube.t₂ D.cube.t₁ D.cube.h D.cube.h' D.cube.base_comm.symm
      D.t₂_firstOrder.isThickening D.t₁_firstOrder.isThickening ≫
    (ringPushforward D.cube.h.hom.base).map
      ((ringAdjunction D.cube.f₂.hom.base).unit.app
        (thickenedRing D.cube.t₂ D.t₂_firstOrder.isThickening)) ≫
    pushEq D.source_comm_base _

/-- **The comparison `g⁻¹f₁⁻¹k_*𝒪_{S'₁} ⟶ f₂⁻¹k_*𝒪_{S'₂}` of the thickened bases.** -/
def gB' : (ringPullback D.cube.g.hom.base).obj
      ((ringPullback D.cube.f₁.hom.base).obj
        (thickenedRing D.cube.t₁ D.t₁_firstOrder.isThickening)) ⟶
    (ringPullback D.cube.f₂.hom.base).obj (thickenedRing D.cube.t₂ D.t₂_firstOrder.isThickening) :=
  ((ringAdjunction D.cube.g.hom.base).homEquiv _ _).symm
    (((ringAdjunction D.cube.f₁.hom.base).homEquiv _ _).symm D.gB'Transpose)

/-- The two preimages of an open of `S₁` in `X₂`. -/
theorem source_le (V : Opens D.cube.S₁.carrier) :
    (Opens.map D.cube.g.hom.base).obj ((Opens.map D.cube.f₁.hom.base).obj V) ≤
      (Opens.map D.cube.f₂.hom.base).obj ((Opens.map D.cube.h.hom.base).obj V) := by
  intro x hx
  have e := ConcreteCategory.congr_hom D.source_comm_base x
  change D.cube.h.hom.base (D.cube.f₂.hom.base x) ∈ V
  change D.cube.h.hom.base (D.cube.f₂.hom.base x) = D.cube.f₁.hom.base (D.cube.g.hom.base x) at e
  rw [e]
  exact hx

/-- The comparison `gB` before transposition, on sections. -/
theorem gBTranspose_apply (V : Opens D.cube.S₁.carrier) (σ : D.cube.S₁.presheaf.obj (op V)) :
    D.gBTranspose.hom.app (op V) σ =
      ((ringPullback D.cube.f₂.hom.base).obj (ringOf D.cube.S₂)).obj.map
        (homOfLE (D.source_le V)).op
        (ringUnit D.cube.f₂.hom.base (ringOf D.cube.S₂) ((Opens.map D.cube.h.hom.base).obj V)
          (D.cube.h.hom.c.app (op V) σ)) :=
  pushEq_apply D.source_comm_base _ V (D.source_le V) _

/-- The comparison `gB'` before transposition, on sections. -/
theorem gB'Transpose_apply (V : Opens D.cube.S₁.carrier)
    (σ : (thickenedRing D.cube.t₁ D.t₁_firstOrder.isThickening).obj.obj (op V)) :
    D.gB'Transpose.hom.app (op V) σ =
      ((ringPullback D.cube.f₂.hom.base).obj
          (thickenedRing D.cube.t₂ D.t₂_firstOrder.isThickening)).obj.map
        (homOfLE (D.source_le V)).op
        (ringUnit D.cube.f₂.hom.base (thickenedRing D.cube.t₂ D.t₂_firstOrder.isThickening)
          ((Opens.map D.cube.h.hom.base).obj V)
          ((thickeningStructure D.cube.t₂ D.cube.t₁ D.cube.h D.cube.h' D.cube.base_comm.symm
            D.t₂_firstOrder.isThickening D.t₁_firstOrder.isThickening).hom.app (op V) σ)) :=
  pushEq_apply D.source_comm_base _ V (D.source_le V) _

/-- The comparison of reduced sources lies over the comparison of reduced bases. -/
theorem g_comm : D.gB ≫ structureMap D.cube.f₂ =
    (ringPullback D.cube.g.hom.base).map (structureMap D.cube.f₁) ≫ structureMap D.cube.g := by
  apply ((ringAdjunction D.cube.g.hom.base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left, gB,
    Equiv.apply_symm_apply, homEquiv_structureMap]
  apply ((ringAdjunction D.cube.f₁.hom.base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, homEquiv_structureMap]
  refine sheafHom_ext _ fun V σ => ?_
  obtain ⟨V⟩ := V
  change (structureMap D.cube.f₂).hom.app _ (D.gBTranspose.hom.app (op V) σ) =
    D.cube.g.hom.c.app _ (D.cube.f₁.hom.c.app (op V) σ)
  refine (congrArg (fun x => (structureMap D.cube.f₂).hom.app _ x)
    (D.gBTranspose_apply V σ)).trans ?_
  refine (sheafHom_naturality_apply _ _ _ _).trans ?_
  refine (congrArg (fun x => D.cube.X₂.presheaf.map _ x)
    (structureMap_ringUnit D.cube.f₂ _ _)).trans ?_
  exact comp_c_congr' D.cube.source_comm V _ σ

/-- The square of bases of the reduced diagram commutes. -/
theorem gB'_comm : D.gB' ≫ (ringPullback D.cube.f₂.hom.base).map
      (thickeningReduction D.cube.t₂ D.t₂_firstOrder.isThickening) =
    (ringPullback D.cube.g.hom.base).map ((ringPullback D.cube.f₁.hom.base).map
      (thickeningReduction D.cube.t₁ D.t₁_firstOrder.isThickening)) ≫ D.gB := by
  apply ((ringAdjunction D.cube.g.hom.base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left, gB', gB,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply ((ringAdjunction D.cube.f₁.hom.base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
  refine sheafHom_ext _ fun V σ => ?_
  obtain ⟨V⟩ := V
  have hs := congrArg (fun k => k.hom.app (op V) σ)
    (thickeningStructure_comp_reduction D.cube.t₂ D.cube.t₁ D.cube.h D.cube.h'
      D.cube.base_comm.symm D.t₂_firstOrder.isThickening D.t₁_firstOrder.isThickening)
  change ((ringPullback D.cube.f₂.hom.base).map
      (thickeningReduction D.cube.t₂ D.t₂_firstOrder.isThickening)).hom.app _
        (D.gB'Transpose.hom.app (op V) σ) =
    D.gBTranspose.hom.app (op V)
      ((thickeningReduction D.cube.t₁ D.t₁_firstOrder.isThickening).hom.app (op V) σ)
  refine (congrArg (fun x => ((ringPullback D.cube.f₂.hom.base).map
      (thickeningReduction D.cube.t₂ D.t₂_firstOrder.isThickening)).hom.app _ x)
    (D.gB'Transpose_apply V σ)).trans ?_
  refine (sheafHom_naturality_apply _ _ _ _).trans ?_
  refine (congrArg (fun x => ((ringPullback D.cube.f₂.hom.base).obj
      (ringOf D.cube.S₂)).obj.map _ x) (ringUnit_naturality _ _ _ _ _)).trans ?_
  refine Eq.trans ?_ (D.gBTranspose_apply V _).symm
  exact congrArg (fun x => ((ringPullback D.cube.f₂.hom.base).obj (ringOf D.cube.S₂)).obj.map _
    (ringUnit D.cube.f₂.hom.base (ringOf D.cube.S₂) _ x)) hs

/-- The transport of sections of a direct image of sheaves of modules along an equality of
morphisms of sheaves of rings is the identity. -/
theorem eqToHom_pushforward_val_app {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {C' : Type u} [Category.{u} C'] {J' : GrothendieckTopology C'} {F : C ⥤ C'}
    [F.IsContinuous J J'] {R : Sheaf J' RingCat.{u}} {S : Sheaf J RingCat.{u}}
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J J').obj R} (e : φ = ψ)
    (M : SheafOfModules.{u} R) (U : Cᵒᵖ) (x : ((SheafOfModules.pushforward φ).obj M).val.obj U) :
    (eqToHom (congrArg (fun k => (SheafOfModules.pushforward k).obj M) e)).val.app U x = x := by
  subst e
  rfl

/-- The `g`-map `ν` of the diagram, transposed: `𝒢₁ ⟶ g_*𝒢₂`. -/
abbrev nuTranspose : D.G₁ ⟶ (modulePushforward D.cube.g).obj D.G₂ :=
  (modulePullbackPushforwardAdjunction D.cube.g).homEquiv _ _ D.nu

/-- The transposed `ν`, read as a map into the direct image of the restriction of scalars of `𝒢₂`
along `g⁻¹𝒪_{X₁} ⟶ 𝒪_{X₂}`. -/
def nuFlat : D.G₁ ⟶ (SheafOfModules.pushforward (inverseImageRingHom D.cube.g.hom.base
      (ringOf D.cube.X₁))).obj ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology D.cube.X₂.carrier)
          (forget₂ CommRingCat.{u} RingCat.{u})).map (structureMap D.cube.g))).obj D.G₂) :=
  D.nuTranspose ≫ eqToHom (congrArg (fun k => (SheafOfModules.pushforward k).obj D.G₂)
    (structureSheafHom_eq D.cube.g))

/-- **The comparison `g⁻¹𝒢₁ ⟶ 𝒢₂` of the two ideal modules** induced by the `g`-map `ν`, linear
over `g⁻¹𝒪_{X₁}` acting on `𝒢₂` through `g⁻¹𝒪_{X₁} ⟶ 𝒪_{X₂}`: the transpose of `ν` along the
adjunction between inverse and direct images of sheaves of modules. -/
def nuInverseImage : inverseImageModule D.cube.g.hom.base (ringOf D.cube.X₁) D.G₁ ⟶
    (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology D.cube.X₂.carrier)
        (forget₂ CommRingCat.{u} RingCat.{u})).map (structureMap D.cube.g))).obj D.G₂ :=
  ((inverseImageAdjunction D.cube.g.hom.base (ringOf D.cube.X₁)).homEquiv _ _).symm D.nuFlat

/-- The comparison of the two ideal modules on induced sections is the transposed `ν`. -/
theorem nuInverseImage_moduleUnit (V : Opens D.cube.X₁.carrier) (μ : D.G₁.val.obj (op V)) :
    D.nuInverseImage.val.app (op ((Opens.map D.cube.g.hom.base).obj V))
        (moduleUnit D.cube.g.hom.base (ringOf D.cube.X₁) D.G₁ V μ) =
      pushApp D.nuTranspose V μ := by
  have h := ((inverseImageAdjunction D.cube.g.hom.base (ringOf D.cube.X₁)).homEquiv_unit
    (f := D.nuInverseImage))
  have h' := (Equiv.apply_symm_apply _ D.nuFlat).symm.trans h
  have e1 : D.nuFlat.val.app (op V) μ = D.nuTranspose.val.app (op V) μ :=
    eqToHom_pushforward_val_app (structureSheafHom_eq D.cube.g) D.G₂ (op V)
      (D.nuTranspose.val.app (op V) μ)
  have e2 := congrArg (fun k => k.val.app (op V) μ) h'
  exact e2.symm.trans e1

/-- The front square of the cube, as a morphism of thickenings. -/
abbrev frontSquare : MorphismOfThickenings.{u} := D.front.toMorphismOfThickenings

/-- The back square of the cube, as a morphism of thickenings. -/
abbrev backSquare : MorphismOfThickenings.{u} := D.back.toMorphismOfThickenings

/-- The square of bases of the cube, as a morphism of thickenings. -/
abbrev baseSq : MorphismOfThickenings.{u} :=
  D.cube.baseSquare D.t₁_firstOrder.1 D.t₂_firstOrder.1

/-- The front solution, on sections: `f'₁^♯` carries a section `j` of the ideal of `t₁` to the
section of `𝒪_{X'₁}` corresponding to `c₁(j)`. -/
theorem front_sections (W : Opens D.cube.S₁'.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₁).val.obj (op W)) :
    D.cube.f₁'.hom.c.app (op W) (idealι D.cube.t₁ W j) =
      layerIdealIncl D.cube.i₁ D.G₁ D.kernelIso₁ ((Opens.map D.cube.f₁'.hom.base).obj W)
        (mres D.G₁ (D.frontSquare.preimage_le W)
          (dtApp D.cube.f₁ D.cube.t₁ D.c₁ W j)) :=
  (MorphismOfThickenings.firstOrderIdealMap_eq_iff D.frontSquare D.i₁_firstOrder
    D.t₁_firstOrder D.G₁ D.kernelIso₁ D.c₁).1 D.front_isSolution W j

/-- The back solution, on sections. -/
theorem back_sections (W : Opens D.cube.S₂'.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₂).val.obj (op W)) :
    D.cube.f₂'.hom.c.app (op W) (idealι D.cube.t₂ W j) =
      layerIdealIncl D.cube.i₂ D.G₂ D.kernelIso₂ ((Opens.map D.cube.f₂'.hom.base).obj W)
        (mres D.G₂ (D.backSquare.preimage_le W)
          (dtApp D.cube.f₂ D.cube.t₂ D.c₂ W j)) :=
  (MorphismOfThickenings.firstOrderIdealMap_eq_iff D.backSquare D.i₂_firstOrder
    D.t₂_firstOrder D.G₂ D.kernelIso₂ D.c₂).1 D.back_isSolution W j

/-- The ideal map of the square of bases, transposed: `𝒥₁ ⟶ h'_*𝒥₂`. -/
abbrev baseIdealTranspose :
    AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₁ ⟶
      (modulePushforward D.cube.h').obj (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₂) :=
  (modulePullbackPushforwardAdjunction D.cube.h').homEquiv _ _ D.baseSq.idealMap.1

/-- The transposed ideal map of the square of bases, on sections. -/
theorem idealι_baseIdealTranspose (W : Opens D.cube.S₁'.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₁).val.obj (op W)) :
    idealι D.cube.t₂ _ (pushApp D.baseIdealTranspose W j) =
      D.cube.h'.hom.c.app (op W) (idealι D.cube.t₁ W j) :=
  D.baseSq.idealι_homEquiv_idealMap W j

/-- Transposing the image of a morphism under the left adjoint. -/
theorem homEquiv_map_eq {C' D' : Type*} [Category C'] [Category D'] {F : C' ⥤ D'} {G : D' ⥤ C'}
    (adj : F ⊣ G) {A B : C'} (x : A ⟶ B) :
    adj.homEquiv _ _ (F.map x) = x ≫ adj.unit.app B := by
  rw [Adjunction.homEquiv_unit]
  exact (adj.unit.naturality x).symm

/-- The triple transpose `𝒥₁ ⟶ t₁_*f₁_*g_*𝒢₂` of a map `g^*f₁^*t₁^*𝒥₁ ⟶ 𝒢₂`. -/
abbrev tripleTranspose
    (w : (modulePullback D.cube.g).obj ((modulePullback D.cube.f₁).obj
      ((modulePullback D.cube.t₁).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₁))) ⟶ D.G₂) :
    AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₁ ⟶
      (modulePushforward D.cube.t₁).obj ((modulePushforward D.cube.f₁).obj
        ((modulePushforward D.cube.g).obj D.G₂)) :=
  (modulePullbackPushforwardAdjunction D.cube.t₁).homEquiv _ _
    ((modulePullbackPushforwardAdjunction D.cube.f₁).homEquiv _ _
      ((modulePullbackPushforwardAdjunction D.cube.g).homEquiv _ _ w))

/-- The triple transpose of the left-hand side of the commutativity of `ν`. -/
theorem tripleTranspose_nu :
    D.tripleTranspose ((modulePullback D.cube.g).map D.c₁ ≫ D.nu) =
      doubleTranspose D.cube.f₁ D.cube.t₁ D.c₁ ≫
        (modulePushforward D.cube.t₁).map ((modulePushforward D.cube.f₁).map D.nuTranspose) := by
  rw [tripleTranspose, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]

/-- The triple transpose of the right-hand side of the commutativity of `ν`. -/
theorem tripleTranspose_baseIdealMap :
    D.tripleTranspose (D.cube.baseIdealMap D.t₁_firstOrder.1 D.t₂_firstOrder.1 ≫ D.c₂) =
      ((((D.baseIdealTranspose ≫ (modulePushforward D.cube.h').map
        (doubleTranspose D.cube.f₂ D.cube.t₂ D.c₂)) ≫
          (modulePushforwardComp D.cube.t₂ D.cube.h').hom.app _) ≫
          eqToHom (congrArg (fun k => (modulePushforward k).obj
            ((modulePushforward D.cube.f₂).obj D.G₂)) D.cube.base_comm.symm)) ≫
          (modulePushforwardComp D.cube.h D.cube.t₁).inv.app _) ≫
        (modulePushforward D.cube.t₁).map
          ((modulePushforwardComp D.cube.f₂ D.cube.h).hom.app D.G₂ ≫
            eqToHom (congrArg (fun k => (modulePushforward k).obj D.G₂)
              D.cube.source_comm.symm) ≫
            (modulePushforwardComp D.cube.g D.cube.f₁).inv.app D.G₂) := by
  simp only [tripleTranspose, DeformationCube.baseIdealMap, Category.assoc]
  rw [homEquiv_homEquiv_modulePullbackCompUniq_inv, homEquiv_eqToHom_comp D.cube.source_comm,
    homEquiv_comp_modulePullbackCompUniq_hom, Adjunction.homEquiv_naturality_left]
  simp only [Category.assoc]
  rw [Adjunction.homEquiv_naturality_right]
  rw [homEquiv_homEquiv_modulePullbackCompUniq_inv, homEquiv_eqToHom_comp D.cube.base_comm,
    homEquiv_comp_modulePullbackCompUniq_hom]
  have e1 := (modulePullbackPushforwardAdjunction D.cube.t₂).homEquiv_naturality_left
    D.baseSq.idealMap.1 ((modulePullbackPushforwardAdjunction D.cube.f₂).homEquiv _ _ D.c₂)
  have e2 := (modulePullbackPushforwardAdjunction D.cube.h').homEquiv_naturality_right
    D.baseSq.idealMap.1 (doubleTranspose D.cube.f₂ D.cube.t₂ D.c₂)
  have e3 := (congrArg ((modulePullbackPushforwardAdjunction D.cube.h').homEquiv _ _) e1).trans e2
  simp only [Category.assoc]
  exact (congrArg (fun x => x ≫ _) e3).trans (Category.assoc _ _ _)

/-- The commutativity of `ν` with the two maps out of the base ideals, transposed three times. -/
theorem nu_comm_transpose :
    doubleTranspose D.cube.f₁ D.cube.t₁ D.c₁ ≫
        (modulePushforward D.cube.t₁).map ((modulePushforward D.cube.f₁).map D.nuTranspose) =
      ((((D.baseIdealTranspose ≫ (modulePushforward D.cube.h').map
        (doubleTranspose D.cube.f₂ D.cube.t₂ D.c₂)) ≫
          (modulePushforwardComp D.cube.t₂ D.cube.h').hom.app _) ≫
          eqToHom (congrArg (fun k => (modulePushforward k).obj
            ((modulePushforward D.cube.f₂).obj D.G₂)) D.cube.base_comm.symm)) ≫
          (modulePushforwardComp D.cube.h D.cube.t₁).inv.app _) ≫
        (modulePushforward D.cube.t₁).map
          ((modulePushforwardComp D.cube.f₂ D.cube.h).hom.app D.G₂ ≫
            eqToHom (congrArg (fun k => (modulePushforward k).obj D.G₂)
              D.cube.source_comm.symm) ≫
            (modulePushforwardComp D.cube.g D.cube.f₁).inv.app D.G₂) :=
  D.tripleTranspose_nu.symm.trans
    ((congrArg D.tripleTranspose D.nu_comm).trans D.tripleTranspose_baseIdealMap)

/-- The preimages in `X₂` of an open of `S'₁` along the two sides of the cube. -/
theorem nu_comm_le (W : Opens D.cube.S₁'.carrier) :
    (Opens.map D.cube.g.hom.base).obj ((Opens.map D.cube.f₁.hom.base).obj
        ((Opens.map D.cube.t₁.hom.base).obj W)) ≤
      (Opens.map D.cube.f₂.hom.base).obj ((Opens.map D.cube.t₂.hom.base).obj
        ((Opens.map D.cube.h'.hom.base).obj W)) := by
  intro x hx
  have e1 := ConcreteCategory.congr_hom D.source_comm_base x
  have e2 := ConcreteCategory.congr_hom (congrArg (fun k => k.hom.base) D.cube.base_comm)
    (D.cube.f₂.hom.base x)
  change D.cube.h'.hom.base (D.cube.t₂.hom.base (D.cube.f₂.hom.base x)) ∈ W
  change D.cube.h.hom.base (D.cube.f₂.hom.base x) = D.cube.f₁.hom.base (D.cube.g.hom.base x) at e1
  change D.cube.t₁.hom.base (D.cube.h.hom.base (D.cube.f₂.hom.base x)) =
    D.cube.h'.hom.base (D.cube.t₂.hom.base (D.cube.f₂.hom.base x)) at e2
  rw [← e2, e1]
  exact hx

/-- **The commutativity of `ν` with the two maps out of the base ideals, on sections**: for a
section `j` of the ideal of `t₁`, `ν(c₁(j)) = c₂(j')` where `j'` is the image of `j` in the ideal
of `t₂`. -/
theorem nu_comm_sections (W : Opens D.cube.S₁'.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₁).val.obj (op W)) :
    pushApp D.nuTranspose ((Opens.map D.cube.f₁.hom.base).obj
        ((Opens.map D.cube.t₁.hom.base).obj W))
        (dtApp D.cube.f₁ D.cube.t₁ D.c₁ W j) =
      mres D.G₂ (D.nu_comm_le W)
        (dtApp D.cube.f₂ D.cube.t₂ D.c₂ ((Opens.map D.cube.h'.hom.base).obj W)
          (pushApp D.baseIdealTranspose W j)) := by
  have h := congrArg (fun k => k.val.app (op W) j) D.nu_comm_transpose
  refine h.trans ?_
  have hle₂ : (Opens.map (D.cube.h ≫ D.cube.t₁).hom.base).obj W ≤
      (Opens.map (D.cube.t₂ ≫ D.cube.h').hom.base).obj W := by
    rw [D.cube.base_comm]
  have hle₁ : (Opens.map (D.cube.g ≫ D.cube.f₁).hom.base).obj
        ((Opens.map D.cube.t₁.hom.base).obj W) ≤
      (Opens.map (D.cube.f₂ ≫ D.cube.h).hom.base).obj ((Opens.map D.cube.t₁.hom.base).obj W) := by
    rw [D.cube.source_comm]
  refine (eqToHom_modulePushforward_val_app D.cube.source_comm.symm D.G₂ _ hle₁ _).trans ?_
  refine (congrArg (mres D.G₂ hle₁)
    (eqToHom_modulePushforward_val_app D.cube.base_comm.symm _ W hle₂ _)).trans ?_
  exact mres_mres D.G₂ (opensMap_le D.cube.f₂.hom.base hle₂) hle₁ _

/-- The structure map of the front layer on the base ideal. -/
theorem front_structure_idealι (V : Opens D.cube.S₁.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₁).val.obj
      (op ((Opens.map (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv).obj V))) :
    (thickeningStructure D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
        D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening).hom.app (op V)
          (idealι D.cube.t₁ _ j) =
      layerIdealIncl D.cube.i₁ D.G₁ D.kernelIso₁
        ((Opens.map (thickeningHomeo D.cube.i₁ D.i₁_firstOrder.isThickening).inv).obj
          ((Opens.map D.cube.f₁.hom.base).obj V))
        (mres D.G₁ (solution_le D.cube.i₁ D.cube.t₁ D.cube.f₁ D.i₁_firstOrder.isThickening
            D.t₁_firstOrder.isThickening V)
          (dtApp D.cube.f₁ D.cube.t₁ D.c₁ _ j)) :=
  thickeningStructure_idealι D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
    D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening D.G₁ D.kernelIso₁ D.c₁
    D.front_sections V j

/-- The structure map of the back layer on the base ideal. -/
theorem back_structure_idealι (V : Opens D.cube.S₂.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₂).val.obj
      (op ((Opens.map (thickeningHomeo D.cube.t₂ D.t₂_firstOrder.isThickening).inv).obj V))) :
    (thickeningStructure D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
        D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening).hom.app (op V)
          (idealι D.cube.t₂ _ j) =
      layerIdealIncl D.cube.i₂ D.G₂ D.kernelIso₂
        ((Opens.map (thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).inv).obj
          ((Opens.map D.cube.f₂.hom.base).obj V))
        (mres D.G₂ (solution_le D.cube.i₂ D.cube.t₂ D.cube.f₂ D.i₂_firstOrder.isThickening
            D.t₂_firstOrder.isThickening V)
          (dtApp D.cube.f₂ D.cube.t₂ D.c₂ _ j)) :=
  thickeningStructure_idealι D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
    D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening D.G₂ D.kernelIso₂ D.c₂
    D.back_sections V j

/-- The comorphism of `h'` read on the reduced bases, on the base ideal. -/
theorem base_structure_idealι (V : Opens D.cube.S₁.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₁).val.obj
      (op ((Opens.map (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv).obj V))) :
    (thickeningStructure D.cube.t₂ D.cube.t₁ D.cube.h D.cube.h' D.cube.base_comm.symm
        D.t₂_firstOrder.isThickening D.t₁_firstOrder.isThickening).hom.app (op V)
          (idealι D.cube.t₁ _ j) =
      idealι D.cube.t₂ _ (mres _ (thickening_structure_le D.cube.t₂ D.cube.t₁ D.cube.h D.cube.h'
        D.cube.base_comm.symm D.t₂_firstOrder.isThickening D.t₁_firstOrder.isThickening V)
          (pushApp D.baseIdealTranspose _ j)) := by
  refine (thickeningStructure_apply _ _ _ _ _ _ _ V _).trans ?_
  refine (congrArg (fun x => D.cube.S₂'.presheaf.map _ x)
    (D.idealι_baseIdealTranspose _ j).symm).trans ?_
  exact (idealι_naturality D.cube.t₂ _ _).symm

/-- The comparison `gB'` followed by the structure map of the back layer, before
transposition. -/
abbrev frontBaseToBack :
    thickenedRing D.cube.t₁ D.t₁_firstOrder.isThickening ⟶ (ringPushforward D.cube.f₁.hom.base).obj
      ((ringPushforward D.cube.g.hom.base).obj
        (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening)) :=
  D.gB'Transpose ≫ (ringPushforward D.cube.f₁.hom.base).map ((ringPushforward D.cube.g.hom.base).map
    (thickeningStructureMap D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
      D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening))

/-- The comparison `gB'` followed by the structure map of the back layer, on the base ideal. -/
theorem frontBaseToBack_idealι (V : Opens D.cube.S₁.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₁).val.obj
      (op ((Opens.map (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv).obj V)))
    (hle : (Opens.map D.cube.i₂.hom.base).obj ((Opens.map (thickeningHomeo D.cube.i₂
        D.i₂_firstOrder.isThickening).inv).obj ((Opens.map D.cube.g.hom.base).obj
          ((Opens.map D.cube.f₁.hom.base).obj V))) ≤
      (Opens.map D.cube.f₂.hom.base).obj ((Opens.map D.cube.t₂.hom.base).obj
        ((Opens.map D.cube.h'.hom.base).obj
          ((Opens.map (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv).obj V)))) :
    D.frontBaseToBack.hom.app (op V) (idealι D.cube.t₁ _ j) =
      layerIdealIncl D.cube.i₂ D.G₂ D.kernelIso₂ _ (mres D.G₂ hle
        (dtApp D.cube.f₂ D.cube.t₂ D.c₂ _ (pushApp D.baseIdealTranspose _ j))) := by
  change (thickeningStructureMap D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
      D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening).hom.app _
        (D.gB'Transpose.hom.app (op V) _) = _
  refine (congrArg (fun x => (thickeningStructureMap D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂'
    D.cube.back_comm D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening).hom.app _ x)
      (D.gB'Transpose_apply V _)).trans ?_
  refine (sheafHom_naturality_apply _ _ _ _).trans ?_
  refine (congrArg (fun x => (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening).obj.map _ x)
    (ringAdjunction_homEquiv_symm_ringUnit _ _ _ _ _)).trans ?_
  refine (congrArg (fun x => (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening).obj.map _
    ((thickeningStructure D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
      D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening).hom.app _ x))
    (D.base_structure_idealι V j)).trans ?_
  refine (congrArg (fun x => (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening).obj.map _ x)
    (D.back_structure_idealι _ _)).trans ?_
  refine (layerIdealIncl_naturality D.cube.i₂ D.G₂ D.kernelIso₂ _ _).symm.trans ?_
  refine congrArg (layerIdealIncl D.cube.i₂ D.G₂ D.kernelIso₂ _) ?_
  refine (congrArg (fun x => mres D.G₂ _ (mres D.G₂ _ x))
    (dtApp_mres D.cube.f₂ D.cube.t₂ D.c₂ _ _)).trans ?_
  refine (congrArg (fun x => mres D.G₂ _ x) (mres_mres D.G₂ _ _ _)).trans ?_
  exact mres_mres D.G₂ _ _ _

/-- The opens of `X₂` over which the core identity of `nu_base` is read. -/
theorem nu_base_le (V : Opens D.cube.S₁.carrier) :
    (Opens.map D.cube.i₂.hom.base).obj ((Opens.map (thickeningHomeo D.cube.i₂
        D.i₂_firstOrder.isThickening).inv).obj ((Opens.map D.cube.g.hom.base).obj
          ((Opens.map D.cube.f₁.hom.base).obj V))) ≤
      (Opens.map D.cube.f₂.hom.base).obj ((Opens.map D.cube.t₂.hom.base).obj
        ((Opens.map D.cube.h'.hom.base).obj
          ((Opens.map (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv).obj V))) := by
  intro x hx
  change D.cube.f₁.hom.base (D.cube.g.hom.base
    ((thickeningHomeo D.cube.i₂ D.i₂_firstOrder.isThickening).inv
    (D.cube.i₂.hom.base x))) ∈ V at hx
  rw [thickeningHomeo_hom_inv_apply] at hx
  refine D.nu_comm_le _ ?_
  change (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv
    (D.cube.t₁.hom.base (D.cube.f₁.hom.base (D.cube.g.hom.base x))) ∈ V
  rwa [thickeningHomeo_hom_inv_apply]

/-- **The core of the compatibility of `ν` with the base, on `X₁`.** Let `j` be a section of the
ideal of `t₁`, read as a section of `k_*𝒪_{S'₁}` killed by the reduction, and let `μ` be a section
of `𝒢₁` whose image in `k_*𝒪_{X'₁}` is the image of `j` under the front structure map. Then the
image of `j` under `gB'` followed by the back structure map is the image of `ν(μ)` in
`k_*𝒪_{X'₂}`. -/
theorem nu_base_core (V : Opens D.cube.S₁.carrier)
    (j : (AlgebraicGeometry.SheafOfModules.idealSheaf D.cube.t₁).val.obj
      (op ((Opens.map (thickeningHomeo D.cube.t₁ D.t₁_firstOrder.isThickening).inv).obj V)))
    (W : Opens D.cube.X₁.carrier) (hW : W ≤ (Opens.map D.cube.f₁.hom.base).obj V)
    (μ : D.G₁.val.obj (op W))
    (hμ : (thickenedRing D.cube.i₁ D.i₁_firstOrder.isThickening).obj.map (homOfLE hW).op
        ((thickeningStructure D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
          D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening).hom.app (op V)
            (idealι D.cube.t₁ _ j)) =
      thickeningKernelInclusionApp D.cube.i₁ D.i₁_firstOrder.isThickening D.G₁ D.kernelIso₁ W μ) :
    (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening).obj.map
        (homOfLE (opensMap_le D.cube.g.hom.base hW)).op
        (D.frontBaseToBack.hom.app (op V) (idealι D.cube.t₁ _ j)) =
      thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂ D.kernelIso₂
        ((Opens.map D.cube.g.hom.base).obj W) (pushApp D.nuTranspose W μ) := by
  have hpp := thickening_preimage_preimage D.cube.i₁ D.i₁_firstOrder.isThickening W
  have h1 := (congrArg (fun x => (thickenedRing D.cube.i₁ D.i₁_firstOrder.isThickening).obj.map
      (homOfLE hW).op x) (D.front_structure_idealι V j)).trans
    ((layerIdealIncl_naturality D.cube.i₁ D.G₁ D.kernelIso₁
      (opensMap_le (thickeningHomeo D.cube.i₁ D.i₁_firstOrder.isThickening).inv hW) _).symm.trans
      (congrArg (layerIdealIncl D.cube.i₁ D.G₁ D.kernelIso₁ _) (mres_mres D.G₁ _ _ _)))
  have h3 := layerIdealIncl_injective D.cube.i₁ D.G₁ D.kernelIso₁ _ (h1.symm.trans hμ)
  have h4 := congrArg (mres D.G₁ hpp.ge) h3
  rw [mres_mres, mres_mres, mres_self] at h4
  obtain ⟨hle', hμ'⟩ : ∃ hle', μ = mres D.G₁ hle'
      (dtApp D.cube.f₁ D.cube.t₁ D.c₁ _ j) := ⟨_, h4.symm⟩
  subst hμ'
  refine (congrArg (fun x => (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening).obj.map _ x)
    (D.frontBaseToBack_idealι V j (D.nu_base_le V))).trans ?_
  refine (layerIdealIncl_naturality D.cube.i₂ D.G₂ D.kernelIso₂ _ _).symm.trans ?_
  rw [thickeningKernelInclusionApp_apply]
  refine congrArg (layerIdealIncl D.cube.i₂ D.G₂ D.kernelIso₂ _) ?_
  rw [pushApp_mres, D.nu_comm_sections]
  exact (mres_mres D.G₂ _ _ _).trans
    ((congrArg (mres D.G₂ _) (mres_mres D.G₂ _ _ _)).trans (mres_mres D.G₂ _ _ _)).symm

/-- The comparison `gB'` followed by the structure map of the back layer, transposed along
`g`. -/
abbrev frontBaseToBack' :
    (ringPullback D.cube.f₁.hom.base).obj (thickenedRing D.cube.t₁ D.t₁_firstOrder.isThickening) ⟶
      (ringPushforward D.cube.g.hom.base).obj
        (thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening) :=
  (ringAdjunction D.cube.g.hom.base).homEquiv _ _ (D.gB' ≫
    thickeningStructureMap D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
      D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening)

/-- Transposing `frontBaseToBack'` along `f₁` gives `frontBaseToBack`. -/
theorem homEquiv_frontBaseToBack' :
    (ringAdjunction D.cube.f₁.hom.base).homEquiv _ _ D.frontBaseToBack' = D.frontBaseToBack := by
  rw [frontBaseToBack', Adjunction.homEquiv_naturality_right, gB', Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]

/-- **The compatibility of `ν` with the base, on `X₁`.** A section of `f₁⁻¹k_*𝒪_{S'₁}` killed by
the base reduction whose image under the front structure map is the image of a section `μ` of
`𝒢₁` is carried by `gB'` and the back structure map to the image of `ν(μ)`. -/
theorem nu_base_X₁ (V : Opens D.cube.X₁.carrier)
    (a : ((ringPullback D.cube.f₁.hom.base).obj
      (thickenedRing D.cube.t₁ D.t₁_firstOrder.isThickening)).obj.obj (op V))
    (μ : D.G₁.val.obj (op V))
    (ha : ((ringPullback D.cube.f₁.hom.base).map
      (thickeningReduction D.cube.t₁ D.t₁_firstOrder.isThickening)).hom.app (op V) a = 0)
    (hμ : (thickeningStructureMap D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
        D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening).hom.app (op V) a =
      thickeningKernelInclusionApp D.cube.i₁ D.i₁_firstOrder.isThickening D.G₁ D.kernelIso₁ V μ) :
    D.frontBaseToBack'.hom.app (op V) a =
      thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂ D.kernelIso₂
        ((Opens.map D.cube.g.hom.base).obj V) (pushApp D.nuTranspose V μ) := by
  let T₁ := thickenedRing D.cube.t₁ D.t₁_firstOrder.isThickening
  let P₁ := (ringPullback D.cube.f₁.hom.base).obj T₁
  let red₁ := thickeningReduction D.cube.t₁ D.t₁_firstOrder.isThickening
  let str₁ := thickeningStructureMap D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
    D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening
  let O₂ := thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening
  refine ringSheaf_eq_of_locally_eq O₂ _ _ fun y hy => ?_
  obtain ⟨Vt, hVt, σ, W, hxW, hWV, hWVt, e⟩ :=
    exists_restrict_eq_ringUnit D.cube.f₁.hom.base T₁ a (D.cube.g.hom.base y) hy
  obtain ⟨Vt', hVt', hVt'Vt, e1⟩ := exists_reduction_eq_zero_of_ringUnit D.cube.f₁.hom.base red₁
    a ha σ hWV hWVt e _ hxW
  obtain ⟨j, hj⟩ := exists_idealι_of_reduction D.cube.t₁ D.t₁_firstOrder.isThickening Vt' _ e1
  -- the neighbourhood on which everything is induced
  let W' := W ⊓ (Opens.map D.cube.f₁.hom.base).obj Vt'
  have hW'W : W' ≤ W := inf_le_left
  have hW'Vt' : W' ≤ (Opens.map D.cube.f₁.hom.base).obj Vt' := inf_le_right
  have ea : P₁.obj.map (homOfLE (hW'W.trans hWV)).op a =
      P₁.obj.map (homOfLE hW'Vt').op
        (ringUnit D.cube.f₁.hom.base T₁ Vt' (idealι D.cube.t₁ _ j)) := by
    rw [hj, ← ringUnit_restrict D.cube.f₁.hom.base T₁ hVt'Vt hW'Vt', ← sheaf_map_map P₁ hWV hW'W,
      e, sheaf_map_map]
  -- the hypothesis on `μ`, restricted
  have hμ' : (thickenedRing D.cube.i₁ D.i₁_firstOrder.isThickening).obj.map (homOfLE hW'Vt').op
      ((thickeningStructure D.cube.i₁ D.cube.t₁ D.cube.f₁ D.cube.f₁' D.cube.front_comm
        D.i₁_firstOrder.isThickening D.t₁_firstOrder.isThickening).hom.app (op Vt')
          (idealι D.cube.t₁ _ j)) =
      thickeningKernelInclusionApp D.cube.i₁ D.i₁_firstOrder.isThickening D.G₁ D.kernelIso₁ W'
        (mres D.G₁ (hW'W.trans hWV) μ) := by
    refine Eq.symm ?_
    refine (thickeningKernelInclusionApp_naturality D.cube.i₁ D.i₁_firstOrder.isThickening D.G₁
      D.kernelIso₁ (hW'W.trans hWV) μ).trans ?_
    refine (congrArg (fun x => D.cube.X₁'.presheaf.map _ x) hμ.symm).trans ?_
    refine (sheafHom_map_eq str₁ _ _ ea).trans ?_
    exact congrArg (fun x => (thickenedRing D.cube.i₁ D.i₁_firstOrder.isThickening).obj.map _ x)
      (ringAdjunction_homEquiv_symm_ringUnit _ _ _ _ _)
  have hcore := D.nu_base_core Vt' j W' hW'Vt' _ hμ'
  refine ⟨(Opens.map D.cube.g.hom.base).obj W', ⟨hxW, hVt'⟩,
    opensMap_le D.cube.g.hom.base (hW'W.trans hWV), ?_⟩
  refine (sheafHom_map_eq D.frontBaseToBack' _ _ ea).trans ?_
  refine (congrArg (fun x => O₂.obj.map _ x)
    ((ringAdjunction_homEquiv_apply D.cube.f₁.hom.base T₁ D.frontBaseToBack' Vt' _).symm.trans
      (congrArg (fun k => k.hom.app (op Vt') (idealι D.cube.t₁ _ j))
        D.homEquiv_frontBaseToBack'))).trans ?_
  refine hcore.trans ?_
  refine (congrArg (thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂
    D.kernelIso₂ _) (pushApp_mres D.nuTranspose (hW'W.trans hWV) μ)).trans ?_
  exact thickeningKernelInclusionApp_naturality D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂
    D.kernelIso₂ _ _

/-- The comparison `gB'` followed by the back structure map, on induced sections. -/
theorem gB'_comp_structure_ringUnit (V : Opens D.cube.X₁.carrier)
    (b : ((ringPullback D.cube.f₁.hom.base).obj
      (thickenedRing D.cube.t₁ D.t₁_firstOrder.isThickening)).obj.obj (op V)) :
    (thickeningStructureMap D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
        D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening).hom.app _
        (D.gB'.hom.app _ (ringUnit D.cube.g.hom.base _ V b)) =
      D.frontBaseToBack'.hom.app (op V) b :=
  (ringAdjunction_homEquiv_apply D.cube.g.hom.base _ (D.gB' ≫
    thickeningStructureMap D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
      D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening) V b).symm

/-- **The compatibility of `ν` with the base ideals, on `X₂`**: the field `nu_base` of the
reduced diagram. -/
theorem nu_base (U : (Opens D.cube.X₂.carrier)ᵒᵖ)
    (a : (D.frontLayer.inverseImage D.cube.g.hom.base).OB'.obj.obj U)
    (m : (D.frontLayer.inverseImage D.cube.g.hom.base).G.val.obj U)
    (ha : (D.frontLayer.inverseImage D.cube.g.hom.base).baseReduction.hom.app U a = 0)
    (hm : (D.frontLayer.inverseImage D.cube.g.hom.base).f'.hom.app U a =
      (D.frontLayer.inverseImage D.cube.g.hom.base).incl m) :
    D.backLayer.f'.hom.app U (D.gB'.hom.app U a) =
      D.backLayer.incl (show D.backLayer.G.val.obj U from D.nuInverseImage.val.app U m) := by
  obtain ⟨U⟩ := U
  let L₁ := D.frontLayer
  let g := D.cube.g.hom.base
  let P := (ringPullback g).obj L₁.OB'
  let str₂ := thickeningStructureMap D.cube.i₂ D.cube.t₂ D.cube.f₂ D.cube.f₂' D.cube.back_comm
    D.i₂_firstOrder.isThickening D.t₂_firstOrder.isThickening
  let O₂ := thickenedRing D.cube.i₂ D.i₂_firstOrder.isThickening
  obtain ⟨a, rfl⟩ : ∃ a' : P.obj.obj (op U), a' = a := ⟨a, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m' : (inverseImageModule g L₁.O L₁.G).val.obj (op U), m' = m := ⟨m, rfl⟩
  change ((ringPullback g).map L₁.baseReduction).hom.app (op U) a = 0 at ha
  change ((ringPullback g).map L₁.f').hom.app (op U) a =
    (LiftSquare.inverseImageKernelInclusion g L₁).val.app (op U) m at hm
  refine ringSheaf_eq_of_locally_eq O₂ _ _ fun y hy => ?_
  obtain ⟨V₀, hV₀, b, W₀, hyW₀, hW₀U, hW₀V, e⟩ := exists_restrict_eq_ringUnit g L₁.OB' a y hy
  obtain ⟨V₁, hV₁, μ, W₁, hyW₁, hW₁U, hW₁V, em, -⟩ :=
    LiftSquare.exists_restrict_inverseImageKernelInclusion g L₁ m y hy
  obtain ⟨V₂, hV₂, hV₂V₀, e2⟩ := exists_reduction_eq_zero_of_ringUnit g L₁.baseReduction a ha b
    hW₀U hW₀V e y hyW₀
  -- the image of `b` under the front structure map is the image of `μ` near `g y`
  let W₃ := W₀ ⊓ W₁
  have hW₃₀ : W₃ ≤ W₀ := inf_le_left
  have hW₃₁ : W₃ ≤ W₁ := inf_le_right
  let V₃ := V₀ ⊓ V₁
  have hW₃V₃ : W₃ ≤ (Opens.map g).obj V₃ := fun z hz => ⟨hW₀V hz.1, hW₁V hz.2⟩
  have e3 : ((ringPullback g).obj L₁.O').obj.map (homOfLE hW₃V₃).op
      (ringUnit g L₁.O' V₃ (L₁.f'.hom.app (op V₃) (L₁.OB'.obj.map (homOfLE inf_le_left).op b))) =
      ((ringPullback g).obj L₁.O').obj.map (homOfLE hW₃V₃).op
        (ringUnit g L₁.O' V₃ (L₁.incl (mres L₁.G (inf_le_right : V₃ ≤ V₁) μ))) := by
    let G' := inverseImageModule g L₁.O L₁.G
    have eb : P.obj.map (homOfLE hW₃V₃).op
        (ringUnit g L₁.OB' V₃ (L₁.OB'.obj.map (homOfLE inf_le_left).op b)) =
        P.obj.map (homOfLE (hW₃₀.trans hW₀U)).op a := by
      rw [← ringUnit_restrict g L₁.OB' inf_le_left hW₃V₃, ← sheaf_map_map P hW₀V hW₃₀, ← e,
        sheaf_map_map]
    have emu : G'.val.map (homOfLE (hW₃₁.trans hW₁U)).op m =
        G'.val.map (homOfLE hW₃V₃).op (moduleUnit g L₁.O L₁.G V₃ (mres L₁.G inf_le_right μ)) := by
      rw [← module_map_map G' hW₁U hW₃₁, em, module_map_map]
      exact moduleUnit_restrict g L₁.O L₁.G inf_le_right hW₃V₃ μ
    refine (congrArg (fun x => ((ringPullback g).obj L₁.O').obj.map (homOfLE hW₃V₃).op x)
      (ringUnit_naturality g L₁.OB' L₁.f' V₃ _)).symm.trans ?_
    refine (sheafHom_map_eq ((ringPullback g).map L₁.f') _ _ eb).trans ?_
    refine (congrArg (fun x => ((ringPullback g).obj L₁.O').obj.map _ x) hm).trans ?_
    refine (LiftSquare.inverseImageKernelInclusion_naturality g L₁ _ m).symm.trans ?_
    refine (congrArg (fun x => (LiftSquare.inverseImageKernelInclusion g L₁).val.app (op W₃) x)
      emu).trans ?_
    refine (LiftSquare.inverseImageKernelInclusion_naturality g L₁ _ _).trans ?_
    exact congrArg (fun x => ((ringPullback g).obj L₁.O').obj.map _ x)
      (LiftSquare.inverseImageKernelInclusion_moduleUnit g L₁ V₃ _)
  obtain ⟨V₄, hV₄, hV₄V₃, e4⟩ :=
    exists_restrict_eq_of_ringUnit_eq g L₁.O' _ _ y (show y ∈ W₃ from ⟨hyW₀, hyW₁⟩) hW₃V₃ e3
  -- the common neighbourhood of `g y`
  let V₅ := V₄ ⊓ V₂
  have hV₅₄ : V₅ ≤ V₄ := inf_le_left
  have hV₅₀ : V₅ ≤ V₀ := hV₅₄.trans (hV₄V₃.trans inf_le_left)
  have hV₅₁ : V₅ ≤ V₁ := hV₅₄.trans (hV₄V₃.trans inf_le_right)
  have hb₅ : L₁.baseReduction.hom.app (op V₅) (L₁.OB'.obj.map (homOfLE hV₅₀).op b) = 0 := by
    rw [← sheaf_map_map L₁.OB' hV₂V₀ inf_le_right, sheafHom_naturality_apply, e2, map_zero]
  have hμ₅ : L₁.f'.hom.app (op V₅) (L₁.OB'.obj.map (homOfLE hV₅₀).op b) =
      L₁.incl (mres L₁.G hV₅₁ μ) := by
    have e5 := congrArg (fun x => L₁.O'.obj.map (homOfLE hV₅₄).op x) e4
    simp only [sheaf_map_map] at e5
    refine (congrArg (fun x => L₁.f'.hom.app (op V₅) x)
      (sheaf_map_map L₁.OB' (inf_le_left : V₃ ≤ V₀) (hV₅₄.trans hV₄V₃) b).symm).trans ?_
    refine (sheafHom_naturality_apply _ L₁.f' _ _).trans ?_
    refine e5.trans ?_
    refine (L₁.incl_naturality (homOfLE (hV₅₄.trans hV₄V₃)).op _).symm.trans ?_
    exact congrArg L₁.incl (mres_mres L₁.G _ _ μ)
  have hcore := D.nu_base_X₁ V₅ _ _ hb₅ hμ₅
  let W₅ := W₃ ⊓ (Opens.map g).obj V₅
  have hW₅₃ : W₅ ≤ W₃ := inf_le_left
  have hW₅V : W₅ ≤ (Opens.map g).obj V₅ := inf_le_right
  have hW₅U : W₅ ≤ U := hW₅₃.trans (hW₃₀.trans hW₀U)
  refine ⟨W₅, ⟨⟨hyW₀, hyW₁⟩, hV₄, hV₂⟩, hW₅U, ?_⟩
  have ea : P.obj.map (homOfLE hW₅U).op a =
      P.obj.map (homOfLE hW₅V).op (ringUnit g L₁.OB' V₅ (L₁.OB'.obj.map (homOfLE hV₅₀).op b)) := by
    rw [← ringUnit_restrict g L₁.OB' hV₅₀ hW₅V, ← sheaf_map_map P hW₀U (hW₅₃.trans hW₃₀), e,
      sheaf_map_map]
  let G' := inverseImageModule g L₁.O L₁.G
  have emu : G'.val.map (homOfLE hW₅U).op m =
      G'.val.map (homOfLE hW₅V).op (moduleUnit g L₁.O L₁.G V₅ (mres L₁.G hV₅₁ μ)) :=
    (module_map_map G' hW₁U (hW₅₃.trans hW₃₁) m).symm.trans
      ((congrArg (fun x => G'.val.map (homOfLE (hW₅₃.trans hW₃₁)).op x) em).trans
        ((module_map_map G' hW₁V (hW₅₃.trans hW₃₁) _).trans
          (moduleUnit_restrict g L₁.O L₁.G hV₅₁ hW₅V μ)))
  -- the left-hand side near `y`
  have hl : O₂.obj.map (homOfLE hW₅U).op (str₂.hom.app (op U) (D.gB'.hom.app (op U) a)) =
      O₂.obj.map (homOfLE hW₅V).op (thickeningKernelInclusionApp D.cube.i₂
        D.i₂_firstOrder.isThickening D.G₂ D.kernelIso₂ ((Opens.map g).obj V₅)
          (pushApp D.nuTranspose V₅ (mres L₁.G hV₅₁ μ))) := by
    refine (sheafHom_map_eq str₂ _ _ (sheafHom_map_eq D.gB' _ _ ea)).trans ?_
    refine congrArg (fun x => O₂.obj.map (homOfLE hW₅V).op x) ?_
    exact (D.gB'_comp_structure_ringUnit V₅ _).trans hcore
  refine hl.trans ?_
  -- the right-hand side near `y`
  have hr : thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂ D.kernelIso₂
      W₅ (mres D.G₂ hW₅U (D.nuInverseImage.val.app (op U) m)) =
      thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂ D.kernelIso₂
      W₅ (mres D.G₂ hW₅V (pushApp D.nuTranspose V₅ (mres L₁.G hV₅₁ μ))) := by
    refine congrArg (thickeningKernelInclusionApp D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂
      D.kernelIso₂ W₅) ?_
    refine (mres_naturality _ D.nuInverseImage hW₅U m).symm.trans ?_
    refine (congrArg (fun x => D.nuInverseImage.val.app (op W₅) x) emu).trans ?_
    refine (mres_naturality _ D.nuInverseImage hW₅V
      (moduleUnit g L₁.O L₁.G V₅ (mres L₁.G hV₅₁ μ))).trans ?_
    exact congrArg (mres D.G₂ hW₅V) (D.nuInverseImage_moduleUnit V₅ _)
  refine (thickeningKernelInclusionApp_naturality D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂
    D.kernelIso₂ hW₅V _).symm.trans ?_
  refine hr.symm.trans ?_
  exact thickeningKernelInclusionApp_naturality D.cube.i₂ D.i₂_firstOrder.isThickening D.G₂
    D.kernelIso₂ hW₅U _

/-- **The diagram of Stacks 08U8 reduced to `X₂`**, as in the source's proof: the front layer of
the cube pulled back along `g` — the base `g⁻¹f₁⁻¹𝒪_{S₁}` thickened to `g⁻¹f₁⁻¹𝒪_{S'₁}`, the
source `g⁻¹𝒪_{X₁}` thickened to `g⁻¹𝒪_{X'₁}`, with ideal module `g⁻¹𝒢₁` — the back layer on `X₂`
with ideal module `𝒢₂`, the comparisons `g⁻¹𝒪_{X₁} ⟶ 𝒪_{X₂}`, `g⁻¹f₁⁻¹𝒪_{S₁} ⟶ f₂⁻¹𝒪_{S₂}` and
`g⁻¹f₁⁻¹𝒪_{S'₁} ⟶ f₂⁻¹𝒪_{S'₂}` induced by the cube, and the comparison `g⁻¹𝒢₁ ⟶ 𝒢₂` induced
by `ν`. The thickened structure sheaves are read on the reduced spaces through the
homeomorphisms underlying the thickenings. -/
def toFirstOrderLiftDiagram :
    Deformation.ToposThickening.FirstOrderLiftDiagram.{u, u, u}
      (Opens.grothendieckTopology D.cube.X₂.carrier) where
  front := D.frontLayer.inverseImage D.cube.g.hom.base
  back := D.backLayer
  g := structureMap D.cube.g
  gB := D.gB
  gB' := D.gB'
  g_comm := D.g_comm
  gB_comm := D.gB'_comm
  nu := D.nuInverseImage
  nu_base U a m ha hm := D.nu_base U a m ha hm

/-- The reduced source structure sheaf of the front layer is `g⁻¹𝒪_{X₁}`. -/
@[simp]
theorem toFirstOrderLiftDiagram_front_O :
    D.toFirstOrderLiftDiagram.front.O = Stacks.SheafOfModules.inverseImageMiddleRing D.cube.g :=
  rfl

/-- The reduced base structure sheaf of the front layer is `g⁻¹f₁⁻¹𝒪_{S₁}`. -/
@[simp]
theorem toFirstOrderLiftDiagram_front_OB :
    D.toFirstOrderLiftDiagram.front.OB =
      Stacks.SheafOfModules.inverseImageBaseRing D.cube.g D.cube.f₁ :=
  rfl

/-- The reduced structure map of the front layer is `g⁻¹` of the structure map of `f₁`. -/
@[simp]
theorem toFirstOrderLiftDiagram_front_f :
    D.toFirstOrderLiftDiagram.front.f =
      Stacks.SheafOfModules.inverseImageFirstRingMap D.cube.g D.cube.f₁ :=
  rfl

/-- The reduced source structure sheaf of the back layer is `𝒪_{X₂}`. -/
@[simp]
theorem toFirstOrderLiftDiagram_back_O : D.toFirstOrderLiftDiagram.back.O = D.cube.X₂.sheaf :=
  rfl

/-- The comparison of the reduced sources is the structure map `g⁻¹𝒪_{X₁} ⟶ 𝒪_{X₂}` of `g`. -/
@[simp]
theorem toFirstOrderLiftDiagram_g :
    D.toFirstOrderLiftDiagram.g = Stacks.SheafOfModules.ringedSpaceStructureMap D.cube.g :=
  rfl

/-- The ideal module of the back layer is `𝒢₂`. -/
@[simp]
theorem toFirstOrderLiftDiagram_back_G : D.toFirstOrderLiftDiagram.back.G = D.G₂ :=
  rfl

end DeformationIdealDiagram

end AlgebraicGeometry.RingedSpaceThickening

end
