module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.CechLift

/-!
# Sections of the low-degree summands of the Čech object of a family

Let `f_i : U_i ⟶ X` be a family of arrows of a category with fibre products. The summand of
degree `0` of the Čech object attached to `i` is the one-fold product `U_i` over `X`, whose
projection to `U_i` has a section `s_i`; the summand of degree `1` attached to `(i, j)` is the
twofold product `U_i ×_X U_j`, which receives the arrow `u_{ij}` from the fibre product
`U_i ×_X U_j` of `C`. These arrows are compatible with the projections and with the faces of
the Čech object given by the constant maps `[0] ⟶ [1]`.

## Main definitions

* `AlgebraicGeometry.RingedSite.CoveringGlueing.cechVertexSection`: the section `s_i`.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.cechEdgeLift`: the arrow `u_{ij}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace AlgebraicGeometry.RingedSite.CoveringGlueing

variable {X : RingedSite.{u, u, u}} [HasPullbacks X.C] {X₀ : X.C} {ι : Type u} {U : ι → X.C}
  (f : ∀ i, U i ⟶ X₀)

/-- The summand of degree `0` of the Čech object attached to `i`. -/
abbrev cechVertex (i : ι) : ToType (unop (op ⦋0⦌)) → (family f).I := fun _ => i

/-- The summand of degree `1` of the Čech object attached to `(i, j)`. -/
abbrev cechEdge (i j : ι) : ToType (unop (op ⦋1⦌)) → (family f).I := ![i, j]

/-- The face of the summand attached to `(i, j)` given by the constant map `[0] ⟶ [1]` at `k`. -/
abbrev cechEdgeFace (i j : ι) (k : Fin 2) :=
  ((cechLift f).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ k).op).φ (cechEdge f i j)

/-- The section `U_i ⟶ U_i` of the projection of the one-fold product. -/
def cechVertexSection (i : ι) :
    U i ⟶ (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).V.left :=
  (Pi.lift (fun _ => 𝟙 ((family f).obj i)) :
    (family f).obj i ⟶ ∏ᶜ ((family f).obj ∘ cechVertex f i)).left

/-- `cechVertexSection f i` is a section of the projection of the one-fold product to `U_i`. -/
theorem cechVertexSection_comp (i : ι) :
    cechVertexSection f i ≫ (((cechLift f).obj (op ⦋0⦌)).obj (cechVertex f i)).a = 𝟙 (U i) := by
  change (Pi.lift (fun _ => 𝟙 ((family f).obj i)) :
    (family f).obj i ⟶ ∏ᶜ ((family f).obj ∘ cechVertex f i)).left ≫
      (Pi.π ((family f).obj ∘ cechVertex f i) 0).left = 𝟙 (U i)
  rw [← Over.comp_left, Pi.lift_π]
  rfl

/-- The cone over the twofold product given by the two projections of the fibre product. -/
def cechEdgeCone (i j : ι) :
    ∀ k : Fin 2, Over.mk (pullback.fst (f i) (f j) ≫ f i) ⟶ ((family f).obj ∘ cechEdge f i j) k :=
  Fin.cases (Over.homMk (pullback.fst (f i) (f j)) rfl)
    (Fin.cases (Over.homMk (pullback.snd (f i) (f j)) pullback.condition.symm) finZeroElim)

/-- The arrow from the fibre product `U_i ×_X U_j` to the twofold product. -/
def cechEdgeLift (i j : ι) :
    pullback (f i) (f j) ⟶ (((cechLift f).obj (op ⦋1⦌)).obj (cechEdge f i j)).V.left :=
  (Pi.lift (cechEdgeCone f i j) :
    Over.mk (pullback.fst (f i) (f j) ≫ f i) ⟶ ∏ᶜ ((family f).obj ∘ cechEdge f i j)).left

/-- The arrow `cechEdgeLift f i j` followed by the structure arrow of the twofold product is the
first projection of the fibre product. -/
theorem cechEdgeLift_comp (i j : ι) :
    cechEdgeLift f i j ≫ (((cechLift f).obj (op ⦋1⦌)).obj (cechEdge f i j)).a =
      pullback.fst (f i) (f j) := by
  change (Pi.lift (cechEdgeCone f i j) :
    Over.mk (pullback.fst (f i) (f j) ≫ f i) ⟶ ∏ᶜ ((family f).obj ∘ cechEdge f i j)).left ≫
      (Pi.π ((family f).obj ∘ cechEdge f i j) 0).left = _
  rw [← Over.comp_left, Pi.lift_π]
  rfl

/-- The face `cechEdgeFace f i j k` followed by the structure arrow of the one-fold product is
the `k`-th projection of the twofold product. -/
theorem cechEdgeFace_comp (i j : ι) (k : Fin 2) :
    (cechEdgeFace f i j k).hom.left ≫
        (((cechLift f).obj (op ⦋0⦌)).obj (fun _ => cechEdge f i j k)).a =
      (Pi.π ((family f).obj ∘ cechEdge f i j) k).left := by
  change (Pi.lift (fun _ => Pi.π ((family f).obj ∘ cechEdge f i j) k) :
    ∏ᶜ ((family f).obj ∘ cechEdge f i j) ⟶ ∏ᶜ ((family f).obj ∘ (fun _ => cechEdge f i j k))).left ≫
      (Pi.π ((family f).obj ∘ (fun _ => cechEdge f i j k)) 0).left = _
  rw [← Over.comp_left]
  exact congrArg CommaMorphism.left (Pi.lift_π _ _)

/-- The arrow `cechEdgeLift f i j` followed by the face at `k` is the `k`-th cone projection of
the fibre product followed by the corresponding vertex section. -/
private theorem cechEdgeLift_comp_face (i j : ι) (k : Fin 2) :
    cechEdgeLift f i j ≫ (cechEdgeFace f i j k).hom.left =
      (cechEdgeCone f i j k).left ≫ cechVertexSection f (cechEdge f i j k) := by
  change (Pi.lift (cechEdgeCone f i j) ≫
      (Pi.lift (fun _ => Pi.π ((family f).obj ∘ cechEdge f i j) k) :
    ∏ᶜ ((family f).obj ∘ cechEdge f i j) ⟶
      ∏ᶜ ((family f).obj ∘ cechVertex f (cechEdge f i j k)))).left =
    (cechEdgeCone f i j k ≫
      (Pi.lift (fun _ => 𝟙 ((family f).obj (cechEdge f i j k))) :
        (family f).obj (cechEdge f i j k) ⟶
          ∏ᶜ ((family f).obj ∘ cechVertex f (cechEdge f i j k))) :
      Over.mk (pullback.fst (f i) (f j) ≫ f i) ⟶ _).left
  congr 1
  refine Pi.hom_ext _ _ fun x => ?_
  rw [Category.assoc, Category.assoc, Pi.lift_π, Pi.lift_π, Pi.lift_π]
  exact (Category.comp_id _).symm

/-- The arrow `cechEdgeLift f i j` followed by the face at `0` is the first projection of the
fibre product followed by the section `cechVertexSection f i`. -/
theorem cechEdgeLift_comp_face_zero (i j : ι) :
    cechEdgeLift f i j ≫ (cechEdgeFace f i j 0).hom.left =
      pullback.fst (f i) (f j) ≫ cechVertexSection f i :=
  cechEdgeLift_comp_face f i j 0

/-- The arrow `cechEdgeLift f i j` followed by the face at `1` is the second projection of the
fibre product followed by the section `cechVertexSection f j`. -/
theorem cechEdgeLift_comp_face_one (i j : ι) :
    cechEdgeLift f i j ≫ (cechEdgeFace f i j 1).hom.left =
      pullback.snd (f i) (f j) ≫ cechVertexSection f j :=
  cechEdgeLift_comp_face f i j 1

end AlgebraicGeometry.RingedSite.CoveringGlueing

end
