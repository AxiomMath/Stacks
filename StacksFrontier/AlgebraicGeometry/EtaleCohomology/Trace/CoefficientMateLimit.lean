module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Inverse images commute with a change of coefficients that is a finite limit

Let `u : C ⥤ D` be a continuous functor of sites, so that direct image of sheaves is
precomposition with `u` and has, for each coefficient category, a left adjoint `L` (inverse
image or extension by zero).  A coefficient functor `Γ : A ⥤ B` which preserves the sheaf
condition commutes with direct image on the nose, and the mate of that strict square is a
comparison `L(Γ ∘ c) ⟶ Γ ∘ L(c)`.  Nothing makes it invertible in general: `L` is built from
colimits and `Γ` need not preserve them.

This file proves that it is invertible as soon as `Γ` is, objectwise, a **finite limit** of
coefficient functors whose comparisons are invertible, and `L` is left exact.  For example, the
functor of invariants `M ↦ M^G` of a finite group `G` acting on modules is the limit, over the
one-object category of `G`, of restriction of scalars with `G` acting.

## Main definitions

* `Stacks.EtaleCohomology.sheafComposeCoefficientMate`: the comparison `L ∘ Γ ⟶ Γ ∘ L`, the mate of
  the strict commutation of direct image with `Γ`.

## Main results

* `Stacks.EtaleCohomology.coefficientMate_unit`: `Γ` applied to the unit of `L ⊣ u_*` is the unit
  at the image followed by direct image of the comparison.
* `Stacks.EtaleCohomology.sheafComposeCoefficientMate_naturality`: the comparison is natural in the
  coefficient functor.
* `Stacks.EtaleCohomology.isIso_coefficientMate_of_isLimit`: the comparison of a coefficient
  functor which is objectwise a finite limit of coefficient functors with invertible comparisons
  is invertible, for left exact `L`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace Stacks.EtaleCohomology

variable {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  {A B : Type*} [Category* A] [Category* B]
  {LA : Sheaf J A ⥤ Sheaf K A} {LB : Sheaf J B ⥤ Sheaf K B}
  (adjA : LA ⊣ uf.sheafPushforwardContinuous A J K)
  (adjB : LB ⊣ uf.sheafPushforwardContinuous B J K)

/-- **The comparison `L(Γ ∘ c) ⟶ Γ ∘ L(c)`** of a left adjoint of direct image with a change of
coefficients `Γ`: the mate of the strict commutation `Γ ∘ u_* = u_* ∘ Γ`. -/
def sheafComposeCoefficientMate (Gf : A ⥤ B) [J.HasSheafCompose Gf] [K.HasSheafCompose Gf] :
    TwoSquare (sheafCompose J Gf) LA LB (sheafCompose K Gf) :=
  (mateEquiv adjA adjB).symm (TwoSquare.mk _ _ _ _ (𝟙 _))

/-- `Γ` applied to the unit of `L ⊣ u_*` is the unit at the image followed by direct image of
the comparison. -/
theorem coefficientMate_unit (Gf : A ⥤ B) [J.HasSheafCompose Gf] [K.HasSheafCompose Gf]
    (c : Sheaf J A) :
    (sheafCompose J Gf).map (adjA.unit.app c) =
      adjB.unit.app ((sheafCompose J Gf).obj c) ≫
        (uf.sheafPushforwardContinuous B J K).map
          ((sheafComposeCoefficientMate uf J K adjA adjB Gf).app c) :=
  (Category.comp_id _).symm.trans (unit_mateEquiv_symm adjA adjB
    (TwoSquare.mk (uf.sheafPushforwardContinuous A J K) (sheafCompose K Gf) (sheafCompose J Gf)
      (uf.sheafPushforwardContinuous B J K) (𝟙 _)) c)

/-- **The comparison is natural in the coefficient functor.** -/
theorem sheafComposeCoefficientMate_naturality {Gf Gf' : A ⥤ B} [J.HasSheafCompose Gf]
    [K.HasSheafCompose Gf] [J.HasSheafCompose Gf'] [K.HasSheafCompose Gf'] (τ : Gf ⟶ Gf')
    (c : Sheaf J A) :
    LB.map ((sheafCompose_map J τ).app c) ≫
        (sheafComposeCoefficientMate uf J K adjA adjB Gf').app c =
      (sheafComposeCoefficientMate uf J K adjA adjB Gf).app c ≫
        (sheafCompose_map K τ).app (LA.obj c) := by
  apply (adjB.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [adjB.unit_naturality_assoc, ← coefficientMate_unit, ← Category.assoc,
    ← coefficientMate_unit]
  exact ((sheafCompose_map J τ).naturality (adjA.unit.app c)).symm

section Diagram

variable {I : Type*} [SmallCategory I] {L : GrothendieckTopology C}
  (F : I ⥤ (A ⥤ B)) [∀ i, L.HasSheafCompose (F.obj i)]

/-- The diagram `i ↦ F i ∘ c` of sheaves obtained by composing a sheaf with a diagram of
coefficient functors. -/
@[simps]
def sheafComposeDiagram (c : Sheaf L A) : I ⥤ Sheaf L B where
  obj i := (sheafCompose L (F.obj i)).obj c
  map f := (sheafCompose_map L (F.map f)).app c
  map_id i := by rw [F.map_id]; rfl
  map_comp f g := by rw [F.map_comp]; rfl

variable (Gf : A ⥤ B) [L.HasSheafCompose Gf] (κ : (Functor.const I).obj Gf ⟶ F)

/-- The cone `Γ ∘ c ⟶ F i ∘ c` induced by a cone `Γ ⟶ F i` of coefficient functors. -/
def sheafComposeCone (c : Sheaf L A) : Cone (sheafComposeDiagram F c) where
  pt := (sheafCompose L Gf).obj c
  π :=
    { app i := (sheafCompose_map (F := Gf) (G := F.obj i) L (κ.app i)).app c
      naturality i j f := by
        have h := κ.naturality f
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h
        simp only [Functor.const_obj_obj, Functor.const_obj_map, sheafComposeDiagram_map]
        rw [h]
        exact (Category.id_comp _).trans rfl }

/-- The cone of sheaves is a limit cone when the cone of coefficient functors is a limit cone
at every object. -/
def isLimitSheafComposeCone
    (hκ : ∀ a : A, IsLimit (((evaluation A B).obj a).mapCone ⟨Gf, κ⟩)) (c : Sheaf L A) :
    IsLimit (sheafComposeCone F Gf κ c) :=
  isLimitOfReflects (sheafToPresheaf L B)
    (evaluationJointlyReflectsLimits _ fun U => hκ (c.obj.obj U))

end Diagram

/-- **The comparison of a finite limit of coefficient functors.**  Let `Γ` carry a cone over a
finite diagram `F` of coefficient functors which is a limit cone at every object, and suppose
the comparison of every `F i` is invertible and `L` on `B`-valued sheaves preserves finite
limits.  Then the comparison of `Γ` is invertible. -/
theorem isIso_coefficientMate_of_isLimit {I : Type*} [SmallCategory I] [FinCategory I]
    (F : I ⥤ (A ⥤ B)) (Gf : A ⥤ B) (κ : (Functor.const I).obj Gf ⟶ F)
    (hκ : ∀ a : A, IsLimit (((evaluation A B).obj a).mapCone ⟨Gf, κ⟩))
    [J.HasSheafCompose Gf] [K.HasSheafCompose Gf]
    [∀ i, J.HasSheafCompose (F.obj i)] [∀ i, K.HasSheafCompose (F.obj i)]
    [PreservesFiniteLimits LB]
    (hF : ∀ i, IsIso (sheafComposeCoefficientMate uf J K adjA adjB (F.obj i))) :
    IsIso (sheafComposeCoefficientMate uf J K adjA adjB Gf) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  have hF' : ∀ i, IsIso ((sheafComposeCoefficientMate uf J K adjA adjB (F.obj i)).app c) :=
    fun i => by have := hF i; infer_instance
  have h₁ := isLimitSheafComposeCone (L := K) F Gf κ hκ (LA.obj c)
  have h₂ : IsLimit (LB.mapCone (sheafComposeCone (L := J) F Gf κ c)) :=
    isLimitOfPreserves LB (isLimitSheafComposeCone F Gf κ hκ c)
  let e : sheafComposeDiagram (L := J) F c ⋙ LB ≅ sheafComposeDiagram (L := K) F (LA.obj c) :=
    NatIso.ofComponents
      (fun i => @asIso _ _ _ _
        ((sheafComposeCoefficientMate uf J K adjA adjB (F.obj i)).app c) (hF' i))
      (fun f => sheafComposeCoefficientMate_naturality uf J K adjA adjB (F.map f) c)
  have h₃ := (IsLimit.postcomposeHomEquiv e _).symm h₂
  let φ : (Cone.postcompose e.hom).obj (LB.mapCone (sheafComposeCone F Gf κ c)) ⟶
      sheafComposeCone F Gf κ (LA.obj c) :=
    { hom := (sheafComposeCoefficientMate uf J K adjA adjB Gf).app c
      w i := by
        dsimp [sheafComposeCone, e]
        exact (sheafComposeCoefficientMate_naturality uf J K adjA adjB
          (Gf := Gf) (Gf' := F.obj i) (κ.app i) c).symm }
  have hφ : IsIso φ := IsLimit.hom_isIso h₃ h₁ φ
  exact (Cone.forget _).map_isIso φ

end Stacks.EtaleCohomology

end
