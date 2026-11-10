module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDesc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConePushout

/-!
# A morphism out of a cone is its two coordinates

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of differential graded `R`-algebras and
let `f : K ⟶ L` be a morphism of right differential graded `A`-modules.
`SheafOfModules.DifferentialGradedModule.ConePackage.desc` builds a morphism `C(f) ⟶ N` out of a
morphism `β : L ⟶ N` and a right `A`-linear degreewise family `α n : K^{n+1} ⟶ N^n` which is a
null-homotopy of `f ≫ β`. **This file shows that every morphism out of the cone arises that way,
from exactly one such pair.** The two coordinates of a morphism `h : C(f) ⟶ N` are `β = ι ≫ h`
and the composite of `h` with the section of the cone's projection; `desc` of those two
coordinates is `h` again, and the coordinates of a `desc` are the pair it was built from.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ConePackage.homotopyOfHom` is the degreewise family
  `α n : K^{n+1} ⟶ N^n` a morphism out of the cone restricts to: the identification of `K[1]^n`
  with `K^{n+1}`, the section `K[1]^n ⟶ C(f)^n` of the cone's projection, and the morphism.

## Main results

* `SheafOfModules.DifferentialGradedModule.ShiftPackage.xIso_d`: **the differential of a chosen
  degree-one shift is minus the differential of the module**, read through the identification of
  the pieces. The sign is the one Mathlib's `CochainComplex.shiftFunctor` carries.
* `SheafOfModules.DifferentialGradedModule.ConePackage.homotopyOfHom_mul` and
  `ConePackage.homotopyOfHom_delta`: the family a morphism restricts to satisfies the two
  hypotheses of `ConePackage.desc` — it is right `A`-linear in the degree-shifted form, and it is
  a null-homotopy of `f ≫ ι ≫ h`.
* `SheafOfModules.DifferentialGradedModule.ConePackage.homotopyOfHom_desc`: **the family read off
  a `desc` is the family it was built from.**
* `SheafOfModules.DifferentialGradedModule.ConePackage.desc_homotopyOfHom`: **a morphism out of
  the cone is the `desc` of its two coordinates.**

## Implementation notes

Nothing here descends to the mapping-cone complex. Both round trips are proved from the data
recorded by a cone package through four identities of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeAdmissible.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConePushout.lean`:
`ConePackage.coneSectionX_action`, which says the section of the projection commutes with the
right action; `ConePackage.coneSectionX_d`, which computes the section composed with the cone's
differential; `ConePackage.coneRetractionX_inclusion_add`, which decomposes the identity of the
cone into its two coordinates; and `ConePackage.projection_f`, which reads the projection through
the degreewise splitting. In particular `ConePackage.desc_homotopyOfHom` is a computation with
morphisms in which no section of a sheaf appears.

The one place a sign enters is `ConePackage.homotopyOfHom_delta`, through `ShiftPackage.xIso_d`:
the differential of the chosen shift `K[1]` is `-d_K`, so the term the section of the projection
contributes to `α n ≫ d_N` is `-(d_K ≫ α (n + 1))`, and moving it across the equality produces
the `+` of the cocycle condition `α n ≫ d + d ≫ α (n + 1) = f ≫ β` that `ConePackage.desc`
asks for.

The base is an arbitrary sheaf of rings on an arbitrary site, with the universes of the site, the
ring, the algebra components and the module components independent, as in the neighbouring
differential graded files.

## References

* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {K L N : DifferentialGradedModule.{t, a, m} A}

/-! ### Evaluating an isomorphism of sheaves of modules on sections -/

/-- An isomorphism of sheaves of modules and its inverse cancel on local sections. -/
theorem iso_inv_hom_val_app {X Y : SheafOfModules.{m} R} (e : X ≅ Y) (U : Cᵒᵖ)
    (x : X.val.obj U) : e.inv.val.app U (e.hom.val.app U x) = x :=
  (comp_val_app e.hom e.inv U x).symm.trans (by rw [e.hom_inv_id]; rfl)

/-- An isomorphism of sheaves of modules and its inverse cancel on local sections, in the other
order. -/
theorem iso_hom_inv_val_app {X Y : SheafOfModules.{m} R} (e : X ≅ Y) (U : Cᵒᵖ)
    (y : Y.val.obj U) : e.hom.val.app U (e.inv.val.app U y) = y :=
  iso_inv_hom_val_app e.symm U y

/-! ### The differential of a chosen degree-one shift -/

namespace ShiftPackage

/-- **The differential of a chosen degree-one shift of `K` is minus the differential of `K`**,
read through the identification `ShiftPackage.xIso` of the pieces. The sign is the one Mathlib's
`CochainComplex.shiftFunctor` puts on the differential of a shift. -/
theorem xIso_d (S : ShiftPackage K) (n : ℤ) :
    (S.xIso n).inv ≫ S.shifted.complex.d n (n + 1) ≫ (S.xIso (n + 1)).hom =
      -K.complex.d (n + 1) ((n + 1) + 1) := by
  obtain ⟨⟨cplx, mul, hassoc, hone, hleib⟩, hc, ha⟩ := S
  dsimp only at hc ⊢
  subst hc
  simp only [xIso, eqToHom_refl, HomologicalComplex.id_f, Category.comp_id]
  change (1 : ℤ).negOnePow • K.complex.d (n + 1) ((n + 1) + 1) = _
  rw [Int.negOnePow_one]
  simp

end ShiftPackage

namespace ConePackage

variable {f : K ⟶ L}

/-! ### The family a morphism out of the cone restricts to -/

/-- **The degreewise family `α n : K^{n+1} ⟶ N^n` a morphism out of the cone of `f` restricts
to**: the identification of the degree-`n` piece of the chosen shift `K[1]` with `K^{n+1}`, the
section `K[1]^n ⟶ C(f)^n` of the cone's projection, and the morphism. -/
def homotopyOfHom (P : ConePackage f) (h : P.cone ⟶ N) (n : ℤ) :
    K.complex.X (n + 1) ⟶ N.complex.X n :=
  ((shiftPackage K).xIso n).inv ≫ P.coneSectionX n ≫ h.toHomologicalComplex.f n

/-- The section of the cone's projection, followed by the morphism, read through the family the
morphism restricts to. -/
theorem coneSectionX_comp_hom (P : ConePackage f) (h : P.cone ⟶ N) (n : ℤ) :
    ((shiftPackage K).xIso n).hom ≫ P.homotopyOfHom h n =
      P.coneSectionX n ≫ h.toHomologicalComplex.f n := by
  rw [homotopyOfHom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The family a morphism restricts to, on local sections. -/
theorem homotopyOfHom_val_app (P : ConePackage f) (h : P.cone ⟶ N) (n : ℤ) (U : Cᵒᵖ)
    (w : (K.complex.X (n + 1)).val.obj U) :
    (P.homotopyOfHom h n).val.app U w =
      (h.toHomologicalComplex.f n).val.app U
        ((P.coneSectionX n).val.app U ((((shiftPackage K).xIso n).inv).val.app U w)) := by
  rw [homotopyOfHom, comp_val_app, comp_val_app]

/-- **The family a morphism out of the cone restricts to is natural in the target**: postcomposing
the morphism postcomposes the family. -/
theorem homotopyOfHom_comp (P : ConePackage f) {N' : DifferentialGradedModule.{t, a, m} A}
    (h : P.cone ⟶ N) (k : N ⟶ N') (n : ℤ) :
    P.homotopyOfHom (h ≫ k) n =
      P.homotopyOfHom h n ≫ k.toHomologicalComplex.f n := by
  rw [homotopyOfHom, homotopyOfHom, comp_f]
  simp only [Category.assoc]

/-- **The family a morphism out of the cone restricts to is right `A`-linear**, in the
degree-shifted form `ConePackage.desc` consumes. -/
theorem homotopyOfHom_mul (P : ConePackage f) (h : P.cone ⟶ N) (n i : ℤ) (U : Cᵒᵖ)
    (x : (K.complex.X (n + 1)).val.obj U) (y : (A.complex.X i).val.obj U) :
    (P.homotopyOfHom h (n + i)).val.app U
        (gradedCast (fun q ↦ (K.complex.X q).val.obj U) (add_right_comm n 1 i)
          ((K.mul (n + 1) i).app U x y)) =
      (N.mul n i).app U ((P.homotopyOfHom h n).val.app U x) y := by
  have hshift : (((shiftPackage K).xIso (n + i)).inv).val.app U
      (gradedCast (fun q ↦ (K.complex.X q).val.obj U) (add_right_comm n 1 i)
        ((K.mul (n + 1) i).app U x y)) =
      ((shift K).mul n i).app U ((((shiftPackage K).xIso n).inv).val.app U x) y := by
    refine Eq.trans (congrArg (fun w => (((shiftPackage K).xIso (n + i)).inv).val.app U w) ?_)
      (iso_inv_hom_val_app ((shiftPackage K).xIso (n + i)) U _)
    refine Eq.trans ?_ ((shiftPackage K).xIso_mul n i U
      ((((shiftPackage K).xIso n).inv).val.app U x) y).symm
    rw [iso_hom_inv_val_app ((shiftPackage K).xIso n) U x, castHom_apply]
  rw [homotopyOfHom_val_app, homotopyOfHom_val_app, hshift,
    P.coneSectionX_action n i U ((((shiftPackage K).xIso n).inv).val.app U x) y, h.map_mul]

/-- **The family a morphism out of the cone restricts to is a null-homotopy of `f ≫ ι ≫ h`**,
which is the cocycle condition `ConePackage.desc` consumes. -/
theorem homotopyOfHom_delta (P : ConePackage f) (h : P.cone ⟶ N) (n : ℤ) :
    P.homotopyOfHom h n ≫ N.complex.d n (n + 1)
        + K.complex.d (n + 1) ((n + 1) + 1) ≫ P.homotopyOfHom h (n + 1)
      = f.toHomologicalComplex.f (n + 1) ≫
          (P.inclusion ≫ h).toHomologicalComplex.f (n + 1) := by
  have key : P.homotopyOfHom h n ≫ N.complex.d n (n + 1) =
      f.toHomologicalComplex.f (n + 1) ≫
          (P.inclusion ≫ h).toHomologicalComplex.f (n + 1)
        + (-K.complex.d (n + 1) ((n + 1) + 1)) ≫ P.homotopyOfHom h (n + 1) :=
    calc P.homotopyOfHom h n ≫ N.complex.d n (n + 1)
        = ((shiftPackage K).xIso n).inv ≫ P.coneSectionX n ≫
            h.toHomologicalComplex.f n ≫ N.complex.d n (n + 1) := by
          rw [homotopyOfHom, Category.assoc, Category.assoc]
      _ = ((shiftPackage K).xIso n).inv ≫ (P.coneSectionX n ≫
            P.cone.complex.d n (n + 1)) ≫ h.toHomologicalComplex.f (n + 1) := by
          rw [h.toHomologicalComplex.comm n (n + 1), Category.assoc]
      _ = ((shiftPackage K).xIso n).inv ≫
            ((((shiftPackage K).xIso n).hom ≫ f.toHomologicalComplex.f (n + 1)) ≫
                P.inclusion.toHomologicalComplex.f (n + 1)
              + (shift K).complex.d n (n + 1) ≫ P.coneSectionX (n + 1)) ≫
              h.toHomologicalComplex.f (n + 1) := by
          rw [P.coneSectionX_d n]
      _ = (((shiftPackage K).xIso n).inv ≫ ((shiftPackage K).xIso n).hom) ≫
              f.toHomologicalComplex.f (n + 1) ≫
                P.inclusion.toHomologicalComplex.f (n + 1) ≫
                  h.toHomologicalComplex.f (n + 1)
            + (((shiftPackage K).xIso n).inv ≫ (shift K).complex.d n (n + 1) ≫
                ((shiftPackage K).xIso (n + 1)).hom) ≫ P.homotopyOfHom h (n + 1) := by
          rw [Preadditive.add_comp, Preadditive.comp_add]
          simp only [Category.assoc]
          rw [P.coneSectionX_comp_hom h (n + 1)]
      _ = f.toHomologicalComplex.f (n + 1) ≫
              (P.inclusion ≫ h).toHomologicalComplex.f (n + 1)
            + (-K.complex.d (n + 1) ((n + 1) + 1)) ≫ P.homotopyOfHom h (n + 1) := by
          rw [Iso.inv_hom_id, Category.id_comp, (shiftPackage K).xIso_d n, comp_f]
  rw [key, Preadditive.neg_comp]
  abel

/-! ### The two round trips -/

/-- **`ConePackage.desc` depends only on its two coordinates**: the two hypotheses it carries are
propositions, so equal coordinates give equal morphisms. -/
theorem desc_congr (P : ConePackage f) {β β' : L ⟶ N}
    {α α' : ∀ n : ℤ, K.complex.X (n + 1) ⟶ N.complex.X n} (hβ : β = β') (hαα : α = α')
    (hα : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
        (y : (A.complex.X i).val.obj U),
      (α (n + i)).val.app U (gradedCast (fun q ↦ (K.complex.X q).val.obj U)
          (add_right_comm n 1 i) ((K.mul (n + 1) i).app U x y))
        = (N.mul n i).app U ((α n).val.app U x) y)
    (hδ : ∀ n : ℤ, α n ≫ N.complex.d n (n + 1)
        + K.complex.d (n + 1) ((n + 1) + 1) ≫ α (n + 1)
        = f.toHomologicalComplex.f (n + 1) ≫ β.toHomologicalComplex.f (n + 1))
    (hα' : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
        (y : (A.complex.X i).val.obj U),
      (α' (n + i)).val.app U (gradedCast (fun q ↦ (K.complex.X q).val.obj U)
          (add_right_comm n 1 i) ((K.mul (n + 1) i).app U x y))
        = (N.mul n i).app U ((α' n).val.app U x) y)
    (hδ' : ∀ n : ℤ, α' n ≫ N.complex.d n (n + 1)
        + K.complex.d (n + 1) ((n + 1) + 1) ≫ α' (n + 1)
        = f.toHomologicalComplex.f (n + 1) ≫ β'.toHomologicalComplex.f (n + 1)) :
    P.desc β α hα hδ = P.desc β' α' hα' hδ' := by
  subst hβ
  subst hαα
  rfl

variable (P : ConePackage f) (β : L ⟶ N) (α : ∀ n : ℤ, K.complex.X (n + 1) ⟶ N.complex.X n)
  (hα : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
      (y : (A.complex.X i).val.obj U),
    (α (n + i)).val.app U (gradedCast (fun q ↦ (K.complex.X q).val.obj U)
        (add_right_comm n 1 i) ((K.mul (n + 1) i).app U x y))
      = (N.mul n i).app U ((α n).val.app U x) y)
  (hδ : ∀ n : ℤ, α n ≫ N.complex.d n (n + 1)
      + K.complex.d (n + 1) ((n + 1) + 1) ≫ α (n + 1)
      = f.toHomologicalComplex.f (n + 1) ≫ β.toHomologicalComplex.f (n + 1))

/-- **The family read off `ConePackage.desc` is the family it was built from.** -/
theorem homotopyOfHom_desc (n : ℤ) : P.homotopyOfHom (P.desc β α hα hδ) n = α n := by
  rw [homotopyOfHom, desc_f, coneSectionX]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, biprod.inl_desc]

/-- **A morphism out of the cone of `f` is the `ConePackage.desc` of its two coordinates**: the
composite of the cone's inclusion with it, and the family it restricts to. -/
theorem desc_homotopyOfHom (h : P.cone ⟶ N) :
    P.desc (P.inclusion ≫ h) (P.homotopyOfHom h) (P.homotopyOfHom_mul h)
        (P.homotopyOfHom_delta h) = h :=
  Hom.ext fun n =>
    calc (P.desc (P.inclusion ≫ h) (P.homotopyOfHom h) (P.homotopyOfHom_mul h)
              (P.homotopyOfHom_delta h)).toHomologicalComplex.f n
        = (P.componentIso n).hom ≫
            biprod.desc (P.homotopyOfHom h n)
              ((P.inclusion ≫ h).toHomologicalComplex.f n) := desc_f _ _ _ _ _ n
      _ = ((P.componentIso n).hom ≫ biprod.fst) ≫ P.homotopyOfHom h n
            + ((P.componentIso n).hom ≫ biprod.snd) ≫
              (P.inclusion ≫ h).toHomologicalComplex.f n := by
          rw [biprod.desc_eq, Preadditive.comp_add, Category.assoc, Category.assoc]
      _ = P.projection.toHomologicalComplex.f n ≫ P.coneSectionX n ≫
              h.toHomologicalComplex.f n
            + P.coneRetractionX n ≫ P.inclusion.toHomologicalComplex.f n ≫
              h.toHomologicalComplex.f n := by
          rw [← P.projection_f n, Category.assoc, P.coneSectionX_comp_hom h n,
            show (P.componentIso n).hom ≫ biprod.snd = P.coneRetractionX n from rfl,
            comp_f]
      _ = (P.coneRetractionX n ≫ P.inclusion.toHomologicalComplex.f n
            + P.projection.toHomologicalComplex.f n ≫ P.coneSectionX n) ≫
              h.toHomologicalComplex.f n := by
          rw [Preadditive.add_comp]
          simp only [Category.assoc]
          abel
      _ = h.toHomologicalComplex.f n := by
          rw [P.coneRetractionX_inclusion_add n, Category.id_comp]

end ConePackage

end SheafOfModules.DifferentialGradedModule

end
