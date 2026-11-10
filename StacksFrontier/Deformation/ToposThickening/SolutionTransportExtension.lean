module

public import StacksFrontier.Deformation.ToposThickening.SolutionIsomorphism

/-!
# Transporting a solution along an isomorphism of its middle term

For the square-zero extension problem of [Stacks Project, Tag 08UF], a solution `𝒪'` and an
isomorphism of sheaves of rings `φ : 𝒪' ≅ 𝒜` make `𝒜` a solution — the reduction, the map from the
thickened base and the inclusion of the prescribed module composed with `φ` — isomorphic to `𝒪'`
through `φ`. This lets a solution be read on any sheaf of rings identified with its middle term,
for instance on `i⁻¹𝒪_{X'}` for a first order thickening `i : X ⟶ X'`.

## Main definitions
* `...CompatibleFirstOrderThickening.transportExtension`: the transported solution.

## Main results
* `...CompatibleFirstOrderThickening.isomorphic_transportExtension`: it is isomorphic to the
  original one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B}

omit [X.J.HasSheafCompose (forget RingCat)]
  [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- For an isomorphism `φ : A ≅ A'` of sheaves of commutative rings, `φ.hom` undoes `φ.inv` on
sections over each object `U`. -/
theorem sheaf_iso_hom_inv_app {A A' : Sheaf X.J CommRingCat.{w}} (φ : A ≅ A') (U : X.Cᵒᵖ)
    (a : A'.obj.obj U) : φ.hom.hom.app U (φ.inv.hom.app U a) = a :=
  congrArg (fun k : A' ⟶ A' => k.hom.app U a) φ.inv_hom_id

omit [X.J.HasSheafCompose (forget RingCat)]
  [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- For an isomorphism `φ : A ≅ A'` of sheaves of commutative rings, `φ.inv` undoes `φ.hom` on
sections over each object `U`. -/
theorem sheaf_iso_inv_hom_app {A A' : Sheaf X.J CommRingCat.{w}} (φ : A ≅ A') (U : X.Cᵒᵖ)
    (a : A.obj.obj U) : φ.inv.hom.app U (φ.hom.hom.app U a) = a :=
  congrArg (fun k : A ⟶ A => k.hom.app U a) φ.hom_inv_id

variable (P : S.CompatibleFirstOrderThickening) {A : Sheaf X.J CommRingCat.{w}}
  (φ : P.extension ≅ A)

/-- **A solution read on a sheaf of rings isomorphic to its middle term.** -/
def transportExtension : S.CompatibleFirstOrderThickening where
  extension := A
  reduction := φ.inv ≫ P.reduction
  locallySurjective := by
    have := P.locallySurjective
    have : IsIso φ.inv.hom := (inferInstance : IsIso ((sheafToPresheaf X.J _).map φ.inv))
    exact Presheaf.isLocallySurjective_comp X.J _ _
  squareZero U := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun x hx y hy => (Ideal.mem_bot).2 ?_
    have hx' : φ.inv.hom.app U x ∈ RingHom.ker (P.reduction.hom.app U).hom := hx
    have hy' : φ.inv.hom.app U y ∈ RingHom.ker (P.reduction.hom.app U).hom := hy
    have h0 : φ.inv.hom.app U x * φ.inv.hom.app U y = 0 := by
      have := Ideal.mul_mem_mul hx' hy'
      rw [← pow_two, P.squareZero U] at this
      exact (Ideal.mem_bot).1 this
    rw [← sheaf_iso_hom_inv_app φ U (x * y), map_mul, h0, map_zero]
  baseMap := P.baseMap ≫ φ.hom
  baseMap_reduction := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, P.baseMap_reduction]
  kernelInclusion :=
    { val :=
      { app := fun U => ModuleCat.ofHom
          (X := ((SheafOfModules.restrictScalars
            ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
              (φ.inv ≫ P.reduction))).obj S.G).val.obj U)
          (Y := (SheafOfModules.unit ((sheafCompose X.J
            (forget₂ CommRingCat.{w} RingCat.{w})).obj A)).val.obj U)
          { toFun := fun m => φ.hom.hom.app U (P.incl (show S.G.val.obj U from m))
            map_add' := fun m n =>
              (congrArg (φ.hom.hom.app U) (P.incl_add (U := U) m n)).trans (map_add _ _ _)
            map_smul' := fun a m => by
              have h1 := P.mul_incl (φ.inv.hom.app U (show A.obj.obj U from a))
                (show S.G.val.obj U from m)
              have h2 : φ.hom.hom.app U (φ.inv.hom.app U (show A.obj.obj U from a) *
                  P.incl (show S.G.val.obj U from m)) =
                  (show A.obj.obj U from a) *
                    φ.hom.hom.app U (P.incl (show S.G.val.obj U from m)) := by
                rw [map_mul]
                exact congrArg (· * _) (sheaf_iso_hom_inv_app φ U _)
              exact (congrArg (φ.hom.hom.app U) h1.symm).trans h2 }
        naturality := fun {U V} h => by
          ext m
          exact (congrArg (φ.hom.hom.app V) (P.incl_naturality h m)).trans
            (ConcreteCategory.congr_hom (φ.hom.hom.naturality h) _) } }
  kernelZero U m := by
    change P.reduction.hom.app U (φ.inv.hom.app U (φ.hom.hom.app U (P.incl m))) = 0
    rw [sheaf_iso_inv_hom_app]
    exact P.reduction_incl m
  kernelUniversal U a ha := by
    obtain ⟨g, hg, hu⟩ := P.kernelUniversal U (φ.inv.hom.app U a) ha
    refine ⟨g, ?_, fun g' hg' => hu g' ?_⟩
    · change φ.hom.hom.app U (P.incl g) = a
      have hg1 : P.incl g = φ.inv.hom.app U a := hg
      rw [hg1, sheaf_iso_hom_inv_app]
    · have hg2 : φ.hom.hom.app U (P.incl g') = a := hg'
      change P.incl g' = φ.inv.hom.app U a
      rw [← hg2, sheaf_iso_inv_hom_app]
  baseMap_ideal U a := by
    exact congrArg (φ.hom.hom.app U) (P.baseMap_ideal U a)

/-- **The transported solution is isomorphic to the original one**, through `φ`. -/
theorem isomorphic_transportExtension : Isomorphic P (P.transportExtension φ) :=
  ⟨{ hom := φ
     reduction_comm := Iso.hom_inv_id_assoc φ P.reduction
     baseMap_comm := rfl
     kernel_comm := fun _ _ => rfl }⟩

end Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening

end
