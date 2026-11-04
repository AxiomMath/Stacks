module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechBaseForms

/-!
# The pull-back of de Rham cohomology on classes of closed forms of an affine base

Let `f : X ⟶ Y` be smooth with `Y` and `S` affine, `A = Γ(Y, 𝒪_Y)` and `R = Γ(S, 𝒪_S)`, and let
`U` be a finite open covering of `X` with affine intersections. Fact (3) of the proof of
[Stacks, Tag 0FUM]: the map `Ω^•_{A/R} ⟶ Tot(Č(U, Ω^•_{X/S}))` sending a form to the cochain of
its pull-backs to the intersections induces the pull-back `f^* : H^*_{dR}(Y/S) ⟶ H^*_{dR}(X/S)`.

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.deRhamPullbackModule_affineClassMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.Cech.Hypercohomology (cocycleClass toMor)

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

section Theorem

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine Y] [IsAffine S] [Smooth f]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) (hU : ⊤ = ⨆ i, U i)

/-- The form of `Ω^•_{A/R}` underlying a term of degree `b` of its `ℤ`-indexed extension. -/
abbrev intForm (b : ℕ) (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X b) :
    ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g)) :=
  Stacks.KatzOda.Cech.toForms (baseMap g)
    (((Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex (baseMap g)).extendXIso
      ComplexShape.embeddingUpNat rfl).hom.hom ν)

omit [IsAffine Y] [IsAffine S] in
/-- The form underlying a cocycle of the `ℤ`-indexed `Ω^•_{A/R}` is closed. -/
theorem dForms_intForm (b : ℕ) (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X b)
    (hν : ((Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).d b (b + 1)).hom ν = 0) :
    Stacks.KatzOda.dForms (baseMap g) b (intForm g b ν) = 0 := by
  set C := Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex (baseMap g)
  have h2 := (ConcreteCategory.congr_hom (HomologicalComplex.extend_d_eq C
    ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f b = b)
    (show ComplexShape.embeddingUpNat.f (b + 1) = (b : ℤ) + 1 by simp)) ν).symm.trans hν
  have h3 : (C.d b (b + 1)).hom ((C.extendXIso ComplexShape.embeddingUpNat rfl).hom.hom ν) = 0 :=
    (Iso.inv_hom_id_apply (C.extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f (b + 1) = (b : ℤ) + 1 by simp)) _).symm.trans
      ((congrArg (C.extendXIso ComplexShape.embeddingUpNat
          (show ComplexShape.embeddingUpNat.f (b + 1) = (b : ℤ) + 1 by simp)).hom.hom h2).trans
        (map_zero _))
  exact (Stacks.KatzOda.Cech.toForms_d (gR := baseMap g) _).symm.trans
    ((congrArg (Stacks.KatzOda.Cech.toForms (baseMap g)) h3).trans rfl)

/-- The total Čech cochain of the pull-back to `X` of the global form `affineForm g b ν` of `Y` is
the base cochain `baseTot` of the form `intForm g b ν` of `Ω^•_{A/R}`. -/
theorem pullbackGlobalForm_affineForm (b : ℕ)
    (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X b) :
    restrictTot (f ≫ g) U b (pullbackGlobalForm f g b (affineForm g b ν)) =
      baseTot f g U haff b (intForm g b ν) :=
  (baseTot_eq_restrictTot f g U haff b (intForm g b ν)).symm

/-- **The pull-back of de Rham cohomology on the class of a closed form of the base** ([Stacks,
Tag 0FUM], fact (3) of its proof): for `Y` and `S` affine, `A = Γ(Y, 𝒪_Y)`, `R = Γ(S, 𝒪_S)`,
`f^* : H^b_{dR}(Y/S) ⟶ H^b_{dR}(X/S)` sends the class of a closed form `ν` of `Ω^•_{A/R}`
(through `H^b(Ω^•_{A/R}) ≅ H^b_{dR}(Y/S)`, `affineClassMap`) to the Čech class of the cochain
`t ↦ ν|_{U_t}` of the pull-backs of `ν` to the intersections of an affine open covering of `X`. -/
theorem deRhamPullbackModule_affineClassMap (b : ℕ)
    (ν : (Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).X b)
    (hν : ((Stacks.KatzOda.ShiftedSum.intComplex (baseMap g)).d b (b + 1)).hom ν = 0) :
    deRhamPullbackModule f g b
        ((affineClassMap g b).hom ((cocycleClass b (toMor ν) (toMor_comp_d_eq_zero _ hν)).hom 1)) =
      (classMap (f ≫ g) U hU b).hom
        ((cocycleClass b (toMor (baseTot f g U haff b (intForm g b ν)))
          (toMor_comp_d_eq_zero _
            (baseTot_cocycle f g U haff b _ (dForms_intForm g b ν hν)))).hom 1) := by
  rw [affineClassMap_cocycleClass g b ν hν,
    deRhamPullbackModule_classMap_restrictTot f g U hU topCover top_eq_iSup_topCover b _
      (affineForm_closed g b ν hν)]
  exact congrArg (classMap (f ≫ g) U hU b).hom (ConcreteCategory.congr_hom
    (Stacks.Cech.Hypercohomology.cocycleClass_congr b
      (congrArg toMor (pullbackGlobalForm_affineForm f g U haff b ν)) _ _) 1)

end Theorem

end AlgebraicGeometry.DeRhamKatzOdaCech

end
