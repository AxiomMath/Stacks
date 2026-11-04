module

public import StacksFrontier.AlgebraicGeometry.TwistExistence.Basis

/-!
# Twist data over a basis: the glued comparison is the only one

Let `𝔅` be a basis of the topology of `S` consisting of affine opens and `D`, `E` two sets of twist
data over `𝔅` on `Proj_S(A)`. The chart comparisons glue to an isomorphism
`glueAlgIso : D.algebra ≅ E.algebra` of sheaves of graded algebras carrying the first
homogeneous-section map to the second. This file proves it is the **only** homomorphism of sheaves
of graded algebras `D.algebra ⟶ E.algebra` doing so.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistExistenceBasis.chartEndo`: a homomorphism of the glued algebras,
  read through the chart identifications over a member of `𝔅`.

## Main results

* `Stacks.AlgebraicGeometry.TwistExistenceBasis.chartEndo_eq_id`: it is the identity.
* `Stacks.AlgebraicGeometry.TwistExistenceBasis.app_eq_glueIso_hom`: **a homomorphism of graded
  algebras carrying the first homogeneous-section map to the second is the glued isomorphism**,
  degree by degree.
* `Stacks.AlgebraicGeometry.TwistExistenceBasis.eq_glueHom`: the same for the homomorphism itself.
* `Stacks.AlgebraicGeometry.TwistExistenceBasis.eq_glueAlgIso`: the same for isomorphisms.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistExistenceBasis

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} {𝔅 : Set S.Opens}
  (D E : BasisTwistData A 𝔅) (f : D.algebra ⟶ E.algebra)

/-! ### The chart endomorphism -/

section Chart

variable (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅)

/-- A homomorphism of the glued algebras of two twist data, read through their chart
identifications over a member of `𝔅`: an endomorphism of the absolute twist. -/
def chartEndo (n : ℤ) :
    twistingSheaf (A.grading U) n ⟶ twistingSheaf (A.grading U) n :=
  (D.chartIso U hU hB n).inv ≫
    (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map (f.app n) ≫
      (E.chartIso U hU hB n).hom

/-- Under the section comparisons of the two data, `chartEndo` becomes the homomorphism. -/
theorem mapSection_chartEndo (n : ℤ) (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (a : (twistingSheaf (A.grading U) n).val.obj (op V)) :
    E.mapSection U hU hB n V ((chartEndo D E f U hU hB n).val.app (op V) a) =
      (f.app n).val.app (op (((relativeProj A).chart U hU) ''ᵁ V))
        (D.mapSection U hU hB n V a) := by
  change (E.chartIso U hU hB n).inv.val.app (op V)
      ((E.chartIso U hU hB n).hom.val.app (op V)
        (((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
            (f.app n)).val.app (op V)
          ((D.chartIso U hU hB n).inv.val.app (op V) a))) =
    ((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
        (f.app n)).val.app (op V)
      ((D.chartIso U hU hB n).inv.val.app (op V) a)
  exact TwistRigidity.iso_inv_app_hom_app (E.chartIso U hU hB n) (op V) _

/-- **The chart endomorphism is multiplicative.** -/
theorem isMultiplicative_chartEndo :
    TwistRigidity.IsMultiplicative (chartEndo D E f U hU hB) := by
  intro i j V a b
  refine E.mapSection_injective U hU hB (i + j) V ?_
  calc E.mapSection U hU hB (i + j) V
          ((chartEndo D E f U hU hB (i + j)).val.app (op V)
            (absoluteTwistProduct (A.grading U) i j V a b))
      = (f.app (i + j)).val.app (op (((relativeProj A).chart U hU) ''ᵁ V))
          (D.mapSection U hU hB (i + j) V
            (absoluteTwistProduct (A.grading U) i j V a b)) :=
        mapSection_chartEndo D E f U hU hB (i + j) V _
    _ = (f.app (i + j)).val.app (op (((relativeProj A).chart U hU) ''ᵁ V))
          ((D.algebra.mul i j).app (op (((relativeProj A).chart U hU) ''ᵁ V))
            (D.mapSection U hU hB i V a) (D.mapSection U hU hB j V b)) :=
        TwistRigidity.app_congr _ _ (D.chartIso_mul U hU hB i j V a b)
    _ = (E.algebra.mul i j).app (op (((relativeProj A).chart U hU) ''ᵁ V))
          ((f.app i).val.app (op (((relativeProj A).chart U hU) ''ᵁ V))
            (D.mapSection U hU hB i V a))
          ((f.app j).val.app (op (((relativeProj A).chart U hU) ''ᵁ V))
            (D.mapSection U hU hB j V b)) :=
        f.map_mul i j (op (((relativeProj A).chart U hU) ''ᵁ V)) _ _
    _ = (E.algebra.mul i j).app (op (((relativeProj A).chart U hU) ''ᵁ V))
          (E.mapSection U hU hB i V ((chartEndo D E f U hU hB i).val.app (op V) a))
          (E.mapSection U hU hB j V ((chartEndo D E f U hU hB j).val.app (op V) b)) :=
        TwistRigidity.mul_app_congr E.algebra i j _
          (mapSection_chartEndo D E f U hU hB i V a).symm
          (mapSection_chartEndo D E f U hU hB j V b).symm
    _ = E.mapSection U hU hB (i + j) V
          (absoluteTwistProduct (A.grading U) i j V
            ((chartEndo D E f U hU hB i).val.app (op V) a)
            ((chartEndo D E f U hU hB j).val.app (op V) b)) :=
        (E.chartIso_mul U hU hB i j V _ _).symm

variable {D E f}

/-- **The chart endomorphism fixes the homogeneous sections**, when the homomorphism carries the
first homogeneous-section map to the second. -/
theorem fixesDegreeSections_chartEndo
    (hf : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (f.app (n : ℤ)) = E.ψ n) :
    TwistRigidity.FixesDegreeSections (chartEndo D E f U hU hB) := by
  intro k c
  obtain ⟨y, hy⟩ := c.2
  have hc : c = ⟨DirectSum.of (A.sectionPieces U) k y, A.of_mem_grading U y⟩ :=
    Subtype.ext hy.symm
  subst hc
  have hfk : (f.app (k : ℤ)).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
      ((D.ψ k).val.app (op U) y) = (E.ψ k).val.app (op U) y :=
    congrArg (fun φ : A.piece (k : ℤ) ⟶
        (Scheme.Modules.pushforward (relativeProj A).toBase).obj (E.algebra.piece (k : ℤ)) =>
      φ.val.app (op U) y) (hf k)
  refine E.mapSection_injective U hU hB (k : ℤ) ⊤ ?_
  calc E.mapSection U hU hB (k : ℤ) ⊤
          ((chartEndo D E f U hU hB (k : ℤ)).val.app (op ⊤)
            (degreeSection (A.grading U) k
              ⟨DirectSum.of (A.sectionPieces U) k y, A.of_mem_grading U y⟩))
      = (f.app (k : ℤ)).val.app (op (((relativeProj A).chart U hU) ''ᵁ ⊤))
          (D.mapSection U hU hB (k : ℤ) ⊤
            (degreeSection (A.grading U) k
              ⟨DirectSum.of (A.sectionPieces U) k y, A.of_mem_grading U y⟩)) :=
        mapSection_chartEndo D E f U hU hB (k : ℤ) ⊤ _
    _ = (f.app (k : ℤ)).val.app (op (((relativeProj A).chart U hU) ''ᵁ ⊤))
          ((RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).symm ▸
            ((D.ψ k).val.app (op U) y)) :=
        TwistRigidity.app_congr _ _ (D.ψ_chart U hU hB k y)
    _ = (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).symm ▸
          ((f.app (k : ℤ)).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
            ((D.ψ k).val.app (op U) y)) :=
        TwistRigidity.app_eq_rec _ _ _
    _ = (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).symm ▸
          ((E.ψ k).val.app (op U) y) := by rw [hfk]
    _ = E.mapSection U hU hB (k : ℤ) ⊤
          (degreeSection (A.grading U) k
            ⟨DirectSum.of (A.sectionPieces U) k y, A.of_mem_grading U y⟩) :=
        (E.ψ_chart U hU hB k y).symm

/-- **The chart endomorphism is the identity.** -/
theorem chartEndo_eq_id
    (hf : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (f.app (n : ℤ)) = E.ψ n) (n : ℤ) :
    chartEndo D E f U hU hB n = 𝟙 (twistingSheaf (A.grading U) n) :=
  TwistRigidity.eq_id (isMultiplicative_chartEndo D E f U hU hB)
    (fixesDegreeSections_chartEndo U hU hB hf) n

/-- **Over the inverse image of a member of `𝔅`, the homomorphism is carried by the chart
identification of `E` to that of `D`.** -/
theorem chartLoc_app (hf : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (f.app (n : ℤ)) = E.ψ n) (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U) (x : (D.algebra.piece n).val.obj (op V)) :
    (chartLoc E U hU hB n).app V hV ((f.app n).val.app (op V) x) =
      (chartLoc D U hU hB n).app V hV x := by
  refine (chartLoc_app_eq E U hU hB n V hV _).trans ?_
  refine Eq.trans ?_ (chartLoc_app_eq D U hU hB n V hV x).symm
  have hnat := PresheafOfModules.naturality_apply (f.app n).val
    (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x
  refine (congrArg ((E.chartIso U hU hB n).hom.val.app
    (op ((relativeProj A).chart U hU ⁻¹ᵁ V))) hnat.symm).trans ?_
  have hid := congrArg (fun φ => φ.val.app (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
      ((D.chartIso U hU hB n).hom.val.app (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
        ((D.algebra.piece n).val.map
          (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x)))
    (chartEndo_eq_id U hU hB hf n)
  refine Eq.trans ?_ hid
  exact congrArg (fun z => (E.chartIso U hU hB n).hom.val.app
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
      ((f.app n).val.app (op (((relativeProj A).chart U hU) ''ᵁ
        ((relativeProj A).chart U hU ⁻¹ᵁ V))) z))
    (TwistRigidity.iso_inv_app_hom_app (D.chartIso U hU hB n)
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) _).symm

end Chart

/-! ### Uniqueness -/

variable (h𝔅 : Opens.IsBasis 𝔅) (h𝔅a : ∀ U ∈ 𝔅, IsAffineOpen U)

variable {D E f}

include h𝔅 in
/-- **A homomorphism of graded algebras carrying the first homogeneous-section map to the second
is the glued isomorphism**, degree by degree. -/
theorem app_eq_glueIso_hom
    (hf : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (f.app (n : ℤ)) = E.ψ n) (n : ℤ) :
    f.app n = (glueIso h𝔅 h𝔅a D E n).hom := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  obtain ⟨V⟩ := V
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (E.algebra.piece n).isSheaf
    (fun m : {m : S.Opens // m ∈ 𝔅} => V ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1)
    (fun m => inf_le_left) ?_ fun m => ?_
  · intro p hp
    obtain ⟨m, hm⟩ := Opens.mem_iSup.mp
      ((iSup_preimage_eq_top h𝔅).ge (show p ∈ (⊤ : (relativeProj A).scheme.Opens) from trivial))
    exact Opens.mem_iSup.mpr ⟨m, hp, hm⟩
  have hle : V ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1 ≤ (relativeProj A).toBase ⁻¹ᵁ m.1 :=
    inf_le_right
  have hm := h𝔅a m.1 m.2
  change (E.algebra.piece n).val.map (homOfLE inf_le_left).op ((f.app n).val.app (op V) x) =
    (E.algebra.piece n).val.map (homOfLE inf_le_left).op
      ((glueIso h𝔅 h𝔅a D E n).hom.val.app (op V) x)
  refine (PresheafOfModules.naturality_apply (f.app n).val (homOfLE inf_le_left).op x).symm.trans ?_
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply (glueIso h𝔅 h𝔅a D E n).hom.val
    (homOfLE inf_le_left).op x)
  refine Eq.trans ?_ (glueIso_hom_app_of_le h𝔅 h𝔅a D E m.1 hm m.2 n _ hle _).symm
  exact (cmp_eq_of_chartLoc_eq D E m.1 hm m.2 n _ hle
    (chartLoc_app m.1 hm m.2 hf n _ hle _)).symm

include h𝔅 in
/-- **The glued isomorphism is the only homomorphism of graded algebras carrying the first
homogeneous-section map to the second.** -/
theorem eq_glueHom
    (hf : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (f.app (n : ℤ)) = E.ψ n) :
    f = (glueAlgIso h𝔅 h𝔅a D E).hom :=
  SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    (app_eq_glueIso_hom h𝔅 h𝔅a hf n).trans (glueAlgIso_hom_app h𝔅 h𝔅a D E n).symm

include h𝔅 in
/-- **The glued isomorphism is the only isomorphism of graded algebras carrying the first
homogeneous-section map to the second.** -/
theorem eq_glueAlgIso {e : D.algebra ≅ E.algebra}
    (he : ∀ n : ℕ, D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (e.hom.app (n : ℤ)) = E.ψ n) :
    e = glueAlgIso h𝔅 h𝔅a D E :=
  Iso.ext (eq_glueHom h𝔅 h𝔅a he)

end Stacks.AlgebraicGeometry.TwistExistenceBasis

end
