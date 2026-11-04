module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.TwistingInput
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseTwoCore
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseTwoRepresenting
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerTransition

/-!
# Clause (2) of Stacks Tag 01O9

Toward clause (2) of [Stacks, Tag 01O9]: on an open `W` of `X` where the degree-`k`
component of `ψ` is surjective, the quadruple `(k, f|_W, ℒ^{⊗ k}|_W, ψ)` of Section 01NS, and its
classifying morphism read on the part of `W` over an affine open of the base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace Twisting

variable {S T : Scheme.{u}} {A : SheafOfModules.GradedAlgebra.{u, u}
    (structureRingSheaf S.toRingedSpace)} {f : T ⟶ S} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- Surjectivity of a component of a twisting does not depend on how the degree is written. -/
theorem epi_app_congr (χ : Twisting f A d L) {m n : ℤ} (h : m = n) [Epi (χ.app m)] :
    Epi (χ.app n) := by
  subst h
  infer_instance

end Twisting

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : Twisting f (situationAlgebra A) 1 L)

/-- **The quadruple `(k, f|_W, ℒ^{⊗ k}|_W, ψ|_{𝒜^{(k)}})` of Section 01NS** attached to an open
`W` of `X` on which the degree-`k` component `ψ_k : f^*𝒜_k|_W ⟶ ℒ^{⊗ k}|_W` is surjective. -/
def restrictQuadruple (W : T.Opens) (k : ℕ) [hW : Epi ((ψ.pullback W.ι).app (k : ℤ))] :
    Quadruple (W.ι ≫ f) (situationAlgebra A) (k : ℤ) where
  L := powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ)
  isInvertible := isInvertible_piece _ (k : ℤ)
  twisting :=
    letI := isInvertible_piece ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ)
    ((ψ.pullback W.ι).scale (k : ℤ)).congrDegree (mul_one (k : ℤ))
  epi_app_one := by
    let := isInvertible_piece ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ)
    have : Epi ((ψ.pullback W.ι).app (1 * (k : ℤ))) :=
      Twisting.epi_app_congr (ψ.pullback W.ι) (one_mul (k : ℤ)).symm
    change Epi ((pullbackFunctor (ringedSpaceHom (W.ι ≫ f))).map _ ≫
      ((pullbackFunctor (ringedSpaceHom (W.ι ≫ f))).map _ ≫
        (ψ.pullback W.ι).app (1 * (k : ℤ)) ≫ (powPowIso _ (k : ℤ) 1).hom))
    infer_instance

/-! ### The chart-wise class over an affine open of the base -/

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- A quadruple read over an equal base morphism has the same class. -/
theorem Fd_mk_congrBaseStrict {Y : Scheme.{u}} {g g' : Y ⟶ S} (h : g = g') {d : ℤ}
    (Q : Quadruple g (situationAlgebra A) d) :
    Fd.mk g' (Quadruple.congrBaseStrict h Q) = Fd.mk g Q := by
  subst h
  rfl

variable {W : T.Opens} {k : ℕ} (hk : 0 < k) [Epi ((ψ.pullback W.ι).app (k : ℤ))]
  (V : S.affineOpens)

/-- The part of `W` over the affine open `V` of the base. -/
abbrev partOver (V : S.affineOpens) : W.toScheme.Opens := (W.ι ≫ f) ⁻¹ᵁ (V.1 : S.Opens)

/-- The inclusion of `partOver V` followed by `W.ι ≫ f` equals the restriction of `W.ι ≫ f` to
`V` followed by the inclusion of `V`. -/
theorem partOver_comp (V : S.affineOpens) :
    (partOver (W := W) (f := f) V).ι ≫ W.ι ≫ f
      = ((W.ι ≫ f) ∣_ (V.1 : S.Opens)) ≫ (V.1 : S.Opens).ι :=
  (morphismRestrict_ι _ _).symm

/-- **The quadruple of clause (2) over the part of `W` lying over an affine open `V`**, read over
the factorization through `V`. -/
def partQuadruple :
    Quadruple (((W.ι ≫ f) ∣_ (V.1 : S.Opens)) ≫ (V.1 : S.Opens).ι) (situationAlgebra A) (k : ℤ) :=
  Quadruple.congrBaseStrict (partOver_comp V)
    ((restrictQuadruple ψ W k).pullback (partOver (W := W) (f := f) V).ι)

/-- **The chart-wise class** of the quadruple of clause (2) over `V`: a point of `F_k` for
`𝒜|_V`. -/
def partClass : Fd (situationAlgebra (A.restrict (V.1 : S.Opens).ι)) (k : ℤ)
    (partOver (W := W) (f := f) V).toScheme :=
  Fd.chartClass A (V.1 : S.Opens) ((W.ι ≫ f) ∣_ (V.1 : S.Opens))
    (Quotient.mk _ (partQuadruple ψ V))

/-- Read back from the chart over `V`, the chart-wise class `partClass ψ V` is the pullback to
`partOver V` of the class of `restrictQuadruple ψ W k`. -/
theorem chartClassInv_partClass :
    Fd.chartClassInv A (V.1 : S.Opens) (partClass ψ V)
      = Fd.pullback (partOver (W := W) (f := f) V).ι (Fd.mk (W.ι ≫ f) (restrictQuadruple ψ W k)) :=
  (Fd.chartClassInv_chartClass A (V.1 : S.Opens) _ _).trans
    (Fd_mk_congrBaseStrict (partOver_comp V) _)

/-- **The morphism of clause (2), over an affine open `V` of the base**, is Tag 01NU's chart-wise
morphism of the chart-wise class, read into `Proj_S(𝒜)` through the chart. -/
theorem partOver_ι_classifyingMorphism :
    (partOver (W := W) (f := f) V).ι ≫ F.classifyingMorphism A
        (F.mk (W.ι ≫ f) (by exact_mod_cast hk) (restrictQuadruple ψ W k))
      = toProj (A.grading (V.1 : S.Opens))
          (Fd.chartEquiv A (V.1 : S.Opens) V.2 hk _ (partClass ψ V))
        ≫ (relativeProj A).chart (V.1 : S.Opens) V.2 := by
  rw [F.classifyingMorphism_mk A hk]
  have h1 : (partOver (W := W) (f := f) V).ι ≫
        Fd.homDegreeOpen A (relativeProj A) hk (Fd.mk (W.ι ≫ f) (restrictQuadruple ψ W k)) ≫
          ((relativeProj A).degreeOpen k).ι
      = toProj (A.grading (V.1 : S.Opens))
          (Fd.chartEquiv A (V.1 : S.Opens) V.2 hk _ (partClass ψ V))
        ≫ (relativeProj A).chart (V.1 : S.Opens) V.2 :=
    (Fd.ι_homDegreeOpen A (relativeProj A) hk (Fd.mk (W.ι ≫ f) (restrictQuadruple ψ W k))
      (V.1 : S.Opens) V.2 (partClass ψ V) (chartClassInv_partClass ψ V)).trans
      (Fd.chartHom_eq_toProj_comp_chart A (V.1 : S.Opens) (relativeProj A) V.2 hk _ _)
  calc (partOver (W := W) (f := f) V).ι ≫
        Fd.homDegreeOpen A (relativeProj A) hk (Fd.mk (W.ι ≫ f) (restrictQuadruple ψ W k)) ≫
          ((relativeProj A).degreeOpen k).ι ≫ (canonicalIso A (relativeProj A)).inv
      = ((partOver (W := W) (f := f) V).ι ≫
          Fd.homDegreeOpen A (relativeProj A) hk (Fd.mk (W.ι ≫ f) (restrictQuadruple ψ W k)) ≫
            ((relativeProj A).degreeOpen k).ι) ≫ (canonicalIso A (relativeProj A)).inv := by
        simp only [Category.assoc]
    _ = _ := by
        rw [h1, Category.assoc]
        congr 1
        exact (Iso.comp_inv_eq _).mpr (chart_comp_canonicalIso_hom A (relativeProj A) V).symm

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
