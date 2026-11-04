module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleImageSubmoduleAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjDegreeIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuotientFibrePresentation

/-!
# The kernel of `f^*𝒜 ⟶ f^*(𝒜/ℱ𝒜)` on the small étale site of a scheme point

In Situation 0849 let `ℱ ⊆ 𝒜_d` be a submodule and `ℐ = ℱ𝒜` the graded ideal it generates
(`AlgebraicGeometry.Space.RelativeProjSituation.degreeIdeal`).  For a scheme point `f : T ⟶ X`
the pullback `f^*𝒜` is the algebra of Situation 0849 on the represented space of `T`
(`AlgebraicGeometry.Space.RelativeProjSituation.pullback`), and `f^*ℱ` has an image
`𝒢 ⊆ (f^*𝒜)_d`.  This file proves, on the small étale site of `T`, the inclusion of the kernel of
`f^*𝒜_n ⟶ f^*(𝒜/ℱ𝒜)_n` in the graded ideal `𝒢(f^*𝒜)`, the étale half of the kernel clause of
Stacks 085N.

The argument is the source's "right exactness of pullback": `f^*` preserves the cokernel
`ℐ_n ⟶ 𝒜_n ⟶ (𝒜/ℐ)_n`, so it suffices that `f^*ℐ_n ⟶ (f^*𝒜)_n` lands in `𝒢(f^*𝒜)`.  By the
adjunction `f^* ⊣ f_*` of graded algebras (Stacks 0FQX (3)) this is the statement that the adjunct
`𝒜 ⟶ f_*(f^*𝒜/𝒢(f^*𝒜))` of the quotient map kills `ℐ`; it is a homomorphism of graded algebras
killing `ℱ`, so it kills the ideal `ℱ` generates.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.mem_of_quotientMkApp_eq_zero`: a section of `𝒜_n`
  killed by `𝒜 ⟶ 𝒜/ℐ` lies in `ℐ_n`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointImageSubmodule`: the image `𝒢` of `f^*ℱ`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointQuotientAdjunct_app_eq_zero`: the adjunct
  of the quotient map kills `ℱ𝒜`.

## References

* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedAdj)
open Stacks.SheafOfModules.ImageSubsheaf

universe u

namespace AlgebraicGeometry.Space.RelativeProjSituation

/-- The product of the zero section with any section of a sheaf of graded algebras is zero. -/
theorem mul_app_zero_left {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} R) (i j : ℤ) (U : Cᵒᵖ)
    (y : (A.piece j).val.obj U) : (A.mul i j).app U 0 y = 0 := by
  rw [map_zero]
  rfl

/-- For an adjunction between categories with zero morphisms, a morphism `g` composed with the
adjunct of `q` vanishes as soon as `F g ≫ q` does. -/
theorem _root_.CategoryTheory.Adjunction.comp_homEquiv_eq_zero_of_map_comp {C D : Type*}
    [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {A A' : C} {B : D} (g : A' ⟶ A) (q : F.obj A ⟶ B) (h : F.map g ≫ q = 0) :
    g ≫ adj.homEquiv _ _ q = 0 := by
  have := adj.isLeftAdjoint
  have h0 : (adj.homEquiv A' B).symm 0 = 0 := by
    rw [Adjunction.homEquiv_counit, Functor.map_zero, Limits.zero_comp]
  rw [← adj.homEquiv_naturality_left, h, ← h0, Equiv.apply_symm_apply]

/-- **A section of `𝒜_n` killed by the quotient homomorphism `𝒜 ⟶ 𝒜/ℐ` lies in `ℐ_n`.**  The
quotient homomorphism is the sectionwise quotient followed by the sheafification unit, which is
locally injective, and membership in `ℐ_n` is local. -/
theorem mem_of_quotientMkApp_eq_zero (t : RelativeProjSituation.{u, u})
    (ℐ : t.MulStableGradedSubmodule)
    (n : ℤ) (U : (SmallEtale t.site t.base t.containsBase t.space.1)ᵒᵖ)
    (x : (t.algebra.piece n).val.obj U) (h : (t.quotientMkApp ℐ n).val.app U x = 0) :
    x ∈ (ℐ.piece n).obj U := by
  let J := SmallEtale.topology t.site t.base t.containsBase t.space.1
  let φ := Stacks.SheafOfModules.UliftTensor.sheafifyUnit (J := J)
    (R := structureRingSheaf t.site t.base t.containsBase t.space) (t.preQuotPiece ℐ n)
  have : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map φ) :=
    Stacks.SheafOfModules.UliftTensor.isLocallyInjective_sheafifyUnit (J := J)
      (R := structureRingSheaf t.site t.base t.containsBase t.space) (t.preQuotPiece ℐ n)
  have hloc := Presheaf.equalizerSieve_mem J ((PresheafOfModules.toPresheaf _).map φ)
    (X := U) ((t.preQuotProj ℐ n).app U x) 0 (by rw [map_zero]; exact h)
  refine (ℐ.piece n).isSheaf x (J.superset_covering ?_ hloc)
  intro V g hg
  have hg' : (t.preQuotPiece ℐ n).map g.op ((t.preQuotProj ℐ n).app U x) = 0 := by
    simp only at hg
    exact hg.trans (map_zero _)
  rw [← PresheafOfModules.naturality_apply (t.preQuotProj ℐ n) g.op x] at hg'
  exact (t.preQuotProj_app_eq_zero_iff ℐ n _ _).1 hg'

/-- The quotient homomorphism `𝒜 ⟶ 𝒜/ℐ` kills the sections of `ℐ`. -/
theorem ι_app_mem_quotientMkApp_eq_zero (t : RelativeProjSituation.{u, u})
    (ℐ : t.MulStableGradedSubmodule)
    (n : ℤ) (U : (SmallEtale t.site t.base t.containsBase t.space.1)ᵒᵖ)
    (x : (t.algebra.piece n).val.obj U) (hx : x ∈ (ℐ.piece n).obj U) :
    (t.quotientMkApp ℐ n).val.app U x = 0 :=
  congrArg (fun φ : (ℐ.piece n).toSheafOfModules ⟶ (t.quotientAlgebra ℐ).piece n =>
    φ.val.app U ⟨x, hx⟩) (t.ι_comp_quotientMkApp ℐ n)

variable (s : RelativeProjSituation.{u, u})

/-- The degree-`n` component of the re-presentation of the quotient homomorphism is the quotient
homomorphism itself, read through the comparisons of the two re-presented algebras. -/
theorem shrinkMap_quotientHom_app (ℐ : s.MulStableGradedSubmodule)
    (hℐ : ∀ n : ℤ, (ℐ.piece n).toSheafOfModules.IsQuasicoherentOnSite) (n : ℤ) :
    (shrinkMap s.mul_comm s.negative_isZero s.isQuasicoherent s.sections_hasCardinalLT
      (s.quotient ℐ hℐ).mul_comm (s.quotient ℐ hℐ).negative_isZero
      (s.quotient ℐ hℐ).isQuasicoherent (s.quotient ℐ hℐ).sections_hasCardinalLT
      (s.quotientHom ℐ)).app n =
      (s.smallAlgebraPieceIso n).hom ≫ s.quotientMkApp ℐ n ≫
        ((s.quotient ℐ hℐ).smallAlgebraPieceIso n).inv :=
  rfl

variable {T : BigFppfOver s.site s.base s.containsBase} (f : yoneda.obj T ⟶ s.space.1)

/-- The pullback of modules along a scheme point. -/
local notation "𝒫" => modulePullback s.site s.base s.containsBase (pointHom f)

/-- **The image `𝒢 ⊆ (f^*𝒜)_d` of the pullback of a submodule `ℱ ⊆ 𝒜_d`** to a scheme point,
as a submodule of the degree-`d` piece of the algebra of `s.pullback (pointHom f)`. -/
def pointImageSubmodule {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) :
    ((s.pullback (pointHom f)).algebra.piece d).Submodule :=
  Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (M := (𝒫).obj ℱ.toSheafOfModules)
    (N := (s.pullback (pointHom f)).algebra.piece d)
    ((𝒫).map (ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv))

/-- The graded ideal `𝒢(f^*𝒜)` of the algebra of `s.pullback (pointHom f)`. -/
abbrev pointDegreeIdeal {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) :
    (s.pullback (pointHom f)).MulStableGradedSubmodule :=
  (s.pullback (pointHom f)).degreeIdeal (s.pointImageSubmodule f ℱ)

/-- The morphism of small étale ringed topoi of a scheme point. -/
local notation "ρ" => smallEtaleRingedToposHom s.site s.base s.containsBase (pointHom f)

/-- **The adjunct `𝒜 ⟶ f_*(f^*𝒜/𝒢(f^*𝒜))` of the quotient map**, a homomorphism of sheaves of
graded algebras by Stacks 0FQX (3). -/
def pointQuotientAdjunct {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) :
    s.smallAlgebra ⟶ (gradedPush ρ).obj
      ((s.pullback (pointHom f)).quotientAlgebra (s.pointDegreeIdeal f ℱ)) :=
  ((gradedAdj ρ).homEquiv _ _)
    ((s.pullback (pointHom f)).quotientHom (s.pointDegreeIdeal f ℱ)).toHom

/-- The degree-`n` component of the adjunct is the module adjunct of the degree-`n` component of
the quotient map. -/
theorem pointQuotientAdjunct_app {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) (n : ℤ) :
    (s.pointQuotientAdjunct f ℱ).app n =
      ((ρ).pullbackAdjPushforwardModulesViaComparison.homEquiv _ _)
        ((s.pullback (pointHom f)).quotientMkApp (s.pointDegreeIdeal f ℱ) n) :=
  rfl

/-- The adjunct kills the pullback of `ℱ`: the pullback of `ℱ ⟶ 𝒜_d` lands in `𝒢 ⊆ 𝒢(f^*𝒜)_d`,
which the quotient map kills. -/
theorem pullback_ι_quotientMkApp_eq_zero {d : ℤ} (ℱ : (s.algebra.piece d).Submodule)
    (V : (SmallEtale s.site s.base s.containsBase (yoneda.obj T))ᵒᵖ)
    (x : ((𝒫).obj ℱ.toSheafOfModules).val.obj V) :
    ((s.pullback (pointHom f)).quotientMkApp (s.pointDegreeIdeal f ℱ) d).val.app V
      (((𝒫).map (ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv)).val.app V x) = 0 := by
  refine ι_app_mem_quotientMkApp_eq_zero (s.pullback (pointHom f)) _ d V _ ?_
  exact (s.pullback (pointHom f)).le_generatedByDegree_self (s.pointImageSubmodule f ℱ) V
    (Stacks.SheafOfModules.ImageSubsheaf.apply_mem_imageSubmodule _ x)

/-- **The adjunct of the quotient map kills `ℱ`.** -/
theorem pointQuotientAdjunct_app_ι {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) :
    (ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv) ≫ (s.pointQuotientAdjunct f ℱ).app d = 0 := by
  rw [pointQuotientAdjunct_app]
  refine _root_.CategoryTheory.Adjunction.comp_homEquiv_eq_zero_of_map_comp _ _ _ ?_
  ext V x
  exact (s.pullback_ι_quotientMkApp_eq_zero f ℱ V x).trans rfl

/-- **The adjunct kills the image of `ℱ𝒜`**: it is a homomorphism of graded algebras killing `ℱ`,
so the sections of `𝒜` it kills form a submodule containing the generators of `ℱ𝒜`. -/
theorem pointQuotientAdjunct_app_eq_zero {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) (n : ℤ)
    (V : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ) (x : (s.algebra.piece n).val.obj V)
    (hx : x ∈ ((s.degreeIdeal ℱ).piece n).obj V) :
    ((s.pointQuotientAdjunct f ℱ).app n).val.app V ((s.smallAlgebraPieceIso n).inv.val.app V x) =
      0 := by
  have hle : s.generatedByDegree ℱ n ≤ Stacks.SheafOfModules.kerSubmodule
      ((s.smallAlgebraPieceIso n).inv ≫ (s.pointQuotientAdjunct f ℱ).app n) := by
    refine s.generatedByDegree_le ?_
    rintro m rfl U a ha b y hy
    rw [eq_of_heq hy, Stacks.SheafOfModules.mem_kerSubmodule_obj]
    show ((s.pointQuotientAdjunct f ℱ).app (d + m)).val.app U
      ((s.smallAlgebraEquiv.equiv (d + m) U).symm ((s.algebra.mul d m).app U a b)) = 0
    have hmul : (s.smallAlgebraEquiv.equiv (d + m) U).symm ((s.algebra.mul d m).app U a b) =
        (s.smallAlgebra.mul d m).app U ((s.smallAlgebraEquiv.equiv d U).symm a)
          ((s.smallAlgebraEquiv.equiv m U).symm b) := by
      apply (s.smallAlgebraEquiv.equiv (d + m) U).injective
      rw [LinearEquiv.apply_symm_apply, s.smallAlgebraEquiv_mul_app, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    have h0 : ((s.pointQuotientAdjunct f ℱ).app d).val.app U
        ((s.smallAlgebraEquiv.equiv d U).symm a) = 0 :=
      congrArg (fun φ : ℱ.toSheafOfModules ⟶ _ => φ.val.app U ⟨a, ha⟩)
        (s.pointQuotientAdjunct_app_ι f ℱ)
    refine (congrArg (fun z => ((s.pointQuotientAdjunct f ℱ).app (d + m)).val.app U z) hmul).trans
      (((s.pointQuotientAdjunct f ℱ).map_mul d m U _ _).trans ?_)
    refine (congrArg (fun z => ((((gradedPush ρ).obj ((s.pullback (pointHom f)).quotientAlgebra
      (s.pointDegreeIdeal f ℱ))).mul d m).app U z) _) h0).trans ?_
    exact mul_app_zero_left _ d m U _
  exact (Stacks.SheafOfModules.mem_kerSubmodule_obj _ _ _).1 (hle V hx)

end AlgebraicGeometry.Space.RelativeProjSituation

end
