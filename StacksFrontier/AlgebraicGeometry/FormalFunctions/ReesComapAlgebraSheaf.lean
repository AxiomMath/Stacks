module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.SpecReesRelativeSpec

/-!
# The Rees comparison as a morphism of algebra sheaves, and its adjoint

Let `g : Z ⟶ Y` be a morphism of schemes with `Y` **affine** and let `K` be a quasi-coherent sheaf
of ideals on `Y`. [Stacks, Tag 01OG] supplies the comparison `Kⁿ ⟶ g_*((K𝒪_Z)ⁿ)` of each
homogeneous piece (`Stacks.Blowup.reesPieceComap`), multiplicative and unital
(`Stacks.Blowup.reesPieceComap_mul`, `Stacks.Blowup.reesPieceComap_one`). This file assembles
those pieces into a morphism of sheaves of *commutative algebras*

`β : ⨁ₙ Kⁿ ⟶ g_*(⨁ₙ (K𝒪_Z)ⁿ)`

and transposes it across the base-change adjunction for algebra sheaves into

`ψ : (algebraPullback g).obj (⨁ₙ Kⁿ) ⟶ ⨁ₙ (K𝒪_Z)ⁿ`.

A morphism out of a quasi-coherent algebra sheaf over an *affine* base is a ring homomorphism on
global sections compatible with the two structure maps
(`Stacks.RelativeSpec.AlgebraSheaf.algebraHom`), and over the affine `Y` the global sections of
`⨁ₙ Kⁿ` are the direct sum `⨁ₙ Γ(Y, Kⁿ)` of the sections of the homogeneous pieces
(`Stacks.RelativeSpec.totalSectionsRingEquiv`). So `β` is assembled from the degreewise
comparison on global sections.

## Main definitions

* `Stacks.GradedAlgebra.totalRingHomOfPieces`: a degreewise family of additive maps out of the
  homogeneous sections which is multiplicative and unital is a ring homomorphism out of the
  sections of the ungraded realization, for a graded algebra of presheaves of modules on an
  arbitrary site.
* `Stacks.Blowup.reesComapTotalHom`: the ring homomorphism `⨁ₙ Γ(V, Kⁿ) →+* Γ(g⁻¹V, ⨁ₙ (K𝒪_Z)ⁿ)`
  assembled from `Stacks.Blowup.reesPieceComap`, over an arbitrary open `V` of `Y`.
* `Stacks.Blowup.reesComapAlgebraHom`: **`β : ⨁ₙ Kⁿ ⟶ g_*(⨁ₙ (K𝒪_Z)ⁿ)`**, for `Y` affine.
* `Stacks.Blowup.reesComapPullbackHom`: **`ψ`, its adjoint transpose**, a morphism of sheaves of
  commutative `𝒪_Z`-algebras out of the algebra pullback of `⨁ₙ Kⁿ`.
* `Stacks.Cohomology.FormalFunctions.baseReesComapPullbackHom`: `ψ` at `g = f : X ⟶ Spec A` and
  `K = Ĩ`, with its target read as `⨁ₙ ℐⁿ` for `ℐ = I · 𝒪_X` along
  `Stacks.Cohomology.FormalFunctions.baseIdealSheaf_eq_comap_specIdealSheaf`.

## Main results

* `Stacks.Blowup.reesComapTotalHom_incl`: the assembled ring homomorphism on a homogeneous
  section is `Stacks.Blowup.reesPieceComap` followed by the degree-`n` inclusion into the ungraded
  realization.
* `Stacks.Blowup.reesComapSections_unitTop`: the compatibility of the inverse image on global
  sections with the two structure maps.
* `Stacks.Blowup.reesComapPullbackHom_app_unit`: on the unit image of a global section of
  `⨁ₙ Kⁿ`, `ψ` is `β` on that section.
* `Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_isLocallySurjective`:
  [Stacks, Tag 02O8]'s hypothesis `h0897` at one graded module, granted the local surjectivity of
  `baseReesComapPullbackHom`.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Blowup Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.GradedProperCohomology

universe w v u

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{w} R}

/-- A degreewise family of additive maps out of the homogeneous sections, assembled into an
additive map out of the sections of the ungraded realization. -/
def totalAddHomOfPieces (A : GradedAlgebra P) (X : Cᵒᵖ) {S : Type*} [AddCommMonoid S]
    (f : ∀ n : ι, (P n).obj X →+ S) : A.Total X →+ S :=
  DirectSum.toAddMonoid f

/-- The assembled additive map on a homogeneous section. -/
theorem totalAddHomOfPieces_incl (A : GradedAlgebra P) (X : Cᵒᵖ) {S : Type*} [AddCommMonoid S]
    (f : ∀ n : ι, (P n).obj X →+ S) (n : ι) (x : (P n).obj X) :
    totalAddHomOfPieces A X f (A.incl n x) = f n x :=
  DirectSum.toAddMonoid_of f n x

/-- **A degreewise family of additive maps out of the homogeneous sections which is multiplicative
and unital assembles into a ring homomorphism out of the sections of the ungraded realization.** -/
def totalRingHomOfPieces (A : GradedAlgebra P) (X : Cᵒᵖ) {S : Type*} [Ring S]
    (f : ∀ n : ι, (P n).obj X →+ S) (hone : f 0 (A.one.eval X) = 1)
    (hmul : ∀ (i j : ι) (x : (P i).obj X) (y : (P j).obj X),
      f (i + j) ((A.mul i j).app X x y) = f i x * f j y) :
    A.Total X →+* S where
  toFun := totalAddHomOfPieces A X f
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [A.one_eq_incl X, totalAddHomOfPieces_incl]
    exact hone
  map_mul' a b := by
    induction a using A.incl_induction with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | incl i x =>
        induction b using A.incl_induction with
        | zero => rw [mul_zero, map_zero, mul_zero]
        | incl j y =>
            rw [A.incl_mul_incl, totalAddHomOfPieces_incl, totalAddHomOfPieces_incl,
              totalAddHomOfPieces_incl]
            exact hmul i j x y
        | add b b' hb hb' => rw [mul_add, map_add, map_add, mul_add, hb, hb']
    | add a a' ha ha' => rw [add_mul, map_add, map_add, add_mul, ha, ha']

/-- The assembled ring homomorphism on a homogeneous section. -/
@[simp]
theorem totalRingHomOfPieces_incl (A : GradedAlgebra P) (X : Cᵒᵖ) {S : Type*} [Ring S]
    (f : ∀ n : ι, (P n).obj X →+ S) (hone : f 0 (A.one.eval X) = 1)
    (hmul : ∀ (i j : ι) (x : (P i).obj X) (y : (P j).obj X),
      f (i + j) ((A.mul i j).app X x y) = f i x * f j y) (n : ι) (x : (P n).obj X) :
    totalRingHomOfPieces A X f hone hmul (A.incl n x) = f n x :=
  totalAddHomOfPieces_incl A X f n x

end Stacks.GradedAlgebra

namespace Stacks.Blowup

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) (K : Y.IdealSheafData)

/-- The degree-`n` comparison `Γ(V, Kⁿ) ⟶ Γ(g⁻¹V, ⨁ₙ (K𝒪_Z)ⁿ)`: the inverse image
`Stacks.Blowup.reesPieceComap` on the homogeneous piece, followed by the degree-`n` inclusion into
the ungraded realization, as an additive map. -/
def reesComapInclAddHom (n : ℤ) (V : Y.Opens) :
    (reesPiece K n).val.obj (op V) →+
      (reesGradedAlgebra (K.comap g)).ungradedSheaf.obj.obj (op (g ⁻¹ᵁ V)) where
  toFun x := (reesGradedAlgebra (K.comap g)).ungradedIncl n
    ((reesPieceComap g K n).val.app (op V) x)
  map_zero' := by
    rw [map_zero]
    exact Stacks.GradedAlgebra.inclSheaf_zero _ _ n
  map_add' x y := by
    rw [map_add]
    exact (reesGradedAlgebra (K.comap g)).ungradedIncl_add n _ _ _

/-- **The inverse image on the sections of the Rees algebra over an open `V` of the base**, as a
ring homomorphism `⨁ₙ Γ(V, Kⁿ) →+* Γ(g⁻¹V, ⨁ₙ (K𝒪_Z)ⁿ)`. -/
def reesComapTotalHom (V : Y.Opens) :
    (reesGradedAlgebra K).toPresheafGradedAlgebra.Total (op V) →+*
      (reesGradedAlgebra (K.comap g)).ungradedSheaf.obj.obj (op (g ⁻¹ᵁ V)) :=
  Stacks.GradedAlgebra.totalRingHomOfPieces _ _ (fun n => reesComapInclAddHom g K n V)
    ((congrArg ((reesGradedAlgebra (K.comap g)).ungradedIncl 0) (reesPieceComap_one g K V)).trans
      ((reesGradedAlgebra (K.comap g)).ungradedIncl_one _))
    fun i j x y =>
      (congrArg ((reesGradedAlgebra (K.comap g)).ungradedIncl (i + j))
          (reesPieceComap_mul g K i j V x y)).trans
        ((reesGradedAlgebra (K.comap g)).ungradedIncl_mul i j _ _).symm

/-- The inverse image on sections, on a homogeneous section, is `Stacks.Blowup.reesPieceComap`
followed by the degree-`n` inclusion. -/
theorem reesComapTotalHom_incl (V : Y.Opens) (n : ℤ) (x : (reesPiece K n).val.obj (op V)) :
    reesComapTotalHom g K V ((reesGradedAlgebra K).toPresheafGradedAlgebra.incl n x) =
      (reesGradedAlgebra (K.comap g)).ungradedIncl n
        ((reesPieceComap g K n).val.app (op V) x) :=
  DirectSum.toAddMonoid_of (fun n => reesComapInclAddHom g K n V) n x

/-- **The inverse image carries a scalar multiple of the Rees unit to the corresponding scalar
multiple of the Rees unit.** -/
theorem reesPieceComap_smul_one (V : Y.Opens) (r : Y.ringCatSheaf.obj.obj (op V)) :
    (reesPieceComap g K 0).val.app (op V) (r • (reesUnit K).eval (op V)) =
      (show Z.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from (g.app V).hom (ringSectionToGamma r)) •
        (reesUnit (K.comap g)).eval (op (g ⁻¹ᵁ V)) := by
  refine reesPieceAmbient_injective (K.comap g) 0 le_rfl (g ⁻¹ᵁ V) ?_
  refine (reesPieceAmbient_comap g K 0 V _).trans ?_
  refine Eq.trans (congrArg (fun t => ConcreteCategory.hom (g.app V) t)
    ((reesPieceAmbient_smul K 0 V r _).trans
      (congrArg (fun t => ringSectionToGamma r * t) (reesUnit_ambient K (op V))))) ?_
  refine Eq.trans (congrArg (fun t => ConcreteCategory.hom (g.app V) t)
    (mul_one (ringSectionToGamma r))) ?_
  refine Eq.trans ?_ ((reesPieceAmbient_smul (K.comap g) 0 (g ⁻¹ᵁ V) _ _).trans
    (congrArg (fun t => ringSectionToGamma
        (show Z.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from (g.app V).hom (ringSectionToGamma r)) * t)
      (reesUnit_ambient (K.comap g) (op (g ⁻¹ᵁ V))))).symm
  exact (mul_one _).symm

/-- **The inverse image on sections is compatible with the structure maps from the base
ring.** -/
theorem reesComapTotalHom_structureMap (V : Y.Opens) (r : Y.ringCatSheaf.obj.obj (op V)) :
    reesComapTotalHom g K V
        ((reesGradedAlgebra K).toPresheafGradedAlgebra.structureMap (op V) r) =
      ((reesGradedAlgebra (K.comap g)).ungradedStructureMap.hom.app
          (op (g ⁻¹ᵁ V))).hom ((g.app V).hom (ringSectionToGamma r)) := by
  have h1 : (reesGradedAlgebra K).toPresheafGradedAlgebra.structureMap (op V) r =
      (reesGradedAlgebra K).toPresheafGradedAlgebra.incl 0 (r • (reesUnit K).eval (op V)) :=
    (congrArg (fun t => r • t)
        ((reesGradedAlgebra K).toPresheafGradedAlgebra.one_eq_incl (op V))).trans
      ((reesGradedAlgebra K).toPresheafGradedAlgebra.incl_smul 0 r _).symm
  refine Eq.trans (congrArg (reesComapTotalHom g K V) h1) ?_
  refine Eq.trans (reesComapTotalHom_incl g K V 0 _) ?_
  refine Eq.trans (congrArg ((reesGradedAlgebra (K.comap g)).ungradedIncl 0)
    (reesPieceComap_smul_one g K V r)) ?_
  exact (reesGradedAlgebra (K.comap g)).ungradedIncl_smul_one _ _

section Affine

variable [IsAffine Y]

/-- The inverse image on *global* sections over an affine base, as a morphism of rings:
`Stacks.Blowup.reesComapTotalHom` on the direct sum `⨁ₙ Γ(Y, Kⁿ)`, which is the global sections
of `⨁ₙ Kⁿ` because `Y` is affine. -/
def reesComapSectionsRingCatHom :
    (reesGradedAlgebra K).ungradedSheaf.obj.obj (op (⊤ : Y.Opens)) ⟶
      (reesGradedAlgebra (K.comap g)).ungradedSheaf.obj.obj (op (g ⁻¹ᵁ (⊤ : Y.Opens))) :=
  RingCat.ofHom
    ((reesComapTotalHom g K ⊤).comp
      (Stacks.RelativeSpec.totalSectionsRingEquiv Y (reesGradedAlgebra K)
        (fun i j W a b => reesMultiplication_comm K i j W a b)
        (isAffineOpen_top Y)).symm.toRingHom)

/-- The inverse image on global sections, as a morphism of *commutative* rings: the same data as
`Stacks.Blowup.reesComapSectionsRingCatHom`. -/
def reesComapSections :
    AlgebraSheaf.sections (reesAlgebraSheaf K) ⊤ ⟶
      AlgebraSheaf.sections ((algebraPushforward g).obj (reesAlgebraSheaf (K.comap g))) ⊤ :=
  Stacks.CommRingSheaf.ofRingCatHom
    ((reesGradedAlgebra K).mul_comm_ungradedSheaf
      (fun i j W a b => reesMultiplication_comm K i j W a b) (op (⊤ : Y.Opens)))
    ((reesGradedAlgebra (K.comap g)).mul_comm_ungradedSheaf
      (fun i j W a b => reesMultiplication_comm (K.comap g) i j W a b)
      (op (g ⁻¹ᵁ (⊤ : Y.Opens))))
    (reesComapSectionsRingCatHom g K)

/-- **The inverse image on global sections is compatible with the two structure maps.** -/
theorem reesComapSections_unitTop :
    (reesAlgebraSheaf K).unitTop ≫ reesComapSections g K =
      ((algebraPushforward g).obj (reesAlgebraSheaf (K.comap g))).unitTop := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  exact (congrArg (reesComapTotalHom g K ⊤)
    ((Stacks.RelativeSpec.totalSectionsRingEquiv Y (reesGradedAlgebra K)
        (fun i j W a b => reesMultiplication_comm K i j W a b)
        (isAffineOpen_top Y)).symm_apply_apply
      ((reesGradedAlgebra K).toPresheafGradedAlgebra.structureMap (op ⊤) r))).trans
    (reesComapTotalHom_structureMap g K ⊤ r)

/-- **`β : ⨁ₙ Kⁿ ⟶ g_*(⨁ₙ (K𝒪_Z)ⁿ)`, the inverse image as a morphism of sheaves of commutative
`𝒪_Y`-algebras**, for a morphism `g : Z ⟶ Y` into an affine base. -/
def reesComapAlgebraHom :
    reesAlgebraSheaf K ⟶ (algebraPushforward g).obj (reesAlgebraSheaf (K.comap g)) :=
  AlgebraSheaf.algebraHom _ _ (reesComapSections_unitTop g K)

/-- **`ψ : g^*(⨁ₙ Kⁿ) ⟶ ⨁ₙ (K𝒪_Z)ⁿ`, the adjoint transpose of `β`**, where `g^*` is the
*algebra* pullback `g⁻¹(−) ⊗_{g⁻¹𝒪_Y} 𝒪_Z`, not the degreewise module pullback of
`Stacks.Conormal.gradedPullback`. -/
def reesComapPullbackHom :
    (algebraPullback g).obj (reesAlgebraSheaf K) ⟶ reesAlgebraSheaf (K.comap g) :=
  ((algebraPullbackPushforwardAdjunction g).homEquiv _ _).symm (reesComapAlgebraHom g K)

/-- `β` on global sections is `Stacks.Blowup.reesComapSections`. -/
theorem reesComapAlgebraHom_right_app_top :
    (reesComapAlgebraHom g K).right.hom.app (op ⊤) = reesComapSections g K :=
  AlgebraSheaf.algebraHom_right_app_top (reesAlgebraSheaf K)
    ((algebraPushforward g).obj (reesAlgebraSheaf (K.comap g))) (reesComapSections_unitTop g K)

/-- **The adjunction identity defining `ψ`**: the unit of the base-change adjunction for algebra
sheaves followed by the pushforward of `ψ` is `β`. -/
theorem unit_comp_map_reesComapPullbackHom :
    (algebraPullbackPushforwardAdjunction g).unit.app (reesAlgebraSheaf K) ≫
        (algebraPushforward g).map (reesComapPullbackHom g K) =
      reesComapAlgebraHom g K :=
  (Adjunction.homEquiv_unit (algebraPullbackPushforwardAdjunction g) (reesAlgebraSheaf K)
      (reesAlgebraSheaf (K.comap g)) (reesComapPullbackHom g K)).symm.trans
    (Equiv.apply_symm_apply
      ((algebraPullbackPushforwardAdjunction g).homEquiv (reesAlgebraSheaf K)
        (reesAlgebraSheaf (K.comap g))) _)

/-- **`ψ` on the unit image of a global section of `⨁ₙ Kⁿ` is `β` on that section.** -/
theorem reesComapPullbackHom_app_unit (b : AlgebraSheaf.sections (reesAlgebraSheaf K) ⊤) :
    (reesComapPullbackHom g K).right.hom.app (op (g ⁻¹ᵁ (⊤ : Y.Opens)))
        (((algebraPullbackPushforwardAdjunction g).unit.app
          (reesAlgebraSheaf K)).right.hom.app (op ⊤) b) =
      reesComapSections g K b := by
  refine Eq.trans (show _ = (ConcreteCategory.hom
      ((((algebraPullbackPushforwardAdjunction g).unit.app (reesAlgebraSheaf K) ≫
        (algebraPushforward g).map (reesComapPullbackHom g K)).right).hom.app (op ⊤))) b
      from rfl) ?_
  refine Eq.trans (congrArg (fun t : reesAlgebraSheaf K ⟶
      (algebraPushforward g).obj (reesAlgebraSheaf (K.comap g)) =>
    (ConcreteCategory.hom (t.right.hom.app (op ⊤))) b)
    (unit_comp_map_reesComapPullbackHom g K)) ?_
  exact congrArg (fun φ : AlgebraSheaf.sections (reesAlgebraSheaf K) ⊤ ⟶
      AlgebraSheaf.sections ((algebraPushforward g).obj (reesAlgebraSheaf (K.comap g))) ⊤ =>
    ConcreteCategory.hom φ b) (reesComapAlgebraHom_right_app_top g K)

end Affine

end Stacks.Blowup

namespace Stacks.Cohomology.FormalFunctions

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-- **`ψ : f^* B̃ ⟶ ⨁_{n ≥ 0} ℐⁿ` for the Rees algebra of an ideal of the base**, the morphism of
sheaves of commutative `𝒪_X`-algebras out of the **algebra** pullback of `B̃ = ⨁_{n ≥ 0} Ĩⁿ`.

This is `Stacks.Blowup.reesComapPullbackHom` at `g = f : X ⟶ Spec A` and `K = Ĩ`, with its target
read as the Rees algebra of `ℐ = I · 𝒪_X` along
`Stacks.Cohomology.FormalFunctions.baseIdealSheaf_eq_comap_specIdealSheaf`. -/
def baseReesComapPullbackHom :
    (algebraPullback X.hom).obj (specReesAlgebraSheaf I) ⟶
      reesAlgebraSheaf (baseIdealSheaf A I X.hom) :=
  baseIdealSheaf_eq_comap_specIdealSheaf I X ▸ reesComapPullbackHom X.hom (specIdealSheaf I)

attribute [local instance] cohomologyGradedModule

/-- **[Stacks, Tag 02O8]'s hypothesis `h0897` at one graded module**, granted that the morphism
of sheaves of rings underlying `Stacks.Cohomology.FormalFunctions.baseReesComapPullbackHom` is
locally surjective (`hψ`), a coherent module `F'` on `X'` and the comparison `cmp`.

This is
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_algebraPullbackHom`
with `ψ` taken to be `Stacks.Cohomology.FormalFunctions.baseReesComapPullbackHom`. -/
theorem isCohomologyReesFiniteOfGradedModule_of_isLocallySurjective [IsNoetherianRing A]
    (M : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X)) (p : ℕ)
    (hX : AlgebraicGeometry.IsProper X.hom)
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hft : M.IsFiniteType)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules))
    (hψ : CategoryTheory.Sheaf.IsLocallySurjective (baseReesComapPullbackHom I X).right)
    (F' : (reesRelativeSpec I X).left.Modules) [F'.IsCoherent]
    (cmp :
      letI := gradedCohomologySumModuleRees I X M p hneg
      gradedCohomologySum M p ≃ₗ[↥(reesAlgebra I)]
        ↥((ModuleCat.restrictScalars (specAlgebraRingHom ↥(reesAlgebra I)
            (reesRelativeSpecToPullback I X (baseReesComapPullbackHom I X) ≫
              pullback.fst (reesSpecToBase I) X.hom))).obj
          (cohomologyOf (reesRelativeSpec I X).left p F'))) :
    IsCohomologyReesFiniteOfGradedModule I X M p :=
  isCohomologyReesFiniteOfGradedModule_of_algebraPullbackHom I X M p hX hqc hft hneg
    (baseReesComapPullbackHom I X) hψ F' cmp

end Stacks.Cohomology.FormalFunctions

end
