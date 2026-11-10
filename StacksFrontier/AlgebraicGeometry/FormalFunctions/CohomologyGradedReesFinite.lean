module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyReesSystemGraded
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ReesGradedModule
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemNoetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# The graded cohomology of a graded module over the Rees algebra

Let `A` be a ring, `I ⊆ A` an ideal, `X` a scheme over `Spec A` and `ℐ = I · 𝒪_X`. The sheaf
`𝓑 = ⨁_{n ≥ 0} ℐⁿ` of graded `𝒪_X`-algebras is the Rees algebra of `ℐ`. For an arbitrary graded
`𝓑`-module `M`, the graded module `⨁_{n ≥ 0} Hᵖ(X, Mₙ)` is a graded module over the ring Rees
algebra `B = ⨁_{n ≥ 0} Iⁿ`. If this graded module is finite over `B` for every quasi-coherent
graded `𝓑`-module of finite type on a scheme proper over a Noetherian ring, then for `ℱ` coherent
and `f : X → Spec A` proper the graded module `⨁_{n ≥ 0} Hᵖ(X, Iⁿℱ)` carried by
`Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem` is a finite `B`-module.

## Main definitions

* `SheafOfModules.GradedModule.pieceCast`: transport along an equality of degrees, as a morphism
  between pieces of a graded module.
* `Stacks.Cohomology.FormalFunctions.reesElt` and
  `Stacks.Cohomology.FormalFunctions.gradedReesSection`: the element of `Iᵏ` underlying a
  homogeneous degree-`k` element of `B = ⨁ₙ Iⁿ`, and the global section of `𝓑ₖ = ℐᵏ` it
  determines.
* `Stacks.Cohomology.FormalFunctions.actHom`: the action of a homogeneous element of `B` on an
  arbitrary graded `𝓑`-module, as a morphism `Mₙ ⟶ Mₘ` with `m = n + k`.
* `Stacks.Cohomology.FormalFunctions.cohomologyGradedModule`: the graded `B`-module
  `⨁ₙ Hᵖ(X, Mₙ)`, as a `DirectSum.Gmodule`.
* `Stacks.Cohomology.FormalFunctions.IsCohomologyReesFiniteOfGradedModule`: the assertion that
  `⨁ₙ Hᵖ(X, Mₙ)` is a finite `B`-module.
* `Stacks.Cohomology.FormalFunctions.transferLinear`: the comparison
  `⨁ₙ Hᵖ(X, ℐⁿℱ) ⟶ ⨁ₙ Hᵖ(X, Iⁿℱ)` between the graded module built here at
  `M = ⨁ₙ ℐⁿℱ` and the one carried by `cohomologyIdealPowerSystem`.

## Main results

* `SheafOfModules.GradedModule.smulSectionsHom_one` and
  `SheafOfModules.GradedModule.smulSectionsHom_comp`: the unit and associativity laws for the
  action of global homogeneous sections.
* `Stacks.Cohomology.FormalFunctions.actHom_one` and
  `Stacks.Cohomology.FormalFunctions.actHom_comp`: the same two laws for the action of `B`.
* `Stacks.Cohomology.FormalFunctions.actHom_comp_filtrationPieceIso`: at `M = ⨁ₙ ℐⁿℱ` the action
  of `b ∈ Iᵏ` is, through the identification of the two models of `ℐⁿℱ`, the multiplication map
  `idealPowerSmul`.
* `Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite_of_isCoherent`: `⨁ₙ Hᵖ(X, Iⁿℱ)` is a
  finite `B`-module, given the finiteness of `⨁ₙ Hᵖ(X, Mₙ)` for every quasi-coherent graded
  `𝓑`-module `M` of finite type with vanishing negative pieces.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower Stacks.Cohomology.AffineBase Stacks.Blowup
open scoped DirectSum ModuleCat.Algebra

universe u u' v' t' a' m'

namespace SheafOfModules.GradedModule

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t'}}
  {B : SheafOfModules.GradedAlgebra.{t', a'} R} (M : SheafOfModules.GradedModule.{t', a', m'} B)

/-- Two morphisms of sheaves of modules on a site agree as soon as they agree on sections over
every object. -/
theorem hom_ext_sections {M N : SheafOfModules.{m'} R} {f g : M ⟶ N}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U), f.val.app U x = g.val.app U x) : f = g :=
  SheafOfModules.hom_ext <| PresheafOfModules.Hom.ext <| funext fun U ↦
    ModuleCat.Hom.ext <| LinearMap.ext (h U)

/-- Transport along an equality of degrees, as a morphism between pieces of a graded module. -/
def pieceCast {d d' : ℤ} (e : d = d') : M.piece d ⟶ M.piece d' :=
  eqToHom (congrArg M.piece e)

/-- On sections, transport along an equality of degrees is `SheafOfModules.castHom`. -/
theorem pieceCast_app {d d' : ℤ} (e : d = d') (U : Cᵒᵖ) (x : (M.piece d).val.obj U) :
    (pieceCast M e).val.app U x = SheafOfModules.castHom M.piece e U x := by
  subst e; rfl

/-- Transport along an equality of a degree with itself is the identity. -/
theorem pieceCast_rfl {d : ℤ} (e : d = d) : pieceCast M e = 𝟙 (M.piece d) := rfl

/-- Transports along equalities of degrees compose. -/
theorem pieceCast_pieceCast {d d' d'' : ℤ} (e : d = d') (e' : d' = d'') :
    pieceCast M e ≫ pieceCast M e' = pieceCast M (e.trans e') := by
  subst e; subst e'; exact Category.id_comp _

/-- Multiplication by a global homogeneous section depends on the section only through its
values. -/
theorem smulSectionsHom_congr (n i : ℤ) {r r' : (B.piece i).val.sections}
    (h : ∀ U : Cᵒᵖ, r.eval U = r'.eval U) :
    smulSectionsHom M n i r = smulSectionsHom M n i r' :=
  hom_ext_sections fun U x ↦ by
    change M.smul n i U x (r.eval U) = M.smul n i U x (r'.eval U)
    rw [h U]

/-- Multiplication by a global homogeneous section is additive in the section. -/
theorem smulSectionsHom_eval_add (n i : ℤ) {r r₁ r₂ : (B.piece i).val.sections}
    (h : ∀ U : Cᵒᵖ, r.eval U = r₁.eval U + r₂.eval U) :
    smulSectionsHom M n i r = smulSectionsHom M n i r₁ + smulSectionsHom M n i r₂ :=
  hom_ext_sections fun U x ↦ by
    change M.smul n i U x (r.eval U) = _
    rw [h U, map_add]
    rfl

/-- Multiplication by a global homogeneous section with vanishing values is zero. -/
theorem smulSectionsHom_eval_zero (n i : ℤ) {r : (B.piece i).val.sections}
    (h : ∀ U : Cᵒᵖ, r.eval U = 0) : smulSectionsHom M n i r = 0 :=
  hom_ext_sections fun U x ↦ by
    change M.smul n i U x (r.eval U) = _
    rw [h U, map_zero]
    rfl

/-- Multiplication by the unit section of the algebra is, after the transport `n + 0 = n`, the
identity. -/
theorem smulSectionsHom_one (n : ℤ) :
    smulSectionsHom M n 0 B.one ≫ pieceCast M (add_zero n) = 𝟙 (M.piece n) := by
  refine hom_ext_sections fun U x ↦ ?_
  change (pieceCast M (add_zero n)).val.app U (M.smul n 0 U x (B.one.eval U)) = x
  rw [pieceCast_app]
  exact SheafOfModules.Cofree.castHom_eq_castHom (add_zero n) rfl U (M.smul_one n U x)

/-- Transport along an equality of degrees commutes with multiplication by a global homogeneous
section. -/
theorem pieceCast_comp_smulSectionsHom {n n' : ℤ} (e : n = n') (i : ℤ)
    (r : (B.piece i).val.sections) :
    pieceCast M e ≫ smulSectionsHom M n' i r =
      smulSectionsHom M n i r ≫ pieceCast M (by rw [e]) := by
  subst e
  rw [pieceCast_rfl, Category.id_comp, pieceCast_rfl, Category.comp_id]

/-- Multiplying by a section of degree `i` and then by one of degree `j` is multiplying by their
product, a section `t` of degree `i'` specified by its values up to the transport along
`i + j = i'`. -/
theorem smulSectionsHom_comp {n i j i' m : ℤ} (hij : i + j = i') (hm : n + i' = m)
    (hnij : n + i + j = m)
    (r : (B.piece i).val.sections) (s : (B.piece j).val.sections)
    (t : (B.piece i').val.sections)
    (ht : ∀ U : Cᵒᵖ, SheafOfModules.castHom B.piece hij U
        ((B.mul i j).app U (r.eval U) (s.eval U)) = t.eval U) :
    smulSectionsHom M n i r ≫ smulSectionsHom M (n + i) j s ≫ pieceCast M hnij =
      smulSectionsHom M n i' t ≫ pieceCast M hm := by
  refine hom_ext_sections fun U x ↦ ?_
  change (pieceCast M hnij).val.app U
      (M.smul (n + i) j U (M.smul n i U x (r.eval U)) (s.eval U)) =
    (pieceCast M hm).val.app U (M.smul n i' U x (t.eval U))
  rw [pieceCast_app, pieceCast_app, ← ht U,
    SheafOfModules.Cofree.smul_castHom_right M hij U x
      ((B.mul i j).app U (r.eval U) (s.eval U)),
    SheafOfModules.Cofree.castHom_castHom]
  exact SheafOfModules.Cofree.castHom_eq_castHom _ _ U
    (M.smul_mul n i j U x (r.eval U) (s.eval U))

end SheafOfModules.GradedModule

namespace Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra
  Stacks.Algebraization.sectionsModuleΓ Stacks.Algebraization.sectionsModuleΓSheaf

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-! ### Homogeneous elements of `B = ⨁ₙ Iⁿ` as global sections of `𝓑 = ⨁ₙ ℐⁿ` -/

/-- The Rees algebra `𝓑 = ⨁_{n ≥ 0} ℐⁿ` of `ℐ = I · 𝒪_X`, as a sheaf of graded
`𝒪_X`-algebras. -/
abbrev baseReesAlgebra : SheafOfModules.GradedAlgebra.{u, u} X.left.ringCatSheaf :=
  reesGradedAlgebra (baseIdealSheaf A I X.hom)

/-- The element of `Iᵏ` underlying a homogeneous element of degree `k` of the Rees algebra
`B = ⨁ₙ Iⁿ`: its `k`-th polynomial coefficient. -/
def reesElt {k : ℕ} (b : ↥(reesGrading I k)) : A := ((reesGradingEquivPow I k).symm b : A)

/-- The underlying element of a homogeneous element of degree `k` lies in `Iᵏ`. -/
theorem reesElt_mem {k : ℕ} (b : ↥(reesGrading I k)) : reesElt I b ∈ I ^ k :=
  ((reesGradingEquivPow I k).symm b).2

/-- The global section of `𝓑ₖ = ℐᵏ` attached to a homogeneous element of degree `k` of
`B = ⨁ₙ Iⁿ`: `Stacks.Cohomology.FormalFunctions.baseReesSection` at the underlying element of
`Iᵏ`. -/
def gradedReesSection {k : ℕ} (b : ↥(reesGrading I k)) :
    ((baseReesAlgebra I X).piece (k : ℤ)).val.sections :=
  baseReesSection I X k (reesElt I b) (reesElt_mem I b)

/-- The attached global section is additive. -/
theorem eval_gradedReesSection_add {k : ℕ} (b b' : ↥(reesGrading I k)) (U : (Opens X.left)ᵒᵖ) :
    (gradedReesSection I X (b + b')).eval U =
      (gradedReesSection I X b).eval U + (gradedReesSection I X b').eval U := by
  have he : reesElt I (b + b') = reesElt I b + reesElt I b' :=
    congrArg Subtype.val (map_add (reesGradingEquivPow I k).symm b b')
  change (baseReesSection I X k (reesElt I (b + b')) _).eval (op U.unop) = _
  rw [show (baseReesSection I X k (reesElt I (b + b')) (reesElt_mem I (b + b'))) =
      baseReesSection I X k (reesElt I b + reesElt I b')
        (Ideal.add_mem _ (reesElt_mem I b) (reesElt_mem I b')) by
    simp only [he]]
  exact eval_baseReesSection_add I X k (reesElt_mem I b) (reesElt_mem I b') U.unop

/-- The global section attached to the zero element vanishes. -/
theorem eval_gradedReesSection_zero {k : ℕ} (U : (Opens X.left)ᵒᵖ) :
    (gradedReesSection I X (0 : ↥(reesGrading I k))).eval U = 0 := by
  have h := eval_gradedReesSection_add I X (0 : ↥(reesGrading I k)) 0 U
  rw [add_zero] at h
  refine (add_left_cancel (a := (gradedReesSection I X (0 : ↥(reesGrading I k))).eval U) ?_).symm
  rw [add_zero]
  exact h

/-- The element of `I⁰ = A` underlying the unit of the Rees algebra `B = ⨁ₙ Iⁿ` is `1`. -/
theorem reesElt_one :
    reesElt I (GradedMonoid.GOne.one (A := fun n => ↥(reesGrading I n)) :
      ↥(reesGrading I 0)) = 1 := by
  change ((reesGradingEquivPow I 0).symm
      (GradedMonoid.GOne.one (A := fun n => ↥(reesGrading I n))) : A) = 1
  rw [coe_reesGradingEquivPow_symm, SetLike.coe_gOne, OneMemClass.coe_one,
    Polynomial.coeff_one_zero]

/-- The element of `Iᵏ⁺ˡ` underlying a product of homogeneous elements of the Rees algebra
`B = ⨁ₙ Iⁿ` is the product of the underlying elements. -/
theorem reesElt_mul {k l : ℕ} (b : ↥(reesGrading I k)) (b' : ↥(reesGrading I l)) :
    reesElt I (GradedMonoid.GMul.mul (A := fun n => ↥(reesGrading I n)) b b') =
      reesElt I b * reesElt I b' :=
  Stacks.RingTheory.ReesSystem.coe_symm_gMul b b'

/-- The global section attached to the unit of `B = ⨁ₙ Iⁿ` is the unit of `𝓑 = ⨁ₙ ℐⁿ`. -/
theorem eval_gradedReesSection_one (U : (Opens X.left)ᵒᵖ) :
    (gradedReesSection I X (GradedMonoid.GOne.one (A := fun n => ↥(reesGrading I n)) :
        ↥(reesGrading I 0))).eval U =
      (baseReesAlgebra I X).one.eval U := by
  change (baseReesSection I X 0
      (reesElt I (GradedMonoid.GOne.one (A := fun n => ↥(reesGrading I n)) :
        ↥(reesGrading I 0))) _).eval (op U.unop) = _
  rw [show (baseReesSection I X 0
        (reesElt I (GradedMonoid.GOne.one (A := fun n => ↥(reesGrading I n)) :
          ↥(reesGrading I 0))) (reesElt_mem I _)) =
      baseReesSection I X 0 1
        (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top) by
    simp only [reesElt_one]]
  exact eval_baseReesSection_one I X U.unop

/-- Transporting a homogeneous section of the Rees algebra along an equality of degrees does not
change its image in `Γ(X, U)`. -/
theorem reesPieceAmbient_castHom {d d' : ℤ} (e : d = d') (U : (Opens X.left)ᵒᵖ)
    (z : ((baseReesAlgebra I X).piece d).val.obj U) :
    reesPieceAmbient (baseIdealSheaf A I X.hom) d' U.unop
        (SheafOfModules.castHom (baseReesAlgebra I X).piece e U z) =
      reesPieceAmbient (baseIdealSheaf A I X.hom) d U.unop z := by
  subst e; rfl

/-- The image in `Γ(X, U)` of the global section attached to a homogeneous element of
`B = ⨁ₙ Iⁿ` is the function attached to the underlying element of `Iᵏ`. -/
theorem reesPieceAmbient_gradedReesSection {k : ℕ} (b : ↥(reesGrading I k))
    (U : (Opens X.left)ᵒᵖ) :
    reesPieceAmbient (baseIdealSheaf A I X.hom) (k : ℤ) U.unop
        ((gradedReesSection I X b).eval U) =
      ringSectionToGamma (baseRingToSections A X (op U.unop) (reesElt I b)) :=
  reesPieceAmbient_baseReesSection I X k (reesElt I b) (reesElt_mem I b) U.unop

/-- The image in `Γ(X, U)` of a product of two attached global sections is the function attached
to the product of the underlying elements. -/
theorem reesPieceAmbient_mul_gradedReesSection {k l : ℕ} (b : ↥(reesGrading I k))
    (b' : ↥(reesGrading I l)) (U : (Opens X.left)ᵒᵖ) :
    reesPieceAmbient (baseIdealSheaf A I X.hom) ((k : ℤ) + (l : ℤ)) U.unop
        (((baseReesAlgebra I X).mul (k : ℤ) (l : ℤ)).app U
          ((gradedReesSection I X b).eval U) ((gradedReesSection I X b').eval U)) =
      ringSectionToGamma (baseRingToSections A X (op U.unop) (reesElt I b * reesElt I b')) :=
  reesPieceAmbient_reesMultiplication_baseReesSection I X k l (reesElt_mem I b)
    (reesElt_mem I b') U.unop

/-- The product of the global sections attached to `b` and `b'` is, after the transport along
`k + l = m`, the global section attached to any homogeneous element of degree `m` whose
underlying element is the product. -/
theorem castHom_mul_gradedReesSection {k l m : ℕ} (b : ↥(reesGrading I k))
    (b' : ↥(reesGrading I l)) (c : ↥(reesGrading I m))
    (hc : reesElt I c = reesElt I b * reesElt I b')
    (hkl : (k : ℤ) + (l : ℤ) = (m : ℤ)) (U : (Opens X.left)ᵒᵖ) :
    SheafOfModules.castHom (baseReesAlgebra I X).piece hkl U
        (((baseReesAlgebra I X).mul (k : ℤ) (l : ℤ)).app U
          ((gradedReesSection I X b).eval U) ((gradedReesSection I X b').eval U)) =
      (gradedReesSection I X c).eval U := by
  refine reesPieceAmbient_injective (baseIdealSheaf A I X.hom) (m : ℤ)
    (Int.natCast_nonneg _) U.unop ?_
  rw [reesPieceAmbient_castHom I X hkl U, reesPieceAmbient_mul_gradedReesSection,
    reesPieceAmbient_gradedReesSection, hc]

/-! ### The action of `B = ⨁ₙ Iⁿ` on an arbitrary graded `𝓑`-module -/

section Act

open SheafOfModules.GradedModule

variable (M : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X))

/-- The action of a homogeneous element of degree `k` of `B = ⨁ₙ Iⁿ` on a graded `𝓑`-module,
as a morphism `Mₙ ⟶ Mₘ`, where `m = n + k`. -/
def actHom {k : ℕ} (b : ↥(reesGrading I k)) (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    M.piece n ⟶ M.piece m :=
  smulSectionsHom M n (k : ℤ) (gradedReesSection I X b) ≫ pieceCast M hm

/-- The action on sections: multiplication by the attached global section, followed by the
transport to the target degree. -/
theorem actHom_app {k : ℕ} (b : ↥(reesGrading I k)) (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m)
    (U : (Opens X.left)ᵒᵖ) (y : (M.piece n).val.obj U) :
    ((actHom I X M b n hm).val.app U) y =
      ((pieceCast M hm).val.app U)
        (((smulSectionsHom M n (k : ℤ) (gradedReesSection I X b)).val.app U) y) := rfl

/-- Following the action by a transport of degrees is again an action, with a different target
degree. -/
theorem actHom_comp_pieceCast {k : ℕ} (b : ↥(reesGrading I k)) (n : ℤ) {m m' : ℤ}
    (hm : n + (k : ℤ) = m) (e : m = m') :
    actHom I X M b n hm ≫ pieceCast M e = actHom I X M b n (hm.trans e) := by
  rw [actHom, actHom, Category.assoc, pieceCast_pieceCast]

/-- The action is additive in the acting element. -/
theorem actHom_add {k : ℕ} (b b' : ↥(reesGrading I k)) (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    actHom I X M (b + b') n hm = actHom I X M b n hm + actHom I X M b' n hm := by
  rw [actHom, actHom, actHom,
    smulSectionsHom_eval_add M n (k : ℤ) (eval_gradedReesSection_add I X b b'),
    Preadditive.add_comp]

/-- The zero element acts by zero. -/
theorem actHom_zero {k : ℕ} (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    actHom I X M (0 : ↥(reesGrading I k)) n hm = 0 := by
  rw [actHom, smulSectionsHom_eval_zero M n (k : ℤ) (eval_gradedReesSection_zero I X),
    Limits.zero_comp]

/-- Preceding the action by a transport of degrees is again an action, with a different source
degree. -/
theorem pieceCast_comp_actHom {k : ℕ} (b : ↥(reesGrading I k)) {n n' : ℤ} (e : n = n')
    {m : ℤ} (hm : n' + (k : ℤ) = m) (hm' : n + (k : ℤ) = m) :
    pieceCast M e ≫ actHom I X M b n' hm = actHom I X M b n hm' := by
  subst e
  rw [pieceCast_rfl, Category.id_comp]

/-- The unit of `B = ⨁ₙ Iⁿ` acts by the identity, up to the transport identifying the source
and target degrees. -/
theorem actHom_one (n : ℤ) {m : ℤ} (hm : n + ((0 : ℕ) : ℤ) = m) (hn : n = m) :
    actHom I X M (GradedMonoid.GOne.one (A := fun j => ↥(reesGrading I j))) n hm =
      pieceCast M hn := by
  have h1 : smulSectionsHom M n ((0 : ℕ) : ℤ)
        (gradedReesSection I X
          (GradedMonoid.GOne.one (A := fun j => ↥(reesGrading I j)))) ≫
      pieceCast M (add_zero n) = 𝟙 (M.piece n) := by
    rw [smulSectionsHom_congr M n ((0 : ℕ) : ℤ) (eval_gradedReesSection_one I X)]
    exact smulSectionsHom_one M n
  calc actHom I X M (GradedMonoid.GOne.one (A := fun j => ↥(reesGrading I j))) n hm
      = smulSectionsHom M n ((0 : ℕ) : ℤ)
          (gradedReesSection I X
            (GradedMonoid.GOne.one (A := fun j => ↥(reesGrading I j)))) ≫
          pieceCast M (add_zero n) ≫ pieceCast M hn := by
        rw [pieceCast_pieceCast]; exact rfl
    _ = (smulSectionsHom M n ((0 : ℕ) : ℤ)
          (gradedReesSection I X
            (GradedMonoid.GOne.one (A := fun j => ↥(reesGrading I j)))) ≫
          pieceCast M (add_zero n)) ≫ pieceCast M hn := (Category.assoc _ _ _).symm
    _ = pieceCast M hn := by rw [h1, Category.id_comp]

/-- The action of `B = ⨁ₙ Iⁿ` is associative: acting by `b` and then by `b'` is acting by
any homogeneous element whose underlying element of `A` is the product. -/
theorem actHom_comp {k l m : ℕ} (b : ↥(reesGrading I k)) (b' : ↥(reesGrading I l))
    (c : ↥(reesGrading I m)) (hc : reesElt I c = reesElt I b * reesElt I b')
    (hkl : (k : ℤ) + (l : ℤ) = (m : ℤ)) (n : ℤ) {m₁ m₂ : ℤ} (h1 : n + (k : ℤ) = m₁)
    (h2 : m₁ + (l : ℤ) = m₂) (h3 : n + (m : ℤ) = m₂) :
    actHom I X M b n h1 ≫ actHom I X M b' m₁ h2 = actHom I X M c n h3 := by
  have hnij : n + (k : ℤ) + (l : ℤ) = m₂ := by rw [h1, h2]
  calc actHom I X M b n h1 ≫ actHom I X M b' m₁ h2
      = smulSectionsHom M n (k : ℤ) (gradedReesSection I X b) ≫
          pieceCast M h1 ≫ actHom I X M b' m₁ h2 := Category.assoc _ _ _
    _ = smulSectionsHom M n (k : ℤ) (gradedReesSection I X b) ≫
          actHom I X M b' (n + (k : ℤ)) hnij := by
        rw [pieceCast_comp_actHom I X M b' h1 h2 hnij]
    _ = smulSectionsHom M n (k : ℤ) (gradedReesSection I X b) ≫
          smulSectionsHom M (n + (k : ℤ)) (l : ℤ) (gradedReesSection I X b') ≫
            pieceCast M hnij := rfl
    _ = actHom I X M c n h3 :=
        smulSectionsHom_comp M hkl h3 hnij (gradedReesSection I X b)
          (gradedReesSection I X b') (gradedReesSection I X c)
          (castHom_mul_gradedReesSection I X b b' c hc hkl)

/-! ### The graded `B`-module `⨁ₙ Hᵖ(X, Mₙ)` -/

variable (p : ℕ)

/-- `Hᵖ(X, Mₙ)` for a natural number `n`, the degree-`n` piece of the graded `B`-module. -/
abbrev gradedCohomologyPiece (n : ℕ) : Type u :=
  (cohomologyFunctor X p).obj (M.piece (n : ℤ))

/-- `Hᵖ(X, −)` is additive, read on elements. -/
theorem cohomologyFunctor_map_add_apply {P Q : X.left.Modules} (f g : P ⟶ Q)
    (y : (cohomologyFunctor X p).obj P) :
    ((cohomologyFunctor X p).map (f + g)).hom y =
      ((cohomologyFunctor X p).map f).hom y + ((cohomologyFunctor X p).map g).hom y := by
  rw [CategoryTheory.Functor.map_add]
  rfl

/-- `Hᵖ(X, −)` sends the zero morphism to zero, read on elements. -/
theorem cohomologyFunctor_map_zero_apply {P Q : X.left.Modules}
    (y : (cohomologyFunctor X p).obj P) :
    ((cohomologyFunctor X p).map (0 : P ⟶ Q)).hom y = 0 := by
  rw [CategoryTheory.Functor.map_zero]
  rfl

/-- `Hᵖ(X, −)` applied successively to two morphisms with composite `h` is `Hᵖ(X, h)`, read on
elements. -/
private theorem cohomologyFunctor_map_map_apply {P Q R : X.left.Modules} (f : P ⟶ Q) (g : Q ⟶ R)
    (h : P ⟶ R) (e : f ≫ g = h) (y : (cohomologyFunctor X p).obj P) :
    ((cohomologyFunctor X p).map g).hom (((cohomologyFunctor X p).map f).hom y) =
      ((cohomologyFunctor X p).map h).hom y :=
  (cohomologyFunctor_map_comp_apply X p f g y).trans
    (congrArg (fun φ : _ ⟶ _ => ((cohomologyFunctor X p).map φ).hom y) e)

/-- `n + k = k + n`, read in `ℤ` with the right-hand side cast from `ℕ`. -/
theorem degree_add_eq (k n : ℕ) : (n : ℤ) + (k : ℤ) = ((k + n : ℕ) : ℤ) := by push_cast; ring

/-- The action of a homogeneous element of degree `k` of `B = ⨁ₙ Iⁿ` on `Hᵖ(X, Mₙ)`. -/
def gradedCohomologySmul {k n : ℕ} (b : ↥(reesGrading I k))
    (x : gradedCohomologyPiece I X M p n) : gradedCohomologyPiece I X M p (k + n) :=
  ((cohomologyFunctor X p).map (actHom I X M b (n : ℤ) (degree_add_eq k n))).hom x

/-- Two cohomology classes in propositionally equal degrees are equal in `Σ n, Hᵖ(X, Mₙ)` as soon
as one is the transport of the other. -/
theorem sigma_eq_of_pieceCast {m n : ℕ} (e : m = n) {x : gradedCohomologyPiece I X M p m}
    {y : gradedCohomologyPiece I X M p n}
    (h : ((cohomologyFunctor X p).map
        (pieceCast M (congrArg (Nat.cast (R := ℤ)) e))).hom x = y) :
    (⟨m, x⟩ : Σ j, gradedCohomologyPiece I X M p j) = ⟨n, y⟩ := by
  subst e
  refine congrArg (Sigma.mk m) ?_
  rw [← h, pieceCast_rfl]
  exact (cohomologyFunctor_map_id_apply X p x).symm

/-- The graded `B = ⨁ₙ Iⁿ`-module `⨁ₙ Hᵖ(X, Mₙ)`, for an arbitrary graded `𝓑 = ⨁ₙ ℐⁿ`-module
`M`. -/
@[instance_reducible]
def cohomologyGradedModule :
    DirectSum.Gmodule (fun n => ↥(reesGrading I n)) (gradedCohomologyPiece I X M p) where
  smul := gradedCohomologySmul I X M p
  smul_add _ _ _ := map_add _ _ _
  smul_zero _ := map_zero _
  add_smul b b' x :=
    (congrArg (fun φ : _ ⟶ _ => ((cohomologyFunctor X p).map φ).hom x)
      (actHom_add I X M b b' _ (degree_add_eq _ _))).trans
      (cohomologyFunctor_map_add_apply X p _ _ x)
  zero_smul x :=
    (congrArg (fun φ : _ ⟶ _ => ((cohomologyFunctor X p).map φ).hom x)
      (actHom_zero I X M _ (degree_add_eq _ _))).trans
      (cohomologyFunctor_map_zero_apply X p x)
  one_smul := by
    rintro ⟨n, x⟩
    refine sigma_eq_of_pieceCast I X M p (Nat.zero_add n) ?_
    have key : actHom I X M (GradedMonoid.GOne.one (A := fun j => ↥(reesGrading I j)))
          (n : ℤ) (degree_add_eq 0 n) ≫
          pieceCast M (congrArg (Nat.cast (R := ℤ)) (Nat.zero_add n)) =
        𝟙 (M.piece (n : ℤ)) := by
      rw [actHom_comp_pieceCast, actHom_one I X M (n : ℤ) _ rfl]
      exact pieceCast_rfl M rfl
    change ((cohomologyFunctor X p).map
          (pieceCast M (congrArg (Nat.cast (R := ℤ)) (Nat.zero_add n)))).hom
        (((cohomologyFunctor X p).map
          (actHom I X M (GradedMonoid.GOne.one (A := fun j => ↥(reesGrading I j)))
            (n : ℤ) (degree_add_eq 0 n))).hom x) = x
    refine (cohomologyFunctor_map_comp_apply X p _ _ x).trans ?_
    exact (congrArg (fun φ : M.piece (n : ℤ) ⟶ M.piece (n : ℤ) =>
        ((cohomologyFunctor X p).map φ).hom x) key).trans
      (cohomologyFunctor_map_id_apply X p x)
  mul_smul := by
    rintro ⟨k, b⟩ ⟨l, b'⟩ ⟨n, x⟩
    refine sigma_eq_of_pieceCast I X M p (Nat.add_assoc k l n) ?_
    have key : actHom I X M (GradedMonoid.GMul.mul (A := fun j => ↥(reesGrading I j)) b b')
          (n : ℤ) (degree_add_eq (k + l) n) ≫
          pieceCast M (congrArg (Nat.cast (R := ℤ)) (Nat.add_assoc k l n)) =
        actHom I X M b' (n : ℤ) (degree_add_eq l n) ≫
          actHom I X M b ((l + n : ℕ) : ℤ) (degree_add_eq k (l + n)) := by
      rw [actHom_comp_pieceCast]
      refine (actHom_comp I X M b' b
        (GradedMonoid.GMul.mul (A := fun j => ↥(reesGrading I j)) b b') ?_
        (by push_cast; ring) (n : ℤ) (degree_add_eq l n) (degree_add_eq k (l + n)) _).symm
      rw [reesElt_mul, mul_comm]
    change ((cohomologyFunctor X p).map
          (pieceCast M (congrArg (Nat.cast (R := ℤ)) (Nat.add_assoc k l n)))).hom
        (((cohomologyFunctor X p).map
          (actHom I X M (GradedMonoid.GMul.mul (A := fun j => ↥(reesGrading I j)) b b')
            (n : ℤ) (degree_add_eq (k + l) n))).hom x) =
      ((cohomologyFunctor X p).map
          (actHom I X M b ((l + n : ℕ) : ℤ) (degree_add_eq k (l + n)))).hom
        (((cohomologyFunctor X p).map (actHom I X M b' (n : ℤ) (degree_add_eq l n))).hom x)
    refine (cohomologyFunctor_map_comp_apply X p _ _ x).trans ?_
    exact (congrArg (fun φ : M.piece (n : ℤ) ⟶ M.piece ((k + (l + n) : ℕ) : ℤ) =>
        ((cohomologyFunctor X p).map φ).hom x) key).trans
      (cohomologyFunctor_map_comp_apply X p _ _ x).symm

/-- The graded module `⨁ₙ Hᵖ(X, Mₙ)` attached to the graded `𝓑`-module `M` is a finite module
over the Rees algebra `B = ⨁ₙ Iⁿ`. -/
def IsCohomologyReesFiniteOfGradedModule : Prop :=
  letI := cohomologyGradedModule I X M p
  Module.Finite (⨁ n, ↥(reesGrading I n)) (⨁ n, gradedCohomologyPiece I X M p n)

end Act

/-! ### Specialisation at the ideal-power filtration -/

section Bridge

open SheafOfModules.GradedModule

variable (F : X.left.Modules) (p : ℕ)

/-- `⨁ₙ ℐⁿℱ`, as a graded module over the Rees algebra `𝓑 = ⨁ₙ ℐⁿ` of `ℐ = I · 𝒪_X`. -/
abbrev reesFiltrationModule : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X) :=
  reesGradedModule (baseIdealSheaf A I X.hom) F

/-- The identification of the degree-`n` piece of `⨁ₙ ℐⁿℱ` with the `n`-th member of the
ideal-power filtration of `ℱ`, as a morphism. -/
abbrev filtrationPieceIso (n : ℕ) :
    (reesFiltrationModule I X F).piece (n : ℤ) ⟶ idealPowerMod I X F n :=
  submoduleCast X F (reesMultiple_natCast_eq_idealPowerSub I X F n)

/-- The identification of the two models of `ℐⁿℱ`, in the other direction. -/
abbrev filtrationPieceIsoInv (n : ℕ) :
    idealPowerMod I X F n ⟶ (reesFiltrationModule I X F).piece (n : ℤ) :=
  submoduleCast X F (reesMultiple_natCast_eq_idealPowerSub I X F n).symm

/-- Transports along equalities of subsheaves compose. -/
theorem submoduleCast_comp_submoduleCast {P Q R : F.Submodule} (e : P = Q) (e' : Q = R) :
    submoduleCast X F e ≫ submoduleCast X F e' = submoduleCast X F (e.trans e') := by
  subst e; subst e'; exact Category.id_comp _

/-- Transport along an equality of a subsheaf with itself is the identity. -/
theorem submoduleCast_rfl {P : F.Submodule} (e : P = P) :
    submoduleCast X F e = 𝟙 (P.toSheafOfModules : X.left.Modules) := rfl

/-- The two identifications of the models of `ℐⁿℱ` are mutually inverse. -/
theorem filtrationPieceIsoInv_comp (n : ℕ) :
    filtrationPieceIsoInv I X F n ≫ filtrationPieceIso I X F n =
      𝟙 (idealPowerMod I X F n) :=
  (submoduleCast_comp_submoduleCast X F _ _).trans (submoduleCast_rfl X F _)

/-- Transport along an equality of degrees does not change an ambient section of `ℱ`. -/
theorem pieceCast_reesFiltrationModule_coe {d d' : ℤ} (e : d = d') (U : (Opens X.left)ᵒᵖ)
    (y : ((reesFiltrationModule I X F).piece d).val.obj U) :
    (((pieceCast (reesFiltrationModule I X F) e).val.app U) y).1 = (y.1 : F.val.obj U) := by
  subst e; rfl

/-- At `M = ⨁ₙ ℐⁿℱ` the action of a homogeneous element of degree `k` of `B = ⨁ₙ Iⁿ`, read
through the identification of the two models of `ℐⁿℱ`, is the multiplication map
`Stacks.Cohomology.FormalFunctions.idealPowerSmul` by the underlying element of `Iᵏ`. -/
theorem actHom_comp_filtrationPieceIso (k n : ℕ) (b : ↥(reesGrading I k)) :
    actHom I X (reesFiltrationModule I X F) b (n : ℤ) (degree_add_eq k n) ≫
        filtrationPieceIso I X F (k + n) =
      filtrationPieceIso I X F n ≫
        idealPowerSmul I X F (le_refl (k + n)) (reesElt I b) (reesElt_mem I b) := by
  refine cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun U x ↦ ?_)
  have hL : (((actHom I X (reesFiltrationModule I X F) b (n : ℤ)
        (degree_add_eq k n)).val.app U) x).1 =
      baseRingToSections A X U (reesElt I b) • (x.1 : F.val.obj U) :=
    (congrArg (fun z : ((reesFiltrationModule I X F).piece ((k + n : ℕ) : ℤ)).val.obj U => z.1)
      (actHom_app I X (reesFiltrationModule I X F) b (n : ℤ) (degree_add_eq k n) U x)).trans
      ((pieceCast_reesFiltrationModule_coe I X F (degree_add_eq k n) U _).trans
        (smulSectionsHom_reesGradedModule_coe I X F k n (reesElt I b) (reesElt_mem I b) U x))
  refine (submoduleCast_coe X F (reesMultiple_natCast_eq_idealPowerSub I X F (k + n)) U
    (((actHom I X (reesFiltrationModule I X F) b (n : ℤ)
      (degree_add_eq k n)).val.app U) x)).trans ?_
  refine hL.trans ?_
  refine (congrArg (fun z : F.val.obj U => baseRingToSections A X U (reesElt I b) • z)
    (submoduleCast_coe X F (reesMultiple_natCast_eq_idealPowerSub I X F n) U x).symm).trans ?_
  exact (idealPowerSmul_coe I X F (le_refl (k + n)) (reesElt I b) (reesElt_mem I b) U
    (((filtrationPieceIso I X F n).val.app U) x)).symm

/-! #### Quasi-coherence of the pieces -/

/-- A zero sheaf of modules is quasi-coherent. -/
theorem isQuasicoherent_of_isZero {N : X.left.Modules} (h : Limits.IsZero N) :
    N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).prop_of_iso
    ((Stacks.AlgebraicGeometry.HigherDirectImage.isZero_free_pempty
      (R := X.left.ringCatSheaf)).iso h) inferInstance

/-- The zero subsheaf of a sheaf of modules is a zero object. -/
theorem isZero_bot_toSheafOfModules :
    Limits.IsZero ((⊥ : F.Submodule).toSheafOfModules : X.left.Modules) := by
  rw [Limits.IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.Hom.ext
  ext y
  have h : ∀ w : ((⊥ : F.Submodule).toSheafOfModules).val.obj U, w = 0 := fun w =>
    Subtype.ext ((Submodule.mem_bot _).1 ((SheafOfModules.Submodule.bot_obj F U).le w.2))
  exact (h _).trans (h _).symm

/-- In negative degrees the pieces of `⨁ₙ ℐⁿℱ` are zero objects. -/
theorem isZero_piece_reesFiltrationModule_of_neg (n : ℤ) (hn : n < 0) :
    Limits.IsZero ((reesFiltrationModule I X F).piece n : X.left.Modules) := by
  have he : reesMultiple (baseIdealSheaf A I X.hom) n F = ⊥ :=
    reesMultiple_eq_bot_of_neg (baseIdealSheaf A I X.hom) n F hn
  change Limits.IsZero
    ((reesMultiple (baseIdealSheaf A I X.hom) n F).toSheafOfModules : X.left.Modules)
  rw [he]
  exact isZero_bot_toSheafOfModules X F

/-- Every piece of `⨁ₙ ℐⁿℱ` is quasi-coherent when `ℱ` is coherent. -/
theorem isQuasicoherent_piece_reesFiltrationModule [F.IsCoherent] (n : ℤ) :
    ((reesFiltrationModule I X F).piece n).IsQuasicoherent := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
    exact reesMultiple_isQuasicoherent (baseIdealSheaf A I X.hom) m F
  · exact isQuasicoherent_of_isZero X (isZero_piece_reesFiltrationModule_of_neg I X F n hn)

/-! #### The comparison of the two graded modules of cohomology -/

attribute [local instance] cohomologyGradedModule

/-- The graded `B = ⨁ₙ Iⁿ`-module `⨁ₙ Hᵖ(X, Iⁿℱ)` carried by the Rees system
`cohomologyIdealPowerSystem`. -/
abbrev filtrationCohomologyGmodule :
    DirectSum.Gmodule (fun n => ↥(reesGrading I n)) (cohomologyIdealPower I X F p) :=
  (cohomologyIdealPowerSystem I X F p).gmodule

attribute [local instance] filtrationCohomologyGmodule

/-- The degreewise comparison `Hᵖ(X, ℐⁿℱ) ⟶ Hᵖ(X, Iⁿℱ)`, induced by the identification of the
two models of `ℐⁿℱ`. -/
def transferHom (n : ℕ) :
    gradedCohomologyPiece I X (reesFiltrationModule I X F) p n →+
      cohomologyIdealPower I X F p n :=
  (((cohomologyFunctor X p).map (filtrationPieceIso I X F n)).hom).toAddMonoidHom

/-- The degreewise comparison is compatible with the two actions of `B = ⨁ₙ Iⁿ`. -/
theorem transferHom_smul {k n : ℕ} (b : ↥(reesGrading I k))
    (y : gradedCohomologyPiece I X (reesFiltrationModule I X F) p n) :
    transferHom I X F p (k + n)
        (gradedCohomologySmul I X (reesFiltrationModule I X F) p b y) =
      (cohomologyIdealPowerSystem I X F p).gsmul b (transferHom I X F p n y) := by
  change ((cohomologyFunctor X p).map (filtrationPieceIso I X F (k + n))).hom
      (((cohomologyFunctor X p).map (actHom I X (reesFiltrationModule I X F) b (n : ℤ)
        (degree_add_eq k n))).hom y) =
    ((cohomologyFunctor X p).map
        (idealPowerSmul I X F (le_refl (k + n)) (reesElt I b) (reesElt_mem I b))).hom
      (((cohomologyFunctor X p).map (filtrationPieceIso I X F n)).hom y)
  exact (cohomologyFunctor_map_map_apply X p _ _ _
    (actHom_comp_filtrationPieceIso I X F k n b) y).trans
    (cohomologyFunctor_map_comp_apply X p _ _ y).symm

/-- The comparison `⨁ₙ Hᵖ(X, ℐⁿℱ) ⟶ ⨁ₙ Hᵖ(X, Iⁿℱ)`, as an additive map. -/
def transferAddHom :
    (⨁ n, gradedCohomologyPiece I X (reesFiltrationModule I X F) p n) →+
      (⨁ n, cohomologyIdealPower I X F p n) :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun j => cohomologyIdealPower I X F p j) n).comp (transferHom I X F p n)

/-- The comparison on a homogeneous element is the degreewise comparison. -/
theorem transferAddHom_of (n : ℕ)
    (y : gradedCohomologyPiece I X (reesFiltrationModule I X F) p n) :
    transferAddHom I X F p (DirectSum.of _ n y) =
      DirectSum.of _ n (transferHom I X F p n y) :=
  DirectSum.toAddMonoid_of _ n y

/-- The comparison is `B`-linear. -/
theorem transferAddHom_smul (r : ⨁ n, ↥(reesGrading I n))
    (z : ⨁ n, gradedCohomologyPiece I X (reesFiltrationModule I X F) p n) :
    transferAddHom I X F p (r • z) = r • transferAddHom I X F p z := by
  induction r using DirectSum.induction_on with
  | zero => rw [zero_smul, zero_smul, map_zero]
  | of k b =>
      induction z using DirectSum.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | of n y =>
          rw [DirectSum.Gmodule.of_smul_of, transferAddHom_of, transferAddHom_of,
            DirectSum.Gmodule.of_smul_of]
          exact congrArg (DirectSum.of _ (k + n)) (transferHom_smul I X F p b y)
      | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
  | add r r' hr hr' => rw [add_smul, map_add, hr, hr', add_smul]

/-- The comparison `⨁ₙ Hᵖ(X, ℐⁿℱ) ⟶ ⨁ₙ Hᵖ(X, Iⁿℱ)`, as a map of `B = ⨁ₙ Iⁿ`-modules. -/
def transferLinear :
    (⨁ n, gradedCohomologyPiece I X (reesFiltrationModule I X F) p n) →ₗ[⨁ n, ↥(reesGrading I n)]
      (⨁ n, cohomologyIdealPower I X F p n) where
  toFun := transferAddHom I X F p
  map_add' := map_add _
  map_smul' := transferAddHom_smul I X F p

/-- The comparison is surjective. -/
theorem transferAddHom_surjective : Function.Surjective (transferAddHom I X F p) := by
  intro z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n y =>
      refine ⟨DirectSum.of _ n
        (((cohomologyFunctor X p).map (filtrationPieceIsoInv I X F n)).hom y), ?_⟩
      rw [transferAddHom_of]
      refine congrArg (DirectSum.of _ n) ?_
      change ((cohomologyFunctor X p).map (filtrationPieceIso I X F n)).hom
          (((cohomologyFunctor X p).map (filtrationPieceIsoInv I X F n)).hom y) = y
      exact (cohomologyFunctor_map_map_apply X p _ _ _ (filtrationPieceIsoInv_comp I X F n) y).trans
        (cohomologyFunctor_map_id_apply X p y)
  | add z z' hz hz' =>
      obtain ⟨a, ha⟩ := hz
      obtain ⟨a', ha'⟩ := hz'
      exact ⟨a + a', by rw [map_add, ha, ha']⟩

/-- The `B`-linear comparison is surjective. -/
theorem transferLinear_surjective : Function.Surjective (transferLinear I X F p) :=
  transferAddHom_surjective I X F p

/-! #### Finiteness of `⨁ₙ Hᵖ(X, Iⁿℱ)` -/

/-- For `A` Noetherian, `I ⊆ A` an ideal, `f : X → Spec A` proper and `ℱ` coherent, the graded
module `⨁_{n ≥ 0} Hᵖ(X, Iⁿℱ)` is a finite module over the Rees algebra `B = ⨁_{n ≥ 0} Iⁿ` of `I`,
the graded-module structure being the one carried by
`Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem`, provided that `⨁ₙ Hᵖ(X, Mₙ)` is a
finite `B`-module for every quasi-coherent graded `𝓑 = ⨁ₙ ℐⁿ`-module `M` of finite type whose
negative pieces vanish. -/
theorem isCohomologyReesFinite_of_isCoherent [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom) [F.IsCoherent]
    (h0897 : ∀ M : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X),
      IsNoetherianRing A → AlgebraicGeometry.IsProper X.hom → M.IsFiniteType →
        (∀ n : ℤ, (M.piece n).IsQuasicoherent) →
          (∀ n : ℤ, n < 0 → Limits.IsZero (M.piece n : X.left.Modules)) →
            IsCohomologyReesFiniteOfGradedModule I X M p) :
    IsCohomologyReesFinite I X F p := by
  have hft : (reesFiltrationModule I X F).IsFiniteType :=
    isFiniteType_reesGradedModule_of_isCoherent (baseIdealSheaf A I X.hom) F inferInstance
  have hfin : Module.Finite (⨁ n, ↥(reesGrading I n))
      (⨁ n, gradedCohomologyPiece I X (reesFiltrationModule I X F) p n) :=
    h0897 (reesFiltrationModule I X F) inferInstance hX hft
      (isQuasicoherent_piece_reesFiltrationModule I X F)
      (isZero_piece_reesFiltrationModule_of_neg I X F)
  change Module.Finite (⨁ n, ↥(reesGrading I n)) (⨁ n, cohomologyIdealPower I X F p n)
  exact Module.Finite.of_surjective (transferLinear I X F p) (transferLinear_surjective I X F p)

end Bridge

end Stacks.Cohomology.FormalFunctions

end
