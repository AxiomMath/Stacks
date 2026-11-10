module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDesc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleLift

/-!
# The null-homotopy out of a free differential graded module carried by a family of primitives

Let `R` be a sheaf of rings on a site, let `D` be a sheaf of differential graded `R`-algebras, let
`S` be a sheaf of graded sets and let `M` be a right differential graded `D`-module. A family of
homogeneous local sections of `M` indexed by `S` which drops the degree by one — that is, a
`SheafOfModules.GradedGeneratorFamily S (gradedShiftDown M)`, attaching to a local section of
degree `n` a section of `M^{n-1}` — extends to a degreewise family

`α n : D[S]^{n+1} ⟶ M^n`

which is right `D`-linear in the degree-shifted form a map out of a cone consumes, and which is a
null-homotopy of the homomorphism `D[S] ⟶ M` sending each generator to the differential of its
primitive. These are the two hypotheses of
`SheafOfModules.DifferentialGradedModule.ConePackage.desc`, so this file is what turns a family of
primitives into a morphism out of the cone of a map out of `D[S]`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.freeHomotopy` is the degreewise family the primitives
  lift to: the lift of the family to the free graded module, read in degree `n + 1` with its
  target transported from `M^{(n+1)-1}` to `M^n`.

## Main results

* `SheafOfModules.DifferentialGradedModule.freeHomotopy_mul`: **the family is right `D`-linear**,
  in the degree-shifted form the cone consumes. This is the compatibility of the lift with the
  action, read through the shift down by one.
* `SheafOfModules.DifferentialGradedModule.freeHomotopy_generator`: the family sends the
  generator named by a local section to the primitive of that section.
* `SheafOfModules.DifferentialGradedModule.freeHomotopy_delta`: **the family is a null-homotopy
  of the lift of any family `g` of generators whose sections are the differentials of the
  primitives.** Both sides are morphisms out of a piece of the free module, so the identity is
  checked on the presentation; on the summand of a local section `s` of degree `j` with
  coefficient `x` it is the signed Leibniz rule of `M` applied to `μ_s · x`, whose second term
  cancels the term the differential of `D[S]` contributes because the two signs `(-1)^{j-1}` and
  `(-1)^j` are opposite, and whose first term is `d μ_s · x = g_s · x` by hypothesis.

## Implementation notes

The homotopy is the lift of the family of primitives to the free graded module, read with its
target in the shift down by one of `M`: the degree-`n` piece of
`SheafOfModules.DifferentialGradedModule.gradedShiftDown M` is `M^{n-1}`, so the degree-`n + 1`
component of that lift is a map `D[S]^{n+1} ⟶ M^{(n+1)-1}`, and the homotopy is that component
followed by the transport to `M^n`. Every statement below therefore carries transports along
propositionally but not definitionally equal degrees, written through `SheafOfModules.castHom` as
everywhere in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModule.lean`.

The identity `d ∘ α + α ∘ d = g` is proved on the presentation of `D[S]` rather than on the
canonical generators: the computation is then the one of `SheafOfModules.liftAdd_dPres`, with the
closedness hypothesis there replaced by the hypothesis that `g` is the differential of `μ`, and no
separate verification of the right `D`-linearity of the two sides is needed. The right-hand side
is written as the degree-`n + 1` component of `SheafOfModules.liftHom` rather than as a morphism
of differential graded modules, because that is the spelling in which `liftAdd_freeOf` computes
it; `SheafOfModules.dgLiftHom_f` is a definitional equality, so a caller holding a morphism of
differential graded modules built by `SheafOfModules.dgLiftHom` may use it as it stands.

No closedness is assumed of `g`. It follows — `d g_s = d d μ_s = 0` — and is not needed.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w t a m v u

namespace SheafOfModules.DifferentialGradedModule

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Transports along an equality of degrees -/

/-- `(n + 1) - 1 = n`. Named, rather than proved inline by `omega`, so that the transports below
refer to a public constant: an anonymous `by omega` inside the body of a definition or inside a
hypothesis becomes a private auxiliary proof, which a consumer in another module cannot see. -/
theorem degSuccSubOne (n : ℤ) : (n + 1) - 1 = n := by omega

/-- `j = (j - 1) + 1`, named for the same reason as `degSuccSubOne`. -/
theorem degEqSubOneSucc (j : ℤ) : j = (j - 1) + 1 := by omega

/-- Transport of a degreewise family of sheaves of modules along an equality of degrees acts on
local sections as `SheafOfModules.castHom`. -/
theorem homSections_eqToHom (X : ℤ → SheafOfModules.{a} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (y : (X i).val.obj U) :
    homSections (eqToHom (congrArg X h)) U y = castHom X h U y := by
  subst h
  rfl

/-- The differential of a cochain complex of sheaves of modules, read into a transported target
degree. -/
theorem castHom_homSections_d (N : CochainComplex (SheafOfModules.{a} R) ℤ) (p : ℤ) {q q' : ℤ}
    (h : q = q') (U : Cᵒᵖ) (y : (N.X p).val.obj U) :
    castHom N.X h U (homSections (N.d p q) U y) = homSections (N.d p q') U y := by
  subst h
  rfl

/-- The two terms which the signed Leibniz rule of a module and the differential of the free
module contribute in neighbouring degrees cancel, the signs `(-1)^{j-1}` and `(-1)^j` being
opposite. -/
theorem add_negOnePow_zsmul_cancel {G : Type*} [AddCommGroup G] (j : ℤ) (c z : G) :
    c + ((Int.negOnePow (j - 1) : ℤˣ) : ℤ) • z + ((Int.negOnePow j : ℤˣ) : ℤ) • z = c := by
  have h := Int.negOnePow_succ (j - 1)
  rw [show j - 1 + 1 = j from by omega] at h
  rw [add_assoc, ← add_zsmul, h]
  simp

/-! ### Degree `-1` families and homomorphisms into the shift down by one -/

section ShiftDown

variable {A : DifferentialGradedAlgebra.{t, a} R} {K N : DifferentialGradedModule.{t, a, m} A}

/-- **The degreewise family `α n : K^{n+1} ⟶ N^n` carried by a homomorphism of graded modules
from `K` into the shift down by one of `N`.** The degree-`n + 1` piece of `gradedShiftDown N` is
`N^{(n+1)-1}`, so the component of a homomorphism there is a map `K^{n+1} ⟶ N^{(n+1)-1}`, and the
family is that component transported to `N^n`. -/
noncomputable def ofShiftDownHom
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N)) (n : ℤ) :
    K.complex.X (n + 1) ⟶ N.complex.X n :=
  Φ.app (n + 1) ≫ eqToHom (congrArg N.complex.X (degSuccSubOne n))

/-- The family carried by a homomorphism, on local sections. -/
theorem ofShiftDownHom_homSections
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N)) (n : ℤ)
    (U : Cᵒᵖ) (z : (K.complex.X (n + 1)).val.obj U) :
    homSections (ofShiftDownHom Φ n) U z =
      castHom N.complex.X (degSuccSubOne n) U (homSections (Φ.app (n + 1)) U z) :=
  homSections_eqToHom N.complex.X (degSuccSubOne n) U _

/-- **The family carried by a homomorphism of graded modules is right `A`-linear**, in the
degree-shifted form a map out of a cone consumes: the degree `(n + 1) + i` of a product is the
degree `(n + i) + 1` at which the family reads it. -/
theorem ofShiftDownHom_mul
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N)) (n i : ℤ)
    (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U) (y : (A.complex.X i).val.obj U) :
    (ofShiftDownHom Φ (n + i)).val.app U
        (gradedCast (fun q ↦ (K.complex.X q).val.obj U) (add_right_comm n 1 i)
          ((K.mul (n + 1) i).app U x y)) =
      (N.mul n i).app U ((ofShiftDownHom Φ n).val.app U x) y := by
  have hcast : gradedCast (fun q ↦ (K.complex.X q).val.obj U) (add_right_comm n 1 i)
      ((K.mul (n + 1) i).app U x y) =
    castHom (GradedModule.ofDifferentialGraded K).piece (add_right_comm n 1 i) U
      ((GradedModule.ofDifferentialGraded K).smul (n + 1) i U x y) :=
    (castHom_apply (GradedModule.ofDifferentialGraded K).piece (add_right_comm n 1 i) U _).symm
  rw [hcast]
  change homSections (ofShiftDownHom Φ (n + i)) U _ =
    (N.mul n i).app U (homSections (ofShiftDownHom Φ n) U x) y
  refine Eq.trans (ofShiftDownHom_homSections Φ (n + i) U _) ?_
  refine Eq.trans (congrArg
    (fun z => castHom N.complex.X (degSuccSubOne (n + i)) U z)
    ((GradedModule.app_castHom Φ (add_right_comm n 1 i) U _).trans
      (congrArg (fun z => castHom (gradedShiftDown N).piece (add_right_comm n 1 i) U z)
        (Φ.map_smul (n + 1) i U x y)))) ?_
  refine Eq.trans ?_ (congrArg (fun z => (N.mul n i).app U z y)
    (ofShiftDownHom_homSections Φ n U x)).symm
  refine Eq.trans ?_ (Cofree.smul_castHom_left (GradedModule.ofDifferentialGraded N)
    (degSuccSubOne n) U _ y).symm
  refine eq_of_heq (HEq.trans ?_ (heq_castHom (GradedModule.ofDifferentialGraded N).piece
    (show ((n + 1) - 1) + i = n + i by omega) U _).symm)
  exact (heq_castHom N.complex.X (degSuccSubOne (n + i)) U _).trans
    ((heq_castHom (gradedShiftDown N).piece (add_right_comm n 1 i) U _).trans
      (gradedShiftDown_smul_eval_heq N (n + 1) i U _ y))

/-- **The homomorphism of graded modules carried by a right `A`-linear degreewise family.** -/
noncomputable def toShiftDownHom (α : ∀ n : ℤ, K.complex.X (n + 1) ⟶ N.complex.X n)
    (hα : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
        (y : (A.complex.X i).val.obj U),
      (α (n + i)).val.app U (gradedCast (fun q ↦ (K.complex.X q).val.obj U)
          (add_right_comm n 1 i) ((K.mul (n + 1) i).app U x y))
        = (N.mul n i).app U ((α n).val.app U x) y) :
    GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N) where
  app j := eqToHom (congrArg K.complex.X (degEqSubOneSucc j)) ≫ α (j - 1)
  map_smul n i U x y := by
    have happ : ∀ (j : ℤ) (z : (K.complex.X j).val.obj U),
        (eqToHom (congrArg K.complex.X (degEqSubOneSucc j)) ≫ α (j - 1)).val.app U z =
          (α (j - 1)).val.app U (castHom K.complex.X (degEqSubOneSucc j) U z) := fun j z =>
      (comp_val_app _ _ U z).trans (congrArg (fun w => (α (j - 1)).val.app U w)
        (homSections_eqToHom K.complex.X (degEqSubOneSucc j) U z))
    refine Eq.trans (happ (n + i) ((K.mul n i).app U x y)) ?_
    refine Eq.trans ?_ (congrArg (fun z => (gradedShiftDown N).smul n i U z y) (happ n x)).symm
    refine eq_of_heq (HEq.trans ?_ (gradedShiftDown_smul_eval_heq N n i U
      ((α (n - 1)).val.app U (castHom K.complex.X (degEqSubOneSucc n) U x)) y).symm)
    refine HEq.trans ?_ (heq_of_eq (hα (n - 1) i U
      (castHom K.complex.X (degEqSubOneSucc n) U x) y))
    refine heq_dependent_apply
      (fun d : ℤ => fun z : (K.complex.X (d + 1)).val.obj U => (α d).val.app U z)
      (show (n + i) - 1 = (n - 1) + i by omega) ?_
    have h1 : gradedCast (fun q ↦ (K.complex.X q).val.obj U) (add_right_comm (n - 1) 1 i)
          ((K.mul ((n - 1) + 1) i).app U (castHom K.complex.X (degEqSubOneSucc n) U x) y)
        = castHom K.complex.X (add_right_comm (n - 1) 1 i) U
          ((K.mul ((n - 1) + 1) i).app U (castHom K.complex.X (degEqSubOneSucc n) U x) y) :=
      (castHom_apply K.complex.X (add_right_comm (n - 1) 1 i) U _).symm
    have h2 : (K.mul ((n - 1) + 1) i).app U (castHom K.complex.X (degEqSubOneSucc n) U x) y
        = castHom K.complex.X (show n + i = ((n - 1) + 1) + i by omega) U
            ((K.mul n i).app U x y) :=
      Cofree.smul_castHom_left (GradedModule.ofDifferentialGraded K) (degEqSubOneSucc n) U x y
    rw [h1, h2]
    exact (heq_castHom K.complex.X (degEqSubOneSucc (n + i)) U _).trans
      (((heq_castHom K.complex.X (add_right_comm (n - 1) 1 i) U _).trans
        (heq_castHom K.complex.X (show n + i = ((n - 1) + 1) + i by omega) U _)).symm)

/-- A degreewise family of maps between the pieces of the shift down by one, transported along
an equality of its degree, is that family. -/
private theorem eqToHom_comp_piece {k j : ℤ} (hk : k = j)
    (ψ : ∀ m : ℤ, K.complex.X m ⟶ N.complex.X (m - 1))
    (h₁ : K.complex.X j = K.complex.X k)
    (h₂ : N.complex.X (k - 1) = N.complex.X (j - 1)) :
    eqToHom h₁ ≫ ψ k ≫ eqToHom h₂ = ψ j := by
  subst hk
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- A degreewise family transported along an equality of its degree is that family. -/
private theorem eqToHom_comp_shift {k n : ℤ} (hk : k = n)
    (α : ∀ m : ℤ, K.complex.X (m + 1) ⟶ N.complex.X m)
    (h₁ : K.complex.X (n + 1) = K.complex.X (k + 1))
    (h₂ : N.complex.X k = N.complex.X n) :
    eqToHom h₁ ≫ α k ≫ eqToHom h₂ = α n := by
  subst hk
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **`toShiftDownHom` depends only on the family**: the compatibility with the action it carries
is a proposition, so equal families give equal homomorphisms. -/
theorem toShiftDownHom_congr {α α' : ∀ n : ℤ, K.complex.X (n + 1) ⟶ N.complex.X n}
    (h : α = α')
    (hα : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
        (y : (A.complex.X i).val.obj U),
      (α (n + i)).val.app U (gradedCast (fun q ↦ (K.complex.X q).val.obj U)
          (add_right_comm n 1 i) ((K.mul (n + 1) i).app U x y))
        = (N.mul n i).app U ((α n).val.app U x) y)
    (hα' : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
        (y : (A.complex.X i).val.obj U),
      (α' (n + i)).val.app U (gradedCast (fun q ↦ (K.complex.X q).val.obj U)
          (add_right_comm n 1 i) ((K.mul (n + 1) i).app U x y))
        = (N.mul n i).app U ((α' n).val.app U x) y) :
    toShiftDownHom α hα = toShiftDownHom α' hα' := by
  subst h
  rfl

/-- **The family carried by the homomorphism carried by a family is that family.** -/
theorem ofShiftDownHom_toShiftDownHom (α : ∀ n : ℤ, K.complex.X (n + 1) ⟶ N.complex.X n)
    (hα : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
        (y : (A.complex.X i).val.obj U),
      (α (n + i)).val.app U (gradedCast (fun q ↦ (K.complex.X q).val.obj U)
          (add_right_comm n 1 i) ((K.mul (n + 1) i).app U x y))
        = (N.mul n i).app U ((α n).val.app U x) y) (n : ℤ) :
    ofShiftDownHom (toShiftDownHom α hα) n = α n := by
  change (eqToHom (congrArg K.complex.X (degEqSubOneSucc (n + 1))) ≫ α ((n + 1) - 1)) ≫
    eqToHom (congrArg N.complex.X (degSuccSubOne n)) = α n
  rw [Category.assoc]
  exact eqToHom_comp_shift (degSuccSubOne n) α _ _

/-- **The homomorphism carried by the family carried by a homomorphism is that
homomorphism.** -/
theorem toShiftDownHom_ofShiftDownHom
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N))
    (hα : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
        (y : (A.complex.X i).val.obj U),
      (ofShiftDownHom Φ (n + i)).val.app U (gradedCast (fun q ↦ (K.complex.X q).val.obj U)
          (add_right_comm n 1 i) ((K.mul (n + 1) i).app U x y))
        = (N.mul n i).app U ((ofShiftDownHom Φ n).val.app U x) y) :
    toShiftDownHom (ofShiftDownHom Φ) hα = Φ :=
  GradedModule.Hom.ext fun j => by
    change eqToHom (congrArg K.complex.X (degEqSubOneSucc j)) ≫
        Φ.app ((j - 1) + 1) ≫ eqToHom (congrArg N.complex.X (degSuccSubOne (j - 1))) = Φ.app j
    exact eqToHom_comp_piece (degEqSubOneSucc j).symm (fun m => Φ.app m) _ _

end ShiftDown

/-! ### The homotopy carried by a family of primitives -/

section FreeHomotopy

variable [HasWeakSheafify J (Type w)] [HasWeakSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  (S : SheafOfGradedSets.{w} J) (D : DifferentialGradedAlgebra.{t, a} R)
  (M : DifferentialGradedModule.{t, a, max w a} D)
  (μ : GradedGeneratorFamily S (gradedShiftDown M))

/-- **The null-homotopy carried by a family of primitives**: the lift of the family to the free
graded module, read in degree `n + 1` and transported from `M^{(n+1)-1}` to `M^n`. -/
noncomputable def freeHomotopy (n : ℤ) :
    (freeDGModule S D).complex.X (n + 1) ⟶ M.complex.X n :=
  ofShiftDownHom (K := freeDGModule S D)
    (liftHom D.toGradedAlgebra S (gradedShiftDown M) μ) n

/-- The homotopy on local sections: the degree-`n + 1` component of the lift, transported from
`M^{(n+1)-1}` to `M^n`. -/
theorem freeHomotopy_homSections (n : ℤ) (U : Cᵒᵖ)
    (z : ((freeDGModule S D).complex.X (n + 1)).val.obj U) :
    homSections (freeHomotopy S D M μ n) U z =
      castHom M.complex.X (degSuccSubOne n) U
        (homSections ((liftHom D.toGradedAlgebra S (gradedShiftDown M) μ).app (n + 1)) U z) :=
  ofShiftDownHom_homSections _ n U z

/-- The homotopy on the image of the presentation of `D[S]`. -/
theorem freeHomotopy_freeUnit (n : ℤ) (U : Cᵒᵖ)
    (ζ : freeSections D.toGradedAlgebra S (n + 1) U) :
    homSections (freeHomotopy S D M μ n) U
        ((freeUnit D.toGradedAlgebra S (n + 1)).app U ζ) =
      castHom M.complex.X (degSuccSubOne n) U
        (liftAdd D.toGradedAlgebra S (gradedShiftDown M) μ (n + 1) U ζ) :=
  (freeHomotopy_homSections S D M μ n U _).trans
    (congrArg (fun z => castHom M.complex.X (degSuccSubOne n) U z)
      (liftVal_unit D.toGradedAlgebra S (gradedShiftDown M) μ (n + 1) U ζ))

/-- **The homotopy on the summand of the presentation named by a local section of degree `j`**:
the primitive attached to that section, acted on by the coefficient. -/
theorem freeHomotopy_freeOf (n j : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s j) (x : (D.toGradedAlgebra.piece ((n + 1) - j)).val.obj U) :
    homSections (freeHomotopy S D M μ n) U
        ((freeUnit D.toGradedAlgebra S (n + 1)).app U
          (freeOf D.toGradedAlgebra S (n + 1) U j s hs x)) =
      castHom (GradedModule.ofDifferentialGraded M).piece
          (show (j - 1) + ((n + 1) - j) = n by omega) U
        ((GradedModule.ofDifferentialGraded M).smul (j - 1) ((n + 1) - j) U
          (μ.app j U s hs) x) := by
  refine Eq.trans (freeHomotopy_freeUnit S D M μ n U _) ?_
  refine Eq.trans (congrArg (fun z => castHom M.complex.X (degSuccSubOne n) U z)
    (liftAdd_freeOf D.toGradedAlgebra S (gradedShiftDown M) μ (n + 1) U j s hs x)) ?_
  refine eq_of_heq (HEq.trans ?_ (heq_castHom (GradedModule.ofDifferentialGraded M).piece
    (show (j - 1) + ((n + 1) - j) = n by omega) U _).symm)
  refine (heq_castHom M.complex.X (degSuccSubOne n) U _).trans ?_
  exact (heq_castHom (gradedShiftDown M).piece (freeDegAdd (n + 1) j) U _).trans
    (gradedShiftDown_smul_eval_heq M j ((n + 1) - j) U _ x)

/-- **The homotopy sends the generator named by a local section of degree `n + 1` to the primitive
of that section.** -/
theorem freeHomotopy_generator (n : ℤ) (V : Cᵒᵖ) (s : S.sheaf.obj.obj V)
    (hs : S.HasDegree V s (n + 1)) :
    homSections (freeHomotopy S D M μ n) V
        (freeGeneratorSection D.toGradedAlgebra S (n + 1) V s hs) =
      castHom M.complex.X (degSuccSubOne n) V (μ.app (n + 1) V s hs) :=
  (freeHomotopy_homSections S D M μ n V _).trans
    (congrArg (fun z => castHom M.complex.X (degSuccSubOne n) V z)
      (liftHom_generator D.toGradedAlgebra S (gradedShiftDown M) μ (n + 1) V s hs))

/-! ### The right `D`-linearity of the homotopy -/

/-- **The homotopy is right `D`-linear**, in the degree-shifted form a map out of a cone
consumes: the degree `(n + 1) + i` of a product is the degree `(n + i) + 1` at which the homotopy
reads it. -/
theorem freeHomotopy_mul (n i : ℤ) (U : Cᵒᵖ)
    (x : ((freeDGModule S D).complex.X (n + 1)).val.obj U)
    (y : (D.complex.X i).val.obj U) :
    (freeHomotopy S D M μ (n + i)).val.app U
        (gradedCast (fun q ↦ ((freeDGModule S D).complex.X q).val.obj U)
          (show (n + 1) + i = (n + i) + 1 by omega)
          (((freeDGModule S D).mul (n + 1) i).app U x y)) =
      (M.mul n i).app U ((freeHomotopy S D M μ n).val.app U x) y :=
  ofShiftDownHom_mul (K := freeDGModule S D)
    (liftHom D.toGradedAlgebra S (gradedShiftDown M) μ) n i U x y

/-! ### The homotopy identity -/

variable (g : GradedGeneratorFamily S (GradedModule.ofDifferentialGraded M))
  (hg : ∀ (j : ℤ) (V : Cᵒᵖ) (s : S.sheaf.obj.obj V) (hs : S.HasDegree V s j),
    homSections (M.complex.d (j - 1) ((j - 1) + 1)) V (μ.app j V s hs) =
      castHom (GradedModule.ofDifferentialGraded M).piece (degEqSubOneSucc j) V
        (g.app j V s hs))

/-- The lift of `g` on the summand of the presentation named by a local section of degree `j`. -/
theorem liftHom_freeOf (n j : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s j) (x : (D.toGradedAlgebra.piece ((n + 1) - j)).val.obj U) :
    homSections ((liftHom D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g).app
          (n + 1)) U
        ((freeUnit D.toGradedAlgebra S (n + 1)).app U
          (freeOf D.toGradedAlgebra S (n + 1) U j s hs x)) =
      castHom (GradedModule.ofDifferentialGraded M).piece (freeDegAdd (n + 1) j) U
        ((GradedModule.ofDifferentialGraded M).smul j ((n + 1) - j) U (g.app j U s hs) x) :=
  (liftVal_unit D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g (n + 1) U _).trans
    (liftAdd_freeOf D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g (n + 1) U j s hs x)

include hg

/-- **The homotopy identity on the summand of the presentation named by a local section of degree
`j`.** This is the signed Leibniz rule of `M` applied to the product of the primitive of that
section with the coefficient: its second term is cancelled by the term the differential of `D[S]`
contributes, the signs `(-1)^{j-1}` and `(-1)^j` being opposite, and its first term is the section
`g` attaches to that local section, acted on by the coefficient. -/
theorem freeHomotopy_delta_freeOf (n j : ℤ) (U : Cᵒᵖ) (s : S.sheaf.obj.obj U)
    (hs : S.HasDegree U s j) (x : (D.toGradedAlgebra.piece ((n + 1) - j)).val.obj U) :
    homSections (M.complex.d n (n + 1)) U
        (homSections (freeHomotopy S D M μ n) U
          ((freeUnit D.toGradedAlgebra S (n + 1)).app U
            (freeOf D.toGradedAlgebra S (n + 1) U j s hs x)))
      + homSections (freeHomotopy S D M μ (n + 1)) U
          (homSections ((freeDGModule S D).complex.d (n + 1) ((n + 1) + 1)) U
            ((freeUnit D.toGradedAlgebra S (n + 1)).app U
              (freeOf D.toGradedAlgebra S (n + 1) U j s hs x)))
      = castHom (GradedModule.ofDifferentialGraded M).piece (freeDegAdd (n + 1) j) U
          ((GradedModule.ofDifferentialGraded M).smul j ((n + 1) - j) U (g.app j U s hs) x) := by
  have hfirst : (GradedModule.ofDifferentialGraded M).smul ((j - 1) + 1) ((n + 1) - j) U
        (homSections (M.complex.d (j - 1) ((j - 1) + 1)) U (μ.app j U s hs)) x =
      castHom (GradedModule.ofDifferentialGraded M).piece
        (show j + ((n + 1) - j) = ((j - 1) + 1) + ((n + 1) - j) by omega) U
        ((GradedModule.ofDifferentialGraded M).smul j ((n + 1) - j) U (g.app j U s hs) x) :=
    (congrArg (fun z => (GradedModule.ofDifferentialGraded M).smul ((j - 1) + 1) ((n + 1) - j) U
        z x) (hg j U s hs)).trans
      (Cofree.smul_castHom_left (GradedModule.ofDifferentialGraded M)
        (degEqSubOneSucc j) U _ x)
  have hT1 : homSections (M.complex.d n (n + 1)) U
        (homSections (freeHomotopy S D M μ n) U
          ((freeUnit D.toGradedAlgebra S (n + 1)).app U
            (freeOf D.toGradedAlgebra S (n + 1) U j s hs x))) =
      castHom (GradedModule.ofDifferentialGraded M).piece
          (show j + ((n + 1) - j) = n + 1 by omega) U
          ((GradedModule.ofDifferentialGraded M).smul j ((n + 1) - j) U (g.app j U s hs) x)
        + ((Int.negOnePow (j - 1) : ℤˣ) : ℤ) •
            castHom (GradedModule.ofDifferentialGraded M).piece
              (show (j - 1) + (((n + 1) - j) + 1) = n + 1 by omega) U
              ((GradedModule.ofDifferentialGraded M).smul (j - 1) (((n + 1) - j) + 1) U
                (μ.app j U s hs)
                (homSections (D.complex.d ((n + 1) - j) (((n + 1) - j) + 1)) U x)) := by
    refine Eq.trans (congrArg (fun z => homSections (M.complex.d n (n + 1)) U z)
      (freeHomotopy_freeOf S D M μ n j U s hs x)) ?_
    refine Eq.trans (dgD_castHom M (show (j - 1) + ((n + 1) - j) = n by omega)
      (show (j - 1) + ((n + 1) - j) + 1 = n + 1 by omega) U _) ?_
    refine Eq.trans (congrArg (fun z => castHom (GradedModule.ofDifferentialGraded M).piece
        (show (j - 1) + ((n + 1) - j) + 1 = n + 1 by omega) U z)
      (leibniz_ofDifferentialGraded M (j - 1) ((n + 1) - j) U (μ.app j U s hs) x)) ?_
    rw [hfirst, map_add, AddMonoidHom.map_zsmul]
    simp only [Cofree.castHom_castHom]
    rfl
  have hT2 : homSections (freeHomotopy S D M μ (n + 1)) U
        (homSections ((freeDGModule S D).complex.d (n + 1) ((n + 1) + 1)) U
          ((freeUnit D.toGradedAlgebra S (n + 1)).app U
            (freeOf D.toGradedAlgebra S (n + 1) U j s hs x))) =
      ((Int.negOnePow j : ℤˣ) : ℤ) •
        castHom (GradedModule.ofDifferentialGraded M).piece
          (show (j - 1) + (((n + 1) - j) + 1) = n + 1 by omega) U
          ((GradedModule.ofDifferentialGraded M).smul (j - 1) (((n + 1) - j) + 1) U
            (μ.app j U s hs)
            (homSections (D.complex.d ((n + 1) - j) (((n + 1) - j) + 1)) U x)) := by
    refine Eq.trans (congrArg (fun z => homSections (freeHomotopy S D M μ (n + 1)) U z)
      ((homSections_congr (freeDGModule_complex_d S D (n + 1)) U _).trans
        ((freeD_unit S D (n + 1) U _).trans
          (congrArg
            (fun z => (freeUnit D.toGradedAlgebra S ((n + 1) + 1)).app U z)
            (dPres_freeOf S D (n + 1) U j s hs x))))) ?_
    refine Eq.trans (congrArg (fun z => homSections (freeHomotopy S D M μ (n + 1)) U z)
      (freeUnit_zsmul D.toGradedAlgebra S ((n + 1) + 1) U
        ((Int.negOnePow j : ℤˣ) : ℤ) _)) ?_
    refine Eq.trans (AddMonoidHom.map_zsmul (homSections (freeHomotopy S D M μ (n + 1)) U) _ _) ?_
    refine congrArg (fun z => ((Int.negOnePow j : ℤˣ) : ℤ) • z) ?_
    refine Eq.trans (freeHomotopy_freeOf S D M μ (n + 1) j U s hs _) ?_
    refine Eq.trans (congrArg (fun z => castHom (GradedModule.ofDifferentialGraded M).piece
        (show (j - 1) + (((n + 1) + 1) - j) = n + 1 by omega) U z)
      (Cofree.smul_castHom_right (GradedModule.ofDifferentialGraded M)
        (show ((n + 1) - j) + 1 = ((n + 1) + 1) - j by omega) U (μ.app j U s hs)
        (homSections (D.complex.d ((n + 1) - j) (((n + 1) - j) + 1)) U x))) ?_
    exact Cofree.castHom_castHom (GradedModule.ofDifferentialGraded M).piece _ _ U _
  exact (congrArg₂ (fun c b => c + b) hT1 hT2).trans (add_negOnePow_zsmul_cancel j _ _)

/-- **The homotopy identity on the image of the presentation of `D[S]`.** -/
theorem freeHomotopy_delta_freeUnit (n : ℤ) (U : Cᵒᵖ)
    (ζ : freeSections D.toGradedAlgebra S (n + 1) U) :
    homSections (M.complex.d n (n + 1)) U
        (homSections (freeHomotopy S D M μ n) U
          ((freeUnit D.toGradedAlgebra S (n + 1)).app U ζ))
      + homSections (freeHomotopy S D M μ (n + 1)) U
          (homSections ((freeDGModule S D).complex.d (n + 1) ((n + 1) + 1)) U
            ((freeUnit D.toGradedAlgebra S (n + 1)).app U ζ))
      = homSections ((liftHom D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g).app
            (n + 1)) U
          ((freeUnit D.toGradedAlgebra S (n + 1)).app U ζ) := by
  have key :
      ((homSections (M.complex.d n (n + 1)) U).comp
            ((homSections (freeHomotopy S D M μ n) U).comp
              (((freeUnit D.toGradedAlgebra S (n + 1)).app U).hom.toAddMonoidHom))
          + (homSections (freeHomotopy S D M μ (n + 1)) U).comp
              ((homSections ((freeDGModule S D).complex.d (n + 1) ((n + 1) + 1)) U).comp
                (((freeUnit D.toGradedAlgebra S (n + 1)).app U).hom.toAddMonoidHom))) =
        (homSections ((liftHom D.toGradedAlgebra S
              (GradedModule.ofDifferentialGraded M) g).app (n + 1)) U).comp
          (((freeUnit D.toGradedAlgebra S (n + 1)).app U).hom.toAddMonoidHom) := by
    refine freeSections_addHom_ext D.toGradedAlgebra S ?_
    intro j s hs x
    exact (freeHomotopy_delta_freeOf S D M μ g hg n j U s hs x).trans
      (liftHom_freeOf S D M g n j U s hs x).symm
  exact DFunLike.congr_fun key ζ

/-- **The homotopy carried by a family of primitives is a null-homotopy of the lift of any family
`g` of generators whose sections are the differentials of the primitives.** Both sides are
morphisms out of a piece of the free graded module, so the identity is checked on the
presentation. -/
theorem freeHomotopy_delta (n : ℤ) :
    freeHomotopy S D M μ n ≫ M.complex.d n (n + 1)
        + (freeDGModule S D).complex.d (n + 1) ((n + 1) + 1) ≫ freeHomotopy S D M μ (n + 1)
      = (liftHom D.toGradedAlgebra S (GradedModule.ofDifferentialGraded M) g).app (n + 1) :=
  freePiece_hom_ext D.toGradedAlgebra S fun U ζ =>
    freeHomotopy_delta_freeUnit S D M μ g hg n U ζ

end FreeHomotopy

end SheafOfModules.DifferentialGradedModule

end
