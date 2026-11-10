module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit
public import StacksFrontier.AlgebraicGeometry.FinGenFromCover.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineGeneration
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTensorGeneral
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic

/-!
# A twisting over an affine base, assembled from its effect on global sections

Let `S` be an affine scheme, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous pieces
(Situation 01NN), `f : T ⟶ S` a morphism of schemes and `L` an invertible `𝒪_T`-module. A family
of `Γ(S, 𝒪_S)`-linear maps `Γ(S, 𝒜_{id}) ⟶ Γ(T, L^{⊗ i})`, multiplicative across degrees and
carrying the unit of `Γ(S, 𝒜)` to the unit of the Laurent algebra, assembles into a twisting
`ψ : f^*𝒜^{(d)} ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}`, the datum `ψ` of a quadruple of Section 01NS. A twisting
whose sections `ψ(b)` generate `L` has a surjective degree-one component, and so gives a quadruple.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineTwisting.laurentMul` and `algebraMul`: the multiplications of
  the Laurent algebra of `L` and of `𝒜^{(d)}` on global sections.
* `Stacks.AlgebraicGeometry.AffineTwisting.app`: the morphism `f^*𝒜_{id} ⟶ L^{⊗ i}` recovered
  from the degree-`i` linear map.
* `Stacks.AlgebraicGeometry.AffineTwisting.ofSections`: the twisting assembled from the family.
* `Stacks.AlgebraicGeometry.AffineTwisting.quadrupleOfTwisting`: the quadruple of Section 01NS
  assembled from a twisting and the generation condition.

## Main results

* `Stacks.AlgebraicGeometry.AffineTwisting.app_pullbackUnit`: the recovered morphism has the
  prescribed effect on the pullback-unit image of a global section.
* `Stacks.AlgebraicGeometry.AffineTwisting.app_mul` and `app_one`: the multiplicativity and unit
  conditions of a twisting for the recovered family.
* `Stacks.AlgebraicGeometry.AffineTwisting.epi_app_one`: if the nonvanishing opens of the sections
  `ψ(b)` cover `T`, the degree-one component of `ψ` is an epimorphism.

## Implementation notes

`SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace)` and
`AlgebraicGeometry.Scheme.Modules S` are the same type by `rfl`; the crossings of that equality
are made inside the ascribing abbreviations `pieceMod`, `laurentSections`, `laurentMul` and
`algebraMul`, so that no statement mentions a comparison. Writing the statements directly leaves
`rw` unable to see its own patterns, the target not being type-correct at the transparency `rw`
uses.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineTwisting

open Stacks.RingedSpace (structureRingSheaf pullbackFunctor pullbackUnit)
open Stacks.PullbackTensorCoherence (tmul oneSec inv_val_app_apply tensorHom_tmul mulHom_tmul
  pullbackTensorComparison pullbackTensorComparison_pullbackUnit pullbackUnitComparison
  pullbackUnitComparison_oneSec)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom isSheafStruct laurent Twisting)
open RingedSpaceModuleAdjunction (opensMap)

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {T S : Scheme.{u}} (f : T ⟶ S)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- A homogeneous piece of `𝒜`, retyped as an object of `AlgebraicGeometry.Scheme.Modules`. -/
abbrev pieceMod (i : ℤ) : S.Modules := A.piece i

/-- The global sections of `L^{⊗ i}`, read as the sections of `f_*L^{⊗ i}` over `⊤`. -/
abbrev laurentSections (i : ℤ) : Type u :=
  Γ(AffineHomRecovery.pushforward f ((laurent L).piece i), ⊤)

/-- The multiplication of the Laurent algebra of `L` in the degrees `i` and `j`, read on the
global sections. -/
def laurentMul (i j : ℤ) (x : laurentSections f L i) (y : laurentSections f L j) :
    laurentSections f L (i + j) :=
  ((laurent L).mul i j).app ((opensMap (ringedSpaceHom f)).op.obj (op ⊤)) x y

/-- The unit of the Laurent algebra of `L`, read on the global sections. -/
def laurentOne : laurentSections f L 0 :=
  (laurent L).one.eval ((opensMap (ringedSpaceHom f)).op.obj (op ⊤))

/-- The multiplication of the `d`-th Veronese regrading of `𝒜` in the degrees `i` and `j`, read
on the global sections: the multiplication of `𝒜` in the degrees `id` and `jd`, transported
along `id + jd = (i + j)d`. -/
def algebraMul (i j : ℤ) (s : Γ(pieceMod A (i * d), ⊤)) (t : Γ(pieceMod A (j * d), ⊤)) :
    Γ(pieceMod A ((i + j) * d), ⊤) :=
  (eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))).val.app (op ⊤)
    ((A.mul (i * d) (j * d)).app (op ⊤) s t)

/-- The unit of the `d`-th Veronese regrading of `𝒜`, read on the global sections: the unit of
`𝒜`, transported along `0 = 0 · d`. -/
def algebraOne : Γ(pieceMod A (0 * d), ⊤) :=
  (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))).val.app (op ⊤) (A.one.eval (op ⊤))

/-- The multiplication of the Laurent algebra on global sections vanishes on a zero left
factor. -/
theorem laurentMul_zero_left (i j : ℤ) (y : laurentSections f L j) :
    laurentMul f L i j 0 y = 0 := by
  change ((laurent L).mul i j).app ((opensMap (ringedSpaceHom f)).op.obj (op ⊤)) 0 y = 0
  rw [map_zero]
  rfl

/-- The multiplication of the Laurent algebra on global sections vanishes on a zero right
factor. -/
theorem laurentMul_zero_right (i j : ℤ) (x : laurentSections f L i) :
    laurentMul f L i j x 0 = 0 := by
  change ((laurent L).mul i j).app ((opensMap (ringedSpaceHom f)).op.obj (op ⊤)) x 0 = 0
  rw [map_zero]

/-- The unit of the Laurent algebra, on global sections, is the function `1`. -/
theorem laurentOne_eq_one : laurentOne f L = (1 : Γ(T, ⊤)) := rfl

/-- The multiplication of the `d`-th Veronese regrading of `𝒜` on global sections vanishes on a
zero left factor. -/
theorem algebraMul_zero_left (i j : ℤ) (t : Γ(pieceMod A (j * d), ⊤)) :
    algebraMul A d i j 0 t = 0 := by
  change (eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))).val.app (op ⊤)
    ((A.mul (i * d) (j * d)).app (op ⊤) 0 t) = 0
  rw [map_zero]
  exact map_zero _

/-- The multiplication of the `d`-th Veronese regrading of `𝒜` on global sections vanishes on a
zero right factor. -/
theorem algebraMul_zero_right (i j : ℤ) (s : Γ(pieceMod A (i * d), ⊤)) :
    algebraMul A d i j s 0 = 0 := by
  change (eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))).val.app (op ⊤)
    ((A.mul (i * d) (j * d)).app (op ⊤) s 0) = 0
  rw [map_zero, map_zero]

variable (hqc : ∀ i : ℤ, (pieceMod A i).IsQuasicoherent)
  (φ : ∀ i : ℤ, Γ(pieceMod A (i * d), ⊤) →ₗ[Γ(S, ⊤)] laurentSections f L i)

/-- The morphism `f^*𝒜_{id} ⟶ L^{⊗ i}` recovered from the degree-`i` linear map on global
sections by `Stacks.AlgebraicGeometry.AffineHomRecovery.homEquiv`. -/
def app [IsAffine S] (i : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i :=
  letI := hqc (i * d)
  (AffineHomRecovery.homEquiv f (pieceMod A (i * d)) ((laurent L).piece i)).symm (φ i)

/-- The recovered morphism has the prescribed effect on the pullback-unit image of a global
section. -/
theorem app_pullbackUnit [IsAffine S] (i : ℤ) (x : Γ(pieceMod A (i * d), ⊤)) :
    (app f A d L hqc φ i).val.app ((opensMap (ringedSpaceHom f)).op.obj (op ⊤))
        (pullbackUnit (ringedSpaceHom f) (A.piece (i * d)) (op ⊤) x) =
      φ i x := by
  have := hqc (i * d)
  have h : AffineHomRecovery.sectionsMap f (pieceMod A (i * d)) ((laurent L).piece i)
      (app f A d L hqc φ i) = φ i :=
    (AffineHomRecovery.homEquiv f (pieceMod A (i * d)) ((laurent L).piece i)).apply_symm_apply _
  exact (SheafOfModules.GradedAlgebra.homEquiv_val_app (ringedSpaceHom f)
    (app f A d L hqc φ i) (op ⊤) x).symm.trans (DFunLike.congr_fun h x)

/-- An invertible morphism of sheaves of modules sends back a section to its preimage. -/
private theorem inv_val_app_eq_of_val_app_eq
    {M N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)} (θ : M ⟶ N) [IsIso θ]
    (U : (TopologicalSpace.Opens T.toRingedSpace.carrier)ᵒᵖ)
    {x : M.val.obj U} {y : N.val.obj U} (h : θ.val.app U x = y) : (inv θ).val.app U y = x :=
  (congrArg _ h.symm).trans (inv_val_app_apply _ _ _)

/-- The value of `(ψ_i ⊗ ψ_j) ≫ mul` on the pure tensor of the pullback-unit images of two
global sections: the product, in the Laurent algebra, of the two prescribed values. -/
theorem tensorHom_mulSheaf_pullbackTmul [IsAffine S] (i j : ℤ)
    (s : Γ(pieceMod A (i * d), ⊤)) (t : Γ(pieceMod A (j * d), ⊤)) :
    (MonoidalCategoryStruct.tensorHom (app f A d L hqc φ i) (app f A d L hqc φ j) ≫
          (laurent L).mulSheaf i j).val.app
        ((opensMap (ringedSpaceHom f)).op.obj (op ⊤))
        (AffineTensorGeneral.pullbackTmul f (pieceMod A (i * d)) (pieceMod A (j * d)) s t) =
      laurentMul f L i j (φ i s) (φ j t) := by
  have h : (MonoidalCategoryStruct.tensorHom (app f A d L hqc φ i)
          (app f A d L hqc φ j)).val.app ((opensMap (ringedSpaceHom f)).op.obj (op ⊤))
        (AffineTensorGeneral.pullbackTmul f (pieceMod A (i * d)) (pieceMod A (j * d)) s t) =
      tmul T.toRingedSpace ((laurent L).piece i) ((laurent L).piece j)
        ((opensMap (ringedSpaceHom f)).op.obj (op ⊤)) (φ i s) (φ j t) := by
    refine (tensorHom_tmul (app f A d L hqc φ i) (app f A d L hqc φ j)
      ((opensMap (ringedSpaceHom f)).op.obj (op ⊤)) _ _).trans ?_
    rw [app_pullbackUnit, app_pullbackUnit]
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  rw [h]
  exact mulHom_tmul (laurent L) i j ((opensMap (ringedSpaceHom f)).op.obj (op ⊤))
    (φ i s) (φ j t)

/-- The value, on the same pure tensor, of the other side of the multiplicativity equation: the
prescribed value in degree `i + j` on the product of the two global sections. -/
theorem comparison_map_app_pullbackTmul [IsAffine S] (i j : ℤ)
    (s : Γ(pieceMod A (i * d), ⊤)) (t : Γ(pieceMod A (j * d), ⊤)) :
    (inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d))) ≫
            (pullbackFunctor (ringedSpaceHom f)).map
              (A.mulSheaf (i * d) (j * d) ≫
                eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
              app f A d L hqc φ (i + j)).val.app
        ((opensMap (ringedSpaceHom f)).op.obj (op ⊤))
        (AffineTensorGeneral.pullbackTmul f (pieceMod A (i * d)) (pieceMod A (j * d)) s t) =
      φ (i + j) (algebraMul A d i j s t) := by
  have hc : (inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d))
            (A.piece (j * d)))).val.app ((opensMap (ringedSpaceHom f)).op.obj (op ⊤))
          (AffineTensorGeneral.pullbackTmul f (pieceMod A (i * d)) (pieceMod A (j * d)) s t) =
        pullbackUnit (ringedSpaceHom f) (A.piece (i * d) ⊗ A.piece (j * d)) (op ⊤)
          (tmul S.toRingedSpace (A.piece (i * d)) (A.piece (j * d)) (op ⊤) s t) :=
    inv_val_app_eq_of_val_app_eq _ _ (pullbackTensorComparison_pullbackUnit (ringedSpaceHom f)
      (A.piece (i * d)) (A.piece (j * d)) (op ⊤) s t)
  have hm : ((pullbackFunctor (ringedSpaceHom f)).map
            (A.mulSheaf (i * d) (j * d) ≫
              eqToHom (congrArg A.piece
                (by ring : i * d + j * d = (i + j) * d)))).val.app
          ((opensMap (ringedSpaceHom f)).op.obj (op ⊤))
          (pullbackUnit (ringedSpaceHom f) (A.piece (i * d) ⊗ A.piece (j * d)) (op ⊤)
            (tmul S.toRingedSpace (A.piece (i * d)) (A.piece (j * d)) (op ⊤) s t)) =
        pullbackUnit (ringedSpaceHom f) (A.piece ((i + j) * d)) (op ⊤)
          (algebraMul A d i j s t) :=
    (Stacks.RingedSpace.pullbackUnit_naturality (ringedSpaceHom f) _ (op ⊤) _).trans
      (congrArg (pullbackUnit (ringedSpaceHom f) (A.piece ((i + j) * d)) (op ⊤))
        ((SheafOfModules.comp_val_app_apply _ _ _ _).trans
          (congrArg ((eqToHom (congrArg A.piece
              (by ring : i * d + j * d = (i + j) * d))).val.app (op ⊤))
            (mulHom_tmul A (i * d) (j * d) (op ⊤) s t))))
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  rw [hc, SheafOfModules.comp_val_app_apply]
  exact (congrArg ((app f A d L hqc φ (i + j)).val.app
    ((opensMap (ringedSpaceHom f)).op.obj (op ⊤))) hm).trans
      (app_pullbackUnit f A d L hqc φ (i + j) _)

/-- If the linear maps on global sections are multiplicative across degrees, the assembled family
satisfies the multiplicativity condition of a twisting. -/
theorem app_mul [IsAffine S]
    (hmul : ∀ (i j : ℤ) (s : Γ(pieceMod A (i * d), ⊤)) (t : Γ(pieceMod A (j * d), ⊤)),
      laurentMul f L i j (φ i s) (φ j t) = φ (i + j) (algebraMul A d i j s t))
    (i j : ℤ) :
    MonoidalCategoryStruct.tensorHom (app f A d L hqc φ i) (app f A d L hqc φ j) ≫
        (laurent L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (A.mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
        app f A d L hqc φ (i + j) := by
  have := hqc (i * d)
  have := hqc (j * d)
  refine AffineTensorGeneral.tensor_hom_ext_of_sections f (pieceMod A (i * d))
    (pieceMod A (j * d)) ((laurent L).piece (i + j)) fun s t => ?_
  refine (tensorHom_mulSheaf_pullbackTmul f A d L hqc φ i j s t).trans ?_
  exact (hmul i j s t).trans (comparison_map_app_pullbackTmul f A d L hqc φ i j s t).symm

/-! ### The unit -/

/-- A global section of a sheaf of modules on a scheme is determined by its value over `⊤`. -/
theorem sections_eq_of_eval_top (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    (σ τ : M.sections) (h : σ.eval (op ⊤) = τ.eval (op ⊤)) : σ = τ := by
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  have hσ := σ.property (homOfLE (le_top (a := U.unop))).op
  have hτ := τ.property (homOfLE (le_top (a := U.unop))).op
  rw [← hσ, ← hτ]
  exact congrArg _ h

/-- The global unit of `f^*𝒜`, read on the unit section over `⊤`: the pullback-unit image of the
global unit of `𝒜`. -/
theorem pullbackOne_val_app_oneSec :
    (Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A).val.app (op ⊤)
        (oneSec T.toRingedSpace (op ⊤)) =
      pullbackUnit (ringedSpaceHom f) (A.piece 0) (op ⊤) (A.one.eval (op ⊤)) := by
  have hinv : (inv (pullbackUnitComparison (ringedSpaceHom f))).val.app (op ⊤)
        (oneSec T.toRingedSpace (op ⊤)) =
      pullbackUnit (ringedSpaceHom f)
        (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))) (op ⊤)
        (oneSec S.toRingedSpace (op ⊤)) :=
    inv_val_app_eq_of_val_app_eq _ _ (pullbackUnitComparison_oneSec (ringedSpaceHom f) (op ⊤))
  rw [Stacks.PullbackStrictUnit.pullbackOne_eq, SheafOfModules.comp_val_app_apply, hinv]
  exact (Stacks.RingedSpace.pullbackUnit_naturality (ringedSpaceHom f)
    (SheafOfModules.GradedAlgebra.oneHom A) (op ⊤) _).trans
      (congrArg (pullbackUnit (ringedSpaceHom f) (A.piece 0) (op ⊤))
        (Stacks.PullbackTensorCoherence.oneMorphism_val_app_oneSec A (op ⊤)))

/-- If the degree-zero linear map on global sections carries the unit of `𝒜` to the unit of the
Laurent algebra, the assembled family satisfies the unit condition of a twisting. -/
theorem app_one [IsAffine S] (hone : φ 0 (algebraOne A d) = laurentOne f L) :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
        app f A d L hqc φ 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent L) := by
  have h2 : ((pullbackFunctor (ringedSpaceHom f)).map
            (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d)))).val.app (op ⊤)
          (pullbackUnit (ringedSpaceHom f) (A.piece 0) (op ⊤) (A.one.eval (op ⊤))) =
        pullbackUnit (ringedSpaceHom f) (A.piece (0 * d)) (op ⊤) (algebraOne A d) :=
    Stacks.RingedSpace.pullbackUnit_naturality (ringedSpaceHom f) _ (op ⊤) _
  refine (SheafOfModules.unitHomEquiv ((laurent L).piece 0)).injective
    (sections_eq_of_eval_top ((laurent L).piece 0) _ _ ?_)
  rw [Stacks.PullbackTensorCoherence.unitHomEquiv_eval,
    Stacks.PullbackTensorCoherence.unitHomEquiv_eval, SheafOfModules.comp_val_app_apply,
    pullbackOne_val_app_oneSec]
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine Eq.trans (congrArg ((app f A d L hqc φ 0).val.app (op ⊤)) h2) ?_
  exact ((app_pullbackUnit f A d L hqc φ 0 (algebraOne A d)).trans hone).trans
    (Stacks.PullbackTensorCoherence.oneMorphism_val_app_oneSec (laurent L) (op ⊤)).symm

/-! ### The twisting -/

/-- Let `S` be an affine scheme, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous pieces
(Situation 01NN), `f : T ⟶ S` an arbitrary morphism of schemes and `L` an invertible `𝒪_T`-module.
A family of `Γ(S, 𝒪_S)`-linear maps `Γ(S, 𝒜_{id}) ⟶ Γ(T, L^{⊗ i})`, one for each integer `i`, which
is multiplicative across degrees and carries the unit of `𝒜` to the unit of the Laurent algebra of
`L`, is the datum `ψ` of a quadruple of Section 01NS: the morphisms of sheaves of modules
`f^*𝒜_{id} ⟶ L^{⊗ i}` it determines satisfy the multiplicativity and the unit condition of a
twisting. -/
def ofSections [IsAffine S]
    (hmul : ∀ (i j : ℤ) (s : Γ(pieceMod A (i * d), ⊤)) (t : Γ(pieceMod A (j * d), ⊤)),
      laurentMul f L i j (φ i s) (φ j t) = φ (i + j) (algebraMul A d i j s t))
    (hone : φ 0 (algebraOne A d) = laurentOne f L) :
    Twisting f A d L where
  app i := app f A d L hqc φ i
  app_mul i j := app_mul f A d L hqc φ hmul i j
  app_one := app_one f A d L hqc φ hone

/-- The homogeneous components of the assembled twisting are the recovered morphisms. -/
@[simp]
theorem ofSections_app [IsAffine S]
    (hmul : ∀ (i j : ℤ) (s : Γ(pieceMod A (i * d), ⊤)) (t : Γ(pieceMod A (j * d), ⊤)),
      laurentMul f L i j (φ i s) (φ j t) = φ (i + j) (algebraMul A d i j s t))
    (hone : φ 0 (algebraOne A d) = laurentOne f L) (i : ℤ) :
    (ofSections f A d L hqc φ hmul hone).app i = app f A d L hqc φ i :=
  rfl

/-- The assembled twisting realises the prescribed linear maps on global sections. -/
theorem ofSections_app_pullbackUnit [IsAffine S]
    (hmul : ∀ (i j : ℤ) (s : Γ(pieceMod A (i * d), ⊤)) (t : Γ(pieceMod A (j * d), ⊤)),
      laurentMul f L i j (φ i s) (φ j t) = φ (i + j) (algebraMul A d i j s t))
    (hone : φ 0 (algebraOne A d) = laurentOne f L) (i : ℤ)
    (x : Γ(pieceMod A (i * d), ⊤)) :
    ((ofSections f A d L hqc φ hmul hone).app i).val.app
        ((opensMap (ringedSpaceHom f)).op.obj (op ⊤))
        (pullbackUnit (ringedSpaceHom f) (A.piece (i * d)) (op ⊤) x) =
      φ i x :=
  app_pullbackUnit f A d L hqc φ i x

/-! ### Generation forces the degree-one component to be surjective -/

/-- If the nonvanishing opens of the sections `ψ(b)` cover `T`, the morphism
`𝒪_T^{(Γ(S,𝒜_{1·d}))} ⟶ L` whose components are these sections is an epimorphism. -/
theorem epi_twistingFreeHom (ψ : Twisting f A d L)
    (hgen : (⨆ b : (A.piece d).val.obj (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)),
        Stacks.NonvanishingOpen.nonvanishingOpen T L
          (RelativeProjQcohSheaf.Twisting.degreeOneSectionHom ψ b)) = ⊤) :
    Epi (RelativeProjQcohSheaf.Twisting.freeHom ψ) := by
  have : Stacks.Ample.IsInvertibleModule T L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ ‹_›
  have hcov : ∀ x : T, ∃ a : (A.piece (1 * d)).sections,
      x ∈ Stacks.Ample.nonvanishingLocus (X := T) L
        ((L.freeHomEquiv (RelativeProjQcohSheaf.Twisting.freeHom ψ) a).eval
          (op (⊤ : TopologicalSpace.Opens T.toRingedSpace.carrier))) := by
    intro x
    have hx : x ∈ (⨆ b : (A.piece d).val.obj
        (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)),
          Stacks.NonvanishingOpen.nonvanishingOpen T L
            (RelativeProjQcohSheaf.Twisting.degreeOneSectionHom ψ b)) := by
      rw [hgen]; trivial
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨(Stacks.NonvanishingSpelling.sectionsEquiv S (pieceMod A (1 * d))).symm
      ((eqToHom (congrArg A.piece (one_mul d).symm) : A.piece d ⟶ A.piece (1 * d)).val.app
        (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)) b), ?_⟩
    have hsec : ((Stacks.NonvanishingSpelling.sectionsEquiv S (pieceMod A (1 * d))).symm
          ((eqToHom (congrArg A.piece (one_mul d).symm) :
              A.piece d ⟶ A.piece (1 * d)).val.app
            (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)) b)).eval
          (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)) =
        (eqToHom (congrArg A.piece (one_mul d).symm) :
            A.piece d ⟶ A.piece (1 * d)).val.app
          (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)) b :=
      (Stacks.NonvanishingSpelling.sectionsEquiv S (pieceMod A (1 * d))).apply_symm_apply _
    have hid : (eqToHom (congrArg A.piece (one_mul d).symm) : A.piece d ⟶ A.piece (1 * d)) ≫
        (eqToHom (congrArg A.piece (one_mul d)) : A.piece (1 * d) ⟶ A.piece d) =
        𝟙 (A.piece d) := by
      rw [eqToHom_trans, eqToHom_refl]
    have hcast : (eqToHom (congrArg A.piece (one_mul d)) :
          A.piece (1 * d) ⟶ A.piece d).val.app
          (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier))
          ((eqToHom (congrArg A.piece (one_mul d).symm) :
              A.piece d ⟶ A.piece (1 * d)).val.app
            (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)) b) = b := by
      rw [← SheafOfModules.comp_val_app_apply, hid]
      rfl
    have key : (L.freeHomEquiv (RelativeProjQcohSheaf.Twisting.freeHom ψ)
            ((Stacks.NonvanishingSpelling.sectionsEquiv S (pieceMod A (1 * d))).symm
              ((eqToHom (congrArg A.piece (one_mul d).symm) :
                  A.piece d ⟶ A.piece (1 * d)).val.app
                (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)) b))).eval
          (op (⊤ : TopologicalSpace.Opens T.toRingedSpace.carrier)) =
        RelativeProjQcohSheaf.Twisting.degreeOneSectionHom ψ b :=
      ((RelativeProjQcohSheaf.Twisting.eval_freeHomEquiv ψ _).trans
        (congrArg (fun y : (A.piece (1 * d)).val.obj
              (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)) =>
            RelativeProjQcohSheaf.Twisting.degreeOneSectionHom ψ
              ((eqToHom (congrArg A.piece (one_mul d)) :
                  A.piece (1 * d) ⟶ A.piece d).val.app
                (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)) y))
          hsec)).trans
        (congrArg (RelativeProjQcohSheaf.Twisting.degreeOneSectionHom ψ) hcast)
    have hb' : x ∈ Stacks.Ample.nonvanishingLocus (X := T) L
        (RelativeProjQcohSheaf.Twisting.degreeOneSectionHom ψ b) := hb
    exact Eq.mpr (congrArg (fun z : L.val.obj
        (op (⊤ : TopologicalSpace.Opens T.toRingedSpace.carrier)) =>
      x ∈ Stacks.Ample.nonvanishingLocus (X := T) L z) key) hb'
  have hepi : Epi (L.freeHomEquiv.symm
      (L.freeHomEquiv (RelativeProjQcohSheaf.Twisting.freeHom ψ))) := by
    refine (AlgebraicGeometry.generates_iff_stalkwise_generates T.ringCatSheaf L _).mpr fun x => ?_
    obtain ⟨a, ha⟩ := hcov x
    exact Stacks.FinGenFromCover.span_eq_top_of_mem_nonvanishingLocus L
      (fun a' => (L.freeHomEquiv (RelativeProjQcohSheaf.Twisting.freeHom ψ) a').eval (op ⊤)) ha
  rwa [Equiv.symm_apply_apply] at hepi

/-- If the nonvanishing opens of the global sections `ψ(b)` of `L`, `b` a global section of `𝒜_d`,
cover `T`, then the degree-one component `ψ_1 : f^*𝒜_d ⟶ L^{⊗ 1}` of the twisting is an
epimorphism. -/
theorem epi_app_one (ψ : Twisting f A d L)
    (hgen : (⨆ b : (A.piece d).val.obj (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)),
        Stacks.NonvanishingOpen.nonvanishingOpen T L
          (RelativeProjQcohSheaf.Twisting.degreeOneSectionHom ψ b)) = ⊤) :
    Epi (ψ.app 1) := by
  have h1 : Epi (RelativeProjQcohSheaf.pullbackGenHom f (A.piece (1 * d)) ≫
      ψ.app 1 ≫ (RelativeProjQcohSheaf.Twisting.laurentOneIso L).hom) :=
    epi_twistingFreeHom f A d L ψ hgen
  have h2 : Epi (ψ.app 1 ≫ (RelativeProjQcohSheaf.Twisting.laurentOneIso L).hom) :=
    epi_of_epi (RelativeProjQcohSheaf.pullbackGenHom f (A.piece (1 * d))) _
  have h3 : ψ.app 1 =
      (ψ.app 1 ≫ (RelativeProjQcohSheaf.Twisting.laurentOneIso L).hom) ≫
        (RelativeProjQcohSheaf.Twisting.laurentOneIso L).inv := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h3]
  exact epi_comp _ _

/-- The quadruple of Section 01NS with invertible module `L` and twisting `ψ`, for a twisting whose
sections `ψ(b)` generate `L`. -/
def quadrupleOfTwisting (ψ : Twisting f A d L)
    (hgen : (⨆ b : (A.piece d).val.obj (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)),
        Stacks.NonvanishingOpen.nonvanishingOpen T L
          (RelativeProjQcohSheaf.Twisting.degreeOneSectionHom ψ b)) = ⊤) :
    RelativeProjQcohSheaf.Quadruple f A d where
  L := L
  isInvertible := inferInstance
  twisting := ψ
  epi_app_one := epi_app_one f A d L ψ hgen

/-- The invertible module of the assembled quadruple is `L`. -/
@[simp]
theorem quadrupleOfTwisting_L (ψ : Twisting f A d L)
    (hgen : (⨆ b : (A.piece d).val.obj (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)),
        Stacks.NonvanishingOpen.nonvanishingOpen T L
          (RelativeProjQcohSheaf.Twisting.degreeOneSectionHom ψ b)) = ⊤) :
    (quadrupleOfTwisting f A d L ψ hgen).L = L :=
  rfl

/-- The twisting of the assembled quadruple is `ψ`. -/
@[simp]
theorem quadrupleOfTwisting_twisting (ψ : Twisting f A d L)
    (hgen : (⨆ b : (A.piece d).val.obj (op (⊤ : TopologicalSpace.Opens S.toRingedSpace.carrier)),
        Stacks.NonvanishingOpen.nonvanishingOpen T L
          (RelativeProjQcohSheaf.Twisting.degreeOneSectionHom ψ b)) = ⊤) :
    (quadrupleOfTwisting f A d L ψ hgen).twisting = ψ :=
  rfl

end Stacks.AlgebraicGeometry.AffineTwisting

end
