module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDesc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeShiftSplitting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftCommutator

/-!
# The pullback of right differential graded modules commutes with cones

Let `f` be a morphism of ringed sites and let `φ : ℬ ⟶ f_*𝒜` be a semilinear homomorphism of
sheaves of differential graded algebras. For a pullback `f^*` of right differential graded
`ℬ`-modules, given by its universal property, and a homomorphism `ψ : ℳ ⟶ ℳ₂`, the cone of the
pullback of `ψ` is the pullback of the cone of `ψ`:

`C(f^*ψ) ≅ f^*C(ψ)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.PullbackData.coneIso`: **the cone of the pullback of
  `ψ` is the pullback of the cone of `ψ`**, as right differential graded `𝒜`-modules, and
  `PullbackData.coneComplexIso`: the same as complexes of sheaves of modules.
* `CategoryTheory.Limits.biprod.isIso_desc`: a morphism out of a binary biproduct given by two
  components is an isomorphism as soon as the two components split it.

## Implementation notes

The comparison goes out of the cone of `f^*ψ`, because that is the direction in which the cone
has a universal property: `ConePackage.desc` builds a homomorphism out of `C(χ)` from a
homomorphism out of the target of `χ` together with a null-homotopy of the composite. Here the
homomorphism is the pullback of the cone's inclusion and the null-homotopy is the pullback of the
cone's degreewise section, which is a null-homotopy of `ψ` followed by the inclusion
(`ConePackage.sectionFamily_d`).

The degreewise section is a right-linear family of degree `-1`, not a homomorphism of
differential graded modules, so the pullback *functor* cannot be applied to it;
`PullbackData.gradedShiftMap` is what transports it, and
`PullbackData.gradedShiftMap_shiftDiffCommutator` is what says the transport still has the
pullback of `ψ ≫ inclusion` for its commutator with the differentials, so that the transported
family is still a null-homotopy.

Invertibility is degreewise, and it is the five splitting relations of
`DifferentialGradedConeShiftSplitting.lean` transported: the cone is degreewise the biproduct of
its source raised by one and its target, the images of the degreewise section and of the
inclusion are the two components of a map out of that biproduct, and the images of the first
coordinate and of the degreewise retraction are the two components of its inverse. The transport
preserves composites, sums and zero (`PullbackData.gradedShiftMap_shiftComp`,
`gradedShiftMap_add`, `gradedShiftMap_zero`), which is all the five relations need.

No shift of a differential graded module appears anywhere: the degreewise splitting is written as
right-linear families of degree `±1`, which is what `gradedShiftMap` accepts, and the pullback has
no comparison with the chosen shift of `DifferentialGradedCone.lean`.

The comparison needs no hypothesis on the pullback beyond its universal property: no continuity,
smallness or flatness assumption enters, because the transport of the degreewise section is
determined by the unit and the Leibniz signs cancel.

The exactness of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` — the clause
`SheafOfModules.DifferentialGradedModule.PullbackTensorExactnessData.coneIso` — is this
comparison followed by the corresponding one for the tensor product: since
`(pullbackTensorFunctor P D).obj` is `D.functor.obj ∘ P.obj` and
`(pullbackTensorFunctor P D).map` is `D.functor.map ∘ P.map`, both by definition, the clause is
`D.functor.mapIso (PullbackData.coneIso P ψ).symm` read on complexes, composed with
`D.functor.obj (C χ) ≅ C (D.functor.map χ)` at `χ = P.map ψ`. That second comparison is the one
the additivity of `- ⊗_𝒜 𝒩` (`RelativeTensor.dgTensorFunctor_additive`) gives, and it is not in
this file.

## References

* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a a' m m' v u v' u'

/-! ### A morphism out of a binary biproduct which splits -/

namespace CategoryTheory.Limits

/-- **A morphism out of a binary biproduct is an isomorphism when its two components split it.**
Given `a : X ⟶ Z` and `b : Y ⟶ Z` together with `p : Z ⟶ X` and `q : Z ⟶ Y` which retract `a` and
`b` respectively and annihilate the other one, and whose two products `p ≫ a` and `q ≫ b` add up
to the identity of `Z`, the morphism `biprod.desc a b` is an isomorphism, with inverse
`biprod.lift p q`. -/
theorem biprod.isIso_desc {D : Type u} [Category.{v} D] [Preadditive D] {X Y Z : D}
    [HasBinaryBiproduct X Y] (a : X ⟶ Z) (b : Y ⟶ Z) (p : Z ⟶ X) (q : Z ⟶ Y)
    (hap : a ≫ p = 𝟙 X) (haq : a ≫ q = 0) (hbp : b ≫ p = 0) (hbq : b ≫ q = 𝟙 Y)
    (htotal : p ≫ a + q ≫ b = 𝟙 Z) : IsIso (biprod.desc a b) := by
  refine ⟨biprod.lift p q, ?_, ?_⟩
  · refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [hap, haq, hbp, hbq]
  · rw [biprod.desc_eq, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
      biprod.lift_fst, biprod.lift_snd]
    exact htotal

end CategoryTheory.Limits

namespace SheafOfModules

namespace DifferentialGradedModule

namespace PullbackData

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj} {A : DifferentialGradedAlgebra.{t, a} R}
  {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}
  (PD : PullbackData.{t, a, m, v, u, a', m', v', u'} φ)
  {M M₂ : DifferentialGradedModule.{t, a', m'} B} (ψ : M ⟶ M₂)

/-! ### The pullback of the degreewise splitting of a cone -/

/-- The pullback of the first coordinate of the degreewise splitting of the cone of `ψ`. -/
noncomputable def coneFirstFamily :
    (forgetToGradedModule A).obj (PD.obj (cone ψ)) ⟶
      ((forgetToGradedModule A).obj (PD.obj M)).shift 1 :=
  PD.gradedShiftMap 1 (conePackage ψ).firstFamily

/-- The pullback of the inclusion of the first summand of the degreewise splitting of the cone
of `ψ`. -/
noncomputable def coneSectionFamily :
    (forgetToGradedModule A).obj (PD.obj M) ⟶
      ((forgetToGradedModule A).obj (PD.obj (cone ψ))).shift (-1) :=
  PD.gradedShiftMap (-1) (conePackage ψ).sectionFamily

/-- The pullback of the retraction of the cone's inclusion. -/
noncomputable def coneRetrFamily :
    (forgetToGradedModule A).obj (PD.obj (cone ψ)) ⟶
      ((forgetToGradedModule A).obj (PD.obj M₂)).shift 0 :=
  PD.gradedShiftMap 0 (GradedModule.shiftOfHom (conePackage ψ).gradedSplitting.r)

/-- The pullback of the cone's inclusion, as a right-linear family of degree zero. -/
theorem coneInclFamily_eq :
    PD.gradedShiftMap 0
        (GradedModule.shiftOfHom ((forgetToGradedModule B).map (conePackage ψ).inclusion)) =
      GradedModule.shiftOfHom
        ((forgetToGradedModule A).map (PD.map (conePackage ψ).inclusion)) :=
  PD.gradedShiftMap_shiftOfHom (conePackage ψ).inclusion

/-- The pullback of a degree-zero family carrying the identity carries the identity. -/
theorem gradedShiftMap_shiftOfHom_id (W : DifferentialGradedModule.{t, a', m'} B) :
    PD.gradedShiftMap 0 (GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule B).obj W))) =
      GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule A).obj (PD.obj W))) := by
  refine Eq.trans (congrArg (fun g => PD.gradedShiftMap 0 (GradedModule.shiftOfHom g))
    ((forgetToGradedModule B).map_id W).symm) ?_
  refine Eq.trans (PD.gradedShiftMap_shiftOfHom (𝟙 W)) ?_
  refine congrArg GradedModule.shiftOfHom ?_
  rw [show PD.map (𝟙 W) = 𝟙 (PD.obj W) from PD.functor.map_id W,
    (forgetToGradedModule A).map_id]

/-! ### The five splitting relations, pulled back -/

/-- Pulled back composable families whose composite is the identity compose to the identity. -/
private theorem gradedShiftMap_app_comp_eq_id {W Z : DifferentialGradedModule.{t, a', m'} B}
    {k l : ℤ} (hj : k + l = 0)
    (g : (forgetToGradedModule B).obj W ⟶ ((forgetToGradedModule B).obj Z).shift k)
    (g' : (forgetToGradedModule B).obj Z ⟶ ((forgetToGradedModule B).obj W).shift l)
    (hrel : GradedModule.shiftComp hj g g' =
      GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule B).obj W))) (p : ℤ) :
    (PD.gradedShiftMap k g).app p ≫ (PD.gradedShiftMap l g').app (p + k) =
      degCastHom ((forgetToGradedModule A).obj (PD.obj W)).piece
        (show p = p + k + l by omega) :=
  (GradedModule.shiftComp_app_of_eq_shiftOfHom _ _ hj _
    (by rw [← PD.gradedShiftMap_shiftComp, hrel, PD.gradedShiftMap_shiftOfHom_id]) p).trans
    (Category.id_comp _)

/-- Pulled back composable families whose composite vanishes compose to zero. -/
private theorem gradedShiftMap_app_comp_eq_zero {W Z Y : DifferentialGradedModule.{t, a', m'} B}
    {k l j : ℤ} (hj : k + l = j)
    (g : (forgetToGradedModule B).obj W ⟶ ((forgetToGradedModule B).obj Z).shift k)
    (g' : (forgetToGradedModule B).obj Z ⟶ ((forgetToGradedModule B).obj Y).shift l)
    (hrel : GradedModule.shiftComp hj g g' = 0) (p : ℤ) :
    (PD.gradedShiftMap k g).app p ≫ (PD.gradedShiftMap l g').app (p + k) = 0 :=
  GradedModule.shiftComp_app_of_eq_zero _ _ hj
    (by rw [← PD.gradedShiftMap_shiftComp, hrel, PD.gradedShiftMap_zero]) p

/-- The pullback of the degreewise section followed by the pullback of the first coordinate is
the identity. -/
theorem coneSectionFamily_coneFirstFamily (p : ℤ) :
    (PD.coneSectionFamily ψ).app p ≫ (PD.coneFirstFamily ψ).app (p + -1) =
      degCastHom ((forgetToGradedModule A).obj (PD.obj M)).piece
        (show p = p + -1 + 1 by omega) :=
  PD.gradedShiftMap_app_comp_eq_id (by omega) _ _ (conePackage ψ).sectionFamily_firstFamily p

/-- The pullback of the degreewise section is annihilated by the pullback of the retraction. -/
theorem coneSectionFamily_coneRetrFamily (p : ℤ) :
    (PD.coneSectionFamily ψ).app p ≫ (PD.coneRetrFamily ψ).app (p + -1) = 0 :=
  PD.gradedShiftMap_app_comp_eq_zero (by omega) _ _ (conePackage ψ).sectionFamily_retraction p

/-- The pullback of the cone's inclusion is annihilated by the pullback of the first
coordinate. -/
theorem coneIncl_coneFirstFamily (p : ℤ) :
    (GradedModule.shiftOfHom
          ((forgetToGradedModule A).map (PD.map (conePackage ψ).inclusion))).app p ≫
        (PD.coneFirstFamily ψ).app (p + 0) = 0 := by
  rw [← PD.coneInclFamily_eq ψ]
  exact PD.gradedShiftMap_app_comp_eq_zero (by omega) _ _
    (conePackage ψ).inclusion_firstFamily p

/-- The pullback of the cone's inclusion followed by the pullback of the retraction is the
identity. -/
theorem coneIncl_coneRetrFamily (p : ℤ) :
    (GradedModule.shiftOfHom
          ((forgetToGradedModule A).map (PD.map (conePackage ψ).inclusion))).app p ≫
        (PD.coneRetrFamily ψ).app (p + 0) =
      degCastHom ((forgetToGradedModule A).obj (PD.obj M₂)).piece
        (show p = p + 0 + 0 by omega) := by
  rw [← PD.coneInclFamily_eq ψ]
  exact PD.gradedShiftMap_app_comp_eq_id (by omega) _ _
    (conePackage ψ).inclusion_retraction p

/-- The two diagonal products of the pulled-back splitting add up to the identity of the
pullback of the cone. -/
theorem coneFirstFamily_coneSectionFamily_add (p : ℤ) :
    (PD.coneFirstFamily ψ).app p ≫ (PD.coneSectionFamily ψ).app (p + 1) ≫
          degCastHom ((forgetToGradedModule A).obj (PD.obj (cone ψ))).piece
            (show p + 1 + -1 = p by omega)
        + (PD.coneRetrFamily ψ).app p ≫
          (GradedModule.shiftOfHom
              ((forgetToGradedModule A).map (PD.map (conePackage ψ).inclusion))).app (p + 0) ≫
            degCastHom ((forgetToGradedModule A).obj (PD.obj (cone ψ))).piece
              (show p + 0 + 0 = p by omega)
      = 𝟙 _ := by
  have hrel : GradedModule.shiftComp (show (1 : ℤ) + -1 = 0 by omega)
        (PD.coneFirstFamily ψ) (PD.coneSectionFamily ψ)
      + GradedModule.shiftComp (show (0 : ℤ) + 0 = 0 by omega) (PD.coneRetrFamily ψ)
        (GradedModule.shiftOfHom
          ((forgetToGradedModule A).map (PD.map (conePackage ψ).inclusion)))
      = GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule A).obj (PD.obj (cone ψ)))) := by
    rw [← PD.coneInclFamily_eq ψ, coneFirstFamily, coneSectionFamily, coneRetrFamily,
      ← PD.gradedShiftMap_shiftComp, ← PD.gradedShiftMap_shiftComp, ← PD.gradedShiftMap_add,
      (conePackage ψ).firstFamily_sectionFamily_add, PD.gradedShiftMap_shiftOfHom_id]
  have h : (PD.coneFirstFamily ψ).app p ≫ (PD.coneSectionFamily ψ).app (p + 1) ≫
          degCastHom ((forgetToGradedModule A).obj (PD.obj (cone ψ))).piece
            (show p + 1 + -1 = p + 0 by omega)
        + (PD.coneRetrFamily ψ).app p ≫
          (GradedModule.shiftOfHom
              ((forgetToGradedModule A).map (PD.map (conePackage ψ).inclusion))).app (p + 0) ≫
            degCastHom ((forgetToGradedModule A).obj (PD.obj (cone ψ))).piece
              (show p + 0 + 0 = p + 0 by omega)
      = 𝟙 (((forgetToGradedModule A).obj (PD.obj (cone ψ))).piece p) ≫
          degCastHom ((forgetToGradedModule A).obj (PD.obj (cone ψ))).piece
            (show p = p + 0 by omega) :=
    congrArg (fun α : (forgetToGradedModule A).obj (PD.obj (cone ψ)) ⟶
      ((forgetToGradedModule A).obj (PD.obj (cone ψ))).shift 0 => α.app p) hrel
  have h2 := congrArg (fun z => z ≫ degCastHom
    ((forgetToGradedModule A).obj (PD.obj (cone ψ))).piece
      (show p + 0 = p by omega)) h
  simp only [Preadditive.add_comp, Category.assoc, degCastHom_comp_degCastHom,
    degCastHom_eq_id, Category.id_comp] at h2
  exact h2

/-! ### The comparison out of the cone of the pullback -/

/-- **The degreewise section of a cone is a null-homotopy of `ψ` followed by the cone's
inclusion**, read as the commutator of a right-linear family of degree `-1` with the
differentials. -/
theorem shiftDiffCommutator_sectionFamily :
    shiftDiffCommutator (conePackage ψ).sectionFamily =
      (forgetToGradedModule B).map (ψ ≫ (conePackage ψ).inclusion) := by
  refine GradedModule.Hom.ext fun n => ?_
  change shiftDiffFst (conePackage ψ).sectionFamily n +
      shiftDiffSnd (conePackage ψ).sectionFamily n =
    ψ.toHomologicalComplex.f n ≫ (conePackage ψ).inclusion.toHomologicalComplex.f n
  refine Eq.trans ?_ ((conePackage ψ).sectionFamily_d n)
  refine congrArg₂ (· + ·) ?_ rfl
  exact congrArg (fun z => (conePackage ψ).sectionFamily.app n ≫ z)
    (d_comp_degCastHom (conePackage ψ).cone.complex (n + -1)
      (show n + -1 + 1 = n by omega)).symm

/-- **The pullback of the degreewise section of the cone of `ψ` is a null-homotopy of the
pullback of `ψ` followed by the pullback of the cone's inclusion.** -/
noncomputable def coneHomotopy :
    Homotopy (PD.map (ψ ≫ (conePackage ψ).inclusion))
      (0 : PD.obj M ⟶ PD.obj (cone ψ)) :=
  homotopyOfShiftDiffCommutator (PD.coneSectionFamily ψ)
    (((PD.gradedShiftMap_shiftDiffCommutator (conePackage ψ).sectionFamily).trans
        (congrArg PD.gradedMap (shiftDiffCommutator_sectionFamily ψ))).trans
      (PD.gradedMap_forget (ψ ≫ (conePackage ψ).inclusion)))

/-- The degreewise family out of which the comparison is built: the pullback of the cone's
degreewise section, read in the degrees of the cone of the pullback. -/
noncomputable def coneDescFamily (n : ℤ) :
    (PD.obj M).complex.X (n + 1) ⟶ (PD.obj (cone ψ)).complex.X n :=
  (PD.coneSectionFamily ψ).app (n + 1) ≫
    degCastHom (PD.obj (cone ψ)).complex.X (show n + 1 + -1 = n by omega)

/-- The degreewise family is right-linear, in the shape `ConePackage.desc` consumes. -/
theorem coneDescFamily_mul (n i : ℤ) (U : Cᵒᵖ)
    (x : ((PD.obj M).complex.X (n + 1)).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (PD.coneDescFamily ψ (n + i)).val.app U
        (gradedCast (fun q ↦ ((PD.obj M).complex.X q).val.obj U) (add_right_comm n 1 i)
          (((PD.obj M).mul (n + 1) i).app U x y)) =
      ((PD.obj (cone ψ)).mul n i).app U ((PD.coneDescFamily ψ n).val.app U x) y := by
  have hcast : ∀ (q : ℤ) (z : ((PD.obj M).complex.X (q + 1)).val.obj U),
      (PD.coneDescFamily ψ q).val.app U z =
        castHom (PD.obj (cone ψ)).complex.X (show q + 1 + -1 = q by omega) U
          (((PD.coneSectionFamily ψ).app (q + 1)).val.app U z) := fun q z =>
    degCastHom_val_app (PD.obj (cone ψ)).complex.X
      (show q + 1 + -1 = q by omega) U _
  have hsec : ∀ {k k' : ℤ} (h : k = k') (z : ((PD.obj M).complex.X k).val.obj U),
      ((PD.coneSectionFamily ψ).app k').val.app U
          (castHom (PD.obj M).complex.X h U z) =
        castHom (PD.obj (cone ψ)).complex.X (show k + -1 = k' + -1 by omega) U
          (((PD.coneSectionFamily ψ).app k).val.app U z) := by
    intro k k' h z
    subst h
    rfl
  have hmul : ∀ (q : ℤ) (z : ((PD.obj M).complex.X q).val.obj U),
      ((PD.coneSectionFamily ψ).app (q + i)).val.app U
          (((PD.obj M).mul q i).app U z y) =
        castHom (PD.obj (cone ψ)).complex.X (show q + -1 + i = q + i + -1 by omega) U
          (((PD.obj (cone ψ)).mul (q + -1) i).app U
            (((PD.coneSectionFamily ψ).app q).val.app U z) y) := fun q z =>
    ((PD.coneSectionFamily ψ).map_smul q i U z y).trans
      (GradedModule.shift_smul ((forgetToGradedModule A).obj (PD.obj (cone ψ))) (-1) q i U
        (((PD.coneSectionFamily ψ).app q).val.app U z) y)
  refine Eq.trans (hcast (n + i) _) ?_
  refine Eq.trans (congrArg (castHom (PD.obj (cone ψ)).complex.X
      (show n + i + 1 + -1 = n + i by omega) U)
    (Eq.trans (congrArg (((PD.coneSectionFamily ψ).app (n + i + 1)).val.app U)
        (castHom_apply (PD.obj M).complex.X (add_right_comm n 1 i) U
          (((PD.obj M).mul (n + 1) i).app U x y)).symm)
      (Eq.trans (hsec (add_right_comm n 1 i) (((PD.obj M).mul (n + 1) i).app U x y))
        (congrArg (castHom (PD.obj (cone ψ)).complex.X
          (show n + 1 + i + -1 = n + i + 1 + -1 by omega) U)
          (hmul (n + 1) x))))) ?_
  refine Eq.trans (Cofree.castHom_castHom (PD.obj (cone ψ)).complex.X _ _ U _) ?_
  refine Eq.trans (Cofree.castHom_castHom (PD.obj (cone ψ)).complex.X _ _ U _) ?_
  refine Eq.trans ?_ (congrArg (fun z => ((PD.obj (cone ψ)).mul n i).app U z y)
    (hcast n x)).symm
  exact (mul_app_castHom (PD.obj (cone ψ)) (show n + 1 + -1 = n by omega) i U
    (((PD.coneSectionFamily ψ).app (n + 1)).val.app U x) y).symm

/-- The degreewise family is a null-homotopy of the pullback of `ψ` followed by the pullback of
the cone's inclusion, in the shape `ConePackage.desc` consumes. -/
theorem coneDescFamily_delta (n : ℤ) :
    PD.coneDescFamily ψ n ≫ (PD.obj (cone ψ)).complex.d n (n + 1) +
        (PD.obj M).complex.d (n + 1) (n + 1 + 1) ≫ PD.coneDescFamily ψ (n + 1) =
      (PD.map ψ).toHomologicalComplex.f (n + 1) ≫
        (PD.map (conePackage ψ).inclusion).toHomologicalComplex.f (n + 1) := by
  have hc := (PD.coneHomotopy ψ).comm (n + 1)
  rw [show ((0 : PD.obj M ⟶ PD.obj (cone ψ)).toHomologicalComplex.f (n + 1)) = 0 from rfl,
    sub_zero] at hc
  refine Eq.trans ?_ (Eq.trans hc.symm ?_)
  · refine congrArg₂ (· + ·) ?_ ?_
    · exact (Category.assoc _ _ _).trans (congrArg
        (fun z => (PD.coneSectionFamily ψ).app (n + 1) ≫ z)
        (degCastHom_comp_d (PD.obj (cone ψ)).complex
          (show n + 1 + -1 = n by omega) (n + 1)))
    · exact (Category.assoc _ _ _).symm.trans (congrArg
        (fun z => ((PD.obj M).complex.d (n + 1) (n + 1 + 1) ≫
          (PD.coneSectionFamily ψ).app (n + 1 + 1)) ≫ z)
        (degCastHom_eq_eqToHom (PD.obj (cone ψ)).complex.X
          (show n + 1 + 1 + -1 = n + 1 by omega)))
  · rw [show PD.map (ψ ≫ (conePackage ψ).inclusion) =
      PD.map ψ ≫ PD.map (conePackage ψ).inclusion from
        PD.functor.map_comp ψ (conePackage ψ).inclusion]
    rfl

/-- **The comparison from the cone of the pullback of `ψ` to the pullback of the cone of `ψ`**:
the homomorphism out of the cone determined by the pullback of the cone's inclusion together with
the pullback of its degreewise section. -/
noncomputable def coneDesc : cone (PD.map ψ) ⟶ PD.obj (cone ψ) :=
  (conePackage (PD.map ψ)).desc (PD.map (conePackage ψ).inclusion) (PD.coneDescFamily ψ)
    (PD.coneDescFamily_mul ψ) (PD.coneDescFamily_delta ψ)

/-- The degree-`n` component of the comparison is the degreewise splitting of the cone followed
by its two coordinates. -/
theorem coneDesc_f (n : ℤ) :
    (PD.coneDesc ψ).toHomologicalComplex.f n =
      ((conePackage (PD.map ψ)).componentIso n).hom ≫
        biprod.desc (PD.coneDescFamily ψ n)
          ((PD.map (conePackage ψ).inclusion).toHomologicalComplex.f n) :=
  (conePackage (PD.map ψ)).desc_f (PD.map (conePackage ψ).inclusion) (PD.coneDescFamily ψ)
    (PD.coneDescFamily_mul ψ) (PD.coneDescFamily_delta ψ) n

/-! ### The comparison is an isomorphism -/

/-- The pullback of the degreewise retraction of the cone's inclusion, in degree `n`. -/
noncomputable def coneRetrApp (n : ℤ) :
    (PD.obj (cone ψ)).complex.X n ⟶ (PD.obj M₂).complex.X n :=
  (PD.coneRetrFamily ψ).app n ≫
    degCastHom (PD.obj M₂).complex.X (show n + 0 = n by omega)

/-- A right-linear family commutes with transport along an equality of degrees. -/
private theorem degCastHom_comp_app_shift {X Y : GradedModule.{t, a, m} A.toGradedAlgebra} {k : ℤ}
    (f : X ⟶ Y.shift k) {n n' : ℤ} (h : n = n') :
    degCastHom X.piece h ≫ f.app n' = f.app n ≫ degCastHom Y.piece (show n + k = n' + k by omega) :=
  (GradedModule.degCastHom_comp_app f h).trans
    (congrArg (f.app n ≫ ·) (GradedModule.degCastHom_shift_piece Y k h))

/-- The degreewise section followed by the first coordinate is the identity. -/
theorem coneDescFamily_coneFirstFamily (n : ℤ) :
    PD.coneDescFamily ψ n ≫ (PD.coneFirstFamily ψ).app n =
      𝟙 ((PD.obj M).complex.X (n + 1)) := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => (PD.coneSectionFamily ψ).app (n + 1) ≫ z)
    (degCastHom_comp_app_shift (PD.coneFirstFamily ψ) (show n + 1 + -1 = n by omega))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ _) (PD.coneSectionFamily_coneFirstFamily ψ (n + 1))) ?_
  exact (degCastHom_comp_degCastHom (PD.obj M).complex.X _ _).trans
    (degCastHom_eq_id (PD.obj M).complex.X _)

/-- The pullback of the retraction, read in the two spellings of the degree. -/
theorem degCastHom_coneRetrFamily_app (n : ℤ) :
    degCastHom (PD.obj (cone ψ)).complex.X (show n + 1 + -1 = n by omega) ≫
        (PD.coneRetrFamily ψ).app n =
      (PD.coneRetrFamily ψ).app (n + 1 + -1) ≫
        degCastHom (PD.obj M₂).complex.X (show n + 1 + -1 + 0 = n + 0 by omega) :=
  degCastHom_comp_app_shift (PD.coneRetrFamily ψ) (show n + 1 + -1 = n by omega)

/-- The degreewise section is annihilated by the retraction. -/
theorem coneDescFamily_coneRetrApp (n : ℤ) :
    PD.coneDescFamily ψ n ≫ PD.coneRetrApp ψ n = 0 := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => (PD.coneSectionFamily ψ).app (n + 1) ≫ z)
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (fun z => z ≫ degCastHom (PD.obj M₂).complex.X
          (show n + 0 = n by omega)) (PD.degCastHom_coneRetrFamily_app ψ n))
        (Category.assoc _ _ _)))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ (degCastHom (PD.obj M₂).complex.X
      (show n + 1 + -1 + 0 = n + 0 by omega) ≫
      degCastHom (PD.obj M₂).complex.X (show n + 0 = n by omega)))
    (PD.coneSectionFamily_coneRetrFamily ψ (n + 1))) ?_
  exact zero_comp

/-- The pullback of the cone's inclusion is annihilated by the first coordinate. -/
theorem coneIncl_f_coneFirstFamily (n : ℤ) :
    (PD.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫
      (PD.coneFirstFamily ψ).app n = 0 := by
  have h := PD.coneIncl_coneFirstFamily ψ n
  refine (cancel_mono (degCastHom
    (((forgetToGradedModule A).obj (PD.obj M)).shift 1).piece
      (show n = n + 0 by omega))).1 ?_
  refine Eq.trans ?_ (Eq.trans h (zero_comp).symm)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z =>
      (PD.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫ z)
    (GradedModule.degCastHom_comp_app (PD.coneFirstFamily ψ)
      (show n = n + 0 by omega)).symm) ?_
  exact (Category.assoc _ _ _).symm

/-- The pullback of the cone's inclusion followed by the retraction, with the transport
cancelled. -/
theorem coneIncl_f_coneRetrFamily_app (n : ℤ) :
    (PD.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫
        (PD.coneRetrFamily ψ).app n =
      degCastHom (PD.obj M₂).complex.X (show n = n + 0 by omega) := by
  have hmid : (PD.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫
        (PD.coneRetrFamily ψ).app n ≫
          degCastHom (PD.obj M₂).complex.X (show n + 0 = n + 0 + 0 by omega) =
      degCastHom (PD.obj M₂).complex.X (show n = n + 0 + 0 by omega) := by
    have e1 : (PD.coneRetrFamily ψ).app n ≫
          degCastHom (PD.obj M₂).complex.X (show n + 0 = n + 0 + 0 by omega) =
        degCastHom (PD.obj (cone ψ)).complex.X (show n = n + 0 by omega) ≫
          (PD.coneRetrFamily ψ).app (n + 0) :=
      (degCastHom_comp_app_shift (PD.coneRetrFamily ψ) (show n = n + 0 by omega)).symm
    refine Eq.trans (congrArg (fun z =>
      (PD.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫ z) e1) ?_
    exact (Category.assoc _ _ _).symm.trans (PD.coneIncl_coneRetrFamily ψ n)
  refine (cancel_mono (degCastHom (PD.obj M₂).complex.X
    (show n + 0 = n + 0 + 0 by omega))).1 ?_
  refine Eq.trans (Category.assoc _ _ _) (hmid.trans ?_)
  exact (degCastHom_comp_degCastHom (PD.obj M₂).complex.X
    (show n = n + 0 by omega) (show n + 0 = n + 0 + 0 by omega)).symm

/-- The pullback of the cone's inclusion followed by the retraction is the identity. -/
theorem coneIncl_f_coneRetrApp (n : ℤ) :
    (PD.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫ PD.coneRetrApp ψ n =
      𝟙 ((PD.obj M₂).complex.X n) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ degCastHom (PD.obj M₂).complex.X
    (show n + 0 = n by omega)) (PD.coneIncl_f_coneRetrFamily_app ψ n)) ?_
  exact (degCastHom_comp_degCastHom (PD.obj M₂).complex.X _ _).trans
    (degCastHom_eq_id (PD.obj M₂).complex.X _)

/-- The two diagonal products add up to the identity of the pullback of the cone. -/
theorem coneFirstFamily_coneDescFamily_add (n : ℤ) :
    (show (PD.obj (cone ψ)).complex.X n ⟶ (PD.obj (cone ψ)).complex.X n from
          (PD.coneFirstFamily ψ).app n ≫ PD.coneDescFamily ψ n) +
        (show (PD.obj (cone ψ)).complex.X n ⟶ (PD.obj (cone ψ)).complex.X n from
          PD.coneRetrApp ψ n ≫
            (PD.map (conePackage ψ).inclusion).toHomologicalComplex.f n) =
      𝟙 ((PD.obj (cone ψ)).complex.X n) := by
  refine Eq.trans ?_ (PD.coneFirstFamily_coneSectionFamily_add ψ n)
  refine congrArg₂ (· + ·) (Category.assoc _ _ _).symm ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun z => (PD.coneRetrFamily ψ).app n ≫ z) ?_
  refine Eq.trans (GradedModule.degCastHom_comp_hom_f
    (PD.map (conePackage ψ).inclusion).toHomologicalComplex
    (show n + 0 = n by omega)) ?_
  have hr : (GradedModule.shiftOfHom
        ((forgetToGradedModule A).map (PD.map (conePackage ψ).inclusion))).app (n + 0) ≫
        degCastHom (PD.obj (cone ψ)).complex.X (show n + 0 + 0 = n by omega) =
      (PD.map (conePackage ψ).inclusion).toHomologicalComplex.f (n + 0) ≫
        degCastHom (PD.obj (cone ψ)).complex.X (show n + 0 = n by omega) :=
    (Category.assoc _ _ _).trans (congrArg
      (fun z => (PD.map (conePackage ψ).inclusion).toHomologicalComplex.f (n + 0) ≫ z)
      (degCastHom_comp_degCastHom (PD.obj (cone ψ)).complex.X
        (show n + 0 = n + 0 + 0 by omega) (show n + 0 + 0 = n by omega)))
  exact hr.symm

/-! ### The comparison is an isomorphism -/

/-- **The degree-`n` component of the comparison is an isomorphism.** The degreewise splitting
identifies it with the morphism out of a binary biproduct whose two components are the pullback
of the cone's degreewise section and the pullback of the cone's inclusion
(`PullbackData.coneDesc_f`), and the five splitting relations exhibit the pullback of the first
coordinate and the pullback of the degreewise retraction as the two components of an inverse. -/
theorem isIso_coneDesc_f (n : ℤ) : IsIso ((PD.coneDesc ψ).toHomologicalComplex.f n) := by
  have hdesc : IsIso (biprod.desc (PD.coneDescFamily ψ n)
      ((PD.map (conePackage ψ).inclusion).toHomologicalComplex.f n)) :=
    biprod.isIso_desc _ _ ((PD.coneFirstFamily ψ).app n) (PD.coneRetrApp ψ n)
      (PD.coneDescFamily_coneFirstFamily ψ n) (PD.coneDescFamily_coneRetrApp ψ n)
      (PD.coneIncl_f_coneFirstFamily ψ n) (PD.coneIncl_f_coneRetrApp ψ n)
      (PD.coneFirstFamily_coneDescFamily_add ψ n)
  rw [PD.coneDesc_f ψ n]
  infer_instance

/-- **The comparison is an isomorphism of right differential graded `𝒜`-modules**, being an
isomorphism in every degree. -/
theorem isIso_coneDesc : IsIso (PD.coneDesc ψ) :=
  isIso_of_componentwise _ (PD.isIso_coneDesc_f ψ)

/-- **The cone of the pullback of `ψ` is the pullback of the cone of `ψ`**: `C(f^*ψ) ≅ f^*C(ψ)`,
as right differential graded `𝒜`-modules. -/
noncomputable def coneIso : cone (PD.map ψ) ≅ PD.obj (cone ψ) :=
  haveI := PD.isIso_coneDesc ψ
  asIso (PD.coneDesc ψ)

/-- The forward map of `PullbackData.coneIso` is the comparison `PullbackData.coneDesc`. -/
@[simp]
theorem coneIso_hom : (PD.coneIso ψ).hom = PD.coneDesc ψ := rfl

/-- **The cone of the pullback of `ψ` is the pullback of the cone of `ψ`**, as complexes of
sheaves of modules. -/
noncomputable def coneComplexIso :
    (cone (PD.map ψ)).complex ≅ (PD.obj (cone ψ)).complex :=
  haveI (n : ℤ) : IsIso ((PD.coneDesc ψ).toHomologicalComplex.f n) := PD.isIso_coneDesc_f ψ n
  haveI : IsIso (PD.coneDesc ψ).toHomologicalComplex :=
    HomologicalComplex.Hom.isIso_of_components _
  asIso (PD.coneDesc ψ).toHomologicalComplex

/-- The forward map of `PullbackData.coneComplexIso` is the morphism of complexes underlying
`PullbackData.coneDesc`. -/
@[simp]
theorem coneComplexIso_hom :
    (PD.coneComplexIso ψ).hom = (PD.coneDesc ψ).toHomologicalComplex := rfl

end PullbackData

end DifferentialGradedModule

end SheafOfModules

end
