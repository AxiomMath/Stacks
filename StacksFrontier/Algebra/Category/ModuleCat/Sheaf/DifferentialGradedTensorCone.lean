module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorGradedShift

/-!
# The relative tensor product of right differential graded modules commutes with cones

Let `𝒜` and `ℬ` be sheaves of differential graded algebras on a site, let `𝒩` be a differential
graded `(𝒜, ℬ)`-bimodule and let `- ⊗_𝒜 𝒩` be a tensor product functor for `𝒩`, given by the
universal property of `SheafOfModules.TensorFunctorData`. For a homomorphism `ψ : ℳ ⟶ ℳ₂` of
right differential graded `𝒜`-modules, the cone of `ψ ⊗ 1` is `C(ψ) ⊗_𝒜 𝒩`:

`C(ψ ⊗_𝒜 1) ≅ C(ψ) ⊗_𝒜 𝒩`.

## Main results

* `SheafOfModules.TensorFunctorData.coneIso`: **the cone of the tensor product of `ψ` is the
  tensor product of the cone of `ψ`**, as right differential graded `ℬ`-modules, and
  `TensorFunctorData.coneComplexIso`: the same as complexes of sheaves of modules.

## Implementation notes

This is the second half of the exactness of the functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of [Stacks, Tag 0FTE],
whose first half — the pullback of a cone — is
`SheafOfModules.DifferentialGradedModule.PullbackData.coneIso`. The construction here is the one
of that comparison with the pullback replaced by the tensor product everywhere: both functors
transport a right-linear family of a given degree
(`SheafOfModules.TensorFunctorData.gradedShiftMap` here,
`SheafOfModules.DifferentialGradedModule.PullbackData.gradedShiftMap` there), and both
transports preserve composites, sums and zero, which is all the five splitting relations of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeShiftSplitting.lean` need.

The comparison goes out of the cone of `ψ ⊗ 1`, because that is the direction in which the cone
has a universal property: `ConePackage.desc` builds a homomorphism out of `C(χ)` from a
homomorphism out of the target of `χ` together with a null-homotopy of the composite. Here the
homomorphism is `C(ψ)`'s inclusion tensored with `1` and the null-homotopy is the tensor product
of the cone's degreewise section, which is a null-homotopy of `ψ` followed by the inclusion
(`ConePackage.sectionFamily_d`).

That the transported section is still a null-homotopy is `TensorFunctorData.mapHomotopy`, the
tensor product `h ⊗ 1` of a homotopy: its degreewise components are by definition the components
of `TensorFunctorData.gradedShiftMap` at the degree `-1` family of `h`, so no second comparison
between the two transports is needed. The homotopy whose tensor product is taken is the one
`DifferentialGradedModule.homotopyOfShiftDiffCommutator` reads off the degreewise section, the
input being `PullbackData.shiftDiffCommutator_sectionFamily`.

Invertibility is degreewise, by `CategoryTheory.Limits.biprod.isIso_desc` at the five transported
splitting relations, exactly as for the pullback.

The comparison needs no hypothesis on the tensor product beyond its universal property: no
flatness of `𝒩` enters, because the transport of the degreewise section is determined by the
multiplication map and the Leibniz signs cancel.

## References

* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m z s v u

namespace SheafOfModules

namespace DifferentialGradedModule

section NullHomotopy

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {M M₂ : DifferentialGradedModule.{t, a, m} A}
  (ψ : M ⟶ M₂)

/-- **The degreewise section of a cone is a null-homotopy of `ψ` followed by the cone's
inclusion**, read as a homotopy of right differential graded modules. The commutator of that
section with the differentials is `PullbackData.shiftDiffCommutator_sectionFamily`. -/
noncomputable def coneNullHomotopy :
    Homotopy (ψ ≫ (conePackage ψ).inclusion) (0 : M ⟶ cone ψ) :=
  homotopyOfShiftDiffCommutator (conePackage ψ).sectionFamily
    (PullbackData.shiftDiffCommutator_sectionFamily ψ)

/-- The null-homotopy read back as a right-linear family of degree `-1` is the degreewise
section it was built from. -/
theorem coneNullHomotopy_toGradedShift :
    (coneNullHomotopy ψ).toGradedShift = (conePackage ψ).sectionFamily :=
  GradedModule.Hom.ext fun _ => rfl

end NullHomotopy

end DifferentialGradedModule

namespace TensorFunctorData

open DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} {N : DifferentialGradedBimodule.{t, a, z} A B}
  (D : TensorFunctorData.{t, a, m, z, s} A B N)
  {M M₂ : DifferentialGradedModule.{t, a, m} A} (ψ : M ⟶ M₂)

/-! ### The tensor product of the degreewise splitting of a cone -/

/-- The tensor product of the first coordinate of the degreewise splitting of the cone of `ψ`. -/
noncomputable def coneFirstFamily :
    (forgetToGradedModule B).obj (D.functor.obj (cone ψ)) ⟶
      ((forgetToGradedModule B).obj (D.functor.obj M)).shift 1 :=
  D.gradedShiftMap 1 (conePackage ψ).firstFamily

/-- The tensor product of the inclusion of the first summand of the degreewise splitting of the
cone of `ψ`. -/
noncomputable def coneSectionFamily :
    (forgetToGradedModule B).obj (D.functor.obj M) ⟶
      ((forgetToGradedModule B).obj (D.functor.obj (cone ψ))).shift (-1) :=
  D.gradedShiftMap (-1) (conePackage ψ).sectionFamily

/-- The tensor product of the retraction of the cone's inclusion. -/
noncomputable def coneRetrFamily :
    (forgetToGradedModule B).obj (D.functor.obj (cone ψ)) ⟶
      ((forgetToGradedModule B).obj (D.functor.obj M₂)).shift 0 :=
  D.gradedShiftMap 0 (GradedModule.shiftOfHom (conePackage ψ).gradedSplitting.r)

/-- The tensor product of the cone's inclusion, as a right-linear family of degree zero. -/
theorem coneInclFamily_eq :
    D.gradedShiftMap 0
        (GradedModule.shiftOfHom ((forgetToGradedModule A).map (conePackage ψ).inclusion)) =
      GradedModule.shiftOfHom
        ((forgetToGradedModule B).map (D.functor.map (conePackage ψ).inclusion)) :=
  D.gradedShiftMap_shiftOfHom (conePackage ψ).inclusion

/-- The tensor product of a degree-zero family carrying the identity carries the identity. -/
theorem gradedShiftMap_shiftOfHom_id (W : DifferentialGradedModule.{t, a, m} A) :
    D.gradedShiftMap 0 (GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule A).obj W))) =
      GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule B).obj (D.functor.obj W))) := by
  refine Eq.trans (congrArg (fun g => D.gradedShiftMap 0 (GradedModule.shiftOfHom g))
    ((forgetToGradedModule A).map_id W).symm) ?_
  refine Eq.trans (D.gradedShiftMap_shiftOfHom (𝟙 W)) ?_
  refine congrArg GradedModule.shiftOfHom ?_
  rw [show D.functor.map (𝟙 W) = 𝟙 (D.functor.obj W) from D.functor.map_id W,
    (forgetToGradedModule B).map_id]

/-! ### The five splitting relations, tensored -/

/-- The tensor product of the degreewise section followed by the tensor product of the first
coordinate is the identity. -/
theorem coneSectionFamily_coneFirstFamily (p : ℤ) :
    (D.coneSectionFamily ψ).app p ≫ (D.coneFirstFamily ψ).app (p + -1) =
      degCastHom ((forgetToGradedModule B).obj (D.functor.obj M)).piece
        (show p = p + -1 + 1 by omega) := by
  have hrel : GradedModule.shiftComp (show (-1 : ℤ) + 1 = 0 by omega)
      (D.coneSectionFamily ψ) (D.coneFirstFamily ψ) =
        GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule B).obj (D.functor.obj M))) := by
    refine Eq.trans (D.gradedShiftMap_shiftComp (show (-1 : ℤ) + 1 = 0 by omega)
      (conePackage ψ).sectionFamily (conePackage ψ).firstFamily).symm ?_
    refine Eq.trans (congrArg (D.gradedShiftMap 0)
      ((conePackage ψ).sectionFamily_firstFamily)) ?_
    exact D.gradedShiftMap_shiftOfHom_id M
  exact (GradedModule.shiftComp_app_of_eq_shiftOfHom _ _ _ _ hrel p).trans
    (Category.id_comp _)

/-- The tensor product of the degreewise section is annihilated by the tensor product of the
retraction. -/
theorem coneSectionFamily_coneRetrFamily (p : ℤ) :
    (D.coneSectionFamily ψ).app p ≫ (D.coneRetrFamily ψ).app (p + -1) = 0 := by
  have hrel : GradedModule.shiftComp (show (-1 : ℤ) + 0 = -1 by omega)
      (D.coneSectionFamily ψ) (D.coneRetrFamily ψ) = 0 := by
    refine Eq.trans (D.gradedShiftMap_shiftComp (show (-1 : ℤ) + 0 = -1 by omega)
      (conePackage ψ).sectionFamily
      (GradedModule.shiftOfHom (conePackage ψ).gradedSplitting.r)).symm ?_
    refine Eq.trans (congrArg (D.gradedShiftMap (-1))
      ((conePackage ψ).sectionFamily_retraction)) ?_
    exact D.gradedShiftMap_zero (-1)
  exact GradedModule.shiftComp_app_of_eq_zero _ _ _ hrel p

/-- The tensor product of the cone's inclusion is annihilated by the tensor product of the first
coordinate. -/
theorem coneIncl_coneFirstFamily (p : ℤ) :
    (GradedModule.shiftOfHom
          ((forgetToGradedModule B).map (D.functor.map (conePackage ψ).inclusion))).app p ≫
        (D.coneFirstFamily ψ).app (p + 0) = 0 := by
  have hrel : GradedModule.shiftComp (show (0 : ℤ) + 1 = 1 by omega)
      (GradedModule.shiftOfHom
        ((forgetToGradedModule B).map (D.functor.map (conePackage ψ).inclusion)))
      (D.coneFirstFamily ψ) = 0 := by
    refine Eq.trans (congrArg (fun g => GradedModule.shiftComp
      (show (0 : ℤ) + 1 = 1 by omega) g (D.coneFirstFamily ψ))
      (D.coneInclFamily_eq ψ).symm) ?_
    refine Eq.trans (D.gradedShiftMap_shiftComp (show (0 : ℤ) + 1 = 1 by omega)
      (GradedModule.shiftOfHom
        ((forgetToGradedModule A).map (conePackage ψ).inclusion))
      (conePackage ψ).firstFamily).symm ?_
    refine Eq.trans (congrArg (D.gradedShiftMap 1)
      ((conePackage ψ).inclusion_firstFamily)) ?_
    exact D.gradedShiftMap_zero 1
  exact GradedModule.shiftComp_app_of_eq_zero _ _ _ hrel p

/-- The tensor product of the cone's inclusion followed by the tensor product of the retraction
is the identity. -/
theorem coneIncl_coneRetrFamily (p : ℤ) :
    (GradedModule.shiftOfHom
          ((forgetToGradedModule B).map (D.functor.map (conePackage ψ).inclusion))).app p ≫
        (D.coneRetrFamily ψ).app (p + 0) =
      degCastHom ((forgetToGradedModule B).obj (D.functor.obj M₂)).piece
        (show p = p + 0 + 0 by omega) := by
  have hrel : GradedModule.shiftComp (show (0 : ℤ) + 0 = 0 by omega)
      (GradedModule.shiftOfHom
        ((forgetToGradedModule B).map (D.functor.map (conePackage ψ).inclusion)))
      (D.coneRetrFamily ψ) =
        GradedModule.shiftOfHom (𝟙 ((forgetToGradedModule B).obj (D.functor.obj M₂))) := by
    refine Eq.trans (congrArg (fun g => GradedModule.shiftComp
      (show (0 : ℤ) + 0 = 0 by omega) g (D.coneRetrFamily ψ))
      (D.coneInclFamily_eq ψ).symm) ?_
    refine Eq.trans (D.gradedShiftMap_shiftComp (show (0 : ℤ) + 0 = 0 by omega)
      (GradedModule.shiftOfHom
        ((forgetToGradedModule A).map (conePackage ψ).inclusion))
      (GradedModule.shiftOfHom (conePackage ψ).gradedSplitting.r)).symm ?_
    refine Eq.trans (congrArg (D.gradedShiftMap 0)
      ((conePackage ψ).inclusion_retraction)) ?_
    exact D.gradedShiftMap_shiftOfHom_id M₂
  exact (GradedModule.shiftComp_app_of_eq_shiftOfHom _ _ _ _ hrel p).trans
    (Category.id_comp _)

/-- The two diagonal products of the tensored splitting add up to the identity of the tensor
product of the cone. -/
theorem coneFirstFamily_coneSectionFamily_add (p : ℤ) :
    (D.coneFirstFamily ψ).app p ≫ (D.coneSectionFamily ψ).app (p + 1) ≫
          degCastHom ((forgetToGradedModule B).obj (D.functor.obj (cone ψ))).piece
            (show p + 1 + -1 = p by omega)
        + (D.coneRetrFamily ψ).app p ≫
          (GradedModule.shiftOfHom ((forgetToGradedModule B).map
              (D.functor.map (conePackage ψ).inclusion))).app (p + 0) ≫
            degCastHom ((forgetToGradedModule B).obj (D.functor.obj (cone ψ))).piece
              (show p + 0 + 0 = p by omega)
      = 𝟙 _ := by
  have hrel : GradedModule.shiftComp (show (1 : ℤ) + -1 = 0 by omega)
        (D.coneFirstFamily ψ) (D.coneSectionFamily ψ)
      + GradedModule.shiftComp (show (0 : ℤ) + 0 = 0 by omega) (D.coneRetrFamily ψ)
        (GradedModule.shiftOfHom
          ((forgetToGradedModule B).map (D.functor.map (conePackage ψ).inclusion)))
      = GradedModule.shiftOfHom
          (𝟙 ((forgetToGradedModule B).obj (D.functor.obj (cone ψ)))) := by
    refine Eq.trans (congrArg₂ (· + ·)
      (D.gradedShiftMap_shiftComp (show (1 : ℤ) + -1 = 0 by omega)
        (conePackage ψ).firstFamily (conePackage ψ).sectionFamily).symm
      (Eq.trans (congrArg (fun g => GradedModule.shiftComp
          (show (0 : ℤ) + 0 = 0 by omega) (D.coneRetrFamily ψ) g)
          (D.coneInclFamily_eq ψ).symm)
        (D.gradedShiftMap_shiftComp (show (0 : ℤ) + 0 = 0 by omega)
          (GradedModule.shiftOfHom (conePackage ψ).gradedSplitting.r)
          (GradedModule.shiftOfHom
            ((forgetToGradedModule A).map (conePackage ψ).inclusion))).symm)) ?_
    refine Eq.trans (D.gradedShiftMap_add 0 _ _).symm ?_
    refine Eq.trans (congrArg (D.gradedShiftMap 0)
      ((conePackage ψ).firstFamily_sectionFamily_add)) ?_
    exact D.gradedShiftMap_shiftOfHom_id (cone ψ)
  have h : (D.coneFirstFamily ψ).app p ≫ (D.coneSectionFamily ψ).app (p + 1) ≫
          degCastHom ((forgetToGradedModule B).obj (D.functor.obj (cone ψ))).piece
            (show p + 1 + -1 = p + 0 by omega)
        + (D.coneRetrFamily ψ).app p ≫
          (GradedModule.shiftOfHom ((forgetToGradedModule B).map
              (D.functor.map (conePackage ψ).inclusion))).app (p + 0) ≫
            degCastHom ((forgetToGradedModule B).obj (D.functor.obj (cone ψ))).piece
              (show p + 0 + 0 = p + 0 by omega)
      = 𝟙 (((forgetToGradedModule B).obj (D.functor.obj (cone ψ))).piece p) ≫
          degCastHom ((forgetToGradedModule B).obj (D.functor.obj (cone ψ))).piece
            (show p = p + 0 by omega) :=
    congrArg (fun α : (forgetToGradedModule B).obj (D.functor.obj (cone ψ)) ⟶
      ((forgetToGradedModule B).obj (D.functor.obj (cone ψ))).shift 0 => α.app p) hrel
  have h2 := congrArg (fun w => w ≫ degCastHom
    ((forgetToGradedModule B).obj (D.functor.obj (cone ψ))).piece
      (show p + 0 = p by omega)) h
  simp only [Preadditive.add_comp, Category.assoc, degCastHom_comp_degCastHom,
    degCastHom_eq_id, Category.id_comp] at h2
  exact h2

/-! ### The comparison out of the cone of the tensor product -/

/-- **The tensor product of the zero homomorphism is the zero homomorphism**: its degree-zero
family is the transport of the degree-zero family of zero, which is zero. -/
theorem map_zero_f {X Y : DifferentialGradedModule.{t, a, m} A} (n : ℤ) :
    (D.functor.map (0 : X ⟶ Y)).toHomologicalComplex.f n = 0 := by
  have hforget : (forgetToGradedModule A).map (0 : X ⟶ Y) = 0 :=
    GradedModule.Hom.ext fun _ => rfl
  have hshift : GradedModule.shiftOfHom
      (0 : (forgetToGradedModule A).obj X ⟶ (forgetToGradedModule A).obj Y) = 0 :=
    GradedModule.Hom.ext fun _ => zero_comp
  have hshift' : GradedModule.shiftOfHom
      (0 : (forgetToGradedModule B).obj (D.functor.obj X) ⟶
        (forgetToGradedModule B).obj (D.functor.obj Y)) = 0 :=
    GradedModule.Hom.ext fun _ => zero_comp
  have key : (forgetToGradedModule B).map (D.functor.map (0 : X ⟶ Y)) = 0 := by
    refine GradedModule.shiftOfHom_injective ?_
    refine Eq.trans (D.gradedShiftMap_shiftOfHom (0 : X ⟶ Y)).symm ?_
    refine Eq.trans (congrArg (D.gradedShiftMap 0)
      ((congrArg GradedModule.shiftOfHom hforget).trans hshift)) ?_
    exact (D.gradedShiftMap_zero 0).trans hshift'.symm
  exact congrArg (fun α : (forgetToGradedModule B).obj (D.functor.obj X) ⟶
    (forgetToGradedModule B).obj (D.functor.obj Y) => α.app n) key

/-- **The tensor product of the degreewise section of the cone of `ψ` is a null-homotopy of the
tensor product of `ψ` followed by the tensor product of the cone's inclusion**: it is the tensor
product `h ⊗ 1` of the null-homotopy with the identity of the bimodule. -/
noncomputable def coneHomotopy :
    Homotopy (D.functor.map (ψ ≫ (conePackage ψ).inclusion))
      (D.functor.map (0 : M ⟶ cone ψ)) :=
  D.mapHomotopy (coneNullHomotopy ψ)

/-- The components of that null-homotopy are the components of the tensor product of the
degreewise section: both are `SheafOfModules.TensorFunctorData.shiftHom` at the degree `-1`
family of the section. -/
theorem coneHomotopy_app (n : ℤ) :
    (D.coneHomotopy ψ).app n = (D.coneSectionFamily ψ).app n :=
  congrArg (fun g => D.shiftHom (-1) g n) (coneNullHomotopy_toGradedShift ψ)

/-- The degreewise family out of which the comparison is built: the tensor product of the cone's
degreewise section, read in the degrees of the cone of the tensor product. -/
noncomputable def coneDescFamily (n : ℤ) :
    (D.functor.obj M).complex.X (n + 1) ⟶ (D.functor.obj (cone ψ)).complex.X n :=
  (D.coneSectionFamily ψ).app (n + 1) ≫
    degCastHom (D.functor.obj (cone ψ)).complex.X (show n + 1 + -1 = n by omega)

/-- The degreewise family is right-linear, in the shape `ConePackage.desc` consumes. -/
theorem coneDescFamily_mul (n i : ℤ) (U : Cᵒᵖ)
    (x : ((D.functor.obj M).complex.X (n + 1)).val.obj U)
    (y : (B.complex.X i).val.obj U) :
    (D.coneDescFamily ψ (n + i)).val.app U
        (gradedCast (fun q ↦ ((D.functor.obj M).complex.X q).val.obj U) (add_right_comm n 1 i)
          (((D.functor.obj M).mul (n + 1) i).app U x y)) =
      ((D.functor.obj (cone ψ)).mul n i).app U ((D.coneDescFamily ψ n).val.app U x) y := by
  have hcast : ∀ (q : ℤ) (w : ((D.functor.obj M).complex.X (q + 1)).val.obj U),
      (D.coneDescFamily ψ q).val.app U w =
        castHom (D.functor.obj (cone ψ)).complex.X (show q + 1 + -1 = q by omega) U
          (((D.coneSectionFamily ψ).app (q + 1)).val.app U w) := fun q w =>
    degCastHom_val_app (D.functor.obj (cone ψ)).complex.X
      (show q + 1 + -1 = q by omega) U _
  have hsec : ∀ {k k' : ℤ} (h : k = k') (w : ((D.functor.obj M).complex.X k).val.obj U),
      ((D.coneSectionFamily ψ).app k').val.app U
          (castHom (D.functor.obj M).complex.X h U w) =
        castHom (D.functor.obj (cone ψ)).complex.X (show k + -1 = k' + -1 by omega) U
          (((D.coneSectionFamily ψ).app k).val.app U w) := by
    intro k k' h w
    subst h
    rfl
  have hmul : ∀ (q : ℤ) (w : ((D.functor.obj M).complex.X q).val.obj U),
      ((D.coneSectionFamily ψ).app (q + i)).val.app U
          (((D.functor.obj M).mul q i).app U w y) =
        castHom (D.functor.obj (cone ψ)).complex.X
          (show q + -1 + i = q + i + -1 by omega) U
          (((D.functor.obj (cone ψ)).mul (q + -1) i).app U
            (((D.coneSectionFamily ψ).app q).val.app U w) y) := fun q w =>
    ((D.coneSectionFamily ψ).map_smul q i U w y).trans
      (GradedModule.shift_smul ((forgetToGradedModule B).obj (D.functor.obj (cone ψ))) (-1)
        q i U (((D.coneSectionFamily ψ).app q).val.app U w) y)
  refine Eq.trans (hcast (n + i) _) ?_
  refine Eq.trans (congrArg (castHom (D.functor.obj (cone ψ)).complex.X
      (show n + i + 1 + -1 = n + i by omega) U)
    (Eq.trans (congrArg (((D.coneSectionFamily ψ).app (n + i + 1)).val.app U)
        (castHom_apply (D.functor.obj M).complex.X (add_right_comm n 1 i) U
          (((D.functor.obj M).mul (n + 1) i).app U x y)).symm)
      (Eq.trans (hsec (add_right_comm n 1 i) (((D.functor.obj M).mul (n + 1) i).app U x y))
        (congrArg (castHom (D.functor.obj (cone ψ)).complex.X
          (show n + 1 + i + -1 = n + i + 1 + -1 by omega) U)
          (hmul (n + 1) x))))) ?_
  refine Eq.trans (Cofree.castHom_castHom (D.functor.obj (cone ψ)).complex.X _ _ U _) ?_
  refine Eq.trans (Cofree.castHom_castHom (D.functor.obj (cone ψ)).complex.X _ _ U _) ?_
  refine Eq.trans ?_ (congrArg (fun w => ((D.functor.obj (cone ψ)).mul n i).app U w y)
    (hcast n x)).symm
  exact (mul_app_castHom (D.functor.obj (cone ψ)) (show n + 1 + -1 = n by omega) i U
    (((D.coneSectionFamily ψ).app (n + 1)).val.app U x) y).symm

/-- The degreewise family is a null-homotopy of the tensor product of `ψ` followed by the tensor
product of the cone's inclusion, in the shape `ConePackage.desc` consumes. -/
theorem coneDescFamily_delta (n : ℤ) :
    D.coneDescFamily ψ n ≫ (D.functor.obj (cone ψ)).complex.d n (n + 1) +
        (D.functor.obj M).complex.d (n + 1) (n + 1 + 1) ≫ D.coneDescFamily ψ (n + 1) =
      (D.functor.map ψ).toHomologicalComplex.f (n + 1) ≫
        (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f (n + 1) := by
  have hc := (D.coneHomotopy ψ).comm (n + 1)
  rw [D.map_zero_f (n + 1), sub_zero, D.coneHomotopy_app ψ (n + 1),
    D.coneHomotopy_app ψ (n + 1 + 1)] at hc
  refine Eq.trans ?_ (Eq.trans hc.symm ?_)
  · refine congrArg₂ (· + ·) ?_ ?_
    · exact (Category.assoc _ _ _).trans (congrArg
        (fun w => (D.coneSectionFamily ψ).app (n + 1) ≫ w)
        (degCastHom_comp_d (D.functor.obj (cone ψ)).complex
          (show n + 1 + -1 = n by omega) (n + 1)))
    · exact (Category.assoc _ _ _).symm.trans (congrArg
        (fun w => ((D.functor.obj M).complex.d (n + 1) (n + 1 + 1) ≫
          (D.coneSectionFamily ψ).app (n + 1 + 1)) ≫ w)
        (degCastHom_eq_eqToHom (D.functor.obj (cone ψ)).complex.X
          (show n + 1 + 1 + -1 = n + 1 by omega)))
  · rw [show D.functor.map (ψ ≫ (conePackage ψ).inclusion) =
      D.functor.map ψ ≫ D.functor.map (conePackage ψ).inclusion from
        D.functor.map_comp ψ (conePackage ψ).inclusion]
    rfl

/-- **The comparison from the cone of the tensor product of `ψ` to the tensor product of the cone
of `ψ`**: the homomorphism out of the cone determined by the tensor product of the cone's
inclusion together with the tensor product of its degreewise section. -/
noncomputable def coneDesc : cone (D.functor.map ψ) ⟶ D.functor.obj (cone ψ) :=
  (conePackage (D.functor.map ψ)).desc (D.functor.map (conePackage ψ).inclusion)
    (D.coneDescFamily ψ) (D.coneDescFamily_mul ψ) (D.coneDescFamily_delta ψ)

/-- The degree-`n` component of the comparison is the degreewise splitting of the cone followed
by its two coordinates. -/
theorem coneDesc_f (n : ℤ) :
    (D.coneDesc ψ).toHomologicalComplex.f n =
      ((conePackage (D.functor.map ψ)).componentIso n).hom ≫
        biprod.desc (D.coneDescFamily ψ n)
          ((D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f n) :=
  (conePackage (D.functor.map ψ)).desc_f (D.functor.map (conePackage ψ).inclusion)
    (D.coneDescFamily ψ) (D.coneDescFamily_mul ψ) (D.coneDescFamily_delta ψ) n

/-! ### The comparison is an isomorphism -/

/-- The tensor product of the degreewise retraction of the cone's inclusion, in degree `n`. -/
noncomputable def coneRetrApp (n : ℤ) :
    (D.functor.obj (cone ψ)).complex.X n ⟶ (D.functor.obj M₂).complex.X n :=
  (D.coneRetrFamily ψ).app n ≫
    degCastHom (D.functor.obj M₂).complex.X (show n + 0 = n by omega)

/-- A right-linear family commutes with transport along an equality of degrees. -/
private theorem degCastHom_comp_shift_app {X Y : GradedModule.{t, a, m} B.toGradedAlgebra} {k : ℤ}
    (α : X ⟶ Y.shift k) {p q : ℤ} (h : p = q) :
    degCastHom X.piece h ≫ α.app q =
      α.app p ≫ degCastHom Y.piece (show p + k = q + k by omega) :=
  (GradedModule.degCastHom_comp_app α h).trans
    (congrArg (fun w => α.app p ≫ w) (GradedModule.degCastHom_shift_piece Y k h))

/-- The degreewise section followed by the first coordinate is the identity. -/
theorem coneDescFamily_coneFirstFamily (n : ℤ) :
    D.coneDescFamily ψ n ≫ (D.coneFirstFamily ψ).app n =
      𝟙 ((D.functor.obj M).complex.X (n + 1)) := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun w => (D.coneSectionFamily ψ).app (n + 1) ≫ w)
    (degCastHom_comp_shift_app (D.coneFirstFamily ψ) (show n + 1 + -1 = n by omega))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ _) (D.coneSectionFamily_coneFirstFamily ψ (n + 1))) ?_
  exact (degCastHom_comp_degCastHom (D.functor.obj M).complex.X _ _).trans
    (degCastHom_eq_id (D.functor.obj M).complex.X _)

/-- The tensor product of the retraction, read in the two spellings of the degree. -/
theorem degCastHom_coneRetrFamily_app (n : ℤ) :
    degCastHom (D.functor.obj (cone ψ)).complex.X (show n + 1 + -1 = n by omega) ≫
        (D.coneRetrFamily ψ).app n =
      (D.coneRetrFamily ψ).app (n + 1 + -1) ≫
        degCastHom (D.functor.obj M₂).complex.X (show n + 1 + -1 + 0 = n + 0 by omega) :=
  degCastHom_comp_shift_app (D.coneRetrFamily ψ) (show n + 1 + -1 = n by omega)

/-- The degreewise section is annihilated by the retraction. -/
theorem coneDescFamily_coneRetrApp (n : ℤ) :
    D.coneDescFamily ψ n ≫ D.coneRetrApp ψ n = 0 := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun w => (D.coneSectionFamily ψ).app (n + 1) ≫ w)
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (fun w => w ≫ degCastHom (D.functor.obj M₂).complex.X
          (show n + 0 = n by omega)) (D.degCastHom_coneRetrFamily_app ψ n))
        (Category.assoc _ _ _)))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun w => w ≫ (degCastHom (D.functor.obj M₂).complex.X
      (show n + 1 + -1 + 0 = n + 0 by omega) ≫
      degCastHom (D.functor.obj M₂).complex.X (show n + 0 = n by omega)))
    (D.coneSectionFamily_coneRetrFamily ψ (n + 1))) ?_
  exact zero_comp

/-- The tensor product of the cone's inclusion is annihilated by the first coordinate. -/
theorem coneIncl_f_coneFirstFamily (n : ℤ) :
    (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫
      (D.coneFirstFamily ψ).app n = 0 := by
  have h := D.coneIncl_coneFirstFamily ψ n
  refine (cancel_mono (degCastHom
    (((forgetToGradedModule B).obj (D.functor.obj M)).shift 1).piece
      (show n = n + 0 by omega))).1 ?_
  refine Eq.trans ?_ (Eq.trans h (zero_comp).symm)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun w =>
      (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫ w)
    (GradedModule.degCastHom_comp_app (D.coneFirstFamily ψ)
      (show n = n + 0 by omega)).symm) ?_
  exact (Category.assoc _ _ _).symm

/-- The tensor product of the cone's inclusion followed by the retraction, with the transport
cancelled. -/
theorem coneIncl_f_coneRetrFamily_app (n : ℤ) :
    (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫
        (D.coneRetrFamily ψ).app n =
      degCastHom (D.functor.obj M₂).complex.X (show n = n + 0 by omega) := by
  have hmid : (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫
        (D.coneRetrFamily ψ).app n ≫
          degCastHom (D.functor.obj M₂).complex.X (show n + 0 = n + 0 + 0 by omega) =
      degCastHom (D.functor.obj M₂).complex.X (show n = n + 0 + 0 by omega) := by
    have e1 : (D.coneRetrFamily ψ).app n ≫
          degCastHom (D.functor.obj M₂).complex.X (show n + 0 = n + 0 + 0 by omega) =
        degCastHom (D.functor.obj (cone ψ)).complex.X (show n = n + 0 by omega) ≫
          (D.coneRetrFamily ψ).app (n + 0) :=
      (degCastHom_comp_shift_app (D.coneRetrFamily ψ) (show n = n + 0 by omega)).symm
    refine Eq.trans (congrArg (fun w =>
      (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫ w) e1) ?_
    exact (Category.assoc _ _ _).symm.trans (D.coneIncl_coneRetrFamily ψ n)
  refine (cancel_mono (degCastHom (D.functor.obj M₂).complex.X
    (show n + 0 = n + 0 + 0 by omega))).1 ?_
  refine Eq.trans (Category.assoc _ _ _) (hmid.trans ?_)
  exact (degCastHom_comp_degCastHom (D.functor.obj M₂).complex.X
    (show n = n + 0 by omega) (show n + 0 = n + 0 + 0 by omega)).symm

/-- The tensor product of the cone's inclusion followed by the retraction is the identity. -/
theorem coneIncl_f_coneRetrApp (n : ℤ) :
    (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f n ≫
        D.coneRetrApp ψ n =
      𝟙 ((D.functor.obj M₂).complex.X n) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun w => w ≫ degCastHom (D.functor.obj M₂).complex.X
    (show n + 0 = n by omega)) (D.coneIncl_f_coneRetrFamily_app ψ n)) ?_
  exact (degCastHom_comp_degCastHom (D.functor.obj M₂).complex.X _ _).trans
    (degCastHom_eq_id (D.functor.obj M₂).complex.X _)

/-- The two diagonal products add up to the identity of the tensor product of the cone. -/
theorem coneFirstFamily_coneDescFamily_add (n : ℤ) :
    (show (D.functor.obj (cone ψ)).complex.X n ⟶ (D.functor.obj (cone ψ)).complex.X n from
          (D.coneFirstFamily ψ).app n ≫ D.coneDescFamily ψ n) +
        (show (D.functor.obj (cone ψ)).complex.X n ⟶ (D.functor.obj (cone ψ)).complex.X n from
          D.coneRetrApp ψ n ≫
            (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f n) =
      𝟙 ((D.functor.obj (cone ψ)).complex.X n) := by
  refine Eq.trans ?_ (D.coneFirstFamily_coneSectionFamily_add ψ n)
  refine congrArg₂ (· + ·) (Category.assoc _ _ _).symm ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun w => (D.coneRetrFamily ψ).app n ≫ w) ?_
  refine Eq.trans (GradedModule.degCastHom_comp_hom_f
    (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex
    (show n + 0 = n by omega)) ?_
  have hr : (GradedModule.shiftOfHom ((forgetToGradedModule B).map
          (D.functor.map (conePackage ψ).inclusion))).app (n + 0) ≫
        degCastHom (D.functor.obj (cone ψ)).complex.X (show n + 0 + 0 = n by omega) =
      (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f (n + 0) ≫
        degCastHom (D.functor.obj (cone ψ)).complex.X (show n + 0 = n by omega) :=
    (Category.assoc _ _ _).trans (congrArg
      (fun w => (D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f (n + 0) ≫ w)
      (degCastHom_comp_degCastHom (D.functor.obj (cone ψ)).complex.X
        (show n + 0 = n + 0 + 0 by omega) (show n + 0 + 0 = n by omega)))
  exact hr.symm

/-- **The degree-`n` component of the comparison is an isomorphism.** The degreewise splitting
identifies it with the morphism out of a binary biproduct whose two components are the tensor
product of the cone's degreewise section and the tensor product of the cone's inclusion
(`TensorFunctorData.coneDesc_f`), and the five splitting relations exhibit the tensor product of
the first coordinate and the tensor product of the degreewise retraction as the two components
of an inverse. -/
theorem isIso_coneDesc_f (n : ℤ) : IsIso ((D.coneDesc ψ).toHomologicalComplex.f n) := by
  have hdesc : IsIso (biprod.desc (D.coneDescFamily ψ n)
      ((D.functor.map (conePackage ψ).inclusion).toHomologicalComplex.f n)) :=
    biprod.isIso_desc _ _ ((D.coneFirstFamily ψ).app n) (D.coneRetrApp ψ n)
      (D.coneDescFamily_coneFirstFamily ψ n) (D.coneDescFamily_coneRetrApp ψ n)
      (D.coneIncl_f_coneFirstFamily ψ n) (D.coneIncl_f_coneRetrApp ψ n)
      (D.coneFirstFamily_coneDescFamily_add ψ n)
  rw [D.coneDesc_f ψ n]
  infer_instance

/-- **The comparison is an isomorphism of right differential graded `ℬ`-modules**, being an
isomorphism in every degree. -/
theorem isIso_coneDesc : IsIso (D.coneDesc ψ) :=
  isIso_of_componentwise _ (D.isIso_coneDesc_f ψ)

/-- **The cone of the tensor product of `ψ` is the tensor product of the cone of `ψ`**:
`C(ψ ⊗_𝒜 1) ≅ C(ψ) ⊗_𝒜 𝒩`, as right differential graded `ℬ`-modules. -/
noncomputable def coneIso : cone (D.functor.map ψ) ≅ D.functor.obj (cone ψ) :=
  haveI := D.isIso_coneDesc ψ
  asIso (D.coneDesc ψ)

/-- The forward morphism of `coneIso` is the comparison `coneDesc`. -/
@[simp]
theorem coneIso_hom : (D.coneIso ψ).hom = D.coneDesc ψ := rfl

/-- **The cone of the tensor product of `ψ` is the tensor product of the cone of `ψ`**, as
complexes of sheaves of modules. -/
noncomputable def coneComplexIso :
    (cone (D.functor.map ψ)).complex ≅ (D.functor.obj (cone ψ)).complex :=
  haveI (n : ℤ) : IsIso ((D.coneDesc ψ).toHomologicalComplex.f n) := D.isIso_coneDesc_f ψ n
  haveI : IsIso (D.coneDesc ψ).toHomologicalComplex :=
    HomologicalComplex.Hom.isIso_of_components _
  asIso (D.coneDesc ψ).toHomologicalComplex

/-- The forward morphism of `coneComplexIso` is the morphism of complexes underlying the
comparison `coneDesc`. -/
@[simp]
theorem coneComplexIso_hom :
    (D.coneComplexIso ψ).hom = (D.coneDesc ψ).toHomologicalComplex := rfl

end TensorFunctorData

/-! ### The exactness of `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` -/

namespace DifferentialGradedModule

universe a' m' v' u'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj} {A A' : DifferentialGradedAlgebra.{t, a} R}
  {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}
  (P : PullbackData.{t, a, m, v, u, a', m', v', u'} φ)
  (D : TensorFunctorData.{t, a, m, z, s} A A' N)
  {M M₂ : DifferentialGradedModule.{t, a', m'} B} (ψ : M ⟶ M₂)

/-- **The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of [Stacks, Tag 0FTE] commutes with cones**: the image of
the cone of `ψ` is the cone of the image of `ψ`, as right differential graded `𝒜'`-modules. The
two halves are `PullbackData.coneIso` for the pullback and `TensorFunctorData.coneIso` for the
tensor product, and the composite is read through
`DifferentialGradedModule.pullbackTensorFunctor_obj` and `pullbackTensorFunctor_map`, both of
which hold by definition. -/
noncomputable def pullbackTensorConeIso :
    (pullbackTensorFunctor P D).obj (cone ψ) ≅ cone ((pullbackTensorFunctor P D).map ψ) :=
  D.functor.mapIso (P.coneIso ψ).symm ≪≫ (D.coneIso (P.map ψ)).symm

/-- **The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` commutes with cones**, as complexes of sheaves of modules.
This is the `coneIso` clause of
`SheafOfModules.DifferentialGradedModule.PullbackTensorExactnessData`. -/
noncomputable def pullbackTensorConeComplexIso :
    ((pullbackTensorFunctor P D).obj (cone ψ)).complex ≅
      (cone ((pullbackTensorFunctor P D).map ψ)).complex :=
  (toCochainComplex A').mapIso (pullbackTensorConeIso P D ψ)

end DifferentialGradedModule

end SheafOfModules

end
