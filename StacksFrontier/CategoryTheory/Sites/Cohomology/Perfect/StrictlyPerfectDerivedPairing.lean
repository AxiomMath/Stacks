module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatExactPairing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.LeftDualOfALocallyStrictlyPerfectComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.TermsOfADualComplexOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.StrictlyPerfectIsKFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionComplexMonoidal

/-!
# A strictly perfect complex is a dualizable object of the derived category

Let `(C, O)` be a ringed site and `P` a strictly perfect complex of `O`-modules (Stacks 08FL).
Its dual complex `P^∨ = SheafHom^•(P, O)` is a left dual of `P` in the monoidal category of
complexes (Stacks 0FPR), and both are K-flat, so the pairing descends to the derived category:
the image of `P` in `D(O)` is dualizable for the derived tensor product of Stacks 0FPT.

## Main results

* `Stacks.SheafOfModules.Strict.isZero_of_exactPairing`: a dual of a zero module is zero.
* `Stacks.SheafOfModules.Strict.isFlat_of_exactPairing`: a module with a left dual partner is
  flat.
* `Stacks.SheafOfModules.Strict.isLocallyStrictlyPerfect_of_isStrictlyPerfect`: a strictly
  perfect complex is locally strictly perfect.
* `Stacks.SheafOfModules.Strict.exactPairingQStrictlyPerfect`: the exact pairing of `Q P` and
  `Q P^∨` in `D(O)`.

## References

* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

section Dualizable

/-- **A dual of a zero module is zero.** The identity of `Y` factors, by a triangle identity,
through `Y ⊗ X ⊗ Y`, which vanishes with `X`. -/
theorem isZero_of_exactPairing {X Y : Mod R}
    (p : @ExactPairing _ _ (monoidalCategory R.obj (isSheaf_ringSheaf R)) X Y) (hX : IsZero X) :
    IsZero Y := by
  let : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  let : ExactPairing X Y := p
  have hZ : IsZero (Y ⊗ X ⊗ Y) := by
    have hXY : IsZero (X ⊗ Y) := by
      rw [IsZero.iff_id_eq_zero] at hX ⊢
      rw [← MonoidalCategory.id_whiskerRight, hX, MonoidalPreadditive.zero_whiskerRight]
    rw [IsZero.iff_id_eq_zero] at hXY ⊢
    rw [← MonoidalCategory.whiskerLeft_id, hXY, MonoidalPreadditive.whiskerLeft_zero]
  have h := ExactPairing.coevaluation_evaluation X Y
  simp only [hZ.eq_of_tgt (Y ◁ η_ X Y) 0, zero_comp] at h
  refine (IsZero.iff_id_eq_zero Y).2 ?_
  calc 𝟙 Y = (ρ_ Y).inv ≫ ((ρ_ Y).hom ≫ (λ_ Y).inv) ≫ (λ_ Y).hom := by simp
    _ = 0 := by rw [← h, zero_comp, comp_zero]

variable [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A module paired with another is flat.** If `X ⊣ Y` is an exact pairing for the tensor
product of Stacks 01CA, then `- ⊗ Y` is right adjoint to `- ⊗ X`, so it preserves limits, and a
tensor product preserves colimits in each variable; so `- ⊗ Y` is exact. -/
theorem isFlat_of_exactPairing {X Y : Mod R}
    (p : @ExactPairing _ _ (monoidalCategory R.obj (isSheaf_ringSheaf R)) X Y) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) Y := by
  let : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
  let : ExactPairing X Y := p
  have hL : PreservesFiniteLimits (MonoidalCategory.tensorRight Y) :=
    have : PreservesLimitsOfSize.{0, 0} (MonoidalCategory.tensorRight Y) :=
      (tensorRightAdjunction X Y).rightAdjoint_preservesLimits
    inferInstance
  have hC : PreservesFiniteColimits (MonoidalCategory.tensorRight Y) :=
    ⟨fun _ _ _ => ⟨fun {F} => preservesColimit_tensorRight R F Y⟩⟩
  exact (exactFunctor_iff _).2
    ⟨@preservesFiniteLimits_of_natIso _ _ _ _ _ _ (tensorRightIsoSheafTensor R Y) hL,
      @preservesFiniteColimits_of_natIso _ _ _ _ _ _ (tensorRightIsoSheafTensor R Y) hC⟩

end Dualizable

section LocallyStrictlyPerfect

variable [HasBinaryProducts C] [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u}]

/-- **Restriction to a slice preserves strict perfection**: it is additive, so it carries zero
terms to zero terms, and it carries a finite free module to a finite free module and a
retraction to a retraction. -/
theorem isStrictlyPerfect_restrictComplexOver {P : CochainComplex (Mod R) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf R) P) (V : C) :
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf R).over V)
      (restrictComplexOver R P V) := by
  let F := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R) V
  have : F.Additive := ⟨rfl⟩
  refine ⟨hP.bounded.subset (fun i hi => ?_), fun i => ?_⟩
  · simp only [Set.mem_ofPred_eq] at hi ⊢
    exact fun hz => hi (F.map_isZero hz)
  · obtain ⟨n, a, r, har⟩ := (isDirectSummandOfFiniteFree_iff_free _ (P.X i)).mp
      (hP.termDirectSummand i)
    let e := SheafOfModules.overFunctorFreeIso (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      V (ULift.{u} (Fin n))
    refine (isDirectSummandOfFiniteFree_iff_free _ _).mpr ⟨n, F.map a ≫ e.inv, e.hom ≫ F.map r, ?_⟩
    rw [Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp,
      ← CategoryTheory.Functor.map_comp, har, CategoryTheory.Functor.map_id]
    rfl

/-- **A strictly perfect complex is locally strictly perfect**, with the maximal sieve as the
covering of every object. -/
theorem isLocallyStrictlyPerfect_of_isStrictlyPerfect {P : CochainComplex (Mod R) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf R) P) :
    IsLocallyStrictlyPerfect R P :=
  fun U => ⟨⊤, J.top_mem U, fun V _ _ => isStrictlyPerfect_restrictComplexOver R hP V⟩

end LocallyStrictlyPerfect

section Transport

/-- The monoidal category of complexes over the re-seated tensor product
`SheafOfModules.monoidalCategorySheafTensor`: the structure the derived tensor product of
Stacks 0FPT is the localization of. -/
abbrev sheafTensorComplexMonoidal : MonoidalCategory (CochainComplex (Mod.{u, u} R) ℤ) :=
  letI := SheafOfModules.monoidalCategorySheafTensor R
  letI := SheafOfModules.symmetricCategorySheafTensor R
  letI := SheafOfModules.monoidalPreadditiveSheafTensor R
  letI := SheafOfModules.monoidalClosedSheafTensor R
  letI : ∀ X₂ : Mod.{u, u} R, PreservesColimit (Functor.empty.{0} (Mod.{u, u} R))
      ((curriedTensor (Mod.{u, u} R)).flip.obj X₂) := fun X₂ =>
    SheafOfModules.preservesColimit_tensorRight_sheafTensor R _ X₂
  inferInstance

/-- The identity functor of modules, from the spelling of the structure sheaf the tensor product of
Stacks 01CA is stated at to the one the re-seated tensor product is stated at. -/
abbrev idStrictToSheafTensor : ModSS.{u, u} R ⥤ Mod.{u, u} R := 𝟭 _

/-- The identity functor `idStrictToSheafTensor` is additive. -/
instance : (idStrictToSheafTensor R).Additive := ⟨rfl⟩

/-- **The identity functor on complexes is monoidal** from the total tensor product over the
tensor product of Stacks 01CA to the one over the re-seated tensor product: it is
`CategoryTheory.Functor.mapHomologicalComplexMonoidal` for the identity functor of modules, which
is monoidal by `SheafOfModules.idMonoidalStrictToSheafTensor`. -/
@[instance_reducible]
def complexIdMonoidal :
    @Functor.Monoidal (CochainComplex (ModSS.{u, u} R) ℤ) _ (monoidalCategoryCochainComplex R)
      (CochainComplex (Mod.{u, u} R) ℤ) _ (sheafTensorComplexMonoidal R)
      ((idStrictToSheafTensor R).mapHomologicalComplex (ComplexShape.up ℤ)) := by
  letI instSrc : MonoidalCategory (ModSS.{u, u} R) :=
    monoidalCategory R.obj (isSheaf_ringSheaf R)
  letI : @MonoidalPreadditive _ _ _ instSrc := monoidalPreadditiveRingSheaf R
  letI : (curriedTensor (ModSS.{u, u} R)).Additive := inferInstance
  letI : ∀ X₁ : ModSS.{u, u} R, ((curriedTensor (ModSS.{u, u} R)).obj X₁).Additive :=
    fun _ => inferInstance
  letI : ∀ X₁ : ModSS.{u, u} R, PreservesColimit (Functor.empty.{0} (ModSS.{u, u} R))
      ((curriedTensor (ModSS.{u, u} R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  letI : ∀ X₂ : ModSS.{u, u} R, PreservesColimit (Functor.empty.{0} (ModSS.{u, u} R))
      ((curriedTensor (ModSS.{u, u} R)).flip.obj X₂) := fun X₂ =>
    preservesColimit_tensorRight R _ X₂
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (ModSS.{u, u} R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (ModSS.{u, u} R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (ModSS.{u, u} R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  letI instTgt : MonoidalCategory (Mod.{u, u} R) := SheafOfModules.monoidalCategorySheafTensor R
  letI := SheafOfModules.symmetricCategorySheafTensor R
  letI := SheafOfModules.monoidalPreadditiveSheafTensor R
  letI := SheafOfModules.monoidalClosedSheafTensor R
  letI : ∀ X₂ : Mod.{u, u} R, PreservesColimit (Functor.empty.{0} (Mod.{u, u} R))
      ((curriedTensor (Mod.{u, u} R)).flip.obj X₂) := fun X₂ =>
    SheafOfModules.preservesColimit_tensorRight_sheafTensor R _ X₂
  letI : @Functor.Monoidal _ _ instSrc _ _ instTgt (idStrictToSheafTensor R) :=
    SheafOfModules.idMonoidalStrictToSheafTensor R
  letI : ∀ n : ℤ, PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n})) (idStrictToSheafTensor R) := fun _ =>
    inferInstanceAs (PreservesColimitsOfShape _ (𝟭 (ModSS.{u, u} R)))
  exact Functor.mapHomologicalComplexMonoidal (c := ComplexShape.up ℤ) (idStrictToSheafTensor R)

/-- **An exact pairing of complexes for the tensor product of Stacks 01CA is one for the re-seated
tensor product**, by `complexIdMonoidal`. -/
@[instance_reducible]
def exactPairingSheafTensorOfStrict {K L : CochainComplex (Mod.{u, u} R) ℤ}
    (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) :
    @ExactPairing _ _ (sheafTensorComplexMonoidal R) K L :=
  @ExactPairing.map _ _ _ _ (monoidalCategoryCochainComplex R) (sheafTensorComplexMonoidal R)
    ((idStrictToSheafTensor R).mapHomologicalComplex (ComplexShape.up ℤ))
    (complexIdMonoidal R) K L p

end Transport

section Derived

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (Z : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Z.C, HasWeakSheafify (Z.J.over V) AddCommGrpCat.{u}]
  [∀ V : Z.C, (Z.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Z.C, HasSheafify (Z.J.over V) AddCommGrpCat.{u}] [HasBinaryProducts Z.C]

/-- **The dual complex of a strictly perfect complex is K-flat.** It is bounded above, because
the dual of a zero term is zero, and its terms are flat, because each is paired with a term of
the complex (`isFlat_of_exactPairing`); Stacks 06YQ concludes. -/
theorem kFlat_dualComplex_of_isStrictlyPerfect {P : CochainComplex (Mod Z.O) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) P) :
    Stacks.SheafOfModules.IsKFlat Z.O (dualComplexOfLocallyStrictlyPerfect Z.O P
      (isLocallyStrictlyPerfect_of_isStrictlyPerfect Z.O hP)) := by
  set hPl := isLocallyStrictlyPerfect_of_isStrictlyPerfect Z.O hP
  let p := exactPairingDualComplexOfLocallyStrictlyPerfect hPl
  obtain ⟨m, hm⟩ := hP.bounded.bddBelow
  refine Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat Z.O _ ⟨-m, ?_⟩ fun j => ?_
  · refine (CochainComplex.isStrictlyLE_iff _ (-m)).2 fun j hj => ?_
    have hz : IsZero (P.X (-j)) := by
      by_contra h
      exact absurd (hm (by simpa only [Set.mem_ofPred_eq] using h)) (by omega)
    simpa only [neg_neg] using
      isZero_of_exactPairing Z.O (exactPairingX_of_complex Z.O P _ p (-j)) hz
  · simpa only [neg_neg] using
      isFlat_of_exactPairing Z.O (exactPairingX_of_complex Z.O P _ p (-j))

/-- **A strictly perfect complex is dualizable in `D(O)`**: the exact pairing of Stacks 0FPR of
`P` with its dual complex, carried to the re-seated tensor product of complexes and descended to
the derived category of Stacks 0FPT. -/
@[instance_reducible]
def exactPairingQStrictlyPerfect {P : CochainComplex (Mod Z.O) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) P) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.O
    ExactPairing (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj (dualComplexOfLocallyStrictlyPerfect Z.O P
        (isLocallyStrictlyPerfect_of_isStrictlyPerfect Z.O hP))) :=
  letI : @ExactPairing _ _ (sheafTensorComplexMonoidal Z.O) P _ :=
    exactPairingSheafTensorOfStrict Z.O (exactPairingDualComplexOfLocallyStrictlyPerfect
      (isLocallyStrictlyPerfect_of_isStrictlyPerfect Z.O hP))
  CochainComplex.KFlatMonoidal.exactPairingQ (Mod Z.O)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Z.O)
    (AlgebraicGeometry.RingedSite.kFlat_of_isStrictlyPerfect Z P hP)
    (kFlat_dualComplex_of_isStrictlyPerfect Z hP)

end Derived

end Stacks.SheafOfModules.Strict

end
