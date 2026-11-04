module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOnBoundedResolutions

/-!
# The derived lower shriek of modules over essentially small sites

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `O_D` be a sheaf of rings
on `D` and set `O_C = g^{-1} O_D`. `StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/`
`DerivedExistence.lean` and `DerivedAdjunction.lean` reduce the existence of the unbounded left
derived functor `Lg_! : D(O_C) ⥤ D(O_D)` of `g_! : Mod(O_C) ⥤ Mod(O_D)` and its adjointness to
`g^*` (Stacks 07AC) to one acyclicity statement, under the hypothesis that `C` is `w`-small,
`w` being the universe of the module sections.

The sites of algebraic stacks — the lisse-étale and flat-fppf sites of Stacks 0787 and the
étale and fppf sites of Stacks 06TP — are not small: their objects live one universe above the
module sections. They are *essentially* small. This file runs the same argument under essential
smallness, which is all the generation lemma of Stacks 03EW (3) needs, and adds the module form
of the last assertion of Stacks 07AS, `g^* Lg_! = id` whenever the ordinary unit is invertible.

## Main results

All names below are in the namespace `Stacks.Cohomology.DerivedLowerShriek`.

* `exists_epi_isSumOfExtensionByZeroUnits_of_essentiallySmall`: **Stacks 03EW (3)** over an
  essentially small site: every sheaf of modules is a quotient of a direct sum of the
  `j_{U!} O_U`.
* `hasPointwiseLeftDerivedLowerShriek_of_essentiallySmall`: existence of `Lg_!`, given the
  acyclicity statement.
* `isLeftDerivedFunctor_totalLeftDerivedLowerShriek_comp`: `Lg_!` is absolute, being constructed
  by resolutions; this is the second instance hypothesis of `derivedLowerShriekAdjunction`.
* `isIso_totalLeftDerivedLowerShriekAdjunction_unit`: the unit of `Lg_! ⊣ g^*` is invertible as
  soon as the unit of `g_! ⊣ g^*` is (no smallness needed).

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open StacksDraft.UnboundedLeftDerivedFunctor

universe w t t' v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

section Generation

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).IsRightAdjoint]

/-- **Stacks 03EW (3) over an essentially small site**, for an arbitrary sheaf of rings: every
sheaf of modules receives an epimorphism from a direct sum of extensions by zero of the
structure sheaves of the slices. Index the sum by pairs `(V, x)` with `V` an object of a small
model of `C` and `x` a section over the corresponding object of `C`; every section over an
arbitrary object is carried to one of these by an isomorphism, so the sum still detects
morphisms. -/
theorem exists_epi_isSumOfExtensionByZeroUnits_of_essentiallySmall [EssentiallySmall.{w} C]
    (M : SheafOfModules.{w} R) :
    ∃ (N : SheafOfModules.{w} R) (_ : IsSumOfExtensionByZeroUnits R N) (p : N ⟶ M), Epi p := by
  classical
  let e := equivSmallModel.{w} C
  let σ : Type w := Σ V : SmallModel.{w} C, (M.val.obj (op (e.inverse.obj V)) : Type w)
  let U : σ → C := fun i => e.inverse.obj i.1
  refine ⟨∐ fun i : σ => extensionByZeroUnit R (U i), ⟨σ, U, ⟨Iso.refl _⟩⟩,
    Sigma.desc fun i =>
      (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R (U i) M).symm i.2, ⟨?_⟩⟩
  intro N f g h
  have key (i : σ) : f.val.app (op (U i)) i.2 = g.val.app (op (U i)) i.2 := by
    have hh := Sigma.ι (fun i : σ => extensionByZeroUnit R (U i)) i ≫= h
    simp only [← Category.assoc, Sigma.ι_desc] at hh
    have he := congrArg
      (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R (U i) N) hh
    rwa [Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality,
      Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality,
      Equiv.apply_symm_apply] at he
  have hs (Y : C) (x : M.val.obj (op Y)) : f.val.app (op Y) x = g.val.app (op Y) x := by
    let a : Y ≅ e.inverse.obj (e.functor.obj Y) := e.unitIso.app Y
    let φ := (PresheafOfModules.toPresheaf R.obj).map f.val
    let ψ := (PresheafOfModules.toPresheaf R.obj).map g.val
    let P := (PresheafOfModules.toPresheaf R.obj).obj M.val
    let x' : P.obj (op Y) := x
    show φ.app (op Y) x' = ψ.app (op Y) x'
    have hx : x' = P.map a.hom.op (P.map a.inv.op x') := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, a.hom_inv_id, op_id]
      simp
    rw [hx, NatTrans.naturality_apply φ a.hom.op, NatTrans.naturality_apply ψ a.hom.op]
    exact congrArg _ (key ⟨e.functor.obj Y, P.map a.inv.op x'⟩)
  refine (SheafOfModules.toSheaf R).map_injective (Sheaf.hom_ext ?_)
  ext Y x
  exact hs Y.unop x

end Generation

section LowerShriek

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}] [EssentiallySmall.{w} C]
  [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
    (𝟙 ((inverseImageRing J K f O).over U) :
      (inverseImageRing J K f O).over U ⟶ (inverseImageRing J K f O).over U)).IsRightAdjoint]
  [(SheafOfModules.pushforward.{w} (F := f) (idRingMap J K f O)).IsRightAdjoint]
  [HasDerivedCategory.{t} (SheafOfModules.{w} (inverseImageRing J K f O))]
  [HasDerivedCategory.{t'} (SheafOfModules.{w} O)]

omit [f.IsCocontinuous J K] in
/-- **Stacks 07AC, existence, over an essentially small site and for any model of the derived
categories**, conditional on the acyclicity statement: if the lower-shriek functor carries every
bounded above acyclic complex whose terms are direct sums of the `j_{U!} O_U` to an acyclic
complex, then it has an unbounded left derived functor. This is
`hasPointwiseLeftDerivedLowerShriek_of_acyclic` with `Small.{w} C` weakened to essential
smallness. -/
theorem hasPointwiseLeftDerivedLowerShriek_of_essentiallySmall
    (hFP : ∀ (a : ℤ) (L : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ),
      L.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (L.X n)) → L.Acyclic →
      (((lowerShriekModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic) :
    (lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (sourceQuasiIso J K f O) := by
  have := hasExactColimitsOfShape_nat (inverseImageRing J K f O)
  have := hasExactColimitsOfShape_nat O
  exact CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex
    (lowerShriekModules J K f O) (IsSumOfExtensionByZeroUnits (inverseImageRing J K f O))
    (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
    (exists_epi_isSumOfExtensionByZeroUnits_of_essentiallySmall _) hFP

section Total

variable [(lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (sourceQuasiIso J K f O)]

/-- **The derived lower shriek `Lg_! : D(O_C) ⥤ D(O_D)`**, for any models of the two derived
categories: the total left derived functor of `g_!` applied degreewise. At the standard models
it is `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek`. -/
abbrev totalLeftDerivedLowerShriek :
    DerivedCategory (SheafOfModules.{w} (inverseImageRing J K f O)) ⥤
      DerivedCategory (SheafOfModules.{w} O) :=
  Functor.totalLeftDerived (lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh (sourceQuasiIso J K f O)

/-- The comparison `Qh ⋙ Lg_! ⟶ g_! ⋙ Qh` exhibiting `Lg_!` as a left derived functor. -/
abbrev totalLeftDerivedLowerShriekCounit :
    DerivedCategory.Qh ⋙ totalLeftDerivedLowerShriek J K f O ⟶
      lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh :=
  Functor.totalLeftDerivedCounit (lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh (sourceQuasiIso J K f O)

omit [f.IsCocontinuous J K] in
/-- **The derived lower-shriek functor over an essentially small site is absolute**: under the
acyclicity statement, `Lg_!` stays a left derived functor after composition with any functor out
of `D(O_D)`, being constructed by resolutions. -/
theorem isLeftDerivedFunctor_totalLeftDerivedLowerShriek_comp
    (hFP : ∀ (a : ℤ) (L : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ),
      L.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (L.X n)) → L.Acyclic →
      (((lowerShriekModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    {E : Type*} [Category E] (G : DerivedCategory (SheafOfModules.{w} O) ⥤ E) :
    (totalLeftDerivedLowerShriek J K f O ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (totalLeftDerivedLowerShriek J K f O) G).inv ≫
        Functor.whiskerRight (totalLeftDerivedLowerShriekCounit J K f O) G)
      (sourceQuasiIso J K f O) := by
  have := hasExactColimitsOfShape_nat (inverseImageRing J K f O)
  have := hasExactColimitsOfShape_nat O
  exact Functor.isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex
    (lowerShriekModules J K f O) (IsSumOfExtensionByZeroUnits (inverseImageRing J K f O))
    (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
    (exists_epi_isSumOfExtensionByZeroUnits_of_essentiallySmall _) hFP
    DerivedCategory.Qh (totalLeftDerivedLowerShriek J K f O)
    (totalLeftDerivedLowerShriekCounit J K f O) G

omit [f.IsCocontinuous J K] in
/-- **`Lg_!` is computed degreewise on a bounded above complex of direct sums of the
`j_{U!} O_U`, over an essentially small site** (Stacks 0794): the comparison
`Qh ⋙ Lg_! ⟶ g_! ⋙ Qh` is invertible there, these complexes being cellular for the class with
which `Lg_!` is constructed. -/
lemma isIso_totalLeftDerivedLowerShriekCounit_app
    (hFP : ∀ (a : ℤ) (L : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ),
      L.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (L.X n)) → L.Acyclic →
      (((lowerShriekModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    (L : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ)
    (hL0 : CochainComplex.IsStrictlyLE L 0)
    (hL : ∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (L.X n)) :
    IsIso ((totalLeftDerivedLowerShriekCounit J K f O).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) := by
  have := hasExactColimitsOfShape_nat (inverseImageRing J K f O)
  have := hasExactColimitsOfShape_nat O
  have : PreservesColimitsOfShape ℕ (lowerShriekModules J K f O) :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0}
      (adjunctionModules J K f O)).preservesColimitsOfShape
  have h := derives_cellularLocalizerMorphism (lowerShriekModules J K f O)
    (IsSumOfExtensionByZeroUnits (inverseImageRing J K f O))
    (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
    (exists_epi_isSumOfExtensionByZeroUnits_of_essentiallySmall _) hFP
  have := isLeftDerivabilityStructure_cellularLocalizerMorphism
    _ (hasLeftResolutions_cellularLocalizerMorphism
      (IsSumOfExtensionByZeroUnits (inverseImageRing J K f O))
      (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
      (exists_epi_isSumOfExtensionByZeroUnits_of_essentiallySmall _))
  exact CategoryTheory.LeftDerivedByResolutions.isIso_app_of_derives _ _ h DerivedCategory.Qh _ _
    ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L,
      ⟨L, isPCellular_of_isStrictlyLE_zero _ L hL, ⟨Iso.refl _⟩⟩⟩

/-- Degreewise restriction is the right derived functor of restriction, its comparison being
invertible, restriction being exact. -/
instance isRightDerivedFunctor_mapDerivedCategory_restrictionModules :
    (restrictionModules J K f O).mapDerivedCategory.IsRightDerivedFunctor
      (restrictionModules J K f O).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (SheafOfModules.{w} O) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    ((restrictionModules J K f O).mapDerivedCategoryFactorsh)

variable [IsGrothendieckAbelian.{w} (SheafOfModules.{w} O)]

/-- **Stacks 07AC, the derived adjunction, for any models**: `Lg_! ⊣ g^*`, `g^*` being
restriction applied degreewise. This is Stacks 09T5 on the unbounded derived category of the
Grothendieck abelian category `Mod(O_D)`; the absoluteness of `Lg_!` is
`isLeftDerivedFunctor_totalLeftDerivedLowerShriek_comp`. -/
def totalLeftDerivedLowerShriekAdjunction
    (hFP : ∀ (a : ℤ) (L : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ),
      L.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (L.X n)) → L.Acyclic →
      (((lowerShriekModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic) :
    totalLeftDerivedLowerShriek J K f O ⊣ (restrictionModules J K f O).mapDerivedCategory :=
  have := isLeftDerivedFunctor_totalLeftDerivedLowerShriek_comp J K f O hFP
    (restrictionModules J K f O).mapDerivedCategory
  Stacks.Cohomology.UnboundedComplexes.derivedAdjunction (homotopyAdjunction J K f O)
    (sourceQuasiIso J K f O) (totalLeftDerivedLowerShriekCounit J K f O)
    (restrictionModules J K f O).mapDerivedCategoryFactorsh.inv

/-- **The unit of `Lg_! ⊣ g^*` is invertible as soon as the unit of `g_! ⊣ g^*` is**, for any
models. This is the module form of the last assertion of Stacks 07AS, `g^* Lg_! = id`, which the
source reads off from `g^* g_! = id` (Stacks 0789).

The argument is uniqueness of left derived functors: an invertible ordinary unit stays invertible
degreewise on complexes and hence on the homotopy category, derived restriction is degreewise
restriction up to its invertible comparison, so the identity of `D(O_C)` is a left derived
functor of `Qh ⋙ Lg_! ⋙ g^*`; the unit of the derived adjunction is the canonical comparison
between that left derived functor and `Lg_! ⋙ g^*`, hence invertible. -/
theorem isIso_totalLeftDerivedLowerShriekAdjunction_unit
    (hFP : ∀ (a : ℤ) (L : CochainComplex (SheafOfModules.{w} (inverseImageRing J K f O)) ℤ),
      L.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (L.X n)) → L.Acyclic →
      (((lowerShriekModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    (hunit : IsIso (adjunctionModules J K f O).unit) :
    IsIso (totalLeftDerivedLowerShriekAdjunction J K f O hFP).unit := by
  have := isLeftDerivedFunctor_totalLeftDerivedLowerShriek_comp J K f O hFP
    (restrictionModules J K f O).mapDerivedCategory
  set A := SheafOfModules.{w} (inverseImageRing J K f O)
  set W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  set Gh := lowerShriekOnHomotopy J K f O
  set Lg := totalLeftDerivedLowerShriek J K f O
  set Fd := (restrictionModules J K f O).mapDerivedCategory
  set α := totalLeftDerivedLowerShriekCounit J K f O
  set β := (restrictionModules J K f O).mapDerivedCategoryFactorsh.inv with hβ
  set adjh := homotopyAdjunction J K f O
  have hadjhunit : ∀ X, IsIso (adjh.unit.app X) := by
    rintro ⟨X⟩
    let v := (NatTrans.mapHomologicalComplex (adjunctionModules J K f O).unit
      (ComplexShape.up ℤ)).app X
    have (n : ℤ) : IsIso (v.f n) :=
      inferInstanceAs (IsIso ((adjunctionModules J K f O).unit.app (X.X n)))
    have : IsIso v := HomologicalComplex.Hom.isIso_of_components _
    show IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map v)
    infer_instance
  have : IsIso adjh.unit := NatIso.isIso_of_isIso_app _
  have : IsIso β := by
    rw [hβ]
    infer_instance
  set ηcmp := DerivedCategory.Qh.rightUnitor.hom ≫ DerivedCategory.Qh.leftUnitor.inv ≫
    Functor.whiskerRight adjh.unit DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Gh β ≫
    (Functor.associator _ _ _).inv with hηcmp
  have : IsIso ηcmp := by
    rw [hηcmp]
    infer_instance
  exact (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift (Lg ⋙ Fd)
    ((Functor.associator DerivedCategory.Qh Lg Fd).inv ≫ Functor.whiskerRight α Fd) W
    (𝟭 (DerivedCategory A)) ηcmp).mp
      (Functor.isLeftDerivedFunctor_of_inverts W (𝟭 (DerivedCategory A)) (asIso ηcmp))

end Total

end LowerShriek

end Stacks.Cohomology.DerivedLowerShriek

end
