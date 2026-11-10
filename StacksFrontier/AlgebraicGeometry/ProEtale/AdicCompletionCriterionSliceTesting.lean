module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsomSupplement
public import StacksFrontier.AlgebraicGeometry.ProEtale.AdicCompletionCriterion
public import StacksFrontier.AlgebraicGeometry.ProEtale.AdicQuotientSystemOfSize
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSectionsSliceTesting
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SliceTestingFamily
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.Homology.DerivedComplete.NakayamaModule
import all StacksFrontier.AlgebraicGeometry.ProEtale.AdicCompletionCriterion

/-!
# Adic completeness of a sheaf of modules on a slice testing family, in any module universe

`StacksFrontier.AlgebraicGeometry.ProEtale.AdicCompletionCriterion` proves, for a small ringed site
with enough weakly contractible objects and modules in the universe `max u v` of the site, that
the cone of quotient maps `F ⟶ F/IⁿF` of a sheaf of modules `F` along a sheaf of ideals `I` is a
limit cone exactly when `F`, in degree zero, is derived complete along `I`, and that a derived
complete `F` with `IF = F` is zero. This file proves both for a site that is not assumed small,
with the sections of the modules in an arbitrary universe `max u v w` containing the site, the
weakly contractible objects being a `Stacks.WeaklyContractible.SliceTestingFamily` at that
universe. On a small site a covering collection of weakly contractible objects is such a family
by `Stacks.WeaklyContractible.SliceTestingFamily.ofIsWeaklyContractible`; the small pro-étale
site of a scheme, which is not essentially small, carries one in every universe.

The proofs are those of the small case: both sides are tested on sections over a member of the
family, where evaluation is exact and the sections of `IⁿF` are the usual products of sections
of `Iⁿ` with sections of `F`, because a locally surjective map is surjective on sections there.

## Main results

* `RingedSite.isDerivedComplete_sheaf_single_iff_sections_of_sliceTestingFamily`: a sheaf of
  modules is derived complete exactly when its modules of sections over the members of the family
  are.
* `RingedSite.isLimit_adicQuotientSystem_iff_of_sliceTestingFamily`: the cone of adic quotient
  maps is a limit cone exactly when the sheaf is derived complete.
* `RingedSite.isZero_of_isDerivedComplete_of_idealProduct_eq_top_of_sliceTestingFamily`:
  derived Nakayama — a derived complete sheaf of modules with `IF = F` is zero.

## Implementation notes

The helpers of `AdicCompletionCriterion` that do not depend on the universe are used from there
(`import all`); those stated over sheaves in the universe `max u v` are restated here in the
universe `max u v w`, under the suffix `OfSize`/`_ofSize`, and those taking the testing family
under the suffix `_of_sliceTestingFamily`.

The limit statement quantifies over an `AlgebraicGeometry.RingedSite.AdicQuotientSystemOfSize`, so
it says the same thing about every presentation of `F/IⁿF`. Vanishing of `F/IF` is expressed as
the equality `IF = F` of subsheaves of `F`. Finite generation of the sheaf of ideals is asked for
only on sections over the members of the family, which is where it is used.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
* [Stacks Project, Tag 09BY](https://stacks.math.columbia.edu/tag/09BY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSite Opposite
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace AlgebraicGeometry.RingedSite

/-- The underlying type-valued presheaf of a sheaf of abelian groups is a sheaf of types. -/
private lemma isSheaf_forget_obj_ofSize
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{max u v w}) :
    Presieve.IsSheaf J (F.obj ⋙ CategoryTheory.forget AddCommGrpCat) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf _ F.property

private def submoduleSheafifyOfSize
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v w}} {F : SheafOfModules.{max u v w} R}
    (N : F.val.Submodule) : F.Submodule where
  toSubmodule :=
    { obj U :=
        { carrier := (N.toSubfunctor.sheafify J).obj U
          zero_mem' := N.toSubfunctor.le_sheafify J U ((N.obj U).zero_mem)
          add_mem' := by
            intro x y hx hy
            refine J.superset_covering (fun V f hf => ?_) (J.intersection_covering hx hy)
            change F.val.map f.op (x + y) ∈ N.obj (op V)
            rw [map_add]
            exact (N.obj (op V)).add_mem hf.1 hf.2
          smul_mem' := by
            intro a x hx
            refine J.superset_covering (fun V f hf => ?_) hx
            change F.val.map f.op (a • x) ∈ N.obj (op V)
            rw [F.val.map_smul]
            exact (N.obj (op V)).smul_mem _ hf }
      map f := (N.toSubfunctor.sheafify J).map f }
  isSheaf := by
    intro U x hx
    change x ∈ ((N.toSubfunctor.sheafify J).sheafify J).obj U at hx
    rwa [N.toSubfunctor.sheafify_sheafify (isSheaf_forget_obj_ofSize ⟨F.val.presheaf, F.isSheaf⟩)]
      at hx

private lemma le_submoduleSheafify_ofSize
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v w}} {F : SheafOfModules.{max u v w} R}
    (N : F.val.Submodule) : N ≤ (submoduleSheafifyOfSize N).toSubmodule :=
  fun U _ hx => N.toSubfunctor.le_sheafify J U hx

private lemma submoduleSheafify_le_iff_ofSize
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v w}} {F : SheafOfModules.{max u v w} R}
    (N : F.val.Submodule) (P : F.Submodule) :
    submoduleSheafifyOfSize N ≤ P ↔ N ≤ P.toSubmodule := by
  refine ⟨fun h => (le_submoduleSheafify_ofSize N).trans h, fun h U x hx => ?_⟩
  change N.toSubfunctor.sieveOfSection x ∈ J U.unop at hx
  exact P.isSheaf x (J.superset_covering (fun V f hf => h (op V) hf) hx)

private def idealPowerActionPresheafOfSize
    (X : RingedSite.{u, v, max u v w})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    F.val.Submodule where
  obj U :=
    letI : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := by
      change IsMulCommutative (X.O.obj.obj U)
      infer_instance
    letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (F.val.obj U) :=
      (F.val.obj U).isModule
    let J : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := I.toSubmodule.obj U
    J ^ n • ⊤
  map {U V} f := by
    let : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := by
      change IsMulCommutative (X.O.obj.obj U)
      infer_instance
    let : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) := by
      change IsMulCommutative (X.O.obj.obj V)
      infer_instance
    let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (F.val.obj U) :=
      (F.val.obj U).isModule
    let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) (F.val.obj V) :=
      (F.val.obj V).isModule
    let φ := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom
    let JU : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := I.toSubmodule.obj U
    let JV : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) := I.toSubmodule.obj V
    have hI : Ideal.map φ JU ≤ JV := Ideal.map_le_iff_le_comap.mpr (I.toSubmodule.map f)
    have hn : Ideal.map φ (JU ^ n) ≤ JV ^ n :=
      (Ideal.map_pow φ JU n).trans_le (pow_le_pow_left' hI n)
    intro x hx
    change x ∈ JU ^ n • (⊤ : Submodule _ _) at hx
    change F.val.restrictₛₗ f x ∈ JV ^ n •
      (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) (F.val.obj V))
    refine Submodule.smul_induction_on hx (fun a ha m _ => ?_) fun x y hx hy => ?_
    · rw [(F.val.restrictₛₗ f).map_smulₛₗ]
      exact Submodule.smul_mem_smul (Ideal.map_le_iff_le_comap.mp hn ha) trivial
    · change F.val.map f (x + y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ hx hy

private lemma idealPowerProduct_eq_sheafify_ofSize
    (X : RingedSite.{u, v, max u v w})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    idealPowerProductOfSize X I F n =
      submoduleSheafifyOfSize (idealPowerActionPresheafOfSize X I F n) := by
  apply le_antisymm
  · apply sInf_le
    intro U
    dsimp only
    intro a ha m
    let : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := by
      change IsMulCommutative (X.O.obj.obj U)
      infer_instance
    let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (F.val.obj U) :=
      (F.val.obj U).isModule
    apply le_submoduleSheafify_ofSize (idealPowerActionPresheafOfSize X I F n) U
    let J : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := I.toSubmodule.obj U
    change a • m ∈ J ^ n •
      (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (F.val.obj U))
    exact Submodule.smul_mem_smul (show a ∈ J ^ n from ha) Submodule.mem_top
  · refine le_sInf fun N hN => ?_
    rw [submoduleSheafify_le_iff_ofSize]
    intro U
    let : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := by
      change IsMulCommutative (X.O.obj.obj U)
      infer_instance
    let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (F.val.obj U) :=
      (F.val.obj U).isModule
    let J : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := I.toSubmodule.obj U
    change J ^ n •
      (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (F.val.obj U)) ≤ _
    exact Submodule.smul_le.mpr fun a ha m _ => hN U a ha m

private lemma exists_locallyFiniteSum_ofSize
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{max u v w}) (U : C)
    (S : Sieve U) (hS : S ∈ J U)
    (b : ∀ (W : C) (f : W ⟶ U), S f → ℕ)
    (x : ℕ → F.obj.obj (op U))
    (hx : ∀ (W : C) (f : W ⟶ U) (hf : S f) (i : ℕ), b W f hf ≤ i →
      F.obj.map f.op (x i) = 0) :
    ∃ y : F.obj.obj (op U), ∀ (W : C) (f : W ⟶ U) (hf : S f),
      F.obj.map f.op y = ∑ i ∈ Finset.range (b W f hf), F.obj.map f.op (x i) := by
  let P := F.obj ⋙ CategoryTheory.forget AddCommGrpCat
  have hF : Presieve.IsSheaf J P := isSheaf_forget_obj_ofSize F
  let t : Presieve.FamilyOfElements P S.arrows := fun W f hf =>
    ∑ i ∈ Finset.range (b W f hf), F.obj.map f.op (x i)
  have ht : t.Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ heq
    change F.obj.map g₁.op (∑ i ∈ Finset.range (b W₁ f₁ hf₁), F.obj.map f₁.op (x i)) =
      F.obj.map g₂.op (∑ i ∈ Finset.range (b W₂ f₂ hf₂), F.obj.map f₂.op (x i))
    simp only [map_sum, ← Functor.map_comp_apply, ← op_comp, heq]
    refine sum_range_eq_of_eventually_zero _ (fun i hi => ?_) fun i hi => ?_
    · rw [← heq, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hx W₁ f₁ hf₁ i hi,
        map_zero]
    · rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hx W₂ f₂ hf₂ i hi, map_zero]
  exact ⟨(hF S hS).amalgamate t ht, fun W f hf => (hF S hS).valid_glue ht f hf⟩

private abbrev moduleSectionsSheafOfSize
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v w}} (F : SheafOfModules.{max u v w} R) :
    Sheaf J (Type (max u v w)) :=
  (sheafCompose J (CategoryTheory.forget AddCommGrpCat)).obj ⟨F.val.presheaf, F.isSheaf⟩

/-- **Derived completeness of a sheaf of modules is tested on sections.** A sheaf of modules,
placed in degree zero, is derived complete along a sheaf of ideals `I` exactly when its module
of sections over every member `U` of a testing family of weakly contractible objects is derived
complete along the ideal of sections of `I` over `U`. -/
theorem isDerivedComplete_sheaf_single_iff_sections_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F) ↔
      ∀ U : X.C, B.B U →
        let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
        letI : IsMulCommutative R := by
          change IsMulCommutative (X.O.obj.obj (op U))
          infer_instance
        letI : CommRing R := inferInstance
        let J : Ideal R := by
          change Submodule R R
          exact I.toSubmodule.obj (op U)
        let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
        letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v w} R)) :=
          Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
        IsDerivedCompleteModule J (G.obj F) := by
  rw [AlgebraicGeometry.RingedSite.isDerivedComplete_iff_derivedSections_of_sliceTestingFamily X B I
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F)]
  refine ⟨fun h U hU => ?_, fun h U hU => ?_⟩
  all_goals
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    let : IsMulCommutative R := by
      change IsMulCommutative (X.O.obj.obj (op U))
      infer_instance
    let : CommRing R := inferInstance
    let J : Ideal R := by
      change Submodule R R
      exact I.toSubmodule.obj (op U)
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
  · obtain ⟨hAdd, hLim, hColim, hProd, hComplete⟩ := h U hU
    let : G.Additive := hAdd
    let : PreservesFiniteLimits G := hLim
    let : PreservesFiniteColimits G := hColim
    let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v w} R)) := hProd
    change ∀ f ∈ J, IsDerivedCompleteAt
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj
        (G.obj F)) f
    intro f hf
    rw [isDerivedCompleteAt_iff_isIso]
    exact (isIso_oneSubSmulShift_congr
      ((G.mapDerivedCategorySingleFunctor 0).app F) f).mp (hComplete f hf)
  · let : HasProductsOfShape ℕ (ModuleCat.{max u v w} R) := inferInstance
    let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v w} R) :=
      moduleCat_hasExactLimitsOfShape_discrete.{max u v w} R ℕ
    let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v w} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let : G.Additive := ⟨fun {_ _} _ _ => rfl⟩
    let : G.PreservesZeroMorphisms := inferInstance
    let : G.PreservesHomology := Functor.preservesHomology_of_map_exact G
      fun S hS => evaluation_map_exact_of_sliceTestingFamily X B U hU S hS
    let : ∀ {A B : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
        (f : A ⟶ B),
        PreservesColimit (parallelPair f 0) G := fun f =>
      Functor.PreservesHomology.preservesCokernel G f
    let : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesCokernels G
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun f hf => ?_⟩
    change IsDerivedCompleteAt ((G.mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F)) f
    rw [isDerivedCompleteAt_iff_isIso]
    have hsingle : IsDerivedCompleteAt
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj (G.obj F)) f :=
      h U hU f hf
    rw [isDerivedCompleteAt_iff_isIso] at hsingle
    exact (isIso_oneSubSmulShift_congr
      ((G.mapDerivedCategorySingleFunctor 0).app F) f).mpr hsingle

private theorem evaluation_jointly_reflects_iso_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    {F G : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : F ⟶ G)
    (hf : ∀ U : X.C, B.B U →
      Function.Bijective
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).map f)) :
    IsIso f := by
  let S₁ : ShortComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    ShortComplex.mk (0 : F ⟶ F) f (by simp)
  have hS₁ : S₁.Exact := by
    refine (Stacks.WeaklyContractible.SliceTestingFamily.exact_iff_exact_sections X.J B
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) S₁).2 fun {U} hU => ?_
    change ∀ x, (f.val.app (op U)) x = 0 ↔
      x ∈ Set.range (fun _ : F.val.obj (op U) => (0 : F.val.obj (op U)))
    refine fun x => ⟨fun hx => ⟨0, ((hf U hU).1 (a₁ := x) (a₂ := 0) ?_).symm⟩, ?_⟩
    · change f.val.app (op U) x = f.val.app (op U) 0
      rw [hx, map_zero]
    · rintro ⟨y, rfl⟩
      simp
  have hmono : Mono f := (ShortComplex.exact_iff_mono S₁ (by rfl)).mp hS₁
  let S₂ : ShortComplex (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    ShortComplex.mk f (0 : G ⟶ G) (by simp)
  have hS₂ : S₂.Exact := by
    refine (Stacks.WeaklyContractible.SliceTestingFamily.exact_iff_exact_sections X.J B
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) S₂).2 fun {U} hU => ?_
    change ∀ y, (0 : G.val.obj (op U)) = 0 ↔
      y ∈ Set.range (f.val.app (op U))
    exact fun y => ⟨fun _ => (hf U hU).2 y, fun _ => rfl⟩
  have hepi : Epi f := (ShortComplex.exact_iff_epi S₂ (by rfl)).mp hS₂
  exact isIso_of_mono_of_epi f

private theorem evaluation_jointly_reflects_limit_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (D : ℕᵒᵖ ⥤ SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (c : Cone D) :
    Nonempty (IsLimit c) ↔ ∀ U : X.C, B.B U →
      Nonempty (IsLimit ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).mapCone c)) := by
  refine ⟨fun ⟨hc⟩ U hU => ⟨isLimitOfPreserves _ hc⟩, fun h => ?_⟩
  let f := (limit.isLimit D).liftConeMorphism c
  have hf : IsIso f.hom := by
    refine evaluation_jointly_reflects_iso_of_sliceTestingFamily X B f.hom fun U hU => ?_
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    obtain ⟨hc⟩ := h U hU
    let m : G.mapCone c ⟶ G.mapCone (limit.cone D) := G.mapConeMorphism f
    have : IsIso m := hc.hom_isIso (isLimitOfPreserves G (limit.isLimit D)) m
    have : IsIso m.hom := (Cone.forget _).map_isIso m
    exact (ConcreteCategory.isIso_iff_bijective m.hom).mp inferInstance
  have : IsIso f := Cone.cone_iso_of_hom_iso f
  exact ⟨(limit.isLimit D).ofIsoLimit (asIso f).symm⟩

private lemma exists_sections_refinement_ofSize
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [J.WEqualsLocallyBijective (Type (max u v w))]
    (U : C) (hU : ∀ {F G : Sheaf J (Type (max u v w))} (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U)))
    {ι : Type (max u v w)} (V : ι → C) (f : ∀ i, V i ⟶ U)
    (hcov : Sieve.ofArrows V f ∈ J U)
    {κ : Type*} (F : κ → Sheaf J (Type (max u v w)))
    (x : ∀ k i, (F k).obj.obj (op (V i))) :
    ∃ y : ∀ k, (F k).obj.obj (op U), ∃ S : Sieve U,
      S ∈ J U ∧ ∀ (W : C) (g : W ⟶ U), S g →
        ∃ i, ∃ a : W ⟶ V i, a ≫ f i = g ∧
          ∀ k, (F k).obj.map g.op (y k) = (F k).obj.map a.op (x k i) := by
  classical
  let P : Cᵒᵖ ⥤ Type (max u v w) :=
    { obj W := Σ i, W.unop ⟶ V i
      map g := ↾fun t => ⟨t.1, g.unop ≫ t.2⟩
      map_id W := by
        apply ConcreteCategory.hom_ext (CC := fun X => X)
        intro t
        change (⟨t.1, 𝟙 _ ≫ t.2⟩ : Σ i, W.unop ⟶ V i) = t
        simp
      map_comp g h := by
        apply ConcreteCategory.hom_ext (CC := fun X => X)
        intro t
        change (⟨t.1, (h.unop ≫ g.unop) ≫ t.2⟩ : Σ i, _ ⟶ V i) =
          ⟨t.1, h.unop ≫ (g.unop ≫ t.2)⟩
        rw [Category.assoc] }
  let Y : Cᵒᵖ ⥤ Type (max u v w) := yoneda.obj U ⋙ uliftFunctor.{max u w}
  let π : P ⟶ Y :=
    { app W := ↾fun t => ULift.up (t.2 ≫ f t.1)
      naturality W Z g := by ext t; exact congrArg ULift.up (Category.assoc _ _ _) }
  have : Presheaf.IsLocallySurjective J π := ⟨fun {W} g => by
    refine J.superset_covering (fun Z a ha => ?_) (J.pullback_stable g.down hcov)
    obtain ⟨i, b, hb⟩ := (Sieve.mem_ofArrows_iff V f (a ≫ g.down)).mp ha
    exact ⟨⟨i, b⟩, congrArg ULift.up hb.symm⟩⟩
  let η := toSheafify J P
  let ε := toSheafify J Y
  let π' := (presheafToSheaf J (Type (max u v w))).map π
  have hπ' : Sheaf.IsLocallySurjective π' := by
    change Presheaf.IsLocallySurjective J (sheafifyMap J π)
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (toSheafify_naturality J π).symm
  obtain ⟨s, hs⟩ := hU π' hπ' (ε.app (op U) (ULift.up (𝟙 U)))
  change (sheafifyMap J π).app (op U) s = ε.app (op U) (ULift.up (𝟙 U)) at hs
  let α (k : κ) : P ⟶ (F k).obj :=
    { app W := ↾fun t => (F k).obj.map t.2.op (x k t.1)
      naturality W Z g := by
        apply ConcreteCategory.hom_ext
        intro t
        change (F k).obj.map (g.unop ≫ t.2).op (x k t.1) =
          (F k).obj.map g ((F k).obj.map t.2.op (x k t.1))
        simp only [op_comp, Functor.map_comp, types_comp_apply, Quiver.Hom.op_unop] }
  let β (k : κ) := sheafifyLift J (α k) (F k).property
  have hβ (k : κ) : η ≫ β k = α k := toSheafify_sheafifyLift J (α k) (F k).property
  let y (k : κ) := (β k).app (op U) s
  let S : Sieve U :=
    { arrows W g := ∃ t : P.obj (op W), π.app _ t = ULift.up g ∧
        η.app _ t = (sheafify J P).map g.op s
      downward_closed := by
        rintro W Z g ⟨t, ht, hs⟩ a
        refine ⟨P.map a.op t, ?_, ?_⟩
        · exact (π.naturality_apply a.op t).trans (congrArg (fun z => ULift.up (a ≫ z.down)) ht)
        · rw [η.naturality_apply, hs, ← Functor.map_comp_apply, ← op_comp] }
  have hS : S ∈ J U := by
    refine J.transitive (Presheaf.imageSieve_mem J η s) _ fun W g hg => ?_
    obtain ⟨t, ht⟩ := hg
    have heq : ε.app (op W) (π.app _ t) = ε.app (op W) (ULift.up g) := by
      calc
        _ = (sheafifyMap J π).app (op W) (η.app (op W) t) :=
          (congrArg (fun q : P ⟶ sheafify J Y => q.app (op W) t)
            (toSheafify_naturality J π))
        _ = (sheafify J Y).map g.op ((sheafifyMap J π).app (op U) s) := by
          rw [ht, NatTrans.naturality_apply]
        _ = (sheafify J Y).map g.op (ε.app (op U) (ULift.up (𝟙 U))) := by rw [hs]
        _ = ε.app (op W) (ULift.up g) := by
          refine (NatTrans.naturality_apply ε g.op
            (show Y.obj (op U) from ULift.up (𝟙 U))).symm.trans ?_
          change ε.app (op W) (ULift.up (g ≫ 𝟙 U)) = _
          rw [Category.comp_id]
    refine J.superset_covering (fun Z a ha => ⟨P.map a.op t, ?_, ?_⟩)
      (Presheaf.equalizerSieve_mem J ε (π.app _ t) (show Y.obj (op W) from ULift.up g) heq)
    · exact (π.naturality_apply a.op t).trans ha
    · rw [η.naturality_apply, ht, ← Functor.map_comp_apply, ← op_comp]
  refine ⟨y, S, hS, ?_⟩
  rintro W g ⟨⟨i, a⟩, ht, hs'⟩
  refine ⟨i, a, congrArg ULift.down ht, fun k => ?_⟩
  have hh := congrArg (fun q => q.app (op W) (⟨i, a⟩ : P.obj (op W))) (hβ k)
  change (β k).app (op W) (η.app (op W) ⟨i, a⟩) =
    (F k).obj.map a.op (x k i) at hh
  rw [hs'] at hh
  exact (ConcreteCategory.congr_hom (C := Type (max u v w)) (CC := fun X => X)
    ((β k).naturality g.op) s).symm.trans hh

private lemma idealPowerProduct_obj_of_weaklyContractible_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    {B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J}
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (hU : B.B U)
    (hI : (I.toSubmodule.obj (op U)).FG) (n : ℕ) :
    (idealPowerProductOfSize X I F n).toSubmodule.obj (op U) =
      (idealPowerActionPresheafOfSize X I F n).obj (op U) := by
  classical
  let (W : X.Cᵒᵖ) : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj W) := by
    change IsMulCommutative (X.O.obj.obj W); infer_instance
  let (W : X.Cᵒᵖ) : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj W)
      (F.val.obj W) := (F.val.obj W).isModule
  rw [idealPowerProduct_eq_sheafify_ofSize]
  refine le_antisymm (fun x hx => ?_) (le_submoduleSheafify_ofSize _ (op U))
  change (idealPowerActionPresheafOfSize X I F n).toSubfunctor.sieveOfSection x ∈ X.J U at hx
  let ι := ULift.{w} (Σ W : X.C,
    {g : W ⟶ U // (idealPowerActionPresheafOfSize X I F n).toSubfunctor.sieveOfSection x g})
  let V : ι → X.C := fun i => i.down.1
  let f : ∀ i, V i ⟶ U := fun i => i.down.2.1
  have hcov : Sieve.ofArrows V f ∈ X.J U :=
    X.J.superset_covering (fun W g hg => Sieve.ofArrows_mk V f (ULift.up ⟨W, g, hg⟩)) hx
  have hex (i : ι) : ∃ l : PowerExpression
      (I.toSubmodule.obj (op (V i)) :
        Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op (V i))))
      (F.val.obj (op (V i))) n,
      powerExpressionValue l = F.val.restrictₛₗ (f i).op x :=
    (mem_pow_smul_iff_expression _ n _).mp i.down.2.2
  choose l hl using hex
  let z (i : ι) : (Fin n → (I.toSubmodule.obj (op (V i)) :
      Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op (V i))))) ×
        F.val.obj (op (V i)) := (fun _ => 0, 0)
  let a (i : ι) (j : ℕ) (k : Fin n) := (l i |>.getD j (z i)).1 k
  let m (i : ι) (j : ℕ) := (l i |>.getD j (z i)).2
  let T : ((ℕ × Fin n) ⊕ ℕ) → Sheaf X.J (Type (max u v w)) :=
    Sum.elim (fun _ => moduleSectionsSheafOfSize I.toSheafOfModules)
      (fun _ => moduleSectionsSheafOfSize F)
  let s : ∀ k i, (T k).obj.obj (op (V i)) := fun k i =>
    match k with
    | .inl jk => a i jk.1 jk.2
    | .inr j => m i j
  obtain ⟨y, S, hS, href⟩ := exists_sections_refinement_ofSize.{u, v, w} X.J U
    (fun φ hφ => B.surjective_app hU φ hφ) V f hcov T s
  choose d g hg hy using href
  let A (j : ℕ) (k : Fin n) :
      (I.toSubmodule.obj (op U) :
        Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) := y (.inl (j, k))
  let M (j : ℕ) : F.val.obj (op U) := y (.inr j)
  let b (W : X.C) (q : W ⟶ U) (hq : S q) := (l (d W q hq)).length
  have hA (W : X.C) (q : W ⟶ U) (hq : S q) (j : ℕ) (k : Fin n) :
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map q.op).hom (A j k).val =
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (g W q hq).op).hom
          (a (d W q hq) j k) :=
    congrArg Subtype.val (hy W q hq (.inl (j, k)))
  have hM (W : X.C) (q : W ⟶ U) (hq : S q) (j : ℕ) :
      F.val.restrictₛₗ q.op (M j) =
        F.val.restrictₛₗ (g W q hq).op (m (d W q hq) j) :=
    hy W q hq (.inr j)
  have hzero (W : X.C) (q : W ⟶ U) (hq : S q) (j : ℕ) (hj : b W q hq ≤ j) :
      F.val.restrictₛₗ q.op (M j) = 0 := by
    rw [hM W q hq j]
    have hm : m (d W q hq) j = 0 := by
      simpa only [m, z] using congrArg Prod.snd
        (List.getD_eq_default (l (d W q hq)) (z (d W q hq)) hj)
    rw [hm, map_zero]
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
  let J : Ideal R := I.toSubmodule.obj (op U)
  let c (j : ℕ) : R := ∏ k, (show R from (A j k).val)
  have hc (j : ℕ) : c j ∈ J ^ n := by
    have hh := Ideal.prod_mem_prod (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
      (A j k).property)
    have hpow : (∏ _ : Fin n, J) = J ^ n := by
      let : CommRing R := by change CommRing (X.O.obj.obj (op U)); infer_instance
      simp only [Finset.prod_const, Finset.card_fin]
    exact hpow ▸ hh
  obtain ⟨r, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.FG.pow (n := n) (show J.FG from hI))
  have hcoeff (j : ℕ) : ∃ e : Fin r → R, ∑ k, e k • z k = c j :=
    (Submodule.mem_span_range_iff_exists_fun R).mp (hz ▸ hc j)
  choose e he using hcoeff
  have hlocal (W : X.C) (q : W ⟶ U) (hq : S q) :
      F.val.restrictₛₗ q.op x = ∑ j ∈ Finset.range (b W q hq),
        F.val.restrictₛₗ q.op (c j • M j) := by
    conv_lhs => rw [← hg W q hq]
    change F.val.presheaf.map (g W q hq ≫ f (d W q hq)).op x = _
    rw [op_comp, Functor.map_comp]
    change F.val.restrictₛₗ (g W q hq).op (F.val.restrictₛₗ (f (d W q hq)).op x) = _
    rw [← hl (d W q hq), powerExpressionValue_eq_sum_range (l (d W q hq)), map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change F.val.restrictₛₗ (g W q hq).op
        ((∏ k, (a (d W q hq) j k).val) • m (d W q hq) j) =
      F.val.restrictₛₗ q.op (c j • M j)
    rw [(F.val.restrictₛₗ (g W q hq).op).map_smulₛₗ, (F.val.restrictₛₗ q.op).map_smulₛₗ]
    dsimp only [c]
    simp only [map_prod, hM W q hq j]
    congr 1
    change (∏ k, ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (g W q hq).op).hom
        (a (d W q hq) j k).val) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map q.op).hom
        (∏ k, (show R from (A j k).val))
    let : CommMonoid R := inferInstance
    rw [map_prod ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map q.op).hom
      (fun k => (show R from (A j k).val)) Finset.univ]
    exact Finset.prod_congr rfl (fun k _ => (hA W q hq j k).symm)
  let F' : Sheaf X.J AddCommGrpCat.{max u v w} := ⟨F.val.presheaf, F.isSheaf⟩
  have hsum (k : Fin r) : ∃ t : F.val.obj (op U), ∀ (W : X.C) (q : W ⟶ U) (hq : S q),
      F.val.restrictₛₗ q.op t = ∑ j ∈ Finset.range (b W q hq),
        F.val.restrictₛₗ q.op (e j k • M j) := by
    refine exists_locallyFiniteSum_ofSize F' U S hS b (fun j => e j k • M j)
      fun W q hq j hj => ?_
    change F.val.restrictₛₗ q.op (e j k • M j) = 0
    rw [(F.val.restrictₛₗ q.op).map_smulₛₗ, hzero W q hq j hj, smul_zero]
  choose t ht using hsum
  have hxsum : x = ∑ k, z k • t k := by
    apply (isSheaf_forget_obj_ofSize F' S hS).isSeparatedFor.ext
    intro W q hq
    change F.val.restrictₛₗ q.op x = F.val.restrictₛₗ q.op (∑ k, z k • t k)
    have htk (k : Fin r) : F.val.restrictₛₗ q.op (z k • t k) =
        ∑ j ∈ Finset.range (b W q hq), F.val.restrictₛₗ q.op (z k • (e j k • M j)) := by
      rw [(F.val.restrictₛₗ q.op).map_smulₛₗ, ht k W q hq, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ =>
        ((F.val.restrictₛₗ q.op).map_smulₛₗ (z k) (e j k • M j)).symm
    rw [hlocal W q hq, map_sum]
    simp_rw [htk]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_sum]
    apply congrArg (F.val.restrictₛₗ q.op)
    rw [← he j, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (e j k * z k) • M j = z k • (e j k • M j)
    rw [mul_smul, smul_comm]
  change x ∈ J ^ n • (⊤ : Submodule R (F.val.obj (op U)))
  rw [hxsum, ← hz]
  exact sum_mem fun k _ =>
    Submodule.smul_mem_smul (Submodule.subset_span (Set.mem_range_self k)) Submodule.mem_top

private lemma idealPowerProduct_obj_eq_pow_smul_top_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    {B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J}
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (hU : B.B U)
    (hI : (I.toSubmodule.obj (op U)).FG) (n : ℕ) :
    letI : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) := by
      change IsMulCommutative (X.O.obj.obj (op U))
      infer_instance
    letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
        (F.val.obj (op U)) :=
      (F.val.obj (op U)).isModule
    (idealPowerProductOfSize X I F n).toSubmodule.obj (op U) =
      idealSectionsOfSize X I (op U) ^ n •
        (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
          (F.val.obj (op U))) :=
  idealPowerProduct_obj_of_weaklyContractible_of_sliceTestingFamily X I F U hU hI n

private lemma sheafSubmodule_eq_bot_iff_weaklyContractible_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    {F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (N : F.Submodule) :
    N = ⊥ ↔ ∀ U : X.C, B.B U →
      N.toSubmodule.obj (op U) = ⊥ := by
  refine ⟨fun h U _ => h ▸ sheafSubmodule_bot_obj F (op U), ?_⟩
  intro h
  apply (sheafSubmodule_eq_bot_iff N).mpr
  intro U
  apply le_bot_iff.mp
  intro x hx
  change x = 0
  obtain ⟨ι, V, f, hcov, hV⟩ := B.hasEnoughObjects U.unop
  apply (isSheaf_forget_obj_ofSize (J := X.J) ⟨F.val.presheaf, F.isSheaf⟩ _ hcov).isSeparatedFor.ext
  intro W g hg
  rw [Sieve.mem_ofArrows_iff] at hg
  obtain ⟨i, a, rfl⟩ := hg
  have hz : F.val.map (f i).op x = 0 := by
    have hm := N.toSubmodule.map (f i).op hx
    rwa [h _ (hV i)] at hm
  change (F.val.presheaf.map (a ≫ f i).op) x = (F.val.presheaf.map (a ≫ f i).op) 0
  simp only [op_comp, Functor.map_comp, map_zero]
  exact congrArg (fun z => F.val.presheaf.map a.op z) hz |>.trans (map_zero _)

private lemma evaluation_cokernel_submodule_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (U : X.C) (hU : B.B U)
    (F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (N : F.Submodule) :
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    ∃ e : ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
        (G.obj F ⧸ N.toSubmodule.obj (op U)) ≅ G.obj (cokernel N.ι),
      ModuleCat.ofHom (N.toSubmodule.obj (op U)).mkQ ≫ e.hom =
        G.map (cokernel.π N.ι) := by
  let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
  let : PreservesFiniteColimits G := evaluation_preservesFiniteColimits_of_sliceTestingFamily
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) B U hU
  let q := ((cokernel.π N.ι).val.app (op U)).hom
  have hsurj : Function.Surjective q :=
    (ModuleCat.epi_iff_surjective (G.map (cokernel.π N.ι))).mp inferInstance
  have hker : q.ker = N.toSubmodule.obj (op U) := by
    have he := (Stacks.WeaklyContractible.SliceTestingFamily.exact_iff_exact_sections X.J B
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (ShortComplex.cokernelSequence N.ι)).mp (ShortComplex.cokernelSequence_exact N.ι) hU
    ext x
    change q x = 0 ↔ x ∈ N.toSubmodule.obj (op U)
    have he' : q x = 0 ↔ ∃ y : N.toSubmodule.obj (op U), (y : F.val.obj (op U)) = x := he x
    exact he'.trans ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  let e := ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    (q.quotKerEquivOfSurjective hsurj)).toModuleIso
  refine ⟨e, ?_⟩
  ext x
  exact q.quotKerEquivOfSurjective_apply_mk hsurj x

private lemma evaluation_adicQuotientCone_isLimit_iff_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (hU : B.B U)
    (hpow : ∀ n, (idealPowerProductOfSize X I F n).toSubmodule.obj (op U) =
      (idealPowerActionPresheafOfSize X I F n).obj (op U)) :
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    letI : IsMulCommutative R := by
      change IsMulCommutative (X.O.obj.obj (op U)); infer_instance
    let J : Ideal R := I.toSubmodule.obj (op U)
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    Nonempty (IsLimit (G.mapCone
      (Cone.mk F (adicQuotientSystemOfSize X I F).quotientMap))) ↔ IsAdicComplete J (G.obj F) := by
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
  let : IsMulCommutative R := by
    change IsMulCommutative (X.O.obj.obj (op U)); infer_instance
  let J : Ideal R := I.toSubmodule.obj (op U)
  let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
  let M := G.obj F
  let D := (adicQuotientSystemOfSize X I F).Q ⋙ G
  have he (n : ℕ) : ∃ e : (moduleAdicQuotientSystem J M).obj (op n) ≅ D.obj (op n),
      (moduleAdicQuotientCone J M).π.app (op n) ≫ e.hom =
        G.map ((adicQuotientSystemOfSize X I F).quotientMap.app (op n)) := by
    have hex := evaluation_cokernel_submodule_of_sliceTestingFamily X B U hU F
      (idealPowerProductOfSize X I F n)
    have hn := hpow n
    change (idealPowerProductOfSize X I F n).toSubmodule.obj (op U) =
      J ^ n • (⊤ : Submodule R M) at hn
    dsimp only at hex
    rwa [hn] at hex
  choose e he using he
  let eD : moduleAdicQuotientSystem J M ≅ D := NatIso.ofComponents (fun n => e n.unop) (by
    intro n m f
    have : Epi ((moduleAdicQuotientCone J M).π.app n) :=
      (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
    apply (cancel_epi ((moduleAdicQuotientCone J M).π.app n)).1
    rw [← Category.assoc, (moduleAdicQuotientCone J M).w f, he, ← Category.assoc, he]
    exact (G.congr_map ((Cone.mk F (adicQuotientSystemOfSize X I F).quotientMap).w f)).symm)
  have ec : (Cone.postcompose eD.hom).obj (moduleAdicQuotientCone J M) ≅
      G.mapCone (Cone.mk F (adicQuotientSystemOfSize X I F).quotientMap) :=
    Cone.ext (Iso.refl M) (by
      intro n
      change (moduleAdicQuotientCone J M).π.app n ≫ (e n.unop).hom =
        𝟙 M ≫ G.map ((adicQuotientSystemOfSize X I F).quotientMap.app n)
      simpa only [Category.id_comp] using he n.unop)
  refine ⟨fun ⟨hc⟩ => (moduleAdicQuotientCone_isLimit_iff J M).mp
    ⟨IsLimit.postcomposeHomEquiv eD _ (hc.ofIsoLimit ec.symm)⟩, fun h => ?_⟩
  obtain ⟨hm⟩ := (moduleAdicQuotientCone_isLimit_iff J M).mpr h
  exact ⟨((IsLimit.postcomposeHomEquiv eD _).symm hm).ofIsoLimit ec⟩

/-- Ordinary completeness is derived completeness plus separatedness. -/
@[stacks 099Q "completion_criterion"]
theorem isLimit_adicQuotientSystem_iff_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hI : ∀ U : X.C, B.B U →
      (I.toSubmodule.obj (op U)).FG)
    (F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Nonempty (IsLimit (Cone.mk F (adicQuotientSystemOfSize X I F).quotientMap)) ↔
      AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F) ∧
        (⨅ n : ℕ, idealPowerProductOfSize X I F n) = ⊥ := by
  let (W : X.Cᵒᵖ) : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj W) := by
    change IsMulCommutative (X.O.obj.obj W)
    infer_instance
  let (W : X.Cᵒᵖ) : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj W)
      (F.val.obj W) := (F.val.obj W).isModule
  let (U : X.C) : HasProductsOfShape ℕ
      (DerivedCategory (ModuleCat.{max u v w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let J (U : X.C) : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) :=
    I.toSubmodule.obj (op U)
  have hp (U : X.C) (hU : B.B U) (n : ℕ) :=
    idealPowerProduct_obj_of_weaklyContractible_of_sliceTestingFamily X I F U hU (hI U hU) n
  have hi : (⨅ n : ℕ, idealPowerProductOfSize X I F n) = ⊥ ↔
      ∀ U : X.C, B.B U →
        (⨅ n : ℕ, J U ^ n •
          (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
            (F.val.obj (op U)))) = ⊥ := by
    rw [sheafSubmodule_eq_bot_iff_weaklyContractible_of_sliceTestingFamily X B]
    refine forall_congr' fun U => imp_congr_right fun hU => ?_
    rw [sheafSubmodule_iInf_obj]
    simp_rw [hp U hU]
    rfl
  rw [isDerivedComplete_sheaf_single_iff_sections_of_sliceTestingFamily X B I F, hi,
    evaluation_jointly_reflects_limit_of_sliceTestingFamily X B]
  have hm (U : X.C) (hU : B.B U) :=
    evaluation_adicQuotientCone_isLimit_iff_of_sliceTestingFamily X B I F U hU (hp U hU)
  have hc (U : X.C) (hU : B.B U) :=
    isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (J U) (hI U hU)
      (F.val.obj (op U))
  exact ⟨fun h => ⟨fun U hU => ((hc U hU).mp ((hm U hU).mp (h U hU))).1,
      fun U hU => ((hc U hU).mp ((hm U hU).mp (h U hU))).2⟩,
    fun ⟨hd, hs⟩ U hU => (hm U hU).mpr ((hc U hU).mpr ⟨hd U hU, hs U hU⟩)⟩

/-- **Stacks 09BY.** A sheaf of modules on a ringed site with enough weakly contractible
objects which is derived complete along a sheaf of ideals and satisfies `IF = F`, that is
whose adic quotient `F/IF` vanishes, is zero. The sheaf of ideals is assumed finitely
generated on sections over the weakly contractible objects. -/
@[stacks 09BY]
theorem isZero_of_isDerivedComplete_of_idealProduct_eq_top_of_sliceTestingFamily
    (X : RingedSite.{u, v, max u v w})
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (B : Stacks.WeaklyContractible.SliceTestingFamily.{max u v w} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hI : ∀ U : X.C, B.B U →
      (I.toSubmodule.obj (op U)).FG)
    (F : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, v, max u v w, max u v w} X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))
    (hIF : idealPowerProductOfSize X I F 1 = ⊤) :
    IsZero F := by
  have key : ∀ U : X.C, B.B U →
      (⊤ : F.Submodule).toSubmodule.obj (op U) = ⊥ := by
    intro U hU
    let : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) := by
      change IsMulCommutative (X.O.obj.obj (op U))
      infer_instance
    let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (F.val.obj (op U)) :=
      (F.val.obj (op U)).isModule
    let : HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    have hsmul : idealSectionsOfSize X I (op U) •
        (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
          (F.val.obj (op U))) = ⊤ := by
      have h := idealPowerProduct_obj_eq_pow_smul_top_of_sliceTestingFamily X I F U hU (hI U hU) 1
      rw [hIF, sheafSubmodule_top_obj, pow_one] at h
      exact h.symm
    have hcomplete : IsDerivedCompleteModule
        (idealSectionsOfSize X I (op U))
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).obj F) :=
      (isDerivedComplete_sheaf_single_iff_sections_of_sliceTestingFamily X B I F).mp hF U hU
    have hsub : Subsingleton
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).obj F) :=
      subsingleton_of_isDerivedCompleteModule_of_quotient_smul
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
        (idealSectionsOfSize X I (op U))
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).obj F)
        (hI U hU) hcomplete
        (Submodule.Quotient.subsingleton_iff.mpr hsmul)
    refine le_bot_iff.mp fun x _ ↦ ?_
    change x = 0
    exact Subsingleton.elim
      (α := (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).obj F)
      x 0
  have hall : ∀ U : X.Cᵒᵖ, (⊤ : F.Submodule).toSubmodule.obj U = ⊥ :=
    (sheafSubmodule_eq_bot_iff (⊤ : F.Submodule)).mp
      ((sheafSubmodule_eq_bot_iff_weaklyContractible_of_sliceTestingFamily X B
        (⊤ : F.Submodule)).mpr key)
  rw [IsZero.iff_id_eq_zero]
  ext U m
  change m = 0
  have hm : m ∈ (⊤ : F.Submodule).toSubmodule.obj U := by
    rw [sheafSubmodule_top_obj]
    exact Submodule.mem_top
  rwa [hall U] at hm

end AlgebraicGeometry.RingedSite

end
