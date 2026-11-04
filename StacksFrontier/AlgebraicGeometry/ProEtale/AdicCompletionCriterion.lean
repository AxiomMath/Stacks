module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.AdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.Homology.DerivedComplete.NakayamaModule

/-!
# Adic completeness of a sheaf of modules as a limit of its adic quotients

Let `X` be a ringed site whose topology has enough weakly contractible objects, let `I` be a
sheaf of ideals in its structure sheaf and let `F` be a sheaf of modules. The cone of quotient
maps `F ⟶ F/IⁿF` is a limit cone exactly when `F`, viewed in degree zero of the derived
category, is derived complete along `I`. A derived complete `F` whose first adic quotient
`F/IF` vanishes is itself zero.

Both sides are tested on sections over a weakly contractible object. There evaluation is exact,
so it commutes with the quotients and with the limit, and derived completeness of the sheaf is
derived completeness of the module of sections along the ideal of sections; for modules over a
ring, derived completeness along an ideal is already known to be the limit condition on the adic
quotients. The one point needing the weakly contractible object is that the sections of `IⁿF`
there are the usual products of sections of `Iⁿ` with sections of `F`: in general `IⁿF` is only
the subsheaf such products generate, and identifying the two uses that a locally surjective map
is surjective on sections.

## Main results

* `AlgebraicGeometry.RingedSite.isLimit_adicQuotientSystem_iff`: the cone of adic quotient maps
  is a limit cone exactly when the sheaf is derived complete.
* `AlgebraicGeometry.RingedSite.isZero_of_isDerivedComplete_of_idealProduct_eq_top`: derived
  Nakayama — a derived complete sheaf of modules with `IF = F` is zero.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_single_iff_sections_of_slicedObjectsSituation`:
  a sheaf of modules is derived complete exactly when its modules of sections over the members of
  a covering collection of weakly contractible objects are.
* `RingedSite.isDerivedComplete_single_of_pow_smul_eq_zero_of_slicedObjectsSituation`:
  a sheaf of modules on whose sections over those objects every section of the ideal sheaf acts
  nilpotently is derived complete.

## Implementation notes

The limit statement quantifies over an `AlgebraicGeometry.RingedSite.AdicQuotientSystem`, a
specification of the inverse system of quotients rather than a particular construction, so it
says the same thing about every presentation of `F/IⁿF`. Vanishing of `F/IF` is expressed as
the equality `IF = F` of subsheaves of `F`, with `IF` the adic filtration at exponent one.
Finite generation of the sheaf of ideals is asked for only on sections over the weakly
contractible objects, which is where it is used.

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

/-- Sections of the structure sheaf over any object form a commutative ring. -/
private instance (X : RingedSite.{u, v, max u v}) (U : X.Cᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := by
  change IsMulCommutative (X.O.obj.obj U)
  infer_instance

/-- Sections of a sheaf of modules are a module over the sections of the structure sheaf. -/
private instance (X : RingedSite.{u, v, max u v})
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ) :
    Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (F.val.obj U) :=
  (F.val.obj U).isModule

private theorem isDerivedComplete_sheaf_single_iff_sections_of_slicedObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : Stacks.WeaklyContractible.SlicedObjectsSituation.{w, v, u, max u v} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F) ↔
      ∀ U : X.C, hX.B U →
        let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
        letI : IsMulCommutative R := by
          change IsMulCommutative (X.O.obj.obj (op U))
          infer_instance
        letI : CommRing R := inferInstance
        let J : Ideal R := by
          change Submodule R R
          exact I.toSubmodule.obj (op U)
        let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
        letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)) :=
          Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
        IsDerivedCompleteModule J (G.obj F) := by
  rw [AlgebraicGeometry.RingedSite.isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation
    X hX I ((DerivedCategory.singleFunctor
      (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F)]
  constructor
  · intro h U hU
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    let : CommRing R := inferInstance
    let J : Ideal R := by
      show Submodule R R
      exact I.toSubmodule.obj (op U)
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    obtain ⟨hAdd, hLim, hColim, hProd, hComplete⟩ := h U hU
    let : G.Additive := hAdd
    let : PreservesFiniteLimits G := hLim
    let : PreservesFiniteColimits G := hColim
    let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)) := hProd
    show IsDerivedCompleteModule J (G.obj F)
    show ∀ f ∈ J, IsDerivedCompleteAt
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
        (G.obj F)) f
    intro f hf
    rw [isDerivedCompleteAt_iff_isIso]
    exact (isIso_oneSubSmulShift_congr
      ((G.mapDerivedCategorySingleFunctor 0).app F) f).mp (hComplete f hf)
  · intro h U hU
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    let : CommRing R := inferInstance
    let J : Ideal R := by
      show Submodule R R
      exact I.toSubmodule.obj (op U)
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    let : HasProductsOfShape ℕ (ModuleCat.{max u v} R) := inferInstance
    let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} R) :=
      moduleCat_hasExactLimitsOfShape_discrete.{max u v} R ℕ
    let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let : G.Additive := ⟨fun {_ _} _ _ => rfl⟩
    let : G.PreservesZeroMorphisms := inferInstance
    let : G.PreservesHomology := by
      apply Functor.preservesHomology_of_map_exact G
      intro S hS
      exact evaluation_map_exact_of_weaklyContractibleObjectsSituation X
        hX.toWeaklyContractibleObjectsSituation U hU S hS
    let : ∀ {A B : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
        (f : A ⟶ B), PreservesColimit (parallelPair f 0) G := fun f =>
      Functor.PreservesHomology.preservesCokernel G f
    let : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesCokernels G
    refine ⟨inferInstance, inferInstance, inferInstance,
      inferInstance, ?_⟩
    intro f hf
    show IsDerivedCompleteAt ((G.mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F)) f
    rw [isDerivedCompleteAt_iff_isIso]
    have hmod := h U hU
    have hsingle : IsDerivedCompleteAt
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj (G.obj F)) f :=
      hmod f hf
    rw [isDerivedCompleteAt_iff_isIso] at hsingle
    exact (isIso_oneSubSmulShift_congr
      ((G.mapDerivedCategorySingleFunctor 0).app F) f).mpr hsingle

private noncomputable def moduleAdicQuotientSystem
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A) :
    ℕᵒᵖ ⥤ ModuleCat A where
  obj n := ModuleCat.of A (M ⧸ (I ^ n.unop • (⊤ : Submodule A M)))
  map f := ModuleCat.ofHom (AdicCompletion.transitionMap I M
    (leOfHom f.unop))
  map_id n := by
    ext x; rfl
  map_comp f g := by
    ext x; rfl

private noncomputable def moduleAdicQuotientCone
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A) :
    Cone (moduleAdicQuotientSystem I M) where
  pt := M
  π := {
    app n := ModuleCat.ofHom (Submodule.mkQ (I ^ n.unop • (⊤ : Submodule A M)))
    naturality := by
      intro n m f
      ext x
      change Submodule.mkQ (I ^ m.unop • (⊤ : Submodule A M)) x =
        AdicCompletion.transitionMap I M (leOfHom f.unop)
          (Submodule.mkQ (I ^ n.unop • (⊤ : Submodule A M)) x)
      rfl }

private noncomputable def moduleAdicCompletionCone
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A) :
    Cone (moduleAdicQuotientSystem I M) where
  pt := ModuleCat.of A (AdicCompletion I M)
  π := {
    app n := ModuleCat.ofHom (AdicCompletion.eval I M n.unop)
    naturality := by
      intro n m f
      ext x
      exact (x.property (leOfHom f.unop)).symm }

private noncomputable def moduleAdicCompletionConeIsLimit
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A) :
    IsLimit (moduleAdicCompletionCone I M) := by
  refine IsLimit.mk (fun s => ModuleCat.ofHom {
    toFun x := ⟨fun n => (s.π.app (op n)) x, by
      intro m n h
      have hw := s.w (homOfLE h).op
      have he := congrArg (fun f : s.pt ⟶
        (moduleAdicQuotientSystem I M).obj (op m) => f x) hw
      change AdicCompletion.transitionMap I M h
        ((s.π.app (op n)) x) = (s.π.app (op m)) x at he
      exact he⟩
    map_add' := by
      intro x y
      apply AdicCompletion.ext
      intro n
      exact (s.π.app (op n)).hom.map_add x y
    map_smul' := by
      intro a x
      apply AdicCompletion.ext
      intro n
      exact (s.π.app (op n)).hom.map_smul a x }) ?_ ?_
  · intro s n
    ext x
    rfl
  · intro s f hf
    ext x
    apply AdicCompletion.ext
    intro n
    exact ConcreteCategory.congr_hom (hf (op n)) x

private noncomputable def moduleAdicCompletionComparison
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A) :
    moduleAdicQuotientCone I M ⟶ moduleAdicCompletionCone I M where
  hom := ModuleCat.ofHom (AdicCompletion.of I M)
  w := by
    intro n
    ext x
    exact AdicCompletion.eval_of I M n.unop x

/-- A morphism between two limit cones in `ModuleCat` is bijective on the cone points. -/
private lemma bijective_hom_of_isLimit {A : Type*} [Ring A] {ι : Type*} [Category ι]
    {D : ι ⥤ ModuleCat A} {c c' : Cone D} (hc : IsLimit c) (hc' : IsLimit c') (m : c ⟶ c') :
    Function.Bijective m.hom := by
  have : IsIso m := hc.hom_isIso hc' m
  exact (ConcreteCategory.isIso_iff_bijective m.hom).mp ((Cone.forget _).map_isIso m)

private theorem moduleAdicQuotientCone_isLimit_iff
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A) :
    Nonempty (IsLimit (moduleAdicQuotientCone I M)) ↔
      IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  constructor
  · rintro ⟨h⟩
    exact bijective_hom_of_isLimit h (moduleAdicCompletionConeIsLimit I M)
      (moduleAdicCompletionComparison I M)
  · intro h
    let : IsIso (moduleAdicCompletionComparison I M).hom :=
      (ConcreteCategory.isIso_iff_bijective _).mpr h
    have hcompCone : IsIso (moduleAdicCompletionComparison I M) :=
      Cone.cone_iso_of_hom_iso (moduleAdicCompletionComparison I M)
    let e := asIso (moduleAdicCompletionComparison I M)
    exact ⟨(moduleAdicCompletionConeIsLimit I M).ofIsoLimit e.symm⟩

private theorem evaluation_jointly_reflects_iso_of_weaklyContractibleObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{w, v, u, max u v}
      X.C X.J)
    {F G : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : F ⟶ G)
    (hf : ∀ U : X.C, hX.B U →
      Function.Bijective
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).map f)) :
    IsIso f := by
  let B := hX.withRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let S₁ : ShortComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    ShortComplex.mk (0 : F ⟶ F) f (by simp)
  have hS₁ : S₁.Exact := by
    apply (Stacks.WeaklyContractible.exact_iff_exact_sections_of_weaklyContractibleObjectsSituation
      X.J B S₁).2
    intro U hU
    show ∀ x, (f.val.app (op U)) x = 0 ↔
      x ∈ Set.range (fun _ : F.val.obj (op U) => (0 : F.val.obj (op U)))
    intro x
    constructor
    · intro hx
      have hzero : x = 0 := (hf U hU).1 (a₁ := x) (a₂ := 0) (by
        show f.val.app (op U) x = f.val.app (op U) 0
        rw [hx, map_zero])
      simp [hzero]
    · rintro ⟨y, rfl⟩
      simp
  have hmono : Mono f := (ShortComplex.exact_iff_mono S₁ (by rfl)).mp hS₁
  let S₂ : ShortComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    ShortComplex.mk f (0 : G ⟶ G) (by simp)
  have hS₂ : S₂.Exact := by
    apply (Stacks.WeaklyContractible.exact_iff_exact_sections_of_weaklyContractibleObjectsSituation
      X.J B S₂).2
    intro U hU
    show ∀ y, (0 : G.val.obj (op U)) = 0 ↔
      y ∈ Set.range (f.val.app (op U))
    intro y
    constructor
    · intro _
      exact (hf U hU).2 y
    · intro _
      simp
  have hepi : Epi f := (ShortComplex.exact_iff_epi S₂ (by rfl)).mp hS₂
  exact isIso_of_mono_of_epi f

/-- The underlying type-valued presheaf of a sheaf of abelian groups is a sheaf of types. -/
private lemma isSheaf_forget_comp {C : Type*} [Category C] {J : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (hP : Presheaf.IsSheaf J P) :
    Presieve.IsSheaf J (P ⋙ CategoryTheory.forget AddCommGrpCat) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf _ hP

private lemma sheafSubmodule_bot_obj
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (F : SheafOfModules.{v} R) (U : Cᵒᵖ) :
    (⊥ : F.Submodule).toSubmodule.obj U = ⊥ := by
  let N : F.Submodule :=
    { toSubmodule := ⊥
      isSheaf := by
        intro V x hx
        show x = 0
        apply (isSheaf_forget_comp F.isSheaf _ hx).isSeparatedFor.ext
        intro W f hf
        show F.val.map f.op x = F.val.map f.op 0
        simpa only [map_zero] using (show F.val.map f.op x = 0 from hf) }
  exact le_bot_iff.mp (show (⊥ : F.Submodule).toSubmodule.obj U ≤ N.toSubmodule.obj U
    from (SheafOfModules.Submodule.le_iff.mp (bot_le : (⊥ : F.Submodule) ≤ N)) U)

private lemma sheafSubmodule_eq_bot_iff
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {F : SheafOfModules.{v} R} (N : F.Submodule) :
    N = ⊥ ↔ ∀ U, N.toSubmodule.obj U = ⊥ := by
  constructor
  · rintro rfl U
    exact sheafSubmodule_bot_obj F U
  · intro h
    apply SheafOfModules.Submodule.ext
    apply PresheafOfModules.Submodule.ext
    intro U
    rw [h, sheafSubmodule_bot_obj]

private lemma sheafSubmodule_iInf_obj
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {F : SheafOfModules.{v} R}
    {ι : Sort*} (N : ι → F.Submodule) (U : Cᵒᵖ) :
    (⨅ i, N i).toSubmodule.obj U = ⨅ i, (N i).toSubmodule.obj U := by
  rw [SheafOfModules.Submodule.toSubmodule_iInf]
  conv_lhs => rw [iInf, PresheafOfModules.Submodule.sInf_obj]
  rw [iInf_range]

private theorem evaluation_jointly_reflects_limit_of_weaklyContractibleObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{w, v, u, max u v}
      X.C X.J)
    (D : ℕᵒᵖ ⥤ SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (c : Cone D) :
    Nonempty (IsLimit c) ↔ ∀ U : X.C, hX.B U →
      Nonempty (IsLimit ((SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).mapCone c)) := by
  constructor
  · rintro ⟨hc⟩ U hU
    exact ⟨isLimitOfPreserves _ hc⟩
  · intro h
    let f := (limit.isLimit D).liftConeMorphism c
    have hf : IsIso f.hom := by
      apply evaluation_jointly_reflects_iso_of_weaklyContractibleObjectsSituation X hX f.hom
      intro U hU
      let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
      obtain ⟨hc⟩ := h U hU
      exact bijective_hom_of_isLimit hc (isLimitOfPreserves G (limit.isLimit D))
        (G.mapConeMorphism f)
    have : IsIso ((limit.isLimit D).lift c) := hf
    exact ⟨(limit.isLimit D).ofPointIso⟩

private def submoduleSheafify
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v}} {F : SheafOfModules.{max u v} R}
    (N : F.val.Submodule) : F.Submodule where
  toSubmodule :=
    { obj U :=
        { carrier := (N.toSubfunctor.sheafify J).obj U
          zero_mem' := N.toSubfunctor.le_sheafify J U ((N.obj U).zero_mem)
          add_mem' := by
            intro x y hx hy
            apply J.superset_covering _ (J.intersection_covering hx hy)
            intro V f hf
            change F.val.map f.op (x + y) ∈ N.obj (op V)
            rw [map_add]
            exact (N.obj (op V)).add_mem hf.1 hf.2
          smul_mem' := by
            intro a x hx
            apply J.superset_covering _ hx
            intro V f hf
            change F.val.map f.op (a • x) ∈ N.obj (op V)
            rw [F.val.map_smul]
            exact (N.obj (op V)).smul_mem _ hf }
      map f := (N.toSubfunctor.sheafify J).map f }
  isSheaf := by
    intro U x hx
    change x ∈ ((N.toSubfunctor.sheafify J).sheafify J).obj U at hx
    rwa [N.toSubfunctor.sheafify_sheafify (isSheaf_forget_comp F.isSheaf)] at hx

private lemma le_submoduleSheafify
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v}} {F : SheafOfModules.{max u v} R}
    (N : F.val.Submodule) : N ≤ (submoduleSheafify N).toSubmodule := by
  intro U x hx
  exact N.toSubfunctor.le_sheafify J U hx

private lemma submoduleSheafify_le_iff
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v}} {F : SheafOfModules.{max u v} R}
    (N : F.val.Submodule) (P : F.Submodule) :
    submoduleSheafify N ≤ P ↔ N ≤ P.toSubmodule := by
  refine ⟨fun h => (le_submoduleSheafify N).trans h, ?_⟩
  intro h U x hx
  change N.toSubfunctor.sieveOfSection x ∈ J U.unop at hx
  apply P.isSheaf x
  exact J.superset_covering (fun V f hf => h (op V) hf) hx

private def idealPowerActionPresheaf
    (X : RingedSite.{u, v, max u v})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    F.val.Submodule where
  obj U :=
    let J : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := I.toSubmodule.obj U
    J ^ n • ⊤
  map {U V} f := by
    let φ := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom
    let JU : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := I.toSubmodule.obj U
    let JV : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) := I.toSubmodule.obj V
    have hI : Ideal.map φ JU ≤ JV := by
      apply Ideal.map_le_iff_le_comap.mpr
      exact I.toSubmodule.map f
    have hn : Ideal.map φ (JU ^ n) ≤ JV ^ n := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' hI n
    intro x hx
    change x ∈ JU ^ n • (⊤ : Submodule _ _) at hx
    change F.val.restrictₛₗ f x ∈ JV ^ n •
      (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) (F.val.obj V))
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha m hm
      rw [(F.val.restrictₛₗ f).map_smulₛₗ]
      exact Submodule.smul_mem_smul (Ideal.map_le_iff_le_comap.mp hn ha) trivial
    · intro x y hx hy
      change F.val.map f (x + y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ hx hy

private lemma idealPowerProduct_eq_sheafify
    (X : RingedSite.{u, v, max u v})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℕ) :
    idealPowerProduct X I F n = submoduleSheafify (idealPowerActionPresheaf X I F n) := by
  apply le_antisymm
  · apply sInf_le
    intro U
    dsimp only
    intro a ha m
    apply le_submoduleSheafify (idealPowerActionPresheaf X I F n) U
    let J : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := I.toSubmodule.obj U
    show a • m ∈ J ^ n •
      (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (F.val.obj U))
    exact Submodule.smul_mem_smul (show a ∈ J ^ n from ha) Submodule.mem_top
  · apply le_sInf
    intro N hN
    rw [submoduleSheafify_le_iff]
    intro U
    let J : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) := I.toSubmodule.obj U
    show J ^ n •
      (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (F.val.obj U)) ≤ _
    apply Submodule.smul_le.mpr
    intro a ha m hm
    exact hN U a ha m

private lemma pow_smul_le_iff_products
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) (N : Submodule A M) :
    I ^ n • (⊤ : Submodule A M) ≤ N ↔
      ∀ a : Fin n → I, ∀ m : M, (∏ i, (a i : A)) • m ∈ N := by
  constructor
  · intro h a m
    apply h
    apply Submodule.smul_mem_smul _ (Submodule.mem_top)
    simpa using Ideal.prod_mem_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      (a i).property)
  · intro h
    induction n generalizing N with
    | zero =>
      rw [pow_zero, one_smul]
      intro m hm
      simpa using h (fun i => Fin.elim0 i) m
    | succ n ih =>
      rw [pow_succ', Submodule.mul_smul]
      apply Submodule.smul_le.mpr
      intro a ha m hm
      apply (ih (N.comap (LinearMap.lsmul A M a)) ?_) hm
      intro b y
      have hh := h (Fin.cons ⟨a, ha⟩ b) y
      show a • ((∏ i, (b i : A)) • y) ∈ N
      simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_smul] using hh

private abbrev PowerExpression
    {A : Type*} [CommRing A] (I : Ideal A) (M : Type*) (n : ℕ) :=
  List ((Fin n → I) × M)

private def powerExpressionValue
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {I : Ideal A} {n : ℕ} (l : PowerExpression I M n) : M :=
  (l.map fun t => (∏ i, (t.1 i : A)) • t.2).sum

private lemma mem_pow_smul_iff_expression
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) (x : M) :
    x ∈ I ^ n • (⊤ : Submodule A M) ↔
      ∃ l : PowerExpression I M n, powerExpressionValue l = x := by
  classical
  let N : Submodule A M :=
    { carrier := Set.range (powerExpressionValue (I := I) (M := M) (n := n))
      zero_mem' := ⟨[], rfl⟩
      add_mem' := by
        rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a ++ b, by simp [powerExpressionValue]⟩
      smul_mem' := by
        rintro r x ⟨a, rfl⟩
        refine ⟨a.map (fun t => (t.1, r • t.2)), ?_⟩
        induction a with
        | nil => simp [powerExpressionValue]
        | cons t l ih =>
          simp only [List.map_cons, powerExpressionValue, List.sum_cons] at ih ⊢
          rw [smul_add, smul_comm, ih] }
  have hN : N = I ^ n • (⊤ : Submodule A M) := by
    apply le_antisymm
    · rintro y ⟨l, rfl⟩
      induction l with
      | nil => exact Submodule.zero_mem _
      | cons t l ih =>
        exact Submodule.add_mem _
          ((pow_smul_le_iff_products I n (I ^ n • (⊤ : Submodule A M))).mp le_rfl t.1 t.2)
          ih
    · apply (pow_smul_le_iff_products I n N).mpr
      intro a m
      exact ⟨[(a, m)], by simp [powerExpressionValue]⟩
  show x ∈ I ^ n • (⊤ : Submodule A M) ↔ x ∈ N
  rw [hN]

private lemma locallyBijective_ulift
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type v} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η] :
    J.W (Functor.whiskerRight η uliftFunctor.{u}) := by
  let η' := Functor.whiskerRight η uliftFunctor.{u}
  let : Presheaf.IsLocallyInjective J η' := ⟨by
    intro V x y h
    change ULift.up (η.app V x.down) = ULift.up (η.app V y.down) at h
    have hh := Presheaf.equalizerSieve_mem J η x.down y.down (ULift.up_injective h)
    apply J.superset_covering _ hh
    intro W f hf
    exact ULift.ext _ _ hf⟩
  let : Presheaf.IsLocallySurjective J η' := ⟨by
    intro V x
    apply J.superset_covering _ (Presheaf.imageSieve_mem J η x.down)
    rintro W f ⟨y, hy⟩
    exact ⟨ULift.up y, ULift.ext _ _ hy⟩⟩
  exact J.W_of_isLocallyBijective η'

private lemma exists_sections_refinement_of_surjective_sections
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (U : C)
    (hU : ∀ (A B : Sheaf J (Type (max u v))) (φ : A ⟶ B),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U)))
    {ι : Type (max u v)} (V : ι → C) (f : ∀ i, V i ⟶ U)
    (hcov : Sieve.ofArrows V f ∈ J U)
    {κ : Type*} (F : κ → Sheaf J (Type (max u v)))
    (x : ∀ k i, (F k).obj.obj (op (V i))) :
    ∃ y : ∀ k, (F k).obj.obj (op U), ∃ S : Sieve U,
      S ∈ J U ∧ ∀ (W : C) (g : W ⟶ U), S g →
        ∃ i, ∃ a : W ⟶ V i, a ≫ f i = g ∧
          ∀ k, (F k).obj.map g.op (y k) = (F k).obj.map a.op (x k i) := by
  classical
  let P : Cᵒᵖ ⥤ Type (max u v) :=
    { obj W := ULift.{u} (Σ i, W.unop ⟶ V i)
      map g := ↾fun t => ULift.up ⟨t.down.1, g.unop ≫ t.down.2⟩
      map_id W := by
        apply ConcreteCategory.hom_ext (CC := fun X => X)
        intro t
        show (ULift.up ⟨t.down.1, 𝟙 _ ≫ t.down.2⟩ :
          ULift.{u} (Σ i, W.unop ⟶ V i)) = t
        simp
      map_comp g h := by
        apply ConcreteCategory.hom_ext (CC := fun X => X)
        intro t
        show (ULift.up ⟨t.down.1, (h.unop ≫ g.unop) ≫ t.down.2⟩ :
            ULift.{u} (Σ i, _ ⟶ V i)) =
          ULift.up ⟨t.down.1, h.unop ≫ (g.unop ≫ t.down.2)⟩
        rw [Category.assoc] }
  let Y : Cᵒᵖ ⥤ Type (max u v) :=
    { obj W := ULift.{u} (W.unop ⟶ U)
      map g := ↾fun h => ULift.up (g.unop ≫ h.down)
      map_id W := by
        apply ConcreteCategory.hom_ext (CC := fun X => X)
        intro h
        show (ULift.up (𝟙 _ ≫ h.down) : ULift.{u} (W.unop ⟶ U)) = h
        simp
      map_comp g h := by
        apply ConcreteCategory.hom_ext (CC := fun X => X)
        intro q
        show (ULift.up ((h.unop ≫ g.unop) ≫ q.down) : ULift.{u} (_ ⟶ U)) =
          ULift.up (h.unop ≫ (g.unop ≫ q.down))
        rw [Category.assoc] }
  let π : P ⟶ Y :=
    { app W := ↾fun t => ULift.up (t.down.2 ≫ f t.down.1)
      naturality W Z g := by
        apply ConcreteCategory.hom_ext (CC := fun X => X)
        intro t
        exact congrArg ULift.up (Category.assoc _ _ _) }
  have : Presheaf.IsLocallySurjective J π := ⟨by
    intro W g
    apply J.superset_covering _ (J.pullback_stable g.down hcov)
    intro Z a ha
    obtain ⟨i, b, hb⟩ := (Sieve.mem_ofArrows_iff V f (a ≫ g.down)).mp ha
    exact ⟨ULift.up ⟨i, b⟩, congrArg ULift.up hb.symm⟩⟩
  let η := toSheafify J P
  let ε := toSheafify J Y
  let idU : Y.obj (op U) := ULift.up (𝟙 U)
  let π' := (presheafToSheaf J (Type (max u v))).map π
  obtain ⟨s, hs⟩ := hU _ _ π'
    ((Presheaf.isLocallySurjective_presheafToSheaf_map_iff J π).mpr inferInstance)
    (ε.app (op U) idU)
  change π'.hom.app (op U) s = ε.app (op U) idU at hs
  let α (k : κ) : P ⟶ (F k).obj :=
    { app W := ↾fun t => (F k).obj.map t.down.2.op (x k t.down.1)
      naturality W Z g := by
        apply ConcreteCategory.hom_ext
        intro t
        show (F k).obj.map (g.unop ≫ t.down.2).op (x k t.down.1) =
          (F k).obj.map g ((F k).obj.map t.down.2.op (x k t.down.1))
        simp only [op_comp, Functor.map_comp, types_comp_apply, Quiver.Hom.op_unop] }
  let hη : J.W η := J.W_toSheafify P
  let β (k : κ) := (hη.homEquiv (F k).obj (F k).property).symm (α k)
  have hβ (k : κ) : η ≫ β k = α k :=
    (hη.homEquiv (F k).obj (F k).property).apply_symm_apply (α k)
  let y (k : κ) := (β k).app (op U) s
  let S : Sieve U :=
    { arrows W g := ∃ t : P.obj (op W), π.app _ t = ULift.up g ∧
        η.app _ t = (sheafify J P).map g.op s
      downward_closed := by
        rintro W Z g ⟨t, ht, hsq⟩ a
        refine ⟨P.map a.op t, ?_, ?_⟩
        · exact (π.naturality_apply a.op t).trans (congrArg (Y.map a.op) ht)
        · rw [η.naturality_apply, hsq, ← Functor.map_comp_apply, ← op_comp] }
  have hS : S ∈ J U := by
    apply J.transitive (Presheaf.imageSieve_mem J η s)
    intro W g hg
    obtain ⟨t, ht⟩ := hg
    let gW : Y.obj (op W) := ULift.up g
    have heq : ε.app (op W) (π.app _ t) = ε.app (op W) gW := by
      have h1 : ε.app (op W) (π.app _ t) = π'.hom.app (op W) (η.app (op W) t) :=
        congrArg (fun q : P ⟶ sheafify J Y => q.app (op W) t) (toSheafify_naturality J π)
      have h2 : π'.hom.app (op W) (η.app (op W) t) =
          (sheafify J Y).map g.op (π'.hom.app (op U) s) := by
        rw [ht, π'.hom.naturality_apply]
      have h3 := NatTrans.naturality_apply ε g.op idU
      rw [h1, h2, hs, ← h3]
      congr 1
      exact ULift.ext _ _ (Category.comp_id g)
    apply J.superset_covering _
      (Presheaf.equalizerSieve_mem J ε (π.app _ t) gW heq)
    intro Z a ha
    refine ⟨P.map a.op t, ?_, ?_⟩
    · exact (π.naturality_apply a.op t).trans ha
    · rw [η.naturality_apply, ht, ← Functor.map_comp_apply, ← op_comp]
  refine ⟨y, S, hS, ?_⟩
  rintro W g ⟨⟨⟨i, a⟩⟩, ht, hs'⟩
  refine ⟨i, a, ULift.up_injective ht, ?_⟩
  intro k
  have hh := congrArg (fun q => q.app (op W)
    (ULift.up (⟨i, a⟩ : Σ i, W ⟶ V i))) (hβ k)
  change (β k).app (op W) (η.app (op W) (ULift.up ⟨i, a⟩)) =
    (F k).obj.map a.op (x k i) at hh
  rw [hs'] at hh
  have hn := ConcreteCategory.congr_hom (C := Type (max u v)) (CC := fun X => X)
    ((β k).naturality g.op) s
  exact hn.symm.trans hh

private lemma sum_range_eq_of_eventually_zero
    {A : Type*} [AddCommMonoid A] (a : ℕ → A) {m n : ℕ}
    (hm : ∀ i, m ≤ i → a i = 0) (hn : ∀ i, n ≤ i → a i = 0) :
    ∑ i ∈ Finset.range m, a i = ∑ i ∈ Finset.range n, a i := by
  wlog h : m ≤ n generalizing m n
  · exact (this hn hm (Nat.le_of_not_ge h)).symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro i hi him
  exact hm i (Nat.le_of_not_lt (by simpa using him))

private lemma exists_locallyFiniteSum
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{max u v}) (U : C)
    (S : Sieve U) (hS : S ∈ J U)
    (b : ∀ (W : C) (f : W ⟶ U), S f → ℕ)
    (x : ℕ → F.obj.obj (op U))
    (hx : ∀ (W : C) (f : W ⟶ U) (hf : S f) (i : ℕ), b W f hf ≤ i →
      F.obj.map f.op (x i) = 0) :
    ∃ y : F.obj.obj (op U), ∀ (W : C) (f : W ⟶ U) (hf : S f),
      F.obj.map f.op y = ∑ i ∈ Finset.range (b W f hf), F.obj.map f.op (x i) := by
  let P := F.obj ⋙ CategoryTheory.forget AddCommGrpCat
  have hF : Presieve.IsSheaf J P := isSheaf_forget_comp F.property
  let t : Presieve.FamilyOfElements P S.arrows := fun W f hf =>
    ∑ i ∈ Finset.range (b W f hf), F.obj.map f.op (x i)
  have ht : t.Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ heq
    show F.obj.map g₁.op (∑ i ∈ Finset.range (b W₁ f₁ hf₁), F.obj.map f₁.op (x i)) =
      F.obj.map g₂.op (∑ i ∈ Finset.range (b W₂ f₂ hf₂), F.obj.map f₂.op (x i))
    simp only [map_sum, ← Functor.map_comp_apply, ← op_comp, heq]
    apply sum_range_eq_of_eventually_zero
    · intro i hi
      rw [← heq, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hx W₁ f₁ hf₁ i hi,
        map_zero]
    · intro i hi
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hx W₂ f₂ hf₂ i hi, map_zero]
  exact ⟨(hF S hS).amalgamate t ht, fun W f hf => (hF S hS).valid_glue ht f hf⟩

private lemma powerExpressionValue_eq_sum_range
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {I : Ideal A} {n : ℕ} (l : PowerExpression I M n) :
    powerExpressionValue l = ∑ j ∈ Finset.range l.length,
      (∏ k, ((l.getD j (0, 0)).1 k : A)) • (l.getD j (0, 0)).2 := by
  induction l with
  | nil => simp [powerExpressionValue]
  | cons t l ih =>
    simp only [powerExpressionValue, List.map_cons, List.sum_cons] at ih ⊢
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at ih ⊢
    rw [ih, add_comm]


private abbrev moduleSectionsSheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u v}} (F : SheafOfModules.{max u v} R) :
    Sheaf J (Type (max u v)) :=
  (sheafCompose J (CategoryTheory.forget AddCommGrpCat)).obj ⟨F.val.presheaf, F.isSheaf⟩

private lemma idealPowerProduct_obj_of_surjective_sections
    (X : RingedSite.{u, v, max u v})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C)
    (hU : ∀ (A B : Sheaf X.J (Type (max u v))) (φ : A ⟶ B),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U)))
    (hI : (I.toSubmodule.obj (op U)).FG) (n : ℕ) :
    (idealPowerProduct X I F n).toSubmodule.obj (op U) =
      (idealPowerActionPresheaf X I F n).obj (op U) := by
  classical
  rw [idealPowerProduct_eq_sheafify]
  apply le_antisymm
  swap
  · exact le_submoduleSheafify _ (op U)
  intro x hx
  change (idealPowerActionPresheaf X I F n).toSubfunctor.sieveOfSection x ∈ X.J U at hx
  set S₀ := (idealPowerActionPresheaf X I F n).toSubfunctor.sieveOfSection x with hS₀
  let ι : Type (max u v) := Σ W : X.C, {a : W ⟶ U // S₀.arrows a}
  let V : ι → X.C := fun i => i.1
  let f : ∀ i, V i ⟶ U := fun i => i.2.1
  have hcov : Sieve.ofArrows V f ∈ X.J U := by
    refine X.J.superset_covering (fun W g hg => ?_) hx
    exact Sieve.ofArrows_mk V f (⟨W, ⟨g, hg⟩⟩ : ι)
  have hle : Sieve.ofArrows V f ≤ S₀ := by
    intro W g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨i, a, rfl⟩ := hg
    exact S₀.downward_closed i.2.2 a
  have hex (i : ι) : ∃ l : PowerExpression
      (I.toSubmodule.obj (op (V i)) :
        Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op (V i))))
      (F.val.obj (op (V i))) n,
      powerExpressionValue l = F.val.restrictₛₗ (f i).op x := by
    apply (mem_pow_smul_iff_expression _ n _).mp
    exact hle _ (Sieve.ofArrows_mk V f i)
  choose l hl using hex
  let z (i : ι) : (Fin n → (I.toSubmodule.obj (op (V i)) :
      Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op (V i))))) ×
      F.val.obj (op (V i)) := (fun _ => 0, 0)
  let a (i : ι) (j : ℕ) (k : Fin n) := (l i |>.getD j (z i)).1 k
  let m (i : ι) (j : ℕ) := (l i |>.getD j (z i)).2
  let T : ((ℕ × Fin n) ⊕ ℕ) → Sheaf X.J (Type (max u v)) :=
    Sum.elim (fun _ => moduleSectionsSheaf I.toSheafOfModules)
      (fun _ => moduleSectionsSheaf F)
  let s : ∀ k i, (T k).obj.obj (op (V i)) := fun k i =>
    match k with
    | .inl jk => a i jk.1 jk.2
    | .inr j => m i j
  obtain ⟨y, S, hS, href⟩ := exists_sections_refinement_of_surjective_sections X.J U hU V f hcov T s
  choose d g hg hy using href
  let A (j : ℕ) (k : Fin n) :
      (I.toSubmodule.obj (op U) :
        Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) := y (.inl (j, k))
  let M (j : ℕ) : F.val.obj (op U) := y (.inr j)
  let b (W : X.C) (q : W ⟶ U) (hq : S q) := (l (d W q hq)).length
  have hA (W : X.C) (q : W ⟶ U) (hq : S q) (j : ℕ) (k : Fin n) :
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map q.op).hom (A j k).val =
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (g W q hq).op).hom
          (a (d W q hq) j k) := by
    exact congrArg Subtype.val (hy W q hq (.inl (j, k)))
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
      let : CommRing R := by show CommRing (X.O.obj.obj (op U)); infer_instance
      simp only [Finset.prod_const, Finset.card_fin]
    rw [← hpow]
    exact hh
  obtain ⟨r, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.FG.pow (n := n) (show J.FG from hI))
  have hcoeff (j : ℕ) : ∃ e : Fin r → R, ∑ k, e k • z k = c j := by
    apply (Submodule.mem_span_range_iff_exists_fun R).mp
    rw [hz]
    exact hc j
  choose e he using hcoeff
  have hlocal (W : X.C) (q : W ⟶ U) (hq : S q) :
      F.val.restrictₛₗ q.op x = ∑ j ∈ Finset.range (b W q hq),
        F.val.restrictₛₗ q.op (c j • M j) := by
    conv_lhs => rw [← hg W q hq]
    show F.val.presheaf.map (g W q hq ≫ f (d W q hq)).op x = _
    rw [op_comp, Functor.map_comp]
    show F.val.restrictₛₗ (g W q hq).op (F.val.restrictₛₗ (f (d W q hq)).op x) = _
    rw [← hl (d W q hq), powerExpressionValue_eq_sum_range (l (d W q hq)), map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    show F.val.restrictₛₗ (g W q hq).op
        ((∏ k, (a (d W q hq) j k).val) • m (d W q hq) j) =
      F.val.restrictₛₗ q.op (c j • M j)
    rw [(F.val.restrictₛₗ (g W q hq).op).map_smulₛₗ, (F.val.restrictₛₗ q.op).map_smulₛₗ]
    dsimp only [c]
    simp only [map_prod, hM W q hq j]
    congr 1
    show (∏ k, ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (g W q hq).op).hom
        (a (d W q hq) j k).val) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map q.op).hom
        (∏ k, (show R from (A j k).val))
    let : CommMonoid R := inferInstance
    rw [map_prod ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map q.op).hom
      (fun k => (show R from (A j k).val)) Finset.univ]
    exact Finset.prod_congr rfl (fun k _ => (hA W q hq j k).symm)
  let F' : Sheaf X.J AddCommGrpCat.{max u v} := ⟨F.val.presheaf, F.isSheaf⟩
  have hsum (k : Fin r) : ∃ t : F.val.obj (op U), ∀ (W : X.C) (q : W ⟶ U) (hq : S q),
      F.val.restrictₛₗ q.op t = ∑ j ∈ Finset.range (b W q hq),
        F.val.restrictₛₗ q.op (e j k • M j) := by
    apply exists_locallyFiniteSum F' U S hS b (fun j => e j k • M j)
    intro W q hq j hj
    show F.val.restrictₛₗ q.op (e j k • M j) = 0
    rw [(F.val.restrictₛₗ q.op).map_smulₛₗ, hzero W q hq j hj, smul_zero]
  choose t ht using hsum
  have hxsum : x = ∑ k, z k • t k := by
    apply (isSheaf_forget_comp F.isSheaf S hS).isSeparatedFor.ext
    intro W q hq
    show F.val.restrictₛₗ q.op x = F.val.restrictₛₗ q.op (∑ k, z k • t k)
    have htk (k : Fin r) : F.val.restrictₛₗ q.op (z k • t k) =
        ∑ j ∈ Finset.range (b W q hq), F.val.restrictₛₗ q.op (z k • (e j k • M j)) := by
      rw [(F.val.restrictₛₗ q.op).map_smulₛₗ]
      rw [ht k W q hq, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact ((F.val.restrictₛₗ q.op).map_smulₛₗ (z k) (e j k • M j)).symm
    rw [hlocal W q hq, map_sum]
    simp_rw [htk]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← map_sum]
    apply congrArg (F.val.restrictₛₗ q.op)
    rw [← he j, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro k hk
    show (e j k * z k) • M j = z k • (e j k • M j)
    rw [mul_smul, smul_comm]
  show x ∈ J ^ n • (⊤ : Submodule R (F.val.obj (op U)))
  rw [hxsum]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  rw [← hz]
  exact Submodule.subset_span (Set.mem_range_self k)

private lemma idealPowerProduct_obj_eq_pow_smul_top_of_surjective_sections
    (X : RingedSite.{u, v, max u v})
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C)
    (hU : ∀ (A B : Sheaf X.J (Type (max u v))) (φ : A ⟶ B),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U)))
    (hI : (I.toSubmodule.obj (op U)).FG) (n : ℕ) :
    letI : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) := by
      change IsMulCommutative (X.O.obj.obj (op U))
      infer_instance
    letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
        (F.val.obj (op U)) :=
      (F.val.obj (op U)).isModule
    (idealPowerProduct X I F n).toSubmodule.obj (op U) =
      idealSections X I (op U) ^ n •
        (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
          (F.val.obj (op U))) :=
  idealPowerProduct_obj_of_surjective_sections X I F U hU hI n

private lemma sheafSubmodule_eq_bot_iff_hasEnoughObjects
    (X : RingedSite.{u, v, max u v})
    (B : ObjectProperty X.C) (hX : X.J.HasEnoughObjects B)
    {F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (N : F.Submodule) :
    N = ⊥ ↔ ∀ U : X.C, B U →
      N.toSubmodule.obj (op U) = ⊥ := by
  refine ⟨fun h U _ => h ▸ sheafSubmodule_bot_obj F (op U), ?_⟩
  intro h
  apply (sheafSubmodule_eq_bot_iff N).mpr
  intro U
  apply le_bot_iff.mp
  intro x hx
  show x = 0
  obtain ⟨ι, V, f, hcov, hV⟩ := hX U.unop
  apply (isSheaf_forget_comp F.isSheaf _ hcov).isSeparatedFor.ext
  intro W g hg
  rw [Sieve.mem_ofArrows_iff] at hg
  obtain ⟨i, a, rfl⟩ := hg
  have hz : F.val.map (f i).op x = 0 := by
    have hm := N.toSubmodule.map (f i).op hx
    rwa [h _ (hV i)] at hm
  show (F.val.presheaf.map (a ≫ f i).op) x = (F.val.presheaf.map (a ≫ f i).op) 0
  simp only [op_comp, Functor.map_comp, map_zero]
  exact congrArg (fun z => F.val.presheaf.map a.op z) hz |>.trans (map_zero _)

private lemma evaluation_cokernel_submodule_of_weaklyContractibleObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{w, v, u, max u v}
      X.C X.J)
    (U : X.C) (hU : hX.B U)
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (N : F.Submodule) :
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    ∃ e : ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
        (G.obj F ⧸ N.toSubmodule.obj (op U)) ≅ G.obj (cokernel N.ι),
      ModuleCat.ofHom (N.toSubmodule.obj (op U)).mkQ ≫ e.hom =
        G.map (cokernel.π N.ι) := by
  let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
  let : PreservesFiniteColimits G :=
    evaluation_preservesFiniteColimits_of_weaklyContractibleObjectsSituation
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) hX U hU
  let B := hX.withRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let q := ((cokernel.π N.ι).val.app (op U)).hom
  have hsurj : Function.Surjective q :=
    (ModuleCat.epi_iff_surjective (G.map (cokernel.π N.ι))).mp inferInstance
  have hker : q.ker = N.toSubmodule.obj (op U) := by
    have he :=
      (Stacks.WeaklyContractible.exact_iff_exact_sections_of_weaklyContractibleObjectsSituation
        X.J B (ShortComplex.cokernelSequence N.ι)).mp
        (ShortComplex.cokernelSequence_exact N.ι) hU
    ext x
    show q x = 0 ↔ x ∈ N.toSubmodule.obj (op U)
    have he' : q x = 0 ↔ ∃ y : N.toSubmodule.obj (op U), (y : F.val.obj (op U)) = x := he x
    exact he'.trans ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  let e := ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    (q.quotKerEquivOfSurjective hsurj)).toModuleIso
  refine ⟨e, ?_⟩
  ext x
  exact q.quotKerEquivOfSurjective_apply_mk hsurj x

private lemma evaluation_adicQuotientCone_isLimit_iff_of_weaklyContractibleObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : Stacks.WeaklyContractible.WeaklyContractibleObjectsSituation.{w, v, u, max u v}
      X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (hU : hX.B U)
    (hpow : ∀ n, (idealPowerProduct X I F n).toSubmodule.obj (op U) =
      (idealPowerActionPresheaf X I F n).obj (op U)) :
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    letI : IsMulCommutative R := by
      change IsMulCommutative (X.O.obj.obj (op U)); infer_instance
    let J : Ideal R := I.toSubmodule.obj (op U)
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    Nonempty (IsLimit (G.mapCone
      (Cone.mk F (adicQuotientSystem X I F).quotientMap))) ↔ IsAdicComplete J (G.obj F) := by
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
  let J : Ideal R := I.toSubmodule.obj (op U)
  let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
  let M := G.obj F
  let D := (adicQuotientSystem X I F).Q ⋙ G
  have he (n : ℕ) : ∃ e : (moduleAdicQuotientSystem J M).obj (op n) ≅ D.obj (op n),
      (moduleAdicQuotientCone J M).π.app (op n) ≫ e.hom =
        G.map ((adicQuotientSystem X I F).quotientMap.app (op n)) := by
    have hex := evaluation_cokernel_submodule_of_weaklyContractibleObjectsSituation X hX U hU F
      (idealPowerProduct X I F n)
    have hn := hpow n
    change (idealPowerProduct X I F n).toSubmodule.obj (op U) =
      J ^ n • (⊤ : Submodule R M) at hn
    dsimp only at hex
    rw [hn] at hex
    exact hex
  choose e he using he
  let eD : moduleAdicQuotientSystem J M ≅ D := NatIso.ofComponents (fun n => e n.unop) (by
    intro n m f
    have : Epi ((moduleAdicQuotientCone J M).π.app n) :=
      (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
    apply (cancel_epi ((moduleAdicQuotientCone J M).π.app n)).1
    rw [← Category.assoc, (moduleAdicQuotientCone J M).w f]
    rw [he, ← Category.assoc, he]
    exact (G.congr_map ((Cone.mk F (adicQuotientSystem X I F).quotientMap).w f)).symm)
  let c := G.mapCone (Cone.mk F (adicQuotientSystem X I F).quotientMap)
  have ec : (Cone.postcompose eD.hom).obj (moduleAdicQuotientCone J M) ≅ c :=
    Cone.ext (Iso.refl M) (by
      intro n
      show (moduleAdicQuotientCone J M).π.app n ≫ (e n.unop).hom =
        𝟙 M ≫ G.map ((adicQuotientSystem X I F).quotientMap.app n)
      simpa only [Category.id_comp] using he n.unop)
  constructor
  · rintro ⟨hc⟩
    apply (moduleAdicQuotientCone_isLimit_iff J M).mp
    exact ⟨(IsLimit.postcomposeHomEquiv eD _)
      (hc.ofIsoLimit ec.symm)⟩
  · intro h
    obtain ⟨hm⟩ := (moduleAdicQuotientCone_isLimit_iff J M).mpr h
    exact ⟨((IsLimit.postcomposeHomEquiv eD _).symm hm).ofIsoLimit ec⟩

/-- Ordinary completeness is derived completeness plus separatedness. -/
@[stacks 099Q "completion_criterion"]
theorem isLimit_adicQuotientSystem_iff_of_slicedObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : Stacks.WeaklyContractible.SlicedObjectsSituation.{w, v, u, max u v} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hI : ∀ U : X.C, hX.B U →
      (I.toSubmodule.obj (op U)).FG)
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Nonempty (IsLimit (Cone.mk F (adicQuotientSystem X I F).quotientMap)) ↔
      AlgebraicGeometry.RingedSite.IsDerivedComplete X I
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F) ∧
        (⨅ n : ℕ, idealPowerProduct X I F n) = ⊥ := by
  let (U : X.C) : HasProductsOfShape ℕ
      (DerivedCategory (ModuleCat.{max u v}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let J (U : X.C) : Ideal ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) :=
    I.toSubmodule.obj (op U)
  have hp (U : X.C) (hU : hX.B U) (n : ℕ) :=
    idealPowerProduct_obj_of_surjective_sections X I F U
      (fun _ _ φ hφ => hX.isWeaklyContractible hU _ _ φ hφ) (hI U hU) n
  have hi : (⨅ n : ℕ, idealPowerProduct X I F n) = ⊥ ↔
      ∀ U : X.C, hX.B U →
        (⨅ n : ℕ, J U ^ n •
          (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
            (F.val.obj (op U)))) = ⊥ := by
    rw [sheafSubmodule_eq_bot_iff_hasEnoughObjects X hX.B hX.hasEnoughObjects]
    apply forall_congr'
    intro U
    apply imp_congr_right
    intro hU
    rw [sheafSubmodule_iInf_obj]
    simp_rw [hp U hU]
    rfl
  rw [isDerivedComplete_sheaf_single_iff_sections_of_slicedObjectsSituation X hX I F, hi,
    evaluation_jointly_reflects_limit_of_weaklyContractibleObjectsSituation X
      hX.toWeaklyContractibleObjectsSituation]
  have hm (U : X.C) (hU : hX.B U) :=
    evaluation_adicQuotientCone_isLimit_iff_of_weaklyContractibleObjectsSituation X
      hX.toWeaklyContractibleObjectsSituation I F U hU (hp U hU)
  have hc (U : X.C) (hU : hX.B U) :=
    isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (J U) (hI U hU)
      (F.val.obj (op U))
  constructor
  · intro h
    exact ⟨fun U hU => ((hc U hU).mp ((hm U hU).mp (h U hU))).1,
      fun U hU => ((hc U hU).mp ((hm U hU).mp (h U hU))).2⟩
  · rintro ⟨hd, hs⟩ U hU
    exact (hm U hU).mpr ((hc U hU).mpr ⟨hd U hU, hs U hU⟩)

private lemma sheafSubmodule_top_toSubmodule
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {F : SheafOfModules.{v} R} :
    (⊤ : F.Submodule).toSubmodule = ⊤ := by
  rw [← sInf_empty (α := F.Submodule), SheafOfModules.Submodule.toSubmodule_sInf]
  simp

private lemma sheafSubmodule_top_obj
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {F : SheafOfModules.{v} R} (U : Cᵒᵖ) :
    (⊤ : F.Submodule).toSubmodule.obj U = ⊤ := by
  rw [sheafSubmodule_top_toSubmodule]
  simp

/-- **Stacks 09BY.** A sheaf of modules on a ringed site with enough weakly contractible
objects which is derived complete along a sheaf of ideals and satisfies `IF = F`, that is
whose adic quotient `F/IF` vanishes, is zero. The sheaf of ideals is assumed finitely
generated on sections over the weakly contractible objects.

This generalizes the content of the tag, whose site is `X_proétale` and whose coefficients are a
constant ring `Λ` with a finitely generated ideal `I`: the site here is any ringed site with
enough weakly contractible objects, `I` is any sheaf of ideals, and the finite-generation
requirement is *weaker* than the source's, being asked only on sections over weakly contractible
objects.

The weakly contractible objects enter only through the bundle `hX`, whose members test
surjectivity of sheaves of sets valued in the *module* universe `max u v`, on the site and on
each of its slice sites. That is what makes the statement readable at a site whose objects
outnumber its morphisms. The small pro-étale site of a scheme is such a site: it is a
`RingedSite.{u + 1, u, _}` — for instance
`AlgebraicGeometry.ProEtale.constantCoefficientRingedSite`, which is `X_proétale` ringed by the
constant sheaf `Λ̲` — and its weak contractibility cannot be tested at the morphism universe `u`
at all, since `Small.{u} X.ProEt` is false: the objects of `X.ProEt` lie in `Type (u + 1)` and
the site is small, and essentially small, only at `u + 1`. -/
@[stacks 09BY "generalized to a ringed site with a covering collection of objects testing \
surjectivity of sheaves of sets in the module universe, on the site and on its slices, and to \
an arbitrary sheaf of ideals; the Small and HasSheafify hypotheses that used to exclude the \
pro-etale site are gone, but the sliced bundle is not yet constructed for that site, so the \
pro-etale site is still NOT an instance of this statement"]
theorem isZero_of_isDerivedComplete_of_idealProduct_eq_top_of_slicedObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : Stacks.WeaklyContractible.SlicedObjectsSituation.{w, v, u, max u v} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hI : ∀ U : X.C, hX.B U →
      (I.toSubmodule.obj (op U)).FG)
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))
    (hIF : idealPowerProduct X I F 1 = ⊤) :
    IsZero F := by
  have key : ∀ U : X.C, hX.B U →
      (⊤ : F.Submodule).toSubmodule.obj (op U) = ⊥ := by
    intro U hU
    let : HasProductsOfShape ℕ
        (DerivedCategory (ModuleCat.{max u v}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    have hsmul : idealSections X I (op U) •
        (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
          (F.val.obj (op U))) = ⊤ := by
      have h := idealPowerProduct_obj_eq_pow_smul_top_of_surjective_sections X I F U
        (fun _ _ φ hφ => hX.isWeaklyContractible hU _ _ φ hφ) (hI U hU) 1
      rw [hIF, sheafSubmodule_top_obj, pow_one] at h
      exact h.symm
    have hcomplete : IsDerivedCompleteModule
        (idealSections X I (op U))
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).obj F) :=
      (isDerivedComplete_sheaf_single_iff_sections_of_slicedObjectsSituation X hX I F).mp hF U hU
    have hsub : Subsingleton
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).obj F) :=
      subsingleton_of_isDerivedCompleteModule_of_quotient_smul
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) (idealSections X I (op U))
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).obj F)
        (hI U hU) hcomplete
        (Submodule.Quotient.subsingleton_iff.mpr hsmul)
    refine le_bot_iff.mp fun x _ ↦ ?_
    show x = 0
    exact Subsingleton.elim
      (α := (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).obj F)
      x 0
  have hall : ∀ U : X.Cᵒᵖ, (⊤ : F.Submodule).toSubmodule.obj U = ⊥ :=
    (sheafSubmodule_eq_bot_iff (⊤ : F.Submodule)).mp
      ((sheafSubmodule_eq_bot_iff_hasEnoughObjects X hX.B hX.hasEnoughObjects
        (⊤ : F.Submodule)).mpr key)
  rw [IsZero.iff_id_eq_zero]
  ext U m
  show m = 0
  have hm : m ∈ (⊤ : F.Submodule).toSubmodule.obj U := by
    rw [sheafSubmodule_top_obj]
    exact Submodule.mem_top
  rw [hall U] at hm
  exact hm

/-! ### The statements on a site with enough weakly contractible objects

A `Type v`-small site with enough weakly contractible objects supplies the bundles the
statements above consume, by `Stacks.WeaklyContractible.SlicedObjectsSituation.of` applied to
the testing family of all weakly contractible objects; these are the resulting statements, in
the form that only mentions `CategoryTheory.GrothendieckTopology.IsWeaklyContractible`. -/

private theorem isDerivedComplete_sheaf_single_iff_sections
    (X : RingedSite.{u, v, max u v})
    [Small.{v} X.C] [HasSheafify X.J (Type v)]
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F) ↔
      ∀ U : X.C, X.J.IsWeaklyContractible U →
        let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
        letI : IsMulCommutative R := by
          change IsMulCommutative (X.O.obj.obj (op U))
          infer_instance
        letI : CommRing R := inferInstance
        let J : Ideal R := by
          change Submodule R R
          exact I.toSubmodule.obj (op U)
        let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
        letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)) :=
          Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
        IsDerivedCompleteModule J (G.obj F) :=
  isDerivedComplete_sheaf_single_iff_sections_of_slicedObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of
      ⟨fun U => X.J.IsWeaklyContractible U, fun {_} hU => hU, hX⟩
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I F

private theorem evaluation_jointly_reflects_iso
    (X : RingedSite.{u, v, max u v}) [Small.{v} X.C]
    [HasSheafify X.J (Type v)]
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    {F G : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : F ⟶ G)
    (hf : ∀ U : X.C, X.J.IsWeaklyContractible U →
      Function.Bijective
        ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).map f)) :
    IsIso f :=
  evaluation_jointly_reflects_iso_of_weaklyContractibleObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of
      ⟨fun U => X.J.IsWeaklyContractible U, fun {_} hU => hU, hX⟩
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).toWeaklyContractibleObjectsSituation f hf

private theorem evaluation_jointly_reflects_limit
    (X : RingedSite.{u, v, max u v}) [Small.{v} X.C]
    [HasSheafify X.J (Type v)]
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    (D : ℕᵒᵖ ⥤ SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (c : Cone D) :
    Nonempty (IsLimit c) ↔ ∀ U : X.C, X.J.IsWeaklyContractible U →
      Nonempty (IsLimit ((SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).mapCone c)) :=
  evaluation_jointly_reflects_limit_of_weaklyContractibleObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of
      ⟨fun U => X.J.IsWeaklyContractible U, fun {_} hU => hU, hX⟩
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).toWeaklyContractibleObjectsSituation D c

private lemma exists_sections_refinement
    {C : Type u} [Category.{v} C] [Small.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type v)]
    (U : C) (hU : J.IsWeaklyContractible U)
    {ι : Type v} (V : ι → C) (f : ∀ i, V i ⟶ U)
    (hcov : Sieve.ofArrows V f ∈ J U)
    {κ : Type*} (F : κ → Sheaf J (Type (max u v)))
    (x : ∀ k i, (F k).obj.obj (op (V i))) :
    ∃ y : ∀ k, (F k).obj.obj (op U), ∃ S : Sieve U,
      S ∈ J U ∧ ∀ (W : C) (g : W ⟶ U), S g →
        ∃ i, ∃ a : W ⟶ V i, a ≫ f i = g ∧
          ∀ k, (F k).obj.map g.op (y k) = (F k).obj.map a.op (x k i) := by
  have hcov' : Sieve.ofArrows (fun i : ULift.{u} ι => V i.down)
      (fun i : ULift.{u} ι => f i.down) ∈ J U := by
    refine J.superset_covering (fun W g hg => ?_) hcov
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨i, a, rfl⟩ := hg
    have hmk := Sieve.ofArrows_mk (fun i : ULift.{u} ι => V i.down)
      (fun i : ULift.{u} ι => f i.down) (ULift.up i)
    exact (Sieve.ofArrows _ _).downward_closed hmk a
  obtain ⟨y, S, hS, hrefine⟩ :=
    exists_sections_refinement_of_surjective_sections J U
      (fun A B φ hφ =>
        Stacks.WeaklyContractible.surjective_sections_of_isWeaklyContractible.{max u v}
          J U hU A B φ hφ)
      (fun i : ULift.{u} ι => V i.down) (fun i : ULift.{u} ι => f i.down) hcov' F
      (fun k i => x k i.down)
  refine ⟨y, S, hS, fun W g hg => ?_⟩
  obtain ⟨i, a, ha, hk⟩ := hrefine W g hg
  exact ⟨i.down, a, ha, hk⟩

private lemma idealPowerProduct_obj_of_weaklyContractible
    (X : RingedSite.{u, v, max u v}) [Small.{v} X.C]
    [HasSheafify X.J (Type v)]
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (hU : X.J.IsWeaklyContractible U)
    (hI : (I.toSubmodule.obj (op U)).FG) (n : ℕ) :
    (idealPowerProduct X I F n).toSubmodule.obj (op U) =
      (idealPowerActionPresheaf X I F n).obj (op U) :=
  idealPowerProduct_obj_of_surjective_sections X I F U
    (fun A B φ hφ =>
      Stacks.WeaklyContractible.surjective_sections_of_isWeaklyContractible.{max u v}
        X.J U hU A B φ hφ) hI n

private lemma idealPowerProduct_obj_eq_pow_smul_top
    (X : RingedSite.{u, v, max u v}) [Small.{v} X.C]
    [HasSheafify X.J (Type v)]
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (hU : X.J.IsWeaklyContractible U)
    (hI : (I.toSubmodule.obj (op U)).FG) (n : ℕ) :
    letI : IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) := by
      change IsMulCommutative (X.O.obj.obj (op U))
      infer_instance
    letI : Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
        (F.val.obj (op U)) :=
      (F.val.obj (op U)).isModule
    (idealPowerProduct X I F n).toSubmodule.obj (op U) =
      idealSections X I (op U) ^ n •
        (⊤ : Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
          (F.val.obj (op U))) :=
  idealPowerProduct_obj_of_weaklyContractible X I F U hU hI n

private lemma sheafSubmodule_eq_bot_iff_weaklyContractible
    (X : RingedSite.{u, v, max u v}) [Small.{v} X.C]
    [HasSheafify X.J (Type v)]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    {F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (N : F.Submodule) :
    N = ⊥ ↔ ∀ U : X.C, X.J.IsWeaklyContractible U →
      N.toSubmodule.obj (op U) = ⊥ :=
  sheafSubmodule_eq_bot_iff_hasEnoughObjects X (fun U => X.J.IsWeaklyContractible U) hX N

private lemma evaluation_cokernel_submodule
    (X : RingedSite.{u, v, max u v}) [Small.{v} X.C]
    [HasSheafify X.J (Type v)]
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    (U : X.C) (hU : X.J.IsWeaklyContractible U)
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (N : F.Submodule) :
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    ∃ e : ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
        (G.obj F ⧸ N.toSubmodule.obj (op U)) ≅ G.obj (cokernel N.ι),
      ModuleCat.ofHom (N.toSubmodule.obj (op U)).mkQ ≫ e.hom =
        G.map (cokernel.π N.ι) :=
  evaluation_cokernel_submodule_of_weaklyContractibleObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of
      ⟨fun U => X.J.IsWeaklyContractible U, fun {_} hU => hU, hX⟩
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).toWeaklyContractibleObjectsSituation U hU F N

private lemma evaluation_adicQuotientCone_isLimit_iff
    (X : RingedSite.{u, v, max u v}) [Small.{v} X.C]
    [HasSheafify X.J (Type v)]
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (hU : X.J.IsWeaklyContractible U)
    (hpow : ∀ n, (idealPowerProduct X I F n).toSubmodule.obj (op U) =
      (idealPowerActionPresheaf X I F n).obj (op U)) :
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)
    letI : IsMulCommutative R := by
      change IsMulCommutative (X.O.obj.obj (op U)); infer_instance
    let J : Ideal R := I.toSubmodule.obj (op U)
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    Nonempty (IsLimit (G.mapCone
      (Cone.mk F (adicQuotientSystem X I F).quotientMap))) ↔ IsAdicComplete J (G.obj F) :=
  evaluation_adicQuotientCone_isLimit_iff_of_weaklyContractibleObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of
      ⟨fun U => X.J.IsWeaklyContractible U, fun {_} hU => hU, hX⟩
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).toWeaklyContractibleObjectsSituation
    I F U hU hpow

/-- Ordinary completeness is derived completeness plus separatedness. -/
@[stacks 099Q "completion_criterion"]
theorem isLimit_adicQuotientSystem_iff
    (X : RingedSite.{u, v, max u v})
    [Small.{v} X.C] [HasSheafify X.J (Type v)]
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hI : ∀ U : X.C, X.J.IsWeaklyContractible U →
      (I.toSubmodule.obj (op U)).FG)
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Nonempty (IsLimit (Cone.mk F (adicQuotientSystem X I F).quotientMap)) ↔
      AlgebraicGeometry.RingedSite.IsDerivedComplete X I
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F) ∧
        (⨅ n : ℕ, idealPowerProduct X I F n) = ⊥ :=
  isLimit_adicQuotientSystem_iff_of_slicedObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of
      ⟨fun U => X.J.IsWeaklyContractible U, fun {_} hU => hU, hX⟩
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I hI F

/-- **Stacks 09BY.** A sheaf of modules on a ringed site with enough weakly contractible
objects which is derived complete along a sheaf of ideals and satisfies `IF = F`, that is
whose adic quotient `F/IF` vanishes, is zero. The sheaf of ideals is assumed finitely
generated on sections over the weakly contractible objects. -/
@[stacks 09BY]
theorem isZero_of_isDerivedComplete_of_idealProduct_eq_top
    (X : RingedSite.{u, v, max u v}) [Small.{v} X.C]
    [HasSheafify X.J (Type v)]
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hI : ∀ U : X.C, X.J.IsWeaklyContractible U →
      (I.toSubmodule.obj (op U)).FG)
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))
    (hIF : idealPowerProduct X I F 1 = ⊤) :
    IsZero F :=
  isZero_of_isDerivedComplete_of_idealProduct_eq_top_of_slicedObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of
      ⟨fun U => X.J.IsWeaklyContractible U, fun {_} hU => hU, hX⟩
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I hI F hF hIF

/-! ### Sections over the testing objects -/

/-- **Derived completeness of a sheaf of modules is read off its sections** over the members of
a covering collection of objects which test surjectivity of sheaves of sets in the module
universe, on the site and on its slices: `ℱ`, placed in degree zero, is derived complete along
`ℐ` exactly when, for every member `U` of the collection, the module `Γ(U, ℱ)` is derived
complete along the ideal `Γ(U, ℐ)` of `Γ(U, 𝒪)`. -/
alias isDerivedComplete_single_iff_sections_of_slicedObjectsSituation := isDerivedComplete_sheaf_single_iff_sections_of_slicedObjectsSituation

/-- **A sheaf of modules killed locally by powers of the sections of `ℐ` is derived complete.**
If, over every member `U` of a covering collection of weakly contractible objects, every section
`f` of `ℐ` has a power `fⁿ` acting as zero on `Γ(U, ℱ)`, then `ℱ`, placed in degree zero, is
derived complete along `ℐ`: on sections over `U` multiplication by `f` is nilpotent. -/
theorem isDerivedComplete_single_of_pow_smul_eq_zero_of_slicedObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (h : Stacks.WeaklyContractible.SlicedObjectsSituation.{w, v, u, max u v} X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : ∀ U : X.C, h.B U → ∀ f : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U),
      f ∈ I.toSubmodule.obj (op U) → ∃ n : ℕ, ∀ x : F.val.obj (op U), f ^ n • x = 0) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F) := by
  refine (isDerivedComplete_sheaf_single_iff_sections_of_slicedObjectsSituation X h I F).2
    fun U hU => ?_
  intro R J G f hf
  obtain ⟨n, hn⟩ := hF U hU f hf
  rw [DerivedCompleteRecurrence.isDerivedCompleteAt_single_iff_bijective_recurrence,
    ← DerivedCompleteRecurrence.isIso_oneSubSmulShift_moduleCat_iff,
    ← isDerivedCompleteAt_iff_isIso]
  refine isDerivedCompleteAt_of_isNilpotent ⟨n, ?_⟩
  rw [smul_id_pow]
  apply ModuleCat.hom_ext
  ext x
  exact hn x

/-- Over an object on which locally surjective maps of sheaves of sets are surjective, and over
which the ideal of sections is finitely generated, the sections of `IⁿF` are the products of the
`n`-th power of that ideal with the sections of `F`. -/
alias idealPowerProduct_obj_eq_pow_smul_top_of_sections_surjective := idealPowerProduct_obj_eq_pow_smul_top_of_surjective_sections

/-- Over a testing object of a weakly contractible situation, the sections of the quotient of a
sheaf of modules by a subsheaf are the quotient of the sections, compatibly with the projection. -/
alias exists_evaluation_cokernel_iso_of_weaklyContractibleObjectsSituation := evaluation_cokernel_submodule_of_weaklyContractibleObjectsSituation

end AlgebraicGeometry.RingedSite

end
