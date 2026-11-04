module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Adequate functors

A module-valued functor on the commutative algebras over a ring `A` is *adequate* when it is
the kernel of a map of finitely presented free module-valued functors, and *linearly adequate*
when it is such a kernel for a map of finite free ones.  This file sets up the ambient
categories, the base-change functor on module-valued functors, and the two predicates with
their unfolding lemmas.

A module-valued functor in the sense of Stacks 06Z4 — a functor `Alg_A → Ab` whose value at `B`
is endowed with a `B`-module structure and whose transition maps are `B`-linear — is exactly an
object of `ModuleValuedFunctor A`, the presheaves of modules over the tautological ring-valued
functor on `Alg_A`; and a morphism of module-valued functors is exactly a morphism there. So
that tag is recorded against `ModuleValuedFunctor` rather than restated.

## References

* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
* [Stacks Project, Tag 06Z4](https://stacks.math.columbia.edu/tag/06Z4)
-/

@[expose] public section

namespace AdequateFunctor

section

open CategoryTheory CategoryTheory.Limits

universe w' w v u v₁ u₁


/-- The tautological presheaf of commutative rings on the opposite of the category of
commutative `A`-algebras in a universe containing the base ring. -/
public abbrev algebraRingDiagram (A : Type u) [CommRing A] :
    ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ ⥤ RingCat.{max u v} :=
  unopUnop (CommAlgCat.{max u v} A) ⋙ forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v} ⋙
    forget₂ CommRingCat.{max u v} RingCat.{max u v}

/-- Module-valued functors on the category of commutative `A`-algebras. The values may live in
a universe independent of the algebra carriers. -/
public abbrev ModuleValuedFunctor (A : Type u) [CommRing A] :=
  PresheafOfModules.{w} (algebraRingDiagram.{v} A)

/-- The algebras allowed by the chosen category of schemes in Tag 06Z3. For the big sites
of Tag 03XB, `P` is their `Contains` predicate, namely `X.size < κ`. -/
public abbrev algebraInSite (A : Type u) [CommRing A]
    (P : ObjectProperty AlgebraicGeometry.Scheme.{max u v}) :
    ObjectProperty (CommAlgCat.{max u v} A) :=
  fun B => P (AlgebraicGeometry.Spec (CommRingCat.of B))

/-- The source's category `Alg_A`: the full subcategory of algebras whose spectra belong
to the chosen big site. -/
public abbrev AlgebrasInSite (A : Type u) [CommRing A]
    (P : ObjectProperty AlgebraicGeometry.Scheme.{max u v}) :=
  (algebraInSite A P).FullSubcategory

/-- Forget the condition that the spectrum belongs to the chosen site. -/
public abbrev siteAlgebraInclusion (A : Type u) [CommRing A]
    (P : ObjectProperty AlgebraicGeometry.Scheme.{max u v}) :
    AlgebrasInSite A P ⥤ CommAlgCat.{max u v} A := (algebraInSite A P).ι

/-- Taking spectra of the allowed algebras lands in the chosen category of schemes. -/
public noncomputable def spectrumInSite (A : Type u) [CommRing A]
    (P : ObjectProperty AlgebraicGeometry.Scheme.{max u v}) :
    (AlgebrasInSite A P)ᵒᵖ ⥤ P.FullSubcategory where
  obj B := ⟨AlgebraicGeometry.Spec (CommRingCat.of B.unop.obj), B.unop.property⟩
  map f := ObjectProperty.homMk
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom))
  map_id B := by
    apply ObjectProperty.hom_ext
    exact AlgebraicGeometry.Spec.map_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact AlgebraicGeometry.Spec.map_comp
      (CommRingCat.ofHom g.unop.hom.hom.toRingHom)
      (CommRingCat.ofHom f.unop.hom.hom.toRingHom)

/-- The scalar rings on any chosen domain of `A`-algebras. In the source, `ι` is
`siteAlgebraInclusion A P`; the identity also permits purely algebraic applications. -/
public abbrev algebraRingDiagramOn {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{max u v} A) :=
  ι.op.op ⋙ algebraRingDiagram.{v} A

/-- Module-valued functors defined only on the chosen domain of algebras. -/
public abbrev ModuleValuedFunctorOn {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{max u v} A) :=
  PresheafOfModules.{w} (algebraRingDiagramOn ι)

/-- Every map of presheaves of modules has a kernel. Supplied as a direct instance
reducing to `PresheafOfModules.hasLimitsOfShape`: reached instead through the abelian
structure, the search is quadratic in the ambient `HasLimit` instances and times out at
the independent universes used for module-valued functors. -/
public instance hasKernel_presheafOfModules {C : Type u₁} [Category.{v₁} C]
    {R : Cᵒᵖ ⥤ RingCat.{w'}} {F G : PresheafOfModules.{w} R} (g : F ⟶ G) :
    HasLimit (parallelPair g 0) :=
  have h : HasLimitsOfShape WalkingParallelPair (PresheafOfModules.{w} R) :=
    PresheafOfModules.hasLimitsOfShape _ _
  h.has_limit _

section UniverseLift

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

/-- Raise the value universe of a presheaf of modules without changing its scalars. -/
@[implicit_reducible]
public noncomputable def presheafOfModulesUlift (F : PresheafOfModules.{w} R) :
    PresheafOfModules.{max w w'} R where
  obj X := (ModuleCat.uliftFunctor.{w'} (R.obj X)).obj (F.obj X)
  map {X Y} f := (ModuleCat.uliftFunctor.{w'} (R.obj X)).map (F.map f)
  map_id X := by
    ext x
    exact congrArg ULift.up (CategoryTheory.congr_fun (F.map_id X) x.down)
  map_comp f g := by
    ext x
    exact congrArg ULift.up (F.map_comp_apply f g x.down)

/-- The fully faithful change of value universe for presheaves of modules. -/
@[implicit_reducible]
public noncomputable def presheafOfModulesUliftFunctor :
    PresheafOfModules.{w} R ⥤ PresheafOfModules.{max w w'} R where
  obj := presheafOfModulesUlift.{w'} R
  map f :=
    { app X := (ModuleCat.uliftFunctor.{w'} (R.obj X)).map (f.app X)
      naturality g := by
        ext x
        exact congrArg ULift.up (PresheafOfModules.naturality_apply f g x.down) }

/-- The restriction maps of `presheafOfModulesUlift R F` are those of `F` on the underlying
elements. -/
@[simp]
public lemma presheafOfModulesUlift_map_apply (F : PresheafOfModules.{w} R)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : ULift.{w'} (F.obj X)) :
    ((presheafOfModulesUlift.{w'} R F).map f x).down = F.map f x.down := rfl

/-- The components of `(presheafOfModulesUliftFunctor R).map f` are those of `f` on the
underlying elements. -/
@[simp]
public lemma presheafOfModulesUliftFunctor_map_app_apply
    {F G : PresheafOfModules.{w} R} (f : F ⟶ G) (X : Cᵒᵖ)
    (x : ULift.{w'} (F.obj X)) :
    (((presheafOfModulesUliftFunctor.{w'} R).map f).app X x).down =
      f.app X x.down := rfl

/-- Raising the value universe loses neither morphisms nor their naturality. -/
public noncomputable def fullyFaithfulPresheafOfModulesUliftFunctor :
    (presheafOfModulesUliftFunctor.{w', w} R).FullyFaithful where
  preimage f :=
    { app X := (ModuleCat.fullyFaithfulUliftFunctor (R.obj X)).preimage (f.app X)
      naturality g := by
        ext x
        exact congrArg ULift.down
          (PresheafOfModules.naturality_apply f g (ULift.up x)) }
  map_preimage f := by ext X x; rfl
  preimage_map f := by ext X x; rfl

/-- Raising the value universe of presheaves of modules is a full functor. -/
public instance : (presheafOfModulesUliftFunctor.{w', w} R).Full :=
  (fullyFaithfulPresheafOfModulesUliftFunctor R).full

/-- Raising the value universe of presheaves of modules is a faithful functor. -/
public instance : (presheafOfModulesUliftFunctor.{w', w} R).Faithful :=
  (fullyFaithfulPresheafOfModulesUliftFunctor R).faithful

/-- Raising the value universe of presheaves of modules is an additive functor. -/
public instance : (presheafOfModulesUliftFunctor.{w', w} R).Additive where
  map_add := by intros; ext X x; rfl

/-- When the values already lie in the larger universe, their lift is naturally isomorphic
to the original presheaf. -/
@[implicit_reducible]
public noncomputable def presheafOfModulesUliftIso (F : PresheafOfModules.{max w w'} R) :
    (presheafOfModulesUliftFunctor.{w', max w w'} R).obj F ≅ F :=
  PresheafOfModules.isoMk
    (fun X ↦ (ULift.moduleEquiv : ULift.{w'} (F.obj X) ≃ₗ[R.obj X] F.obj X).toModuleIso)
    (by intros; ext x; rfl)

end UniverseLift

/-- Extension of scalars on tensor products along a morphism of `A`-algebras. -/
@[implicit_reducible]
public noncomputable def moduleExtensionMap (A : Type u) [CommRing A]
    (M : ModuleCat.{w} A) {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) :
    ModuleCat.of B (TensorProduct A (B : Type (max u v)) M) ⟶
      (ModuleCat.restrictScalars f.hom.toRingHom).obj
        (ModuleCat.of C (TensorProduct A (C : Type (max u v)) M)) := by
  refine ModuleCat.ofHom
    (X := ModuleCat.of B (TensorProduct A (B : Type (max u v)) M))
    (Y := (ModuleCat.restrictScalars f.hom.toRingHom).obj
      (ModuleCat.of C (TensorProduct A (C : Type (max u v)) M)))
    { toFun := TensorProduct.map f.hom.toLinearMap LinearMap.id
      map_add' := map_add _
      map_smul' := ?_ }
  intro b x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul c m =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul]
    change f.hom (b * c) ⊗ₜ[A] m = (f.hom b * f.hom c) ⊗ₜ[A] m
    rw [map_mul]
  | add x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add]
    exact (smul_add b _ _).symm

/-- Extension of scalars along the identity algebra morphism agrees with the canonical
restriction-of-scalars identification. -/
public lemma moduleExtensionMap_id (A : Type u) [CommRing A]
    (M : ModuleCat.{w} A) (B : CommAlgCat.{max u v} A) :
    moduleExtensionMap.{w, v} A M (𝟙 B) =
      (ModuleCat.restrictScalarsId' (𝟙 B : B ⟶ B).hom.toRingHom
        (congrArg CommRingCat.Hom.hom
          ((forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}).map_id B))).inv.app _ := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul b m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The module-valued functor `B ↦ B ⊗[A] M` associated to an `A`-module `M`. -/
@[implicit_reducible]
public noncomputable def moduleExtension (A : Type u) [CommRing A]
    (M : ModuleCat.{w} A) : ModuleValuedFunctor.{max u v w, v} A where
  obj X := ModuleCat.of X.unop.unop (TensorProduct A (X.unop.unop : Type (max u v)) M)
  map {X Y} f := moduleExtensionMap.{w, v} A M f.unop.unop
  map_id X := moduleExtensionMap_id.{w, v} A M X.unop.unop
  map_comp f g := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul b m => rfl
    | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Base change of a linear map, as a morphism between its associated module-valued functors. -/
@[implicit_reducible]
public noncomputable def moduleExtensionHom (A : Type u) [CommRing A]
    {M N : ModuleCat.{w} A} (f : M ⟶ N) : moduleExtension.{w, v} A M ⟶
      moduleExtension.{w, v} A N where
  app X := ModuleCat.ofHom (f.hom.baseChange X.unop.unop)
  naturality := by
    intro X Y g
    ext x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul b m => rfl
    | add x y hx hy =>
      convert congrArg₂ (· + ·) hx hy using 1 <;> apply map_add

/-- The restriction map of `moduleExtension A M` along `f` sends `b ⊗ₜ m` to
`f.unop.unop.hom b ⊗ₜ m`. -/
@[simp↓]
public lemma moduleExtension_map_tmul (A : Type u) [CommRing A]
    (M : ModuleCat.{w} A) {X Y : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ} (f : X ⟶ Y)
    (b : X.unop.unop) (m : M) :
    (moduleExtension.{w, v} A M).map f (b ⊗ₜ[A] m) = f.unop.unop.hom b ⊗ₜ[A] m := rfl

/-- Extension of scalars from `A`-modules to module-valued functors on `A`-algebras. -/
@[implicit_reducible]
public noncomputable def moduleExtensionFunctor (A : Type u) [CommRing A] :
    ModuleCat.{w} A ⥤ ModuleValuedFunctor.{max u v w, v} A where
  obj M := moduleExtension.{w, v} A M
  map f := moduleExtensionHom.{w, v} A f
  map_id M := by
    ext B x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul b m => rfl
    | add x y hx hy =>
      convert congrArg₂ (· + ·) hx hy using 1 <;> apply map_add
  map_comp f g := by
    ext B x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul b m => rfl
    | add x y hx hy =>
      convert congrArg₂ (· + ·) hx hy using 1 <;> apply map_add

/-- The components of `(moduleExtensionFunctor A).map f` send `b ⊗ₜ m` to `b ⊗ₜ f.hom m`. -/
@[simp↓]
public lemma moduleExtensionFunctor_map_app_tmul (A : Type u) [CommRing A]
    {M N : ModuleCat.{w} A} (f : M ⟶ N) (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ)
    (b : X.unop.unop) (m : M) :
    ((moduleExtensionFunctor.{w, v} A).map f).app X (b ⊗ₜ[A] m) = b ⊗ₜ[A] f.hom m := rfl

/-- Evaluation of a module extension at the lifted base algebra recovers the module. -/
public noncomputable def moduleExtensionAtBaseEquiv {A : Type u} [CommRing A]
    (M : ModuleCat.{w} A) :
    TensorProduct A (ULift.{v} A) M ≃ₗ[A] M :=
  (TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl A M)).trans
    (TensorProduct.lid A M)

/-- Evaluation at the lifted base algebra sends a pure tensor to scalar multiplication. -/
@[simp] public lemma moduleExtensionAtBaseEquiv_tmul {A : Type u} [CommRing A]
    (M : ModuleCat.{w} A) (a : ULift.{v} A) (m : M) :
    moduleExtensionAtBaseEquiv M (a ⊗ₜ[A] m) = a.down • m := rfl

/-- The inverse evaluation map sends a module element to its tensor with one. -/
@[simp] public lemma moduleExtensionAtBaseEquiv_symm_apply {A : Type u} [CommRing A]
    (M : ModuleCat.{w} A) (m : M) :
    (moduleExtensionAtBaseEquiv.{w, v} M).symm m = (1 : ULift.{v} A) ⊗ₜ[A] m := rfl

/-- Recover the underlying module map by evaluating at the lifted base algebra. -/
public noncomputable def moduleHomOfExtensionNatTrans {A : Type u} [CommRing A]
    {M N : ModuleCat.{w} A} (η : moduleExtension.{w, v} A M ⟶ moduleExtension.{w, v} A N) :
    M ⟶ N := by
  let t : TensorProduct A (ULift.{v} A) M →ₗ[ULift.{v} A]
      TensorProduct A (ULift.{v} A) N :=
    (η.app (Opposite.op (Opposite.op (CommAlgCat.of A (ULift.{v} A))))).hom
  exact ModuleCat.ofHom ((moduleExtensionAtBaseEquiv N).toLinearMap.comp
    ((t.restrictScalars A).comp (moduleExtensionAtBaseEquiv M).symm.toLinearMap))

/-- Every morphism between module extensions is the base change of a module map. -/
public lemma moduleExtension_natTrans_eq_map {A : Type u} [CommRing A]
    {M N : ModuleCat.{w} A} (η : moduleExtension.{w, v} A M ⟶ moduleExtension.{w, v} A N) :
    η = (moduleExtensionFunctor.{w, v} A).map (moduleHomOfExtensionNatTrans η) := by
  ext X x
  let g : CommAlgCat.of A (ULift.{v} A) ⟶ X.unop.unop :=
    CommAlgCat.ofHom ((Algebra.ofId A X.unop.unop).comp ULift.algEquiv.toAlgHom)
  have hbase (z : TensorProduct A (ULift.{v} A) N) :
      (moduleExtension.{w, v} A N).map g.op.op z =
        (1 : X.unop.unop) ⊗ₜ[A] moduleExtensionAtBaseEquiv N z := by
    induction z using TensorProduct.induction_on with
    | zero => change (0 : TensorProduct A X.unop.unop N) = 1 ⊗ₜ[A] 0; simp
    | tmul a n =>
      show algebraMap A X.unop.unop a.down ⊗ₜ[A] n = 1 ⊗ₜ[A] (a.down • n)
      rw [← TensorProduct.smul_tmul]
      simp [Algebra.smul_def]
    | add z t hz ht =>
      simp only [map_add, hz, ht, TensorProduct.tmul_add]
      rfl
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    have hn := PresheafOfModules.naturality_apply η g.op.op ((1 : ULift.{v} A) ⊗ₜ[A] m)
    have hg : (moduleExtension.{w, v} A M).map g.op.op ((1 : ULift.{v} A) ⊗ₜ[A] m) =
        (1 : X.unop.unop) ⊗ₜ[A] m := by
      show g.hom 1 ⊗ₜ[A] m = 1 ⊗ₜ[A] m
      rw [map_one]
    rw [hg, hbase] at hn
    have ht : b • ((1 : X.unop.unop) ⊗ₜ[A] m) = b ⊗ₜ[A] m := by
      rw [TensorProduct.smul_tmul']
      simp
    rw [← ht, (η.app X).hom.map_smul, hn]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Recovering the module map inverts extension of scalars on morphisms. -/
public lemma moduleHomOfExtensionNatTrans_map {A : Type u} [CommRing A]
    {M N : ModuleCat.{w} A} (f : M ⟶ N) :
    moduleHomOfExtensionNatTrans ((moduleExtensionFunctor.{w, v} A).map f) = f := by
  ext m
  show (1 : A) • f.hom m = f.hom m
  exact one_smul A _

/-- Extension of scalars to module-valued functors is fully faithful. -/
public noncomputable def fullyFaithfulModuleExtensionFunctor (A : Type u) [CommRing A] :
    (moduleExtensionFunctor.{w, v} A).FullyFaithful where
  preimage := moduleHomOfExtensionNatTrans
  map_preimage η := (moduleExtension_natTrans_eq_map η).symm
  preimage_map := moduleHomOfExtensionNatTrans_map

/-- Extension of scalars to module-valued functors is a full functor. -/
public instance (A : Type u) [CommRing A] : (moduleExtensionFunctor.{w, v} A).Full :=
  (fullyFaithfulModuleExtensionFunctor A).full

/-- Extension of scalars to module-valued functors is a faithful functor. -/
public instance (A : Type u) [CommRing A] : (moduleExtensionFunctor.{w, v} A).Faithful :=
  (fullyFaithfulModuleExtensionFunctor A).faithful

/-- Extension of scalars to module-valued functors is an additive functor. -/
public instance (A : Type u) [CommRing A] : (moduleExtensionFunctor.{w, v} A).Additive where
  map_add := by
    intro M N f g
    ext X x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m => exact TensorProduct.tmul_add b (f.hom m) (g.hom m)
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Mathlib's `ModuleCat.extendScalars` presents its left tensor factor as `B` with the
`A`-action restricted along `algebraMap A B`, where scalar multiplication by `a` is
multiplication by `algebraMap A B a`.  That is compatible with `B`'s own multiplication. -/
public instance isScalarTower_restrictScalars_self {A : Type u} [CommRing A] {B : Type w'}
    [CommRing B] [Algebra A B] :
    IsScalarTower A B
      ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type w') :=
  IsScalarTower.of_algebraMap_smul fun a x =>
    (ModuleCat.restrictScalars.smul_def (algebraMap A B) a x).symm

/-- Restricting scalars along `algebraMap A B` leaves the `B`-module `B` unchanged: the
identity is a `B`-linear equivalence onto it.

Stated rather than left to `LinearEquiv.refl`, which would identify the two sides *with
their instance arguments* and so force the `A`-module structure of the restriction to be
the algebra's own — an identification only `ModuleCat.restrictScalars` unfolding provides. -/
public noncomputable def restrictScalarsSelfEquiv (A : Type u) [CommRing A] (B : Type w')
    [CommRing B] [Algebra A B] :
    B ≃ₗ[B] ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type w') where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of extension at an algebra agrees with Mathlib's extension of scalars. -/
public noncomputable def moduleExtensionEvaluationIso (A : Type u) [CommRing A]
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) :
    moduleExtensionFunctor.{max u v w, v} A ⋙
      PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X ≅
    ModuleCat.extendScalars.{u, max u v, max u v w}
      (R := A) (S := X.unop.unop) (algebraMap A X.unop.unop) := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · exact (TensorProduct.AlgebraTensorModule.congr (R := A) (A := (X.unop.unop : Type max u v))
      (restrictScalarsSelfEquiv A (X.unop.unop : Type max u v))
      (LinearEquiv.refl A M)).toModuleIso
  · intro M N f
    ext x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul b m => rfl
    | add x y hx hy =>
      exact ((map_add _ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add _ x y).symm

/-- Tensor products are right exact, so module extension preserves finite colimits
in a common value universe. -/
public instance moduleExtensionFunctor_preservesFiniteColimits (A : Type u) [CommRing A] :
    PreservesFiniteColimits (moduleExtensionFunctor.{max u v w, v} A) where
  preservesFiniteColimits J := { preservesColimit := fun {K} => {
    preserves := fun {c} hc => ⟨by
      apply PresheafOfModules.evaluationJointlyReflectsColimits
      intro X
      letI : PreservesFiniteColimits
          (moduleExtensionFunctor.{max u v w, v} A ⋙
            PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X) :=
        preservesFiniteColimits_of_natIso (moduleExtensionEvaluationIso A X).symm
      exact isColimitOfPreserves
        (moduleExtensionFunctor.{max u v w, v} A ⋙
          PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X) hc⟩ } }

/-- The cokernel of an extended module map is the extension of its module cokernel. -/
public noncomputable def moduleExtensionCokernelIso {A : Type u} [CommRing A]
    {M N : ModuleCat.{max u v w} A} (f : M ⟶ N) :
    moduleExtension.{max u v w, v} A (cokernel f) ≅
      cokernel ((moduleExtensionFunctor.{max u v w, v} A).map f) :=
  PreservesCokernel.iso (moduleExtensionFunctor.{max u v w, v} A) f

/-- Restrict `B ↦ B ⊗[A] M` and its action on module maps to the chosen algebra domain. -/
public noncomputable abbrev moduleExtensionFunctorOn {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{max u v} A) :
    ModuleCat.{w} A ⥤ ModuleValuedFunctorOn.{max u v w} ι :=
  moduleExtensionFunctor.{w, v} A ⋙
    PresheafOfModules.pushforward₀ ι.op (algebraRingDiagram.{v} A)

/-- `F` is the categorical kernel of the base-changed map on its chosen domain. No values
of `F` outside that domain are required. -/
public abbrev IsKernelPresentation {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctorOn.{w} ι) {M N : ModuleCat.{max u v w} A} (f : M ⟶ N) : Prop :=
  Nonempty ((presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)).obj F ≅
    kernel ((moduleExtensionFunctorOn.{max u v w} ι).map f))

/-- A module-valued functor is adequate if it is the kernel of the base changes of a map of
`A`-modules. -/
@[stacks 06UT "part (1)"]
public abbrev IsAdequate {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctorOn.{w} ι) : Prop :=
  ∃ (M N : ModuleCat.{max u v w} A) (f : M ⟶ N), IsKernelPresentation ι F f

/-- The finite free `A`-module of rank `n`, placed in a possibly larger universe. -/
public abbrev finiteFreeModule (A : Type u) [CommRing A] (n : ℕ) : ModuleCat.{max u w} A :=
  (ModuleCat.uliftFunctor.{w, u} A).obj (ModuleCat.of A (Fin n → A))

/-- A module-valued functor is linearly adequate if it is the kernel of a morphism between
the module-valued functors associated to two finite free modules. -/
@[stacks 06UT "part (2)"]
public abbrev IsLinearlyAdequate {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctorOn.{w} ι) : Prop :=
  ∃ (n m : ℕ)
    (f : (moduleExtensionFunctorOn.{max u v w} ι).obj (finiteFreeModule.{max u v w} A n) ⟶
      (moduleExtensionFunctorOn.{max u v w} ι).obj (finiteFreeModule.{max u v w} A m)),
    Nonempty ((presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)).obj F ≅
      kernel f)

/-- If the value universe already contains the base ring and algebra universes, a kernel
presentation is precisely an isomorphism to the ordinary categorical kernel. -/
public lemma isKernelPresentation_iff {A : Type u} [CommRing A]
    (F : ModuleValuedFunctor.{max u v w, v} A) {M N : ModuleCat.{max u v w} A}
    (f : M ⟶ N) :
    IsKernelPresentation (𝟭 _) F f ↔
      Nonempty (F ≅ kernel ((moduleExtensionFunctor.{max u v w, v} A).map f)) := by
  let e := presheafOfModulesUliftIso.{max u v, w} (algebraRingDiagram.{v} A) F
  exact ⟨fun ⟨i⟩ ↦ ⟨e.symm ≪≫ i⟩, fun ⟨i⟩ ↦ ⟨e ≪≫ i⟩⟩

/-- In a common value universe, linear adequacy is precisely the existence of a categorical
kernel presentation by a morphism between finite-free module-valued functors. -/
public lemma isLinearlyAdequate_iff {A : Type u} [CommRing A]
    (F : ModuleValuedFunctor.{max u v w, v} A) :
    IsLinearlyAdequate (𝟭 _) F ↔
      ∃ (n m : ℕ)
        (f : moduleExtension.{max u v w, v} A (finiteFreeModule.{max u v w} A n) ⟶
          moduleExtension.{max u v w, v} A (finiteFreeModule.{max u v w} A m)),
        Nonempty (F ≅ kernel f) := by
  let e := presheafOfModulesUliftIso.{max u v, w} (algebraRingDiagram.{v} A) F
  exact ⟨fun ⟨n, m, f, ⟨i⟩⟩ ↦ ⟨n, m, f, ⟨e.symm ≪≫ i⟩⟩,
    fun ⟨n, m, f, ⟨i⟩⟩ ↦ ⟨n, m, f, ⟨e ≪≫ i⟩⟩⟩

/-- Adequacy can equivalently be witnessed by any morphism between module extensions.
Full faithfulness supplies the underlying module map. -/
public lemma isAdequate_iff {A : Type u} [CommRing A]
    (F : ModuleValuedFunctor.{max u v w, v} A) :
    IsAdequate (𝟭 _) F ↔
      ∃ (M N : ModuleCat.{max u v w} A)
        (f : moduleExtension.{max u v w, v} A M ⟶
          moduleExtension.{max u v w, v} A N), Nonempty (F ≅ kernel f) := by
  constructor
  · rintro ⟨M, N, f, h⟩
    exact ⟨M, N, (moduleExtensionFunctor.{max u v w, v} A).map f,
      (isKernelPresentation_iff F f).mp h⟩
  · rintro ⟨M, N, f, h⟩
    refine ⟨M, N, moduleHomOfExtensionNatTrans f,
      (isKernelPresentation_iff F _).mpr ?_⟩
    rwa [← moduleExtension_natTrans_eq_map f]

/-- A linear presentation may be chosen with an underlying map of finite free modules,
as used to form the finitely presented cokernel in Tag 06ZH. -/
public lemma isLinearlyAdequate_iff_exists_module_map {A : Type u} [CommRing A]
    (F : ModuleValuedFunctor.{w, v} A) :
    IsLinearlyAdequate (𝟭 _) F ↔
      ∃ (n m : ℕ)
        (f : finiteFreeModule.{max u v w} A n ⟶ finiteFreeModule.{max u v w} A m),
        IsKernelPresentation (𝟭 _) F f := by
  constructor
  · rintro ⟨n, m, f, h⟩
    refine ⟨n, m, moduleHomOfExtensionNatTrans f, ?_⟩
    show Nonempty (_ ≅ kernel ((moduleExtensionFunctor.{max u v w, v} A).map
      (moduleHomOfExtensionNatTrans f)))
    rwa [← moduleExtension_natTrans_eq_map f]
  · rintro ⟨n, m, f, h⟩
    exact ⟨n, m, (moduleExtensionFunctor.{max u v w, v} A).map f, h⟩

/-- Adequacy is invariant under isomorphism of module-valued functors. -/
public lemma IsAdequate.of_iso {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] {ι : C ⥤ CommAlgCat.{max u v} A}
    {F G : ModuleValuedFunctorOn.{w} ι} (hF : IsAdequate ι F) (e : G ≅ F) :
    IsAdequate ι G := by
  obtain ⟨M, N, f, ⟨i⟩⟩ := hF
  exact ⟨M, N, f,
    ⟨(presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)).mapIso e ≪≫ i⟩⟩

/-- Linear adequacy is invariant under isomorphism of module-valued functors. -/
public lemma IsLinearlyAdequate.of_iso {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] {ι : C ⥤ CommAlgCat.{max u v} A}
    {F G : ModuleValuedFunctorOn.{w} ι} (hF : IsLinearlyAdequate ι F) (e : G ≅ F) :
    IsLinearlyAdequate ι G := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := hF
  exact ⟨n, m, f,
    ⟨(presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)).mapIso e ≪≫ i⟩⟩

add_to_stacks 06Z4 "module-valued functors and their morphisms"
  AdequateFunctor.ModuleValuedFunctor

end

end AdequateFunctor

end
