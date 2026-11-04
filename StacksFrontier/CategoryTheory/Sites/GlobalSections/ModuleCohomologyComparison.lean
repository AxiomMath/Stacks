module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of sheaves of modules and of their underlying abelian sheaves

Let `J` be a Grothendieck topology on a small category `C` and let `R` be a sheaf of rings for
`J`. The cohomology of an `R`-module sheaf, computed by deriving sections in the category
`Sheaf J (ModuleCat R)`, agrees with the cohomology of the underlying sheaf of abelian groups,
computed by deriving sections in `Sheaf J Ab`. This holds both for the global sections of the
site and for the sections over each object of `C`, naturally in the module sheaf.

The proof is the `δ`-functor argument of the source. Cohomology over `U` is the right-derived
functor of sections over `U`; the forgetful functor `SheafOfModules.toSheaf R` is exact, so
composing with it again yields a `δ`-functor, and it suffices to see that the underlying abelian
sheaf of an injective module sheaf is acyclic. Acyclicity is obtained from the representability
of sections: sections over `U` are corepresented by the sheafification of the free abelian
presheaf on `yoneda.obj U`, global sections by the constant sheaf on `ℤ`, and both corepresenting
objects are sectionwise torsion free. Against a sectionwise torsion-free abelian sheaf, the
underlying sheaf of an injective module sheaf has vanishing higher `Ext`, because extension of
scalars `F ↦ R ⊗[ℤ] F` from abelian presheaves to presheaves of modules stays a monomorphism on a
short exact sequence with torsion-free quotient and is left adjoint to the forgetful functor.

## Main results

* `ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying`: the natural comparison between
  module-sheaf cohomology and the cohomology of the underlying abelian sheaf, globally and over
  every object of the site, normalized in degree zero.

## Implementation notes

Cohomology is represented by Mathlib's right-derived functors of `Sheaf.Γ` and of
`(sheafSections J Ab).obj (op U)`. The source's equalities of cohomology groups are expressed as
natural isomorphisms of the derived functors; their canonical normalization is recorded by
compatibility in degree zero with `Functor.toRightDerivedZero`.

Part of the supporting machinery is private to this module: the auxiliary torsion-freeness
lemmas and the assembly of the comparison in positive degree out of the `δ`-functor comparison
(`extComparisonIso`, `rightDerivedCompIsoOfRepresentable`, `represented_succ_comparison`). The
adjunction data of extension of scalars on presheaves is *not*: it is public, because the second
copy of it that `Cohomology.ObjectSections.DerivedSectionsVanishing` carried was collapsed onto
this one, and that file builds its own corepresentation out of these declarations.

What is public is the input needed to build the comparison *as a named isomorphism* rather than
by existence, which is what `ModuleCohomologyComparisonDef` does: the identification of `Ext` in
positive degree with the right-derived functors of `preadditiveCoyoneda`
(`rightDerivedCoyonedaSuccIso`, together with the homology data `extLeftHomologyData` and
`extCyclesMap` through which it is defined), its degree-zero counterpart
(`extZeroIsoCoyoneda`), transport of right-derived functors along an isomorphism of functors
(`rightDerivedIso`), the `δ`-functor structure on `Ext` in the second variable
(`extDeltaFunctor`) together with its universality, the `Ext`-vanishing statements for
sectionwise torsion-free sheaves (`ext_eq_zero_of_isTorsionFree`) and for the image of an
injective object under a right adjoint whose left adjoint stays a monomorphism on short exact
sequences with resolving quotient (`ext_eq_zero_of_adjunction`), the two corepresentations
(`globalSectionsRepresentation`, `evaluationRepresentation`) and the corepresenting module sheaf
`tensorPresheaf` with its functoriality `tensorPresheafMap`, its hom-isomorphism
`tensorSheafHomIso` and the naturality of that isomorphism in the abelian presheaf
(`tensorSheafHomIso_naturality`).

Public with them is the whole extension-of-scalars adjunction they are built from:
`tensorPresheafRestrict` and `tensorPresheafRestrict_tmul`, the elementary-tensor description
`tensorPresheaf_map_tmul`, the universal property `tensorPresheafLift` with
`tensorPresheafLift_app_tmul`, the unit `tensorPresheafUnit` with `tensorPresheafUnit_comp_lift`
and `tensorPresheafUnit_naturality`, and the resulting corepresentation
`tensorPresheafHomAddEquiv`. These were private, and a second copy of all of them lived in
`Cohomology.ObjectSections.DerivedSectionsVanishing`, which needs the same adjunction over a site
whose objects need not be small. The duplicate was deleted and that file now uses these, so the
adjunction data is public here. Only `tensorSheafHomIso` keeps `@[no_expose]`: its type is all
that is needed downstream.

Tag 03FD belongs to the chapter on cohomology on sites; it is recorded here because it is what
the section on `Rlim` of modules appeals to in order to compare `Rlim` of an inverse system of
modules with `Rlim` of the underlying inverse system of abelian groups.

## References

* [Stacks: Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/


@[expose] public noncomputable section

open CategoryTheory Opposite Limits

namespace ModuleSheafCohomology

open CategoryTheory.Abelian

section TensorProduct

/-- Over a Dedekind domain, an exact sequence with torsion-free last term stays
injective at its first map after tensoring. Surjectivity of the second map is unnecessary. -/
public lemma lTensor_injective_of_exact_of_isTorsionFree
    {R M N P : Type*} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module.IsTorsionFree R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f)
    (h : Function.Exact f g) (T : Type*) [AddCommGroup T] [Module R T] :
    Function.Injective (f.lTensor T) := by
  apply LinearMap.lTensor_injective_of_exact_of_flat g.rangeRestrict
    g.surjective_rangeRestrict f hf
  intro x
  show (g.rangeRestrict x = 0) ↔ x ∈ Set.range f
  rw [Subtype.ext_iff]
  exact h x

end TensorProduct

section TorsionFreeSheaves

universe w v u

variable {D : Type w} [Category.{v} D] (K : GrothendieckTopology D)
  [HasSheafify K Ab.{u}]

/-- Sheafification preserves sectionwise torsion-freeness. -/
public lemma isTorsionFree_sheafify (F : Dᵒᵖ ⥤ Ab.{u})
    (hF : ∀ X, Module.IsTorsionFree ℤ (F.obj X)) (X : Dᵒᵖ) :
    Module.IsTorsionFree ℤ ((sheafify K F).obj X) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n x hx
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  have hmono : Mono (n • 𝟙 F) := by
    have (Y : Dᵒᵖ) : Mono ((n • 𝟙 F).app Y) := by
      have := hF Y
      rw [AddCommGrpCat.mono_iff_injective]
      exact IsSMulRegular.of_ne_zero hn
    exact NatTrans.mono_of_mono_app _
  have hm : Mono (((presheafToSheaf K Ab.{u}).map (n • 𝟙 F)).hom.app X) :=
    inferInstance
  have hi := (AddCommGrpCat.mono_iff_injective _).mp hm
  rw [Functor.map_zsmul, CategoryTheory.Functor.map_id] at hi
  change Function.Injective (fun y : (sheafify K F).obj X => n • y) at hi
  apply hi
  simpa only [smul_zero] using hx

/-- A subsheaf of a sectionwise torsion-free abelian sheaf is sectionwise torsion-free. -/
public lemma isTorsionFree_of_mono {F G : Sheaf K Ab.{u}} (f : F ⟶ G) [Mono f]
    (hG : ∀ X, Module.IsTorsionFree ℤ (G.obj.obj X)) (X : Dᵒᵖ) :
    Module.IsTorsionFree ℤ (F.obj.obj X) := by
  have := hG X
  exact Function.Injective.moduleIsTorsionFree (f.hom.app X)
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance) (map_zsmul _)

/-- Free abelian groups are torsion free. -/
private lemma isTorsionFree_free_obj (X : Type u) :
    Module.IsTorsionFree ℤ (AddCommGrpCat.free.obj X) :=
  Module.Flat.isTorsionFree (R := ℤ) (M := FreeAbelianGroup X)

/-- Every abelian sheaf is an epimorphic image of a sectionwise torsion-free sheaf. -/
public lemma exists_isTorsionFree_epi (F : Sheaf K Ab.{u}) :
    ∃ (G : Sheaf K Ab.{u}) (p : G ⟶ F),
      (∀ X, Module.IsTorsionFree ℤ (G.obj.obj X)) ∧ Epi p := by
  let P := F.obj ⋙ forget Ab.{u} ⋙ AddCommGrpCat.free
  let ε : P ⟶ F.obj :=
    { app X := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun x : F.obj.obj X => x))
      naturality _ _ f := by
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro x
        show FreeAbelianGroup.lift (fun x => x)
            (FreeAbelianGroup.map (F.obj.map f) (FreeAbelianGroup.of x)) =
          F.obj.map f (FreeAbelianGroup.lift (fun x => x) (FreeAbelianGroup.of x))
        simp }
  have hε : Epi ε := by
    have (X : Dᵒᵖ) : Epi (ε.app X) := by
      rw [AddCommGrpCat.epi_iff_surjective]
      intro x
      refine ⟨FreeAbelianGroup.of x, ?_⟩
      exact FreeAbelianGroup.lift_apply_of _ x
    exact NatTrans.epi_of_epi_app ε
  refine ⟨(presheafToSheaf K Ab.{u}).obj P,
    (presheafToSheaf K Ab.{u}).map ε ≫ (sheafificationAdjunction K Ab.{u}).counit.app F,
    ?_, inferInstance⟩
  apply isTorsionFree_sheafify K P
  intro X
  exact isTorsionFree_free_obj _

end TorsionFreeSheaves

section TensorPresheaf

universe w v u

open TensorProduct

variable {D : Type w} [Category.{v} D] (R : Dᵒᵖ ⥤ RingCat.{u})

/-- Restriction along `f` in the extension of scalars of an abelian presheaf, as a semilinear
map over the restriction of the presheaf of rings. -/
public def tensorPresheafRestrict (F : Dᵒᵖ ⥤ Ab.{u}) {X Y : Dᵒᵖ} (f : X ⟶ Y) :
    (R.obj X ⊗[ℤ] F.obj X) →ₛₗ[(R.map f).hom] (R.obj Y ⊗[ℤ] F.obj Y) where
  toFun := TensorProduct.map (R.map f).hom.toAddMonoidHom.toIntLinearMap
    (F.map f).hom.toIntLinearMap
  map_add' := map_add _
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul a x => simp [TensorProduct.smul_tmul', smul_eq_mul]

public lemma tensorPresheafRestrict_tmul (F : Dᵒᵖ ⥤ Ab.{u})
    {X Y : Dᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (x : F.obj X) :
    tensorPresheafRestrict R F f (r ⊗ₜ[ℤ] x) = R.map f r ⊗ₜ[ℤ] F.map f x :=
  TensorProduct.map_tmul _ _ _ _

/-- Extension of scalars from abelian presheaves to module presheaves, on objects. -/
public def tensorPresheaf (F : Dᵒᵖ ⥤ Ab.{u}) : PresheafOfModules.{u} R where
  obj X := ModuleCat.of (R.obj X) (R.obj X ⊗[ℤ] F.obj X)
  map f := (ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _)
    (tensorPresheafRestrict R F f)
  map_id X := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change tensorPresheafRestrict R F (𝟙 X) (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] x
    simp [tensorPresheafRestrict_tmul]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change tensorPresheafRestrict R F (f ≫ g) (a ⊗ₜ[ℤ] x) =
      tensorPresheafRestrict R F g (tensorPresheafRestrict R F f (a ⊗ₜ[ℤ] x))
    simp [tensorPresheafRestrict_tmul]

/-- Restriction in the extension of scalars of an abelian presheaf, on elementary tensors. -/
public lemma tensorPresheaf_map_tmul (F : Dᵒᵖ ⥤ Ab.{u})
    {X Y : Dᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (x : F.obj X) :
    (tensorPresheaf R F).map f (r ⊗ₜ[ℤ] x) = R.map f r ⊗ₜ[ℤ] F.map f x :=
  TensorProduct.map_tmul _ _ _ _

/-- Extension of scalars on a morphism of abelian presheaves. -/
public def tensorPresheafMap {F G : Dᵒᵖ ⥤ Ab.{u}} (f : F ⟶ G) :
    tensorPresheaf R F ⟶ tensorPresheaf R G where
  app X := ModuleCat.ofHom (AlgebraTensorModule.map (LinearMap.id : R.obj X →ₗ[R.obj X] R.obj X)
    (f.app X).hom.toIntLinearMap)
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change R.map g r ⊗ₜ[ℤ] f.app Y (F.map g x) =
      R.map g r ⊗ₜ[ℤ] G.map g (f.app X x)
    rw [NatTrans.naturality_apply]

private lemma tensorPresheafMap_app_tmul {F G : Dᵒᵖ ⥤ Ab.{u}} (f : F ⟶ G)
    (X : Dᵒᵖ) (r : R.obj X) (x : F.obj X) :
    (tensorPresheafMap R f).app X (r ⊗ₜ[ℤ] x) = r ⊗ₜ[ℤ] f.app X x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- An additive morphism extends uniquely to an `R`-linear morphism from its tensor product. -/
public def tensorPresheafLift {F : Dᵒᵖ ⥤ Ab.{u}} {M : PresheafOfModules.{u} R}
    (f : F ⟶ M.presheaf) : tensorPresheaf R F ⟶ M where
  app X := ModuleCat.ofHom
    (X := (tensorPresheaf R F).obj X) (Y := M.obj X)
    (AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton (R.obj X) (F.obj X →ₗ[ℤ] M.obj X)
        (f.app X).hom.toIntLinearMap))
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change R.map g r • f.app Y (F.map g x) = M.map g (r • f.app X x)
    rw [M.map_smul, NatTrans.naturality_apply]
    rfl

public lemma tensorPresheafLift_app_tmul {F : Dᵒᵖ ⥤ Ab.{u}}
    {M : PresheafOfModules.{u} R} (f : F ⟶ M.presheaf)
    (X : Dᵒᵖ) (r : R.obj X) (x : F.obj X) :
    (tensorPresheafLift R f).app X (r ⊗ₜ[ℤ] x) = r • f.app X x := rfl

/-- The canonical additive map into extension of scalars. -/
public def tensorPresheafUnit (F : Dᵒᵖ ⥤ Ab.{u}) :
    F ⟶ (tensorPresheaf R F).presheaf where
  app X := AddCommGrpCat.ofHom ((TensorProduct.mk ℤ (R.obj X) (F.obj X) 1).toAddMonoidHom)
  naturality {X Y} f := by
    ext x
    change 1 ⊗ₜ[ℤ] F.map f x = (tensorPresheaf R F).map f (1 ⊗ₜ[ℤ] x)
    rw [tensorPresheaf_map_tmul, map_one]

public lemma tensorPresheafUnit_comp_lift {F : Dᵒᵖ ⥤ Ab.{u}}
    {M : PresheafOfModules.{u} R} (f : F ⟶ M.presheaf) :
    tensorPresheafUnit R F ≫ (PresheafOfModules.toPresheaf R).map
      (tensorPresheafLift R f) = f := by
  ext X x
  show (tensorPresheafLift R f).app X (1 ⊗ₜ[ℤ] x) = f.app X x
  rw [tensorPresheafLift_app_tmul, one_smul]

public lemma tensorPresheafUnit_naturality {F G : Dᵒᵖ ⥤ Ab.{u}} (f : F ⟶ G) :
    f ≫ tensorPresheafUnit R G = tensorPresheafUnit R F ≫
      (PresheafOfModules.toPresheaf R).map (tensorPresheafMap R f) := by
  ext X x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The tensor presheaf represents additive maps from the original abelian presheaf. -/
public def tensorPresheafHomAddEquiv (F : Dᵒᵖ ⥤ Ab.{u})
    (M : PresheafOfModules.{u} R) :
    (tensorPresheaf R F ⟶ M) ≃+ (F ⟶ M.presheaf) where
  toFun f := tensorPresheafUnit R F ≫ (PresheafOfModules.toPresheaf R).map f
  invFun := tensorPresheafLift R
  left_inv f := by
    ext1 X
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change r • f.app X (1 ⊗ₜ[ℤ] x) = f.app X (r ⊗ₜ[ℤ] x)
    change r • (f.app X).hom (1 ⊗ₜ[ℤ] x) = (f.app X).hom (r ⊗ₜ[ℤ] x)
    calc
      _ = (f.app X).hom (r • (1 ⊗ₜ[ℤ] x)) :=
        ((f.app X).hom.map_smul r (1 ⊗ₜ[ℤ] x)).symm
      _ = _ := by
        congr 1
        change (r * 1) ⊗ₜ[ℤ] x = r ⊗ₜ[ℤ] x
        rw [mul_one]
  right_inv := tensorPresheafUnit_comp_lift R
  map_add' f g := by
    ext X x
    rfl

end TensorPresheaf

section ExtComparison

universe w v u
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasExt.{w} A] [HasInjectiveResolutions A]

/-- The kernel of an epimorphism sits in a short exact sequence. -/
private lemma shortExact_kernel_of_epi {T : Type*} [Category T] [Abelian T] {X Y : T}
    (p : X ⟶ Y) [Epi p] :
    (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance

private lemma ext_exists_epi {X Y : A} (n : ℕ) (e : Ext X Y (n + 1)) :
    ∃ (P : A) (p : P ⟶ X), Epi p ∧ (Ext.mk₀ p).comp e (zero_add _) = 0 := by
  let I := injectiveResolution Y
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective e (n + 2) rfl
  obtain ⟨P, p, hp, g, hg⟩ := (I.exact_succ n).exact_up_to_refinements f hf
  refine ⟨P, p, hp, ?_⟩
  rw [I.mk₀_comp_extMk, I.extMk_eq_zero_iff _ _ _ _ n rfl]
  exact ⟨g, hg.symm⟩

public lemma ext_eq_zero_of_resolving
    (P : A → Prop)
    (hsub : ∀ {X Y : A} (f : X ⟶ Y), Mono f → P Y → P X)
    (henough : ∀ X : A, ∃ (Y : A) (p : Y ⟶ X), P Y ∧ Epi p)
    (I : A) (hI : ∀ X : A, P X → ∀ e : Ext X I 1, e = 0)
    (n : ℕ) (X : A) (hX : P X) (e : Ext X I (n + 1)) : e = 0 := by
  induction n generalizing X with
  | zero => exact hI X hX e
  | succ n ih =>
    obtain ⟨Y, p, hp, he⟩ := ext_exists_epi (n + 1) e
    obtain ⟨Z, q, hZ, hq⟩ := henough Y
    let r := q ≫ p
    have hr : Epi r := inferInstance
    have hre : (Ext.mk₀ r).comp e (zero_add _) = 0 := by
      dsimp [r]
      rw [← Ext.mk₀_comp_mk₀_assoc, he, Ext.comp_zero]
    obtain ⟨a, ha⟩ :=
      Ext.contravariant_sequence_exact₃ (shortExact_kernel_of_epi r) I e hre
      (show 1 + (n + 1) = n + 1 + 1 by omega)
    rw [ih _ (hsub (kernel.ι r) inferInstance hZ) a, Ext.comp_zero] at ha
    exact ha.symm

public lemma ext_one_eq_zero_of_extension
    (P : A → Prop) (I : A)
    (hI : ∀ (S : ShortComplex A), S.ShortExact → P S.X₃ →
      ∀ f : S.X₁ ⟶ I, ∃ g : S.X₂ ⟶ I, S.f ≫ g = f)
    (X : A) (hX : P X) (e : Ext X I 1) : e = 0 := by
  obtain ⟨Y, p, hp, he⟩ := ext_exists_epi 0 e
  have hS := shortExact_kernel_of_epi p
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₃ hS I e he (show 1 + 0 = 1 from rfl)
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 a
  obtain ⟨g, hg⟩ := hI _ hS hX f
  rw [← hg, ← Ext.mk₀_comp_mk₀, hS.extClass_comp_assoc] at ha
  exact ha.symm

/-- **`Ext` out of a resolving object into the image of an injective vanishes in positive
degree.** Let `L ⊣ F` be an adjunction, let `P` be a property of objects closed under subobjects
whose objects cover every object, and suppose `L` keeps the first map of a short exact sequence
with `P`-quotient a monomorphism. Then `Ext X (F I) (n + 1) = 0` for every injective `I` and
every `X` with `P X`: the dévissage of `ext_eq_zero_of_resolving` reduces to degree one, where
an extension is split by factoring through the injective `I` after applying `L`. -/
public lemma ext_eq_zero_of_adjunction
    {B : Type*} [Category B] [Abelian B] (L : A ⥤ B) (F : B ⥤ A)
    (adj : L ⊣ F) (P : A → Prop)
    (hsub : ∀ {X Y : A} (f : X ⟶ Y), Mono f → P Y → P X)
    (henough : ∀ X : A, ∃ (Y : A) (p : Y ⟶ X), P Y ∧ Epi p)
    (hL : ∀ (S : ShortComplex A), S.ShortExact → P S.X₃ → Mono (L.map S.f))
    (I : B) [Injective I] (n : ℕ) (X : A) (hX : P X)
    (e : Ext X (F.obj I) (n + 1)) : e = 0 := by
  apply ext_eq_zero_of_resolving P hsub henough (F.obj I) _ n X hX e
  apply ext_one_eq_zero_of_extension
  intro S hS hP f
  have := hL S hS hP
  let g := Injective.factorThru ((adj.homEquiv _ _).symm f) (L.map S.f)
  refine ⟨adj.homEquiv _ _ g, ?_⟩
  rw [← adj.homEquiv_naturality_left]
  simp [g]

end ExtComparison

section ExtRightDerived

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A]
  {Y : A} (I : InjectiveResolution Y) (X : A) (n : ℕ)

public abbrev homShortComplex : ShortComplex Ab.{v} :=
  (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex).sc' n (n + 1) (n + 2)

/-- A cocycle in a Hom complex determines its Ext class. -/
public def extCyclesMap :
    (homShortComplex I X n).g.hom.ker →+ Ext X Y (n + 1) where
  toFun f := I.extMk f.val (n + 2) rfl f.property
  map_zero' := I.extMk_zero _ _
  map_add' f g := (I.add_extMk f.val g.val (n + 2) rfl f.property g.property).symm

public lemma extCyclesMap_surjective : Function.Surjective (extCyclesMap I X n) := by
  intro e
  obtain ⟨f, hf, he⟩ := I.extMk_surjective e (n + 2) rfl
  exact ⟨⟨f, hf⟩, he⟩

set_option backward.isDefEq.respectTransparency false in
public lemma extCyclesMap_eq_zero_iff (f : (homShortComplex I X n).g.hom.ker) :
    extCyclesMap I X n f = 0 ↔
      ∃ g, (homShortComplex I X n).abToCycles g = f := by
  rw [show extCyclesMap I X n f = I.extMk f.val (n + 2) rfl f.property from rfl,
    I.extMk_eq_zero_iff _ _ _ _ n rfl]
  apply exists_congr
  intro g
  constructor
  · exact fun h => Subtype.ext h
  · exact fun h => congrArg Subtype.val h

/-- Ext is the homology of the Hom complex of an injective resolution. -/
public def extLeftHomologyData : (homShortComplex I X n).LeftHomologyData where
  K := (homShortComplex I X n).abLeftHomologyData.K
  H := AddCommGrpCat.of (Ext X Y (n + 1))
  i := (homShortComplex I X n).abLeftHomologyData.i
  π := AddCommGrpCat.ofHom (extCyclesMap I X n)
  wi := (homShortComplex I X n).abLeftHomologyData.wi
  hi := (homShortComplex I X n).abLeftHomologyData.hi
  wπ := by
    ext g
    apply (extCyclesMap_eq_zero_iff I X n _).2
    exact ⟨g, rfl⟩
  hπ := by
    have : Epi (AddCommGrpCat.ofHom (extCyclesMap I X n)) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr (extCyclesMap_surjective I X n)
    apply ShortComplex.Exact.gIsCokernel (S := ShortComplex.mk
      (AddCommGrpCat.ofHom (homShortComplex I X n).abToCycles)
      (AddCommGrpCat.ofHom (extCyclesMap I X n)) (by
        ext g
        exact (extCyclesMap_eq_zero_iff I X n _).2 ⟨g, rfl⟩))
    rw [ShortComplex.ab_exact_iff]
    intro f hf
    exact (extCyclesMap_eq_zero_iff I X n f).1 hf

public abbrev homShortComplexMap {Y' : A} {I' : InjectiveResolution Y'}
    {f : Y ⟶ Y'} (φ : I.Hom I' f) : homShortComplex I X n ⟶ homShortComplex I' X n :=
  (HomologicalComplex.shortComplexFunctor' Ab.{v} (ComplexShape.up ℕ) n (n + 1) (n + 2)).map
    (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex _).map φ.hom)

set_option backward.isDefEq.respectTransparency false in
public def extLeftHomologyMapData {Y' : A} {I' : InjectiveResolution Y'}
    {f : Y ⟶ Y'} (φ : I.Hom I' f) :
    ShortComplex.LeftHomologyMapData (homShortComplexMap I X n φ)
      (extLeftHomologyData I X n) (extLeftHomologyData I' X n) where
  φK := AddCommGrpCat.ofHom
    { toFun t := ⟨t.val ≫ φ.hom.f (n + 1), by
        change (t.val ≫ φ.hom.f (n + 1)) ≫ I'.cocomplex.d (n + 1) (n + 2) = 0
        rw [Category.assoc, φ.hom.comm, ← Category.assoc]
        have ht : t.val ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := t.property
        rw [ht, zero_comp]⟩
      map_zero' := by apply Subtype.ext; exact zero_comp
      map_add' _ _ := by apply Subtype.ext; apply Preadditive.add_comp }
  φH := (extFunctorObj X (n + 1)).map f
  commi := by ext t; rfl
  commf' := by
    ext t
    apply Subtype.ext
    change (t ≫ I.cocomplex.d n (n + 1)) ≫ φ.hom.f (n + 1) =
      (t ≫ φ.hom.f n) ≫ I'.cocomplex.d n (n + 1)
    rw [Category.assoc, Category.assoc, φ.hom.comm]
  commπ := by
    ext t
    exact I.extMk_comp_mk₀ t.val (n + 2) rfl t.property φ

variable [HasInjectiveResolutions A]

set_option backward.isDefEq.respectTransparency false in
public def rightDerivedCoyonedaSuccIso :
    (preadditiveCoyoneda.obj (op X)).rightDerived (n + 1) ≅ extFunctorObj X (n + 1) :=
  NatIso.ofComponents (fun Y =>
    (injectiveResolution Y).isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) (n + 1) ≪≫
      (HomologicalComplex.homologyFunctorIso' Ab.{v} (ComplexShape.up ℕ) n (n + 1) (n + 2)
        (by simp) (by simp)).app _ ≪≫
      (extLeftHomologyData (injectiveResolution Y) X n).homologyIso) (by
    intro Y Y' f
    let φ : (injectiveResolution Y).Hom (injectiveResolution Y') f :=
      ⟨InjectiveResolution.desc f _ _, by
        simp⟩
    dsimp only [Iso.trans_hom]
    rw [← Category.assoc,
      InjectiveResolution.isoRightDerivedObj_hom_naturality f _ _ φ.hom
        (by simp)]
    rw [Category.assoc, ← Category.assoc _ _ ((extLeftHomologyData _ _ _).homologyIso.hom)]
    erw [(HomologicalComplex.homologyFunctorIso' Ab.{v} (ComplexShape.up ℕ)
      n (n + 1) (n + 2) (by simp) (by simp)).hom.naturality
        (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex _).map φ.hom)]
    erw [Category.assoc, Category.assoc,
      (extLeftHomologyMapData _ X n φ).homologyMap_comm]
    simp only [InjectiveResolution.isoRightDerivedObj, Iso.trans_hom,
      extLeftHomologyMapData, Category.assoc]
    rfl)

end ExtRightDerived

section ExtDeltaFunctor

universe w v v' u u'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : A)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
-- Exactness is transported through both the Ext functor and the given exact functor.
set_option backward.defeqAttrib.useBackward true in
/-- Ext in the second variable, precomposed with an exact functor, is a delta functor. -/
@[sga "4 V 2.1.1" "more general"]
public def extDeltaFunctor : DeltaFunctor B Ab.{w} where
  functor n := F ⋙ extFunctorObj X n
  δ hS n := by
    have := hS.mono_f
    have := hS.epi_g
    exact AddCommGrpCat.ofHom ((hS.map_of_exact F).extClass.postcomp X (rfl : n + 1 = n + 1))
  map_g_δ hS n := by
    ext e
    change Ext X _ n at e
    change (e.comp (Ext.mk₀ (F.map _)) (add_zero n)).comp
      (hS.map_of_exact F).extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero]
    erw [(hS.map_of_exact F).comp_extClass, Ext.comp_zero]
  δ_map_f hS n := by
    ext e
    change Ext X _ n at e
    change (e.comp (hS.map_of_exact F).extClass rfl).comp
      (Ext.mk₀ (F.map _)) (add_zero _) = 0
    rw [Ext.comp_assoc_of_third_deg_zero]
    erw [(hS.map_of_exact F).extClass_comp, Ext.comp_zero]
  mono_map_f hS := by
    have := hS.mono_f
    exact Ext.mono_postcomp_mk₀_of_mono X (F.map _)
  exact_map hS n := by
    have := hS.mono_f
    have := hS.epi_g
    exact Ext.covariant_sequence_exact₂' X (hS.map_of_exact F) n
  exact_δ₁ hS n := by
    have := hS.mono_f
    have := hS.epi_g
    exact Ext.covariant_sequence_exact₃' X (hS.map_of_exact F) n (n + 1) rfl
  exact_δ₂ hS n := by
    have := hS.mono_f
    have := hS.epi_g
    exact Ext.covariant_sequence_exact₁' X (hS.map_of_exact F) n (n + 1) rfl
  δ_naturality hS hT φ n := by
    have := hS.mono_f
    have := hS.epi_g
    have := hT.mono_f
    have := hT.epi_g
    ext e
    change Ext X _ n at e
    change (e.comp (Ext.mk₀ (F.map φ.τ₃)) (add_zero n)).comp
      (hT.map_of_exact F).extClass rfl =
      (e.comp (hS.map_of_exact F).extClass rfl).comp
        (Ext.mk₀ (F.map φ.τ₁)) (add_zero _)
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]
    exact congrArg (fun a => e.comp a rfl)
      ((hS.map_of_exact F).extClass_naturality (hT.map_of_exact F)
        (F.mapShortComplex.map φ)).symm

public lemma extDeltaFunctor_isUniversal [EnoughInjectives B]
    (h : ∀ (I : B) [Injective I] (n : ℕ) (e : Ext X (F.obj I) (n + 1)), e = 0) :
    (extDeltaFunctor F X).IsUniversal := by
  apply DeltaFunctor.isUniversal_of_isZero_injective
  intro n I hI
  have : Subsingleton (Ext X (F.obj I) (n + 1)) :=
    subsingleton_of_forall_eq 0 (h I n)
  exact AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (Ext X (F.obj I) (n + 1)))

end ExtDeltaFunctor

section ExtComparisonIso

universe v u u'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A]
  {B : Type u'} [Category.{v} B] [Abelian B] [HasExt.{v} B]

set_option backward.isDefEq.respectTransparency false in
public def extZeroIsoCoyoneda (X : A) :
    extFunctorObj X 0 ≅ preadditiveCoyoneda.obj (op X) :=
  NatIso.ofComponents (fun Y => Ext.addEquiv₀.toAddCommGrpIso) (by
    intro Y Y' f
    ext e
    change Ext.addEquiv₀ (e.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ e ≫ f
    apply Ext.addEquiv₀.symm.injective
    simp only [AddEquiv.symm_apply_apply, Ext.addEquiv₀_symm_apply,
      ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply])

set_option backward.isDefEq.respectTransparency false in
/-- **`Ext` out of a fixed object transported along an exact functor, from acyclicity.** Let
`F : B ⥤ A` be exact, let `X : A` and `Y : B`, and suppose `Hom_B(Y, -)` is isomorphic to
`Hom_A(X, F -)`. If `F` carries every injective object of `B` to an object with no positive
`Ext` out of `X`, then `Ext_B^n(Y, -) ≅ F ⋙ Ext_A^n(X, -)`.

Both sides are δ-functors on `B` — `extDeltaFunctor (𝟭 B) Y` and `extDeltaFunctor F X` — and
both are universal: the first because `Ext^{≥1}` out of anything vanishes on an injective
object, the second by the hypothesis `h`. They agree in degree zero by `e`, so Stacks 010U
extends that identification to every degree.

This is the acyclicity form of
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp`, which instead asks `F` to preserve
injective objects. Acyclicity is the weaker hypothesis, and the only one available for the
inclusion of a subsite that is not closed under fibre products — the lisse-étale and flat-fppf
sites of Stacks 0787 among them. -/
public def extComparisonIso [EnoughInjectives B]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : A) (Y : B)
    (h : ∀ (I : B) [Injective I] (n : ℕ) (e : Ext X (F.obj I) (n + 1)), e = 0)
    (e : preadditiveCoyoneda.obj (op Y) ≅ F ⋙ preadditiveCoyoneda.obj (op X))
    (n : ℕ) : extFunctorObj Y n ≅ F ⋙ extFunctorObj X n := by
  let D := extDeltaFunctor (𝟭 B) Y
  let E := extDeltaFunctor F X
  have : D.IsUniversal := extDeltaFunctor_isUniversal (𝟭 B) Y
    (by
      intro I hI n a
      change Ext Y I (n + 1) at a
      exact Ext.eq_zero_of_injective a)
  have : E.IsUniversal := extDeltaFunctor_isUniversal F X h
  let e₀ : D.functor 0 ≅ E.functor 0 :=
    Functor.leftUnitor _ ≪≫ extZeroIsoCoyoneda Y ≪≫ e ≪≫
      Functor.isoWhiskerLeft F (extZeroIsoCoyoneda X).symm
  let α : D ≅ E := DeltaFunctor.IsUniversal.isoOfIso e₀
  exact (Functor.leftUnitor _).symm ≪≫
    { hom := α.hom.app n
      inv := α.inv.app n
      hom_inv_id := congrArg (fun η => η.app n) α.hom_inv_id
      inv_hom_id := congrArg (fun η => η.app n) α.inv_hom_id }

public def rightDerivedIso [HasInjectiveResolutions A]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

private def rightDerivedCoyonedaCompIso [HasInjectiveResolutions A]
    [HasInjectiveResolutions B] [EnoughInjectives B]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : A) (Y : B)
    (h : ∀ (I : B) [Injective I] (n : ℕ) (e : Ext X (F.obj I) (n + 1)), e = 0)
    (e : preadditiveCoyoneda.obj (op Y) ≅ F ⋙ preadditiveCoyoneda.obj (op X))
    (n : ℕ) :
    (F ⋙ preadditiveCoyoneda.obj (op X)).rightDerived (n + 1) ≅
      F ⋙ (preadditiveCoyoneda.obj (op X)).rightDerived (n + 1) :=
  rightDerivedIso e.symm (n + 1) ≪≫ rightDerivedCoyonedaSuccIso Y n ≪≫
    extComparisonIso F X Y h e (n + 1) ≪≫
      Functor.isoWhiskerLeft F (rightDerivedCoyonedaSuccIso X n).symm

/-- A represented left exact functor commutes with deriving after an exact functor when
its representing object has vanishing positive Ext against images of injectives. -/
private def rightDerivedCompIsoOfRepresentable [HasInjectiveResolutions A]
    [HasInjectiveResolutions B] [EnoughInjectives B]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : A ⥤ Ab.{v}) [G.Additive] (X : A) (Y : B)
    (h : ∀ (I : B) [Injective I] (n : ℕ) (e : Ext X (F.obj I) (n + 1)), e = 0)
    (α : G ≅ preadditiveCoyoneda.obj (op X))
    (β : preadditiveCoyoneda.obj (op Y) ≅ F ⋙ preadditiveCoyoneda.obj (op X))
    (n : ℕ) : (F ⋙ G).rightDerived (n + 1) ≅ F ⋙ G.rightDerived (n + 1) :=
  rightDerivedIso (Functor.isoWhiskerLeft F α) (n + 1) ≪≫
    rightDerivedCoyonedaCompIso F X Y h β n ≪≫
      Functor.isoWhiskerLeft F (rightDerivedIso α.symm (n + 1))

end ExtComparisonIso

universe u v u'

/-- Positive-degree comparison isomorphisms extend to a comparison normalized by the
canonical maps in degree zero. -/
private theorem exists_rightDerived_comp_iso_of_succ
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasInjectiveResolutions A] [HasInjectiveResolutions B]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteLimits (F ⋙ G)]
    (h : ∀ n : ℕ, Nonempty ((F ⋙ G).rightDerived (n + 1) ≅
      F ⋙ G.rightDerived (n + 1))) :
    ∃ e : ∀ n : ℕ, (F ⋙ G).rightDerived n ≅ F ⋙ G.rightDerived n,
      (F ⋙ G).toRightDerivedZero ≫ (e 0).hom =
        Functor.whiskerLeft F G.toRightDerivedZero := by
  classical
  refine ⟨(fun n => match n with
    | 0 => (F ⋙ G).rightDerivedZeroIsoSelf ≪≫
        Functor.isoWhiskerLeft F G.rightDerivedZeroIsoSelf.symm
    | n + 1 => (h n).some), ?_⟩
  simp

/-- **`Ext` out of a corepresenting object computes right-derived sections.** Let `G` be an
additive, left exact functor from an abelian category with injective resolutions to abelian
groups, corepresented by an object `X`. Then in every degree the right-derived functors of `G`
are the `Ext`-functors out of `X`. In degree zero this is the corepresentation composed with
left exactness of `G`; in positive degree it is `rightDerivedCoyonedaSuccIso`, the
identification of `Ext` in the second variable with the right-derived functors of
`preadditiveCoyoneda`, transported along the corepresentation by `rightDerivedIso`.

Only existence is asserted. The two degree ranges are built by different constructions, and no
compatibility between them — in particular no normalization in degree zero — is claimed; this
is the same weakening as in `exists_rightDerived_comp_iso_of_succ`. Stating existence also
keeps the construction's module-private ingredients out of the public interface. -/
@[sga "3 XXIV 1.13" "more general", sga "4 V 2.1.1" "more general"]
public theorem nonempty_extFunctorObj_iso_rightDerived
    {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]
    (G : A ⥤ Ab.{v}) [G.Additive] [PreservesFiniteLimits G] (X : A)
    (α : G ≅ preadditiveCoyoneda.obj (op X)) (n : ℕ) :
    Nonempty (extFunctorObj X n ≅ G.rightDerived n) := by
  cases n with
  | zero => exact ⟨extZeroIsoCoyoneda X ≪≫ α.symm ≪≫ G.rightDerivedZeroIsoSelf.symm⟩
  | succ n => exact ⟨(rightDerivedCoyonedaSuccIso X n).symm ≪≫ rightDerivedIso α.symm (n + 1)⟩

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Exact sheafification makes an injective module sheaf injective as a presheaf of
modules. -/
public theorem injective_forget_obj
    {D : Type*} [Category D] {K : GrothendieckTopology D}
    (R : Sheaf K RingCat.{u}) [HasSheafify K Ab.{v}]
    [K.WEqualsLocallyBijective Ab.{v}]
    (I : SheafOfModules.{v} R) [Injective I] :
    Injective ((SheafOfModules.forget R).obj I) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).map_injective I inferInstance

/-- Tensoring a short exact sequence with sectionwise torsion-free quotient preserves
the inclusion on the underlying presheaves. -/
private lemma mono_tensorPresheafMap_of_shortExact
    (R : Cᵒᵖ ⥤ RingCat.{u}) (S : ShortComplex (Sheaf J Ab.{u}))
    (hS : S.ShortExact) (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X)) :
    Mono (tensorPresheafMap R S.f.hom) := by
  have := hS.mono_f
  apply PresheafOfModules.mono_of_injective
  intro X
  have := hP X
  let E := sheafToPresheaf J Ab.{u} ⋙ (evaluation Cᵒᵖ Ab.{u}).obj X
  have hE : (S.map E).Exact :=
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp
      inferInstance S hS).1
  exact lTensor_injective_of_exact_of_isTorsionFree
    (S.f.hom.app X).hom.toIntLinearMap (S.g.hom.app X).hom.toIntLinearMap
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
    ((ShortComplex.ab_exact_iff_function_exact (S.map E)).mp hE) (R.obj X)

set_option backward.isDefEq.respectTransparency false in
/-- Maps to the underlying abelian sheaf of an injective module sheaf extend across
short exact sequences with sectionwise torsion-free quotient. -/
public lemma exists_extension_of_isTorsionFree
    (R : Sheaf J RingCat.{u}) (I : SheafOfModules.{u} R) [Injective I]
    (S : ShortComplex (Sheaf J Ab.{u})) (hS : S.ShortExact)
    (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X))
    (f : S.X₁ ⟶ (SheafOfModules.toSheaf R).obj I) :
    ∃ g : S.X₂ ⟶ (SheafOfModules.toSheaf R).obj I, S.f ≫ g = f := by
  have : Injective I.val := injective_forget_obj R I
  have := mono_tensorPresheafMap_of_shortExact J R.obj S hS hP
  let g := Injective.factorThru (tensorPresheafLift R.obj f.hom)
    (tensorPresheafMap R.obj S.f.hom)
  refine ⟨⟨tensorPresheafUnit R.obj S.X₂.obj ≫
    (PresheafOfModules.toPresheaf R.obj).map g⟩, ?_⟩
  apply Sheaf.hom_ext
  show S.f.hom ≫ tensorPresheafUnit R.obj S.X₂.obj ≫
    (PresheafOfModules.toPresheaf R.obj).map g = f.hom
  rw [← Category.assoc, tensorPresheafUnit_naturality, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  dsimp [g]
  rw [Injective.comp_factorThru, tensorPresheafUnit_comp_lift]

/-- The underlying abelian sheaf of an injective module sheaf is Ext-acyclic against
every sectionwise torsion-free sheaf. -/
public lemma ext_eq_zero_of_isTorsionFree
    (R : Sheaf J RingCat.{u}) (I : SheafOfModules.{u} R) [Injective I]
    (X : Sheaf J Ab.{u}) (hX : ∀ U, Module.IsTorsionFree ℤ (X.obj.obj U))
    (n : ℕ) (e : Ext.{u} X ((SheafOfModules.toSheaf R).obj I) (n + 1)) : e = 0 := by
  apply ext_eq_zero_of_resolving (fun F : Sheaf J Ab.{u} =>
    ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U)) ?_ (exists_isTorsionFree_epi J)
    ((SheafOfModules.toSheaf R).obj I) ?_ n X hX e
  · intro F G f hf hG
    exact isTorsionFree_of_mono J f hG
  · apply ext_one_eq_zero_of_extension
    intro S hS hP f
    exact exists_extension_of_isTorsionFree J R I S hS hP f

local instance : (Sheaf.Γ J Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance (U : C) : ((sheafSections J Ab.{u}).obj (op U)).Additive where
  map_add := by intros; rfl

local instance (U : C) :
    PreservesFiniteLimits ((sheafSections J Ab.{u}).obj (op U)) :=
  preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J Ab.{u}).symm

local instance toSheaf_preservesFiniteColimits (R : Sheaf J RingCat.{u}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) := by
  let sheafification := PresheafOfModules.sheafification (𝟙 R.obj)
  let adjunction := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let counitIso := asIso adjunction.counit
  have composite : PreservesFiniteColimits (sheafification ⋙ SheafOfModules.toSheaf R) := by
    exact preservesFiniteColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  let : PreservesColimitsOfSize.{0, 0} sheafification :=
    adjunction.leftAdjoint_preservesColimits
  refine ⟨fun {index} _ _ => ⟨fun {diagram} => ?_⟩⟩
  let forgetful := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have comparison : (diagram ⋙ forgetful) ⋙ sheafification ≅ diagram :=
    NatIso.ofComponents (fun point => counitIso.app (diagram.obj point)) (by
      intro source target map
      exact counitIso.hom.naturality (diagram.map map))
  have : PreservesColimit (diagram ⋙ forgetful)
      (sheafification ⋙ SheafOfModules.toSheaf R) :=
    (composite.preservesFiniteColimits index).preservesColimit
  have : PreservesColimit ((diagram ⋙ forgetful) ⋙ sheafification)
      (SheafOfModules.toSheaf R) := by
    apply preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves sheafification (colimit.isColimit (diagram ⋙ forgetful)))
    exact isColimitOfPreserves (sheafification ⋙ SheafOfModules.toSheaf R)
      (colimit.isColimit (diagram ⋙ forgetful))
  exact preservesColimit_of_iso_diagram _ comparison

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms out of the sheafified extension of scalars of an abelian presheaf `P` are the
morphisms out of the sheafification of `P` into the underlying abelian sheaf. -/
@[no_expose]
public def tensorSheafHomIso (R : Sheaf J RingCat.{u})
    (P : Cᵒᵖ ⥤ Ab.{u}) :
    preadditiveCoyoneda.obj (op
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (tensorPresheaf R.obj P))) ≅
    SheafOfModules.toSheaf R ⋙ preadditiveCoyoneda.obj
      (op ((presheafToSheaf J Ab.{u}).obj P)) := by
  letI : (PresheafOfModules.sheafification (𝟙 R.obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).left_adjoint_additive
  refine NatIso.ofComponents (fun M => ?_) ?_
  · exact (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homAddEquiv
      (tensorPresheaf R.obj P) M).trans
      ((tensorPresheafHomAddEquiv R.obj P
        ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M)).trans
        ((sheafificationAdjunction J Ab.{u}).homAddEquiv P
          ((SheafOfModules.toSheaf R).obj M)).symm)).toAddCommGrpIso
  · intro M N map
    ext element
    change ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
      (tensorPresheaf R.obj P) ⟶ M) at element
    apply ((sheafificationAdjunction J Ab.{u}).homEquiv P
      ((SheafOfModules.toSheaf R).obj N)).injective
    change ((sheafificationAdjunction J Ab.{u}).homEquiv P
      ((SheafOfModules.toSheaf R).obj N))
      ((((sheafificationAdjunction J Ab.{u}).homEquiv P
        ((SheafOfModules.toSheaf R).obj N)).symm
        ((tensorPresheafHomAddEquiv R.obj P
          ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj N))
          ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ N
            (element ≫ map))))) =
      ((sheafificationAdjunction J Ab.{u}).homEquiv P
        ((SheafOfModules.toSheaf R).obj N))
        (((sheafificationAdjunction J Ab.{u}).homEquiv P
          ((SheafOfModules.toSheaf R).obj M)).symm
          ((tensorPresheafHomAddEquiv R.obj P
            ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M))
            ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ M element)) ≫
          (SheafOfModules.toSheaf R).map map)
    conv_rhs =>
      rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    erw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
    simp [tensorPresheafHomAddEquiv]
    rfl

/-- **`tensorSheafHomIso` is natural in the abelian presheaf.** A morphism `p : P ⟶ P'` of
abelian presheaves induces `tensorPresheafMap` on the extensions of scalars, hence a morphism of
the sheafified extensions of scalars, and `presheafToSheaf.map p` on the sheafifications; the two
identifications of morphisms out of the sheafified extension of scalars with morphisms out of the
sheafification intertwine these.

Both sides are read through the three isomorphisms `tensorSheafHomIso` is built from, where the
statement is naturality of each in its left argument: `homEquiv_naturality_left` for the
sheafification of module presheaves, `tensorPresheafUnit_naturality` for extension of scalars,
and `homEquiv_naturality_left_symm` for the sheafification of abelian presheaves. -/
public lemma tensorSheafHomIso_naturality (R : Sheaf J RingCat.{u})
    {P P' : Cᵒᵖ ⥤ Ab.{u}} (p : P ⟶ P') :
    preadditiveCoyoneda.map
        ((PresheafOfModules.sheafification (𝟙 R.obj)).map (tensorPresheafMap R.obj p)).op ≫
        (tensorSheafHomIso J R P).hom =
      (tensorSheafHomIso J R P').hom ≫
        Functor.whiskerLeft (SheafOfModules.toSheaf R)
          (preadditiveCoyoneda.map ((presheafToSheaf J Ab.{u}).map p).op) := by
  refine NatTrans.ext (funext fun M => ?_)
  ext element
  change ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (tensorPresheaf R.obj P') ⟶ M)
    at element
  show ((sheafificationAdjunction J Ab.{u}).homEquiv P
        ((SheafOfModules.toSheaf R).obj M)).symm
        ((tensorPresheafHomAddEquiv R.obj P
          ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M))
          ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ M
            ((PresheafOfModules.sheafification (𝟙 R.obj)).map (tensorPresheafMap R.obj p) ≫
              element))) =
      (presheafToSheaf J Ab.{u}).map p ≫
        ((sheafificationAdjunction J Ab.{u}).homEquiv P'
          ((SheafOfModules.toSheaf R).obj M)).symm
          ((tensorPresheafHomAddEquiv R.obj P'
            ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M))
            ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ M element))
  have key : (tensorPresheafHomAddEquiv R.obj P
        ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M))
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          (tensorPresheaf R.obj P) M
          ((PresheafOfModules.sheafification (𝟙 R.obj)).map (tensorPresheafMap R.obj p) ≫
            element)) =
      p ≫ (tensorPresheafHomAddEquiv R.obj P'
        ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M))
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
          (tensorPresheaf R.obj P') M element) := by
    rw [Adjunction.homEquiv_naturality_left]
    show tensorPresheafUnit R.obj P ≫ (PresheafOfModules.toPresheaf R.obj).map
        (tensorPresheafMap R.obj p ≫ _) =
      p ≫ tensorPresheafUnit R.obj P' ≫ (PresheafOfModules.toPresheaf R.obj).map _
    rw [Functor.map_comp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (PresheafOfModules.toPresheaf R.obj).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
            (tensorPresheaf R.obj P') M element))
        (tensorPresheafUnit_naturality R.obj p).symm).trans (Category.assoc _ _ _))
  exact (congrArg (fun m => ((sheafificationAdjunction J Ab.{u}).homEquiv P
      ((SheafOfModules.toSheaf R).obj M)).symm m) key).trans
    ((sheafificationAdjunction J Ab.{u}).homEquiv_naturality_left_symm p _)

/-- A corepresented additive functor on abelian sheaves, whose corepresenting object is the
sheafification of a sectionwise torsion-free presheaf, commutes in positive degree with deriving
after the forgetful functor from module sheaves. -/
private theorem represented_succ_comparison (R : Sheaf J RingCat.{u})
    (P : Cᵒᵖ ⥤ Ab.{u}) (hP : ∀ point, Module.IsTorsionFree ℤ (P.obj point))
    (G : Sheaf J Ab.{u} ⥤ Ab.{u}) [G.Additive]
    (representation : G ≅ preadditiveCoyoneda.obj
      (op ((presheafToSheaf J Ab.{u}).obj P))) (degree : ℕ) :
    Nonempty ((SheafOfModules.toSheaf R ⋙ G).rightDerived (degree + 1) ≅
      SheafOfModules.toSheaf R ⋙ G.rightDerived (degree + 1)) := by
  refine ⟨rightDerivedCompIsoOfRepresentable (SheafOfModules.toSheaf R) G
    ((presheafToSheaf J Ab.{u}).obj P)
    ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (tensorPresheaf R.obj P))
    ?_ representation (tensorSheafHomIso J R P) degree⟩
  intro injectiveObject instanceInjective index extension
  exact ext_eq_zero_of_isTorsionFree J R injectiveObject _
    (isTorsionFree_sheafify J P hP) index extension

set_option backward.isDefEq.respectTransparency false in
/-- Global sections of abelian sheaves are corepresented by the constant sheaf on `ℤ`. -/
public def globalSectionsRepresentation :
    Sheaf.Γ J Ab.{u} ≅ preadditiveCoyoneda.obj
      (op ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) := by
  refine (NatIso.ofComponents (fun F =>
    (((constantSheafΓAdj J Ab.{u}).homAddEquiv (AddCommGrpCat.of (ULift.{u} ℤ)) F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toAddCommGrpIso) ?_).symm
  intro F G map
  ext element
  change ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ F) at element
  change ((constantSheafΓAdj J Ab.{u}).homEquiv _ G (element ≫ map)) (ULift.up (1 : ℤ)) =
    ((Sheaf.Γ J Ab.{u}).map map)
      (((constantSheafΓAdj J Ab.{u}).homEquiv _ F element) (ULift.up (1 : ℤ)))
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The free abelian presheaf on `yoneda.obj U` corepresents evaluation at `U`.

Stated for a site whose objects form a type of any universe, since the equivalence uses only
the category structure of `C`; the surrounding section fixes a small site. -/
@[sga "4 Vbis 2.3.1" "partial"]
public def freeEvaluationHomAddEquiv {C : Type u'} [Category.{u} C] (U : C) (F : Cᵒᵖ ⥤ Ab.{u}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ F) ≃+ F.obj (op U) where
  toFun map := map.app (op U) (FreeAbelianGroup.of (𝟙 U))
  invFun element :=
    { app point := AddCommGrpCat.ofHom
        (FreeAbelianGroup.lift (fun arrow : point.unop ⟶ U => F.map arrow.op element))
      naturality source target arrow := by
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro generator
        change FreeAbelianGroup.lift _
          (FreeAbelianGroup.map _ (FreeAbelianGroup.of generator)) =
            F.map arrow (FreeAbelianGroup.lift _ (FreeAbelianGroup.of generator))
        simp }
  left_inv map := by
    apply NatTrans.ext
    funext point
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro generator
    change FreeAbelianGroup.lift (fun arrow : point.unop ⟶ U =>
      F.map arrow.op (map.app (op U) (FreeAbelianGroup.of (𝟙 U))))
      (FreeAbelianGroup.of generator) = map.app point (FreeAbelianGroup.of generator)
    rw [FreeAbelianGroup.lift_apply_of]
    have naturality := (ConcreteCategory.congr_hom (map.naturality generator.op)
      (FreeAbelianGroup.of (𝟙 U))).symm
    change F.map generator.op (map.app (op U) (FreeAbelianGroup.of (𝟙 U))) =
      map.app point (FreeAbelianGroup.map (fun arrow => generator ≫ arrow)
        (FreeAbelianGroup.of (𝟙 U))) at naturality
    simpa using naturality
  right_inv element := by
    change FreeAbelianGroup.lift (fun arrow : U ⟶ U => F.map arrow.op element)
      (FreeAbelianGroup.of (𝟙 U)) = element
    simp
  map_add' first second := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Sections of abelian sheaves over `U` are corepresented by the sheafification of the free
abelian presheaf on `yoneda.obj U`. -/
public def evaluationRepresentation (U : C) :
    (sheafSections J Ab.{u}).obj (op U) ≅ preadditiveCoyoneda.obj
      (op ((presheafToSheaf J Ab.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free))) := by
  refine (NatIso.ofComponents (fun F =>
    (((sheafificationAdjunction J Ab.{u}).homAddEquiv
      (yoneda.obj U ⋙ AddCommGrpCat.free) F).trans
      (freeEvaluationHomAddEquiv U F.obj)).toAddCommGrpIso) ?_).symm
  intro F G map
  ext element
  change ((presheafToSheaf J Ab.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) at element
  change freeEvaluationHomAddEquiv U G.obj
    ((sheafificationAdjunction J Ab.{u}).homEquiv _ G (element ≫ map)) =
    map.hom.app (op U) (freeEvaluationHomAddEquiv U F.obj
      ((sheafificationAdjunction J Ab.{u}).homEquiv _ F element))
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- **The acyclicity input of Stacks 03FD, for sections over an object of the site.** The
underlying abelian sheaf of an injective module sheaf has vanishing higher `Ext` against the
sheafification of the free abelian presheaf on `yoneda.obj U`, which is the object
corepresenting sections over `U` by `evaluationRepresentation`. The free abelian presheaf is
sectionwise torsion free, so `ext_eq_zero_of_isTorsionFree` applies to its sheafification. -/
public theorem ext_eq_zero_of_injective_toSheaf (R : Sheaf J RingCat.{u})
    (I : SheafOfModules.{u} R) [Injective I] (U : C) (n : ℕ)
    (e : Ext.{u} ((presheafToSheaf J Ab.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free))
      ((SheafOfModules.toSheaf R).obj I) (n + 1)) :
    e = 0 :=
  ext_eq_zero_of_isTorsionFree J R I _
    (isTorsionFree_sheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)
      (fun _ => isTorsionFree_free_obj _)) n e

/-- **Stacks 03FD.** For a sheaf of rings `R` on a site, deriving sections in the category of
`R`-module sheaves and then forgetting to abelian groups gives the same cohomology as first
forgetting to an abelian sheaf and deriving there. The comparison is natural in the module
sheaf, holds globally and over every object of the site, and is compatible in degree zero with
the canonical maps to right-derived functors. -/
@[stacks 03FD, stacks 03F2 "the degree one case", sga "4 V 3.5"]
public theorem moduleSheafCohomologyIsoUnderlying (R : Sheaf J RingCat.{u}) :
    ∃ eSite : ∀ i : ℕ,
        (SheafOfModules.toSheaf.{u} R ⋙ Sheaf.Γ J Ab.{u}).rightDerived i ≅
          SheafOfModules.toSheaf.{u} R ⋙ (Sheaf.Γ J Ab.{u}).rightDerived i,
      (SheafOfModules.toSheaf.{u} R ⋙ Sheaf.Γ J Ab.{u}).toRightDerivedZero ≫
          (eSite 0).hom =
        Functor.whiskerLeft (SheafOfModules.toSheaf.{u} R)
          (Sheaf.Γ J Ab.{u}).toRightDerivedZero ∧
      ∀ U : C,
        ∃ eU : ∀ i : ℕ,
            (SheafOfModules.toSheaf.{u} R ⋙
                (sheafSections J Ab.{u}).obj (op U)).rightDerived i ≅
              SheafOfModules.toSheaf.{u} R ⋙
                ((sheafSections J Ab.{u}).obj (op U)).rightDerived i,
          (SheafOfModules.toSheaf.{u} R ⋙
                (sheafSections J Ab.{u}).obj (op U)).toRightDerivedZero ≫
              (eU 0).hom =
            Functor.whiskerLeft (SheafOfModules.toSheaf.{u} R)
              ((sheafSections J Ab.{u}).obj (op U)).toRightDerivedZero := by
  obtain ⟨eSite, heSite⟩ := exists_rightDerived_comp_iso_of_succ
    (SheafOfModules.toSheaf.{u} R) (Sheaf.Γ J Ab.{u})
    (represented_succ_comparison J R
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
      (fun _ => by
        show Module.IsTorsionFree ℤ (ULift.{u} ℤ)
        exact Module.Flat.isTorsionFree) (Sheaf.Γ J Ab.{u}) (globalSectionsRepresentation J))
  refine ⟨eSite, heSite, ?_⟩
  intro U
  exact exists_rightDerived_comp_iso_of_succ
    (SheafOfModules.toSheaf.{u} R) ((sheafSections J Ab.{u}).obj (op U))
    (represented_succ_comparison J R (yoneda.obj U ⋙ AddCommGrpCat.free)
      (fun _ => isTorsionFree_free_obj _) ((sheafSections J Ab.{u}).obj (op U))
      (evaluationRepresentation J U))

end ModuleSheafCohomology

end
