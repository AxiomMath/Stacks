module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian

/-!
# Extension of scalars as a left adjoint, with the ring and coefficient universes independent

Let `R` be a presheaf of rings in `RingCat.{r}` on a category `D`.  Extension of scalars
`F ↦ R ⊗_ℤ F` from abelian presheaves to presheaves of `R`-modules is
`Stacks.SheafOfModules.tensorPresheaf`, which already takes the coefficients in a universe
`max r t` independent of the universes of `D`.  This file adds the rest of the adjunction data —
the unit, the functoriality in the abelian presheaf, and the resulting hom-equivalence and
corepresentation isomorphism — and then the two consequences that need them: the `Ext`-acyclicity
of the underlying abelian sheaf of an injective sheaf of modules, and the identification of
morphisms out of the sheafified extension of scalars with morphisms out of the sheafification.

Both consequences are already in the library with the ring universe and the module universe tied
together: `ModuleSheafCohomology.ext_eq_zero_of_isTorsionFree` and
`ModuleSheafCohomology.tensorSheafHomIso` for a site whose objects form a small type, and
`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree` with the universes of the site
free but still `R` in `RingCat.{v}` and the modules in `SheafOfModules.{v} R`.  Neither applies
to the small crystalline site `Cris(X/S)` of a global crystalline situation at level `u`, whose
structure sheaf is valued in `RingCat.{u}` while its modules have sections in `Type (u + 1)`;
that is the case `r = u`, `t = u + 1` here.

## Main definitions

* `Stacks.SheafOfModules.tensorPresheafUnit`: the additive map `F ⟶ R ⊗_ℤ F`.
* `Stacks.SheafOfModules.tensorPresheafMap`: extension of scalars on a morphism.
* `Stacks.SheafOfModules.tensorPresheafHomAddEquiv`: `R`-linear maps out of `R ⊗_ℤ F` are
  additive maps out of `F`.
* `Stacks.SheafOfModules.tensorPresheafCoyonedaIso`: the same, as an isomorphism of functors to
  abelian groups.
* `Stacks.SheafOfModules.tensorSheafHomIso`: morphisms out of the sheafified extension of
  scalars of an abelian presheaf `P` are the morphisms out of the sheafification of `P` into the
  underlying abelian sheaf.

## Main results

* `Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree`: **the acyclicity input of
  [Stacks, Tag 03FD]** at independent ring and module universes — the underlying abelian sheaf of
  an injective sheaf of modules has vanishing positive-degree `Ext` against every sectionwise
  torsion-free abelian sheaf.

## Implementation notes

The proofs are those of `Stacks.Cohomology.ObjectSections`, with the diagonal extension of
scalars replaced by the one of `Stacks.SheafOfModules`; the universe split is the only change.
The coefficient universe is written `max r t` rather than as a free variable because the carrier
of `R.obj X ⊗[ℤ] F.obj X` lies in the maximum of the ring and coefficient universes, and the
`max` is how `r ≤` coefficient universe is said to the elaborator.

`tensorSheafHomIso` is a composite of three corepresentations transported along adjunctions —
the sheafification adjunction for presheaves of modules, `tensorPresheafCoyonedaIso`, and the
sheafification adjunction for abelian presheaves — rather than a single hand-built natural
isomorphism, which is what keeps it short.  The two sheafification adjunctions have left adjoints
between categories with the same morphism universe, which is what
`Stacks.Cohomology.ObjectSections.coyonedaAdjunctionIso` requires and what the universe split
preserves.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian TensorProduct

namespace Stacks.SheafOfModules

/-! ### The adjunction data of extension of scalars -/

section ExtendScalars

universe w v t r

variable {D : Type w} [Category.{v} D] (R : Dᵒᵖ ⥤ RingCat.{r})

/-- Restriction in `R ⊗_ℤ F` on a pure tensor. -/
lemma tensorPresheaf_map_tmul (F : Dᵒᵖ ⥤ Ab.{max r t}) {X Y : Dᵒᵖ} (f : X ⟶ Y)
    (a : R.obj X) (x : F.obj X) :
    (tensorPresheaf R F).map f (a ⊗ₜ[ℤ] x) = R.map f a ⊗ₜ[ℤ] F.map f x :=
  TensorProduct.map_tmul _ _ _ _

/-- **Extension of scalars on a morphism** of abelian presheaves: `R ⊗_ℤ (-)` applied to
`f : F ⟶ G`, which is the identity on the ring factor. -/
def tensorPresheafMap {F G : Dᵒᵖ ⥤ Ab.{max r t}} (f : F ⟶ G) :
    tensorPresheaf R F ⟶ tensorPresheaf R G where
  app X := ModuleCat.ofHom (AlgebraTensorModule.map (LinearMap.id : R.obj X →ₗ[R.obj X] R.obj X)
    (f.app X).hom.toIntLinearMap)
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change R.map g a ⊗ₜ[ℤ] f.app Y (F.map g x) = R.map g a ⊗ₜ[ℤ] G.map g (f.app X x)
    rw [NatTrans.naturality_apply]

/-- **The unit of extension of scalars**: the additive map `F ⟶ R ⊗_ℤ F` sending a section `x`
to `1 ⊗ x`. -/
def tensorPresheafUnit (F : Dᵒᵖ ⥤ Ab.{max r t}) :
    F ⟶ (tensorPresheaf R F).presheaf where
  app X := AddCommGrpCat.ofHom ((TensorProduct.mk ℤ (R.obj X) (F.obj X) 1).toAddMonoidHom)
  naturality {X Y} f := by
    ext x
    change 1 ⊗ₜ[ℤ] F.map f x = (tensorPresheaf R F).map f (1 ⊗ₜ[ℤ] x)
    rw [tensorPresheaf_map_tmul, map_one]

/-- The unit followed by the linear extension of an additive map is that map again. -/
lemma tensorPresheafUnit_comp_lift {F : Dᵒᵖ ⥤ Ab.{max r t}}
    {M : PresheafOfModules.{max r t} R} (f : F ⟶ M.presheaf) :
    tensorPresheafUnit R F ≫ (PresheafOfModules.toPresheaf R).map
      (tensorPresheafLift R f) = f := by
  ext X x
  show (tensorPresheafLift R f).app X (1 ⊗ₜ[ℤ] x) = f.app X x
  rw [tensorPresheafLift_app_tmul, one_smul]

/-- The unit is natural in the abelian presheaf. -/
lemma tensorPresheafUnit_naturality {F G : Dᵒᵖ ⥤ Ab.{max r t}} (f : F ⟶ G) :
    f ≫ tensorPresheafUnit R G = tensorPresheafUnit R F ≫
      (PresheafOfModules.toPresheaf R).map (tensorPresheafMap R f) := by
  ext X x
  rfl

/-- The value of an `R`-linear map out of `R ⊗_ℤ F` on a pure tensor is determined by its
restriction along the unit. -/
lemma tensorPresheafHom_app_tmul {F : Dᵒᵖ ⥤ Ab.{max r t}}
    {M : PresheafOfModules.{max r t} R} (f : tensorPresheaf R F ⟶ M) (X : Dᵒᵖ)
    (a : R.obj X) (x : F.obj X) :
    f.app X (a ⊗ₜ[ℤ] x) = a • (show M.obj X from f.app X (1 ⊗ₜ[ℤ] x)) := by
  have h : a • (1 : R.obj X) ⊗ₜ[ℤ] x = a ⊗ₜ[ℤ] x := by
    show (a * 1) ⊗ₜ[ℤ] x = a ⊗ₜ[ℤ] x
    rw [mul_one]
  exact ((congrArg (f.app X) h).symm.trans ((f.app X).hom.map_smul a _))

/-- **Freeness of extension of scalars, as a hom-equivalence**: `R`-linear maps `R ⊗_ℤ F ⟶ M`
are additive maps `F ⟶ M`. -/
def tensorPresheafHomAddEquiv (F : Dᵒᵖ ⥤ Ab.{max r t})
    (M : PresheafOfModules.{max r t} R) :
    (tensorPresheaf R F ⟶ M) ≃+ (F ⟶ M.presheaf) where
  toFun f := tensorPresheafUnit R F ≫ (PresheafOfModules.toPresheaf R).map f
  invFun := tensorPresheafLift R
  left_inv f := by
    ext1 X
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    exact (tensorPresheafHom_app_tmul R f X a x).symm
  right_inv := tensorPresheafUnit_comp_lift R
  map_add' f g := by
    ext X x
    rfl

/-- **Extension of scalars corepresents additive maps out of the abelian presheaf**, naturally
in the presheaf of modules. -/
def tensorPresheafCoyonedaIso (P : Dᵒᵖ ⥤ Ab.{max r t}) :
    preadditiveCoyoneda.obj (op (tensorPresheaf R P)) ≅
      PresheafOfModules.toPresheaf R ⋙ preadditiveCoyoneda.obj (op P) :=
  NatIso.ofComponents (fun M => (tensorPresheafHomAddEquiv R P M).toAddCommGrpIso)
    (fun {M N} map => by
      ext φ
      exact ((congrArg (tensorPresheafUnit R P ≫ ·)
        ((PresheafOfModules.toPresheaf R).map_comp φ map)).trans (Category.assoc _ _ _).symm))

end ExtendScalars

/-! ### `Ext`-acyclicity of the underlying abelian sheaf of an injective sheaf of modules -/

section Acyclicity

universe e t r v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{max r t}] [J.WEqualsLocallyBijective Ab.{max r t}]

omit [J.WEqualsLocallyBijective Ab.{max r t}] in
/-- Tensoring a short exact sequence of abelian sheaves whose last term is sectionwise
torsion-free by a presheaf of rings preserves the inclusion on the underlying presheaves. -/
private lemma mono_tensorPresheafMap_of_shortExact
    (R : Cᵒᵖ ⥤ RingCat.{r}) (S : ShortComplex (Sheaf J Ab.{max r t}))
    (hS : S.ShortExact) (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X)) :
    Mono (tensorPresheafMap R S.f.hom) := by
  have := hS.mono_f
  apply PresheafOfModules.mono_of_injective
  intro X
  have := hP X
  let E := sheafToPresheaf J Ab.{max r t} ⋙ (evaluation Cᵒᵖ Ab.{max r t}).obj X
  exact ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree
    (S.f.hom.app X).hom.toIntLinearMap (S.g.hom.app X).hom.toIntLinearMap
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
    ((ShortComplex.ab_exact_iff_function_exact (S.map E)).mp
      ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp
        inferInstance S hS).1) (R.obj X)

/-- Morphisms to the underlying abelian sheaf of an injective sheaf of modules extend across a
short exact sequence whose last term is sectionwise torsion-free. -/
private lemma exists_extension_of_isTorsionFree
    (R : Sheaf J RingCat.{r}) (I : SheafOfModules.{max r t} R) [Injective I]
    (S : ShortComplex (Sheaf J Ab.{max r t})) (hS : S.ShortExact)
    (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X))
    (f : S.X₁ ⟶ (SheafOfModules.toSheaf R).obj I) :
    ∃ g : S.X₂ ⟶ (SheafOfModules.toSheaf R).obj I, S.f ≫ g = f := by
  have : Injective I.val := ModuleSheafCohomology.injective_forget_obj R I
  have := mono_tensorPresheafMap_of_shortExact J R.obj S hS hP
  let fp : S.X₁.obj ⟶ (PresheafOfModules.toPresheaf R.obj).obj I.val := f.hom
  let g := Injective.factorThru (tensorPresheafLift R.obj fp)
    (tensorPresheafMap R.obj S.f.hom)
  have hg : tensorPresheafMap R.obj S.f.hom ≫ g = tensorPresheafLift R.obj fp :=
    Injective.comp_factorThru _ _
  have key : S.f.hom ≫ tensorPresheafUnit R.obj S.X₂.obj ≫
      (PresheafOfModules.toPresheaf R.obj).map g = fp := by
    erw [← Category.assoc, tensorPresheafUnit_naturality, Category.assoc, ← Functor.map_comp, hg,
      tensorPresheafUnit_comp_lift]
  exact ⟨⟨tensorPresheafUnit R.obj S.X₂.obj ≫
    (PresheafOfModules.toPresheaf R.obj).map g⟩, Sheaf.hom_ext key⟩

/-- **The acyclicity input of [Stacks, Tag 03FD], with the ring universe and the module universe
independent.**  The underlying abelian sheaf of an injective sheaf of modules has vanishing
positive-degree `Ext` against every sectionwise torsion-free abelian sheaf.

`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree` is the same statement with the
structure sheaf and the modules in one universe; here the structure sheaf is valued in
`RingCat.{r}` and the modules have sections in `Type (max r t)`. -/
theorem ext_eq_zero_of_isTorsionFree [HasExt.{e} (Sheaf J Ab.{max r t})]
    [EnoughInjectives (Sheaf J Ab.{max r t})]
    (R : Sheaf J RingCat.{r}) (I : SheafOfModules.{max r t} R) [Injective I]
    (X : Sheaf J Ab.{max r t}) (hX : ∀ U, Module.IsTorsionFree ℤ (X.obj.obj U))
    (n : ℕ) (e : Ext.{e} X ((SheafOfModules.toSheaf R).obj I) (n + 1)) : e = 0 := by
  apply ModuleSheafCohomology.ext_eq_zero_of_resolving (fun F : Sheaf J Ab.{max r t} =>
    ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U)) ?_
    (ModuleSheafCohomology.exists_isTorsionFree_epi J)
    ((SheafOfModules.toSheaf R).obj I) ?_ n X hX e
  · intro F G f hf hG
    exact ModuleSheafCohomology.isTorsionFree_of_mono J f hG
  · apply ModuleSheafCohomology.ext_one_eq_zero_of_extension
    intro S hS hP f
    exact exists_extension_of_isTorsionFree J R I S hS hP f

end Acyclicity

/-! ### Morphisms out of the sheafified extension of scalars -/

section SheafifiedExtension

universe t r v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{max r t}] [J.WEqualsLocallyBijective Ab.{max r t}]

/-- **Morphisms out of the sheafified extension of scalars of an abelian presheaf `P` are the
morphisms out of the sheafification of `P` into the underlying abelian sheaf**, with the ring
universe and the module universe independent.

This is the corepresentation half of [Stacks, Tag 03FD]: it exhibits the composite of
`SheafOfModules.toSheaf` with the functor corepresented by the sheafification of `P` as itself
corepresented, by a sheaf of modules.  Both sides are corepresentations transported along an
adjunction, so the identification is the composite of the sheafification adjunction for
presheaves of modules, `tensorPresheafCoyonedaIso`, and the sheafification adjunction for
abelian presheaves. -/
def tensorSheafHomIso (R : Sheaf J RingCat.{r}) (P : Cᵒᵖ ⥤ Ab.{max r t}) :
    preadditiveCoyoneda.obj (op
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj (tensorPresheaf R.obj P))) ≅
    SheafOfModules.toSheaf R ⋙ preadditiveCoyoneda.obj
      (op ((presheafToSheaf J Ab.{max r t}).obj P)) :=
  have : (PresheafOfModules.sheafification (𝟙 R.obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).left_adjoint_additive
  have : (presheafToSheaf J Ab.{max r t}).Additive :=
    (sheafificationAdjunction J Ab.{max r t}).left_adjoint_additive
  (Stacks.Cohomology.ObjectSections.coyonedaAdjunctionIso
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) (tensorPresheaf R.obj P)).symm ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.forget R ⋙
        PresheafOfModules.restrictScalars (𝟙 R.obj)) (tensorPresheafCoyonedaIso R.obj P) ≪≫
      Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
        (Stacks.Cohomology.ObjectSections.coyonedaAdjunctionIso
          (sheafificationAdjunction J Ab.{max r t}) P)

end SheafifiedExtension

end Stacks.SheafOfModules

end
