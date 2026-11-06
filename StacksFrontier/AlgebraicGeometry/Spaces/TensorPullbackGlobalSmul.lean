module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightScalar
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSupportHomFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes

/-!
# Scalars on `𝒢 ⊗ f^*M^~`

Let `f : X ⟶ U` be a morphism from an algebraic space to an object `U` of the site whose scheme
is affine, with ring of functions `R = Γ(U, 𝒪_U)`, let `𝒢` be an `𝒪_X`-module, and consider the
functor `M ↦ 𝒢 ⊗ f^*M^~` from `R`-modules to `𝒪_X`-modules. This file shows how scalars act on
it:

* tensoring with `𝒢` and pulling back along `f` commute with multiplication by the functions
  pulled back from `U`;
* on the free module of rank one, every multiplication by a function of `U` comes from a
  scalar of `R`, the associated-module functor being fully faithful.

## Main results

* `Stacks.sheafTensorObj_map_globalSectionToEnd`: `F ⊗ -` carries multiplication by a compatible
  family of local sections to itself.
* `AlgebraicGeometry.Space.tensorPullbackBifunctor_obj_map_globalSmul`: `𝒢 ⊗ f^*(-)` carries
  multiplication by a function `h^♯ x` of `Y` to multiplication by `(f ≫ h)^♯ x`.
* `AlgebraicGeometry.Space.exists_representedAffineAssociated_map_smul_eq_globalSmul`: on the free
  module of rank one, every multiplication by a pulled-back function of `U` is the associated map
  of a scalar.
* `Module.finite_of_addEquiv_of_forall_exists_smul`: finiteness passes along an additive
  equivalence as soon as every scalar of the target acts as some scalar of the source.
* `AlgebraicGeometry.Space.tensorPullbackRepresentedAffineUnitIso`: `𝒢 ⊗ f^*R^~ ≅ 𝒢`.

## References

* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
* [Stacks Project, Tag 0CZW](https://stacks.math.columbia.edu/tag/0CZW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct IsMulCommutative

universe v u w

/-- **Comparison of two module structures along an additive equivalence.** Let `e : M ≃+ N` be
an additive equivalence from an `S`-module to a finite `R`-module. If every scalar `r ∈ R` acts
on `N` as some scalar `s ∈ S` acts on `M`, that is `e (s • m) = r • e m`, then `M` is a finite
`S`-module. -/
theorem Module.finite_of_addEquiv_of_forall_exists_smul {R S M N : Type*} [Semiring R]
    [Semiring S] [AddCommMonoid M] [Module S M] [AddCommMonoid N] [Module R N]
    [Module.Finite R N] (e : M ≃+ N) (h : ∀ r : R, ∃ s : S, ∀ m : M, e (s • m) = r • e m) :
    Module.Finite S M := by
  classical
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule R N).FG)
  refine ⟨⟨t.image e.symm, eq_top_iff.2 fun m _ => ?_⟩⟩
  have hm : e m ∈ Submodule.span R (t : Set N) := ht ▸ Submodule.mem_top
  suffices H : ∀ n ∈ Submodule.span R (t : Set N),
      e.symm n ∈ Submodule.span S ((t.image e.symm : Finset M) : Set M) by
    simpa using H _ hm
  intro n hn
  refine Submodule.span_induction (fun x hx => Submodule.subset_span ?_) ?_
    (fun x y _ _ hx hy => ?_) (fun r x _ hx => ?_) hn
  · exact Finset.mem_image_of_mem _ hx
  · simp
  · rw [map_add]
    exact Submodule.add_mem _ hx hy
  · obtain ⟨s, hs⟩ := h r
    rw [show e.symm (r • x) = s • e.symm x from
      e.injective (by rw [hs, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply])]
    exact Submodule.smul_mem _ s hx

namespace Stacks

section Presheaf

variable {C : Type u} [Category.{v} C]

/-- **The objectwise tensor product commutes with multiplication by a section, in its second
factor**: `𝟙 F ⊗ (f · -)` is multiplication by `f` on `F ⊗ P`. -/
theorem tensorLeft_map_presheafSmul {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : PresheafOfModules.{w} (ringPresheaf O))
    (f : (ringPresheaf O ⋙ forget RingCat).sections)
    (P : PresheafOfModules.{w} (ringPresheaf O)) :
    PresheafOfModules.tensorHom (O := O) (𝟙 F)
        ((presheafSectionToEnd (ringPresheaf O) f).asHom.app P) =
      (presheafSectionToEnd (ringPresheaf O) f).asHom.app
        (PresheafOfModules.tensorObj (O := O) F P) := by
  refine PresheafOfModules.tensorObj_hom_ext fun U x y ↦ ?_
  let r : ((ringPresheaf O).obj U) := f.val U
  show x ⊗ₜ[(ringPresheaf O).obj U] (r • y) = r • (x ⊗ₜ[(ringPresheaf O).obj U] y)
  rw [TensorProduct.tmul_smul]

end Presheaf

section Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {O : Sheaf J CommRingCat.{w}}
  [∀ U, IsMulCommutative ((commRingSheafToRingSheaf O).obj.obj U)]
  (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O))

/-- **Tensoring on the left with `F` commutes with multiplication by a section**: the
endofunctor `G ↦ F ⊗_O G` carries multiplication by a compatible family `f` of local sections
of `O` on `G` to multiplication by `f` on `F ⊗_O G`. -/
theorem sheafTensorObj_map_globalSectionToEnd
    (f : ((commRingSheafToRingSheaf O).obj ⋙ forget RingCat).sections)
    (G : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    ((SheafOfModules.Tensor.sheafTensor O).obj F).map
        ((SheafOfModules.globalSectionToEnd (commRingSheafToRingSheaf O) f).asHom.app G) =
      (SheafOfModules.globalSectionToEnd (commRingSheafToRingSheaf O) f).asHom.app
        (((SheafOfModules.Tensor.sheafTensor O).obj F).obj G) := by
  have h1 : PresheafOfModules.tensorHom (O := O.obj) (𝟙 F.val)
        (((SheafOfModules.globalSectionToEnd (commRingSheafToRingSheaf O) f).asHom.app G).val) =
      (presheafSectionToEnd (commRingSheafToRingSheaf O).obj f).asHom.app
        (PresheafOfModules.tensorObj (O := O.obj) F.val G.val) :=
    tensorLeft_map_presheafSmul (O := O.obj) F.val f G.val
  exact (congrArg (PresheafOfModules.sheafification (𝟙 (commRingSheafToRingSheaf O).obj)).map
    h1).trans (sheafification_map_presheafSmul (commRingSheafToRingSheaf O) f _)

end Sheaf

end Stacks

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.SiteModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`𝒢 ⊗ f^*(-)` commutes with multiplication by pulled-back functions.** For `f : X ⟶ Y`,
`h : Y ⟶ T` with `T` an object of the site, an `𝒪_X`-module `𝒢`, an `𝒪_Y`-module `M` and a
function `x` on `T`, the map `𝒢 ⊗ f^*(h^♯ x)` is multiplication by `(f ≫ h)^♯ x` on
`𝒢 ⊗ f^*M`. -/
theorem tensorPullbackBifunctor_obj_map_globalSmul {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T : BigFppfOver B S hS} (h : Y ⟶ schemeSpace T)
    (G : Modules.{u, u} B S hS X.1 X.2) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    ((tensorPullbackBifunctor f).obj G).map
        (globalSmul
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
          (objectRingHom T h x) M) =
      globalSmul ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        (objectRingHom T (f ≫ h) x)
        (((tensorPullbackBifunctor f).obj G).obj M) := by
  have hP : (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules =
      modulePullback B S hS f :=
    RingedToposHom.pullbackModules_eq_pullbackModules_toRingedToposModulesHom
      (smallEtaleRingedToposHom B S hS f)
  show ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X).O).obj G).map
        ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.map
          (globalSmul _ (pullbackToGlobalFunctions B S hS Y T h x) M)) =
    globalSmul _ (pullbackToGlobalFunctions B S hS X T (f ≫ h) x)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS X).O).obj G).obj
          ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.obj M))
  rw [hP, modulePullback_map_globalSmul_pullbackToGlobalFunctions]
  have : ∀ U, IsMulCommutative ((Stacks.commRingSheafToRingSheaf
      (smallEtaleRingedTopos B S hS X).O).obj.obj U) := fun U =>
    ⟨⟨fun a b => mul_comm (G := ((smallEtaleRingedTopos B S hS X).O.obj.obj U : Type u)) a b⟩⟩
  exact Stacks.sheafTensorObj_map_globalSectionToEnd (O := (smallEtaleRingedTopos B S hS X).O) G _ _

/-- **On the free module of rank one, multiplication by a function of `U` is the associated map
of a scalar.** Let `U` be an object of the site whose scheme is affine, with `R = Γ(U, 𝒪_U)`.
For every `d ∈ R`, multiplication by the function `d` on `R^~` is `r^~` for some `r ∈ R`. -/
theorem exists_representedAffineAssociated_map_smul_eq_globalSmul (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (d : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ∃ r : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤),
      (representedAffineAssociated B S hS U).map
          (r • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) =
        globalSmul ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O))
          (objectRingHom U (𝟙 (schemeSpace U)) d)
          ((representedAffineAssociated B S hS U).obj
            (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
              Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) := by
  let hF := representedAffineAssociatedFullyFaithful B S hS U
  let e := hF.preimage (globalSmul ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O))
    (objectRingHom U (𝟙 (schemeSpace U)) d)
    ((representedAffineAssociated B S hS U).obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))))
  refine ⟨e.hom 1, ?_⟩
  have he : e.hom 1 • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) = e := by
    ext
    show e.hom 1 • (1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) = e.hom 1
    rw [smul_eq_mul, mul_one]
  rw [he]
  exact hF.map_preimage _

/-- **`𝒢 ⊗ f^*R^~ ≅ 𝒢`**: the associated module of the free module of rank one is the structure
sheaf, its inverse image is the structure sheaf, and tensoring with the structure sheaf is the
identity. -/
def tensorPullbackRepresentedAffineUnitIso (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace U) (G : Modules.{u, u} B S hS X.1 X.2) :
    ((tensorPullbackBifunctor f).obj G).obj ((representedAffineAssociated B S hS U).obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) ≅ G :=
  ((tensorPullbackBifunctor f).obj G).mapIso (representedAffineAssociatedObjUnitIso B S hS U) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X).O).obj G).mapIso
        (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
          (smallEtaleRingedToposHom B S hS f).toModulesHom).symm ≪≫
    Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoRight _ G

end AlgebraicGeometry.Space

