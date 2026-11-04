module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackProperties
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse image of a finite free sheaf of modules is finite free

Let `Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)` be a finite-product-preserving functor between
categories of sheaves of sets on two sites, let `O` be a sheaf of rings on `(D, K)`, and let
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor J Φ O` be the inverse-image functor on sheaves
of modules. The inverse image of a coproduct of finitely many copies of the structure sheaf is a
coproduct of the same number of copies of the inverse-image structure sheaf, and a finite family
of generating sections of a sheaf of modules transports to a family of generating sections of its
inverse image indexed by the same type.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso`: the inverse image of the structure sheaf,
  viewed as a module over itself, is the structure sheaf of the inverse-image ring.
* `Stacks.Sheaves.ToposPullback.pullbackModuleFreeIso`: the finite-free comparison, an isomorphism
  from `free I` over the inverse-image ring to the inverse image of `free I`, for a finite `I`.
* `Stacks.Sheaves.ToposPullback.generatingSectionsPullback`: a family of finitely many generating
  sections of `F`, transported to a family of generating sections of the inverse image of `F`
  indexed by the *same* type.

## Main results

* `Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_add'`: the underlying morphism of sheaves
  of sets of a sum of two morphisms of sheaves of modules is the lift of the two underlying
  morphisms followed by the addition map.
* `Stacks.Sheaves.ToposPullback.map_moduleSheafFunctor_map_add`: the same statement after applying
  a finite-product-preserving functor to types, read on elements.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

/-! ## Additivity of the inverse image -/

section Additive

universe t ww'' vv'' uu''

variable {D : Type uu''} [Category.{vv''} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget AddCommGrpCat.{ww''})]
  (O : Sheaf K RingCat.{ww''}) {G G' : SheafOfModules.{ww''} O}

/-- The underlying morphism of sheaves of sets of a sum of two morphisms of sheaves of modules is
the lift of the two underlying morphisms followed by the addition map of the target. -/
lemma moduleSheafFunctor_map_add' (φ ψ : G ⟶ G') :
    (moduleSheafFunctor O).map (φ + ψ) =
      Limits.prod.lift ((moduleSheafFunctor O).map φ) ((moduleSheafFunctor O).map ψ) ≫
        moduleAddHom O G' := by
  refine hom_ext_sections (fun X s ↦ ?_)
  rw [Functor.map_comp_apply, CategoryTheory.Functor.map_lift_apply,
    sectionsFunctor_map_moduleAddHom]
  rfl

/-- The image under a finite-product-preserving functor to types of the underlying morphism of
sheaves of sets of a sum, read on elements: it is the transported addition of the two images. -/
lemma map_moduleSheafFunctor_map_add (P : Sheaf K (Type ww'') ⥤ Type t)
    [PreservesFiniteProducts P] (φ ψ : G ⟶ G') (x : P.obj (moduleSheaf O G)) :
    P.map ((moduleSheafFunctor O).map (φ + ψ)) x =
      moduleAddObj O G' P (P.map ((moduleSheafFunctor O).map φ) x)
        (P.map ((moduleSheafFunctor O).map ψ) x) := by
  simpa [moduleAddObj] using
    congrArg (fun m ↦ P.map m x) (moduleSheafFunctor_map_add' O φ ψ)

end Additive

/-! ## The unit comparison, at independent coefficient universes -/

section Unit

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'})

/-- The inverse image of the structure sheaf, viewed as a module over itself, is the structure
sheaf of the inverse-image ring, with its module structure, at independent coefficient
universes. -/
noncomputable def pullbackModuleUnitIso :
    SheafOfModules.unit (pullbackRingSheaf J Φ O) ≅
      (pullbackModuleFunctor J Φ O).obj (SheafOfModules.unit O) :=
  Iso.refl _

end Unit

/-! ## The finite-free comparison -/

section Free

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww})
  [HasWeakSheafify J AddCommGrpCat.{ww}] [J.WEqualsLocallyBijective AddCommGrpCat.{ww}]
  [HasWeakSheafify K AddCommGrpCat.{ww}] [K.WEqualsLocallyBijective AddCommGrpCat.{ww}]

/-- For a finite index type `I`, the free sheaf of modules on `I` over the inverse-image sheaf of
rings is the inverse image of the free sheaf of `O`-modules on `I`. -/
@[sga "4 IV 13.4" "special case"]
noncomputable def pullbackModuleFreeIso (I : Type ww) [Finite I] :
    SheafOfModules.free (R := pullbackRingSheaf J Φ O) I ≅
      (pullbackModuleFunctor J Φ O).obj (SheafOfModules.free (R := O) I) :=
  haveI : PreservesColimitsOfShape (Discrete I) (pullbackModuleFunctor J Φ O) := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
    exact preservesColimitsOfShape_of_equiv (Discrete.equivalence e).symm _
  (SheafOfModules.isColimitFreeCofan I).coconePointsIsoOfNatIso
    (isColimitOfPreserves (pullbackModuleFunctor J Φ O) (SheafOfModules.isColimitFreeCofan I))
    (Discrete.natIso fun _ ↦ pullbackModuleUnitIso J Φ O)

variable [HasSheafify K AddCommGrpCat.{ww}]

/-- A family of finitely many sections generating a sheaf of `O`-modules `F`, transported to a
family of generating sections of the inverse image of `F` indexed by the *same* type: the image of
`σ.π : free σ.I ⟶ F` under the inverse image, read through the finite-free comparison. -/
noncomputable def generatingSectionsPullback
    (hΦ : ∀ {A B : Sheaf K (Type ww)} (ψ : A ⟶ B), Sheaf.IsLocallySurjective ψ →
      Sheaf.IsLocallySurjective (Φ.map ψ))
    (F : SheafOfModules.{ww} O) (σ : F.GeneratingSections) [Finite σ.I] :
    ((pullbackModuleFunctor J Φ O).obj F).GeneratingSections where
  I := σ.I
  s := ((pullbackModuleFunctor J Φ O).obj F).freeHomEquiv
    ((pullbackModuleFreeIso J Φ O σ.I).hom ≫ (pullbackModuleFunctor J Φ O).map σ.π)
  epi := by
    rw [Equiv.symm_apply_apply]
    have : Epi ((pullbackModuleFunctor J Φ O).map σ.π) :=
      epi_pullbackModuleMap J Φ O hΦ σ.π
    infer_instance

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The transported generating sections are indexed by the index type of `σ`. -/
@[simp]
lemma generatingSectionsPullback_I
    (hΦ : ∀ {A B : Sheaf K (Type ww)} (ψ : A ⟶ B), Sheaf.IsLocallySurjective ψ →
      Sheaf.IsLocallySurjective (Φ.map ψ))
    (F : SheafOfModules.{ww} O) (σ : F.GeneratingSections) [Finite σ.I] :
    (generatingSectionsPullback J Φ O hΦ F σ).I = σ.I := rfl

/-- The transported generating sections form a finite family. -/
instance generatingSectionsPullback_isFiniteType
    (hΦ : ∀ {A B : Sheaf K (Type ww)} (ψ : A ⟶ B), Sheaf.IsLocallySurjective ψ →
      Sheaf.IsLocallySurjective (Φ.map ψ))
    (F : SheafOfModules.{ww} O) (σ : F.GeneratingSections) [Finite σ.I] :
    (generatingSectionsPullback J Φ O hΦ F σ).IsFiniteType where
  finite := inferInstanceAs (Finite σ.I)

end Free

end Stacks.Sheaves.ToposPullback

end
