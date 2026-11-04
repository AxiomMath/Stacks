module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.CategoryTheory.Limits.KernelBiproduct

/-!
# Finite products of adequate functors on a restricted domain of algebras

A module-valued functor on commutative `A`-algebras may be defined only on a chosen domain
`ι : C ⥤ CommAlgCat A`, and `AdequateFunctor.IsAdequate ι F` is adequacy computed on that
domain. The closure of adequacy under finite products is proved here *for every* such domain,
and in particular for `AdequateFunctor.siteAlgebraInclusion A P`, the algebras whose spectra
belong to a chosen big site, which is the domain on which the sections of a sheaf of modules on
a big site are defined.

The argument needs nothing beyond the definition of adequacy. A kernel presentation of `F` and
one of `G` are maps of `A`-modules `a : M₁ ⟶ N₁` and `b : M₂ ⟶ N₂`; their biproduct
`biprod.map a b` presents `F ⊞ G`, because extension of scalars is additive and so carries
`biprod.map a b` to the biproduct of the two base-changed maps, whose kernel is the biproduct of
their kernels.

## Main definitions

* `AdequateFunctor.adequateOn` — adequacy as a property of the module-valued functors on a
  chosen domain of algebras, the restricted-domain counterpart of `AdequateFunctor.adequate`.
* `AdequateFunctor.moduleExtensionOnBiprodIso` — the module extension of a direct sum of two
  modules, read on the chosen domain, is the biproduct of the two module extensions.

## Main results

* `AdequateFunctor.IsAdequate.biprod` — the biproduct of two adequate module-valued functors on
  a chosen domain of algebras is adequate.
* `AdequateFunctor.isAdequate_of_isLimit_discrete` — a finite product of adequate module-valued
  functors on a chosen domain of algebras is adequate: [Stacks, Tag 06VB] on that domain.
* `AdequateFunctor.map_biprod_map_comp_mapBiprod` — an additive functor between preadditive
  categories with binary biproducts carries the biproduct of two morphisms to the biproduct of
  their images.

## Implementation notes

`AdequateFunctor.adequateOn` is a generalization, not a second copy, of
`Stacks.Adequate.adequateOn`: the latter is this one at `AdequateFunctor.siteAlgebraInclusion`,
reducibly so, since both are the property `fun F ↦ IsAdequate _ F`. The closure instances proved
here for `adequateOn` therefore apply to `Stacks.Adequate.adequateOn` with no transport.

The closure of adequacy under finite products, `adequate_isClosedUnderFiniteProducts`, fixes
the domain to be the identity of the commutative `A`-algebras, and its proof of the binary case
goes through [Stacks, Tag 06V3]; closure under kernels is not available on a restricted domain.
The proof here does not use it: the presenting map of the biproduct is written down from the
presenting maps of the two factors, so only additivity of extension of scalars is needed.

`map_biprod_map_comp_mapBiprod` restates, for the comparison isomorphism `Functor.mapBiprod`,
the naturality of `Functor.biprodComparison` recorded as
`biprodComparison_naturality` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfASquare`, where it is
module-private.

No `@[stacks]` attribute is placed here: `isAdequate_of_isLimit_discrete` is the closure property
of 06VB for module-valued functors transported to a restricted domain.

## References

* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
* [Stacks Project, Tag 06VB](https://stacks.math.columbia.edu/tag/06VB)
* [Stacks Project, Tag 06Z3](https://stacks.math.columbia.edu/tag/06Z3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe w' w v u u₁ v₁ u₂ v₂ u₃ v₃

namespace AdequateFunctor

/-! ### Biproducts of morphisms under an additive functor -/

section MapBiprodMap

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasBinaryBiproducts D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [HasBinaryBiproducts E]
  (F : D ⥤ E) [F.Additive]

variable [PreservesBinaryBiproducts F]

omit [HasBinaryBiproducts E] in
/-- An additive functor between preadditive categories with binary biproducts carries the
biproduct of two morphisms to the biproduct of their images, up to the comparison isomorphisms
identifying the image of a biproduct with the biproduct of the images. -/
public theorem map_biprod_map_comp_mapBiprod {X₁ X₂ Y₁ Y₂ : D} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) :
    F.map (Limits.biprod.map a b) ≫ (F.mapBiprod Y₁ Y₂).hom =
      (F.mapBiprod X₁ X₂).hom ≫ Limits.biprod.map (F.map a) (F.map b) := by
  apply Limits.biprod.hom_ext <;>
    simp only [Category.assoc, Functor.mapBiprod_hom, Limits.biprod.lift_fst,
      Limits.biprod.lift_snd, Limits.biprod.lift_fst_assoc, Limits.biprod.lift_snd_assoc,
      Limits.biprod.map_fst, Limits.biprod.map_snd, ← F.map_comp]

end MapBiprodMap

/-! ### Biproducts of module-valued functors on a domain of algebras -/

section Reindex

variable {E : Type u₂} [Category.{v₂} E] {E' : Type u₃} [Category.{v₃} E']

/-- Reindexing a presheaf of modules is additive: it leaves the sections unchanged, reindexing
them along `K.op`, and addition of morphisms is objectwise. -/
public instance pushforward₀_additive (K : E' ⥤ E) (R : Eᵒᵖ ⥤ RingCat.{w'}) :
    (PresheafOfModules.pushforward₀.{w} K R).Additive where
  map_add := by intros; rfl

end Reindex

section Adequate

variable {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]
  (ι : C ⥤ CommAlgCat.{max u v} A)

/-- Binary biproducts of module-valued functors on a chosen domain of algebras. -/
public instance hasBinaryBiproducts_moduleValuedFunctorOn :
    HasBinaryBiproducts (ModuleValuedFunctorOn.{w} ι) :=
  haveI : HasBinaryProducts (ModuleValuedFunctorOn.{w} ι) :=
    PresheafOfModules.hasLimitsOfShape _ _
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Finite products of module-valued functors on a chosen domain of algebras. -/
public instance hasFiniteProducts_moduleValuedFunctorOn :
    HasFiniteProducts (ModuleValuedFunctorOn.{w} ι) where
  out _ := PresheafOfModules.hasLimitsOfShape _ _

/-- Extension of scalars to the module-valued functors on a chosen domain of algebras is
additive: it is base change of the presenting module, computed objectwise. -/
public instance moduleExtensionFunctorOn_additive :
    (moduleExtensionFunctorOn.{w} ι).Additive :=
  inferInstance

/-- Extension of scalars to the module-valued functors on a chosen domain of algebras preserves
binary biproducts, being additive. -/
public instance moduleExtensionFunctorOn_preservesBinaryBiproducts :
    PreservesBinaryBiproducts (moduleExtensionFunctorOn.{w} ι) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- Raising the value universe of the module-valued functors on a chosen domain of algebras
preserves binary biproducts, being additive. -/
public instance presheafOfModulesUliftFunctor_preservesBinaryBiproducts :
    PreservesBinaryBiproducts
      (presheafOfModulesUliftFunctor.{w', w} (algebraRingDiagramOn ι)) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- The module extension of a direct sum of two `A`-modules, read on a chosen domain of
algebras, is the biproduct of their module extensions: extension of scalars is additive. -/
public noncomputable def moduleExtensionOnBiprodIso (M N : ModuleCat.{max u v w} A) :
    (moduleExtensionFunctorOn.{max u v w} ι).obj (M ⊞ N) ≅
      (moduleExtensionFunctorOn.{max u v w} ι).obj M ⊞
        (moduleExtensionFunctorOn.{max u v w} ι).obj N :=
  Functor.mapBiprod _ _ _

/-- The biproduct of two adequate module-valued functors on any domain of algebras is adequate.
Kernel presentations `a : M₁ ⟶ N₁` of the first and `b : M₂ ⟶ N₂` of the second present the
biproduct, because the kernel of the biproduct of two morphisms is the biproduct of their
kernels and extension of scalars carries `biprod.map a b` to the biproduct of the base changes
of `a` and of `b`. -/
public lemma IsAdequate.biprod {F G : ModuleValuedFunctorOn.{w} ι}
    (hF : IsAdequate.{w, v} ι F) (hG : IsAdequate.{w, v} ι G) :
    IsAdequate.{w, v} ι (F ⊞ G) := by
  obtain ⟨M₁, N₁, a, ⟨eF⟩⟩ := hF
  obtain ⟨M₂, N₂, b, ⟨eG⟩⟩ := hG
  refine ⟨M₁ ⊞ M₂, N₁ ⊞ N₂, Limits.biprod.map a b, ⟨?_⟩⟩
  let U := presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)
  let E := moduleExtensionFunctorOn.{max u v w} ι
  exact U.mapBiprod F G ≪≫ Limits.biprod.mapIso eF eG ≪≫
    kernelBiprodMapIso (E.map a) (E.map b) ≪≫
    (kernel.mapIso (E.map (Limits.biprod.map a b))
      (Limits.biprod.map (E.map a) (E.map b))
      (E.mapBiprod M₁ M₂) (E.mapBiprod N₁ N₂)
      (map_biprod_map_comp_mapBiprod E a b)).symm

/-! ### Adequacy as a property of the functors on a domain of algebras -/

/-- Adequacy, as a property of the module-valued functors on a chosen domain of algebras. -/
public abbrev adequateOn : ObjectProperty (ModuleValuedFunctorOn.{w} ι) :=
  fun F ↦ IsAdequate.{w, v} ι F

/-- Adequacy on a chosen domain of algebras is invariant under isomorphism. -/
public instance adequateOn_isClosedUnderIsomorphisms :
    (adequateOn.{w, v} ι).IsClosedUnderIsomorphisms where
  of_iso e hF := IsAdequate.of_iso hF e.symm

/-- The zero functor is adequate on any domain of algebras: it is the kernel of the identity of
the zero module. -/
public instance adequateOn_containsZero : (adequateOn.{w, v} ι).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    let M : ModuleCat.{max u v w} A := 0
    refine ⟨M, M, 𝟙 M, ⟨IsZero.iso (Functor.map_isZero _ (isZero_zero _)) ?_⟩⟩
    have : Mono ((moduleExtensionFunctorOn.{max u v w} ι).map (𝟙 M)) := by
      rw [CategoryTheory.Functor.map_id]; infer_instance
    exact isZero_kernel_of_mono _

/-- Adequacy on a chosen domain of algebras is stable under binary products, which in a
preadditive category are the binary biproducts. -/
public instance adequateOn_isClosedUnderBinaryProducts :
    (adequateOn.{w, v} ι).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine (adequateOn.{w, v} ι).prop_of_iso ?_
      (IsAdequate.of_iso (IsAdequate.biprod ι
        (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
        (Limits.biprod.isoProd _ _).symm)
    exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

/-- Adequacy on a chosen domain of algebras is stable under finite products: it is stable under
binary products and the zero functor is adequate. -/
public instance adequateOn_isClosedUnderFiniteProducts :
    (adequateOn.{w, v} ι).IsClosedUnderFiniteProducts :=
  .mk'

/-- A finite product of adequate module-valued functors on any domain of algebras is adequate:
[Stacks, Tag 06VB] on that domain of algebras. -/
public lemma isAdequate_of_isLimit_discrete (J : Type) [Finite J]
    (K : Discrete J ⥤ ModuleValuedFunctorOn.{w} ι) {c : Cone K} (hc : IsLimit c)
    (hK : ∀ j, IsAdequate.{w, v} ι (K.obj j)) :
    IsAdequate.{w, v} ι c.pt :=
  (adequateOn.{w, v} ι).prop_of_isLimit hc hK

end Adequate

end AdequateFunctor

end
