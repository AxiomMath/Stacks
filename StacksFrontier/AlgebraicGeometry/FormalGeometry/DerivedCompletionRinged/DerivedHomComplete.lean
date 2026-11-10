module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Products
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom into a derived-complete complex

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊂ 𝒪` a sheaf of ideals. [Stacks, Tag 099A] asserts that for
every `K ∈ D(𝒪)` and every derived-complete `L ∈ D_{comp}(𝒪)` the object
`R𝑆heafHom_𝒪(K, L)` is again derived complete. The source `K` is arbitrary: no finiteness,
perfectness or boundedness is assumed, and none is assumed below either.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_derivedSheafHom` — Tag 099A.

## Implementation notes

Derived completeness is `AlgebraicGeometry.RingedSite.IsDerivedComplete` of
[Stacks, Tag 0999]: for every object `U` and every section `f ∈ ℐ(U)`, the restriction `K|_U` to
the slice site satisfies `T(K|_U, f) = 0`, which is encoded as the invertibility of the Milnor
difference map `1 - f·shift` on the countable product, that is as
`IsDerivedCompleteAt (K|_U) f`. The sheaf of ideals `ℐ` enters the statement only through this
predicate, and it is the same `ℐ` on both sides of the implication below.

The proof here is not the source's. The Stacks proof of Tag 099A runs through the
characterization of derived completeness by the vanishing of `R𝑆heafHom(𝒪_f, -)`
([Stacks, Tag 0997]) and derived currying ([Stacks, Tag 08J9], [Stacks, Tag 08JA]). Both are now
available: Tag 0997 is complete, its three implications registered in
`VanishingCriterion.lean`, `VanishingCriterionCoextension.lean` and
`VanishingCriterionTelescope.lean`, and derived currying is
`AlgebraicGeometry.RingedSite.derivedCurryIso` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedCurrying.lean`. The argument
below predates them and transports
`T(-, f) = 0` directly, which remains the shorter route: restriction to the slice site commutes
with derived internal Hom by
[Stacks, Tag 08JB], and the Milnor difference map is carried along by any functor that is
additive, preserves the countable product involved, and takes multiplication by `f` to
multiplication by `f`.

All three properties of `R𝑆heafHom_{𝒪_U}(K|_U, -)` are available. Additivity is
`AlgebraicGeometry.RingedSite.additive_derivedSheafHom_obj` and the compatibility with
multiplication by a local section of `𝒪` is
`AlgebraicGeometry.RingedSite.derivedSheafHom_map_globalSectionToEnd`, both in
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomAdditive.lean`; preservation
of the countable power of `L|_U` is
`AlgebraicGeometry.RingedSite.preservesLimit_derivedSheafHom` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomProducts.lean`. All three are
properties of the functor alone, not of derived completeness, and all three are proved by
reduction to K-injective (and, for the source of the product statement, K-flat)
representatives, the K-injective resolution being used only to produce objects and never as a
functor.

The universes are those at which the two halves of the statement meet. The derived internal Hom
bifunctor is constructed for a `RingedSite.{u, u, u}` with modules in `SheafOfModules.{u}`, and
`IsDerivedComplete.{u, u, u, u}` is that predicate at the same spelling.

## References

* [Stacks Project, Tag 099A](https://stacks.math.columbia.edu/tag/099A)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSite

/-- **Derived completeness at a scalar is carried along by a functor that is additive, preserves
the countable power of the object, and takes multiplication by the scalar to multiplication by
the scalar.** Such a functor intertwines the two Milnor difference maps through the product
comparison, which is an isomorphism by the product-preservation hypothesis. -/
theorem isDerivedCompleteAt_map_of_map_smul_id
    {R : Type*} [CommSemiring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    [HasProductsOfShape ℕ C] [HasProductsOfShape ℕ D]
    (F : C ⥤ D) [F.Additive] (M : C) (f : R)
    [PreservesLimit (Discrete.functor (fun _ : ℕ ↦ M)) F]
    (hF : F.map (f • 𝟙 M) = f • 𝟙 (F.obj M))
    (hM : IsDerivedCompleteAt M f) : IsDerivedCompleteAt (F.obj M) f := by
  rw [isDerivedCompleteAt_iff_isIso] at hM ⊢
  have he : piComparison F (fun _ : ℕ ↦ M) ≫ oneSubSmulShift (F.obj M) f =
      F.map (oneSubSmulShift M f) ≫ piComparison F (fun _ : ℕ ↦ M) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul,
      piComparison_comp_π, piComparison_comp_π, Category.assoc, piComparison_comp_π,
      ← F.map_comp, oneSubSmulShift_π, F.map_sub]
    congr 1
    rw [show f • Pi.π (fun _ : ℕ ↦ M) (n + 1) = Pi.π (fun _ : ℕ ↦ M) (n + 1) ≫ (f • 𝟙 M) by
      rw [Linear.comp_smul, Category.comp_id], F.map_comp, hF, Linear.comp_smul,
      Category.comp_id]
  have h : IsIso (F.map (oneSubSmulShift M f) ≫ piComparison F (fun _ : ℕ ↦ M)) := inferInstance
  rw [← he] at h
  exact IsIso.of_isIso_comp_left (piComparison F (fun _ : ℕ ↦ M)) _

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- The structure sheaf of the slice site over `U` is a sheaf of commutative rings. -/
theorem isMulCommutative_ringSheaf_over (V : (Over U)ᵒᵖ) :
    IsMulCommutative ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).obj.obj V) := by
  change IsMulCommutative (X.O.obj.obj (op V.unop.left))
  infer_instance

attribute [local instance] isMulCommutative_ringSheaf_over

/-- Sheaves of modules on the slice site over `U` are linear over the centre of their own
category, which is the linear structure the derived-completeness predicate of Tag 0999 uses. -/
abbrev linearCatCenterOver :
    Linear (CatCenter (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U)))
      (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U)) :=
  Linear.ofRingMorphism (RingHom.id _)

attribute [local instance] linearCatCenterOver

/-- Restriction to the slice site over `U`, on derived categories. -/
abbrev derivedSliceRestriction :=
  (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    U).mapDerivedCategory

/-- Derived internal Hom out of the restriction of `K` to the slice site over `U`. The type is
written at the spelling `((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U` of the structure
sheaf of the slice site, which is the one the derived-completeness predicate of Tag 0999 uses; the
derived internal Hom bifunctor is stated at the other spelling
`(Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)` of the same sheaf of rings. -/
abbrev derivedSliceSheafHom
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    DerivedCategory (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U)) ⥤
      DerivedCategory
        (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U)) :=
  (derivedSheafHomBifunctor (X.over U)).obj (op ((derivedSliceRestriction X U).obj K))

/-- **Stacks 099A.** Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊂ 𝒪` a sheaf of ideals. For every
`K ∈ D(𝒪)` — arbitrary, with no finiteness or boundedness assumed — and every derived-complete
`L ∈ D(𝒪)`, the object `R𝑆heafHom_𝒪(K, L)` is derived complete along the same `ℐ`.

Derived completeness is tested slice by slice. On the slice site over `U`, restriction commutes
with derived internal Hom by [Stacks, Tag 08JB], so the object to be tested is
`R𝑆heafHom_{𝒪_U}(K|_U, L|_U)`; and `L|_U` passes the test by hypothesis. That functor is
additive and takes multiplication by `f` to multiplication by `f`, both proved in
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomAdditive.lean`, and it
preserves the countable power of `L|_U` by
`AlgebraicGeometry.RingedSite.preservesLimit_derivedSheafHom`. Together these let it carry the
Milnor difference map, hence the test, from `L|_U` to its value. -/
@[stacks 099A]
theorem isDerivedComplete_derivedSheafHom
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (K L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hL : IsDerivedComplete.{u, u, u, u} X I L) :
    IsDerivedComplete.{u, u, u, u} X I
      (((derivedSheafHomBifunctor X).obj (op K)).obj L) := by
  intro V f hf
  obtain ⟨hAdd, hLim, hColim, hProd, hComplete⟩ := hL V f hf
  refine ⟨hAdd, hLim, hColim, hProd, ?_⟩
  have := hProd
  have : PreservesLimit (Discrete.functor fun _ : ℕ ↦ (derivedSliceRestriction X V).obj L)
      (derivedSliceSheafHom X V K) :=
    preservesLimit_derivedSheafHom (X.over V) _ _
  have : (derivedSliceSheafHom X V K).Additive :=
    additive_derivedSheafHom_obj (X.over V) ((derivedSliceRestriction X V).obj K)
  exact (isDerivedCompleteAt_iff_of_iso ((derivedHomRestriction X V).iso K L) _).mpr
    (isDerivedCompleteAt_map_of_map_smul_id (derivedSliceSheafHom X V K)
      ((derivedSliceRestriction X V).obj L) _
      (derivedSheafHom_map_globalSectionToEnd (X.over V)
        (Stacks.SheafOfModules.terminalSection
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over V) (Over.mk (𝟙 V))
          Over.mkIdTerminal f) _ _)
      hComplete)

end AlgebraicGeometry.RingedSite

end
