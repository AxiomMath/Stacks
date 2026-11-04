module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsComparisonNaturality
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseCotangentComplex

/-!
# The sectionwise cotangent complex as a presheaf of modules

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site.
`StacksFrontier/Cotangent/SheavesOfRings/SectionwiseCotangentComplex.lean` assembles the presheaf
`U ↦ L_{B(U)/A(U)}` at the level of complexes of *abelian groups*, which is the level at which
Tag 08SW takes the sheafification. This file refines that to a presheaf of modules over `B`: in
cohomological degree `i` the sections over `U` form a `B(U)`-module, and the comparison map of a
restriction square is semilinear over `B(U) → B(V)`, which is exactly the data of a
`PresheafOfModules` over the presheaf of rings underlying `B`.

It also assembles, as presheaves of commutative rings, the terms of the standard resolutions of
the section maps `A(U) → B(U)` together with their base maps, their augmentations and the
comparison with the sections of the standard resolution of `A ⟶ B`, and proves the universal
property of the degree-`-n` presheaf of modules: morphisms to a sheaf of `B`-modules are the
`A`-derivations of the presheaf of resolution terms.

## Main definitions

* `CategoryTheory.Sheaf.sectionwiseCotangentModules`: the presheaf of `B`-modules
  `U ↦ L_{B(U)/A(U)}^i`.
* `CategoryTheory.Sheaf.sectionsResolutionPresheaf`: the presheaf of commutative rings
  `U ↦ P'_i(U)`, the degree-`i` term of the standard resolution of `A(U) → B(U)`, with the
  canonical maps of the restriction squares as restriction maps.
* `CategoryTheory.Sheaf.sectionsResolutionBase` and
  `CategoryTheory.Sheaf.sectionsResolutionAugmentation`: its structure map from `A` and its
  augmentation to `B`.
* `CategoryTheory.Sheaf.sectionsResolutionComparison`: the comparison `P'_i ⟶ P_i` with the
  sections of the standard resolution of `A ⟶ B`, as a morphism of presheaves of rings.
* `CategoryTheory.Sheaf.sectionsResolutionDerivations`: the `A`-derivations of `P'_i` with
  values in a sheaf of `B`-modules.
* `CategoryTheory.Sheaf.sectionwiseDifferential`: the pure differential `1 ⊗ d p`, read in
  cohomological degree `-n`.
* `CategoryTheory.Sheaf.sectionwiseUniversalDerivation`: the tautological `A`-derivation of
  `P'_n` with values in the degree-`-n` presheaf of modules.

## Main results

* `CategoryTheory.Sheaf.sectionwiseCotangentModulesHomEquiv`: **the universal property.**
  Morphisms of presheaves of modules `L_{B(•)/A(•)}^{-n} ⟶ M` are exactly the `A`-derivations of
  `P'_n` with values in `M`. This is the objectwise universal property of the base-changed
  differentials, assembled over the site.
* `CategoryTheory.Sheaf.sectionwiseDifferential_map`: the restriction maps carry pure
  differentials to pure differentials.
* `CategoryTheory.Sheaf.sectionwiseCotangentModules_hom_ext`: two maps out of the degree-`-n`
  term agree as soon as they agree on pure differentials.

## Implementation notes

Nothing here is new mathematics: the functor laws of the presheaf of modules are the ones
already proved for the presheaf of complexes of abelian groups
(`CategoryTheory.Sheaf.cotangentComplexAbMap_sectionsRestrictionSquare_id` and `_comp`), read
elementwise, because the comparison map of a restriction square is the same underlying map at
both levels. The functor laws of `sectionsResolutionPresheaf` are
`CommAlgCat.squareFunctoriality_resolution_id` and `_comp` in the same way.

The universal property is the objectwise one, `CommAlgCat.cotangentTermDesc`, together with the
observation that a family of maps out of the degree-`-n` terms is natural as soon as it is
natural on pure differentials (`CategoryTheory.Sheaf.sectionwiseCotangentModules_hom_ext`), the
degreewise analogue of the argument used throughout the sectionwise development.

A `B(U)`-module appears here in two spellings: as an object of
`ModuleCat (sectionsAlgebra J f U)`, which is where the algebraic development of the cotangent
complex of a ring map leaves it, and as an object of
`ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj U)`, which is where a presheaf of
modules over `B` wants it. The two are the same up to unfolding instances, but not interchangeable
for `rw` and `simp`, so every statement below is phrased inside one spelling: the algebraic one for
the lemmas about pure differentials, and `CategoryTheory.Sheaf.moduleSections` — the evaluation of
a sheaf of `B`-modules, which already lands in the algebraic spelling — for the coefficients of a
derivation. Only the structure fields of the presheaf of modules and of its morphisms cross between
the two, where a definitional unfolding does the work.

## References

* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w t s

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-! ## The sectionwise cotangent complex as a presheaf of modules -/

/-- **The presheaf of `B`-modules `U ↦ L_{B(U)/A(U)}^i`.** In cohomological degree `i` the
sections over `U` of the sectionwise cotangent complex form a `B(U)`-module, and the comparison
map of the restriction square along `g : U ⟶ V` is semilinear over `B(U) → B(V)`. -/
noncomputable def sectionwiseCotangentModules (i : ℤ) :
    PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj where
  obj U := (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
    (sectionsAlgebra J f U)).X i
  map g := (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
    (sectionsRestrictionSquare J f g)).complexMap.f i
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{max u v w})
      (congrArg (fun k => k.f i)
        (cotangentComplexAbMap_sectionsRestrictionSquare_id J f U)) x
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{max u v w})
      (congrArg (fun k => k.f i)
        (cotangentComplexAbMap_sectionsRestrictionSquare_comp J f g h)) x

/-- The sections over `U` of `sectionwiseCotangentModules J f i` are the degree-`i` term of the
cotangent complex of `A(U) → B(U)`. -/
@[simp]
theorem sectionwiseCotangentModules_obj (i : ℤ) (U : Cᵒᵖ) :
    (sectionwiseCotangentModules J f i).obj U =
      (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).X i :=
  rfl

/-! ## Pure differentials -/

/-- The pure differential `1 ⊗ d p` of the cotangent complex of `A(U) → B(U)`, read in
cohomological degree `-n`. -/
noncomputable def sectionwiseDifferential (n : ℕ) (U : Cᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).X (-(n : ℤ)) :=
  (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) n).inv
    (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) (op ⦋n⦌) p)

/-- `1 ⊗ d -` is additive. -/
theorem sectionwiseDifferential_add (n : ℕ) (U : Cᵒᵖ)
    (p q : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    sectionwiseDifferential J f n U (p + q) =
      sectionwiseDifferential J f n U p + sectionwiseDifferential J f n U q := by
  dsimp only [sectionwiseDifferential]
  rw [CommAlgCat.cotangentTermDifferential_add.{max u v w, max u v w}, map_add]

/-- The Leibniz rule for `1 ⊗ d -`: the coefficients are the values of the augmentation. -/
theorem sectionwiseDifferential_mul (n : ℕ) (U : Cᵒᵖ)
    (p q : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    sectionwiseDifferential J f n U (p * q) =
      CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) (op ⦋n⦌) p • sectionwiseDifferential J f n U q +
        CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) (op ⦋n⦌) q • sectionwiseDifferential J f n U p := by
  dsimp only [sectionwiseDifferential]
  rw [CommAlgCat.cotangentTermDifferential_mul.{max u v w, max u v w}, map_add, map_smul,
    map_smul]

/-- `1 ⊗ d -` kills the image of the base ring. -/
theorem sectionwiseDifferential_algebraMap (n : ℕ) (U : Cᵒᵖ) (a : A.obj.obj U) :
    sectionwiseDifferential J f n U
      (algebraMap (A.obj.obj U)
        ((CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) a) = 0 := by
  dsimp only [sectionwiseDifferential]
  rw [CommAlgCat.cotangentTermDifferential_algebraMap.{max u v w, max u v w}, map_zero]

/-- `1 ⊗ d -`, as an additive map. -/
noncomputable def sectionwiseDifferentialAddHom (n : ℕ) (U : Cᵒᵖ) :
    (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).left.obj (op ⦋n⦌) →+
      (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).X (-(n : ℤ)) :=
  AddMonoidHom.mk' (sectionwiseDifferential J f n U) (sectionwiseDifferential_add J f n U)

/-- `sectionwiseDifferentialAddHom` evaluates to the pure differential `1 ⊗ d p`. -/
@[simp]
theorem sectionwiseDifferentialAddHom_apply (n : ℕ) (U : Cᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    sectionwiseDifferentialAddHom J f n U p = sectionwiseDifferential J f n U p :=
  rfl

/-- **The restriction maps carry pure differentials to pure differentials**, along the map of
standard resolutions of the restriction square. -/
theorem sectionwiseDifferential_map (n : ℕ) {U V : Cᵒᵖ} (g : U ⟶ V)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g)).complexMap.f (-(n : ℤ))
        (sectionwiseDifferential J f n U p) =
      sectionwiseDifferential J f n V
        ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g)).resolution (op ⦋n⦌) p) :=
  eq_inv_apply_of_hom_apply_eq'
    (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj V)
      (sectionsAlgebra J f V) n)
    ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f g)).complexMap_differential n p)

/-- **Two maps out of the degree-`-n` term agree as soon as they agree on pure
differentials.** -/
theorem sectionwiseCotangentModules_hom_ext (n : ℕ) (U : Cᵒᵖ)
    {N : ModuleCat.{max u v w} (sectionsAlgebra J f U)}
    (α β : (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).X (-(n : ℤ)) ⟶ N)
    (h : ∀ p, α (sectionwiseDifferential J f n U p) =
      β (sectionwiseDifferential J f n U p)) : α = β := by
  refine (cancel_epi (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
    (A.obj.obj U) (sectionsAlgebra J f U) n).inv).mp ?_
  exact CommAlgCat.cotangentTerm_hom_ext.{max u v w, max u v w} _ _ _ _ _ h

/-! ## The presheaf of terms of the sectionwise standard resolutions -/

/-- **The presheaf of commutative rings `U ↦ P'_i(U)`**, the degree-`i` term of the standard
resolution of the section map `A(U) → B(U)`, whose restriction maps are the canonical maps of
the restriction squares. -/
noncomputable def sectionsResolutionPresheaf (i : SimplexCategoryᵒᵖ) :
    Cᵒᵖ ⥤ CommRingCat.{max u v w} where
  obj U := CommRingCat.of ((CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
    (sectionsAlgebra J f U)).left.obj i)
  map g := CommRingCat.ofHom
    ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f g)).resolution i)
  map_id U := by
    apply CommRingCat.hom_ext
    rw [sectionsRestrictionSquare_id,
      CommAlgCat.squareFunctoriality_resolution_id.{max u v w, max u v w}]
    rfl
  map_comp g h := by
    apply CommRingCat.hom_ext
    rw [sectionsRestrictionSquare_comp,
      CommAlgCat.squareFunctoriality_resolution_comp.{max u v w, max u v w}]
    rfl

/-- The restriction map of `sectionsResolutionPresheaf J f i` along `g` is the map of standard
resolutions of the restriction square of `g`. -/
@[simp]
theorem sectionsResolutionPresheaf_map {U V : Cᵒᵖ} (g : U ⟶ V) (i : SimplexCategoryᵒᵖ) :
    ((sectionsResolutionPresheaf J f i).map g).hom =
      (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare J f g)).resolution i :=
  rfl

/-- The structure map `A ⟶ P'_i` from the base sheaf of rings. -/
noncomputable def sectionsResolutionBase (i : SimplexCategoryᵒᵖ) :
    A.obj ⟶ sectionsResolutionPresheaf J f i where
  app U := CommRingCat.ofHom
    (algebraMap (A.obj.obj U)
      ((CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).left.obj i))
  naturality U V g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun a => ?_
    exact ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f g)).resolution_algebraMap i a).symm

/-- Over `U`, the structure map `A ⟶ P'_i` is the algebra map `A(U) → P'_i(U)`. -/
@[simp]
theorem sectionsResolutionBase_app (i : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) (a : A.obj.obj U) :
    ((sectionsResolutionBase J f i).app U).hom a =
      algebraMap (A.obj.obj U)
        ((CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U)).left.obj i) a :=
  rfl

/-- The augmentation `P'_i ⟶ B`. -/
noncomputable def sectionsResolutionAugmentation (i : SimplexCategoryᵒᵖ) :
    sectionsResolutionPresheaf J f i ⟶ B.obj where
  app U := CommRingCat.ofHom
    (CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) i)
  naturality U V g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun p => ?_
    exact (CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f g)).resolution_augmentation i p

/-- Over `U`, the augmentation `P'_i ⟶ B` is the augmentation of the standard resolution of
`A(U) → B(U)`. -/
@[simp]
theorem sectionsResolutionAugmentation_app (i : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    ((sectionsResolutionAugmentation J f i).app U).hom p =
      CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) i p :=
  rfl

/-- **The comparison `P'_i ⟶ P_i` of Tag 08SX as a morphism of presheaves of commutative
rings.** Over every object of the site it is the comparison of standard resolutions; naturality
in the object is the naturality square of
`CategoryTheory.Sheaf.resolutionSectionsComparison_restriction`. -/
noncomputable def sectionsResolutionComparison (i : SimplexCategoryᵒᵖ) :
    sectionsResolutionPresheaf J f i ⟶ (resolutionTerm J f i).obj where
  app U := CommRingCat.ofHom ((resolutionSectionsComparison J f U).app i).hom.toRingHom
  naturality U V g := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun p => ?_
    exact (resolutionTerm_map_resolutionSectionsComparison J f g i p).symm

/-- Over `U`, the comparison `P'_i ⟶ P_i` is `CategoryTheory.Sheaf.resolutionSectionsComparison`
in degree `i`. -/
@[simp]
theorem sectionsResolutionComparison_app (i : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    ((sectionsResolutionComparison J f i).app U).hom p =
      ((resolutionSectionsComparison J f U).app i).hom p :=
  rfl

/-- The comparison of standard resolutions is compatible with the two structure maps from the
base sheaf of rings. -/
theorem sectionsResolutionBase_comp_comparison (i : SimplexCategoryᵒᵖ) :
    sectionsResolutionBase J f i ≫ sectionsResolutionComparison J f i =
      (resolutionBase J f i).hom := by
  exact NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun a =>
    ((resolutionSectionsComparison J f U).app i).hom.commutes a))

/-- The comparison of standard resolutions is compatible with the two augmentations. -/
theorem comparison_comp_resolutionAugmentation (i : SimplexCategoryᵒᵖ) :
    sectionsResolutionComparison J f i ≫ (resolutionAugmentation J f i).hom =
      sectionsResolutionAugmentation J f i := by
  exact NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext fun p =>
    resolutionAugmentation_resolutionSectionsComparison J f U i p))

/-! ## Derivations of the presheaf of resolution terms -/

/-- Restriction of scalars of a presheaf of `B`-modules along the augmentation `P'_i ⟶ B`. -/
noncomputable abbrev sectionsResolutionRestrict (i : SimplexCategoryᵒᵖ) :
    PresheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj ⥤
      PresheafOfModules.{max u v w} (sectionsResolutionPresheaf J f i ⋙
        forget₂ CommRingCat.{max u v w} RingCat.{max u v w}) :=
  PresheafOfModules.restrictScalars (Functor.whiskerRight
    (sectionsResolutionAugmentation J f i)
      (forget₂ CommRingCat.{max u v w} RingCat.{max u v w}))

/-- The `A`-derivations of the presheaf of rings `P'_i` with values in a sheaf of `B`-modules,
its `P'_i`-module structure coming from the augmentation `P'_i ⟶ B`. -/
noncomputable abbrev sectionsResolutionDerivations (i : SimplexCategoryᵒᵖ)
    (M : targetModules J B) :=
  ((sectionsResolutionRestrict J f i).obj M.val).Derivation' (sectionsResolutionBase J f i)

/-- **The tautological `A`-derivation of `P'_n`** with values in the degree-`-n` term of the
sectionwise cotangent complex: it sends `p` to the pure differential `1 ⊗ d p`. -/
noncomputable def sectionwiseUniversalDerivation (n : ℕ) :
    ((sectionsResolutionRestrict J f (op ⦋n⦌)).obj
        (sectionwiseCotangentModules J f (-(n : ℤ)))).Derivation'
      (sectionsResolutionBase J f (op ⦋n⦌)) where
  d {U} := sectionwiseDifferentialAddHom J f n U
  d_mul {U} x y := sectionwiseDifferential_mul J f n U x y
  d_map {_U _V} g x := (sectionwiseDifferential_map J f n g x).symm
  d_app {U} a := sectionwiseDifferential_algebraMap J f n U a

/-- The tautological derivation sends `p` to the pure differential `1 ⊗ d p`. -/
@[simp]
theorem sectionwiseUniversalDerivation_d (n : ℕ) (U : Cᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    (sectionwiseUniversalDerivation J f n).d p = sectionwiseDifferential J f n U p :=
  rfl

/-! ## The universal property -/

/-- The `A`-derivation of `P'_n` attached to a morphism of presheaves of modules out of the
degree-`-n` term: differentiate, then apply the morphism. -/
noncomputable def sectionwiseCotangentModulesDerivation (n : ℕ) (M : targetModules J B)
    (h : sectionwiseCotangentModules J f (-(n : ℤ)) ⟶ M.val) :
    sectionsResolutionDerivations J f (op ⦋n⦌) M :=
  (sectionwiseUniversalDerivation J f n).postcomp
    ((sectionsResolutionRestrict J f (op ⦋n⦌)).map h)

/-- The derivation attached to `h` sends `p` to the image under `h` of the pure differential
`1 ⊗ d p`. -/
theorem sectionwiseCotangentModulesDerivation_d (n : ℕ) (M : targetModules J B)
    (h : sectionwiseCotangentModules J f (-(n : ℤ)) ⟶ M.val) (U : Cᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    (sectionwiseCotangentModulesDerivation J f n M h).d p =
      (h.app U).hom (sectionwiseDifferential J f n U p) :=
  rfl

/-- The map out of the degree-`-n` term over a single object of the site, determined by an
`A`-derivation of `P'_n`. -/
noncomputable def sectionwiseCotangentModulesDescApp (n : ℕ) (M : targetModules J B)
    (d : sectionsResolutionDerivations J f (op ⦋n⦌) M) (U : Cᵒᵖ) :
    (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).X (-(n : ℤ)) ⟶ (moduleSections J f U).obj M :=
  (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) n).hom ≫
    CommAlgCat.cotangentTermDesc.{max u v w, max u v w} (A.obj.obj U) (sectionsAlgebra J f U)
      (op ⦋n⦌) ((moduleSections J f U).obj M) d.d (fun x y => d.d_mul x y)
      (fun a => d.d_app a)

/-- The map determined by an `A`-derivation `d` sends the pure differential `1 ⊗ d p` to
`d.d p`. -/
theorem sectionwiseCotangentModulesDescApp_differential (n : ℕ) (M : targetModules J B)
    (d : sectionsResolutionDerivations J f (op ⦋n⦌) M) (U : Cᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    sectionwiseCotangentModulesDescApp J f n M d U (sectionwiseDifferential J f n U p) =
      d.d p := by
  dsimp only [sectionwiseCotangentModulesDescApp, sectionwiseDifferential]
  rw [ModuleCat.comp_apply, ModuleCat.hom_inv_apply]
  exact CommAlgCat.cotangentTermDesc_differential.{max u v w, max u v w} _ _ _ _ _ _ _ p

/-- **The morphism of presheaves of modules determined by an `A`-derivation of `P'_n`.** -/
noncomputable def sectionwiseCotangentModulesDesc (n : ℕ) (M : targetModules J B)
    (d : sectionsResolutionDerivations J f (op ⦋n⦌) M) :
    sectionwiseCotangentModules J f (-(n : ℤ)) ⟶ M.val where
  app U := sectionwiseCotangentModulesDescApp J f n M d U
  naturality {U V} g :=
    sectionwiseCotangentModules_hom_ext J f n U _ _ fun p =>
      (congrArg (fun z => sectionwiseCotangentModulesDescApp J f n M d V z)
            (sectionwiseDifferential_map J f n g p)).trans
        ((sectionwiseCotangentModulesDescApp_differential J f n M d V _).trans
          ((d.d_map g p).trans
            (congrArg (fun z => M.val.map g z)
              (sectionwiseCotangentModulesDescApp_differential J f n M d U p).symm)))

/-- **The universal property of the sectionwise base-changed differentials.** Morphisms of
presheaves of modules from the degree-`-n` term of the sectionwise cotangent complex to a sheaf
of `B`-modules `M` are exactly the `A`-derivations of the presheaf `P'_n` of resolution terms
with values in `M`. -/
noncomputable def sectionwiseCotangentModulesHomEquiv (n : ℕ) (M : targetModules J B) :
    (sectionwiseCotangentModules J f (-(n : ℤ)) ⟶ M.val) ≃
      sectionsResolutionDerivations J f (op ⦋n⦌) M where
  toFun := sectionwiseCotangentModulesDerivation J f n M
  invFun := sectionwiseCotangentModulesDesc J f n M
  left_inv h := by
    refine PresheafOfModules.hom_ext fun U => ?_
    refine sectionwiseCotangentModules_hom_ext J f n U _ _ fun p => ?_
    exact sectionwiseCotangentModulesDescApp_differential J f n M
      (sectionwiseCotangentModulesDerivation J f n M h) U p
  right_inv d := by
    refine PresheafOfModules.Derivation.ext ?_
    funext U
    refine AddMonoidHom.ext fun p => ?_
    exact sectionwiseCotangentModulesDescApp_differential J f n M d U p

end CategoryTheory.Sheaf

end
