module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Coproduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionInduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZero
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.FiniteEtaleSpec
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ScalarExtensionSplitting
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension of scalars along finite separable algebras

Let `(D0)`–`(D3)` be data satisfying `(A)`, `(B)` and `(C)` (`Stacks.WeilCohomology.WeilData`).
Let `k''/k'/k` be finite separable algebras and let `X` be a smooth projective scheme over `k'`.
Stacks 0FHX says that

`H^*(X) ⊗_{H^0(Spec k')} H^0(Spec k'') = H^*(X ×_{Spec k'} Spec k'')`.

This file sets up the objects and proves that statement from Künneth, the cohomology of a
zero-dimensional scheme (Stacks 0FHQ) and additivity on a disjoint union (Stacks 0FHJ).

## The objects

* `X` is a scheme with a smooth H-projective morphism `π : X ⟶ Spec k'`. It is a smooth projective
  scheme over `k` (`SmoothProjectiveScheme.ofOver`), and `π` is a morphism
  `SmoothProjectiveScheme.toSpec` to `Spec k'`, the smooth projective `k`-scheme
  `SmoothProjectiveScheme.spec k k'`.
* `X ×_{Spec k'} Spec k''` is the fibre product of schemes, a smooth projective scheme over `k`
  (`SmoothProjectiveScheme.baseChangeObj`) with its projections `baseChangeFst` and
  `baseChangeSnd`.
* The comparison `X ×_{Spec k'} Spec k'' ⟶ X ×_{Spec k} Spec k''` is an open and closed immersion
  (`Concrete/ScalarExtensionSplitting.lean`). With its complement `X ×_{Spec k'} Spec l`
  (`baseChangeComplement`), where `k' ⊗_k k'' = k'' × l`, it exhibits `X ×_{Spec k} Spec k''` as
  a coproduct (`isColimitBaseChange`). The same applies for `X = Spec k'`: the graph
  `Spec k'' ⟶ Spec k' ×_{Spec k} Spec k''` and its complement `Spec l` (`isColimitGraph`).
  Under `π × id` the second decomposition pulls back to the first (`comparison_productHom`,
  `complementHom_graphComplementι`).

## The cohomological argument

`H^*(X)` is an `H^0(Spec k')`-algebra by `π^*`, and `H^0(Spec k'')` is one by pullback along
`Spec k'' ⟶ Spec k'`. The comparison map `WeilData.scalarExtensionMap` sends `a ⊗ b` to
`pr₁^*a ∪ pr₂^*b`. By Künneth and 0FHQ(1), `H^*(X) ⊗_F H^0(Spec k'') = H^*(X ×_{Spec k} Spec k'')`.
By 0FHJ this is `H^*(X ×_{Spec k'} Spec k'') × H^*(X ×_{Spec k'} Spec l)`. In the same way,
`H^0(Spec k') ⊗_F H^0(Spec k'') = H^0(Spec k'') × H^0(Spec l)`, with first projection the
multiplication map. The element `e` of `H^0(Spec k') ⊗_F H^0(Spec k'')` corresponding to `(0, 1)`
dies under multiplication. It acts on `H^*(X) ⊗_F H^0(Spec k'')` as the idempotent cutting out
`H^*(X ×_{Spec k'} Spec l)`. The algebraic lemma
`Stacks.WeilCohomology.bijective_scalarExtensionHom_of_idempotent` then gives bijectivity.

## References

* [Stacks Project, Tag 0FHX](https://stacks.math.columbia.edu/tag/0FHX)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable (k : Type u) [Field k]

section Objects

variable {k' : Type u} [CommRing k'] [Algebra k k'] [Module.Finite k k'] [Algebra.Etale k k']
  {X : Scheme.{u}} (π : X ⟶ Spec (.of k'))

/-- A scheme smooth and projective over `Spec k'`, for `k'` finite étale over `k`, is smooth and
projective over `k`. -/
theorem isProjectiveMorphism_comp_specStructure (hπ : IsProjectiveMorphism π) :
    IsProjectiveMorphism (π ≫ specStructure k k') :=
  hπ.comp ((isProjective_iff_isProjectiveMorphism_of_isAffine _).1
      (SmoothProjectiveScheme.isProjective (spec k k')))

/-- A scheme `X` smooth and projective over `Spec k'`, for `k'` finite étale over `k`, as a
smooth projective scheme over `k`. -/
def ofOver [Smooth π] (hπ : IsProjectiveMorphism π) : (SmoothProjectiveScheme k).FullSubcategory :=
  haveI := etale_specStructure k k'
  ⟨Over.mk (π ≫ specStructure k k'), (inferInstance : Smooth (π ≫ specStructure k k')),
    (isProjectiveMorphism_comp_specStructure k π hπ).isProjective⟩

/-- The underlying scheme of `ofOver k π hπ` is `X`. -/
@[simp]
theorem ofOver_obj_left [Smooth π] (hπ : IsProjectiveMorphism π) : (ofOver k π hπ).obj.left = X :=
  rfl

/-- The structure morphism of `ofOver k π hπ` is `X ⟶ Spec k' ⟶ Spec k`. -/
@[simp]
theorem ofOver_obj_hom [Smooth π] (hπ : IsProjectiveMorphism π) :
    (ofOver k π hπ).obj.hom = π ≫ specStructure k k' :=
  rfl

/-- The structure morphism `X ⟶ Spec k'`, as a morphism of smooth projective schemes over `k`. -/
def toSpec [Smooth π] (hπ : IsProjectiveMorphism π) : ofOver k π hπ ⟶ spec k k' :=
  ObjectProperty.homMk (Over.homMk π rfl)

/-- The underlying morphism of schemes of `toSpec k π hπ` is `π`. -/
@[simp]
theorem toSpec_hom_left [Smooth π] (hπ : IsProjectiveMorphism π) : (toSpec k π hπ).hom.left = π :=
  rfl

end Objects

section Morphisms

variable {k' k'' : Type u} [CommRing k'] [CommRing k''] [Algebra k k'] [Algebra k k'']
  [Algebra k' k''] [IsScalarTower k k' k''] [Module.Finite k k'] [Algebra.Etale k k']
  [Module.Finite k k''] [Algebra.Etale k k'']
  {X : Scheme.{u}} (π : X ⟶ Spec (.of k')) [Smooth π] (hπ : IsProjectiveMorphism π)

/-- The structure morphism `X ×_{Spec k'} Spec k'' ⟶ Spec k''`. -/
abbrev baseChangeStructure : Limits.pullback π (Spec.map (CommRingCat.ofHom (algebraMap k' k''))) ⟶
    Spec (.of k'') :=
  pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k' k'')))

/-- **The base change `X ×_{Spec k'} Spec k''`**, as a smooth projective scheme over `k`. -/
def baseChangeObj : (SmoothProjectiveScheme k).FullSubcategory :=
  ofOver k (baseChangeStructure π (k'' := k'')) (hπ.baseChange _)

omit [Algebra k k'] [IsScalarTower k k' k''] [Module.Finite k k'] [Algebra.Etale k k'] in
/-- The underlying scheme of `baseChangeObj k π hπ` is the fibre product
`X ×_{Spec k'} Spec k''`. -/
@[simp]
theorem baseChangeObj_obj_left :
    (baseChangeObj k π hπ (k'' := k'')).obj.left =
      Limits.pullback π (Spec.map (CommRingCat.ofHom (algebraMap k' k''))) :=
  rfl

/-- The morphism `Spec k'' ⟶ Spec k'` of smooth projective schemes over `k`. -/
abbrev specTower : spec k k'' ⟶ spec k k' := specMap (IsScalarTower.toAlgHom k k' k'')

/-- The underlying morphism of `Spec k'' ⟶ Spec k'` is `Spec` of the structure map. -/
theorem specTower_hom_left :
    (specTower k (k' := k') (k'' := k'')).hom.left =
      Spec.map (CommRingCat.ofHom (algebraMap k' k'')) :=
  rfl

/-- The projection `X ×_{Spec k'} Spec k'' ⟶ X`. -/
def baseChangeFst : baseChangeObj k π hπ (k'' := k'') ⟶ ofOver k π hπ :=
  ObjectProperty.homMk (Over.homMk (pullback.fst _ _) (by
    change pullback.fst _ _ ≫ π ≫ specStructure k k' = pullback.snd _ _ ≫ specStructure k k''
    rw [pullback.condition_assoc, specMap_algebraMap_comp k k' k'']))

/-- The projection `X ×_{Spec k'} Spec k'' ⟶ Spec k''`. -/
def baseChangeSnd : baseChangeObj k π hπ (k'' := k'') ⟶ spec k k'' :=
  ObjectProperty.homMk (Over.homMk (pullback.snd _ _) rfl)

/-- The underlying morphism of `baseChangeFst k π hπ` is the first projection of the pullback. -/
@[simp]
theorem baseChangeFst_hom_left :
    (baseChangeFst k π hπ (k'' := k'')).hom.left = pullback.fst _ _ :=
  rfl

omit [Algebra k k'] [IsScalarTower k k' k''] [Module.Finite k k'] [Algebra.Etale k k'] in
/-- The underlying morphism of `baseChangeSnd k π hπ` is the second projection of the pullback. -/
@[simp]
theorem baseChangeSnd_hom_left :
    (baseChangeSnd k π hπ (k'' := k'')).hom.left = pullback.snd _ _ :=
  rfl

/-- The square `X ×_{Spec k'} Spec k'' ⟶ X ⟶ Spec k'` and `⟶ Spec k'' ⟶ Spec k'` commutes. -/
theorem baseChangeFst_toSpec :
    baseChangeFst k π hπ (k'' := k'') ≫ toSpec k π hπ = baseChangeSnd k π hπ ≫ specTower k :=
  hom_ext_left pullback.condition

/-- The comparison `X ×_{Spec k'} Spec k'' ⟶ X ×_{Spec k} Spec k''`. -/
def comparison : baseChangeObj k π hπ (k'' := k'') ⟶ prod (ofOver k π hπ) (spec k k'') :=
  ObjectProperty.homMk (Over.homMk (baseChangeComparison k k'' π) (by
    change baseChangeComparison k k'' π ≫ pullback.fst _ _ ≫ π ≫ specStructure k k' =
      pullback.snd _ _ ≫ specStructure k k''
    rw [baseChangeComparison_fst_assoc, pullback.condition_assoc,
      specMap_algebraMap_comp k k' k'']))

/-- The underlying morphism of `comparison k π hπ` is `baseChangeComparison k k'' π`. -/
@[simp]
theorem comparison_hom_left :
    (comparison k π hπ (k'' := k'')).hom.left = baseChangeComparison k k'' π :=
  rfl

/-- The comparison morphism followed by the first projection is the projection to `X`. -/
theorem comparison_fst :
    comparison k π hπ (k'' := k'') ≫ fst _ _ = baseChangeFst k π hπ :=
  hom_ext_left (baseChangeComparison_fst k k'' π)

/-- The comparison morphism followed by the second projection is the projection to `Spec k''`. -/
theorem comparison_snd :
    comparison k π hπ (k'' := k'') ≫ snd _ _ = baseChangeSnd k π hπ :=
  hom_ext_left (baseChangeComparison_snd k k'' π)

/-- The graph `Spec k'' ⟶ Spec k' ×_{Spec k} Spec k''` of `Spec k'' ⟶ Spec k'`. -/
def graphHom : spec k k'' ⟶ prod (spec k k') (spec k k'') :=
  ObjectProperty.homMk (Over.homMk (specGraph k k' k'') (by
    change specGraph k k' k'' ≫ pullback.fst _ _ ≫ specStructure k k' = specStructure k k''
    rw [specGraph_fst_assoc, specMap_algebraMap_comp k k' k'']))

/-- The underlying morphism of `graphHom k` is `specGraph k k' k''`. -/
@[simp]
theorem graphHom_hom_left : (graphHom k (k' := k') (k'' := k'')).hom.left = specGraph k k' k'' :=
  rfl

/-- The first component of the graph is `Spec k'' ⟶ Spec k'`. -/
theorem graphHom_fst : graphHom k (k' := k') (k'' := k'') ≫ fst _ _ = specTower k :=
  hom_ext_left (specGraph_fst k k' k'')

/-- The second component of the graph is the identity. -/
theorem graphHom_snd : graphHom k (k' := k') (k'' := k'') ≫ snd _ _ = 𝟙 _ :=
  hom_ext_left (specGraph_snd k k' k'')

/-- The morphism `π × id : X ×_{Spec k} Spec k'' ⟶ Spec k' ×_{Spec k} Spec k''`. -/
def productHom : prod (ofOver k π hπ) (spec k k'') ⟶ prod (spec k k') (spec k k'') :=
  ObjectProperty.homMk (Over.homMk (productMap k k'' π) (by
    change productMap k k'' π ≫ pullback.fst _ _ ≫ specStructure k k' =
      pullback.fst _ _ ≫ π ≫ specStructure k k'
    rw [productMap_fst_assoc]))

/-- The underlying morphism of `productHom k π hπ` is `productMap k k'' π`. -/
@[simp]
theorem productHom_hom_left :
    (productHom k π hπ (k'' := k'')).hom.left = productMap k k'' π :=
  rfl

/-- The first component of `π × id` is `π` on the first factor. -/
theorem productHom_fst :
    productHom k π hπ (k'' := k'') ≫ fst _ _ = fst _ _ ≫ toSpec k π hπ :=
  hom_ext_left (productMap_fst k k'' π)

/-- The second component of `π × id` is the second projection. -/
theorem productHom_snd :
    productHom k π hπ (k'' := k'') ≫ snd _ _ = snd _ _ :=
  hom_ext_left (productMap_snd k k'' π)

/-- `X ×_{Spec k'} Spec k'' ⟶ X ×_{Spec k} Spec k'' ⟶ Spec k' ×_{Spec k} Spec k''` factors
through the graph. -/
theorem comparison_productHom :
    comparison k π hπ (k'' := k'') ≫ productHom k π hπ = baseChangeSnd k π hπ ≫ graphHom k :=
  hom_ext_left (baseChangeComparison_productMap k k'' π)

end Morphisms

section Clopen

variable {k}

/-- The complement of the image of an open and closed immersion is open and closed. -/
theorem isClopen_rangeComplement {Z U : Scheme.{u}} (f : U ⟶ Z) [IsClosedImmersion f]
    [IsOpenImmersion f] : IsClopen (rangeComplement f : Set Z) := by
  rw [coe_rangeComplement]
  exact ⟨isClosed_compl_iff.mpr f.isOpenEmbedding.isOpen_range,
    f.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The complement of the image of an open and closed immersion into a smooth projective scheme,
as a smooth projective scheme over `k`. -/
def complementObj (Z : (SmoothProjectiveScheme k).FullSubcategory) {U : Scheme.{u}}
    (f : U ⟶ Z.obj.left)
    [IsClosedImmersion f] [IsOpenImmersion f] : (SmoothProjectiveScheme k).FullSubcategory :=
  clopenObj Z (rangeComplement f) (isClopen_rangeComplement f)

/-- The inclusion of the complement. -/
def complementι (Z : (SmoothProjectiveScheme k).FullSubcategory) {U : Scheme.{u}}
    (f : U ⟶ Z.obj.left)
    [IsClosedImmersion f] [IsOpenImmersion f] : complementObj Z f ⟶ Z :=
  ObjectProperty.homMk (Over.homMk (U := (complementObj Z f).obj) (rangeComplement f).ι rfl)

/-- The underlying scheme of `complementObj Z f` is the complement `rangeComplement f`. -/
@[simp]
theorem complementObj_obj_left (Z : (SmoothProjectiveScheme k).FullSubcategory) {U : Scheme.{u}}
    (f : U ⟶ Z.obj.left) [IsClosedImmersion f] [IsOpenImmersion f] :
    (complementObj Z f).obj.left = rangeComplement f :=
  rfl

/-- The underlying morphism of `complementι Z f` is the inclusion of `rangeComplement f`. -/
@[simp]
theorem complementι_hom_left (Z : (SmoothProjectiveScheme k).FullSubcategory) {U : Scheme.{u}}
    (f : U ⟶ Z.obj.left) [IsClosedImmersion f] [IsOpenImmersion f] :
    (complementι Z f).hom.left = (rangeComplement f).ι :=
  rfl

/-- The inclusion of the complement is an open immersion. -/
instance isOpenImmersion_complementι (Z : (SmoothProjectiveScheme k).FullSubcategory)
    {U : Scheme.{u}}
    (f : U ⟶ Z.obj.left) [IsClosedImmersion f] [IsOpenImmersion f] :
    IsOpenImmersion (complementι Z f).hom.left :=
  inferInstanceAs (IsOpenImmersion (rangeComplement f).ι)

/-- Under `g⁻¹(f'(U')) ⊆ f(U)`, `g` maps the complement of `f(U)` into that of `f'(U')`. -/
theorem range_complementMap_subset {Z Z' : (SmoothProjectiveScheme k).FullSubcategory}
    {U U' : Scheme.{u}}
    (f : U ⟶ Z.obj.left) (f' : U' ⟶ Z'.obj.left) [IsClosedImmersion f] [IsOpenImmersion f]
    [IsClosedImmersion f'] [IsOpenImmersion f'] (g : Z ⟶ Z')
    (h : g.hom.left ⁻¹' Set.range f' ⊆ Set.range f) :
    Set.range ((rangeComplement f).ι ≫ g.hom.left) ⊆ Set.range (rangeComplement f').ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι, coe_rangeComplement]
  intro hx
  have hx' : (rangeComplement f).ι x ∈ Set.range f := h hx
  have : (rangeComplement f).ι x ∈ (Set.range f)ᶜ := by
    rw [← coe_rangeComplement, ← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  exact this hx'

/-- The restriction of `g : Z ⟶ Z'` to the complements, as a morphism of schemes. -/
def complementLift {Z Z' : (SmoothProjectiveScheme k).FullSubcategory} {U U' : Scheme.{u}}
    (f : U ⟶ Z.obj.left)
    (f' : U' ⟶ Z'.obj.left) [IsClosedImmersion f] [IsOpenImmersion f] [IsClosedImmersion f']
    [IsOpenImmersion f'] (g : Z ⟶ Z') (h : g.hom.left ⁻¹' Set.range f' ⊆ Set.range f) :
    (rangeComplement f).toScheme ⟶ (rangeComplement f').toScheme :=
  IsOpenImmersion.lift (rangeComplement f').ι ((rangeComplement f).ι ≫ g.hom.left)
    (range_complementMap_subset f f' g h)

/-- The restriction of `g` to the complements commutes with the inclusions. -/
theorem complementLift_ι {Z Z' : (SmoothProjectiveScheme k).FullSubcategory} {U U' : Scheme.{u}}
    (f : U ⟶ Z.obj.left) (f' : U' ⟶ Z'.obj.left) [IsClosedImmersion f] [IsOpenImmersion f]
    [IsClosedImmersion f'] [IsOpenImmersion f'] (g : Z ⟶ Z')
    (h : g.hom.left ⁻¹' Set.range f' ⊆ Set.range f) :
    complementLift f f' g h ≫ (rangeComplement f').ι = (rangeComplement f).ι ≫ g.hom.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- A morphism `g : Z ⟶ Z'` with `g⁻¹(f'(U')) ⊆ f(U)` restricts to the complements. -/
def complementMap {Z Z' : (SmoothProjectiveScheme k).FullSubcategory} {U U' : Scheme.{u}}
    (f : U ⟶ Z.obj.left)
    (f' : U' ⟶ Z'.obj.left) [IsClosedImmersion f] [IsOpenImmersion f] [IsClosedImmersion f']
    [IsOpenImmersion f'] (g : Z ⟶ Z') (h : g.hom.left ⁻¹' Set.range f' ⊆ Set.range f) :
    complementObj Z f ⟶ complementObj Z' f' :=
  ObjectProperty.homMk (Over.homMk (U := (complementObj Z f).obj) (V := (complementObj Z' f').obj)
    (complementLift f f' g h) (by
      change _ ≫ ((rangeComplement f').ι ≫ Z'.obj.hom) = (rangeComplement f).ι ≫ Z.obj.hom
      rw [← Category.assoc, complementLift_ι, Category.assoc, Over.w g.hom]))

/-- The restriction of `g` to the complements commutes with the inclusions. -/
theorem complementMap_complementι {Z Z' : (SmoothProjectiveScheme k).FullSubcategory}
    {U U' : Scheme.{u}}
    (f : U ⟶ Z.obj.left) (f' : U' ⟶ Z'.obj.left) [IsClosedImmersion f] [IsOpenImmersion f]
    [IsClosedImmersion f'] [IsOpenImmersion f'] (g : Z ⟶ Z')
    (h : g.hom.left ⁻¹' Set.range f' ⊆ Set.range f) :
    complementMap f f' g h ≫ complementι Z' f' = complementι Z f ≫ g :=
  hom_ext_left (complementLift_ι f f' g h)

end Clopen

section Decomposition

variable {k' k'' : Type u} [CommRing k'] [CommRing k''] [Algebra k k'] [Algebra k k'']
  [Algebra k' k''] [IsScalarTower k k' k''] [Module.Finite k k'] [Algebra.Etale k k']
  [Module.Finite k k''] [Algebra.Etale k k'']
  {X : Scheme.{u}} (π : X ⟶ Spec (.of k')) [Smooth π] (hπ : IsProjectiveMorphism π)

/-- An étale algebra is formally unramified. -/
@[sga "3 XI 1.4" "affine over a field"]
theorem formallyUnramified_of_etale (A : Type u) [CommRing A] [Algebra k A] [Algebra.Etale k A] :
    Algebra.FormallyUnramified k A :=
  (Algebra.Etale.iff_formallyUnramified_and_smooth.mp inferInstance).1

attribute [local instance] formallyUnramified_of_etale

/-- The comparison morphism is a closed immersion. -/
instance isClosedImmersion_comparison :
    IsClosedImmersion (comparison k π hπ (k'' := k'')).hom.left :=
  inferInstanceAs (IsClosedImmersion (baseChangeComparison k k'' π))

/-- The comparison morphism is an open immersion. -/
instance isOpenImmersion_comparison :
    IsOpenImmersion (comparison k π hπ (k'' := k'')).hom.left :=
  inferInstanceAs (IsOpenImmersion (baseChangeComparison k k'' π))

/-- The graph is a closed immersion. -/
instance isClosedImmersion_graph :
    IsClosedImmersion (graphHom k (k' := k') (k'' := k'')).hom.left :=
  inferInstanceAs (IsClosedImmersion (specGraph k k' k''))

/-- The graph is an open immersion. -/
instance isOpenImmersion_graph :
    IsOpenImmersion (graphHom k (k' := k') (k'' := k'')).hom.left :=
  inferInstanceAs (IsOpenImmersion (specGraph k k' k''))


/-- The complement `X ×_{Spec k'} Spec l` of `X ×_{Spec k'} Spec k''` in `X ×_{Spec k} Spec k''`,
where `k' ⊗_k k'' = k'' × l`. -/
def baseChangeComplement : (SmoothProjectiveScheme k).FullSubcategory :=
  complementObj (prod (ofOver k π hπ) (spec k k'')) (comparison k π hπ (k'' := k'')).hom.left

/-- The inclusion of the complement into `X ×_{Spec k} Spec k''`. -/
abbrev baseChangeComplementι :
    baseChangeComplement k π hπ (k'' := k'') ⟶ prod (ofOver k π hπ) (spec k k'') :=
  complementι _ _

/-- The complement `Spec l` of the graph of `Spec k'' ⟶ Spec k'` in
`Spec k' ×_{Spec k} Spec k''`. -/
def graphComplement : (SmoothProjectiveScheme k).FullSubcategory :=
  complementObj (prod (spec k k') (spec k k'')) (graphHom k (k' := k') (k'' := k'')).hom.left

/-- The inclusion of the complement of the graph. -/
abbrev graphComplementι :
    graphComplement k (k' := k') (k'' := k'') ⟶ prod (spec k k') (spec k k'') :=
  complementι _ _

/-- **`X ×_{Spec k} Spec k'' = (X ×_{Spec k'} Spec k'') ⨿ (X ×_{Spec k'} Spec l)`**, as a
coproduct of smooth projective schemes over `k`. -/
def isColimitBaseChange :
    IsColimit (BinaryCofan.mk (comparison k π hπ (k'' := k'')) (baseChangeComplementι k π hπ)) :=
  isColimitOfIsColimitMapCofan
    (nonempty_isColimit_rangeComplement (comparison k π hπ (k'' := k'')).hom.left).some

/-- **`Spec k' ×_{Spec k} Spec k'' = Spec k'' ⨿ Spec l`**, as a coproduct of smooth projective
schemes over `k`. -/
def isColimitGraph :
    IsColimit (BinaryCofan.mk (graphHom k (k' := k') (k'' := k'')) (graphComplementι k)) :=
  isColimitOfIsColimitMapCofan
    (nonempty_isColimit_rangeComplement (graphHom k (k' := k') (k'' := k'')).hom.left).some

/-- The preimage of the graph under `π × id` is `X ×_{Spec k'} Spec k''`. -/
theorem preimage_range_graph :
    (productHom k π hπ (k'' := k'')).hom.left ⁻¹'
        Set.range (graphHom k (k' := k') (k'' := k'')).hom.left ⊆
      Set.range (comparison k π hπ (k'' := k'')).hom.left :=
  (range_baseChangeComparison k k'' π).symm.subset

/-- The morphism `π × id` restricted to the complements: `X ×_{Spec k'} Spec l ⟶ Spec l`. -/
def complementHom :
    baseChangeComplement k π hπ (k'' := k'') ⟶ graphComplement k (k' := k') (k'' := k'') :=
  complementMap _ _ (productHom k π hπ) (preimage_range_graph k π hπ)

/-- `π × id` restricted to the complements commutes with the inclusions. -/
theorem complementHom_graphComplementι :
    complementHom k π hπ (k'' := k'') ≫ graphComplementι k (k' := k') (k'' := k'') =
      baseChangeComplementι k π hπ ≫ productHom k π hπ :=
  complementMap_complementι _ _ _ _

end Decomposition

end Stacks.WeilCohomology.SmoothProjectiveScheme

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

/-! ### Degree zero and the Künneth map against a degree-zero factor -/

/-- Pullback `f^* : H^0(Y) → H^0(X)` on degree-zero parts. -/
def H0.pullHom {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) : W.H0 Y →ₐ[F] W.H0 X
    :=
  ((W.pull f).comp (W.H0 Y).val).codRestrict (W.H0 X) fun c => W.pull_grade f 0 _ c.2

/-- As a class in `H^*(X)`, `H0.pullHom W f c` is `f^*c`. -/
@[simp]
theorem H0.coe_pullHom {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (c : W.H0 Y) :
    (H0.pullHom W f c : W.H X) = W.pull f c :=
  rfl

/-- If `H^*(X)` is concentrated in degree zero, `H^0(X) = H^*(X)`. -/
theorem bijective_H0_val_of_grade_eq_bot {X : (SmoothProjectiveScheme k).FullSubcategory}
    (hX : ∀ i : ℤ, i ≠ 0 → W.grade X i = ⊥) : Function.Bijective (W.H0 X).val :=
  ⟨Subtype.val_injective, fun x =>
    ⟨⟨x, (H0_eq_top_of_grade_eq_bot hX).symm ▸ Algebra.mem_top⟩, rfl⟩⟩

/-- The Künneth map `H^*(X) ⊗_F H^0(Y) → H^*(X × Y)`, `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`, as a map of
`F`-algebras: `pr₂^*b` lies in degree zero, hence is central. -/
def kunnethH0 (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    W.H X ⊗[F] W.H0 Y →ₐ[F] W.H (prod X Y) :=
  Algebra.TensorProduct.lift (W.pull (fst X Y)) ((W.pull (snd X Y)).comp (W.H0 Y).val)
    fun _a b => (W.mul_comm_of_mem_grade_zero _ (W.pull_grade (snd X Y) 0 _ b.2) _).symm

/-- The Künneth map `kunnethH0` sends `a ⊗ b` to `pr₁^*a ∪ pr₂^*b`. -/
@[simp]
theorem kunnethH0_tmul (X Y : (SmoothProjectiveScheme k).FullSubcategory) (a : W.H X) (b : W.H0 Y) :
    W.kunnethH0 X Y (a ⊗ₜ b) = W.pull (fst X Y) a * W.pull (snd X Y) b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

/-- Under (B)(a), the Künneth map against `H^0(Y)` is bijective when `H^*(Y)` is concentrated in
degree zero. -/
theorem bijective_kunnethH0 (hB : W.KunnethIsomorphism)
    (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    (hY : ∀ i : ℤ, i ≠ 0 → W.grade Y i = ⊥) : Function.Bijective (W.kunnethH0 X Y) := by
  let e : W.H0 Y ≃ₗ[F] W.H Y :=
    LinearEquiv.ofBijective (W.H0 Y).val.toLinearMap (W.bijective_H0_val_of_grade_eq_bot hY)
  have h : (W.kunnethH0 X Y).toLinearMap = W.kunnethMap X Y ∘ₗ e.lTensor (W.H X) :=
    TensorProduct.ext' fun a b => by simp [e]; rfl
  change Function.Bijective (W.kunnethH0 X Y).toLinearMap
  rw [h]
  exact (hB X Y).comp (e.lTensor (W.H X)).bijective

/-- Restriction to the two summands of a disjoint union, as a map of `F`-algebras. -/
def restrictPair {X Y : (SmoothProjectiveScheme k).FullSubcategory} (c : BinaryCofan X Y) :
    W.H c.pt →ₐ[F] W.H X × W.H Y :=
  (W.pull c.inl).prod (W.pull c.inr)

/-- `restrictPair c` sends a class to its pair of pullbacks along the two inclusions. -/
@[simp]
theorem restrictPair_apply {X Y : (SmoothProjectiveScheme k).FullSubcategory} (c : BinaryCofan X Y)
    (a : W.H c.pt) :
    W.restrictPair c a = (W.pull c.inl a, W.pull c.inr a) :=
  rfl

/-- Functoriality of pullback, applied to a class. -/
theorem pull_apply_comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : W.H Z) :
    W.pull (f ≫ g) a = W.pull f (W.pull g a) := by
  rw [W.pull_comp]
  rfl

/-! ### The scalar extension -/

section ScalarExtension

variable {k' k'' : Type u} [CommRing k'] [CommRing k''] [Algebra k k'] [Algebra k k'']
  [Algebra k' k''] [IsScalarTower k k' k''] [Module.Finite k k'] [Algebra.Etale k k']
  [Module.Finite k k''] [Algebra.Etale k k'']
  {X : Scheme.{u}} (π : X ⟶ Spec (.of k')) [Smooth π] (hπ : IsProjectiveMorphism π)

/-- `H^*(X)` is an `H^0(Spec k')`-algebra by pullback along the structure morphism
`X ⟶ Spec k'`. -/
instance algebraH0SpecOfOver : Algebra (W.H0 (spec k k')) (W.H (ofOver k π hπ)) :=
  H0.algebraOfHom W (toSpec k π hπ)

/-- The `H^0(Spec k')`-algebra structure on `H^*(X)` is compatible with the `F`-algebra
structure. -/
instance : IsScalarTower F (W.H0 (spec k k')) (W.H (ofOver k π hπ)) :=
  IsScalarTower.of_algebraMap_eq fun c => ((W.pull (toSpec k π hπ)).commutes c).symm

/-- `H^0(Spec k'')` is an `H^0(Spec k')`-algebra by pullback along `Spec k'' ⟶ Spec k'`. -/
instance algebraH0SpecTower : Algebra (W.H0 (spec k k')) (W.H0 (spec k k'')) :=
  (H0.pullHom W (specTower k (k' := k') (k'' := k''))).toAlgebra

/-- The `H^0(Spec k')`-algebra structure on `H^0(Spec k'')` is compatible with the `F`-algebra
structure. -/
instance : IsScalarTower F (W.H0 (spec k k')) (W.H0 (spec k k'')) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((H0.pullHom W (specTower k (k' := k') (k'' := k''))).commutes c).symm

/-- `H^*(X ×_{Spec k'} Spec k'')` is an `H^0(Spec k'')`-algebra by pullback along the projection
to `Spec k''`. -/
instance algebraH0SpecBaseChange :
    Algebra (W.H0 (spec k k'')) (W.H (baseChangeObj k π hπ (k'' := k''))) :=
  H0.algebraOfHom W (baseChangeSnd k π hπ)

/-- `H^*(X ×_{Spec k'} Spec k'')` is an `H^0(Spec k')`-algebra by pullback along
`X ×_{Spec k'} Spec k'' ⟶ Spec k'`. -/
instance algebraH0SpecBaseChange' :
    Algebra (W.H0 (spec k k')) (W.H (baseChangeObj k π hπ (k'' := k''))) :=
  H0.algebraOfHom W (baseChangeSnd k π hπ ≫ specTower k)

/-- The two `H^0(Spec k')`-algebra structures on `H^*(X ×_{Spec k'} Spec k'')` agree. -/
instance : IsScalarTower (W.H0 (spec k k')) (W.H0 (spec k k''))
    (W.H (baseChangeObj k π hπ (k'' := k''))) :=
  IsScalarTower.of_algebraMap_eq fun _c => W.pull_apply_comp _ _ _

/-- Pullback along the projection `X ×_{Spec k'} Spec k'' ⟶ X`, as a map of
`H^0(Spec k')`-algebras. -/
def pullBaseChangeFst :
    W.H (ofOver k π hπ) →ₐ[W.H0 (spec k k')] W.H (baseChangeObj k π hπ (k'' := k'')) :=
  AlgHom.mk (W.pull (baseChangeFst k π hπ)).toRingHom fun c => by
    change W.pull (baseChangeFst k π hπ) (W.pull (toSpec k π hπ) (c : W.H (spec k k'))) =
      W.pull (baseChangeSnd k π hπ ≫ specTower k (k' := k') (k'' := k'')) (c : W.H (spec k k'))
    rw [← W.pull_apply_comp, baseChangeFst_toSpec]

/-- `pullBaseChangeFst π hπ` is pullback along `baseChangeFst k π hπ`. -/
@[simp]
theorem pullBaseChangeFst_apply (a : W.H (ofOver k π hπ)) :
    W.pullBaseChangeFst π hπ (k'' := k'') a = W.pull (baseChangeFst k π hπ) a :=
  rfl

/-- **The comparison map of Stacks 0FHX**:
`H^*(X) ⊗_{H^0(Spec k')} H^0(Spec k'') ⟶ H^*(X ×_{Spec k'} Spec k'')`,
`a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`. -/
def scalarExtensionMap :
    W.H (ofOver k π hπ) ⊗[W.H0 (spec k k')] W.H0 (spec k k'') →ₐ[W.H0 (spec k k')]
      W.H (baseChangeObj k π hπ (k'' := k'')) :=
  scalarExtensionHom (W.pullBaseChangeFst π hπ)

/-- The comparison map `scalarExtensionMap` sends `a ⊗ b` to `pr₁^*a ∪ pr₂^*b`. -/
@[simp]
theorem scalarExtensionMap_tmul (a : W.H (ofOver k π hπ)) (b : W.H0 (spec k k'')) :
    W.scalarExtensionMap π hπ (a ⊗ₜ b) =
      W.pull (baseChangeFst k π hπ) a * W.pull (baseChangeSnd k π hπ) b :=
  scalarExtensionHom_tmul _ a b

/-- The comparison map preserves degrees: it sends `H^i(X) ⊗ H^0(Spec k'')` into
`H^i(X ×_{Spec k'} Spec k'')`. -/
theorem scalarExtensionMap_tmul_mem_grade {i : ℤ} {a : W.H (ofOver k π hπ)}
    (ha : a ∈ W.grade _ i) (b : W.H0 (spec k k'')) :
    W.scalarExtensionMap π hπ (a ⊗ₜ b) ∈ W.grade (baseChangeObj k π hπ (k'' := k'')) i := by
  rw [scalarExtensionMap_tmul, ← add_zero i]
  exact SetLike.GradedMul.mul_mem (W.pull_grade _ i a ha) (W.pull_grade _ 0 _ b.2)

variable (hzero : ∀ (A : Type u) [CommRing A] [Algebra k A] [Module.Finite k A]
    [Algebra.Etale k A] (i : ℤ), i ≠ 0 → W.grade (spec k A) i = ⊥)
  (hunion : ∀ {Y₁ Y₂ : (SmoothProjectiveScheme k).FullSubcategory} (c : BinaryCofan Y₁ Y₂),
      IsColimit c →
    Function.Bijective (W.restrictPair c))

include hzero hunion in
/-- The comparison map `scalarExtensionMap π hπ` is bijective, given that the Künneth map is an
isomorphism, that `H^i(Spec A) = 0` for `i ≠ 0` and every finite étale `k`-algebra `A`, and that
restriction to the two summands of every binary coproduct is bijective. -/
theorem bijective_scalarExtensionMap_of (hB : W.KunnethIsomorphism) :
    Function.Bijective (W.scalarExtensionMap π hπ (k'' := k'')) := by
  -- the decomposition `H^*(X) ⊗_F H^0(Spec k'') = H^*(X ×_{k'} k'') × H^*(X ×_{k'} l)`
  let κ := (W.restrictPair (BinaryCofan.mk (comparison k π hπ (k'' := k''))
    (baseChangeComplementι k π hπ))).comp (W.kunnethH0 (ofOver k π hπ) (spec k k''))
  have hκ : Function.Bijective κ :=
    (hunion _ (isColimitBaseChange k π hπ (k'' := k''))).comp
      (W.bijective_kunnethH0 hB _ _ (hzero k''))
  let kunneth := AlgEquiv.ofBijective κ hκ
  -- the Künneth isomorphism `H^0(Spec k') ⊗_F H^0(Spec k'') = H^*(Spec k' × Spec k'')`
  let κT := (W.kunnethH0 (spec k k') (spec k k'')).comp
    (Algebra.TensorProduct.map (W.H0 (spec k k')).val (AlgHom.id F (W.H0 (spec k k''))))
  have hκT : Function.Bijective κT := by
    refine (W.bijective_kunnethH0 hB _ _ (hzero k'')).comp ?_
    let e := LinearEquiv.ofBijective (W.H0 (spec k k')).val.toLinearMap
      (W.bijective_H0_val_of_grade_eq_bot (hzero k'))
    have h : (Algebra.TensorProduct.map (W.H0 (spec k k')).val
        (AlgHom.id F (W.H0 (spec k k'')))).toLinearMap = e.rTensor (W.H0 (spec k k'')) :=
      TensorProduct.ext' fun _ _ => rfl
    convert (e.rTensor (W.H0 (spec k k''))).bijective using 1
    exact congrArg DFunLike.coe h
  -- the idempotent cutting out `Spec l` in `Spec k' ×_{Spec k} Spec k''`
  obtain ⟨ε, hε⟩ := (hunion _ (isColimitGraph k (k' := k') (k'' := k''))).2 (0, 1)
  simp only [restrictPair_apply, BinaryCofan.mk_inl, BinaryCofan.mk_inr, Prod.mk.injEq] at hε
  obtain ⟨z, rfl⟩ := hκT.2 ε
  have hκT_tmul : ∀ (a : W.H0 (spec k k')) (b : W.H0 (spec k k'')),
      κT (a ⊗ₜ b) = W.pull (fst _ _) a * W.pull (snd _ _) b := fun a b => by
    simp [κT]
  -- multiplication `F' ⊗_F F'' → F''` is restriction along the graph
  have hmul : (W.H0 (spec k k'')).val.comp (tensorMulHom F (W.H0 (spec k k'))
      (W.H0 (spec k k''))) = (W.pull (graphHom k)).comp κT := by
    refine Algebra.TensorProduct.ext' fun a b => ?_
    simp only [AlgHom.comp_apply, tensorMulHom_tmul, hκT_tmul, map_mul, ← W.pull_apply_comp,
        graphHom_fst, graphHom_snd, W.pull_id]
    rfl
  -- the action of `F' ⊗_F F''` on `H^*(X) ⊗_F F''` is pullback along `π × id`
  have hact : (W.kunnethH0 (ofOver k π hπ) (spec k k'')).comp (tensorActionHom F
      (W.H0 (spec k k')) (W.H0 (spec k k'')) (W.H (ofOver k π hπ))) =
      (W.pull (productHom k π hπ)).comp κT := by
    refine Algebra.TensorProduct.ext' fun a b => ?_
    simp only [AlgHom.comp_apply, tensorActionHom_tmul, hκT_tmul, kunnethH0_tmul, map_mul,
      ← W.pull_apply_comp, productHom_fst, productHom_snd]
    rw [W.pull_apply_comp (fst _ _) (toSpec k π hπ)]
    rfl
  refine bijective_scalarExtensionHom_of_idempotent (W.pullBaseChangeFst π hπ) kunneth ?_ z ?_ ?_
  · intro a b
    show W.pull (comparison k π hπ) (W.kunnethH0 _ _ (a ⊗ₜ b)) = _
    rw [kunnethH0_tmul, map_mul, ← W.pull_apply_comp, ← W.pull_apply_comp, comparison_fst,
      comparison_snd]
    rfl
  · exact Subtype.ext ((AlgHom.congr_fun hmul z).trans hε.1)
  · show W.restrictPair (BinaryCofan.mk (comparison k π hπ (k'' := k''))
      (baseChangeComplementι k π hπ)) (W.kunnethH0 _ _ _) = _
    rw [← AlgHom.comp_apply, hact]
    show (W.pull (comparison k π hπ) (W.pull (productHom k π hπ) (κT z)),
      W.pull (baseChangeComplementι k π hπ) (W.pull (productHom k π hπ) (κT z))) = _
    rw [← W.pull_apply_comp, ← W.pull_apply_comp, comparison_productHom,
      ← complementHom_graphComplementι, W.pull_apply_comp, W.pull_apply_comp]
    have h1 : W.pull (graphHom k) (κT z) = 0 := hε.1
    have h2 : W.pull (graphComplementι k (k' := k') (k'' := k'')) (κT z) = 1 := hε.2
    rw [h1, h2, map_zero, map_one]

/-- **Stacks 0FHQ (1) for `Spec A`**: for a finite étale `k`-algebra `A`, `H^i(Spec A) = 0` for
`i ≠ 0`. For `A ≠ 0` this is Stacks 0FHQ (1), `Spec A` being of dimension zero; for `A = 0` the
cohomology of the empty scheme vanishes (Stacks 0FHF). -/
theorem grade_spec_eq_bot [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (A : Type u) [CommRing A] [Algebra k A]
    [Module.Finite k A] [Algebra.Etale k A] (i : ℤ) (hi : i ≠ 0) : W.grade (spec k A) i = ⊥ := by
  rcases subsingleton_or_nontrivial A with hA0 | hA0
  · have : IsEmpty (spec k A).obj.left :=
      show IsEmpty (PrimeSpectrum A) from PrimeSpectrum.isEmpty_iff_subsingleton.mpr hA0
    have := subsingleton_of_isEmpty (W := W) hB.kunnethIsomorphism hC.pullback hC.mul hC.point
      (spec k A)
    exact Subsingleton.elim _ _
  · exact grade_eq_bot_of_dimension_zero hA hB hC
      (topologicalKrullDim_spec_eq_zero (k := k) A) hi

/-- **Stacks Project, Tag 0FHX.** Assume given `(D0)`–`(D3)` satisfying `(A)`, `(B)` and `(C)`.
Let `k''/k'/k` be finite separable algebras and let `X` be a smooth projective scheme over `k'`.
Then the comparison map

`H^*(X) ⊗_{H^0(Spec k')} H^0(Spec k'') ⟶ H^*(X ×_{Spec k'} Spec k'')`,
`a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`,

is bijective. Here `H^*(X)` is an `H^0(Spec k')`-algebra by pullback along `X ⟶ Spec k'`, and
`X` and `X ×_{Spec k'} Spec k''` are smooth projective schemes over `k`. -/
@[stacks 0FHX "H^*(X) ⊗_{H^0(Spec k')} H^0(Spec k'') = H^*(X ×_{Spec k'} Spec k'') for the actual \
Weil data, X smooth projective over k', k''/k'/k finite separable"]
theorem bijective_scalarExtensionMap [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) :
    Function.Bijective (W.scalarExtensionMap π hπ (k'' := k'')) :=
  W.bijective_scalarExtensionMap_of π hπ (W.grade_spec_eq_bot hA hB hC)
    (fun _c hc => pullbackPair_bijective_of_isColimit hA hB hC hc) hB.kunnethIsomorphism

/-- **Stacks Project, Tag 0FHX**, as an isomorphism of `H^0(Spec k')`-algebras:
`H^*(X) ⊗_{H^0(Spec k')} H^0(Spec k'') ≃ H^*(X ×_{Spec k'} Spec k'')`,
`a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`. -/
@[stacks 0FHX "the H^0(Spec k')-algebra isomorphism H^*(X) ⊗_{H^0(Spec k')} H^0(Spec k'') ≃ \
H^*(X ×_{Spec k'} Spec k'') for the actual Weil data"]
def scalarExtensionAlgEquiv [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) :
    W.H (ofOver k π hπ) ⊗[W.H0 (spec k k')] W.H0 (spec k k'') ≃ₐ[W.H0 (spec k k')]
      W.H (baseChangeObj k π hπ (k'' := k'')) :=
  AlgEquiv.ofBijective (W.scalarExtensionMap π hπ) (W.bijective_scalarExtensionMap π hπ hA hB hC)

/-- The isomorphism `scalarExtensionAlgEquiv` sends `a ⊗ b` to `pr₁^*a ∪ pr₂^*b`. -/
@[simp]
theorem scalarExtensionAlgEquiv_tmul [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (a : W.H (ofOver k π hπ))
    (b : W.H0 (spec k k'')) :
    W.scalarExtensionAlgEquiv π hπ hA hB hC (a ⊗ₜ b) =
      W.pull (baseChangeFst k π hπ) a * W.pull (baseChangeSnd k π hπ) b :=
  W.scalarExtensionMap_tmul π hπ a b

end ScalarExtension

end Stacks.WeilCohomology.WeilData
