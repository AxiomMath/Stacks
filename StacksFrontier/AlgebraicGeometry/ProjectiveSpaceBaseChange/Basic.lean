module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace

/-!
# Projective space is stable under base change

`AlgebraicGeometry.projectiveSpaceOver n S` is the pullback `S ×_{⊤} ℙⁿ_ℤ` of the integral model
along the structure morphism of `S`, so a morphism `g : S' ⟶ S` of base schemes induces a
morphism `ℙⁿ_{S'} ⟶ ℙⁿ_S`, and the square

```
ℙⁿ_{S'} ---> ℙⁿ_S
  |            |
  v            v
  S'  ---g---> S
```

is cartesian. This is the statement that makes the base-change machinery applicable to projective
space: it is the input `IsPullback p k iX q` of
`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange`
([Stacks, Tag 02KH] in degree zero) and of every base-change statement phrased over a cartesian
square.

The cartesianness is pure pullback cancellation: pasting the square above onto the defining
square of `ℙⁿ_S` gives the defining square of `ℙⁿ_{S'}`, because `g` composed with the structure
morphism of `S` is the structure morphism of `S'` and the induced morphism is compatible with the
projections to the integral model.

## Main definitions

* `AlgebraicGeometry.projectiveSpaceOverMap`: the morphism `ℙⁿ_{S'} ⟶ ℙⁿ_S` induced by a morphism
  `S' ⟶ S` of base schemes.
* `AlgebraicGeometry.projectiveSpaceOverRingMap`: the same for a morphism of base rings.
* `AlgebraicGeometry.projectiveSpaceFieldExtensionMap`: the same for a field extension, which is
  the morphism `ℙⁿ_{K} ⟶ ℙⁿ_{k}` appearing in [Stacks, Tag 08A4].

## Main results

* `AlgebraicGeometry.isPullback_projectiveSpaceOverMap`: the square above is cartesian.
* `AlgebraicGeometry.isPullback_projectiveSpaceFieldExtensionMap`: its field-extension case.
* `AlgebraicGeometry.projectiveSpaceFieldExtensionMap` is an affine and flat morphism, both by
  base change from `Spec K ⟶ Spec k`.

## Implementation notes

No `@[stacks 08A4]` attribute is attached anywhere in this file. Tag 08A4 asserts that a coherent
sheaf on `ℙⁿ_k` is `m`-regular if and only if its pullback to `ℙⁿ_{K}` is, and the source proves
that from flat base change for cohomology, [Stacks, Tag 02KH] part (2), *in every degree*. The
tag is proved in `ProjectiveSpaceBaseChange/FieldExtension.lean` as
`AlgebraicGeometry.isMRegular_iff_fieldExtension`, over
`AlgebraicGeometry.isZero_Hgroup_projectiveSpace_baseChange_iff` there — that part of that tag
for projective space, in every degree. This file supplies the cartesian square those statements
are indexed by, with the construction of the morphism, which did not previously exist here.

`projectiveSpaceOverMap` is `CategoryTheory.Limits.pullback.map` with the identity on the
integral model, so its composite with the projection to the integral model is that projection,
and its composite with the structure morphism is the structure morphism followed by `g`. Those
two identities are `projectiveSpaceOverMap_snd` and `projectiveSpaceOverMap_fst`, and they are
exactly what the pullback cancellation lemma `CategoryTheory.IsPullback.of_right` consumes.

The orientation of `isPullback_projectiveSpaceOverMap` is chosen to match the hypothesis
`IsPullback p k iX q` of the degree-zero base-change theorem: the induced morphism is `p`, the
structure morphisms are `k` and `iX`, and `g` is `q`. Instance arguments deduced by base change
need the transpose, obtained with `CategoryTheory.IsPullback.flip`.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 08A4](https://stacks.math.columbia.edu/tag/08A4)
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- The morphism `ℙⁿ_{S'} ⟶ ℙⁿ_S` induced by a morphism `g : S' ⟶ S` of base schemes: both
projective spaces are pullbacks of the integral model over the terminal scheme, and this is the
induced morphism of pullbacks which is `g` on the base and the identity on the integral model. -/
public noncomputable def projectiveSpaceOverMap (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) :
    projectiveSpaceOver n S' ⟶ projectiveSpaceOver n S :=
  pullback.map _ _ _ _ g (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- `projectiveSpaceOverMap` is the identity on the integral model. -/
public theorem projectiveSpaceOverMap_snd (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) :
    projectiveSpaceOverMap n g ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      projectiveSpaceOver.toIntegralAtUniverse n S' := by
  rw [projectiveSpaceOverMap, pullback.map]
  exact pullback.lift_snd _ _ _

/-- `projectiveSpaceOverMap` lies over `g`. -/
public theorem projectiveSpaceOverMap_fst (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) :
    projectiveSpaceOverMap n g ≫ pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      pullback.fst (terminal.from S')
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) ≫ g := by
  rw [projectiveSpaceOverMap, pullback.map]
  exact pullback.lift_fst _ _ _

/-- **`projectiveSpaceOverMap` is functorial in the base scheme.** Both sides are morphisms into
the pullback defining `ℙⁿ_S`, and they agree on the base by
`AlgebraicGeometry.projectiveSpaceOverMap_fst` and on the integral model by
`AlgebraicGeometry.projectiveSpaceOverMap_snd`. -/
public theorem projectiveSpaceOverMap_comp (n : ℕ) {S'' S' S : Scheme.{u}} (g : S'' ⟶ S')
    (h : S' ⟶ S) :
    projectiveSpaceOverMap n g ≫ projectiveSpaceOverMap n h =
      projectiveSpaceOverMap n (g ≫ h) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projectiveSpaceOverMap_fst, ← Category.assoc,
      projectiveSpaceOverMap_fst, Category.assoc, projectiveSpaceOverMap_fst]
  · simp [projectiveSpaceOverMap_snd]

/-- **`projectiveSpaceOverMap` of an identity is an identity.** -/
public theorem projectiveSpaceOverMap_id (n : ℕ) (S : Scheme.{u}) :
    projectiveSpaceOverMap n (𝟙 S) = 𝟙 (projectiveSpaceOver n S) := by
  refine pullback.hom_ext ?_ ?_
  · simp [projectiveSpaceOverMap_fst]
  · simp [projectiveSpaceOverMap_snd]

/-- **Projective space is stable under base change.** The square whose horizontal arrows are
`projectiveSpaceOverMap n g` and `g` and whose vertical arrows are the structure morphisms is
cartesian: pasted onto the defining square of `ℙⁿ_S` it is the defining square of `ℙⁿ_{S'}`. -/
public theorem isPullback_projectiveSpaceOverMap (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) :
    IsPullback (projectiveSpaceOverMap n g)
      (pullback.fst (terminal.from S') (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))) g := by
  refine IsPullback.of_right ?_ (projectiveSpaceOverMap_fst n g)
    (IsPullback.of_hasPullback _ _).flip
  rw [projectiveSpaceOverMap_snd n g,
    show g ≫ terminal.from S = terminal.from S' from terminal.hom_ext _ _]
  exact (IsPullback.of_hasPullback _ _).flip

/-- The morphism `ℙⁿ_S ⟶ ℙⁿ_R` of projective spaces over rings induced by a ring map
`R ⟶ S`. -/
public noncomputable def projectiveSpaceOverRingMap (n : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    projectiveSpaceOverRing n S ⟶ projectiveSpaceOverRing n R :=
  projectiveSpaceOverMap n (Spec.map f)

/-- `AlgebraicGeometry.projectiveSpaceOverRingMap` is
`AlgebraicGeometry.projectiveSpaceOverMap` of the morphism of spectra, spelled so that the
functoriality of the latter applies to it. -/
public theorem projectiveSpaceOverRingMap_eq (n : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    projectiveSpaceOverRingMap n f = projectiveSpaceOverMap n (Spec.map f) :=
  rfl

/-- The map from projective space over `K` to projective space over `k` induced by a field
extension `k → K`. -/
public noncomputable def projectiveSpaceFieldExtensionMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] (n : ℕ) :
    projectiveSpaceOverRing n (.of K) ⟶ projectiveSpaceOverRing n (.of k) :=
  projectiveSpaceOverRingMap n (CommRingCat.ofHom (algebraMap k K))

/-- The field-extension case of `AlgebraicGeometry.isPullback_projectiveSpaceOverMap`:
`ℙⁿ_{K} = ℙⁿ_{k} ×_{Spec k} Spec K`. -/
public theorem isPullback_projectiveSpaceFieldExtensionMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] (n : ℕ) :
    IsPullback (projectiveSpaceFieldExtensionMap k K n)
      (pullback.fst (terminal.from (Spec (.of K)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      (pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  isPullback_projectiveSpaceOverMap n _

/-- The field-extension map of projective spaces is an affine morphism, being the base change of
`Spec K ⟶ Spec k`. -/
public instance isAffineHom_projectiveSpaceFieldExtensionMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] (n : ℕ) : IsAffineHom (projectiveSpaceFieldExtensionMap k K n) :=
  MorphismProperty.of_isPullback (isPullback_projectiveSpaceFieldExtensionMap k K n).flip
    inferInstance

/-- The field-extension map of projective spaces is flat, being the base change of
`Spec K ⟶ Spec k` and `K` being flat over `k`. -/
public instance flat_projectiveSpaceFieldExtensionMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] (n : ℕ) : Flat (projectiveSpaceFieldExtensionMap k K n) :=
  MorphismProperty.of_isPullback (isPullback_projectiveSpaceFieldExtensionMap k K n).flip
    inferInstance

end AlgebraicGeometry

end
