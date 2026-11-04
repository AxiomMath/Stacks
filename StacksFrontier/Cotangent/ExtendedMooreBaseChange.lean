module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.Cotangent.BaseChangeComplexCounit
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# Extended Moore complexes and base change

A map of simplicial modules whose target is read along a ring map `f : R → S` — a morphism
`α : X ⟶ (restrictScalars f).obj Y` of simplicial `R`-modules, for `Y` a simplicial `S`-module —
induces a map of the associated complexes. This file carries that induced map through the two
identifications it needs and records the three facts about it which the descent of
[Stacks, Tag 08SC] from the base `A[x]` to the base `A` consumes.

The complex associated to a simplicial module is the alternating-face-map (Moore) complex
reindexed so that simplicial degree `n` sits in cohomological degree `-n`, i.e. the composite
`AlgebraicTopology.extendedMooreFunctor` of `AlgebraicTopology.alternatingFaceMapComplex` with
`ComplexShape.Embedding.extendFunctor`. Neither step commutes with applying a functor degreewise
on the nose: the first is `AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso`
and the second `HomologicalComplex.mapHomologicalComplexExtendIso`. The induced map
`AlgebraicTopology.extendMooreMap` is the map of Moore complexes composed with both.

## Main definitions

* `AlgebraicTopology.extendedMooreFunctor`: the Moore complex of a simplicial object, reindexed
  along an embedding of complex shapes.
* `AlgebraicTopology.extendMooreMap`: **the induced map of extended Moore complexes**, for a
  morphism of simplicial objects whose target is read along a functor.
* `ModuleCat.shortComplexExtendScalarsAdjoint`: **the adjoint of a morphism of short complexes of
  complexes of modules** whose target is read along a ring map: extension of scalars of the
  morphism, followed by the counit.

## Main results

* `HomologicalComplex.mapHomologicalComplexExtendIso_hom_naturality`: the comparison
  isomorphism of extension and a degreewise functor is natural in the complex, in the `hom`
  direction. Mathlib's statement — and the one in
  `StacksFrontier/Algebra/Homology/Embedding/ExtendMap.lean` — is for `inv`.
* `AlgebraicTopology.extendMooreMap_comp_left` and
  `AlgebraicTopology.extendMooreMap_comp_right`: the induced map is compatible with composition
  on either side. These two are exactly the two commuting squares of a morphism of short
  complexes, so a morphism of short complexes of simplicial objects induces one of short
  complexes of extended Moore complexes with no further computation.
* `CommAlgCat.extendMooreMap_squareCotangentSimplicialMap`: the functoriality map
  `CommAlgCat.squareCotangentComplexMap` of [Stacks, Tag 08PN] on the cotangent complexes **is**
  the induced map of the simplicial functoriality map. Both are the Moore complex of the
  simplicial map composed with the same two identifications, so this is `rfl`.
* `ModuleCat.shortExact_map_extendScalars_of_flat`: extension of scalars along a flat ring map
  keeps a short exact sequence of complexes of modules short exact.

## Implementation notes

`AlgebraicTopology.extendMooreMap` is stated for an arbitrary additive functor and an arbitrary
embedding of complex shapes, not for `ModuleCat.restrictScalars` and
`ComplexShape.embeddingUpIntLE 0`: the content is the two identifications and nothing about
modules enters. Both compatibility lemmas are proved by rewriting, the only inputs being
functoriality of `HomologicalComplex.extendMap`, naturality of the Moore comparison, and
`HomologicalComplex.mapHomologicalComplexExtendIso_hom_naturality`.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial

universe u

namespace HomologicalComplex

/-- **Being a quasi-isomorphism transports along an equality of morphisms.** Stated for two
morphisms which are *variables*, so that the motive is always type-correct; a `rw` of an equality
of two large concrete composites inside `QuasiIso` is routinely rejected for want of
type-correctness at `implicit` transparency. -/
theorem quasiIso_of_eq {V : Type*} [Category* V] [HasZeroMorphisms V] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex V c}
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] {φ ψ : K ⟶ L} (h : φ = ψ)
    (hφ : QuasiIso φ) : QuasiIso ψ :=
  h ▸ hφ

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : HomologicalComplex C c)

/-- **The comparison isomorphism of extension and a degreewise functor is natural in the
complex**, in the `hom` direction: this is
`HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality` with both isomorphisms
inverted. -/
theorem mapHomologicalComplexExtendIso_hom_naturality {L : HomologicalComplex C c} (φ : K ⟶ L)
    (e : c.Embedding c') :
    extendMap ((F.mapHomologicalComplex c).map φ) e ≫
        (mapHomologicalComplexExtendIso F L e).hom =
      (mapHomologicalComplexExtendIso F K e).hom ≫
        (F.mapHomologicalComplex c').map (extendMap φ e) := by
  rw [← cancel_epi (mapHomologicalComplexExtendIso F K e).inv, Iso.inv_hom_id_assoc,
    ← Category.assoc, ← mapHomologicalComplexExtendIso_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end HomologicalComplex

namespace AlgebraicTopology

/-- **The complex of a simplicial object, reindexed along an embedding of complex shapes.** For
the embedding `ComplexShape.embeddingUpIntLE 0` this is the shape in which the cotangent complex
is written: simplicial degree `n` sits in cohomological degree `-n`. -/
noncomputable abbrev extendedMooreFunctor (V : Type*) [Category* V] [Preadditive V]
    [HasZeroObject V] {ι' : Type*} {c' : ComplexShape ι'}
    (e : (ComplexShape.down ℕ).Embedding c') :
    SimplicialObject V ⥤ HomologicalComplex V c' :=
  alternatingFaceMapComplex V ⋙ e.extendFunctor V

section

variable {V V' : Type*} [Category* V] [Category* V'] [Preadditive V] [Preadditive V']
  [HasZeroObject V] [HasZeroObject V'] (F : V ⥤ V') [F.Additive]
  {ι' : Type*} {c' : ComplexShape ι'} (e : (ComplexShape.down ℕ).Embedding c')

/-- **The induced map of extended Moore complexes** of a morphism `α : X ⟶ F(Y)` of simplicial
objects, the target read along an additive functor `F`: the Moore complex of `α`, followed by the
comparison of the Moore complex with `F` applied degreewise and then by the comparison of the
reindexing with `F` applied degreewise. -/
noncomputable def extendMooreMap {X : SimplicialObject V'} {Y : SimplicialObject V}
    (α : X ⟶ ((SimplicialObject.whiskering V V').obj F).obj Y) :
    (extendedMooreFunctor V' e).obj X ⟶
      (F.mapHomologicalComplex c').obj ((extendedMooreFunctor V e).obj Y) :=
  HomologicalComplex.extendMap ((alternatingFaceMapComplex V').map α ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app Y) e ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso F
      ((alternatingFaceMapComplex V).obj Y) e).hom

/-- The defining equation of `AlgebraicTopology.extendMooreMap`. -/
theorem extendMooreMap_eq {X : SimplicialObject V'} {Y : SimplicialObject V}
    (α : X ⟶ ((SimplicialObject.whiskering V V').obj F).obj Y) :
    extendMooreMap F e α =
      HomologicalComplex.extendMap ((alternatingFaceMapComplex V').map α ≫
          (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app Y) e ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso F
          ((alternatingFaceMapComplex V).obj Y) e).hom :=
  rfl

/-- **The induced map is compatible with precomposition.** -/
theorem extendMooreMap_comp_left {X X' : SimplicialObject V'} {Y : SimplicialObject V}
    (γ : X' ⟶ X) (α : X ⟶ ((SimplicialObject.whiskering V V').obj F).obj Y) :
    extendMooreMap F e (γ ≫ α) =
      (extendedMooreFunctor V' e).map γ ≫ extendMooreMap F e α := by
  rw [extendMooreMap_eq, extendMooreMap_eq, Functor.map_comp, Category.assoc,
    HomologicalComplex.extendMap_comp, Category.assoc]
  rfl

/-- **The induced map is compatible with postcomposition.** -/
theorem extendMooreMap_comp_right {X : SimplicialObject V'} {Y Z : SimplicialObject V}
    (α : X ⟶ ((SimplicialObject.whiskering V V').obj F).obj Y) (β : Y ⟶ Z) :
    extendMooreMap F e (α ≫ ((SimplicialObject.whiskering V V').obj F).map β) =
      extendMooreMap F e α ≫
        (F.mapHomologicalComplex c').map ((extendedMooreFunctor V e).map β) := by
  have hnat : (alternatingFaceMapComplex V').map
        (((SimplicialObject.whiskering V V').obj F).map β) ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app Z =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.app Y ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((alternatingFaceMapComplex V).map β) :=
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).inv.naturality β
  rw [extendMooreMap_eq, extendMooreMap_eq, Functor.map_comp, Category.assoc, hnat,
    ← Category.assoc, HomologicalComplex.extendMap_comp, Category.assoc,
    HomologicalComplex.mapHomologicalComplexExtendIso_hom_naturality]
  exact (Category.assoc _ _ _).symm

end

end AlgebraicTopology

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {ι : Type*} (c : ComplexShape ι)

/-- **The adjoint of a morphism of short complexes of complexes of modules whose target is read
along a ring map.** Each component is extension of scalars of the corresponding component,
followed by the counit of `ModuleCat.extendScalars f ⊣ ModuleCat.restrictScalars f`; the two
commuting squares are the original ones together with
`ModuleCat.extendRestrictScalarsAdjCounitComplex_naturality`. -/
noncomputable def shortComplexExtendScalarsAdjoint
    {P : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c)}
    {Q : ShortComplex (HomologicalComplex (ModuleCat.{u} S) c)}
    (φ : P ⟶ Q.map ((restrictScalars f).mapHomologicalComplex c)) :
    P.map ((extendScalars f).mapHomologicalComplex c) ⟶ Q where
  τ₁ := ((extendScalars f).mapHomologicalComplex c).map φ.τ₁ ≫
    extendRestrictScalarsAdjCounitComplex f c Q.X₁
  τ₂ := ((extendScalars f).mapHomologicalComplex c).map φ.τ₂ ≫
    extendRestrictScalarsAdjCounitComplex f c Q.X₂
  τ₃ := ((extendScalars f).mapHomologicalComplex c).map φ.τ₃ ≫
    extendRestrictScalarsAdjCounitComplex f c Q.X₃
  comm₁₂ := by
    have h := φ.comm₁₂
    dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_f] at h ⊢
    rw [Category.assoc, ← extendRestrictScalarsAdjCounitComplex_naturality,
      ← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
  comm₂₃ := by
    have h := φ.comm₂₃
    dsimp only [ShortComplex.map_X₂, ShortComplex.map_X₃, ShortComplex.map_g] at h ⊢
    rw [Category.assoc, ← extendRestrictScalarsAdjCounitComplex_naturality,
      ← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]

/-- The second component of `shortComplexExtendScalarsAdjoint f c φ` is extension of scalars of
`φ.τ₂` followed by the counit `extendRestrictScalarsAdjCounitComplex f c Q.X₂`. -/
@[simp]
theorem shortComplexExtendScalarsAdjoint_τ₂
    {P : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c)}
    {Q : ShortComplex (HomologicalComplex (ModuleCat.{u} S) c)}
    (φ : P ⟶ Q.map ((restrictScalars f).mapHomologicalComplex c)) :
    (shortComplexExtendScalarsAdjoint f c φ).τ₂ =
      ((extendScalars f).mapHomologicalComplex c).map φ.τ₂ ≫
        extendRestrictScalarsAdjCounitComplex f c Q.X₂ :=
  rfl

/-- The first component of `shortComplexExtendScalarsAdjoint f c φ` is extension of scalars of
`φ.τ₁` followed by the counit `extendRestrictScalarsAdjCounitComplex f c Q.X₁`. -/
@[simp]
theorem shortComplexExtendScalarsAdjoint_τ₁
    {P : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c)}
    {Q : ShortComplex (HomologicalComplex (ModuleCat.{u} S) c)}
    (φ : P ⟶ Q.map ((restrictScalars f).mapHomologicalComplex c)) :
    (shortComplexExtendScalarsAdjoint f c φ).τ₁ =
      ((extendScalars f).mapHomologicalComplex c).map φ.τ₁ ≫
        extendRestrictScalarsAdjCounitComplex f c Q.X₁ :=
  rfl

/-- The third component of `shortComplexExtendScalarsAdjoint f c φ` is extension of scalars of
`φ.τ₃` followed by the counit `extendRestrictScalarsAdjCounitComplex f c Q.X₃`. -/
@[simp]
theorem shortComplexExtendScalarsAdjoint_τ₃
    {P : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c)}
    {Q : ShortComplex (HomologicalComplex (ModuleCat.{u} S) c)}
    (φ : P ⟶ Q.map ((restrictScalars f).mapHomologicalComplex c)) :
    (shortComplexExtendScalarsAdjoint f c φ).τ₃ =
      ((extendScalars f).mapHomologicalComplex c).map φ.τ₃ ≫
        extendRestrictScalarsAdjCounitComplex f c Q.X₃ :=
  rfl

/-- **Extending the adjoint of an induced map of Moore complexes.** The adjoint of
`AlgebraicTopology.extendMooreMap` is, up to the comparison isomorphism of extension with
extension of scalars, the extension of the adjoint of the map of Moore complexes. This is
`ModuleCat.extendMap_comp_extendRestrictScalarsAdjCounitComplex` with the inner map folded back
into `AlgebraicTopology.extendMooreMap`. -/
theorem extendMap_extendScalars_extendMooreMap_comp_counit
    {X : SimplicialObject (ModuleCat.{u} R)} {Y : SimplicialObject (ModuleCat.{u} S)}
    (α : X ⟶ ((SimplicialObject.whiskering (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (restrictScalars f)).obj Y)
    {ι' : Type*} {c' : ComplexShape ι'} (e : (ComplexShape.down ℕ).Embedding c') :
    HomologicalComplex.extendMap
        (((extendScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).map
              ((alternatingFaceMapComplex (ModuleCat.{u} R)).map α ≫
                (alternatingFaceMapComplexCompMapHomologicalComplexIso
                  (restrictScalars f)).inv.app Y) ≫
            extendRestrictScalarsAdjCounitComplex f (ComplexShape.down ℕ)
              ((alternatingFaceMapComplex (ModuleCat.{u} S)).obj Y)) e =
      (HomologicalComplex.mapHomologicalComplexExtendIso (extendScalars f)
          ((alternatingFaceMapComplex (ModuleCat.{u} R)).obj X) e).hom ≫
        (((extendScalars f).mapHomologicalComplex c').map
            (AlgebraicTopology.extendMooreMap (restrictScalars f) e α) ≫
          extendRestrictScalarsAdjCounitComplex f c'
            ((AlgebraicTopology.extendedMooreFunctor (ModuleCat.{u} S) e).obj Y)) :=
  extendMap_comp_extendRestrictScalarsAdjCounitComplex f (ComplexShape.down ℕ) e _

/-- **The adjoint of an induced map of extended Moore complexes is an isomorphism as soon as it
is one in every simplicial degree.** The Moore complex of the adjoint is degreewise the adjoint
of the degreewise map, and extension along an embedding of complex shapes is a functor, so it
carries an isomorphism to one. -/
theorem isIso_extendScalars_extendMooreMap_comp_counit
    {X : SimplicialObject (ModuleCat.{u} R)} {Y : SimplicialObject (ModuleCat.{u} S)}
    (α : X ⟶ ((SimplicialObject.whiskering (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (restrictScalars f)).obj Y)
    {ι' : Type*} {c' : ComplexShape ι'} (e : (ComplexShape.down ℕ).Embedding c')
    (h : ∀ n : SimplexCategoryᵒᵖ, IsIso ((extendScalars f).map (α.app n) ≫
      (extendRestrictScalarsAdj f).counit.app (Y.obj n))) :
    IsIso (((extendScalars f).mapHomologicalComplex c').map
        (AlgebraicTopology.extendMooreMap (restrictScalars f) e α) ≫
      extendRestrictScalarsAdjCounitComplex f c'
        ((AlgebraicTopology.extendedMooreFunctor (ModuleCat.{u} S) e).obj Y)) := by
  refine @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ (Iso.isIso_hom _) ?_
    (extendMap_extendScalars_extendMooreMap_comp_counit f α e).symm
  change IsIso ((e.extendFunctor (ModuleCat.{u} S)).map _)
  exact @Functor.map_isIso _ _ _ _ _ _ _ _
    (@HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ fun n => h (op ⦋n⦌))

/-- **A commuting square of complexes, base changed with the counit folded in.** If
`a ≫ b = a' ≫ (restrictScalars f)(b')`, then the two adjoint composites agree. Stated for
arbitrary morphisms of complexes, so that both sides are one spelling by construction; the
consumers instantiate it at the naturality square of the comparison of [Stacks, Tag 08PU]. -/
theorem extendScalars_comp_counit_naturality
    {K K' : HomologicalComplex (ModuleCat.{u} R) c}
    {L L' : HomologicalComplex (ModuleCat.{u} S) c} (a : K ⟶ K')
    (b : K' ⟶ ((restrictScalars f).mapHomologicalComplex c).obj L')
    (a' : K ⟶ ((restrictScalars f).mapHomologicalComplex c).obj L) (b' : L ⟶ L')
    (h : a ≫ b = a' ≫ ((restrictScalars f).mapHomologicalComplex c).map b') :
    ((extendScalars f).mapHomologicalComplex c).map a ≫
        (((extendScalars f).mapHomologicalComplex c).map b ≫
          extendRestrictScalarsAdjCounitComplex f c L') =
      (((extendScalars f).mapHomologicalComplex c).map a' ≫
          extendRestrictScalarsAdjCounitComplex f c L) ≫ b' := by
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc,
    extendRestrictScalarsAdjCounitComplex_naturality, ← Category.assoc]

/-- **Extension of scalars along a flat ring map keeps a short exact sequence of complexes short
exact.** Short exactness of a sequence of complexes is degreewise, and in each degree extension
of scalars along a flat map preserves finite limits (`extendScalars_preservesFiniteLimits_of_flat'`)
and finite colimits (it is a left adjoint). -/
theorem shortExact_map_extendScalars_of_flat (hf : f.Flat)
    {P : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c)} (hP : P.ShortExact) :
    (P.map ((extendScalars f).mapHomologicalComplex c)).ShortExact := by
  have : PreservesFiniteLimits (extendScalars.{u, u, u} f) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} f hf
  have : PreservesColimitsOfSize.{0, 0} (extendScalars.{u, u, u} f) :=
    (extendRestrictScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (extendScalars.{u, u, u} f) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact] at hP ⊢
  intro i
  exact (hP i).map_of_exact (extendScalars f)

end ModuleCat

namespace CommAlgCat

/-- **The functoriality map of [Stacks, Tag 08PN] on the cotangent complexes is the induced map
of the simplicial functoriality map.** Both `CommAlgCat.squareCotangentComplexMap` and
`AlgebraicTopology.extendMooreMap` of `CommAlgCat.squareCotangentSimplicialMap` are the Moore
complex of the simplicial map followed by the same two comparison isomorphisms. -/
theorem extendMooreMap_squareCotangentSimplicialMap {A A' : Type u} [CommRing A] [CommRing A']
    {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'} (sq : AlgebraSquare.{u, u, u} A A' B B') :
    AlgebraicTopology.extendMooreMap (ModuleCat.restrictScalars sq.map)
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) (squareCotangentSimplicialMap.{u, u, u} sq) =
      squareCotangentComplexMap.{u, u, u} sq :=
  rfl

end CommAlgCat

end
