module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Groupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidTranslate
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidTwist

/-!
# The source and the target of the finite part of a groupoid in algebraic spaces

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over `B` whose source and target
are separated and locally of finite type, and let `(U', Z_univ)` be the two structure spaces of
its finite part, recorded in `AlgebraicGeometry.Space.FinitePartUniversalOpen` (Stacks 04RU,
clauses (1) and (2)). Clause (3) of Stacks 04RU asserts that `Z_univ` carries source, target and
composition morphisms making `(U', Z_univ, s', t', c', e', i')` a groupoid in algebraic spaces
over `B`, together with a canonical morphism of groupoids to `(U, R, s, t, c, e, i)`.

On the functor of points a section of `Z_univ` over a test space `T` is a triple `(u, Z, z)`
where `u : T ⟶ U`, where `Z ⊂ R ×_{s, U, u} T` is an open and closed subspace finite over `T`
through which the unit section factors, and where `z : T ⟶ R` is a section of `R` with
`s ∘ z = u` which factors through `Z`. In those terms the source is `(u, Z, z) ↦ (u, Z)`, the map
to `R` of the morphism of groupoids is `(u, Z, z) ↦ z`, the target is
`(u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z))` and the composition is
`((u₁, Z₁, z₁), (u₂, Z₂, z₂)) ↦ (u₂, Z₂, c(z₁, z₂))`.

This file builds the first three of those four morphisms: the source `s'`, which is finite, the
map `Z_univ ⟶ R` on arrows, and the target `t'`, together with the two squares they form with
the source and the target of the given groupoid over the étale projection `g : U' ⟶ U`, and the
structure morphisms of `U'` and of `Z_univ` over `B`. The composition `c'` is not built, and
neither the groupoid nor the morphism of groupoids is assembled; see "What is not reached".

## Main definitions

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.arrows`: the arrow space `Z_univ` of the
  finite part, read as an algebraic space over `S`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.source`: the source morphism `s'`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.arrowMap`: the morphism `Z_univ ⟶ R` on
  arrows of the canonical morphism of groupoids.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.sourcePair` and
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.targetPair`: the pair `(u, Z)` over `Z_univ`
  obtained from the universal pair by base change along `s'`, and its twist
  `(t ∘ z, c(Z, i ∘ z))` by the tautological arrow, which is the value the target has to take.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.target`: the target morphism `t'`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.objectsToBase` and
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.arrowsToBase`: the structure morphisms of
  `U'` and of `Z_univ` to `B`.

## Main results

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.source_finite`: the source morphism `s'` is
  finite.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.arrowMap_comp_source` and
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.arrowMap_comp_target`: the two squares which
  say that `(g, arrowMap)` is compatible with the source and with the target, these being the
  source and target halves of the canonical morphism of groupoids of Stacks 04RU.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.targetPair_containsUnit`: the twisted pair
  contains the unit, which is what makes the target land in `U'` and not merely in the finite
  part of the source.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.source_over`,
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.target_over`,
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.arrowMap_over` and
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.objectProjection_over`: `s'`, `t'` and the two
  components of the morphism of groupoids are morphisms over `B`.
* `AlgebraicGeometry.Space.containsSection_restrict`: a pair over an algebraic space whose unit
  section factors through its open subspace restricts, at every section over a test scheme, to a
  pair with the same property.

## Implementation notes

Everything here is carried by the data of a `FinitePartUniversalOpen G`, so no hypothesis beyond
having such a structure is used: no separatedness, finite type or étaleness assumption appears,
those having been consumed already in producing the structure by
`AlgebraicGeometry.Space.finitePartUniversalOpen`. Of its fields, this file uses `unit`,
`unit_source`, `unit_identity`, `objects`, `objectProjection`, `objectsEquiv`,
`objectProjection_spec`, `universalOpen` with its `isOpen` and `finite_projection`, and
`universalOpen_base`; it uses neither `objectProjection_etale` nor `universalOpen_spec`,
`universalOpen_containsUnit` or `universalOpen_closed`.

`Z_univ` is an algebraic space because it is an open subspace of the fibre product
`R ×_{s, U, g} U'`, which is the first half of the `isOpen` field of the universal pair. The
field `universalOpen_base`, which says that the ambient fibre product of `Z_univ` is taken along
the projection `g`, is what makes the square with the source commute: it identifies the base of
the universal pair with `g`, after which that square is the cartesian square of the ambient
fibre product. For that reason the base of the universal pair, rather than `g`, is what is
written throughout, so that no ambient fibre product has to be transported along an equality of
morphisms; `arrowMap_comp_source'` is the source square in that form.

The target is built exactly as in Stacks 04RT. The pair `(u, Z)` over `Z_univ` is the base change
of the universal pair along `s'`: its open subspace is the preimage of the universal one under
`AlgebraicGeometry.Space.baseChangeAmbientMap`, open by
`AlgebraicGeometry.Space.isOpenSubspace_preimage` and finite over `Z_univ` because that preimage
square pasted onto the base-change square is cartesian, so
`AlgebraicGeometry.Space.isFinite_of_isPullback` applies. The twisted pair is the image of that
one under the isomorphism `c(-, i ∘ z)` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidTwist.lean`, transported
by `AlgebraicGeometry.Space.FiniteOpenSubspace.ofAmbientIso`, which is what carries openness and
finiteness across. That the twisted pair contains the unit is the computation
`c(e(t ∘ z), z) = z`: untwisting its unit section returns the tautological section `(1, z)` of
the ambient fibre product of the base-changed pair, which lies in the open subspace of that pair
because a section of `Z_univ` is by construction a section of the universal open subspace. The
target is then the morphism classifying the twisted pair under the universal property
`AlgebraicGeometry.Space.finiteOpenSubspaceEquiv`, lifted into the section-containing part of the
finite part presheaf — which is legitimate by `containsSection_restrict` — and read in `U'`
through `objectsEquiv`.

`AlgebraicGeometry.Space.finiteOpenSubspaceEquiv_toBase` and
`AlgebraicGeometry.Space.containsSection_restrict` restate for public use two facts which the
proof of Stacks 04RU clauses (1) and (2) establishes only privately; they are re-derived here
rather than imported, since the originals are `private`.

This development is split over two modules only because a single one does not compile within
Lean's default memory limit: the groupoid-level twisting isomorphism, which mentions nothing of
the finite part, is in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidTwist.lean`, and this
module is what uses it.

### What is not reached

The composition `c'` is **not** constructed, and therefore neither is the groupoid
`(U', Z_univ, s', t', c', e', i')` as an `AlgebraicGeometry.GroupoidInAlgebraicSpaces`, nor the
canonical morphism of groupoids of Stacks 04RU clause (3) as an
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom` — that notion does exist in this library, as
Stacks 043W part (2). What is missing for them is: the morphism `c'` on the fibre product
`Z_univ ×_{s', U', t'} Z_univ`, which on points is
`((u₁, Z₁, z₁), (u₂, Z₂, z₂)) ↦ (u₂, Z₂, c(z₁, z₂))` and whose construction needs the
identification of `Z₁` with `c(Z₂, i ∘ z₂)` supplied by the composability condition
`s' ∘ pr₁ = t' ∘ pr₂`; the unit `e'` and the inverse `i'`; and the verification of the groupoid
axioms at every test scheme, which the source of Stacks 04RT explicitly omits. Accordingly the
morphism of groupoids appears here only as its two component morphisms `g` and `arrowMap`
together with the two squares `arrowMap_comp_source` and `arrowMap_comp_target`.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04RQ](https://stacks.math.columbia.edu/tag/04RQ)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section Presheaf

variable {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-! ### The finite part presheaf, read on an algebraic space

Three facts about the universal property `AlgebraicGeometry.Space.finiteOpenSubspaceEquiv` of
the finite part presheaf which are needed to classify a pair by a morphism of algebraic spaces:
the base of the classified pair is the morphism to the base of the finite part presheaf, the
canonical morphism of ambient fibre products does not move the component in the source of the
given morphism, and a pair whose unit section factors through its open subspace restricts to
pairs over test schemes with the same property.
-/

/-- The base of the pair classified by a morphism to the finite part presheaf is that morphism
followed by the projection of the finite part presheaf to the base. -/
public theorem finiteOpenSubspaceEquiv_toBase
    {X Y T : AlgebraicGeometry.AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (v : T.obj ⟶ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).toFunctor) :
    ((finiteOpenSubspaceEquiv C S hS f T).1 v).toBase.hom =
      v ≫ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).baseMap := by
  ext V x
  have hs := (finiteOpenSubspaceEquiv C S hS f T).2 v V.unop (yonedaEquiv.symm x)
  have hb := congrArg yonedaEquiv hs.1
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at hb
  have hp := congrArg yonedaEquiv
    ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).baseMap_spec V.unop
      (v.app V x))
  exact hb.symm.trans (by simpa using hp.symm)

/-- A pair over an algebraic space whose unit section factors through its open subspace
restricts, at every section over a test scheme, to a pair with the same property. This is the
descent step which lets a morphism classifying such a pair be lifted into the
section-containing part of the finite part presheaf. -/
public theorem containsSection_restrict
    {X Y T : AlgebraicGeometry.AlgebraicSpaces C S hS} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (v : T.obj ⟶ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).toFunctor)
    (hv : AlgebraicGeometry.Space.ContainsSection C S hS f σ hσ
      ((finiteOpenSubspaceEquiv C S hS f T).1 v))
    (V : AlgebraicGeometry.BigFppfOver C S hS) (x : T.obj.obj (Opposite.op V)) :
    AlgebraicGeometry.Space.ContainsSection C S hS f σ hσ
      ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).sections V
        (v.app (Opposite.op V) x)) := by
  obtain ⟨σp, hσp⟩ := hv
  let g : AlgebraicGeometry.schemeSpace V ⟶ T :=
    ObjectProperty.homMk (yonedaEquiv.symm x)
  have hg : yonedaEquiv g.hom = x := Equiv.apply_symm_apply _ _
  have hspec := (finiteOpenSubspaceEquiv C S hS f T).2 v V g.hom
  rw [hg] at hspec
  obtain ⟨hbase, j, hpb, hjsnd⟩ := hspec
  have hσpfst : σp ≫ ((finiteOpenSubspaceEquiv C S hS f T).1 v).subspace.ι ≫
      pullback.fst ((finiteOpenSubspaceEquiv C S hS f T).1 v).toBase.hom f.hom = 𝟙 T.obj := by
    rw [← Category.assoc, hσp, pullback.lift_fst]
  have hσpsnd : σp ≫ ((finiteOpenSubspaceEquiv C S hS f T).1 v).subspace.ι ≫
      pullback.snd ((finiteOpenSubspaceEquiv C S hS f T).1 v).toBase.hom f.hom =
      ((finiteOpenSubspaceEquiv C S hS f T).1 v).toBase.hom ≫ σ.hom := by
    rw [← Category.assoc, hσp, pullback.lift_snd]
  refine ⟨hpb.lift (𝟙 (AlgebraicGeometry.schemeSpace V).obj)
    (g.hom ≫ σp) ?_, ?_⟩
  · rw [Category.id_comp, Category.assoc, hσpfst, Category.comp_id]
  · apply pullback.hom_ext
    · rw [Category.assoc, hpb.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, ← hjsnd, ← Category.assoc, hpb.lift_snd, Category.assoc, hσpsnd,
        pullback.lift_snd, ← Category.assoc]
      exact congrArg (fun k => k ≫ σ.hom) hbase.symm

end Presheaf

namespace FinitePartUniversalOpen

variable {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  {G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B}

/-- The arrow space `Z_univ` of the finite part of a groupoid in algebraic spaces, read as an
algebraic space over `S`: the universal finite open subspace of `R ×_{s, U, g} U'`, which is an
algebraic space because it is an open subspace. -/
public def arrows (F : FinitePartUniversalOpen G) :
    AlgebraicGeometry.AlgebraicSpaces C S hS :=
  ⟨F.universalOpen.subspace.toFunctor, F.universalOpen.isOpen.1⟩

/-- The source morphism `s' : Z_univ ⟶ U'` of the finite part: on points it sends a triple
`(u, Z, z)` to the pair `(u, Z)`, so it is the first projection of the ambient fibre product
`R ×_{s, U, g} U'` restricted to `Z_univ`. -/
public def source (F : FinitePartUniversalOpen G) : F.arrows ⟶ F.objects :=
  ObjectProperty.homMk
    (F.universalOpen.subspace.ι ≫ pullback.fst F.universalOpen.toBase.hom G.source.hom)

/-- The morphism `Z_univ ⟶ R` on arrows of the canonical morphism of groupoids: on points it
sends a triple `(u, Z, z)` to `z`, so it is the second projection of the ambient fibre product
`R ×_{s, U, g} U'` restricted to `Z_univ`. -/
public def arrowMap (F : FinitePartUniversalOpen G) : F.arrows ⟶ G.arrows :=
  ObjectProperty.homMk
    (F.universalOpen.subspace.ι ≫ pullback.snd F.universalOpen.toBase.hom G.source.hom)

/-- The source morphism of the finite part is finite: it is the projection to `U'` of the
universal finite open subspace. -/
public theorem source_finite (F : FinitePartUniversalOpen G) :
    AlgebraicGeometry.Space.IsFinite C S hS F.source.hom :=
  F.universalOpen.finite_projection

/-- **Stacks 04RU, part of clause (3).** The source morphism `s'` of the finite part and the
map `Z_univ ⟶ R` on arrows commute with the source `s` of the given groupoid and the étale
projection `g : U' ⟶ U`: on points both composites send `(u, Z, z)` to `u = s ∘ z`. This is the
square over the source of the canonical morphism of groupoids of Stacks 04RU. -/
public theorem arrowMap_comp_source (F : FinitePartUniversalOpen G) :
    F.arrowMap ≫ G.source = F.source ≫ F.objectProjection := by
  apply ObjectProperty.hom_ext
  have hbase : F.objectProjection.hom = F.universalOpen.toBase.hom :=
    congrArg (fun k : F.objects ⟶ G.objects => k.hom) F.universalOpen_base.symm
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom, hbase]
  show F.universalOpen.subspace.ι ≫
      pullback.snd F.universalOpen.toBase.hom G.source.hom ≫ G.source.hom =
    (F.universalOpen.subspace.ι ≫
      pullback.fst F.universalOpen.toBase.hom G.source.hom) ≫ F.universalOpen.toBase.hom
  rw [Category.assoc, pullback.condition]

/-- The source morphism composed with the base of the universal pair is the base of the given
groupoid's source along the tautological arrow. -/
public theorem arrowMap_comp_source' (F : FinitePartUniversalOpen G) :
    F.arrowMap ≫ G.source = F.source ≫ F.universalOpen.toBase :=
  F.arrowMap_comp_source.trans
    (congrArg (fun k : F.objects ⟶ G.objects => F.source ≫ k) F.universalOpen_base.symm)

/-- The pair over `Z_univ` obtained from the universal pair by base change along the source
morphism `s'`: on points it sends a triple `(u, Z, z)` to the pair `(u, Z)`, read over `Z_univ`
itself. This is the pair which the twisting isomorphism carries to the value of the target. -/
public def sourcePair (F : FinitePartUniversalOpen G) :
    AlgebraicGeometry.Space.FiniteOpenSubspace C S hS G.source F.arrows where
  toBase := F.source ≫ F.universalOpen.toBase
  subspace := F.universalOpen.subspace.preimage
    (AlgebraicGeometry.Space.baseChangeAmbientMap C S hS G.source F.universalOpen.toBase
      F.source)
  isOpen := AlgebraicGeometry.Space.isOpenSubspace_preimage C S hS _ _
    (AlgebraicGeometry.isAlgebraicSpace_pullback C S hS F.universalOpen.toBase.hom
      G.source.hom F.objects.property G.arrows.property G.objects.property)
    (AlgebraicGeometry.isAlgebraicSpace_pullback C S hS
      (F.source ≫ F.universalOpen.toBase).hom G.source.hom F.arrows.property
      G.arrows.property G.objects.property)
    F.universalOpen.isOpen
  finite_projection := AlgebraicGeometry.Space.isFinite_of_isPullback C S hS
    ((CategoryTheory.Subfunctor.isPullback_preimage _ _).paste_vert
      (AlgebraicGeometry.Space.isPullback_baseChangeAmbientMap C S hS G.source
        F.universalOpen.toBase F.source))
    F.universalOpen.finite_projection

/-- The base of the base-changed pair is the source morphism followed by the base of the
universal pair. -/
public theorem sourcePair_toBase (F : FinitePartUniversalOpen G) :
    F.sourcePair.toBase = F.source ≫ F.universalOpen.toBase := rfl

/-- **The pair `(t ∘ z, c(Z, i ∘ z))`** over `Z_univ`, which is the value that the target
morphism `t'` of the finite part has to classify: the base change of the universal pair along
the source, twisted by the tautological arrow `z : Z_univ ⟶ R`. -/
public def targetPair (F : FinitePartUniversalOpen G) :
    AlgebraicGeometry.Space.FiniteOpenSubspace C S hS G.source F.arrows :=
  AlgebraicGeometry.Space.FiniteOpenSubspace.ofAmbientIso C S hS F.sourcePair
    (F.arrowMap ≫ G.target)
    (twistIso G F.arrowMap (F.source ≫ F.universalOpen.toBase) (F.arrowMap ≫ G.target)
      F.arrowMap_comp_source' rfl)
    (twistIso_hom_fst G F.arrowMap (F.source ≫ F.universalOpen.toBase)
      (F.arrowMap ≫ G.target) F.arrowMap_comp_source' rfl)

/-- The base of the target pair is `t ∘ z`, the target of the given groupoid along the
tautological arrow. -/
public theorem targetPair_toBase (F : FinitePartUniversalOpen G) :
    F.targetPair.toBase = F.arrowMap ≫ G.target := rfl

/-- The tautological section of the ambient fibre product of the base-changed pair: on points
it sends a triple `(u, Z, z)` to the section `((u, Z, z), z)`. -/
public def tautologicalSection (F : FinitePartUniversalOpen G) :
    F.arrows.obj ⟶ pullback (F.source ≫ F.universalOpen.toBase).hom G.source.hom :=
  pullback.lift (𝟙 F.arrows.obj) F.arrowMap.hom (by
    rw [Category.id_comp]
    exact (congrArg (fun k : F.arrows ⟶ G.objects => k.hom) F.arrowMap_comp_source').symm)

/-- The tautological section is a section over `Z_univ`. -/
public theorem tautologicalSection_fst (F : FinitePartUniversalOpen G) :
    F.tautologicalSection ≫
        pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom =
      𝟙 F.arrows.obj :=
  pullback.lift_fst _ _ _

/-- The arrow component of the tautological section is the tautological arrow. -/
public theorem tautologicalSection_snd (F : FinitePartUniversalOpen G) :
    F.tautologicalSection ≫
        pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom =
      F.arrowMap.hom :=
  pullback.lift_snd _ _ _

/-- The tautological section is the inclusion of `Z_univ` into the ambient fibre product of
the universal pair, read after base change along the source. -/
public theorem tautologicalSection_comp_baseChangeAmbientMap (F : FinitePartUniversalOpen G) :
    F.tautologicalSection ≫ AlgebraicGeometry.Space.baseChangeAmbientMap C S hS G.source
        F.universalOpen.toBase F.source =
      F.universalOpen.subspace.ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, (AlgebraicGeometry.Space.isPullback_baseChangeAmbientMap C S hS
      G.source F.universalOpen.toBase F.source).w, ← Category.assoc,
      F.tautologicalSection_fst, Category.id_comp]
    rfl
  · rw [Category.assoc, baseChangeAmbientMap_comp_snd, F.tautologicalSection_snd]
    rfl

/-- The tautological section factors through the open subspace of the base-changed pair: this
is the statement that the arrow `z` of a triple `(u, Z, z)` lies in `Z`. -/
public theorem tautologicalSection_mem (F : FinitePartUniversalOpen G)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (y : F.arrows.obj.obj V) :
    F.tautologicalSection.app V y ∈ F.sourcePair.subspace.obj V := by
  show (AlgebraicGeometry.Space.baseChangeAmbientMap C S hS G.source
    F.universalOpen.toBase F.source).app V (F.tautologicalSection.app V y) ∈
      F.universalOpen.subspace.obj V
  rw [show (AlgebraicGeometry.Space.baseChangeAmbientMap C S hS G.source
      F.universalOpen.toBase F.source).app V (F.tautologicalSection.app V y) =
      F.universalOpen.subspace.ι.app V y from
      congrArg (fun k => k.app V y) F.tautologicalSection_comp_baseChangeAmbientMap]
  exact y.property

/-- The unit section of the ambient fibre product of the target pair: on points it sends a
triple `(u, Z, z)` to the section `((u, Z, z), e(t ∘ z))`, which is the section whose
factorization through the open subspace of the target pair is required of a pair in the finite
part containing the unit. -/
public def targetUnitSection (F : FinitePartUniversalOpen G) :
    F.arrows.obj ⟶ pullback (F.arrowMap ≫ G.target).hom G.source.hom :=
  pullback.lift (𝟙 F.arrows.obj) ((F.arrowMap ≫ G.target).hom ≫ F.unit.hom) (by
    simp only [Category.id_comp, Category.assoc, F.unit_source, Category.comp_id])

/-- The unit section of the target pair is a section over `Z_univ`. -/
private theorem targetUnitSection_fst (F : FinitePartUniversalOpen G) :
    F.targetUnitSection ≫ pullback.fst (F.arrowMap ≫ G.target).hom G.source.hom =
      𝟙 F.arrows.obj :=
  pullback.lift_fst _ _ _

/-- The arrow component of the unit section is the unit at `t ∘ z`. -/
private theorem targetUnitSection_snd (F : FinitePartUniversalOpen G) :
    F.targetUnitSection ≫ pullback.snd (F.arrowMap ≫ G.target).hom G.source.hom =
      (F.arrowMap ≫ G.target).hom ≫ F.unit.hom :=
  pullback.lift_snd _ _ _

/-- Untwisting the unit section of the target pair gives back the tautological section: on
points this is the identity `c(e(t ∘ z), z) = z`. -/
public theorem targetUnitSection_comp_untwistMap (F : FinitePartUniversalOpen G) :
    F.targetUnitSection ≫ untwistMap G F.arrowMap (F.source ≫ F.universalOpen.toBase)
        (F.arrowMap ≫ G.target) F.arrowMap_comp_source' rfl =
      F.tautologicalSection := by
  apply pullback.hom_ext
  · rw [Category.assoc, untwistMap_fst, F.tautologicalSection_fst, F.targetUnitSection_fst]
  · rw [Category.assoc, untwistMap_snd, F.tautologicalSection_snd]
    ext V y
    have hfstU := congrArg (fun k => k.app V y) F.targetUnitSection_fst
    have hsndU : (pullback.snd (F.arrowMap ≫ G.target).hom G.source.hom).app V
        (F.targetUnitSection.app V y) =
        G.toGroupoidInFunctors.identity V (G.target.hom.app V (F.arrowMap.hom.app V y)) :=
      (congrArg (fun k => k.app V y) F.targetUnitSection_snd).trans (F.unit_identity V _)
    have hfstUp : (pullback.fst G.source.hom G.target.hom).app V
        ((untwistPair G F.arrowMap (F.arrowMap ≫ G.target) rfl).app V
          (F.targetUnitSection.app V y)) =
        G.toGroupoidInFunctors.identity V (G.target.hom.app V (F.arrowMap.hom.app V y)) :=
      (congrArg (fun k => k.app V (F.targetUnitSection.app V y))
        (untwistPair_fst G F.arrowMap (F.arrowMap ≫ G.target) rfl)).trans hsndU
    have hsndUp : (pullback.snd G.source.hom G.target.hom).app V
        ((untwistPair G F.arrowMap (F.arrowMap ≫ G.target) rfl).app V
          (F.targetUnitSection.app V y)) = F.arrowMap.hom.app V y :=
      (congrArg (fun k => k.app V (F.targetUnitSection.app V y))
        (untwistPair_snd G F.arrowMap (F.arrowMap ≫ G.target) rfl)).trans
        (congrArg (fun q => F.arrowMap.hom.app V q) hfstU)
    have hcondUp := pullback_condition_app G.source.hom G.target.hom V
      ((untwistPair G F.arrowMap (F.arrowMap ≫ G.target) rfl).app V
        (F.targetUnitSection.app V y))
    have hid : G.source.hom.app V (G.toGroupoidInFunctors.identity V
        (G.target.hom.app V (F.arrowMap.hom.app V y))) =
        G.target.hom.app V (F.arrowMap.hom.app V y) := by
      rwa [← hfstUp, ← hsndUp]
    show G.comp.hom.app V
        ((untwistPair G F.arrowMap (F.arrowMap ≫ G.target) rfl).app V
          (F.targetUnitSection.app V y)) = F.arrowMap.hom.app V y
    exact ((comp_hom_app G V _ hcondUp).trans
      (compose_congr G V _ _ _ _ hcondUp hid hfstUp hsndUp)).trans
      (compose_identity_app G V _ hid)

/-- **The target pair contains the unit.** The unit section of the ambient fibre product of the
target pair factors through its open subspace, because untwisting carries it to the
tautological section, which lies in the open subspace of the base-changed pair. -/
public theorem targetPair_containsUnit (F : FinitePartUniversalOpen G) :
    AlgebraicGeometry.Space.ContainsSection C S hS G.source F.unit F.unit_source
      F.targetPair := by
  refine ⟨Subfunctor.lift F.targetUnitSection ?_, Subfunctor.lift_ι _ _⟩
  intro V y hy
  obtain ⟨y, rfl⟩ := hy
  show (untwistMap G F.arrowMap (F.source ≫ F.universalOpen.toBase)
      (F.arrowMap ≫ G.target) F.arrowMap_comp_source' rfl).app V
      (F.targetUnitSection.app V y) ∈ F.sourcePair.subspace.obj V
  rw [show (untwistMap G F.arrowMap (F.source ≫ F.universalOpen.toBase)
      (F.arrowMap ≫ G.target) F.arrowMap_comp_source' rfl).app V
      (F.targetUnitSection.app V y) = F.tautologicalSection.app V y from
    congrArg (fun k => k.app V y) F.targetUnitSection_comp_untwistMap]
  exact F.tautologicalSection_mem V y

/-- The morphism to the finite part presheaf classifying the target pair. -/
public def targetClassify (F : FinitePartUniversalOpen G) :
    F.arrows.obj ⟶
      (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).toFunctor :=
  (finiteOpenSubspaceEquiv C S hS G.source F.arrows).1.symm F.targetPair

/-- The classifying morphism of the target pair has range in the section-containing part of
the finite part presheaf, since the target pair contains the unit. -/
public theorem targetClassify_range (F : FinitePartUniversalOpen G) :
    Subfunctor.range F.targetClassify ≤
      (finitePartWithSection C S hS G.source F.unit F.unit_source).toSubfunctor := by
  intro V y hy
  obtain ⟨y, rfl⟩ := hy
  refine ((finitePartWithSection C S hS G.source F.unit F.unit_source).mem_iff V.unop _).2 ?_
  refine containsSection_restrict G.source F.unit F.unit_source F.targetClassify ?_ V.unop y
  rw [show (finiteOpenSubspaceEquiv C S hS G.source F.arrows).1 F.targetClassify =
    F.targetPair from Equiv.apply_symm_apply _ _]
  exact F.targetPair_containsUnit

/-- **Stacks 04RU, part of clause (3).** The target morphism `t' : Z_univ ⟶ U'` of the finite
part: on points it sends a triple `(u, Z, z)` to the pair `(t ∘ z, c(Z, i ∘ z))`, which is a
point of `U'` because it contains the unit. -/
public def target (F : FinitePartUniversalOpen G) : F.arrows ⟶ F.objects :=
  ObjectProperty.homMk
    (Subfunctor.lift F.targetClassify F.targetClassify_range ≫ F.objectsEquiv.inv)

/-- **Stacks 04RU, part of clause (3).** The target morphism `t'` of the finite part and the
map `Z_univ ⟶ R` on arrows commute with the target `t` of the given groupoid and the étale
projection `g : U' ⟶ U`: on points both composites send `(u, Z, z)` to `t ∘ z`. This is the
square over the target of the canonical morphism of groupoids of Stacks 04RU. -/
public theorem arrowMap_comp_target (F : FinitePartUniversalOpen G) :
    F.arrowMap ≫ G.target = F.target ≫ F.objectProjection := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    F.objectProjection_spec]
  show F.arrowMap.hom ≫ G.target.hom =
    (Subfunctor.lift F.targetClassify F.targetClassify_range ≫ F.objectsEquiv.inv) ≫
      F.objectsEquiv.hom ≫
      (finitePartWithSection C S hS G.source F.unit F.unit_source).toSubfunctor.ι ≫
      (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).baseMap
  rw [Category.assoc, ← Category.assoc F.objectsEquiv.inv, Iso.inv_hom_id, Category.id_comp,
    ← Category.assoc, Subfunctor.lift_ι,
    ← finiteOpenSubspaceEquiv_toBase G.source F.targetClassify,
    show (finiteOpenSubspaceEquiv C S hS G.source F.arrows).1 F.targetClassify =
      F.targetPair from Equiv.apply_symm_apply _ _]
  rfl

/-- The structure morphism of the object space `U'` of the finite part to the base `B`: the
projection `g : U' ⟶ U` followed by the structure morphism of `U`. -/
public def objectsToBase (F : FinitePartUniversalOpen G) : F.objects ⟶ B :=
  F.objectProjection ≫ G.objectsToBase

/-- The structure morphism of the arrow space `Z_univ` of the finite part to the base `B`: the
map `Z_univ ⟶ R` followed by the structure morphism of `R`. -/
public def arrowsToBase (F : FinitePartUniversalOpen G) : F.arrows ⟶ B :=
  F.arrowMap ≫ G.arrowsToBase

/-- A morphism `Z_univ ⟶ U'` lying over a morphism `m : R ⟶ U` of the given groupoid, via the
tautological arrow, is a morphism over the base `B` once `m` is. -/
private theorem comp_objectsToBase_of_arrowMap_comp (F : FinitePartUniversalOpen G)
    (k : F.arrows ⟶ F.objects) (m : G.arrows ⟶ G.objects)
    (hm : m ≫ G.objectsToBase = G.arrowsToBase)
    (h : F.arrowMap ≫ m = k ≫ F.objectProjection) : k ≫ F.objectsToBase = F.arrowsToBase := by
  rw [objectsToBase, ← Category.assoc, ← h, Category.assoc, hm, arrowsToBase]

/-- The source morphism of the finite part is a morphism over the base `B`. -/
public theorem source_over (F : FinitePartUniversalOpen G) :
    F.source ≫ F.objectsToBase = F.arrowsToBase :=
  comp_objectsToBase_of_arrowMap_comp F _ _ G.source_over F.arrowMap_comp_source

/-- The target morphism of the finite part is a morphism over the base `B`. -/
public theorem target_over (F : FinitePartUniversalOpen G) :
    F.target ≫ F.objectsToBase = F.arrowsToBase :=
  comp_objectsToBase_of_arrowMap_comp F _ _ G.target_over F.arrowMap_comp_target

/-- The map `Z_univ ⟶ R` on arrows is a morphism over the base `B`, by the very definition of
the structure morphism of `Z_univ`. -/
public theorem arrowMap_over (F : FinitePartUniversalOpen G) :
    F.arrowMap ≫ G.arrowsToBase = F.arrowsToBase := rfl

/-- The projection `g : U' ⟶ U` is a morphism over the base `B`, by the very definition of the
structure morphism of `U'`. -/
public theorem objectProjection_over (F : FinitePartUniversalOpen G) :
    F.objectProjection ≫ G.objectsToBase = F.objectsToBase := rfl

end FinitePartUniversalOpen

end AlgebraicGeometry.Space

end
