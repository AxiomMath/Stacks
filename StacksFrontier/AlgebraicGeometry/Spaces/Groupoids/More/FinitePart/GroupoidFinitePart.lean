module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.FppfSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.WithSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.PointwiseComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage

/-!
# The finite part of a groupoid in algebraic spaces

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over an algebraic space `B` whose
source morphism `s` is separated and locally of finite type. Writing `R_s` for `R` regarded as a
space over `U` through `s`, the unit `e` is a section of `s`, so the finite part of `s`
containing that section is available: it is the algebraic space

`U' = (R_s/U, e)_fin`,

an open subspace of the finite part `(R_s/U)_fin` of `s`, carrying an étale morphism
`g : U' ⟶ U`. The pair which `U'` names under Stacks 04PE, part (2), is `(g, Z_univ)`, where
`Z_univ` is an open subspace of `U' ×_{g, U, s} R`, finite over `U'`, closed because `s` is
separated, and containing the base change of the unit. This is the construction of the object
space and arrow space of the finite part of the groupoid, which is the content of Stacks 04RT
before the five structure morphisms are written down.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityHom`: the unit `e : U ⟶ R` of a groupoid
  in algebraic spaces, as a morphism of algebraic spaces.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart`: the data `(U', g, Z_univ)` of the
  finite part of a groupoid in algebraic spaces, with the properties the construction supplies.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.finitePart`: **Stacks 04RT**, the construction of
  that data from a groupoid whose source morphism is separated and locally of finite type.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.sourceHom`: the source morphism
  `s' : Z_univ ⟶ U'` of the finite part, the rule `(u, Z, z) ↦ (u, Z)`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.arrowHom`: the morphism
  `Z_univ ⟶ R` on arrows of the canonical morphism of groupoids, the rule `(u, Z, z) ↦ z`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityHom_comp_source`: the unit is a section of
  the source morphism, which is what lets the finite part containing a section be formed for `s`.
* `AlgebraicGeometry.Space.toBase_finiteOpenSubspaceEquiv`: the pair named by a morphism from an
  algebraic space into the finite part has, as its morphism to the base, the composite of that
  morphism with the projection of the finite part.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.FinitePart.sourceHom_comp_toBase`: the source
  morphism of the finite part lies over the source morphism of the groupoid.

## Implementation notes

`AlgebraicGeometry.GroupoidInAlgebraicSpaces` does not carry the unit and the inverse as fields;
they are determined by the source, target and composition, which is Stacks 06K5. The unit is
therefore built here as a morphism of algebraic spaces, with the pointwise identity arrow of
`Deformation.GroupoidInFunctors` as its components and
`Deformation.GroupoidInFunctors.map_identity` as its naturality. Nothing is chosen: the
construction is the components written out, so `identityHom` is a definition with a body rather
than a witness extracted from the uniqueness assertion of Stacks 06K5.

`U'` is recorded as an abstract algebraic space together with the inclusion into `(R_s/U)_fin`
and the equality of the range of that inclusion with the subfunctor of Stacks 04RR. That
equality is what makes `U'` the finite part *containing the unit* rather than some open subspace
of the finite part, and it is what a consumer needs in order to read a section of `U'` as a pair
whose open subspace contains the unit.

`Z_univ` is presented as the open subspace of the pair of Stacks 04PC which `U'` names, rather
than as independently chosen data. In the source the ambient fibre product is written
`R ×_{s, U, g} U'`; here it is `U' ×_{g, U, s} R`, the fibre product in the other order, because
that is the ambient space of a pair of Stacks 04PC with test space `U'`. The two differ by the
symmetry of the fibre product and nothing is lost.

Containment of the base change of the unit is `AlgebraicGeometry.Space.ContainsSection`, an
actual factorization through the inclusion of `Z_univ`; it is derived from the pointwise
containment carried by membership in the subfunctor of Stacks 04RR, by transporting a
scheme-valued factorization along the cartesian square that Stacks 04PE, part (2), supplies.

Of the five structure morphisms `s', t', c', e', i'` on `(U', Z_univ)`, only the source `s'` is
available as a projection of the pair, and it is named here together with the morphism on arrows
of the canonical morphism of groupoids; the object map of that canonical morphism is the pair's
own morphism to the base, `FinitePart.pair.toBase`. The remaining three structure morphisms and
the groupoid laws they satisfy are not constructed here, and so neither is the canonical morphism
of groupoids of Stacks 04RU.

## References

* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04PH](https://stacks.math.columbia.edu/tag/04PH)
* [Stacks Project, Tag 04QH](https://stacks.math.columbia.edu/tag/04QH)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) AlgebraicGeometry.Space.hasPullbacks_presheaf_groupoidFinitePart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) AlgebraicGeometry.Space.hasPullback_presheaf_groupoidFinitePart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (AlgebraicGeometry.Space.hasPullbacks_presheaf_groupoidFinitePart B S hS).has_limit _

namespace AlgebraicGeometry.Space

/-- The pair of Stacks 04PC named by a morphism from an algebraic space `T` into the finite part
of `f : X ⟶ Y` has, as its morphism `T ⟶ Y`, the composite of that morphism with the projection
of the finite part to `Y`. -/
theorem toBase_finiteOpenSubspaceEquiv (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : AlgebraicSpaces B S hS)
    (v : T.obj ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor) :
    ((finiteOpenSubspaceEquiv B S hS f T).1 v).toBase.hom =
      v ≫ (finiteOpenSubspacePresheaf B S hS f).baseMap := by
  let P := finiteOpenSubspacePresheaf B S hS f
  let p := (finiteOpenSubspaceEquiv B S hS f T).1 v
  ext U x
  let g : yoneda.obj U.unop ⟶ T.obj := yonedaEquiv.symm x
  have hx : yonedaEquiv g = x := Equiv.apply_symm_apply _ _
  have hspec := ((finiteOpenSubspaceEquiv B S hS f T).2 v U.unop g).1
  rw [hx] at hspec
  calc
    _ = p.toBase.hom.app U (yonedaEquiv g) := congrArg _ hx.symm
    _ = yonedaEquiv (g ≫ p.toBase.hom) := (yonedaEquiv_comp g p.toBase.hom).symm
    _ = yonedaEquiv (P.sections U.unop (v.app U x)).toBase.hom :=
        congrArg yonedaEquiv hspec.symm
    _ = yonedaEquiv (yonedaEquiv.symm (P.baseMap.app U (v.app U x))) :=
        congrArg yonedaEquiv (P.baseMap_spec U.unop (v.app U x)).symm
    _ = P.baseMap.app U (v.app U x) := Equiv.apply_symm_apply _ _

/-- A pair of Stacks 04PC over an algebraic space `T` contains the section induced by `σ` as
soon as every pair it base changes to over a scheme of the site does.

The hypotheses are the data that Stacks 04PE, part (2), supplies for the morphism
`T ⟶ (X/Y)_fin` naming the pair: for each scheme `V` of the site and each morphism `V ⟶ T`, the
pair over `V` that the composite names, its morphism to `Y` as the composite with the morphism
of the pair over `T`, and the cartesian square identifying its open subspace with the base
change. The factorization of the section over `V` is transported along that square, and the
resulting pointwise membership assembles into a factorization over `T`. -/
theorem containsSection_of_pointwise (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj) (T : AlgebraicSpaces B S hS)
    (p : FiniteOpenSubspace B S hS f T)
    (q : ∀ V : BigFppfOver B S hS, ((schemeSpace V).obj ⟶ T.obj) →
      FiniteOpenSubspace B S hS f (schemeSpace V))
    (hbase : ∀ V g, (q V g).toBase.hom = g ≫ p.toBase.hom)
    (hsquare : ∀ V g, ∃ j : (q V g).subspace.toFunctor ⟶ p.subspace.toFunctor,
      IsPullback ((q V g).subspace.ι ≫ pullback.fst (q V g).toBase.hom f.hom) j g
          (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom) ∧
        j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
          (q V g).subspace.ι ≫ pullback.snd (q V g).toBase.hom f.hom)
    (hq : ∀ V g, ContainsSection B S hS f σ hσ (q V g)) :
    ContainsSection B S hS f σ hσ p := by
  classical
  let s := pullback.lift (f := p.toBase.hom) (g := f.hom) (𝟙 T.obj)
    (p.toBase.hom ≫ σ.hom) (by simp [hσ])
  have hsfst : s ≫ pullback.fst p.toBase.hom f.hom = 𝟙 T.obj := pullback.lift_fst _ _ _
  have hssnd : s ≫ pullback.snd p.toBase.hom f.hom = p.toBase.hom ≫ σ.hom :=
    pullback.lift_snd _ _ _
  have hle : Subfunctor.range s ≤ p.subspace := by
    intro V y hy
    obtain ⟨z, rfl⟩ := hy
    let g : (schemeSpace V.unop).obj ⟶ T.obj := yonedaEquiv.symm z
    have hz : yonedaEquiv g = z := Equiv.apply_symm_apply _ _
    obtain ⟨j, hpbsq, hjsnd⟩ := hsquare V.unop g
    obtain ⟨l, hl⟩ := hq V.unop g
    have hlfst : l ≫ (q V.unop g).subspace.ι ≫
        pullback.fst (q V.unop g).toBase.hom f.hom =
        𝟙 (schemeSpace V.unop).obj := by
      rw [← Category.assoc, hl, pullback.lift_fst]
    have hlsnd : l ≫ (q V.unop g).subspace.ι ≫
        pullback.snd (q V.unop g).toBase.hom f.hom =
        (q V.unop g).toBase.hom ≫ σ.hom := by
      rw [← Category.assoc, hl, pullback.lift_snd]
    have hfst : (l ≫ j) ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom = g := by
      rw [Category.assoc, ← hpbsq.w, ← Category.assoc, hlfst, Category.id_comp]
    have hsnd : (l ≫ j) ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
        g ≫ p.toBase.hom ≫ σ.hom := by
      rw [Category.assoc, hjsnd, hlsnd, hbase V.unop g, Category.assoc]
    have hm : (l ≫ j) ≫ p.subspace.ι = g ≫ s := by
      apply pullback.hom_ext
      · rw [Category.assoc, hfst, Category.assoc, hsfst, Category.comp_id]
      · rw [Category.assoc, hsnd, Category.assoc, hssnd]
    have hgoal : s.app V z = yonedaEquiv (g ≫ s) := by rw [yonedaEquiv_comp, hz]
    rw [hgoal.trans (congrArg yonedaEquiv hm).symm]
    exact (yonedaEquiv (l ≫ j)).2
  exact ⟨Subfunctor.lift s hle, Subfunctor.lift_ι s hle⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The unit of a groupoid in algebraic spaces: the morphism `e : U ⟶ R` from the object space
to the arrow space whose value at a point of a test scheme is the identity arrow there.

A groupoid in algebraic spaces does not carry its unit as data; the unit is determined by the
source, target and composition, which is Stacks 06K5. Its components are the pointwise identity
arrows of the underlying groupoid in presheaves, and these are natural. -/
noncomputable def identityHom (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.objects ⟶ G.arrows :=
  ObjectProperty.homMk
    { app := fun T => ↾ fun x => G.toGroupoidInFunctors.identity T x
      naturality := by
        intro T T' f
        ext x
        exact (Deformation.GroupoidInFunctors.map_identity
          G.toGroupoidInFunctors f x).symm }

/-- The component of the unit `identityHom G` at a test scheme `T` sends a point `x` of the
object space to the identity arrow at `x`. -/
@[simp]
theorem identityHom_hom_app (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : G.objects.obj.obj T) :
    (identityHom G).hom.app T x = G.toGroupoidInFunctors.identity T x := rfl

/-- The unit is a section of the source morphism of the groupoid: the identity arrow at a point
has that point as its source. -/
theorem identityHom_comp_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    (identityHom G).hom ≫ G.source.hom = 𝟙 G.objects.obj := by
  ext T x
  let : Groupoid (G.objects.obj.obj T) := G.toGroupoidInFunctors.evaluationGroupoid T
  exact (G.toGroupoidInFunctors.evaluationArrowEquiv T x x (𝟙 x)).2.1

/-- The unit is a section of the target morphism of the groupoid: the identity arrow at a point
has that point as its target. -/
theorem identityHom_comp_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    (identityHom G).hom ≫ G.target.hom = 𝟙 G.objects.obj := by
  ext T x
  let : Groupoid (G.objects.obj.obj T) := G.toGroupoidInFunctors.evaluationGroupoid T
  exact (G.toGroupoidInFunctors.evaluationArrowEquiv T x x (𝟙 x)).2.2

/-- The data produced by the construction of **Stacks 04RT**: the object space `U'` of the finite
part of a groupoid in algebraic spaces, its étale morphism `g` to the object space of the
groupoid, and the universal open subspace `Z_univ` which is its arrow space.

`U'` is the finite part of the source morphism containing the unit, `(R_s/U, e)_fin`, presented
as an abstract algebraic space with an open immersion into the finite part `(R_s/U)_fin` whose
range is the subfunctor of Stacks 04RR. The morphism `g` and the subspace `Z_univ` together form
the pair of Stacks 04PC which that open immersion names under Stacks 04PE, part (2). -/
structure FinitePart (G : GroupoidInAlgebraicSpaces C S hS B) where
  /-- The object space `U' = (R_s/U, e)_fin` of the finite part of the groupoid. -/
  objects : AlgebraicSpaces C S hS
  /-- The inclusion of `U'` into the finite part `(R_s/U)_fin` of the source morphism. -/
  inclusion : objects.obj ⟶
    (Space.finiteOpenSubspacePresheaf C S hS G.source).toFunctor
  /-- The inclusion identifies `U'` with the pairs whose open subspace contains the unit, so
  that `U'` is `(R_s/U, e)_fin` and not merely some open subspace of `(R_s/U)_fin`. -/
  range_inclusion : Subfunctor.range inclusion =
    (Space.finitePartWithSection C S hS G.source (identityHom G)
      (identityHom_comp_source G)).toSubfunctor
  /-- `U'` is an open subspace of `(R_s/U)_fin`. -/
  isOpenImmersion_inclusion : Space.IsOpenImmersion C S hS inclusion
  /-- The pair `(g, Z_univ)`: the morphism `g : U' ⟶ U` together with the open subspace
  `Z_univ` of `U' ×_{g, U, s} R`, finite over `U'`. -/
  pair : Space.FiniteOpenSubspace C S hS G.source objects
  /-- The pair is the one the inclusion names under Stacks 04PE, part (2); this is what makes
  `Z_univ` universal. -/
  pair_eq : pair =
    (Space.finiteOpenSubspaceEquiv C S hS G.source objects).1 inclusion
  /-- `g` is the projection of `(R_s/U)_fin` to `U` restricted to `U'`. -/
  toBase_pair : pair.toBase.hom =
    inclusion ≫ (Space.finiteOpenSubspacePresheaf C S hS G.source).baseMap
  /-- The morphism `g : U' ⟶ U` is étale. -/
  isEtale_toBase : Space.IsEtale C S hS pair.toBase.hom
  /-- `Z_univ` is closed in `U' ×_{g, U, s} R` as well as open, because `s` is separated. -/
  isClosed_subspace : Space.IsClosedSubspace C S hS pair.subspace
  /-- The base change of the unit along `g` factors through `Z_univ`. -/
  containsUnit : Space.ContainsSection C S hS G.source (identityHom G)
    (identityHom_comp_source G) pair

/-- **Stacks 04RT.** The finite part of a groupoid in algebraic spaces whose source morphism is
separated and locally of finite type.

Its object space is `U' = (R_s/U, e)_fin`, the finite part of the source morphism containing the
unit: an algebraic space by Stacks 04QH and Stacks 04RR, part (3), and an open subspace of
`(R_s/U)_fin`. Its morphism `g : U' ⟶ U` is the projection of `(R_s/U)_fin` restricted to `U'`,
and is étale because that projection is étale by Stacks 04QH and the inclusion of an open
subspace is étale. Its arrow space is the open subspace `Z_univ` of `U' ×_{g, U, s} R` belonging
to the pair which the inclusion names under Stacks 04PE, part (2); it is finite over `U'` by
construction, closed by Stacks 04PH, and contains the base change of the unit because every
pair named by a section of `U'` does.

The structure morphisms `t', e', i', c'`, the groupoid they form and its canonical morphism to the
given groupoid are built from this in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidStructure.lean`;
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.finitePartGroupoid_spec` records the whole of Stacks
04RT. -/
noncomputable def finitePart (G : GroupoidInAlgebraicSpaces C S hS B)
    (hsep : Space.IsSeparated C S hS G.source.hom)
    (hft : Space.IsLocallyOfFiniteType C S hS G.source.hom) :
    FinitePart G := by
  classical
  let hu := identityHom_comp_source G
  let P := Space.finiteOpenSubspacePresheaf C S hS G.source
  have hP : IsAlgebraicSpace C S hS P.toFunctor :=
    Space.isAlgebraicSpace_finiteOpenSubspacePresheaf C S hS G.source hsep hft
  let W := Space.finitePartWithSection C S hS G.source (identityHom G) hu
  have hW : Space.IsOpenSubspace C S hS W.toSubfunctor :=
    Space.isOpenSubspace_finitePartWithSection C S hS G.source (identityHom G) hu hP
  let U' : AlgebraicSpaces C S hS := ⟨W.toSubfunctor.toFunctor, hW.1⟩
  let incl : U'.obj ⟶ P.toFunctor := W.toSubfunctor.ι
  let p := (Space.finiteOpenSubspaceEquiv C S hS G.source U').1 incl
  have htoBase : p.toBase.hom = incl ≫ P.baseMap :=
    Space.toBase_finiteOpenSubspaceEquiv C S hS G.source U' incl
  -- The base change of the unit factors through the universal open subspace.
  have hcontains : Space.ContainsSection C S hS G.source (identityHom G) hu p :=
    Space.containsSection_of_pointwise C S hS G.source (identityHom G) hu U' p
      (fun V g => P.sections V (incl.app (op V) (yonedaEquiv g)))
      (fun V g => ((Space.finiteOpenSubspaceEquiv C S hS G.source U').2 incl V g).1)
      (fun V g => ((Space.finiteOpenSubspaceEquiv C S hS G.source U').2 incl V g).2)
      (fun V g => (W.mem_iff V (incl.app (op V) (yonedaEquiv g))).1 (yonedaEquiv g).2)
  exact
    { objects := U'
      inclusion := incl
      range_inclusion := Subfunctor.range_ι W.toSubfunctor
      isOpenImmersion_inclusion := hW.2
      pair := p
      pair_eq := rfl
      toBase_pair := htoBase
      isEtale_toBase := by
        rw [htoBase]
        exact Space.isEtale_comp C S hS (Space.isEtale_ι_of_isOpenSubspace hW)
          (Space.isEtale_baseMap_finiteOpenSubspacePresheaf C S hS G.source hsep hft)
      isClosed_subspace :=
        Space.FiniteOpenSubspace.isClosedSubspace C S hS G.source U' p hsep
      containsUnit := hcontains }

namespace FinitePart

variable {G : GroupoidInAlgebraicSpaces C S hS B}

/-- The source morphism `s' : Z_univ ⟶ U'` of the finite part: the rule `(u, Z, z) ↦ (u, Z)`,
read as the inclusion of `Z_univ` into `U' ×_{g, U, s} R` followed by the projection to `U'`. -/
noncomputable def sourceHom (fp : FinitePart G) :
    fp.pair.subspace.toFunctor ⟶ fp.objects.obj :=
  fp.pair.subspace.ι ≫ pullback.fst fp.pair.toBase.hom G.source.hom

/-- The morphism `Z_univ ⟶ R` on arrows of the canonical morphism of groupoids: the rule
`(u, Z, z) ↦ z`, read as the inclusion of `Z_univ` into `U' ×_{g, U, s} R` followed by the
projection to `R`. -/
noncomputable def arrowHom (fp : FinitePart G) :
    fp.pair.subspace.toFunctor ⟶ G.arrows.obj :=
  fp.pair.subspace.ι ≫ pullback.snd fp.pair.toBase.hom G.source.hom

/-- The source morphism of the finite part lies over the source morphism of the groupoid: the
object `(u, Z)` of `U'` which `(u, Z, z)` is sent to has `u` as its morphism to `U`, and `u` is
the source of `z`. -/
theorem sourceHom_comp_toBase (fp : FinitePart G) :
    fp.sourceHom ≫ fp.pair.toBase.hom = fp.arrowHom ≫ G.source.hom := by
  change (fp.pair.subspace.ι ≫ pullback.fst fp.pair.toBase.hom G.source.hom) ≫
      fp.pair.toBase.hom =
    (fp.pair.subspace.ι ≫ pullback.snd fp.pair.toBase.hom G.source.hom) ≫ G.source.hom
  rw [Category.assoc, Category.assoc, pullback.condition]

end FinitePart

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
