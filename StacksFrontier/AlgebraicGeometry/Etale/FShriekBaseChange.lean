module

public import Mathlib.Algebra.DirectSum.Module
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients

/-!
# Base change of the direct image with compact support on geometric stalks

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'`, with `f` locally
quasi-finite, and let `F` be an abelian sheaf on the small étale site of `X`. Transitivity of
fibre products identifies the geometric fibre of `f'` over a geometric point `t` of `Y'` with
the geometric fibre of `f` over its image in `Y`, and over corresponding points of the two
fibres the stalks of `p⁻¹F` and of `F` agree. Combined with the stalk decompositions of
Stacks 0F5F for `f` and for `f'` this identifies the stalk of `g⁻¹f_!F` at `t` with the stalk
of `f'_!p⁻¹F` at `t`, compatibly with those decompositions. This is Stacks 0F5J on stalks.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fiberPointBaseChange` — the map from the geometric fibre of `f'`
  to the geometric fibre of `f` given by composing with `p`, with
  `AlgebraicGeometry.SmallEtale.fiberPointBaseChangeEquiv` the resulting equivalence.
* `AlgebraicGeometry.SmallEtale.fiberStalkBaseChangeIso` — the identification of the stalk of
  `F` at a point of the geometric fibre of `f` with the stalk of `p⁻¹F` at the corresponding
  point of the geometric fibre of `f'`.
* `AlgebraicGeometry.SmallEtale.fiberStalksBaseChangeEquiv` — the resulting comparison of the
  two direct sums of stalks over the geometric fibres.
* `AlgebraicGeometry.SmallEtale.fShriekStalkBaseChangeIso` — the base-change comparison
  `(g⁻¹f_!F)_t ≅ (f'_!p⁻¹F)_t` on the stalk at a geometric point of `Y'`.

## Main results

* `AlgebraicGeometry.SmallEtale.fiberPointBaseChange_bijective` — the geometric fibres of `f`
  and of `f'` are in bijection through `p`.
* `AlgebraicGeometry.SmallEtale.fiberStalksBaseChangeEquiv_apply` and
  `AlgebraicGeometry.SmallEtale.fiberStalksBaseChangeEquiv_natural` — the comparison of the two
  direct sums of stalks acts componentwise and is functorial in the abelian sheaf.
* `AlgebraicGeometry.SmallEtale.fShriekStalkBaseChangeIso_comp_fShriekStalkIso` and
  `AlgebraicGeometry.SmallEtale.fShriekStalkBaseChangeIso_hom_comp` — the compatibility of the
  stalkwise comparison with the stalk decompositions of Stacks 0F5F, which is the commutative
  square of Stacks 0F5J for the base-change map.

## Implementation notes

The finite-type and quasi-finiteness hypotheses on `f'` are carried as instance arguments; they
are automatic, being the base change along `g` of those for `f`, and
`AlgebraicGeometry.SmallEtale.locallyOfFiniteType_of_isPullback` and
`AlgebraicGeometry.SmallEtale.locallyQuasiFinite_of_isPullback` supply them from the square.

The identification of the stalks over corresponding points of the fibres is the inverse-image
comparison of Stacks 03Q1 with abelian coefficients, which is available for an arbitrary
coefficient category; the comparison of the two direct sums is then a reindexing along the
bijection of fibres followed by that identification on each summand.

## References

* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v

namespace DirectSum

/-- The additive equivalence of direct sums induced by a family of additive equivalences acts
componentwise. -/
public theorem congrAddEquiv_apply {ι : Type*} {N P : ι → Type*}
    [∀ i, AddCommMonoid (N i)] [∀ i, AddCommMonoid (P i)] (u : ∀ i, N i ≃+ P i)
    (z : ⨁ i, N i) (i : ι) : congrAddEquiv u z i = u i (z i) :=
  map_apply (fun j => (u j).toAddMonoidHom) i z

end DirectSum

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- A point of the geometric fibre of `f'` over a geometric point `t` of `Y'` gives a point of
the geometric fibre of `f` over the image of `t` in `Y`, by composing with `p`. -/
public def fiberPointBaseChange (sq : IsPullback p f' f g) (t : GeometricPoint Y'.obj)
    (x : GeometricFiberPoint B f' t) :
    GeometricFiberPoint B f (t.map (B.inclusion.map g)) :=
  ⟨x.1 ≫ B.inclusion.map p, by
    have h : B.inclusion.map p ≫ B.inclusion.map f =
        B.inclusion.map f' ≫ B.inclusion.map g := by
      rw [← Functor.map_comp, ← Functor.map_comp, sq.w]
    rw [Category.assoc, h, ← Category.assoc, x.2]
    rfl⟩

/-- **Stacks 0F5J.** For a cartesian square, `p` induces a bijection from the geometric fibre
of `f'` over a geometric point `t` of `Y'` onto the geometric fibre of `f` over the image of
`t`: transitivity of fibre products identifies `X'_t` with `X_{g ∘ t}`. -/
@[stacks 0F5J "the bijection of geometric fibres induced by the horizontal morphism"]
public theorem fiberPointBaseChange_bijective (sq : IsPullback p f' f g)
    (t : GeometricPoint Y'.obj) :
    Function.Bijective (fiberPointBaseChange B p f' f g sq t) := by
  refine ⟨fun x y hxy => Subtype.ext <| (sq.map B.inclusion).hom_ext ?_ (x.2.trans y.2.symm),
    fun y => ?_⟩
  · simpa [fiberPointBaseChange] using congrArg Subtype.val hxy
  · have hcomm : y.1 ≫ B.inclusion.map f = t.hom ≫ B.inclusion.map g := by
      simpa [GeometricPoint.map] using y.2
    exact ⟨⟨(sq.map B.inclusion).lift y.1 t.hom hcomm,
      (sq.map B.inclusion).lift_snd y.1 t.hom hcomm⟩,
      Subtype.ext ((sq.map B.inclusion).lift_fst y.1 t.hom hcomm)⟩

/-- The base change of a morphism locally of finite type is locally of finite type, so the
finite-type hypothesis of the vertical morphism of a cartesian square is inherited by its base
change. -/
public theorem locallyOfFiniteType_of_isPullback (sq : IsPullback p f' f g)
    [LocallyOfFiniteType (B.inclusion.map f)] :
    LocallyOfFiniteType (B.inclusion.map f') :=
  MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance

/-- The base change of a locally quasi-finite morphism is locally quasi-finite, so the
quasi-finiteness hypothesis of the vertical morphism of a cartesian square is inherited by its
base change. -/
public theorem locallyQuasiFinite_of_isPullback (sq : IsPullback p f' f g)
    [LocallyQuasiFinite (B.inclusion.map f)] :
    LocallyQuasiFinite (B.inclusion.map f') :=
  MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance

/-- The inverse image of abelian sheaves on small étale sites along a morphism of the big étale
site. -/
public abbrev abPullback {S T : B.Scheme} (q : T ⟶ S) :
    Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{max (u + 1) v} :=
  (smallEtaleBaseChange B q).sheafPullback AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

/-- The bijection of geometric fibres of Stacks 0F5J, packaged as an equivalence of types. -/
public def fiberPointBaseChangeEquiv (sq : IsPullback p f' f g) (t : GeometricPoint Y'.obj) :
    GeometricFiberPoint B f' t ≃ GeometricFiberPoint B f (t.map (B.inclusion.map g)) :=
  Equiv.ofBijective _ (fiberPointBaseChange_bijective B p f' f g sq t)

section FiberStalks

/-- **Stacks 0F5J.** The stalk of the inverse image `p⁻¹F` at a point `x` of the geometric
fibre of `f'` is the stalk of `F` at the corresponding point of the geometric fibre of `f`.
This is the right vertical arrow of the comparison square of Stacks 0F5J. -/
@[stacks 0F5J "the identification of the stalks over corresponding points of the fibres"]
public def fiberStalkBaseChangeIso (sq : IsPullback p f' f g) (t : GeometricPoint Y'.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (x : GeometricFiberPoint B f' t) :
    etaleStalk B X.obj X.property
        ((fiberPointBaseChange B p f' f g sq t x).toGeometricPoint B f
          (t.map (B.inclusion.map g))) F.obj ≅
      etaleStalk B X'.obj X'.property (x.toGeometricPoint B f' t)
        ((abPullback.{u, v} B p).obj F).obj :=
  (etaleStalkSmallEtalePullObjIso B p (x.toGeometricPoint B f' t)
    AddCommGrpCat.{max (u + 1) v} F).symm

/-- **Stacks 0F5J.** The direct sums of stalks over the two geometric fibres agree: the fibres
are in bijection through `p`, and over corresponding points the stalks of `F` and of `p⁻¹F`
agree. -/
@[stacks 0F5J "the comparison of the two direct sums of stalks over the geometric fibres"]
public def fiberStalksBaseChangeEquiv (sq : IsPullback p f' f g) (t : GeometricPoint Y'.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    fiberStalks.{u, max (u + 1) v} B f (t.map (B.inclusion.map g)) F ≃+
      fiberStalks.{u, max (u + 1) v} B f' t ((abPullback.{u, v} B p).obj F) :=
  (DirectSum.equivCongrLeft (fiberPointBaseChangeEquiv B p f' f g sq t).symm).trans
    (DirectSum.congrAddEquiv fun x =>
      (fiberStalkBaseChangeIso B p f' f g sq t F x).addCommGroupIsoToAddEquiv)

/-- The comparison of the two direct sums of stalks acts componentwise: its component at a
point `x` of the geometric fibre of `f'` is the component at `p ∘ x` of the geometric fibre of
`f`, read through the identification of the two stalks. -/
public theorem fiberStalksBaseChangeEquiv_apply (sq : IsPullback p f' f g)
    (t : GeometricPoint Y'.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (w : fiberStalks.{u, max (u + 1) v} B f (t.map (B.inclusion.map g)) F)
    (x : GeometricFiberPoint B f' t) :
    fiberStalksBaseChangeEquiv B p f' f g sq t F w x =
      (fiberStalkBaseChangeIso B p f' f g sq t F x).hom
        (w (fiberPointBaseChange B p f' f g sq t x)) := by
  rfl

/-- **Stacks 0F5J.** The comparison of the two direct sums of stalks is functorial in the
abelian sheaf: it intertwines the map induced on the direct sum of stalks over the geometric
fibre of `f` by a morphism of sheaves with the map induced over the geometric fibre of `f'` by
its inverse image. -/
@[stacks 0F5J "functoriality in the sheaf of the comparison of the direct sums of stalks"]
public theorem fiberStalksBaseChangeEquiv_natural (sq : IsPullback p f' f g)
    (t : GeometricPoint Y'.obj)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) (w : fiberStalks.{u, max (u + 1) v} B f (t.map (B.inclusion.map g)) F) :
    fiberStalksBaseChangeEquiv B p f' f g sq t G
        (fiberStalksMap.{u, max (u + 1) v} B f (t.map (B.inclusion.map g)) φ w) =
      fiberStalksMap.{u, max (u + 1) v} B f' t ((abPullback.{u, v} B p).map φ)
        (fiberStalksBaseChangeEquiv B p f' f g sq t F w) := by
  refine DFinsupp.ext fun x => ?_
  exact ConcreteCategory.congr_hom
    ((smallEtalePullbackSheafFiberIso B p (x.toGeometricPoint B f' t)
      AddCommGrpCat.{max (u + 1) v}).inv.naturality φ)
    (w (fiberPointBaseChange B p f' f g sq t x))

/-- The comparison of the two direct sums of stalks, as an isomorphism of abelian groups, is
functorial in the abelian sheaf. -/
public theorem fiberStalksBaseChangeIso_natural (sq : IsPullback p f' f g)
    (t : GeometricPoint Y'.obj)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) :
    AddCommGrpCat.ofHom
          (fiberStalksMap.{u, max (u + 1) v} B f (t.map (B.inclusion.map g)) φ) ≫
        (AddEquiv.toAddCommGrpIso (fiberStalksBaseChangeEquiv B p f' f g sq t G)).hom =
      (AddEquiv.toAddCommGrpIso (fiberStalksBaseChangeEquiv B p f' f g sq t F)).hom ≫
        AddCommGrpCat.ofHom
          (fiberStalksMap.{u, max (u + 1) v} B f' t ((abPullback.{u, v} B p).map φ)) := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun w => ?_)
  exact fiberStalksBaseChangeEquiv_natural B p f' f g sq t φ w

end FiberStalks

section Stalks

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]

/-- **Stacks 0F5J.** The base-change comparison on stalks: for a geometric point `t` of `Y'`
the stalk of `g⁻¹f_!F` at `t` is the stalk of `f'_!p⁻¹F` at `t`. It is obtained from the stalk
decompositions of Stacks 0F5F on both sides, the bijection of geometric fibres and the
identification of the stalks over corresponding points of the fibres, so it is compatible with
those decompositions by construction. -/
@[stacks 0F5J "the base-change isomorphism on the stalk at a geometric point of the base"]
public def fShriekStalkBaseChangeIso (sq : IsPullback p f' f g) (t : GeometricPoint Y'.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    etaleStalk B Y'.obj Y'.property t
        ((abPullback.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F)).obj ≅
      etaleStalk B Y'.obj Y'.property t
        ((fShriekFunctor.{u, v} B f').obj ((abPullback.{u, v} B p).obj F)).obj :=
  etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{max (u + 1) v}
      ((fShriekFunctor.{u, v} B f).obj F) ≪≫
    fShriekStalkIso.{u, v} B f (t.map (B.inclusion.map g)) F ≪≫
    AddEquiv.toAddCommGrpIso (fiberStalksBaseChangeEquiv B p f' f g sq t F) ≪≫
    (fShriekStalkIso.{u, v} B f' t ((abPullback.{u, v} B p).obj F)).symm

/-- **Stacks 0F5J.** The precise compatibility of the stalkwise base-change comparison with the
stalk decompositions of Stacks 0F5F: the square whose horizontal arrows are those
decompositions, whose left vertical arrow is the comparison preceded by the identification of
the stalk of an inverse image, and whose right vertical arrow is the summandwise comparison of
the two direct sums, commutes. -/
@[stacks 0F5J "compatibility of the stalkwise comparison with the decompositions of 0F5F"]
public theorem fShriekStalkBaseChangeIso_comp_fShriekStalkIso (sq : IsPullback p f' f g)
    (t : GeometricPoint Y'.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{max (u + 1) v}
          ((fShriekFunctor.{u, v} B f).obj F)).inv ≫
        (fShriekStalkBaseChangeIso B p f' f g sq t F).hom ≫
        (fShriekStalkIso.{u, v} B f' t ((abPullback.{u, v} B p).obj F)).hom =
      (fShriekStalkIso.{u, v} B f (t.map (B.inclusion.map g)) F).hom ≫
        AddCommGrpCat.ofHom
          (fiberStalksBaseChangeEquiv B p f' f g sq t F).toAddMonoidHom := by
  simp only [fShriekStalkBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  rfl

/-- The stalkwise base-change comparison, followed by the stalk decomposition of Stacks 0F5F
for `f'`, is the identification of the stalk of an inverse image followed by the stalk
decomposition for `f` and the comparison of the two direct sums. -/
public theorem fShriekStalkBaseChangeIso_hom_comp (sq : IsPullback p f' f g)
    (t : GeometricPoint Y'.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (fShriekStalkBaseChangeIso B p f' f g sq t F).hom ≫
        (fShriekStalkIso.{u, v} B f' t ((abPullback.{u, v} B p).obj F)).hom =
      (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{max (u + 1) v}
          ((fShriekFunctor.{u, v} B f).obj F)).hom ≫
        (fShriekStalkIso.{u, v} B f (t.map (B.inclusion.map g)) F).hom ≫
        (AddEquiv.toAddCommGrpIso (fiberStalksBaseChangeEquiv B p f' f g sq t F)).hom := by
  exact (Iso.inv_comp_eq _).1 (fShriekStalkBaseChangeIso_comp_fShriekStalkIso B p f' f g sq t F)

end Stalks

end AlgebraicGeometry.SmallEtale

end
