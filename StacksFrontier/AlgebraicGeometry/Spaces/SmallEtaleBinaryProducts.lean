module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite

/-!
# Binary products in the small étale site of an algebraic space

Let `F` be a presheaf on the big fppf site of `S`. Two étale charts `φ : yoneda.obj U ⟶ F`
and `ψ : yoneda.obj V ⟶ F` of `F` have a product in the small étale site
`AlgebraicGeometry.Space.SmallEtale`, namely the fibre product `U ×_F V`.

The point is that this fibre product is *representable*: being an étale chart includes being a
representable morphism of presheaves, so `φ` has a represented base change along `ψ`. The
resulting object `W` of the big fppf site of `S`, with its morphism
`yoneda.map (W ⟶ V) ≫ ψ` to `F`, is again an étale chart, because the projection `W ⟶ V` is a
represented base change of `φ` and is therefore étale by the very definition of an étale chart,
and composing an étale morphism of the site with an étale chart gives an étale chart (part (1)
of Stacks 03EC). Its universal property as a product in the small étale site is exactly the
universal property of the fibre product read off inside the big fppf site of `S`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.prodObj` is the fibre product of two étale charts,
  with `AlgebraicGeometry.Space.SmallEtale.prodFst` and
  `AlgebraicGeometry.Space.SmallEtale.prodSnd` its two projections.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.prodIsLimit` exhibits those projections as a product
  (it is data, being a universal property, but it is stated here with the results it serves).
* `AlgebraicGeometry.Space.SmallEtale.instHasBinaryProducts`: the small étale site of any
  presheaf on the big fppf site of `S` has binary products.
* `AlgebraicGeometry.Space.smallEtaleRingedSite_hasBinaryProducts` restates this for the
  underlying category of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search
  does not unfold.
* `AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over` is a further restatement of
  the same kind, needed alongside the previous one by the same consumers.
* `AlgebraicGeometry.Space.smallEtaleRingedSite_essentiallySmall` is the same restatement for
  essential smallness, and is deliberately **not** an instance; its docstring records the
  result that making it one breaks.

## Implementation notes

No algebraic space hypothesis on `F` is needed, and in particular the representability of the
diagonal of `F` is not used: representability of the two charts themselves already supplies
the fibre product. The construction is therefore stated for an arbitrary presheaf `F`, which is
the most general form in which it is true. The restatements for
`AlgebraicGeometry.Space.smallEtaleRingedSite` carry that hypothesis only because the ringed
site itself does, its structure sheaf being defined from it.

Everything is phrased through Mathlib's API for relatively representable morphisms:
`CategoryTheory.Functor.relativelyRepresentable.pullback` is the representing object,
`fst'`/`snd` its projections, `lift'` the induced morphism and `hom_ext'` its uniqueness.
Those are formulated inside the big fppf site of `S` rather than in presheaves, which is what
makes the product object an honest object of the site with no comparison isomorphism needed:
the second projection of the fibre product is the second projection of the product *on the
nose*, so `AlgebraicGeometry.Space.SmallEtale.prodSnd` is built from `rfl`.

The small étale site has no terminal object in general — `F` itself need not be
representable — so binary products do not follow from
`AlgebraicGeometry.Space.SmallEtale.instHasPullbacks` by
`hasBinaryProducts_of_hasTerminal_and_pullbacks`, and they are not
instances of the general theory of slices either: a product in the small étale site is a fibre
product *over `F`*, and `F` is not an object of the site.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

namespace SmallEtale

/-- The fibre product `U ×_F V` of two étale charts `X = (U, φ)` and `Y = (V, ψ)` of `F`, as an
étale chart of `F`.

Its underlying object of the big fppf site of `S` is the represented base change of `φ` along
`ψ`, and its structure morphism to `F` is the second projection followed by `ψ`. The projection
is étale because being an étale chart says exactly that every represented base change is, and
the composite is then an étale chart by part (1) of Stacks 03EC. -/
noncomputable def prodObj (X Y : SmallEtale B S hS F) : SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk (yoneda.map (X.property.rep.snd Y.obj.hom) ≫ Y.obj.hom),
    etale_comp_of_scheme B S hS _ Y.obj.hom
      (X.property.property_snd Y.obj.hom) Y.property⟩

/-- The first projection of the fibre product of two étale charts, given by the first
projection of the representing base change; its triangle over `F` commutes because that base
change is a pullback square. -/
noncomputable def prodFst (X Y : SmallEtale B S hS F) : prodObj B S hS F X Y ⟶ X :=
  ObjectProperty.homMk (CostructuredArrow.homMk (X.property.rep.fst' Y.obj.hom)
    (X.property.rep.isPullback' Y.obj.hom).w)

/-- The second projection of the fibre product of two étale charts. Its triangle over `F`
commutes by definition of the structure morphism of
`AlgebraicGeometry.Space.SmallEtale.prodObj`. -/
noncomputable def prodSnd (X Y : SmallEtale B S hS F) : prodObj B S hS F X Y ⟶ Y :=
  ObjectProperty.homMk (CostructuredArrow.homMk (X.property.rep.snd Y.obj.hom) rfl)

/-- The two projections of the fibre product of two étale charts exhibit it as their product
in the small étale site of `F`.

A cone over the pair is a chart `(T, θ)` together with morphisms `T ⟶ U` and `T ⟶ V` of the
big fppf site of `S` whose composites with `φ` and `ψ` are both `θ`; the universal property of
the representing base change turns such a pair into a unique morphism `T ⟶ U ×_F V`. -/
noncomputable def prodIsLimit (X Y : SmallEtale B S hS F) :
    IsLimit (BinaryFan.mk (prodFst B S hS F X Y) (prodSnd B S hS F X Y)) := by
  refine BinaryFan.isLimitMk (fun s => ObjectProperty.homMk (CostructuredArrow.homMk
    (X.property.rep.lift' (s.fst : s.pt ⟶ X).hom.left (s.snd : s.pt ⟶ Y).hom.left
      ((CostructuredArrow.w (s.fst : s.pt ⟶ X).hom).trans
        (CostructuredArrow.w (s.snd : s.pt ⟶ Y).hom).symm)) ?_)) ?_ ?_ ?_
  · change yoneda.map _ ≫ yoneda.map (X.property.rep.snd Y.obj.hom) ≫ Y.obj.hom = _
    rw [← Functor.map_comp_assoc, Functor.relativelyRepresentable.lift'_snd]
    exact CostructuredArrow.w (s.snd : s.pt ⟶ Y).hom
  · intro s
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    exact Functor.relativelyRepresentable.lift'_fst _ _ _ _
  · intro s
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    exact Functor.relativelyRepresentable.lift'_snd _ _ _ _
  · intro s m h₁ h₂
    have e₁ : m.hom.left ≫ X.property.rep.fst' Y.obj.hom = (s.fst : s.pt ⟶ X).hom.left :=
      congrArg (fun f : s.pt ⟶ X => f.hom.left) h₁
    have e₂ : m.hom.left ≫ X.property.rep.snd Y.obj.hom = (s.snd : s.pt ⟶ Y).hom.left :=
      congrArg (fun f : s.pt ⟶ Y => f.hom.left) h₂
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
      (Functor.relativelyRepresentable.hom_ext' _ ?_ ?_))
    · exact e₁.trans (Functor.relativelyRepresentable.lift'_fst _ _ _ _).symm
    · exact e₂.trans (Functor.relativelyRepresentable.lift'_snd _ _ _ _).symm

/-- The small étale site of a presheaf on the big fppf site of `S` has binary products: they
are the fibre products of étale charts over the presheaf. -/
instance instHasBinaryProducts : HasBinaryProducts (SmallEtale B S hS F) :=
  have : ∀ {X Y : SmallEtale B S hS F}, HasLimit (pair X Y) := fun {X Y} =>
    ⟨_, prodIsLimit B S hS F X Y⟩
  hasBinaryProducts_of_hasLimit_pair _

end SmallEtale

/-- The underlying category of the small étale ringed site of an algebraic space has binary
products.

The content is `AlgebraicGeometry.Space.SmallEtale.instHasBinaryProducts`; this restates it for
the projection of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does
not unfold. -/
instance smallEtaleRingedSite_hasBinaryProducts (hF : IsAlgebraicSpace B S hS F) :
    HasBinaryProducts (smallEtaleRingedSite B S hS F hF).C := by
  change HasBinaryProducts (SmallEtale B S hS F)
  infer_instance

/-- The underlying category of the small étale ringed site of an algebraic space has a small
model at the universe of its schemes.

The content is `AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`; this restates it for
the projection of `AlgebraicGeometry.Space.smallEtaleRingedSite`.

**This must not be made an instance.** Unlike the other restatements in this file and in
`AlgebraicGeometry.Space.RingedSite`, making it one changes how the implicit category argument
of `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` is solved:
with it available, that argument is taken to be the unreduced projection rather than
`AlgebraicGeometry.Space.SmallEtale`, and the instance it then asks for on the induced topology
of `CategoryTheory.equivSmallModel` of the projection is not found. As an instance it
breaks `AlgebraicGeometry.Space.wEqualsLocallyBijective_smallEtaleRingedSite_addCommGrpCat`
outright for any module importing both. Consumers should use this lemma with `have`. -/
theorem smallEtaleRingedSite_essentiallySmall (hF : IsAlgebraicSpace B S hS F) :
    EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
  show EssentiallySmall.{u} (SmallEtale B S hS F)
  infer_instance

/-- Presheaves of abelian groups on every slice of the small étale ringed site of an algebraic
space have sheafifications, in the `∀`-quantified form that the sheaves-of-modules API consumes.

The content is `AlgebraicGeometry.Space.SmallEtale.instHasSheafifyOver`; this restates it for
the projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does
not unfold.  It is the `HasSheafify` companion of
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over`. -/
instance smallEtaleRingedSite_hasSheafify_over (hF : IsAlgebraicSpace B S hS F) :
    ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      HasSheafify ((smallEtaleRingedSite B S hS F hF).J.over U) AddCommGrpCat.{u} := by
  change ∀ U : SmallEtale B S hS F,
    HasSheafify ((SmallEtale.topology B S hS F).over U) AddCommGrpCat.{u}
  infer_instance

end AlgebraicGeometry.Space

end
