module

public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# Computing a sheaf on the spaces-étale site from a scheme chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `U`
be an algebraic space étale over `X`, that is, an object of the spaces-étale site of `X`.
Then `U` is covered, in that site, by a single *scheme* chart: an object of the small étale
site of `X` whose associated algebraic space maps to `U`.  The self-intersection of that chart
over `U` is again represented by a scheme chart, so the two projections of the self-intersection
are again morphisms in the image of the small étale site.

Consequently the sheaf condition for a sheaf `G` on the spaces-étale site reads, over `U`, as an
equalizer of the two restriction maps from the covering chart to its self-intersection — a
diagram all of whose terms are sections of `G` on *schemes*.

## Main results

* `AlgebraicGeometry.Space.exists_scheme_chart_self_intersection`: the fibre product of such a
  chart with itself over the object it covers is again an étale scheme chart of `X`.
* `AlgebraicGeometry.Space.sections_equalizer_of_scheme_chart`: the sections of a sheaf on the
  spaces-étale site over an object are the equalizer of the two restriction maps from a covering
  scheme chart to its scheme self-intersection.

## References

* [Stacks Project, Lemma 66.18.9 (Tag 03H7)](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

/-- The morphism of ambient objects underlying the `CategoryTheory.eqToHom` of an equality of
objects of a slice category over a full subcategory is the `CategoryTheory.eqToHom` of the
induced equality of ambient objects. -/
theorem over_left_underlying_eqToHom {D : Type*} [Category D] {P : ObjectProperty D}
    (X : ObjectProperty.FullSubcategory P) {A C : Over X} (e : A = C) :
    ((eqToHom e).left).hom = eqToHom (congrArg (fun Z : Over X => Z.left.1) e) := by
  cases e; rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The self-intersection of a scheme chart over an object of the spaces-étale site of `X` is
again an étale scheme chart of `X`, with its canonical pullback projections. -/
@[stacks 03H7 "the scheme self-intersection"]
theorem exists_scheme_chart_self_intersection {U : SpacesEtale B S hS X}
    {V : SmallEtale B S hS X.1} (f : (comparisonFunctor B S hS X).obj V ⟶ U) :
    ∃ (W : SmallEtale B S hS X.1)
      (p q : (comparisonFunctor B S hS X).obj W ⟶ (comparisonFunctor B S hS X).obj V),
      IsPullback p q f f := by
  classical
  let Uover := (SpacesEtale.inclusion B S hS X).obj U
  let Vover := chartOver B S hS X V
  let heqV := comparisonFunctor_obj B S hS X V
  let fOver : Vover ⟶ Uover := eqToHom heqV.symm ≫ (SpacesEtale.inclusion B S hS X).map f
  let T := (SmallEtale.toOver B S hS X.1).obj V
  let a : yoneda.obj T ⟶ Uover.left.1 := fOver.left.hom
  let b : yoneda.obj T ⟶ X.1 := V.1.hom
  let u : Uover.left.1 ⟶ X.1 := Uover.hom.hom
  have hcompat : a ≫ u = b := by
    change fOver.left.hom ≫ Uover.hom.hom = Vover.hom.hom
    exact congrArg (fun g : Vover.left ⟶ X => g.hom) fOver.w
  have hb : IsEtale B S hS b := isEtale_of_presheaf_etale B S hS V.property
  have ha : IsEtale B S hS a :=
    isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS T) Uover.left.property
      X.property a b u hb U.property hcompat
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrep : yoneda.relativelyRepresentable a :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := Uover.left.1)).mp
      Uover.left.property.diagonal_representable a
  let T' := hrep.pullback a
  let p' := hrep.fst' a
  let q' := hrep.snd a
  have hpullback : IsPullback (yoneda.map p') (yoneda.map q') a a := hrep.isPullback' a
  let Wsp : AlgebraicSpaces B S hS := ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩
  let Vsp := Vover.left
  let psp : Wsp ⟶ Vsp := ObjectProperty.homMk (yoneda.map p')
  let qsp : Wsp ⟶ Vsp := ObjectProperty.homMk (yoneda.map q')
  have hpbsp : IsPullback psp qsp fOver.left fOver.left :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS)) hpullback
  let b' : yoneda.obj T' ⟶ X.1 := yoneda.map p' ≫ b
  let W : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk b', presheaf_etale_of_isEtale B S hS
    (isEtale_comp B S hS
      (isEtale_of_isPullback B S hS qsp psp fOver.left fOver.left hpbsp.flip ha) hb)⟩
  let Wover := chartOver B S hS X W
  let heqW := comparisonFunctor_obj B S hS X W
  let pOver : Wover ⟶ Vover := Over.homMk psp (ObjectProperty.hom_ext _ rfl)
  let qOver : Wover ⟶ Vover := Over.homMk qsp (by
    apply ObjectProperty.hom_ext
    change yoneda.map q' ≫ b = b'
    dsimp [b']
    rw [← hcompat, ← Category.assoc, ← Category.assoc, ← hpullback.w])
  let toComparison (r : Wover ⟶ Vover) :
      (comparisonFunctor B S hS X).obj W ⟶ (comparisonFunctor B S hS X).obj V :=
    ObjectProperty.homMk (eqToHom heqW ≫ r ≫ eqToHom heqV.symm)
  let p := toComparison pOver
  let q := toComparison qOver
  have hpbOver : IsPullback pOver qOver fOver fOver :=
    IsPullback.of_map_of_faithful (Over.forget X) hpbsp
  let eW : Wover ≅ ((comparisonFunctor B S hS X).obj W).1 := eqToIso heqW.symm
  let eV : Vover ≅ ((comparisonFunctor B S hS X).obj V).1 := eqToIso heqV.symm
  have hpbOver' : IsPullback
      ((SpacesEtale.inclusion B S hS X).map p) ((SpacesEtale.inclusion B S hS X).map q)
      ((SpacesEtale.inclusion B S hS X).map f) ((SpacesEtale.inclusion B S hS X).map f) := by
    apply IsPullback.of_iso hpbOver eW eV eV (Iso.refl Uover) <;>
      simp [p, q, toComparison, pOver, qOver, fOver, eW, eV]
  exact ⟨W, p, q, IsPullback.of_map_of_faithful (SpacesEtale.inclusion B S hS X) hpbOver'⟩

/-- The sections of a sheaf on the spaces-étale site of `X` over an object `U` are the equalizer
of the two restriction maps from a scheme chart covering `U` to the scheme self-intersection of
that chart. -/
@[stacks 03H7 "the equalizer diagram"]
theorem sections_equalizer_of_scheme_chart {U : SpacesEtale B S hS X}
    {V W : SmallEtale B S hS X.1} (f : (comparisonFunctor B S hS X).obj V ⟶ U)
    (p q : (comparisonFunctor B S hS X).obj W ⟶ (comparisonFunctor B S hS X).obj V)
    (hcover : Sieve.generate (Presieve.singleton f) ∈ SpacesEtale.topology B S hS X U)
    (hpullback : IsPullback p q f f)
    (G : Sheaf (SpacesEtale.topology B S hS X) (Type w)) :
    Nonempty (IsLimit (Fork.ofι (G.obj.map f.op) (f := G.obj.map p.op) (g := G.obj.map q.op)
      (by simp [← Functor.map_comp, ← op_comp, hpullback.w]))) :=
  (Equalizer.Presieve.isSheafFor_singleton_iff (F := G.obj) (f := f)
      (c := PullbackCone.mk p q hpullback.w) hpullback.isLimit).mp
    ((Presieve.isSheafFor_iff_generate (P := G.obj) (R := Presieve.singleton f)).2
      (G.property.isSheafFor _ hcover))

end AlgebraicGeometry.Space

end
