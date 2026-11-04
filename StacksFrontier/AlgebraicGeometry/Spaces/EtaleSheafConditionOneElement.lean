module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison

/-!
# Computing a sheaf on the spaces-étale site from its restriction to the scheme charts

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `F'` be
a sheaf on the spaces-étale site `X_{spaces,étale}`, with values in an arbitrary category, whose
restriction to the small étale site `X_{étale}` along
`AlgebraicGeometry.Space.comparisonFunctor` is `F`. If `U` is an algebraic space étale over
`X`, there is a scheme `U'` with a surjective étale morphism `U' → U`; then `{U' → U}` is a
covering of the spaces-étale site, the fibre product `U' ×_U U'` is again a scheme étale over
`X`, and the sheaf condition for that one-element covering presents the sections over `U` as an
equalizer

`F'(U) → F(U') ⇉ F(U' ×_U U')`

whose middle and right terms involve only `F`.

## Main results

* `CategoryTheory.Presheaf.isLimitForkOfSingletonCovering`: on an arbitrary site, a sheaf
  with values in an arbitrary category turns a one-element covering with a fibre product
  into a limiting fork.
* `AlgebraicGeometry.Space.exists_etaleChart_singleton_covering`: every algebraic space étale
  over `X` receives a surjective étale morphism from an étale scheme chart of `X`, and the
  resulting one-element family is a covering of the spaces-étale site.
* `AlgebraicGeometry.Space.exists_etaleChart_isPullback_self`: the fibre product of an étale
  scheme chart with itself over an algebraic space étale over `X` is again an étale scheme
  chart of `X`.
* `AlgebraicGeometry.Space.exists_isLimit_fork_of_isSheaf`: the equalizer diagram above, with
  its covering and its fibre product, for a sheaf on the spaces-étale site.

## References

* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Presheaf

universe w w' v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {A : Type w} [Category.{w'} A]

/-- A sheaf turns a one-element covering with a fibre product into a limiting fork.

If `{f : V ⟶ U}` generates a covering sieve and `p, q : W ⟶ V` exhibit `W` as the fibre
product `V ×_U V`, then for every sheaf `P`, with values in an arbitrary category, the fork

`P(U) → P(V) ⇉ P(W)`

built from `f` and the two projections is a limit. -/
@[sga "4 II 6.2" "special case"]
noncomputable def isLimitForkOfSingletonCovering (P : Cᵒᵖ ⥤ A) (hP : IsSheaf J P)
    {W V U : C} {f : V ⟶ U} {p q : W ⟶ V} (hpb : IsPullback p q f f)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J U)
    (w : P.map f.op ≫ P.map p.op = P.map f.op ≫ P.map q.op) :
    IsLimit (Fork.ofι (P.map f.op) w) := by
  apply coyonedaJointlyReflectsLimits
  intro E
  have hsheaf : Presieve.IsSheafFor (P ⋙ coyoneda.obj E) (Presieve.singleton f) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hP E.unop _ hf
  rw [Equalizer.Presieve.isSheafFor_singleton_iff
    (PullbackCone.mk p q hpb.w) hpb.isLimit] at hsheaf
  exact (isLimitMapConeForkEquiv (coyoneda.obj E) w).symm hsheaf.some

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Space

universe w w' u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The one-element covering by a scheme chart -/

/-- Let `U` be an algebraic space étale over `X`. There is an étale scheme chart `V` of `X`
and a morphism `V → U` of the spaces-étale site which is étale and surjective, and the
one-element family `{V → U}` is a covering family of the spaces-étale site of `X`. -/
@[stacks 03H7 "the one-element covering by a scheme"]
theorem exists_etaleChart_singleton_covering (U : SpacesEtale B S hS X) :
    ∃ (V : SmallEtale B S hS X.1) (f : (comparisonFunctor B S hS X).obj V ⟶ U),
      IsEtale B S hS ((SpacesEtale.toSpaces B S hS X).map f).hom ∧
      IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map f).hom ∧
      SpacesEtale.IsCovering B S hS X ⟨U, PreZeroHypercover.singleton.{u + 1} f⟩ := by
  set Usp := (SpacesEtale.toSpaces B S hS X).obj U
  obtain ⟨T, a, hasurj, haetale⟩ := Usp.property.exists_atlas
  have haEtale : IsEtale B S hS a := isEtale_of_presheaf_etale B S hS haetale
  have hbEtale : IsEtale B S hS (a ≫ (((SpacesEtale.inclusion B S hS X).obj U).hom.hom)) :=
    isEtale_comp B S hS haEtale U.property
  have hsurj : IsSurjective B S hS a :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Usp.1 Usp.property T a).mp hasurj
  refine ⟨⟨CostructuredArrow.mk (a ≫ (((SpacesEtale.inclusion B S hS X).obj U).hom.hom)),
      presheaf_etale_of_isEtale B S hS hbEtale⟩,
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) rfl), haEtale, hsurj,
    fun x => ⟨default, (hsurj x).choose, (hsurj x).choose_spec⟩⟩

/-- The one-element covering of `AlgebraicGeometry.Space.exists_etaleChart_singleton_covering`
generates a covering sieve of the spaces-étale topology. -/
theorem singleton_generate_mem_topology {U : SpacesEtale B S hS X}
    {V : SmallEtale B S hS X.1} (f : (comparisonFunctor B S hS X).obj V ⟶ U)
    (hf : SpacesEtale.IsCovering B S hS X ⟨U, PreZeroHypercover.singleton.{u + 1} f⟩) :
    Sieve.generate (Presieve.singleton f) ∈ SpacesEtale.topology B S hS X U := by
  rw [show Presieve.singleton f = (PreZeroHypercover.singleton.{u + 1} f).presieve₀ from
    (PreZeroHypercover.presieve₀_singleton f).symm]
  exact Precoverage.generate_mem_toGrothendieck ⟨_, rfl, hf⟩

/-! ### The fibre product of a scheme chart with itself -/

/-- The fibre product of a scheme over an algebraic space `Y` with itself is a scheme, and
one projection is étale as soon as the given morphism is. -/
theorem exists_isPullback_yoneda_self_of_isEtale (V' : BigFppfOver B S hS)
    (Y : AlgebraicSpaces B S hS) (u : yoneda.obj V' ⟶ Y.1) (hu : IsEtale B S hS u) :
    ∃ (W' : BigFppfOver B S hS) (p' q' : W' ⟶ V'),
      IsPullback (yoneda.map p') (yoneda.map q') u u ∧ IsEtale B S hS (yoneda.map p') := by
  have huPre : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u :=
    presheaf_etale_of_isEtale B S hS hu
  have hrep : yoneda.relativelyRepresentable u := Y.property.diagonal_representable.of_diag u
  have hpb : IsPullback (yoneda.map (hrep.fst' u)) (yoneda.map (hrep.snd u)) u u :=
    hrep.isPullback' u
  refine ⟨hrep.pullback u, hrep.fst' u, hrep.snd u, hpb, isEtale_of_presheaf_etale B S hS ?_⟩
  exact (MorphismProperty.relative_isStableUnderBaseChange (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))).of_isPullback hpb.flip huPre

/-- Let `U` be an algebraic space étale over `X`, let `V` be an étale scheme chart of `X` and
let `f : V → U` be a morphism of the spaces-étale site. Then there is an étale scheme chart `W`
of `X` and a pair of morphisms `p, q : W → V` of the *small* étale site whose images under the
comparison functor exhibit `W` as the fibre product `V ×_U V` in the spaces-étale site. -/
@[stacks 03H7 "the fibre product is a scheme"]
theorem exists_etaleChart_isPullback_self (U : SpacesEtale B S hS X)
    (V : SmallEtale B S hS X.1) (f : (comparisonFunctor B S hS X).obj V ⟶ U) :
    ∃ (W : SmallEtale B S hS X.1) (p q : W ⟶ V),
      IsPullback ((comparisonFunctor B S hS X).map p)
        ((comparisonFunctor B S hS X).map q) f f := by
  have hwf : ((SpacesEtale.toSpaces B S hS X).map f).hom ≫
      (((SpacesEtale.inclusion B S hS X).obj U).hom.hom) = V.1.hom :=
    congrArg (fun k => k.hom) ((SpacesEtale.inclusion B S hS X).map f).w
  have huEtale : IsEtale B S hS (((SpacesEtale.toSpaces B S hS X).map f).hom) :=
    isEtale_of_isEtale_over B S hS
      ((SpacesEtale.toSpaces B S hS X).obj ((comparisonFunctor B S hS X).obj V)).property
      ((SpacesEtale.toSpaces B S hS X).obj U).property X.property _
      (((SpacesEtale.inclusion B S hS X).obj ((comparisonFunctor B S hS X).obj V)).hom.hom)
      (((SpacesEtale.inclusion B S hS X).obj U).hom.hom)
      ((comparisonFunctor B S hS X).obj V).property U.property hwf
  obtain ⟨W', p', q', hpb, hp'⟩ := exists_isPullback_yoneda_self_of_isEtale B S hS V.1.left
    ((SpacesEtale.toSpaces B S hS X).obj U) (((SpacesEtale.toSpaces B S hS X).map f).hom)
    huEtale
  have hWEtale : IsEtale B S hS (yoneda.map p' ≫ V.1.hom) :=
    isEtale_comp B S hS hp' (isEtale_of_presheaf_etale B S hS V.2)
  have hcomm : yoneda.map q' ≫ V.1.hom = yoneda.map p' ≫ V.1.hom := by
    rw [← hwf]; erw [← Category.assoc, ← Category.assoc, hpb.w]
  refine ⟨⟨CostructuredArrow.mk (yoneda.map p' ≫ V.1.hom),
      presheaf_etale_of_isEtale B S hS hWEtale⟩,
    ObjectProperty.homMk (CostructuredArrow.homMk p' rfl),
    ObjectProperty.homMk (CostructuredArrow.homMk q' hcomm), ?_⟩
  exact IsPullback.of_map_of_faithful
    (SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _) hpb

/-! ### Restriction to the small étale site -/

variable {A : Type w} [Category.{w'} A]

/-- The sections of a presheaf `P` on the spaces-étale site over the algebraic space attached to
an étale scheme chart `V` are the sections over `V` of the restriction of `P` to the small étale
site. -/
theorem comparison_restriction_obj (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (V : SmallEtale B S hS X.1) :
    ((comparisonFunctor B S hS X).op ⋙ P).obj (Opposite.op V) =
      P.obj (Opposite.op ((comparisonFunctor B S hS X).obj V)) := rfl

/-- The restriction map of a presheaf `P` on the spaces-étale site along the comparison image of
a morphism of étale scheme charts is the restriction map of the restriction of `P` to the small
étale site. -/
theorem comparison_restriction_map (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    {V W : SmallEtale B S hS X.1} (p : W ⟶ V) :
    ((comparisonFunctor B S hS X).op ⋙ P).map p.op =
      P.map ((comparisonFunctor B S hS X).map p).op := rfl

/-! ### The equalizer diagram -/

/-- The equalizer diagram of `AlgebraicGeometry.Space.exists_isLimit_fork_of_isSheaf` for a
*given* one-element covering of an algebraic space `U` étale over `X` by an étale scheme chart
`V`, with a *given* presentation of `V ×_U V` by an étale scheme chart `W`: for every sheaf `P`
on the spaces-étale site the fork `P(U) → P(V) ⇉ P(W)` is a limit. -/
noncomputable def isLimitForkOfEtaleChartCovering (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U : SpacesEtale B S hS X} {V W : SmallEtale B S hS X.1} {p q : W ⟶ V}
    {f : (comparisonFunctor B S hS X).obj V ⟶ U}
    (hf : SpacesEtale.IsCovering B S hS X ⟨U, PreZeroHypercover.singleton.{u + 1} f⟩)
    (hpb : IsPullback ((comparisonFunctor B S hS X).map p)
      ((comparisonFunctor B S hS X).map q) f f)
    (w : P.map f.op ≫ ((comparisonFunctor B S hS X).op ⋙ P).map p.op =
      P.map f.op ≫ ((comparisonFunctor B S hS X).op ⋙ P).map q.op) :
    IsLimit (Fork.ofι (P.map f.op) w) :=
  Presheaf.isLimitForkOfSingletonCovering (SpacesEtale.topology B S hS X) P hP hpb
    (singleton_generate_mem_topology B S hS X f hf) w

/-- Let `X` be an algebraic space over `S`, let `P` be a sheaf on the spaces-étale site of
`X`, and write `F = (comparisonFunctor).op ⋙ P` for its restriction to the small étale site of
`X`. Then for every algebraic space `U` étale over `X` there are an étale scheme chart `V` of
`X`, a surjective étale morphism `f : V → U` of the spaces-étale site whose one-element family
is a covering, and a second étale scheme chart `W` with morphisms `p, q : W → V` of the small
étale site exhibiting `W` as `V ×_U V`, such that

`P(U) → F(V) ⇉ F(W)`

is an equalizer diagram, the two parallel arrows being restriction along `p` and along `q`. -/
@[stacks 03H7 "the equalizer diagram"]
theorem exists_isLimit_fork_of_isSheaf (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P) (U : SpacesEtale B S hS X) :
    ∃ (V : SmallEtale B S hS X.1) (f : (comparisonFunctor B S hS X).obj V ⟶ U)
      (W : SmallEtale B S hS X.1) (p q : W ⟶ V)
      (_ : IsPullback ((comparisonFunctor B S hS X).map p)
        ((comparisonFunctor B S hS X).map q) f f)
      (w : P.map f.op ≫ ((comparisonFunctor B S hS X).op ⋙ P).map p.op =
        P.map f.op ≫
          ((comparisonFunctor B S hS X).op ⋙ P).map q.op),
      IsEtale B S hS ((SpacesEtale.toSpaces B S hS X).map f).hom ∧
      IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map f).hom ∧
      SpacesEtale.IsCovering B S hS X ⟨U, PreZeroHypercover.singleton.{u + 1} f⟩ ∧
      Nonempty (IsLimit (Fork.ofι (P.map f.op) w)) := by
  obtain ⟨V, f, hfEtale, hfSurj, hfCov⟩ :=
    exists_etaleChart_singleton_covering B S hS X U
  obtain ⟨W, p, q, hpb⟩ := exists_etaleChart_isPullback_self B S hS X U V f
  have w : P.map f.op ≫ ((comparisonFunctor B S hS X).op ⋙ P).map p.op =
      P.map f.op ≫ ((comparisonFunctor B S hS X).op ⋙ P).map q.op := by
    rw [comparison_restriction_map, comparison_restriction_map, ← P.map_comp, ← P.map_comp,
      ← op_comp, ← op_comp, hpb.w]
  exact ⟨V, f, W, p, q, hpb, w, hfEtale, hfSurj, hfCov,
    ⟨isLimitForkOfEtaleChartCovering B S hS X P hP hfCov hpb w⟩⟩

end AlgebraicGeometry.Space

end
