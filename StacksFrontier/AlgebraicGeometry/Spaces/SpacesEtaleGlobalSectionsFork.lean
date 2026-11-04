module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCounitFork
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections of a sheaf on the spaces-étale site as an equalizer over a chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `U` be an
étale scheme chart of `X` whose structure morphism is surjective on points, and let `R` be an
étale scheme chart with two morphisms `t, s : R ⟶ U` exhibiting it as `U ×_X U`.  Stacks 03M8
presents the sections of a sheaf over `X` as the equalizer of the two restrictions to `R` of its
sections over `U`.  This file states that presentation **on global sections**, in the two forms
a consumer asks for: as a limiting fork at the terminal object of the spaces-étale site, and as
a bijection of the type of sections of the underlying presheaf with a subtype of the sections
over `U`.

The spaces-étale site of `X` has `X` itself as a terminal object
(`AlgebraicGeometry.Space.SpacesEtale.isTerminal_idObj`), so a global section of a sheaf on that
site is a section over that terminal object, and the fork of Stacks 03M8 at the terminal object
is the sequence `Γ(X, ℱ) → ℱ(U) ⇉ ℱ(R)` of the source.  Both statements below are therefore
instances of the computation already carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardPresentationExact.lean`; what is added is the
terminal object as the place to evaluate it, and the passage from a limiting fork in `Type u` to
a bijection with a subtype, which is the shape in which
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation` consumes the
presentation.

## Main definitions

* `CategoryTheory.Functor.sectionsEquivObjOfIsInitial`: the sections of a functor whose index
  category has an initial object are its value at that object.  For a presheaf on the
  spaces-étale site the initial index is the opposite of the terminal object, so this says that
  global sections are sections over `X`.
* `CategoryTheory.Limits.Fork.IsLimit.ptEquivSubtype`: the vertex of a limiting fork in `Type v`
  is in bijection with the subtype of the elements of its source on which the two parallel maps
  agree.
* `AlgebraicGeometry.Space.isLimitForkIdObj` is the fork of Stacks 03M8 at the terminal object:
  for a sheaf `P` on the spaces-étale site of `X` with values in an arbitrary category,

  `P(X) → P(U) ⇉ P(R)`

  is a limit, the first arrow being restriction along the structure morphism of `U` and the two
  parallel arrows restriction along `t` and along `s`.
* `AlgebraicGeometry.Space.sectionsEquivEqualizerOfEtalePresentation` is the same statement for a
  sheaf of sets at the universe of the structure rings, read on the type of sections of the
  underlying presheaf: `Γ(X, P) ≃ {x : P(U) // t^*x = s^*x}`.
* `AlgebraicGeometry.Space.restrictSectionsToCharts` restricts a section over the terminal object
  to a compatible family of sections over the étale scheme charts, and
  `AlgebraicGeometry.Space.equivSectionsComparison` is the bijection it induces.
* `AlgebraicGeometry.Space.sectionsComparisonEquivEqualizer` is the equalizer presentation with
  the global sections computed over the **small** étale site, which is the site an `𝒪`-module of
  Stacks 03LU lives on.

## Main results

* `AlgebraicGeometry.Space.injective_map_op_of_isSurjective`: restriction of sections along a
  morphism of the spaces-étale site which is surjective on points is injective.
* `AlgebraicGeometry.Space.bijective_restrictSectionsToCharts`: restriction to the étale scheme
  charts is a bijection on global sections of a sheaf.  This is the passage from the
  spaces-étale site to the small étale site.

## Implementation notes

*Why the fork at the terminal object is not a new computation.*  The covering used is the
one-element family given by the unique morphism `U ⟶ X` of the site, which is surjective on
points exactly because the structure morphism of `U` is
(`AlgebraicGeometry.Space.SpacesEtale.toSpaces_map_from_idObj`), and the fibre product of that
morphism with itself is the hypothesis `hR` on the nose.  So
`AlgebraicGeometry.Space.isLimitForkOfSurjectiveSingleton` applies with no geometry beyond what
the hypotheses already carry, and neither
`AlgebraicGeometry.Space.isLimitForkOfEtalePresentation` nor its product form is needed: those
exist to handle a *general* object `W` of the site, where the fibre products `W ×_X U` and
`W ×_X R` have to be produced.

*Why the passage to the small étale site needs the sheaf condition.*  An `𝒪`-module of
Stacks 03LU lives on the *small* étale site, whose objects are the étale *scheme* charts and
which has **no terminal object**; its global sections are the sections of the underlying
presheaf over that site.  Identifying those with the sections over the terminal object of the
spaces-étale site is `AlgebraicGeometry.Space.bijective_restrictSectionsToCharts`, and it is not
an instance of `CategoryTheory.Functor.bijective_sectionsPrecomp`: that asks the opposite of
`AlgebraicGeometry.Space.comparisonFunctor` to be initial, which would mean every object of the
spaces-étale site admits a morphism *to* an étale scheme chart, and `X` itself does not.  For a
presheaf which is not a sheaf the statement is false — restriction to the charts forgets the
sections over `X` entirely — so the proof uses the sheaf condition, at the chart `U` for
injectivity and at a chart covering of each `V ×_X U` for surjectivity.

*What is left to reach a module.*  The statements below are for a sheaf on the spaces-étale
site, and read on the small étale site through restriction along the comparison functor.  A
`Modules.{u, u}` object is not presented that way: it is a sheaf on the small étale site, and
identifying it with the restriction of its extension is the counit of the comparison equivalence
of Stacks 03G1 (`AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`).  Transporting the
bijection below along that isomorphism of functors to types is not done here.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v' w w' t u

namespace CategoryTheory.Functor

/-- **The sections of a functor to types whose index category has an initial object are its
value at that object.**  A section is determined by its value at the initial index, every other
value being the image of it along the unique morphism, and any element of the value at the
initial index extends to a section in that way.

For a presheaf on a site with a terminal object the initial index is the opposite of that
terminal object, so this identifies the global sections of the presheaf — the limit over the
whole site — with its sections over the terminal object. -/
@[sga "3 I 1.2" "more general",
  sga "3 IV 4.3.17" "Set-valued diagrams",
  sga "4 V 8.1.5" "special case"]
def sectionsEquivObjOfIsInitial {J : Type v} [Category.{v'} J] (F : J ⥤ Type w) {i : J}
    (hi : Limits.IsInitial i) : F.sections ≃ F.obj i where
  toFun s := s.1 i
  invFun x :=
    ⟨fun j => F.map (hi.to j) x, fun {j j'} f => by
      rw [← Functor.map_comp_apply, hi.hom_ext (hi.to j ≫ f) (hi.to j')]⟩
  left_inv s := Subtype.ext (funext fun j => s.2 (hi.to j))
  right_inv x := by
    dsimp only
    rw [hi.hom_ext (hi.to i) (𝟙 i), F.map_id]
    rfl

end CategoryTheory.Functor

namespace CategoryTheory.Limits

/-- **The vertex of a limiting fork in `Type v` is the subtype on which the two parallel maps
agree.**  The forward map is the arrow of the fork, which lands in that subtype by the fork's
own commutation; the inverse is the lift of the fork on a one-element type determined by an
element of the subtype.

Both halves of the inverse property are `CategoryTheory.Limits.Fork.IsLimit.lift'` read at the
unique element of `PUnit`, together with the uniqueness clause
`CategoryTheory.Limits.Fork.IsLimit.hom_ext`. -/
def Fork.IsLimit.ptEquivSubtype {X Y : Type v} {f g : X ⟶ Y} {c : Fork f g}
    (hc : IsLimit c) : c.pt ≃ {x : X // f x = g x} where
  toFun p := ⟨c.ι p, ConcreteCategory.congr_hom c.condition p⟩
  invFun y := (Fork.IsLimit.lift' hc (↾(fun _ : PUnit.{v + 1} => y.1)) (by ext _; exact y.2)).1
    PUnit.unit
  left_inv p := by
    dsimp only
    refine ConcreteCategory.congr_hom (Fork.IsLimit.hom_ext hc
      (l := ↾(fun _ : PUnit.{v + 1} => p)) ?_) PUnit.unit
    exact (Fork.IsLimit.lift' hc (↾(fun _ : PUnit.{v + 1} => c.ι p))
      (by ext _; exact ConcreteCategory.congr_hom c.condition p)).2
  right_inv y := Subtype.ext (by
    dsimp only
    exact ConcreteCategory.congr_hom (Fork.IsLimit.lift' hc
      (↾(fun _ : PUnit.{v + 1} => y.1)) (by ext _; exact y.2)).2 PUnit.unit)

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} {A : Type w} [Category.{w'} A]

/-! ### The fork of Stacks 03M8 at the terminal object -/

/-- **Stacks 03M8 on global sections.**  Let `U` be an étale scheme chart of the algebraic space
`X` whose structure morphism is surjective on points, and let `R` be an étale scheme chart with
two morphisms `t, s : R ⟶ U` whose comparison images exhibit `R` as the fibre product `U ×_X U`.
Then for every sheaf `P` on the spaces-étale site of `X`, with values in an arbitrary category,

`P(X) → P(U) ⇉ P(R)`

is an equalizer diagram: the first arrow is restriction along the unique morphism `U ⟶ X` of the
site and the two parallel arrows are restriction along `t` and along `s`.

The terminal object of the spaces-étale site is `X` itself, so the first term is the global
sections of `P`; see
`AlgebraicGeometry.Space.sectionsEquivEqualizerOfEtalePresentation` for that reading at the
universe of the structure rings.  The covering used is the one-element family `{U ⟶ X}`, whose
covering condition is surjectivity on points of the structure morphism of `U` by
`AlgebraicGeometry.Space.SpacesEtale.toSpaces_map_from_idObj`, and the fibre product of that
morphism with itself is the hypothesis `hR`; so this is
`AlgebraicGeometry.Space.isLimitForkOfSurjectiveSingleton` with nothing added. -/
noncomputable def isLimitForkIdObj (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    IsLimit (Fork.ofι (P.map ((SpacesEtale.isTerminal_idObj B S hS X).from
      ((comparisonFunctor B S hS X).obj U)).op)
      (Presheaf.fork_condition_of_isPullback P hR)) := by
  refine isLimitForkOfSurjectiveSingleton B S hS P hP ?_ hR _
  rw [SpacesEtale.toSpaces_map_from_idObj]
  exact hU

/-! ### Global sections as the equalizer, elementwise -/

/-- **Stacks 03M8 on global sections, as a bijection.**  In the situation of
`AlgebraicGeometry.Space.isLimitForkIdObj`, for a sheaf `P` of sets at the universe of the
structure rings the type of sections of the underlying presheaf — the limit over the whole
spaces-étale site, that is the global sections — is in bijection with the subtype of the
sections over the chart `U` on which restriction along `t` and restriction along `s` agree:

`Γ(X, P) ≃ {x : P(U) // t^*x = s^*x}`.

This is the shape in which
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation` consumes the
equalizer presentation of the final sentence of the proof of Stacks 07SI.  It is assembled from
`CategoryTheory.Functor.sectionsEquivObjOfIsInitial`, the terminal object of the site being `X`
itself, and `CategoryTheory.Limits.Fork.IsLimit.ptEquivSubtype` applied to the fork. -/
noncomputable def sectionsEquivEqualizerOfEtalePresentation
    (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type u)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    P.sections ≃ {x : P.obj (op ((comparisonFunctor B S hS X).obj U)) //
      P.map ((comparisonFunctor B S hS X).map t).op x =
        P.map ((comparisonFunctor B S hS X).map s).op x} :=
  (P.sectionsEquivObjOfIsInitial
      (initialOpOfTerminal (SpacesEtale.isTerminal_idObj B S hS X))).trans
    (Fork.IsLimit.ptEquivSubtype (isLimitForkIdObj B S hS P hP hU hR))

/-! ### Restriction to the étale scheme charts -/

/-- **Restriction along a surjective morphism of the spaces-étale site is injective on
sections.**  For a sheaf of sets `P` on the spaces-étale site of `X` and a morphism `g : Z ⟶ W`
of that site which is surjective on points, restriction of sections along `g` is injective.

The one-element family `{g}` is a covering by
`AlgebraicGeometry.Space.SpacesEtale.isCovering_singleton_of_isSurjective`, so restriction along
`g` is the arrow of a limiting fork
(`AlgebraicGeometry.Space.isLimitForkOfSurjectiveSingleton`, with the chosen fibre product of
`g` with itself), and the arrow of a limiting fork in `Type u` is injective by
`CategoryTheory.Limits.Fork.IsLimit.ptEquivSubtype`. -/
theorem injective_map_op_of_isSurjective (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type t)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {W Z : SpacesEtale B S hS X} (g : Z ⟶ W)
    (hg : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map g).hom) :
    Function.Injective (P.map g.op) := by
  intro a b hab
  have hpb : IsPullback (pullback.fst g g) (pullback.snd g g) g g := IsPullback.of_hasPullback g g
  have hfork := isLimitForkOfSurjectiveSingleton B S hS P hP hg hpb
    (Presheaf.fork_condition_of_isPullback P hpb)
  exact (Fork.IsLimit.ptEquivSubtype hfork).injective (Subtype.ext hab)

/-- **Restriction of a global section to the étale scheme charts.**  A section of a presheaf `P`
on the spaces-étale site of `X` over the terminal object `X` restricts, along the unique
morphism of the site out of each étale scheme chart, to a compatible family of sections over the
charts — that is, to a section of the restriction of `P` along the comparison functor of
Stacks 03G1.

Compatibility is the fact that any two morphisms of the site into the terminal object agree. -/
noncomputable def restrictSectionsToCharts (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type t)
    (x : P.obj (op (SpacesEtale.idObj B S hS X))) :
    ((comparisonFunctor B S hS X).op ⋙ P).sections :=
  ⟨fun V => P.map ((SpacesEtale.isTerminal_idObj B S hS X).from
    ((comparisonFunctor B S hS X).obj V.unop)).op x, by
      intro V₁ V₂ f
      dsimp only [Functor.comp_map, Functor.op_map]
      rw [← Functor.map_comp_apply, ← op_comp,
        (SpacesEtale.isTerminal_idObj B S hS X).hom_ext
          ((comparisonFunctor B S hS X).map f.unop ≫
            (SpacesEtale.isTerminal_idObj B S hS X).from
              ((comparisonFunctor B S hS X).obj V₁.unop))
          ((SpacesEtale.isTerminal_idObj B S hS X).from
            ((comparisonFunctor B S hS X).obj V₂.unop))]⟩

/-- **A sheaf on the spaces-étale site has the same global sections as its restriction to the
étale scheme charts.**  If `X` admits an étale scheme chart `U` whose structure morphism is
surjective on points — which every algebraic space does, by Stacks 03H6 — then for every sheaf
of sets `P` on the spaces-étale site of `X` at the universe of the structure rings, restriction
to the charts is a bijection from the sections of `P` over the terminal object `X` onto the
sections of the restriction of `P` along the comparison functor of Stacks 03G1.

This is the step from the spaces-étale site to the small étale site, and it is **not** formal:
it is not an instance of `CategoryTheory.Functor.bijective_sectionsPrecomp`, which would ask the
opposite of the comparison functor to be initial, that is every object of the spaces-étale site
to admit a morphism *to* an étale scheme chart, and `X` itself does not.  The sheaf condition is
what makes it true, and it enters twice.

*Injectivity* is restriction to the single chart `U`, which is injective by
`AlgebraicGeometry.Space.injective_map_op_of_isSurjective`.

*Surjectivity.*  A compatible family over the charts has a value at `U` which the two
projections of `R = U ×_X U` (produced by `AlgebraicGeometry.Space.exists_relationChart`) carry
to the same section of `R`, so `AlgebraicGeometry.Space.isLimitForkIdObj` amalgamates it to a
section `x` over `X`.  That `x` restricts to the given family at *every* chart `V` is checked
after restricting further to an étale scheme chart `V'` of the product `V ×_X U` in the site:
both restrictions along the two projections `V' ⟶ V` and `V' ⟶ U` — which are morphisms of the
small étale site because the comparison functor is full,
`AlgebraicGeometry.Space.comparisonFunctor_full` — agree with the family's value at `V'`, and
restriction along `V ×_X U ⟶ V` and along `V' ⟶ V ×_X U` are both injective, the first by
Stacks 03MH (`AlgebraicGeometry.Space.isSurjective_of_isPullback_isTerminal`) and the second
because a chart covering of an object of the site is surjective
(`AlgebraicGeometry.Space.exists_etaleChart_singleton_covering`). -/
theorem bijective_restrictSectionsToCharts (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type t)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) :
    Function.Bijective (restrictSectionsToCharts B S hS P) := by
  have hsurjU : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map
      ((SpacesEtale.isTerminal_idObj B S hS X).from
        ((comparisonFunctor B S hS X).obj U))).hom := by
    rwa [SpacesEtale.toSpaces_map_from_idObj]
  constructor
  · intro a b hab
    exact injective_map_op_of_isSurjective B S hS P hP _ hsurjU
      (congrFun (congrArg Subtype.val hab) (op U))
  · intro t
    have hterm : ∀ {Y Z : SpacesEtale B S hS X} (g : Z ⟶ Y)
        (y : P.obj (op (SpacesEtale.idObj B S hS X))),
        P.map g.op (P.map ((SpacesEtale.isTerminal_idObj B S hS X).from Y).op y) =
          P.map ((SpacesEtale.isTerminal_idObj B S hS X).from Z).op y := by
      intro Y Z g y
      rw [← Functor.map_comp_apply, ← op_comp,
        (SpacesEtale.isTerminal_idObj B S hS X).hom_ext (g ≫ _) _]
    obtain ⟨R, τ, σ, hR⟩ := exists_relationChart B S hS U
    have hw : P.map ((comparisonFunctor B S hS X).map τ).op (t.val (op U)) =
        P.map ((comparisonFunctor B S hS X).map σ).op (t.val (op U)) :=
      (t.property τ.op).trans (t.property σ.op).symm
    set x := (Fork.IsLimit.ptEquivSubtype (isLimitForkIdObj B S hS P hP hU hR)).symm
      ⟨t.val (op U), hw⟩
    have hx : P.map ((SpacesEtale.isTerminal_idObj B S hS X).from
        ((comparisonFunctor B S hS X).obj U)).op x = t.val (op U) :=
      congrArg Subtype.val ((Fork.IsLimit.ptEquivSubtype
        (isLimitForkIdObj B S hS P hP hU hR)).apply_symm_apply ⟨t.val (op U), hw⟩)
    refine ⟨x, Subtype.ext (funext fun V => ?_)⟩
    obtain ⟨V⟩ := V
    dsimp only [restrictSectionsToCharts]
    have := comparisonFunctor_full B S hS X
    set cV := (comparisonFunctor B S hS X).obj V
    set cU := (comparisonFunctor B S hS X).obj U
    have hZpb : IsPullback (prod.fst : cV ⨯ cU ⟶ cV) (prod.snd : cV ⨯ cU ⟶ cU)
        ((SpacesEtale.isTerminal_idObj B S hS X).from cV)
        ((SpacesEtale.isTerminal_idObj B S hS X).from cU) :=
      IsPullback.of_isLimit_binaryFan_of_isTerminal (prodIsProd cV cU)
        (SpacesEtale.isTerminal_idObj B S hS X)
    obtain ⟨V', f, hfEt, hfSurj, hfCov⟩ :=
      exists_etaleChart_singleton_covering B S hS X (cV ⨯ cU)
    obtain ⟨p, hp⟩ := (comparisonFunctor B S hS X).map_surjective
      (f ≫ (prod.fst : cV ⨯ cU ⟶ cV))
    obtain ⟨q, hq⟩ := (comparisonFunctor B S hS X).map_surjective
      (f ≫ (prod.snd : cV ⨯ cU ⟶ cU))
    have hcollapse : ∀ Z : P.obj (op cV),
        P.map f.op (P.map (prod.fst : cV ⨯ cU ⟶ cV).op Z) =
          P.map ((comparisonFunctor B S hS X).map p).op Z := by
      intro Z
      rw [← Functor.map_comp_apply, ← op_comp, ← hp]
    refine injective_map_op_of_isSurjective B S hS P hP (prod.fst : cV ⨯ cU ⟶ cV)
      (isSurjective_of_isPullback_isTerminal B S hS hU hZpb)
      (injective_map_op_of_isSurjective B S hS P hP f hfSurj ?_)
    rw [hcollapse, hcollapse]
    rw [hterm, ← hterm ((comparisonFunctor B S hS X).map q), hx]
    exact (t.property q.op).trans (t.property p.op).symm

/-! ### Global sections over the charts as the equalizer -/

/-- **Global sections of a sheaf on the spaces-étale site, read on the étale scheme charts.**
The sections of the restriction of a sheaf `P` along the comparison functor of Stacks 03G1 — the
global sections of `P` computed over the *small* étale site — are the sections of `P` over the
terminal object `X` of the spaces-étale site.

This is `AlgebraicGeometry.Space.bijective_restrictSectionsToCharts` as a bijection. -/
noncomputable def equivSectionsComparison (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type t)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) :
    P.obj (op (SpacesEtale.idObj B S hS X)) ≃
      ((comparisonFunctor B S hS X).op ⋙ P).sections :=
  Equiv.ofBijective _ (bijective_restrictSectionsToCharts B S hS P hP hU)

/-- **Stacks 03M8 on the global sections computed over the small étale site.**  Let `U` be an
étale scheme chart of `X` whose structure morphism is surjective on points and let `R` be an
étale scheme chart with two morphisms `t, s : R ⟶ U` exhibiting it as `U ×_X U`.  Then for every
sheaf of sets `P` on the spaces-étale site of `X` at the universe of the structure rings, the
sections of the restriction of `P` to the small étale site — the global sections, computed as the
limit over the étale scheme charts — are in bijection with the subtype of the sections over `U`
on which restriction along `t` and restriction along `s` agree:

`Γ(X, ℱ) ≃ {x : ℱ(U) // t^*x = s^*x}`.

This is the equalizer presentation of the final sentence of the proof of Stacks 07SI, in the
shape `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation`
consumes it, with the global sections taken over the small étale site — the site on which an
`𝒪`-module of Stacks 03LU lives.  It is
`AlgebraicGeometry.Space.equivSectionsComparison` followed by
`AlgebraicGeometry.Space.sectionsEquivEqualizerOfEtalePresentation`.

What is still needed to read it on an `𝒪`-module `M` itself, rather than on a sheaf presented as
a restriction from the spaces-étale site, is the transport along the comparison equivalence of
Stacks 03G1 (`AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`): its counit
identifies the restriction of the extension of the sheaf of sets underlying `M` with that sheaf
of sets, and a bijection of sections transports along an isomorphism of functors to types.  That
transport is not carried out here. -/
noncomputable def sectionsComparisonEquivEqualizer (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type u)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) P)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    ((comparisonFunctor B S hS X).op ⋙ P).sections ≃
      {x : P.obj (op ((comparisonFunctor B S hS X).obj U)) //
        P.map ((comparisonFunctor B S hS X).map t).op x =
          P.map ((comparisonFunctor B S hS X).map s).op x} :=
  (equivSectionsComparison B S hS P hP hU).symm.trans
    (Fork.IsLimit.ptEquivSubtype (isLimitForkIdObj B S hS P hP hU hR))

end AlgebraicGeometry.Space

end
