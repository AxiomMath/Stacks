module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleGlobalSectionsFork

/-!
# Global sections of a module on the small étale site as an equalizer over a chart

`AlgebraicGeometry.Space.sectionsComparisonEquivEqualizer` reads the equalizer presentation of
Stacks 03M8 on the sections of a sheaf which is *presented* as a restriction along the
comparison functor of Stacks 03G1.  An `𝒪`-module of Stacks 03LU is not presented that way: it
is a sheaf on the small étale site of the algebraic space, full stop.  This file supplies the
transport that closes that gap and states the presentation for a module.

## Main definitions

* `CategoryTheory.Functor.sectionsEquivOfIso` transports the sections of a functor to types
  along an isomorphism of functors.
* `CategoryTheory.Functor.equalizerSubtypeEquivOfIso` transports, along the same isomorphism,
  the subtype of an object on which two parallel arrows of the functor agree.
* `AlgebraicGeometry.Space.smallEtaleSectionsEquivEqualizer` is Stacks 03M8 for a sheaf of sets
  on the small étale site of an algebraic space: its global sections are the sections over an
  étale scheme chart `U` equalized by the two projections of `U ×_X U`.
* `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer` is the same statement for the sheaf of
  sets underlying an `𝒪`-module, which is the module-level reading of Stacks 03M8.

## Implementation notes

The two transports are purely formal and independent of each other: the composite
`Γ(G) ≃ Γ(c^*P) ≃ {x : P(U) // t^*x = s^*x} ≃ {y : G(U) // t^*y = s^*y}` uses the first on the
left and the second on the right, and no compatibility between them is needed.  The first
applies the components of the isomorphism index by index; the second is `Equiv.subtypeEquiv` on
the component at the source of the two arrows, the predicate being carried across by naturality
and injectivity of the component at their target.

The sheaf `P` on the spaces-étale site which restricts to the given `G` is produced by the
inverse of the comparison equivalence of Stacks 03G1
(`AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`) and the isomorphism is the counit
of that equivalence; nothing else about `P` is used, so no choice is made beyond the equivalence
itself.

The existence of the chart `U` with surjective structure morphism and of the relation chart `R`
is not assumed away: both are hypotheses here, in the shape in which
`AlgebraicGeometry.Space.exists_relationChart` and Stacks 03H6 produce them, so that a consumer
which has already produced a particular presentation can use its own.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v' w u

namespace CategoryTheory.Functor

variable {J : Type v} [Category.{v'} J] {F G : J ⥤ Type w}

/-- **The sections of a functor to types transport along an isomorphism of functors.**  A
section of `F` is carried to a section of `G` by applying the component of the isomorphism at
each index; compatibility is naturality.

The two inverse properties are the inverse properties of the components, read as bijections of
types through `CategoryTheory.Iso.toEquiv`. -/
def sectionsEquivOfIso (e : F ≅ G) : F.sections ≃ G.sections where
  toFun s := ⟨fun j => e.hom.app j (s.val j), fun {j j'} f => by
    simp [← NatTrans.naturality_apply, s.property f]⟩
  invFun t := ⟨fun j => e.inv.app j (t.val j), fun {j j'} f => by
    simp [← NatTrans.naturality_apply, t.property f]⟩
  left_inv s := Subtype.ext (funext fun j => (e.app j).toEquiv.symm_apply_apply (s.val j))
  right_inv t := Subtype.ext (funext fun j => (e.app j).toEquiv.apply_symm_apply (t.val j))

/-- The component at `j` of the image of a section `s` under `sectionsEquivOfIso e` is the
component of `e` at `j` applied to the component of `s` at `j`. -/
@[simp]
lemma sectionsEquivOfIso_apply_val (e : F ≅ G) (s : F.sections) (j : J) :
    (sectionsEquivOfIso e s).val j = e.hom.app j (s.val j) :=
  rfl

/-- **The subtype on which two parallel arrows of a functor to types agree transports along an
isomorphism of functors.**  For `f g : a ⟶ b` in the index category, the component of the
isomorphism at `a` carries the elements of `F.obj a` equalized by `F.map f` and `F.map g` onto
those of `G.obj a` equalized by `G.map f` and `G.map g`.

The predicate is carried across by naturality together with injectivity of the component at
`b`.  Together with `CategoryTheory.Functor.sectionsEquivOfIso` this transports an equalizer
presentation of the sections of `F` to one of the sections of `G`. -/
def equalizerSubtypeEquivOfIso (e : F ≅ G) {a b : J} (f g : a ⟶ b) :
    {x : F.obj a // F.map f x = F.map g x} ≃ {y : G.obj a // G.map f y = G.map g y} :=
  Equiv.subtypeEquiv (e.app a).toEquiv fun x => by
    rw [show (e.app a).toEquiv x = e.hom.app a x from rfl, ← NatTrans.naturality_apply,
      ← NatTrans.naturality_apply]
    exact ((e.app b).toEquiv.apply_eq_iff_eq).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}

/-- **Stacks 03M8 for a sheaf of sets on the small étale site.**  Let `X` be an algebraic space,
let `U` be an étale scheme chart of `X` whose structure morphism is surjective on points, and
let `R` be an étale scheme chart with two morphisms `t, s : R ⟶ U` whose comparison images
exhibit `R` as the fibre product `U ×_X U`.  Then for every sheaf of sets `G` on the **small**
étale site of `X` at the universe of the structure rings, the global sections of `G` — the
sections of the underlying presheaf, that is the limit over the small étale site — are in
bijection with the subtype of the sections over `U` on which restriction along `t` and
restriction along `s` agree:

`Γ(X, G) ≃ {y : G(U) // t^*y = s^*y}`.

Unlike `AlgebraicGeometry.Space.sectionsComparisonEquivEqualizer`, nothing here presents `G` as
a restriction from the spaces-étale site.  The sheaf `P` on the spaces-étale site which does
restrict to `G` is produced by the inverse of the comparison equivalence of Stacks 03G1, and the
identification of its restriction with `G` is the counit of that equivalence; the presentation
for `P` is then transported along that isomorphism by
`CategoryTheory.Functor.sectionsEquivOfIso` on the left and
`CategoryTheory.Functor.equalizerSubtypeEquivOfIso` on the right. -/
noncomputable def smallEtaleSectionsEquivEqualizer
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    G.obj.sections ≃
      {y : G.obj.obj (op U) // G.obj.map t.op y = G.obj.map s.op y} :=
  let P := (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G
  let e : (comparisonFunctor B S hS X).op ⋙ P.obj ≅ G.obj :=
    (sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u)).mapIso
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.app G)
  ((Functor.sectionsEquivOfIso e).symm.trans
      (sectionsComparisonEquivEqualizer B S hS P.obj P.property hU hR)).trans
    (Functor.equalizerSubtypeEquivOfIso e t.op s.op)

/-- **Stacks 03M8 on the global sections of an `𝒪`-module.**  In the situation of
`AlgebraicGeometry.Space.smallEtaleSectionsEquivEqualizer`, for an `𝒪_X`-module `M` of
Stacks 03LU with sections in the universe of the structure rings, the global sections of the
sheaf of sets underlying `M` are in bijection with the subtype of the sections over the chart
`U` on which restriction along `t` and restriction along `s` agree.

This is the module-level reading of the equalizer presentation used in the final sentence of the
proof of Stacks 07SI, in the shape
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation` consumes
it. -/
noncomputable def moduleSectionsEquivEqualizer (M : Modules.{u, u} B S hS X.1 X.2)
    {U R : SmallEtale B S hS X.1} (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U))) :
    (Sheaf.moduleSheaf.{u, u, u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        M).obj.sections ≃
      {y : (Sheaf.moduleSheaf.{u, u, u + 1}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
          M).obj.obj (op U) //
        (Sheaf.moduleSheaf.{u, u, u + 1}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
            M).obj.map t.op y =
          (Sheaf.moduleSheaf.{u, u, u + 1}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
            M).obj.map s.op y} :=
  smallEtaleSectionsEquivEqualizer B S hS _ hU hR

end AlgebraicGeometry.Space

end
