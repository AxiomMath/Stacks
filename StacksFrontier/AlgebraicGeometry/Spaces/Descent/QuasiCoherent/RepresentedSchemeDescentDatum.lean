module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionSquare

/-!
# A descent datum of a represented family, read as a descent datum of the underlying schemes

Let `f i : T i ⟶ U` be a family of the big fppf category over a scheme `S`. Its members and its
target represent algebraic spaces, so a descent datum for quasi-coherent modules relative to the
represented family makes sense. Reading its pairwise isomorphisms on the underlying schemes gives
a descent datum for `AlgebraicGeometry.modulePullbackPseudofunctor` relative to the family of
underlying morphisms of schemes, restricted along `AlgebraicGeometry.BigFppfOver.toScheme` in the
sense of `CategoryTheory.Pseudofunctor.restrict`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.reprSchemeDatum`: the descent datum for
  `AlgebraicGeometry.modulePullbackPseudofunctor` restricted along
  `AlgebraicGeometry.BigFppfOver.toScheme`, of a descent datum of a represented family.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullHom_zariskiTransitionOn`: the readings of
  the pairwise isomorphisms are invariant under pullback along a morphism of the site, in the
  spelling `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.reprSchemeDatum_obj` and `…_hom`: the components
  of the datum are the modules on the underlying schemes of the component modules of the given
  datum, and its gluing morphisms are the readings of its pairwise isomorphisms.

## Implementation notes

`AlgebraicGeometry.Space.smallEtaleRingedSite` is made locally `implicit_reducible`: the rewrite
in `pullHom_zariskiTransitionOn` crosses the two spellings of the structure ring sheaf of a
representable algebraic space, and `rw` re-checks its motive at a transparency at which they do
not agree.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe v u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Represented

variable {I : Type v} {U : BigFppfOver B S hS} (T : I → BigFppfOver B S hS)
  (f : ∀ i, T i ⟶ U)
variable (D : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f))

section Coherence

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- The readings of the pairwise isomorphisms of a descent datum of a represented family are
invariant under pullback along a morphism of the site, in the spelling
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`. -/
public theorem pullHom_zariskiTransitionOn {Y Z : BigFppfOver B S hS} {q : Y ⟶ U} {i j : I}
    (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) (m : Z ⟶ Y)
    {a₁ : Z ⟶ T i} (ha₁ : m ≫ a = a₁) {b₁ : Z ⟶ T j} (hb₁ : m ≫ b = b₁)
    {q₁ : Z ⟶ U} (ha₁' : a₁ ≫ f i = q₁) (hb₁' : b₁ ≫ f j = q₁) :
    pullHom (F := modulePullbackPseudofunctor)
        (zariskiTransitionOn B S hS T f D a b ha hb).hom
        ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map a₁)
        ((BigFppfOver.toScheme B S hS).map b₁)
        (by subst ha₁; rfl) (by subst hb₁; rfl) =
      (zariskiTransitionOn B S hS T f D a₁ b₁ ha₁' hb₁').hom := by
  subst ha₁ hb₁
  have step :
      (Scheme.Modules.pullbackComp
            (SmallEtale.schemeHom (associatedBigEtaleSite B) m.left)
            (SmallEtale.schemeHom (associatedBigEtaleSite B) a.left)).inv.app
          (representedZariskiModule B S hS (T i) (D.F i)) ≫
        (Scheme.Modules.pullback
            (SmallEtale.schemeHom (associatedBigEtaleSite B) m.left)).map
          (zariskiTransitionOn B S hS T f D a b ha hb).hom ≫
          (Scheme.Modules.pullbackComp
              (SmallEtale.schemeHom (associatedBigEtaleSite B) m.left)
              (SmallEtale.schemeHom (associatedBigEtaleSite B) b.left)).hom.app
            (representedZariskiModule B S hS (T j) (D.F j)) =
        (zariskiTransitionOn B S hS T f D (m ≫ a) (m ≫ b) ha₁' hb₁').hom := by
    rw [zariskiTransitionOn_pullbackComp B S hS T f D m a b ha hb ha₁' hb₁',
      Iso.inv_hom_id_app_assoc]
  exact step

end Coherence

/-- The descent datum of the underlying schemes of a descent datum of a represented family, for
`AlgebraicGeometry.modulePullbackPseudofunctor` restricted along
`AlgebraicGeometry.BigFppfOver.toScheme`. Its components are the modules on the schemes
underlying the members, and its gluing morphisms over an object `Y` mapping to two members are
the readings `AlgebraicGeometry.Space.QuasiCoherentDescent.zariskiTransitionOn` of the pairwise
isomorphisms. -/
public def reprSchemeDatum :
    (modulePullbackPseudofunctor.restrict (BigFppfOver.toScheme B S hS)).DescentData f where
  obj i := representedZariskiModule B S hS (T i) (D.F i)
  hom _ _ _ _ a b ha hb := (zariskiTransitionOn B S hS T f D a b ha hb).hom
  pullHom_hom _ _ m _ _ _ _ _ a b ha hb a₁ b₁ ha₁ hb₁ :=
    (Pseudofunctor.restrict_pullHom modulePullbackPseudofunctor
        (BigFppfOver.toScheme B S hS) _ m a₁ b₁ ha₁ hb₁).trans
      (pullHom_zariskiTransitionOn B S hS T f D a b ha hb m ha₁ hb₁ _ _)
  hom_self _ _ _ a ha := congrArg Iso.hom (zariskiTransitionOn_self B S hS T f D a ha)
  hom_comp _ _ _ _ _ a b c ha hb hc :=
    congrArg Iso.hom (zariskiTransitionOn_comp B S hS T f D a b c ha hb hc)

/-- The components of the transported datum are the modules on the underlying schemes of the
component modules of the given datum. -/
@[simp]
public theorem reprSchemeDatum_obj (i : I) :
    (reprSchemeDatum B S hS T f D).obj i = representedZariskiModule B S hS (T i) (D.F i) :=
  rfl

/-- The gluing morphisms of the transported datum are the readings of the pairwise isomorphisms
of the given datum. -/
@[simp]
public theorem reprSchemeDatum_hom {Y : BigFppfOver B S hS} (q : Y ⟶ U) {i j : I}
    (a : Y ⟶ T i) (b : Y ⟶ T j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (reprSchemeDatum B S hS T f D).hom q a b ha hb =
      (zariskiTransitionOn B S hS T f D a b ha hb).hom :=
  rfl

end Represented

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
