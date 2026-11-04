module

public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonCoalgebra

/-!
# The single-morphism comparison of descent data with coalgebras, on objects

`StacksFrontier.CategoryTheory.Sites.Descent.SingletonCoalgebra` settles the comparison of
`CategoryTheory.Pseudofunctor.DescentData` with Eilenberg–Moore coalgebras **on morphisms**, for
a one-element family.  This file does the corresponding work **on objects**, which is what the
effectivity half of a descent statement needs.

Fix `f : X ⟶ S`, a chosen pullback `sq` of `f` with itself with projections `p₁, p₂`, and right
adjoints `f^* ⊣ f_*` and `p₁^* ⊣ (p₁)_*`.  A descent datum `D` for the one-element family `f`
has, over `sq`, a transition isomorphism `θ : p₁^* A ⟶ p₂^* A` of its component `A`; a coalgebra
structure on `A` for the comonad `f^* f_*` is a morphism `a : A ⟶ f^* f_* A`.  The two are
exchanged by transposing along `p₁^* ⊣ (p₁)_*` and the base-change morphism
`CategoryTheory.Pseudofunctor.descentBaseChange`.

* The compatibility of a morphism `e : f^* M ⟶ A` with the transition morphisms over **one**
  chosen pullback already gives an isomorphism of descent data: the compatibility over an
  arbitrary object mapping to `X` twice over `S` follows, by pulling the single square back
  along the lift.  This is the object-level analogue of
  `CategoryTheory.Pseudofunctor.descentComparison_comm_of_comm`, and it is unconditional.
* A morphism of coalgebras satisfies that single-square compatibility.  No hypothesis on the
  base-change morphism is needed for this direction, because the equation is obtained by
  transposing, and transposition along an adjunction is a bijection.
* **The counit axiom of the induced coalgebra structure holds.**  Pulling the transposed
  description of `θ` back along the diagonal `X ⟶ sq.pullback` turns `D.hom_self` — the
  statement that the transition over a *single* map is the identity — into `a ≫ ε = 𝟙`.

* **The coassociativity axiom holds as well.**  It is first reduced to
  `CategoryTheory.Pseudofunctor.DescentDataCoassoc`, a single equation over `sq` alone saying
  that the transition morphism is compatible with the structure map, and that equation is then
  proved from the datum's cocycle condition `D.hom_comp` over a *threefold* fibre product of `f`
  — which is presented here as a chosen pullback `sq'` of `p₁` with itself, so that the second
  base-change morphism needed is again an instance of
  `CategoryTheory.Pseudofunctor.descentBaseChange`.

Consequently `CategoryTheory.Pseudofunctor.essImage_toDescentData` is unconditional in the
descent datum: a one-element family whose base-change morphisms are invertible and whose
Eilenberg–Moore comparison functor is essentially surjective has effective descent.

## Main definitions

* `CategoryTheory.Pseudofunctor.descentCoalgebraMap`: the coalgebra structure map that a descent
  datum for a one-element family induces on its component, when the base-change morphism is an
  isomorphism there.
* `CategoryTheory.Pseudofunctor.descentDataIsoOfCoalgebraIso`: the isomorphism of descent data
  that an isomorphism of coalgebras produces.
* `CategoryTheory.Pseudofunctor.IsTransposeOf`: the correspondence between a coalgebra structure
  map on the component and a transition morphism over the chosen pullback.
* `CategoryTheory.Pseudofunctor.DescentDataCoassoc`: the equation, over the chosen pullback
  alone, from which coassociativity of that structure map follows.
* `CategoryTheory.Pseudofunctor.descentDoubleBaseChange`: the composite of the two base-change
  morphisms attached to `sq` and to a chosen pullback `sq'` of `p₁` with itself, through which
  the coassociativity equation is transposed onto the threefold fibre product.

## Main results

* `CategoryTheory.Pseudofunctor.descentDataIsoOfDescentSquareApp_comm` and its one-element form
  `…_of_unique`: compatibility over the chosen pullback identifies a descent datum with a
  canonical one, so `CategoryTheory.Pseudofunctor.essImage_toDescentData_of_coalgebraIso` puts it
  in the essential image of `CategoryTheory.Pseudofunctor.toDescentData`.
* `CategoryTheory.Pseudofunctor.descentSquareApp_comm_of_coalgebraHom`: a morphism of coalgebras
  satisfies that compatibility.
* `CategoryTheory.Pseudofunctor.unit_comp_map_descentSquareApp_counit` and
  `CategoryTheory.Pseudofunctor.isTransposeOf_iff_descentBaseChange_app_eq`: the transposition
  identity behind the correspondence between structure maps and transition morphisms, and the
  resulting equivalence of the two ways of writing it.
* `CategoryTheory.Pseudofunctor.counit_of_descentData`: the counit axiom, from `hom_self`.
* `CategoryTheory.Pseudofunctor.coassoc_of_descentDataCoassoc`: the coassociativity axiom, from
  `DescentDataCoassoc`.
* `CategoryTheory.Pseudofunctor.counit_descentBaseChange` and
  `CategoryTheory.Pseudofunctor.hom_eq_of_isTransposeOf`: the counit companion of
  `unit_descentBaseChange`, and the transposed description of the transition morphism pulled back
  along an arbitrary lift — the two inputs of the computation over the threefold fibre product.
* `CategoryTheory.Pseudofunctor.descentDataCoassoc_of_isTransposeOf` and
  `CategoryTheory.Pseudofunctor.descentDataCoassoc`: **`DescentDataCoassoc` holds**, from
  `DescentData.hom_comp` over a threefold fibre product.
* `CategoryTheory.Pseudofunctor.essImage_toDescentData_of_descentDataCoassoc` and
  `CategoryTheory.Pseudofunctor.essImage_toDescentData`: **every descent datum for a one-element
  family is effective** — the first over `DescentDataCoassoc`, the second with that equation
  discharged, so over invertible base-change morphisms and essential surjectivity of the
  Eilenberg–Moore comparison functor alone.

## Implementation notes

The transposition computations are all of one shape: compose with the base-change morphism,
transpose along `p₁^* ⊣ (p₁)_*`, and use
`CategoryTheory.Pseudofunctor.unit_descentBaseChange` — the one normalisation that pins the
base-change morphism down on the image of the unit — together with the naturality of the base
change and of the unit.  `unit_comp_map_descentSquareApp_counit` and
`coassoc_of_descentDataCoassoc` are that computation; they differ in which triangle identity
closes it.

`DescentDataCoassoc` is equivalent to coassociativity whenever the base-change morphism is a
monomorphism at `f^* f_* A`, by `coassoc_of_descentDataCoassoc` and the same computation run
backwards, and it is the cocycle condition of the descent datum written over the chosen pullback
instead of over a threefold fibre product.  Deriving it from
`CategoryTheory.Pseudofunctor.DescentData.hom_comp` — the object half of the `TODO` of
`Mathlib/CategoryTheory/Sites/Descent/DescentDataAsCoalgebra.lean`, "compare
`DescentDataAsCoalgebra` with `DescentData` when suitable pullbacks exist and certain base change
morphisms are isomorphisms" — is `descentDataCoassoc_of_isTransposeOf`, and with it the whole of
that comparison, in both directions and for objects as well as for morphisms, is done.

The threefold fibre product is taken to be a chosen pullback `sq'` of `p₁` with itself, not of
`p₂` with `p₁`.  The two present the same object, but only the first makes the base-change
morphism it carries an instance of `descentBaseChange`, which is defined for a chosen pullback of
a morphism with *itself*; the canonical comparison `p₂^* f^* f_* A ≅ p₁^* f^* f_* A` absorbs the
difference, and it is the first factor of `descentDoubleBaseChange`.  No base change along a
general commutative square is therefore needed.

The equation is then proved by composing both of its sides with `descentDoubleBaseChange`, which
is a monomorphism, and transposing along `s₁^* ⊣ (s₁)_*`.  What the two sides become over the
threefold fibre product is read off by `hom_eq_of_isTransposeOf` at the three lifts of the pairs
of projections, and the identity between them is `D.hom_comp`.

Everything in this file is stated for a general pseudofunctor and belongs upstream in Mathlib.
-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Opposite Bicategory Limits Pseudofunctor.LocallyDiscreteOpToCat

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f) {ι : Type t}

/-- **The object-level reduction to one chosen pullback.**  Let `D` be a descent datum for the
constant family `f` and let `e i` identify `f^* M` with its components.  If each `e i` is
compatible with the transition morphisms over **one** chosen pullback of `f` with itself, then
`D` is isomorphic to the canonical descent datum of `M`.

The compatibility that an isomorphism of descent data requires is a condition over *every*
object mapping to `X` twice over `S`; it follows from the single equation over `sq` by pulling
that equation back along the lift, exactly as in
`CategoryTheory.Pseudofunctor.descentComparison_comm_of_comm`. -/
noncomputable def descentDataIsoOfDescentSquareApp_comm
    {M : F.obj (.mk (op S))} {D : F.DescentData (fun _ : ι ↦ f)}
    (e : ∀ i, (F.map f.op.toLoc).toFunctor.obj M ≅ D.obj i)
    (he : ∀ i₁ i₂, (F.map sq.p₁.op.toLoc).toFunctor.map (e i₁).hom ≫
        D.hom (i₁ := i₁) (i₂ := i₂) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ =
      descentSquareApp sq M ≫ (F.map sq.p₂.op.toLoc).toFunctor.map (e i₂).hom) :
    (F.toDescentData (fun _ : ι ↦ f)).obj M ≅ D := by
  refine DescentData.isoMk e ?_
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  change (F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
      D.hom (i₁ := i₁) (i₂ := i₂) q f₁ f₂ hf₁ hf₂ =
    descentComparison M q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (e i₂).hom
  obtain ⟨g, h₁, h₂⟩ := sq.isPullback.exists_lift f₁ f₂ (by rw [hf₁, hf₂])
  have hq : g ≫ sq.p = q := by rw [← sq.hp₁, reassoc_of% h₁, hf₁]
  simp only [descentSquareApp_eq_descentComparison] at he
  rw [← D.pullHom_hom g sq.p q hq sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ f₁ f₂ h₁ h₂,
    ← pullHom_descentComparison M g sq.p q hq sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ f₁ f₂ h₁ h₂]
  dsimp only [pullHom]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc, he i₁ i₂, Functor.map_comp_assoc, mapComp'_inv_naturality]
  simp only [Category.assoc]

/-- `CategoryTheory.Pseudofunctor.descentDataIsoOfDescentSquareApp_comm` for a one-element
family, where a single isomorphism of the component is all that is needed. -/
noncomputable def descentDataIsoOfDescentSquareApp_comm_of_unique [Unique ι]
    {M : F.obj (.mk (op S))} {D : F.DescentData (fun _ : ι ↦ f)}
    (e : (F.map f.op.toLoc).toFunctor.obj M ≅ D.obj default)
    (he : (F.map sq.p₁.op.toLoc).toFunctor.map e.hom ≫
        D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ =
      descentSquareApp sq M ≫ (F.map sq.p₂.op.toLoc).toFunctor.map e.hom) :
    (F.toDescentData (fun _ : ι ↦ f)).obj M ≅ D := by
  refine descentDataIsoOfDescentSquareApp_comm sq
    (fun j ↦ e ≪≫ eqToIso (congrArg D.obj (Subsingleton.elim default j))) ?_
  intro i₁ i₂
  obtain rfl := Subsingleton.elim i₁ (default : ι)
  obtain rfl := Subsingleton.elim i₂ (default : ι)
  simpa using he

/-- Compatibility over one chosen pullback puts a descent datum for a one-element family in the
essential image of `CategoryTheory.Pseudofunctor.toDescentData`. -/
theorem essImage_toDescentData_of_descentSquareApp_comm_of_unique [Unique ι]
    {M : F.obj (.mk (op S))} {D : F.DescentData (fun _ : ι ↦ f)}
    (e : (F.map f.op.toLoc).toFunctor.obj M ≅ D.obj default)
    (he : (F.map sq.p₁.op.toLoc).toFunctor.map e.hom ≫
        D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ =
      descentSquareApp sq M ≫ (F.map sq.p₂.op.toLoc).toFunctor.map e.hom) :
    (F.toDescentData (fun _ : ι ↦ f)).essImage D :=
  ⟨M, ⟨descentDataIsoOfDescentSquareApp_comm_of_unique sq e he⟩⟩

/-- Pulling back a transition morphism whiskered by morphisms of the underlying objects: the
whiskering is unaffected. -/
@[reassoc]
lemma pullHom_map_comp_comp_map ⦃X₁ X₂ : C⦄ {M₁ N₁ : F.obj (.mk (op X₁))}
    {N₂ M₂ : F.obj (.mk (op X₂))} ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ (a : M₁ ⟶ N₁)
    (γ : (F.map f₁.op.toLoc).toFunctor.obj N₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj N₂)
    (b : N₂ ⟶ M₂) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom ((F.map f₁.op.toLoc).toFunctor.map a ≫ γ ≫
        (F.map f₂.op.toLoc).toFunctor.map b) g gf₁ gf₂ hgf₁ hgf₂ =
      (F.map gf₁.op.toLoc).toFunctor.map a ≫ pullHom γ g gf₁ gf₂ hgf₁ hgf₂ ≫
        (F.map gf₂.op.toLoc).toFunctor.map b := by
  dsimp only [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← mapComp'_hom_naturality_assoc, mapComp'_inv_naturality]

/-- `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` is multiplicative: pulling
back a composite is the composite of the pullbacks. -/
@[reassoc]
lemma pullHom_comp ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃M₃ : F.obj (.mk (op X₃))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (α : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (β : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom (α ≫ β) g gf₁ gf₃ hgf₁ hgf₃ =
      pullHom α g gf₁ gf₂ hgf₁ hgf₂ ≫ pullHom β g gf₂ gf₃ hgf₂ hgf₃ := by
  dsimp only [pullHom]
  simp only [Functor.map_comp, Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]

/-- Pulling back an inverse image of a morphism gives the inverse image along the composite. -/
lemma pullHom_map ⦃X₁ : C⦄ ⦃M₁ N₁ : F.obj (.mk (op X₁))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄
    (x : M₁ ⟶ N₁) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) :
    pullHom ((F.map f₁.op.toLoc).toFunctor.map x) g gf₁ gf₁ hgf₁ hgf₁ =
      (F.map gf₁.op.toLoc).toFunctor.map x := by
  dsimp only [pullHom]
  simp only [← Functor.comp_map]
  exact mapComp'_naturality_2 F f₁.op.toLoc g.op.toLoc gf₁.op.toLoc _ x

/-- **The cocycle identity for the canonical comparisons.**  For three morphisms `f₁, f₂, f₃`
from `Y` to `X` over `S`, the comparisons of the inverse images of an object of `F.obj (op S)`
compose.  This is `CategoryTheory.Pseudofunctor.DescentData.hom_comp` for the canonical descent
datum, stated at the iterated pullback. -/
@[reassoc]
lemma descentComparison_comp (M : F.obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S)
    (f₁ f₂ f₃ : Y ⟶ X) (hf₁ : f₁ ≫ f = q) (hf₂ : f₂ ≫ f = q) (hf₃ : f₃ ≫ f = q) :
    descentComparison M q f₁ f₂ hf₁ hf₂ ≫ descentComparison M q f₂ f₃ hf₂ hf₃ =
      descentComparison M q f₁ f₃ hf₁ hf₃ := by
  rw [← ofObj_hom_eq_descentComparison (ι := Unit) M q () (),
    ← ofObj_hom_eq_descentComparison (ι := Unit) M q () (),
    ← ofObj_hom_eq_descentComparison (ι := Unit) M q () ()]
  exact (DescentData.ofObj (f := fun _ : Unit ↦ f) M).hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- The canonical comparison of an inverse image with itself is the identity.  This is
`CategoryTheory.Pseudofunctor.DescentData.hom_self` for the canonical descent datum. -/
@[simp]
lemma descentComparison_self (M : F.obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S)
    (g : Y ⟶ X) (hg : g ≫ f = q) :
    descentComparison M q g g hg hg = 𝟙 _ := by
  rw [← ofObj_hom_eq_descentComparison (ι := Unit) M q () ()]
  exact (DescentData.ofObj (f := fun _ : Unit ↦ f) M).hom_self q g hg

/-- The canonical comparison `p₂^* f^* M ⟶ p₁^* f^* M` is a right inverse of
`CategoryTheory.Pseudofunctor.descentSquareApp`. -/
private lemma descentSquareApp_comp_descentComparison (M : F.obj (.mk (op S))) :
    descentSquareApp sq M ≫ descentComparison M sq.p sq.p₂ sq.p₁ sq.hp₂ sq.hp₁ = 𝟙 _ := by
  rw [descentSquareApp_eq_descentComparison, descentComparison_comp, descentComparison_self]

/-- The canonical comparison `p₂^* f^* M ⟶ p₁^* f^* M` is a left inverse of
`CategoryTheory.Pseudofunctor.descentSquareApp`. -/
private lemma descentComparison_comp_descentSquareApp (M : F.obj (.mk (op S))) :
    descentComparison M sq.p sq.p₂ sq.p₁ sq.hp₂ sq.hp₁ ≫ descentSquareApp sq M = 𝟙 _ := by
  rw [descentSquareApp_eq_descentComparison, descentComparison_comp, descentComparison_self]

section Coalgebra

variable {Rf : F.obj (.mk (op X)) ⥤ F.obj (.mk (op S))}
  (adj : (F.map f.op.toLoc).toFunctor ⊣ Rf)
  {Rp : F.obj (.mk (op sq.pullback)) ⥤ F.obj (.mk (op X))}
  (adjp : (F.map sq.p₁.op.toLoc).toFunctor ⊣ Rp)

/-- **The transposition identity.**  Transposing, along `p₁^* ⊣ (p₁)_*`, the composite of
`p₁^* a` with the canonical comparison of the two pullbacks of `f_* A` and with `p₂^* ε` gives
the composite of `a` with the base-change morphism.

This is the one computation behind the correspondence between coalgebra structure maps on `A` and
transition morphisms `p₁^* A ⟶ p₂^* A`; both directions of that correspondence, and the
coassociativity transfer, are read off from it. -/
lemma unit_comp_map_descentSquareApp_counit {A : F.obj (.mk (op X))}
    (a : A ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj A)) :
    adjp.unit.app A ≫ Rp.map ((F.map sq.p₁.op.toLoc).toFunctor.map a ≫
        descentSquareApp sq (Rf.obj A) ≫
          (F.map sq.p₂.op.toLoc).toFunctor.map (adj.counit.app A)) =
      a ≫ (descentBaseChange sq adj adjp).app A := by
  have hun := adjp.unit.naturality a
  dsimp at hun
  have hnat := (descentBaseChange sq adj adjp).naturality (adj.counit.app A)
  dsimp at hnat
  simp only [Functor.map_comp]
  rw [← reassoc_of% hun, ← reassoc_of% (unit_descentBaseChange sq adj adjp (Rf.obj A)),
    ← hnat, ← Functor.map_comp_assoc, adj.right_triangle_components, Functor.map_id,
    Category.id_comp]

/-- **A transition morphism is the transposition of a structure map.**  For
`a : A ⟶ f^* f_* A` and `θ : p₁^* A ⟶ p₂^* A`, this says that `θ` is the composite of `p₁^* a`
with the canonical comparison of the two pullbacks of `f_* A` and with `p₂^* ε`.

By `CategoryTheory.Pseudofunctor.isTransposeOf_iff_descentBaseChange_app_eq` this is equivalent
to the equation that `a` and `θ` correspond under transposition along `p₁^* ⊣ (p₁)_*` and the
base-change morphism.  It is stated in this form because it mentions neither the base-change
morphism nor `CategoryTheory.mateEquiv`, which is what makes it usable in the statements of the
geometric applications. -/
def IsTransposeOf {A : F.obj (.mk (op X))}
    (a : A ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj A))
    (θ : (F.map sq.p₁.op.toLoc).toFunctor.obj A ⟶
      (F.map sq.p₂.op.toLoc).toFunctor.obj A) : Prop :=
  (F.map sq.p₁.op.toLoc).toFunctor.map a ≫ descentSquareApp sq (Rf.obj A) ≫
    (F.map sq.p₂.op.toLoc).toFunctor.map (adj.counit.app A) = θ

/-- `CategoryTheory.Pseudofunctor.IsTransposeOf` is the transposition, along `p₁^* ⊣ (p₁)_*` and
the base-change morphism, of the equation relating a structure map to a transition morphism. -/
lemma isTransposeOf_iff_descentBaseChange_app_eq {A : F.obj (.mk (op X))}
    {a : A ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj A)}
    {θ : (F.map sq.p₁.op.toLoc).toFunctor.obj A ⟶
      (F.map sq.p₂.op.toLoc).toFunctor.obj A} :
    IsTransposeOf sq adj a θ ↔
      a ≫ (descentBaseChange sq adj adjp).app A = adjp.unit.app A ≫ Rp.map θ := by
  rw [IsTransposeOf, ← (adjp.homEquiv _ _).apply_eq_iff_eq, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, unit_comp_map_descentSquareApp_counit]

include adjp in
/-- **A morphism of coalgebras is compatible with the transition morphisms.**  Let
`a : A ⟶ f^* f_* A` correspond to `θ : p₁^* A ⟶ p₂^* A` under transposition along
`p₁^* ⊣ (p₁)_*` and the base-change morphism, which is the hypothesis `ha`.  Then a morphism
`e : f^* M ⟶ A` satisfying the Eilenberg–Moore coalgebra condition satisfies the compatibility
over the chosen pullback that
`CategoryTheory.Pseudofunctor.essImage_toDescentData_of_descentSquareApp_comm` consumes.

No hypothesis on the base-change morphism is needed: the conclusion is obtained by transposing,
and transposition along an adjunction is a bijection. -/
lemma descentSquareApp_comm_of_coalgebraHom {M : F.obj (.mk (op S))} {A : F.obj (.mk (op X))}
    {θ : (F.map sq.p₁.op.toLoc).toFunctor.obj A ⟶ (F.map sq.p₂.op.toLoc).toFunctor.obj A}
    {a : A ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj A)}
    (ha : IsTransposeOf sq adj a θ)
    (e : (F.map f.op.toLoc).toFunctor.obj M ⟶ A)
    (he : (F.map f.op.toLoc).toFunctor.map (adj.unit.app M) ≫
        (F.map f.op.toLoc).toFunctor.map (Rf.map e) = e ≫ a) :
    (F.map sq.p₁.op.toLoc).toFunctor.map e ≫ θ =
      descentSquareApp sq M ≫ (F.map sq.p₂.op.toLoc).toFunctor.map e := by
  replace ha := (isTransposeOf_iff_descentBaseChange_app_eq sq adj adjp).1 ha
  have hnat := (descentBaseChange sq adj adjp).naturality e
  dsimp at hnat
  have hun := adjp.unit.naturality e
  dsimp at hun
  have hL : adjp.unit.app ((F.map f.op.toLoc).toFunctor.obj M) ≫
        Rp.map ((F.map sq.p₁.op.toLoc).toFunctor.map e) ≫ Rp.map θ =
      e ≫ a ≫ (descentBaseChange sq adj adjp).app A := by
    conv_lhs => rw [← Category.assoc, ← hun, Category.assoc, ← ha]
  have hR : adjp.unit.app ((F.map f.op.toLoc).toFunctor.obj M) ≫
        Rp.map (descentSquareApp sq M) ≫ Rp.map ((F.map sq.p₂.op.toLoc).toFunctor.map e) =
      e ≫ a ≫ (descentBaseChange sq adj adjp).app A := by
    conv_lhs => rw [← Category.assoc, ← unit_descentBaseChange sq adj adjp M, Category.assoc,
      ← hnat, ← Category.assoc, he, Category.assoc]
  rw [← (adjp.homEquiv _ _).apply_eq_iff_eq, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp, hL, hR]

include adjp in
/-- **Effectivity of a descent datum for a one-element family, from an isomorphism of
coalgebras.**  If the component of `D` carries a morphism `a` corresponding to the transition
morphism of `D` over the chosen pullback, and if `a` is isomorphic, as a coalgebra structure, to
the canonical one on `f^* M`, then `D` is isomorphic to the canonical descent datum of `M`.

No axiom of `a` and no hypothesis on the base-change morphism enters: they are what produce the
isomorphism, not what the isomorphism is used through. -/
noncomputable def descentDataIsoOfCoalgebraIso [Unique ι]
    {D : F.DescentData (fun _ : ι ↦ f)} {M : F.obj (.mk (op S))}
    {a : D.obj default ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj (D.obj default))}
    (ha : IsTransposeOf sq adj a
      (D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂))
    (e : (F.map f.op.toLoc).toFunctor.obj M ≅ D.obj default)
    (he : (F.map f.op.toLoc).toFunctor.map (adj.unit.app M) ≫
      (F.map f.op.toLoc).toFunctor.map (Rf.map e.hom) = e.hom ≫ a) :
    (F.toDescentData (fun _ : ι ↦ f)).obj M ≅ D :=
  descentDataIsoOfDescentSquareApp_comm_of_unique sq e
    (descentSquareApp_comm_of_coalgebraHom sq adj adjp ha e.hom he)

include adjp in
/-- `CategoryTheory.Pseudofunctor.descentDataIsoOfCoalgebraIso` read as a membership in the
essential image. -/
theorem essImage_toDescentData_of_coalgebraIso [Unique ι]
    {D : F.DescentData (fun _ : ι ↦ f)} {M : F.obj (.mk (op S))}
    {a : D.obj default ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj (D.obj default))}
    (ha : IsTransposeOf sq adj a
      (D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂))
    (e : (F.map f.op.toLoc).toFunctor.obj M ≅ D.obj default)
    (he : (F.map f.op.toLoc).toFunctor.map (adj.unit.app M) ≫
      (F.map f.op.toLoc).toFunctor.map (Rf.map e.hom) = e.hom ≫ a) :
    (F.toDescentData (fun _ : ι ↦ f)).essImage D :=
  ⟨M, ⟨descentDataIsoOfCoalgebraIso sq adj adjp ha e he⟩⟩

/-- Pulled back along a lift, the transposed transition morphism is the transition morphism
of the datum. -/
private lemma hom_eq_aux [Unique ι] (D : F.DescentData (fun _ : ι ↦ f))
    {a : D.obj default ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj (D.obj default))}
    (ha : IsTransposeOf sq adj a (D.hom sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂))
    ⦃Z : C⦄ (l : Z ⟶ sq.pullback) (q : Z ⟶ S) (u v : Z ⟶ X)
    (hq : l ≫ sq.p = q) (hu : l ≫ sq.p₁ = u) (hv : l ≫ sq.p₂ = v)
    (hu' : u ≫ f = q) (hv' : v ≫ f = q) :
    (F.map u.op.toLoc).toFunctor.map a ≫
        descentComparison (Rf.obj (D.obj default)) q u v hu' hv' ≫
        (F.map v.op.toLoc).toFunctor.map (adj.counit.app (D.obj default)) =
      D.hom (i₁ := default) (i₂ := default) q u v hu' hv' := by
  have h2 := congrArg (fun φ ↦ pullHom φ l u v hu hv) ha
  rwa [pullHom_map_comp_comp_map, descentSquareApp_eq_descentComparison,
    pullHom_descentComparison _ l sq.p q hq sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ u v hu hv,
    D.pullHom_hom l sq.p q hq sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ u v hu hv] at h2

/-- **The counit axiom of the coalgebra structure induced by a descent datum.**  If the structure
map `a` on the component of a descent datum for a one-element family corresponds to the datum's
transition morphism over the chosen pullback, then `a ≫ ε = 𝟙`.

The proof pulls the transposed description `CategoryTheory.Pseudofunctor.IsTransposeOf` back
along the diagonal `X ⟶ sq.pullback`, where the transition morphism of the datum becomes
`D.hom f (𝟙 X) (𝟙 X)` and
the comparison of the two pullbacks of `f_* A` becomes the corresponding transition of the
canonical datum of `f_* A`; both are the identity, by `hom_self`. -/
lemma counit_of_descentData [Unique ι] (D : F.DescentData (fun _ : ι ↦ f))
    {a : D.obj default ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj (D.obj default))}
    (ha : IsTransposeOf sq adj a
      (D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂)) :
    a ≫ adj.counit.app (D.obj default) = 𝟙 _ := by
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := sq.isPullback.exists_lift (𝟙 X) (𝟙 X) rfl
  have hΔ : Δ ≫ sq.p = f := by rw [← sq.hp₁, reassoc_of% hΔ₁]
  have h2 := hom_eq_aux sq adj D ha Δ f (𝟙 X) (𝟙 X) hΔ hΔ₁ hΔ₂ (by simp) (by simp)
  rw [descentComparison_self, Category.id_comp, ← Functor.map_comp,
    D.hom_self f (𝟙 X) (by simp)] at h2
  have hid : ((𝟙 X).op.toLoc : LocallyDiscrete.mk (op X) ⟶ _) = 𝟙 _ := by simp
  have hiso : IsIso ((Cat.Hom.toNatIso
      (F.mapId' ((𝟙 X).op.toLoc) hid)).hom.app (D.obj default)) := inferInstance
  rw [Cat.Hom.toNatIso_hom] at hiso
  rw [← cancel_epi ((F.mapId' ((𝟙 X).op.toLoc) hid).hom.toNatTrans.app (D.obj default)),
    ← mapId'_hom_naturality, h2]
  simp

/-- **The coassociativity axiom, from compatibility of the transition morphism with the structure
map.**  If `a` corresponds to `θ` and the base-change morphism is invertible at `f^* f_* A` —
which the hypotheses state at an object `Z` identified with it, so that only an equality of
objects and never an `IsIso` is converted when the two spellings of the inverse image differ —
then the equation `p₁^* a ≫ (comparison at f_* A) = θ ≫ p₂^* a` — which is
`CategoryTheory.Pseudofunctor.DescentDataCoassoc` — gives the Eilenberg–Moore coassociativity
axiom for `a`.

Both equations are the cocycle condition of the descent datum; this one is its transposition, and
the implication is the computation of
`CategoryTheory.Pseudofunctor.unit_comp_map_descentSquareApp_counit` closed by naturality
instead of by a triangle identity. -/
lemma coassoc_of_descentDataCoassoc {A : F.obj (.mk (op X))}
    {θ : (F.map sq.p₁.op.toLoc).toFunctor.obj A ⟶ (F.map sq.p₂.op.toLoc).toFunctor.obj A}
    {a : A ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj A)}
    (ha : IsTransposeOf sq adj a θ)
    {Z : F.obj (.mk (op X))} (hZ : (F.map f.op.toLoc).toFunctor.obj (Rf.obj A) = Z)
    (hiso : IsIso ((descentBaseChange sq adj adjp).app Z))
    (hco : (F.map sq.p₁.op.toLoc).toFunctor.map a ≫ descentSquareApp sq (Rf.obj A) =
      θ ≫ (F.map sq.p₂.op.toLoc).toFunctor.map a) :
    a ≫ (F.map f.op.toLoc).toFunctor.map (adj.unit.app (Rf.obj A)) =
      a ≫ (F.map f.op.toLoc).toFunctor.map (Rf.map a) := by
  subst hZ
  replace ha := (isTransposeOf_iff_descentBaseChange_app_eq sq adj adjp).1 ha
  have hnat := (descentBaseChange sq adj adjp).naturality a
  dsimp at hnat
  have hun := adjp.unit.naturality a
  dsimp at hun
  have hmono : Mono ((descentBaseChange sq adj adjp).app
    ((F.map f.op.toLoc).toFunctor.obj (Rf.obj A))) := inferInstance
  rw [← cancel_mono ((descentBaseChange sq adj adjp).app
    ((F.map f.op.toLoc).toFunctor.obj (Rf.obj A))), Category.assoc, Category.assoc,
    unit_descentBaseChange sq adj adjp (Rf.obj A), hnat, reassoc_of% hun, reassoc_of% ha,
    ← Functor.map_comp, ← Functor.map_comp, hco]

/-- **The coalgebra structure map that a descent datum induces on its component.**  For a
one-element family whose base-change morphism is invertible on the component of `D`, this is the
transposition of the transition morphism of `D` over the chosen pullback.  It is the unique
morphism satisfying
`CategoryTheory.Pseudofunctor.descentCoalgebraMap_comp_descentBaseChange`. -/
noncomputable def descentCoalgebraMap [Unique ι] (D : F.DescentData (fun _ : ι ↦ f))
    [IsIso ((descentBaseChange sq adj adjp).app (D.obj default))] :
    D.obj default ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj (D.obj default)) :=
  (adjp.unit.app (D.obj default) ≫ Rp.map
      (D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂)) ≫
    inv ((descentBaseChange sq adj adjp).app (D.obj default))

/-- The composite of `descentCoalgebraMap` with the base-change morphism at the component of `D`
is the unit of `adjp` followed by the image under `Rp` of the transition morphism of `D` over the
chosen pullback. -/
@[simp]
lemma descentCoalgebraMap_comp_descentBaseChange [Unique ι]
    (D : F.DescentData (fun _ : ι ↦ f))
    [IsIso ((descentBaseChange sq adj adjp).app (D.obj default))] :
    descentCoalgebraMap sq adj adjp D ≫ (descentBaseChange sq adj adjp).app (D.obj default) =
      adjp.unit.app (D.obj default) ≫ Rp.map
        (D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂) := by
  rw [descentCoalgebraMap, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The morphism `descentCoalgebraMap` transposes to the transition morphism of `D` over the
chosen pullback. -/
lemma isTransposeOf_descentCoalgebraMap [Unique ι] (D : F.DescentData (fun _ : ι ↦ f))
    [IsIso ((descentBaseChange sq adj adjp).app (D.obj default))] :
    IsTransposeOf sq adj (descentCoalgebraMap sq adj adjp D)
      (D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂) :=
  (isTransposeOf_iff_descentBaseChange_app_eq sq adj adjp).2
    (descentCoalgebraMap_comp_descentBaseChange sq adj adjp D)

/-- **A descent datum for a one-element family has a structure map on its component**: there
exists a morphism `a : A ⟶ f^* f_* A` transposing to the transition morphism of the datum over
the chosen pullback, namely `CategoryTheory.Pseudofunctor.descentCoalgebraMap`.

This is `CategoryTheory.Pseudofunctor.isTransposeOf_descentCoalgebraMap` read existentially, so
that a consumer which only needs *some* such morphism never has to mention
`descentCoalgebraMap` — whose value depends on the inverse of the base-change morphism. -/
theorem exists_isTransposeOf [Unique ι] (D : F.DescentData (fun _ : ι ↦ f))
    [IsIso ((descentBaseChange sq adj adjp).app (D.obj default))] :
    ∃ a : D.obj default ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj (D.obj default)),
      IsTransposeOf sq adj a
        (D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂) :=
  ⟨_, isTransposeOf_descentCoalgebraMap sq adj adjp D⟩

/-- **The equation that the object half of the comparison of descent data with coalgebras still
needs.**  For a descent datum `D` for a one-element family whose base-change morphism is
invertible on the component, this says that the transition morphism of `D` over the chosen
pullback is compatible with the induced coalgebra structure map.

It is the cocycle condition of `D` — `CategoryTheory.Pseudofunctor.DescentData.hom_comp`, which
for a one-element family lives over a threefold fibre product — transposed onto the chosen
pullback, and by `CategoryTheory.Pseudofunctor.coassoc_of_descentDataCoassoc` it is what
coassociativity of the structure map amounts to. -/
def DescentDataCoassoc [Unique ι] (D : F.DescentData (fun _ : ι ↦ f))
    [IsIso ((descentBaseChange sq adj adjp).app (D.obj default))] : Prop :=
  (F.map sq.p₁.op.toLoc).toFunctor.map (descentCoalgebraMap sq adj adjp D) ≫
      descentSquareApp sq (Rf.obj (D.obj default)) =
    D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ ≫
      (F.map sq.p₂.op.toLoc).toFunctor.map (descentCoalgebraMap sq adj adjp D)

/-- **Effectivity of a descent datum for a one-element family, from comonadicity.**  Let
`f : X ⟶ S` have a chosen pullback with itself, let the pullbacks along `f` and along the first
projection have right adjoints, and let the base-change morphism `f^* f_* ⟶ (p₁)_* p₂^*` be
invertible at the component of a descent datum `D` and a monomorphism at `f^* f_*` of it.  If the
Eilenberg–Moore comparison functor of `f^* ⊣ f_*` is essentially surjective and `D` satisfies
`CategoryTheory.Pseudofunctor.DescentDataCoassoc`, then `D` is in the essential image of
`CategoryTheory.Pseudofunctor.toDescentData`: it is effective.

This is the object-level content of the comparison between
`CategoryTheory.Pseudofunctor.DescentData` and
`CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra` for a one-element family, which is what the
effectivity half of a descent statement needs. -/
theorem essImage_toDescentData_of_descentDataCoassoc [Unique ι]
    (D : F.DescentData (fun _ : ι ↦ f))
    [IsIso ((descentBaseChange sq adj adjp).app (D.obj default))]
    (hiso' : IsIso ((descentBaseChange sq adj adjp).app
      ((F.map f.op.toLoc).toFunctor.obj (Rf.obj (D.obj default)))))
    (hco : DescentDataCoassoc sq adj adjp D) [(Comonad.comparison adj).EssSurj] :
    (F.toDescentData (fun _ : ι ↦ f)).essImage D := by
  obtain ⟨M, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := Comonad.comparison adj)
    { A := D.obj default
      a := descentCoalgebraMap sq adj adjp D
      counit := counit_of_descentData sq adj D
        (isTransposeOf_descentCoalgebraMap sq adj adjp D)
      coassoc := coassoc_of_descentDataCoassoc sq adj adjp
        (isTransposeOf_descentCoalgebraMap sq adj adjp D) rfl hiso' hco }
  exact essImage_toDescentData_of_descentSquareApp_comm_of_unique sq
    (adj.toComonad.forget.mapIso i) (descentSquareApp_comm_of_coalgebraHom sq adj adjp
      (isTransposeOf_descentCoalgebraMap sq adj adjp D) i.hom.f i.hom.h)

/-- **The counit companion of `CategoryTheory.Pseudofunctor.unit_descentBaseChange`.**  Pulling
the base-change morphism back along `p₁` and composing with the counit of `p₁^* ⊣ (p₁)_*` gives
the canonical comparison of the two pullbacks of `f_* A` followed by `p₂^*` of the counit of
`f^* ⊣ f_*`.

Where the unit identity pins the base-change morphism down on the image of `f^*` of a unit, this
one pins it down after pulling back along `p₁`, which is what a computation over a *further*
pullback needs.  Both are instances of the transposed forms of `CategoryTheory.mateEquiv`. -/
lemma counit_descentBaseChange (A : F.obj (.mk (op X))) :
    (F.map sq.p₁.op.toLoc).toFunctor.map ((descentBaseChange sq adj adjp).app A) ≫
        adjp.counit.app ((F.map sq.p₂.op.toLoc).toFunctor.obj A) =
      descentSquareApp sq (Rf.obj A) ≫
        (F.map sq.p₂.op.toLoc).toFunctor.map (adj.counit.app A) :=
  mateEquiv_counit adj adjp (descentSquare sq) A

/-- **The transposed transition morphism, pulled back along a lift.**  If the structure map `a`
on the component of a descent datum for a one-element family transposes to the transition
morphism of the datum over the chosen pullback, then for *every* object `Z` mapping to
`sq.pullback` the same description holds over `Z`: the composite of `u^* a`, the canonical
comparison of the inverse images of `f_* A`, and `v^*` of the counit is `D.hom q u v`.

This is the move behind both axioms of the induced coalgebra structure: taking `Z = X` and the
diagonal gives the counit axiom, and taking `Z` to be a threefold fibre product gives
coassociativity. -/
lemma hom_eq_of_isTransposeOf [Unique ι] (D : F.DescentData (fun _ : ι ↦ f))
    {a : D.obj default ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj (D.obj default))}
    (ha : IsTransposeOf sq adj a (D.hom sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂))
    ⦃Z : C⦄ (l : Z ⟶ sq.pullback) (q : Z ⟶ S) (u v : Z ⟶ X)
    (hq : l ≫ sq.p = q) (hu : l ≫ sq.p₁ = u) (hv : l ≫ sq.p₂ = v)
    (hu' : u ≫ f = q) (hv' : v ≫ f = q) :
    (F.map u.op.toLoc).toFunctor.map a ≫
        descentComparison (Rf.obj (D.obj default)) q u v hu' hv' ≫
        (F.map v.op.toLoc).toFunctor.map (adj.counit.app (D.obj default)) =
      D.hom (i₁ := default) (i₂ := default) q u v hu' hv' :=
  hom_eq_aux sq adj D ha l q u v hq hu hv hu' hv'

section Triple

variable (sq' : ChosenPullback sq.p₁ sq.p₁)
  {Rs : F.obj (.mk (op sq'.pullback)) ⥤ F.obj (.mk (op sq.pullback))}
  (adjs : (F.map sq'.p₁.op.toLoc).toFunctor ⊣ Rs)

/-- **The double base-change morphism of the threefold fibre product.**  For a chosen pullback
`sq` of `f` with itself and a chosen pullback `sq'` of `p₁` with itself — whose underlying object
is a threefold fibre product of `f` — this is the composite

`p₂^* f^* f_* A ≅ p₁^* f^* f_* A ⟶ p₁^* (p₁)_* p₂^* A ⟶ (s₁)_* (s₂)^* p₂^* A`

of the canonical comparison with `p₁^*` of the base-change morphism of `sq` and with the
base-change morphism of `sq'`.  Both base-change morphisms are instances of
`CategoryTheory.Pseudofunctor.descentBaseChange` — the second one only because the comparison
rewrites `p₂^*` as `p₁^*`, which is what makes the threefold fibre product a chosen pullback of
`p₁` with *itself* rather than of `p₂` with `p₁`.

When both are invertible this morphism is a monomorphism, and that is exactly what makes the
cocycle condition over the threefold fibre product imply the coassociativity equation over the
twofold one. -/
noncomputable def descentDoubleBaseChange (A : F.obj (.mk (op X))) :
    (F.map sq.p₂.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj (Rf.obj A)) ⟶
      Rs.obj ((F.map sq'.p₂.op.toLoc).toFunctor.obj
        ((F.map sq.p₂.op.toLoc).toFunctor.obj A)) :=
  descentComparison (Rf.obj A) sq.p sq.p₂ sq.p₁ sq.hp₂ sq.hp₁ ≫
    (F.map sq.p₁.op.toLoc).toFunctor.map ((descentBaseChange sq adj adjp).app A) ≫
    (descentBaseChange sq' adjp adjs).app ((F.map sq.p₂.op.toLoc).toFunctor.obj A)

/-- A composite `s₁^* u ≫ (comparison over sq') ≫ s₂^* v` of inverse images along the two
projections of the threefold fibre product is the conjugate, by the canonical comparisons, of the
composite of the two pulled-back morphisms.  This is the bookkeeping that turns a computation
over the threefold fibre product into one over the twofold one: the comparison of `sq'` is by
definition the pair of compositors that
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` inserts. -/
lemma map_comp_descentSquareApp_comp_map {A N A' : F.obj (.mk (op X))}
    (u : (F.map sq.p₁.op.toLoc).toFunctor.obj A ⟶ (F.map sq.p₁.op.toLoc).toFunctor.obj N)
    (v : (F.map sq.p₁.op.toLoc).toFunctor.obj N ⟶ (F.map sq.p₂.op.toLoc).toFunctor.obj A') :
    (F.map sq'.p₁.op.toLoc).toFunctor.map u ≫ descentSquareApp sq' N ≫
        (F.map sq'.p₂.op.toLoc).toFunctor.map v =
      (F.mapComp' sq.p₁.op.toLoc sq'.p₁.op.toLoc sq'.p.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq'.hp₁])).inv.toNatTrans.app A ≫
        (pullHom u sq'.p₁ sq'.p sq'.p sq'.hp₁ sq'.hp₁ ≫
          pullHom v sq'.p₂ sq'.p (sq'.p₂ ≫ sq.p₂) sq'.hp₂ rfl) ≫
        (F.mapComp' sq.p₂.op.toLoc sq'.p₂.op.toLoc (sq'.p₂ ≫ sq.p₂).op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app A' := by
  dsimp only [pullHom, descentSquareApp, descentPullbackIso₁, descentPullbackIso₂]
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  simp

/-- **The transposition of the double base-change morphism.**  Pulled back along `s₁` and
composed with the counit of `s₁^* ⊣ (s₁)_*`, the double base-change morphism of
`CategoryTheory.Pseudofunctor.descentDoubleBaseChange` is the canonical comparison followed by
`s₂^*` of the transposed transition description.

This is `CategoryTheory.Pseudofunctor.counit_descentBaseChange` applied twice, the two
applications joined by the naturality of the comparison of `sq'`. -/
lemma map_descentDoubleBaseChange_comp_counit (A : F.obj (.mk (op X))) :
    (F.map sq'.p₁.op.toLoc).toFunctor.map (descentDoubleBaseChange sq adj adjp sq' adjs A) ≫
        adjs.counit.app ((F.map sq'.p₂.op.toLoc).toFunctor.obj
          ((F.map sq.p₂.op.toLoc).toFunctor.obj A)) =
      (F.map sq'.p₁.op.toLoc).toFunctor.map
          (descentComparison (Rf.obj A) sq.p sq.p₂ sq.p₁ sq.hp₂ sq.hp₁) ≫
        descentSquareApp sq' ((F.map f.op.toLoc).toFunctor.obj (Rf.obj A)) ≫
        (F.map sq'.p₂.op.toLoc).toFunctor.map
          (descentSquareApp sq (Rf.obj A) ≫
            (F.map sq.p₂.op.toLoc).toFunctor.map (adj.counit.app A)) := by
  rw [descentDoubleBaseChange, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    counit_descentBaseChange sq' adjp adjs ((F.map sq.p₂.op.toLoc).toFunctor.obj A),
    descentSquareApp_naturality_assoc sq'
      (M := (F.map f.op.toLoc).toFunctor.obj (Rf.obj A))
      (N := Rp.obj ((F.map sq.p₂.op.toLoc).toFunctor.obj A))
      ((descentBaseChange sq adj adjp).app A),
    ← Functor.map_comp, counit_descentBaseChange sq adj adjp A]

/-- Pulled back along the second projection of `sq'`, the transposed counit description over `sq`
is the canonical comparison over the threefold fibre product followed by the counit. -/
private lemma pullHom_descentSquareApp_comp_map_counit (A : F.obj (.mk (op X)))
    (hq : (sq'.p₂ ≫ sq.p₂) ≫ f = sq'.p ≫ f) :
    pullHom (descentSquareApp sq (Rf.obj A) ≫
        (F.map sq.p₂.op.toLoc).toFunctor.map (adj.counit.app A))
        sq'.p₂ sq'.p (sq'.p₂ ≫ sq.p₂) sq'.hp₂ rfl =
      descentComparison (Rf.obj A) (sq'.p ≫ f) sq'.p (sq'.p₂ ≫ sq.p₂) rfl hq ≫
        (F.map (sq'.p₂ ≫ sq.p₂).op.toLoc).toFunctor.map (adj.counit.app A) := by
  rw [pullHom_comp (gf₂ := sq'.p₂ ≫ sq.p₂) (hgf₂ := rfl), pullHom_map,
    descentSquareApp_eq_descentComparison,
    pullHom_descentComparison _ sq'.p₂ sq.p (sq'.p ≫ f)
      (by rw [← sq.hp₁, reassoc_of% sq'.hp₂]) sq.p₁ sq.p₂ sq.hp₁ sq.hp₂
      sq'.p (sq'.p₂ ≫ sq.p₂) sq'.hp₂ rfl]

/-- **Cancellation of the double base-change morphism.**  When both base-change morphisms are
invertible, two morphisms `p₁^* A ⟶ p₂^* f^* f_* A` are equal as soon as they agree after being
transported to the threefold fibre product, because
`CategoryTheory.Pseudofunctor.descentDoubleBaseChange` is then a monomorphism. -/
private lemma eq_of_pullHom_comp_descentComparison_eq {A : F.obj (.mk (op X))}
    [IsIso ((descentBaseChange sq adj adjp).app A)]
    [IsIso ((descentBaseChange sq' adjp adjs).app ((F.map sq.p₂.op.toLoc).toFunctor.obj A))]
    {x y : (F.map sq.p₁.op.toLoc).toFunctor.obj A ⟶
      (F.map sq.p₂.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj (Rf.obj A))}
    (h : pullHom (x ≫ descentComparison (Rf.obj A) sq.p sq.p₂ sq.p₁ sq.hp₂ sq.hp₁)
          sq'.p₁ sq'.p sq'.p sq'.hp₁ sq'.hp₁ ≫
        pullHom (descentSquareApp sq (Rf.obj A) ≫
          (F.map sq.p₂.op.toLoc).toFunctor.map (adj.counit.app A))
          sq'.p₂ sq'.p (sq'.p₂ ≫ sq.p₂) sq'.hp₂ rfl =
      pullHom (y ≫ descentComparison (Rf.obj A) sq.p sq.p₂ sq.p₁ sq.hp₂ sq.hp₁)
          sq'.p₁ sq'.p sq'.p sq'.hp₁ sq'.hp₁ ≫
        pullHom (descentSquareApp sq (Rf.obj A) ≫
          (F.map sq.p₂.op.toLoc).toFunctor.map (adj.counit.app A))
          sq'.p₂ sq'.p (sq'.p₂ ≫ sq.p₂) sq'.hp₂ rfl) :
    x = y := by
  have : IsIso (descentComparison (Rf.obj A) sq.p sq.p₂ sq.p₁ sq.hp₂ sq.hp₁) :=
    ⟨descentSquareApp sq (Rf.obj A), descentComparison_comp_descentSquareApp sq _,
      descentSquareApp_comp_descentComparison sq _⟩
  have : IsIso (descentDoubleBaseChange sq adj adjp sq' adjs A) := by
    dsimp only [descentDoubleBaseChange]
    infer_instance
  rw [← cancel_mono (descentDoubleBaseChange sq adj adjp sq' adjs A)]
  apply (adjs.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  conv_lhs => rw [Functor.map_comp, Category.assoc,
    map_descentDoubleBaseChange_comp_counit, ← Functor.map_comp_assoc,
    map_comp_descentSquareApp_comp_map]
  conv_rhs => rw [Functor.map_comp, Category.assoc,
    map_descentDoubleBaseChange_comp_counit, ← Functor.map_comp_assoc,
    map_comp_descentSquareApp_comp_map]
  rw [h]

/-- **The coassociativity equation, from the cocycle condition of the descent datum.**  Let `D`
be a descent datum for a one-element family `f : X ⟶ S`, let `a` be a morphism on its component
transposing to the transition morphism of `D` over a chosen pullback `sq` of `f` with itself, and
let `sq'` be a chosen pullback of `p₁` with itself — a threefold fibre product of `f`.  If the
base-change morphism of `sq` is invertible at the component and that of `sq'` at `p₂^*` of the
component, then `a` satisfies the equation
`CategoryTheory.Pseudofunctor.DescentDataCoassoc` asks for.

This is the object half of the `TODO` of
`Mathlib/CategoryTheory/Sites/Descent/DescentDataAsCoalgebra.lean`.  The proof is the only place
where the threefold fibre product is needed: both sides of the equation become equal after
composing with `CategoryTheory.Pseudofunctor.descentDoubleBaseChange`, which is a monomorphism
under the two invertibility hypotheses, and the resulting identity over the threefold fibre
product is `CategoryTheory.Pseudofunctor.DescentData.hom_comp` for the three projections, each
transition morphism being described by
`CategoryTheory.Pseudofunctor.hom_eq_of_isTransposeOf` at the corresponding lift. -/
theorem descentDataCoassoc_of_isTransposeOf [Unique ι] (D : F.DescentData (fun _ : ι ↦ f))
    {a : D.obj default ⟶ (F.map f.op.toLoc).toFunctor.obj (Rf.obj (D.obj default))}
    (ha : IsTransposeOf sq adj a (D.hom sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂))
    (h₁ : IsIso ((descentBaseChange sq adj adjp).app (D.obj default)))
    (h₂ : IsIso ((descentBaseChange sq' adjp adjs).app
      ((F.map sq.p₂.op.toLoc).toFunctor.obj (D.obj default)))) :
    (F.map sq.p₁.op.toLoc).toFunctor.map a ≫ descentSquareApp sq (Rf.obj (D.obj default)) =
      D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ ≫
        (F.map sq.p₂.op.toLoc).toFunctor.map a := by
  have := h₁
  have := h₂
  have hq1 : (sq'.p₁ ≫ sq.p₂) ≫ f = sq'.p ≫ f := by
    rw [Category.assoc, sq.hp₂, ← sq.hp₁, ← Category.assoc, sq'.hp₁]
  have hq2 : (sq'.p₂ ≫ sq.p₂) ≫ f = sq'.p ≫ f := by
    rw [Category.assoc, sq.hp₂, ← sq.hp₁, ← Category.assoc, sq'.hp₂]
  have hp1 : sq'.p₁ ≫ sq.p = sq'.p ≫ f := by rw [← sq.hp₁, reassoc_of% sq'.hp₁]
  have hp2 : sq'.p₂ ≫ sq.p = sq'.p ≫ f := by rw [← sq.hp₁, reassoc_of% sq'.hp₂]
  obtain ⟨l, hl₁, hl₂⟩ := sq.isPullback.exists_lift (sq'.p₁ ≫ sq.p₂) (sq'.p₂ ≫ sq.p₂)
    (by rw [hq1, hq2])
  have hlp : l ≫ sq.p = sq'.p ≫ f := by
    rw [← sq.hp₁, reassoc_of% hl₁, ← Category.assoc, hq1]
  -- the second projection of `sq'` is a lift of the outer pair of projections
  have T02 := hom_eq_of_isTransposeOf sq adj D ha sq'.p₂ (sq'.p ≫ f) sq'.p
    (sq'.p₂ ≫ sq.p₂) hp2 sq'.hp₂ rfl rfl hq2
  -- and `l` is a lift of the inner pair
  have T12 := hom_eq_of_isTransposeOf sq adj D ha l (sq'.p ≫ f) (sq'.p₁ ≫ sq.p₂)
    (sq'.p₂ ≫ sq.p₂) hlp hl₁ hl₂ hq1 hq2
  -- the factor common to the two sides
  have hQ := pullHom_descentSquareApp_comp_map_counit sq adj sq' (D.obj default) hq2
  -- both sides, pulled back to the threefold fibre product, are the outer transition morphism
  have hR : pullHom ((D.hom (i₁ := default) (i₂ := default) sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ ≫
            (F.map sq.p₂.op.toLoc).toFunctor.map a) ≫
          descentComparison (Rf.obj (D.obj default)) sq.p sq.p₂ sq.p₁ sq.hp₂ sq.hp₁)
          sq'.p₁ sq'.p sq'.p sq'.hp₁ sq'.hp₁ ≫
        pullHom (descentSquareApp sq (Rf.obj (D.obj default)) ≫
          (F.map sq.p₂.op.toLoc).toFunctor.map (adj.counit.app (D.obj default)))
          sq'.p₂ sq'.p (sq'.p₂ ≫ sq.p₂) sq'.hp₂ rfl =
      D.hom (i₁ := default) (i₂ := default) (sq'.p ≫ f) sq'.p (sq'.p₂ ≫ sq.p₂) rfl hq2 := by
    rw [Category.assoc, pullHom_comp (gf₂ := sq'.p₁ ≫ sq.p₂) (hgf₂ := rfl),
      D.pullHom_hom sq'.p₁ sq.p (sq'.p ≫ f) hp1 sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ sq'.p
        (sq'.p₁ ≫ sq.p₂) sq'.hp₁ rfl,
      pullHom_comp (gf₂ := sq'.p₁ ≫ sq.p₂) (hgf₂ := rfl), pullHom_map,
      pullHom_descentComparison _ sq'.p₁ sq.p (sq'.p ≫ f) hp1 sq.p₂ sq.p₁ sq.hp₂ sq.hp₁
        (sq'.p₁ ≫ sq.p₂) sq'.p rfl sq'.hp₁, hQ]
    simp only [Category.assoc]
    rw [descentComparison_comp_assoc (Rf.obj (D.obj default)) (sq'.p ≫ f) (sq'.p₁ ≫ sq.p₂) sq'.p
      (sq'.p₂ ≫ sq.p₂) hq1 rfl hq2, T12]
    exact D.hom_comp (sq'.p ≫ f) sq'.p (sq'.p₁ ≫ sq.p₂) (sq'.p₂ ≫ sq.p₂) rfl hq1 hq2
  refine eq_of_pullHom_comp_descentComparison_eq sq adj adjp sq' adjs (Eq.trans ?_ hR.symm)
  rw [Category.assoc, descentSquareApp_comp_descentComparison, Category.comp_id, pullHom_map, hQ]
  exact T02

/-- **`CategoryTheory.Pseudofunctor.DescentDataCoassoc` holds.**  The one equation that the
object-level comparison of `CategoryTheory.Pseudofunctor.DescentData` with Eilenberg–Moore
coalgebras was reduced to is a consequence of the descent datum's own cocycle condition, as soon
as a threefold fibre product exists and the two base-change morphisms are invertible. -/
theorem descentDataCoassoc [Unique ι] (D : F.DescentData (fun _ : ι ↦ f))
    [IsIso ((descentBaseChange sq adj adjp).app (D.obj default))]
    (h₂ : IsIso ((descentBaseChange sq' adjp adjs).app
      ((F.map sq.p₂.op.toLoc).toFunctor.obj (D.obj default)))) :
    DescentDataCoassoc sq adj adjp D :=
  descentDataCoassoc_of_isTransposeOf sq adj adjp sq' adjs D
    (isTransposeOf_descentCoalgebraMap sq adj adjp D) ‹_› h₂

/-- **Every descent datum for a one-element family is effective.**  Let `f : X ⟶ S` have a chosen
pullback `sq` with itself and let `p₁` have a chosen pullback `sq'` with itself, let the three
inverse-image functors involved have right adjoints, let the base-change morphism of `sq` be
invertible at the component of a descent datum `D` and at `f^* f_*` of it, and let that of `sq'`
be invertible at `p₂^*` of the component.  If the Eilenberg–Moore comparison functor of
`f^* ⊣ f_*` is essentially surjective, then `D` is in the essential image of
`CategoryTheory.Pseudofunctor.toDescentData`.

This is `CategoryTheory.Pseudofunctor.essImage_toDescentData_of_descentDataCoassoc` with its
remaining equation discharged by `CategoryTheory.Pseudofunctor.descentDataCoassoc`, and it is the
object-level content of the comparison between `CategoryTheory.Pseudofunctor.DescentData` and
`CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra` for a one-element family. -/
theorem essImage_toDescentData [Unique ι] (D : F.DescentData (fun _ : ι ↦ f))
    [IsIso ((descentBaseChange sq adj adjp).app (D.obj default))]
    (hiso' : IsIso ((descentBaseChange sq adj adjp).app
      ((F.map f.op.toLoc).toFunctor.obj (Rf.obj (D.obj default)))))
    (h₂ : IsIso ((descentBaseChange sq' adjp adjs).app
      ((F.map sq.p₂.op.toLoc).toFunctor.obj (D.obj default))))
    [(Comonad.comparison adj).EssSurj] :
    (F.toDescentData (fun _ : ι ↦ f)).essImage D :=
  essImage_toDescentData_of_descentDataCoassoc sq adj adjp D hiso'
    (descentDataCoassoc sq adj adjp sq' adjs D h₂)

end Triple

end Coalgebra

end Pseudofunctor

end CategoryTheory

end
