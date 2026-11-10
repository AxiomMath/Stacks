module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeCompositionOnRingedTopoi
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem

/-!
# Pasting of derived base change maps for ringed topoi

Two commutative squares of ringed topoi sharing an edge paste to a commutative rectangle, and the
derived base change map of Stacks 07A7 for the rectangle is the composite of the derived base
change maps of the two squares, read through the composition isomorphisms for the two composite
legs.  There are two such statements, according to whether the shared edge is vertical or
horizontal:

```
         g''        g'                  k
  X'' ———→ X' ———→ X             B' ———→ B
   |f''      |f'     |f            |f'     |f
   v         v       v             v       v
  Y'' ———→ Y' ———→ Y             C' ———→ C
         h          g                  l
                                   |g'     |g
                                   v       v
                                  D' ———→ D
                                       m
```

For the horizontal pasting the two composite legs are the horizontal composites `g ∘ h` and
`g' ∘ g''`, compared with the iterated derived pullbacks by the composition formula of Stacks
0D6D; this is Stacks 0E47.  For the vertical pasting they are the vertical composites `g ∘ f` and
`g' ∘ f'`, and what compares the iterated derived pushforwards with the derived pushforward along
the composite is `derivedPushforwardCompIso`; this is Stacks 0E46.

## Main definitions

* `derivedPushforwardCompIso`: the composition isomorphism `Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*` for the
  unbounded derived pushforward along two composable morphisms of ringed topoi, with no further
  hypothesis.  It is the adjoint of the composition isomorphism of Stacks 0D6D.

## Main results

* `derivedBaseChangeMap_horizontal`: **Stacks 0E47**, the horizontal pasting law.
* `derivedBaseChangeMap_comp`: the vertical pasting law of Stacks 0E46, for morphisms of sites;
  the general statement is
  `Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedBaseChangeMapOfTwoIso_vertical`.
* `derivedSquareComparison_horizontal`: the comparison of iterated derived pullbacks around a
  rectangle is the horizontal composite of the comparisons of its two squares.  This is the
  geometric content of both pasting laws, and `derivedPullbackSquare_paste` is the same statement
  for a vertically composable pair, obtained from it by transposing the diagram.
* `derivedBaseChangeSquare_paste`: the vertical pasting law as an identity of 2-squares, so with
  the naturality of all four factors in the object.
* `conjugateEquiv_derivedPullbackCompIso_inv` and `conjugateEquiv_derivedPullbackCompIso_hom`:
  `derivedPushforwardCompIso` is the adjoint of the Stacks 0D6D isomorphism, in both directions.

## Implementation notes

*Where the content is.*  The derived base change morphism is the mate of the comparison of the two
iterated derived pullbacks around a square, so both pasting laws reduce to the pasting of those
comparisons, and that in turn to the cocycle identity
`Stacks.Cohomology.DerivedBaseChangeComposition.derivedPullbackCompComparison_assoc` of Stacks
0D6D, used three times, together with the compatibility of the composition isomorphism with an
equality of either of its two arguments.  `squareComparison_horizontal` carries out that argument
on abstract functors, and `derivedSquareComparison_horizontal` is a single application of it.

*Composition of morphisms of ringed topoi is strictly associative.*  So the transports that the
ringed-space analogue `Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare_paste` of Stacks
0ATL carries along an associativity isomorphism are absent here: in
`squareComparison_horizontal` the three identifications of a threefold composite with its other
bracketing are made at the level of types, by instantiating one functor variable with two
definitionally equal spellings.  Instance resolution is still syntactic, so each spelling of a
composite carries its own `HasLeftDerivedFunctor` hypothesis.

*Why everything formal is on abstract functors.*
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback` and
`derivedPushforward` are reducible abbreviations over total derived functors, and a rewriting step
performed at these types forces the elaborator and then the kernel to unfold the localization
construction.  Every rearrangement below is therefore a lemma on variables —
`squareComparison_horizontal`, `baseChangeMate_horizontal`, `twoSquare_paste_of_app`,
`mate_twoSquare_paste`, `comp₄_inv` — of which the geometric statement is one application.

*Why the transports are componentwise.*  `derivedPullbackCongr` is built by substituting the
equality of morphisms, so its components do not reduce while that equality is a variable;
`transportNatTrans` is a projection out of an explicit structure and does.
`derivedPullbackCongr_inv_app` is the single bridge between the two spellings, and
`derivedBaseChangeMap_adjoint_split` is where it is used to restate the adjoint characterization
of Stacks 07A7 in the form the pasting argument consumes.

*The derived pushforward composition isomorphism is unconditional.*  Both `Rf_* ⋙ Rg_*` and
`R(g ∘ f)_*` are right adjoint to the derived pullback along `g ∘ f` — the second by the derived
adjunction of Stacks 07A6, the first by the composite of the two derived adjunctions transported
along Stacks 0D6D — so `CategoryTheory.Adjunction.rightAdjointUniq` produces the comparison with
no hypothesis on the morphisms beyond their being morphisms of ringed topoi, and
`conjugateEquiv_iso_inv` identifies it with the adjoint of the Stacks 0D6D isomorphism.

## References

* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.TwoSquare
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
open Stacks.Cohomology.DerivedBaseChangeOnTopoi
open Stacks.Cohomology.DerivedBaseChangeComposition
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

namespace Stacks.Cohomology.DerivedBaseChangePasting

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-! ### Abstract bookkeeping -/

/-- The transport along an equality of functors, defined componentwise. -/
def transportNatTrans {A B : Type*} [Category* A] [Category* B] {F G : A ⥤ B} (e : F = G) :
    F ⟶ G where
  app M := eqToHom (Functor.congr_obj e M)
  naturality _ _ p := by
    subst e
    simp

/-- The components of `transportNatTrans` are those of `eqToHom`. -/
@[simp]
theorem transportNatTrans_app {A B : Type*} [Category* A] [Category* B] {F G : A ⥤ B}
    (e : F = G) (M : A) :
    (transportNatTrans e).app M = eqToHom (Functor.congr_obj e M) :=
  rfl

/-- Two transports between functors compose to the transport along the composed equality. -/
theorem transportNatTrans_app_trans {A B : Type*} [Category* A] [Category* B] {F₁ F₂ F₃ : A ⥤ B}
    (a : F₁ = F₂) (b : F₂ = F₃) (p : F₁ = F₃) (M : A) :
    (transportNatTrans a).app M ≫ (transportNatTrans b).app M =
      (transportNatTrans p).app M := by
  simp only [transportNatTrans_app, eqToHom_trans]

/-- Naturality of a transformation out of a composite functor, with the composite unfolded. -/
theorem natTrans_comp_naturality {A B B' : Type*} [Category* A] [Category* B] [Category* B']
    {P : A ⥤ B} {Q : B ⥤ B'} {T : A ⥤ B'} (α : P ⋙ Q ⟶ T) {M N : A} (u : M ⟶ N) :
    Q.map (P.map u) ≫ α.app N = α.app M ≫ T.map u := by
  simpa only [Functor.comp_map] using α.naturality u

/-- Naturality of a threefold composite of natural transformations, taken componentwise. -/
theorem natTrans_comp₃_naturality {A B : Type*} [Category* A] [Category* B] {F₁ F₂ F₃ F₄ : A ⥤ B}
    (x : F₁ ⟶ F₂) (y : F₂ ⟶ F₃) (z : F₃ ⟶ F₄) {M N : A} (u : M ⟶ N) :
    F₁.map u ≫ x.app N ≫ y.app N ≫ z.app N =
      (x.app M ≫ y.app M ≫ z.app M) ≫ F₄.map u := by
  rw [x.naturality_assoc, y.naturality_assoc, z.naturality, Category.assoc, Category.assoc]

/-- Naturality of a threefold componentwise composite between two composite functors, in the form
`baseChangeMate_horizontal` consumes it. -/
theorem comp₃_app_naturality_assoc {X X' Y' Y'' : Type*}
    [Category* X] [Category* X'] [Category* Y'] [Category* Y'']
    {H' : X ⥤ X'} {F'' : X' ⥤ Y''} {F' : X ⥤ Y'} {G' : Y' ⥤ Y''} {P₁ P₂ : X ⥤ Y''}
    (x : H' ⋙ F'' ⟶ P₁) (y : P₁ ⟶ P₂) (z : P₂ ⟶ F' ⋙ G') {M N : X} (u : M ⟶ N) {T : Y''}
    (v : (F' ⋙ G').obj N ⟶ T) :
    F''.map (H'.map u) ≫ x.app N ≫ y.app N ≫ z.app N ≫ v =
      x.app M ≫ y.app M ≫ z.app M ≫ G'.map (F'.map u) ≫ v := by
  rw [reassoc_of% (natTrans_comp₃_naturality x y z u)]

/-- A componentwise identity between natural transformations of composite functors, read off from
the whiskered identity the cocycle of Stacks 0D6D is stated as. -/
theorem app_of_whiskered_assoc {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {P : A ⥤ B} {Q : B ⥤ C} {R : C ⥤ D} {S : A ⥤ C} {T : B ⥤ D} {U : A ⥤ D}
    {c : Q ⋙ R ⟶ T} {d : P ⋙ T ⟶ U} {a : P ⋙ Q ⟶ S} {b : S ⋙ R ⟶ U}
    (h : Functor.whiskerLeft P c ≫ d =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight a R ≫ b)
    (M : A) :
    c.app (P.obj M) ≫ d.app M = R.map (a.app M) ≫ b.app M := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc] using NatTrans.congr_app h M

/-- Inverting a fourfold composite, with the inverse of each factor supplied separately.

Stated on variables: the morphisms it is applied to are components of comparisons between
composites of derived functors, where the rearrangement is unaffordable in place. -/
theorem comp₄_inv {E : Type*} [Category* E] {V₀ V₁ V₂ V₃ V₄ : E}
    (p : V₀ ⟶ V₁) (p' : V₁ ⟶ V₀) {a : V₁ ⟶ V₂} {a' : V₂ ⟶ V₁} (q : V₂ ⟶ V₃) (q' : V₃ ⟶ V₂)
    {b : V₃ ⟶ V₄} {b' : V₄ ⟶ V₃} {c : V₀ ⟶ V₄} {c' : V₄ ⟶ V₀}
    (hp : p' ≫ p = 𝟙 V₁) (ha : a' ≫ a = 𝟙 V₂) (hq : q' ≫ q = 𝟙 V₃) (hb : b' ≫ b = 𝟙 V₄)
    (hc : c ≫ c' = 𝟙 V₀) (h : p ≫ a ≫ q ≫ b = c) :
    b' ≫ q' ≫ a' ≫ p' = c' := by
  rw [← Category.comp_id (b' ≫ q' ≫ a' ≫ p'), ← hc, ← h]
  simp only [Category.assoc, reassoc_of% hp, reassoc_of% ha, reassoc_of% hq, reassoc_of% hb]

/-! ### The two abstract pasting lemmas -/

/-- **Horizontal composition of the comparison maps attached to two squares.**

Each square comparison is built from two composition isomorphisms and a transport along the
equality expressing commutativity of the square.  The identity is then a formal consequence of
associativity for those composition isomorphisms (`h1`, `h2`, `h3`), of their compatibility with
the two commutativity equalities (`h4`, `h5`), and of transport bookkeeping.

The statement is kept at the level of abstract functors on purpose: the functors it is applied to
are reducible abbreviations for a left derived functor, so performing this computation at the
concrete types forces the elaborator and the kernel to unfold the whole localization
construction. -/
theorem squareComparison_horizontal
    {X X' X'' Y Y' Y'' : Type*} [Category* X] [Category* X'] [Category* X'']
    [Category* Y] [Category* Y'] [Category* Y'']
    {H : X ⥤ X'} {H' : X' ⥤ X''} {Hc : X ⥤ X''}
    {F : X ⥤ Y} {F' : X' ⥤ Y'} {F'' : X'' ⥤ Y''}
    {G : Y ⥤ Y'} {G' : Y' ⥤ Y''} {Gc : Y ⥤ Y''}
    {P P₂ : X ⥤ Y'} {Q Q₂ : X' ⥤ Y''} {R R₂ W : X ⥤ Y''}
    (nH : H ⋙ H' ≅ Hc) (nG : G ⋙ G' ≅ Gc)
    (a : H ⋙ F' ≅ P) (b : F ⋙ G ≅ P₂)
    (a' : H' ⋙ F'' ≅ Q) (b' : F' ⋙ G' ≅ Q₂)
    (a₀ : Hc ⋙ F'' ≅ R) (b₀ : F ⋙ Gc ≅ R₂)
    (d : H ⋙ Q ≅ R) (e : P₂ ⋙ G' ≅ R₂) (k : P ⋙ G' ≅ W) (m : H ⋙ Q₂ ≅ W)
    (esq : P = P₂) (esq' : Q = Q₂) (eouter : R = R₂) (eWR : W = R₂) (eRW : R = W)
    (h1 : ∀ M, a'.hom.app (H.obj M) ≫ d.hom.app M =
      F''.map (nH.hom.app M) ≫ a₀.hom.app M)
    (h2 : ∀ M, nG.hom.app (F.obj M) ≫ b₀.hom.app M =
      G'.map (b.hom.app M) ≫ e.hom.app M)
    (h3 : ∀ M, b'.hom.app (H.obj M) ≫ m.hom.app M =
      G'.map (a.hom.app M) ≫ k.hom.app M)
    (h4 : ∀ M, G'.map ((transportNatTrans esq).app M) ≫ e.hom.app M =
      k.hom.app M ≫ (transportNatTrans eWR).app M)
    (h5 : ∀ M, (transportNatTrans esq').app (H.obj M) ≫ m.hom.app M =
      d.hom.app M ≫ (transportNatTrans eRW).app M)
    (M : X) :
    F''.map (nH.inv.app M) ≫
        (a'.hom.app (H.obj M) ≫ (transportNatTrans esq').app (H.obj M) ≫
          b'.inv.app (H.obj M)) ≫
        G'.map (a.hom.app M ≫ (transportNatTrans esq).app M ≫ b.inv.app M) ≫
        nG.hom.app (F.obj M) =
      a₀.hom.app M ≫ (transportNatTrans eouter).app M ≫ b₀.inv.app M := by
  apply (cancel_mono (b₀.hom.app M)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [h2 M]
  simp only [← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [Functor.map_comp, Category.assoc, h4 M, ← reassoc_of% (h3 M)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% (h5 M), transportNatTrans_app_trans eRW eWR eouter M, reassoc_of% (h1 M)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  exact CategoryTheory.Functor.map_id_comp _ _

/-- **Horizontal composition for adjoint mates**: if the three squares of left adjoints compose,
so do the mates of their right adjoints.

The outer two square comparisons are given by their components `sa` and `s₀a`, and the middle one
by its three factors `x'`, `y'`, `z'`, so that the naturality the argument needs is the naturality
of those factors and no comparison of a transformation with its components is required at the
concrete types. -/
theorem baseChangeMate_horizontal {A A' A'' B B' B'' : Type*}
    [Category* A] [Category* A'] [Category* A''] [Category* B] [Category* B'] [Category* B'']
    {F : B ⥤ A} {R : A ⥤ B} {F' : B' ⥤ A'} {R' : A' ⥤ B'} {F'' : B'' ⥤ A''} {R'' : A'' ⥤ B''}
    (adj : F ⊣ R) (adj' : F' ⊣ R') (adj'' : F'' ⊣ R'')
    {G : A ⥤ A'} {G' : A' ⥤ A''} {H : B ⥤ B'} {H' : B' ⥤ B''} {G₀ : A ⥤ A''} {H₀ : B ⥤ B''}
    (eG : G ⋙ G' ≅ G₀) (eH : H ⋙ H' ≅ H₀)
    (sa : ∀ M : B, (H ⋙ F').obj M ⟶ (F ⋙ G).obj M)
    {P₁ P₂ : B' ⥤ A''} (x' : H' ⋙ F'' ⟶ P₁) (y' : P₁ ⟶ P₂) (z' : P₂ ⟶ F' ⋙ G')
    (s₀a : ∀ M : B, (H₀ ⋙ F'').obj M ⟶ (F ⋙ G₀).obj M)
    (hs : ∀ M, F''.map (eH.inv.app M) ≫
      (x'.app (H.obj M) ≫ y'.app (H.obj M) ≫ z'.app (H.obj M)) ≫
      G'.map (sa M) ≫ eG.hom.app (F.obj M) = s₀a M)
    (K : A) (c : H.obj (R.obj K) ⟶ R'.obj (G.obj K))
    (c' : H'.obj (R'.obj (G.obj K)) ⟶ R''.obj (G'.obj (G.obj K)))
    (c₀ : H₀.obj (R.obj K) ⟶ R''.obj (G₀.obj K))
    (hc : (adj'.homEquiv _ _).symm c = sa (R.obj K) ≫ G.map (adj.counit.app K))
    (hc' : (adj''.homEquiv _ _).symm c' =
      (x'.app (R'.obj (G.obj K)) ≫ y'.app (R'.obj (G.obj K)) ≫ z'.app (R'.obj (G.obj K))) ≫
        G'.map (adj'.counit.app (G.obj K)))
    (hc₀ : (adj''.homEquiv _ _).symm c₀ = s₀a (R.obj K) ≫ G₀.map (adj.counit.app K)) :
    eH.inv.app (R.obj K) ≫ H'.map c ≫ c' ≫ R''.map (eG.hom.app K) = c₀ := by
  apply (adj''.homEquiv _ _).symm.injective
  rw [adj''.homEquiv_naturality_left_symm, adj''.homEquiv_naturality_left_symm,
    adj''.homEquiv_naturality_right_symm, hc', hc₀]
  simp only [Category.assoc]
  rw [comp₃_app_naturality_assoc x' y' z' c, ← G'.map_comp_assoc]
  change F''.map (eH.inv.app (R.obj K)) ≫ x'.app (H.obj (R.obj K)) ≫
      y'.app (H.obj (R.obj K)) ≫ z'.app (H.obj (R.obj K)) ≫
      G'.map ((adj'.homEquiv _ _).symm c) ≫ eG.hom.app K = _
  rw [hc, ← hs (R.obj K), Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun t => F''.map (eH.inv.app (R.obj K)) ≫ x'.app (H.obj (R.obj K)) ≫
      y'.app (H.obj (R.obj K)) ≫ z'.app (H.obj (R.obj K)) ≫ G'.map (sa (R.obj K)) ≫ t)
    (natTrans_comp_naturality eG.hom (adj.counit.app K))

/-- Two mutually inverse square comparisons: a composition isomorphism, a transport along an
equality of functors and the inverse of a second composition isomorphism, against the same data
for the transposed square. -/
theorem squareComparison_comp_symm {A B : Type*} [Category* A] [Category* B]
    {F G P Q : A ⥤ B} (u : F ≅ P) (v : G ≅ Q) (e : P = Q) (e' : Q = P) (M : A) :
    (u.hom.app M ≫ (transportNatTrans e).app M ≫ v.inv.app M) ≫
        (v.hom.app M ≫ (transportNatTrans e').app M ≫ u.inv.app M) = 𝟙 (F.obj M) := by
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, transportNatTrans_app,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.hom_inv_id_app]

/-- Pasting of 2-squares, reduced to one identity of morphisms at each object.

An identity between an outer 2-square and the vertical composite of two inner ones, whiskered
with comparisons of the two composite legs, is componentwise exactly the factorization of the
outer square's component into the four factors on the right. -/
theorem twoSquare_paste_of_app {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
    {Tl : A ⥤ B} {Ll : A ⥤ C} {Rl : B ⥤ D} {Tu : C ⥤ D} {Lu : C ⥤ E} {Ru : D ⥤ F}
    {Bu : E ⥤ F} {Lo : A ⥤ E} {Ro : B ⥤ F} {Cl Pl : A ⥤ D} {Cu Pu : C ⥤ F} {Co Po : A ⥤ F}
    (ego₁ : Tl ⋙ Ro ⟶ Po) (ego₂ : Po ⟶ Co) (efo : Co ⟶ Lo ⋙ Bu) (eg₂₁ : Tl ⋙ Rl ⟶ Pl)
    (eg₂₂ : Pl ⟶ Cl) (ef₂ : Cl ⟶ Ll ⋙ Tu) (eg₁₁ : Tu ⋙ Ru ⟶ Pu) (eg₁₂ : Pu ⟶ Cu)
    (ef₁ : Cu ⟶ Lu ⋙ Bu) (cL : Ll ⋙ Lu ⟶ Lo) (cR : Ro ⟶ Rl ⋙ Ru)
    (d₀ : ∀ M, Po.obj M ⟶ Co.obj M) (hd₀ : ∀ M, ego₂.app M = d₀ M)
    (d₂ : ∀ M, Pl.obj M ⟶ Cl.obj M) (hd₂ : ∀ M, eg₂₂.app M = d₂ M)
    (d₁ : ∀ N, Pu.obj N ⟶ Cu.obj N) (hd₁ : ∀ N, eg₁₂.app N = d₁ N)
    (h : ∀ M, ego₁.app M ≫ d₀ M ≫ efo.app M = cR.app (Tl.obj M) ≫
      Ru.map (eg₂₁.app M ≫ d₂ M ≫ ef₂.app M) ≫
      (eg₁₁.app (Ll.obj M) ≫ d₁ (Ll.obj M) ≫ ef₁.app (Ll.obj M)) ≫ Bu.map (cL.app M)) :
    TwoSquare.mk Tl Lo Ro Bu (ego₁ ≫ ego₂ ≫ efo) =
      ((TwoSquare.mk Tl Ll Rl Tu (eg₂₁ ≫ eg₂₂ ≫ ef₂) ≫ᵥ
        TwoSquare.mk Tu Lu Ru Bu (eg₁₁ ≫ eg₁₂ ≫ ef₁)).whiskerLeft cL).whiskerRight cR := by
  refine NatTrans.ext (funext fun M => ?_)
  have hM := h M
  rw [← hd₀ M, ← hd₂ M, ← hd₁ (Ll.obj M)] at hM
  simpa [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight, Functor.map_comp,
    Category.assoc] using hM

/-- **Pasting of mates, with every functor and adjunction a variable.**

If an outer 2-square is the vertical composite of two inner ones whiskered with comparisons `cL`,
`cR` of the two composite legs, then its mate is the horizontal composite of the two inner mates
whiskered with the conjugates `dL`, `dR` of those comparisons. -/
theorem mate_twoSquare_paste {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
    {Tl : A ⥤ B} {Ll : A ⥤ C} {Rl : B ⥤ D} {Tu : C ⥤ D} {Lu : C ⥤ E} {Ru : D ⥤ F}
    {Bu : E ⥤ F} {Lo : A ⥤ E} {Ro : B ⥤ F} {RLl : C ⥤ A} {RRl : D ⥤ B} {RLu : E ⥤ C}
    {RRu : F ⥤ D} {RLo : E ⥤ A} {RRo : F ⥤ B} (adjLl : Ll ⊣ RLl) (adjRl : Rl ⊣ RRl)
    (adjLu : Lu ⊣ RLu) (adjRu : Ru ⊣ RRu) (adjLo : Lo ⊣ RLo) (adjRo : Ro ⊣ RRo)
    (Sl : TwoSquare Tl Ll Rl Tu) (Su : TwoSquare Tu Lu Ru Bu) (So : TwoSquare Tl Lo Ro Bu)
    (cL : Ll ⋙ Lu ⟶ Lo) (cR : Ro ⟶ Rl ⋙ Ru) (dL : RLo ⟶ RLu ⋙ RLl) (dR : RRu ⋙ RRl ⟶ RRo)
    (hSo : So = ((Sl ≫ᵥ Su).whiskerLeft cL).whiskerRight cR)
    (hdL : conjugateEquiv adjLo (adjLl.comp adjLu) cL = dL)
    (hdR : conjugateEquiv (adjRl.comp adjRu) adjRo cR = dR) :
    mateEquiv adjLo adjRo So =
      ((mateEquiv adjLu adjRu Su ≫ₕ mateEquiv adjLl adjRl Sl).whiskerTop dL).whiskerBottom dR := by
  subst hSo
  subst hdL
  subst hdR
  rw [mateEquiv_conjugateEquiv_vcomp adjLo (adjRl.comp adjRu) adjRo,
    conjugateEquiv_mateEquiv_vcomp adjLo (adjLl.comp adjLu) (adjRl.comp adjRu), mateEquiv_hcomp]

/-- **The conjugate of an isomorphism of left adjoints is the canonical comparison of the right
adjoints.**  For adjunctions `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` and an isomorphism
`cmp : L₁ ≅ L₂`, the conjugate of `cmp.inv` is the comparison of `R₁` and `R₂` as two right
adjoints of `L₂`. -/
theorem conjugateEquiv_iso_inv {A B : Type*} [Category* A] [Category* B]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (cmp : L₁ ≅ L₂) :
    conjugateEquiv adj₁ adj₂ cmp.inv =
      (Adjunction.rightAdjointUniq (adj₁.ofNatIsoLeft cmp) adj₂).hom := by
  ext Y
  apply (adj₂.homEquiv (R₁.obj Y) Y).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    conjugateEquiv_counit adj₁ adj₂ cmp.inv Y, Adjunction.rightAdjointUniq_hom_app_counit]
  simp

/-! ### Transport of the derived pullback along an equality of morphisms -/

section Transport

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {m₁ m₂ : RingedToposSiteHom X Y}
  [(pullbackOnHomotopy m₁).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy m₂).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Equal morphisms of ringed topoi have equal derived pullbacks.

This is the equality of functors underlying
`Stacks.Cohomology.DerivedBaseChangeOnTopoi.derivedPullbackCongr`, and like it, it cannot be
`congrArg derivedPullback`: the derived pullback takes a `HasLeftDerivedFunctor` instance argument
depending on the morphism, so it is not a function of the morphism alone. -/
theorem derivedPullback_eq (e : m₁ = m₂) : derivedPullback m₁ = derivedPullback m₂ := by
  subst e
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The transport of `derivedPullbackCongr` is the componentwise transport.

`derivedPullbackCongr` is built by substituting the equality of morphisms, so its components do
not reduce while that equality is a variable; `transportNatTrans` is a projection out of an
explicit structure and does.  This is the single bridge between the two spellings. -/
theorem derivedPullbackCongr_inv_app (e : m₁ = m₂)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullbackCongr e.symm).inv.app M = (transportNatTrans (derivedPullback_eq e)).app M := by
  subst e
  simp [derivedPullbackCongr]

end Transport

/-! ### Compatibility of the composition comparison with an equality of morphisms -/

section Congr

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Compatibility of the Stacks 0D6D comparison with an equality of the inner morphism.** -/
theorem derivedPullbackCompComparison_congr_left (f f' : RingedToposSiteHom X Y) (e : f = f')
    (g : RingedToposSiteHom Y Z)
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy f').HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy g).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy (g.comp f')).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (transportNatTrans (derivedPullback_eq e)).app ((derivedPullback g).obj K) ≫
        (derivedPullbackCompComparison f' g).app K =
      (derivedPullbackCompComparison f g).app K ≫
        (transportNatTrans (derivedPullback_eq
          (congrArg (fun t : RingedToposSiteHom X Y => g.comp t) e))).app K := by
  subst e
  simp

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Compatibility of the Stacks 0D6D comparison with an equality of the outer morphism.** -/
theorem derivedPullbackCompComparison_congr_right (f : RingedToposSiteHom X Y)
    (g g' : RingedToposSiteHom Y Z) (e : g = g')
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy g).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy g').HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy (g'.comp f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (derivedPullback f).map ((transportNatTrans (derivedPullback_eq e)).app K) ≫
        (derivedPullbackCompComparison f g').app K =
      (derivedPullbackCompComparison f g).app K ≫
        (transportNatTrans (derivedPullback_eq
          (congrArg (fun t : RingedToposSiteHom Y Z => t.comp f) e))).app K := by
  subst e
  simp

end Congr

/-! ### The adjoint characterization with the transport split off -/

section Square

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (g' : RingedToposSiteHom X' X)
  (f' : RingedToposSiteHom X' Y') (g : RingedToposSiteHom Y' Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (f.comp g')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

/-- **The adjoint characterization of the derived base change map, with the transport split
off.**  The comparison of the two iterated derived pullbacks around the square is written as its
three factors: the composition isomorphism of Stacks 0D6D down the left and along the bottom, the
componentwise transport along the commutativity of the square, and the inverse of the composition
isomorphism along the top and down the right.

This is `Stacks.Cohomology.DerivedBaseChangeOnTopoi.derivedBaseChangeMap_adjoint` with the
transport of `derivedPullbackCongr` traded for `transportNatTrans`, which is the form the pasting
argument consumes. -/
theorem derivedBaseChangeMap_adjoint_split (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (hsq : g.comp f' = f.comp g')
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedAdjunction f' hmosf').homEquiv
        ((derivedPullback g).obj ((derivedPushforward f).obj K))
        ((derivedPullback g').obj K)).symm
        (derivedBaseChangeMap f g' f' g hmosf hmosg' hmosf' hmosg hsq K) =
      ((derivedPullbackCompIso f' g hmosf' hmosg).hom.app ((derivedPushforward f).obj K) ≫
          (transportNatTrans (derivedPullback_eq hsq)).app ((derivedPushforward f).obj K) ≫
          (derivedPullbackCompIso g' f hmosg' hmosf).inv.app ((derivedPushforward f).obj K)) ≫
        (derivedPullback g').map ((derivedAdjunction f hmosf).counit.app K) := by
  rw [derivedBaseChangeMap_adjoint]
  unfold derivedPullbackCompIsoLeft derivedPullbackCompIsoRight
  rw [Iso.trans_inv, NatTrans.comp_app, derivedPullbackCongr_inv_app hsq]
  simp only [Category.assoc]

/-- The derived base change 2-square is the mate of the comparison of the two iterated derived
pullbacks around the square, written out as its three factors. -/
theorem derivedBaseChangeSquare_eq_mateEquiv (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (hsq : g.comp f' = f.comp g') :
    derivedBaseChangeSquare f g' f' g hmosf hmosg' hmosf' hmosg hsq =
      mateEquiv (derivedAdjunction f hmosf) (derivedAdjunction f' hmosf')
        (TwoSquare.mk (derivedPullback g) (derivedPullback f) (derivedPullback f')
          (derivedPullback g')
          ((derivedPullbackCompIso f' g hmosf' hmosg).hom ≫
            (derivedPullbackCongr hsq.symm).inv ≫
            (derivedPullbackCompIso g' f hmosg' hmosf).inv)) :=
  rfl

/-- The derived base change map is the component of the derived base change 2-square. -/
theorem derivedBaseChangeMap_eq_app (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (hsq : g.comp f' = f.comp g')
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedBaseChangeMap f g' f' g hmosf hmosg' hmosf' hmosg hsq K =
      (derivedBaseChangeSquare f g' f' g hmosf hmosg' hmosf' hmosg hsq).app K :=
  rfl

end Square

/-! ### The composition isomorphism for the derived pushforward -/

section Pushforward

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]

/-- **The composition isomorphism for the unbounded derived pushforward**
`Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*`, for two composable morphisms of ringed topoi and with no further
hypothesis.

Both functors are right adjoint to the derived pullback along `g ∘ f`: the second by the derived
adjunction of Stacks 07A6, the first by the composite of the two derived adjunctions, transported
along the composition isomorphism of Stacks 0D6D.  The isomorphism is the canonical comparison of
two right adjoints of one functor, so it is by construction the adjoint of the Stacks 0D6D
isomorphism; that is the content of `conjugateEquiv_derivedPullbackCompIso_inv`. -/
def derivedPushforwardCompIso (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg : g.u.IsMorphismOfSites Z.J Y.J) :
    derivedPushforward f ⋙ derivedPushforward g ≅ derivedPushforward (g.comp f) :=
  Adjunction.rightAdjointUniq
    (((derivedAdjunction g hmosg).comp (derivedAdjunction f hmosf)).ofNatIsoLeft
      (derivedPullbackCompIso f g hmosf hmosg))
    (derivedAdjunction (g.comp f) (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))

/-- **The composition isomorphism for derived pushforward is the adjoint of the one for derived
pullback.**  The conjugate, with respect to the composite of the two derived adjunctions and the
derived adjunction for the composite, of the inverse of the Stacks 0D6D isomorphism is
`derivedPushforwardCompIso`. -/
theorem conjugateEquiv_derivedPullbackCompIso_inv (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg : g.u.IsMorphismOfSites Z.J Y.J) :
    conjugateEquiv ((derivedAdjunction g hmosg).comp (derivedAdjunction f hmosf))
        (derivedAdjunction (g.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))
        (derivedPullbackCompIso f g hmosf hmosg).inv =
      (derivedPushforwardCompIso f g hmosf hmosg).hom :=
  conjugateEquiv_iso_inv _ _ _

/-- The conjugate of the Stacks 0D6D isomorphism itself, in the direction that replaces the
derived adjunction for `g ∘ f` by the composite of the two derived adjunctions. -/
theorem conjugateEquiv_derivedPullbackCompIso_hom (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg : g.u.IsMorphismOfSites Z.J Y.J) :
    conjugateEquiv
        (derivedAdjunction (g.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))
        ((derivedAdjunction g hmosg).comp (derivedAdjunction f hmosf))
        (derivedPullbackCompIso f g hmosf hmosg).hom =
      (derivedPushforwardCompIso f g hmosf hmosg).inv := by
  have h := conjugateEquiv_comm
    (derivedAdjunction (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))
    ((derivedAdjunction g hmosg).comp (derivedAdjunction f hmosf))
    (α := (derivedPullbackCompIso f g hmosf hmosg).hom)
    (β := (derivedPullbackCompIso f g hmosf hmosg).inv) (Iso.inv_hom_id _)
  rw [conjugateEquiv_derivedPullbackCompIso_inv] at h
  exact (Iso.comp_hom_eq_id _).1 h

end Pushforward

/-! ### Pasting of two horizontally composable squares -/

section Horizontal

variable {X X' X'' Y Y' Y'' : RingedTopos.{u, u, u}}
  (f : RingedToposSiteHom X Y) (f' : RingedToposSiteHom X' Y')
  (f'' : RingedToposSiteHom X'' Y'') (g' : RingedToposSiteHom X' X)
  (g'' : RingedToposSiteHom X'' X') (g : RingedToposSiteHom Y' Y)
  (h : RingedToposSiteHom Y'' Y')

/-- **The outer rectangle of two horizontally composable commutative squares commutes.**  No
associativity isomorphism intervenes: composition of morphisms of ringed topoi is strictly
associative. -/
theorem comp_rectangle (sq : g.comp f' = f.comp g') (sq' : h.comp f'' = f'.comp g'') :
    (g.comp h).comp f'' = f.comp (g'.comp g'') :=
  calc (g.comp h).comp f'' = g.comp (h.comp f'') := rfl
    _ = g.comp (f'.comp g'') := by rw [sq']
    _ = (g.comp f').comp g'' := rfl
    _ = (f.comp g').comp g'' := by rw [sq]
    _ = f.comp (g'.comp g'') := rfl

variable
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X''.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y''.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X''.J AddCommGrpCat.{u}] [X''.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y''.J AddCommGrpCat.{u}] [Y''.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f'').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y''.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g'').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy h).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp h)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g'.comp g'')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (f.comp g')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (h.comp f'')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (f'.comp g'')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy ((g.comp h).comp f'')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (f.comp (g'.comp g''))).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp (h.comp f''))).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy ((f.comp g').comp g'')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp (f'.comp g''))).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy ((g.comp f').comp g'')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

/-- **Horizontal composition of the comparisons of iterated derived pullbacks.**  For two
horizontally composable commutative squares of ringed topoi, the comparison of the two iterated
derived pullbacks around the outer rectangle is the horizontal composite of the comparisons for
the two squares, read through the composition isomorphisms of Stacks 0D6D for the two composite
horizontal legs.

This is the geometric input to Stacks 0E47 and, applied to the transposed diagram, to Stacks
0E46.  The only ingredient is the cocycle identity
`Stacks.Cohomology.DerivedBaseChangeComposition.derivedPullbackCompComparison_assoc` of Stacks
0D6D, applied to the three ways the rectangle's threefold composite can be bracketed, together
with the compatibility of the composition isomorphism with the two commutativity equalities. -/
theorem derivedSquareComparison_horizontal (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J) (hmosf'' : f''.u.IsMorphismOfSites Y''.J X''.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosg'' : g''.u.IsMorphismOfSites X'.J X''.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (hmosh : h.u.IsMorphismOfSites Y'.J Y''.J)
    (sq : g.comp f' = f.comp g') (sq' : h.comp f'' = f'.comp g'')
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullback f'').map ((derivedPullbackCompIso h g hmosh hmosg).inv.app M) ≫
        ((derivedPullbackCompIso f'' h hmosf'' hmosh).hom.app ((derivedPullback g).obj M) ≫
          (transportNatTrans (derivedPullback_eq sq')).app ((derivedPullback g).obj M) ≫
          (derivedPullbackCompIso g'' f' hmosg'' hmosf').inv.app ((derivedPullback g).obj M)) ≫
        (derivedPullback g'').map
          ((derivedPullbackCompIso f' g hmosf' hmosg).hom.app M ≫
            (transportNatTrans (derivedPullback_eq sq)).app M ≫
            (derivedPullbackCompIso g' f hmosg' hmosf).inv.app M) ≫
        (derivedPullbackCompIso g'' g' hmosg'' hmosg').hom.app ((derivedPullback f).obj M) =
      (derivedPullbackCompIso f'' (g.comp h) hmosf''
            (RingedToposSiteHom.isMorphismOfSites_comp_u h g hmosh hmosg)).hom.app M ≫
        (transportNatTrans (derivedPullback_eq (comp_rectangle f f' f'' g' g'' g h sq sq'))).app
          M ≫
        (derivedPullbackCompIso (g'.comp g'') f
            (RingedToposSiteHom.isMorphismOfSites_comp_u g'' g' hmosg'' hmosg') hmosf).inv.app
          M := by
  refine squareComparison_horizontal (derivedPullbackCompIso h g hmosh hmosg)
    (derivedPullbackCompIso g'' g' hmosg'' hmosg')
    (derivedPullbackCompIso f' g hmosf' hmosg) (derivedPullbackCompIso g' f hmosg' hmosf)
    (derivedPullbackCompIso f'' h hmosf'' hmosh) (derivedPullbackCompIso g'' f' hmosg'' hmosf')
    (derivedPullbackCompIso f'' (g.comp h) hmosf''
      (RingedToposSiteHom.isMorphismOfSites_comp_u h g hmosh hmosg))
    (derivedPullbackCompIso (g'.comp g'') f
      (RingedToposSiteHom.isMorphismOfSites_comp_u g'' g' hmosg'' hmosg') hmosf)
    (derivedPullbackCompIso (h.comp f'') g
      (RingedToposSiteHom.isMorphismOfSites_comp_u f'' h hmosf'' hmosh) hmosg)
    (derivedPullbackCompIso g'' (f.comp g') hmosg''
      (RingedToposSiteHom.isMorphismOfSites_comp_u g' f hmosg' hmosf))
    (derivedPullbackCompIso g'' (g.comp f') hmosg''
      (RingedToposSiteHom.isMorphismOfSites_comp_u f' g hmosf' hmosg))
    (derivedPullbackCompIso (f'.comp g'') g
      (RingedToposSiteHom.isMorphismOfSites_comp_u g'' f' hmosg'' hmosf') hmosg)
    (derivedPullback_eq sq) (derivedPullback_eq sq')
    (derivedPullback_eq (comp_rectangle f f' f'' g' g'' g h sq sq'))
    (derivedPullback_eq (congrArg (fun t : RingedToposSiteHom X' Y => t.comp g'') sq))
    (derivedPullback_eq (congrArg (fun t : RingedToposSiteHom X'' Y' => g.comp t) sq'))
    ?_ ?_ ?_ ?_ ?_ M
  all_goals intro N
  · exact app_of_whiskered_assoc (derivedPullbackCompComparison_assoc f'' h g) N
  · exact app_of_whiskered_assoc (derivedPullbackCompComparison_assoc g'' g' f) N
  · exact app_of_whiskered_assoc (derivedPullbackCompComparison_assoc g'' f' g) N
  · exact derivedPullbackCompComparison_congr_right g'' (g.comp f') (f.comp g') sq N
  · exact derivedPullbackCompComparison_congr_left (h.comp f'') (f'.comp g'') sq' g N

/-- **Stacks 0E47.**  For two horizontally composable commutative squares of ringed topoi, the
composite of the derived base change maps of the two squares, read through the composition
isomorphisms of Stacks 0D6D for the two composite horizontal legs, is the derived base change map
of the outer rectangle. -/
@[stacks 0E47]
theorem derivedBaseChangeMap_horizontal (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J) (hmosf'' : f''.u.IsMorphismOfSites Y''.J X''.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosg'' : g''.u.IsMorphismOfSites X'.J X''.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (hmosh : h.u.IsMorphismOfSites Y'.J Y''.J)
    (sq : g.comp f' = f.comp g') (sq' : h.comp f'' = f'.comp g'')
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPullbackCompIso h g hmosh hmosg).inv.app ((derivedPushforward f).obj K) ≫
        (derivedPullback h).map
          (derivedBaseChangeMap f g' f' g hmosf hmosg' hmosf' hmosg sq K) ≫
        derivedBaseChangeMap f' g'' f'' h hmosf' hmosg'' hmosf'' hmosh sq'
          ((derivedPullback g').obj K) ≫
        (derivedPushforward f'').map
          ((derivedPullbackCompIso g'' g' hmosg'' hmosg').hom.app K) =
      derivedBaseChangeMap f (g'.comp g'') f'' (g.comp h) hmosf
        (RingedToposSiteHom.isMorphismOfSites_comp_u g'' g' hmosg'' hmosg') hmosf''
        (RingedToposSiteHom.isMorphismOfSites_comp_u h g hmosh hmosg)
        (comp_rectangle f f' f'' g' g'' g h sq sq') K :=
  baseChangeMate_horizontal (derivedAdjunction f hmosf) (derivedAdjunction f' hmosf')
    (derivedAdjunction f'' hmosf'') (derivedPullbackCompIso g'' g' hmosg'' hmosg')
    (derivedPullbackCompIso h g hmosh hmosg)
    (fun N => (derivedPullbackCompIso f' g hmosf' hmosg).hom.app N ≫
      (transportNatTrans (derivedPullback_eq sq)).app N ≫
      (derivedPullbackCompIso g' f hmosg' hmosf).inv.app N)
    (derivedPullbackCompIso f'' h hmosf'' hmosh).hom
    (transportNatTrans (derivedPullback_eq sq'))
    (derivedPullbackCompIso g'' f' hmosg'' hmosf').inv
    (fun N => (derivedPullbackCompIso f'' (g.comp h) hmosf''
          (RingedToposSiteHom.isMorphismOfSites_comp_u h g hmosh hmosg)).hom.app N ≫
      (transportNatTrans (derivedPullback_eq
        (comp_rectangle f f' f'' g' g'' g h sq sq'))).app N ≫
      (derivedPullbackCompIso (g'.comp g'') f
        (RingedToposSiteHom.isMorphismOfSites_comp_u g'' g' hmosg'' hmosg') hmosf).inv.app N)
    (derivedSquareComparison_horizontal f f' f'' g' g'' g h hmosf hmosf' hmosf'' hmosg' hmosg''
      hmosg hmosh sq sq')
    K _ _ _
    (derivedBaseChangeMap_adjoint_split f g' f' g hmosf hmosg' hmosf' hmosg sq K)
    (derivedBaseChangeMap_adjoint_split f' g'' f'' h hmosf' hmosg'' hmosf'' hmosh sq'
      ((derivedPullback g').obj K))
    (derivedBaseChangeMap_adjoint_split f (g'.comp g'') f'' (g.comp h) hmosf
      (RingedToposSiteHom.isMorphismOfSites_comp_u g'' g' hmosg'' hmosg') hmosf''
      (RingedToposSiteHom.isMorphismOfSites_comp_u h g hmosh hmosg)
      (comp_rectangle f f' f'' g' g'' g h sq sq') K)

end Horizontal

/-! ### Pasting of two vertically composable squares -/

section Stacked

variable {B B' C C' D D' : RingedTopos.{u, u, u}}
  (f : RingedToposSiteHom B C) (g : RingedToposSiteHom C D)
  (f' : RingedToposSiteHom B' C') (g' : RingedToposSiteHom C' D')
  (k : RingedToposSiteHom B' B) (l : RingedToposSiteHom C' C)
  (m : RingedToposSiteHom D' D)

/-- **The outer rectangle of two vertically composable commutative squares commutes.** -/
theorem comp_stack (htop : l.comp f' = f.comp k) (hbot : m.comp g' = g.comp l) :
    m.comp (g'.comp f') = (g.comp f).comp k :=
  (comp_rectangle m l k g' f' g f hbot.symm htop.symm).symm

variable
  [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify B.J AddCommGrpCat.{u}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify B'.J AddCommGrpCat.{u}] [B'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify C.J AddCommGrpCat.{u}] [C.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify C'.J AddCommGrpCat.{u}] [C'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify D.J AddCommGrpCat.{u}] [D.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify D'.J AddCommGrpCat.{u}] [D'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf C.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf C'.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D'.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy k).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy l).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf C.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy m).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g'.comp f')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D'.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (m.comp g')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp l)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (l.comp f')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf C.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (f.comp k)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf C.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (m.comp (g'.comp f'))).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy ((g.comp f).comp k)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp (f.comp k))).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy ((m.comp g').comp f')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp (l.comp f'))).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy ((g.comp l).comp f')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O)) (ComplexShape.up ℤ))]
  (hmosf : f.u.IsMorphismOfSites C.J B.J) (hmosg : g.u.IsMorphismOfSites D.J C.J)
  (hmosf' : f'.u.IsMorphismOfSites C'.J B'.J) (hmosg' : g'.u.IsMorphismOfSites D'.J C'.J)
  (hmosk : k.u.IsMorphismOfSites B.J B'.J) (hmosl : l.u.IsMorphismOfSites C.J C'.J)
  (hmosm : m.u.IsMorphismOfSites D.J D'.J)

/-- **The component identity behind the vertical pasting of two derived pullback squares.**

This is `derivedSquareComparison_horizontal` read on the transposed diagram and inverted: each of
the four factors of the transposed identity is a composite of comparison isomorphisms and
transports, whose inverse is the corresponding factor of the untransposed one. -/
theorem derivedPullbackSquare_paste_app (htop : l.comp f' = f.comp k)
    (hbot : m.comp g' = g.comp l)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O))) :
    (derivedPullbackCompIso (g'.comp f') m
            (RingedToposSiteHom.isMorphismOfSites_comp_u f' g' hmosf' hmosg') hmosm).hom.app M ≫
        (transportNatTrans
          (derivedPullback_eq (comp_stack f g f' g' k l m htop hbot))).app M ≫
        (derivedPullbackCompIso k (g.comp f) hmosk
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)).inv.app M =
      (derivedPullbackCompIso f' g' hmosf' hmosg').inv.app ((derivedPullback m).obj M) ≫
        (derivedPullback f').map
          ((derivedPullbackCompIso g' m hmosg' hmosm).hom.app M ≫
            (transportNatTrans (derivedPullback_eq hbot)).app M ≫
            (derivedPullbackCompIso l g hmosl hmosg).inv.app M) ≫
        ((derivedPullbackCompIso f' l hmosf' hmosl).hom.app ((derivedPullback g).obj M) ≫
          (transportNatTrans (derivedPullback_eq htop)).app ((derivedPullback g).obj M) ≫
          (derivedPullbackCompIso k f hmosk hmosf).inv.app ((derivedPullback g).obj M)) ≫
        (derivedPullback k).map ((derivedPullbackCompIso f g hmosf hmosg).hom.app M) :=
  (comp₄_inv
      ((derivedPullback k).map ((derivedPullbackCompIso f g hmosf hmosg).inv.app M))
      ((derivedPullback k).map ((derivedPullbackCompIso f g hmosf hmosg).hom.app M))
      ((derivedPullback f').map
        ((derivedPullbackCompIso l g hmosl hmosg).hom.app M ≫
          (transportNatTrans (derivedPullback_eq hbot.symm)).app M ≫
          (derivedPullbackCompIso g' m hmosg' hmosm).inv.app M))
      ((derivedPullback f').map
        ((derivedPullbackCompIso g' m hmosg' hmosm).hom.app M ≫
          (transportNatTrans (derivedPullback_eq hbot)).app M ≫
          (derivedPullbackCompIso l g hmosl hmosg).inv.app M))
      (by rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id])
      (squareComparison_comp_symm (derivedPullbackCompIso f' l hmosf' hmosl)
        (derivedPullbackCompIso k f hmosk hmosf) (derivedPullback_eq htop)
        (derivedPullback_eq htop.symm) ((derivedPullback g).obj M))
      (by
        rw [← Functor.map_comp,
          squareComparison_comp_symm (derivedPullbackCompIso g' m hmosg' hmosm)
            (derivedPullbackCompIso l g hmosl hmosg) (derivedPullback_eq hbot)
            (derivedPullback_eq hbot.symm) M, CategoryTheory.Functor.map_id])
      (Iso.inv_hom_id_app (derivedPullbackCompIso f' g' hmosf' hmosg')
        ((derivedPullback m).obj M))
      (squareComparison_comp_symm
        (derivedPullbackCompIso k (g.comp f) hmosk
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))
        (derivedPullbackCompIso (g'.comp f') m
          (RingedToposSiteHom.isMorphismOfSites_comp_u f' g' hmosf' hmosg') hmosm)
        (derivedPullback_eq (comp_rectangle m l k g' f' g f hbot.symm htop.symm))
        (derivedPullback_eq (comp_stack f g f' g' k l m htop hbot)) M)
      (derivedSquareComparison_horizontal m l k g' f' g f hmosm hmosl hmosk hmosg' hmosf' hmosg
        hmosf hbot.symm htop.symm M)).symm

/-- **Pasting of the comparisons of iterated derived pullbacks, vertically.**  For two vertically
composable commutative squares of ringed topoi, the comparison of the two iterated derived
pullbacks around the outer rectangle is the vertical composite of the comparisons for the two
squares, whiskered with the composition isomorphisms of Stacks 0D6D for the two composite vertical
legs. -/
theorem derivedPullbackSquare_paste (htop : l.comp f' = f.comp k) (hbot : m.comp g' = g.comp l) :
    TwoSquare.mk (derivedPullback m) (derivedPullback (g.comp f)) (derivedPullback (g'.comp f'))
        (derivedPullback k)
        ((derivedPullbackCompIso (g'.comp f') m
              (RingedToposSiteHom.isMorphismOfSites_comp_u f' g' hmosf' hmosg') hmosm).hom ≫
          (derivedPullbackCongr (comp_stack f g f' g' k l m htop hbot).symm).inv ≫
          (derivedPullbackCompIso k (g.comp f) hmosk
            (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)).inv) =
      ((TwoSquare.mk (derivedPullback m) (derivedPullback g) (derivedPullback g')
            (derivedPullback l)
            ((derivedPullbackCompIso g' m hmosg' hmosm).hom ≫
              (derivedPullbackCongr hbot.symm).inv ≫
              (derivedPullbackCompIso l g hmosl hmosg).inv) ≫ᵥ
          TwoSquare.mk (derivedPullback l) (derivedPullback f) (derivedPullback f')
            (derivedPullback k)
            ((derivedPullbackCompIso f' l hmosf' hmosl).hom ≫
              (derivedPullbackCongr htop.symm).inv ≫
              (derivedPullbackCompIso k f hmosk hmosf).inv)).whiskerLeft
          (derivedPullbackCompIso f g hmosf hmosg).hom).whiskerRight
        (derivedPullbackCompIso f' g' hmosf' hmosg').inv :=
  twoSquare_paste_of_app
    (derivedPullbackCompIso (g'.comp f') m
      (RingedToposSiteHom.isMorphismOfSites_comp_u f' g' hmosf' hmosg') hmosm).hom
    (derivedPullbackCongr (comp_stack f g f' g' k l m htop hbot).symm).inv
    (derivedPullbackCompIso k (g.comp f) hmosk
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg)).inv
    (derivedPullbackCompIso g' m hmosg' hmosm).hom
    (derivedPullbackCongr hbot.symm).inv
    (derivedPullbackCompIso l g hmosl hmosg).inv
    (derivedPullbackCompIso f' l hmosf' hmosl).hom
    (derivedPullbackCongr htop.symm).inv
    (derivedPullbackCompIso k f hmosk hmosf).inv
    (derivedPullbackCompIso f g hmosf hmosg).hom
    (derivedPullbackCompIso f' g' hmosf' hmosg').inv
    _ (derivedPullbackCongr_inv_app (comp_stack f g f' g' k l m htop hbot))
    _ (derivedPullbackCongr_inv_app hbot) _ (derivedPullbackCongr_inv_app htop)
    (derivedPullbackSquare_paste_app f g f' g' k l m hmosf hmosg hmosf' hmosg' hmosk hmosl hmosm
      htop hbot)

/-- **Pasting of the derived base change morphisms of functors, vertically.**  For two vertically
composable commutative squares of ringed topoi, the derived base change 2-square of the outer
rectangle is the horizontal composite of the 2-squares of the two squares, read through the
composition isomorphisms for the derived pushforward along the two composite vertical legs. -/
theorem derivedBaseChangeSquare_paste (htop : l.comp f' = f.comp k)
    (hbot : m.comp g' = g.comp l) :
    derivedBaseChangeSquare (g.comp f) k (g'.comp f') m
        (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) hmosk
        (RingedToposSiteHom.isMorphismOfSites_comp_u f' g' hmosf' hmosg') hmosm
        (comp_stack f g f' g' k l m htop hbot) =
      ((derivedBaseChangeSquare f k f' l hmosf hmosk hmosf' hmosl htop ≫ₕ
          derivedBaseChangeSquare g l g' m hmosg hmosl hmosg' hmosm hbot).whiskerTop
            (derivedPushforwardCompIso f g hmosf hmosg).inv).whiskerBottom
        (derivedPushforwardCompIso f' g' hmosf' hmosg').hom := by
  simp only [derivedBaseChangeSquare_eq_mateEquiv]
  exact mate_twoSquare_paste (derivedAdjunction g hmosg) (derivedAdjunction g' hmosg')
    (derivedAdjunction f hmosf) (derivedAdjunction f' hmosf')
    (derivedAdjunction (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))
    (derivedAdjunction (g'.comp f')
      (RingedToposSiteHom.isMorphismOfSites_comp_u f' g' hmosf' hmosg'))
    _ _ _ _ _ _ _
    (derivedPullbackSquare_paste f g f' g' k l m hmosf hmosg hmosf' hmosg' hmosk hmosl hmosm
      htop hbot)
    (conjugateEquiv_derivedPullbackCompIso_hom f g hmosf hmosg)
    (conjugateEquiv_derivedPullbackCompIso_inv f' g' hmosf' hmosg')

/-- **The vertical pasting law, for ringed topoi presented by morphisms of sites.**  For two
vertically composable commutative squares of ringed topoi whose arrows come from morphisms of the
underlying sites, the composite of the derived base change maps of the two squares, read through
the composition isomorphisms for the derived pushforward along the two composite vertical legs, is
the derived base change map of the outer rectangle.

Stacks 0E46 for arbitrary morphisms of ringed topoi is
`Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedBaseChangeMapOfTwoIso_vertical`. -/
@[stacks 0E46 "variant: the special case of squares of morphisms of ringed topoi presented by
morphisms of sites; the tag for arbitrary morphisms of ringed topoi is
Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedBaseChangeMapOfTwoIso_vertical"]
theorem derivedBaseChangeMap_comp (htop : l.comp f' = f.comp k) (hbot : m.comp g' = g.comp l)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B.O))) :
    (derivedPullback m).map ((derivedPushforwardCompIso f g hmosf hmosg).inv.app K) ≫
        derivedBaseChangeMap g l g' m hmosg hmosl hmosg' hmosm hbot
          ((derivedPushforward f).obj K) ≫
        (derivedPushforward g').map
          (derivedBaseChangeMap f k f' l hmosf hmosk hmosf' hmosl htop K) ≫
        (derivedPushforwardCompIso f' g' hmosf' hmosg').hom.app ((derivedPullback k).obj K) =
      derivedBaseChangeMap (g.comp f) k (g'.comp f') m
        (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) hmosk
        (RingedToposSiteHom.isMorphismOfSites_comp_u f' g' hmosf' hmosg') hmosm
        (comp_stack f g f' g' k l m htop hbot) K := by
  have hpaste := congr_app
    (derivedBaseChangeSquare_paste f g f' g' k l m hmosf hmosg hmosf' hmosg' hmosk hmosl hmosm
      htop hbot) K
  rw [derivedBaseChangeMap_eq_app, derivedBaseChangeMap_eq_app, derivedBaseChangeMap_eq_app]
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc] at hpaste
  exact hpaste.symm

end Stacked

end

end Stacks.Cohomology.DerivedBaseChangePasting

end
