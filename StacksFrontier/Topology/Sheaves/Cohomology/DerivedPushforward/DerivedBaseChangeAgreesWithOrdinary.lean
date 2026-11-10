module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DegreewiseAndDerivedPullbackSquare
import StacksCore.Tactic.StacksAttribute

/-!
# The derived base change map of a square agrees with the ordinary one

Let

```
X' --g'--> X
|f'        |f
S' --g-->  S
```

be a commutative square of ringed spaces.  Two base change maps are attached to it: the
**derived** one, `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` of
[Stacks, Tag 08HY], a map `Lg^* (Rf_* K) ⟶ Rf'_* (Lg'^* K)` of `D(𝒪_{S'})`, and the **ordinary**
one, got by applying the same mate construction to the degreewise adjunctions `k^* ⊣ k_*` of
[Stacks, Tag 0096] on the homotopy categories.  This file proves that they agree: the ordinary
map, localized to the derived category and conjugated by the four canonical comparisons
`Lk^* ⟶ k^*` and `k_* ⟶ Rk_*` of the square's four morphisms, *is* the derived map.

`derivedBaseChangeMap_adjoint` characterises the derived map only by its transpose under the
derived adjunctions, whereas sections see the ordinary unit and counit; an equation between a
derived and an ordinary map proved by rewriting one into the other would be a tautology.  Here
the two maps are built independently — the derived one from the derived adjunctions of
[Stacks, Tag 079W], the ordinary one from the degreewise adjunctions — and the comparison has
content: it is [Stacks, Tag 0FP1] at `f` and at `f'` together with the agreement of the two
comparisons of the square's iterated pullbacks.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare`: the **ordinary base change
  map** of the square, read on the unbounded homotopy categories — the mate, under the degreewise
  adjunctions of [Stacks, Tag 0096], of the comparison
  `Stacks.Cohomology.DerivedBaseChange.homotopyPullbackSquare` of the two iterated degreewise
  pullbacks.
* `Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeMap`: its component at a complex,
  a map `g^* (f_* M) ⟶ f'_* ((g')^* M)` of `K(𝒪_{S'})`.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_fac`: **the derived base change map
  of the square agrees with the ordinary one**, at a complex `M` of `𝒪_X`-modules.  This is the
  file's conclusion; everything else is one of its inputs.
* `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft_hom_naturality`: the
  composition isomorphism down the left of the square is natural, and
  `derivedPullbackCompIsoLeft_hom_naturality_pushforwardUnit`,
  `derivedPullbackCompIsoCanonical_inv_naturality_pushforwardUnit`: that naturality and the
  naturality of the inverse composition isomorphism along the top, at the two objects of
  `D(𝒪_S)` the splice needs them at.
* `Stacks.Cohomology.DerivedBaseChange.Mate.eq_of_transpose`: **the two base change maps of a
  square agree, objectwise.**  Given the two conjugated maps' transposes under the derived
  adjunction of `f'`, and the agreement of those two transposes, the derived base change map
  conjugated by the four comparisons is the ordinary one.  At a complex `M` of `𝒪_X`-modules the
  conclusion reads

  > `Lg^*(f_* M ⟶ Rf_* M) ≫ γ_{Q M} ≫ Rf'_*(Lg'^* Q M ⟶ Q (g'^* M))`
  > ` = (Lg^* Q (f_* M) ⟶ Q (g^* f_* M)) ≫ Q(γ^{ord}_M) ≫ (f'_* g'^* M ⟶ Rf'_* g'^* M)`.

* `Stacks.Cohomology.DerivedBaseChange.Mate.transpose_left₁`,
  `Stacks.Cohomology.DerivedBaseChange.Mate.transpose_left₂` and
  `Stacks.Cohomology.DerivedBaseChange.Mate.transpose_right`: those two transposes, computed
  from the identities that pin the mates down.  Except for the adjunction itself they are
  statements about morphisms of one category, not about functors.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeTransposeLeft₁`,
  `derivedBaseChangeTransposeLeft₂`, `derivedBaseChangeTransposeLeft` and
  `Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeTransposeRight`: the two halves of the
  left-hand transpose, their splice, and the whole of the right-hand one, at the canonical data.
* `Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare_counit_fac`,
  `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare_counit_fac`,
  `Stacks.Cohomology.DerivedBaseChange.derivedPullback_map_derivedAdjunction_counit_fac` and
  `Stacks.Cohomology.DerivedBaseChange.Qh_map_homotopyBaseChangeSquare_counit_fac`: the
  identities fed to those, at the canonical data of a square of ringed spaces — the
  transposition identity of each of the two base change maps and [Stacks, Tag 0FP1] at `f` and
  at `f'`, each pushed through the functor the splice needs it under.

## Implementation notes

*Why the core statements carry no `mateEquiv`.*  Each of the four maps the comparison conjugates
by, and each of the two base change maps, is a mate; but what the proof uses of a mate is only
the identity `CategoryTheory.mateEquiv_counit` asserts of it, and the transposition bijection is
injective, so that identity determines it.  Taking those identities as hypotheses means the
canonical instantiation can feed in
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_counit_fac`, which is
[Stacks, Tag 0FP1] as the source states it, with no mate calculus in between.

*Why the core statements are objectwise.*  The two transposition computations are formal
consequences of their hypotheses and nothing else; they use no functor but `Lf'^*` and `Rf'_*`,
and `Lf'^*` only to apply the counit.  Everything else enters as a morphism.  This is not
brevity: a version stated over the eight categories and sixteen functors of the cube is proved
just as easily, and is then uncheckable at the canonical data — the kernel exhausts its budget
on the delta steps between the derived functors and their definitions inside the implicit functor
arguments of five natural transformations at once.

*What the kernel's budget actually pays for here.*  The splice is the one place in this
file where the kernel runs out, and every form of it that fails fails for the same reason, which
is worth recording because it is not the reason one would guess.

The naturality of `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` is **not**
expensive.  `CategoryTheory.NatTrans.naturality` of its `hom`, stated with the source written
`(Lg^* ⋙ Lf'^*).map u` and the target `L(g' ≫ f)^*.map u`, passes in seconds even though the
isomorphism carries the transport `eqToIso (congrArg (fun h => Lh^*) sq.symm)`: a naturality
field is read off a transformation and never computed from it, so the transport is not reduced.
Splitting the isomorphism first — `rw [derivedPullbackCompIsoLeft_eq, Iso.trans_hom]` and then
naturality of each factor — is what fails, in both the `rw` chain and the
`CategoryTheory.NatTrans.comp_app` form; so the transport must be left alone rather than
decomposed.

What is expensive is **one object of `D(𝒪_S)` spelled two ways in one application.**  The
transposition identity `derivedBaseChangeSquare_counit_fac` spells the target of the comparison
`f_* M ⟶ Rf_* M` as `Rf_*.obj (Q M)`, while naturality taken at that comparison spells it
`(Q ⋙ Rf_*).obj M`.  Each spelling is fine on its own: `rfl` between the two is instantaneous,
the naturality square is checkable with either of them written out, and the transposition
identity is checkable against an `h₁` built by hand out of identities.  Asking
`Mate.transpose_left₁` to identify the two inside one application is not, in either direction —
`deterministic timeout`, and raising `maxHeartbeats` is not a way to finish.  The fix is the
two declarations
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft_hom_naturality_pushforwardUnit`
and `derivedPullbackCompIsoCanonical_inv_naturality_pushforwardUnit`: naturality at a *variable*
morphism between the objects spelled the way the transposition identity spells them.  A variable
morphism costs the kernel nothing to match, and the comparison is substituted for it only at the
application, where the one `rfl` it needs is the cheap one.

The same budget explains why `derivedBaseChangeTransposeLeft₁`,
`derivedBaseChangeTransposeLeft₂`, `derivedBaseChangeTransposeLeft` and
`homotopyBaseChangeTransposeRight` leave their types to be inferred.  A statement elaborated
afresh spells those objects however elaboration happens to spell them; comparing it with the
inferred type is the same unaffordable reconciliation.  Only
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_fac` writes its statement out, and it
can, because every object in it is already an argument of `Mate.eq_of_transpose`.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0FP1](https://stacks.math.columbia.edu/tag/0FP1)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Mate

section Objectwise

/-- Postcomposing a four-factor identity with a fifth morphism. -/
theorem comp_right₄ {C : Type*} [Category C] {A B₁ B₂ B₃ B₁' B₂' B₃' D E : C}
    {a : A ⟶ B₁} {b : B₁ ⟶ B₂} {c : B₂ ⟶ B₃} {d : B₃ ⟶ D}
    {a' : A ⟶ B₁'} {b' : B₁' ⟶ B₂'} {c' : B₂' ⟶ B₃'} {d' : B₃' ⟶ D}
    (h : a ≫ b ≫ c ≫ d = a' ≫ b' ≫ c' ≫ d') (k : D ⟶ E) :
    a ≫ b ≫ c ≫ d ≫ k = a' ≫ b' ≫ c' ≫ d' ≫ k := by
  simpa only [Category.assoc] using congrArg (· ≫ k) h

/-- Splicing two factorizations: if a three-factor composite factors as `p₀ ≫ m` and `m ≫ c`
is `G`, then appending `c` to the three factors gives `p₀ ≫ G`. -/
theorem comp_of_comp {C : Type*} [Category C] {A B₁ B₂ B₃ P₀ D : C}
    {a : A ⟶ B₁} {b : B₁ ⟶ B₂} {e : B₂ ⟶ B₃} {p₀ : A ⟶ P₀} {m : P₀ ⟶ B₃} {c : B₃ ⟶ D}
    {G : P₀ ⟶ D} (h : a ≫ b ≫ e = p₀ ≫ m) (h' : m ≫ c = G) :
    a ≫ b ≫ e ≫ c = p₀ ≫ G := by
  calc a ≫ b ≫ e ≫ c = (a ≫ b ≫ e) ≫ c := by simp only [Category.assoc]
    _ = (p₀ ≫ m) ≫ c := by rw [h]
    _ = p₀ ≫ G := by rw [Category.assoc, h']

variable {DS DS' DX' KS' : Type*} [Category DS] [Category DS'] [Category DX'] [Category KS']
  {lf' : DS' ⥤ DX'} {rf' : DX' ⥤ DS'}
  {P R : DS} {Z Z' : KS'} {B₀ : DS'}
  {Y Y' W₁ W₂ W₃ W₄ W₅ W₆ V₁ V₂ V₃ : DX'}
  {q : W₁ ⟶ W₂} {r : W₂ ⟶ Y}
  {s : W₃ ⟶ W₁} {q₀ : W₃ ⟶ W₄} {t : W₄ ⟶ W₂}
  {t₀ : W₄ ⟶ W₅} {r₀ : W₅ ⟶ Y} {c₀ : W₅ ⟶ W₆} {w : W₆ ⟶ Y'}
  {y : V₁ ⟶ Y'} {z : V₂ ⟶ V₁} {z₀ : V₂ ⟶ V₃} {z₁ : V₃ ⟶ W₆}

/-- **The derived base change map of a square, transposed: the first two steps.**  Read `b` as
the derived pullback along `f'` of the derived base change map, `a` as the derived pullback along
`f' ⋙ g` of the comparison `f_* M ⟶ Rf_* M`, and `lf' ⊣ rf'` as the derived adjunction of `f'`.
`hγ` is then the transposition identity of the derived base change map and `h₁` is naturality of
the composition isomorphism down the left of the square at that comparison.

Only the adjunction appears; `a` and `b` are morphisms, not components of natural
transformations, which is what lets the canonical instantiation be a bare assignment with no
functor composite for the kernel to unfold. -/
theorem transpose_left₁ (adjLf' : lf' ⊣ rf') {A₀ A₁ : DX'}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ lf'.obj (rf'.obj Y)} {p : A₁ ⟶ W₁} {p₀ : A₀ ⟶ W₃}
    (hγ : b ≫ adjLf'.counit.app Y = p ≫ q ≫ r) (h₁ : a ≫ p = p₀ ≫ s) :
    a ≫ b ≫ adjLf'.counit.app Y = p₀ ≫ s ≫ q ≫ r := by
  rw [hγ, reassoc_of% h₁]

/-- **The derived base change map of a square, transposed: the last three steps.**  `h₂` is
naturality of the composition isomorphism along the top of the square, `h₃` is
[Stacks, Tag 0FP1] at `f` pulled back along `g'`, and `h₄` is naturality of the comparison for
`g'` at the degreewise counit of `f`. -/
theorem transpose_left₂ {c : Y ⟶ Y'} (h₂ : s ≫ q = q₀ ≫ t) (h₃ : t ≫ r = t₀ ≫ r₀)
    (h₄ : r₀ ≫ c = c₀ ≫ w) :
    (s ≫ q ≫ r) ≫ c = q₀ ≫ t₀ ≫ c₀ ≫ w := by
  simp only [Category.assoc]
  rw [reassoc_of% h₂, reassoc_of% h₃, h₄]

/-- **The ordinary base change map of a square, transposed.**  Read `qS'` as the localization
`K(𝒪_{S'}) ⥤ D(𝒪_{S'})`, `b` as the comparison `Lg^* ⟶ g^*` at `f_* M`, `o` as the ordinary base
change map and `v` as the comparison `f'_* ⟶ Rf'_*`.  Then `hv` is the transposition identity of
`v`, `h₅` is naturality of the comparison for `f'` at `o`, and `h₆` is the transposition
identity of the ordinary base change map pushed through the localization; the conclusion is the
transpose of the conjugated ordinary base change map, computed.

`qS'` is explicit for the reason given at
`Stacks.Cohomology.DerivedBaseChange.Mate.transpose_left₁`. -/
theorem transpose_right (qS' : KS' ⥤ DS') (adjLf' : lf' ⊣ rf')
    (b : B₀ ⟶ qS'.obj Z) {o : Z ⟶ Z'} {v : qS'.obj Z' ⟶ rf'.obj Y'}
    {x : lf'.obj (qS'.obj Z') ⟶ V₁} {x₀ : lf'.obj (qS'.obj Z) ⟶ V₂}
    (hv : lf'.map v ≫ adjLf'.counit.app Y' = x ≫ y)
    (h₅ : lf'.map (qS'.map o) ≫ x = x₀ ≫ z) (h₆ : z ≫ y = z₀ ≫ z₁ ≫ w) :
    lf'.map b ≫ lf'.map (qS'.map o) ≫ lf'.map v ≫ adjLf'.counit.app Y' =
      lf'.map b ≫ x₀ ≫ z₀ ≫ z₁ ≫ w := by
  rw [hv, reassoc_of% h₅, h₆]

/-- **The derived and the ordinary base change map of a square agree, objectwise.**  Given the
two transposes computed — `hleft` and `hright`, which for the square are
`Stacks.Cohomology.DerivedBaseChange.Mate.transpose_left₁` spliced with `transpose_left₂`, and
`transpose_right` — and their agreement `hEF`, which for the square is the agreement of the
degreewise with the derived comparison of the two iterated pullbacks, the derived base change
map conjugated by the four
comparisons is the ordinary one.  The transposition bijection of `lf' ⊣ rf'` is injective, which
is all this step is. -/
theorem eq_of_transpose (lg : DS ⥤ DS') (qS' : KS' ⥤ DS') (adjLf' : lf' ⊣ rf')
    (u : P ⟶ R) (γ : lg.obj R ⟶ rf'.obj Y) (c : Y ⟶ Y')
    (b : lg.obj P ⟶ qS'.obj Z) (o : Z ⟶ Z') (v : qS'.obj Z' ⟶ rf'.obj Y')
    {E F : lf'.obj (lg.obj P) ⟶ Y'}
    (hleft : (lg ⋙ lf').map u ≫ lf'.map γ ≫ adjLf'.counit.app Y ≫ c = E)
    (hright : lf'.map b ≫ lf'.map (qS'.map o) ≫ lf'.map v ≫ adjLf'.counit.app Y' = F)
    (hEF : F = E) :
    lg.map u ≫ γ ≫ rf'.map c = b ≫ qS'.map o ≫ v := by
  refine (adjLf'.homEquiv (lg.obj P) Y').symm.injective ?_
  simp only [Functor.comp_map] at hleft
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.counit_naturality]
  rw [hleft, hright, hEF]

end Objectwise

end Mate

section Canonical

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- **The ordinary base change map** of a commutative square of ringed spaces, as a morphism of
functors `f_* ⋙ g^* ⟶ (g')^* ⋙ f'_*` on the unbounded homotopy categories: the mate, under the
degreewise adjunctions `k^* ⊣ k_*` of [Stacks, Tag 0096], of the comparison
`Stacks.Cohomology.DerivedBaseChange.homotopyPullbackSquare` of the two iterated degreewise
pullbacks.

This is built in exactly the way `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare`
is built from the derived adjunctions, so the two are independent of one another; that they
agree is `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_fac`. -/
def homotopyBaseChangeSquare :
    TwoSquare ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePushforward f').mapHomotopyCategory (ComplexShape.up ℤ)) :=
  mateEquiv (homotopyPullbackPushforwardAdjunction f) (homotopyPullbackPushforwardAdjunction f')
    (homotopyPullbackSquare g' f' f g sq)

/-- **The ordinary base change map** `g^* (f_* M) ⟶ f'_* ((g')^* M)` of a commutative square of
ringed spaces, at a complex of `𝒪_X`-modules. -/
def homotopyBaseChangeMap
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    ((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ⟶
      ((modulePushforward f').mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  (homotopyBaseChangeSquare g' f' f g sq).app M

/-- Under the degreewise adjunction `(f')^* ⊣ f'_*`, the ordinary base change map is the
degreewise pullback along `g'` of the degreewise counit, transported across the two degreewise
composition isomorphisms.  This is `CategoryTheory.mateEquiv_counit`, the defining property of
the mate at a component.

The map is written as a component of
`Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare` rather than as
`Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeMap`, which is that component: this is
the hypothesis `ho` of `Stacks.Cohomology.DerivedBaseChange.Mate.comp_of_counit_fac` at the
canonical data, and a spelling the kernel has to reconcile there costs budget the application
cannot spare. -/
theorem homotopyBaseChangeSquare_counit_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    ((modulePullback f').mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((homotopyBaseChangeSquare g' f' f g sq).app M) ≫
        (homotopyPullbackPushforwardAdjunction f').counit.app
          (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M) =
      (pullbackOnHomotopyCompIsoLeft g' f' f g sq).hom.app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        (pullbackOnHomotopyCompIso g' f).inv.app
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
          ((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((homotopyPullbackPushforwardAdjunction f).counit.app M) := by
  rw [homotopyBaseChangeSquare,
    mateEquiv_counit (homotopyPullbackPushforwardAdjunction f)
      (homotopyPullbackPushforwardAdjunction f') (homotopyPullbackSquare g' f' f g sq) M,
    homotopyPullbackSquare_app, Category.assoc]

/-- Under the derived adjunction `Lf'^* ⊣ Rf'_*`, the derived base change map is the derived
pullback along `g'` of the derived counit, transported across the two composition isomorphisms.
This is `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint`, with the transpose
written out as a composite with the counit. -/
theorem derivedBaseChangeSquare_counit_fac
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullback f').map ((derivedBaseChangeSquare g' f' f g sq).app K) ≫
        (derivedAdjunction f').counit.app ((derivedPullback g').obj K) =
      (derivedPullbackCompIsoLeft g' f' f g sq).hom.app ((derivedPushforward f).obj K) ≫
        (derivedPullbackCompIsoCanonical g' f).inv.app ((derivedPushforward f).obj K) ≫
          (derivedPullback g').map ((derivedAdjunction f).counit.app K) := by
  have h := derivedBaseChangeMap_adjoint g' f' f g sq K
  rwa [Adjunction.homEquiv_counit] at h

/-- **The composition isomorphism down the left of the square is natural.**  At a morphism `u` of
`D(𝒪_S)` the iterated derived pullback of `u`, down the left and along the bottom, followed by
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`, is that isomorphism followed by
the derived pullback of `u` along the common composite `g' ≫ f`.

This is `CategoryTheory.NatTrans.naturality` of the isomorphism's underlying transformation and
nothing more.  The transport `eqToIso (congrArg (fun h => Lh^*) sq.symm)` that
`derivedPullbackCompIsoLeft` carries is never reduced: a naturality field is read off a
transformation, not computed from it, and `CategoryTheory.eqToHom` of an equality of functors is
a transformation whatever that equality is. -/
theorem derivedPullbackCompIsoLeft_hom_naturality
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))} (u : K ⟶ L) :
    (derivedPullback g ⋙ derivedPullback f').map u ≫
        (derivedPullbackCompIsoLeft g' f' f g sq).hom.app L =
      (derivedPullbackCompIsoLeft g' f' f g sq).hom.app K ≫
        (derivedPullback (g' ≫ f)).map u :=
  (derivedPullbackCompIsoLeft g' f' f g sq).hom.naturality u

/-- **The naturality square of
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` at the comparison
`f_* M ⟶ Rf_* M`**, with the two objects of `D(𝒪_S)` spelled out.  This is the hypothesis `h₁` of
`Stacks.Cohomology.DerivedBaseChange.Mate.transpose_left₁` at the canonical data.

The morphism `u` is a variable rather than the comparison itself, and that is the whole content
of the declaration.  `Mate.transpose_left₁` identifies the map
`(derivedPullbackCompIsoLeft g' f' f g sq).hom.app _` occurring here with the one occurring in
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare_counit_fac`, which spells its object
`(derivedPushforward f).obj (DerivedCategory.Qh.obj M)`; naturality taken directly at the
comparison spells the same object `(DerivedCategory.Qh ⋙ derivedPushforward f).obj M`.  The two
are `rfl`-equal and the kernel checks that `rfl` on its own instantly, but reconciling them
*inside* the application of `transpose_left₁` exceeds its budget, in either direction.  Leaving
`u` a variable fixes the spelling here, where there is nothing else to pay for, and the
application is then free. -/
theorem derivedPullbackCompIsoLeft_hom_naturality_pushforwardUnit
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (u : DerivedCategory.Qh.obj
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ⟶
        (derivedPushforward f).obj (DerivedCategory.Qh.obj M)) :
    (derivedPullback g ⋙ derivedPullback f').map u ≫
        (derivedPullbackCompIsoLeft g' f' f g sq).hom.app
          ((derivedPushforward f).obj (DerivedCategory.Qh.obj M)) =
      (derivedPullbackCompIsoLeft g' f' f g sq).hom.app
          (DerivedCategory.Qh.obj
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPullback (g' ≫ f)).map u :=
  derivedPullbackCompIsoLeft_hom_naturality g' f' f g sq u

/-- **The naturality square of the composition isomorphism of [Stacks, Tag 0D5S] along the top of
the square, at the comparison `f_* M ⟶ Rf_* M`**, with the two objects of `D(𝒪_S)` spelled out.
This is the hypothesis `h₂` of `Stacks.Cohomology.DerivedBaseChange.Mate.transpose_left₂` at the
canonical data.

`u` is a variable for the reason given at
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft_hom_naturality_pushforwardUnit`:
the map this shares with `Mate.transpose_left₁` — the inverse composition isomorphism along the
top — must be spelled here exactly as `derivedBaseChangeSquare_counit_fac` spells it, and
naturality taken at the comparison itself spells it otherwise. -/
theorem derivedPullbackCompIsoCanonical_inv_naturality_pushforwardUnit
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (u : DerivedCategory.Qh.obj
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ⟶
        (derivedPushforward f).obj (DerivedCategory.Qh.obj M)) :
    (derivedPullback (g' ≫ f)).map u ≫
        (derivedPullbackCompIsoCanonical g' f).inv.app
          ((derivedPushforward f).obj (DerivedCategory.Qh.obj M)) =
      (derivedPullbackCompIsoCanonical g' f).inv.app
          (DerivedCategory.Qh.obj
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPullback f ⋙ derivedPullback g').map u :=
  (derivedPullbackCompIsoCanonical g' f).inv.naturality u

/-- **[Stacks, Tag 0FP1] at `f`, pulled back along `g'`.**  This is the hypothesis `h₃` of
`Stacks.Cohomology.DerivedBaseChange.Mate.eq_of_counit_fac` at the canonical data. -/
theorem derivedPullback_map_derivedAdjunction_counit_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPullback g').map ((derivedPullback f).map ((derivedPushforwardUnit f).app M)) ≫
        (derivedPullback g').map
          ((derivedAdjunction f).counit.app (DerivedCategory.Qh.obj M)) =
      (derivedPullback g').map ((derivedPullbackComparison f).app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPullback g').map (DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction f).counit.app M)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, derivedAdjunction_counit_fac f M]

/-- **The transposition identity of the ordinary base change map, localized.**  This is the
hypothesis `h₆` of `Stacks.Cohomology.DerivedBaseChange.Mate.eq_of_counit_fac` at the canonical
data. -/
theorem Qh_map_homotopyBaseChangeSquare_counit_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map (((modulePullback f').mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((homotopyBaseChangeSquare g' f' f g sq).app M)) ≫
        DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f').counit.app
          (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) =
      DerivedCategory.Qh.map ((pullbackOnHomotopyCompIsoLeft g' f' f g sq).hom.app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso g' f).inv.app
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
          DerivedCategory.Qh.map (((modulePullback g').mapHomotopyCategory
            (ComplexShape.up ℤ)).map
              ((homotopyPullbackPushforwardAdjunction f).counit.app M)) := by
  simpa only [Functor.map_comp] using congrArg DerivedCategory.Qh.map
    (homotopyBaseChangeSquare_counit_fac g' f' f g sq M)

/-- **The derived base change map of the square, conjugated and transposed: the first two
steps.**  `Stacks.Cohomology.DerivedBaseChange.Mate.transpose_left₁` at the canonical data, fed
the transposition identity of the derived base change map and the naturality of the composition
isomorphism down the left of the square at the comparison `f_* M ⟶ Rf_* M`.

Its type is not written out.  Both sides are composites of four maps between objects of
`D(𝒪_{X'})` spelled as iterated applications of derived functors; the kernel checks this
application against the type it *infers*, but a type elaborated afresh from such a statement
differs from the inferred one in how those objects are spelled, and reconciling the two exceeds
its budget. -/
theorem derivedBaseChangeTransposeLeft₁
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    type_of% (Mate.transpose_left₁ (derivedAdjunction f')
        (derivedBaseChangeSquare_counit_fac g' f' f g sq (DerivedCategory.Qh.obj M))
        (derivedPullbackCompIsoLeft_hom_naturality_pushforwardUnit g' f' f g sq M
          ((derivedPushforwardUnit f).app M))) :=
  Mate.transpose_left₁ (derivedAdjunction f')
    (derivedBaseChangeSquare_counit_fac g' f' f g sq (DerivedCategory.Qh.obj M))
    (derivedPullbackCompIsoLeft_hom_naturality_pushforwardUnit g' f' f g sq M
      ((derivedPushforwardUnit f).app M))

/-- **The derived base change map of the square, conjugated and transposed: the last three
steps.**  `Stacks.Cohomology.DerivedBaseChange.Mate.transpose_left₂` at the canonical data, fed
the naturality of the composition isomorphism along the top of the square, [Stacks, Tag 0FP1] at
`f` pulled back along `g'`, and the naturality of the comparison for `g'` at the degreewise
counit of `f`.

Its type is not written out, for the reason given at
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeTransposeLeft₁`. -/
theorem derivedBaseChangeTransposeLeft₂
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    type_of% (Mate.transpose_left₂
        (derivedPullbackCompIsoCanonical_inv_naturality_pushforwardUnit g' f M
          ((derivedPushforwardUnit f).app M))
        (derivedPullback_map_derivedAdjunction_counit_fac g' f M)
        ((derivedPullbackComparison g').naturality
          ((homotopyPullbackPushforwardAdjunction f).counit.app M))) :=
  Mate.transpose_left₂
    (derivedPullbackCompIsoCanonical_inv_naturality_pushforwardUnit g' f M
      ((derivedPushforwardUnit f).app M))
    (derivedPullback_map_derivedAdjunction_counit_fac g' f M)
    ((derivedPullbackComparison g').naturality
      ((homotopyPullbackPushforwardAdjunction f).counit.app M))

/-- **The derived base change map of the square, conjugated and transposed.**
`Stacks.Cohomology.DerivedBaseChange.Mate.comp_of_comp` of the two halves above: the transpose of
the conjugated derived base change map, computed down to the composition isomorphism down the
left, the inverse one along the top, [Stacks, Tag 0FP1] at `f` pulled back along `g'`, the
comparison for `g'`, and the degreewise counit of `f`.

Its type is not written out, for the reason given at
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeTransposeLeft₁`. -/
theorem derivedBaseChangeTransposeLeft
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    type_of% (Mate.comp_of_comp (derivedBaseChangeTransposeLeft₁ g' f' f g sq M)
        (derivedBaseChangeTransposeLeft₂ g' f M)) :=
  Mate.comp_of_comp (derivedBaseChangeTransposeLeft₁ g' f' f g sq M)
    (derivedBaseChangeTransposeLeft₂ g' f M)

/-- **The ordinary base change map of the square, conjugated and transposed.**
`Stacks.Cohomology.DerivedBaseChange.Mate.transpose_right` at the canonical data: the three
identities fed to it are [Stacks, Tag 0FP1] at `f'`, the naturality of the comparison for `f'`
at the ordinary base change map, and the transposition identity of the ordinary base change map
pushed through the localization.

Its type is not written out, for the reason given at
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeTransposeLeft`. -/
theorem homotopyBaseChangeTransposeRight
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    type_of% (Mate.transpose_right DerivedCategory.Qh (derivedAdjunction f')
        ((derivedPullbackComparison g).app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
        (derivedAdjunction_counit_fac f'
          (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
        ((derivedPullbackComparison f').naturality ((homotopyBaseChangeSquare g' f' f g sq).app M))
        (Qh_map_homotopyBaseChangeSquare_counit_fac g' f' f g sq M)) :=
  Mate.transpose_right DerivedCategory.Qh (derivedAdjunction f')
    ((derivedPullbackComparison g).app
      (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
    (derivedAdjunction_counit_fac f'
      (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
    ((derivedPullbackComparison f').naturality ((homotopyBaseChangeSquare g' f' f g sq).app M))
    (Qh_map_homotopyBaseChangeSquare_counit_fac g' f' f g sq M)

/-- **The derived base change map of a commutative square of ringed spaces agrees with the
ordinary one.**  At a complex `M` of `𝒪_X`-modules, the derived base change map of
[Stacks, Tag 08HY], precomposed with the derived pullback along `g` of the comparison
`f_* M ⟶ Rf_* M` and postcomposed with the derived pushforward along `f'` of the comparison
`Lg'^* (Q M) ⟶ Q ((g')^* M)`, is the ordinary base change map
`Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare` of [Stacks, Tag 0096] localized to
the derived category, conjugated by the comparison `Lg^* (Q (f_* M)) ⟶ Q (g^* (f_* M))` and the
comparison `f'_* ((g')^* M) ⟶ Rf'_* ((g')^* M)`.

The two maps are built independently — the derived one from the derived adjunctions of
[Stacks, Tag 079W], the ordinary one from the degreewise adjunctions of [Stacks, Tag 0096] — so
this has content: it is
`Stacks.Cohomology.DerivedBaseChange.comparison_comp_homotopyPullbackSquare`, which is
[Stacks, Tag 0D5S] down the left and along the top of the square, transposed under the derived
adjunction of `f'` using [Stacks, Tag 0FP1] at `f` and at `f'`.

The derived base change map is written as the component of
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare` that it is, rather than as
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`, for the reason recorded at
`Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare_counit_fac`. -/
theorem derivedBaseChangeMap_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPullback g).map ((derivedPushforwardUnit f).app M) ≫
        (derivedBaseChangeSquare g' f' f g sq).app (DerivedCategory.Qh.obj M) ≫
          (derivedPushforward f').map ((derivedPullbackComparison g').app M) =
      (derivedPullbackComparison g).app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map ((homotopyBaseChangeSquare g' f' f g sq).app M) ≫
          (derivedPushforwardUnit f').app
            (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  Mate.eq_of_transpose (derivedPullback g) DerivedCategory.Qh (derivedAdjunction f')
    ((derivedPushforwardUnit f).app M)
    ((derivedBaseChangeSquare g' f' f g sq).app (DerivedCategory.Qh.obj M))
    ((derivedPullbackComparison g').app M)
    ((derivedPullbackComparison g).app
      (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
    ((homotopyBaseChangeSquare g' f' f g sq).app M)
    ((derivedPushforwardUnit f').app
      (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
    (derivedBaseChangeTransposeLeft g' f' f g sq M)
    (homotopyBaseChangeTransposeRight g' f' f g sq M)
    (Mate.comp_right₄ (comparison_comp_homotopyPullbackSquare g' f' f g sq
        (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
      (DerivedCategory.Qh.map (((modulePullback g').mapHomotopyCategory
        (ComplexShape.up ℤ)).map ((homotopyPullbackPushforwardAdjunction f).counit.app M))))

end Canonical

end Stacks.Cohomology.DerivedBaseChange

end
