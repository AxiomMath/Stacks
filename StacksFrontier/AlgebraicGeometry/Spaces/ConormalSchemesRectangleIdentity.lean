module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalCoborderSquareAmbient
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionNaturalityAssembly
public import StacksFrontier.CategoryTheory.EqToHomAbsorption

/-!
# The schemes-side rectangle identity of Stacks 04G2 (2)

The reduction of part (2) of [Stacks Project, Tag 04G2] to the closed case stacks four squares
and reads one outer rectangle two ways; the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionNaturalityAssembly.lean` sets out
the layout.  Writing `L`, `L'` for the coborder lifts of the two immersions `j`, `j'`, `C`, `C'` for
their ambients, `J` for `AlgebraicGeometry.Space.coborderSquareLift`, `W` for its ambient,
`w = AlgebraicGeometry.Space.coborderSquareHom` and
`A = AlgebraicGeometry.Space.coborderSquareMap`, the four squares are
`S₁ = (J, L, 𝟙, w)`, `S₂ = (J, L', b, A)` and the two changes of ambient `S₃ = (L, j, 𝟙, ι)`,
`S₄ = (L', j', 𝟙, ι')`.  The rectangle `S₂` over `S₄` and the rectangle `S₁` over `S₃` stacked
over the square `(j, j', b, a)` are **the same** outer rectangle `(J, j', b, A ≫ ι')`, because
`AlgebraicGeometry.Space.squareAmbientMap_comp_openSubHom` gives `A ≫ ι' = (w ≫ ι) ≫ a`.

The backward step of the reduction takes as its hypothesis `ha` the statement that the two
readings of that rectangle agree on the Zariski side, as maps of sheaves of modules on the
source.  This file is that statement.

## Main results

* `Stacks.ClosedImmersion.conormalSheafMap_congr`: the canonical map of [Stacks Project,
  Tag 01R4] under equalities of **both** vertical morphisms of the square.
* `Stacks.ClosedImmersion.conormalSheafMap_comp_eq_comp` and
  `Stacks.ClosedImmersion.conormalSheafMap_comp_eq_comp₅`: **the rectangle identity at plain
  variables**, in the three-factor form and with the upper rectangle's own canonical map expanded
  into three factors in turn.
* `AlgebraicGeometry.Space.conormalSheafMap_coborderRectangle_eq`: **the rectangle identity at
  the geometric instance** — the hypothesis `ha` of
  `Stacks.CategoryTheory.square_transport_of_comp` for the backward step.
* `AlgebraicGeometry.Space.conormalCoborderRectangle_square` and
  `.conormalCoborderOuterRectangle_square`: the two stacks of the reduction, transported — the
  rectangle `S₁` over `S₃`, which is the backward step's **upper square**, and the rectangle `S₂`
  over `S₄`, which is its **outer rectangle**.  Each is one instantiation of
  `AlgebraicGeometry.Space.conormalStack_ambient_comp`.
* `AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso_zPow`: the
  unconditional closed naturality with its left-hand side folded into
  `AlgebraicGeometry.Space.kernelIdealZPowSquareMap`, which is the shape the forward step consumes.
* `AlgebraicGeometry.Space.conormalSheafMap_immersionCoborder_eq`: the canonical map of the
  change-of-ambient square read as `Stacks.Immersion.conormalSheafSelfIso`, used at `j` and at
  `j'`.
* `AlgebraicGeometry.Space.immersionCoborderLift_comp_openSubHom_id`,
  `.coborderSquareLift_comp_coborderRectangle_id`, `.coborderSquareMap_comp_openSubHom`,
  `.coborderSquare_comp_comm_representedSpaceMap_id` and
  `.coborderSquareMap_comp_comm_representedSpaceMap_id`: the squares and edges the above consume.
* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_eq_of_eq_left`: the comparison of
  [Stacks Project, Tag 03LU] moved on its **outer** argument.  Its docstring records the
  measurement that stops the backward step.

## What this file does not do

It does not prove part (2), and does not register [Stacks Project, Tag 04G2].  What remains is
`Stacks.CategoryTheory.square_transport_of_comp` at the two stacks above, and its hypothesis
`hTcomp` — the transport's composition law at a **leading** identity — is a kernel deterministic
timeout for the reason
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_eq_of_eq_left` records.  Its other
hypotheses are reachable: `hD` and `h₁` are the two stacks here, `ha` is the rectangle identity
here, `hki` is
`AlgebraicGeometry.Space.isIso_kernelIdealZPowSquareMap_coborderSquare_comp`, `hfaith` follows
from the instance `AlgebraicGeometry.Space.isEquivalence_modulePullback_id`, and `hTnat` is
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_naturality`.  Each of those still
needs its left-edge spelling matched to the others, by the bridges
`AlgebraicGeometry.Space.kernelIdealZPowSquareMap_eq_of_eq_left` and
`.kernelIdealZPowSquareMap_congr_right`.

## Why the identity is a congruence, and where its one junction is

Both readings are `Stacks.ClosedImmersion.conormalSheafMap_comp` of one rectangle, so each is
that rectangle's own canonical map and the identity is a congruence in the square's data.  The
right-hand verticals compose to one morphism of the site, so that half is
`Stacks.ClosedImmersion.conormalSheafMap_congr_right`, which stays inside one type.  The
left-hand verticals compose to `b ≫ 𝟙` on one side and to `(𝟙 ≫ 𝟙) ≫ b` on the other, and the
left-hand vertical **does** appear in the type — it is the morphism the source is pulled back
along — so that half moves the source object and is crossed by a `CategoryTheory.eqToHom`.

That junction is cheap, and the following hold at this neighbourhood's concrete data, each by
`rfl`:

* `((BigFppfOver.toScheme B S hS).map (𝟙 R)).toLRSHom.toShHom` is the identity of the ringed
  space, so passing to ringed spaces is definitionally unital as well as definitionally
  functorial — which is what makes `AlgebraicGeometry.Space.toShHom_square_of_comp_eq` usable at
  a composite edge by a type ascription alone;
* `AlgebraicGeometry.Scheme.Modules.pullback (B.inclusion.map b.left)` is
  `RingedSpaceModuleAdjunction.modulePullback` of the underlying morphism of ringed spaces, and
  `AlgebraicGeometry.Scheme.Modules.pullbackComp` is
  `RingedSpaceModuleAdjunction.modulePullbackComp` with its sides exchanged;
* the two spellings of the left-hand vertical give the **same object** after
  `RingedSpaceModuleAdjunction.modulePullback`, so the `CategoryTheory.eqToHom` above is supplied
  as `rfl` and absorbed by `CategoryTheory.eqToHom_comp_of_refl`.

Also, contrary to the docstring of
`AlgebraicGeometry.Space.representedSpaceMap_id` in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedKernelIdealSquareMapAgreement.lean`:
`AlgebraicGeometry.Space.representedSpaceMap (𝟙 T)` **is** the identity by `rfl`.

## Implementation notes

Everything except the last three declarations is at plain variables, and the geometric instance is
a single application of one abstract lemma to five squares and three junction proofs.  That
is the discipline the implementation notes of
`ConormalModuleImmersionNaturalityAssembly.lean` record: the comparisons here are built by
sheafification, so the kernel must never be asked to identify two definitionally equal spellings
of one of them, only two spellings of an **object** such a comparison is read at.

The three commutativities of the stacked rectangles are derived inside the abstract lemma rather
than taken as hypotheses, so that the conclusion mentions only the five squares a consumer
already has.  They occur only under `Stacks.ClosedImmersion.conormalSheafMap`, where proof
irrelevance makes the choice immaterial.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry

universe u

namespace Stacks.ClosedImmersion

open RingedSpaceModuleAdjunction

/-- **The canonical map of [Stacks Project, Tag 01R4] under equalities of both verticals of the
square.**

`Stacks.ClosedImmersion.conormalSheafMap_congr_right` moves the right-hand vertical morphism,
which does not appear in the type.  The left-hand one does — it is the morphism the source of the
map is pulled back along — so moving it changes the source object, and the equation carries a
`CategoryTheory.eqToHom` between the two sources.  A consumer whose two spellings of that
morphism are definitionally equal supplies `e` as `rfl` and absorbs the transport with
`CategoryTheory.eqToHom_comp_of_refl`. -/
theorem conormalSheafMap_congr {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'}
    {f₁ f₂ : Z ⟶ W} (hf : f₁ = f₂) {k₁ k₂ : Z' ⟶ W'} (hk : k₁ = k₂)
    (comm₁ : i ≫ k₁ = f₁ ≫ j) (comm₂ : i ≫ k₂ = f₂ ≫ j)
    (e : (modulePullback f₁).obj (conormalSheaf j) =
      (modulePullback f₂).obj (conormalSheaf j)) :
    conormalSheafMap comm₁ = eqToHom e ≫ conormalSheafMap comm₂ := by
  subst hf
  subst hk
  exact (conormalSheafMap_congr_right rfl comm₁ comm₂).trans
    (eqToHom_comp_of_refl e (conormalSheafMap comm₂)).symm

/-- Two commutative squares stacked vertically give a commutative outer rectangle. -/
private theorem comm_comp_of_comm {A₀ A₁ A₂ B₀ B₁ B₂ : RingedSpace.{u, u}}
    {i₀ : A₀ ⟶ B₀} {i₁ : A₁ ⟶ B₁} {i₂ : A₂ ⟶ B₂} {f₁ : A₀ ⟶ A₁} {k₁ : B₀ ⟶ B₁}
    {f₂ : A₁ ⟶ A₂} {k₂ : B₁ ⟶ B₂} (commA : i₀ ≫ k₁ = f₁ ≫ i₁) (commB : i₁ ≫ k₂ = f₂ ≫ i₂) :
    i₀ ≫ k₁ ≫ k₂ = (f₁ ≫ f₂) ≫ i₂ := by
  rw [← Category.assoc, commA, Category.assoc, commB, Category.assoc]

/-- **The rectangle identity.**  Two vertical stackings of commutative squares of ringed spaces
with the same outer rectangle — the same top row `i₀`, the same bottom row `i₂`, left-hand
verticals that compose to one morphism and right-hand verticals that compose to one morphism —
have the same three-factor composite of [Stacks Project, Tag 01R4] maps.

Both composites are the canonical map of the outer rectangle by
`Stacks.ClosedImmersion.conormalSheafMap_comp`, and the two readings of that rectangle are
identified by `Stacks.ClosedImmersion.conormalSheafMap_congr`.  The middle rows are
unconstrained: the two stackings may pass through entirely different squares, which is what the
reduction of part (2) of [Stacks Project, Tag 04G2] needs — there one reading goes through the
coborder lift of the lower immersion and the other through the immersion itself.

Nothing is assumed about closedness, immersions or quasi-coherence. -/
theorem conormalSheafMap_comp_eq_comp {A₀ A₁ A₂ B₀ B₁ B₂ B₁' : RingedSpace.{u, u}}
    {i₀ : A₀ ⟶ B₀} {i₁ : A₁ ⟶ B₁} {i₂ : A₂ ⟶ B₂} {i₁' : A₀ ⟶ B₁'}
    {f₁ : A₀ ⟶ A₁} {k₁ : B₀ ⟶ B₁} {f₂ : A₁ ⟶ A₂} {k₂ : B₁ ⟶ B₂}
    {f₁' : A₀ ⟶ A₀} {k₁' : B₀ ⟶ B₁'} {f₂' : A₀ ⟶ A₂} {k₂' : B₁' ⟶ B₂}
    (commA : i₀ ≫ k₁ = f₁ ≫ i₁) (commB : i₁ ≫ k₂ = f₂ ≫ i₂)
    (commA' : i₀ ≫ k₁' = f₁' ≫ i₁') (commB' : i₁' ≫ k₂' = f₂' ≫ i₂)
    (hf : f₁ ≫ f₂ = f₁' ≫ f₂') (hk : k₁ ≫ k₂ = k₁' ≫ k₂')
    (e : (modulePullback (f₁ ≫ f₂)).obj (conormalSheaf i₂) =
      (modulePullback (f₁' ≫ f₂')).obj (conormalSheaf i₂)) :
    (modulePullbackComp f₁ f₂).hom.app (conormalSheaf i₂) ≫
        (modulePullback f₁).map (conormalSheafMap commB) ≫ conormalSheafMap commA =
      eqToHom e ≫ (modulePullbackComp f₁' f₂').hom.app (conormalSheaf i₂) ≫
        (modulePullback f₁').map (conormalSheafMap commB') ≫ conormalSheafMap commA' := by
  have comm := comm_comp_of_comm commA commB
  have comm' := comm_comp_of_comm commA' commB'
  exact ((conormalSheafMap_comp commA commB comm).symm.trans
        (conormalSheafMap_congr hf hk comm comm' e)).trans
      (congrArg (fun t => eqToHom e ≫ t) (conormalSheafMap_comp commA' commB' comm'))

/-- **The rectangle identity with the upper rectangle's own canonical map expanded.**

`Stacks.ClosedImmersion.conormalSheafMap_comp_eq_comp` at a right-hand reading whose upper square
is itself a rectangle, stacked from `(i₀, i₁'', f₁'', k₁'')` over `(i₁'', i₁', f₂'', k₂'')`, so
that its canonical map is three factors in turn by
`Stacks.ClosedImmersion.conormalSheafMap_comp`.  This is the five-factor shape in which the
backward step of the reduction of part (2) of [Stacks Project, Tag 04G2] meets the identity: the
upper square of that stack is a rectangle, so its own statement arrives with its canonical map
already expanded.

**The upper rectangle's own left-hand vertical `f₁'` is a variable, with `f₁'' ≫ f₂'' = f₁'` as a
hypothesis, and not the composite itself.**  That is not a convenience.  At the geometric
instance the two are definitionally equal but differently spelled — `𝟙 ≫ 𝟙` against `𝟙` — and the
outer two factors of the right-hand side are read at `f₁'`, where the consumer has them, while the
inner three are read at the composite, where the composition law puts them.  Were the composite
used throughout, the two spellings would have to be identified **inside
`RingedSpaceModuleAdjunction.modulePullbackComp`**, a comparison built by sheafification, which
the implementation notes of this file record as the one crossing that must never be asked for.
Here each spelling is used where it arises and the two meet only on an **object**, through
`e₁`. -/
theorem conormalSheafMap_comp_eq_comp₅ {A₀ A₁ A₂ A₁'' B₀ B₁ B₂ B₁' B₁'' : RingedSpace.{u, u}}
    {i₀ : A₀ ⟶ B₀} {i₁ : A₁ ⟶ B₁} {i₂ : A₂ ⟶ B₂} {i₁' : A₀ ⟶ B₁'} {i₁'' : A₁'' ⟶ B₁''}
    {f₁ : A₀ ⟶ A₁} {k₁ : B₀ ⟶ B₁} {f₂ : A₁ ⟶ A₂} {k₂ : B₁ ⟶ B₂}
    {f₁' : A₀ ⟶ A₀} {k₁' : B₀ ⟶ B₁'} {f₂' : A₀ ⟶ A₂} {k₂' : B₁' ⟶ B₂}
    {f₁'' : A₀ ⟶ A₁''} {k₁'' : B₀ ⟶ B₁''} {f₂'' : A₁'' ⟶ A₀} {k₂'' : B₁'' ⟶ B₁'}
    (commA : i₀ ≫ k₁ = f₁ ≫ i₁) (commB : i₁ ≫ k₂ = f₂ ≫ i₂)
    (commA' : i₀ ≫ k₁' = f₁' ≫ i₁') (commB' : i₁' ≫ k₂' = f₂' ≫ i₂)
    (commA₁ : i₀ ≫ k₁'' = f₁'' ≫ i₁'') (commB₁ : i₁'' ≫ k₂'' = f₂'' ≫ i₁')
    (hf : f₁ ≫ f₂ = f₁' ≫ f₂') (hk : k₁ ≫ k₂ = k₁' ≫ k₂')
    (hf₁ : f₁'' ≫ f₂'' = f₁') (hk₁ : k₁'' ≫ k₂'' = k₁')
    (e : (modulePullback (f₁ ≫ f₂)).obj (conormalSheaf i₂) =
      (modulePullback (f₁' ≫ f₂')).obj (conormalSheaf i₂))
    (e₁ : (modulePullback f₁').obj (conormalSheaf i₁') =
      (modulePullback (f₁'' ≫ f₂'')).obj (conormalSheaf i₁')) :
    (modulePullbackComp f₁ f₂).hom.app (conormalSheaf i₂) ≫
        (modulePullback f₁).map (conormalSheafMap commB) ≫ conormalSheafMap commA =
      eqToHom e ≫ (modulePullbackComp f₁' f₂').hom.app (conormalSheaf i₂) ≫
        (modulePullback f₁').map (conormalSheafMap commB') ≫
          (eqToHom e₁ ≫ (modulePullbackComp f₁'' f₂'').hom.app (conormalSheaf i₁') ≫
            (modulePullback f₁'').map (conormalSheafMap commB₁) ≫ conormalSheafMap commA₁) := by
  have commA₁' := comm_comp_of_comm commA₁ commB₁
  refine (conormalSheafMap_comp_eq_comp commA commB commA' commB' hf hk e).trans ?_
  refine congrArg
    (fun t => eqToHom e ≫ (modulePullbackComp f₁' f₂').hom.app (conormalSheaf i₂) ≫
      (modulePullback f₁').map (conormalSheafMap commB') ≫ t) ?_
  exact (conormalSheafMap_congr hf₁.symm hk₁.symm commA' commA₁' e₁).trans
    (congrArg (fun t => eqToHom e₁ ≫ t) (conormalSheafMap_comp commA₁ commB₁ commA₁'))

end Stacks.ClosedImmersion

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section LeadingIdentity

attribute [local irreducible] modulePullback modulePullbackCompIso modulePullbackIdIso
  representedModuleObjPullbackIso representedAssociatedModulePullbackIso
  representedSmallEtaleModuleEquivalence

/-- **The comparison of [Stacks Project, Tag 03LU] at two equal OUTER morphisms**, with the two
transports of objects made explicit.

`AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_eq_of_eq` moves the inner morphism `g`;
the stack of the backward step of the reduction of part (2) of [Stacks Project, Tag 04G2] needs
the outer one moved instead, because there the junction is on the upper square's left edge — the
functor the whole step is taken along — and not on the lower square's.

Routed through `CategoryTheory.eqToHom` on objects for the reason recorded throughout this
neighbourhood: identifying the comparison itself at two definitionally equal spellings makes the
kernel unfold a sheafification, while identifying its source and target objects is a congruence
on the argument of `AlgebraicGeometry.Space.modulePullback`.

**This is the reason the backward step of the reduction of part (2) of
[Stacks Project, Tag 04G2] is not assembled in this file.**  At a *variable* outer morphism this
bridge is cheap: instantiated with `hff := (Category.comp_id f).symm` and both transports `rfl`,
at a variable `f`, a variable inner `g` and a variable module, it checks in about two seconds, and
so do the two object equalities on their own.  Specialised with `f :=
AlgebraicGeometry.Space.representedSpaceMap (𝟙 T₁)` — which is what the stack's upper left edge
is — the same instantiation is a **kernel deterministic timeout**: the kernel may now unfold
`representedSpaceMap (𝟙 T₁)` and then `AlgebraicGeometry.Space.modulePullback` of it, and it does.
No `attribute [local irreducible]` removes this, the kernel ignoring them.

This is the asymmetry that leaves
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_id_right` without a
leading-identity companion.  For a *trailing* identity the junction the transport's composition
law leaves is on the **inner** argument of the comparison, which
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_eq_of_eq` moves at a cost the kernel pays;
for a *leading* identity it is on the **outer** argument — the functor the whole step is taken
along — and specialising it is the wall above.  The transport's composition law is indexed by
morphisms of the site, while the stack's edge is `representedSpaceMap (𝟙 T₁) ≫ 𝟙`, which is
`representedSpaceMap` of nothing, so the junction cannot be kept at a variable and discharged by
substitution the way the other junctions of this neighbourhood are. -/
theorem modulePullbackCompIso_hom_app_eq_of_eq_left {W X Y : AlgebraicSpaces B S hS}
    {f f' : W ⟶ X} (hff : f = f') (g : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (e : (modulePullback B S hS g ⋙ modulePullback B S hS f).obj M =
      (modulePullback B S hS g ⋙ modulePullback B S hS f').obj M)
    (e' : (modulePullback B S hS (f' ≫ g)).obj M = (modulePullback B S hS (f ≫ g)).obj M) :
    (modulePullbackCompIso B S hS f g).hom.app M =
      eqToHom e ≫ (modulePullbackCompIso B S hS f' g).hom.app M ≫ eqToHom e' := by
  subst hff
  exact ((eqToHom_comp_of_refl e _).trans (comp_eqToHom_of_refl e' _)).symm

end LeadingIdentity

section Coborder

variable {R V : BigFppfOver B S hS} (j : R ⟶ V)
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)]

/-- **The change of ambient of [Stacks Project, Tag 04CE] as a commutative square of the site.**
`AlgebraicGeometry.Space.immersionCoborderLift_comp_openSubHom` with the identity in front, which
is the shape a commutative square takes.  The companion of
`AlgebraicGeometry.Space.coborderSquareLift_comp_coborderSquareHom_id` one level down. -/
theorem immersionCoborderLift_comp_openSubHom_id :
    immersionCoborderLift B S hS j ≫
        openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange = 𝟙 R ≫ j :=
  (immersionCoborderLift_comp_openSubHom B S hS j).trans (Category.id_comp _).symm

/-- **The canonical map of the change-of-ambient square is the change of ambient of
[Stacks Project, Tag 01R2].**

`Stacks.Immersion.conormalSheafMap_coborder_eq_conormalSheafSelfIso` at the represented immersion,
with the square's bottom edge moved from the inclusion of
`AlgebraicGeometry.Space.openSub` to `AlgebraicGeometry.Scheme.Opens.ι` by
`AlgebraicGeometry.Space.toScheme_map_openSubHom`.

**That move is propositional and must be made.**  The square's left edge and top edge need no
move: `((BigFppfOver.toScheme B S hS).map (𝟙 R)).toLRSHom.toShHom` is the identity of the ringed
space and `AlgebraicGeometry.Space.toScheme_map_immersionCoborderLift` holds, both by `rfl`.  The
bottom edge does not — `AlgebraicGeometry.Space.toScheme_map_openSubHom` is
`B.inclusion.map_preimage`, not `rfl` — so it is moved by
`Stacks.ClosedImmersion.conormalSheafMap_congr_right`, which stays inside one type because the
square's right-hand vertical does not appear in it.

This is what puts the canonical map of the change-of-ambient square into the spelling
`AlgebraicGeometry.Space.conormalChangeOfAmbientAgreement_transport` states its own map at. -/
theorem conormalSheafMap_immersionCoborder_eq :
    Stacks.ClosedImmersion.conormalSheafMap
        (toShHom_square_of_comp_eq B S hS (immersionCoborderLift B S hS j) j (𝟙 R)
          (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)
          (immersionCoborderLift_comp_openSubHom_id B S hS j)) =
      (Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R)).hom.app
          (Stacks.ClosedImmersion.conormalSheaf
            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
        (Stacks.Immersion.conormalSheafSelfIso ((BigFppfOver.toScheme B S hS).map j)).hom := by
  have hk : ((BigFppfOver.toScheme B S hS).map
          (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)).toLRSHom.toShHom =
      ((BigFppfOver.toScheme B S hS).map j).coborderRange.ι.toLRSHom.toShHom :=
    congrArg (fun m : ((BigFppfOver.toScheme B S hS).obj
        (openSub V ((BigFppfOver.toScheme B S hS).map j).coborderRange)) ⟶
        ((BigFppfOver.toScheme B S hS).obj V) => m.toLRSHom.toShHom)
      (toScheme_map_openSubHom B S hS V ((BigFppfOver.toScheme B S hS).map j).coborderRange)
  have comm₂ : ((BigFppfOver.toScheme B S hS).map j).liftCoborder.toLRSHom.toShHom ≫
      ((BigFppfOver.toScheme B S hS).map j).coborderRange.ι.toLRSHom.toShHom =
        𝟙 ((BigFppfOver.toScheme B S hS).obj R).toLocallyRingedSpace.toRingedSpace ≫
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom := by
    rw [← hk]
    exact toShHom_square_of_comp_eq B S hS (immersionCoborderLift B S hS j) j (𝟙 R)
      (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)
      (immersionCoborderLift_comp_openSubHom_id B S hS j)
  exact (Stacks.ClosedImmersion.conormalSheafMap_congr_right hk _ comm₂).trans
    (Stacks.Immersion.conormalSheafMap_coborder_eq_conormalSheafSelfIso
      ((BigFppfOver.toScheme B S hS).map j) comm₂)

end Coborder

section Square

attribute [local irreducible] RingedSpaceModuleAdjunction.modulePullback
  RingedSpaceModuleAdjunction.modulePullbackComp Stacks.ClosedImmersion.conormalSheafMap

variable {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [hj' : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j')]

/-- **The bottom edge of the outer rectangle, read the second way.**  The morphism of ambients of
the lifted square followed by the inclusion of the coborder ambient of `j'` is the morphism to the
coborder ambient of `j`, its inclusion, and then `a`.

This is `AlgebraicGeometry.Space.squareAmbientMap_comp_openSubHom` at the lifted square, with the
right-hand side rebracketed so that the two readings of the rectangle have their right-hand
verticals composed in the same order. -/
theorem coborderSquareMap_comp_openSubHom (hsq : j ≫ a = b ≫ j') :
    coborderSquareMap B S hS j j' b a hsq ≫
        openSubHom V' ((BigFppfOver.toScheme B S hS).map j').coborderRange =
      (coborderSquareHom B S hS j j' b a hsq ≫
          openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange) ≫ a := by
  rw [coborderSquareMap, coborderSquareHom, Category.assoc]
  exact squareAmbientMap_comp_openSubHom B S hS (immersionCoborderLift B S hS j) j' b
    (coborderAmbientMap B S hS j a) (coborderSquare_comm B S hS j j' b a hsq)

/-- **The coborder rectangle of the lifted square, as a commutative square of the site.**  The
closed factorisation of `j` through the ambient of the lifted square, followed by the morphism to
the coborder ambient of `j` and its inclusion, is `j` — with the identity in front.

This is the outer rectangle of `S₁` over `S₃` read with its left-hand vertical spelled as the
single morphism `𝟙 R`, which is where
`Stacks.ClosedImmersion.conormalSheafMap_comp_eq_comp₅` reads the outer two factors of its
right-hand side; `AlgebraicGeometry.Space.coborderSquare_comp_comm` is the same rectangle at the
represented spaces with the left-hand vertical spelled `𝟙 ≫ 𝟙`, which is where the cancellation
`AlgebraicGeometry.Space.isIso_kernelIdealZPowSquareMap_coborderSquare_comp` is stated. -/
theorem coborderSquareLift_comp_coborderRectangle_id (hsq : j ≫ a = b ≫ j') :
    coborderSquareLift B S hS j j' b a hsq ≫
        (coborderSquareHom B S hS j j' b a hsq ≫
          openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange) = 𝟙 R ≫ j :=
  (Category.assoc _ _ _).symm.trans
    (((congrArg
          (fun t => t ≫ openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)
          (coborderSquareLift_comp_coborderSquareHom B S hS j j' b a hsq)).trans
        (immersionCoborderLift_comp_openSubHom B S hS j)).trans (Category.id_comp _).symm)

/-- **The schemes-side rectangle identity of part (2) of [Stacks Project, Tag 04G2].**

The outer rectangle `(J, j', b, A ≫ ι')` of the reduction is read two ways — as the square over
the two coborder ambients stacked over the change of ambient at `j'`, and as the change of
ambient at `j` under the square over the ambient of the lifted square, all stacked over the
square `(j, j', b, a)` itself — and the two readings have the same canonical map of
[Stacks Project, Tag 01R4] on the Zariski side.

This is the hypothesis `ha` of `Stacks.CategoryTheory.square_transport_of_comp` for the backward
step of that reduction, as a map of sheaves of modules on the scheme underlying `R`.  Nothing is
assumed beyond the two immersions and the commutativity of the square; it is one application of
`Stacks.ClosedImmersion.conormalSheafMap_comp_eq_comp₅` to the six squares, with the
bottom edge moved by `AlgebraicGeometry.Space.coborderSquareMap_comp_openSubHom`, the left-hand
edge by the unit laws of the site, and the two object transports supplied as `rfl` and absorbed by
`CategoryTheory.eqToHom_comp_of_refl`. -/
theorem conormalSheafMap_coborderRectangle_eq (hsq : j ≫ a = b ≫ j') :
    (RingedSpaceModuleAdjunction.modulePullbackComp
            ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom
            ((BigFppfOver.toScheme B S hS).map (𝟙 R')).toLRSHom.toShHom).hom.app
          (Stacks.ClosedImmersion.conormalSheaf
            ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
        (RingedSpaceModuleAdjunction.modulePullback
              ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom).map
            (Stacks.ClosedImmersion.conormalSheafMap
              (toShHom_square_of_comp_eq B S hS (immersionCoborderLift B S hS j') j' (𝟙 R')
                (openSubHom V' ((BigFppfOver.toScheme B S hS).map j').coborderRange)
                (immersionCoborderLift_comp_openSubHom_id B S hS j'))) ≫
          Stacks.ClosedImmersion.conormalSheafMap
            (toShHom_square_of_comp_eq B S hS (coborderSquareLift B S hS j j' b a hsq)
              (immersionCoborderLift B S hS j') b (coborderSquareMap B S hS j j' b a hsq)
              (coborderSquareLift_comp_coborderSquareMap B S hS j j' b a hsq)) =
      (RingedSpaceModuleAdjunction.modulePullbackComp
              ((BigFppfOver.toScheme B S hS).map (𝟙 R)).toLRSHom.toShHom
              ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom).hom.app
            (Stacks.ClosedImmersion.conormalSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
          (RingedSpaceModuleAdjunction.modulePullback
                ((BigFppfOver.toScheme B S hS).map (𝟙 R)).toLRSHom.toShHom).map
              (Stacks.ClosedImmersion.conormalSheafMap
                (toShHom_square_of_comp_eq B S hS j j' b a hsq)) ≫
            ((RingedSpaceModuleAdjunction.modulePullbackComp
                    ((BigFppfOver.toScheme B S hS).map (𝟙 R)).toLRSHom.toShHom
                    ((BigFppfOver.toScheme B S hS).map (𝟙 R)).toLRSHom.toShHom).hom.app
                  (Stacks.ClosedImmersion.conormalSheaf
                    ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
                (RingedSpaceModuleAdjunction.modulePullback
                      ((BigFppfOver.toScheme B S hS).map (𝟙 R)).toLRSHom.toShHom).map
                    (Stacks.ClosedImmersion.conormalSheafMap
                      (toShHom_square_of_comp_eq B S hS (immersionCoborderLift B S hS j) j (𝟙 R)
                        (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)
                        (immersionCoborderLift_comp_openSubHom_id B S hS j))) ≫
                  Stacks.ClosedImmersion.conormalSheafMap
                    (toShHom_square_of_comp_eq B S hS
                      (coborderSquareLift B S hS j j' b a hsq) (immersionCoborderLift B S hS j)
                      (𝟙 R) (coborderSquareHom B S hS j j' b a hsq)
                      (coborderSquareLift_comp_coborderSquareHom_id B S hS j j' b a hsq))) := by
  refine (Stacks.ClosedImmersion.conormalSheafMap_comp_eq_comp₅
    (toShHom_square_of_comp_eq B S hS (coborderSquareLift B S hS j j' b a hsq)
      (immersionCoborderLift B S hS j') b (coborderSquareMap B S hS j j' b a hsq)
      (coborderSquareLift_comp_coborderSquareMap B S hS j j' b a hsq))
    (toShHom_square_of_comp_eq B S hS (immersionCoborderLift B S hS j') j' (𝟙 R')
      (openSubHom V' ((BigFppfOver.toScheme B S hS).map j').coborderRange)
      (immersionCoborderLift_comp_openSubHom_id B S hS j'))
    (toShHom_square_of_comp_eq B S hS (coborderSquareLift B S hS j j' b a hsq) j (𝟙 R)
      (coborderSquareHom B S hS j j' b a hsq ≫
        openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)
      (coborderSquareLift_comp_coborderRectangle_id B S hS j j' b a hsq))
    (toShHom_square_of_comp_eq B S hS j j' b a hsq)
    (toShHom_square_of_comp_eq B S hS (coborderSquareLift B S hS j j' b a hsq)
      (immersionCoborderLift B S hS j) (𝟙 R) (coborderSquareHom B S hS j j' b a hsq)
      (coborderSquareLift_comp_coborderSquareHom_id B S hS j j' b a hsq))
    (toShHom_square_of_comp_eq B S hS (immersionCoborderLift B S hS j) j (𝟙 R)
      (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)
      (immersionCoborderLift_comp_openSubHom_id B S hS j))
    (congrArg (fun m : R ⟶ R' => ((BigFppfOver.toScheme B S hS).map m).toLRSHom.toShHom)
      (show b ≫ 𝟙 R' = 𝟙 R ≫ b by rw [Category.comp_id, Category.id_comp]))
    (congrArg
      (fun m : coborderSquareObj B S hS j j' b a hsq ⟶ V' =>
        ((BigFppfOver.toScheme B S hS).map m).toLRSHom.toShHom)
      (coborderSquareMap_comp_openSubHom B S hS j j' b a hsq))
    (congrArg (fun m : R ⟶ R => ((BigFppfOver.toScheme B S hS).map m).toLRSHom.toShHom)
      (Category.id_comp (𝟙 R)))
    rfl rfl rfl).trans ?_
  refine (eqToHom_comp_of_refl _ _).trans (congrArg (fun t => _ ≫ _ ≫ t) ?_)
  exact eqToHom_comp_of_refl _ _

end Square

section FoldedNaturality

attribute [local irreducible] modulePullback modulePullbackCompIso
  representedModuleObjPullbackIso representedAssociatedModulePullbackIso squarePullbackCompIso
  representedSmallEtaleModuleEquivalence

variable {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')

/-- **The unconditional closed naturality of part (1) of [Stacks Project, Tag 04G2], with its
left-hand side folded into the canonical map of [Stacks Project, Tag 04CP].**

`AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq` states
it with `AlgebraicGeometry.Space.kernelIdealZPowSquareMap` written out — the square comparison
read at the degree-one piece, followed by the inverse image of the map of ideal sheaves — while
`AlgebraicGeometry.Space.conormalStack_ambient_comp` takes its hypothesis `h₁` with that composite
folded.  This folds it, by `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_eq`.

**The reason this is a declaration of its own rather than a step inside the
instantiation below.**  Folding is `rfl`, so a consumer may be tempted to let the elaborator do it
in passing.  At the concrete data of the coborder squares that is a **kernel deterministic
timeout**: the definition being unfolded is built from
`AlgebraicGeometry.Space.squarePullbackCompIso`, which is built by sheafification, and the kernel
ignores the `attribute [local irreducible]` that lets the elaborator past it.  Done here, where
`j`, `j'`, `b` and `a` are variables, the fold costs nothing and the instantiation below meets its
hypothesis syntactically. -/
theorem conormalSheafMap_representedConormalKernelIdealZPowIso_zPow
    [hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [hj' : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')]
    (hsq : j ≫ a = b ≫ j') :
    (modulePullback B S hS (representedSpaceMap B S hS b)).map
          (representedConormalKernelIdealZPowIso B S hS j').hom ≫
        kernelIdealZPowSquareMap B S hS (representedSpaceMap B S hS j)
          (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
          (representedSpaceMap B S hS a)
          (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq) 1 =
      (representedAssociatedModulePullbackIso B S hS b
            (relativelyRepresentable_yoneda_map B S hS b)
            (Stacks.ClosedImmersion.conormalSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              (Stacks.ClosedImmersion.conormalSheafMap
                (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
                (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
                (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
                (toShHom_square_of_comp_eq B S hS j j' b a hsq))) ≫
          (representedConormalKernelIdealZPowIso B S hS j).hom := by
  rw [kernelIdealZPowSquareMap_eq B S hS (representedSpaceMap B S hS j)
    (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
    (representedSpaceMap B S hS a)
    (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq) 1]
  exact conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq B S hS j j' b a hsq

end FoldedNaturality

section Stack

attribute [local irreducible] modulePullback modulePullbackCompIso modulePullbackIdIso
  representedModuleObjPullbackIso representedAssociatedModulePullbackIso
  squarePullbackCompIso representedSmallEtaleModuleEquivalence

variable {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R')
    (a : V ⟶ V')
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [hj' : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j')]

/-- **The outer rectangle of `S₁` over `S₃` at the represented spaces, with its left-hand
vertical spelled as `AlgebraicGeometry.Space.representedSpaceMap` of the site's identity.**

`AlgebraicGeometry.Space.coborderSquare_comp_comm` spells that vertical `𝟙 ≫ 𝟙`, which is the
spelling the cancellation
`AlgebraicGeometry.Space.isIso_kernelIdealZPowSquareMap_coborderSquare_comp` is stated at;
`AlgebraicGeometry.Space.conormalStack_ambient_comp` reads it as `representedSpaceMap (𝟙 R) ≫ 𝟙`.
The two are definitionally equal, by `AlgebraicGeometry.Space.representedSpaceMap_id` — which is
`rfl`, contrary to its own docstring.

**This crossing is made here, at a statement of two lines, and that is the point.**  Left inside
the instantiation below it is made instead underneath every sheafification-built comparison that
instantiation mentions, once per occurrence, and the result is a kernel deterministic timeout,
not removed by any `attribute [local irreducible]`, which the kernel ignores. -/
theorem coborderSquare_comp_comm_representedSpaceMap_id (hsq : j ≫ a = b ≫ j') :
    representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq) ≫
        representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
          representedSpaceMap B S hS
            (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange) =
      (representedSpaceMap B S hS (𝟙 R) ≫
          𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS)) ≫
        representedSpaceMap B S hS j := by
  rw [representedSpaceMap_id]
  exact coborderSquare_comp_comm B S hS j j' b a hsq

/-- **The transported naturality square of the rectangle `S₁` over `S₃`.**

The upper square is the one over the two closed factorisations of `j` — through the ambient of the
lifted square and through its own coborder ambient — and the lower one is the change of ambient at
`j` itself.  Both have the identity down their left-hand side, so the rectangle does too.

This is the upper square of the backward step of the reduction of part (2) of
[Stacks Project, Tag 04G2]: one instantiation of
`AlgebraicGeometry.Space.conormalStack_ambient_comp`, whose `h₁` is the unconditional closed
naturality at `S₁` and whose `h₂` is
`AlgebraicGeometry.Space.conormalChangeOfAmbientAgreement_transport` at `j`. -/
theorem conormalCoborderRectangle_square (hsq : j ≫ a = b ≫ j') :
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 R) ≫
            𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))).map
          (representedConormalOfImmersionKernelIdealZPowIso B S hS j).hom ≫
        kernelIdealZPowSquareMap B S hS
          (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
          (representedSpaceMap B S hS j)
          (representedSpaceMap B S hS (𝟙 R) ≫
            𝟙 (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS))
          (representedSpaceMap B S hS (coborderSquareHom B S hS j j' b a hsq) ≫
            representedSpaceMap B S hS
              (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange))
          (coborderSquare_comp_comm_representedSpaceMap_id B S hS j j' b a hsq) 1 =
      (representedAssociatedModulePullbackIso B S hS (𝟙 R)
            (relativelyRepresentable_yoneda_map B S hS (𝟙 R))
            (Stacks.ClosedImmersion.conormalSheaf
              ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              ((Scheme.Modules.pullbackComp (B.inclusion.map (Over.Hom.left (𝟙 R)))
                    (B.inclusion.map (Over.Hom.left (𝟙 R)))).inv.app
                  (Stacks.ClosedImmersion.conormalSheaf
                    ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
                (Scheme.Modules.pullback (B.inclusion.map (Over.Hom.left (𝟙 R)))).map
                    (((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R)).hom.app
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
                        (Stacks.Immersion.conormalSheafSelfIso
                          ((BigFppfOver.toScheme B S hS).map j)).hom :
                      (Scheme.Modules.pullback
                            (B.inclusion.map (Over.Hom.left (𝟙 R)))).obj
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ⟶
                        Stacks.ClosedImmersion.conormalSheaf
                          ((BigFppfOver.toScheme B S hS).map
                            (immersionCoborderLift B S hS j)).toLRSHom.toShHom)) ≫
                  Stacks.ClosedImmersion.conormalSheafMap
                    (toShHom_square_of_comp_eq B S hS
                      (coborderSquareLift B S hS j j' b a hsq)
                      (immersionCoborderLift B S hS j) (𝟙 R)
                      (coborderSquareHom B S hS j j' b a hsq)
                      (coborderSquareLift_comp_coborderSquareHom_id B S hS j j' b a hsq)))) ≫
          (representedConormalKernelIdealZPowIso B S hS
            (coborderSquareLift B S hS j j' b a hsq)).hom :=
  conormalStack_ambient_comp B S hS (coborderSquareLift B S hS j j' b a hsq)
    (immersionCoborderLift B S hS j) j (𝟙 R) (coborderSquareHom B S hS j j' b a hsq)
    (openSubHom V ((BigFppfOver.toScheme B S hS).map j).coborderRange)
    (representedConormalKernelIdealZPowIso B S hS (coborderSquareLift B S hS j j' b a hsq))
    (representedConormalKernelIdealZPowIso B S hS (immersionCoborderLift B S hS j))
    (representedConormalOfImmersionKernelIdealZPowIso B S hS j)
    (Stacks.ClosedImmersion.conormalSheafMap
      (toShHom_square_of_comp_eq B S hS (coborderSquareLift B S hS j j' b a hsq)
        (immersionCoborderLift B S hS j) (𝟙 R) (coborderSquareHom B S hS j j' b a hsq)
        (coborderSquareLift_comp_coborderSquareHom_id B S hS j j' b a hsq)))
    ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R)).hom.app
        (Stacks.ClosedImmersion.conormalSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
      (Stacks.Immersion.conormalSheafSelfIso ((BigFppfOver.toScheme B S hS).map j)).hom)
    (representedSpaceMap_square_of_comp_eq B S hS (coborderSquareLift B S hS j j' b a hsq)
      (immersionCoborderLift B S hS j) (𝟙 R) (coborderSquareHom B S hS j j' b a hsq)
      (coborderSquareLift_comp_coborderSquareHom_id B S hS j j' b a hsq))
    (isPullback_representedSpaceMap_immersionCoborderLift B S hS j).w.symm
    (coborderSquare_comp_comm_representedSpaceMap_id B S hS j j' b a hsq)
    (conormalSheafMap_representedConormalKernelIdealZPowIso_zPow B S hS
      (coborderSquareLift B S hS j j' b a hsq) (immersionCoborderLift B S hS j) (𝟙 R)
      (coborderSquareHom B S hS j j' b a hsq)
      (coborderSquareLift_comp_coborderSquareHom_id B S hS j j' b a hsq))
    (conormalChangeOfAmbientAgreement_transport B S hS j)

/-- **The outer rectangle of `S₂` over `S₄` at the represented spaces**, with its left-hand
vertical in the shape `AlgebraicGeometry.Space.conormalStack_ambient_comp` reads it, `b ≫ 𝟙`.
The companion of `AlgebraicGeometry.Space.coborderSquare_comp_comm_representedSpaceMap_id` for
the other of the two stacks, and made at a small statement for the same reason. -/
theorem coborderSquareMap_comp_comm_representedSpaceMap_id (hsq : j ≫ a = b ≫ j') :
    representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq) ≫
        representedSpaceMap B S hS (coborderSquareMap B S hS j j' b a hsq) ≫
          representedSpaceMap B S hS
            (openSubHom V' ((BigFppfOver.toScheme B S hS).map j').coborderRange) =
      (representedSpaceMap B S hS b ≫
          𝟙 (⟨yoneda.obj R', isAlgebraicSpace_yoneda B S hS R'⟩ : AlgebraicSpaces B S hS)) ≫
        representedSpaceMap B S hS j' := by
  rw [Category.comp_id, ← Category.assoc,
    representedSpaceMap_square_of_comp_eq B S hS (coborderSquareLift B S hS j j' b a hsq)
      (immersionCoborderLift B S hS j') b (coborderSquareMap B S hS j j' b a hsq)
      (coborderSquareLift_comp_coborderSquareMap B S hS j j' b a hsq),
    Category.assoc, representedSpaceMap_comp, immersionCoborderLift_comp_openSubHom]

/-- **The transported naturality square of the rectangle `S₂` over `S₄`: the outer rectangle of
the reduction.**

The upper square is the one over the two coborder ambients — both of whose horizontal morphisms
are closed immersions — and the lower one is the change of ambient at `j'`.  This is the outer
rectangle the backward step of the reduction of part (2) of [Stacks Project, Tag 04G2] takes as
its hypothesis `hD`; the rectangle `S₁` over `S₃` of
`AlgebraicGeometry.Space.conormalCoborderRectangle_square` is the same rectangle read the other
way, which is what `AlgebraicGeometry.Space.conormalSheafMap_coborderRectangle_eq` says on the
Zariski side. -/
theorem conormalCoborderOuterRectangle_square (hsq : j ≫ a = b ≫ j') :
    (modulePullback B S hS (representedSpaceMap B S hS b ≫
            𝟙 (⟨yoneda.obj R', isAlgebraicSpace_yoneda B S hS R'⟩ : AlgebraicSpaces B S hS))).map
          (representedConormalOfImmersionKernelIdealZPowIso B S hS j').hom ≫
        kernelIdealZPowSquareMap B S hS
          (representedSpaceMap B S hS (coborderSquareLift B S hS j j' b a hsq))
          (representedSpaceMap B S hS j')
          (representedSpaceMap B S hS b ≫
            𝟙 (⟨yoneda.obj R', isAlgebraicSpace_yoneda B S hS R'⟩ : AlgebraicSpaces B S hS))
          (representedSpaceMap B S hS (coborderSquareMap B S hS j j' b a hsq) ≫
            representedSpaceMap B S hS
              (openSubHom V' ((BigFppfOver.toScheme B S hS).map j').coborderRange))
          (coborderSquareMap_comp_comm_representedSpaceMap_id B S hS j j' b a hsq) 1 =
      (representedAssociatedModulePullbackIso B S hS b
            (relativelyRepresentable_yoneda_map B S hS b)
            (Stacks.ClosedImmersion.conormalSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              ((Scheme.Modules.pullbackComp (B.inclusion.map b.left)
                    (B.inclusion.map (Over.Hom.left (𝟙 R')))).inv.app
                  (Stacks.ClosedImmersion.conormalSheaf
                    ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
                (Scheme.Modules.pullback (B.inclusion.map b.left)).map
                    (((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R')).hom.app
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
                        (Stacks.Immersion.conormalSheafSelfIso
                          ((BigFppfOver.toScheme B S hS).map j')).hom :
                      (Scheme.Modules.pullback
                            (B.inclusion.map (Over.Hom.left (𝟙 R')))).obj
                          (Stacks.ClosedImmersion.conormalSheaf
                            ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ⟶
                        Stacks.ClosedImmersion.conormalSheaf
                          ((BigFppfOver.toScheme B S hS).map
                            (immersionCoborderLift B S hS j')).toLRSHom.toShHom)) ≫
                  Stacks.ClosedImmersion.conormalSheafMap
                    (i := ((BigFppfOver.toScheme B S hS).map
                      (coborderSquareLift B S hS j j' b a hsq)).toLRSHom.toShHom)
                    (j := ((BigFppfOver.toScheme B S hS).map
                      (immersionCoborderLift B S hS j')).toLRSHom.toShHom)
                    (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                    (k := ((BigFppfOver.toScheme B S hS).map
                      (coborderSquareMap B S hS j j' b a hsq)).toLRSHom.toShHom)
                    (toShHom_square_of_comp_eq B S hS
                      (coborderSquareLift B S hS j j' b a hsq)
                      (immersionCoborderLift B S hS j') b
                      (coborderSquareMap B S hS j j' b a hsq)
                      (coborderSquareLift_comp_coborderSquareMap B S hS j j' b a hsq)))) ≫
          (representedConormalKernelIdealZPowIso B S hS
            (coborderSquareLift B S hS j j' b a hsq)).hom :=
  conormalStack_ambient_comp B S hS (coborderSquareLift B S hS j j' b a hsq)
    (immersionCoborderLift B S hS j') j' b (coborderSquareMap B S hS j j' b a hsq)
    (openSubHom V' ((BigFppfOver.toScheme B S hS).map j').coborderRange)
    (representedConormalKernelIdealZPowIso B S hS (coborderSquareLift B S hS j j' b a hsq))
    (representedConormalKernelIdealZPowIso B S hS (immersionCoborderLift B S hS j'))
    (representedConormalOfImmersionKernelIdealZPowIso B S hS j')
    (Stacks.ClosedImmersion.conormalSheafMap
      (i := ((BigFppfOver.toScheme B S hS).map
        (coborderSquareLift B S hS j j' b a hsq)).toLRSHom.toShHom)
      (j := ((BigFppfOver.toScheme B S hS).map
        (immersionCoborderLift B S hS j')).toLRSHom.toShHom)
      (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
      (k := ((BigFppfOver.toScheme B S hS).map
        (coborderSquareMap B S hS j j' b a hsq)).toLRSHom.toShHom)
      (toShHom_square_of_comp_eq B S hS (coborderSquareLift B S hS j j' b a hsq)
        (immersionCoborderLift B S hS j') b (coborderSquareMap B S hS j j' b a hsq)
        (coborderSquareLift_comp_coborderSquareMap B S hS j j' b a hsq)))
    ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj R')).hom.app
        (Stacks.ClosedImmersion.conormalSheaf
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) ≫
      (Stacks.Immersion.conormalSheafSelfIso ((BigFppfOver.toScheme B S hS).map j')).hom)
    (representedSpaceMap_square_of_comp_eq B S hS (coborderSquareLift B S hS j j' b a hsq)
      (immersionCoborderLift B S hS j') b (coborderSquareMap B S hS j j' b a hsq)
      (coborderSquareLift_comp_coborderSquareMap B S hS j j' b a hsq))
    (isPullback_representedSpaceMap_immersionCoborderLift B S hS j').w.symm
    (coborderSquareMap_comp_comm_representedSpaceMap_id B S hS j j' b a hsq)
    (conormalSheafMap_representedConormalKernelIdealZPowIso_zPow B S hS
      (coborderSquareLift B S hS j j' b a hsq) (immersionCoborderLift B S hS j') b
      (coborderSquareMap B S hS j j' b a hsq)
      (coborderSquareLift_comp_coborderSquareMap B S hS j j' b a hsq))
    (conormalChangeOfAmbientAgreement_transport B S hS j')

end Stack

end AlgebraicGeometry.Space

end
