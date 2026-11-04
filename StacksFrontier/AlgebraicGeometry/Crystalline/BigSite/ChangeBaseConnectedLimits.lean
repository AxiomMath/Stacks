module

public import Mathlib.CategoryTheory.IsConnected
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Functoriality

/-!
# Change of divided power base commutes with connected limits

Let `f : (S, I, γ) ⟶ (S', I', γ')` be a morphism of divided power schemes and `g : X ⟶ Y` a
morphism over it.  Change of divided power base,
`Crystalline.GlobalCrystallineSituation.changeBase` of [Stacks, Tag 07IC], reads a divided power
thickening of `X` relative to `S` as one of `Y` relative to `S'`: the underlying thickening
`U ↪ T` is untouched, the structure morphisms become `T ⟶ S ⟶ S'` and `U ⟶ X ⟶ Y`, and a
morphism of `CRIS(X/S)` is carried to the morphism of `CRIS(Y/S')` with the *same* two components.

The functor therefore cannot disturb a limit whose shape is **connected**.  An object of
`CRIS(X/S)` is an object of `CRIS(Y/S')` together with a factorisation of its two structure
morphisms through `S` and through `X`, and `rebaseAlong` below builds one out of a morphism to an
object of `CRIS(X/S)`.  A cone over a rebased diagram has such a morphism at every leg, and the
object they produce is the same at every leg — that is where connectedness enters, and nothing
else in the argument uses anything about the shape.  So a cone of `CRIS(Y/S')` over a rebased
diagram is the image of a cone of `CRIS(X/S)`, and the limiting property transfers.

The two shapes this gets used at are `WalkingCospan` and `WalkingParallelPair`: change of base
preserves the fibre products and the equalizers of the crystalline category.  Both are connected,
and neither is a product.  Connectedness is a real restriction and not an artefact: `WalkingPair`
is not connected, and the argument below says nothing about it — the apex of a cone over two
objects carries no map to `S` that its two legs agree on.  That is also the shape one would not
expect to be preserved, a product in `CRIS(X/S)` having for ambient divided power scheme an
envelope of `T₁ ×_S T₂`, built over the base that `f` moves; that non-preservation is not proved
here, only the absence of any claim about it.  Nothing here routes equalizers through products,
which is why
the equalizer case does not inherit that obstruction even though the library's proof that
`CRIS(X/S)` *has* equalizers does go through binary products
(`Crystalline.GlobalCrystallineSituation.hasNonemptyFiniteLimits_thickening`).

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `rebaseAlong` — a divided power thickening of schemes mapping to the thickening of an object of
  `CRIS(X/S)` is itself an object of `CRIS(X/S)`.
* `changeBaseConeApex`, `changeBaseCone` — a cone over a rebased diagram, read back as a cone of
  `CRIS(X/S)` through a chosen leg.
* `changeBaseLift`, `changeBaseConeUniqHom` — the lift of such a cone through the image of a
  limit cone, and the reading of a competing lift as a morphism of `CRIS(X/S)`.
* `isLimitChangeBaseMapCone` — the image of a limit cone over a preconnected diagram is a limit
  cone.

## Main results

* `changeBase_preservesLimitsOfShape` — **change of divided power base preserves limits of every
  connected shape**, in particular fibre products and equalizers.

## Implementation notes

The chosen leg `j₀` is an explicit argument of `changeBaseConeApex` and `changeBaseCone`, so the
constructions need only `CategoryTheory.IsPreconnected`; nonemptiness of the shape is used once,
in `changeBase_preservesLimitsOfShape`.

`Thickening.coneSourceHom` and `Thickening.coneTargetHom`, and their counterparts
`changeBaseConeSourceHom` and `changeBaseConeTargetHom` for a cone over a rebased diagram, are
the two components of a cone leg named so that their types mention the apex and the object of the
diagram directly.  They are definitionally the fields of the leg, but the types Lean infers for
those fields read through `Functor.const` and through `changeBase`, and every statement below is
cleaner on the other side of that identification.

No `@[stacks]` attribute is placed: the Stacks project states the functor of [Stacks, Tag 07IC]
and its small-site form [Stacks, Tag 07KL], but not this preservation property, and the two limit
shapes of [Stacks, Tag 07I9] are about existence in one situation rather than preservation under
change of base.

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w' w u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **A divided power thickening of schemes mapping to the thickening of an object of `CRIS(X/S)`
is an object of `CRIS(X/S)`.**  The structure morphisms are those of `B` precomposed with the two
components, and the compatibility over `S` is the one of `B` together with the commuting square
of thickenings. -/
def rebaseAlong (D : SchemeThickening.{u}) (B : Thickening S)
    (p : D.source ⟶ B.thickening.source) (q : D.target ⟶ B.thickening.target)
    (hpq : D.immersion ≫ q.hom = p ≫ B.thickening.immersion) : Thickening S where
  thickening := D
  toBase := q ≫ B.toBase
  toX := p ≫ B.toX
  over_base := by
    have hd : D.immersion ≫ (q ≫ B.toBase).hom =
        p ≫ B.thickening.immersion ≫ B.toBase.hom := by
      rw [DividedPowerScheme.Hom.comp_hom, ← Category.assoc, hpq, Category.assoc]
    rw [hd, B.over_base, Category.assoc]

/-- The thickening of `rebaseAlong D B p q hpq` is `D`. -/
@[simp]
theorem rebaseAlong_thickening (D : SchemeThickening.{u}) (B : Thickening S)
    (p : D.source ⟶ B.thickening.source) (q : D.target ⟶ B.thickening.target)
    (hpq : D.immersion ≫ q.hom = p ≫ B.thickening.immersion) :
    (rebaseAlong D B p q hpq).thickening = D := rfl

/-- The structure morphism of `rebaseAlong D B p q hpq` to `S` is `q` followed by that of `B`. -/
@[simp]
theorem rebaseAlong_toBase (D : SchemeThickening.{u}) (B : Thickening S)
    (p : D.source ⟶ B.thickening.source) (q : D.target ⟶ B.thickening.target)
    (hpq : D.immersion ≫ q.hom = p ≫ B.thickening.immersion) :
    (rebaseAlong D B p q hpq).toBase = q ≫ B.toBase := rfl

/-- The map of `rebaseAlong D B p q hpq` to `X` is `p` followed by that of `B`. -/
@[simp]
theorem rebaseAlong_toX (D : SchemeThickening.{u}) (B : Thickening S)
    (p : D.source ⟶ B.thickening.source) (q : D.target ⟶ B.thickening.target)
    (hpq : D.immersion ≫ q.hom = p ≫ B.thickening.immersion) :
    (rebaseAlong D B p q hpq).toX = p ≫ B.toX := rfl

namespace Thickening

variable {J : Type w} [Category.{w'} J] {K : J ⥤ Thickening S}

/-- The thickened component of a leg of a cone of `CRIS(X/S)`, with the domain written as the
apex of the cone. -/
def coneSourceHom (c : Cone K) (j : J) :
    c.pt.thickening.source ⟶ (K.obj j).thickening.source := (c.π.app j).sourceHom

/-- The ambient component of a leg of a cone of `CRIS(X/S)`, with the domain written as the apex
of the cone. -/
def coneTargetHom (c : Cone K) (j : J) :
    c.pt.thickening.target ⟶ (K.obj j).thickening.target := (c.π.app j).targetHom

/-- A leg of a cone of `CRIS(X/S)` is a morphism over `S`. -/
theorem coneTargetHom_comp_toBase (c : Cone K) (j : J) :
    coneTargetHom c j ≫ (K.obj j).toBase = c.pt.toBase := (c.π.app j).base_naturality

/-- A leg of a cone of `CRIS(X/S)` is a morphism over `X`. -/
theorem coneSourceHom_comp_toX (c : Cone K) (j : J) :
    coneSourceHom c j ≫ (K.obj j).toX = c.pt.toX := (c.π.app j).toX_naturality

end Thickening

variable {S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}

section ConnectedLimits

variable {J : Type w} [Category.{w'} J] {K : J ⥤ Thickening S}
  (s : Cone (K ⋙ changeBase S S' f g h))

/-- The thickened component of a leg of a cone over a rebased diagram, with the codomain written
as the object before rebasing. -/
def changeBaseConeSourceHom (j : J) :
    s.pt.thickening.source ⟶ (K.obj j).thickening.source := (s.π.app j).sourceHom

/-- The ambient component of a leg of a cone over a rebased diagram, with the codomain written as
the object before rebasing. -/
def changeBaseConeTargetHom (j : J) :
    s.pt.thickening.target ⟶ (K.obj j).thickening.target := (s.π.app j).targetHom

/-- The commuting square of thickenings of a leg of a cone over a rebased diagram. -/
theorem changeBaseCone_immersion_naturality (j : J) :
    s.pt.thickening.immersion ≫ (changeBaseConeTargetHom s j).hom =
      changeBaseConeSourceHom s j ≫ (K.obj j).thickening.immersion :=
  (s.π.app j).immersion_naturality

/-- A leg of a cone over a rebased diagram is a morphism over `S'`. -/
theorem changeBaseCone_base_naturality (j : J) :
    changeBaseConeTargetHom s j ≫ (K.obj j).toBase ≫ f = s.pt.toBase :=
  (s.π.app j).base_naturality

/-- A leg of a cone over a rebased diagram is a morphism over `Y`. -/
theorem changeBaseCone_toX_naturality (j : J) :
    changeBaseConeSourceHom s j ≫ (K.obj j).toX ≫ g = s.pt.toX :=
  (s.π.app j).toX_naturality

/-- The legs of a cone over a rebased diagram are compatible with the diagram, on thickened
schemes. -/
theorem changeBaseConeSourceHom_naturality {j j' : J} (u : j ⟶ j') :
    changeBaseConeSourceHom s j ≫ (K.map u).sourceHom = changeBaseConeSourceHom s j' :=
  congrArg Thickening.Hom.sourceHom (s.w u)

/-- The legs of a cone over a rebased diagram are compatible with the diagram, on ambient divided
power schemes. -/
theorem changeBaseConeTargetHom_naturality {j j' : J} (u : j ⟶ j') :
    changeBaseConeTargetHom s j ≫ (K.map u).targetHom = changeBaseConeTargetHom s j' :=
  congrArg Thickening.Hom.targetHom (s.w u)

/-- **The structure morphism over `S` read off a leg of a cone over a rebased diagram does not
depend on the leg.**  A morphism of the shape moves the one into the other, every object of the
diagram having the same structure morphism before and after rebasing; connectedness spreads that
over the whole shape. -/
theorem changeBaseConeTargetHom_comp_toBase_eq [IsPreconnected J] (j j' : J) :
    changeBaseConeTargetHom s j ≫ (K.obj j).toBase =
      changeBaseConeTargetHom s j' ≫ (K.obj j').toBase := by
  refine constant_of_preserves_morphisms (α := s.pt.thickening.target ⟶ S.S)
    (fun i ↦ changeBaseConeTargetHom s i ≫ (K.obj i).toBase) (fun j₁ j₂ u ↦ ?_) j j'
  rw [← changeBaseConeTargetHom_naturality s u, Category.assoc, (K.map u).base_naturality]

/-- **The map to `X` read off a leg of a cone over a rebased diagram does not depend on the
leg.** -/
theorem changeBaseConeSourceHom_comp_toX_eq [IsPreconnected J] (j j' : J) :
    changeBaseConeSourceHom s j ≫ (K.obj j).toX =
      changeBaseConeSourceHom s j' ≫ (K.obj j').toX := by
  refine constant_of_preserves_morphisms (α := s.pt.thickening.source ⟶ S.X)
    (fun i ↦ changeBaseConeSourceHom s i ≫ (K.obj i).toX) (fun j₁ j₂ u ↦ ?_) j j'
  rw [← changeBaseConeSourceHom_naturality s u, Category.assoc, (K.map u).toX_naturality]

/-- **The apex of a cone over a rebased diagram, read back as an object of `CRIS(X/S)`**, by
factoring its structure morphisms through the leg `j₀`. -/
def changeBaseConeApex (j₀ : J) : Thickening S :=
  rebaseAlong s.pt.thickening (K.obj j₀) (changeBaseConeSourceHom s j₀)
    (changeBaseConeTargetHom s j₀) (changeBaseCone_immersion_naturality s j₀)

/-- The thickening of `changeBaseConeApex s j₀` is that of the apex of `s`. -/
@[simp]
theorem changeBaseConeApex_thickening (j₀ : J) :
    (changeBaseConeApex s j₀).thickening = s.pt.thickening := rfl

/-- The structure morphism of `changeBaseConeApex s j₀` to `S` is `changeBaseConeTargetHom s j₀`
followed by that of `K.obj j₀`. -/
@[simp]
theorem changeBaseConeApex_toBase (j₀ : J) :
    (changeBaseConeApex s j₀).toBase =
      changeBaseConeTargetHom s j₀ ≫ (K.obj j₀).toBase := rfl

/-- The map of `changeBaseConeApex s j₀` to `X` is `changeBaseConeSourceHom s j₀` followed by
that of `K.obj j₀`. -/
@[simp]
theorem changeBaseConeApex_toX (j₀ : J) :
    (changeBaseConeApex s j₀).toX = changeBaseConeSourceHom s j₀ ≫ (K.obj j₀).toX := rfl

/-- A leg of the cone of `CRIS(X/S)` underlying a cone over a rebased diagram. -/
def changeBaseConeLeg [IsPreconnected J] (j₀ j : J) : changeBaseConeApex s j₀ ⟶ K.obj j where
  sourceHom := changeBaseConeSourceHom s j
  targetHom := changeBaseConeTargetHom s j
  immersion_naturality := changeBaseCone_immersion_naturality s j
  base_naturality := changeBaseConeTargetHom_comp_toBase_eq s j j₀
  toX_naturality := changeBaseConeSourceHom_comp_toX_eq s j j₀

/-- **A cone over a rebased diagram is the image of a cone over the diagram itself**, when the
shape is preconnected. -/
def changeBaseCone [IsPreconnected J] (j₀ : J) : Cone K where
  pt := changeBaseConeApex s j₀
  π :=
    { app := changeBaseConeLeg s j₀
      naturality := fun _ _ u ↦
        Thickening.Hom.ext (changeBaseConeSourceHom_naturality s u).symm
          (changeBaseConeTargetHom_naturality s u).symm }

variable {c : Cone K}

/-- The thickened component of the lift of a cone over a rebased diagram through a limit cone,
with the domain written as the apex of the given cone. -/
def changeBaseLiftSourceHom [IsPreconnected J] (j₀ : J) (hc : IsLimit c) :
    s.pt.thickening.source ⟶ c.pt.thickening.source :=
  (hc.lift (changeBaseCone s j₀)).sourceHom

/-- The ambient component of the lift of a cone over a rebased diagram through a limit cone,
with the domain written as the apex of the given cone. -/
def changeBaseLiftTargetHom [IsPreconnected J] (j₀ : J) (hc : IsLimit c) :
    s.pt.thickening.target ⟶ c.pt.thickening.target :=
  (hc.lift (changeBaseCone s j₀)).targetHom

/-- The commuting square of thickenings of the lift. -/
theorem changeBaseLift_immersion_naturality [IsPreconnected J] (j₀ : J) (hc : IsLimit c) :
    s.pt.thickening.immersion ≫ (changeBaseLiftTargetHom s j₀ hc).hom =
      changeBaseLiftSourceHom s j₀ hc ≫ c.pt.thickening.immersion :=
  (hc.lift (changeBaseCone s j₀)).immersion_naturality

/-- Rewriting a composite through a leg: if `x ≫ y = m ≫ z` and `m ≫ z ≫ f = t`, then
`x ≫ y ≫ f = t`. -/
private theorem comp_comp_eq_of_comp_eq {C : Type*} [Category C] {A B D E F : C}
    {x : A ⟶ B} {y : B ⟶ D} {m : A ⟶ E} {z : E ⟶ D} {f : D ⟶ F} {t : A ⟶ F}
    (h1 : x ≫ y = m ≫ z) (h2 : m ≫ z ≫ f = t) : x ≫ y ≫ f = t := by
  rw [← Category.assoc, h1, Category.assoc, h2]

/-- The lift is a morphism over `S'`: it is one over `S`, and the structure morphism read off the
leg `j₀` composed with `f` is that of the apex. -/
theorem changeBaseLiftTargetHom_comp_toBase [IsPreconnected J] (j₀ : J) (hc : IsLimit c) :
    changeBaseLiftTargetHom s j₀ hc ≫ c.pt.toBase ≫ f = s.pt.toBase := by
  exact comp_comp_eq_of_comp_eq (hc.lift (changeBaseCone s j₀)).base_naturality
    (changeBaseCone_base_naturality s j₀)

/-- The lift is a morphism over `Y`. -/
theorem changeBaseLiftSourceHom_comp_toX [IsPreconnected J] (j₀ : J) (hc : IsLimit c) :
    changeBaseLiftSourceHom s j₀ hc ≫ c.pt.toX ≫ g = s.pt.toX := by
  exact comp_comp_eq_of_comp_eq (hc.lift (changeBaseCone s j₀)).toX_naturality
    (changeBaseCone_toX_naturality s j₀)

/-- **The lift of a cone over a rebased diagram through the image of a limit cone**: the lift of
`changeBaseCone`, read as a morphism of `CRIS(Y/S')`.  Its two naturality conditions over `S'`
and over `Y` are those of `changeBaseCone` composed with `f` and with `g`. -/
def changeBaseLift [IsPreconnected J] (j₀ : J) (hc : IsLimit c) :
    s.pt ⟶ (changeBase S S' f g h).obj c.pt where
  sourceHom := changeBaseLiftSourceHom s j₀ hc
  targetHom := changeBaseLiftTargetHom s j₀ hc
  immersion_naturality := changeBaseLift_immersion_naturality s j₀ hc
  base_naturality := changeBaseLiftTargetHom_comp_toBase s j₀ hc
  toX_naturality := changeBaseLiftSourceHom_comp_toX s j₀ hc

/-- The lift is a morphism of cones. -/
theorem changeBaseLift_comp [IsPreconnected J] (j₀ : J) (hc : IsLimit c) (j : J) :
    changeBaseLift s j₀ hc ≫ (changeBase S S' f g h).map (c.π.app j) = s.π.app j := by
  have h1 := congrArg Thickening.Hom.sourceHom (hc.fac (changeBaseCone s j₀) j)
  have h2 := congrArg Thickening.Hom.targetHom (hc.fac (changeBaseCone s j₀) j)
  exact Thickening.Hom.ext h1 h2

/-- **A morphism of `CRIS(Y/S')` into the rebased apex of a cone of `CRIS(X/S)`, read as a
morphism of `CRIS(X/S)` into the apex of `changeBaseCone`.**  This is what makes the lift unique:
the two components, their commuting square and their factorisations through the leg `j₀` are all
the datum of a morphism of `CRIS(X/S)`. -/
def changeBaseConeUniqHom [IsPreconnected J] (j₀ : J)
    (p : s.pt.thickening.source ⟶ c.pt.thickening.source)
    (q : s.pt.thickening.target ⟶ c.pt.thickening.target)
    (hpq : s.pt.thickening.immersion ≫ q.hom = p ≫ c.pt.thickening.immersion)
    (hq : q ≫ c.pt.toBase = changeBaseConeTargetHom s j₀ ≫ (K.obj j₀).toBase)
    (hp : p ≫ c.pt.toX = changeBaseConeSourceHom s j₀ ≫ (K.obj j₀).toX) :
    changeBaseConeApex s j₀ ⟶ c.pt where
  sourceHom := p
  targetHom := q
  immersion_naturality := hpq
  base_naturality := hq
  toX_naturality := hp

/-- Factoring through a leg: if `a ≫ b = d` and `b ≫ e = t`, then `a ≫ t = d ≫ e`. -/
private theorem comp_eq_comp_of_comp_eq {C : Type*} [Category C] {A B D E : C}
    {a : A ⟶ B} {b : B ⟶ D} {d : A ⟶ D} {e : D ⟶ E} {t : B ⟶ E}
    (h1 : a ≫ b = d) (h2 : b ≫ e = t) : a ≫ t = d ≫ e := by
  rw [← h2, ← Category.assoc, h1]

/-- **A morphism of `CRIS(Y/S')` into the image of the apex of a limit cone has the components of
the lift.**  This is the uniqueness half of `isLimitChangeBaseMapCone`, stated on the two
components so that nothing in the proof has to see through `changeBase`. -/
theorem changeBaseConeUniq [IsPreconnected J] (j₀ : J) (hc : IsLimit c)
    (p : s.pt.thickening.source ⟶ c.pt.thickening.source)
    (q : s.pt.thickening.target ⟶ c.pt.thickening.target)
    (hpq : s.pt.thickening.immersion ≫ q.hom = p ≫ c.pt.thickening.immersion)
    (hp : ∀ j, p ≫ Thickening.coneSourceHom c j = changeBaseConeSourceHom s j)
    (hq : ∀ j, q ≫ Thickening.coneTargetHom c j = changeBaseConeTargetHom s j) :
    p = (hc.lift (changeBaseCone s j₀)).sourceHom ∧
      q = (hc.lift (changeBaseCone s j₀)).targetHom := by
  have key : changeBaseConeUniqHom s j₀ p q hpq
      (comp_eq_comp_of_comp_eq (hq j₀) (Thickening.coneTargetHom_comp_toBase c j₀))
      (comp_eq_comp_of_comp_eq (hp j₀) (Thickening.coneSourceHom_comp_toX c j₀)) =
        hc.lift (changeBaseCone s j₀) :=
    hc.uniq (changeBaseCone s j₀) _ fun j ↦ Thickening.Hom.ext (hp j) (hq j)
  exact ⟨congrArg Thickening.Hom.sourceHom key, congrArg Thickening.Hom.targetHom key⟩

/-- **Change of divided power base carries a limit cone over a preconnected diagram to a limit
cone.**  The lift is `changeBaseLift`; uniqueness is `changeBaseConeUniq`. -/
def isLimitChangeBaseMapCone [IsPreconnected J] (j₀ : J) (hc : IsLimit c) :
    IsLimit ((changeBase S S' f g h).mapCone c) where
  lift t := changeBaseLift t j₀ hc
  fac t j := changeBaseLift_comp t j₀ hc j
  uniq t m hm := by
    have hms : ∀ j, (m.sourceHom : t.pt.thickening.source ⟶ c.pt.thickening.source) ≫
        Thickening.coneSourceHom c j = changeBaseConeSourceHom t j :=
      fun j ↦ congrArg Thickening.Hom.sourceHom (hm j)
    have hmt : ∀ j, (m.targetHom : t.pt.thickening.target ⟶ c.pt.thickening.target) ≫
        Thickening.coneTargetHom c j = changeBaseConeTargetHom t j :=
      fun j ↦ congrArg Thickening.Hom.targetHom (hm j)
    obtain ⟨k1, k2⟩ := changeBaseConeUniq t j₀ hc
      (m.sourceHom : t.pt.thickening.source ⟶ c.pt.thickening.source)
      (m.targetHom : t.pt.thickening.target ⟶ c.pt.thickening.target)
      m.immersion_naturality hms hmt
    refine Thickening.Hom.ext ?_ ?_
    · exact k1
    · exact k2

end ConnectedLimits

/-- **Change of divided power base preserves limits of every connected shape.**  The functor
leaves the underlying thickening and both components of a morphism untouched, so a cone over a
rebased diagram is the image of a cone, `changeBaseCone`; connectedness is what identifies the
structure morphisms read off the different legs, and is used nowhere else.

In particular change of base preserves fibre products and equalizers.  It says nothing about
products of pairs: `WalkingPair` is not connected, and the ambient divided power scheme of a
product in `CRIS(X/S)` is an envelope of `T₁ ×_S T₂`, built over the base that `f` moves. -/
theorem changeBase_preservesLimitsOfShape (J : Type w) [Category.{w'} J] [IsConnected J] :
    PreservesLimitsOfShape J (changeBase S S' f g h) where
  preservesLimit :=
    { preserves := fun hc ↦ ⟨isLimitChangeBaseMapCone (Classical.arbitrary J) hc⟩ }

end Crystalline.GlobalCrystallineSituation

end

end
