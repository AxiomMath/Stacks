module

public import StacksFrontier.Topology.Sheaves.Cohomology.SheafedSpaceLimits.LimitOfSheafedSpaces

/-!
# Lifting a cone of spaces to a cone of sheafed spaces, and pushing a sheaf along a base map

Two constructions on `SheafedSpace C`, both of them about base maps alone, that a *construction*
of a limiting cone of sheafed spaces over a given limiting cone of the spaces needs and that
`StacksDraft.Ch20.Sec16.Tag0A37Limit` does not offer.

The first lifts a cone.  A cone `c₀` of the spaces underlying a diagram `E` of sheafed spaces
becomes a cone over `E` itself by putting the constant sheaf at a terminal object on its vertex:
the sheaf component of each leg is then forced, and so is the cone identity.  The vertex sheaf is
useless, and that is the point.  `SheafedSpaceLimit.pullSystem` reads a cone of sheafed spaces
only through the base maps of its legs, so this lift makes the germ-model pullback system — whose
colimit is the sheaf one wants to put on the vertex — available over a cone of *spaces*, which is
what breaks the apparent circularity: the system has to exist before the sheaf that is its
colimit.

The second pushes a sheafed space forward along a map out of its space.  `pushSpace M b` carries
`b _* M.presheaf` on the target of `b`, and `pushDesc` turns a morphism `g : M ⟶ N` whose base map
*factors* as `b ≫ bb` into a morphism `pushSpace M b ⟶ N` with base map `bb`.  This is what
confines the base-map transport of the whole construction to a single place: a lift against a
limiting cone of spaces satisfies its factorization only propositionally, and `pushDesc` absorbs
that propositional equality into one `eqToHom` between two pushforwards along equal maps.

## Main definitions

* `SheafedSpaceLimit.constTerminalCone`: a cone of spaces, read as a cone of sheafed spaces with
  the constant terminal sheaf on its vertex.
* `SheafedSpaceLimit.pushSpace`, `SheafedSpaceLimit.pushMor`, `SheafedSpaceLimit.pushDesc`: the
  pushforward of a sheafed space along a map of its space, the canonical morphism into it, and
  the morphism out of it attached to a factorization of base maps.

## Main results

* `SheafedSpaceLimit.constTerminal_hom_ext`: a morphism out of a constant terminal sheafed space
  is determined by its base map.
* `SheafedSpaceLimit.hom_c_eq`: two morphisms of presheafed spaces written with the *same* base
  map are equal only if their sheaf components are.
* `SheafedSpaceLimit.pushMor_comp_pushDesc`: `pushDesc` solves the problem it is named for.
* `SheafedSpaceLimit.pushDesc_comp` and `SheafedSpaceLimit.pushDesc_congr`: functoriality of
  `pushDesc` in its morphism, and its independence of the factorization, which is a proposition.

## Implementation notes

The factorization `h : g.hom.base = b ≫ bb` that `pushDesc` consumes is a propositional equality,
and every proof here begins by substituting it: with the two base maps identified the `eqToHom` of
`pushDesc` is the identity by proof irrelevance, and what is left is a composite with identities in
a presheaf category.  That composite is *not* definitional — `Category.comp_id` in a functor
category is componentwise `Category.comp_id` in the target — so each proof ends with a term-mode
composite of `Category.comp_id`, read at one open through `NatTrans.ext`.

The rewriting tactics cannot be used for that last step.  The goals mention `pushSpace` and
`pushDesc`, which are `def`s; once `dsimp` has unfolded them the target is no longer type-correct
at the transparency level at which `rw` and `simp` match, and the `eqToHom` they would have to see
becomes invisible to them — `rw [eqToHom_map]` reports that its own pattern does not occur in a
target that visibly contains it.  Term mode has no such restriction, since `exact` checks
definitional equality at full transparency.

Two definitional facts of `TopCat` are used silently and are worth naming.  Associativity and the
right unit law hold by `rfl` there, because composition is composition of the underlying functions;
that is why the two base maps of `pushDesc_comp`, `(b ≫ bb) ≫ g'.hom.base` and
`b ≫ bb ≫ g'.hom.base`, need no transport between them, and why `pushMor` followed by a morphism
with base map `𝟙` has base map `b` on the nose.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe v u w

namespace Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit

/-! ### Cones with a constant terminal vertex -/

section ConstTerminal

variable {C : Type u} [Category.{v} C] [HasTerminal C]

/-- Two morphisms of sheafed spaces with the same base map are equal once their sheaf components
are. -/
private theorem hom_ext_of_c_eq {C : Type u} [Category.{v} C] {M N : SheafedSpace.{u, v, w} C}
    {b : (M : TopCat.{w}) ⟶ (N : TopCat.{w})} {γ δ : N.presheaf ⟶ b _* M.presheaf} (h : γ = δ) :
    (InducedCategory.homMk { base := b, c := γ } : M ⟶ N) =
      (InducedCategory.homMk { base := b, c := δ } : M ⟶ N) := by
  subst h
  rfl

/-- **A morphism out of a constant terminal sheafed space is determined by its base map.**  Its
sheaf component lands in a pointwise terminal presheaf, so `toConstTerminal_unique` pins it down
once the base maps agree. -/
theorem constTerminal_hom_ext {Z : TopCat.{w}} {Y : SheafedSpace.{u, v, w} C}
    {α β : constTerminal C Z ⟶ Y} (h : α.hom.base = β.hom.base) : α = β := by
  obtain ⟨⟨b, γ⟩⟩ := α
  obtain ⟨⟨b', γ'⟩⟩ := β
  have hb : b = b' := h
  subst hb
  exact hom_ext_of_c_eq (toConstTerminal_unique C b Y.presheaf γ γ')

/-- **A cone of spaces, read as a cone of sheafed spaces with a constant terminal vertex.**  The
base map of the `k`-th leg is the `k`-th leg of the given cone; the sheaf component is the unique
map into the constant terminal sheaf, and the cone identity holds for the same reason, by
`constTerminal_hom_ext`.

The vertex sheaf carries no information.  What the lift is for is that
`SheafedSpaceLimit.pullSystem` and everything proved about it in
`StacksDraft.Ch20.Sec16.Tag0A37PullSystem` depends on its cone only through the base maps of the
legs, so the lift transports that whole development to a cone of spaces. -/
def constTerminalCone {K : Type*} [Category K] (E : K ⥤ SheafedSpace.{u, v, w} C)
    (c₀ : Cone (E ⋙ SheafedSpace.forget C)) : Cone E where
  pt := constTerminal C c₀.pt
  π :=
    { app := fun k => constTerminalHomMk C (c₀.π.app k)
      naturality := fun _ k' a => constTerminal_hom_ext
        ((Category.id_comp (c₀.π.app k')).trans (c₀.w a).symm) }

/-- The base map of the `k`-th leg of `constTerminalCone` is the `k`-th leg of the given cone of
spaces. -/
lemma constTerminalCone_base {K : Type*} [Category K] (E : K ⥤ SheafedSpace.{u, v, w} C)
    (c₀ : Cone (E ⋙ SheafedSpace.forget C)) (k : K) :
    ((constTerminalCone E c₀).π.app k).hom.base = c₀.π.app k := rfl

end ConstTerminal

/-! ### Morphisms of presheafed spaces with a common base map -/

/-- **Two morphisms of presheafed spaces written with the same base map are equal only if their
sheaf components are.**  The sheaf component has a type depending on the base map, so this is not
a projection of an arbitrary equality of morphisms; with the base map shared it is plain
injectivity of the structure. -/
theorem hom_c_eq {C : Type u} [Category.{v} C] {P Q : PresheafedSpace C}
    {bs : (P : TopCat) ⟶ (Q : TopCat)} {γ δ : Q.presheaf ⟶ bs _* P.presheaf}
    (h : PresheafedSpace.Hom.mk bs γ = PresheafedSpace.Hom.mk bs δ) : γ = δ := by
  injection h with _ h

/-! ### Pushing the sheaf on a sheafed space forward along a map of its base -/

section Push

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} (M : SheafedSpace.{u, v, w} C)
  (b : (M : TopCat.{w}) ⟶ X)

/-- The space `X`, carrying the pushforward along `b` of the sheaf of `M`.  The sheaf condition is
`TopCat.Sheaf.pushforward_sheaf_of_sheaf`. -/
def pushSpace : SheafedSpace.{u, v, w} C where
  carrier := X
  presheaf := b _* M.presheaf
  IsSheaf := TopCat.Sheaf.pushforward_sheaf_of_sheaf b M.IsSheaf

/-- The canonical morphism `M ⟶ pushSpace M b`: the base map is `b`, and the sheaf component is
the identity, the target sheaf being the pushforward itself. -/
def pushMor : M ⟶ pushSpace M b :=
  InducedCategory.homMk { base := b, c := 𝟙 _ }

variable {N : SheafedSpace.{u, v, w} C}

/-- **A morphism out of `pushSpace M b`, from a morphism out of `M` whose base map factors through
`b`.**  The base map is the second factor and the sheaf component is the one of `g`, read through
the identification of `g.hom.base _* M.presheaf` with `(b ≫ bb) _* M.presheaf`.  The two double
pushforwards agree on the nose, `Opens.map` of a composite being `rfl`, so that identification is
a single `eqToHom`, and it is the only place in this development where the factorization of a base
map enters a definition. -/
def pushDesc (g : M ⟶ N) (bb : X ⟶ (N : TopCat.{w})) (h : g.hom.base = b ≫ bb) :
    pushSpace M b ⟶ N :=
  InducedCategory.homMk
    { base := bb
      c := g.hom.c ≫ eqToHom (congrArg
        (fun m => (TopCat.Presheaf.pushforward C m).obj M.presheaf) h) }

/-- The base map of `pushDesc` is the prescribed one. -/
lemma pushDesc_hom_base (g : M ⟶ N) (bb : X ⟶ (N : TopCat.{w})) (h : g.hom.base = b ≫ bb) :
    (pushDesc M b g bb h).hom.base = bb := rfl

/-- The sheaf component of `pushDesc` is the sheaf component of `g`, transported. -/
lemma pushDesc_hom_c (g : M ⟶ N) (bb : X ⟶ (N : TopCat.{w})) (h : g.hom.base = b ≫ bb) :
    (pushDesc M b g bb h).hom.c = g.hom.c ≫ eqToHom (congrArg
      (fun m => (TopCat.Presheaf.pushforward C m).obj M.presheaf) h) := rfl

/-- **`pushDesc` depends on nothing but the morphism and the base map it is given**, the
factorization between them being a proposition.  This is what lets a cone identity be pushed
forward: the two legs of the pushed cone are `pushDesc` of equal morphisms at equal base maps, and
their factorizations need not be compared. -/
lemma pushDesc_congr {g g' : M ⟶ N} {bb bb' : X ⟶ (N : TopCat.{w})} (hg : g = g') (hb : bb = bb')
    (h : g.hom.base = b ≫ bb) (h' : g'.hom.base = b ≫ bb') :
    pushDesc M b g bb h = pushDesc M b g' bb' h' := by
  subst hg
  subst hb
  rfl

/-- **`pushDesc` solves the problem it is named for**: composing it with `pushMor` recovers `g`.
With the factorization substituted, the sheaf component of the composite is that of `g` followed
by two identities. -/
lemma pushMor_comp_pushDesc (g : M ⟶ N) (bb : X ⟶ (N : TopCat.{w}))
    (h : g.hom.base = b ≫ bb) : pushMor M b ≫ pushDesc M b g bb h = g := by
  obtain ⟨⟨gb, gc⟩⟩ := g
  have h' : gb = b ≫ bb := h
  subst h'
  refine hom_ext_of_c_eq (NatTrans.ext (funext fun U => ?_))
  dsimp only [pushMor, pushDesc, InducedCategory.homMk]
  exact (Category.comp_id _).trans (Category.comp_id _)

/-- **`pushDesc` is functorial in its morphism**: postcomposing with `g'` is `pushDesc` of the
composite, at the composed base map.  The two base maps agree on the nose, associativity in
`TopCat` being definitional, so only the sheaf components are compared. -/
lemma pushDesc_comp (g : M ⟶ N) (bb : X ⟶ (N : TopCat.{w})) (h : g.hom.base = b ≫ bb)
    {N' : SheafedSpace.{u, v, w} C} (g' : N ⟶ N')
    (h' : (g ≫ g').hom.base = b ≫ bb ≫ g'.hom.base) :
    pushDesc M b g bb h ≫ g' = pushDesc M b (g ≫ g') (bb ≫ g'.hom.base) h' := by
  obtain ⟨⟨gb, gc⟩⟩ := g
  have hgb : gb = b ≫ bb := h
  subst hgb
  refine hom_ext_of_c_eq (NatTrans.ext (funext fun U => ?_))
  dsimp only [pushDesc, InducedCategory.homMk]
  exact (congrArg (fun t => g'.hom.c.app U ≫ t) (Category.comp_id _)).trans
    (Category.comp_id _).symm

end Push

end Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit

end
