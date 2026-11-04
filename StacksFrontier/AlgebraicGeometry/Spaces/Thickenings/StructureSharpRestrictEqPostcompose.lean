module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEq
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqCompose
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-!
# The comparison of two direct images is compatible with postcomposition

Let `G ⊂ X'` be a thickening of algebraic spaces with inclusion `i : X ⟶ X'`, let
`a', b' : X' ⟶ Y'` be two morphisms with `i ≫ a' = i ≫ b'`, and let `q : Y' ⟶ Bb` be a morphism
with `a' ≫ q = b' ≫ q` — the two morphisms being morphisms over `Bb`.  The comparison
`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq` of the two direct images of
[Stacks Project, Tag 05ZM] is characterised only on a sheaf of the form `i_*F`
(`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward`), `i_*`
being an equivalence.

This file proves that read through `q_*` it **is** the comparison that `a' ≫ q = b' ≫ q`
induces, `AlgebraicGeometry.Space.smallEtaleCompPushforwardIsoOfCompEq`, at *every* sheaf.  With
it the difference of the two structure maps of two lifts may be computed on a sheaf pulled back
from `Bb`, which says that the difference kills `q^{-1}𝒪_{Bb}` and is therefore a
`Bb`-derivation, as hypothesis `hφ` of [Stacks Project, Tag 0618] requires.

## Main results

* `Stacks.CategoryTheory.comp_eq_of_cocycle_chase`: the whole chase as one bookkeeping lemma
  with every datum a variable — twelve morphisms, one invertible, and five equations.
* `AlgebraicGeometry.Space.eqToIso_pushforward_hom_app`: the transport along an equality of
  morphisms, taken between the direct image *functors* and then read at a sheaf, is the
  transport taken between that sheaf's two direct images.  This is the respelling on which
  everything here turns.
* `AlgebraicGeometry.Space.map_eqToHom_comp_smallToposMorphismTypeU_comp` and
  `AlgebraicGeometry.Space.eqToHom_comp_smallToposMorphismTypeU_comp`: the two slots'
  bookkeeping lemmas of
  `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqCompose`, restated
  with object-level transports.
* `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_postcomp_cocycle`: the chase at an
  arbitrary inclusion, with no thickening and no comparison of [Stacks Project, Tag 05ZM]
  involved — only the composition isomorphism of [Stacks Project, Tag 03G2] part (3) and its
  associativity cocycle.
* `AlgebraicGeometry.Space.whiskerRight_smallEtalePushforwardIsoOfRestrictEq_comp`: the
  comparison of Tag 05ZM read through `q_*`, followed by the composition isomorphism at
  `(b', q)`, is the composition isomorphism at `(a', q)` followed by the transport along
  `a' ≫ q = b' ≫ q`.  An equality of natural transformations, so it is detected on the sheaves
  `i_*F` by `CategoryTheory.NatTrans.ext_of_essSurj`, and there the chase applies.
* `AlgebraicGeometry.Space.map_smallEtalePushforwardIsoOfRestrictEq_hom_app`: the same read at
  an arbitrary sheaf, which is the form a consumer uses — and the only form stated, the
  implementation notes saying why the equality of the two *isomorphisms* is not.
* `AlgebraicGeometry.Space.structureSharpPush_comp_map_smallEtalePushforwardIsoOfRestrictEq`:
  the consequence for the structure maps — the structure map of `a'`, read into the direct image
  along `b'` through the comparison of Tag 05ZM and then along `q`, agrees with that of `b'`
  after the structure map of `q`.  Both sides are the structure map of the common composite
  `a' ≫ q = b' ≫ q`.  **This is the content of hypothesis (1) of [Stacks Project, Tag 0618]**:
  the difference of the two structure maps kills `𝒪_{Bb}`, so it is a `Bb`-derivation.

## Implementation notes

Every transport is taken at the level of objects.  Identifying the two bracketings
`(i ≫ a') ≫ q` and `i ≫ (a' ≫ q)` inside an object-level transport
`eqToHom (congrArg (fun k ↦ (smallToposMorphismTypeU B S hS k).pushforward.obj F) _)` is cheap,
associativity of composition in `AlgebraicGeometry.Space.AlgebraicSpaces` being definitional;
inside a functor-level transport
`(eqToIso (congrArg (fun k ↦ (smallToposMorphismTypeU B S hS k).pushforward) _)).hom.app F` it
forces `(smallToposMorphismTypeU _).pushforward` to be unfolded, and the kernel times out.  A
functor-level transport handed in by a definition is converted once with
`AlgebraicGeometry.Space.eqToIso_pushforward_hom_app`.

The chase is stated once with every datum a variable,
`Stacks.CategoryTheory.comp_eq_of_cocycle_chase`, and instantiated by a term.  At the
instantiation `CategoryTheory.Category.assoc` cannot be rewritten (nor used by `simp only`): in
the composite `comp(b', q).hom.app (i_*F) ≫ comp(i, b' ≫ q).hom.app F` the target of the first
factor is spelled `(b' ≫ q)_*(i_*F)` and the source of the second
`(MorphismOfTopoi.comp (b' ≫ q) i)_*F`, which are definitionally but not syntactically equal.

Only the pointwise equation is stated, not the equality of the two *isomorphisms*:
`AlgebraicGeometry.Space.smallEtaleCompPushforwardIsoOfCompEq` carries the inverse of a
composition isomorphism, and cancelling an isomorphism of functors is too expensive to
elaborate.  The pointwise equation determines the comparison, the composition isomorphism being
invertible.

`(smallEtaleCompPushforwardIsoOfRestrictEq ...).hom.app F` is read as the composite of its three
factors through `AlgebraicGeometry.Space.smallEtaleCompPushforwardIsoOfRestrictEq_eq`, an
equality of isomorphisms, and `CategoryTheory.NatTrans.congr_app`, never by `rfl` under
`.hom.app`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryTheory

open _root_.CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- **The cocycle chase comparing two comparisons of direct images**, with every datum a
variable.

Read at the geometric instantiation: `pA`, `pE` and `pBi` are the three factors of the
comparison of [Stacks Project, Tag 05ZM] on a sheaf `i_*F`, pushed forward along `q`; `pB` is
the inverse of the third; `cb` and `cqb`, `cqa` and `cia` are composition isomorphisms of
[Stacks Project, Tag 03G2] part (3); `cib` is the one which is cancelled; `eh` and `ehq` are the
two transports.  The five hypotheses are the two instances of the associativity cocycle and the
two slots' bookkeeping lemmas, plus the invertibility of the third factor.

Stated generically because `CategoryTheory.Category.assoc` is not rewritable at the
instantiation; see the implementation notes. -/
theorem comp_eq_of_cocycle_chase {a b c d e t g u : C}
    (pA : a ⟶ b) (pE : b ⟶ c) (pBi : c ⟶ d) (pB : d ⟶ c) (cb : d ⟶ e)
    (cib : e ≅ t) (cqb : c ⟶ t) (cqa : b ⟶ u) (eh : u ⟶ t) (ca : a ⟶ g)
    (cia : g ⟶ u) (ehq : g ⟶ e)
    (hBi : pBi ≫ pB = 𝟙 c) (hb : pB ≫ cqb = cb ≫ cib.hom)
    (ha : pA ≫ cqa = ca ≫ cia) (hs1 : pE ≫ cqb = cqa ≫ eh)
    (hs3 : ehq ≫ cib.hom = cia ≫ eh) :
    pA ≫ pE ≫ pBi ≫ cb = ca ≫ ehq := by
  refine (Iso.cancel_iso_hom_right _ _ cib).mp ?_
  simp only [Category.assoc]
  rw [← hb, hs3, ← Category.assoc pBi pB cqb, hBi, Category.id_comp, hs1,
    ← Category.assoc, ha, Category.assoc]

end Stacks.CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transports at the level of objects -/

section Obj

variable {U V W : AlgebraicSpaces B S hS}

/-- **The transport along an equality of morphisms, read at a sheaf, is the transport between
that sheaf's two direct images.**  The left-hand side is the transport between the two direct
image *functors*; the right-hand side mentions only their values at `F`.

The two are equal, and only the right-hand side is affordable: identifying two differently
bracketed spellings of one morphism inside an `eqToHom` costs, at functor level, an unfolding of
`AlgebraicGeometry.Space.smallToposMorphismTypeU`, and at object level nothing.  See the
implementation notes. -/
theorem eqToIso_pushforward_hom_app {k₁ k₂ : U ⟶ V} (e : k₁ = k₂)
    (F : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    (eqToIso (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward) e)).hom.app F =
      eqToHom (congrArg
        (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj F) e) := by
  subst e
  simp

/-- **A transport along an equality of the first morphism crosses the composition isomorphism**,
with object-level transports.  This is
`AlgebraicGeometry.Space.map_eqToIso_comp_smallToposMorphismTypeU_comp` respelled so that no
transport between direct image functors occurs. -/
theorem map_eqToHom_comp_smallToposMorphismTypeU_comp {k₁ k₂ : U ⟶ V} (e : k₁ = k₂) (q : V ⟶ W)
    (e' : k₁ ≫ q = k₂ ≫ q) (F : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    (smallToposMorphismTypeU B S hS q).pushforward.map
          (eqToHom (congrArg
            (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj F) e)) ≫
        (smallToposMorphismTypeU_comp B S hS k₂ q).hom.app F =
      (smallToposMorphismTypeU_comp B S hS k₁ q).hom.app F ≫
        eqToHom (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj F) e') := by
  subst e
  have he' : e' = rfl := rfl
  subst he'
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
  exact Category.id_comp ((smallToposMorphismTypeU_comp B S hS k₁ q).hom.app F)

/-- **A transport along an equality of the second morphism crosses the composition
isomorphism**, with object-level transports.  This is
`AlgebraicGeometry.Space.eqToIso_comp_smallToposMorphismTypeU_comp` respelled the same way.

Because the transport is object-level, this fires at `g₁ := a' ≫ q` and `g₂ := b' ≫ q` with the
*left*-bracketed equality `(i ≫ a') ≫ q = (i ≫ b') ≫ q` supplied for `e'`, which is what the
first slot's lemma produces.  That coercion is the one the kernel could not afford at functor
level. -/
theorem eqToHom_comp_smallToposMorphismTypeU_comp (i : U ⟶ V) {g₁ g₂ : V ⟶ W} (e : g₁ = g₂)
    (e' : i ≫ g₁ = i ≫ g₂) (F : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    eqToHom (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj
            ((smallToposMorphismTypeU B S hS i).pushforward.obj F)) e) ≫
        (smallToposMorphismTypeU_comp B S hS i g₂).hom.app F =
      (smallToposMorphismTypeU_comp B S hS i g₁).hom.app F ≫
        eqToHom (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj F) e') := by
  subst e
  have he' : e' = rfl := rfl
  subst he'
  simp only [eqToHom_refl, Category.comp_id]
  exact Category.id_comp ((smallToposMorphismTypeU_comp B S hS i g₁).hom.app F)

end Obj

/-! ### The chase, with no thickening -/

section Cocycle

variable {U V W Z : AlgebraicSpaces B S hS}

/-- **The cocycle chase at an arbitrary inclusion.**  The three factors of the comparison of
[Stacks Project, Tag 05ZM] on a sheaf `i_*F` — the composition isomorphism at `(i, a')`, the
transport along `i ≫ a' = i ≫ b'` and the inverse of the composition isomorphism at `(i, b')` —
pushed forward along `q` and followed by the composition isomorphism at `(b', q)`, are the
composition isomorphism at `(a', q)` followed by the transport along `a' ≫ q = b' ≫ q`.

No thickening is involved and the comparison of Tag 05ZM does not appear: the inputs are the
associativity cocycle `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc` of
[Stacks Project, Tag 03G2] part (3) at `(i, a', q)` and at `(i, b', q)`, and the two slots'
bookkeeping lemmas. -/
theorem smallToposMorphismTypeU_comp_postcomp_cocycle (i : U ⟶ V) (a' b' : V ⟶ W) (q : W ⟶ Z)
    (h : i ≫ a' = i ≫ b') (hq : a' ≫ q = b' ≫ q) (h' : (i ≫ a') ≫ q = (i ≫ b') ≫ q)
    (F : Sheaf (SmallEtale.topology B S hS U.1) (Type u)) :
    (smallToposMorphismTypeU B S hS q).pushforward.map
          ((smallToposMorphismTypeU_comp B S hS i a').hom.app F) ≫
        (smallToposMorphismTypeU B S hS q).pushforward.map
          (eqToHom (congrArg
            (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj F) h)) ≫
        (smallToposMorphismTypeU B S hS q).pushforward.map
          ((smallToposMorphismTypeU_comp B S hS i b').inv.app F) ≫
        (smallToposMorphismTypeU_comp B S hS b' q).hom.app
          ((smallToposMorphismTypeU B S hS i).pushforward.obj F) =
      (smallToposMorphismTypeU_comp B S hS a' q).hom.app
          ((smallToposMorphismTypeU B S hS i).pushforward.obj F) ≫
        eqToHom (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj
            ((smallToposMorphismTypeU B S hS i).pushforward.obj F)) hq) := by
  have hBi : (smallToposMorphismTypeU B S hS q).pushforward.map
        ((smallToposMorphismTypeU_comp B S hS i b').inv.app F) ≫
      (smallToposMorphismTypeU B S hS q).pushforward.map
        ((smallToposMorphismTypeU_comp B S hS i b').hom.app F) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact Stacks.CategoryTheory.comp_eq_of_cocycle_chase _ _ _ _ _
    ((smallToposMorphismTypeU_comp B S hS i (b' ≫ q)).app F) _ _ _ _ _ _
    hBi (smallToposMorphismTypeU_comp_assoc B S hS i b' q F)
    (smallToposMorphismTypeU_comp_assoc B S hS i a' q F)
    (map_eqToHom_comp_smallToposMorphismTypeU_comp B S hS h q h' F)
    (eqToHom_comp_smallToposMorphismTypeU_comp B S hS i hq h' F)

end Cocycle

/-! ### The compatibility of the comparison of Tag 05ZM with postcomposition -/

section Restrict

variable {X' Y' Bb : AlgebraicSpaces B S hS} {G : Subfunctor X'.1}
  (hG : IsThickening B S hS X' G) (a' b' : X' ⟶ Y')
  (h : IsThickening.inclusion B S hS hG ≫ a' = IsThickening.inclusion B S hS hG ≫ b')

/-- **The comparison of the two direct images of [Stacks Project, Tag 05ZM], read through
`q_*`, is the comparison induced by `a' ≫ q = b' ≫ q`** — in the form with no inverse: followed
by the composition isomorphism at `(b', q)` it is the composition isomorphism at `(a', q)`
followed by the transport along the hypothesis.

This is an equality of natural transformations, so
`CategoryTheory.NatTrans.ext_of_essSurj` detects it on the sheaves `i_*F`, the direct image
along the inclusion of the thickening being an equivalence; and there the comparison of Tag 05ZM
is the composite of three factors by
`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward`, so
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_postcomp_cocycle` applies. -/
theorem whiskerRight_smallEtalePushforwardIsoOfRestrictEq_comp (q : Y' ⟶ Bb)
    (hq : a' ≫ q = b' ≫ q) :
    Functor.whiskerRight (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom
          (smallToposMorphismTypeU B S hS q).pushforward ≫
        (smallToposMorphismTypeU_comp B S hS b' q).hom =
      (smallToposMorphismTypeU_comp B S hS a' q).hom ≫
        (eqToIso (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward) hq)).hom := by
  let := isEquivalence_smallEtaleDirectImage_of_isThickening B S hS hG
  refine NatTrans.ext_of_essSurj
    (smallToposMorphismTypeU B S hS (IsThickening.inclusion B S hS hG)).pushforward
    (fun F => ?_)
  have e0 : (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app
        ((smallToposMorphismTypeU B S hS
          (IsThickening.inclusion B S hS hG)).pushforward.obj F) =
      (smallToposMorphismTypeU_comp B S hS
            (IsThickening.inclusion B S hS hG) a').hom.app F ≫
        eqToHom (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj F) h) ≫
        (smallToposMorphismTypeU_comp B S hS
          (IsThickening.inclusion B S hS hG) b').inv.app F := by
    rw [smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward,
      ← eqToIso_pushforward_hom_app B S hS h F]
    exact NatTrans.congr_app
      (congrArg Iso.hom (smallEtaleCompPushforwardIsoOfRestrictEq_eq B S hS hG a' b' h)) F
  have e2 : (smallToposMorphismTypeU B S hS q).pushforward.map
        ((smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app
          ((smallToposMorphismTypeU B S hS
            (IsThickening.inclusion B S hS hG)).pushforward.obj F)) =
      (smallToposMorphismTypeU B S hS q).pushforward.map
          ((smallToposMorphismTypeU_comp B S hS
            (IsThickening.inclusion B S hS hG) a').hom.app F) ≫
        (smallToposMorphismTypeU B S hS q).pushforward.map
          (eqToHom (congrArg
            (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj F) h)) ≫
        (smallToposMorphismTypeU B S hS q).pushforward.map
          ((smallToposMorphismTypeU_comp B S hS
            (IsThickening.inclusion B S hS hG) b').inv.app F) := by
    exact (congrArg _ e0).trans
      ((Functor.map_comp _ _ _).trans (congrArg _ (Functor.map_comp _ _ _)))
  exact (congrArg (fun m => m ≫ (smallToposMorphismTypeU_comp B S hS b' q).hom.app
        ((smallToposMorphismTypeU B S hS
          (IsThickening.inclusion B S hS hG)).pushforward.obj F)) e2).trans
    ((smallToposMorphismTypeU_comp_postcomp_cocycle B S hS
        (IsThickening.inclusion B S hS hG) a' b' q h hq
        (congrArg (fun k => k ≫ q) h) F).trans
      (congrArg (fun m => (smallToposMorphismTypeU_comp B S hS a' q).hom.app
          ((smallToposMorphismTypeU B S hS
            (IsThickening.inclusion B S hS hG)).pushforward.obj F) ≫ m)
        (eqToIso_pushforward_hom_app B S hS hq
          ((smallToposMorphismTypeU B S hS
            (IsThickening.inclusion B S hS hG)).pushforward.obj F)).symm))

/-- **The same read at an arbitrary sheaf**, which is the form a consumer uses: the comparison
of [Stacks Project, Tag 05ZM] at `X`, pushed forward along `q` and followed by the composition
isomorphism at `(b', q)`, is the composition isomorphism at `(a', q)` followed by the transport
along `a' ≫ q = b' ≫ q`.

Nothing is known about the comparison of Tag 05ZM at a sheaf which is not a direct image along
the inclusion; what is known is this equation, and it holds at every sheaf because both sides
are natural. -/
theorem map_smallEtalePushforwardIsoOfRestrictEq_hom_app (q : Y' ⟶ Bb)
    (hq : a' ≫ q = b' ≫ q) (X : Sheaf (SmallEtale.topology B S hS X'.1) (Type u)) :
    (smallToposMorphismTypeU B S hS q).pushforward.map
          ((smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app X) ≫
        (smallToposMorphismTypeU_comp B S hS b' q).hom.app X =
      (smallToposMorphismTypeU_comp B S hS a' q).hom.app X ≫
        eqToHom (congrArg
          (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj X) hq) :=
  (NatTrans.congr_app
      (whiskerRight_smallEtalePushforwardIsoOfRestrictEq_comp B S hS hG a' b' h q hq) X).trans
    (congrArg (fun m => (smallToposMorphismTypeU_comp B S hS a' q).hom.app X ≫ m)
      (eqToIso_pushforward_hom_app B S hS hq X))

/-- **The two structure maps of two lifts agree after the comparison of [Stacks Project,
Tag 05ZM], once both are read on the structure sheaf of the base** — at the level of sheaves of
sets.

Both sides are the structure map of the common composite `a' ≫ q = b' ≫ q`, read backwards
through the composition isomorphism of [Stacks Project, Tag 03G2] part (3) at `(b', q)`: the
left-hand side by
`AlgebraicGeometry.Space.map_smallEtalePushforwardIsoOfRestrictEq_hom_app` followed by
`AlgebraicGeometry.Space.structureSharpPush_comp` at `(a', q)` and the transport
`AlgebraicGeometry.Space.structureSharpPush_comp_eqToIso_hom_app`, the right-hand side by
`AlgebraicGeometry.Space.structureSharpPush_comp` at `(b', q)`.

This is the statement that the difference of the two structure maps of two lifts kills the
structure sheaf of `Bb`, and so is a `Bb`-derivation — the content of hypothesis (1) of
[Stacks Project, Tag 0618].  Unlike
`AlgebraicGeometry.Space.structureSharpPush_comp_smallEtalePushforwardIsoOfRestrictEq`, which
composes with the structure map of the inclusion and so says nothing a difference landing in the
defining ideal does not already say, this is read against `𝒪_{Bb}` and is the real content. -/
theorem structureSharpPush_comp_map_smallEtalePushforwardIsoOfRestrictEq (q : Y' ⟶ Bb)
    (hq : a' ≫ q = b' ≫ q) :
    structureSharpPush B S hS q ≫
        (smallToposMorphismTypeU B S hS q).pushforward.map (structureSharpPush B S hS a') ≫
        (smallToposMorphismTypeU B S hS q).pushforward.map
          ((smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app
            (structureSetSheaf B S hS X')) =
      structureSharpPush B S hS q ≫
        (smallToposMorphismTypeU B S hS q).pushforward.map (structureSharpPush B S hS b') := by
  refine (Iso.cancel_iso_hom_right _ _
    ((smallToposMorphismTypeU_comp B S hS b' q).app (structureSetSheaf B S hS X'))).mp ?_
  refine Eq.trans ?_ (((Category.assoc _ _ _).trans
    (structureSharpPush_comp B S hS b' q)).symm)
  refine ((Category.assoc _ _ _).trans
    (congrArg (fun m => structureSharpPush B S hS q ≫ m) (Category.assoc _ _ _))).trans ?_
  refine (congrArg (fun m => structureSharpPush B S hS q ≫
      (smallToposMorphismTypeU B S hS q).pushforward.map (structureSharpPush B S hS a') ≫ m)
    (map_smallEtalePushforwardIsoOfRestrictEq_hom_app B S hS hG a' b' h q hq
      (structureSetSheaf B S hS X'))).trans ?_
  refine (((Category.assoc _ _ _).trans
    (congrArg (fun m => structureSharpPush B S hS q ≫ m)
      (Category.assoc _ _ _))).symm).trans ?_
  refine (congrArg (fun m => m ≫ eqToHom (congrArg
      (fun k => (smallToposMorphismTypeU B S hS k).pushforward.obj
        (structureSetSheaf B S hS X')) hq))
    (structureSharpPush_comp B S hS a' q)).trans ?_
  exact (congrArg (fun m => structureSharpPush B S hS (a' ≫ q) ≫ m)
      (eqToIso_pushforward_hom_app B S hS hq (structureSetSheaf B S hS X')).symm).trans
    (structureSharpPush_comp_eqToIso_hom_app B S hS hq)

end Restrict

end AlgebraicGeometry.Space

end
