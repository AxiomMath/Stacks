module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafEquivalence

/-!
# The two structure maps of two lifts agree after the structure map of the thickening

Let `G ⊂ X'` be a thickening of algebraic spaces over a scheme `S`, with inclusion
`i : X ⟶ X'`, and let `a', b' : X' ⟶ Y'` be two morphisms with `i ≫ a' = i ≫ b'`.  The
structure-sheaf half of [Stacks Project, Tag 05ZM],
`AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfRestrictEq`, puts the two structure
maps `(a')^♯` and `(b')^♯` in parallel as homomorphisms `𝒪_{Y'} ⟶ (b')_*𝒪_{X'}`, the first of
them being `AlgebraicGeometry.Space.structureSharpOfRestrictEq`.

This file proves that the two become **equal** after `(b')_*(i^♯)`, the direct image along `b'`
of the structure map of the inclusion.  That is the first of the two things which the "Partial
coverage" section of `StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDerivation` lists as
owed between the general fact proved there and [Stacks Project, Tag 0618] for two morphisms of
thickenings: it is the hypothesis `hfg` of `AlgebraicGeometry.Space.liftDifference`, read
through the direct image, and it is what makes the difference of the two structure maps take
its values in the defining ideal of the thickening.

## Main definitions

* `AlgebraicGeometry.Space.structureSharpPush`: the structure map of Stacks 03G8 on sheaves of
  sets, with its target spelled as the direct image of the morphism of small étale topoi rather
  than as `AlgebraicGeometry.Space.smallEtaleDirectImage`.  These are the same functor, and the
  point of the respelling is explained in the implementation notes.

## Main results

* `Stacks.CategoryTheory.comp_natIso_app_comp_map_eq`: the bookkeeping, with the functors, the
  comparison isomorphism, the two composition isomorphisms and the two presented composites all
  *variables*.
* `AlgebraicGeometry.Space.structureSharpPush_comp_smallEtalePushforwardIsoOfRestrictEq`: the
  statement at the level of sheaves of sets.
* `AlgebraicGeometry.Space.structureSharpOfRestrictEq_comp_pushforward_structureSharp`: the
  statement for sheaves of rings, which is the form [Stacks Project, Tag 0618] consumes.

## Implementation notes

The mathematics is three steps and no computation with the comparison isomorphism beyond its
characterising property.  Writing `Θ` for the comparison of the two direct images of sheaves of
sets, `AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq`:

* *naturality* of `Θ` at `i^♯ : 𝒪_{X'} ⟶ i_*𝒪_X` moves `Θ` past the direct image of `i^♯`, so
  that it is evaluated at `i_*𝒪_X` rather than at `𝒪_{X'}`;
* at a sheaf in the image of `i_*` the comparison is described by
  `AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward`, namely as
  functoriality of the direct image followed by the hypothesis `i ≫ a' = i ≫ b'`;
* functoriality of the structure map, Stacks 03G8,
  `AlgebraicGeometry.Space.structureSharpSet_comp`, then turns each side into the structure map
  of a composite, and the two composites are equal by hypothesis.

So the comparison isomorphism is never computed: it is used only through naturality and through
the one value which its construction by cancelling an equivalence pins down.

**Why nothing is restated at the geometric instantiation.**  Two spellings of one functor meet
here: the small étale direct image is `AlgebraicGeometry.Space.smallEtaleDirectImage` in the
type of the structure map and `(AlgebraicGeometry.Space.smallToposMorphismTypeU _).pushforward`
in the type of the comparison isomorphism and of the composition isomorphism of Stacks 03G2
part (3).  The two are the same functor, `rfl`, but a *composite* written at both spellings
makes the kernel decide that equality at every object occurring in it, and a `rw` inside such a
composite cannot build a motive either.  So the structure map is respelled once, as
`AlgebraicGeometry.Space.structureSharpPush`, with the composition law and the transport along
an equality of morphisms restated at that spelling — each a declaration of its own, since the
kernel's budget, like the elaborator's, is per declaration.

That by itself is not enough, and the measurement is worth recording.  With the generic lemma
taking the *value* of the comparison and the equality of the two presented composites as its
hypotheses, both hypotheses had to be restated at the instantiation — the first with the three
factors of `AlgebraicGeometry.Space.smallEtaleCompPushforwardIsoOfRestrictEq` displayed, the
second with its composites reassociated — and **each of those two restatements exhausted the
kernel's budget on its own**, even though every term in them is already at one spelling and the
proof of each is a single `exact` or a `congrArg`.  No attribute reaches the kernel, so there is
nothing to switch off.

What works is to put *everything* into the generic lemma: it now takes the comparison of the two
composites as a further variable `Ξ` together with `Ξ = κ ≪≫ Eiso ≪≫ κ'.symm`, and the two
presented composites as variables `τ`, `τ'` with the three equations relating them.  Each of the
five hypotheses is then an **existing lemma applied verbatim** at the instantiation — the value
of the comparison is
`AlgebraicGeometry.Space.smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward`, the two
composites are `AlgebraicGeometry.Space.structureSharpPush_comp`, the comparison of the two
presentations is `AlgebraicGeometry.Space.structureSharpPush_comp_eqToIso_hom_app`, and
`Ξ = κ ≪≫ Eiso ≪≫ κ'.symm` is `rfl`, one delta step of a definition.  Nothing is restated, the
kernel has no conversion to decide, and the file checks in about 45 s.

Transport of the structure map along an equality of morphisms is isolated as
`AlgebraicGeometry.Space.structureSharpPush_comp_eqToIso_hom_app`, where the two morphisms are
*variables* so that the equality can be substituted.

The ring-level statement is deduced from the set-level one rather than proved again: a morphism
of sheaves of rings is determined by its underlying morphism of sheaves of sets, the forgetful
functor being faithful, and both the ring-level comparison
(`AlgebraicGeometry.Space.forget_structureRingSheafDirectImageIsoOfRestrictEq`) and the
ring-level direct image of a homomorphism
(`Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMap`) are known on underlying
sheaves of sets.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback

namespace Stacks.CategoryTheory

open _root_.CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {E : Type u₁} [Category.{v₁} E] {D : Type u₂} [Category.{v₂} D]
  {C : Type u₃} [Category.{v₃} C]

/-- **Two sections of two comparable functors which become equal after a comparison of the
composites with a third functor.**  Let `Θ : A ≅ B` be a comparison of two functors `D ⥤ C`,
let `I : E ⥤ D`, let `κ : I ⋙ A ≅ Ka` and `κ' : I ⋙ B ≅ Kb` present the two composites with
`I`, and let `Ξ : I ⋙ A ≅ I ⋙ B` be `κ`, an isomorphism `Eiso : Ka ≅ Kb` and `κ'` inverted.
Given a morphism `ι : O' ⟶ I.obj O`, two morphisms `σ : R ⟶ A.obj O'` and `σ' : R ⟶ B.obj O'`,
two morphisms `τ : R ⟶ Ka.obj O` and `τ' : R ⟶ Kb.obj O` with

* `Θ.hom.app (I.obj O) = Ξ.hom.app O`, the value of the comparison on the image of `I`,
* `σ ≫ A.map ι ≫ κ.hom.app O = τ` and `σ' ≫ B.map ι ≫ κ'.hom.app O = τ'`, the two presented
  composites, and
* `τ ≫ Eiso.hom.app O = τ'`, the comparison of the two presentations,

the two sections become equal after the direct image of `ι`:
`σ ≫ Θ.hom.app O' ≫ B.map ι = σ' ≫ B.map ι`.

Only naturality of `Θ` and the given value of `Θ` on the image of `I` are used; the comparison
is never computed anywhere else.

Every datum is a variable on purpose.  At a geometric instantiation each of the five hypotheses
is an existing lemma applied, with nothing restated, so the kernel has no conversion to decide:
restating any one of them at the instantiation exhausts the kernel's budget. -/
theorem comp_natIso_app_comp_map_eq {A B : D ⥤ C} (Θ : A ≅ B) {I : E ⥤ D} {Ka Kb : E ⥤ C}
    (κ : I ⋙ A ≅ Ka) (κ' : I ⋙ B ≅ Kb) (Eiso : Ka ≅ Kb) (Ξ : I ⋙ A ≅ I ⋙ B)
    (hΞ : Ξ = κ ≪≫ Eiso ≪≫ κ'.symm) {O : E} {O' : D} (ι : O' ⟶ I.obj O) {R : C}
    (σ : R ⟶ A.obj O') (σ' : R ⟶ B.obj O') (τ : R ⟶ Ka.obj O) (τ' : R ⟶ Kb.obj O)
    (hΘ : Θ.hom.app (I.obj O) = Ξ.hom.app O)
    (hσ : σ ≫ A.map ι ≫ κ.hom.app O = τ)
    (hσ' : σ' ≫ B.map ι ≫ κ'.hom.app O = τ')
    (hτ : τ ≫ Eiso.hom.app O = τ') :
    σ ≫ Θ.hom.app O' ≫ B.map ι = σ' ≫ B.map ι := by
  subst hΞ
  refine (Iso.cancel_iso_hom_right _ _ (κ'.app O)).mp ?_
  rw [← Θ.hom.naturality ι, hΘ]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.app_hom, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rw [hσ', ← hτ, ← hσ]
  simp only [Category.assoc]

end Stacks.CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The structure map at the spelling of the morphism of topoi -/

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The structure map of Stacks 03G8 on sheaves of sets**, with its target spelled as the
direct image of the morphism of small étale topoi of Stacks 03G2 part (3).  This is
`AlgebraicGeometry.Space.structureSharpSet`; only the spelling of the direct image differs, and
the two spellings are the same functor.  See the implementation notes for why the respelling is
a declaration of its own. -/
noncomputable def structureSharpPush (f : X ⟶ Y) :
    structureSetSheaf B S hS Y ⟶
      (smallToposMorphismTypeU B S hS f).pushforward.obj (structureSetSheaf B S hS X) :=
  structureSharpSet B S hS f

/-- `AlgebraicGeometry.Space.structureSharpPush` is the structure map on sheaves of sets. -/
theorem structureSharpPush_eq (f : X ⟶ Y) :
    structureSharpPush B S hS f = structureSharpSet B S hS f :=
  rfl

/-- **Stacks 03G8, compatibility with composition**, at the spelling of
`AlgebraicGeometry.Space.structureSharpPush`. -/
theorem structureSharpPush_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSharpPush B S hS g ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map (structureSharpPush B S hS f) ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) =
      structureSharpPush B S hS (f ≫ g) :=
  structureSharpSet_comp B S hS f g

/-- **The structure map is transported along an equality of morphisms by the induced
`eqToHom`.**  The two morphisms are variables, so the equality can be substituted; this is the
form in which the hypothesis `i ≫ a' = i ≫ b'` of a pair of lifts is used. -/
theorem structureSharpPush_comp_eqToIso_hom_app {k₁ k₂ : X ⟶ Y} (e : k₁ = k₂) :
    structureSharpPush B S hS k₁ ≫
        (eqToIso (congrArg (fun k => (smallToposMorphismTypeU B S hS k).pushforward)
          e)).hom.app (structureSetSheaf B S hS X) =
      structureSharpPush B S hS k₂ := by
  subst e
  exact Category.comp_id _

/-! ### The two structure maps of two lifts -/

section Restrict

variable {X' Y' : AlgebraicSpaces B S hS} {G : Subfunctor X'.1}
  (hG : IsThickening B S hS X' G) (a' b' : X' ⟶ Y')
  (h : IsThickening.inclusion B S hS hG ≫ a' = IsThickening.inclusion B S hS hG ≫ b')

/-- **The comparison of the two composites with the direct image of the inclusion is the two
composition isomorphisms of Stacks 03G2 part (3) with the transport along the hypothesis
between them.**  This is the definition of
`AlgebraicGeometry.Space.smallEtaleCompPushforwardIsoOfRestrictEq`, stated so that it can be
substituted into the generic bookkeeping lemma. -/
theorem smallEtaleCompPushforwardIsoOfRestrictEq_eq :
    smallEtaleCompPushforwardIsoOfRestrictEq B S hS hG a' b' h =
      smallToposMorphismTypeU_comp B S hS (IsThickening.inclusion B S hS hG) a' ≪≫
        eqToIso (congrArg (fun k => (smallToposMorphismTypeU B S hS k).pushforward) h) ≪≫
        (smallToposMorphismTypeU_comp B S hS (IsThickening.inclusion B S hS hG) b').symm :=
  rfl

/-- **The two structure maps of two lifts agree after the structure map of the thickening**, at
the level of sheaves of sets.  For two morphisms `a', b' : X' ⟶ Y'` agreeing on the closed
subspace `X` of a thickening `G ⊂ X'`, the structure map `(a')^♯`, read into `(b')_*𝒪_{X'}`
through the comparison of [Stacks Project, Tag 05ZM], becomes equal to `(b')^♯` after the
direct image along `b'` of `i^♯ : 𝒪_{X'} ⟶ i_*𝒪_X`.

Both sides are the structure map of `i ≫ a' = i ≫ b'`, read backwards through the composition
isomorphism of Stacks 03G2 part (3). -/
theorem structureSharpPush_comp_smallEtalePushforwardIsoOfRestrictEq :
    structureSharpPush B S hS a' ≫
        (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app
          (structureSetSheaf B S hS X') ≫
        (smallToposMorphismTypeU B S hS b').pushforward.map
          (structureSharpPush B S hS (IsThickening.inclusion B S hS hG)) =
      structureSharpPush B S hS b' ≫
        (smallToposMorphismTypeU B S hS b').pushforward.map
          (structureSharpPush B S hS (IsThickening.inclusion B S hS hG)) :=
  Stacks.CategoryTheory.comp_natIso_app_comp_map_eq
    (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h)
    (smallToposMorphismTypeU_comp B S hS (IsThickening.inclusion B S hS hG) a')
    (smallToposMorphismTypeU_comp B S hS (IsThickening.inclusion B S hS hG) b')
    (eqToIso (congrArg (fun k => (smallToposMorphismTypeU B S hS k).pushforward) h))
    (smallEtaleCompPushforwardIsoOfRestrictEq B S hS hG a' b' h)
    (smallEtaleCompPushforwardIsoOfRestrictEq_eq B S hS hG a' b' h)
    (structureSharpPush B S hS (IsThickening.inclusion B S hS hG))
    (structureSharpPush B S hS a') (structureSharpPush B S hS b')
    (structureSharpPush B S hS (IsThickening.inclusion B S hS hG ≫ a'))
    (structureSharpPush B S hS (IsThickening.inclusion B S hS hG ≫ b'))
    (smallEtalePushforwardIsoOfRestrictEq_hom_app_pushforward B S hS hG a' b' h _)
    (structureSharpPush_comp B S hS (IsThickening.inclusion B S hS hG) a')
    (structureSharpPush_comp B S hS (IsThickening.inclusion B S hS hG) b')
    (structureSharpPush_comp_eqToIso_hom_app B S hS h)

/-- The underlying morphism of sheaves of sets of
`AlgebraicGeometry.Space.structureSharpOfRestrictEq` is the structure map of `a'` followed by
the comparison of the two direct images of sheaves of sets. -/
theorem forget_structureSharpOfRestrictEq :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (structureSharpOfRestrictEq B S hS hG a' b' h) =
      structureSharpPush B S hS a' ≫
        (smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h).hom.app
          (structureSetSheaf B S hS X') :=
  (Functor.map_comp _ _ _).trans
    (congrArg (fun m => structureSharpPush B S hS a' ≫ m)
      (forget_structureRingSheafDirectImageIsoOfRestrictEq B S hS hG a' b' h))

/-- The underlying morphism of sheaves of sets of the direct image along `b'` of the structure
map of the inclusion is the direct image of its own underlying morphism of sheaves of sets. -/
theorem forget_pullbackRingSheafMap_structureSharp_inclusion :
    (sheafCompose (SmallEtale.topology B S hS Y'.1) (forget RingCat.{u})).map
        (pullbackRingSheafMap.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y'.1)
          (smallEtaleDirectImage B S hS b')
          (structureSharp B S hS (IsThickening.inclusion B S hS hG))) =
      (smallToposMorphismTypeU B S hS b').pushforward.map
        (structureSharpPush B S hS (IsThickening.inclusion B S hS hG)) :=
  ringSheafMap_pullbackRingSheafMap.{u, u, u, u + 1, u, u + 1} _ _ _

/-- **The two structure maps of two lifts agree after the structure map of the thickening**, for
sheaves of rings.  This is the hypothesis which [Stacks Project, Tag 0618] needs of the pair
`AlgebraicGeometry.Space.structureSharpOfRestrictEq`, `(b')^♯`: read into the direct image along
`b'` of `i_*𝒪_X` the two homomorphisms coincide, so their difference takes its values in the
defining ideal of the thickening.

It is the set-level statement with the ring operations carried along: the forgetful functor on
sheaves of rings is faithful, and both the comparison and the direct image of a homomorphism are
known on underlying sheaves of sets. -/
@[stacks 0618 "the two structure maps of two lifts of one morphism become equal after the \
  structure map of the thickening, so their difference lands in the defining ideal"]
theorem structureSharpOfRestrictEq_comp_pushforward_structureSharp :
    structureSharpOfRestrictEq B S hS hG a' b' h ≫
        pullbackRingSheafMap.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y'.1)
          (smallEtaleDirectImage B S hS b')
          (structureSharp B S hS (IsThickening.inclusion B S hS hG)) =
      structureSharp B S hS b' ≫
        pullbackRingSheafMap.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y'.1)
          (smallEtaleDirectImage B S hS b')
          (structureSharp B S hS (IsThickening.inclusion B S hS hG)) := by
  refine (sheafCompose (SmallEtale.topology B S hS Y'.1)
    (forget RingCat.{u})).map_injective ?_
  refine ((Functor.map_comp _ _ _).trans ?_).trans (Functor.map_comp _ _ _).symm
  rw [forget_pullbackRingSheafMap_structureSharp_inclusion B S hS hG b',
    forget_structureSharpOfRestrictEq B S hS hG a' b' h]
  exact (Category.assoc _ _ _).trans
    (structureSharpPush_comp_smallEtalePushforwardIsoOfRestrictEq B S hS hG a' b' h)

end Restrict

end AlgebraicGeometry.Space

end
