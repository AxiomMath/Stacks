module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Neighbourhoods
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtaleAlgebra
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SectionsExtendFromCompletion

/-!
# Sections of an affine morphism near a closed subscheme, over a varying open neighbourhood

Let `c : Y ⟶ S` be a closed immersion and `f : U ⟶ S` an affine morphism. This file carries the
geometric bookkeeping which reduces the *shrinking* form of the section-extension statement —
a section of `f` over `Y` extends to a section over some open neighbourhood of `Y`, and two
sections over neighbourhoods which agree over `Y` agree over a smaller one — to statements about
morphisms of `𝒪_S`-modules out of the one direct image algebra `A = f _* 𝒪_U`. There is no
mathematical input here: the statements about modules are carried as explicit hypotheses, exactly
as `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful`
carries its `h0GN2` and `halgebra`, and another module supplies them from
`Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete`.

**Why no module is ever restricted to an open.** By the universal property of the relative
spectrum ([Stacks, Tag 01SA]), uniformly in the base, a section of `f` over an `S`-scheme `G` is
a morphism of sheaves of `𝒪_S`-algebras `f _* 𝒪_U ⟶ G.hom _* 𝒪_{G.left}`, and that is a
statement on the one fixed base `S`. So a section over an open `W ⊆ S`, a section over an
infinitesimal neighbourhood `Y_n` of `Y` in `S`, and a section over `Y` are all morphisms out of
the single algebra `A`, with targets `W.ι _* 𝒪_W`, `(Y_n → S) _* 𝒪_{Y_n}` and `c _* 𝒪_Y`; and
restriction along a morphism of `S`-schemes is composition with the canonical map
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap` attached to it. Neither the restriction
of a module to an open subscheme nor any pullback appears anywhere below, and the infinitesimal
neighbourhoods are always the ones computed in `S`.

**The maps a neighbourhood comes with.** An open `W` whose underlying set contains the image of
`c` receives each infinitesimal neighbourhood of `Y`, because an infinitesimal neighbourhood has
the same image as the closed immersion itself
(`Stacks.Algebraization.range_nthInfinitesimalNeighbourhoodι`); the factorisation is unique,
since `W.ι` is a monomorphism, and all the compatibilities between these factorisations below are
proved by cancelling it. That gives, for each `n`, a canonical map
`W.ι _* 𝒪_W ⟶ (Y_n → S) _* 𝒪_{Y_n}` of algebras and of underlying modules
(`nthOrderOpenAlgebraMap`, `nthOrderOpenUnitMap`), compatible with shrinking `W`
(`nthOrderOpenUnitMap_openRestriction`). These are the maps in which the hypotheses of the two
bridges are phrased, and the module ones are typed in the direct-image spelling
`(Scheme.Modules.pushforward W.ι).obj (SheafOfModules.unit _)` of the module underlying
`W.ι _* 𝒪_W`, which is the spelling the completion side speaks.

## Main results

* `Stacks.FundamentalGroup.exists_shrink_eq_of_restrict_eq` — the uniqueness half: two sections
  of `f` over two open neighbourhoods of `Y` which induce the same section over `Y` agree over a
  smaller common neighbourhood, granted that two module maps whose composites down to all the
  infinitesimal neighbourhoods agree are equal after shrinking.
* `Stacks.FundamentalGroup.exists_section_on_open_of_bridge` — the extension half: a section of
  `f` over `Y` is the restriction of a section of `f` over some open neighbourhood of `Y`,
  granted that a compatible system of module maps into the infinitesimal neighbourhoods is
  algebraized over some neighbourhood and that the algebraization is multiplicative.
* `Stacks.FundamentalGroup.bijective_restrictSection_nthOrder_finiteEtale` — the lifting
  hypothesis both bridges ask for, discharged for a finite étale cover from
  `bijective_restrictSection_nthOrderInclusion`.

## Implementation notes

**These are auxiliary lemmas and carry no `@[stacks]` attribute.** Neither is a clause of any
tag: the shrinking statement they are heading for is the conclusion of [Stacks, Tag 0EL8] in the
form [Stacks, Tag 0ELA] consumes it, namely
`Stacks.FundamentalGroup.SectionsExtendNearSubscheme`, and the hypotheses standing for full
faithfulness of completion are assumed rather than proved here.

The non-shrinking form of both halves is carried, at a single scheme, by the two private bridges
`injective_restrictSection_of_bridge` and `surjective_restrictSection_of_bridge` of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/RestrictionToClosedSubscheme.lean`; the proofs
below follow their structure. Their supporting identifications — the universal property read as
`sectionAlgebraEquiv`, its compatibility with restriction, and injectivity of the passage from a
morphism of algebra sheaves to its underlying morphism of modules — are private there. The
universal property itself is `Stacks.FundamentalGroup.sectionAlgebraHomEquiv` of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/SectionsExtendFromCompletion.lean`, which is
public, and is used as it stands: the `S`-schemes over which sections are taken appear below as
objects `G` of `Over S`, so it is applied to their structure morphisms `G.hom`. The other two are
re-proved here as `sectionAlgebraHomEquiv_restrict`,
`underlyingModuleMap_sectionAlgebraHomEquiv_restrict` and `eq_of_underlyingModuleMap_eq`.

Proofs are in term mode, as there: the projection separating a sheaf of modules from its
underlying presheaf is not transparent to `rw`, so the identifications above are chained with
`Eq.trans` and `congrArg` instead of rewritten.

**Two spellings, and how they are kept apart.** The module underlying a direct image algebra has
the two spellings mentioned above, equal by
`Stacks.FundamentalGroup.underlyingModule_pushforwardAlgebra_eq`; the check that identifies them
is cheap when both sides are closed terms, and hopeless when one side is a metavariable, since
`underlyingModule ?A =?= (Scheme.Modules.pushforward g).obj _` has no solution the unifier can
find without unfolding the sheafification of a limit. Two habits keep every crossing of the
closed kind. The implicit arguments of `pushforwardAlgebraMap` are supplied positionally, so that
no `pushforwardAlgebra ?X.hom =?= pushforwardAlgebra g` is ever posed; and each statement whose
two sides are written in different spellings is restated with `show` in the algebra spelling
before its proof term is given, rather than left to be reconciled inside the term.

The two neighbourhood vocabularies of the library are one definition, so no comparison appears:
`Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood c n` and
`Stacks.Algebraization.nthInfinitesimalNeighbourhood c n` are both
`(c.liftCoborder.ker ^ (n + 1)).subscheme`, and `Stacks.Thickenings.nthOrderToBase c n` and
`Stacks.Algebraization.nthInfinitesimalNeighbourhoodι c n` are both
`(c.liftCoborder.ker ^ (n + 1)).subschemeι ≫ c.coborderRange.ι`. Sections over a neighbourhood
are spelled in the first vocabulary, as in the template file; the `Over S`-object and the
transition maps are taken from the second.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0BQB](https://stacks.math.columbia.edu/tag/0BQB)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence Stacks.Thickenings
open Stacks.Algebraization (nthInfinitesimalNeighbourhoodOver
  nthInfinitesimalNeighbourhoodTransition range_nthInfinitesimalNeighbourhoodι)

universe u

namespace Stacks.FundamentalGroup

/-! ### Morphisms of algebra sheaves and their underlying modules -/

/-- Taking underlying modules is compatible with composition of morphisms of algebra sheaves. -/
private theorem underlyingModuleMap_comp_eq {X : Scheme.{u}} {A B C : AlgebraSheaf X}
    (φ : A ⟶ B) (ψ : B ⟶ C) :
    AlgebraSheaf.underlyingModuleMap (φ ≫ ψ) =
      AlgebraSheaf.underlyingModuleMap φ ≫ AlgebraSheaf.underlyingModuleMap ψ :=
  (AlgebraSheaf.underlyingModuleFunctor X).map_comp φ ψ

/-- **A morphism of algebra sheaves is determined by its underlying morphism of modules.** On
sections the underlying morphism of modules is the morphism of the underlying sheaves of rings,
and a morphism of algebra sheaves is determined by that. -/
public theorem eq_of_underlyingModuleMap_eq {X : Scheme.{u}} {A B : AlgebraSheaf X}
    {φ ψ : A ⟶ B}
    (h : AlgebraSheaf.underlyingModuleMap φ = AlgebraSheaf.underlyingModuleMap ψ) : φ = ψ := by
  have happ : ∀ (V : (X.Opens)ᵒᵖ) (x : (A.right.obj.obj V : Type u)),
      (φ.right.hom.app V).hom x = (ψ.right.hom.app V).hom x := fun V x =>
    congrArg (fun χ : AlgebraSheaf.underlyingModule A ⟶ AlgebraSheaf.underlyingModule B =>
      χ.val.app V x) h
  refine Under.UnderMorphism.ext (Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_)))
  exact CommRingCat.hom_ext (RingHom.ext (happ V))

/-! ### Sections of an affine morphism as morphisms out of the direct image algebra -/

/-- Under `sectionAlgebraHomEquiv`, restricting a section along a morphism `k` of `S`-schemes is
composition with the canonical morphism of direct image algebras attached to `k`. The source and
target of `k` are objects of `Over S`, which is the form in which the neighbourhoods below come,
so `sectionAlgebraHomEquiv` is applied to their structure morphisms. -/
public theorem sectionAlgebraHomEquiv_restrict {S U : Scheme.{u}} (f : U ⟶ S) [IsAffineHom f]
    {G G' : Over S} (k : G' ⟶ G) (s : {s : G.left ⟶ U // s ≫ f = G.hom})
    (s' : {s : G'.left ⟶ U // s ≫ f = G'.hom}) (hs' : s'.1 = k.left ≫ s.1) :
    sectionAlgebraHomEquiv f G'.hom s' =
      sectionAlgebraHomEquiv f G.hom s ≫ pushforwardAlgebraMap k := by
  have h1 : (Over.homMk s'.1 s'.2 : (Over.mk G'.hom : Over S) ⟶ Over.mk f) =
      k ≫ (Over.homMk s.1 s.2 : (Over.mk G.hom : Over S) ⟶ Over.mk f) :=
    Over.OverMorphism.ext hs'
  rw [sectionAlgebraHomEquiv_apply, sectionAlgebraHomEquiv_apply, h1, pushforwardAlgebraMap_comp]

/-- `sectionAlgebraHomEquiv_restrict`, read on the underlying modules. -/
public theorem underlyingModuleMap_sectionAlgebraHomEquiv_restrict {S U : Scheme.{u}}
    (f : U ⟶ S) [IsAffineHom f] {G G' : Over S} (k : G' ⟶ G)
    (s : {s : G.left ⟶ U // s ≫ f = G.hom}) (s' : {s : G'.left ⟶ U // s ≫ f = G'.hom})
    (hs' : s'.1 = k.left ≫ s.1) :
    AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f G'.hom s') =
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f G.hom s) ≫
        AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap k) := by
  rw [sectionAlgebraHomEquiv_restrict f k s s' hs', underlyingModuleMap_comp_eq]

/-- Two sections of `f` over `G` whose algebra maps have the same underlying module map are
equal. -/
private theorem eq_of_underlyingModuleMap_sectionAlgebraHomEquiv_eq {S U G : Scheme.{u}}
    (f : U ⟶ S) [IsAffineHom f] (g : G ⟶ S) {s s' : {s : G ⟶ U // s ≫ f = g}}
    (h : AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f g s) =
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f g s')) : s = s' :=
  (sectionAlgebraHomEquiv f g).injective (eq_of_underlyingModuleMap_eq h)

/-! ### An open subscheme containing a closed subscheme -/

variable {S : Scheme.{u}}

/-- The factorisation of a morphism whose image lies in an open subscheme of the target through
the inclusion of that open subscheme. -/
public def liftOpenHom {T : Scheme.{u}} (W : S.Opens) (g : T ⟶ S)
    (hg : Set.range g.base ⊆ (W : Set S)) : T ⟶ W.toScheme :=
  IsOpenImmersion.lift W.ι g (by rw [Scheme.Opens.range_ι]; exact hg)

/-- `liftOpenHom` does factor the given morphism. -/
public theorem liftOpenHom_ι {T : Scheme.{u}} (W : S.Opens) (g : T ⟶ S)
    (hg : Set.range g.base ⊆ (W : Set S)) : liftOpenHom W g hg ≫ W.ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- Two morphisms into an open subscheme which agree after the inclusion of that open subscheme
are equal: the inclusion is a monomorphism. -/
private theorem hom_ext_opens {T : Scheme.{u}} (W : S.Opens) {a b : T ⟶ W.toScheme}
    (h : a ≫ W.ι = b ≫ W.ι) : a = b :=
  (cancel_mono W.ι).mp h

/-- Shrinking an open subscheme, as a morphism of `S`-schemes. -/
public def openInclusionOver {W W' : S.Opens} (h : W' ≤ W) :
    (Over.mk W'.ι : Over S) ⟶ Over.mk W.ι :=
  Over.homMk (S.homOfLE h) (Scheme.homOfLE_ι S h)

/-- **Restriction of a direct image algebra to a smaller open.** The map
`W.ι _* 𝒪_W ⟶ W'.ι _* 𝒪_{W'}` of sheaves of `𝒪_S`-algebras induced by `W' ≤ W`. -/
public def openRestrictionAlgebraMap {W W' : S.Opens} (h : W' ≤ W) :
    pushforwardAlgebra W.ι ⟶ pushforwardAlgebra W'.ι :=
  pushforwardAlgebraMap (X := (Over.mk W'.ι : Over S)) (Y := Over.mk W.ι) (openInclusionOver h)

/-- `openRestrictionAlgebraMap` read on the underlying modules, typed in the direct-image
spelling of the module underlying a direct image algebra. -/
public def openRestrictionUnitMap {W W' : S.Opens} (h : W' ≤ W) :
    (Scheme.Modules.pushforward W.ι).obj (SheafOfModules.unit W.toScheme.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward W'.ι).obj (SheafOfModules.unit W'.toScheme.ringCatSheaf) :=
  AlgebraSheaf.underlyingModuleMap (openRestrictionAlgebraMap h)

/-- `openRestrictionUnitMap` is `openRestrictionAlgebraMap` read on the underlying modules. The
algebra spelling is written on the left: both sides are closed terms, so this is where the
crossing between the two spellings is checked. -/
public theorem underlyingModuleMap_openRestrictionAlgebraMap {W W' : S.Opens} (h : W' ≤ W) :
    AlgebraSheaf.underlyingModuleMap (openRestrictionAlgebraMap h) = openRestrictionUnitMap h :=
  rfl

section Neighbourhood

variable {Y : Scheme.{u}} (c : Y ⟶ S) [IsClosedImmersion c] (W : S.Opens)

/-- An open subscheme containing the image of a closed immersion contains the image of each
infinitesimal neighbourhood of the closed subscheme, since the two images coincide. -/
public theorem range_nthOrderToBase_subset (hW : Set.range c.base ⊆ (W : Set S)) (n : ℕ) :
    Set.range (nthOrderToBase c n).base ⊆ (W : Set S) :=
  fun _ hx => hW ((range_nthInfinitesimalNeighbourhoodι c n).subset hx)

/-- The factorisation of the `n`-th infinitesimal neighbourhood of `Y` through an open subscheme
`W` containing the image of `c`. -/
public def nthOrderOpenHom (hW : Set.range c.base ⊆ (W : Set S)) (n : ℕ) :
    nthOrderInfinitesimalNeighbourhood c n ⟶ W.toScheme :=
  liftOpenHom W (nthOrderToBase c n) (range_nthOrderToBase_subset c W hW n)

/-- `nthOrderOpenHom` does factor the structure morphism of the neighbourhood. -/
public theorem nthOrderOpenHom_ι (hW : Set.range c.base ⊆ (W : Set S)) (n : ℕ) :
    nthOrderOpenHom c W hW n ≫ W.ι = nthOrderToBase c n :=
  liftOpenHom_ι W (nthOrderToBase c n) (range_nthOrderToBase_subset c W hW n)

/-- The `n`-th infinitesimal neighbourhood of `Y` in `S`, as a scheme over an open subscheme `W`
containing the image of `c`. -/
public def nthOrderOpenOver (hW : Set.range c.base ⊆ (W : Set S)) (n : ℕ) :
    nthInfinitesimalNeighbourhoodOver c n ⟶ (Over.mk W.ι : Over S) :=
  Over.homMk (nthOrderOpenHom c W hW n) (nthOrderOpenHom_ι c W hW n)

/-- The inclusion of `Y` into its `n`-th infinitesimal neighbourhood, followed by the
factorisation of that neighbourhood through `W`, is the factorisation of `c` itself through `W`.
Both composites with the inclusion of `W` are `c`, and that inclusion is a monomorphism. -/
public theorem nthOrderInclusion_comp_nthOrderOpenHom (hW : Set.range c.base ⊆ (W : Set S))
    (n : ℕ) {r : Y ⟶ W.toScheme} (hr : r ≫ W.ι = c) :
    nthOrderInclusion c n ≫ nthOrderOpenHom c W hW n = r :=
  hom_ext_opens W (by rw [Category.assoc, nthOrderOpenHom_ι, nthOrderInclusion_toBase, hr])

/-- **The canonical morphism of algebras from an open neighbourhood down to an infinitesimal
neighbourhood.** For an open `W` containing the image of `c`, the map
`W.ι _* 𝒪_W ⟶ (Y_n → S) _* 𝒪_{Y_n}` of sheaves of `𝒪_S`-algebras induced by the factorisation of
the `n`-th infinitesimal neighbourhood of `Y` through `W`. -/
public def nthOrderOpenAlgebraMap (hW : Set.range c.base ⊆ (W : Set S)) (n : ℕ) :
    pushforwardAlgebra W.ι ⟶ nthOrderAlgebra c n :=
  pushforwardAlgebraMap (X := nthInfinitesimalNeighbourhoodOver c n)
    (Y := (Over.mk W.ι : Over S)) (nthOrderOpenOver c W hW n)

/-- `nthOrderOpenAlgebraMap` read on the underlying modules, typed in the direct-image spelling
of the module underlying a direct image algebra. -/
public def nthOrderOpenUnitMap (hW : Set.range c.base ⊆ (W : Set S)) (n : ℕ) :
    (Scheme.Modules.pushforward W.ι).obj (SheafOfModules.unit W.toScheme.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward (nthOrderToBase c n)).obj
        (SheafOfModules.unit (nthOrderInfinitesimalNeighbourhood c n).ringCatSheaf) :=
  AlgebraSheaf.underlyingModuleMap (nthOrderOpenAlgebraMap c W hW n)

/-- `nthOrderOpenUnitMap` is `nthOrderOpenAlgebraMap` read on the underlying modules. The algebra
spelling is written on the left, for the reason given at
`underlyingModuleMap_openRestrictionAlgebraMap`. -/
public theorem underlyingModuleMap_nthOrderOpenAlgebraMap
    (hW : Set.range c.base ⊆ (W : Set S)) (n : ℕ) :
    AlgebraSheaf.underlyingModuleMap (nthOrderOpenAlgebraMap c W hW n) =
      nthOrderOpenUnitMap c W hW n :=
  rfl

end Neighbourhood

section Compatibility

variable {Y : Scheme.{u}} (c : Y ⟶ S) [IsClosedImmersion c]

/-- **Shrinking the open neighbourhood does not change the map down to an infinitesimal
neighbourhood.** The factorisations of `Y_n` through `W` and through a smaller `W'` differ by the
inclusion `W' ⊆ W`, since all three composites with the inclusion of `W` are the structure
morphism of `Y_n`. -/
private theorem nthOrderOpenOver_openInclusionOver {W W' : S.Opens}
    (hW : Set.range c.base ⊆ (W : Set S)) (hW' : Set.range c.base ⊆ (W' : Set S)) (h : W' ≤ W)
    (n : ℕ) :
    nthOrderOpenOver c W' hW' n ≫ openInclusionOver h = nthOrderOpenOver c W hW n :=
  Over.OverMorphism.ext (hom_ext_opens W
    ((Category.assoc _ _ _).trans
      (((congrArg (fun k => nthOrderOpenHom c W' hW' n ≫ k) (Scheme.homOfLE_ι S h)).trans
        (nthOrderOpenHom_ι c W' hW' n)).trans (nthOrderOpenHom_ι c W hW n).symm)))

/-- The map of algebras from an open neighbourhood down to an infinitesimal neighbourhood factors
through restriction to a smaller open neighbourhood. -/
public theorem openRestrictionAlgebraMap_comp_nthOrderOpenAlgebraMap {W W' : S.Opens}
    (hW : Set.range c.base ⊆ (W : Set S)) (hW' : Set.range c.base ⊆ (W' : Set S)) (h : W' ≤ W)
    (n : ℕ) :
    openRestrictionAlgebraMap h ≫ nthOrderOpenAlgebraMap c W' hW' n =
      nthOrderOpenAlgebraMap c W hW n :=
  show pushforwardAlgebraMap (X := (Over.mk W'.ι : Over S)) (Y := Over.mk W.ι)
          (openInclusionOver h) ≫
        pushforwardAlgebraMap (X := nthInfinitesimalNeighbourhoodOver c n)
          (Y := (Over.mk W'.ι : Over S)) (nthOrderOpenOver c W' hW' n) =
      pushforwardAlgebraMap (X := nthInfinitesimalNeighbourhoodOver c n)
        (Y := (Over.mk W.ι : Over S)) (nthOrderOpenOver c W hW n) from
  (pushforwardAlgebraMap_comp (nthOrderOpenOver c W' hW' n) (openInclusionOver h)).symm.trans
    (congrArg
      (fun k : nthInfinitesimalNeighbourhoodOver c n ⟶ (Over.mk W.ι : Over S) =>
        pushforwardAlgebraMap k)
      (nthOrderOpenOver_openInclusionOver c hW hW' h n))

/-- The map from an open neighbourhood down to an infinitesimal neighbourhood factors through
restriction to a smaller open neighbourhood, read on the underlying modules. -/
public theorem nthOrderOpenUnitMap_openRestriction {W W' : S.Opens}
    (hW : Set.range c.base ⊆ (W : Set S)) (hW' : Set.range c.base ⊆ (W' : Set S)) (h : W' ≤ W)
    (n : ℕ) :
    openRestrictionUnitMap h ≫ nthOrderOpenUnitMap c W' hW' n = nthOrderOpenUnitMap c W hW n :=
  show AlgebraSheaf.underlyingModuleMap (openRestrictionAlgebraMap h) ≫
        AlgebraSheaf.underlyingModuleMap (nthOrderOpenAlgebraMap c W' hW' n) =
      AlgebraSheaf.underlyingModuleMap (nthOrderOpenAlgebraMap c W hW n) from
  (underlyingModuleMap_comp_eq (openRestrictionAlgebraMap h)
      (nthOrderOpenAlgebraMap c W' hW' n)).symm.trans
    (congrArg AlgebraSheaf.underlyingModuleMap
      (openRestrictionAlgebraMap_comp_nthOrderOpenAlgebraMap c hW hW' h n))

/-- The inclusion of `Y` into the `n`-th infinitesimal neighbourhood, followed by the inclusion
of that neighbourhood into the `(n+1)`-st, is the inclusion of `Y` into the `(n+1)`-st: both
composites with the structure morphism of the `(n+1)`-st neighbourhood are `c`, and that
structure morphism is a monomorphism. This is the analogue, re-proved here, of the private
`nthOrderInclusion_transition` of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/RestrictionToClosedSubscheme.lean`. -/
public theorem nthOrderInclusion_comp_transition (n : ℕ) :
    nthOrderInclusion c n ≫
        (nthInfinitesimalNeighbourhoodTransition c (Nat.le_succ n)).left =
      nthOrderInclusion c (n + 1) := by
  have h1 : (nthOrderInclusion c n ≫
      (nthInfinitesimalNeighbourhoodTransition c (Nat.le_succ n)).left) ≫
      nthOrderToBase c (n + 1) = c :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => nthOrderInclusion c n ≫ k)
        (Over.w (nthInfinitesimalNeighbourhoodTransition c (Nat.le_succ n)))).trans
          (nthOrderInclusion_toBase c n))
  have _ : Mono (nthOrderToBase c (n + 1)) := inferInstance
  exact (cancel_mono (nthOrderToBase c (n + 1))).mp
    (h1.trans (nthOrderInclusion_toBase c (n + 1)).symm)

end Compatibility

/-! ### The two bridges -/

/-- **The lifting hypothesis of the two bridges, for a finite étale cover.** Sections of a finite
étale cover of `S` over the `n`-th infinitesimal neighbourhood of `Y` restrict bijectively to
sections over `Y`. This is `bijective_restrictSection_nthOrderInclusion`, a consequence of
[Stacks, Tag 0BQB], restated at the structure morphism of the cover: it is literally the `hrn`
argument of `exists_shrink_eq_of_restrict_eq` and `exists_section_on_open_of_bridge`, so it
records that the two bridges can be fed. -/
public theorem bijective_restrictSection_nthOrder_finiteEtale {Y : Scheme.{u}} (c : Y ⟶ S)
    [IsClosedImmersion c] (V : FiniteEtaleOver S) (n : ℕ) :
    Function.Bijective
      (fun t : {t : nthOrderInfinitesimalNeighbourhood c n ⟶ V.left //
          t ≫ V.hom = nthOrderToBase c n} =>
        (⟨nthOrderInclusion c n ≫ t.1, by
            rw [Category.assoc, t.2, nthOrderInclusion_toBase]⟩ :
          {t : Y ⟶ V.left // t ≫ V.hom = c})) :=
  bijective_restrictSection_nthOrderInclusion c V n

section Bridges

variable {Y U : Scheme.{u}} (c : Y ⟶ S) [IsClosedImmersion c] (f : U ⟶ S) [IsAffineHom f]

/-- The restriction of a section of `f` over an open neighbourhood `W` of `Y` to the `n`-th
infinitesimal neighbourhood of `Y`. -/
private def restrictToNthOrder (W : S.Opens) (hW : Set.range c.base ⊆ (W : Set S))
    (s : W.toScheme ⟶ U) (hs : s ≫ f = W.ι) (n : ℕ) :
    {t : nthOrderInfinitesimalNeighbourhood c n ⟶ U // t ≫ f = nthOrderToBase c n} :=
  ⟨nthOrderOpenHom c W hW n ≫ s, by rw [Category.assoc, hs, nthOrderOpenHom_ι]⟩

/-- The restriction of a section of `f` over an open neighbourhood to the `n`-th infinitesimal
neighbourhood, read as a morphism of modules out of the direct image algebra: it is composition
with `nthOrderOpenUnitMap`. -/
private theorem underlyingModuleMap_restrictToNthOrder (W : S.Opens)
    (hW : Set.range c.base ⊆ (W : Set S)) (s : W.toScheme ⟶ U) (hs : s ≫ f = W.ι) (n : ℕ) :
    AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f
        (nthInfinitesimalNeighbourhoodOver c n).hom (restrictToNthOrder c f W hW s hs n)) =
      AlgebraSheaf.underlyingModuleMap
          (sectionAlgebraHomEquiv f W.ι ⟨s, hs⟩) ≫
        nthOrderOpenUnitMap c W hW n :=
  show AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f
        (nthInfinitesimalNeighbourhoodOver c n).hom (restrictToNthOrder c f W hW s hs n)) =
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f W.ι ⟨s, hs⟩) ≫
        AlgebraSheaf.underlyingModuleMap (nthOrderOpenAlgebraMap c W hW n) from
  underlyingModuleMap_sectionAlgebraHomEquiv_restrict f (nthOrderOpenOver c W hW n) ⟨s, hs⟩
    (restrictToNthOrder c f W hW s hs n) rfl

omit [IsAffineHom f] in
/-- The restriction of a section of `f` over an open neighbourhood to the `n`-th infinitesimal
neighbourhood, then to `Y`, is its restriction to `Y`. -/
private theorem nthOrderInclusion_comp_restrictToNthOrder (W : S.Opens)
    (hW : Set.range c.base ⊆ (W : Set S)) (s : W.toScheme ⟶ U) (hs : s ≫ f = W.ι) (n : ℕ)
    {r : Y ⟶ W.toScheme} (hr : r ≫ W.ι = c) :
    nthOrderInclusion c n ≫ (restrictToNthOrder c f W hW s hs n).1 = r ≫ s :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ s) (nthOrderInclusion_comp_nthOrderOpenHom c W hW n hr))

omit [IsAffineHom f] in
/-- The restriction of a section of `f` over an open neighbourhood to a smaller one is a section
of `f`. -/
private theorem restrictToOpen_fac {W W' : S.Opens} (h : W' ≤ W) (s : W.toScheme ⟶ U)
    (hs : s ≫ f = W.ι) : (S.homOfLE h ≫ s) ≫ f = W'.ι :=
  by rw [Category.assoc, hs, Scheme.homOfLE_ι]

/-- The restriction of a section of `f` over an open neighbourhood `W` to a smaller open
neighbourhood `W'`, read as a morphism of modules out of the direct image algebra: it is
composition with `openRestrictionUnitMap`. -/
private theorem underlyingModuleMap_restrictToOpen {W W' : S.Opens} (h : W' ≤ W)
    (s : W.toScheme ⟶ U) (hs : s ≫ f = W.ι) :
    AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f W'.ι
        ⟨S.homOfLE h ≫ s, restrictToOpen_fac f h s hs⟩) =
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f W.ι ⟨s, hs⟩) ≫
        openRestrictionUnitMap h :=
  show AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f W'.ι
        ⟨S.homOfLE h ≫ s, restrictToOpen_fac f h s hs⟩) =
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f W.ι ⟨s, hs⟩) ≫
        AlgebraSheaf.underlyingModuleMap (openRestrictionAlgebraMap h) from
  underlyingModuleMap_sectionAlgebraHomEquiv_restrict f (openInclusionOver h) ⟨s, hs⟩
    ⟨S.homOfLE h ≫ s, restrictToOpen_fac f h s hs⟩ rfl

/-- **The uniqueness half of the shrinking section-extension statement.** Let `c : Y ⟶ S` be a
closed immersion and `f : U ⟶ S` affine. Let `s` and `s'` be sections of `f` over two open
subschemes `W`, `W'` of `S` containing the image of `c`, and suppose they induce the same section
of `f` over `Y`. Then they agree over some smaller open subscheme still containing the image of
`c`.

Two hypotheses are carried, each a general statement about general objects, quantified over them.

* `hrn` says that sections of `f` over the `n`-th infinitesimal neighbourhood of `Y` in `S`
  restrict bijectively to sections over `Y`. For `f` finite étale this is
  `Stacks.FundamentalGroup.bijective_restrictSection_nthOrderInclusion`, which is
  [Stacks, Tag 0BQB] for the thickening `Y ⊆ Y_n`. Only injectivity is used.
* `hshrink` is the hypothesis standing for faithfulness of completion over the colimit of the
  neighbourhoods: two morphisms of `𝒪_S`-modules out of an arbitrary module `M`, into the direct
  images of the structure sheaves of two open neighbourhoods of the image of `c`, whose
  composites with the canonical maps down to every infinitesimal neighbourhood of `Y` agree,
  agree already after restriction to some smaller open neighbourhood. It is supplied elsewhere
  from `Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete`.

The passage from sections to module maps is the universal property of the relative spectrum, read
on the one fixed base `S`: no module is restricted to an open subscheme. -/
public theorem exists_shrink_eq_of_restrict_eq
    (hrn : ∀ n : ℕ, Function.Bijective
      (fun t : {t : nthOrderInfinitesimalNeighbourhood c n ⟶ U //
          t ≫ f = nthOrderToBase c n} =>
        (⟨nthOrderInclusion c n ≫ t.1, by
            rw [Category.assoc, t.2, nthOrderInclusion_toBase]⟩ :
          {t : Y ⟶ U // t ≫ f = c})))
    (hshrink : ∀ (M : S.Modules) (W W' : S.Opens)
      (hW : Set.range c.base ⊆ (W : Set S)) (hW' : Set.range c.base ⊆ (W' : Set S))
      (φ : M ⟶ (Scheme.Modules.pushforward W.ι).obj
        (SheafOfModules.unit W.toScheme.ringCatSheaf))
      (φ' : M ⟶ (Scheme.Modules.pushforward W'.ι).obj
        (SheafOfModules.unit W'.toScheme.ringCatSheaf)),
      (∀ n : ℕ, φ ≫ nthOrderOpenUnitMap c W hW n = φ' ≫ nthOrderOpenUnitMap c W' hW' n) →
      ∃ (W'' : S.Opens) (h : W'' ≤ W) (h' : W'' ≤ W'),
        Set.range c.base ⊆ (W'' : Set S) ∧
          φ ≫ openRestrictionUnitMap h = φ' ≫ openRestrictionUnitMap h')
    (W W' : S.Opens) (hW : Set.range c.base ⊆ (W : Set S))
    (hW' : Set.range c.base ⊆ (W' : Set S))
    (s : W.toScheme ⟶ U) (hs : s ≫ f = W.ι) (s' : W'.toScheme ⟶ U) (hs' : s' ≫ f = W'.ι)
    (r : Y ⟶ W.toScheme) (hr : r ≫ W.ι = c) (r' : Y ⟶ W'.toScheme) (hr' : r' ≫ W'.ι = c)
    (hagree : r ≫ s = r' ≫ s') :
    ∃ (W'' : S.Opens) (h : W'' ≤ W) (h' : W'' ≤ W'),
      Set.range c.base ⊆ (W'' : Set S) ∧ S.homOfLE h ≫ s = S.homOfLE h' ≫ s' := by
  have hcomp : ∀ n : ℕ,
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f W.ι ⟨s, hs⟩) ≫
          nthOrderOpenUnitMap c W hW n =
        AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f W'.ι ⟨s', hs'⟩) ≫
          nthOrderOpenUnitMap c W' hW' n := by
    intro n
    have hsame : restrictToNthOrder c f W hW s hs n = restrictToNthOrder c f W' hW' s' hs' n :=
      (hrn n).1 (Subtype.ext
        (((nthOrderInclusion_comp_restrictToNthOrder c f W hW s hs n hr).trans hagree).trans
          (nthOrderInclusion_comp_restrictToNthOrder c f W' hW' s' hs' n hr').symm))
    refine ((underlyingModuleMap_restrictToNthOrder c f W hW s hs n).symm.trans ?_).trans
      (underlyingModuleMap_restrictToNthOrder c f W' hW' s' hs' n)
    exact congrArg (fun z => AlgebraSheaf.underlyingModuleMap
      (sectionAlgebraHomEquiv f (nthInfinitesimalNeighbourhoodOver c n).hom z)) hsame
  obtain ⟨W'', h, h', hW'', heq⟩ := hshrink
    (AlgebraSheaf.underlyingModule (pushforwardAlgebra f)) W W' hW hW'
    (AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f W.ι ⟨s, hs⟩))
    (AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f W'.ι ⟨s', hs'⟩)) hcomp
  refine ⟨W'', h, h', hW'', ?_⟩
  exact congrArg Subtype.val (eq_of_underlyingModuleMap_sectionAlgebraHomEquiv_eq f W''.ι
    (((underlyingModuleMap_restrictToOpen f h s hs).trans heq).trans
      (underlyingModuleMap_restrictToOpen f h' s' hs').symm))

omit [IsAffineHom f] in
/-- The chosen lift of a section over `Y` to the `(n+1)`-st infinitesimal neighbourhood restricts
to the chosen lift to the `n`-th: both restrict to the given section over `Y`, and sections over
the `n`-th neighbourhood are determined by their restriction to `Y`. -/
private theorem restrictSection_tower_step
    (hrn : ∀ n : ℕ, Function.Bijective
      (fun t : {t : nthOrderInfinitesimalNeighbourhood c n ⟶ U //
          t ≫ f = nthOrderToBase c n} =>
        (⟨nthOrderInclusion c n ≫ t.1, by
            rw [Category.assoc, t.2, nthOrderInclusion_toBase]⟩ :
          {t : Y ⟶ U // t ≫ f = c})))
    (t : {t : Y ⟶ U // t ≫ f = c})
    (tn : ∀ n : ℕ, {x : nthOrderInfinitesimalNeighbourhood c n ⟶ U //
      x ≫ f = nthOrderToBase c n})
    (htn : ∀ n : ℕ, (⟨nthOrderInclusion c n ≫ (tn n).1, by
        rw [Category.assoc, (tn n).2, nthOrderInclusion_toBase]⟩ :
      {t : Y ⟶ U // t ≫ f = c}) = t) (n : ℕ) :
    (tn n).1 =
      (nthInfinitesimalNeighbourhoodTransition c (Nat.le_succ n)).left ≫ (tn (n + 1)).1 := by
  have hmem : ((nthInfinitesimalNeighbourhoodTransition c (Nat.le_succ n)).left ≫
      (tn (n + 1)).1) ≫ f = nthOrderToBase c n :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => (nthInfinitesimalNeighbourhoodTransition c
          (Nat.le_succ n)).left ≫ z) (tn (n + 1)).2).trans
        (Over.w (nthInfinitesimalNeighbourhoodTransition c (Nat.le_succ n))))
  have hval : nthOrderInclusion c n ≫
      ((nthInfinitesimalNeighbourhoodTransition c (Nat.le_succ n)).left ≫
        (tn (n + 1)).1) = nthOrderInclusion c (n + 1) ≫ (tn (n + 1)).1 :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (tn (n + 1)).1) (nthOrderInclusion_comp_transition c n))
  have hx : (⟨(nthInfinitesimalNeighbourhoodTransition c (Nat.le_succ n)).left ≫
        (tn (n + 1)).1, hmem⟩ :
      {x : nthOrderInfinitesimalNeighbourhood c n ⟶ U // x ≫ f = nthOrderToBase c n}) = tn n :=
    (hrn n).1 ((Subtype.ext hval).trans ((htn (n + 1)).trans (htn n).symm))
  exact (congrArg Subtype.val hx).symm

/-- **The extension half of the shrinking section-extension statement.** Let `c : Y ⟶ S` be a
closed immersion and `f : U ⟶ S` affine. A section `t` of `f` over `Y` is the restriction of a
section of `f` over some open subscheme of `S` containing the image of `c`.

Three hypotheses are carried, each a general statement about general objects, quantified over
them.

* `hrn` says that sections of `f` over the `n`-th infinitesimal neighbourhood of `Y` in `S`
  restrict bijectively to sections over `Y`. For `f` finite étale this is
  `Stacks.FundamentalGroup.bijective_restrictSection_nthOrderInclusion`, which is
  [Stacks, Tag 0BQB] for the thickening `Y ⊆ Y_n`. It is what lifts `t` to each `Y_n`.
* `halg` is the hypothesis standing for fullness of completion over the colimit of the
  neighbourhoods: a compatible system of morphisms of `𝒪_S`-modules from an arbitrary module `M`
  into the direct images of the structure sheaves of the infinitesimal neighbourhoods of `Y` is
  the system of composites of a single morphism into the direct image of the structure sheaf of
  some open neighbourhood of the image of `c`.
* `hmul` is the multiplicativity criterion in the shape of
  `Stacks.RelativeSpec.AlgebraSheaf.exists_hom_of_jointlyInjective`: a morphism of the modules
  underlying `f _* 𝒪_U` and `W.ι _* 𝒪_W` which becomes a morphism of algebra sheaves after
  composition with each map down to an infinitesimal neighbourhood is itself a morphism of
  algebra sheaves. It is quantified over the open `W`, since which neighbourhood the
  algebraization lives on is produced by `halg`.

The two last hypotheses are supplied elsewhere, the first from
`Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete` and the second
from `exists_hom_of_jointlyInjective` together with the joint injectivity that the same
completion hypothesis gives. -/
public theorem exists_section_on_open_of_bridge
    (hrn : ∀ n : ℕ, Function.Bijective
      (fun t : {t : nthOrderInfinitesimalNeighbourhood c n ⟶ U //
          t ≫ f = nthOrderToBase c n} =>
        (⟨nthOrderInclusion c n ≫ t.1, by
            rw [Category.assoc, t.2, nthOrderInclusion_toBase]⟩ :
          {t : Y ⟶ U // t ≫ f = c})))
    (halg : ∀ (M : S.Modules)
      (α : ∀ n : ℕ, M ⟶ (Scheme.Modules.pushforward (nthOrderToBase c n)).obj
        (SheafOfModules.unit (nthOrderInfinitesimalNeighbourhood c n).ringCatSheaf)),
      (∀ n : ℕ, α (n + 1) ≫ nthOrderTransitionMap c n = α n) →
      ∃ (W : S.Opens) (hW : Set.range c.base ⊆ (W : Set S))
        (φ : M ⟶ (Scheme.Modules.pushforward W.ι).obj
          (SheafOfModules.unit W.toScheme.ringCatSheaf)),
        ∀ n : ℕ, φ ≫ nthOrderOpenUnitMap c W hW n = α n)
    (hmul : ∀ (W : S.Opens) (hW : Set.range c.base ⊆ (W : Set S))
      (φ : (Scheme.Modules.pushforward f).obj (SheafOfModules.unit U.ringCatSheaf) ⟶
        (Scheme.Modules.pushforward W.ι).obj (SheafOfModules.unit W.toScheme.ringCatSheaf)),
      (∀ n : ℕ, ∃ ψ : pushforwardAlgebra f ⟶ nthOrderAlgebra c n,
        AlgebraSheaf.underlyingModuleMap ψ = φ ≫ nthOrderOpenUnitMap c W hW n) →
      ∃ ψ : pushforwardAlgebra f ⟶ pushforwardAlgebra W.ι,
        AlgebraSheaf.underlyingModuleMap ψ = φ)
    (t : Y ⟶ U) (ht : t ≫ f = c) :
    ∃ (W : S.Opens) (_hW : Set.range c.base ⊆ (W : Set S)) (s : W.toScheme ⟶ U),
      s ≫ f = W.ι ∧ ∀ r : Y ⟶ W.toScheme, r ≫ W.ι = c → r ≫ s = t := by
  have hex : ∀ n : ℕ, ∃ x : {x : nthOrderInfinitesimalNeighbourhood c n ⟶ U //
      x ≫ f = nthOrderToBase c n},
      (⟨nthOrderInclusion c n ≫ x.1, by
        rw [Category.assoc, x.2, nthOrderInclusion_toBase]⟩ :
          {t : Y ⟶ U // t ≫ f = c}) = ⟨t, ht⟩ := fun n => (hrn n).2 ⟨t, ht⟩
  choose tn htn using hex
  have hcompat : ∀ n : ℕ,
      AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f
            (nthInfinitesimalNeighbourhoodOver c (n + 1)).hom (tn (n + 1))) ≫
          nthOrderTransitionMap c n =
        AlgebraSheaf.underlyingModuleMap (sectionAlgebraHomEquiv f
          (nthInfinitesimalNeighbourhoodOver c n).hom (tn n)) := fun n =>
    (underlyingModuleMap_sectionAlgebraHomEquiv_restrict f
      (nthInfinitesimalNeighbourhoodTransition c (Nat.le_succ n)) (tn (n + 1)) (tn n)
      (restrictSection_tower_step c f hrn ⟨t, ht⟩ tn htn n)).symm
  obtain ⟨W, hW, φ, hφ⟩ := halg (AlgebraSheaf.underlyingModule (pushforwardAlgebra f))
    (fun n => AlgebraSheaf.underlyingModuleMap
      (sectionAlgebraHomEquiv f (nthInfinitesimalNeighbourhoodOver c n).hom (tn n))) hcompat
  obtain ⟨ψ, hψ⟩ := hmul W hW φ fun n =>
    ⟨sectionAlgebraHomEquiv f (nthInfinitesimalNeighbourhoodOver c n).hom (tn n), (hφ n).symm⟩
  refine ⟨W, hW, ((sectionAlgebraHomEquiv f W.ι).symm ψ).1,
    ((sectionAlgebraHomEquiv f W.ι).symm ψ).2, fun r hr => ?_⟩
  have hsec : ((sectionAlgebraHomEquiv f W.ι).symm ψ).1 ≫ f = W.ι :=
    ((sectionAlgebraHomEquiv f W.ι).symm ψ).2
  have hψ' : sectionAlgebraHomEquiv f W.ι
      ((sectionAlgebraHomEquiv f W.ι).symm ψ) = ψ :=
    (sectionAlgebraHomEquiv f W.ι).apply_symm_apply ψ
  have hzero : restrictToNthOrder c f W hW _ hsec 0 = tn 0 :=
    eq_of_underlyingModuleMap_sectionAlgebraHomEquiv_eq f _
      ((underlyingModuleMap_restrictToNthOrder c f W hW _ hsec 0).trans
        (((congrArg (fun χ : pushforwardAlgebra f ⟶ pushforwardAlgebra W.ι =>
            AlgebraSheaf.underlyingModuleMap χ ≫ nthOrderOpenUnitMap c W hW 0) hψ').trans
          (congrArg (fun χ => χ ≫ nthOrderOpenUnitMap c W hW 0) hψ)).trans (hφ 0)))
  refine (nthOrderInclusion_comp_restrictToNthOrder c f W hW _ hsec 0 hr).symm.trans ?_
  exact (congrArg (fun z : {x : nthOrderInfinitesimalNeighbourhood c 0 ⟶ U //
      x ≫ f = nthOrderToBase c 0} => nthOrderInclusion c 0 ≫ z.1) hzero).trans
    (congrArg Subtype.val (htn 0))

end Bridges

end Stacks.FundamentalGroup

end
