module

public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.Group
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso

/-!
# The relative Picard functor of a morphism of algebraic spaces

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S`.  Every scheme `T` over `B`
gives a base change `X_T = X ×_B T`, again an algebraic space, and the invertible
`𝒪_{X_T}`-modules on its small étale site have a group of isomorphism classes `Pic(X_T)`
(Stacks 01CX).  Pulling an invertible module back along the transition map `X_U ⟶ X_T` of two
test schemes makes `T ↦ Pic(X_T)` a presheaf of sets on the schemes over `B`, and the *relative
Picard functor* `Pic_{X/B}` is its sheafification for the fppf topology.  This file constructs
the presheaf and the sheafification.

The Picard group of an algebraic space `Z` is `Stacks.SheafOfModules.PicardGroup` of the
structure sheaf of the small étale site of `Z`, so a Picard class is literally an isomorphism
class of
invertible `𝒪_Z`-modules and two invertible modules have the same class exactly when they are
isomorphic.  Pullback acts on classes because a functor carries isomorphic modules to isomorphic
modules; the two functor laws then say that the inverse image along an identity, and the inverse
image along a composite, change a module only up to isomorphism, which is what the comparisons
of Stacks 03LU supply.

## Main definitions

* `AlgebraicGeometry.Space.picardGroup`: `Pic(Z)` for an algebraic space `Z`, and
  `AlgebraicGeometry.Space.picardClass` the class of an invertible `𝒪_Z`-module.
* `AlgebraicGeometry.Space.ModulePullbackInvertible`: the assertion that the inverse image of an
  invertible module along a morphism of algebraic spaces is invertible.
* `AlgebraicGeometry.Space.picardPullback`: the induced map `Pic(V) → Pic(W)` of Picard groups.
* `AlgebraicGeometry.Space.PicardSituation`: **the standing data of Stacks 0D25**, a morphism
  `f : X ⟶ base` of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.PicardSituation.picardAt`: `Pic(X_T)` at a test scheme `T` over the
  base, and `AlgebraicGeometry.Space.PicardSituation.picardMap` the pullback of Picard classes
  along a morphism of test schemes.
* `AlgebraicGeometry.Space.PicardSituation.picardPresheaf`: **the presheaf `T ↦ Pic(X_T)`** on
  the schemes over the base.
* `AlgebraicGeometry.Space.PicardSituation.fppfTopology`: the fppf topology on the schemes over
  the base, induced from the big fppf topology.
* `AlgebraicGeometry.Space.PicardSituation.picardFunctor`: **Stacks 0D25**, the relative Picard
  functor `Pic_{X/B}`, the fppf sheafification of that presheaf, with
  `AlgebraicGeometry.Space.PicardSituation.toPicardFunctor` the canonical map into it.
* `AlgebraicGeometry.Space.ModulePushforwardUnitIso`: the assertion that the unit `N ⟶ g_*g^*N`
  of the adjunction of Stacks 03LU is an isomorphism at an invertible module when the structure
  map `𝒪_V ⟶ g_*𝒪_W` is one.
* `AlgebraicGeometry.Space.PicardSituation.basePicardAt` and
  `AlgebraicGeometry.Space.PicardSituation.structureSheafMap`: `Pic(T)` for a test scheme `T`
  over the base, and the structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the projection of the base
  change; `AlgebraicGeometry.Space.PicardSituation.StructureSheafMapIso` is **the hypothesis of
  Stacks 0D27**, that this map is an isomorphism for every `T`.
* `AlgebraicGeometry.Space.PicardSituation.basePicardPullback` and
  `AlgebraicGeometry.Space.PicardSituation.picardClassMap`: **the two arrows
  `Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T)` of the sequence of Stacks 0D27**.

## Main results

* `AlgebraicGeometry.Space.modulePullbackInvertible`: the inverse image of an invertible module
  along a morphism of algebraic spaces is invertible.  This is what makes the pullback of Picard
  classes exist.
* `AlgebraicGeometry.Space.picardPullback_picardClass`: pullback sends the class of `L` to the
  class of the inverse image of `L`.  This is what makes `picardPullback` the pullback of Picard
  classes rather than some other map.
* `AlgebraicGeometry.Space.exists_picardClass`: every element of `Pic(Z)` is the class of an
  invertible `𝒪_Z`-module, so the previous result determines `picardPullback` completely.
* `AlgebraicGeometry.Space.picardPullback_id` and
  `AlgebraicGeometry.Space.picardPullback_comp`: pullback of Picard classes along an identity is
  the identity, and along a composite is the composite of the pullbacks.  The second holds with
  no hypothesis.
* `AlgebraicGeometry.Space.PicardSituation.picardMap_id` and
  `AlgebraicGeometry.Space.PicardSituation.picardMap_comp`: the same two laws for the test
  schemes.  These are the well-definedness of the presheaf.
* `AlgebraicGeometry.Space.PicardSituation.isSheaf_picardFunctor`: the relative Picard functor is
  an fppf sheaf.
* `AlgebraicGeometry.Space.PicardSituation.injective_basePicardPullback`: **Stacks 0D27 at
  `Pic(T)`**, the first arrow of the sequence is injective.

## Implementation notes

**The invertibility of an inverse image is not a hypothesis.**  Without it there would be no map
`Pic(X_T) → Pic(X_U)` at all, and it is `AlgebraicGeometry.Space.ModulePullbackInvertible`; that
statement is proved here by `AlgebraicGeometry.Space.modulePullbackInvertible`, which reads
`AlgebraicGeometry.Space.isInvertible_modulePullback_obj` — the same assertion for the small
étale ringed topoi of two algebraic spaces — through the two spellings of invertibility compared
in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleCompare.lean`.  Nothing below takes
it as an argument.

**The pseudofunctoriality of the direct images is not a hypothesis.**  The identity law of the
presheaf needs `(𝟙 X_T)^* L ≅ L`, which is
`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackIdIso` of the
pseudofunctoriality data of Stacks 03LU, and that data is inhabited with no hypothesis by
`AlgebraicGeometry.Space.modulePushforwardCoherence`.  The presheaf and its sheafification
therefore take no coherence argument; the two pullback-of-classes laws
`AlgebraicGeometry.Space.picardPullback_id` and
`AlgebraicGeometry.Space.PicardSituation.picardMap_id` still accept the data as an explicit
argument, and the presheaf hands them that proved term.  The composition law needs nothing at
all, because
`AlgebraicGeometry.Space.modulePullbackCompIso` is unconditional and an isomorphism of modules is
already an equality of Picard classes.  No coherence *between* the comparisons is needed anywhere:
Picard classes are isomorphism classes, so only the existence of each comparison matters, not how
two of them compose.

**Why the two base-change laws are strict.**  `AlgebraicGeometry.Space.baseChangeMap_id` and
`AlgebraicGeometry.Space.baseChangeMap_comp` are equalities of morphisms of algebraic spaces,
being uniqueness statements for a fibre product, so the functor laws of the presheaf reduce to
the two statements about `picardPullback` at a *single* morphism and no transport along an
equality of test schemes appears.

**Universes.**  An invertible `𝒪_Z`-module is a `AlgebraicGeometry.Space.Modules.{u, u}`: the
tensor product of sheaves of modules, through which invertibility is defined, exists only when
the module sections share the universe of the structure sheaf, which on the small étale site is
the universe `u` of the schemes.  The objects of that site lie in `Type (u + 1)`, so `Pic(Z)` —
a type of isomorphism classes of such modules — lies in `Type (u + 1)`, and the presheaf takes
values there.  That is also the universe in which the schemes over the base form a category with
morphisms in `Type u`, so the size-matched sheafification of `Type`-valued presheaves applies to
the fppf topology on them with no appeal to essential smallness.

**The tag.**  Stacks 0D25 states that `Pic_{X/B}` *is* the fppf sheafification of `T ↦ Pic(X_T)`,
so both halves carry the tag: the presheaf being sheafified and the sheafification.  The source's
second reading of the same functor, on the schemes over `S` together with a map to the base, is
not formed here.

**What of Stacks 0D27 is here, and what is not.**  The sequence
`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/B}(T)` is written down, and exactness at `Pic(T)` — injectivity
of the first arrow — is proved.  The one input it carries is
`AlgebraicGeometry.Space.ModulePushforwardUnitIso`: the source argues that `N ⟶ f_*f^*N` is an
isomorphism because `N` is locally trivial, and an invertible module on a *general* site need not
be locally trivial — `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleBraidingSelf.lean`
records that, and the library has the converse only for a ringed space whose stalks are local
rings (`Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible`).  Deducing it on the
small étale site of an algebraic space from the étale base change of Stacks 03LX would need
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` to be the adjunction mate of the
inverse-image identification, which its own docstring records as not proved.

Exactness at `Pic(X_T)` is *not* proved.  Its two halves need, beyond the above, the descent
datum argument of Descent, Proposition 023T: a trivialising section of `L` over each `X_{T_i}`,
and the transition units in `Γ(X_{T_i ×_T T_j}, 𝒪^*)` that the structure-sheaf hypothesis
identifies with `Γ(T_i ×_T T_j, 𝒪^*)`.  There is no sheaf of units, and no group of global
units, of the structure sheaf of an algebraic space in this development, so that argument cannot
be stated at all; the fpqc descent of Stacks 023T itself *is* available unconditionally, for
schemes, as `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor'` and
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`.

## References

* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 0D27](https://stacks.math.columbia.edu/tag/0D27)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The Picard group of an algebraic space -/

/-- An `𝒪_Z`-module on the small étale site of an algebraic space `Z` is *invertible* when
tensoring by it is an equivalence of the category of `𝒪_Z`-modules, which is Stacks 01CS at the
structure sheaf of `Z`. -/
abbrev IsInvertibleModule (Z : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS Z.1 Z.2) :
    Prop :=
  Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS Z.1 Z.2).obj
    (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) L

/-- **Stacks 01CX for an algebraic space.**  The Picard group `Pic(Z)` of an algebraic space `Z`:
the abelian group of isomorphism classes of invertible `𝒪_Z`-modules on the small étale site of
`Z` under tensor product. -/
abbrev picardGroup (Z : AlgebraicSpaces B S hS) :=
  Stacks.SheafOfModules.PicardGroup (structureSheaf B S hS Z.1 Z.2).obj
    (structureRingPresheaf_isSheaf B S hS Z.1 Z.2)

/-- The category of invertible `𝒪_Z`-modules, whose isomorphism classes are the elements of
`Pic(Z)`. -/
abbrev InvertibleModules (Z : AlgebraicSpaces B S hS) :=
  Stacks.SheafOfModules.InvertibleModules (structureSheaf B S hS Z.1 Z.2).obj
    (structureRingPresheaf_isSheaf B S hS Z.1 Z.2)

/-- The class in `Pic(Z)` of an invertible `𝒪_Z`-module. -/
abbrev picardClass (Z : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS Z.1 Z.2)
    (hL : IsInvertibleModule Z L) : picardGroup Z :=
  Stacks.SheafOfModules.picardClass (structureSheaf B S hS Z.1 Z.2).obj
    (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) L hL

/-- Two invertible `𝒪_Z`-modules have the same class in `Pic(Z)` exactly when they are
isomorphic. -/
theorem picardClass_eq_picardClass_iff (Z : AlgebraicSpaces B S hS)
    (L N : Modules.{u, u} B S hS Z.1 Z.2) (hL : IsInvertibleModule Z L)
    (hN : IsInvertibleModule Z N) :
    picardClass Z L hL = picardClass Z N hN ↔ Nonempty (L ≅ N) :=
  Stacks.SheafOfModules.picardClass_eq_iff (structureSheaf B S hS Z.1 Z.2).obj
    (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) L N hL hN

/-- Every element of `Pic(Z)` is the class of an invertible `𝒪_Z`-module. -/
theorem exists_picardClass (Z : AlgebraicSpaces B S hS) (x : picardGroup Z) :
    ∃ (L : Modules.{u, u} B S hS Z.1 Z.2) (hL : IsInvertibleModule Z L),
      picardClass Z L hL = x :=
  Stacks.SheafOfModules.exists_picardClass_eq _ _ x

/-! ### Pullback of Picard classes -/

/-- **Stacks 0B8P for the small étale sites of algebraic spaces.**  The assertion that the
inverse image of an invertible `𝒪_V`-module along a morphism `W ⟶ V` of algebraic spaces is an
invertible `𝒪_W`-module.

It is proved by `AlgebraicGeometry.Space.modulePullbackInvertible`. -/
def ModulePullbackInvertible (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) (L : Modules.{u, u} B S hS V.1 V.2),
    IsInvertibleModule V L → IsInvertibleModule W ((modulePullback B S hS q).obj L)

/-- **The inverse image of an invertible module along a morphism of algebraic spaces is
invertible.**  This is `AlgebraicGeometry.Space.isInvertible_modulePullback_obj`, read through
the two spellings of invertibility of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleCompare.lean`. -/
@[stacks 0B8P "the inverse image of an invertible module along a morphism of algebraic spaces is
invertible"]
theorem modulePullbackInvertible : ModulePullbackInvertible B S hS := by
  intro V W q L hL
  exact Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (isInvertible_modulePullback_obj B S hS q L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL))

/-- The inverse image of an invertible `𝒪_V`-module along `q : W ⟶ V`, as an invertible
`𝒪_W`-module. -/
def picardPullbackObj {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) (L : InvertibleModules V) :
    InvertibleModules W :=
  ⟨(modulePullback B S hS q).obj L.obj, modulePullbackInvertible q L.obj L.property⟩

/-- The inverse image along `q : W ⟶ V` on isomorphism classes of invertible modules.  It is
well defined because a functor carries isomorphic modules to isomorphic modules. -/
def picardSkeletonPullback {V W : AlgebraicSpaces B S hS} (q : W ⟶ V)
    (a : Skeleton (InvertibleModules V)) : Skeleton (InvertibleModules W) :=
  toSkeleton (picardPullbackObj q ((fromSkeleton (InvertibleModules V)).obj a))

@[simp]
theorem picardSkeletonPullback_toSkeleton {V W : AlgebraicSpaces B S hS} (q : W ⟶ V)
    (L : InvertibleModules V) :
    picardSkeletonPullback q (toSkeleton L) = toSkeleton (picardPullbackObj q L) :=
  toSkeleton_eq_toSkeleton_iff.2 ⟨ObjectProperty.isoMk _
    ((modulePullback B S hS q).mapIso
      ((ObjectProperty.ι _).mapIso (fromSkeletonToSkeletonIso L)))⟩

/-- **The pullback of Picard classes along a morphism `q : W ⟶ V` of algebraic spaces**: the map
`Pic(V) → Pic(W)` sending the class of an invertible `𝒪_V`-module to the class of its inverse
image. -/
def picardPullback {V W : AlgebraicSpaces B S hS} (q : W ⟶ V) (x : picardGroup V) :
    picardGroup W :=
  (Stacks.Picard.picardGroupData (structureSheaf B S hS W.1 W.2).obj
      (structureRingPresheaf_isSheaf B S hS W.1 W.2)).classEquiv
    (picardSkeletonPullback q
      ((Stacks.Picard.picardGroupData (structureSheaf B S hS V.1 V.2).obj
        (structureRingPresheaf_isSheaf B S hS V.1 V.2)).classEquiv.symm x))

/-- **Pullback of Picard classes sends the class of `L` to the class of the inverse image of
`L`.** -/
theorem picardPullback_picardClass {V W : AlgebraicSpaces B S hS} (q : W ⟶ V)
    (L : Modules.{u, u} B S hS V.1 V.2) (hL : IsInvertibleModule V L) :
    picardPullback q (picardClass V L hL) =
      picardClass W ((modulePullback B S hS q).obj L) (modulePullbackInvertible q L hL) := by
  exact congrArg Additive.ofMul (picardSkeletonPullback_toSkeleton q ⟨L, hL⟩)

/-- **Pullback of Picard classes along an identity is the identity.**  This is the unit law of
Stacks 03LU for the inverse image, read on isomorphism classes. -/
theorem picardPullback_id (hc : ModulePushforwardCoherence B S hS)
    (Z : AlgebraicSpaces B S hS) (x : picardGroup Z) :
    picardPullback (𝟙 Z) x = x := by
  obtain ⟨L, hL, rfl⟩ := exists_picardClass Z x
  rw [picardPullback_picardClass]
  exact (picardClass_eq_picardClass_iff Z _ _ _ _).2 ⟨(hc.modulePullbackIdIso Z).app L⟩

/-- **Pullback of Picard classes along a composite is the composite of the pullbacks.**  This is
the comparison `r^* ∘ q^*`-style law of Stacks 03LU, read on isomorphism classes; it needs no
coherence, only the existence of the comparison. -/
theorem picardPullback_comp {V₁ V₂ V₃ : AlgebraicSpaces B S hS} (q : V₁ ⟶ V₂) (r : V₂ ⟶ V₃)
    (x : picardGroup V₃) :
    picardPullback (q ≫ r) x = picardPullback q (picardPullback r x) := by
  obtain ⟨L, hL, rfl⟩ := exists_picardClass V₃ x
  simp only [picardPullback_picardClass]
  exact (picardClass_eq_picardClass_iff V₁ _ _ _ _).2
    ⟨((modulePullbackCompIso B S hS q r).app L).symm⟩

/-- **The unit of the adjunction of Stacks 03LU is an isomorphism at an invertible module.**  The
assertion that for a morphism `g : W ⟶ V` of algebraic spaces whose structure map
`𝒪_V ⟶ g_*𝒪_W` is an isomorphism, the canonical map `N ⟶ g_*g^*N` is an isomorphism for every
invertible `𝒪_V`-module `N`.

It is the first paragraph of the proof of Stacks 0D27 read on modules, and it is not proved in
this development; see the implementation notes. -/
def ModulePushforwardUnitIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ {V W : AlgebraicSpaces B S hS} (g : W ⟶ V), IsIso (structureSharp B S hS g) →
    ∀ N : Modules.{u, u} B S hS V.1 V.2, IsInvertibleModule V N →
      IsIso ((modulePullbackAdjunction B S hS g).unit.app N)

/-! ### The relative Picard functor -/

/-- **Stacks 0D25.**  The standing data of the relative Picard functor: a morphism
`f : X ⟶ base` of algebraic spaces over the scheme `S`. -/
@[stacks 0D25 "the standing data"]
structure PicardSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The algebraic space whose invertible modules are classified. -/
  X : AlgebraicSpaces B S hS
  /-- The algebraic space over which the test schemes live. -/
  base : AlgebraicSpaces B S hS
  /-- The morphism of algebraic spaces being base changed along. -/
  f : X ⟶ base

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-- The test schemes over the base of the situation: the schemes of the big fppf site of `S`,
regarded as algebraic spaces, equipped with a morphism to the base. -/
abbrev SchemesOver := _root_.AlgebraicGeometry.Space.SchemesOver s.base

/-- The base change `X_T = X ×_base T` along a test scheme. -/
abbrev baseChange (T : s.SchemesOver) : AlgebraicSpaces B S hS :=
  baseChangeSpace s.f T

/-- **Stacks 0D25.**  The value `Pic(X_T)` of the presheaf being sheafified: the group of
isomorphism classes of invertible `𝒪_{X_T}`-modules. -/
abbrev picardAt (T : s.SchemesOver) := picardGroup (s.baseChange T)

/-- **Stacks 0D25.**  The pullback of a Picard class of `X_T` along a morphism `U ⟶ T` of test
schemes: its inverse image along the transition map `X_U ⟶ X_T`. -/
def picardMap {U T : s.SchemesOver} (g : U ⟶ T) (x : s.picardAt T) : s.picardAt U :=
  picardPullback (baseChangeMap s.f g) x

/-- Pullback of Picard classes along a morphism of test schemes is pullback along the transition
map of the two base changes. -/
theorem picardMap_eq {U T : s.SchemesOver} (g : U ⟶ T) :
    s.picardMap g = picardPullback (baseChangeMap s.f g) :=
  rfl

/-- **Pullback of Picard classes along the identity of a test scheme is the identity.** -/
theorem picardMap_id (hc : ModulePushforwardCoherence B S hS) (T : s.SchemesOver)
    (x : s.picardAt T) : s.picardMap (𝟙 T) x = x := by
  rw [picardMap_eq, baseChangeMap_id]
  exact picardPullback_id hc _ x

/-- **Pullback of Picard classes is compatible with composition of morphisms of test
schemes.** -/
theorem picardMap_comp {V U T : s.SchemesOver} (g : V ⟶ U) (h : U ⟶ T) (x : s.picardAt T) :
    s.picardMap (g ≫ h) x = s.picardMap g (s.picardMap h x) := by
  rw [picardMap_eq, baseChangeMap_comp, picardPullback_comp]
  rfl

/-- **Stacks 0D25.**  The presheaf `T ↦ Pic(X_T)` on the schemes over the base, whose fppf
sheafification is the relative Picard functor.  Its action on a morphism of test schemes is
pullback of Picard classes. -/
@[stacks 0D25 "the presheaf of Picard groups of the base changes"]
def picardPresheaf : (s.SchemesOver)ᵒᵖ ⥤ Type (u + 1) where
  obj T := s.picardAt T.unop
  map g := TypeCat.ofHom (s.picardMap g.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro x
    exact s.picardMap_id (modulePushforwardCoherence B S hS) T.unop x
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    exact s.picardMap_comp h.unop g.unop x

/-- The value of the presheaf at a test scheme is the Picard group of the base change. -/
theorem picardPresheaf_obj (T : s.SchemesOver) :
    s.picardPresheaf.obj (Opposite.op T) = s.picardAt T :=
  rfl

/-- The action of the presheaf on a morphism of test schemes is pullback of Picard classes. -/
theorem picardPresheaf_map {U T : s.SchemesOver} (g : U ⟶ T) :
    s.picardPresheaf.map (Opposite.op g) = TypeCat.ofHom (s.picardMap g) :=
  rfl

/-- The fppf topology on the schemes over the base: a family of test schemes covers when the
underlying family of schemes of the big fppf site does. -/
abbrev fppfTopology : GrothendieckTopology s.SchemesOver :=
  (CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base).restrictedTopology
    (BigFppfOver.topology B S hS)

/-- **Stacks 0D25.**  The *relative Picard functor* `Pic_{X/base} : (Sch/base)ᵒᵖ ⥤ Sets`: the
fppf sheafification of the presheaf `T ↦ Pic(X_T)` of isomorphism classes of invertible modules
on the base changes. -/
@[stacks 0D25 "the relative Picard functor",
  sga "6 X 2.4" "definition of Pic_{X/B}",
  sga "6 XIII 3.1"]
def picardFunctor : (s.SchemesOver)ᵒᵖ ⥤ Type (u + 1) :=
  sheafify s.fppfTopology s.picardPresheaf

/-- The canonical map from the presheaf of Picard groups of the base changes to the relative
Picard functor: the unit of the sheafification. -/
def toPicardFunctor : s.picardPresheaf ⟶ s.picardFunctor :=
  toSheafify s.fppfTopology s.picardPresheaf

/-- **The relative Picard functor is an fppf sheaf.** -/
theorem isSheaf_picardFunctor :
    Presheaf.IsSheaf s.fppfTopology s.picardFunctor :=
  ((presheafToSheaf s.fppfTopology (Type (u + 1))).obj s.picardPresheaf).property

/-! ### The sequence of Stacks 0D27 -/

/-- A test scheme over the base, regarded as an algebraic space. -/
abbrev baseSpaceAt (T : s.SchemesOver) : AlgebraicSpaces B S hS :=
  (schemeSpaceFunctor B S hS).obj T.left

/-- `Pic(T)`, the group of isomorphism classes of invertible modules on the small étale site of
a test scheme over the base. -/
abbrev basePicardAt (T : s.SchemesOver) := picardGroup (s.baseSpaceAt T)

/-- The structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the projection `f_T : X_T ⟶ T` of the base
change to a test scheme, a morphism of sheaves of rings on the small étale site of `T`. -/
abbrev structureSheafMap (T : s.SchemesOver) :=
  structureSharp B S hS (baseChangeInclusion s.f T)

/-- **The hypothesis of Stacks 0D27**: the structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an
isomorphism for every scheme `T` over the base. -/
def StructureSheafMapIso : Prop := ∀ T : s.SchemesOver, IsIso (s.structureSheafMap T)

/-- **The first arrow `Pic(T) ⟶ Pic(X_T)` of the sequence of Stacks 0D27**: pullback of Picard
classes along the projection `f_T : X_T ⟶ T` of the base change. -/
def basePicardPullback (T : s.SchemesOver) (x : s.basePicardAt T) : s.picardAt T :=
  picardPullback (baseChangeInclusion s.f T) x

/-- The first arrow sends the class of an invertible `𝒪_T`-module to the class of its inverse
image along `f_T`. -/
theorem basePicardPullback_picardClass (T : s.SchemesOver)
    (N : Modules.{u, u} B S hS (s.baseSpaceAt T).1 (s.baseSpaceAt T).2)
    (hN : IsInvertibleModule (s.baseSpaceAt T) N) :
    s.basePicardPullback T (picardClass _ N hN) =
      picardClass _ ((modulePullback B S hS (baseChangeInclusion s.f T)).obj N)
        (modulePullbackInvertible _ N hN) :=
  picardPullback_picardClass _ N hN

/-- **The second arrow `Pic(X_T) ⟶ Pic_{X/B}(T)` of the sequence of Stacks 0D27**: the component
at `T` of the canonical map from the presheaf of Picard groups to its fppf sheafification. -/
def picardClassMap (T : s.SchemesOver) (x : s.picardAt T) :
    s.picardFunctor.obj (Opposite.op T) :=
  s.toPicardFunctor.app (Opposite.op T) x

/-- **Stacks 0D27, exactness at `Pic(T)`.**  If `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for
every scheme `T` over the base, then pullback along `f_T` is an injection `Pic(T) ⟶ Pic(X_T)`:
an invertible `𝒪_T`-module is determined up to isomorphism by its inverse image on `X_T`. -/
@[stacks 0D27 "exactness at the Picard group of the test scheme, conditional on the unit of \
the Stacks 03LU adjunction being an isomorphism at an invertible module"]
theorem injective_basePicardPullback (hu : ModulePushforwardUnitIso B S hS)
    (h : s.StructureSheafMapIso) (T : s.SchemesOver) :
    Function.Injective (s.basePicardPullback T) := by
  intro x y hxy
  obtain ⟨N, hN, rfl⟩ := exists_picardClass (s.baseSpaceAt T) x
  obtain ⟨N', hN', rfl⟩ := exists_picardClass (s.baseSpaceAt T) y
  simp only [basePicardPullback, picardPullback_picardClass] at hxy
  obtain ⟨e⟩ := (picardClass_eq_picardClass_iff _ _ _ _ _).1 hxy
  refine (picardClass_eq_picardClass_iff _ _ _ _ _).2 ⟨?_⟩
  have := hu (baseChangeInclusion s.f T) (h T) N hN
  have := hu (baseChangeInclusion s.f T) (h T) N' hN'
  exact asIso ((modulePullbackAdjunction B S hS (baseChangeInclusion s.f T)).unit.app N) ≪≫
    (modulePushforward B S hS (baseChangeInclusion s.f T)).mapIso e ≪≫
      (asIso ((modulePullbackAdjunction B S hS (baseChangeInclusion s.f T)).unit.app N')).symm

end PicardSituation

end AlgebraicGeometry.Space

end

