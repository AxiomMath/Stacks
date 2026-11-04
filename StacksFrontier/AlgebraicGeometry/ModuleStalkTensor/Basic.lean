module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleSkyscraper.PullbackStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison morphism of the quasi-coherence clause of Stacks Tag 01SA

Let `g : T ⟶ S` be a morphism of schemes and `A` a sheaf of commutative `𝒪_S`-algebras.  The
`algebraPullback_isQuasicoherent` clause of Stacks Tag 01SA asserts that
`Stacks.AffineAlgebraEquivalence.algebraPullback` carries a quasi-coherent algebra to a
quasi-coherent one.  By construction that pullback is the pushout
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` of sheaves of commutative rings, so the clause is a statement about the
underlying sheaf of `𝒪_T`-modules of a pushout, and the way to it is to compare that module
with the inverse image `g^*` of the underlying `𝒪_S`-module of `A`, whose quasi-coherence is
`Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback` (Tag 01BG).

**This file builds that comparison morphism and reduces the clause to its invertibility.**  It
does not prove the clause: `isQuasicoherent_of_isIso_comparison` takes invertibility as a
hypothesis.  Nothing beyond the data of the statement is assumed — `g`, `S`, `T` and `A` are
arbitrary, with no affineness, Noetherian, finiteness or flatness hypothesis anywhere.

## Main definitions

* `Stacks.ModuleStalkTensor.adjointAlgebraMap`: the adjoint transpose `A ⟶ g_*(g⁻¹A ⊗ 𝒪_T)` of
  `Stacks.AffineAlgebraEquivalence.algebraPullbackMap`, as sheaves of commutative rings, with
  `adjointRingMap` its reading as a morphism of sheaves of not necessarily commutative rings.
* `Stacks.ModuleStalkTensor.comparisonPushforward`: the induced morphism of underlying
  `𝒪_S`-modules into the direct image, `A ⟶ g_*(g⁻¹A ⊗ 𝒪_T)`.
* `Stacks.ModuleStalkTensor.comparison`: its adjoint transpose
  `g^*A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`, **the comparison morphism whose invertibility the clause
  asserts**.

## Main results

* `Stacks.ModuleStalkTensor.homEquiv_sq`: transposing a commuting square across an adjunction.
* `Stacks.ModuleStalkTensor.adjointAlgebraMap_structure` and `adjointRingMap_structure`: the
  adjoint transpose is a morphism of algebras, i.e. it carries the structure morphism of `A` to
  the structure morphism of the pullback precomposed with `g.c`.  This is the one piece of real
  content below: it is the pushout square of
  `Stacks.AffineAlgebraEquivalence.algebraPullback_isPushout` transposed across the
  inverse-image/direct-image adjunction on sheaves of commutative rings.
* `Stacks.ModuleStalkTensor.restrictScalars_pushforward_obj` and
  `pushforward_restrictScalars_obj`: restriction of scalars and direct image of sheaves of
  modules commute with each other in the two ways needed, **on the nose**.
* `Stacks.ModuleStalkTensor.isQuasicoherent_of_isIso_comparison`: **the reduction.** If
  `comparison` is invertible then the pullback algebra is quasi-coherent.  So the clause is now
  exactly one invertibility statement.
* `Stacks.ModuleStalkTensor.stalkPullbackModulesIso`: the stalk of the inverse image of a sheaf
  of modules on a scheme, `(g^*M)_t ≅ L(M_{g t})` for `L` left adjoint to restriction of
  scalars along the stalk map — `L = ModuleCat.extendScalars` whenever the stalk rings are
  available as commutative rings, so `(g^*M)_t ≅ M_{g t} ⊗_{𝒪_{S,g t}} 𝒪_{T,t}`.

## Route

`Stacks.AffineAlgebraEquivalence.algebraPullbackMap` is a morphism of sheaves of commutative
rings `g⁻¹A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`, and the only way out of an inverse image is the
adjunction, so the comparison is built by transposing twice: once on sheaves of commutative
rings, to get a morphism of algebras `A ⟶ g_*(g⁻¹A ⊗ 𝒪_T)`, and then back on sheaves of
modules, after that algebra morphism has been turned into a morphism of underlying modules.

The middle step is where a bridge was expected and none is needed.  The underlying module of an
algebra sheaf is its sheaf of rings viewed over itself and restricted along the structure
morphism, so a morphism of algebras `A ⟶ g_*B` gives a morphism of modules by Mathlib's
`SheafOfModules.unitToPushforwardObjUnit` followed by `SheafOfModules.restrictScalars`.  What
that produces is restriction of scalars *outside* a direct image, where the target of
`comparisonPushforward` has the direct image outside; and the two agree definitionally, because
both scalar actions are given by composites of ring maps that `adjointRingMap_structure` shows
to be equal.  `restrictScalars_pushforward_obj` and `pushforward_restrictScalars_obj` are those
two definitional identifications, and `SheafOfModules.pushforwardCongr` transports along the
equality of ring maps between them.

## Why no filtered-colimit computation appears

A stalk is a filtered colimit, so computing the stalk of an inverse image of modules by
unwinding the construction would need a tensor product to commute with a filtered colimit
*along which the base ring also varies*.  That statement is genuinely absent from Mathlib at
this pin — checked by reading the module docstring of every file under `Mathlib/Algebra/Colimit/`,
by searching for `DirectLimit` together with `TensorProduct` in either order across all of
Mathlib, by searching for a tensor sign whose base-ring argument is a colimit, by inspecting
`Mathlib/LinearAlgebra/TensorProduct/DirectLimit.lean`,
`Mathlib/RingTheory/TensorProduct/DirectLimitFG.lean`,
`Mathlib/Algebra/Category/ModuleCat/{Colimits,FilteredColimits}.lean`,
`Mathlib/Algebra/Category/Ring/FilteredColimits.lean`,
`Mathlib/Algebra/Category/ModuleCat/Presheaf/ColimitFunctor.lean` and
`Mathlib/CategoryTheory/Monoidal/Limits/Colimits.lean`, and by semantic search on four
phrasings.  What exists is the fixed-base statement only, in two forms:
`TensorProduct.directLimitLeft`/`directLimitRight` and `CategoryTheory.Limits.IsColimit.tensor`.
The varying-base *module structure* does exist — `CategoryTheory.Limits.IsColimit.module` and
`PresheafOfModules.ModuleColimit` — but `PresheafOfModules.colimitFunctor` is nowhere shown to
be monoidal, which is the same gap phrased categorically.

**It is not needed.**  `Stacks.ModuleSkyscraper.pullbackStalkIsoOfAdjunction` computes the
stalk of the
inverse image of a sheaf of modules directly, by conjugating the comparison of module
skyscrapers under two composite adjunctions, with no colimit computed anywhere; and
`AlgebraicGeometry.Scheme.Modules.pullback g` *is*
`SheafOfModules.pullback g.toRingCatSheafHom`, so it applies verbatim.
`stalkPullbackModulesIso` records that instance.

## Transparency gotchas

* `adjointAlgebraMap_structure` must not be proved by rewriting with `adjointAlgebraMap`.
  Unfolding it leaves a goal that is not type-correct at implicit transparency, because
  `Stacks.AffineAlgebraEquivalence.algebraPullbackMap` is a natural transformation between
  composites of `Under.post` and `Under.forget` and its component is not syntactically a
  morphism out of `(TopCat.Sheaf.pullback _ g.base).obj A.right`.  The repair is to do the
  adjunction algebra in a separate general lemma, `homEquiv_sq`, and apply it with `exact`,
  which checks definitional equality at default transparency.
* The direct image of sheaves of rings must be written
  `(Opens.map g.base).sheafPushforwardContinuous _ _ _`, the spelling
  `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` uses, and the topologies must be left to be
  inferred.  Writing the functor's type out with the carrier spelled `S.toTopCat` produces
  `Opens.grothendieckTopology ↑S.toTopCat` where the scheme-level definitions produce
  `Opens.grothendieckTopology ↥S`; the two are definitionally equal, and instance search is
  syntactic, so `Functor.IsContinuous` is then not found.
* `AlgebraicGeometry.Scheme.Modules` is a `def` with its own `Category` instance, so in
  `isQuasicoherent_of_isIso_comparison` the invertibility of `comparison` is taken as an
  explicit hypothesis and handed to `CategoryTheory.asIso` positionally.  As an instance
  argument it is not found, because instance search looks for `IsIso` in the `SheafOfModules`
  category rather than in the wrapper.

## What is not done

**No clause of [Stacks, Tag 01SA] is proved here, and no project tag attribute is attached.**
The statement of Tag 01SA is a nine-field structure with a single unqualified tag; fields 4, 8 and 9 are
open, and the types of the last two take field 4 as an argument.

The `algebraPullback_isQuasicoherent` clause is now exactly `IsIso (comparison g A)`.  By
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk` that is a question about
stalks, and both stalks are known: the source by `stalkPullbackModulesIso` above, the target by
`Stacks.AffineAlgebraEquivalence.stalkAlgebraPullbackIso` together with
`Stacks.SkyscraperPushforward.stalkInverseImageNatIso`.  Three things are missing, none of them
started here:

* the two descriptions use different stalk rings.  `stalkPullbackModulesIso` tensors over the
  stalk of the structure sheaf taken in `RingCat`, since `SheafOfModules` is over `RingCat`,
  while `stalkAlgebraPullbackIso` tensors over the stalk taken in `CommRingCat`.  The carriers
  are not equal by `rfl`, the two colimits being built in two different categories.  What
  identifies them is `forget₂ CommRingCat RingCat` preserving filtered colimits, through
  `CategoryTheory.Limits.preservesColimitIso`, together with the transport of a tensor product
  of stalks along that isomorphism;
* the compatibility of `Stacks.SheafifyStalk.stalkInverseImageIso` with the algebra structures,
  i.e. that under it the stalk of
  `Stacks.AffineAlgebraEquivalence.inverseImageStructureMap` becomes
  `AlgebraicGeometry.Scheme.Hom.stalkMap`.  Its presheaf-level half is exactly
  `Stacks.SkyscraperPushforward.stalkPullbackHom_stalkMap`; the sheaf-level statement needs the
  sheaf adjunction's unit related to the presheaf one through sheafification;
* the identification of the effect of `comparison` on stalks with the composite of those
  isomorphisms.  This is the analogue, for the clause of Tag 01SA, of what
  `Stacks.PullbackTensorIso.tensorStalkIso_germ_comparison` is for Tag 01CD, and it is the one
  remaining step that is not bookkeeping.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.ModuleStalkTensor

open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

/-! ### Transposing a square across an adjunction -/

section Generic

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- **Transposing a commuting square across an adjunction.**  If `F.map a ≫ p = i ≫ q` then the
adjoint transposes satisfy `a ≫ adj.homEquiv p = adj.homEquiv i ≫ G.map q`.

Stated separately rather than inlined because the adjunction algebra is then carried out at a
spelling where the rewrites fire; at the spelling the clause of Stacks Tag 01SA produces, the
unfolded goal is not type-correct at the transparency a rewrite builds its motive at. -/
public theorem homEquiv_sq {X X' : C} {W Z : D} (a : X ⟶ X') (p : F.obj X' ⟶ Z)
    (i : F.obj X ⟶ W) (q : W ⟶ Z) (h : F.map a ≫ p = i ≫ q) :
    a ≫ adj.homEquiv X' Z p = adj.homEquiv X W i ≫ G.map q := by
  rw [adj.homEquiv_unit, adj.homEquiv_unit, ← Category.assoc, ← adj.unit_naturality a]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [h]

end Generic

/-! ### Restriction of scalars and direct image of sheaves of modules commute -/

section Commutation

variable {C₁ : Type u} [Category.{u} C₁] {C₂ : Type u} [Category.{u} C₂]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂} {F : C₁ ⥤ C₂}
  [F.IsContinuous J₁ J₂] {R R' : Sheaf J₁ RingCat.{u}} {Q Q' : Sheaf J₂ RingCat.{u}}

/-- **Restricting scalars after a direct image is the direct image along the composite.**  Both
sides are the same sections with the same action, the scalars acting through `α` and then `δ`
either way. -/
public theorem restrictScalars_pushforward_obj (α : R ⟶ R')
    (δ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{u} J₁ J₂).obj Q)
    (M : SheafOfModules.{u} Q) :
    (SheafOfModules.restrictScalars α).obj ((SheafOfModules.pushforward δ).obj M) =
      (SheafOfModules.pushforward (α ≫ δ)).obj M :=
  rfl

/-- **A direct image along a composite whose second factor is itself a direct image is a direct
image followed by restriction of scalars.**  This is the identification the comparison morphism
of the quasi-coherence clause of Stacks Tag 01SA was expected to need a bridge for; it holds on
the nose. -/
public theorem pushforward_restrictScalars_obj
    (γ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J₁ J₂).obj Q) (β : Q ⟶ Q')
    (M : SheafOfModules.{u} Q') :
    (SheafOfModules.pushforward
        (γ ≫ (F.sheafPushforwardContinuous RingCat.{u} J₁ J₂).map β)).obj M =
      (SheafOfModules.pushforward γ).obj ((SheafOfModules.restrictScalars β).obj M) :=
  rfl

end Commutation

/-! ### The adjoint transpose of the algebra-pullback map -/

variable {T S : Scheme.{u}} (g : T ⟶ S) (A : AlgebraSheaf S)

/-- The adjoint transpose `A ⟶ g_*(g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T)` of
`Stacks.AffineAlgebraEquivalence.algebraPullbackMap`, as sheaves of commutative rings. -/
public def adjointAlgebraMap :
    A.right ⟶ (TopCat.Sheaf.pushforward CommRingCat g.base).obj
      ((algebraPullback g).obj A).right :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv _ _)
    ((algebraPullbackMap g).app A)

/-- **The adjoint transpose is a morphism of algebras.**  Composing the structure morphism of
`A` with it gives the structure morphism of the pullback algebra, pushed forward and precomposed
with the comorphism of `g`.

This is the pushout square of `Stacks.AffineAlgebraEquivalence.algebraPullback_isPushout`
transposed across the inverse-image/direct-image adjunction, by `homEquiv_sq`; the second edge
of that square is `Stacks.AffineAlgebraEquivalence.inverseImageStructureMap`, whose transpose is
the comorphism of `g` by construction. -/
public theorem adjointAlgebraMap_structure :
    A.hom ≫ adjointAlgebraMap g A =
      (⟨g.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat g.base).obj T.sheaf) ≫
        (TopCat.Sheaf.pushforward CommRingCat g.base).map
          ((algebraPullback g).obj A).hom := by
  have key := homEquiv_sq (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base)
    A.hom ((algebraPullbackMap g).app A) (inverseImageStructureMap g)
    ((algebraPullback g).obj A).hom (algebraPullback_isPushout g A).w
  refine key.trans (congrArg (· ≫ _) ?_)
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
    S.sheaf T.sheaf).apply_symm_apply _

/-- `adjointAlgebraMap` read as a morphism of sheaves of not necessarily commutative rings,
which is the category sheaves of modules are taken over. -/
public def adjointRingMap :
    AlgebraSheaf.ringSheaf A ⟶
      ((Opens.map g.base).sheafPushforwardContinuous _ _ _).obj
        (AlgebraSheaf.ringSheaf ((algebraPullback g).obj A)) :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (adjointAlgebraMap g A)

/-- `adjointAlgebraMap_structure` for sheaves of not necessarily commutative rings.  The
underlying sheaf of rings and the structure morphism of an algebra sheaf are by definition the
image of the algebra and of its structure morphism under `forget₂ CommRingCat RingCat`, so this
is the image of the preceding square, and both the comorphism of `g` and the direct image are
unchanged by that functor. -/
public theorem adjointRingMap_structure :
    AlgebraSheaf.structureMap A ≫ adjointRingMap g A =
      g.toRingCatSheafHom ≫ ((Opens.map g.base).sheafPushforwardContinuous _ _ _).map
        (AlgebraSheaf.structureMap ((algebraPullback g).obj A)) := by
  refine ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map_comp _ _).symm.trans ?_
  refine (congrArg _ (adjointAlgebraMap_structure g A)).trans ?_
  exact (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map_comp _ _

/-! ### The comparison morphism, and the reduction of the clause to its invertibility -/

/-- The morphism of underlying `𝒪_S`-modules induced by `adjointAlgebraMap`, landing in the
direct image of the underlying `𝒪_T`-module of the pullback algebra.

The underlying module of an algebra sheaf is its sheaf of rings over itself with scalars
restricted along the structure morphism, so the morphism on underlying modules is
`SheafOfModules.unitToPushforwardObjUnit` of `adjointRingMap` with scalars restricted; that
lands in restriction of scalars taken outside the direct image, and
`restrictScalars_pushforward_obj`, `SheafOfModules.pushforwardCongr` at
`adjointRingMap_structure`, and `pushforward_restrictScalars_obj` move it to the other side. -/
public def comparisonPushforward :
    AlgebraSheaf.underlyingModule A ⟶ (Scheme.Modules.pushforward g).obj
      (AlgebraSheaf.underlyingModule ((algebraPullback g).obj A)) :=
  (SheafOfModules.restrictScalars (AlgebraSheaf.structureMap A)).map
      (SheafOfModules.unitToPushforwardObjUnit (adjointRingMap g A)) ≫
    (SheafOfModules.pushforwardCongr (adjointRingMap_structure g A)).hom.app _

/-- **The comparison morphism of the quasi-coherence clause of Stacks Tag 01SA**:
`g^*A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` on underlying modules, the adjoint transpose of
`comparisonPushforward`.  The clause is the assertion that this is invertible. -/
public def comparison :
    (Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule A) ⟶
      AlgebraSheaf.underlyingModule ((algebraPullback g).obj A) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (comparisonPushforward g A)

/-- **The quasi-coherence clause of Stacks Tag 01SA, reduced to invertibility of `comparison`.**
If the comparison morphism is invertible then the pullback of a quasi-coherent algebra sheaf
along an arbitrary morphism of schemes is quasi-coherent.

The inverse image of a quasi-coherent module is quasi-coherent by
`Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback` (Stacks Tag 01BG), and
quasi-coherence is closed under isomorphism. -/
public theorem isQuasicoherent_of_isIso_comparison
    [(AlgebraSheaf.underlyingModule A).IsQuasicoherent] (h : IsIso (comparison g A)) :
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ (comparison g A) h)
    (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g
      (AlgebraSheaf.underlyingModule A))

/-! ### The stalk of the inverse image of a sheaf of modules on a scheme -/

/-- **The stalk of the inverse image of a sheaf of modules on a scheme**:
`(g^*M)_t ≅ L(M_{g t})`, naturally in `M`, for any `L` left adjoint to restriction of scalars
along the stalk map of `g`.  For `L = ModuleCat.extendScalars` — available whenever the stalk
rings are in hand as commutative rings — this reads
`(g^*M)_t ≅ M_{g t} ⊗_{𝒪_{S,g t}} 𝒪_{T,t}`.

This is `Stacks.ModuleSkyscraper.pullbackStalkIsoOfAdjunction` at the structure sheaves of two
schemes:
`AlgebraicGeometry.Scheme.Modules.pullback g` is by definition
`SheafOfModules.pullback g.toRingCatSheafHom`, so that result applies with no bridge.  It is
recorded because it is the stalk of the source of `comparison`, and because it is obtained by
conjugating a comparison of module skyscrapers under adjunctions rather than by computing a
filtered colimit — so the clause needs no statement about a tensor product commuting with a
filtered colimit of base rings. -/
@[ega "0 6.7.2" "special case", ega "I 9.1.12" "case Y = S"]
public def stalkPullbackModulesIso (t : T)
    {L : ModuleCat.{u} (Stacks.ModuleSkyscraper.Stalk S.ringCatSheaf (g.base t)) ⥤
      ModuleCat.{u} (Stacks.ModuleSkyscraper.Stalk T.ringCatSheaf t)}
    (adjL : L ⊣ ModuleCat.restrictScalars (Stacks.ModuleSkyscraper.stalkRingMap
      g.base T.ringCatSheaf S.ringCatSheaf g.toRingCatSheafHom t).hom) :
    Scheme.Modules.pullback g ⋙
        AlgebraicGeometry.SheafOfModules.stalkFunctor T.ringCatSheaf t ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor S.ringCatSheaf (g.base t) ⋙ L :=
  Stacks.ModuleSkyscraper.pullbackStalkIsoOfAdjunction g.base T.ringCatSheaf S.ringCatSheaf
    g.toRingCatSheafHom t adjL

end Stacks.ModuleStalkTensor

end

end
