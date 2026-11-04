module

public import StacksFrontier.AlgebraicGeometry.OpenImmersionAlgebraBridges.PushforwardFullyFaithful
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.InverseImageStructureSheaf

/-!
# The structural map of an open immersion is an isomorphism: `j⁻¹𝒪_X ≅ 𝒪_U`

Let `j : U ⟶ X` be an open immersion of schemes. The structural map
`inverseImageStructureMap j : j⁻¹𝒪_X ⟶ 𝒪_U` — the adjunct of the comorphism `j.c` under the
pullback–pushforward adjunction on sheaves of commutative rings — is an isomorphism.

## Main results

* `Stacks.OpenImmersionAlgebraBridges.inverseImageStructureMap_eq`: for *any* morphism of
  schemes, the structural map is `j⁻¹(j.c)` followed by the counit of the adjunction.
* `Stacks.OpenImmersionAlgebraBridges.isIso_inverseImageStructureMap`: for an open immersion it
  is an isomorphism. Stated for both spellings of the constant that occur in the repository,
  which are `rfl`-equal (see below).

## How it is proved, and what each half needs

The decomposition `inverseImageStructureMap j = j⁻¹(j.c) ≫ ε_{𝒪_U}` is
`CategoryTheory.Adjunction.homEquiv_counit` and holds for every morphism of schemes. Its two
factors are isomorphisms for different reasons.

* The counit `ε` is an isomorphism because the right adjoint `j_*` is fully faithful
  (`CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful`), which is
  `Stacks.SheafPushforwardInducing.fullyFaithful_pushforward_of_isInducing` applied to the open
  embedding `j.base`.
* `IsIso (j⁻¹(j.c))` is read off the naive pullback. Mathlib's
  `Topology.IsOpenEmbedding.sheafPullbackIso` identifies `TopCat.Sheaf.pullback` along an open
  embedding with `Topology.IsOpenEmbedding.sheafPullback`, which on presheaves is precomposition
  with the image functor on opens; so the component of `j⁻¹(j.c)` at `V : U.Opens` is
  `j.c.app (op (j ''ᵁ V))`, an isomorphism by
  `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`. Being componentwise an isomorphism
  of presheaves it is an isomorphism of sheaves, `sheafToPresheaf` being fully faithful.

So no stalk argument is needed, and nothing has to be said about `U` or `X` beyond that `j` is
an open immersion.

## Two parallel copies of one constant

`inverseImageStructureMap` is **defined twice in this repository**, and the two are `rfl`-equal
where their types meet:

* `AlgebraicGeometry.inverseImageStructureMap`, for a morphism of schemes — the one that
  `Stacks.AffineAlgebraEquivalence.algebraPullback` is built from, hence the one the algebra
  fibre product needs;
* `AlgebraicGeometry.ProEtale.inverseImageStructureMap`, for a morphism of locally ringed
  spaces, where `IsIso (inverseImageStructureMap p)` is *assumed* as a hypothesis and used to
  prove Stacks Tag 096K.

`inverseImageStructureMap_eq_proEtale` records the identification, so the single isomorphism
proof below serves both consumers; in particular Tag 096K's
`AlgebraicGeometry.ProEtale.bijective_forgetToTop_morphism_over` now applies to an open
immersion of schemes.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 096K](https://stacks.math.columbia.edu/tag/096K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe u

namespace Stacks.OpenImmersionAlgebraBridges

variable {U X : Scheme.{u}} (j : U ⟶ X)

/-- The comorphism `𝒪_X ⟶ j_* 𝒪_U` of a morphism of schemes, as a morphism of sheaves of
commutative rings. Spelled as a definition because the anonymous constructor `⟨j.c⟩` for a
morphism of `TopCat.Sheaf CommRingCat X` is not type-correct at instance transparency. -/
public def structureSheafHom :
    X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).obj U.sheaf :=
  ⟨j.c⟩

/-- The structural map `j⁻¹𝒪_X ⟶ 𝒪_U` is the inverse image of the comorphism followed by the
counit of the pullback–pushforward adjunction. True for every morphism of schemes. -/
public theorem inverseImageStructureMap_eq :
    AlgebraicGeometry.inverseImageStructureMap j =
      (TopCat.Sheaf.pullback CommRingCat.{u} j.base).map (structureSheafHom j) ≫
        (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j.base).counit.app U.sheaf :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j.base).homEquiv_counit
    X.sheaf U.sheaf (structureSheafHom j)

variable [H : IsOpenImmersion j]

/-! ### Bridge 1 at an open immersion -/

/-- The direct image of sheaves of commutative rings along an open immersion is full. -/
public instance full_pushforward_base :
    (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).Full :=
  Stacks.SheafPushforwardInducing.full_pushforward_of_isInducing
    H.base_open.isInducing CommRingCat.{u}

/-- The direct image of sheaves of commutative rings along an open immersion is faithful. -/
public instance faithful_pushforward_base :
    (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).Faithful :=
  Stacks.SheafPushforwardInducing.faithful_pushforward_of_isInducing
    H.base_open.isInducing CommRingCat.{u}

/-- The direct image of sheaves of commutative rings along an open immersion is fully
faithful. -/
public def fullyFaithful_pushforward_base :
    (TopCat.Sheaf.pushforward CommRingCat.{u} j.base).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- The counit of the pullback–pushforward adjunction on sheaves of commutative rings is an
isomorphism along an open immersion, because the right adjoint is fully faithful. -/
public instance isIso_counit_pullbackPushforward :
    IsIso (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} j.base).counit :=
  inferInstance

/-! ### Bridge 2: the inverse image of the comorphism -/

/-- The inverse image of the comorphism is an isomorphism for the *naive* pullback along an
open embedding: its component at `V` is `j.c.app (op (j ''ᵁ V))`, which the open-immersion
structure provides. -/
public theorem isIso_sheafPullback_naive_map
    (hf : Topology.IsOpenEmbedding (TopCat.Hom.hom j.base)) :
    IsIso ((hf.sheafPullback CommRingCat.{u}).map (structureSheafHom j)) := by
  have hcomp : ∀ V : U.Opens, IsIso
      (((hf.sheafPullback CommRingCat.{u}).map (structureSheafHom j)).hom.app (op V)) := by
    intro V
    change IsIso (j.c.app (op (hf.functor.obj V)))
    infer_instance
  have h1 : IsIso ((hf.sheafPullback CommRingCat.{u}).map (structureSheafHom j)).hom :=
    NatIso.isIso_of_isIso_app _
  have h2 : IsIso ((sheafToPresheaf (Opens.grothendieckTopology U.toPresheafedSpace)
      CommRingCat.{u}).map ((hf.sheafPullback CommRingCat.{u}).map (structureSheafHom j))) := h1
  exact isIso_of_fully_faithful
    (sheafToPresheaf (Opens.grothendieckTopology U.toPresheafedSpace) CommRingCat.{u}) _

/-- The inverse image `j⁻¹(j.c) : j⁻¹𝒪_X ⟶ j⁻¹j_*𝒪_U` of the comorphism is an isomorphism,
transported from the naive pullback along `Topology.IsOpenEmbedding.sheafPullbackIso`. -/
public theorem isIso_sheafPullback_map_structureSheafHom :
    IsIso ((TopCat.Sheaf.pullback CommRingCat.{u} j.base).map (structureSheafHom j)) :=
  (NatIso.isIso_map_iff (H.base_open.sheafPullbackIso CommRingCat.{u})
    (structureSheafHom j)).mpr (isIso_sheafPullback_naive_map j H.base_open)

/-- **The structural map of an open immersion is an isomorphism**: `j⁻¹𝒪_X ≅ 𝒪_U`. -/
public instance isIso_inverseImageStructureMap :
    IsIso (AlgebraicGeometry.inverseImageStructureMap j) := by
  rw [inverseImageStructureMap_eq]
  have := isIso_sheafPullback_map_structureSheafHom j
  infer_instance

/-- `j⁻¹𝒪_X ≅ 𝒪_U` as an isomorphism of sheaves of commutative rings. -/
public def inverseImageStructureIso :
    (TopCat.Sheaf.pullback CommRingCat.{u} j.base).obj X.sheaf ≅ U.sheaf :=
  asIso (AlgebraicGeometry.inverseImageStructureMap j)

/-! ### The same statement at the locally-ringed-space spelling of the constant -/

omit H in
/-- The locally-ringed-space copy of the structural map, evaluated at the underlying morphism
of locally ringed spaces of a morphism of schemes, is the scheme-level one. -/
public theorem inverseImageStructureMap_eq_proEtale :
    AlgebraicGeometry.ProEtale.inverseImageStructureMap j.toLRSHom =
      AlgebraicGeometry.inverseImageStructureMap j := rfl

/-- The hypothesis of Stacks Tag 096K is satisfied by an open immersion of schemes: the
structure sheaf of `U` is the inverse image of the structure sheaf of `X`. -/
public instance isIso_inverseImageStructureMap_proEtale :
    IsIso (AlgebraicGeometry.ProEtale.inverseImageStructureMap j.toLRSHom) :=
  isIso_inverseImageStructureMap j

/-- **Stacks Tag 096K for an open immersion.** A morphism of locally ringed spaces to `U` over
`X` is determined by, and determines, a continuous map over `X`. -/
public theorem bijective_forgetToTop_morphism_over_openImmersion
    {Z : LocallyRingedSpace.{u}} (q : Z ⟶ X.toLocallyRingedSpace) :
    Function.Bijective
      (fun g : {g : Z ⟶ U.toLocallyRingedSpace // g ≫ j.toLRSHom = q} ↦
        (⟨g.1.base, congrArg (fun k : Z ⟶ X.toLocallyRingedSpace ↦ k.base) g.2⟩ :
          {h : Z.toTopCat ⟶ U.toLocallyRingedSpace.toTopCat // h ≫ j.toLRSHom.base = q.base})) :=
  AlgebraicGeometry.ProEtale.bijective_forgetToTop_morphism_over j.toLRSHom q

end Stacks.OpenImmersionAlgebraBridges
