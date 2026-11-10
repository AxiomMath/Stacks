module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.FlatPullback
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionExistence
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksCore.Tactic.StacksAttribute

import all StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
import all StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.FlatPullback
import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtension
import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionExistence

/-!
# Improving a coherent module along a nested pair of subsets

Let `T'` and `T` be subsets of a Noetherian scheme `X` and let `F` be a coherent `𝒪_X`-module.
A map `F → F''` of coherent modules is an *improvement of `F` along `T' ⊆ T`* when it is an
isomorphism on stalks away from `T`, is surjective on stalks with target of depth at least one at
the points of `T` outside `T'`, and has target of depth at least two at the points of `T'`.  Such
a map exists, and it is unique up to a unique isomorphism over `F`.

Both halves reduce to the two steps of the source's construction, which this library already
has: the depth-one quotient of `F` along `T` (`AlgebraicGeometry.depthOneQuotient`,
[Stacks, Tag 0DX3]) followed by a depth-two extension along `T'`
(`AlgebraicGeometry.IsDepthTwoExtension`, [Stacks, Tag 0EI3]).

## Main definitions

* `AlgebraicGeometry.IsNestedImprovement`: the three local conditions on a map out of a coherent
  module.

## Main results

* `AlgebraicGeometry.isDepthTwoExtension_lift_of_isNestedImprovement`: an improvement factors
  uniquely through the depth-one quotient of its source along `T`, by a depth-two extension
  along `T'`.
* `AlgebraicGeometry.nestedImprovement_unique`: two improvements of one module along the same
  pair of subsets are isomorphic by a unique isomorphism over that module.
* `AlgebraicGeometry.exists_isNestedImprovement`: a coherent module admits an improvement.
* `AlgebraicGeometry.isNestedImprovement_pullback`: the pullback of an improvement along a
  Cohen-Macaulay morphism of Noetherian schemes is an improvement along the inverse images of the
  two subsets.
* `AlgebraicGeometry.isCoherent_pullback_of_isNestedImprovement`,
  `AlgebraicGeometry.isIso_stalk_pullback_of_isNestedImprovement`,
  `AlgebraicGeometry.one_le_depth_stalk_pullback_of_isNestedImprovement` and
  `AlgebraicGeometry.two_le_depth_stalk_pullback_of_isNestedImprovement`: its clauses one at a
  time, each carrying only the hypotheses that clause needs.

## Implementation notes

The two depth conditions together give depth at least one at every point of `T`, so an
improvement factors uniquely through the depth-one quotient `F'` of `F` along `T`.  The factoring
map `F' → F''` is a depth-two extension along `T'`: away from `T` it is an isomorphism on stalks
because both `F → F'` and `F → F''` are; at a point of `T` outside `T'` it is surjective on
stalks because `F → F''` is, and injective because a map out of the depth-one quotient which is
an isomorphism on the stalks away from `T` is a monomorphism
(`AlgebraicGeometry.mono_of_depthOneQuotient_source`).  Uniqueness of an improvement is therefore
uniqueness of the depth-two extension (`AlgebraicGeometry.depthTwoExtension_unique`), transported
across the epimorphism `F → F'`.  It needs neither a dualizing complex nor `T' ⊆ T`.

Surjectivity on a stalk is epimorphy in `AddCommGrpCat` and the condition away from `T` is
invertibility of the induced map of abelian-group stalks, matching
`AlgebraicGeometry.IsDepthOneQuotient` and `AlgebraicGeometry.IsImprovement`.  The depth
conditions are stated with the module structure on the stalk spelled out, as in
`AlgebraicGeometry.IsDepthTwoExtension`, so that they fit the existing depth results without
transport.

Existence carries the two hypotheses that `AlgebraicGeometry.exists_isDepthTwoExtension` carries,
because this library does not have them: `hdepthOutside`, which is [Stacks, Tag 0EY0] part (3),
and `hext`, which asks for the extension of the depth-one quotient across `T'` by sections over
the opens whose complement lies in `T'` — the colimit of pushforwards, stabilized, which is
`AlgebraicGeometry.IsStabilizedOpenExtension`.  The source derives the coherence of that colimit
from Faltings' finiteness criterion [Stacks, Tag 0EFD] applied to a dualizing complex, using both
the hypothesis that `X` locally has one and the hypothesis on immediate specializations into
`T'`; those two hypotheses of the source enter its argument only through that finiteness, so, as
in `AlgebraicGeometry.exists_isDepthTwoExtension`, neither appears below and the statement is
correspondingly stronger.  The depth-one quotient of `F` along `T` already has depth at least one
along `T'`, so `hext` is asked of it directly rather than of its own depth-one quotient along
`T'`, which is the same module.

The assertion about the pullback along a Cohen-Macaulay morphism is proved clause by clause and
then bundled, so that each clause records the hypotheses it alone needs.  Coherence of the target
and condition (1) need no hypothesis on the morphism at all; of the Cohen-Macaulay hypothesis only
the flatness half is used, through the formula for the change in depth along a flat local
homomorphism [Stacks, Tag 0338], so the fibre never has to be identified and its
Cohen-Macaulayness is an unused hypothesis rather than a missing ingredient.

Surjectivity on the stalks in condition (2) is not read off a comparison of a stalk map with its
base change: this library has that comparison only for a bijective map, in
`AlgebraicGeometry.modulePullback_stalkMap_bijective`, and not for a surjective one.  It is
obtained from the cokernel instead.  Epimorphy on the stalk at a point is the vanishing of the
stalk of the cokernel there, in both directions; the pullback of modules preserves cokernels,
being a left adjoint; and the stalk of a pullback is an extension of scalars of the stalk, which
vanishes wherever the stalk downstairs does.  Only the first of those three steps needs anything
new, and it is the proof of `AlgebraicGeometry.isZero_stalk_cokernel_of_isIso_stalkAb` with `Epi`
in place of `IsIso`, which is all that proof uses of its hypothesis.

## References

* [Stacks Project, Tag 0EI4](https://stacks.math.columbia.edu/tag/0EI4)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The three local conditions defining an improvement of a coherent module `F` along a nested
pair `T' ⊆ T` of subsets: an isomorphism on stalks outside `T`, surjective on stalks with target
of depth at least one at the points of `T` outside `T'`, and target of depth at least two at the
points of `T'`. -/
public def IsNestedImprovement {X : Scheme.{u}} (T T' : Set X) {F G : X.Modules}
    (φ : F ⟶ G) : Prop :=
  G.IsCoherent ∧
    (∀ x : X, x ∉ T →
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf)) ∧
    (∀ x : X, x ∈ T → x ∉ T' →
      Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf) ∧
        (letI : Module (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val x
        (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))) ∧
    (∀ x : X, x ∈ T' →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))

/-- The target of an improvement along `T' ⊆ T` has depth at least one at every point of `T`:
at least one at the points outside `T'` and at least two at the points of `T'`. -/
public theorem one_le_depth_stalk_of_isNestedImprovement {X : Scheme.{u}} {T T' : Set X}
    {F G : X.Modules} {φ : F ⟶ G} (h : IsNestedImprovement T T' φ) (x : X) (hx : x ∈ T) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
    (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) := by
  by_cases hx' : x ∈ T'
  · exact le_trans (by norm_num) (h.2.2.2 x hx')
  · exact (h.2.2.1 x hx hx').2

/-- Depth is unchanged by a stalkwise isomorphism: the stalk map is then a linear equivalence of
modules over the local ring at the point. -/
private lemma depth_stalk_eq_of_isIso_stalkMap {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : X) (h : IsIso (SheafOfModules.stalkMap X.ringCatSheaf x f)) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) M.val x
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) N.val x
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x) =
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) N.val.presheaf x) :=
  have hbij : Function.Bijective (stalkMapLinear (R := X.presheaf) M.val N.val f.val x) :=
    (ConcreteCategory.isIso_iff_bijective (SheafOfModules.stalkMap X.ringCatSheaf x f)).mp h
  Module.depth_eq_depth_of_linearEquiv _ (LinearEquiv.ofBijective _ hbij)

/-- The stalk functor on abelian presheaves takes a composite of module maps to the composite. -/
private lemma stalkFunctor_map_comp_mapPresheaf {X : Scheme.{u}} {F G H : X.Modules}
    (f : F ⟶ G) (g : G ⟶ H) (x : X) :
    (TopCat.Presheaf.stalkFunctor Ab.{u} x).map (f ≫ g).mapPresheaf =
      (TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf ≫
        (TopCat.Presheaf.stalkFunctor Ab.{u} x).map g.mapPresheaf :=
  (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map_comp f g

/-- An improvement of `F` along `T' ⊆ T` factors uniquely through the depth-one quotient of `F`
along `T`, and the factoring map is a depth-two extension along `T'`.

This is the factorization `F → F' → F''` of the source's proof, read backwards: the depth
conditions of an improvement give depth at least one along `T`, which is the universal property
of the depth-one quotient, and the resulting map is a monomorphism, hence an isomorphism on the
stalks at the points of `T` outside `T'`, where the improvement is surjective. -/
public theorem isDepthTwoExtension_lift_of_isNestedImprovement {X : Scheme.{u}} [IsNoetherian X]
    {T T' : Set X} (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent] {G : X.Modules} (φ : F ⟶ G)
    (hφ : IsNestedImprovement T T' φ) :
    ∃! l : depthOneQuotient X T hT F ⟶ G,
      toDepthOneQuotient X T hT F ≫ l = φ ∧ IsDepthTwoExtension T' l := by
  let : G.IsCoherent := hφ.1
  have hq := depthOneQuotient_spec X T hT F
  obtain ⟨l, hl, hluniq⟩ := depthOneQuotient_lift X T hT F G φ
    fun x hx => one_le_depth_stalk_of_isNestedImprovement hφ x hx
  have hcomp := stalkFunctor_map_comp_mapPresheaf (toDepthOneQuotient X T hT F) l
  rw [hl] at hcomp
  -- the factoring map is an isomorphism on the stalks away from `T`
  have hlT : ∀ x : X, x ∉ T →
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map l.mapPresheaf) := by
    intro x hx
    have : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      (toDepthOneQuotient X T hT F).mapPresheaf) := hq.2.2.1 x hx
    have := hφ.2.1 x hx
    exact IsIso.of_isIso_fac_left (hcomp x).symm
  have hmonol : Mono l := mono_of_depthOneQuotient_source _ hq l hlT
  -- hence it is a depth-two extension along `T'`
  have hlD : IsDepthTwoExtension T' l := by
    refine ⟨hφ.1, ?_, fun x hx' => hφ.2.2.2 x hx'⟩
    intro x hx'
    by_cases hx : x ∈ T
    · have := (hφ.2.2.1 x hx hx').1
      have := epi_of_epi_fac (hcomp x).symm
      have : Mono ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map l.mapPresheaf) :=
        mono_stalkAb_of_mono l hmonol x
      exact isIso_stalkMap_of_isIso_stalkFunctor l x (isIso_of_mono_of_epi _)
    · exact isIso_stalkMap_of_isIso_stalkFunctor l x (hlT x hx)
  exact ⟨l, ⟨hl, hlD⟩, fun m hm => hluniq m hm.1⟩

/-- **Stacks Project, Tag 0EI4, uniqueness.** Two improvements of a coherent module along the
same pair of subsets are isomorphic by a unique isomorphism compatible with the two maps.

Each one factors through the depth-one quotient of its source along `T` by a depth-two extension
along `T'`, so the comparison is the one of [Stacks, Tag 0EI3], transported across the
epimorphism onto the depth-one quotient. -/
@[stacks 0EI4 "uniqueness, unconditionally: no dualizing complex is needed, no condition on \
immediate specializations is used, and the inclusion T' ⊆ T is not needed either"]
public theorem nestedImprovement_unique (X : Scheme.{u}) [IsNoetherian X]
    (T T' : Set X) (hT : StableUnderSpecialization T)
    (F G H : X.Modules) [F.IsCoherent] (φ : F ⟶ G) (ψ : F ⟶ H)
    (hφ : IsNestedImprovement T T' φ) (hψ : IsNestedImprovement T T' ψ) :
    ∃! e : G ≅ H, φ ≫ e.hom = ψ := by
  have hq := depthOneQuotient_spec X T hT F
  have hepiq : Epi (toDepthOneQuotient X T hT F) := hq.2.1
  obtain ⟨l, ⟨hl, hlD⟩, -⟩ := isDepthTwoExtension_lift_of_isNestedImprovement hT F φ hφ
  obtain ⟨m, ⟨hm, hmD⟩, -⟩ := isDepthTwoExtension_lift_of_isNestedImprovement hT F ψ hψ
  obtain ⟨e, he, heuniq⟩ :=
    depthTwoExtension_unique X T' (depthOneQuotient X T hT F) G H l m hlD hmD
  refine ⟨e, ?_, fun c hc => heuniq c ?_⟩
  · change φ ≫ e.hom = ψ
    rw [← hl, Category.assoc, he, hm]
  · change l ≫ c.hom = m
    refine (cancel_epi (toDepthOneQuotient X T hT F)).mp ?_
    rw [← Category.assoc, hl, hc, hm]

/-- **Stacks Project, Tag 0EI4, existence.** A coherent module on a Noetherian scheme admits an
improvement along a nested pair `T' ⊆ T` of subsets stable under specialization: a map to a
coherent module which is an isomorphism on the stalks away from `T`, is surjective on the stalks
with target of depth at least one at the points of `T` outside `T'`, and has target of depth at
least two at the points of `T'`.

The map is the depth-one quotient of `F` along `T` followed by a depth-two extension of that
quotient along `T'`, which is the source's construction.  The hypotheses `hdepthOutside` and
`hext` are the two inputs of the source's existence proof which this library does not have; they
subsume what the source extracts from the dualizing complex and from the condition on immediate
specializations into `T'`, so neither of those two hypotheses of the source appears here.  See
the implementation notes of this module. -/
@[stacks 0EI4 "existence, conditional on a coherent stabilized open extension of the depth-one \
quotient along T' and on Tag 0EY0 part (3); as for Tag 0EI3 in this library, those two \
hypotheses replace the dualizing complex and the condition on immediate specializations, which \
are therefore not assumed"]
public theorem exists_isNestedImprovement (X : Scheme.{u}) [IsNoetherian X]
    (T T' : Set X) (hTT' : T' ⊆ T) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent]
    (hdepthOutside : ∀ (V : X.Opens) (H : X.Modules), H.IsCoherent →
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H) →
      ∀ y : X, y ∉ (V : Set X) →
        letI : Module (X.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) H.val y
        (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
          (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
          (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y))
    (hext : ∃ (G : X.Modules) (ψ : depthOneQuotient X T hT F ⟶ G),
      IsStabilizedOpenExtension T' ψ) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsNestedImprovement T T' φ := by
  have hq := depthOneQuotient_spec X T hT F
  let : Epi (toDepthOneQuotient X T hT F) := hq.2.1
  obtain ⟨G, ψ, hψ⟩ := hext
  -- the stabilized open extension of the depth-one quotient is a depth-two extension along `T'`
  have hψD : IsDepthTwoExtension T' ψ := by
    refine ⟨hψ.1, ?_, ?_⟩
    · intro x hx
      obtain ⟨V, hVT, -, hψV, -⟩ := hψ.2 x
      exact hψV x (by by_contra h; exact hx (hVT h))
    · intro x hx
      obtain ⟨V, -, hxV, -, hunit⟩ := hψ.2 x
      exact hdepthOutside V G hψ.1 hunit x (hxV hx)
  refine ⟨G, toDepthOneQuotient X T hT F ≫ ψ, hψ.1, ?_, ?_, fun x hx' => hψD.2.2 x hx'⟩
  · -- away from `T` both steps are isomorphisms on stalks
    intro x hx
    rw [stalkFunctor_map_comp_mapPresheaf]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hq.2.2.1 x hx)
      (isIso_stalkAb_of_isIso_stalkMap ψ x (hψD.2.1 x fun hx' => hx (hTT' hx')))
  · -- on `T` outside `T'` the first step is surjective and the second keeps the depth bound
    intro x hx hx'
    have hiso : IsIso (SheafOfModules.stalkMap X.ringCatSheaf x ψ) := hψD.2.1 x hx'
    refine ⟨?_, ?_⟩
    · rw [stalkFunctor_map_comp_mapPresheaf]
      exact @epi_comp _ _ _ _ _ _ (epi_stalkAb_of_epi (toDepthOneQuotient X T hT F) x) _
        (isIso_stalkAb_of_isIso_stalkMap ψ x hiso).epi_of_iso
    · rw [← depth_stalk_eq_of_isIso_stalkMap ψ x hiso]
      exact hq.2.2.2 x hx

/-! ### Cohen-Macaulay pullback -/

/-- A stalkwise isomorphism stays one after pullback along any morphism of schemes: the stalk of
a pullback is an extension of scalars of the stalk, so a bijective stalk map stays bijective. -/
private lemma isIso_stalk_pullback_map_of_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F G : X.Modules} (φ : F ⟶ G) (y : Y)
    (hiso : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} (f.base y)).map φ.mapPresheaf)) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
      ((Scheme.Modules.pullback f).map φ).mapPresheaf) := by
  have hbij : Function.Bijective
      (stalkMapLinear (R := X.presheaf) F.val G.val φ.val (f.base y)) := by
    let p := (TopCat.Presheaf.stalkFunctor Ab.{u} (f.base y)).map φ.mapPresheaf
    have : IsIso p := hiso
    have hp := (ConcreteCategory.isIso_iff_bijective p).mp (inferInstance : IsIso p)
    change Function.Bijective
      ((TopCat.Presheaf.stalkFunctor Ab.{u} (f.base y)).map
        ((PresheafOfModules.toPresheaf
          (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map φ.val)).hom at hp
    exact hp
  have hpb := modulePullback_stalkMap_bijective f.toLRSHom.toShHom F G φ y hbij
  let q := (TopCat.Presheaf.stalkFunctor Ab.{u} y).map
    (Scheme.Modules.Hom.mapPresheaf ((Scheme.Modules.pullback f).map φ))
  have hq : Function.Bijective q.hom := by
    change Function.Bijective
      ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
        ((PresheafOfModules.toPresheaf
          (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map
          ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).map
            φ).val)).hom at hpb
    exact hpb
  exact (ConcreteCategory.isIso_iff_bijective q).mpr hq

/-- A lower bound on the depth of a stalk is inherited by the pullback along a morphism which is
flat on the local ring at the point: the stalk of the pullback is the base change of the stalk,
whose depth is the depth of the stalk plus the depth of the fibre. -/
private lemma le_depth_stalk_pullback_of_flat_stalkMap {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : Y ⟶ X)
    (G : X.Modules) [G.IsFiniteType] (y : Y) (hflat : (f.stalkMap y).hom.Flat) (n : ℕ∞)
    (hdepth :
      letI : Module (X.presheaf.stalk (f.base y))
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val (f.base y)
      n ≤ Module.depth (X.presheaf.stalk (f.base y))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (f.base y)))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y))) :
    letI : Module (Y.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
    n ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback f).obj G).val.presheaf y) := by
  dsimp only at hdepth ⊢
  let R := X.presheaf.stalk (f.base y)
  let S := Y.presheaf.stalk y
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y)
  let N := TopCat.Presheaf.stalk (C := Ab.{u})
    ((Scheme.Modules.pullback f).obj G).val.presheaf y
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) G.val (f.base y)
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
  let : Algebra R S := (f.stalkMap y).hom.toAlgebra
  let : IsNoetherianRing R := inferInstance
  let : IsNoetherianRing S := inferInstance
  have : Module.Finite R M := SheafOfModules.finite_stalk X.sheaf G (f.base y)
  have : IsLocalHom (algebraMap R S) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.Flat R S := hflat
  have hformula := Module.depth_tensorProduct_of_flat (R := R) (S := S) (M := M) (N := S)
  obtain ⟨E, -⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f.toLRSHom.toShHom G y
  have hdepthEq : Module.depth S (IsLocalRing.maximalIdeal S) N =
      Module.depth S (IsLocalRing.maximalIdeal S) (TensorProduct R S M) :=
    Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal S) E
  change n ≤ Module.depth S (IsLocalRing.maximalIdeal S) N
  rw [hdepthEq, hformula]
  exact le_trans hdepth (le_add_of_nonneg_right (by positivity))

/-- **Stacks Project, Tag 0EI4, the pullback clause: coherence of the target.** The target of the
pullback of an improvement along a morphism with locally Noetherian source is again coherent.

A pullback of a coherent module needs only a locally Noetherian source, so neither flatness nor
Cohen-Macaulayness of the morphism is used. -/
@[stacks 0EI4 "coherence of the target of the pullback, in the assertion about the pullback \
along a Cohen-Macaulay morphism"]
public theorem isCoherent_pullback_of_isNestedImprovement {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (f : Y ⟶ X) {T T' : Set X} {F G : X.Modules} (φ : F ⟶ G)
    (hφ : IsNestedImprovement T T' φ) :
    ((Scheme.Modules.pullback f).obj G).IsCoherent :=
  letI : G.IsCoherent := hφ.1
  isCoherent_pullback f G

/-- **Stacks Project, Tag 0EI4, the pullback clause, condition (1).** The pullback of an
improvement along any morphism of schemes is an isomorphism on the stalks at every point outside
the inverse image of `T`.

The stalk of a pullback is the base change of the stalk, so a bijective stalk map stays
bijective; no hypothesis on the morphism is used. -/
@[stacks 0EI4 "condition (1) for the pullback: the isomorphism away from the inverse image of T, \
in the assertion about the pullback along a Cohen-Macaulay morphism"]
public theorem isIso_stalk_pullback_of_isNestedImprovement {X Y : Scheme.{u}} (f : Y ⟶ X)
    {T T' : Set X} {F G : X.Modules} (φ : F ⟶ G) (hφ : IsNestedImprovement T T' φ)
    (y : Y) (hy : y ∉ f.base ⁻¹' T) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
      ((Scheme.Modules.pullback f).map φ).mapPresheaf) :=
  isIso_stalk_pullback_map_of_isIso f φ y (hφ.2.1 (f.base y) hy)

/-- **Stacks Project, Tag 0EI4, the pullback clause, the depth bound of condition (2).** The
target of the pullback of an improvement along a Cohen-Macaulay morphism of Noetherian schemes
has stalks of depth at least one at every point of the inverse image of `T` lying outside the
inverse image of `T'`.

Only the flatness half of the Cohen-Macaulay hypothesis is used: the depth of the base change of
a stalk along a flat local homomorphism is the depth of the stalk plus the depth of the fibre, so
the bound downstairs is inherited. -/
@[stacks 0EI4 "the depth bound of condition (2) for the pullback, in the assertion about the \
pullback along a Cohen-Macaulay morphism"]
public theorem one_le_depth_stalk_pullback_of_isNestedImprovement {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {T T' : Set X} {F G : X.Modules} (φ : F ⟶ G)
    (hφ : IsNestedImprovement T T' φ) (f : Y ⟶ X)
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib)
    (y : Y) (hy : y ∈ f.base ⁻¹' T) (hy' : y ∉ f.base ⁻¹' T') :
    letI : Module (Y.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
    (1 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
  letI : G.IsCoherent := hφ.1
  letI : G.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  le_depth_stalk_pullback_of_flat_stalkMap f G y (hcm y).1 1
    (hφ.2.2.1 (f.base y) hy hy').2

/-- **Stacks Project, Tag 0EI4, the pullback clause, condition (3).** The target of the pullback
of an improvement along a Cohen-Macaulay morphism of Noetherian schemes has stalks of depth at
least two at every point of the inverse image of `T'`.

Only the flatness half of the Cohen-Macaulay hypothesis is used, by the same depth formula along
a flat local homomorphism. -/
@[stacks 0EI4 "condition (3) for the pullback, in the assertion about the pullback along a \
Cohen-Macaulay morphism"]
public theorem two_le_depth_stalk_pullback_of_isNestedImprovement {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {T T' : Set X} {F G : X.Modules} (φ : F ⟶ G)
    (hφ : IsNestedImprovement T T' φ) (f : Y ⟶ X)
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib)
    (y : Y) (hy' : y ∈ f.base ⁻¹' T') :
    letI : Module (Y.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
    (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback f).obj G).val.presheaf y) :=
  letI : G.IsCoherent := hφ.1
  letI : G.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  le_depth_stalk_pullback_of_flat_stalkMap f G y (hcm y).1 2 (hφ.2.2.2 (f.base y) hy')

/-! ### Surjectivity on stalks under pullback -/

/-- Pullback of modules along a morphism of schemes preserves cokernels, being a left adjoint. -/
private noncomputable def modulePullbackCokernelIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (α : M ⟶ N) :
    (Scheme.Modules.pullback f).obj (cokernel α) ≅
      cokernel ((Scheme.Modules.pullback f).map α) :=
  haveI : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  PreservesCokernel.iso (Scheme.Modules.pullback f) α

/-- Where a map is an epimorphism on the stalk at `x`, the stalk of its cokernel at `x` vanishes:
the projection to the cokernel dies on that stalk, and it is an epimorphism there. -/
private lemma isZero_stalk_cokernel_of_epi_stalkAb {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : X) (h : Epi ((stalkAb X x).map f)) :
    IsZero ((stalkAb X x).obj (cokernel f)) := by
  have hepi : Epi ((stalkAb X x).map (cokernel.π f)) := epi_stalkAb_of_epi _ x
  have hcomp : (stalkAb X x).map f ≫ (stalkAb X x).map (cokernel.π f) = 0 :=
    stalkAb_map_comp_eq_zero f (cokernel.π f) x (cokernel.condition f)
  have hzero : (stalkAb X x).map (cokernel.π f) = 0 :=
    have := h
    (cancel_epi ((stalkAb X x).map f)).mp (hcomp.trans comp_zero.symm)
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_epi ((stalkAb X x).map (cokernel.π f))).mp ?_
  rw [hzero]
  exact zero_comp.trans zero_comp.symm

/-- A module whose stalk at the image point vanishes has vanishing stalk after pullback: the
stalk of the pullback is an extension of scalars of that stalk, and an extension of scalars of
the zero module is zero. -/
private lemma isZero_stalk_pullback_of_isZero_stalk {X Y : Scheme.{u}} (f : Y ⟶ X)
    (H : X.Modules) (y : Y) (h : IsZero ((stalkAb X (f.base y)).obj H)) :
    IsZero ((stalkAb Y y).obj ((Scheme.Modules.pullback f).obj H)) := by
  let R := X.presheaf.stalk (f.base y)
  let S := Y.presheaf.stalk y
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf (f.base y)
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) H.val (f.base y)
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Y.presheaf) ((Scheme.Modules.pullback f).obj H).val y
  let : Algebra R S := (f.stalkMap y).hom.toAlgebra
  obtain ⟨E, -⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f.toLRSHom.toShHom H y
  have hM : Subsingleton M := AddCommGrpCat.isZero_iff_subsingleton.mp h
  have hzero : ∀ z : TensorProduct R S M, z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s m => rw [Subsingleton.elim m (0 : M), TensorProduct.tmul_zero]
    | add p q hp hq => rw [hp, hq, add_zero]
  have hN : Subsingleton ((stalkAb Y y).obj ((Scheme.Modules.pullback f).obj H)) :=
    ⟨fun a b => E.injective ((hzero (E a)).trans (hzero (E b)).symm)⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Surjectivity on the stalk at a point is inherited by the pullback at every point above it.

Epimorphy on a stalk is the vanishing of the stalk of the cokernel there; the pullback of modules
preserves cokernels, being a left adjoint, and the stalk of a pullback is an extension of scalars
of the stalk, which carries the zero module to the zero module. -/
private lemma epi_stalk_pullback_map_of_epi_stalk {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F G : X.Modules} (φ : F ⟶ G) (y : Y)
    (hepi : Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} (f.base y)).map φ.mapPresheaf)) :
    Epi ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
      ((Scheme.Modules.pullback f).map φ).mapPresheaf) := by
  have h1 : IsZero ((stalkAb X (f.base y)).obj (cokernel φ)) :=
    isZero_stalk_cokernel_of_epi_stalkAb φ (f.base y) hepi
  have h2 : IsZero ((stalkAb Y y).obj ((Scheme.Modules.pullback f).obj (cokernel φ))) :=
    isZero_stalk_pullback_of_isZero_stalk f (cokernel φ) y h1
  have h3 : IsZero ((stalkAb Y y).obj (cokernel ((Scheme.Modules.pullback f).map φ))) :=
    h2.of_iso ((stalkAb Y y).mapIso (modulePullbackCokernelIso f φ).symm)
  exact epi_stalkAb_of_isZero_stalk_cokernel _ y h3

/-- **Stacks Project, Tag 0EI4, the assertion about the pullback.** The pullback of an improvement
along a Cohen-Macaulay morphism of Noetherian schemes is an improvement along the inverse images
of the two subsets.

Coherence of the target and condition (1) need no hypothesis on the morphism at all.  Of the
Cohen-Macaulay hypothesis only the flatness half is used, for the two depth bounds, by the formula
for the change in depth along a flat local homomorphism [Stacks, Tag 0338]; the fibre never has to
be identified.  Surjectivity in condition (2) is epimorphy on a stalk, which is the vanishing of
the stalk of the cokernel, and the pullback preserves cokernels and kills the zero module. -/
@[stacks 0EI4 "the assertion about the pullback along a Cohen-Macaulay morphism: the pullback \
satisfies conditions (1), (2) and (3) with respect to the inverse images of the two subsets"]
public theorem isNestedImprovement_pullback {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {T T' : Set X} {F G : X.Modules} (φ : F ⟶ G) (hφ : IsNestedImprovement T T' φ) (f : Y ⟶ X)
    (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x)) (hcm : f.IsCohenMacaulay hfib) :
    IsNestedImprovement (f.base ⁻¹' T) (f.base ⁻¹' T')
      ((Scheme.Modules.pullback f).map φ) :=
  ⟨isCoherent_pullback_of_isNestedImprovement f φ hφ,
    fun y hy => isIso_stalk_pullback_of_isNestedImprovement f φ hφ y hy,
    fun y hy hy' =>
      ⟨epi_stalk_pullback_map_of_epi_stalk f φ y (hφ.2.2.1 (f.base y) hy hy').1,
        one_le_depth_stalk_pullback_of_isNestedImprovement φ hφ f hfib hcm y hy hy'⟩,
    fun y hy' => two_le_depth_stalk_pullback_of_isNestedImprovement φ hφ f hfib hcm y hy'⟩

end AlgebraicGeometry

end
