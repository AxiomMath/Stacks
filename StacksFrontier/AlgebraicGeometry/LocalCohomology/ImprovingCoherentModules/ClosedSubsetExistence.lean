module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPointsDepth
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointSplittingConstruction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentOpenPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.UniversallyCatenaryDimension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ClosedStabilizedExtension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthDimensionCriterionGlobal
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FaltingsOpenPushforward
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.EssentiallyFiniteType
public import StacksCore.Tactic.StacksAttribute

import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionExistence
import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovement

/-!
# Existence of the depth-two extension along a closed subset

Let `X` be a Noetherian scheme, let `T ⊆ X` be closed and let `F` be a coherent `𝒪_X`-module.
[Stacks, Tag 0EI3] constructs a *depth-two extension* of `F` along `T` — a map to a coherent
module which is a stalk isomorphism away from `T` and whose stalks on `T` have depth at least
two — out of the depth-one quotient `F'` of `F` along `T`, by taking the colimit of the
pushforwards `j_{W,*}(F'|_W)` over the opens `W` whose complement lies in `T`.

For a closed `T` that colimit is not needed: the complement `V` of `T` is itself such an open
and is the smallest one, so the single pushforward `j_{V,*}(F'|_V)` is the extension.  Three of
the four clauses of `AlgebraicGeometry.IsStabilizedOpenExtension` are then formal, and are
discharged in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ClosedStabilizedExtension`;
what remains is coherence of that one pushforward, which this module proves and uses to remove
the hypothesis `hext` of the existence half of [Stacks, Tag 0EI3] for a closed subset.

Coherence is obtained from **Faltings' finiteness criterion**, which is the source's own route:
coherence of a direct image along an open immersion is local on the target
(`Stacks.AlgebraicGeometry.CoherentOpenPushforward.isCoherent_pushforward_of_forall_affineOpen`),
on an affine open it is finiteness of `H¹` of a local cohomology module, and that finiteness is
[Stacks, Tag 0EFD] at `s = 1` fed the depth hypothesis of [Stacks, Tag 0EI3].  The chain over the
spectrum of a ring with a dualizing complex is
`Stacks.AlgebraicGeometry.FaltingsPushforward.isCoherent_pushforward_of_depth_immediate_isoSpec`;
what is added here is its globalization over the affine opens of `X`, and its application to the
depth-one quotient, whose stalks away from `T` are those of `F`.

The library also has **Kollár's criterion** in the form [Stacks, Tag 0AWB]
(`AlgebraicGeometry.isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure`): the
direct image of a coherent module along an open immersion is coherent exactly when
`dim(𝒪_{closure {x}, z}) ≥ 2` for every associated point `x` of the module and every omitted
specialization `z` of `x`.  The depth hypothesis of [Stacks, Tag 0EI3] verifies that condition
too: an associated point `x` of `F'|_V` has `depth(F'_x) = 0`, hence `x ∉ T` and
`depth(F_x) = 0`, so by the hypothesis no point of `T` is an *immediate* specialization of `x`;
a specialization `z ∈ T` of `x` therefore admits a strictly intermediate point, and the
resulting chain `closure {z} ⊊ closure {w} ⊊ closure {x}` of irreducible closeds gives the
dimension bound.  That route is kept below, as
`AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient_of_formalFibres`, because its
hypotheses are not comparable with Faltings': it asks for universal catenarity and Serre's
condition `(S₁)` on the formal fibres along `T` instead of for a dualizing complex.  It is not
what [Stacks, Tag 0EI3] is proved from.

## Main results

* `IrreducibleClosedsCodim.two_le_topCodim_closureSingleton_of_not_isImmediateSpecialization`:
  a specialization which is not immediate has codimension at least two.
* `AlgebraicGeometry.isUniversallyCatenary_of_locallyHasDualizingComplex`: a scheme every affine
  open of which has a dualizing complex over its ring of sections is universally catenary.
* `AlgebraicGeometry.locallyHasDualizingComplex_of_locallyOfFiniteType`: a scheme locally of
  finite type over a Noetherian ring with a dualizing complex locally has a dualizing complex.
* `AlgebraicGeometry.isCoherent_pushforward_of_locallyHasDualizingComplex`: **Faltings'
  criterion globalized** — on a scheme which locally has a dualizing complex, the direct image
  of a coherent module along an open immersion is coherent as soon as its stalks have depth at
  least one at the points with an omitted immediate specialization.
* `AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient`:
  **coherence of the single pushforward**, which is the whole content of `hext` for a closed
  subset.
* `AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient_of_formalFibres`: the
  same coherence from Kollár's criterion instead, at universal catenarity and `(S₁)` on the
  formal fibres.
* `AlgebraicGeometry.exists_isDepthTwoExtension_of_locallyHasDualizingComplex`:
  **[Stacks, Tag 0EI3], existence** along a closed subset, with no hypothesis about extensions
  or colimits.

## The hypotheses, against the source's

[Stacks, Tag 0EI3] assumes that `X` locally has a dualizing complex and that `depth(F_x) ≥ 1`
whenever `x ⤳ x'` is an immediate specialization with `x' ∈ T` and `x ∉ T`.  Those two are
exactly the hypotheses of the existence statement below, and nothing else is assumed of `F`, `T`
or `X` beyond `X` being Noetherian and `T` closed.  Both are necessary:
`AlgebraicGeometry.exists_isDepthTwoExtension` omits them only because it carries `hext`
instead, and the implementation notes of its module record the `Spec ℤ` witness showing that the
conclusion fails without the depth hypothesis.  The dualizing hypothesis is in the affine-local
existential form `AlgebraicGeometry.LocallyHasDualizingComplex`, which is stronger than the
source's hypothesis that the members of *some* affine open cover have dualizing complexes, for
the reason recorded in the implementation notes of that definition.

## Implementation notes

The depth bound the globalized criterion asks of the depth-one quotient `F'` is stated at the
points of `V`, where `F'` is not `F` but is isomorphic to it on stalks.  Two file-private
lemmas, reached by `import all`, move the bound across that isomorphism:
`AlgebraicGeometry.isIso_stalkMap_of_isIso_stalkFunctor` of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionExistence`
reads the stalk isomorphism supplied by `AlgebraicGeometry.depthOneQuotient_spec` over the local
ring, and `AlgebraicGeometry.depth_stalk_eq_of_isIso_stalkMap` of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovement` then
equates the two depths.  This is the same pair of lemmas, used in the same way, as in
`Stacks.Algebraization.depthTwoImprovedSystem`.

## References

* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentOpenPushforward (isCoherent_pushforward_of_forall_affineOpen)
open Stacks.AlgebraicGeometry.FaltingsPushforward
  (isCoherent_pushforward_of_depth_immediate_isoSpec)
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace IrreducibleClosedsCodim

/-- **A specialization which is not immediate has codimension at least two.** If `x ⤳ z` with
`x ≠ z` and the specialization is not immediate, there is a point `w` strictly between the two,
and the chain `closure {z} ⊊ closure {w} ⊊ closure {x}` of irreducible closed subsets has
length two. -/
public theorem two_le_topCodim_closureSingleton_of_not_isImmediateSpecialization
    {Z : Type*} [TopologicalSpace Z] [T0Space Z] {x z : Z} (hxz : x ⤳ z) (hne : x ≠ z)
    (himm : ¬ TopologicalSpace.IsImmediateSpecialization x z) :
    2 ≤ topCodim (IrreducibleCloseds.closureSingleton z)
      (IrreducibleCloseds.closureSingleton x) := by
  have hall : ¬ ∀ w : Z, x ⤳ w → w ⤳ z → w = x ∨ w = z := fun h => himm ⟨hxz, hne, h⟩
  push Not at hall
  obtain ⟨w, hxw, hwz, hwx, hwz'⟩ := hall
  have h1 : IrreducibleCloseds.closureSingleton z < IrreducibleCloseds.closureSingleton w :=
    Topology.closureSingleton_lt_of_specializes_injective id continuous_id
      (fun _ _ _ h => h) hwz hwz'
  have h2 : IrreducibleCloseds.closureSingleton w < IrreducibleCloseds.closureSingleton x :=
    Topology.closureSingleton_lt_of_specializes_injective id continuous_id
      (fun _ _ _ h => h) hxw (fun h => hwx h.symm)
  let p : LTSeries (IrreducibleCloseds Z) :=
    { length := 2
      toFun := ![IrreducibleCloseds.closureSingleton z, IrreducibleCloseds.closureSingleton w,
        IrreducibleCloseds.closureSingleton x]
      step := by
        intro i
        match i with
        | ⟨0, _⟩ => exact h1
        | ⟨1, _⟩ => exact h2 }
  simpa [p] using length_le_topCodim (IrreducibleCloseds.closureSingleton z)
    (IrreducibleCloseds.closureSingleton x) p rfl rfl

end IrreducibleClosedsCodim

namespace AlgebraicGeometry

/-! ### Universal catenarity from the affine-local dualizing hypothesis -/

/-- **A scheme which locally has a dualizing complex is universally catenary.** Universal
catenarity of a locally Noetherian scheme is universal catenarity of the ring of sections of
every affine open (`AlgebraicGeometry.Scheme.isUniversallyCatenary_iff_forall_affineOpens`), and
a Noetherian ring with a dualizing complex is universally catenary, which is
[Stacks, Tag 0A80]. -/
public theorem isUniversallyCatenary_of_locallyHasDualizingComplex (X : Scheme.{u})
    [IsLocallyNoetherian X] (h : LocallyHasDualizingComplex X) :
    Scheme.IsUniversallyCatenary X := by
  refine (Scheme.isUniversallyCatenary_iff_forall_affineOpens X).mpr fun U => ?_
  have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨omega, homega⟩ := h U
  exact Dualizing.isUniversallyCatenary_of_isDualizingComplex homega

/-- **A scheme locally of finite type over a ring with a dualizing complex locally has a
dualizing complex.**  If `A` is Noetherian with a dualizing complex `K` and `f : X ⟶ Spec A` is
locally of finite type, then the ring of sections of every affine open of `X` has a dualizing
complex.

For an affine open `U` of `X`, the comparison `A → Γ(X, U)` is of finite type by
`AlgebraicGeometry.Scheme.Hom.finiteType_appLE` read at the affine opens `⊤ ⊆ Spec A` and
`U ⊆ X`, hence essentially of finite type, so [Stacks, Tag 0A7K]
(`Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType`) transports `K` to
`Γ(X, U)`.  No hypothesis is placed on `f` beyond being locally of finite type; in particular an
open subscheme of `Spec A` qualifies, since an open immersion is locally of finite type.

The dualizing complex is taken in the module universe of `A` itself, which is the universe in
which [Stacks, Tag 0A7K] produces the transported complex and in which
`AlgebraicGeometry.LocallyHasDualizingComplex` asks for its complexes.  This is the convention of
the ring-level consumers too, such as
`Dualizing.isUniversallyCatenary_of_isDualizingComplex`. -/
public theorem locallyHasDualizingComplex_of_locallyOfFiniteType {A : Type u} [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : Dualizing.IsDualizingComplex K) :
    LocallyHasDualizingComplex X := by
  intro U
  let _ : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hle : U.1 ≤ f ⁻¹ᵁ ⊤ := le_top
  let φ : A →+* Γ(X, U.1) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.1 hle).hom
  have hφ : φ.FiniteType :=
    (f.finiteType_appLE (isAffineOpen_top _) U.2 hle).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2)
  let _ : Algebra A Γ(X, U.1) := φ.toAlgebra
  have hfin : Algebra.FiniteType A Γ(X, U.1) := hφ
  obtain ⟨_, L, hL⟩ := Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType
    (B := Γ(X, U.1)) ⟨Γ(X, U.1), inferInstance, inferInstance, hfin, ⊥,
      Algebra.id Γ(X, U.1), IsScalarTower.right, IsLocalization.self bot_le⟩ K hK
  exact ⟨L, hL⟩

/-! ### Faltings' criterion over a scheme which locally has a dualizing complex -/

/-- **Faltings' criterion, globalized.** Let `X` be a locally Noetherian scheme which locally has
a dualizing complex, let `j : U ⟶ X` be an open immersion and let `G` be a coherent `𝒪_U`-module
whose stalk at `x` has depth at least one whenever some point outside the image of `j` is an
immediate specialization of `j(x)`.  Then `j_* G` is coherent.

Coherence of a direct image along an open immersion is tested on the affine opens of the target
(`Stacks.AlgebraicGeometry.CoherentOpenPushforward.isCoherent_pushforward_of_forall_affineOpen`),
and over an affine open `V` the restricted morphism `j ∣_ V` has a target identified with
`Spec Γ(X, V)` by `AlgebraicGeometry.IsAffineOpen.isoSpec`, a ring the hypothesis supplies a
dualizing complex over; so
`Stacks.AlgebraicGeometry.FaltingsPushforward.isCoherent_pushforward_of_depth_immediate_isoSpec`
applies there.  Its depth hypothesis is the given one read inside `V`: the depth by
`AlgebraicGeometry.Scheme.Modules.depth_stalk_restrict`, the omitted points by
`AlgebraicGeometry.mem_range_morphismRestrict_iff`, and the immediate specializations by
`TopologicalSpace.IsImmediateSpecialization.map_of_isOpenEmbedding` at the open embedding
`V.ι`. -/
@[sga "2 VIII 2.1" "special case", sga "2 VIII 2.3" "(ii) ⇒ (iv)"]
public theorem isCoherent_pushforward_of_locallyHasDualizingComplex {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (hdual : LocallyHasDualizingComplex X) (G : U.Modules) [G.IsCoherent]
    (hdepth : ∀ (x : U) (z : X), z ∉ Set.range j.base →
      TopologicalSpace.IsImmediateSpecialization (j.base x) z →
      (1 : ℕ∞) ≤ Module.depth (U.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (U.presheaf.stalk x)) (G.presheaf.stalk x)) :
    ((Scheme.Modules.pushforward j).obj G).IsCoherent := by
  refine isCoherent_pushforward_of_forall_affineOpen j G fun V hV => ?_
  let _ : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨omega, homega⟩ := hdual ⟨V, hV⟩
  have hVN : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have hUN : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : (G.restrict (j ⁻¹ᵁ V).ι).IsCoherent :=
    Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion (j ⁻¹ᵁ V).ι G
  refine isCoherent_pushforward_of_depth_immediate_isoSpec (j ∣_ V) hV.isoSpec omega homega
    (G.restrict (j ⁻¹ᵁ V).ι) ?_
  intro x z hz himm
  rw [Scheme.Modules.depth_stalk_restrict (j ⁻¹ᵁ V).ι G x]
  refine hdepth ((j ⁻¹ᵁ V).ι.base x) (V.ι.base z)
    (fun hmem => hz ((mem_range_morphismRestrict_iff j V z).mpr hmem)) ?_
  have hmap := himm.map_of_isOpenEmbedding (f := V.ι.base) V.ι.isOpenEmbedding
  have heq : V.ι.base ((j ∣_ V).base x) = j.base ((j ⁻¹ᵁ V).ι.base x) :=
    morphismRestrict_base_coe j V x
  rwa [heq] at hmap

/-! ### Coherence of the single pushforward -/

/-- A point of the open `V` whose complement is `T` is not in `T`. -/
private theorem image_notMem_of_hV {X : Scheme.{u}} {T : Set X} {V : X.Opens}
    (hV : (V : Set X) = Tᶜ) (x : V) : V.ι.base x ∉ T := by
  rw [← Set.mem_compl_iff, ← hV]
  exact x.2

/-- A point outside the range of `V.ι`, where `V` has complement `T`, lies in `T`. -/
private theorem mem_of_notMem_range_ι {X : Scheme.{u}} {T : Set X} {V : X.Opens}
    (hV : (V : Set X) = Tᶜ) {z : X} (hz : z ∉ Set.range V.ι.base) : z ∈ T := by
  have hz' : z ∉ (V : Set X) := by
    rw [← Scheme.Opens.opensRange_ι V]
    exact hz
  rw [hV] at hz'
  exact not_not.mp hz'

/-- The restriction of the depth-one quotient to an open is coherent. -/
private theorem isCoherent_restrict_depthOneQuotient (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T) (V : X.Opens) (F : X.Modules)
    [F.IsCoherent] : ((depthOneQuotient X T hT F).restrict V.ι).IsCoherent := by
  have : (depthOneQuotient X T hT F).IsCoherent := (depthOneQuotient_spec X T hT F).1
  exact Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion V.ι _

/-- **The pushforward of the depth-one quotient from the complement of a closed subset is
coherent.** Let `X` be a Noetherian scheme which locally has a dualizing complex, let `V` be an
open of `X` whose complement is `T`, and let `F` be a coherent module whose depth at a point
outside `T` is at least one as soon as some point of `T` is an immediate specialization of it.
Then `j_{V,*}(F'|_V)` is coherent, `F'` being the depth-one quotient of `F` along `T`.

This is `isCoherent_pushforward_of_locallyHasDualizingComplex` at `j = V.ι` and `G = F'|_V`, so
the only thing to supply is its depth bound.  A point `x` of `V` lies outside `T` and an omitted
point `z` lies in `T`, where the hypothesis bounds the depth of the stalk of `F`; the stalk of
`F'` at `x` is the stalk of `F` there, `AlgebraicGeometry.depthOneQuotient_spec` making
`F ⟶ F'` a stalk isomorphism away from `T`. -/
public theorem isCoherent_pushforward_restrict_depthOneQuotient
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
    (V : X.Opens) (hV : (V : Set X) = Tᶜ) (F : X.Modules) [F.IsCoherent]
    (hdual : LocallyHasDualizingComplex X)
    (hdepth : ∀ x z : X, x ∉ T → z ∈ T → TopologicalSpace.IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    ((Scheme.Modules.pushforward V.ι).obj
      ((depthOneQuotient X T hT F).restrict V.ι)).IsCoherent := by
  have := isCoherent_restrict_depthOneQuotient X T hT V F
  refine isCoherent_pushforward_of_locallyHasDualizingComplex V.ι hdual _ ?_
  intro x z hz himm
  have hxT := image_notMem_of_hV hV x
  have hzT := mem_of_notMem_range_ι hV hz
  have heq := depth_stalk_eq_of_isIso_stalkMap (toDepthOneQuotient X T hT F) (V.ι.base x)
    (isIso_stalkMap_of_isIso_stalkFunctor _ _
      ((depthOneQuotient_spec X T hT F).2.2.1 (V.ι.base x) hxT))
  rw [Scheme.Modules.depth_stalk_restrict V.ι (depthOneQuotient X T hT F) x]
  exact (hdepth (V.ι.base x) z hxT hzT himm).trans heq.le

/-! ### Coherence of the single pushforward from Kollár's criterion -/

/-- **The pushforward of the depth-one quotient from the complement of a closed subset is
coherent.** Let `X` be a Noetherian universally catenary scheme, let `V` be an open of `X` whose
complement is `T`, and let `F` be a coherent module whose depth at a point outside `T` is at
least one as soon as some point of `T` is an immediate specialization of it.  Assume the formal
fibres of `𝒪_{X,z}` satisfy `(S₁)` at every `z ∈ T`.  Then `j_{V,*}(F'|_V)` is coherent, `F'`
being the depth-one quotient of `F` along `T`.

This is Kollár's criterion in the form [Stacks, Tag 0AWB] with its condition verified.  At an
associated point `x` of `F'|_V` the stalk of `F'` has depth zero, so `x ∉ T` and the stalk of `F`
there has depth zero too — the two stalks agree off `T`, and association is detected on stalks by
`Stacks.Algebraization.isAssociatedPoint_iff_of_isIso_stalkFunctor_map`.  The depth hypothesis
then forbids any point of `T` from being an immediate specialization of `x`, so an omitted
specialization `z ∈ T` of `x` is not immediate and
`IrreducibleClosedsCodim.two_le_topCodim_closureSingleton_of_not_isImmediateSpecialization`
bounds the codimension, which is the dimension of `𝒪_{closure {x}, z}` by
`AlgebraicGeometry.ringKrullDim_stalk_vanishingIdeal_closure_eq_topCodim`. -/
public theorem isCoherent_pushforward_restrict_depthOneQuotient_of_formalFibres
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : StableUnderSpecialization T)
    (V : X.Opens) (hV : (V : Set X) = Tᶜ) (F : X.Modules) [F.IsCoherent]
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, z ∈ T → ∀ q : PrimeSpectrum (X.presheaf.stalk z),
      HasSerreCondition
        (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1)
    (hdepth : ∀ x z : X, x ∉ T → z ∈ T → TopologicalSpace.IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    ((Scheme.Modules.pushforward V.ι).obj
      ((depthOneQuotient X T hT F).restrict V.ι)).IsCoherent := by
  have : ((depthOneQuotient X T hT F).restrict V.ι).IsCoherent :=
    isCoherent_restrict_depthOneQuotient X T hT V F
  refine (isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure V.ι hX
    (fun z hz => hFibres z (mem_of_notMem_range_ι hV hz))).mpr ?_
  intro x hx y hy
  have hz0T := image_notMem_of_hV hV x
  have hA' : Stacks.Divisors.IsAssociatedPoint (depthOneQuotient X T hT F) (V.ι.base x) :=
    (Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff V.ι
      (depthOneQuotient X T hT F) x).mp hx
  have hA : Stacks.Divisors.IsAssociatedPoint F (V.ι.base x) :=
    (Stacks.Algebraization.isAssociatedPoint_iff_of_isIso_stalkFunctor_map
      (toDepthOneQuotient X T hT F)
      (V.ι.base x) ((depthOneQuotient_spec X T hT F).2.2.1 (V.ι.base x) hz0T)).mpr hA'
  have hzT : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({V.ι.base x} : Set X))).subschemeι.base y ∈ T := mem_of_notMem_range_ι hV hy
  have hzcl : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({V.ι.base x} : Set X))).subschemeι.base y ∈
        closure ({V.ι.base x} : Set X) := by
    rw [← range_subschemeι_vanishingIdeal_closure (V.ι.base x)]
    exact ⟨y, rfl⟩
  have hspec : V.ι.base x ⤳ (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({V.ι.base x} : Set X))).subschemeι.base y :=
    specializes_iff_mem_closure.mpr hzcl
  have hne : V.ι.base x ≠ (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({V.ι.base x} : Set X))).subschemeι.base y := fun h => hz0T (h ▸ hzT)
  have himm : ¬ TopologicalSpace.IsImmediateSpecialization (V.ι.base x)
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({V.ι.base x} : Set X))).subschemeι.base y) := by
    intro h
    exact Stacks.Divisors.notMem_associatedPoints_of_one_le_depth F (V.ι.base x)
      (hdepth _ _ hz0T hzT h) hA
  rw [ringKrullDim_stalk_vanishingIdeal_closure_eq_topCodim,
    show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe]
  exact IrreducibleClosedsCodim.two_le_topCodim_closureSingleton_of_not_isImmediateSpecialization
    hspec hne himm

/-! ### Tag 0EI3, existence along a closed subset -/

/-- **Stacks Project, Tag 0EI3, existence along a closed subset.** Let `X` be a Noetherian
scheme which locally has a dualizing complex, let `V` be an open of `X` with complement `T` —
so `T` is closed — and let `F` be a coherent `𝒪_X`-module such that `depth(F_x) ≥ 1` whenever
some point of `T` is an immediate specialization of `x ∉ T`.  Then `F` admits a depth-two
extension along `T`.

No hypothesis about extensions or colimits is left: the module is the single pushforward
`j_{V,*}(F'|_V)` of the depth-one quotient, which is a stabilized open extension by
`AlgebraicGeometry.isStabilizedOpenExtension_unit` and coherent by
`isCoherent_pushforward_restrict_depthOneQuotient`.  The two
hypotheses are the source's, and both are necessary.  See the module documentation. -/
@[stacks 0EI3 "existence along a closed subset, with no hypothesis about extensions or \
colimits, and at the source's hypotheses: the dualizing hypothesis and the depth hypothesis on \
immediate specializations, nothing else, the coherence of the single pushforward coming from \
the source's Faltings criterion Tag 0EFD"]
public theorem exists_isDepthTwoExtension_of_locallyHasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (V : X.Opens) (hV : (V : Set X) = Tᶜ)
    (F : X.Modules) [F.IsCoherent]
    (hdual : LocallyHasDualizingComplex X)
    (hdepth : ∀ x z : X, x ∉ T → z ∈ T → TopologicalSpace.IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ := by
  have hTclosed : IsClosed T := isOpen_compl_iff.mp (hV ▸ V.isOpen)
  have := isCoherent_pushforward_restrict_depthOneQuotient X T
    hTclosed.stableUnderSpecialization V hV F hdual hdepth
  have e : (Scheme.Modules.pushforward V.ι).obj
        ((depthOneQuotient X T hTclosed.stableUnderSpecialization F).restrict V.ι) ≅
      (Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.pullback V.ι).obj
        (depthOneQuotient X T hTclosed.stableUnderSpecialization F)) :=
    (Scheme.Modules.pushforward V.ι).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app
        (depthOneQuotient X T hTclosed.stableUnderSpecialization F))
  have hpull : ((Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.pullback V.ι).obj
      (depthOneQuotient X T hTclosed.stableUnderSpecialization F))).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e.symm
  exact exists_isDepthTwoExtension_of_isCoherent_pushforward X T hTclosed V hV F hpull

end AlgebraicGeometry

end
