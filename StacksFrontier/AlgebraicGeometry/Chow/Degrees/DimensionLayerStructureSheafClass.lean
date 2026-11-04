module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleFromCycles
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealFiltration
public import StacksFrontier.AlgebraicGeometry.FullSupport.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The class of a coherent module in a dimension layer is the class of a sum of structure sheaves

Let `(S, δ)` be a base situation with a dimension function, let `X` be a scheme locally of finite
type over `S`, and let `k ∈ ℤ`. Tag 02S9 asserts that the two homomorphisms

`Z_k(X) ⟶ K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` and `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ Z_k(X)`

are mutually inverse. One composite is the identity unconditionally
(`Stacks.Chow.dimensionLayerCycleHom_comp_cycleDimensionLayerHom`); the remaining content is that
for a coherent module `F` of support dimension at most `k` the class of `F` in the layer is the
class of the locally finite direct sum `⨁_ξ 𝒪_{Z_ξ}^{⊕ m_ξ}` attached to the cycle
`[F]_k = ∑ m_ξ [Z_ξ]`. That assertion is
`Stacks.Chow.DimensionLayerClassIsStructureSheafSum`, and it is proved here for a Noetherian
scheme.

It is an assertion about *classes in the Grothendieck group*, not about objects. The stronger
assertion `Stacks.Chow.DimensionLayerIsStructureSheafSum`, that `F` and that direct sum become
isomorphic in the layer, is false: on `X = Spec k[t]` over `S = Spec k` with `δ = dim` and `k = 0`
every nonzero coherent module has support of delta-dimension `0`, so `Coh_{≤-1}(X) = 0` and the
localization functor onto the layer is an equivalence; for `F = 𝒪_X/(t²)` the cycle is `2[(t)]`
and the direct sum is `(𝒪_X/(t))^{⊕2}`, and a module of length two over a discrete valuation ring
is not the square of the residue field. The two classes in `K₀` agree all the same, which is all
the two homomorphisms of Tag 02S9 see.

## Main definitions

* `Stacks.Chow.DimensionLayerClassIsStructureSheafSum` — the assertion that in
  `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` the class of a coherent module of support dimension at most `k`
  is the class of the locally finite direct sum of the structure sheaves of the integral closed
  subschemes of its cycle, taken with multiplicity.
* `Stacks.Chow.DimensionLayerClassMemRange` — the assertion, for a single `𝒪_X`-module, that its
  class in the layer lies in the image of the map `Z_k(X) ⟶ K₀(Coh_{≤k}/Coh_{≤k-1})`.
* `Stacks.Chow.dimLEObj` — a coherent `𝒪_X`-module all of whose support points have relative
  dimension at most `k`, read as an object of `Coh_{≤k}(X)`.
* `Stacks.Chow.cycleDimensionLayerEquiv` — for a Noetherian scheme, the group of `k`-cycles and
  the Grothendieck group of the dimension layer, identified.
* `Stacks.Chow.singlePointCoeff` and `Stacks.Chow.pointCoefficients` — the coefficient function of
  the prime cycle `[closure {ξ}]`.
* `Stacks.Chow.pushforwardUnitIsoIntegralComponent` — the structure sheaf of an integral closed
  subscheme is the structure sheaf of the integral closed subscheme attached to its generic point.

## Main results

* `Stacks.Chow.cycleDimensionLayerHom_dimensionLayerCycle_of_mem_range` — **membership in the
  image is already the inverse identity at `F`**: if the class of `F` in the layer is the image of
  *some* `k`-cycle, that cycle is forced to be `[F]_k`, because the cycle class homomorphism is a
  left inverse of the map from cycles. No multiplicity computation is involved.
* `Stacks.Chow.of_add_of_shortExact`, `Stacks.Chow.of_eq_zero_of_lowerDimensionClass` — the two
  facts that make that membership a dévissage statement: the classes in the layer are additive
  along a short exact sequence of `Coh_{≤k}(X)`, read on the underlying `𝒪_X`-modules, and the
  class of a module of support dimension at most `k - 1` vanishes.
* `Stacks.Chow.dimensionLayerClassMemRange_pushforward_integralIdeal` — the case of the direct
  image `i_*I` of a quasi-coherent sheaf of ideals on an integral closed subscheme `i : Z ⟶ X`.
  Writing `ξ` for the image of the generic point of `Z`: if `ξ` has relative dimension less than
  `k` the whole module lies in `Coh_{≤k-1}(X)` and its class vanishes; otherwise `i_*I ⊆ i_*𝒪_Z`
  has a quotient whose support misses `ξ`, because the stalk of `i_*𝒪_Z` at `ξ` has length one
  while that of `i_*I` is nonzero, so the two classes agree, and `i_*𝒪_Z` is the structure sheaf
  of the integral closed subscheme attached to `ξ`.
* `Stacks.Chow.dimensionLayerClassMemRange_of_isCoherent` — on a Noetherian scheme every coherent
  module has such a class, by the dévissage filtration of Stacks 01YF and the induction of
  Stacks 01YG. Over a scheme merely locally of finite type over the base the same conclusion is
  `Stacks.Chow.dimensionLayerClassMemRange_of_stalkKilled`, for a module killed at every
  top-dimensional point of its support; see "What is not proved".
* `Stacks.Chow.dimensionLayerClassIsStructureSheafSum_of_isNoetherian` — hence the assertion
  itself, for a Noetherian scheme.
* `Stacks.Chow.cycleDimensionLayerHom_dimensionLayerCycle`,
  `Stacks.Chow.cycleDimensionLayerHom_comp_dimensionLayerCycleHom`,
  `Stacks.Chow.surjective_cycleDimensionLayerHom`,
  `Stacks.Chow.bijective_cycleDimensionLayerHom` — **the remaining inverse identity of Tag 02S9
  for a Noetherian scheme**, and the bijectivity of the two maps that follows.
* `Stacks.Chow.classIsStructureSheafSum_of_isStructureSheafSum` — the false object-level assertion
  implies the class-level one, so everything deduced from the latter is also a consequence of the
  former.

## Implementation notes

An object of `Coh_{≤k}(X)` is determined by its underlying `𝒪_X`-module, the coherence and the
dimension bound being propositions; `Stacks.Chow.dimLE_ext` records that, so a statement about
objects of the layer can be made into a statement about `𝒪_X`-modules, which is the shape the
dévissage engine of Stacks 01YG consumes.

The dimension bound on an object of `Coh_{≤k}(X)` is equivalent to the pointwise bound
`relativeDimension ≤ k` on the support, by
`Stacks.Chow.schemeDeltaDimension_reducedSupport_le_iff`, and in that form it is inherited by sub-
and quotient modules from the containment of supports. The bound itself is read off as
`(Stacks.Chow.dimLEObj C f k M hc h).property`, which carries the coherence witness it was built
from and therefore needs no instance to be found again.

Short exactness is transported between `Coh_{≤k}(X)` and all `𝒪_X`-modules along the two
inclusions, which are fully faithful: forwards by exactness of the inclusion of a Serre
subcategory, backwards by `CategoryTheory.ShortExact.reflects_shortExact_of_faithful`.

The comparison of `i_*𝒪_Z` with the structure sheaf of the integral closed subscheme attached to
`ξ` goes through the ideal sheaves: `Scheme.Hom.ker i` has support the closure of `ξ`, and its
subscheme is reduced because it is isomorphic to the integral scheme `Z`, so
`Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme` identifies it with
`Stacks.Chow.integralComponentAt ξ`; the two closed immersions with equal ideal sheaf differ by an
isomorphism, along which the structure sheaf is carried to the structure sheaf.

## What is not proved

`Stacks.Chow.DimensionLayerClassIsStructureSheafSum` is proved here only for a Noetherian
scheme, and the five declarations of this file that register Tag 02S9 carry `[IsNoetherian X]`
accordingly: that is an *added hypothesis*, since the tag asks only that `X` be locally of finite
type over the base. Over such a scheme the filtration of Stacks 01YF is unavailable, and the
source argues instead with the locally finite direct sum `⨁_{p ≥ 0} F^p` of the terms of a
filtration spread out from the stalks at the generic points of the support.

**All but one step of that argument is proved, with no Noetherian hypothesis.**

* `Stacks.Chow.of_eq_natCoproduct_cokernel_of_filtration`, in
  `StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTelescope`, is the telescope: for a
  decreasing sequence of coherent modules with locally finite supports of delta-dimension at most
  `k`, the class of the zeroth term is the class of the direct sum of the successive quotients.
* `Stacks.Chow.of_eq_natCoproduct_adicGraded`, in
  `StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerAdicFiltration`, feeds the ideal-adic
  filtration `F ⊇ J·F ⊇ J²·F ⊇ …` of the ideal sheaf `J` of the support into it and concludes
  `[F] = [⨁_{p ≥ 0} J^p·F / J^{p+1}·F]`.
* `Stacks.Chow.exists_free_comparison_near_genericPoint`, in
  `StacksFrontier.AlgebraicGeometry.Chow.Degrees.GenericFreeComparison`, is **Stacks 01YE over a
  locally Noetherian scheme**: the source's choice of a power of an ideal sheaf needs one
  exponent valid over the whole of `Z`, hence `Z` quasi-compact, and is replaced by Stacks 0FD0,
  which holds over a locally Noetherian scheme. The two comparison maps it produces are not
  claimed to be monomorphisms, which the dévissage of a layer does not need.
* `Stacks.Chow.dimensionLayerClassMemRange_of_stalkKilled`, in
  `StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerGenericDevissage`, is the dévissage
  itself: **a coherent module whose stalk at every point of delta-dimension `k` in its support is
  annihilated by the maximal ideal there has its class in the image of `Z_k(X) → K₀`**, over a
  scheme merely locally of finite type over the base. The locally finite direct sums of the
  comparison modules and of the structure sheaves are assembled, and the two induced morphisms
  are invertible near every point of delta-dimension `k` because near such a point only one
  summand survives (`Stacks.Chow.exists_isIso_restrict_sigmaι`); their kernels and cokernels
  therefore lie in `Coh_{≤k-1}(X)`.

**What is left is one implication.** The graded pieces of the ideal-adic filtration are annihilated
by `J`, with no quasi-compactness (`smul_top_cokernel_idealPowStep_of_isLocallyNoetherian` in
`Stacks.AlgebraicGeometry.IrreducibleDevissage`), so their direct sum is annihilated by `J` as
well. Turning that into the hypothesis of `Stacks.Chow.dimensionLayerClassMemRange_of_stalkKilled`
needs the stalk of `J` at a point `ξ` of delta-dimension `k` of `supp F` to be the *whole* maximal
ideal of `𝒪_{X, ξ}` — equivalently that the local ring at `ξ` of the reduced induced structure on
`supp F` is a field, which it is, `ξ` being the generic point of an irreducible component of a
reduced scheme. The field statement itself is available as
`AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents`; what is absent is the
identification of the stalk of the ideal sheaf of a closed subscheme with the kernel of the stalk
map of its closed immersion, which is what carries a section-level annihilation to a germ-level
one. For that reason the five declarations below carry the Noetherian hypothesis.

## References

* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Two facts about zero objects and cokernels -/

/-- A monomorphism together with its cokernel projection is a short exact sequence. -/
theorem shortExact_mk_cokernel {D : Type*} [Category D] [Abelian D] {A B : D} (u : A ⟶ B)
    [Mono u] : (ShortComplex.mk u (cokernel.π u) (cokernel.condition u)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel u)
  mono_f := inferInstance
  epi_g := inferInstance

/-! ### Supports along monomorphisms and epimorphisms -/

variable {X : Scheme.{u}}

/-- **A monomorphism of `𝒪_X`-modules does not enlarge the support.** A monomorphism of sheaves of
modules is injective on every stalk, so a nonzero element of a stalk of the source gives a nonzero
element of the corresponding stalk of the target. -/
theorem supp_subset_of_mono {F G : X.Modules} (u : F ⟶ G) [Mono u] :
    SheafOfModules.supp F ⊆ SheafOfModules.supp G := by
  have hm : @Mono (_root_.SheafOfModules.{u} X.ringCatSheaf) inferInstance F G u :=
    ⟨fun g h hcomp => (‹Mono u›).right_cancellation g h hcomp⟩
  have hms : Mono ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map u) :=
    CategoryTheory.preserves_mono_of_preservesLimit
      (_root_.SheafOfModules.toSheaf X.ringCatSheaf) u
  have hst := (TopCat.Presheaf.mono_iff_stalk_mono
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map u)).mp hms
  intro x hx
  obtain ⟨a, ha⟩ := hx
  refine ⟨((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map u).hom) a, fun hz => ha ?_⟩
  exact ((AddCommGrpCat.mono_iff_injective _).mp (hst x)) (hz.trans (map_zero _).symm)

/-- An epimorphism of `𝒪_X`-modules is surjective on every stalk: an epimorphism of sheaves of
modules is locally surjective on the underlying abelian sheaves, which is surjectivity on
stalks. -/
private theorem epi_stalk_surjective {F G : X.Modules} (u : F ⟶ G) [Epi u] (x : X) :
    Function.Surjective (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf u))) := by
  have hloc : Presheaf.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of X))
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map u).hom :=
    @_root_.SheafOfModules.isLocallySurjective_toSheaf_of_epi (Opens (TopCat.of X)) _
      (Opens.grothendieckTopology (TopCat.of X)) X.ringCatSheaf _ _ F G u ‹Epi u›
  exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mp hloc x

/-- **An epimorphism of `𝒪_X`-modules does not enlarge the support.** It is surjective on every
stalk, so a stalk of the target is a quotient of the corresponding stalk of the source and is zero
as soon as that one is. -/
theorem supp_subset_of_epi {F G : X.Modules} (u : F ⟶ G) [Epi u] :
    SheafOfModules.supp G ⊆ SheafOfModules.supp F := by
  intro x hx
  have hG : Nontrivial (G.presheaf.stalk x) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk G x).mp hx
  by_contra hF
  have hF' : ¬ Nontrivial (F.presheaf.stalk x) := fun h =>
    hF ((SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mpr h)
  have hFsub : Subsingleton (F.presheaf.stalk x) := not_nontrivial_iff_subsingleton.mp hF'
  have hsurj := epi_stalk_surjective u x
  have hGsub : Subsingleton (G.presheaf.stalk x) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨c, hc⟩ := hsurj (a - b)
    have hc0 : c = 0 := hFsub.elim c 0
    rw [hc0] at hc
    have hdiff : (0 : G.presheaf.stalk x) = a - b := by
      rw [← hc]
      exact (map_zero _).symm
    exact sub_eq_zero.mp hdiff.symm
  exact (not_nontrivial_iff_subsingleton.mpr hGsub) hG

/-- **The support of a direct image along a closed immersion.** A point `i z` lies in the support
of `i_*M` exactly when `z` lies in the support of `M`: the stalk of `i_*M` at `i z` is the stalk
of `M` at `z`, the underlying map of a closed immersion being an embedding. -/
theorem mem_supp_pushforward_iff {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Z.Modules) (z : Z) :
    i z ∈ SheafOfModules.supp ((Scheme.Modules.pushforward i).obj M) ↔
      z ∈ SheafOfModules.supp M := by
  have hi : Topology.IsInducing (ConcreteCategory.hom i.base) :=
    (IsClosedImmersion.isClosedEmbedding i).isInducing
  have hbij := bijective_stalkPushforwardComparison i M z hi
  constructor
  · intro hx
    obtain ⟨a, b, hab⟩ :=
      (SheafOfModules.mem_supp_iff_nontrivial_stalk
        ((Scheme.Modules.pushforward i).obj M) (i z)).mp hx
    refine (SheafOfModules.mem_supp_iff_nontrivial_stalk M z).mpr
      ⟨stalkPushforwardComparison i M z a, stalkPushforwardComparison i M z b, ?_⟩
    exact fun h => hab (hbij.1 h)
  · intro hz
    obtain ⟨a, b, hab⟩ := (SheafOfModules.mem_supp_iff_nontrivial_stalk M z).mp hz
    obtain ⟨a', rfl⟩ := hbij.2 a
    obtain ⟨b', rfl⟩ := hbij.2 b
    exact (SheafOfModules.mem_supp_iff_nontrivial_stalk
      ((Scheme.Modules.pushforward i).obj M) (i z)).mpr ⟨a', b', fun h => hab (by rw [h])⟩

/-! ### The structure sheaf of an integral closed subscheme -/

/-- The comparison map from the structure sheaf of the target to the direct image of the structure
sheaf of the source is an isomorphism for an isomorphism of schemes: it is an isomorphism on
sections over every open. -/
theorem isIso_unitToPushforwardObjUnit_of_isIso {Z W : Scheme.{u}} (e : Z ⟶ W) [IsIso e] :
    IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  show IsIso (((forget₂ CommRingCat RingCat) ⋙ forget₂ RingCat Ab).map (e.app U))
  infer_instance

/-- **The direct image of the structure sheaf along an isomorphism of schemes is the structure
sheaf.** -/
def pushforwardUnitIsoOfIsIso {Z W : Scheme.{u}} (e : Z ⟶ W) [IsIso e] :
    (Scheme.Modules.pushforward e).obj (Stacks.Ample.unitModule Z) ≅
      Stacks.Ample.unitModule W :=
  have := isIso_unitToPushforwardObjUnit_of_isIso e
  (asIso (_root_.SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom)).symm

/-- The range of a closed immersion with integral source is the closure of the image of the
generic point: a closed embedding carries the closure of a set to the closure of its image. -/
theorem range_eq_closure_singleton {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] : Set.range (ConcreteCategory.hom i.base) = closure {i (genericPoint Z)} := by
  have hgen : closure ({genericPoint Z} : Set Z) = Set.univ := genericPoint_spec Z
  have hce := (IsClosedImmersion.isClosedEmbedding i)
  calc Set.range (ConcreteCategory.hom i.base)
      = ConcreteCategory.hom i.base '' Set.univ := by rw [Set.image_univ]
    _ = ConcreteCategory.hom i.base '' closure ({genericPoint Z} : Set Z) := by rw [hgen]
    _ = closure (ConcreteCategory.hom i.base '' ({genericPoint Z} : Set Z)) :=
        (hce.closure_image_eq _).symm
    _ = closure {i (genericPoint Z)} := by rw [Set.image_singleton]

/-- **Stacks 01J3 for an integral closed subscheme.** The ideal sheaf of a closed immersion with
integral source is the vanishing ideal of the closure of the image of the generic point: its
support is that closure, and its subscheme is reduced, being isomorphic to the integral scheme
`Z`. -/
@[sga "6 X 1.1.2" "partial"]
theorem ker_eq_integralComponentAt {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] : i.ker = integralComponentAt (i (genericPoint Z)) := by
  have hsupp : i.ker.support = Closeds.closure ({i (genericPoint Z)} : Set X) := by
    refine Closeds.ext ?_
    rw [Scheme.Hom.support_ker, range_eq_closure_singleton i]
    exact closure_closure
  have : IsIntegral i.image := IsIntegral.of_isIso i.toImage
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme i.ker _ hsupp

/-- **The structure sheaf of an integral closed subscheme is the structure sheaf of the integral
closed subscheme attached to its generic point.** The two closed immersions have the same ideal
sheaf, hence differ by an isomorphism of schemes over `X`, along which the structure sheaf is
carried to the structure sheaf. -/
def pushforwardUnitIsoIntegralComponent {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] :
    (Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z) ≅
      integralComponentStructureSheaf (i (genericPoint Z)) :=
  have hker : (integralComponentAt (i (genericPoint Z))).subschemeι.ker = i.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ker_eq_integralComponentAt i]
  have hfac := IsClosedImmersion.lift_fac
    (integralComponentAt (i (genericPoint Z))).subschemeι i hker.le
  have : IsIso (IsClosedImmersion.lift
    (integralComponentAt (i (genericPoint Z))).subschemeι i hker.le) :=
    IsClosedImmersion.isIso_lift _ _ hker
  ((Scheme.Modules.pushforwardCongr hfac).symm.app (Stacks.Ample.unitModule Z)) ≪≫
    (Scheme.Modules.pushforwardComp _ _).symm.app (Stacks.Ample.unitModule Z) ≪≫
      (Scheme.Modules.pushforward
          (integralComponentAt (i (genericPoint Z))).subschemeι).mapIso
        (pushforwardUnitIsoOfIsIso _)

/-! ### Relative dimension along a specialization -/

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-- **Stacks 02JW.** The relative dimension drops strictly along a nontrivial specialization, it
being the underlying function of a dimension function on `X`. -/
theorem relativeDimension_lt_of_mem_closure_of_ne {x y : X} (hmem : y ∈ closure {x})
    (hne : y ≠ x) :
    relativeDimension C.dimensionFunction f y < relativeDimension C.dimensionFunction f x := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
    C.dimensionFunction f
  have hlt := d.strictAnti_specializes ((isGenericPoint_closure (x := x)).specializes hmem)
    (Ne.symm hne)
  rw [hd, hd] at hlt
  exact hlt

/-- The relative dimension is monotone along a specialization. -/
theorem relativeDimension_le_of_mem_closure {x y : X} (hmem : y ∈ closure {x}) :
    relativeDimension C.dimensionFunction f y ≤ relativeDimension C.dimensionFunction f x := by
  by_cases h : y = x
  · exact h ▸ le_rfl
  · exact (relativeDimension_lt_of_mem_closure_of_ne C f hmem h).le

/-! ### Objects of a dimension layer -/

variable (k : ℤ)

/-- A coherent `𝒪_X`-module every point of whose support has relative dimension at most `k`, read
as an object of `Coh_{≤k}(X)`. -/
def dimLEObj (M : X.Modules) (hc : _root_.SheafOfModules.IsCoherent M)
    (h : ∀ x ∈ SheafOfModules.supp M, relativeDimension C.dimensionFunction f x ≤ k) :
    CoherentModulesDimLE C f k :=
  ⟨⟨M, AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hc⟩,
    letI := hc
    schemeDeltaDimension_reducedSupport_le C f M h⟩

/-- The underlying `𝒪_X`-module of the object of `Coh_{≤k}(X)` attached to a coherent module is
that module. -/
@[simp]
theorem dimLEObj_obj_obj (M : X.Modules) (hc : _root_.SheafOfModules.IsCoherent M)
    (h : ∀ x ∈ SheafOfModules.supp M, relativeDimension C.dimensionFunction f x ≤ k) :
    (dimLEObj C f k M hc h).obj.obj = M :=
  rfl

/-- An object of `Coh_{≤k}(X)` is determined by its underlying `𝒪_X`-module, coherence and the
bound on the delta-dimension of the support being propositions. -/
theorem dimLE_ext {A B : CoherentModulesDimLE C f k} (h : A.obj.obj = B.obj.obj) : A = B := by
  obtain ⟨⟨MA, hA⟩, hA'⟩ := A
  obtain ⟨⟨MB, hB⟩, hB'⟩ := B
  cases h
  rfl

/-- The underlying `𝒪_X`-module of an object of `Coh_{≤k}(X)` is coherent. -/
private theorem isCoherent_obj_obj (A : CoherentModulesDimLE C f k) :
    _root_.SheafOfModules.IsCoherent A.obj.obj :=
  AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent A.obj.property

/-- Every point of the support of an object of `Coh_{≤k}(X)` has relative dimension at most
`k`. -/
theorem relativeDimension_le_of_mem_supp_dimLE (A : CoherentModulesDimLE C f k) :
    ∀ x ∈ SheafOfModules.supp A.obj.obj, relativeDimension C.dimensionFunction f x ≤ k := by
  intro x hx
  have := isCoherent_obj_obj C f k A
  exact relativeDimension_le_of_mem_supp C f A.obj.obj A.property hx

/-! ### Classes in the Grothendieck group of a dimension layer -/

/-- An object of `Coh_{≤k}(X)` with zero underlying `𝒪_X`-module has zero class in
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`: the inclusion into all `𝒪_X`-modules is fully faithful, so the
object itself is a zero object, and the localization functor preserves zero morphisms. -/
theorem of_eq_zero_of_isZero_obj (A : CoherentModulesDimLE C f k) (h : IsZero A.obj.obj) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj A) = 0 :=
  GrothendieckGroup.of_eq_zero_of_isZero (Functor.map_isZero _
    (IsZero.of_full_of_faithful_of_isZero ((coherentModulesDimLE C f k).ι ⋙
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι) A h))

/-- An object of `Coh_{≤k}(X)` whose support has delta-dimension at most `k - 1` has zero class in
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`: the localization functor at a Serre class kills exactly the
objects of that class. -/
theorem of_eq_zero_of_lowerDimensionClass (A : CoherentModulesDimLE C f k)
    (h : lowerDimensionClass C f (k - 1) k A) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj A) = 0 :=
  GrothendieckGroup.of_eq_zero_of_isZero
    ((ObjectProperty.SerreClassLocalization.isZero_obj_iff
      (lowerDimensionClass C f (k - 1) k).isoModSerre.Q
      (lowerDimensionClass C f (k - 1) k) A).2 h)

/-- Two objects of `Coh_{≤k}(X)` with isomorphic underlying `𝒪_X`-modules have the same class in
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`. -/
theorem of_eq_of_module_iso (A B : CoherentModulesDimLE C f k) (e : A.obj.obj ≅ B.obj.obj) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj A) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj B) :=
  GrothendieckGroup.of_eq_of_iso
    (((lowerDimensionClass C f (k - 1) k).isoModSerre.Q).mapIso (dimLEIsoOfModuleIso C f k A B e))

/-- The short exact sequence of `Coh_{≤k}(X)` underlying a short exact sequence of `𝒪_X`-modules
whose three terms are objects of `Coh_{≤k}(X)`: the inclusion into all `𝒪_X`-modules is fully
faithful, so it reflects short exactness. -/
private theorem shortExact_preimage (A₁ A₂ A₃ : CoherentModulesDimLE C f k)
    (u : A₁.obj.obj ⟶ A₂.obj.obj) (v : A₂.obj.obj ⟶ A₃.obj.obj) (w : u ≫ v = 0)
    (hS : (ShortComplex.mk u v w).ShortExact) :
    ∃ (u' : A₁ ⟶ A₂) (v' : A₂ ⟶ A₃) (w' : u' ≫ v' = 0),
      (ShortComplex.mk u' v' w').ShortExact := by
  have FF : ((coherentModulesDimLE C f k).ι ⋙
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι).FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)
  have hu := FF.map_preimage u
  have hv := FF.map_preimage v
  have w' : FF.preimage u ≫ FF.preimage v = 0 := by
    refine FF.map_injective ?_
    rw [CategoryTheory.Functor.map_comp, hu, hv, w, CategoryTheory.Functor.map_zero]
  have e : (ShortComplex.mk (FF.preimage u) (FF.preimage v) w').map
      ((coherentModulesDimLE C f k).ι ⋙
        (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι) ≅
      ShortComplex.mk u v w :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simpa using hu.symm)
      (by simpa using hv.symm)
  exact ⟨FF.preimage u, FF.preimage v, w',
    CategoryTheory.ShortExact.reflects_shortExact_of_faithful _
      (ShortComplex.shortExact_of_iso e.symm hS)⟩

/-- **Additivity of the classes in a dimension layer, read on the underlying `𝒪_X`-modules.** A
short exact sequence of `𝒪_X`-modules whose three terms are objects of `Coh_{≤k}(X)` is a short
exact sequence of `Coh_{≤k}(X)`, and the localization functor onto the layer carries it to a short
exact sequence. -/
theorem of_add_of_shortExact (A₁ A₂ A₃ : CoherentModulesDimLE C f k)
    (u : A₁.obj.obj ⟶ A₂.obj.obj) (v : A₂.obj.obj ⟶ A₃.obj.obj) (w : u ≫ v = 0)
    (hS : (ShortComplex.mk u v w).ShortExact) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj A₂) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj A₁) +
        GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj A₃) := by
  obtain ⟨u', v', w', hT⟩ := shortExact_preimage C f k A₁ A₂ A₃ u v w hS
  exact GrothendieckGroup.additivity (shortExact_map_q_lowerDimensionClass C f k hT)

/-- **Stacks 02QZ on a dimension layer, read on the underlying `𝒪_X`-modules.** The cycle class is
additive along a short exact sequence of `𝒪_X`-modules whose three terms are objects of
`Coh_{≤k}(X)`. -/
theorem dimensionLayerCycle_add_of_shortExact (A₁ A₂ A₃ : CoherentModulesDimLE C f k)
    (u : A₁.obj.obj ⟶ A₂.obj.obj) (v : A₂.obj.obj ⟶ A₃.obj.obj) (w : u ≫ v = 0)
    (hS : (ShortComplex.mk u v w).ShortExact) :
    dimensionLayerCycle C f k A₂ =
      dimensionLayerCycle C f k A₁ + dimensionLayerCycle C f k A₃ := by
  obtain ⟨u', v', w', hT⟩ := shortExact_preimage C f k A₁ A₂ A₃ u v w hS
  exact dimensionLayerCycle_add C f k hT

/-- **Stacks 02QX (2).** At a point of relative dimension `k` the coefficient of the cycle of an
object of `Coh_{≤k}(X)` is the length of the stalk there. -/
theorem dimensionLayerCycle_apply_of_relativeDimension_eq (A : CoherentModulesDimLE C f k)
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k) :
    (dimensionLayerCycle C f k A).1 x = sheafMultiplicity A.obj.obj x := by
  have := isCoherent_obj_obj C f k A
  exact cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f A.obj.obj k A.property hx

/-- At a point of relative dimension `k` the stalk of a coherent `𝒪_X`-module whose support has
relative dimension at most `k` everywhere has finite length over the local ring there. -/
theorem isFiniteLength_stalk_of_forall_relativeDimension_le (M : X.Modules)
    (hc : _root_.SheafOfModules.IsCoherent M)
    (h : ∀ y ∈ SheafOfModules.supp M, relativeDimension C.dimensionFunction f y ≤ k) {x : X}
    (hx : relativeDimension C.dimensionFunction f x = k) :
    IsFiniteLength (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  let := hc
  isFiniteLength_stalk_of_relativeDimension_eq C f M
    (schemeDeltaDimension_reducedSupport_le C f M h) hx

/-! ### The coefficient function of a prime cycle -/

section SinglePointCoeff

variable {Y : Type*}

/-- The coefficient function of the prime cycle `[closure {ξ}]`: the value one at `ξ` and zero
elsewhere. -/
def singlePointCoeff (ξ : Y) : Y → ℕ :=
  @Function.update Y _ (Classical.decEq Y) 0 ξ 1

/-- The value of `Stacks.Chow.singlePointCoeff` at the point it is concentrated at. -/
@[simp]
theorem singlePointCoeff_self (ξ : Y) : singlePointCoeff ξ ξ = 1 := by
  classical simp [singlePointCoeff]

/-- The value of `Stacks.Chow.singlePointCoeff` at any other point. -/
theorem singlePointCoeff_of_ne {ξ x : Y} (h : x ≠ ξ) : singlePointCoeff ξ x = 0 := by
  classical simp [singlePointCoeff, h]

/-- A point carrying a nonzero value of `Stacks.Chow.singlePointCoeff` is the point it is
concentrated at. -/
theorem eq_of_singlePointCoeff_ne_zero {ξ x : Y} (h : singlePointCoeff ξ x ≠ 0) : x = ξ := by
  by_contra hne
  exact h (singlePointCoeff_of_ne hne)

/-- The index type of the direct sum attached to `Stacks.Chow.singlePointCoeff` has exactly one
element, namely the unique index lying over the point it is concentrated at. -/
instance uniqueSigmaFinSinglePointCoeff (ξ : Y) :
    Unique (Σ x : Y, Fin (singlePointCoeff ξ x)) where
  default := ⟨ξ, ⟨0, by rw [singlePointCoeff_self]; omega⟩⟩
  uniq := by
    rintro ⟨x, m⟩
    have hm : (m : ℕ) < singlePointCoeff ξ x := m.isLt
    have hx : singlePointCoeff ξ x ≠ 0 := by omega
    obtain rfl : x = ξ := eq_of_singlePointCoeff_ne_zero hx
    have h1 : singlePointCoeff x x = 1 := singlePointCoeff_self x
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Fin.ext_iff]
    omega

end SinglePointCoeff

/-- The coefficient function of the prime cycle `[closure {ξ}]`, as a nonnegative coefficient
function of delta-dimension `k`. -/
def pointCoefficients (ξ : X) (hξ : relativeDimension C.dimensionFunction f ξ = k) :
    DimensionCoefficients C f k :=
  ⟨singlePointCoeff ξ, fun _ => ⟨Set.univ, Filter.univ_mem,
      (Set.finite_singleton ξ).subset fun z hz => eq_of_singlePointCoeff_ne_zero hz.2⟩,
    fun x hx => by rw [eq_of_singlePointCoeff_ne_zero hx]; exact hξ⟩

/-- The locally finite direct sum attached to the coefficient function of a prime cycle is the
structure sheaf of the integral closed subscheme it is concentrated at. -/
def cycleStructureSheafPointIso (ξ : X) :
    cycleStructureSheaf (singlePointCoeff ξ) ≅ integralComponentStructureSheaf ξ :=
  coproductUniqueIso fun i : Σ x : X, Fin (singlePointCoeff ξ x) =>
    integralComponentStructureSheaf i.1

/-- The `k`-cycle with a given nonnegative coefficient function. -/
def dimensionCoefficientsCycle (p : DimensionCoefficients C f k) : CycleGroup C f k := by
  refine ⟨⟨fun x => (p.1 x : ℤ), fun x _ => Set.mem_univ x, fun z _ => ?_⟩, ?_⟩
  · obtain ⟨t, ht, hfin⟩ := p.2.1 z
    refine ⟨t, ht, hfin.subset fun y hy => ⟨hy.1, ?_⟩⟩
    have hy2 : ((p.1 y : ℤ)) ≠ 0 := hy.2
    simpa only [Function.mem_support, ne_eq, Nat.cast_eq_zero] using hy2
  · refine (mem_cyclesOfDimension_iff_forall_point C f k _).2 fun x hx => p.2.2 x ?_
    have hx' : ((p.1 x : ℤ)) ≠ 0 := hx
    simpa only [ne_eq, Nat.cast_eq_zero] using hx'

/-- The class of a locally finite direct sum `⨁_x 𝒪_{closure {x}}^{⊕ n x}` lies in the image of
the map `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9: it is the image of the cycle with
coefficient function `n`, whose negative part vanishes. -/
theorem cycleStructureSheafClass_mem_range (p : DimensionCoefficients C f k) :
    cycleStructureSheafClass C f k p ∈ (cycleDimensionLayerHom C f k).range := by
  refine ⟨dimensionCoefficientsCycle C f k p, ?_⟩
  have hpos : cyclePositivePart C f k (dimensionCoefficientsCycle C f k p) = p := by
    refine DimensionCoefficients.ext C f k ?_
    funext x
    show ((p.1 x : ℤ)).toNat = p.1 x
    omega
  have hneg : (cycleNegativePart C f k (dimensionCoefficientsCycle C f k p)).1 = 0 := by
    funext x
    show (-(p.1 x : ℤ)).toNat = 0
    omega
  rw [cycleDimensionLayerHom_apply]
  show cycleStructureSheafClass C f k (cyclePositivePart C f k _) -
    cycleStructureSheafClass C f k (cycleNegativePart C f k _) = _
  rw [hpos, cycleStructureSheafClass_eq_zero C f k _ hneg, sub_zero]

/-! ### The remaining step of Tag 02S9, at the level of classes -/

/-- **The generic structure of a coherent module in a dimension layer, as an identity of
classes.** The assertion that for every coherent `𝒪_X`-module `F` whose support has
delta-dimension at most `k` the class of `F` in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is the class of
the locally finite direct sum `⨁_ξ 𝒪_{Z_ξ}^{⊕ m_ξ}` of the structure sheaves of the integral
closed subschemes of its cycle `[F]_k = ∑ m_ξ [Z_ξ]`, each repeated with its multiplicity.

This is what the two homomorphisms of Tag 02S9 need, and unlike
`Stacks.Chow.DimensionLayerIsStructureSheafSum` it does not ask for an isomorphism of objects of
the layer, which `F = 𝒪/(t²)` on the affine line already refutes. -/
def DimensionLayerClassIsStructureSheafSum : Prop :=
  ∀ F : CoherentModulesDimLE C f k,
    cycleStructureSheafClass C f k (multiplicityCoefficients C f k F) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F)

/-- The assertion that `F` and the locally finite direct sum of the structure sheaves of the
integral closed subschemes of `[F]_k` become isomorphic in the dimension layer implies that their
classes in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` agree. -/
theorem classIsStructureSheafSum_of_isStructureSheafSum
    (h : DimensionLayerIsStructureSheafSum C f k) :
    DimensionLayerClassIsStructureSheafSum C f k :=
  fun F => GrothendieckGroup.of_eq_of_iso (h F).some

/-- **Membership in the image of the map from cycles is already the inverse identity at `F`.** If
the class of `F` in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is the image of some `k`-cycle under the map
`Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})` of Tag 02S9, that cycle is `[F]_k`: the cycle class
homomorphism is a left inverse of the map from cycles, so applying it to the equation identifies
the cycle. No computation of multiplicities enters. -/
theorem cycleDimensionLayerHom_dimensionLayerCycle_of_mem_range
    (F : CoherentModulesDimLE C f k)
    (h : GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F) ∈
      (cycleDimensionLayerHom C f k).range) :
    cycleDimensionLayerHom C f k (dimensionLayerCycle C f k F) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F) := by
  obtain ⟨c, hc⟩ := h
  have h1 : dimensionLayerCycle C f k F = c := by
    rw [← dimensionLayerCycleHom_of C f k F, ← hc,
      dimensionLayerCycleHom_cycleDimensionLayerHom]
  rw [h1, hc]

/-- The assertion that in a dimension layer the class of a coherent module is the class of a
locally finite direct sum of structure sheaves follows from the weaker statement that the class
lies in the image of the map `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})` at all. -/
theorem dimensionLayerClassIsStructureSheafSum_of_forall_mem_range
    (h : ∀ F : CoherentModulesDimLE C f k,
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F) ∈
        (cycleDimensionLayerHom C f k).range) :
    DimensionLayerClassIsStructureSheafSum C f k := fun F => by
  rw [← cycleDimensionLayerHom_dimensionLayerCycle_eq_cycleStructureSheafClass]
  exact cycleDimensionLayerHom_dimensionLayerCycle_of_mem_range C f k F (h F)

/-! ### The dévissage -/

/-- The assertion, for one `𝒪_X`-module `M`, that whenever `M` is coherent with every point of its
support of relative dimension at most `k` its class in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` lies in the
image of the map `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})` of Tag 02S9. For a module that is not an
object of `Coh_{≤k}(X)` the assertion is empty. -/
def DimensionLayerClassMemRange (M : X.Modules) : Prop :=
  ∀ (hc : _root_.SheafOfModules.IsCoherent M)
    (h : ∀ x ∈ SheafOfModules.supp M, relativeDimension C.dimensionFunction f x ≤ k),
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
      (dimLEObj C f k M hc h)) ∈ (cycleDimensionLayerHom C f k).range

/-- An `𝒪_X`-module which is a zero object has its class in the image, that class being zero. -/
theorem dimensionLayerClassMemRange_of_isZero {M : X.Modules} (h : IsZero M) :
    DimensionLayerClassMemRange C f k M := fun hc hsupp => by
  rw [of_eq_zero_of_isZero_obj C f k (dimLEObj C f k M hc hsupp) h]
  exact zero_mem _

/-- The classes in the image form a subgroup, so the middle term of a short exact sequence of
coherent `𝒪_X`-modules of support dimension at most `k` has its class in the image as soon as the
two outer terms do. -/
theorem dimensionLayerClassMemRange_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (hc₁ : _root_.SheafOfModules.IsCoherent S.X₁)
    (hc₃ : _root_.SheafOfModules.IsCoherent S.X₃)
    (h₁ : DimensionLayerClassMemRange C f k S.X₁)
    (h₃ : DimensionLayerClassMemRange C f k S.X₃) :
    DimensionLayerClassMemRange C f k S.X₂ := by
  intro hc hsupp
  have hm := hS.mono_f
  have he := hS.epi_g
  have hs₁ : ∀ x ∈ SheafOfModules.supp S.X₁,
      relativeDimension C.dimensionFunction f x ≤ k := fun x hx =>
    hsupp x (supp_subset_of_mono S.f hx)
  have hs₃ : ∀ x ∈ SheafOfModules.supp S.X₃,
      relativeDimension C.dimensionFunction f x ≤ k := fun x hx =>
    hsupp x (supp_subset_of_epi S.g hx)
  rw [of_add_of_shortExact C f k (dimLEObj C f k S.X₁ hc₁ hs₁) (dimLEObj C f k S.X₂ hc hsupp)
    (dimLEObj C f k S.X₃ hc₃ hs₃) S.f S.g S.zero hS]
  exact add_mem (h₁ hc₁ hs₁) (h₃ hc₃ hs₃)

/-- **The direct image of a quasi-coherent sheaf of ideals on an integral closed subscheme has its
class in the image of the map from cycles.** Let `i : Z ⟶ X` be a closed immersion with `Z`
integral, let `I ⊆ 𝒪_Z` be a quasi-coherent sheaf of ideals and let `ξ` be the image of the
generic point of `Z`.

If `I` is zero so is `i_*I`. Otherwise the support of `I` is all of `Z`, so `ξ` lies in the
support of `i_*I`, and the support of `i_*I` is contained in the closure of `ξ`. If `ξ` has
relative dimension less than `k`, the whole of that closure has relative dimension at most
`k - 1`, so `i_*I` lies in `Coh_{≤k-1}(X)` and its class vanishes. If `ξ` has relative dimension
`k`, the inclusion `i_*I ⊆ i_*𝒪_Z` has a cokernel whose stalk at `ξ` vanishes: the stalk of
`i_*𝒪_Z` there has length one by Stacks 02QU, that of `i_*I` is nonzero, and the lengths add along
the short exact sequence. The cokernel is therefore supported in the closure of `ξ` minus `ξ`,
which has relative dimension at most `k - 1`, so the classes of `i_*I` and of `i_*𝒪_Z` agree; and
`i_*𝒪_Z` is the structure sheaf of the integral closed subscheme attached to `ξ`, whose class is
the image of the prime cycle `[closure {ξ}]`. -/
theorem dimensionLayerClassMemRange_pushforward_integralIdeal
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : (_root_.SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherent) :
    DimensionLayerClassMemRange C f k
      ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) := by
  have hXN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  by_cases hIz : IsZero I.toSheafOfModules
  · exact dimensionLayerClassMemRange_of_isZero C f k
      (Functor.map_isZero (Scheme.Modules.pushforward i) hIz)
  intro hc hsupp
  have hmonoI : Mono (C := Z.Modules) I.ι :=
    ⟨fun g h hcomp => (_root_.SheafOfModules.Submodule.instMonoι I).right_cancellation g h hcomp⟩
  have hu : Mono ((Scheme.Modules.pushforward i).map I.ι) :=
    CategoryTheory.preserves_mono_of_preservesLimit (Scheme.Modules.pushforward i) I.ι
  have hOc : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) := inferInstance
  have hOsupp : SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) =
      closure {i (genericPoint Z)} := by
    rw [supp_pushforwardStructureSheaf, range_eq_closure_singleton i]
  have hMO : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) ⊆
      SheafOfModules.supp
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) :=
    supp_subset_of_mono ((Scheme.Modules.pushforward i).map I.ι)
  have hηI : genericPoint Z ∈ SheafOfModules.supp I.toSheafOfModules :=
    Stacks.AlgebraicGeometry.Tag01YHFullSupport.genericPoint_mem_supp_of_not_isZero I hI hIz
  have hξM : i (genericPoint Z) ∈
      SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) :=
    (mem_supp_pushforward_iff i _ (genericPoint Z)).mpr hηI
  have hξk : relativeDimension C.dimensionFunction f (i (genericPoint Z)) ≤ k := hsupp _ hξM
  have hcl : ∀ m, relativeDimension C.dimensionFunction f (i (genericPoint Z)) ≤ m →
      ∀ y ∈ SheafOfModules.supp ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)),
        relativeDimension C.dimensionFunction f y ≤ m := by
    intro m hm y hy
    rw [hOsupp] at hy
    exact le_trans (relativeDimension_le_of_mem_closure C f hy) hm
  have hOdim := hcl k hξk
  by_cases hξeq : relativeDimension C.dimensionFunction f (i (genericPoint Z)) = k
  · have hQc : _root_.SheafOfModules.IsCoherent
        (cokernel ((Scheme.Modules.pushforward i).map I.ι)) :=
      Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel_modules hc hOc _
    have hE : (ShortComplex.mk ((Scheme.Modules.pushforward i).map I.ι)
        (cokernel.π ((Scheme.Modules.pushforward i).map I.ι))
        (cokernel.condition _)).ShortExact :=
      shortExact_mk_cokernel ((Scheme.Modules.pushforward i).map I.ι)
    have hepi : Epi (cokernel.π ((Scheme.Modules.pushforward i).map I.ι)) := hE.epi_g
    have hQO : SheafOfModules.supp (cokernel ((Scheme.Modules.pushforward i).map I.ι)) ⊆
        SheafOfModules.supp
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) :=
      @supp_subset_of_epi X _ _ (cokernel.π ((Scheme.Modules.pushforward i).map I.ι)) hepi
    have hQdim0 : ∀ y ∈ SheafOfModules.supp
        (cokernel ((Scheme.Modules.pushforward i).map I.ι)),
        relativeDimension C.dimensionFunction f y ≤ k := fun y hy => hOdim y (hQO hy)
    have hadd := dimensionLayerCycle_add_of_shortExact C f k
      (dimLEObj C f k _ hc hsupp) (dimLEObj C f k _ hOc hOdim)
      (dimLEObj C f k _ hQc hQdim0) ((Scheme.Modules.pushforward i).map I.ι)
      (cokernel.π ((Scheme.Modules.pushforward i).map I.ι)) (cokernel.condition _) hE
    have hmO : sheafMultiplicity
        ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))
        (i (genericPoint Z)) = 1 := by
      have hmem := genericPoint_mem_genericPoints Z
      rw [sheafMultiplicity_pushforwardStructureSheaf i ⟨genericPoint Z, hmem⟩]
      exact componentMultiplicity_eq_one i hmem
    have hcoeff : sheafMultiplicity
          ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))
          (i (genericPoint Z)) =
        sheafMultiplicity ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)
            (i (genericPoint Z)) +
          sheafMultiplicity (cokernel ((Scheme.Modules.pushforward i).map I.ι))
            (i (genericPoint Z)) := by
      have h : (dimensionLayerCycle C f k (dimLEObj C f k _ hOc hOdim)).1
            (i (genericPoint Z)) =
          (dimensionLayerCycle C f k (dimLEObj C f k _ hc hsupp)).1 (i (genericPoint Z)) +
            (dimensionLayerCycle C f k (dimLEObj C f k _ hQc hQdim0)).1
              (i (genericPoint Z)) := by
        rw [hadd]
        rfl
      rw [dimensionLayerCycle_apply_of_relativeDimension_eq C f k _ hξeq,
        dimensionLayerCycle_apply_of_relativeDimension_eq C f k _ hξeq,
        dimensionLayerCycle_apply_of_relativeDimension_eq C f k _ hξeq] at h
      exact h
    have hmMpos := sheafMultiplicity_pos_of_mem_supp
      ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)
      (isFiniteLength_stalk_of_forall_relativeDimension_le C f k _ hc hsupp hξeq) hξM
    have hξQ : i (genericPoint Z) ∉
        SheafOfModules.supp (cokernel ((Scheme.Modules.pushforward i).map I.ι)) := by
      intro hmem
      have hpos := sheafMultiplicity_pos_of_mem_supp
        (cokernel ((Scheme.Modules.pushforward i).map I.ι))
        (isFiniteLength_stalk_of_forall_relativeDimension_le C f k _ hQc hQdim0 hξeq) hmem
      omega
    have hQdim : ∀ y ∈ SheafOfModules.supp
        (cokernel ((Scheme.Modules.pushforward i).map I.ι)),
        relativeDimension C.dimensionFunction f y ≤ k - 1 := by
      intro y hy
      have hyc : y ∈ closure {i (genericPoint Z)} := hOsupp ▸ hQO hy
      have hne : y ≠ i (genericPoint Z) := fun h => hξQ (h ▸ hy)
      have hlt := relativeDimension_lt_of_mem_closure_of_ne C f hyc hne
      omega
    have hsum := of_add_of_shortExact C f k
      (dimLEObj C f k _ hc hsupp) (dimLEObj C f k _ hOc hOdim)
      (dimLEObj C f k _ hQc hQdim0) ((Scheme.Modules.pushforward i).map I.ι)
      (cokernel.π ((Scheme.Modules.pushforward i).map I.ι)) (cokernel.condition _) hE
    have hQzero := of_eq_zero_of_lowerDimensionClass C f k (dimLEObj C f k _ hQc hQdim0)
      (dimLEObj C f (k - 1) _ hQc hQdim).property
    have hiso : (dimLEObj C f k _ hOc hOdim).obj.obj ≅
        (cycleStructureSheafDimLE C f k
          (pointCoefficients C f k (i (genericPoint Z)) hξeq)).obj.obj :=
      pushforwardUnitIsoIntegralComponent i ≪≫
        (cycleStructureSheafPointIso (i (genericPoint Z))).symm
    rw [show GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
        (dimLEObj C f k _ hc hsupp)) =
        GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
          (dimLEObj C f k _ hOc hOdim)) by rw [hsum, hQzero, add_zero],
      of_eq_of_module_iso C f k _ _ hiso]
    exact cycleStructureSheafClass_mem_range C f k _
  · have hlt : relativeDimension C.dimensionFunction f (i (genericPoint Z)) ≤ k - 1 := by omega
    rw [of_eq_zero_of_lowerDimensionClass C f k (dimLEObj C f k _ hc hsupp)
      (dimLEObj C f (k - 1) _ hc fun y hy => hcl (k - 1) hlt y (hMO hy)).property]
    exact zero_mem _

/-- **Stacks 01YG for the classes in a dimension layer.** On a Noetherian scheme the class of
every coherent `𝒪_X`-module of support dimension at most `k` lies in the image of the map
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9: the module carries a dévissage filtration
whose successive quotients are direct images of quasi-coherent sheaves of ideals on integral
closed subschemes by Stacks 01YF, those have their classes in the image, and the classes are
additive along the filtration. -/
theorem dimensionLayerClassMemRange_of_isCoherent [IsNoetherian X] (M : X.Modules)
    (hM : _root_.SheafOfModules.IsCoherent M) : DimensionLayerClassMemRange C f k M :=
  Stacks.AlgebraicGeometry.CoherentDevissage.property_of_forall_hasIdealFiltration
    (DimensionLayerClassMemRange C f k)
    (fun F hF =>
      let := hF
      Stacks.AlgebraicGeometry.CoherentDevissage.hasIdealFiltration X F)
    (dimensionLayerClassMemRange_of_isZero C f k
      Stacks.AlgebraicGeometry.CoherentDevissage.isZero_terminal)
    (fun S hS hc₁ _ hc₃ h₁ h₃ =>
      dimensionLayerClassMemRange_of_shortExact C f k S hS hc₁ hc₃ h₁ h₃)
    (fun {_} i _ _ I hI =>
      dimensionLayerClassMemRange_pushforward_integralIdeal C f k i I hI) M hM

/-- **The generic structure of a coherent module in a dimension layer, for a Noetherian scheme.**
The class of a coherent `𝒪_X`-module `F` whose support has delta-dimension at most `k` in
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is the class of the locally finite direct sum
`⨁_ξ 𝒪_{Z_ξ}^{⊕ m_ξ}` of the structure sheaves of the integral closed subschemes of
`[F]_k = ∑ m_ξ [Z_ξ]`, each repeated with its multiplicity. -/
theorem dimensionLayerClassIsStructureSheafSum_of_isNoetherian [IsNoetherian X] :
    DimensionLayerClassIsStructureSheafSum C f k := by
  refine dimensionLayerClassIsStructureSheafSum_of_forall_mem_range C f k fun F => ?_
  have hc := isCoherent_obj_obj C f k F
  have hsupp := relativeDimension_le_of_mem_supp_dimLE C f k F
  have hF : dimLEObj C f k F.obj.obj hc hsupp = F := dimLE_ext C f k rfl
  have hmem := dimensionLayerClassMemRange_of_isCoherent C f k F.obj.obj hc hc hsupp
  rwa [hF] at hmem

/-! ### The consequences of Tag 02S9 -/

/-- Granting the class-level generic structure of a dimension layer, the class of a coherent
`𝒪_X`-module of support dimension at most `k` in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is the image of
its cycle `[F]_k` under the map `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9. -/
theorem cycleDimensionLayerHom_dimensionLayerCycle_of_classIsStructureSheafSum
    (h : DimensionLayerClassIsStructureSheafSum C f k) (F : CoherentModulesDimLE C f k) :
    cycleDimensionLayerHom C f k (dimensionLayerCycle C f k F) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F) := by
  rw [cycleDimensionLayerHom_dimensionLayerCycle_eq_cycleStructureSheafClass]
  exact h F

/-- Granting the class-level generic structure of a dimension layer, the composite
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of the two maps of
Tag 02S9 is the identity. -/
theorem cycleDimensionLayerHom_comp_dimensionLayerCycleHom_of_classIsStructureSheafSum
    (h : DimensionLayerClassIsStructureSheafSum C f k) :
    (cycleDimensionLayerHom C f k).comp (dimensionLayerCycleHom C f k) = AddMonoidHom.id _ := by
  refine GrothendieckGroup.hom_ext fun Y => ?_
  have e := (lowerDimensionClass C f (k - 1) k).isoModSerre.Q.objObjPreimageIso Y
  rw [← GrothendieckGroup.of_eq_of_iso e, AddMonoidHom.comp_apply, dimensionLayerCycleHom_of,
    AddMonoidHom.id_apply]
  exact cycleDimensionLayerHom_dimensionLayerCycle_of_classIsStructureSheafSum C f k h _

/-- Granting the class-level generic structure of a dimension layer, the map
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of Tag 02S9 is surjective. -/
theorem surjective_cycleDimensionLayerHom_of_classIsStructureSheafSum
    (h : DimensionLayerClassIsStructureSheafSum C f k) :
    Function.Surjective (cycleDimensionLayerHom C f k) := fun x =>
  ⟨dimensionLayerCycleHom C f k x, congrArg
    (fun φ : GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) →+
      GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) => φ x)
    (cycleDimensionLayerHom_comp_dimensionLayerCycleHom_of_classIsStructureSheafSum C f k h)⟩

/-- On a Noetherian scheme, the class of a coherent `𝒪_X`-module `F` of support dimension at most
`k` in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is the image of its cycle `[F]_k` under the map
`Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`. -/
@[stacks 02S9 "`[F] = ∑ m_ξ[Z_ξ]` in `K₀(Coh_{≤k}/Coh_{≤k-1})`, for `X` Noetherian"]
theorem cycleDimensionLayerHom_dimensionLayerCycle [IsNoetherian X]
    (F : CoherentModulesDimLE C f k) :
    cycleDimensionLayerHom C f k (dimensionLayerCycle C f k F) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj F) :=
  cycleDimensionLayerHom_dimensionLayerCycle_of_classIsStructureSheafSum C f k
    (dimensionLayerClassIsStructureSheafSum_of_isNoetherian C f k) F

/-- On a Noetherian scheme, the composite
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) → Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` of the cycle map and
the cycle class map is the identity. -/
@[stacks 02S9 "`K₀(Coh_{≤k}/Coh_{≤k-1}) → Z_k(X) → K₀` is the identity, for `X` Noetherian"]
theorem cycleDimensionLayerHom_comp_dimensionLayerCycleHom [IsNoetherian X] :
    (cycleDimensionLayerHom C f k).comp (dimensionLayerCycleHom C f k) = AddMonoidHom.id _ :=
  cycleDimensionLayerHom_comp_dimensionLayerCycleHom_of_classIsStructureSheafSum C f k
    (dimensionLayerClassIsStructureSheafSum_of_isNoetherian C f k)

/-- On a Noetherian scheme, the map `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is surjective. -/
@[stacks 02S9 "surjectivity of `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})`, for `X` Noetherian"]
theorem surjective_cycleDimensionLayerHom [IsNoetherian X] :
    Function.Surjective (cycleDimensionLayerHom C f k) :=
  surjective_cycleDimensionLayerHom_of_classIsStructureSheafSum C f k
    (dimensionLayerClassIsStructureSheafSum_of_isNoetherian C f k)

/-- On a Noetherian scheme, the map `Z_k(X) → K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is bijective, the
cycle class homomorphism being a two-sided inverse. -/
@[stacks 02S9 "bijectivity of `Z_k(X) → K₀(Coh_{≤k}/Coh_{≤k-1})`, for `X` Noetherian"]
theorem bijective_cycleDimensionLayerHom [IsNoetherian X] :
    Function.Bijective (cycleDimensionLayerHom C f k) :=
  ⟨injective_cycleDimensionLayerHom C f k, surjective_cycleDimensionLayerHom C f k⟩

/-- On a Noetherian scheme `X`, the group of `k`-cycles on `X` is the Grothendieck
group of the dimension layer `Coh_{≤k}(X)/Coh_{≤k-1}(X)`, by the two mutually inverse
homomorphisms `∑ n_Z[Z] ↦ [⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]` and
`F ↦ [F]_k`. -/
@[stacks 02S9 "`Z_k(X) ≃ K₀(Coh_{≤k}/Coh_{≤k-1})`, for `X` Noetherian"]
def cycleDimensionLayerEquiv [IsNoetherian X] :
    CycleGroup C f k ≃+ GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) :=
  AddEquiv.ofBijective (cycleDimensionLayerHom C f k) (bijective_cycleDimensionLayerHom C f k)

/-- On a Noetherian scheme, the identification of the group of `k`-cycles with the Grothendieck
group of the dimension layer sends a cycle `∑ n_Z[Z]` to
`[⨁_{n_Z > 0} 𝒪_Z^{⊕n_Z}] - [⨁_{n_Z < 0} 𝒪_Z^{⊕-n_Z}]`. -/
@[simp, stacks 02S9 "the formula for `Z_k(X) ≃ K₀(Coh_{≤k}/Coh_{≤k-1})`, for `X` Noetherian"]
theorem cycleDimensionLayerEquiv_apply [IsNoetherian X] (c : CycleGroup C f k) :
    cycleDimensionLayerEquiv C f k c = cycleDimensionLayerHom C f k c :=
  rfl

/-- On a Noetherian scheme, the inverse of the identification of the group of `k`-cycles with the
Grothendieck group of the dimension layer sends the class of a coherent module `F` to the cycle
`[F]_k`. -/
@[simp, stacks 02S9 "the inverse formula for `Z_k(X) ≃ K₀`, for `X` Noetherian"]
theorem cycleDimensionLayerEquiv_symm_apply [IsNoetherian X]
    (x : GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k)) :
    (cycleDimensionLayerEquiv C f k).symm x = dimensionLayerCycleHom C f k x := by
  refine (cycleDimensionLayerEquiv C f k).injective ?_
  rw [AddEquiv.apply_symm_apply, cycleDimensionLayerEquiv_apply]
  exact (congrArg
    (fun φ : GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) →+
      GrothendieckGroup (coherentDimensionQuotient C f (k - 1) k) => φ x)
    (cycleDimensionLayerHom_comp_dimensionLayerCycleHom C f k)).symm

end Stacks.Chow

end
