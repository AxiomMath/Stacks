module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorBaseChangeGermSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorChartPointNeighborhood
public import StacksFrontier.RingTheory.FaithfullyFlatFractionUnit

/-!
# The order of vanishing of the chart ratio

Let `X` be a normal, locally Noetherian, integral, decent algebraic space over a scheme `S`, let
`ℒ` be an invertible `𝒪_X`-module free on `e` over an étale chart `V` of `X` with integral affine
scheme, and let `t` be a meromorphic section of `ℒ` whose canonical ratio at the generic point of
**every** prime divisor of `X` is the image of a unit of the henselian local ring there — the
hypothesis of Stacks 0EPX. Then the ratio `t / e`, read as a rational function of
`chartScheme V`, has **order of vanishing zero at every coheight-one point** of that scheme.

## Main results

* `AlgebraicGeometry.Space.ord_chartRatio_eq_zero_of_forall_isUnit_canonicalGenericRatio`: the
  ratio `t / e` has order of vanishing zero at every coheight-one point of `chartScheme V`.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Order
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] nonempty_top_chartScheme
attribute [local instance] chartMeromorphicFunctionAlgebra chartFunctionFieldAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (hdec : IsDecentSpace B S hS X.1)
    (hInt : IsIntegralSpace B S hS X.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- A ring map `A → D` carrying nonzerodivisors to nonzerodivisors extends to a ring map from any
fraction ring `K` of `A` to the fraction ring of `D`. -/
private theorem exists_ringHom_fractionRing_of_map_nonZeroDivisors {A D K : Type*} [CommRing A]
    [CommRing D] [CommRing K] [Algebra A K] [IsFractionRing A K] (f : A →+* D)
    (hf : ∀ y ∈ A⁰, f y ∈ D⁰) :
    ∃ g : K →+* FractionRing D, ∀ r : A,
      g (algebraMap A K r) = algebraMap D (FractionRing D) (f r) := by
  have hu : ∀ y : A⁰, IsUnit (((algebraMap D (FractionRing D)).comp f) (y : A)) := fun y ↦
    IsLocalization.map_units (M := D⁰) (FractionRing D) ⟨_, hf y y.2⟩
  exact ⟨IsLocalization.lift hu, fun r ↦ IsLocalization.lift_eq hu r⟩

/-- On a normal, locally Noetherian, integral, decent algebraic space `X`, let `ℒ` be an invertible
`𝒪_X`-module free on `e` over an étale chart `V` with integral affine scheme and let `t` be a
meromorphic section of `ℒ` whose canonical ratio at the generic point of every prime divisor is
the image of a unit of the henselian local ring there — the hypothesis of Stacks 0EPX. Then the
ratio `t / e`, read as a rational function of `chartScheme V` by
`AlgebraicGeometry.Space.chartMeromorphicFunctionFieldEquiv`, has order of vanishing zero at
every coheight-one point of `chartScheme V`. -/
theorem ord_chartRatio_eq_zero_of_forall_isUnit_canonicalGenericRatio
    (hNormal : IsNormal B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule (B := B) X L)
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (V : SmallEtale B S hS X.1)
    [AlgebraicGeometry.IsIntegral (chartScheme V)]
    [IsLocallyNoetherian (chartScheme V)]
    (hV : IsAffine (chartScheme V))
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (hgen : ∀ W : PrimeDivisor B S hS X.1,
      ∃ v : ↥(W.genericHenselianLocalRing B S hS X.2 hdec), IsUnit v ∧
        W.canonicalGenericRatio B S hS X.2 hdec L hL hInt hN t =
          algebraMap ↥(W.genericHenselianLocalRing B S hS X.2 hdec)
            (W.genericTotalFractionRing B S hS X.2 hdec) v)
    (z : chartScheme V) (hz : coheight z = 1) :
    (chartScheme V).ord (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
      (chartRatio B S hS X.1 X.2 L V e hecompat hebij t)) z = 0 := by
  obtain ⟨Z, hZ⟩ :=
    exists_primeDivisor_genericPoint_eq_chartSchemeToPoints B S hS X.2 hdec V z hz
  obtain ⟨v, hv, hveq⟩ := hgen Z
  obtain ⟨T, hT, hTunit⟩ := Z.exists_sieve_isUnit_baseChangeChartRatio B S hS X.2 hdec hInt hN
    L hL hNormal t V e hecompat hebij v hv hveq
  obtain ⟨p, -, hpz⟩ :=
    Z.exists_points_genericStalkBaseChangeChart B S hS X.2 hdec V z hZ.symm
  obtain ⟨Q, ι, hι, hQaff, q, hq⟩ := SmallEtale.exists_affine_mem_range_of_mem_topology B S hS
    (Z.genericStalkSpace B S hS X.2 hdec).1 hT p
  obtain ⟨w, hw, hweq⟩ := hTunit ι hι
  have hqz : (Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q = z :=
    (congrArg ((BigFppfOver.toScheme B S hS).map
      (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V).g).base hq).trans hpz
  have hflat : AlgebraicGeometry.Flat (Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι) :=
    Z.flat_genericStalkBaseChangeSchemeMap B S hS hdec V ι
  let algVQ : Algebra ↥((chartScheme V).presheaf.stalk
        ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q))
      ↥((chartScheme Q).presheaf.stalk q) :=
    ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).stalkMap q).hom.toAlgebra
  have hVQflat : Module.Flat ↥((chartScheme V).presheaf.stalk
        ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q))
      ↥((chartScheme Q).presheaf.stalk q) :=
    AlgebraicGeometry.Flat.stalkMap (Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι) q
  have hVQloc : IsLocalHom (algebraMap ↥((chartScheme V).presheaf.stalk
        ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q))
      ↥((chartScheme Q).presheaf.stalk q)) :=
    inferInstanceAs (IsLocalHom
      ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).stalkMap q).hom)
  have : Module.FaithfullyFlat ↥((chartScheme V).presheaf.stalk
        ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q))
      ↥((chartScheme Q).presheaf.stalk q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨fV, hfV⟩ := exists_ringHom_fractionRing_of_map_nonZeroDivisors
    (K := (chartScheme V).functionField)
    ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).stalkMap q).hom
    fun _ hy ↦ mem_nonZeroDivisors_algebraMap_of_flat hy
  have hQaff' : IsAffine (chartScheme Q) := hQaff
  let algOQ : Algebra ↥Γ(chartScheme Q, ⊤) ↥((chartScheme Q).presheaf.stalk q) :=
    TopCat.Presheaf.algebra_section_stalk (chartScheme Q).presheaf
      (⟨q, trivial⟩ : (⊤ : (chartScheme Q).Opens))
  have hlocQ : IsLocalization.AtPrime ↥((chartScheme Q).presheaf.stalk q)
      ((isAffineOpen_top (chartScheme Q)).primeIdealOf
        (⟨q, trivial⟩ : (⊤ : (chartScheme Q).Opens))).asIdeal :=
    (isAffineOpen_top (chartScheme Q)).isLocalization_stalk
      (⟨q, trivial⟩ : (⊤ : (chartScheme Q).Opens))
  have hOQflat : Module.Flat ↥Γ(chartScheme Q, ⊤) ↥((chartScheme Q).presheaf.stalk q) :=
    IsLocalization.flat ↥((chartScheme Q).presheaf.stalk q)
      ((isAffineOpen_top (chartScheme Q)).primeIdealOf
        (⟨q, trivial⟩ : (⊤ : (chartScheme Q).Opens))).asIdeal.primeCompl
  have hfracQ : IsFractionRing
      ↥((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj (op Q))
      ↥((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
        (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj (op Q)) :=
    Z.isFractionRing_genericStalkChartMeromorphic B S hS X.2 hdec hInt hN Q hQaff
  obtain ⟨gQ, hgQ⟩ := exists_ringHom_fractionRing_of_map_nonZeroDivisors
    (A := ↥((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj (op Q)))
    (K := ↥((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
      (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj (op Q)))
    ((chartScheme Q).presheaf.germ ⊤ q trivial).hom
    fun _ hy ↦ mem_nonZeroDivisors_algebraMap_of_flat (A := ↥Γ(chartScheme Q, ⊤))
      (D := ↥((chartScheme Q).presheaf.stalk q)) hy
  have hgerm := Z.lift_chartMeromorphicFunctionFieldEquiv_eq B S hS hwa hfin hdec V hV ι q
    fV hfV gQ hgQ (chartRatio B S hS X.1 X.2 L V e hecompat hebij t)
  have hweq' : ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
          (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map ι.op).hom
        (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
          (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V)
          (chartRatio B S hS X.1 X.2 L V e hecompat hebij t)) =
      algebraMap
        ((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj (op Q))
        ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
          (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj (op Q)) w :=
    hweq
  have hc := hgerm.trans ((congrArg gQ hweq').trans (hgQ w))
  obtain ⟨a, ha, haeq⟩ := exists_isUnit_eq_algebraMap_of_isUnit_of_faithfullyFlat fV hfV
    (hw.map ((chartScheme Q).presheaf.germ ⊤ q trivial).hom) hc
  have hco : coheight ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q) = 1 := by
    rwa [hqz]
  rw [← hqz, haeq]
  exact Scheme.ord_algebraMap_of_isUnit hco ha

end AlgebraicGeometry.Space

end
