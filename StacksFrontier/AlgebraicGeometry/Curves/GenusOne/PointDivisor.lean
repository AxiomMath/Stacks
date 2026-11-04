module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.SectionOrder
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# The canonical section of `𝒪_X(n · x)` in the section ring, and its order at `x`

Let `x` be a closed point of a scheme `X` such that `n · x` is an effective Cartier divisor, and
let `𝒪_X(n · x)` be its invertible sheaf with canonical section `1_{n · x}`. This file reads
`1_{n · x}` as a homogeneous element of degree one of the section ring `Γ_*(X, 𝒪_X(n · x))`,
proves that for `n ≥ 1` it vanishes exactly at `x`, and, when the local ring at `x` is a discrete
valuation ring, that its order at `x` is `n`. Finally, for a `k`-rational point `x` of a scheme
over a field `k`, every element of the local ring at `x` is a constant modulo the maximal ideal:
the residue field at `x` is `k`.

## Main definitions

* `AlgebraicGeometry.GenusOne.pointSection`: the canonical section of `𝒪_X(n · x)`, as a degree-one
  element of the section ring.

## Main results

* `AlgebraicGeometry.GenusOne.stalkOrd_Γgerm_eq_of_map_germ_ideal_zeroScheme`: the order at `x` of
  a global section of an invertible module is `n` when the ideal of its zero scheme has germ
  `𝔪_x ^ n` at `x`.
* `AlgebraicGeometry.GenusOne.coe_nonvanishingOpen_pointSection`: for `n ≥ 1` the nonvanishing
  locus of the canonical section is `X ∖ {x}`; `mem_nonvanishingOpen_pointSection` and
  `notMem_nonvanishingOpen_pointSection` are its two halves.
* `AlgebraicGeometry.GenusOne.sectionOrd_pointSection`: the order at `x` of the canonical section
  is `n`.
* `AlgebraicGeometry.GenusOne.exists_sub_Γgerm_mem_maximalIdeal`: the residue field at a rational
  point is the base field.

## Implementation notes

**The order.** Around `x` the invertible module is trivialized over an affine open `U` by a basis
section `e`, and the canonical section restricts to `a • e`. The ideal of the zero scheme on `U`
is then `(a)` (`AlgebraicGeometry.zeroScheme_ideal_of_trivialization`), and the zero scheme of
`1_D` is `D` itself ([Stacks, Tag 01X0]), whose ideal on `U` is the `n`-th power of the ideal of
the reduced point. Its germ at `x` is `𝔪_x ^ n`, so the germ of `a` has valuation `n`, while the
germ of `e` generates the stalk and has order zero.

**The tensor power.** A degree-one element of the section ring is a global section of
`𝒪_X(n · x) ^ ⊗ 1`, which is compared with `𝒪_X(n · x)` through the left unitor
(`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.twistOneSection`); the stalks are
compared through `Stacks.ModuleStalk.equivOfIso`, which preserves orders.

**The residue field.** The stalk map of the section `p : Spec k ⟶ X` is a local homomorphism into
the stalk of `Spec k`, which `k` maps onto; since `p` followed by the structure morphism is the
identity, the constant `c` with the same image as `v` has `v - c` in the kernel, hence in the
maximal ideal.

## References

* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite IsLocalRing
open Stacks.ModuleStalk
open Stacks.GradedSections (powSections)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.Divisors (modulesInvertibleSheaf canonicalSection canonicalSections
  IsEffectiveCartierDivisor)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (twistOneSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (secOf)

universe u

namespace AlgebraicGeometry.GenusOne

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- **In a discrete valuation ring, a generator of `𝔪 ^ n` has valuation `n`.** -/
theorem addVal_eq_of_span_eq_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {r : R} {n : ℕ} (h : Ideal.span {r} = maximalIdeal R ^ n) :
    IsDiscreteValuationRing.addVal R r = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.span_singleton_eq_span_singleton] at h
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated r (ϖ ^ n)).mpr h, hϖ.addVal_pow]

variable {X : Scheme.{u}}

/-- **`𝒪_X(D)` is an invertible module in the spelling of the section ring**, for an effective
Cartier divisor `D`. -/
instance isInvertibleModule_modulesInvertibleSheaf (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] :
    Stacks.Ample.IsInvertibleModule X (modulesInvertibleSheaf D) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
    (Stacks.Divisors.stacksIsInvertible_invertibleSheaf D)

/-- **The order of a section is read off the germ of the ideal of its zero scheme.** If the ideal
of the zero scheme of a global section `s` of an invertible module has germ `𝔪_x ^ n` at `x` on
every affine open through `x`, then the germ of `s` at `x` has order `n`. -/
theorem stalkOrd_Γgerm_eq_of_map_germ_ideal_zeroScheme (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] (s : Γ(M, ⊤)) {x : X}
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)] {n : ℕ}
    (h : ∀ (U : X.affineOpens) (hxU : x ∈ (U : Set X)),
      Ideal.map (X.presheaf.germ U.1 x hxU).hom ((zeroScheme X M s).ideal U) =
        maximalIdeal (X.presheaf.stalk x) ^ n) :
    Stacks.StalkOrder.stalkOrd M x ((M.presheaf.Γgerm x).hom s) = n := by
  obtain ⟨V, hxV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at M x
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hUV' : U ≤ V := hUV
  set a : Γ(X, U) := Stacks.NonvanishingOpen.triv t (homOfLE hUV')
    (M.presheaf.map (homOfLE le_top).op s)
  have hideal : (zeroScheme X M s).ideal ⟨U, hU⟩ = Ideal.span {a} :=
    zeroScheme_ideal_of_trivialization X M s ⟨U, hU⟩ (t.θ U (homOfLE hUV')) a rfl
  -- the germ of `s` is the germ of `a` times the germ of the basis section
  have hs : (M.presheaf.Γgerm x).hom s = (X.presheaf.germ U x hxU).hom a •
      (M.presheaf.germ V x hxV).hom (Stacks.NonvanishingOpen.basis t) := by
    have e := Stacks.SectionProduct.eq_triv_smul_res_basis t (homOfLE hUV')
      (M.presheaf.map (homOfLE le_top).op s)
    have h1 : (M.presheaf.Γgerm x).hom s =
        (M.presheaf.germ U x hxU).hom (M.presheaf.map (homOfLE le_top).op s) :=
      (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE le_top) x hxU s).symm
    rw [h1, e, germ_smul, TopCat.Presheaf.germ_res_apply]
  -- the germ of the basis section generates the stalk
  obtain ⟨g, hg, hfree⟩ := Stacks.StalkOrder.exists_generator M x
  obtain ⟨d, hd⟩ := hg ((M.presheaf.germ V x hxV).hom (Stacks.NonvanishingOpen.basis t))
  obtain ⟨c, hc⟩ := Stacks.SectionProduct.exists_smul_germ_basis t hxV g
  have hcd : c * d = 1 := by
    have h2 : (c * d - 1) • g = 0 := by
      rw [sub_smul, ← smul_smul, ← hd, ← hc, one_smul, sub_self]
    exact sub_eq_zero.mp (hfree _ h2)
  have hd0 : IsDiscreteValuationRing.addVal (X.presheaf.stalk x) d = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_of_unit (IsUnit.of_mul_eq_one_right c hcd).unit
  rw [hs, hd, smul_smul, Stacks.StalkOrder.stalkOrd_smul_generator hg hfree,
    IsDiscreteValuationRing.addVal_mul, hd0, add_zero]
  refine addVal_eq_of_span_eq_maximalIdeal_pow ?_
  rw [← h ⟨U, hU⟩ hxU, hideal, Ideal.map_span, Set.image_singleton]

variable {x : X} (hx : IsClosed ({x} : Set X)) (n : ℕ)
  [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)]

/-- **The canonical section of `𝒪_X(n · x)`, as a degree-one element of the section ring**
`Γ_*(X, 𝒪_X(n · x))`: the canonical section `1_{n · x}` read as a global section of the first
tensor power. -/
def pointSection :
    powSections (modulesInvertibleSheaf
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) 1 :=
  secOf _ (twistOneSection
    (modulesInvertibleSheaf (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n))
    (canonicalSection (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)))

omit [IsEffectiveCartierDivisor
  (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)] in
/-- The global section of `pointSection` is the canonical section, read in the first tensor
power. -/
theorem globalSection_pointSection :
    globalSection X _ (pointSection hx n) = twistOneSection
      (modulesInvertibleSheaf (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n))
      (canonicalSection (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) :=
  Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf _ _

/-- **The canonical section of `𝒪_X(n · x)` vanishes exactly at `x`**, for `n ≥ 1`: its
nonvanishing locus in the section ring is `X ∖ {x}`. -/
theorem coe_nonvanishingOpen_pointSection (hn : 0 < n) :
    (Stacks.NonvanishingOpen.nonvanishingOpen X
        (natTensorPow (modulesInvertibleSheaf
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) 1)
        (globalSection X _ (pointSection hx n)) : Set X) = ({x} : Set X)ᶜ := by
  rw [globalSection_pointSection]
  exact (congrArg (fun U : X.Opens => (U : Set X))
    (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.nonvanishingOpen_twistOneSection
      _ _)).trans ((Stacks.AmpleBridge.nonvanishingLocus_sectionsOfTop _ _).symm.trans
    (Stacks.Divisors.nonvanishingChart_canonicalSections_vanishingIdeal_pow hx hn))

/-- **The canonical section of `𝒪_X(n · x)` does not vanish off `x`**, for `n ≥ 1`. -/
theorem mem_nonvanishingOpen_pointSection (hn : 0 < n) :
    ∀ y : X, y ≠ x → y ∈ Stacks.NonvanishingOpen.nonvanishingOpen X
      (natTensorPow (modulesInvertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) 1)
      (globalSection X _ (pointSection hx n)) := fun y hy => by
  rw [← SetLike.mem_coe, coe_nonvanishingOpen_pointSection hx n hn]
  exact hy

/-- **The canonical section of `𝒪_X(n · x)` vanishes at `x`**, for `n ≥ 1`. -/
theorem notMem_nonvanishingOpen_pointSection (hn : 0 < n) :
    x ∉ Stacks.NonvanishingOpen.nonvanishingOpen X
      (natTensorPow (modulesInvertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) 1)
      (globalSection X _ (pointSection hx n)) := by
  rw [← SetLike.mem_coe, coe_nonvanishingOpen_pointSection hx n hn]
  exact fun h => h rfl

/-- **The canonical section of `𝒪_X(n · x)` has order `n` at `x`**, when the local ring at `x` is
a discrete valuation ring: the ideal of its zero scheme is that of `n · x` ([Stacks, Tag 01X0]),
whose germ at `x` is `𝔪_x ^ n`. -/
theorem sectionOrd_pointSection [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    Stacks.StalkOrder.sectionOrd x (modulesInvertibleSheaf
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) (pointSection hx n) =
      n := by
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n with hD
  set L := modulesInvertibleSheaf D
  unfold Stacks.StalkOrder.sectionOrd Stacks.StalkOrder.sectionGerm
  rw [globalSection_pointSection]
  have h1 : ((natTensorPow L 1).presheaf.Γgerm x).hom (twistOneSection L (canonicalSection D)) =
      equivOfIso (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).symm x
        ((L.presheaf.Γgerm x).hom (canonicalSection D)) :=
    (mapFun_Γgerm _ x _).symm
  rw [h1, ← LinearEquiv.coe_toLinearMap,
    Stacks.StalkOrder.stalkOrd_map_of_bijective _ (LinearEquiv.bijective _)]
  refine stalkOrd_Γgerm_eq_of_map_germ_ideal_zeroScheme L (canonicalSection D) fun U hxU => ?_
  rw [Stacks.Divisors.zeroScheme_canonicalSection', hD, Scheme.IdealSheafData.ideal_pow,
    Pi.pow_apply, Ideal.map_pow, map_germ_ideal_vanishingIdeal_singleton hx U hxU]

/-- **The residue field at a rational point is the base field.** For a scheme `X` over a field
`k` with a section `p` of the structure morphism, every element of the local ring at the point of
`p` agrees with a constant modulo the maximal ideal. -/
theorem exists_sub_Γgerm_mem_maximalIdeal {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) (v : X.presheaf.stalk (point p)) :
    ∃ c : k, v - (X.presheaf.Γgerm (point p)).hom (globalSectionsHom f c) ∈
      maximalIdeal (X.presheaf.stalk (point p)) := by
  set φ := p.stalkMap (closedPoint k)
  set c : k := (stalkClosedPointIso (.of k)).hom.hom (φ.hom v)
  refine ⟨c, ?_⟩
  -- the stalk map of `p` sends the germ of a constant to the germ of the constant
  have hgerm : ∀ a : Γ(Spec (.of k), ⊤),
      φ.hom ((X.presheaf.Γgerm (point p)).hom (f.appTop a)) =
        ((Spec (.of k)).presheaf.Γgerm (closedPoint k)).hom a := by
    intro a
    have h3 : p.appTop (f.appTop a) = a := by
      have h4 : (p ≫ f).appTop a = a := by rw [hp]; rfl
      exact h4
    exact (Scheme.Hom.germ_stalkMap_apply p ⊤ (closedPoint k) trivial (f.appTop a)).trans
      (congrArg ((Spec (.of k)).presheaf.Γgerm (closedPoint k)).hom h3)
  -- every element of the stalk of `Spec k` is a constant
  have hc : ((Spec (.of k)).presheaf.Γgerm (closedPoint k)).hom
      ((Scheme.ΓSpecIso (.of k)).inv.hom c) = φ.hom v := by
    have e1 := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))
      (ΓSpecIso_hom_stalkClosedPointIso_inv (.of k))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
    refine Eq.trans (b := (stalkClosedPointIso (.of k)).inv.hom
      ((Scheme.ΓSpecIso (.of k)).hom.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))) e1.symm ?_
    simp [c]
  have hzero : φ.hom (v - (X.presheaf.Γgerm (point p)).hom (globalSectionsHom f c)) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact ((hgerm _).trans hc).symm
  have := (Spec (.of k)).isLocalRing (closedPoint k)
  by_contra hmem
  have hu : IsUnit (v - (X.presheaf.Γgerm (point p)).hom (globalSectionsHom f c)) := by
    simpa only [mem_maximalIdeal, mem_nonunits_iff, not_not] using hmem
  exact not_isUnit_zero (hzero ▸ hu.map φ.hom)

end AlgebraicGeometry.GenusOne

end
