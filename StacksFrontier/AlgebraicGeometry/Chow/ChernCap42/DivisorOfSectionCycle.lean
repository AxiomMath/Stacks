module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.RegularMeromorphicSection
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.StalkBasis
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.Codimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierRegular.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
import all StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization

/-!
# The divisor of a nonzero global section is the cycle of its zero scheme

Let `X` be an integral scheme locally of finite type over the base scheme of chapter 42 of the
Stacks Project, of delta-dimension `n`, let `L` be an invertible `𝒪_X`-module and let
`s ∈ Γ(X, L)` be a nonzero global section. Then

`div_L(s) = [Z(s)]_{n-1}` in `Z_{n-1}(X)` and `c₁(L) ∩ [X] = [Z(s)]_{n-1}` in `CH_{n-1}(X)`.

## Main results

* `Stacks.ChernCap42.isCoordinateAt_frameSections` — on a trivializing open the function
  representing `s` is a coordinate of `s` in the sense of Stacks 02SF.
* `Stacks.ChernCap42.orderOfVanishingMeromorphic_eq_ord_frameSections` — the order of vanishing
  of `s` along a prime divisor is the order of vanishing of that function.
* `Stacks.ChernCap42.cycleAssociatedToZeroScheme_apply_eq_ord` — the coefficient of `[Z(s)]_{n-1}`
  at a point of codimension one is that same order of vanishing.
* `Stacks.ChernCap42.divisorOfMeromorphicSectionCycle_eq_cycleAssociatedToZeroScheme` — the
  equality of cycles `div_L(s) = [Z(s)]_{n-1}`.
* `Stacks.ChernCap42.firstChernClassCapOfInvertible_fundamentalCycle` — the equality of classes
  `c₁(L) ∩ [X] = [Z(s)]_{n-1}` in the Chow group.

## References

* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

universe u

namespace Stacks.ChernCap42

open Stacks.Chow Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### A trivializing section as a local coordinate -/

/-- The sectionwise trivialization of `L` over an open set contained in `U` determined by a
trivialization `eU : L|_U ≅ 𝒪_U`. Over `U` itself it is `Stacks.Divisors.frameSections`. -/
def frameSectionsLE (X : Scheme.{u}) (L : X.Modules) {U : X.Opens}
    (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) {V : X.Opens} (hV : V ≤ U) :
    Γ(L, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  ((_root_.SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (op (Over.mk (homOfLE hV)))).mapIso eU).toLinearEquiv

/-- The trivializations of `L` over the open sets contained in `U` are compatible with
restriction. -/
theorem frameSectionsLE_res (X : Scheme.{u}) (L : X.Modules) {U : X.Opens}
    (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) {V : X.Opens} (hV : V ≤ U)
    (t : Γ(L, U)) :
    frameSectionsLE X L eU hV (L.presheaf.map (homOfLE hV).op t) =
      X.presheaf.map (homOfLE hV).op (Stacks.Divisors.frameSections X L eU t) :=
  PresheafOfModules.naturality_apply eU.hom.val
    (Over.homMk (homOfLE hV) (Subsingleton.elim _ _) :
      (Over.mk (homOfLE hV) : Over U) ⟶ Over.mk (𝟙 U)).op t

/-- On an open set carrying a trivialization `e : Γ(L, U) ≃ₗ Γ(X, U)`, the germ of the restriction
of a global section `s` is the germ of the function `e (s|_U)` times the germ of the section
representing the constant function `1`. -/
theorem germ_restrict_eq_smul (L : X.Modules) (s : Γ(L, ⊤)) {U : X.Opens} {x : X} (hx : x ∈ U)
    (e : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(X, U)) :
    L.presheaf.germ U x hx (L.presheaf.map (homOfLE le_top).op s) =
      X.presheaf.germ U x hx (e (L.presheaf.map (homOfLE le_top).op s)) •
        L.presheaf.germ U x hx (e.symm 1) := by
  have hsU : L.presheaf.map (homOfLE le_top).op s =
      e (L.presheaf.map (homOfLE le_top).op s) • e.symm (1 : Γ(X, U)) := by
    refine e.injective ?_
    rw [map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  conv_lhs => rw [hsU]
  exact Scheme.Modules.germ_smul L hx _ _

/-- If `eU : L|_U ≅ 𝒪_U` is a trivialization of `L` over `U`, the section of `L` corresponding to
the constant function `1` has, at every point of `U`, a germ spanning the stalk of `L` there. -/
theorem span_germ_frameSections_symm_one (X : Scheme.{u}) (L : X.Modules) {U : X.Opens}
    (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (x : X) (hx : x ∈ U) :
    Submodule.span ↑(X.presheaf.stalk x)
        {L.presheaf.germ U x hx ((Stacks.Divisors.frameSections X L eU).symm 1)} = ⊤ := by
  refine le_antisymm le_top fun z _ => ?_
  obtain ⟨V, hxV, v, hv⟩ := L.presheaf.exists_germ_eq z
  have hWU : U ⊓ V ≤ U := inf_le_left
  have hWV : U ⊓ V ≤ V := inf_le_right
  have hxW : x ∈ U ⊓ V := ⟨hx, hxV⟩
  have hgen : frameSectionsLE X L eU hWU (L.presheaf.map (homOfLE hWU).op
      ((Stacks.Divisors.frameSections X L eU).symm 1)) = (1 : Γ(X, U ⊓ V)) := by
    rw [frameSectionsLE_res, LinearEquiv.apply_symm_apply, map_one]
  set c : Γ(X, U ⊓ V) := frameSectionsLE X L eU hWU (L.presheaf.map (homOfLE hWV).op v) with hc
  have hlocal : L.presheaf.map (homOfLE hWV).op v =
      c • L.presheaf.map (homOfLE hWU).op ((Stacks.Divisors.frameSections X L eU).symm 1) := by
    refine (frameSectionsLE X L eU hWU).injective ?_
    rw [map_smul, hgen, smul_eq_mul, mul_one]
  have hz : z = X.presheaf.germ (U ⊓ V) x hxW c •
      L.presheaf.germ U x hx ((Stacks.Divisors.frameSections X L eU).symm 1) := by
    calc
      z = L.presheaf.germ V x hxV v := hv.symm
      _ = L.presheaf.germ (U ⊓ V) x hxW (L.presheaf.map (homOfLE hWV).op v) :=
        (L.presheaf.germ_res_apply (homOfLE hWV) x hxW v).symm
      _ = L.presheaf.germ (U ⊓ V) x hxW (c • L.presheaf.map (homOfLE hWU).op
            ((Stacks.Divisors.frameSections X L eU).symm 1)) := by rw [hlocal]
      _ = X.presheaf.germ (U ⊓ V) x hxW c •
            L.presheaf.germ (U ⊓ V) x hxW (L.presheaf.map (homOfLE hWU).op
              ((Stacks.Divisors.frameSections X L eU).symm 1)) :=
        Scheme.Modules.germ_smul L hxW _ _
      _ = X.presheaf.germ (U ⊓ V) x hxW c •
            L.presheaf.germ U x hx ((Stacks.Divisors.frameSections X L eU).symm 1) := by
        rw [L.presheaf.germ_res_apply (homOfLE hWU) x hxW]
  rw [hz]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- The germ of a trivializing section of an invertible module is a stalk basis. -/
theorem isStalkBasis_germ_frameSections (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {U : X.Opens} (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (x : X)
    (hx : x ∈ U) :
    IsStalkBasis L x (L.presheaf.germ U x hx ((Stacks.Divisors.frameSections X L eU).symm 1)) :=
  (isStalkBasis_iff_span_eq_top L x _).mpr (span_germ_frameSections_symm_one X L eU x hx)

/-- The germ of a global section at a point of a trivializing open is the germ of the function
representing it times the germ of the section corresponding to the constant function `1`. -/
private theorem germ_top_eq_smul (L : X.Modules) (s : Γ(L, ⊤)) {U : X.Opens} {x : X}
    (hx : x ∈ U) (e : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(X, U)) :
    L.presheaf.germ ⊤ x trivial s =
      X.presheaf.germ U x hx (e (L.presheaf.map (homOfLE le_top).op s)) •
        L.presheaf.germ U x hx (e.symm 1) := by
  rw [← L.presheaf.germ_res_apply (homOfLE (le_top (a := U))) x hx s]
  exact germ_restrict_eq_smul L s hx e

/-- The function representing a section under a trivialization is a coordinate of it in the
sense of Stacks 02SF: the germ of `s` at the generic point is the rational function that function
determines times the generic value of a basis of the stalk of `L` at `x`. -/
theorem isCoordinateAt_frameSections [IsIntegral X] [IsLocallyNoetherian X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {U : X.Opens} [Nonempty U]
    (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (x : X) (hx : x ∈ U) :
    IsCoordinateAt L x (L.presheaf.germ ⊤ (genericPoint X) trivial s)
      (X.germToFunctionField U
        (Stacks.Divisors.frameSections X L eU (L.presheaf.map (homOfLE le_top).op s))) := by
  have hη : genericPoint X ∈ U := genericPoint_mem_of_mem hx
  refine ⟨L.presheaf.germ U x hx ((Stacks.Divisors.frameSections X L eU).symm 1),
    isStalkBasis_germ_frameSections L eU x hx, ?_⟩
  rw [toGenericStalk_germ hx hη]
  exact germ_top_eq_smul L s hη (Stacks.Divisors.frameSections X L eU)

/-! ### Nonvanishing of the local equation -/

/-- On an integral scheme a nonzero global section of an invertible module has a nonzero germ at
every point. -/
theorem germ_ne_zero_of_ne_zero [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (x : X) : L.presheaf.germ ⊤ x trivial s ≠ 0 := by
  have _ := isInvertible_stacks_of_algebraicGeometry L
  exact fun h => hs (eq_zero_of_germ_eq_zero L s h)

/-- The function representing a nonzero global section under a trivialization has a nonzero germ
at every point of the trivializing open. -/
theorem germ_frameSections_ne_zero [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) {U : X.Opens}
    (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (x : X) (hx : x ∈ U) :
    X.presheaf.germ U x hx
      (Stacks.Divisors.frameSections X L eU (L.presheaf.map (homOfLE le_top).op s)) ≠ 0 := by
  intro h0
  refine germ_ne_zero_of_ne_zero L s hs x ?_
  rw [germ_top_eq_smul L s hx (Stacks.Divisors.frameSections X L eU), h0, zero_smul]

/-- The function representing a nonzero global section under a trivialization is nonzero. -/
theorem frameSections_ne_zero [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) {U : X.Opens}
    (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (x : X) (hx : x ∈ U) :
    Stacks.Divisors.frameSections X L eU (L.presheaf.map (homOfLE le_top).op s) ≠ 0 := fun h =>
  germ_frameSections_ne_zero L s hs eU x hx (by rw [h]; exact map_zero _)

/-- On an integral scheme, the zero scheme of a nonzero global section of an invertible module
does not contain the generic point. -/
theorem genericPoint_notMem_range_subschemeι_zeroScheme [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    genericPoint X ∉ Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base := by
  obtain ⟨U, eU, hηU, -⟩ :=
    Stacks.Divisors.exists_affine_frame_subset X L (genericPoint X) ⊤ trivial
  have hgerm : X.presheaf.germ U.1 (genericPoint X) hηU
      (Stacks.Divisors.frameSections X L eU (L.presheaf.map (homOfLE le_top).op s)) ≠ 0 :=
    germ_frameSections_ne_zero L s hs eU _ hηU
  have hfield : IsField ↑(X.presheaf.stalk (genericPoint X)) :=
    isField_stalk_of_isMax (fun b _ => genericPoint_specializes b)
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hgerm
  have hstalk : IdealSheafData.stalk (Stacks.Divisors.zeroScheme X L s) (genericPoint X) = ⊤ := by
    rw [IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span (U := U) hηU
      (Stacks.Divisors.zeroScheme_ideal_of_trivialization X L s U
        (Stacks.Divisors.frameSections X L eU) _ rfl)]
    exact Ideal.span_singleton_eq_top.mpr (IsUnit.of_mul_eq_one b hb)
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).mp hstalk

/-! ### The two coefficients -/

/-- The order of vanishing of a nonzero global section along a prime divisor is the order of
vanishing of the function representing it on a trivializing open around the generic point of that
prime divisor. -/
theorem orderOfVanishingMeromorphic_eq_ord_frameSections [IsIntegral X] [IsLocallyNoetherian X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (Z : Stacks.Divisors.PrimeDivisor X) {U : X.Opens} [Nonempty U]
    (eU : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (hx : Z.genericPoint ∈ U) :
    orderOfVanishingMeromorphic X L (meromorphicSectionOfSection L s)
        (isRegularMeromorphicSection_of_ne_zero X L s hs) Z =
      X.ord (X.germToFunctionField U
        (Stacks.Divisors.frameSections X L eU (L.presheaf.map (homOfLE le_top).op s)))
        Z.genericPoint := by
  refine orderOfVanishingMeromorphic_eq X L _ _ ?_
  rw [genericValue_meromorphicSectionOfSection]
  exact isCoordinateAt_frameSections L s eU Z.genericPoint hx

/-- At a point of codimension one, the coefficient of `[Z(s)]_{n-1}` is the order of vanishing of
the function representing `s` on a trivializing affine open around that point. -/
theorem cycleAssociatedToZeroScheme_apply_eq_ord (C : ChowSituation.{u}) (p : X ⟶ C.S)
    [LocallyOfFiniteType p] [IsIntegral X] [IsLocallyNoetherian X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) {x : X} (hco : coheight x = 1) {U : X.affineOpens} [Nonempty U.1]
    (eU : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) (hx : x ∈ U.1) :
    (cycleAssociatedToClosedSubscheme C p
        (Stacks.Divisors.zeroScheme X L s).subschemeι (n - 1)).1 x =
      X.ord (X.germToFunctionField U.1
        (Stacks.Divisors.frameSections X L eU (L.presheaf.map (homOfLE le_top).op s))) x := by
  set a := Stacks.Divisors.frameSections X L eU (L.presheaf.map (homOfLE le_top).op s) with hadef
  have ha : a ≠ 0 := frameSections_ne_zero L s hs eU x hx
  have hstalk : IdealSheafData.stalk (Stacks.Divisors.zeroScheme X L s) x =
      Ideal.span {(X.presheaf.germ U.1 x hx).hom a} :=
    IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span (U := U) hx
      (Stacks.Divisors.zeroScheme_ideal_of_trivialization X L s U
        (Stacks.Divisors.frameSections X L eU) a rfl)
  by_cases hmem : x ∈ Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base
  · have hkey := principalDivisorCycle_apply_eq_cycleAssociatedToClosedSubscheme_apply C p hn
      (Stacks.Divisors.zeroScheme X L s)
      (genericPoint_notMem_range_subschemeι_zeroScheme L s hs) hco hmem hx a ha hstalk
    rw [← hkey, principalDivisorCycle_apply]
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C p _ (n - 1) hmem]
    have hnot : x ∉ (Stacks.Divisors.zeroScheme X L s).support := fun hc =>
      hmem (by rw [Scheme.IdealSheafData.range_subschemeι]; exact hc)
    have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).mpr hnot
    rw [hstalk] at htop
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx a,
      Scheme.ord_algebraMap_of_isUnit hco (Ideal.span_singleton_eq_top.mp htop)]

/-! ### Stacks 02SK, the equality of cycles -/

/-- Let `X` be an integral scheme locally of finite type over the base of
chapter 42, of delta-dimension `n`, let `L` be an invertible `𝒪_X`-module and let `s` be a nonzero
global section of `L`. Then the divisor of `s` is the cycle of its zero scheme:
`div_L(s) = [Z(s)]_{n-1}` in `Z_{n-1}(X)`. -/
@[stacks 02SK "divisor cycle"]
theorem divisorOfMeromorphicSectionCycle_eq_cycleAssociatedToZeroScheme (C : ChowSituation.{u})
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] (n : ℤ)
    (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    divisorOfMeromorphicSectionCycle C p n hn L (meromorphicSectionOfSection L s)
        (isRegularMeromorphicSection_of_ne_zero X L s hs) =
      cycleAssociatedToClosedSubscheme C p
        (Stacks.Divisors.zeroScheme X L s).subschemeι (n - 1) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  by_cases hco : coheight x = 1
  · set Z : Stacks.Divisors.PrimeDivisor X := PrimeDivisor.ofCoheightOne x hco with hZdef
    have hZx : Z.genericPoint = x := PrimeDivisor.genericPoint_ofCoheightOne x hco
    obtain ⟨U, eU, hxU, -⟩ := Stacks.Divisors.exists_affine_frame_subset X L x ⊤ trivial
    have : Nonempty (U : X.Opens) := ⟨⟨x, hxU⟩⟩
    rw [cycleAssociatedToZeroScheme_apply_eq_ord C p hn L s hs hco eU hxU, ← hZx]
    rw [show ((divisorOfMeromorphicSectionCycle C p n hn L (meromorphicSectionOfSection L s)
        (isRegularMeromorphicSection_of_ne_zero X L s hs) : CycleGroup C p (n - 1)) :
        AlgebraicCycle X ℤ) Z.genericPoint =
        orderOfVanishingMeromorphic X L (meromorphicSectionOfSection L s)
          (isRegularMeromorphicSection_of_ne_zero X L s hs) Z from
      divisorOfMeromorphicSectionCycle_genericPoint C p n hn L _ _ Z]
    rw [orderOfVanishingMeromorphic_eq_ord_frameSections L s hs Z eU (hZx ▸ hxU), hZx]
  · have hleft : ((divisorOfMeromorphicSectionCycle C p n hn L (meromorphicSectionOfSection L s)
        (isRegularMeromorphicSection_of_ne_zero X L s hs) : CycleGroup C p (n - 1)) :
        AlgebraicCycle X ℤ) x = 0 :=
      divisorOfMeromorphicSectionCycle_eq_zero C p n hn L _ _ x
        fun Z hZ => hco (hZ ▸ PrimeDivisor.coheight_genericPoint Z)
    have hright : (cycleAssociatedToClosedSubscheme C p
        (Stacks.Divisors.zeroScheme X L s).subschemeι (n - 1)).1 x = 0 := by
      by_contra hne
      exact hco ((relativeDimension_eq_sub_one_iff_coheight_eq_one C p hn x).mp
        ((mem_cyclesOfDimension_iff_forall_point C p (n - 1) _).mp
          (cycleAssociatedToClosedSubscheme C p
            (Stacks.Divisors.zeroScheme X L s).subschemeι (n - 1)).2 x hne))
    rw [hleft, hright]

/-! ### Stacks 02SK, the equality of Chow classes -/

/-- The pullback of an invertible module along a morphism of schemes is invertible. -/
theorem isInvertible_sheafObj_modulePullback (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {X' : Scheme.{u}} (f : X' ⟶ X) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X'.sheaf.obj X'.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L
    ‹AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›

/-- On an integral scheme, the pullback of a nonzero global section of an invertible module
along an isomorphism is nonzero. -/
theorem pullbackGlobalSections_ne_zero_of_isIso [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) {X' : Scheme.{u}} (f : X' ⟶ X) [IsIso f] :
    AlgebraicGeometry.pullbackGlobalSections f L s ≠ 0 := by
  intro h
  obtain ⟨g, hg⟩ :=
    (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s f).mp h
  refine genericPoint_notMem_range_subschemeι_zeroScheme L s hs
    ⟨g.base ((inv f).base (genericPoint X)), ?_⟩
  show (g ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι).base
    ((inv f).base (genericPoint X)) = genericPoint X
  rw [hg]
  show (inv f ≫ f).base (genericPoint X) = genericPoint X
  simp

/-- The closed immersion of a closed subscheme is carried to that of an equal closed subscheme by
the transport along the equality. -/
alias subschemeι_eqToHom := Stacks.Chow.subschemeι_eqToHom

/-- For an isomorphism `j : X' ⟶ X`, the zero scheme of `j^* s` is isomorphic over `X` to the
zero scheme of `s`. -/
theorem exists_zeroSchemeIso_of_isIso (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {X' : Scheme.{u}} (j : X' ⟶ X) [IsIso j] :
    ∃ e : (Stacks.Divisors.zeroScheme X' ((Scheme.Modules.pullback j).obj L)
        (AlgebraicGeometry.pullbackGlobalSections j L s)).subscheme ≅
        (Stacks.Divisors.zeroScheme X L s).subscheme,
      e.hom ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι =
        (Stacks.Divisors.zeroScheme X' ((Scheme.Modules.pullback j).obj L)
          (AlgebraicGeometry.pullbackGlobalSections j L s)).subschemeι ≫ j := by
  have hZ : Stacks.Divisors.zeroScheme X' ((Scheme.Modules.pullback j).obj L)
      (AlgebraicGeometry.pullbackGlobalSections j L s) =
      (Stacks.Divisors.zeroScheme X L s).comap j := Stacks.Divisors.zeroScheme_pullback j L s
  refine ⟨eqToIso (congrArg Scheme.IdealSheafData.subscheme hZ) ≪≫
    (Stacks.Divisors.zeroScheme X L s).comapIso j ≪≫
      asIso (Limits.pullback.snd j (Stacks.Divisors.zeroScheme X L s).subschemeι), ?_⟩
  have hsnd : Limits.pullback.snd j (Stacks.Divisors.zeroScheme X L s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι =
      Limits.pullback.fst j (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ j :=
    Limits.pullback.condition.symm
  simp only [Iso.trans_hom, asIso_hom, eqToIso.hom, Category.assoc]
  rw [hsnd, Scheme.IdealSheafData.comapIso_hom_fst_assoc, ← Category.assoc,
    subschemeι_eqToHom hZ]

/-- The divisor cycle of the pullback of `s` along an isomorphism, pushed forward, is the cycle of
the zero scheme of `s`. -/
theorem properPushforward_divisorOfMeromorphicSectionCycle_pullback (C : ChowSituation.{u})
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] (n : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) {X' : Scheme.{u}} (j : X' ⟶ X) [IsIso j] [IsClosedImmersion j]
    [IsIntegral X']
    [AlgebraicGeometry.SheafOfModules.IsInvertible X'.sheaf.obj X'.ringCatSheaf.property
      ((Scheme.Modules.pullback j).obj L)]
    (hn' : schemeDeltaDimension C (j ≫ p) = (n : EInt)) :
    properPushforward C (j ≫ p) p j rfl (n - 1)
        (divisorOfMeromorphicSectionCycle C (j ≫ p) n hn'
          ((Scheme.Modules.pullback j).obj L)
          (meromorphicSectionOfSection _ (AlgebraicGeometry.pullbackGlobalSections j L s))
          (isRegularMeromorphicSection_of_ne_zero X' _ _
            (pullbackGlobalSections_ne_zero_of_isIso L s hs j))) =
      cycleAssociatedToClosedSubscheme C p
        (Stacks.Divisors.zeroScheme X L s).subschemeι (n - 1) := by
  obtain ⟨e, he⟩ := exists_zeroSchemeIso_of_isIso L s j
  rw [divisorOfMeromorphicSectionCycle_eq_cycleAssociatedToZeroScheme C (j ≫ p) n hn' _ _
      (pullbackGlobalSections_ne_zero_of_isIso L s hs j),
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C (j ≫ p) p j
      rfl _ (n - 1)]
  exact cycleAssociatedToClosedSubscheme_eq_of_iso C p _ _ e he (n - 1)

/-- Let `X` be an integral scheme locally of finite type over the base of chapter 42, of
delta-dimension `n`, let `L` be an invertible `𝒪_X`-module and let `s` be a nonzero global section
of `L`. Then the first Chern class of `L` capped with the fundamental cycle `[X]` of `X`, in
degree `n - 1 + 1`, is the class of the cycle of the zero scheme of `s`:
`c₁(L) ∩ [X] = [Z(s)]_{n-1}` in `CH_{n-1}(X)`. -/
@[stacks 02SK "first Chern class"]
theorem firstChernClassCapOfInvertible_fundamentalCycle (C : ChowSituation.{u}) (p : X ⟶ C.S)
    [LocallyOfFiniteType p] [IsIntegral X] (n : ℤ)
    (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    firstChernClassCapOfInvertible C p (n - 1) L
        (cycleAssociatedToClosedSubscheme C p (𝟙 X) (n - 1 + 1)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C p
        (Stacks.Divisors.zeroScheme X L s).subschemeι (n - 1)) := by
  have hLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hIntW : IsIntegral (⊥ : X.IdealSheafData).subscheme :=
    IsIntegral.of_isIso (asIso (⊥ : X.IdealSheafData).subschemeι).inv
  have hLNW : IsLocallyNoetherian (⊥ : X.IdealSheafData).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((⊥ : X.IdealSheafData).subschemeι ≫ p)
  have hinv' := isInvertible_sheafObj_modulePullback L (⊥ : X.IdealSheafData).subschemeι
  have hnn : n - 1 + 1 = n := by ring
  have hnW : schemeDeltaDimension C ((⊥ : X.IdealSheafData).subschemeι ≫ p) = (n : EInt) :=
    (schemeDeltaDimension_of_iso C ((⊥ : X.IdealSheafData).subschemeι ≫ p) p
      (asIso (⊥ : X.IdealSheafData).subschemeι) rfl).symm.trans hn
  have hDim : schemeDeltaDimension C ((⊥ : X.IdealSheafData).subschemeι ≫ p) =
      ((n - 1 + 1 : ℤ) : EInt) := by rw [hnn]; exact hnW
  have hs' := pullbackGlobalSections_ne_zero_of_isIso L s hs (⊥ : X.IdealSheafData).subschemeι
  have hσ' : Stacks.Divisors.genericValue
      ((Scheme.Modules.pullback (⊥ : X.IdealSheafData).subschemeι).obj L)
      (meromorphicSectionOfSection _
        (AlgebraicGeometry.pullbackGlobalSections
          (⊥ : X.IdealSheafData).subschemeι L s)) ≠ 0 := by
    rw [Stacks.Divisors.genericValue_meromorphicSectionOfSection]
    exact germ_ne_zero_of_ne_zero _ _ hs' _
  have h1 : (QuotientAddGroup.mk (firstChernComponentCycleRule C p (n - 1) L
          (⊥ : X.IdealSheafData) hIntW hDim) :
        chowGroup C ((⊥ : X.IdealSheafData).subschemeι ≫ p) (n - 1)) =
      QuotientAddGroup.mk (divisorOfMeromorphicSectionCycle C
        ((⊥ : X.IdealSheafData).subschemeι ≫ p) n hnW
        ((Scheme.Modules.pullback (⊥ : X.IdealSheafData).subschemeι).obj L)
        (meromorphicSectionOfSection _
          (AlgebraicGeometry.pullbackGlobalSections (⊥ : X.IdealSheafData).subschemeι L s))
        (isRegularMeromorphicSection_of_ne_zero _ _ _ hs')) :=
    (firstChernComponentClass_eq_mk C p (n - 1) L (⊥ : X.IdealSheafData) hIntW hDim).symm.trans
      ((firstChernComponentClass_eq_mk_of_ne_zero C p (n - 1) L (⊥ : X.IdealSheafData) hDim
        hσ').trans (congrArg QuotientAddGroup.mk (Subtype.ext rfl)))
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso C p (𝟙 X)
      (⊥ : X.IdealSheafData).subschemeι (asIso (⊥ : X.IdealSheafData).subschemeι).symm (by simp)
      (n - 1 + 1),
    firstChernClassCapOfInvertible_integral_cycle C p (n - 1) L (⊥ : X.IdealSheafData) hIntW hDim]
  refine (congrArg (chowPushforwardOfIsClosedImmersion C
    ((⊥ : X.IdealSheafData).subschemeι ≫ p) p (⊥ : X.IdealSheafData).subschemeι rfl (n - 1))
    h1).trans ?_
  exact congrArg QuotientAddGroup.mk
    (properPushforward_divisorOfMeromorphicSectionCycle_pullback C p n L s hs
      (⊥ : X.IdealSheafData).subschemeι hnW)

end Stacks.ChernCap42

end
