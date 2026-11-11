module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.PointChoice
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.Fibre
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.Flat
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.InfiniteFibres
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.FibreIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.PrincipalSlice
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.RingTheory.LocalRing.CotangentQuotient

/-!
# The central fibre of the cubic surface as a divisor, and the chosen point

The construction of [Stacks, Tag 0D5E] blows up the cubic surface
`Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` at a closed point `y` of the central fibre `Y₀`.
This file sets up the inputs of the general blowup results of
`StacksFrontier/Examples/Spaces/CurveFamilyNotScheme/Blowup/` for this `Y`:

* the coordinate `t` of the affine line pulled back to a global function on `Y`, and
  `Y₀ = V(t)`, which is the scheme-theoretic fibre over the origin and is identified with the
  Fermat cubic compatibly with the inclusions into `Y`;
* `Y₀` is integral, regular and an effective Cartier divisor, and `Y` is Noetherian;
* the point `y` of property (2) of the source, `chosenPoint`, lies on `Y₀`, and `t` is a regular
  parameter at it: its germ is not in `𝔪_y²`, because `𝒪_{Y,y}/(t) = 𝒪_{Y₀,y}` is regular of
  dimension one less than `𝒪_{Y,y}`.

## Main definitions

* `Stacks.Examples.CurveFamilyNotScheme.cubicSurfaceCoordinate`: the global function `t` on `Y`.
* `Stacks.Examples.CurveFamilyNotScheme.centralFibreIdeal`: `Y₀ = V(t)`.
* `Stacks.Examples.CurveFamilyNotScheme.centralFibreIso`: `Y₀ ≅` the Fermat cubic.
* `Stacks.Examples.CurveFamilyNotScheme.chosenPoint`: the point `y` of property (2).

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.ker_fiberι_originPoint`: `Y₀` is the ideal sheaf of the
  fibre over the origin.
* `Stacks.Examples.CurveFamilyNotScheme.isEffectiveCartierDivisor_centralFibreIdeal`,
  `Stacks.Examples.CurveFamilyNotScheme.isIntegral_subscheme_centralFibreIdeal`,
  `Stacks.Examples.CurveFamilyNotScheme.isRegular_subscheme_centralFibreIdeal`.
* `Stacks.Examples.CurveFamilyNotScheme.Γgerm_cubicSurfaceCoordinate_notMem_sq`: `t ∉ 𝔪_y²` at
  every closed point of `Y₀`.
* `Stacks.Examples.CurveFamilyNotScheme.notMem_maximalIdeal_sq_of_isRegularLocalRing_quotient`:
  in a regular local ring, a nonzero element of `𝔪` with regular quotient is not in `𝔪²`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace
open Stacks.Divisors (IsEffectiveCartierDivisor)

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

/-! ### A ring-theoretic criterion for a regular parameter -/

/-- **A nonzero element `x ∈ 𝔪` of a regular local ring whose quotient is regular is not in
`𝔪²`.** If `x ∈ 𝔪²` the cotangent spaces of `R` and `R ⧸ (x)` agree, but the dimension drops by
one, so they cannot both be regular. -/
theorem notMem_maximalIdeal_sq_of_isRegularLocalRing_quotient {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    (hq : IsRegularLocalRing (R ⧸ Ideal.span {x})) : x ∉ maximalIdeal R ^ 2 := by
  intro hx2
  have := hq
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have h1 := IsLocalRing.finrank_cotangentSpace_quotient (Ideal.span {x})
    (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  have h2 := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  have h3 := (IsRegularLocalRing.iff_finrank_cotangentSpace (R ⧸ Ideal.span {x})).mp hq
  have h4 := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hx0) hx
  rw [← h2, ← h3, h1] at h4
  norm_cast at h4
  omega

/-! ### The coordinate `t` and the central fibre -/

variable (k : Type u) [Field k]

/-- The coordinate `t` of the affine line, pulled back to a global function on the cubic
surface `Y`. -/
def cubicSurfaceCoordinate : Γ(cubicSurface k, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫
    (cubicSurfaceToLine k).appTop).hom Polynomial.X

/-- The central fibre `Y₀ = V(t)` of the cubic surface, as an ideal sheaf. -/
def centralFibreIdeal : (cubicSurface k).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {cubicSurfaceCoordinate k})

/-- `Y₀` is cut out by `t`. -/
theorem centralFibreIdeal_eq :
    centralFibreIdeal k =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {cubicSurfaceCoordinate k}) :=
  rfl

/-- The origin of the affine line is a closed point. -/
theorem isClosed_originPoint : IsClosed ({originPoint k} : Set (affineLine k)) := by
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal (originPoint k)).mpr
    (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X)

/-- **`Y₀ = V(t)` is the ideal sheaf of the scheme-theoretic fibre of `Y ⟶ A¹_k` over the
origin.** -/
theorem ker_fiberι_originPoint :
    ((cubicSurfaceToLine k).fiberι (originPoint k)).ker = centralFibreIdeal k := by
  rw [Stacks.IdealSheaf.ker_fiberι _ _ (isClosed_originPoint k), centralFibreIdeal_eq]
  congr 1
  change Ideal.map _ (Ideal.span {Polynomial.X}) = _
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- The inclusion of the fibre over the origin is a closed immersion. -/
instance isClosedImmersion_fiberι_originPoint :
    IsClosedImmersion ((cubicSurfaceToLine k).fiberι (originPoint k)) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 (isClosed_originPoint k)
  exact inferInstanceAs (IsClosedImmersion (pullback.fst _ _))

/-- A closed immersion `f` is isomorphic to the closed subscheme cut out by any ideal sheaf
equal to its kernel. -/
def subschemeIsoOfKerEq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (I : Y.IdealSheafData) (h : f.ker = I) : X ≅ I.subscheme :=
  asIso f.toImage ≪≫ eqToIso (congrArg Scheme.IdealSheafData.subscheme h)

/-- `subschemeIsoOfKerEq` is compatible with the inclusions. -/
@[reassoc]
theorem subschemeIsoOfKerEq_hom_subschemeι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (I : Y.IdealSheafData) (h : f.ker = I) :
    (subschemeIsoOfKerEq f I h).hom ≫ I.subschemeι = f := by
  subst h
  simp [subschemeIsoOfKerEq, Scheme.Hom.toImage_imageι]

/-- **The central fibre `V(t)` is the Fermat cubic.** -/
def centralFibreIso : fermatCurve k ≅ (centralFibreIdeal k).subscheme :=
  fermatCurveIsoFiber k ≪≫
    subschemeIsoOfKerEq _ (centralFibreIdeal k) (ker_fiberι_originPoint k)

/-- The identification of the Fermat cubic with `V(t)` is compatible with the inclusions into
`Y`. -/
@[reassoc]
theorem centralFibreIso_hom_subschemeι :
    (centralFibreIso k).hom ≫ (centralFibreIdeal k).subschemeι = fermatToCubicSurface k := by
  rw [centralFibreIso, Iso.trans_hom, Category.assoc, subschemeIsoOfKerEq_hom_subschemeι,
    fermatCurveIsoFiber_hom_fiberι]

/-- **The support of `Y₀` is the set-theoretic fibre over the origin.** -/
theorem coe_support_centralFibreIdeal :
    ((centralFibreIdeal k).support : Set (cubicSurface k)) =
      cubicSurfaceToLine k ⁻¹' {originPoint k} := by
  rw [← ker_fiberι_originPoint, Scheme.Hom.support_ker, Scheme.Hom.range_fiberι]
  exact ((isClosed_originPoint k).preimage (cubicSurfaceToLine k).continuous).closure_eq

/-- A point lies on `Y₀` exactly when it lies over the origin. -/
theorem mem_support_centralFibreIdeal_iff (z : cubicSurface k) :
    z ∈ (centralFibreIdeal k).support ↔ cubicSurfaceToLine k z = originPoint k := by
  rw [← SetLike.mem_coe, coe_support_centralFibreIdeal]
  rfl

/-- **The function `t` on `Y` is nonzero**: otherwise every point would lie over the origin,
whereas the fibre over the generic point of the affine line is infinite. -/
theorem cubicSurfaceCoordinate_ne_zero [Infinite k] : cubicSurfaceCoordinate k ≠ 0 := by
  intro h
  let s : affineLine k := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨z, hz⟩ := (infinite_setOf_cubicSurfaceToLine_eq k s).nonempty
  have hzI : z ∈ (centralFibreIdeal k).support := by
    rw [centralFibreIdeal_eq, Stacks.Divisors.mem_support_ofIdealTop_span_singleton_iff, h,
      map_zero]
    exact not_isUnit_zero
  rw [mem_support_centralFibreIdeal_iff] at hzI
  have hs : s = originPoint k := (show cubicSurfaceToLine k z = s from hz).symm.trans hzI
  have h0 : (⊥ : Ideal (Polynomial k)) = Ideal.span {Polynomial.X} :=
    congrArg PrimeSpectrum.asIdeal hs
  exact Polynomial.X_ne_zero (Ideal.span_singleton_eq_bot.mp h0.symm)

/-- **`Y₀ = V(t)` is an effective Cartier divisor**: on every affine open `U` its ideal is
generated by the restriction of `t`, which is nonzero in the domain `Γ(Y, U)`. -/
theorem isEffectiveCartierDivisor_centralFibreIdeal [Infinite k] :
    IsEffectiveCartierDivisor (centralFibreIdeal k) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem x
  have : Nonempty (U : (cubicSurface k).Opens) := ⟨⟨x, hxU⟩⟩
  refine ⟨U, U.2, hxU, _, IsRegular.of_ne_zero fun h0 => cubicSurfaceCoordinate_ne_zero k ?_,
    Stacks.Divisors.ideal_ofIdealTop_span_singleton _ U⟩
  exact map_injective_of_isIntegral (cubicSurface k) (homOfLE le_top)
    (h0.trans (map_zero _).symm)

/-- The cubic surface is Noetherian: it is of finite type and quasi-compact over the affine
line. -/
instance isNoetherian_cubicSurface : IsNoetherian (cubicSurface k) := by
  have : IsLocallyNoetherian (cubicSurface k) :=
    LocallyOfFiniteType.isLocallyNoetherian (cubicSurfaceToLine k)
  have : CompactSpace (cubicSurface k) :=
    QuasiCompact.compactSpace_of_compactSpace (cubicSurfaceToLine k)
  exact {}

/-- `Y₀` is nonempty in characteristic other than three. -/
theorem nonempty_subscheme_centralFibreIdeal {k : Type u} [Field k] (h3 : ringChar k ≠ 3) :
    Nonempty (centralFibreIdeal k).subscheme :=
  have := nonempty_fermatCurve h3
  ⟨(centralFibreIso k).hom (Classical.arbitrary _)⟩

/-- **`Y₀` is integral**, being the Fermat cubic. -/
theorem isIntegral_subscheme_centralFibreIdeal [IsAlgClosed k] (h3 : ringChar k ≠ 3) :
    IsIntegral (centralFibreIdeal k).subscheme := by
  have := isCurve_fermatCurveToSpec k h3
  have := nonempty_subscheme_centralFibreIdeal h3
  exact isIntegral_of_isOpenImmersion (centralFibreIso k).inv

/-- **`Y₀` is regular**, being isomorphic to the Fermat cubic, which is smooth over `k`. -/
theorem isRegular_subscheme_centralFibreIdeal [IsAlgClosed k] (h3 : ringChar k ≠ 3) :
    AlgebraicGeometry.IsRegular (centralFibreIdeal k).subscheme := by
  have := smooth_fermatCurveToSpec k h3
  exact IsRegular.of_iso (centralFibreIso k).symm
    (isRegular_of_smooth_over_field (fermatCurveToSpec k))

/-- The kernel of the map of local rings `𝒪_{Y,y} ⟶ 𝒪_{Y₀,y}` is generated by the germ of
`t`. -/
theorem ker_stalkMap_subschemeι_centralFibreIdeal (y₀ : (centralFibreIdeal k).subscheme) :
    RingHom.ker ((centralFibreIdeal k).subschemeι.stalkMap y₀).hom =
      Ideal.span {((cubicSurface k).presheaf.Γgerm ((centralFibreIdeal k).subschemeι y₀)
        (cubicSurfaceCoordinate k))} := by
  obtain ⟨U, hU⟩ := Stacks.Divisors.exists_affineOpens_mem ((centralFibreIdeal k).subschemeι y₀)
  rw [IdealSheafData.ker_stalkMap_subschemeι, IdealSheafData.stalk_eq_map_germ _ _ U hU,
    show (centralFibreIdeal k).ideal U = _ from
      Stacks.Divisors.ideal_ofIdealTop_span_singleton (cubicSurfaceCoordinate k) U, Ideal.map_span,
    Set.image_singleton, TopCat.Presheaf.germ_res_apply]
  rfl

/-- **`t` is a regular parameter at every point of `Y₀`**: its germ does not lie in the square
of the maximal ideal. The quotient `𝒪_{Y,y}/(t) = 𝒪_{Y₀,y}` is regular because `Y₀` is, and `t`
is a nonzero element of the maximal ideal of the regular local domain `𝒪_{Y,y}`. -/
theorem Γgerm_cubicSurfaceCoordinate_notMem_sq [IsAlgClosed k] (h3 : ringChar k ≠ 3)
    (y : cubicSurface k) (hy : cubicSurfaceToLine k y = originPoint k) :
    (cubicSurface k).presheaf.Γgerm y (cubicSurfaceCoordinate k) ∉
      maximalIdeal ((cubicSurface k).presheaf.stalk y) ^ 2 := by
  have hyI : y ∈ (centralFibreIdeal k).support :=
    (mem_support_centralFibreIdeal_iff k y).mpr hy
  have hnu : ¬ IsUnit ((cubicSurface k).presheaf.Γgerm y (cubicSurfaceCoordinate k)) :=
    (Stacks.Divisors.mem_support_ofIdealTop_span_singleton_iff (cubicSurfaceCoordinate k) y).mp hyI
  obtain ⟨y₀, rfl⟩ : y ∈ Set.range (centralFibreIdeal k).subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  have := isRegularLocalRing_stalk_cubicSurface k h3 ((centralFibreIdeal k).subschemeι y₀)
  have hreg₀ : IsRegularLocalRing ((centralFibreIdeal k).subscheme.presheaf.stalk y₀) :=
    (isRegular_subscheme_centralFibreIdeal k h3).isRegularLocalRing_stalk y₀
  have hq := IsRegularLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective
    ((centralFibreIdeal k).subschemeι.stalkMap_surjective y₀)).symm
  rw [ker_stalkMap_subschemeι_centralFibreIdeal] at hq
  refine notMem_maximalIdeal_sq_of_isRegularLocalRing_quotient ?_ ?_ hq
  · exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
  · intro h0
    exact cubicSurfaceCoordinate_ne_zero k
      (germ_injective_of_isIntegral _ (U := ⊤) _ trivial (h0.trans (map_zero _).symm))

/-! ### The chosen point -/

/-- **The point `y` of property (2) of [Stacks, Tag 0D5E]**: a closed point of `Y` over the
origin such that every closed subset `T ≠ Y` surjecting onto the affine line meets the central
fibre in a point other than `y` (`exists_point_forall_isClosed_surjective_exists_ne`). -/
def chosenPoint [IsAlgClosed k] [Uncountable k] (h3 : ringChar k ≠ 3) : cubicSurface k :=
  Classical.choose (exists_point_forall_isClosed_surjective_exists_ne k h3)

variable [IsAlgClosed k] [Uncountable k] (h3 : ringChar k ≠ 3)

/-- The chosen point is closed. -/
theorem isClosed_chosenPoint : IsClosed ({chosenPoint k h3} : Set (cubicSurface k)) :=
  (Classical.choose_spec (exists_point_forall_isClosed_surjective_exists_ne k h3)).1

/-- The chosen point lies over the origin. -/
theorem cubicSurfaceToLine_chosenPoint : cubicSurfaceToLine k (chosenPoint k h3) = originPoint k :=
  (Classical.choose_spec (exists_point_forall_isClosed_surjective_exists_ne k h3)).2.1

/-- **Property (2) of [Stacks, Tag 0D5E] for the chosen point.** -/
theorem exists_ne_chosenPoint_of_isClosed_surjective (T : Set (cubicSurface k)) (hT : IsClosed T)
    (hTne : T ≠ Set.univ) (hTsurj : ∀ s : affineLine k, ∃ z ∈ T, cubicSurfaceToLine k z = s) :
    ∃ z ∈ T, cubicSurfaceToLine k z = originPoint k ∧ z ≠ chosenPoint k h3 :=
  (Classical.choose_spec (exists_point_forall_isClosed_surjective_exists_ne k h3)).2.2 T hT hTne
    hTsurj

/-- The chosen point lies on the central fibre `Y₀`. -/
theorem chosenPoint_mem_support_centralFibreIdeal :
    chosenPoint k h3 ∈ (centralFibreIdeal k).support :=
  (mem_support_centralFibreIdeal_iff k _).mpr (cubicSurfaceToLine_chosenPoint k h3)

/-- **`t` is a regular parameter at the chosen point.** -/
theorem Γgerm_cubicSurfaceCoordinate_chosenPoint_notMem_sq :
    (cubicSurface k).presheaf.Γgerm (chosenPoint k h3) (cubicSurfaceCoordinate k) ∉
      maximalIdeal ((cubicSurface k).presheaf.stalk (chosenPoint k h3)) ^ 2 :=
  Γgerm_cubicSurfaceCoordinate_notMem_sq k h3 _ (cubicSurfaceToLine_chosenPoint k h3)

end Stacks.Examples.CurveFamilyNotScheme

end
