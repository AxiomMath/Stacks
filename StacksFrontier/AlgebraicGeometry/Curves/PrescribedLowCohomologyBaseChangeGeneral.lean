module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDown
public import StacksFrontier.AlgebraicGeometry.Curves.PointTwistDown
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomology
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Scheme.ClosedPointRationalPoint
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.OffDiagonalIncidenceVariety
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RationalPointHyperplane
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyBaseChange

/-!
# Twisting an invertible sheaf on a base-changed curve to prescribed low cohomology

Let `k` be a separably closed field, `X` a smooth projective curve over `k`, `K/k` a field
extension and `𝓛` an invertible sheaf on `X_K`. [Stacks, Tag 0B9Y] says there is an invertible
sheaf `𝓛₀` on `X` with

`dim_K H⁰(X_K, 𝓛 ⊗ 𝓛₀|_{X_K}) = 1` and `dim_K H¹(X_K, 𝓛 ⊗ 𝓛₀|_{X_K}) = 0`.

The source calls its proof "a variant of the proof of Varieties, Tag 0B8Z" and runs it in three
movements, all of which are proved here:

1. **The start.** Twist `𝓛` by a high power of an ample invertible sheaf `𝓐` on `X` so that `H¹`
   vanishes (Tag 0B5U) and `H⁰ ≠ 0`. Here `𝓐` comes from Tag 09ND, its pullback to `X_K` is ample
   because `X_K ⟶ X` is affine, and Serre vanishing on `X_K` (clause (4) of Tag 0B5T) is applied
   to the two coherent modules `𝓛` and `ℐ ⊗ 𝓛`, `ℐ` the ideal sheaf of the fibre of `X_K ⟶ X`
   over a `k`-rational point. The second vanishing makes `H⁰` of the twist surject onto `H⁰` of
   its restriction to that fibre, which is a line; this is the source's "the nonvanishing because
   the degree of the tensor product is `≫ 0`", without a degree.
2. **The descending induction** on `t = dim_K H⁰(X_K, 𝓛)`, the case `t = 1` being the assertion.
3. **The step.** For `t > 1` pick a nonzero section `s`; the `k`-rational points of `X` are dense
   (Tag 056U, since a finite separable extension of a separably closed field is trivial) and
   `X_K ⟶ X` is open, so `s` does not vanish at some point of `X_K` over a `k`-rational point
   `x`. The ideal sheaf `ℐ_x` is invertible (Tag 0B8Y, `𝒪_{X,x}` being a discrete valuation
   ring) and pulls back along the flat `X_K ⟶ X` to the ideal sheaf of the fibre `x_K`
   (`Stacks.Divisors.pullbackIdealSheafComapIso`), and `x_K` is a single `K`-rational point. The
   sequence `0 ⟶ ℐ_{x_K} ⊗ 𝓛 ⟶ 𝓛 ⟶ i_*i^*𝓛 ⟶ 0` drops `dim H⁰` by one and keeps `H¹ = 0`, and
   `ℐ_{x_K} ⊗ (𝓛 ⊗ 𝓛₀|_{X_K}) ≅ 𝓛 ⊗ (ℐ_x ⊗ 𝓛₀)|_{X_K}` is again a twist from `X`.

## Main definitions

* `AlgebraicGeometry.baseChangeTwist`: the twist `M ⊗_{𝒪_{X'}} p^*L₀` of a module on `X'` by the
  inverse image of a module on `X`.
* `AlgebraicGeometry.HasPrescribedLowCohomology`: vanishing `H¹` together with a
  finite-dimensional `H⁰` of a given dimension.

## Main results

* `AlgebraicGeometry.dense_isRationalPoint_of_isSepClosed`: Tag 056U over a separably closed
  field, in the form "closed rational points are dense".
* `AlgebraicGeometry.exists_section_of_isSepClosed`: a rational point as a section, the first
  sentence of the proof of Tag 0B9Z.
* `AlgebraicGeometry.isIso_subschemeι_comap_ker_ptOfIsRationalPoint`: the fibre of `X_K ⟶ X`
  over a rational point is `Spec K`.
* `AlgebraicGeometry.baseChangeTwistIdealIso`: `L ⊗ p^*(ℐ_D ⊗ L₀) ≅ ℐ_{p^{-1}D} ⊗ (L ⊗ p^*L₀)`.
* `AlgebraicGeometry.exists_hasPrescribedLowCohomology_succ`: movement 1.
* `AlgebraicGeometry.exists_hasPrescribedLowCohomology_of_succ_succ`: movement 3.
* `AlgebraicGeometry.exists_hasPrescribedLowCohomology_one_of_succ`: movement 2.
* `AlgebraicGeometry.exists_invertible_baseChangeTwist_finrank_cohomologyOverField_eq_one'`:
  **Stacks Tag 0B9Y.**

## Implementation notes

`X_K` is an abstract pullback square, which is this repository's idiom for extension of the
ground field — compare `AlgebraicGeometry.finrank_cohomologyOverField_baseChange_field` and
`AlgebraicGeometry.genus_baseChange`. The inverse image of a module is
`AlgebraicGeometry.Scheme.Modules.pullback` and the tensor product is
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, the spelling across which the
invertibility class `Stacks.Ample.IsInvertibleModule` is found by instance search.

The sequence `0 ⟶ ℐ ⊗ M ⟶ M ⟶ i_*i^*M ⟶ 0` is `Stacks.Divisors.exists_shortExact_invertibleTwist`,
stated in the category `SheafOfModules (structureSheafRing X.toRingedSpace)`; it is the same
category as `X.Modules` but instance search and `rw` do not cross the two spellings, so the
sequence is restated once, in `X.Modules`, as
`AlgebraicGeometry.exists_shortExact_tensorModules_idealSheafOfModules`, with the unit of the
pullback--pushforward adjunction named `AlgebraicGeometry.closedSubschemeUnit`.

The rational point is used through its `k`-point `AlgebraicGeometry.ptOfIsRationalPoint`, whose
kernel is the ideal sheaf of the point (the source scheme `Spec k` being reduced). Its base change
along `X_K ⟶ X` is a closed immersion whose kernel is the pullback of that ideal sheaf
(`AlgebraicGeometry.Scheme.IdealSheafData.ker_fst_of_isClosedImmersion`), and pasting the two
pullback squares identifies its source with `Spec K`.

The genus `g` of the source is not a parameter: it occurs in neither the assertion nor the
proof, so a genus binder would be unconstrained. Vanishing of `H¹` is recorded inside
`AlgebraicGeometry.HasPrescribedLowCohomology` as `CategoryTheory.Limits.IsZero`, which is
exactly the source's `dim_K H¹ = 0`, and is how the tagged statement says it.

## References

* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
* [Stacks Project, Tag 0B8Z](https://stacks.math.columbia.edu/tag/0B8Z)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 0383](https://stacks.math.columbia.edu/tag/0383)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-! ### The twist of a module on the base change by one coming from the base -/


/-! ### The invariant carried by the descending induction -/


/-! ### The cohomology of one step, from Tag 0B8Z's step lemma -/


section RationalPoints

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The ring map `k ⟶ κ(x)` read off the composite `Spec κ(x) ⟶ X ⟶ Spec k` is the evaluation at
`x` of the global functions pulled back from `k`. -/
theorem preimage_fromSpecResidueField_comp_eq_Γevaluation (x : X) :
    Spec.preimage (X.fromSpecResidueField x ≫ f) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x := by
  rw [Spec.preimage_fromSpecResidueField_comp, ← Category.assoc,
    Scheme.Spec.algebraMap_residueFieldIso_inv, Category.assoc, Category.assoc,
    ← Scheme.Γevaluation_naturality]
  rfl

/-- **Over a separably closed field a point with finite separable residue field is rational.** -/
theorem isRationalPoint_of_isSeparable [IsSepClosed k] (x : X)
    (hsep : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField x)) :
    IsRationalPoint f x := by
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  unfold IsRationalPoint
  rw [preimage_fromSpecResidueField_comp_eq_Γevaluation, ConcreteCategory.isIso_iff_bijective]
  exact ⟨RingHom.injective _, IsSepClosed.algebraMap_surjective k (X.residueField x)⟩

/-- **Stacks Tag 056U over a separably closed field.** The closed rational points of a scheme
smooth over a separably closed field are dense. -/
@[ega "IV 17.15.10" "special case", sga "6 X 7.18.2" "(a), special case"]
theorem dense_isRationalPoint_of_isSepClosed [IsSepClosed k] [Smooth f] :
    Dense {x : X | IsClosed ({x} : Set X) ∧ IsRationalPoint f x} :=
  (dense_closedPoints_with_finite_separable_residueField_of_smooth f).mono
    fun x hx => ⟨hx.1, isRationalPoint_of_isSeparable f x hx.2.2⟩

/-- **A nonempty scheme smooth over a separably closed field has a rational point**, given as a
section of its structure morphism through a closed point. This is the first sentence of the
proof of [Stacks, Tag 0B9Z] ("Since `k` is separably closed there exists a `k`-rational point
`σ` of `X`"), which together with [Stacks, Tag 0B9U]
(`AlgebraicGeometry.isIso_c_baseChange_of_isCurve_of_section`) supplies the hypotheses of
[Stacks, Tag 0B9N]. -/
@[sga "6 X 7.18.2" "(a), special case"]
theorem exists_section_of_isSepClosed [IsSepClosed k] [Smooth f] [Nonempty X] :
    ∃ σ : Spec (.of k) ⟶ X, σ ≫ f = 𝟙 _ ∧ IsClosed (Set.range σ.base) := by
  obtain ⟨x, hxc, hx⟩ := (dense_isRationalPoint_of_isSepClosed f).nonempty
  refine ⟨ptOfIsRationalPoint f x hx, ptOfIsRationalPoint_comp f x hx, ?_⟩
  have hr := range_ptOfIsRationalPoint f _ hx
  rw [hr]
  exact hxc

end RationalPoints

/-! ### One-dimensionality of `H⁰` of an invertible module over a point -/

/-- **On a scheme isomorphic over `K` to `Spec K`, every invertible module has a
one-dimensional space of global sections.** The scheme is a single point, so the module is
trivial, and its sections are `Γ(Z, 𝒪_Z) ≅ K`. -/
theorem finrank_cohomologyOverField_zero_eq_one_of_isIso (K : Type u) [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of K)) [IsIso g] (N : Z.Modules)
    [Stacks.SheafOfModules.IsInvertible Z.presheaf (structureSheafRing Z.toRingedSpace).property
      N] :
    Module.finrank K (cohomologyOverField K g N 0) = 1 := by
  have : Subsingleton (Z : Type u) := (asIso g).hom.homeomorph.injective.subsingleton
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology Z N
  have e' : N ≅ SheafOfModules.unit Z.ringCatSheaf := e
  rw [finrank_cohomologyOverField_eq_of_iso K g e' 0,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
  let : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.toAlgebra
  have : IsIso g.appTop := inferInstanceAs (IsIso (g.app ⊤))
  have hbij : Function.Bijective (algebraMap K Γ(Z, ⊤)) :=
    ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop)
  rw [← (AlgEquiv.ofBijective (Algebra.ofId K Γ(Z, ⊤)) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of K)} {p : X' ⟶ X}
  (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
include hp

/-- If `X'` is the base change of a `k`-scheme `X` along `Spec K → Spec k` for a field extension
`K / k`, then the projection `X' ⟶ X` is affine. -/
theorem isAffineHom_of_isPullback_specMap : IsAffineHom p :=
  MorphismProperty.of_isPullback hp.flip inferInstance

/-- If `X'` is the base change of a `k`-scheme `X` along `Spec K → Spec k` for a field extension
`K / k`, then the projection `X' ⟶ X` is flat. -/
theorem flat_of_isPullback_specMap : Flat p :=
  MorphismProperty.of_isPullback hp.flip inferInstance

/-- If `X'` is the base change of a `k`-scheme `X` along `Spec K → Spec k` for a field extension
`K / k`, then the projection `X' ⟶ X` is universally open. -/
theorem universallyOpen_of_isPullback_specMap : UniversallyOpen p :=
  MorphismProperty.of_isPullback hp.flip inferInstance

/-- If `X'` is the base change of a `k`-scheme `X` along `Spec K → Spec k` for a field extension
`K / k`, and `X` is smooth over `k`, then `X'` is smooth over `K`. -/
theorem smooth_of_isPullback_specMap [Smooth f] : Smooth f' :=
  MorphismProperty.of_isPullback hp inferInstance

/-- If `X'` is the base change of a `k`-scheme `X` along `Spec K → Spec k` for a field extension
`K / k`, and `X` is proper over `k`, then `X'` is proper over `K`. -/
theorem isProper_of_isPullback_specMap [IsProper f] : IsProper f' :=
  MorphismProperty.of_isPullback hp inferInstance

/-- If `X'` is the base change of a `k`-scheme `X` along `Spec K → Spec k` for a field extension
`K / k`, and `X` is smooth over `k`, then `X'` is reduced. -/
theorem isReduced_of_isPullback_specMap [Smooth f] : IsReduced X' :=
  have := smooth_of_isPullback_specMap hp
  isReduced_of_smooth f'

end BaseChange


/-! ### The twist by the ideal sheaf of a point, on the base change -/

section Twist

variable {X X' : Scheme.{u}} (p : X' ⟶ X)

/-- **Twisting by the pullback of an ideal sheaf commutes past the given module.** For an
effective Cartier divisor `D` on `X` whose pullback along `p` is defined,
`L ⊗ p^*(ℐ_D ⊗ L₀) ≅ ℐ_{p^{-1}D} ⊗ (L ⊗ p^*L₀)`. -/
def baseChangeTwistIdealIso (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hD : Stacks.Divisors.IsPullbackDefined p D)
    (L : X'.Modules) (L₀ : X.Modules) :
    baseChangeTwist p L (Stacks.RelativeVeryAmple.tensorModules X
        (Stacks.Divisors.idealSheafOfModules D) L₀) ≅
      Stacks.RelativeVeryAmple.tensorModules X' (Stacks.Divisors.idealSheafOfModules (D.comap p))
        (baseChangeTwist p L L₀) :=
  Stacks.RelativeVeryAmple.tensorModulesMapIso X' (Iso.refl L)
      (Stacks.RelativeVeryAmple.pullbackTensorModulesIso p _ L₀ ≪≫
        Stacks.RelativeVeryAmple.tensorModulesMapIso X'
          (Stacks.Divisors.pullbackIdealSheafComapIso p D hD) (Iso.refl _)) ≪≫
    (Stacks.SheafOfModules.Invertible.tensorProductAssociator X'.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X') _ _ _).symm ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso X'
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding X'.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X') _ _) (Iso.refl _) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductAssociator X'.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X') _ _ _

end Twist

/-! ### The divisor of a rational point, and its base change -/

section Point

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) {f' : X' ⟶ Spec (.of K)} {p : X' ⟶ X}
  {x : X} (hx : IsRationalPoint f x)

/-- The ideal sheaf of a rational point is the kernel of the corresponding `k`-point. -/
theorem ker_ptOfIsRationalPoint (hxc : IsClosed ({x} : Set X)) :
    (ptOfIsRationalPoint f x hx).ker = Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hxc⟩ := by
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  congr 1
  ext y
  have hr := range_ptOfIsRationalPoint f _ hx
  change y ∈ closure (Set.range (ptOfIsRationalPoint f x hx).base) ↔ y ∈ ({x} : Set X)
  rw [hr, hxc.closure_eq]

/-- **The ideal sheaf of a rational point of a smooth curve is invertible.** The local ring at
the point is a discrete valuation ring (Stacks Tag 0B8Y). -/
theorem isEffectiveCartierDivisor_ker_ptOfIsRationalPoint [IsCurve k f] [Smooth f]
    (hxc : IsClosed ({x} : Set X)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (ptOfIsRationalPoint f x hx).ker := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := IsCurve.isDiscreteValuationRing_stalk_of_isClosed k f hxc
  rw [ker_ptOfIsRationalPoint f hx hxc]
  exact isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing hxc

variable (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
include hp

/-- **The fibre of `X_K ⟶ X` over a rational point is a single `K`-rational point**: the closed
subscheme cut out on `X_K` by the ideal sheaf of a rational point of `X` maps isomorphically to
`Spec K`. -/
theorem isIso_subschemeι_comap_ker_ptOfIsRationalPoint :
    IsIso (((ptOfIsRationalPoint f x hx).ker.comap p).subschemeι ≫ f') := by
  set σ := ptOfIsRationalPoint f x hx
  have hσ : IsClosedImmersion σ :=
    isClosedImmersion_of_comp_eq_id f σ (ptOfIsRationalPoint_comp f x hx)
  have h1 : IsPullback (pullback.fst p σ ≫ f') (pullback.snd p σ)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) (σ ≫ f) :=
    (IsPullback.of_hasPullback p σ).paste_horiz hp.flip
  rw [ptOfIsRationalPoint_comp] at h1
  have : IsIso (pullback.fst p σ ≫ f') := h1.isIso_fst_of_isIso
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have : IsIso ((pullback.fst p σ).toImage ≫ (pullback.fst p σ).ker.subschemeι ≫ f') := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    infer_instance
  exact IsIso.of_isIso_comp_left (pullback.fst p σ).toImage _

/-- **`H⁰` of the restriction of an invertible module to the fibre over a rational point is a
line**: the fibre is `Spec K` (`isIso_subschemeι_comap_ker_ptOfIsRationalPoint`), and the
dimension is read on `X_K` through the push-forward along the closed immersion. -/
theorem finrank_cohomologyOverField_pushforward_comap_ker_ptOfIsRationalPoint (M : X'.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property M) :
    Module.finrank K (cohomologyOverField K f'
      ((Scheme.Modules.pushforward ((ptOfIsRationalPoint f x hx).ker.comap p).subschemeι).obj
        ((Scheme.Modules.pullback ((ptOfIsRationalPoint f x hx).ker.comap p).subschemeι).obj M))
      0) = 1 := by
  set C := (ptOfIsRationalPoint f x hx).ker.comap p
  have := isIso_subschemeι_comap_ker_ptOfIsRationalPoint f hx hp
  have : Stacks.SheafOfModules.IsInvertible C.subscheme.presheaf
      (structureSheafRing C.subscheme.toRingedSpace).property
      ((Scheme.Modules.pullback C.subschemeι).obj M) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι M hM
  rw [← (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion K C.subschemeι f'
    ((Scheme.Modules.pullback C.subschemeι).obj M) 0).toLinearEquiv.finrank_eq]
  exact finrank_cohomologyOverField_zero_eq_one_of_isIso K _ _

end Point

/-! ### The sequence of the fibre over a rational point -/

/-- The unit `M ⟶ i_*i^*M` of a closed subscheme, as a morphism of modules of the scheme. -/
abbrev closedSubschemeUnit {Y : Scheme.{u}} (C : Y.IdealSheafData) (M : Y.Modules) :
    M ⟶ (Scheme.Modules.pushforward C.subschemeι).obj
      ((Scheme.Modules.pullback C.subschemeι).obj M) :=
  (modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app M

/-- **The sequence `0 ⟶ ℐ ⊗ M ⟶ M ⟶ i_*i^*M ⟶ 0`** of a closed subscheme `C` with inclusion `i`
and an invertible `M`, read in the category of modules of the scheme. This is
`Stacks.Divisors.exists_shortExact_invertibleTwist`, whose objects live in the other spelling of
the same category. -/
theorem exists_shortExact_tensorModules_idealSheafOfModules {Y : Scheme.{u}} (C : Y.IdealSheafData)
    (M : Y.Modules) (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property M) :
    ∃ (α : Stacks.RelativeVeryAmple.tensorModules Y (Stacks.Divisors.idealSheafOfModules C) M ⟶ M)
      (w : α ≫ closedSubschemeUnit C M = 0),
      (ShortComplex.mk α (closedSubschemeUnit C M) w).ShortExact := by
  obtain ⟨w, hSE⟩ := Stacks.Divisors.exists_shortExact_invertibleTwist C M hM
  exact ⟨_, w, hSE⟩

/-! ### The two movements of the proof of Stacks Tag 0B9Y -/

section Induction

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X X' : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of K)} {p : X' ⟶ X}

/-- **One step of the descending induction of Stacks Tag 0B9Y.** Over a separably closed `k`,
for a smooth curve `X` and its base change `X_K`: if a twist of `L` by an invertible module on
`X` has vanishing `H¹` and `dim_K H⁰ = t + 2`, then another such twist has vanishing `H¹` and
`dim_K H⁰ = t + 1`.

The source's argument: pick a nonzero global section `s`; the rational points of `X` are dense
(Tag 056U, every finite separable residue field being trivial over a separably closed field) and
`X_K ⟶ X` is open, so some `k`-rational point `x` has a point of `X_K` above it at which `s`
does not vanish. The ideal sheaf of `x` is invertible (Tag 0B8Y) and pulls back along the flat
`X_K ⟶ X` to the ideal sheaf `ℐ` of the fibre, which is a single `K`-rational point. Twisting by
it, `0 ⟶ ℐ ⊗ 𝓛 ⟶ 𝓛 ⟶ i_*i^*𝓛 ⟶ 0` drops `dim H⁰` by one and keeps `H¹ = 0`
(`AlgebraicGeometry.hasPrescribedLowCohomology_of_shortExact`), and `ℐ ⊗ 𝓛` is again a twist of
`L` by an invertible module on `X`, namely by `ℐ_x ⊗ 𝓛₀`. -/
theorem exists_hasPrescribedLowCohomology_of_succ_succ [IsSepClosed k] [IsCurve k f] [Smooth f]
    (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (L : X'.Modules) [Stacks.Ample.IsInvertibleModule X' L] (L₀ : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L₀] (t : ℕ)
    (h : HasPrescribedLowCohomology K f' (baseChangeTwist p L L₀) (t + 2)) :
    ∃ L₁ : X.Modules, Stacks.Ample.IsInvertibleModule X L₁ ∧
      HasPrescribedLowCohomology K f' (baseChangeTwist p L L₁) (t + 1) := by
  set M : X'.Modules := baseChangeTwist p L L₀ with hMdef
  have hMinv : Stacks.Ample.IsInvertibleModule X' M :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X' L _
  have hMl : Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property M := hMinv
  -- A nonzero global section of the twist.
  have _ := h.finiteDimensional_zero
  have hpos : 0 < Module.finrank K (cohomologyOverField K f' M 0) := by
    rw [h.finrank_zero]; omega
  have _ : Nontrivial (cohomologyOverField K f' M 0 : Type u) := Module.finrank_pos_iff.mp hpos
  have _ : Nontrivial Γ(M, ⊤) := (cohomologyOverFieldZeroEquivSections K f' M).symm.nontrivial
  obtain ⟨s, hs⟩ := exists_ne (0 : Γ(M, ⊤))
  -- Its nonvanishing locus is a nonempty open of `X_K`.
  have := isReduced_of_isPullback_specMap hp
  have hbridge : Stacks.SheafOfModules.nonvanishingLocus (X := X'.toRingedSpace) M
      (Stacks.SheafOfModules.sectionsOfTop M s) = Stacks.Ample.nonvanishingLocus M s :=
    nonvanishingLocus_sectionsOfTop_eq M s
  have hVo : IsOpen (Stacks.Ample.nonvanishingLocus M s) := by
    rw [← hbridge]
    exact Stacks.SheafOfModules.isOpen_nonvanishingLocus (X := X'.toRingedSpace) M _
  have hVne : (Stacks.Ample.nonvanishingLocus M s).Nonempty :=
    hbridge ▸ nonempty_nonvanishingLocus_of_ne_zero M s hs
  -- Its image in `X` is a nonempty open, so it contains a closed rational point.
  have := universallyOpen_of_isPullback_specMap hp
  have hpo : IsOpen (p.base '' Stacks.Ample.nonvanishingLocus M s) := p.isOpenMap _ hVo
  obtain ⟨x, ⟨z, hzV, rfl⟩, hxc, hx⟩ :=
    (dense_isRationalPoint_of_isSepClosed f).inter_open_nonempty _ hpo (hVne.image _)
  -- The ideal sheaf of `x`, and its pullback to `X_K`.
  set σ := ptOfIsRationalPoint f (p.base z) hx with hσ
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor σ.ker :=
    isEffectiveCartierDivisor_ker_ptOfIsRationalPoint f hx hxc
  have _ := hD
  have := flat_of_isPullback_specMap hp
  have hDef : Stacks.Divisors.IsPullbackDefined p σ.ker :=
    Stacks.Divisors.isPullbackDefined_of_flat p σ.ker hD
  set C : X'.IdealSheafData := σ.ker.comap p with hC
  -- A point of the fibre at which `s` does not vanish.
  obtain ⟨z', hz'⟩ : ∃ z' : C.subscheme, C.subschemeι.base z' = z := by
    have hz : z ∈ Set.range C.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι, hC, Scheme.IdealSheafData.support_comap,
        Scheme.Hom.support_ker_eq_closure_range]
      change p.base z ∈ closure (Set.range σ.base)
      exact subset_closure ⟨IsLocalRing.closedPoint k, ptOfIsRationalPoint_apply f _ hx _⟩
    exact hz
  -- The sequence, with its left-hand term rewritten as a twist of `L` from `X`.
  obtain ⟨α₀, w₀, hSE₀⟩ := exists_shortExact_tensorModules_idealSheafOfModules C M hMl
  set β₀ := closedSubschemeUnit C M
  set e := baseChangeTwistIdealIso p σ.ker hDef L L₀
  have w₁ : (e.hom ≫ α₀) ≫ β₀ = 0 := by rw [Category.assoc, w₀, comp_zero]
  have eS : ShortComplex.mk α₀ β₀ w₀ ≅ ShortComplex.mk (e.hom ≫ α₀) β₀ w₁ :=
    ShortComplex.isoMk e.symm (Iso.refl M) (Iso.refl _) (by simp) (by simp)
  have hSE₁ := ShortComplex.shortExact_of_iso eS hSE₀
  -- The image of `s` on the fibre is nonzero.
  have ha : cohomologyOverFieldMap K f' β₀ 0
      ((cohomologyOverFieldZeroEquivSections K f' M).symm s) ≠ 0 := by
    intro hc
    refine app_top_unit_ne_zero_of_mem_nonvanishingLocus C.subschemeι M s z' (hz' ▸ hzV) ?_
    have key := cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap K f' β₀
      ((cohomologyOverFieldZeroEquivSections K f' M).symm s)
    exact ((congrArg (fun t => (Scheme.Modules.Hom.app β₀ ⊤) t)
          (Equiv.apply_symm_apply (cohomologyOverFieldZeroEquivSections K f' M) s).symm).trans
        (key.symm.trans
          ((congrArg (cohomologyOverFieldZeroEquivSections K f'
              ((Scheme.Modules.pushforward C.subschemeι).obj
                ((Scheme.Modules.pullback C.subschemeι).obj M))) hc).trans
            (cohomologyOverFieldZeroEquivSections_zero K f' _))))
  have hI : Stacks.Ample.IsInvertibleModule X (Stacks.Divisors.idealSheafOfModules σ.ker) := hD
  exact ⟨_, Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X _ L₀,
    hasPrescribedLowCohomology_of_shortExact K f' hSE₁ (t + 1) h
      (finrank_cohomologyOverField_pushforward_comap_ker_ptOfIsRationalPoint f hx hp M hMl) ha⟩

/-- **The descending induction of Stacks Tag 0B9Y.** From a twist of `L` with vanishing `H¹` and
`dim_K H⁰ = t + 1`, `exists_hasPrescribedLowCohomology_of_succ_succ` descends to a twist with
vanishing `H¹` and exactly one independent global section. -/
theorem exists_hasPrescribedLowCohomology_one_of_succ [IsSepClosed k] [IsCurve k f] [Smooth f]
    (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (L : X'.Modules) [Stacks.Ample.IsInvertibleModule X' L] (t : ℕ) (L₀ : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L₀]
    (h : HasPrescribedLowCohomology K f' (baseChangeTwist p L L₀) (t + 1)) :
    ∃ L₁ : X.Modules, Stacks.Ample.IsInvertibleModule X L₁ ∧
      HasPrescribedLowCohomology K f' (baseChangeTwist p L L₁) 1 := by
  induction t generalizing L₀ with
  | zero => exact ⟨L₀, ‹_›, h⟩
  | succ t ih =>
      obtain ⟨L₁, hL₁, h₁⟩ := exists_hasPrescribedLowCohomology_of_succ_succ hp L L₀ t h
      exact ih L₁ h₁

/-- **The start of the induction of Stacks Tag 0B9Y.** Over a separably closed `k`, for a proper
smooth curve `X` and its base change `X_K`, some
twist of `L` by an invertible module on `X` has vanishing `H¹` and a nonzero `H⁰`.

The twist is by a high power `A^{⊗ d}` of an ample invertible module `A` on `X` (Tag 09ND), whose
pullback to `X_K` is ample (`X_K ⟶ X` is affine). Serre vanishing (Tag 0B5U, clause (4) of Tag
0B5T) on `X_K` kills `H¹` of the twists of the two coherent modules `L` and `ℐ ⊗ L`, where `ℐ` is
the ideal sheaf of the fibre of `X_K ⟶ X` over a `k`-rational point. The second vanishing makes
`H⁰(X_K, L ⊗ A^d) ⟶ H⁰(X_K, i_*i^*(L ⊗ A^d))` surjective onto a one-dimensional space, which is
the source's "the nonvanishing because the degree of the tensor product is `≫ 0`". -/
theorem exists_hasPrescribedLowCohomology_succ [IsSepClosed k] [IsCurve k f] [Smooth f]
    [IsProper f] (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (L : X'.Modules) [Stacks.Ample.IsInvertibleModule X' L] :
    ∃ (L₀ : X.Modules) (t : ℕ), Stacks.Ample.IsInvertibleModule X L₀ ∧
      HasPrescribedLowCohomology K f' (baseChangeTwist p L L₀) (t + 1) := by
  -- An ample invertible module on `X`, and its pullback to `X_K`.
  have : AlgebraicGeometry.IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field f
  have : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field f
  obtain ⟨A, hAinv, hA⟩ := Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one X
    (IsCurve.topologicalKrullDim_eq_one (k := k) f)
  have hAinv' : Stacks.Ample.IsInvertibleModule X A := hAinv
  have := isAffineHom_of_isPullback_specMap hp
  have := isProper_of_isPullback_specMap hp
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian f'
  set A' : X'.Modules := (Scheme.Modules.pullback p).obj A
  have hA'inv : Stacks.Ample.IsInvertibleModule X' A' := inferInstance
  have hA'invr : AlgebraicGeometry.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (structureSheafRing X'.toRingedSpace).property A' := hA'inv
  have hA' : Stacks.Ample.IsAmple X' A' :=
    Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X' A'
      (Scheme.Modules.isAmple_pullback_of_isAffineHom p A hA)
  -- A rational point of `X`, and the ideal sheaf of its fibre in `X_K`.
  obtain ⟨x, hxc, hx⟩ := (dense_isRationalPoint_of_isSepClosed f).nonempty
  set σ := ptOfIsRationalPoint f x hx
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor σ.ker :=
    isEffectiveCartierDivisor_ker_ptOfIsRationalPoint f hx hxc
  have := flat_of_isPullback_specMap hp
  have hDef : Stacks.Divisors.IsPullbackDefined p σ.ker :=
    Stacks.Divisors.isPullbackDefined_of_flat p σ.ker hD
  set C : X'.IdealSheafData := σ.ker.comap p
  have hCinv : Stacks.Ample.IsInvertibleModule X' (Stacks.Divisors.idealSheafOfModules C) := hDef
  -- Serre vanishing for `L` and for `ℐ ⊗ L`.
  have : (L).IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X' L
  set F : X'.Modules :=
    Stacks.RelativeVeryAmple.tensorModules X' (Stacks.Divisors.idealSheafOfModules C) L
  have hFinv : Stacks.Ample.IsInvertibleModule X' F :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X' _ L
  have : F.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X' F
  obtain ⟨d₁, h₁⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist f' L A' hA'
  obtain ⟨d₂, h₂⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist f' F A' hA'
  set d : ℕ := max d₁ d₂
  -- The twist `L ⊗ p^*(A^{⊗ d})`, compared with `L ⊗ (p^*A)^{⊗ d}`.
  set L₀ : X.Modules := Stacks.Ample.tensorPowModule X A (d : ℤ)
  set M : X'.Modules := baseChangeTwist p L L₀
  let eM : M ≅ Stacks.RelativeVeryAmple.tensorModules X' L (Stacks.Ample.tensorPowModule X' A' d) :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso X' (Iso.refl L)
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso p A d)
  have hMinv : Stacks.Ample.IsInvertibleModule X' M :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X' L _
  have hMl : Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property M := hMinv
  have : M.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X' M
  -- `H¹(X_K, M) = 0`.
  have hM1 : IsZero (cohomologyOverField K f' M 1) :=
    ((isZero_cohomologyOverField_iff_isZero_hgroup K f' _ 1).mpr
      (h₁ d 1 (le_max_left _ _) Nat.one_pos)).of_iso (cohomologyOverFieldIso K f' eM 1)
  -- `H¹(X_K, ℐ ⊗ M) = 0`.
  let eI : Stacks.RelativeVeryAmple.tensorModules X' (Stacks.Divisors.idealSheafOfModules C) M ≅
      Stacks.RelativeVeryAmple.tensorModules X' F (Stacks.Ample.tensorPowModule X' A' d) :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso X' (Iso.refl _) eM ≪≫
      (Stacks.SheafOfModules.Invertible.tensorProductAssociator X'.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X') _ _ _).symm
  have hI1 : IsZero (cohomologyOverField K f'
      (Stacks.RelativeVeryAmple.tensorModules X' (Stacks.Divisors.idealSheafOfModules C) M) 1) :=
    ((isZero_cohomologyOverField_iff_isZero_hgroup K f' _ 1).mpr
      (h₂ d 1 (le_max_right _ _) Nat.one_pos)).of_iso (cohomologyOverFieldIso K f' eI 1)
  -- The sequence `0 ⟶ ℐ ⊗ M ⟶ M ⟶ i_*i^*M ⟶ 0` makes `H⁰(M)` surject onto a line.
  obtain ⟨α₀, w₀, hSE₀⟩ := exists_shortExact_tensorModules_idealSheafOfModules C M hMl
  have hsurj := surjective_cohomologyOverFieldMap_g_of_isZero_succ_X₁ K f' hSE₀ 0 hI1
  have hone := finrank_cohomologyOverField_pushforward_comap_ker_ptOfIsRationalPoint f hx hp M hMl
  have hfd := finiteDimensional_cohomologyOverField_of_isProper K f' M 0
  have hpos : 1 ≤ Module.finrank K (cohomologyOverField K f' M 0) := by
    rw [← hone]
    exact LinearMap.finrank_range_le (cohomologyOverFieldMap K f' _ 0).hom |>.trans' (by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top])
  refine ⟨L₀, Module.finrank K (cohomologyOverField K f' M 0) - 1,
    Stacks.Ample.isInvertibleModule_tensorPowModule X A d, hM1, hfd, (Nat.sub_add_cancel hpos).symm⟩

end Induction

/-! ### Stacks Tag 0B9Y -/

/-- **Stacks Project, Tag 0B9Y.** Let `k` be a separably closed field, `X` a smooth projective
curve over `k`, `K/k` a field extension and `X' = X_K` the base change. For every invertible
sheaf `L` on `X'` there is an invertible sheaf `L₀` on `X` with

`dim_K H⁰(X', L ⊗ p^*L₀) = 1` and `dim_K H¹(X', L ⊗ p^*L₀) = 0`.

The vanishing of `H¹` is stated as `CategoryTheory.Limits.IsZero`, which is `dim_K H¹ = 0` without
a separate finite-dimensionality clause (`Module.finrank` is also zero on an infinite-dimensional
space); `AlgebraicGeometry.HasPrescribedLowCohomology.finrank_one` recovers the `finrank` form.
The start of the source's descending induction is
`AlgebraicGeometry.exists_hasPrescribedLowCohomology_succ`, the induction is
`AlgebraicGeometry.exists_hasPrescribedLowCohomology_one_of_succ`, and its step is
`AlgebraicGeometry.exists_hasPrescribedLowCohomology_of_succ_succ`. Projectivity enters through
properness (`AlgebraicGeometry.IsProjective.isProper`). The genus `g` of the source occurs in
neither the assertion nor the proof and is not a parameter. -/
public theorem exists_invertible_baseChangeTwist_finrank_cohomologyOverField_eq_one'
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of K)) (p : X' ⟶ X)
    (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [IsCurve k f] [Smooth f] (hproj : IsProjective f)
    (L : X'.Modules) [Stacks.Ample.IsInvertibleModule X' L] :
    ∃ L₀ : X.Modules, Stacks.Ample.IsInvertibleModule X L₀ ∧
      Module.finrank K (cohomologyOverField K f' (baseChangeTwist p L L₀) 0) = 1 ∧
      IsZero (cohomologyOverField K f' (baseChangeTwist p L L₀) 1) := by
  have := hproj.isProper
  obtain ⟨L₀, t, hL₀, h⟩ := exists_hasPrescribedLowCohomology_succ hp L
  obtain ⟨L₁, hL₁, h₁⟩ := exists_hasPrescribedLowCohomology_one_of_succ hp L t L₀ h
  exact ⟨L₁, hL₁, h₁.finrank_zero, h₁.isZero_one⟩

end AlgebraicGeometry

end
