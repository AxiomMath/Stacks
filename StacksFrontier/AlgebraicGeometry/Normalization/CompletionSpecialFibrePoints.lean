module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective

/-!
# Closed points of the special fibre after base change to the completion

Let `A` be a Noetherian local ring, let `X` be a scheme over `A`, and let `Y` be the base change
of `X` to the completion `A^` of `A` at its maximal ideal. Because `A` and `A^` have the same
quotient by the maximal ideal, the projection `p : Y ⟶ X` has a one-point reduced fibre over
every point of the special fibre of `X`. Consequently a closed point `y` of `Y` lying over the
special fibre is the only point of `Y` above `x = p(y)`, the point `x` is closed in `X`, and the
reduced closed subscheme supported at `y` is the inverse image of the one supported at `x`.

## Main results

* `AlgebraicGeometry.isIso_fiberToSpecResidueField_of_isPullback_adicCompletion`: over a point of
  the special fibre, the fibre of the projection from the completed base change is the spectrum
  of the residue field.
* `AlgebraicGeometry.isClosed_singleton_and_comap_vanishingIdeal`: for a flat morphism whose
  fibres over the closure of a point are spectra of residue fields, a closed point upstairs has a
  closed image, is alone in its fibre, and its vanishing ideal sheaf is the inverse image of the
  vanishing ideal sheaf of its image.

## Implementation notes

The comparison of the two reduced points is made through the scheme-theoretic fibre rather than
affine-locally: the fibre of `p` over `x` is the pullback of the spectrum of the residue field at
`x`, so the inverse image of the vanishing ideal at `x` is the kernel of the fibre inclusion, and
that kernel is computed by the vanishing ideal of the closure of its range as soon as the fibre is
reduced.

Closedness of `x` is obtained from closedness of `y` by lifting generalizations: a flat morphism
is generalizing, so a point specializing from `x` would acquire a preimage specializing from `y`,
which must be `y` itself.

The three private statements about the completion of a ring mirror helpers used in the proof of
Stacks tag 0BG9.

## References

* [Stacks Project, Tag 0BGA](https://stacks.math.columbia.edu/tag/0BGA)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing TensorProduct

universe w v u

namespace AlgebraicGeometry

/-! ### Kernels of morphisms with reduced source -/

/-- The kernel of the canonical morphism from the spectrum of the residue field at a closed point
is the vanishing ideal sheaf of that point. -/
theorem fromSpecResidueField_ker_eq_vanishingIdeal {Y : Scheme.{u}} (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    (Y.fromSpecResidueField y).ker = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ := by
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  congr 1
  apply Closeds.ext
  rw [Closeds.coe_closure, Scheme.range_fromSpecResidueField]
  exact hy.closure_eq

/-! ### Fibres of a base change to the completion -/

/-- If `S` is flat over `R` and has the same quotient by `I`, then base change to `S` is bijective
on every `R`-algebra in which the image of `I` is nilpotent. -/
theorem tensorProduct_includeLeft_bijective_of_isNilpotent_ideal_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (B : Type (max u v w)) [CommRing B] [Algebra R B]
    (hI : IsNilpotent (I.map (algebraMap R B))) :
    Function.Bijective (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S) := by
  obtain ⟨n, hn⟩ := hI
  have hM : IsIPowerTorsion R B I := by
    intro b
    refine ⟨n + 1, Nat.succ_pos _, fun a ha => ?_⟩
    have hmem : algebraMap R B a ∈ (I.map (algebraMap R B)) ^ n := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (Ideal.pow_le_pow_right (Nat.le_succ n) ha)
    rw [hn] at hmem
    rw [Algebra.smul_def, Ideal.mem_bot.mp hmem, zero_mul]
  exact (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective
    R S I hflat).2 hq B hM

/-- At a prime containing `I`, the fibre of `Spec S → Spec R` is the spectrum of the residue
field, because `S` is flat over `R` with the same quotient by `I`. -/
theorem isIso_fiber_of_flat_quotient_iso
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (x : PrimeSpectrum R) (hx : I ≤ x.asIdeal) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberToSpecResidueField x) := by
  apply ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (Spec.fiberToSpecResidueFieldIso R S x)).mpr
  apply isIso_SpecMap_iff.mpr
  apply tensorProduct_includeLeft_bijective_of_isNilpotent_ideal_map I hflat hq
  have hI : I.map (algebraMap R x.asIdeal.ResidueField) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.ker_algebraMap_residueField]
    exact hx
  rw [hI]
  exact ⟨1, by simp⟩

/-- The fibre of a base change of `Spec S ⟶ Spec R` over a point whose prime contains `I` is the
spectrum of the residue field at that point. -/
theorem isIso_fiberToSpecResidueField_of_isPullback
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of R)} {p : Y ⟶ X} {q : Y ⟶ Spec (.of S)}
    (hsq : IsPullback p q f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (x : X) (hx : I ≤ (f.base x).asIdeal) :
    IsIso (p.fiberToSpecResidueField x) := by
  have hiso : MorphismProperty.isomorphisms Scheme
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberToSpecResidueField (f.base x)) :=
    isIso_fiber_of_flat_quotient_iso I hflat hq (f.base x) hx
  exact (MorphismProperty.isomorphisms Scheme).of_isPullback
    (isPullback_fiberToSpecResidueField_of_isPullback hsq.flip x) hiso

/-- The completion of a Noetherian local ring is flat over it. -/
private instance flat_adicCompletion (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : Module.Flat A (AdicCompletion (maximalIdeal A) A) :=
  have : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (by rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
  inferInstance

/-- Over a point of the special fibre, the fibre of the projection from the base change of `X` to
the completion of a Noetherian local ring `A` is the spectrum of the residue field. -/
theorem isIso_fiberToSpecResidueField_of_isPullback_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)} {p : Y ⟶ X}
    {q : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))}
    (hsq : IsPullback p q f (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (maximalIdeal A) A)))))
    (x : X) (hx : maximalIdeal A ≤ (f.base x).asIdeal) :
    IsIso (p.fiberToSpecResidueField x) :=
  isIso_fiberToSpecResidueField_of_isPullback (maximalIdeal A) inferInstance
    (AdicCompletion.quotientMap_bijective _ (IsNoetherian.noetherian _)) hsq x hx

/-! ### Points with one-point fibres -/

/-- A fibre which is the spectrum of the residue field at the point consists of a single point,
so the set-theoretic fibre there is a singleton. -/
theorem exists_preimage_eq_singleton_of_isIso_fiberToSpecResidueField
    {X Y : Scheme.{u}} (p : Y ⟶ X) (x : X) (h : IsIso (p.fiberToSpecResidueField x)) :
    ∃ y : Y, p.base ⁻¹' {x} = {y} := by
  have hinj : Function.Injective (p.fiberToSpecResidueField x).base :=
    (p.fiberToSpecResidueField x).isOpenEmbedding.injective
  have hsub : Subsingleton (p.fiber x) :=
    ⟨fun a b => hinj (by
      rw [Scheme.Hom.fiberToSpecResidueField_apply, Scheme.Hom.fiberToSpecResidueField_apply])⟩
  obtain ⟨z⟩ : Nonempty (p.fiber x) :=
    ⟨(asIso (p.fiberToSpecResidueField x)).inv.base (closedPoint (X.residueField x))⟩
  refine ⟨(p.fiberι x).base z, ?_⟩
  rw [← p.range_fiberι x]
  exact Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨z, rfl⟩, fun a ha => by obtain ⟨b, rfl⟩ := ha; rw [hsub.elim b z]⟩

/-- The fibre of a morphism over a point at which it is the spectrum of the residue field is
reduced. -/
theorem isReduced_fiber_of_isIso_fiberToSpecResidueField
    {X Y : Scheme.{u}} (p : Y ⟶ X) (x : X) (h : IsIso (p.fiberToSpecResidueField x)) :
    IsReduced (p.fiber x) :=
  isReduced_of_isOpenImmersion (p.fiberToSpecResidueField x)

/-- A point mapping to `x` is the unique point of the fibre over `x`, if that fibre is `{y}`. -/
private theorem eq_of_preimage_eq_singleton {X Y : Scheme.{u}} {p : Y ⟶ X} {x : X} {y y' : Y}
    (hxy : p.base ⁻¹' {x} = {y}) (h : p.base y' = x) : y' = y :=
  Set.mem_singleton_iff.mp (hxy ▸ h)

/-- If a flat morphism has nonempty fibres over every specialization of a point `x`, and some
closed point `y` is alone in the fibre over `x`, then `x` is closed. -/
theorem isClosed_singleton_of_flat {X Y : Scheme.{u}} (p : Y ⟶ X) [Flat p] {x : X} {y : Y}
    (hxy : p.base ⁻¹' {x} = {y}) (hy : IsClosed ({y} : Set Y))
    (hfib : ∀ x' ∈ closure ({x} : Set X), (p.base ⁻¹' {x'}).Nonempty) :
    IsClosed ({x} : Set X) := by
  rw [← closure_eq_iff_isClosed]
  refine subset_antisymm (fun x' hx' => ?_) subset_closure
  obtain ⟨y', hy'⟩ := hfib x' hx'
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hy'
  obtain ⟨y₀, hy₀, hpy₀⟩ := Flat.generalizingMap p (a := y') (b := x)
    (by rw [hy']; exact specializes_iff_mem_closure.mpr hx')
  have hmem : y' ∈ closure ({y} : Set Y) := by
    rw [← eq_of_preimage_eq_singleton hxy hpy₀]
    exact specializes_iff_mem_closure.mp hy₀
  rw [hy.closure_eq, Set.mem_singleton_iff] at hmem
  have hpy : p.base y = x := (Set.ext_iff.mp hxy y).mpr rfl
  rw [Set.mem_singleton_iff, ← hy', hmem, hpy]

/-- The inverse image of the reduced point at `x` along a morphism whose fibre over `x` is the
spectrum of the residue field is the reduced point at the unique preimage of `x`. -/
theorem comap_vanishingIdeal_singleton_of_isIso_fiberToSpecResidueField
    {X Y : Scheme.{u}} (p : Y ⟶ X) {x : X} {y : Y}
    (h : IsIso (p.fiberToSpecResidueField x)) (hxy : p.base ⁻¹' {x} = {y})
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set Y)) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap p
      = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have : IsReduced (p.fiber x) := isReduced_fiber_of_isIso_fiberToSpecResidueField p x h
  have hcl : Closeds.closure (Set.range (p.fiberι x).base) = (⟨{y}, hy⟩ : Closeds Y) :=
    Closeds.ext (by rw [Closeds.coe_closure, p.range_fiberι x, hxy]; exact hy.closure_eq)
  rw [← fromSpecResidueField_ker_eq_vanishingIdeal x hx,
    ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (X.fromSpecResidueField x) p]
  show (p.fiberι x).ker = _
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hcl]

/-- For a flat morphism whose fibres over the closure of the image of a closed point `y` are
spectra of residue fields, the image `p y` is closed, `y` is alone above it, and the reduced
point at `y` is the inverse image of the reduced point at `p y`. -/
theorem isClosed_singleton_and_comap_vanishingIdeal {X Y : Scheme.{u}} (p : Y ⟶ X) [Flat p]
    {y : Y} (hy : IsClosed ({y} : Set Y))
    (hfib : ∀ x' ∈ closure ({p.base y} : Set X), IsIso (p.fiberToSpecResidueField x')) :
    ∃ hx : IsClosed ({p.base y} : Set X), p.base ⁻¹' {p.base y} = {y} ∧
      (Scheme.IdealSheafData.vanishingIdeal ⟨{p.base y}, hx⟩).comap p
        = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ := by
  have hself : p.base y ∈ closure ({p.base y} : Set X) := subset_closure rfl
  obtain ⟨y', hy'⟩ := exists_preimage_eq_singleton_of_isIso_fiberToSpecResidueField p
    (p.base y) (hfib _ hself)
  obtain rfl := eq_of_preimage_eq_singleton hy' rfl
  have hx : IsClosed ({p.base y} : Set X) := by
    refine isClosed_singleton_of_flat p hy' hy fun x' hx' => ?_
    obtain ⟨y'', hy''⟩ := exists_preimage_eq_singleton_of_isIso_fiberToSpecResidueField p x'
      (hfib x' hx')
    exact ⟨y'', by rw [hy'']; exact rfl⟩
  exact ⟨hx, hy', comap_vanishingIdeal_singleton_of_isIso_fiberToSpecResidueField p
    (hfib _ hself) hy' hx hy⟩

end AlgebraicGeometry

end
