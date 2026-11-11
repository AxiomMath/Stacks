module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.Proper
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurfaceIrreducible
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.TorusChart
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.TorusRingFacts
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.TorusFermatPoints
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.FermatTorusPoint

/-!
# The choice of the point `y` on the central fibre of the cubic surface

This file proves property (2) of the construction of Stacks 0D5E for the cubic surface
`Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` over the affine line: for `k` uncountable and
algebraically closed of characteristic different from three there is a closed point `y` of the
central fibre `Y₀` such that every closed subset `T ≠ Y` surjecting onto the affine line meets
`Y₀` in a point other than `y`.

## The argument

The point is chosen on the torus chart `U = D₊(T₀ T₁ T₂)` of `Y`, which is the spectrum of the
factorial ring `R = k[x, y][1 / (x y)]`, the coordinate `t` being `(1 + x ^ 3 + y ^ 3) / (x y)`
there (`exists_iso_surfaceTorusOpen`); the central fibre meets `U` in the spectrum of
`A = R ⧸ (1 + x ^ 3 + y ^ 3)`. The point `y` corresponds to a maximal ideal `P₀` of `A` which is
the exact zero locus of no element of `A`; that such a `P₀` exists is the choice the source makes
through the Picard group (`exists_isMaximal_forall_not_zeroLocus_eq`, proved on the Fermat curve).

Suppose `T` surjects onto the affine line and meets `Y₀` only in `y`. A point `z₀ ∈ T` over the
generic point of the line has closure `T'` surjecting onto the line, because `Y` is proper over
it; so `y ∈ T'`, and `z₀` lies in `U` and corresponds to a prime `Q` of `R`. It is neither zero
(else `T ⊇ U`, which is dense in the irreducible `Y`) nor maximal (else `T'` would be a point), so
it has height one and `Q = (g)` for a prime element `g` (`exists_prime_eq_span_of_isPrime`). A
prime of `R` containing `1 + x ^ 3 + y ^ 3` and `g` is a point of `T'` over the origin, hence is
`y`; so the image of `g` in `A` vanishes exactly at `P₀`, a contradiction.

The source instead argues that the curve components of `T` form an effective Cartier divisor `D`
with `𝒪_{Y₀}(n y) ≅ 𝒪_Y(D)|_{Y₀}`, and chooses `y` outside the countably many classes so
obtained, `Pic(Y)` being finitely generated. Only the torus chart is needed here: on it `D` is the
principal divisor `(g)`, so its restriction to `Y₀ ∩ U` is principal.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.exists_point_forall_isClosed_surjective_exists_ne`:
  property (2) of Stacks 0D5E.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

/-! ### Points of an affine chart -/

section Chart

variable {Y : Scheme.{u}} {R : Type u} [CommRing R] (U : Y.Opens)
  (e : Spec (CommRingCat.of R) ≅ (U : Scheme.{u}))

/-- The point of `Y` given by a prime of `R`, through a chart `e : Spec R ≅ U`. -/
def chartPoint (p : PrimeSpectrum R) : Y := U.ι (e.hom p)

theorem chartPoint_mem (p : PrimeSpectrum R) : chartPoint U e p ∈ U := by
  rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
  exact ⟨_, rfl⟩

theorem exists_chartPoint_eq {z : Y} (hz : z ∈ U) : ∃ p, chartPoint U e p = z := by
  rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι] at hz
  obtain ⟨w, rfl⟩ := hz
  refine ⟨(Scheme.homeoOfIso e).symm w, ?_⟩
  simp only [chartPoint]
  rw [← Scheme.coe_homeoOfIso, Homeomorph.apply_symm_apply]

theorem chartPoint_injective : Function.Injective (chartPoint U e) :=
  U.ι.isOpenEmbedding.injective.comp (Scheme.homeoOfIso e).injective

theorem chartPoint_specializes_iff (p q : PrimeSpectrum R) :
    chartPoint U e p ⤳ chartPoint U e q ↔ p ≤ q :=
  (U.ι.isOpenEmbedding.isInducing.specializes_iff).trans <|
    ((Scheme.homeoOfIso e).isInducing.specializes_iff (x := (p : Spec (CommRingCat.of R)))
      (y := q)).trans (PrimeSpectrum.le_iff_specializes p q).symm

theorem isClosed_chartPoint_iff [JacobsonSpace Y] (p : PrimeSpectrum R) :
    IsClosed ({chartPoint U e p} : Set Y) ↔ p.asIdeal.IsMaximal := by
  have h1 : IsClosed ({chartPoint U e p} : Set Y) ↔ IsClosed ({e.hom p} : Set U) :=
    Set.ext_iff.mp U.ι.isOpenEmbedding.preimage_closedPoints (e.hom p)
  have h2 : IsClosed ({e.hom p} : Set U) ↔
      IsClosed ({p} : Set (Spec (CommRingCat.of R))) :=
    Set.ext_iff.mp (Scheme.homeoOfIso e).isClosedEmbedding.preimage_closedPoints p
  exact h1.trans (h2.trans (PrimeSpectrum.isClosed_singleton_iff_isMaximal p))

end Chart

/-! ### The torus chart of the cubic surface -/

variable (k : Type u) [Field k]

/-- The generic point of the affine line. -/
def lineGenericPoint : affineLine k := ⟨⊥, Ideal.isPrime_bot⟩

theorem lineGenericPoint_specializes (s : affineLine k) : lineGenericPoint k ⤳ s :=
  (PrimeSpectrum.le_iff_specializes _ _).mp bot_le

theorem lineGenericPoint_ne_originPoint : lineGenericPoint k ≠ originPoint k := by
  intro h
  have hX : (Polynomial.X : Polynomial k) ∈ (originPoint k).asIdeal :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [← h] at hX
  exact Polynomial.X_ne_zero ((Submodule.mem_bot _).mp hX)

/-- The map `k[t] → R`, `t ↦ (1 + x ^ 3 + y ^ 3) / (x y)`, describing the torus chart over the
affine line. -/
abbrev torusLineHom : Polynomial k →+* torusRing k :=
  Polynomial.eval₂RingHom (algebraMap k (torusRing k)) (torusParameter k)

/-- A prime of `R` lies over the origin of the affine line exactly when it contains the affine
Fermat equation. -/
theorem comap_torusLineHom_eq_originPoint_iff (p : PrimeSpectrum (torusRing k)) :
    PrimeSpectrum.comap (torusLineHom k) p = originPoint k ↔ torusFermat k ∈ p.asIdeal := by
  have hF : torusFermat k ∈ p.asIdeal ↔ torusParameter k ∈ p.asIdeal := by
    rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.span_singleton_le_iff_mem,
      span_torusParameter]
  rw [hF]
  have hX : torusLineHom k Polynomial.X = torusParameter k := Polynomial.eval₂_X _ _
  constructor
  · intro h
    have hmem : (Polynomial.X : Polynomial k) ∈ (PrimeSpectrum.comap (torusLineHom k) p).asIdeal :=
      h ▸ Ideal.subset_span (Set.mem_singleton _)
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hX] at hmem
    exact hmem
  · intro h
    have hmax : (originPoint k).asIdeal.IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
    refine PrimeSpectrum.ext (hmax.eq_of_le
      (PrimeSpectrum.comap (torusLineHom k) p).isPrime.ne_top ?_).symm
    rw [originPoint, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hX]
    exact h

/-- **Property (2), from a maximal ideal of the affine central fibre which is the exact zero
locus of no function.** -/
theorem exists_point_forall_isClosed_surjective_exists_ne_of_isMaximal
    (P₀ : Ideal (torusFermatRing k)) (hP₀ : P₀.IsMaximal)
    (hP₀' : ∀ a : torusFermatRing k, ¬ ∀ Q : Ideal (torusFermatRing k), Q.IsPrime →
      (a ∈ Q ↔ Q = P₀)) :
    ∃ y : cubicSurface k, IsClosed ({y} : Set (cubicSurface k)) ∧
      cubicSurfaceToLine k y = originPoint k ∧
      ∀ T : Set (cubicSurface k), IsClosed T → T ≠ Set.univ →
        (∀ s : affineLine k, ∃ z ∈ T, cubicSurfaceToLine k z = s) →
        ∃ z ∈ T, cubicSurfaceToLine k z = originPoint k ∧ z ≠ y := by
  classical
  have : JacobsonSpace (cubicSurface k) :=
    LocallyOfFiniteType.jacobsonSpace (cubicSurfaceToLine k)
  have := irreducibleSpace_cubicSurface k
  set U := surfaceTorusOpen k
  set f := cubicSurfaceToLine k
  obtain ⟨e, he⟩ := exists_iso_surfaceTorusOpen k
  set pt := chartPoint U e
  -- the structure map on the chart
  have hf' : ∀ q : Spec (CommRingCat.of (torusRing k)),
      (cubicSurfaceToLine k) ((surfaceTorusOpen k).ι (e.hom q)) =
        Spec.map (CommRingCat.ofHom (torusLineHom k)) q := fun q => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, he]
  have hf : ∀ p, f (pt p) = PrimeSpectrum.comap (torusLineHom k) p := fun p => hf' p
  have hover : ∀ p : PrimeSpectrum (torusRing k), f (pt p) = originPoint k ↔
      torusFermat k ∈ p.asIdeal := fun p => by
    rw [hf]
    exact comap_torusLineHom_eq_originPoint_iff k p
  -- the chosen point
  set mk := Ideal.Quotient.mk (Ideal.span {torusFermat k})
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have h𝔭max : (P₀.comap mk).IsMaximal := Ideal.comap_isMaximal_of_surjective _ hmk
  set 𝔭 : PrimeSpectrum (torusRing k) := ⟨P₀.comap mk, h𝔭max.isPrime⟩
  have hF𝔭 : torusFermat k ∈ 𝔭.asIdeal := by
    change mk (torusFermat k) ∈ P₀
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
    exact P₀.zero_mem
  refine ⟨pt 𝔭, (isClosed_chartPoint_iff U e 𝔭).mpr h𝔭max, (hover 𝔭).mpr hF𝔭, ?_⟩
  intro T hT hTne hTsurj
  by_contra! hcon
  -- a point of `T` over the generic point of the line, and its closure
  obtain ⟨z₀, hz₀T, hz₀⟩ := hTsurj (lineGenericPoint k)
  have hT' : closure {z₀} ⊆ T := hT.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz₀T)
  have hT'surj : ∀ s, ∃ z ∈ closure ({z₀} : Set (cubicSurface k)), f z = s := by
    intro s
    have hcl : IsClosed (f '' closure {z₀}) := f.isClosedMap _ isClosed_closure
    have hmem : f z₀ ∈ f '' closure {z₀} := ⟨z₀, subset_closure rfl, rfl⟩
    rw [hz₀] at hmem
    exact (lineGenericPoint_specializes k s).mem_closed hcl hmem
  -- `y` lies in the closure of `z₀`
  have hspec : z₀ ⤳ pt 𝔭 := by
    obtain ⟨z₁, hz₁, hz₁o⟩ := hT'surj (originPoint k)
    have := hcon z₁ (hT' hz₁) hz₁o
    rw [← this]
    exact specializes_iff_mem_closure.mpr hz₁
  have hz₀U : z₀ ∈ U := hspec.mem_open U.isOpen (chartPoint_mem U e 𝔭)
  obtain ⟨Q, rfl⟩ := exists_chartPoint_eq U e hz₀U
  have hQ𝔭 : Q ≤ 𝔭 := (chartPoint_specializes_iff U e Q 𝔭).mp hspec
  -- `Q` is not zero
  have hQ0 : Q.asIdeal ≠ ⊥ := by
    intro hQ
    apply hTne
    have hUsub : (U : Set (cubicSurface k)) ⊆ T := by
      intro z hz
      obtain ⟨p, rfl⟩ := exists_chartPoint_eq U e hz
      refine hT' (specializes_iff_mem_closure.mp ?_)
      rw [chartPoint_specializes_iff]
      change Q.asIdeal ≤ p.asIdeal
      rw [hQ]
      exact bot_le
    have hdense : Dense (U : Set (cubicSurface k)) :=
      U.isOpen.dense ⟨_, chartPoint_mem U e 𝔭⟩
    exact Set.eq_univ_of_univ_subset (hdense.closure_eq ▸ hT.closure_subset_iff.mpr hUsub)
  -- `Q` is not maximal
  have hQm : ¬ Q.asIdeal.IsMaximal := by
    intro hQ
    have hcl := (isClosed_chartPoint_iff U e Q).mpr hQ
    obtain ⟨z₁, hz₁, hz₁o⟩ := hT'surj (originPoint k)
    rw [hcl.closure_eq, Set.mem_singleton_iff] at hz₁
    rw [hz₁] at hz₁o
    exact lineGenericPoint_ne_originPoint k ((hz₀.symm.trans hz₁o))
  obtain ⟨g, -, hg⟩ := exists_prime_eq_span_of_isPrime k Q.asIdeal hQ0 hQm
  -- a prime containing `g` and the Fermat equation is `𝔭`
  have hkey : ∀ P : PrimeSpectrum (torusRing k), torusFermat k ∈ P.asIdeal →
      (g ∈ P.asIdeal ↔ P = 𝔭) := by
    intro P hFP
    constructor
    · intro hgP
      have hQP : Q ≤ P := by
        change Q.asIdeal ≤ P.asIdeal
        rw [hg, Ideal.span_singleton_le_iff_mem]
        exact hgP
      have hmemT : pt P ∈ T :=
        hT' (specializes_iff_mem_closure.mp ((chartPoint_specializes_iff U e Q P).mpr hQP))
      exact chartPoint_injective U e (hcon _ hmemT ((hover P).mpr hFP))
    · rintro rfl
      exact hQ𝔭 (hg ▸ Ideal.subset_span (Set.mem_singleton g))
  -- so the image of `g` in the affine central fibre vanishes exactly at `P₀`
  refine hP₀' (mk g) fun Q' hQ' => ?_
  have hFQ' : torusFermat k ∈ Q'.comap mk := by
    change mk (torusFermat k) ∈ Q'
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
    exact Q'.zero_mem
  have := hkey ⟨Q'.comap mk, Ideal.comap_isPrime mk Q'⟩ hFQ'
  rw [show mk g ∈ Q' ↔ g ∈ Q'.comap mk from Iff.rfl, this, PrimeSpectrum.ext_iff]
  exact (Ideal.comap_injective_of_surjective mk hmk).eq_iff

/-- **Property (2) of the construction of Stacks 0D5E.** Let `k` be an uncountable algebraically
closed field of characteristic different from three, and `Y` the cubic surface
`T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` over the affine line. There is a closed point `y` of
`Y` over the origin such that every closed subset `T ≠ Y` surjecting onto the affine line meets
the central fibre `Y₀` in a point other than `y`.

The source chooses `y` with `𝒪_{Y₀}(n y)` outside the image of `Pic(Y) → Pic(Y₀)` for every
`n > 0`, using that `Pic(Y)` is finitely generated; here `y` is chosen on the torus chart so that
no function on the affine central fibre `Y₀ ∩ D₊(T₀ T₁ T₂)` vanishes there exactly at `y`
(`exists_isMaximal_forall_not_zeroLocus_eq`), which is all the argument for (2) uses. -/
theorem exists_point_forall_isClosed_surjective_exists_ne [IsAlgClosed k] [Uncountable k]
    (h3 : ringChar k ≠ 3) :
    ∃ y : cubicSurface k, IsClosed ({y} : Set (cubicSurface k)) ∧
      cubicSurfaceToLine k y = originPoint k ∧
      ∀ T : Set (cubicSurface k), IsClosed T → T ≠ Set.univ →
        (∀ s : affineLine k, ∃ z ∈ T, cubicSurfaceToLine k z = s) →
        ∃ z ∈ T, cubicSurfaceToLine k z = originPoint k ∧ z ≠ y := by
  obtain ⟨P₀, hP₀, hP₀'⟩ := exists_isMaximal_forall_not_zeroLocus_eq k h3
  exact exists_point_forall_isClosed_surjective_exists_ne_of_isMaximal k P₀ hP₀ hP₀'

end Stacks.Examples.CurveFamilyNotScheme

end
