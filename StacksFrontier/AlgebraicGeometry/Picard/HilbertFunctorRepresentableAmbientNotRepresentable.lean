module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorRepresentableAmbientDegreeOne
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorRepresentableAmbientDoubledOrigin

/-!
# The degree-one Hilbert functor of the doubled origin is not representable

The hypothesis of Stacks Tag 0B9A at `d = 1` holds for every morphism of schemes, yet its
conclusion fails there: the degree-one Hilbert functor of the affine line with its origin
doubled, taken over affine `1`-space through the coordinate morphism, is represented by no
scheme over the base. This file assembles that counterexample, the capstone of the erratum to
Tag 0B9A.

## Main results

* `Stacks.Hilbert.not_nonempty_representsHilbertFunctorOfRank_one` — no scheme over affine
  `1`-space represents the degree-one Hilbert functor of the affine line with doubled origin.

## Implementation notes

The test objects are the fat points `T n = Spec (k[y] / (y ^ (n + 1)))` of the base. Each has a
single point, and the coordinate `y` pulls back to a nilpotent element of nilpotency order
exactly `n + 1`, so the preimage in `T n` of the standard open of `y` is empty and the graph of
either chart of the doubled origin cuts out a degree-one family there
(`Stacks.Hilbert.doubledChartFamily`).

Let `u n : T n ⟶ H` classify the family of the first chart. The fat points are nested, and a
chart point pulls back to a chart point because both factor through the terminal object
`Over.mk (𝟙 S)` of `Over S`; so all the `u n` restrict to one morphism on `T 0`, and since each
`T n` has a single point they all have the same image `h` in `H`.

The universal family over `H` makes the preimage in `H` of the standard open of `y` closed, by
`Stacks.Hilbert.isClosed_preimage_basicOpen_of_hilbertFamily`, and `h` lies outside it. So `h`
has an affine open neighbourhood `U` missing that preimage, on which the pullback `b` of `y` has
empty standard open and is therefore nilpotent, say `b ^ N = 0`. But `u N` factors through `U`,
and the pullback of `b` along that factorisation is the class of `y`, whose `N`-th power is
nonzero in `k[y] / (y ^ (N + 1))`.

The last step is the only algebra: `y ^ N ∉ (y ^ (N + 1))`, because `y` is prime in a polynomial
ring over a field and a power of a prime divides only the larger powers.

*The standard open of the coordinate is named.* `PrimeSpectrum.basicOpen y` lives in
`TopologicalSpace.Opens (PrimeSpectrum k[y])` while the preimage operation on a scheme asks for
an open of `Spec k[y]`; the two types are definitionally equal but not syntactically so, and a
rewrite whose motive abstracts such a term cannot re-typecheck it at its own transparency. So
`Stacks.Hilbert.coordOpen` names that open at the type the scheme-level operations expect, and
every statement here is phrased with it; the two spellings meet only where a statement from
elsewhere is applied, which costs nothing because they are definitionally equal.

No declaration here carries a Stacks attribute: the file refutes the degree-one case of Tag 0B9A
rather than proving any of its statements, and the tag is registered in
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbient.lean`.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-! ### The fat points of the affine line -/

section FatPoints

variable (k : Type u) [Field k]

/-- The standard open of the coordinate `y` in the affine line, at the type the scheme-level
preimage operation expects. -/
def coordOpen : (Spec (.of (MvPolynomial (Fin 1) k))).Opens :=
  PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1))

/-- The ideal `(y ^ (n + 1))` of the coordinate ring `k[y]` of the affine line. -/
abbrev truncIdeal (n : ℕ) : Ideal (MvPolynomial (Fin 1) k) :=
  Ideal.span {(MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) k) ^ (n + 1)}

/-- The coordinate ring `k[y] / (y ^ (n + 1))` of the `(n + 1)`-st order fat point. -/
abbrev truncRing (n : ℕ) : Type u := MvPolynomial (Fin 1) k ⧸ truncIdeal k n

/-- The quotient map onto the coordinate ring of the `(n + 1)`-st order fat point. -/
abbrev truncMk (n : ℕ) : MvPolynomial (Fin 1) k →+* truncRing k n := Ideal.Quotient.mk _

/-- The `(n + 1)`-st order fat point of the affine line, as a scheme over the affine line. -/
def truncObj (n : ℕ) : Over (Spec (.of (MvPolynomial (Fin 1) k))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (truncMk k n)))

/-- A prime of `k[y]` containing a power of `y` is the origin: it contains `y`, so it does not
lie in the punctured affine line. -/
theorem eq_affineOrigin_of_pow_mem {k : Type u} [Field k]
    {P : PrimeSpectrum (MvPolynomial (Fin 1) k)} {m : ℕ}
    (hm : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) k) ^ m ∈ P.asIdeal) :
    P = affineOrigin k 1 := by
  have hy : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) k) ∈ P.asIdeal :=
    P.isPrime.mem_of_pow_mem m hm
  refine eq_affineOrigin_of_notMem_puncturedAffineSpace k 1 ?_
  rw [puncturedAffineSpace_one]
  exact fun hmem => (PrimeSpectrum.mem_basicOpen _ _).mp hmem hy

/-- The relation defining the coordinate ring of the `(n + 1)`-st order fat point. -/
theorem truncMk_coord_pow_eq_zero (n : ℕ) :
    truncMk k n ((MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) k) ^ (n + 1)) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- The class of `y` in `k[y] / (y ^ (n + 1))` is nilpotent. -/
theorem isNilpotent_truncMk_coord (n : ℕ) :
    IsNilpotent (truncMk k n (MvPolynomial.X (0 : Fin 1))) :=
  ⟨n + 1, by rw [← map_pow]; exact truncMk_coord_pow_eq_zero k n⟩

/-- **The fat point has a single point**: every prime of `k[y] / (y ^ (n + 1))` pulls back to a
prime of `k[y]` containing `y`, hence to the origin, and pulling back along a surjective ring
map is injective. -/
instance subsingleton_truncRing (n : ℕ) : Subsingleton (PrimeSpectrum (truncRing k n)) := by
  have hinj : Function.Injective (PrimeSpectrum.comap (truncMk k n)) :=
    PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨fun p q => hinj ?_⟩
  have hmem : ∀ r : PrimeSpectrum (truncRing k n),
      (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) k) ^ (n + 1) ∈
        (PrimeSpectrum.comap (truncMk k n) r).asIdeal := by
    intro r
    change truncMk k n _ ∈ r.asIdeal
    rw [truncMk_coord_pow_eq_zero]
    exact r.asIdeal.zero_mem
  rw [eq_affineOrigin_of_pow_mem (hmem p), eq_affineOrigin_of_pow_mem (hmem q)]

/-- The fat point has a single point, read on the scheme rather than on the ring. -/
instance subsingleton_truncObj_left (n : ℕ) : Subsingleton (truncObj k n).left :=
  inferInstanceAs (Subsingleton (PrimeSpectrum (truncRing k n)))

/-- **The standard open of the coordinate pulls back to the empty open on the fat point**: the
coordinate becomes nilpotent there. -/
theorem preimage_coordOpen_truncObj (n : ℕ) :
    (truncObj k n).hom ⁻¹ᵁ coordOpen k = ⊥ := by
  have h : PrimeSpectrum.basicOpen (truncMk k n (MvPolynomial.X (0 : Fin 1))) = ⊥ :=
    (PrimeSpectrum.basicOpen_eq_bot_iff _).mpr (isNilpotent_truncMk_coord k n)
  change Spec.map (CommRingCat.ofHom (truncMk k n)) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1)) = ⊥
  rw [SpecMap_preimage_basicOpen]
  exact h

/-- The standard open of the coordinate is the scheme-theoretic standard open of the coordinate
read as a global section of the affine line. -/
theorem basicOpen_coord_eq_coordOpen :
    (Spec (.of (MvPolynomial (Fin 1) k))).basicOpen
        ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 1) k))).inv
          (MvPolynomial.X (0 : Fin 1))) = coordOpen k :=
  basicOpen_eq_of_affine _

/-- Pulling the coordinate back along the structure morphism of the fat point gives the class of
the coordinate in `k[y] / (y ^ (n + 1))`. -/
theorem specMap_truncMk_appTop_coord (n : ℕ) :
    (Spec.map (CommRingCat.ofHom (truncMk k n))).appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 1) k))).inv (MvPolynomial.X (0 : Fin 1))) =
      (Scheme.ΓSpecIso (.of (truncRing k n))).inv
        (truncMk k n (MvPolynomial.X (0 : Fin 1))) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
    CommRingCat.ofHom_apply]

/-- A power of `y` never lies in the ideal generated by the next one: the variable is prime in a
polynomial ring over a field, so a power of it divides only the larger powers. -/
theorem notMem_truncIdeal_pow (N : ℕ) :
    (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) k) ^ N ∉ truncIdeal k N := by
  intro h
  rw [Ideal.mem_span_singleton] at h
  have := (pow_dvd_pow_iff (MvPolynomial.X_ne_zero (0 : Fin 1))
    MvPolynomial.X_prime.not_isUnit).mp h
  omega

/-- **The pullback of the coordinate to the `(n + 1)`-st order fat point has nonzero `n`-th
power**: it is the class of `y`, and `y ^ n` does not lie in `(y ^ (n + 1))`. -/
theorem pow_appTop_coord_ne_zero (n : ℕ) :
    (truncObj k n).hom.appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 1) k))).inv
          (MvPolynomial.X (0 : Fin 1))) ^ n ≠ 0 := by
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of (truncRing k n))).inv.hom := by
    intro a c hac
    rw [← CommRingCat.hom_inv_apply (Scheme.ΓSpecIso (.of (truncRing k n))) a,
      ← CommRingCat.hom_inv_apply (Scheme.ΓSpecIso (.of (truncRing k n))) c, hac]
  change (Spec.map (CommRingCat.ofHom (truncMk k n))).appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 1) k))).inv
        (MvPolynomial.X (0 : Fin 1))) ^ n ≠ 0
  rw [specMap_truncMk_appTop_coord, ← map_pow, ← map_pow]
  intro hz
  refine notMem_truncIdeal_pow k n (Ideal.Quotient.eq_zero_iff_mem.mp (hinj ?_))
  rw [map_zero]
  exact hz

/-- The ideal `(y)` is proper, since `1` is not a multiple of `y`. -/
instance nontrivial_truncRing_zero : Nontrivial (truncRing k 0) :=
  Ideal.Quotient.nontrivial_iff.mpr fun htop =>
    notMem_truncIdeal_pow k 0 (by rw [htop]; trivial)

/-- **The first-order fat point is a nonempty scheme.** -/
instance nonempty_truncObj_zero_left : Nonempty (truncObj k 0).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum (truncRing k 0)))

/-- The first-order fat point maps into every fat point: the ideals are nested. -/
theorem truncIdeal_le_zero (n : ℕ) : truncIdeal k n ≤ truncIdeal k 0 := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
  exact pow_dvd_pow _ (by omega)

/-- The ring map `k[y] / (y ^ (n + 1)) →+* k[y] / (y)` through which the quotient maps
factor. -/
abbrev truncFactor (n : ℕ) : truncRing k n →+* truncRing k 0 :=
  Ideal.Quotient.factor (truncIdeal_le_zero k n)

/-- **The first-order fat point is a point of every fat point, over the affine line.** -/
def truncIncl (n : ℕ) : truncObj k 0 ⟶ truncObj k n :=
  Over.homMk (Spec.map (CommRingCat.ofHom (truncFactor k n))) (by
    change Spec.map (CommRingCat.ofHom (truncFactor k n)) ≫
        Spec.map (CommRingCat.ofHom (truncMk k n)) = Spec.map (CommRingCat.ofHom (truncMk k 0))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk])

end FatPoints

/-! ### The classifying maps of the chart families -/

section Representing

variable {k : Type u} [Field k]

/-- Composing a chart point with a morphism of test objects gives the chart point of the
source: both factor through the terminal object `Over.mk (𝟙 S)` of `Over S`. -/
theorem comp_doubledChartPoint {T' T : Over (Spec (.of (MvPolynomial (Fin 1) k)))} (g : T' ⟶ T)
    (i : Fin 2) : g ≫ doubledChartPoint k T i = doubledChartPoint k T' i := by
  rw [doubledChartPoint, doubledChartPoint, ← Category.assoc,
    Over.mkIdTerminal.hom_ext (g ≫ Over.homMk T.hom) (Over.homMk T'.hom)]

/-- The ideal of the degree-one family cut out by a chart point is that chart point's point
ideal. -/
theorem doubledChartFamily_ideal (T : Over (Spec (.of (MvPolynomial (Fin 1) k))))
    (hT : T.hom ⁻¹ᵁ coordOpen k = ⊥) (i : Fin 2) :
    (doubledChartFamily k T hT i).ideal =
      pointIdeal (Over.mk (coordinateMorphism k 1)) T (doubledChartPoint k T i) :=
  rfl

variable {H : Over (Spec (.of (MvPolynomial (Fin 1) k)))}
  (R : RepresentsHilbertFunctorOfRank (Over.mk (coordinateMorphism k 1)) H 1)

/-- The morphism to a representing scheme classifying the family cut out by the first chart of
the doubled origin over the `(n + 1)`-st order fat point. -/
def truncClassifyingMap (n : ℕ) : truncObj k n ⟶ H :=
  R.family.symm (doubledChartFamily k (truncObj k n) (preimage_coordOpen_truncObj k n) 0)

/-- **The classifying maps of the fat points are compatible with their inclusions.** Both sides
classify the family cut out by the first chart point of the first-order fat point: a point ideal
is stable under base change, and a chart point pulls back to a chart point. -/
theorem truncIncl_comp_truncClassifyingMap (n : ℕ) :
    truncIncl k n ≫ truncClassifyingMap R n = truncClassifyingMap R 0 := by
  have := isClosedImmersion_pointGraph_doubledChartPoint k (truncObj k n)
    (preimage_coordOpen_truncObj k n) 0
  refine R.family.injective (HilbertFamily.ext ?_)
  rw [R.naturality]
  simp only [truncClassifyingMap, Equiv.apply_symm_apply]
  rw [doubledChartFamily_ideal, doubledChartFamily_ideal,
    pointIdeal_comap_familyBaseChangeMap, comp_doubledChartPoint]

/-- **Every point of every fat point has the same image in a representing scheme.** The fat
points have a single point each, and their classifying maps are compatible with the
inclusions. -/
theorem truncClassifyingMap_left_apply (n : ℕ) (t : (truncObj k n).left)
    (t₀ : (truncObj k 0).left) :
    (truncClassifyingMap R n).left t = (truncClassifyingMap R 0).left t₀ := by
  rw [show t = (truncIncl k n).left t₀ from Subsingleton.elim _ _,
    ← Scheme.Hom.comp_apply, ← Over.comp_left, truncIncl_comp_truncClassifyingMap]

/-- **The standard open of the coordinate misses the image of a fat point.** The preimage of
that open along a classifying map is the preimage along the structure morphism of the fat
point, which is empty. -/
theorem preimage_preimage_coordOpen_truncClassifyingMap (n : ℕ) :
    (truncClassifyingMap R n).left ⁻¹ᵁ (H.hom ⁻¹ᵁ coordOpen k) = ⊥ := by
  rw [← Scheme.Hom.comp_preimage, Over.w]
  exact preimage_coordOpen_truncObj k n

end Representing

/-! ### Nilpotency of the coordinate on an affine open -/

section Nilpotent

variable {k : Type u} [Field k]

/-- **The coordinate pulls back to a section with empty standard open** on an affine open of a
scheme over the affine line which misses the preimage of the standard open of the
coordinate. -/
theorem basicOpen_appTop_coord_eq_bot {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (MvPolynomial (Fin 1) k))) (U : X.Opens)
    (hU : (U : Set X) ⊆ ((f ⁻¹ᵁ coordOpen k : X.Opens) : Set X)ᶜ) :
    U.toScheme.basicOpen ((U.ι ≫ f).appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 1) k))).inv
          (MvPolynomial.X (0 : Fin 1)))) = ⊥ := by
  have h : U.toScheme.basicOpen ((U.ι ≫ f).appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 1) k))).inv (MvPolynomial.X (0 : Fin 1)))) =
      U.ι ⁻¹ᵁ (f ⁻¹ᵁ coordOpen k) := by
    rw [← Scheme.Hom.comp_preimage, ← basicOpen_coord_eq_coordOpen,
      Scheme.preimage_basicOpen_top]
  rw [h]
  refine TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_)
  exact hU (by rw [← Scheme.Opens.range_ι]; exact ⟨z, rfl⟩) hz

end Nilpotent

/-! ### The counterexample -/

/-- **The degree-one Hilbert functor of the affine line with doubled origin is represented by no
scheme over the affine line.** The hypothesis of Stacks Tag 0B9A holds at `d = 1` for every
morphism of schemes, by `Stacks.Hilbert.exists_isAffineOpen_forall_mem_of_le_one`, so this is a
counterexample to the conclusion of that tag there.

Suppose a scheme `H` over `S = Spec k[y]` represented the functor. Over the fat point
`T n = Spec (k[y] / (y ^ (n + 1)))` the preimage of the standard open of `y` is empty, so the
graph of the first chart of the doubled origin cuts out a degree-one family; let `u n` classify
it. All the `u n` restrict to one morphism on `T 0`, and since each `T n` has a single point
they all have the same image `h` in `H`.

The universal family over `H` makes the preimage in `H` of the standard open of `y` closed, and
`h` lies outside it, so `h` has an affine open neighbourhood `U` missing that preimage. On `U`
the pullback `b` of `y` has empty standard open, hence is nilpotent, say `b ^ N = 0`. But `u N`
factors through `U` and carries `b` to the class of `y` in `k[y] / (y ^ (N + 1))`, whose `N`-th
power is nonzero. -/
theorem not_nonempty_representsHilbertFunctorOfRank_one (k : Type u) [Field k] :
    ¬ Nonempty (Σ H : Over (Spec (.of (MvPolynomial (Fin 1) k))),
        Stacks.Hilbert.RepresentsHilbertFunctorOfRank
          (Over.mk (AlgebraicGeometry.coordinateMorphism k 1)) H 1) := by
  rintro ⟨⟨H, R⟩⟩
  obtain ⟨t₀⟩ : Nonempty (truncObj k 0).left := inferInstance
  have hHclosed : IsClosed ((H.hom ⁻¹ᵁ coordOpen k : H.left.Opens) : Set H.left) :=
    isClosed_preimage_basicOpen_of_hilbertFamily k H (R.family (𝟙 H))
  have hnot : (truncClassifyingMap R 0).left t₀ ∉ (H.hom ⁻¹ᵁ coordOpen k : H.left.Opens) := by
    intro hmem
    have hmem' : t₀ ∈ ((truncClassifyingMap R 0).left ⁻¹ᵁ (H.hom ⁻¹ᵁ coordOpen k)) := hmem
    rw [preimage_preimage_coordOpen_truncClassifyingMap] at hmem'
    simp at hmem'
  obtain ⟨U, hUaff, hhU, hUW⟩ := exists_isAffineOpen_mem_and_subset
    (X := H.left) (x := (truncClassifyingMap R 0).left t₀)
    (U := ⟨((H.hom ⁻¹ᵁ coordOpen k : H.left.Opens) : Set H.left)ᶜ, hHclosed.isOpen_compl⟩) hnot
  have : IsAffine U.toScheme := hUaff
  obtain ⟨N, hN⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot _).mpr
    (basicOpen_appTop_coord_eq_bot H.hom U hUW)
  have hrange : Set.range (truncClassifyingMap R N).left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    rw [truncClassifyingMap_left_apply R N t t₀]
    exact hhU
  have hcomp : IsOpenImmersion.lift U.ι (truncClassifyingMap R N).left hrange ≫ (U.ι ≫ H.hom) =
      (truncObj k N).hom := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w (truncClassifyingMap R N)
  refine pow_appTop_coord_ne_zero k N ?_
  rw [← hcomp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← map_pow, hN, map_zero]

/-- **Stacks Tag 0B9A is false as literally stated, in one statement.**  For the coordinate
morphism of the affine line with doubled origin and `d = 1`, the tag's hypothesis HOLDS -- and
holds vacuously, every single point of a scheme lying in an affine open -- while the tag's
conclusion FAILS.

The two halves are
`Stacks.Hilbert.exists_isAffineOpen_forall_mem_of_le_one`, which proves the `d`-tuple hypothesis
for every morphism of schemes once `d ≤ 1`, and
`Stacks.Hilbert.not_nonempty_representsHilbertFunctorOfRank_one`.  This is the erratum that the
tag's registration is scoped against:
`nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one` carries
`@[stacks 0B9A]` and states the tag under the source's own `d`-tuple hypothesis for every `d ≠ 1`,
the range this statement leaves intact.  The generalisation to every `d`,
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem`, asks
for the affine-open condition at `max d 2` points, which for `2 ≤ d` is again the source's own
`d` points and at `d ≤ 1` is the minimal repair. -/
theorem exists_isAffineOpen_forall_mem_and_not_representable_one (k : Type u) [Field k] :
    (∀ (s : Spec (.of (MvPolynomial (Fin 1) k)))
        (x : Fin 1 → (Over.mk (AlgebraicGeometry.coordinateMorphism k 1)).left),
        (∀ i, (Over.mk (AlgebraicGeometry.coordinateMorphism k 1)).hom.base (x i) = s) →
        ∃ U : (Over.mk (AlgebraicGeometry.coordinateMorphism k 1)).left.Opens,
          IsAffineOpen U ∧ ∀ i, x i ∈ U) ∧
      ¬ Nonempty (Σ H : Over (Spec (.of (MvPolynomial (Fin 1) k))),
        Stacks.Hilbert.RepresentsHilbertFunctorOfRank
          (Over.mk (AlgebraicGeometry.coordinateMorphism k 1)) H 1) :=
  ⟨fun s x hx => exists_isAffineOpen_forall_mem_of_le_one _ le_rfl s x hx,
    not_nonempty_representsHilbertFunctorOfRank_one k⟩

end Stacks.Hilbert

end
