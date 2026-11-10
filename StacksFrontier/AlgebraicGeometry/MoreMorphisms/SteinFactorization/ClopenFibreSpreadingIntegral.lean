module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ClopenFibreSpreading

/-!
# Spreading a clopen decomposition of a fibre of a proper morphism over an arbitrary base

Let `f : X ⟶ S` be a proper morphism of schemes with `S` affine, let `s ∈ S`, and let the fibre
`f ⁻¹' {s}` be split by two closed subsets `P` and `Q` of `X` into two disjoint pieces.  Then
after an étale base change `(U, u) ⟶ (S, s)` the split extends to an open and closed subset `A`
of `X ×_S U`, which meets the fibre over `u` exactly in the points lying over `P`.

This is `Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isProper` without its
locally Noetherian hypothesis.  That hypothesis enters there only through the finiteness of the
second factor `π : S' ⟶ S` of the Stein factorization;  over an arbitrary base `π` is integral,
and the argument here replaces it by a finite morphism through which `π` factors and which still
separates the two pieces of the fibre.

## Main results

* `Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isFinite`: for a finite
  morphism `π₀ : T ⟶ S` and *any* subset `P₀ ⊆ T`, the points of `P₀` over `s` are cut out,
  after an elementary étale base change, by an open and closed subset.
* `Stacks.SteinFactorization.exists_fg_subalgebra_separates`: the commutative algebra.  If two
  ideals `I, J` of an `R`-algebra `R'` have no common prime over the prime `p` of `R`, the same
  holds for their traces on some finitely generated subalgebra.
* `Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isIntegralHom`: the same
  spreading for an integral morphism to an affine scheme and a split of a fibre by two closed
  sets.
* `Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isProper_of_isAffine`: the
  statement above.

## Implementation notes

The finite morphism is `Spec A ⟶ S` for a finitely generated `Γ(S)`-subalgebra `A` of
`Γ(S')`.  Write `P` and `Q` as the zero loci of ideals `I` and `J` of `Γ(S')`.  No prime over `s`
contains `I + J`, so some `t ∉ 𝔭_s` lies in `I + J + 𝔭_s Γ(S')`; the finitely many elements
needed to write `t` this way generate `A`, and then no prime of `A` over `s` contains both
`I ∩ A` and `J ∩ A`.  The traces of `P` and `Q` on `Spec A` are therefore separated over `s`,
and a finite morphism has a finite discrete fibre, which an elementary étale neighbourhood splits
into open and closed pieces ([Stacks, Tag 02LN]).

## References

* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SteinFactorization

/-! ### A finite morphism -/

/-- A point of a base change over the base point of an étale neighbourhood maps to the point `s`. -/
private theorem apply_fst_eq_of_snd_eq_point {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (U : AlgebraicGeometry.EtaleNeighborhood S s) (w : (pullback f U.toBase : Scheme.{u}))
    (hw : pullback.snd f U.toBase w = U.point) : f (pullback.fst f U.toBase w) = s := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hw, U.map_point]

/-- A map `g : X ⟶ Y` over `S` induces a map of base changes compatible with both projections. -/
private theorem exists_pullback_map {X Y S T : Scheme.{u}} (f : X ⟶ S) (π : Y ⟶ S) (b : T ⟶ S)
    (g : X ⟶ Y) (h : g ≫ π = f) :
    ∃ ψ : (pullback f b : Scheme.{u}) ⟶ pullback π b,
      (∀ w, pullback.fst π b (ψ w) = g (pullback.fst f b w)) ∧
        ∀ w, pullback.snd π b (ψ w) = pullback.snd f b w :=
  ⟨pullback.map f b π b g (𝟙 _) (𝟙 _) (by simp [h]) (by simp),
    fun w => by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst],
    fun w => by rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Category.comp_id]⟩

/-- **The points over `s` of an arbitrary subset of the source of a finite morphism are cut out
étale locally by an open and closed subset.**  Let `π₀ : T ⟶ S` be finite, `s ∈ S` and
`P₀ ⊆ T`.  There are an elementary étale neighbourhood `(U, u)` of `s` and an open and closed
subset `Z` of `T ×_S U` such that a point `w` over `u` lies in `Z` exactly when its image in `T`
lies in `P₀`.

The fibre of `π₀` over `s` is finite and discrete, and an elementary étale neighbourhood splits
its points off into open and closed pieces of the base change ([Stacks, Tag 02LN]); `Z` is the
union of the pieces of the points of `P₀`. -/
theorem exists_etaleNeighborhood_isClopen_of_isFinite {T S : Scheme.{u}} (π₀ : T ⟶ S)
    [IsFinite π₀] (s : S) (P₀ : Set T) :
    ∃ (U : AlgebraicGeometry.EtaleNeighborhood S s) (_ : U.IsElementary)
      (Z : Set (pullback π₀ U.toBase : Scheme.{u})), IsClopen Z ∧
        ∀ w : (pullback π₀ U.toBase : Scheme.{u}), pullback.snd π₀ U.toBase w = U.point →
          (w ∈ Z ↔ pullback.fst π₀ U.toBase w ∈ P₀) := by
  classical
  -- the fibre of `π₀` over `s` is finite; enumerate it
  obtain ⟨n, x, hxinj, hrange⟩ := (π₀.finite_preimage_singleton s).fin_param
  have hx : ∀ i, π₀ (x i) = s := fun i => hrange.subset ⟨i, rfl⟩
  have hxiso : ∀ i, IsOpen {π₀.asFiber (x i)} := fun i =>
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (π₀.quasiFiniteAt (x i))
  -- split the fibre of `π₀` off after an elementary étale base change
  obtain ⟨U, hU, R, j, hjo, hjc, hiso, v, hfin, hjx, hjv, -, hnone⟩ :=
    Stacks.Flatness.exists_etaleNeighborhood_decomposition π₀ s _ x hx hxinj hxiso
  let I₁ : Finset (Fin n) := Finset.univ.filter fun i => x i ∈ P₀
  let Z : Set (pullback π₀ U.toBase : Scheme.{u}) := ⋃ i ∈ I₁, Set.range (j (some i)).base
  have hZ : IsClopen Z := Set.Finite.isClopen_biUnion I₁.finite_toSet fun i _ =>
    ⟨(j (some i)).isClosedEmbedding.isClosed_range, (j (some i)).isOpenEmbedding.isOpen_range⟩
  -- every point of the base change lies in one of the pieces
  have hcov : ∀ w : (pullback π₀ U.toBase : Scheme.{u}), ∃ a y, j a y = w := by
    intro w
    obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso (Sigma.desc j).base).2 w
    obtain ⟨⟨a⟩, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (Discrete.functor R) y
    refine ⟨a, y, ?_⟩
    change (Sigma.desc j) ((Sigma.ι R a) y) = _ at hy
    rw [← hy, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  -- points over `u` of the piece of `x i` map to `x i`
  have hpiece : ∀ (i : Fin n) (y : R (some i)),
      (j (some i) ≫ pullback.snd π₀ U.toBase) y = U.point →
        pullback.fst π₀ U.toBase (j (some i) y) = x i := by
    intro i y hy
    have hy' : y ∈ {y : R (some i) | (j (some i) ≫ pullback.snd π₀ U.toBase) y = U.point} := hy
    rw [hjv i, Set.mem_singleton_iff] at hy'
    subst hy'
    rw [← Scheme.Hom.comp_apply]
    exact hjx i
  -- distinct pieces do not meet
  have hjinj : ∀ (b c : Option (Fin n)) (p : R b) (q : R c),
      j b p = j c q → b = c := by
    intro b c p q hpq
    have : (Sigma.ι R b ≫ Sigma.desc j) p = (Sigma.ι R c ≫ Sigma.desc j) q := by
      simpa only [Sigma.ι_comp_desc] using hpq
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
    exact congrArg Sigma.fst ((sigmaι_eq_iff R b c p q).mp
      ((ConcreteCategory.bijective_of_isIso (Sigma.desc j).base).1 this))
  refine ⟨U, hU, Z, hZ, fun w hw => ?_⟩
  have hπw := apply_fst_eq_of_snd_eq_point π₀ U w hw
  obtain ⟨a, y, hy⟩ := hcov w
  have hyu : (j a ≫ pullback.snd π₀ U.toBase) y = U.point := by
    rw [Scheme.Hom.comp_apply, hy, hw]
  cases a with
  | none =>
    obtain ⟨k, hk⟩ := hrange.symm.subset hπw
    exact absurd (by rw [Scheme.Hom.comp_apply, hy, hk]) (hnone y hyu k)
  | some i =>
    have hxi : pullback.fst π₀ U.toBase w = x i := by
      rw [← hy]; exact hpiece i y hyu
    have hmemZ : w ∈ Z ↔ i ∈ I₁ := by
      simp only [Z, Set.mem_iUnion, Set.mem_range]
      refine ⟨fun ⟨k, hk, q, hq⟩ => ?_, fun hi => ⟨i, hi, y, hy⟩⟩
      obtain rfl := Option.some_injective _ (hjinj (some k) (some i) q y (hq.trans hy.symm))
      exact hk
    rw [hmemZ, hxi]
    simp only [I₁, Finset.mem_filter, Finset.mem_univ, true_and]

/-! ### Separating two ideals on a finitely generated subalgebra -/

/-- **Two ideals with no common prime over `p` are already separated on a finitely generated
subalgebra.**  Let `R'` be an `R`-algebra, `p` a prime of `R` and `I, J` ideals of `R'` such that
no prime of `R'` lying over `p` contains both.  Then some finitely generated `R`-subalgebra `A`
of `R'` has the same property for the traces `I ∩ A` and `J ∩ A`.

Some `t ∉ p` lies in `I + J + p R'`, since otherwise a prime containing `I + J + p R'` and
missing the image of `R \ p` would lie over `p`.  Writing `t = a + b + Σ rᵢ pᵢ` with `a ∈ I`,
`b ∈ J`, `pᵢ ∈ p`, the subalgebra generated by `a`, `b` and the `rᵢ` does it. -/
theorem exists_fg_subalgebra_separates {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    (p : Ideal R) [p.IsPrime] (I J : Ideal R')
    (h : ∀ q : Ideal R', q.IsPrime → q.comap (algebraMap R R') = p → ¬ (I ≤ q ∧ J ≤ q)) :
    ∃ A : Subalgebra R R', A.FG ∧ ∀ q : Ideal A, q.IsPrime →
      q.comap (algebraMap R A) = p → ¬ (I.comap A.val ≤ q ∧ J.comap A.val ≤ q) := by
  classical
  let M : Submonoid R' := Algebra.algebraMapSubmonoid R' p.primeCompl
  let L : Ideal R' := I ⊔ J ⊔ p.map (algebraMap R R')
  -- some `t ∉ p` has its image in `L`
  obtain ⟨t, htp, htL⟩ : ∃ t : R, t ∉ p ∧ algebraMap R R' t ∈ L := by
    by_contra hcon
    push Not at hcon
    have hdisj : Disjoint (L : Set R') (M : Set R') := by
      rw [Set.disjoint_left]
      rintro y hyL ⟨t, ht, rfl⟩
      exact hcon t ht hyL
    obtain ⟨q, hq, hLq, hqM⟩ := Ideal.exists_le_prime_disjoint L M hdisj
    refine h q hq ?_ ⟨le_sup_left.trans (le_sup_left.trans hLq),
      le_sup_right.trans (le_sup_left.trans hLq)⟩
    exact le_antisymm (fun x hx => by_contra fun hxp => Set.disjoint_left.mp hqM hx ⟨x, hxp, rfl⟩)
      (Ideal.map_le_iff_le_comap.mp (le_sup_right.trans hLq))
  -- write it out
  obtain ⟨ab, hab, c, hc, habc⟩ := Submodule.mem_sup.mp htL
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
  obtain ⟨n, r, g, hrg⟩ := (Submodule.mem_span_set' (R := R') (s := algebraMap R R' '' p)).mp hc
  choose x hx hxg using fun i => (g i).property
  let F : Finset R' := {a, b} ∪ Finset.univ.image r
  refine ⟨Algebra.adjoin R (F : Set R'), Subalgebra.fg_adjoin_finset F, ?_⟩
  set A := Algebra.adjoin R (F : Set R')
  have hmem : ∀ y ∈ F, y ∈ A := fun y hy => Algebra.subset_adjoin hy
  let aA : A := ⟨a, hmem a (by simp [F])⟩
  let bA : A := ⟨b, hmem b (by simp [F])⟩
  let rA : Fin n → A := fun i => ⟨r i, hmem (r i) (by simp [F])⟩
  let cA : A := ∑ i, rA i * algebraMap R A (x i)
  have hcA : A.val cA = c := by
    rw [← hrg]
    simp only [cA, map_sum, map_mul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hxg i]
    rfl
  have hsum : aA + bA + cA = algebraMap R A t :=
    Subtype.val_injective (by
      change a + b + A.val cA = algebraMap R R' t
      rw [hcA, habc])
  intro q hq hqp ⟨hIq, hJq⟩
  have hcq : cA ∈ q := by
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
    change x i ∈ q.comap (algebraMap R A)
    rw [hqp]
    exact hx i
  have htq : algebraMap R A t ∈ q :=
    hsum ▸ q.add_mem (q.add_mem (hIq ha : aA ∈ q) (hJq hb : bA ∈ q)) hcq
  exact htp (hqp ▸ htq)

/-! ### An integral morphism to an affine scheme -/

/-- **A clopen split of a fibre of an integral morphism to an affine scheme spreads out étale
locally.**  Let `π : S' ⟶ S` be integral with `S` affine, let `s ∈ S`, and let `P` and `Q` be
closed subsets of `S'` which cover the fibre `π ⁻¹' {s}` and do not meet inside it.  Then there
are an elementary étale neighbourhood `(U, u)` of `s` and an open and closed subset `Z` of
`S' ×_S U` such that a point `w` over `u` lies in `Z` exactly when its image in `S'` lies in `P`.

By `Stacks.SteinFactorization.exists_fg_subalgebra_separates`, `π` factors through a finite
`Spec A ⟶ S` on which the traces of `P` and `Q` are still separated over `s`, and
`Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isFinite` applies there. -/
theorem exists_etaleNeighborhood_isClopen_of_isIntegralHom {S' S : Scheme.{u}} (π : S' ⟶ S)
    [IsIntegralHom π] [IsAffine S] (s : S) (P Q : Set S') (hP : IsClosed P) (hQ : IsClosed Q)
    (hcover : π ⁻¹' {s} ⊆ P ∪ Q) (hdisj : π ⁻¹' {s} ∩ (P ∩ Q) = ∅) :
    ∃ (U : AlgebraicGeometry.EtaleNeighborhood S s) (_ : U.IsElementary)
      (Z : Set (pullback π U.toBase : Scheme.{u})), IsClopen Z ∧
        ∀ w : (pullback π U.toBase : Scheme.{u}), pullback.snd π U.toBase w = U.point →
          (w ∈ Z ↔ pullback.fst π U.toBase w ∈ P) := by
  classical
  have : IsAffine S' := isAffine_of_isAffineHom π
  let R := Γ(S, ⊤)
  let R' := Γ(S', ⊤)
  let : Algebra R R' := π.appTop.hom.toAlgebra
  have hint : Algebra.IsIntegral R R' :=
    ⟨fun x => IsIntegralHom.isIntegral_app π ⊤ (isAffineOpen_top S) x⟩
  -- the prime of `s` and the ideals of `P` and `Q`
  let p : Ideal R := (S.isoSpec.hom s).asIdeal
  let I : Ideal R' := PrimeSpectrum.vanishingIdeal (S'.isoSpec.hom '' P)
  let J : Ideal R' := PrimeSpectrum.vanishingIdeal (S'.isoSpec.hom '' Q)
  have hmap : ∀ x : S', S.isoSpec.hom (π x) =
      PrimeSpectrum.comap (algebraMap R R') (S'.isoSpec.hom x) := by
    intro x
    rw [← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply]
    rfl
  have hclosed : ∀ Z : Set S', IsClosed Z →
      PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal (S'.isoSpec.hom '' Z) : Set R') =
        S'.isoSpec.hom '' Z := by
    intro Z hZ
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact ((S'.isoSpec.hom.homeomorph).isClosedMap Z hZ).closure_eq
  have hsep : ∀ q : Ideal R', q.IsPrime → q.comap (algebraMap R R') = p → ¬ (I ≤ q ∧ J ≤ q) := by
    intro q hq hqp ⟨hIq, hJq⟩
    let y : PrimeSpectrum R' := ⟨q, hq⟩
    let x : S' := S'.isoSpec.inv y
    have hxy : S'.isoSpec.hom x = y := by
      change (S'.isoSpec.inv ≫ S'.isoSpec.hom) y = y
      rw [Iso.inv_hom_id]
      rfl
    have hx : π x = s := by
      apply (ConcreteCategory.bijective_of_isIso S.isoSpec.hom.base).1
      change S.isoSpec.hom (π x) = S.isoSpec.hom s
      rw [hmap, hxy]
      exact PrimeSpectrum.ext hqp
    have hxmem : ∀ Z : Set S', IsClosed Z →
        PrimeSpectrum.vanishingIdeal (S'.isoSpec.hom '' Z) ≤ q → x ∈ Z := by
      intro Z hZ hZq
      have : y ∈ S'.isoSpec.hom '' Z := by
        rw [← hclosed Z hZ]
        exact hZq
      obtain ⟨x', hx'Z, hx'⟩ := this
      rwa [← (ConcreteCategory.bijective_of_isIso S'.isoSpec.hom.base).1 (hx'.trans hxy.symm)]
    exact hdisj.subset ⟨hx, hxmem P hP hIq, hxmem Q hQ hJq⟩
  obtain ⟨A, hAfg, hA⟩ := exists_fg_subalgebra_separates p I J hsep
  -- the finite morphism `Spec A ⟶ S` through which `π` factors
  have : Algebra.IsIntegral R A := Algebra.IsIntegral.of_injective A.val Subtype.val_injective
  have : Algebra.FiniteType R A := (Subalgebra.fg_iff_finiteType A).mp hAfg
  have : Module.Finite R A := Algebra.IsIntegral.finite
  let T : Scheme.{u} := Spec (CommRingCat.of A)
  let ι : R ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap R A)
  let κ : CommRingCat.of A ⟶ R' := CommRingCat.ofHom A.val.toRingHom
  let π₀ : T ⟶ S := Spec.map ι ≫ S.isoSpec.inv
  let ρ : S' ⟶ T := S'.isoSpec.hom ≫ Spec.map κ
  have hικ : ι ≫ κ = π.appTop := by
    ext r
    exact (IsScalarTower.algebraMap_apply R A R' r).symm
  have hρπ : ρ ≫ π₀ = π := by
    simp only [ρ, π₀, Category.assoc]
    rw [← Spec.map_comp_assoc, hικ, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id,
      Category.comp_id]
  have : IsFinite (Spec.map ι) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : IsFinite π₀ := inferInstance
  have hπ₀ : ∀ y : T, S.isoSpec.hom (π₀ y) = PrimeSpectrum.comap (algebraMap R A) y := by
    intro y
    change (S.isoSpec.inv ≫ S.isoSpec.hom) (Spec.map ι y) = _
    rw [Iso.inv_hom_id]
    rfl
  let P₀ : Set T := {y | I.comap A.val ≤ (y : PrimeSpectrum A).asIdeal}
  let Q₀ : Set T := {y | J.comap A.val ≤ (y : PrimeSpectrum A).asIdeal}
  have hρ : ∀ x : S', (ρ x : PrimeSpectrum A) =
      PrimeSpectrum.comap A.val.toRingHom (S'.isoSpec.hom x) := fun x => rfl
  have hcomap : ∀ (Z : Set S') (x : S'), x ∈ Z →
      (PrimeSpectrum.vanishingIdeal (S'.isoSpec.hom '' Z)).comap A.val ≤
        (ρ x : PrimeSpectrum A).asIdeal := by
    intro Z x hx a ha
    rw [hρ]
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha _ ⟨x, hx, rfl⟩
  have hPP₀ : ∀ x ∈ P, ρ x ∈ P₀ := hcomap P
  have hQQ₀ : ∀ x ∈ Q, ρ x ∈ Q₀ := hcomap Q
  obtain ⟨U, hU, Z₀, hZ₀, hZ₀p⟩ := exists_etaleNeighborhood_isClopen_of_isFinite π₀ s P₀
  obtain ⟨ψ, hψfst, hψsnd⟩ := exists_pullback_map π π₀ U.toBase ρ hρπ
  refine ⟨U, hU, ψ ⁻¹' Z₀, hZ₀.preimage ψ.continuous, fun w hw => ?_⟩
  have hπw := apply_fst_eq_of_snd_eq_point π U w hw
  change ψ w ∈ Z₀ ↔ _
  rw [hZ₀p (ψ w) ((hψsnd w).trans hw), hψfst]
  refine ⟨fun hP₀ => ?_, hPP₀ _⟩
  by_contra hnP
  have hxQ : pullback.fst π U.toBase w ∈ Q := (hcover hπw).resolve_left hnP
  refine hA _ (ρ (pullback.fst π U.toBase w) : PrimeSpectrum A).isPrime ?_
    ⟨hP₀, hQQ₀ _ hxQ⟩
  have h2 : π₀ (ρ (pullback.fst π U.toBase w)) = s := by
    rw [← Scheme.Hom.comp_apply, hρπ]
    exact hπw
  have h1 := hπ₀ (ρ (pullback.fst π U.toBase w))
  rw [h2] at h1
  exact congrArg PrimeSpectrum.asIdeal h1.symm

/-! ### A proper morphism to an affine scheme -/

/-- **A clopen decomposition of a fibre of a proper morphism to an affine scheme spreads out
étale locally.**  Let `f : X ⟶ S` be proper with `S` affine, let `s ∈ S`, and let `P` and `Q` be
closed subsets of `X` which cover the fibre `f ⁻¹' {s}` and do not meet inside it.  Then there
are an elementary étale neighbourhood `(U, u)` of `s` and an open and closed subset `A` of
`X ×_S U` such that a point `z` over `u` lies in `A` exactly when its image in `X` lies in `P`.

This is `Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isProper` with the
locally Noetherian hypothesis on `S` replaced by affineness.  The proof factors `f = π ∘ f'`
through its Stein factorization ([Stacks, Tag 03H2]): `f'` is surjective with geometrically
connected fibres, so the images of `P` and `Q` in `S'` split the fibre of `π` over `s`, and `π`
is integral, so `Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isIntegralHom`
spreads that split. -/
theorem exists_etaleNeighborhood_isClopen_of_isProper_of_isAffine {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [IsAffine S] (s : S) (P Q : Set X) (hP : IsClosed P)
    (hQ : IsClosed Q) (hcover : f ⁻¹' {s} ⊆ P ∪ Q) (hdisj : f ⁻¹' {s} ∩ (P ∩ Q) = ∅) :
    ∃ (U : AlgebraicGeometry.EtaleNeighborhood S s) (_ : U.IsElementary)
      (A : Set (pullback f U.toBase : Scheme.{u})), IsClopen A ∧
        ∀ z : (pullback f U.toBase : Scheme.{u}), pullback.snd f U.toBase z = U.point →
          (z ∈ A ↔ pullback.fst f U.toBase z ∈ P) := by
  classical
  let g := f.toNormalization
  let π := f.fromNormalization
  have hgπ : g ≫ π = f := toNormalization_fromNormalization f
  have : IsIntegralHom π := isIntegralHom_fromNormalization f
  have : IsProper g := isProper_toNormalization f
  have : GeometricallyConnected g := geometricallyConnected_toNormalization_of_isProper f
  have hgs : Function.Surjective g := (surjective_toNormalization f).surj
  have hfg : ∀ z, π (g z) = f z := fun z => by rw [← Scheme.Hom.comp_apply, hgπ]
  -- each fibre of `g` over a point of the fibre of `π` lies in `P` or in `Q`
  have hfib : ∀ y, π y = s → g ⁻¹' {y} ⊆ P ∨ g ⁻¹' {y} ⊆ Q := by
    intro y hy
    have hsub : g ⁻¹' {y} ⊆ f ⁻¹' {s} := by
      intro z hz
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hz ⊢
      rw [← hfg, hz, hy]
    refine isPreconnected_iff_subset_of_disjoint_closed.mp
      (g.isConnected_preimage_singleton y).isPreconnected P Q hP hQ
      (hsub.trans hcover) ?_
    exact Set.eq_empty_of_subset_empty
      ((Set.inter_subset_inter_left _ hsub).trans hdisj.subset)
  have hP' : IsClosed (g '' P) := g.isClosedMap P hP
  have hQ' : IsClosed (g '' Q) := g.isClosedMap Q hQ
  have hcover' : π ⁻¹' {s} ⊆ g '' P ∪ g '' Q := by
    intro y hy
    obtain ⟨z, rfl⟩ := hgs y
    have hz : f z = s := (hfg z).symm.trans hy
    rcases hcover hz with h | h
    · exact Or.inl ⟨z, h, rfl⟩
    · exact Or.inr ⟨z, h, rfl⟩
  have hdisj' : π ⁻¹' {s} ∩ (g '' P ∩ g '' Q) = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro hy ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    have hfa : f a = s := (hfg a).symm.trans hy
    have hfb : f b = s := (hfg b).symm.trans (hba ▸ hy)
    rcases hfib (g a) hy with h | h
    · have : b ∈ f ⁻¹' {s} ∩ (P ∩ Q) := ⟨hfb, h hba, hb⟩
      rw [hdisj] at this
      exact this
    · have : a ∈ f ⁻¹' {s} ∩ (P ∩ Q) := ⟨hfa, ha, h rfl⟩
      rw [hdisj] at this
      exact this
  obtain ⟨U, hU, Z, hZ, hZp⟩ :=
    exists_etaleNeighborhood_isClopen_of_isIntegralHom π s (g '' P) (g '' Q) hP' hQ' hcover'
      hdisj'
  obtain ⟨ψ, hψfst, hψsnd⟩ := exists_pullback_map f π U.toBase g hgπ
  refine ⟨U, hU, ψ ⁻¹' Z, hZ.preimage ψ.continuous, fun z hz => ?_⟩
  have hfz := apply_fst_eq_of_snd_eq_point f U z hz
  change ψ z ∈ Z ↔ _
  rw [hZp (ψ z) ((hψsnd z).trans hz), hψfst]
  refine ⟨fun ⟨a, ha, hga⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
  by_contra hnP
  have hQz : pullback.fst f U.toBase z ∈ Q := (hcover hfz).resolve_left hnP
  exact hdisj'.subset ⟨(hfg _).trans hfz, ⟨a, ha, hga⟩, ⟨_, hQz, rfl⟩⟩

end Stacks.SteinFactorization

end
