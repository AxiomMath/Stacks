module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.CartesianImmersions
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

/-!
# Finite étale covers of a proper scheme over a complete Noetherian ring

Let `A` be a Noetherian ring complete with respect to an ideal `I` and let `X` be proper over
`Spec A`, with closed fibre `X₀ = X ×_{Spec A} Spec (A ⧸ I)`. This file carries out the first two
stages of the Stacks proof of Tag 0A48 (and of Tag 0GS2, whose proof is the same): base change
`FÉt_X ⥤ FÉt_{X₀}` is essentially surjective, and then an equivalence. The one input taken as a
hypothesis is Grothendieck's existence theorem for finite sheaves of algebras,
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization`, which is the input of
`AlgebraicGeometry.exists_finite_algebraization_of_adicFiniteSystem`, and which the library
proves as `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_holds`.

## The argument

Write `Xₙ = X ×_{Spec A} Spec (A ⧸ Iⁿ⁺¹)`. Given a finite étale `U₀ ⟶ X₀`:

* each transition `Xₙ ⟶ Xₙ₊₁` is a thickening, being the base change of the first-order
  thickening `Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec (A ⧸ Iⁿ⁺²)`
  (`AlgebraicGeometry.isFiniteOrderThickening_adicBaseChangeSucc`), so by Stacks 039R the étale
  scheme `Uₙ ⟶ Xₙ` lifts to an étale `Uₙ₊₁ ⟶ Xₙ₊₁` with `Uₙ = Uₙ₊₁ ×_{Xₙ₊₁} Xₙ`; building the
  lifts one after the other gives a system with cartesian transition squares, which is the
  hypothesis `hcart` of 09ZT;
* every `Uₙ ⟶ Xₙ` is finite, by Stacks 09ZW across the cartesian squares;
* `U₀` is proper over `Spec (A ⧸ I)`, being finite over the proper `X₀`;
* so 09ZT produces a finite `U ⟶ X` with `U ×_X Xₙ = Uₙ` for every `n`;
* the `n`-th infinitesimal neighbourhood of `X₀` in `X` maps into `Xₙ`
  (`AlgebraicGeometry.exists_lift_adicThickeningι_of_isNthOrderThickening`), so the base change
  of `U ⟶ X` to it is a base change of `Uₙ ⟶ Xₙ`, hence étale, and Stacks 0A43 makes `U ⟶ X`
  étale at every point above `X₀`;
* every point of `U` specializes to such a point, `U` being proper over `Spec A` and `I` lying
  in the Jacobson radical, and the étale locus is open, so `U ⟶ X` is étale.

Full faithfulness then comes from essential surjectivity over every finite étale cover of `X`
(each again proper over `Spec A`) by the library's reduction
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`,
which is the source's graph argument with Stacks 04DH.

## Main definitions

* `AlgebraicGeometry.ProperCompleteLocalFiniteEtaleEquivalence` — the conclusion of Tag 0A48 for
  every proper scheme over every complete local Noetherian ring, in the shape of
  `AlgebraicGeometry.ProperHenselianFiniteEtaleEquivalence`.

## Main results

* `AlgebraicGeometry.exists_finite_etale_isPullback_of_adicFiniteAlgebraAlgebraization` — every
  finite étale `U₀ ⟶ X₀` is the closed fibre of a finite étale `U ⟶ X`.
* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_adicFiniteAlgebraAlgebraization` —
  essential surjectivity of `FÉt_X ⥤ FÉt_{X₀}`.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_adicFiniteAlgebraAlgebraization` —
  the equivalence.
* `isEquivalence_finiteEtaleBaseChange_of_isProper_of_isAdicComplete_maximalIdeal` and
  `properCompleteLocalFiniteEtaleEquivalence_of_adicFiniteAlgebraAlgebraization` — the first
  stage of Tag 0A48 over a complete local Noetherian ring, granted the algebraization hypothesis.

## References

* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A43](https://stacks.math.columbia.edu/tag/0A43)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Thickenings

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The structure morphism of an adic thickening is a closed immersion. -/
instance isClosedImmersion_adicThickeningι (n : ℕ) : IsClosedImmersion (adicThickeningι A I n) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The transition `Spec (A ⧸ Iⁿ⁺¹) ⟶ Spec (A ⧸ Iⁿ⁺²)` between consecutive adic thickenings is a
first-order thickening: the kernel `Iⁿ⁺¹ / Iⁿ⁺²` squares to zero because `n + 2 ≤ 2n + 2`. -/
theorem isFirstOrderThickening_adicThickeningSucc (n : ℕ) :
    Stacks.Thickenings.IsFirstOrderThickening (adicThickeningSucc A I n) := by
  unfold adicThickeningSucc
  refine Stacks.Smooth.isFirstOrderThickening_specMap _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) ?_
  refine le_bot_iff.mp ?_
  rw [pow_two, Ideal.mul_le]
  intro r hr s hs
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective s
  have hmem : ∀ z : A, Ideal.Quotient.mk (I ^ (n + 1 + 1)) z ∈
      RingHom.ker (CommRingCat.ofHom
        (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))).hom → z ∈ I ^ (n + 1) := by
    intro z hz
    rw [RingHom.mem_ker] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hxy := Ideal.mul_mem_mul (hmem x hr) (hmem y hs)
  rw [← pow_add] at hxy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_le_pow_right (by omega) hxy

/-- The transition `Xₙ ⟶ Xₙ₊₁` between consecutive adic base changes is a finite-order
thickening, being the base change of `isFirstOrderThickening_adicThickeningSucc`. -/
theorem isFiniteOrderThickening_adicBaseChangeSucc {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (n : ℕ) : Stacks.Thickenings.IsFiniteOrderThickening (adicBaseChangeSucc A I f n) := by
  have h := isFirstOrderThickening_adicThickeningSucc A I n
  exact MorphismProperty.of_isPullback (P := @Stacks.Thickenings.IsFiniteOrderThickening)
    (isPullback_adicBaseChangeSucc A I f n).flip ⟨h.1, 1, h.2⟩

/-- The ideal sheaf of `Spec (A ⧸ Iⁿ⁺¹)` in `Spec A` is contained in the `(n + 1)`-st power of
the ideal sheaf of `Spec (A ⧸ I)`. -/
theorem ker_adicThickeningι_le_pow (n : ℕ) :
    (adicThickeningι A I n).ker ≤ (adicThickeningι A I 0).ker ^ (n + 1) := by
  apply Scheme.IdealSheafData.le_of_isAffine
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply]
  change RingHom.ker (adicThickeningι A I n).appTop.hom ≤
    RingHom.ker (adicThickeningι A I 0).appTop.hom ^ (n + 1)
  rw [adicThickeningι, adicThickeningι, Stacks.Smooth.ker_specMap_appTop,
    Stacks.Smooth.ker_specMap_appTop]
  simp only [CommRingCat.hom_ofHom, Ideal.mk_ker, zero_add, pow_one]
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  change Ideal.comap e (I ^ (n + 1)) ≤ (Ideal.comap e I) ^ (n + 1)
  rw [← Ideal.map_symm e, ← Ideal.map_symm e, Ideal.map_pow]

/-- **A thickening of order `n` of a scheme over `Spec (A ⧸ I)` lies over `Spec (A ⧸ Iⁿ⁺¹)`.**
If `j : T ⟶ T'` is an `n`-th order thickening and `g : T' ⟶ Spec A` restricts on `T` to a
morphism through `Spec (A ⧸ I)`, then `g` factors through `Spec (A ⧸ Iⁿ⁺¹)`. This is Stacks 01HP
(`Stacks.Thickenings.ker_pow_le_ker_of_comm_square`) together with the universal property of a
closed immersion. -/
theorem exists_lift_adicThickeningι_of_isNthOrderThickening {T T' : Scheme.{u}} (j : T ⟶ T')
    (n : ℕ) (hj : Stacks.Thickenings.IsNthOrderThickening n j) (g : T' ⟶ Spec (.of A))
    (a : T ⟶ adicThickening A I 0) (h : j ≫ g = a ≫ adicThickeningι A I 0) :
    ∃ g' : T' ⟶ adicThickening A I n, g' ≫ adicThickeningι A I n = g := by
  have := hj.1
  have hle := Stacks.Thickenings.ker_pow_le_ker_of_comm_square (adicThickeningι A I 0) j a g
    (n + 1) h hj.2
  exact ⟨IsClosedImmersion.lift _ g ((ker_adicThickeningι_le_pow A I n).trans hle),
    IsClosedImmersion.lift_fac _ _ _⟩

end Thickenings

section Lift

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **One step of the tower of étale lifts (Stacks 039R).** An étale scheme over the adic base
change `Xₙ` is the base change, along the thickening `Xₙ ⟶ Xₙ₊₁`, of an étale scheme over
`Xₙ₊₁`, the square being cartesian. -/
theorem exists_etale_isPullback_adicBaseChangeSucc (n : ℕ)
    (s : MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤
      (adicBaseChange A I f n)) :
    ∃ (s' : MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤
        (adicBaseChange A I f (n + 1))) (t : s.left ⟶ s'.left),
      IsPullback t s.hom s'.hom (adicBaseChangeSucc A I f n) := by
  have hj := (isFiniteOrderThickening_adicBaseChangeSucc A I f n).isThickening
  have := hj.1
  obtain ⟨V, q, hq, e, he⟩ :=
    Stacks.Etale.exists_etale_pullback_iso_of_isClosedImmersion_of_surjective
      (adicBaseChangeSucc A I f n) hj.2 s.left s.hom s.prop
  have he' : e.inv ≫ pullback.snd q (adicBaseChangeSucc A I f n) = s.hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  refine ⟨MorphismProperty.Over.mk ⊤ q hq, e.inv ≫ pullback.fst q _, ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ e.symm rfl he'
  change (e.inv ≫ pullback.fst q _) ≫ q = s.hom ≫ adicBaseChangeSucc A I f n
  rw [Category.assoc, pullback.condition, ← Category.assoc, he']

end Lift

section Complete

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]

/-- **Algebraization of a finite étale cover of the closed fibre.** Let `A` be Noetherian and
`I`-adically complete, let `X` be proper over `Spec A`, and grant Grothendieck existence for finite
sheaves of algebras on `X` (`AdicFiniteAlgebraAlgebraization`). Then every finite étale
`U₀ ⟶ X₀` over the closed fibre `X₀ = X ×_{Spec A} Spec (A ⧸ I)` is the base change of a finite
étale `U ⟶ X`.

This is the essential-surjectivity paragraph of the Stacks proof of Tag 0A48; see the module
docstring for the argument. -/
theorem exists_finite_etale_isPullback_of_adicFiniteAlgebraAlgebraization
    (halg : AdicFiniteAlgebraAlgebraization A I f)
    {U₀ : Scheme.{u}} (p₀ : U₀ ⟶ adicBaseChange A I f 0) [IsFinite p₀] [Etale p₀] :
    ∃ (U : Scheme.{u}) (p : U ⟶ X) (k : U₀ ⟶ U), IsFinite p ∧ Etale p ∧
      IsPullback k p₀ p (pullback.fst f (adicThickeningι A I 0)) := by
  -- the tower of étale lifts, built one thickening at a time (Stacks 039R)
  choose step t ht using exists_etale_isPullback_adicBaseChangeSucc A I f
  let T : ∀ n, MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤
      (adicBaseChange A I f n) := fun n =>
    Nat.rec (motive := fun n => MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤
        (adicBaseChange A I f n))
      (MorphismProperty.Over.mk ⊤ p₀ inferInstance) (fun n s => step n s) n
  let y : ∀ n, (T n).left ⟶ adicBaseChange A I f n := fun n => (T n).hom
  let t' : ∀ n, (T n).left ⟶ (T (n + 1)).left := fun n => t n (T n)
  have hcart : ∀ n, IsPullback (t' n) (y n) (y (n + 1)) (adicBaseChangeSucc A I f n) :=
    fun n => ht n (T n)
  -- every member of the tower is finite (Stacks 09ZW)
  have hfin : ∀ n, IsFinite (y n) := by
    intro n
    induction n with
    | zero => exact (inferInstance : IsFinite p₀)
    | succ n ih =>
      exact (Stacks.Thickenings.isFinite_iff_of_isFiniteOrderThickening _ _ _ _
        (isFiniteOrderThickening_adicBaseChangeSucc A I f n) (hcart n)).mp ih
  -- the closed member is proper over `Spec (A ⧸ I)`
  have hproper : IsProper (y 0 ≫ pullback.snd f (adicThickeningι A I 0)) := by
    have := hfin 0
    infer_instance
  -- Grothendieck's algebraization theorem, in the form of Stacks 09ZT
  obtain ⟨Z, a, ha, haf, k, hk, hka⟩ := exists_finite_algebraization_of_adicFiniteSystem A I f
    halg (fun n => (T n).left) y t' hcart hfin hproper
  have hX : ∀ n, IsPullback (k n) (y n) a (pullback.fst f (adicThickeningι A I n)) := fun n =>
    IsPullback.of_bot (hk n) (hka n) (IsPullback.of_hasPullback f (adicThickeningι A I n))
  -- étaleness above the closed fibre (Stacks 0A43)
  let i := pullback.fst f (adicThickeningι A I 0)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hloc : ∀ z : Z, a z ∈ Set.range i → EtaleAt a z := by
    refine etaleAt_of_etale_infinitesimalNeighbourhoods a i (fun n => ?_)
    obtain ⟨g', hg'⟩ := exists_lift_adicThickeningι_of_isNthOrderThickening A I
      (Stacks.Thickenings.nthOrderInclusion i n) n
      (Stacks.Thickenings.nthOrderInclusion_isNthOrderThickening i n)
      (Stacks.Thickenings.nthOrderToBase i n ≫ f) (pullback.snd f (adicThickeningι A I 0))
      (by rw [← Category.assoc, Stacks.Thickenings.nthOrderInclusion_toBase]
          exact pullback.condition)
    let h : Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n ⟶
        adicBaseChange A I f n := pullback.lift _ g' hg'.symm
    have hh : h ≫ pullback.fst f (adicThickeningι A I n) =
        Stacks.Thickenings.nthOrderToBase i n := pullback.lift_fst _ _ _
    rw [← hh]
    have : Etale (y n) := (T n).prop
    let α : pullback a (h ≫ pullback.fst f (adicThickeningι A I n)) ⟶ (T n).left :=
      (hX n).lift (pullback.fst _ _) (pullback.snd _ _ ≫ h)
        (by rw [pullback.condition, Category.assoc])
    have hα : α ≫ k n = pullback.fst _ _ := (hX n).lift_fst _ _ _
    have hs : IsPullback (α ≫ k n) (pullback.snd a (h ≫ pullback.fst f (adicThickeningι A I n)))
        a (h ≫ pullback.fst f (adicThickeningι A I n)) := by
      rw [hα]
      exact IsPullback.of_hasPullback _ _
    exact MorphismProperty.of_isPullback (P := @Etale)
      (IsPullback.of_right hs ((hX n).lift_snd _ _ _) (hX n)) this
  -- every point of `Z` specializes into the closed fibre, so `a` is étale everywhere
  have : IsProper (a ≫ f) := haf
  have het : Etale a := by
    refine (etale_iff_forall_etaleAt a).2 fun z => ?_
    obtain ⟨z', hz', hzz'⟩ := exists_specializes_mem_range_pullback_fst_of_isProper A
      (I := I ^ (0 + 1)) (by simpa using IsAdicComplete.le_jacobson_bot I) (a ≫ f) z
    have hz'i : a z' ∈ Set.range i := by
      simp only [i, Scheme.Pullback.range_fst] at hz' ⊢
      exact hz'
    obtain ⟨U, hU, hz'U, V, hV, hUV, hUVet⟩ := hloc z' hz'i
    exact ⟨U, hU, hzz'.mem_open U.isOpen hz'U, V, hV, hUV, hUVet⟩
  exact ⟨Z, a, k 0, ha, het, hX 0⟩

/-- **Stacks 0A48, essential surjectivity over a complete Noetherian base, granted Grothendieck
existence.** Let `A` be Noetherian and `I`-adically complete and let `X` be proper over `Spec A`.
If `AdicFiniteAlgebraAlgebraization A I f` holds, base change to the closed fibre
`X ×_{Spec A} Spec (A ⧸ I)` is essentially surjective on finite étale covers. -/
theorem essSurj_finiteEtaleBaseChange_of_adicFiniteAlgebraAlgebraization
    (halg : AdicFiniteAlgebraAlgebraization A I f) :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).EssSurj := by
  have key : (finiteEtaleBaseChange (pullback.fst f (adicThickeningι A I 0))).EssSurj := by
    refine ⟨fun Q => ?_⟩
    have : IsFinite Q.hom := Q.prop.1
    have : Etale Q.hom := Q.prop.2
    obtain ⟨U, p, k, hpfin, hpet, hpb⟩ :=
      exists_finite_etale_isPullback_of_adicFiniteAlgebraAlgebraization A I f halg Q.hom
    exact ⟨MorphismProperty.Over.mk ⊤ p ⟨hpfin, hpet⟩,
      ⟨MorphismProperty.Over.isoMk hpb.isoPullback.symm hpb.isoPullback_inv_snd⟩⟩
  have htransport : ∀ J : Ideal A, J = I ^ (0 + 1) →
      (finiteEtaleBaseChange (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))).EssSurj := by
    rintro J rfl
    exact key
  exact htransport I (by rw [zero_add, pow_one])

/-- **Stacks 0A48 over a complete Noetherian base, granted Grothendieck existence.** Let `A` be
Noetherian and `I`-adically complete and let `X` be proper over `Spec A`. If
`AdicFiniteAlgebraAlgebraization A I` holds for every scheme finite étale over `X` (each of which
is again proper over `Spec A`), then base change to the closed fibre
`X ×_{Spec A} Spec (A ⧸ I)` is an equivalence of categories of finite étale covers.

Essential surjectivity over each finite étale cover of `X` is
`essSurj_finiteEtaleBaseChange_of_adicFiniteAlgebraAlgebraization`; faithfulness and fullness come
from it by the library's reduction
`isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`, the pair `(A, I)`
being henselian because `A` is `I`-adically complete. -/
theorem isEquivalence_finiteEtaleBaseChange_of_adicFiniteAlgebraAlgebraization
    (halg : ∀ P : FiniteEtaleOver X, AdicFiniteAlgebraAlgebraization A I (P.hom ≫ f)) :
    (finiteEtaleBaseChange (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj A I
    (henselianPair_of_henselianRing A I) f fun P =>
      have := isProper_comp_of_finiteEtaleOver f P
      essSurj_finiteEtaleBaseChange_of_adicFiniteAlgebraAlgebraization A I (P.hom ≫ f) (halg P)

end Complete

/-! ### The first stage of Tag 0A48 -/

/-- **Stacks 0A48 over a complete local Noetherian ring, granted Grothendieck existence.** Let
`R` be a complete local Noetherian ring and let `p : Y ⟶ Spec R` be proper. If Grothendieck
existence for finite sheaves of algebras (`AdicFiniteAlgebraAlgebraization`) holds for the proper
schemes over `Spec R`, then base change to the closed fibre `Y ×_{Spec R} Spec (R ⧸ 𝔪)` is an
equivalence of categories of finite étale covers.

The hypothesis is used for `Y` and for the schemes finite étale over `Y`, which are proper over
`Spec R` too; the conclusion is in the shape of `ProperHenselianFiniteEtaleEquivalence`. -/
theorem isEquivalence_finiteEtaleBaseChange_of_isProper_of_isAdicComplete_maximalIdeal
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
    (hp : IsProper p)
    (halg : ∀ {P : Scheme.{u}} (fP : P ⟶ Spec (.of R)), IsProper fP →
      AdicFiniteAlgebraAlgebraization R (IsLocalRing.maximalIdeal R) fP) :
    (finiteEtaleBaseChange (pullback.fst p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))))).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_adicFiniteAlgebraAlgebraization R
    (IsLocalRing.maximalIdeal R) p fun P => halg (P.hom ≫ p) (isProper_comp_of_finiteEtaleOver p P)

/-- **The conclusion of Stacks Tag 0A48 over a complete local Noetherian ring**: for every complete
local Noetherian ring `R` and every proper `p : Y ⟶ Spec R`, base change to the closed fibre
`Y ×_{Spec R} Spec (R ⧸ 𝔪)` is an equivalence on finite étale covers.

This is `ProperHenselianFiniteEtaleEquivalence` restricted to the complete local Noetherian rings
(each of which is henselian), in the same shape. -/
def ProperCompleteLocalFiniteEtaleEquivalence : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)),
    IsProper p →
      (finiteEtaleBaseChange (pullback.fst p (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))))).IsEquivalence

/-- **The first stage of the Stacks proof of Tag 0A48, granted Grothendieck existence.** If
Grothendieck existence for finite sheaves of algebras (`AdicFiniteAlgebraAlgebraization`) holds
for every proper scheme over every complete local Noetherian ring, then so does the conclusion of
Tag 0A48: base change to the closed fibre is an equivalence on finite étale covers. -/
theorem properCompleteLocalFiniteEtaleEquivalence_of_adicFiniteAlgebraAlgebraization
    (halg : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)),
      IsProper p → AdicFiniteAlgebraAlgebraization R (IsLocalRing.maximalIdeal R) p) :
    ProperCompleteLocalFiniteEtaleEquivalence.{u} := by
  intro R _ _ _ _ Y p hp
  exact isEquivalence_finiteEtaleBaseChange_of_isProper_of_isAdicComplete_maximalIdeal R p hp
    (halg R)

end AlgebraicGeometry

end
