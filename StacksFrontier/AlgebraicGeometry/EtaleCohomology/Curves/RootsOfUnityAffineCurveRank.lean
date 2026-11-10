module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.AffineCurveRankCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.AffineCurveRankData
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurveGmVanishing

/-!
# Tag 03RR with the rank count proved

This file discharges the rank count `hunits`, `htors`, `hrank` of
`AlgebraicGeometry.nonempty_etaleH1RootsOfUnityAddEquivZModPow` (clause (2) of
[Stacks, Tag 03RR]) and the divisibility `hdvd` of clause (3), for an *affine* smooth curve `X`
with smooth projective compactification `X̄`, over exactly the two inputs about `X̄` that
[Stacks, Tag 03RQ] carries as well:

* `hdvd₀`, that `Pic⁰(X̄)` is `n`-divisible ([Stacks, Tag 03RP] (4) for the Jacobian of
  [Stacks, Tag 0BA0]);
* `hgenus`, that `Pic⁰(X̄)[n] ≅ (𝐙/n𝐙)^{2g}` ([Stacks, Tag 03RP] (7)).

The argument is the source's: the Kummer sequence presents `H¹_ét(X, μ_n)` as an extension of
`Pic(X)[n]` by `Γ(X, 𝒪_X)^*/n`; `Pic(X)` is `Pic(X̄)` modulo the classes of the punctures
(`AlgebraicGeometry.AffineCurveRankData.ker_restrictPicard`); the units of `X` modulo constants
are the relations among those classes
(`AlgebraicGeometry.AffineCurveRankData.mem_range_ordHom_iff`,
`AlgebraicGeometry.AffineCurveRankData.exists_nsmul_eq_of_ordHom_eq_zero`); and the rank count is
then group theory, `AlgebraicGeometry.AffineCurveRankCount.nonempty_addEquiv_of_rankData`, which
goes through the source's group of triples `(L̄, D, ᾱ)`.

## Main results

* `AlgebraicGeometry.nonempty_etaleH1RootsOfUnity_affineCurve_of_jacobian`: clause (2).
* `AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_picardDegreeZero`: all
  three clauses.

## References

* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry.AffineCurveRankCount
  AlgebraicGeometry.AffineCurveRankData

universe t u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

/-! ### An affine curve is not proper -/

section NotProper

/-- Every prime of a ring that is a field is zero, so its spectrum is a point. -/
theorem subsingleton_primeSpectrum_of_isField {R : Type u} [CommRing R] (hR : IsField R) :
    Subsingleton (PrimeSpectrum R) := by
  have key : ∀ p : PrimeSpectrum R, p.asIdeal = ⊥ := by
    intro p
    rw [Submodule.eq_bot_iff]
    intro a ha
    by_contra h0
    obtain ⟨b, hb⟩ := hR.mul_inv_cancel h0
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem ha (IsUnit.of_mul_eq_one b hb))
  exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩

variable (k : Type u) [Field k] {X Xbar : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k f] [IsProper fbar] (j : X ⟶ Xbar) [IsOpenImmersion j]

include fbar in
/-- **An affine curve has at least one puncture**: if `j` were onto, `X` would be affine and
proper, so a point. -/
theorem nonempty_compl_range [IsAffine X] (hj : j ≫ fbar = f) :
    (Set.range j.base)ᶜ.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hne
  have : IsIso j := (isIso_iff_isOpenImmersion_and_epi_base j).2
    ⟨inferInstance, (TopCat.epi_iff_surjective _).2 (Set.range_eq_univ.1 hne)⟩
  have : UniversallyClosed f := by
    rw [← hj]
    infer_instance
  have : Subsingleton X := by
    have : Subsingleton ↥(Spec Γ(X, ⊤)) :=
      subsingleton_primeSpectrum_of_isField (isField_of_universallyClosed k f)
    exact ⟨fun a b => X.isoSpec.hom.isOpenEmbedding.injective (Subsingleton.elim _ _)⟩
  have h₁ : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_zero] at h₁
  norm_num at h₁

end NotProper

/-! ### Enumerating the punctures -/

section Punctures

variable (k : Type u) [Field k] [IsAlgClosed k] {X Xbar : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsCurve k fbar] [Smooth fbar]
  [IsProjectiveVariety k fbar] [IsNoetherian Xbar] (j : X ⟶ Xbar) [IsOpenImmersion j]

omit [IsAlgClosed k] [Smooth f] [Smooth fbar] in
include f in
/-- **The punctures of an affine curve**: `X̄ ∖ X` is a nonempty finite set of closed points of
coheight one, enumerated by `Fin r` when it has `r` elements. -/
theorem exists_punctures [IsAffine X] (hj : j ≫ fbar = f) (r : ℕ)
    (hr : Nat.card ↥(Set.range j.base)ᶜ = r) :
    ∃ r' : ℕ, r = r' + 1 ∧ ∃ x : Fin (r' + 1) → Xbar, Function.Injective x ∧
      (∀ y, y ∉ Set.range j.base ↔ y ∈ Set.range x) ∧ ∀ i, x i ≠ genericPoint Xbar := by
  have : IsNoetherian X := AffineCurveRankData.isNoetherian k f
  have hgen : ∀ y, y ∉ Set.range j.base → y ≠ genericPoint Xbar := fun y hy h =>
    hy (h ▸ genericPoint_mem_range k f fbar j)
  have hfin : (Set.range j.base)ᶜ.Finite :=
    (Stacks.AlgebraicGeometry.UnitsBoundaryValuations.finite_coheight_one_notMem
      (fun _ _ => Scheme.le_iff_specializes) j.isOpenEmbedding.isOpen_range
      (genericPoint_mem_range k f fbar j)).subset fun y hy =>
        ⟨(coheight_eq_one_and_isClosed k fbar (hgen y hy)).1, hy⟩
  have : Finite ↥(Set.range j.base)ᶜ := hfin.to_subtype
  have : Nonempty ↥(Set.range j.base)ᶜ := (nonempty_compl_range k f fbar j hj).to_subtype
  obtain ⟨r', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (hr ▸ Nat.card_pos.ne')
  let e : ↥(Set.range j.base)ᶜ ≃ Fin (r' + 1) := (Finite.equivFin _).trans (finCongr hr)
  refine ⟨r', rfl, fun i => (e.symm i).1, Subtype.val_injective.comp e.symm.injective,
    fun y => ⟨fun hy => ⟨e ⟨y, hy⟩, by simp⟩, ?_⟩, fun i => hgen _ (e.symm i).2⟩
  rintro ⟨i, rfl⟩
  exact (e.symm i).2

include f in
/-- **`Pic(X)` is `n`-divisible** when `Pic⁰(X̄)` is: `Pic(X)` is a quotient of `Pic(X̄)` in
which the class of a puncture, of degree one, dies, so it is a quotient of `Pic⁰(X̄)`. -/
theorem exists_nsmul_eq_schemePicard_of_picardDegreeZero [IsAffine X] [IsNoetherian X]
    (hj : j ≫ fbar = f) (n : ℕ)
    (hdvd₀ : ∀ x ∈ curvePicardDegreeZero k Xbar fbar, ∃ y, n • y = x) :
    ∀ q : schemePicard X, ∃ y, q = n • y := by
  have : IsDominant j := isDominant_of_isOpenImmersion_of_isIntegral j
  obtain ⟨r', -, x, hxinj, hxS, hxg⟩ := exists_punctures k f fbar j hj _ rfl
  set deg := picardDegree k fbar (AffineCurveRankData.topologicalKrullDim_le_one k fbar)
  set c0 := cls k fbar x hxg 0
  have hc0 : restrictPicard k f fbar j c0 = 0 := by
    rw [← AddMonoidHom.mem_ker, ker_restrictPicard k f fbar j x hxinj hxS hxg]
    exact AddSubgroup.subset_closure ⟨0, rfl⟩
  intro q
  obtain ⟨p, rfl⟩ := surjective_restrictPicard k f fbar j q
  obtain ⟨y, hy⟩ := hdvd₀ (p - deg p • c0) (by
    change deg (p - deg p • c0) = 0
    rw [map_sub, map_zsmul, picardDegree_cls k fbar x hxg 0, smul_eq_mul, mul_one, sub_self])
  refine ⟨restrictPicard k f fbar j y, ?_⟩
  rw [← map_nsmul, hy, map_sub, map_zsmul, hc0, smul_zero, sub_zero]

end Punctures

/-! ### The rank count -/

section AffineCurve

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]

omit [IsAlgClosed k] [IsCurve k f] [Smooth f] in
include f in
/-- **The kernel of `H¹_ét(X, μ_n) ⟶ Pic(X)[n]` is `Γ(X, 𝒪_X)^*/n`.** -/
theorem nonempty_ker_etaleH1RootsOfUnityToPicardNTorsion_addEquiv (hn : IsUnit (n : k)) :
    Nonempty (↥(etaleH1RootsOfUnityToPicardNTorsion k X f B hX n hn).ker ≃+
      Additive Γ(X, ⊤)ˣ ⧸ nsmulRange n (Additive Γ(X, ⊤)ˣ)) := by
  let κ : Additive Γ(X, ⊤)ˣ →+ Sheaf.H (kummerSmallEtale B X hX n).X₁ 1 :=
    kummerBoundaryHom (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX) n (kummerSmallEtale_shortExact k X f B hX n hn)
    (SmallEtale.finalIsTerminal B X hX)
  have hκ : κ.ker = nsmulRange n (Additive Γ(X, ⊤)ˣ) := by
    ext x
    rw [AddMonoidHom.mem_ker, mem_nsmulRange]
    refine (kummerBoundary_eq_zero_iff (SmallEtale.topology B X hX)
      (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n
      (kummerSmallEtale_shortExact k X f B hX n hn) (SmallEtale.finalIsTerminal B X hX)
      x.toMul).trans ⟨?_, ?_⟩
    · rintro ⟨b, hb⟩
      exact ⟨Additive.ofMul b, Additive.toMul.injective ((toMul_nsmul n _).trans hb.symm)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y.toMul, toMul_nsmul n y⟩
  have : (nsmulRange n (Additive Γ(X, ⊤)ˣ)).Normal :=
    ⟨fun a ha g => by rwa [add_comm g a, add_neg_cancel_right]⟩
  have : κ.ker.Normal := ⟨fun a ha g => by rwa [add_comm g a, add_neg_cancel_right]⟩
  exact ⟨(AddEquiv.addSubgroupCongr
    ((ker_etaleH1RootsOfUnityToPicardNTorsion k X f B hX n hn).trans
      (ker_etaleH1RootsOfUnityToPicard_eq_range_kummerBoundaryHom k X f B hX n hn))).trans
    ((QuotientAddGroup.quotientKerEquivRange κ).symm.trans
      (QuotientAddGroup.quotientAddEquivOfEq hκ))⟩

/-- `Pic(X̄)[n] = Pic⁰(X̄)[n]` on a projective curve: torsion has degree zero. -/
def torsionEquivCurvePicardDegreeZeroTorsion {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k))
    [IsCurve k fbar] [IsProjectiveVariety k fbar] (hn : n ≠ 0) :
    ↥(torsion n (schemePicard Xbar)) ≃+ ↥(curvePicardDegreeZeroTorsion k Xbar fbar n) where
  toFun t := ⟨⟨t.1, by
      have h := congrArg (curvePicardDegree k Xbar fbar) (AddMonoidHom.mem_ker.1 t.2)
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, map_nsmul, map_zero,
        smul_eq_zero, hn, false_or] at h
      exact h⟩,
      Subtype.ext (AddMonoidHom.mem_ker.1 t.2)⟩
  invFun s := ⟨s.1.1, AddMonoidHom.mem_ker.2 (congrArg Subtype.val s.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

include f in
/-- **Clause (2) of [Stacks, Tag 03RR]: `H¹_ét(X, μ_n) ≅ (𝐙/n𝐙)^{2g + r - 1}`**, for an affine
smooth curve over exactly the two inputs about `X̄` that [Stacks, Tag 03RQ] carries. -/
theorem nonempty_etaleH1RootsOfUnity_affineCurve_of_jacobian (hn : IsUnit (n : k)) [IsAffine X]
    {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar] [Smooth fbar]
    [IsProjectiveVariety k fbar] (j : X ⟶ Xbar) [IsOpenImmersion j] (hj : j ≫ fbar = f)
    (r : ℕ) (hr : Nat.card ↥(Set.range j.base)ᶜ = r)
    (hdvd₀ : ∀ x ∈ curvePicardDegreeZero k Xbar fbar, ∃ y, n • y = x)
    (hgenus : Nonempty (↥(curvePicardDegreeZeroTorsion k Xbar fbar n) ≃+
      (Fin (2 * genus fbar) → ZMod n))) :
    Nonempty (Sheaf.H (kummerSmallEtale B X hX n).X₁ 1 ≃+
      (Fin (2 * genus fbar + r - 1) → ZMod n)) := by
  have hn0 : n ≠ 0 := ne_zero_of_isUnit_natCast k n hn
  have : NeZero n := ⟨hn0⟩
  have : IsNoetherian X := AffineCurveRankData.isNoetherian k f
  have : IsNoetherian Xbar := AffineCurveRankData.isNoetherian k fbar
  have : IsDominant j := isDominant_of_isOpenImmersion_of_isIntegral j
  obtain ⟨r', rfl, x, hxinj, hxS, hxg⟩ := exists_punctures k f fbar j hj r hr
  -- the rank count
  obtain ⟨eπ⟩ := nonempty_ker_etaleH1RootsOfUnityToPicardNTorsion_addEquiv k X f B hX n hn
  obtain ⟨eg⟩ := hgenus
  obtain ⟨E⟩ := nonempty_addEquiv_of_rankData
    (deg := picardDegree k fbar (AffineCurveRankData.topologicalKrullDim_le_one k fbar))
    (c := cls k fbar x hxg) (picardDegree_cls k fbar x hxg)
    (restrictPicard k f fbar j) (surjective_restrictPicard k f fbar j)
    (ker_restrictPicard k f fbar j x hxinj hxS hxg)
    (fun p hp => (hdvd₀ p hp).imp fun _ => Eq.symm)
    ⟨(torsionEquivCurvePicardDegreeZeroTorsion k n fbar hn0).trans eg⟩
    (ordHom j x)
    (exists_nsmul_eq_of_ordHom_eq_zero k f fbar j x hxinj hxS hxg (Nat.pos_of_ne_zero hn0))
    (mem_range_ordHom_iff k f fbar j x hxinj hxS hxg)
    (nsmul_sheafH_rootsOfUnitySheaf_eq_zero (SmallEtale.topology B X hX)
      (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n 1)
    (etaleH1RootsOfUnityToPicardNTorsion k X f B hX n hn)
    (surjective_etaleH1RootsOfUnityToPicardNTorsion k X f B hX n hn) ⟨eπ⟩
  rw [show 2 * genus fbar + (r' + 1) - 1 = 2 * genus fbar + r' by lia]
  exact ⟨E⟩

include f in
/-- **[Stacks, Tag 03RR], all three clauses**, for an affine smooth curve `X` with smooth
projective compactification `X̄`, over the two inputs about `X̄` that [Stacks, Tag 03RQ] carries
as well, `Pic⁰(X̄)` divisible by `n` and `Pic⁰(X̄)[n] ≅ (𝐙/n𝐙)^{2g}`:

* `H⁰_ét(X, μ_n) = μ_n(k)`;
* `H¹_ét(X, μ_n) ≅ (𝐙/n𝐙)^{2g + r - 1}`;
* `H^q_ét(X, μ_n) = 0` for `q ≥ 2`. -/
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_of_picardDegreeZero (hn : IsUnit (n : k))
    [IsAffine X] {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar] [Smooth fbar]
    [IsProjectiveVariety k fbar] (j : X ⟶ Xbar) [IsOpenImmersion j] (hj : j ≫ fbar = f)
    (r : ℕ) (hr : Nat.card ↥(Set.range j.base)ᶜ = r)
    (hdvd₀ : ∀ x ∈ curvePicardDegreeZero k Xbar fbar, ∃ y, n • y = x)
    (hgenus : Nonempty (↥(curvePicardDegreeZeroTorsion k Xbar fbar n) ≃+
      (Fin (2 * genus fbar) → ZMod n))) :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) ∧
      Nonempty (Sheaf.H (kummerSmallEtale B X hX n).X₁ 1 ≃+
        (Fin (2 * genus fbar + r - 1) → ZMod n)) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale B X hX n).X₁ q) := by
  have : IsNoetherian X := AffineCurveRankData.isNoetherian k f
  have : IsNoetherian Xbar := AffineCurveRankData.isNoetherian k fbar
  obtain ⟨h0, h3⟩ := etaleCohomology_rootsOfUnity_affineSmoothCurve_clauses_one_three_of_gm
    k X f B hX n hn (exists_nsmul_eq_schemePicard_of_picardDegreeZero k f fbar j hj n hdvd₀)
  exact ⟨h0, nonempty_etaleH1RootsOfUnity_affineCurve_of_jacobian k X f B hX n hn fbar j hj r hr
    hdvd₀ hgenus, h3⟩

end AffineCurve

end AlgebraicGeometry

end
