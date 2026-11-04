module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.CartierPart
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Chart
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DivisorCover
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Writing an effective Cartier divisor as a sum of integral ones

Let `X` be a Noetherian scheme and `D ⊆ X` an effective Cartier divisor.  If the points of `D`
are covered by a family `Dᵢ` of *integral* effective Cartier divisors, then `D` is a finite
nonnegative combination `D = Σ aᵢ Dᵢ` of members of that family; in the ideal-sheaf presentation
used here, `ℐ_D = Π ℐ_{Dᵢ}^{aᵢ}`.  Such a covering family exists as soon as the local rings of `X`
along `D` are factorial, and in particular when `X` is regular.

## Main results

* `AlgebraicGeometry.isNowhereDense_supportSet_of_isEffectiveCartierDivisor`: the support of an
  effective Cartier divisor is nowhere dense.
* `AlgebraicGeometry.exists_finsupp_eq_prod_of_support_cover`: an effective Cartier divisor whose
  points are covered by integral effective Cartier divisors `Dᵢ` is a finite nonnegative
  combination of the `Dᵢ`.
* `AlgebraicGeometry.exists_pow_eq_of_supportSet_subset`: an effective Cartier divisor supported
  on an integral effective Cartier divisor `D` is a power of `D`.
* `AlgebraicGeometry.exists_integral_effectiveCartierDivisors_cover_supportSet`: if the local
  rings along `D` are factorial, or `X` is regular, such a covering family exists.

## References

* [Stacks Project, Tag 0BCP](https://stacks.math.columbia.edu/tag/0BCP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- A nonzerodivisor of the sections over a nonempty compact open of a scheme has nonempty basic
open. -/
private theorem basicOpen_ne_bot_of_isRegular {X : Scheme.{u}} {U : X.Opens}
    (hU : IsCompact (U : Set X)) {f : Γ(X, U)} (hf : _root_.IsRegular f)
    (hne : U ≠ ⊥) : X.basicOpen f ≠ ⊥ := by
  intro hbot
  obtain ⟨n, hn⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU f).mpr hbot
  have hone : (1 : Γ(X, U)) = 0 := (hf.left.pow n) (by simp [hn])
  exact hne (by rw [← X.basicOpen_one (U := U), hone, Scheme.basicOpen_zero])

/-- The restriction of a nonzerodivisor on an affine open to a basic open of it is a
nonzerodivisor. -/
private theorem isRegular_restrict_basicOpen {X : Scheme.{u}} {U W : X.affineOpens}
    (hUW : (W : X.Opens) ≤ (U : X.Opens)) (g f : Γ(X, U))
    (e : W.1 = X.basicOpen g) (hf : _root_.IsRegular f) :
    _root_.IsRegular ((X.presheaf.map (homOfLE hUW).op).hom f) := by
  let : Algebra (Γ(X, U)) (Γ(X, W)) := (X.presheaf.map (homOfLE hUW).op).hom.toAlgebra
  let : IsLocalization.Away g (Γ(X, W)) :=
    U.2.isLocalization_of_eq_basicOpen g (homOfLE hUW) e
  have hsmul : IsSMulRegular (Γ(X, W)) ((X.presheaf.map (homOfLE hUW).op).hom f) :=
    hf.isSMulRegular.of_isLocalization (Γ(X, W)) (.powers g)
  exact ⟨fun a b hab => hsmul (by simpa [Algebra.smul_def] using hab),
    fun a b hab => hsmul (by simpa [Algebra.smul_def, mul_comm] using hab)⟩

/-- The support of an effective Cartier divisor on a scheme is nowhere dense. -/
theorem isNowhereDense_supportSet_of_isEffectiveCartierDivisor
    {X : Scheme.{u}} (I : X.IdealSheafData) (hI : IsEffectiveCartierDivisor I) :
    IsNowhereDense (I.supportSet : Set X) := by
  rw [IsNowhereDense, I.isClosed_supportSet.closure_eq]
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hxInt => ?_
  have hx : x ∈ I.supportSet := interior_subset hxInt
  obtain ⟨U, hU, hxU, f, hf, e, he⟩ :=
    (isEffectiveCartierDivisor_iff_affineLocal I).mp hI x hx
  have hideal : I.ideal ⟨U, hU⟩ = Ideal.span {f} := ideal_eq_quotient_of_chart I U hU _ e he
  have hmiss : ∀ z : X, z ∈ (U : Set X) → z ∈ I.supportSet → z ∉ X.basicOpen f := by
    intro z hzU hz
    have hzero := (I.mem_supportSet_iff_of_mem (U := ⟨U, hU⟩) hzU).mp hz
    rwa [hideal, X.zeroLocus_span, X.zeroLocus_singleton] at hzero
  let V : X.Opens := ⟨interior (I.supportSet : Set X) ∩ (U : Set X), isOpen_interior.inter U.2⟩
  obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le (V := V) ⟨x, ⟨hxInt, hxU⟩⟩ hxU
  have hWU : X.basicOpen g ≤ U := X.basicOpen_le g
  have hle : X.basicOpen ((X.presheaf.map (homOfLE hWU).op).hom f) ≤
      X.basicOpen g ⊓ X.basicOpen f := le_of_eq (Scheme.basicOpen_res _ _ _)
  refine basicOpen_ne_bot_of_isRegular (hU.basicOpen g).isCompact
    (isRegular_restrict_basicOpen (U := ⟨U, hU⟩)
      (W := X.affineBasicOpen (U := ⟨U, hU⟩) g) hWU g f rfl hf)
    (fun hbot => by simp [hbot] at hxg)
    (le_antisymm (hle.trans fun z hz =>
      absurd hz.2 (hmiss z (hWU hz.1) (interior_subset (hgV hz.1).1))) bot_le)

/-- The codimension of the closure of a point of a scheme is the Krull dimension of the local
ring there. -/
@[ega "IV 21.6.2" "partial", sga "1 II 5.9" "partial"]
private theorem codimension_closureSingleton_eq_ringKrullDim_stalk
    {X : Scheme.{u}} (x : X) :
    (codimension (IrreducibleCloseds.closureSingleton x) : WithBot ℕ∞) =
      ringKrullDim (X.presheaf.stalk x) := by
  rw [codimension_eq_coheight, AlgebraicGeometry.ringKrullDim_stalk_eq_coheight,
    ← Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x]
  rfl

/-- If the closed subscheme `I` is cut out on an affine open `U` by a single section `f`, then on
any smaller affine open it is cut out by the restriction of `f`. -/
private theorem ideal_eq_span_restrict_of_chart {X : Scheme.{u}} (I : X.IdealSheafData)
    {U W : X.affineOpens} (hWU : W ≤ U) (f : Γ(X, U))
    (e : pullback I.subschemeι U.1.ι ≅ Spec (.of (Γ(X, U.1) ⧸ Ideal.span {f})))
    (he : pullback.snd I.subschemeι U.1.ι ≫ U.2.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) :
    I.ideal W = Ideal.span {(X.presheaf.map (homOfLE hWU).op).hom f} := by
  rw [← I.map_ideal hWU, ideal_eq_quotient_of_chart I U.1 U.2 (Ideal.span {f}) e he,
    Ideal.map_span]
  simp

/-- The support of a product of ideal sheaves contains the support of each factor. -/
private theorem mem_supportSet_mul_right {X : Scheme.{u}} (E J : X.IdealSheafData) {x : X}
    (hx : x ∈ J.supportSet) : x ∈ (E * J).supportSet := by
  change x ∈ ((E * J).support : Set X)
  rw [Scheme.IdealSheafData.support_mul]
  exact Or.inr (by simpa using hx)

/-- If `I = E · J` with `E` an effective Cartier divisor, and `E` and `I` agree over an open `V`,
then no point of `V` lies in the support of `J`. -/
private theorem notMem_supportSet_of_comap_eq {X : Scheme.{u}} (E I J : X.IdealSheafData)
    (hE : IsEffectiveCartierDivisor E) (V : X.Opens) (hIE : E.comap V.ι = I.comap V.ι)
    (hIJ : I = E * J) {x : X} (hxJ : x ∈ J.supportSet) (hxV : x ∈ V) : False := by
  have hxI : x ∈ I.supportSet := hIJ ▸ mem_supportSet_mul_right E J hxJ
  have hsup : (E.support.preimage V.ι.continuous : Set V.toScheme) =
      (I.support.preimage V.ι.continuous : Set V.toScheme) := by
    simpa only [Scheme.IdealSheafData.support_comap] using
      congrArg (fun K : V.toScheme.IdealSheafData => (K.support : Set V.toScheme)) hIE
  have hxE : x ∈ E.supportSet := (Set.ext_iff.mp hsup ⟨x, hxV⟩).mpr (show
      (⟨x, hxV⟩ : V.toScheme) ∈ (I.support.preimage V.ι.continuous : Set V.toScheme) from hxI)
  obtain ⟨V₀, hV₀, hxV₀, f, hf, e, he⟩ :=
    (isEffectiveCartierDivisor_iff_affineLocal E).mp hE x hxE
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hxW₀, hW₀V⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.2
  obtain ⟨f₀, g₀, hfg, hxW⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter hV₀ hW₀ x ⟨hxV₀, hxW₀⟩
  let W : X.affineOpens := X.affineBasicOpen (U := ⟨V₀, hV₀⟩) f₀
  have hWV₀ : W ≤ (⟨V₀, hV₀⟩ : X.affineOpens) := X.affineBasicOpen_le _
  have hWV : (W : X.Opens) ≤ V := by
    refine fun z hz => hW₀V (X.basicOpen_le g₀ ?_)
    rw [← hfg]
    simpa [W] using hz
  let fW : Γ(X, W) := (X.presheaf.map (homOfLE hWV₀).op).hom f
  have hfW : _root_.IsRegular fW := isRegular_restrict_basicOpen hWV₀ f₀ f rfl hf
  have hEspan : E.ideal W = Ideal.span {fW} :=
    ideal_eq_span_restrict_of_chart E hWV₀ f e he
  have hWcomp : E.comap W.1.ι = I.comap W.1.ι := by
    simpa only [← Scheme.homOfLE_ι X hWV, Scheme.IdealSheafData.comap_comp] using
      congrArg (fun K => K.comap (X.homOfLE hWV)) hIE
  have hWideal : E.ideal W = I.ideal W :=
    eq_of_heq ((ideal_comap_top_heq E W).symm.trans
      ((heq_of_eq (congrArg
        (fun K : W.1.toScheme.IdealSheafData => K.ideal ⟨⊤, isAffineOpen_top W.1⟩)
        hWcomp)).trans (ideal_comap_top_heq I W)))
  have hprincipal : Ideal.span {fW} = Ideal.span {fW} * J.ideal W := by
    calc Ideal.span {fW} = E.ideal W := hEspan.symm
      _ = I.ideal W := hWideal
      _ = (E * J).ideal W := by rw [hIJ]
      _ = E.ideal W * J.ideal W := by simp
      _ = Ideal.span {fW} * J.ideal W := by rw [hEspan]
  obtain ⟨z, hzJ, hmul⟩ := Ideal.mem_span_singleton_mul.mp
    (hprincipal ▸ Ideal.subset_span (Set.mem_singleton fW))
  have hJtop : J.ideal W = ⊤ := (J.ideal W).eq_top_iff_one.mpr
    (by simpa [hfW.left (show fW * z = fW * 1 by simpa using hmul)] using hzJ)
  have hxW' : x ∈ (W : X.Opens) := by simpa [W] using hxW
  exact (by simpa [hJtop] using (J.mem_supportSet_iff_of_mem hxW').mp hxJ :
    x ∉ (W : X.Opens)) hxW'

/-- Every point of the support of an effective Cartier divisor on a locally Noetherian scheme is
a specialisation of a point of the support whose closure has codimension one. -/
private theorem exists_specializes_codimension_eq_one {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : IsEffectiveCartierDivisor I) {x : X} (hx : x ∈ I.supportSet) :
    ∃ y ∈ I.supportSet, y ⤳ x ∧
      codimension (IrreducibleCloseds.closureSingleton y) = 1 := by
  obtain ⟨ξ, hξ⟩ : x ∈ Set.range I.subschemeι := by rw [I.range_subschemeι]; exact hx
  let c : irreducibleComponents I.subscheme :=
    ⟨irreducibleComponent ξ, irreducibleComponent_mem_irreducibleComponents ξ⟩
  let η : I.subscheme := genericPoints.ofComponent c
  have hη : IsGenericPoint η (c : Set I.subscheme) := genericPoints.isGenericPoint_ofComponent c
  have hrange : I.subschemeι η ∈ I.supportSet := by
    have h : I.subschemeι η ∈ Set.range I.subschemeι := ⟨η, rfl⟩
    rwa [I.range_subschemeι] at h
  refine ⟨I.subschemeι η, hrange, ?_, ?_⟩
  · simpa [hξ] using (hη.specializes mem_irreducibleComponent).map I.subschemeι.continuous
  · refine WithBot.coe_injective ?_
    rw [codimension_closureSingleton_eq_ringKrullDim_stalk]
    exact ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor I hI η ⟨c, hη⟩

/-- If `I = E · J` with `E` and `J` effective Cartier divisors, `E` and `I` agree over an open `V`,
and `V` contains every point of `I` whose closure has codimension one, then `I = E`. -/
private theorem eq_of_mul_eq_of_codimension_one_mem {X : Scheme.{u}} [IsLocallyNoetherian X]
    (E I J : X.IdealSheafData) (hE : IsEffectiveCartierDivisor E)
    (hJ : IsEffectiveCartierDivisor J) (hIJ : I = E * J) (V : X.Opens)
    (hIE : E.comap V.ι = I.comap V.ι)
    (hV : ∀ y ∈ I.supportSet, codimension (IrreducibleCloseds.closureSingleton y) = 1 → y ∈ V) :
    I = E := by
  have hJempty : J.supportSet = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hxJ => ?_
    obtain ⟨y, hyJ, -, hycod⟩ := exists_specializes_codimension_eq_one J hJ hxJ
    have hyI : y ∈ I.supportSet := hIJ ▸ mem_supportSet_mul_right E J hyJ
    exact notMem_supportSet_of_comap_eq E I J hE V hIE hIJ hyJ (hV y hyI hycod)
  rw [hIJ, (Scheme.IdealSheafData.support_eq_bot_iff (I := J)).mp (SetLike.coe_injective hJempty)]
  simp

/-- Let `X` be a Noetherian scheme and `D` an effective Cartier divisor on `X` whose points are
covered by a family `Dᵢ` of integral effective Cartier divisors. Then `D` is a finite nonnegative
combination of the `Dᵢ`: there is a finitely supported `a : ι →₀ ℕ` with
`ℐ_D = Π ℐ_{Dᵢ}^{aᵢ}`. -/
@[stacks 0BCP "decomposition"]
theorem exists_finsupp_eq_prod_of_support_cover
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I)
    {ι : Type v} (D : ι → X.IdealSheafData)
    (hD : ∀ i, IsIntegral (D i).subscheme ∧ IsEffectiveCartierDivisor (D i))
    (hcover : ∀ x ∈ I.supportSet, ∃ i, x ∈ (D i).supportSet) :
    ∃ a : ι →₀ ℕ, I = a.prod fun i n => D i ^ n := by
  classical
  obtain ⟨a, hEeff, hIEle, V, hEIeq, hcod⟩ :=
    exists_effectiveCartierDivisor_agree_off_codimension_two X I D ⊥ hD
      (by intro x hx; simp at hx)
      (fun x hx => Set.mem_union_right _
        (Set.mem_iUnion.mpr (hcover x (by simpa using hx))))
  set E : X.IdealSheafData := a.prod fun i n => D i ^ n with hE
  obtain ⟨J, hJeff, hIJ⟩ := exists_isEffectiveCartierDivisor_mul_eq_of_le E I hEeff hI hIEle
  refine ⟨a, eq_of_mul_eq_of_codimension_one_mem E I J hEeff hJeff hIJ V hEIeq
    fun y hyI hycod => ?_⟩
  by_contra hyV
  have hlarge := hcod y (by simpa using hyI) hyV
  norm_num [hycod] at hlarge

/-- On a locally Noetherian scheme, an effective Cartier divisor supported on an integral
effective Cartier divisor `D` is a power of `D`. -/
theorem exists_pow_eq_of_supportSet_subset
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I D : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (hDint : IsIntegral D.subscheme)
    (hD : IsEffectiveCartierDivisor D) (hsub : I.supportSet ⊆ D.supportSet) :
    ∃ k : ℕ, I = D ^ k := by
  let _ : IsIntegral D.subscheme := hDint
  obtain ⟨k, hDk, hle, U, hUeq, hU⟩ :=
    exists_le_pow_comap_eq_of_supportSet_subset I D hD hsub
  obtain ⟨J, hJeff, hIJ⟩ := exists_isEffectiveCartierDivisor_mul_eq_of_le (D ^ k) I hDk hI hle
  exact ⟨k, eq_of_mul_eq_of_codimension_one_mem (D ^ k) I J hDk hJeff hIJ U hUeq.symm
    fun y hyI hycod => hU y hyI hycod⟩

/-- Let `X` be a Noetherian scheme and `D` an effective Cartier divisor on `X`. If the local rings
of `X` at the points of `D` are unique factorization domains — in particular if `X` is regular —
then there is a family of integral effective Cartier divisors covering the points of `D`. -/
@[stacks 0BCP "existence of the covering divisors"]
theorem exists_integral_effectiveCartierDivisors_cover_supportSet
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I)
    (h : (∀ x : X, x ∈ I.supportSet → UniqueFactorizationMonoid (X.presheaf.stalk x)) ∨
      IsRegular X) :
    ∃ S : Set X.IdealSheafData,
      (∀ J ∈ S, IsIntegral J.subscheme ∧ IsEffectiveCartierDivisor J) ∧
      (∀ x ∈ I.supportSet, ∃ J ∈ S, x ∈ J.supportSet) := by
  obtain ⟨D, Z, hD, hZ, hcover⟩ :=
    exists_integral_effectiveCartierDivisors_cover X I
      (isNowhereDense_supportSet_of_isEffectiveCartierDivisor I hI) h
  refine ⟨D, hD, fun x hx => ?_⟩
  obtain ⟨y, hyI, hyx, hycod⟩ := exists_specializes_codimension_eq_one I hI hx
  rcases (Set.mem_union _ _ _).mp (hcover hyI) with hyZ | hyDiv
  · have hc := hZ y hyZ
    norm_num [hycod] at hc
  · obtain ⟨J, hyJ⟩ := Set.mem_iUnion.mp hyDiv
    obtain ⟨hJD, hyJ⟩ := Set.mem_iUnion.mp hyJ
    exact ⟨J, hJD, (specializes_iff_forall_closed.mp hyx _ J.isClosed_supportSet) hyJ⟩

end AlgebraicGeometry

end
