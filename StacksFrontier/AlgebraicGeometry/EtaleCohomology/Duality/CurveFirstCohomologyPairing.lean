module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CyclicCoverSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PicardDegreeZeroDivisible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FiniteEtaleExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MainstreamRepresentability
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen

/-!
# Nondegeneracy of the cup product on `H¹` of a curve with `ℤ/ℓ` coefficients

Let `X` be a smooth proper connected curve over an algebraically closed field `k`, `ℓ` a prime
invertible in `k`, and `Λ = ℤ/ℓ`. For every nonzero `a ∈ H¹(X, Λ) = Ext¹(Λ_X, Λ_X)` there is an
`x ∈ H¹(X, Λ)` with `x ∪ a = x ∘ a ≠ 0` in `H²(X, Λ) = Ext²(Λ_X, Λ_X)`.

Write `a` as the class of an extension `0 → Λ_X → E → Λ_X → 0`. Its torsor `P = ε⁻¹(1)` is finite
locally constant, represented by a finite étale `π : V → X`, and `Λ[P] ≅ π_* Λ_V`. Since `a ≠ 0`,
`Λ[P]` has at most `ℓ` global sections (`finite_and_natCard_hom_unitSheaf_freeTorsor_le`), and
these are the locally constant `ℤ/ℓ`-valued maps on `V`; so `V` is connected, hence again a
smooth proper curve, and `#H²(X, Λ[P]) = #H²(V, Λ) = ℓ` given that `Pic⁰(V)` is `ℓ`-divisible.
The filtration of `Λ[P]` by the cokernels of the powers of `s = τ - 1`, with steps `Λ_X` and
`H³(X, Λ) = 0`, makes `H²(X, E) = H²(X, coker s²)` a quotient of `H²(X, Λ[P])`, so
`#H²(X, E) ≤ ℓ = #H²(X, Λ)`, and the connecting map `x ↦ x ∘ a` of the extension is onto
`H²(X, Λ)`, which is nonzero.

The divisibility of `Pic⁰` of the smooth proper curves over `k` that enters is the
`ℓ`-divisibility of the Jacobian, `Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero`.

## Main results

* `Stacks.EtaleCohomology.ExtensionTorsor.connectedSpace_of_extClass_ne_zero`: the cyclic cover of
  a nonsplit extension is connected.
* `Stacks.EtaleCohomology.ExtensionTorsor.exists_comp_ne_zero_of_ne_zero`: the nondegeneracy.
* `Stacks.EtaleCohomology.ExtensionTorsor.bijective_bilinearComp_flip`: perfectness, given that
  `H¹(X, ℤ/ℓ)` is finite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.ExtensionTorsor

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : EtaleModules.{u, 0} (ZMod ℓ) X}
  {i : unitSheaf ℓ ⟶ E} {ε : E ⟶ unitSheaf ℓ} {w : i ≫ ε = 0}
  (hS : (ShortComplex.mk i ε w).ShortExact)

section Cover

variable {V : X.Etale} [IsFinite V.hom]
  (e : torsor i ε w ≅ X.smallEtaleTopology.uliftYoneda.{u + 1}.obj V)

/-- `Λ[P] ≅ π_* Λ_V` for the finite étale `π : V → X` representing the torsor. -/
def freeTorsorIsoDirectImage :
    letI : Etale V.hom := V.prop
    freeTorsor (i := i) (ε := ε) (w := w) ≅ (etaleModuleDirectImage.{u, 0} (ZMod ℓ) V.hom).obj
      (unitSheaf (X := V.left) ℓ) :=
  etaleModuleFreeIsoDirectImage (ZMod ℓ) (torsor i ε w) V e

/-- `Hⁿ(X, Λ[P]) ≃ Hⁿ(V, Λ)`. -/
def extFreeTorsorEquiv (n : ℕ) :
    Ext (unitSheaf (X := X) ℓ) (freeTorsor (i := i) (ε := ε) (w := w)) n ≃
      Ext (unitSheaf (X := V.left) ℓ) (unitSheaf (X := V.left) ℓ) n :=
  letI : Etale V.hom := V.prop
  ((extFunctorObj (unitSheaf (X := X) ℓ) n).mapIso
    (freeTorsorIsoDirectImage e)).addCommGroupIsoToAddEquiv.toEquiv.trans
      (extConstantDirectImageAddEquiv (ZMod ℓ) V.hom (unitSheaf (X := V.left) ℓ) n).toEquiv

include e in
/-- `Γ(X, Λ[P])` is the set of locally constant `ℤ/ℓ`-valued maps on `V`. -/
theorem natCard_hom_unitSheaf_freeTorsor :
    Nat.card (unitSheaf (X := X) ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w)) =
      Nat.card (LocallyConstant V.left (ZMod ℓ)) := by
  rw [← natCard_hom_unitSheaf_unitSheaf]
  exact Nat.card_congr ((Ext.homEquiv₀.symm.trans (extFreeTorsorEquiv e 0)).trans Ext.homEquiv₀)

end Cover

include hS in
/-- **`Λ[P]` has a nonzero global section**: `Λ_X ≅ coker s --s^{ℓ-1}--> Λ[P]` is a monomorphism
and `Λ_X ≠ 0`. -/
theorem one_lt_natCard_hom_unitSheaf_freeTorsor [ConnectedSpace X] :
    ∃ g : unitSheaf ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w), g ≠ 0 := by
  have hp : ℓ.Prime := Fact.out
  have := isIso_cokernelShiftDesc hS
  have hcancel := fun (a b : unitSheaf ℓ ⟶ cokernel (shift hS ^ 1).asHom) =>
    (exists_comp_cokernelPowLift_shift_and_cancel hS hp.one_le).2 (A := unitSheaf ℓ) a b
  have hpow : (shift hS ^ 1).asHom = (shift hS).asHom := by rw [pow_one]
  refine ⟨(inv (cokernelShiftDesc hS) ≫ (cokernelIsoOfEq hpow).inv) ≫
    Stacks.Abelian.cokernelPowLift (shift hS) (shift_pow_self hS) hp.one_le, fun h => ?_⟩
  have h0 := hcancel _ 0 (by rw [h, zero_comp])
  have h1 : (𝟙 (unitSheaf (X := X) ℓ) : unitSheaf ℓ ⟶ unitSheaf ℓ) = 0 := by
    simpa using
      congrArg (· ≫ (cokernelIsoOfEq hpow).hom ≫ cokernelShiftDesc hS) h0
  have h2 : Nat.card (unitSheaf (X := X) ℓ ⟶ unitSheaf ℓ) ≤ 1 := by
    have : Subsingleton (unitSheaf (X := X) ℓ ⟶ unitSheaf ℓ) := ⟨fun a b => by
      rw [← Category.id_comp a, ← Category.id_comp b, h1, zero_comp, zero_comp]⟩
    exact (Nat.card_of_subsingleton (𝟙 _)).le
  rw [natCard_end_unitSheaf] at h2
  exact absurd h2 (not_le.2 hp.one_lt)

include hS in
/-- **The cyclic cover of a nonsplit extension is connected.** -/
theorem connectedSpace_of_extClass_ne_zero [ConnectedSpace X] (hne : hS.extClass ≠ 0)
    {V : X.Etale} [IsFinite V.hom]
    (e : torsor i ε w ≅ X.smallEtaleTopology.uliftYoneda.{u + 1}.obj V) :
    ConnectedSpace V.left := by
  have hp : ℓ.Prime := Fact.out
  obtain ⟨hfin, hle⟩ := finite_and_natCard_hom_unitSheaf_freeTorsor_le hS hne
  rw [natCard_hom_unitSheaf_freeTorsor e] at hle
  have hfin' : Finite (LocallyConstant V.left (ZMod ℓ)) :=
    Finite.of_equiv _ ((((Ext.homEquiv₀.symm.trans (extFreeTorsorEquiv e 0)).trans
      Ext.homEquiv₀).trans ((homUnitSheafEquiv ℓ _).trans (unitSheafSectionsEquiv ℓ))).trans
        (LocallyConstant.congrRight Equiv.ulift))
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have : PreconnectedSpace V.left :=
    preconnectedSpace_of_natCard_locallyConstant_le (A := ZMod ℓ)
      (by rw [Nat.card_zmod]; exact hp.two_le) (by rwa [Nat.card_zmod])
  refine ⟨?_⟩
  by_contra hempty
  rw [not_nonempty_iff] at hempty
  obtain ⟨g, hg⟩ := one_lt_natCard_hom_unitSheaf_freeTorsor hS
  have h1 : Nat.card (unitSheaf (X := X) ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w)) ≤ 1 := by
    rw [natCard_hom_unitSheaf_freeTorsor e]
    have : Subsingleton (LocallyConstant V.left (ZMod ℓ)) :=
      ⟨fun a b => LocallyConstant.ext fun x => (IsEmpty.false x).elim⟩
    exact (Nat.card_of_subsingleton (0 : LocallyConstant V.left (ZMod ℓ))).le
  have : Finite (unitSheaf (X := X) ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w)) := hfin
  exact hg ((Finite.card_le_one_iff_subsingleton.1 h1).elim g 0)

section Curve

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f]

/-- **A connected finite étale cover of a smooth proper curve is a curve**: it is integral, being
connected and smooth over `k`; an étale map does not raise the dimension and a finite surjective
one does not lower it. -/
theorem isCurve_comp_of_isFinite {V : X.Etale} [IsFinite V.hom] [ConnectedSpace V.left] :
    IsCurve k (V.hom ≫ f) := by
  have : Etale V.hom := V.prop
  have : IsIntegral V.left := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (V.hom ≫ f)
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have : ConnectedSpace X := inferInstanceAs (ConnectedSpace X)
  have : Nonempty V.left := ConnectedSpace.toNonempty
  have hdimX : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one f
  let Y : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ V.hom ⟨inferInstance, inferInstance⟩
  have : Nonempty Y.left := inferInstanceAs (Nonempty V.left)
  have hle : topologicalKrullDim V.left ≤ 1 := hdimX ▸ topologicalKrullDim_le_of_etale V.hom
  have hge : 1 ≤ topologicalKrullDim V.left := hdimX ▸
    topologicalKrullDim_le_of_surjective_of_isClosedMap V.hom (surjective_of_finiteEtale Y)
      V.hom.isClosedMap
  have : IsIntegral ((𝟭 Scheme).obj V.left) := ‹IsIntegral V.left›
  exact (isCurve_iff k _).2 ⟨IsVariety.mk, le_antisymm hle hge⟩

end Curve

/-- `#H²(X, ℤ/ℓ) = ℓ` for a smooth proper curve over an algebraically closed field. -/
private theorem natCard_ext_two_unitSheaf {k : Type u} [Field k] [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f] (hℓ : IsUnit (ℓ : k)) :
    Nat.card (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2) = ℓ :=
  Stacks.Kummer.natCard_ext_two_constantModuleSheaf_of_smoothProperCurve f hℓ
    (Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero f _ hℓ)

/-- A type with `ℓ` elements, `ℓ` prime, is finite. -/
private theorem finite_of_natCard_eq_prime {α : Type*} (h : Nat.card α = ℓ) : Finite α :=
  Nat.finite_of_card_ne_zero (by rw [h]; exact (Fact.out : ℓ.Prime).ne_zero)

/-- **Nondegeneracy of the cup product on `H¹` of a curve with `ℤ/ℓ` coefficients.** Let `X` be a
smooth proper curve over an algebraically closed field `k` and `ℓ` a prime invertible in `k`.
For every nonzero `a ∈ H¹(X, ℤ/ℓ) = Ext¹(ℤ/ℓ_X, ℤ/ℓ_X)` there is `x ∈ H¹(X, ℤ/ℓ)` with
`x ∪ a = x ∘ a ≠ 0` in `H²(X, ℤ/ℓ)`. -/
theorem exists_comp_ne_zero_of_ne_zero {k : Type u} [Field k] [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f] (hℓ : IsUnit (ℓ : k))
    (a : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 1) (ha : a ≠ 0) :
    ∃ x : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 1, x.comp a (by norm_num : 1 + 1 = 2) ≠ 0 := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have : ConnectedSpace X := inferInstanceAs (ConnectedSpace X)
  obtain ⟨E, i, ε, w, hS, rfl⟩ := (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ _ _).1 a
  have := isFiniteLocallyConstant_torsor hS
  obtain ⟨V, hV, ⟨e⟩⟩ := exists_isFinite_iso_uliftYoneda_of_isFiniteLocallyConstant (torsor i ε w)
  have := hV
  have : Etale V.hom := V.prop
  have := connectedSpace_of_extClass_ne_zero hS ha e
  have := isCurve_comp_of_isFinite f (V := V)
  have hX2 := natCard_ext_two_unitSheaf f hℓ
  have hP2 : Nat.card (Ext (unitSheaf (X := X) ℓ) (freeTorsor (i := i) (ε := ε) (w := w)) 2) = ℓ :=
    (Nat.card_congr (extFreeTorsorEquiv e 2)).trans (natCard_ext_two_unitSheaf (V.hom ≫ f) hℓ)
  have := finite_of_natCard_eq_prime hP2
  have h3 : Subsingleton (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 3) :=
    Stacks.Kummer.subsingleton_ext_constantModuleSheaf_of_smoothCurve f hℓ 3 le_rfl
  have h3' : Subsingleton (Ext (unitSheaf (X := X) ℓ) (cokernel (shift hS).asHom) 3) :=
    (Equiv.ofBijective _ (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
      (cokernelShiftIso hS).hom (X := unitSheaf ℓ) 3)).subsingleton
  obtain ⟨hfin2, hle2⟩ := Stacks.Abelian.natCard_ext_two_cokernel_pow_le (shift hS)
    (unitSheaf ℓ) (shift_pow_self hS)
    (fun j _ hj => cokernelPowShortComplex_shift_shortExact hS hj) h3' 2 (by norm_num) hp.two_le
  let eE : Ext (unitSheaf (X := X) ℓ) (cokernel (shift hS ^ 2).asHom) 2 ≃
      Ext (unitSheaf (X := X) ℓ) E 2 :=
    Equiv.ofBijective _ (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
      (cokernelShiftSqIso hS).hom (X := unitSheaf ℓ) 2)
  have : Finite (Ext (unitSheaf (X := X) ℓ) E 2) := Finite.of_equiv _ eE
  have hcard : Nat.card (Ext (unitSheaf (X := X) ℓ) E 2) ≤
      Nat.card (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2) := by
    rw [← Nat.card_congr eE, hX2]
    exact hle2.trans hP2.le
  have hsurj := CategoryTheory.Abelian.Ext.surjective_comp_extClass_of_natCard_le hS
    (unitSheaf ℓ) 1 h3 hcard
  have := finite_of_natCard_eq_prime hX2
  have : Nontrivial (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hX2]
    exact hp.one_lt
  obtain ⟨y, hy⟩ := exists_ne (0 : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2)
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, fun h => hy (hx.symm.trans h)⟩

/-- **A left-nondegenerate pairing into a group of order `ℓ` is perfect**: for finite
`ℤ/ℓ`-vector spaces `V`, `W` with `#W = ℓ`, an injective additive map `V → Hom(V, W)` is bijective,
the two sides having `ℓ^{dim V}` elements. -/
theorem bijective_of_injective_addMonoidHom_of_natCard_eq {ℓ : ℕ} [Fact ℓ.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod ℓ) V] [Finite V] [AddCommGroup W] [Module (ZMod ℓ) W]
    (hW : Nat.card W = ℓ) (φ : V → (V →+ W)) (hφ : Function.Injective φ) :
    Function.Bijective φ := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have := finite_of_natCard_eq_prime hW
  have : Module.Finite (ZMod ℓ) V := Module.Finite.of_finite
  have : Module.Finite (ZMod ℓ) W := Module.Finite.of_finite
  have hW1 : Module.finrank (ZMod ℓ) W = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := W)
    rw [hW, Nat.card_zmod] at h
    exact (Nat.pow_eq_self_iff hp.one_lt).1 h.symm
  have hcard : Nat.card (V →+ W) = Nat.card V := by
    rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv ℓ).toEquiv,
      Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := V →ₗ[ZMod ℓ] W),
      Module.finrank_linearMap, hW1, mul_one, ← Module.natCard_eq_pow_finrank]
  have : Finite (V →+ W) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact Nat.card_pos.ne')
  exact hφ.bijective_of_nat_card_le hcard.le

/-- **Perfectness of the cup product on `H¹` of a curve with `ℤ/ℓ` coefficients**:
`a ↦ (x ↦ x ∘ a)` is a bijection `H¹(X, ℤ/ℓ) ≅ Hom(H¹(X, ℤ/ℓ), H²(X, ℤ/ℓ))`, `H²(X, ℤ/ℓ)`
having `ℓ` elements, given that `H¹(X, ℤ/ℓ)` is finite. -/
theorem bijective_bilinearComp_flip {k : Type u} [Field k] [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f] (hℓ : IsUnit (ℓ : k))
    [Finite (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 1)] :
    Function.Bijective (fun a : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 1 =>
      (Ext.bilinearComp (unitSheaf (X := X) ℓ) (unitSheaf ℓ) (unitSheaf ℓ) 1 1 2 rfl).flip a) := by
  refine bijective_of_injective_addMonoidHom_of_natCard_eq (ℓ := ℓ) (natCard_ext_two_unitSheaf f hℓ)
    _ ?_
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨x, hx⟩ := exists_comp_ne_zero_of_ne_zero f hℓ a hne
  exact hx (DFunLike.congr_fun ha x)

end Stacks.EtaleCohomology.ExtensionTorsor

end
