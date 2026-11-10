module

public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.TensorProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ring maps defining open immersions of affine schemes

A ring homomorphism defines an open immersion on affine spectra if, around every prime of its
target, some principal localization induced by an element of its source is an isomorphism. This
property is stable under base change and under composition.

## Main definitions

* `RingHom.IsOpenImmersion` is the principal-localization criterion for the induced morphism of
  affine spectra to be an open immersion.

## Main results

* `RingHom.isOpenImmersion_isStableUnderBaseChange` states stability under base change.
* `RingHom.isOpenImmersion_stableUnderComposition` states stability under composition.

## Implementation notes

The induced map `R_f → A_f` is expressed by saying that `A_f`, equipped with the algebra
structure induced by the original ring map, is a localization of `R` away from `f`. This
retains the particular element `f` required by the source, rather than only asserting that
`A_f` is isomorphic to some principal localization of `R`.

This is a pointwise condition, and so is weaker than Mathlib's
`RingHom.IsStandardOpenImmersion`, which asks for a single element `r` of the source with the
whole map a localization away from `r`. The two are kept apart deliberately.

## References

* [Stacks Project, Tag 01SY](https://stacks.math.columbia.edu/tag/01SY)
* [Stacks Project, Tag 01SZ](https://stacks.math.columbia.edu/tag/01SZ)
-/

@[expose] public section

open scoped TensorProduct

namespace RingHom

universe u

/-- A ring map defining an open immersion on affine spectra, expressed by
principal localizations around primes of the target. -/
def IsOpenImmersion {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) : Prop :=
  ∀ (q : Ideal A) [q.IsPrime],
    ∃ f : R, φ f ∉ q ∧
      (let : Algebra R (Localization.Away (φ f)) :=
        ((algebraMap A (Localization.Away (φ f))).comp φ).toAlgebra
       IsLocalization.Away f (Localization.Away (φ f)))

/-- A ring isomorphism induces a ring isomorphism of principal localizations compatible with it. -/
private theorem exists_ringEquiv_away_of_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] (e : R ≃+* S) (x : R) (Rx Sx : Type*) [CommRing Rx] [CommRing Sx]
    [Algebra R Rx] [Algebra S Sx] [IsLocalization.Away x Rx]
    [IsLocalization.Away ((e : R →+* S) x) Sx] :
    ∃ E : Rx ≃+* Sx, ∀ a, E (algebraMap R Rx a) = algebraMap S Sx (e a) := by
  refine ⟨RingEquiv.ofBijective (IsLocalization.Away.map Rx Sx (e : R →+* S) x) ⟨?_, ?_⟩,
    fun a => by simp [IsLocalization.Away.map]⟩
  · rw [IsLocalization.Away.map_injective_iff]
    intro a ha
    have ha0 : a = 0 := e.injective (by simpa using ha)
    exact ⟨0, by simp [ha0]⟩
  · rw [IsLocalization.Away.map_surjective_iff]
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    exact ⟨a, 0, by simp⟩

/-- Postcomposing with a ring isomorphism preserves the affine open-immersion criterion. -/
private theorem isOpenImmersion_of_postcomp_equiv
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (e : S ≃+* T) (hf : f.IsOpenImmersion) :
    ((e : S →+* T).comp f).IsOpenImmersion := by
  intro qT hqT
  let qS : Ideal S := qT.comap (e : S →+* T)
  have : qS.IsPrime := Ideal.IsPrime.comap _
  obtain ⟨r, hr, hloc⟩ := hf qS
  let rLoc := Localization.Away (f r)
  let tLoc := Localization.Away (e (f r))
  have : IsLocalization.Away (f r) rLoc := inferInstance
  have : IsLocalization.Away ((e : S →+* T) (f r)) tLoc := by
    simpa [tLoc] using (inferInstance : IsLocalization.Away (e (f r)) tLoc)
  let : Algebra R rLoc := ((algebraMap S rLoc).comp f).toAlgebra
  let : Algebra R tLoc := ((algebraMap T tLoc).comp ((e : S →+* T).comp f)).toAlgebra
  obtain ⟨E₀, hE₀⟩ := exists_ringEquiv_away_of_ringEquiv e (f r) rLoc tLoc
  let E : rLoc ≃ₐ[R] tLoc := { E₀ with
    commutes' := fun a => by simpa [RingHom.algebraMap_toAlgebra] using hE₀ (f a) }
  have : IsLocalization.Away r rLoc := hloc
  have hloc' : IsLocalization.Away r tLoc :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) E
  exact ⟨r, by simpa [qS] using hr, hloc'⟩

/-- Precomposing with a ring isomorphism preserves the affine open-immersion criterion. -/
private theorem isOpenImmersion_of_precomp_equiv
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : S →+* T) (e : R ≃+* S) (hf : f.IsOpenImmersion) :
    (f.comp (e : R →+* S)).IsOpenImmersion := by
  intro q hq
  obtain ⟨s, hs, hloc⟩ := hf q
  let x : R := e.symm s
  let RX := Localization.Away x
  let SX := Localization.Away s
  let Cold := Localization.Away (f s)
  let C := Localization.Away ((f.comp (e : R →+* S)) x)
  let : Algebra S Cold := ((algebraMap T Cold).comp f).toAlgebra
  have : IsLocalization.Away s Cold := hloc
  have : IsLocalization.Away (f s) C := by
    change IsLocalization.Away (f s) (Localization.Away (f (e x)))
    exact IsLocalization.Away.of_associated (Associated.of_eq (by simp [x] : f (e x) = f s))
  let E₃ : Cold ≃ₐ[T] C :=
    IsLocalization.algEquiv (Submonoid.powers (f s)) Cold C
  let : Algebra S C := ((algebraMap T C).comp f).toAlgebra
  let : Algebra R C := ((algebraMap T C).comp (f.comp (e : R →+* S))).toAlgebra
  let : Algebra R SX := ((algebraMap S SX).comp (e : R →+* S)).toAlgebra
  have : IsLocalization.Away ((e : R →+* S) x) SX := by
    simpa [x] using (inferInstance : IsLocalization.Away s SX)
  obtain ⟨E₁₀, hE₁₀⟩ := exists_ringEquiv_away_of_ringEquiv e x RX SX
  let E₁ : RX ≃ₐ[R] SX := { E₁₀ with
    commutes' := fun a => by simpa [RingHom.algebraMap_toAlgebra] using hE₁₀ a }
  let E₂ : SX ≃ₐ[S] Cold := IsLocalization.algEquiv (Submonoid.powers s) SX Cold
  let E₂' : SX ≃ₐ[S] C := {
    toRingEquiv := E₂.toRingEquiv.trans E₃.toRingEquiv
    commutes' := by
      intro a
      calc
        _ = E₃ (E₂ (algebraMap S SX a)) := rfl
        _ = E₃ (algebraMap S Cold a) := by rw [E₂.commutes]
        _ = algebraMap T C (f a) := E₃.commutes _
        _ = algebraMap S C a := by
          simp [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  }
  let eR : RX ≃+* C := E₁.toRingEquiv.trans E₂'.toRingEquiv
  let E : RX ≃ₐ[R] C := {
    toRingEquiv := eR
    commutes' := by
      intro a
      calc
        eR (algebraMap R RX a) = E₂' (algebraMap S SX ((e : R →+* S) a)) := by
          simp [eR, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
        _ = algebraMap S C ((e : R →+* S) a) := E₂'.commutes _
        _ = algebraMap R C a := by
          simp [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  }
  exact ⟨x, by simpa [x] using hs,
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers x) E⟩

/-- The affine open-immersion criterion is invariant under pre- and post-composition with
ring isomorphisms. -/
private theorem isOpenImmersion_respectsIso :
    RingHom.RespectsIso (fun {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) =>
      φ.IsOpenImmersion) :=
  ⟨fun f e hf => isOpenImmersion_of_postcomp_equiv f e hf,
   fun f e hf => isOpenImmersion_of_precomp_equiv f e hf⟩

/-- The tensor-product form of base-change stability for the affine open-immersion
criterion. -/
private theorem isOpenImmersion_tensorProduct
    {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
    [Algebra R R'] [Algebra R A] (hφ : (algebraMap R A).IsOpenImmersion) :
    (algebraMap R' (R' ⊗[R] A)).IsOpenImmersion := by
  let B := TensorProduct R R' A
  let ψ : R' →+* B := algebraMap R' B
  change ∀ (q' : Ideal B) [q'.IsPrime], ∃ f : R', ψ f ∉ q' ∧ _
  intro q' hq'
  let q : Ideal A := q'.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] B).toRingHom
  have : q.IsPrime := Ideal.IsPrime.comap _
  obtain ⟨f, hf, hloc⟩ := hφ q
  let f' : R' := algebraMap R R' f
  let Af := Localization.Away (algebraMap R A f)
  let C := Localization.Away (ψ f')
  have hmap : ψ f' = Algebra.TensorProduct.includeRight (R := R) (A := R') (B := A)
      (algebraMap R A f) := by
    simp [ψ, f', B]
  have hnot : ψ f' ∉ q' := by
    rw [hmap]
    simpa [q] using hf
  refine ⟨f', hnot, ?_⟩
  have : IsScalarTower R A Af := inferInstance
  let : Algebra R Af := inferInstance
  have hAlgAf : (inferInstance : Algebra R Af) =
      ((algebraMap A Af).comp (algebraMap R A)).toAlgebra :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hlocAf : @IsLocalization.Away R inferInstance f Af inferInstance
      (inferInstance : Algebra R Af) := by
    rwa [hAlgAf]
  have : IsLocalization.Away f Af := hlocAf
  let : Algebra R' (TensorProduct R R' Af) :=
    Algebra.TensorProduct.leftAlgebra (R := R) (A := R') (B := Af) (S := R')
  have : IsLocalization.Away f' (TensorProduct R R' Af) := by
    simpa [f'] using (inferInstance :
      IsLocalization.Away (algebraMap R R' f) (TensorProduct R R' Af))
  have : IsScalarTower R' B C := inferInstance
  let : Algebra R' C := inferInstance
  have hM : Submonoid.map (Algebra.TensorProduct.includeRight
      (R := R) (A := R') (B := A)) (Submonoid.powers (algebraMap R A f)) =
      Submonoid.powers (ψ f') := by
    rw [Submonoid.map_powers, hmap]
  have : IsLocalization (Submonoid.map (Algebra.TensorProduct.includeRight
      (R := R) (A := R') (B := A)) (Submonoid.powers (algebraMap R A f))) C :=
    hM.symm ▸ (inferInstance : IsLocalization (Submonoid.powers (ψ f')) C)
  let e : (TensorProduct R R' Af) ≃ₐ[R'] C :=
    IsLocalization.tensorProductEquivOfMapIncludeRight R R'
      (Submonoid.powers (algebraMap R A f)) Af (Localization.Away (ψ f'))
  have hlocC : @IsLocalization.Away R' inferInstance f' C inferInstance
      (inferInstance : Algebra R' C) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers f') e
  have hAlgC : (inferInstance : Algebra R' C) = ((algebraMap B C).comp ψ).toAlgebra :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hlocC' : @IsLocalization.Away R' inferInstance f' C inferInstance
      (((algebraMap B C).comp ψ).toAlgebra) := by
    rwa [← hAlgC]
  exact hlocC'

/-- The principal-localization criterion for an affine open immersion is
stable under arbitrary base change of commutative rings. -/
@[stacks 01SY "open_immersion_base_change",
  ega "I 4.3.2" "affine open immersions",
  ega "I 4.5.5" "(iii), special case", sga "1 VIII 5.5" "special case"]
theorem isOpenImmersion_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) =>
        φ.IsOpenImmersion) :=
  .mk isOpenImmersion_respectsIso fun _ _ _ _ _ _ _ _ hφ => isOpenImmersion_tensorProduct hφ

/-- The element of the source witnessing the criterion for a composite, together with the
two witnesses it is built from. -/
private lemma exists_notMem_comp_of_isOpenImmersion
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (q : Ideal T) [q.IsPrime]
    {p : Ideal S} (hp : p.IsPrime) (hpq : p = Ideal.comap g q)
    (r : R) (hr : f r ∉ p) (s : S) (hs : s ∉ p)
    (S₁ : Type u) [CommRing S₁] [Algebra S S₁] [IsLocalization.Away (f r) S₁]
    (a : R) (n : ℕ)
    (hsec : algebraMap S S₁ s * (algebraMap S S₁ (f r)) ^ n = algebraMap S S₁ (f a)) :
    (g.comp f) (r * a) ∉ q := by
  have hDisj : Disjoint (Submonoid.powers (f r) : Set S) p := by
    rw [Set.disjoint_left]
    intro x hx hxp
    rcases hx with ⟨k, rfl⟩
    exact hr (hp.mem_of_pow_mem k hxp)
  have hUnder : (Ideal.map (algebraMap S S₁) p).under S = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (f r)) S₁ hp hDisj
  have ha : f a ∉ p := by
    intro ha
    let I : Ideal S₁ := Ideal.map (algebraMap S S₁) p
    have hfaI : algebraMap S S₁ (f a) ∈ I := Ideal.mem_map_of_mem _ ha
    have hsI : algebraMap S S₁ s ∈ I :=
      (I.mul_unit_mem_iff_mem ((IsLocalization.Away.algebraMap_isUnit (f r)).pow n)).mp
        (hsec.symm ▸ hfaI)
    exact hs (by simpa [hUnder] using (Ideal.mem_under S (Ideal.map (algebraMap S S₁) p)).2 hsI)
  intro hhq
  have hhp : f (r * a) ∈ p := by rwa [hpq]
  exact (hp.mem_or_mem (by simpa [map_mul] using hhp)).elim hr ha

/-- Being an isomorphism on some principal neighborhood of each target prime
is stable under composition of commutative-ring homomorphisms. -/
@[stacks 01SZ "open_immersion_composition"]
theorem isOpenImmersion_stableUnderComposition :
    RingHom.StableUnderComposition
      (fun {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) ↦
        φ.IsOpenImmersion) := by
  intro R S T _ _ _ f g hf hg
  let : Algebra R S := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R T := (g.comp f).toAlgebra
  have : IsScalarTower R S T :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := S) (A := T) (by
      simp [RingHom.algebraMap_toAlgebra])
  intro q hq
  let p : Ideal S := Ideal.comap g q
  have hp : p.IsPrime := Ideal.comap_isPrime g q
  obtain ⟨r, hr, hrLoc⟩ := hf p
  obtain ⟨s, hs, hsLoc⟩ := hg q
  let S₁ := Localization.Away (f r)
  let algRS₁ : Algebra R S₁ := ((algebraMap S S₁).comp f).toAlgebra
  let : SMul R S₁ := algRS₁.toSMul
  let : SMul S S₁ := (inferInstance : Algebra S S₁).toSMul
  have halgRS₁ : algebraMap R S₁ = (algebraMap S S₁).comp f := rfl
  have : IsScalarTower R S S₁ :=
    @IsScalarTower.of_algebraMap_eq' R S S₁ inferInstance inferInstance inferInstance
      (by assumption) inferInstance algRS₁ halgRS₁
  have : IsLocalization.Away r S₁ := hrLoc
  let S₂ := Localization.Away (g s)
  let : Algebra S S₂ := ((algebraMap T S₂).comp g).toAlgebra
  have : IsLocalization.Away s S₂ := hsLoc
  let aN := IsLocalization.Away.sec r (algebraMap S S₁ s)
  let a : R := aN.1
  let n : ℕ := aN.2
  have hsec :
      algebraMap S S₁ s * algebraMap R S₁ r ^ n = algebraMap R S₁ a := by
    simpa [aN, n, IsScalarTower.algebraMap_apply] using
      IsLocalization.Away.sec_spec r (algebraMap S S₁ s)
  let T₂ := Localization.Away (algebraMap T S₂ (g (f r)))
  have hfrT₂ : IsLocalization.Away (algebraMap S S₂ (f r)) T₂ := by
    change IsLocalization.Away (algebraMap T S₂ (g (f r))) T₂
    infer_instance
  let : Algebra S₁ T₂ :=
    (IsLocalization.Away.map S₁ T₂ (algebraMap S S₂) (f r)).toAlgebra
  let : Algebra S T₂ := Algebra.compHom T₂ ((algebraMap T S₂).comp g)
  let : Algebra T T₂ := Algebra.compHom T₂ (algebraMap T S₂)
  let : Algebra R T₂ :=
    Algebra.compHom T₂ ((algebraMap S₁ T₂).comp (algebraMap R S₁))
  let : SMul S S₂ := (inferInstance : Algebra S S₂).toSMul
  let : SMul S₂ T₂ := (inferInstance : Algebra S₂ T₂).toSMul
  let : SMul S T₂ := (inferInstance : Algebra S T₂).toSMul
  let : SMul S₁ T₂ := (inferInstance : Algebra S₁ T₂).toSMul
  let : SMul R T₂ := (inferInstance : Algebra R T₂).toSMul
  let : SMul T S₂ := (inferInstance : Algebra T S₂).toSMul
  let : SMul T T₂ := (inferInstance : Algebra T T₂).toSMul
  have hmapS : (algebraMap S₁ T₂).comp (algebraMap S S₁) = algebraMap S T₂ := by
    ext x
    change IsLocalization.Away.map S₁ T₂ (algebraMap S S₂) (f r)
        (algebraMap S S₁ x) =
      algebraMap S₂ T₂ ((algebraMap T S₂) (g x))
    simp only [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have : IsScalarTower S S₁ T₂ :=
    IsScalarTower.of_algebraMap_eq' hmapS.symm
  have : IsScalarTower R S₁ T₂ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower S S₂ T₂ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower T S₂ T₂ := IsScalarTower.of_algebraMap_eq' rfl
  have hcomm : IsLocalization.Away (algebraMap S S₁ s) T₂ :=
    IsLocalization.Away.commutes S₁ S₂ T₂ (f r) s
  have hAssoc : Associated (algebraMap S S₁ s) (algebraMap R S₁ a) := by
    simpa [a, aN, IsScalarTower.algebraMap_apply] using
      (IsLocalization.Away.associated_sec_fst r (algebraMap S S₁ s)).symm
  have hA₂ : IsLocalization.Away (algebraMap R S₁ a) T₂ :=
    hcomm.of_associated hAssoc
  let h : R := r * a
  have hR₂ : IsLocalization.Away h T₂ := by
    simpa [h, IsScalarTower.algebraMap_apply] using
      (IsLocalization.Away.mul' S₁ T₂ r a)
  have hmapr (x : R) : algebraMap R S₁ x = algebraMap S S₁ (f x) := by
    simp [RingHom.algebraMap_toAlgebra]
  have hh : (g.comp f) h ∉ q := by
    refine exists_notMem_comp_of_isOpenImmersion f g q hp rfl r hr s hs S₁ a n ?_
    rwa [hmapr r, hmapr a] at hsec
  let V := Localization.Away ((g.comp f) h)
  let : Algebra R V := ((algebraMap T V).comp (g.comp f)).toAlgebra
  have hProdUnit : IsUnit (algebraMap T V ((g.comp f) h)) :=
    IsLocalization.Away.algebraMap_isUnit ((g.comp f) h)
  have hPairV : IsUnit (algebraMap T V (g (f r)) * algebraMap T V (g (f a))) := by
    simpa [h, RingHom.comp_apply, map_mul] using hProdUnit
  rcases (IsUnit.mul_iff.mp hPairV) with ⟨hfrV, hfaV⟩
  let vS₁ : S₁ →+* V :=
    IsLocalization.Away.lift (f r) hfrV
      (g := (algebraMap T V).comp g)
  have hsecV := congrArg vS₁ hsec
  have hsV : IsUnit (algebraMap T V (g s)) := by
    have heq : algebraMap T V (g s) * algebraMap T V (g (f r)) ^ n =
        algebraMap T V (g (f a)) := by
      rw [hmapr r, hmapr a] at hsecV
      simpa [vS₁, IsLocalization.Away.lift_eq] using hsecV
    exact isUnit_of_mul_isUnit_left (heq.symm ▸ hfaV)
  let vS₂ : S₂ →+* V := IsLocalization.Away.lift (g s) hsV (g := algebraMap T V)
  have hvfrS₂ : IsUnit (vS₂ (algebraMap T S₂ (g (f r)))) := by
    simpa [vS₂, IsLocalization.Away.lift_eq] using hfrV
  let vT₂ : T₂ →+* V :=
    IsLocalization.Away.lift (algebraMap T S₂ (g (f r))) hvfrS₂ (g := vS₂)
  have hH₂ : IsUnit (algebraMap R T₂ h) := IsLocalization.Away.algebraMap_isUnit h
  have hmapRT : algebraMap R T₂ = (algebraMap T T₂).comp (g.comp f) := by
    ext x
    calc
      algebraMap R T₂ x = algebraMap S₁ T₂ (algebraMap R S₁ x) := rfl
      _ = algebraMap S₁ T₂ (algebraMap S S₁ (f x)) := by
        rw [halgRS₁]
        simp only [RingHom.comp_apply]
      _ = algebraMap S T₂ (f x) :=
        congrArg (fun F : S →+* T₂ => F (f x)) hmapS
      _ = algebraMap T T₂ (g (f x)) := rfl
  have hH₂T : IsUnit (algebraMap T T₂ ((g.comp f) h)) :=
    ((RingHom.ext_iff.mp hmapRT) h) ▸ hH₂
  let v₂V : V →+* T₂ :=
    IsLocalization.Away.lift ((g.comp f) h) hH₂T (g := algebraMap T T₂)
  have hVfromS₂ : vS₂.comp (algebraMap T S₂) = algebraMap T V := by
    ext x
    simp [vS₂]
  have hT₂fromS₂ : vT₂.comp (algebraMap S₂ T₂) = vS₂ := by
    ext x
    simp [vT₂]
  have hT₂fromT : vT₂.comp (algebraMap T T₂) = algebraMap T V := by
    rw [IsScalarTower.algebraMap_eq T S₂ T₂, ← RingHom.comp_assoc, hT₂fromS₂, hVfromS₂]
  have hv₂S₂ : v₂V.comp vS₂ = algebraMap S₂ T₂ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (g s))
    ext x
    have hx := congrArg (fun F : T →+* V => F x) hVfromS₂
    calc
      v₂V (vS₂ (algebraMap T S₂ x)) = v₂V (algebraMap T V x) := congrArg v₂V
        (by simpa [RingHom.comp_apply] using hx)
      _ = algebraMap T T₂ x := by simp [v₂V]
      _ = algebraMap S₂ T₂ (algebraMap T S₂ x) := by
        rw [IsScalarTower.algebraMap_apply T S₂ T₂]
  have hleft : v₂V.comp vT₂ = RingHom.id T₂ := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (algebraMap T S₂ (g (f r))))
    ext x
    have hx := congrArg (fun F : S₂ →+* T₂ => F x) hv₂S₂
    calc
      v₂V (vT₂ (algebraMap S₂ T₂ x)) = v₂V (vS₂ x) := by
        simpa [RingHom.comp_apply] using
          congrArg v₂V (congrArg (fun F : S₂ →+* V => F x) hT₂fromS₂)
      _ = algebraMap S₂ T₂ x := by simpa [RingHom.comp_apply] using hx
  have hright : vT₂.comp v₂V = RingHom.id V := by
    apply IsLocalization.ringHom_ext (Submonoid.powers ((g.comp f) h))
    ext x
    calc
      vT₂ (v₂V (algebraMap T V x)) = vT₂ (algebraMap T T₂ x) := by simp [v₂V]
      _ = algebraMap T V x :=
        congrArg (fun F : T →+* V => F x) hT₂fromT
  have hv₂V : Function.Bijective vT₂ :=
    Function.bijective_iff_has_inverse.mpr
      ⟨v₂V, fun x => RingHom.congr_fun hleft x, fun y => RingHom.congr_fun hright y⟩
  let vT₂Alg : T₂ →ₐ[R] V :=
    { toRingHom := vT₂
      commutes' := by
        intro x
        calc
          vT₂ (algebraMap R T₂ x) =
              vT₂ (algebraMap T T₂ ((g.comp f) x)) :=
            congrArg vT₂ ((RingHom.ext_iff.mp hmapRT) x)
          _ = algebraMap T V ((g.comp f) x) :=
            (RingHom.ext_iff.mp hT₂fromT) ((g.comp f) x)
          _ = algebraMap R V x := rfl }
  exact ⟨h, hh, IsLocalization.isLocalization_of_algEquiv (Submonoid.powers h)
    (AlgEquiv.ofBijective vT₂Alg hv₂V)⟩

end RingHom
