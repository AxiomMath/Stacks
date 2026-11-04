module

public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.Depth.AlgebraMap
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
public import StacksFrontier.RingTheory.LocalRing.ResidueField.FiberBaseChange

@[expose] public section

/-!
# The Cohen–Macaulay locus in the fibres commutes with base change

For `R → S` of finite type, `R → R'` arbitrary and `S' = R' ⊗_R S`, the set `W'` of primes of `S'`
whose fibre ring over `R'` is Cohen–Macaulay is the preimage of the corresponding set `W` for `S`
over `R` under `f : Spec S' → Spec S`. The file also shows that for a field `k`, a finite type
`k`-algebra `S` and a field extension `K/k`, the local ring of `S` at a prime `𝔮` is
Cohen–Macaulay if and only if the local ring of `K ⊗_k S` at a prime lying over `𝔮` is.

## Main results

* `Algebra.IsPushout.isMaximalCohenMacaulay_iff`: for a field extension `K/k` and a finite type
  `k`-algebra `S`, the local ring `S_𝔮` is Cohen–Macaulay if and only if the local ring of
  `K ⊗_k S` at a prime lying over `𝔮` is.
* `Algebra.IsPushout.setOf_isMaximalCohenMacaulay_fiber_eq_preimage_comap`: the set of primes of
  `S'` at which the fibre ring over `R'` is Cohen–Macaulay is the preimage of the corresponding set
  for `S` over `R`.

## References

* [StacksProject 00RK](https://stacks.math.columbia.edu/tag/00RK), Lemma 10.130.8
* [StacksProject 00RJ](https://stacks.math.columbia.edu/tag/00RJ), Lemma 10.130.7
* [StacksProject 045J](https://stacks.math.columbia.edu/tag/045J)
* [StacksProject 045M](https://stacks.math.columbia.edu/tag/045M)
* [StacksProject 045N](https://stacks.math.columbia.edu/tag/045N)
-/

@[expose] public section

/-! ### Cohen–Macaulayness under base change to a field extension -/

namespace Stacks.CohenMacaulay.FiniteTypeBaseChange

open IsLocalRing RingTheory.Sequence

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-- A Cohen–Macaulay ring is Cohen–Macaulay at each of its primes. -/
public lemma isMaximalCohenMacaulay_localization_atPrime {B : Type*} [CommRing B]
    (h : Module.IsCohenMacaulay B B) (P : Ideal B) [P.IsPrime] :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  have hmem : (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum B) ∈ Module.support B B :=
    Module.mem_support_iff.mpr (inferInstanceAs (Nontrivial (Localization.AtPrime P)))
  have := h _ hmem
  rwa [Module.supportDim_self_eq_ringKrullDim] at this

/-- A localization at a prime of a Cohen–Macaulay ring is Cohen–Macaulay, read through a ring
isomorphism. -/
public lemma isMaximalCohenMacaulay_localization_of_ringEquiv {B C : Type*} [CommRing B]
    [CommRing C] (e : B ≃+* C) (h : Module.IsCohenMacaulay C C) (P : Ideal B) [P.IsPrime] :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  have hP : P = (P.comap (e.symm : C →+* B)).comap (e : B →+* C) := by
    rw [Ideal.comap_comap]; simp
  exact (BaseFieldExtension.isMaximalCohenMacaulay_self_congr
    (Localization.localRingEquiv P (P.comap (e.symm : C →+* B)) e hP)).mpr
      (isMaximalCohenMacaulay_localization_atPrime h _)

/-- **Cohen–Macaulayness across a base field extension, for the concrete tensor product.** Let `k`
be a field, `S` a `k`-algebra with `K ⊗[k] S` Noetherian, `K/k` a field extension, `𝔮 ⊆ S` a prime
and `𝔮_K ⊆ K ⊗[k] S` a prime lying over it, and assume that one of the field extensions `κ(𝔮)/k`,
`K/k` is essentially of finite type. Then `S_𝔮` is Cohen–Macaulay if and only if
`(K ⊗[k] S)_{𝔮_K}` is. -/
@[ega "IV 6.7.1" "Clause (i), special case",
  ega "IV 6.7.1.1" "more general",
  sga "3 VIA 1.1.1" "special case"]
private theorem isMaximalCohenMacaulay_localizationAtPrime_iff (k S K : Type*) [Field k]
    [CommRing S] [Algebra k S] [Field K] [Algebra k K] [IsNoetherianRing (K ⊗[k] S)]
    (q : Ideal S) [q.IsPrime] (qK : Ideal (K ⊗[k] S)) [qK.IsPrime]
    (hqK : q = qK.comap Algebra.TensorProduct.includeRight.toRingHom)
    (hfg : Algebra.EssFiniteType k q.ResidueField ∨ Algebra.EssFiniteType k K) :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime q) (Localization.AtPrime q) ↔
      Module.IsMaximalCohenMacaulay (Localization.AtPrime qK) (Localization.AtPrime qK) := by
  have : Module.Flat S (K ⊗[k] S) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight k S K).symm.toLinearEquiv
  have : qK.LiesOver q := ⟨hqK⟩
  have : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK)) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  rw [Module.isMaximalCohenMacaulay_self_iff_of_flat (Localization.AtPrime q)
    (Localization.AtPrime qK)]
  refine (and_iff_left ?_).symm
  set Q : Ideal (q.Fiber (K ⊗[k] S)) :=
    ((PrimeSpectrum.primesOverOrderIsoFiber S (K ⊗[k] S) q)
      ⟨qK, inferInstance, inferInstance⟩).asIdeal with hQdef
  have hQ : Q.comap (Algebra.TensorProduct.includeRight :
      (K ⊗[k] S) →ₐ[S] q.Fiber (K ⊗[k] S)) = qK := by
    rw [hQdef, ← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply, OrderIso.symm_apply_apply]
  set P := Q.comap (Algebra.TensorProduct.includeRight :
    (K ⊗[k] S) →ₐ[S] q.Fiber (K ⊗[k] S)) with hPdef
  have e2 := Localization.localAlgEquiv (R := S) P qK
    (AlgEquiv.refl : (K ⊗[k] S) ≃ₐ[S] (K ⊗[k] S)) (by rw [hQ]; ext x; simp)
  have e1 := Ideal.Fiber.algEquivAux₂ q Q
  have hIeq : (maximalIdeal (Localization.AtPrime q)).map
      (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK)) =
      q.map (algebraMap S (Localization.AtPrime qK)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hmapE : ((q.map (algebraMap S (K ⊗[k] S))).map (algebraMap (K ⊗[k] S)
        (Localization.AtPrime P))).map (e2 : _ →+* Localization.AtPrime qK) =
      q.map (algebraMap S (Localization.AtPrime qK)) := by
    have hcomp : (e2 : _ →+* Localization.AtPrime qK).comp
        (algebraMap S (Localization.AtPrime P)) = algebraMap S (Localization.AtPrime qK) :=
      RingHom.ext e2.commutes
    rw [Ideal.map_map, Ideal.map_map, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq S (K ⊗[k] S) (Localization.AtPrime P), hcomp]
  have E := e1.toRingEquiv.trans
    (Ideal.quotientEquiv _ _ e2.toRingEquiv (hIeq.trans hmapE.symm))
  have hnt : Nontrivial (Localization.AtPrime qK ⧸
      (maximalIdeal (Localization.AtPrime q)).map
        (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK))) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top _).ne
  have hlocF : IsLocalRing (Localization.AtPrime qK ⧸
      (maximalIdeal (Localization.AtPrime q)).map
        (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK))) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime qK)
      (Localization.AtPrime qK ⧸ (maximalIdeal (Localization.AtPrime q)).map
        (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK)))) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  rw [Module.depth_eq_depth_map_algebraMap hsurj,
    IsLocalRing.map_maximalIdeal_of_surjective _ hsurj, ← Module.depth_self_eq_of_ringEquiv E,
    ← ringKrullDim_eq_of_ringEquiv E]
  exact isMaximalCohenMacaulay_localization_of_ringEquiv
    (((Algebra.TensorProduct.congr (AlgEquiv.refl : q.ResidueField ≃ₐ[S] q.ResidueField)
        (Algebra.TensorProduct.commRight k S K).symm).toRingEquiv).trans
      (Algebra.TensorProduct.cancelBaseChange k S q.ResidueField q.ResidueField K).toRingEquiv)
    (Algebra.TensorProduct.isNoetherianRing_and_isCohenMacaulay_of_essFiniteType k
      q.ResidueField K hfg).2 Q

end Stacks.CohenMacaulay.FiniteTypeBaseChange

open scoped TensorProduct

namespace Algebra.IsPushout

/-- Let `k` be a field, let `S` be a finite type `k`-algebra, let `K/k` be a field extension and
let `T = K ⊗_k S` be the base change, presented as a pushout square. Let `𝔮K` be a prime of `T`
lying over the prime `𝔮` of `S`, and let `Sq = S_𝔮` and `TqK = T_{𝔮K}` be the local rings at
them. Then `S_𝔮` is Cohen–Macaulay if and only if `T_{𝔮K}` is Cohen–Macaulay. -/
@[stacks 00RJ "Cohen-Macaulayness of a Noetherian local ring `A` (Definition 00N8) is
`Module.IsMaximalCohenMacaulay A A` (tag 00NF); the base change `K ⊗_k S` is an arbitrary pushout
square of `k`-algebras `Algebra.IsPushout k K S T`, as in the sibling 00P4; the two local rings
are abstract `IsLocalization.AtPrime`s; and `𝔮_K` lying over `𝔮` is `Ideal.LiesOver`. See the
module docstring.", ega "IV 6.7.1" "(i), CM, affine", sga "3 VIA 1.1.1" "special case"]
public theorem isMaximalCohenMacaulay_iff (k K S T : Type*) [Field k] [Field K] [CommRing S]
    [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T] [Algebra S T]
    [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] (𝔮 : Ideal S) [𝔮.IsPrime] (𝔮K : Ideal T) [𝔮K.IsPrime]
    [𝔮K.LiesOver 𝔮] (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq 𝔮]
    [IsLocalRing Sq] (TqK : Type*) [CommRing TqK] [Algebra T TqK]
    [IsLocalization.AtPrime TqK 𝔮K] [IsLocalRing TqK] :
    Module.IsMaximalCohenMacaulay Sq Sq ↔ Module.IsMaximalCohenMacaulay TqK TqK := by
  rw [Stacks.CohenMacaulay.BaseFieldExtension.isMaximalCohenMacaulay_self_congr
      (IsLocalization.algEquiv 𝔮.primeCompl Sq (Localization.AtPrime 𝔮)).toRingEquiv,
    Stacks.CohenMacaulay.BaseFieldExtension.isMaximalCohenMacaulay_self_congr
      (IsLocalization.algEquiv 𝔮K.primeCompl TqK (Localization.AtPrime 𝔮K)).toRingEquiv]
  set e : K ⊗[k] S ≃+* T := (Algebra.IsPushout.equiv k K S T).toRingEquiv with hedef
  have he : (e : K ⊗[k] S →+* T).comp
      (Algebra.TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom = algebraMap S T := by
    refine RingHom.ext fun s ↦ ?_
    rw [hedef]
    simpa using Algebra.IsPushout.equiv_tmul k K S T 1 s
  set qK : Ideal (K ⊗[k] S) := 𝔮K.comap (e : K ⊗[k] S →+* T) with hqKdef
  have : qK.IsPrime := hqKdef ▸ Ideal.comap_isPrime _ _
  rw [← Stacks.CohenMacaulay.BaseFieldExtension.isMaximalCohenMacaulay_self_congr
    (Localization.localRingEquiv qK 𝔮K e rfl)]
  have : IsNoetherianRing (K ⊗[k] S) :=
    Algebra.FiniteType.isNoetherianRing K (K ⊗[k] S)
  refine Stacks.CohenMacaulay.FiniteTypeBaseChange.isMaximalCohenMacaulay_localizationAtPrime_iff
    k S K 𝔮 qK ?_ (Or.inl ?_)
  · rw [hqKdef, Ideal.comap_comap, he]
    exact Ideal.LiesOver.over
  · exact Algebra.EssFiniteType.of_surjective
      (IsScalarTower.toAlgHom k (Localization.AtPrime 𝔮) 𝔮.ResidueField)
      Ideal.Quotient.mk_surjective

end Algebra.IsPushout

namespace Stacks.CohenMacaulay.FiniteTypeBaseChange

/-- Let `k` be a field, `S` a finite type `k`-algebra, `K/k` a field extension and `T` a pushout
of `K` and `S` over `k`. Let `𝔮K` be a prime of `T` lying over the prime `𝔮` of `S`, and let `Sq`
and `TqK` be the local rings at them. Then `Sq` is Cohen–Macaulay if and only if `TqK` is. -/
public alias solution := Algebra.IsPushout.isMaximalCohenMacaulay_iff

end Stacks.CohenMacaulay.FiniteTypeBaseChange

namespace Stacks.CohenMacaulay.LocusBaseChange

open scoped TensorProduct

/-! ### The fibre ring is the local ring of the fibre -/

/-- The fibre ring `S_𝔮/𝔭S_𝔮` at a prime `𝔮` of `S`, with `𝔭 = R ∩ 𝔮`, as the localization of
`S/𝔭S` at the image of `𝔮`. -/
private abbrev fiberRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (𝔮 : Ideal S) [𝔮.IsPrime] : Type _ :=
  Localization.AtPrime (𝔮.map (Ideal.Quotient.mk ((𝔮.under R).map (algebraMap R S))))

/-- The point `q̄` of the fibre `κ(𝔭) ⊗_R S` corresponding to a prime `𝔮` of `S`, where
`𝔭 = R ∩ 𝔮`. -/
private noncomputable abbrev fiberPoint {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (𝔮 : PrimeSpectrum S) :
    PrimeSpectrum ((PrimeSpectrum.comap (algebraMap R S) 𝔮).asIdeal.Fiber S) :=
  PrimeSpectrum.preimageHomeomorphFiber R S (PrimeSpectrum.comap (algebraMap R S) 𝔮) ⟨𝔮, rfl⟩

/-- A prime of the fibre `κ(𝔭) ⊗_R S` is determined by its contraction to `S`. -/
private theorem eq_of_comap_includeRight_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (𝔭 : Ideal R) [𝔭.IsPrime] {q₁ q₂ : Ideal (𝔭.Fiber S)} [q₁.IsPrime] [q₂.IsPrime]
    (h : q₁.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] 𝔭.Fiber S).toRingHom
      = q₂.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] 𝔭.Fiber S).toRingHom) :
    q₁ = q₂ :=
  congrArg PrimeSpectrum.asIdeal
    ((PrimeSpectrum.preimageEquivFiber R S (⟨𝔭, ‹_›⟩ : PrimeSpectrum R)).symm.injective
      (a₁ := ⟨q₁, ‹_›⟩) (a₂ := ⟨q₂, ‹_›⟩) (Subtype.ext (PrimeSpectrum.ext h)))

/-- The point `q̄` of the fibre contracts to `𝔮` along `S → κ(𝔭) ⊗_R S`. -/
private theorem comap_asIdeal_fiberPoint {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (𝔮 : PrimeSpectrum S) :
    Ideal.comap (Algebra.TensorProduct.includeRight :
        S →ₐ[R] (PrimeSpectrum.comap (algebraMap R S) 𝔮).asIdeal.Fiber S).toRingHom
      (fiberPoint (R := R) 𝔮).asIdeal = 𝔮.asIdeal :=
  congrArg (fun q : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {PrimeSpectrum.comap
      (algebraMap R S) 𝔮} ↦ q.1.asIdeal)
    ((PrimeSpectrum.preimageHomeomorphFiber R S
      (PrimeSpectrum.comap (algebraMap R S) 𝔮)).symm_apply_apply ⟨𝔮, rfl⟩)

/-- The quotient of the local ring at a prime by the ideal generated by an ideal of the base
depends only on the prime, not on the proof that it is prime nor on the spelling of the prime. -/
private noncomputable def quotientLocalizationAtPrimeCongr {A : Type*} [CommRing A] {I J : Ideal A}
    [I.IsPrime] [J.IsPrime] (h : I = J) {R : Type*} [CommRing R] [Algebra R A] (𝔭 : Ideal R) :
    (Localization.AtPrime I ⧸ 𝔭.map (algebraMap R (Localization.AtPrime I)))
      ≃ₐ[R] (Localization.AtPrime J ⧸ 𝔭.map (algebraMap R (Localization.AtPrime J))) := by
  subst h; exact AlgEquiv.refl

/-- The quotient of a localization `S_P` by the ideal generated by `𝔭 ⊆ R` is the same whether `𝔭`
is pushed through `R → S_P` directly or through `R → S → S_P`. -/
private noncomputable def quotientMapLocalizationAlgEquiv (R : Type*) {S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (P : Ideal S) [P.IsPrime] (𝔭 : Ideal R) :
    (Localization.AtPrime P ⧸ 𝔭.map (algebraMap R (Localization.AtPrime P)))
      ≃ₐ[R] (Localization.AtPrime P ⧸ (𝔭.map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime P))) :=
  Ideal.quotientEquivAlgOfEq R (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq])

/-- **The two spellings of the fibre ring `S_𝔮/𝔭S_𝔮` agree**: localizing the quotient `S/𝔭S` at
the image `𝔮/𝔭S` of `𝔮` gives the same `R`-algebra as the quotient of the localization `S_𝔮` by
the ideal generated by `𝔭 = R ∩ 𝔮`. -/
private noncomputable def fiberLocalRingAlgEquiv (R : Type*) {S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime] :
    (Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localization.AtPrime q)))
      ≃ₐ[R] fiberRing R q := by
  have : (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))).LiesOver q :=
    ⟨.trans (by simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
      (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm⟩
  have hsub := Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective
    (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))) q Ideal.Quotient.mk_surjective
  refine (quotientMapLocalizationAlgEquiv R q _).trans ?_
  have : IsLocalization (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))).primeCompl
      (Localization.AtPrime q ⧸ ((q.under R).map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime q))) := hsub ▸ inferInstance
  have : IsScalarTower R (S ⧸ (q.under R).map (algebraMap R S))
      (Localization.AtPrime q ⧸ ((q.under R).map (algebraMap R S)).map
        (algebraMap S (Localization.AtPrime q))) := .of_algebraMap_eq' rfl
  exact (IsLocalization.algEquiv
    (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))).primeCompl _
    (fiberRing R q)).restrictScalars R

/-- **The fibre ring is the local ring of the fibre.** For a prime `𝔮` of `S` lying over
`𝔭 = R ∩ 𝔮`, the localization of the fibre `κ(𝔭) ⊗_R S` at the point `q̄` corresponding to `𝔮`
is the fibre ring `S_𝔮/𝔭S_𝔮`, as `R`-algebras. -/
private noncomputable def localizationFiberPointAlgEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (𝔮 : PrimeSpectrum S) :
    Localization.AtPrime (fiberPoint (R := R) 𝔮).asIdeal ≃ₐ[R] fiberRing R 𝔮.asIdeal :=
  (Ideal.Fiber.algEquivAux₂ _ (fiberPoint (R := R) 𝔮).asIdeal).trans
    ((quotientMapLocalizationAlgEquiv R _ _).symm.trans
      ((quotientLocalizationAtPrimeCongr (comap_asIdeal_fiberPoint 𝔮) _).trans
        (fiberLocalRingAlgEquiv R 𝔮.asIdeal)))

/-- The fibre ring at `𝔮` is a localization of the fibre `κ(𝔭) ⊗_R S` at the point `q̄`, for the
`κ(𝔭) ⊗_R S`-algebra structure transported along `localizationFiberPointAlgEquiv`. -/
private theorem exists_isLocalization_fiberRing {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (𝔮 : PrimeSpectrum S) :
    ∃ _ : Algebra ((PrimeSpectrum.comap (algebraMap R S) 𝔮).asIdeal.Fiber S)
        (fiberRing R 𝔮.asIdeal),
      IsLocalization.AtPrime (fiberRing R 𝔮.asIdeal) (fiberPoint (R := R) 𝔮).asIdeal := by
  let : Algebra ((PrimeSpectrum.comap (algebraMap R S) 𝔮).asIdeal.Fiber S)
      (fiberRing R 𝔮.asIdeal) :=
    ((localizationFiberPointAlgEquiv 𝔮).toRingEquiv.toRingHom.comp
      (algebraMap _ (Localization.AtPrime (fiberPoint (R := R) 𝔮).asIdeal))).toAlgebra
  exact ⟨_, IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofRingEquiv (f := (localizationFiberPointAlgEquiv 𝔮).toRingEquiv) fun _ ↦ rfl)⟩

/-! ### Cohen–Macaulayness over the two fibres -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Cohen–Macaulayness of the local rings of the fibres of `S/R` and `S'/R'`.** Let
`S' = R' ⊗_R S` with `R → S` of finite type, let `𝔭' ⊆ R'` lie over `𝔭 ⊆ R`, and let `q` and `q'`
be primes of the two fibres `κ(𝔭) ⊗_R S` and `κ(𝔭') ⊗_{R'} S'` whose contractions to `S` and to
`S'` correspond under `S → S'`. Then a local ring of the first fibre at `q` is Cohen–Macaulay if
and only if a local ring of the second at `q'` is. -/
private theorem isMaximalCohenMacaulay_iff_of_fiber (R R' S S' : Type*) [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S']
    [Algebra S S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']
    [Algebra.FiniteType R S] (𝔭 : Ideal R) [𝔭.IsPrime] (𝔭' : Ideal R') [𝔭'.IsPrime]
    [𝔭'.LiesOver 𝔭] (q : Ideal (𝔭.Fiber S)) [q.IsPrime] (q' : Ideal (𝔭'.Fiber S')) [q'.IsPrime]
    (hqq' : q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] 𝔭.Fiber S).toRingHom
      = (q'.comap (Algebra.TensorProduct.includeRight :
          S' →ₐ[R'] 𝔭'.Fiber S').toRingHom).comap (algebraMap S S'))
    (Sq : Type*) [CommRing Sq] [Algebra (𝔭.Fiber S) Sq] [IsLocalization.AtPrime Sq q]
    [IsLocalRing Sq] (Tq' : Type*) [CommRing Tq'] [Algebra (𝔭'.Fiber S') Tq']
    [IsLocalization.AtPrime Tq' q'] [IsLocalRing Tq'] :
    Module.IsMaximalCohenMacaulay Sq Sq ↔ Module.IsMaximalCohenMacaulay Tq' Tq' := by
  let := Ideal.residueFieldAlgebra 𝔭 𝔭'
  have := Ideal.isScalarTower_residueField 𝔭 𝔭'
  let := Ideal.Fiber.baseChangeAlgebra R R' S S' 𝔭 𝔭'
  have := Ideal.Fiber.isScalarTower_baseChange R R' S S' 𝔭 𝔭'
  have := Ideal.Fiber.isPushout_baseChange R R' S S' 𝔭 𝔭'
  have : q'.LiesOver q := ⟨eq_of_comap_includeRight_eq 𝔭 <| by
    rw [hqq', Ideal.comap_comap,
      ← Ideal.Fiber.algebraMap_baseChange_comp_includeRight R R' S S' 𝔭 𝔭', Ideal.comap_comap]⟩
  exact Algebra.IsPushout.isMaximalCohenMacaulay_iff 𝔭.ResidueField 𝔭'.ResidueField
    (𝔭.Fiber S) (𝔭'.Fiber S') q q' Sq Tq'

/-! ### The Cohen–Macaulay locus in the fibres -/

/-- The set of primes of `S'` at which the fibre ring over `R'` is Cohen–Macaulay is the preimage
of the corresponding set for `S` over `R`. -/
public theorem solution (R R' S S' : Type*)
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S'] [Algebra R R'] [Algebra R S]
    [Algebra R S'] [Algebra R' S'] [Algebra S S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R R' S S'] [Algebra.FiniteType R S] :
    {𝔮' : PrimeSpectrum S' |
        Module.IsMaximalCohenMacaulay
          (Localization.AtPrime (𝔮'.asIdeal.map (Ideal.Quotient.mk
            ((𝔮'.asIdeal.under R').map (algebraMap R' S')))))
          (Localization.AtPrime (𝔮'.asIdeal.map (Ideal.Quotient.mk
            ((𝔮'.asIdeal.under R').map (algebraMap R' S')))))} =
      PrimeSpectrum.comap (algebraMap S S') ⁻¹'
        {𝔮 : PrimeSpectrum S |
          Module.IsMaximalCohenMacaulay
            (Localization.AtPrime (𝔮.asIdeal.map (Ideal.Quotient.mk
              ((𝔮.asIdeal.under R).map (algebraMap R S)))))
            (Localization.AtPrime (𝔮.asIdeal.map (Ideal.Quotient.mk
              ((𝔮.asIdeal.under R).map (algebraMap R S)))))} := by
  ext 𝔮'
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have : ((PrimeSpectrum.comap (algebraMap R' S') 𝔮').asIdeal).LiesOver
      ((PrimeSpectrum.comap (algebraMap R S)
        (PrimeSpectrum.comap (algebraMap S S') 𝔮')).asIdeal) := ⟨by
    show Ideal.comap (algebraMap R S) (Ideal.comap (algebraMap S S') 𝔮'.asIdeal)
        = Ideal.comap (algebraMap R R') (Ideal.comap (algebraMap R' S') 𝔮'.asIdeal)
    rw [Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R S S',
      ← IsScalarTower.algebraMap_eq R R' S']⟩
  obtain ⟨_, _⟩ := exists_isLocalization_fiberRing (R := R)
    (PrimeSpectrum.comap (algebraMap S S') 𝔮')
  obtain ⟨_, _⟩ := exists_isLocalization_fiberRing (R := R') 𝔮'
  refine (isMaximalCohenMacaulay_iff_of_fiber R R' S S'
    (PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap (algebraMap S S') 𝔮')).asIdeal
    (PrimeSpectrum.comap (algebraMap R' S') 𝔮').asIdeal
    (fiberPoint (R := R) (PrimeSpectrum.comap (algebraMap S S') 𝔮')).asIdeal
    (fiberPoint (R := R') 𝔮').asIdeal ?_
    (fiberRing R (PrimeSpectrum.comap (algebraMap S S') 𝔮').asIdeal)
    (fiberRing R' 𝔮'.asIdeal)).symm
  rw [comap_asIdeal_fiberPoint (R := R) (PrimeSpectrum.comap (algebraMap S S') 𝔮'),
    comap_asIdeal_fiberPoint (R := R') 𝔮']
  rfl

end Stacks.CohenMacaulay.LocusBaseChange

end

@[expose] public section

namespace Algebra.IsPushout

/-- Let `R → S` be of finite type, let `R → R'` be any ring map and let `S' = R' ⊗_R S`,
presented as a pushout square. Let `f : Spec S' → Spec S` be the map of the ring map `S → S'`.
Then the set `W'` of primes `𝔮'` of `S'` whose fibre ring `S'_{𝔮'} ⊗_{R'} κ(𝔭')`,
`𝔭' = R' ∩ 𝔮'`, is Cohen–Macaulay is the preimage `f ⁻¹' W` of the corresponding set `W` for `S`
over `R`. The fibre ring is the localization of `S/𝔭S` at the prime `𝔮/𝔭S`. -/
@[stacks 00RK "The base change is an arbitrary pushout square `Algebra.IsPushout R R' S S'`, as in
the siblings 00P3, 00P4 and 00SS, so `f` is `PrimeSpectrum.comap (algebraMap S S')`. The fibre
ring `S_𝔮 ⊗_R κ(𝔭)` is `Localization.AtPrime` of the image of `𝔮` in `S/𝔭S`, with `𝔭 = 𝔮.under R`,
as in 00RH and 00RI, and Cohen-Macaulayness of a local ring (Definition 00N8) is
`Module.IsMaximalCohenMacaulay A A` (tag 00NF). The conclusion is the source's equality of sets of
primes; `Set.ext_iff` gives the pointwise form. See the module docstring."]
public theorem setOf_isMaximalCohenMacaulay_fiber_eq_preimage_comap (R R' S S' : Type*)
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S'] [Algebra R R'] [Algebra R S]
    [Algebra R S'] [Algebra R' S'] [Algebra S S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R R' S S'] [Algebra.FiniteType R S] :
    {𝔮' : PrimeSpectrum S' |
        Module.IsMaximalCohenMacaulay
          (Localization.AtPrime (𝔮'.asIdeal.map (Ideal.Quotient.mk
            ((𝔮'.asIdeal.under R').map (algebraMap R' S')))))
          (Localization.AtPrime (𝔮'.asIdeal.map (Ideal.Quotient.mk
            ((𝔮'.asIdeal.under R').map (algebraMap R' S')))))} =
      PrimeSpectrum.comap (algebraMap S S') ⁻¹'
        {𝔮 : PrimeSpectrum S |
          Module.IsMaximalCohenMacaulay
            (Localization.AtPrime (𝔮.asIdeal.map (Ideal.Quotient.mk
              ((𝔮.asIdeal.under R).map (algebraMap R S)))))
            (Localization.AtPrime (𝔮.asIdeal.map (Ideal.Quotient.mk
              ((𝔮.asIdeal.under R).map (algebraMap R S)))))} :=
  Stacks.CohenMacaulay.LocusBaseChange.solution R R' S S'

end Algebra.IsPushout

end
