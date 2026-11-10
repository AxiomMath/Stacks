module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppUniverseAssembly
public import StacksFrontier.RingTheory.IntegralClosure.DedekindDomain

/-!
# Transporting a weak solution across an intermediate base DVR

Let `R → A → B` be a tower of discrete valuation rings with fraction fields
`k → K → L`.  If a finite extension `E / k` is a weak solution for `R → B`, choose a
field factor `F` of `K ⊗[k] E`.  Then `F / K` is finite and is a weak solution for `A → B`.

This is the base-change transport needed by the perfect-core reduction in Epp's theorem.  The
point is that one chooses a single field factor of `K ⊗[k] E`; one does not assert that every
factor of a preassigned base change is simultaneously a weak solution.  The induced map

`(L ⊗[k] E)ᵣₑᵈ → (L ⊗[K] F)ᵣₑᵈ`

is surjective.  Since its source is a reduced Artinian ring, it is semisimple, and the induced
map on integral closures is a flat surjection.  Ramification indices are unchanged by that
surjection; ramification index one over the smaller base then implies ramification index one over
the intermediate base by divisibility in a flat tower.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

open IsDiscreteValuationRing

universe u

/-- Ramification index one passes to the upper part of a flat tower. -/
private theorem ramificationIdx_eq_one_of_flat_tower
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T] (q : Ideal T) (h : q.ramificationIdx R = 1) :
    q.ramificationIdx S = 1 :=
  Nat.dvd_one.mp (h ▸ Ideal.ramificationIdx_above_dvd (R := R) (q.under S) q)

/-- A tensor product with a finite field extension has a finite field quotient. -/
private theorem exists_finite_field_tensorProduct_surjective
    (k K E : Type u) [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Module.Finite k E] :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : Module.Finite K F),
      ∃ g : K ⊗[k] E →ₐ[K] F, Function.Surjective g := by
  classical
  obtain ⟨q, hq⟩ := Ideal.exists_maximal (K ⊗[k] E)
  let F := (K ⊗[k] E) ⧸ q
  let : Field F := Ideal.Quotient.field q
  have : Module.Finite K F := inferInstance
  exact ⟨F, inferInstance, inferInstance, this, Ideal.Quotient.mkₐ K q,
    Ideal.Quotient.mk_surjective⟩

/-- A surjective algebra map from a semisimple ring splits off a product factor. -/
private theorem exists_algEquiv_prod_of_surjective
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [IsSemisimpleRing S]
    (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    ∃ (U : Type u) (_ : CommRing U) (_ : Algebra R U),
      ∃ e : S ≃ₐ[R] T × U, ∀ x, (e x).1 = f x := by
  classical
  let I := RingHom.ker f
  obtain ⟨J, hJ⟩ := exists_isCompl I
  let g : S →ₐ[R] T × (S ⧸ J) := f.prod (Ideal.Quotient.mkₐ R J)
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).mpr fun x hx ↦ ?_
    have hxij : x ∈ I ⊓ J :=
      ⟨congrArg Prod.fst hx, Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩
    simpa only [hJ.inf_eq_bot, Ideal.mem_bot] using hxij
  have hsurj : Function.Surjective g := by
    have h1 : (1 : S) ∈ I ⊔ J := by rw [hJ.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    have hfa : f a = 0 := ha
    have hfb : f b = 1 := by
      simpa only [map_add, hfa, zero_add, map_one] using congrArg f hab
    have hqb : Ideal.Quotient.mk J b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    have hqa : Ideal.Quotient.mk J a = 1 := by
      simpa only [map_add, hqb, add_zero, map_one] using congrArg (Ideal.Quotient.mk J) hab
    rintro ⟨t, z⟩
    obtain ⟨x, rfl⟩ := hf t
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨b * x + a * y, Prod.ext (by simp [g, hfa, hfb]) (by simp [g, hqa, hqb])⟩
  exact ⟨S ⧸ J, inferInstance, inferInstance, AlgEquiv.ofBijective g ⟨hinj, hsurj⟩,
    fun _ ↦ rfl⟩

/-- Integral closure preserves quotient maps from semisimple rings as flat surjections. -/
private theorem flat_surjective_mapIntegralClosure_of_isSemisimpleRing
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [IsSemisimpleRing S]
    (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    letI := f.mapIntegralClosure.toRingHom.toAlgebra
    Module.Flat (integralClosure R S) (integralClosure R T) ∧
      Function.Surjective f.mapIntegralClosure := by
  classical
  let := f.mapIntegralClosure.toRingHom.toAlgebra
  obtain ⟨U, _, _, e, he⟩ := exists_algEquiv_prod_of_surjective f hf
  have hint : ∀ t : T, IsIntegral R t → IsIntegral R (e.symm (t, 0)) := fun t ht ↦
    (ht.pair (isIntegral_zero : IsIntegral R (0 : U))).map e.symm.toAlgHom
  have hsurj : Function.Surjective f.mapIntegralClosure := by
    intro x
    refine ⟨⟨e.symm ((x : T), 0), hint _ x.property⟩, Subtype.ext ?_⟩
    change f (e.symm ((x : T), 0)) = (x : T)
    rw [← he, e.apply_symm_apply]
  let d : integralClosure R S := ⟨e.symm (1, 0), hint 1 isIntegral_one⟩
  have hd : IsIdempotentElem d := by
    apply Subtype.ext
    change e.symm (1, 0) * e.symm (1, 0) = e.symm (1, 0)
    rw [← map_mul]
    simp only [Prod.mk_mul_mk, one_mul, zero_mul]
  have : IsLocalization.Away d (integralClosure R T) := by
    apply IsLocalization.away_of_isIdempotentElem_of_mul hd _ hsurj
    refine fun x y ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · apply Subtype.ext
      apply e.injective
      have h' : f (x : S) = f (y : S) := congrArg Subtype.val h
      change e ((d : S) * (x : S)) = e ((d : S) * (y : S))
      simp only [map_mul, d, e.apply_symm_apply]
      apply Prod.ext
      · simpa only [Prod.fst_mul, Prod.fst_one, one_mul, he] using h'
      · simp
    · apply Subtype.ext
      change f (x : S) = f (y : S)
      simpa only [Subalgebra.coe_mul, map_mul, d, e.apply_symm_apply,
        Prod.fst_mul, one_mul, he] using
        congrArg (fun z : integralClosure R S ↦ (e (z : S)).1) h
  exact ⟨IsLocalization.flat _ (Submonoid.powers d), hsurj⟩

private noncomputable def tensorProductFactorMap
    {k K L E F : Type u}
    [CommRing k] [CommRing K] [CommRing L] [CommRing E] [CommRing F]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra k E] [Algebra K F] (g : K ⊗[k] E →ₐ[K] F) :
    L ⊗[k] E →ₐ[L] L ⊗[K] F :=
  (Algebra.TensorProduct.map (AlgHom.id L L) g).comp
    (Algebra.TensorProduct.cancelBaseChange k K L L E).symm.toAlgHom

private theorem tensorProductFactorMap_tmul
    {k K L E F : Type u}
    [CommRing k] [CommRing K] [CommRing L] [CommRing E] [CommRing F]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra k E] [Algebra K F] (g : K ⊗[k] E →ₐ[K] F) (l : L) (x : E) :
    tensorProductFactorMap g (l ⊗ₜ[k] x) = l ⊗ₜ[K] g (1 ⊗ₜ[k] x) := by
  simp [tensorProductFactorMap]

private theorem tensorProductFactorMap_surjective
    {k K L E F : Type u}
    [CommRing k] [CommRing K] [CommRing L] [CommRing E] [CommRing F]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra k E] [Algebra K F] (g : K ⊗[k] E →ₐ[K] F) (hg : Function.Surjective g) :
    Function.Surjective (tensorProductFactorMap (L := L) g) :=
  (Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hg).comp
    (Algebra.TensorProduct.cancelBaseChange k K L L E).symm.surjective

private noncomputable def reducedMap
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) :
    S ⧸ nilradical S →ₐ[R] T ⧸ nilradical T :=
  Ideal.quotientMapₐ _ f (by
    intro x hx
    exact (mem_nilradical.mp hx).map f)

private theorem reducedMap_surjective
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (hf : Function.Surjective f) : Function.Surjective (reducedMap f) := by
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨z, rfl⟩ := hf y
  exact ⟨Ideal.Quotient.mk _ z, rfl⟩

/-- A flat surjection of algebras does not change ramification indices over the base. -/
private theorem ramificationIdx_eq_under_of_surjective
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Module.Flat S T]
    (h : Function.Surjective (algebraMap S T)) (r : Ideal T) [r.IsPrime] :
    r.ramificationIdx R = (r.under S).ramificationIdx R := by
  have : Algebra.FormallyUnramified S T :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId S T) h
  have : Algebra.FiniteType S T := Algebra.FiniteType.of_surjective (Algebra.ofId S T) h
  rw [Ideal.ramificationIdx_tower (R := R) (r.under S) r,
    Ideal.ramificationIdx_eq_one r S, mul_one]

/-- A chosen weak solution over a smaller DVR induces one over an intermediate DVR through a
surjective field factor of the scalar extension.  The factor map is retained for descent
arguments that must follow a distinguished element through base change. -/
theorem exists_field_factor_isWeakSolution_of_baseChange
    (R A B k K L : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [IsDomain R] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field k] [Field K] [Field L]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra R k] [Algebra A K] [Algebra B L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    [Algebra R K] [Algebra R L] [Algebra A L]
    [IsScalarTower R k K] [IsScalarTower R k L] [IsScalarTower R K L]
    [IsScalarTower R A K] [IsScalarTower R A L] [IsScalarTower R B L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsExtension R A] [IsExtension A B] [IsExtension R B]
    [IsFractionRing R k] [IsFractionRing A K] [IsFractionRing B L]
    (E : Type u) [Field E] [Algebra k E] [Algebra R E]
    [IsScalarTower R k E] [Module.Finite k E]
    (DE : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} R B k L E)
    (hDE : DE.IsWeakSolution) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ g : K ⊗[k] E →ₐ[K] F, Function.Surjective g ∧
        ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L F,
          D.IsWeakSolution := by
  classical
  let D₀ := canonicalBaseChange R B k L E
  have hD₀ : D₀.IsWeakSolution :=
    isWeakSolution_canonicalBaseChange_of_isWeakSolution R B k L E DE hDE
  obtain ⟨F, hFfield, hKF, hfinF, g, hg⟩ :=
    exists_finite_field_tensorProduct_surjective k K E
  let := hFfield
  let := hKF
  let := hfinF
  let : Algebra k F := ((algebraMap K F).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e : E →ₐ[k] F := (g.restrictScalars k).comp Algebra.TensorProduct.includeRight
  let : Algebra E F := e.toRingHom.toAlgebra
  let : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
  let : Algebra A F := ((algebraMap K F).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra R F := ((algebraMap K F).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower R k F := IsScalarTower.to₁₂₄ R k K F
  let : IsScalarTower R A F := IsScalarTower.to₁₂₄ R A K F
  let : IsScalarTower R E F := IsScalarTower.to₁₃₄ R k E F
  let D₁ := canonicalBaseChange A B K L F
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    g, hg, D₁, ?_⟩
  let S := reducedCompositum k L E
  let T := reducedCompositum K L F
  let R₁ := integralClosure R E
  let A₁ := integralClosure A F
  let B₀ := integralClosure B S
  let B₁ := integralClosure B T
  let φ : S →ₐ[B] T := (reducedMap (tensorProductFactorMap (L := L) g)).restrictScalars B
  have hφ : Function.Surjective φ := reducedMap_surjective (tensorProductFactorMap (L := L) g)
    (tensorProductFactorMap_surjective (L := L) g hg)
  have : IsArtinianRing S := IsArtinianRing.of_finite L S
  have : IsReduced S := (Ideal.isRadical_iff_quotient_reduced _).mp
    (Ideal.radical_isRadical ⊥)
  have : IsSemisimpleRing S := IsArtinianRing.isSemisimpleRing_of_isReduced S
  let : Algebra R₁ B₀ := D₀.algebraA₁B₁
  let : Algebra A₁ B₁ := D₁.algebraA₁B₁
  let : Algebra B₀ B₁ := φ.mapIntegralClosure.toRingHom.toAlgebra
  have hflat := flat_surjective_mapIntegralClosure_of_isSemisimpleRing φ hφ
  have : Module.Flat B₀ B₁ := hflat.1
  let α : R₁ →ₐ[R] A₁ :=
    ((IsScalarTower.toAlgHom R E F).comp R₁.val).codRestrict (A₁.restrictScalars R)
      (fun x ↦ (x.property.map (IsScalarTower.toAlgHom R E F)).tower_top)
  let : Algebra R₁ A₁ := α.toRingHom.toAlgebra
  let : Algebra R₁ B₁ := ((algebraMap B₀ B₁).comp (algebraMap R₁ B₀)).toAlgebra
  have : IsScalarTower R₁ B₀ B₁ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R₁ A₁ B₁ := IsScalarTower.of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    change φ (Ideal.Quotient.mk _ (1 ⊗ₜ[k] (x : E))) =
      Ideal.Quotient.mk _ (1 ⊗ₜ[K] e (x : E))
    change Ideal.Quotient.mk _ (tensorProductFactorMap g (1 ⊗ₜ[k] (x : E))) = _
    rw [tensorProductFactorMap_tmul]
    rfl
  let : IsDedekindDomain A₁ :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite A K F A₁).1
  let : Algebra F (L ⊗[K] F) := Algebra.TensorProduct.rightAlgebra
  let : Algebra F T := Ideal.Quotient.algebra _
  let : Algebra A₁ T := ((algebraMap F T).comp A₁.val.toRingHom).toAlgebra
  let : IsScalarTower A₁ F T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A₁ B₁ T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.IsTorsionFree A₁ T := Module.IsTorsionFree.trans (S := A₁) F (M := T)
  let : Module.IsTorsionFree A₁ B₁ := Function.Injective.moduleIsTorsionFree
    (R := A₁) (fun x : B₁ ↦ (x : T)) Subtype.val_injective
    (fun _ _ ↦ rfl)
  have : Module.Flat A₁ B₁ := inferInstance
  change ∀ (q : Ideal B₁), q.IsMaximal → q.ramificationIdx A₁ = 1
  intro q hq
  apply ramificationIdx_eq_one_of_flat_tower (R := R₁) q
  rw [ramificationIdx_eq_under_of_surjective (R := R₁) hflat.2]
  exact hD₀ (q.under B₀) (Ideal.comap_isMaximal_of_surjective (algebraMap B₀ B₁) hflat.2)

/-- A weak solution over a smaller DVR induces one over an intermediate DVR by choosing a field
factor of the scalar extension. -/
theorem exists_finite_extension_isWeakSolution_of_baseChange
    (R A B k K L : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [IsDomain R] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field k] [Field K] [Field L]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra R k] [Algebra A K] [Algebra B L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    [Algebra R K] [Algebra R L] [Algebra A L]
    [IsScalarTower R k K] [IsScalarTower R k L] [IsScalarTower R K L]
    [IsScalarTower R A K] [IsScalarTower R A L] [IsScalarTower R B L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsExtension R A] [IsExtension A B] [IsExtension R B]
    [IsFractionRing R k] [IsFractionRing A K] [IsFractionRing B L]
    (h : ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra R E)
      (_ : IsScalarTower R k E) (_ : Module.Finite k E),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} R B k L E,
        D.IsWeakSolution) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L F,
        D.IsWeakSolution := by
  obtain ⟨E, _, _, _, _, _, DE, hDE⟩ := h
  obtain ⟨F, _, _, _, _, _, _, _, D, hD⟩ :=
    exists_field_factor_isWeakSolution_of_baseChange R A B k K L E DE hDE
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, hD⟩

end Stacks.EppTheorem

end
