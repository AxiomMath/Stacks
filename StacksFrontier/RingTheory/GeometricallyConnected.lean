module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.GeometricallyConnected.Criteria
public import StacksFrontier.RingTheory.GeometricallyConnected.Defs

@[expose] public section

/-!
# Geometric connectedness of subalgebras, filtered unions and directed colimits

Let `k` be a field. A `k`-algebra `S` is *geometrically connected over `k`* if `Spec (K ⊗[k] S)`
is connected for every field extension `K/k`. Geometric connectedness passes to `k`-subalgebras,
is detected on finitely generated `k`-subalgebras, and is stable under directed colimits. Over a
separably closed field `k`, a `k`-algebra is geometrically connected if and only if its spectrum
is connected.

A connected space is nonempty, so the zero ring does not have connected spectrum.

## Main definitions

* `IsConnectedSpec`: the prime spectrum of a commutative ring is a connected space.

## Main results

* `isConnectedSpec_iff`: `Spec R` is connected if and only if `R` is nontrivial and has no
  idempotents besides `0` and `1`.
* `geometricallyConnected_of_subalgebra`: a `k`-subalgebra of a geometrically connected
  `k`-algebra is geometrically connected.
* `geometricallyConnected_of_forall_fg`: a `k`-algebra all of whose finitely generated
  `k`-subalgebras are geometrically connected is geometrically connected.
* `geometricallyConnected_of_directedColimit`: a directed colimit of geometrically connected
  `k`-algebras is geometrically connected.
* `Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum`: over a separably closed
  field `k`, a `k`-algebra `R` is geometrically connected over `k` if and only if `Spec R` is
  connected.

## References

* [Stacks 037V](https://stacks.math.columbia.edu/tag/037V)
* [Stacks 037U](https://stacks.math.columbia.edu/tag/037U)
-/

@[expose] public section

universe u w v

open scoped TensorProduct

/-- A commutative ring `R` has *connected spectrum* if the prime spectrum `Spec(R)`, equipped with
the Zariski topology, is a connected topological space. A connected space is nonempty, so the zero
ring does not have connected spectrum. -/
@[ega "I 2.1.8" "special case"]
def IsConnectedSpec (R : Type*) [CommRing R] : Prop :=
  ConnectedSpace (PrimeSpectrum R)

/-- A `k`-algebra `S` is geometrically connected over `k` exactly when, for every field
extension `k'/k` in the universe of `k`, the base change `S ⊗[k] k'` has connected spectrum. -/
private theorem isGeometricallyConnected_iff_forall_isConnectedSpec
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S] :
    Algebra.IsGeometricallyConnected k S ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k'], IsConnectedSpec (S ⊗[k] k') :=
  have swap : ∀ (k' : Type u) [Field k'] [Algebra k k'],
      (IsConnectedSpec (S ⊗[k] k') ↔ ConnectedSpace (PrimeSpectrum (k' ⊗[k] S))) :=
    fun k' _ _ ↦ (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm k S k').toRingEquiv).connectedSpace_iff
  ⟨fun h k' _ _ ↦ (swap k').mpr (h.connectedSpace_primeSpectrum_tensorProduct k'),
    fun h ↦ ⟨fun k' _ _ ↦ (swap k').mp (h k')⟩⟩

/-- For a commutative ring `R`, `Spec R` is connected if and only if `R` is nonzero
(`Nontrivial`) and has no nontrivial idempotents (the only `e` with `e ^ 2 = e` are `0` and
`1`). -/
@[ega "III 7.8.6.1" "affine case Z = Spec R"]
theorem isConnectedSpec_iff (R : Type*) [CommRing R] :
    IsConnectedSpec R ↔ (Nontrivial R ∧ ∀ e : R, e ^ 2 = e → e = 0 ∨ e = 1) := by
  have key : PreconnectedSpace (PrimeSpectrum R) ↔ ∀ e : R, e ^ 2 = e → e = 0 ∨ e = 1 := by
    simp only [PrimeSpectrum.preconnectedSpace_iff_isIdempotentElem, isIdempotentElem_iff, sq]
  rw [IsConnectedSpec, ← key, ← PrimeSpectrum.nonempty_iff_nontrivial]
  exact ⟨fun h ↦ ⟨h.toNonempty, h.toPreconnectedSpace⟩,
    fun ⟨h₁, h₂⟩ ↦ @ConnectedSpace.mk _ _ h₂ h₁⟩

/-- Connected spectrum is reflected along an injective ring hom, given nontriviality of
the source. -/
theorem isConnectedSpec_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Nontrivial A] (f : A →+* B) (hf : Function.Injective f) (hB : IsConnectedSpec B) :
    IsConnectedSpec A := by
  rw [isConnectedSpec_iff] at hB ⊢
  exact ⟨inferInstance, fun e he ↦ (hB.2 (f e) (by rw [← map_pow, he])).imp
    (fun h ↦ hf (by rw [h, map_zero])) fun h ↦ hf (by rw [h, map_one])⟩

/-- Base change of the inclusion of a subalgebra along a field extension is injective. -/
theorem subalgebra_baseChange_injective
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (R : Subalgebra k S) (k' : Type u) [Field k'] [Algebra k k'] :
    Function.Injective
      (Algebra.TensorProduct.map (R.val) (AlgHom.id k k') : (R ⊗[k] k') →ₐ[k] (S ⊗[k] k')) := by
  exact Stacks.TensorProduct.IdempotentBijection.tensorProduct_map_injective R.val
    (AlgHom.id k k') Subtype.val_injective fun _ _ h ↦ h

/-- A ring hom sends `0` or `1` to `0` or `1`. -/
private theorem map_eq_zero_or_one {A B F : Type*} [Semiring A] [Semiring B] [FunLike F A B]
    [RingHomClass F A B] (f : F) {e : A} (h : e = 0 ∨ e = 1) : f e = 0 ∨ f e = 1 := by
  rcases h with rfl | rfl <;> simp

/-- If `F` maps into `S ⊗[k] k'` and each term of a finite-sum decomposition of `x` is in the range
of `F`, then so is `x`. -/
private theorem exists_eq_of_forall_tmul {k : Type u} {S M k' : Type*} [Field k] [CommRing S]
    [Algebra k S] [AddCommMonoid M] [Field k'] [Algebra k k'] {G : Type*}
    [FunLike G M (S ⊗[k] k')] [AddMonoidHomClass G M (S ⊗[k] k')] (F : G) (x : S ⊗[k] k')
    (T : Finset (S × k')) (hT : x = ∑ p ∈ T, p.1 ⊗ₜ[k] p.2)
    (h : ∀ p ∈ T, ∃ y, F y = p.1 ⊗ₜ[k] p.2) : ∃ y, F y = x :=
  hT ▸ (AddMonoidHom.mrange (F : M →+ S ⊗[k] k')).sum_mem h

/-- If `S` is geometrically connected over `k`, then every `k`-subalgebra `R ⊆ S` is
geometrically connected over `k`. -/
@[stacks 037V "(1)"]
theorem geometricallyConnected_of_subalgebra
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (hS : Algebra.IsGeometricallyConnected k S) (R : Subalgebra k S) :
    Algebra.IsGeometricallyConnected k R := by
  rw [isGeometricallyConnected_iff_forall_isConnectedSpec] at hS ⊢
  intro k' _ _
  let F : (R ⊗[k] k') →+* (S ⊗[k] k') := Algebra.TensorProduct.map (R.val) (AlgHom.id k k')
  have : Nontrivial (S ⊗[k] k') := ((isConnectedSpec_iff _).mp (hS k')).1
  have : Nontrivial (R ⊗[k] k') := F.domain_nontrivial
  exact isConnectedSpec_of_injective F (subalgebra_baseChange_injective k S R k') (hS k')

/-- If every finitely generated `k`-subalgebra of `S` is geometrically connected over `k`,
then `S` is geometrically connected over `k`. -/
@[stacks 037V "(2)"]
theorem geometricallyConnected_of_forall_fg
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (h : ∀ R : Subalgebra k S, R.FG → Algebra.IsGeometricallyConnected k R) :
    Algebra.IsGeometricallyConnected k S := by
  classical
  simp only [isGeometricallyConnected_iff_forall_isConnectedSpec] at h ⊢
  intro k' _ _
  rw [isConnectedSpec_iff]
  have : Nontrivial ((⊥ : Subalgebra k S) ⊗[k] k') :=
    ((isConnectedSpec_iff _).mp (h ⊥ Subalgebra.fg_bot k')).1
  refine ⟨(subalgebra_baseChange_injective k S ⊥ k').nontrivial, fun x hx ↦ ?_⟩
  obtain ⟨T, hT⟩ := TensorProduct.exists_finset x
  set R : Subalgebra k S := Algebra.adjoin k ((T.image Prod.fst : Finset S) : Set S)
  set F : (R ⊗[k] k') →ₐ[k] (S ⊗[k] k') :=
    Algebra.TensorProduct.map (R.val) (AlgHom.id k k') with hFdef
  have hFinj : Function.Injective F := subalgebra_baseChange_injective k S R k'
  have hmem : ∀ p ∈ T, p.fst ∈ R := fun p hp ↦
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst hp))
  obtain ⟨y, hFy⟩ := exists_eq_of_forall_tmul F x T hT fun p hp ↦
    ⟨(⟨p.1, hmem p hp⟩ : R) ⊗ₜ[k] p.2, by simp [hFdef]⟩
  rw [← hFy]
  exact map_eq_zero_or_one F (((isConnectedSpec_iff _).mp (h R ⟨T.image Prod.fst, rfl⟩ k')).2 y
    (hFinj (by rw [map_pow, hFy, hx])))

/-- A filtered colimit of rings with connected spectrum again has connected spectrum. The
colimit is presented elementarily by its universal property: a directed index set `ι` and a
cocone `g i : T i →+* T` that is *jointly surjective* and *detects equality at a finite
stage* via the transition maps `f`. -/
theorem isConnectedSpec_of_directedColimit_core
    (ι : Type w) [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (T : ι → Type v) [(i : ι) → CommRing (T i)]
    (f : (i j : ι) → i ≤ j → (T i →+* T j))
    (U : Type v) [CommRing U]
    (g : (i : ι) → (T i →+* U))
    (hg : ∀ (i j : ι) (hij : i ≤ j), (g j).comp (f i j hij) = g i)
    (hsurj : ∀ x : U, ∃ (i : ι) (y : T i), g i y = x)
    (hsep : ∀ (i : ι) (y z : T i), g i y = g i z →
      ∃ (j : ι) (hij : i ≤ j), f i j hij y = f i j hij z)
    (hconn : ∀ i, IsConnectedSpec (T i)) :
    IsConnectedSpec U := by
  rw [isConnectedSpec_iff]
  refine ⟨?_, fun ε hε ↦ ?_⟩
  · let i₀ := Classical.arbitrary ι
    refine nontrivial_of_ne (0 : U) 1 fun h01 ↦ ?_
    obtain ⟨j, hij, hfe⟩ := hsep i₀ 0 1 (by rw [map_zero, map_one, h01])
    have : Nontrivial (T j) := ((isConnectedSpec_iff (T j)).mp (hconn j)).1
    rw [map_zero, map_one] at hfe
    exact zero_ne_one hfe
  · obtain ⟨i, e₀, rfl⟩ := hsurj ε
    obtain ⟨j, hij, hfe⟩ := hsep i (e₀ ^ 2) e₀ (by rw [map_pow, hε])
    have htrans : g j (f i j hij e₀) = g i e₀ := RingHom.congr_fun (hg i j hij) e₀
    rw [← htrans]
    exact map_eq_zero_or_one (g j) (((isConnectedSpec_iff (T j)).mp (hconn j)).2 (f i j hij e₀)
      (by rw [← map_pow, hfe]))

/-- A directed colimit of geometrically connected `k`-algebras is geometrically connected
over `k`. The colimit `S` of the directed system `(S_i, φ_{ij})` with cocone maps
`ψ_i : S_i →ₐ[k] S` is presented by its elementary universal property: the `ψ_i` are jointly
surjective, and `ψ_i y = ψ_i z` holds only if `y` and `z` become equal after some transition map
`φ_{ij}`. -/
@[stacks 037V "(3)"]
theorem geometricallyConnected_of_directedColimit
    (k : Type u) [Field k]
    (ι : Type w) [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (Sfun : ι → Type v) [(i : ι) → CommRing (Sfun i)] [(i : ι) → Algebra k (Sfun i)]
    (φ : (i j : ι) → i ≤ j → (Sfun i →ₐ[k] Sfun j))
    (hφcomp : ∀ (i j l : ι) (hij : i ≤ j) (hjl : j ≤ l),
      (φ j l hjl).comp (φ i j hij) = φ i l (le_trans hij hjl))
    (S : Type v) [CommRing S] [Algebra k S]
    (ψ : (i : ι) → (Sfun i →ₐ[k] S))
    (hψ : ∀ (i j : ι) (hij : i ≤ j), (ψ j).comp (φ i j hij) = ψ i)
    (hsurj : ∀ x : S, ∃ (i : ι) (y : Sfun i), ψ i y = x)
    (hsep : ∀ (i : ι) (y z : Sfun i), ψ i y = ψ i z →
      ∃ (j : ι) (hij : i ≤ j), φ i j hij y = φ i j hij z)
    (hgc : ∀ i, Algebra.IsGeometricallyConnected k (Sfun i)) :
    Algebra.IsGeometricallyConnected k S := by
  simp only [isGeometricallyConnected_iff_forall_isConnectedSpec] at hgc ⊢
  intro k' _ _
  set φ' : (i j : ι) → i ≤ j → ((Sfun i ⊗[k] k') →ₐ[k] (Sfun j ⊗[k] k')) :=
    fun i j h ↦ Algebra.TensorProduct.map (φ i j h) (AlgHom.id k k') with hφ'def
  set ψ' : (i : ι) → ((Sfun i ⊗[k] k') →ₐ[k] (S ⊗[k] k')) :=
    fun i ↦ Algebra.TensorProduct.map (ψ i) (AlgHom.id k k') with hψ'def
  have hψ' : ∀ (i j : ι) (hij : i ≤ j), (ψ' j).comp (φ' i j hij) = ψ' i := fun i j hij ↦ by
    rw [hψ'def, hφ'def, ← Algebra.TensorProduct.map_comp, hψ i j hij, AlgHom.id_comp]
  have hsurj' : ∀ x : S ⊗[k] k', ∃ (i : ι) (y : Sfun i ⊗[k] k'), ψ' i y = x := by
    classical
    intro x
    obtain ⟨T, hT⟩ := TensorProduct.exists_finset x
    set idx : S × k' → ι := fun p ↦ (hsurj p.fst).choose
    set wit : (p : S × k') → Sfun (idx p) := fun p ↦ (hsurj p.fst).choose_spec.choose
    have hwit_spec : ∀ p : S × k', ψ (idx p) (wit p) = p.fst :=
      fun p ↦ (hsurj p.fst).choose_spec.choose_spec
    obtain ⟨j, hj⟩ := Finset.exists_le (T.image idx)
    have hidxle : ∀ p ∈ T, idx p ≤ j := fun p hp ↦ hj (idx p) (Finset.mem_image_of_mem idx hp)
    refine ⟨j, exists_eq_of_forall_tmul (ψ' j) x T hT fun p hp ↦
      ⟨φ (idx p) j (hidxle p hp) (wit p) ⊗ₜ[k] p.snd, by
        rw [hψ'def, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
        congr 1
        simpa using (AlgHom.congr_fun (hψ (idx p) j (hidxle p hp)) (wit p)).trans
          (hwit_spec p)⟩⟩
  have hsep' : ∀ (i : ι) (u v : Sfun i ⊗[k] k'), ψ' i u = ψ' i v →
      ∃ (j : ι) (hij : i ≤ j), φ' i j hij u = φ' i j hij v := by
    classical
    set B := Module.Free.chooseBasis k k'
    set κ := Module.Free.ChooseBasisIndex k k'
    have nat : ∀ (M N : Type v) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
        (ρ : M →ₗ[k] N) (z : M ⊗[k] k'),
        (TensorProduct.equivFinsuppOfBasisRight (M := N) (N := k') B) (ρ.rTensor k' z)
          = ((TensorProduct.equivFinsuppOfBasisRight (M := M) (N := k') B) z).mapRange ρ
              (map_zero ρ) := by
      intro M N _ _ _ _ ρ z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul m c =>
          rw [LinearMap.rTensor_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
              TensorProduct.equivFinsuppOfBasisRight_apply_tmul]
          ext b
          simp [Finsupp.mapRange_apply, map_smul]
      | add x y hx hy => simp [map_add, hx, hy, Finsupp.mapRange_add]
    have bridge : ∀ {M N : Type v} [CommRing M] [Algebra k M] [CommRing N] [Algebra k N]
        (ρ : M →ₐ[k] N) (z : M ⊗[k] k'),
        Algebra.TensorProduct.map ρ (AlgHom.id k k') z = ρ.toLinearMap.rTensor k' z := by
      intro M N _ _ _ _ ρ z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a c => simp [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      | add x y hx hy => simp [map_add, hx, hy]
    have bridgeψ : ∀ (i : ι) (z : Sfun i ⊗[k] k'), ψ' i z = (ψ i).toLinearMap.rTensor k' z :=
      fun i ↦ bridge (ψ i)
    have bridgeφ : ∀ (i j : ι) (hij : i ≤ j) (z : Sfun i ⊗[k] k'),
        φ' i j hij z = (φ i j hij).toLinearMap.rTensor k' z := fun i j hij ↦ bridge (φ i j hij)
    intro i u v huv
    set ei := TensorProduct.equivFinsuppOfBasisRight (M := Sfun i) (N := k') B
    set cu := ei u with hcu
    set cv := ei v with hcv
    have hcoord : ∀ b : κ, ψ i (cu b) = ψ i (cv b) := by
      have h1 := congrArg (TensorProduct.equivFinsuppOfBasisRight (M := S) (N := k') B) huv
      rw [bridgeψ, bridgeψ, nat (Sfun i) S (ψ i).toLinearMap u,
          nat (Sfun i) S (ψ i).toLinearMap v] at h1
      exact fun b ↦ by simpa [Finsupp.mapRange_apply, hcu, hcv] using DFunLike.congr_fun h1 b
    set s : Finset κ := cu.support ∪ cv.support
    have hjb : ∀ b : κ, ∃ (jb : ι) (hib : i ≤ jb), φ i jb hib (cu b) = φ i jb hib (cv b) :=
      fun b ↦ hsep i (cu b) (cv b) (hcoord b)
    set jbf : κ → ι := fun b ↦ (hjb b).choose
    have hjbf_le : ∀ b, i ≤ jbf b := fun b ↦ (hjb b).choose_spec.choose
    have hjbf_eq : ∀ b, φ i (jbf b) (hjbf_le b) (cu b) = φ i (jbf b) (hjbf_le b) (cv b) :=
      fun b ↦ (hjb b).choose_spec.choose_spec
    obtain ⟨j, hj⟩ := Finset.exists_le (insert i (s.image jbf))
    have hij : i ≤ j := hj i (Finset.mem_insert_self _ _)
    have hjbf_to_j : ∀ b ∈ s, jbf b ≤ j := fun b hb ↦
      hj (jbf b) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jbf hb))
    refine ⟨j, hij, ?_⟩
    apply (TensorProduct.equivFinsuppOfBasisRight (M := Sfun j) (N := k') B).injective
    rw [bridgeφ, bridgeφ, nat (Sfun i) (Sfun j) (φ i j hij).toLinearMap u,
        nat (Sfun i) (Sfun j) (φ i j hij).toLinearMap v]
    ext b
    simp only [Finsupp.mapRange_apply]
    show φ i j hij (cu b) = φ i j hij (cv b)
    by_cases hb : b ∈ s
    · rw [← hφcomp i (jbf b) j (hjbf_le b) (hjbf_to_j b hb)]
      exact congrArg (φ (jbf b) j (hjbf_to_j b hb)) (hjbf_eq b)
    · have hcu0 : cu b = 0 :=
        Finsupp.notMem_support_iff.mp (fun h ↦ hb (Finset.mem_union_left _ h))
      have hcv0 : cv b = 0 :=
        Finsupp.notMem_support_iff.mp (fun h ↦ hb (Finset.mem_union_right _ h))
      rw [hcu0, hcv0]
  refine isConnectedSpec_of_directedColimit_core ι (fun i ↦ Sfun i ⊗[k] k')
    (fun i j hij ↦ (φ' i j hij : (Sfun i ⊗[k] k') →+* (Sfun j ⊗[k] k')))
    (S ⊗[k] k') (fun i ↦ (ψ' i : (Sfun i ⊗[k] k') →+* (S ⊗[k] k')))
    (fun i j hij ↦ ?_) hsurj' hsep' fun i ↦ hgc i k'
  exact congrArg AlgHom.toRingHom (hψ' i j hij)

open scoped TensorProduct

namespace Stacks.RingTheory.SepClosedConnected

/-- Base change along an isomorphism of base rings does not change the spectrum: if
`algebraMap R A` is bijective, then `Spec (A ⊗[R] B)` is connected if and only if `Spec B` is. -/
private theorem connectedSpace_primeSpectrum_tensorProduct_iff (R : Type*) (A : Type*)
    (B : Type*) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (h : Function.Bijective (algebraMap R A)) :
    ConnectedSpace (PrimeSpectrum (A ⊗[R] B)) ↔ ConnectedSpace (PrimeSpectrum B) :=
  (PrimeSpectrum.homeomorphOfRingEquiv
    ((Algebra.TensorProduct.congr (AlgEquiv.ofBijective (Algebra.ofId R A) h)
      (AlgEquiv.refl (R := R) (A₁ := B))).symm.trans
        (Algebra.TensorProduct.lid R B)).toRingEquiv).connectedSpace_iff

/-- Over a separably closed field `k`, a `k`-algebra `R` is geometrically connected over `k` if and
only if `Spec R` is connected. -/
public theorem solution (k : Type u) (R : Type v) [Field k] [IsSepClosed k] [CommRing R]
    [Algebra k R] :
    Algebra.IsGeometricallyConnected k R ↔ ConnectedSpace (PrimeSpectrum R) := by
  rw [Algebra.isGeometricallyConnected_iff_forall_finite_separable]
  exact ⟨fun h ↦ (connectedSpace_primeSpectrum_tensorProduct_iff k k R
      (IsSepClosed.algebraMap_bijective k k)).mp (h k),
    fun h K _ _ _ _ ↦ (connectedSpace_primeSpectrum_tensorProduct_iff k K R
      (IsSepClosed.algebraMap_bijective k K)).mpr h⟩

end Stacks.RingTheory.SepClosedConnected

/-- **Geometric connectedness over a separably closed field.** Let `k` be a separably
algebraically closed field and let `R` be a `k`-algebra. Then `R` is geometrically connected
over `k` if and only if `Spec R` is connected. -/
@[stacks 037U]
public theorem Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum
    (k : Type u) (R : Type v) [Field k] [IsSepClosed k] [CommRing R] [Algebra k R] :
    Algebra.IsGeometricallyConnected k R ↔ ConnectedSpace (PrimeSpectrum R) :=
  Stacks.RingTheory.SepClosedConnected.solution k R
