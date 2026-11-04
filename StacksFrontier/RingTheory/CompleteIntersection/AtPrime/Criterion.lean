module

import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.NaiveCotangent.Localization
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.Spectrum.Prime.Codimension
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime.GlobalFromLocal

/-!
# The complete intersection criterion at a prime: from item (1) to item (2), and the criterion

A standard open `D(g)` of a spectrum has the dimension of `R[g⁻¹]`
(`PrimeSpectrum.topologicalKrullDim_basicOpen_le_ringKrullDim`), conormal modules after base change
to a field, the implication (1) ⇒ (2)
(`Algebra.Generators.spanFinrank_ker_map_le_of_exists_isGlobalCompleteIntersection_away`), and the
five equivalent conditions (`Algebra.Generators.tfae_isGlobalCompleteIntersection_away`).

See `StacksFrontier.RingTheory.CompleteIntersection.AtPrime` for the overview and references.
-/

@[expose] public section

universe u v w

open IsLocalRing RingTheory.Sequence

variable {A : Type*} [CommRing A]

/-! ### From item (1) to item (2): the local dimension and a standard open -/

/-- **A standard open of a spectrum has the dimension of the localization it carries.** The
corestriction of `Spec R[g⁻¹] → Spec R` to `D(g)` is a continuous bijection which is inducing, so a
homeomorphism; this is the inequality opposite to
`PrimeSpectrum.ringKrullDim_le_topologicalKrullDim_basicOpen`. -/
@[ega "IV 5.1.1" "partial"]
theorem PrimeSpectrum.topologicalKrullDim_basicOpen_le_ringKrullDim
    {R : Type*} [CommRing R] (g : R) (T : Type*) [CommRing T] [Algebra R T]
    [IsLocalization.Away g T] :
    topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ≤ ringKrullDim T := by
  have hrange : Set.range (PrimeSpectrum.comap (algebraMap R T))
      = (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range T g
  set f : PrimeSpectrum T → (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) :=
    fun p => ⟨PrimeSpectrum.comap (algebraMap R T) p, hrange ▸ Set.mem_range_self p⟩ with hf
  have hind : Topology.IsInducing f := by
    refine Topology.IsInducing.of_comp ?_ continuous_subtype_val ?_
    · exact Continuous.subtype_mk (PrimeSpectrum.continuous_comap _) _
    · exact (PrimeSpectrum.localization_comap_isEmbedding T (Submonoid.powers g)).isInducing
  have hinj : Function.Injective f := fun a b hab =>
    PrimeSpectrum.localization_comap_injective T (Submonoid.powers g) (by
      simpa [hf] using hab)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, by simp [hf, hp]⟩
  let e : PrimeSpectrum T ≃ₜ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) :=
    (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfIsInducing hind
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact e.symm.isInducing.topologicalKrullDim_le

/-- **The dimension of a spectrum at a point is at most that of a standard open through it.** -/
theorem PrimeSpectrum.localKrullDim_le_ringKrullDim_of_notMem
    {R : Type*} [CommRing R] (x : PrimeSpectrum R) {g : R} (hg : g ∉ x.asIdeal)
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization.Away g T] :
    TopologicalSpace.localKrullDim (PrimeSpectrum R) x ≤ ringKrullDim T := by
  refine le_trans ?_ (PrimeSpectrum.topologicalKrullDim_basicOpen_le_ringKrullDim g T)
  rw [TopologicalSpace.localKrullDim]
  exact iInf_le_of_le _ (iInf_le_of_le (PrimeSpectrum.basicOpen g).isOpen
    (iInf_le _ ((PrimeSpectrum.mem_basicOpen g x).2 hg)))

/-! ### Conormal modules after base change to a field -/

open TensorProduct in
private theorem finrank_le_of_surjective {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    (hf : Function.Surjective f) : Module.finrank K W ≤ Module.finrank K V := by
  have h := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top] at h

open TensorProduct in
private theorem tensor_map_surjective {A : Type*} [CommRing A] {K : Type*} [CommRing K]
    [Algebra A K] {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    Function.Surjective (AlgebraTensorModule.map (LinearMap.id (R := K) (M := K)) f) := by
  intro u
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a n => obtain ⟨m, rfl⟩ := hf n; exact ⟨a ⊗ₜ m, rfl⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', by rw [map_add]⟩

/-- The `A`-linear surjection `A ⊗[R] I → I·A` onto the extension of `I` to an `R`-algebra `A`. -/
private noncomputable def idealBaseChangeMap {R : Type*} [CommRing R] (I : Ideal R)
    (A : Type*) [CommRing A] [Algebra R A] :
    TensorProduct R A ↥I →ₗ[A] ↥(I.map (algebraMap R A)) :=
  LinearMap.liftBaseChange A
    { toFun := fun y => ⟨algebraMap R A y.1, Ideal.mem_map_of_mem _ y.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext; simp [Algebra.smul_def] }

private theorem idealBaseChangeMap_surjective {R : Type*} [CommRing R] (I : Ideal R)
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Surjective (idealBaseChangeMap I A) := by
  rw [← LinearMap.range_eq_top, idealBaseChangeMap, LinearMap.range_liftBaseChange]
  refine Submodule.map_injective_of_injective
    (f := (I.map (algebraMap R A)).subtype) Subtype.val_injective ?_
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  show Submodule.span A _ = Ideal.span (algebraMap R A '' I)
  congr 1
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_range, Submodule.coe_subtype]
  constructor
  · rintro ⟨w, ⟨y, rfl⟩, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨algebraMap R A y, Ideal.mem_map_of_mem _ hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩

open TensorProduct in
/-- **The minimal number of generators of an extended ideal, after Nakayama.** If `A` is a local
`R`-algebra and `I ⊆ R` is a finitely generated ideal, then the ideal `I·A` needs at most
`dim_κ (κ ⊗_R I)` generators, `κ` being the residue field of `A`: the two are in fact equal, the
canonical map `A ⊗_R I → I·A` being surjective. -/
private theorem spanFinrank_map_le_finrank_residueField_tensor
    {R : Type*} [CommRing R] {I : Ideal R} (hI : I.FG)
    (A : Type*) [CommRing A] [IsLocalRing A] [Algebra R A] :
    (I.map (algebraMap R A)).spanFinrank
      ≤ Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A ⊗[R] ↥I) := by
  have hfinI : Module.Finite R ↥I := Module.Finite.iff_fg.2 hI
  have hfin1 : Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[R] ↥I) :=
    Module.Finite.base_change R (IsLocalRing.ResidueField A) ↥I
  let e : IsLocalRing.ResidueField A ⊗[A] (A ⊗[R] ↥I)
      ≃ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A ⊗[R] ↥I :=
    AlgebraTensorModule.cancelBaseChange R A (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A) ↥I
  have hfin2 : Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] (A ⊗[R] ↥I)) := Module.Finite.equiv e.symm
  have hstep : Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A ⊗[A] ↥(I.map (algebraMap R A)))
      ≤ Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A ⊗[R] ↥I) := by
    rw [← e.finrank_eq]
    exact finrank_le_of_surjective _ (tensor_map_surjective
      (K := IsLocalRing.ResidueField A) (idealBaseChangeMap I A)
      (idealBaseChangeMap_surjective I A))
  refine le_trans (le_of_eq ?_) hstep
  rw [← TensorProduct.spanFinrank_top_eq_of_residueField (I.map (algebraMap R A))
    (hI.map (algebraMap R A)), Module.finrank_eq_spanFinrank_of_free]

open TensorProduct in
/-- **The conormal module of a presentation, after base change.** For a presentation with kernel
`I` and a commutative ring `K` that is an algebra over both the polynomial ring and `S`
compatibly, `K ⊗ I` and `K ⊗ (I/I²)` are isomorphic: the conormal module is `S ⊗_{R[x]} I`
(`Algebra.Extension.cotangentEquiv`), and base change composes. -/
private noncomputable def tensorKerEquivTensorCotangent
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*}
    (P : Algebra.Generators R S ι)
    (K : Type*) [CommRing K] [Algebra S K] [Algebra P.Ring K] [IsScalarTower P.Ring S K] :
    K ⊗[P.Ring] ↥P.ker ≃ₗ[K] K ⊗[S] P.toExtension.Cotangent :=
  (AlgebraTensorModule.cancelBaseChange P.Ring S K K ↥P.ker).symm.trans
    (AlgebraTensorModule.congr (LinearEquiv.refl K K) P.toExtension.cotangentEquiv)

open TensorProduct in
/-- An ideal spanned by `t` elements stays spanned by `t` elements after base change to a field. -/
private theorem finrank_tensor_span_range_le {R : Type*} [CommRing R] {t : ℕ}
    (f : Fin t → R) (K : Type*) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] ↥(Ideal.span (Set.range f))) ≤ t := by
  classical
  have hfg : (Ideal.span (Set.range f)).FG := ⟨(Set.range f).toFinset, by simp⟩
  have hsp : (Ideal.span (Set.range f)).spanFinrank ≤ t := by
    calc (Ideal.span (Set.range f)).spanFinrank
        ≤ (Set.range f).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range f)
      _ ≤ t := by
          rw [← Set.image_univ]
          calc (f '' Set.univ).ncard ≤ (Set.univ : Set (Fin t)).ncard :=
                Set.ncard_image_le Set.finite_univ
            _ = t := by simp
  calc Module.finrank K (K ⊗[R] ↥(Ideal.span (Set.range f)))
      = (⊤ : Submodule K (K ⊗[R] ↥(Ideal.span (Set.range f)))).spanFinrank :=
        Module.finrank_eq_spanFinrank_of_free
    _ ≤ (Ideal.span (Set.range f)).spanFinrank :=
        TensorProduct.spanFinrank_top_le_of_fg _ hfg
    _ ≤ t := hsp

open TensorProduct in
/-- **Base change of a free summand adds its rank.** For a `T`-module `X` whose base change to a
field `K` is finite dimensional, `dim_K (K ⊗ (X × Tᵐ)) = dim_K (K ⊗ X) + m`. -/
public theorem finrank_tensor_prod_pi {T : Type*} [CommRing T]
    {X : Type*} [AddCommGroup X] [Module T X] {m : ℕ}
    (K : Type*) [Field K] [Algebra T K] [Module.Finite K (K ⊗[T] X)] :
    Module.finrank K (K ⊗[T] (X × (Fin m → T))) = Module.finrank K (K ⊗[T] X) + m := by
  have hfin : Module.Finite K (K ⊗[T] (Fin m → T)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight T K K (Fin m)).symm
  rw [(TensorProduct.prodRight T K K X (Fin m → T)).finrank_eq, Module.finrank_prod,
    (TensorProduct.piScalarRight T K K (Fin m)).finrank_eq, Module.finrank_fin_fun]

open TensorProduct in
/-- **Cancelling free summands after base change to a field.** An isomorphism
`X ⊕ Tᵐ ≅ Y ⊕ Tⁿ` of `T`-modules gives, over a field `K` that is a `T`-algebra,
`dim_K (K ⊗ X) + m = dim_K (K ⊗ Y) + n`. -/
public theorem finrank_add_eq_of_prodPi_linearEquiv {T : Type*} [CommRing T]
    {X Y : Type*} [AddCommGroup X] [Module T X] [AddCommGroup Y] [Module T Y] {n m : ℕ}
    (K : Type*) [Field K] [Algebra T K] [Module.Finite K (K ⊗[T] X)]
    [Module.Finite K (K ⊗[T] Y)]
    (e : (X × (Fin m → T)) ≃ₗ[T] (Y × (Fin n → T))) :
    Module.finrank K (K ⊗[T] X) + m = Module.finrank K (K ⊗[T] Y) + n := by
  rw [← finrank_tensor_prod_pi (X := X) (m := m) K, ← finrank_tensor_prod_pi (X := Y) (m := n) K]
  exact (AlgebraTensorModule.congr (LinearEquiv.refl K K) e).finrank_eq

/-! ### From item (1) to item (2) -/

open TensorProduct in
/-- **The implication (1) ⇒ (2), for a presentation by `Fin n` variables.** -/
private theorem spanFinrank_ker_map_le_of_gci_away_fin
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    {n : ℕ} (P : Algebra.Generators k S (Fin n))
    (q : Ideal S) [q.IsPrime] (c : ℕ)
    (hc : (q.comap (algebraMap P.Ring S)).height = q.height + c)
    (A : Type*) [CommRing A] [Algebra P.Ring A]
    [IsLocalization.AtPrime A (q.comap (algebraMap P.Ring S))]
    {g : S} (hgq : g ∉ q)
    (hgci : IsGlobalCompleteIntersection k (Localization.Away g)) :
    Submodule.spanFinrank (P.ker.map (algebraMap P.Ring A)) ≤ c := by
  classical
  have hsurjP : Function.Surjective (algebraMap P.Ring S) := P.algebraMap_surjective
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A (q.comap (algebraMap P.Ring S))
  have hmaxA : (IsLocalRing.maximalIdeal A).comap (algebraMap P.Ring A)
      = q.comap (algebraMap P.Ring S) :=
    IsLocalization.AtPrime.under_maximalIdeal A (q.comap (algebraMap P.Ring S))
  have hzero : ∀ y : P.Ring, algebraMap P.Ring (IsLocalRing.ResidueField A) y = 0 ↔
      algebraMap P.Ring S y ∈ q := by
    intro y
    rw [IsScalarTower.algebraMap_apply P.Ring A (IsLocalRing.ResidueField A),
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff,
      ← Ideal.mem_comap (f := algebraMap P.Ring A), hmaxA, Ideal.mem_comap]
  have hψ0 : ∀ y ∈ RingHom.ker (algebraMap P.Ring S),
      algebraMap P.Ring (IsLocalRing.ResidueField A) y = 0 := by
    intro y hy
    rw [hzero, show algebraMap P.Ring S y = 0 from hy]
    exact Submodule.zero_mem _
  set eS : (P.Ring ⧸ RingHom.ker (algebraMap P.Ring S)) ≃+* S :=
    RingHom.quotientKerEquivOfSurjective hsurjP with heS
  set ψ : S →+* IsLocalRing.ResidueField A :=
    (Ideal.Quotient.lift (RingHom.ker (algebraMap P.Ring S))
      (algebraMap P.Ring (IsLocalRing.ResidueField A)) hψ0).comp eS.symm.toRingHom with hψdef
  have hψeq : ∀ x : P.Ring, ψ (algebraMap P.Ring S x)
      = algebraMap P.Ring (IsLocalRing.ResidueField A) x := by
    intro x
    have h1 : eS.symm (algebraMap P.Ring S x)
        = Ideal.Quotient.mk (RingHom.ker (algebraMap P.Ring S)) x := by
      rw [← RingHom.quotientKerEquivOfSurjective_apply_mk hsurjP x, ← heS,
        RingEquiv.symm_apply_apply]
    rw [hψdef]
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, h1]
    exact Ideal.Quotient.lift_mk _ _ _
  let : Algebra S (IsLocalRing.ResidueField A) := ψ.toAlgebra
  have : IsScalarTower P.Ring S (IsLocalRing.ResidueField A) :=
    IsScalarTower.of_algebraMap_eq fun x => (hψeq x).symm
  have hψg : IsUnit (ψ g) := by
    rw [isUnit_iff_ne_zero]
    obtain ⟨w, rfl⟩ := hsurjP g
    rw [hψeq, Ne, hzero]
    exact hgq
  have hpow : ∀ y : Submonoid.powers g, IsUnit (ψ y) := by
    rintro ⟨_, j, rfl⟩
    simpa using hψg.pow j
  let : Algebra (Localization.Away g) (IsLocalRing.ResidueField A) :=
    (IsLocalization.lift (M := Submonoid.powers g) hpow).toAlgebra
  have : IsScalarTower S (Localization.Away g) (IsLocalRing.ResidueField A) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hpow x).symm
  have hntT : Nontrivial (Localization.Away g) :=
    (algebraMap (Localization.Away g) (IsLocalRing.ResidueField A)).domain_nontrivial
  obtain ⟨m, t, f, E, htm, hdimT⟩ := hgci.resolve_left (not_subsingleton_iff_nontrivial.2 hntT)
  set β : MvPolynomial (Fin m) k →ₐ[k] Localization.Away g :=
    (E.symm.toAlgHom).comp (Ideal.Quotient.mkₐ k (Ideal.span (Set.range f))) with hβdef
  have hβsurj : Function.Surjective β :=
    E.symm.surjective.comp Ideal.Quotient.mk_surjective
  obtain ⟨Q, hQmap⟩ : ∃ Q : Algebra.Generators k (Localization.Away g) (Fin m),
      algebraMap Q.Ring (Localization.Away g)
        = (β : MvPolynomial (Fin m) k →+* Localization.Away g) :=
    ⟨Algebra.Generators.ofAlgHom β hβsurj, by
      rw [Algebra.Generators.algebraMap_eq]
      congr 1
      ext i
      simp [Algebra.Generators.ofAlgHom]⟩
  have hQker : Q.ker = Ideal.span (Set.range f) := by
    show RingHom.ker (algebraMap Q.Ring (Localization.Away g)) = _
    rw [hQmap]
    ext y
    rw [RingHom.mem_ker]
    show E.symm (Ideal.Quotient.mk (Ideal.span (Set.range f)) y) = 0 ↔ _
    rw [map_eq_zero_iff _ E.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  let : Algebra Q.Ring (IsLocalRing.ResidueField A) :=
    ((algebraMap (Localization.Away g) (IsLocalRing.ResidueField A)).comp
      (algebraMap Q.Ring (Localization.Away g))).toAlgebra
  have : IsScalarTower Q.Ring (Localization.Away g) (IsLocalRing.ResidueField A) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hPbase := (AlgebraTensorModule.cancelBaseChange S (Localization.Away g)
    (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A) P.toExtension.Cotangent).finrank_eq
  have hfinPT : Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[Localization.Away g]
        (Localization.Away g ⊗[S] P.toExtension.Cotangent)) :=
    Module.Finite.equiv ((tensorKerEquivTensorCotangent P
      (IsLocalRing.ResidueField A)).trans
      (AlgebraTensorModule.cancelBaseChange S (Localization.Away g)
        (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)
        P.toExtension.Cotangent).symm)
  have hfinQT : Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[Localization.Away g] Q.toExtension.Cotangent) :=
    Module.Finite.equiv (tensorKerEquivTensorCotangent Q
      (IsLocalRing.ResidueField A))
  obtain ⟨ε⟩ :=
    Algebra.Generators.nonempty_cotangent_baseChange_prod_linearEquiv_of_isLocalizationAway
      (T := Localization.Away g) g P Q
  have hmain : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[P.Ring] ↥P.ker) + m
      = Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A ⊗[Q.Ring] ↥Q.ker) + n := by
    rw [(tensorKerEquivTensorCotangent P _).finrank_eq,
      (tensorKerEquivTensorCotangent Q _).finrank_eq, ← hPbase]
    exact finrank_add_eq_of_prodPi_linearEquiv (IsLocalRing.ResidueField A) ε
  have hQbound : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[Q.Ring] ↥Q.ker) ≤ t := by
    rw [hQker]
    exact finrank_tensor_span_range_le f (IsLocalRing.ResidueField A)
  have hD := PrimeSpectrum.localKrullDim_add_height_comap_eq_natCard_add_height k
    (show MvPolynomial (Fin n) k →ₐ[k] S from IsScalarTower.toAlgHom k P.Ring S) hsurjP
    (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)
  have hqq : (PrimeSpectrum.comap
      (IsScalarTower.toAlgHom k P.Ring S).toRingHom (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)).asIdeal
      = q.comap (algebraMap P.Ring S) := rfl
  rw [hqq, hc, Nat.card_fin] at hD
  have hq'le : ((q.comap (algebraMap P.Ring S)).height : WithBot ℕ∞) ≤ ringKrullDim P.Ring :=
    Ideal.height_le_ringKrullDim_of_ne_top
      (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _))
  have hq'ne : (q.comap (algebraMap P.Ring S)).height ≠ ⊤ := by
    intro htop
    rw [htop, show ringKrullDim P.Ring = ringKrullDim (MvPolynomial (Fin n) k) from rfl,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at hq'le
    simp only [zero_add, Nat.card_fin] at hq'le
    have htle : (⊤ : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hq'le
    simp at htle
  have hqne : q.height ≠ ⊤ := by
    intro htop
    rw [hc, htop] at hq'ne
    simp at hq'ne
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hqne
  rw [← ha] at hD
  have hDD : TopologicalSpace.localKrullDim (PrimeSpectrum S) (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)
      + (c : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    refine add_right_cancel_coe (c := (a : ℕ∞)) (by simp) ?_
    rw [show (((a : ℕ) : ℕ∞) + (c : ℕ∞) : ℕ∞) = (((a + c : ℕ)) : ℕ∞) by push_cast; ring] at hD
    calc TopologicalSpace.localKrullDim (PrimeSpectrum S) (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)
          + (c : WithBot ℕ∞) + (((a : ℕ) : ℕ∞) : WithBot ℕ∞)
        = TopologicalSpace.localKrullDim (PrimeSpectrum S) (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)
            + ((((a + c : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
          push_cast
          ring
      _ = (n : WithBot ℕ∞) + (((a : ℕ) : ℕ∞) : WithBot ℕ∞) := by rw [hD]
  obtain ⟨hcn, hdq⟩ := natCast_le_and_eq_of_add_eq hDD
  have hlocle : TopologicalSpace.localKrullDim (PrimeSpectrum S)
      (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S) ≤ ringKrullDim (Localization.Away g) :=
    PrimeSpectrum.localKrullDim_le_ringKrullDim_of_notMem _ hgq _
  rw [hdq, hdimT] at hlocle
  have hnum : n - c ≤ m - t := by exact_mod_cast hlocle
  refine le_trans (spanFinrank_map_le_finrank_residueField_tensor (IsNoetherian.noetherian _) A) ?_
  omega

open TensorProduct in
/-- **The implication (1) ⇒ (2).**

Let `k` be a field, let `S = k[x_i]/I` be a presented `k`-algebra with finitely many variables,
let `q` be a prime of `S`, let `q'` be the corresponding prime of `k[x_i]` and let `c` be the
codimension, `height q' = height q + c`. If `S_g` is a global complete intersection over `k` for
some `g ∉ q`, then the ideal `I_{q'}` of `A = k[x_i]_{q'}` can be generated by `c` elements.

The argument is carried out over the residue field. Write `S_g = k[y_1, …, y_m]/(f_1, …, f_t)` with
`dim S_g = m - t`; this is a second presentation `Q` of `S_g`, with `Q.ker = (f_1, …, f_t)`. Let
`κ` be the residue field of `A`, that is `κ(q)`: it is an algebra over `S` because `I ⊆ q'`, and
over `S_g` because `g ∉ q` makes the image of `g` a unit. The two conormal modules agree up to free
summands, `(I/I²)_g ⊕ S_g^{⊕m} ≅ J/J² ⊕ S_g^{⊕n}` with `J = Q.ker`; base changing to `κ` turns this
into an isomorphism of `κ`-vector spaces, in which the free summands cancel numerically because the
dimension is additive: `dim_κ (κ ⊗ I/I²) + m = dim_κ (κ ⊗ J/J²) + n ≤ t + n`, the last step because
`J` is generated by `t` elements. On the other side `dim_κ (κ ⊗ I/I²)` bounds the minimal number of
generators of `I_{q'}`, by Nakayama. Finally `n = dim_q Spec S + c` and
`dim_q Spec S ≤ dim S_g = m - t`, so `t + n ≤ m + c` and the bound is `c`. -/
theorem Algebra.Generators.spanFinrank_ker_map_le_of_exists_isGlobalCompleteIntersection_away
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    {ι : Type w} [Finite ι] (P : Algebra.Generators k S ι)
    (q : Ideal S) [q.IsPrime] (c : ℕ)
    (hc : (q.comap (algebraMap P.Ring S)).height = q.height + c)
    (A : Type*) [CommRing A] [Algebra P.Ring A]
    [IsLocalization.AtPrime A (q.comap (algebraMap P.Ring S))]
    (h : ∃ g ∉ q, IsGlobalCompleteIntersection k (Localization.Away g)) :
    Submodule.spanFinrank (P.ker.map (algebraMap P.Ring A)) ≤ c := by
  obtain ⟨g, hgq, hgci⟩ := h
  set ee : Fin (Nat.card ι) ≃ ι := (Finite.equivFin ι).symm with hee
  set P' : Algebra.Generators k S (Fin (Nat.card ι)) := P.reindex ee with hP'
  set ρ : P'.Ring ≃+* P.Ring := (MvPolynomial.renameEquiv k ee).toRingEquiv with hρ
  have hmap : ∀ x : P'.Ring, algebraMap P'.Ring S x = algebraMap P.Ring S (ρ x) := by
    intro x
    rw [Algebra.Generators.algebraMap_apply, Algebra.Generators.algebraMap_apply,
      show ρ x = MvPolynomial.rename ee x from rfl, MvPolynomial.aeval_rename]
    rfl
  have hcc : ∀ I : Ideal P.Ring,
      Ideal.comap ρ I = Ideal.comap (ρ : P'.Ring →+* P.Ring) I := fun _ => rfl
  have hker' : P'.ker = P.ker.comap ρ := by
    ext x
    show algebraMap P'.Ring S x = 0 ↔ _
    rw [Ideal.mem_comap, hmap]
    rfl
  have hq'' : q.comap (algebraMap P'.Ring S)
      = (q.comap (algebraMap P.Ring S)).comap ρ := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, hmap]
  let : Algebra P'.Ring A := ((algebraMap P.Ring A).comp (ρ : P'.Ring →+* P.Ring)).toAlgebra
  have halg : ∀ x : P'.Ring, algebraMap P'.Ring A x = algebraMap P.Ring A (ρ x) := fun _ => rfl
  have hmem : ∀ x : P'.Ring, x ∈ (q.comap (algebraMap P'.Ring S)).primeCompl ↔
      ρ x ∉ q.comap (algebraMap P.Ring S) := by
    intro x
    show x ∉ q.comap (algebraMap P'.Ring S) ↔ _
    rw [hq'', Ideal.mem_comap]
  have hmono : Submonoid.map ρ (q.comap (algebraMap P'.Ring S)).primeCompl
      = (q.comap (algebraMap P.Ring S)).primeCompl := by
    ext y
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).1 hx
    · intro hy
      refine ⟨ρ.symm y, (hmem _).2 ?_, ρ.apply_symm_apply y⟩
      rw [ρ.apply_symm_apply]
      exact hy
  have : IsLocalization.AtPrime A (q.comap (algebraMap P'.Ring S)) :=
    IsLocalization.of_ringEquiv_left (K := A) ρ hmono halg
  have hc' : (q.comap (algebraMap P'.Ring S)).height = q.height + c := by
    rw [hq'', RingEquiv.height_comap ρ]
    exact hc
  have hideal : P'.ker.map (algebraMap P'.Ring A) = P.ker.map (algebraMap P.Ring A) := by
    have h1 : (algebraMap P'.Ring A) = (algebraMap P.Ring A).comp (ρ : P'.Ring →+* P.Ring) :=
      RingHom.ext halg
    rw [h1, ← Ideal.map_map, hker', hcc,
      Ideal.map_comap_of_surjective (ρ : P'.Ring →+* P.Ring) ρ.surjective]
  rw [← hideal]
  exact spanFinrank_ker_map_le_of_gci_away_fin k S P' q c hc' A hgq hgci

/-! ### The complete intersection criterion -/

/-- **The complete intersection criterion at a prime.** Let `k` be a field, let `S = k[x_i]/I` be a
presented `k`-algebra with finitely many variables, let `q` be a prime of `S`, let `q'` be the
corresponding prime of `k[x_i]` and let `c` be the codimension, `height q' = height q + c`. Write
`A = k[x_i]_{q'}` and `I_A = I_{q'}`. Then the following are equivalent:

1. there is a `g ∈ S`, `g ∉ q`, such that `S_g` is a global complete intersection over `k`;
2. the ideal `I_A` can be generated by `c` elements;
3. the conormal module `I_A/I_A²` can be generated by `c` elements over `A/I_A`;
4. the conormal module `I_A/I_A²` is a free `A/I_A`-module of rank `c`;
5. the ideal `I_A` can be generated by a regular sequence in the regular local ring `A`.

Items (3) and (4) are stated for the conormal module of `I_A` over `A/I_A`, which agrees with
`(I/I²)_q` over `S_q`: `A/I_A` is the localization `S_q` (this is
`ringKrullDim_quotient_map_ker_eq_height`), and `I_A/I_A²` is `(I/I²)_q`, localization being flat.

The closing assertion of the lemma, that any `c` elements of `I_A` generating `I_A/q'I_A` form a
regular sequence in `A`, is the second conjunct of
`Algebra.Generators.spanFinrank_ker_map_le_iff_exists_isRegular`. -/
@[stacks 00SC "Items (1)-(5) are the five entries of the `List.TFAE`, in order. The source's `c`,
defined there as `height 𝔮' - height 𝔮`, is the hypothesis `height 𝔮' = height 𝔮 + c`, the
additive form (see the module docstring); the source's parenthetical `dim_𝔮(S) = n - c` is a
consequence of it, by Stacks 00P2. Items (3) and (4) are stated for the conormal module of
`I_A = I_{𝔮'}` over `A/I_A` rather than for `(I/I²)_𝔮` over `S_𝔮`; the two agree under the
canonical identification of `A/I_A` with `S_𝔮`, localization being flat. The closing assertion of
the lemma is the second conjunct of
`Algebra.Generators.spanFinrank_ker_map_le_iff_exists_isRegular`, which carries this tag as
well."]
theorem Algebra.Generators.tfae_isGlobalCompleteIntersection_away
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    {ι : Type w} [Finite ι] (P : Algebra.Generators k S ι)
    (q : Ideal S) [q.IsPrime] (c : ℕ)
    (hc : (q.comap (algebraMap P.Ring S)).height = q.height + c)
    (A : Type*) [CommRing A] [Algebra P.Ring A]
    [IsLocalization.AtPrime A (q.comap (algebraMap P.Ring S))] :
    List.TFAE
      [∃ g ∉ q, IsGlobalCompleteIntersection k (Localization.Away g),
        Submodule.spanFinrank (P.ker.map (algebraMap P.Ring A)) ≤ c,
        (⊤ : Submodule (A ⧸ P.ker.map (algebraMap P.Ring A))
            (P.ker.map (algebraMap P.Ring A)).Cotangent).spanFinrank ≤ c,
        Module.Free (A ⧸ P.ker.map (algebraMap P.Ring A))
              (P.ker.map (algebraMap P.Ring A)).Cotangent ∧
          Module.finrank (A ⧸ P.ker.map (algebraMap P.Ring A))
            (P.ker.map (algebraMap P.Ring A)).Cotangent = c,
        ∃ rs : List A, IsRegular A rs ∧
          Ideal.ofList rs = P.ker.map (algebraMap P.Ring A)] := by
  have hrl : IsRegularLocalRing A :=
    IsRegularRing.isRegularLocalRing_of_isLocalization
      (q.comap (algebraMap P.Ring S)) A
  have hA : Module.IsMaximalCohenMacaulay A A :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay A).2
  have hdim : ringKrullDim (A ⧸ P.ker.map (algebraMap P.Ring A)) = (q.height : WithBot ℕ∞) :=
    ringKrullDim_quotient_map_ker_eq_height (algebraMap P.Ring S) P.algebraMap_surjective q A
  have hdimA : ringKrullDim A = ((q.comap (algebraMap P.Ring S)).height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height _ A
  have hI : P.ker.map (algebraMap P.Ring A) ≠ ⊤ := by
    intro htop
    rw [htop] at hdim
    have hsub : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim.symm (by simp)
  have hcA : ringKrullDim (A ⧸ P.ker.map (algebraMap P.Ring A))
      + (c : WithBot ℕ∞) = ringKrullDim A := by
    rw [hdim, hdimA, hc]
    push_cast
    rfl
  have hlocal := hA.tfae_spanFinrank_cotangent hI c hcA
  tfae_have 1 → 2 := fun hg =>
    P.spanFinrank_ker_map_le_of_exists_isGlobalCompleteIntersection_away k S q c hc A hg
  tfae_have 2 → 1 := fun hsp =>
    P.exists_isGlobalCompleteIntersection_away_of_spanFinrank_ker_map_le k S q c hc A hsp
  tfae_have 2 → 3 := (hlocal.out 1 2).mp
  tfae_have 3 → 4 := (hlocal.out 2 3).mp
  tfae_have 4 → 5 := (hlocal.out 3 4).mp
  tfae_have 5 → 2 := (hlocal.out 4 1).mp
  tfae_finish

end
