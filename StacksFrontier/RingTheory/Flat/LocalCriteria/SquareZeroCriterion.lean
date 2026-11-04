module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.PUnit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroTor
import all StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroTor

/-!
# The square-zero local criterion for flatness, and the fibre lemmas behind 00ME

The square-zero case of the local criterion and Stacks 051I
(`flat_quot_idealTwo_smul_top_of_flat_quot_and_flat_baseChange`), followed by the fibre
computations, the local homomorphism `R_𝔭 → S_𝔮` and the first auxiliary steps of Stacks 00ME.
-/

@[expose] public section

open TensorProduct

universe w

-- this proof's elaboration needs more than the default heartbeat budget
/-- The local criterion of flatness in the square-zero case: if `J ^ 2 = ⊥`, the quotient
`N ⧸ JN` is flat over `S ⧸ J`, and `J ⊗ N → N` is injective, then `N` is flat over `S`. -/
@[ega "0 10.1.3" "special case",
  ega "0 10.2.1" "c ⇒ a for J²=0",
  ega "0 10.2.2" "special case",
  ega "IV 11.2.5" "special case",
  ega "IV 11.4.1.1" "special case", sga "1 IV 5.5" "special case", sga "1 IV 5.6" "special case"]
theorem flat_of_sq_zero_local_criterion
    {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N] [Module S N]
    (J : Ideal S) (hJ : J ^ 2 = ⊥)
    (hquot : Module.Flat (S ⧸ J) (N ⧸ J • (⊤ : Submodule S N)))
    (htor : Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype))) :
    Module.Flat S N := by
  -- Stacks Tag 051C, square-zero (`n = 2`) case.
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ K
  -- `iff_lTensor_injectiveₛ` only gives `AddCommMonoid P`; upgrade to `AddCommGroup`
  -- (valid over the ring `S`) so the `AddCommGroup`-stated sub-lemmas apply.
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup S
  -- The J-filtration four-lemma chase.
  exact step3_assembly_lTensor_subtype J hJ hquot htor K

-- this proof's elaboration needs more than the default heartbeat budget
/-- The canonical `R`-linear quotient map `M → M ⧸ K•⊤` realizes `M ⧸ K•⊤` as the
base change of `M` along the quotient ring map `R → R ⧸ K`. (Concretely, the induced
`(R ⧸ K)`-linear map `(R ⧸ K) ⊗[R] M → M ⧸ K•⊤` is the canonical isomorphism
`quotTensorEquivQuotSMul`.) -/
@[ega "0 22.4.5" "partial", sga "7 VIII 2.1" "special case"]
theorem isBaseChange_mkQ_smul_top
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (K : Ideal R) :
    IsBaseChange (R ⧸ K) ((K • (⊤ : Submodule R M)).mkQ) := by
  have hsurj : Function.Surjective (algebraMap R (R ⧸ K)) := Ideal.Quotient.mk_surjective
  let e : (R ⧸ K) ⊗[R] M ≃ₗ[R ⧸ K] (M ⧸ K • (⊤ : Submodule R M)) :=
    LinearEquiv.extendScalarsOfSurjective hsurj (TensorProduct.quotTensorEquivQuotSMul M K)
  apply IsBaseChange.of_equiv e
  intro x
  change (TensorProduct.quotTensorEquivQuotSMul M K) ((1 : R ⧸ K) ⊗ₜ[R] x) = _
  rw [show (1 : R ⧸ K) = Ideal.Quotient.mk K 1 from rfl]
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  simp

-- this proof's elaboration needs more than the default heartbeat budget
/-- In `S := R ⧸ I₂`, the image `J` of `I` is square-zero, and
`(S ⧸ J)`-flatness of `(N ⧸ J•⊤)` (with `N = M ⧸ I₂•⊤`) follows from hypothesis
`h1` by base change.

**Informal proof.** Let `J = Ideal.map (Quotient.mk I₂) I` be the image of `I`
in `S = R ⧸ I₂`. There is a canonical ring isomorphism `S ⧸ J ≅ R ⧸ (I + I₂)`
(third isomorphism theorem: `(R⧸I₂)⧸((I+I₂)/I₂) ≅ R⧸(I+I₂)`), and compatibly an
`R`-linear isomorphism `N ⧸ J•⊤ ≅ M ⧸ (I + I₂)•⊤`. Now `R⧸(I+I₂) = (R⧸I)⧸ Ī₂`
where `Ī₂` is the image of `I₂` in `R⧸I`, and likewise
`M⧸(I+I₂)•⊤ ≅ (M⧸I•⊤) ⧸ Ī₂•⊤ ≅ (R⧸(I+I₂)) ⊗_{R⧸I} (M⧸I•⊤)`. Hence
`M⧸(I+I₂)•⊤` is the base change of the `(R⧸I)`-module `M⧸I•⊤` along the quotient
map `R⧸I → R⧸(I+I₂)`. Flatness is stable under base change
(`Module.Flat.baseChange`), so from `h1`
(`M⧸I•⊤` flat over `R⧸I`) we get `M⧸(I+I₂)•⊤` flat over `R⧸(I+I₂)`, i.e.
`N⧸J•⊤` flat over `S⧸J`. -/
theorem hquot_from_h1
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (h1 : Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) :
    Module.Flat
      ((R ⧸ idealTwo I R') ⧸ Ideal.map (Ideal.Quotient.mk (idealTwo I R')) I)
      ((M ⧸ (idealTwo I R') • (⊤ : Submodule R M)) ⧸
        (Ideal.map (Ideal.Quotient.mk (idealTwo I R')) I) •
          (⊤ : Submodule (R ⧸ idealTwo I R')
            (M ⧸ (idealTwo I R') • (⊤ : Submodule R M)))) := by
  -- Third-isomorphism + base change of `h1`.
  set I₂ := idealTwo I R' with hI₂
  -- Algebra/scalar-tower instances for `R⧸I → (R⧸I₂)⧸J` (Mathlib's quotient-map algebra).
  let alg : Algebra (R ⧸ I) ((R ⧸ I₂) ⧸ Ideal.map (Ideal.Quotient.mk I₂) I) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  let : Module (R ⧸ I) ((R ⧸ I₂) ⧸ Ideal.map (Ideal.Quotient.mk I₂) I) := alg.toModule
  let tower : IsScalarTower R (R ⧸ I) ((R ⧸ I₂) ⧸ Ideal.map (Ideal.Quotient.mk I₂) I) :=
    Ideal.Quotient.tower_quotient_map_quotient
  -- Base-change facts for each quotient layer.
  have hfN : IsBaseChange (R ⧸ I₂) ((I₂ • (⊤ : Submodule R M)).mkQ) :=
    isBaseChange_mkQ_smul_top I₂
  have hgN : IsBaseChange ((R ⧸ I₂) ⧸ Ideal.map (Ideal.Quotient.mk I₂) I)
      ((Ideal.map (Ideal.Quotient.mk I₂) I •
        (⊤ : Submodule (R ⧸ I₂) (M ⧸ I₂ • (⊤ : Submodule R M)))).mkQ) :=
    isBaseChange_mkQ_smul_top (Ideal.map (Ideal.Quotient.mk I₂) I)
  -- Composite `M → N → Q` is a base change along `R → (R⧸I₂)⧸J`.
  have hc := hfN.comp hgN
  -- `M → M⧸I•⊤` is a base change along `R → R⧸I`.
  have hf0 : IsBaseChange (R ⧸ I) ((I • (⊤ : Submodule R M)).mkQ) :=
    isBaseChange_mkQ_smul_top I
  -- Assemble the `(R⧸I₂)⧸J`-linear isomorphism
  --   `((R⧸I₂)⧸J) ⊗[R⧸I] (M⧸I•⊤) ≃ Q`.
  let e3 := hc.equiv
  let e2 := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I)
    ((R ⧸ I₂) ⧸ Ideal.map (Ideal.Quotient.mk I₂) I)
    ((R ⧸ I₂) ⧸ Ideal.map (Ideal.Quotient.mk I₂) I) M
  let e1 := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl ((R ⧸ I₂) ⧸ Ideal.map (Ideal.Quotient.mk I₂) I)
      ((R ⧸ I₂) ⧸ Ideal.map (Ideal.Quotient.mk I₂) I))
    (hf0.equiv.symm)
  let e := e1.trans (e2.trans e3)
  -- Flatness is stable under base change of `h1`; transport along `e`.
  have := Module.Flat.baseChange (R ⧸ I) ((R ⧸ I₂) ⧸ Ideal.map (Ideal.Quotient.mk I₂) I)
      (M ⧸ I • (⊤ : Submodule R M))
  exact Module.Flat.of_linearEquiv e.symm

/-- **Base-change injectivity helper.** If `A` is an `R`-algebra and `A ⊗[R] M` is
flat over `A`, then for any ideal `K ⊆ A`, the R-linear inclusion-tensor
`K ⊗[R] M → A ⊗[R] M` is injective. (Conjugate to the A-linear `rTensor (A⊗M) K.subtype`,
which is injective by flatness, through `cancelBaseChange`.) -/
@[sga "3 III 4.13" "partial", sga "3 VIB 11.7" "affine ideal inclusion"]
theorem rTensor_subtype_baseChange_inj
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M]
    (K : Ideal A) (hflat : Module.Flat A (A ⊗[R] M)) :
    Function.Injective
      (LinearMap.rTensor M (K.subtype.restrictScalars R)) := by
  let cb : (↥K) ⊗[A] (A ⊗[R] M) ≃ₗ[A] (↥K) ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A A (↥K) M
  have hμAinj : Function.Injective (LinearMap.rTensor (A ⊗[R] M) K.subtype) :=
    (Module.Flat.iff_rTensor_injective' (R := A) (M := A ⊗[R] M)).mp hflat K
  set L : (↥K) ⊗[A] (A ⊗[R] M) →ₗ[R] A ⊗[R] M :=
    (LinearMap.rTensor M (K.subtype.restrictScalars R)).comp (cb.toLinearMap.restrictScalars R)
    with hL
  set Rgt : (↥K) ⊗[A] (A ⊗[R] M) →ₗ[R] A ⊗[R] M :=
    ((TensorProduct.lid A (A ⊗[R] M)).toLinearMap.comp
      (LinearMap.rTensor (A ⊗[R] M) K.subtype)).restrictScalars R
    with hRgt
  have hsqt : ∀ (k : ↥K) (x : A ⊗[R] M), L (k ⊗ₜ[A] x) = Rgt (k ⊗ₜ[A] x) := by
    intro k x
    induction x using TensorProduct.induction_on with
    | zero => simp [hL, hRgt]
    | add a b ha hb => rw [tmul_add, map_add, map_add, ha, hb]
    | tmul a m =>
      simp only [hL, hRgt, LinearMap.coe_comp, LinearMap.restrictScalars_apply,
        Function.comp_apply, LinearEquiv.coe_coe, cb,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        LinearMap.rTensor_tmul, Submodule.coe_subtype, TensorProduct.lid_tmul]
      rw [TensorProduct.smul_tmul']
      congr 1
      simp only [Submodule.coe_smul, smul_eq_mul, mul_comm]
  have hLRgt : L = Rgt := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | tmul k x => exact hsqt k x
  have hRgtinj : Function.Injective Rgt := by
    rw [hRgt]
    intro p q hpq
    apply (LinearEquiv.injective (TensorProduct.lid A (A ⊗[R] M))).comp hμAinj
    simpa [LinearMap.restrictScalars_apply] using hpq
  have hLinj : Function.Injective L := hLRgt ▸ hRgtinj
  rw [hL] at hLinj
  rw [LinearMap.coe_comp] at hLinj
  exact hLinj.of_comp_right cb.surjective

/-- **`J`-killed helper.** The image ideal of `I` in an `R`-algebra `S`, when its
square vanishes, is annihilated by `I` as an `R`-module. -/
theorem killed_of_sq_bot
    {R : Type*} [CommRing R] (I : Ideal R)
    {S : Type*} [CommRing S] [Algebra R S] (K : Ideal S)
    (hmkI : ∀ i ∈ I, (algebraMap R S i) ∈ K) (hKsq : K ^ 2 = ⊥) :
    I • (⊤ : Submodule R (↥K)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro i hi k _
  rw [Submodule.mem_bot]
  apply Subtype.ext
  change (i • (k : S)) = 0
  have hval : (i • (k : S)) = (algebraMap R S i) * (k : S) := by rw [Algebra.smul_def]
  rw [hval]
  have hmem : (algebraMap R S i) * (k : S) ∈ K ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul (hmkI i hi) k.property
  rwa [hKsq, Submodule.mem_bot] at hmem

/-- **Homological core (R-linear form).** With `S = R ⧸ I₂`, `J = image of I` in
`S`, the multiplication-comparison `rTensor M (J.subtype : J →ₗ[R] S)`,
`J ⊗[R] M → S ⊗[R] M`, is injective.

This is the Stacks-051I core after the base-change
reduction below: by `cancelBaseChange` and `quotTensorEquivQuotSMul`, the original
`S`-linear `rTensor N J.subtype` (`N = M ⧸ I₂•⊤`) is conjugate to this R-linear map.
The remaining content, in two steps: route through
`M' = R'⊗[R]M`; `h2` gives the square-zero multiplication `barμ` injective, and
`h1` (`M/IM` flat over `R/I`) together with `ker(I → IR'/(IR')²) = I∩I₂`
(the definition of `idealTwo`) gives `Ψ = f ⊗_{R/I} id` injective; the square
`bar_μ₂ ∘ Ψ = ν ∘ (J.subtype ⊗ id)` then forces injectivity. -/
theorem htor_core_rTensor_inj
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (h1 : Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)))
    (h2 : Module.Flat R' (R' ⊗[R] M)) :
    Function.Injective
      (LinearMap.rTensor M
        ((Ideal.map (Ideal.Quotient.mk (idealTwo I R')) I).subtype.restrictScalars R)) := by
  set φ := algebraMap R R' with hφ
  set IR' := Ideal.map φ I with hIR
  set I2 := idealTwo I R' with hI2
  set S := R ⧸ I2 with hS
  set J : Ideal S := Ideal.map (Ideal.Quotient.mk I2) I with hJ
  set Rb := R' ⧸ IR'^2 with hRb
  set Jb : Ideal Rb := Ideal.map (algebraMap R' Rb) IR' with hJb
  -- ιR : J →ₗ[R] S (the R-linear inclusion whose rTensor we study)
  set ιR : (↥J) →ₗ[R] S := J.subtype.restrictScalars R with hιR
  -- `x ∈ I₂` exactly when `x` dies in `R' ⧸ (IR')²`.
  have hmem : ∀ x : R, algebraMap R Rb x = 0 ↔ x ∈ I2 := fun x => by
    change Ideal.Quotient.mk (IR'^2) (algebraMap R R' x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, hIR, ← Ideal.map_pow, hI2, idealTwo, Ideal.mem_comap]
  -- the image of `I` lies in `Jb`
  have hIJb : ∀ x ∈ I, algebraMap R Rb x ∈ Jb := fun x hx =>
    Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)
  -- g : S →ₗ[R] Rb, induced by φ (well-defined since φ(I₂) ⊆ (IR')²), and injective.
  have hkill2 : I2 ≤ LinearMap.ker (Algebra.linearMap R Rb) := fun x hx => (hmem x).2 hx
  set g : S →ₗ[R] Rb := Submodule.liftQ I2 (Algebra.linearMap R Rb) hkill2 with hg
  have hg_inj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hmem x).1 hs)
  -- Sbar : S →+* Rb, agreeing with g; used for membership.
  have hkillR : I2 ≤ RingHom.ker ((Ideal.Quotient.mk (IR'^2)).comp φ) := fun x hx =>
    (hmem x).2 hx
  set Sbar : S →+* Rb :=
    Ideal.Quotient.lift I2 ((Ideal.Quotient.mk (IR'^2)).comp φ)
      (fun a ha => RingHom.mem_ker.mp (hkillR ha))
    with hSbar
  have hgSbar : ∀ s : S, g s = Sbar s := by
    intro s
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
    rfl
  have hJcomap : J ≤ Ideal.comap Sbar Jb := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change Sbar (Ideal.Quotient.mk I2 x) ∈ Jb
    exact hIJb x hx
  have hfmem : ∀ j : ↥J, (g.comp ιR) j ∈ Jb := by
    intro j
    have : (g.comp ιR) j = Sbar (j : S) := by
      simp only [LinearMap.comp_apply, hιR, LinearMap.restrictScalars_apply,
        Submodule.subtype_apply, hgSbar]
    rw [this]; exact hJcomap j.property
  -- f : J →ₗ[R] Jb
  set f : (↥J) →ₗ[R] (↥Jb) := LinearMap.codRestrict (Jb.restrictScalars R) (g.comp ιR) hfmem
    with hf
  have hf_subtype : (Jb.subtype.restrictScalars R).comp f = g.comp ιR := rfl
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hg2 : g (ιR a) = g (ιR b) := by
      have hc := congrArg (Subtype.val) hab
      exact hc
    have hia : ιR a = ιR b := hg_inj hg2
    exact Subtype.ext hia
  -- killed facts
  have hJsq : J ^ 2 = ⊥ := image_I_sq_eq_bot I
  have hJkilled : I • (⊤ : Submodule R (↥J)) = ⊥ :=
    killed_of_sq_bot I J (fun i hi => Ideal.mem_map_of_mem _ hi) hJsq
  have hJbsq : Jb ^ 2 = ⊥ := by
    have h := Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk (IR'^2)) (I := IR'^2)
    rw [Ideal.mk_ker] at h
    have he : Jb ^ 2 = Ideal.map (Ideal.Quotient.mk (IR'^2)) (IR'^2) := by
      rw [hJb]; exact (Ideal.map_pow _ _ _).symm
    rw [he, h.mpr le_rfl]
  have hJbkilled : I • (⊤ : Submodule R (↥Jb)) = ⊥ := by
    refine killed_of_sq_bot I Jb (fun i hi => ?_) hJbsq
    exact hIJb i hi
  -- Ψ injective via `factB_Jkilled'` (S:=R, J:=I, N:=M)
  have hΨ : Function.Injective (LinearMap.rTensor M f) := by
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact factB_Jkilled' I h1 hJkilled hJbkilled f hf_inj
  -- barμ injective via base change + h2
  have hRbflat : Module.Flat Rb (Rb ⊗[R] M) := by
    have : Module.Flat Rb (Rb ⊗[R'] (R' ⊗[R] M)) := Module.Flat.baseChange R' Rb (R' ⊗[R] M)
    exact Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' Rb Rb M).symm
  have hbarμ : Function.Injective (LinearMap.rTensor M (Jb.subtype.restrictScalars R)) :=
    rTensor_subtype_baseChange_inj Jb hRbflat
  -- The chase: rTensor M ιR z = 0 ⟹ z = 0.
  intro z w hzw
  rw [← sub_eq_zero] at hzw ⊢
  set y := z - w with hy
  rw [← map_sub] at hzw
  -- barμ (Ψ y) = rTensor M g (rTensor M ιR y) = rTensor M g 0 = 0
  have hcomp : (Jb.subtype.restrictScalars R).comp f = g.comp ιR := hf_subtype
  have hkey : (LinearMap.rTensor M (Jb.subtype.restrictScalars R)) (LinearMap.rTensor M f
      y) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp, LinearMap.rTensor_comp,
      LinearMap.comp_apply, hzw, map_zero]
  have hΨy : LinearMap.rTensor M f y = 0 := hbarμ (by rw [hkey, map_zero])
  exact hΨ (by rw [hΨy, map_zero])

-- this proof's elaboration needs more than the default heartbeat budget
/-- The injectivity hypothesis of the local criterion, for the image of `I` in `R ⧸ I₂`
acting on `M ⧸ I₂ M`, deduced from flatness of `M ⧸ IM` over `R ⧸ I` and of `R' ⊗ M` over
`R'`. -/
theorem htor_rTensor_subtype_injective
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (h1 : Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)))
    (h2 : Module.Flat R' (R' ⊗[R] M)) :
    Function.Injective
      (LinearMap.rTensor (M ⧸ (idealTwo I R') • (⊤ : Submodule R M))
        (Ideal.map (Ideal.Quotient.mk (idealTwo I R')) I).subtype) := by
  -- Base-change reduction: conjugate the `S`-linear `rTensor N J.subtype`
  -- to the R-linear core `htor_core_rTensor_inj` via `cancelBaseChange` +
  -- `quotTensorEquivQuotSMul`.
  have Hcore := htor_core_rTensor_inj I h1 h2
  set I₂ := idealTwo I R' with hI2
  set S := R ⧸ I₂ with hS
  set N := M ⧸ I₂ • (⊤ : Submodule R M) with hN
  set J := Ideal.map (Ideal.Quotient.mk I₂) I with hJ
  have hsurj : Function.Surjective (algebraMap R S) := Ideal.Quotient.mk_surjective
  let qN : (S ⊗[R] M) ≃ₗ[S] N :=
    LinearEquiv.extendScalarsOfSurjective hsurj (TensorProduct.quotTensorEquivQuotSMul M I₂)
  let cb : (↥J) ⊗[S] (S ⊗[R] M) ≃ₗ[S] (↥J) ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (↥J) M
  let Θ : (↥J) ⊗[S] N ≃ₗ[S] (↥J) ⊗[R] M :=
    (TensorProduct.congr (LinearEquiv.refl S (↥J)) qN.symm).trans cb
  set ιR : (↥J) →ₗ[R] S := J.subtype.restrictScalars R with hιR
  let μS : (↥J) ⊗[S] N →ₗ[S] N :=
    (TensorProduct.lid S N).toLinearMap.comp (LinearMap.rTensor N J.subtype)
  have hsquare : (μS.restrictScalars R).comp (Θ.symm.toLinearMap.restrictScalars R)
      = (qN.toLinearMap.restrictScalars R).comp (LinearMap.rTensor M ιR) := by
    apply TensorProduct.ext'
    intro j m
    simp only [LinearMap.coe_comp, LinearMap.restrictScalars_apply, Function.comp_apply,
      LinearEquiv.coe_coe]
    have hΘsymm : Θ.symm (j ⊗ₜ[R] m) = j ⊗ₜ[S] qN (1 ⊗ₜ[R] m) := by
      simp only [Θ, LinearEquiv.trans_symm, LinearEquiv.trans_apply, cb,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
        TensorProduct.congr_symm, LinearEquiv.refl_symm, LinearEquiv.symm_symm,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    rw [hΘsymm]
    change (TensorProduct.lid S N) (LinearMap.rTensor N J.subtype (j ⊗ₜ[S] qN (1 ⊗ₜ[R] m)))
        = qN ((LinearMap.rTensor M ιR) (j ⊗ₜ[R] m))
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.rTensor_tmul]
    rw [← map_smul qN]
    congr 1
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  have hRHS : Function.Injective
      ((qN.toLinearMap.restrictScalars R).comp (LinearMap.rTensor M ιR)) := by
    rw [LinearMap.coe_comp]
    exact qN.injective.comp Hcore
  have hLHS : Function.Injective
      ((μS.restrictScalars R).comp (Θ.symm.toLinearMap.restrictScalars R)) := by
    rwa [hsquare]
  have hμS : Function.Injective μS := by
    have hc : Function.Injective
        ((μS.restrictScalars R) ∘ (Θ.symm.toLinearMap.restrictScalars R)) := by
      rwa [← LinearMap.coe_comp]
    exact hc.of_comp_right Θ.symm.surjective
  have hfin : Function.Injective
      ((TensorProduct.lid S N).toLinearMap.comp (LinearMap.rTensor N J.subtype)) := hμS
  rw [LinearMap.coe_comp] at hfin
  exact hfin.of_comp

/-- The Tor-vanishing / injectivity condition for
`flat_quot_idealTwo_smul_top_of_flat_quot_and_flat_baseChange`: with
`S = R ⧸ I₂`, `J = image of I`, `N = M ⧸ I₂•⊤`, the multiplication map
`J ⊗_S N → N` is injective. This is the step where hypothesis `h2` (flatness of
`R' ⊗_R M` over `R'`) is used, and where the precise definition
`I₂ = φ⁻¹(φ(I²)R')` enters.

**Informal proof (Stacks 051I core).** After passing to `S = R⧸I₂` we have
`I²·S = 0`, and `K := ker(J ⊗_S N → N) = Tor₁^S(S⧸J, N)`. We must show `K = 0`.
Set `M' = M ⊗_R R'` and `I' = I·R'`. Hypothesis `h2` says `M'` is flat over
`R'`, so the multiplication `I' ⊗_{R'} M' → M'` is injective; thus the image of
`K` in `I' ⊗_{R'} M'` is zero. Using `I' ⊗_{R'} M' = I' ⊗_R M =
I' ⊗_{R/I} (M/IM)` (base change identities), `K` maps to zero there. Finally the
inclusion `I → I'` is an injective map of `R/I`-modules and `M/IM` is flat over
`R/I` (hypothesis `h1`), so `I ⊗_{R/I} (M/IM) → I' ⊗_{R/I} (M/IM)` is injective;
combined with the previous step this forces `K = 0` already in
`I ⊗_R M = I ⊗_{R/I} (M/IM) = J ⊗_S N`. The definition
`I₂ = φ⁻¹(φ(I²)R')` is exactly what makes `φ : R/I₂ → R'/φ(I)²R'` injective so
that the base-change comparison `I' ⊗_R M ≅ I' ⊗_{R'} M'` is faithful. -/
theorem htor_from_base_change
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (h1 : Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)))
    (h2 : Module.Flat R' (R' ⊗[R] M)) :
    Function.Injective
      (TensorProduct.lift
        ((LinearMap.lsmul (R ⧸ idealTwo I R')
            (M ⧸ (idealTwo I R') • (⊤ : Submodule R M))).comp
          (Ideal.map (Ideal.Quotient.mk (idealTwo I R')) I).subtype)) := by
  set S := R ⧸ idealTwo I R' with hS
  set N := M ⧸ (idealTwo I R') • (⊤ : Submodule R M) with hN
  set J := Ideal.map (Ideal.Quotient.mk (idealTwo I R')) I with hJ
  -- The `lift`-form is `lid ∘ rTensor`; reduce to `rTensor`-of-inclusion injectivity.
  have hgoal : (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype))
      = (TensorProduct.lid S N).toLinearMap.comp (LinearMap.rTensor N J.subtype) := by
    apply TensorProduct.ext'; intro j n; simp
  rw [hgoal, LinearMap.coe_comp]
  exact (TensorProduct.lid S N).injective.comp (htor_rTensor_subtype_injective I h1 h2)

/-- **Stacks Tag 051I, Lemma 10.101.4.** Wires the square-zero local criterion
(`flat_of_sq_zero_local_criterion`) to the two base-change inputs
(`hquot_from_h1`, `htor_from_base_change`), using that the image of `I` in
`R ⧸ I₂` is square-zero (`image_I_sq_eq_bot`). -/
@[stacks 051I]
theorem flat_quot_idealTwo_smul_top_of_flat_quot_and_flat_baseChange
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (h1 : Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)))
    (h2 : Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat (R ⧸ idealTwo I R')
      (M ⧸ (idealTwo I R') • (⊤ : Submodule R M)) :=
  flat_of_sq_zero_local_criterion
    (Ideal.map (Ideal.Quotient.mk (idealTwo I R')) I)
    (image_I_sq_eq_bot I)
    (hquot_from_h1 I h1)
    (htor_from_base_change I h1 h2)

end

section

universe u v w

@[expose] public section

/-!
# Criteria for flatness over a Noetherian local base

Let `R → S` be a local homomorphism of local rings, let `𝔪` be the maximal ideal of `R` and let
`M` be a module which is finite over `S`. This file collects the criteria that test a property of
`M` over `R` on the fibre of `M` over the residue field of `R`, in the Noetherian local setting.

The engine is the first result below: for `M` flat over `R`, a map `u : N → M` of `R`-modules out
of a finite `S`-module `N` is injective as soon as its fibre `ū : N/𝔪N → M/𝔪M` is, and then the
cokernel `M/u(N)` is again flat over `R`. Everything else in the file is obtained from it by
choosing `u`: multiplication by an element of `S` gives the lifting of a nonzerodivisor, and then
of a regular sequence, from the fibre ring `S/𝔪S` to `S`, together with the flatness of the
quotients; a map from a free module gives freeness of `M` over `S` and flatness of `S` over `R`;
and an iteration along a complex gives the lifting of exactness.

The last two results have a different flavour. Over a local ring, the vanishing of `Tor₁` against
the residue field propagates to every module of finite length. And over an arbitrary ring, for `f`
a nonzerodivisor on `A` and on `M`, flatness of `M` is glued from flatness of `M_f` over `A_f` and
flatness of `M/fM` over `A/fA`.

## Main results

* `injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing`
  (00ME): injectivity of `u` and flatness of `M/u(N)` from injectivity of the fibre `ū`.
* 00MF, `Module.Flat`.`mem_nonZeroDivisors_and_flat_quotient_span_singleton_of_mem_nonZeroDivisors`
  `_maximalIdeal`: a nonzerodivisor of `S/𝔪S` lifts to one of `S`, with flat quotient.
* `Module.Flat.isRegular_and_flat_quotient_ofList_take_of_isRegular_maximalIdeal` (00MG): the same
  for a regular sequence, with all partial quotients flat.
* `Module.Flat.free_and_flat_of_free_maximalIdeal` (00MH): `M` free over `S` and `S` flat over `R`,
  from freeness of the fibre `M/𝔪M` over `S/𝔪S`.
* `Module.Flat.exactAt_and_flat_cokernel_of_exactAt_maximalIdeal` (00MI): exactness of a finite
  complex of finite `S`-modules, and flatness of its cokernel, from exactness of its fibre.
* `IsLocalRing.isZero_Tor'_one_of_isFiniteLength` (00MJ): `Tor₁(κ, M) = 0` forces `Tor₁(N, M) = 0`
  for every finite length `N`.
* `Module.flat_and_faithfullyFlat_of_flat_away_of_flat_quotSMulTop` (0H7N): flatness of `M` over
  `A` from flatness of `M_f` over `A_f` and of `M/fM` over `A/fA`, for `f` a nonzerodivisor.

## Implementation notes

Fibres are quotients rather than tensor products: `N/𝔪N` is `N ⧸ 𝔪 • (⊤ : Submodule R N)` and the
fibre ring is `S ⧸ Ideal.map (algebraMap R S) 𝔪`. The map `ū` is the canonical `Submodule.mapQ` of
`u`. `Tor` appears only in 00MJ, where it is `CategoryTheory.Tor'`, the derived functor in the
*first* variable, because it is the residue field that gets resolved.

Each result is proved in a private namespace `Stacks<tag>` holding the auxiliary constructions,
and is then stated in the library's own namespace.

## References

Stacks Project, Section 10.99 "Criteria for flatness": Lemma 10.99.1 (tag 00ME), Lemma 10.99.2
(tag 00MF), Lemma 10.99.3 (tag 00MG), Lemma 10.99.4 (tag 00MH), Lemma 10.99.5 (tag 00MI),
Lemma 10.99.6 (tag 00MJ) and Lemma 10.99.15 (tag 0H7N).
-/


/-! ### Fibres over the base, computed over `R` or over `S` -/

section

namespace Module.Flat

/-- For a module with compatible `R`- and `S`-actions, the `S`-submodule `(IS)M` and the
`R`-submodule `IM` have the same elements; this is `Ideal.smul_restrictScalars` at `⊤`. -/
public lemma mem_map_smul_top_iff {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (I : Ideal R) (x : M) :
    x ∈ (I.map (algebraMap R S)) • (⊤ : Submodule S M) ↔ x ∈ I • (⊤ : Submodule R M) := by
  rw [← Submodule.restrictScalars_mem R ((I.map (algebraMap R S)) • (⊤ : Submodule S M)) x,
    Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

end Module.Flat

namespace TensorProduct

variable {A : Type*} [CommRing A] (J : Ideal A) {X : Type*} [AddCommGroup X] [Module A X]

/-- Every element of `(A/J) ⊗[A] X` is of the form `1 ⊗ y`. -/
public theorem exists_one_tmul (t : (A ⧸ J) ⊗[A] X) : ∃ y : X, t = 1 ⊗ₜ[A] y := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule A X))
    (quotTensorEquivQuotSMul X J t)
  exact ⟨y, by rw [← quotTensorEquivQuotSMul_symm_mk J y, hy, LinearEquiv.symm_apply_apply]⟩

/-- `1 ⊗ y` vanishes in `(A/J) ⊗[A] X` exactly when `y` lies in `JX`. -/
public theorem one_tmul_eq_zero_iff_mem_smul_top (y : X) :
    (1 : A ⧸ J) ⊗ₜ[A] y = 0 ↔ y ∈ J • (⊤ : Submodule A X) := by
  rw [← Submodule.Quotient.mk_eq_zero, ← quotTensorEquivQuotSMul_mk_one_tmul J y,
    LinearEquiv.map_eq_zero_iff]

end TensorProduct

end

/-! ### The local homomorphism `R_𝔭 → S_𝔮` -/

section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The canonical local homomorphism `R_𝔭 → S_𝔮`, for `𝔭 = R ∩ 𝔮`, as an algebra structure. -/
@[instance_reducible]
public noncomputable def algebraLocalizationAtPrimeUnder (q : Ideal S) [q.IsPrime] :
    Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
  (Localization.localRingHom (q.under R) q (algebraMap R S) rfl).toAlgebra

attribute [local instance] algebraLocalizationAtPrimeUnder

/-- `R → S_𝔮` factors through `R_𝔭`, for `𝔭 = R ∩ 𝔮`. -/
public theorem isScalarTower_localizationAtPrimeUnder (q : Ideal S) [q.IsPrime] :
    IsScalarTower R (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime q)]
    exact (Localization.localRingHom_to_map (q.under R) q (algebraMap R S) rfl x).symm

attribute [local instance] isScalarTower_localizationAtPrimeUnder

/-- `R_𝔭 → S_𝔮` is a local homomorphism. -/
public theorem isLocalHom_algebraMap_localizationAtPrimeUnder (q : Ideal S) [q.IsPrime] :
    IsLocalHom (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) :=
  Localization.isLocalHom_localRingHom (q.under R) q (algebraMap R S) rfl

attribute [local instance] isLocalHom_algebraMap_localizationAtPrimeUnder

end Ideal

end

section

namespace Ideal

/-- **The fibre ring is the reduction of `S_𝔮` modulo the maximal ideal of `R_𝔭`:** the extension
of `𝔪_{R_𝔭}` along `R_𝔭 → S_𝔮` is the extension of `𝔭 = R ∩ 𝔮` along `R → S_𝔮`.

Stated for an arbitrary algebra structure on `S_𝔮` over `R_𝔭` making `R → R_𝔭 → S_𝔮` a tower, so
that it applies both to the canonical `Ideal.algebraLocalizationAtPrimeUnder` and to any other
such structure. -/
public theorem map_maximalIdeal_eq_map_under {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime]
    [Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q)]
    [IsScalarTower R (Localization.AtPrime (q.under R)) (Localization.AtPrime q)] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).map
        (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) =
      (q.under R).map (algebraMap R (Localization.AtPrime q)) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (q.under R) (Localization.AtPrime (q.under R)),
    Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- If `B ⧸ I` is flat over `R`, then `I` meets the extension of an ideal `m` of `R` in exactly
`mB · I`. -/
public theorem inf_map_eq_smul_of_flat_quotient
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal B) [Module.Flat R (B ⧸ I)] (m : Ideal R) :
    I ⊓ m.map (algebraMap R B) = m.map (algebraMap R B) • I := by
  let f : B →ₐ[R] B ⧸ I := IsScalarTower.toAlgHom R B (B ⧸ I)
  have hker : LinearMap.ker f.toLinearMap = I.restrictScalars R := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  apply Submodule.restrictScalars_injective R
  rw [Ideal.smul_restrictScalars, ← hker,
    ← LinearMap.ker_inf_smul_top_eq_smul_of_flat m f.toLinearMap Ideal.Quotient.mk_surjective,
    hker, Ideal.smul_top_eq_map]
  rfl

/-- **Nakayama for a flat quotient.** A subideal `J` of a finitely generated ideal `I` which
together with the extension of a Jacobson-small ideal `m` of the base covers `I` is all of `I`. -/
@[sga "3 X 4.5" "partial"]
public theorem eq_of_le_sup_map_of_flat_quotient
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {I J : Ideal B} (hI : I.FG) (hJI : J ≤ I) (m : Ideal R)
    (hm : m.map (algebraMap R B) ≤ (⊥ : Ideal B).jacobson)
    [Module.Flat R (B ⧸ I)] (h : I ≤ J ⊔ m.map (algebraMap R B)) : I = J := by
  refine le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot hI hm ?_) hJI
  rw [← inf_map_eq_smul_of_flat_quotient I m]
  intro x hx
  obtain ⟨y, hy, z, hz, hsum⟩ := Submodule.mem_sup.mp (h hx)
  refine Submodule.mem_sup.mpr ⟨y, hy, z, ⟨?_, hz⟩, hsum⟩
  have hz' : x - y = z := by rw [← hsum]; abel
  rw [← hz']
  exact I.sub_mem hx (hJI hy)

end Ideal

end

/-! ### Stacks 00ME -/

section

open Function TensorProduct IsLocalRing

namespace Stacks.Flatness.LocalCriterion

section SmulMap

variable {R Y Z X W : Type*} [CommRing R] [AddCommGroup Y] [Module R Y] [AddCommGroup Z]
  [Module R Z] [AddCommGroup X] [Module R X] [AddCommGroup W] [Module R W]

/-- The canonical map `Y ⊗[R] X → X`, `y ⊗ x ↦ f y • x`, attached to `f : Y →ₗ[R] R`. -/
private noncomputable def smulMap (f : Y →ₗ[R] R) (X : Type*) [AddCommGroup X] [Module R X] :
    Y ⊗[R] X →ₗ[R] X :=
  (TensorProduct.lid R X).toLinearMap ∘ₗ f.rTensor X

private lemma smulMap_tmul (f : Y →ₗ[R] R) (y : Y) (x : X) : smulMap f X (y ⊗ₜ[R] x) = f y • x :=
  rfl

private lemma smulMap_comp_rTensor (f : Y →ₗ[R] R) (g : Z →ₗ[R] Y) :
    smulMap f X ∘ₗ g.rTensor X = smulMap (f ∘ₗ g) X :=
  TensorProduct.ext' fun z x => by simp [smulMap_tmul]

private lemma smulMap_rTensor (f : Y →ₗ[R] R) (g : Z →ₗ[R] Y) (t : Z ⊗[R] X) :
    smulMap f X (g.rTensor X t) = smulMap (f ∘ₗ g) X t :=
  LinearMap.congr_fun (smulMap_comp_rTensor f g) t

private lemma smulMap_lTensor (f : Y →ₗ[R] R) (g : X →ₗ[R] W) (t : Y ⊗[R] X) :
    smulMap f W (g.lTensor Y t) = g (smulMap f X t) :=
  LinearMap.congr_fun
    (TensorProduct.ext' fun y x => by simp [smulMap_tmul] :
      smulMap f W ∘ₗ g.lTensor Y = g ∘ₗ smulMap f X) t

private lemma range_smulMap (f : Y →ₗ[R] R) :
    LinearMap.range (smulMap f X) = LinearMap.range f • (⊤ : Submodule R X) := by
  conv_lhs => rw [← LinearMap.subtype_comp_rangeRestrict f]
  rw [← smulMap_comp_rTensor, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.2 (LinearMap.rTensor_surjective X f.surjective_rangeRestrict))]
  exact Ideal.subtype_rTensor_range X (LinearMap.range f)

/-- An element of `X` lies in `JX` exactly when it is `smulMap J.subtype X` of a tensor. -/
private lemma mem_smul_top_iff_exists_smulMap (J : Ideal R) (x : X) :
    x ∈ J • (⊤ : Submodule R X) ↔ ∃ t, smulMap J.subtype X t = x := by
  rw [← LinearMap.mem_range, range_smulMap, Submodule.range_subtype]

/-- The image of `J' ⊗ X → Q ⊗ X → X`, for `J' = J ∩ Q` viewed inside `Q`, is `JX`. -/
private lemma range_smulMap_comp_subtype_comap {J Q : Ideal R} (hJQ : J ≤ Q) :
    LinearMap.range
        (smulMap (Q.subtype ∘ₗ (Submodule.comap Q.subtype (J : Submodule R R)).subtype) X)
      = J • (⊤ : Submodule R X) := by
  rw [range_smulMap, LinearMap.range_comp, Submodule.range_subtype, Submodule.map_comap_eq,
    Submodule.range_subtype, inf_eq_right.2 hJQ]

private lemma injective_smulMap_iff (f : Y →ₗ[R] R) :
    Injective (smulMap f X) ↔ Injective (f.rTensor X) :=
  (TensorProduct.lid R X).injective.of_comp_iff _

private lemma injective_smulMap [Module.Flat R X] (J : Ideal R) :
    Injective (smulMap J.subtype X) :=
  (injective_smulMap_iff _).2 (Module.Flat.iff_rTensor_injective'.1 ‹Module.Flat R X› J)

end SmulMap

section Step

variable {R N M V : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup V] [Module R V]

/-- Over a field the injection `ū : k ⊗ N → k ⊗ M` splits: for `𝔪` maximal, an injective
`R/𝔪 ⊗ u` has a linear left inverse. -/
private lemma exists_leftInverse_lTensor_residue {𝔪 : Ideal R} [𝔪.IsMaximal] (u : N →ₗ[R] M)
    (hu : Injective (u.lTensor (R ⧸ 𝔪))) :
    ∃ g : (R ⧸ 𝔪) ⊗[R] M →ₗ[R] (R ⧸ 𝔪) ⊗[R] N, g ∘ₗ u.lTensor (R ⧸ 𝔪) = LinearMap.id := by
  let _i : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hbc : (LinearMap.baseChange (R ⧸ 𝔪) u).restrictScalars R = u.lTensor (R ⧸ 𝔪) :=
    TensorProduct.ext' fun a n => by simp
  obtain ⟨g, hg⟩ := (LinearMap.baseChange (R ⧸ 𝔪) u).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 fun a b hab => hu (by rwa [← hbc]))
  refine ⟨g.restrictScalars R, LinearMap.ext fun z => ?_⟩
  have hz : (u.lTensor (R ⧸ 𝔪)) z = LinearMap.baseChange (R ⧸ 𝔪) u z := by rw [← hbc]; rfl
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hz, LinearMap.id_apply]
    using LinearMap.congr_fun hg z

/-- If `𝔪` kills `V` then `V ⊗ N → V ⊗ (R/𝔪 ⊗ N)` is injective: the kernel of `N → R/𝔪 ⊗ N` is
`𝔪N`, and every tensor `v ⊗ y` with `y ∈ 𝔪N` vanishes. -/
private lemma injective_lTensor_mk_of_smul_top_eq_bot {𝔪 : Ideal R}
    (hV : 𝔪 • (⊤ : Submodule R V) = ⊥) (N : Type*) [AddCommGroup N] [Module R N] :
    Injective ((TensorProduct.mk R (R ⧸ 𝔪) N 1).lTensor V) := by
  have hVN : ∀ (v : V) (y : N), y ∈ 𝔪 • (⊤ : Submodule R N) → v ⊗ₜ[R] y = 0 := by
    intro v y hy
    refine Submodule.smul_induction_on (p := fun z => v ⊗ₜ[R] z = (0 : V ⊗[R] N)) hy ?_ ?_
    · intro m hm y' _
      have hmv : m • v = 0 := by
        have := Submodule.smul_mem_smul (r := m) (n := v) hm Submodule.mem_top
        rwa [hV, Submodule.mem_bot] at this
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', hmv, TensorProduct.zero_tmul]
    · intro y₁ y₂ h₁ h₂
      rw [TensorProduct.tmul_add, h₁, h₂, add_zero]
  have hzero : ∀ w : V ⊗[R] ↥(𝔪 • (⊤ : Submodule R N)),
      ((𝔪 • (⊤ : Submodule R N)).subtype.lTensor V) w = 0 := by
    intro w
    induction w with
    | zero => simp
    | tmul v y => simpa using hVN v y.1 y.2
    | add a b ha hb => simp [ha, hb]
  rw [injective_iff_map_eq_zero]
  intro s hs
  have h1 : ((𝔪 • (⊤ : Submodule R N)).mkQ.lTensor V) s = 0 := by
    rw [← TensorProduct.quotTensorEquivQuotSMul_comp_mk (M := N) 𝔪, LinearMap.lTensor_comp,
      LinearMap.comp_apply, hs, map_zero]
  obtain ⟨w, hw⟩ := (lTensor_exact V (LinearMap.exact_subtype_mkQ _)
    (Submodule.mkQ_surjective _) s).1 h1
  rw [← hw, hzero w]

/-- The inductive step of Stacks 00ME. Let `𝔪` be a maximal ideal of `R`, let `M` be flat and let
`u : N → M` be injective on the fibre over `R/𝔪`. If `J ≤ Q` are ideals with `𝔪Q ≤ J`, then
`u⁻¹(JM) ∩ QN ⊆ JN`. -/
private theorem mem_smul_top_of_le_of_mul_le {𝔪 : Ideal R} [𝔪.IsMaximal] [Module.Flat R M]
    (u : N →ₗ[R] M) (hu : Injective (u.lTensor (R ⧸ 𝔪)))
    {J Q : Ideal R} (hJQ : J ≤ Q) (hmQ : 𝔪 * Q ≤ J)
    {x : N} (hxQ : x ∈ Q • (⊤ : Submodule R N)) (hux : u x ∈ J • (⊤ : Submodule R M)) :
    x ∈ J • (⊤ : Submodule R N) := by
  obtain ⟨g, hg⟩ := exists_leftInverse_lTensor_residue u hu
  set J' : Submodule R Q := Submodule.comap Q.subtype (J : Submodule R R)
  -- `𝔪` kills `Q/J`, because `𝔪Q ≤ J`.
  have hV : 𝔪 • (⊤ : Submodule R (↥Q ⧸ J')) = ⊥ := by
    refine le_bot_iff.1 (Submodule.smul_le.2 fun m hm v _ => ?_)
    obtain ⟨q, rfl⟩ := J'.mkQ_surjective v
    rw [Submodule.mem_bot, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmQ (Ideal.mul_mem_mul hm q.2)
  -- Lift `x` to `t ∈ Q ⊗ N`.
  obtain ⟨t, ht⟩ := (mem_smul_top_iff_exists_smulMap Q x).1 hxQ
  -- `Q ⊗ u` sends `t` into the image of `J ⊗ M`, by flatness of `M`.
  obtain ⟨w, hwm⟩ : ∃ w, (J'.subtype.rTensor M) w = (u.lTensor ↥Q) t := by
    obtain ⟨w, hw⟩ : u x ∈ LinearMap.range (smulMap (Q.subtype ∘ₗ J'.subtype) M) := by
      rwa [range_smulMap_comp_subtype_comap hJQ]
    exact ⟨w, injective_smulMap Q (by rw [smulMap_rTensor, hw, ← ht, smulMap_lTensor])⟩
  -- Hence `t` dies in `(Q/J) ⊗ M`, so also in `(Q/J) ⊗ N`, because `R/𝔪 ⊗ u` splits.
  have hzero : (u.lTensor (↥Q ⧸ J')) ((J'.mkQ.rTensor N) t) = 0 := by
    have hcomm : (J'.mkQ.rTensor M) ∘ₗ (u.lTensor ↥Q)
        = (u.lTensor (↥Q ⧸ J')) ∘ₗ (J'.mkQ.rTensor N) :=
      TensorProduct.ext' fun q n => by simp
    have h := LinearMap.congr_fun hcomm t
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hwm, ← LinearMap.comp_apply,
      ← LinearMap.rTensor_comp, (LinearMap.exact_subtype_mkQ J').linearMap_comp_eq_zero] at h
    simpa using h.symm
  have hs0 : (J'.mkQ.rTensor N) t = 0 := by
    refine (injective_iff_map_eq_zero _).1
      (injective_lTensor_mk_of_smul_top_eq_bot hV N) _ ?_
    have hcomm2 : (g.lTensor (↥Q ⧸ J')) ∘ₗ ((TensorProduct.mk R (R ⧸ 𝔪) M 1).lTensor (↥Q ⧸ J'))
          ∘ₗ (u.lTensor (↥Q ⧸ J'))
        = (TensorProduct.mk R (R ⧸ 𝔪) N 1).lTensor (↥Q ⧸ J') := by
      rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp]
      congr 1
      have h3 : (TensorProduct.mk R (R ⧸ 𝔪) M 1) ∘ₗ u
          = (u.lTensor (R ⧸ 𝔪)) ∘ₗ (TensorProduct.mk R (R ⧸ 𝔪) N 1) :=
        LinearMap.ext fun n => by simp
      rw [h3, ← LinearMap.comp_assoc, hg, LinearMap.id_comp]
    rw [← hcomm2]
    simp [hzero]
  -- So `t` comes from `J ⊗ N`, whence `x ∈ JN`.
  obtain ⟨v, hv⟩ := (rTensor_exact N (LinearMap.exact_subtype_mkQ J')
    (Submodule.mkQ_surjective _) t).1 hs0
  rw [← ht, ← hv, smulMap_rTensor, ← range_smulMap_comp_subtype_comap (X := N) hJQ]
  exact LinearMap.mem_range_self _ _

/-- Iterating the step along the filtration by `𝔪ⁿ + I`: `u⁻¹((𝔪ⁿ + I)M) ⊆ (𝔪ⁿ + I)N`. -/
private lemma comap_smul_top_pow_add_le {𝔪 : Ideal R} [𝔪.IsMaximal] [Module.Flat R M]
    (u : N →ₗ[R] M) (hu : Injective (u.lTensor (R ⧸ 𝔪))) (I : Ideal R) (n : ℕ) :
    ((𝔪 ^ n + I) • (⊤ : Submodule R M)).comap u ≤ (𝔪 ^ n + I) • (⊤ : Submodule R N) := by
  induction n with
  | zero =>
      simp only [pow_zero, Ideal.one_eq_top, Ideal.add_eq_sup, top_sup_eq, Submodule.top_smul]
      exact le_top
  | succ n ih =>
      intro y hy
      rw [Submodule.mem_comap] at hy
      have hJQ : 𝔪 ^ (n + 1) + I ≤ 𝔪 ^ n + I :=
        sup_le_sup_right (Ideal.pow_le_pow_right (Nat.le_succ n)) I
      refine mem_smul_top_of_le_of_mul_le u hu hJQ ?_
        (ih (Submodule.smul_mono_left hJQ hy)) hy
      rw [mul_add]
      exact sup_le_sup (le_of_eq (pow_succ' 𝔪 n).symm) Ideal.mul_le_right

/-- If `u⁻¹(IM) ⊆ IN` for every ideal `I`, then `I ⊗ (M/u(N)) → M/u(N)` is injective for every
`I`, so the cokernel of `u` is flat. -/
private lemma flat_quotient_range_of_comap_smul_top_le [Module.Flat R M] (u : N →ₗ[R] M)
    (h : ∀ I : Ideal R, (I • (⊤ : Submodule R M)).comap u ≤ I • (⊤ : Submodule R N)) :
    Module.Flat R (M ⧸ LinearMap.range u) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  rw [← injective_smulMap_iff, injective_iff_map_eq_zero]
  intro ξ hξ
  obtain ⟨η, hη⟩ :=
    (LinearMap.range u).mkQ.lTensor_surjective ↥I (Submodule.mkQ_surjective _) ξ
  have h1 : (LinearMap.range u).mkQ (smulMap I.subtype M η) = 0 := by
    rw [← smulMap_lTensor, hη, hξ]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨y, hy⟩ := h1
  obtain ⟨θ, hθ⟩ := (mem_smul_top_iff_exists_smulMap I y).1
    (h I ((mem_smul_top_iff_exists_smulMap I (u y)).2 ⟨η, hy.symm⟩))
  have h3 : (u.lTensor ↥I) θ = η := injective_smulMap I (by rw [smulMap_lTensor, hθ, hy])
  rw [← hη, ← h3, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    (u.exact_map_mkQ_range).linearMap_comp_eq_zero]
  simp

end Step

end Stacks.Flatness.LocalCriterion

end

end

end
