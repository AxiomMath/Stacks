module

public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Tor.Flatness
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Flat.TorCriterion.NilpotentIdeal
import all StacksFrontier.RingTheory.Flat.TorCriterion.Tor1Vanishing
import all StacksFrontier.RingTheory.Flat.TorCriterion.NilpotentIdeal

/-!
# Flatness along a finite generating family of an ideal

Let `A` be a ring, `M` an `A`-module and `I = (f₁, …, f_r)` an ideal of `A` with a finite chosen
family of generators. If each `M_{f_i}` is flat over `A_{f_i}`, if `M/IM` is flat over `A/I`, and
if `Tor_n^A(A/I, M) = 0` for `n = 1, …, r + 1`, then `M` is flat over `A`; and the same with
"flat" replaced by "faithfully flat".

For the second statement, write `Tor_n(K, M)` for `Tor_n^A(K, M)`. Flatness of `M/IM` over `A/I`
together with the case `n = 1` of the hypothesis gives the vanishing of `Tor_1(K, M)` for every
`A`-module `K` annihilated by `I`; presenting such a `K` as a quotient of a direct sum of copies of
`A/I` and running the long exact sequence of Tor propagates this to `Tor_n(K, M) = 0` for
`n = 1, …, r + 1`. The generators are then removed one at a time: if `Tor_n(K, M) = 0` for every
`K` annihilated by `f₁, …, f_j` and every `n ≤ j + 1`, then for `K` annihilated by
`f₁, …, f_{j-1}` the two short exact sequences `0 → K[f_j] → K → f_j K → 0` and
`0 → f_j K → K → K / f_j K → 0` show that `f_j` acts injectively on `Tor_n(K, M)` for `n ≤ j`, so
that module vanishes as soon as it does after inverting `f_j`, where it vanishes by the flatness
of `M_{f_j}`. A descending induction on `j` reaches `j = 0`, that is `Tor_1(K, M) = 0` for every
`A`-module `K`, which is flatness.

## Main results

* `Stacks.Flatness.AwayTorCriterion.solution`,
  `Module.flat_and_faithfullyFlat_of_isLocalized_away_of_isZero_Tor'`: the criterion along a
  generating family, for flatness and for faithful flatness.

## Implementation notes

`Tor1Vanishes R N M` resolves the second variable, as `CategoryTheory.Tor` does. The criterion
along a generating family states its hypothesis with `CategoryTheory.Tor'`, which resolves the
first variable, as `Tor_n^A(A/I, M)`; the two agree by the balancing isomorphism `Tor_iso_Tor'`.
The flat and the faithfully flat statements are the components `.1` and `.2` of one conjunction.
The generators are a family `f : ι → A` indexed by a finite type with
`Ideal.span (Set.range f) = I`, the number `r` of generators is `Nat.card ι`, and no hypothesis
`r ≥ 1` is needed: for `ι` empty, `I = ⊥`. The localizations are given abstractly, by
`IsLocalization.Away (f i) (Af i)` and `IsLocalizedModule.Away (f i) (g i)`, and the quotient
`M/IM` is `M ⧸ (I • ⊤ : Submodule A M)` with its `A ⧸ I`-module structure.

The descending induction runs over an arbitrary `Finset` `s` of indices: the statement is that
`Tor_n(K, M) = 0` whenever `K` is annihilated by `f i` for all `i ∈ s` and `1 ≤ n ≤ s.card + 1`,
and the induction is on the cardinality of the complement of `s`.

## References

* [Stacks Project, Tag 0H7P](https://stacks.math.columbia.edu/tag/0H7P)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M]

@[expose] public section


namespace Stacks.Flatness.AwayTorCriterion

open CategoryTheory Limits TensorProduct Tor1VanishesAux

/-- `Tor_n^A(K, M) = 0`, with the *second* variable resolved: the degree-`n` value of the
`Tor` bifunctor of `ModuleCat A` is a zero object. -/
private abbrev TorVanishes (A : Type u) [CommRing A] (n : ℕ) (K M : Type u)
    [AddCommGroup K] [Module A K] [AddCommGroup M] [Module A M] : Prop :=
  IsZero (((Tor (ModuleCat.{u} A) n).obj (ModuleCat.of A K)).obj (ModuleCat.of A M))

/-- The underlying module of `Tor_n^A(K, M)`. -/
private noncomputable abbrev TorObj (A : Type u) [CommRing A] (n : ℕ) (K M : Type u)
    [AddCommGroup K] [Module A K] [AddCommGroup M] [Module A M] : ModuleCat.{u} A :=
  ((Tor (ModuleCat.{u} A) n).obj (ModuleCat.of A K)).obj (ModuleCat.of A M)

/-- Resolving the first variable or the second gives the same vanishing statement. -/
private theorem torVanishes_iff_isZero_Tor' (A : Type u) [CommRing A] (n : ℕ) (K M : Type u)
    [AddCommGroup K] [Module A K] [AddCommGroup M] [Module A M] :
    TorVanishes A n K M ↔
      IsZero (((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A K)).obj (ModuleCat.of A M)) :=
  Iso.isZero_iff (((Tor_iso_Tor' A n).app (ModuleCat.of A K)).app (ModuleCat.of A M))

/-- A module on which `a` acts injectively and every element of which is killed by a power of `a`
is zero. -/
private theorem subsingleton_of_injective_smul_of_exists_pow_smul_eq_zero
    {A : Type u} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N] {a : A}
    (hinj : Function.Injective fun x : N => a • x)
    (htors : ∀ x : N, ∃ m : ℕ, a ^ m • x = 0) : Subsingleton N := by
  have key : ∀ (m : ℕ) (x : N), a ^ m • x = 0 → x = 0 := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      refine ih x (hinj ?_)
      change a • a ^ k • x = a • 0
      rw [smul_zero, smul_smul, ← pow_succ']
      exact hx
  refine ⟨fun x y => ?_⟩
  obtain ⟨m, hm⟩ := htors (x - y)
  exact sub_eq_zero.1 (key m _ hm)

/-- A module is annihilated by `I` exactly when each element of `I` acts as zero on it. -/
private theorem smul_top_eq_bot_iff_forall_smul_eq_zero {A : Type u} [CommRing A] (I : Ideal A)
    (N : Type u) [AddCommGroup N] [Module A N] :
    I • (⊤ : Submodule A N) = ⊥ ↔ ∀ a ∈ I, ∀ x : N, a • x = 0 := by
  constructor
  · intro h a ha x
    have : a • x ∈ I • (⊤ : Submodule A N) :=
      Submodule.smul_mem_smul ha Submodule.mem_top
    rw [h] at this
    simpa using this
  · intro h
    rw [eq_bot_iff]
    exact Submodule.smul_le.2 fun a ha x _ => by simp [h a ha x]

/-- If `K` is annihilated by every member of a generating family of `I`, it is annihilated
by `I`. -/
private theorem smul_top_eq_bot_of_span_range {A : Type u} [CommRing A] {ι : Type*} (f : ι → A)
    (I : Ideal A) (hI : Ideal.span (Set.range f) = I)
    (K : Type u) [AddCommGroup K] [Module A K] (hK : ∀ i, ∀ x : K, f i • x = 0) :
    I • (⊤ : Submodule A K) = ⊥ := by
  subst hI
  refine (smul_top_eq_bot_iff_forall_smul_eq_zero _ K).2 fun a ha x => ?_
  have h2 : a ∈ Module.annihilator A K :=
    Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Module.mem_annihilator.2 (hK i)) ha
  exact Module.mem_annihilator.1 h2 x

/-! ### Linearity of `Tor_n(-, M)`

For a projective resolution `Pr` of `M`, the module `Tor_n(X, M)` is the degree-`n` homology of
`X ⊗ Pr` (`Tor1VanishesAux.torPhi`, `torIsoHomologyDeg`). That model is `A`-linear in `X`, so the
endomorphism of `Tor_n(K, M)` induced by `a • 𝟙 : K ⟶ K` is multiplication by `a`.
-/

/-- Whiskering is `A`-linear: `(a • 𝟙) ▷ Y = a • 𝟙`. -/
private theorem whiskerRight_smul_id {A : Type u} [CommRing A] (a : A) (X Y : ModuleCat.{u} A) :
    MonoidalCategoryStruct.whiskerRight (a • 𝟙 X) Y
      = a • 𝟙 (MonoidalCategoryStruct.tensorObj X Y) := by
  rw [MonoidalLinear.smul_whiskerRight, MonoidalCategory.id_whiskerRight]

/-- `X ↦ X ⊗ Pr` is `A`-linear. -/
private theorem torPhi_map_smul_id {A : Type u} [CommRing A] (a : A)
    (Pr : HomologicalComplex (ModuleCat.{u} A) (ComplexShape.down ℕ)) (X : ModuleCat.{u} A) :
    (torPhi Pr).map (a • 𝟙 X) = a • 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  have hf : (a • 𝟙 ((torPhi Pr).obj X)).f k = a • 𝟙 (((torPhi Pr).obj X).X k) := by simp
  rw [hf]
  exact whiskerRight_smul_id a X (Pr.X k)

/-- `Tor_n(X, M)` is the degree-`n` homology of `X ⊗ Pr`, for a projective resolution `Pr` of
`M`. -/
private noncomputable def torIsoHomologyDeg {A : Type u} [CommRing A] {M : Type u}
    [AddCommGroup M] [Module A M] (Pr : ProjectiveResolution (ModuleCat.of A M))
    (X : ModuleCat.{u} A) (n : ℕ) :
    ((Tor (ModuleCat.{u} A) n).obj X).obj (ModuleCat.of A M)
      ≅ ((torPhi Pr.complex).obj X).homology n :=
  (eqToIso (by rw [Tor_obj])).trans
    (Pr.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).obj X) n)

/-- `Tor_n(K, M)` vanishes exactly when the degree-`n` homology of `K ⊗ Pr` does. -/
private theorem torVanishes_iff_isZero_homology {A : Type u} [CommRing A] {M : Type u}
    [AddCommGroup M] [Module A M] (Pr : ProjectiveResolution (ModuleCat.of A M)) (K : Type u)
    [AddCommGroup K] [Module A K] (n : ℕ) :
    TorVanishes A n K M ↔ IsZero (((torPhi Pr.complex).obj (ModuleCat.of A K)).homology n) :=
  Iso.isZero_iff (torIsoHomologyDeg Pr (ModuleCat.of A K) n)

/-- The kernel of multiplication by `a` on `K` is `K[a]`. -/
private theorem ker_smul_id {A : Type u} [CommRing A] (a : A) (K : Type u) [AddCommGroup K]
    [Module A K] :
    LinearMap.ker (a • LinearMap.id : K →ₗ[A] K) = Submodule.torsionBy A K a := by
  ext x; simp [Submodule.mem_torsionBy_iff]

/-- The image of multiplication by `a` on `K` is `a K`. -/
private theorem range_smul_id {A : Type u} [CommRing A] (a : A) (K : Type u) [AddCommGroup K]
    [Module A K] :
    LinearMap.range (a • LinearMap.id : K →ₗ[A] K) = Ideal.span {a} • (⊤ : Submodule A K) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) Submodule.mem_top
  · refine Submodule.smul_le.2 fun r hr x _ => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    refine ⟨c • x, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    rw [mul_comm]

/-- Multiplication by `a` factors as `K ↠ K ⧸ K[a] ≅ a K ↪ K`; this is the isomorphism in the
middle, the first isomorphism theorem for multiplication by `a`. -/
private noncomputable def quotTorsionByEquivSmulRange {A : Type u} [CommRing A] (a : A)
    (K : Type u) [AddCommGroup K] [Module A K] :
    (K ⧸ Submodule.torsionBy A K a) ≃ₗ[A] ↥(Ideal.span {a} • (⊤ : Submodule A K)) :=
  (Submodule.quotEquivOfEq _ _ (ker_smul_id a K).symm).trans
    (((a • LinearMap.id : K →ₗ[A] K).quotKerEquivRange).trans
      (LinearEquiv.ofEq _ _ (range_smul_id a K)))

private theorem quotTorsionByEquivSmulRange_apply {A : Type u} [CommRing A] (a : A)
    (K : Type u) [AddCommGroup K] [Module A K] (x : K) :
    (quotTorsionByEquivSmulRange a K
      (Submodule.Quotient.mk x : K ⧸ Submodule.torsionBy A K a)).1 = a • x := by
  simp [quotTorsionByEquivSmulRange, LinearMap.quotKerEquivRange_apply_mk]

attribute [local simp] quotTorsionByEquivSmulRange_apply

/-! ### Direct sums, and the dimension shift -/

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the tensored complex passes to direct sums, in every degree: if `S ⊗ Pr` is
exact at `j`, so is `(ι →₀ S) ⊗ Pr`. -/
private theorem torPhi_finsupp_exactAt {A : Type u} [CommRing A] (ι S : Type u)
    [AddCommGroup S] [Module A S]
    (Pr : HomologicalComplex (ModuleCat.{u} A) (ComplexShape.down ℕ)) (j : ℕ)
    (hC : ((torPhi Pr).obj (ModuleCat.of A S)).ExactAt j) :
    ((torPhi Pr).obj (ModuleCat.of A (ι →₀ S))).ExactAt j := by
  classical
  set C := (torPhi Pr).obj (ModuleCat.of A S) with hCdef
  set D := (torPhi Pr).obj (ModuleCat.of A (ι →₀ S)) with hDdef
  obtain ⟨i, hi⟩ : ∃ i, (ComplexShape.down ℕ).prev j = i := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, (ComplexShape.down ℕ).next j = k := ⟨_, rfl⟩
  rw [HomologicalComplex.exactAt_iff' C i j k hi hk] at hC
  rw [HomologicalComplex.exactAt_iff' D i j k hi hk]
  have hCdij : ModuleCat.Hom.hom (C.d i j)
      = LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d i j)) := by
    apply TensorProduct.ext'; intro s b; rfl
  have hCdjk : ModuleCat.Hom.hom (C.d j k)
      = LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d j k)) := by
    apply TensorProduct.ext'; intro s b; rfl
  rw [ShortComplex.moduleCat_exact_iff] at hC
  have hCfun : Function.Exact (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d i j)))
      (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d j k))) := by
    rw [← hCdij, ← hCdjk]
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hC x hx
      exact ⟨y, hy⟩
    · rintro ⟨y, rfl⟩
      rw [hCdjk, hCdij, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d Pr i j k]
      simp
  have hSfun : Function.Exact
      (Finsupp.mapRange.linearMap (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d i j)))
        : (ι →₀ _) →ₗ[A] _)
      (Finsupp.mapRange.linearMap (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d j k)))) :=
    finsupp_mapRange_exact ι _ _ hCfun
  let Sf := ModuleCat.ofHom (Finsupp.mapRange.linearMap
    (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d i j)))
      : (ι →₀ (S ⊗[A] (Pr.X i))) →ₗ[A] (ι →₀ (S ⊗[A] (Pr.X j))))
  let Sg := ModuleCat.ofHom (Finsupp.mapRange.linearMap
    (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d j k)))
      : (ι →₀ (S ⊗[A] (Pr.X j))) →ₗ[A] (ι →₀ (S ⊗[A] (Pr.X k))))
  have hSfg : Sf ≫ Sg = 0 := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro z; exact hSfun.apply_apply_eq_zero z
  let Sfin : ShortComplex (ModuleCat.{u} A) := ShortComplex.mk Sf Sg hSfg
  have hSfinExact : Sfin.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    rw [LinearMap.exact_iff] at hSfun
    have hmem : x ∈
        (Finsupp.mapRange.linearMap
          (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d j k)))).ker := by
      rw [LinearMap.mem_ker]; exact hx
    rw [hSfun] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, hy⟩
  have hiso : Sfin ≅ D.sc' i j k := by
    refine ShortComplex.isoMk
      (TensorProduct.finsuppLeft A A S (Pr.X i) ι).symm.toModuleIso
      (TensorProduct.finsuppLeft A A S (Pr.X j) ι).symm.toModuleIso
      (TensorProduct.finsuppLeft A A S (Pr.X k) ι).symm.toModuleIso ?_ ?_
    · apply ModuleCat.hom_ext
      change LinearMap.lTensor (ι →₀ S) (ModuleCat.Hom.hom (Pr.d i j)) ∘ₗ
          (TensorProduct.finsuppLeft A A S (Pr.X i) ι).symm.toLinearMap
            = (TensorProduct.finsuppLeft A A S (Pr.X j) ι).symm.toLinearMap ∘ₗ
                Finsupp.mapRange.linearMap
                  (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d i j)))
      exact finsuppLeft_lTensor_sq ι S (Pr.X i) (Pr.X j) (ModuleCat.Hom.hom (Pr.d i j))
    · apply ModuleCat.hom_ext
      change LinearMap.lTensor (ι →₀ S) (ModuleCat.Hom.hom (Pr.d j k)) ∘ₗ
          (TensorProduct.finsuppLeft A A S (Pr.X j) ι).symm.toLinearMap
            = (TensorProduct.finsuppLeft A A S (Pr.X k) ι).symm.toLinearMap ∘ₗ
                Finsupp.mapRange.linearMap
                  (LinearMap.lTensor S (ModuleCat.Hom.hom (Pr.d j k)))
      exact finsuppLeft_lTensor_sq ι S (Pr.X j) (Pr.X k) (ModuleCat.Hom.hom (Pr.d j k))
  exact ShortComplex.exact_of_iso hiso hSfinExact

/-- `Tor` commutes with direct sums in its unresolved variable: if
`Tor_n^A(S, M) = 0` then `Tor_n^A(ι →₀ S, M) = 0`. -/
private theorem torVanishes_finsupp {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M]
    [Module A M] (ι S : Type u) [AddCommGroup S] [Module A S] (n : ℕ)
    (h : TorVanishes A n S M) : TorVanishes A n (ι →₀ S) M := by
  let Pr : ProjectiveResolution (ModuleCat.of A M) := ProjectiveResolution.of (ModuleCat.of A M)
  have hCexact : ((torPhi Pr.complex).obj (ModuleCat.of A S)).ExactAt n := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (torVanishes_iff_isZero_homology Pr S n).1 h
  have hD := torPhi_finsupp_exactAt ι S Pr.complex n hCexact
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hD
  exact (torVanishes_iff_isZero_homology Pr _ n).2 hD

/-- `Tor_n^A(-, M)` carries a linear equivalence to an isomorphism, so its vanishing only depends
on the isomorphism class of the first variable. -/
private theorem torVanishes_of_linearEquiv {A : Type u} [CommRing A] {M : Type u}
    [AddCommGroup M] [Module A M] {K L : Type u} [AddCommGroup K] [Module A K]
    [AddCommGroup L] [Module A L] (e : K ≃ₗ[A] L) (n : ℕ) (h : TorVanishes A n L M) :
    TorVanishes A n K M :=
  IsZero.of_iso h (((Tor (ModuleCat.{u} A) n).mapIso e.toModuleIso).app (ModuleCat.of A M))

/-- If `Tor_{n+1}(A ⧸ I, M) = 0` and `Tor_n(N, M) = 0` for every `A`-module `N` annihilated by
`I`, then `Tor_{n+1}(K, M) = 0` for every `A`-module `K` annihilated by `I`. -/
private theorem torVanishes_succ_of_smul_top_eq_bot
    {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M] (I : Ideal A) (n : ℕ)
    (hquot : TorVanishes A (n + 1) (A ⧸ I) M)
    (ih : ∀ (N : Type u) [AddCommGroup N] [Module A N], I • (⊤ : Submodule A N) = ⊥ →
      TorVanishes A n N M)
    (K : Type u) [AddCommGroup K] [Module A K] (hK : I • (⊤ : Submodule A K) = ⊥) :
    TorVanishes A (n + 1) K M := by
  classical
  have hzero : ∀ a ∈ I, ∀ (N : Type u) [AddCommGroup N] [Module (A ⧸ I) N] [Module A N]
      [IsScalarTower A (A ⧸ I) N] (x : N), a • x = 0 := by
    intro a ha N _ _ _ _ x
    have h0 : algebraMap A (A ⧸ I) a = 0 := by
      simpa using (Ideal.Quotient.eq_zero_iff_mem (I := I) (a := a)).2 ha
    rw [← IsScalarTower.algebraMap_smul (A ⧸ I) a x, h0, zero_smul]
  have hKz : ∀ a ∈ I, ∀ x : K, a • x = 0 :=
    (smul_top_eq_bot_iff_forall_smul_eq_zero I K).1 hK
  have htors : Module.IsTorsionBySet A K (I : Set A) := fun x r => hKz r r.2 x
  let _ : Module (A ⧸ I) K := htors.module
  have : IsScalarTower A (A ⧸ I) K := by
    refine ⟨fun r x m => ?_⟩
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [show (Ideal.Quotient.mk I r' : A ⧸ I) • m = r' • m from rfl, ← smul_assoc]; rfl
  let π : (K →₀ (A ⧸ I)) →ₗ[A ⧸ I] K := Finsupp.linearCombination (A ⧸ I) id
  let πA : (K →₀ (A ⧸ I)) →ₗ[A] K := π.restrictScalars A
  have hπ : Function.Surjective πA := by
    intro x
    refine ⟨Finsupp.single x 1, ?_⟩
    change π (Finsupp.single x 1) = x
    rw [Finsupp.linearCombination_single]
    simp
  have hPz : I • (⊤ : Submodule A (LinearMap.ker πA)) = ⊥ :=
    (smul_top_eq_bot_iff_forall_smul_eq_zero I _).2 fun r hr y =>
      Subtype.ext (by simpa using hzero r hr (K →₀ (A ⧸ I)) y.1)
  let Pr : ProjectiveResolution (ModuleCat.of A M) := ProjectiveResolution.of (ModuleCat.of A M)
  have hrel : (ComplexShape.down ℕ).Rel (n + 1) n := by simp
  have hX2 := (torVanishes_iff_isZero_homology Pr _ (n + 1)).1
    (torVanishes_finsupp K (A ⧸ I) (n + 1) hquot)
  have hX1 := (torVanishes_iff_isZero_homology Pr _ n).1 (ih (LinearMap.ker πA) hPz)
  have hmid := middle_zero _
    ((mappedSES_shortExact (LinearMap.ker πA) Pr).homology_exact₃ (n + 1) n hrel) hX2 hX1
  exact torVanishes_of_linearEquiv (πA.quotKerEquivOfSurjective hπ).symm (n + 1)
    ((torVanishes_iff_isZero_homology Pr _ (n + 1)).2 hmid)

/-- If `Tor_n(K[a], M) = 0` and `Tor_{n+1}(K / a K, M) = 0`, where `K[a]` is the `a`-torsion of
`K`, then multiplication by `a` on `Tor_n(K, M)` is injective. -/
private theorem injective_smul_torObj_of_torVanishes
    {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M] (a : A)
    (K : Type u) [AddCommGroup K] [Module A K] (n : ℕ)
    (hker : TorVanishes A n (Submodule.torsionBy A K a) M)
    (hcok : TorVanishes A (n + 1) (K ⧸ (Ideal.span {a} • (⊤ : Submodule A K))) M) :
    Function.Injective fun x : TorObj A n K M => a • x := by
  classical
  let Pr : ProjectiveResolution (ModuleCat.of A M) := ProjectiveResolution.of (ModuleCat.of A M)
  have hrel : (ComplexShape.down ℕ).Rel (n + 1) n := by simp
  have mono1 : Mono (HomologicalComplex.homologyMap
      ((torPhi Pr.complex).map (ModuleCat.ofHom (Submodule.torsionBy A K a).mkQ)) n) :=
    ((mappedSES_shortExact (Submodule.torsionBy A K a) Pr).homology_exact₂ n).mono_g
      (((torVanishes_iff_isZero_homology Pr _ n).1 hker).eq_of_src _ _)
  have mono2 : Mono (HomologicalComplex.homologyMap
      ((torPhi Pr.complex).map
        (ModuleCat.ofHom (Ideal.span {a} • (⊤ : Submodule A K)).subtype)) n) :=
    ((mappedSES_shortExact (Ideal.span {a} • (⊤ : Submodule A K)) Pr).homology_exact₁
      (n + 1) n hrel).mono_g
      (((torVanishes_iff_isZero_homology Pr _ (n + 1)).1 hcok).eq_of_src _ _)
  have hinv : HomologicalComplex.homologyMap
        ((torPhi Pr.complex).map (quotTorsionByEquivSmulRange a K).toModuleIso.hom) n
      ≫ HomologicalComplex.homologyMap
        ((torPhi Pr.complex).map (quotTorsionByEquivSmulRange a K).toModuleIso.inv) n
      = 𝟙 (((torPhi Pr.complex).obj
          (ModuleCat.of A (K ⧸ Submodule.torsionBy A K a))).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp, Iso.hom_inv_id]
    simp
  have mono3 : IsSplitMono (HomologicalComplex.homologyMap
      ((torPhi Pr.complex).map (quotTorsionByEquivSmulRange a K).toModuleIso.hom) n) :=
    ⟨⟨⟨_, hinv⟩⟩⟩
  have hfactor : (ModuleCat.ofHom (Submodule.torsionBy A K a).mkQ ≫
      ((quotTorsionByEquivSmulRange a K).toModuleIso.hom ≫
        ModuleCat.ofHom (Ideal.span {a} • (⊤ : Submodule A K)).subtype))
      = a • 𝟙 (ModuleCat.of A K) :=
    ModuleCat.hom_ext (LinearMap.ext fun x => by simp)
  have key : (a • 𝟙 (((torPhi Pr.complex).obj (ModuleCat.of A K)).homology n))
      = HomologicalComplex.homologyMap
          ((torPhi Pr.complex).map (ModuleCat.ofHom (Submodule.torsionBy A K a).mkQ)) n
        ≫ (HomologicalComplex.homologyMap
            ((torPhi Pr.complex).map (quotTorsionByEquivSmulRange a K).toModuleIso.hom) n
          ≫ HomologicalComplex.homologyMap ((torPhi Pr.complex).map
              (ModuleCat.ofHom (Ideal.span {a} • (⊤ : Submodule A K)).subtype)) n) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp, hfactor, torPhi_map_smul_id,
      HomologicalComplex.homologyMap_smul_id]
  have hmonoH : Mono (a • 𝟙 (((torPhi Pr.complex).obj (ModuleCat.of A K)).homology n)) := by
    rw [key]; infer_instance
  have hconj : (torIsoHomologyDeg Pr (ModuleCat.of A K) n).hom
      ≫ (a • 𝟙 (((torPhi Pr.complex).obj (ModuleCat.of A K)).homology n))
      ≫ (torIsoHomologyDeg Pr (ModuleCat.of A K) n).inv = a • 𝟙 (TorObj A n K M) := by
    simp [Linear.comp_smul, Linear.smul_comp]
  have hmonoT : Mono (a • 𝟙 (TorObj A n K M)) := by rw [← hconj]; infer_instance
  have hinjT := (ModuleCat.mono_iff_injective (a • 𝟙 (TorObj A n K M))).1 hmonoT
  intro x y hxy
  refine hinjT ?_
  simpa only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
    id_eq] using hxy

/-! ### Inverting one generator

For a flat `A`-module `R`, the functor `- ⊗ R` commutes with `Tor'_n(K, -)`, since `Tor'` resolves
its first variable and `- ⊗ R` is exact. Applied to the localization `A_a`, this gives the
vanishing of `Tor_n^A(K, M)` after inverting `a` when `M_a` is flat over `A_a`.
-/

/-- An exact functor commutes with the homology of a chain complex. -/
public noncomputable def mapHomologyIso {A : Type u} [CommRing A]
    (G : ModuleCat.{u} A ⥤ ModuleCat.{u} A) [G.PreservesZeroMorphisms] [G.PreservesHomology]
    (C : HomologicalComplex (ModuleCat.{u} A) (ComplexShape.down ℕ)) (n : ℕ) :
    G.obj (C.homology n) ≅ ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology n :=
  (ShortComplex.mapHomologyIso (C.sc n) G).symm ≪≫
    HomologicalComplex.homologyMapIso
      (Iso.refl ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj C)) n

/-- For a flat `A`-module `R`, `Tor'_n(K, M) ⊗ R ≅ Tor'_n(K, M ⊗ R)`. -/
private noncomputable def tor'TensorRightIso {A : Type u} [CommRing A]
    (K M R : ModuleCat.{u} A) [Module.Flat A R] (n : ℕ) :
    (MonoidalCategory.tensorRight R).obj (((Tor' (ModuleCat.{u} A) n).obj K).obj M) ≅
      ((Tor' (ModuleCat.{u} A) n).obj K).obj (MonoidalCategoryStruct.tensorObj M R) := by
  haveI : (MonoidalCategory.tensorRight R).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  let P : ProjectiveResolution K := ProjectiveResolution.of K
  refine (MonoidalCategory.tensorRight R).mapIso
    (P.isoLeftDerivedObj (MonoidalCategory.tensorRight M) n) ≪≫ ?_
  refine mapHomologyIso (MonoidalCategory.tensorRight R) _ n ≪≫ ?_
  refine HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (MonoidalCategory.tensorRightTensor M R).symm
      (ComplexShape.down ℕ)).app P.complex) n ≪≫ ?_
  exact (P.isoLeftDerivedObj
    (MonoidalCategory.tensorRight (MonoidalCategoryStruct.tensorObj M R)) n).symm

/-- `Tor'_{n+1}(K, F) = 0` for a flat `A`-module `F`. -/
@[ega "0 6.1.1" "(a) ⇒ (b)"]
private theorem isZero_Tor'_of_flat {A : Type u} [CommRing A] (K F : ModuleCat.{u} A)
    [Module.Flat A F] (n : ℕ) :
    IsZero (((Tor' (ModuleCat.{u} A) (n + 1)).obj K).obj F) :=
  IsZero.of_iso (Tor_iso_Tor'.tor_flat_isZero A F K n)
    (((torFlip_iso_Tor' A (n + 1)).app K).app F).symm

/-- `M ⊗_A A_a` is flat over `A` as soon as the localization `M_a` is flat over `A_a`. -/
private theorem flat_tensor_localization {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M]
    [Module A M] (a : A)
    (Aa : Type*) [CommRing Aa] [Algebra A Aa] [IsLocalization.Away a Aa]
    (Ma : Type*) [AddCommGroup Ma] [Module A Ma] [Module Aa Ma] [IsScalarTower A Aa Ma]
    (ga : M →ₗ[A] Ma) [IsLocalizedModule.Away a ga] [Module.Flat Aa Ma] :
    Module.Flat A (M ⊗[A] Localization.Away a) := by
  have : Module.Flat A Aa := IsLocalization.flat Aa (Submonoid.powers a)
  have : Module.Flat A Ma := Module.Flat.trans A Aa Ma
  have e1 : Aa ⊗[A] M ≃ₗ[Aa] Ma :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers a) Aa ga).equiv
  have e2 : Localization.Away a ≃ₐ[A] Aa := IsLocalization.algEquiv (Submonoid.powers a) _ _
  exact Module.Flat.of_linearEquiv
    ((TensorProduct.comm A M (Localization.Away a)).trans
      ((TensorProduct.congr e2.toLinearEquiv (LinearEquiv.refl A M)).trans
        (e1.restrictScalars A)))

/-- An element of an `A`-module whose localization at `a` vanishes is killed by a power of `a`. -/
private theorem exists_pow_smul_eq_zero_of_subsingleton_tensor {A : Type u} [CommRing A] (a : A)
    (T : Type*) [AddCommGroup T] [Module A T]
    (hT : Subsingleton (T ⊗[A] Localization.Away a)) (x : T) : ∃ m : ℕ, a ^ m • x = 0 := by
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers a) (Localization.Away a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) T)
  have h0 : (x ⊗ₜ[A] (1 : Localization.Away a)) = 0 := hT.elim _ _
  have h1 : ((1 : Localization.Away a) ⊗ₜ[A] x) = 0 := by
    have := congrArg (TensorProduct.comm A T (Localization.Away a)) h0
    simpa using this
  have h2 : LocalizedModule.mk x 1 = (0 : LocalizedModule (Submonoid.powers a) T) := by
    have h := congrArg hbc.equiv h1
    rw [IsBaseChange.equiv_tmul, map_zero, one_smul] at h
    exact h
  rw [show (0 : LocalizedModule (Submonoid.powers a) T) = LocalizedModule.mk 0 1 from
    (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq] at h2
  obtain ⟨u, hu⟩ := h2
  obtain ⟨m, hm⟩ := u.2
  have hm' : a ^ m = (u : A) := hm
  refine ⟨m, ?_⟩
  rw [hm']
  have hu' : u • x = (0 : T) := by simpa using hu
  exact hu'

/-- If the localization `M_a` is flat over `A_a`, then every element of `Tor_n^A(K, M)`, for
`n ≥ 1`, is killed by a power of `a`. -/
private theorem exists_pow_smul_eq_zero_of_flat_localization
    {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M] (a : A)
    (Aa : Type*) [CommRing Aa] [Algebra A Aa] [IsLocalization.Away a Aa]
    (Ma : Type*) [AddCommGroup Ma] [Module A Ma] [Module Aa Ma] [IsScalarTower A Aa Ma]
    (ga : M →ₗ[A] Ma) [IsLocalizedModule.Away a ga] [Module.Flat Aa Ma]
    (K : Type u) [AddCommGroup K] [Module A K] (n : ℕ) (hn : 1 ≤ n)
    (x : TorObj A n K M) : ∃ m : ℕ, a ^ m • x = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have : Module.Flat A (M ⊗[A] Localization.Away a) := flat_tensor_localization a Aa Ma ga
  have : Module.Flat A (Localization.Away a) :=
    IsLocalization.flat (Localization.Away a) (Submonoid.powers a)
  have h0 : IsZero ((MonoidalCategory.tensorRight
      (ModuleCat.of A (Localization.Away a))).obj (TorObj A (j + 1) K M)) := by
    refine IsZero.of_iso (isZero_Tor'_of_flat (ModuleCat.of A K)
      (MonoidalCategoryStruct.tensorObj (ModuleCat.of A M)
        (ModuleCat.of A (Localization.Away a))) j) ?_
    exact (MonoidalCategory.tensorRight _).mapIso
        (((Tor_iso_Tor' A (j + 1)).app (ModuleCat.of A K)).app (ModuleCat.of A M)) ≪≫
      tor'TensorRightIso (ModuleCat.of A K) (ModuleCat.of A M) _ (j + 1)
  exact exists_pow_smul_eq_zero_of_subsingleton_tensor a (TorObj A (j + 1) K M)
    (ModuleCat.isZero_iff_subsingleton.mp h0) x

/-- The image of an element of `𝔪 • ⊤` under a map that is semilinear over a ring homomorphism
`φ` lies in `(𝔪.map φ) • ⊤`. -/
private theorem map_mem_smul_top {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    {N₁ N₂ : Type*} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module B N₂]
    (ψ : N₁ →+ N₂) (hψ : ∀ (a : A) (x : N₁), ψ (a • x) = φ a • ψ x)
    (𝔪 : Ideal A) {y : N₁} (hy : y ∈ 𝔪 • (⊤ : Submodule A N₁)) :
    ψ y ∈ (𝔪.map φ) • (⊤ : Submodule B N₂) := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro a ha x _
    rw [hψ]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem φ ha) Submodule.mem_top
  · intro x z hx hz
    rw [map_add]
    exact Submodule.add_mem _ hx hz

/-- If `M` is flat over `A`, each `M_{f i}` is faithfully flat over `A_{f i}` and `M ⧸ I M` is
faithfully flat over `A ⧸ I`, where the `f i` generate `I`, then `M` is faithfully flat over
`A`. -/
private theorem faithfullyFlat_of_faithfullyFlat_localization
    {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    {ι : Type*} [Finite ι] (f : ι → A) (I : Ideal A)
    (Af : ι → Type*) [∀ i, CommRing (Af i)] [∀ i, Algebra A (Af i)]
    [∀ i, IsLocalization.Away (f i) (Af i)]
    (Mf : ι → Type*) [∀ i, AddCommGroup (Mf i)] [∀ i, Module A (Mf i)]
    [∀ i, Module (Af i) (Mf i)] [∀ i, IsScalarTower A (Af i) (Mf i)]
    (g : ∀ i, M →ₗ[A] Mf i) [∀ i, IsLocalizedModule.Away (f i) (g i)]
    (hI : Ideal.span (Set.range f) = I) (hflat : Module.Flat A M)
    (hloc : ∀ i, Module.FaithfullyFlat (Af i) (Mf i))
    (hquot : Module.FaithfullyFlat (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M)))) :
    Module.FaithfullyFlat A M := by
  classical
  rw [Module.faithfullyFlat_iff]
  refine ⟨hflat, ?_⟩
  intro 𝔪 h𝔪 h𝔪top
  have hall : ∀ y : M, y ∈ 𝔪 • (⊤ : Submodule A M) := fun y => by
    rw [h𝔪top]; exact Submodule.mem_top
  by_cases hcase : ∀ i, f i ∈ 𝔪
  · have hI𝔪 : I ≤ 𝔪 := by
      rw [← hI]; exact Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hcase i)
    have hne : 𝔪.map (Ideal.Quotient.mk I) ≠ ⊤ := by
      intro htop
      have h1 := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective 𝔪
      rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        sup_eq_left.2 hI𝔪] at h1
      exact h𝔪.ne_top h1.symm
    refine hne ?_
    rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top] at hquot
    refine hquot.2 _ (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule A M)) x
    exact map_mem_smul_top (Ideal.Quotient.mk I)
      ((I • (⊤ : Submodule A M)).mkQ).toAddMonoidHom (fun a z => rfl) 𝔪 (hall y)
  · obtain ⟨i, hi⟩ := not_forall.1 hcase
    have hprime : (𝔪.map (algebraMap A (Af i))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (f i)) (Af i) 𝔪 h𝔪.isPrime
        (by
          rw [Set.disjoint_left]
          rintro s ⟨k, rfl⟩ hs
          exact hi (h𝔪.isPrime.mem_of_pow_mem k hs))
    refine hprime.ne_top ?_
    have hff := hloc i
    rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top] at hff
    refine hff.2 _ (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨⟨y, s⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (g i) x
    have hgy : g i y ∈ (𝔪.map (algebraMap A (Af i))) • (⊤ : Submodule (Af i) (Mf i)) :=
      map_mem_smul_top (algebraMap A (Af i)) (g i).toAddMonoidHom
        (fun a z => by simp [algebraMap_smul]) 𝔪 (hall y)
    have hsx : (algebraMap A (Af i) (s : A)) • x
        ∈ (𝔪.map (algebraMap A (Af i))) • (⊤ : Submodule (Af i) (Mf i)) := by
      have hxy : (algebraMap A (Af i) (s : A)) • x = g i y := by
        rw [algebraMap_smul]
        exact hy
      rw [hxy]; exact hgy
    obtain ⟨u, hu⟩ : IsUnit (algebraMap A (Af i) (s : A)) :=
      IsLocalization.map_units (Af i) s
    have hxeq : x = (↑u⁻¹ : Af i) • ((algebraMap A (Af i) (s : A)) • x) := by
      rw [← hu, smul_smul]
      simp
    rw [hxeq]
    exact Submodule.smul_mem _ _ hsx

/-! ### The two inductions -/

/-- If `M ⧸ I M` is flat over `A ⧸ I` and `Tor_n^A(A ⧸ I, M) = 0` for `1 ≤ n ≤ r + 1`, then
`Tor_n^A(K, M) = 0` for every `A`-module `K` annihilated by `I` and every `1 ≤ n ≤ r + 1`. -/
private theorem torVanishes_of_smul_top_eq_bot
    {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M] (I : Ideal A) (r : ℕ)
    (hflat : Module.Flat (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M))))
    (hTor : ∀ n : ℕ, 1 ≤ n → n ≤ r + 1 → TorVanishes A n (A ⧸ I) M)
    (n : ℕ) :
    1 ≤ n → n ≤ r + 1 → ∀ (K : Type u) [AddCommGroup K] [Module A K],
      I • (⊤ : Submodule A K) = ⊥ → TorVanishes A n K M := by
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro _ hnr K _ _ hK
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact tor1_vanishes_of_smul_eq_bot I hflat (hTor 1 le_rfl (by omega)) K hK
    · exact torVanishes_succ_of_smul_top_eq_bot I m (hTor (m + 1) (by omega) hnr)
        (fun N _ _ hN => ih hm (by omega) N hN) K hK

/-- Suppose `Tor_n^A(K, M) = 0` for every `A`-module `K` annihilated by all the `f i` and every
`1 ≤ n ≤ Fintype.card ι + 1`, and that every element of `Tor_n^A(K, M)`, for `n ≥ 1`, is killed by
a power of each `f i`. Then for every finite set `s` of indices, `Tor_n^A(K, M) = 0` for every `K`
annihilated by the `f i` with `i ∈ s` and every `1 ≤ n ≤ s.card + 1`. -/
private theorem torVanishes_of_forall_mem_smul_eq_zero
    {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
    {ι : Type*} [Fintype ι] (f : ι → A)
    (hbase : ∀ (K : Type u) [AddCommGroup K] [Module A K], (∀ i, ∀ x : K, f i • x = 0) →
      ∀ n, 1 ≤ n → n ≤ Fintype.card ι + 1 → TorVanishes A n K M)
    (htors : ∀ (i : ι) (K : Type u) [AddCommGroup K] [Module A K] (n : ℕ), 1 ≤ n →
      ∀ x : TorObj A n K M, ∃ m : ℕ, f i ^ m • x = 0)
    (s : Finset ι) (K : Type u) [AddCommGroup K] [Module A K]
    (hK : ∀ i ∈ s, ∀ x : K, f i • x = 0)
    (n : ℕ) (hn1 : 1 ≤ n) (hns : n ≤ s.card + 1) : TorVanishes A n K M := by
  classical
  suffices H : ∀ (k : ℕ) (s : Finset ι), sᶜ.card = k →
      ∀ (K : Type u) [AddCommGroup K] [Module A K], (∀ i ∈ s, ∀ x : K, f i • x = 0) →
        ∀ n, 1 ≤ n → n ≤ s.card + 1 → TorVanishes A n K M from
    H sᶜ.card s rfl K hK n hn1 hns
  clear hK hn1 hns
  intro k
  induction k with
  | zero =>
    intro s hs K _ _ hK n hn1 hn2
    have hsu : s = Finset.univ := by
      rwa [Finset.card_eq_zero, Finset.compl_eq_empty_iff] at hs
    subst hsu
    exact hbase K (fun i x => hK i (Finset.mem_univ i) x) n hn1
      (by simpa [Finset.card_univ] using hn2)
  | succ k ih =>
    intro s hs K _ _ hK n hn1 hn2
    obtain ⟨i₀, hi₀⟩ : sᶜ.Nonempty := Finset.card_pos.1 (by omega)
    have hi₀s : i₀ ∉ s := Finset.mem_compl.1 hi₀
    have hcard : (insert i₀ s).card = s.card + 1 := Finset.card_insert_of_notMem hi₀s
    have hs' : (insert i₀ s)ᶜ.card = k := by
      have h1 : sᶜ.card = Fintype.card ι - s.card := Finset.card_compl s
      have h2 : (insert i₀ s)ᶜ.card = Fintype.card ι - (insert i₀ s).card :=
        Finset.card_compl _
      have h3 : s.card ≤ Fintype.card ι := by
        simpa [Finset.card_univ] using Finset.card_le_univ s
      omega
    have hT : ∀ i ∈ insert i₀ s, ∀ x : Submodule.torsionBy A K (f i₀), f i • x = 0 := by
      intro i hi x
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Subtype.ext (by simp)
      · exact Subtype.ext (by simp [hK i hi x.1])
    have hQ : ∀ i ∈ insert i₀ s,
        ∀ x : K ⧸ (Ideal.span {f i₀} • (⊤ : Submodule A K)), f i • x = 0 := by
      intro i hi x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
      · simp [hK i hi y]
    have hinj : Function.Injective fun x : TorObj A n K M => f i₀ • x := by
      refine injective_smul_torObj_of_torVanishes (f i₀) K n
        (ih _ hs' _ (fun i hi x => hT i hi x) n hn1 (by omega))
        (ih _ hs' _ (fun i hi x => hQ i hi x) (n + 1) (by omega) (by omega))
    have : Subsingleton (TorObj A n K M) :=
      subsingleton_of_injective_smul_of_exists_pow_smul_eq_zero hinj (htors i₀ K n hn1)
    exact ModuleCat.isZero_of_subsingleton _

/-! ### The criterion -/

/-- Let `I` be generated by a finite family `f`, and suppose `Tor_n^A(A/I, M) = 0` for
`1 ≤ n ≤ Nat.card ι + 1`. If each `M_{f i}` is flat over `A_{f i}` and `M/IM` is flat over `A/I`,
then `M` is flat over `A`; and the same with "flat" replaced by "faithfully flat". -/
public theorem solution {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    {ι : Type*} [Finite ι] (f : ι → A) (I : Ideal A)
    (Af : ι → Type*) [∀ i, CommRing (Af i)] [∀ i, Algebra A (Af i)]
    [∀ i, IsLocalization.Away (f i) (Af i)]
    (Mf : ι → Type*) [∀ i, AddCommGroup (Mf i)] [∀ i, Module A (Mf i)]
    [∀ i, Module (Af i) (Mf i)] [∀ i, IsScalarTower A (Af i) (Mf i)]
    (g : ∀ i, M →ₗ[A] Mf i) [∀ i, IsLocalizedModule.Away (f i) (g i)]
    (hI : Ideal.span (Set.range f) = I)
    (hTor : ∀ n : ℕ, 1 ≤ n → n ≤ Nat.card ι + 1 →
      IsZero (((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A M))) :
    ((∀ i, Module.Flat (Af i) (Mf i)) →
        Module.Flat (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M))) →
        Module.Flat A M) ∧
      ((∀ i, Module.FaithfullyFlat (Af i) (Mf i)) →
        Module.FaithfullyFlat (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M))) →
        Module.FaithfullyFlat A M) := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  have hcard : Nat.card ι = Fintype.card ι := Nat.card_eq_fintype_card
  have hTor' : ∀ n : ℕ, 1 ≤ n → n ≤ Fintype.card ι + 1 → TorVanishes A n (A ⧸ I) M := by
    intro n hn1 hn2
    exact (torVanishes_iff_isZero_Tor' A n (A ⧸ I) M).2 (hTor n hn1 (by omega))
  have main : (∀ i, Module.Flat (Af i) (Mf i)) →
      Module.Flat (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M))) → Module.Flat A M := by
    intro hlocflat hquotflat
    refine flat_of_tor1_quotient_vanishes fun J => ?_
    refine torVanishes_of_forall_mem_smul_eq_zero f ?_ ?_ ∅ (A ⧸ J) (by simp) 1 le_rfl (by simp)
    · intro K _ _ hK n hn1 hn2
      exact torVanishes_of_smul_top_eq_bot I (Fintype.card ι) hquotflat hTor' n hn1 hn2 K
        (smul_top_eq_bot_of_span_range f I hI K hK)
    · intro i K _ _ n hn x
      exact exists_pow_smul_eq_zero_of_flat_localization (f i) (Af i) (Mf i) (g i) K n hn x
  refine ⟨main, fun hlocff hquotff => ?_⟩
  have hflat : Module.Flat A M :=
    main (fun i => (hlocff i).toFlat) hquotff.toFlat
  exact faithfullyFlat_of_faithfullyFlat_localization M f I Af Mf g hI hflat hlocff hquotff

end Stacks.Flatness.AwayTorCriterion


open CategoryTheory Limits

namespace Module

variable {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
  {ι : Type*} [Finite ι] (f : ι → A) (I : Ideal A)
  (Af : ι → Type*) [∀ i, CommRing (Af i)] [∀ i, Algebra A (Af i)]
  [∀ i, IsLocalization.Away (f i) (Af i)]
  (Mf : ι → Type*) [∀ i, AddCommGroup (Mf i)] [∀ i, Module A (Mf i)]
  [∀ i, Module (Af i) (Mf i)] [∀ i, IsScalarTower A (Af i) (Mf i)]
  (g : ∀ i, M →ₗ[A] Mf i) [∀ i, IsLocalizedModule.Away (f i) (g i)]

include g in
/-- Let `A` be a ring, let `M` be an `A`-module, and let `I` be the ideal
generated by a finite family of elements `f i` of `A`, with `r` the number of generators. Assume
`Tor_n^A(A/I, M) = 0` for `1 ≤ n ≤ r + 1`. If each localization `M_{f i}` is flat over `A_{f i}`
and `M/IM` is flat over `A/I`, then `M` is flat over `A`; and the same with "flat" replaced by
"faithfully flat" throughout.

Here `Tor_n^A(A/I, M)` is `((Tor' (ModuleCat A) n).obj (A ⧸ I)).obj M`, the `n`-th left derived
functor of `- ⊗_A M` evaluated at `A ⧸ I`, and `M/IM` is `M ⧸ I • ⊤` with its canonical
`A ⧸ I`-module structure. The localizations are given abstractly, by
`IsLocalization.Away (f i) (Af i)` and `IsLocalizedModule.Away (f i) (g i)`. -/
@[stacks 0H7P "Both statements: `.1` is the flat one and `.2` the faithfully flat one (\"same
with flat replaced by faithfully flat\"), sharing the generating family and the Tor hypotheses.
The two arguments of `Tor_n^A` are in the order used by the source's own proof (through 051C),
namely `Tor_n^A(A/I, M)`; the two orders agree by the symmetry of Tor (00M3). The generators are
a family indexed by a finite type, and the source's `r ≥ 1` is dropped. See the module
docstring."]
public theorem flat_and_faithfullyFlat_of_isLocalized_away_of_isZero_Tor'
    (hI : Ideal.span (Set.range f) = I)
    (hTor : ∀ n : ℕ, 1 ≤ n → n ≤ Nat.card ι + 1 →
      IsZero (((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A M))) :
    ((∀ i, Module.Flat (Af i) (Mf i)) →
        Module.Flat (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M))) →
        Module.Flat A M) ∧
      ((∀ i, Module.FaithfullyFlat (Af i) (Mf i)) →
        Module.FaithfullyFlat (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M))) →
        Module.FaithfullyFlat A M) :=
  Stacks.Flatness.AwayTorCriterion.solution M f I Af Mf g hI hTor

end Module

end
