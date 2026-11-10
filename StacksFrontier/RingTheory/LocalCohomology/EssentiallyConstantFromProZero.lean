module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapCokernel
public import StacksFrontier.RingTheory.LocalCohomology.IdealPowerProZero

/-!
# Essential constancy of `{H^i_T(M/IⁿM)}` from the pro-zero assertions

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `T ⊆ Spec(A)` a subset and `M` a finite
`A`-module. Theorem [Stacks, Tag 0EIE] asserts that in the bootstrap situation of
[Stacks, Tag 0EFU] the inverse system `{H^i_T(M/IⁿM)}` is essentially constant with value
`H^i_T(M)` for every `i ≤ s`. Its proof rests on Lemma [Stacks, Tag 0EFX]: the systems
`{H^i_T(IⁿM)}` are pro-zero for `i ≤ s`, and in degree `s + 1` the transition images inject
into a fixed term. This file derives Theorem 0EIE from those two assertions, taken for every
bootstrap situation.

The route is shorter than the source's at the last step. Essential constancy with value
`H^i_T(M)` follows directly from two facts about the cone `H^i_T(M) → H^i_T(M/IⁿM)`: its
projections are injective for `n ≫ 0` (part (1) of [Stacks, Tag 0EFY]), and for every `n` the
transition image from some `H^i_T(M/IᵏM)` lies in the image of `H^i_T(M)`. No limit argument
is needed. By the long exact sequence of `0 → IⁿM → M → M/IⁿM → 0` and the naturality of its
connecting map, the second fact holds once every class of `H^{i+1}_T(IᵏM)` dying in
`H^{i+1}_T(M)` dies in `H^{i+1}_T(IⁿM)`. For `i < s` that is the pro-zero assertion in degree
`i + 1`. For `i = s` it is the diagram chase in the source's proof of Theorem 0EIE: choose
generators `f₁, …, f_r` of `I^{m₀}`, form the cokernel `Q` of `M → Mʳ, x ↦ (fⱼx)`, and use the
stable-image assertion for `M` together with the pro-zero assertion for `Q`, which is again a
bootstrap situation (`Stacks.Algebraization.BootstrapSituation.cokernel`).

The source first passes to `M/H^0_I(M)`, which makes `M → Mʳ` injective. Here that reduction is
replaced by working with the image `L ⊆ Mʳ` of `M`. By Artin–Rees, `IᵃM → IᵃL` is an
isomorphism for `a ≫ 0`, which carries the conclusion from `L` back to `M`. So only `Q` has to be
a bootstrap situation, and `M/H^0_I(M)` never does.

## Main results

* `Stacks.LocalCohomology.exists_isEssentiallyConstantWith_of_injective_of_range_le`: a cone
  on an `ℕᵒᵖ`-indexed system of modules whose projections are eventually injective, and whose
  projection images contain transition images, carries essential-constancy data.
* `Stacks.LocalCohomology.localCohomologyδ_naturality`: the connecting map of the long exact
  sequence of `H^*_T` is natural in the short exact sequence.
* `Stacks.LocalCohomology.exists_forall_localCohomology_idealPower_submodule_eq_zero`: the
  degree `s + 1` diagram chase of Tag 0EIE.
* `Stacks.LocalCohomology.exists_forall_localCohomology_idealPowerTower_eq_zero_of_inclusion`:
  the kernel condition in degree `s + 1`.
* `Stacks.LocalCohomology.exists_isEssentiallyConstantWith_localCohomologyAdicCone_of_proZero`:
  essential constancy for `i ≤ s`, from the pro-zero assertion and the kernel condition.
* `Stacks.LocalCohomology.Bootstrap.exists_isEssentiallyConstantWith_of_proZero`: Theorem
  0EIE in the bootstrap situation, from both assertions of Tag 0EFX for every bootstrap
  situation.

## Implementation notes

The two assertions of Tag 0EFX enter as hypotheses quantified over all bootstrap situations
(`hXa`, `hXb`), because the proof applies the pro-zero assertion to the auxiliary situation `Q`
as well as to `M`. Both are statements of the Stacks project, so nothing here carries a
registration of Tag 0EIE: the registration belongs on the composite with an unconditional
proof of Tag 0EFX.

The module universe equals the ring universe. The long exact sequence is stated in
`ModuleCat.{max u v}`, and so are the modules `Mʳ`, `Q` and the submodules that appear.

## References

* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.LocalCohomology

/-! ### A criterion for essential constancy with a given value -/

/-- **An inverse system of modules whose cone projections are eventually injective and whose
transition images eventually lie in the images of the projections is essentially constant with
value the cone point.** -/
theorem exists_isEssentiallyConstantWith_of_injective_of_range_le
    {R : Type u} [CommRing R] {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} (c : Cone F) {n : ℕ}
    (hinj : ∀ m : ℕ, n ≤ m → Function.Injective (c.π.app (op m)).hom)
    (hrange : ∀ j : ℕ, ∃ b : ℕ, ∃ hjb : j ≤ b,
      LinearMap.range (F.map (homOfLE hjb).op).hom ≤ LinearMap.range (c.π.app (op j)).hom) :
    ∃ (j : ℕᵒᵖ) (σ : F.obj j ⟶ c.pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith F c j σ := by
  let p (m : ℕ) : c.pt →ₗ[R] F.obj (op m) := (c.π.app (op m)).hom
  let t {a b : ℕ} (h : a ≤ b) : F.obj (op b) →ₗ[R] F.obj (op a) := (F.map (homOfLE h).op).hom
  have tcomp {a b d : ℕ} (hab : a ≤ b) (hbd : b ≤ d) (x : F.obj (op d)) :
      t hab (t hbd x) = t (hab.trans hbd) x := by
    change (F.map (homOfLE hbd).op ≫ F.map (homOfLE hab).op).hom x = _
    rw [← F.map_comp]
    rfl
  have pcomp {a b : ℕ} (hab : a ≤ b) (z : c.pt) : t hab (p b z) = p a z := by
    change (c.π.app (op b) ≫ F.map (homOfLE hab).op).hom z = _
    rw [c.w]
  have hstab : ∀ j : ℕ, ∃ b : ℕ, ∃ hjb : j ≤ b, ∀ k (hbk : b ≤ k),
      LinearMap.range (t (hjb.trans hbk)) = LinearMap.range (p j) := by
    intro j
    obtain ⟨b, hjb, hle⟩ := hrange j
    refine ⟨b, hjb, fun k hbk => le_antisymm ?_ ?_⟩
    · rintro _ ⟨x, rfl⟩
      rw [← tcomp hjb hbk x]
      exact hle ⟨_, rfl⟩
    · rintro _ ⟨z, rfl⟩
      exact ⟨p k z, pcomp _ z⟩
  have hpn : Function.Injective (p n) := hinj n le_rfl
  obtain ⟨i, hni, hstn⟩ := hstab n
  have hrangeI : LinearMap.range (t hni) = LinearMap.range (p n) := hstn i le_rfl
  let e : c.pt ≃ₗ[R] LinearMap.range (p n) := LinearEquiv.ofInjective (p n) hpn
  let q : F.obj (op i) →ₗ[R] LinearMap.range (p n) :=
    LinearMap.codRestrict (LinearMap.range (p n)) (t hni) (fun x => by
      rw [← hrangeI]
      exact ⟨x, rfl⟩)
  let sₗ : F.obj (op i) →ₗ[R] c.pt := e.symm.toLinearMap.comp q
  have hfactor_apply (y : F.obj (op i)) : p n (sₗ y) = t hni y := by
    simp [e, q, sₗ]
  have hretract (z : c.pt) : sₗ (p i z) = z := by
    apply hpn
    rw [hfactor_apply, pcomp]
  refine ⟨op i, ModuleCat.ofHom sₗ, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext z
    exact hretract z
  · intro j
    let jn := j.unop
    obtain ⟨cj, hjcj, hstabj⟩ := hstab jn
    let k := max i cj
    have hik : i ≤ k := le_max_left _ _
    have hckj : cj ≤ k := le_max_right _ _
    have hjk : jn ≤ k := hjcj.trans hckj
    have hrj : LinearMap.range (t hjk) = LinearMap.range (p jn) := hstabj k hckj
    have hnk : n ≤ k := hni.trans hik
    refine ⟨op k, op (homOfLE hik), op (homOfLE hjk), ?_⟩
    apply ModuleCat.hom_ext
    ext x
    change t hjk x = p jn (sₗ (t hik x))
    by_cases hjn : jn ≤ n
    · calc
        t hjk x = t hjn (t hnk x) := (tcomp hjn hnk x).symm
        _ = t hjn (t hni (t hik x)) := by rw [tcomp hni hik]
        _ = t hjn (p n (sₗ (t hik x))) := by rw [hfactor_apply]
        _ = p jn (sₗ (t hik x)) := pcomp hjn _
    · have hnj : n ≤ jn := Nat.le_of_not_ge hjn
      obtain ⟨z, hz⟩ : t hjk x ∈ LinearMap.range (p jn) := by
        rw [← hrj]
        exact ⟨x, rfl⟩
      have hzs : z = sₗ (t hik x) := hpn (by
        calc
          p n z = t hnj (p jn z) := (pcomp hnj z).symm
          _ = t hnj (t hjk x) := by rw [hz]
          _ = t hnk x := tcomp hnj hjk x
          _ = t hni (t hik x) := (tcomp hni hik x).symm
          _ = p n (sₗ (t hik x)) := (hfactor_apply _).symm)
      rw [← hz, hzs]

/-! ### Naturality of the connecting map -/

section Naturality

variable {A : Type u} [CommRing A]

/-- **The connecting map of the long exact sequence of local cohomology is natural** with
respect to morphisms of short exact sequences of modules. -/
theorem localCohomologyδ_naturality (T : Set (PrimeSpectrum A))
    {S₁ S₂ : ShortComplex (ModuleCat.{max u v} A)} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (φ : S₁ ⟶ S₂) (i j : ℤ) (h : i + 1 = j) :
    localCohomologyMap.{u, v} A T i φ.τ₃ ≫ localCohomologyδ.{u, v} T h₂ i j h =
      localCohomologyδ.{u, v} T h₁ i j h ≫ localCohomologyMap.{u, v} A T j φ.τ₁ :=
  (DerivedCategory.homologyFunctor _ 0).homologySequenceδ_naturality
    ((derivedSectionsWithSupportIn.{u, v} A T).mapTriangle.map
      (ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ)) i j h

end Naturality

/-! ### The cokernel of `H^i_T(M) → H^i_T(M/IⁿM)` -/

section Cokernel

variable {A : Type u} [CommRing A]

/-- The morphism from `0 → IᵏM → M → M/IᵏM → 0` to `0 → IⁿM → M → M/IⁿM → 0` for `n ≤ k`. -/
def idealPowerShortComplexMap (I : Ideal A) (M : ModuleCat.{max u v} A) {n k : ℕ}
    (h : n ≤ k) :
    idealPowerShortComplex.{u, v} I M k ⟶ idealPowerShortComplex.{u, v} I M n where
  τ₁ := (idealPowerTower.{u, v} I M).map (homOfLE h).op
  τ₂ := 𝟙 M
  τ₃ := (idealPowerQuotientTower.{u, v} I M).map (homOfLE h).op
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- **The transition images of `{H^i_T(M/IⁿM)}` lie in the image of `H^i_T(M)`** as soon as the
classes of `H^{i+1}_T(IᵏM)` dying in `H^{i+1}_T(M)` die in `H^{i+1}_T(IⁿM)`: the image of
`H^i_T(M) → H^i_T(M/IⁿM)` is the kernel of the connecting map into `H^{i+1}_T(IⁿM)`, and the
connecting map is natural in `n`. -/
theorem range_map_localCohomologyAdicTower_le (T : Set (PrimeSpectrum A)) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (i : ℤ) {n k : ℕ} (h : n ≤ k)
    (hz : ∀ ξ : (localCohomologyWithSupportInModuleFunctor.{u, v} A T (i + 1)).obj
        ((idealPowerTower.{u, v} I M).obj (op k)),
      ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (i + 1)).map
        (idealPowerInclusion.{u, v} I M k)).hom ξ = 0 →
      ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (i + 1)).map
        ((idealPowerTower.{u, v} I M).map (homOfLE h).op)).hom ξ = 0) :
    LinearMap.range ((localCohomologyAdicTower.{u, v} A T I i M).map (homOfLE h).op).hom ≤
      LinearMap.range ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op n)).hom := by
  rintro _ ⟨x, rfl⟩
  have hSn := idealPowerShortComplex_shortExact.{u, v} I M n
  have hSk := idealPowerShortComplex_shortExact.{u, v} I M k
  have hex := (ShortComplex.moduleCat_exact_iff _).mp
    (localCohomology_exact₃.{u, v} T hSn i (i + 1) rfl)
  have hnat := localCohomologyδ_naturality.{u, v} T hSk hSn
    (idealPowerShortComplexMap.{u, v} I M h) i (i + 1) rfl
  have hcomp := localCohomologyδ_comp_localCohomologyMap.{u, v} T hSk i (i + 1) rfl
  have hδ : (localCohomologyδ.{u, v} T hSn i (i + 1) rfl).hom
      (((localCohomologyAdicTower.{u, v} A T I i M).map (homOfLE h).op).hom x) = 0 := by
    have h1 := congrArg (fun f => f.hom x) hnat
    change (localCohomologyδ.{u, v} T hSn i (i + 1) rfl).hom
        ((localCohomologyMap.{u, v} A T i
          (idealPowerShortComplexMap.{u, v} I M h).τ₃).hom x) = _ at h1
    refine h1.trans ?_
    change ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (i + 1)).map
        ((idealPowerTower.{u, v} I M).map (homOfLE h).op)).hom
          ((localCohomologyδ.{u, v} T hSk i (i + 1) rfl).hom x) = 0
    refine hz _ ?_
    have h2 := congrArg (fun f => f.hom x) hcomp
    exact h2
  obtain ⟨y, hy⟩ := hex _ hδ
  exact ⟨y, hy⟩

end Cokernel

/-! ### The kernel condition in degree `s + 1` -/

section KernelCondition

variable {A : Type u} [CommRing A]

/-- A linear map carries `J • X` into `J • Y`. -/
theorem map_mem_smul_top {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (g : X →ₗ[A] Y) {J : Ideal A} {y : X} (hy : y ∈ J • (⊤ : Submodule A X)) :
    g y ∈ J • (⊤ : Submodule A Y) := by
  have hle : Submodule.map g (J • (⊤ : Submodule A X)) ≤ J • (⊤ : Submodule A Y) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨y, hy, rfl⟩

/-- An element of `Iᵖ` carries `I^q M` into `I^{p+q} M`. -/
theorem smul_mem_pow_smul_top {X : Type*} [AddCommGroup X] [Module A X] (I : Ideal A)
    {p q : ℕ} {a : A} (ha : a ∈ I ^ p) {x : X} (hx : x ∈ I ^ q • (⊤ : Submodule A X)) :
    a • x ∈ I ^ (p + q) • (⊤ : Submodule A X) := by
  have h := Submodule.smul_mem_smul ha hx
  rwa [← Submodule.mul_smul, ← pow_add] at h

/-- A vector all of whose coordinates lie in `J • X` lies in `J • Xʳ`. -/
theorem pi_mem_smul_top {X : Type*} [AddCommGroup X] [Module A X] {r : ℕ} (J : Ideal A)
    (y : Fin r → X) (hy : ∀ i, y i ∈ J • (⊤ : Submodule A X)) :
    y ∈ J • (⊤ : Submodule A (Fin r → X)) := by
  rw [← Finset.univ_sum_single y]
  exact Submodule.sum_mem _ fun i _ => map_mem_smul_top (LinearMap.single A (fun _ => X) i) (hy i)

variable (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M]

/-- The short exact sequence `0 → L ∩ IⁿN → IⁿN → IⁿQ → 0` attached to a submodule `L` of a
module `N` with quotient `Q = N/L`. -/
def idealPowerCokernelShortComplex {N : Type u} [AddCommGroup N] [Module A N]
    (L : Submodule A N) (n : ℕ) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk
    (ModuleCat.ofHom (Submodule.inclusion (inf_le_right :
      L ⊓ I ^ n • (⊤ : Submodule A N) ≤ I ^ n • (⊤ : Submodule A N))))
    (ModuleCat.ofHom (L.mkQ.restrict (q := I ^ n • (⊤ : Submodule A (N ⧸ L)))
      (fun y hy => map_mem_smul_top L.mkQ hy)) :
      ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A N)) ⟶
        (idealPowerTower.{u, u} I (ModuleCat.of A (N ⧸ L))).obj (op n))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero L).2 y.2.1)

/-- The sequence `0 → L ∩ IⁿN → IⁿN → IⁿQ → 0` is short exact. -/
theorem idealPowerCokernelShortComplex_shortExact {N : Type u} [AddCommGroup N] [Module A N]
    (L : Submodule A N) (n : ℕ) : (idealPowerCokernelShortComplex I L n).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    have hy' : L.mkQ y.1 = 0 := congrArg Subtype.val hy
    exact ⟨⟨y.1, (Submodule.Quotient.mk_eq_zero L).1 hy', y.2⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 (Submodule.inclusion_injective inf_le_right)
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    rintro ⟨z, hz⟩
    have hz' : z ∈ Submodule.map L.mkQ (I ^ n • (⊤ : Submodule A N)) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
      exact hz
    obtain ⟨y, hy, rfl⟩ := hz'
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The morphism `(0 → L ∩ IᵏN → IᵏN → IᵏQ → 0) ⟶ (0 → L ∩ IⁿN → IⁿN → IⁿQ → 0)`, `n ≤ k`. -/
def idealPowerCokernelShortComplexMap {N : Type u} [AddCommGroup N] [Module A N]
    (L : Submodule A N) {n k : ℕ} (h : n ≤ k) :
    idealPowerCokernelShortComplex I L k ⟶ idealPowerCokernelShortComplex I L n where
  τ₁ := ModuleCat.ofHom (Submodule.inclusion
    (inf_le_inf_left L (Submodule.pow_smul_top_le I N h)))
  τ₂ := ModuleCat.ofHom (Submodule.inclusion (Submodule.pow_smul_top_le I N h))
  τ₃ := (idealPowerTower.{u, u} I (ModuleCat.of A (N ⧸ L))).map (homOfLE h).op
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Composing two transition maps of `{IⁿM}` gives the transition map of the composite bound. -/
theorem idealPowerTower_map_homOfLE_comp (N : ModuleCat.{u} A) {a b c : ℕ} (h₁ : a ≤ b)
    (h₂ : b ≤ c) (h₃ : a ≤ c) :
    (idealPowerTower.{u, u} I N).map (homOfLE h₂).op ≫
        (idealPowerTower.{u, u} I N).map (homOfLE h₁).op =
      (idealPowerTower.{u, u} I N).map (homOfLE h₃).op := by
  rw [← Functor.map_comp]
  rfl

/-- Applying `H^j_T` to two composable maps of modules, elementwise. -/
theorem localCohomologyWithSupportInModuleFunctor_map_comp_apply (j : ℤ)
    {X Y Z : ModuleCat.{u} A} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : f ≫ g = h)
    (x : (localCohomologyWithSupportInModuleFunctor.{u, u} A T j).obj X) :
    ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map g).hom
        (((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map f).hom x) =
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map h).hom x := by
  rw [← hfg, Functor.map_comp]
  rfl

/-- Applying `H^j_T` to two factorizations of the same map of modules gives the same result. -/
private theorem localCohomologyWithSupportInModuleFunctor_map_map_eq (j : ℤ)
    {X Y Y' Z : ModuleCat.{u} A} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'} {g' : Y' ⟶ Z}
    (hfg : f ≫ g = f' ≫ g')
    (x : (localCohomologyWithSupportInModuleFunctor.{u, u} A T j).obj X) :
    ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map g).hom
        (((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map f).hom x) =
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map g').hom
        (((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map f').hom x) :=
  (localCohomologyWithSupportInModuleFunctor_map_comp_apply T j rfl x).trans
    (localCohomologyWithSupportInModuleFunctor_map_comp_apply T j hfg.symm x).symm

/-- **The diagram chase of [Stacks, Tag 0EIE] in degree `s + 1`.** Let `L ⊆ N` be a submodule
with quotient `Q = N/L`, contained in `I^{m₀}N`, and satisfying the Artin–Rees inclusion
`L ∩ I^{m+c}N ⊆ IᵐL`. Suppose that classes of `H^{s+1}_T(IᵏN)` dying in `H^{s+1}_T(I^{m₀}N)`
die in `H^{s+1}_T(IᵐN)` for `k ≫ m ≥ m₀`, and that `{H^s_T(IⁿQ)}` is pro-zero. Then for every
`m` there is `k ≥ m` such that classes of `H^{s+1}_T(IᵏL)` dying in `H^{s+1}_T(L)` die in
`H^{s+1}_T(IᵐL)`. -/
theorem exists_forall_localCohomology_idealPower_submodule_eq_zero (s : ℤ)
    {N : Type u} [AddCommGroup N] [Module A N] (L : Submodule A N) (m₀ c₀ : ℕ)
    (hLm₀ : L ≤ I ^ m₀ • (⊤ : Submodule A N))
    (hAR : ∀ m : ℕ, L ⊓ I ^ (m + c₀) • (⊤ : Submodule A N) ≤ I ^ m • L)
    (hW : ∀ m : ℕ, ∀ hm : m₀ ≤ m, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k)
      (x : (localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).obj
        ((idealPowerTower.{u, u} I (ModuleCat.of A N)).obj (op k))),
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
        ((idealPowerTower.{u, u} I (ModuleCat.of A N)).map
          (homOfLE (hm.trans (hmc.trans hck))).op)).hom x = 0 →
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
        ((idealPowerTower.{u, u} I (ModuleCat.of A N)).map
          (homOfLE (hmc.trans hck)).op)).hom x = 0)
    (hQ : ∀ m : ℕ, ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, u} A T s).map
        ((idealPowerTower.{u, u} I (ModuleCat.of A (N ⧸ L))).map (homOfLE h).op) = 0)
    (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k, ∀ ξ : (localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).obj
        (ModuleCat.of A ↥(I ^ k • L)),
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
        (ModuleCat.ofHom (Submodule.inclusion (Submodule.smul_le_right :
          I ^ k • L ≤ L)))).hom ξ = 0 →
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
        (ModuleCat.ofHom (Submodule.inclusion
          (Submodule.smul_mono_left (Ideal.pow_le_pow_right h) : I ^ k • L ≤ I ^ m • L)))).hom
          ξ = 0 := by
  obtain ⟨m₁, hm₁, hQz⟩ := hQ (m + c₀)
  set m₂ := max m₁ m₀ with hm₂def
  have hm₁₂ : m₁ ≤ m₂ := le_max_left _ _
  have hm₀₂ : m₀ ≤ m₂ := le_max_right _ _
  have hQz₂ : (localCohomologyWithSupportInModuleFunctor.{u, u} A T s).map
      ((idealPowerTower.{u, u} I (ModuleCat.of A (N ⧸ L))).map
        (homOfLE (hm₁.trans hm₁₂)).op) = 0 := by
    rw [← idealPowerTower_map_homOfLE_comp I (ModuleCat.of A (N ⧸ L)) hm₁ hm₁₂,
      Functor.map_comp, hQz, comp_zero]
  obtain ⟨c, hm₂c, hc⟩ := hW m₂ hm₀₂
  have hmc : m ≤ c := (Nat.le_add_right m c₀).trans (hm₁.trans (hm₁₂.trans hm₂c))
  refine ⟨c, hmc, fun ξ hξ => ?_⟩
  -- the image of `ξ` in `H^{s+1}_T(I^cN)`
  let x := ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
    (ModuleCat.ofHom (Submodule.inclusion
    (Submodule.smul_mono le_rfl le_top : I ^ c • L ≤ I ^ c • (⊤ : Submodule A N))))).hom ξ
  have hx₀ : ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
      ((idealPowerTower.{u, u} I (ModuleCat.of A N)).map
      (homOfLE (hm₀₂.trans (hm₂c.trans le_rfl))).op)).hom x = 0 := by
    refine (localCohomologyWithSupportInModuleFunctor_map_map_eq T (s + 1)
      (g' := ModuleCat.ofHom (Submodule.inclusion hLm₀))
      (f' := ModuleCat.ofHom (Submodule.inclusion (Submodule.smul_le_right :
          I ^ c • L ≤ L))) (by rfl) ξ).trans ?_
    rw [hξ]
    exact map_zero _
  have hxm₂ := hc c le_rfl x hx₀
  -- the image `ξ'` of `ξ` in `H^{s+1}_T(L ∩ I^{m₂}N)` lifts along the connecting map
  have hcm₂ : I ^ c • L ≤ L ⊓ I ^ m₂ • (⊤ : Submodule A N) :=
    le_inf Submodule.smul_le_right (Submodule.smul_mono (Ideal.pow_le_pow_right hm₂c) le_top)
  let ξ' := ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
    (ModuleCat.ofHom (Submodule.inclusion hcm₂))).hom ξ
  have hS₂ := idealPowerCokernelShortComplex_shortExact I L m₂
  have hξ'f : (localCohomologyMap.{u, u} A T (s + 1)
      (idealPowerCokernelShortComplex I L m₂).f).hom ξ' = 0 := by
    exact (localCohomologyWithSupportInModuleFunctor_map_map_eq T (s + 1)
      (g' := (idealPowerTower.{u, u} I (ModuleCat.of A N)).map (homOfLE hm₂c).op) (by rfl) ξ).trans
      hxm₂
  obtain ⟨η, hη⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (localCohomology_exact₁.{u, u} T hS₂ s (s + 1) rfl) ξ' hξ'f
  -- naturality of the connecting map kills `ξ'` in `H^{s+1}_T(L ∩ I^{m+c₀}N)`
  have hS₁ := idealPowerCokernelShortComplex_shortExact I L (m + c₀)
  have hle : m + c₀ ≤ m₂ := hm₁.trans hm₁₂
  have hnat := localCohomologyδ_naturality.{u, u} T hS₂ hS₁
    (idealPowerCokernelShortComplexMap I L hle) s (s + 1) rfl
  have hτ₃ : localCohomologyMap.{u, u} A T s (idealPowerCokernelShortComplexMap I L hle).τ₃ = 0 :=
    hQz₂
  have hξ'z : (localCohomologyMap.{u, u} A T (s + 1)
      (idealPowerCokernelShortComplexMap I L hle).τ₁).hom ξ' = 0 := by
    have h1 := congrArg (fun f => f.hom η) hnat
    simp only [hτ₃, zero_comp] at h1
    change 0 = (localCohomologyMap.{u, u} A T (s + 1)
      (idealPowerCokernelShortComplexMap I L hle).τ₁).hom
        ((localCohomologyδ.{u, u} T hS₂ s (s + 1) rfl).hom η) at h1
    rw [hη] at h1
    exact h1.symm
  -- and `L ∩ I^{m+c₀}N ⊆ IᵐL`
  have h1 := localCohomologyWithSupportInModuleFunctor_map_comp_apply T (s + 1)
    (f := ModuleCat.ofHom (Submodule.inclusion hcm₂))
    (g := (idealPowerCokernelShortComplexMap I L hle).τ₁ ≫
      ModuleCat.ofHom (Submodule.inclusion (hAR m)))
    (h := ModuleCat.ofHom (Submodule.inclusion
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmc) : I ^ c • L ≤ I ^ m • L))) rfl ξ
  refine h1.symm.trans (((localCohomologyWithSupportInModuleFunctor_map_comp_apply T (s + 1)
    (f := (idealPowerCokernelShortComplexMap I L hle).τ₁)
    (g := ModuleCat.ofHom (Submodule.inclusion (hAR m))) rfl _).symm).trans ?_)
  change ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map _).hom
    ((localCohomologyMap.{u, u} A T (s + 1)
      (idealPowerCokernelShortComplexMap I L hle).τ₁).hom ξ') = 0
  exact (congrArg (((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
    (ModuleCat.ofHom (Submodule.inclusion (hAR m)))).hom) hξ'z).trans (map_zero _)

/-- `H^j_T` is an additive functor. -/
instance localCohomologyWithSupportInModuleFunctor_additive (j : ℤ) :
    (localCohomologyWithSupportInModuleFunctor.{u, u} A T j).Additive := by
  unfold localCohomologyWithSupportInModuleFunctor
  infer_instance

/-- An element of `H^j_T(IⁿMʳ)` all of whose coordinates in `H^j_T(IⁿM)` vanish is zero: `H^j_T`
is additive and the identity of `IⁿMʳ` is the sum of the coordinate idempotents. -/
theorem eq_zero_of_forall_localCohomology_proj_eq_zero (j : ℤ) {r : ℕ} (n : ℕ)
    (ζ : (localCohomologyWithSupportInModuleFunctor.{u, u} A T j).obj
      (ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A (Fin r → M)))))
    (hζ : ∀ i : Fin r, ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map
      (ModuleCat.ofHom ((LinearMap.proj i : (Fin r → M) →ₗ[A] M).restrict
        (q := I ^ n • (⊤ : Submodule A M))
        (fun _y hy => map_mem_smul_top (LinearMap.proj i) hy)))).hom ζ = 0) :
    ζ = 0 := by
  let pr (i : Fin r) : ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A (Fin r → M))) ⟶
      ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A M)) :=
    ModuleCat.ofHom ((LinearMap.proj i : (Fin r → M) →ₗ[A] M).restrict
      (q := I ^ n • (⊤ : Submodule A M)) (fun y hy => map_mem_smul_top (LinearMap.proj i) hy))
  let ι (i : Fin r) : ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A M)) ⟶
      ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A (Fin r → M))) :=
    ModuleCat.ofHom ((LinearMap.single A (fun _ => M) i).restrict
      (q := I ^ n • (⊤ : Submodule A (Fin r → M)))
      (fun y hy => map_mem_smul_top (LinearMap.single A (fun _ => M) i) hy))
  have hsum : ∑ i, pr i ≫ ι i = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change (∑ i, (pr i ≫ ι i)).hom y = (y : Fin r → M)
    rw [ModuleCat.hom_sum, LinearMap.sum_apply, Submodule.coe_sum]
    exact Finset.univ_sum_single (y : Fin r → M)
  have h1 : ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map (𝟙 _)).hom ζ = ζ := by
    simp
  rw [← h1, ← hsum, Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Functor.map_comp]
  change ((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map (ι i)).hom
    (((localCohomologyWithSupportInModuleFunctor.{u, u} A T j).map (pr i)).hom ζ) = 0
  rw [hζ i, map_zero]

/-- The stable-image assertion of Tag 0EFX for `M`, in degree `s + 1`, implies the same assertion
for `Mʳ`, coordinatewise. -/
theorem stableImage_pi (s : ℤ) {r : ℕ} (m₀ : ℕ)
    (hb : ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (idealPowerTower.{u, u} I (ModuleCat.of A M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).obj (op k),
        ((idealPowerTower.{u, u} I (ModuleCat.of A M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, u} I (ModuleCat.of A M) ⋙
            localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
              (homOfLE hm₀m).op).hom →
        ((idealPowerTower.{u, u} I (ModuleCat.of A M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0) :
    ∀ m : ℕ, ∀ hm : m₀ ≤ m, ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k)
      (x : (localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).obj
        ((idealPowerTower.{u, u} I (ModuleCat.of A (Fin r → M))).obj (op k))),
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
        ((idealPowerTower.{u, u} I (ModuleCat.of A (Fin r → M))).map
          (homOfLE (hm.trans (hmc.trans hck))).op)).hom x = 0 →
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
        ((idealPowerTower.{u, u} I (ModuleCat.of A (Fin r → M))).map
          (homOfLE (hmc.trans hck)).op)).hom x = 0 := by
  intro m hm
  obtain ⟨c, hmc, hc⟩ := hb m hm
  refine ⟨c, hmc, fun k hck x hx => ?_⟩
  let pr (n : ℕ) (i : Fin r) : ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A (Fin r → M))) ⟶
      ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A M)) :=
    ModuleCat.ofHom ((LinearMap.proj i : (Fin r → M) →ₗ[A] M).restrict
      (q := I ^ n • (⊤ : Submodule A M)) (fun y hy => map_mem_smul_top (LinearMap.proj i) hy))
  refine eq_zero_of_forall_localCohomology_proj_eq_zero T I M (s + 1) m _ fun i => ?_
  have hcomm (a b : ℕ) (hab : a ≤ b) :
      (idealPowerTower.{u, u} I (ModuleCat.of A (Fin r → M))).map (homOfLE hab).op ≫ pr a i =
        pr b i ≫ (idealPowerTower.{u, u} I (ModuleCat.of A M)).map (homOfLE hab).op := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl
  refine (localCohomologyWithSupportInModuleFunctor_map_map_eq T (s + 1)
    (hcomm m k (hmc.trans hck)) x).trans ?_
  refine hc k hck _ ?_
  rw [LinearMap.mem_ker]
  refine ((localCohomologyWithSupportInModuleFunctor_map_comp_apply T (s + 1)
      (idealPowerTower_map_homOfLE_comp I (ModuleCat.of A M) hm (hmc.trans hck)
        (hm.trans (hmc.trans hck))) _).trans
    (localCohomologyWithSupportInModuleFunctor_map_map_eq T (s + 1)
      (hcomm m₀ k (hm.trans (hmc.trans hck))) x).symm).trans ?_
  rw [hx]
  exact map_zero _

/-- **The kernel condition of [Stacks, Tag 0EIE] in degree `s + 1`.** Let `A` be Noetherian, `M`
a finite `A`-module and `f₁, …, f_r` generators of `I^{m₀}`, where `m₀` is the integer of the
stable-image assertion of Tag 0EFX for `M` in degree `s + 1`. Let `Q` be the cokernel of
`M → Mʳ, x ↦ (fᵢx)`, and suppose `{H^s_T(IⁿQ)}` is pro-zero. Then for every `m` there is `k ≥ m`
such that every class of `H^{s+1}_T(IᵏM)` dying in `H^{s+1}_T(M)` dies in `H^{s+1}_T(IᵐM)`.

*Argument.* The image `L ⊆ I^{m₀}Mʳ` of `M` satisfies the Artin–Rees inclusion
`L ∩ I^{m+c}Mʳ ⊆ IᵐL`, and the chase
`exists_forall_localCohomology_idealPower_submodule_eq_zero` gives the assertion for `L`. The
kernel of `M → L` is killed by `I^{m₀}`, so by Artin–Rees it meets `IᵃM` trivially for `a ≫ 0`,
and `IᵃM → IᵃL` is an isomorphism; this transports the assertion from `L` back to `M`. -/
theorem exists_forall_localCohomology_idealPowerTower_eq_zero_of_inclusion [IsNoetherianRing A]
    [Module.Finite A M] (s : ℤ) (m₀ : ℕ)
    (hb : ∀ (m : ℕ) (hm₀m : m₀ ≤ m), ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (idealPowerTower.{u, u} I (ModuleCat.of A M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).obj (op k),
        ((idealPowerTower.{u, u} I (ModuleCat.of A M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, u} I (ModuleCat.of A M) ⋙
            localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
              (homOfLE hm₀m).op).hom →
        ((idealPowerTower.{u, u} I (ModuleCat.of A M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0)
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I ^ m₀)
    (φ : M →ₗ[A] (Fin r → M)) (hφ : ∀ x i, φ x i = f i • x)
    (hQ : ∀ m : ℕ, ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, u} A T s).map
        ((idealPowerTower.{u, u} I (ModuleCat.of A ((Fin r → M) ⧸ LinearMap.range φ))).map
          (homOfLE h).op) = 0)
    (m : ℕ) :
    ∃ k : ℕ, ∃ h : m ≤ k, ∀ ξ : (localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).obj
        ((idealPowerTower.{u, u} I (ModuleCat.of A M)).obj (op k)),
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
        (idealPowerInclusion.{u, u} I (ModuleCat.of A M) k)).hom ξ = 0 →
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
        ((idealPowerTower.{u, u} I (ModuleCat.of A M)).map (homOfLE h).op)).hom ξ = 0 := by
  set L := LinearMap.range φ with hLdef
  have hLm₀ : L ≤ I ^ m₀ • (⊤ : Submodule A (Fin r → M)) := by
    rintro _ ⟨x, rfl⟩
    refine pi_mem_smul_top _ _ fun i => ?_
    rw [hφ]
    exact Submodule.smul_mem_smul (hf ▸ Ideal.subset_span ⟨i, rfl⟩) Submodule.mem_top
  obtain ⟨c₀, hc₀⟩ := Ideal.exists_pow_inf_eq_pow_smul I L
  have hAR : ∀ m : ℕ, L ⊓ I ^ (m + c₀) • (⊤ : Submodule A (Fin r → M)) ≤ I ^ m • L := by
    intro m
    rw [inf_comm, hc₀ (m + c₀) (Nat.le_add_left _ _), Nat.add_sub_cancel]
    exact Submodule.smul_mono le_rfl inf_le_right
  have chase := exists_forall_localCohomology_idealPower_submodule_eq_zero T I s L m₀ c₀ hLm₀ hAR
    (stableImage_pi T I M s m₀ hb) hQ
  obtain ⟨a₁, ha₁⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.ker φ)
  have hann : I ^ m₀ ≤ (LinearMap.ker φ).annihilator := by
    rw [← hf, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_annihilator]
    intro x hx
    have h := congrFun (LinearMap.mem_ker.mp hx) i
    rwa [hφ] at h
  have hinj : ∀ a : ℕ, a₁ + m₀ ≤ a → ∀ x ∈ I ^ a • (⊤ : Submodule A M), φ x = 0 → x = 0 := by
    intro a ha x hx hφx
    have hmem : x ∈ I ^ a • (⊤ : Submodule A M) ⊓ LinearMap.ker φ := ⟨hx, hφx⟩
    rw [ha₁ a (by omega)] at hmem
    have hle : I ^ (a - a₁) • (I ^ a₁ • (⊤ : Submodule A M) ⊓ LinearMap.ker φ) ≤ ⊥ := by
      rw [← Submodule.annihilator_smul (LinearMap.ker φ)]
      exact Submodule.smul_mono ((Ideal.pow_le_pow_right (by omega)).trans hann) inf_le_right
    exact (Submodule.mem_bot A).mp (hle hmem)
  have hmap : ∀ n : ℕ, Submodule.map φ (I ^ n • (⊤ : Submodule A M)) = I ^ n • L := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top]
  set a := max m (a₁ + m₀) with hadef
  obtain ⟨k, hak, hk⟩ := chase a
  have hmk : m ≤ k := (le_max_left _ _).trans hak
  refine ⟨k, hmk, fun ξ hξ => ?_⟩
  have hmemk : ∀ x ∈ I ^ k • (⊤ : Submodule A M), φ x ∈ I ^ k • L := by
    intro x hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hmema : ∀ x ∈ I ^ a • (⊤ : Submodule A M), φ x ∈ I ^ a • L := by
    intro x hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  let φk : ModuleCat.of A ↥(I ^ k • (⊤ : Submodule A M)) ⟶ ModuleCat.of A ↥(I ^ k • L) :=
    ModuleCat.ofHom (φ.restrict hmemk)
  let φa : ↥(I ^ a • (⊤ : Submodule A M)) →ₗ[A] ↥(I ^ a • L) := φ.restrict hmema
  have hφa : Function.Bijective φa := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => Subtype.ext ?_, fun y => ?_⟩
    · exact hinj a (le_max_right _ _) x.1 x.2 (congrArg Subtype.val hx)
    · have hy : (y : Fin r → M) ∈ Submodule.map φ (I ^ a • (⊤ : Submodule A M)) := by
        rw [hmap]
        exact y.2
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e := LinearEquiv.ofBijective φa hφa
  let ψa : ModuleCat.of A ↥(I ^ a • L) ⟶ ModuleCat.of A ↥(I ^ a • (⊤ : Submodule A M)) :=
    ModuleCat.ofHom e.symm.toLinearMap
  let φL : ModuleCat.of A M ⟶ ModuleCat.of A ↥L := ModuleCat.ofHom φ.rangeRestrict
  have hcomm₁ : φk ≫ ModuleCat.ofHom (Submodule.inclusion (Submodule.smul_le_right :
      I ^ k • L ≤ L)) = idealPowerInclusion.{u, u} I (ModuleCat.of A M) k ≫ φL := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hcomm₂ : φk ≫ ModuleCat.ofHom (Submodule.inclusion
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right hak) : I ^ k • L ≤ I ^ a • L)) ≫ ψa =
      (idealPowerTower.{u, u} I (ModuleCat.of A M)).map (homOfLE hak).op := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change e.symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have hξL : ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
      (ModuleCat.ofHom (Submodule.inclusion (Submodule.smul_le_right :
        I ^ k • L ≤ L)))).hom
      (((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map φk).hom ξ) = 0 := by
    refine (localCohomologyWithSupportInModuleFunctor_map_map_eq T (s + 1) hcomm₁ ξ).trans
      ((congrArg _ hξ).trans (map_zero _))
  have hξa := hk _ hξL
  have hka : ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
      ((idealPowerTower.{u, u} I (ModuleCat.of A M)).map (homOfLE hak).op)).hom ξ = 0 := by
    exact (localCohomologyWithSupportInModuleFunctor_map_comp_apply T (s + 1) hcomm₂ ξ).symm.trans
      ((localCohomologyWithSupportInModuleFunctor_map_comp_apply T (s + 1)
        (g := ψa) rfl _).symm.trans
        ((congrArg ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map ψa).hom
          hξa).trans
          (map_zero _)))
  exact (localCohomologyWithSupportInModuleFunctor_map_comp_apply T (s + 1)
    (idealPowerTower_map_homOfLE_comp I (ModuleCat.of A M)
      (le_max_left m (a₁ + m₀)) hak hmk) ξ).symm.trans
    ((congrArg ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map _).hom hka).trans
      (map_zero _))

end KernelCondition

/-! ### Essential constancy -/

section Assembly

variable {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : Type u)
  [AddCommGroup M] [Module A M]

/-- **Essential constancy of `{H^i_T(M/IⁿM)}` with value `H^i_T(M)`, for `i ≤ s`, from the
pro-zero assertion in degrees `≤ s` and the kernel condition in degree `s + 1`.**

*Argument.* By part (1) of Tag 0EFY the projections `H^i_T(M) → H^i_T(M/IⁿM)` are injective for
`n ≫ 0`. The image of `H^i_T(M) → H^i_T(M/IⁿM)` is the kernel of the connecting map into
`H^{i+1}_T(IⁿM)`, which is natural in `n`; so the transition image from `H^i_T(M/IᵏM)` lies in
it as soon as the classes of `H^{i+1}_T(IᵏM)` dying in `H^{i+1}_T(M)` die in `H^{i+1}_T(IⁿM)`.
For `i < s` this holds because `{H^{i+1}_T(IⁿM)}` is pro-zero, and for `i = s` it is the kernel
condition. Eventually injective projections whose images contain the transition images are
essential-constancy data. -/
theorem exists_isEssentiallyConstantWith_localCohomologyAdicCone_of_proZero (s : ℤ)
    (ha : ∀ i : ℤ, i ≤ s → ∀ m : ℕ, ∃ k : ℕ, ∃ h : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, u} A T i).map
        ((idealPowerTower.{u, u} I (ModuleCat.of A M)).map (homOfLE h).op) = 0)
    (hP : ∀ m : ℕ, ∃ k : ℕ, ∃ h : m ≤ k,
      ∀ ξ : (localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).obj
        ((idealPowerTower.{u, u} I (ModuleCat.of A M)).obj (op k)),
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
        (idealPowerInclusion.{u, u} I (ModuleCat.of A M) k)).hom ξ = 0 →
      ((localCohomologyWithSupportInModuleFunctor.{u, u} A T (s + 1)).map
        ((idealPowerTower.{u, u} I (ModuleCat.of A M)).map (homOfLE h).op)).hom ξ = 0)
    (i : ℤ) (hi : i ≤ s) :
    ∃ (j : ℕᵒᵖ) (σ : (localCohomologyAdicTower.{u, u} A T I i (ModuleCat.of A M)).obj j ⟶
        (localCohomologyAdicCone.{u, u} A T I i (ModuleCat.of A M)).pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith
        (localCohomologyAdicTower.{u, u} A T I i (ModuleCat.of A M))
        (localCohomologyAdicCone.{u, u} A T I i (ModuleCat.of A M)) j σ := by
  obtain ⟨m₀, hm₀⟩ := exists_forall_injective_localCohomologyAdicProjection_of_proZero.{u, u}
    T I (ModuleCat.of A M) s (fun i hi => ha i hi 0)
  refine exists_isEssentiallyConstantWith_of_injective_of_range_le _ (n := m₀)
    (fun m hm => hm₀ i hi m hm) fun j => ?_
  rcases lt_or_eq_of_le hi with hlt | rfl
  · obtain ⟨k, h, hz⟩ := ha (i + 1) (by omega) j
    refine ⟨k, h, range_map_localCohomologyAdicTower_le.{u, u} T I _ i h fun ξ _ => ?_⟩
    rw [hz]
    rfl
  · obtain ⟨k, h, hk⟩ := hP j
    exact ⟨k, h, range_map_localCohomologyAdicTower_le.{u, u} T I _ i h hk⟩

end Assembly

/-! ### Theorem 0EIE in the bootstrap situation -/

namespace Bootstrap

open Stacks.Algebraization

/-- **Theorem 0EIE from Lemma 0EFX.** In the bootstrap situation of [Stacks, Tag 0EFU], for
`i ≤ s` the inverse system `{H^i_T(M/IⁿM)}` is essentially constant with value `H^i_T(M)`,
provided both assertions of [Stacks, Tag 0EFX] hold for every bootstrap situation: `hXa`, the
systems `{H^i_T(IⁿM)}` are pro-zero for `i ≤ s`, and `hXb`, in degree `s + 1` the transition
images inject into a fixed term (in the shape of the conclusion of
`Stacks.LocalCohomology.exists_eventually_injective_image_idealPowerTower_of_local`).

*Argument.* Let `m₀` be the integer of `hXb` for `S` and `f₁, …, f_r` generators of `I^{m₀}`.
The cokernel `Q` of `M → Mʳ, x ↦ (fⱼx)` is again a bootstrap situation
(`Stacks.Algebraization.BootstrapSituation.cokernel`), so `hXa` makes `{H^s_T(IⁿQ)}` pro-zero.
Together with `hXb` for `M`, this gives the kernel condition in degree `s + 1`
(`exists_forall_localCohomology_idealPowerTower_eq_zero_of_inclusion`). That condition and `hXa`
for `M` give essential constancy
(`exists_isEssentiallyConstantWith_localCohomologyAdicCone_of_proZero`). -/
theorem exists_isEssentiallyConstantWith_of_proZero
    (hXa : ∀ S' : BootstrapSituation.{u, u, w}, ∀ i : ℤ, i ≤ S'.s → ∀ m : ℕ, ∃ k : ℕ,
      ∃ h : m ≤ k,
        (localCohomologyWithSupportInModuleFunctor.{u, u} S'.A S'.T i).map
          ((idealPowerTower.{u, u} S'.I (ModuleCat.of S'.A S'.M)).map (homOfLE h).op) = 0)
    (hXb : ∀ S' : BootstrapSituation.{u, u, w}, ∃ m₀ : ℕ, ∀ (m : ℕ) (hm₀m : m₀ ≤ m),
      ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      ∀ x : (idealPowerTower.{u, u} S'.I (ModuleCat.of S'.A S'.M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} S'.A S'.T (S'.s + 1)).obj (op k),
        ((idealPowerTower.{u, u} S'.I (ModuleCat.of S'.A S'.M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} S'.A S'.T (S'.s + 1)).map
            (homOfLE (hmc.trans hck)).op).hom x ∈
          LinearMap.ker ((idealPowerTower.{u, u} S'.I (ModuleCat.of S'.A S'.M) ⋙
            localCohomologyWithSupportInModuleFunctor.{u, u} S'.A S'.T (S'.s + 1)).map
              (homOfLE hm₀m).op).hom →
        ((idealPowerTower.{u, u} S'.I (ModuleCat.of S'.A S'.M) ⋙
          localCohomologyWithSupportInModuleFunctor.{u, u} S'.A S'.T (S'.s + 1)).map
            (homOfLE (hmc.trans hck)).op).hom x = 0)
    (S : BootstrapSituation.{u, u, w}) (i : ℤ) (hi : i ≤ S.s) :
    ∃ (j : ℕᵒᵖ) (σ : (Bootstrap.tower.{u, u} S i).obj j ⟶ (Bootstrap.cone.{u, u} S i).pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith
        (Bootstrap.tower.{u, u} S i) (Bootstrap.cone.{u, u} S i) j σ := by
  obtain ⟨m₀, hb⟩ := hXb S
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (S.I ^ m₀))
  have hP := exists_forall_localCohomology_idealPowerTower_eq_zero_of_inclusion S.T S.I S.M
    S.s m₀ hb f hf (generatorMap S.M f) (fun x i => rfl)
    (hXa (S.cokernel f m₀ hf) S.s le_rfl)
  exact exists_isEssentiallyConstantWith_localCohomologyAdicCone_of_proZero S.T S.I S.M S.s
    (hXa S) hP i hi

end Bootstrap

end Stacks.LocalCohomology

end
