module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.PowerEpi
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseShortExact
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# Exactness of the symmetric presentation sequence of Tag 01CJ

Let `O` be a sheaf of commutative rings on a site and let `M₂ ⟶ M₁ ⟶ M ⟶ 0` be an exact
sequence of sheaves of `O`-modules. Tag 01CJ asserts that in every degree `n = 1 + k` with
`k ≥ 0` the three-term sequence

`M₂ ⊗ Sym^k(M₁) ⟶ Symⁿ(M₁) ⟶ Symⁿ(M) ⟶ 0`

is exact. Its two maps and the fact that they compose to zero are built in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences`; epimorphy of the
second
map is `SheafOfModules.epi_descComp_app_symmetric`. **This file proves exactness at the middle
term**, and therefore completes the symmetric half of the tag.

## The route

The proof is the source's: it is the purely algebraic Tag 00DO
(`symmetric_power_presentation` in `StacksFrontier.LinearAlgebra.SymmetricPower.Presentation`)
plus exactness of sheafification. No stalk and no comparison of symmetric powers with
symmetric powers of stalks appears anywhere, so the argument holds over an arbitrary site.

1. **Replace `M` by the presheaf cokernel of `q`.** Cokernels of presheaves of modules are
   computed sectionwise, so if `Q = coker q.val` then `M₂(U) ⟶ M₁(U) ⟶ Q(U) ⟶ 0` is exact for
   *every* `U`, which is what Tag 00DO consumes. The sheaf `M` is only the *sheaf* cokernel, so
   `M₂(U) ⟶ M₁(U) ⟶ M(U)` is in general not exact and `00DO` cannot be applied to it directly.
2. **Apply Tag 00DO over each object.** The sectionwise symmetric powers of
   `PresheafOfModules.symPowInt` have `SymPow.symmetricPower` as their sections and
   the objectwise tensor product has the algebraic tensor product as its sections, so
   `PresheafOfModules.exact_symmetricMulPresheaf_shortComplex` is Tag 00DO read over each `U`,
   assembled with `PresheafOfModules.exact_of_sectionwise`.
3. **Sheafify.** `PresheafOfModules.sheafification` preserves finite limits (Mathlib) and is a
   left adjoint, so it is exact and carries the sequence of (2) to an exact sequence of sheaves
   of modules.
4. **Identify the three terms.** The middle term is `Symⁿ(M₁)` on the nose, because
   `Stacks.GradedAlgebra.sheafify_piece` is `rfl`. For the outer terms,
   `SheafOfModules.symmetricTensorSheafifyHom` compares the sheafification of the objectwise
   tensor product with the tensor product of the sheaves, and
   `SheafOfModules.symmetricCokernelPieceIso` identifies `Symⁿ` of the sheafification of `Q`
   with `Symⁿ(M)` — the two are symmetric algebras of the same sheaf of modules, by
   `PresheafOfModules.isSymmetricAlgebra_sheafify_symmetricAlgebra` and
   `SheafOfModules.cokernelSheafifyIso`, hence canonically isomorphic in every degree.

## Main definitions

* `SheafOfModules.cokernelSheafifyIso`: the sheafification of the presheaf cokernel of `q` is
  `M`, for an exact sequence `M₂ ⟶ M₁ ⟶ M ⟶ 0` of sheaves of modules.
* `PresheafOfModules.symmetricMulPresheaf`: the first map of the sectionwise sequence.
* `SheafOfModules.symmetricPresheafHom`: the homomorphism of graded algebras
  `Sym(M₁) ⟶ (Sym N₀)♯` induced by a morphism `M₁.val ⟶ N₀` of presheaves of modules.
* `SheafOfModules.symmetricTensorSheafifyHom` and
  `SheafOfModules.symmetricCokernelPieceIso`: the comparisons of the two outer terms.

## Main results

* `CategoryTheory.ShortComplex.exact_of_exact_precomp_postcomp_iso`: exactness in the middle
  survives enlarging the source of the first map and composing the second with an isomorphism.
  This is what makes the comparison of the first terms need no epimorphy hypothesis.
* `SymPow.mem_rangeSubmodule_mul_of_symAlgMap_eq_zero`: **Tag 00DO's hard inclusion, read
  inside the symmetric algebra** rather than inside the subtype `Sym^{k+1}`.
* `PresheafOfModules.exact_symmetricMulPresheaf_shortComplex`: **Tag 00DO for presheaves of
  modules**, from a sectionwise exact sequence.
* `SheafOfModules.map_symmetricMulPresheaf_eq` and
  `SheafOfModules.map_symmetricAlgebraPieceMap_comp_symmetricCokernelPieceIso`: the two squares
  identifying the sheafified sectionwise sequence with the sequence of Tag 01CJ. The second is
  proved from the uniqueness half of the universal property of the symmetric algebra, which is
  what makes the comparison of the third terms compatible with the maps.
* `SheafOfModules.exact_symmetricPresentationShortComplex`: **exactness at the middle term.**
* `SheafOfModules.exact_and_epi_symmetricPresentationShortComplex`: **the symmetric half of
  Tag 01CJ**, exactness at the middle together with epimorphy of the second map.

## Implementation notes

**The tag is clause-qualified.** Tag 01CJ asserts the statement for symmetric *and* for
exterior powers. Only the symmetric half is proved here, so the attribute reads
`@[stacks 01CJ "symmetric powers"]`. The exterior half needs the exterior analogue of
`PresheafOfModules.symmetricMulPresheaf` and of the two squares; the algebraic input, Tag 00DO
for exterior powers, is already available as `exterior_power_presentation`.

**Degrees.** The tag's `n ≥ 1` is carried as `0 ≤ k` together with `1 + k = n`, which is the
shape `SheafOfModules.GradedAlgebra.presentationShortComplex` presents. Inside the proof `k` is
written as a natural number, and the sectionwise statements are read at the degree `1 + (k : ℤ)`
rather than at `((k + 1 : ℕ) : ℤ)`: the two integers are definitionally equal, whereas `1 + k`
and `k + 1` are not definitionally equal natural numbers, so the single `Nat.add_comm` is paid
once, inside `SymPow.mem_rangeSubmodule_mul_of_symAlgMap_eq_zero` and
`SymPow.mul_mem_one_add`.

**Why no epimorphy of the comparison of the first terms.** The sheafification of the objectwise
tensor product `M₂.val ⊗ Sym^k(M₁.val)` maps to `M₂ ⊗ Sym^k(M₁)` and that map is in fact an
isomorphism (it is Tag 0GMW composed with the counit), but exactness in the middle does not need
it: the image of the first map only has to be large enough, which is
`CategoryTheory.ShortComplex.exact_of_exact_precomp_postcomp_iso`.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 00DO](https://stacks.math.columbia.edu/tag/00DO)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

open scoped TensorProduct

universe v u w a

/-! ### Exactness in the middle, transported along a change of the outer terms -/

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Exactness in the middle survives enlarging the source of the first map and composing the
second map with an isomorphism.** The image of the first map can only grow and the kernel of
the second does not change, so the inclusion `im ⊆ ker` which holds in any complex becomes an
equality. -/
theorem exact_of_exact_precomp_postcomp_iso {X₁ X₁' X₂ X₃ X₃' : C}
    (e : X₁' ⟶ X₁) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (ε : X₃ ⟶ X₃') [IsIso ε]
    (hfg : f ≫ g = 0)
    (hex : (ShortComplex.mk (e ≫ f) (g ≫ ε)
      (by rw [Category.assoc, ← Category.assoc f, hfg, Limits.zero_comp,
        Limits.comp_zero])).Exact) :
    (ShortComplex.mk f g hfg).Exact := by
  have hzero : (e ≫ f) ≫ g ≫ ε = 0 := by
    rw [Category.assoc, ← Category.assoc f, hfg]; simp
  have hL₁ : Epi (kernel.lift (g ≫ ε) (e ≫ f) hzero) :=
    (ShortComplex.exact_iff_epi_kernel_lift (ShortComplex.mk (e ≫ f) (g ≫ ε) hzero)).1 hex
  have hfac : kernel.lift (g ≫ ε) (e ≫ f) hzero ≫ (kernelCompMono g ε).hom =
      e ≫ kernel.lift g f hfg := by
    refine (cancel_mono (kernel.ι g)).mp ?_
    simp
  refine (ShortComplex.exact_iff_epi_kernel_lift (ShortComplex.mk f g hfg)).2 ?_
  have hcomp : Epi (e ≫ kernel.lift g f hfg) := by rw [← hfac]; infer_instance
  exact epi_of_epi e _

/-- Exactness of a three-term complex depends on its two maps only. -/
theorem exact_of_eq {X₁ X₂ X₃ : C} {f f' : X₁ ⟶ X₂} {g g' : X₂ ⟶ X₃}
    (hf : f = f') (hg : g = g') {z : f ≫ g = 0} {z' : f' ≫ g' = 0}
    (h : (ShortComplex.mk f g z).Exact) : (ShortComplex.mk f' g' z').Exact := by
  subst hf
  subst hg
  exact h

end CategoryTheory.ShortComplex

/-! ### Tag 00DO inside the symmetric algebra -/

namespace SymmetricAlgebra

/-- Base change of the symmetric algebra along the identity of the ring is the functorial
algebra homomorphism `SymPow.symAlgMap`. -/
theorem mapₛₗ_id_apply {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (u : M →ₗ[R] N) (x : SymmetricAlgebra R M) :
    mapₛₗ (RingHom.id R) u x = SymPow.symAlgMap u x :=
  congrFun (congrArg (fun g : SymmetricAlgebra R M →+* SymmetricAlgebra R N => g.toFun)
    (ringHom_ext (f := mapₛₗ (RingHom.id R) u) (g := (SymPow.symAlgMap u).toRingHom)
      (fun r => by rw [mapₛₗ_algebraMap]; exact ((SymPow.symAlgMap u).commutes r).symm)
      (fun m => by rw [mapₛₗ_ι]; exact (SymPow.symAlgMap_ι u m).symm))) x

end SymmetricAlgebra

namespace SymPow

variable {R : Type*} [CommRing R] {M M₁ M₂ : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]

/-- Multiplying a degree-one generator by a degree-`k` element lands in degree `1 + k`. -/
theorem mul_mem_one_add (k : ℕ) (m : M₁) (y : ↥(symmetricPower k R M₁)) :
    SymmetricAlgebra.ι R M₁ m * (y : SymmetricAlgebra R M₁) ∈
      symmetricPower (1 + k) R M₁ := by
  rw [Nat.add_comm]
  exact mul_mem_succ k m y

/-- **Tag 00DO, the hard inclusion, stated inside the symmetric algebra.** A degree-`1 + k`
element of `Sym(M₁)` killed by `Sym(f)` lies in `ι(range g) · Sym^k(M₁)`. This is the content of
`symmetric_ker_le_im_alpha` with both sides read in `SymmetricAlgebra R M₁` instead of in the
subtype `Sym^{k+1}(M₁)`. -/
theorem mem_rangeSubmodule_mul_of_symAlgMap_eq_zero (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) (k : ℕ)
    {z : SymmetricAlgebra R M₁} (hz : z ∈ symmetricPower (1 + k) R M₁)
    (hz0 : symAlgMap f z = 0) :
    z ∈ rangeSubmodule g * symmetricPower k R M₁ := by
  rw [Nat.add_comm] at hz
  have hcoeff := (rangeIdeal_degree g (ker_symAlgMap_le_rangeIdeal g f hf hexact hz0)).right k
  have hzeq : (degreeMap z).coeff (k + 1) = z := by
    rw [degreeMap_eq_of_mem (k + 1) z hz, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  rwa [hzeq] at hcoeff

end SymPow

/-! ### The sectionwise sequence of Tag 01CJ -/

namespace PresheafOfModules

section SymMul

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {N₂ N₁ N : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}

/-- **The first map of the sectionwise sequence of Tag 01CJ**: on a pure tensor it multiplies
the degree-one image of a local section of `N₂` with a local section of the sectionwise
degree-`k` symmetric power of `N₁`. -/
noncomputable def symmetricMulPresheaf (q : N₂ ⟶ N₁) (k : ℕ) :
    tensorObj N₂ (symPowInt (k : ℤ) N₁) ⟶
      symPowInt (1 + (k : ℤ)) N₁ :=
  tensorMk
    (fun X s y => ⟨SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (N₁.obj X)
        (Hom.app q X s) * symPowIntVal y,
      SymPow.mul_mem_one_add k (Hom.app q X s)
        ⟨symPowIntVal y,
          (y : ↥(SymPow.symmetricPowerInt (k : ℤ) ((O ⋙ forget₂ _ RingCat).obj X)
            (N₁.obj X))).2⟩⟩)
    (fun X s s' y => Subtype.ext (by
      change SymmetricAlgebra.ι _ _ (Hom.app q X (s + s')) * _ = _
      rw [map_add, map_add, add_mul]
      rfl))
    (fun X r s y => Subtype.ext (by
      change SymmetricAlgebra.ι _ _ (Hom.app q X (r • s)) * _ = _
      rw [map_smul, map_smul, smul_mul_assoc]
      rfl))
    (fun X s y y' => Subtype.ext (by
      change _ * symPowIntVal (y + y') = _
      change _ * (symPowIntVal y
        + symPowIntVal y') = _
      rw [mul_add]
      rfl))
    (fun X r s y => Subtype.ext (by
      change _ * symPowIntVal (r • y) = _
      change _ * (r • symPowIntVal y) = _
      rw [mul_smul_comm]
      rfl))
    (fun {X Y} f s y => Subtype.ext (by
      change SymmetricAlgebra.mapₛₗ _ (N₁.restrictₛₗ f)
          (SymmetricAlgebra.ι _ _ (Hom.app q X s)
            * symPowIntVal y) = _
      rw [map_mul, SymmetricAlgebra.mapₛₗ_ι, restrictₛₗ_naturality_apply q f s]
      rfl))

/-- `PresheafOfModules.symmetricMulPresheaf` on the image of a pure tensor. -/
theorem symPowIntVal_symmetricMulPresheaf_tmul (q : N₂ ⟶ N₁) (k : ℕ) (X : Cᵒᵖ)
    (s : N₂.obj X) (y : (symPowInt (k : ℤ) N₁).obj X) :
    symPowIntVal (Hom.app (symmetricMulPresheaf q k) X (s ⊗ₜ y)) =
      SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (N₁.obj X) (Hom.app q X s) *
        symPowIntVal y :=
  congrArg (fun t => symPowIntVal t)
    (tensorMk_tmul _ _ _ _ _ _ X s y)

/-- If `f ≫ g = 0` for morphisms of presheaves of modules, then `g` kills the image of `f` on
every local section. -/
private theorem app_app_eq_zero_of_comp_eq_zero (f : N₂ ⟶ N₁) (g : N₁ ⟶ N) (h : f ≫ g = 0)
    (X : Cᵒᵖ) (s : N₂.obj X) : Hom.app g X (Hom.app f X s) = 0 :=
  (comp_app_apply f g X s).symm.trans (congrArg (fun φ : N₂ ⟶ N => Hom.app φ X s) h)

/-- The two maps of the sectionwise sequence of Tag 01CJ compose to zero. -/
theorem symmetricMulPresheaf_comp_pieceMap_eq_zero (q : N₂ ⟶ N₁) (p : N₁ ⟶ N) (k : ℕ)
    (hqp : q ≫ p = 0) :
    symmetricMulPresheaf q k ≫ symmetricAlgebraPieceMap (1 + (k : ℤ)) p = 0 := by
  refine tensorObj_hom_ext (ψ := 0) fun X s y => ?_
  refine symPowIntVal_injective (1 + (k : ℤ)) N ?_
  have h0 := app_app_eq_zero_of_comp_eq_zero q p hqp X s
  have h1 := congrArg (fun t => symPowIntVal t)
    (comp_app_apply (symmetricMulPresheaf q k)
      (symmetricAlgebraPieceMap (1 + (k : ℤ)) p) X (s ⊗ₜ y))
  refine h1.trans ?_
  rw [symPowIntVal_pieceMap,
    symPowIntVal_symmetricMulPresheaf_tmul, map_mul, SymmetricAlgebra.mapₛₗ_ι,
    h0, map_zero, zero_mul]
  rfl

/-- **Tag 00DO at the level of presheaves of modules.** If `N₂ --q--> N₁ --p--> N --> 0` is
exact on sections over every object, then so is
`N₂ ⊗ Sym^k(N₁) --> Sym^{1+k}(N₁) --> Sym^{1+k}(N)`, because the sectionwise symmetric powers
are computed sectionwise and the tensor product here is the objectwise one. -/
theorem exact_symmetricMulPresheaf_shortComplex (q : N₂ ⟶ N₁) (p : N₁ ⟶ N) (k : ℕ)
    (hqp : q ≫ p = 0)
    (hsur : ∀ X : Cᵒᵖ, Function.Surjective (p.app X).hom)
    (hker : ∀ X : Cᵒᵖ, LinearMap.ker (p.app X).hom ≤ LinearMap.range (q.app X).hom) :
    (ShortComplex.mk (symmetricMulPresheaf q k)
      (symmetricAlgebraPieceMap (1 + (k : ℤ)) p)
      (symmetricMulPresheaf_comp_pieceMap_eq_zero q p k hqp)).Exact := by
  refine exact_of_sectionwise _ fun X b => ?_
  have key : ∀ v ∈ SymPow.rangeSubmodule (q.app X).hom *
      SymPow.symmetricPower k ((O ⋙ forget₂ _ RingCat).obj X) (N₁.obj X),
      ∃ t, symPowIntVal (Hom.app (symmetricMulPresheaf q k) X t) = v := by
    intro v hv
    refine Submodule.mul_induction_on hv ?_ ?_
    · rintro m ⟨aa, rfl⟩ n hn
      exact ⟨aa ⊗ₜ ⟨n, hn⟩,
        symPowIntVal_symmetricMulPresheaf_tmul q k X aa ⟨n, hn⟩⟩
    · rintro x y ⟨t, ht⟩ ⟨t', ht'⟩
      refine ⟨t + t', ?_⟩
      rw [map_add, ← ht, ← ht']
      rfl
  constructor
  · intro hb
    have hbv : SymPow.symAlgMap (p.app X).hom
        (symPowIntVal b) = 0 := by
      have h := congrArg (fun t => symPowIntVal t) hb
      rw [symPowIntVal_pieceMap, SymmetricAlgebra.mapₛₗ_id_apply] at h
      exact h
    obtain ⟨t, ht⟩ := key _ (SymPow.mem_rangeSubmodule_mul_of_symAlgMap_eq_zero
      (q.app X).hom (p.app X).hom (hsur X) (hker X) k
      (b : ↥(SymPow.symmetricPowerInt (1 + (k : ℤ)) ((O ⋙ forget₂ _ RingCat).obj X)
        (N₁.obj X))).2 hbv)
    exact ⟨t, symPowIntVal_injective (1 + (k : ℤ)) N₁ ht⟩
  · rintro ⟨t, rfl⟩
    exact app_app_eq_zero_of_comp_eq_zero _ _
      (symmetricMulPresheaf_comp_pieceMap_eq_zero q p k hqp) X t

end SymMul

end PresheafOfModules

/-! ### The sheafification of a presheaf cokernel -/

namespace SheafOfModules

section Cokernel

open PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {M₂ M₁ M : SheafOfModules.{w} (toRingCat J Osharp)}

/-- `SheafOfModules.sheafifiedValIso` is natural: it is the counit of the sheafification
adjunction. -/
theorem map_val_comp_sheafifiedValIso_hom (q : M₂ ⟶ M₁) :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map q.val ≫
        (sheafifiedValIso J M₁).hom = (sheafifiedValIso J M₂).hom ≫ q :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (toRingCat J Osharp).obj)).counit.naturality q

/-- The inverse of `SheafOfModules.sheafifiedValIso` is natural: `q` followed by it equals it
followed by the sheafification of `q.val`. -/
theorem comp_sheafifiedValIso_inv (q : M₂ ⟶ M₁) :
    q ≫ (sheafifiedValIso J M₁).inv =
      (sheafifiedValIso J M₂).inv ≫
        (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map q.val := by
  rw [Iso.comp_inv_eq, Category.assoc, map_val_comp_sheafifiedValIso_hom,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
/-- If `q ≫ p = 0` for morphisms of sheaves of modules, then `q.val ≫ p.val = 0` for the
underlying morphisms of presheaves of modules. -/
theorem val_comp_val_eq_zero {q : M₂ ⟶ M₁} {p : M₁ ⟶ M} (hqp : q ≫ p = 0) :
    q.val ≫ p.val = 0 :=
  congrArg SheafOfModules.Hom.val hqp

/-- The factorization of `p` through the presheaf cokernel of `q`. -/
noncomputable def cokernelDescVal {q : M₂ ⟶ M₁} {p : M₁ ⟶ M} (hqp : q ≫ p = 0) :
    cokernel q.val ⟶ M.val :=
  cokernel.desc q.val p.val (val_comp_val_eq_zero hqp)

/-- The comparison from the sheafification of the presheaf cokernel of `q` to `M`. -/
noncomputable def cokernelSheafifyHom {q : M₂ ⟶ M₁} {p : M₁ ⟶ M} (hqp : q ≫ p = 0) :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj (cokernel q.val) ⟶ M :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
      (cokernelDescVal hqp) ≫ (sheafifiedValIso J M).hom

/-- The sheafification of the projection onto the presheaf cokernel of `q`, followed by
`cokernelSheafifyHom`, is `sheafifiedValIso J M₁` followed by `p`. -/
theorem map_cokernelπ_comp_cokernelSheafifyHom {q : M₂ ⟶ M₁} {p : M₁ ⟶ M}
    (hqp : q ≫ p = 0) :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map (cokernel.π q.val) ≫
        cokernelSheafifyHom hqp = (sheafifiedValIso J M₁).hom ≫ p := by
  rw [cokernelSheafifyHom, ← Category.assoc, ← Functor.map_comp, cokernelDescVal,
    cokernel.π_desc, map_val_comp_sheafifiedValIso_hom]

/-- **The sheafification of the presheaf cokernel of `q` is `M`** whenever
`M₂ --q--> M₁ --p--> M --> 0` is exact. Sheafification is a left adjoint, so it carries the
presheaf cokernel to the sheaf cokernel, and `p` exhibits `M` as that cokernel. -/
noncomputable def cokernelSheafifyIso {q : M₂ ⟶ M₁} {p : M₁ ⟶ M} (hqp : q ≫ p = 0)
    [Epi p] (hex : (ShortComplex.mk q p hqp).Exact) :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj (cokernel q.val) ≅
      M := by
  have hqz : q ≫ ((sheafifiedValIso J M₁).inv ≫
      (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
        (cokernel.π q.val)) = 0 := by
    rw [← Category.assoc, comp_sheafifiedValIso_inv, Category.assoc, ← Functor.map_comp,
      cokernel.condition, Functor.map_zero, Limits.comp_zero]
  have hdq : p ≫ hex.gIsCokernel.desc (CokernelCofork.ofπ _ hqz) =
    (sheafifiedValIso J M₁).inv ≫
      (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
        (cokernel.π q.val) := Cofork.IsColimit.π_desc hex.gIsCokernel
  refine ⟨cokernelSheafifyHom hqp, hex.gIsCokernel.desc (CokernelCofork.ofπ _ hqz), ?_, ?_⟩
  · have hepi : Epi ((PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
      (cokernel.π q.val)) := Functor.map_epi _ _
    refine hepi.left_cancellation _ _ ?_
    rw [← Category.assoc, map_cokernelπ_comp_cokernelSheafifyHom hqp, Category.assoc, hdq,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  · have hp : Epi p := inferInstance
    refine hp.left_cancellation _ _ ?_
    rw [← Category.assoc, hdq, Category.assoc, map_cokernelπ_comp_cokernelSheafifyHom hqp,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- The forward map of `cokernelSheafifyIso` is `cokernelSheafifyHom`. -/
@[simp]
theorem cokernelSheafifyIso_hom {q : M₂ ⟶ M₁} {p : M₁ ⟶ M} (hqp : q ≫ p = 0)
    [Epi p] (hex : (ShortComplex.mk q p hqp).Exact) :
    (cokernelSheafifyIso hqp hex).hom = cokernelSheafifyHom hqp := rfl

end Cokernel

/-! ### Symmetric powers of a morphism into a presheaf of modules -/

section PresheafTarget

open PresheafOfModules Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {M₁ : SheafOfModules.{w} (toRingCat J Osharp)}
  {N₀ : PresheafOfModules.{w} (toRingCat J Osharp).obj}

/-- The degreewise datum out of the sectionwise symmetric algebra of `M₁` into the sheafified
sectionwise symmetric algebra of a presheaf of modules `N₀` receiving `M₁.val`. -/
noncomputable def symmetricPresheafFamily (π : M₁.val ⟶ N₀) (n : ℤ) :
    symPowInt n M₁.val ⟶
      sheafifyRestrict (𝟙 (toRingCat J Osharp).obj) (symPowInt n N₀) :=
  symmetricAlgebraPieceMap n π ≫
    sheafifyUnit (𝟙 (toRingCat J Osharp).obj) (symPowInt n N₀)

/-- `symmetricPresheafFamily` is multiplicative: it carries the product of sections of degrees
`i` and `j` to the product of their images in the sheafified symmetric algebra of `N₀`. -/
theorem symmetricPresheafFamily_mul (π : M₁.val ⟶ N₀) (i j : ℤ) (X : Cᵒᵖ)
    (x : (symPowInt i M₁.val).obj X)
    (y : (symPowInt j M₁.val).obj X) :
    Hom.app (symmetricPresheafFamily π (i + j)) X
        (((symPowIntGradedAlgebra M₁.val).mul i j).app X x y) =
      (((symPowIntGradedAlgebra N₀).sheafify
        (𝟙 (toRingCat J Osharp).obj)).mul i j).app X
          (Hom.app (symmetricPresheafFamily π i) X x)
          (Hom.app (symmetricPresheafFamily π j) X y) := by
  change Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj) _) X
      (Hom.app (symmetricAlgebraPieceMap (i + j) π) X _) = _
  rw [symmetricAlgebraPieceMap_mul]
  exact ((symPowIntGradedAlgebra N₀).sheafify_mul_unit
    (𝟙 (toRingCat J Osharp).obj) i j X _ _).symm

/-- `symmetricPresheafFamily` carries the unit section of the sectionwise symmetric algebra
of `M₁` to the unit section of the sheafified symmetric algebra of `N₀`. -/
theorem symmetricPresheafFamily_one (π : M₁.val ⟶ N₀) (X : Cᵒᵖ) :
    Hom.app (symmetricPresheafFamily π 0) X
        ((symPowIntGradedAlgebra M₁.val).one.eval X) =
      (((symPowIntGradedAlgebra N₀).sheafify
        (𝟙 (toRingCat J Osharp).obj)).one).eval X := by
  change Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj) _) X
      (Hom.app (symmetricAlgebraPieceMap 0 π) X
        ((symPowIntOne M₁.val).eval X)) = _
  rw [symmetricAlgebraPieceMap_one]
  exact ((symPowIntGradedAlgebra N₀).sheafify_one_eval
    (𝟙 (toRingCat J Osharp).obj) X).symm

/-- The homomorphism of graded algebras `Sym(M₁) ⟶ (Sym N₀)♯` induced degreewise by the
sectionwise symmetric powers of a morphism `M₁.val ⟶ N₀` of presheaves of modules. -/
noncomputable def symmetricPresheafHom (π : M₁.val ⟶ N₀) :
    GradedAlgebra.UnitalHom (sheafifiedSymmetricAlgebra J M₁)
      ((symPowIntGradedAlgebra N₀).sheafify (𝟙 (toRingCat J Osharp).obj)) :=
  (Stacks.GradedAlgebra.existsUnique_desc (𝟙 (toRingCat J Osharp).obj)
    (symPowIntGradedAlgebra M₁.val)
    (B := (symPowIntGradedAlgebra N₀).sheafify (𝟙 (toRingCat J Osharp).obj))
    (symmetricPresheafFamily π)
    (symmetricPresheafFamily_mul π) (symmetricPresheafFamily_one π)).choose

/-- On the image of a section `s` under the sheafification unit, the degree-`n` component of
`symmetricPresheafHom π` agrees with `symmetricPresheafFamily π n` applied to `s`. -/
theorem symmetricPresheafHom_unit (π : M₁.val ⟶ N₀) (n : ℤ) (X : Cᵒᵖ)
    (s : (symPowInt n M₁.val).obj X) :
    ((symmetricPresheafHom π).app n).val.app X
        (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt n M₁.val)) X s) =
      Hom.app (symmetricPresheafFamily π n) X s :=
  (Stacks.GradedAlgebra.existsUnique_desc (𝟙 (toRingCat J Osharp).obj)
    (symPowIntGradedAlgebra M₁.val)
    (B := (symPowIntGradedAlgebra N₀).sheafify (𝟙 (toRingCat J Osharp).obj))
    (symmetricPresheafFamily π)
    (symmetricPresheafFamily_mul π) (symmetricPresheafFamily_one π)).choose_spec.1 n X s

/-- `symmetricPresheafHom` is degreewise the sheafification of the sectionwise symmetric
power of `π`. -/
theorem symmetricPresheafHom_app (π : M₁.val ⟶ N₀) (n : ℤ) :
    (symmetricPresheafHom π).app n =
      (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
        (symmetricAlgebraPieceMap n π) := by
  refine PresheafOfModules.sheafification_hom_ext (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  change ((symmetricPresheafHom π).app n).val.app X
    (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
      (symPowInt n M₁.val)) X s) = _
  rw [symmetricPresheafHom_unit]
  exact (PresheafOfModules.unit_naturality_apply (symmetricAlgebraPieceMap n π) X s).symm

/-- **The degree-one generator of `Sym(M₁)`, composed with `symmetricPresheafHom`**: it is
`π` followed by the degree-one generator of the sheafified sectionwise symmetric algebra of
`N₀`, read through the identification of `M₁` with the sheafification of `M₁.val`. -/
theorem sheafifiedSymmetricGenerator_comp_symmetricPresheafHom (π : M₁.val ⟶ N₀) :
    sheafifiedSymmetricGenerator J M₁ ≫ (symmetricPresheafHom π).app 1 =
      (sheafifiedValIso J M₁).inv ≫
        (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map π ≫
          (symPowIntGradedAlgebra N₀).sheafifyGen (𝟙 (toRingCat J Osharp).obj)
            (symPowIntGen N₀) := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  change ((symmetricPresheafHom π).app 1).val.app U
      ((sheafifiedSymmetricGenerator J M₁).val.app U s) =
    ((symPowIntGradedAlgebra N₀).sheafifyGen (𝟙 (toRingCat J Osharp).obj)
        (symPowIntGen N₀)).val.app U
      (((PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map π).val.app U
        ((sheafifiedValIso J M₁).inv.val.app U s))
  rw [sheafifiedSymmetricGenerator_apply, symmetricPresheafHom_unit,
    sheafifiedValIso_inv_apply]
  change Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
      (symPowInt 1 N₀)) U
      (Hom.app (symmetricAlgebraPieceMap 1 π) U
        (Hom.app (symPowIntGen M₁.val) U s)) = _
  rw [symmetricAlgebraPieceMap_gen, PresheafOfModules.unit_naturality_apply]
  exact ((symPowIntGradedAlgebra N₀).sheafifyGen_unit
    (𝟙 (toRingCat J Osharp).obj) (symPowIntGen N₀) U (Hom.app π U s)).symm

end PresheafTarget

/-! ### The first map after sheafification -/

section Tensor

open PresheafOfModules Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {M₂ M₁ : SheafOfModules.{w} (toRingCat J Osharp)}

/-- The sheafification unit of the sectionwise degree-`k` symmetric power, tensored with the
identity of `M₂`. -/
noncomputable def tensorSymmetricUnit (k : ℤ) :
    tensorObj M₂.val (symPowInt k M₁.val) ⟶
      tensorObj M₂.val ((sheafifiedSymmetricAlgebra J M₁).piece k).val :=
  tensorHom (𝟙 M₂.val)
    (sheafifyUnit (𝟙 (toRingCat J Osharp).obj) (symPowInt k M₁.val))

/-- **The comparison of the two outer first terms**: from the sheafification of the objectwise
tensor product of `M₂` with the *sectionwise* degree-`k` symmetric power of `M₁` to the tensor
product of `M₂` with `Sym^k(M₁)`. -/
noncomputable def symmetricTensorSheafifyHom (k : ℤ) :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
        (tensorObj M₂.val (symPowInt k M₁.val)) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj M₂).obj
        ((sheafifiedSymmetricAlgebra J M₁).piece k) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (toRingCat J Osharp).obj)).homEquiv _ _).symm
    (tensorSymmetricUnit k ≫
      tensorSheafUnit M₂ ((sheafifiedSymmetricAlgebra J M₁).piece k))

/-- On the image of `s ⊗ₜ y` under the sheafification unit, `symmetricTensorSheafifyHom k` is
`tensorSheafUnit` applied to `s` tensored with the image of `y` under the sheafification
unit of the sectionwise degree-`k` symmetric power. -/
theorem symmetricTensorSheafifyHom_unit_tmul (k : ℤ) (U : Cᵒᵖ) (s : M₂.val.obj U)
    (y : (symPowInt k M₁.val).obj U) :
    (symmetricTensorSheafifyHom k).val.app U
        (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (tensorObj M₂.val (symPowInt k M₁.val))) U (s ⊗ₜ y)) =
      (tensorSheafUnit M₂ ((sheafifiedSymmetricAlgebra J M₁).piece k)).app U
        (s ⊗ₜ Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt k M₁.val)) U y) := by
  have h := PresheafOfModules.hom_congr_apply'
    (PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm
      (𝟙 (toRingCat J Osharp).obj)
      (N := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj M₂).obj
        ((sheafifiedSymmetricAlgebra J M₁).piece k))
      (tensorSymmetricUnit k ≫
        tensorSheafUnit M₂ ((sheafifiedSymmetricAlgebra J M₁).piece k))) U (s ⊗ₜ y)
  exact h.trans ((PresheafOfModules.comp_app_apply (tensorSymmetricUnit k)
      (tensorSheafUnit M₂ ((sheafifiedSymmetricAlgebra J M₁).piece k)) U (s ⊗ₜ y)).trans
    (congrArg (fun z => (tensorSheafUnit M₂
        ((sheafifiedSymmetricAlgebra J M₁).piece k)).app U z)
      (tensorHom_tmul (𝟙 M₂.val)
        (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt k M₁.val)) U s y)))

/-- The second factor of the first map of the sequence of Tag 01CJ, computed on the image of
a pure tensor under the sheafification unit. -/
theorem generatorMul_symmetricTensorSheafifyHom_unit_tmul (q : M₂ ⟶ M₁) (k : ℕ) (U : Cᵒᵖ)
    (s : M₂.val.obj U) (y : (symPowInt (k : ℤ) M₁.val).obj U) :
    (symmetricTensorSheafifyHom (k : ℤ) ≫
          GradedAlgebra.generatorMul (q ≫ sheafifiedSymmetricGenerator J M₁)
            (k : ℤ)).val.app U
        (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (tensorObj M₂.val (symPowInt (k : ℤ) M₁.val))) U (s ⊗ₜ y)) =
      Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt (1 + (k : ℤ)) M₁.val)) U
        (Hom.app (symmetricMulPresheaf q.val k) U (s ⊗ₜ y)) := by
  refine (SheafOfModules.comp_val_app_apply (symmetricTensorSheafifyHom (k : ℤ))
    (GradedAlgebra.generatorMul (q ≫ sheafifiedSymmetricGenerator J M₁) (k : ℤ)) U _).trans ?_
  refine (congrArg (fun t => (GradedAlgebra.generatorMul
      (q ≫ sheafifiedSymmetricGenerator J M₁) (k : ℤ)).val.app U t)
    (symmetricTensorSheafifyHom_unit_tmul (k : ℤ) U s y)).trans ?_
  refine (GradedAlgebra.generatorMul_unit (q ≫ sheafifiedSymmetricGenerator J M₁)
    (k : ℤ) U s _).trans ?_
  rw [SheafOfModules.comp_val_app_apply, sheafifiedSymmetricGenerator_apply]
  refine ((symPowIntGradedAlgebra M₁.val).sheafify_mul_unit
    (𝟙 (toRingCat J Osharp).obj) 1 (k : ℤ) U
    (Hom.app (symPowIntGen M₁.val) U (Hom.app q.val U s)) y).trans ?_
  refine congrArg (fun t => Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
    (symPowInt (1 + (k : ℤ)) M₁.val)) U t) ?_
  refine (symPowIntVal_injective (1 + (k : ℤ)) M₁.val ?_).symm
  rw [symPowIntVal_symmetricMulPresheaf_tmul,
    symPowIntGradedAlgebra_mul, symPowIntVal_mul,
    symPowIntVal_gen]

/-- **The square identifying the first map of the sheafified sectionwise sequence with the
first map of the sequence of Tag 01CJ.** -/
theorem map_symmetricMulPresheaf_eq (q : M₂ ⟶ M₁) (k : ℕ) :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
        (symmetricMulPresheaf q.val k) =
      symmetricTensorSheafifyHom (k : ℤ) ≫
        GradedAlgebra.generatorMul (q ≫ sheafifiedSymmetricGenerator J M₁) (k : ℤ) := by
  refine PresheafOfModules.sheafification_hom_ext (PresheafOfModules.tensorObj_hom_ext
    fun U s y => ?_)
  change ((PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
      (symmetricMulPresheaf q.val k)).val.app U
      (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
        (tensorObj M₂.val (symPowInt (k : ℤ) M₁.val))) U (s ⊗ₜ y)) =
    (symmetricTensorSheafifyHom (k : ℤ) ≫
      GradedAlgebra.generatorMul (q ≫ sheafifiedSymmetricGenerator J M₁)
        (k : ℤ)).val.app U
      (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
        (tensorObj M₂.val (symPowInt (k : ℤ) M₁.val))) U (s ⊗ₜ y))
  exact (PresheafOfModules.unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
      (symmetricMulPresheaf q.val k) U (s ⊗ₜ y)).trans
    (generatorMul_symmetricTensorSheafifyHom_unit_tmul q k U s y).symm

end Tensor

/-! ### Exactness at the middle term -/

section Exact

open PresheafOfModules Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {M₂ M₁ M : SheafOfModules.{w} (toRingCat J Osharp)}

/-- **The degree-`n` symmetric power of the sheafified presheaf cokernel of `q` is the
degree-`n` symmetric power of `M`.** Both are symmetric algebras of `M`, and a symmetric
algebra is unique up to a canonical isomorphism in every degree. -/
noncomputable def symmetricCokernelPieceIso {q : M₂ ⟶ M₁} {p : M₁ ⟶ M} (hqp : q ≫ p = 0)
    [Epi p] (hex : (ShortComplex.mk q p hqp).Exact) (n : ℤ) :
    ((symPowIntGradedAlgebra (cokernel q.val)).sheafify
        (𝟙 (toRingCat J Osharp).obj)).piece n ≅
      (sheafifiedSymmetricAlgebra J M).piece n :=
  (GradedAlgebra.isSymmetricAlgebra_ofIso (cokernelSheafifyIso hqp hex).symm
    (PresheafOfModules.isSymmetricAlgebra_sheafify_symmetricAlgebra
      (𝟙 (toRingCat J Osharp).obj) (cokernel q.val))).pieceIso
    (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M) n

/-- **The square identifying the second map of the sheafified sectionwise sequence with the
second map of the sequence of Tag 01CJ.** -/
theorem map_symmetricAlgebraPieceMap_comp_symmetricCokernelPieceIso
    {q : M₂ ⟶ M₁} {p : M₁ ⟶ M} (hqp : q ≫ p = 0) [Epi p]
    (hex : (ShortComplex.mk q p hqp).Exact) (n : ℤ) :
    (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
          (symmetricAlgebraPieceMap n (cokernel.π q.val)) ≫
        (symmetricCokernelPieceIso hqp hex n).hom = (symmetricDescHom J p).app n := by
  have hA'e := GradedAlgebra.isSymmetricAlgebra_ofIso (cokernelSheafifyIso hqp hex).symm
    (PresheafOfModules.isSymmetricAlgebra_sheafify_symmetricAlgebra
      (𝟙 (toRingCat J Osharp).obj) (cokernel q.val))
  set Ξ := hA'e.isUniversal.desc (sheafifiedSymmetricAlgebra J M)
    (sheafifiedSymmetricGenerator J M)
    (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M).isUniversal.1 with hΞ
  have hext : ((cokernelSheafifyIso hqp hex).symm.hom ≫
      (symPowIntGradedAlgebra (cokernel q.val)).sheafifyGen
        (𝟙 (toRingCat J Osharp).obj) (symPowIntGen (cokernel q.val))) ≫ Ξ.app 1 =
      sheafifiedSymmetricGenerator J M :=
    hA'e.isUniversal.desc_extends _ _ _
  have hι' : (symPowIntGradedAlgebra (cokernel q.val)).sheafifyGen
        (𝟙 (toRingCat J Osharp).obj) (symPowIntGen (cokernel q.val)) ≫ Ξ.app 1 =
      cokernelSheafifyHom hqp ≫ sheafifiedSymmetricGenerator J M := by
    rw [← hext, Category.assoc, ← Category.assoc (cokernelSheafifyHom hqp)]
    rw [show cokernelSheafifyHom hqp ≫ (cokernelSheafifyIso hqp hex).symm.hom = 𝟙 _ from
      (cokernelSheafifyIso hqp hex).hom_inv_id, Category.id_comp]
  have hg : sheafifiedSymmetricGenerator J M₁ ≫
      ((symmetricPresheafHom (cokernel.π q.val)).comp Ξ).app 1 =
        p ≫ sheafifiedSymmetricGenerator J M := by
    rw [GradedAlgebra.UnitalHom.comp_app, ← Category.assoc,
      sheafifiedSymmetricGenerator_comp_symmetricPresheafHom, Category.assoc, Category.assoc,
      hι', ← Category.assoc ((PresheafOfModules.sheafification
        (𝟙 (toRingCat J Osharp).obj)).map (cokernel.π q.val)),
      map_cokernelπ_comp_cokernelSheafifyHom hqp, Category.assoc, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  have hfinal := (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M₁).isUniversal.descComp_unique
    p (sheafifiedSymmetricGenerator J M)
    (GradedAlgebra.pairwiseCommutes_comp p
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M).isUniversal.1) hg
  have happ := congrArg (fun h : GradedAlgebra.UnitalHom (sheafifiedSymmetricAlgebra J M₁)
      (sheafifiedSymmetricAlgebra J M) => h.app n) hfinal
  rw [GradedAlgebra.UnitalHom.comp_app, symmetricPresheafHom_app] at happ
  rw [symmetricDescHom_eq_descComp]
  exact happ

/-- **Tag 01CJ, symmetric case, exactness at the middle term.** Let
`M₂ --q--> M₁ --p--> M --> 0` be an exact sequence of sheaves of modules on a ringed site. For
every `n = 1 + k` with `k ≥ 0`, the three-term complex

`M₂ ⊗ Sym^k(M₁) ⟶ Symⁿ(M₁) ⟶ Symⁿ(M)`

of `SheafOfModules.GradedAlgebra.symmetricPresentationShortComplex` is exact at the middle
term. Together with `SheafOfModules.epi_descComp_app_symmetric` this is the whole of the
symmetric half of Tag 01CJ. -/
@[sga "5 VII 3.6.1" "partial"]
theorem exact_symmetricPresentationShortComplex (q : M₂ ⟶ M₁) (p : M₁ ⟶ M)
    (hqp : q ≫ p = 0) [Epi p] (hex : (ShortComplex.mk q p hqp).Exact)
    (k n : ℤ) (hk : 0 ≤ k) (hn : 1 + k = n) :
    (GradedAlgebra.symmetricPresentationShortComplex
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M₁)
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M).isUniversal.1
      q p hqp k n hn).Exact := by
  obtain ⟨k₀, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  subst hn
  have hsur : ∀ X : Cᵒᵖ, Function.Surjective ((cokernel.π q.val).app X).hom := fun X =>
    (ModuleCat.epi_iff_surjective _).1
      ((PresheafOfModules.evaluation.{w} (toRingCat J Osharp).obj X).map_epi _)
  have hker : ∀ X : Cᵒᵖ, LinearMap.ker ((cokernel.π q.val).app X).hom ≤
      LinearMap.range (q.val.app X).hom := by
    intro X
    have h : (ShortComplex.mk q.val (cokernel.π q.val) (cokernel.condition q.val)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel q.val)
    have h2 := h.map (PresheafOfModules.evaluation.{w} (toRingCat J Osharp).obj X)
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h2
    exact h2.ge
  have hPre := PresheafOfModules.exact_symmetricMulPresheaf_shortComplex q.val
    (cokernel.π q.val) k₀ (cokernel.condition q.val) hsur hker
  have hSheaf := hPre.map (PresheafOfModules.sheafification.{w} (𝟙 (toRingCat J Osharp).obj))
  have hfg : GradedAlgebra.generatorMul (q ≫ sheafifiedSymmetricGenerator J M₁) (k₀ : ℤ) ≫
      (symmetricDescHom J p).app (1 + (k₀ : ℤ)) =
        (HasZeroMorphisms.zero
          (C := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} Osharp))
          _ _).zero := by
    rw [symmetricDescHom_eq_descComp]
    exact GradedAlgebra.generatorMul_comp_descComp_eq_zero
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M₁).isUniversal q p _ hqp (k₀ : ℤ)
  refine ShortComplex.exact_of_eq (z := hfg) (Category.comp_id _).symm
    (congrArg (fun h : GradedAlgebra.UnitalHom (sheafifiedSymmetricAlgebra J M₁)
      (sheafifiedSymmetricAlgebra J M) => h.app (1 + (k₀ : ℤ)))
      (symmetricDescHom_eq_descComp J p)) ?_
  refine ShortComplex.exact_of_exact_precomp_postcomp_iso
    (symmetricTensorSheafifyHom (k₀ : ℤ))
    (GradedAlgebra.generatorMul (q ≫ sheafifiedSymmetricGenerator J M₁) (k₀ : ℤ))
    ((symmetricDescHom J p).app (1 + (k₀ : ℤ)))
    (symmetricCokernelPieceIso hqp hex (1 + (k₀ : ℤ))).inv hfg ?_
  have hg2 : (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).map
        (symmetricAlgebraPieceMap (1 + (k₀ : ℤ)) (cokernel.π q.val)) =
      (symmetricDescHom J p).app (1 + (k₀ : ℤ)) ≫
        (symmetricCokernelPieceIso hqp hex (1 + (k₀ : ℤ))).inv :=
    (Iso.eq_comp_inv (symmetricCokernelPieceIso hqp hex (1 + (k₀ : ℤ)))).mpr
      (map_symmetricAlgebraPieceMap_comp_symmetricCokernelPieceIso hqp hex _)
  exact ShortComplex.exact_of_eq (map_symmetricMulPresheaf_eq q k₀) hg2 hSheaf

/-- **Stacks Tag 01CJ, symmetric powers.** Let `M₂ --q--> M₁ --p--> M --> 0` be an exact
sequence of sheaves of modules on a ringed site, and let `n = 1 + k` with `k ≥ 0`. Then

`M₂ ⊗ Sym^k(M₁) ⟶ Symⁿ(M₁) ⟶ Symⁿ(M) ⟶ 0`

is exact: the complex is exact at the middle term and its second map is an epimorphism. -/
@[stacks 01CJ "symmetric powers"]
theorem exact_and_epi_symmetricPresentationShortComplex (q : M₂ ⟶ M₁) (p : M₁ ⟶ M)
    (hqp : q ≫ p = 0) [Epi p] (hex : (ShortComplex.mk q p hqp).Exact)
    (k n : ℤ) (hk : 0 ≤ k) (hn : 1 + k = n) :
    (GradedAlgebra.symmetricPresentationShortComplex
        (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M₁)
        (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M).isUniversal.1
        q p hqp k n hn).Exact ∧
      Epi (GradedAlgebra.symmetricPresentationShortComplex
        (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M₁)
        (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M).isUniversal.1
        q p hqp k n hn).g :=
  ⟨exact_symmetricPresentationShortComplex q p hqp hex k n hk hn,
    epi_descComp_app_symmetric J p n⟩

end Exact

end SheafOfModules

end
