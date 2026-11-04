module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.Idempotents
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Splitting `D_ctf` along central idempotents of the coefficient ring

Let `Λ` be a ring and `e ∈ Λ` a central idempotent. Multiplication by `e` is an idempotent
endomorphism of every sheaf of `Λ`-modules, natural in the sheaf, and the summand `e F` it cuts
out is an exact functor of `F`. It preserves constructible flat sheaves and `D_ctf`, and a complete
family of orthogonal central idempotents splits every sheaf, and every complex, into the direct sum
of its parts. For a finite ring `Λ` the primary decomposition of `Λ` is such a family, which is how
[Stacks, Tag 03UG], Step 3, reduces the trace formula to rings killed by a power of a prime.

## Main definitions

* `CategoryTheory.idempotentPart` — the summand cut out by an idempotent endomorphism of the
  identity functor of an abelian category, as a functor.
* `CategoryTheory.idempotentDecompositionIso` — the decomposition of an object into the direct sum
  of the summands cut out by a complete family of orthogonal idempotent endomorphisms of the
  identity.
* `Stacks.EtaleCohomology.sheafCentralEndo` — multiplication by a central element of `Λ`, as an
  endomorphism of the identity functor of sheaves of `Λ`-modules.

## Main results

* `CategoryTheory.idempotentPart_preservesFiniteLimits` and
  `CategoryTheory.idempotentPart_preservesFiniteColimits` — that summand is an exact functor.
* `CategoryTheory.idempotentDecompositionIso_hom_naturality` — the decomposition is natural.
* `Stacks.EtaleCohomology.exists_primary_completeOrthogonalIdempotents` — a finite ring carries a
  complete family of orthogonal central idempotents `e_i` with `ℓ_i ^ a_i e_i = 0`, the `ℓ_i`
  prime.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] (p : 𝟭 C ⟶ 𝟭 C)

/-- The component of an endomorphism of the identity functor, as an endomorphism. -/
abbrev _root_.CategoryTheory.NatTrans.app' (A : C) : A ⟶ A := p.app A

/-- The summand cut out by an endomorphism `p` of the identity functor: the kernel of `𝟙 - p`,
functorially. For an idempotent `p` it is the image of `p`. -/
def idempotentPart : C ⥤ C where
  obj A := kernel (𝟙 A - p.app' A)
  map {A B} f := kernel.lift _ (kernel.ι _ ≫ f) (by
    have h := p.naturality f
    simp only [Functor.id_obj, Functor.id_map] at h
    have h' : f ≫ (𝟙 B - p.app' B) = (𝟙 A - p.app' A) ≫ f := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp]
      exact congrArg (f - ·) h
    rw [Category.assoc, h', ← Category.assoc, kernel.condition, zero_comp])
  map_id A := (cancel_mono (kernel.ι (𝟙 A - p.app' A))).1 (by simp)
  map_comp {A B D} f g := (cancel_mono (kernel.ι (𝟙 D - p.app' D))).1 (by simp)

/-- The inclusion of the summand. -/
def idempotentPartι : idempotentPart p ⟶ 𝟭 C where
  app A := kernel.ι _
  naturality _ _ f := by simp [idempotentPart]

variable {p}

/-- The projection onto the summand of an idempotent `p`. -/
def idempotentPartπ (hp : p ≫ p = p) : 𝟭 C ⟶ idempotentPart p where
  app A := kernel.lift (𝟙 A - p.app' A) (p.app' A) (by
    have h := congrArg (fun q => q.app A) hp
    simp only [NatTrans.comp_app] at h
    rw [Preadditive.comp_sub, Category.comp_id, h, sub_self])
  naturality A B f := by
    refine (cancel_mono (kernel.ι (𝟙 B - p.app' B))).1 ?_
    change (f ≫ kernel.lift (𝟙 B - p.app' B) (p.app' B) _) ≫ kernel.ι _ =
      (kernel.lift (𝟙 A - p.app' A) (p.app' A) _ ≫
        kernel.lift (𝟙 B - p.app' B) (kernel.ι _ ≫ f) _) ≫ kernel.ι _
    rw [Category.assoc, Category.assoc, kernel.lift_ι, kernel.lift_ι, ← Category.assoc,
      kernel.lift_ι]
    exact p.naturality f

/-- The kernel inclusion of `𝟙 A - p` is fixed by `p`. -/
private theorem kernel_ι_comp_app_eq (A : C) :
    kernel.ι (𝟙 A - p.app' A) ≫ p.app A = kernel.ι (𝟙 A - p.app' A) := by
  have h := kernel.condition (𝟙 A - p.app' A)
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h
  exact h.symm

/-- The inclusion of the summand of an idempotent, followed by the projection onto it, is the
identity. -/
theorem idempotentPartι_π (hp : p ≫ p = p) (A : C) :
    (idempotentPartι p).app A ≫ (idempotentPartπ hp).app A = 𝟙 _ := by
  refine (cancel_mono (kernel.ι (𝟙 A - p.app' A))).1 ?_
  show (kernel.ι _ ≫ kernel.lift (𝟙 A - p.app' A) (p.app' A) _) ≫ kernel.ι _ = 𝟙 _ ≫ kernel.ι _
  rw [Category.assoc, kernel.lift_ι, Category.id_comp]
  exact kernel_ι_comp_app_eq A

/-- The summand functor preserves zero morphisms. -/
instance idempotentPart_preservesZeroMorphisms : (idempotentPart p).PreservesZeroMorphisms where
  map_zero A B := (cancel_mono (kernel.ι (𝟙 B - p.app' B))).1 (by
    change kernel.lift _ (kernel.ι (𝟙 A - p.app' A) ≫ 0) _ ≫ kernel.ι _ = 0 ≫ kernel.ι _
    rw [kernel.lift_ι, comp_zero, zero_comp])

/-- The summand functor on a morphism `f` is the restriction of `f` to the summands. -/
theorem idempotentPart_map_ι {A B : C} (f : A ⟶ B) :
    (idempotentPart p).map f ≫ (idempotentPartι p).app B = (idempotentPartι p).app A ≫ f :=
  kernel.lift_ι _ _ _

/-- The inclusion of the summand is a monomorphism. -/
instance mono_idempotentPartι_app (A : C) : Mono ((idempotentPartι p).app A) :=
  inferInstanceAs (Mono (kernel.ι _))

/-- The summand functor is additive. -/
instance idempotentPart_additive : (idempotentPart p).Additive where
  map_add {A B} {f g} := (cancel_mono ((idempotentPartι p).app B)).1 (by
    rw [Preadditive.add_comp, idempotentPart_map_ι, idempotentPart_map_ι, idempotentPart_map_ι,
      Preadditive.comp_add])

/-- **The summand cut out by an idempotent endomorphism of the identity is exact**: it preserves
homology. -/
theorem idempotentPart_preservesHomology (hp : p ≫ p = p) : (idempotentPart p).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (fun S hS => by
    rw [ShortComplex.exact_iff_isZero_homology] at hS ⊢
    let i : S.map (idempotentPart p) ⟶ S :=
      ⟨(idempotentPartι p).app _, (idempotentPartι p).app _, (idempotentPartι p).app _,
        ((idempotentPartι p).naturality _).symm, ((idempotentPartι p).naturality _).symm⟩
    let r : S ⟶ S.map (idempotentPart p) :=
      ⟨(idempotentPartπ hp).app _, (idempotentPartπ hp).app _, (idempotentPartπ hp).app _,
        ((idempotentPartπ hp).naturality _).symm, ((idempotentPartπ hp).naturality _).symm⟩
    have hir : i ≫ r = 𝟙 _ := by
      ext <;> exact idempotentPartι_π hp _
    have : Mono (ShortComplex.homologyMap i) := by
      refine ⟨fun g h hgh => ?_⟩
      have := congrArg (· ≫ ShortComplex.homologyMap r) hgh
      simpa only [Category.assoc, ← ShortComplex.homologyMap_comp, hir,
        ShortComplex.homologyMap_id, Category.comp_id] using this
    exact hS.of_mono (ShortComplex.homologyMap i))

/-- The summand cut out by an idempotent endomorphism of the identity preserves finite limits. -/
theorem idempotentPart_preservesFiniteLimits (hp : p ≫ p = p) :
    PreservesFiniteLimits (idempotentPart p) :=
  have := idempotentPart_preservesHomology hp
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- The summand cut out by an idempotent endomorphism of the identity preserves finite colimits. -/
theorem idempotentPart_preservesFiniteColimits (hp : p ≫ p = p) :
    PreservesFiniteColimits (idempotentPart p) :=
  have := idempotentPart_preservesHomology hp
  Functor.preservesFiniteColimits_of_preservesHomology _


section Transport

/-- **A left adjoint commutes with natural endomorphisms of the identity which its right adjoint
commutes with.** If `R` carries `β` to `α`, then `L` carries `α` to `β`. -/
theorem map_app_of_adjunction {D : Type*} [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D) (hR : ∀ Y, R.map (β.app Y) = α.app (R.obj Y)) (X : C) :
    L.map (α.app X) = β.app (L.obj X) := by
  apply (adj.homEquiv X (L.obj X)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hR]
  have h₁ := adj.unit.naturality (α.app X)
  have h₂ := α.naturality (adj.unit.app X)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h₁ h₂
  rw [← h₁, h₂]

variable {D : Type*} [Category* D] [Abelian D] (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ]
  (q : 𝟭 D ⟶ 𝟭 D)

/-- **A left exact functor commuting with the idempotents commutes with their summands**: if
`Φ (p A) = q (Φ A)` for every `A`, then `Φ` carries the summand of `A` cut out by `p` to the
summand of `Φ A` cut out by `q`. -/
def idempotentPartMapIso (hΦ : ∀ A, Φ.map (p.app A) = q.app (Φ.obj A)) (A : C) :
    Φ.obj ((idempotentPart p).obj A) ≅ (idempotentPart q).obj (Φ.obj A) :=
  PreservesKernel.iso Φ (𝟙 A - p.app' A) ≪≫
    kernelIsoOfEq (by rw [Functor.map_sub, Functor.map_id]; exact congrArg (𝟙 _ - ·) (hΦ A))

end Transport

section Decomposition

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ι → (𝟭 C ⟶ 𝟭 C)}

/-- The projection onto the summand of an idempotent `p`, followed by its inclusion, is `p`. -/
theorem idempotentPartπ_ι (hp : p ≫ p = p) (A : C) :
    (idempotentPartπ hp).app A ≫ (idempotentPartι p).app A = p.app A :=
  kernel.lift_ι _ _ _

/-- `p` restricts to the identity on the summand it cuts out. -/
theorem idempotentPartι_comp_app (A : C) :
    (idempotentPartι p).app A ≫ p.app A = (idempotentPartι p).app A :=
  kernel_ι_comp_app_eq A

/-- **A complete family of orthogonal idempotent endomorphisms of the identity splits every
object** into the direct sum of the summands they cut out. -/
@[ega "IV 2.5.8.8" "partial"]
def idempotentDecompositionIso (hq : ∀ i, q i ≫ q i = q i) (ho : ∀ i j, i ≠ j → q i ≫ q j = 0)
    (hs : ∑ i, q i = 𝟙 (𝟭 C)) (A : C) :
    A ≅ ⨁ fun i => (idempotentPart (q i)).obj A where
  hom := ∑ i, (idempotentPartπ (hq i)).app A ≫
    biproduct.ι (fun i => (idempotentPart (q i)).obj A) i
  inv := biproduct.desc fun i => (idempotentPartι (q i)).app A
  hom_inv_id := by
    simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_desc, idempotentPartπ_ι]
    simpa [NatTrans.app_sum] using congrArg (fun t => t.app A) hs
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ (fun j => ?_)
    simp only [biproduct.ι_desc_assoc, Preadditive.comp_sum, Category.comp_id]
    rw [Finset.sum_eq_single j]
    · rw [← Category.assoc, idempotentPartι_π, Category.id_comp]
    · intro i _ hij
      have h0 : (idempotentPartι (q j)).app A ≫ (idempotentPartπ (hq i)).app A = 0 := by
        refine (cancel_mono ((idempotentPartι (q i)).app A)).1 ?_
        rw [Category.assoc, idempotentPartπ_ι, zero_comp, ← idempotentPartι_comp_app (p := q j),
          Category.assoc]
        have := congrArg (fun t => t.app A) (ho j i (Ne.symm hij))
        simp only [NatTrans.comp_app, NatTrans.app_zero] at this
        rw [this, comp_zero]
      rw [← Category.assoc, h0, zero_comp]
    · simp

/-- The decomposition `CategoryTheory.idempotentDecompositionIso` is natural in the object. -/
theorem idempotentDecompositionIso_hom_naturality (hq : ∀ i, q i ≫ q i = q i)
    (ho : ∀ i j, i ≠ j → q i ≫ q j = 0) (hs : ∑ i, q i = 𝟙 (𝟭 C)) {A B : C} (f : A ⟶ B) :
    f ≫ (idempotentDecompositionIso hq ho hs B).hom =
      (idempotentDecompositionIso hq ho hs A).hom ≫
        biproduct.map fun i => (idempotentPart (q i)).map f := by
  simp only [idempotentDecompositionIso, Preadditive.comp_sum, Preadditive.sum_comp,
    Category.assoc, biproduct.ι_map]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact (idempotentPartπ (hq i)).naturality f

end Decomposition

end CategoryTheory

namespace Stacks.EtaleCohomology

universe w r

variable {Λ : Type r} [Ring Λ] (c : Λ) (hc : ∀ a : Λ, a * c = c * a)

/-- Multiplication by a central element `c` of `Λ` is `Λ`-linear on every `Λ`-module. -/
def centralSMulLinear (M : Type*) [AddCommGroup M] [Module Λ M] : M →ₗ[Λ] M where
  toFun m := c • m
  map_add' := smul_add c
  map_smul' a m := by
    change c • a • m = a • c • m
    rw [smul_smul, smul_smul, hc a]

/-- Multiplication by a central element of `Λ`, as an endomorphism of the identity functor of
`Λ`-modules. -/
def moduleCatCentralEndo : 𝟭 (ModuleCat.{w} Λ) ⟶ 𝟭 _ where
  app M := ModuleCat.ofHom (centralSMulLinear c hc M)
  naturality _ _ f := by
    ext m
    exact (f.hom.map_smul c m).symm

/-- Multiplication by a central element of `Λ`, as an endomorphism of the identity functor of
sheaves of `Λ`-modules on any site: it is applied sectionwise. -/
def sheafCentralEndo {D : Type*} [Category* D] (J : GrothendieckTopology D) :
    𝟭 (Sheaf J (ModuleCat.{w} Λ)) ⟶ 𝟭 _ where
  app F := ⟨Functor.whiskerLeft F.obj (moduleCatCentralEndo c hc)⟩
  naturality _ _ f := by
    ext U m
    exact (f.hom.app U).hom.map_smul c m |>.symm

/-- For a central idempotent `e`, multiplication by `e` is an idempotent endomorphism. -/
theorem sheafCentralEndo_idem {D : Type*} [Category* D] (J : GrothendieckTopology D) {e : Λ}
    (he : IsIdempotentElem e) (hc : ∀ a : Λ, a * e = e * a) :
    sheafCentralEndo e hc J ≫ sheafCentralEndo e hc J = sheafCentralEndo e hc J := by
  ext F U m
  show e • e • m = e • m
  rw [smul_smul, he.eq]

/-- **The primary decomposition of a finite ring.** A finite ring `Λ` carries a complete family
of orthogonal central idempotents `e_i`, indexed by the primes `ℓ_i` dividing its characteristic,
such that `ℓ_i ^ a_i` kills `e_i Λ`: the images in `Λ` of the idempotents of the Chinese remainder
decomposition `ℤ/n = ∏ ℤ/ℓ^a` of `ℤ/n`, `n` the characteristic of `Λ`. This is the decomposition
of `Λ` into its primary parts used in Step 3 of [Stacks, Tag 03UG]. -/
theorem exists_primary_completeOrthogonalIdempotents (Λ : Type r) [Ring Λ] [Finite Λ] :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → Λ) (ℓ a : ι → ℕ), CompleteOrthogonalIdempotents e ∧
      (∀ i (x : Λ), x * e i = e i * x) ∧ (∀ i, (ℓ i).Prime) ∧
      (∀ i, ((ℓ i ^ a i : ℕ) : Λ) * e i = 0) := by
  classical
  set n := ringChar Λ with hn
  have hn0 : n ≠ 0 := CharP.ringChar_ne_zero_of_finite Λ
  let ι := {p // p ∈ n.primeFactors}
  let ℓ : ι → ℕ := fun p => p.1
  let a : ι → ℕ := fun p => n.factorization p.1
  let q : ι → ℕ := fun p => ℓ p ^ a p
  have hprime : ∀ i, (ℓ i).Prime := fun i => Nat.prime_of_mem_primeFactors i.2
  have hcop : Pairwise (Function.onFun Nat.Coprime q) := fun i j hij =>
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (hprime i) (hprime j)).2
      (fun h => hij (Subtype.ext h)))
  have hprod : ∏ i, q i = n := by
    have h1 : ∏ i, q i = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      Finset.prod_coe_sort n.primeFactors (fun p => p ^ n.factorization p)
    rw [h1, ← Nat.support_factorization]
    exact Nat.factorization_prod_pow_eq_self hn0
  have : CharP Λ (∏ i, q i) := by rw [hprod, hn]; exact ringChar.charP Λ
  let φ := (ZMod.prodEquivPi q hcop).symm
  let ψ : ZMod (∏ i, q i) →+* Λ := ZMod.castHom (dvd_refl _) Λ
  let e₀ : ι → ZMod (∏ i, q i) := fun i => φ (Pi.single i 1)
  have he₀ : CompleteOrthogonalIdempotents e₀ :=
    (CompleteOrthogonalIdempotents.single (fun i => ZMod (q i))).map φ.toRingHom
  refine ⟨ι, inferInstance, fun i => ψ (e₀ i), ℓ, a, he₀.map ψ, fun i x => ?_, hprime, fun i => ?_⟩
  · have : ψ (e₀ i) = (((e₀ i).val : ℕ) : Λ) := by
      have : NeZero (∏ i, q i) := ⟨by rw [hprod]; exact hn0⟩
      exact ZMod.cast_eq_val (e₀ i)
    show x * ψ (e₀ i) = ψ (e₀ i) * x
    rw [this]
    exact (Nat.cast_commute _ x).symm.eq
  · have h0 : ((q i : ℕ) : ZMod (∏ j, q j)) * e₀ i = 0 := by
      apply (ZMod.prodEquivPi q hcop).injective
      rw [map_mul, map_zero, map_natCast]
      show (q i : ∀ j, ZMod (q j)) * (ZMod.prodEquivPi q hcop) (φ (Pi.single i 1)) = 0
      rw [show (ZMod.prodEquivPi q hcop) (φ (Pi.single i 1)) = Pi.single i 1 from
        (ZMod.prodEquivPi q hcop).apply_symm_apply _]
      ext j
      by_cases hij : j = i
      · subst hij
        simp
      · simp [hij]
    have := congrArg ψ h0
    rwa [map_mul, map_natCast, map_zero] at this

end Stacks.EtaleCohomology
