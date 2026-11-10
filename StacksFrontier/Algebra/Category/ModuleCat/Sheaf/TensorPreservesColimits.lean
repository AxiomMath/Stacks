module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Colimit.TensorProduct
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Basic
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Tensoring a sheaf of modules commutes with colimits

Let `(C, J)` be a site, `R` a sheaf of commutative rings on it and `F` a sheaf of `R`-modules.
Stacks 05NB says that the functor `G ↦ F ⊗_R G` on sheaves of modules commutes with arbitrary
colimits.

The tensor product of sheaves of modules is the sheafification of the objectwise tensor
product of the underlying presheaves, so the statement splits into two halves. At the presheaf
level the objectwise tensor product preserves colimits because colimits of presheaves of
modules are computed objectwise and, over a fixed ring, `M ⊗ -` is a left adjoint
(`moduleTensorAdjunction`). The second half is that sheafification may be moved across the
tensor product, i.e. that the comparison
`sheafify (F ⊗ P) ⟶ sheafify (F ⊗ sheafify P)` is an isomorphism; by the universal property of
the localization `sheafification` inverts, this is the statement that tensoring preserves the
class `J.W` of locally bijective maps of presheaves. That statement is `TensorLocalization`
below: local surjectivity is a covering-sieve chase on simple tensors, and local injectivity
is the delicate half — a relation among finitely many pure tensors is captured in a finitely
generated submodule of the target, the generators are lifted on a finite intersection of
covering image sieves, and right exactness of the tensor product then exhibits the restricted
relation as a finite sum of pure tensors with factors in the kernel, each of which dies on a
further covering sieve.

## Main definitions

* `PresheafOfModules.tensorBifunctor`: the native curried objectwise tensor product of
  presheaves of modules, with module size independent of ring size.
* `Stacks.SheafOfModules.Tensor.sheafTensor`: the canonical curried tensor product of sheaves
  of modules.
* `moduleTensorAdjunction`: the pointwise tensor-hom adjunction used to preserve colimits.

## Main results

* `tensorLeft_preservesColimits`: tensoring with a fixed sheaf of modules
  preserves all colimits indexed in the module universe.
* `TensorLocalization.W_whiskerRight`: tensoring preserves locally bijective maps of
  presheaves of modules. This is the engine of the above.

## Implementation notes

The ring and module universes are independent: the statement is for `R : Sheaf J CommRingCat.{w}`
and `F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R)` with `w` and `z` unrelated,
and the colimit diagrams have objects in the module universe `z` and morphisms in an arbitrary
universe `a`. The ringed-space form of the tag is the case `C = Opens X`,
`J = Opens.grothendieckTopology X`.

`TensorLocalization` retains the finite-relation and covering-sieve results establishing
stability of local bijections in independent ring and module universes. Every tensor object and
morphism in those statements is the canonical root `PresheafOfModules.tensorObj` or
`PresheafOfModules.tensorHom`; there is no separate tensor implementation here.

Fixed-factor functors are used directly as components of the native bifunctors. Generic
functor flipping supplies the right-tensor functor in the commutativity comparison, while
`Stacks.SheafOfModules.Tensor.ringSheaf` supplies the coefficient sheaf. The equalizer-sieve
membership lemma `mem_equalizerSieve_zero_iff` lets the finite-relation proofs convert the
restriction equation in term mode without changing the representation of tensor sections.

## References

* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA), sheafification and the
  tensor product.
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER), flatness and the
  objectwise tensor product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open PresheafOfModules (tensorObj tensorHom)

universe u v w z a

namespace Stacks.SheafOfModules.TensorColimits


attribute [local implicit_reducible] tensorObj tensorHom

namespace TensorLocalization
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Membership of `ψ` in the equalizer sieve of `x` and `0` is the vanishing of the restriction
of `x` along `ψ`. The two sides are the same proposition by definition; naming the equivalence
lets the proofs below convert in term mode, without rewriting underneath the identification of
the sections of a tensor-product presheaf with a tensor product of sections (that
identification is not available at the transparency `rw` uses to build its motive). -/
private lemma mem_equalizerSieve_zero_iff {F : Cᵒᵖ ⥤ AddCommGrpCat.{z}} {V : C}
    (x : ToType (F.obj (.op V))) {W : C} (ψ : W ⟶ V) :
    (Presheaf.equalizerSieve (F := F) (X := .op V) x 0).arrows ψ ↔
      ConcreteCategory.hom (F.map ψ.op) x = 0 :=
  ⟨fun h => h.trans (map_zero _), fun h => h.trans (map_zero _).symm⟩

/-- The restriction maps of `A ⊗ B` send `x ⊗ₜ y` to the tensor product of the restrictions of
`x` and `y`. -/
lemma tensorObj_map_tmul
    (A B : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : A.obj U) (y : B.obj U) :
    (tensorObj (O := 𝒪) A B).map f (x ⊗ₜ[𝒪.obj U] y) =
      A.map f x ⊗ₜ[𝒪.obj V] B.map f y := rfl

/-- The component of `f ⊗ 𝟙 X` sends `x ⊗ₜ y` to `f x ⊗ₜ y`. -/
lemma tensorRight_map_tmul
    {A B : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    (f : A ⟶ B) (X : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    (U : Cᵒᵖ) (x : A.obj U) (y : X.obj U) :
    ((tensorHom (O := 𝒪) f (𝟙 X)).app U).hom (x ⊗ₜ[𝒪.obj U] y) = f.app U x ⊗ₜ[𝒪.obj U] y := rfl

/-- Tensoring a locally surjective map is locally surjective. -/
theorem W_whiskerRight_isLocallySurjective
    {A B : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat)} (f : A ⟶ B)
    (X : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    (hf : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f)) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map
        (tensorHom (O := 𝒪) f (𝟙 X))) := by
  have simple : ∀ {U : C} (b : B.obj (.op U)) (x : X.obj (.op U)),
      Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map f) b ≤
        Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map (tensorHom (O := 𝒪) f (𝟙 X)))
          (b ⊗ₜ[𝒪.obj (.op U)] x) := by
    intro U b x V φ ⟨a, ha⟩
    refine ⟨a ⊗ₜ[𝒪.obj (.op V)] (X.map φ.op).hom x, ?_⟩
    change (ConcreteCategory.hom (f.app (.op V))) a ⊗ₜ[𝒪.obj (.op V)]
          (ConcreteCategory.hom (X.map φ.op)) x
        = (ConcreteCategory.hom (B.map φ.op)) b ⊗ₜ[𝒪.obj (.op V)]
          (ConcreteCategory.hom (X.map φ.op)) x
    exact congrArg
      (fun t => t ⊗ₜ[𝒪.obj (.op V)] (ConcreteCategory.hom (X.map φ.op)) x) ha
  constructor
  intro U t
  change Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map
    (tensorHom (O := 𝒪) f (𝟙 X))) t ∈ J U
  induction t using TensorProduct.inductionOn with
  | tmul b x =>
    exact J.superset_covering (simple b x) (hf.imageSieve_mem b)
  | add s t hs ht =>
    refine J.superset_covering ?_ (J.intersection_covering hs ht)
    rintro V φ ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
    refine ⟨a + c, ?_⟩
    rw [map_add, ha, hc]
    exact (map_add _ _ _).symm

/-- If the restriction of `k` along `ψ` vanishes, so does the restriction of `k ⊗ₜ y` along
`ψ` in `A ⊗ X`. -/
theorem restrict_tmul_ker_eq_zero
    {A : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    (X : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    {V : C} (k : A.obj (.op V)) (y : X.obj (.op V)) {W : C} (ψ : W ⟶ V)
    (hψ : (ConcreteCategory.hom (A.map ψ.op)) k = 0) :
    ((tensorObj (O := 𝒪) A X).map ψ.op).hom (k ⊗ₜ[𝒪.obj (.op V)] y) = 0 := by
  change (ConcreteCategory.hom (A.map ψ.op)) k ⊗ₜ[𝒪.obj (.op W)]
      (ConcreteCategory.hom (X.map ψ.op)) y = 0
  rw [hψ, TensorProduct.zero_tmul]

/-- If `f` is locally injective and `f k = 0`, then `k ⊗ₜ y` vanishes locally in `A ⊗ X`: the
sieve on which its restriction is zero is covering. -/
theorem c3_single
    {A B : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat)} (f : A ⟶ B)
    (X : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f))
    {V : C} (k : A.obj (.op V)) (y : X.obj (.op V))
    (hk : (f.app (.op V)).hom k = 0) :
    Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
        (tensorObj (O := 𝒪) A X))
      (X := .op V)
      (k ⊗ₜ[𝒪.obj (.op V)] y) 0 ∈ J V := by
  have hcov : Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj A) (X := .op V)
      k 0 ∈ J V := by
    apply Presheaf.IsLocallyInjective.equalizerSieve_mem
      (φ := (PresheafOfModules.toPresheaf _).map f)
    change (f.app (.op V)).hom k = (f.app (.op V)).hom 0
    rw [hk, map_zero]
  refine J.superset_covering ?_ hcov
  intro W ψ hψ
  exact (mem_equalizerSieve_zero_iff _ ψ).mpr
    (restrict_tmul_ker_eq_zero 𝒪 X k y ψ ((mem_equalizerSieve_zero_iff _ ψ).mp hψ))

/-- If two sections of `A ⊗ X` vanish locally, so does their sum. -/
theorem eq_sieve_add
    {A : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    (X : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    {V : C} (u v : (tensorObj (O := 𝒪) A X).obj (.op V))
    (hu : Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
        (tensorObj (O := 𝒪) A X)) (X := .op V)
      u 0 ∈ J V)
    (hv : Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
        (tensorObj (O := 𝒪) A X)) (X := .op V)
      v 0 ∈ J V) :
    Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
        (tensorObj (O := 𝒪) A X)) (X := .op V)
      (u + v) 0 ∈ J V := by
  refine J.superset_covering ?_ (J.intersection_covering hu hv)
  intro W ψ ⟨h1, h2⟩
  have e1 := (mem_equalizerSieve_zero_iff _ ψ).mp h1
  have e2 := (mem_equalizerSieve_zero_iff _ ψ).mp h2
  refine (mem_equalizerSieve_zero_iff _ ψ).mpr ?_
  calc (ConcreteCategory.hom
        (((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
          (tensorObj (O := 𝒪) A X)).map ψ.op)) (u + v)
      = _ + _ := map_add _ u v
    _ = (0 : _) + 0 := congrArg₂ (· + ·) e1 e2
    _ = 0 := add_zero 0

/-- If `f` is locally injective, then a finite sum of pure tensors `k ⊗ₜ y` with each `k` in the
kernel of `f` vanishes locally in `A ⊗ X`. -/
theorem c3_sum
    {A B : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat)} (f : A ⟶ B)
    (X : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f))
    {V : C} (S : Finset (A.obj (.op V) × X.obj (.op V)))
    (hS : ∀ p ∈ S, (f.app (.op V)).hom p.1 = 0) :
    Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
        (tensorObj (O := 𝒪) A X)) (X := .op V)
      (∑ p ∈ S, p.1 ⊗ₜ[𝒪.obj (.op V)] p.2) 0 ∈ J V := by
  classical
  induction S using Finset.induction with
  | empty =>
    refine J.superset_covering (fun W ψ _ => ?_) (J.top_mem V)
    exact (mem_equalizerSieve_zero_iff _ ψ).mpr (map_zero _)
  | insert a s ha ih =>
    have hsplit : ∑ p ∈ insert a s, p.1 ⊗ₜ[𝒪.obj (.op V)] p.2
        = a.1 ⊗ₜ[𝒪.obj (.op V)] a.2 + ∑ p ∈ s, p.1 ⊗ₜ[𝒪.obj (.op V)] p.2 :=
      Finset.sum_insert ha
    refine Eq.mpr (congrArg (fun t => Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
        (tensorObj (O := 𝒪) A X))
      (X := .op V) t 0 ∈ J V) hsplit) ?_
    exact eq_sieve_add 𝒪 X _ _
      (c3_single 𝒪 f X hinj a.1 a.2 (hS a (Finset.mem_insert_self a s)))
      (ih (fun p hp => hS p (Finset.mem_insert_of_mem hp)))

/-- Right exactness extracts a finite kernel decomposition after restriction. -/
theorem sum_tmul_restrict_ker_decomp
    {RU RV : Type w} [CommRing RU] [CommRing RV] (ρ : RU →+* RV)
    {AU BU XU AV BV XV : Type z}
    [AddCommGroup AU] [AddCommGroup BU] [AddCommGroup XU]
    [AddCommGroup AV] [AddCommGroup BV] [AddCommGroup XV]
    [Module RU AU] [Module RU BU] [Module RU XU]
    [Module RV AV] [Module RV BV] [Module RV XV]
    (fU : AU →ₗ[RU] BU) (fV : AV →ₗ[RV] BV)
    (rA : AU →ₛₗ[ρ] AV) (rB : BU →ₛₗ[ρ] BV) (rX : XU →ₛₗ[ρ] XV)
    (hnat : ∀ a, rB (fU a) = fV (rA a))
    {ι : Type z} [Fintype ι] (a : ι → AU) (x : ι → XU)
    (P : Submodule RU BU)
    (hmemP : ∀ i, fU (a i) ∈ P)
    (hsum0 : ∑ i, (⟨fU (a i), hmemP i⟩ : ↥P) ⊗ₜ[RU] x i = 0)
    (hlift : ∀ b : ↥P, rB b ∈ LinearMap.range fV) :
    ∃ S : Finset (AV × XV), (∀ p ∈ S, fV p.1 = 0) ∧
      ∑ i, (rA (a i)) ⊗ₜ[RV] (rX (x i)) = ∑ p ∈ S, p.1 ⊗ₜ[RV] p.2 := by
  classical
  let σ : ↥P →ₛₗ[ρ] ↥(LinearMap.range fV) :=
    { toFun := fun b => ⟨rB b, hlift b⟩
      map_add' := by intro b c; apply Subtype.ext; simp [map_add]
      map_smul' := by intro r b; apply Subtype.ext; simp [map_smulₛₗ] }
  let Φ := TensorProduct.map σ rX
  have hΦ0 : Φ (∑ i, (⟨fU (a i), hmemP i⟩ : ↥P) ⊗ₜ[RU] x i) = 0 := by
    rw [hsum0, map_zero]
  have hΦval : Φ (∑ i, (⟨fU (a i), hmemP i⟩ : ↥P) ⊗ₜ[RU] x i)
      = ∑ i, (fV.rangeRestrict (rA (a i))) ⊗ₜ[RV] (rX (x i)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => congrArg (· ⊗ₜ[RV] rX (x i)) (Subtype.ext (hnat (a i)))
  have hzero : ∑ i, (fV.rangeRestrict (rA (a i))) ⊗ₜ[RV] (rX (x i)) = 0 := by
    rw [← hΦval, hΦ0]
  set z' : TensorProduct RV AV XV := ∑ i, (rA (a i)) ⊗ₜ[RV] (rX (x i)) with hz'
  have hrt : LinearMap.rTensor XV fV.rangeRestrict z' = 0 := by
    rw [hz', map_sum]
    rw [← hzero]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.rTensor_tmul]
  have hg : Function.Surjective fV.rangeRestrict := LinearMap.surjective_rangeRestrict fV
  have hexact : Function.Exact (LinearMap.ker fV.rangeRestrict).subtype fV.rangeRestrict :=
    LinearMap.exact_subtype_ker_map fV.rangeRestrict
  have hT := rTensor_exact XV hexact hg
  rw [LinearMap.exact_iff] at hT
  have hmem : z' ∈ LinearMap.range (LinearMap.rTensor XV (LinearMap.ker
      fV.rangeRestrict).subtype) := by
    rw [← hT]; exact hrt
  obtain ⟨w, hw⟩ := hmem
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset w
  let emb : (LinearMap.ker fV.rangeRestrict × XV) ↪ (AV × XV) :=
    ⟨fun p => ((p.1 : AV), p.2), by
      intro u v huv
      simp only [Prod.mk.injEq, Subtype.coe_inj] at huv
      exact Prod.ext huv.1 huv.2⟩
  refine ⟨S.map emb, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_map, emb] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hk : (q.1 : AV) ∈ LinearMap.ker fV := by
      rw [← LinearMap.ker_rangeRestrict fV]; exact q.1.2
    exact hk
  · rw [← hw, hS, map_sum, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [emb, LinearMap.rTensor_tmul, Submodule.subtype_apply]
    rfl

/-- A finite intersection of covering sieves is covering. -/
theorem iInf_finset_covering {U : C} {β : Type z} (s : Finset β) (Gs : β → Sieve U)
    (hGs : ∀ b ∈ s, Gs b ∈ J U) : (⨅ b ∈ s, Gs b) ∈ J U := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.iInf_insert]
    exact J.intersection_covering (hGs b (Finset.mem_insert_self b s))
      (ih (fun x hx => hGs x (Finset.mem_insert_of_mem hx)))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- A finite tensor relation lifts on a covering sieve, using local surjectivity. -/
theorem exists_locally_ker_decomp
    {A B : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat)} (f : A ⟶ B)
    (X : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    (hf : J.W ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f))
    (U : C) (z : (tensorObj (O := 𝒪) A X).obj (.op U))
    (hz : ((tensorHom (O := 𝒪) f (𝟙 X)).app (.op U)).hom z = 0) :
    ∃ G : Sieve U, G ∈ J U ∧
      ∀ ⦃V : C⦄ (ψ : V ⟶ U), G.arrows ψ →
        ∃ S : Finset (A.obj (.op V) × X.obj (.op V)),
          (∀ p ∈ S, (f.app (.op V)).hom p.1 = 0) ∧
          ((tensorObj (O := 𝒪) A X).map ψ.op).hom z = ∑ p ∈ S, p.1 ⊗ₜ[𝒪.obj (.op V)] p.2 := by
  classical
  have hsurj := hf.isLocallySurjective
  obtain ⟨S₀, hS₀⟩ := TensorProduct.exists_finset z
  set aa : {p : A.obj (.op U) × X.obj (.op U) // p ∈ S₀} → A.obj (.op U) :=
    fun p => (p : A.obj (.op U) × X.obj (.op U)).1 with haa
  set xx : {p : A.obj (.op U) × X.obj (.op U) // p ∈ S₀} → X.obj (.op U) :=
    fun p => (p : A.obj (.op U) × X.obj (.op U)).2 with hxx
  have hzsum : z = ∑ i, aa i ⊗ₜ[𝒪.obj (.op U)] xx i := by
    rw [hS₀]
    exact (Finset.sum_coe_sort S₀ (fun p => p.1 ⊗ₜ[𝒪.obj (.op U)] p.2)).symm
  have hzero0 : ∑ i, (f.app (.op U)).hom (aa i) ⊗ₜ[𝒪.obj (.op U)] xx i = 0 := by
    have hcalc : ((tensorHom (O := 𝒪) f (𝟙 X)).app (.op U)).hom z
        = ∑ i, (f.app (.op U)).hom (aa i) ⊗ₜ[𝒪.obj (.op U)] xx i := by
      rw [hzsum, map_sum]
      rfl
    rw [← hcalc, hz]
  -- Capture the tensor relation in a finitely generated submodule.
  set N₀ : Submodule (𝒪.obj (.op U)) (B.obj (.op U)) :=
    Submodule.span (𝒪.obj (.op U)) (Set.range (fun i => (f.app (.op U)).hom (aa i))) with hN₀
  have hmem0 : ∀ i, (f.app (.op U)).hom (aa i) ∈ N₀ :=
    fun i => Submodule.subset_span (Set.mem_range_self i)
  set t₀ : TensorProduct (𝒪.obj (.op U)) (↥N₀) (X.obj (.op U)) :=
    ∑ i, (⟨(f.app (.op U)).hom (aa i), hmem0 i⟩ : ↥N₀) ⊗ₜ[𝒪.obj (.op U)] xx i with ht₀
  have hsub : (LinearMap.rTensor (X.obj (.op U)) N₀.subtype) t₀
      = (LinearMap.rTensor (X.obj (.op U)) N₀.subtype) 0 := by
    rw [ht₀, map_sum, map_zero]
    simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
    exact hzero0
  obtain ⟨N', hN'fg, hle, hN'eq⟩ :=
    (Submodule.fg_span (Set.finite_range _)).exists_rTensor_fg_inclusion_eq hsub
  have hmemP : ∀ i, (f.app (.op U)).hom (aa i) ∈ N' := fun i => hle (hmem0 i)
  have hsum0 : ∑ i, (⟨(f.app (.op U)).hom (aa i), hmemP i⟩ : ↥N') ⊗ₜ[𝒪.obj (.op U)] xx i = 0 := by
    have e1 : (LinearMap.rTensor (X.obj (.op U)) (Submodule.inclusion hle)) t₀
        = ∑ i, (⟨(f.app (.op U)).hom (aa i), hmemP i⟩ : ↥N') ⊗ₜ[𝒪.obj (.op U)] xx i := by
      rw [ht₀, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.rTensor_tmul]
      rfl
    rw [← e1, hN'eq, map_zero]
  -- Lift all generators on a finite intersection of covering image sieves.
  obtain ⟨gens, hgens⟩ := hN'fg
  set G : Sieve U := ⨅ g ∈ gens, Presheaf.imageSieve
    ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f) g with hG
  have hGcov : G ∈ J U :=
    iInf_finset_covering gens _ (fun g _ => hsurj.imageSieve_mem g)
  refine ⟨G, hGcov, ?_⟩
  intro V ψ hψ
  have hliftgen : ∀ g ∈ gens, (B.map ψ.op).hom g ∈ LinearMap.range (f.app (.op V)).hom := by
    intro g hg
    have hgψ : (Presheaf.imageSieve
        ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f) g).arrows ψ := by
      have hle2 : G ≤ Presheaf.imageSieve
          ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f) g :=
        iInf_le_of_le g (iInf_le _ hg)
      exact hle2 _ hψ
    obtain ⟨a', ha'⟩ := hgψ
    exact ⟨a', ha'⟩
  have hlift : ∀ b : ↥N',
      (B.restrictₛₗ ψ.op) (b : B.obj (.op U)) ∈ LinearMap.range (f.app (.op V)).hom := by
    rintro ⟨b, hb⟩
    change (B.map ψ.op).hom b ∈ _
    rw [← hgens] at hb
    induction hb using Submodule.span_induction with
    | mem g hg => exact hliftgen g hg
    | zero => rw [map_zero]; exact zero_mem _
    | add u v hu hv ihu ihv => rw [map_add]; exact add_mem ihu ihv
    | smul r u hu ihu => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ ihu
  -- Right exactness now gives a finite decomposition into kernel tensors.
  obtain ⟨S, hSker, hSdec⟩ := sum_tmul_restrict_ker_decomp
    (ρ := ((𝒪 ⋙ forget₂ CommRingCat RingCat).map ψ.op).hom)
    (fU := (f.app (.op U)).hom) (fV := (f.app (.op V)).hom)
    (rA := A.restrictₛₗ ψ.op) (rB := B.restrictₛₗ ψ.op)
    (rX := X.restrictₛₗ ψ.op)
    (hnat := fun a => (PresheafOfModules.naturality_apply f ψ.op a).symm)
    (a := aa) (x := xx) (P := N') (hmemP := hmemP) (hsum0 := hsum0) (hlift := hlift)
  refine ⟨S, hSker, ?_⟩
  rw [hzsum, map_sum]
  exact hSdec

/-- If `f` is in `J.W` and locally injective, then every section of `A ⊗ X` killed by `f ⊗ 𝟙 X`
vanishes locally. -/
theorem equalizerSieve_zero_mem_of_whiskerRight_eq_zero
    {A B : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat)} (f : A ⟶ B)
    (X : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    (hf : J.W ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f))
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f))
    (U : C) (z : (tensorObj (O := 𝒪) A X).obj (.op U))
    (hz : ((tensorHom (O := 𝒪) f (𝟙 X)).app (.op U)).hom z = 0) :
    Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
        (tensorObj (O := 𝒪) A X)) (X := .op U)
      z 0 ∈ J U := by
  obtain ⟨G, hG, hGdec⟩ := exists_locally_ker_decomp 𝒪 f X hf U z hz
  apply J.transitive hG
  intro V ψ hψ
  obtain ⟨S, hSker, hSdec⟩ := hGdec ψ hψ
  refine J.superset_covering ?_ (c3_sum 𝒪 f X hinj S hSker)
  intro W φ hφ
  have hφ' := (mem_equalizerSieve_zero_iff _ φ).mp hφ
  refine (mem_equalizerSieve_zero_iff _ (φ ≫ ψ)).mpr ?_
  exact (PresheafOfModules.map_comp_apply (tensorObj (O := 𝒪) A X) ψ.op φ.op z).trans
    ((congrArg (fun t => ((tensorObj (O := 𝒪) A X).map φ.op).hom t) hSdec).trans hφ')

/-- If `f` is in `J.W`, then `f ⊗ 𝟙 X` is locally injective. -/
theorem W_whiskerRight_isLocallyInjective_of_W
    {A B : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat)} (f : A ⟶ B)
    (X : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    (hf : J.W ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f)) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map
        (tensorHom (O := 𝒪) f (𝟙 X))) := by
  have hinj := hf.isLocallyInjective
  apply Presheaf.IsLocallyInjective.mk
  intro U z₁ z₂ hz
  have hzeq : Presheaf.equalizerSieve z₁ z₂
      = Presheaf.equalizerSieve
          (F := (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
            (tensorObj (O := 𝒪) A X)) (X := U)
          (z₁ - z₂) 0 := by
    apply Sieve.ext
    intro W ψ
    rw [Presheaf.equalizerSieve_apply, Presheaf.equalizerSieve_apply]
    constructor
    · intro h
      rw [map_sub, map_zero, sub_eq_zero]; exact h
    · intro h
      rw [map_sub, map_zero, sub_eq_zero] at h; exact h
  rw [hzeq]
  have hz' : ((tensorHom (O := 𝒪) f (𝟙 X)).app U).hom (z₁ - z₂) = 0 :=
    (map_sub ((tensorHom (O := 𝒪) f (𝟙 X)).app U).hom z₁ z₂).trans
      (sub_eq_zero_of_eq
        (show ((tensorHom (O := 𝒪) f (𝟙 X)).app U).hom z₁ =
          ((tensorHom (O := 𝒪) f (𝟙 X)).app U).hom z₂ from hz))
  exact equalizerSieve_zero_mem_of_whiskerRight_eq_zero 𝒪 f X hf hinj (Opposite.unop U)
    (z₁ - z₂) (by simpa using hz')

/-- Local bijections remain local bijections after tensoring: if the underlying map of
presheaves of abelian groups of `f` is locally bijective, so is that of `f ▷ X`. This is the
`J.W`-stability that makes sheafification pass through the tensor product, stated at
independent ring and module universes. -/
public theorem W_whiskerRight
    {A B : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat)} (f : A ⟶ B)
    (X : PresheafOfModules.{z} (𝒪 ⋙ forget₂ CommRingCat RingCat))
    (hf : J.W ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map f)) :
    J.W ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map
      (tensorHom (O := 𝒪) f (𝟙 X))) := by
  have := W_whiskerRight_isLocallyInjective_of_W 𝒪 f X hf
  have := W_whiskerRight_isLocallySurjective 𝒪 f X hf.isLocallySurjective
  exact J.W_of_isLocallyBijective _

end TensorLocalization

open scoped TensorProduct
open Opposite

/-- The functor `N ↦ M ⊗[R] N` on `R`-modules, with the module universe independent of the ring
universe: Mathlib's monoidal `tensorLeft` ties the two together, so this is restated by
hand. Shared by `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FlatColimits` and
`StacksFrontier.CategoryTheory.Sites.Modules.TensorColimits`, which build the same functor for the
same reason; not `private` so that they can use this one instead of restating it. -/
noncomputable def moduleTensorLeft {R : Type w} [CommRing R] (M : ModuleCat.{z} R) :
    ModuleCat.{z} R ⥤ ModuleCat.{z} R where
  obj N := ModuleCat.of R (M ⊗[R] N)
  map f := ModuleCat.ofHom (TensorProduct.map LinearMap.id f.hom)
  map_id N := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intros
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intros
    rfl

/-- The tensor-hom equivalence `(M ⊗[R] N ⟶ P) ≃ (N ⟶ Hom(M, P))`, exhibiting
`moduleTensorLeft M` as a left adjoint; the data underlying `moduleTensorAdjunction`, which this
section's `@[expose]` requires to be as public as that adjunction. -/
noncomputable def moduleTensorHomEquiv {R : Type w} [CommRing R] (M N P : ModuleCat.{z} R) :
    ((moduleTensorLeft M).obj N ⟶ P) ≃
      (N ⟶ ((linearCoyoneda R (ModuleCat.{z} R)).obj (op M)).obj P) where
  toFun f := ModuleCat.ofHom₂ (TensorProduct.curry f.hom).flip
  invFun f := ModuleCat.ofHom (TensorProduct.lift f.hom₂.flip)
  left_inv f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intros
    rfl
  right_inv f := by
    ext x y
    rfl

/-- Tensoring on the left by a module is left adjoint to the hom functor out of it. Shared by
`StacksFrontier.CategoryTheory.Sites.Modules.TensorColimits`, which needs the same adjunction to
transport colimit-preservation across the same `moduleTensorLeft`; not `private` for that
reason. -/
noncomputable def moduleTensorAdjunction {R : Type w} [CommRing R] (M : ModuleCat.{z} R) :
    moduleTensorLeft M ⊣ (linearCoyoneda R (ModuleCat.{z} R)).obj (op M) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N P => moduleTensorHomEquiv M N P
      homEquiv_naturality_left_symm := by
        intros
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intros
        rfl
      homEquiv_naturality_right := by
        intros
        ext x
        rfl }

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Tensoring on the left by a presheaf of modules `F` is isomorphic to tensoring on the right
by `F`: the functors `(PresheafOfModules.tensorBifunctor R.obj).obj F` and
`(PresheafOfModules.tensorBifunctor R.obj).flip.obj F` are isomorphic. -/
public noncomputable def tensorCommIso (R : Sheaf J CommRingCat.{w})
    (F : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :
    ((PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).obj F) ≅
      ((PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).flip.obj F) :=
  letI modF (X : Cᵒᵖ) : Module (ToType (R.obj.obj X)) (ToType (F.obj X)) :=
    (F.obj X).isModule
  letI modG (G : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) (X : Cᵒᵖ) :
      Module (ToType (R.obj.obj X)) (ToType (G.obj X)) := (G.obj X).isModule
  NatIso.ofComponents (fun G => PresheafOfModules.isoMk
    (fun X => (TensorProduct.comm (R.obj.obj X) (F.obj X) (G.obj X)).toModuleIso)
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.inductionOn with
      | add x y hx hy =>
        exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
      | tmul x y => rfl)) (by
        intro G H f
        ext X : 1
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro t
        induction t using TensorProduct.inductionOn with
        | add x y hx hy =>
        exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
        | tmul x y => rfl)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [HasWeakSheafify J AddCommGrpCat.{z}]

/-- Sheafification inverts the morphisms that tensoring on the left sends into the
localization class: if `f` becomes invertible after sheafification, so does `F ⊗ f`.

Public because `tensorSheafificationIsoGeneral` below uses it, and a `public` declaration may
not reference a `private` one inside this file's `@[expose] public section`. -/
public lemma sheafification_inverts_tensorLeft (R : Sheaf J CommRingCat.{w})
    (F : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    {P Q : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj} (f : P ⟶ Q)
    (hf : IsIso ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map f)) :
    IsIso ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map
        ((((PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).obj F)).map f)) := by
  let L := PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
  have key : ∀ {P Q : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj}
      (g : P ⟶ Q),
      IsIso (L.map g) ↔ J.W ((PresheafOfModules.toPresheaf _).map g) := by
    intro P Q g
    change MorphismProperty.isomorphisms _ (L.map g) ↔ _
    change ((MorphismProperty.isomorphisms _).inverseImage L) g ↔ _
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
    rfl
  have hright : IsIso (L.map
      ((((PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).flip.obj F)).map f)) :=
    (key _).mpr (TensorLocalization.W_whiskerRight R.obj f F ((key f).mp hf))
  let e := tensorCommIso J R F
  have he : (((PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).obj F)).map f =
      e.hom.app P ≫ (((PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).flip.obj F)).map f ≫
        e.inv.app Q := by
    exact ((Iso.eq_comp_inv (e.app Q)).2 (e.hom.naturality f)).trans
      (Category.assoc _ _ _)
  have hcomp : L.map ((((PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).obj F)).map f)
      = L.map (e.hom.app P) ≫
        L.map ((((PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).flip.obj F)).map f) ≫
          L.map (e.inv.app Q) :=
    (congrArg L.map he).trans
      ((L.map_comp _ _).trans
        (congrArg (fun t => L.map (e.hom.app P) ≫ t) (L.map_comp _ _)))
  exact hcomp.symm ▸ ((L.mapIso (e.app P)) ≪≫
    (@asIso _ _ _ _ (L.map
      (((PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).flip.obj F).map f)) hright) ≪≫
        (L.mapIso (e.app Q)).symm).isIso_hom

/-- Tensoring commutes with sheafification: `(- ⊗ F)` followed by sheafification is isomorphic
to sheafification followed by the sheaf-level `(- ⊗ F)`.

Naturality compares the tensor of an identity scalar restriction with the original tensor. -/
public noncomputable def tensorSheafificationIsoGeneral
    (R : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (show PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj ⥤
        PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj from
      (PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).obj F.val) ⋙
        PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) ≅
      PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).obj F) := by
  let L := PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
  let forgetThenRestrict : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R) ⥤
      PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj :=
    SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R) ⋙
      PresheafOfModules.restrictScalars (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
  let adj : L ⊣ forgetThenRestrict := PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
  let tensorThenSheafify : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj ⥤
      SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R) :=
    ((PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).obj F.val) ⋙ L
  let τ : tensorThenSheafify ⟶
      L ⋙ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).obj F) :=
    { app := fun presheaf => tensorThenSheafify.map (adj.unit.app presheaf)
      naturality := fun sourcePresheaf targetPresheaf morphism => by
        change tensorThenSheafify.map morphism ≫
            tensorThenSheafify.map (adj.unit.app targetPresheaf) =
          tensorThenSheafify.map (adj.unit.app sourcePresheaf) ≫
            tensorThenSheafify.map (forgetThenRestrict.map (L.map morphism))
        exact (tensorThenSheafify.map_comp morphism (adj.unit.app targetPresheaf)).symm.trans
          ((congrArg (tensorThenSheafify.map (X := sourcePresheaf)
            (Y := forgetThenRestrict.obj (L.obj targetPresheaf)))
              (adj.unit.naturality morphism)).trans
              (tensorThenSheafify.map_comp (adj.unit.app sourcePresheaf)
                (forgetThenRestrict.map (L.map morphism)))) }
  have hτ (P) : IsIso (τ.app P) := by
    apply sheafification_inverts_tensorLeft
    exact PresheafOfModules.sheafification_map_unit_isIso
      (Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) P
  letI : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

omit [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}] in
/-- Tensoring with a fixed sheaf of modules commutes with all small colimits, independently of
the ring universe. -/
@[stacks 05NB, sga "5 V 1.2.1" "inductive limits"]
public theorem tensorLeft_preservesColimits (R : Sheaf J CommRingCat.{w})
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimitsOfSize.{a, z}
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).obj F)) := by
  have : HasColimitsOfSize.{a, z} AddCommGrpCat.{z} := ⟨fun {_ _} => inferInstance⟩
  let h : PreservesColimitsOfSize.{a, z}
      (show PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj ⥤
          PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj from
        (PresheafOfModules.tensorBifunctor.{v, u, w, z, z} R.obj).obj F.val) :=
    { preservesColimitsOfShape :=
        { preservesColimit := fun {K} =>
            { preserves := fun {c} hc => by
                refine ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X => ?_)⟩
                let M : ModuleCat.{z} (R.obj.obj X) := F.val.obj X
                -- `moduleTensorLeft M` is a left adjoint, hence preserves colimits. The
                -- witness is applied directly rather than through `isColimitOfPreserves`:
                -- the latter takes it as an instance argument, and instance search does not
                -- see past the two spellings `ModuleCat (R.obj.obj X)` and
                -- `ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj X)` of the
                -- same category.
                have hM : PreservesColimitsOfSize.{a, z} (moduleTensorLeft M) :=
                  (moduleTensorAdjunction M).leftAdjoint_preservesColimits
                exact (hM.preservesColimitsOfShape.preservesColimit.preserves
                  (isColimitOfPreserves (PresheafOfModules.evaluation
                    (Stacks.SheafOfModules.Tensor.ringSheaf R).obj X) hc)).some } } }
  let : (SheafOfModules.forget.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R) ⋙
      PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).Full :=
    (PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).fullyFaithfulROfIsIsoCounit.full
  let : (SheafOfModules.forget.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R) ⋙
      PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).Faithful :=
    (PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).fullyFaithfulROfIsIsoCounit.faithful
  apply (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).preservesColimitsOfSize_iff
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).obj F)) |>.mpr
  exact preservesColimits_of_natIso (tensorSheafificationIsoGeneral J R F)

attribute [instance] tensorLeft_preservesColimits


end Stacks.SheafOfModules.TensorColimits

end
