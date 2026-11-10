module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.Algebra.Module.Adequate.SplittingRepresentabilityLarge
public import StacksFrontier.Algebra.Module.Adequate.SplittingWeightOneLarge

/-!
# Weight-space lifting and flat base change in an extension, at independent universes

This file carries two of the inputs of the splitting argument of Stacks 06V7 across the
single-universe diagonal: a weight-homogeneous element of the quotient term of an extension
lifts to a weight-homogeneous element of its middle term, and the middle term of a short exact
sequence commutes with flat base change as soon as its two outer terms do.

Everything is stated for `AdequateFunctor.ModuleValuedFunctor.{max u v w, v} A`: the algebras
are objects of `CommAlgCat.{max u v} A` and the values lie in `Type (max u v w)`, so the value
universe `w` is independent of the universe `v` of the algebra carriers and of the universe `u`
of the base ring. `StacksFrontier.Algebra.Module.Adequate.Splitting` proves the same statements at
the diagonal `ModuleValuedFunctor.{u, u} A`; those are left untouched.

## Main definitions

* `AdequateFunctor.baseChangeValueMap`: the canonical map `C ⊗[B] F(B) → F(C)`.

## Main results

* `AdequateFunctor.exists_weightSpace_lift_of_epi_large`: along an epimorphism of
  module-valued functors commuting with flat base change, a weight-`k` element of the target
  is the image of a weight-`k` element of the source.
* `AdequateFunctor.baseChangeValueMap_bijective`: the canonical base-change map of a functor
  commuting with flat base change is bijective.
* `AdequateFunctor.preservesFlatBaseChange_of_shortExact_large`: commuting with flat base
  change passes to the middle term of a short exact sequence.

## Implementation notes

The weight-space decomposition used for the lifting is Tag 06UZ at these universes,
`AdequateFunctor.LaurentLarge.existsUnique_finsupp_weightSpace_eq_large`.

The flat-base-change transfer is the four lemma. At the diagonal it is run categorically, by
tensoring the evaluated short complex with `C` through `MonoidalCategory.tensorLeft` and
comparing with the evaluation at `C`. That route is unavailable here: `ModuleCat` is monoidal
only when the module universe agrees with the ring universe, and here the values live in
`Type (max u v w)` while the ring `C` lives in `Type (max u v)`, so `tensorLeft` does not even
typecheck. The diagram chase is therefore run once, over variable abelian groups and variable
additive maps, as `bijective_of_exact_ladder`, and applied to the ladder whose rows are
`C ⊗[B] -` of the sections over `B` and the sections over `C`. Nothing in that lemma mentions a
module-valued functor, so no definitional unification is demanded at the concrete nested
arguments.

The exactness of the top row is `Module.Flat.lTensor_exact`, which is already polymorphic in
the universes of both tensor factors; the bottom row is
`AdequateFunctor.exact_component_preimage_large`.

`baseChangeValueMap` is the base-change comparison in the spelling that
`AdequateFunctor.LaurentLarge.PreservesFlatBaseChange` itself uses — a plain algebra map
`f : B →ₐ[A] C` with `Algebra B C` taken from `f`, rather than a morphism of the identity
functor's image — so the equivalence that hypothesis provides is recognised without any
instance transport. It is built with `LinearMap.liftBaseChange`.

## References

* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
* [Stacks Project, Tag 06UZ](https://stacks.math.columbia.edu/tag/06UZ)
* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace AdequateFunctor

/-! ### The remaining transition-map plumbing

`algebraValueLarge`, `algebraMapValueLarge` and `algebraMapValueLarge_naturality` are in
`StacksFrontier.Algebra.Module.Adequate.SplittingRepresentabilityLarge`; these three complete
the block. -/

/-- The transition maps compose. -/
public lemma algebraMapValueLarge_comp {A : Type u} [CommRing A]
    {B C D : Type (max u v)} [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D]
    (F : ModuleValuedFunctor.{max u v w, v} A) (f : B →ₐ[A] C) (g : C →ₐ[A] D)
    (x : algebraValueLarge F B) :
    algebraMapValueLarge F g (algebraMapValueLarge F f x) =
      algebraMapValueLarge F (g.comp f) x :=
  (F.map_comp_apply (CommAlgCat.ofHom f).op.op (CommAlgCat.ofHom g).op.op x).symm

/-- The transition map along the identity is the identity. -/
public lemma algebraMapValueLarge_id {A : Type u} [CommRing A]
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (F : ModuleValuedFunctor.{max u v w, v} A) (x : algebraValueLarge F B) :
    algebraMapValueLarge F (AlgHom.id A B) x = x :=
  F.presheaf.map_id_apply _ x

/-- `algebraMapValueLarge_naturality` with the morphism applied through the
concrete-category coercion, which is the spelling goals produced by `PresheafOfModules`
use. -/
public lemma algebraMapValueLarge_naturality' {A : Type u} [CommRing A]
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {F G : ModuleValuedFunctor.{max u v w, v} A} (η : F ⟶ G) (f : B →ₐ[A] C)
    (x : algebraValueLarge F B) :
    η.app (Opposite.op (Opposite.op (CommAlgCat.of A C))) (algebraMapValueLarge F f x) =
      algebraMapValueLarge G f (η.app (Opposite.op (Opposite.op (CommAlgCat.of A B))) x) :=
  algebraMapValueLarge_naturality η f x

/-! ### Lifting a weight-homogeneous element along an epimorphism -/

/-- A morphism of module-valued functors preserves the weight spaces. -/
public lemma weightSpace_map_large {A : Type u} [CommRing A] {B : Type (max u v)}
    [CommRing B] [Algebra A B] {F G : ModuleValuedFunctor.{max u v w, v} A} (η : F ⟶ G)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (x : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (hx : x ∈ LaurentLarge.weightSpace A B F 𝒜 k) :
    η.app _ x ∈ LaurentLarge.weightSpace A B G 𝒜 k := by
  change _ = _ at hx ⊢
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  exact (app_smul_laurent_large η _ _).symm.trans (congrArg (η.app _) hx)

/-- Along an epimorphism of module-valued functors both of whose terms commute with flat base
change, every weight-`k` element of the target lifts to a weight-`k` element of the source.
Independent-universe form. -/
public lemma exists_weightSpace_lift_of_epi_large {A : Type u} [CommRing A]
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    {E L : ModuleValuedFunctor.{max u v w, v} A} (p : E ⟶ L) [Epi p]
    (hE : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A E)
    (hL : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A L)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (z : L.obj (Opposite.op (Opposite.op (CommAlgCat.of A B))))
    (hz : z ∈ LaurentLarge.weightSpace A B L 𝒜 k) :
    ∃ y, y ∈ LaurentLarge.weightSpace A B E 𝒜 k ∧ p.app _ y = z := by
  classical
  let X := Opposite.op (Opposite.op (CommAlgCat.of A B))
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (p.app X)).mp inferInstance z
  obtain ⟨c, hc, -⟩ :=
    LaurentLarge.existsUnique_finsupp_weightSpace_eq_large.{u, v, w} A B E hE 𝒜 y
  let t : ℤ →₀ L.obj X := Finsupp.mapRange (p.app X).hom (map_zero _) c
  have htsum : t.sum (fun _ x => x) = z := by
    dsimp only [t]
    rw [Finsupp.sum_mapRange_index (fun _ => rfl), ← hy, ← hc.2]
    simp only [Finsupp.sum, map_sum]
  have hsingle : ∀ j, (Finsupp.single k z : ℤ →₀ L.obj X) j ∈
      LaurentLarge.weightSpace A B L 𝒜 j := by
    intro j
    by_cases hj : j = k
    · simpa [hj] using hz
    · simpa [Finsupp.single_apply, Ne.symm hj] using weightSpace_zero_mem_large L 𝒜 j
  obtain ⟨_, _, huniq⟩ :=
    LaurentLarge.existsUnique_finsupp_weightSpace_eq_large.{u, v, w} A B L hL 𝒜 z
  have heq : t = Finsupp.single k z :=
    (huniq t ⟨fun j => weightSpace_map_large p 𝒜 j (c j) (hc.1 j), htsum⟩).trans
      (huniq _ ⟨hsingle, by simp⟩).symm
  refine ⟨c k, hc.1 k, ?_⟩
  simpa only [t, Finsupp.mapRange_apply, Finsupp.single_eq_same] using DFunLike.congr_fun heq k

/-! ### The canonical base-change map on values -/

/-- The canonical map `C ⊗[B] F(B) → F(C)` of a module-valued functor along a map of
`A`-algebras, in the spelling of
`AdequateFunctor.LaurentLarge.PreservesFlatBaseChange`. -/
public noncomputable def baseChangeValueMap {A : Type u} [CommRing A]
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (F : ModuleValuedFunctor.{max u v w, v} A) (f : B →ₐ[A] C) :
    letI : Algebra B C := f.toRingHom.toAlgebra
    C ⊗[B] algebraValueLarge F B →ₗ[C] algebraValueLarge F C := by
  letI : Algebra B C := f.toRingHom.toAlgebra
  letI : Module B (algebraValueLarge F C) := Module.compHom _ (algebraMap B C)
  letI : IsScalarTower B C (algebraValueLarge F C) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact TensorProduct.AlgebraTensorModule.lift {
    toFun := fun c => {
      toFun := fun x => c • algebraMapValueLarge F f x
      map_add' := by
        intro x y
        change c • algebraMapValueLarge F f (x + y) =
          c • algebraMapValueLarge F f x + c • algebraMapValueLarge F f y
        rw [map_add, smul_add]
      map_smul' := by
        intro b x
        change c • algebraMapValueLarge F f (b • x) =
          b • (c • algebraMapValueLarge F f x)
        rw [map_smulₛₗ]
        change c • (f b • algebraMapValueLarge F f x) =
          f b • (c • algebraMapValueLarge F f x)
        exact smul_comm c (f b) _ }
    map_add' := by
      intro c d
      ext x
      change (c + d) • algebraMapValueLarge F f x =
        c • algebraMapValueLarge F f x + d • algebraMapValueLarge F f x
      exact add_smul c d _
    map_smul' := by
      intro c d
      ext x
      change (c * d) • algebraMapValueLarge F f x =
        c • (d • algebraMapValueLarge F f x)
      exact mul_smul c d _ }

/-- The canonical base-change map on a pure tensor. -/
public lemma baseChangeValueMap_tmul {A : Type u} [CommRing A]
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (F : ModuleValuedFunctor.{max u v w, v} A) (f : B →ₐ[A] C) :
    letI : Algebra B C := f.toRingHom.toAlgebra
    ∀ (c : C) (x : algebraValueLarge F B),
      baseChangeValueMap F f (c ⊗ₜ[B] x) = c • algebraMapValueLarge F f x :=
  fun _ _ => rfl

/-- The canonical base-change map is natural in the module-valued functor. -/
public lemma baseChangeValueMap_naturality {A : Type u} [CommRing A]
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {F G : ModuleValuedFunctor.{max u v w, v} A} (η : F ⟶ G) (f : B →ₐ[A] C) :
    letI : Algebra B C := f.toRingHom.toAlgebra
    ∀ t, baseChangeValueMap G f
        (LinearMap.lTensor C
          ((η.app (Opposite.op (Opposite.op (CommAlgCat.of A B)))).hom :
            algebraValueLarge F B →ₗ[B] algebraValueLarge G B) t) =
      (η.app (Opposite.op (Opposite.op (CommAlgCat.of A C)))).hom
        (baseChangeValueMap F f t) := by
  let : Algebra B C := f.toRingHom.toAlgebra
  intro t
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
  | tmul c x =>
    rw [LinearMap.lTensor_tmul, baseChangeValueMap_tmul, baseChangeValueMap_tmul,
      map_smul]
    exact congrArg (fun z => c • z) (algebraMapValueLarge_naturality η f x).symm

/-- The canonical base-change map of a module-valued functor commuting with flat base change
is bijective. Independent-universe form. -/
public lemma baseChangeValueMap_bijective {A : Type u} [CommRing A]
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (F : ModuleValuedFunctor.{max u v w, v} A)
    (hF : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A F)
    (f : B →ₐ[A] C)
    (hf : letI : Algebra B C := f.toRingHom.toAlgebra; Module.Flat B C) :
    Function.Bijective (baseChangeValueMap F f) := by
  let : Algebra B C := f.toRingHom.toAlgebra
  obtain ⟨e, he⟩ := hF B C f hf
  have hm : baseChangeValueMap F f = e.toLinearMap := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul c x =>
      calc baseChangeValueMap F f (c ⊗ₜ[B] x)
          = c • algebraMapValueLarge F f x := baseChangeValueMap_tmul F f c x
        _ = c • e ((1 : C) ⊗ₜ[B] x) := congrArg (fun z => c • z) (he x).symm
        _ = e (c • ((1 : C) ⊗ₜ[B] x)) := (map_smul e c _).symm
        _ = e (c ⊗ₜ[B] x) := by simp [TensorProduct.smul_tmul']
  exact hm ▸ e.bijective

/-! ### Flat base change in an extension -/

/-- The four lemma for additive maps: in a ladder with two exact rows whose outer vertical
maps are bijective, the middle vertical map is bijective.

Stated over variable abelian groups and variable additive maps, so that applying it never
asks for definitional unification at the concrete nested arguments of a module-valued
functor. -/
public lemma bijective_of_exact_ladder
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    (α : M₁ →+ M₂) (β : M₂ →+ M₃) (a : N₁ →+ N₂) (b : N₂ →+ N₃)
    (m₁ : M₁ →+ N₁) (m₂ : M₂ →+ N₂) (m₃ : M₃ →+ N₃)
    (hc₁ : ∀ x, m₂ (α x) = a (m₁ x)) (hc₂ : ∀ x, m₃ (β x) = b (m₂ x))
    (hβ : Function.Surjective β) (htop : ∀ x, β x = 0 → ∃ y, α y = x)
    (ha : Function.Injective a) (hbot : ∀ x, b x = 0 → ∃ y, a y = x)
    (h₁ : Function.Bijective m₁) (h₃ : Function.Bijective m₃) :
    Function.Bijective m₂ := by
  refine ⟨(injective_iff_map_eq_zero m₂).mpr fun d hd => ?_, fun z => ?_⟩
  · obtain ⟨y, rfl⟩ := htop d (h₃.injective (by rw [hc₂, hd, map_zero, map_zero]))
    obtain rfl : y = 0 := h₁.injective (ha (by rw [← hc₁, hd, map_zero, map_zero]))
    exact map_zero α
  · obtain ⟨t, ht⟩ := h₃.surjective (b z)
    obtain ⟨x, rfl⟩ := hβ t
    obtain ⟨y', hy'⟩ := hbot (z - m₂ x) (by rw [map_sub, ← hc₂, ht, sub_self])
    obtain ⟨y, rfl⟩ := h₁.surjective y'
    refine ⟨x + α y, ?_⟩
    rw [map_add, hc₁, hy']
    abel

/-- Commuting with flat base change passes to the middle term of a short exact sequence of
module-valued functors. Independent-universe form. -/
public lemma preservesFlatBaseChange_of_shortExact_large {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleValuedFunctor.{max u v w, v} A)) (hS : S.ShortExact)
    (h₁ : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A S.X₁)
    (h₃ : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A S.X₃) :
    LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A S.X₂ := by
  intro B C _ _ _ _ f
  let : Algebra B C := f.toRingHom.toAlgebra
  intro hf
  have := hS.mono_f
  have := hS.epi_g
  let XB : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (CommAlgCat.of A B))
  let XC : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (CommAlgCat.of A C))
  -- the evaluated maps of the short complex, over `B` and over `C`
  let fB : algebraValueLarge S.X₁ B →ₗ[B] algebraValueLarge S.X₂ B := (S.f.app XB).hom
  let gB : algebraValueLarge S.X₂ B →ₗ[B] algebraValueLarge S.X₃ B := (S.g.app XB).hom
  let fC : algebraValueLarge S.X₁ C →ₗ[C] algebraValueLarge S.X₂ C := (S.f.app XC).hom
  let gC : algebraValueLarge S.X₂ C →ₗ[C] algebraValueLarge S.X₃ C := (S.g.app XC).hom
  -- the bottom row is exact
  have hbot : ∀ x, gC x = 0 → ∃ y, fC y = x :=
    exact_component_preimage_large.{w, v, u} A S hS.exact XC
  have haC : Function.Injective fC :=
    (ModuleCat.mono_iff_injective (S.f.app XC)).mp inferInstance
  -- the top row is exact, because `C` is flat over `B`
  have hexB : Function.Exact fB gB := fun x =>
    ⟨exact_component_preimage_large.{w, v, u} A S hS.exact XB x, by
      rintro ⟨y, rfl⟩
      exact congrArg (fun τ => (τ.app XB).hom y) S.zero⟩
  have htop := Module.Flat.lTensor_exact (R := B) C hexB
  have hβ : Function.Surjective (LinearMap.lTensor C gB) :=
    LinearMap.lTensor_surjective C
      ((ModuleCat.epi_iff_surjective (S.g.app XB)).mp inferInstance)
  -- the ladder
  have hm₂ : Function.Bijective (baseChangeValueMap S.X₂ f) :=
    bijective_of_exact_ladder
      (LinearMap.lTensor C fB).toAddMonoidHom (LinearMap.lTensor C gB).toAddMonoidHom
      fC.toAddMonoidHom gC.toAddMonoidHom
      (baseChangeValueMap S.X₁ f).toAddMonoidHom
      (baseChangeValueMap S.X₂ f).toAddMonoidHom
      (baseChangeValueMap S.X₃ f).toAddMonoidHom
      (baseChangeValueMap_naturality S.f f) (baseChangeValueMap_naturality S.g f)
      hβ (fun x hx => (htop x).mp hx) haC hbot
      (baseChangeValueMap_bijective S.X₁ h₁ f hf)
      (baseChangeValueMap_bijective S.X₃ h₃ f hf)
  exact ⟨LinearEquiv.ofBijective _ hm₂, fun x =>
    (baseChangeValueMap_tmul S.X₂ f 1 x).trans (one_smul C _)⟩

end AdequateFunctor

end
