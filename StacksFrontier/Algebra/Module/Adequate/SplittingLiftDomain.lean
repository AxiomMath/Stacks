module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.Algebra.Module.Adequate.LaurentDomain
public import StacksFrontier.Algebra.Module.Adequate.SplittingLiftLarge

/-!
# Flat base change and weight-space lifting on a restricted domain of algebras

This file supplies two of the inputs of the splitting argument of [Stacks, Tag 06V7] for a
module-valued functor defined only on the full subcategory of commutative `A`-algebras
satisfying a property `Q`:

* an adequate functor on such a domain commutes with flat base change *inside* the domain
  ([Stacks, Tag 06UW]), and that property passes to the middle term of a short exact sequence;
* a weight-homogeneous element of the quotient term of an extension lifts to a
  weight-homogeneous element of its middle term.

`StacksFrontier.Algebra.Module.Adequate.SplittingLiftLarge` proves the same statements for a
functor on all commutative `A`-algebras.

## Main definitions

* `AdequateFunctor.LaurentDomain.algebraMapValue` — the transition map of a module-valued
  functor on the domain along an algebra map, with its semilinearity exposed.
* `AdequateFunctor.LaurentDomain.baseChangeValueMap` — the canonical map
  `C ⊗[B] F(B) → F(C)`, in the spelling
  `AdequateFunctor.LaurentDomain.PreservesFlatBaseChange` uses.

## Main results

* `AdequateFunctor.LaurentDomain.adequate_preservesFlatBaseChange` — [Stacks, Tag 06UW] on the
  domain, a rephrasing of `AdequateFunctor.moduleValuedFunctorBaseChangeMap_bijective` (stated for
  an arbitrary domain functor) in the `PreservesFlatBaseChange` spelling.
* `AdequateFunctor.LaurentDomain.preservesFlatBaseChange_of_shortExact` — commuting with flat
  base change inside the domain passes to the middle term of a short exact sequence.
* `AdequateFunctor.LaurentDomain.exists_weightSpace_lift_of_epi` — along an epimorphism both of
  whose terms commute with flat base change inside the domain, every weight-`k` element of the
  target lifts to a weight-`k` element of the source.

## Implementation notes

The flat-base-change transfer is the four lemma. As in the full-domain independent-universe
proof, it cannot be run categorically: `ModuleCat` is monoidal only when the module universe
agrees with the ring universe, so `MonoidalCategory.tensorLeft` does not typecheck on the
values here. The diagram chase is therefore run once, over variable abelian groups and variable
additive maps, as `bijective_of_exact_ladder`, and applied to the ladder whose rows are
`C ⊗[B] -` of the sections over `B` and the sections over `C`. Nothing in that lemma mentions a
module-valued functor, so no definitional unification is demanded at the concrete nested
arguments.

The exactness of the top row is `Module.Flat.lTensor_exact`, already polymorphic in the
universes of both tensor factors; the bottom row is
`AdequateFunctor.exact_component_preimage_on`, which is the restricted-domain exactness tool.

The weight-space decomposition used for the lifting is [Stacks, Tag 06UZ] on the domain,
`AdequateFunctor.LaurentDomain.existsUnique_finsupp_weightSpace_eq`, which is why the lifting
statement carries the two iterated Laurent memberships.

## References

* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
* [Stacks Project, Tag 06UZ](https://stacks.math.columbia.edu/tag/06UZ)
* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AdequateFunctor.LaurentDomain

universe w v u

variable {A : Type u} [CommRing A] {Q : ObjectProperty (CommAlgCat.{max u v} A)}

/-! ### The transition maps, with their semilinearity exposed -/

/-- The transition map of a module-valued functor on the domain along an algebra map between
two algebras of the domain, as a map semilinear over that algebra map. -/
public noncomputable abbrev algebraMapValue (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C)) :
    F.obj (algObj Q B hB) →ₛₗ[f.toRingHom] F.obj (algObj Q C hC) :=
  F.restrictₛₗ (algMor Q f hB hC)

/-- The semilinear transition map is the functor's action on morphisms. -/
public lemma algebraMapValue_apply (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C))
    (x : F.obj (algObj Q B hB)) :
    algebraMapValue F f hB hC x = F.map (algMor Q f hB hC) x := rfl

/-! ### Tag 06UW on the domain -/

/-- **Stacks Lemma 06UW on a restricted domain of algebras**, read off for a single algebra
map: an adequate module-valued functor on a domain of algebras commutes with flat base change
along every algebra map internal to that domain, the map being a plain algebra map with
`Algebra B C` taken from it rather than a morphism of the domain. -/
public lemma adequate_preservesFlatBaseChange (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    (hF : IsAdequate.{max u v w, v} Q.ι F) : PreservesFlatBaseChange Q F := by
  intro B C _ _ _ _ hB hC f
  let : Algebra B C := f.toRingHom.toAlgebra
  intro hflat
  let g : (⟨CommAlgCat.of A B, hB⟩ : Q.FullSubcategory) ⟶
      (⟨CommAlgCat.of A C, hC⟩ : Q.FullSubcategory) :=
    ObjectProperty.homMk (CommAlgCat.ofHom f)
  have hg : RingHom.Flat (Q.ι.map g).hom.toRingHom := by
    rwa [RingHom.Flat, RingHom.toAlgebra]
  have hb := moduleValuedFunctorBaseChangeMap_bijective Q.ι F hF g hg
  refine ⟨LinearEquiv.ofBijective (moduleValuedFunctorBaseChangeMap Q.ι F g) hb, ?_⟩
  intro x
  have h := moduleValuedFunctorBaseChangeMap_tmul.{max u v w, v, u, max u v, max (u + 1) (v + 1)}
    Q.ι F g 1 x
  rwa [one_smul] at h

/-! ### The canonical base-change map on values -/

/-- The canonical map `C ⊗[B] F(B) → F(C)` of a module-valued functor on the domain along an
algebra map of the domain, in the spelling
`AdequateFunctor.LaurentDomain.PreservesFlatBaseChange` uses. -/
public noncomputable def baseChangeValueMap (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C)) :
    letI : Algebra B C := f.toRingHom.toAlgebra
    C ⊗[B] F.obj (algObj Q B hB) →ₗ[C] F.obj (algObj Q C hC) := by
  letI : Algebra B C := f.toRingHom.toAlgebra
  letI : Module B (F.obj (algObj Q C hC)) := Module.compHom _ (algebraMap B C)
  letI : IsScalarTower B C (F.obj (algObj Q C hC)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact TensorProduct.AlgebraTensorModule.lift {
    toFun := fun c => {
      toFun := fun x => c • algebraMapValue F f hB hC x
      map_add' := by
        intro x y
        change c • algebraMapValue F f hB hC (x + y) =
          c • algebraMapValue F f hB hC x + c • algebraMapValue F f hB hC y
        rw [map_add, smul_add]
      map_smul' := by
        intro b x
        change c • algebraMapValue F f hB hC (b • x) =
          b • (c • algebraMapValue F f hB hC x)
        rw [map_smulₛₗ]
        change c • (f b • algebraMapValue F f hB hC x) =
          f b • (c • algebraMapValue F f hB hC x)
        exact smul_comm c (f b) _ }
    map_add' := by
      intro c d
      ext x
      change (c + d) • algebraMapValue F f hB hC x =
        c • algebraMapValue F f hB hC x + d • algebraMapValue F f hB hC x
      exact add_smul c d _
    map_smul' := by
      intro c d
      ext x
      change (c * d) • algebraMapValue F f hB hC x =
        c • (d • algebraMapValue F f hB hC x)
      exact mul_smul c d _ }

/-- The canonical base-change map on a pure tensor. -/
public lemma baseChangeValueMap_tmul (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C)) :
    letI : Algebra B C := f.toRingHom.toAlgebra
    ∀ (c : C) (x : F.obj (algObj Q B hB)),
      baseChangeValueMap F f hB hC (c ⊗ₜ[B] x) = c • algebraMapValue F f hB hC x :=
  fun _ _ => rfl

/-- The canonical base-change map is natural in the module-valued functor. -/
public lemma baseChangeValueMap_naturality {F G : ModuleValuedFunctorOn.{max u v w} Q.ι}
    (η : F ⟶ G) {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C)) :
    letI : Algebra B C := f.toRingHom.toAlgebra
    ∀ t, baseChangeValueMap G f hB hC
        (LinearMap.lTensor C ((η.app (algObj Q B hB)).hom :
          F.obj (algObj Q B hB) →ₗ[B] G.obj (algObj Q B hB)) t) =
      (η.app (algObj Q C hC)).hom (baseChangeValueMap F f hB hC t) := by
  let : Algebra B C := f.toRingHom.toAlgebra
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
  | tmul c x =>
    rw [LinearMap.lTensor_tmul, baseChangeValueMap_tmul, baseChangeValueMap_tmul, map_smul]
    exact congrArg (fun z => c • z) (app_map_algMor η f hB hC x).symm

/-- The canonical base-change map of a module-valued functor commuting with flat base change
inside the domain is bijective. -/
public lemma baseChangeValueMap_bijective (F : ModuleValuedFunctorOn.{max u v w} Q.ι)
    (hF : PreservesFlatBaseChange Q F)
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C))
    (hf : letI : Algebra B C := f.toRingHom.toAlgebra; Module.Flat B C) :
    Function.Bijective (baseChangeValueMap F f hB hC) := by
  let : Algebra B C := f.toRingHom.toAlgebra
  obtain ⟨e, he⟩ := hF B C hB hC f hf
  have hm : baseChangeValueMap F f hB hC = e.toLinearMap := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul c x =>
      exact (baseChangeValueMap_tmul F f hB hC c x).trans
        (flatBaseChange_tmul Q B C hB hC F f e he c x).symm
  exact hm ▸ e.bijective

/-! ### Flat base change in an extension -/

/-- The four lemma for additive maps: in a ladder with two exact rows whose outer vertical maps
are bijective, the middle vertical map is bijective. -/
private alias bijective_of_exact_ladder := AdequateFunctor.bijective_of_exact_ladder

/-- Commuting with flat base change inside the domain passes to the middle term of a short
exact sequence of module-valued functors on the domain. -/
public lemma preservesFlatBaseChange_of_shortExact
    (S : ShortComplex (ModuleValuedFunctorOn.{max u v w} Q.ι)) (hS : S.ShortExact)
    (h₁ : PreservesFlatBaseChange Q S.X₁) (h₃ : PreservesFlatBaseChange Q S.X₃) :
    PreservesFlatBaseChange Q S.X₂ := by
  intro B C _ _ _ _ hB hC f
  let : Algebra B C := f.toRingHom.toAlgebra
  intro hf
  have := hS.mono_f
  have := hS.epi_g
  let XB := algObj Q B hB
  let XC := algObj Q C hC
  let fB : S.X₁.obj XB →ₗ[B] S.X₂.obj XB := (S.f.app XB).hom
  let gB : S.X₂.obj XB →ₗ[B] S.X₃.obj XB := (S.g.app XB).hom
  let fC : S.X₁.obj XC →ₗ[C] S.X₂.obj XC := (S.f.app XC).hom
  let gC : S.X₂.obj XC →ₗ[C] S.X₃.obj XC := (S.g.app XC).hom
  have hex : ∀ X, Function.Exact (S.f.app X).hom (S.g.app X).hom := fun X x =>
    ⟨exact_component_preimage_on.{w} Q.ι S hS.exact X x, by
      rintro ⟨y, rfl⟩
      exact congrArg (fun τ => (τ.app X).hom y) S.zero⟩
  have haC : Function.Injective fC :=
    (ModuleCat.mono_iff_injective (S.f.app XC)).mp inferInstance
  have htop := Module.Flat.lTensor_exact (R := B) C (hex XB)
  have hβ : Function.Surjective (LinearMap.lTensor C gB) :=
    LinearMap.lTensor_surjective C
      ((ModuleCat.epi_iff_surjective (S.g.app XB)).mp inferInstance)
  have hm₂ : Function.Bijective (baseChangeValueMap S.X₂ f hB hC) :=
    bijective_of_exact_ladder
      (LinearMap.lTensor C fB).toAddMonoidHom (LinearMap.lTensor C gB).toAddMonoidHom
      fC.toAddMonoidHom gC.toAddMonoidHom
      (baseChangeValueMap S.X₁ f hB hC).toAddMonoidHom
      (baseChangeValueMap S.X₂ f hB hC).toAddMonoidHom
      (baseChangeValueMap S.X₃ f hB hC).toAddMonoidHom
      (baseChangeValueMap_naturality S.f f hB hC)
      (baseChangeValueMap_naturality S.g f hB hC)
      hβ (fun x => (htop x).mp) haC (fun x => (hex XC x).mp)
      (baseChangeValueMap_bijective S.X₁ h₁ f hB hC hf)
      (baseChangeValueMap_bijective S.X₃ h₃ f hB hC hf)
  exact ⟨LinearEquiv.ofBijective _ hm₂,
    fun x => (baseChangeValueMap_tmul S.X₂ f hB hC 1 x).trans (one_smul C _)⟩

/-! ### Lifting a weight-homogeneous element along an epimorphism -/

/-- Along an epimorphism of module-valued functors on the domain both of whose terms commute
with flat base change inside the domain, every weight-`k` element of the target lifts to a
weight-`k` element of the source. -/
public lemma exists_weightSpace_lift_of_epi
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (hLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial B))))
    {E L : ModuleValuedFunctorOn.{max u v w} Q.ι} (p : E ⟶ L) [Epi p]
    (hE : PreservesFlatBaseChange Q E) (hLf : PreservesFlatBaseChange Q L)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (z : L.obj (algObj Q B hB)) (hz : z ∈ weightSpace Q B hB hL L 𝒜 k) :
    ∃ y, y ∈ weightSpace Q B hB hL E 𝒜 k ∧ (p.app (algObj Q B hB)).hom y = z := by
  classical
  let X := algObj Q B hB
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (p.app X)).mp inferInstance z
  obtain ⟨c, hc, -⟩ :=
    existsUnique_finsupp_weightSpace_eq Q B hB hL hLL E hE 𝒜 y
  let t : ℤ →₀ L.obj X := Finsupp.mapRange (p.app X).hom (map_zero _) c
  have ht : ∀ j, t j ∈ weightSpace Q B hB hL L 𝒜 j := fun j =>
    weightSpace_map hB hL p 𝒜 j (c j) (hc.1 j)
  have htsum : t.sum (fun _ x => x) = z := by
    dsimp only [t]
    rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
    calc
      c.sum (fun _ x => (p.app X).hom x) = (p.app X).hom (c.sum (fun _ x => x)) := by
        simp only [Finsupp.sum, map_sum]
      _ = z := hc.2 ▸ hy
  have hsingle : ∀ j, (Finsupp.single k z : ℤ →₀ L.obj X) j ∈
      weightSpace Q B hB hL L 𝒜 j := by
    intro j
    by_cases hj : j = k
    · simpa [hj] using hz
    · simpa [Finsupp.single_apply, Ne.symm hj] using weightSpace_zero_mem hB hL L 𝒜 j
  obtain ⟨_, _, huniq⟩ :=
    existsUnique_finsupp_weightSpace_eq Q B hB hL hLL L hLf 𝒜 z
  have heq : t = Finsupp.single k z :=
    (huniq t ⟨ht, htsum⟩).trans (huniq _ ⟨hsingle, by simp⟩).symm
  refine ⟨c k, hc.1 k, ?_⟩
  simpa only [t, Finsupp.mapRange_apply, Finsupp.single_eq_same] using
    congrArg (fun a : ℤ →₀ L.obj X => a k) heq

end AdequateFunctor.LaurentDomain

end
