module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift

/-!
# Values of a module-valued functor on a full subcategory of algebras

The splitting argument of [Stacks, Tag 06V7] is carried out entirely in terms of the values of
the module-valued functors involved at a handful of auxiliary algebras and the transition maps
along the algebra maps between them. This file sets up that vocabulary for a functor defined
only on a *full subcategory* `Q` of the commutative `A`-algebras, which is the domain shape of
`AdequateFunctor.siteAlgebraInclusion`: an object is an algebra together with a proof that it
belongs to `Q`, and a morphism is an algebra map, so nothing is ever transported along an
isomorphism of algebras.

Two points make the vocabulary usable. The underlying ring of the object carried by an algebra
`B` is `B` on the nose (`AdequateFunctor.LaurentDomain.algObj`), so the value is a `B`-module
without any transport; and membership in `Q` is a proposition, so the object carried by `B`
does not depend on *which* proof of membership is supplied — the two spellings are
definitionally equal, which is `AdequateFunctor.LaurentDomain.algObj_congr`.

## Main definitions

* `AdequateFunctor.LaurentDomain.algObj` — the object of `Q.FullSubcategory`, doubly opposed,
  carried by an algebra of `Q`.
* `AdequateFunctor.LaurentDomain.algMor` — the morphism carried by an algebra map between two
  algebras of `Q`.
* `AdequateFunctor.LaurentDomain.weightSpace` — [Stacks, Tag 06UY] on such a domain: the
  weight-`k` part of the value at a graded algebra of `Q`.
* `AdequateFunctor.LaurentDomain.PreservesFlatBaseChange` — commuting with flat base change
  along the algebra maps *internal to the domain*. This is weaker than the property over all
  algebras, and it is all the weight-space argument ever uses.

## References

* [Stacks Project, Tag 06UY](https://stacks.math.columbia.edu/tag/06UY)
* [Stacks Project, Tag 06UZ](https://stacks.math.columbia.edu/tag/06UZ)
* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe uM u v

namespace AdequateFunctor.LaurentDomain

variable {A : Type u} [CommRing A]

/-! ### The objects and morphisms carried by algebras of the domain -/

/-- The object of `Q.FullSubcategory`, placed in the double opposite where module-valued
functors live, carried by an algebra belonging to `Q`. -/
public abbrev algObj (Q : ObjectProperty (CommAlgCat.{max u v} A))
    (B : Type (max u v)) [CommRing B] [Algebra A B] (hB : Q (CommAlgCat.of A B)) :
    ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ :=
  Opposite.op (Opposite.op ⟨CommAlgCat.of A B, hB⟩)

/-- Membership in `Q` is a proposition, so the object carried by an algebra does not depend on
which proof of membership is supplied. -/
public lemma algObj_congr (Q : ObjectProperty (CommAlgCat.{max u v} A))
    (B : Type (max u v)) [CommRing B] [Algebra A B] (h₁ h₂ : Q (CommAlgCat.of A B)) :
    algObj Q B h₁ = algObj Q B h₂ := rfl

/-- The morphism of `Q.FullSubcategory`, doubly opposed, carried by an algebra map between two
algebras belonging to `Q`. The subcategory is full, so this is the algebra map itself. -/
public abbrev algMor (Q : ObjectProperty (CommAlgCat.{max u v} A))
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C)) :
    algObj Q B hB ⟶ algObj Q C hC :=
  (ObjectProperty.homMk (X := (⟨CommAlgCat.of A B, hB⟩ : Q.FullSubcategory))
    (Y := (⟨CommAlgCat.of A C, hC⟩ : Q.FullSubcategory)) (CommAlgCat.ofHom f)).op.op

/-- The morphisms carried by algebra maps compose. -/
public lemma algMor_comp (Q : ObjectProperty (CommAlgCat.{max u v} A))
    {B C D : Type (max u v)} [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] (f : B →ₐ[A] C) (g : C →ₐ[A] D)
    (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C))
    (hD : Q (CommAlgCat.of A D)) :
    algMor Q f hB hC ≫ algMor Q g hC hD = algMor Q (g.comp f) hB hD := rfl

/-- The morphism carried by the identity algebra map is the identity. -/
public lemma algMor_id (Q : ObjectProperty (CommAlgCat.{max u v} A))
    {B : Type (max u v)} [CommRing B] [Algebra A B] (hB : Q (CommAlgCat.of A B)) :
    algMor Q (AlgHom.id A B) hB hB = 𝟙 _ := rfl

/-- Transition maps carried by equal algebra maps agree. -/
public lemma map_algMor_congr {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {f g : B →ₐ[A] C} (h : f = g)
    (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C))
    (x : F.obj (algObj Q B hB)) :
    F.map (algMor Q f hB hC) x = F.map (algMor Q g hB hC) x := by
  subst h; rfl

/-- The transition maps of a module-valued functor on the domain compose. -/
public lemma map_algMor_comp {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    {B C D : Type (max u v)} [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] (f : B →ₐ[A] C) (g : C →ₐ[A] D)
    (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C))
    (hD : Q (CommAlgCat.of A D)) (x : F.obj (algObj Q B hB)) :
    F.map (algMor Q g hC hD) (F.map (algMor Q f hB hC) x) =
      F.map (algMor Q (g.comp f) hB hD) x :=
  (F.map_comp_apply (algMor Q f hB hC) (algMor Q g hC hD) x).symm

/-- The transition map along the identity algebra map is the identity. -/
public lemma map_algMor_id {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    {B : Type (max u v)} [CommRing B] [Algebra A B] (hB : Q (CommAlgCat.of A B))
    (x : F.obj (algObj Q B hB)) :
    F.map (algMor Q (AlgHom.id A B) hB hB) x = x :=
  F.presheaf.map_id_apply _ x

/-- A morphism of module-valued functors on the domain commutes with the transition maps. -/
public lemma app_map_algMor {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    {F G : ModuleValuedFunctorOn.{uM} Q.ι} (η : F ⟶ G)
    {B C : Type (max u v)} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C))
    (x : F.obj (algObj Q B hB)) :
    (η.app (algObj Q C hC)).hom (F.map (algMor Q f hB hC) x) =
      G.map (algMor Q f hB hC) ((η.app (algObj Q B hB)).hom x) :=
  PresheafOfModules.naturality_apply η (algMor Q f hB hC) x

/-! ### Weight spaces -/

/-- The weight-`k` part of `F(B)` for `B` a graded algebra of the domain: those elements whose
images under the constant and grading maps into `B[T, T⁻¹]` differ by multiplication by `T k`.
This is [Stacks, Tag 06UY] on a full subcategory of algebras containing `B` and `B[T, T⁻¹]`. -/
public def weightSpace (Q : ObjectProperty (CommAlgCat.{max u v} A))
    (B : Type (max u v)) [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) :
    Set (F.obj (algObj Q B hB)) :=
  {ξ | (LaurentPolynomial.T k : LaurentPolynomial B) •
      F.map (algMor Q (constantLaurentMapLarge A B) hB hL) ξ =
    F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) ξ}

/-- Membership in a weight space, unfolded. -/
public lemma mem_weightSpace_iff {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    {hB : Q (CommAlgCat.of A B)} {hL : Q (CommAlgCat.of A (LaurentPolynomial B))}
    {F : ModuleValuedFunctorOn.{uM} Q.ι}
    {𝒜 : ℕ → Submodule A B} [GradedAlgebra 𝒜] {k : ℤ} {ξ : F.obj (algObj Q B hB)} :
    ξ ∈ weightSpace Q B hB hL F 𝒜 k ↔
      (LaurentPolynomial.T k : LaurentPolynomial B) •
        F.map (algMor Q (constantLaurentMapLarge A B) hB hL) ξ =
      F.map (algMor Q (gradedLaurentMapLarge A B 𝒜) hB hL) ξ :=
  Iff.rfl

/-- Zero has every weight. -/
public lemma weightSpace_zero_mem {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ) :
    (0 : F.obj (algObj Q B hB)) ∈ weightSpace Q B hB hL F 𝒜 k := by
  rw [mem_weightSpace_iff, (F.map _).hom.map_zero, (F.map _).hom.map_zero]
  exact smul_zero _

/-- The weight spaces are closed under negation. -/
public lemma weightSpace_neg_mem {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    {x : F.obj (algObj Q B hB)} (hx : x ∈ weightSpace Q B hB hL F 𝒜 k) :
    -x ∈ weightSpace Q B hB hL F 𝒜 k := by
  rw [mem_weightSpace_iff] at hx ⊢
  rw [(F.map _).hom.map_neg, (F.map _).hom.map_neg, smul_neg]
  exact congrArg Neg.neg hx

/-- The weight spaces are closed under addition. -/
public lemma weightSpace_add_mem {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    {x y : F.obj (algObj Q B hB)} (hx : x ∈ weightSpace Q B hB hL F 𝒜 k)
    (hy : y ∈ weightSpace Q B hB hL F 𝒜 k) :
    x + y ∈ weightSpace Q B hB hL F 𝒜 k := by
  rw [mem_weightSpace_iff] at hx hy ⊢
  rw [(F.map _).hom.map_add, (F.map _).hom.map_add, smul_add]
  exact congrArg₂ (· + ·) hx hy

/-- The weight spaces are closed under subtraction. -/
public lemma weightSpace_sub_mem {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    (F : ModuleValuedFunctorOn.{uM} Q.ι)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    {x y : F.obj (algObj Q B hB)} (hx : x ∈ weightSpace Q B hB hL F 𝒜 k)
    (hy : y ∈ weightSpace Q B hB hL F 𝒜 k) :
    x - y ∈ weightSpace Q B hB hL F 𝒜 k := by
  rw [mem_weightSpace_iff] at hx hy ⊢
  rw [(F.map _).hom.map_sub, (F.map _).hom.map_sub, smul_sub]
  exact congrArg₂ (· - ·) hx hy

/-- A morphism of module-valued functors on the domain commutes with scalar multiplication by
Laurent polynomials after a transition map into `B[T, T⁻¹]`. -/
private lemma app_smul_map_algMor_laurent {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    {F G : ModuleValuedFunctorOn.{uM} Q.ι} (η : F ⟶ G)
    (f : B →ₐ[A] LaurentPolynomial B) (c : LaurentPolynomial B) (x : F.obj (algObj Q B hB)) :
    (η.app (algObj Q (LaurentPolynomial B) hL)).hom (c • F.map (algMor Q f hB hL) x) =
      c • G.map (algMor Q f hB hL) ((η.app (algObj Q B hB)).hom x) := by
  rw [← app_map_algMor]
  exact map_smul (η.app (algObj Q (LaurentPolynomial B) hL)).hom _ _

/-- A morphism of module-valued functors on the domain preserves the weight spaces. -/
public lemma weightSpace_map {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    {F G : ModuleValuedFunctorOn.{uM} Q.ι} (η : F ⟶ G)
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (x : F.obj (algObj Q B hB)) (hx : x ∈ weightSpace Q B hB hL F 𝒜 k) :
    (η.app (algObj Q B hB)).hom x ∈ weightSpace Q B hB hL G 𝒜 k := by
  rw [mem_weightSpace_iff] at hx ⊢
  rw [← app_smul_map_algMor_laurent hB hL η _ _, ← app_map_algMor η _ hB hL, hx]

/-- A monomorphism of module-valued functors on the domain detects the weight spaces. -/
public lemma weightSpace_map_iff_of_mono {Q : ObjectProperty (CommAlgCat.{max u v} A)}
    {B : Type (max u v)} [CommRing B] [Algebra A B]
    (hB : Q (CommAlgCat.of A B)) (hL : Q (CommAlgCat.of A (LaurentPolynomial B)))
    {F G : ModuleValuedFunctorOn.{uM} Q.ι} (η : F ⟶ G) [Mono η]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (k : ℤ)
    (x : F.obj (algObj Q B hB)) :
    (η.app (algObj Q B hB)).hom x ∈ weightSpace Q B hB hL G 𝒜 k ↔
      x ∈ weightSpace Q B hB hL F 𝒜 k := by
  rw [mem_weightSpace_iff, mem_weightSpace_iff, ← app_smul_map_algMor_laurent hB hL η _ _,
    ← app_map_algMor η _ hB hL]
  exact (PresheafOfModules.injective_of_mono η _).eq_iff

/-! ### Flat base change inside the domain -/

/-- A module-valued functor on the domain preserves flat base change if, for every flat algebra
map *between algebras of the domain*, its canonical map from extension of scalars is an
isomorphism. The displayed condition on pure tensors identifies the isomorphism with the
canonical one.

This quantifies only over the domain, unlike
`AdequateFunctor.LaurentLarge.PreservesFlatBaseChange`; the weight-space argument of
[Stacks, Tag 06UZ] uses it only at the two maps `B → B[T, T⁻¹]` and
`B[T, T⁻¹] → B[T, T⁻¹][S, S⁻¹]`, both internal to a domain closed under Laurent extension. -/
public def PreservesFlatBaseChange (Q : ObjectProperty (CommAlgCat.{max u v} A))
    (F : ModuleValuedFunctorOn.{uM} Q.ι) : Prop :=
  ∀ (B C : Type (max u v)) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C)) (f : B →ₐ[A] C),
    letI : Algebra B C := f.toRingHom.toAlgebra
    Module.Flat B C →
      ∃ e : (C ⊗[B] F.obj (algObj Q B hB)) ≃ₗ[C] F.obj (algObj Q C hC),
        ∀ x, e (1 ⊗ₜ[B] x) = F.map (algMor Q f hB hC) x

/-- The canonical base-change map on a general tensor, once it is known on `1 ⊗ x`. -/
public lemma flatBaseChange_tmul (Q : ObjectProperty (CommAlgCat.{max u v} A))
    (B C : Type (max u v)) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra B C] (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C))
    (F : ModuleValuedFunctorOn.{uM} Q.ι) (f : B →ₐ[A] C) :
    ∀ (e : (C ⊗[B] F.obj (algObj Q B hB)) ≃ₗ[C] F.obj (algObj Q C hC)),
      (∀ x, e (1 ⊗ₜ[B] x) = F.map (algMor Q f hB hC) x) →
      ∀ c x, e (c ⊗ₜ[B] x) = c • F.map (algMor Q f hB hC) x := by
  intro e he c x
  have h : c ⊗ₜ[B] x = c • ((1 : C) ⊗ₜ[B] x) := by
    simp [TensorProduct.smul_tmul']
  rw [h, map_smul, he]
  rfl

end AdequateFunctor.LaurentDomain

end
