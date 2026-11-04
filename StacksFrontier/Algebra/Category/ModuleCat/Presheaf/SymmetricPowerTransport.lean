module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.UniversalProperty
public import StacksFrontier.LinearAlgebra.SymmetricPower.BaseChange

/-!
# Transporting unital homomorphisms out of sectionwise symmetric algebras

A unital homomorphism of graded algebras of presheaves out of the sectionwise symmetric algebra
`Sym(P)` is determined, on the sections over an object, by its value on degree-one sections.  Two
such homomorphisms matched in degree one along a ring map and a semilinear map are matched in
every degree along `Symᵏ` of that map, and bijectivity transfers between them when the ring map and
the degree-one map are bijective.

## Main results

* `SymPow.symMapIntₛₗ_bijective`: base change of a symmetric power along a ring isomorphism and
  a bijective semilinear map is bijective.
* `Stacks.GradedAlgebra.bijective_unitalHom_app_of_transport`: a unital homomorphism out of
  `Sym(P₁)` is bijective in degree `k` over `X₁` when it corresponds, along such a transport, to
  one that is.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u v r

namespace SymPow

variable {R S : Type*} [CommRing R] [CommRing S] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module S N]

/-- Mapping the symmetric algebra along `(φ, u)` and then along a left inverse `(ψ, w)` is the
identity. -/
private theorem mapₛₗ_mapₛₗ_of_leftInverse (φ : R →+* S) (u : M →ₛₗ[φ] N) (ψ : S →+* R)
    (w : N →ₛₗ[ψ] M) (h₁ : ∀ r, ψ (φ r) = r) (h₃ : ∀ m, w (u m) = m)
    (x : SymmetricAlgebra R M) :
    SymmetricAlgebra.mapₛₗ ψ w (SymmetricAlgebra.mapₛₗ φ u x) = x :=
  (SymmetricAlgebra.mapₛₗ_eq_comp u w (LinearMap.id) (fun r => (h₁ r).symm)
    (fun m => (h₃ m).symm) x).symm.trans
    (SymmetricAlgebra.mapₛₗ_eq_self _ (fun _ => rfl) (fun _ => rfl) _)

/-- The base change of a symmetric power along a ring isomorphism and a bijective semilinear map is
bijective, with inverse the base change along the inverses. -/
theorem symMapIntₛₗ_bijective (n : ℤ) (φ : R →+* S) (u : M →ₛₗ[φ] N) (ψ : S →+* R)
    (w : N →ₛₗ[ψ] M) (h₁ : ∀ r, ψ (φ r) = r) (h₂ : ∀ s, φ (ψ s) = s) (h₃ : ∀ m, w (u m) = m)
    (h₄ : ∀ m, u (w m) = m) :
    Function.Bijective (symMapIntₛₗ n φ u) :=
  Function.bijective_iff_has_inverse.mpr ⟨symMapIntₛₗ n ψ w,
    fun x => Subtype.ext (mapₛₗ_mapₛₗ_of_leftInverse φ u ψ w h₁ h₃ x.1),
    fun y => Subtype.ext (mapₛₗ_mapₛₗ_of_leftInverse ψ w φ u h₂ h₄ y.1)⟩

end SymPow

namespace Stacks.GradedAlgebra

section Transport

universe u₁ v₁ u₂ v₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {O₁ : C₁ᵒᵖ ⥤ CommRingCat.{r}} {O₂ : C₂ᵒᵖ ⥤ CommRingCat.{r}}
  {P₁ : _root_.PresheafOfModules.{r} (O₁ ⋙ forget₂ CommRingCat RingCat)}
  {P₂ : _root_.PresheafOfModules.{r} (O₂ ⋙ forget₂ CommRingCat RingCat)}
  {Q₁ : ℤ → _root_.PresheafOfModules.{r} (O₁ ⋙ forget₂ CommRingCat RingCat)}
  {Q₂ : ℤ → _root_.PresheafOfModules.{r} (O₂ ⋙ forget₂ CommRingCat RingCat)}
  (A₁ : Stacks.GradedAlgebra Q₁) (A₂ : Stacks.GradedAlgebra Q₂)
  {X₁ : C₁ᵒᵖ} {X₂ : C₂ᵒᵖ}
  (φ : (O₁ ⋙ forget₂ CommRingCat RingCat).obj X₁ →+* (O₂ ⋙ forget₂ CommRingCat RingCat).obj X₂)
  (τ : ∀ n : ℤ, (Q₁ n).obj X₁ →ₛₗ[φ] (Q₂ n).obj X₂)
  (hmul : ∀ (i j : ℤ) (x : (Q₁ i).obj X₁) (y : (Q₁ j).obj X₁),
    τ (i + j) ((A₁.mul i j).app X₁ x y) = (A₂.mul i j).app X₂ (τ i x) (τ j y))
  (hone : τ 0 (A₁.one.eval X₁) = A₂.one.eval X₂)

include hmul hone in
/-- A multiplicative and unital family of maps between the sections of two graded algebras of
presheaves carries ordered products of degree-one sections to ordered products. -/
theorem homogeneousProd_transport (k : ℕ) (z : Fin k → (Q₁ 1).obj X₁) :
    τ k (A₁.homogeneousProd X₁ k z) = A₂.homogeneousProd X₂ k fun i => τ 1 (z i) := by
  induction k with
  | zero => exact hone
  | succ k ih =>
    exact (hmul (k : ℤ) 1 _ _).trans (congrArg (fun t => (A₂.mul (k : ℤ) 1).app X₂ t
      (τ 1 (z (Fin.last k)))) (ih fun i => z i.castSucc))

variable (g₁ : UnitalHom (_root_.PresheafOfModules.symPowIntGradedAlgebra P₁) A₁)
  (g₂ : UnitalHom (_root_.PresheafOfModules.symPowIntGradedAlgebra P₂) A₂)
  (u : P₁.obj X₁ →ₛₗ[φ] P₂.obj X₂)
  (hgen : ∀ s : P₁.obj X₁,
    τ 1 (_root_.PresheafOfModules.Hom.app (g₁.app 1) X₁
        (_root_.PresheafOfModules.Hom.app (_root_.PresheafOfModules.symPowIntGen P₁) X₁ s)) =
      _root_.PresheafOfModules.Hom.app (g₂.app 1) X₂
        (_root_.PresheafOfModules.Hom.app (_root_.PresheafOfModules.symPowIntGen P₂) X₂ (u s)))

include hmul hone hgen in
/-- **Unital homomorphisms out of two sectionwise symmetric algebras, matched in degree one, are
matched in every degree** along the base change `Symᵏ(u)` of the symmetric powers. -/
theorem unitalHom_app_symMapIntₛₗ (k : ℕ)
    (x : (_root_.PresheafOfModules.symPowInt (k : ℤ) P₁).obj X₁) :
    τ k (_root_.PresheafOfModules.Hom.app (g₁.app k) X₁ x) =
      _root_.PresheafOfModules.Hom.app (g₂.app k) X₂ (SymPow.symMapIntₛₗ (k : ℤ) φ u x) := by
  let L : SymPow.symmetricPower k ((O₁ ⋙ forget₂ CommRingCat RingCat).obj X₁) (P₁.obj X₁)
      →ₛₗ[φ] (Q₂ k).obj X₂ := (τ k).comp ((g₁.app k).app X₁).hom
  let R : SymPow.symmetricPower k ((O₁ ⋙ forget₂ CommRingCat RingCat).obj X₁) (P₁.obj X₁)
      →ₛₗ[φ] (Q₂ k).obj X₂ := ((g₂.app k).app X₂).hom.comp (SymPow.symMapIntₛₗ (k : ℤ) φ u)
  have hLR : L = R := by
    refine SymPow.ext_of_prod_ι fun s => ?_
    have h₁ := A₁.unitalHom_app_prod_ι
      (_root_.PresheafOfModules.symPowIntGen P₁ ≫ g₁.app 1) g₁ (fun _ _ => rfl) k X₁ s
      ⟨_, SymmetricAlgebra.prod_ι_mem _ s⟩ rfl
    have h₂ := A₂.unitalHom_app_prod_ι
      (_root_.PresheafOfModules.symPowIntGen P₂ ≫ g₂.app 1) g₂ (fun _ _ => rfl) k X₂
      (fun i => u (s i))
      (SymPow.symMapIntₛₗ (k : ℤ) φ u ⟨_, SymmetricAlgebra.prod_ι_mem _ s⟩)
      (by
        show SymmetricAlgebra.mapₛₗ φ u (∏ i : Fin k, SymmetricAlgebra.ι _ _ (s i)) = _
        rw [map_prod]
        simp only [SymmetricAlgebra.mapₛₗ_ι])
    refine (congrArg (τ k) h₁).trans (Eq.trans ?_ h₂.symm)
    refine (homogeneousProd_transport A₁ A₂ φ τ hmul hone k _).trans ?_
    exact congrArg (A₂.homogeneousProd X₂ k) (funext fun i => hgen (s i))
  exact congrArg (fun f => f x) hLR

include hmul hone hgen in
/-- **Bijectivity transfers between matched unital homomorphisms** out of two sectionwise symmetric
algebras: if the ring map and the degree-one map are bijective, the identification `τ` of the
targets is bijective in degree `k`, and the second homomorphism is bijective in degree `k`, so is
the first. -/
theorem bijective_unitalHom_app_of_transport (k : ℕ)
    (ψ : (O₂ ⋙ forget₂ CommRingCat RingCat).obj X₂ →+* (O₁ ⋙ forget₂ CommRingCat RingCat).obj X₁)
    (w : P₂.obj X₂ →ₛₗ[ψ] P₁.obj X₁) (h₁ : ∀ r, ψ (φ r) = r) (h₂ : ∀ s, φ (ψ s) = s)
    (h₃ : ∀ m, w (u m) = m) (h₄ : ∀ m, u (w m) = m) (hτ : Function.Bijective (τ k))
    (hg₂ : Function.Bijective (_root_.PresheafOfModules.Hom.app (g₂.app k) X₂)) :
    Function.Bijective (_root_.PresheafOfModules.Hom.app (g₁.app k) X₁) := by
  have hcomp : (τ k ∘ _root_.PresheafOfModules.Hom.app (g₁.app k) X₁) =
      (_root_.PresheafOfModules.Hom.app (g₂.app k) X₂ ∘ SymPow.symMapIntₛₗ (k : ℤ) φ u) :=
    funext (unitalHom_app_symMapIntₛₗ A₁ A₂ φ τ hmul hone g₁ g₂ u hgen k)
  have hσ := SymPow.symMapIntₛₗ_bijective (k : ℤ) φ u ψ w h₁ h₂ h₃ h₄
  refine (Function.Bijective.of_comp_iff' hτ _).mp ?_
  rw [hcomp]
  exact hg₂.comp hσ

end Transport

end Stacks.GradedAlgebra
