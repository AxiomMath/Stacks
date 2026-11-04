module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteDirectImageRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CohomologyVanishingTransport
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FilteredColimitClasses

/-!
# Restriction along a morphism with a section is injective

Let `p : Y ⟶ X` be a morphism of schemes with a section `s : X ⟶ Y`, `s ≫ p = 𝟙 X`. Then
restriction `H^q(X, G) ⟶ H^q(Y, p^{-1} G)` is injective for every abelian sheaf `G` on `X_étale`:
restricting further along `s` gives restriction along `s ≫ p = 𝟙 X`, which is bijective. This is
the last step of the injectivity half of Stacks 03SC (7): once a class on `X` dies on `X_{k'}` it
dies on some `X_A`, `A ⊆ k'` of finite type over `k` (Stacks 03Q6), and for `k` algebraically
closed `X_A ⟶ X` has a section coming from a `k`-point of `A`.

## Main results

* `Stacks.EtaleCohomology.injective_mapExactFunctor_of_comp_iso`: an exact functor `L` is injective
  on `Ext` if `L ⋙ M` is isomorphic to a functor which is.
* `Stacks.EtaleCohomology.injective_etaleCohomologyRestrictionMap_of_comp_eq_id`: the statement on
  étale cohomology.
* `Stacks.EtaleCohomology.injective_etaleCohomologyRestrictionMap_of_vanishing_at_fg`: injectivity
  of restriction to `X_{k'}`, `k` algebraically closed, from vanishing at a finitely generated
  stage `X_A`, which is what Stacks 03Q6 supplies.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

section Ext

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  {E : Type*} [Category E] [Abelian E]

/-- **Injectivity on `Ext` through a composite.** Let `L : C ⥤ D` and `M : D ⥤ E` be exact, and
`L ⋙ M ≅ N` with `N` injective on `Ext^n(X, Y)`. Then `L` is injective on `Ext^n(X, Y)`: the image
under `M` of the image under `L` of a class is its image under `L ⋙ M`, and the isomorphism
`L ⋙ M ≅ N` changes that image only by composition with invertible degree-zero classes. -/
theorem injective_mapExactFunctor_of_comp_iso [HasExt.{w} C] [HasExt.{w} D] [HasExt.{w} E]
    [EnoughInjectives C] (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] (M : D ⥤ E) [M.Additive] [PreservesFiniteLimits M]
    [PreservesFiniteColimits M] (N : C ⥤ E) [N.Additive] [PreservesFiniteLimits N]
    [PreservesFiniteColimits N] (e : L ⋙ M ≅ N) (X Y : C) (n : ℕ)
    (hN : Function.Injective (N.mapExtAddHom X Y n)) :
    Function.Injective (L.mapExtAddHom X Y n) := by
  intro a b hab
  apply hN
  simp only [Functor.mapExtAddHom_apply] at hab ⊢
  have key : ∀ c : Ext.{w} X Y n, c.mapExactFunctor N =
      ((Ext.mk₀ (e.inv.app X)).comp ((c.mapExactFunctor L).mapExactFunctor M) (zero_add n)).comp
        (Ext.mk₀ (e.hom.app Y)) (add_zero n) := fun c => by
    rw [Stacks.ExtFunctorial.mapExactFunctor_comp_functor L M X n c,
      Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor e.inv X n c, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, ← NatTrans.comp_app, e.inv_hom_id, NatTrans.id_app, Ext.comp_mk₀_id]
  rw [key a, key b, hab]

end Ext

/-- **Restriction along a morphism with a section is injective.** If `s ≫ p = 𝟙 X`, restriction
`H^q(X, G) ⟶ H^q(Y, p^{-1} G)` along `p : Y ⟶ X` is injective. -/
theorem injective_etaleCohomologyRestrictionMap_of_comp_eq_id {X Y : Scheme.{u}} (p : Y ⟶ X)
    (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} p G q) := by
  rw [etaleCohomologyRestrictionMap_injective_iff.{u, 0, u + 1}]
  have : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
    have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
    infer_instance
  refine injective_mapExactFunctor_of_comp_iso.{u + 1} (etaleAbelianInverseImage.{u, 0} p)
    (etaleAbelianInverseImage.{u, 0} s) (etaleAbelianInverseImage.{u, 0} (𝟙 X))
    ((etaleAbelianInverseImageCompIso.{u, 0} s p).symm ≪≫
      eqToIso (congrArg (fun g : X ⟶ X => etaleAbelianInverseImage.{u, 0} g) hs)) _ _ q ?_
  rw [← etaleCohomologyRestrictionMap_injective_iff.{u, 0, u + 1}]
  exact (bijective_etaleCohomologyRestrictionMap_of_isIso (𝟙 X) G q).1

/-- **A finitely generated subalgebra of an extension of an algebraically closed field has a
point.** A nonzero algebra of finite type over an algebraically closed field `k` has a maximal
ideal, whose residue field is finite over `k` (Nullstellensatz), hence `k` itself. -/
theorem nonempty_algHom_of_fg {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    (A : Subalgebra k K) (hA : A.FG) : Nonempty (A →ₐ[k] k) := by
  have : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType A).1 hA
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  let : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hbij : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ m)
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hbij).symm.toAlgHom.comp
    (Ideal.Quotient.mkₐ k m)⟩

/-- **Injectivity of restriction to an extension of an algebraically closed field, from vanishing
at a finitely generated stage.** Let `k` be algebraically closed, `k'/k` an extension and `X` a
`k`-scheme. If every class of `H^q(X, G)` that vanishes on `X_{k'}` already vanishes on
`X_A = X ×_k Spec A` for some finitely generated `k`-subalgebra `A ⊆ k'` (the content of Stacks
03Q6, `X_{k'}` being the limit of the `X_A`), then restriction to `X_{k'}` is injective: `X_A ⟶ X`
has a section, coming from a `k`-point of `A`. -/
theorem injective_etaleCohomologyRestrictionMap_of_vanishing_at_fg (k k' : Type u) [Field k]
    [IsAlgClosed k] [Field k'] [Algebra k k'] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : ∀ c : Sheaf.H.{u + 1} G q,
      etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π) G q c = 0 →
        ∃ A : Subalgebra k k', A.FG ∧ etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k A)))) G q c = 0) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π)
      G q) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
  obtain ⟨A, hA, hcA⟩ := h c hc
  obtain ⟨φ⟩ := nonempty_algHom_of_fg A hA
  let a := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let b : Spec (.of k) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hba : b ≫ a = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact φ.commutes x
  let s : X ⟶ pullback π a := pullback.lift (𝟙 X) (π ≫ b) (by
    rw [Category.id_comp, Category.assoc, hba, Category.comp_id])
  have hs : s ≫ pullback.fst π a = 𝟙 X := pullback.lift_fst _ _ _
  exact injective_etaleCohomologyRestrictionMap_of_comp_eq_id (pullback.fst π a) s hs G q
    (hcA.trans (map_zero _).symm)

end Stacks.EtaleCohomology

end
