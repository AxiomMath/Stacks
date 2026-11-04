module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SpecOver
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting along a thickening with nilpotent kernel

A formally smooth transformation `a : F ⟶ G` of presheaves on the big fppf site of `S`
(`AlgebraicGeometry.Space.FormallySmooth`) lifts across square-zero closed immersions of affine
objects. It then lifts across every closed immersion `T ⟶ T'` of affine objects whose kernel on
global sections is nilpotent: such a thickening is a composite of square-zero ones, through the
spectra of the quotients of the ring of global sections of `T'` by the powers of the kernel.

## Main results

* `AlgebraicGeometry.Space.FormallySmooth.exists_isLift_specOverHom_of_isNilpotent`: lifting
  along the spectrum of a surjection of algebras with nilpotent kernel.
* `AlgebraicGeometry.Space.FormallySmooth.exists_isLift_of_isNilpotent`: lifting along a closed
  immersion of affine objects of the site with nilpotent kernel on global sections.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Lifts along the spectrum of a surjection with nilpotent kernel.** Let `a : F ⟶ G` be
formally smooth, let `A ⟶ A₀` be a surjection of algebras over a ring `R'` with `Spec R' ⟶ S`
fixed, whose kernel has vanishing `n`-th power, and suppose both spectra lie in the site. Then
every lifting problem for `a` along `Spec A₀ ⟶ Spec A` has a solution: the thickening is the
composite of the square-zero thickening `Spec A₀ ⟶ Spec (A ⧸ K ^ (n - 1))` and of
`Spec (A ⧸ K ^ (n - 1)) ⟶ Spec A`, whose kernel has smaller nilpotency index. -/
@[sga "3 III 2.5" "more general"]
theorem FormallySmooth.exists_isLift_specOverHom_of_isNilpotent
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} {a : F ⟶ G} (ha : FormallySmooth a)
    {R' : Type u} [CommRing R'] (s₀ : Spec (.of R') ⟶ S) (n : ℕ) :
    ∀ {A A₀ : Type u} [CommRing A] [CommRing A₀] [Algebra R' A] [Algebra R' A₀]
      [Algebra A A₀] [IsScalarTower R' A A₀],
      Function.Surjective (algebraMap A A₀) →
      RingHom.ker (algebraMap A A₀) ^ n = ⊥ →
      ∀ (hA : B.Contains (Spec (.of A))) (hA₀ : B.Contains (Spec (.of A₀)))
        (x : F.obj (op (specOver B S hS s₀ A₀ hA₀))) (y : G.obj (op (specOver B S hS s₀ A hA))),
        a.app _ x = G.map (specOverHom B S hS s₀ hA hA₀ (IsScalarTower.toAlgHom R' A A₀)).op y →
        ∃ z, IsLift a (specOverHom B S hS s₀ hA hA₀ (IsScalarTower.toAlgHom R' A A₀)) x y z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A A₀ _ _ _ _ _ _ hπ hn hA hA₀ x y hxy
  by_cases h2 : n ≤ 2
  · refine ha _ _ (inferInstanceAs (IsAffine (Spec (.of A₀))))
      (inferInstanceAs (IsAffine (Spec (.of A)))) _ ?_ x y hxy
    exact Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom (algebraMap A A₀)) hπ
      (pow_eq_zero_of_le h2 hn)
  push Not at h2
  -- the intermediate quotient `A₁ = A ⧸ K ^ (n - 1)`
  set K := RingHom.ker (algebraMap A A₀)
  let A₁ := A ⧸ K ^ (n - 1)
  let : Algebra A₁ A₀ := (Ideal.Quotient.lift (K ^ (n - 1)) (algebraMap A A₀) fun b hb =>
    (RingHom.mem_ker).1 (Ideal.pow_le_self (by omega) hb)).toAlgebra
  have : IsScalarTower A A₁ A₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R' A₁ A₀ := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R' A A₁, IsScalarTower.algebraMap_apply R' A A₀,
      IsScalarTower.algebraMap_apply A A₁ A₀]
  have hA₁ : B.Contains (Spec (.of A₁)) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hA
      ((Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (le_max_right _ _))
  have hπ₁ : Function.Surjective (algebraMap A₁ A₀) :=
    Function.Surjective.of_comp (g := Ideal.Quotient.mk (K ^ (n - 1))) hπ
  have hker₁ : RingHom.ker (algebraMap A₁ A₀) = K.map (Ideal.Quotient.mk (K ^ (n - 1))) := by
    ext c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.2 (Ideal.pow_le_self (by omega)),
      RingHom.mem_ker, RingHom.mem_ker]
    rfl
  have hfac : specOverHom B S hS s₀ hA hA₀ (IsScalarTower.toAlgHom R' A A₀) =
      specOverHom B S hS s₀ hA₁ hA₀ (IsScalarTower.toAlgHom R' A₁ A₀) ≫
        specOverHom B S hS s₀ hA hA₁ (IsScalarTower.toAlgHom R' A A₁) := by
    rw [specOverHom_comp]
    rfl
  rw [hfac, op_comp, Functor.map_comp, types_comp_apply] at hxy
  -- first lift across `Spec A₀ ⟶ Spec A₁`, then across `Spec A₁ ⟶ Spec A`
  obtain ⟨z₁, hz₁x, hz₁y⟩ := ih (n - 1) (by omega) (A := A₁) (A₀ := A₀) hπ₁ (by
    rw [hker₁, ← Ideal.map_pow, Ideal.map_quotient_self]) hA₁ hA₀ x _ hxy
  obtain ⟨z, hzx, hzy⟩ := ih 2 (by omega) (A := A) (A₀ := A₁) Ideal.Quotient.mk_surjective (by
    rw [show RingHom.ker (algebraMap A A₁) = K ^ (n - 1) from Ideal.mk_ker, ← pow_mul]
    exact pow_eq_zero_of_le (by omega) hn) hA hA₁ z₁ y hz₁y
  refine ⟨z, ?_, hzy⟩
  rw [hfac, op_comp, Functor.map_comp, types_comp_apply, hzx, hz₁x]

/-- **Lifts along a closed immersion with nilpotent kernel.** A formally smooth transformation
`a : F ⟶ G` of presheaves on the big fppf site of `S` lifts along every closed immersion
`i : T ⟶ T'` of affine objects of the site whose kernel on global sections is nilpotent: such
an `i` is, under the identification of affine objects with spectra, the spectrum of a surjection
of rings with nilpotent kernel. -/
theorem FormallySmooth.exists_isLift_of_isNilpotent
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} {a : F ⟶ G} (ha : FormallySmooth a)
    {T T' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] (i : T ⟶ T')
    (hi : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hnil : IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom))
    (x : F.obj (op T)) (y : G.obj (op T')) (hxy : a.app (op T) x = G.map i.op y) :
    ∃ z, IsLift a i x y z := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map i)
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map i).appTop.hom.toAlgebra
  have hsurj : Function.Surjective (algebraMap Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigFppfOver.toScheme B S hS).map i)).2
  obtain ⟨n, hn⟩ := hnil
  let eT := isoSpecOver B S hS i rfl
  let eT' := isoSpecOverSelf B S hS T'
  let m := specOverHom B S hS (specStructure B S hS T') (contains_spec_sections B S hS T')
    (contains_spec_sections B S hS T) (IsScalarTower.toAlgHom _ _ _)
  have hiT : i = eT.hom ≫ m ≫ eT'.inv := by
    calc i = eT.hom ≫ eT.inv ≫ i := by simp
      _ = _ := by
        rw [isoSpecOver_inv_comp]
        exact congrArg (fun t => eT.hom ≫ t ≫ eT'.inv)
          (specOverHom_congr (AlgHom.ext fun _ => rfl))
  -- transport the lifting problem along the identifications with spectra
  have hxy' : a.app _ (F.map eT.inv.op x) = G.map m.op (G.map eT'.inv.op y) := by
    rw [← types_comp_apply (F.map _) (a.app _), a.naturality, types_comp_apply, hxy,
      ← types_comp_apply (G.map _) (G.map _), ← types_comp_apply (G.map _) (G.map _),
      ← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp, hiT, ← Category.assoc,
      eT.inv_hom_id, Category.id_comp]
  obtain ⟨z, hzx, hzy⟩ := ha.exists_isLift_specOverHom_of_isNilpotent
    (specStructure B S hS T') n hsurj (by rwa [Ideal.zero_eq_bot] at hn) _ _ _ _ hxy'
  refine ⟨F.map eT'.hom.op z, ?_, ?_⟩
  · rw [← types_comp_apply (F.map _) (F.map _), ← F.map_comp, ← op_comp, hiT,
      Category.assoc, Category.assoc, eT'.inv_hom_id, Category.comp_id, op_comp, F.map_comp,
      types_comp_apply, hzx, ← types_comp_apply (F.map _) (F.map _), ← F.map_comp, ← op_comp,
      eT.hom_inv_id, op_id, F.map_id, types_id_apply]
  · rw [← types_comp_apply (F.map _) (a.app _), a.naturality, types_comp_apply, hzy,
      ← types_comp_apply (G.map _) (G.map _), ← G.map_comp, ← op_comp, eT'.hom_inv_id, op_id,
      G.map_id, types_id_apply]

end AlgebraicGeometry.Space
