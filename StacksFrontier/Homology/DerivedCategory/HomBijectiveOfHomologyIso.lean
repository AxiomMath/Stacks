module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Precomposition with a morphism inducing isomorphisms on high cohomology

Let `α : X ⟶ L` be a morphism in the derived category `D(C)` of an abelian category such that
`Hⁱ(α)` is an isomorphism for `i > m` and surjective for `i = m`. Then the cone of `α` is
concentrated in degrees `≤ m - 1`, so for every object `Y` concentrated in degrees `≥ m + 1`
precomposition with `α` is a bijection `Hom(L, Y) ⟶ Hom(X, Y)`.

This is how an `m`-pseudo-coherent object (Stacks 064Q) may be replaced by a bounded complex of
finite free modules when computing `Ext^n(-, M)` for `n < -m`.

## Main results

* `DerivedCategory.isZero_homology_cone_of_isIso_of_epi`: the cohomology of the cone of `α` in
  degrees `≥ m` vanishes.
* `DerivedCategory.bijective_precomp_of_isIso_homology_of_epi`: precomposition with `α` is
  bijective on morphisms into objects `≥ m + 1`.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated Triangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **The cone of a morphism inducing isomorphisms above `m` and a surjection in degree `m`
has no cohomology in degrees `≥ m`.** -/
theorem isZero_homology_cone_of_isIso_of_epi (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso ((homologyFunctor C i).map T.mor₁))
    (hepi : Epi ((homologyFunctor C m).map T.mor₁)) (i : ℤ) (hi : m ≤ i) :
    IsZero ((homologyFunctor C i).obj T.obj₃) := by
  have hep : Epi (((homologyFunctor C 0).shift i).map T.mor₁) := by
    rcases hi.lt_or_eq with hlt | rfl
    · have := hiso i hlt
      show Epi ((homologyFunctor C i).map T.mor₁)
      infer_instance
    · exact hepi
  have hmo : Mono (((homologyFunctor C 0).shift (i + 1)).map T.mor₁) := by
    have := hiso (i + 1) (by omega)
    show Mono ((homologyFunctor C (i + 1)).map T.mor₁)
    infer_instance
  have h₁ := ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff T hT i).1 hep
  have h₂ := ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff T hT i (i + 1)
    rfl).1 hmo
  exact ((homologyFunctor C 0).homologySequence_exact₃ T hT i (i + 1) rfl).isZero_of_both_zeros
    h₁ h₂

/-- **Precomposition with a morphism inducing isomorphisms above `m` and a surjection in degree
`m` is bijective on morphisms into an object concentrated in degrees `≥ m + 1`.** -/
theorem bijective_precomp_of_isIso_homology_of_epi {X L : DerivedCategory C} (α : X ⟶ L)
    (m : ℤ) (hiso : ∀ i : ℤ, m < i → IsIso ((homologyFunctor C i).map α))
    (hepi : Epi ((homologyFunctor C m).map α)) (Y : DerivedCategory C) [Y.IsGE (m + 1)] :
    Function.Bijective (fun e : L ⟶ Y => α ≫ e) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle α
  let T := Triangle.mk α g h
  have hZ : Z.IsLE (m - 1) := (isLE_iff Z (m - 1)).2 fun i hi =>
    isZero_homology_cone_of_isIso_of_epi T hT m hiso hepi i (by omega)
  have hZ' : (Z⟦(-1 : ℤ)⟧).IsLE m := TStructure.t.isLE_shift Z (m - 1) (-1) m (by omega)
  constructor
  · intro e₁ e₂ he
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ T hT (e₁ - e₂)
      (by rw [Preadditive.comp_sub, sub_eq_zero]; exact he)
    have : TStructure.t.IsLE T.obj₃ (m - 1) := hZ
    rw [TStructure.t.zero k (m - 1) (m + 1) (by omega), comp_zero] at hk
    exact sub_eq_zero.1 hk
  · intro e
    have : TStructure.t.IsLE T.invRotate.obj₁ m := hZ'
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ T.invRotate (inv_rot_of_distTriang T hT) e
      (TStructure.t.zero _ m (m + 1) (by omega))
    exact ⟨k, hk.symm⟩

end DerivedCategory
