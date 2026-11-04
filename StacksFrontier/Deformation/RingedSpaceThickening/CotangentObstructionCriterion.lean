module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTriangleObstruction

/-!
# The obstruction class of a distinguished triangle, read through a comparison

This file isolates the formal step of the proof of clause (1) of **Stacks 08UZ**: given a
distinguished triangle `A ⟶ L' ⟶ L ⟶ A[1]`, a map `π : L' ⟶ N` along which every degree one
class on `L'` is restricted from `N`, a map `κ : A ⟶ M` which is injective on the classes it
pulls back, a map `ν : M ⟶ N` with `u ∘ π = ν ∘ κ`, and a family of "extensions" whose classes
on `N` exhaust the degree one classes and restrict along `ν` to the negatives of prescribed
classes on `M`, the Yoneda product of the connecting morphism with `κ^* c` vanishes exactly
when `c` is the prescribed class of some extension.

## Main results

* `CategoryTheory.Pretriangulated.shiftedHom_comp_eq_zero_iff_exists`: the formal criterion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {𝒯 : Type*} [Category 𝒯] [HasZeroObject 𝒯] [HasShift 𝒯 ℤ] [Preadditive 𝒯]
  [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]

/-- **The formal step of the obstruction criterion.** Let `T` be a distinguished triangle with
first morphism `u : A ⟶ L'`, let `π : L' ⟶ N` be such that every map `L' ⟶ G⟦1⟧` factors through
`π`, let `κ : A ⟶ M`, `ν : M ⟶ N` with `u ≫ π = κ ≫ ν`, let `ι : Γ →+ (M ⟶ G⟦1⟧)` be a group of
classes on `M` on which precomposition with `κ` is injective, and let `cls : 𝓔 → (N ⟶ G⟦1⟧)` be a
surjective family with `ν ≫ cls E = -ι (γ E)`. Then for `c : Γ` the Yoneda product of the third
morphism of `T` with `κ ≫ ι c` vanishes exactly when `c = γ E` for some `E`. -/
theorem shiftedHom_comp_eq_zero_iff_exists (T : Triangle 𝒯) (hT : T ∈ distTriang 𝒯)
    {N M G : 𝒯} (π : T.obj₂ ⟶ N)
    (hπ : ∀ z : T.obj₂ ⟶ G⟦(1 : ℤ)⟧, ∃ z' : N ⟶ G⟦(1 : ℤ)⟧, z = π ≫ z')
    (κ : T.obj₁ ⟶ M) (ν : M ⟶ N) (hcompat : T.mor₁ ≫ π = κ ≫ ν)
    {Γ : Type*} [AddCommGroup Γ] (ι : Γ →+ (M ⟶ G⟦(1 : ℤ)⟧))
    (hinj : ∀ a : Γ, κ ≫ ι a = 0 → a = 0)
    {𝓔 : Type*} (cls : 𝓔 → (N ⟶ G⟦(1 : ℤ)⟧)) (hcls : Function.Surjective cls)
    (γ : 𝓔 → Γ) (hγ : ∀ E, ν ≫ cls E = -ι (γ E)) (c : Γ) :
    ShiftedHom.comp T.mor₃ (κ ≫ ι c : ShiftedHom T.obj₁ G (1 : ℤ))
        (show (1 : ℤ) + 1 = 2 by omega) = 0 ↔ ∃ E, γ E = c := by
  rw [← AlgebraicGeometry.RingedSpaceThickening.exists_comp_eq_iff_shiftedHom_comp_eq_zero' T hT]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨z', rfl⟩ := hπ z
    obtain ⟨E, hE⟩ := hcls (-z')
    have hν : ν ≫ z' = ι (γ E) := neg_injective (by rw [← Preadditive.comp_neg, ← hE, hγ])
    refine ⟨E, (sub_eq_zero.1 (hinj _ ?_)).symm⟩
    have hz' : κ ≫ ι c = κ ≫ ι (γ E) := by
      rw [hz, ← Category.assoc, hcompat, Category.assoc, hν]
    rw [map_sub, Preadditive.comp_sub, hz', sub_self]
  · rintro ⟨E, rfl⟩
    refine ⟨π ≫ (-cls E), ?_⟩
    rw [← Category.assoc, hcompat, Category.assoc, Preadditive.comp_neg, hγ, neg_neg]

end CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasDerivedCategory 𝒞]

/-- **A map into `M[1]` which is surjective on `H^{-1}` detects degree one classes coming from
`M`.** If `K` lies in degrees `≤ -1` and `κ : K ⟶ M[1]` is an epimorphism on `H^{-1}`, then a map
`a : M ⟶ G` of objects of `𝒞` with `κ ≫ a[1] = 0` vanishes. The cone of `κ` lies in degrees
`≤ -2`, and has no map to `G[1]`. -/
theorem eq_zero_of_comp_shift_map_eq_zero {K : DerivedCategory 𝒞} {M G : 𝒞}
    (κ : K ⟶ ((singleFunctor 𝒞 0).obj M)⟦(1 : ℤ)⟧) [K.IsLE (-1)]
    (hκ : Epi ((homologyFunctor 𝒞 (-1)).map κ)) (a : M ⟶ G)
    (ha : κ ≫ ((singleFunctor 𝒞 0).map a)⟦(1 : ℤ)⟧' = 0) : a = 0 := by
  obtain ⟨Z, v, w, hT⟩ := Pretriangulated.distinguished_cocone_triangle κ
  have hM₁ : TStructure.t.IsLE (((singleFunctor 𝒞 0).obj M)⟦(1 : ℤ)⟧) (-1) :=
    TStructure.t.isLE_shift _ 0 1 (-1)
  have hG₁ : TStructure.t.IsGE (((singleFunctor 𝒞 0).obj G)⟦(1 : ℤ)⟧) (-1) :=
    TStructure.t.isGE_shift _ 0 1 (-1)
  have hZ : Z.IsLE (-2) := by
    rw [isLE_iff]
    intro i hi
    have hepi : Epi ((homologyFunctor 𝒞 i).map v) :=
      (HomologySequence.exact₃ (Triangle.mk κ v w) hT i (i + 1)).epi_f
        ((isZero_of_isLE K (-1) (i + 1) (by omega)).eq_of_tgt _ _)
    have hv : (homologyFunctor 𝒞 i).map v = 0 := by
      obtain rfl | hi' := eq_or_ne i (-1)
      · rw [← cancel_epi ((homologyFunctor 𝒞 (-1)).map κ), ← Functor.map_comp,
          show κ ≫ v = 0 from comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero, comp_zero]
      · exact (isZero_of_isLE _ (-1) i (by omega)).eq_of_src _ _
    rw [hv] at hepi
    exact IsZero.of_epi_zero ((homologyFunctor 𝒞 i).obj (((singleFunctor 𝒞 0).obj M)⟦(1 : ℤ)⟧))
      ((homologyFunctor 𝒞 i).obj Z)
  obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ (Triangle.mk κ v w) hT
    (((singleFunctor 𝒞 0).map a)⟦(1 : ℤ)⟧') ha
  rw [TStructure.t.zero_of_isLE_of_isGE y (-2) (-1) (by omega) hZ hG₁, comp_zero] at hy
  exact (singleFunctor 𝒞 0).map_eq_zero_iff.1
    ((shiftFunctor (DerivedCategory 𝒞) (1 : ℤ)).map_eq_zero_iff.1 hy)

/-- **A complex in degrees `≤ 0` mapping isomorphically on `H⁰` to a complex isomorphic in the
derived category to an object placed in degree `-1` lies in degrees `≤ -1`.** -/
theorem isLE_negOne_Q_obj_of_iso {D N : CochainComplex 𝒞 ℤ} {M : 𝒞} (π : D ⟶ N)
    (I : Q.obj ((HomologicalComplex.single 𝒞 (ComplexShape.up ℤ) (-1)).obj M) ≅ Q.obj N)
    (hπ : IsIso (HomologicalComplex.homologyMap π 0)) (hD : ∀ i : ℤ, 0 < i → IsZero (D.X i)) :
    (Q.obj D).IsLE (-1) := by
  rw [isLE_Q_obj_iff, CochainComplex.isLE_iff]
  intro i hi
  obtain rfl | h₀ := eq_or_ne i 0
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine (asIso (HomologicalComplex.homologyMap π 0)).isZero_iff.2 ?_
    refine ((homologyFunctorFactors 𝒞 0).app N).isZero_iff.1 ?_
    refine ((homologyFunctor 𝒞 0).mapIso I).isZero_iff.1 ?_
    refine ((homologyFunctorFactors 𝒞 0).app _).isZero_iff.2 ?_
    exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ (by decide)
  · exact HomologicalComplex.ExactAt.of_isZero (hD i (by omega))

/-- **The composite `Q D ⟶ Q N ≅ Y` is an isomorphism on `H^n`** when the first map is. -/
theorem isIso_homologyFunctor_map_Q_map_comp_iso_inv {D N : CochainComplex 𝒞 ℤ}
    {Y : DerivedCategory 𝒞} (π : D ⟶ N) (I : Y ≅ Q.obj N) (n : ℤ)
    (hπ : IsIso (HomologicalComplex.homologyMap π n)) :
    IsIso ((homologyFunctor 𝒞 n).map (Q.map π ≫ I.inv)) := by
  have : IsIso ((homologyFunctor 𝒞 n).map (Q.map π)) :=
    (NatIso.isIso_map_iff (homologyFunctorFactors 𝒞 n) π).2 hπ
  rw [Functor.map_comp]
  infer_instance

end DerivedCategory
