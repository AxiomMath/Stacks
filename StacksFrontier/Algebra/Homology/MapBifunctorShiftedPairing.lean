module

public import Mathlib.Algebra.Homology.BifunctorShift
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PairingFiveLemma

/-!
# Shifted pairings of total complexes, summand by summand

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor additive in each variable and `g : Tot(F(K, L)) ⟶ M` a
morphism of cochain complexes. For `n + m = 0` the shift of the pairing `g` for the bifunctor
`F.map₂CochainComplex` (`CategoryTheory.Functor.shiftedPairing`, built from the commutations
`CochainComplex.mapBifunctorShift₁Iso` and `CochainComplex.mapBifunctorShift₂Iso` of the total
complex with the shifts) is the map `Tot(F(K[n], L[m])) ⟶ M` which on the summand
`F(K[n]^i, L[m]^j) = F(K^{i+n}, L^{j+m})` is `(-1)^{im}` times `g` on the summand
`F(K^{i+n}, L^{j+m})` (`CategoryTheory.Functor.ι_shiftedPairing_map₂CochainComplex_f`).

This is how the connecting maps of the triangles of the stupid filtrations are paired in the
proof of [Stacks, Tag 0G8K].

## Main results

* `CochainComplex.shiftFunctorCompIsoId_hom_app_f`: the components of `K[n][m] ≅ K`.
* `CategoryTheory.Functor.ι_shiftedPairing_map₂CochainComplex_f`.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C]

/-- The components of the identification `K[n][m] ≅ K`, for `n + m = 0`, are the identifications
of terms `K^{k+m+n} = K^k`. -/
theorem shiftFunctorCompIsoId_hom_app_f (K : CochainComplex C ℤ) (n m : ℤ) (h : n + m = 0)
    (k : ℤ) :
    ((shiftFunctorCompIsoId (CochainComplex C ℤ) n m h).hom.app K).f k =
      (K.XIsoOfEq (show k + m + n = k by omega)).hom := by
  simp [shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]

end CochainComplex

namespace CategoryTheory.Functor

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
    CochainComplex.HasMapBifunctor K₁ K₂ F]

/-- **The shift of a pairing of total complexes on a summand**: for `g : Tot(F(K, L)) ⟶ M` and
`n + m = 0`, the shifted pairing `Tot(F(K[n], L[m])) ⟶ M` is, on the summand
`F(K[n]^i, L[m]^j) = F(K^{i'}, L^{j'})` (`i' = i + n`, `j' = j + m`), the sign `(-1)^{im}` times
`g` on the summand `F(K^{i'}, L^{j'})`. -/
theorem ι_shiftedPairing_map₂CochainComplex_f {K : CochainComplex C₁ ℤ}
    {L : CochainComplex C₂ ℤ} {M : CochainComplex D ℤ}
    (g : CochainComplex.mapBifunctor K L F ⟶ M) (n m : ℤ) (h : n + m = 0)
    (i j k : ℤ) (hk : i + j = k) (i' j' : ℤ) (hi' : i' = i + n) (hj' : j' = j + m) :
    CochainComplex.ιMapBifunctor (K⟦n⟧) (L⟦m⟧) F i j k hk ≫
        (F.map₂CochainComplex.shiftedPairing g n m h).f k =
      (i * m).negOnePow • ((F.map (K.shiftFunctorObjXIso n i i' hi').hom).app _ ≫
        (F.obj _).map (L.shiftFunctorObjXIso m j j' hj').hom ≫
          CochainComplex.ιMapBifunctor K L F i' j' k (by omega) ≫ g.f k) := by
  subst hi' hj'
  have key : ∀ (k₁ k₂ : ℤ) (e : k₁ = k₂) (hh : i + n + (j + m) = k₁),
      CochainComplex.ιMapBifunctor K L F (i + n) (j + m) k₁ hh ≫
        ((CochainComplex.mapBifunctor K L F).XIsoOfEq e).hom =
      CochainComplex.ιMapBifunctor K L F (i + n) (j + m) k₂ (hh.trans e) := by
    rintro _ _ rfl _
    simp
  change CochainComplex.ιMapBifunctor (K⟦n⟧) (L⟦m⟧) F i j k hk ≫
      (CochainComplex.mapBifunctorShift₂Iso (K⟦n⟧) L F m).hom.f k ≫
      (CochainComplex.mapBifunctorShift₁Iso K L F n).hom.f (k + m) ≫
      ((shiftFunctorCompIsoId (CochainComplex D ℤ) n m h).hom.app
        (CochainComplex.mapBifunctor K L F)).f k ≫ g.f k = _
  rw [CochainComplex.shiftFunctorCompIsoId_hom_app_f,
    CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ F m i j k hk (j + m) (k + m) rfl rfl,
    Linear.units_smul_comp]
  congr 1
  have e₀ : (CochainComplex.shiftFunctorObjXIso (CochainComplex.mapBifunctor (K⟦n⟧) L F) m k
      (k + m) rfl).inv = 𝟙 _ := by simp
  rw [Category.assoc, Category.assoc, e₀, Category.id_comp,
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ F n i (j + m) (k + m) (by omega)
      (i + n) (k + m + n) rfl rfl, NatTrans.naturality_assoc]
  congr 2
  change CochainComplex.ιMapBifunctor K L F (i + n) (j + m) (k + m + n) (by omega) ≫
      ((CochainComplex.mapBifunctor K L F).XIsoOfEq (rfl : k + m + n = k + m + n)).inv ≫
      ((CochainComplex.mapBifunctor K L F).XIsoOfEq (show k + m + n = k by omega)).hom ≫
        g.f k = _
  rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.id_comp,
    reassoc_of% (key (k + m + n) k (by omega) (by omega))]

end CategoryTheory.Functor
