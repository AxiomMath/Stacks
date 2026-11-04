module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Invertibility of the transpose of a comparison of right adjoints

Consider adjunctions `φ^* ⊣ φ_*` between `ℰ` and `ℰ'`, `τ^* ⊣ τ_*` between `𝒵` and `𝒵'`,
`a ⊣ Z` between `𝒵` and `ℰ` and `a' ⊣ Z'` between `𝒵'` and `ℰ'`, together with a natural
isomorphism `σ : φ_* ⋙ Z ≅ Z' ⋙ τ_*`.  For an object `N` of `ℰ` the morphism

`β_N : τ^*(Z N) ⟶ Z'(φ^* N)`,

the transpose along `τ^* ⊣ τ_*` of `Z(η_N)` followed by `σ`, is an isomorphism as soon as the
counit of `a ⊣ Z` at `N` and the unit of `a' ⊣ Z'` at `τ^*(Z N)` are: it is the unit, followed
by `Z'` applied to the conjugate of `σ` and to `φ^*` of the counit.

## Main results

* `CategoryTheory.Adjunction.transposeComparison_eq`: the factorization of `β_N`.
* `CategoryTheory.Adjunction.isIso_transposeComparison`: `β_N` is an isomorphism.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.Adjunction

variable {ℰ ℰ' 𝒵 𝒵' : Type*} [Category* ℰ] [Category* ℰ'] [Category* 𝒵] [Category* 𝒵']
  {φu : ℰ ⥤ ℰ'} {φl : ℰ' ⥤ ℰ} {τu : 𝒵 ⥤ 𝒵'} {τl : 𝒵' ⥤ 𝒵}
  {a : 𝒵 ⥤ ℰ} {Z : ℰ ⥤ 𝒵} {a' : 𝒵' ⥤ ℰ'} {Z' : ℰ' ⥤ 𝒵'}
  (adjφ : φu ⊣ φl) (adjτ : τu ⊣ τl) (adja : a ⊣ Z) (adja' : a' ⊣ Z')
  (σ : φl ⋙ Z ⟶ Z' ⋙ τl)

/-- The transpose along `τ^* ⊣ τ_*` of `Z(η_N)` followed by `σ`. -/
def transposeComparison (N : ℰ) : τu.obj (Z.obj N) ⟶ Z'.obj (φu.obj N) :=
  (adjτ.homEquiv _ _).symm (Z.map (adjφ.unit.app N) ≫ σ.app (φu.obj N))

/-- **The factorization of the transposed comparison** through the conjugate of `σ`. -/
theorem transposeComparison_eq (N : ℰ) :
    transposeComparison adjφ adjτ σ N =
      adja'.unit.app (τu.obj (Z.obj N)) ≫
        Z'.map (((conjugateEquiv (adja.comp adjφ) (adjτ.comp adja')).symm σ).app (Z.obj N)) ≫
          Z'.map (φu.map (adja.counit.app N)) := by
  rw [transposeComparison, Equiv.symm_apply_eq, homEquiv_unit]
  have hc := unit_conjugateEquiv (adja.comp adjφ) (adjτ.comp adja')
    ((conjugateEquiv (adja.comp adjφ) (adjτ.comp adja')).symm σ) (Z.obj N)
  rw [Equiv.apply_symm_apply] at hc
  simp only [comp_unit_app, Functor.comp_obj, Functor.comp_map, Category.assoc] at hc
  have hn := σ.naturality (φu.map (adja.counit.app N))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [Functor.map_comp]
  rw [← reassoc_of% hc, ← hn, ← Functor.map_comp_assoc]
  have hη := adjφ.unit.naturality (adja.counit.app N)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hη
  rw [← hη, Functor.map_comp, ← Category.assoc, ← Category.assoc, adja.right_triangle_components,
    Category.id_comp]

/-- The transpose along `τ^* ⊣ τ_*` of `Z(r)` followed by `σ`, for an arbitrary `r : N ⟶ φ_* M`,
is the transposed comparison followed by `Z'` of the transpose of `r`. -/
theorem homEquiv_symm_map_comp_app {N : ℰ} {M : ℰ'} (r : N ⟶ φl.obj M) :
    (adjτ.homEquiv _ _).symm (Z.map r ≫ σ.app M) =
      transposeComparison adjφ adjτ σ N ≫ Z'.map ((adjφ.homEquiv _ _).symm r) := by
  rw [transposeComparison, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hr : r = adjφ.unit.app N ≫ φl.map ((adjφ.homEquiv _ _).symm r) :=
    ((adjφ.homEquiv _ _).apply_symm_apply r).symm.trans (adjφ.homEquiv_unit _ _ _)
  have hn := σ.naturality ((adjφ.homEquiv _ _).symm r)
  simp only [Functor.comp_map] at hn
  conv_lhs => rw [hr]
  rw [Functor.map_comp, Category.assoc, hn, Category.assoc]

/-- **The transposed comparison is an isomorphism** as soon as the counit of `a ⊣ Z` at `N` and
the unit of `a' ⊣ Z'` at `τ^*(Z N)` are, `σ` being an isomorphism. -/
theorem isIso_transposeComparison [IsIso σ] (N : ℰ) [IsIso (adja.counit.app N)]
    [IsIso (adja'.unit.app (τu.obj (Z.obj N)))] :
    IsIso (transposeComparison adjφ adjτ σ N) := by
  rw [transposeComparison_eq adjφ adjτ adja adja' σ N]
  infer_instance

/-- **The transpose of `Z(r)` followed by `σ` is an isomorphism** as soon as the transpose of `r`
is, the counit of `a ⊣ Z` at `N` and the unit of `a' ⊣ Z'` at `τ^*(Z N)` are, `σ` being an
isomorphism. -/
theorem isIso_homEquiv_symm_map_comp [IsIso σ] {N : ℰ} {M : ℰ'} (r : N ⟶ φl.obj M)
    [IsIso (adja.counit.app N)] [IsIso (adja'.unit.app (τu.obj (Z.obj N)))]
    [IsIso ((adjφ.homEquiv _ _).symm r)] :
    IsIso ((adjτ.homEquiv _ _).symm (Z.map r ≫ σ.app M)) := by
  rw [homEquiv_symm_map_comp_app adjφ adjτ σ r]
  have := isIso_transposeComparison adjφ adjτ adja adja' σ N
  infer_instance

/-- Transporting an adjunction along an isomorphism of right adjoints keeps the units
invertible. -/
theorem isIso_ofNatIsoRight_unit_app {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) (X : C) [IsIso (adj.unit.app X)] :
    IsIso ((adj.ofNatIsoRight iso).unit.app X) := by
  simp only [ofNatIsoRight]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- Transporting an adjunction along an isomorphism of right adjoints keeps the counits
invertible. -/
theorem isIso_ofNatIsoRight_counit_app {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) (Y : D) [IsIso (adj.counit.app Y)] :
    IsIso ((adj.ofNatIsoRight iso).counit.app Y) := by
  simp only [ofNatIsoRight]
  rw [NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

end CategoryTheory.Adjunction
