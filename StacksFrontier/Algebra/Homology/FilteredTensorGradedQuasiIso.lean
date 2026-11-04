module

public import StacksFrontier.Algebra.Homology.SubmoduleFiltrationQuasiIso
public import StacksFrontier.Homology.KFlat.TensorLeftQuasiIso
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Filtered complexes whose graded pieces are tensor products with the zeroth one

Let `φ : M ⟶ K` be a morphism of finitely filtered complexes of `R`-modules (see
`CochainComplex.SubmoduleFiltration`). Suppose that over a commutative ring `A` the zeroth graded
pieces are modelled by bounded above complexes `G_M`, `G_K` of flat `A`-modules and an
`A`-linear quasi-isomorphism `g : G_M ⟶ G_K`, and that for every `k` the `k`-th graded pieces
are, as complexes of abelian groups, the complexes `N_k ⊗_A G_M` and `N_k ⊗_A G_K` moved up by
`k` degrees, for some `A`-module `N_k`, compatibly with `φ` and `N_k ⊗ g`. Then `φ` is a
quasi-isomorphism.

This is the skeleton of the proof of [Stacks, Tag 0FUM]: there `M = ⨁ Ω^•_{A/R}[-n_i]`, `K` is a
Čech complex computing `RΓ(X, Ω^•_{X/S})`, both are filtered by the forms pulled back from
`Y = Spec A`, `N_k = Ω^k_{A/R}`, and the graded pieces are `Ω^k_{A/R}[-k] ⊗_A gr^0`. The zeroth
graded piece of `K` is a bounded complex of flat `A`-modules, so tensoring with `N_k` preserves the
quasi-isomorphism `gr^0φ` (`CochainComplex.KFlat.quasiIso_tensorLeft_map_of_flat`), and the
comparison of finitely filtered complexes
(`CochainComplex.SubmoduleFiltration.quasiIso_of_quasiIso_gradedMap`) concludes.

The move by `k` degrees is the *unsigned* one, `CochainComplex.reindex`: the graded pieces of a
filtration by forms pulled back from the base acquire no sign, because multiplication on the right
by a closed pulled-back form commutes with the differential modulo the next step.

## Main definitions

* `CochainComplex.reindex`: the complex `Z` moved up by `k` degrees, with the same differentials.

## Main results

* `CochainComplex.quasiIso_reindexMap_iff`: moving up by `k` degrees preserves and reflects
  quasi-isomorphisms.
* `CochainComplex.SubmoduleFiltration.quasiIso_of_graded_iso_tensor`: the statement above.

## References

* [Stacks Project, Tag 0FUM](https://stacks.math.columbia.edu/tag/0FUM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe v u

namespace CochainComplex

section Reindex

variable {C : Type*} [Category* C] [Preadditive C]

/-- The complex `Z` moved up by `k` degrees with **unchanged** differentials:
`(reindex Z k)^n = Z^{n-k}`. This differs from the shift `Z⟦-k⟧` by the sign `(-1)^k` of the
differentials. -/
def reindex (Z : CochainComplex C ℤ) (k : ℤ) : CochainComplex C ℤ where
  X n := Z.X (n - k)
  d n m := Z.d (n - k) (m - k)
  shape n m h := Z.shape _ _ fun h' => h (by simp only [ComplexShape.up_Rel] at h' ⊢; omega)
  d_comp_d' _ _ _ _ _ := Z.d_comp_d _ _ _

/-- The morphism of complexes moved up by `k` degrees. -/
def reindexMap {Z Z' : CochainComplex C ℤ} (f : Z ⟶ Z') (k : ℤ) : Z.reindex k ⟶ Z'.reindex k where
  f n := f.f (n - k)
  comm' _ _ _ := f.comm _ _

/-- The degree `n` component of `reindexMap f k` is the degree `n - k` component of `f`. -/
@[simp]
theorem reindexMap_f {Z Z' : CochainComplex C ℤ} (f : Z ⟶ Z') (k n : ℤ) :
    (reindexMap f k).f n = f.f (n - k) :=
  rfl

/-- `reindexMap f k` is a quasi-isomorphism in degree `n` if and only if `f` is one in degree
`n - k`. -/
theorem quasiIsoAt_reindexMap_iff [CategoryWithHomology C] {Z Z' : CochainComplex C ℤ}
    (f : Z ⟶ Z') (k n : ℤ) : QuasiIsoAt (reindexMap f k) n ↔ QuasiIsoAt f (n - k) := by
  rw [quasiIsoAt_iff' (reindexMap f k) (n - 1) n (n + 1) (by simp) (by simp),
    quasiIsoAt_iff' f (n - 1 - k) (n - k) (n + 1 - k) (by simp; omega) (by simp; omega)]
  rfl

/-- **Moving up by `k` degrees preserves and reflects quasi-isomorphisms.** -/
theorem quasiIso_reindexMap_iff [CategoryWithHomology C] {Z Z' : CochainComplex C ℤ}
    (f : Z ⟶ Z') (k : ℤ) : QuasiIso (reindexMap f k) ↔ QuasiIso f := by
  simp only [quasiIso_iff, quasiIsoAt_reindexMap_iff]
  exact ⟨fun h n => by simpa using h (n + k), fun h n => h (n - k)⟩

/-- Moving the identity up by `k` degrees gives the identity. -/
@[simp]
theorem reindexMap_id (Z : CochainComplex C ℤ) (k : ℤ) : reindexMap (𝟙 Z) k = 𝟙 (Z.reindex k) :=
  rfl

/-- Moving up by `k` degrees is compatible with composition. -/
@[simp]
theorem reindexMap_comp {Z Z' Z'' : CochainComplex C ℤ} (f : Z ⟶ Z') (g : Z' ⟶ Z'') (k : ℤ) :
    reindexMap (f ≫ g) k = reindexMap f k ≫ reindexMap g k :=
  rfl

/-- An isomorphism of complexes, moved up by `k` degrees. -/
def reindexIso {Z Z' : CochainComplex C ℤ} (e : Z ≅ Z') (k : ℤ) : Z.reindex k ≅ Z'.reindex k where
  hom := reindexMap e.hom k
  inv := reindexMap e.inv k
  hom_inv_id := by rw [← reindexMap_comp, e.hom_inv_id, reindexMap_id]
  inv_hom_id := by rw [← reindexMap_comp, e.inv_hom_id, reindexMap_id]

/-- Moving up by `k` degrees commutes with applying a functor degreewise. -/
def reindexMapHomologicalComplexIso {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] (Z : CochainComplex C ℤ) (k : ℤ) :
    reindex ((F.mapHomologicalComplex _).obj Z) k ≅ (F.mapHomologicalComplex _).obj (Z.reindex k) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by simp [reindex])

end Reindex

namespace SubmoduleFiltration

variable {R : Type u} [Ring R] {A : Type u} [CommRing A]
  {M K : CochainComplex (ModuleCat.{u} R) ℤ} (FM : SubmoduleFiltration M)
  (FK : SubmoduleFiltration K) (φ : M ⟶ K)
  (hφ : ∀ (k : ℕ) (n : ℤ), (FM.step k n).map (φ.f n).hom ≤ FK.step k n)

/-- The forgetful functor from `R`-modules to abelian groups, on complexes. -/
abbrev forgetAb (R : Type u) [Ring R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex _

/-- If the `k`-th graded pieces are `N ⊗ G_M`, `N ⊗ G_K` moved up by `k` degrees, compatibly
with `φ` and `N ⊗ g`, and `N ⊗ g` is a quasi-isomorphism, then `gr^k φ` is one. -/
private theorem quasiIso_gradedMap_of_tensor {GM GK : CochainComplex (ModuleCat.{u} A) ℤ}
    (g : GM ⟶ GK) (N : ModuleCat.{u} A) (k : ℕ)
    (αM : (forgetAb R).obj (FM.graded k) ≅ (forgetAb A).obj
      (reindex (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj GM) k))
    (αK : (forgetAb R).obj (FK.graded k) ≅ (forgetAb A).obj
      (reindex (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj GK) k))
    (hα : (forgetAb R).map (gradedMap FM FK φ hφ k) ≫ αK.hom =
      αM.hom ≫ (forgetAb A).map
        (reindexMap (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).map g) k))
    (h : QuasiIso (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) :
    QuasiIso (gradedMap FM FK φ hφ k) := by
  have : QuasiIso
      (reindexMap (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).map g) k) :=
    (quasiIso_reindexMap_iff _ _).2 h
  have : QuasiIso ((forgetAb R).map (gradedMap FM FK φ hφ k) ≫ αK.hom) := by
    rw [hα]
    infer_instance
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ _).1
    ((quasiIso_iff_comp_right _ αK.hom).1 this)

/-- **The comparison of filtered complexes whose graded pieces are tensor products with the
zeroth one.** Let `φ : M ⟶ K` respect two finite filtrations. Let `g : G_M ⟶ G_K` be a
quasi-isomorphism of bounded above complexes of flat `A`-modules, and suppose that for every `k`
there are an `A`-module `N_k` and isomorphisms of complexes of abelian groups between the `k`-th
graded pieces of `M` and `K` and the complexes `N_k ⊗_A G_M`, `N_k ⊗_A G_K` moved up by `k`
degrees, compatible with `φ` and `N_k ⊗ g`. Then `φ` is a quasi-isomorphism. -/
theorem quasiIso_of_graded_iso_tensor {GM GK : CochainComplex (ModuleCat.{u} A) ℤ}
    (g : GM ⟶ GK) [QuasiIso g] (a b : ℤ) [GM.IsStrictlyLE a] [GK.IsStrictlyLE b]
    [∀ n : ℤ, Module.Flat A (GM.X n)] [∀ n : ℤ, Module.Flat A (GK.X n)]
    (N : ℕ → ModuleCat.{u} A)
    (αM : ∀ k : ℕ, (forgetAb R).obj (FM.graded k) ≅ (forgetAb A).obj
      (reindex (((tensorLeft (N k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj GM) k))
    (αK : ∀ k : ℕ, (forgetAb R).obj (FK.graded k) ≅ (forgetAb A).obj
      (reindex (((tensorLeft (N k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj GK) k))
    (hα : ∀ k : ℕ, (forgetAb R).map (gradedMap FM FK φ hφ k) ≫ (αK k).hom =
      (αM k).hom ≫ (forgetAb A).map
        (reindexMap (((tensorLeft (N k)).mapHomologicalComplex (ComplexShape.up ℤ)).map g) k)) :
    QuasiIso φ := by
  refine quasiIso_of_quasiIso_gradedMap FM FK φ hφ fun k => ?_
  have h₁ : QuasiIso (((tensorLeft (N k)).mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
    KFlat.quasiIso_tensorLeft_map_of_flat (N k) g a b
  exact quasiIso_gradedMap_of_tensor FM FK φ hφ g (N k) k (αM k) (αK k) (hα k) h₁

/-- **The comparison of filtered complexes whose graded pieces are tensor products with the
zeroth one, for K-flat zeroth pieces.** As `quasiIso_of_graded_iso_tensor`, with the complexes
`G_M`, `G_K` modelling the zeroth graded pieces only assumed K-flat. -/
theorem quasiIso_of_graded_iso_tensor_of_kFlat {GM GK : CochainComplex (ModuleCat.{u} A) ℤ}
    (g : GM ⟶ GK) [QuasiIso g] (hGM : CochainComplex.KFlat.{u, u} GM)
    (hGK : CochainComplex.KFlat.{u, u} GK)
    (N : ℕ → ModuleCat.{u} A)
    (αM : ∀ k : ℕ, (forgetAb R).obj (FM.graded k) ≅ (forgetAb A).obj
      (reindex (((tensorLeft (N k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj GM) k))
    (αK : ∀ k : ℕ, (forgetAb R).obj (FK.graded k) ≅ (forgetAb A).obj
      (reindex (((tensorLeft (N k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj GK) k))
    (hα : ∀ k : ℕ, (forgetAb R).map (gradedMap FM FK φ hφ k) ≫ (αK k).hom =
      (αM k).hom ≫ (forgetAb A).map
        (reindexMap (((tensorLeft (N k)).mapHomologicalComplex (ComplexShape.up ℤ)).map g) k)) :
    QuasiIso φ := by
  refine quasiIso_of_quasiIso_gradedMap FM FK φ hφ fun k => ?_
  have h₁ : QuasiIso (((tensorLeft (N k)).mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
    KFlat.quasiIso_tensorLeft_map_of_kFlat (N k) g hGM hGK
  exact quasiIso_gradedMap_of_tensor FM FK φ hφ g (N k) k (αM k) (αK k) (hα k) h₁

end SubmoduleFiltration

end CochainComplex

end
