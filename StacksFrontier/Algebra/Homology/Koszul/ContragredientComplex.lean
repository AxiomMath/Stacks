module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.Perfect.Koszul

/-!
# Contragredient complexes of the truncated Koszul complexes

Let `A` be a commutative ring and `K` a nonnegatively graded chain complex of `A`-modules.
Applying `Hom_A(-, M)` termwise to `K` turns it into a nonnegatively graded cochain complex of
abelian groups, the *contragredient complex* of `K` with coefficients in `M`, whose differential
is precomposition with the differential of `K`. The construction is contravariant in `K` and
covariant in `M`.

Applied to the inverse system `I^•(f) ← I^•(f²) ← ⋯` of truncated Koszul complexes attached to a
finite family `f` in `A`, it produces a direct system of cochain complexes indexed by `ℕ`.

## Main definitions

* `Koszul.koszulHomComplex`: the contragredient cochain complex `Hom_A(K_•, M)`.
* `Koszul.koszulHomComplexMap`: its functoriality in the coefficient module.
* `Koszul.koszulHomComplexPrecomp`: its contravariant functoriality in the source complex.
* `Koszul.koszulHomDiagram`: the direct system obtained from the inverse system of truncated
  Koszul complexes on the powers of a finite family.
* `Koszul.koszulHomDiagramMap`: its functoriality in the coefficient module.
* `Koszul.koszulHomColimitMap`: the induced map of colimits of these direct systems.

## Main results

* `Koszul.koszulHomComplexPrecomp_naturality`: precomposition in the source and postcomposition
  in the target commute.

## References

* [Stacks Project, Tag 08CY](https://stacks.math.columbia.edu/tag/08CY)
* [Stacks Project, Tag 08D0](https://stacks.math.columbia.edu/tag/08D0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Koszul

universe u v w

variable {A : Type u} [CommRing A]

/-- The cochain complex obtained by applying `Hom_A(-, M)` to a chain complex.
Its differential is precomposition by the differential of the chain complex. -/
noncomputable def koszulHomComplex (K : ChainComplex (ModuleCat.{w} A) ℕ)
    (M : ModuleCat.{v} A) : CochainComplex AddCommGrpCat.{max w v} ℕ :=
  CochainComplex.of
    (fun n ↦ AddCommGrpCat.of (K.X n →ₗ[A] M))
    (fun n ↦ AddCommGrpCat.ofHom
      { toFun := fun t ↦ t.comp (K.d (n + 1) n).hom
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })
    (fun n ↦ by
      apply AddCommGrpCat.hom_ext
      ext t x
      change t ((K.d (n + 1 + 1) (n + 1) ≫ K.d (n + 1) n) x) = 0
      rw [K.d_comp_d]
      simp)

/-- The differential of the contragredient complex is precomposition with the differential of
the source complex. -/
theorem koszulHomComplex_d (K : ChainComplex (ModuleCat.{w} A) ℕ) (M : ModuleCat.{v} A)
    (n : ℕ) :
    (koszulHomComplex K M).d n (n + 1) =
      AddCommGrpCat.ofHom
        { toFun := fun (t : K.X n →ₗ[A] M) ↦ t.comp (K.d (n + 1) n).hom
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl } :=
  CochainComplex.of_d
    (fun n ↦ AddCommGrpCat.of (K.X n →ₗ[A] M))
    (fun n ↦ AddCommGrpCat.ofHom
      { toFun := fun t ↦ t.comp (K.d (n + 1) n).hom
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }) n

/-- A map of target modules induces a map of contragredient cochain complexes. -/
noncomputable def koszulHomComplexMap (K : ChainComplex (ModuleCat.{w} A) ℕ)
    {M N : ModuleCat.{v} A} (f : M ⟶ N) : koszulHomComplex K M ⟶ koszulHomComplex K N :=
  CochainComplex.ofHom
    (fun n ↦ AddCommGrpCat.ofHom
      { toFun := fun (t : K.X n →ₗ[A] M) ↦ f.hom.comp t
        map_zero' := LinearMap.comp_zero _
        map_add' := fun _ _ ↦ LinearMap.comp_add _ _ _ })
    (fun n ↦ by
      dsimp [koszulHomComplex]
      ext t : 2
      simp only [CochainComplex.of_d]
      rfl)

/-- Precomposition turns a map of chain complexes into a map of the associated
contragredient cochain complexes. -/
noncomputable def koszulHomComplexPrecomp
    {K L : ChainComplex (ModuleCat.{w} A) ℕ} (f : K ⟶ L) (M : ModuleCat.{v} A) :
    koszulHomComplex L M ⟶ koszulHomComplex K M :=
  CochainComplex.ofHom
    (fun n ↦ AddCommGrpCat.ofHom
      { toFun := fun (t : L.X n →ₗ[A] M) ↦ t.comp (f.f n).hom
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })
    (fun n ↦ by
      dsimp [koszulHomComplex]
      ext t : 2
      simp only [CochainComplex.of_d]
      ext x
      change t ((K.d (n + 1) n ≫ f.f n) x) =
        t ((f.f (n + 1) ≫ L.d (n + 1) n) x)
      rw [f.comm])

/-- Precomposition in the source and postcomposition in the target commute. -/
theorem koszulHomComplexPrecomp_naturality
    {K L : ChainComplex (ModuleCat.{w} A) ℕ} (h : K ⟶ L)
    {M N : ModuleCat.{v} A} (g : M ⟶ N) :
    koszulHomComplexPrecomp h M ≫ koszulHomComplexMap K g =
      koszulHomComplexMap L g ≫ koszulHomComplexPrecomp h N := by
  ext n t
  rfl

/-- Precomposition along the identity is the identity. -/
theorem koszulHomComplexPrecomp_id (K : ChainComplex (ModuleCat.{w} A) ℕ)
    (M : ModuleCat.{v} A) : koszulHomComplexPrecomp (𝟙 K) M = 𝟙 _ := by
  ext n : 2
  rfl

/-- Postcomposition with the identity is the identity. -/
theorem koszulHomComplexMap_id (K : ChainComplex (ModuleCat.{w} A) ℕ)
    (M : ModuleCat.{v} A) : koszulHomComplexMap K (𝟙 M) = 𝟙 _ := by
  ext n : 2
  rfl

/-- The direct system of contragredient complexes associated to the inverse system of Koszul
ideal complexes on powers of `f`; its stage `e` is the contragredient complex of the Koszul
ideal complex on the `(e + 1)`-st powers of `f`. -/
noncomputable def koszulHomDiagram {r : ℕ} (f : Fin r → A) (M : ModuleCat.{v} A) :
    ℕ ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ :=
  Functor.ofSequence (fun e ↦ koszulHomComplexPrecomp
    ((koszulIdealComplexSystem f).transition e) M)

/-- The successor transition of the direct system is precomposition with the transition of the
inverse system of truncated Koszul complexes. -/
theorem koszulHomDiagram_map_succ {r : ℕ} (f : Fin r → A) (M : ModuleCat.{v} A) (e : ℕ) :
    (koszulHomDiagram f M).map (homOfLE (Nat.le_add_right e 1)) =
      koszulHomComplexPrecomp ((koszulIdealComplexSystem f).transition e) M :=
  Functor.ofSequence_map_homOfLE_succ _ e

/-- The natural transformation of direct systems induced by a map of coefficient modules. -/
noncomputable def koszulHomDiagramMap {r : ℕ} (f : Fin r → A)
    {M N : ModuleCat.{v} A} (g : M ⟶ N) :
    koszulHomDiagram f M ⟶ koszulHomDiagram f N :=
  NatTrans.ofSequence
    (fun e ↦ koszulHomComplexMap (koszulIdealComplexPower f e) g)
    (fun e ↦ by
      rw [koszulHomDiagram_map_succ, koszulHomDiagram_map_succ]
      exact koszulHomComplexPrecomp_naturality
        ((koszulIdealComplexSystem f).transition e) g)

/-- The component of `koszulHomDiagramMap` at a stage. -/
theorem koszulHomDiagramMap_app {r : ℕ} (f : Fin r → A) {M N : ModuleCat.{v} A} (g : M ⟶ N)
    (e : ℕ) :
    (koszulHomDiagramMap f g).app e = koszulHomComplexMap (koszulIdealComplexPower f e) g :=
  rfl

/-- The map of colimits induced by a map of target modules. -/
noncomputable def koszulHomColimitMap {r : ℕ} (f : Fin r → A)
    {M N : ModuleCat.{v} A} (g : M ⟶ N) :
    colimit (koszulHomDiagram f M) ⟶ colimit (koszulHomDiagram f N) :=
  colim.map (koszulHomDiagramMap f g)

end Koszul
