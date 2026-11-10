module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Homology.Additive

/-!
# Additive functors agreeing on an object agree on its finite sums

Let `F, G : 𝒜 ⥤ ℬ` be additive functors between preadditive categories and let `A` be an object
of `𝒜` with an isomorphism `e : F A ≅ G A` which is natural with respect to the endomorphisms
of `A`. Then `F` and `G` are isomorphic on every object `M` which is a finite sum of copies of
`A`, naturally in `M`: if `πᵢ : M ⟶ A` and `ιᵢ : A ⟶ M` satisfy `∑ᵢ πᵢ ≫ ιᵢ = 𝟙`, the comparison
is `∑ᵢ F πᵢ ≫ e ≫ G ιᵢ`, and its naturality with respect to `φ : M ⟶ N` comes from writing the
matrix coefficients `ιᵢ ≫ φ ≫ π'ⱼ` of `φ` as endomorphisms of `A`.

For `𝒜` the category of modules over a ring `Λ` and `A = Λ`, this compares two additive functors
on the finite free `Λ`-modules as soon as they agree on `Λ` together with the action of `Λ` on it
by multiplications.

## Main definitions

* `CategoryTheory.Functor.isoOfSummands`: the comparison `F M ≅ G M` at a finite sum of copies of
  `A`.
* `CategoryTheory.Functor.summandsOfIsIsoPiLift`: the inclusions `ιᵢ` attached to coordinates
  `πᵢ` presenting `M` as the product `∏ᵢ A`.

## Main results

* `CategoryTheory.Functor.homOfSummands_naturality`: the comparison is natural.
* `CategoryTheory.Functor.sum_comp_summandsOfIsIsoPiLift`: the coordinates and inclusions of a
  presentation as a product decompose the identity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {𝒜 ℬ : Type*} [Category 𝒜] [Preadditive 𝒜] [Category ℬ] [Preadditive ℬ]
  {F G : 𝒜 ⥤ ℬ} [F.Additive] [G.Additive] {A : 𝒜} (e : F.obj A ≅ G.obj A)
  (he : ∀ φ : A ⟶ A, F.map φ ≫ e.hom = e.hom ≫ G.map φ)

/-- The comparison `F M ⟶ G M` attached to maps `πᵢ : M ⟶ A` and `ιᵢ : A ⟶ M`:
`∑ᵢ F πᵢ ≫ e ≫ G ιᵢ`. -/
def homOfSummands {ι : Type*} [Fintype ι] {M : 𝒜} (π : ι → (M ⟶ A)) (j : ι → (A ⟶ M)) :
    F.obj M ⟶ G.obj M :=
  ∑ i, F.map (π i) ≫ e.hom ≫ G.map (j i)

/-- If `∑ᵢ πᵢ ≫ ιᵢ = 𝟙`, then `∑ᵢ πᵢ ≫ ιᵢ ≫ f = f` for every `f` out of `M`. -/
private theorem sum_comp_comp_eq {ι : Type*} [Fintype ι] {M X : 𝒜} (π : ι → (M ⟶ A))
    (j : ι → (A ⟶ M)) (hM : ∑ i, π i ≫ j i = 𝟙 M) (f : M ⟶ X) : ∑ i, π i ≫ j i ≫ f = f := by
  simp only [← Category.assoc, ← Preadditive.sum_comp, hM, Category.id_comp]

/-- If `∑ᵢ πᵢ ≫ ιᵢ = 𝟙`, then `∑ᵢ (f ≫ πᵢ) ≫ ιᵢ = f` for every `f` into `M`. -/
private theorem sum_comp_comp_eq' {ι : Type*} [Fintype ι] {M X : 𝒜} (π : ι → (M ⟶ A))
    (j : ι → (A ⟶ M)) (hM : ∑ i, π i ≫ j i = 𝟙 M) (f : X ⟶ M) :
    ∑ i, (f ≫ π i) ≫ j i = f := by
  simp only [Category.assoc, ← Preadditive.comp_sum, hM, Category.comp_id]

include he in
/-- **The comparison is natural.** If `∑ᵢ πᵢ ≫ ιᵢ = 𝟙` on `M` and `∑ⱼ π'ⱼ ≫ ι'ⱼ = 𝟙` on `N`, then
the comparisons at `M` and `N` intertwine `F φ` and `G φ` for every `φ : M ⟶ N`. -/
theorem homOfSummands_naturality {ι κ : Type*} [Fintype ι] [Fintype κ] {M N : 𝒜}
    (π : ι → (M ⟶ A)) (j : ι → (A ⟶ M)) (hM : ∑ i, π i ≫ j i = 𝟙 M)
    (π' : κ → (N ⟶ A)) (j' : κ → (A ⟶ N)) (hN : ∑ k, π' k ≫ j' k = 𝟙 N) (φ : M ⟶ N) :
    F.map φ ≫ homOfSummands e π' j' = homOfSummands e π j ≫ G.map φ := by
  have step : ∀ k, F.map (φ ≫ π' k) ≫ e.hom =
      ∑ i, F.map (π i) ≫ e.hom ≫ G.map (j i ≫ φ ≫ π' k) := fun k => by
    conv_lhs => rw [← sum_comp_comp_eq π j hM (φ ≫ π' k), F.map_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [F.map_comp, Category.assoc, he]
  have hG : ∀ i, G.map (j i ≫ φ) = ∑ k, G.map (j i ≫ φ ≫ π' k) ≫ G.map (j' k) := fun i => by
    conv_lhs => rw [← sum_comp_comp_eq' π' j' hN (j i ≫ φ), G.map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← G.map_comp]
    simp only [Category.assoc]
  calc F.map φ ≫ homOfSummands e π' j'
      = ∑ k, (F.map (φ ≫ π' k) ≫ e.hom) ≫ G.map (j' k) := by
        simp only [homOfSummands, Preadditive.comp_sum, F.map_comp, Category.assoc]
    _ = ∑ k, ∑ i, F.map (π i) ≫ e.hom ≫ G.map (j i ≫ φ ≫ π' k) ≫ G.map (j' k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [step, Preadditive.sum_comp]
        simp only [Category.assoc]
    _ = ∑ i, F.map (π i) ≫ e.hom ≫ G.map (j i ≫ φ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hG i, Preadditive.comp_sum, Preadditive.comp_sum]
    _ = homOfSummands e π j ≫ G.map φ := by
        simp only [homOfSummands, Preadditive.sum_comp, G.map_comp, Category.assoc]

include he in
omit [G.Additive] in
/-- **The comparison at a finite sum of copies of `A` is an isomorphism**, with inverse the
comparison for `e⁻¹`. -/
theorem homOfSummands_comp_homOfSummands {ι : Type*} [Fintype ι] {M : 𝒜}
    (π : ι → (M ⟶ A)) (j : ι → (A ⟶ M)) (hM : ∑ i, π i ≫ j i = 𝟙 M) :
    homOfSummands e π j ≫ homOfSummands e.symm π j = 𝟙 (F.obj M) := by
  have he' : ∀ φ : A ⟶ A, e.hom ≫ G.map φ ≫ e.inv = F.map φ := fun φ => by
    rw [← reassoc_of% he, Iso.hom_inv_id, Category.comp_id]
  calc homOfSummands e π j ≫ homOfSummands e.symm π j
      = ∑ i, ∑ k, F.map (π i) ≫ (e.hom ≫ G.map (j i ≫ π k) ≫ e.inv) ≫ F.map (j k) := by
        simp only [homOfSummands, Preadditive.sum_comp, Preadditive.comp_sum, Iso.symm_hom,
          Category.assoc, G.map_comp]
        exact Finset.sum_comm
    _ = ∑ i, ∑ k, F.map (π i ≫ j i ≫ π k ≫ j k) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [he', ← F.map_comp, ← F.map_comp]
        simp only [Category.assoc]
    _ = F.map ((∑ i, π i ≫ j i) ≫ ∑ k, π k ≫ j k) := by
        rw [Preadditive.sum_comp, F.map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Preadditive.comp_sum, F.map_sum]
        simp only [Category.assoc]
    _ = 𝟙 (F.obj M) := by rw [hM, Category.comp_id, F.map_id]

/-- **The comparison `F M ≅ G M` at a finite sum `M` of copies of `A`**, for maps
`πᵢ : M ⟶ A` and `ιᵢ : A ⟶ M` with `∑ᵢ πᵢ ≫ ιᵢ = 𝟙`. -/
def isoOfSummands {ι : Type*} [Fintype ι] {M : 𝒜} (π : ι → (M ⟶ A)) (j : ι → (A ⟶ M))
    (hM : ∑ i, π i ≫ j i = 𝟙 M) : F.obj M ≅ G.obj M where
  hom := homOfSummands e π j
  inv := homOfSummands e.symm π j
  hom_inv_id := homOfSummands_comp_homOfSummands e he π j hM
  inv_hom_id := homOfSummands_comp_homOfSummands (F := G) (G := F) e.symm
    (fun φ => by
      rw [Iso.symm_hom, ← cancel_epi e.hom, ← reassoc_of% he, Iso.hom_inv_id_assoc,
        Iso.hom_inv_id, Category.comp_id]) π j hM

/-- The forward map of `isoOfSummands` is `homOfSummands e π j`. -/
theorem isoOfSummands_hom {ι : Type*} [Fintype ι] {M : 𝒜} (π : ι → (M ⟶ A)) (j : ι → (A ⟶ M))
    (hM : ∑ i, π i ≫ j i = 𝟙 M) :
    (isoOfSummands e he π j hM).hom = homOfSummands e π j :=
  rfl

section Product

variable [HasFiniteProducts 𝒜]

/-- The inclusions `ιᵢ : A ⟶ M` attached to coordinates `πᵢ : M ⟶ A` which present `M` as the
finite product `∏ᵢ A`. -/
def summandsOfIsIsoPiLift {ι : Type*} [Fintype ι] [DecidableEq ι] {M : 𝒜} (π : ι → (M ⟶ A))
    [IsIso (Pi.lift π)] (i : ι) : A ⟶ M :=
  Pi.lift (fun k => if k = i then 𝟙 A else 0) ≫ CategoryTheory.inv (Pi.lift π)

/-- **Coordinates presenting `M` as a finite product of copies of `A` decompose its identity**,
together with the inclusions `summandsOfIsIsoPiLift`. -/
theorem sum_comp_summandsOfIsIsoPiLift {ι : Type*} [Fintype ι] [DecidableEq ι] {M : 𝒜}
    (π : ι → (M ⟶ A)) [IsIso (Pi.lift π)] :
    ∑ i, π i ≫ summandsOfIsIsoPiLift π i = 𝟙 M := by
  rw [← cancel_mono (Pi.lift π), Category.id_comp, Preadditive.sum_comp]
  refine Pi.hom_ext _ _ fun k => ?_
  simp only [summandsOfIsIsoPiLift, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    Preadditive.sum_comp, Pi.lift_comp_π]
  rw [Finset.sum_eq_single k (fun i _ hik => by rw [ite_eq_right (Ne.symm hik), Limits.comp_zero])
    (fun h => absurd (Finset.mem_univ k) h), ite_eq_left rfl, Category.comp_id]

end Product

section Complex

variable {ι : Type*} {c : ComplexShape ι}

/-- **The comparison of complexes** `F K ≅ G K` for a complex `K` each of whose terms is given as
a finite sum of copies of `A`: degreewise `CategoryTheory.Functor.isoOfSummands`, which
commutes with the differentials by `CategoryTheory.Functor.homOfSummands_naturality`. -/
def mapHomologicalComplexIsoOfSummands (K : HomologicalComplex 𝒜 c) (κ : ι → Type*)
    [∀ i, Fintype (κ i)] (π : ∀ i, κ i → (K.X i ⟶ A)) (j : ∀ i, κ i → (A ⟶ K.X i))
    (h : ∀ i, ∑ k, π i k ≫ j i k = 𝟙 (K.X i)) :
    (F.mapHomologicalComplex c).obj K ≅ (G.mapHomologicalComplex c).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => isoOfSummands e he (π i) (j i) (h i))
    (fun i i' _ => (homOfSummands_naturality e he (π i) (j i) (h i) (π i') (j i') (h i')
      (K.d i i')).symm)

/-- In degree `i`, the forward map of `mapHomologicalComplexIsoOfSummands` is
`homOfSummands e (π i) (j i)`. -/
theorem mapHomologicalComplexIsoOfSummands_hom_f (K : HomologicalComplex 𝒜 c) (κ : ι → Type*)
    [∀ i, Fintype (κ i)] (π : ∀ i, κ i → (K.X i ⟶ A)) (j : ∀ i, κ i → (A ⟶ K.X i))
    (h : ∀ i, ∑ k, π i k ≫ j i k = 𝟙 (K.X i)) (i : ι) :
    (mapHomologicalComplexIsoOfSummands e he K κ π j h).hom.f i = homOfSummands e (π i) (j i) :=
  rfl

include he in
/-- **The comparison of complexes is natural**, for every chain map between two complexes whose
terms are given as finite sums of copies of `A`. -/
theorem mapHomologicalComplexIsoOfSummands_hom_naturality (K L : HomologicalComplex 𝒜 c)
    (κ κ' : ι → Type*) [∀ i, Fintype (κ i)] [∀ i, Fintype (κ' i)]
    (π : ∀ i, κ i → (K.X i ⟶ A)) (j : ∀ i, κ i → (A ⟶ K.X i))
    (h : ∀ i, ∑ k, π i k ≫ j i k = 𝟙 (K.X i))
    (π' : ∀ i, κ' i → (L.X i ⟶ A)) (j' : ∀ i, κ' i → (A ⟶ L.X i))
    (h' : ∀ i, ∑ k, π' i k ≫ j' i k = 𝟙 (L.X i)) (φ : K ⟶ L) :
    (F.mapHomologicalComplex c).map φ ≫
        (mapHomologicalComplexIsoOfSummands e he L κ' π' j' h').hom =
      (mapHomologicalComplexIsoOfSummands e he K κ π j h).hom ≫
        (G.mapHomologicalComplex c).map φ := by
  ext i
  exact homOfSummands_naturality e he (π i) (j i) (h i) (π' i) (j' i) (h' i) (φ.f i)

end Complex

end CategoryTheory.Functor
