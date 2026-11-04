module

public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.Exactness
public import StacksFrontier.Homology.AcyclicDimensionShifting
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopVanishing

/-!
# The multiplication pairing on the top cohomology of projective space

Let `A` be a ring, `n ≥ 1` and `ℙⁿ_A = Proj A[X₀, …, Xₙ]`. For an integer `d ≤ -n - 1` and
`k = -n - 1 - d`, multiplication by the monomials of degree `k` gives a map

`Hⁿ(ℙⁿ_A, 𝒪(d)) ⟶ ∏_{|α| = k} Hⁿ(ℙⁿ_A, 𝒪(-n-1)),   c ↦ (X^α · c)_α`,

and this map is bijective. The proof is by induction on `k`, using the Koszul complex of the
coordinates: its exactness and the vanishing of `Hᵠ(ℙⁿ_A, 𝒪(e))` for `q < n` and `e < 0` make
`0 ⟶ Hⁿ(𝒪(d)) ⟶ Hⁿ(𝒪(d+1))^{n+1} ⟶ Hⁿ(𝒪(d+2))^{binom(n+1,2)}` exact.

## Main results

In the namespace `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ProjectiveSpacePairing`:

* `eq_zero_of_mulX`: a class in `Hⁿ(𝒪(d))`, `d ≤ -n - 2`, killed by every coordinate vanishes.
* `exists_mulX_eq`: a compatible family in `Hⁿ(𝒪(d+1))` is the family of products of one class
  with the coordinates.
* `bijective_monomialPairing`: the multiplication map above is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjKoszulComplex Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ProjectiveSpacePairing

section Biproducts

variable {C : Type*} [Category C] [Preadditive C] {J : Type} [Fintype J] (f : J → C)
  [HasBiproduct f] (H : C ⥤ AddCommGrpCat.{u}) [H.Additive]

/-- Evaluation of a finite sum of morphisms of abelian groups. -/
theorem hom_sum_apply {X Y : AddCommGrpCat.{u}} {ι : Type*} (S : Finset ι) (φ : ι → (X ⟶ Y))
    (z : X) : (∑ s ∈ S, φ s).hom z = ∑ s ∈ S, (φ s).hom z := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

/-- An element of the image of a finite biproduct under an additive functor to abelian groups is
determined by its components. -/
theorem ext_biproduct {y y' : H.obj (⨁ f)}
    (h : ∀ s, (H.map (biproduct.π f s)).hom y = (H.map (biproduct.π f s)).hom y') : y = y' := by
  have htot : H.map (𝟙 (⨁ f)) = ∑ s, H.map (biproduct.π f s) ≫ H.map (biproduct.ι f s) := by
    rw [← biproduct.total, Functor.map_sum]
    simp only [Functor.map_comp]
  have hy : ∀ z : H.obj (⨁ f), z = ∑ s, (H.map (biproduct.ι f s)).hom
      ((H.map (biproduct.π f s)).hom z) := by
    intro z
    have := congrArg (fun φ => φ.hom z) htot
    simp only [CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id, AddMonoidHom.id_apply] at this
    refine this.trans ?_
    rw [hom_sum_apply]
    rfl
  rw [hy y, hy y']
  simp only [h]

/-- The components of the image of a sum of inclusions. -/
theorem π_sum_ι (z : ∀ s, H.obj (f s)) (t : J) :
    (H.map (biproduct.π f t)).hom (∑ s, (H.map (biproduct.ι f s)).hom (z s)) = z t := by
  classical
  rw [map_sum]
  rw [Finset.sum_eq_single t]
  · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, biproduct.ι_π_self,
      CategoryTheory.Functor.map_id]
    rfl
  · intro s _ hst
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, biproduct.ι_π_ne _ hst,
      Functor.map_zero]
    rfl
  · intro h
    exact absurd (Finset.mem_univ t) h

/-- The image of a finite biproduct under an additive functor to abelian groups is the product
of the images: an element is the same as the family of its components. -/
theorem bijective_biproduct_components :
    Function.Bijective (fun y : H.obj (⨁ f) => fun s => (H.map (biproduct.π f s)).hom y) :=
  ⟨fun _ _ h => ext_biproduct f H fun s => congrFun h s,
    fun z => ⟨∑ s, (H.map (biproduct.ι f s)).hom (z s), funext (π_sum_ι f H z)⟩⟩

/-- A finite biproduct of objects on which an additive functor vanishes is sent to zero. -/
theorem isZero_map_biproduct {D : Type*} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (h : ∀ s, IsZero (G.obj (f s))) : IsZero (G.obj (⨁ f)) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← G.map_id, ← biproduct.total, Functor.map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Functor.map_comp, (h s).eq_of_src (G.map (biproduct.ι f s)) 0, comp_zero]

end Biproducts

section Koszul

variable (A : Type u) [CommRing A] (m : ℕ)

/-- **`Hᵠ(ℙⁿ_A, 𝒪(e)) = 0` for `q < n` and `e < 0`**, `n = m + 1`. -/
theorem isZero_Hgroup_twistingSheaf_of_lt (e : ℤ) (he : e < 0) (q : ℕ) (hq : q < m + 1) :
    IsZero (Hgroup (projRingSheaf (polyGrading A (m + 1))) ⊤ q
      (twistingSheaf (polyGrading A (m + 1)) e)) := by
  have h0 : IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology A (m + 1) e q) :=
    Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology A (m + 1) e q (by omega)
  have h1 : IsZero (((Stacks.Cohomology.sectionsFunctor
      (AlgebraicGeometry.Proj (polyGrading A (m + 1))) ⊤).rightDerived q).obj
      (twistingSheaf (polyGrading A (m + 1)) e)) := by
    have hs : Subsingleton (Stacks.ProjectiveSpace.Cohomology.twistCohomology A (m + 1) e q) :=
      ModuleCat.subsingleton_of_isZero h0
    rw [ModuleCat.isZero_iff_subsingleton]
    exact hs
  exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (projRingSheaf (polyGrading A (m + 1))) ⊤ q (twistingSheaf (polyGrading A (m + 1)) e)).mp h1

/-- The degree `j` of a nonempty term of the Koszul complex on `m + 2` coordinates satisfies
`0 ≤ j ≤ m + 2`. -/
theorem card_le_of_koszulIndex {j : ℤ} (s : koszulIndex (m + 2) j) : 0 ≤ j ∧ j ≤ m + 2 := by
  have h1 := s.2
  have h2 : s.1.card ≤ m + 2 := (Finset.card_le_univ s.1).trans (by simp)
  omega

/-- The term of the Koszul complex in degree `j` is zero for `j < 0` or `j > n + 1`. -/
theorem isZero_koszulTerm_of_lt (a : ℤ) {j : ℤ} (hj : j < 0 ∨ m + 2 < j) :
    IsZero ((koszulComplex A (m + 1) a).X j) :=
  isZero_map_biproduct (koszulFamily A (m + 1) a j) (𝟭 _) fun s => by
    have := card_le_of_koszulIndex m s
    omega

/-- For `a ≤ -n - 2` and `q < n`, the group `Hᵠ(ℙⁿ_A, -)` of every term of the Koszul complex
starting at `𝒪(a)` vanishes. -/
theorem isZero_Hgroup_koszulTerm (a : ℤ) (ha : a + (m + 2) < 0) (j : ℤ) (q : ℕ)
    (hq : q < m + 1) :
    IsZero (Hgroup (projRingSheaf (polyGrading A (m + 1))) ⊤ q
      ((koszulComplex A (m + 1) a).X j)) :=
  isZero_map_biproduct (koszulFamily A (m + 1) a j) _ fun s => by
    have := card_le_of_koszulIndex m s
    exact isZero_Hgroup_twistingSheaf_of_lt A m (a + j) (by omega) q hq

/-- `Hⁿ(𝒪(a)) ⟶ Hⁿ(𝒪(a + 1))^{n+1}` is a monomorphism for `a ≤ -n - 2`. -/
theorem mono_Hfunctor_koszul_d (a : ℤ) (ha : a + (m + 2) < 0) :
    Mono ((Hfunctor (projRingSheaf (polyGrading A (m + 1))) ⊤ (m + 1)).map
      ((koszulComplex A (m + 1) a).d 0 1)) :=
  Stacks.Homology.AcyclicDimensionShifting.mono_rightDerived_map_d_zero
    (secF (projRingSheaf (polyGrading A (m + 1))) ⊤) (acyclic_koszulComplex A (m + 1) a) m
    (m + 3) (fun j hj => isZero_koszulTerm_of_lt A m a (Or.inr (by omega)))
    (fun j q hq => isZero_Hgroup_koszulTerm A m a ha j q hq)
    (isZero_koszulTerm_of_lt A m a (Or.inl (by omega)))

/-- `Hⁿ(𝒪(a)) ⟶ Hⁿ(𝒪(a + 1))^{n+1} ⟶ Hⁿ(𝒪(a + 2))^{binom(n+1,2)}` is exact for `a ≤ -n - 2`. -/
theorem exact_Hfunctor_koszul_d (a : ℤ) (ha : a + (m + 2) < 0) :
    (ShortComplex.mk ((Hfunctor (projRingSheaf (polyGrading A (m + 1))) ⊤ (m + 1)).map
      ((koszulComplex A (m + 1) a).d 0 1))
      ((Hfunctor (projRingSheaf (polyGrading A (m + 1))) ⊤ (m + 1)).map
        ((koszulComplex A (m + 1) a).d 1 2))
      ((Functor.map_comp _ _ _).symm.trans ((congrArg _
        ((koszulComplex A (m + 1) a).d_comp_d 0 1 2)).trans (Functor.map_zero _ _ _)))).Exact :=
  Stacks.Homology.AcyclicDimensionShifting.exact_rightDerived_map_d
    (secF (projRingSheaf (polyGrading A (m + 1))) ⊤) (acyclic_koszulComplex A (m + 1) a) m
    (m + 3) (fun j hj => isZero_koszulTerm_of_lt A m a (Or.inr (by omega)))
    (fun j q hq => isZero_Hgroup_koszulTerm A m a ha j q hq)
    (isZero_koszulTerm_of_lt A m a (Or.inl (by omega)))

end Koszul

section Elements

variable {A : Type u} [CommRing A] {m : ℕ}

/-- The index of the summand of the zeroth term of the Koszul complex. -/
def emptyIndex : koszulIndex (m + 1 + 1) 0 := ⟨∅, by simp⟩

/-- The index of the summand of the first term of the Koszul complex attached to a coordinate. -/
def singleIndex (i : Fin (m + 1 + 1)) : koszulIndex (m + 1 + 1) 1 := ⟨{i}, by simp⟩

/-- `emptyIndex` is the only index of the zeroth term of the Koszul complex. -/
theorem eq_emptyIndex (s : koszulIndex (m + 1 + 1) 0) : s = emptyIndex :=
  Subtype.ext (Finset.card_eq_zero.mp (by have := s.2; omega))

/-- Every index of the first term of the Koszul complex is `singleIndex i` for a coordinate `i`. -/
theorem exists_eq_singleIndex (t : koszulIndex (m + 1 + 1) 1) : ∃ i, t = singleIndex i := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by have := t.2; omega : t.1.card = 1)
  exact ⟨i, Subtype.ext hi⟩

/-- The Koszul sign of inserting a coordinate into the empty set is `1`. -/
theorem koszulSign_empty (i : Fin (m + 1 + 1)) : koszulSign i ∅ = 1 := by
  simp [koszulSign]

/-- The component of the first Koszul differential from `emptyIndex` to `singleIndex i` is
multiplication by `Xᵢ`. -/
theorem koszulCoeff_emptyIndex_singleIndex (a : ℤ) (i : Fin (m + 1 + 1)) :
    koszulCoeff A (m + 1) a 0 emptyIndex (singleIndex i) =
      twistMulX A (m + 1) i (a + 0) (a + (0 + 1)) (by ring) := by
  have hs : koszulSign i (emptyIndex (m := m)).1 = 1 := koszulSign_empty i
  have h := koszulCoeff_eq A (m + 1) a 0 emptyIndex (singleIndex i) (i := i)
    (Finset.notMem_empty i) (LawfulSingleton.insert_empty_eq i).symm
  exact h.trans ((congrArg (fun z : ℤ => z • twistMulX A (m + 1) i (a + 0) (a + (0 + 1))
    (by ring)) hs).trans (one_zsmul _))

variable (A m)

/-- `Hⁿ(ℙⁿ_A, -)` with `n = m + 1`. -/
abbrev topH : SheafOfModules.{u} (projRingSheaf (polyGrading A (m + 1))) ⥤ AddCommGrpCat.{u} :=
  Hfunctor (projRingSheaf (polyGrading A (m + 1))) ⊤ (m + 1)

variable {A m}

/-- On top cohomology, the projection of an element included into a summand of a term of the
Koszul complex is the element itself. -/
private theorem topH_π_ι_self (a j : ℤ) (l : koszulIndex (m + 1 + 1) j)
    (x : (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) (a + j))) :
    ((topH A m).map (biproduct.π (koszulFamily A (m + 1) a j) l)).hom
      (((topH A m).map (biproduct.ι (koszulFamily A (m + 1) a j) l)).hom x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, biproduct.ι_π_self,
    CategoryTheory.Functor.map_id]
  rfl

/-- On top cohomology, the `(l, u)` component of a Koszul differential is induced by
`koszulCoeff A (m + 1) a j l u`. -/
private theorem topH_π_koszulDiff_ι (a j : ℤ) (l : koszulIndex (m + 1 + 1) j)
    (u : koszulIndex (m + 1 + 1) (j + 1))
    (x : (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) (a + j))) :
    ((topH A m).map (biproduct.π (koszulFamily A (m + 1) a (j + 1)) u)).hom
      (((topH A m).map ((koszulComplex A (m + 1) a).d j (j + 1))).hom
        (((topH A m).map (biproduct.ι (koszulFamily A (m + 1) a j) l)).hom x)) =
      ((topH A m).map (koszulCoeff A (m + 1) a j l u)).hom x := by
  have h := congrArg (fun φ => ((topH A m).map φ).hom x)
    (biproduct_ι_comp_koszulDiff_comp_π A (m + 1) a j l u)
  refine Eq.trans ?_ h
  rw [koszulComplex_d]
  simp only [Functor.map_comp]
  rfl

/-- **A top cohomology class of `𝒪(d)`, `d ≤ -n - 2`, killed by every coordinate vanishes.** -/
theorem eq_zero_of_mulX {d e : ℤ} (he : 1 + d = e) (hd : d + (m + 2) < 0)
    (c : (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) d))
    (hc : ∀ i, ((topH A m).map (twistMulX A (m + 1) i d e he)).hom c = 0) : c = 0 := by
  obtain ⟨a, rfl⟩ : ∃ a, d = a + 0 := ⟨d, (add_zero d).symm⟩
  obtain rfl : e = a + (0 + 1) := by omega
  have hinj := (AddCommGrpCat.mono_iff_injective _).1 (mono_Hfunctor_koszul_d A m a (by omega))
  let ι₀ := biproduct.ι (koszulFamily A (m + 1) a 0) (emptyIndex (m := m))
  let π₀ := biproduct.π (koszulFamily A (m + 1) a 0) (emptyIndex (m := m))
  have hc' : ((topH A m).map ((koszulComplex A (m + 1) a).d 0 1)).hom
      (((topH A m).map ι₀).hom c) = 0 := by
    refine ext_biproduct (koszulFamily A (m + 1) a 1) (topH A m) fun t => ?_
    obtain ⟨i, rfl⟩ := exists_eq_singleIndex t
    exact (topH_π_koszulDiff_ι a 0 emptyIndex (singleIndex i) c).trans
      ((congrArg (fun φ => ((topH A m).map φ).hom c) (koszulCoeff_emptyIndex_singleIndex a i)).trans
        ((hc i).trans (map_zero _).symm))
  have h0 : ((topH A m).map ι₀).hom c = 0 := hinj (hc'.trans (map_zero _).symm)
  exact (topH_π_ι_self a 0 emptyIndex c).symm.trans ((congrArg _ h0).trans (map_zero _))

/-- The coordinate of a one-element subset. -/
def singleIndexElt (t : koszulIndex (m + 1 + 1) 1) : Fin (m + 1 + 1) :=
  (exists_eq_singleIndex t).choose

/-- `singleIndex` is a left inverse of `singleIndexElt`. -/
theorem singleIndex_singleIndexElt (t : koszulIndex (m + 1 + 1) 1) :
    singleIndex (singleIndexElt t) = t :=
  (exists_eq_singleIndex t).choose_spec.symm

/-- `singleIndexElt` is a left inverse of `singleIndex`. -/
theorem singleIndexElt_singleIndex (i : Fin (m + 1 + 1)) : singleIndexElt (singleIndex i) = i :=
  Finset.singleton_inj.mp (congrArg Subtype.val (singleIndex_singleIndexElt (singleIndex i)))

/-- `singleIndex` is injective. -/
theorem singleIndex_injective : Function.Injective (singleIndex (m := m)) := fun _ _ h =>
  Finset.singleton_inj.mp (congrArg Subtype.val h)

/-- Evaluation of an integer multiple of a morphism of abelian groups. -/
theorem zsmul_hom_apply {X Y : AddCommGrpCat.{u}} (z : ℤ) (φ : X ⟶ Y) (x : X) :
    (z • φ).hom x = z • φ.hom x :=
  rfl

/-- For `u = {j, i}` with `j ≠ i`, the component of the second Koszul differential from
`singleIndex i` to `u` is `koszulSign j {i}` times multiplication by `Xⱼ`. -/
theorem koszulCoeff_singleIndex_of_mem (a : ℤ) (u : koszulIndex (m + 1 + 1) 2)
    {i j : Fin (m + 1 + 1)} (hij : j ≠ i) (hu : u.1 = insert j {i}) :
    koszulCoeff A (m + 1) a 1 (singleIndex i) u =
      koszulSign j {i} • twistMulX A (m + 1) j (a + 1) (a + (1 + 1)) (by ring) :=
  koszulCoeff_eq A (m + 1) a 1 (singleIndex i) u (i := j)
    (fun h => hij (Finset.mem_singleton.mp h)) hu

/-- The component of the second Koszul differential from `l` to `u` vanishes when the coordinate
of `l` does not lie in `u`. -/
theorem koszulCoeff_singleIndex_of_notMem (a : ℤ) (u : koszulIndex (m + 1 + 1) 2)
    (l : koszulIndex (m + 1 + 1) 1) (hl : singleIndexElt l ∉ u.1) :
    koszulCoeff A (m + 1) a 1 l u = 0 := by
  refine koszulCoeff_eq_zero A (m + 1) a 1 l u fun x _ hx => hl ?_
  rw [hx]
  have h2 : singleIndexElt l ∈ l.1 :=
    (congrArg (fun t : koszulIndex (m + 1 + 1) 1 => singleIndexElt l ∈ t.1)
      (singleIndex_singleIndexElt l)).mp (Finset.mem_singleton_self _)
  exact Finset.mem_insert_of_mem h2

/-- On top cohomology, the component of the second Koszul differential from `l` to `u` sends
every class to zero when the coordinate of `l` does not lie in `u`. -/
theorem topH_map_koszulCoeff_eq_zero (a : ℤ) (u : koszulIndex (m + 1 + 1) 2)
    (l : koszulIndex (m + 1 + 1) 1) (hl : singleIndexElt l ∉ u.1)
    (x : (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) (a + 1))) :
    ((topH A m).map (koszulCoeff A (m + 1) a 1 l u)).hom x = 0 := by
  rw [koszulCoeff_singleIndex_of_notMem a u l hl, Functor.map_zero]
  rfl

/-- The family `(cᵢ)` placed in the summands of the first term of the Koszul complex. -/
def koszulOneElement (a : ℤ)
    (c : Fin (m + 1 + 1) → (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) (a + 1))) :
    (topH A m).obj ((koszulComplex A (m + 1) a).X 1) :=
  ∑ l, ((topH A m).map (biproduct.ι (koszulFamily A (m + 1) a 1) l)).hom (c (singleIndexElt l))

/-- The component of `koszulOneElement a c` at the index `t` is `c` at the coordinate of `t`. -/
theorem π_koszulOneElement (a : ℤ)
    (c : Fin (m + 1 + 1) → (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) (a + 1)))
    (t : koszulIndex (m + 1 + 1) 1) :
    ((topH A m).map (biproduct.π (koszulFamily A (m + 1) a 1) t)).hom (koszulOneElement a c) =
      c (singleIndexElt t) :=
  π_sum_ι (koszulFamily A (m + 1) a 1) (topH A m) (fun l => c (singleIndexElt l)) t

/-- For a compatible family `(cᵢ)` of top cohomology classes, `Xⱼ cᵢ = Xᵢ cⱼ`, and
`u = {i, j}`, the two components of the second Koszul differential landing in `u` cancel. -/
private theorem topH_map_koszulCoeff_pair_add_eq_zero (a : ℤ) (hf : 1 + (a + 1) = a + (1 + 1))
    (c : Fin (m + 1 + 1) → (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) (a + 1)))
    (hc : ∀ i j, ((topH A m).map (twistMulX A (m + 1) j (a + 1) (a + (1 + 1)) hf)).hom (c i) =
      ((topH A m).map (twistMulX A (m + 1) i (a + 1) (a + (1 + 1)) hf)).hom (c j))
    (u : koszulIndex (m + 1 + 1) 2) {i j : Fin (m + 1 + 1)} (hij : i ≠ j) (hu : u.1 = {i, j}) :
    ((topH A m).map (koszulCoeff A (m + 1) a 1 (singleIndex i) u)).hom
        (c (singleIndexElt (singleIndex i))) +
      ((topH A m).map (koszulCoeff A (m + 1) a 1 (singleIndex j) u)).hom
        (c (singleIndexElt (singleIndex j))) = 0 := by
  have ei : (topH A m).map (koszulCoeff A (m + 1) a 1 (singleIndex i) u) =
      koszulSign j {i} • (topH A m).map (twistMulX A (m + 1) j (a + 1) (a + (1 + 1)) (by ring)) :=
    (congrArg (topH A m).map (koszulCoeff_singleIndex_of_mem a u (Ne.symm hij)
      (by rw [hu, Finset.pair_comm]))).trans (Functor.map_zsmul _)
  have ej : (topH A m).map (koszulCoeff A (m + 1) a 1 (singleIndex j) u) =
      koszulSign i {j} • (topH A m).map (twistMulX A (m + 1) i (a + 1) (a + (1 + 1)) (by ring)) :=
    (congrArg (topH A m).map (koszulCoeff_singleIndex_of_mem a u hij (by rw [hu]))).trans
      (Functor.map_zsmul _)
  have hs := koszulSign_pair_add_eq_zero (s := ∅) hij (Finset.notMem_empty i)
    (Finset.notMem_empty j)
  rw [koszulSign_empty, koszulSign_empty, one_mul, one_mul,
    show insert i (∅ : Finset (Fin (m + 1 + 1))) = {i} from
      LawfulSingleton.insert_empty_eq i,
    show insert j (∅ : Finset (Fin (m + 1 + 1))) = {j} from
      LawfulSingleton.insert_empty_eq j] at hs
  calc ((topH A m).map (koszulCoeff A (m + 1) a 1 (singleIndex i) u)).hom
        (c (singleIndexElt (singleIndex i))) +
      ((topH A m).map (koszulCoeff A (m + 1) a 1 (singleIndex j) u)).hom
        (c (singleIndexElt (singleIndex j)))
      = koszulSign j {i} •
          ((topH A m).map (twistMulX A (m + 1) j (a + 1) (a + (1 + 1)) hf)).hom (c i) +
        koszulSign i {j} •
          ((topH A m).map (twistMulX A (m + 1) i (a + 1) (a + (1 + 1)) hf)).hom (c j) := by
        have hci : c (singleIndexElt (singleIndex i)) = c i :=
          congrArg c (singleIndexElt_singleIndex i)
        have hcj : c (singleIndexElt (singleIndex j)) = c j :=
          congrArg c (singleIndexElt_singleIndex j)
        exact congrArg₂ (· + ·)
          ((congrArg (fun φ => φ.hom (c (singleIndexElt (singleIndex i)))) ei).trans
            (congrArg (fun w => koszulSign j {i} •
              ((topH A m).map (twistMulX A (m + 1) j (a + 1) (a + (1 + 1)) hf)).hom w) hci))
          ((congrArg (fun φ => φ.hom (c (singleIndexElt (singleIndex j)))) ej).trans
            (congrArg (fun w => koszulSign i {j} •
              ((topH A m).map (twistMulX A (m + 1) i (a + 1) (a + (1 + 1)) hf)).hom w) hcj))
    _ = (koszulSign j {i} + koszulSign i {j}) •
          ((topH A m).map (twistMulX A (m + 1) i (a + 1) (a + (1 + 1)) hf)).hom (c j) :=
        (congrArg (fun w => koszulSign j {i} • w + koszulSign i {j} •
          ((topH A m).map (twistMulX A (m + 1) i (a + 1) (a + (1 + 1)) hf)).hom (c j))
            (hc i j)).trans (add_zsmul _ _ _).symm
    _ = 0 := (congrArg (fun z : ℤ => z •
          ((topH A m).map (twistMulX A (m + 1) i (a + 1) (a + (1 + 1)) hf)).hom (c j)) hs).trans
          (zero_zsmul _)

/-- For a compatible family `(cᵢ)` of top cohomology classes, `Xⱼ cᵢ = Xᵢ cⱼ`, the second
Koszul differential kills `koszulOneElement a c`. -/
theorem d_koszulOneElement (a : ℤ) (hf : 1 + (a + 1) = a + (1 + 1))
    (c : Fin (m + 1 + 1) → (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) (a + 1)))
    (hc : ∀ i j, ((topH A m).map (twistMulX A (m + 1) j (a + 1) (a + (1 + 1)) hf)).hom (c i) =
      ((topH A m).map (twistMulX A (m + 1) i (a + 1) (a + (1 + 1)) hf)).hom (c j)) :
    ((topH A m).map ((koszulComplex A (m + 1) a).d 1 2)).hom (koszulOneElement a c) = 0 := by
  classical
  set y := koszulOneElement a c
  refine ext_biproduct (koszulFamily A (m + 1) a 2) (topH A m) fun u => ?_
  obtain ⟨i, j, hij, hu⟩ := Finset.card_eq_two.mp (by have := u.2; omega : u.1.card = 2)
  refine Eq.trans ?_ (map_zero _).symm
  have hsum : ((topH A m).map (biproduct.π (koszulFamily A (m + 1) a 2) u)).hom
      (((topH A m).map ((koszulComplex A (m + 1) a).d 1 2)).hom y) =
      ∑ l, ((topH A m).map (koszulCoeff A (m + 1) a 1 l u)).hom (c (singleIndexElt l)) :=
    (congrArg _ (map_sum _ _ _)).trans ((map_sum _ _ _).trans
      (Finset.sum_congr rfl fun l _ => topH_π_koszulDiff_ι a 1 l u _))
  refine hsum.trans ?_
  refine (Fintype.sum_eq_add (singleIndex i) (singleIndex j)
    (fun h => hij (singleIndex_injective h)) fun l hl => ?_).trans ?_
  · have hl' : singleIndexElt l ∉ u.1 := by
      rw [hu]
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hl.1 (by rw [← h, singleIndex_singleIndexElt])
      · exact hl.2 (by rw [← Finset.mem_singleton.mp h, singleIndex_singleIndexElt])
    exact topH_map_koszulCoeff_eq_zero a u l hl' _
  · exact topH_map_koszulCoeff_pair_add_eq_zero a hf c hc u hij hu

/-- On top cohomology, multiplying the `emptyIndex` component of a class by `Xᵢ` gives the
`singleIndex i` component of its image under the first Koszul differential. -/
theorem topH_map_twistMulX_π_emptyIndex (a : ℤ) (he : 1 + (a + 0) = a + 1)
    (i : Fin (m + 1 + 1)) (x' : (topH A m).obj ((koszulComplex A (m + 1) a).X 0)) :
    ((topH A m).map (twistMulX A (m + 1) i (a + 0) (a + 1) he)).hom
        (((topH A m).map (biproduct.π (koszulFamily A (m + 1) a 0) emptyIndex)).hom x') =
      ((topH A m).map (biproduct.π (koszulFamily A (m + 1) a 1) (singleIndex i))).hom
        (((topH A m).map ((koszulComplex A (m + 1) a).d 0 1)).hom x') := by
  let ι₀ := biproduct.ι (koszulFamily A (m + 1) a 0) (emptyIndex (m := m))
  let π₀ := biproduct.π (koszulFamily A (m + 1) a 0) (emptyIndex (m := m))
  have hx'' : (((topH A m).map ι₀).hom (((topH A m).map π₀).hom x')) = x' := by
    refine ext_biproduct (koszulFamily A (m + 1) a 0) (topH A m) fun s => ?_
    obtain rfl := eq_emptyIndex s
    exact topH_π_ι_self a 0 emptyIndex _
  refine (congrArg (fun φ => ((topH A m).map φ).hom (((topH A m).map π₀).hom x'))
    (koszulCoeff_emptyIndex_singleIndex a i)).symm.trans ?_
  conv_rhs => rw [← hx'']
  exact (topH_π_koszulDiff_ι a 0 emptyIndex (singleIndex i) _).symm

/-- **A compatible family of top cohomology classes of `𝒪(d+1)`, `d ≤ -n - 2`, is the family of
products of one class of `𝒪(d)` with the coordinates.** -/
theorem exists_mulX_eq {d e f : ℤ} (he : 1 + d = e) (hf : 1 + e = f) (hd : d + (m + 2) < 0)
    (c : Fin (m + 1 + 1) → (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) e))
    (hc : ∀ i j, ((topH A m).map (twistMulX A (m + 1) j e f hf)).hom (c i) =
      ((topH A m).map (twistMulX A (m + 1) i e f hf)).hom (c j)) :
    ∃ x, ∀ i, ((topH A m).map (twistMulX A (m + 1) i d e he)).hom x = c i := by
  obtain ⟨a, rfl⟩ : ∃ a, d = a + 0 := ⟨d, (add_zero d).symm⟩
  obtain rfl : e = a + 1 := by omega
  obtain rfl : f = a + (1 + 1) := by omega
  have hex := exact_Hfunctor_koszul_d A m a (by omega)
  rw [ShortComplex.ab_exact_iff] at hex
  obtain ⟨x', hx'⟩ := hex (koszulOneElement a c) (d_koszulOneElement a hf c hc)
  refine ⟨((topH A m).map (biproduct.π (koszulFamily A (m + 1) a 0) emptyIndex)).hom x',
    fun i => ?_⟩
  rw [topH_map_twistMulX_π_emptyIndex a he i x']
  refine (congrArg (fun w => ((topH A m).map (biproduct.π (koszulFamily A (m + 1) a 1)
    (singleIndex i))).hom w) hx').trans ?_
  exact (π_koszulOneElement a c (singleIndex i)).trans (congrArg c (singleIndexElt_singleIndex i))

end Elements


section Pairing

variable {A : Type u} [CommRing A] {m : ℕ}

/-- The exponent vectors of the monomials of degree `k` in `X₀, …, Xₙ`. -/
abbrev Monomials (m k : ℕ) := {α : Fin (m + 1 + 1) →₀ ℕ // α.degree = k}

/-- The monomial `X^α`, as a homogeneous element of degree `k`. -/
def monomialElt {k : ℕ} (α : Monomials m k) : polyGrading A (m + 1) k :=
  ⟨MvPolynomial.monomial α.1 1,
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_monomial 1 α.2)⟩

/-- **Multiplication by `X^α`**, `𝒪(d) ⟶ 𝒪(e)` for `e = k + d`. -/
def mulMonomial {k : ℕ} (α : Monomials m k) (d e : ℤ) (he : (k : ℤ) + d = e) :
    twistingSheaf (polyGrading A (m + 1)) d ⟶ twistingSheaf (polyGrading A (m + 1)) e :=
  twistMulLeftIntOf (polyGrading A (m + 1)) (monomialElt α) d e he

/-- `α + eᵢ`, a monomial of degree `k + 1`. -/
def Monomials.addSingle {k : ℕ} (α : Monomials m k) (i : Fin (m + 1 + 1)) :
    Monomials m (k + 1) :=
  ⟨α.1 + Finsupp.single i 1, by rw [map_add, α.2, Finsupp.degree_single]⟩

/-- Multiplication by `Xᵢ` followed by multiplication by `X^β` is multiplication by
`X^(β + eᵢ)`. -/
theorem mulMonomial_comp_twistMulX {k : ℕ} (β : Monomials m k) (i : Fin (m + 1 + 1))
    (d e g : ℤ) (he : 1 + d = e) (hg : (k : ℤ) + e = g) :
    twistMulX A (m + 1) i d e he ≫ mulMonomial β e g hg =
      mulMonomial (β.addSingle i) d g (by push_cast; omega) := by
  have he' : ((1 : ℕ) : ℤ) + d = e := by rw [Nat.cast_one]; exact he
  refine (twistMulLeftIntOf_comp (polyGrading A (m + 1)) ⟨MvPolynomial.X i, X_mem_one A (m + 1) i⟩
    (monomialElt β) d e g he' hg).trans ?_
  refine congrArg (fun x : polyGrading A (m + 1) (k + 1) =>
    twistMulLeftIntOf (polyGrading A (m + 1)) x d g _) (Subtype.ext ?_)
  change MvPolynomial.monomial β.1 (1 : A) * MvPolynomial.X i =
    MvPolynomial.monomial (β.1 + Finsupp.single i 1) 1
  rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]

/-- Multiplication by the monomial of degree `0` is the identity of `𝒪(d)`. -/
theorem mulMonomial_zero (d : ℤ) (he : ((0 : ℕ) : ℤ) + d = d)
    (α : Monomials m 0) : mulMonomial (A := A) α d d he = 𝟙 _ := by
  have hα : α.1 = 0 := (Finsupp.degree_eq_zero_iff _).mp α.2
  have hφ : LinearMap.mulLeft (MvPolynomial (Fin (m + 1 + 1)) A)
      ((monomialElt (A := A) α : polyGrading A (m + 1) 0) : MvPolynomial (Fin (m + 1 + 1)) A) =
      LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    change MvPolynomial.monomial α.1 1 * x = x
    rw [hα, MvPolynomial.monomial_zero', MvPolynomial.C_1, one_mul]
  unfold mulMonomial twistMulLeftIntOf
  rw [← Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_id]
  congr 1

/-- Every element of a zero abelian group is zero. -/
theorem eq_zero_of_isZero {X : AddCommGrpCat.{u}} (h : IsZero X) (x : X) : x = 0 := by
  have := congrArg (fun φ : X ⟶ X => φ.hom x) ((IsZero.iff_id_eq_zero X).1 h)
  exact this

variable (A m) in
/-- **The multiplication pairing on the top cohomology of `𝒪(d)`**, `k = -n - 1 - d`:
`c ↦ (X^α · c)_α`. -/
def monomialPairing (k : ℕ) (d : ℤ) (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1)
    (c : (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) d)) :
    Monomials m k →
      (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) (-((m + 1 : ℕ) : ℤ) - 1)) :=
  fun α => ((topH A m).map (mulMonomial α d _ hd)).hom c

/-- The multiplication pairing commutes with subtraction. -/
theorem monomialPairing_add (k : ℕ) (d : ℤ) (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1)
    (c c' : (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) d)) :
    monomialPairing A m k d hd (c - c') =
      monomialPairing A m k d hd c - monomialPairing A m k d hd c' :=
  funext fun _ => map_sub _ _ _

/-- The `β`-component of the pairing of `Xᵢ · c` is the `(β + eᵢ)`-component of the pairing of
`c`. -/
theorem monomialPairing_twistMulX (k : ℕ) (d : ℤ)
    (hd : ((k + 1 : ℕ) : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1)
    (hd' : (k : ℤ) + (d + 1) = -((m + 1 : ℕ) : ℤ) - 1) (i : Fin (m + 1 + 1))
    (c : (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) d)) (β : Monomials m k) :
    monomialPairing A m k (d + 1) hd'
        (((topH A m).map (twistMulX A (m + 1) i d (d + 1) (by ring))).hom c) β =
      monomialPairing A m (k + 1) d hd c (β.addSingle i) := by
  unfold monomialPairing
  rw [← mulMonomial_comp_twistMulX β i d (d + 1) _ (by ring) hd', Functor.map_comp]
  rfl

/-- Every monomial of degree `k + 1` is `β + eᵢ` for a monomial `β` of degree `k`. -/
theorem exists_eq_addSingle {k : ℕ} (α : Monomials m (k + 1)) :
    ∃ (i : Fin (m + 1 + 1)) (β : Monomials m k), α = β.addSingle i := by
  have hne : α.1 ≠ 0 := by
    intro h
    have := α.2
    rw [h, map_zero] at this
    omega
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  have hle : Finsupp.single i 1 ≤ α.1 := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hi
  have hsum : α.1 - Finsupp.single i 1 + Finsupp.single i 1 = α.1 := tsub_add_cancel_of_le hle
  refine ⟨i, ⟨α.1 - Finsupp.single i 1, ?_⟩, Subtype.ext hsum.symm⟩
  have h := α.2
  rw [← hsum, map_add, Finsupp.degree_single] at h
  omega

/-- `(γ + eⱼ) + eᵢ = (γ + eᵢ) + eⱼ`. -/
theorem addSingle_comm {k : ℕ} (γ : Monomials m k) (i j : Fin (m + 1 + 1)) :
    (γ.addSingle j).addSingle i = (γ.addSingle i).addSingle j :=
  Subtype.ext (by simp only [Monomials.addSingle]; abel)

/-- For `k = 0`, the pairing sends `c` to `c` at the unique monomial of degree `0`. -/
theorem monomialPairing_zero (d : ℤ) (hd : ((0 : ℕ) : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1)
    (c : (topH A m).obj (twistingSheaf (polyGrading A (m + 1)) d)) (α : Monomials m 0) :
    HEq (monomialPairing A m 0 d hd c α) c := by
  obtain rfl : d = -((m + 1 : ℕ) : ℤ) - 1 := by omega
  unfold monomialPairing
  rw [mulMonomial_zero, CategoryTheory.Functor.map_id]
  rfl

/-- **The multiplication pairing is injective.** -/
theorem injective_monomialPairing (k : ℕ) :
    ∀ (d : ℤ) (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1),
      Function.Injective (monomialPairing A m k d hd) := by
  induction k with
  | zero =>
    intro d hd c c' h
    have h0 := congrFun h ⟨0, map_zero _⟩
    exact eq_of_heq ((monomialPairing_zero d hd c _).symm.trans
      ((heq_of_eq h0).trans (monomialPairing_zero d hd c' _)))
  | succ k ih =>
    intro d hd c c' h
    have hd' : (k : ℤ) + (d + 1) = -((m + 1 : ℕ) : ℤ) - 1 := by push_cast at hd ⊢; omega
    have hz : monomialPairing A m (k + 1) d hd (c - c') = 0 := by
      rw [monomialPairing_add, h, sub_self]
    have hX : ∀ i, ((topH A m).map (twistMulX A (m + 1) i d (d + 1) (by ring))).hom
        (c - c') = 0 := by
      intro i
      refine ih (d + 1) hd' ?_
      refine funext fun β => ?_
      rw [monomialPairing_twistMulX k d hd hd' i (c - c') β, hz]
      exact (map_zero ((topH A m).map (mulMonomial β (d + 1) _ hd')).hom).symm
    exact sub_eq_zero.mp (eq_zero_of_mulX (by ring) (by push_cast at hd; omega) (c - c') hX)

/-- **The multiplication pairing is surjective.** -/
theorem surjective_monomialPairing (k : ℕ) :
    ∀ (d : ℤ) (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1),
      Function.Surjective (monomialPairing A m k d hd) := by
  induction k with
  | zero =>
    intro d hd f
    obtain rfl : d = -((m + 1 : ℕ) : ℤ) - 1 := by omega
    refine ⟨f ⟨0, map_zero _⟩, funext fun α => ?_⟩
    have hα : α = ⟨0, map_zero _⟩ := Subtype.ext ((Finsupp.degree_eq_zero_iff _).mp α.2)
    rw [hα]
    exact eq_of_heq (monomialPairing_zero _ hd _ _)
  | succ k ih =>
    intro d hd f
    have hd' : (k : ℤ) + (d + 1) = -((m + 1 : ℕ) : ℤ) - 1 := by push_cast at hd ⊢; omega
    choose y hy using fun i => ih (d + 1) hd' (fun β => f (β.addSingle i))
    have hcompat : ∀ i j,
        ((topH A m).map (twistMulX A (m + 1) j (d + 1) (d + 1 + 1) (by ring))).hom (y i) =
        ((topH A m).map (twistMulX A (m + 1) i (d + 1) (d + 1 + 1) (by ring))).hom (y j) := by
      intro i j
      cases k with
      | zero =>
        have h0 : IsZero ((topH A m).obj (twistingSheaf (polyGrading A (m + 1)) (d + 1 + 1))) :=
          isZero_Hgroup_twistingSheaf_top A m (d + 1 + 1) (by push_cast at hd ⊢; omega)
        exact (eq_zero_of_isZero h0 _).trans (eq_zero_of_isZero h0 _).symm
      | succ k =>
        have hd'' : (k : ℤ) + (d + 1 + 1) = -((m + 1 : ℕ) : ℤ) - 1 := by
          push_cast at hd ⊢; omega
        refine injective_monomialPairing k (d + 1 + 1) hd'' (funext fun γ => ?_)
        rw [monomialPairing_twistMulX k (d + 1) hd' hd'' j (y i) γ,
          monomialPairing_twistMulX k (d + 1) hd' hd'' i (y j) γ, hy i, hy j]
        exact congrArg f (addSingle_comm γ i j)
    obtain ⟨x, hx⟩ := exists_mulX_eq (by ring) (by ring) (by push_cast at hd; omega) y hcompat
    refine ⟨x, funext fun α => ?_⟩
    obtain ⟨i, β, rfl⟩ := exists_eq_addSingle α
    rw [← monomialPairing_twistMulX k d hd hd' i x β, hx i, hy i]

/-- **The multiplication pairing `Hⁿ(ℙⁿ_A, 𝒪(d)) ⟶ ∏_{|α| = k} Hⁿ(ℙⁿ_A, 𝒪(-n-1))`,
`c ↦ (X^α · c)_α`, is bijective** for `k = -n - 1 - d`. -/
theorem bijective_monomialPairing (k : ℕ) (d : ℤ) (hd : (k : ℤ) + d = -((m + 1 : ℕ) : ℤ) - 1) :
    Function.Bijective (monomialPairing A m k d hd) :=
  ⟨injective_monomialPairing k d hd, surjective_monomialPairing k d hd⟩

end Pairing

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.ProjectiveSpacePairing

end
