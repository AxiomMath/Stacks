module

public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.Homology.KunnethDegreeZero
public import StacksFrontier.Homology.Tor.ProductNaturality
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Homology.Tor.DerivedTensorBoundedAbove

/-!
# The Künneth formula in the top degree, in canonical form

Tensoring cocycles gives, for any two objects `K` and `L` of the derived category of modules over
a commutative ring `R`, a canonical map

`Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^𝐋_R L)`,

the cohomology product of [Stacks, Tag 068H] (`RingTheory.TorProducts.cohomologyTensorProduct`).
This file proves that **when the cohomology of `K` vanishes above `i` and that of `L` above `j`,
the map in degree `i + j` is an isomorphism, over an arbitrary commutative ring.** This is the
top-degree case of the Künneth formula: in the top degree no higher `Tor` intervenes, because the
tensor product is right exact. It is the step "since we are looking in top degree there are no
higher tor groups that intervene" of the proof of [Stacks, Tag 0G8J], where it identifies
`H^{2n}(X ×_A X, ℱ ⊠ 𝒢)` with `Hⁿ(X, ℱ) ⊗_A Hⁿ(X, 𝒢)` through the Künneth isomorphism of
[Stacks, Tag 0FLQ].

At the level of complexes the statement is elementary: if `P` vanishes strictly above `i` and
`Q` strictly above `j`, then `(P ⊗ Q)^{i+j} = P^i ⊗ Q^j`, nothing lies above it, and the
cokernel of the differential into it is `coker(d_P) ⊗ coker(d_Q)` by right exactness. In the
derived category the two objects are represented by complexes of projective modules vanishing
strictly above `i` and `j` ([Stacks, Tag 05T7]); such complexes are K-projective and K-flat, and
at a K-projective K-flat pair the cohomology product is computed by tensoring cocycles
(`TorCrossProduct.cohomologyTensorProduct_map_eq_of_isKProjective`), which reduces the derived
statement to the statement about complexes.

## Main results

* `CochainComplex.Kunneth.isIso_tensorHomology_top`: for complexes vanishing strictly above `i`
  and `j`, the product `Hⁱ(P) ⊗ Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)` is an isomorphism.
* `CochainComplex.Kunneth.isIso_cohomologyTensorProduct_map_top`: for `K ∈ D^{≤ i}(R)` and
  `L ∈ D^{≤ j}(R)`, the cohomology product of [Stacks, Tag 068H] in degree `i + j` is an
  isomorphism.
* `CochainComplex.Kunneth.cohomologyTensorProductIsoTop`: the same, packaged as an isomorphism.

## Implementation notes

The cohomology product `RingTheory.TorProducts.cohomologyTensorProduct` is defined only for the
standard model of the derived category, so the derived statements are made there: the section
`Derived` opens the scope `Stacks.StandardDerivedModel`, and nothing else in the file depends on a
model of the derived category.

## References

* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

universe u

namespace CochainComplex.Kunneth

variable {R : Type u} [CommRing R]

/-- Tensoring on the right with a module preserves finite colimits, being isomorphic to tensoring
on the left through the braiding. -/
local instance preservesFiniteColimits_curriedTensor_flip_obj (X : ModuleCat.{u} R) :
    PreservesFiniteColimits ((curriedTensor (ModuleCat.{u} R)).flip.obj X) :=
  preservesFiniteColimits_of_natIso
    (NatIso.ofComponents (fun Y => β_ X Y) (fun f => by simp) :
      (curriedTensor (ModuleCat.{u} R)).obj X ≅ (curriedTensor (ModuleCat.{u} R)).flip.obj X)

section TopDegree

variable (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) [P.IsStrictlyLE i]
  [Q.IsStrictlyLE j]

/-- A summand `Pᵃ ⊗ Qᵇ` with `a ≠ i` vanishes, if `b > j` whenever `a < i`. -/
private theorem isZero_tensor_of_ne_of_lt (a b : ℤ) (ha : a ≠ i) (hb : a < i → j < b) :
    IsZero (P.X a ⊗ Q.X b) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · exact isZero_tensor_right (Q.isZero_of_isStrictlyLE j b (hb ha))
  · exact isZero_tensor_left (P.isZero_of_isStrictlyLE i a ha)

/-- A summand `Pᵃ ⊗ Qᵇ` of total degree `a + b = i + j` other than the one of bidegree `(i, j)`
vanishes, when `P` vanishes strictly above `i` and `Q` strictly above `j`. -/
theorem isZero_tensor_of_add_eq_of_ne (a b : ℤ) (h : a + b = i + j) (ha : a ≠ i) :
    IsZero (P.X a ⊗ Q.X b) :=
  isZero_tensor_of_ne_of_lt P Q i j a b ha (by omega)

/-- A summand `Pᵃ ⊗ Qᵇ` of total degree above `i + j` vanishes. -/
theorem isZero_tensor_of_lt_add (a b : ℤ) (h : i + j < a + b) : IsZero (P.X a ⊗ Q.X b) := by
  rcases lt_or_ge i a with ha | ha
  · exact isZero_tensor_left (P.isZero_of_isStrictlyLE i a ha)
  · exact isZero_tensor_right (Q.isZero_of_isStrictlyLE j b (by omega))

/-- The tensor product of complexes vanishing strictly above `i` and `j` vanishes strictly above
`i + j`. -/
theorem isZero_tensorObj_X_of_lt (n : ℤ) (hn : i + j < n) :
    IsZero ((HomologicalComplex.tensorObj P Q).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b h
  have h' : a + b = n := h
  exact (isZero_tensor_of_lt_add P Q i j a b (by omega)).eq_of_src _ _

/-- **The inclusion of the summand of bidegree `(i, j)` into degree `i + j` of the tensor product
is an isomorphism**, for complexes vanishing strictly above `i` and `j`. -/
theorem isIso_ιTensorObj_top :
    IsIso (HomologicalComplex.ιTensorObj P Q i j (i + j) rfl) := by
  refine ⟨HomologicalComplex.mapBifunctorDesc (fun a b h =>
    if ha : a = i then eqToHom (by
        have h' : a + b = i + j := h
        rw [ha, show b = j by omega]
        rfl) else 0), ?_, ?_⟩
  · simp only [HomologicalComplex.ιTensorObj, HomologicalComplex.ι_mapBifunctorDesc]
    simp
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b h
    have h' : a + b = i + j := h
    rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc, Category.comp_id]
    by_cases ha : a = i
    · subst ha
      obtain rfl : b = j := by omega
      simp
    · rw [dif_neg ha, Limits.zero_comp,
        (isZero_tensor_of_add_eq_of_ne P Q i j a b h' ha).eq_of_src
          (HomologicalComplex.ιMapBifunctor P Q (curriedTensor (ModuleCat.{u} R))
            (ComplexShape.up ℤ) a b (i + j) h) 0]

/-- In the top degree every cochain of `P` is a cocycle. -/
theorem isIso_iCycles_top : IsIso (P.iCycles i) :=
  P.isIso_iCycles i (i + 1) (by simp)
    ((P.isZero_of_isStrictlyLE i (i + 1) (by omega)).eq_of_tgt _ _)

/-- In the top degree `i + j` every cochain of `P ⊗ Q` is a cocycle. -/
theorem isIso_tensorObj_iCycles_top :
    IsIso ((HomologicalComplex.tensorObj P Q).iCycles (i + j)) :=
  (HomologicalComplex.tensorObj P Q).isIso_iCycles (i + j) (i + j + 1) (by simp)
    ((isZero_tensorObj_X_of_lt P Q i j (i + j + 1) (by omega)).eq_of_tgt _ _)

/-- **In the top degree the tensor of two cocycles is every cocycle**: the map
`Zⁱ(P) ⊗ Zʲ(Q) ⟶ Zⁱ⁺ʲ(P ⊗ Q)` is an isomorphism. -/
theorem isIso_tensorCycles_top : IsIso (CochainComplex.tensorCycles P Q i j) := by
  have := isIso_iCycles_top P i
  have := isIso_iCycles_top Q j
  have := isIso_ιTensorObj_top P Q i j
  have := isIso_tensorObj_iCycles_top P Q i j
  have h : IsIso (CochainComplex.tensorCycles P Q i j ≫
      (HomologicalComplex.tensorObj P Q).iCycles (i + j)) := by
    rw [CochainComplex.tensorCycles_i]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((HomologicalComplex.tensorObj P Q).iCycles (i + j))

/-- A boundary of bidegree `(i - 1, j)` in the top degree is the tensor of a boundary of `P`
with a cycle of `Q`. -/
theorem ιTensorObj_toCycles_left (hij : i - 1 + j = i + j - 1) [IsIso (Q.iCycles j)] :
    HomologicalComplex.ιTensorObj P Q (i - 1) j (i + j - 1) hij ≫
        (HomologicalComplex.tensorObj P Q).toCycles (i + j - 1) (i + j) =
      (𝟙 (P.X (i - 1)) ⊗ₘ inv (Q.iCycles j)) ≫ (P.toCycles (i - 1) i ⊗ₘ 𝟙 (Q.cycles j)) ≫
        CochainComplex.tensorCycles P Q i j := by
  rw [← cancel_mono ((HomologicalComplex.tensorObj P Q).iCycles (i + j))]
  simp only [Category.assoc, CochainComplex.tensorCycles_i, HomologicalComplex.toCycles_i]
  rw [← Category.assoc (P.toCycles (i - 1) i ⊗ₘ 𝟙 (Q.cycles j)), tensorHom_comp_tensorHom,
    HomologicalComplex.toCycles_i, Category.id_comp,
    ← CochainComplex.tensor_left_boundary_d, ← Category.assoc, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.id_comp, IsIso.inv_hom_id, MonoidalCategory.id_tensorHom_id,
    Category.id_comp]

/-- A boundary of bidegree `(i, j - 1)` in the top degree is, up to the Koszul sign, the tensor of
a cycle of `P` with a boundary of `Q`. -/
theorem ιTensorObj_toCycles_right (hij : i + (j - 1) = i + j - 1) [IsIso (P.iCycles i)] :
    HomologicalComplex.ιTensorObj P Q i (j - 1) (i + j - 1) hij ≫
        (HomologicalComplex.tensorObj P Q).toCycles (i + j - 1) (i + j) =
      ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⟨i, j - 1⟩ •
        ((inv (P.iCycles i) ⊗ₘ 𝟙 (Q.X (j - 1))) ≫ (𝟙 (P.cycles i) ⊗ₘ Q.toCycles (j - 1) j) ≫
          CochainComplex.tensorCycles P Q i j) := by
  rw [← cancel_mono ((HomologicalComplex.tensorObj P Q).iCycles (i + j))]
  simp only [Category.assoc, CochainComplex.tensorCycles_i, HomologicalComplex.toCycles_i,
    Linear.units_smul_comp]
  rw [← cancel_epi (P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))), Linear.comp_units_smul]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, IsIso.hom_inv_id, Category.id_comp,
    Category.comp_id, HomologicalComplex.toCycles_i]
  exact CochainComplex.tensor_right_boundary_d P Q i j

/-- The inverse of the top-degree tensor of cycles, followed by the two projections to
cohomology, kills the boundaries of `P ⊗ Q`. -/
theorem toCycles_inv_tensorCycles_homologyπ [IsIso (CochainComplex.tensorCycles P Q i j)] :
    (HomologicalComplex.tensorObj P Q).toCycles (i + j - 1) (i + j) ≫
        inv (CochainComplex.tensorCycles P Q i j) ≫ (P.homologyπ i ⊗ₘ Q.homologyπ j) = 0 := by
  have := isIso_iCycles_top P i
  have := isIso_iCycles_top Q j
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b h
  have h' : a + b = i + j - 1 := h
  rw [comp_zero]
  by_cases ha : a = i - 1
  · subst ha
    obtain rfl : b = j := by omega
    have e := ιTensorObj_toCycles_left P Q i b h
    show HomologicalComplex.ιTensorObj P Q (i - 1) b (i + b - 1) h ≫ _ = 0
    rw [reassoc_of% e, IsIso.hom_inv_id_assoc, tensorHom_comp_tensorHom,
      HomologicalComplex.toCycles_comp_homologyπ, MonoidalPreadditive.zero_tensor, comp_zero]
  · by_cases hb : a = i
    · subst hb
      obtain rfl : b = j - 1 := by omega
      have e := ιTensorObj_toCycles_right P Q a j h
      show HomologicalComplex.ιTensorObj P Q a (j - 1) (a + j - 1) h ≫ _ = 0
      rw [reassoc_of% e, Linear.units_smul_comp, Category.assoc, Category.assoc,
        IsIso.hom_inv_id_assoc, tensorHom_comp_tensorHom,
        HomologicalComplex.toCycles_comp_homologyπ, MonoidalPreadditive.tensor_zero, comp_zero,
        smul_zero]
    · exact (isZero_tensor_of_ne_of_lt P Q i j a b hb (by omega)).eq_of_src _ _

/-- **The Künneth product in the top degree, for complexes.** If `P` vanishes strictly above `i`
and `Q` strictly above `j`, the product `Hⁱ(P) ⊗_R Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗ Q)` induced by tensoring
cocycles is an isomorphism: by right exactness of the tensor product, the cokernel of the
differential into `(P ⊗ Q)^{i+j} = Pⁱ ⊗ Qʲ` is the tensor product of the cokernels of the
differentials into `Pⁱ` and into `Qʲ`. No flatness is needed. -/
theorem isIso_tensorHomology_top : IsIso (CochainComplex.tensorHomology P Q i j) := by
  have := isIso_tensorCycles_top P Q i j
  have hepi : Epi (P.homologyπ i ⊗ₘ Q.homologyπ j) :=
    RingTheory.TorProducts.epi_tensorHom _ _
  let T := HomologicalComplex.tensorObj P Q
  let ψ : T.homology (i + j) ⟶ P.homology i ⊗ Q.homology j :=
    (T.homologyIsCokernel (i + j - 1) (i + j) (by simp)).desc
      (CokernelCofork.ofπ (inv (CochainComplex.tensorCycles P Q i j) ≫
        (P.homologyπ i ⊗ₘ Q.homologyπ j)) (by
          simpa using toCycles_inv_tensorCycles_homologyπ P Q i j))
  have hψ : T.homologyπ (i + j) ≫ ψ =
      inv (CochainComplex.tensorCycles P Q i j) ≫ (P.homologyπ i ⊗ₘ Q.homologyπ j) :=
    Cofork.IsColimit.π_desc (T.homologyIsCokernel (i + j - 1) (i + j) (by simp))
  refine ⟨ψ, ?_, ?_⟩
  · rw [← cancel_epi (P.homologyπ i ⊗ₘ Q.homologyπ j), ← Category.assoc,
      CochainComplex.homologyπ_tensorHomology, Category.assoc]
    show _ ≫ T.homologyπ (i + j) ≫ ψ = _
    rw [hψ, IsIso.hom_inv_id_assoc, Category.comp_id]
  · rw [← cancel_epi (T.homologyπ (i + j)), ← Category.assoc, hψ, Category.assoc,
      CochainComplex.homologyπ_tensorHomology, IsIso.inv_hom_id_assoc, Category.comp_id]

end TopDegree

section Derived

open scoped Stacks.StandardDerivedModel

/-- **The Künneth product in the top degree** ([Stacks, Tag 068H] and the step "in top degree no
higher tor groups intervene" of [Stacks, Tag 0G8J]). For objects `K ∈ D^{≤ i}(R)` and
`L ∈ D^{≤ j}(R)` over an arbitrary commutative ring `R`, the cohomology product

`Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^𝐋_R L)`

induced by tensoring cocycles is an isomorphism. Neither object is assumed bounded below. -/
theorem isIso_cohomologyTensorProduct_map_top (K L : CochainComplex.DerivedTensor.DObj R)
    (i j : ℤ) [K.IsLE i] [L.IsLE j] :
    IsIso (RingTheory.TorProducts.cohomologyTensorProduct K L i j).map := by
  obtain ⟨P, hP, hPi, ⟨eK⟩⟩ := StacksDraft.TorAmplitude.exists_projective_representative_of_isLE
    K i ((DerivedCategory.isLE_iff K i).1 inferInstance)
  obtain ⟨Q, hQ, hQj, ⟨eL⟩⟩ := StacksDraft.TorAmplitude.exists_projective_representative_of_isLE
    L j ((DerivedCategory.isLE_iff L j).1 inferInstance)
  have := hPi
  have := hQj
  have : ∀ n, Projective (P.X n) := hP
  have : ∀ n, Projective (Q.X n) := hQ
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P i
  have : Q.IsKProjective := CochainComplex.isKProjective_of_projective Q j
  have hPf : P.KFlat := CochainComplex.DerivedTensor.kFlat_of_projective_isStrictlyLE P i hP
  have hQf : Q.KFlat := CochainComplex.DerivedTensor.kFlat_of_projective_isStrictlyLE Q j hQ
  -- the product at the projective representatives is the product of complexes
  have hE := TorCrossProduct.cohomologyTensorProduct_map_eq_of_isKProjective P Q hPf hQf i j
    (CochainComplex.tensorCycles P Q i j) (CochainComplex.tensorCycles_i P Q i j)
  have := RingTheory.TorProducts.epi_tensorHom (P.homologyπ i) (Q.homologyπ j)
  replace hE := (cancel_epi (P.homologyπ i ⊗ₘ Q.homologyπ j)).1
    (hE.trans (CochainComplex.homologyπ_tensorHomology P Q i j).symm)
  have hth := isIso_tensorHomology_top P Q i j
  have hrep : IsIso (RingTheory.TorProducts.cohomologyTensorProduct (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj Q) i j).map := by
    have h₁ : IsIso ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).inv.app P ⊗ₘ
        (DerivedCategory.homologyFunctorFactors (ModuleCat R) j).inv.app Q) := inferInstance
    have h₂ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).map
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).comparison P Q hPf
          hQf).hom ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat R) (i + j)).hom.app (P ⊗ Q)) :=
      inferInstance
    have h₃ : IsIso (((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).inv.app P ⊗ₘ
        (DerivedCategory.homologyFunctorFactors (ModuleCat R) j).inv.app Q) ≫
        (RingTheory.TorProducts.cohomologyTensorProduct (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj Q) i j).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).map
          ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).comparison P Q hPf
            hQf).hom ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat R) (i + j)).hom.app (P ⊗ Q)) := by
      have h := hth
      rw [← hE] at h
      exact h
    have h₄ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₁ h₃
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h₂ h₄
  -- transport along the representatives, by naturality of the product
  have hnat := RingTheory.TorProducts.cohomologyTensorProduct_naturality_of_isKProjective P Q
    hPf hQf eK.inv eL.inv i j
  have hl : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map eK.inv ⊗ₘ
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map eL.inv) := inferInstance
  have hr : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).map eK.inv).app
          (DerivedCategory.Q.obj Q) ≫
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).map
          eL.inv)) := inferInstance
  have h₅ : IsIso (((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map eK.inv ⊗ₘ
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map eL.inv) ≫
      (RingTheory.TorProducts.cohomologyTensorProduct K L i j).map) := by
    rw [hnat]
    infer_instance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hl h₅

/-- **The top-degree Künneth isomorphism** `Hⁱ(K) ⊗_R Hʲ(L) ≅ Hⁱ⁺ʲ(K ⊗^𝐋_R L)` for
`K ∈ D^{≤ i}(R)` and `L ∈ D^{≤ j}(R)`. Its underlying map is the cohomology product of
[Stacks, Tag 068H]. -/
def cohomologyTensorProductIsoTop (K L : CochainComplex.DerivedTensor.DObj R) (i j : ℤ)
    [K.IsLE i] [L.IsLE j] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K ⊗
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj L ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj L) :=
  @asIso _ _ _ _ (RingTheory.TorProducts.cohomologyTensorProduct K L i j).map
    (isIso_cohomologyTensorProduct_map_top K L i j)

/-- The forward map of `cohomologyTensorProductIsoTop K L i j` is the cohomology product
`Hⁱ(K) ⊗_R Hʲ(L) → Hⁱ⁺ʲ(K ⊗^𝐋_R L)`. -/
@[simp]
theorem cohomologyTensorProductIsoTop_hom (K L : CochainComplex.DerivedTensor.DObj R)
    (i j : ℤ) [K.IsLE i] [L.IsLE j] :
    (cohomologyTensorProductIsoTop K L i j).hom =
      (RingTheory.TorProducts.cohomologyTensorProduct K L i j).map :=
  rfl

end Derived

end CochainComplex.Kunneth

end
