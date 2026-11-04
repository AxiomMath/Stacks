module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import StacksFrontier.Homology.HomComplex.KoszulBraiding
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# The total tensor product of cochain complexes

Let `R` be a commutative ring. The category of cochain complexes of `R`-modules carries a
tensor product: the total complex of the degreewise tensor-product double complex, with the
Koszul sign convention in the differential. This file records the monoidal structure that
tensor product carries, and how much of it survives passage to the homotopy category.

## Main results

* `TotalTensorComplex.cochainComplex_symmetricMonoidalCategory`: cochain complexes of
  `R`-modules are symmetric monoidal under the total tensor product, with braiding given on
  the summand of bidegree `(p, q)` by the ordinary symmetry times the Koszul sign `(-1)^(p*q)`.
* `TotalTensorComplex.tensorTotal_preserves_homotopy_and_descends`: tensoring with a fixed
  complex sends homotopic maps to homotopic maps, hence descends to the homotopy category.
* `TotalTensorComplex.homotopyCategory_symmetricMonoidalCategory`: the induced monoidal
  structure on the homotopy category is again symmetric, and the quotient functor is braided.
* `TotalTensorComplex.tensor_isStrictlyLE`: the total tensor product of complexes bounded
  above by `a` and `b` is bounded above by `a + b`.
* `TotalTensorComplex.tleft_isTriangulated` and `TotalTensorComplex.tright_isTriangulated`:
  tensoring on either side and totalizing is an exact functor of triangulated categories.

## Implementation notes

The total tensor product is Mathlib's monoidal product on
`CochainComplex (ModuleCat R) ℤ`, built from `Functor.map₂CochainComplex` applied to
`curriedTensor`; the Koszul signs are the ones baked into that construction. The descent to
the homotopy category is obtained by localizing at the homotopy equivalences, which form a
monoidal morphism property.

The triangulatedness results are stated for an arbitrary preadditive monoidal category with
additive tensor product, the generality in which they are proved in
`StacksFrontier.Homology.TensorComplex.ExactFunctor`. Module categories in any universe satisfy
those hypotheses, so these apply to `ModuleCat.{max u v} R` and not only to `ModuleCat.{u} R`.
The symmetric monoidal statements, by contrast, are genuinely about `ModuleCat.{u} R`: they
name the tensor unit, which for a larger module universe is a lift of `R` rather than `R`.

## References

* [The Stacks Project, Tag 0FNI](https://stacks.math.columbia.edu/tag/0FNI)
* [The Stacks Project, Tag 064I](https://stacks.math.columbia.edu/tag/064I)
* [The Stacks Project, Tag 0GWP](https://stacks.math.columbia.edu/tag/0GWP)
* [The Stacks Project, Tag 064J](https://stacks.math.columbia.edu/tag/064J)
-/

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Localization

universe u

namespace TotalTensorComplex

section Braiding

variable {R : Type u} [CommRing R]

private lemma complexBraiding_symm (K L : CochainComplex (ModuleCat R) ℤ) :
    (CochainComplex.Koszul.complexBraiding K L).symm =
      CochainComplex.Koszul.complexBraiding L K := by
  simpa using congrArg Iso.symm (CochainComplex.Koszul.complexBraiding_swap K L)

-- the `simpa` rewriting of composite isomorphisms in `hr` below is heavy
private lemma complexBraiding_hexagon_reverse
    (K L M : CochainComplex (ModuleCat R) ℤ) :
    (α_ K L M).inv ≫ (CochainComplex.Koszul.complexBraiding (K ⊗ L) M).hom ≫ (α_ M K L).inv =
      K ◁ (CochainComplex.Koszul.complexBraiding L M).hom ≫ (α_ K M L).inv ≫
        (CochainComplex.Koszul.complexBraiding K M).hom ▷ L := by
  have hf :
      (α_ M K L) ≪≫ CochainComplex.Koszul.complexBraiding M (K ⊗ L) ≪≫ (α_ K L M) =
        whiskerRightIso (CochainComplex.Koszul.complexBraiding M K) L ≪≫ (α_ K M L) ≪≫
          whiskerLeftIso K (CochainComplex.Koszul.complexBraiding M L) :=
    Iso.ext (CochainComplex.Koszul.complexBraiding_hexagon_forward M K L)
  have hr :
      (α_ K L M).symm ≪≫ CochainComplex.Koszul.complexBraiding (K ⊗ L) M ≪≫ (α_ M K L).symm =
        whiskerLeftIso K (CochainComplex.Koszul.complexBraiding L M) ≪≫ (α_ K M L).symm ≪≫
          whiskerRightIso (CochainComplex.Koszul.complexBraiding K M) L := by
    simpa only [Iso.trans_assoc, Iso.trans_symm, complexBraiding_symm, whiskerLeftIso_symm,
      whiskerRightIso_symm] using congrArg Iso.symm hf
  exact (congrArg Iso.hom hr :)

private noncomputable def symmetric :
    SymmetricCategory (CochainComplex (ModuleCat R) ℤ) where
  braiding := CochainComplex.Koszul.complexBraiding
  braiding_naturality_left := CochainComplex.Koszul.complexBraiding_naturality_left
  braiding_naturality_right := CochainComplex.Koszul.complexBraiding_naturality_right
  hexagon_forward := CochainComplex.Koszul.complexBraiding_hexagon_forward
  hexagon_reverse := complexBraiding_hexagon_reverse
  symmetry := CochainComplex.Koszul.complexBraiding_symmetry
end Braiding

/-- The category of cochain complexes of modules over a commutative ring, with tensor product
given by the total complex of the degreewise tensor product, is symmetric monoidal. On the
summand of bidegree `(p, q)`, its braiding is the ordinary symmetry of tensor products multiplied
by the Koszul sign `(-1)^(p*q)`. -/
@[stacks 0FNI, stacks 0GWR]
public theorem cochainComplex_symmetricMonoidalCategory (R : Type u) [CommRing R] :
    ∃ s : SymmetricCategory (CochainComplex (ModuleCat R) ℤ),
      ∀ (K L : CochainComplex (ModuleCat R) ℤ) (p q n : ℤ) (h : p + q = n),
        HomologicalComplex.ιTensorObj K L p q n h ≫
            (s.toBraidedCategory.braiding K L).hom.f n =
          ((p * q).negOnePow : ℤˣ) •
            ((β_ (K.X p) (L.X q)).hom ≫
              HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h)) :=
  ⟨symmetric, CochainComplex.Koszul.complexBraiding_ι⟩

/-- Tensoring with a fixed complex and taking the total complex preserves homotopic maps,
and therefore induces an endofunctor of the homotopy category of complexes. -/
@[stacks 064I, sga "4½ Etat_0 1.3.3" "tensor over ModuleCat R"]
public theorem tensorTotal_preserves_homotopy_and_descends {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    let T := (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.flip.obj P
    (∀ {L M : CochainComplex (ModuleCat.{u} R) ℤ} {f g : L ⟶ M},
      homotopic (ModuleCat.{u} R) (ComplexShape.up ℤ) f g →
        homotopic (ModuleCat.{u} R) (ComplexShape.up ℤ) (T.map f) (T.map g)) ∧
    ∃ T' : HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤
        HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ),
      HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙ T' =
        T ⋙ HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) := by
  intro T
  have hT : ∀ {L M : CochainComplex (ModuleCat.{u} R) ℤ} {f g : L ⟶ M},
      homotopic (ModuleCat.{u} R) (ComplexShape.up ℤ) f g →
        homotopic (ModuleCat.{u} R) (ComplexShape.up ℤ) (T.map f) (T.map g) := by
    rintro L M f g ⟨h⟩
    exact ⟨HomologicalComplex.mapBifunctorMapHomotopy₁ h
      (𝟙 P) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)⟩
  exact ⟨hT, CategoryTheory.Quotient.lift (homotopic (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (T ⋙ HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (fun _ _ _ _ h ↦ HomotopyCategory.eq_of_homotopy _ _ (hT h).some),
    CategoryTheory.Quotient.lift_spec _ _ _⟩

/-- The total tensor product of two homotopy equivalences of complexes is a homotopy
equivalence.  Both homotopies are the ones `HomologicalComplex.mapBifunctorMapHomotopy`
produces for the total complex, composed in the two variables. -/
public noncomputable def tensorHomotopyEquiv
    {R : Type u} [CommRing R]
    {K₁ K₂ L₁ L₂ : CochainComplex (ModuleCat.{u} R) ℤ}
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (K₁ ⊗ K₂) (L₁ ⊗ L₂) where
  hom := e₁.hom ⊗ₘ e₂.hom
  inv := e₁.inv ⊗ₘ e₂.inv
  homotopyHomInvId := by
    rw [tensorHom_comp_tensorHom]
    exact (((HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId
        (e₂.hom ≫ e₂.inv) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K₁) e₂.homotopyHomInvId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (id_tensorHom_id K₁ K₂)))
  homotopyInvHomId := by
    rw [tensorHom_comp_tensorHom]
    exact (((HomologicalComplex.mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId
        (e₂.inv ≫ e₂.hom) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 L₁) e₂.homotopyInvHomId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ))).trans
      (Homotopy.ofEq (id_tensorHom_id L₁ L₂)))

/-- The homotopy category of cochain complexes of modules over a commutative ring is symmetric
monoidal under the total tensor product. Its associator and Koszul braiding are induced from the
corresponding canonical constraints on complexes. -/
@[stacks 0GWP]
public theorem homotopyCategory_symmetricMonoidalCategory (R : Type u) [CommRing R] :
    ∃ sC : SymmetricCategory (CochainComplex (ModuleCat.{u} R) ℤ),
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ) (p q n : ℤ) (h : p + q = n),
        HomologicalComplex.ιTensorObj K L p q n h ≫
            (sC.toBraidedCategory.braiding K L).hom.f n =
          ((p * q).negOnePow : ℤˣ) •
            ((β_ (K.X p) (L.X q)).hom ≫
              HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h))) ∧
      letI := sC
      ∃ mK : MonoidalCategory
          (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)),
        letI := mK
        ∃ sK : SymmetricCategory
            (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)),
          letI := sK
          Nonempty
            (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).Braided := by
  obtain ⟨sC, hsC⟩ := cochainComplex_symmetricMonoidalCategory R
  refine ⟨sC, hsC, ?_⟩
  let := sC
  let W := HomologicalComplex.homotopyEquivalences
    (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let : W.IsMonoidal := by
    dsimp [W]
    apply MorphismProperty.IsMonoidal.mk'
    rintro K₁ K₂ L₁ L₂ _ _ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    exact ⟨tensorHomotopyEquiv e₁ e₂, rfl⟩
  let Q := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let : Q.IsLocalization W :=
    (ComplexShape.up ℤ).quotient_isLocalization (fun n ↦ ⟨n - 1, by simp⟩) (ModuleCat.{u} R)
  let ε : Q.obj (𝟙_ _) ≅ Q.obj (𝟙_ _) := Iso.refl _
  show ∃ mK : MonoidalCategory (LocalizedMonoidal Q W ε),
    let := mK
    ∃ sK : SymmetricCategory (LocalizedMonoidal Q W ε),
      let := sK
      Nonempty (Localization.Monoidal.toMonoidalCategory Q W ε).Braided
  let mK : MonoidalCategory (LocalizedMonoidal Q W ε) := inferInstance
  refine ⟨mK, ?_⟩
  let sK : SymmetricCategory (LocalizedMonoidal Q W ε) := inferInstance
  refine ⟨sK, ?_⟩
  exact ⟨inferInstanceAs ((Localization.Monoidal.toMonoidalCategory Q W ε).Braided)⟩

section Triangulated

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [∀ (K₁ K₂ : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) (ComplexShape.up ℤ)]

/-! ### Degreewise boundedness -/

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- The total tensor product of a complex concentrated in degrees `≤ a` with one concentrated
in degrees `≤ b` is concentrated in degrees `≤ a + b`: the summand of bidegree `(p, q)` with
`p + q > a + b` has one of its two factors zero. -/
public lemma tensor_isStrictlyLE (P Q : CochainComplex C ℤ) (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj P Q) (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (P.X p ⊗ Q.X q) := by
    by_cases hp : a < p
    · exact (tensorRight (Q.X q)).map_isZero (P.isZero_of_isStrictlyLE a p hp)
    · exact (tensorLeft (P.X p)).map_isZero
        (Q.isZero_of_isStrictlyLE b q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

/-! ### Exactness -/

/-- Tensoring on the left with a fixed complex and totalizing is an exact functor of
triangulated categories on the homotopy category.

Stated for an arbitrary preadditive monoidal category whose tensor product is additive in each
variable, which is the generality the statement holds in. Module categories are the case of
interest, at any module universe: the instances above hold for `ModuleCat.{max u v} R` as well
as for `ModuleCat.{u} R`. -/
@[stacks 064J]
public theorem tleft_isTriangulated (G : CochainComplex C ℤ) :
    ∃ e : (Tleft G).CommShift ℤ,
      @Functor.IsTriangulated _ _ _ _ _ _ (Tleft G) e _ _ _ _ _ _ _ _ :=
  main_left G

/-- Tensoring on the right with a fixed complex and totalizing is an exact functor of
triangulated categories on the homotopy category. This is genuinely distinct from
`tleft_isTriangulated`: the two differ by the Koszul sign in the commutativity constraint. -/
@[stacks 064J]
public theorem tright_isTriangulated (G : CochainComplex C ℤ) :
    ∃ e : (Tright G).CommShift ℤ,
      @Functor.IsTriangulated _ _ _ _ _ _ (Tright G) e _ _ _ _ _ _ _ _ :=
  main_right G

end Triangulated

end TotalTensorComplex

end
