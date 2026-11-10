module

public import StacksFrontier.CategoryTheory.Monoidal.ExternalAdjunctionMate
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
public import StacksFrontier.CategoryTheory.Shift.AdjunctionMateCommShift

/-!
# Naturality and shift compatibility of the two-variable mate

Let `adj : L ⊣ R`, `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions with common target `E`, a
monoidal category, `R` lax monoidal, and `α₁ : R₁ ⋙ S₁ ⟶ R`, `α₂ : R₂ ⋙ S₂ ⟶ R` two
comparisons.  `CategoryTheory.Adjunction.externalMate` is the two-variable mate
`L (S₁ M₁ ⊗ S₂ M₂) ⟶ L₁ M₁ ⊗ L₂ M₂`.  This file records how it is characterised, that it is
natural in both variables, and that -- read in one variable at a time -- it commutes with shifts.

## Main definitions

* `CategoryTheory.Adjunction.externalMateNatTransFst` and
  `CategoryTheory.Adjunction.externalMateNatTransSnd`: the two-variable mate at a fixed object in
  one variable, as a natural transformation in the other -- the shape a dévissage in that
  variable consumes.  Both readings are needed to reduce the mate to a pair of generators: one
  dévissage fixes a generator in the first variable and runs in the second, the other runs in the
  first with the second object arbitrary.
* `CategoryTheory.Adjunction.externalMateTranspose` and
  `CategoryTheory.Adjunction.externalMateTransposeSnd`: their transposes along `adj`, the morphism
  `S₁ M₁ ⊗ S₂ M₂ ⟶ R (L₁ M₁ ⊗ L₂ M₂)`, as a natural transformation in one variable or the other.
* `CategoryTheory.Adjunction.restrictionMateTranspose`: the transpose of the one-variable mate of
  `α₁`, as a natural transformation `S₁ ⟶ L₁ ⋙ R`.

## Main results

* `CategoryTheory.Adjunction.eq_externalMate_of_unit_comp_map`: the defining property
  `CategoryTheory.Adjunction.unit_comp_map_externalMate` characterises the mate.
* `CategoryTheory.Adjunction.isIso_externalMate_of_unit_comp_map`: **the two-variable mate is
  invertible at a pair of objects as soon as some isomorphism there has its defining property.**
* `CategoryTheory.Adjunction.externalMate_naturality`: the two-variable mate is natural in
  `(M₁, M₂)`.
* `CategoryTheory.Adjunction.commShift_externalMateNatTransFst`: **the one-variable mate is
  compatible with the shift as soon as its transpose is.**
* `CategoryTheory.Adjunction.externalMateTranspose_eq`,
  `CategoryTheory.Adjunction.externalMateTransposeSnd_eq` and
  `CategoryTheory.Adjunction.restrictionMateTranspose_eq`: those transposes written out as
  composites of unitors, associators, whiskerings and the tensorator of `R` in one variable.
* `CategoryTheory.Adjunction.commShift_externalMateTranspose` and
  `CategoryTheory.Adjunction.commShift_externalMateNatTransFst'`: **the transpose of the
  two-variable mate, and so the mate itself, is compatible with the shift**, from the shift
  compatibility of the tensorator of `R` (`CategoryTheory.Functor.LaxMonoidal.CommShift`) and of
  the action of the tensor product of `A` on morphisms
  (`CategoryTheory.MonoidalCategory.TensorCommShift`); and
  `CategoryTheory.Adjunction.commShift_externalMateTransposeSnd`,
  `CategoryTheory.Adjunction.commShift_externalMateNatTransSnd'`, the same for the other reading.

## Implementation notes

The shift compatibility is obtained in two steps.  `externalMate` is by definition the transpose
along `adj` of the composite `externalMateTranspose`, so
`CategoryTheory.Adjunction.natTrans_commShift_of_homEquiv_symm` carries the shift compatibility of
that composite to the mate; that is `commShift_externalMateNatTransFst`, which takes the shift
compatibility of the composite as a hypothesis.  The composite is then decomposed by
`externalMateTranspose_eq`, in which every factor except the tensorator of `R` is a whiskering, an
associator or a unitor, and the hypothesis is discharged from
`CategoryTheory.Functor.LaxMonoidal.CommShift` -- the shift compatibility of that tensorator,
which is a condition on `R` and not a theorem -- together with
`CategoryTheory.MonoidalCategory.TensorCommShift`.

## References

* [Stacks Project, Tag 08QB](https://stacks.math.columbia.edu/tag/08QB)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

universe v₁ v₂ v vE u₁ u₂ u uE

variable {A₁ : Type u₁} [Category.{v₁} A₁] {A₂ : Type u₂} [Category.{v₂} A₂]
  {A : Type u} [Category.{v} A] {E : Type uE} [Category.{vE} E]
  [MonoidalCategory A] [MonoidalCategory E]
  {L : A ⥤ E} {R : E ⥤ A} (adj : L ⊣ R) [R.LaxMonoidal]
  {L₁ : A₁ ⥤ E} {R₁ : E ⥤ A₁} (adj₁ : L₁ ⊣ R₁)
  {L₂ : A₂ ⥤ E} {R₂ : E ⥤ A₂} (adj₂ : L₂ ⊣ R₂)
  (S₁ : A₁ ⥤ A) (S₂ : A₂ ⥤ A) (α₁ : R₁ ⋙ S₁ ⟶ R) (α₂ : R₂ ⋙ S₂ ⟶ R)

/-- **The defining property of the two-variable mate characterises it.**  Any morphism whose
transpose along `adj` is the composite of `(α₁ ∘ S₁ η₁) ⊗ (α₂ ∘ S₂ η₂)` with the tensorator of
`R` *is* the two-variable mate; the transpose along an adjunction is a bijection.

This is the form in which the mate is computed at a particular pair of objects: exhibit a
morphism with the property above, and it is the mate. -/
lemma eq_externalMate_of_unit_comp_map (M₁ : A₁) (M₂ : A₂)
    (t : L.obj (S₁.obj M₁ ⊗ S₂.obj M₂) ⟶ L₁.obj M₁ ⊗ L₂.obj M₂)
    (ht : adj.unit.app (S₁.obj M₁ ⊗ S₂.obj M₂) ≫ R.map t =
      ((S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)) ⊗ₘ
          (S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))) ≫
        μ R (L₁.obj M₁) (L₂.obj M₂)) :
    t = externalMate adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂ := by
  apply (adj.homEquiv _ _).injective
  rw [homEquiv_unit, homEquiv_unit, ht, unit_comp_map_externalMate]

/-- **The two-variable mate is invertible as soon as some isomorphism has its defining
property.**  By `CategoryTheory.Adjunction.eq_externalMate_of_unit_comp_map` such an isomorphism
*is* the mate.

For a product of sites this is the statement that Stacks 08QB holds at a pair of objects as soon
as the identity of the lemma can be realised there by an isomorphism whose transpose is the
canonical composite -- which is what a computation at the compact generators produces. -/
lemma isIso_externalMate_of_unit_comp_map (M₁ : A₁) (M₂ : A₂)
    (t : L.obj (S₁.obj M₁ ⊗ S₂.obj M₂) ⟶ L₁.obj M₁ ⊗ L₂.obj M₂) [IsIso t]
    (ht : adj.unit.app (S₁.obj M₁ ⊗ S₂.obj M₂) ≫ R.map t =
      ((S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)) ⊗ₘ
          (S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))) ≫
        μ R (L₁.obj M₁) (L₂.obj M₂)) :
    IsIso (externalMate adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂) := by
  rw [← eq_externalMate_of_unit_comp_map adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂ t ht]
  infer_instance

/-- **The transpose of the two-variable mate at a fixed second object, as a natural
transformation in the first.**  Its value at `M₁` is the composite

`S₁ M₁ ⊗ S₂ M₂ ⟶ R (L₁ M₁) ⊗ R (L₂ M₂) ⟶ R (L₁ M₁ ⊗ L₂ M₂)`

of the introduction, and `CategoryTheory.Adjunction.externalMate` is its transpose along `adj`.
Naturality is the computation in the proof of
`CategoryTheory.Adjunction.externalMate_naturality` with the transpose not yet taken. -/
def externalMateTranspose (M₂ : A₂) :
    S₁ ⋙ tensorRight (S₂.obj M₂) ⟶ (L₁ ⋙ tensorRight (L₂.obj M₂)) ⋙ R where
  app M₁ := ((S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)) ⊗ₘ
    (S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))) ≫ μ R (L₁.obj M₁) (L₂.obj M₂)
  naturality {M₁ M₁'} f := by
    have hα₁ := α₁.naturality (L₁.map f)
    simp only [Functor.comp_map] at hα₁
    have h₁ : S₁.map f ≫ S₁.map (adj₁.unit.app M₁') ≫ α₁.app (L₁.obj M₁') =
        S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁) ≫ R.map (L₁.map f) := by
      rw [← Category.assoc, ← S₁.map_comp, ← adj₁.unit_naturality, S₁.map_comp, Category.assoc,
        hα₁]
    dsimp only [Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app]
    rw [← tensorHom_id, ← tensorHom_id]
    simp only [Category.assoc]
    rw [← μ_natural]
    simp only [← Category.assoc, tensorHom_comp_tensorHom]
    simp only [Category.assoc, h₁, Category.id_comp, Category.comp_id,
      CategoryTheory.Functor.map_id]

/-- Naturality of the unit of an adjunction followed by that of a comparison `α`. -/
private lemma map_comp_unit_comp_app_naturality {C : Type u} [Category.{v} C]
    {D : Type uE} [Category.{vE} D] {F : A₁ ⥤ D} {G : D ⥤ A₁} (a : F ⊣ G) (S : A₁ ⥤ C)
    {R' : D ⥤ C} (α : G ⋙ S ⟶ R') {M M' : A₁} (f : M ⟶ M') :
    S.map f ≫ S.map (a.unit.app M') ≫ α.app (F.obj M') =
      S.map (a.unit.app M) ≫ α.app (F.obj M) ≫ R'.map (F.map f) := by
  have hα := α.naturality (F.map f)
  simp only [Functor.comp_map] at hα
  rw [← Category.assoc, ← S.map_comp, ← a.unit_naturality, S.map_comp, Category.assoc, hα]

/-- **The two-variable mate is natural in both variables.**  Composing it with the image under
`L` of a tensor product of morphisms `S₁ f₁ ⊗ S₂ f₂` is the same as composing the other mate
with `L₁ f₁ ⊗ L₂ f₂`; so the two-variable mates assemble into a morphism of bifunctors from
`(M₁, M₂) ↦ L (S₁ M₁ ⊗ S₂ M₂)` to `(M₁, M₂) ↦ L₁ M₁ ⊗ L₂ M₂`. -/
@[reassoc]
lemma externalMate_naturality {M₁ M₁' : A₁} {M₂ M₂' : A₂} (f₁ : M₁ ⟶ M₁') (f₂ : M₂ ⟶ M₂') :
    L.map (S₁.map f₁ ⊗ₘ S₂.map f₂) ≫ externalMate adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁' M₂' =
      externalMate adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂ ≫ (L₁.map f₁ ⊗ₘ L₂.map f₂) := by
  have h₁ := map_comp_unit_comp_app_naturality adj₁ S₁ α₁ f₁
  have h₂ := map_comp_unit_comp_app_naturality adj₂ S₂ α₂ f₂
  apply (adj.homEquiv _ _).injective
  simp only [homEquiv_unit, Functor.map_comp, ← Category.assoc, unit_naturality]
  simp only [Category.assoc, unit_comp_map_externalMate]
  rw [← μ_natural]
  simp only [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, h₁, h₂]

/-- **The two-variable mate at a fixed second object, as a natural transformation in the first.**
This is `CategoryTheory.Adjunction.externalMate_naturality` with the second morphism taken to be
the identity; it is the shape in which a dévissage of the comparison in one variable reads it. -/
def externalMateNatTransFst (M₂ : A₂) :
    (S₁ ⋙ tensorRight (S₂.obj M₂)) ⋙ L ⟶ L₁ ⋙ tensorRight (L₂.obj M₂) where
  app M₁ := externalMate adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂
  naturality {M₁ M₁'} f := by
    dsimp only [Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app]
    rw [← tensorHom_id, ← tensorHom_id, ← S₂.map_id,
      externalMate_naturality adj adj₁ adj₂ S₁ S₂ α₁ α₂ f (𝟙 M₂), L₂.map_id]

/-- The one-variable mate is the transpose of
`CategoryTheory.Adjunction.externalMateTranspose`, componentwise. -/
lemma externalMateNatTransFst_app (M₂ : A₂) (M₁ : A₁) :
    (externalMateNatTransFst adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₂).app M₁ =
      (adj.homEquiv _ _).symm
        ((externalMateTranspose adj₁ adj₂ S₁ S₂ α₁ α₂ M₂).app M₁) :=
  rfl

/-- **The transpose of the two-variable mate at a fixed first object, as a natural
transformation in the second.**  Its value at `M₂` is the same composite

`S₁ M₁ ⊗ S₂ M₂ ⟶ R (L₁ M₁) ⊗ R (L₂ M₂) ⟶ R (L₁ M₁ ⊗ L₂ M₂)`

as `CategoryTheory.Adjunction.externalMateTranspose`, read in the other variable; naturality is
the computation in the proof of `CategoryTheory.Adjunction.externalMate_naturality` with the
transpose not yet taken and the first morphism an identity. -/
def externalMateTransposeSnd (M₁ : A₁) :
    S₂ ⋙ tensorLeft (S₁.obj M₁) ⟶ (L₂ ⋙ tensorLeft (L₁.obj M₁)) ⋙ R where
  app M₂ := ((S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)) ⊗ₘ
    (S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))) ≫ μ R (L₁.obj M₁) (L₂.obj M₂)
  naturality {M₂ M₂'} f := by
    have hα₂ := α₂.naturality (L₂.map f)
    simp only [Functor.comp_map] at hα₂
    have h₂ : S₂.map f ≫ S₂.map (adj₂.unit.app M₂') ≫ α₂.app (L₂.obj M₂') =
        S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂) ≫ R.map (L₂.map f) := by
      rw [← Category.assoc, ← S₂.map_comp, ← adj₂.unit_naturality, S₂.map_comp, Category.assoc,
        hα₂]
    dsimp only [Functor.comp_map, curriedTensor_obj_map]
    rw [← id_tensorHom, ← id_tensorHom]
    simp only [Category.assoc]
    rw [← μ_natural]
    simp only [← Category.assoc, tensorHom_comp_tensorHom]
    simp only [Category.assoc, h₂, Category.id_comp, Category.comp_id,
      CategoryTheory.Functor.map_id]

/-- **The two-variable mate at a fixed first object, as a natural transformation in the second.**
This is `CategoryTheory.Adjunction.externalMate_naturality` with the first morphism taken to be
the identity; it is the shape in which a dévissage of the comparison in the second variable reads
it, and the companion of `CategoryTheory.Adjunction.externalMateNatTransFst`. -/
def externalMateNatTransSnd (M₁ : A₁) :
    (S₂ ⋙ tensorLeft (S₁.obj M₁)) ⋙ L ⟶ L₂ ⋙ tensorLeft (L₁.obj M₁) where
  app M₂ := externalMate adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂
  naturality {M₂ M₂'} f := by
    dsimp only [Functor.comp_map, curriedTensor_obj_map]
    rw [← id_tensorHom, ← id_tensorHom, ← S₁.map_id,
      externalMate_naturality adj adj₁ adj₂ S₁ S₂ α₁ α₂ (𝟙 M₁) f, L₁.map_id]

/-- The mate read in the second variable is the transpose of
`CategoryTheory.Adjunction.externalMateTransposeSnd`, componentwise. -/
lemma externalMateNatTransSnd_app (M₁ : A₁) (M₂ : A₂) :
    (externalMateNatTransSnd adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁).app M₂ =
      (adj.homEquiv _ _).symm
        ((externalMateTransposeSnd adj₁ adj₂ S₁ S₂ α₁ α₂ M₁).app M₂) :=
  rfl

/-- **The transpose of the one-variable mate of `α₁`, as a natural transformation
`S₁ ⟶ L₁ ⋙ R`.**  Its value at `M₁` is `S₁(η₁ M₁) ≫ α₁`, the morphism whose transpose along
`adj` is the one-variable mate of `α₁`; naturality is the identity `h₁` that appears in the
proofs of `CategoryTheory.Adjunction.externalMateTranspose` and
`CategoryTheory.Adjunction.externalMate_naturality`, namely the naturality of the unit of `adj₁`
followed by that of `α₁`.

It is a composite of a unitor, a whiskering of `adj₁.unit` and a whiskering of `α₁`, which is
what makes it compatible with the shift as soon as `adj₁` and `α₁` are; see
`CategoryTheory.Adjunction.restrictionMateTranspose_eq`. -/
def restrictionMateTranspose : S₁ ⟶ L₁ ⋙ R where
  app M₁ := S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)
  naturality {M₁ M₁'} f := by
    have hα₁ := α₁.naturality (L₁.map f)
    simp only [Functor.comp_map] at hα₁
    dsimp only [Functor.comp_map]
    rw [Category.assoc, ← Category.assoc, ← S₁.map_comp, ← adj₁.unit_naturality, S₁.map_comp,
      Category.assoc, hα₁]

omit [MonoidalCategory A] [MonoidalCategory E] [R.LaxMonoidal] in
/-- The component of `CategoryTheory.Adjunction.restrictionMateTranspose` at `M₁` is
`S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)`. -/
@[simp]
lemma restrictionMateTranspose_app (M₁ : A₁) :
    (restrictionMateTranspose adj₁ S₁ α₁).app M₁ =
      S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁) :=
  rfl

omit [MonoidalCategory A] [MonoidalCategory E] [R.LaxMonoidal] in
/-- **The transpose of the one-variable mate, written as a composite of a unitor, a whiskering of
the unit of `adj₁` and a whiskering of `α₁`.**  Each factor of the right-hand side has
`CategoryTheory.NatTrans.CommShift` under the standing hypotheses, which is what
`CategoryTheory.Adjunction.commShift_restrictionMateTranspose` uses; the left-hand side, being an
anonymous constructor application, is not matched by instance search against it. -/
lemma restrictionMateTranspose_eq :
    restrictionMateTranspose adj₁ S₁ α₁ =
      (Functor.leftUnitor S₁).inv ≫ Functor.whiskerRight adj₁.unit S₁ ≫
        (Functor.associator L₁ R₁ S₁).hom ≫ Functor.whiskerLeft L₁ α₁ := by
  ext M₁
  simp

/-- **The transpose of the two-variable mate, decomposed into whiskerings, associators and the
tensorator of `R` read in one variable.**  At `M₁` the right-hand side is

`S₁ M₁ ⊗ S₂ M₂ ⟶ S₁ M₁ ⊗ R(L₂ M₂) ⟶ R(L₁ M₁) ⊗ R(L₂ M₂) ⟶ R(L₁ M₁ ⊗ L₂ M₂)`,

which is the definition of `CategoryTheory.Adjunction.externalMateTranspose` with
`CategoryTheory.MonoidalCategory.tensorHom_def'` applied to its first factor.  Every factor
except the last is a whiskering of a transformation whose shift compatibility is standard; the
last is `CategoryTheory.Functor.LaxMonoidal.μNatTransFst`, and its shift compatibility is the
content of `CategoryTheory.Functor.LaxMonoidal.CommShift`. -/
lemma externalMateTranspose_eq (M₂ : A₂) :
    externalMateTranspose adj₁ adj₂ S₁ S₂ α₁ α₂ M₂ =
      Functor.whiskerLeft S₁ ((curriedTensor A).flip.map
            (S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))) ≫
        Functor.whiskerRight (restrictionMateTranspose adj₁ S₁ α₁)
            (tensorRight (R.obj (L₂.obj M₂))) ≫
          (Functor.associator L₁ R (tensorRight (R.obj (L₂.obj M₂)))).hom ≫
            Functor.whiskerLeft L₁ (Functor.LaxMonoidal.μNatTransFst R (L₂.obj M₂)) ≫
              (Functor.associator L₁ (tensorRight (L₂.obj M₂)) R).inv := by
  ext M₁
  change ((S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)) ⊗ₘ
      (S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))) ≫ μ R (L₁.obj M₁) (L₂.obj M₂) = _
  rw [tensorHom_def']
  simp [Functor.LaxMonoidal.μNatTransFst]

/-- **The transpose of the two-variable mate read in the second variable, decomposed into
whiskerings, associators and the tensorator of `R` read in one variable.**  At `M₂` the
right-hand side is

`S₁ M₁ ⊗ S₂ M₂ ⟶ R(L₁ M₁) ⊗ S₂ M₂ ⟶ R(L₁ M₁) ⊗ R(L₂ M₂) ⟶ R(L₁ M₁ ⊗ L₂ M₂)`,

which is the definition of `CategoryTheory.Adjunction.externalMateTransposeSnd` with
`CategoryTheory.MonoidalCategory.tensorHom_def` applied to its first factor -- the companion of
`CategoryTheory.Adjunction.externalMateTranspose_eq`, where the other decomposition
`tensorHom_def'` is used.  The last factor is
`CategoryTheory.Functor.LaxMonoidal.μNatTransSnd`, whose shift compatibility is the second field
of `CategoryTheory.Functor.LaxMonoidal.CommShift`. -/
lemma externalMateTransposeSnd_eq (M₁ : A₁) :
    externalMateTransposeSnd adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ =
      Functor.whiskerLeft S₂ ((curriedTensor A).map
            (S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁))) ≫
        Functor.whiskerRight (restrictionMateTranspose adj₂ S₂ α₂)
            (tensorLeft (R.obj (L₁.obj M₁))) ≫
          (Functor.associator L₂ R (tensorLeft (R.obj (L₁.obj M₁)))).hom ≫
            Functor.whiskerLeft L₂ (Functor.LaxMonoidal.μNatTransSnd R (L₁.obj M₁)) ≫
              (Functor.associator L₂ (tensorLeft (L₁.obj M₁)) R).inv := by
  ext M₂
  change ((S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)) ⊗ₘ
      (S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))) ≫ μ R (L₁.obj M₁) (L₂.obj M₂) = _
  rw [tensorHom_def]
  simp [Functor.LaxMonoidal.μNatTransSnd]

section CommShift

variable (T : Type*) [AddMonoid T] [HasShift A₁ T] [HasShift A T] [HasShift E T]
  [L.CommShift T] [R.CommShift T] [adj.CommShift T]

/-- **The one-variable mate is compatible with the shift as soon as its transpose is.**  The mate
is by definition the transpose along `adj` of
`CategoryTheory.Adjunction.externalMateTranspose`, and the transpose along a shift-compatible
adjunction carries shift-compatible transformations to shift-compatible transformations
(`CategoryTheory.Adjunction.natTrans_commShift_of_homEquiv_symm`).

`CategoryTheory.NatTrans.commShift_mateEquiv_symm` does not apply: that lemma is about the mate of
a 2-square, i.e. the one-variable mate, whereas the transformation here is built from the
tensorator of `R`.  The hypothesis is exactly the shift compatibility of that tensorator in one
variable, packaged with the whiskerings it is composed with. -/
lemma commShift_externalMateNatTransFst (M₂ : A₂)
    [(S₁ ⋙ tensorRight (S₂.obj M₂)).CommShift T]
    [(L₁ ⋙ tensorRight (L₂.obj M₂)).CommShift T]
    [NatTrans.CommShift (externalMateTranspose adj₁ adj₂ S₁ S₂ α₁ α₂ M₂) T] :
    NatTrans.CommShift (externalMateNatTransFst adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₂) T :=
  natTrans_commShift_of_homEquiv_symm T adj (S₁ ⋙ tensorRight (S₂.obj M₂))
    (L₁ ⋙ tensorRight (L₂.obj M₂)) (externalMateTranspose adj₁ adj₂ S₁ S₂ α₁ α₂ M₂) _
    (externalMateNatTransFst_app adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₂)

section Transpose

variable [S₁.CommShift T] [L₁.CommShift T] [R₁.CommShift T] [adj₁.CommShift T]
  [NatTrans.CommShift α₁ T]
  [∀ X : E, (tensorLeft X).CommShift T] [∀ Y : E, (tensorRight Y).CommShift T]
  [∀ X : A, (tensorLeft X).CommShift T] [∀ Y : A, (tensorRight Y).CommShift T]
  [MonoidalCategory.TensorCommShift A T] [Functor.LaxMonoidal.CommShift R T]

/-- **The transpose of the one-variable mate of `α₁` is compatible with the shift.**  By
`CategoryTheory.Adjunction.restrictionMateTranspose_eq` it is a unitor, a whiskering of the unit
of `adj₁` and a whiskering of `α₁`; the first has
`CategoryTheory.NatTrans.CommShift` unconditionally, the second by `adj₁.CommShift`, and the
third by the hypothesis on `α₁`. -/
instance commShift_restrictionMateTranspose :
    NatTrans.CommShift (restrictionMateTranspose adj₁ S₁ α₁) T := by
  rw [restrictionMateTranspose_eq]
  infer_instance

/-- **The transpose of the two-variable mate is compatible with the shift.**  This is the
remaining obligation of `CategoryTheory.Adjunction.commShift_externalMateNatTransFst`, and it is
discharged here from the shift compatibility of the tensorator of `R`
(`CategoryTheory.Functor.LaxMonoidal.CommShift`) together with the shift compatibility of the
action of the tensor product of `A` on morphisms
(`CategoryTheory.MonoidalCategory.TensorCommShift`): by
`CategoryTheory.Adjunction.externalMateTranspose_eq` the transpose is a composite in which those
two are the only factors that are not whiskerings of transformations whose shift compatibility is
standard. -/
instance commShift_externalMateTranspose (M₂ : A₂) :
    NatTrans.CommShift (externalMateTranspose adj₁ adj₂ S₁ S₂ α₁ α₂ M₂) T := by
  rw [externalMateTranspose_eq]
  infer_instance

/-- **The two-variable mate at a fixed second object is compatible with the shift**, as a
natural transformation in the first.  This is
`CategoryTheory.Adjunction.commShift_externalMateNatTransFst` with its hypothesis on the
transpose discharged by `CategoryTheory.Adjunction.commShift_externalMateTranspose`, so the
only monoidal input left is the shift compatibility of the tensorator of `R`.

This is the shape a dévissage of the comparison of Stacks 08QB in one variable consumes: the
subcategory of objects at which a shift-compatible morphism of exact coproduct-preserving
functors is invertible is closed under the shift, which is what lets the comparison be tested on
a generating family. -/
instance commShift_externalMateNatTransFst' (M₂ : A₂) :
    NatTrans.CommShift (externalMateNatTransFst adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₂) T :=
  commShift_externalMateNatTransFst adj adj₁ adj₂ S₁ S₂ α₁ α₂ T M₂

end Transpose

end CommShift

section CommShiftSnd

variable (T : Type*) [AddMonoid T] [HasShift A₂ T] [HasShift A T] [HasShift E T]
  [L.CommShift T] [R.CommShift T] [adj.CommShift T]

/-- **The mate read in the second variable is compatible with the shift as soon as its transpose
is.**  The companion of `CategoryTheory.Adjunction.commShift_externalMateNatTransFst`: the mate
is by definition the transpose along `adj` of
`CategoryTheory.Adjunction.externalMateTransposeSnd`, and the transpose along a shift-compatible
adjunction carries shift-compatible transformations to shift-compatible transformations. -/
lemma commShift_externalMateNatTransSnd (M₁ : A₁)
    [(S₂ ⋙ tensorLeft (S₁.obj M₁)).CommShift T]
    [(L₂ ⋙ tensorLeft (L₁.obj M₁)).CommShift T]
    [NatTrans.CommShift (externalMateTransposeSnd adj₁ adj₂ S₁ S₂ α₁ α₂ M₁) T] :
    NatTrans.CommShift (externalMateNatTransSnd adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁) T :=
  natTrans_commShift_of_homEquiv_symm T adj (S₂ ⋙ tensorLeft (S₁.obj M₁))
    (L₂ ⋙ tensorLeft (L₁.obj M₁)) (externalMateTransposeSnd adj₁ adj₂ S₁ S₂ α₁ α₂ M₁) _
    (externalMateNatTransSnd_app adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁)

section Transpose

variable [S₂.CommShift T] [L₂.CommShift T] [R₂.CommShift T] [adj₂.CommShift T]
  [NatTrans.CommShift α₂ T]
  [∀ X : E, (tensorLeft X).CommShift T] [∀ Y : E, (tensorRight Y).CommShift T]
  [∀ X : A, (tensorLeft X).CommShift T] [∀ Y : A, (tensorRight Y).CommShift T]
  [MonoidalCategory.TensorCommShift A T] [Functor.LaxMonoidal.CommShift R T]

/-- **The transpose of the two-variable mate read in the second variable is compatible with the
shift.**  By `CategoryTheory.Adjunction.externalMateTransposeSnd_eq` it is a composite in which
the only factors that are not whiskerings of transformations whose shift compatibility is
standard are the action of the tensor product of `A` on morphisms
(`CategoryTheory.MonoidalCategory.TensorCommShift`) and the tensorator of `R` read in its second
variable, whose shift compatibility is the field
`CategoryTheory.Functor.LaxMonoidal.CommShift.commShift_μNatTransSnd`. -/
instance commShift_externalMateTransposeSnd (M₁ : A₁) :
    NatTrans.CommShift (externalMateTransposeSnd adj₁ adj₂ S₁ S₂ α₁ α₂ M₁) T := by
  rw [externalMateTransposeSnd_eq]
  infer_instance

/-- **The two-variable mate at a fixed first object is compatible with the shift**, as a natural
transformation in the second.  This is the shape a dévissage of the comparison of Stacks 08QB in
the *second* variable consumes, and with
`CategoryTheory.Adjunction.commShift_externalMateNatTransFst'` it is what reduces that comparison
to a computation at a pair of generators: one dévissage in each variable. -/
instance commShift_externalMateNatTransSnd' (M₁ : A₁) :
    NatTrans.CommShift (externalMateNatTransSnd adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁) T :=
  commShift_externalMateNatTransSnd adj adj₁ adj₂ S₁ S₂ α₁ α₂ T M₁

end Transpose

end CommShiftSnd

end CategoryTheory.Adjunction

end
