module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor

/-!
# The symmetric monoidal derived category

For a commutative ring `R`, the derived category of `R`-modules is symmetric monoidal under
derived tensor product. Its associator is induced by the ordinary associator of total tensor
products of K-flat complexes, and its braiding is induced by the Koszul signed interchange map.

## Main results

* `DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory`: the derived category
  `D(R)` carries a symmetric monoidal structure whose tensor bifunctor is naturally isomorphic
  to the canonical derived tensor product, whose braiding is the canonical Koszul symmetry, and
  whose associator is induced by the ordinary associator of complexes under the K-flat
  comparisons.

## Implementation notes

Everything is built on the providers of the derived tensor product rather than reconstructed
here: `CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct` (Stacks 0BYI)
supplies the bifunctor, its comparison with total tensor products of K-flat complexes, its right
unitor and its Koszul symmetry, and
`CochainComplex.DerivedTensor.derivedTensorProduct_associator` (Stacks 0BYJ) supplies the
associator. The monoidal coherence laws are then checked by transporting the corresponding laws
for complexes along K-flat representatives, which exist by
`CochainComplex.KFlat.exists_kFlat_resolution` (Stacks 06Y4) and are closed under tensor product
by `CochainComplex.KFlat.tensor` (Stacks 0795).

`CochainComplex.KFlat.exists_kFlat_resolution` is stated for module universes `max u v` above
the universe of the ring. Only the diagonal case `v = u` is needed here, and it is used through
`CochainComplex.KFlat.exists_kFlat_representative`, which packages a resolution of a complex
representing a given object of the derived category as a representative together with an
isomorphism.

## References

* [The Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace DerivedCategory.Invertible

attribute [local instance] HasDerivedCategory.standard

/-- The Koszul formula determines a morphism between total tensor products uniquely. -/
theorem isKoszulSwap_unique {R : Type u} [CommRing R]
    (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    {f g : (K ⊗ L) ⟶ (L ⊗ K)}
    (hf : CochainComplex.DerivedTensor.IsKoszulSwap K L f)
    (hg : CochainComplex.DerivedTensor.IsKoszulSwap K L g) : f = g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [hf p q n h, hg p q n h]

/-- The tensor unit complex is K-flat. -/
private theorem kFlat_unit {R : Type u} [CommRing R] :
    (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).KFlat := by
  intro M hM
  exact HomologicalComplex.Acyclic.of_iso (rightUnitor M).symm hM

/-- On K-flat representatives, the derived braiding is induced by the Koszul braiding of
complexes. -/
theorem braiding_comparison (R : Type u) [CommRing R] :
    let T := CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct R
    ∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
      (hK : K.KFlat) (hL : L.KFlat),
      (T.braiding.iso.hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        (T.tensorProduct.comparison L K hL hK).hom =
      (T.tensorProduct.comparison K L hK hL).hom ≫
        DerivedCategory.Q.map
          ((TotalTensorComplex.cochainComplex_symmetricMonoidalCategory
            R).choose.toBraidedCategory.braiding K L).hom := by
  intro T K L hK hL
  obtain ⟨f, hf, hQf⟩ := T.braiding.isKoszul K L hK hL
  let sC := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose
  have hβ : CochainComplex.DerivedTensor.IsKoszulSwap K L
      (sC.toBraidedCategory.braiding K L).hom :=
    (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose_spec K L
  rw [isKoszulSwap_unique K L hf hβ] at hQf
  rw [← cancel_epi (T.tensorProduct.comparison K L hK hL).inv]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hQf.symm

private theorem leftUnitor_comparison (R : Type u) [CommRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) :
    let T := CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct R
    let U : CochainComplex (ModuleCat.{u} R) ℤ := 𝟙_ _
    (T.tensorProduct.comparison U L kFlat_unit hL).hom ≫
      DerivedCategory.Q.map (leftUnitor L).hom =
    ((T.braiding.iso.app (DerivedCategory.Q.obj U)).app (DerivedCategory.Q.obj L)).hom ≫
      T.tensorProduct.rightUnitor.hom.app (DerivedCategory.Q.obj L) := by
  intro T U
  let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose
  -- The complex left unitor is the braiding followed by the right unitor.
  calc
    (T.tensorProduct.comparison U L kFlat_unit hL).hom ≫
        DerivedCategory.Q.map (leftUnitor L).hom =
      (T.tensorProduct.comparison U L kFlat_unit hL).hom ≫
        DerivedCategory.Q.map ((β_ U L).hom ≫ (rightUnitor L).hom) := by
          rw [braiding_rightUnitor]
    _ = ((T.braiding.iso.app (DerivedCategory.Q.obj U)).app (DerivedCategory.Q.obj L)).hom ≫
      T.tensorProduct.rightUnitor.hom.app (DerivedCategory.Q.obj L) := by
        rw [Functor.map_comp, ← Category.assoc, ← braiding_comparison R U L kFlat_unit hL,
          Category.assoc, T.tensorProduct.rightUnitor_comparison L hL kFlat_unit]
        simp only [Iso.app_hom]
        dsimp only [T]

/-- The derived tensor product, unit, and canonical constraints provide the underlying data for
the monoidal structure. -/
private noncomputable abbrev derivedMonoidalStruct (R : Type u) [CommRing R] :
    MonoidalCategoryStruct (DerivedCategory (ModuleCat.{u} R)) := by
  let T := CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct R
  let unit := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let a := (CochainComplex.DerivedTensor.derivedTensorProduct_associator R).choose
  exact
    { tensorObj := fun K L => (T.tensorProduct.tensor.obj K).obj L
      whiskerLeft := fun K _ _ g => (T.tensorProduct.tensor.obj K).map g
      whiskerRight := fun f L => (T.tensorProduct.tensor.map f).app L
      tensorHom := fun f g => (T.tensorProduct.tensor.map f).app _ ≫
        (T.tensorProduct.tensor.obj _).map g
      tensorUnit := unit
      associator := a
      rightUnitor := fun K => T.tensorProduct.rightUnitor.app K
      leftUnitor := fun K => ((T.braiding.iso.app unit).app K) ≪≫
        T.tensorProduct.rightUnitor.app K }

section Coherence

variable {R : Type u} [CommRing R]

private abbrev Complex (R : Type u) [CommRing R] :=
  CochainComplex (ModuleCat.{u} R) ℤ

local notation "D" => CochainComplex.DerivedTensor.DObj R
local notation "C" => Complex R
local notation "Q" => (DerivedCategory.Q : C ⥤ D)
local notation "T" => CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R

attribute [local instance] derivedMonoidalStruct

private theorem tensor_id (X Y : D) : (𝟙 X) ⊗ₘ (𝟙 Y) = 𝟙 (X ⊗ Y) := by
  show ((T).tensor.map (𝟙 X)).app Y ≫ ((T).tensor.obj X).map (𝟙 Y) =
    𝟙 (((T).tensor.obj X).obj Y)
  simp

private theorem tensor_comp {X Y Z X' Y' Z' : D}
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : Y ⟶ Z) (k : Y' ⟶ Z') :
    (f ⊗ₘ g) ≫ (h ⊗ₘ k) = (f ≫ h) ⊗ₘ (g ≫ k) :=
  ((Functor.uncurry.obj (T).tensor).map_comp
    (X := (X, X')) (Y := (Y, Y')) (Z := (Z, Z')) (f, g) (h, k)).symm

private theorem tensor_id_left (X : D) {Y Z : D} (f : Y ⟶ Z) :
    (𝟙 X) ⊗ₘ f = X ◁ f := by
  show ((T).tensor.map (𝟙 X)).app Y ≫ ((T).tensor.obj X).map f =
    ((T).tensor.obj X).map f
  simp

private theorem tensor_id_right {X Y : D} (f : X ⟶ Y) (Z : D) :
    f ⊗ₘ (𝟙 Z) = f ▷ Z := by
  show ((T).tensor.map f).app Z ≫ ((T).tensor.obj Y).map (𝟙 Z) =
    ((T).tensor.map f).app Z
  simp

private theorem assoc_naturality {X Y Z X' Y' Z' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X' Y' Z').hom =
      (α_ X Y Z).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
  simpa only [tensorHom, MonoidalCategory.associator, tensorObj, derivedMonoidalStruct,
    Category.assoc] using
    (CochainComplex.DerivedTensor.derivedTensorProduct_associator R).choose_spec.1 f g h

private abbrev swap (X Y : D) : X ⊗ Y ≅ Y ⊗ X :=
  (((CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct
    R).braiding.iso.app X).app Y)

private theorem swap_naturality {X Y X' Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (swap X' Y').hom = (swap X Y).hom ≫ (g ⊗ₘ f) := by
  let b := (CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct
    R).braiding.iso.hom
  show (((T).tensor.map f).app Y ≫ ((T).tensor.obj X').map g) ≫ (b.app X').app Y' =
    (b.app X).app Y ≫ (((T).tensor.map g).app X ≫ ((T).tensor.obj Y').map f)
  simp only [Category.assoc]
  rw [← Category.assoc, Category.assoc, (b.app X').naturality g]
  have hn := congrArg (fun t => t.app Y) (b.naturality f)
  change ((T).tensor.map f).app Y ≫ (b.app X').app Y =
    (b.app X).app Y ≫ ((T).tensor.obj Y).map f at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  show ((b.app X).app Y ≫ ((T).tensor.obj Y).map f) ≫
      ((T).tensor.map g).app X' =
    ((b.app X).app Y ≫ ((T).tensor.map g).app X) ≫ ((T).tensor.obj Y').map f
  simpa only [Category.assoc] using
    congrArg (fun t => (b.app X).app Y ≫ t) (((T).tensor.map g).naturality f)

private theorem right_naturality {X Y : D} (f : X ⟶ Y) :
    (f ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  rw [tensor_id_right]
  exact (T).rightUnitor.hom.naturality f

private theorem left_naturality {X Y : D} (f : X ⟶ Y) :
    (𝟙 (𝟙_ D) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  show (𝟙 (𝟙_ D) ⊗ₘ f) ≫ ((swap (𝟙_ D) Y).hom ≫ (ρ_ Y).hom) =
    ((swap (𝟙_ D) X).hom ≫ (ρ_ X).hom) ≫ f
  rw [← Category.assoc, swap_naturality, Category.assoc, right_naturality, Category.assoc]

/-- A K-flat complex representing a specified derived object. -/
private structure Representative (X : D) where
  complex : C
  flat : complex.KFlat
  iso : X ≅ (Q).obj complex

private def representative (X : D) : Representative X := by
  let h := CochainComplex.KFlat.exists_kFlat_representative (R := R) X
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.some.symm⟩

private abbrev Representative.tensor {X Y : D} (A : Representative X) (B : Representative Y) :
    Representative (X ⊗ Y) where
  complex := A.complex ⊗ B.complex
  flat := CochainComplex.KFlat.tensor R _ _ A.flat B.flat
  iso := (Functor.uncurry.obj (T).tensor).mapIso (A.iso.prod B.iso) ≪≫
    (T).comparison _ _ A.flat B.flat

private abbrev unitRepresentative : Representative (𝟙_ D) where
  complex := 𝟙_ C
  flat := kFlat_unit
  iso := Iso.refl _

private theorem Representative.tensor_hom {X Y : D}
    (A : Representative X) (B : Representative Y) :
    (A.tensor B).iso.hom = (A.iso.hom ⊗ₘ B.iso.hom) ≫
      ((T).comparison _ _ A.flat B.flat).hom := rfl

/-- A morphism is represented by a chain map under the chosen comparisons. -/
private def Represents {X Y : D} (A : Representative X) (B : Representative Y)
    (f : X ⟶ Y) (g : A.complex ⟶ B.complex) : Prop :=
  f ≫ B.iso.hom = A.iso.hom ≫ (Q).map g

private theorem Represents.id {X : D} (A : Representative X) :
    Represents A A (𝟙 X) (𝟙 A.complex) := by
  simp [Represents]

private theorem Represents.comp {X Y Z : D} {A : Representative X}
    {B : Representative Y} {E : Representative Z} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : A.complex ⟶ B.complex} {g' : B.complex ⟶ E.complex}
    (hf : Represents A B f f') (hg : Represents B E g g') :
    Represents A E (f ≫ g) (f' ≫ g') := by
  dsimp [Represents] at *
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc, (Q).map_comp]

private theorem Represents.eq {X Y : D} {A : Representative X} {B : Representative Y}
    {f g : X ⟶ Y} {f' g' : A.complex ⟶ B.complex}
    (hf : Represents A B f f') (hg : Represents A B g g') (h : f' = g') : f = g := by
  subst h
  exact (cancel_mono B.iso.hom).1 (hf.trans hg.symm)

private theorem Represents.tensor {X Y X' Y' : D}
    {A : Representative X} {B : Representative Y}
    {A' : Representative X'} {B' : Representative Y'}
    {f : X ⟶ X'} {g : Y ⟶ Y'}
    {f' : A.complex ⟶ A'.complex} {g' : B.complex ⟶ B'.complex}
    (hf : Represents A A' f f') (hg : Represents B B' g g') :
    Represents (A.tensor B) (A'.tensor B') (f ⊗ₘ g) (f' ⊗ₘ g') := by
  change f ≫ A'.iso.hom = A.iso.hom ≫ (Q).map f' at hf
  change g ≫ B'.iso.hom = B.iso.hom ≫ (Q).map g' at hg
  rw [Represents, Representative.tensor_hom, Representative.tensor_hom, ← Category.assoc,
    tensor_comp, hf, hg, ← tensor_comp, Category.assoc, Category.assoc]
  congr 1
  simpa only [tensorHom, derivedMonoidalStruct, Category.assoc] using
    (T).comparison_naturality f' g' A.flat A'.flat B.flat B'.flat

private theorem tensor_comp_right {X X' Y Y' Y'' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Y' ⟶ Y'') :
    f ⊗ₘ (g ≫ h) = (f ⊗ₘ g) ≫ (𝟙 X' ⊗ₘ h) := by
  rw [tensor_comp, Category.comp_id]

private theorem tensor_comp_left {X X' X'' Y Y' : D}
    (f : X ⟶ X') (g : X' ⟶ X'') (h : Y ⟶ Y') :
    (f ≫ g) ⊗ₘ h = (f ⊗ₘ h) ≫ (g ⊗ₘ 𝟙 Y') := by
  rw [tensor_comp, Category.comp_id]

private theorem Represents.associator {X Y Z : D}
    (A : Representative X) (B : Representative Y) (E : Representative Z) :
    Represents ((A.tensor B).tensor E) (A.tensor (B.tensor E))
      (α_ X Y Z).hom (α_ A.complex B.complex E.complex).hom := by
  rw [Represents, Representative.tensor_hom, Representative.tensor_hom,
    Representative.tensor_hom, Representative.tensor_hom]
  simp only [tensor_comp_left, tensor_comp_right, Category.assoc]
  rw [← reassoc_of% (assoc_naturality A.iso.hom B.iso.hom E.iso.hom)]
  congr 1
  simp only [tensor_id_left, tensor_id_right]
  exact (CochainComplex.DerivedTensor.derivedTensorProduct_associator R).choose_spec.2
      A.complex B.complex E.complex A.flat B.flat E.flat

private theorem Represents.rightUnitor {X : D} (A : Representative X) :
    Represents (A.tensor unitRepresentative) A (ρ_ X).hom (ρ_ A.complex).hom := by
  show (ρ_ X).hom ≫ A.iso.hom =
    ((A.iso.hom ⊗ₘ 𝟙 (𝟙_ D)) ≫
      ((T).comparison A.complex (𝟙_ C) A.flat kFlat_unit).hom) ≫
        (Q).map (ρ_ A.complex).hom
  rw [Category.assoc, (T).rightUnitor_comparison]
  exact (right_naturality A.iso.hom).symm

private theorem Represents.leftUnitor {X : D} (A : Representative X) :
    Represents (unitRepresentative.tensor A) A (λ_ X).hom (λ_ A.complex).hom := by
  show (λ_ X).hom ≫ A.iso.hom =
    ((𝟙 (𝟙_ D) ⊗ₘ A.iso.hom) ≫
      ((T).comparison (𝟙_ C) A.complex kFlat_unit A.flat).hom) ≫
        (Q).map (λ_ A.complex).hom
  rw [Category.assoc, leftUnitor_comparison]
  exact (left_naturality A.iso.hom).symm

private theorem Represents.braiding {X Y : D} (A : Representative X) (B : Representative Y) :
    let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose
    Represents (A.tensor B) (B.tensor A) (swap X Y).hom (β_ A.complex B.complex).hom := by
  dsimp only [Represents]
  rw [Representative.tensor_hom, Representative.tensor_hom]
  rw [← reassoc_of% (swap_naturality A.iso.hom B.iso.hom), Category.assoc]
  congr 1
  exact braiding_comparison R A.complex B.complex A.flat B.flat

private theorem Represents.inv {X Y : D} {A : Representative X} {B : Representative Y}
    (f : X ≅ Y) (g : A.complex ≅ B.complex)
    (h : Represents A B f.hom g.hom) : Represents B A f.inv g.inv := by
  dsimp only [Represents] at *
  apply (cancel_epi f.hom).1
  simp only [← Category.assoc, h]
  simp only [Category.assoc, ← (Q).map_comp, Iso.hom_inv_id, (Q).map_id,
    Category.comp_id, Category.id_comp]

private theorem Represents.associator_inv {X Y Z : D}
    (A : Representative X) (B : Representative Y) (E : Representative Z) :
    Represents (A.tensor (B.tensor E)) ((A.tensor B).tensor E)
      (α_ X Y Z).inv (α_ A.complex B.complex E.complex).inv :=
  Represents.inv (A := (A.tensor B).tensor E) (B := A.tensor (B.tensor E))
    (α_ X Y Z) (α_ A.complex B.complex E.complex) (Represents.associator A B E)

private theorem derived_pentagon (W X Y Z : D) :
    ((α_ W X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫
        (𝟙 W ⊗ₘ (α_ X Y Z).hom) =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  let A := representative W
  let B := representative X
  let E := representative Y
  let F := representative Z
  apply Represents.eq
    (((Represents.associator A B E).tensor (Represents.id F)).comp
      ((Represents.associator A (B.tensor E) F).comp
        ((Represents.id A).tensor (Represents.associator B E F))))
    ((Represents.associator (A.tensor B) E F).comp
      (Represents.associator A B (E.tensor F)))
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
    MonoidalCategory.pentagon A.complex B.complex E.complex F.complex

private theorem derived_triangle (X Y : D) :
    (α_ X (𝟙_ D) Y).hom ≫ (𝟙 X ⊗ₘ (λ_ Y).hom) = (ρ_ X).hom ⊗ₘ 𝟙 Y := by
  let A := representative X
  let B := representative Y
  apply Represents.eq
    ((Represents.associator A unitRepresentative B).comp
      ((Represents.id A).tensor (Represents.leftUnitor B)))
    ((Represents.rightUnitor A).tensor (Represents.id B))
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
    MonoidalCategory.triangle A.complex B.complex

/-- The canonical derived tensor and constraints satisfy the monoidal coherence laws. -/
@[instance_reducible]
private def derivedMonoidalCategory : MonoidalCategory D :=
  MonoidalCategory.ofTensorHom
    tensor_id tensor_id_left tensor_id_right tensor_comp assoc_naturality
    left_naturality right_naturality derived_pentagon derived_triangle

/-- **The right unit of the derived tensor product passes through the associator.** The inverse
right unit on `X ⊗ᴸ Y`, followed by the associator, is `X ⊗ᴸ -` applied to the inverse right unit
on `Y`.

This is the unit half of the monoidal coherence of `D(R)`, which the K-flat comparison laws of
`CochainComplex.DerivedTensor.derivedTensorProduct_associator` and the `rightUnitor_comparison`
field do not state directly. It is what identifies the canonical map `K ⟶ K ⊗ᴸ N` at a tensor
product `K = X ⊗ᴸ Y` with the one at `Y`, which is the compatibility the reduction maps of a
tower `n ↦ K ⊗ᴸ A/Iⁿ` need in order to be recognized after the associativity rewrite. -/
public theorem rightUnitor_inv_comp_associator (X Y : D) :
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).rightUnitor.inv.app
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj X).obj Y) ≫
        ((CochainComplex.DerivedTensor.derivedTensorProduct_associator R).choose X Y
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).hom =
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj X).map
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).rightUnitor.inv.app Y) := by
  let := derivedMonoidalCategory (R := R)
  exact (MonoidalCategory.whiskerLeft_rightUnitor_inv X Y).symm

private theorem derived_hexagon_forward (X Y Z : D) :
    (α_ X Y Z).hom ≫ (swap X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      ((swap X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ Y X Z).hom ≫ (𝟙 Y ⊗ₘ (swap X Z).hom) := by
  let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose
  let A := representative X
  let B := representative Y
  let E := representative Z
  apply Represents.eq
    ((Represents.associator A B E).comp
      ((Represents.braiding A (B.tensor E)).comp (Represents.associator B E A)))
    (((Represents.braiding A B).tensor (Represents.id E)).comp
      ((Represents.associator B A E).comp
        ((Represents.id B).tensor (Represents.braiding A E))))
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
    BraidedCategory.hexagon_forward A.complex B.complex E.complex

private theorem derived_hexagon_reverse (X Y Z : D) :
    (α_ X Y Z).inv ≫ (swap (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (𝟙 X ⊗ₘ (swap Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((swap X Z).hom ⊗ₘ 𝟙 Y) := by
  let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose
  let A := representative X
  let B := representative Y
  let E := representative Z
  apply Represents.eq
    ((Represents.associator_inv A B E).comp
      ((Represents.braiding (A.tensor B) E).comp (Represents.associator_inv E A B)))
    (((Represents.id A).tensor (Represents.braiding B E)).comp
      ((Represents.associator_inv A E B).comp ((Represents.braiding A E).tensor (Represents.id B))))
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
    BraidedCategory.hexagon_reverse A.complex B.complex E.complex

private theorem derived_symmetry (X Y : D) :
    (swap X Y).hom ≫ (swap Y X).hom = 𝟙 (X ⊗ Y) := by
  let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R).choose
  let A := representative X
  let B := representative Y
  exact ((Represents.braiding A B).comp (Represents.braiding B A)).eq
    (Represents.id (A.tensor B)) (SymmetricCategory.symmetry A.complex B.complex)

/-- The canonical Koszul swap equips the derived tensor product with a symmetry. -/
@[instance_reducible]
private def derivedSymmetricCategory :
    letI := derivedMonoidalCategory (R := R)
    SymmetricCategory D := by
  letI := derivedMonoidalCategory (R := R)
  exact
    { braiding := swap
      braiding_naturality_right := fun X _ _ f => by
        simpa only [tensor_id_left, tensor_id_right] using swap_naturality (𝟙 X) f
      braiding_naturality_left := fun f Z => by
        simpa only [tensor_id_left, tensor_id_right] using swap_naturality f (𝟙 Z)
      hexagon_forward := fun X Y Z => by
        simpa only [tensor_id_left, tensor_id_right] using derived_hexagon_forward X Y Z
      hexagon_reverse := fun X Y Z => by
        simpa only [tensor_id_left, tensor_id_right] using derived_hexagon_reverse X Y Z
      symmetry := derived_symmetry }

end Coherence

/-- **Stacks 0FNQ.** The derived category of modules over a commutative ring is symmetric
monoidal under derived tensor product. Under the canonical comparison with tensor products of
K-flat representatives, its associator is induced by the ordinary associator of complexes, and
its braiding is the canonical Koszul symmetry. -/
@[stacks 0FNQ]
public theorem derivedCategory_symmetricMonoidalCategory (R : Type u) [CommRing R] :
    let D := DerivedCategory (ModuleCat.{u} R)
    let C := CochainComplex (ModuleCat.{u} R) ℤ
    let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
    let T := CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct R
    ∃ m : MonoidalCategory D,
      letI := m
      ∃ s : SymmetricCategory D,
        letI := s
        ∃ e : curriedTensor D ≅ T.tensorProduct.tensor,
          (∀ K L : D,
              (β_ K L).hom ≫ ((e.app L).app K).hom =
                ((e.app K).app L).hom ≫ ((T.braiding.iso.app K).app L).hom) ∧
            ∀ (K L M : C) (hK : K.KFlat) (hL : L.KFlat) (hM : M.KFlat)
                (hKL : (K ⊗ L).KFlat) (hLM : (L ⊗ M).KFlat),
              let comparison : ∀ (A B : C), A.KFlat → B.KFlat →
                  (Q.obj A ⊗ Q.obj B ⟶ Q.obj (A ⊗ B)) :=
                fun A B hA hB =>
                  ((e.app (Q.obj A)).app (Q.obj B)).hom ≫
                    (T.tensorProduct.comparison A B hA hB).hom
              (α_ (Q.obj K) (Q.obj L) (Q.obj M)).hom ≫
                    (Q.obj K ◁ comparison L M hL hM) ≫
                    comparison K (L ⊗ M) hK hLM =
                ((comparison K L hK hL :
                    Q.obj K ⊗ Q.obj L ⟶ Q.obj (K ⊗ L)) ▷ Q.obj M) ≫
                  comparison (K ⊗ L) M hKL hM ≫
                  Q.map (HomologicalComplex.associator K L M).hom := by
  intro D C Q T
  let := derivedMonoidalCategory (R := R)
  let := derivedSymmetricCategory (R := R)
  refine ⟨derivedMonoidalCategory, derivedSymmetricCategory, Iso.refl _, ?_, ?_⟩
  · intro K L
    show (swap K L).hom ≫ 𝟙 _ = 𝟙 _ ≫ (swap K L).hom
    simp
  · intro K L M hK hL hM hKL hLM
    show (α_ (Q.obj K) (Q.obj L) (Q.obj M)).hom ≫
        (Q.obj K ◁ (𝟙 _ ≫ (T.tensorProduct.comparison L M hL hM).hom)) ≫
        (𝟙 _ ≫ (T.tensorProduct.comparison K (L ⊗ M) hK hLM).hom) =
      ((𝟙 _ ≫ (T.tensorProduct.comparison K L hK hL).hom) ▷ Q.obj M) ≫
        (𝟙 _ ≫ (T.tensorProduct.comparison (K ⊗ L) M hKL hM).hom) ≫
        Q.map (HomologicalComplex.associator K L M).hom
    simp only [Category.id_comp]
    exact (CochainComplex.DerivedTensor.derivedTensorProduct_associator R).choose_spec.2
      K L M hK hL hM

end DerivedCategory.Invertible

end
