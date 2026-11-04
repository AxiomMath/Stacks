module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorPowerOfATensorProduct

/-!
# Transporting the tensor power of a tensor product

Let `(C₁, O₁)` and `(C₂, O₂)` be ringed sites and let

`F : Mod(O₁) ⥤ Mod(O₂)`

carry the structure sheaf to the structure sheaf and the tensor product sheaf of Tag 01CA to the
tensor product sheaf, *on objects only* — the data `Stacks.SheafOfModules.Picard.UnitIso` and
`Stacks.SheafOfModules.Picard.TensorIso`.  Two comparisons are then available at an invertible
`L ⊗ M`: the transport of tensor powers
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso`, and the comparison
`Stacks.Cohomology.Torsors.Generators.tpowTensorIso` of Tag 01CU which splits the `k`-th power of
a tensor product into the tensor product of the `k`-th powers.  This file proves that the square
they form commutes:

`F((L ⊗ M)^{⊗ k}) → F(L^{⊗ k} ⊗ M^{⊗ k}) → F(L^{⊗ k}) ⊗ F(M^{⊗ k}) → (F L)^{⊗ k} ⊗ (F M)^{⊗ k}`

is the same as

`F((L ⊗ M)^{⊗ k}) → (F(L ⊗ M))^{⊗ k} → (F L ⊗ F M)^{⊗ k} → (F L)^{⊗ k} ⊗ (F M)^{⊗ k}`.

## What the object-level data does not give

As for the naturality of the transport itself, the object-level isomorphisms are not enough: the
square is an identity between morphisms of tensor products, and
`Stacks.SheafOfModules.Picard.TensorIso` may be composed with an arbitrary automorphism of its
target at each pair of arguments without leaving that datum.  Four coherences of the pair
`(hunit, hten)` are taken as explicit arguments, each an honest equation and none of them implied
by the object-level data:

* `Stacks.SheafOfModules.TensorPowerTransport.TensorIsoNatural` — naturality of `hten`, from
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerTransport.lean`;
* `TensorIsoAssociator` — compatibility with the associativity constraint of Tag 01CA;
* `TensorIsoBraiding` — compatibility with the symmetry constraint of Tag 01CA, needed because
  `tpowTensorIso` is built from `CategoryTheory.MonoidalCategory.tensorμ`, the middle-four
  interchange, which is two associators, a braiding and three whiskerings;
* `TensorIsoRightUnitor` — compatibility of `hten` and `hunit` with the right unit constraint,
  needed for the exponent `0`, where `tpowTensorIso _ _ _ 0` is the inverse right unitor of the
  structure sheaf and the transport is `hunit`.

## Main definitions

* `Stacks.SheafOfModules.TensorPowerTransport.TensorIsoAssociator`,
  `Stacks.SheafOfModules.TensorPowerTransport.TensorIsoBraiding` and
  `Stacks.SheafOfModules.TensorPowerTransport.TensorIsoRightUnitor`: the three further
  coherences of the object-level comparisons.
* `Stacks.SheafOfModules.TensorPowerTransport.braidMiddleIso`: the isomorphism
  `P ⊗ (Q ⊗ R) ≅ Q ⊗ (P ⊗ R)` out of which the middle-four interchange is built.
* `Stacks.SheafOfModules.TensorPowerTransport.tensorComparison`,
  `Stacks.SheafOfModules.TensorPowerTransport.unitComparison` and
  `Stacks.SheafOfModules.TensorPowerTransport.tpowTransport`: the three input comparisons read at
  the ring sheaf of a ringed site.

## Main results

* `Stacks.SheafOfModules.TensorPowerTransport.tensorComparison_tensorMu`: **the middle-four
  interchange crosses an object-level tensor comparison**, given its naturality and its
  compatibility with the associator and the braiding.  Stated in an abstract braided monoidal
  category.
* `Stacks.SheafOfModules.TensorPowerTransport.tensorMu_transport_step`: the inductive step of the
  square, likewise isolated as an identity of an abstract braided monoidal category.
* `Stacks.SheafOfModules.TensorPowerTransport.tpowTransport_tensor` and
  `Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor`: **the square commutes**,
  the second with the invertibility of the images discharged from the input data.

## Implementation notes

The statement mixes the two developments: the transport of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerTransport.lean` is written over a sheaf
of commutative rings `O` and a sheaf condition `hO`, while the power of a tensor product of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Torsors/TensorPowerOfATensorProduct.lean` is written
over a ringed site `X`; `O := X.O.obj` and
`hO := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2` make the two the same terms.  A
composite of isomorphisms of sheaves of modules mixing the
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O)` index with the
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.O.obj
(Stacks.SheafOfModules.Tensor.ringSheaf X.O).2` index is
type-correct only at *default* transparency, which silently blocks `rw` and `simp` — they report
a missing pattern, not the cause.  Every composite below is therefore written at the
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O)` index, through
`Stacks.Cohomology.Torsors.Generators.tensorIsoOfModules` and the
three wrappers `tensorComparison`, `unitComparison` and `tpowTransport`, each of which is a bare
type ascription of the datum it names; the crossing happens once, inside those ascriptions, and
is discharged by `exact`, which elaborates at default transparency.

The monoidal and symmetric structures used are **the very instances of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Torsors/TensorPowerOfATensorProduct.lean`**, made
instances again here by `attribute [local instance]` rather than redeclared.  Redeclaring them
produces a defeq but syntactically different instance term, and the lemmas imported from that
file — `tensorIsoOfModules_hom`, `tensorInterchangeIso_hom` — then fail to `rw`.

The two purely monoidal identities, `tensorComparison_tensorMu` and `tensorMu_transport_step`,
are stated in an abstract braided monoidal category for the same transparency reason: there the
objects carry no projections of a ringed site, so `rw` on the monoidal lemmas fires, and each is
applied to the sheaf case by `exact`.  `tensorComparison_tensorMu` is in turn assembled from
three squares — `tensorComparison_whiskerLeft`, `tensorComparison_whiskerRight` and
`tensorComparison_associator` — so that the only place the braiding appears is
`tensorComparison_braidMiddle`.

The inductive step takes the induction hypothesis in the shape `u ≫ (p ⊗ₘ q) = v`, which is what
survives the two successor squares `tpowTransport_succ_comm` and
`Stacks.Cohomology.Torsors.Generators.powerMap_succ_tensorIsoOfModules`; both sides of the
`k + 1` case are brought to a common form by those squares, so no
`CategoryTheory.Functor.mapIso` has to be cancelled against its inverse inside a tensor product.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerSuccIso tensorProductIso
  tensorProductAssociator tensorProductBraiding tensorProductRightUnitor)
open Stacks.SheafOfModules (IsInvertible)
open Stacks.Cohomology.Torsors.Generators

attribute [local instance] Stacks.Cohomology.Torsors.Generators.ringedSiteModulesMonoidal
  Stacks.Cohomology.Torsors.Generators.ringedSiteModulesSymmetric

universe u₁ v₁ u₂ v₂ w

namespace Stacks.SheafOfModules.TensorPowerTransport

/-! ### The middle-four interchange across an object-level tensor comparison -/

section BraidedComparison

variable {D₁ : Type*} [Category D₁] [MonoidalCategory D₁] [BraidedCategory D₁]
  {D₂ : Type*} [Category D₂] [MonoidalCategory D₂] [BraidedCategory D₂]
  (G : D₁ ⥤ D₂) (h : ∀ P Q : D₁, G.obj (P ⊗ Q) ≅ G.obj P ⊗ G.obj Q)

/-- The isomorphism `P ⊗ (Q ⊗ R) ≅ Q ⊗ (P ⊗ R)` carrying the first factor past the second: two
associativity constraints and one braiding.  Whiskered on the left and conjugated by two further
associators it is the middle-four interchange
`CategoryTheory.MonoidalCategory.tensorμ`, which is what `tensorMu_eq_braidMiddle` records. -/
def braidMiddleIso (P Q R : D₁) : P ⊗ (Q ⊗ R) ≅ Q ⊗ (P ⊗ R) :=
  (α_ P Q R).symm ≪≫ MonoidalCategory.whiskerRightIso (β_ P Q) R ≪≫ α_ Q P R

/-- The underlying morphism of `braidMiddleIso`. -/
theorem braidMiddleIso_hom (P Q R : D₁) :
    (braidMiddleIso P Q R).hom =
      (α_ P Q R).inv ≫ ((β_ P Q).hom ▷ R) ≫ (α_ Q P R).hom := rfl

/-- **The middle-four interchange is `braidMiddleIso` whiskered by the first factor**, between
two associativity constraints. -/
theorem tensorMu_eq_braidMiddle (A B P Q : D₁) :
    tensorμ A B P Q =
      (α_ A B (P ⊗ Q)).hom ≫ (A ◁ (braidMiddleIso B P Q).hom) ≫
        (α_ A P (B ⊗ Q)).inv := by
  simp only [tensorμ, braidMiddleIso_hom, MonoidalCategory.whiskerLeft_comp, Category.assoc]

omit [BraidedCategory D₁] [BraidedCategory D₂] in
/-- **Naturality of an object-level tensor comparison, whiskered on the left**: a square over an
isomorphism, whiskered by a fixed object on the left, is carried to the whiskered square of the
images. -/
theorem tensorComparison_whiskerLeft
    (hnat : ∀ {P P' Q Q' : D₁} (e : P ≅ P') (f : Q ≅ Q'),
      G.map (e.hom ⊗ₘ f.hom) ≫ (h P' Q').hom =
        (h P Q).hom ≫ (G.map e.hom ⊗ₘ G.map f.hom))
    (A : D₁) {V W : D₁} (g : V ≅ W) {Z Z' : D₂}
    (phiV : G.obj V ⟶ Z) (phiW : G.obj W ⟶ Z') (u : Z ⟶ Z')
    (hsq : G.map g.hom ≫ phiW = phiV ≫ u) :
    G.map (A ◁ g.hom) ≫ ((h A W).hom ≫ (G.obj A ◁ phiW)) =
      ((h A V).hom ≫ (G.obj A ◁ phiV)) ≫ (G.obj A ◁ u) := by
  have hn : G.map (A ◁ g.hom) ≫ (h A W).hom =
      (h A V).hom ≫ (G.obj A ◁ G.map g.hom) := by
    simpa only [Iso.refl_hom, G.map_id, MonoidalCategory.id_tensorHom] using hnat (Iso.refl A) g
  rw [← Category.assoc, hn, Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hsq,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]

omit [BraidedCategory D₁] [BraidedCategory D₂] in
/-- **Naturality of an object-level tensor comparison, whiskered on the right**: a square over an
isomorphism, whiskered by a fixed object on the right, is carried to the whiskered square of the
images. -/
theorem tensorComparison_whiskerRight
    (hnat : ∀ {P P' Q Q' : D₁} (e : P ≅ P') (f : Q ≅ Q'),
      G.map (e.hom ⊗ₘ f.hom) ≫ (h P' Q').hom =
        (h P Q).hom ≫ (G.map e.hom ⊗ₘ G.map f.hom))
    {V W : D₁} (g : V ≅ W) (R : D₁) {Z Z' : D₂}
    (phiV : G.obj V ⟶ Z) (phiW : G.obj W ⟶ Z') (u : Z ⟶ Z')
    (hsq : G.map g.hom ≫ phiW = phiV ≫ u) :
    G.map (g.hom ▷ R) ≫ ((h W R).hom ≫ (phiW ▷ G.obj R)) =
      ((h V R).hom ≫ (phiV ▷ G.obj R)) ≫ (u ▷ G.obj R) := by
  have hn : G.map (g.hom ▷ R) ≫ (h W R).hom =
      (h V R).hom ≫ (G.map g.hom ▷ G.obj R) := by
    simpa only [Iso.refl_hom, G.map_id, MonoidalCategory.tensorHom_id] using hnat g (Iso.refl R)
  rw [← Category.assoc, hn, Category.assoc, ← MonoidalCategory.comp_whiskerRight, hsq,
    MonoidalCategory.comp_whiskerRight, Category.assoc]

omit [BraidedCategory D₁] [BraidedCategory D₂] in
/-- **The associativity coherence of an object-level tensor comparison, read against a further
flattening of the third factor.**  Taking `theta` to be an identity gives the coherence itself in
whiskered form. -/
theorem tensorComparison_associator
    (hassoc : ∀ P Q R : D₁,
      G.map (α_ P Q R).hom ≫ (h P (Q ⊗ R)).hom ≫ (𝟙 (G.obj P) ⊗ₘ (h Q R).hom) =
        (h (P ⊗ Q) R).hom ≫ ((h P Q).hom ⊗ₘ 𝟙 (G.obj R)) ≫
          (α_ (G.obj P) (G.obj Q) (G.obj R)).hom)
    (A B : D₁) {X : D₁} {Z : D₂} (theta : G.obj X ⟶ Z) :
    G.map (α_ A B X).hom ≫
        ((h A (B ⊗ X)).hom ≫ (G.obj A ◁ ((h B X).hom ≫ (G.obj B ◁ theta)))) =
      ((h (A ⊗ B) X).hom ≫ ((h A B).hom ⊗ₘ theta)) ≫
        (α_ (G.obj A) (G.obj B) Z).hom := by
  have ha : G.map (α_ A B X).hom ≫ ((h A (B ⊗ X)).hom ≫ (G.obj A ◁ (h B X).hom)) =
      ((h (A ⊗ B) X).hom ≫ ((h A B).hom ▷ G.obj X)) ≫
        (α_ (G.obj A) (G.obj B) (G.obj X)).hom := by
    simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id, Category.assoc]
      using hassoc A B X
  calc G.map (α_ A B X).hom ≫
        ((h A (B ⊗ X)).hom ≫ (G.obj A ◁ ((h B X).hom ≫ (G.obj B ◁ theta))))
      = (G.map (α_ A B X).hom ≫ ((h A (B ⊗ X)).hom ≫ (G.obj A ◁ (h B X).hom))) ≫
          (G.obj A ◁ (G.obj B ◁ theta)) := by
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    _ = (((h (A ⊗ B) X).hom ≫ ((h A B).hom ▷ G.obj X)) ≫
          (α_ (G.obj A) (G.obj B) (G.obj X)).hom) ≫
          (G.obj A ◁ (G.obj B ◁ theta)) := by rw [ha]
    _ = ((h (A ⊗ B) X).hom ≫ ((h A B).hom ▷ G.obj X)) ≫
          ((α_ (G.obj A) (G.obj B) (G.obj X)).hom ≫ (G.obj A ◁ (G.obj B ◁ theta))) := by
        simp only [Category.assoc]
    _ = ((h (A ⊗ B) X).hom ≫ ((h A B).hom ▷ G.obj X)) ≫
          (((G.obj A ⊗ G.obj B) ◁ theta) ≫ (α_ (G.obj A) (G.obj B) Z).hom) := by
        rw [← MonoidalCategory.associator_naturality_right]
    _ = _ := by
        rw [MonoidalCategory.tensorHom_def]
        simp only [Category.assoc]

/-- A square over an isomorphism, whose right edge is an isomorphism, is also a square over the
inverses. -/
private theorem map_inv_comp_eq_of_map_hom_comp_eq {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {X Y : C} (e : X ≅ Y) {Z W : D} (e' : Z ≅ W) (a : G.obj Y ⟶ W) (b : G.obj X ⟶ Z)
    (h : G.map e.hom ≫ a = b ≫ e'.hom) : G.map e.inv ≫ b = a ≫ e'.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, ← h, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id,
    G.map_id, Category.id_comp]

/-- **`braidMiddleIso` crosses an object-level tensor comparison.**  This is where the
compatibility with the braiding is used, and it is the only place it is used. -/
theorem tensorComparison_braidMiddle
    (hnat : ∀ {P P' Q Q' : D₁} (e : P ≅ P') (f : Q ≅ Q'),
      G.map (e.hom ⊗ₘ f.hom) ≫ (h P' Q').hom =
        (h P Q).hom ≫ (G.map e.hom ⊗ₘ G.map f.hom))
    (hassoc : ∀ P Q R : D₁,
      G.map (α_ P Q R).hom ≫ (h P (Q ⊗ R)).hom ≫ (𝟙 (G.obj P) ⊗ₘ (h Q R).hom) =
        (h (P ⊗ Q) R).hom ≫ ((h P Q).hom ⊗ₘ 𝟙 (G.obj R)) ≫
          (α_ (G.obj P) (G.obj Q) (G.obj R)).hom)
    (hbraid : ∀ P Q : D₁,
      G.map (β_ P Q).hom ≫ (h Q P).hom =
        (h P Q).hom ≫ (β_ (G.obj P) (G.obj Q)).hom)
    (P Q R : D₁) :
    G.map (braidMiddleIso P Q R).hom ≫
        ((h Q (P ⊗ R)).hom ≫ (G.obj Q ◁ (h P R).hom)) =
      ((h P (Q ⊗ R)).hom ≫ (G.obj P ◁ (h Q R).hom)) ≫
        (braidMiddleIso (G.obj P) (G.obj Q) (G.obj R)).hom := by
  have e : ∀ A B : D₁, G.map (α_ A B R).hom ≫ ((h A (B ⊗ R)).hom ≫ (G.obj A ◁ (h B R).hom)) =
      ((h (A ⊗ B) R).hom ≫ ((h A B).hom ▷ G.obj R)) ≫
        (α_ (G.obj A) (G.obj B) (G.obj R)).hom := fun A B => by
    simpa only [MonoidalCategory.whiskerLeft_id, Category.comp_id,
      MonoidalCategory.tensorHom_id] using
      tensorComparison_associator G h hassoc A B (𝟙 (G.obj R))
  have e2 := tensorComparison_whiskerRight G h hnat (β_ P Q) R
    (h P Q).hom (h Q P).hom (β_ (G.obj P) (G.obj Q)).hom (hbraid P Q)
  have e1' := map_inv_comp_eq_of_map_hom_comp_eq G (α_ P Q R) (α_ _ _ _) _ _ (e P Q)
  calc G.map (braidMiddleIso P Q R).hom ≫
        ((h Q (P ⊗ R)).hom ≫ (G.obj Q ◁ (h P R).hom))
      = G.map (α_ P Q R).inv ≫ G.map ((β_ P Q).hom ▷ R) ≫
          (G.map (α_ Q P R).hom ≫ ((h Q (P ⊗ R)).hom ≫ (G.obj Q ◁ (h P R).hom))) := by
        rw [braidMiddleIso_hom, G.map_comp, G.map_comp, Category.assoc, Category.assoc]
    _ = G.map (α_ P Q R).inv ≫ G.map ((β_ P Q).hom ▷ R) ≫
          (((h (Q ⊗ P) R).hom ≫ ((h Q P).hom ▷ G.obj R)) ≫
            (α_ (G.obj Q) (G.obj P) (G.obj R)).hom) := by rw [e Q P]
    _ = G.map (α_ P Q R).inv ≫
          (G.map ((β_ P Q).hom ▷ R) ≫
            ((h (Q ⊗ P) R).hom ≫ ((h Q P).hom ▷ G.obj R))) ≫
            (α_ (G.obj Q) (G.obj P) (G.obj R)).hom := by simp only [Category.assoc]
    _ = G.map (α_ P Q R).inv ≫
          (((h (P ⊗ Q) R).hom ≫ ((h P Q).hom ▷ G.obj R)) ≫
            ((β_ (G.obj P) (G.obj Q)).hom ▷ G.obj R)) ≫
            (α_ (G.obj Q) (G.obj P) (G.obj R)).hom := by rw [e2]
    _ = (G.map (α_ P Q R).inv ≫ ((h (P ⊗ Q) R).hom ≫ ((h P Q).hom ▷ G.obj R))) ≫
          ((β_ (G.obj P) (G.obj Q)).hom ▷ G.obj R) ≫
            (α_ (G.obj Q) (G.obj P) (G.obj R)).hom := by simp only [Category.assoc]
    _ = (((h P (Q ⊗ R)).hom ≫ (G.obj P ◁ (h Q R).hom)) ≫
          (α_ (G.obj P) (G.obj Q) (G.obj R)).inv) ≫
          ((β_ (G.obj P) (G.obj Q)).hom ▷ G.obj R) ≫
            (α_ (G.obj Q) (G.obj P) (G.obj R)).hom := by rw [e1']
    _ = _ := by rw [braidMiddleIso_hom]; simp only [Category.assoc]

/-- **The middle-four interchange crosses an object-level tensor comparison**, given its
naturality and its compatibility with the associativity and symmetry constraints. -/
theorem tensorComparison_tensorMu
    (hnat : ∀ {P P' Q Q' : D₁} (e : P ≅ P') (f : Q ≅ Q'),
      G.map (e.hom ⊗ₘ f.hom) ≫ (h P' Q').hom =
        (h P Q).hom ≫ (G.map e.hom ⊗ₘ G.map f.hom))
    (hassoc : ∀ P Q R : D₁,
      G.map (α_ P Q R).hom ≫ (h P (Q ⊗ R)).hom ≫ (𝟙 (G.obj P) ⊗ₘ (h Q R).hom) =
        (h (P ⊗ Q) R).hom ≫ ((h P Q).hom ⊗ₘ 𝟙 (G.obj R)) ≫
          (α_ (G.obj P) (G.obj Q) (G.obj R)).hom)
    (hbraid : ∀ P Q : D₁,
      G.map (β_ P Q).hom ≫ (h Q P).hom =
        (h P Q).hom ≫ (β_ (G.obj P) (G.obj Q)).hom)
    (A B P Q : D₁) :
    G.map (tensorμ A B P Q) ≫
        ((h (A ⊗ P) (B ⊗ Q)).hom ≫ ((h A P).hom ⊗ₘ (h B Q).hom)) =
      ((h (A ⊗ B) (P ⊗ Q)).hom ≫ ((h A B).hom ⊗ₘ (h P Q).hom)) ≫
        tensorμ (G.obj A) (G.obj B) (G.obj P) (G.obj Q) := by
  have k3' := map_inv_comp_eq_of_map_hom_comp_eq G (α_ A P (B ⊗ Q)) (α_ _ _ _) _ _
    (tensorComparison_associator G h hassoc A P (h B Q).hom)
  have k2 := tensorComparison_whiskerLeft G h hnat A (braidMiddleIso B P Q)
    ((h B (P ⊗ Q)).hom ≫ (G.obj B ◁ (h P Q).hom))
    ((h P (B ⊗ Q)).hom ≫ (G.obj P ◁ (h B Q).hom))
    (braidMiddleIso (G.obj B) (G.obj P) (G.obj Q)).hom
    (tensorComparison_braidMiddle G h hnat hassoc hbraid B P Q)
  calc G.map (tensorμ A B P Q) ≫
        ((h (A ⊗ P) (B ⊗ Q)).hom ≫ ((h A P).hom ⊗ₘ (h B Q).hom))
      = G.map (α_ A B (P ⊗ Q)).hom ≫ G.map (A ◁ (braidMiddleIso B P Q).hom) ≫
          (G.map (α_ A P (B ⊗ Q)).inv ≫
            ((h (A ⊗ P) (B ⊗ Q)).hom ≫ ((h A P).hom ⊗ₘ (h B Q).hom))) := by
        rw [tensorMu_eq_braidMiddle, G.map_comp, G.map_comp, Category.assoc, Category.assoc]
    _ = G.map (α_ A B (P ⊗ Q)).hom ≫ G.map (A ◁ (braidMiddleIso B P Q).hom) ≫
          (((h A (P ⊗ (B ⊗ Q))).hom ≫
              (G.obj A ◁ ((h P (B ⊗ Q)).hom ≫ (G.obj P ◁ (h B Q).hom)))) ≫
            (α_ (G.obj A) (G.obj P) (G.obj B ⊗ G.obj Q)).inv) := by rw [k3']
    _ = G.map (α_ A B (P ⊗ Q)).hom ≫
          (G.map (A ◁ (braidMiddleIso B P Q).hom) ≫
            ((h A (P ⊗ (B ⊗ Q))).hom ≫
              (G.obj A ◁ ((h P (B ⊗ Q)).hom ≫ (G.obj P ◁ (h B Q).hom))))) ≫
            (α_ (G.obj A) (G.obj P) (G.obj B ⊗ G.obj Q)).inv := by
        simp only [Category.assoc]
    _ = G.map (α_ A B (P ⊗ Q)).hom ≫
          (((h A (B ⊗ (P ⊗ Q))).hom ≫
              (G.obj A ◁ ((h B (P ⊗ Q)).hom ≫ (G.obj B ◁ (h P Q).hom)))) ≫
            (G.obj A ◁ (braidMiddleIso (G.obj B) (G.obj P) (G.obj Q)).hom)) ≫
            (α_ (G.obj A) (G.obj P) (G.obj B ⊗ G.obj Q)).inv := by rw [k2]
    _ = (G.map (α_ A B (P ⊗ Q)).hom ≫
          ((h A (B ⊗ (P ⊗ Q))).hom ≫
            (G.obj A ◁ ((h B (P ⊗ Q)).hom ≫ (G.obj B ◁ (h P Q).hom))))) ≫
          (G.obj A ◁ (braidMiddleIso (G.obj B) (G.obj P) (G.obj Q)).hom) ≫
            (α_ (G.obj A) (G.obj P) (G.obj B ⊗ G.obj Q)).inv := by
        simp only [Category.assoc]
    _ = (((h (A ⊗ B) (P ⊗ Q)).hom ≫ ((h A B).hom ⊗ₘ (h P Q).hom)) ≫
          (α_ (G.obj A) (G.obj B) (G.obj P ⊗ G.obj Q)).hom) ≫
          (G.obj A ◁ (braidMiddleIso (G.obj B) (G.obj P) (G.obj Q)).hom) ≫
            (α_ (G.obj A) (G.obj P) (G.obj B ⊗ G.obj Q)).inv := by
        rw [tensorComparison_associator G h hassoc A B (h P Q).hom]
    _ = _ := by
        rw [tensorMu_eq_braidMiddle]
        simp only [Category.assoc]

/-- **The inductive step of the square, isolated as an identity of a braided monoidal
category.**  Both sides are read after the leading successor comparison has been cancelled; `ih`
is the square at the previous exponent. -/
theorem tensorMu_transport_step {A' B' P' Q' R S W W' T₀ T₁ : D₂}
    (u : T₀ ⟶ A' ⊗ B') (t : T₁ ⟶ R ⊗ S) (p : A' ⟶ P') (q : B' ⟶ Q') (v : T₀ ⟶ P' ⊗ Q')
    (sL : P' ⊗ R ⟶ W) (sM : Q' ⊗ S ⟶ W') (ih : u ≫ (p ⊗ₘ q) = v) :
    (u ⊗ₘ t) ≫ tensorμ A' B' R S ≫
        (((p ⊗ₘ 𝟙 R) ≫ sL) ⊗ₘ ((q ⊗ₘ 𝟙 S) ≫ sM)) =
      (v ⊗ₘ t) ≫ tensorμ P' Q' R S ≫ (sL ⊗ₘ sM) := by
  have h1 : tensorμ A' B' R S ≫ (((p ⊗ₘ 𝟙 R) ≫ sL) ⊗ₘ ((q ⊗ₘ 𝟙 S) ≫ sM)) =
      ((p ⊗ₘ q) ⊗ₘ 𝟙 (R ⊗ S)) ≫ tensorμ P' Q' R S ≫ (sL ⊗ₘ sM) := by
    rw [← MonoidalCategory.tensorHom_comp_tensorHom, ← Category.assoc,
      ← MonoidalCategory.tensorμ_natural, MonoidalCategory.id_tensorHom_id]
    simp only [Category.assoc]
  rw [h1, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, ih]

omit [BraidedCategory D₂] in
/-- **The base case of the square, isolated as an identity of a monoidal category**: a morphism
to the unit object, tensored with itself and followed by the right unitor of the unit object, is
the morphism whiskered on the right, followed by the right unitor and by the morphism again.
This is the right unitor read twice, and it is all the exponent `0` needs beyond the unit
coherence. -/
theorem rightUnitor_unit_step {A : D₂} (u : A ⟶ 𝟙_ D₂) :
    (u ⊗ₘ u) ≫ (ρ_ (𝟙_ D₂)).hom = ((𝟙 A ⊗ₘ u) ≫ (ρ_ A).hom) ≫ u := by
  rw [Category.assoc, ← MonoidalCategory.rightUnitor_naturality,
    ← MonoidalCategory.tensorHom_id, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

end BraidedComparison

/-! ### The further coherences of the object-level comparisons -/

section TwoSites

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  (O₁ : C₁ᵒᵖ ⥤ CommRingCat.{w}) (hO₁ : Presheaf.IsSheaf J₁ (structureRingPresheaf O₁))
  [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J₁ AddCommGrpCat.{w}]
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  (O₂ : C₂ᵒᵖ ⥤ CommRingCat.{w}) (hO₂ : Presheaf.IsSheaf J₂ (structureRingPresheaf O₂))
  [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J₂ AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (structureSheaf O₁ hO₁) ⥤ SheafOfModules.{w} (structureSheaf O₂ hO₂))

/-- **Compatibility of an object-level tensor comparison with the associativity constraint of
Tag 01CA.**  It asserts that the image under `F` of the associativity constraint of `A`, `B`, `D`,
followed by the comparison at `(A, B ⊗ D)` and the comparison at `(B, D)` tensored on the left
with the identity of `F A`, is the comparison at `(A ⊗ B, D)`, followed by the comparison at
`(A, B)` tensored on the right with the identity of `F D` and by the associativity constraint of
the images.  Like `Stacks.SheafOfModules.TensorPowerTransport.TensorIsoNatural` it is a property
of the comparison and not of `F`, and it is not implied by
`Stacks.SheafOfModules.Picard.TensorIso`: composing the comparison with an arbitrary automorphism
of its target at each pair of arguments leaves that datum intact and destroys this equation. -/
def TensorIsoAssociator (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F) : Prop :=
  ∀ A B D : SheafOfModules.{w} (structureSheaf O₁ hO₁),
    F.map (tensorProductAssociator O₁ hO₁ A B D).hom ≫
        (hten A (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ O₁ (forget₂ CommRingCat RingCat) hO₁⟩).obj
            B).obj D)).hom ≫
        (tensorProductIso O₂ hO₂ (Iso.refl (F.obj A)) (hten B D)).hom =
      (hten (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ O₁ (forget₂ CommRingCat RingCat) hO₁⟩).obj
            A).obj B) D).hom ≫
        (tensorProductIso O₂ hO₂ (hten A B) (Iso.refl (F.obj D))).hom ≫
        (tensorProductAssociator O₂ hO₂ (F.obj A) (F.obj B) (F.obj D)).hom

/-- **Compatibility of an object-level tensor comparison with the symmetry constraint of
Tag 01CA.**  It asserts that the image under `F` of the symmetry constraint of `A`, `B`, followed
by the comparison at `(B, A)`, is the comparison at `(A, B)` followed by the symmetry constraint
of the images.  It is needed because
`Stacks.Cohomology.Torsors.Generators.tpowTensorIso` is built from the middle-four interchange
`CategoryTheory.MonoidalCategory.tensorμ`, which contains one braiding. -/
def TensorIsoBraiding (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F) : Prop :=
  ∀ A B : SheafOfModules.{w} (structureSheaf O₁ hO₁),
    F.map (tensorProductBraiding O₁ hO₁ A B).hom ≫ (hten B A).hom =
      (hten A B).hom ≫ (tensorProductBraiding O₂ hO₂ (F.obj A) (F.obj B)).hom

/-- **Compatibility of an object-level tensor comparison and an object-level unit comparison with
the right unit constraint of Tag 01CA.**  It asserts that the image under `F` of the right unit
constraint of `A` is the comparison at `(A, O₁)`, followed by the unit comparison tensored on the
left with the identity of `F A`, followed by the right unit constraint of `F A`.  It is needed at
the exponent `0`, where `Stacks.Cohomology.Torsors.Generators.tpowTensorIso` is the inverse right
unit constraint of the structure sheaf and
`Stacks.SheafOfModules.TensorPowerTransport.powerTransport` is the unit comparison. -/
def TensorIsoRightUnitor (hunit : Picard.UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : Picard.TensorIso O₁ hO₁ O₂ hO₂ F) : Prop :=
  ∀ A : SheafOfModules.{w} (structureSheaf O₁ hO₁),
    F.map (tensorProductRightUnitor O₁ hO₁ A).hom =
      (hten A (SheafOfModules.unit (structureSheaf O₁ hO₁))).hom ≫
        (tensorProductIso O₂ hO₂ (Iso.refl (F.obj A)) hunit).hom ≫
        (tensorProductRightUnitor O₂ hO₂ (F.obj A)).hom

end TwoSites

/-! ### The square, over two ringed sites -/

section RingedSites

variable (X₁ : RingedSite.{u₁, v₁, w})
    [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X₁.J AddCommGrpCat.{w}]
    (X₂ : RingedSite.{u₂, v₂, w})
    [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X₂.J AddCommGrpCat.{w}]
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O) ⥤ SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))

/-- The object-level tensor comparison of `F`, read at the ring sheaves of the two ringed sites.
This is `hten` itself; the ascription is what keeps every composite below in one spelling. -/
noncomputable def tensorComparison
    (hten : Picard.TensorIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) :
    F.obj (tensorSheafOfModules X₁ L N) ≅
      tensorSheafOfModules X₂ (F.obj L) (F.obj N) := hten L N

/-- The object-level unit comparison of `F`, read at the ring sheaves of the two ringed sites,
with the structure sheaves spelled as the monoidal units of Tag 01CA.  This is `hunit` itself;
the spelling matters, because `CategoryTheory.MonoidalCategory.tensorUnit` and
`Stacks.SheafOfModules.unit` of the ring sheaf agree only at *default* transparency. -/
noncomputable def unitComparison
    (hunit : Picard.UnitIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F) :
    F.obj (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))) ≅
      𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)) := hunit

/-- The transport of tensor powers along `F`, read at the ring sheaves of the two ringed sites.
This is `Stacks.SheafOfModules.TensorPowerTransport.powerTransport` itself. -/
noncomputable def tpowTransport
    (hunit : Picard.UnitIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hten : Picard.TensorIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
      [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 L]
    [IsInvertible X₂.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 (F.obj L)] (k : ℕ) :
    F.obj (tpow X₁ L k) ≅ tpow X₂ (F.obj L) k :=
  powerTransport X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L k

/-- The successor square for the transport, read at the ring sheaves of the two ringed sites.
This is `Stacks.SheafOfModules.TensorPowerTransport.powerTransport_succ_comm`. -/
theorem tpowTransport_succ_comm
    (hunit : Picard.UnitIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hten : Picard.TensorIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
      [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 L]
    [IsInvertible X₂.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 (F.obj L)] (k : ℕ) :
    (tensorComparison X₁ X₂ F hten (tpow X₁ L k) L).hom ≫
        ((tpowTransport X₁ X₂ F hunit hten L k).hom ⊗ₘ 𝟙 (F.obj L)) ≫
        (tpowSuccIso X₂ (F.obj L) k).hom =
      F.map (tpowSuccIso X₁ L k).hom ≫ (tpowTransport X₁ X₂ F hunit hten L (k + 1)).hom :=
  powerTransport_succ_comm X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L k

/-- **The square relating the transport of tensor powers to the tensor power of a tensor
product**, with the invertibility of the images of `L`, `M` and `L ⊗ M` as instance arguments.
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor` is this with those
instances discharged from the input data.

The proof is induction on `k`.  At `0` it is the compatibility with the right unit constraint,
`hrunit`; at `k + 1` both sides are brought to a common form by the two successor squares
`tpowTransport_succ_comm` and
`Stacks.Cohomology.Torsors.Generators.powerMap_succ_tensorIsoOfModules`, the middle-four
interchange is moved across the comparison by `tensorComparison_tensorMu`, and the induction
hypothesis is read inside a tensor product by `tensorMu_transport_step`. -/
theorem tpowTransport_tensor
    (hunit : Picard.UnitIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hten : Picard.TensorIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hnat : TensorIsoNatural X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hten)
    (hassoc : TensorIsoAssociator X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hten)
    (hbraid : TensorIsoBraiding X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hten)
    (hrunit : TensorIsoRightUnitor X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten)
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
    [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 L]
      [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 M]
    [IsInvertible X₂.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 (F.obj L)]
    [IsInvertible X₂.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 (F.obj M)]
    [IsInvertible X₂.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2
      (F.obj (tensorSheafOfModules X₁ L M))] (k : ℕ) :
    F.map (tpowTensorIso X₁ L M k).hom ≫
        (tensorComparison X₁ X₂ F hten (tpow X₁ L k) (tpow X₁ M k)).hom ≫
        ((tpowTransport X₁ X₂ F hunit hten L k).hom ⊗ₘ
          (tpowTransport X₁ X₂ F hunit hten M k).hom) =
      (tpowTransport X₁ X₂ F hunit hten (tensorSheafOfModules X₁ L M) k).hom ≫
        (powerMap X₂ (tensorComparison X₁ X₂ F hten L M) k).hom ≫
        (tpowTensorIso X₂ (F.obj L) (F.obj M) k).hom := by
  have hnat' : ∀ {P P' Q Q' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)}
    (e : P ≅ P') (f : Q ≅ Q'),
      F.map (e.hom ⊗ₘ f.hom) ≫ (tensorComparison X₁ X₂ F hten P' Q').hom =
        (tensorComparison X₁ X₂ F hten P Q).hom ≫ (F.map e.hom ⊗ₘ F.map f.hom) :=
    fun e f => hnat _ _ _ _ e f
  have hassoc' : ∀ P Q R : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O),
      F.map (α_ P Q R).hom ≫ (tensorComparison X₁ X₂ F hten P (Q ⊗ R)).hom ≫
          (𝟙 (F.obj P) ⊗ₘ (tensorComparison X₁ X₂ F hten Q R).hom) =
        (tensorComparison X₁ X₂ F hten (P ⊗ Q) R).hom ≫
          ((tensorComparison X₁ X₂ F hten P Q).hom ⊗ₘ 𝟙 (F.obj R)) ≫
          (α_ (F.obj P) (F.obj Q) (F.obj R)).hom :=
    fun P Q R => hassoc P Q R
  have hbraid' : ∀ P Q : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O),
      F.map (β_ P Q).hom ≫ (tensorComparison X₁ X₂ F hten Q P).hom =
        (tensorComparison X₁ X₂ F hten P Q).hom ≫ (β_ (F.obj P) (F.obj Q)).hom :=
    fun P Q => hbraid P Q
  induction k with
  | zero =>
      have hu := rightUnitor_unit_step (unitComparison X₁ X₂ F hunit).hom
      have hr : F.map
        (ρ_ (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))).hom =
          (tensorComparison X₁ X₂ F hten
            (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))
              (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))).hom ≫
            (𝟙 (F.obj (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))) ⊗ₘ
              (unitComparison X₁ X₂ F hunit).hom) ≫
            (ρ_ (F.obj (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))))).hom
              :=
        hrunit (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))
      have main :
        (tensorComparison X₁ X₂ F hten
        (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))
              (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))).hom ≫
            ((unitComparison X₁ X₂ F hunit).hom ⊗ₘ (unitComparison X₁ X₂ F hunit).hom) ≫
            (ρ_ (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)))).hom =
          F.map (ρ_ (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))).hom ≫
            (unitComparison X₁ X₂ F hunit).hom := by
        rw [hu, hr]
        simp only [Category.assoc]
      have hCT :
        (tensorComparison X₁ X₂ F hten
        (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))
              (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))).hom ≫
            ((unitComparison X₁ X₂ F hunit).hom ⊗ₘ (unitComparison X₁ X₂ F hunit).hom) =
          F.map (ρ_ (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))).hom ≫
            (unitComparison X₁ X₂ F hunit).hom ≫
            (ρ_ (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)))).inv := by
        rw [← Category.assoc, ← main]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have hzero : F.map
        (ρ_ (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))).inv ≫
            (tensorComparison X₁ X₂ F hten
              (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))
                (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)))).hom ≫
              ((unitComparison X₁ X₂ F hunit).hom ⊗ₘ (unitComparison X₁ X₂ F hunit).hom) =
          (unitComparison X₁ X₂ F hunit).hom ≫
            𝟙 (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))) ≫
            (ρ_ (𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)))).inv := by
        rw [Category.id_comp, hCT, ← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id,
          Category.id_comp]
      exact hzero
  | succ k ih =>
      refine (Iso.cancel_iso_hom_left
        (F.mapIso (tpowSuccIso X₁ (tensorSheafOfModules X₁ L M) k)) _ _).1 ?_
      rw [Functor.mapIso_hom]
      have hnatI : ∀ {P P' Q Q' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)}
        (e : P ≅ P') (f : Q ≅ Q')
          {W : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)}
          (g : tensorSheafOfModules X₂ (F.obj P') (F.obj Q') ⟶ W),
          F.map (tensorIsoOfModules X₁ e f).hom ≫
              (tensorComparison X₁ X₂ F hten P' Q').hom ≫ g =
            (tensorComparison X₁ X₂ F hten P Q).hom ≫
              (tensorIsoOfModules X₂ (F.mapIso e) (F.mapIso f)).hom ≫ g := by
        intro P P' Q Q' e f W g
        simp only [← Category.assoc]
        exact congrArg (fun z => z ≫ g) (hnat P Q P' Q' e f)
      have htail : (tensorIsoOfModules X₂ (F.mapIso (tpowSuccIso X₁ L k))
              (F.mapIso (tpowSuccIso X₁ M k))).hom ≫
            ((tpowTransport X₁ X₂ F hunit hten L (k + 1)).hom ⊗ₘ
              (tpowTransport X₁ X₂ F hunit hten M (k + 1)).hom) =
          ((tensorComparison X₁ X₂ F hten (tpow X₁ L k) L).hom ⊗ₘ
              (tensorComparison X₁ X₂ F hten (tpow X₁ M k) M).hom) ≫
            ((((tpowTransport X₁ X₂ F hunit hten L k).hom ⊗ₘ 𝟙 (F.obj L)) ≫
                (tpowSuccIso X₂ (F.obj L) k).hom) ⊗ₘ
              (((tpowTransport X₁ X₂ F hunit hten M k).hom ⊗ₘ 𝟙 (F.obj M)) ≫
                (tpowSuccIso X₂ (F.obj M) k).hom)) := by
        rw [tensorIsoOfModules_hom, Functor.mapIso_hom, Functor.mapIso_hom,
          MonoidalCategory.tensorHom_comp_tensorHom, ← tpowTransport_succ_comm,
          ← tpowTransport_succ_comm, ← MonoidalCategory.tensorHom_comp_tensorHom]
      have hmuBase : F.map (tensorInterchangeIso X₁ (tpow X₁ L k) (tpow X₁ M k) L M).hom ≫
            ((tensorComparison X₁ X₂ F hten (tensorSheafOfModules X₁ (tpow X₁ L k) L)
                (tensorSheafOfModules X₁ (tpow X₁ M k) M)).hom ≫
              ((tensorComparison X₁ X₂ F hten (tpow X₁ L k) L).hom ⊗ₘ
                (tensorComparison X₁ X₂ F hten (tpow X₁ M k) M).hom)) =
          ((tensorComparison X₁ X₂ F hten
                (tensorSheafOfModules X₁ (tpow X₁ L k) (tpow X₁ M k))
                (tensorSheafOfModules X₁ L M)).hom ≫
              ((tensorComparison X₁ X₂ F hten (tpow X₁ L k) (tpow X₁ M k)).hom ⊗ₘ
                (tensorComparison X₁ X₂ F hten L M).hom)) ≫
            tensorμ (F.obj (tpow X₁ L k)) (F.obj (tpow X₁ M k)) (F.obj L) (F.obj M) :=
        tensorComparison_tensorMu F (tensorComparison X₁ X₂ F hten) hnat' hassoc' hbraid'
          (tpow X₁ L k) (tpow X₁ M k) L M
      have hfront : ∀ {W : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)}
          (g : tensorSheafOfModules X₂
              (tensorSheafOfModules X₂ (F.obj (tpow X₁ L k)) (F.obj L))
              (tensorSheafOfModules X₂ (F.obj (tpow X₁ M k)) (F.obj M)) ⟶ W),
          F.map (tensorIsoOfModules X₁ (tpowTensorIso X₁ L M k)
                (Iso.refl (tensorSheafOfModules X₁ L M))).hom ≫
              F.map (tensorInterchangeIso X₁ (tpow X₁ L k) (tpow X₁ M k) L M).hom ≫
              (tensorComparison X₁ X₂ F hten (tensorSheafOfModules X₁ (tpow X₁ L k) L)
                (tensorSheafOfModules X₁ (tpow X₁ M k) M)).hom ≫
              ((tensorComparison X₁ X₂ F hten (tpow X₁ L k) L).hom ⊗ₘ
                (tensorComparison X₁ X₂ F hten (tpow X₁ M k) M).hom) ≫ g =
            (tensorComparison X₁ X₂ F hten (tpow X₁ (tensorSheafOfModules X₁ L M) k)
                (tensorSheafOfModules X₁ L M)).hom ≫
              ((F.map (tpowTensorIso X₁ L M k).hom ≫
                  (tensorComparison X₁ X₂ F hten (tpow X₁ L k) (tpow X₁ M k)).hom) ⊗ₘ
                (tensorComparison X₁ X₂ F hten L M).hom) ≫
              tensorμ (F.obj (tpow X₁ L k)) (F.obj (tpow X₁ M k)) (F.obj L) (F.obj M) ≫ g := by
        intro W g
        rw [(reassoc_of% hmuBase) g,
          hnatI (tpowTensorIso X₁ L M k) (Iso.refl (tensorSheafOfModules X₁ L M)),
          tensorIsoOfModules_hom, Functor.mapIso_hom, Functor.mapIso_hom, Iso.refl_hom,
          F.map_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp]
      have hLHS : F.map (tpowSuccIso X₁ (tensorSheafOfModules X₁ L M) k).hom ≫
            (F.map (tpowTensorIso X₁ L M (k + 1)).hom ≫
              (tensorComparison X₁ X₂ F hten (tpow X₁ L (k + 1)) (tpow X₁ M (k + 1))).hom ≫
              ((tpowTransport X₁ X₂ F hunit hten L (k + 1)).hom ⊗ₘ
                (tpowTransport X₁ X₂ F hunit hten M (k + 1)).hom)) =
          (tensorComparison X₁ X₂ F hten (tpow X₁ (tensorSheafOfModules X₁ L M) k)
              (tensorSheafOfModules X₁ L M)).hom ≫
            ((F.map (tpowTensorIso X₁ L M k).hom ≫
                (tensorComparison X₁ X₂ F hten (tpow X₁ L k) (tpow X₁ M k)).hom) ⊗ₘ
              (tensorComparison X₁ X₂ F hten L M).hom) ≫
            tensorμ (F.obj (tpow X₁ L k)) (F.obj (tpow X₁ M k)) (F.obj L) (F.obj M) ≫
            ((((tpowTransport X₁ X₂ F hunit hten L k).hom ⊗ₘ 𝟙 (F.obj L)) ≫
                (tpowSuccIso X₂ (F.obj L) k).hom) ⊗ₘ
              (((tpowTransport X₁ X₂ F hunit hten M k).hom ⊗ₘ 𝟙 (F.obj M)) ≫
                (tpowSuccIso X₂ (F.obj M) k).hom)) := by
        rw [tpowTensorIso_succ]
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, F.map_comp]
        rw [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp,
          hnatI (tpowSuccIso X₁ L k) (tpowSuccIso X₁ M k), htail, hfront]
      have hRHS : F.map (tpowSuccIso X₁ (tensorSheafOfModules X₁ L M) k).hom ≫
            ((tpowTransport X₁ X₂ F hunit hten (tensorSheafOfModules X₁ L M) (k + 1)).hom ≫
              (powerMap X₂ (tensorComparison X₁ X₂ F hten L M) (k + 1)).hom ≫
              (tpowTensorIso X₂ (F.obj L) (F.obj M) (k + 1)).hom) =
          (tensorComparison X₁ X₂ F hten (tpow X₁ (tensorSheafOfModules X₁ L M) k)
              (tensorSheafOfModules X₁ L M)).hom ≫
            (((tpowTransport X₁ X₂ F hunit hten (tensorSheafOfModules X₁ L M) k).hom ≫
                (powerMap X₂ (tensorComparison X₁ X₂ F hten L M) k).hom ≫
                (tpowTensorIso X₂ (F.obj L) (F.obj M) k).hom) ⊗ₘ
              (tensorComparison X₁ X₂ F hten L M).hom) ≫
            tensorμ (tpow X₂ (F.obj L) k) (tpow X₂ (F.obj M) k) (F.obj L) (F.obj M) ≫
            ((tpowSuccIso X₂ (F.obj L) k).hom ⊗ₘ (tpowSuccIso X₂ (F.obj M) k).hom) := by
        rw [← Category.assoc, ← tpowTransport_succ_comm, powerMap_succ_tensorIsoOfModules,
          tpowTensorIso_succ]
        simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, tensorIsoOfModules_hom,
          tensorInterchangeIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
        simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp,
          Category.comp_id]
      rw [hLHS, hRHS]
      exact congrArg (fun z => (tensorComparison X₁ X₂ F hten
          (tpow X₁ (tensorSheafOfModules X₁ L M) k) (tensorSheafOfModules X₁ L M)).hom ≫ z)
        (tensorMu_transport_step
          (F.map (tpowTensorIso X₁ L M k).hom ≫
            (tensorComparison X₁ X₂ F hten (tpow X₁ L k) (tpow X₁ M k)).hom)
          (tensorComparison X₁ X₂ F hten L M).hom
          (tpowTransport X₁ X₂ F hunit hten L k).hom
          (tpowTransport X₁ X₂ F hunit hten M k).hom
          ((tpowTransport X₁ X₂ F hunit hten (tensorSheafOfModules X₁ L M) k).hom ≫
            (powerMap X₂ (tensorComparison X₁ X₂ F hten L M) k).hom ≫
            (tpowTensorIso X₂ (F.obj L) (F.obj M) k).hom)
          (tpowSuccIso X₂ (F.obj L) k).hom (tpowSuccIso X₂ (F.obj M) k).hom
          (by rw [Category.assoc]; exact ih))

/-- **The transport of tensor powers is compatible with the splitting of the tensor power of a
tensor product.**  The three further coherences of the object-level comparisons — with the
associativity constraint, the symmetry constraint and the right unit constraint of Tag 01CA — are
explicit data, as is the naturality of the tensor comparison: see the discussion at the head of
this file. -/
theorem powerTransportIso_tensor
    (hunit : Picard.UnitIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hten : Picard.TensorIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F)
    (hnat : TensorIsoNatural X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hten)
    (hassoc : TensorIsoAssociator X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hten)
    (hbraid : TensorIsoBraiding X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hten)
    (hrunit : TensorIsoRightUnitor X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten)
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))
    [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 L]
      [IsInvertible X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 M]
    (k : ℕ) :
    letI := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L
    letI := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten M
    letI := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten
      (tensorSheafOfModules X₁ L M)
    letI := Stacks.SheafOfModules.isInvertible_tensorSheaf X₂.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 (F.obj L) (F.obj M)
    F.map (tpowTensorIso X₁ L M k).hom ≫
        (hten (tpow X₁ L k) (tpow X₁ M k)).hom ≫
        (tensorIsoOfModules X₂
          (powerTransportIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L k)
          (powerTransportIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten
            M k)).hom =
      (powerTransportIso X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten
          (tensorSheafOfModules X₁ L M) k).hom ≫
        (powerMap X₂ (hten L M) k).hom ≫
        (tpowTensorIso X₂ (F.obj L) (F.obj M) k).hom := by
  let := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten L
  let := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten M
  let := isInvertible_obj X₁.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O).2 X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 F hunit hten
    (tensorSheafOfModules X₁ L M)
  let := Stacks.SheafOfModules.isInvertible_tensorSheaf X₂.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O).2 (F.obj L) (F.obj M)
  exact tpowTransport_tensor X₁ X₂ F hunit hten hnat hassoc hbraid hrunit L M k

end RingedSites

end Stacks.SheafOfModules.TensorPowerTransport

end
