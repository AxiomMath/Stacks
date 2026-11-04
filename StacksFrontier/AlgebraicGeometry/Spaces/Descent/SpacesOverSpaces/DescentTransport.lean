module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.Transport
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Descent

/-!
# The move operation of a descent datum for algebraic spaces

The gluing isomorphisms of a descent datum for a family of morphisms of algebraic spaces
satisfy a cocycle condition, so they are the same data as a move operation in the sense of
`CategoryTheory.FamilyTransport` in `CategoryTheory.Over T`, in which the pairwise fibre
product `X i ×_T X j` is the binary product. This file constructs the move operation, gives
criteria for a family of maps to be a morphism or an isomorphism of descent data, and describes
the move operation under a morphism of descent data.

## Main definitions

* `AlgebraicGeometry.Space.Descent.DescentData.transport` is the move operation of a descent
  datum.
* `AlgebraicGeometry.Space.Descent.DescentData.homOfMove` builds a morphism of descent data
  from a family of maps commuting with the move operations.
* `AlgebraicGeometry.Space.Descent.DescentData.isoMk` builds an isomorphism of descent data
  from a family of isomorphisms commuting with the gluing isomorphisms.

## Main results

* `AlgebraicGeometry.Space.Descent.DescentData.gluing_hom_fst` and
  `AlgebraicGeometry.Space.Descent.DescentData.gluing_hom_snd_structureMap`: a gluing
  isomorphism preserves the pairwise base.
* `AlgebraicGeometry.Space.Descent.DescentData.transport_gluing`: the gluing isomorphisms
  recovered from the move operation are the original ones.
* `AlgebraicGeometry.Space.Descent.DescentData.move_naturality`: a morphism of descent data
  commutes with the move operations.

## References

* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Over

/-- `CategoryTheory.Over.map` is faithful. -/
lemma map_injective {C : Type*} [Category C] {R Y : C} (f : Y ⟶ R) {A E : Over Y}
    {a b : A ⟶ E} (h : (Over.map f).map a = (Over.map f).map b) : a = b := by
  exact Over.OverMorphism.ext (by simpa using congrArg Over.Hom.left h)

end CategoryTheory.Over

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A map of spaces over `Y` composed with the structure map of its target is the structure map
of its source. -/
@[reassoc (attr := simp)]
lemma structureMap_naturality {R Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ R) {A E : Over Y}
    (m : A ⟶ E) : (Over.map g).map m ≫ structureMap g E = structureMap g A :=
  Over.OverMorphism.ext (Over.w m)

variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ T}
    {hT : IsAlgebraicSpace B S hS T} {hX : ∀ i, IsAlgebraicSpace B S hS (X i)}

namespace DescentData

/-- The gluing isomorphism preserves the first component of the pairwise base. -/
@[reassoc (attr := simp)]
lemma gluing_hom_fst (D : DescentData f hT hX) (i j : ι) :
    (D.gluing i j).hom.left ≫ prod.fst = prod.fst ≫ structureMap (f i) (D.obj i) := by
  simpa using congrArg (fun g ↦ g ≫ prod.fst) (Over.w (D.gluing i j).hom)

/-- The gluing isomorphism preserves the second component of the pairwise base. -/
@[reassoc (attr := simp)]
lemma gluing_hom_snd_structureMap (D : DescentData f hT hX) (i j : ι) :
    (D.gluing i j).hom.left ≫ prod.snd ≫ structureMap (f j) (D.obj j) = prod.snd := by
  simpa using congrArg (fun g ↦ g ≫ prod.snd) (Over.w (D.gluing i j).hom)

/-- The move operation of a descent datum: a point of the `i`-th space over a point of
`X i ×_T X j` is carried to a point of the `j`-th space by the gluing isomorphism. -/
def transport (D : DescentData f hT hX) :
    FamilyTransport (fun i ↦ (Over.map (f i)).obj (D.obj i)) (fun i ↦ Over.mk (f i))
      (fun i ↦ structureMap (f i) (D.obj i)) :=
  familyTransportOfGluing _ D.gluing D.cocycle

/-- The move operation of a descent datum carries `v` over `y` to the second component of the
gluing isomorphism applied to the pair `(v, y)`. -/
@[simp]
lemma transport_move (D : DescentData f hT hX) {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (D.obj i)) (y : Z ⟶ Over.mk (f j)) :
    D.transport.move v y = prod.lift v y ≫ (D.gluing i j).hom.left ≫ prod.snd := rfl

/-- The gluing isomorphisms recovered from the move operation are the original ones. -/
@[simp]
lemma transport_gluing (D : DescentData f hT hX) (i j : ι) :
    D.transport.gluing i j = D.gluing i j := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply prod.hom_ext <;> simp

/-- A morphism of descent data commutes with the move operations. -/
lemma move_naturality {D E : DescentData f hT hX} (φ : D ⟶ E) {i j : ι} {Z : Over T}
    (v : Z ⟶ (Over.map (f i)).obj (D.obj i)) (y : Z ⟶ Over.mk (f j)) :
    D.transport.move v y ≫ (Over.map (f j)).map (φ.hom j) =
      E.transport.move (v ≫ (Over.map (f i)).map (φ.hom i)) y := by
  simpa [Category.assoc, prod.lift_map, prod.comp_lift] using
    (congrArg (fun m ↦ prod.lift v y ≫ m ≫ prod.snd) (φ.comm i j)).symm

/-- A family of maps commuting with the move operations is a morphism of descent data. -/
def homOfMove {D E : DescentData f hT hX} (m : ∀ i, D.obj i ⟶ E.obj i)
    (hm : ∀ {i j : ι} {Z : Over T} (v : Z ⟶ (Over.map (f i)).obj (D.obj i))
      (y : Z ⟶ Over.mk (f j)), D.transport.move v y ≫ (Over.map (f j)).map (m j) =
        E.transport.move (v ≫ (Over.map (f i)).map (m i)) y) : D ⟶ E where
  hom := m
  comm i j := by
    simpa using D.transport.gluing_comm E.transport (fun i ↦ (Over.map (f i)).map (m i))
      (fun i ↦ structureMap_naturality (f i) (m i)) (fun v y ↦ hm v y) i j

/-- A family of isomorphisms commuting with the gluing isomorphisms is an isomorphism of
descent data. -/
def isoMk {D E : DescentData f hT hX} (e : ∀ i, D.obj i ≅ E.obj i)
    (comm : ∀ i j, prod.map ((Over.map (f i)).map (e i).hom) (𝟙 (Over.mk (f j))) ≫
        (E.gluing i j).hom.left =
      (D.gluing i j).hom.left ≫
        prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (e j).hom)) : D ≅ E where
  hom := { hom := fun i ↦ (e i).hom, comm := comm }
  inv :=
    { hom := fun i ↦ (e i).inv
      comm := by
        intro i j
        apply (cancel_epi
          (prod.map ((Over.map (f i)).map (e i).hom) (𝟙 (Over.mk (f j))))).mp
        apply (cancel_mono
          (prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (e j).hom))).mp
        simpa [Category.assoc, prod.map_map, Functor.map_comp] using (comm i j).symm }
  hom_inv_id := DescentData.Hom.ext (funext fun i ↦ (e i).hom_inv_id)
  inv_hom_id := DescentData.Hom.ext (funext fun i ↦ (e i).inv_hom_id)

end DescentData

end AlgebraicGeometry.Space.Descent

end
