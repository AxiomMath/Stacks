module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap

/-!
# The projection-formula map at a unit object which is only a unit up to a shift

`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj` derives the
invertibility of the abstract projection-formula morphism
`CategoryTheory.adjunctionTensorMap adj A B α G eC` from a *right-unitor coherence*: for a
functor `L : C ⥤ D` with right adjoint `R`, bifunctors `A` on `C` and `B` on `D`, a morphism of
bifunctors `α : A ⋙ L ⟶ (L × L) ⋙ B`, right unitors `ρA Z : A(Z, eC) ≅ Z`,
`ρB W : B(W, eD) ≅ W` and a unit comparison `ν : L(eC) ≅ eD`, the equation

`α.app (Z, eC) ≫ B(𝟙, ν) ≫ ρB(L Z) = L(ρA Z)`.

This file is the same development for an object `eC` which is a unit only **up to a functor**:
`ρA Z : A(Z, eC) ≅ S_C Z` and `ρB W : B(W, eD) ≅ S_D W` for functors `S_C` on `C` and `S_D` on
`D`, with a comparison `γ : S_C ⋙ L ⟶ L ⋙ S_D` entering the coherence as

`α.app (Z, eC) ≫ B(𝟙, ν) ≫ ρB(L Z) = L(ρA Z) ≫ γ.app Z`.

The case this is for is the structure sheaf placed in a degree `q ≠ 0`: it is not the unit of
`⊗^𝐋`, and `Z ⊗^𝐋 𝒪[q]` is `Z⟦-q⟧` rather than `Z`, so `S_C` and `S_D` are the shift functors
by `-q` and `γ` is the commutation of `L` with that shift.

## Main results

* `Stacks.AlgebraicGeometry.ProjectionFormula.shiftedUnitorCoherence_of_iso` and
  `shiftedUnitorCoherence_of_essSurj`: the twisted coherence is invariant under isomorphism in
  `Z`, hence needs checking only on an essentially surjective family — which is what makes it
  checkable, since the comparisons it is built from are computable only on a distinguished class
  of objects.
* `Stacks.AlgebraicGeometry.ProjectionFormula.homEquiv_commShift_counit`: **the mate of the
  commutation of a left adjoint with the shift is the commutation of the right adjoint with the
  shift.**  Explicitly, `γ.app (R G) ≫ (ε_G)⟦a⟧'` has adjoint transpose
  `(R.commShiftIso a).inv.app G`, so that transpose is invertible.
* `Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_shiftedUnitObj_comp`: the
  twisted projection-formula map, composed with the unit comparison and the two twisted unitors,
  is `ρA(R G)` followed by that mate.
* `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_shiftedUnitObj`: **the
  projection-formula map at a shifted unit object is an isomorphism** as soon as the twisted
  coherence holds, for `S_C` and `S_D` the shifts by one and the same element of a group acting
  on both categories and `γ` the commutation isomorphism of `L`.

## Implementation notes

**Why the mate is an isomorphism, and why no `CategoryTheory.Adjunction.CommShift` hypothesis is
needed.**  The composite `ρA(R G)⁻¹ ≫ (the twisted projection-formula map)` is the adjoint
transpose of `γ.app (R G) ≫ (ε_G)⟦a⟧'`, a morphism `(R G)⟦a⟧ ⟶ R(G⟦a⟧)`; so the invertibility of
the projection-formula map is exactly the invertibility of that transpose.  Mathlib's
`CategoryTheory.Adjunction.rightAdjointCommShift` constructs, out of a `CommShift` structure on
`L` alone, a compatible one on `R`, and `CategoryTheory.Adjunction.shift_unit_app` then forces the
transpose to be `(R.commShiftIso a).inv.app G`: an isomorphism.  So the hypothesis is only
`L.CommShift`, and which `CommShift` structure `R` carries is immaterial — the conclusion does
not mention it.

**The product morphisms are ascribed**, as in
`StacksFrontier/AlgebraicGeometry/Duality/RightUnitorCoherenceInvariance.lean`: each `u ×ₘ 𝟙`
carries an explicit type ascription naming its source and target in the product category, so that
the statements match syntactically the shape the consumer produces.

## References

* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
-/

@[expose] public section

open CategoryTheory

open scoped CategoryTheory.Prod

namespace Stacks.AlgebraicGeometry.ProjectionFormula

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ## Invariance of the twisted coherence under isomorphism -/

/-- A functor on a product category sends the two ways around a commuting square of product
morphisms `f ×ₘ 𝟙` and `𝟙 ×ₘ g` to equal composites. -/
private theorem map_prod_id_comp_prod_id_comm {D : Type u₂} [Category.{v₂} D] (B : D × D ⥤ D)
    {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    B.map ((f ×ₘ 𝟙 Y) : ((X, Y) : D × D) ⟶ (X', Y)) ≫
        B.map ((𝟙 X' ×ₘ g) : ((X', Y) : D × D) ⟶ (X', Y')) =
      B.map ((𝟙 X ×ₘ g) : ((X, Y) : D × D) ⟶ (X, Y')) ≫
        B.map ((f ×ₘ 𝟙 Y') : ((X, Y') : D × D) ⟶ (X', Y')) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply Prod.ext <;> simp

section Invariance

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {eC : C} {eD : D} {SC : C ⥤ C} {SD : D ⥤ D}
  (ρA : ∀ Z : C, A.obj (Z, eC) ≅ SC.obj Z) (ρB : ∀ W : D, B.obj (W, eD) ≅ SD.obj W)
  (γ : SC ⋙ L ⟶ L ⋙ SD) (ν : L.obj eC ⟶ eD)

/-- **The twisted right-unitor coherence transports backwards along an isomorphism of the
object.**  If it holds at `Z'` and `i : Z ≅ Z'`, it holds at `Z`.  The unit comparison `ν` is a
morphism, not an isomorphism: nothing below inverts it.

The proof is the naturality square of `α` at `(i.hom, 𝟙 eC)`, pasted against the naturality of
the two twisted unitors and of `γ`; the four together prove the wanted equation composed with the
isomorphism `S_D(L(i.hom))`, which is then cancelled. -/
theorem shiftedUnitorCoherence_of_iso
    (hρA : ∀ {Z Z' : C} (u : Z ⟶ Z'),
      A.map ((u ×ₘ 𝟙 eC) : ((Z, eC) : C × C) ⟶ (Z', eC)) ≫ (ρA Z').hom =
        (ρA Z).hom ≫ SC.map u)
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 eD) : ((W, eD) : D × D) ⟶ (W', eD)) ≫ (ρB W').hom =
        (ρB W).hom ≫ SD.map u)
    {Z Z' : C} (i : Z ≅ Z')
    (h : α.app (Z', eC) ≫ B.map ((𝟙 (L.obj Z') ×ₘ ν) :
          ((L.obj Z', L.obj eC) : D × D) ⟶ (L.obj Z', eD)) ≫ (ρB (L.obj Z')).hom =
        L.map (ρA Z').hom ≫ γ.app Z') :
    α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν) :
        ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom =
      L.map (ρA Z).hom ≫ γ.app Z := by
  have : IsIso (L.map i.hom) := (L.mapIso i).isIso_hom
  have : IsIso (SD.map (L.map i.hom)) := (SD.mapIso (L.mapIso i)).isIso_hom
  have hα := α.naturality ((i.hom ×ₘ 𝟙 eC) : ((Z, eC) : C × C) ⟶ (Z', eC))
  dsimp only [Functor.comp_map, Functor.prod_map] at hα
  rw [CategoryTheory.Functor.map_id] at hα
  have hγ : L.map (SC.map i.hom) ≫ γ.app Z' = γ.app Z ≫ SD.map (L.map i.hom) :=
    γ.naturality i.hom
  have hmid := (map_prod_id_comp_prod_id_comm B (L.map i.hom) ν).symm
  apply (cancel_mono (SD.map (L.map i.hom))).1
  have hlhs : (α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν) :
          ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom) ≫
        SD.map (L.map i.hom) =
      L.map (A.map ((i.hom ×ₘ 𝟙 eC) : ((Z, eC) : C × C) ⟶ (Z', eC))) ≫
        L.map (ρA Z').hom ≫ γ.app Z' := by
    simp only [Category.assoc]
    rw [← hρB (L.map i.hom), ← Category.assoc (B.map ((𝟙 (L.obj Z) ×ₘ ν) :
        ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD))), hmid, Category.assoc,
      ← Category.assoc (α.app (Z, eC)), ← hα, Category.assoc, h]
  rw [hlhs, ← CategoryTheory.Functor.map_comp_assoc, hρA i.hom,
    CategoryTheory.Functor.map_comp_assoc, hγ, Category.assoc]

/-- **The twisted right-unitor coherence needs checking only on an essentially surjective
family.**  If it holds at `G.obj e` for every object `e` of `E`, and `G : E ⥤ C` is essentially
surjective, then it holds at every object of `C`.

This is what makes the equation checkable: the comparisons it is built from are descended from a
distinguished class of objects — K-flat complexes, or the images of a localization — and
`CategoryTheory.Functor.objObjPreimageIso` is the isomorphism `shiftedUnitorCoherence_of_iso`
consumes. -/
theorem shiftedUnitorCoherence_of_essSurj {E : Type u₃} [Category.{v₃} E] (G : E ⥤ C)
    [G.EssSurj]
    (hρA : ∀ {Z Z' : C} (u : Z ⟶ Z'),
      A.map ((u ×ₘ 𝟙 eC) : ((Z, eC) : C × C) ⟶ (Z', eC)) ≫ (ρA Z').hom =
        (ρA Z).hom ≫ SC.map u)
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 eD) : ((W, eD) : D × D) ⟶ (W', eD)) ≫ (ρB W').hom =
        (ρB W).hom ≫ SD.map u)
    (h : ∀ e : E, α.app (G.obj e, eC) ≫ B.map ((𝟙 (L.obj (G.obj e)) ×ₘ ν) :
          ((L.obj (G.obj e), L.obj eC) : D × D) ⟶ (L.obj (G.obj e), eD)) ≫
            (ρB (L.obj (G.obj e))).hom =
        L.map (ρA (G.obj e)).hom ≫ γ.app (G.obj e)) (Z : C) :
    α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν) :
        ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom =
      L.map (ρA Z).hom ≫ γ.app Z :=
  shiftedUnitorCoherence_of_iso A B α ρA ρB γ ν hρA hρB (G.objObjPreimageIso Z).symm
    (h (G.objPreimage Z))

end Invariance

/-! ## The mate of the commutation of a left adjoint with the shift -/

section Mate

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- **The adjoint transpose of `γ.app (R G) ≫ (ε_G)⟦a⟧'` is `(R.commShiftIso a).inv.app G`**,
where `γ` is the commutation of the left adjoint with the shift by `a` and `ε` is the counit.

This is the classical fact that the mate of the commutation isomorphism of `L` is the one of `R`,
in the one form the twisted projection formula needs: the transpose is an *isomorphism*.  The
proof is `CategoryTheory.Adjunction.shift_unit_app`, which replaces
`unit ≫ R(γ)` by `(unit)⟦a⟧' ≫ (R.commShiftIso a).inv`, followed by the naturality of
`(R.commShiftIso a).inv` at the counit and the right triangle identity. -/
theorem homEquiv_commShift_counit {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M]
    [L.CommShift M] [R.CommShift M] [adj.CommShift M] (a : M) (G : D) :
    adj.homEquiv ((R.obj G)⟦a⟧) (G⟦a⟧)
        ((L.commShiftIso a).hom.app (R.obj G) ≫ (adj.counit.app G)⟦a⟧') =
      (R.commShiftIso a).inv.app G := by
  have key : adj.unit.app ((R.obj G)⟦a⟧) ≫ R.map ((L.commShiftIso a).hom.app (R.obj G)) =
      (adj.unit.app (R.obj G))⟦a⟧' ≫ (R.commShiftIso a).inv.app (L.obj (R.obj G)) := by
    rw [Adjunction.shift_unit_app adj a (R.obj G)]
    simp
  have hnat : (R.commShiftIso a).inv.app (L.obj (R.obj G)) ≫
        R.map ((adj.counit.app G)⟦a⟧') =
      (R.map (adj.counit.app G))⟦a⟧' ≫ (R.commShiftIso a).inv.app G :=
    ((R.commShiftIso a).inv.naturality (adj.counit.app G)).symm
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, ← Category.assoc, key,
    Category.assoc, hnat, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    adj.right_triangle_components]
  simp

end Mate

/-! ## The abstract reduction at a shifted unit object -/

section Abstract

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {eC : C} {eD : D} {SC : C ⥤ C} {SD : D ⥤ D}
  (ρA : ∀ Z : C, A.obj (Z, eC) ≅ SC.obj Z) (ρB : ∀ W : D, B.obj (W, eD) ≅ SD.obj W)
  (γ : SC ⋙ L ⟶ L ⋙ SD) (ν : L.obj eC ≅ eD)

/-- **The twisted projection-formula map at the shifted unit object, composed with the two
twisted unitors and the unit comparison, is `ρA(R G)` followed by the mate of `γ`.**  The two
hypotheses are the naturality of the twisted unitor of `B` and the twisted coherence of `α`;
everything else is the triangle identity of `L ⊣ R`. -/
theorem adjunctionTensorMap_shiftedUnitObj_comp
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 eD) : ((W, eD) : D × D) ⟶ (W', eD)) ≫ (ρB W').hom =
        (ρB W).hom ≫ SD.map u)
    (hcoh : ∀ Z : C, α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν.hom) :
          ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom =
        L.map (ρA Z).hom ≫ γ.app Z)
    (G : D) :
    adjunctionTensorMap adj A B α G eC ≫
        R.map (B.map ((𝟙 G ×ₘ ν.hom) : ((G, L.obj eC) : D × D) ⟶ (G, eD)) ≫ (ρB G).hom) =
      (ρA (R.obj G)).hom ≫
        adj.homEquiv (SC.obj (R.obj G)) (SD.obj G)
          (γ.app (R.obj G) ≫ SD.map (adj.counit.app G)) := by
  have h1 := map_prod_id_comp_prod_id_comm B (X := L.obj (R.obj G)) (X' := G)
    (adj.counit.app G) ν.hom
  have hinner : (α.app (R.obj G, eC) ≫ B.map ((adj.counit.app G ×ₘ 𝟙 (L.obj eC)) :
          ((L.obj (R.obj G), L.obj eC) : D × D) ⟶ (G, L.obj eC))) ≫
        (B.map ((𝟙 G ×ₘ ν.hom) : ((G, L.obj eC) : D × D) ⟶ (G, eD)) ≫ (ρB G).hom) =
      L.map (ρA (R.obj G)).hom ≫ γ.app (R.obj G) ≫ SD.map (adj.counit.app G) := by
    simp only [Category.assoc]
    rw [← Category.assoc (B.map ((adj.counit.app G ×ₘ 𝟙 (L.obj eC)) :
        ((L.obj (R.obj G), L.obj eC) : D × D) ⟶ (G, L.obj eC))), h1, Category.assoc,
      hρB (W := L.obj (R.obj G)) (W' := G) (adj.counit.app G),
      reassoc_of% (hcoh (R.obj G))]
  unfold adjunctionTensorMap
  rw [← Adjunction.homEquiv_naturality_right, hinner, Adjunction.homEquiv_naturality_left]

/-- **The projection-formula map at a shifted unit object is an isomorphism as soon as the
twisted coherence holds and the mate of `γ` is invertible.**  Its composite with the two twisted
unitors and the unit comparison is `ρA(R G)` followed by that mate, by
`adjunctionTensorMap_shiftedUnitObj_comp`, and the unitors and the unit comparison are
invertible. -/
theorem isIso_adjunctionTensorMap_shiftedUnitObj_of_isIso_mate
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 eD) : ((W, eD) : D × D) ⟶ (W', eD)) ≫ (ρB W').hom =
        (ρB W).hom ≫ SD.map u)
    (hcoh : ∀ Z : C, α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν.hom) :
          ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom =
        L.map (ρA Z).hom ≫ γ.app Z)
    (G : D)
    (hmate : IsIso (adj.homEquiv (SC.obj (R.obj G)) (SD.obj G)
      (γ.app (R.obj G) ≫ SD.map (adj.counit.app G)))) :
    IsIso (adjunctionTensorMap adj A B α G eC) := by
  have : IsIso ((𝟙 G ×ₘ ν.hom) : ((G, L.obj eC) : D × D) ⟶ (G, eD)) :=
    ⟨(𝟙 G ×ₘ ν.inv), by apply Prod.ext <;> simp, by apply Prod.ext <;> simp⟩
  have : IsIso (B.map ((𝟙 G ×ₘ ν.hom) : ((G, L.obj eC) : D × D) ⟶ (G, eD)) ≫
    (ρB G).hom) := inferInstance
  have := hmate
  have h := adjunctionTensorMap_shiftedUnitObj_comp adj A B α ρA ρB γ ν hρB hcoh G
  have h2 : adjunctionTensorMap adj A B α G eC =
      ((ρA (R.obj G)).hom ≫
          adj.homEquiv (SC.obj (R.obj G)) (SD.obj G)
            (γ.app (R.obj G) ≫ SD.map (adj.counit.app G))) ≫
        inv (R.map (B.map ((𝟙 G ×ₘ ν.hom) : ((G, L.obj eC) : D × D) ⟶ (G, eD)) ≫
          (ρB G).hom)) := by
    rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h2]
  infer_instance

end Abstract

/-! ## The abstract reduction at a shift of the unit object -/

section Shift

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {eC : C} {eD : D}

/-- **The projection-formula map at a shifted unit object is an isomorphism.**  Let `S_C` and
`S_D` be the shifts by one and the same element `a` of a group `M` acting on `C` and on `D`, let
`L` commute with those shifts, and let the twisted right-unitor coherence hold with `γ` the
commutation isomorphism of `L`.  Then `adjunctionTensorMap adj A B α G eC` is an isomorphism for
every `G`.

The only hypothesis on the shifts is `L.CommShift M`: the `CommShift` structure on `R` that makes
the mate of `γ` an isomorphism is the one Mathlib builds from it,
`CategoryTheory.Adjunction.rightAdjointCommShift`, and the conclusion does not mention it. -/
theorem isIso_adjunctionTensorMap_shiftedUnitObj {M : Type*} [AddGroup M]
    [HasShift C M] [HasShift D M] [L.CommShift M] (a : M)
    (ρA : ∀ Z : C, A.obj (Z, eC) ≅ (shiftFunctor C a).obj Z)
    (ρB : ∀ W : D, B.obj (W, eD) ≅ (shiftFunctor D a).obj W)
    (ν : L.obj eC ≅ eD)
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 eD) : ((W, eD) : D × D) ⟶ (W', eD)) ≫ (ρB W').hom =
        (ρB W).hom ≫ (shiftFunctor D a).map u)
    (hcoh : ∀ Z : C, α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν.hom) :
          ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom =
        L.map (ρA Z).hom ≫ (L.commShiftIso a).hom.app Z)
    (G : D) :
    IsIso (adjunctionTensorMap adj A B α G eC) := by
  let : R.CommShift M := adj.rightAdjointCommShift M
  have : adj.CommShift M := adj.commShift_of_leftAdjoint M
  refine isIso_adjunctionTensorMap_shiftedUnitObj_of_isIso_mate adj A B α ρA ρB
    (L.commShiftIso a).hom ν hρB hcoh G ?_
  rw [homEquiv_commShift_counit adj a G]
  infer_instance

end Shift

end Stacks.AlgebraicGeometry.ProjectionFormula

end
