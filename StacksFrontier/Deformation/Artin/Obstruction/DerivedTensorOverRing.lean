module

public import StacksFrontier.Homology.Tor.DerivedTensorFunctorLargeUniverse
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse

/-!
# The derived tensor product of the canonical tensor--Hom adjunction

`CochainComplex.DerivedTensor.derivedTensorProduct M` is the endofunctor `- ⊗ᴸ M` of `D(A)`
built from a K-flat resolution of a representative of `M`, and it is the one the obstruction
theory of a dual deformation situation is phrased with. The tensor--Hom adjunction
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` carries its own derived tensor product,
and that is the one duality for perfect complexes is proved for.

This file compares the two: for an object of `D(A)` represented by a K-flat complex — in
particular for a perfect object — the two endofunctors `- ⊗ᴸ M` are isomorphic.

## Main results

* `Deformation.Artin.tensorOverRingIso` — the K-flat comparison of the tensor product of
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, with its naturality in the first
  variable.
* `Deformation.Artin.nonempty_derivedTensorProduct_iso_tensorOverRing` — the two derived
  tensor products with a fixed K-flat-representable object agree as endofunctors of `D(A)`.

## Implementation notes

Both endofunctors become the ordinary total tensor product with the chosen K-flat
representative after restriction along the localization functor
`DerivedCategory.Q`: for `CochainComplex.DerivedTensor.derivedTensorProduct` this is
[Stacks, Tag 064M] as recorded in
`CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution`, and for the
adjunction it is the scalar transport of the K-flat comparison of
`StacksDraft.DerivedHom.DerivedHomData`. Since `DerivedCategory.Q` is a localization functor,
a natural isomorphism between the two restrictions descends to one between the two
endofunctors, which is `CategoryTheory.Localization.liftNatIso`.

The comparison for the adjunction is assembled here rather than taken from
`CochainComplex.DerivedTensor.derivedTensor_comparison`, which is the same composite but
recorded only object by object: the naturality in the first variable is exactly what the
descent needs, and it is the composite of the four naturality statements of the four factors.

## References

* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor StacksDraft.DerivedHom

universe u

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

section Bridge

variable (A : Type u) [CommRing A]

/-- The restriction-of-scalars equivalence of module categories used by the scalar
transport. -/
public abbrev liftEquiv : ModuleCat.{u} (ULift.{0} A) ≌ ModuleCat.{u} A :=
  uliftModuleEquivalence.{u, u, 0} A

/-- Restriction of scalars on complexes. -/
public abbrev liftComplex :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} (ULift.{0} A)) ℤ :=
  (liftEquiv A).inverse.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The scalar transport of derived categories. -/
public abbrev scalarEquiv :
    DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ≌ DerivedCategory (ModuleCat.{u} A) :=
  derivedScalarEquivalence.{u, 0, u + 1} A

/-- The tensor--Hom adjunction over the lifted ring, which is the one duality for perfect
complexes is proved for. -/
public abbrev liftedData : DerivedHomData (ULift.{0} A) :=
  derivedHomAdjunctionULift.{u, 0, u + 1} (R := A)

/-- The tensor--Hom adjunction over the ring itself. -/
public abbrev overRingData : DerivedHomAdjunction (R := A) :=
  derivedHomAdjunctionOverRing.{u, 0, u + 1} A

variable {A}
variable (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat)

include hP in
/-- Restriction of scalars along the canonical ring isomorphism preserves K-flatness. -/
public theorem kFlat_liftComplex : ((liftComplex A).obj P).KFlat :=
  isKFlat_restrictScalars_of_ringEquiv (ULift.ringEquiv.{u, 0} (R := A)) P hP

/-- **The K-flat comparison for the tensor product of the canonical tensor--Hom adjunction
over the ring.** It is the scalar transport of the K-flat comparison over the lifted ring:
the two localizations are compared by
`CochainComplex.DerivedTensor.scalarEquivalenceQObjIso`, the two tensor products by
`StacksDraft.DerivedHom.derivedTensorULiftIso`, and the two total tensor complexes by
`CochainComplex.DerivedTensor.scalarEquivalenceTensorComplexIso`. -/
public def tensorOverRingIso (Y : CochainComplex (ModuleCat.{u} A) ℤ) :
    (overRingData A).tensor.obj (DerivedCategory.Q.obj Y, DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (Y ⊗ P) :=
  (overRingData A).tensor.mapIso
      ((scalarEquivalenceQObjIso.{u, 0} A Y).symm.prod
        (scalarEquivalenceQObjIso.{u, 0} A P).symm) ≪≫
    (derivedTensorULiftIso.{u, 0, u + 1} A).app
      (DerivedCategory.Q.obj ((liftComplex A).obj Y),
        DerivedCategory.Q.obj ((liftComplex A).obj P)) ≪≫
    (scalarEquiv A).functor.mapIso
      ((liftedData A).tensorIso ((liftComplex A).obj Y) ((liftComplex A).obj P)
        (kFlat_liftComplex P hP)) ≪≫
    scalarEquivalenceTensorComplexIso.{u, 0} A Y P

include hP in
/-- The K-flat comparison of `Deformation.Artin.tensorOverRingIso` is natural in the first
complex. -/
public theorem tensorOverRingIso_naturality
    {Y Y' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Y ⟶ Y') :
    (overRingData A).tensor.map
          ((DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj P)) :
            ((DerivedCategory.Q.obj Y, DerivedCategory.Q.obj P) :
              DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
              (DerivedCategory.Q.obj Y', DerivedCategory.Q.obj P)) ≫
        (tensorOverRingIso P hP Y').hom =
      (tensorOverRingIso P hP Y).hom ≫ DerivedCategory.Q.map (f ⊗ₘ 𝟙 P) := by
  have hP₀ := kFlat_liftComplex P hP
  -- The comparison is a composite of four factors, and the naturality square is the pasting
  -- of the four naturality squares of those factors. Every intermediate object is named below
  -- by a `let` carrying an explicit type, so that each square and each associativity step is
  -- an identity between composites that are already spelled the same way: the types of the
  -- four factors involve the monoidal product of complexes, the restriction of scalars and
  -- two curried bifunctors, and the defeq identifying the spellings of an intermediate object
  -- holds only at default transparency, where these `let`s and `show` put it.
  let T := (overRingData A).tensor
  let S := (liftedData A).tensor
  let F := (scalarEquiv A).functor
  let Y₀ := (liftComplex A).obj Y
  let Y₀' := (liftComplex A).obj Y'
  let P₀ := (liftComplex A).obj P
  -- the four factors of the comparison at a complex `Z`
  let a (Z : CochainComplex (ModuleCat.{u} A) ℤ) :
      T.obj (DerivedCategory.Q.obj Z, DerivedCategory.Q.obj P) ⟶
      T.obj (F.obj (DerivedCategory.Q.obj ((liftComplex A).obj Z)),
        F.obj (DerivedCategory.Q.obj P₀)) :=
    T.map ((scalarEquivalenceQObjIso.{u, 0} A Z).symm.prod
      (scalarEquivalenceQObjIso.{u, 0} A P).symm).hom
  let b (Z : CochainComplex (ModuleCat.{u} A) ℤ) :
      T.obj (F.obj (DerivedCategory.Q.obj ((liftComplex A).obj Z)),
        F.obj (DerivedCategory.Q.obj P₀)) ⟶
      F.obj (S.obj (DerivedCategory.Q.obj ((liftComplex A).obj Z), DerivedCategory.Q.obj P₀)) :=
    (derivedTensorULiftIso.{u, 0, u + 1} A).hom.app
      (DerivedCategory.Q.obj ((liftComplex A).obj Z), DerivedCategory.Q.obj P₀)
  let c (Z : CochainComplex (ModuleCat.{u} A) ℤ) :
      F.obj (S.obj (DerivedCategory.Q.obj ((liftComplex A).obj Z), DerivedCategory.Q.obj P₀)) ⟶
      F.obj (DerivedCategory.Q.obj ((liftComplex A).obj Z ⊗ P₀)) :=
    F.map ((liftedData A).tensorIso ((liftComplex A).obj Z) P₀ hP₀).hom
  let d (Z : CochainComplex (ModuleCat.{u} A) ℤ) :
      F.obj (DerivedCategory.Q.obj ((liftComplex A).obj Z ⊗ P₀)) ⟶
      DerivedCategory.Q.obj (Z ⊗ P) :=
    (scalarEquivalenceTensorComplexIso.{u, 0} A Z P).hom
  -- the five horizontal maps induced by `f`
  let u : T.obj (DerivedCategory.Q.obj Y, DerivedCategory.Q.obj P) ⟶
      T.obj (DerivedCategory.Q.obj Y', DerivedCategory.Q.obj P) :=
    T.map (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj P))
  let v : T.obj (F.obj (DerivedCategory.Q.obj Y₀), F.obj (DerivedCategory.Q.obj P₀)) ⟶
      T.obj (F.obj (DerivedCategory.Q.obj Y₀'), F.obj (DerivedCategory.Q.obj P₀)) :=
    T.map (F.map (DerivedCategory.Q.map ((liftComplex A).map f)),
      F.map (DerivedCategory.Q.map (𝟙 P₀)))
  let w : F.obj (S.obj (DerivedCategory.Q.obj Y₀, DerivedCategory.Q.obj P₀)) ⟶
      F.obj (S.obj (DerivedCategory.Q.obj Y₀', DerivedCategory.Q.obj P₀)) :=
    F.map (S.map (DerivedCategory.Q.map ((liftComplex A).map f),
      DerivedCategory.Q.map (𝟙 P₀)))
  let x : F.obj (DerivedCategory.Q.obj (Y₀ ⊗ P₀)) ⟶
      F.obj (DerivedCategory.Q.obj (Y₀' ⊗ P₀)) :=
    F.map (DerivedCategory.Q.map ((liftComplex A).map f ⊗ₘ 𝟙 P₀))
  let y : DerivedCategory.Q.obj (Y ⊗ P) ⟶ DerivedCategory.Q.obj (Y' ⊗ P) :=
    DerivedCategory.Q.map (f ⊗ₘ 𝟙 P)
  -- the first square: the two localization comparisons
  have s1 : (overRingData A).tensor.map
          ((DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj P)) :
            ((DerivedCategory.Q.obj Y, DerivedCategory.Q.obj P) :
              DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
              (DerivedCategory.Q.obj Y', DerivedCategory.Q.obj P)) ≫
        (overRingData A).tensor.map
          (((scalarEquivalenceQObjIso.{u, 0} A Y').symm.prod
            (scalarEquivalenceQObjIso.{u, 0} A P).symm).hom) =
      (overRingData A).tensor.map
          (((scalarEquivalenceQObjIso.{u, 0} A Y).symm.prod
            (scalarEquivalenceQObjIso.{u, 0} A P).symm).hom) ≫
        (overRingData A).tensor.map
          (((scalarEquiv A).functor.map (DerivedCategory.Q.map ((liftComplex A).map f)),
              (scalarEquiv A).functor.map
                (DerivedCategory.Q.map (𝟙 ((liftComplex A).obj P)))) :
            (((scalarEquiv A).functor.obj (DerivedCategory.Q.obj ((liftComplex A).obj Y)),
                (scalarEquiv A).functor.obj
                  (DerivedCategory.Q.obj ((liftComplex A).obj P))) :
              DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
              ((scalarEquiv A).functor.obj (DerivedCategory.Q.obj ((liftComplex A).obj Y')),
                (scalarEquiv A).functor.obj
                  (DerivedCategory.Q.obj ((liftComplex A).obj P)))) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact Prod.ext (scalarEquivalenceQObjIso_inv_naturality.{u, 0} A f) (by simp)
  have q1 : u ≫ a Y' = a Y ≫ v := s1
  -- the second square: the scalar transport of the tensor product
  have s2 := (derivedTensorULiftIso.{u, 0, u + 1} A).hom.naturality
    ((DerivedCategory.Q.map ((liftComplex A).map f),
        DerivedCategory.Q.map (𝟙 ((liftComplex A).obj P))) :
      ((DerivedCategory.Q.obj ((liftComplex A).obj Y),
          DerivedCategory.Q.obj ((liftComplex A).obj P)) :
        DerivedCategory (ModuleCat.{u} (ULift.{0} A)) ×
          DerivedCategory (ModuleCat.{u} (ULift.{0} A))) ⟶
        (DerivedCategory.Q.obj ((liftComplex A).obj Y'),
          DerivedCategory.Q.obj ((liftComplex A).obj P)))
  simp only [Functor.comp_map, Functor.prod_map] at s2
  have q2 : v ≫ b Y' = b Y ≫ w := s2
  -- the third square: the K-flat comparison over the lifted ring
  have s3 := congrArg (scalarEquiv A).functor.map
    ((liftedData A).tensorIso_naturality ((liftComplex A).map f)
      (𝟙 ((liftComplex A).obj P)) hP₀ hP₀)
  simp only [Functor.map_comp] at s3
  have q3 : w ≫ c Y' = c Y ≫ x := s3
  -- the fourth square: the scalar transport of the total tensor complex
  have q4 : x ≫ d Y' = d Y ≫ y := scalarEquivalenceTensorComplexIso_naturality.{u, 0} A f (𝟙 P)
  -- the pasting of the four squares
  change u ≫ a Y' ≫ b Y' ≫ c Y' ≫ d Y' = (a Y ≫ b Y ≫ c Y ≫ d Y) ≫ y
  rw [reassoc_of% q1, reassoc_of% q2, reassoc_of% q3, q4]
  simp only [Category.assoc]

end Bridge

/-! ### Descending the comparison to the derived category -/

section Descent

variable {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat)

/-- The K-flat comparison read at an object isomorphic to `Q P`. -/
public def tensorOverRingIsoOf (M : DerivedCategory (ModuleCat.{u} A))
    (κ : DerivedCategory.Q.obj P ≅ M) (Y : CochainComplex (ModuleCat.{u} A) ℤ) :
    (overRingData A).tensor.obj (DerivedCategory.Q.obj Y, M) ≅
      DerivedCategory.Q.obj (Y ⊗ P) :=
  (overRingData A).tensor.mapIso (Iso.prod (Iso.refl (DerivedCategory.Q.obj Y)) κ.symm) ≪≫
    tensorOverRingIso P hP Y

include hP in
/-- The comparison at an arbitrary representative is natural in the first complex. -/
public theorem tensorOverRingIsoOf_naturality (M : DerivedCategory (ModuleCat.{u} A))
    (κ : DerivedCategory.Q.obj P ≅ M)
    {Y Y' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Y ⟶ Y') :
    (overRingData A).tensor.map
          ((DerivedCategory.Q.map f, 𝟙 M) :
            ((DerivedCategory.Q.obj Y, M) :
              DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
              (DerivedCategory.Q.obj Y', M)) ≫
        (tensorOverRingIsoOf P hP M κ Y').hom =
      (tensorOverRingIsoOf P hP M κ Y).hom ≫ DerivedCategory.Q.map (f ⊗ₘ 𝟙 P) := by
  have hcomm : (overRingData A).tensor.map
        ((DerivedCategory.Q.map f, 𝟙 M) :
          ((DerivedCategory.Q.obj Y, M) :
            DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
            (DerivedCategory.Q.obj Y', M)) ≫
      (overRingData A).tensor.map
        (Iso.prod (Iso.refl (DerivedCategory.Q.obj Y')) κ.symm).hom =
    (overRingData A).tensor.map
        (Iso.prod (Iso.refl (DerivedCategory.Q.obj Y)) κ.symm).hom ≫
      (overRingData A).tensor.map
        ((DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj P)) :
          ((DerivedCategory.Q.obj Y, DerivedCategory.Q.obj P) :
            DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
            (DerivedCategory.Q.obj Y', DerivedCategory.Q.obj P)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact Prod.ext (by simp) (by simp)
  dsimp only [tensorOverRingIsoOf, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hcomm, Category.assoc, tensorOverRingIso_naturality P hP f,
    Category.assoc]

include hP in
/-- The naturality square, at a morphism of cochain complexes, of the composite comparison
that descends `Deformation.Artin.tensorOverRingIso` along the localization of the homotopy
category.

This is the naturality obligation of the `CategoryTheory.NatIso.ofComponents` in
`Deformation.Artin.nonempty_derivedTensorProduct_iso_tensorOverRing`, with the two objects of
the homotopy category replaced by cochain complexes. There the complexes appear as `X.as`,
and `CategoryTheory.Quotient.as` is a field of the quotient category rather than of
`HomotopyCategory`, so such a term is well-typed only once `HomotopyCategory` has been
unfolded; stating the square at cochain complexes instead, and naming every intermediate
object by a `let` with an explicit type, keeps each of the three squares and each
associativity step an identity between composites that are already spelled the same way. -/
private theorem qhComparison_naturality (M : DerivedCategory (ModuleCat.{u} A))
    (κ : DerivedCategory.Q.obj P ≅ M)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L) :
    (DerivedCategory.Qh ⋙
            (Functor.curry.obj (overRingData A).tensor).flip.obj M).map
          ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map f) ≫
        (((Functor.curry.obj (overRingData A).tensor).flip.obj M).mapIso
              ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app L) ≪≫
            tensorOverRingIsoOf P hP M κ L ≪≫
            ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (L ⊗ P)).symm).hom =
      (((Functor.curry.obj (overRingData A).tensor).flip.obj M).mapIso
            ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app K) ≪≫
          tensorOverRingIsoOf P hP M κ K ≪≫
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (K ⊗ P)).symm).hom ≫
        (Tright P ⋙ DerivedCategory.Qh).map
          ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map f) := by
  let T := (overRingData A).tensor
  let G := (Functor.curry.obj (overRingData A).tensor).flip.obj M
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  let R := HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  -- the three factors of the component at `K`
  let p : G.obj (R.obj K) ⟶ T.obj (DerivedCategory.Q.obj K, M) := G.map (e.hom.app K)
  let q : T.obj (DerivedCategory.Q.obj K, M) ⟶ DerivedCategory.Q.obj (K ⊗ P) :=
    (tensorOverRingIsoOf P hP M κ K).hom
  let r : DerivedCategory.Q.obj (K ⊗ P) ⟶ R.obj (K ⊗ P) := e.inv.app (K ⊗ P)
  -- the three factors of the component at `L`
  let p' : G.obj (R.obj L) ⟶ T.obj (DerivedCategory.Q.obj L, M) := G.map (e.hom.app L)
  let q' : T.obj (DerivedCategory.Q.obj L, M) ⟶ DerivedCategory.Q.obj (L ⊗ P) :=
    (tensorOverRingIsoOf P hP M κ L).hom
  let r' : DerivedCategory.Q.obj (L ⊗ P) ⟶ R.obj (L ⊗ P) := e.inv.app (L ⊗ P)
  -- the four vertical maps induced by `f`
  let m : G.obj (R.obj K) ⟶ G.obj (R.obj L) :=
    (DerivedCategory.Qh ⋙ G).map
      ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map f)
  let j : T.obj (DerivedCategory.Q.obj K, M) ⟶ T.obj (DerivedCategory.Q.obj L, M) :=
    G.map (DerivedCategory.Q.map f)
  let k : DerivedCategory.Q.obj (K ⊗ P) ⟶ DerivedCategory.Q.obj (L ⊗ P) :=
    DerivedCategory.Q.map (f ⊗ₘ 𝟙 P)
  let n : R.obj (K ⊗ P) ⟶ R.obj (L ⊗ P) :=
    (Tright P ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map f)
  -- the first square: the comparison of the two localizations, tensored with `M`
  have h1 := congrArg G.map
    (DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{u} A) f)
  rw [Functor.map_comp, Functor.map_comp] at h1
  have s1 : m ≫ p' = p ≫ j := h1
  -- the second square: the K-flat comparison at the representative `M`
  have s2 : j ≫ q' = q ≫ k := tensorOverRingIsoOf_naturality P hP M κ f
  -- the third square: the inverse comparison of the two localizations
  have s3 : k ≫ r' = r ≫ n :=
    DerivedCategory.quotientCompQhIso_inv_naturality (C := ModuleCat.{u} A) (f ⊗ₘ 𝟙 P)
  -- the pasting of the three squares
  change m ≫ p' ≫ q' ≫ r' = (p ≫ q ≫ r) ≫ n
  rw [reassoc_of% s1, reassoc_of% s2, s3]
  simp only [Category.assoc]

include hP in
/-- **The two derived tensor products with a K-flat-representable object agree.** Both
`CochainComplex.DerivedTensor.derivedTensorProduct` and the tensor product of the canonical
tensor--Hom adjunction over the ring become the ordinary total tensor product with `P` after
restriction along the localization functor of the homotopy category, so they are isomorphic
as endofunctors of `D(A)`. -/
public theorem nonempty_derivedTensorProduct_iso_tensorOverRing
    (M : DerivedCategory (ModuleCat.{u} A)) (κ : DerivedCategory.Q.obj P ≅ M) :
    Nonempty (derivedTensorProduct M ≅
      (Functor.curry.obj (overRingData A).tensor).flip.obj M) := by
  obtain ⟨α⟩ := (derivedTensorProduct_iso_lift_of_kFlat_resolution
      M P P (𝟙 P) hP
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P ≪≫ κ)).1
  have hβ : DerivedCategory.Qh ⋙
      (Functor.curry.obj (overRingData A).tensor).flip.obj M ≅
        Tright P ⋙ DerivedCategory.Qh := by
    refine NatIso.ofComponents (fun X =>
      ((Functor.curry.obj (overRingData A).tensor).flip.obj M).mapIso
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app X.as) ≪≫
        tensorOverRingIsoOf P hP M κ X.as ≪≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (X.as ⊗ P)).symm) ?_
    intro X Y g
    obtain ⟨f, rfl⟩ :=
      (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map_surjective g
    exact qhComparison_naturality P hP M κ f
  let : Localization.Lifting (DerivedCategory.Qh (C := ModuleCat.{u} A))
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (DerivedCategory.Qh ⋙ derivedTensorProduct M)
      (derivedTensorProduct M) := ⟨Iso.refl _⟩
  let : Localization.Lifting (DerivedCategory.Qh (C := ModuleCat.{u} A))
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (DerivedCategory.Qh ⋙
        (Functor.curry.obj (overRingData A).tensor).flip.obj M)
      ((Functor.curry.obj (overRingData A).tensor).flip.obj M) :=
    ⟨Iso.refl _⟩
  exact ⟨Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    (DerivedCategory.Qh ⋙ derivedTensorProduct M)
    (DerivedCategory.Qh ⋙
      (Functor.curry.obj (overRingData A).tensor).flip.obj M)
    (derivedTensorProduct M)
    ((Functor.curry.obj (overRingData A).tensor).flip.obj M)
    (α ≪≫ hβ.symm)⟩

end Descent

end Deformation.Artin

end
