module

public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorMate

/-!
# The pentagon of the lax monoidal structure map of restriction of scalars

`CochainComplex.ExtendScalars.restrictScalarsLaxTensor` is the lax monoidal structure map

`ρ : X|_R ⊗_R Y|_R ⟶ (X ⊗_S Y)|_R`

of restriction of scalars on cochain complexes, built in
`StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoRestrictedEvaluation` as the transpose
of the inverse of the strong monoidality isomorphism
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` of extension of scalars.  Of the three
laws a lax monoidal structure map has to satisfy, only naturality was proved there --
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor_naturality` -- and
`StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorMate` added the compatibility with
the strong structure of the left adjoint, which needs no law of `ρ` at all.

This file proves the **associativity constraint**, the Eilenberg--Kelly pentagon of `ρ`:

`(ρ_{X,Y} ⊗ 𝟙) ≫ ρ_{X ⊗ Y, Z} ≫ (α_{X,Y,Z})|_R`
  `= α_{X|_R, Y|_R, Z|_R} ≫ (𝟙 ⊗ ρ_{Y,Z}) ≫ ρ_{X, Y ⊗ Z}`.

This is the law the remaining residue of the chapter asks for.  The module documentation of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaEvaluation` records that what is
left of the second input of [stacks 0E2H] is one coherence, equally expressible as the
associativity of `Dualizing.derivedTensorBaseChange`, as the associativity of the canonical
projection morphism, or as the compatibility of [stacks 0E1W] with the currying isomorphism of
[stacks 0A65] -- the three being identified by
`Dualizing.derivedTensorBaseChangeAssoc_iff_curryCompat` and
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorAssoc_iff_homMateCurryCompat`.  Since
`StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoRestrictedEvaluation` puts the model
comparison of [stacks 0E1W] into the vocabulary of `ρ`, the chain-level pentagon of `ρ` is the
chain-level form of that coherence.

**The content is entirely the pentagon of the strong structure.**  Transposing the two sides of
the pentagon of `ρ` across the extension--restriction adjunction turns each into a morphism out
of the extension of `(X|_R ⊗ Y|_R) ⊗ Z|_R`, and there the three counits detach: both sides become
the inverse monoidality comparison in the two bracketings, followed by the tensor of the three
counits.  What relates those is the pentagon of
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` read in the `inv` direction,
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso_associativity_inv`, together with
naturality of the associator of the target category.  No property of the counit
beyond naturality of the adjunction isomorphism is used, and the unit never appears.

As in the two files above, the abstract content is isolated over variable monoidal categories with
the family of monoidality isomorphisms, its two-variable inverse naturality and its inverse
pentagon taken as **data**, so that no `CategoryTheory.Functor.Monoidal` instance is required --
`extendScalarsMonoidalIso` carries none.
`CategoryTheory.Adjunction.laxTensorOfMonoidalIso` names the induced lax structure map in that
generality, and `CochainComplex.ExtendScalars.restrictScalarsLaxTensor_eq_laxTensorOfMonoidalIso`
identifies it with `ρ`.

**What is not done here.**  No tag is registered and no caveat is lifted.  The two hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` are both still open: this is a
chain-level coherence that the identification `μ' = μ` of its `hmu` consumes, and it says nothing
whatever about its comparison identity `h`, whose frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  The unit constraints of `ρ` -- its left
and right unitor laws -- are still unproved; they are not needed by anything in the chapter so
far.  Nor is the pentagon transported to the derived category here.

## Main definitions

* `CategoryTheory.Adjunction.laxTensorOfMonoidalIso` -- the lax monoidal structure map a right
  adjoint inherits from a monoidality isomorphism of its left adjoint, over variable monoidal
  categories.

## Main results

* `CategoryTheory.Adjunction.map_laxTensorOfMonoidalIso_comp_counit` -- the defining property:
  the inherited structure map transposes back to the inverse comparison followed by the tensor of
  the two counits.
* `CategoryTheory.Adjunction.laxTensorOfMonoidalIso_associativity` -- **the abstract pentagon.**
  Out of nothing but the inverse naturality square of the comparison, its inverse pentagon and
  naturality of the associator.
* `CochainComplex.ExtendScalars.extendScalarsMonoidalIso_inv_pentagon` -- the inverse pentagon of
  `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` with both whiskerings written as
  tensors with an identity and both associators in the `hom` direction, which is the shape the
  abstract pentagon asks for.
* `CochainComplex.ExtendScalars.restrictScalarsLaxTensor_associativity` -- **the pentagon of
  `ρ`**, the instance of the abstract pentagon at
  `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars

universe u

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {L : C ⥤ D} {U : D ⥤ C}

/-- **The lax monoidal structure map a right adjoint inherits from a monoidality isomorphism of
its left adjoint.**  Given `L ⊣ U` and a family of isomorphisms `m K M : L K ⊗ L M ≅ L (K ⊗ M)`,
the transpose of

`L (U X ⊗ U Y) --(m (U X) (U Y))⁻¹--> L U X ⊗ L U Y --ε ⊗ ε--> X ⊗ Y`.

No coherence of `m` is required to form it. `CochainComplex.ExtendScalars.restrictScalarsLaxTensor`
is this at `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, by
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor_eq_laxTensorOfMonoidalIso`. -/
def laxTensorOfMonoidalIso (adj : L ⊣ U)
    (m : ∀ K M : C, L.obj K ⊗ L.obj M ≅ L.obj (K ⊗ M)) (X Y : D) :
    U.obj X ⊗ U.obj Y ⟶ U.obj (X ⊗ Y) :=
  adj.homEquiv (U.obj X ⊗ U.obj Y) (X ⊗ Y)
    ((m (U.obj X) (U.obj Y)).inv ≫ (adj.counit.app X ⊗ₘ adj.counit.app Y))

/-- **The defining property of the inherited lax structure map**: transposing it back across the
adjunction gives the inverse monoidality comparison followed by the tensor of the two counits. -/
theorem map_laxTensorOfMonoidalIso_comp_counit (adj : L ⊣ U)
    (m : ∀ K M : C, L.obj K ⊗ L.obj M ≅ L.obj (K ⊗ M)) (X Y : D) :
    L.map (adj.laxTensorOfMonoidalIso m X Y) ≫ adj.counit.app (X ⊗ Y) =
      (m (U.obj X) (U.obj Y)).inv ≫ (adj.counit.app X ⊗ₘ adj.counit.app Y) :=
  (adj.homEquiv (U.obj X ⊗ U.obj Y) (X ⊗ Y)).symm_apply_apply _

/-- **The pentagon of the inherited lax monoidal structure map.**

If the family `m` of monoidality isomorphisms of the left adjoint is natural in both variables in
the `inv` direction (`hnat`) and satisfies the pentagon in the `inv` direction (`hpent`), then the
lax structure map `CategoryTheory.Adjunction.laxTensorOfMonoidalIso` it induces on the right
adjoint satisfies the Eilenberg--Kelly associativity law.

This is the standard fact that a strong monoidal left adjoint transposes into a lax monoidal right
adjoint, in the one law that is not formal.  The proof transposes both sides across the
adjunction: by naturality of the adjunction isomorphism in both its variables each becomes a
transpose, and by `CategoryTheory.Adjunction.map_laxTensorOfMonoidalIso_comp_counit` the inner
occurrences of the structure map become inverse comparisons.  What is left is `hpent` conjugated
by naturality of the associator of the target category.

The comparison is taken as data, not as a `CategoryTheory.Functor.Monoidal` instance, because
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` carries no such instance. -/
theorem laxTensorOfMonoidalIso_associativity (adj : L ⊣ U)
    (m : ∀ K M : C, L.obj K ⊗ L.obj M ≅ L.obj (K ⊗ M))
    (hnat : ∀ {K K' M M' : C} (a : K ⟶ K') (b : M ⟶ M'),
      L.map (a ⊗ₘ b) ≫ (m K' M').inv = (m K M).inv ≫ (L.map a ⊗ₘ L.map b))
    (hpent : ∀ K M N : C,
      (m (K ⊗ M) N).inv ≫ ((m K M).inv ⊗ₘ 𝟙 (L.obj N)) ≫
          (α_ (L.obj K) (L.obj M) (L.obj N)).hom =
        L.map (α_ K M N).hom ≫ (m K (M ⊗ N)).inv ≫ (𝟙 (L.obj K) ⊗ₘ (m M N).inv))
    (X Y Z : D) :
    (adj.laxTensorOfMonoidalIso m X Y ⊗ₘ 𝟙 (U.obj Z)) ≫
        adj.laxTensorOfMonoidalIso m (X ⊗ Y) Z ≫ U.map (α_ X Y Z).hom =
      (α_ (U.obj X) (U.obj Y) (U.obj Z)).hom ≫
        (𝟙 (U.obj X) ⊗ₘ adj.laxTensorOfMonoidalIso m Y Z) ≫
          adj.laxTensorOfMonoidalIso m X (Y ⊗ Z) := by
  have hXY := adj.map_laxTensorOfMonoidalIso_comp_counit m X Y
  have hYZ := adj.map_laxTensorOfMonoidalIso_comp_counit m Y Z
  have h1 : (L.map (adj.laxTensorOfMonoidalIso m X Y) ⊗ₘ L.map (𝟙 (U.obj Z))) ≫
        (adj.counit.app (X ⊗ Y) ⊗ₘ adj.counit.app Z) =
      ((m (U.obj X) (U.obj Y)).inv ⊗ₘ 𝟙 (L.obj (U.obj Z))) ≫
        ((adj.counit.app X ⊗ₘ adj.counit.app Y) ⊗ₘ adj.counit.app Z) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hXY, Functor.map_id]
  have h2 : (L.map (𝟙 (U.obj X)) ⊗ₘ L.map (adj.laxTensorOfMonoidalIso m Y Z)) ≫
        (adj.counit.app X ⊗ₘ adj.counit.app (Y ⊗ Z)) =
      (𝟙 (L.obj (U.obj X)) ⊗ₘ (m (U.obj Y) (U.obj Z)).inv) ≫
        (adj.counit.app X ⊗ₘ (adj.counit.app Y ⊗ₘ adj.counit.app Z)) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hYZ, Functor.map_id]
  have hstar : L.map (adj.laxTensorOfMonoidalIso m X Y ⊗ₘ 𝟙 (U.obj Z)) ≫
        ((m (U.obj (X ⊗ Y)) (U.obj Z)).inv ≫
          (adj.counit.app (X ⊗ Y) ⊗ₘ adj.counit.app Z)) ≫ (α_ X Y Z).hom =
      L.map (α_ (U.obj X) (U.obj Y) (U.obj Z)).hom ≫
        L.map (𝟙 (U.obj X) ⊗ₘ adj.laxTensorOfMonoidalIso m Y Z) ≫
          ((m (U.obj X) (U.obj (Y ⊗ Z))).inv ≫
            (adj.counit.app X ⊗ₘ adj.counit.app (Y ⊗ Z))) := by
    have hα : ((adj.counit.app X ⊗ₘ adj.counit.app Y) ⊗ₘ adj.counit.app Z) ≫
          (α_ X Y Z).hom =
        (α_ (L.obj (U.obj X)) (L.obj (U.obj Y)) (L.obj (U.obj Z))).hom ≫
          (adj.counit.app X ⊗ₘ (adj.counit.app Y ⊗ₘ adj.counit.app Z)) :=
      associator_naturality _ _ _
    simp only [Category.assoc]
    rw [reassoc_of% (hnat (adj.laxTensorOfMonoidalIso m X Y) (𝟙 (U.obj Z))),
      reassoc_of% h1, hα,
      reassoc_of% (hpent (U.obj X) (U.obj Y) (U.obj Z)),
      reassoc_of% (hnat (𝟙 (U.obj X)) (adj.laxTensorOfMonoidalIso m Y Z)), h2]
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, counit_naturality]
  rw [reassoc_of% (adj.map_laxTensorOfMonoidalIso_comp_counit m (X ⊗ Y) Z),
    adj.map_laxTensorOfMonoidalIso_comp_counit m X (Y ⊗ Z)]
  simpa only [Category.assoc] using hstar

end CategoryTheory.Adjunction

namespace CochainComplex.ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Extension of scalars `ModuleCat.extendScalars f` is an additive functor. -/
local instance extendScalarsAdditiveLaxTensorAssoc :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **The inverse pentagon of the monoidality comparison, in tensor-with-identity form.**
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso_associativity_inv` with the two whiskerings
written as tensors with an identity and both associators moved to the `hom` direction, which is
the shape `CategoryTheory.Adjunction.laxTensorOfMonoidalIso_associativity` asks its pentagon
hypothesis in.  Every factor of the inverse pentagon is an isomorphism, so the two shapes are
equivalent. -/
public theorem extendScalarsMonoidalIso_inv_pentagon
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extendScalarsMonoidalIso f (K ⊗ L) M).inv ≫
        ((extendScalarsMonoidalIso f K L).inv ⊗ₘ 𝟙 ((mapCochainComplex f).obj M)) ≫
          (α_ ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj L)
            ((mapCochainComplex f).obj M)).hom =
      (mapCochainComplex f).map (α_ K L M).hom ≫
        (extendScalarsMonoidalIso f K (L ⊗ M)).inv ≫
          (𝟙 ((mapCochainComplex f).obj K) ⊗ₘ (extendScalarsMonoidalIso f L M).inv) := by
  have key : (extendScalarsMonoidalIso f (K ⊗ L) M).inv ≫
        ((extendScalarsMonoidalIso f K L).inv ▷ (mapCochainComplex f).obj M) =
      (mapCochainComplex f).map (α_ K L M).hom ≫
        (extendScalarsMonoidalIso f K (L ⊗ M)).inv ≫
          ((mapCochainComplex f).obj K ◁ (extendScalarsMonoidalIso f L M).inv) ≫
            (α_ ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj L)
              ((mapCochainComplex f).obj M)).inv := by
    rw [extendScalarsMonoidalIso_associativity_inv, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [tensorHom_id, id_tensorHom, ← Category.assoc, key, Category.assoc, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The lax monoidal structure map of restriction of scalars is the abstract one.**
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor` is
`CategoryTheory.Adjunction.laxTensorOfMonoidalIso` of the degreewise extension--restriction
adjunction at the family `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`; the two are the
same transpose, written once concretely and once generically. -/
public theorem restrictScalarsLaxTensor_eq_laxTensorOfMonoidalIso
    (X Y : CochainComplex (ModuleCat.{u} S) ℤ) :
    restrictScalarsLaxTensor f X Y =
      (extendRestrictScalarsComplexAdj f).laxTensorOfMonoidalIso
        (extendScalarsMonoidalIso f) X Y :=
  rfl

/-- **The pentagon of the lax monoidal structure map of restriction of scalars.**

`CochainComplex.ExtendScalars.restrictScalarsLaxTensor` satisfies the Eilenberg--Kelly
associativity law: comparing the first two factors and then the result with the third agrees,
across the two associators, with comparing the last two factors and then the first with the
result.

Together with `CochainComplex.ExtendScalars.restrictScalarsLaxTensor_naturality` this is all of
the lax monoidal structure of restriction of scalars except the two unit constraints.  It is
`CategoryTheory.Adjunction.laxTensorOfMonoidalIso_associativity` at the two-variable inverse
naturality square `CochainComplex.ExtendScalars.extendScalarsMonoidalIso_inv_naturality` and the
inverse pentagon `CochainComplex.ExtendScalars.extendScalarsMonoidalIso_inv_pentagon`; all of the
content is the chain-level pentagon
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso_associativity`. -/
public theorem restrictScalarsLaxTensor_associativity
    (X Y Z : CochainComplex (ModuleCat.{u} S) ℤ) :
    (restrictScalarsLaxTensor f X Y ⊗ₘ
          𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z)) ≫
        restrictScalarsLaxTensor f (X ⊗ Y) Z ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map (α_ X Y Z).hom =
      (α_ ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X)
            ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Y)
            ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z)).hom ≫
        (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X) ⊗ₘ
            restrictScalarsLaxTensor f Y Z) ≫
          restrictScalarsLaxTensor f X (Y ⊗ Z) :=
  Adjunction.laxTensorOfMonoidalIso_associativity (extendRestrictScalarsComplexAdj f)
    (extendScalarsMonoidalIso f)
    (fun a b => extendScalarsMonoidalIso_inv_naturality f a b)
    (extendScalarsMonoidalIso_inv_pentagon f) X Y Z

end CochainComplex.ExtendScalars

end
