module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentDataSheavesEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.TransportOrbit
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions

/-!
# Descent data and sheaves: the equivalence of categories

Let `{X i ⟶ T}` be a family of morphisms of algebraic spaces over `S`. A descent datum
`(V i, φ ij)` relative to the family is the same thing as a move operation on the family of
spaces `V i`, so the members may be glued: the *orbit* of that move operation is a presheaf
over `T` whose product with each `X i` is `V i`, and sheafifying it keeps those products
because they are already sheaves. The resulting sheaf over `T` therefore has the prescribed
descent datum, so the functor from sheaves over `T` to descent data is essentially
surjective. For an fppf covering that functor is also fully faithful, which is
`AlgebraicGeometry.Space.Descent.fibreDescentFunctorFullyFaithful`, so it is an **equivalence
of categories** — the assertion of Tag 0ADT. Under the equivalence the fibre product
`X i ×_T F` is the member `V i`, which is part (1), and the sheaf is an algebraic space
exactly when the descent datum is effective, which is part (2).

## Main definitions

* `AlgebraicGeometry.Space.Descent.fibreComponentIsoOfIsPullback` and
  `AlgebraicGeometry.Space.Descent.isoFibreDescentData` identify a descent datum with the
  descent datum of a sheaf over `T`, from a family of component pullback squares compatible
  with the move operation.
* `AlgebraicGeometry.Space.Descent.fppfDescentDataSheafEquivalence` is the equivalence of
  categories of Tag 0ADT.
* `AlgebraicGeometry.Space.Descent.descendedFibreComponentIso` and
  `AlgebraicGeometry.Space.Descent.descentInclusion` are the identification of the fibre
  product of the descended sheaf with a member of the covering, and the resulting map of a
  member into the descended sheaf.

## Main results

* `AlgebraicGeometry.Space.Descent.fibreDescentFunctor_essSurj`: the functor from sheaves over
  `T` whose fibre products with the family are algebraic spaces to descent data relative to
  the family is essentially surjective. No covering hypothesis is used: gluing and
  sheafification need only that the target and the members of the family are algebraic
  spaces.
* `AlgebraicGeometry.Space.Descent.isPullback_descentInclusion`: part (1) of the lemma, that
  the member `V i` of a descent datum is the fibre product of the sheaf it descends to with
  `X i`.
* `AlgebraicGeometry.Space.Descent.isAlgebraicSpace_inverse_iff_isEffective`: part (2) of the
  lemma read on the descent-datum side.

## Implementation notes

Hypotheses carried explicitly rather than derived. The gluing construction and essential
surjectivity assume that the target `T` and the members `X i` are algebraic spaces, which is
what the category of descent data requires anyway; `T` being an algebraic space is used
through its sheaf condition, to sheafify the glued presheaf over `T`, and the members through
theirs, to see that the fibre products survive sheafification. The statements naming the
equivalence assume only `AlgebraicGeometry.Space.IsFppfCovering`, Tag 03Y8, which is the
hypothesis of the source and which supplies the algebraicity of the target and of the members
itself.

The glued presheaf is `CategoryTheory.FamilyTransport.orbitOver` applied to the move operation
`AlgebraicGeometry.Space.Descent.DescentData.transport` of the descent datum, which is the
coequalizer of the two maps from the pairwise overlaps to the disjoint union of the members
that the source forms: its sections over a slice object are the points of the members modulo
the identification made by the gluing isomorphisms.
`CategoryTheory.FamilyTransport.orbitOverProductIsLimit` is the statement that `V i` is the
product of that presheaf with `X i` in the slice over `T`, i.e. their fibre product, and
`CategoryTheory.isPullback_sheafify` carries it through sheafification. The sheaf condition on
`V i` and on `X i` is what sheafification needs; without it the fibre product of the
sheafification would be larger.

Essential surjectivity produces the sheaf whose descent datum is *isomorphic* to the given
one, which is what essential surjectivity asks; it is not claimed that the fibre products of
the glued sheaf are equal to the members on the nose.

## References

* [Stacks Project, Tag 0ADT](https://stacks.math.columbia.edu/tag/0ADT)
* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
* [Stacks Project, Tag 0ADR](https://stacks.math.columbia.edu/tag/0ADR)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable (f : ∀ i, X i ⟶ T)

/-! ### Recognising the descent datum of a sheaf over the target -/

section Recognise

variable (hT : IsAlgebraicSpace B S hS T) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
    (D : DescentData f hT hX) (F : SheavesWithSpaceFibres f)
    (q : ∀ i, (D.obj i).left ⟶ F.obj.left)
    (hq : ∀ i, IsPullback (q i) (D.obj i).hom F.obj.hom (f i))

/-- A pullback square exhibiting the `i`-th member of a descent datum as the fibre product of
a sheaf over `T` with `X i` identifies that member with the `i`-th component of the descent
datum of the sheaf. -/
public def fibreComponentIsoOfIsPullback (i : ι) : D.obj i ≅ fibreComponent f F.obj i :=
  Over.isoMk (hq i).isoPullback (hq i).isoPullback_hom_snd

/-- The identification of components carries the projection to the sheaf to the given map. -/
@[simp]
public lemma fibreComponentIsoOfIsPullback_hom_left_fst (i : ι) :
    (fibreComponentIsoOfIsPullback f hT hX D F q hq i).hom.left ≫
      pullback.fst F.obj.hom (f i) = q i :=
  (hq i).isoPullback_hom_fst

/-- The identification of components carries the projection to `X i` to the structure map of
the member. -/
@[simp]
public lemma fibreComponentIsoOfIsPullback_hom_left_snd (i : ι) :
    (fibreComponentIsoOfIsPullback f hT hX D F q hq i).hom.left ≫
      pullback.snd F.obj.hom (f i) = (D.obj i).hom :=
  (hq i).isoPullback_hom_snd

/-- The identification of components commutes with the move operations, as soon as the given
maps to the sheaf do. -/
public lemma move_fibreComponentIsoOfIsPullback
    (hmove : ∀ {i j : ι} {Z : Over T} (v : Z ⟶ (Over.map (f i)).obj (D.obj i))
      (y : Z ⟶ Over.mk (f j)), v.left ≫ q i = (D.transport.move v y).left ≫ q j)
    {i j : ι} {Z : Over T} (v : Z ⟶ (Over.map (f i)).obj (D.obj i))
    (y : Z ⟶ Over.mk (f j)) :
    D.transport.move v y ≫
        (Over.map (f j)).map (fibreComponentIsoOfIsPullback f hT hX D F q hq j).hom =
      fibreMove f F.obj
        (v ≫ (Over.map (f i)).map
          (fibreComponentIsoOfIsPullback f hT hX D F q hq i).hom) y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.map_map_left, Category.assoc,
      fibreComponentIsoOfIsPullback_hom_left_fst, fibreMove_left_fst]
    exact (hmove v y).symm
  · simp only [Over.comp_left, Over.map_map_left, Category.assoc,
      fibreComponentIsoOfIsPullback_hom_left_snd, fibreMove_left_snd]
    exact congrArg Over.Hom.left (D.transport.move_base v y)

/-- The identification of components commutes with the gluing isomorphisms of the descent
datum and of the fibre products. -/
public lemma gluing_fibreComponentIsoOfIsPullback
    (hmove : ∀ {i j : ι} {Z : Over T} (v : Z ⟶ (Over.map (f i)).obj (D.obj i))
      (y : Z ⟶ Over.mk (f j)), v.left ≫ q i = (D.transport.move v y).left ≫ q j) (i j : ι) :
    prod.map ((Over.map (f i)).map
          (fibreComponentIsoOfIsPullback f hT hX D F q hq i).hom) (𝟙 (Over.mk (f j))) ≫
        ((fibreTransport f F.obj).gluing i j).hom.left =
      (D.gluing i j).hom.left ≫ prod.map (𝟙 (Over.mk (f i)))
        ((Over.map (f j)).map (fibreComponentIsoOfIsPullback f hT hX D F q hq j).hom) := by
  rw [← DescentData.transport_gluing D i j]
  exact FamilyTransport.gluing_comm D.transport (fibreTransport f F.obj)
    (fun k ↦ (Over.map (f k)).map (fibreComponentIsoOfIsPullback f hT hX D F q hq k).hom)
    (fun k ↦ structureMap_naturality (f k)
      (fibreComponentIsoOfIsPullback f hT hX D F q hq k).hom)
    (fun v y ↦ (move_fibreComponentIsoOfIsPullback f hT hX D F q hq hmove v y).trans
      (fibreTransport_move f F.obj _ y).symm) i j

/-- **A descent datum whose members are the fibre products of a sheaf over `T`, compatibly
with its move operation, is the descent datum of that sheaf.** -/
public def isoFibreDescentData
    (hmove : ∀ {i j : ι} {Z : Over T} (v : Z ⟶ (Over.map (f i)).obj (D.obj i))
      (y : Z ⟶ Over.mk (f j)), v.left ≫ q i = (D.transport.move v y).left ≫ q j) :
    D ≅ fibreDescentData f hT hX F :=
  DescentData.isoMk (fibreComponentIsoOfIsPullback f hT hX D F q hq)
    (gluing_fibreComponentIsoOfIsPullback f hT hX D F q hq hmove)

end Recognise

/-! ### Essential surjectivity: gluing a descent datum -/

section EssSurj

variable (hT : IsAlgebraicSpace B S hS T) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

/-- **Every descent datum is the descent datum of a sheaf over the target.** The members of a
descent datum are glued along its move operation and the result is sheafified; the fibre
products with the members of the family survive, because they are already sheaves. -/
public theorem fibreDescentFunctor_essSurj : (fibreDescentFunctor f hT hX).EssSurj := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  refine ⟨fun D ↦ ?_⟩
  let J := BigFppfOver.topology B S hS
  let q : ∀ i, (D.obj i).left ⟶ sheafify J D.transport.orbitOver.left :=
    fun i ↦ (D.transport.toOrbitOver i).left ≫ toSheafify J D.transport.orbitOver.left
  have hq : ∀ i, IsPullback (q i) (D.obj i).hom
      (sheafifyLift J D.transport.orbitOver.hom hT.isSheaf) (f i) := fun i ↦
    isPullback_sheafify J
      (Over.isPullback_of_binaryFan_isLimit _ (D.transport.orbitOverProductIsLimit i))
      (D.obj_isAlgebraicSpace i).isSheaf (hX i).isSheaf hT.isSheaf
  refine ⟨⟨Over.mk (sheafifyLift J D.transport.orbitOver.hom hT.isSheaf),
      ((presheafToSheaf J (Type u)).obj D.transport.orbitOver.left).property,
      fun i ↦ (D.obj_isAlgebraicSpace i).of_iso (hq i).isoPullback⟩, ⟨?_⟩⟩
  refine (isoFibreDescentData f hT hX D _ q hq (fun {i j Z} v y ↦ ?_)).symm
  simpa only [Over.comp_left, Category.assoc] using
    congrArg (· ≫ toSheafify J D.transport.orbitOver.left)
      (congrArg Over.Hom.left (D.transport.toOrbitOver_move v y))

end EssSurj

/-! ### The equivalence of categories -/

section Equivalence

variable (hcov : Space.IsFppfCovering B S hS X f)

/-- **Stacks 0ADT.** For an fppf covering of algebraic spaces `{X i ⟶ T}`, the sheaves on the
big fppf site endowed with a map to `T` whose fibre products `X i ×_T F` are all algebraic
spaces are equivalent to the descent data relative to the covering. The functor takes a sheaf
to the descent datum formed by those fibre products. -/
@[stacks 0ADT "THE EQUIVALENCE OF CATEGORIES, for an fppf covering of algebraic spaces: \
descent data relative to the covering are the sheaves over the target whose fibre products \
with the covering are algebraic spaces. Full faithfulness is \
fibreDescentFunctorFullyFaithful, essential surjectivity is fibreDescentFunctor_essSurj, \
which glues the members of the datum as the source's coequalizer and sheafifies"]
public def fppfDescentDataSheafEquivalence :
    SheavesWithSpaceFibres f ≌
      DescentData f hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace :=
  haveI : (fibreDescentFunctor f hcov.target_isAlgebraicSpace
      hcov.source_isAlgebraicSpace).IsEquivalence :=
    ⟨(fibreDescentFunctorFullyFaithful f hcov.target_isAlgebraicSpace
        hcov.source_isAlgebraicSpace hcov).faithful,
      (fibreDescentFunctorFullyFaithful f hcov.target_isAlgebraicSpace
        hcov.source_isAlgebraicSpace hcov).full,
      fibreDescentFunctor_essSurj f hcov.target_isAlgebraicSpace
        hcov.source_isAlgebraicSpace⟩
  (fibreDescentFunctor f hcov.target_isAlgebraicSpace
    hcov.source_isAlgebraicSpace).asEquivalence

/-- The equivalence of Tag 0ADT sends a sheaf over the target to the descent datum formed by
its fibre products with the members of the covering. -/
public lemma fppfDescentDataSheafEquivalence_functor :
    (fppfDescentDataSheafEquivalence f hcov).functor =
      fibreDescentFunctor f hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace :=
  rfl

variable (D : DescentData f hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace)

/-- **Stacks 0ADT, part (1).** Under the equivalence, the fibre product of the sheaf a descent
datum corresponds to with the `i`-th member of the covering is the `i`-th member of the
descent datum, as a space over that member of the covering. -/
@[stacks 0ADT "PART (1): the algebraic space X i ×_X F on the sheaf side of the equivalence is \
the member V i on the descent-datum side, as an object over X i"]
public def descendedFibreComponentIso (i : ι) :
    fibreComponent f ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj i ≅
      D.obj i where
  hom := ((fppfDescentDataSheafEquivalence f hcov).counitIso.app D).hom.hom i
  inv := ((fppfDescentDataSheafEquivalence f hcov).counitIso.app D).inv.hom i
  hom_inv_id := congrArg (fun φ ↦ φ.hom i)
    ((fppfDescentDataSheafEquivalence f hcov).counitIso.app D).hom_inv_id
  inv_hom_id := congrArg (fun φ ↦ φ.hom i)
    ((fppfDescentDataSheafEquivalence f hcov).counitIso.app D).inv_hom_id

/-- The canonical map from the `i`-th member of a descent datum into the sheaf it descends
to. -/
public def descentInclusion (i : ι) :
    (D.obj i).left ⟶ ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.left :=
  (descendedFibreComponentIso f hcov D i).inv.left ≫
    pullback.fst ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.hom (f i)

/-- **Stacks 0ADT, part (1)** in pullback form: the `i`-th member of a descent datum, with its
structure map to `X i` and its canonical map to the sheaf the datum descends to, is the fibre
product of that sheaf with `X i`. -/
@[stacks 0ADT "PART (1) in pullback form: V i, with its structure map to X i and its canonical \
map into the descended sheaf F, is the fibre product X i ×_X F"]
public theorem isPullback_descentInclusion (i : ι) :
    IsPullback (descentInclusion f hcov D i) (D.obj i).hom
      ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.hom (f i) := by
  refine (IsPullback.of_hasPullback
    ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.hom (f i)).of_iso'
      ((Over.forget (X i)).mapIso (descendedFibreComponentIso f hcov D i).symm)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [descentInclusion]
  · simpa using Over.w (descendedFibreComponentIso f hcov D i).inv
  · simp
  · simp

/-- **Stacks 0ADT, part (2)** read on the descent-datum side: the sheaf a descent datum
descends to is an algebraic space exactly when the descent datum is effective. -/
@[stacks 0ADT "PART (2) on the descent-datum side: the sheaf F corresponding to a descent \
datum is an algebraic space if and only if that datum is effective"]
public theorem isAlgebraicSpace_inverse_iff_isEffective :
    IsAlgebraicSpace B S hS
        ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.left ↔
      DescentData.IsEffective D := by
  rw [isAlgebraicSpace_iff_isEffective_fibreDescentData f hcov.target_isAlgebraicSpace
    hcov.source_isAlgebraicSpace hcov]
  exact ⟨fun h ↦ Functor.essImage.ofIso
      ((fppfDescentDataSheafEquivalence f hcov).counitIso.app D) h,
    fun h ↦ Functor.essImage.ofIso
      ((fppfDescentDataSheafEquivalence f hcov).counitIso.app D).symm h⟩

end Equivalence

end AlgebraicGeometry.Space.Descent

end
