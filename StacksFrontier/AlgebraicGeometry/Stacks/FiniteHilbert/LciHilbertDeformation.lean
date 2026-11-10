module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMapFromRepresentingSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciHilbertFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusExists
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusRepresentable
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Transport
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointOfObject

/-!
# The first-order lifting problem of the local complete intersection locus over the target

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
which is representable by algebraic spaces, flat and locally of finite presentation, and let `d`
be a natural number. The first-order lifting problem for
`p : ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` asks: given a quintuple `(U, Z, y, x, α)` of the locus over an affine
`U`, a first-order thickening `U ⊂ U'` of affine objects of the site and an object `y'` of `𝒴`
over `U'` restricting to `y`, produce a quintuple over `U'` whose cover restricts to `Z` and
whose object of `𝒴` is `y'`.

This file solves that problem from a solution of the deformation problem of **Stacks 06D8** for
the cover, and concludes that `p` is formally smooth on objects.

## Main definitions

* `FiniteHilbert.restrictUnit`: the identification of the value at the base of the quintuple of a
  scheme-valued point of `𝒴` over `U'` with the object `y` of the quintuple.
* `FiniteHilbert.restrictData`: **the identification `X_y = U ×_{U'} X'_{y'}`**, in the form of
  data exhibiting the relative map of the quintuple whose algebraic space is the restriction along
  `U ⟶ U'` of an algebraic space representing the 2-fibre product over `U'`.
* `FiniteHilbert.HasCoverDeformations`: the deformation problem of Stacks 06D8 for a degree-`d`
  finite locally free cover mapping to the special fibre of a flat algebraic space.

## Main results

* `FiniteHilbert.restrictData_y` and `FiniteHilbert.restrictData_Xy`: the point and the algebraic
  space of that data are the restrictions along `U ⟶ U'` of the given ones.
* `FiniteHilbert.isUnramified_and_isLocalCompleteIntersection_restrictData_map`: the relative map
  of a quintuple of the locus into the restriction of an algebraic space representing the 2-fibre
  product over `U'` is unramified and a local complete intersection morphism.
* `FiniteHilbert.exists_object_hom_of_coverDeformation`: **the first-order lifting problem of
  Stacks 06D9 at one quintuple**, solved from a deformation of the cover.
* `isFormallySmoothOnObjects_lciFiniteHilbertToTarget_of_coverDeformations`:
  `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is formally smooth on objects.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 06D9](https://stacks.math.columbia.edu/tag/06D9)
-/

@[expose] public section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

namespace FiniteHilbert

/-! ### The restriction of a point of the target along a morphism of the base -/

section Restrict

variable (P : Object B S hS 𝒳 𝒴 F d) {U' : BigFppfOver B S hS} (i : P.U ⟶ U')
  (w : BigFppfOver B U'.left.1 U'.left.2 ⥤ 𝒴.toBasedCategory.obj)

/-- Two morphisms of a slice with the same underlying morphism agree up to `eqToHom`-conjugation
by equalities of the objects. -/
private theorem over_hom_eq_conj_of_heq {C : Type*} [Category C] {X : C} {b b' c c' : Over X}
    (hb : b = c) (hb' : b' = c') (φ : b ⟶ b') (ψ : c ⟶ c') (h : HEq φ.left ψ.left) :
    φ = eqToHom hb ≫ ψ ≫ eqToHom hb'.symm := by
  subst hb hb'
  simpa using Over.OverMorphism.ext (eq_of_heq h)

/-- The structure morphism of the base of the quintuple, read in the big fppf site of `U'`, is
the given morphism of the site. -/
theorem structHom_restrictBaseOver :
    eqToHom (Object.overMap_restrictBaseOver P i) ≫ i ≫ eqToHom (rfl : U' = U').symm =
      Functor.structHom U' ((Over.map i.left).obj P.baseOver) :=
  (over_hom_eq_conj_of_heq (Object.overMap_restrictBaseOver P i) (rfl : U' = U') _ i
    (heq_of_eq (Category.id_comp i.left))).symm

/-- The value of a point of `𝒴` over `U'` at the structure map of an object `V`, followed by a
vertical morphism, lies over the structure morphism of `V`. -/
private theorem isHomLift_map_toMkId_comp
    (hw : w ⋙ 𝒴.toBasedCategory.p = Over.map U'.hom) {z' : 𝒴.toBasedCategory.obj}
    (c : w.obj (Over.mk (𝟙 U'.left)) ⟶ z') (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 U') c)
    (V : BigFppfOver B U'.left.1 U'.left.2) :
    𝒴.toBasedCategory.p.IsHomLift (Functor.structHom U' V) (w.map (Functor.toMkId U' V) ≫ c) :=
  have := Functor.isHomLift_map_toMkId 𝒴.toBasedCategory.p U' w hw V
  have := hc
  IsHomLift.comp_lift_id_right' 𝒴.toBasedCategory.p (Functor.structHom U' V)
    (w.map (Functor.toMkId U' V)) U' c

/-- **The restriction of a point of `𝒴` over `U'` to the base of the quintuple, followed by the
identification of its value at the terminal object with `y'`, lies over the given morphism of the
site.** -/
theorem isHomLift_restrictPointToBase
    (hw : w ⋙ 𝒴.toBasedCategory.p = Over.map U'.hom) {z' : 𝒴.toBasedCategory.obj}
    (c : w.obj (Over.mk (𝟙 U'.left)) ⟶ z')
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 U') c) :
    𝒴.toBasedCategory.p.IsHomLift i
      (w.map (Functor.toMkId U' ((Over.map i.left).obj P.baseOver)) ≫ c) :=
  Functor.isHomLift_of_base_eq _ _
    (isHomLift_map_toMkId_comp w hw c hc ((Over.map i.left).obj P.baseOver)) i
    (Object.overMap_restrictBaseOver P i) rfl (structHom_restrictBaseOver P i)

/-- The given morphism of `𝒴` over the morphism of the site is strongly cartesian, `𝒴` being
fibred in groupoids. -/
theorem isStronglyCartesian_hom {z' : 𝒴.toBasedCategory.obj} (a : P.y ⟶ z')
    (ha : 𝒴.toBasedCategory.p.IsHomLift i a) :
    𝒴.toBasedCategory.p.IsStronglyCartesian i a :=
  have := ha
  𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift i a

/-- **The identification of the value at the base of the quintuple of a point of `𝒴` over `U'`
with the object `y` of the quintuple.** It is the unique vertical morphism whose composite with
the given morphism `a : y ⟶ y'` is the restriction of the point to the base of the quintuple
followed by the identification of its value at the terminal object with `y'`. -/
noncomputable def restrictUnit (hw : w ⋙ 𝒴.toBasedCategory.p = Over.map U'.hom)
    {z' : 𝒴.toBasedCategory.obj} (c : w.obj (Over.mk (𝟙 U'.left)) ⟶ z')
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 U') c) (a : P.y ⟶ z')
    (ha : 𝒴.toBasedCategory.p.IsHomLift i a) :
    (Over.map i.left ⋙ w).obj P.baseOver ⟶ P.y :=
  have := isStronglyCartesian_hom P i a ha
  have := isHomLift_restrictPointToBase P i w hw c hc
  Functor.IsStronglyCartesian.map 𝒴.toBasedCategory.p i a (Category.id_comp i).symm
    (w.map (Functor.toMkId U' ((Over.map i.left).obj P.baseOver)) ≫ c)

/-- The identification of the value at the base is vertical. -/
theorem isHomLift_restrictUnit (hw : w ⋙ 𝒴.toBasedCategory.p = Over.map U'.hom)
    {z' : 𝒴.toBasedCategory.obj} (c : w.obj (Over.mk (𝟙 U'.left)) ⟶ z')
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 U') c) (a : P.y ⟶ z')
    (ha : 𝒴.toBasedCategory.p.IsHomLift i a) :
    𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) (restrictUnit P i w hw c hc a ha) :=
  have := isStronglyCartesian_hom P i a ha
  have := isHomLift_restrictPointToBase P i w hw c hc
  Functor.IsStronglyCartesian.map_isHomLift 𝒴.toBasedCategory.p i a (Category.id_comp i).symm
    (w.map (Functor.toMkId U' ((Over.map i.left).obj P.baseOver)) ≫ c)

/-- **The defining factorization of the identification of the value at the base.** -/
theorem restrictUnit_comp (hw : w ⋙ 𝒴.toBasedCategory.p = Over.map U'.hom)
    {z' : 𝒴.toBasedCategory.obj} (c : w.obj (Over.mk (𝟙 U'.left)) ⟶ z')
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 U') c) (a : P.y ⟶ z')
    (ha : 𝒴.toBasedCategory.p.IsHomLift i a) :
    restrictUnit P i w hw c hc a ha ≫ a =
      w.map (Functor.toMkId U' ((Over.map i.left).obj P.baseOver)) ≫ c :=
  have := isStronglyCartesian_hom P i a ha
  have := isHomLift_restrictPointToBase P i w hw c hc
  Functor.IsStronglyCartesian.fac 𝒴.toBasedCategory.p i a (Category.id_comp i).symm
    (w.map (Functor.toMkId U' ((Over.map i.left).obj P.baseOver)) ≫ c)

/-! ### The identification of the two algebraic spaces -/

/-- **The identification `X_y = U ×_{U'} X'_{y'}`**, in the form of data exhibiting the relative
map of the quintuple: the scheme-valued point is the restriction along `i` of the given point of
`𝒴` over `U'`, and the algebraic space is the restriction along `i` of the given algebraic space
representing the 2-fibre product over `U'`, which represents the restricted 2-fibre product by
`AlgebraicGeometry.Stack.relativeSpaceRestrictEquivalence`. -/
noncomputable def restrictData (hw : w ⋙ 𝒴.toBasedCategory.p = Over.map U'.hom)
    {z' : 𝒴.toBasedCategory.obj} (c : w.obj (Over.mk (𝟙 U'.left)) ⟶ z')
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 U') c) (a : P.y ⟶ z')
    (ha : 𝒴.toBasedCategory.p.IsHomLift i a)
    {Xw : (BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u}
    (hXw : IsAlgebraicSpace B U'.left.1 U'.left.2 Xw)
    (ew : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p w
        F.toFunctor)
      (presheafOfCategories (Xw ⋙ typeToCat)).p) :
    RelativeMapData P :=
  RelativeMapData.ofPoint P (Over.map i.left ⋙ w) (restrictPoint_comp i hw)
    (restrictUnit P i w hw c hc a ha) (isHomLift_restrictUnit P i w hw c hc a ha)
    ((OverShriek.relocalizeRestrict i.left).obj Xw)
    (isAlgebraicSpace_relocalizeRestrict B P.U.left.1 U'.left.1 P.U.left.2 U'.left.2 i.left Xw
      hXw)
    (relativeSpaceRestrictEquivalence F w ew i.left (Over.w i)
      𝒳.isStackInGroupoids.isFiberedInGroupoids 𝒴.isStackInGroupoids.isFiberedInGroupoids hw)

section Data

variable (hw : w ⋙ 𝒴.toBasedCategory.p = Over.map U'.hom) {z' : 𝒴.toBasedCategory.obj}
  (c : w.obj (Over.mk (𝟙 U'.left)) ⟶ z') (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 U') c)
  (a : P.y ⟶ z') (ha : 𝒴.toBasedCategory.p.IsHomLift i a)
  {Xw : (BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u}
  (hXw : IsAlgebraicSpace B U'.left.1 U'.left.2 Xw)
  (ew : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p w
      F.toFunctor)
    (presheafOfCategories (Xw ⋙ typeToCat)).p)

/-- The scheme-valued point of the restricted data is the restriction of the given point. -/
theorem restrictData_y :
    (restrictData P i w hw c hc a ha hXw ew).y = Over.map i.left ⋙ w := rfl

/-- The algebraic space of the restricted data is the restriction of the given one. -/
theorem restrictData_Xy :
    (restrictData P i w hw c hc a ha hXw ew).Xy =
      (OverShriek.relocalizeRestrict i.left).obj Xw := rfl

/-- **The relative map of a quintuple of the local complete intersection locus into the
restriction of an algebraic space representing the 2-fibre product over `U'` is unramified and a
local complete intersection morphism.** -/
theorem isUnramified_and_isLocalCompleteIntersection_restrictData_map
    (hP : lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) P) :
    Space.IsUnramified B P.U.left.1 P.U.left.2
        (restrictData P i w hw c hc a ha hXw ew).map.hom ∧
      Space.IsLocalCompleteIntersection B P.U.left.1 P.U.left.2
        (restrictData P i w hw c hc a ha hXw ew).map.hom :=
  hP _

end Data

end Restrict

/-! ### The deformation problem of the cover -/

/-- **The deformation problem of Stacks 06D8 for algebraic spaces.** The data is a first-order
thickening `U ⊂ U'` of affine objects of the big fppf site of `S`, an algebraic space `X'` over
`U'` which is flat and locally of finite presentation, a degree-`d` finite locally free cover
`q : Z ⟶ U`, and a morphism `f` of algebraic spaces over `U` from `Z` to the special fibre
`U ×_{U'} X'` which is unramified and a local complete intersection morphism. The problem is to
produce a degree-`d` finite locally free cover `q' : Z' ⟶ U'` presenting `Z` as `U ×_{U'} Z'`,
together with a morphism `Z' ⟶ X'` of algebraic spaces over `U'` whose restriction along
`U ⟶ U'` is `f`.

The special fibre is the restriction of presheaves `CategoryTheory.OverShriek.relocalizeRestrict`,
and the restriction of the produced morphism is read through the comparison
`CategoryTheory.OverShriek.restrictYonedaHom` of the representable presheaf of `Z` with the
restriction of the representable presheaf of `Z'`, which the cartesian square makes an
isomorphism. -/
def HasCoverDeformations (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ) :
    Prop :=
  ∀ (U U' : BigFppfOver B S hS) (i : U ⟶ U'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj U') →
    Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
    ∀ (X' : (BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B U'.left.1 U'.left.2 X' →
      Space.IsFlat B U'.left.1 U'.left.2 (Space.toYonedaId B U'.left.1 U'.left.2 X') →
      Space.IsLocallyOfFinitePresentation B U'.left.1 U'.left.2
        (Space.toYonedaId B U'.left.1 U'.left.2 X') →
      ∀ (Z : BigFppfOver B S hS) (q : Z ⟶ U),
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) d →
        ∀ f : yoneda.obj (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶
            (OverShriek.relocalizeRestrict i.left).obj X',
          Space.IsUnramified B U.left.1 U.left.2 f →
          Space.IsLocalCompleteIntersection B U.left.1 U.left.2 f →
          ∃ (Z' : BigFppfOver B S hS) (q' : Z' ⟶ U') (g : Z ⟶ Z')
            (hg : IsPullback g q q' i),
            Stacks.Morphisms.IsFiniteLocallyFreeOfRank
                ((BigFppfOver.toScheme B S hS).map q') d ∧
              ∃ f' : yoneda.obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) ⟶ X',
                OverShriek.restrictYonedaHom i.left (coverComparisonOfSquare hg.w) ≫
                  (OverShriek.relocalizeRestrict i.left).map f' = f

/-! ### The quintuple produced over the thickening -/

section Lift

variable (P : Object B S hS 𝒳 𝒴 F d) {U' : BigFppfOver B S hS} (i : P.U ⟶ U')
  (w : BigFppfOver B U'.left.1 U'.left.2 ⥤ 𝒴.toBasedCategory.obj)

/-- **The first-order lifting problem of Stacks 06D9 at one quintuple.** Given a quintuple
`(U, Z, y, x, α)`, a morphism `i : U ⟶ U'` of the site, a scheme-valued point `y'` of `𝒴` over
`U'` whose value at the terminal object maps to an object `z'` of `𝒴` over `U'`, a morphism
`a : y ⟶ z'` over `i`, an algebraic space `X'_{y'}` over `U'` representing
`(Sch/U')_{fppf} ×_{y', 𝒴, F} 𝒳`, a degree-`d` finite locally free cover `q' : Z' ⟶ U'`
presenting `Z` as `U ×_{U'} Z'`, and a morphism `Z' ⟶ X'_{y'}` of algebraic spaces over `U'`
restricting to the relative map of the quintuple: there is a quintuple over `U'` whose object of
`𝒴` is `z'`, and a morphism of quintuples to it over `i` whose `𝒴`-component is `a`. -/
theorem exists_object_hom_of_coverDeformation
    (hw : w ⋙ 𝒴.toBasedCategory.p = Over.map U'.hom) {z' : 𝒴.toBasedCategory.obj}
    (hz' : 𝒴.toBasedCategory.p.obj z' = U') (c : w.obj (Over.mk (𝟙 U'.left)) ⟶ z')
    (hc : 𝒴.toBasedCategory.p.IsHomLift (𝟙 U') c) (a : P.y ⟶ z')
    (ha : 𝒴.toBasedCategory.p.IsHomLift i a)
    {Xw : (BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u}
    (hXw : IsAlgebraicSpace B U'.left.1 U'.left.2 Xw)
    (ew : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p w
        F.toFunctor)
      (presheafOfCategories (Xw ⋙ typeToCat)).p)
    {Z' : BigFppfOver B S hS} (q' : Z' ⟶ U') (g : P.Z ⟶ Z') (hg : IsPullback g P.q q' i)
    (hq' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q') d)
    (f' : yoneda.obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) ⟶ Xw)
    (hf' : OverShriek.restrictYonedaHom i.left (coverComparisonOfSquare hg.w) ≫
      (OverShriek.relocalizeRestrict i.left).map f' =
      (restrictData P i w hw c hc a ha hXw ew).map.hom) :
    ∃ (Q : Object B S hS 𝒳 𝒴 F d) (φ : P ⟶ Q) (κ : Q.y ⟶ z'),
      (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).IsHomLift i φ ∧
        𝒴.toBasedCategory.p.IsHomLift (𝟙 U') κ ∧ φ.b ≫ κ = a := by
  have hZ' : (Over.map U'.hom).obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) = Z' := by
    change Over.mk (q'.left ≫ U'.hom) = Z'
    exact PresheafOfCategories.over_mk_eq Z' (Over.w q')
  have hstruct : eqToHom hZ' ≫ q' ≫ eqToHom (rfl : U' = U').symm =
      Functor.structHom U' (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) := by
    exact (over_hom_eq_conj_of_heq hZ' (rfl : U' = U') _ q' HEq.rfl).symm
  obtain ⟨x', hx', α', hα', hs'⟩ := exists_relativeSection_eq (e := ew)
    (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) (yonedaEquiv f')
  have hαQ : 𝒴.toBasedCategory.p.IsHomLift q'
      (α'.inv ≫ w.map (Functor.toMkId U'
        (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)) ≫ c) := by
    have h2 := isHomLift_map_toMkId_comp w hw c hc
      (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)
    have h3 : 𝒴.toBasedCategory.p.IsHomLift
        (𝟙 ((Over.map U'.hom).obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)))
        α'.inv :=
      have := hα'
      IsHomLift.lift_id_inv 𝒴.toBasedCategory.p
        ((Over.map U'.hom).obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)) α'
    have h4 : 𝒴.toBasedCategory.p.IsHomLift
        (Functor.structHom U' (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2))
        (α'.inv ≫ w.map (Functor.toMkId U'
          (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)) ≫ c) :=
      have := h3
      have := h2
      IsHomLift.comp_lift_id_left' 𝒴.toBasedCategory.p
        ((Over.map U'.hom).obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)) α'.inv
        (Functor.structHom U' (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2))
        (w.map (Functor.toMkId U'
          (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)) ≫ c)
    exact Functor.isHomLift_of_base_eq _ _ h4 q' hZ' rfl hstruct
  have hPZ : (Over.map U'.hom).obj ((Over.map i.left).obj P.coverOver) = P.Z :=
    Object.overMap_restrictCoverOver P i
  have hgeq : eqToHom hPZ ≫ g ≫ eqToHom hZ'.symm =
      (Over.map U'.hom).map (coverComparisonOfSquare hg.w) := by
    exact (over_hom_eq_conj_of_heq hPZ hZ' _ g HEq.rfl).symm
  have hgeq' : eqToHom hPZ.symm ≫ (Over.map U'.hom).map (coverComparisonOfSquare hg.w) ≫
      eqToHom hZ'.symm.symm = g := by
    exact (over_hom_eq_conj_of_heq hPZ.symm hZ'.symm g _ HEq.rfl).symm
  obtain ⟨x'', a₀, ha₀⟩ := 𝒳.isStackInGroupoids.isFiberedInGroupoids.exists_lift g x'
    (hx'.trans hZ')
  have := ha₀
  have := hα'
  have hx''PZ : 𝒳.toBasedCategory.p.obj x'' = P.Z :=
    IsHomLift.domain_eq 𝒳.toBasedCategory.p g a₀
  have ha₀cmp : 𝒳.toBasedCategory.p.IsHomLift
      ((Over.map U'.hom).map (coverComparisonOfSquare hg.w)) a₀ :=
    Functor.isHomLift_of_base_eq g a₀ ha₀
      ((Over.map U'.hom).map (coverComparisonOfSquare hg.w)) hPZ.symm hZ'.symm hgeq'
  have hx''big : 𝒳.toBasedCategory.p.obj x'' =
      (Over.map U'.hom).obj ((Over.map i.left).obj P.coverOver) := hx''PZ.trans hPZ.symm
  have hx''small : 𝒳.toBasedCategory.p.obj x'' = (Over.map P.U.hom).obj P.coverOver :=
    hx''PZ.trans P.overMap_coverOver.symm
  obtain ⟨α'', hα''PZ, hα''fac⟩ :
      ∃ α'' : w.obj ((Over.map i.left).obj P.coverOver) ≅ F.toFunctor.obj x'',
        𝒴.toBasedCategory.p.IsHomLift (𝟙 P.Z) α''.hom ∧
          α''.hom ≫ F.toFunctor.map a₀ =
            w.map (coverComparisonOfSquare hg.w) ≫ α'.hom := by
    have hwcmp : 𝒴.toBasedCategory.p.IsHomLift
        ((Over.map U'.hom).map (coverComparisonOfSquare hg.w))
        (w.map (coverComparisonOfSquare hg.w)) :=
      PresheafOfCategories.isHomLift_map_of_comp hw
        ((Over.map U'.hom).map (coverComparisonOfSquare hg.w))
        (coverComparisonOfSquare hg.w)
        (inferInstance : (Over.map U'.hom).IsHomLift
          ((Over.map U'.hom).map (coverComparisonOfSquare hg.w))
          (coverComparisonOfSquare hg.w))
    have hwg : 𝒴.toBasedCategory.p.IsHomLift g (w.map (coverComparisonOfSquare hg.w)) :=
      Functor.isHomLift_of_base_eq
        ((Over.map U'.hom).map (coverComparisonOfSquare hg.w))
        (w.map (coverComparisonOfSquare hg.w)) hwcmp g hPZ hZ' hgeq
    have hFa₀ : 𝒴.toBasedCategory.p.IsHomLift g (F.toFunctor.map a₀) :=
      PresheafOfCategories.isHomLift_map_of_comp F.w g a₀ ha₀
    have hsc : 𝒴.toBasedCategory.p.IsStronglyCartesian g (F.toFunctor.map a₀) :=
      𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift g
        (F.toFunctor.map a₀)
    have hτ : 𝒴.toBasedCategory.p.IsHomLift g
        (w.map (coverComparisonOfSquare hg.w) ≫ α'.hom) :=
      IsHomLift.comp_lift_id_right' 𝒴.toBasedCategory.p g
        (w.map (coverComparisonOfSquare hg.w))
        ((Over.map U'.hom).obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)) α'.hom
    have hvert := Functor.IsStronglyCartesian.map_isHomLift 𝒴.toBasedCategory.p g
      (F.toFunctor.map a₀) (Category.id_comp g).symm
      (w.map (coverComparisonOfSquare hg.w) ≫ α'.hom)
    have hfacv := Functor.IsStronglyCartesian.fac 𝒴.toBasedCategory.p g (F.toFunctor.map a₀)
      (Category.id_comp g).symm (w.map (coverComparisonOfSquare hg.w) ≫ α'.hom)
    obtain ⟨αh, hαh⟩ : ∃ αh, αh = Functor.IsStronglyCartesian.map 𝒴.toBasedCategory.p g
        (F.toFunctor.map a₀) (Category.id_comp g).symm
        (w.map (coverComparisonOfSquare hg.w) ≫ α'.hom) := ⟨_, rfl⟩
    rw [← hαh] at hvert hfacv
    have := hvert
    have := 𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 P.Z) αh
    have hiso := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒴.toBasedCategory.p (𝟙 P.Z) αh
    exact ⟨@asIso _ _ _ _ αh hiso, hvert, hfacv⟩
  have hα''small : 𝒴.toBasedCategory.p.IsHomLift
      (𝟙 ((Over.map P.U.hom).obj P.coverOver)) α''.hom := by
    refine Functor.isHomLift_of_base_eq (𝟙 P.Z) α''.hom hα''PZ _
      P.overMap_coverOver.symm P.overMap_coverOver.symm ?_
    simp
  have hα''vert : 𝒴.toBasedCategory.p.IsHomLift
      (𝟙 ((Over.map U'.hom).obj ((Over.map i.left).obj P.coverOver))) α''.hom := by
    refine Functor.isHomLift_of_base_eq (𝟙 P.Z) α''.hom hα''PZ _
      hPZ.symm hPZ.symm ?_
    simp
  have hmap : (restrictData P i w hw c hc a ha hXw ew).map.hom =
      yonedaEquiv.symm (relativeSection F (Over.map i.left ⋙ w)
        (relativeSpaceRestrictEquivalence F w ew i.left (Over.w i)
          𝒳.isStackInGroupoids.isFiberedInGroupoids
          𝒴.isStackInGroupoids.isFiberedInGroupoids hw)
        P.coverOver P.x P.x_over_coverOver (restrictData P i w hw c hc a ha hXw ew).α
        (restrictData P i w hw c hc a ha hXw ew).α_over) := rfl
  have hsec : Xw.map (coverComparisonOfSquare hg.w).op (yonedaEquiv f') =
      relativeSection F (Over.map i.left ⋙ w)
        (relativeSpaceRestrictEquivalence F w ew i.left (Over.w i)
          𝒳.isStackInGroupoids.isFiberedInGroupoids
          𝒴.isStackInGroupoids.isFiberedInGroupoids hw)
        P.coverOver P.x P.x_over_coverOver (restrictData P i w hw c hc a ha hXw ew).α
        (restrictData P i w hw c hc a ha hXw ew).α_over := by
    refine (yonedaEquiv (X := P.coverOver)
      (F := (OverShriek.relocalizeRestrict i.left).obj Xw)).symm.injective ?_
    refine (OverShriek.restrictYonedaHom_comp_relocalizeRestrict_map i.left
      (coverComparisonOfSquare hg.w) Xw (yonedaEquiv f')
      (Xw.map (coverComparisonOfSquare hg.w).op (yonedaEquiv f')) rfl).trans ?_
    refine Eq.trans (congrArg (fun k => OverShriek.restrictYonedaHom i.left
      (coverComparisonOfSquare hg.w) ≫ (OverShriek.relocalizeRestrict i.left).map k)
      (yonedaEquiv.symm_apply_apply f')) ?_
    exact hf'.trans hmap
  have hchain : relativeSection F (Over.map i.left ⋙ w)
        (relativeSpaceRestrictEquivalence F w ew i.left (Over.w i)
          𝒳.isStackInGroupoids.isFiberedInGroupoids
          𝒴.isStackInGroupoids.isFiberedInGroupoids hw)
        P.coverOver P.x P.x_over_coverOver (restrictData P i w hw c hc a ha hXw ew).α
        (restrictData P i w hw c hc a ha hXw ew).α_over =
      relativeSection F (Over.map i.left ⋙ w)
        (relativeSpaceRestrictEquivalence F w ew i.left (Over.w i)
          𝒳.isStackInGroupoids.isFiberedInGroupoids
          𝒴.isStackInGroupoids.isFiberedInGroupoids hw)
        P.coverOver x'' hx''small α'' hα''small :=
    hsec.symm.trans
      ((congrArg (fun t => Xw.map (coverComparisonOfSquare hg.w).op t) hs').symm.trans
        ((relativeSection_map (e := ew) (hx := hx') (hx' := hx''big) (α := α') (α' := α'')
            (hα := hα') (hα' := hα''vert) (coverComparisonOfSquare hg.w) a₀ ha₀cmp
            hα''fac.symm).symm.trans
          (relativeSection_relocalizeRestrict F w ew i.left (Over.w i)
            𝒳.isStackInGroupoids.isFiberedInGroupoids
            𝒴.isStackInGroupoids.isFiberedInGroupoids hw
            P.coverOver x'' hx''small hx''big α'' hα''small hα''vert).symm))
  obtain ⟨ax₀, hax₀, hax₀fac⟩ := exists_hom_of_relativeSection_eq
    (e := relativeSpaceRestrictEquivalence F w ew i.left (Over.w i)
      𝒳.isStackInGroupoids.isFiberedInGroupoids 𝒴.isStackInGroupoids.isFiberedInGroupoids hw)
    (hx := P.x_over_coverOver) (hx' := hx''small)
    (hα := (restrictData P i w hw c hc a ha hXw ew).α_over) (hα' := hα''small) hchain
  have hax₀PZ : 𝒳.toBasedCategory.p.IsHomLift (𝟙 P.Z) ax₀ := by
    refine Functor.isHomLift_of_base_eq
      (𝟙 ((Over.map P.U.hom).obj P.coverOver)) ax₀ hax₀ _ P.overMap_coverOver
      P.overMap_coverOver ?_
    simp
  have := hax₀PZ
  have hgfinal : 𝒳.toBasedCategory.p.IsHomLift g (ax₀ ≫ a₀) :=
    IsHomLift.comp_lift_id_left' 𝒳.toBasedCategory.p P.Z ax₀ g a₀
  have hterm1 : coverComparisonOfSquare hg.w ≫
      Functor.toMkId U' (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) =
      Functor.toMkId U' ((Over.map i.left).obj P.coverOver) := by
    refine Over.OverMorphism.ext ?_
    change g.left ≫ q'.left = P.q.left ≫ i.left
    simpa only [Over.comp_left] using congrArg Over.Hom.left hg.w
  have hterm2 : (Over.map i.left).map P.coverToBase ≫
      Functor.toMkId U' ((Over.map i.left).obj P.baseOver) =
      Functor.toMkId U' ((Over.map i.left).obj P.coverOver) := by
    refine Over.OverMorphism.ext ?_
    change P.q.left ≫ 𝟙 P.U.left ≫ i.left = P.q.left ≫ i.left
    simp
  have hmerge1 : w.map (coverComparisonOfSquare hg.w) ≫
      w.map (Functor.toMkId U' (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)) =
      w.map (Functor.toMkId U' ((Over.map i.left).obj P.coverOver)) :=
    (w.map_comp (coverComparisonOfSquare hg.w) (Functor.toMkId U'
      (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2))).symm.trans
      (congrArg (fun k => w.map k) hterm1)
  have hmerge2 : w.map ((Over.map i.left).map P.coverToBase) ≫
      w.map (Functor.toMkId U' ((Over.map i.left).obj P.baseOver)) =
      w.map (Functor.toMkId U' ((Over.map i.left).obj P.coverOver)) :=
    (w.map_comp ((Over.map i.left).map P.coverToBase) (Functor.toMkId U'
      ((Over.map i.left).obj P.baseOver))).symm.trans
      (congrArg (fun k => w.map k) hterm2)
  have hFax : (restrictData P i w hw c hc a ha hXw ew).α.inv ≫ α''.hom =
      F.toFunctor.map ax₀ :=
    (Iso.inv_comp_eq (restrictData P i w hw c hc a ha hXw ew).α).mpr hax₀fac
  have hαcomp : (restrictData P i w hw c hc a ha hXw ew).α.inv ≫
      w.map ((Over.map i.left).map P.coverToBase) ≫ restrictUnit P i w hw c hc a ha = P.α :=
    (restrictData P i w hw c hc a ha hXw ew).α_comp
  have hcompat : F.toFunctor.map (ax₀ ≫ a₀) ≫
      (α'.inv ≫ w.map (Functor.toMkId U'
        (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)) ≫ c) = P.α ≫ a :=
    by
    rw [← hαcomp, Functor.map_comp, ← hFax, Category.assoc]
    erw [Category.assoc]
    simp only [Category.assoc]
    erw [reassoc_of% hα''fac]
    erw [Category.assoc, Iso.hom_inv_id_assoc]
    erw [Category.assoc, restrictUnit_comp, reassoc_of% hmerge1, reassoc_of% hmerge2]
    rfl
  refine ⟨{ U := U'
            Z := Z'
            q := q'
            finiteLocallyFree := hq'
            y := z'
            y_over := hz'
            x := x'
            x_over := hx'.trans hZ'
            α := α'.inv ≫ w.map (Functor.toMkId U'
              (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2)) ≫ c
            α_over := hαQ },
    { f := i
      g := g
      square := hg
      b := a
      b_over := ha
      a := ax₀ ≫ a₀
      a_over := hgfinal
      compatible := hcompat }, 𝟙 z', ?_, IsHomLift.id hz', Category.comp_id a⟩
  refine IsHomLift.of_fac' _ i _ rfl rfl ?_
  change i = eqToHom (rfl : P.U = P.U) ≫ i ≫ eqToHom (Eq.symm (rfl : U' = U'))
  simp

end Lift

end FiniteHilbert

/-! ### Formal smoothness on objects of the locus over the target -/

section Fibered

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

/-- **The 1-morphism `p : ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is formally smooth on objects** in the sense of
**Stacks 06D0**, for `F : 𝒳 ⟶ 𝒴` representable by algebraic spaces, flat and locally of finite
presentation, and with the deformation problem of
`AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations` solved. -/
theorem isFormallySmoothOnObjects_lciFiniteHilbertToTarget_of_coverDeformations
    (hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hdef : FiniteHilbert.HasCoverDeformations B S hS d) :
    IsFormallySmoothOnObjects B S hS
      (lciFiniteHilbertFibered (isFiberedInGroupoids_lciFiniteHilbertCategory
        (FiniteHilbert.hasOpenLciLocus (d := d) hFrep hFflat hFlfp)))
      (stackFibered B S hS 𝒴)
      (lciFiniteHilbertToTargetFibered (isFiberedInGroupoids_lciFiniteHilbertCategory
        (FiniteHilbert.hasOpenLciLocus (d := d) hFrep hFflat hFlfp))) := by
  refine isFormallySmoothOnObjects_lciFiniteHilbertToTarget_of_lifts
    (FiniteHilbert.hasOpenLciLocus (d := d) hFrep hFflat hFlfp)
    (isFiberedInGroupoids_lciFiniteHilbertCategory
      (FiniteHilbert.hasOpenLciLocus (d := d) hFrep hFflat hFlfp)) ?_
  intro U U' i hU hU' hi x z' a ha
  obtain ⟨⟨P, hPlci⟩, hPU⟩ := x
  have hPU' : P.U = U := hPU
  subst hPU'
  have := 𝒴.isStackInGroupoids.isFiberedInGroupoids.isFibered
  obtain ⟨w, hw, cw, hcw⟩ := Functor.exists_slicePoint 𝒴.toBasedCategory.p U' z'.1 z'.2
  obtain ⟨Xw, hXw, ⟨ew⟩⟩ := hFrep U' w hw
  have hflat : Space.IsFlat B U'.left.1 U'.left.2
      (Space.toYonedaId B U'.left.1 U'.left.2 Xw) :=
    (Space.holdsOnEveryEtaleChart_algebraicSpaceMap_iff B S hS
        (@_root_.AlgebraicGeometry.Flat.{u}) U' Xw hXw).mp
      (hFflat U' w hw Xw hXw ⟨ew⟩)
  have hlfp : Space.IsLocallyOfFinitePresentation B U'.left.1 U'.left.2
      (Space.toYonedaId B U'.left.1 U'.left.2 Xw) :=
    (Space.holdsOnEveryEtaleChart_algebraicSpaceMap_iff B S hS
        (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) U' Xw hXw).mp
      (hFlfp U' w hw Xw hXw ⟨ew⟩)
  obtain ⟨hunr, hlciP⟩ :=
    FiniteHilbert.isUnramified_and_isLocalCompleteIntersection_restrictData_map P i w hw cw hcw
      a ha hXw ew hPlci
  obtain ⟨Z', q', g, hg, hq', f', hf'⟩ := hdef P.U U' i hU hU' hi Xw hXw hflat hlfp P.Z P.q
    P.finiteLocallyFree
    (FiniteHilbert.restrictData P i w hw cw hcw a ha hXw ew).map.hom hunr hlciP
  obtain ⟨Q, φ, κ, hφ, hκ, hbκ⟩ := FiniteHilbert.exists_object_hom_of_coverDeformation P i w hw
    z'.2 cw hcw a ha hXw ew q' g hg hq' f' hf'
  have := hφ
  exact ⟨⟨Q, IsHomLift.codomain_eq (finiteHilbertProjection (B := B) (S := S) (hS := hS)
    (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) i φ⟩, φ, κ, hφ, hκ, hbκ⟩

end Fibered

end AlgebraicGeometry.Stack

end
