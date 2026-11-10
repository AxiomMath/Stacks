module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf

/-!
# Functoriality of the ungraded realization

The ungraded realization of a graded algebra turns a family of homogeneous pieces into a single
ring of sections: over an object of the site the sections are the direct sum of the pieces, and
the sheaf of rings is the sheafification of that presheaf. This file makes that passage
functorial. A unital homomorphism of graded algebras acts degreewise, so it acts on the direct
sums, and the resulting map is a ring homomorphism because the homomorphism preserves products of
homogeneous sections and carries the graded unit to the graded unit.

Three layers are built, each from the previous one: the ring homomorphism on the sections, the
morphism of presheaves of rings, and the morphism of sheaves of rings. On a scheme the last one
is upgraded to a morphism of the algebra sheaves of Stacks Tag 01LM, which is the shape the
relative spectrum consumes. Each layer carries the two functoriality laws, and the comparison
homomorphism of a universal graded algebra carries them as well.

## Main definitions

* `Stacks.GradedAlgebra.totalAddHomOfFamily` and `totalRingHomOfFamily`: **an additive, resp. a
  ring, homomorphism out of the sections of the ungraded realization into an arbitrary target**,
  from a degreewise family of additive maps out of the homogeneous pieces.
* `Stacks.GradedAlgebra.totalRingHom`: **a unital homomorphism of graded algebras, acting on the
  sections of the ungraded realization**, as a ring homomorphism.
* `Stacks.GradedAlgebra.totalPresheafMap` and `Stacks.GradedAlgebra.totalSheafMap`: the same as a
  morphism of presheaves of rings and as a morphism of sheaves of rings.
* `SheafOfModules.GradedAlgebra.ungradedSheafMap` and `ungradedCommSheafMap`: the sheaf-level
  versions for a sheaf of graded algebras, the second between the commutative lifts.
* `Stacks.RelativeSpec.gradedAlgebraSheafMap`: **the morphism of algebra sheaves on a scheme
  induced by a unital homomorphism of sheaves of graded algebras with commutative homogeneous
  multiplication.**

## Main results

* `Stacks.GradedAlgebra.totalRingHom_incl`: the ring homomorphism is the given degreewise map on
  homogeneous sections, which is its defining property.
* `Stacks.GradedAlgebra.structureHom_totalPresheafMap`: it is compatible with the structure maps
  from the base ring, so it is a homomorphism of algebras and not merely of rings.
* `Stacks.GradedAlgebra.toTotalSheaf_totalSheafMap` and
  `SheafOfModules.GradedAlgebra.ungradedIncl_ungradedSheafMap`: the sheaf-level morphism restricts
  to the presheaf-level one along the sheafification unit, hence is the degreewise map on
  homogeneous sections.
* `Stacks.GradedAlgebra.totalSheaf_hom_ext`: two morphisms out of the ungraded realization as a
  sheaf of rings agree as soon as they agree after the sheafification unit.
* `Stacks.GradedAlgebra.totalPresheafMap_id`, `totalPresheafMap_comp`, `totalSheafMap_id`,
  `totalSheafMap_comp`, and `SheafOfModules.GradedAlgebra.ungradedSheafMap_id`,
  `ungradedSheafMap_comp`, `ungradedCommSheafMap_id`, `ungradedCommSheafMap_comp`:
  **functoriality** of each of the four layers.
* `SheafOfModules.GradedAlgebra.IsUniversal.descComp_id` and `descComp_comp`: **functoriality of
  the comparison homomorphism of a universal graded algebra in its module argument**, derived
  from `SheafOfModules.GradedAlgebra.IsUniversal.descComp_unique`.

## Implementation notes

The additive map on the sections is `DirectSum.toAddMonoid` of the degreewise maps, so it is
determined by its values on homogeneous sections and `Stacks.GradedAlgebra.incl_induction` proves
every identity about it. Multiplicativity is that induction in both arguments, with
`Stacks.GradedAlgebra.incl_mul_incl` turning a product of homogeneous sections into a homogeneous
section of the sum degree in both the source and the target.

Compatibility with the structure maps is not an extra hypothesis. The structure map is
`r ↦ r • 1`, the unit is the homogeneous section `Stacks.GradedAlgebra.one_eq_incl`, and the
degreewise maps are linear, so preservation of the unit already gives it.

The sheaf-level morphism is obtained from the universal property of sheafification rather than by
sheafifying the presheaf morphism as a functor: `Stacks.GradedAlgebra.totalSheafLift` maps out of
the realization, and the morphism into the target's realization is the presheaf morphism followed
by the target's sheafification unit. The two sheaf-level functoriality laws are proved by
`Stacks.GradedAlgebra.totalSheaf_hom_ext` rather than by computing on sections of the
sheafification: a section of the sheafification of the direct sum is only *locally* a finite sum
of homogeneous ones, so the elementwise route would need a local induction, while the universal
property needs none.

For a sheaf of graded algebras the commutative lift of `Stacks.CommRingSheaf` keeps the carrier
and the ring operations and only adds a field, so a ring homomorphism between two sheaves whose
sections commute *is* a homomorphism of commutative rings; `Stacks.CommRingSheaf.sheafMap`
records that, and it is why no comparison morphism appears in
`Stacks.RelativeSpec.gradedAlgebraSheafMap`. In particular every equation between morphisms of
the commutative lifts is reduced by `Stacks.CommRingSheaf.sheaf_hom_ext` to the corresponding
equation in `RingCat` applied to a section, with no transport.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe a v u t w

namespace Stacks.GradedAlgebra

/-! ### Maps out of the sections of the realization into an arbitrary ring -/

section OfFamily

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{w} R} (A : GradedAlgebra P)

/-- A degreewise family of additive maps out of the homogeneous pieces, acting on the sections
of the ungraded realization over an object of the site. -/
def totalAddHomOfFamily {S : Type w} [AddCommMonoid S] (X : Cᵒᵖ)
    (φ : ∀ i : ι, (P i).obj X →+ S) : A.Total X →+ S :=
  DirectSum.toAddMonoid φ

/-- On a homogeneous section, the additive map is the given degreewise map. -/
@[simp]
lemma totalAddHomOfFamily_incl {S : Type w} [AddCommMonoid S] (X : Cᵒᵖ)
    (φ : ∀ i : ι, (P i).obj X →+ S) (i : ι) (x : (P i).obj X) :
    A.totalAddHomOfFamily X φ (A.incl i x) = φ i x :=
  DirectSum.toAddMonoid_of φ i x

/-- **A ring homomorphism out of the sections of the ungraded realization into an arbitrary
ring**, from a degreewise family of additive maps out of the homogeneous pieces which is
multiplicative on homogeneous sections and sends the graded unit to `1`.

This is `Stacks.GradedAlgebra.totalRingHom` with the target freed: there the family is the
action of a `Stacks.GradedAlgebra.UnitalHom` and the target is another realization, here the
target is any ring at all. That freedom is what a comparison between realizations over
*different* base ring sheaves — the two sides of
`Stacks.RelativeSpec.pullbackUnderlyingModuleIso`, say — needs, since there is no `UnitalHom`
between them to apply `totalRingHom` to. -/
def totalRingHomOfFamily {S : Type w} [Ring S] (X : Cᵒᵖ) (φ : ∀ i : ι, (P i).obj X →+ S)
    (hmul : ∀ (i j : ι) (x : (P i).obj X) (y : (P j).obj X),
      φ (i + j) ((A.mul i j).app X x y) = φ i x * φ j y)
    (hone : φ 0 (A.one.eval X) = 1) : A.Total X →+* S where
  toFun := A.totalAddHomOfFamily X φ
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [A.one_eq_incl, A.totalAddHomOfFamily_incl]
    exact hone
  map_mul' a b := by
    induction a using A.incl_induction with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | incl i x =>
      induction b using A.incl_induction with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | incl j y =>
        rw [A.incl_mul_incl, A.totalAddHomOfFamily_incl, A.totalAddHomOfFamily_incl,
          A.totalAddHomOfFamily_incl]
        exact hmul i j x y
      | add b b' hb hb' => rw [mul_add, map_add, map_add, mul_add, hb, hb']
    | add a a' ha ha' => rw [add_mul, map_add, map_add, add_mul, ha, ha']

/-- On a homogeneous section, the ring homomorphism is the given degreewise map. -/
@[simp]
lemma totalRingHomOfFamily_incl {S : Type w} [Ring S] (X : Cᵒᵖ) (φ : ∀ i : ι, (P i).obj X →+ S)
    (hmul : ∀ (i j : ι) (x : (P i).obj X) (y : (P j).obj X),
      φ (i + j) ((A.mul i j).app X x y) = φ i x * φ j y)
    (hone : φ 0 (A.one.eval X) = 1) (i : ι) (x : (P i).obj X) :
    A.totalRingHomOfFamily X φ hmul hone (A.incl i x) = φ i x :=
  A.totalAddHomOfFamily_incl X φ i x

end OfFamily

section Presheaf

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P Q : ι → PresheafOfModules.{w} R} {A : GradedAlgebra P} {B : GradedAlgebra Q}

omit [DecidableEq ι] in
/-- The degreewise component of a homomorphism of graded algebras over an object of the site, as
an additive map. -/
def appAddHom (f : Hom A B) (i : ι) (X : Cᵒᵖ) : (P i).obj X →+ (Q i).obj X where
  toFun x := PresheafOfModules.Hom.app (f.app i) X x
  map_zero' := map_zero (PresheafOfModules.Hom.app (f.app i) X).hom
  map_add' x y := map_add (PresheafOfModules.Hom.app (f.app i) X).hom x y

omit [DecidableEq ι] in
/-- The degreewise component as an additive map is the component of the homomorphism. -/
@[simp]
lemma appAddHom_apply (f : Hom A B) (i : ι) (X : Cᵒᵖ) (x : (P i).obj X) :
    appAddHom f i X x = PresheafOfModules.Hom.app (f.app i) X x :=
  rfl

/-- The inclusion of a homogeneous piece into the sections of the ungraded realization, as an
additive map. -/
def inclAddHom (A : GradedAlgebra P) (i : ι) (X : Cᵒᵖ) : (P i).obj X →+ A.Total X where
  toFun x := A.incl i x
  map_zero' := A.incl_zero i
  map_add' := A.incl_add i

/-- A homomorphism of graded algebras, acting on the sections of the ungraded realization over an
object of the site, as an additive map. -/
def totalAddHom (f : Hom A B) (X : Cᵒᵖ) : A.Total X →+ B.Total X :=
  DirectSum.toAddMonoid fun i => (inclAddHom B i X).comp (appAddHom f i X)

/-- A homomorphism of graded algebras acts on a homogeneous section by its degreewise
component. -/
@[simp]
lemma totalAddHom_incl (f : Hom A B) (X : Cᵒᵖ) (i : ι) (x : (P i).obj X) :
    totalAddHom f X (A.incl i x) = B.incl i (PresheafOfModules.Hom.app (f.app i) X x) :=
  DirectSum.toAddMonoid_of (fun i => (inclAddHom B i X).comp (appAddHom f i X)) i x

/-- **A unital homomorphism of graded algebras, acting on the sections of the ungraded
realization**, as a ring homomorphism: it is additive by construction, multiplicative because
products of homogeneous sections are preserved, and unital because the graded unit is. -/
def totalRingHom (f : UnitalHom A B) (X : Cᵒᵖ) : A.Total X →+* B.Total X where
  toFun := totalAddHom f.toHom X
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [A.one_eq_incl, totalAddHom_incl, f.map_one, ← B.one_eq_incl]
  map_mul' a b := by
    induction a using A.incl_induction with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | incl i x =>
      induction b using A.incl_induction with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | incl j y =>
        rw [A.incl_mul_incl, totalAddHom_incl, totalAddHom_incl, totalAddHom_incl,
          B.incl_mul_incl]
        exact congrArg (B.incl (i + j)) (f.map_mul i j X x y)
      | add b b' hb hb' => rw [mul_add, map_add, map_add, mul_add, hb, hb']
    | add a a' ha ha' => rw [add_mul, map_add, map_add, add_mul, ha, ha']

/-- A unital homomorphism of graded algebras acts on a homogeneous section by its degreewise
component, as a ring homomorphism. -/
@[simp]
lemma totalRingHom_incl (f : UnitalHom A B) (X : Cᵒᵖ) (i : ι) (x : (P i).obj X) :
    totalRingHom f X (A.incl i x) = B.incl i (PresheafOfModules.Hom.app (f.app i) X x) :=
  totalAddHom_incl f.toHom X i x

/-- The action on sections is compatible with restriction along a morphism of the site. -/
lemma totalRestrict_totalAddHom (f : Hom A B) {X Y : Cᵒᵖ} (g : X ⟶ Y) (a : A.Total X) :
    B.totalRestrict g (totalAddHom f X a) = totalAddHom f Y (A.totalRestrict g a) := by
  induction a using A.incl_induction with
  | zero => simp
  | incl i x =>
    rw [totalAddHom_incl, B.totalRestrict_incl, A.totalRestrict_incl, totalAddHom_incl]
    refine congrArg (B.incl i) ?_
    exact (CategoryTheory.congr_fun ((f.app i).naturality g) x).symm
  | add a a' ha ha' => simp only [map_add, ha, ha']

/-- **A unital homomorphism of graded algebras, as a morphism of the ungraded realizations as
presheaves of rings.** -/
def totalPresheafMap (f : UnitalHom A B) : A.totalPresheaf ⟶ B.totalPresheaf where
  app X := RingCat.ofHom (totalRingHom f X)
  naturality X Y g := by
    refine RingCat.hom_ext (RingHom.ext fun a => ?_)
    exact (totalRestrict_totalAddHom f.toHom g a).symm

/-- The morphism of presheaves of rings acts on a homogeneous section by the degreewise
component. -/
@[simp]
lemma totalPresheafMap_app_incl (f : UnitalHom A B) (X : Cᵒᵖ) (i : ι) (x : (P i).obj X) :
    (totalPresheafMap f).app X (A.incl i x) =
      B.incl i (PresheafOfModules.Hom.app (f.app i) X x) :=
  totalRingHom_incl f X i x

/-- The structure map from the base ring is the homogeneous section of degree `0` given by the
scalar multiple of the unit. -/
private lemma structureMap_eq_incl_zero {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    {ι : Type} [DecidableEq ι] [AddMonoid ι] {P : ι → PresheafOfModules.{w} R}
    (A : GradedAlgebra P) (X : Cᵒᵖ) (r : R.obj X) :
    A.structureMap X r = A.incl 0 (r • A.one.eval X) := by
  rw [A.incl_smul, ← A.one_eq_incl]
  rfl

/-- **The morphism of ungraded realizations is compatible with the structure maps from the base
ring**, so it is a homomorphism of algebras over that ring. -/
lemma structureHom_totalPresheafMap (f : UnitalHom A B) :
    A.structureHom ≫ totalPresheafMap f = B.structureHom := by
  ext X r
  change totalRingHom f X (A.structureMap X r) = B.structureMap X r
  rw [structureMap_eq_incl_zero, structureMap_eq_incl_zero, totalRingHom_incl]
  refine congrArg (B.incl 0) ?_
  rw [← f.map_one X]
  exact map_smul (PresheafOfModules.Hom.app (f.toHom.app 0) X).hom r (A.one.eval X)

variable (J : GrothendieckTopology C) [HasSheafify J RingCat.{w}]

/-- **A unital homomorphism of graded algebras, as a morphism of the ungraded realizations as
sheaves of rings.** -/
def totalSheafMap (f : UnitalHom A B) : A.totalSheaf J ⟶ B.totalSheaf J :=
  A.totalSheafLift J (B.totalSheaf J) (totalPresheafMap f ≫ B.toTotalSheaf J)

/-- Along the sheafification unit, the morphism of sheaves of rings is the morphism of presheaves
of rings followed by the sheafification unit of the target. -/
@[simp]
lemma toTotalSheaf_totalSheafMap (f : UnitalHom A B) :
    A.toTotalSheaf J ≫ (totalSheafMap J f).hom = totalPresheafMap f ≫ B.toTotalSheaf J :=
  A.toTotalSheaf_totalSheafLift J _ _

/-- The morphism of ungraded realizations as sheaves of rings is the degreewise map on
homogeneous local sections. -/
lemma inclSheaf_totalSheafMap (f : UnitalHom A B) {X : Cᵒᵖ} (i : ι) (x : (P i).obj X) :
    ((totalSheafMap J f).hom.app X).hom (A.inclSheaf J i x) =
      B.inclSheaf J i (PresheafOfModules.Hom.app (f.app i) X x) := by
  have h : (A.toTotalSheaf J ≫ (totalSheafMap J f).hom).app X =
      (totalPresheafMap f ≫ B.toTotalSheaf J).app X :=
    congrArg (fun φ => NatTrans.app φ X) (toTotalSheaf_totalSheafMap J f)
  have key : ((totalSheafMap J f).hom.app X).hom (A.totalUnit J X (A.incl i x)) =
      B.totalUnit J X (totalRingHom f X (A.incl i x)) :=
    congrArg (fun g : A.totalPresheaf.obj X ⟶ (B.totalSheaf J).obj.obj X =>
      RingCat.Hom.hom g (A.incl i x)) h
  simp only [inclSheaf]
  rw [← totalRingHom_incl f X i x]
  exact key

/-- The morphism of ungraded realizations as sheaves of rings is compatible with the structure
maps from the base ring. -/
lemma structureSheafHom_totalSheafMap (f : UnitalHom A B) :
    A.structureSheafHom J ≫ (totalSheafMap J f).hom = B.structureSheafHom J := by
  rw [structureSheafHom, Category.assoc, toTotalSheaf_totalSheafMap,
    ← Category.assoc, structureHom_totalPresheafMap, structureSheafHom]

end Presheaf

/-! ### Functoriality on presheaves of rings -/

section PresheafFunctoriality

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P Q N : ι → PresheafOfModules.{w} R} {A : GradedAlgebra P} {B : GradedAlgebra Q}
  {D : GradedAlgebra N}

/-- The identity acts on the sections of the ungraded realization as the identity. -/
lemma totalRingHom_id (X : Cᵒᵖ) (a : A.Total X) : totalRingHom (UnitalHom.id A) X a = a := by
  induction a using A.incl_induction with
  | zero => simp
  | incl i x => rw [totalRingHom_incl]; rfl
  | add a a' ha ha' => rw [map_add, ha, ha']

/-- A composite acts on the sections of the ungraded realization as the composite. -/
lemma totalRingHom_comp (f : UnitalHom A B) (g : UnitalHom B D) (X : Cᵒᵖ) (a : A.Total X) :
    totalRingHom (f.comp g) X a = totalRingHom g X (totalRingHom f X a) := by
  induction a using A.incl_induction with
  | zero => simp
  | incl i x => rw [totalRingHom_incl, totalRingHom_incl, totalRingHom_incl]; rfl
  | add a a' ha ha' => simp only [map_add, ha, ha']

/-- **The morphism of presheaves of rings induced by the identity is the identity.** -/
lemma totalPresheafMap_id : totalPresheafMap (UnitalHom.id A) = 𝟙 A.totalPresheaf :=
  by
  ext X a
  exact totalRingHom_id X a

/-- **The morphism of presheaves of rings induced by a composite is the composite of the induced
morphisms.** -/
lemma totalPresheafMap_comp (f : UnitalHom A B) (g : UnitalHom B D) :
    totalPresheafMap (f.comp g) = totalPresheafMap f ≫ totalPresheafMap g :=
  by
  ext X a
  exact totalRingHom_comp f g X a

end PresheafFunctoriality

/-! ### Morphisms out of the ungraded realization as a sheaf of rings -/

section SheafUniqueness

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{w} R}

/-- **Two morphisms out of the ungraded realization of a graded algebra agree as soon as they
agree after the sheafification unit**, the unit being the universal map into the
sheafification. -/
theorem totalSheaf_hom_ext (A : GradedAlgebra P) (J : GrothendieckTopology C)
    [HasSheafify J RingCat.{w}] {S : Sheaf J RingCat.{w}} {g h : A.totalSheaf J ⟶ S}
    (hgh : A.toTotalSheaf J ≫ g.hom = A.toTotalSheaf J ≫ h.hom) : g = h :=
  Sheaf.hom_ext
    ((sheafifyLift_unique J (A.toTotalSheaf J ≫ g.hom) S.property g.hom rfl).trans
      (sheafifyLift_unique J (A.toTotalSheaf J ≫ g.hom) S.property h.hom hgh.symm).symm)

end SheafUniqueness

/-! ### Functoriality on sheaves of rings -/

section SheafFunctoriality

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P Q N : ι → PresheafOfModules.{w} R} {A : GradedAlgebra P} {B : GradedAlgebra Q}
  {D : GradedAlgebra N} (J : GrothendieckTopology C) [HasSheafify J RingCat.{w}]

/-- **The morphism of sheaves of rings induced by the identity is the identity.** -/
lemma totalSheafMap_id : totalSheafMap J (UnitalHom.id A) = 𝟙 (A.totalSheaf J) := by
  refine totalSheaf_hom_ext A J ?_
  rw [toTotalSheaf_totalSheafMap, totalPresheafMap_id, Category.id_comp]
  exact (Category.comp_id _).symm

/-- **The morphism of sheaves of rings induced by a composite is the composite of the induced
morphisms.** -/
lemma totalSheafMap_comp (f : UnitalHom A B) (g : UnitalHom B D) :
    totalSheafMap J (f.comp g) = totalSheafMap J f ≫ totalSheafMap J g := by
  refine totalSheaf_hom_ext A J ?_
  rw [toTotalSheaf_totalSheafMap, totalPresheafMap_comp, Category.assoc,
    ← toTotalSheaf_totalSheafMap J g, ← Category.assoc, ← toTotalSheaf_totalSheafMap J f]
  exact Category.assoc _ _ _

end SheafFunctoriality

end Stacks.GradedAlgebra

namespace Stacks.CommRingSheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- A ring homomorphism between presheaves of rings whose sections commute, as a morphism of the
presheaves of commutative rings they lift to. The carrier and the operations are unchanged, so
this is the same data. -/
def presheafMap {S T : Cᵒᵖ ⥤ RingCat.{u}} (hS : ∀ (W : Cᵒᵖ) (a b : S.obj W), a * b = b * a)
    (hT : ∀ (W : Cᵒᵖ) (a b : T.obj W), a * b = b * a) (f : S ⟶ T) :
    presheaf S hS ⟶ presheaf T hT where
  app W := ofRingCatHom (hS W) (hT W) (f.app W)
  naturality W W' g := by
    ext x
    exact congrArg (fun φ => RingCat.Hom.hom φ x) (f.naturality g)

/-- **A morphism of sheaves of rings whose sections commute, as a morphism of the sheaves of
commutative rings they lift to.** -/
def sheafMap {S T : Sheaf J RingCat.{u}} (hS : ∀ (W : Cᵒᵖ) (a b : S.obj.obj W), a * b = b * a)
    (hT : ∀ (W : Cᵒᵖ) (a b : T.obj.obj W), a * b = b * a) (f : S ⟶ T) :
    sheaf S hS ⟶ sheaf T hT :=
  ObjectProperty.homMk (presheafMap hS hT f.hom)

/-- Two morphisms of sheaves of commutative rings out of the lift of a sheaf of rings agree as
soon as they agree on every section. The lift keeps the carrier, so this is extensionality of
the underlying morphisms of sheaves of rings. -/
theorem sheaf_hom_ext {S : Sheaf J RingCat.{u}}
    (hS : ∀ (W : Cᵒᵖ) (a b : S.obj.obj W), a * b = b * a) {O : Sheaf J CommRingCat.{u}}
    {f g : sheaf S hS ⟶ O}
    (h : ∀ (W : Cᵒᵖ) (x : S.obj.obj W), (f.hom.app W).hom x = (g.hom.app W).hom x) : f = g :=
  Sheaf.hom_ext (NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext (h W))))

/-- Equal morphisms of sheaves of rings agree on every section. -/
private lemma app_eq_of_eq {S T : Sheaf J RingCat.{u}} {k k' : S ⟶ T} (h : k = k') (W : Cᵒᵖ)
    (x : S.obj.obj W) : (k.hom.app W).hom x = (k'.hom.app W).hom x :=
  h ▸ rfl

end Stacks.CommRingSheaf

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]

/-- A unital homomorphism of sheaves of graded algebras, read as one of the underlying graded
algebras of presheaves of modules. The data are the same: only the sheaf conditions on the pieces
are forgotten. -/
def UnitalHom.toPresheafGradedAlgebraHom {A B : GradedAlgebra.{u, u} R} (f : UnitalHom A B) :
    Stacks.GradedAlgebra.UnitalHom A.toPresheafGradedAlgebra B.toPresheafGradedAlgebra where
  app n := (f.app n).val
  map_mul i j U x y := f.map_mul i j U x y
  map_one U := f.map_one U

/-- **A unital homomorphism of sheaves of graded algebras, as a morphism of their ungraded
realizations as sheaves of rings.** -/
def ungradedSheafMap {A B : GradedAlgebra.{u, u} R} (f : UnitalHom A B) :
    A.ungradedSheaf ⟶ B.ungradedSheaf :=
  Stacks.GradedAlgebra.totalSheafMap J f.toPresheafGradedAlgebraHom

omit [J.WEqualsLocallyBijective RingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})] in
/-- The morphism of ungraded realizations is the degreewise map on homogeneous local sections. -/
lemma ungradedIncl_ungradedSheafMap {A B : GradedAlgebra.{u, u} R} (f : UnitalHom A B) {X : Cᵒᵖ}
    (i : ℤ) (x : (A.piece i).val.obj X) :
    ((ungradedSheafMap f).hom.app X).hom (A.ungradedIncl i x) =
      B.ungradedIncl i ((f.app i).val.app X x) :=
  Stacks.GradedAlgebra.inclSheaf_totalSheafMap J f.toPresheafGradedAlgebraHom i x

omit [J.WEqualsLocallyBijective RingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})] in
/-- The morphism of ungraded realizations is compatible with the structure maps from the structure
sheaf. -/
lemma ungradedStructureMap_ungradedSheafMap {A B : GradedAlgebra.{u, u} R} (f : UnitalHom A B) :
    A.ungradedStructureMap ≫ ungradedSheafMap f = B.ungradedStructureMap :=
  Sheaf.hom_ext
    (Stacks.GradedAlgebra.structureSheafHom_totalSheafMap J f.toPresheafGradedAlgebraHom)

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **A unital homomorphism of sheaves of graded algebras with commutative homogeneous
multiplication, as a morphism of the ungraded realizations as sheaves of commutative rings.** -/
def ungradedCommSheafMap {A B : GradedAlgebra.{u, u} R} (f : UnitalHom A B)
    (hcA : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hcB : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (B.piece i).val.obj W) (b : (B.piece j).val.obj W),
      HEq ((B.mul i j).app W a b) ((B.mul j i).app W b a)) :
    A.ungradedCommSheaf hcA ⟶ B.ungradedCommSheaf hcB :=
  Stacks.CommRingSheaf.sheafMap (A.mul_comm_ungradedSheaf hcA) (B.mul_comm_ungradedSheaf hcB)
    (ungradedSheafMap f)

end SheafOfModules.GradedAlgebra

/-! ### Functoriality of the ungraded realization of a sheaf of graded algebras -/

namespace SheafOfModules.GradedAlgebra

section Functoriality

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})] {A B D : GradedAlgebra.{u, u} R}

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})] in
/-- Reading the identity on the underlying graded algebra of presheaves of modules gives the
identity. -/
@[simp]
lemma UnitalHom.toPresheafGradedAlgebraHom_id :
    (UnitalHom.id A).toPresheafGradedAlgebraHom =
      Stacks.GradedAlgebra.UnitalHom.id A.toPresheafGradedAlgebra :=
  rfl

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})] in
/-- Reading a composite on the underlying graded algebras of presheaves of modules gives the
composite. -/
@[simp]
lemma UnitalHom.toPresheafGradedAlgebraHom_comp (ψ : UnitalHom A B) (χ : UnitalHom B D) :
    (ψ.comp χ).toPresheafGradedAlgebraHom =
      ψ.toPresheafGradedAlgebraHom.comp χ.toPresheafGradedAlgebraHom :=
  rfl

omit [J.WEqualsLocallyBijective RingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})] in
/-- **The ungraded realization of the identity is the identity.** -/
lemma ungradedSheafMap_id : ungradedSheafMap (UnitalHom.id A) = 𝟙 A.ungradedSheaf :=
  Stacks.GradedAlgebra.totalSheafMap_id J

omit [J.WEqualsLocallyBijective RingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})] in
/-- **The ungraded realization of a composite is the composite of the realizations.** -/
lemma ungradedSheafMap_comp (ψ : UnitalHom A B) (χ : UnitalHom B D) :
    ungradedSheafMap (ψ.comp χ) = ungradedSheafMap ψ ≫ ungradedSheafMap χ :=
  Stacks.GradedAlgebra.totalSheafMap_comp J ψ.toPresheafGradedAlgebraHom
    χ.toPresheafGradedAlgebraHom

/-- **The ungraded realization of the identity is the identity**, between the commutative
lifts. -/
lemma ungradedCommSheafMap_id
    (hcA : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a)) :
    ungradedCommSheafMap (UnitalHom.id A) hcA hcA = 𝟙 (A.ungradedCommSheaf hcA) := by
  refine Stacks.CommRingSheaf.sheaf_hom_ext (A.mul_comm_ungradedSheaf hcA) fun W x => ?_
  exact Stacks.CommRingSheaf.app_eq_of_eq ungradedSheafMap_id W x

/-- **The ungraded realization of a composite is the composite of the realizations**, between the
commutative lifts. -/
lemma ungradedCommSheafMap_comp
    (hcA : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hcB : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (B.piece i).val.obj W) (b : (B.piece j).val.obj W),
      HEq ((B.mul i j).app W a b) ((B.mul j i).app W b a))
    (hcD : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (D.piece i).val.obj W) (b : (D.piece j).val.obj W),
      HEq ((D.mul i j).app W a b) ((D.mul j i).app W b a))
    (ψ : UnitalHom A B) (χ : UnitalHom B D) :
    ungradedCommSheafMap (ψ.comp χ) hcA hcD =
      ungradedCommSheafMap ψ hcA hcB ≫ ungradedCommSheafMap χ hcB hcD := by
  refine Stacks.CommRingSheaf.sheaf_hom_ext (A.mul_comm_ungradedSheaf hcA) fun W x => ?_
  exact Stacks.CommRingSheaf.app_eq_of_eq (ungradedSheafMap_comp ψ χ) W x

end Functoriality

/-! ### Functoriality of the comparison homomorphism of a universal graded algebra -/

namespace IsUniversal

section Functorial

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N L : SheafOfModules.{a} R} {A B D : GradedAlgebra.{t, a} R}
  {P : ∀ B : GradedAlgebra.{t, a} R, (M ⟶ B.piece 1) → Prop}
  {Q : ∀ B : GradedAlgebra.{t, a} R, (N ⟶ B.piece 1) → Prop}
  {ι : M ⟶ A.piece 1} {κ : N ⟶ B.piece 1}

/-- **The comparison homomorphism induced by the identity is the identity**, by the uniqueness
`SheafOfModules.GradedAlgebra.IsUniversal.descComp_unique`. -/
theorem descComp_id (hA : IsUniversal P A ι) (hPA : P A (𝟙 M ≫ ι)) :
    hA.descComp (𝟙 M) ι hPA = UnitalHom.id A :=
  (hA.descComp_unique (𝟙 M) ι hPA
    (by rw [UnitalHom.id_app, Category.comp_id, Category.id_comp])).symm

/-- **The comparison homomorphism induced by a composite is the composite of the comparison
homomorphisms.** -/
theorem descComp_comp (hA : IsUniversal P A ι) (hB : IsUniversal Q B κ) (p : M ⟶ N) (q : N ⟶ L)
    (lam : L ⟶ D.piece 1) (hPB : P B (p ≫ κ)) (hQD : Q D (q ≫ lam))
    (hPD : P D ((p ≫ q) ≫ lam)) :
    hA.descComp (p ≫ q) lam hPD =
      (hA.descComp p κ hPB).comp (hB.descComp q lam hQD) :=
  (hA.descComp_unique (p ≫ q) lam hPD (by
    rw [UnitalHom.comp_app, ← Category.assoc, descComp_extends, Category.assoc,
      descComp_extends, Category.assoc])).symm

end Functorial

end IsUniversal

end SheafOfModules.GradedAlgebra

namespace Stacks.RelativeSpec

open _root_.AlgebraicGeometry

/-- **The morphism of algebra sheaves on a scheme induced by a unital homomorphism of sheaves of
graded algebras with commutative homogeneous multiplication.** Its underlying morphism of sheaves
of rings is the morphism of ungraded realizations, and it commutes with the two structure
morphisms from the structure sheaf. -/
def gradedAlgebraSheafMap (X : Scheme.{u})
    {A B : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (f : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (hcA : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hcB : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (B.piece i).val.obj W)
      (b : (B.piece j).val.obj W), HEq ((B.mul i j).app W a b) ((B.mul j i).app W b a)) :
    gradedAlgebraSheaf X A hcA ⟶ gradedAlgebraSheaf X B hcB :=
  Under.homMk (A.ungradedCommSheafMap f hcA hcB)
    (Sheaf.hom_ext (NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun r =>
      congrArg (fun ψ : X.ringCatSheaf ⟶ B.ungradedSheaf => RingCat.Hom.hom (ψ.hom.app W) r)
        (A.ungradedStructureMap_ungradedSheafMap f)))))

end Stacks.RelativeSpec

end
