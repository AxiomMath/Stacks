module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMorphism

/-!
# The zero section and the punctured total space of a line bundle

Let `f : X ⟶ S` be a morphism of schemes and `L` an invertible `𝒪_X`-module. The total space of
`L` is the relative spectrum of `Sym(L) = ⨁_{n ≥ 0} L^{⊗ n}` over `X`. Since the homogeneous
pieces of `Sym(L)` vanish in negative degrees, the degree-zero component of a section of its
ungraded realization is a ring homomorphism, and degree zero is the structure sheaf: this is the
augmentation `Sym(L) ⟶ 𝒪_X`, which kills every positive degree and retracts the structure map of
the algebra. The section of the total space it cuts out is the zero section, a closed immersion
because it splits an affine, hence separated, morphism, and the punctured total space is the open
complement of its image.

## Main definitions

* `Stacks.GradedAlgebra.degreeZeroComponent`: the degree-zero component of a section of the
  ungraded realization of a `ℤ`-graded algebra.
* `Stacks.GradedAlgebra.augmentation` and `Stacks.GradedAlgebra.totalCommAugmentation`: **the
  degree-zero augmentation of the ungraded realization of a `ℤ`-graded algebra concentrated in
  nonnegative degrees**, as a ring homomorphism on sections and as a morphism of presheaves of
  commutative rings.
* `Stacks.RelativeSpec.pieceZeroAugmentation`: the degree-zero identification of a sheaf of
  graded algebras on a scheme, read with the ring of sections of the structure sheaf as target.
* `Stacks.RelativeSpec.algebraSheafAugmentation`: the degree-zero augmentation of the ungraded
  algebra sheaf, as a morphism of sheaves of commutative rings.
* `Stacks.RelativeSpec.retractionSection` and `Stacks.RelativeSpec.retractionComplement`: **the
  section of a relative spectrum attached to a retraction of the structure map of its algebra,
  and the open complement of its image.**
* `Stacks.LineBundle.Situation.zeroSection`: **the zero section of the total space of a line
  bundle.**
* `Stacks.LineBundle.Situation.puncturedOpen`,
  `Stacks.LineBundle.Situation.puncturedTotalSpace` and
  `Stacks.LineBundle.Situation.puncturedProjection`: **the punctured total space of a line
  bundle** and its projection to the base.

## Main results

* `Stacks.GradedAlgebra.augmentation_structureMap`: the degree-zero augmentation retracts the
  structure map `r ↦ r • 1` of the ungraded realization.
* `Stacks.RelativeSpec.pieceZeroAugmentation_mul`: the degree-zero identification of a sheaf of
  graded algebras is multiplicative.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceZeroIso_hom_one`: the degree-zero
  identification of the symmetric algebra of a module sheaf on a scheme carries the algebra unit
  to `1`.
* `Stacks.RelativeSpec.isClosedImmersion_retractionSection`: **a section of a relative spectrum
  attached to a retraction of the structure map of its algebra is a closed immersion.**
* `Stacks.RelativeSpec.ι_retractionSection` and `Stacks.LineBundle.Situation.ι_zeroSection`:
  over an affine open of the base such a section is the spectrum of the retraction on sections.
* `Stacks.LineBundle.Situation.zeroSection_comp_totalSpaceToBase` and
  `Stacks.LineBundle.Situation.isClosedImmersion_zeroSection`: the zero section splits the
  structure morphism of the total space, and is a closed immersion.

## Implementation notes

Multiplicativity of the degree-zero component rests only on the vanishing of the negative
pieces: a product of homogeneous sections of degrees `i` and `j` contributes to degree zero only
when `i + j = 0`, and then either one of the two degrees is negative, so that the corresponding
section vanishes, or both are zero. That is why no hypothesis beyond `hzero` is needed, and why
the multiplicativity of the degree-zero piece itself is the only extra input; for a symmetric
algebra the latter comes from degree zero being free of rank one on the algebra unit,
`SheafOfModules.GradedAlgebra.eq_smul_one_of_isoUnit`.

The scalar of a degree-zero local section is named through
`Stacks.RelativeSpec.pieceZeroAugmentation` rather than as `e.hom.val.app U x`, for the reason
recorded in `SheafOfModules.GradedAlgebra.eq_smul_one_of_isoUnit`: written the latter way the
scalar has type `(SheafOfModules.unit R).val.obj U`, which is the ring of sections only up to
unfolding `SheafOfModules.unit`, and instance search for the scalar action does not unfold it.

That the zero section is a closed immersion is not proved by a local computation: it splits
`Stacks.RelativeSpec.gluedSpectrum`'s structure morphism, which is affine by
`Stacks.RelativeSpec.isAffineHom_toBase` and hence separated, so
`AlgebraicGeometry.IsClosedImmersion.of_comp` applies to the identity of the base.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

universe v u w

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
  {P : ℤ → PresheafOfModules.{w} R} (A : GradedAlgebra P)

/-- The degree-zero component of a section of the ungraded realization of a `ℤ`-graded
algebra. -/
def degreeZeroComponent (X : Cᵒᵖ) : A.Total X →+ ((P 0).obj X : Type w) :=
  (DirectSum.component (R.obj X) ℤ (fun i => ((P i).obj X : Type w)) 0).toAddMonoidHom

/-- The degree-zero component of a degree-zero section is that section. -/
@[simp]
lemma degreeZeroComponent_incl_self (X : Cᵒᵖ) (x : (P 0).obj X) :
    A.degreeZeroComponent X (A.incl 0 x) = x := by
  change DirectSum.component (R.obj X) ℤ (fun i => ((P i).obj X : Type w)) 0
    (DirectSum.of (fun i => ((P i).obj X : Type w)) 0 x) = x
  rw [← DirectSum.lof_eq_of (R.obj X), DirectSum.component.of]
  simp

/-- The degree-zero component of a homogeneous section of nonzero degree vanishes. -/
@[simp]
lemma degreeZeroComponent_incl_of_ne {i : ℤ} (hi : i ≠ 0) (X : Cᵒᵖ) (x : (P i).obj X) :
    A.degreeZeroComponent X (A.incl i x) = 0 := by
  change DirectSum.component (R.obj X) ℤ (fun i => ((P i).obj X : Type w)) 0
    (DirectSum.of (fun i => ((P i).obj X : Type w)) i x) = 0
  rw [← DirectSum.lof_eq_of (R.obj X), DirectSum.component.of, dite_eq_right_iff.mpr]
  intro h
  exact absurd h hi

/-- The degree-zero component commutes with restriction. -/
lemma degreeZeroComponent_totalRestrict {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : A.Total X) :
    A.degreeZeroComponent Y (A.totalRestrict f a) =
      sectionRestrict (P 0) f (A.degreeZeroComponent X a) := by
  induction a using A.incl_induction with
  | zero => simp
  | incl i y =>
    rcases eq_or_ne i 0 with rfl | hi
    · rw [A.totalRestrict_incl, A.degreeZeroComponent_incl_self,
        A.degreeZeroComponent_incl_self]
    · rw [A.totalRestrict_incl, A.degreeZeroComponent_incl_of_ne hi,
        A.degreeZeroComponent_incl_of_ne hi, map_zero]
  | add a a' ha ha' => simp only [map_add, ha, ha']

/-! ### The degree-zero augmentation

A `ℤ`-graded algebra concentrated in nonnegative degrees has a degree-zero projection, and that
projection is multiplicative because a product of homogeneous sections of degrees summing to `0`
has a vanishing factor unless both degrees are `0`. -/

variable (ε : ∀ X : Cᵒᵖ, ((P 0).obj X : Type w) →+ R.obj X)
  (hzero : ∀ i : ℤ, i < 0 → ∀ (X : Cᵒᵖ) (x : (P i).obj X), x = 0)
  (hone : ∀ X : Cᵒᵖ, ε X (A.one.eval X) = 1)
  (hmul : ∀ (X : Cᵒᵖ) (x y : (P 0).obj X), ε X ((A.mul 0 0).app X x y) = ε X x * ε X y)

include hzero hmul in
/-- Multiplicativity of the degree-zero augmentation on homogeneous local sections. -/
private lemma augmentation_mul_incl (X : Cᵒᵖ) (i j : ℤ) (x : (P i).obj X) (y : (P j).obj X) :
    ε X (A.degreeZeroComponent X (A.incl i x * A.incl j y)) =
      ε X (A.degreeZeroComponent X (A.incl i x)) *
        ε X (A.degreeZeroComponent X (A.incl j y)) := by
  have hvanish : x = 0 ∨ y = 0 →
      ε X (A.degreeZeroComponent X (A.incl i x * A.incl j y)) =
        ε X (A.degreeZeroComponent X (A.incl i x)) *
          ε X (A.degreeZeroComponent X (A.incl j y)) := by
    rintro (rfl | rfl) <;> simp
  by_cases hij : i + j = 0
  · rcases lt_trichotomy i 0 with hi | hi | hi
    · exact hvanish (Or.inl (hzero i hi X x))
    · have hj : j = 0 := by omega
      subst hi
      subst hj
      have key : A.incl 0 x * A.incl 0 y = A.incl 0 ((A.mul 0 0).app X x y) :=
        A.incl_mul_incl 0 0 x y
      rw [key, A.degreeZeroComponent_incl_self, A.degreeZeroComponent_incl_self,
        A.degreeZeroComponent_incl_self, hmul]
    · exact hvanish (Or.inr (hzero j (by omega) X y))
  · rw [A.incl_mul_incl, A.degreeZeroComponent_incl_of_ne hij, map_zero]
    rcases (by omega : i ≠ 0 ∨ j ≠ 0) with hi | hj
    · rw [A.degreeZeroComponent_incl_of_ne hi, map_zero, zero_mul]
    · rw [A.degreeZeroComponent_incl_of_ne hj, map_zero, mul_zero]

include hzero hone hmul in
/-- **The degree-zero augmentation of the ungraded realization of a `ℤ`-graded algebra
concentrated in nonnegative degrees**: the ring homomorphism to the base ring given by the
degree-zero component, killing all positive degrees. -/
def augmentation (X : Cᵒᵖ) : A.Total X →+* R.obj X where
  toFun a := ε X (A.degreeZeroComponent X a)
  map_one' := by rw [A.one_eq_incl, A.degreeZeroComponent_incl_self, hone]
  map_zero' := by rw [map_zero, map_zero]
  map_add' a b := by rw [map_add, map_add]
  map_mul' a b := by
    induction a using A.incl_induction with
    | zero => rw [zero_mul]; simp
    | incl i x =>
      induction b using A.incl_induction with
      | zero => rw [mul_zero]; simp
      | incl j y => exact augmentation_mul_incl A ε hzero hmul X i j x y
      | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
    | add a a' ha ha' => simp only [add_mul, map_add, ha, ha']

/-- The degree-zero augmentation applies `ε` to the degree-zero component. -/
@[simp]
lemma augmentation_apply (X : Cᵒᵖ) (a : A.Total X) :
    A.augmentation ε hzero hone hmul X a = ε X (A.degreeZeroComponent X a) := rfl

variable (hsmul : ∀ (X : Cᵒᵖ) (r : R.obj X) (x : (P 0).obj X), ε X (r • x) = r * ε X x)
  (hnat : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (P 0).obj X),
    ε Y (sectionRestrict (P 0) f x) = R.map f (ε X x))

include hone hsmul in
/-- **The degree-zero augmentation is a retraction of the structure map `r ↦ r • 1`.** -/
lemma augmentation_structureMap (X : Cᵒᵖ) (r : R.obj X) :
    ε X (A.degreeZeroComponent X (A.structureMap X r)) = r := by
  have h : A.structureMap X r = A.incl 0 (r • A.one.eval X) := by
    rw [A.incl_smul, ← A.one_eq_incl]
    rfl
  rw [h, A.degreeZeroComponent_incl_self, hsmul, hone, _root_.mul_one]

include hnat in
/-- The degree-zero augmentation commutes with restriction. -/
lemma augmentation_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : A.Total X) :
    ε Y (A.degreeZeroComponent Y (A.totalRestrict f a)) =
      R.map f (ε X (A.degreeZeroComponent X a)) := by
  rw [A.degreeZeroComponent_totalRestrict, hnat]

end Stacks.GradedAlgebra

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Q : ℤ → PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
  (B : GradedAlgebra Q)
  (hcomm : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (Q i).obj X) (y : (Q j).obj X),
    HEq ((B.mul i j).app X x y) ((B.mul j i).app X y x))
  (ε : ∀ X : Cᵒᵖ, ((Q 0).obj X : Type w) →+ (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X)
  (hzero : ∀ i : ℤ, i < 0 → ∀ (X : Cᵒᵖ) (x : (Q i).obj X), x = 0)
  (hone : ∀ X : Cᵒᵖ, ε X (B.one.eval X) = 1)
  (hmul : ∀ (X : Cᵒᵖ) (x y : (Q 0).obj X), ε X ((B.mul 0 0).app X x y) = ε X x * ε X y)
  (hsmul : ∀ (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X)
    (x : (Q 0).obj X), ε X (r • x) = r * ε X x)
  (hnat : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (Q 0).obj X),
    ε Y (sectionRestrict (Q 0) f x) = (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).map f (ε X x))

include hzero hone hmul hnat in
/-- **The degree-zero augmentation of the ungraded realization, as a morphism of presheaves of
commutative rings** onto the base. -/
def totalCommAugmentation : B.totalCommPresheaf hcomm ⟶ O where
  app X := @CommRingCat.ofHom _ _ (B.commRingTotal hcomm X) _
    (B.augmentation ε hzero hone hmul X)
  naturality X Y f := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    exact B.augmentation_naturality ε hnat f a

include hsmul in
/-- **The degree-zero augmentation retracts the structure map of the ungraded realization**: the
composite `𝒪 ⟶ Total ⟶ 𝒪` is the identity. -/
lemma totalCommStructureMap_comp_totalCommAugmentation :
    B.totalCommStructureMap hcomm ≫ B.totalCommAugmentation hcomm ε hzero hone hmul hnat =
      𝟙 O := by
  refine NatTrans.ext (funext fun X => CommRingCat.hom_ext (RingHom.ext fun r => ?_))
  exact B.augmentation_structureMap ε hone hsmul X r

end Stacks.GradedAlgebra

namespace Stacks.RelativeSpec

variable {X : Scheme.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))
  (e : A.piece 0 ≅ SheafOfModules.unit X.ringCatSheaf)

/-- The degree-zero identification of a sheaf of graded algebras on a scheme, as an additive map
on local sections with the ring of sections of the structure sheaf as target. -/
def pieceZeroAugmentation (U : (Opens X)ᵒᵖ) :
    ((A.piece 0).val.obj U : Type u) →+ X.ringCatSheaf.obj.obj U :=
  AddMonoidHom.mk' (fun x => e.hom.val.app U x) (fun x y => map_add _ x y)

variable {A e}

/-- `Stacks.RelativeSpec.pieceZeroAugmentation` evaluates the degree-zero identification. -/
@[simp]
lemma pieceZeroAugmentation_apply (U : (Opens X)ᵒᵖ) (x : (A.piece 0).val.obj U) :
    pieceZeroAugmentation A e U x = e.hom.val.app U x := rfl

/-- The degree-zero identification is linear over the ring of sections. -/
lemma pieceZeroAugmentation_smul (U : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj U)
    (x : (A.piece 0).val.obj U) :
    pieceZeroAugmentation A e U (r • x) = r * pieceZeroAugmentation A e U x := by
  rw [pieceZeroAugmentation_apply, pieceZeroAugmentation_apply, map_smul]
  rfl

/-- The degree-zero identification commutes with restriction. -/
lemma pieceZeroAugmentation_naturality {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (x : (A.piece 0).val.obj U) :
    pieceZeroAugmentation A e V (Stacks.sectionRestrict (A.piece 0).val f x) =
      X.ringCatSheaf.obj.map f (pieceZeroAugmentation A e U x) := by
  change e.hom.val.app V ((A.piece 0).val.map f x) =
    (SheafOfModules.unit X.ringCatSheaf).val.map f (e.hom.val.app U x)
  exact PresheafOfModules.naturality_apply e.hom.val f x

/-- The hypothesis that the degree-zero identification carries the algebra unit to `1`. -/
abbrev PieceZeroUnit (e : A.piece 0 ≅ SheafOfModules.unit X.ringCatSheaf) : Prop :=
  ∀ U : (Opens X)ᵒᵖ, e.hom.val.app U (A.one.eval U) = (1 : X.ringCatSheaf.obj.obj U)

/-- Under `Stacks.RelativeSpec.PieceZeroUnit`, the degree-zero identification carries the
algebra unit to `1`. -/
lemma pieceZeroAugmentation_one (he : PieceZeroUnit e) (U : (Opens X)ᵒᵖ) :
    pieceZeroAugmentation A e U (A.one.eval U) = 1 := he U

/-- **The degree-zero identification of a sheaf of graded algebras is multiplicative**: degree
zero is free of rank one on the algebra unit, so a product of degree-zero local sections is the
product of their scalars times the unit. -/
lemma pieceZeroAugmentation_mul (he : PieceZeroUnit e) (U : (Opens X)ᵒᵖ)
    (x y : (A.piece 0).val.obj U) :
    pieceZeroAugmentation A e U ((A.mul 0 0).app U x y) =
      pieceZeroAugmentation A e U x * pieceZeroAugmentation A e U y := by
  have hsmul_one : ∀ z : (A.piece 0).val.obj U,
      pieceZeroAugmentation A e U z • A.one.eval U = z := fun z =>
    SheafOfModules.GradedAlgebra.eq_smul_one_of_isoUnit A e he U z _ rfl
  conv_lhs => rw [← hsmul_one x, ← hsmul_one y]
  rw [(A.mul 0 0).map_smul_left, (A.mul 0 0).map_smul_right,
    eq_of_heq (A.one_mul 0 U (A.one.eval U)), smul_smul, pieceZeroAugmentation_smul,
    pieceZeroAugmentation_one he, _root_.mul_one]

variable (A e)

/-- **The degree-zero augmentation of the ungraded realization of a sheaf of graded algebras
concentrated in nonnegative degrees**, as a morphism of presheaves of commutative rings onto the
structure sheaf of the base. -/
def ungradedCommAugmentation (he : PieceZeroUnit e) (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) :
    ungradedCommPresheaf X A hA ⟶ X.sheaf.obj :=
  A.toPresheafGradedAlgebra.totalCommAugmentation hA (pieceZeroAugmentation A e)
    (fun n hn U x => (Stacks.subsingleton_of_isZero (hzero n hn) U).elim x 0)
    (pieceZeroAugmentation_one he) (pieceZeroAugmentation_mul he)
    (fun f x => pieceZeroAugmentation_naturality f x)

/-- The degree-zero augmentation of the ungraded realization retracts its structure map. -/
lemma ungradedCommStructureMap_comp_ungradedCommAugmentation (he : PieceZeroUnit e)
    (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) :
    ungradedCommStructureMap X A hA ≫ ungradedCommAugmentation A hA e he hzero =
      𝟙 X.sheaf.obj :=
  A.toPresheafGradedAlgebra.totalCommStructureMap_comp_totalCommAugmentation hA
    (pieceZeroAugmentation A e)
    (fun n hn U x => (Stacks.subsingleton_of_isZero (hzero n hn) U).elim x 0)
    (pieceZeroAugmentation_one he) (pieceZeroAugmentation_mul he)
    (fun U r x => pieceZeroAugmentation_smul U r x)
    (fun f x => pieceZeroAugmentation_naturality f x)

/-- **The degree-zero augmentation of the ungraded algebra sheaf**, as a morphism of sheaves of
commutative rings onto the structure sheaf of the base. -/
def algebraSheafAugmentation (he : PieceZeroUnit e)
    (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) :
    (ungradedAlgebraSheaf X A hA).right ⟶ X.sheaf :=
  ((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
    CommRingCat.{u}).homEquiv (ungradedCommPresheaf X A hA) X.sheaf).symm
      (ungradedCommAugmentation A hA e he hzero)

/-- **The degree-zero augmentation of the ungraded algebra sheaf retracts its structure
morphism.** -/
lemma structureMap_comp_algebraSheafAugmentation (he : PieceZeroUnit e)
    (hzero : ∀ n : ℤ, n < 0 → IsZero (A.piece n)) :
    (ungradedAlgebraSheaf X A hA).hom.hom ≫
        (algebraSheafAugmentation A hA e he hzero).hom = 𝟙 X.sheaf.obj := by
  have hunit : (sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
        CommRingCat.{u}).unit.app (ungradedCommPresheaf X A hA) ≫
      (algebraSheafAugmentation A hA e he hzero).hom =
        ungradedCommAugmentation A hA e he hzero :=
    ((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
      CommRingCat.{u}).homEquiv (ungradedCommPresheaf X A hA) X.sheaf).apply_symm_apply _
  calc (ungradedAlgebraSheaf X A hA).hom.hom ≫
        (algebraSheafAugmentation A hA e he hzero).hom
      = ungradedCommStructureMap X A hA ≫
          ((sheafificationAdjunction (Opens.grothendieckTopology (X : TopCat))
            CommRingCat.{u}).unit.app (ungradedCommPresheaf X A hA) ≫
              (algebraSheafAugmentation A hA e he hzero).hom) := Category.assoc _ _ _
    _ = ungradedCommStructureMap X A hA ≫ ungradedCommAugmentation A hA e he hzero := by
        rw [hunit]
    _ = 𝟙 X.sheaf.obj :=
        ungradedCommStructureMap_comp_ungradedCommAugmentation A hA e he hzero

/-! ### Sections of the relative spectrum -/

variable (s : RelativeSpecSituation.{u}) (ρ : s.algebra.right.obj ⟶ s.base.presheaf)
  (hρ : s.algebra.hom.hom ≫ ρ = 𝟙 s.base.presheaf)

/-- The relative-spectrum pair over the base attached to a retraction of the structure map of the
algebra: the identity of the base together with the retraction. -/
def retractionPair : RelativeSpecPair s s.base :=
  ⟨𝟙 s.base, Under.homMk ρ hρ⟩

/-- **The section of the relative spectrum attached to a retraction of the structure map of the
algebra.** -/
def retractionSection : s.base ⟶ (gluedSpectrum s).scheme :=
  pairToHom (retractionPair s ρ hρ)

/-- **Over an affine open of the base, the section attached to a retraction of the structure map
of the algebra is the spectrum of that retraction on sections**, read in the chart of the open. -/
theorem ι_retractionSection (U : s.base.affineOpens) :
    U.1.ι ≫ retractionSection s ρ hρ =
      U.1.toSpecΓ ≫ Spec.map (ρ.app (op U.1)) ≫ (gluedSpectrum s).chart U :=
  ι_pairToHom (retractionPair s ρ hρ) U

include hρ in
/-- A retraction of the structure map of the algebra is surjective on sections over every open of
the base, the structure map being a section of it. -/
theorem rightInverse_retraction_app (U : (Opens s.base)ᵒᵖ)
    (y : s.base.presheaf.obj U) : ρ.app U (s.algebra.hom.hom.app U y) = y :=
  congrFun (congrArg (fun k : s.base.presheaf.obj U ⟶ s.base.presheaf.obj U =>
    (ConcreteCategory.hom k : s.base.presheaf.obj U → s.base.presheaf.obj U))
      (NatTrans.congr_app hρ U)) y

/-- The section attached to a retraction of the structure map splits the structure morphism of
the relative spectrum. -/
theorem retractionSection_comp_toBase :
    retractionSection s ρ hρ ≫ (gluedSpectrum s).toBase = 𝟙 s.base :=
  pairToHom_toBase (retractionPair s ρ hρ)

/-- **The section of the relative spectrum attached to a retraction of the structure map is a
closed immersion**, being a section of an affine, hence separated, morphism. -/
instance isClosedImmersion_retractionSection :
    IsClosedImmersion (retractionSection s ρ hρ) := by
  have h : IsClosedImmersion (retractionSection s ρ hρ ≫ (gluedSpectrum s).toBase) := by
    rw [retractionSection_comp_toBase]
    infer_instance
  exact IsClosedImmersion.of_comp (retractionSection s ρ hρ) (gluedSpectrum s).toBase

/-- **The open complement of the section of the relative spectrum attached to a retraction of the
structure map of the algebra.** -/
def retractionComplement : (gluedSpectrum s).scheme.Opens where
  carrier := (Set.range (retractionSection s ρ hρ).base)ᶜ
  is_open' := (retractionSection s ρ hρ).isClosedEmbedding.isClosed_range.isOpen_compl

end Stacks.RelativeSpec

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf)

/-- **The degree-zero identification of the symmetric algebra of a module sheaf on a scheme
carries the algebra unit to `1`.** -/
theorem symmetricAlgebraPieceZeroIso_hom_one (U : (Opens X)ᵒᵖ) :
    (symmetricAlgebraPieceZeroIso X F).hom.val.app U ((symmetricAlgebra X F).one.eval U) =
      (1 : X.ringCatSheaf.obj.obj U) :=
  @PresheafOfModules.symmetricAlgebraSheafifyPieceZeroIso_hom_one.{u, u, u} _ _ _ X.sheaf.obj
    X.ringCatSheaf (𝟙 X.ringCatSheaf.obj) (isLocallyInjective_id_ringCatSheaf X)
    (isLocallySurjective_id_ringCatSheaf X) inferInstance inferInstance F.val U

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **Degree zero of `Sym(L)` is the structure sheaf of the scheme on which `L` lives.** -/
def Situation.pieceZeroIso :
    D.symmetricAlgebra.piece 0 ≅ SheafOfModules.unit D.X.ringCatSheaf :=
  AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceZeroIso D.X D.L

/-- The degree-zero identification of `Sym(L)` carries the algebra unit to `1`. -/
theorem Situation.pieceZeroIso_hom_one (U : (Opens D.X)ᵒᵖ) :
    D.pieceZeroIso.hom.val.app U (D.symmetricAlgebra.one.eval U) =
      (1 : D.X.ringCatSheaf.obj.obj U) :=
  AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceZeroIso_hom_one D.X D.L U

/-- **The augmentation of the algebra sheaf of a line bundle**: the morphism of sheaves of
commutative `𝒪_X`-algebras `Sym(L) ⟶ 𝒪_X` which is the identity in degree zero and kills every
positive degree. -/
def Situation.algebraSheafAugmentation : D.algebraSheaf.right ⟶ D.X.sheaf :=
  Stacks.RelativeSpec.algebraSheafAugmentation D.symmetricAlgebra D.symmetricAlgebra_mul_comm
    D.pieceZeroIso D.pieceZeroIso_hom_one D.isZero_symmetricAlgebra_piece

/-- **The augmentation of the algebra sheaf of a line bundle retracts its structure
morphism**: the composite `𝒪_X ⟶ Sym(L) ⟶ 𝒪_X` is the identity. -/
theorem Situation.hom_comp_algebraSheafAugmentation :
    D.algebraSheaf.hom.hom ≫ D.algebraSheafAugmentation.hom = 𝟙 D.X.sheaf.obj :=
  Stacks.RelativeSpec.structureMap_comp_algebraSheafAugmentation D.symmetricAlgebra
    D.symmetricAlgebra_mul_comm D.pieceZeroIso D.pieceZeroIso_hom_one
    D.isZero_symmetricAlgebra_piece

/-- **The zero section of the total space of a line bundle**: the section of the structure
morphism cut out by the augmentation `Sym(L) ⟶ 𝒪_X`. -/
def Situation.zeroSection : D.X ⟶ D.totalSpace :=
  Stacks.RelativeSpec.retractionSection D.relativeSpecSituation
    D.algebraSheafAugmentation.hom D.hom_comp_algebraSheafAugmentation

/-- The zero section splits the structure morphism of the total space of a line bundle. -/
theorem Situation.zeroSection_comp_totalSpaceToBase :
    D.zeroSection ≫ D.totalSpaceToBase = 𝟙 D.X :=
  Stacks.RelativeSpec.retractionSection_comp_toBase D.relativeSpecSituation
    D.algebraSheafAugmentation.hom D.hom_comp_algebraSheafAugmentation

/-- **Over an affine open `U` of the base, the zero section of the total space of a line bundle
is the spectrum of the augmentation of `Sym(L)` on sections over `U`**, read in the chart of
`U`. -/
theorem Situation.ι_zeroSection (U : D.X.affineOpens) :
    U.1.ι ≫ D.zeroSection =
      U.1.toSpecΓ ≫ Spec.map (D.algebraSheafAugmentation.hom.app (op U.1)) ≫
        (Stacks.RelativeSpec.gluedSpectrum D.relativeSpecSituation).chart U :=
  Stacks.RelativeSpec.ι_retractionSection D.relativeSpecSituation
    D.algebraSheafAugmentation.hom D.hom_comp_algebraSheafAugmentation U

/-- **The zero section of the total space of a line bundle is a closed immersion.** -/
instance Situation.isClosedImmersion_zeroSection : IsClosedImmersion D.zeroSection :=
  Stacks.RelativeSpec.isClosedImmersion_retractionSection D.relativeSpecSituation
    D.algebraSheafAugmentation.hom D.hom_comp_algebraSheafAugmentation

/-- **The punctured total space of a line bundle**, as an open subset of the total space: the
complement of the zero section. -/
def Situation.puncturedOpen : D.totalSpace.Opens :=
  Stacks.RelativeSpec.retractionComplement D.relativeSpecSituation
    D.algebraSheafAugmentation.hom D.hom_comp_algebraSheafAugmentation

/-- **The punctured total space of a line bundle**: the total space with its zero section
deleted. -/
abbrev Situation.puncturedTotalSpace : Scheme.{u} := D.puncturedOpen.toScheme

/-- The projection of the punctured total space of a line bundle to the scheme on which the line
bundle lives. -/
def Situation.puncturedProjection : D.puncturedTotalSpace ⟶ D.X :=
  D.puncturedOpen.ι ≫ D.totalSpaceToBase

end Stacks.LineBundle

end
