module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# From a sheaf of graded algebras to a sheaf of commutative algebras over the structure sheaf

A sheaf of rings all of whose sections commute is a sheaf of commutative rings on the same
underlying presheaf of types. The ungraded realization
`SheafOfModules.GradedAlgebra.ungradedSheaf` of a sheaf of graded algebras with commutative
homogeneous multiplication is of that kind, and together with `ungradedStructureMap` it is a sheaf
of commutative algebras over the structure sheaf.

## Main definitions

* `Stacks.CommRingSheaf.ofRingCat`, `Stacks.CommRingSheaf.presheaf` and
  `Stacks.CommRingSheaf.sheaf`: a ring, a presheaf of rings and a sheaf of rings whose sections
  commute, read as a commutative ring, a presheaf of commutative rings and a sheaf of commutative
  rings.
* `Stacks.CommRingSheaf.homMk`: a morphism of sheaves of rings out of the underlying sheaf of
  rings of a sheaf of commutative rings, read as a morphism of sheaves of commutative rings.
* `SheafOfModules.GradedAlgebra.ungradedCommSheaf` and
  `SheafOfModules.GradedAlgebra.ungradedCommStructureMap`: the ungraded realization of a sheaf of
  graded algebras with commutative homogeneous multiplication, as a sheaf of commutative rings,
  together with its structure map.
* `Stacks.RelativeSpec.gradedAlgebraSheaf`: the same realization on a scheme, as a
  `Stacks.RelativeSpec.AlgebraSheaf`.

## Main results

* `Stacks.GradedAlgebra.mul_comm_total`: graded commutativity makes the ungraded realization of a
  graded algebra of presheaves of modules commutative over each object of the site.
* `SheafOfModules.GradedAlgebra.mul_comm_ungradedSheaf`: the same for the ungraded realization of
  a sheaf of graded algebras, as a sheaf of rings.
* `Stacks.CommRingSheaf.presheaf_comp_forget₂`: composing the lift to `CommRingCat` with the
  forgetful functor to `RingCat` returns the original presheaf of rings.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{u} R} (A : GradedAlgebra P)

/-- Two homogeneous local sections of equal degree which are heterogeneously equal have the same
image in the ungraded realization. -/
theorem incl_eq_incl_of_heq {W : Cᵒᵖ} {i j : ι} (hij : i = j) {x : (P i).obj W}
    {y : (P j).obj W} (hxy : HEq x y) : A.incl i x = A.incl j y := by
  subst hij
  rw [eq_of_heq hxy]

/-- **Graded commutativity makes the ungraded realization commutative**: if the graded
multiplication commutes in each pair of degrees, the multiplication of the direct sum of the
homogeneous components over an object of the site is commutative. -/
theorem mul_comm_total (hadd : ∀ i j : ι, i + j = j + i)
    (hc : ∀ (i j : ι) (W : Cᵒᵖ) (x : (P i).obj W) (y : (P j).obj W),
      HEq ((A.mul i j).app W x y) ((A.mul j i).app W y x))
    (W : Cᵒᵖ) (a b : A.Total W) : a * b = b * a := by
  induction a using A.incl_induction with
  | incl i x =>
    induction b using A.incl_induction with
    | incl j y =>
      rw [A.incl_mul_incl, A.incl_mul_incl]
      exact A.incl_eq_incl_of_heq (hadd i j) (hc i j W x y)
    | _ => simp_all [mul_add, add_mul]
  | _ => simp_all [mul_add, add_mul]

end Stacks.GradedAlgebra

namespace Stacks.CommRingSheaf

/-- The commutative ring structure on a ring whose elements commute. -/
@[instance_reducible]
def commRing (S : RingCat.{u}) (h : ∀ a b : S, a * b = b * a) : CommRing S :=
  { (inferInstance : Ring S) with mul_comm := h }

/-- A ring whose elements commute, as an object of the category of commutative rings. The carrier
and the ring operations are unchanged. -/
def ofRingCat (S : RingCat.{u}) (h : ∀ a b : S, a * b = b * a) : CommRingCat.{u} :=
  @CommRingCat.of S (commRing S h)

/-- A ring homomorphism between rings whose elements commute, as a morphism of commutative
rings. -/
def ofRingCatHom {S T : RingCat.{u}} (hS : ∀ a b : S, a * b = b * a)
    (hT : ∀ a b : T, a * b = b * a) (f : S ⟶ T) : ofRingCat S hS ⟶ ofRingCat T hT :=
  @CommRingCat.ofHom S T (commRing S hS) (commRing T hT) f.hom

variable {C : Type u} [Category.{u} C]

/-- A presheaf of rings whose sections commute, as a presheaf of commutative rings. -/
def presheaf (P : Cᵒᵖ ⥤ RingCat.{u})
    (h : ∀ (W : Cᵒᵖ) (a b : P.obj W), a * b = b * a) : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj W := ofRingCat (P.obj W) (h W)
  map {W W'} f := ofRingCatHom (h W) (h W') (P.map f)
  map_id W := by ext x; exact congrArg (fun g ↦ RingCat.Hom.hom g x) (P.map_id W)
  map_comp f g := by ext x; exact congrArg (fun g ↦ RingCat.Hom.hom g x) (P.map_comp f g)

/-- Forgetting commutativity in `presheaf P h` returns the presheaf of rings `P`. -/
theorem presheaf_comp_forget₂ (P : Cᵒᵖ ⥤ RingCat.{u})
    (h : ∀ (W : Cᵒᵖ) (a b : P.obj W), a * b = b * a) :
    presheaf P h ⋙ forget₂ CommRingCat.{u} RingCat.{u} = P :=
  rfl

/-- A presheaf of rings whose sections commute is a sheaf of commutative rings as soon as it is a
sheaf of rings. -/
theorem isSheaf_presheaf (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ RingCat.{u})
    (h : ∀ (W : Cᵒᵖ) (a b : P.obj W), a * b = b * a) (hP : Presheaf.IsSheaf J P) :
    Presheaf.IsSheaf J (presheaf P h) :=
  (Presheaf.isSheaf_iff_isSheaf_forget J (presheaf P h) (forget CommRingCat.{u})).2
    ((Presheaf.isSheaf_iff_isSheaf_forget J P (forget RingCat.{u})).1 hP)

variable {J : GrothendieckTopology C}

/-- **A sheaf of rings whose sections commute, as a sheaf of commutative rings.** -/
def sheaf (S : Sheaf J RingCat.{u})
    (h : ∀ (W : Cᵒᵖ) (a b : S.obj.obj W), a * b = b * a) : Sheaf J CommRingCat.{u} :=
  ⟨presheaf S.obj h, isSheaf_presheaf J S.obj h S.property⟩

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- A morphism of sheaves of rings out of the underlying sheaf of rings of a sheaf of commutative
rings, read as a morphism of sheaves of commutative rings into the lift of its target. -/
def homMk (O : Sheaf J CommRingCat.{u}) {S : Sheaf J RingCat.{u}}
    (h : ∀ (W : Cᵒᵖ) (a b : S.obj.obj W), a * b = b * a)
    (f : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O ⟶ S) :
    O ⟶ sheaf S h :=
  ObjectProperty.homMk
    { app := fun W ↦
        @CommRingCat.ofHom (O.obj.obj W) (S.obj.obj W) inferInstance
          (commRing (S.obj.obj W) (h W)) (f.hom.app W).hom
      naturality := fun W W' g ↦ by
        ext x
        exact congrArg (fun φ ↦ RingCat.Hom.hom φ x) (f.hom.naturality g) }

end Stacks.CommRingSheaf

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]

/-- **The ungraded realization of a sheaf of graded algebras with commutative homogeneous
multiplication has commuting sections.** -/
theorem mul_comm_ungradedSheaf (A : GradedAlgebra.{u, u} R)
    (hc : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (W : Cᵒᵖ) (s t : A.ungradedSheaf.obj.obj W) : s * t = t * s :=
  A.toPresheafGradedAlgebra.mul_comm_totalSheaf J
    (A.toPresheafGradedAlgebra.mul_comm_total add_comm hc) W s t

/-- **The ungraded realization of a sheaf of graded algebras with commutative homogeneous
multiplication, as a sheaf of commutative rings.** -/
def ungradedCommSheaf (A : GradedAlgebra.{u, u} R)
    (hc : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a)) :
    Sheaf J CommRingCat.{u} :=
  Stacks.CommRingSheaf.sheaf A.ungradedSheaf (A.mul_comm_ungradedSheaf hc)

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **The structure map of the ungraded realization, as a morphism of sheaves of commutative
rings** out of the sheaf of commutative rings the graded algebra is an algebra over. -/
def ungradedCommStructureMap {O : Sheaf J CommRingCat.{u}}
    (A : GradedAlgebra.{u, u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))
    (hc : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a)) :
    O ⟶ A.ungradedCommSheaf hc :=
  Stacks.CommRingSheaf.homMk O (A.mul_comm_ungradedSheaf hc) A.ungradedStructureMap

end SheafOfModules.GradedAlgebra

namespace Stacks.RelativeSpec

open _root_.AlgebraicGeometry

/-- **A sheaf of graded algebras on a scheme with commutative homogeneous multiplication, as a
sheaf of commutative algebras over the structure sheaf.** Its sheaf of rings is the ungraded
realization `SheafOfModules.GradedAlgebra.ungradedSheaf` and its structure morphism is
`SheafOfModules.GradedAlgebra.ungradedStructureMap`. -/
def gradedAlgebraSheaf (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a)) :
    AlgebraSheaf X :=
  Under.mk (A.ungradedCommStructureMap hc)

/-- The sheaf of rings of `Stacks.RelativeSpec.gradedAlgebraSheaf` is the ungraded realization
`SheafOfModules.GradedAlgebra.ungradedSheaf`. -/
theorem ringSheaf_gradedAlgebraSheaf (X : Scheme.{u})
    (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a)) :
    AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X A hc) = A.ungradedSheaf :=
  rfl

end Stacks.RelativeSpec

end
