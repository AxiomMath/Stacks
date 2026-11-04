module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Adic fibres of an algebraic space over an affine base

Let `A` be a ring and `I ⊆ A` an ideal. The positive-order infinitesimal thickenings
`Spec (A / I ^ (n + 1))` of `AlgebraicGeometry.adicThickening` are schemes over `Spec A`, so
once a big fppf site contains both `Spec A` and every thickening they become objects of the
big fppf category over `Spec A`, and the Yoneda presheaves they represent are algebraic
spaces over `Spec A`. The *adic fibres* of an algebraic space over `Spec A` are its base
changes along those objects. They form an inverse system, and a morphism of algebraic spaces
over `Spec A` induces a morphism of the two inverse systems.

This is the vocabulary in which the formal algebraization theorems for algebraic spaces are
stated: the system of adic fibres is the formal completion of the space along the closed
subspace cut out by `I`, and algebraization asks for an actual morphism, closed subspace or
scheme inducing a prescribed compatible system of adic fibres.

## Main definitions

* `AlgebraicGeometry.Space.baseObject` is `Spec A` viewed as the terminal object of the big
  fppf category over itself.
* `AlgebraicGeometry.Space.adicThickeningObject` is the `n`-th thickening viewed as an object
  of the big fppf category over `Spec A`, with structure morphism
  `AlgebraicGeometry.Space.adicThickeningMap` to `baseObject` and transition morphism
  `AlgebraicGeometry.Space.adicThickeningSuccMap` into the next thickening.
* `AlgebraicGeometry.Space.adicFibre` is the base change of a presheaf over `baseObject`
  along `adicThickeningMap`, with transition morphism
  `AlgebraicGeometry.Space.adicFibreSucc`.
* `AlgebraicGeometry.Space.adicFibreMap` is the base change of a morphism over `baseObject`.

## Main results

* `AlgebraicGeometry.Space.adicThickeningSuccMap_adicThickeningMap`: the transition
  morphisms between thickenings are morphisms over `Spec A`.
* `AlgebraicGeometry.Space.isPullback_adicFibreSucc`: consecutive adic fibres form cartesian
  squares over the thickenings, so the adic fibres of a presheaf are a cartesian tower.
* `AlgebraicGeometry.Space.adicFibreMap_snd` and
  `AlgebraicGeometry.Space.adicFibreSucc_adicFibreMap`: the adic fibres of a morphism over
  `baseObject` are morphisms over the thickenings and are compatible with the transition
  morphisms. Together these say that the adic fibres of a morphism form a *compatible
  system* in the sense the algebraization theorems use, so that those theorems ask for a
  preimage of a genuine map rather than for an unconstrained one.
* `AlgebraicGeometry.Space.adicFibreMap_id` and
  `AlgebraicGeometry.Space.adicFibreMap_comp`: taking adic fibres is functorial.

## Implementation notes

Positive powers are indexed by natural numbers, with index `n` denoting the quotient by
`I ^ (n + 1)`, as in `StacksFrontier/AlgebraicGeometry/Algebraization.lean`.

Membership of the thickenings in the chosen big fppf site is a hypothesis `hSn`, because
`AlgebraicGeometry.BigFppfSite.Contains` is a size condition that no geometric hypothesis
supplies. It is only needed to regard the thickenings as objects of the site, hence to form
their Yoneda presheaves; it is not a restriction on `A` or `I`.

The adic fibre is the presheaf pullback `CategoryTheory.Limits.pullback`, as elsewhere in
the algebraic-space layer: fibre products of algebraic spaces are computed as presheaf
pullbacks and are again algebraic spaces by
`AlgebraicGeometry.isAlgebraicSpace_pullback`. The definitions here therefore apply to an
arbitrary presheaf over `baseObject` and do not take an algebraicity hypothesis; a client
proving something about algebraic spaces supplies it separately.

`AlgebraicGeometry.Space.baseObject` is an abbreviation for `Over.mk (𝟙 (B.obj hS))`, so it
is interchangeable with that term by `rfl` and a client may write either.

## References

* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A))) (hSn : ∀ n, B.Contains (adicThickening A I n))

/-! ### The thickenings as objects of the big fppf category over the base -/

/-- The affine base, viewed as the terminal object of the big fppf category over itself. -/
abbrev baseObject : BigFppfOver B (Spec (.of A)) hS := Over.mk (𝟙 (B.obj hS))

/-- The `n`-th positive-order adic thickening of the base, viewed as an object of the big
fppf category over the base. -/
def adicThickeningObject (n : ℕ) : BigFppfOver B (Spec (.of A)) hS :=
  Over.mk (ObjectProperty.homMk (adicThickeningι A I n) : B.obj (hSn n) ⟶ B.obj hS)

/-- The structure morphism of an adic thickening to the base, in the big fppf category over
the base. -/
def adicThickeningMap (n : ℕ) :
    adicThickeningObject A I B hS hSn n ⟶ baseObject A B hS :=
  Over.homMk (ObjectProperty.homMk (adicThickeningι A I n) : B.obj (hSn n) ⟶ B.obj hS)

/-- The canonical morphism from one adic thickening to the next, in the big fppf category
over the base. -/
def adicThickeningSuccMap (n : ℕ) :
    adicThickeningObject A I B hS hSn n ⟶ adicThickeningObject A I B hS hSn (n + 1) :=
  Over.homMk (ObjectProperty.homMk (adicThickeningSucc A I n) :
    B.obj (hSn n) ⟶ B.obj (hSn (n + 1))) (ObjectProperty.hom_ext _ (adicThickeningSucc_ι A I n))

/-- The transition morphisms between consecutive adic thickenings are morphisms over the
base. -/
@[reassoc (attr := simp)]
lemma adicThickeningSuccMap_adicThickeningMap (n : ℕ) :
    adicThickeningSuccMap A I B hS hSn n ≫ adicThickeningMap A I B hS hSn (n + 1) =
      adicThickeningMap A I B hS hSn n := by
  ext
  exact adicThickeningSucc_ι A I n

/-! ### Adic fibres of a presheaf over the base -/

variable {F G H : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}

/-- The `n`-th adic fibre of a presheaf over the base: its base change along the `n`-th
adic thickening. -/
abbrev adicFibre (f : F ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :=
  pullback f (yoneda.map (adicThickeningMap A I B hS hSn n))

/-- Every adic fibre of an algebraic space over the base is again an algebraic space over
the base. -/
theorem isAlgebraicSpace_adicFibre (hF : IsAlgebraicSpace B (Spec (.of A)) hS F)
    (f : F ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    IsAlgebraicSpace B (Spec (.of A)) hS (adicFibre A I B hS hSn f n) :=
  isAlgebraicSpace_pullback B (Spec (.of A)) hS f
    (yoneda.map (adicThickeningMap A I B hS hSn n)) hF
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hS (adicThickeningObject A I B hS hSn n))
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hS (baseObject A B hS))

/-- The canonical morphism from one adic fibre of a presheaf into the next. -/
def adicFibreSucc (f : F ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    adicFibre A I B hS hSn f n ⟶ adicFibre A I B hS hSn f (n + 1) :=
  pullback.lift
    (pullback.fst f (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (pullback.snd f (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫
      yoneda.map (adicThickeningSuccMap A I B hS hSn n)) (by
      rw [Category.assoc, ← yoneda.map_comp,
        adicThickeningSuccMap_adicThickeningMap]
      exact pullback.condition)

/-- The transition morphism between adic fibres commutes with the projections to the
presheaf. -/
@[reassoc (attr := simp)]
lemma adicFibreSucc_fst (f : F ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    adicFibreSucc A I B hS hSn f n ≫
        pullback.fst f (yoneda.map (adicThickeningMap A I B hS hSn (n + 1))) =
      pullback.fst f (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
  pullback.lift_fst _ _ _

/-- The transition morphism between adic fibres lies over the transition morphism between the
adic thickenings. -/
@[reassoc (attr := simp)]
lemma adicFibreSucc_snd (f : F ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    adicFibreSucc A I B hS hSn f n ≫
        pullback.snd f (yoneda.map (adicThickeningMap A I B hS hSn (n + 1))) =
      pullback.snd f (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫
        yoneda.map (adicThickeningSuccMap A I B hS hSn n) :=
  pullback.lift_snd _ _ _

/-- Consecutive adic fibres of a presheaf over `Spec A` form a cartesian square over the
thickenings: `F_n = F_{n + 1} ×_{S_{n + 1}} S_n`. -/
theorem isPullback_adicFibreSucc (f : F ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    IsPullback (adicFibreSucc A I B hS hSn f n)
      (pullback.snd f (yoneda.map (adicThickeningMap A I B hS hSn n)))
      (pullback.snd f (yoneda.map (adicThickeningMap A I B hS hSn (n + 1))))
      (yoneda.map (adicThickeningSuccMap A I B hS hSn n)) := by
  refine IsPullback.of_right ?_ (adicFibreSucc_snd A I B hS hSn f n)
    (IsPullback.of_hasPullback f (yoneda.map (adicThickeningMap A I B hS hSn (n + 1))))
  rw [adicFibreSucc_fst, ← yoneda.map_comp, adicThickeningSuccMap_adicThickeningMap]
  exact IsPullback.of_hasPullback f _

/-- The `n`-th adic fibre of a morphism over the base. -/
def adicFibreMap {fF : F ⟶ yoneda.obj (baseObject A B hS)}
    {fG : G ⟶ yoneda.obj (baseObject A B hS)} (g : F ⟶ G) (hg : g ≫ fG = fF) (n : ℕ) :
    adicFibre A I B hS hSn fF n ⟶ adicFibre A I B hS hSn fG n :=
  pullback.lift
    (pullback.fst fF (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ g)
    (pullback.snd fF (yoneda.map (adicThickeningMap A I B hS hSn n))) (by
      rw [Category.assoc, hg]
      exact pullback.condition)

/-- The adic fibre of a morphism commutes with the projections to the presheaves. -/
@[reassoc (attr := simp)]
lemma adicFibreMap_fst {fF : F ⟶ yoneda.obj (baseObject A B hS)}
    {fG : G ⟶ yoneda.obj (baseObject A B hS)} (g : F ⟶ G) (hg : g ≫ fG = fF) (n : ℕ) :
    adicFibreMap A I B hS hSn g hg n ≫
        pullback.fst fG (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.fst fF (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ g :=
  pullback.lift_fst _ _ _

/-- The adic fibres of a morphism over the base are morphisms over the adic thickenings. -/
@[reassoc (attr := simp)]
lemma adicFibreMap_snd {fF : F ⟶ yoneda.obj (baseObject A B hS)}
    {fG : G ⟶ yoneda.obj (baseObject A B hS)} (g : F ⟶ G) (hg : g ≫ fG = fF) (n : ℕ) :
    adicFibreMap A I B hS hSn g hg n ≫
        pullback.snd fG (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fF (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
  pullback.lift_snd _ _ _

/-- Taking adic fibres preserves the identity. -/
@[simp]
lemma adicFibreMap_id (fF : F ⟶ yoneda.obj (baseObject A B hS)) (n : ℕ) :
    adicFibreMap A I B hS hSn (𝟙 F) (Category.id_comp fF) n =
      𝟙 (adicFibre A I B hS hSn fF n) := by
  apply pullback.hom_ext <;> simp

/-- Taking adic fibres preserves composition. -/
lemma adicFibreMap_comp {fF : F ⟶ yoneda.obj (baseObject A B hS)}
    {fG : G ⟶ yoneda.obj (baseObject A B hS)}
    {fH : H ⟶ yoneda.obj (baseObject A B hS)} (g : F ⟶ G) (hg : g ≫ fG = fF)
    (h : G ⟶ H) (hh : h ≫ fH = fG) (n : ℕ) :
    adicFibreMap A I B hS hSn (g ≫ h) (by rw [Category.assoc, hh, hg]) n =
      adicFibreMap A I B hS hSn g hg n ≫ adicFibreMap A I B hS hSn h hh n := by
  apply pullback.hom_ext <;> simp

/-- The adic fibres of a morphism over the base commute with the transition morphisms
between adic fibres. Together with `AlgebraicGeometry.Space.adicFibreMap_snd` this says that
the adic fibres of a morphism form a compatible system over the adic thickenings. -/
@[reassoc]
lemma adicFibreSucc_adicFibreMap {fF : F ⟶ yoneda.obj (baseObject A B hS)}
    {fG : G ⟶ yoneda.obj (baseObject A B hS)} (g : F ⟶ G) (hg : g ≫ fG = fF) (n : ℕ) :
    adicFibreSucc A I B hS hSn fF n ≫ adicFibreMap A I B hS hSn g hg (n + 1) =
      adicFibreMap A I B hS hSn g hg n ≫ adicFibreSucc A I B hS hSn fG n := by
  apply pullback.hom_ext <;> simp

end AlgebraicGeometry.Space

end
