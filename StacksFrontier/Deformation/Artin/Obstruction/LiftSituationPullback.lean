module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.TangentBaseChange

/-!
# Pullback of lift classes across a morphism of deformation situations

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`. Stacks 07YA
compares the lifts of an object `x` over `Spec A` with the lifts of its restriction `y` over
`Spec C` along a ring map `A ⟶ C`, and it does so over two kinds of base: the trivial
square-zero extensions `A[M]`, `C[N]`, where the comparison is the transition on tangent
modules, and a *deformation situation* `A' ⟶ A`, `C' ⟶ C`, where the comparison is the
compatibility with the action of Stacks 07Y9 (2)(b) on the lifts.

Before this file only the first kind was available: the pullback of lift classes of
`Deformation.Artin.squareZeroLiftBaseChangeMap` is tied to the morphism
`Spec C[N] ⟶ Spec A[M]` of *trivial* square-zero extensions attached to a map of coefficients,
because its construction asks for the square of square-zero immersions
`Spec C ⟶ Spec C[N]`, `Spec A ⟶ Spec A[M]`. Nothing of that construction uses the particular
shape of those arrows, and this file carries it out over an arbitrary commuting square of the
base.

## Main definitions

* `Deformation.Artin.underFiberPullback` — the pullback of a lift of `x` along an arbitrary
  commuting square of the base, as a lift of `y`, with its cartesian comparison arrow.
* `Deformation.Artin.underFiberClassPullback` — the induced map on isomorphism classes of
  lifts. It is well defined because the pullback of a lift class along a fixed arrow of the
  base is unique (`Deformation.Artin.underFiberClass_eq_of_cartesian`).
* `Deformation.Artin.deformationSituationPullback` — the same map read at a morphism of
  deformation situations `(y, C' ⟶ C) ⟶ (x, A' ⟶ A)`, which is the shape the second
  commuting square of Stacks 07YA needs.

## Main results

* `Deformation.Artin.exists_cartesian_underFiberClassPullback` — the defining property of the
  map on classes: some representative of the image carries a cartesian arrow over the fourth
  side of the square to some representative of the source, compatibly with `y ⟶ x`.
* `Deformation.Artin.eq_underFiberClassPullback_of_cartesian` — that property determines the
  map on classes.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

/-! ### An arrow out of `x` as a lift of `x` -/

section UnderFiberObj

open CategoryTheory.Functor

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X] (p : X ⥤ C)
  {U V : C} {x : X} (hx : p.obj x = U) (aa : U ⟶ V)

/-- **A bare arrow out of `x` lying over `aa` is a lift of `x` under `aa`.** The codomain lies
over `V` because the arrow does, and the structure arrow is the arrow itself. -/
public def underFiberObjMk {v : X} (m : x ⟶ v) (hm : p.IsHomLift aa m) :
    (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa)) := by
  have := hm
  refine ⟨Under.mk m, StructuredArrow.obj_ext _ _ (IsHomLift.codomain_eq p aa m) ?_⟩
  change p.map m ≫ eqToHom (IsHomLift.codomain_eq p aa m) = eqToHom hx ≫ aa
  rw [IsHomLift.fac' p aa m]
  simp

/-- The structure arrow of `underFiberObjMk p hx aa m hm` is `m`. -/
@[simp]
public theorem underFiberObjMk_hom {v : X} (m : x ⟶ v) (hm : p.IsHomLift aa m) :
    (underFiberObjMk p hx aa m hm).1.hom = m := rfl

/-- The object underlying `underFiberObjMk p hx aa m hm` is the codomain `v` of `m`. -/
@[simp]
public theorem underFiberObjMk_right {v : X} (m : x ⟶ v) (hm : p.IsHomLift aa m) :
    (underFiberObjMk p hx aa m hm).1.right = v := rfl

end UnderFiberObj

/-! ### Pullback of a lift along a commuting square of the base -/

section LiftSquarePullback

open CategoryTheory.Functor

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X] (p : X ⥤ C)
  (hp : p.IsFiberedInGroupoids) {U U' V V' : C} {aa : U ⟶ U'} {bb : V ⟶ U} {cc : V ⟶ V'}
  (D : V' ⟶ U') (hsq : bb ≫ aa = cc ≫ D)
  {x y : X} {hx : p.obj x = U} {hy : p.obj y = V} (φ : y ⟶ x) (hφ : p.IsHomLift bb φ)

include hp hsq hφ in
/-- The pullback of a lift of `x` under `aa : U ⟶ U'` along a commuting square
`bb ≫ aa = cc ≫ D` of the base, as a lift of `y` under `cc : V ⟶ V'`: the chosen strongly
cartesian pullback over `D`, whose structure arrow out of `y` is supplied by the universal
property applied to the composite `y ⟶ x ⟶ x'`.

This is `Deformation.Artin.squareZeroLiftBaseChange` with the two sides of the square
arbitrary arrows rather than square-zero immersions. -/
public def underFiberPullback (u : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))) :
    { v : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ cc)) //
      ∃ ρ : v.1.right ⟶ u.1.right,
        p.IsStronglyCartesian D ρ ∧ v.1.hom ≫ ρ = φ ≫ u.1.hom } := by
  letI : p.IsFibered := hp.isFibered
  have hau : p.IsHomLift aa u.1.hom := underFiber_isHomLift p hx aa u
  have hcomp : p.IsHomLift (cc ≫ D) (φ ≫ u.1.hom) := by
    rw [← hsq]
    exact isHomLift_comp p hφ hau
  have hfac : cc ≫ D = cc ≫ D := rfl
  let xu : p.Fiber U' := ⟨u.1.right, underFiber_right_obj p hx aa u⟩
  let ρ := (Functor.chosenPullbacks p).map D xu
  have hρ : p.IsStronglyCartesian D ρ := (Functor.chosenPullbacks p).isStronglyCartesian D xu
  have hhomlift : p.IsHomLift cc
      (Functor.IsStronglyCartesian.map p D ρ hfac (φ ≫ u.1.hom)) :=
    Functor.IsStronglyCartesian.map_isHomLift p D ρ hfac _
  refine ⟨⟨Under.mk (Functor.IsStronglyCartesian.map p D ρ hfac (φ ≫ u.1.hom)),
    StructuredArrow.obj_ext _ _ ((Functor.chosenPullbacks p).obj D xu).2 ?_⟩,
    ρ, hρ, Functor.IsStronglyCartesian.fac p D ρ hfac _⟩
  change p.map (Functor.IsStronglyCartesian.map p D ρ hfac (φ ≫ u.1.hom)) ≫
      eqToHom ((Functor.chosenPullbacks p).obj D xu).2 = eqToHom hy ≫ cc
  rw [IsHomLift.fac' p cc _, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

include hp hsq hφ in
/-- **The pullback of lift classes along a commuting square of the base.** The isomorphism
classes of lifts of `x` under `aa` are carried to the isomorphism classes of lifts of `y`
under `cc` by pullback over `D`. -/
public def underFiberClassPullback
    (a : Quotient (isIsomorphicSetoid ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))))) :
    Quotient (isIsomorphicSetoid ((Under.post p).Fiber (Under.mk (eqToHom hy ≫ cc)))) :=
  Quotient.lift (fun u => Quotient.mk _ (underFiberPullback p hp D hsq φ hφ u).1)
    (fun u₁ u₂ hu => underFiberClass_eq_of_cartesian p D φ (Quotient.sound hu)
      (underFiberPullback p hp D hsq φ hφ u₁).2.choose
      (underFiberPullback p hp D hsq φ hφ u₂).2.choose
      (underFiberPullback p hp D hsq φ hφ u₁).2.choose_spec.1
      (underFiberPullback p hp D hsq φ hφ u₂).2.choose_spec.1
      (underFiberPullback p hp D hsq φ hφ u₁).2.choose_spec.2
      (underFiberPullback p hp D hsq φ hφ u₂).2.choose_spec.2) a

include hp hsq hφ in
/-- **The defining property of the pullback of lift classes.** The image class has a
representative carrying a strongly cartesian arrow over `D` to a representative of the source
class, compatibly with `y ⟶ x`. -/
public theorem exists_cartesian_underFiberClassPullback
    (a : Quotient (isIsomorphicSetoid ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))))) :
    ∃ (u : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa)))
      (v : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ cc))),
      Quotient.mk _ u = a ∧
        Quotient.mk _ v = underFiberClassPullback p hp D hsq φ hφ a ∧
          ∃ ρ : v.1.right ⟶ u.1.right,
            p.IsStronglyCartesian D ρ ∧ v.1.hom ≫ ρ = φ ≫ u.1.hom := by
  induction a using Quotient.ind with
  | _ u =>
    exact ⟨u, (underFiberPullback p hp D hsq φ hφ u).1, rfl, rfl,
      (underFiberPullback p hp D hsq φ hφ u).2.choose,
      (underFiberPullback p hp D hsq φ hφ u).2.choose_spec.1,
      (underFiberPullback p hp D hsq φ hφ u).2.choose_spec.2⟩

include hp hsq hφ in
/-- **The defining property determines the pullback of lift classes.** A class of lifts of `y`
with a representative carrying a strongly cartesian arrow over `D` to a representative of `a`,
compatibly with `y ⟶ x`, is the pullback of `a`. -/
public theorem eq_underFiberClassPullback_of_cartesian
    {a : Quotient (isIsomorphicSetoid ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))))}
    {b : Quotient (isIsomorphicSetoid ((Under.post p).Fiber (Under.mk (eqToHom hy ≫ cc))))}
    (u : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa)))
    (v : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ cc)))
    (hu : Quotient.mk _ u = a) (hv : Quotient.mk _ v = b)
    (ρ : v.1.right ⟶ u.1.right) (hρ : p.IsStronglyCartesian D ρ)
    (hw : v.1.hom ≫ ρ = φ ≫ u.1.hom) :
    b = underFiberClassPullback p hp D hsq φ hφ a := by
  obtain ⟨u', v', hu', hv', ρ', hρ', hw'⟩ :=
    exists_cartesian_underFiberClassPullback p hp D hsq φ hφ a
  rw [← hv, ← hv']
  exact underFiberClass_eq_of_cartesian p D φ (hu.trans hu'.symm) ρ ρ' hρ hρ' hw hw'

/-- **Conjugation of an automorphism of a lift along a cartesian comparison arrow.** Let `v`
be a lift of `y` under `cc` carrying a strongly cartesian arrow `ρ` over `D` to a lift `u` of
`x` under `aa`, compatibly with `y ⟶ x`. Every automorphism `θ` of `u` has a unique
conjugate automorphism of `v`: the universal property of `ρ` produces the arrow of the
ambient category, and it is compatible with the structure arrow of `v` because `θ` is
compatible with that of `u`.

This is the construction behind the transition of Stacks 07YA on infinitesimal automorphisms;
`Deformation.Artin.IsInfinitesimalAutomorphismBaseChange` is its defining property read at the
trivial lifts. -/
public def underFiberConjugate
    {u : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))}
    {v : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ cc))}
    (ρ : v.1.right ⟶ u.1.right) (hρ : p.IsStronglyCartesian D ρ)
    (hw : v.1.hom ≫ ρ = φ ≫ u.1.hom) (θ : u ⟶ u) :
    { χ : v ⟶ v // χ.1.right ≫ ρ = ρ ≫ θ.1.right } := by
  have hθ : p.IsHomLift (𝟙 U') θ.1.right := underPost_isHomLift_right p (𝟙 _) θ.1 θ.2
  have hid : D = 𝟙 V' ≫ D := (Category.id_comp D).symm
  have := hρ
  have hcomp : p.IsHomLift D (ρ ≫ θ.1.right) :=
    IsHomLift.comp_lift_id_right' p D ρ U' θ.1.right
  have := hcomp
  have hχlift : p.IsHomLift (𝟙 V')
      (Functor.IsStronglyCartesian.map p D ρ hid (ρ ≫ θ.1.right)) :=
    Functor.IsStronglyCartesian.map_isHomLift p D ρ hid _
  have hχfac : Functor.IsStronglyCartesian.map p D ρ hid (ρ ≫ θ.1.right) ≫ ρ =
      ρ ≫ θ.1.right := Functor.IsStronglyCartesian.fac p D ρ hid _
  have hsv : p.IsHomLift cc v.1.hom := underFiber_isHomLift p hy cc v
  have hcompat : v.1.hom ≫ Functor.IsStronglyCartesian.map p D ρ hid (ρ ≫ θ.1.right) =
      v.1.hom := by
    have hl : p.IsHomLift cc
        (v.1.hom ≫ Functor.IsStronglyCartesian.map p D ρ hid (ρ ≫ θ.1.right)) := by
      have := hsv
      have := hχlift
      simpa only [Category.comp_id] using (inferInstance : p.IsHomLift (cc ≫ 𝟙 V')
        (v.1.hom ≫ Functor.IsStronglyCartesian.map p D ρ hid (ρ ≫ θ.1.right)))
    have := hl
    have := hsv
    refine Functor.IsStronglyCartesian.ext p D ρ cc ?_
    rw [Category.assoc, hχfac, ← Category.assoc, hw, Category.assoc, Under.w θ.1]
  exact ⟨underFiberHomMk p hy cc _ hχlift hcompat, hχfac⟩

/-- **Conjugation along a cartesian comparison arrow is unique.** -/
public theorem eq_of_conj_underFiber
    {u : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))}
    {v : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ cc))}
    (ρ : v.1.right ⟶ u.1.right) (hρ : p.IsStronglyCartesian D ρ) {θ : u ⟶ u} {χ χ' : v ⟶ v}
    (hχ : χ.1.right ≫ ρ = ρ ≫ θ.1.right) (hχ' : χ'.1.right ≫ ρ = ρ ≫ θ.1.right) :
    χ = χ' := by
  have hc : p.IsHomLift (𝟙 V') χ.1.right := underPost_isHomLift_right p (𝟙 _) χ.1 χ.2
  have hc' : p.IsHomLift (𝟙 V') χ'.1.right := underPost_isHomLift_right p (𝟙 _) χ'.1 χ'.2
  have key : χ.1.right = χ'.1.right := by
    have := hρ
    have := hc
    have := hc'
    exact Functor.IsStronglyCartesian.ext p D ρ (𝟙 V') (hχ.trans hχ'.symm)
  apply Functor.Fiber.hom_ext
  apply Under.UnderMorphism.ext
  exact key

end LiftSquarePullback

/-! ### The pullback of lift classes is functorial in the base square -/

section PullbackComp

open CategoryTheory.Functor

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X] (p : X ⥤ C)
  (hp : p.IsFiberedInGroupoids)
  {U U' V V' W W' : C} {aa : U ⟶ U'} {cc : V ⟶ V'} {dd : W ⟶ W'}
  {bb₁ : V ⟶ U} {bb₂ : W ⟶ V} (D₁ : V' ⟶ U') (D₂ : W' ⟶ V')
  (hsq₁ : bb₁ ≫ aa = cc ≫ D₁) (hsq₂ : bb₂ ≫ cc = dd ≫ D₂)
  {x y z : X} {hx : p.obj x = U} {hy : p.obj y = V} {hz : p.obj z = W}
  (φ₁ : y ⟶ x) (hφ₁ : p.IsHomLift bb₁ φ₁) (φ₂ : z ⟶ y) (hφ₂ : p.IsHomLift bb₂ φ₂)

include hp hsq₁ hsq₂ hφ₁ hφ₂ in
/-- **The pullback of lift classes is functorial in the base square.** Pullback along a
composite of two commuting squares of the base is the composite of the two pullbacks.

Both sides are pullbacks of the same class along the composite arrow `D₂ ≫ D₁`, compatibly with
the composite `φ₂ ≫ φ₁`: on the right the two comparison arrows compose, and a composite of
strongly cartesian arrows is strongly cartesian. So the two agree by the uniqueness of such a
pullback, `Deformation.Artin.eq_underFiberClassPullback_of_cartesian`.

This is what the transport of a geometric difference needs. The comparison out of a
pulled-back lift into a pulled-back glueing is not an independent pullback but the arrow
induced by cartesianness, and this is the law which identifies the two. -/
public theorem underFiberClassPullback_comp
    (hsqc : (bb₂ ≫ bb₁) ≫ aa = dd ≫ D₂ ≫ D₁)
    (hφc : p.IsHomLift (bb₂ ≫ bb₁) (φ₂ ≫ φ₁))
    (a : Quotient (isIsomorphicSetoid ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))))) :
    underFiberClassPullback p hp (D₂ ≫ D₁) hsqc (φ₂ ≫ φ₁) hφc (hy := hz) a =
      underFiberClassPullback p hp D₂ hsq₂ φ₂ hφ₂ (hy := hz)
        (underFiberClassPullback p hp D₁ hsq₁ φ₁ hφ₁ (hy := hy) a) := by
  induction a using Quotient.ind with
  | _ u =>
    obtain ⟨ρ₁, hρ₁, hw₁⟩ := (underFiberPullback p hp D₁ hsq₁ φ₁ hφ₁ (hy := hy) u).2
    obtain ⟨ρ₂, hρ₂, hw₂⟩ := (underFiberPullback p hp D₂ hsq₂ φ₂ hφ₂ (hy := hz)
      (underFiberPullback p hp D₁ hsq₁ φ₁ hφ₁ (hy := hy) u).1).2
    obtain ⟨ρ, hρ, hw⟩ :=
      (underFiberPullback p hp (D₂ ≫ D₁) hsqc (φ₂ ≫ φ₁) hφc (hy := hz) u).2
    exact underFiberClass_eq_of_cartesian p (D₂ ≫ D₁) (φ₂ ≫ φ₁) rfl ρ (ρ₂ ≫ ρ₁) hρ
      (IsStronglyCartesian.comp p) hw
      (by rw [← Category.assoc, hw₂, Category.assoc, hw₁, Category.assoc])

end PullbackComp

/-! ### A cartesian comparison of lifts transports along the pullbacks -/

section ComparisonTransport

open CategoryTheory.Functor

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X] (p : X ⥤ C)
  (hp : p.IsFiberedInGroupoids)
  {U V U₁ U₂ V₁ V₂ : C} {aa₁ : U ⟶ U₁} {aa₂ : U ⟶ U₂} {cc₁ : V ⟶ V₁} {cc₂ : V ⟶ V₂}
  {bb : V ⟶ U} (E₁ : V₁ ⟶ U₁) (E₂ : V₂ ⟶ U₂)
  (hsq₁ : bb ≫ aa₁ = cc₁ ≫ E₁) (hsq₂ : bb ≫ aa₂ = cc₂ ≫ E₂)
  (r : U₁ ⟶ U₂) (r' : V₁ ⟶ V₂) (hr : r' ≫ E₂ = E₁ ≫ r)
  {x y : X} {hx : p.obj x = U} {hy : p.obj y = V} (φ₀ : y ⟶ x) (hφ₀ : p.IsHomLift bb φ₀)

include hp hsq₁ hsq₂ hr hφ₀ in
/-- **A cartesian comparison of two lifts of `x` transports to their pullbacks.** Let `t` be a
lift of `x` under `aa₁` carrying a strongly cartesian arrow over `r` to a lift `u` of `x` under
`aa₂`. Pulling `t` and `u` back along the two squares, the comparison transports: there is a
strongly cartesian arrow over `r'` between the two pullbacks, compatible with the two pullback
comparisons.

It is the arrow induced by cartesianness of the comparison out of the pullback of `u` — not an
independent pullback — and it is strongly cartesian by cancellation
(`CategoryTheory.Functor.IsStronglyCartesian.of_comp`), the two squares composing to one by
`hr`.

This is what carries the arrows of a geometric-difference witness of Stacks 07Y9 (2)(b) to the
other side of a ring map. -/
public theorem exists_cartesian_underFiberPullback_comparison
    {t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa₁))}
    {u : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa₂))}
    (φ : t.1.right ⟶ u.1.right) (hφ : p.IsStronglyCartesian r φ) :
    ∃ χ : (underFiberPullback p hp E₁ hsq₁ φ₀ hφ₀ (hy := hy) t).1.1.right ⟶
        (underFiberPullback p hp E₂ hsq₂ φ₀ hφ₀ (hy := hy) u).1.1.right,
      p.IsStronglyCartesian r' χ ∧
        χ ≫ (underFiberPullback p hp E₂ hsq₂ φ₀ hφ₀ (hy := hy) u).2.choose =
          (underFiberPullback p hp E₁ hsq₁ φ₀ hφ₀ (hy := hy) t).2.choose ≫ φ := by
  have hρt := (underFiberPullback p hp E₁ hsq₁ φ₀ hφ₀ (hy := hy) t).2.choose_spec.1
  have hρu := (underFiberPullback p hp E₂ hsq₂ φ₀ hφ₀ (hy := hy) u).2.choose_spec.1
  have := hρt
  have := hρu
  have := hφ
  have hcomp : p.IsHomLift (r' ≫ E₂)
      ((underFiberPullback p hp E₁ hsq₁ φ₀ hφ₀ (hy := hy) t).2.choose ≫ φ) := by
    rw [hr]
    exact isHomLift_comp p hρt.toIsHomLift hφ.toIsHomLift
  have := hcomp
  refine ⟨IsStronglyCartesian.map p E₂
      (underFiberPullback p hp E₂ hsq₂ φ₀ hφ₀ (hy := hy) u).2.choose (rfl : r' ≫ E₂ = r' ≫ E₂)
      ((underFiberPullback p hp E₁ hsq₁ φ₀ hφ₀ (hy := hy) t).2.choose ≫ φ), ?_, ?_⟩
  · have hmap : p.IsHomLift r' (IsStronglyCartesian.map p E₂
        (underFiberPullback p hp E₂ hsq₂ φ₀ hφ₀ (hy := hy) u).2.choose
        (rfl : r' ≫ E₂ = r' ≫ E₂)
        ((underFiberPullback p hp E₁ hsq₁ φ₀ hφ₀ (hy := hy) t).2.choose ≫ φ)) :=
      IsStronglyCartesian.map_isHomLift p E₂ _ _ _
    exact hp.isStronglyCartesian_homLift _ _
  · exact IsStronglyCartesian.fac p E₂ _ _ _

omit hp in
/-- **Two transported comparisons into one pulled-back glueing agree on the structure arrows
when the originals do.** This is the witness's glueing identity, transported.

Both composites are arrows out of the pulled-back object over the same arrow of the base, and
after the cartesian comparison `ρ` into the glueing each becomes `φ₀` followed by the
corresponding original composite; those agree by hypothesis, so the two are equal by
cancellation against `ρ`.

The two comparisons and their defining identities are taken as given — they are what
`Deformation.Artin.exists_cartesian_underFiberPullback_comparison` produces — so this lemma
carries no bookkeeping of its own. -/
public theorem eq_of_comp_cartesian_glue {V₃ U₃ : C} {cc₃ : V ⟶ V₃} {E₃ : V₃ ⟶ U₃}
    {t₁ t₂ v : X} {u : X}
    (ρ : v ⟶ u) (hρ : p.IsStronglyCartesian E₃ ρ)
    {s₁ : y ⟶ t₁} {s₂ : y ⟶ t₂} {m₁ : x ⟶ u} {m₂ : x ⟶ u}
    {ρ₁ : t₁ ⟶ x} {ρ₂ : t₂ ⟶ x}
    {χ₁ : t₁ ⟶ v} {χ₂ : t₂ ⟶ v}
    (hχ₁ : χ₁ ≫ ρ = ρ₁ ≫ m₁) (hχ₂ : χ₂ ≫ ρ = ρ₂ ≫ m₂)
    (hw₁ : s₁ ≫ ρ₁ = φ₀) (hw₂ : s₂ ≫ ρ₂ = φ₀)
    (hglue : m₁ = m₂)
    (h₁ : p.IsHomLift cc₃ (s₁ ≫ χ₁)) (h₂ : p.IsHomLift cc₃ (s₂ ≫ χ₂)) :
    s₁ ≫ χ₁ = s₂ ≫ χ₂ := by
  refine IsStronglyCartesian.ext p E₃ ρ cc₃ ?_
  rw [Category.assoc, Category.assoc, hχ₁, hχ₂, ← Category.assoc, ← Category.assoc, hw₁, hw₂,
    hglue]

end ComparisonTransport

/-! ### The morphism of deformation situations -/

section DeformationSituation

open CategoryTheory.Functor

universe u v w

variable {A C : Type u} [CommRing A] [CommRing C] {B : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : B.Contains S} {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {toSC : Spec (.of C) ⟶ S} {hC : B.Contains (Spec (.of C))}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)
  {x y : X} {hx : p.obj x = algebraOver A B S hS toS hA}
  {hy : p.obj y = algebraOver C B S hS toSC hC}
  {W W' : BigFppfOver B S hS}
  (gA : algebraOver A B S hS toS hA ⟶ W) (gC : algebraOver C B S hS toSC hC ⟶ W')
  (bb : algebraOver C B S hS toSC hC ⟶ algebraOver A B S hS toS hA) (e : W' ⟶ W)
  (hdef : bb ≫ gA = gC ≫ e) (φ : y ⟶ x) (hφ : p.IsHomLift bb φ)

include hp hdef hφ in
/-- **The pullback of lift classes across a morphism of deformation situations.** A
deformation situation of `x` is an arrow `gA : Spec A ⟶ Spec A'` out of the base of `x`; a
morphism to it from one of `y` is a commuting square with the arrow `Spec C ⟶ Spec A` under
`y ⟶ x`. Pullback along the fourth side `Spec C' ⟶ Spec A'` of that square carries
isomorphism classes of lifts of `x` over `Spec A'` to isomorphism classes of lifts of `y`
over `Spec C'`.

The targets `W`, `W'` of the two deformation situations are arbitrary objects of the site over
`S`; at the affine presentations of a square-zero deformation situation they are `Spec A'` and
`Spec C'`, and `gA`, `gC` are the arrows induced by the two augmentations.

This is the map which the compatibility of Stacks 07YA with the action of Stacks 07Y9 (2)(b)
compares with the transition on tangent modules; before it the pullback of lift classes was
available only across the square of trivial square-zero extensions
(`Deformation.Artin.squareZeroLiftBaseChangeMap`). -/
public def deformationSituationPullback :
    liftClassesOver A B S hS toS hA p x hx gA →
      liftClassesOver C B S hS toSC hC p y hy gC :=
  underFiberClassPullback p hp e hdef φ hφ

include hp hdef hφ in
/-- **The defining property of the pullback across a morphism of deformation situations.** -/
public theorem exists_cartesian_deformationSituationPullback
    (a : liftClassesOver A B S hS toS hA p x hx gA) :
    ∃ (u : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA)))
      (v : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC))),
      Quotient.mk _ u = a ∧
        Quotient.mk _ v = deformationSituationPullback hp gA gC bb e hdef φ hφ a ∧
          ∃ ρ : v.1.right ⟶ u.1.right,
            p.IsStronglyCartesian e ρ ∧ v.1.hom ≫ ρ = φ ≫ u.1.hom :=
  exists_cartesian_underFiberClassPullback p hp e hdef φ hφ a

include hp hdef hφ in
/-- **The defining property determines the pullback across a morphism of deformation
situations.** -/
public theorem eq_deformationSituationPullback_of_cartesian
    {a : liftClassesOver A B S hS toS hA p x hx gA}
    {b : liftClassesOver C B S hS toSC hC p y hy gC}
    (u : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA)))
    (v : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC)))
    (hu : Quotient.mk _ u = a) (hv : Quotient.mk _ v = b)
    (ρ : v.1.right ⟶ u.1.right) (hρ : p.IsStronglyCartesian e ρ)
    (hw : v.1.hom ≫ ρ = φ ≫ u.1.hom) :
    b = deformationSituationPullback hp gA gC bb e hdef φ hφ a :=
  eq_underFiberClassPullback_of_cartesian p hp e hdef φ hφ u v hu hv ρ hρ hw

end DeformationSituation

end Deformation.Artin

end
