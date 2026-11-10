module

public import StacksFrontier.CategoryTheory.Sites.Topos.PolynomialSystemSections
public import StacksFrontier.CategoryTheory.Sites.Topos.RingSheafHomPolynomialEvaluation

/-!
# The row of a polynomial system, read along a functor to sets

Let `(C, J)` be a site, `𝒪` a sheaf of commutative rings on it, and `P₁, …, P_ν` a family of
polynomials in `κ` variables whose coefficients are read into the global sections of `𝒪` by a
ring homomorphism `c`.  The *row* of the system is the pair of arrows `∏ᵏ 𝒪 ⇉ ∏ᵛ 𝒪` given by
`CategoryTheory.CommRingObj.evalSystemHom` and `CategoryTheory.CommRingObj.zeroSystemHom`.

`StacksFrontier.CategoryTheory.Sites.Topos.PolynomialSystemSections` reads that row on the sections
over an object of the site, where `𝒪` has a commutative ring of sections of its own.  This file
reads it along an arbitrary functor `Q` to sets which preserves finite products.  There is no
ring of sections to hand there, so the ring structure used is the one *transported* along `Q`
from the internal operations of `𝒪` — `CategoryTheory.Sheaf.ringObjRing`, which is
commutative here because the sections of `𝒪` are.

The reading is the same statement: a point of `Q(∏ᵏ 𝒪)` is a `κ`-tuple of points of `Q(𝒪)`, and
the two legs of the row agree at it exactly when that tuple solves the system over `Q(𝒪)`.  Its
point is that the *stalk* functor at a point of the site is such a `Q` while being nothing like
a sections functor, which is what step (4) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6) needs: there the stalk of
a sheaf of solutions has to be recognized as a set of solutions over a strictly henselian local
ring, the shape [Stacks Project, Tag 04GX] is stated at.

## Main definitions

* `Stacks.Sheaves.PolynomialSystem.objCommRing`: the transported commutative ring structure on
  `Q(𝒪)`.
* `Stacks.Sheaves.PolynomialSystem.objEvalRingHom`: evaluating a generalized element `Z ⟶ 𝒪` at
  a point of `Q(Z)`, as a ring homomorphism into `Q(𝒪)`.
* `Stacks.Sheaves.PolynomialSystem.objGlobalRingHom`: the same for a global generalized element,
  i.e. the map `Γ(C, 𝒪) ⟶ Q(𝒪)` reading a global section of `𝒪` into `Q(𝒪)`.

## Main results

* `Stacks.Sheaves.PolynomialSystem.objEvalRingHom_evalRingHom`: **the internal evaluation of a
  polynomial, read along `Q`, is honest polynomial evaluation in `Q(𝒪)`**, the coefficients
  read along `objGlobalRingHom`.
* `Stacks.Sheaves.PolynomialSystem.obj_evalSystemHom_eq_zeroSystemHom_iff` and
  `obj_row_eq_iff_isSolution`: the two legs of the row agree at a point of `Q(∏ᵏ 𝒪)` exactly
  when its coordinates solve the system, the second in the spelling `MvPolynomial.IsSolution`
  that [Stacks Project, Tag 04GX] uses.

## Implementation notes

The sections statements of
`StacksFrontier.CategoryTheory.Sites.Topos.PolynomialSystemSections` are not instances of these:
there the target ring is the ring of sections of `𝒪` itself, here it is the transported ring,
and the two structures are different structures on different types.  What the two readings share
is `CategoryTheory.Sheaf.map_hom_add` and its companions — the statement that applying a
finite-product-preserving functor to a generalized element is additive and multiplicative — and
both are proved from those and from nothing else.

`Stacks.Sheaves.PolynomialSystem.objCommRing` is a `def` and not an instance, for the reason
recorded at `CategoryTheory.Sheaf.ringObjRing`: it is stated for an arbitrary `Q` and as an instance
would
be tried in every instance search.  Every statement below therefore carries it in a `letI`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CommRingObj Obj

universe t w v u

namespace Stacks.Sheaves.PolynomialSystem

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget CommRingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})]

attribute [local instance] Stacks.sheafCommRingObj

open CategoryTheory.Sheaf

/-! ### The transported commutative ring structure -/

section Transported

variable (O : Sheaf J CommRingCat.{w}) (Q : Sheaf J (Type w) ⥤ Type t)
  [PreservesFiniteProducts Q]

/-- **The image of the underlying sheaf of sets of a sheaf of commutative rings under a
finite-product-preserving functor to sets is a commutative ring.**  The operations are the ones
`CategoryTheory.Sheaf.ringObjRing` transports from the internal operations of `𝒪`;
commutativity comes from commutativity of the sections of `𝒪` through
`CategoryTheory.Sheaf.ringMulObj_comm`. -/
@[instance_reducible]
def objCommRing : CommRing (Q.obj (Stacks.underlyingRingSheaf J O)) :=
  letI := ringObjRing (Stacks.SheafOfModules.Tensor.ringSheaf O) Q
  { __ := ringObjRing (Stacks.SheafOfModules.Tensor.ringSheaf O) Q
    mul_comm := ringMulObj_comm (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (fun X x y => mul_comm (G := ToType (O.obj.obj X)) x y) Q }

variable {O} {Z : Sheaf J (Type w)}

/-! ### The internal operations are the transported operations

The generalized elements `Z ⟶ 𝒪` carry two ring structures, Mathlib's
`CategoryTheory.CommRingObj.Hom.commRing` of the internal commutative ring object and the
project's `CategoryTheory.Sheaf.homRing`; they are identified by
`Stacks.Sheaves.PolynomialSystem.hom_add_eq` and its companions.  The four statements below are
the resulting reading of the first structure along `Q`. -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Along `Q`, the sum of two generalized elements `Z ⟶ 𝒪` evaluates to the sum of their values
in the transported ring `objCommRing`. -/
theorem obj_map_add (a b : Z ⟶ Stacks.underlyingRingSheaf J O) (z : Q.obj Z) :
    letI := objCommRing O Q
    Q.map (a + b) z = Q.map a z + Q.map b z :=
  (congrArg (fun m => Q.map m z)
      ((hom_add_eq a b).trans
        (Sheaf.hom_add_eq (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a b).symm)).trans
    (Sheaf.map_hom_add (R := Stacks.SheafOfModules.Tensor.ringSheaf O) Q a b z)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Along `Q`, the product of two generalized elements `Z ⟶ 𝒪` evaluates to the product of their
values in the transported ring `objCommRing`. -/
theorem obj_map_mul (a b : Z ⟶ Stacks.underlyingRingSheaf J O) (z : Q.obj Z) :
    letI := objCommRing O Q
    Q.map (a * b) z = Q.map a z * Q.map b z :=
  (congrArg (fun m => Q.map m z)
      ((hom_mul_eq a b).trans
        (Sheaf.hom_mul_eq (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a b).symm)).trans
    (Sheaf.map_hom_mul (R := Stacks.SheafOfModules.Tensor.ringSheaf O) Q a b z)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Along `Q`, the zero generalized element `Z ⟶ 𝒪` evaluates to zero in the transported ring
`objCommRing`. -/
theorem obj_map_zero (z : Q.obj Z) :
    letI := objCommRing O Q
    Q.map (0 : Z ⟶ Stacks.underlyingRingSheaf J O) z = 0 :=
  (congrArg (fun m => Q.map m z)
      ((hom_zero_eq (O := O) (Z := Z)).trans
        (Sheaf.hom_ringZero_eq
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (Z := Z)).symm)).trans
    (Sheaf.map_hom_ringZero (R := Stacks.SheafOfModules.Tensor.ringSheaf O) Q z)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Along `Q`, the unit generalized element `Z ⟶ 𝒪` evaluates to one in the transported ring
`objCommRing`. -/
theorem obj_map_one (z : Q.obj Z) :
    letI := objCommRing O Q
    Q.map (1 : Z ⟶ Stacks.underlyingRingSheaf J O) z = 1 :=
  (congrArg (fun m => Q.map m z)
      ((hom_one_eq (O := O) (Z := Z)).trans
        (Sheaf.hom_one_eq (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (Z := Z)).symm)).trans
    (Sheaf.map_hom_one (R := Stacks.SheafOfModules.Tensor.ringSheaf O) Q z)

variable (O Z)

/-- **Evaluating a generalized element of a sheaf of commutative rings along a
finite-product-preserving functor to sets.**  A generalized element `Z ⟶ 𝒪` of shape `Z`,
evaluated at a fixed point of `Q(Z)`, gives a point of `Q(𝒪)`, and taking that value is a ring
homomorphism onto the transported ring structure. -/
def objEvalRingHom (z : Q.obj Z) :
    letI := objCommRing O Q
    (Z ⟶ Stacks.underlyingRingSheaf J O) →+* Q.obj (Stacks.underlyingRingSheaf J O) :=
  letI := objCommRing O Q
  { toFun := fun m => Q.map m z
    map_one' := obj_map_one Q z
    map_mul' := fun a b => obj_map_mul Q a b z
    map_zero' := obj_map_zero Q z
    map_add' := fun a b => obj_map_add Q a b z }

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `objEvalRingHom` sends a generalized element `m` to `Q.map m z`. -/
theorem objEvalRingHom_apply (z : Q.obj Z) (m : Z ⟶ Stacks.underlyingRingSheaf J O) :
    objEvalRingHom O Q Z z m = Q.map m z :=
  rfl

/-- **A global section of a sheaf of commutative rings, read along a
finite-product-preserving functor to sets.**  It is `objEvalRingHom` at the unique point of the
image of the terminal sheaf. -/
def objGlobalRingHom :
    letI := objCommRing O Q
    (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O) →+*
      Q.obj (Stacks.underlyingRingSheaf J O) :=
  objEvalRingHom O Q (𝟙_ (Sheaf J (Type w)))
    (default : Q.obj (⊤_ (Sheaf J (Type w))))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `objGlobalRingHom` is `objEvalRingHom` at the unique point of the image of the terminal
sheaf. -/
theorem objGlobalRingHom_eq (g : 𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O) :
    objGlobalRingHom O Q g =
      objEvalRingHom O Q (𝟙_ (Sheaf J (Type w)))
        (default : Q.obj (⊤_ (Sheaf J (Type w)))) g :=
  rfl

variable {O Z}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A constant generalized element is the global section it is constant at, read along `Q`. -/
theorem objEvalRingHom_comp_toUnit (z : Q.obj Z)
    (g : 𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O) :
    objEvalRingHom O Q Z z (toUnit Z ≫ g) = objGlobalRingHom O Q g :=
  (Q.map_comp_apply (toUnit Z) g z).trans
    (congrArg (Q.map g) (Subsingleton.elim (α := Q.obj (⊤_ (Sheaf J (Type w)))) _ default))

end Transported

/-! ### The row of a polynomial system, read along a functor to sets -/

section Row

variable (O : Sheaf J CommRingCat.{w}) (Q : Sheaf J (Type w) ⥤ Type t)
  [PreservesFiniteProducts Q] {Z : Sheaf J (Type w)} {Γ : Type*} [CommRing Γ]
  (c : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The internal evaluation of a polynomial, read along `Q`, is polynomial evaluation in the
transported ring `Q(𝒪)`.**  The coefficients are the global sections named by `c`, read into
`Q(𝒪)` along `Stacks.Sheaves.PolynomialSystem.objGlobalRingHom`, and the variables take the
values of the coordinates at the point `z`. -/
theorem objEvalRingHom_evalRingHom {κ : Type*}
    (x : κ → (Z ⟶ Stacks.underlyingRingSheaf J O))
    (z : Q.obj Z) (Qq : MvPolynomial κ Γ) :
    letI := objCommRing O Q
    objEvalRingHom O Q Z z (CommRingObj.evalRingHom _ c x Qq) =
      MvPolynomial.eval₂Hom ((objGlobalRingHom O Q).comp c)
        (fun i => objEvalRingHom O Q Z z (x i)) Qq := by
  let := objCommRing O Q
  have key : (objEvalRingHom O Q Z z).comp (CommRingObj.evalRingHom _ c x) =
      MvPolynomial.eval₂Hom ((objGlobalRingHom O Q).comp c)
        (fun i => objEvalRingHom O Q Z z (x i)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, CommRingObj.evalRingHom_C, MvPolynomial.eval₂Hom_C,
        RingHom.comp_apply, objEvalRingHom_comp_toUnit]
    · rw [RingHom.comp_apply, CommRingObj.evalRingHom_X, MvPolynomial.eval₂Hom_X']
  exact RingHom.congr_fun key Qq

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The evaluation morphism of a power of `𝒪`, read along `Q`: a point of `Q(∏ᵏ 𝒪)` is a
`κ`-tuple of points of `Q(𝒪)`, and the value of `Qq` at it is the honest value of `Qq` at that
tuple. -/
theorem obj_map_evalPowRingHom (κ : Type*)
    [HasProduct fun _ : κ => Stacks.underlyingRingSheaf J O]
    (l : Q.obj (∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf J O)) (Qq : MvPolynomial κ Γ) :
    letI := objCommRing O Q
    Q.map (CommRingObj.evalPowRingHom _ c κ Qq) l =
      MvPolynomial.eval₂Hom ((objGlobalRingHom O Q).comp c)
        (fun i => Q.map (Pi.π _ i) l) Qq :=
  objEvalRingHom_evalRingHom O Q c (Pi.π (fun _ : κ => Stacks.underlyingRingSheaf J O)) l Qq

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The two legs of the row agree at a point of `Q(∏ᵏ 𝒪)` exactly when its coordinates solve
the system.**  This is the vanishing condition that the equalizer of the row cuts out, read
along `Q`. -/
theorem obj_evalSystemHom_eq_zeroSystemHom_iff (κ : Type) [Finite κ] (ν : Type) [Finite ν]
    (P : ν → MvPolynomial κ Γ)
    (l : Q.obj (∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf J O)) :
    letI := objCommRing O Q
    Q.map (CommRingObj.evalSystemHom _ c κ P) l =
        Q.map (CommRingObj.zeroSystemHom _ κ ν) l ↔
      ∀ j, MvPolynomial.eval₂Hom ((objGlobalRingHom O Q).comp c)
        (fun i => Q.map (Pi.π _ i) l) (P j) = 0 := by
  let := objCommRing O Q
  have hcomp : ∀ j : ν,
      Q.map (Pi.π (fun _ : ν => Stacks.underlyingRingSheaf J O) j)
          (Q.map (CommRingObj.evalSystemHom _ c κ P) l) =
        MvPolynomial.eval₂Hom ((objGlobalRingHom O Q).comp c)
          (fun i => Q.map (Pi.π _ i) l) (P j) := fun j => by
    rw [← Functor.map_comp_apply, CommRingObj.evalSystemHom_comp_π, obj_map_evalPowRingHom]
  have hzero : ∀ j : ν,
      Q.map (Pi.π (fun _ : ν => Stacks.underlyingRingSheaf J O) j)
          (Q.map (CommRingObj.zeroSystemHom _ κ ν) l) = 0 := fun j => by
    rw [← Functor.map_comp_apply, CommRingObj.zeroSystemHom_comp_π, obj_map_zero]
  refine ⟨fun h j => ?_, fun h => Functor.piObjMk_ext (fun j => ?_)⟩
  · rw [← hcomp j, h, hzero j]
  · rw [hcomp j, hzero j, h j]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The same for a square system indexed by `Fin n`, in the spelling `MvPolynomial.IsSolution`
that [Stacks Project, Tag 04GX] uses for its two solution sets. -/
theorem obj_row_eq_iff_isSolution {n : ℕ} (P : Fin n → MvPolynomial (Fin n) Γ)
    (l : Q.obj (∏ᶜ fun _ : Fin n => Stacks.underlyingRingSheaf J O)) :
    letI := objCommRing O Q
    Q.map (CommRingObj.evalSystemHom _ c (Fin n) P) l =
        Q.map (CommRingObj.zeroSystemHom _ (Fin n) (Fin n)) l ↔
      MvPolynomial.IsSolution P ((objGlobalRingHom O Q).comp c)
        (fun i => Q.map (Pi.π _ i) l) := by
  let := objCommRing O Q
  rw [obj_evalSystemHom_eq_zeroSystemHom_iff]
  exact ⟨fun h j => (MvPolynomial.eval_map _ _ _).trans (h j),
    fun h j => (MvPolynomial.eval_map _ _ _).symm.trans (h j)⟩

end Row


/-! ### Invertibility of the induced map of equalizers -/

section Comparison

variable {O₁ O₂ : Sheaf J CommRingCat.{w}} (α : O₁ ⟶ O₂)
  (Q : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteLimits Q]
  {Γ : Type*} [CommRing Γ] (κ : Type) [Finite κ] {ν : Type} [Finite ν]
  (P : ν → MvPolynomial κ Γ)
  (c₁ : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O₁))
  (c₂ : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O₂))

/-- The solutions of the system over the transported ring `Q(𝒪)`: the `κ`-tuples of points of
`Q(𝒪)` at which every `P j`, its coefficients read along `Q`, vanishes. -/
def objSolutions (O : Sheaf J CommRingCat.{w})
    (c : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O)) :
    Set (κ → Q.obj (Stacks.underlyingRingSheaf J O)) :=
  letI := objCommRing O Q
  {a | ∀ j, MvPolynomial.eval₂Hom ((objGlobalRingHom O Q).comp c) a (P j) = 0}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The induced map of equalizers is bijective along `Q` as soon as it is bijective on
solution sets.**

Let `H₁ ⟶ ∏ᵏ 𝒪₁` and `H₂ ⟶ ∏ᵏ 𝒪₂` be the equalizers of the rows of one system `P` over two
sheaves of commutative rings, let `α : 𝒪₁ ⟶ 𝒪₂` be a morphism between them, and let `m` be a
morphism `H₁ ⟶ H₂` compatible with the coordinates.  Applying a left exact functor `Q` to sets
turns both equalizers into the solution sets of `P` over the transported rings `Q(𝒪₁)` and
`Q(𝒪₂)`, and `m` into the coordinatewise map along `Q(α)`.  So `Q(m)` is bijective exactly when
that coordinatewise map is a bijection of solution sets.

This is the shape of step (4) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6): the comparison
`g⁻¹h_V ⟶ h_{X ×_Y V}` is an isomorphism because the small étale site has enough points and at
each point the coordinatewise map is the bijection of
[Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX).  Nothing about the
surrounding geometry enters here: only that `Q` is left exact.

No compatibility between `c₁` and `c₂` is required.  The hypothesis is an assertion about the
two solution sets as they stand, and the compatibility is what one uses to *prove* that
assertion. -/
theorem bijective_map_of_bijOn_solutions
    {H₁ H₂ : Sheaf J (Type w)}
    {ι₁ : H₁ ⟶ ∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf J O₁}
    (h₁ : ι₁ ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O₁) c₁ κ P =
      ι₁ ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O₁) κ ν)
    (hl₁ : IsLimit (Fork.ofι ι₁ h₁))
    {ι₂ : H₂ ⟶ ∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf J O₂}
    (h₂ : ι₂ ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O₂) c₂ κ P =
      ι₂ ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O₂) κ ν)
    (hl₂ : IsLimit (Fork.ofι ι₂ h₂))
    (m : H₁ ⟶ H₂)
    (hm : m ≫ ι₂ = ι₁ ≫ Limits.Pi.map (fun _ : κ => underlyingMap α))
    (hbij : Set.BijOn (fun a : κ → Q.obj (Stacks.underlyingRingSheaf J O₁) =>
        fun i => Q.map (underlyingMap α) (a i))
      (objSolutions Q κ P O₁ c₁) (objSolutions Q κ P O₂ c₂)) :
    Function.Bijective (Q.map m) := by
  -- for each equalizer: unique lifts, points solve the system, and the inclusion is injective
  have key : ∀ {O : Sheaf J CommRingCat.{w}}
      {c : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O)}
      {H : Sheaf J (Type w)} {ι : H ⟶ ∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf J O}
      (h : ι ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O) c κ P =
        ι ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O) κ ν)
      (hl : IsLimit (Fork.ofι ι h)),
      (∀ y : Q.obj (∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf J O),
        Q.map (CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O) c κ P) y =
          Q.map (CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O) κ ν) y →
        ∃! x, Q.map ι x = y) ∧
      (∀ x : Q.obj H,
        (fun i => Q.map (Pi.π _ i) (Q.map ι x)) ∈ objSolutions Q κ P O c) ∧
      Function.Injective (Q.map ι) := fun {O c H ι} h hl => by
    have hu := fun y hy => Limits.Types.unique_of_type_equalizer _ _
      (isLimitForkMapOfIsLimit Q h hl) (y : Q.obj (∏ᶜ fun _ : κ => _)) hy
    have hsol : ∀ x : Q.obj H,
        (fun i => Q.map (Pi.π _ i) (Q.map ι x)) ∈ objSolutions Q κ P O c := fun x => by
      refine (obj_evalSystemHom_eq_zeroSystemHom_iff O Q c κ ν P _).1 ?_
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, h]
    exact ⟨hu, hsol, fun x x' hxx =>
      (hu (Q.map ι x)
        ((obj_evalSystemHom_eq_zeroSystemHom_iff O Q c κ ν P _).2 (hsol x))).unique rfl hxx.symm⟩
  obtain ⟨hu₁, hsol₁, hinj₁⟩ := key h₁ hl₁
  obtain ⟨-, hsol₂, hinj₂⟩ := key h₂ hl₂
  -- the square, read on coordinates
  have hsq : ∀ (x : Q.obj H₁) (i : κ),
      Q.map (Pi.π _ i) (Q.map ι₂ (Q.map m x)) =
        Q.map (underlyingMap α) (Q.map (Pi.π _ i) (Q.map ι₁ x)) := fun x i => by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← Category.assoc, hm,
      Category.assoc, Limits.Pi.map_π, ← Category.assoc, Functor.map_comp_apply,
      Functor.map_comp_apply]
  refine ⟨fun x x' hxx => ?_, fun z => ?_⟩
  · have hco : (fun i => Q.map (underlyingMap α) (Q.map (Pi.π _ i) (Q.map ι₁ x))) =
      fun i => Q.map (underlyingMap α) (Q.map (Pi.π _ i) (Q.map ι₁ x')) :=
      funext fun i => by rw [← hsq x i, ← hsq x' i, hxx]
    exact hinj₁ (Functor.piObjMk_ext fun i =>
      congrFun (hbij.2.1 (hsol₁ x) (hsol₁ x') hco) i)
  · obtain ⟨a, ha, hae⟩ := hbij.2.2 (hsol₂ z)
    obtain ⟨x, hx, -⟩ := hu₁ (Functor.piObjMk (P := Q) a)
      ((obj_evalSystemHom_eq_zeroSystemHom_iff O₁ Q c₁ κ ν P _).2
        (fun j => by simpa only [Functor.map_piπ_piObjMk] using ha j))
    refine ⟨x, hinj₂ (Functor.piObjMk_ext fun i => ?_)⟩
    rw [hsq x i, hx, Functor.map_piπ_piObjMk]
    exact congrFun hae i

end Comparison

end Stacks.Sheaves.PolynomialSystem

end
