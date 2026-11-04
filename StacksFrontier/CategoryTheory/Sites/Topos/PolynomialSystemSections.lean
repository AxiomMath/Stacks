module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSquareZeroIdeal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomAlgebra
public import StacksFrontier.CategoryTheory.Sites.Topos.InternalPolynomialEvaluation
public import StacksFrontier.RingTheory.Etale.StandardPresentationSolutions

/-!
# A sheaf cut out by a system of polynomial equations is an equalizer

Let `(C, J)` be a site and `𝒪` a sheaf of commutative rings on it.  The underlying sheaf of sets
of `𝒪` is an internal commutative ring object (`Stacks.sheafCommRingObj`), so a family
`P₁, …, P_ν` of polynomials in `κ` variables with coefficients read into the global sections of
`𝒪` has an *evaluation row* `∏ᵏ 𝒪 ⇉ ∏ᵛ 𝒪` whose two legs are
`CategoryTheory.CommRingObj.evalSystemHom` and `CategoryTheory.CommRingObj.zeroSystemHom`.

This file reads that row **on sections**, and uses the reading to recognise a sheaf mapping into
`∏ᵏ 𝒪` as its equalizer.

Both halves are needed because the two descriptions of a sheaf of commutative rings as an
internal ring object are built differently.  The internal operations that
`CategoryTheory.CommRingObj.evalRingHom` is assembled from are Mathlib's `MonObj.mul`,
`AddMonObj.add`, … of `Stacks.sheafCommRingObj`; the operations whose effect on sections is
known are `CategoryTheory.Sheaf.ringAddHom`, `ringMulHom`, … of the sheaf of rings underlying
`𝒪`.  The two agree definitionally — that is `Stacks.Sheaves.PolynomialSystem.hom_add_eq` and
its companions, and it is what makes everything below provable by rewriting rather than by
re-deriving the ring axioms on sections.

## Main definitions

* `Stacks.Sheaves.PolynomialSystem.sectionsEvalRingHom`: evaluating a generalized element
  `Z ⟶ 𝒪` of the sheaf of commutative rings at a fixed section of `Z` over `X`, as a ring
  homomorphism into `Γ(X, 𝒪)`.
* `Stacks.Sheaves.PolynomialSystem.globalSectionRingHom`: the same for a *global* generalized
  element, i.e. the restriction `Γ(C, 𝒪) ⟶ Γ(X, 𝒪)` of global sections to `X`.

## Main results

* `Stacks.Sheaves.PolynomialSystem.sectionsEvalRingHom_evalRingHom`: **the internal evaluation
  of a polynomial, read on sections, is honest polynomial evaluation in the ring of sections**,
  the coefficients restricted along `globalSectionRingHom`.
* `Stacks.Sheaves.PolynomialSystem.sections_evalSystemHom_eq_iff` and
  `sections_row_eq_iff_isSolution`: the two legs of the row agree on a section of `∏ᵏ 𝒪` exactly
  when its coordinates solve the system — the second in the spelling
  `MvPolynomial.IsSolution` that [Stacks Project, Tag 04GX] uses.
* `Stacks.Sheaves.PolynomialSystem.isLimitForkOfSections`: **a sheaf whose sections over every
  object of the site are, via `ι`, exactly the solutions of the system is the equalizer of the
  row.**  This is step (2) of the proof of [Stacks Project, Tag 04I6] at the level of sheaves,
  with the set-level identification supplied by the caller.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CommRingObj Obj

universe w v u

namespace Stacks.Sheaves.PolynomialSystem

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget CommRingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})]

attribute [local instance] Stacks.sheafCommRingObj

/-! ### The sections of the underlying sheaf of sets, as a commutative ring -/

/-- The sections over `X` of the underlying sheaf of sets of a sheaf of commutative rings are the
sections of the sheaf of commutative rings itself, hence a commutative ring. -/
instance sectionsCommRing (O : Sheaf J CommRingCat.{w}) (X : Cᵒᵖ) :
    CommRing ((Sheaf.sectionsFunctor J X).obj (Stacks.underlyingRingSheaf J O)) :=
  inferInstanceAs (CommRing (ToType (O.obj.obj X)))

variable {O : Sheaf J CommRingCat.{w}} {Z : Sheaf J (Type w)}

/-! ### The internal operations are the sectionwise operations

Mathlib's internal addition of the commutative ring object `Stacks.sheafCommRingObj J O` is the
addition `CategoryTheory.Sheaf.ringAddHom` of the sheaf of rings underlying `O`, and likewise for
the other four operations; the generalized-element ring structures therefore coincide. -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The sum of two generalized elements of `𝒪` is their pairing followed by the addition of the
sheaf of rings underlying `𝒪`. -/
theorem hom_add_eq (a b : Z ⟶ Stacks.underlyingRingSheaf J O) :
    a + b = Limits.prod.lift a b ≫
      Sheaf.ringAddHom (Stacks.SheafOfModules.Tensor.ringSheaf O) := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The product of two generalized elements of `𝒪` is their pairing followed by the
multiplication of the sheaf of rings underlying `𝒪`. -/
theorem hom_mul_eq (a b : Z ⟶ Stacks.underlyingRingSheaf J O) :
    a * b = Limits.prod.lift a b ≫
      Sheaf.ringMulHom (Stacks.SheafOfModules.Tensor.ringSheaf O) := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The negative of a generalized element of `𝒪` is its composite with the negation of the sheaf
of rings underlying `𝒪`. -/
theorem hom_neg_eq (a : Z ⟶ Stacks.underlyingRingSheaf J O) :
    -a = a ≫ Sheaf.ringNegHom (Stacks.SheafOfModules.Tensor.ringSheaf O) := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The zero generalized element of `𝒪` factors through the terminal sheaf via the zero of the
sheaf of rings underlying `𝒪`. -/
theorem hom_zero_eq :
    (0 : Z ⟶ Stacks.underlyingRingSheaf J O) =
      Limits.terminal.from Z ≫ Sheaf.ringZeroHom (Stacks.SheafOfModules.Tensor.ringSheaf O) := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The unit generalized element of `𝒪` factors through the terminal sheaf via the unit of the
sheaf of rings underlying `𝒪`. -/
theorem hom_one_eq :
    (1 : Z ⟶ Stacks.underlyingRingSheaf J O) =
      Limits.terminal.from Z ≫ Sheaf.ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf O) := rfl


/-! ### Evaluating a generalized element on sections

The generalized elements `Z ⟶ 𝒪` carry two ring structures: Mathlib's
`CategoryTheory.CommRingObj.Hom.commRing`, which is what
`CategoryTheory.CommRingObj.evalRingHom` adds and multiplies in, and the project's
`CategoryTheory.Sheaf.homRing`, whose effect on sections is known.  The five statements above
identify their operations. -/

section Eval

variable (X : Cᵒᵖ)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Evaluating a sum of generalized elements of `𝒪` at a section of `Z` over `X` gives the sum
of their values. -/
theorem sections_map_add (a b : Z ⟶ Stacks.underlyingRingSheaf J O)
    (z : (Sheaf.sectionsFunctor J X).obj Z) :
    (Sheaf.sectionsFunctor J X).map (a + b) z =
      (Sheaf.sectionsFunctor J X).map a z + (Sheaf.sectionsFunctor J X).map b z :=
  (congrArg (fun m => (Sheaf.sectionsFunctor J X).map m z)
      ((hom_add_eq a b).trans
        (Sheaf.hom_add_eq (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a b).symm)).trans
    (Sheaf.sectionsFunctor_map_hom_add (R := Stacks.SheafOfModules.Tensor.ringSheaf O) X a b z)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Evaluating a product of generalized elements of `𝒪` at a section of `Z` over `X` gives the
product of their values. -/
theorem sections_map_mul (a b : Z ⟶ Stacks.underlyingRingSheaf J O)
    (z : (Sheaf.sectionsFunctor J X).obj Z) :
    (Sheaf.sectionsFunctor J X).map (a * b) z =
      (Sheaf.sectionsFunctor J X).map a z * (Sheaf.sectionsFunctor J X).map b z :=
  (congrArg (fun m => (Sheaf.sectionsFunctor J X).map m z)
      ((hom_mul_eq a b).trans
        (Sheaf.hom_mul_eq (R := Stacks.SheafOfModules.Tensor.ringSheaf O) a b).symm)).trans
    (Sheaf.sectionsFunctor_map_hom_mul (R := Stacks.SheafOfModules.Tensor.ringSheaf O) X a b z)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The zero generalized element of `𝒪` takes the value `0` at every section of `Z`. -/
theorem sections_map_zero (z : (Sheaf.sectionsFunctor J X).obj Z) :
    (Sheaf.sectionsFunctor J X).map (0 : Z ⟶ Stacks.underlyingRingSheaf J O) z = 0 :=
  (congrArg (fun m => (Sheaf.sectionsFunctor J X).map m z)
      ((hom_zero_eq (O := O) (Z := Z)).trans
        (Sheaf.hom_ringZero_eq
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (Z := Z)).symm)).trans
    (Sheaf.sectionsFunctor_map_hom_ringZero (R := Stacks.SheafOfModules.Tensor.ringSheaf O) X z)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] in
/-- The unit generalized element of `𝒪` takes the value `1` at every section of `Z`. -/
theorem sections_map_one (z : (Sheaf.sectionsFunctor J X).obj Z) :
    (Sheaf.sectionsFunctor J X).map (1 : Z ⟶ Stacks.underlyingRingSheaf J O) z = 1 := rfl

variable (O Z)

/-- **Evaluating a generalized element of a sheaf of commutative rings at a section.**  A
generalized element `Z ⟶ 𝒪` of shape `Z`, evaluated at a fixed section of `Z` over `X`, gives a
section of `𝒪` over `X`, and taking that value is a ring homomorphism: the operations of the
internal ring structure on the generalized elements are the sectionwise operations of `𝒪`. -/
def sectionsEvalRingHom (z : (Sheaf.sectionsFunctor J X).obj Z) :
    (Z ⟶ Stacks.underlyingRingSheaf J O) →+*
      (Sheaf.sectionsFunctor J X).obj (Stacks.underlyingRingSheaf J O) where
  toFun m := (Sheaf.sectionsFunctor J X).map m z
  map_one' := sections_map_one X z
  map_mul' a b := sections_map_mul X a b z
  map_zero' := sections_map_zero X z
  map_add' a b := sections_map_add X a b z

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `sectionsEvalRingHom O Z X z` sends a generalized element `m` to its value at `z`. -/
theorem sectionsEvalRingHom_apply (z : (Sheaf.sectionsFunctor J X).obj Z)
    (m : Z ⟶ Stacks.underlyingRingSheaf J O) :
    sectionsEvalRingHom O Z X z m = (Sheaf.sectionsFunctor J X).map m z :=
  rfl

/-- **The restriction of a global section of a sheaf of commutative rings to an object of the
site.**  A global generalized element `𝟙 ⟶ 𝒪` is a global section of `𝒪`; this reads it over
`X`, as a ring homomorphism.  It is `sectionsEvalRingHom` at the unique section of the terminal
sheaf. -/
def globalSectionRingHom :
    (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O) →+*
      (Sheaf.sectionsFunctor J X).obj (Stacks.underlyingRingSheaf J O) :=
  sectionsEvalRingHom O (𝟙_ (Sheaf J (Type w))) X
    (default : (Sheaf.sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w))))

variable {O Z}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A constant generalized element is the global section it is constant at, read over `X`. -/
theorem sectionsEvalRingHom_comp_toUnit (z : (Sheaf.sectionsFunctor J X).obj Z)
    (g : 𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O) :
    sectionsEvalRingHom O Z X z (toUnit Z ≫ g) = globalSectionRingHom O X g :=
  ((Sheaf.sectionsFunctor J X).map_comp_apply (toUnit Z) g z).trans
    (congrArg ((Sheaf.sectionsFunctor J X).map g)
      (Subsingleton.elim (α := (Sheaf.sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w)))) _ default))

end Eval

/-! ### The row of a polynomial system, read on sections -/

section Row

variable (O) (X : Cᵒᵖ) {Γ : Type*} [CommRing Γ]
  (c : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The internal evaluation of a polynomial, read on sections, is polynomial evaluation in the
ring of sections.**  The coefficients are the global sections named by `c`, restricted to `X`
along `Stacks.Sheaves.PolynomialSystem.globalSectionRingHom`, and the variables take the values
of the coordinates at the section `z`. -/
theorem sectionsEvalRingHom_evalRingHom {κ : Type*}
    (x : κ → (Z ⟶ Stacks.underlyingRingSheaf J O))
    (z : (Sheaf.sectionsFunctor J X).obj Z) (Q : MvPolynomial κ Γ) :
    sectionsEvalRingHom O Z X z (CommRingObj.evalRingHom _ c x Q) =
      MvPolynomial.eval₂Hom ((globalSectionRingHom O X).comp c)
        (fun i => sectionsEvalRingHom O Z X z (x i)) Q := by
  have key : (sectionsEvalRingHom O Z X z).comp (CommRingObj.evalRingHom _ c x) =
      MvPolynomial.eval₂Hom ((globalSectionRingHom O X).comp c)
        (fun i => sectionsEvalRingHom O Z X z (x i)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · change sectionsEvalRingHom O Z X z (CommRingObj.evalRingHom _ c x (MvPolynomial.C r)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.C r)
      rw [CommRingObj.evalRingHom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        sectionsEvalRingHom_comp_toUnit]
    · change sectionsEvalRingHom O Z X z (CommRingObj.evalRingHom _ c x (MvPolynomial.X i)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i)
      rw [CommRingObj.evalRingHom_X, MvPolynomial.eval₂Hom_X']
  exact RingHom.congr_fun key Q

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The evaluation morphism of a power of `𝒪`, read on sections: a section of `∏ᵏ 𝒪` over `X` is
a `κ`-tuple of sections of `𝒪`, and the value of `Q` at it is the honest value of `Q` at that
tuple. -/
theorem sections_map_evalPowRingHom (κ : Type*)
    [HasProduct fun _ : κ => Stacks.underlyingRingSheaf J O]
    (l : (Sheaf.sectionsFunctor J X).obj (∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf J O))
    (Q : MvPolynomial κ Γ) :
    (Sheaf.sectionsFunctor J X).map (CommRingObj.evalPowRingHom _ c κ Q) l =
      MvPolynomial.eval₂Hom ((globalSectionRingHom O X).comp c)
        (fun i => (Sheaf.sectionsFunctor J X).map (Pi.π _ i) l) Q :=
  sectionsEvalRingHom_evalRingHom O X c (Pi.π (fun _ : κ => Stacks.underlyingRingSheaf J O)) l Q

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The two legs of the row agree at a section of `∏ᵏ 𝒪` exactly when its coordinates solve the
system.**  This is the vanishing condition that the equalizer of the row cuts out, read over a
single object of the site. -/
theorem sections_evalSystemHom_eq_zeroSystemHom_iff (κ : Type) [Finite κ] (ν : Type) [Finite ν]
    (P : ν → MvPolynomial κ Γ)
    (l : (Sheaf.sectionsFunctor.{w} J X).obj (∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf J O)) :
    (Sheaf.sectionsFunctor.{w} J X).map (CommRingObj.evalSystemHom _ c κ P) l =
        (Sheaf.sectionsFunctor.{w} J X).map (CommRingObj.zeroSystemHom _ κ ν) l ↔
      ∀ j, MvPolynomial.eval₂Hom ((globalSectionRingHom O X).comp c)
        (fun i => (Sheaf.sectionsFunctor.{w} J X).map (Pi.π _ i) l) (P j) = 0 := by
  have hcomp : ∀ j : ν,
      (Sheaf.sectionsFunctor.{w} J X).map
          (Pi.π (fun _ : ν => Stacks.underlyingRingSheaf J O) j)
          ((Sheaf.sectionsFunctor.{w} J X).map (CommRingObj.evalSystemHom _ c κ P) l) =
        MvPolynomial.eval₂Hom ((globalSectionRingHom O X).comp c)
          (fun i => (Sheaf.sectionsFunctor.{w} J X).map (Pi.π _ i) l) (P j) := fun j => by
    rw [← Functor.map_comp_apply, CommRingObj.evalSystemHom_comp_π,
      sections_map_evalPowRingHom]
  have hzero : ∀ j : ν,
      (Sheaf.sectionsFunctor.{w} J X).map
          (Pi.π (fun _ : ν => Stacks.underlyingRingSheaf J O) j)
          ((Sheaf.sectionsFunctor.{w} J X).map (CommRingObj.zeroSystemHom _ κ ν) l) = 0 :=
      fun j => by
    rw [← Functor.map_comp_apply, CommRingObj.zeroSystemHom_comp_π, sections_map_zero]
  refine ⟨fun h j => ?_, fun h => Functor.piObjMk_ext (fun j => ?_)⟩
  · rw [← hcomp j, h, hzero j]
  · rw [hcomp j, hzero j, h j]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The same for a square system indexed by `Fin n`, in the spelling `MvPolynomial.IsSolution`
that [Stacks Project, Tag 04GX] uses for its two solution sets. -/
theorem sections_row_eq_iff_isSolution {n : ℕ} (P : Fin n → MvPolynomial (Fin n) Γ)
    (l : (Sheaf.sectionsFunctor.{w} J X).obj (∏ᶜ fun _ : Fin n => Stacks.underlyingRingSheaf J O)) :
    (Sheaf.sectionsFunctor.{w} J X).map (CommRingObj.evalSystemHom _ c (Fin n) P) l =
        (Sheaf.sectionsFunctor.{w} J X).map (CommRingObj.zeroSystemHom _ (Fin n) (Fin n)) l ↔
      MvPolynomial.IsSolution P ((globalSectionRingHom O X).comp c)
        (fun i => (Sheaf.sectionsFunctor.{w} J X).map (Pi.π _ i) l) := by
  rw [sections_evalSystemHom_eq_zeroSystemHom_iff]
  exact ⟨fun h j => (MvPolynomial.eval_map _ _ _).trans (h j),
    fun h j => (MvPolynomial.eval_map _ _ _).symm.trans (h j)⟩

end Row

/-! ### The equalizer presentation -/

section Fork

variable (O) {Γ : Type*} [CommRing Γ]
  (c : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O))
  {H : Sheaf J (Type w)} {n : ℕ} (P : Fin n → MvPolynomial (Fin n) Γ)
  (ι : H ⟶ ∏ᶜ fun _ : Fin n => Stacks.underlyingRingSheaf J O)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The fork condition of a polynomial system is a sectionwise vanishing condition.**  If over
every object of the site the coordinates of a section of `H`, read through `ι`, solve the system,
then `ι` equalizes the two legs of the row. -/
theorem comp_evalSystemHom_eq_comp_zeroSystemHom
    (h : ∀ (X : Cᵒᵖ) (t : (Sheaf.sectionsFunctor J X).obj H),
      MvPolynomial.IsSolution P ((globalSectionRingHom O X).comp c)
        (fun i => (Sheaf.sectionsFunctor J X).map (ι ≫ Pi.π _ i) t)) :
    ι ≫ CommRingObj.evalSystemHom _ c (Fin n) P =
      ι ≫ CommRingObj.zeroSystemHom _ (Fin n) (Fin n) := by
  refine Sheaf.hom_ext_sections (fun X t => ?_)
  have hfun : (fun i => (Sheaf.sectionsFunctor J X).map
        (ι ≫ Pi.π (fun _ : Fin n => Stacks.underlyingRingSheaf J O) i) t) =
      fun i => (Sheaf.sectionsFunctor J X).map
        (Pi.π (fun _ : Fin n => Stacks.underlyingRingSheaf J O) i)
        ((Sheaf.sectionsFunctor J X).map ι t) :=
    funext fun i => (Sheaf.sectionsFunctor J X).map_comp_apply ι (Pi.π _ i) t
  rw [Functor.map_comp_apply, Functor.map_comp_apply]
  exact (sections_row_eq_iff_isSolution O X c P _).2 (hfun ▸ h X t)

/-- **The equalizer presentation of a sheaf cut out by a polynomial system.**  Let `𝒪` be a sheaf
of commutative rings on a site, let `P₁, …, P_n` be polynomials in `n` variables with
coefficients read into the global sections of `𝒪`, and let `ι : H ⟶ ∏ⁿ 𝒪` be a morphism which
over every object of the site is injective with image exactly the solutions of the system.  Then
`H` is the equalizer of the two legs `∏ⁿ 𝒪 ⇉ ∏ⁿ 𝒪` of the row of the system.

This is step (2) of the proof of [Stacks Project, Tag 04I6] at the level of sheaves: the
set-level identification of the sections of `H` with the solution sets is the hypothesis, and the
conclusion is the limit in the category of sheaves.  Nothing here is special to the étale
topology, to schemes, or to a square system; it is the transfer
`CategoryTheory.Sheaf.isLimitForkOfForallApp` fed with
`Stacks.Sheaves.PolynomialSystem.sections_row_eq_iff_isSolution`. -/
def isLimitForkOfSections
    (hinj : ∀ X : Cᵒᵖ, Function.Injective (ι.hom.app X))
    (hsurj : ∀ (X : Cᵒᵖ)
      (l : (Sheaf.sectionsFunctor.{w} J X).obj
        (∏ᶜ fun _ : Fin n => Stacks.underlyingRingSheaf J O)),
      MvPolynomial.IsSolution P ((globalSectionRingHom O X).comp c)
          (fun i => (Sheaf.sectionsFunctor.{w} J X).map (Pi.π _ i) l) →
        ∃ t, ι.hom.app X t = l)
    (hcond : ι ≫ CommRingObj.evalSystemHom _ c (Fin n) P =
      ι ≫ CommRingObj.zeroSystemHom _ (Fin n) (Fin n)) :
    IsLimit (Fork.ofι ι hcond) :=
  Sheaf.isLimitForkOfForallApp hinj
    (fun X l hl => hsurj X l ((sections_row_eq_iff_isSolution O X c P l).1 hl)) hcond

end Fork

end Stacks.Sheaves.PolynomialSystem

end
