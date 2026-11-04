module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.EtaleLifting

/-!
# Points of a standard presentation are solutions of its equations

Let `R` be a ring and let `P₁, …, P_n ∈ R[x₁, …, x_n]` be polynomials.  Write
`A = R[x₁, …, x_n]/(P₁, …, P_n)` for the quotient they present.  For any ring `A'` and any ring
map `g : R ⟶ A'` the `R`-points of `A` in `A'` — the ring maps `A ⟶ A'` lying over `g` — are the
same thing as the solutions in `A'` of the system obtained from the `Pⱼ` by applying `g` to their
coefficients:

`{φ : A →+* A' // φ ∘ (structure map) = g} ≃ {a : Fin n → A' // ∀ j, (g Pⱼ)(a) = 0}`.

This is the elementary half of the second step of the proof of [Stacks Project, Tag 04I6]: for
`V = Spec C` étale over `Y = Spec B` with a standard presentation
`C = B[x₁, …, x_n]/(P₁, …, P_n)`, the representable sheaf `h_V` on the small étale site of `Y` is
the equalizer of two maps `∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y`, one of them `a ↦ (Pⱼ(a))ⱼ` and the other the zero
section.  That equalizer presentation is the identification above, read at the ring of global
functions of a varying étale chart; the geometric half, which turns a morphism of schemes into
such a ring map, is `Stacks.EtaleCohomology.homOverEquivSolutions`.

Composed with [Stacks Project, Tag 04GX], the identification gives
`MvPolynomial.bijective_homOverMap_of_etale`: for a local homomorphism of strictly henselian
local rings, the points of a standard *étale* presentation are carried bijectively from the
source to the target.  In the geometry of Stacks 04I6 this says that the comparison map
`g⁻¹h_V ⟶ h_{X ×_Y V}` is bijective on stalks.

## Main definitions

* `MvPolynomial.quotientSpanRangeStructureMap` — the structure map
  `R ⟶ R[x₁, …, x_n]/(P₁, …, P_n)`, namely `C` followed by the quotient map.
* `MvPolynomial.IsSolution` — the predicate on `a : Fin n → A` that every `g Pⱼ` vanishes at `a`.
* `MvPolynomial.HomOver` — the points of the presentation lying over a given `g : R →+* A`.
* `MvPolynomial.solutionOfHomOver` and `MvPolynomial.homOverOfSolution` — the two directions,
  reading off the images of the variables and lifting an evaluation through the quotient.
* `MvPolynomial.quotientSpanRangeHomOverEquiv` — the bijection above.
* `MvPolynomial.homOverMap` — postcomposition of a point with a ring map.

## Main results

* `MvPolynomial.solutionOfHomOver_homOverMap` — the bijection is natural: postcomposing a point
  with a ring map applies that ring map to the solution coordinatewise.
* `MvPolynomial.bijective_homOverMap_of_etale` — [Stacks Project, Tag 04GX] read on the points
  of a standard presentation: for a local homomorphism `φ : R' ⟶ S'` of strictly henselian
  local rings and a standard presentation which is étale over `R'`, postcomposition with `φ` is a
  bijection from the points of the presentation with values in `R'` onto those with values
  in `S'`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public noncomputable section

universe u v w

namespace MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R)

/-- The structure map `R ⟶ R[x₁, …, x_n]/(P₁, …, P_n)`: a constant polynomial, read in the
quotient. -/
def quotientSpanRangeStructureMap :
    R →+* (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)) :=
  (Ideal.Quotient.mk (Ideal.span (Set.range P))).comp MvPolynomial.C

/-- The structure map sends `r` to the class of the constant polynomial `C r`. -/
@[simp]
theorem quotientSpanRangeStructureMap_apply (r : R) :
    quotientSpanRangeStructureMap P r =
      Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.C r) :=
  rfl

/-- Each defining polynomial is zero in the quotient it defines. -/
@[simp]
theorem quotientSpanRange_mk_eq_zero (j : Fin n) :
    Ideal.Quotient.mk (Ideal.span (Set.range P)) (P j) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨j, rfl⟩

variable {A : Type v} [CommRing A]

/-- `a : Fin n → A` **is a solution** of the system `P` transported along `g : R →+* A` when every
polynomial `g Pⱼ` vanishes at `a`. -/
def IsSolution (g : R →+* A) (a : Fin n → A) : Prop :=
  ∀ j, MvPolynomial.eval a (MvPolynomial.map g (P j)) = 0

/-- Being a solution is the vanishing of the `eval₂` of every `Pⱼ` at `a` over `g`. -/
theorem isSolution_iff_forall_eval₂ (g : R →+* A) (a : Fin n → A) :
    IsSolution P g a ↔ ∀ j, MvPolynomial.eval₂ g a (P j) = 0 := by
  simp only [IsSolution, MvPolynomial.eval_map]

/-- The ring maps out of the quotient `R[x]/(P)` which lie over a prescribed `g : R →+* A`: the
points of the presentation with values in `A`. -/
abbrev HomOver (g : R →+* A) : Type _ :=
  {φ : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)) →+* A //
    φ.comp (quotientSpanRangeStructureMap P) = g}

section Equiv

variable {P} (g : R →+* A)

/-- `eval₂ g a` and `φ ∘ mk` are the same ring map, when `a` is the tuple of images of the
variables under a point `φ` of the presentation. -/
theorem eval₂Hom_eq_comp_mk (φ : HomOver P g) :
    MvPolynomial.eval₂Hom g
        (fun i => φ.1 (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i))) =
      φ.1.comp (Ideal.Quotient.mk (Ideal.span (Set.range P))) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · rw [MvPolynomial.eval₂Hom_C]
    exact (congrFun (congrArg (fun f : R →+* A => (f : R → A)) φ.2) r).symm
  · rw [MvPolynomial.eval₂Hom_X']
    rfl

/-- **The solution named by a point of the presentation**: the images of the variables. -/
def solutionOfHomOver (φ : HomOver P g) : {a : Fin n → A // IsSolution P g a} :=
  ⟨fun i => φ.1 (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)), fun j => by
    rw [show MvPolynomial.eval
          (fun i => φ.1 (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)))
          (MvPolynomial.map g (P j)) =
        MvPolynomial.eval₂Hom g
          (fun i => φ.1 (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)))
          (P j) from MvPolynomial.eval_map _ _ _, eval₂Hom_eq_comp_mk g φ,
      show (φ.1.comp (Ideal.Quotient.mk (Ideal.span (Set.range P)))) (P j) =
        φ.1 (Ideal.Quotient.mk (Ideal.span (Set.range P)) (P j)) from rfl,
      quotientSpanRange_mk_eq_zero, map_zero]⟩

/-- The `i`-th coordinate of the solution named by `φ` is the image under `φ` of the class of the
variable `X i`. -/
@[simp]
theorem solutionOfHomOver_coe (φ : HomOver P g) (i : Fin n) :
    (solutionOfHomOver g φ).1 i =
      φ.1 (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)) :=
  rfl

/-- The defining ideal of the presentation is killed by evaluation at a solution. -/
theorem span_range_le_ker_eval₂Hom {a : Fin n → A} (ha : IsSolution P g a) :
    Ideal.span (Set.range P) ≤ RingHom.ker (MvPolynomial.eval₂Hom g a) := by
  refine Ideal.span_le.2 ?_
  rintro y ⟨j, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker,
    show MvPolynomial.eval₂Hom g a (P j) =
      MvPolynomial.eval a (MvPolynomial.map g (P j)) from (MvPolynomial.eval_map _ _ _).symm]
  exact ha j

/-- Evaluation at a solution, read as a ring map out of the quotient: it factors through the
quotient exactly because the defining polynomials vanish at the solution. -/
def eval₂HomQuotient (a : {a : Fin n → A // IsSolution P g a}) :
    (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)) →+* A :=
  Ideal.Quotient.lift (Ideal.span (Set.range P)) (MvPolynomial.eval₂Hom g a.1)
    (fun _ hx => span_range_le_ker_eval₂Hom g a.2 hx)

/-- Evaluation at a solution, on the class of a polynomial `p`, is `eval₂Hom g a p`. -/
@[simp]
theorem eval₂HomQuotient_mk (a : {a : Fin n → A // IsSolution P g a})
    (p : MvPolynomial (Fin n) R) :
    eval₂HomQuotient g a (Ideal.Quotient.mk (Ideal.span (Set.range P)) p) =
      MvPolynomial.eval₂Hom g a.1 p :=
  Ideal.Quotient.lift_mk _ _ _

/-- **The point of the presentation named by a solution**: evaluation at the solution. -/
def homOverOfSolution (a : {a : Fin n → A // IsSolution P g a}) : HomOver P g :=
  ⟨eval₂HomQuotient g a, RingHom.ext fun r => by
    change eval₂HomQuotient g a
      (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.C r)) = g r
    rw [eval₂HomQuotient_mk, MvPolynomial.eval₂Hom_C]⟩

/-- The point named by a solution `a` sends the class of a polynomial `p` to `eval₂Hom g a p`. -/
@[simp]
theorem homOverOfSolution_apply_mk (a : {a : Fin n → A // IsSolution P g a})
    (p : MvPolynomial (Fin n) R) :
    (homOverOfSolution g a).1 (Ideal.Quotient.mk (Ideal.span (Set.range P)) p) =
      MvPolynomial.eval₂Hom g a.1 p :=
  eval₂HomQuotient_mk g a p

/-- **The points of a standard presentation are the solutions of its equations.** For a ring map
`g : R ⟶ A`, the ring maps `R[x₁, …, x_n]/(P₁, …, P_n) ⟶ A` lying over `g` correspond to the
tuples `a : Fin n → A` at which every `g Pⱼ` vanishes, a point going to the images of the
variables. -/
@[ega "IV 18.5.2" "special case"]
def quotientSpanRangeHomOverEquiv :
    HomOver P g ≃ {a : Fin n → A // IsSolution P g a} where
  toFun := solutionOfHomOver g
  invFun := homOverOfSolution g
  left_inv φ := by
    refine Subtype.ext (RingHom.ext fun x => ?_)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [homOverOfSolution_apply_mk]
    exact congrArg (fun f : MvPolynomial (Fin n) R →+* A => f p) (eval₂Hom_eq_comp_mk g φ)
  right_inv a := by
    refine Subtype.ext (funext fun i => ?_)
    rw [solutionOfHomOver_coe, homOverOfSolution_apply_mk, MvPolynomial.eval₂Hom_X']

/-- The equivalence sends a point of the presentation to the solution it names. -/
@[simp]
theorem quotientSpanRangeHomOverEquiv_apply (φ : HomOver P g) :
    quotientSpanRangeHomOverEquiv g φ = solutionOfHomOver g φ :=
  rfl

/-- The inverse equivalence sends a solution to the point of the presentation it names. -/
@[simp]
theorem quotientSpanRangeHomOverEquiv_symm_apply
    (a : {a : Fin n → A // IsSolution P g a}) :
    (quotientSpanRangeHomOverEquiv g).symm a = homOverOfSolution g a :=
  rfl

end Equiv

section Map

variable {P} {A' : Type w} [CommRing A']

/-- Postcomposing a point of the presentation with a ring map `ψ : A ⟶ A'` is a point over the
composite structure map. -/
def homOverMap (g : R →+* A) (ψ : A →+* A') (φ : HomOver P g) : HomOver P (ψ.comp g) :=
  ⟨ψ.comp φ.1, by rw [RingHom.comp_assoc, φ.2]⟩

/-- **The identification is natural.**  The solution named by a point postcomposed with `ψ` is
the image under `ψ` of the solution named by the point, coordinatewise. -/
theorem solutionOfHomOver_homOverMap (g : R →+* A) (ψ : A →+* A') (φ : HomOver P g) :
    (solutionOfHomOver (ψ.comp g) (homOverMap g ψ φ)).1 =
      fun i => ψ ((solutionOfHomOver g φ).1 i) :=
  rfl

/-- The image of a solution under a ring map is a solution of the transported system. -/
theorem isSolution_comp (g : R →+* A) (ψ : A →+* A') {a : Fin n → A}
    (ha : IsSolution P g a) : IsSolution P (ψ.comp g) (fun i => ψ (a i)) := by
  intro j
  have h : MvPolynomial.eval (fun i => ψ (a i)) (MvPolynomial.map (ψ.comp g) (P j)) =
      ψ (MvPolynomial.eval a (MvPolynomial.map g (P j))) := by
    rw [MvPolynomial.eval_map, MvPolynomial.eval_map,
      MvPolynomial.eval₂_comp_left ψ g a (P j)]
    rfl
  rw [h, ha j, map_zero]

end Map

/-! ### Stacks 04GX, read on the points of a standard presentation -/

section Etale

variable {R' S' : Type u} [CommRing R'] [CommRing S'] [HenselianLocalRing R']
  [HenselianLocalRing S'] [IsSepClosed (IsLocalRing.ResidueField R')]
  [IsSepClosed (IsLocalRing.ResidueField S')]

omit [HenselianLocalRing R'] [IsSepClosed (IsLocalRing.ResidueField R')] in
/-- Over the identity structure map, being a solution is vanishing of the `Pⱼ` themselves — the
spelling in which [Stacks Project, Tag 04GX] states its source solution set. -/
theorem isSolution_id_iff {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R') (a : Fin n → R') :
    IsSolution P (RingHom.id R') a ↔ ∀ j, MvPolynomial.eval a (P j) = 0 :=
  forall_congr' fun j => by rw [MvPolynomial.map_id]

/-- Let `φ : R' ⟶ S'` be a local homomorphism of strictly henselian local rings and let
`P₁, …, P_n ∈ R'[x₁, …, x_n]` present a ring `R'[x]/(P)` which is étale over `R'`.  Then
postcomposition with `φ` is a bijection from the points of the presentation with values in `R'`
onto its points with values in `S'`: Stacks Tag 04GX, read on the points of a standard
presentation. -/
theorem bijective_homOverMap_of_etale
    {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R') (φ : R' →+* S') (hφ : IsLocalHom φ)
    [Algebra.Etale R' (MvPolynomial (Fin n) R' ⧸ Ideal.span (Set.range P))] :
    Function.Bijective
      (fun p : HomOver P (RingHom.id R') =>
        (⟨φ.comp p.1, by rw [RingHom.comp_assoc, p.2, RingHom.comp_id]⟩ :
          HomOver P φ)) := by
  have hbij := bijOn_solutions_of_etale φ hφ n P
  set G : {a : Fin n → R' // IsSolution P (RingHom.id R') a} →
      {s : Fin n → S' // IsSolution P φ s} := fun a =>
    ⟨fun i => φ (a.1 i), hbij.1 ((isSolution_id_iff P a.1).1 a.2)⟩ with hGdef
  have key : ∀ p : HomOver P (RingHom.id R'),
      quotientSpanRangeHomOverEquiv φ
          (⟨φ.comp p.1, by rw [RingHom.comp_assoc, p.2, RingHom.comp_id]⟩ : HomOver P φ) =
        G (quotientSpanRangeHomOverEquiv (RingHom.id R') p) := fun _ => rfl
  have hGinj : Function.Injective G := by
    intro a b hab
    refine Subtype.ext (hbij.2.1 ((isSolution_id_iff P a.1).1 a.2)
      ((isSolution_id_iff P b.1).1 b.2) (funext fun i => ?_))
    exact congrFun (congrArg Subtype.val hab) i
  have hGsurj : Function.Surjective G := by
    intro s
    obtain ⟨a, ha, hae⟩ := hbij.2.2 (show s.1 ∈ {t : Fin n → S' |
      ∀ j, MvPolynomial.eval t (MvPolynomial.map φ (P j)) = 0} from s.2)
    exact ⟨⟨a, (isSolution_id_iff P a).2 ha⟩, Subtype.ext hae⟩
  refine ⟨fun p q hpq => ?_, fun r => ?_⟩
  · refine (quotientSpanRangeHomOverEquiv (P := P) (RingHom.id R')).injective (hGinj ?_)
    rw [← key p, ← key q]
    exact congrArg (quotientSpanRangeHomOverEquiv φ) hpq
  · obtain ⟨s, hs⟩ := hGsurj (quotientSpanRangeHomOverEquiv φ r)
    refine ⟨(quotientSpanRangeHomOverEquiv (P := P) (RingHom.id R')).symm s, ?_⟩
    refine (quotientSpanRangeHomOverEquiv (P := P) φ).injective ?_
    rw [key, Equiv.apply_symm_apply]
    exact hs

end Etale

end MvPolynomial

end
