module

public import StacksFrontier.AlgebraicGeometry.DeRham.SheafLogLeibniz
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapDeRham

/-!
# Wedging with an exact one-form, for relative differential forms of a morphism of schemes

Let `f : X ⟶ S` be a morphism of schemes. For a local function `c` and a local relative
`p`-form `β` over an open `V` of `X`, this file names the `(p + 1)`-form `dc ∧ β`
(`AlgebraicGeometry.Scheme.Hom.exactWedge`) and records the calculus of it that the de Rham
complex of log poles of [Stacks, Tag 0FMW] is computed with:

* it is additive in `β`, `𝒪_X`-linear in `β`, additive in `c`, and satisfies
  `d(r c) ∧ β = r (dc ∧ β) + c (dr ∧ β)`;
* it commutes with restriction to smaller opens;
* `dc ∧ dc ∧ β = 0`;
* restricting to a closed subscheme `i : Z ⟶ X` carries `dc ∧ β` to `d(c|_Z) ∧ β|_Z`
  (`AlgebraicGeometry.Scheme.Hom.formRestriction_exactWedge`);
* the Leibniz rules `d(c β) = dc ∧ β + c dβ` and `d(dc ∧ β) = - dc ∧ dβ` for the relative de Rham
  differential (`AlgebraicGeometry.Scheme.Hom.deRhamD_smul` and
  `AlgebraicGeometry.Scheme.Hom.deRhamD_exactWedge`).

All of these are instances, for the package `AlgebraicGeometry.Scheme.Hom.deRhamAlgebras f`, of
statements about an arbitrary exterior algebra of `Ω` on a ringed space, except the restriction
to a closed subscheme, which goes through the multiplicativity of the pullback of forms.

## Implementation notes

The degree of `dc ∧ β` is written `p + 1` rather than `1 + p`, through
`AlgebraicGeometry.SheafOfModules.reindexForm`, as in
`StacksFrontier.AlgebraicGeometry.DeRham.SheafLogLeibniz`; that is the degree the de Rham
differential lands in.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.SheafOfModules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The form `dc ∧ β`** of degree `p + 1`, for a local function `c` and a local relative
`p`-form `β` over an open `V`. -/
def exactWedge (p : ℕ) (V : X.Opens) (c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V) :=
  reindexForm (deRhamAlgebras f) (Nat.add_comm 1 p) (op V)
    (formProduct (deRhamAlgebras f) 1 p (op V) (exactOne (deRhamAlgebras f) (op V) c) β)

/-- **The relative de Rham differential on local sections**,
`d : Ω^p_{X/S}(V) → Ω^{p+1}_{X/S}(V)`. -/
abbrev deRhamD (p : ℕ) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V) :=
  ((deRhamComplex f).d p (p + 1)).val.app (op V) ω

variable {f}

/-- `dc ∧ (β + β') = dc ∧ β + dc ∧ β'`. -/
theorem exactWedge_add_right (p : ℕ) (V : X.Opens) (c : Γ(X, V))
    (β β' : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    exactWedge f p V c (β + β') = exactWedge f p V c β + exactWedge f p V c β' :=
  AlgebraicGeometry.SheafOfModules.exactWedge_add_right (deRhamAlgebras f) p (op V) c β β'

/-- `dc ∧ (r β) = r (dc ∧ β)` for a local function `r`. -/
theorem exactWedge_smul_right (p : ℕ) (V : X.Opens) (r c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    exactWedge f p V c (r • β) = r • exactWedge f p V c β :=
  AlgebraicGeometry.SheafOfModules.exactWedge_smul_right (deRhamAlgebras f) p (op V) r c β

/-- `d(c + c') ∧ β = dc ∧ β + dc' ∧ β`. -/
theorem exactWedge_add_left (p : ℕ) (V : X.Opens) (c c' : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    exactWedge f p V (c + c') β = exactWedge f p V c β + exactWedge f p V c' β :=
  AlgebraicGeometry.SheafOfModules.exactWedge_add_left (deRhamAlgebras f) p (op V) c c' β

/-- `d(r c) ∧ β = r (dc ∧ β) + c (dr ∧ β)`. -/
theorem exactWedge_mul_left (p : ℕ) (V : X.Opens) (r c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    exactWedge f p V (r * c) β = r • exactWedge f p V c β + c • exactWedge f p V r β :=
  AlgebraicGeometry.SheafOfModules.exactWedge_mul_left (deRhamAlgebras f) p (op V) r c β

/-- `dc ∧ 0 = 0`. -/
theorem exactWedge_zero_right (p : ℕ) (V : X.Opens) (c : Γ(X, V)) :
    exactWedge f p V c 0 = 0 := by
  simpa using exactWedge_add_right (f := f) p V c 0 0

/-- `dc ∧ (-β) = -(dc ∧ β)`. -/
theorem exactWedge_neg_right (p : ℕ) (V : X.Opens) (c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    exactWedge f p V c (-β) = -exactWedge f p V c β :=
  eq_neg_of_add_eq_zero_left (by
    rw [← exactWedge_add_right, neg_add_cancel, exactWedge_zero_right])

/-- `dc ∧ (β - β') = dc ∧ β - dc ∧ β'`. -/
theorem exactWedge_sub_right (p : ℕ) (V : X.Opens) (c : Γ(X, V))
    (β β' : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    exactWedge f p V c (β - β') = exactWedge f p V c β - exactWedge f p V c β' := by
  rw [sub_eq_add_neg, exactWedge_add_right, exactWedge_neg_right, ← sub_eq_add_neg]

/-- `d0 ∧ β = 0`. -/
theorem exactWedge_zero_left (p : ℕ) (V : X.Opens)
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    exactWedge f p V 0 β = 0 := by
  simpa using exactWedge_add_left (f := f) p V 0 0 β

/-- `dc ∧ β` commutes with restriction to a smaller open. -/
theorem exactWedge_res (p : ℕ) {V W : X.Opens} (h : W ≤ V) (c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h).op
        (exactWedge f p V c β) =
      exactWedge f p W (X.presheaf.map (homOfLE h).op c)
        ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op β) :=
  AlgebraicGeometry.SheafOfModules.exactWedge_map (deRhamAlgebras f) (homOfLE h).op p c β

attribute [local instance] gradedFormsGOne gradedFormsGMul gradedFormsGRing in
/-- **`dc ∧ dc ∧ β = 0`.** -/
theorem exactWedge_exactWedge_self (p : ℕ) (V : X.Opens) (c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    exactWedge f (p + 1) V c (exactWedge f p V c β) = 0 := by
  let B := deRhamAlgebras f
  refine DirectSum.of_injective (β := gradedForms B (op V)) ((p + 1 + 1 : ℕ) : ℤ) ?_
  have hof (q : ℕ) (γ : Γ(relativeDifferentialForms f (q : ℤ), V)) :
      ofGradedForm B (op V) ((q + 1 : ℕ) : ℤ) (exactWedge f q V c γ) =
        exactForm B (op V) c * ofGradedForm B (op V) (q : ℤ) γ :=
    (ofGradedForm_reindexForm B (Nat.add_comm 1 q) (op V) _).trans
      (ofGradedForm_mul B (op V) 1 (q : ℤ) _ γ)
  have hout : ofGradedForm B (op V) ((p + 1 + 1 : ℕ) : ℤ)
      (exactWedge f (p + 1) V c (exactWedge f p V c β)) =
        exactForm B (op V) c * (exactForm B (op V) c * ofGradedForm B (op V) (p : ℤ) β) :=
    (hof (p + 1) _).trans (congrArg (fun z => exactForm B (op V) c * z) (hof p β))
  refine hout.trans ((mul_assoc _ _ _).symm.trans ?_)
  refine (congrArg (fun z => z * ofGradedForm B (op V) (p : ℤ) β)
    (exactForm_mul_self B (op V) c)).trans ?_
  exact (zero_mul _).trans (map_zero (DirectSum.of (gradedForms B (op V)) _)).symm


/-! ### The Leibniz rules -/

/-- **The Leibniz rule against a scalar**, `d(r β) = dr ∧ β + r dβ`. -/
theorem deRhamD_smul (p : ℕ) (V : X.Opens) (r : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    deRhamD f p V (r • β) = exactWedge f p V r β + r • deRhamD f p V β :=
  dForm_smul (deRhamAlgebras f) (deRhamDifferential (deRhamAlgebras f)) p (op V) r β

/-- **`d(dc ∧ β) = - dc ∧ dβ`.** -/
theorem deRhamD_exactWedge (p : ℕ) (V : X.Opens) (c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    deRhamD f (p + 1) V (exactWedge f p V c β) = -exactWedge f (p + 1) V c (deRhamD f p V β) :=
  dForm_exactWedge (deRhamAlgebras f) (deRhamDifferential (deRhamAlgebras f)) p (op V) c β

/-- The differential on local sections commutes with restriction to a smaller open. -/
theorem deRhamD_res (p : ℕ) {V W : X.Opens} (h : W ≤ V)
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map (homOfLE h).op (deRhamD f p V β) =
      deRhamD f p W ((relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op β) :=
  dForm_map (deRhamAlgebras f) (deRhamDifferential (deRhamAlgebras f)) (homOfLE h).op p β

/-- `d ∘ d = 0` on local sections. -/
theorem deRhamD_deRhamD (p : ℕ) (V : X.Opens)
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    deRhamD f (p + 1) V (deRhamD f p V β) = 0 :=
  _root_.SheafOfModules.hom_congr_app_apply ((deRhamComplex f).d_comp_d p (p + 1) (p + 2))
    (op V) β

/-- The differential on local sections is additive: `d(β + β') = dβ + dβ'`. -/
theorem deRhamD_add (p : ℕ) (V : X.Opens)
    (β β' : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    deRhamD f p V (β + β') = deRhamD f p V β + deRhamD f p V β' :=
  map_add _ _ _

/-- `d(β - β') = dβ - dβ'` on local sections. -/
theorem deRhamD_sub (p : ℕ) (V : X.Opens)
    (β β' : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    deRhamD f p V (β - β') = deRhamD f p V β - deRhamD f p V β' :=
  map_sub _ _ _

/-! ### Restriction to a closed subscheme -/

variable {Z : Scheme.{u}} (i : Z ⟶ X)

/-- **Restricting `dc ∧ β` to a subscheme gives `d(c|_Z) ∧ β|_Z`.** -/
theorem formRestriction_exactWedge (p : ℕ) (V : X.Opens) (c : Γ(X, V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    (formRestriction i f ((p + 1 : ℕ) : ℤ)).val.app (op V) (exactWedge f p V c β) =
      exactWedge (i ≫ f) p (i ⁻¹ᵁ V) ((i.app V).hom c)
        ((formRestriction i f (p : ℤ)).val.app (op V) β) := by
  have hcomm : i ≫ f = (i ≫ f) ≫ 𝟙 S := (Category.comp_id _).symm
  have hL : HEq ((formRestriction i f ((p + 1 : ℕ) : ℤ)).val.app (op V) (exactWedge f p V c β))
      (((relativeDifferentialFormsAlgebra (i ≫ f)).mul 1 (p : ℤ)).app (op (i ⁻¹ᵁ V))
        (exactOne (deRhamAlgebras (i ≫ f)) (op (i ⁻¹ᵁ V)) ((i.app V).hom c))
        ((formRestriction i f (p : ℤ)).val.app (op V) β)) :=
    HEq.trans
      (relativeDifferentialFormsPullback_heq i f (i ≫ f) (𝟙 S) hcomm
        (show ((p + 1 : ℕ) : ℤ) = 1 + (p : ℤ) by push_cast; ring) V
        (reindexForm_heq (deRhamAlgebras f) (Nat.add_comm 1 p) (op V) _))
      (heq_of_eq (Eq.trans
        (relativeDifferentialFormsPullback_mul i f (i ≫ f) (𝟙 S) hcomm 1 (p : ℤ) V _ β)
        (congrArg (fun z => ((relativeDifferentialFormsAlgebra (i ≫ f)).mul 1 (p : ℤ)).app
            (op (i ⁻¹ᵁ V)) z (relativeDifferentialFormsPullback i f (i ≫ f) (𝟙 S) hcomm
              (p : ℤ) V β))
          (relativeDifferentialFormsPullback_exactOne i f (i ≫ f) (𝟙 S) hcomm V c))))
  exact eq_of_heq (hL.trans (reindexForm_heq (deRhamAlgebras (i ≫ f)) (Nat.add_comm 1 p)
    (op (i ⁻¹ᵁ V)) _).symm)

/-- The restriction `β|_Z ∈ Ω^n_{Z/S}(i⁻¹V)` of a local form to the subscheme. -/
abbrev formRes (n : ℤ) (V : X.Opens) (β : Γ(relativeDifferentialForms f n, V)) :
    Γ(relativeDifferentialForms (i ≫ f) n, i ⁻¹ᵁ V) :=
  (formRestriction i f n).val.app (op V) β

/-- Restriction to the subscheme is additive: `(β + β')|_Z = β|_Z + β'|_Z`. -/
theorem formRes_add (n : ℤ) (V : X.Opens) (β β' : Γ(relativeDifferentialForms f n, V)) :
    formRes i n V (β + β') = formRes i n V β + formRes i n V β' :=
  map_add _ _ _

/-- `(-β)|_Z = -(β|_Z)`. -/
theorem formRes_neg (n : ℤ) (V : X.Opens) (β : Γ(relativeDifferentialForms f n, V)) :
    formRes i n V (-β) = -formRes i n V β :=
  map_neg _ _

/-- `(β - β')|_Z = β|_Z - β'|_Z`. -/
theorem formRes_sub (n : ℤ) (V : X.Opens) (β β' : Γ(relativeDifferentialForms f n, V)) :
    formRes i n V (β - β') = formRes i n V β - formRes i n V β' :=
  map_sub _ _ _

/-- The restriction of the zero form is zero. -/
theorem formRes_zero (n : ℤ) (V : X.Opens) :
    formRes i n V (0 : Γ(relativeDifferentialForms f n, V)) = 0 :=
  map_zero _

/-- **Restriction to a subscheme is semilinear** over restriction of functions. -/
theorem formRes_smul (n : ℤ) (V : X.Opens) (r : Γ(X, V))
    (β : Γ(relativeDifferentialForms f n, V)) :
    formRes i n V (r • β) = (i.app V).hom r • formRes i n V β :=
  relativeDifferentialFormsPullback_smul i f (i ≫ f) (𝟙 S) (Category.comp_id _).symm n V r β

/-- **Restriction to a subscheme commutes with the de Rham differential**, on local sections. -/
theorem formRestriction_deRhamD (p : ℕ) (V : X.Opens)
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    (formRestriction i f ((p + 1 : ℕ) : ℤ)).val.app (op V) (deRhamD f p V β) =
      deRhamD (i ≫ f) p (i ⁻¹ᵁ V) ((formRestriction i f (p : ℤ)).val.app (op V) β) :=
  (deRhamComplex_d_relativeDifferentialFormsMap i f (i ≫ f) (𝟙 S) (by simp) p V β).symm

end AlgebraicGeometry.Scheme.Hom

end
