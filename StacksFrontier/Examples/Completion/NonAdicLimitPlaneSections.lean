module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Functions on the punctured coordinate plane extend

Let `R` be a commutative ring, `B = R[x,y]` and `W = D(x) ∪ D(y) ⊆ Spec B` the complement of
`V(x, y)`. Then

`Γ(W, 𝒪) = B`:

every function regular away from `V(x, y)` is a polynomial. The locus removed has codimension
two, and this is the resulting failure of `Spec B ∖ V(x,y)` to acquire any new function — the
reason a punctured plane is not affine, and an input to Stacks 0EH8.

The argument is elementary and needs no hypothesis on `R`; in particular `R` need not be
reduced. It is carried out on an arbitrary affine scheme `X` with
two global sections `r`, `s`, as `bijective_res_sup_basicOpen`: a section on `D(r) ∪ D(s)` is
a pair of sections `a/rᵐ` and `b/sⁿ` agreeing on `D(rs)`; since `rs` is regular the identity
`a·sⁿ = b·rᵐ` already holds in `Γ(X, ⊤)`; and if `rᵐ` divides `a` whenever that identity
holds, the quotient `c = a/rᵐ` is a global section restricting to the given one on both
charts. For `X = Spec R[x,y]` and `r, s` the two coordinates, regularity is
`MvPolynomial.isRegular_X` and the divisibility is `X_pow_dvd_of_mul_eq`, a comparison of
monomials.

## Main definitions

* `Stacks.CoordinatePlane.planeRing` — the ring `B = R[x,y]`, as `MvPolynomial (Fin 2) R`.
* `Stacks.CoordinatePlane.planeCoord` — the two coordinates as global sections of `Spec B`.
* `Stacks.CoordinatePlane.puncturedPlane` — the open `W = D(x) ∪ D(y)` of `Spec B`.
* `Stacks.CoordinatePlane.sectionsPuncturedPlane` — the ring map `B ⟶ Γ(W.toScheme, ⊤)`.

## Main results

* `Stacks.CoordinatePlane.bijective_res_sup_basicOpen` — on an affine scheme, restriction
  `Γ(X, ⊤) ⟶ Γ(X, D(r) ∪ D(s))` is bijective as soon as `r` and `s` are regular and `rᵐ`
  divides `a` whenever `a·sⁿ = b·rᵐ`.
* `Stacks.CoordinatePlane.X_pow_dvd_of_mul_eq` — that divisibility, for `R[x,y]`.
* `Stacks.CoordinatePlane.bijective_sectionsPuncturedPlane`,
  `.sectionsPuncturedPlaneEquiv` — `B ≃ Γ(W.toScheme, ⊤)`, in the form in which a morphism of
  schemes into `W.toScheme` meets the ring.

## Implementation notes

Everything is phrased with `X.basicOpen r` rather than `PrimeSpectrum.basicOpen f`. The two
describe the same open, but only the first has `X.Opens` as its *written* type, and Mathlib's
`Algebra Γ(X, U) Γ(X, X.basicOpen f)` and `IsLocalization.Away r Γ(X, X.basicOpen r)` are
found by instance search only at that spelling. Likewise `D(r) ∩ D(s)` is introduced as
`X.basicOpen (r * s)`, which carries the localization instance, with
`AlgebraicGeometry.Scheme.basicOpen_mul` identifying it with the intersection.
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.CoordinatePlane

/-! ### Sections on a union of two basic opens of an affine scheme -/

section Affine

variable {X : Scheme.{u}}

/-- Restriction twice is restriction once. The third inclusion is taken as an argument so that
the statement can be used at whatever proof of `U ≤ W` the goal happens to carry. -/
private theorem res_res {U V W : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W) (h₃ : U ≤ W)
    (z : Γ(X, W)) :
    X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op z) =
      X.presheaf.map (homOfLE h₃).op z := by
  change (X.presheaf.map _ ≫ X.presheaf.map _) z = _
  simp only [← Functor.map_comp]
  rfl

variable [IsAffine X] (r s : Γ(X, (⊤ : X.Opens)))

omit [IsAffine X] in
/-- `D(rs) ⊆ D(r)`, from `D(rs) = D(r) ∩ D(s)`. -/
private theorem basicOpen_mul_le_left : X.basicOpen (r * s) ≤ X.basicOpen r :=
  (Scheme.basicOpen_mul X r s).le.trans inf_le_left

omit [IsAffine X] in
/-- `D(rs) ⊆ D(s)`. -/
private theorem basicOpen_mul_le_right : X.basicOpen (r * s) ≤ X.basicOpen s :=
  (Scheme.basicOpen_mul X r s).le.trans inf_le_right

/-- **Restriction to `D(r) ∪ D(s)` is bijective.** On an affine scheme a function regular on
`D(r) ∪ D(s)` extends uniquely to a global one, provided `r` and `s` are regular and `rᵐ`
divides `a` whenever `a·sⁿ = b·rᵐ`. For the coordinate plane both hypotheses hold, and this is
the statement that the plane minus `V(x,y)` carries no new function. -/
theorem bijective_res_sup_basicOpen (hr : IsRegular r) (hs : IsRegular s)
    (hdvd : ∀ (a b : Γ(X, (⊤ : X.Opens))) (m n : ℕ),
      a * s ^ n = b * r ^ m → ∃ c, a = r ^ m * c) :
    Function.Bijective
      ((X.presheaf.map (homOfLE (le_top : X.basicOpen r ⊔ X.basicOpen s ≤ ⊤)).op).hom) := by
  classical
  have hle : X.basicOpen r ⊔ X.basicOpen s ≤ ⊤ := le_top
  have hrW : X.basicOpen r ≤ X.basicOpen r ⊔ X.basicOpen s := le_sup_left
  have hsW : X.basicOpen s ≤ X.basicOpen r ⊔ X.basicOpen s := le_sup_right
  have hinjr : Function.Injective (algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen r)) :=
    IsLocalization.injective _ (Submonoid.powers_le.mpr hr.mem_nonZeroDivisors)
  have hinjrs : Function.Injective
      (algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen (r * s))) :=
    IsLocalization.injective _ (Submonoid.powers_le.mpr (hr.mul hs).mem_nonZeroDivisors)
  have halg (f : Γ(X, (⊤ : X.Opens))) (w : Γ(X, (⊤ : X.Opens))) :
      algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen f) w =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op w := rfl
  -- the restrictions from a chart to the overlap
  have hρ (f : Γ(X, (⊤ : X.Opens))) (h : X.basicOpen (r * s) ≤ X.basicOpen f)
      (w : Γ(X, (⊤ : X.Opens))) :
      X.presheaf.map (homOfLE h).op (algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen f) w) =
        algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen (r * s)) w := by
    rw [halg, halg]
    exact res_res _ _ _ w
  -- a lift `c` of a chart section `z'` of `D(f)`, with `f ^ m * c = a`, is `z'`
  have hlift (f : Γ(X, (⊤ : X.Opens))) (z' : Γ(X, X.basicOpen f)) (a c : Γ(X, (⊤ : X.Opens)))
      (m : ℕ) (hc : a = f ^ m * c)
      (ha : z' * algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen f) (f ^ m) =
        algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen f) a) :
      algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen f) c = z' := by
    refine (IsLocalization.Away.algebraMap_pow_isUnit f m).mul_right_cancel ?_
    rw [← map_pow, ← map_mul, mul_comm c, ← hc]
    exact ha.symm
  refine ⟨fun p q hpq => hinjr ?_, fun z => ?_⟩
  · rw [halg, halg, ← res_res hrW hle (X.basicOpen_le r) p,
      ← res_res hrW hle (X.basicOpen_le r) q]
    exact congrArg (X.presheaf.map (homOfLE hrW).op) hpq
  · set zr : Γ(X, X.basicOpen r) := X.presheaf.map (homOfLE hrW).op z with hzrdef
    set zs : Γ(X, X.basicOpen s) := X.presheaf.map (homOfLE hsW).op z with hzsdef
    set a : Γ(X, (⊤ : X.Opens)) := (IsLocalization.Away.sec r zr).1 with hadef
    set m : ℕ := (IsLocalization.Away.sec r zr).2 with hmdef
    set b : Γ(X, (⊤ : X.Opens)) := (IsLocalization.Away.sec s zs).1 with hbdef
    set n : ℕ := (IsLocalization.Away.sec s zs).2 with hndef
    have ha : zr * algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen r) (r ^ m) =
        algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen r) a :=
      IsLocalization.Away.sec_spec r zr
    have hb : zs * algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen s) (s ^ n) =
        algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen s) b :=
      IsLocalization.Away.sec_spec s zs
    -- both charts restrict to the same section of `D(rs)`
    have hoverlap :
        X.presheaf.map (homOfLE (basicOpen_mul_le_left r s)).op zr =
          X.presheaf.map (homOfLE (basicOpen_mul_le_right r s)).op zs := by
      rw [hzrdef, hzsdef,
        res_res (basicOpen_mul_le_left r s) hrW ((basicOpen_mul_le_left r s).trans hrW) z,
        res_res (basicOpen_mul_le_right r s) hsW ((basicOpen_mul_le_right r s).trans hsW) z]
    have har := congrArg (X.presheaf.map (homOfLE (basicOpen_mul_le_left r s)).op) ha
    have hbr := congrArg (X.presheaf.map (homOfLE (basicOpen_mul_le_right r s)).op) hb
    rw [map_mul, hρ, hρ] at har hbr
    have hcross : algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen (r * s)) (a * s ^ n) =
        algebraMap Γ(X, (⊤ : X.Opens)) Γ(X, X.basicOpen (r * s)) (b * r ^ m) := by
      rw [map_mul, map_mul, ← har, ← hbr, hoverlap]
      ring
    obtain ⟨c, hc⟩ := hdvd a b m n (hinjrs hcross)
    have hcb : s ^ n * c = b := by
      refine (hr.pow m).left ?_
      calc r ^ m * (s ^ n * c) = a * s ^ n := by rw [hc]; ring
        _ = b * r ^ m := hinjrs hcross
        _ = r ^ m * b := mul_comm _ _
    have hcr := hlift r zr a c m hc ha
    have hcs := hlift s zs b c n hcb.symm hb
    refine ⟨c, ?_⟩
    let V : Bool → X.Opens := fun i => if i then X.basicOpen r else X.basicOpen s
    have hV (i : Bool) : V i ≤ X.basicOpen r ⊔ X.basicOpen s := by
      cases i
      · exact hsW
      · exact hrW
    have hcover : X.basicOpen r ⊔ X.basicOpen s ≤ iSup V := by simp [V, iSup_bool_eq]
    refine X.sheaf.eq_of_locally_eq' V _ (fun i => homOfLE (hV i)) hcover _ _ (fun i => ?_)
    cases i
    · change X.presheaf.map (homOfLE hsW).op (X.presheaf.map (homOfLE hle).op c) =
        X.presheaf.map (homOfLE hsW).op z
      rw [res_res hsW hle (X.basicOpen_le s) c, ← halg, hcs, hzsdef]
    · change X.presheaf.map (homOfLE hrW).op (X.presheaf.map (homOfLE hle).op c) =
        X.presheaf.map (homOfLE hrW).op z
      rw [res_res hrW hle (X.basicOpen_le r) c, ← halg, hcr, hzrdef]

end Affine

/-! ### The coordinate plane -/

variable (R : Type u) [CommRing R]

/-- `B = R[x,y]`, the coordinate ring of the affine plane over `R`. -/
abbrev planeRing : Type u := MvPolynomial (Fin 2) R

/-- `B ≃+* Γ(Spec B, ⊤)`, the global-sections identification of an affine scheme, as a ring
equivalence. The plane's two coordinates are read as global sections through it. -/
def planeGammaEquiv :
    planeRing R ≃+* Γ(Spec (CommRingCat.of (planeRing R)), (⊤ : (Spec
      (CommRingCat.of (planeRing R))).Opens)) :=
  (Scheme.ΓSpecIso (CommRingCat.of (planeRing R))).symm.commRingCatIsoToRingEquiv

/-- The `i`-th coordinate of the plane, as a global section of `Spec R[x,y]`. -/
def planeCoord (i : Fin 2) :
    Γ(Spec (CommRingCat.of (planeRing R)), (⊤ : (Spec (CommRingCat.of (planeRing R))).Opens)) :=
  planeGammaEquiv R (MvPolynomial.X i)

/-- `W = D(x) ∪ D(y)`, the plane with the codimension-two locus `V(x,y)` removed. -/
def puncturedPlane : (Spec (CommRingCat.of (planeRing R))).Opens :=
  (Spec (CommRingCat.of (planeRing R))).basicOpen (planeCoord R 0) ⊔
    (Spec (CommRingCat.of (planeRing R))).basicOpen (planeCoord R 1)

variable {R}

/-- Regularity transports along a ring equivalence. -/
private theorem isRegular_ringEquiv {A S : Type u} [CommRing A] [CommRing S] (e : A ≃+* S)
    {w : A} (hw : IsRegular w) : IsRegular (e w) := by
  refine ⟨fun p q hpq => e.symm.injective (hw.left ?_),
    fun p q hpq => e.symm.injective (hw.right ?_)⟩ <;>
  simpa only [map_mul, RingEquiv.symm_apply_apply] using congrArg e.symm hpq

/-- **The monomial comparison behind the gluing.** If `a·yⁿ = b·xᵐ` in `R[x,y]` then `xᵐ ∣ a`:
a monomial of `a` of `x`-degree below `m` contributes a monomial of `a·yⁿ` of `x`-degree below
`m`, and `b·xᵐ` has none. -/
theorem X_pow_dvd_of_mul_eq (a b : planeRing R) (m n : ℕ)
    (h : a * MvPolynomial.X 1 ^ n = b * MvPolynomial.X 0 ^ m) :
    (MvPolynomial.X 0 : planeRing R) ^ m ∣ a := by
  classical
  rw [MvPolynomial.X_pow_eq_monomial]
  refine MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero.mpr ?_
  ext d
  by_cases hd : Finsupp.single (0 : Fin 2) m ≤ d
  · exact MvPolynomial.coeff_modMonomial_of_le a hd
  · rw [MvPolynomial.coeff_modMonomial_of_not_le a hd]
    have hd0 : d 0 < m := by simpa only [Finsupp.single_le_iff, not_le] using hd
    have hz := congrArg (MvPolynomial.coeff (d + Finsupp.single 1 n)) h
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.coeff_mul_monomial, mul_one] at hz
    have hnle : ¬ Finsupp.single (0 : Fin 2) m ≤ d + Finsupp.single 1 n := by
      simpa only [Finsupp.single_le_iff, Finsupp.add_apply,
        Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), add_zero, not_le] using hd0
    rw [MvPolynomial.coeff_mul_monomial', ite_eq_right hnle] at hz
    exact hz

variable (R)

/-- The two coordinates are regular global sections. -/
theorem isRegular_planeCoord (i : Fin 2) : IsRegular (planeCoord R i) :=
  isRegular_ringEquiv _ MvPolynomial.isRegular_X

/-- The divisibility hypothesis of `bijective_res_sup_basicOpen`, read on `Γ(Spec B, ⊤)`. -/
theorem exists_eq_planeCoord_pow_mul
    (a b : Γ(Spec (CommRingCat.of (planeRing R)),
      (⊤ : (Spec (CommRingCat.of (planeRing R))).Opens))) (m n : ℕ)
    (h : a * planeCoord R 1 ^ n = b * planeCoord R 0 ^ m) :
    ∃ c, a = planeCoord R 0 ^ m * c := by
  set e := planeGammaEquiv R with hedef
  have h' : e.symm a * MvPolynomial.X 1 ^ n = e.symm b * MvPolynomial.X 0 ^ m := by
    have := congrArg e.symm h
    rwa [map_mul, map_mul, map_pow, map_pow, planeCoord, planeCoord,
      e.symm_apply_apply, e.symm_apply_apply] at this
  obtain ⟨c, hc⟩ := X_pow_dvd_of_mul_eq (e.symm a) (e.symm b) m n h'
  refine ⟨e c, ?_⟩
  have := congrArg e hc
  rwa [e.apply_symm_apply, map_mul, map_pow] at this

/-- **`Γ(W, 𝒪) = R[x,y]`.** Restriction from the whole plane to `W = D(x) ∪ D(y)` is
bijective. -/
theorem bijective_res_puncturedPlane :
    Function.Bijective
      (((Spec (CommRingCat.of (planeRing R))).presheaf.map
        (homOfLE (le_top : puncturedPlane R ≤ ⊤)).op).hom) :=
  bijective_res_sup_basicOpen (planeCoord R 0) (planeCoord R 1)
    (isRegular_planeCoord R 0) (isRegular_planeCoord R 1) (exists_eq_planeCoord_pow_mul R)

/-! ### The same, as a map out of `R[x,y]` into the sections of `W` as a scheme -/

/-- The ring map `R[x,y] ⟶ Γ(W.toScheme, ⊤)` for `W = D(x) ∪ D(y)`: the global-sections
isomorphism of `Spec` followed by restriction along the open immersion `W ⟶ Spec R[x,y]`. This
is the shape in which a morphism of schemes *into* `W.toScheme` meets the ring. -/
def sectionsPuncturedPlane :
    CommRingCat.of (planeRing R) ⟶
      Γ((puncturedPlane R).toScheme, (⊤ : (puncturedPlane R).toScheme.Opens)) :=
  (Scheme.ΓSpecIso (CommRingCat.of (planeRing R))).inv ≫ (puncturedPlane R).ι.appTop

variable {R}

/-- **`U.ι.appTop` is restriction followed by an isomorphism.** Reading a global section of `X`
on the open subscheme `U` is: restrict it to `U`, then transport along the isomorphism
`Γ(X, U) ≅ Γ(U, ⊤)`, which is `AlgebraicGeometry.Scheme.Hom.appLE` of the open immersion and is
an isomorphism by Mathlib's instance. -/
theorem res_comp_ι_appLE {X : Scheme.{u}} (U : X.Opens) :
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
        U.ι.appLE U ⊤ U.ι_preimage_self.ge =
      U.ι.appTop := by
  rw [Scheme.Hom.map_appLE]
  exact Scheme.Hom.appLE_eq_app _

variable (R)

/-- **`R[x,y] ≃ Γ(W.toScheme, ⊤)`, the codimension-two input of Stacks 0EH8.** -/
theorem bijective_sectionsPuncturedPlane :
    Function.Bijective (sectionsPuncturedPlane R).hom := by
  have hiso : Function.Bijective
      (Scheme.ΓSpecIso (CommRingCat.of (planeRing R))).inv.hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have happ : Function.Bijective
      ((puncturedPlane R).ι.appLE (puncturedPlane R) ⊤
        (puncturedPlane R).ι_preimage_self.ge).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have htop : Function.Bijective ((puncturedPlane R).ι.appTop).hom := by
    rw [← res_comp_ι_appLE, CommRingCat.hom_comp, RingHom.coe_comp]
    exact happ.comp (bijective_res_puncturedPlane R)
  rw [sectionsPuncturedPlane, CommRingCat.hom_comp, RingHom.coe_comp]
  exact htop.comp hiso

/-- `R[x,y] ≃+* Γ(W.toScheme, ⊤)`, as a ring equivalence. -/
def sectionsPuncturedPlaneEquiv :
    planeRing R ≃+* Γ((puncturedPlane R).toScheme, (⊤ : (puncturedPlane R).toScheme.Opens)) :=
  RingEquiv.ofBijective (sectionsPuncturedPlane R).hom (bijective_sectionsPuncturedPlane R)

/-- `sectionsPuncturedPlaneEquiv R` acts as the ring map `sectionsPuncturedPlane R`. -/
@[simp]
theorem sectionsPuncturedPlaneEquiv_apply (p : planeRing R) :
    sectionsPuncturedPlaneEquiv R p = (sectionsPuncturedPlane R).hom p := rfl

end Stacks.CoordinatePlane

end
