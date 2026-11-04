module

public import StacksCore.Algebra.Homology.ExactCouple
public import StacksCore.Algebra.Homology.SpectralSequence.OfNat
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
import StacksCore.Tactic.StacksAttribute

/-! # The spectral sequence of an exact couple: Stacks 011S and 011T

Stacks 011S: an exact couple `(A, E, α, f, g)` (011Q) determines a spectral sequence
`(E_r, d_r)_{r ≥ 1}` with `E_1 = E`, `d_1 = d = g ∘ f`, `E_2 = E'`, `d_2 = d'`, `E_3 = E''`, and
so on: `(E_{n+1}, d_{n+1}) = (E^{(n)}, d^{(n)})`, the `E`-object and differential of the `n`-th
iterated derived couple `X^{(n)}` (`X^{(0)} = X`, `X^{(n+1)} = (X^{(n)})'` by 011R); the
identification `E_{n+2} ≅ Ker d_{n+1} / Im d_{n+1}` is the definition `E^{(n+1)} = Ker d^{(n)} /
Im d^{(n)}` of the derived couple. Stacks
011T: the towers `0 = B_1 ⊆ B_2 ⊆ ⋯ ⊆ Z_2 ⊆ Z_1 = E` of this spectral sequence (011N) are
`Z_{r+1} = f⁻¹(Im α^r)` and `B_{r+1} = g(Ker α^r)`, and the differential `d_{r+1}` on
`E_{r+1} = Z_{r+1}/B_{r+1}` is: for `x ∈ Z_{r+1}` choose `y ∈ A` with `f(x) = α^r(y)`; then
`d_{r+1}(x̄) = \overline{g(y)}`.

* The spectral sequence is `ExactCouple.spectralSequence : SpectralSequence.Ungraded C 1`, built
  by `Ungraded.ofNat` from the sequence `(E^{(n)}, d^{(n)})` of iterated derived couples
  `derivedIter n` and the identifications
  `derivedIterSuccIso n : Ker d^{(n)}/Im d^{(n)} ≅ E^{(n+1)}`.
  The iteration is carried by `IterData n`: the `n`-th derived couple `Y` together with
  `ι : Y.A ↪ A`, `π : A ↠ Y.A`, `π ≫ ι = α ^ n` and the naturality of `α`; `IterData.step`
  derives `Y` and composes with `Im α_Y ↪ Y.A ↠ Im α_Y`, and `iterData n` iterates it by
  `Nat.rec`. The equalities `iterData_succ`, `derivedIter_succ` are `rfl`, and the transport
  lemmas `IterData.f_ι_eqToHom`, `IterData.π_g_eqToHom` move `Y.f ≫ ι` and `π ≫ Y.g` along them.
* All statements about the pages go through *explicit isomorphisms*: `spectralSequenceXIso n :
  E_{n+1} ≅ E^{(n)}`, `spectralSequenceXOneIso : E_1 ≅ E`, `spectralSequenceXTwoIso : E_2 ≅ E'`,
  with `d_{n+1}`, `d_1`, `d_2` conjugated accordingly (`spectralSequence_d`,
  `spectralSequence_d_one`, `spectralSequence_d_two`). The raw form
  `X.spectralSequence.Z () 2 = (Subobject.pullback X.f).obj (imageSubobject X.α)` is *not*
  type-correct at implicit transparency: `E_1 = E` only after evaluating `(1 - 1).toNat` and the
  `Nat.rec` defining `iterData`, so the honest statements carry `E_1 ≅ E` as a morphism.
* 011T is proved in the generality of `DerivedPages E`: the data identifying the pages of any
  ungraded spectral sequence `E : Ungraded C 1` with the iterated derived couples of `X`
  (`pageIso : E_r ≅ E^{(n)}` for `(r - 1).toNat = n`, compatible with `d`, cycles, homology and
  with `E_{r+1} ≅ H(E_r)`), in the `(r, hr, n, h)` indexing of
  `StacksCore.Algebra.Homology.SpectralSequence.Tower`. `X.spectralSequence` carries such data
  canonically (`spectralSequenceDerivedPages`, from the `ofNat` API), so the `X.spectralSequence`
  statements are corollaries; the `DerivedPages` API (`pageOneIso`, `pageTwoIso`, `d_one`, `d_two`,
  `pageIso_succ_hom`, `liftCycles_homologyπ_homologyIso_hom`) is what the induction consumes.
* The induction for 011T is `DerivedPages.Invariant s hs n h`, a `Prop`-valued invariant at stage
  `s` (`n = s - 1`): the closed forms of `Z_s`, `B_s` and the compatibilities of the quotient map
  `q_s : Z_s ↠ E_s` with `f^{(n)} ≫ ι` and `π ≫ g^{(n)}` through `E_s ≅ E^{(n)}`. The generic
  step is stated for a `Package` (any exact couple `Y` with `E_s ≅ Y.E`, `ι`, `π`, and the same
  compatibilities) and uses Tower's `Ungraded.Z_add_one`, `Ungraded.B_add_one`, `q_add_one`
  together with 011R (1), (2) for `Y`; `Invariant.step` feeds the iterated data into it, with the
  page isos fixed to `pageIso` and the transports `f_ι_eqToHom`, `π_g_eqToHom` closed by
  `eqToHom_trans_assoc`. Tags: `DerivedPages.Z_succ`, `DerivedPages.B_succ`, `DerivedPages.d_succ`.
* The formula for `d_{r+1}` is spelled with `Subobject.factorThru`: for `x : T ⟶ Z_{r+1}` and
  `y : T ⟶ A` with `x ≫ Z_{r+1}.arrow ≫ e₁.hom ≫ f = y ≫ α ^ r`,
  `x ≫ q_{r+1} ≫ d_{r+1} = y ≫ Z_{r+1}.factorThru (g ≫ e₁.inv) _ ≫ q_{r+1}`, where the lift of
  `g ≫ e₁.inv` to `Z_{r+1}` exists because `g ≫ f = 0` and `Z_{r+1} = f⁻¹(Im α^r)`.
* Not formalised here: the Massey-style model of the spectral sequence as the explicit subquotients
  `f⁻¹(Im α^r)/g(Ker α^r)` (Tower's `pageIsoSubquotient` with `Z_succ`, `B_succ` already give
  `E_{r+1} ≅ Z_{r+1}/B_{r+1}`); the remark following 011T that `E_∞ = Z_∞/B_∞` with
  `Z_∞ = f⁻¹(⋂ Im α^r)`, `B_∞ = g(⋃ Ker α^r)`; and 0AMJ (exact couples with shift functors
  `S`, `T`, i.e. the graded variant with `d_r : E_r → T^{r-1} S E_r`), which is deferred.
-/

@[expose] public section

namespace CategoryTheory.ExactCouple

open Limits Category SpectralSequence

variable {C : Type*} [Category* C] [Abelian C] (X : ExactCouple C)

/-! ### Iterated derived couples -/

/-- The `n`-th iterated derived couple `Y` of `X` together with the inclusion `ι : Y.A ↪ A`
and the projection `π : A ↠ Y.A` (`Y.A = Im α^n`), with `π ≫ ι = α ^ n` and the naturality of
`α`. This is the data carried through the iteration `iterData`. -/
structure IterData (n : ℕ) where
  /-- The `n`-th derived couple. -/
  Y : ExactCouple C
  /-- The inclusion `Y.A ↪ A`. -/
  ι : Y.A ⟶ X.A
  /-- The projection `A ↠ Y.A`. -/
  π : X.A ⟶ Y.A
  /-- `ι` is a monomorphism. -/
  [mono_ι : Mono ι]
  /-- `π` is an epimorphism. -/
  [epi_π : Epi π]
  /-- `π ≫ ι = α ^ n`. -/
  π_ι : π ≫ ι = X.α ^ n
  /-- `ι` intertwines `Y.α` and `α`. -/
  α_ι : Y.α ≫ ι = ι ≫ X.α
  /-- `π` intertwines `α` and `Y.α`. -/
  π_α : π ≫ Y.α = X.α ≫ π

namespace IterData

attribute [instance] mono_ι epi_π

variable {X} {n : ℕ} (D : X.IterData n)

/-- The step of the iteration: derive `Y`, with `Im α_Y ↪ Y.A ↪ A` and `A ↠ Y.A ↠ Im α_Y`.
An `abbrev` on purpose (load-bearing): `D.step.Y`, `D.step.ι`, `D.step.π` must reduce. -/
noncomputable abbrev step : X.IterData (n + 1) where
  Y := D.Y.derived
  ι := Abelian.image.ι D.Y.α ≫ D.ι
  π := D.π ≫ Abelian.factorThruImage D.Y.α
  π_ι := by
    rw [assoc, ← assoc (Abelian.factorThruImage D.Y.α), Abelian.image.fac, D.α_ι, ← assoc,
      D.π_ι, X.pow_succ_eq']
  α_ι := by
    rw [derived_α, ← assoc, α'_ι, assoc, D.α_ι, assoc]
  π_α := by
    rw [derived_α, assoc, factorThruImage_α', ← assoc, D.π_α, assoc]

/-- Transport of `Y.f ≫ ι` along an equality of iterated data. -/
lemma f_ι_eqToHom {D' : X.IterData n} (hD : D = D') :
    D.Y.f ≫ D.ι = eqToHom (congrArg (fun D : X.IterData n ↦ D.Y.E) hD) ≫ D'.Y.f ≫ D'.ι := by
  subst hD
  simp

/-- Transport of `π ≫ Y.g` along an equality of iterated data. -/
lemma π_g_eqToHom {D' : X.IterData n} (hD : D = D') :
    D.π ≫ D.Y.g = D'.π ≫ D'.Y.g ≫ eqToHom (congrArg (fun D : X.IterData n ↦ D.Y.E) hD).symm := by
  subst hD
  simp

end IterData

/-- The zeroth iterated data: `X` itself with `ι = π = 𝟙 A`. An `abbrev` on purpose
(load-bearing): its projections must reduce in `invariant_one`. -/
noncomputable abbrev iterDataZero : X.IterData 0 where
  Y := X
  ι := 𝟙 _
  π := 𝟙 _
  π_ι := by rw [id_comp, pow_zero_eq]
  α_ι := by rw [comp_id, id_comp]
  π_α := by rw [comp_id, id_comp]

/-- The iterated derived couples of `X` with their inclusions and projections, by recursion
on `n`: `iterData 0 = iterDataZero` and `iterData (n + 1) = (iterData n).step`. -/
noncomputable def iterData (X : ExactCouple C) : ∀ n : ℕ, X.IterData n
  | 0 => X.iterDataZero
  | n + 1 => (X.iterData n).step

/-- `iterData 0` is `iterDataZero` (definitional). -/
lemma iterData_zero : X.iterData 0 = X.iterDataZero := rfl

/-- `iterData (n + 1)` is the step of `iterData n` (definitional). -/
lemma iterData_succ (n : ℕ) : X.iterData (n + 1) = (X.iterData n).step := rfl

/-- The `n`-th derived couple `X^{(n)}` of `X`. An `abbrev` on purpose (load-bearing):
`X.derivedIter (n + 1)` must reduce to `(X.derivedIter n).derived`. -/
noncomputable abbrev derivedIter (n : ℕ) : ExactCouple C := (X.iterData n).Y

/-- `X^{(0)} = X` (definitional). -/
lemma derivedIter_zero : X.derivedIter 0 = X := rfl

/-- `X^{(n+1)} = (X^{(n)})'` (definitional). -/
lemma derivedIter_succ (n : ℕ) : X.derivedIter (n + 1) = (X.derivedIter n).derived := rfl

/-- `X^{(1)} = X'` (definitional). -/
lemma derivedIter_one : X.derivedIter 1 = X.derived := rfl

/-- `Ker d^{(n)}/Im d^{(n)} ≅ E^{(n+1)}`, the identification of the homology of the `n`-th
derived couple's `E` with the `(n + 1)`-st derived couple's `E`, an `eqToIso` along
`iterData_succ`. -/
noncomputable def derivedIterSuccIso (n : ℕ) :
    (ShortComplex.mk (X.derivedIter n).d (X.derivedIter n).d
      (X.derivedIter n).d_comp_d).homology ≅ (X.derivedIter (n + 1)).E :=
  (eqToIso (congrArg (fun D : X.IterData (n + 1) ↦ D.Y.E) (X.iterData_succ n))).symm

/-- `derivedIterSuccIso` is an `eqToHom` (in the `hom` direction). -/
lemma derivedIterSuccIso_hom (n : ℕ) :
    (X.derivedIterSuccIso n).hom =
      eqToHom (congrArg (fun D : X.IterData (n + 1) ↦ D.Y.E) (X.iterData_succ n)).symm := by
  unfold derivedIterSuccIso
  rw [Iso.symm_hom, eqToIso.inv]

/-- `derivedIterSuccIso` is an `eqToHom` (in the `inv` direction). -/
lemma derivedIterSuccIso_inv (n : ℕ) :
    (X.derivedIterSuccIso n).inv =
      eqToHom (congrArg (fun D : X.IterData (n + 1) ↦ D.Y.E) (X.iterData_succ n)) := by
  unfold derivedIterSuccIso
  rw [Iso.symm_inv, eqToIso.hom]

/-! ### The spectral sequence (011S) -/

/-- The spectral sequence `(E_r, d_r)_{r ≥ 1}` of the exact couple `X`: `(E_{n+1}, d_{n+1})` is
`(E^{(n)}, d^{(n)})`, the `E`-object and differential of the `n`-th derived couple, and
`E_{n+2} ≅ Ker d^{(n)}/Im d^{(n)}` is `derivedIterSuccIso n`. An `abbrev` of `Ungraded.ofNat`
on purpose (load-bearing): `X.spectralSequence.X r hr` must reduce to `(X.derivedIter _).E`. -/
@[stacks 011S "`(E_r, d_r)_{r ≥ 1}`: `E_1 = E`, `d_1 = d`, `E_{r+1} = E_r'`, `d_{r+1} = d_r'`"]
noncomputable abbrev spectralSequence : Ungraded C 1 :=
  Ungraded.ofNat 1 (fun n ↦ (X.derivedIter n).E) (fun n ↦ (X.derivedIter n).d)
    (fun n ↦ (X.derivedIter n).d_comp_d) X.derivedIterSuccIso

/-! ### Spectral sequences whose pages are the derived couples -/

/-- The data identifying the pages of an ungraded spectral sequence `E` (starting at `1`) with
the iterated derived couples of `X`, in Tower's `(r, hr, n, h : (r - 1).toNat = n)` indexing:
`E_r ≅ E^{(n)}` compatible with `d`, with cycles, with homology and with `E_{r+1} ≅ H(E_r)`.
`X.spectralSequence` carries it canonically (`spectralSequenceDerivedPages`); 011T is proved
for any `E` with such data. Write `E.X r hr`, `E.d r hr` with the explicit `hr` (the `by lia`
autoParam fails inside a structure). -/
structure DerivedPages (E : Ungraded C 1) where
  /-- `E_r ≅ E^{(n)}` for `n = r - 1`. -/
  pageIso (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n) : E.X r hr ≅ (X.derivedIter n).E
  /-- `d_r = d^{(n)}` under `pageIso`. -/
  d_pageIso_hom (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n) :
    E.d r hr ≫ (pageIso r hr n h).hom = (pageIso r hr n h).hom ≫ (X.derivedIter n).d
  /-- `Ker d_r ≅ Ker d^{(n)}`. -/
  cyclesIso (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n) :
    (E.page r hr).cycles () ≅ (X.derivedIter n).dComplex.cycles
  /-- `cyclesIso` is compatible with the inclusions of cycles and `pageIso`. -/
  cyclesIso_hom_iCycles (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n) :
    (cyclesIso r hr n h).hom ≫ (X.derivedIter n).dComplex.iCycles =
      (E.page r hr).iCycles () ≫ (pageIso r hr n h).hom
  /-- `H(E_r) ≅ Ker d^{(n)}/Im d^{(n)}`. -/
  homologyIso (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n) :
    (E.page r hr).homology () ≅ (X.derivedIter n).dComplex.homology
  /-- `homologyIso` is compatible with the projections from cycles and `cyclesIso`. -/
  homologyπ_homologyIso_hom (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n) :
    (E.page r hr).homologyπ () ≫ (homologyIso r hr n h).hom =
      (cyclesIso r hr n h).hom ≫ (X.derivedIter n).dComplex.homologyπ
  /-- The identification `E_{r+1} ≅ H(E_r)` of the spectral sequence is `derivedIterSuccIso n`
  under `pageIso` and `homologyIso`. -/
  homologyIso_pageIso (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n) :
    (E.homologyIso r hr).hom ≫ (pageIso (r + 1) (by omega) (n + 1) (by omega)).hom =
      (homologyIso r hr n h).hom ≫ (X.derivedIterSuccIso n).hom

/-- `X.spectralSequence` realises the derived couples on its pages (the `ofNat` API). -/
noncomputable def spectralSequenceDerivedPages : X.DerivedPages X.spectralSequence where
  pageIso r hr n h := Ungraded.ofNatPageXIso _ _ _ _ _ r hr n h
  d_pageIso_hom r hr n h := Ungraded.ofNat_d_ofNatPageXIso_hom _ _ _ _ _ r hr n h
  cyclesIso r hr n h := Ungraded.ofNatPageCyclesIso _ _ _ _ _ r hr n h
  cyclesIso_hom_iCycles r hr n h := Ungraded.ofNatPageCyclesIso_hom_iCycles _ _ _ _ _ r hr n h
  homologyIso r hr n h := Ungraded.ofNatPageHomologyIso _ _ _ _ _ r hr n h
  homologyπ_homologyIso_hom r hr n h :=
    Ungraded.homologyπ_ofNatPageHomologyIso_hom _ _ _ _ _ r hr n h
  homologyIso_pageIso r hr n h := Ungraded.ofNat_homologyIso_hom _ _ _ _ _ r hr n h

namespace DerivedPages

variable {X} {E : Ungraded C 1} (D : X.DerivedPages E)

/-- Classes of cycles correspond under `homologyIso`: the class of a cycle `z : T ⟶ E_r` is the
class of `z ≫ pageIso.hom` in `Ker d^{(n)}/Im d^{(n)}` (the `hψ` hypothesis of the 011T
induction). -/
lemma liftCycles_homologyπ_homologyIso_hom (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n)
    {T : C} (z : T ⟶ E.X r hr) (hz : z ≫ E.d r hr = 0)
    (hz' : (z ≫ (D.pageIso r hr n h).hom) ≫ (X.derivedIter n).d = 0) :
    (E.page r hr).liftCycles z () rfl hz ≫ (E.page r hr).homologyπ () ≫
        (D.homologyIso r hr n h).hom =
      (X.derivedIter n).dComplex.liftCycles (z ≫ (D.pageIso r hr n h).hom) hz' ≫
        (X.derivedIter n).dComplex.homologyπ := by
  rw [D.homologyπ_homologyIso_hom, ← assoc]
  congr 1
  rw [← cancel_mono (X.derivedIter n).dComplex.iCycles, assoc, D.cyclesIso_hom_iCycles,
    HomologicalComplex.liftCycles_i_assoc, ShortComplex.liftCycles_i]

/-- `d_r` as a conjugate of `d^{(n)}` by `pageIso`. -/
lemma d_eq (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n) :
    E.d r hr = (D.pageIso r hr n h).hom ≫ (X.derivedIter n).d ≫ (D.pageIso r hr n h).inv := by
  rw [← assoc, Iso.eq_comp_inv]
  exact D.d_pageIso_hom r hr n h

/-- `pageIso` at `r + 1` is `E_{r+1} ≅ H(E_r) ≅ Ker d^{(n)}/Im d^{(n)} ≅ E^{(n+1)}`. -/
lemma pageIso_succ_hom (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n) :
    (D.pageIso (r + 1) (by omega) (n + 1) (by omega)).hom =
      (E.homologyIso r hr).inv ≫ (D.homologyIso r hr n h).hom ≫ (X.derivedIterSuccIso n).hom := by
  rw [Iso.eq_inv_comp]
  exact D.homologyIso_pageIso r hr n h

/-- The inverse of `pageIso` at `r + 1`, see `pageIso_succ_hom`. -/
lemma pageIso_succ_inv (r : ℤ) (hr : 1 ≤ r) (n : ℕ) (h : (r - 1).toNat = n) :
    (D.pageIso (r + 1) (by omega) (n + 1) (by omega)).inv =
      (X.derivedIterSuccIso n).inv ≫ (D.homologyIso r hr n h).inv ≫ (E.homologyIso r hr).hom := by
  rw [← cancel_epi (D.pageIso (r + 1) (by omega) (n + 1) (by omega)).hom, Iso.hom_inv_id,
    D.pageIso_succ_hom r hr n h]
  simp [assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]

/-- `E_1 ≅ E`: `pageIso` at `r = 1` followed by `E^{(0)} = E`. -/
noncomputable def pageOneIso : E.X 1 ≅ X.E :=
  D.pageIso 1 le_rfl 0 rfl ≪≫ eqToIso (congrArg (fun D : X.IterData 0 ↦ D.Y.E) X.iterData_zero)

/-- `pageOneIso.hom` is `pageIso.hom` followed by an `eqToHom`. -/
lemma pageOneIso_hom :
    D.pageOneIso.hom = (D.pageIso 1 le_rfl 0 rfl).hom ≫
      eqToHom (congrArg (fun D : X.IterData 0 ↦ D.Y.E) X.iterData_zero) := by
  unfold pageOneIso
  rw [Iso.trans_hom, eqToIso.hom]

/-- `pageOneIso.inv` is an `eqToHom` followed by `pageIso.inv`. -/
lemma pageOneIso_inv :
    D.pageOneIso.inv = eqToHom (congrArg (fun D : X.IterData 0 ↦ D.Y.E) X.iterData_zero).symm ≫
      (D.pageIso 1 le_rfl 0 rfl).inv := by
  unfold pageOneIso
  rw [Iso.trans_inv, eqToIso.inv]

/-- `d_1 = d` under `E_1 ≅ E`. -/
lemma d_one : E.d 1 ≫ D.pageOneIso.hom = D.pageOneIso.hom ≫ X.d := by
  rw [D.pageOneIso_hom, ← assoc, D.d_pageIso_hom 1 le_rfl 0 rfl, assoc, assoc,
    eqToHom_naturality (fun D : X.IterData 0 ↦ D.Y.d) X.iterData_zero]

/-- `d_1` as a conjugate of `d` by `E_1 ≅ E`. -/
lemma d_one_eq : E.d 1 = D.pageOneIso.hom ≫ X.d ≫ D.pageOneIso.inv := by
  rw [← assoc, Iso.eq_comp_inv]
  exact D.d_one

/-- `E_2 ≅ E'`: `pageIso` at `r = 2` followed by `E^{(1)} = E'`. -/
noncomputable def pageTwoIso : E.X 2 ≅ X.derived.E :=
  D.pageIso 2 (by omega) 1 rfl ≪≫ eqToIso (congrArg ExactCouple.E X.derivedIter_one)

/-- `pageTwoIso.hom` is `pageIso.hom` followed by an `eqToHom`. -/
lemma pageTwoIso_hom :
    D.pageTwoIso.hom = (D.pageIso 2 (by omega) 1 rfl).hom ≫
      eqToHom (congrArg ExactCouple.E X.derivedIter_one) := by
  unfold pageTwoIso
  rw [Iso.trans_hom, eqToIso.hom]

/-- `d_2 = g' ∘ f'` under `E_2 ≅ E'`. -/
lemma d_two : E.d 2 ≫ D.pageTwoIso.hom = D.pageTwoIso.hom ≫ (X.f' ≫ X.g') := by
  rw [D.pageTwoIso_hom, ← assoc, D.d_pageIso_hom 2 (by omega) 1 rfl, assoc, assoc,
    eqToHom_naturality (fun Y : ExactCouple C ↦ Y.d) X.derivedIter_one, d_def]

end DerivedPages

/-! ### The pages of `X.spectralSequence` (011S) -/

/-- `E_{n+1} ≅ E^{(n)}`: the `(n + 1)`-st page of the spectral sequence of `X` is the `E` of
the `n`-th derived couple. An `abbrev` on purpose (load-bearing): the 011T statements for
`X.spectralSequence` must see through it. -/
@[stacks 011S "`E_{n+1} ≅ E^{(n)}`, the `n`-th derived couple's `E`"]
noncomputable abbrev spectralSequenceXIso (n : ℕ) :
    X.spectralSequence.X (n + 1) ≅ (X.derivedIter n).E :=
  X.spectralSequenceDerivedPages.pageIso (n + 1) (by omega) n (by omega)

/-- `d_{n+1} = d^{(n)}` under `E_{n+1} ≅ E^{(n)}`. -/
@[stacks 011S "`d_{n+1} = d^{(n)}` under `E_{n+1} ≅ E^{(n)}`"]
lemma spectralSequence_d (n : ℕ) :
    X.spectralSequence.d (n + 1) ≫ (X.spectralSequenceXIso n).hom =
      (X.spectralSequenceXIso n).hom ≫ (X.derivedIter n).d :=
  X.spectralSequenceDerivedPages.d_pageIso_hom (n + 1) (by omega) n (by omega)

/-- `E_1 ≅ E`. An `abbrev` on purpose (load-bearing): the 011T statements for
`X.spectralSequence` must see through it. -/
@[stacks 011S "`E_1 = E`"]
noncomputable abbrev spectralSequenceXOneIso : X.spectralSequence.X 1 ≅ X.E :=
  X.spectralSequenceDerivedPages.pageOneIso

/-- `d_1 = d` under `E_1 ≅ E`. -/
@[stacks 011S "`d_1 = d` under `E_1 ≅ E`"]
lemma spectralSequence_d_one :
    X.spectralSequence.d 1 ≫ X.spectralSequenceXOneIso.hom = X.spectralSequenceXOneIso.hom ≫ X.d :=
  X.spectralSequenceDerivedPages.d_one

/-- `E_2 ≅ E'`. An `abbrev` on purpose (load-bearing), as `spectralSequenceXOneIso`. -/
@[stacks 011S "`E_2 = E'`"]
noncomputable abbrev spectralSequenceXTwoIso : X.spectralSequence.X 2 ≅ X.derived.E :=
  X.spectralSequenceDerivedPages.pageTwoIso

/-- `d_2 = g' ∘ f'` under `E_2 ≅ E'`. -/
@[stacks 011S "`d_2 = g' ∘ f'` under `E_2 ≅ E'`"]
lemma spectralSequence_d_two :
    X.spectralSequence.d 2 ≫ X.spectralSequenceXTwoIso.hom =
      X.spectralSequenceXTwoIso.hom ≫ (X.f' ≫ X.g') :=
  X.spectralSequenceDerivedPages.d_two

/-! ### The generic step of the 011T induction -/

section Generic

variable (E : Ungraded C 1) (e₁ : E.X 1 le_rfl ≅ X.E)

/-- `g ≫ e₁⁻¹ : A ⟶ E_1` factors through `f⁻¹(Im α^n)`, since `g ≫ f = 0`. -/
lemma pullback_factors_g (n : ℕ) :
    ((Subobject.pullback (e₁.hom ≫ X.f)).obj (imageSubobject (X.α ^ n))).Factors
      (X.g ≫ e₁.inv) :=
  pullback_factors _ _ _
    (by rw [assoc, Iso.inv_hom_id_assoc, X.g_f]; exact Subobject.factors_zero)

/-- `g ≫ e₁⁻¹` factors through `Z_s` as soon as `Z_s = f⁻¹(Im α^n)`. -/
lemma factors_of_eq {s : ℤ} {n : ℕ}
    (hZ : E.Z () s = (Subobject.pullback (e₁.hom ≫ X.f)).obj (imageSubobject (X.α ^ n))) :
    (E.Z () s).Factors (X.g ≫ e₁.inv) := by
  rw [hZ]
  exact X.pullback_factors_g E e₁ n

/-- `Z_1 = E_1 = f⁻¹(Im α^0)` under `E_1 ≅ E`. -/
theorem Z_one :
    E.Z () 1 = (Subobject.pullback (e₁.hom ≫ X.f)).obj (imageSubobject (X.α ^ 0)) := by
  rw [Z_self]
  simp only [pow_zero, End.one_def]
  rw [Subobject.imageSubobject_eq_top_of_epi, Subobject.pullback_top]

/-- `B_1 = 0 = g(Ker α^0)` under `E_1 ≅ E`. -/
theorem B_one :
    E.B () 1 = (Subobject.exists (X.g ≫ e₁.inv)).obj (kernelSubobject (X.α ^ 0)) := by
  rw [B_self]
  simp only [pow_zero, End.one_def]
  rw [Subobject.kernelSubobject_eq_bot_of_mono, (Subobject.existsPullbackAdj _).gc.l_bot]

/-- The data carried through the 011T induction at stage `s` (with `n = s - 1`), for an
ungraded spectral sequence `E` with `e₁ : E_1 ≅ E`: an exact couple `Y` with `E_s ≅ Y.E`
conjugating `d_s` to `Y.d`, the inclusion `ι : Y.A ↪ A` and projection `π : A ↠ Y.A` with
`π ≫ ι = α ^ n`, the closed forms of `Z_s` and `B_s`, and the compatibilities of the quotient
map `q_s : Z_s ↠ E_s` with `Y.f ≫ ι` and `π ≫ Y.g`. The generic step (`Package.Z_step`,
`Package.B_step`, `Package.q_f_step`, `Package.π_g_step`) produces the same data at stage
`s + 1` from the derived couple of `Y`. -/
structure Package (s : ℤ) (hs : 1 ≤ s) (n : ℕ) where
  /-- The exact couple at stage `s` (the `n`-th derived couple in the application). -/
  Y : ExactCouple C
  /-- `E_s ≅ Y.E`. -/
  φ : E.X s hs ≅ Y.E
  /-- `d_s` is `Y.d` conjugated by `φ`. -/
  hd : E.d s hs = φ.hom ≫ Y.d ≫ φ.inv
  /-- The inclusion `Y.A ↪ A`. -/
  ι : Y.A ⟶ X.A
  /-- `ι` is a monomorphism. -/
  [mono_ι : Mono ι]
  /-- The projection `A ↠ Y.A`. -/
  π : X.A ⟶ Y.A
  /-- `π` is an epimorphism. -/
  [epi_π : Epi π]
  /-- `π ≫ ι = α ^ n`. -/
  π_ι : π ≫ ι = X.α ^ n
  /-- `ι` intertwines `Y.α` and `α`. -/
  α_ι : Y.α ≫ ι = ι ≫ X.α
  /-- `π` intertwines `α` and `Y.α`. -/
  π_α : π ≫ Y.α = X.α ≫ π
  /-- `Z_s = f⁻¹(Im α^n)` under `E_1 ≅ E`. -/
  hZ : E.Z () s = (Subobject.pullback (e₁.hom ≫ X.f)).obj (imageSubobject (X.α ^ n))
  /-- `B_s = g(Ker α^n)` under `E_1 ≅ E`. -/
  hB : E.B () s = (Subobject.exists (X.g ≫ e₁.inv)).obj (kernelSubobject (X.α ^ n))
  /-- `q_s ≫ φ ≫ Y.f ≫ ι` is the restriction of `f` to `Z_s ⊆ E_1 ≅ E`. -/
  q_f : E.q () s hs ≫ φ.hom ≫ Y.f ≫ ι = (E.Z () s).arrow ≫ e₁.hom ≫ X.f
  /-- The lift of `g ≫ e₁⁻¹` to `Z_s`. -/
  ℓ : X.A ⟶ (E.Z () s : C)
  /-- `ℓ` lifts `g ≫ e₁⁻¹`. -/
  ℓ_arrow : ℓ ≫ (E.Z () s).arrow = X.g ≫ e₁.inv
  /-- `π ≫ Y.g ≫ φ⁻¹` is the class of the lift `ℓ` of `g` in `E_s = Z_s/B_s`. -/
  π_g : π ≫ Y.g ≫ φ.inv = ℓ ≫ E.q () s hs

namespace Package

variable {X E e₁} {s : ℤ} {hs : 1 ≤ s} {n : ℕ}

attribute [instance] mono_ι epi_π

variable (P : Package X E e₁ s hs n)

/-- `ι(Im Y.α) = Im α^{n+1}`. -/
lemma map_ι_imageSubobject_α :
    (Subobject.map P.ι).obj (imageSubobject P.Y.α) = imageSubobject (X.α ^ (n + 1)) := by
  rw [← Subobject.exists_iso_map, ← Subobject.imageSubobject_comp_eq_exists, P.α_ι,
    Subobject.imageSubobject_comp_eq_exists, ← Subobject.exists_obj_top P.ι,
    ← Subobject.imageSubobject_eq_top_of_epi P.π, ← Subobject.imageSubobject_comp_eq_exists,
    P.π_ι, ← Subobject.imageSubobject_comp_eq_exists, pow_succ_eq']

/-- `Ker Y.α = π(Ker α^{n+1})`. -/
lemma kernelSubobject_α_eq_exists_π :
    kernelSubobject P.Y.α = (Subobject.exists P.π).obj (kernelSubobject (X.α ^ (n + 1))) := by
  rw [← Abelian.Subobject.exists_pullback_eq_self_of_epi P.π (kernelSubobject P.Y.α),
    Subobject.pullback_kernelSubobject, P.π_α, ← kernelSubobject_comp_mono (X.α ≫ P.π) P.ι,
    pow_succ_eq, ← P.π_ι, ← assoc]

/-- `Ker d_s = (φ ≫ Y.f ≫ ι)⁻¹(Im α^{n+1})`, by 011R (1) for `Y`. -/
lemma kernelSubobject_d_eq :
    kernelSubobject (E.d s hs) = (Subobject.pullback (P.φ.hom ≫ P.Y.f ≫ P.ι)).obj
      (imageSubobject (X.α ^ (n + 1))) := by
  rw [P.hd, ← assoc, kernelSubobject_comp_mono, ← Subobject.pullback_kernelSubobject,
    P.Y.kernelSubobject_d_eq_pullback_imageSubobject,
    ← Subobject.pullback_map_self P.ι (imageSubobject P.Y.α),
    P.map_ι_imageSubobject_α, Subobject.pullback_comp, Subobject.pullback_comp]

/-- `Im d_s = (ℓ ≫ q_s)(Ker α^{n+1})`, by 011R (2) for `Y`. -/
lemma imageSubobject_d_eq :
    imageSubobject (E.d s hs) =
      (Subobject.exists (P.ℓ ≫ E.q () s hs)).obj (kernelSubobject (X.α ^ (n + 1))) := by
  rw [P.hd, ← assoc, Subobject.imageSubobject_comp_eq_exists, Subobject.imageSubobject_iso_comp',
    P.Y.imageSubobject_d_eq_exists_kernelSubobject, P.kernelSubobject_α_eq_exists_π,
    ← Subobject.exists_comp, ← Subobject.exists_comp, P.π_g]

include P in
/-- `Z_{s+1} = f⁻¹(Im α^{n+1})`, from `Z_{s+1} = q_s⁻¹(Ker d_s)` pushed into `E_1`. -/
theorem Z_step :
    E.Z () (s + 1) =
      (Subobject.pullback (e₁.hom ≫ X.f)).obj (imageSubobject (X.α ^ (n + 1))) := by
  have hle : (Subobject.pullback (e₁.hom ≫ X.f)).obj (imageSubobject (X.α ^ (n + 1))) ≤
      E.Z () s := by
    rw [P.hZ]
    exact (Subobject.pullback _).monotone.imp (X.imageSubobject_pow_succ_le n)
  rw [Ungraded.Z_add_one E s hs, P.kernelSubobject_d_eq,
    ← Subobject.pullback_comp, P.q_f, Subobject.pullback_comp, ← Subobject.inf_eq_map_pullback,
    inf_eq_right.2 hle]

include P in
/-- `B_{s+1} = g(Ker α^{n+1})`, from `B_{s+1} = q_s⁻¹(Im d_s)` pushed into `E_1`. -/
theorem B_step :
    E.B () (s + 1) =
      (Subobject.exists (X.g ≫ e₁.inv)).obj (kernelSubobject (X.α ^ (n + 1))) := by
  rw [Ungraded.B_add_one E s hs, P.imageSubobject_d_eq,
    Subobject.exists_comp, Abelian.Subobject.pullback_exists_eq_sup, E.kernelSubobject_q () s hs,
    (Subobject.mapPullbackAdj (E.Z () s).arrow).gc.l_sup, ← Subobject.inf_eq_map_pullback,
    inf_eq_right.2 (E.B_le_Z () s), ← Subobject.exists_iso_map, ← Subobject.exists_comp,
    P.ℓ_arrow, P.hB,
    sup_eq_left.2 ((Subobject.exists _).monotone.imp (X.kernelSubobject_pow_le_succ n))]

/-- `z ≫ d_s = 0` iff `z ≫ φ ≫ Y.d = 0`, as `d_s` is `Y.d` conjugated by `φ`. -/
private theorem comp_d_eq_zero_iff {T : C} (z : T ⟶ E.X s hs) :
    z ≫ E.d s hs = 0 ↔ (z ≫ P.φ.hom) ≫ P.Y.d = 0 := by
  rw [P.hd, ← assoc, ← assoc, Preadditive.IsIso.comp_right_eq_zero]

/-- The `q_f` compatibility at stage `s + 1`: for any factorisation `f' ≫ ι'` of the derived
`f` of `Y` through `A'` (`hf'`) and any identification `ψ` of `H(E_s)` with `Ker Y.d/Im Y.d`
compatible with classes of cycles (`hψ`), `q_{s+1} ≫ ψ ≫ f' ≫ ι' ≫ ι` is the restriction of
`f` to `Z_{s+1}`. The conclusion is right-associated; `DerivedPages.Invariant.step` depends on
this shape. -/
theorem q_f_step {A' : C} (ι' : A' ⟶ P.Y.A) (f' : P.Y.dComplex.homology ⟶ A')
    (hf' : P.Y.dComplex.homologyπ ≫ f' ≫ ι' = P.Y.dComplex.iCycles ≫ P.Y.f)
    (ψ : (E.page s hs).homology () ≅ P.Y.dComplex.homology)
    (hψ : ∀ {T : C} (z : T ⟶ E.X s hs) (hz : z ≫ E.d s hs = 0)
      (hz' : (z ≫ P.φ.hom) ≫ P.Y.d = 0),
      (E.page s hs).liftCycles z () rfl hz ≫ (E.page s hs).homologyπ () ≫ ψ.hom =
        P.Y.dComplex.liftCycles (z ≫ P.φ.hom) hz' ≫ P.Y.dComplex.homologyπ) :
    E.q () (s + 1) (by omega) ≫ (E.homologyIso s hs).inv ≫ ψ.hom ≫ f' ≫ ι' ≫ P.ι =
      (E.Z () (s + 1)).arrow ≫ e₁.hom ≫ X.f := by
  have hz := E.ofLE_q_d () s hs
  rw [E.q_add_one () s hs]
  simp only [assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% (hψ _ hz ((P.comp_d_eq_zero_iff _).1 hz)), reassoc_of% hf',
    ShortComplex.liftCycles_i_assoc, assoc, assoc, P.q_f, Subobject.ofLE_arrow_assoc]

/-- The `π_g` compatibility at stage `s + 1`: for any factorisation `π' ≫ g'` of the derived
`g` of `Y` through `A'` (`hg'`), any identification `ψ` of `H(E_s)` with `Ker Y.d/Im Y.d`
compatible with classes of cycles (`hψ`) and any lift `ℓ'` of `g ≫ e₁⁻¹` to `Z_{s+1}`,
`π ≫ π' ≫ g' ≫ ψ⁻¹ ≫ (E_{s+1} ≅ H(E_s))⁻¹` is the class of `ℓ'` in `E_{s+1}`. The conclusion
is right-associated; `DerivedPages.Invariant.step` depends on this shape. -/
theorem π_g_step {A' : C} (π' : P.Y.A ⟶ A') (g' : A' ⟶ P.Y.dComplex.homology)
    (hg' : π' ≫ g' = P.Y.dComplex.liftCycles P.Y.g P.Y.g_dComplex_g ≫ P.Y.dComplex.homologyπ)
    (ψ : (E.page s hs).homology () ≅ P.Y.dComplex.homology)
    (hψ : ∀ {T : C} (z : T ⟶ E.X s hs) (hz : z ≫ E.d s hs = 0)
      (hz' : (z ≫ P.φ.hom) ≫ P.Y.d = 0),
      (E.page s hs).liftCycles z () rfl hz ≫ (E.page s hs).homologyπ () ≫ ψ.hom =
        P.Y.dComplex.liftCycles (z ≫ P.φ.hom) hz' ≫ P.Y.dComplex.homologyπ)
    (ℓ' : X.A ⟶ (E.Z () (s + 1) : C)) (hℓ' : ℓ' ≫ (E.Z () (s + 1)).arrow = X.g ≫ e₁.inv) :
    P.π ≫ π' ≫ g' ≫ ψ.inv ≫ (E.homologyIso s hs).hom = ℓ' ≫ E.q () (s + 1) (by omega) := by
  have hℓℓ : ℓ' ≫ Subobject.ofLE (E.Z () (s + 1)) (E.Z () s)
      ((E.Z_antitone ()).imp (by lia)) = P.ℓ := by
    rw [← cancel_mono (E.Z () s).arrow, assoc, Subobject.ofLE_arrow, hℓ', P.ℓ_arrow]
  have hπg : (P.ℓ ≫ E.q () s hs) ≫ P.φ.hom = P.π ≫ P.Y.g := by
    rw [← P.π_g, assoc, assoc, Iso.inv_hom_id, comp_id]
  have hz' : ((P.ℓ ≫ E.q () s hs) ≫ P.φ.hom) ≫ P.Y.d = 0 := by
    rw [hπg, assoc, P.Y.g_d, comp_zero]
  have hz := (P.comp_d_eq_zero_iff _).2 hz'
  have hlift : (E.page s hs).liftCycles (ℓ' ≫ Subobject.ofLE (E.Z () (s + 1)) (E.Z () s)
      ((E.Z_antitone ()).imp (by lia)) ≫ E.q () s hs) () rfl
        (by rw [← assoc, hℓℓ]; exact hz) =
      (E.page s hs).liftCycles (P.ℓ ≫ E.q () s hs) () rfl hz := by
    rw [← cancel_mono ((E.page s hs).iCycles ()), HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i, ← assoc, hℓℓ]
  have hlift' : P.Y.dComplex.liftCycles ((P.ℓ ≫ E.q () s hs) ≫ P.φ.hom) hz' =
      P.π ≫ P.Y.dComplex.liftCycles P.Y.g P.Y.g_dComplex_g := by
    rw [← cancel_mono P.Y.dComplex.iCycles, ShortComplex.liftCycles_i, hπg, assoc,
      ShortComplex.liftCycles_i]
  rw [E.q_add_one () s hs, HomologicalComplex.comp_liftCycles_assoc, hlift,
    ← cancel_mono (E.homologyIso s hs).inv, ← cancel_mono ψ.hom]
  simp only [assoc, Iso.hom_inv_id, Iso.inv_hom_id, comp_id]
  rw [hψ _ hz hz', hlift', assoc, hg']

/-- The formula for `d_s` from the package: for `x : T ⟶ Z_s` and `y : T ⟶ A` with
`f x = α^n y` (under `E_1 ≅ E`), `d_s(x̄) = \overline{ℓ y}`, the class of the lift `y ≫ ℓ` of
`g ∘ y` (Lean's `y ≫ g`) to `Z_s`. -/
theorem q_d {T : C} (x : T ⟶ (E.Z () s : C)) (y : T ⟶ X.A)
    (h : x ≫ (E.Z () s).arrow ≫ e₁.hom ≫ X.f = y ≫ X.α ^ n) :
    x ≫ E.q () s hs ≫ E.d s hs = (y ≫ P.ℓ) ≫ E.q () s hs := by
  have h1 : x ≫ E.q () s hs ≫ P.φ.hom ≫ P.Y.f = y ≫ P.π := by
    rw [← cancel_mono P.ι, assoc, assoc, assoc, P.q_f, assoc, P.π_ι, h]
  rw [P.hd, P.Y.d_def, assoc P.Y.f, reassoc_of% h1, P.π_g, assoc]

include P in
/-- The formula for `d_s` spelled with `Subobject.factorThru`: `d_s(x̄) = \overline{g y}`, with
the lift of `g ≫ e₁⁻¹` to `Z_s` given by any factorisation witness `hfac`. -/
theorem q_d_factorThru (hfac : (E.Z () s).Factors (X.g ≫ e₁.inv)) {T : C}
    (x : T ⟶ (E.Z () s : C)) (y : T ⟶ X.A)
    (h : x ≫ (E.Z () s).arrow ≫ e₁.hom ≫ X.f = y ≫ X.α ^ n) :
    x ≫ E.q () s hs ≫ E.d s hs =
      y ≫ (E.Z () s).factorThru (X.g ≫ e₁.inv) hfac ≫ E.q () s hs := by
  have hℓ : (E.Z () s).factorThru (X.g ≫ e₁.inv) hfac = P.ℓ := by
    rw [← cancel_mono (E.Z () s).arrow, Subobject.factorThru_arrow, P.ℓ_arrow]
  rw [P.q_d x y h, hℓ, assoc]

end Package

end Generic

/-! ### The induction and the towers `Z_r`, `B_r` (011T) -/

namespace DerivedPages

variable {X} {E : Ungraded C 1} (D : X.DerivedPages E)

/-- The invariant of the 011T induction at stage `s` (with `n = s - 1`): the closed forms of
`Z_s` and `B_s` under `E_1 ≅ E`, and the compatibilities of the quotient map `q_s : Z_s ↠ E_s`
with `f^{(n)} ≫ ι` and `π ≫ g^{(n)}` through `E_s ≅ E^{(n)}`, where `ι : A^{(n)} ↪ A` and
`π : A ↠ A^{(n)}` are the iterated data `iterData n`. -/
structure Invariant (s : ℤ) (hs : 1 ≤ s) (n : ℕ) (h : (s - 1).toNat = n) : Prop where
  /-- `Z_s = f⁻¹(Im α^n)` under `E_1 ≅ E`. -/
  hZ : E.Z () s = (Subobject.pullback (D.pageOneIso.hom ≫ X.f)).obj (imageSubobject (X.α ^ n))
  /-- `B_s = g(Ker α^n)` under `E_1 ≅ E`. -/
  hB : E.B () s = (Subobject.exists (X.g ≫ D.pageOneIso.inv)).obj (kernelSubobject (X.α ^ n))
  /-- `q_s ≫ pageIso ≫ f^{(n)} ≫ ι` is the restriction of `f` to `Z_s ⊆ E_1 ≅ E`. -/
  q_f : E.q () s hs ≫ (D.pageIso s hs n h).hom ≫ (X.derivedIter n).f ≫ (X.iterData n).ι =
    (E.Z () s).arrow ≫ D.pageOneIso.hom ≫ X.f
  /-- `π ≫ g^{(n)} ≫ pageIso⁻¹` is the class in `E_s = Z_s/B_s` of the lift of `g` to `Z_s`. -/
  π_g : (X.iterData n).π ≫ (X.derivedIter n).g ≫ (D.pageIso s hs n h).inv =
    (E.Z () s).factorThru (X.g ≫ D.pageOneIso.inv) (X.factors_of_eq _ _ hZ) ≫ E.q () s hs

namespace Invariant

variable {D} {s : ℤ} {hs : 1 ≤ s} {n : ℕ} {h : (s - 1).toNat = n}

/-- The `Package` at stage `s` built from an invariant: `Y = X^{(n)}`, `φ = pageIso`, `ι`, `π`
from `iterData n`, and `ℓ` the lift of `g ≫ pageOneIso⁻¹` to `Z_s`. An `abbrev` on purpose
(load-bearing): `Invariant.step` needs its projections to reduce. -/
noncomputable abbrev toPackage (I : D.Invariant s hs n h) :
    Package X E D.pageOneIso s hs n where
  Y := X.derivedIter n
  φ := D.pageIso s hs n h
  hd := D.d_eq s hs n h
  ι := (X.iterData n).ι
  π := (X.iterData n).π
  π_ι := (X.iterData n).π_ι
  α_ι := (X.iterData n).α_ι
  π_α := (X.iterData n).π_α
  hZ := I.hZ
  hB := I.hB
  q_f := I.q_f
  ℓ := (E.Z () s).factorThru (X.g ≫ D.pageOneIso.inv) (X.factors_of_eq _ _ I.hZ)
  ℓ_arrow := Subobject.factorThru_arrow _ _ _
  π_g := I.π_g

/-- The inductive step: the invariant at stage `s` gives the invariant at stage `s + 1`, by the
generic step for `toPackage` with the page isos fixed to `pageIso` and the iterated data
transported along `iterData_succ`. -/
theorem step (I : D.Invariant s hs n h) : D.Invariant (s + 1) (by omega) (n + 1) (by omega) where
  hZ := I.toPackage.Z_step
  hB := I.toPackage.B_step
  q_f := by
    rw [D.pageIso_succ_hom s hs n h, X.derivedIterSuccIso_hom,
      IterData.f_ι_eqToHom _ (X.iterData_succ n)]
    simp only [assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp]
    exact (I.toPackage.q_f_step (Abelian.image.ι (X.derivedIter n).α)
      (X.derivedIter n).f' (X.derivedIter n).homologyπ_f'_ι (D.homologyIso s hs n h)
      (fun z hz hz' ↦ D.liftCycles_homologyπ_homologyIso_hom s hs n h z hz hz'))
  π_g := by
    rw [D.pageIso_succ_inv s hs n h, X.derivedIterSuccIso_inv, ← assoc,
      IterData.π_g_eqToHom _ (X.iterData_succ n)]
    simp only [assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp]
    exact (I.toPackage.π_g_step (Abelian.factorThruImage (X.derivedIter n).α)
      (X.derivedIter n).g' (X.derivedIter n).factorThruImage_g' (D.homologyIso s hs n h)
      (fun z hz hz' ↦ D.liftCycles_homologyπ_homologyIso_hom s hs n h z hz hz') _
      (Subobject.factorThru_arrow _ _ _))

end Invariant

/-- The base case of the induction: the invariant at stage `s = 1` (`n = 0`), from `Z_1 = E_1`,
`B_1 = 0` and `iterData 0 = iterDataZero`. -/
theorem invariant_one : D.Invariant 1 le_rfl 0 rfl where
  hZ := X.Z_one _ _
  hB := X.B_one _ _
  q_f := by
    rw [q_self, D.pageOneIso_hom, IterData.f_ι_eqToHom _ X.iterData_zero]
    dsimp only [iterDataZero]
    simp [assoc, comp_id]
  π_g := by
    rw [q_self, Subobject.factorThru_arrow, D.pageOneIso_inv, ← assoc,
      IterData.π_g_eqToHom _ X.iterData_zero]
    dsimp only [iterDataZero]
    simp [assoc, id_comp]

/-- The invariant holds at every stage `s ≥ 1`, by induction on `n = s - 1`. -/
theorem invariant (D : X.DerivedPages E) :
    ∀ (n : ℕ) (s : ℤ) (hs : 1 ≤ s) (h : (s - 1).toNat = n), D.Invariant s hs n h
  | 0, s, hs, h => by
    obtain rfl : s = 1 := by omega
    exact D.invariant_one
  | n + 1, s, hs, h => by
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    exact (D.invariant n s' (by omega) (by omega)).step

/-- `Z_s = f⁻¹(Im α^n)` under `E_1 ≅ E`, for `n = s - 1`. -/
theorem Z_eq (s : ℤ) (hs : 1 ≤ s) (n : ℕ) (h : (s - 1).toNat = n) :
    E.Z () s = (Subobject.pullback (D.pageOneIso.hom ≫ X.f)).obj (imageSubobject (X.α ^ n)) :=
  (D.invariant n s hs h).hZ

/-- `B_s = g(Ker α^n)` under `E_1 ≅ E`, for `n = s - 1`. -/
theorem B_eq (s : ℤ) (hs : 1 ≤ s) (n : ℕ) (h : (s - 1).toNat = n) :
    E.B () s = (Subobject.exists (X.g ≫ D.pageOneIso.inv)).obj (kernelSubobject (X.α ^ n)) :=
  (D.invariant n s hs h).hB

/-- Stacks 011T: `Z_{r+1} = f⁻¹(Im α^r)` under `E_1 ≅ E`, for any ungraded spectral sequence
`E` whose pages are the derived couples of `X`. -/
@[stacks 011T "`Z_{r+1} = f⁻¹(Im α^r)` under `E_1 ≅ E`, for any `E` with derived-couple pages"]
theorem Z_succ (r : ℕ) :
    E.Z () (r + 1) =
      (Subobject.pullback (D.pageOneIso.hom ≫ X.f)).obj (imageSubobject (X.α ^ r)) :=
  D.Z_eq (r + 1) (by omega) r (by omega)

/-- Stacks 011T: `B_{r+1} = g(Ker α^r)` under `E_1 ≅ E`, for any ungraded spectral sequence
`E` whose pages are the derived couples of `X`. -/
@[stacks 011T "`B_{r+1} = g(Ker α^r)` under `E_1 ≅ E`, for any `E` with derived-couple pages"]
theorem B_succ (r : ℕ) :
    E.B () (r + 1) =
      (Subobject.exists (X.g ≫ D.pageOneIso.inv)).obj (kernelSubobject (X.α ^ r)) :=
  D.B_eq (r + 1) (by omega) r (by omega)

/-- `g ≫ pageOneIso⁻¹ : A ⟶ E_1` factors through `Z_{r+1}` (since `g ≫ f = 0`). -/
theorem factors_g (r : ℕ) : (E.Z () (r + 1)).Factors (X.g ≫ D.pageOneIso.inv) :=
  X.factors_of_eq E D.pageOneIso (D.Z_succ r)

/-- The formula for `d_s` (`n = s - 1`): for `x : T ⟶ Z_s` and `y : T ⟶ A` with `f x = α^n y`
under `E_1 ≅ E`, `d_s(x̄) = \overline{g y}`, the class of the lift of `y ≫ g` (Stacks' `g ∘ y`)
to `Z_s` given by any factorisation witness `hfac`. -/
theorem q_d_eq (s : ℤ) (hs : 1 ≤ s) (n : ℕ) (h : (s - 1).toNat = n)
    (hfac : (E.Z () s).Factors (X.g ≫ D.pageOneIso.inv)) {T : C} (x : T ⟶ (E.Z () s : C))
    (y : T ⟶ X.A) (hxy : x ≫ (E.Z () s).arrow ≫ D.pageOneIso.hom ≫ X.f = y ≫ X.α ^ n) :
    x ≫ E.q () s hs ≫ E.d s hs =
      y ≫ (E.Z () s).factorThru (X.g ≫ D.pageOneIso.inv) hfac ≫ E.q () s hs :=
  (D.invariant n s hs h).toPackage.q_d_factorThru hfac x y hxy

/-- Stacks 011T, the differential: for `x : T ⟶ Z_{r+1}` and `y : T ⟶ A` with `f x = α^r y`
under `E_1 ≅ E`, `d_{r+1}(x̄) = \overline{g y}`: here `x̄ = x ≫ q_{r+1} : T ⟶ E_{r+1}` and
`\overline{g y}` is the class of the lift of `y ≫ g` (Stacks' `g ∘ y`) to `Z_{r+1}` (which
exists by `factors_g`). -/
@[stacks 011T "`d_{r+1}(x̄) = \\overline{g y}` for `x ∈ Z_{r+1}`, `y ∈ A` with `f x = α^r y`"]
theorem d_succ (r : ℕ) {T : C} (x : T ⟶ (E.Z () (r + 1) : C)) (y : T ⟶ X.A)
    (hxy : x ≫ (E.Z () (r + 1)).arrow ≫ D.pageOneIso.hom ≫ X.f = y ≫ X.α ^ r) :
    x ≫ E.q () (r + 1) ≫ E.d (r + 1) =
      y ≫ (E.Z () (r + 1)).factorThru (X.g ≫ D.pageOneIso.inv) (D.factors_g r) ≫
        E.q () (r + 1) :=
  D.q_d_eq (r + 1) (by omega) r (by omega) (D.factors_g r) x y hxy

end DerivedPages

/-! ### 011T for `X.spectralSequence` -/

/-- `Z_{r+1} = f⁻¹(Im α^r)` in the spectral sequence of `X`, under `E_1 ≅ E`. -/
theorem spectralSequence_Z_succ (r : ℕ) :
    X.spectralSequence.Z () (r + 1) =
      (Subobject.pullback (X.spectralSequenceXOneIso.hom ≫ X.f)).obj (imageSubobject (X.α ^ r)) :=
  X.spectralSequenceDerivedPages.Z_succ r

/-- `B_{r+1} = g(Ker α^r)` in the spectral sequence of `X`, under `E_1 ≅ E`. -/
theorem spectralSequence_B_succ (r : ℕ) :
    X.spectralSequence.B () (r + 1) =
      (Subobject.exists (X.g ≫ X.spectralSequenceXOneIso.inv)).obj (kernelSubobject (X.α ^ r)) :=
  X.spectralSequenceDerivedPages.B_succ r

/-- The differential `d_{r+1}` of the spectral sequence of `X`: for `x : T ⟶ Z_{r+1}` and
`y : T ⟶ A` with `f x = α^r y` under `E_1 ≅ E`, `d_{r+1}(x̄) = \overline{g y}`. -/
theorem spectralSequence_d_succ (r : ℕ) {T : C} (x : T ⟶ (X.spectralSequence.Z () (r + 1) : C))
    (y : T ⟶ X.A)
    (hxy : x ≫ (X.spectralSequence.Z () (r + 1)).arrow ≫ X.spectralSequenceXOneIso.hom ≫ X.f =
      y ≫ X.α ^ r) :
    x ≫ X.spectralSequence.q () (r + 1) ≫ X.spectralSequence.d (r + 1) =
      y ≫ (X.spectralSequence.Z () (r + 1)).factorThru (X.g ≫ X.spectralSequenceXOneIso.inv)
        (X.spectralSequenceDerivedPages.factors_g r) ≫ X.spectralSequence.q () (r + 1) :=
  X.spectralSequenceDerivedPages.d_succ r x y hxy

add_to_stacks 011T "the inclusions `B_r ⊆ Z_r` of the towers `0 = B_1 ⊆ … ⊆ Z_1 = E`"
  CategoryTheory.SpectralSequence.B_le_Z
add_to_stacks 011T "the inclusions `B_r ⊆ B_{r+1}` of the tower `0 = B_1 ⊆ B_2 ⊆ …`"
  CategoryTheory.SpectralSequence.B_monotone
add_to_stacks 011T "the inclusions `Z_{r+1} ⊆ Z_r` of the tower `… ⊆ Z_2 ⊆ Z_1 = E`"
  CategoryTheory.SpectralSequence.Z_antitone

end CategoryTheory.ExactCouple
