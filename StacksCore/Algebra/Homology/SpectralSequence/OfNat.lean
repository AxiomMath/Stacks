module

public import StacksCore.Algebra.Homology.SpectralSequence.Basic

/-! # Ungraded spectral sequences from a sequence `(X n, d n)`: `Ungraded.ofEndo`, `Ungraded.ofNat`

Stacks 011N describes an ungraded spectral sequence as a system `(E_r, d_r)_{r ≥ r₀}` of objects
with endomorphisms `d_r` squaring to zero and identifications `E_{r+1} ≅ Ker(d_r)/Im(d_r)`. This
file provides the constructor for such data indexed by `ℕ`: given `X : ℕ → C`,
`d n : X n ⟶ X n` with `d n ≫ d n = 0` and isomorphisms `e n : Ker(d n)/Im(d n) ≅ X (n + 1)`,
`SpectralSequence.Ungraded.ofNat r₀ X d hd e` is the ungraded spectral sequence with
`(E_{r₀+n}, d_{r₀+n}) = (X n, d n)` and `E_{r₀+n+1} ≅ Ker(d n)/Im(d n)` given by `e n`.

* `Ungraded.ofEndo E d hd` is the one-object homological complex `(E, d)` of shape
  `ComplexShape.refl Unit`, the page of an ungraded spectral sequence. Its cycles and homology are
  identified with those of the short complex `E ⟶ E ⟶ E` (`ofEndoCyclesIso`,
  `ofEndoHomologyIso`) through the universal properties `cyclesIsKernel`, `homologyIsCokernel`
  (never through the auxiliary short complex `sc'`), with the compatibilities with `iCycles`,
  `toCycles`, `liftCycles` and `homologyπ` that the spectral sequence of an exact couple needs.
* `Ungraded.ofNat r₀ X d hd e` is the spectral sequence itself; its `r`-th page is
  `ofEndo (X (r - r₀).toNat) _ _`. The API is stated in the convention of
  `StacksCore.Algebra.Homology.SpectralSequence.Tower`: for `(r : ℤ) (hr : r₀ ≤ r) (n : ℕ)
  (h : (r - r₀).toNat = n)`, `ofNatPageXIso : E_r ≅ X n`, `ofNat_d_ofNatPageXIso_hom`
  (`d_r = d n` under it), `ofNatPageCyclesIso`, `ofNatPageHomologyIso` (cycles and homology of
  `E_r` are those of `(X n, d n)`), `ofNat_homologyIso_hom` (the identification
  `E_{r+1} ≅ H(E_r)` is `e n`) and `liftCycles_homologyπ_ofNatPageHomologyIso_hom` (classes of
  cycles correspond). The explicit `n` and `h` let `subst h` eliminate the `toNat` in proofs.

`ofEndo` and `ofNat` are `abbrev`s on purpose (load-bearing): with a `def`, the `simps`-generated
`ofEndo_d` is not type-correct at implicit transparency, and `(ofNat r₀ X d hd e).X r hr` must be
reducibly `X (r - r₀).toNat` for the statements about the spectral sequence of an exact couple
to typecheck.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace SpectralSequence.Ungraded

/-- The one-object complex `(E, d)` of shape `ComplexShape.refl Unit`: the page of an ungraded
spectral sequence. An `abbrev` on purpose (load-bearing): with a `def` the generated `ofEndo_d`
is not type-correct at implicit transparency. -/
@[simps]
abbrev ofEndo (E : C) (d : E ⟶ E) (hd : d ≫ d = 0) :
    HomologicalComplex C (ComplexShape.refl Unit) where
  X _ := E
  d _ _ := d
  shape _ _ h := (h rfl).elim
  d_comp_d' _ _ _ _ _ := hd

section ofEndo

variable (E : C) (d : E ⟶ E) (hd : d ≫ d = 0)

/-- The cycles of the one-object complex `(E, d)` are the cycles of the short complex
`E ⟶ E ⟶ E`, both being kernels of `d`. -/
noncomputable def ofEndoCyclesIso :
    (ofEndo E d hd).cycles () ≅ (ShortComplex.mk d d hd).cycles :=
  IsLimit.conePointUniqueUpToIso ((ofEndo E d hd).cyclesIsKernel () () rfl)
    (ShortComplex.mk d d hd).cyclesIsKernel

/-- `ofEndoCyclesIso` is compatible with the inclusions of the cycles. -/
@[reassoc (attr := simp)]
lemma ofEndoCyclesIso_hom_iCycles :
    (ofEndoCyclesIso E d hd).hom ≫ (ShortComplex.mk d d hd).iCycles =
      (ofEndo E d hd).iCycles () := by
  unfold ofEndoCyclesIso
  simpa using IsLimit.conePointUniqueUpToIso_hom_comp ((ofEndo E d hd).cyclesIsKernel () () rfl)
    (ShortComplex.mk d d hd).cyclesIsKernel WalkingParallelPair.zero

/-- The inverse of `ofEndoCyclesIso` is compatible with the inclusions of the cycles. -/
@[reassoc (attr := simp)]
lemma ofEndoCyclesIso_inv_iCycles :
    (ofEndoCyclesIso E d hd).inv ≫ (ofEndo E d hd).iCycles () =
      (ShortComplex.mk d d hd).iCycles := by
  rw [Iso.inv_comp_eq, ofEndoCyclesIso_hom_iCycles]

/-- `ofEndoCyclesIso` is compatible with the maps `E ⟶ Ker d` induced by `d`. -/
@[reassoc (attr := simp)]
lemma toCycles_ofEndoCyclesIso_hom :
    (ofEndo E d hd).toCycles () () ≫ (ofEndoCyclesIso E d hd).hom =
      (ShortComplex.mk d d hd).toCycles := by
  rw [← cancel_mono (ShortComplex.mk d d hd).iCycles, assoc, ofEndoCyclesIso_hom_iCycles,
    HomologicalComplex.toCycles_i, ShortComplex.toCycles_i]

/-- `ofEndoCyclesIso` is compatible with the lifts of cycles `z : T ⟶ E`, `z ≫ d = 0`. -/
@[reassoc (attr := simp)]
lemma liftCycles_ofEndoCyclesIso_hom {T : C} (z : T ⟶ E) (hz : z ≫ d = 0) :
    (ofEndo E d hd).liftCycles z () rfl hz ≫ (ofEndoCyclesIso E d hd).hom =
      (ShortComplex.mk d d hd).liftCycles z hz := by
  rw [← cancel_mono (ShortComplex.mk d d hd).iCycles, assoc, ofEndoCyclesIso_hom_iCycles,
    HomologicalComplex.liftCycles_i, ShortComplex.liftCycles_i]

/-- The homology of the short complex `E ⟶ E ⟶ E` is a cokernel of `E ⟶ Ker d`, with `Ker d`
spelled as the cycles of the one-object complex `(E, d)`. -/
noncomputable def ofEndoHomologyIsCokernel :
    IsColimit (CokernelCofork.ofπ (f := (ofEndo E d hd).toCycles () ())
      ((ofEndoCyclesIso E d hd).hom ≫ (ShortComplex.mk d d hd).homologyπ)
      (by rw [toCycles_ofEndoCyclesIso_hom_assoc, ShortComplex.toCycles_comp_homologyπ])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun g hg ↦ (ShortComplex.mk d d hd).descHomology ((ofEndoCyclesIso E d hd).inv ≫ g)
      (by rw [← toCycles_ofEndoCyclesIso_hom, assoc, Iso.hom_inv_id_assoc, hg]))
    (fun g hg ↦ by simp)
    (fun g hg m hm ↦ by
      rw [← cancel_epi ((ofEndoCyclesIso E d hd).hom ≫ (ShortComplex.mk d d hd).homologyπ), hm]
      simp)

/-- `H(E, d) ≅ Ker d / Im d`: the homology of the one-object complex `(E, d)` is the homology of
the short complex `E ⟶ E ⟶ E`. -/
noncomputable def ofEndoHomologyIso :
    (ofEndo E d hd).homology () ≅ (ShortComplex.mk d d hd).homology :=
  IsColimit.coconePointUniqueUpToIso ((ofEndo E d hd).homologyIsCokernel () () rfl)
    (ofEndoHomologyIsCokernel E d hd)

/-- `ofEndoHomologyIso` is compatible with the projections `Ker d ↠ H` through
`ofEndoCyclesIso`. -/
@[reassoc (attr := simp)]
lemma homologyπ_ofEndoHomologyIso_hom :
    (ofEndo E d hd).homologyπ () ≫ (ofEndoHomologyIso E d hd).hom =
      (ofEndoCyclesIso E d hd).hom ≫ (ShortComplex.mk d d hd).homologyπ := by
  unfold ofEndoHomologyIso
  simpa using IsColimit.comp_coconePointUniqueUpToIso_hom
    ((ofEndo E d hd).homologyIsCokernel () () rfl) (ofEndoHomologyIsCokernel E d hd)
    WalkingParallelPair.one

/-- The inverse of `ofEndoHomologyIso` is compatible with the projections `Ker d ↠ H`. -/
@[reassoc (attr := simp)]
lemma homologyπ_ofEndoHomologyIso_inv :
    (ShortComplex.mk d d hd).homologyπ ≫ (ofEndoHomologyIso E d hd).inv =
      (ofEndoCyclesIso E d hd).inv ≫ (ofEndo E d hd).homologyπ () := by
  rw [Iso.comp_inv_eq, assoc, homologyπ_ofEndoHomologyIso_hom, Iso.inv_hom_id_assoc]

/-- Classes of cycles correspond under `ofEndoHomologyIso`: the class of `z : T ⟶ E` with
`z ≫ d = 0` in `H(E, d)` is sent to its class in the homology of `E ⟶ E ⟶ E`. -/
@[reassoc]
lemma liftCycles_homologyπ_ofEndoHomologyIso_hom {T : C} (z : T ⟶ E) (hz : z ≫ d = 0) :
    (ofEndo E d hd).liftCycles z () rfl hz ≫ (ofEndo E d hd).homologyπ () ≫
        (ofEndoHomologyIso E d hd).hom =
      (ShortComplex.mk d d hd).liftCycles z hz ≫ (ShortComplex.mk d d hd).homologyπ := by
  rw [homologyπ_ofEndoHomologyIso_hom, liftCycles_ofEndoCyclesIso_hom_assoc]

end ofEndo

section ofNat

variable (r₀ : ℤ) (X : ℕ → C) (d : ∀ n, X n ⟶ X n) (hd : ∀ n, d n ≫ d n = 0)
  (e : ∀ n, (ShortComplex.mk (d n) (d n) (hd n)).homology ≅ X (n + 1))

/-- The ungraded spectral sequence `(E_{r₀+n}, d_{r₀+n}) = (X n, d n)`, with
`E_{r₀+n+1} ≅ Ker(d n)/Im(d n)` given by `e n`. An `abbrev` (load-bearing):
`(ofNat r₀ X d hd e).X r hr` must be reducibly `X (r - r₀).toNat`. -/
@[simps]
noncomputable abbrev ofNat : Ungraded C r₀ where
  page r _ := ofEndo (X (r - r₀).toNat) (d _) (hd _)
  iso r r' _ hrr' hr :=
    ofEndoHomologyIso _ _ _ ≪≫ e _ ≪≫ eqToIso (congrArg X (by omega))

/-- `E_r ≅ X n` for `n = r - r₀`. -/
noncomputable def ofNatPageXIso (r : ℤ) (hr : r₀ ≤ r) (n : ℕ) (h : (r - r₀).toNat = n) :
    (ofNat r₀ X d hd e).X r hr ≅ X n :=
  eqToIso (congrArg X h)

/-- The forward map of `ofNatPageXIso` is an `eqToHom`. -/
@[simp]
lemma ofNatPageXIso_hom (r : ℤ) (hr : r₀ ≤ r) (n : ℕ) (h : (r - r₀).toNat = n) :
    (ofNatPageXIso r₀ X d hd e r hr n h).hom = eqToHom (congrArg X h) := by
  unfold ofNatPageXIso
  exact eqToIso.hom _

/-- The inverse of `ofNatPageXIso` is an `eqToHom`. -/
@[simp]
lemma ofNatPageXIso_inv (r : ℤ) (hr : r₀ ≤ r) (n : ℕ) (h : (r - r₀).toNat = n) :
    (ofNatPageXIso r₀ X d hd e r hr n h).inv = eqToHom (congrArg X h).symm := by
  unfold ofNatPageXIso
  exact eqToIso.inv _

/-- `d_r = d n` through `E_r ≅ X n`, for `n = r - r₀`. -/
@[reassoc]
lemma ofNat_d_ofNatPageXIso_hom (r : ℤ) (hr : r₀ ≤ r) (n : ℕ) (h : (r - r₀).toNat = n) :
    (ofNat r₀ X d hd e).d r hr ≫ (ofNatPageXIso r₀ X d hd e r hr n h).hom =
      (ofNatPageXIso r₀ X d hd e r hr n h).hom ≫ d n := by
  rw [ofNatPageXIso_hom]
  exact eqToHom_naturality d h

/-- `d_r` is the conjugate of `d n` by `E_r ≅ X n`, for `n = r - r₀`. -/
lemma ofNat_d_eq (r : ℤ) (hr : r₀ ≤ r) (n : ℕ) (h : (r - r₀).toNat = n) :
    (ofNat r₀ X d hd e).d r hr = (ofNatPageXIso r₀ X d hd e r hr n h).hom ≫ d n ≫
      (ofNatPageXIso r₀ X d hd e r hr n h).inv := by
  rw [← ofNat_d_ofNatPageXIso_hom_assoc, Iso.hom_inv_id, comp_id]

/-- The cycles of `E_r` are the cycles of `(X n, d n)`, for `n = r - r₀`. -/
noncomputable def ofNatPageCyclesIso (r : ℤ) (hr : r₀ ≤ r) (n : ℕ) (h : (r - r₀).toNat = n) :
    ((ofNat r₀ X d hd e).page r hr).cycles () ≅ (ShortComplex.mk (d n) (d n) (hd n)).cycles :=
  eqToIso (congrArg (fun k ↦ (ofEndo (X k) (d k) (hd k)).cycles ()) h) ≪≫
    ofEndoCyclesIso (X n) (d n) (hd n)

/-- `ofNatPageCyclesIso` is compatible with the inclusions of the cycles, through
`ofNatPageXIso`. -/
@[reassoc (attr := simp)]
lemma ofNatPageCyclesIso_hom_iCycles (r : ℤ) (hr : r₀ ≤ r) (n : ℕ) (h : (r - r₀).toNat = n) :
    (ofNatPageCyclesIso r₀ X d hd e r hr n h).hom ≫ (ShortComplex.mk (d n) (d n) (hd n)).iCycles =
      ((ofNat r₀ X d hd e).page r hr).iCycles () ≫ (ofNatPageXIso r₀ X d hd e r hr n h).hom := by
  subst h
  simp [ofNatPageCyclesIso, ofNatPageXIso]

/-- `H(E_r, d_r) ≅ Ker(d n)/Im(d n)` for `n = r - r₀`. -/
noncomputable def ofNatPageHomologyIso (r : ℤ) (hr : r₀ ≤ r) (n : ℕ) (h : (r - r₀).toNat = n) :
    ((ofNat r₀ X d hd e).page r hr).homology () ≅ (ShortComplex.mk (d n) (d n) (hd n)).homology :=
  eqToIso (congrArg (fun k ↦ (ofEndo (X k) (d k) (hd k)).homology ()) h) ≪≫
    ofEndoHomologyIso (X n) (d n) (hd n)

/-- `ofNatPageHomologyIso` is compatible with the projections `Ker d ↠ H`, through
`ofNatPageCyclesIso`. -/
@[reassoc (attr := simp)]
lemma homologyπ_ofNatPageHomologyIso_hom (r : ℤ) (hr : r₀ ≤ r) (n : ℕ)
    (h : (r - r₀).toNat = n) :
    ((ofNat r₀ X d hd e).page r hr).homologyπ () ≫
        (ofNatPageHomologyIso r₀ X d hd e r hr n h).hom =
      (ofNatPageCyclesIso r₀ X d hd e r hr n h).hom ≫
        (ShortComplex.mk (d n) (d n) (hd n)).homologyπ := by
  subst h
  simp [ofNatPageCyclesIso, ofNatPageHomologyIso]

/-- The identification `E_{r+1} ≅ H(E_r, d_r)` of `ofNat` is `e n`, for `n = r - r₀`. -/
lemma ofNat_homologyIso_hom (r : ℤ) (hr : r₀ ≤ r) (n : ℕ) (h : (r - r₀).toNat = n) :
    ((ofNat r₀ X d hd e).homologyIso r hr).hom ≫
        (ofNatPageXIso r₀ X d hd e (r + 1) (by omega) (n + 1) (by omega)).hom =
      (ofNatPageHomologyIso r₀ X d hd e r hr n h).hom ≫ (e n).hom := by
  subst h
  simp [ofNatPageXIso, ofNatPageHomologyIso, homologyIso]

/-- Classes of cycles correspond under `ofNatPageHomologyIso`: the class of a cycle `z` of `E_r`
is sent to the class of `z ≫ (E_r ≅ X n).hom` in `Ker(d n)/Im(d n)`. -/
lemma liftCycles_homologyπ_ofNatPageHomologyIso_hom (r : ℤ) (hr : r₀ ≤ r) (n : ℕ)
    (h : (r - r₀).toNat = n) {T : C} (z : T ⟶ (ofNat r₀ X d hd e).X r hr)
    (hz : z ≫ (ofNat r₀ X d hd e).d r hr = 0)
    (hz' : (z ≫ (ofNatPageXIso r₀ X d hd e r hr n h).hom) ≫ d n = 0) :
    ((ofNat r₀ X d hd e).page r hr).liftCycles z () rfl hz ≫
        ((ofNat r₀ X d hd e).page r hr).homologyπ () ≫
          (ofNatPageHomologyIso r₀ X d hd e r hr n h).hom =
      (ShortComplex.mk (d n) (d n) (hd n)).liftCycles
          (z ≫ (ofNatPageXIso r₀ X d hd e r hr n h).hom) hz' ≫
        (ShortComplex.mk (d n) (d n) (hd n)).homologyπ := by
  subst h
  simp [ofNatPageHomologyIso, ofNatPageXIso]

end ofNat

end SpectralSequence.Ungraded

end CategoryTheory
