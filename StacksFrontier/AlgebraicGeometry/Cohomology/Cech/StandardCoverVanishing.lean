module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.Zariski.StandardOpenCover
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.RingTheory.CechAcyclicity

/-!
# Čech cohomology of a quasi-coherent module on an affine open

Let `X` be a scheme, let `F` be a quasi-coherent `𝒪_X`-module, let `U` be an affine open of `X`
and let `g : Fin n → Γ(X, U)` be a finite family whose basic opens cover `Spec Γ(X, U)`. This
file proves that the Čech cohomology of `F` with respect to the covering of `U` by the ambient
basic opens `X.basicOpen (g i)` vanishes in every positive degree.

The proof is a comparison of two complexes. On the geometric side, Mathlib's
`CategoryTheory.cechComplexFunctor` applied to the underlying abelian presheaf of `F` has, by
`Stacks.CategoryTheory.CechComplex.isLimitFan`, degree `m` term the product over all tuples
`x : Fin (m + 1) → Fin n` of the sections of `F` over `inter V x`, where `V i = X.basicOpen (g i)`.
On the algebraic side, `Stacks.RingTheory.CechAcyclicity.CechTerm` is the product of the
localizations of `Γ(F, U)` away from the products `tupleProd g x = ∏ k, g (x k)`. The two agree
termwise because `inter V x = X.basicOpen (tupleProd g x)` and because, by
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`, the sections of a
quasi-coherent module over a basic open of an affine open are the localization of its sections
over that affine open. The differentials agree because both are alternating sums of restriction
maps, and a restriction map between localizations is determined by its composite with the
localization map. The vanishing then follows from
`Stacks.RingTheory.CechAcyclicity.cech_exact`.

## Main definitions

* `PrimeSpectrum.IsStandardOpenCover` and
  `PrimeSpectrum.IsStandardOpenCoverOfSpectrum`, from
  `StacksFrontier.AlgebraicGeometry.Scheme.Zariski.StandardOpenCover`: a finite family of elements
  of a commutative ring whose basic opens cover a given basic open, respectively the whole prime
  spectrum.
* `restrictLE`: restriction of sections of an `𝒪_X`-module between two opens contained in `U`,
  as a `Γ(X, U)`-linear map.
* `interEquiv`: the identification of the localization of `Γ(F, U)` away from `tupleProd g x`
  with the sections of `F` over `inter V x`.
* `toCechTerm`, `ofCechTerm` and `cechTermIso`: the degreewise comparison between the Čech
  complex of the covering and the algebraic Čech complex of `g`.

## Main results

* `isZero_cechCohomology_of_isStandardOpenCover` is Tag 01X9: positive-degree Čech cohomology of
  a quasi-coherent module vanishes for a finite standard open covering of an affine open.
* `exactAt_cechComplex`: the underlying exactness statement, in every positive degree.
* `inter_eq_basicOpen`: the intersection of the members of the covering selected by a tuple is
  the basic open of the product of the corresponding sections.
* `d_comp_toCechTerm`: the degreewise comparison commutes with the two differentials.

## Implementation notes

The affine open `U` remains an open of the ambient scheme `X` and the members of the covering are
the ambient basic opens `X.basicOpen (g i)`, so no restriction comparison along `U ⟶ X` is
needed. Čech cohomology is the homology of `cechComplexFunctor` applied to the underlying
abelian presheaf of `F`, which is what `SheafOfModules.toSheaf` produces; the two presheaves are
definitionally equal, and the statement of Tag 01X9 is phrased with `toSheaf` as in the source.

For `W ≤ U` the ring `Γ(X, U)` does not act on `Γ(F, W)` by instance search, so the module
structure is supplied explicitly by
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE` and appears as a `letI` in the
statements below, exactly as in that file. Everything is stated for the twist `f = 1` of the
algebraic Čech complex, whose degree `m` term localizes away from `1 * tupleProd g x`; the
factor `1` is kept rather than cancelled so that the terms match
`Stacks.RingTheory.CechAcyclicity.CechTerm` syntactically.

The comparison is only ever used degreewise and elementwise, so it is not assembled into an
isomorphism of cochain complexes: exactness of the geometric complex is deduced from
`ShortComplex.ab_exact_iff` by transporting a cocycle through `toCechTerm`, applying
`cech_exact`, and transporting the resulting primitive back through `ofCechTerm`. The packaging
of the algebraic complex as an object of `CochainComplex (ModuleCat Γ(X, U)) ℕ`, with the same
vanishing statement, is in `StacksFrontier.RingTheory.CechComplexHomology`.

## References

* [Stacks Project, Tag 01HT](https://stacks.math.columbia.edu/tag/01HT)
* [Stacks Project, Tag 01X9](https://stacks.math.columbia.edu/tag/01X9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.CategoryTheory.CechComplex Stacks.RingTheory.CechAcyclicity

universe u

namespace Stacks.Cohomology.Cech

/-! ### Standard open coverings -/

/-- A finite family of elements is a standard open covering of the whole prime spectrum exactly
when it generates the unit ideal. -/
theorem span_range_eq_top_of_isStandardOpenCoverOfSpectrum {R : Type u} [CommRing R] {n : ℕ}
    {g : Fin n → R} (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) :
    Ideal.span (Set.range g) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp (hg.trans PrimeSpectrum.basicOpen_one)

/-! ### Auxiliary lemmas on infima and on morphisms of abelian groups -/

/-- The infimum of a family indexed by `Fin (m + 1)` splits off its first member. -/
theorem iInf_fin_succ {L : Type*} [CompleteLattice L] {m : ℕ} (h : Fin (m + 1) → L) :
    ⨅ k, h k = h 0 ⊓ ⨅ k : Fin m, h k.succ :=
  le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun k ↦ iInf_le _ k.succ))
    (le_iInf fun k ↦ Fin.cases inf_le_left (fun j ↦ inf_le_right.trans (iInf_le _ j)) k)

/-- A finite sum of morphisms of abelian groups, evaluated at an element. -/
theorem sum_hom_apply {P Q : AddCommGrpCat.{u}} {ι : Type*} (s : Finset ι) (φ : ι → (P ⟶ Q))
    (x : P) : (∑ i ∈ s, φ i) x = ∑ i ∈ s, φ i x :=
  map_sum (AddMonoidHom.mk' (fun ψ : P ⟶ Q ↦ ψ x)
    fun a b ↦ AddCommGrpCat.hom_add_apply a b x) φ s

/-- An integer multiple of a morphism of abelian groups, evaluated at an element. -/
theorem zsmul_hom_apply {P Q : AddCommGrpCat.{u}} (k : ℤ) (φ : P ⟶ Q) (x : P) :
    (k • φ) x = k • φ x := rfl

/-! ### The intersections of a standard covering by basic opens -/

variable {X : Scheme.{u}}

/-- The basic open of the product of the sections selected by a tuple is the intersection of the
basic opens of those sections. -/
theorem basicOpen_tupleProd {U : X.Opens} {n : ℕ} (g : Fin n → Γ(X, U)) :
    ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      X.basicOpen (tupleProd g x) = ⨅ k, X.basicOpen (g (x k)) := by
  intro m
  induction m with
  | zero =>
    intro x
    rw [tupleProd, Fin.prod_univ_one, iInf_fin_succ, iInf_of_empty, inf_top_eq]
  | succ m ih =>
    intro x
    rw [tupleProd, Fin.prod_univ_succ, Scheme.basicOpen_mul, iInf_fin_succ]
    exact congrArg _ (ih fun k ↦ x k.succ)

/-- The intersection of the members of the covering `X.basicOpen (g i)` selected by a tuple `x`
is the basic open of `1 * tupleProd g x`, the twist by `1` matching the degree `m` term of the
algebraic Čech complex. -/
theorem inter_eq_basicOpen {U : X.Opens} {n : ℕ} (g : Fin n → Γ(X, U)) {m : ℕ}
    (x : Fin (m + 1) → Fin n) :
    inter (fun i ↦ X.basicOpen (g i)) x = X.basicOpen (1 * tupleProd g x) := by
  rw [inter_eq_iInf, one_mul, basicOpen_tupleProd]

/-- The intersections occurring in the Čech complex of a standard covering of `U` are opens
of `U`. -/
theorem inter_le {U : X.Opens} {n : ℕ} (g : Fin n → Γ(X, U)) {m : ℕ} (x : Fin (m + 1) → Fin n) :
    inter (fun i ↦ X.basicOpen (g i)) x ≤ U := by
  rw [inter_eq_basicOpen]
  exact X.basicOpen_le _

section Comparison

variable (F : X.Modules) {U : X.Opens}

/-- Restriction of sections of an `𝒪_X`-module between two opens contained in `U`, as a
`Γ(X, U)`-linear map for the module structures obtained by restricting scalars from `U`. -/
noncomputable def restrictLE {W₁ W₂ : X.Opens} (h : W₁ ≤ W₂) (h₂ : W₂ ≤ U) :
    letI := moduleOfLE F (h.trans h₂)
    letI := moduleOfLE F h₂
    Γ(F, W₂) →ₗ[Γ(X, U)] Γ(F, W₁) :=
  letI := moduleOfLE F (h.trans h₂)
  letI := moduleOfLE F h₂
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r z ↦ by
      refine (F.map_smul (homOfLE h) (X.presheaf.map (homOfLE h₂).op r) z).trans ?_
      congr 1
      rw [← Functor.map_comp_apply]
      rfl }

variable [F.IsQuasicoherent] (hU : IsAffineOpen U) {n : ℕ} (g : Fin n → Γ(X, U))

/-- The sections of a quasi-coherent module `F` over the intersection selected by a tuple `x`
are the localization of `Γ(F, U)` away from `1 * tupleProd g x`. -/
noncomputable def interEquiv {m : ℕ} (x : Fin (m + 1) → Fin n) :
    letI := moduleOfLE F (inter_le g x)
    AwayLoc Γ(F, U) (1 * tupleProd g x) ≃ₗ[Γ(X, U)]
      Γ(F, inter (fun i ↦ X.basicOpen (g i)) x) :=
  letI := moduleOfLE F (inter_le g x)
  letI := isLocalizedModule_restrictₗ F hU (1 * tupleProd g x) (inter_eq_basicOpen g x)
    (inter_le g x)
  IsLocalizedModule.iso _ (restrictₗ F (inter_le g x))

/-- The comparison `interEquiv` sends a fraction with denominator `1` to the restriction of its
numerator. -/
theorem interEquiv_mk_one {m : ℕ} (x : Fin (m + 1) → Fin n) (z : Γ(F, U)) :
    interEquiv F hU g x (LocalizedModule.mk z 1) = F.presheaf.map (homOfLE (inter_le g x)).op z :=
  let := moduleOfLE F (inter_le g x)
  let := isLocalizedModule_restrictₗ F hU (1 * tupleProd g x) (inter_eq_basicOpen g x)
    (inter_le g x)
  IsLocalizedModule.iso_mk_one _ (restrictₗ F (inter_le g x)) z

/-- The inverse of the comparison `interEquiv` sends the restriction of a section over `U` to the
fraction with denominator `1`. -/
theorem interEquiv_symm_apply {m : ℕ} (x : Fin (m + 1) → Fin n) (z : Γ(F, U)) :
    letI := moduleOfLE F (inter_le g x)
    (interEquiv F hU g x).symm (F.presheaf.map (homOfLE (inter_le g x)).op z) =
      LocalizedModule.mk z 1 := by
  rw [← interEquiv_mk_one F hU, LinearEquiv.symm_apply_apply]

/-- Omitting the `j`-th index of a tuple enlarges the corresponding intersection. -/
theorem inter_le_inter {m : ℕ} (y : Fin (m + 2) → Fin n) (j : Fin (m + 2)) :
    inter (fun i ↦ X.basicOpen (g i)) y ≤
      inter (fun i ↦ X.basicOpen (g i)) (fun i ↦ y (j.succAbove i)) :=
  leOfHom (interMap (fun i ↦ X.basicOpen (g i)) y j.succAbove)

/-- **The face maps agree.** Under the comparison `interEquiv`, the restriction map of `F` along
the `j`-th face of a tuple is the restriction map `resAway` between localizations of
`Γ(F, U)`. Both are linear maps out of a localization of `Γ(F, U)` whose composite with the
localization map is the restriction to the smaller intersection, so they coincide. -/
theorem resAway_eq_interEquiv {m : ℕ} (y : Fin (m + 2) → Fin n) (j : Fin (m + 2)) :
    letI := moduleOfLE F (inter_le g y)
    letI := moduleOfLE F (inter_le g fun i ↦ y (j.succAbove i))
    resAway Γ(F, U) (dvd_face g 1 y j) =
      (interEquiv F hU g y).symm.toLinearMap ∘ₗ
        (restrictLE F (inter_le_inter g y j) (inter_le g fun i ↦ y (j.succAbove i))) ∘ₗ
          (interEquiv F hU g fun i ↦ y (j.succAbove i)).toLinearMap := by
  let := moduleOfLE F (inter_le g y)
  let := moduleOfLE F (inter_le g fun i ↦ y (j.succAbove i))
  refine LocalizedModule.lift_unique _ _ (isUnit_powers_awayLoc (dvd_face g 1 y j)) _ ?_
  refine LinearMap.ext fun z ↦ ?_
  have h2 : (restrictLE F (inter_le_inter g y j) (inter_le g fun i ↦ y (j.succAbove i)))
      (F.presheaf.map (homOfLE (inter_le g fun i ↦ y (j.succAbove i))).op z) =
      F.presheaf.map (homOfLE (inter_le g y)).op z := by
    change F.presheaf.map _ (F.presheaf.map _ z) = _
    rw [← Functor.map_comp_apply]
    rfl
  change (interEquiv F hU g y).symm
      ((restrictLE F (inter_le_inter g y j) (inter_le g fun i ↦ y (j.succAbove i)))
        ((interEquiv F hU g fun i ↦ y (j.succAbove i)) (LocalizedModule.mk z 1))) = _
  rw [interEquiv_mk_one, h2, interEquiv_symm_apply]
  rfl

/-! ### The degreewise comparison of the two Čech complexes -/

/-- The degree `m` comparison map from the Čech complex of the covering to the algebraic Čech
complex of `g`: its component at a tuple `x` is the projection onto the sections over
`inter V x` followed by the inverse of `interEquiv`. -/
noncomputable def toCechTerm (m : ℕ) :
    ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).X m ⟶
      AddCommGrpCat.of (CechTerm Γ(F, U) g 1 m) :=
  AddCommGrpCat.ofHom (AddMonoidHom.pi fun x ↦
    letI := moduleOfLE F (inter_le g x)
    (interEquiv F hU g x).symm.toLinearMap.toAddMonoidHom.comp
      (ConcreteCategory.hom (π (fun i ↦ X.basicOpen (g i)) F.presheaf m x)))

/-- The component of `toCechTerm` at a tuple. -/
theorem toCechTerm_apply (m : ℕ)
    (z : ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).X m)
    (x : Fin (m + 1) → Fin n) :
    letI := moduleOfLE F (inter_le g x)
    toCechTerm F hU g m z x =
      (interEquiv F hU g x).symm (π (fun i ↦ X.basicOpen (g i)) F.presheaf m x z) := rfl

/-- The degree `m` comparison map from the algebraic Čech complex of `g` to the Čech complex of
the covering, inverse to `toCechTerm`. -/
noncomputable def ofCechTerm (m : ℕ) :
    AddCommGrpCat.of (CechTerm Γ(F, U) g 1 m) ⟶
      ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).X m :=
  lift (fun i ↦ X.basicOpen (g i)) F.presheaf fun x ↦
    letI := moduleOfLE F (inter_le g x)
    AddCommGrpCat.ofHom ((interEquiv F hU g x).toLinearMap.toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun x ↦ AwayLoc Γ(F, U) (1 * tupleProd g x)) x))

/-- The component of `ofCechTerm` at a tuple. -/
theorem ofCechTerm_comp_π (m : ℕ) (x : Fin (m + 1) → Fin n) :
    letI := moduleOfLE F (inter_le g x)
    ofCechTerm F hU g m ≫ π (fun i ↦ X.basicOpen (g i)) F.presheaf m x =
      AddCommGrpCat.ofHom ((interEquiv F hU g x).toLinearMap.toAddMonoidHom.comp
        (Pi.evalAddMonoidHom (fun x ↦ AwayLoc Γ(F, U) (1 * tupleProd g x)) x)) :=
  lift_comp_π _ _ _ x

/-- The component of `ofCechTerm`, on elements. -/
theorem π_ofCechTerm (m : ℕ) (s : CechTerm Γ(F, U) g 1 m) (x : Fin (m + 1) → Fin n) :
    letI := moduleOfLE F (inter_le g x)
    π (fun i ↦ X.basicOpen (g i)) F.presheaf m x (ofCechTerm F hU g m s) =
      interEquiv F hU g x (s x) := by
  rw [← AddCommGrpCat.comp_apply, ofCechTerm_comp_π]
  rfl

/-- `toCechTerm` is a retraction of `ofCechTerm`. -/
theorem ofCechTerm_comp_toCechTerm (m : ℕ) :
    ofCechTerm F hU g m ≫ toCechTerm F hU g m = 𝟙 _ := by
  refine ConcreteCategory.hom_ext _ _ fun s ↦ funext fun x ↦ ?_
  let := moduleOfLE F (inter_le g x)
  rw [AddCommGrpCat.comp_apply, toCechTerm_apply, π_ofCechTerm, LinearEquiv.symm_apply_apply]
  rfl

/-- `ofCechTerm` is a retraction of `toCechTerm`. -/
theorem toCechTerm_comp_ofCechTerm (m : ℕ) :
    toCechTerm F hU g m ≫ ofCechTerm F hU g m = 𝟙 _ := by
  refine hom_ext (fun i ↦ X.basicOpen (g i)) F.presheaf fun x ↦ ?_
  let := moduleOfLE F (inter_le g x)
  rw [Category.assoc, ofCechTerm_comp_π, Category.id_comp]
  refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
  rw [AddCommGrpCat.comp_apply]
  change (interEquiv F hU g x) (toCechTerm F hU g m z x) = _
  rw [toCechTerm_apply, LinearEquiv.apply_symm_apply]

/-- **The degreewise comparison.** The degree `m` term of the Čech complex of the covering of `U`
by the basic opens `X.basicOpen (g i)` is the degree `m` term of the algebraic Čech complex of
`g` with coefficients in `Γ(F, U)`. -/
noncomputable def cechTermIso (m : ℕ) :
    ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).X m ≅
      AddCommGrpCat.of (CechTerm Γ(F, U) g 1 m) where
  hom := toCechTerm F hU g m
  inv := ofCechTerm F hU g m
  hom_inv_id := toCechTerm_comp_ofCechTerm F hU g m
  inv_hom_id := ofCechTerm_comp_toCechTerm F hU g m

/-- `ofCechTerm` followed by `toCechTerm`, on elements. -/
theorem ofCechTerm_toCechTerm (m : ℕ)
    (z : ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).X m) :
    ofCechTerm F hU g m (toCechTerm F hU g m z) = z := by
  exact ConcreteCategory.congr_hom (toCechTerm_comp_ofCechTerm F hU g m) z

/-- `toCechTerm` followed by `ofCechTerm`, on elements. -/
theorem toCechTerm_ofCechTerm (m : ℕ) (s : CechTerm Γ(F, U) g 1 m) :
    toCechTerm F hU g m (ofCechTerm F hU g m s) = s := by
  exact ConcreteCategory.congr_hom (ofCechTerm_comp_toCechTerm F hU g m) s

omit [F.IsQuasicoherent] hU in
/-- The component at a tuple `y` of the Čech differential, on elements: the alternating sum of the
restrictions along the faces of `y`. -/
theorem π_d_apply (m : ℕ)
    (z : ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).X m)
    (y : Fin (m + 2) → Fin n) :
    π (fun i ↦ X.basicOpen (g i)) F.presheaf (m + 1) y
        (((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).d m (m + 1) z) =
      ∑ j : Fin (m + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        F.presheaf.map (interMap (fun i ↦ X.basicOpen (g i)) y j.succAbove).op
          (π (fun i ↦ X.basicOpen (g i)) F.presheaf m (y ∘ j.succAbove) z) := by
  have h := ConcreteCategory.congr_hom
    (d_comp_π (fun i ↦ X.basicOpen (g i)) F.presheaf m y) z
  rw [AddCommGrpCat.comp_apply, sum_hom_apply] at h
  simpa only [zsmul_hom_apply, AddCommGrpCat.comp_apply] using h

/-- **The differentials agree.** The degreewise comparison `toCechTerm` carries the Čech
differential of the covering to the algebraic Čech differential `cechD`. Both are alternating
sums of restriction maps, and the summands agree by `resAway_eq_interEquiv`. -/
theorem d_comp_toCechTerm (m : ℕ) :
    ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).d m (m + 1) ≫
        toCechTerm F hU g (m + 1) =
      toCechTerm F hU g m ≫
        AddCommGrpCat.ofHom (cechD Γ(F, U) g 1 m).toAddMonoidHom := by
  refine ConcreteCategory.hom_ext _ _ fun z ↦ funext fun y ↦ ?_
  let := moduleOfLE F (inter_le g y)
  have hsmul : ∀ (k : ℕ) (v : AwayLoc Γ(F, U) (1 * tupleProd g y)),
      ((-1 : ℤ) ^ k) • v = ((-1 : Γ(X, U)) ^ k) • v := fun k v ↦ by
    rw [← Int.cast_smul_eq_zsmul Γ(X, U) ((-1 : ℤ) ^ k) v]
    norm_num
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply]
  change (interEquiv F hU g y).symm
      (π (fun i ↦ X.basicOpen (g i)) F.presheaf (m + 1) y _) =
    cechD Γ(F, U) g 1 m (toCechTerm F hU g m z) y
  rw [π_d_apply, map_sum, cechD_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, hsmul]
  refine congrArg (fun w ↦ ((-1 : Γ(X, U)) ^ (j : ℕ)) • w) ?_
  rw [LinearMap.congr_fun (resAway_eq_interEquiv F hU g y j)
    (toCechTerm F hU g m z fun i ↦ y (j.succAbove i))]
  change _ = (interEquiv F hU g y).symm _
  refine congrArg (interEquiv F hU g y).symm ?_
  change F.presheaf.map _ _ = F.presheaf.map _ ((interEquiv F hU g fun i ↦ y (j.succAbove i)) _)
  rw [toCechTerm_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The degreewise comparison carries the Čech differential to `cechD`, on elements. -/
theorem toCechTerm_d (m : ℕ)
    (z : ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).X m) :
    toCechTerm F hU g (m + 1)
        (((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).d m (m + 1) z) =
      cechD Γ(F, U) g 1 m (toCechTerm F hU g m z) := by
  rw [← AddCommGrpCat.comp_apply, d_comp_toCechTerm, AddCommGrpCat.comp_apply]
  rfl

include hU in
/-- **Exactness of the Čech complex in positive degrees.** If the family `g` generates the unit
ideal of `Γ(X, U)`, then the Čech complex of a quasi-coherent module `F` with respect to the
covering of the affine open `U` by the basic opens `X.basicOpen (g i)` is exact in every
positive degree. -/
@[ega "III 1.2.4" "special case"]
theorem exactAt_cechComplex (hg : Ideal.span (Set.range g) = ⊤) (p : ℕ) :
    ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro s hs
  obtain ⟨s, rfl⟩ :
      ∃ t : ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).X (p + 1), t = s :=
    ⟨s, rfl⟩
  have hs' : ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).d (p + 1) (p + 2) s
      = 0 := hs
  have h0 : cechD Γ(F, U) g 1 (p + 1) (toCechTerm F hU g (p + 1) s) = 0 := by
    rw [← toCechTerm_d, hs', map_zero]
  obtain ⟨u, hu⟩ := cech_exact g hg 1 p (toCechTerm F hU g (p + 1) s) h0
  refine ⟨ofCechTerm F hU g p u, ?_⟩
  change ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).d p (p + 1)
    (ofCechTerm F hU g p u) = s
  rw [← ofCechTerm_toCechTerm F hU g (p + 1)
    (((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj F.presheaf).d p (p + 1)
      (ofCechTerm F hU g p u)), toCechTerm_d, toCechTerm_ofCechTerm, hu,
    ofCechTerm_toCechTerm]

end Comparison

/-- **Positive-degree Čech cohomology of a quasi-coherent module vanishes on a finite standard
open cover of an affine open.** Here `F` is a quasi-coherent module on the ambient scheme `X`,
the affine open `U` is covered by the ambient basic opens `X.basicOpen (g i)` attached to a
finite family `g` of sections over `U` whose basic opens cover `Spec Γ(X, U)`, and Čech
cohomology is the homology of Mathlib's `cechComplexFunctor` applied to the underlying abelian
sheaf of `F`. -/
@[stacks 01X9]
theorem isZero_cechCohomology_of_isStandardOpenCover
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) {n : ℕ} (g : Fin n → Γ(X, U))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj).homology p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  exact (exactAt_cechComplex F hU g
    (span_range_eq_top_of_isStandardOpenCoverOfSpectrum hg) q).isZero_homology

end Stacks.Cohomology.Cech

end
