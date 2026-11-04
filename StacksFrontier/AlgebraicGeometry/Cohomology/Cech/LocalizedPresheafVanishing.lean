module

public import StacksFrontier.AlgebraicGeometry.AffineChartLocalization.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverVanishing

/-!
# Čech complexes whose terms are localizations of one module

Let `V : Fin n → C` be a finite family in a category with finite products, `P` an abelian presheaf
on `C`, `M` a module over a commutative ring `R` and `g : Fin n → R` a family generating the unit
ideal.  If the sections of `P` over the intersections `inter V x` are identified with the
localizations `M_{g(x 0) ⋯ g(x m)}`, compatibly with the restriction maps along the faces, then
the Čech complex of `P` on `V` is exact in positive degrees: it is the algebraic Čech complex of
`g` with coefficients in `M`, which is exact by `Stacks.RingTheory.CechAcyclicity.cech_exact`.
This is `exactAt_cechComplex_of_addEquiv`.

The geometric instance is `exactAt_cechComplex_of_isLocalizedModule`: on a scheme `X`, a
presheaf of `𝒪_X`-modules `Q` which localizes on the basic opens of an open `U` (the hypothesis
of `Stacks.AlgebraicGeometry.AffineChartLocalization.bijective_toSheafify_app_of_isAffineOpen`),
and an abelian presheaf `P`, in any larger universe, receiving a map from `Q` which is bijective
on the basic opens of `U`.  Then the Čech complex of `P` on the cover of `U` by the basic opens
of a family generating the unit ideal of `Γ(X, U)` is exact in positive degrees.  For `Q` a
quasi-coherent module and `P = Q` this is
`Stacks.Cohomology.Cech.exactAt_cechComplex`, of which this file is the generalization: neither
the sheaf condition nor the universe of `P` plays a role.

## Main results

* `exactAt_cechComplex_of_addEquiv` — the abstract statement.
* `exactAt_cechComplex_of_isLocalizedModule` — the statement for a presheaf receiving a map from
  a presheaf of modules which localizes on basic opens.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.CategoryTheory.CechComplex Stacks.RingTheory.CechAcyclicity

universe w u v u' v'

noncomputable section

namespace Stacks.Cohomology.Cech

/-! ### The abstract statement -/

section Abstract

variable {C : Type u'} [Category.{v'} C] [HasFiniteProducts C] {n : ℕ} (V : Fin n → C)
  (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
  [Module R M] (g : Fin n → R)
  (e : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
    AwayLoc M (1 * tupleProd g x) ≃+ P.obj (op (inter V x)))

/-- The component at a tuple `y` of the Čech differential of an abelian presheaf, on elements:
the alternating sum of the restrictions along the faces of `y`. -/
theorem π_d_apply_presheaf (m : ℕ) (z : ((cechComplexFunctor V).obj P).X m)
    (y : Fin (m + 2) → Fin n) :
    π V P (m + 1) y (((cechComplexFunctor V).obj P).d m (m + 1) z) =
      ∑ j : Fin (m + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        P.map (interMap V y j.succAbove).op (π V P m (y ∘ j.succAbove) z) := by
  have h := ConcreteCategory.congr_hom (d_comp_π V P m y) z
  rw [AddCommGrpCat.comp_apply, sum_hom_apply] at h
  simpa only [zsmul_hom_apply, AddCommGrpCat.comp_apply] using h

/-- The degree `m` comparison from the Čech complex of `P` to the algebraic Čech complex of `g`:
its component at a tuple `x` is the projection to `P(inter V x)` followed by `(e x).symm`. -/
def toCechTermOfEquiv (m : ℕ) : ((cechComplexFunctor V).obj P).X m →+ CechTerm M g 1 m :=
  AddMonoidHom.pi fun x ↦ (e x).symm.toAddMonoidHom.comp (ConcreteCategory.hom (π V P m x))

/-- The component of `toCechTermOfEquiv` at a tuple. -/
theorem toCechTermOfEquiv_apply (m : ℕ) (z : ((cechComplexFunctor V).obj P).X m)
    (x : Fin (m + 1) → Fin n) :
    toCechTermOfEquiv V P g e m z x = (e x).symm (π V P m x z) := rfl

/-- The degree `m` comparison from the algebraic Čech complex of `g` to the Čech complex of `P`,
inverse to `toCechTermOfEquiv`: the element of the product with components `e x (s x)`. -/
def ofCechTermOfEquiv (m : ℕ) (s : CechTerm M g 1 m) : ((cechComplexFunctor V).obj P).X m :=
  (Concrete.productEquiv fun x : Fin (m + 1) → Fin n ↦ P.obj (op (inter V x))).symm
    fun x ↦ e x (s x)

/-- The component of `ofCechTermOfEquiv` at a tuple, on elements. -/
theorem π_ofCechTermOfEquiv (m : ℕ) (s : CechTerm M g 1 m) (x : Fin (m + 1) → Fin n) :
    π V P m x (ofCechTermOfEquiv V P g e m s) = e x (s x) :=
  Concrete.productEquiv_symm_apply_π _ _ x

/-- `toCechTermOfEquiv` is a left inverse of `ofCechTermOfEquiv`. -/
theorem toCechTermOfEquiv_ofCechTermOfEquiv (m : ℕ) (s : CechTerm M g 1 m) :
    toCechTermOfEquiv V P g e m (ofCechTermOfEquiv V P g e m s) = s :=
  funext fun x ↦ by
    rw [toCechTermOfEquiv_apply, π_ofCechTermOfEquiv, AddEquiv.symm_apply_apply]

/-- `ofCechTermOfEquiv` is a left inverse of `toCechTermOfEquiv`. -/
theorem ofCechTermOfEquiv_toCechTermOfEquiv (m : ℕ) (z : ((cechComplexFunctor V).obj P).X m) :
    ofCechTermOfEquiv V P g e m (toCechTermOfEquiv V P g e m z) = z := by
  refine (Equiv.symm_apply_eq _).2 (funext fun x ↦ ?_)
  exact ((e x).apply_symm_apply _).trans (Concrete.productEquiv_apply_apply _ _ _).symm

variable (he : ∀ {m : ℕ} (y : Fin (m + 2) → Fin n) (j : Fin (m + 2))
    (z : AwayLoc M (1 * tupleProd g fun i ↦ y (j.succAbove i))),
    P.map (interMap V y j.succAbove).op (e (fun i ↦ y (j.succAbove i)) z) =
      e y (resAway M (dvd_face g 1 y j) z))

include he in
/-- **The differentials agree**: `toCechTermOfEquiv` carries the Čech differential of `P` to the
algebraic Čech differential `cechD`. -/
theorem toCechTermOfEquiv_d (m : ℕ) (z : ((cechComplexFunctor V).obj P).X m) :
    toCechTermOfEquiv V P g e (m + 1) (((cechComplexFunctor V).obj P).d m (m + 1) z) =
      cechD M g 1 m (toCechTermOfEquiv V P g e m z) := by
  funext y
  have hsmul : ∀ (k : ℕ) (v : AwayLoc M (1 * tupleProd g y)),
      ((-1 : ℤ) ^ k) • v = ((-1 : R) ^ k) • v := fun k v ↦ by
    rw [← Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ k) v]
    norm_num
  rw [toCechTermOfEquiv_apply, π_d_apply_presheaf, map_sum, cechD_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, hsmul]
  refine congrArg (fun w ↦ ((-1 : R) ^ (j : ℕ)) • w) ?_
  rw [AddEquiv.symm_apply_eq, toCechTermOfEquiv_apply, ← he]
  exact congrArg _ ((e fun i ↦ y (j.succAbove i)).apply_symm_apply _).symm

include he in
/-- **Exactness of a Čech complex whose terms are localizations of one module.**  If the
sections of `P` over the intersections `inter V x` are the localizations of `M` away from
`g(x 0) ⋯ g(x m)`, compatibly with the face maps, and `g` generates the unit ideal, then the Čech
complex of `P` on `V` is exact in every positive degree. -/
theorem exactAt_cechComplex_of_addEquiv (hg : Ideal.span (Set.range g) = ⊤) (p : ℕ) :
    ((cechComplexFunctor V).obj P).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro s hs
  obtain ⟨s, rfl⟩ : ∃ t : ((cechComplexFunctor V).obj P).X (p + 1), t = s := ⟨s, rfl⟩
  have hs' : ((cechComplexFunctor V).obj P).d (p + 1) (p + 2) s = 0 := hs
  have h0 : cechD M g 1 (p + 1) (toCechTermOfEquiv V P g e (p + 1) s) = 0 := by
    rw [← toCechTermOfEquiv_d V P g e he, hs', map_zero]
  obtain ⟨t, ht⟩ := cech_exact g hg 1 p (toCechTermOfEquiv V P g e (p + 1) s) h0
  refine ⟨ofCechTermOfEquiv V P g e p t, ?_⟩
  show ((cechComplexFunctor V).obj P).d p (p + 1) (ofCechTermOfEquiv V P g e p t) = s
  rw [← ofCechTermOfEquiv_toCechTermOfEquiv V P g e (p + 1)
    (((cechComplexFunctor V).obj P).d p (p + 1) (ofCechTermOfEquiv V P g e p t)),
    toCechTermOfEquiv_d V P g e he, toCechTermOfEquiv_ofCechTermOfEquiv, ht,
    ofCechTermOfEquiv_toCechTermOfEquiv]

end Abstract

/-! ### Presheaves receiving a map from a presheaf of modules which localizes on basic opens -/

section Presheaf

open Stacks.AlgebraicGeometry.AffineChartLocalization

attribute [local instance] Stacks.AlgebraicGeometry.AffineChartLocalization.sectionsModule

variable {X : Scheme.{u}} (Q : PresheafOfModules.{u} X.ringCatSheaf.obj) {U : X.Opens} {n : ℕ}
  (g : Fin n → Γ(X, U))

/-- Restriction of sections of a presheaf of `𝒪_X`-modules between two opens contained in `U`,
as a `Γ(X, U)`-linear map for the module structures obtained by restricting scalars from `U`. -/
def presheafRestrictLE {W₁ W₂ : X.Opens} (h : W₁ ≤ W₂) (h₂ : W₂ ≤ U) :
    letI := presheafModuleOfLE Q (h.trans h₂)
    letI := presheafModuleOfLE Q h₂
    ↥(Q.obj (op W₂)) →ₗ[Γ(X, U)] ↥(Q.obj (op W₁)) :=
  letI := presheafModuleOfLE Q (h.trans h₂)
  letI := presheafModuleOfLE Q h₂
  { toFun := Q.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r z ↦ by
      refine (Q.map_smul (homOfLE h).op (X.presheaf.map (homOfLE h₂).op r) z).trans ?_
      congr 1
      change (X.presheaf.map (homOfLE h₂).op ≫ X.presheaf.map (homOfLE h).op) r = _
      rw [← Functor.map_comp]
      rfl }

variable (hQ : ∀ (t : Γ(X, U)) {W : X.Opens} (_ : W = X.basicOpen t) (hWU : W ≤ U),
    letI := presheafModuleOfLE Q hWU
    IsLocalizedModule.Away t (presheafRestrictₗ Q hWU))

/-- The sections of `Q` over the intersection selected by a tuple `x` are the localization of
`Q(U)` away from `1 * tupleProd g x`. -/
def presheafInterEquiv {m : ℕ} (x : Fin (m + 1) → Fin n) :
    letI := presheafModuleOfLE Q (inter_le g x)
    AwayLoc ↥(Q.obj (op U)) (1 * tupleProd g x) ≃ₗ[Γ(X, U)]
      ↥(Q.obj (op (inter (fun i ↦ X.basicOpen (g i)) x))) :=
  letI := presheafModuleOfLE Q (inter_le g x)
  letI := hQ (1 * tupleProd g x) (inter_eq_basicOpen g x) (inter_le g x)
  IsLocalizedModule.iso _ (presheafRestrictₗ Q (inter_le g x))

/-- `presheafInterEquiv` sends a fraction with denominator `1` to the restriction of its
numerator. -/
theorem presheafInterEquiv_mk_one {m : ℕ} (x : Fin (m + 1) → Fin n) (z : ↥(Q.obj (op U))) :
    presheafInterEquiv Q g hQ x (LocalizedModule.mk z 1) = Q.map (homOfLE (inter_le g x)).op z :=
  let := presheafModuleOfLE Q (inter_le g x)
  let := hQ (1 * tupleProd g x) (inter_eq_basicOpen g x) (inter_le g x)
  IsLocalizedModule.iso_mk_one _ (presheafRestrictₗ Q (inter_le g x)) z

/-- The inverse of `presheafInterEquiv` sends the restriction of a section over `U` to the fraction
with denominator `1`. -/
theorem presheafInterEquiv_symm_apply {m : ℕ} (x : Fin (m + 1) → Fin n) (z : ↥(Q.obj (op U))) :
    letI := presheafModuleOfLE Q (inter_le g x)
    (presheafInterEquiv Q g hQ x).symm (Q.map (homOfLE (inter_le g x)).op z) =
      LocalizedModule.mk z 1 :=
  (presheafInterEquiv Q g hQ x).symm_apply_eq.2 (presheafInterEquiv_mk_one Q g hQ x z).symm

/-- **The face maps agree**: under `presheafInterEquiv`, the restriction of `Q` along the `j`-th
face of a tuple is the restriction map `resAway` between localizations of `Q(U)`. -/
theorem resAway_eq_presheafInterEquiv {m : ℕ} (y : Fin (m + 2) → Fin n) (j : Fin (m + 2)) :
    letI : Module Γ(X, U) ↥(Q.obj (op (inter (fun i ↦ X.basicOpen (g i)) y))) :=
      presheafModuleOfLE Q (inter_le g y)
    letI := presheafModuleOfLE Q (inter_le g fun i ↦ y (j.succAbove i))
    resAway ↥(Q.obj (op U)) (dvd_face g 1 y j) =
      (presheafInterEquiv Q g hQ y).symm.toLinearMap ∘ₗ
        (presheafRestrictLE Q (inter_le_inter g y j) (inter_le g fun i ↦ y (j.succAbove i))) ∘ₗ
          (presheafInterEquiv Q g hQ fun i ↦ y (j.succAbove i)).toLinearMap := by
  let := presheafModuleOfLE Q (inter_le g y)
  let := presheafModuleOfLE Q (inter_le g fun i ↦ y (j.succAbove i))
  refine LocalizedModule.lift_unique _ _ (isUnit_powers_awayLoc (dvd_face g 1 y j)) _ ?_
  refine LinearMap.ext fun z ↦ ?_
  show (presheafInterEquiv Q g hQ y).symm (Q.map (homOfLE (inter_le_inter g y j)).op
      (presheafInterEquiv Q g hQ (fun i ↦ y (j.succAbove i)) (LocalizedModule.mk z 1))) =
    LocalizedModule.mk z 1
  have h2 : Q.map (homOfLE (inter_le_inter g y j)).op
      (Q.map (homOfLE (inter_le g fun i ↦ y (j.succAbove i))).op z) =
        Q.map (homOfLE (inter_le g y)).op z := by
    show Q.presheaf.map _ (Q.presheaf.map _ z) = Q.presheaf.map _ z
    exact (congrArg (fun f : Q.presheaf.obj (op U) ⟶ _ ↦ f z)
      (Q.presheaf.map_comp (homOfLE (inter_le g fun i ↦ y (j.succAbove i))).op
        (homOfLE (inter_le_inter g y j)).op)).symm
  rw [presheafInterEquiv_mk_one, h2, presheafInterEquiv_symm_apply]

/-- `resAway_eq_presheafInterEquiv` on elements, in the form `exactAt_cechComplex_of_addEquiv`
asks for. -/
theorem presheafInterEquiv_resAway {m : ℕ} (y : Fin (m + 2) → Fin n) (j : Fin (m + 2))
    (z : AwayLoc ↥(Q.obj (op U)) (1 * tupleProd g fun i ↦ y (j.succAbove i))) :
    Q.map (homOfLE (inter_le_inter g y j)).op
        (presheafInterEquiv Q g hQ (fun i ↦ y (j.succAbove i)) z) =
      presheafInterEquiv Q g hQ y (resAway _ (dvd_face g 1 y j) z) := by
  let := presheafModuleOfLE Q (inter_le g y)
  let := presheafModuleOfLE Q (inter_le g fun i ↦ y (j.succAbove i))
  rw [LinearMap.congr_fun (resAway_eq_presheafInterEquiv Q g hQ y j) z]
  exact ((presheafInterEquiv Q g hQ y).apply_symm_apply _).symm

variable {Q g}

include hQ in
/-- **Exactness of the Čech complex of a presheaf receiving a map from a presheaf of modules which
localizes on basic opens.**  Let `Q` be a presheaf of `𝒪_X`-modules whose restriction maps
`Q(U) → Q(D(t))` are localizations away from `t`, for the basic opens `D(t) ⊆ U`, and let
`φ : Q ⟶ P` be a map to an abelian presheaf in a larger universe which is bijective on those basic
opens.  If `g` generates the unit ideal of `Γ(X, U)`, the Čech complex of `P` on the cover of `U`
by the basic opens of `g` is exact in every positive degree. -/
theorem exactAt_cechComplex_of_isLocalizedModule {P : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{max u w}}
    (φ : Q.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w, u} ⟶ P)
    (hφ : ∀ (t : Γ(X, U)) {W : X.Opens}, W = X.basicOpen t → W ≤ U →
      Function.Bijective (φ.app (op W)))
    (hg : Ideal.span (Set.range g) = ⊤) (p : ℕ) :
    ((cechComplexFunctor fun i ↦ X.basicOpen (g i)).obj P).ExactAt (p + 1) := by
  let e : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      AwayLoc ↥(Q.obj (op U)) (1 * tupleProd g x) ≃+
        P.obj (op (inter (fun i ↦ X.basicOpen (g i)) x)) := fun x ↦
    let := presheafModuleOfLE Q (inter_le g x)
    ((presheafInterEquiv Q g hQ x).toAddEquiv.trans AddEquiv.ulift.symm).trans
      (AddEquiv.ofBijective (φ.app (op (inter (fun i ↦ X.basicOpen (g i)) x))).hom
        (hφ _ (inter_eq_basicOpen g x) (inter_le g x)))
  refine exactAt_cechComplex_of_addEquiv _ P g e (fun y j z ↦ ?_) hg p
  have hnat := NatTrans.naturality_apply φ
    (interMap (fun i ↦ X.basicOpen (g i)) y j.succAbove).op
    (ULift.up (presheafInterEquiv Q g hQ (fun i ↦ y (j.succAbove i)) z))
  refine hnat.symm.trans ?_
  show φ.app _ (ULift.up (Q.map (homOfLE (inter_le_inter g y j)).op
    (presheafInterEquiv Q g hQ (fun i ↦ y (j.succAbove i)) z))) = _
  rw [presheafInterEquiv_resAway]
  rfl

end Presheaf

end Stacks.Cohomology.Cech

end
