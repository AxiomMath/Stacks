module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogResidue
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic
public import StacksFrontier.Topology.Sheaves.Sheaf.Abelian
public import StacksCore.Tactic.StacksAttribute

/-!
# The residue sequence of the de Rham complex of log poles

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor for which the
de Rham complex of log poles is defined ([Stacks, Tag 0FMV]). This file assembles
[Stacks, Tag 0FMW]: the canonical short exact sequence of complexes

`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → i_*Ω^•_{Y/S}[-1] → 0`.

* `AlgebraicGeometry.Scheme.Hom.logDeRhamComplex`: the complex `Ω^•_{X/S}(log Y)`, with the
  differential of `StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogDifferential`.
* `AlgebraicGeometry.Scheme.Hom.divisorShiftComplex`: the complex `i_*Ω^•_{Y/S}[-1]`, which is
  `0` in degree `0` and `i_*Ω^{p}_{Y/S}` in degree `p + 1`, with differential `-d`.
* `AlgebraicGeometry.Scheme.Hom.logInclusionMap` and `AlgebraicGeometry.Scheme.Hom.logResidueMap`:
  the inclusion of forms with no pole and the residue, as maps of complexes. In every degree they
  are morphisms of `𝒪_X`-modules (`AlgebraicGeometry.Scheme.Hom.logPolesFormsInclusion` and
  `AlgebraicGeometry.Scheme.Hom.logResHom`).
* `AlgebraicGeometry.Scheme.Hom.logResidueShortComplex_shortExact`: **[Stacks, Tag 0FMW]**, the
  residue sequence is short exact.

## Implementation notes

The de Rham differentials are only `f⁻¹𝒪_S`-linear, so, as in
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapDeRham`, the complexes are complexes of
sheaves of abelian groups on `X`, through the exact faithful forgetful functor
`Stacks.Perfect.AbelianFraction.abelianSheaf`; the first is the abelian reading
`AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex` of the relative de Rham complex. The
complexes are indexed by `ℕ`, and the shift `[-1]` is written out: the degree-`(p + 1)` term of
`i_*Ω^•_{Y/S}[-1]` is `i_*Ω^p_{Y/S}` and its differential is `-d`, the sign of the shift.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject
open Stacks.Perfect.AbelianFraction

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- Two morphisms of sheaves of abelian groups agreeing on all sections are equal. -/
private theorem sheaf_hom_ext {F G : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}}
    {a b : F ⟶ G} (h : ∀ (W : (X.Opens)ᵒᵖ) (s : F.obj.obj W), a.hom.app W s = b.hom.app W s) :
    a = b :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W =>
    AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => h W s)))

include hI hlog

/-! ### The complex of forms with logarithmic poles -/

/-- The differential of forms with logarithmic poles commutes with restriction. -/
theorem presheaf_map_logD {p : ℕ} {W W' : X.Opens} (h : W' ≤ W) (φ : Γ(logPolesForms f I p, W)) :
    (Scheme.Modules.presheaf (logPolesForms f I (p + 1))).map (homOfLE h).op (logD hI hlog φ) =
      logD hI hlog ((Scheme.Modules.presheaf (logPolesForms f I p)).map (homOfLE h).op φ) :=
  (logD_res hI hlog h φ).symm

/-- The residue commutes with restriction. -/
theorem presheaf_map_logRes {p : ℕ} {W W' : X.Opens} (h : W' ≤ W)
    (φ : Γ(logPolesForms f I (p + 1), W)) :
    (Scheme.Modules.presheaf (divisorForms f I p)).map (homOfLE h).op (logRes hI hlog φ) =
      logRes hI hlog ((Scheme.Modules.presheaf (logPolesForms f I (p + 1))).map (homOfLE h).op φ) :=
  (logRes_res hI hlog h φ).symm

/-- The differential on sections over `W`, as an additive map. -/
def logDAddHom (p : ℕ) (W : X.Opens) :
    Γ(logPolesForms f I p, W) →+ Γ(logPolesForms f I (p + 1), W) :=
  AddMonoidHom.mk' (logD hI hlog) (logD_add hI hlog)

/-- `logDAddHom` evaluates to the differential `logD`. -/
theorem logDAddHom_apply (p : ℕ) (W : X.Opens) (φ : Γ(logPolesForms f I p, W)) :
    logDAddHom f I hI hlog p W φ = logD hI hlog φ :=
  rfl

/-- `logDAddHom` commutes with the restriction maps of the presheaves. -/
theorem logDAddHom_naturality (p : ℕ) {W W' : (X.Opens)ᵒᵖ} (g : W ⟶ W')
    (φ : Γ(logPolesForms f I p, W.unop)) :
    logDAddHom f I hI hlog p W'.unop ((Scheme.Modules.presheaf (logPolesForms f I p)).map g φ) =
      (Scheme.Modules.presheaf (logPolesForms f I (p + 1))).map g
        (logDAddHom f I hI hlog p W.unop φ) := by
  rw [show g = (homOfLE (leOfHom g.unop)).op from rfl, logDAddHom_apply, logDAddHom_apply]
  exact (presheaf_map_logD f I hI hlog (W := W.unop) (W' := W'.unop) (leOfHom g.unop) φ).symm

/-- The differential of forms with logarithmic poles, as a morphism of the underlying abelian
presheaves. -/
def logDPresheafHom (p : ℕ) :
    Scheme.Modules.presheaf (logPolesForms f I p) ⟶
      Scheme.Modules.presheaf (logPolesForms f I (p + 1)) where
  app W := AddCommGrpCat.ofHom (logDAddHom f I hI hlog p W.unop)
  naturality _ _ g := AddCommGrpCat.hom_ext
    (AddMonoidHom.ext fun φ => logDAddHom_naturality f I hI hlog p g φ)

/-- **The differential of forms with logarithmic poles**, as a morphism of abelian sheaves. -/
def logDAbHom (p : ℕ) :
    (abelianSheaf X).obj (logPolesForms f I p) ⟶ (abelianSheaf X).obj (logPolesForms f I (p + 1)) :=
  abHom (logDPresheafHom f I hI hlog p)

/-- On sections over `W`, `logDAbHom` is the differential `logD`. -/
theorem logDAbHom_app (p : ℕ) (W : X.Opens) (φ : (logPolesForms f I p).val.obj (op W)) :
    (logDAbHom f I hI hlog p).hom.app (op W) φ = logD hI hlog φ :=
  rfl

/-- `d ∘ d = 0` for the differential of forms with logarithmic poles. -/
theorem logDAbHom_comp_logDAbHom (p : ℕ) :
    logDAbHom f I hI hlog p ≫ logDAbHom f I hI hlog (p + 1) = 0 := by
  refine sheaf_hom_ext fun W φ => ?_
  exact logD_logD hI hlog φ

/-- **The de Rham complex of log poles** `Ω^•_{X/S}(log Y)`, as a complex of sheaves of abelian
groups on `X`. -/
def logDeRhamComplex :
    CochainComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (fun p => (abelianSheaf X).obj (logPolesForms f I p))
    (logDAbHom f I hI hlog) (logDAbHom_comp_logDAbHom f I hI hlog)

/-! ### The residue as a morphism of `𝒪_X`-modules -/

/-- The residue on sections over `W`, as an additive map. -/
def logResAddHom (p : ℕ) (W : X.Opens) :
    Γ(logPolesForms f I (p + 1), W) →+ Γ(divisorForms f I p, W) :=
  AddMonoidHom.mk' (logRes hI hlog) (logRes_add hI hlog)

/-- `logResAddHom` evaluates to the residue `logRes`. -/
theorem logResAddHom_apply (p : ℕ) (W : X.Opens) (φ : Γ(logPolesForms f I (p + 1), W)) :
    logResAddHom f I hI hlog p W φ = logRes hI hlog φ :=
  rfl

/-- `logResAddHom` commutes with the restriction maps of the presheaves. -/
theorem logResAddHom_naturality (p : ℕ) {W W' : (X.Opens)ᵒᵖ} (g : W ⟶ W')
    (φ : Γ(logPolesForms f I (p + 1), W.unop)) :
    logResAddHom f I hI hlog p W'.unop
        ((Scheme.Modules.presheaf (logPolesForms f I (p + 1))).map g φ) =
      (Scheme.Modules.presheaf (divisorForms f I p)).map g
        (logResAddHom f I hI hlog p W.unop φ) := by
  rw [show g = (homOfLE (leOfHom g.unop)).op from rfl, logResAddHom_apply, logResAddHom_apply]
  exact (presheaf_map_logRes f I hI hlog (W := W.unop) (W' := W'.unop) (leOfHom g.unop) φ).symm

/-- The residue, as a morphism of the underlying abelian presheaves. -/
def logResPresheafHom (p : ℕ) :
    Scheme.Modules.presheaf (logPolesForms f I (p + 1)) ⟶
      Scheme.Modules.presheaf (divisorForms f I p) where
  app W := AddCommGrpCat.ofHom (logResAddHom f I hI hlog p W.unop)
  naturality _ _ g := AddCommGrpCat.hom_ext
    (AddMonoidHom.ext fun φ => logResAddHom_naturality f I hI hlog p g φ)

/-- **The residue** `Ω^{p+1}_{X/S}(log Y) ⟶ i_*Ω^p_{Y/S}`, a morphism of `𝒪_X`-modules. -/
def logResHom (p : ℕ) : logPolesForms f I (p + 1) ⟶ divisorForms f I p :=
  ⟨PresheafOfModules.homMk (logResPresheafHom f I hI hlog p) fun W r φ =>
    logRes_smul hI hlog (W := W.unop) r φ⟩

/-- On sections over `W`, `logResHom` is the residue `logRes`. -/
theorem logResHom_app (p : ℕ) (W : X.Opens) (φ : (logPolesForms f I (p + 1)).val.obj (op W)) :
    (logResHom f I hI hlog p).val.app (op W) φ = logRes hI hlog φ :=
  rfl

omit hI hlog

/-! ### The shifted de Rham complex of the divisor -/

/-- `d ∘ d = 0` for the de Rham differential of the divisor, pushed forward to `X`. -/
theorem pushforwardDeRhamDifferentialAbHom_comp (p : ℕ) :
    pushforwardDeRhamDifferentialAbHom I.subschemeι f p ≫
      pushforwardDeRhamDifferentialAbHom I.subschemeι f (p + 1) = 0 := by
  refine sheaf_hom_ext fun W ω => ?_
  exact deRhamD_deRhamD (f := I.subschemeι ≫ f) p (I.subschemeι ⁻¹ᵁ W.unop) ω

/-- The terms of `i_*Ω^•_{Y/S}[-1]`: `0` in degree `0`, `i_*Ω^p_{Y/S}` in degree `p + 1`. -/
def divisorShiftX : ℕ → Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}
  | 0 => 0
  | p + 1 => (abelianSheaf X).obj (divisorForms f I p)

/-- The differential of `i_*Ω^•_{Y/S}[-1]`: `-d`, the sign of the shift. -/
def divisorShiftD : ∀ n : ℕ, divisorShiftX f I n ⟶ divisorShiftX f I (n + 1)
  | 0 => 0
  | p + 1 => -pushforwardDeRhamDifferentialAbHom I.subschemeι f p

/-- `d ∘ d = 0` for the differential of `i_*Ω^•_{Y/S}[-1]`. -/
theorem divisorShiftD_comp (n : ℕ) : divisorShiftD f I n ≫ divisorShiftD f I (n + 1) = 0 := by
  cases n with
  | zero => exact zero_comp
  | succ p =>
    show (-pushforwardDeRhamDifferentialAbHom I.subschemeι f p) ≫
      (-pushforwardDeRhamDifferentialAbHom I.subschemeι f (p + 1)) = 0
    rw [Preadditive.neg_comp_neg]
    exact pushforwardDeRhamDifferentialAbHom_comp f I p

/-- **The complex `i_*Ω^•_{Y/S}[-1]`** of sheaves of abelian groups on `X`: the de Rham complex
of the divisor, pushed forward to `X` and shifted by one, with the differential negated. -/
def divisorShiftComplex :
    CochainComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (divisorShiftX f I) (divisorShiftD f I) (divisorShiftD_comp f I)

include hI hlog

/-! ### The inclusion and the residue as maps of complexes -/

/-- The relative de Rham complex `Ω^•_{X/S}`, read in sheaves of abelian groups on `X`. -/
abbrev deRhamAbComplex :
    CochainComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ℕ :=
  AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (deRhamAlgebras f)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras f))

omit hI hlog in
/-- The differential of `deRhamAbComplex f` from degree `p` to `p + 1` is the de Rham differential.
-/
theorem deRhamAbComplex_d (p : ℕ) :
    (deRhamAbComplex f).d p (p + 1) = deRhamDifferentialAbHom f p :=
  rfl

/-- The differential of `logDeRhamComplex` from degree `p` to `p + 1` is `logDAbHom`. -/
theorem logDeRhamComplex_d (p : ℕ) :
    (logDeRhamComplex f I hI hlog).d p (p + 1) = logDAbHom f I hI hlog p := by
  unfold logDeRhamComplex
  exact CochainComplex.of_d (fun p => (abelianSheaf X).obj (logPolesForms f I p))
    (logDAbHom f I hI hlog) p

omit hI hlog in
/-- The differential of `divisorShiftComplex` from degree `n` to `n + 1` is `divisorShiftD`. -/
theorem divisorShiftComplex_d (n : ℕ) :
    (divisorShiftComplex f I).d n (n + 1) = divisorShiftD f I n := by
  unfold divisorShiftComplex
  exact CochainComplex.of_d (divisorShiftX f I) (divisorShiftD f I) n

/-- **The inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)`** of forms with no pole, as a map of
complexes; in degree `p` it is the morphism of `𝒪_X`-modules
`AlgebraicGeometry.Scheme.Hom.logPolesFormsInclusion`. -/
def logInclusionMap : deRhamAbComplex f ⟶ logDeRhamComplex f I hI hlog where
  f p := (abelianSheaf X).map (logPolesFormsInclusion f I p)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [deRhamAbComplex_d, logDeRhamComplex_d]
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W =>
      AddCommGrpCat.hom_ext (AddMonoidHom.ext fun ω => ?_)))
    exact logD_logPolesFormsInclusion hI hlog (W := W.unop) ω

/-- The residue in each degree: `0` in degree `0`, `AlgebraicGeometry.Scheme.Hom.logResHom` in
degree `p + 1`. -/
def logResidueF : ∀ n : ℕ, (abelianSheaf X).obj (logPolesForms f I n) ⟶ divisorShiftX f I n
  | 0 => 0
  | p + 1 => (abelianSheaf X).map (logResHom f I hI hlog p)

/-- The residue in each degree commutes with the differentials. -/
theorem logResidueF_comm (n : ℕ) :
    logResidueF f I hI hlog n ≫ divisorShiftD f I n =
      logDAbHom f I hI hlog n ≫ logResidueF f I hI hlog (n + 1) := by
  cases n with
  | zero =>
    refine (zero_comp).trans ?_
    refine (sheaf_hom_ext fun W φ => ?_).symm
    exact logRes_logD_zero hI hlog (W := W.unop) φ
  | succ p =>
    refine sheaf_hom_ext fun W φ => ?_
    exact (logRes_logD hI hlog (W := W.unop) φ).symm

/-- **The residue `Ω^•_{X/S}(log Y) ⟶ i_*Ω^•_{Y/S}[-1]`**, as a map of complexes; in degree
`p + 1` it is the morphism of `𝒪_X`-modules `AlgebraicGeometry.Scheme.Hom.logResHom`. -/
def logResidueMap : logDeRhamComplex f I hI hlog ⟶ divisorShiftComplex f I :=
  CochainComplex.ofHom (logResidueF f I hI hlog) fun n => by
    rw [divisorShiftComplex_d, logDeRhamComplex_d]
    exact logResidueF_comm f I hI hlog n

/-- The residue of a form with no pole vanishes: `logInclusionMap ≫ logResidueMap = 0`. -/
theorem logInclusionMap_comp_logResidueMap :
    logInclusionMap f I hI hlog ≫ logResidueMap f I hI hlog = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  cases n with
  | zero => exact comp_zero
  | succ p =>
    refine sheaf_hom_ext fun W ω => ?_
    exact logRes_logPolesFormsInclusion hI hlog (W := W.unop) ω

/-- **The residue sequence of the de Rham complex of log poles**
`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → i_*Ω^•_{Y/S}[-1] → 0`, as a short complex of complexes of
sheaves of abelian groups on `X`. -/
abbrev logResidueShortComplex :
    ShortComplex (CochainComplex (Sheaf (Opens.grothendieckTopology X.carrier)
      AddCommGrpCat.{u}) ℕ) :=
  ShortComplex.mk (logInclusionMap f I hI hlog) (logResidueMap f I hI hlog)
    (logInclusionMap_comp_logResidueMap f I hI hlog)

/-! ### Short exactness -/

omit hI hlog in
/-- A sequence `A → B → C` of `𝒪_X`-modules, read in sheaves of abelian groups, is short exact
once its three conditions hold near every point. -/
theorem shortExact_abelianSheaf_of_local {A B C : X.Modules} (a : A ⟶ B) (b : B ⟶ C)
    (w : (abelianSheaf X).map a ≫ (abelianSheaf X).map b = 0)
    (hmono : ∀ (U : X.Opens) (s : Γ(A, U)), a.app U s = 0 → ∀ x ∈ U,
      ∃ (V : X.Opens) (h : V ≤ U), x ∈ V ∧ A.presheaf.map (homOfLE h).op s = 0)
    (hmid : ∀ (U : X.Opens) (s : Γ(B, U)), b.app U s = 0 → ∀ x ∈ U,
      ∃ (V : X.Opens) (h : V ≤ U), x ∈ V ∧
        ∃ t : Γ(A, V), a.app V t = B.presheaf.map (homOfLE h).op s)
    (hepi : ∀ (U : X.Opens) (s : Γ(C, U)), ∀ x ∈ U,
      ∃ (V : X.Opens) (h : V ≤ U), x ∈ V ∧
        ∃ t : Γ(B, V), b.app V t = C.presheaf.map (homOfLE h).op s) :
    (ShortComplex.mk ((abelianSheaf X).map a) ((abelianSheaf X).map b) w).ShortExact := by
  refine TopCat.Sheaf.shortExact_of_local (X := X.carrier) _ ?_ ?_ ?_
  · intro U s hs x hx
    obtain ⟨V, h, hxV, hV⟩ := hmono U s hs x hx
    exact ⟨V, homOfLE h, hxV, hV⟩
  · intro U s hs x hx
    obtain ⟨V, h, hxV, t, ht⟩ := hmid U s hs x hx
    exact ⟨V, homOfLE h, hxV, t, ht⟩
  · intro U s x hx
    obtain ⟨V, h, hxV, t, ht⟩ := hepi U s x hx
    exact ⟨V, homOfLE h, hxV, t, ht⟩

omit hI hlog in
/-- A sequence `A → B → 0` of `𝒪_X`-modules, read in sheaves of abelian groups, is short exact
once `A → B` is locally injective and locally surjective. -/
theorem shortExact_abelianSheaf_of_local_zero {A B : X.Modules} (a : A ⟶ B)
    (b : (abelianSheaf X).obj B ⟶ 0) (w : (abelianSheaf X).map a ≫ b = 0)
    (hmono : ∀ (U : X.Opens) (s : Γ(A, U)), a.app U s = 0 → ∀ x ∈ U,
      ∃ (V : X.Opens) (h : V ≤ U), x ∈ V ∧ A.presheaf.map (homOfLE h).op s = 0)
    (hsurj : ∀ (U : X.Opens) (s : Γ(B, U)), ∀ x ∈ U,
      ∃ (V : X.Opens) (h : V ≤ U), x ∈ V ∧
        ∃ t : Γ(A, V), a.app V t = B.presheaf.map (homOfLE h).op s) :
    (ShortComplex.mk ((abelianSheaf X).map a) b w).ShortExact := by
  set T := ShortComplex.mk ((abelianSheaf X).map a) b w
  refine { exact := TopCat.Sheaf.exact_of_local (X := X.carrier) T ?_,
           mono_f := ?_, epi_g := IsZero.epi (isZero_zero _) _ }
  · intro U s _ x hx
    obtain ⟨V, h, hxV, t, ht⟩ := hsurj U s x hx
    exact ⟨V, homOfLE h, hxV, t, ht⟩
  · let T' := ShortComplex.mk (0 : T.X₁ ⟶ T.X₁) T.f zero_comp
    refine (T'.exact_iff_mono rfl).1 (TopCat.Sheaf.exact_of_local (X := X.carrier) T' ?_)
    intro U s hs x hx
    obtain ⟨V, h, hxV, hV⟩ := hmono U s hs x hx
    exact ⟨V, homOfLE h, hxV, 0, (map_zero _).trans hV.symm⟩

/-- In degree `p + 1`, the residue sequence
`0 → Ω^{p+1}_{X/S} → Ω^{p+1}_{X/S}(log Y) → i_*Ω^p_{Y/S} → 0` is short exact. -/
theorem shortExact_eval_succ (p : ℕ) :
    ((logResidueShortComplex f I hI hlog).map
      (HomologicalComplex.eval _ _ (p + 1))).ShortExact :=
  shortExact_abelianSheaf_of_local (logPolesFormsInclusion f I (p + 1)) (logResHom f I hI hlog p) _
    (fun U ω hω x hx => exists_map_eq_zero_of_logPolesFormsInclusion_eq_zero hI hlog ω hω x hx)
    (fun U φ hφ x hx => by
      obtain ⟨V, hVU, hxV, ω, hω⟩ :=
        exists_map_eq_logPolesFormsInclusion_of_logRes_eq_zero hI hlog φ hφ x hx
      exact ⟨V, hVU, hxV, ω, hω.symm⟩)
    (fun U ρ x hx => exists_logRes_eq hI hlog ρ x hx)

/-- In degree `0`, the residue sequence `0 → Ω^0_{X/S} → Ω^0_{X/S}(log Y) → 0 → 0` is short
exact. -/
theorem shortExact_eval_zero :
    ((logResidueShortComplex f I hI hlog).map (HomologicalComplex.eval _ _ 0)).ShortExact :=
  shortExact_abelianSheaf_of_local_zero (logPolesFormsInclusion f I 0) _ _
    (fun U ω hω x hx => exists_map_eq_zero_of_logPolesFormsInclusion_eq_zero hI hlog ω hω x hx)
    (fun U φ x hx => by
      obtain ⟨V, hVU, hxV, ω, hω⟩ := exists_map_eq_logPolesFormsInclusion_zero hI φ x hx
      exact ⟨V, hVU, hxV, ω, hω.symm⟩)

/-- **Stacks Project, Tag 0FMW.** Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an
effective Cartier divisor, cut out by `I`, for which the de Rham complex of log poles is defined
([Stacks, Tag 0FMV]). Then the sequence of complexes

`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → i_*Ω^•_{Y/S}[-1] → 0`

formed by the inclusion of forms with no pole and the residue is short exact. Here
`Ω^p_{X/S}(log Y)` is `AlgebraicGeometry.Scheme.Hom.logPolesForms`, its differential is
`AlgebraicGeometry.Scheme.Hom.logD`, characterised by the Leibniz rule
`AlgebraicGeometry.Scheme.Hom.logD_eq`, and the residue is `AlgebraicGeometry.Scheme.Hom.logRes`,
`α + dlog t ∧ β ↦ β|_Y` (`AlgebraicGeometry.Scheme.Hom.logRes_map_eq`). -/
@[stacks 0FMW]
theorem logResidueShortComplex_shortExact : (logResidueShortComplex f I hI hlog).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    cases n with
    | zero => exact shortExact_eval_zero f I hI hlog
    | succ p => exact shortExact_eval_succ f I hI hlog p

end AlgebraicGeometry.Scheme.Hom

end
