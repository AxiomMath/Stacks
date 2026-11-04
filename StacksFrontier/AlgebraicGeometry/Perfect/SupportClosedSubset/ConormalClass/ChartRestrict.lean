module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.ChartSplice

/-!
# Restricting equations to a smaller open

Let `X` be a scheme, `V ⊆ W` opens of `X` and `f₁, …, f_c ∈ Γ(W, 𝒪_W)`.  The restrictions of the
`fᵢ` to `V` are equations on `V`.  Restricting the Čech cochains from the principal opens of the
`fᵢ` in `W` to those of their restrictions in `V` is a map of complexes of `𝒪_X`-modules from the
splice of the Čech complex for `W` to the splice for `V`.  It is the identity in degree `0` and
it carries the fraction cocycle `s / (f₁ ⋯ f_c)` for `W` to the one for `V`.

## Main definitions

* `Stacks.Perfect.ConormalClass.restrictEquations`: the restricted equations.
* `Stacks.Perfect.ConormalClass.chartRestrict`: the restriction map of splices.

## Main results

* `Stacks.Perfect.ConormalClass.chartRestrict_f_zero` and `chartFraction_comp_chartRestrict`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction (fractionHom fractionHom_secIso fractionCochain_apply
  secIso_smul secIso_restrict interMonoOpen)
open Stacks.AlgebraicGeometry.ModuleLimits (homOfSections homOfSections_app)

universe u

namespace Stacks.Perfect.ConormalClass

variable {X : Scheme.{u}} {W V : X.Opens} (hVW : V ≤ W) {c : ℕ}
  (f : Fin c → Γ(W.toScheme, ⊤)) (F : X.Modules)

include hVW in
/-- The image of the top open of a smaller open subscheme. -/
theorem image_top_le : V.ι ''ᵁ ⊤ ≤ W.ι ''ᵁ ⊤ := by
  rw [V.ι_image_top, W.ι_image_top]
  exact hVW

/-- **The restriction of equations on `W` to the smaller open `V`.** -/
def restrictEquations : Fin c → Γ(V.toScheme, ⊤) :=
  fun i => X.presheaf.map (homOfLE (image_top_le hVW)).op (f i)

/-- Two chains of restriction maps of a presheaf of rings on a space with the same endpoints
agree. -/
theorem presheaf_map_map_map_eq {Y : TopCat.{u}} (P : TopCat.Presheaf CommRingCat.{u} Y)
    {A B C D E : (Opens Y)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (a' : A ⟶ E) (b' : E ⟶ D)
    (r : P.obj A) : P.map c (P.map b (P.map a r)) = P.map b' (P.map a' r) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← P.map_comp, ← P.map_comp, ← P.map_comp]
  exact congrArg (fun g => ConcreteCategory.hom (P.map g) r)
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- Two chains of two restriction maps of a presheaf of rings with the same endpoints agree. -/
theorem presheaf_map_map_eq {Y : TopCat.{u}} (P : TopCat.Presheaf CommRingCat.{u} Y)
    {A B D E : (Opens Y)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ D) (a' : A ⟶ E) (b' : E ⟶ D)
    (r : P.obj A) : P.map b (P.map a r) = P.map b' (P.map a' r) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← P.map_comp, ← P.map_comp]
  exact congrArg (fun g => ConcreteCategory.hom (P.map g) r)
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- A restriction map of a presheaf of rings is any chain of two restriction maps with the same
endpoints. -/
theorem presheaf_map_eq_map_map {Y : TopCat.{u}} (P : TopCat.Presheaf CommRingCat.{u} Y)
    {A B D : (Opens Y)ᵒᵖ} (a : A ⟶ D) (b : A ⟶ B) (c : B ⟶ D) (r : P.obj A) :
    P.map a r = P.map c (P.map b r) := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  exact congrArg (fun g => ConcreteCategory.hom (P.map g) r)
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- The scalar action on the sections of a restriction is the action on the sections of the
module. -/
theorem restrict_smul (U : X.Opens) (O : U.toScheme.Opens) (r : Γ(U.toScheme, O))
    (y : Γ((res U).obj F, O)) :
    (r • y : Γ((res U).obj F, O)) =
      @HSMul.hSMul Γ(X, U.ι ''ᵁ O) Γ(F, U.ι ''ᵁ O) Γ(F, U.ι ''ᵁ O) instHSMul r y := by
  have h₁ := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι F O r y
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_hom, Scheme.Opens.ι_appIso,
    Iso.refl_inv] at h₁
  exact h₁

/-- Membership in a finite intersection of opens. -/
theorem mem_iInf_opens {Y : TopCat} {ι : Type*} [Finite ι] (Ufam : ι → Opens Y) (z : Y) :
    z ∈ ⨅ i, Ufam i ↔ ∀ i, z ∈ Ufam i := by
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  rfl

/-- The intersections of principal opens shrink when the equations are restricted. -/
theorem inter_image_le (U : X.Opens) {p : ℕ} (s : CechCochains.OrdIndex (I := Fin c) p) :
    V.ι ''ᵁ CechCochains.inter
        (fun i => V.ι ⁻¹ᵁ U ⊓ V.toScheme.basicOpen (restrictEquations hVW f i)) s.1 ≤
      W.ι ''ᵁ CechCochains.inter (fun i => W.ι ⁻¹ᵁ U ⊓ W.toScheme.basicOpen (f i)) s.1 := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨⟨y.1, hVW y.2⟩, ?_, rfl⟩
  have hy' := (mem_iInf_opens _ y).1 hy
  refine (mem_iInf_opens (fun k => W.ι ⁻¹ᵁ U ⊓ W.toScheme.basicOpen (f (s.1 k))) _).2 fun k => ?_
  obtain ⟨h1, h2⟩ := hy' k
  refine ⟨h1, ?_⟩
  have h2' : y ∈ V.toScheme.basicOpen (restrictEquations hVW f (s.1 k)) := h2
  show (⟨y.1, hVW y.2⟩ : W.toScheme) ∈ W.toScheme.basicOpen (f (s.1 k))
  have e1 := (Scheme.Opens.mem_basicOpen_toScheme (U := V) (V := ⊤)
    (r := restrictEquations hVW f (s.1 k)) (x := y)).1 h2'
  have e2 := (Scheme.basicOpen_res X (f := f (s.1 k)) (homOfLE (image_top_le hVW)).op).le e1
  exact (Scheme.Opens.mem_basicOpen_toScheme (U := W) (V := ⊤) (r := f (s.1 k))
    (x := ⟨y.1, hVW y.2⟩)).2 e2.2

/-! ### The restriction map in positive degrees -/

section Positive

variable (p : ℕ)

/-- The componentwise restriction of Čech cochains, on sections over an open of `X`. -/
def chartRestrictSec (U : X.Opens) (x : Γ((push W).obj (prodTerm f ((res W).obj F) p), U)) :
    Γ((push V).obj (prodTerm (restrictEquations hVW f) ((res V).obj F) p), U) :=
  (secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)).symm fun s =>
    (F.presheaf.map (homOfLE (inter_image_le hVW f U s)).op
      (secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U) x s) : Γ(F, _))

/-- The component at an index of the restriction of Čech cochains is the restriction of the
component. -/
theorem secIso_chartRestrictSec (U : X.Opens)
    (x : Γ((push W).obj (prodTerm f ((res W).obj F) p), U))
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)
        (chartRestrictSec hVW f F p U x) s =
      F.presheaf.map (homOfLE (inter_image_le hVW f U s)).op
        (secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U) x s) :=
  congrFun ((secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)).apply_symm_apply _) s

/-- The restriction of Čech cochains is additive. -/
theorem chartRestrictSec_add (U : X.Opens)
    (x y : Γ((push W).obj (prodTerm f ((res W).obj F) p), U)) :
    chartRestrictSec hVW f F p U (x + y) =
      chartRestrictSec hVW f F p U x + chartRestrictSec hVW f F p U y := by
  refine (secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)).injective
    (funext fun s => ?_)
  have h1 := secIso_chartRestrictSec hVW f F p U (x + y) s
  have h2 : (secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)
      (chartRestrictSec hVW f F p U x + chartRestrictSec hVW f F p U y)) s =
      secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)
        (chartRestrictSec hVW f F p U x) s +
      secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)
        (chartRestrictSec hVW f F p U y) s :=
    congrFun (map_add (secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)) _ _) s
  have h3 : secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U) (x + y) s =
      secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U) x s + secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U) y s :=
    congrFun (map_add (secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U)) _ _) s
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [secIso_chartRestrictSec, secIso_chartRestrictSec]
  exact (congrArg (F.presheaf.map (homOfLE (inter_image_le hVW f U s)).op) h3).trans
    (map_add _ _ _)

/-- Restricting a scalar multiple of a section of `F` along an inclusion of opens. -/
private theorem map_smul_restrict {A : W.toScheme.Opens} {A' : V.toScheme.Opens}
    (h : V.ι ''ᵁ A' ≤ W.ι ''ᵁ A) (r : Γ(W.toScheme, A)) (r' : Γ(V.toScheme, A'))
    (y : Γ((res W).obj F, A)) (y' : Γ((res V).obj F, A'))
    (hr : X.presheaf.map (homOfLE h).op r = r') (hy : F.presheaf.map (homOfLE h).op y = y') :
    F.presheaf.map (homOfLE h).op (r • y : Γ((res W).obj F, A)) =
      (r' • y' : Γ((res V).obj F, A')) := by
  refine (congrArg _ (restrict_smul F W _ _ _)).trans ((Scheme.Modules.map_smul F _ _ _).trans ?_)
  refine Eq.trans ?_ (restrict_smul F V _ _ _).symm
  subst hr hy
  rfl

/-- The restriction of Čech cochains commutes with the scalar action of `Γ(X, U)`. -/
theorem chartRestrictSec_smul (U : X.Opens) (r : Γ(X, U))
    (x : Γ((push W).obj (prodTerm f ((res W).obj F) p), U)) :
    chartRestrictSec hVW f F p U (r • x) = r • chartRestrictSec hVW f F p U x := by
  refine (secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)).injective
    (funext fun s => ?_)
  have hW : secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U) (r • x) s =
      W.toScheme.presheaf.map (homOfLE (interLe f p s (W.ι ⁻¹ᵁ U))).op (W.ι.app U r) •
        secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U) x s :=
    secIso_smul f ((res W).obj F) p (W.ι ⁻¹ᵁ U) (W.ι.app U r) x s
  have hV : secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)
      (r • chartRestrictSec hVW f F p U x) s =
      V.toScheme.presheaf.map (homOfLE (interLe (restrictEquations hVW f) p s (V.ι ⁻¹ᵁ U))).op
          (V.ι.app U r) •
        secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)
          (chartRestrictSec hVW f F p U x) s :=
    secIso_smul (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U) (V.ι.app U r) _ s
  refine (secIso_chartRestrictSec hVW f F p U (r • x) s).trans (Eq.trans ?_ hV.symm)
  rw [hW, secIso_chartRestrictSec]
  exact map_smul_restrict F (inter_image_le hVW f U s) _ _ _ _
    (presheaf_map_map_map_eq X.presheaf _ _ _ _ _ r) rfl

/-- Two chains of two restriction maps of the sections of a module with the same endpoints
agree. -/
theorem modules_map_map_eq {Y : Scheme.{u}} (M : Y.Modules) {A B C E : Y.Opens}
    (a : B ⟶ A) (b : C ⟶ B) (a' : E ⟶ A) (b' : C ⟶ E) (y : Γ(M, A)) :
    M.presheaf.map b.op (M.presheaf.map a.op y) = M.presheaf.map b'.op (M.presheaf.map a'.op y) :=
  Stacks.Perfect.ExtendedAlternatingCech.collapse2_eq M a b a' b' y

/-- Chains of three and of two restriction maps of the sections of a module with the same
endpoints agree. -/
theorem modules_map_map_map_eq {Y : Scheme.{u}} (M : Y.Modules) {A B C D E : Y.Opens}
    (a : B ⟶ A) (b : C ⟶ B) (c' : D ⟶ C) (a' : E ⟶ A) (b' : D ⟶ E) (y : Γ(M, A)) :
    M.presheaf.map c'.op (M.presheaf.map b.op (M.presheaf.map a.op y)) =
      M.presheaf.map b'.op (M.presheaf.map a'.op y) := by
  rw [Stacks.Perfect.ExtendedAlternatingCech.map_map_apply,
    Stacks.Perfect.ExtendedAlternatingCech.map_map_apply,
    Stacks.Perfect.ExtendedAlternatingCech.map_map_apply]
  exact Stacks.Perfect.ExtendedAlternatingCech.map_eq_apply M _ _ y

/-- The restriction maps of sections of `F` from `U` down to the intersections of principal opens
commute with the restriction of Čech cochains. -/
private theorem map_interLe_image_preimage (U : X.Opens)
    (t : CechCochains.OrdIndex (I := Fin c) p) (y : Γ(F, U)) :
    F.presheaf.map (homOfLE (inter_image_le hVW f U t)).op
        (F.presheaf.map (W.ι.opensFunctor.map (homOfLE (interLe f p t (W.ι ⁻¹ᵁ U)))).op
          (F.presheaf.map (homOfLE (W.ι.image_preimage_le U)).op y)) =
      F.presheaf.map
        (V.ι.opensFunctor.map (homOfLE (interLe (restrictEquations hVW f) p t (V.ι ⁻¹ᵁ U)))).op
        (F.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op y) :=
  modules_map_map_map_eq F (homOfLE (W.ι.image_preimage_le U))
    (W.ι.opensFunctor.map (homOfLE (interLe f p t (W.ι ⁻¹ᵁ U))))
    (homOfLE (inter_image_le hVW f U t)) (homOfLE (V.ι.image_preimage_le U))
    (V.ι.opensFunctor.map (homOfLE (interLe (restrictEquations hVW f) p t (V.ι ⁻¹ᵁ U)))) y

/-- The components of the restriction of a Čech cochain to a smaller open are the restrictions
of its components. -/
theorem secIso_push_restrict {U U' : X.Opens} (h : U' ≤ U)
    (x : Γ((push W).obj (prodTerm f ((res W).obj F) p), U))
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U')
        (((push W).obj (prodTerm f ((res W).obj F) p)).presheaf.map (homOfLE h).op x) s =
      F.presheaf.map (W.ι.opensFunctor.map
        (homOfLE (interMonoOpen f p s (W.ι.preimage_mono h)))).op
        (secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U) x s : Γ(F, _)) :=
  secIso_restrict f ((res W).obj F) p (W.ι.preimage_mono h) x s

/-- The restriction of Čech cochains commutes with the restriction maps of the pushforward
sheaves. -/
theorem chartRestrictSec_restrict {U U' : X.Opens} (h : U' ≤ U)
    (x : Γ((push W).obj (prodTerm f ((res W).obj F) p), U)) :
    chartRestrictSec hVW f F p U'
        (((push W).obj (prodTerm f ((res W).obj F) p)).presheaf.map (homOfLE h).op x) =
      ((push V).obj (prodTerm (restrictEquations hVW f) ((res V).obj F) p)).presheaf.map
        (homOfLE h).op (chartRestrictSec hVW f F p U x) := by
  refine (secIso (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U')).injective
    (funext fun s => ?_)
  have hL := secIso_chartRestrictSec hVW f F p U'
    (((push W).obj (prodTerm f ((res W).obj F) p)).presheaf.map (homOfLE h).op x) s
  have hL2 := secIso_push_restrict f F p h x s
  have hR := secIso_push_restrict (restrictEquations hVW f) F p h
    (chartRestrictSec hVW f F p U x) s
  have hR2 := secIso_chartRestrictSec hVW f F p U x s
  refine hL.trans (Eq.trans ?_ hR.symm)
  refine (congrArg (F.presheaf.map (homOfLE (inter_image_le hVW f U' s)).op) hL2).trans ?_
  refine Eq.trans ?_ (congrArg (F.presheaf.map (V.ι.opensFunctor.map
    (homOfLE (interMonoOpen (restrictEquations hVW f) p s (V.ι.preimage_mono h)))).op) hR2).symm
  exact modules_map_map_eq F (W.ι.opensFunctor.map
      (homOfLE (interMonoOpen f p s (W.ι.preimage_mono h))))
    (homOfLE (inter_image_le hVW f U' s)) (homOfLE (inter_image_le hVW f U s))
    (V.ι.opensFunctor.map
      (homOfLE (interMonoOpen (restrictEquations hVW f) p s (V.ι.preimage_mono h)))) _

/-- **The restriction map of splices in positive degrees.** -/
def chartRestrictHom : (push W).obj (prodTerm f ((res W).obj F) p) ⟶
    (push V).obj (prodTerm (restrictEquations hVW f) ((res V).obj F) p) :=
  homOfSections (chartRestrictSec hVW f F p) (chartRestrictSec_add hVW f F p)
    (chartRestrictSec_smul hVW f F p) (fun _ _ h x => chartRestrictSec_restrict hVW f F p h x)

/-- On sections over `U`, `chartRestrictHom` is the restriction of Čech cochains. -/
theorem chartRestrictHom_app (U : X.Opens)
    (x : Γ((push W).obj (prodTerm f ((res W).obj F) p), U)) :
    (chartRestrictHom hVW f F p).app U x = chartRestrictSec hVW f F p U x :=
  rfl

omit hVW in
/-- A restriction of Čech cochains on `W` followed by the comparison to `V` is the comparison
followed by a restriction of Čech cochains on `V`. -/
theorem restr_comparison {A B : W.toScheme.Opens} {A' B' : V.toScheme.Opens} (h₁ : B ≤ A)
    (h₂ : V.ι ''ᵁ B' ≤ W.ι ''ᵁ B) (h₃ : V.ι ''ᵁ A' ≤ W.ι ''ᵁ A) (h₄ : B' ≤ A')
    (y : Γ(F, W.ι ''ᵁ A)) :
    F.presheaf.map (homOfLE h₂).op (CechCochains.restr ((res W).obj F).presheaf h₁ y) =
      CechCochains.restr ((res V).obj F).presheaf h₄ (F.presheaf.map (homOfLE h₃).op y) :=
  modules_map_map_eq F (W.ι.opensFunctor.map (homOfLE h₁)) (homOfLE h₂) (homOfLE h₃)
    (V.ι.opensFunctor.map (homOfLE h₄)) y

/-- The restriction of Čech cochains commutes with the Čech differential, on sections. -/
theorem chartRestrictSec_difSucc (U : X.Opens)
    (x : Γ((push W).obj (prodTerm f ((res W).obj F) p), U)) :
    chartRestrictSec hVW f F (p + 1) U ((difSucc f ((res W).obj F) p).app (W.ι ⁻¹ᵁ U) x) =
      (difSucc (restrictEquations hVW f) ((res V).obj F) p).app (V.ι ⁻¹ᵁ U)
        (chartRestrictSec hVW f F p U x) := by
  refine (secIso (restrictEquations hVW f) ((res V).obj F) (p + 1) (V.ι ⁻¹ᵁ U)).injective
    (funext fun t => ?_)
  have h1 := secIso_chartRestrictSec hVW f F (p + 1) U
    ((difSucc f ((res W).obj F) p).app (W.ι ⁻¹ᵁ U) x) t
  have h2 := congrFun (secIso_difSucc f ((res W).obj F) p (W.ι ⁻¹ᵁ U) x) t
  have h3 := congrFun (secIso_difSucc (restrictEquations hVW f) ((res V).obj F) p (V.ι ⁻¹ᵁ U)
    (chartRestrictSec hVW f F p U x)) t
  refine h1.trans (Eq.trans ?_ h3.symm)
  rw [h2, ordD_apply, ordD_apply]
  refine (map_sum (F.presheaf.map (homOfLE (inter_image_le hVW f U t)).op).hom _ _).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (map_zsmul (F.presheaf.map (homOfLE (inter_image_le hVW f U t)).op).hom _ _).trans ?_
  refine congrArg (fun z => ((-1 : ℤ) ^ (j : ℕ)) • z) ?_
  let t' : CechCochains.OrdIndex (I := Fin c) p :=
    ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩
  refine (restr_comparison F
    (CechCochains.inter_le_omit (fun i => W.ι ⁻¹ᵁ U ⊓ W.toScheme.basicOpen (f i)) t.1 j)
    (inter_image_le hVW f U t) (inter_image_le hVW f U t')
    (CechCochains.inter_le_omit
      (fun i => V.ι ⁻¹ᵁ U ⊓ V.toScheme.basicOpen (restrictEquations hVW f i)) t.1 j)
    (secIso f ((res W).obj F) p (W.ι ⁻¹ᵁ U) x t')).trans ?_
  exact congrArg (CechCochains.restr ((res V).obj F).presheaf
    (CechCochains.inter_le_omit
      (fun i => V.ι ⁻¹ᵁ U ⊓ V.toScheme.basicOpen (restrictEquations hVW f i)) t.1 j))
    (secIso_chartRestrictSec hVW f F p U x t').symm

/-- The restriction of Čech cochains commutes with the first differential, on sections. -/
theorem chartRestrictSec_difZero (U : X.Opens) (y : Γ(F, U)) :
    chartRestrictSec hVW f F 0 U ((difZero f ((res W).obj F)).app (W.ι ⁻¹ᵁ U)
        ((unitW W F).app U y)) =
      (difZero (restrictEquations hVW f) ((res V).obj F)).app (V.ι ⁻¹ᵁ U)
        ((unitW V F).app U y) := by
  refine (secIso (restrictEquations hVW f) ((res V).obj F) 0 (V.ι ⁻¹ᵁ U)).injective
    (funext fun t => ?_)
  refine (secIso_chartRestrictSec hVW f F 0 U _ t).trans ?_
  refine (congrArg (F.presheaf.map (homOfLE (inter_image_le hVW f U t)).op)
    (secIso_difZero f ((res W).obj F) (W.ι ⁻¹ᵁ U) ((unitW W F).app U y) t)).trans ?_
  refine Eq.trans ?_ (secIso_difZero (restrictEquations hVW f) ((res V).obj F) (V.ι ⁻¹ᵁ U)
    ((unitW V F).app U y) t).symm
  exact map_interLe_image_preimage hVW f F 0 U t y

end Positive

/-! ### The fraction cocycle -/

section Fraction

variable {d : ℕ} (f : Fin (d + 1) → Γ(W.toScheme, ⊤))

/-- The restriction of Čech cochains carries the fraction cochain to the fraction cochain. -/
theorem chartRestrictSec_fraction (U : X.Opens) (y : Γ(F, U)) :
    chartRestrictSec hVW f F d U ((fractionHom f ((res W).obj F) d).app (W.ι ⁻¹ᵁ U)
        ((unitW W F).app U y)) =
      (fractionHom (restrictEquations hVW f) ((res V).obj F) d).app (V.ι ⁻¹ᵁ U)
        ((unitW V F).app U y) := by
  refine (secIso (restrictEquations hVW f) ((res V).obj F) d (V.ι ⁻¹ᵁ U)).injective
    (funext fun t => ?_)
  refine (secIso_chartRestrictSec hVW f F d U _ t).trans ?_
  have hW := fractionHom_secIso f ((res W).obj F) d (W.ι ⁻¹ᵁ U) ((unitW W F).app U y) t
  have hV := fractionHom_secIso (restrictEquations hVW f) ((res V).obj F) d (V.ι ⁻¹ᵁ U)
    ((unitW V F).app U y) t
  refine (congrArg (F.presheaf.map (homOfLE (inter_image_le hVW f U t)).op)
    (hW.trans (fractionCochain_apply _ _ _ _ _ _))).trans ?_
  refine Eq.trans ?_ (hV.trans (fractionCochain_apply _ _ _ _ _ _)).symm
  have hu := Stacks.Perfect.SupportedFraction.isUnit_prodEquations f (W.ι ⁻¹ᵁ U) d t
  refine map_smul_restrict F (inter_image_le hVW f U t) _ _ _ _ ?_ ?_
  · refine (Stacks.Perfect.SupportedFraction.map_ringInverse
      (X := X) (homOfLE (inter_image_le hVW f U t)) hu).trans ?_
    congr 1
    have hprod : (∏ k, restrictEquations hVW f (t.1 k)) =
        X.presheaf.map (homOfLE (image_top_le hVW)).op (∏ k, f (t.1 k)) :=
      (map_prod (X.presheaf.map (homOfLE (image_top_le hVW)).op).hom _ _).symm
    rw [hprod]
    exact presheaf_map_map_eq X.presheaf
      (W.ι.opensFunctor.map (homOfLE (le_top :
        CechCochains.inter (fun i => W.ι ⁻¹ᵁ U ⊓ W.toScheme.basicOpen (f i)) t.1 ≤ ⊤))).op
      (homOfLE (inter_image_le hVW f U t)).op (homOfLE (image_top_le hVW)).op
      (V.ι.opensFunctor.map (homOfLE (le_top : CechCochains.inter
        (fun i => V.ι ⁻¹ᵁ U ⊓ V.toScheme.basicOpen (restrictEquations hVW f i)) t.1 ≤ ⊤))).op
      (∏ k, f (t.1 k))
  · exact map_interLe_image_preimage hVW f F d U t y

end Fraction

/-! ### The restriction map of splices -/

section Map

/-- The first differential of the splice on sections. -/
theorem chartSplice_d_zero_app {W : X.Opens} {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)) (U : X.Opens)
    (y : Γ(F, U)) :
    ((chartSplice W f F).d 0 1).app U y =
      (difZero f ((res W).obj F)).app (W.ι ⁻¹ᵁ U) ((unitW W F).app U y) := by
  rw [chartSplice_d_zero, cplx_d_zero]
  rfl

/-- The positive-degree differentials of the splice on sections. -/
theorem chartSplice_d_succ_app {W : X.Opens} {c : ℕ} (f : Fin c → Γ(W.toScheme, ⊤)) (p : ℕ)
    (U : X.Opens) (x : Γ((push W).obj (prodTerm f ((res W).obj F) p), U)) :
    ((chartSplice W f F).d (p + 1) (p + 1 + 1)).app U x =
      (difSucc f ((res W).obj F) p).app (W.ι ⁻¹ᵁ U) x := by
  rw [chartSplice_d_succ, cplx_d_succ]
  rfl

/-- The components of the restriction map of splices. -/
def chartRestrictF : ∀ n : ℕ,
    (chartSplice W f F).X n ⟶ (chartSplice V (restrictEquations hVW f) F).X n
  | 0 => 𝟙 F
  | p + 1 => chartRestrictHom hVW f F p

/-- **The restriction map of splices**, the identity in degree `0` and the componentwise
restriction of Čech cochains in positive degrees. -/
def chartRestrict : chartSplice W f F ⟶ chartSplice V (restrictEquations hVW f) F :=
  CochainComplex.ofHom (chartRestrictF hVW f F) (by
    intro n
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    cases n with
    | zero =>
      exact (chartSplice_d_zero_app F (restrictEquations hVW f) U x).trans
        ((chartRestrictSec_difZero hVW f F U x).symm.trans
          (congrArg (chartRestrictSec hVW f F 0 U) (chartSplice_d_zero_app F f U x).symm))
    | succ p =>
      exact (chartSplice_d_succ_app F (restrictEquations hVW f) p U
          (chartRestrictSec hVW f F p U x)).trans
        ((chartRestrictSec_difSucc hVW f F p U x).symm.trans
          (congrArg (chartRestrictSec hVW f F (p + 1) U)
            (chartSplice_d_succ_app F f p U x).symm)))

/-- The restriction map of splices is the identity in degree `0`. -/
theorem chartRestrict_f_zero : (chartRestrict hVW f F).f 0 = 𝟙 F := rfl

/-- **The restriction map of splices carries the fraction cocycle to the fraction cocycle.** -/
theorem chartFraction_comp_chartRestrict {d : ℕ} (f : Fin (d + 1) → Γ(W.toScheme, ⊤)) :
    chartFraction W f F ≫ (chartRestrict hVW f F).f (d + 1) =
      chartFraction V (restrictEquations hVW f) F := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => ?_)
  exact chartRestrictSec_fraction hVW F f U y

end Map

end Stacks.Perfect.ConormalClass
