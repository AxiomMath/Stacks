module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.ChartTop
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# The class of a chart descends to the restriction to the closed subscheme

Let `i : Z ⟶ X` be a closed immersion, `W ⊆ X` an open and `f₁, …, f_c ∈ Γ(W, 𝒪_X)` sections
generating the ideal sheaf of `Z` over `W`.  The class `c_{W,f} : ℱ ⟶ i_*ℋ^c_T(ℱ)` of the
fraction `s / (f₁ ⋯ f_c)` kills the multiples of the `fᵢ`, so over `W` it factors through the
quotient `ℱ ⟶ i_*i^*ℱ`: there is a unique morphism

`c̄_{W,f} : i_*i^*ℱ ⟶ j_*(i_*ℋ^c_T(ℱ)|_W)`

whose composite with the unit `ℱ ⟶ i_*i^*ℱ` is `c_{W,f}` followed by the restriction to `W`.
This is the map `i_*i^*ℱ ⟶ i_*ℋ^c_Z(ℱ)` of Stacks 0G7Q on the chart.

The factorization goes through the cokernel `𝒬` of `(f₁, …, f_c) : ℱ|_W^{⊕c} ⟶ ℱ|_W`: its direct
image to `X` is annihilated by the ideal of `Z`, hence is a direct image along `i` (Stacks 08KS),
and the map `ℱ ⟶ j_*𝒬` therefore factors through the unit of `i^* ⊣ i_*`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction (supportCohomologySheaf supportCohomologySheafMap globalSmul)
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.RingedSpace

universe u

namespace Stacks.Perfect.ConormalClass

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### The annihilator ideal of a module -/

section Annihilator

variable (N : X.Modules)

/-- The sections of `𝒪_X` over `V` whose restrictions to every open `V' ⊆ V` kill all sections
of `N` over `V'`. -/
def annihilatorObj (V : X.Opens) : Ideal Γ(X, V) where
  carrier := {b | ∀ (V' : X.Opens) (h : V' ≤ V) (m : Γ(N, V')),
    X.presheaf.map (homOfLE h).op b • m = 0}
  zero_mem' V' h m := by rw [map_zero, zero_smul]
  add_mem' {a b} ha hb V' h m := by rw [map_add, add_smul, ha V' h m, hb V' h m, add_zero]
  smul_mem' r b hb V' h m := by
    rw [smul_eq_mul, map_mul, mul_smul, hb V' h m, smul_zero]

/-- A section `b` of `𝒪_X` over `V` lies in `annihilatorObj N V` if and only if its restriction
to every open `V' ⊆ V` kills every section of `N` over `V'`. -/
theorem mem_annihilatorObj {V : X.Opens} {b : Γ(X, V)} :
    b ∈ annihilatorObj N V ↔ ∀ (V' : X.Opens) (h : V' ≤ V) (m : Γ(N, V')),
      X.presheaf.map (homOfLE h).op b • m = 0 :=
  Iff.rfl

/-- **The annihilator ideal subsheaf of a module.** -/
def annihilatorIdeal : (structureSheafModule X.toRingedSpace).Submodule where
  obj V := annihilatorObj N V.unop
  map {V W} i b hb V' h m := by
    have e : ∀ r : X.presheaf.obj V, X.presheaf.map (homOfLE h).op ((X.presheaf.map i) r) =
        X.presheaf.map (homOfLE (h.trans i.unop.le)).op r := fun r =>
      (presheaf_map_eq_map_map X.presheaf _ i _ r).symm
    exact (congrArg (fun r => r • m) (e b)).trans (hb V' _ m)
  isSheaf {V} b hsieve V' h m := by
    classical
    have hcov : ∀ x : V', ∃ (W' : X.Opens) (g : W' ⟶ V.unop),
        X.presheaf.map g.op b ∈ annihilatorObj N W' ∧ x.1 ∈ W' := by
      intro x
      obtain ⟨W', g, hg, hx⟩ := (Opens.mem_grothendieckTopology _).mp hsieve x.1 (h x.2)
      exact ⟨W', g, hg, hx⟩
    choose W' g hg hx using hcov
    refine TopCat.Sheaf.eq_of_locally_eq' (F := (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab.{u} X))
      (fun x : V' => V' ⊓ W' x) V' (fun x => homOfLE inf_le_left)
      (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hy, hx ⟨y, hy⟩⟩) _ _ fun x => ?_
    have e : ∀ r : X.presheaf.obj V,
        X.presheaf.map (homOfLE (inf_le_left : V' ⊓ W' x ≤ V')).op
          (X.presheaf.map (homOfLE h).op r) =
        X.presheaf.map (homOfLE (inf_le_right : V' ⊓ W' x ≤ W' x)).op
          (X.presheaf.map (g x).op r) := fun r =>
      presheaf_map_map_eq X.presheaf _ _ _ _ r
    refine ((Scheme.Modules.map_smul N (homOfLE (inf_le_left : V' ⊓ W' x ≤ V')) _ m).trans
      ((congrArg (fun r => r • N.presheaf.map (homOfLE (inf_le_left : V' ⊓ W' x ≤ V')).op m)
        (e b)).trans (hg x _ inf_le_right _))).trans ?_
    exact (map_zero (N.presheaf.map (homOfLE (inf_le_left : V' ⊓ W' x ≤ V')).op).hom).symm

/-- A section of an ideal generated over `W` by sections killing `N` kills `N`. -/
theorem smul_eq_zero_of_mem_generatedIdealOn {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W))
    (hf : ∀ j, f j ∈ annihilatorObj N W) {V : X.Opens}
    (b : Γ(X, V)) (hb : b ∈ (generatedIdealOn X.toRingedSpace W f).obj (op V)) (m : Γ(N, V)) :
    b • m = 0 := by
  have hle := generatedIdealOn_le X.toRingedSpace W f (annihilatorIdeal N) hf
  have hK : b ∈ annihilatorObj N V := hle (op V) hb
  have h := hK V le_rfl m
  rwa [show (homOfLE (le_refl V)) = 𝟙 V from rfl, op_id, X.presheaf.map_id] at h

end Annihilator

/-! ### Equations on an open -/

section Equations

variable (W : X.Opens) {c : ℕ} (f : Fin c → Γ(X, W))

/-- Sections of `𝒪_X` over an open `W`, read as functions on the open subscheme `W`. -/
def chartEq : Fin c → Γ(W.toScheme, ⊤) :=
  fun j => X.presheaf.map (homOfLE W.ι_image_top.le).op (f j)

/-- Restricting the function `chartEq W f j` on `W` to an open `U ⊆ W` gives the restriction of
`f j` from `W` to `U`. -/
theorem restrictFun_chartEq {U : X.Opens} (hU : U ≤ W) (j : Fin c) :
    restrictFun W hU (chartEq W f j) = X.presheaf.map (homOfLE hU).op (f j) :=
  (presheaf_map_eq_map_map X.presheaf _ _ _ (f j)).symm

/-- Multiplication by a function on `W`, on the restriction of a module to `W`, is
multiplication by the restricted function. -/
theorem globalSmul_res_app (F : X.Modules) (r : Γ(W.toScheme, ⊤)) (P : W.toScheme.Opens)
    (s : Γ((res W).obj F, P)) :
    (globalSmul r ((res W).obj F)).app P s =
      (restrictFun W (W.ι_image_le P) r • (show Γ(F, W.ι ''ᵁ P) from s) : Γ(F, W.ι ''ᵁ P)) := by
  refine (Stacks.Perfect.SupportedFraction.globalSmul_app _ _ _ _).trans ?_
  refine (restrict_smul F W _ _ _).trans ?_
  congr 1

/-- A restriction followed by a restriction back along opens with the same preimage is the
identity on the sections of a module on the open subscheme. -/
theorem modules_map_map_self {Y : Scheme.{u}} (M : Y.Modules) {A B : Y.Opens} (a : B ⟶ A)
    (b : A ⟶ B) (y : Γ(M, A)) : M.presheaf.map b.op (M.presheaf.map a.op y) = y := by
  refine (modules_map_map_eq M a b (𝟙 A) (𝟙 A) y).trans ?_
  rw [op_id, M.presheaf.map_id]
  rfl

/-- On the direct image of a module on `W`, restriction from `U` to `U ⊓ W` is injective. -/
theorem injective_push_map_inf (Q : W.toScheme.Modules) (U : X.Opens) :
    Function.Injective ((push W).obj Q |>.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op) := by
  intro y y' h
  have hle : W.ι ⁻¹ᵁ U ≤ W.ι ⁻¹ᵁ (U ⊓ W) := fun x hx => ⟨hx, x.2⟩
  have e : ∀ z : Γ(Q, W.ι ⁻¹ᵁ U), Q.presheaf.map (homOfLE hle).op
      (((push W).obj Q).presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op z) = z :=
    fun z => modules_map_map_self Q _ _ z
  rw [← e y, ← e y', h]

variable {Z : Scheme.{u}} (i : Z ⟶ X)

include f in
/-- **A module killed by equations of `Z` on `W` has a direct image killed by the ideal of `Z`.**
If `f₁, …, f_c` generate the ideal sheaf of `Z` over `W` and each `fᵢ` acts by zero on a module
`𝒬` on `W`, then every section of `𝒪_X` vanishing on `Z` kills the direct image of `𝒬` to `X`. -/
theorem push_smul_eq_zero (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f)
    (Q : W.toScheme.Modules) (hQ : ∀ j, globalSmul (chartEq W f j) Q = 0) (U : X.Opens)
    (a : Γ(X, U)) (ha : (i.app U).hom a = 0) (m : Γ((push W).obj Q, U)) : a • m = 0 := by
  have hf : ∀ j, f j ∈ annihilatorObj ((push W).obj Q) W := by
    intro j V' hV' m'
    have key : ∀ m'' : Γ(Q, W.ι ⁻¹ᵁ V'),
        W.ι.app V' (X.presheaf.map (homOfLE hV').op (f j)) • m'' = 0 := by
      intro m''
      have h := congrArg (fun φ => φ.app (W.ι ⁻¹ᵁ V') m'') (hQ j)
      simp only [Scheme.Modules.Hom.zero_app, AddCommGrpCat.hom_zero] at h
      refine Eq.trans ?_ ((Stacks.Perfect.SupportedFraction.globalSmul_app _ _ _ _).symm.trans h)
      congr 1
      rw [Scheme.Opens.ι_app]
      exact presheaf_map_map_eq X.presheaf _ _ _ _ (f j)
    exact key m'
  have ha' : a ∈ (definingIdealOfHom i).obj (op U) := ha
  have hres := (definingIdealOfHom i).toSubmodule.map_mem
    (homOfLE (inf_le_left : U ⊓ W ≤ U)).op ha'
  have hgen' := hgen (U ⊓ W) inf_le_right
  have hb : X.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op a ∈
      (generatedIdealOn X.toRingedSpace W f).obj (op (U ⊓ W)) := hgen' ▸ hres
  refine injective_push_map_inf W Q U ?_
  refine (Scheme.Modules.map_smul ((push W).obj Q) (homOfLE (inf_le_left : U ⊓ W ≤ U)) a m).trans ?_
  refine (smul_eq_zero_of_mem_generatedIdealOn ((push W).obj Q) f hf _ hb _).trans ?_
  exact (map_zero (((push W).obj Q).presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op).hom).symm

end Equations

/-! ### The factorization through `i_*i^*ℱ` -/

section Descent

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (W : X.Opens) {c : ℕ}
  (f : Fin c → Γ(X, W)) (F : X.Modules)

/-- The map `(f₁, …, f_c) : ℱ|_W^{⊕c} ⟶ ℱ|_W`. -/
def eqMap : (∐ fun _ : Fin c => (res W).obj F) ⟶ (res W).obj F :=
  Sigma.desc fun j => globalSmul (chartEq W f j) ((res W).obj F)

/-- The quotient `ℱ|_W / (f₁, …, f_c)ℱ|_W`. -/
abbrev eqQuot : W.toScheme.Modules := cokernel (eqMap W f F)

/-- Each `fⱼ` acts by zero on the quotient `ℱ|_W / (f₁, …, f_c)ℱ|_W`. -/
theorem globalSmul_eqQuot (j : Fin c) : globalSmul (chartEq W f j) (eqQuot W f F) = 0 := by
  rw [← cancel_epi (cokernel.π (eqMap W f F)), comp_zero,
    ← Stacks.Perfect.SupportedFraction.globalSmul_naturality]
  have h : globalSmul (chartEq W f j) ((res W).obj F) =
      Sigma.ι (fun _ : Fin c => (res W).obj F) j ≫ eqMap W f F :=
    (Sigma.ι_desc (fun j => globalSmul (chartEq W f j) ((res W).obj F)) j).symm
  rw [h, Category.assoc, cokernel.condition, comp_zero]

variable (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f)

include hgen in
/-- If `f₁, …, f_c` generate the ideal sheaf of `Z` over `W`, the unit of `i^* ⊣ i_*` at the
direct image `j_*(ℱ|_W / (f₁, …, f_c))` is an isomorphism. -/
theorem isIso_unit_push_eqQuot :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      ((push W).obj (eqQuot W f F))) :=
  Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero i _
    (push_smul_eq_zero W f i hgen _ (globalSmul_eqQuot W f F))

/-- The map `i_*i^*ℱ ⟶ j_*(ℱ|_W / (f₁, …, f_c))` induced by the quotient map. -/
def quotFactor : (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F) ⟶
    (push W).obj (eqQuot W f F) :=
  haveI := isIso_unit_push_eqQuot i W f F hgen
  (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map
      (unitW W F ≫ (push W).map (cokernel.π (eqMap W f F)))) ≫
    inv ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app ((push W).obj (eqQuot W f F)))

/-- The composite of the unit `ℱ ⟶ i_*i^*ℱ` with `quotFactor` is the map
`ℱ ⟶ j_*(ℱ|_W / (f₁, …, f_c))` induced by the quotient map. -/
theorem unit_comp_quotFactor :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F ≫ quotFactor i W f F hgen =
      unitW W F ≫ (push W).map (cokernel.π (eqMap W f F)) := by
  have := isIso_unit_push_eqQuot i W f F hgen
  have hn : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F ≫
      (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map
        (unitW W F ≫ (push W).map (cokernel.π (eqMap W f F)))) =
      (unitW W F ≫ (push W).map (cokernel.π (eqMap W f F))) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app ((push W).obj (eqQuot W f F)) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality _).symm
  rw [quotFactor, ← Category.assoc, hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

variable {T : Set X} (hT : IsClosed T) (hfT : chartSupport W (chartEq W f) ⊆ T)

/-- The class of the chart, restricted to `W`, vanishes on the image of
`(f₁, …, f_c) : ℱ|_W^{⊕c} ⟶ ℱ|_W`. -/
theorem eqMap_comp_res_topClass :
    eqMap W f F ≫ (res W).map (topClass W F hT (chartEq W f) hfT) = 0 := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [eqMap, Sigma.ι_desc_assoc, comp_zero]
  refine Scheme.Modules.hom_ext _ _ fun P => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  refine (congrArg ((topClass W F hT (chartEq W f) hfT).app (W.ι ''ᵁ P))
    (globalSmul_res_app W F _ P s)).trans ?_
  refine (topClass_app_smul_eq_zero W F hT (chartEq W f) hfT j (W.ι_image_le P) s).trans ?_
  rw [Scheme.Modules.Hom.zero_app]
  rfl

/-- The class of the chart on the quotient `ℱ|_W / (f₁, …, f_c)`. -/
def quotLift : eqQuot W f F ⟶ (res W).obj (supportCohomologySheaf hT F (c : ℤ)) :=
  cokernel.desc _ _ (eqMap_comp_res_topClass W f F hT hfT)

/-- **The class of the chart, read on `i_*i^*ℱ`**: the morphism
`c̄_{W,f} : i_*i^*ℱ ⟶ j_*(i_*ℋ^c_T(ℱ)|_W)` of Stacks 0G7Q. -/
def chartDescent : (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F) ⟶
    (push W).obj ((res W).obj (supportCohomologySheaf hT F (c : ℤ))) :=
  quotFactor i W f F hgen ≫ (push W).map (quotLift W f F hT hfT)

/-- **The characterizing property of `c̄_{W,f}`**: composed with the unit `ℱ ⟶ i_*i^*ℱ` it is the
class of the chart followed by the restriction to `W`. -/
theorem unit_comp_chartDescent :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F ≫ chartDescent i W f F hgen hT hfT =
      topClass W F hT (chartEq W f) hfT ≫ unitW W (supportCohomologySheaf hT F (c : ℤ)) := by
  rw [chartDescent, ← Category.assoc, unit_comp_quotFactor, Category.assoc, ← Functor.map_comp,
    quotLift, cokernel.π_desc]
  exact ((Scheme.Modules.restrictAdjunction W.ι).unit.naturality _).symm

/-- Morphisms out of `i_*i^*ℱ` are determined by their composites with the unit. -/
theorem hom_ext_unit {N : X.Modules}
    {g g' : (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F) ⟶ N}
    (h : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F ≫ g =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F ≫ g') : g = g' :=
  have := Stacks.ClosedImmersion.epi_unit_app i F
  (cancel_epi _).1 h

end Descent

end Stacks.Perfect.ConormalClass
