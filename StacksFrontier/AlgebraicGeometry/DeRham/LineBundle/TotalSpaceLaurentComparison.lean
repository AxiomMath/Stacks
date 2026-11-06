module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceWeightZero
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.LaurentPuncturedBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.LaurentChartForms
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymGenSections
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.WeightZeroChart
import StacksCore.Tactic.StacksAttribute

/-!
# The positive-weight forms of the total space and of the complement of the zero section

Let `π : 𝕃 → X` be the total space of a line bundle `L` on `X` over `S`, and `L^⋆ ⊆ 𝕃` the
complement of the zero section. This file proves part (3) of Stacks Tag 0FUH: for `n > 0` and
`p ≥ 0` the weight-`n` part `Ω^p_{𝕃/S, n}` of `π_* Ω^p_{𝕃/S}` is identified, by the restriction
of forms along `L^⋆ ⊆ 𝕃`, with the weight-`n` part `Ω^p_{L^⋆/S, n}` of the pushed-forward forms
of `L^⋆`.

## Main definitions

* `Stacks.LineBundle.Situation.formsRestrict`: the restriction of forms
  `π_* Ω^p_{𝕃/S} ⟶ (L^⋆ → X)_* Ω^p_{L^⋆/S}`.
* `Stacks.LineBundle.Situation.gradedFormsIsoLaurent`: the identification
  `Ω^p_{𝕃/S, n} ≅ Ω^p_{L^⋆/S, n}` for `n > 0`.

## Main results

* `Stacks.LineBundle.Situation.gradedTotalForms_le_comap`: the restriction preserves weights.
* `Stacks.LineBundle.Situation.mono_gradedFormsRestrict` and
  `Stacks.LineBundle.Situation.imageSubmodule_gradedFormsRestrict`: in positive weight the
  restriction is injective with image `Ω^p_{L^⋆/S, n}`.
* `Stacks.LineBundle.Situation.gradedFormsIsoLaurent_hom_ι`: the identification is the
  restriction of forms.

## Implementation notes

The statement is checked on charts, affine opens `U = Spec A` of `X` over affine opens
`Spec R` of `S` on which `L` is trivial. There the restriction of forms is the map of Kähler
forms `Ω^p_{A[X]/R} → Ω^p_{A[T, T⁻¹]/R}` (`TotalChart.formsLFs_restrictForms`), and the
comparison of weight components is the ring-level
`LaurentDeRham.transport_weightComparison`.

The printed statement of Tag 0FUH writes `Ω^p_{L/X, n}`; this is a misprint for `Ω^p_{L/S, n}`,
see `Stacks.LineBundle.Situation.gradedFormsIsoLaurent`.

## References

* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite Polynomial

universe u

namespace SheafOfModules.Submodule

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **The preimage of a submodule sheaf under a morphism of sheaves of modules.** -/
@[sga "6 0 2.11" "more general"]
def comap {M N : _root_.SheafOfModules.{u} R} (φ : M ⟶ N) (G : N.Submodule) : M.Submodule where
  obj X := (G.obj X).comap (φ.val.app X).hom
  map {X Y} f x hx := by
    change φ.val.app Y (M.val.map f x) ∈ G.obj Y
    rw [PresheafOfModules.naturality_apply]
    exact G.map f hx
  isSheaf {X} s hs := by
    refine G.isSheaf (φ.val.app X s) (J.superset_covering (fun V g hg => ?_) hs)
    change N.val.map g.op (φ.val.app X s) ∈ G.obj (op V)
    rw [← PresheafOfModules.naturality_apply]
    exact hg

/-- A section lies in the preimage `comap φ G` iff its image under `φ` lies in `G`. -/
theorem mem_comap {M N : _root_.SheafOfModules.{u} R} (φ : M ⟶ N) (G : N.Submodule) {X : Cᵒᵖ}
    (s : M.val.obj X) : s ∈ (comap φ G).obj X ↔ φ.val.app X s ∈ G.obj X :=
  Iff.rfl

end SheafOfModules.Submodule

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- The square of the inclusion `L^⋆ ⟶ 𝕃` over the base. -/
theorem Situation.laurentToTotalSpace_comp_totalToBase :
    D.laurentToTotalSpace ≫ D.totalToBase = D.laurentToBase ≫ 𝟙 D.S := by
  rw [Category.comp_id, Situation.totalToBase, ← Category.assoc,
    D.laurentToTotalSpace_comp_totalSpaceToBase]
  rfl

/-- **The restriction of forms from the total space to the complement of the zero section**,
`π_* Ω^p_{𝕃/S} ⟶ (L^⋆ → X)_* Ω^p_{L^⋆/S}`: the direct image along `π` of the canonical map of
forms of the square of the inclusion `L^⋆ ⟶ 𝕃` over `S`. -/
def Situation.formsRestrict (p : ℕ) :
    D.totalFormsPushforward p ⟶ D.gradedAmbient p :=
  (Scheme.Modules.pushforward D.totalSpaceToBase).map
      ((Scheme.Hom.deRhamFormsPushforwardHom D.laurentToTotalSpace D.totalToBase D.laurentToBase
        (𝟙 D.S) D.laurentToTotalSpace_comp_totalToBase).app (p : ℤ)) ≫
    (Scheme.Modules.pushforwardComp D.laurentToTotalSpace D.totalSpaceToBase).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr D.laurentToTotalSpace_comp_totalSpaceToBase).hom.app _

/-- The restriction of forms on sections over `W`, with its source seated at the forms on
`π⁻¹W`. -/
def Situation.restrictForms (p : ℕ) (W : D.X.Opens)
    (ω : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W)) : Γ(D.gradedAmbient p, W) :=
  (D.formsRestrict p).app W ω

/-- The restriction of forms on sections over `W` is additive. -/
theorem Situation.restrictForms_add (p : ℕ) (W : D.X.Opens)
    (ω χ : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W)) :
    D.restrictForms p W (ω + χ) = D.restrictForms p W ω + D.restrictForms p W χ :=
  map_add ((D.formsRestrict p).app W).hom ω χ

/-- The restriction of forms on sections over `W`, seated at the forms on `π⁻¹W` in `𝕃` and in
`L^⋆`. -/
def Situation.restrictFormsS (p : ℕ) (W : D.X.Opens)
    (ω : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W)) :
    Γ(Scheme.Hom.relativeDifferentialForms (D.laurentSpectrumToBase ≫ D.f) (p : ℤ),
      D.laurentSpectrumToBase ⁻¹ᵁ W) :=
  D.secG p W (D.restrictForms p W ω)

/-- The restriction of forms on sections over `W`, seated at the forms on `π⁻¹W` in `L^⋆`, is
additive. -/
theorem Situation.restrictFormsS_add (p : ℕ) (W : D.X.Opens)
    (ω χ : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W)) :
    D.restrictFormsS p W (ω + χ) = D.restrictFormsS p W ω + D.restrictFormsS p W χ :=
  (congrArg (D.secG p W) (D.restrictForms_add p W ω χ)).trans (map_add (D.secG p W) _ _)

/-- `secG` carries the restriction of forms to `restrictFormsS`. -/
theorem Situation.secG_restrictForms (p : ℕ) (W : D.X.Opens)
    (ω : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W)) :
    D.secG p W (D.restrictForms p W ω) = D.restrictFormsS p W ω :=
  (Situation.restrictFormsS.eq_1 D p W ω).symm

/-- The restriction of forms on sections over `W`, as an additive map. -/
def Situation.restrictFormsHom (p : ℕ) (W : D.X.Opens) :
    Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W) →+ Γ(D.gradedAmbient p, W) :=
  AddMonoidHom.mk' (D.restrictForms p W) (D.restrictForms_add p W)

/-- The additive map `restrictFormsHom` evaluates to `restrictForms`. -/
theorem Situation.restrictFormsHom_apply (p : ℕ) (W : D.X.Opens)
    (ω : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W)) :
    D.restrictFormsHom p W ω = D.restrictForms p W ω :=
  rfl

/-- The ring map `Γ(𝕃, π⁻¹W) ⟶ Γ(L^⋆, π⁻¹W)` of the inclusion `L^⋆ ⟶ 𝕃`, over an open `W` of
`X`. -/
def Situation.jSharp (W : D.X.Opens) :
    Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ W) ⟶
      Γ(D.laurentSpectrum, D.laurentSpectrumToBase ⁻¹ᵁ W) :=
  D.laurentToTotalSpace.appLE _ _ (D.laurentToTotalSpace_preimage W).ge

/-- The pullback of the homogeneous function of a section of `Symᵏ(L)` to `L^⋆` is the
homogeneous function of its image in `L^{⊗ k}`. -/
theorem Situation.jSharp_totalFunction (k : ℕ) (U : D.X.affineOpens)
    (x : (D.symmetricAlgebra.piece (k : ℤ)).val.obj (op U.1)) :
    (D.jSharp U.1).hom (D.totalFunction k U.1 x) =
      D.laurentFunction k U ((D.symmetricToLaurent.app (k : ℤ)).val.app (op U.1) x) := by
  refine (ConcreteCategory.congr_hom (D.laurentToTotalSpace_appLE U)
    (D.algebraSheafIncl k U.1 x)).trans ?_
  refine (congrArg (fun z => ((Stacks.RelativeSpec.universalAlgebraMap
    D.laurentRelativeSpecSituation).right.app (op U.1)).hom z)
    (D.algebraSheafToLaurent_incl k U.1 x)).trans ?_
  rw [Situation.laurentFunction, D.laurentSectionsIso_hom_eq]
  rfl

/-- **The restriction of forms on a multiple of an exact wedge**: `a₀ · d a₁ ∧ ⋯ ∧ d aₚ` on `π⁻¹W`
goes to `j^♯ a₀ · d (j^♯ a₁) ∧ ⋯ ∧ d (j^♯ aₚ)` on the inverse image of `W` in `L^⋆`. -/
theorem Situation.formsRestrict_smul_homogeneousProdLeft (p : ℕ) (W : D.X.Opens)
    (a : Fin (p + 1) → Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ W)) :
    id (α := Γ(D.laurentForms (p : ℤ), D.laurentSpectrumToBase ⁻¹ᵁ W))
      ((D.formsRestrict p).app W (a 0 • id (α := Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ W))
        ((Scheme.Hom.deRhamAlgebras D.totalToBase).exterior.toPresheafGradedAlgebra
          |>.homogeneousProdLeft
          (op (D.totalSpaceToBase ⁻¹ᵁ W)) p fun i =>
            SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.totalToBase) _ (a i.succ)))) =
      (D.jSharp W).hom (a 0) • id (α := Γ(D.laurentForms (p : ℤ), D.laurentSpectrumToBase ⁻¹ᵁ W))
        ((Scheme.Hom.deRhamAlgebras D.laurentToBase).exterior.toPresheafGradedAlgebra
          |>.homogeneousProdLeft
          (op (D.laurentSpectrumToBase ⁻¹ᵁ W)) p fun i =>
            SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.laurentToBase) _
              ((D.jSharp W).hom (a i.succ))) := by
  let g : op (D.laurentToTotalSpace ⁻¹ᵁ (D.totalSpaceToBase ⁻¹ᵁ W)) ⟶
      op (D.laurentSpectrumToBase ⁻¹ᵁ W) := (homOfLE (D.laurentToTotalSpace_preimage W).ge).op
  let Φ := (Scheme.Hom.deRhamFormsPushforwardHom D.laurentToTotalSpace D.totalToBase
      D.laurentToBase (𝟙 D.S) D.laurentToTotalSpace_comp_totalToBase).app (p : ℤ)
  have e0 : ∀ ω, (D.formsRestrict p).app W ω =
      ((Scheme.Modules.pushforwardCongr D.laurentToTotalSpace_comp_totalSpaceToBase).hom.app
        (D.laurentForms (p : ℤ))).app W
        (Scheme.Modules.Hom.app (X := D.totalSpace) Φ (D.totalSpaceToBase ⁻¹ᵁ W) ω) :=
    fun ω => rfl
  have e1 : ∀ ω, (D.formsRestrict p).app W ω =
      (D.laurentForms (p : ℤ)).val.map g (Φ.val.app (op (D.totalSpaceToBase ⁻¹ᵁ W)) ω) :=
    fun ω => by
      rw [e0, Scheme.Modules.pushforwardCongr_hom_app_app]
      exact congrArg (fun k => ((D.laurentForms (p : ℤ)).val.map k).hom
        (Φ.val.app (op (D.totalSpaceToBase ⁻¹ᵁ W)) ω)) (Subsingleton.elim _ _)
  have hsmul := Scheme.Hom.deRhamFormsPushforwardHom_smul D.laurentToTotalSpace D.totalToBase
      D.laurentToBase (𝟙 D.S) D.laurentToTotalSpace_comp_totalToBase (p : ℤ)
      (op (D.totalSpaceToBase ⁻¹ᵁ W)) (a 0)
      ((Scheme.Hom.deRhamAlgebras D.totalToBase).exterior.toPresheafGradedAlgebra
        |>.homogeneousProdLeft
          (op (D.totalSpaceToBase ⁻¹ᵁ W)) p fun i =>
            SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.totalToBase) _ (a i.succ))
  have hprod := Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft D.laurentToTotalSpace
      D.totalToBase D.laurentToBase (𝟙 D.S) D.laurentToTotalSpace_comp_totalToBase
      (op (D.totalSpaceToBase ⁻¹ᵁ W)) p fun i => a i.succ
  have hres : ∀ b : Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ W),
      D.laurentSpectrum.sheaf.obj.map g ((D.laurentToTotalSpace.app _).hom b) =
        (D.jSharp W).hom b := fun b => by
    rw [Situation.jSharp, Scheme.Hom.appLE]
    rfl
  refine (e1 _).trans ?_
  refine (congrArg _ hsmul).trans ?_
  refine (PresheafOfModules.map_smul (D.laurentForms (p : ℤ)).val g _ _).trans ?_
  refine congrArg₂ (· • ·) (hres (a 0)) ?_
  refine (congrArg _ hprod).trans ?_
  refine ((Scheme.Hom.deRhamAlgebras D.laurentToBase).exterior.toPresheafGradedAlgebra
    |>.homogeneousProdLeft_naturality g p _).trans ?_
  exact congrArg (fun z =>
    (Scheme.Hom.deRhamAlgebras D.laurentToBase).exterior.toPresheafGradedAlgebra
      |>.homogeneousProdLeft _ p z)
    (funext fun i => (AlgebraicGeometry.SheafOfModules.exactOne_map _ g _).trans
      (congrArg _ (hres (a i.succ))))

/-! ### Explicit homogeneous forms of `L^⋆` -/

/-- **An ordered product of differentials of homogeneous functions on `L^⋆` is homogeneous**, of
the sum of their degrees. -/
theorem Situation.isHomogeneousLaurentForm_homogeneousProd (U : D.X.affineOpens) :
    ∀ (p : ℕ) (deg : Fin p → ℤ) (x : ∀ i, Γ(D.tensorPower (deg i), U.1)),
      D.IsHomogeneousLaurentForm U p (∑ i, deg i)
        ((Scheme.Hom.deRhamAlgebras D.laurentToBase).exterior.toPresheafGradedAlgebra
          |>.homogeneousProd
          (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1)) p fun i =>
            SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.laurentToBase) _
              (D.laurentFunction (deg i) U (x i)))
  | 0, deg, x => by
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact D.isHomogeneousLaurentForm_gradedOne U
  | p + 1, deg, x => by
      rw [Fin.sum_univ_castSucc]
      exact D.isHomogeneousLaurentForm_gradedWedge p _ _ _ rfl U
        (Situation.isHomogeneousLaurentForm_homogeneousProd U p (fun i => deg i.castSucc)
          fun i => x i.castSucc) (x (Fin.last p))

/-- **A homogeneous function times an ordered product of differentials of homogeneous functions
on `L^⋆` is homogeneous**, of the sum of all the degrees. -/
theorem Situation.isHomogeneousLaurentForm_smul_homogeneousProdLeft (U : D.X.affineOpens)
    (p : ℕ) (deg : Fin (p + 1) → ℤ) (x : ∀ i, Γ(D.tensorPower (deg i), U.1)) :
    D.IsHomogeneousLaurentForm U p (∑ i, deg i)
      (id (α := Γ(D.laurentSpectrum, D.laurentSpectrumToBase ⁻¹ᵁ U.1))
        (D.laurentFunction (deg 0) U (x 0)) • id (α := Γ(D.laurentForms (p : ℤ),
        D.laurentSpectrumToBase ⁻¹ᵁ U.1))
        ((Scheme.Hom.deRhamAlgebras D.laurentToBase).exterior.toPresheafGradedAlgebra
          |>.homogeneousProdLeft
          (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1)) p fun i =>
            SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.laurentToBase) _
              (D.laurentFunction (deg i.succ) U (x i.succ)))) := by
  rw [Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd, Fin.sum_univ_succ]
  exact D.isHomogeneousLaurentForm_gradedSmul p (deg 0) _ _ rfl U (x 0)
    (D.isHomogeneousLaurentForm_homogeneousProd U p (fun i => deg i.succ)
      fun i => x i.succ)

/-! ### The restriction of forms preserves the degree -/

/-- **Over an affine open the restriction of a homogeneous form of degree `n` on the total space is
a section of `Ω^p_{L^⋆/S, n}`.** -/
theorem Situation.formsRestrict_mem_of_isHomogeneousTotalForm (U : D.X.affineOpens) {p n : ℕ}
    {ω : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ U.1)}
    (hω : D.IsHomogeneousTotalForm U.1 p n ω) :
    (D.formsRestrict p).app U.1 ω ∈ (D.gradedLaurentForms p (n : ℤ)).obj (op U.1) := by
  obtain ⟨deg, a, ha, hn, rfl⟩ := hω
  choose x hx using ha
  obtain rfl : a = fun i => D.totalFunction (deg i) U.1 (x i) := funext fun i => (hx i).symm
  have h := D.formsRestrict_smul_homogeneousProdLeft p U.1 fun i =>
    D.totalFunction (deg i) U.1 (x i)
  simp only [D.jSharp_totalFunction] at h
  have hn' : (n : ℤ) = ∑ i, ((deg i : ℕ) : ℤ) := by
    rw [hn]
    push_cast
    rfl
  have hhom := D.isHomogeneousLaurentForm_smul_homogeneousProdLeft U p (fun i => (deg i : ℤ))
    fun i => (D.symmetricToLaurent.app (deg i : ℤ)).val.app (op U.1) (x i)
  rw [← hn'] at hhom
  exact (congrArg (· ∈ (D.gradedLaurentForms p (n : ℤ)).obj (op U.1)) h).mpr
    (D.mem_gradedLaurentForms U hhom)

/-- **Membership in a submodule sheaf of a module on a scheme may be tested on affine opens.** -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.mem_of_forall_affineOpen {Y : Scheme.{u}}
    {M : Y.Modules} (N : M.Submodule) {W : Y.Opens} (s : Γ(M, W))
    (h : ∀ (U : Y.Opens) (hUW : U ≤ W), IsAffineOpen U →
      M.val.map (homOfLE hUW).op s ∈ N.obj (op U)) :
    s ∈ N.obj (op W) := by
  refine N.isSheaf s fun x hx => ?_
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hx
  exact ⟨U, homOfLE hUW, h U hUW hU, hxU⟩

/-- **The restriction of forms carries `Ω^p_{𝕃/S, n}` into `Ω^p_{L^⋆/S, n}`.** -/
theorem Situation.gradedTotalForms_le_comap (p n : ℕ) :
    D.gradedTotalForms p n ≤
      SheafOfModules.Submodule.comap (D.formsRestrict p) (D.gradedLaurentForms p (n : ℤ)) := by
  refine (D.gradedTotalForms_le_iff _).2 fun W ω hω => ?_
  refine (SheafOfModules.Submodule.mem_comap _ _ _).2 ?_
  refine Scheme.Modules.mem_of_forall_affineOpen _ _ fun U hUW hU => ?_
  have h := PresheafOfModules.naturality_apply (D.formsRestrict p).val (homOfLE hUW).op ω
  refine (congrArg (· ∈ (D.gradedLaurentForms p (n : ℤ)).obj (op U)) h).mp ?_
  exact D.formsRestrict_mem_of_isHomogeneousTotalForm ⟨U, hU⟩
    (Situation.IsHomogeneousTotalForm.map D hUW hω)

/-! ### The polynomial chart and the Laurent chart -/

/-- Equal morphisms of schemes have equal restricted section maps. -/
theorem Situation.appLE_congr {Y Z : Scheme.{u}} {g g' : Y ⟶ Z} (h : g = g') {U : Z.Opens}
    {V : Y.Opens} (e : V ≤ g ⁻¹ᵁ U) (e' : V ≤ g' ⁻¹ᵁ U) : g.appLE U V e = g'.appLE U V e' := by
  subst h
  rfl

/-- The ring map of the inclusion `L^⋆ ⟶ 𝕃` carries a function pulled back from `X` to its
pullback to `L^⋆`. -/
theorem Situation.jSharp_app (W : D.X.Opens) (r : Γ(D.X, W)) :
    (D.jSharp W).hom ((D.totalSpaceToBase.app W).hom r) =
      (D.laurentSpectrumToBase.app W).hom r := by
  rw [Situation.jSharp, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
  exact congrArg (fun k => (CommRingCat.Hom.hom k) r)
    (Situation.appLE_congr D.laurentToTotalSpace_comp_totalSpaceToBase _ _)

/-- A Laurent chart carries the constants to the functions pulled back from `X`. -/
theorem Situation.LaurentChart.sectionsRingEquiv_C {U : D.X.affineOpens} (lc : D.LaurentChart U.1)
    (r : Γ(D.X, U.1)) :
    lc.sectionsRingEquiv (LaurentPolynomial.C r) = (D.laurentSpectrumToBase.app U.1).hom r := by
  rw [Situation.LaurentChart.sectionsRingEquiv_apply, Situation.LaurentChart.hom_C,
    D.laurentSectionsIso_hom_laurentStructureHom]

/-- A Laurent chart carries `T` to the function of its generator. -/
theorem Situation.LaurentChart.sectionsRingEquiv_T_one {U : D.X.affineOpens}
    (lc : D.LaurentChart U.1) :
    lc.sectionsRingEquiv (LaurentPolynomial.T 1) = D.laurentFunction 1 U lc.gen := by
  rw [Situation.LaurentChart.sectionsRingEquiv_apply, Situation.LaurentChart.hom_T, zpow_one]
  rfl

namespace Situation.TotalChart

variable {D} (c : D.TotalChart)

/-- The Laurent chart of `L^⋆` over `U` given by the trivialization of the chart. -/
abbrev laurentChart : D.LaurentChart c.U.1 := Situation.LaurentChart.ofTrivialization c.triv

/-- **The fibre coordinate of the polynomial model restricts to the coordinate of the Laurent
chart**: the variable `X` of `Γ(X, U)[X] ≅ Γ(𝕃, π⁻¹U)` is carried by `j^♯` to the homogeneous
function of the generator of the Laurent chart. -/
theorem jSharp_equiv_X :
    (D.jSharp c.U.1).hom (c.equiv Polynomial.X) = D.laurentFunction 1 c.U c.laurentChart.gen := by
  have hX : (D.polynomialAlgEquiv c.U c.basis).symm Polynomial.X =
      SymmetricAlgebra.ι Γ(D.X, c.U.1) Γ(D.L, c.U.1) (c.basis PUnit.unit) := by
    rw [AlgEquiv.symm_apply_eq, D.polynomialAlgEquiv_ι]
  have hmem : SymmetricAlgebra.ι Γ(D.X, c.U.1) Γ(D.L, c.U.1) (c.basis PUnit.unit) ∈
      SymPow.symmetricPower 1 Γ(D.X, c.U.1) Γ(D.L, c.U.1) := by
    rw [SymPow.symmetricPower, pow_one]
    exact LinearMap.mem_range_self _ _
  have h1 : c.equiv Polynomial.X = D.totalFunction 1 c.U.1
      (Stacks.SymAlgSections.pieceUnit D.L c.U.2 1 ⟨_, hmem⟩) := by
    show D.symSectionsRingEquiv c.U ((D.polynomialAlgEquiv c.U c.basis).symm Polynomial.X) = _
    rw [hX]
    exact D.symSectionsRingEquiv_coe c.U 1 ⟨_, hmem⟩
  have h2 : Stacks.SymAlgSections.pieceUnit D.L c.U.2 1 ⟨_, hmem⟩ =
      (D.symmetricAlgebraGen.val.app (op c.U.1)) (c.basis PUnit.unit) :=
    (Stacks.SymGraded.AffinePieces.symmetricAlgebraGen_app_eq D.L c.U.1 _).symm
  rw [h1, h2, D.jSharp_totalFunction]
  congr 1
  have h3 := congrArg (fun φ => φ.val.app (op c.U.1) (c.basis PUnit.unit))
    D.symmetricAlgebraGen_comp_symmetricToLaurent
  refine h3.trans ?_
  have hb : c.basis PUnit.unit = Stacks.SheafOfModules.TensorGenerator.generator D.X.sheaf.obj
      D.X.ringCatSheaf.property c.U.1 D.L c.triv := by
    rw [Situation.TotalChart.basis, Situation.trivializationBasis, Module.Basis.map_apply,
      Module.Basis.singleton_apply]
    rfl
  rw [hb]
  rfl

attribute [local instance] Situation.AffineChart.algebraRA algebraRB algebraAB isScalarTower

/-- The chart of `L^⋆` over `U` attached to a chart of the total space. -/
abbrev baseChart : D.BaseChart := ⟨c.toAffineChart, c.laurentChart⟩

/-- `Γ(L^⋆, π⁻¹U)` as a `Γ(S, V)`-algebra. -/
abbrev algebraRBs : Algebra c.R c.baseChart.B := Situation.BaseChart.algebraRB c.baseChart

/-- `Γ(L^⋆, π⁻¹U)` as a `Γ(X, U)`-algebra. -/
abbrev algebraABs : Algebra c.A c.baseChart.B := Situation.BaseChart.algebraAB c.baseChart

attribute [local instance] algebraRBs algebraABs

/-- The scalar tower `Γ(S, V) → Γ(X, U) → Γ(L^⋆, π⁻¹U)`. -/
theorem isScalarTower_RABs : IsScalarTower c.R c.A c.baseChart.B :=
  Situation.BaseChart.isScalarTower c.baseChart

attribute [local instance] isScalarTower_RABs

/-- `Γ(L^⋆, π⁻¹U)` as a `Γ(𝕃, π⁻¹U)`-algebra, along the inclusion `L^⋆ ⟶ 𝕃`. -/
abbrev algebraBBs : Algebra c.B c.baseChart.B := (D.jSharp c.U.1).hom.toAlgebra

attribute [local instance] algebraBBs

/-- The scalar tower `Γ(X, U) → Γ(𝕃, π⁻¹U) → Γ(L^⋆, π⁻¹U)`. -/
theorem isScalarTower_ABBs : IsScalarTower c.A c.B c.baseChart.B :=
  IsScalarTower.of_algebraMap_eq fun r => (D.jSharp_app c.U.1 r).symm

/-- The scalar tower `Γ(S, V) → Γ(𝕃, π⁻¹U) → Γ(L^⋆, π⁻¹U)`. -/
theorem isScalarTower_RBBs : IsScalarTower c.R c.B c.baseChart.B :=
  IsScalarTower.of_algebraMap_eq fun r => by
    show ((D.laurentSpectrumToBase ≫ D.f).appLE c.V.1 _ c.baseChart.preimage_le).hom r =
      (D.jSharp c.U.1).hom ((D.totalToBase.appLE c.V.1 _ c.preimage_le).hom r)
    rw [Situation.jSharp, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun k => (CommRingCat.Hom.hom k) r)
      (Situation.appLE_congr (by
        rw [Situation.totalToBase, ← Category.assoc,
          D.laurentToTotalSpace_comp_totalSpaceToBase]) _ _)

attribute [local instance] isScalarTower_ABBs isScalarTower_RBBs

/-- **The square of the two affine local models**: the inclusion `L^⋆ ⟶ 𝕃` is, on the chart,
the inclusion `Γ(X, U)[X] → Γ(X, U)[T;T⁻¹]`. -/
theorem jSharp_equiv (q : c.A[X]) :
    algebraMap c.B c.baseChart.B (c.equiv q) = c.baseChart.equiv (Polynomial.toLaurent q) := by
  have h : (algebraMap c.B c.baseChart.B).comp c.equiv.toRingHom =
      c.baseChart.equiv.toRingHom.comp (Polynomial.toLaurent (R := c.A)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show (D.jSharp c.U.1).hom (c.equiv (Polynomial.C a)) =
        c.laurentChart.sectionsRingEquiv (Polynomial.toLaurent (Polynomial.C a))
      rw [Polynomial.toLaurent_C, Situation.LaurentChart.sectionsRingEquiv_C]
      show (D.jSharp c.U.1).hom (D.polynomialSectionsRingEquiv c.U c.basis (Polynomial.C a)) = _
      rw [D.polynomialSectionsRingEquiv_C, D.jSharp_app]
    · show (D.jSharp c.U.1).hom (c.equiv Polynomial.X) =
        c.laurentChart.sectionsRingEquiv (Polynomial.toLaurent Polynomial.X)
      rw [c.jSharp_equiv_X, Polynomial.toLaurent_X, Situation.LaurentChart.sectionsRingEquiv_T_one]
  exact congrArg (fun k => k q) h

/-- The forms of `L^⋆` over the chart as Kähler forms, at the open `U` of the chart of `𝕃`. -/
abbrev formsLs (p : ℕ) :
    ModuleCat.of c.baseChart.B Γ(Scheme.Hom.relativeDifferentialForms
        (D.laurentSpectrumToBase ≫ D.f) (p : ℤ), D.laurentSpectrumToBase ⁻¹ᵁ c.U.1) ≅
      ModuleCat.of c.baseChart.B (⋀[c.baseChart.B]^p c.baseChart.ΩB) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso (D.laurentSpectrumToBase ≫ D.f)
    (D.isAffineOpen_laurentPreimage c.U.2) c.V.2 c.baseChart.preimage_le p

/-- `formsLs` agrees with the identification `formsL` of the Laurent chart. -/
theorem formsLs_eq (p : ℕ) : c.formsLs p = c.baseChart.formsL p := rfl

/-- The restriction of forms on a generator `a₀ · d a₁ ∧ ⋯ ∧ d aₚ`, through the chart
identifications. -/
theorem formsLs_restrictForms_gen (p : ℕ) (a : Fin (p + 1) → c.B) :
    (c.formsLs p).hom (D.restrictFormsS p c.U.1 ((c.formsL p).inv
      (a 0 • exteriorPower.ιMulti c.B p fun i => CommRingCat.KaehlerDifferential.d (a i.succ)))) =
      KaehlerDifferential.mapExteriorPower c.R c.B c.baseChart.B p
        (a 0 • exteriorPower.ιMulti c.B p fun i =>
          (CommRingCat.KaehlerDifferential.d (a i.succ) : c.ΩB)) := by
  refine Eq.trans ?_
    (KaehlerDifferential.mapExteriorPower_smul_ιMulti_D c.R c.B c.baseChart.B p a).symm
  have h1 := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_smul_homogeneousProdLeft
    D.totalToBase c.isAffineOpen_preimage c.V.2 c.preimage_le p (a 0) fun i => a i.succ
  have h1' : (c.formsL p).inv (a 0 • exteriorPower.ιMulti c.B p fun i =>
      CommRingCat.KaehlerDifferential.d (a i.succ)) =
      a 0 • id (α := Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ c.U.1))
        ((Scheme.Hom.deRhamAlgebras D.totalToBase).exterior.toPresheafGradedAlgebra
          |>.homogeneousProdLeft
          (op (D.totalSpaceToBase ⁻¹ᵁ c.U.1)) p fun i =>
            SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras D.totalToBase) _ (a i.succ)) := by
    rw [← h1]
    exact Iso.hom_inv_id_apply _ _
  rw [h1', Situation.restrictFormsS, Situation.restrictForms]
  have h3 := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_smul_homogeneousProdLeft
    (D.laurentSpectrumToBase ≫ D.f) (D.isAffineOpen_laurentPreimage c.U.2) c.V.2
    c.baseChart.preimage_le p ((D.jSharp c.U.1).hom (a 0)) fun i => (D.jSharp c.U.1).hom (a i.succ)
  refine (congrArg (c.formsLs p).hom ?_).trans h3
  exact D.formsRestrict_smul_homogeneousProdLeft p c.U.1 a

/-- **On a chart, the restriction of forms from `𝕃` to `L^⋆`, read through the identifications of
both sides with Kähler forms, is the restriction of Kähler forms along `j^♯`.** -/
theorem formsLs_restrictFormsS (p : ℕ) (x : ⋀[c.B]^p c.ΩB) :
    (c.formsLs p).hom (D.restrictFormsS p c.U.1 ((c.formsL p).inv x)) =
      KaehlerDifferential.mapExteriorPower c.R c.B c.baseChart.B p x := by
  let F : ⋀[c.B]^p c.ΩB →+ ⋀[c.baseChart.B]^p c.baseChart.ΩB :=
    AddMonoidHom.mk' (fun x => (c.formsLs p).hom (D.restrictFormsS p c.U.1 ((c.formsL p).inv x)))
      fun x y => by rw [map_add, Situation.restrictFormsS_add, map_add]
  let G : ⋀[c.B]^p c.ΩB →+ ⋀[c.baseChart.B]^p c.baseChart.ΩB :=
    AddMonoidHom.mk' (KaehlerDifferential.mapExteriorPower c.R c.B c.baseChart.B p) (map_add _)
  have hD : Submodule.span c.B
      (Set.range fun b : c.B => (CommRingCat.KaehlerDifferential.d b : c.ΩB)) = ⊤ :=
    @KaehlerDifferential.span_range_derivation c.R c.B _ _ c.algebraRB
  have key : F = G := Stacks.AlgebraicGeometry.AffineOpenDeRham.addMonoidHom_ext_of_span_int_eq_top
    (Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ)
      (fun b : c.B => (CommRingCat.KaehlerDifferential.d b : c.ΩB)) hD p) (by
        rintro _ ⟨a, rfl⟩
        simp only [F, G, AddMonoidHom.mk'_apply]
        beta_reduce
        rw [c.formsLs_restrictForms_gen p a]
        rfl)
  exact DFunLike.congr_fun key x

/-- The Kähler form of a section of `(L^⋆ → X)_* Ω^p_{L^⋆/S}` over the chart, through the forms of
`L^⋆` at the open `U` of the chart of `𝕃`. -/
def formsLFs (p : ℕ) (η : Γ(D.gradedAmbient p, c.U.1)) :=
  c.baseChart.toΩB p ((c.formsLs p).hom (D.secG p c.U.1 η))

/-- `formsLF` of the Laurent chart agrees with `formsLFs`. -/
theorem formsLF_eq_formsLFs (p : ℕ) (η : Γ(D.gradedAmbient p, c.U.1)) :
    c.baseChart.formsLF p η = c.formsLFs p η := by
  rw [Situation.BaseChart.formsLF_apply, formsLFs]

/-- The map `formsLFs` is injective. -/
theorem formsLFs_injective (p : ℕ) : Function.Injective (c.formsLFs p) :=
  (c.baseChart.toΩB p).injective.comp
    ((c.formsLs p).toLinearEquiv.injective.comp (D.secG p c.U.1).injective)

/-- The map `formsLFs` sends zero to zero. -/
theorem formsLFs_zero (p : ℕ) : c.formsLFs p 0 = 0 := by
  rw [formsLFs, map_zero, map_zero]
  exact (c.baseChart.toΩB p).map_zero

/-- **Over a chart the restriction of forms from `𝕃` to `L^⋆` is the map of Kähler forms along
`A[X] → A[T, T⁻¹]`.** -/
theorem formsLFs_restrictForms (p : ℕ) (z : ⋀[c.B]^p Ω[c.B⁄c.R]) :
    c.formsLFs p (D.restrictForms p c.U.1 ((c.formsLK p).symm z)) =
      KaehlerDifferential.mapExteriorPower c.R c.B c.baseChart.B p z := by
  rw [formsLFs, D.secG_restrictForms]
  have hK := c.formsLs_restrictFormsS p ((c.toΩB p).symm z)
  have e1 : (c.formsL p).inv ((c.toΩB p).symm z) = (c.formsLK p).symm z := rfl
  rw [e1] at hK
  have e4 : c.baseChart.toΩB p (KaehlerDifferential.mapExteriorPower c.R c.B c.baseChart.B p
      ((c.toΩB p).symm z)) = KaehlerDifferential.mapExteriorPower c.R c.B c.baseChart.B p z := rfl
  exact (congrArg (c.baseChart.toΩB p) hK).trans e4

/-- **Over a chart, every section of `Ω^p_{L^⋆/S, n}` with `n > 0` is the restriction of a section
of `Ω^p_{𝕃/S, n}`.** -/
theorem exists_restrictForms_eq {p n : ℕ} (hn : 0 < n) {ω : Γ(D.gradedAmbient p, c.U.1)}
    (hω : ω ∈ (D.gradedLaurentForms p (n : ℤ)).obj (op c.U.1)) :
    ∃ x : Γ(D.totalForms p, D.totalSpaceToBase ⁻¹ᵁ c.U.1),
      D.ofForms p c.U.1 x ∈ (D.gradedTotalForms p n).obj (op c.U.1) ∧
        D.restrictForms p c.U.1 x = ω := by
  have hmem := c.baseChart.formsLF_mem_of_mem hω
  rw [← (LaurentDeRham.transport_weightComparison (R := c.R) c.equiv c.baseChart.equiv
    c.jSharp_equiv n p hn).1] at hmem
  obtain ⟨z, hz, hzω⟩ := hmem
  refine ⟨(c.formsLK p).symm z, c.formsLK_symm_mem_of_mem hz, c.formsLFs_injective p ?_⟩
  exact (c.formsLFs_restrictForms p z).trans (hzω.trans (c.formsLF_eq_formsLFs p ω))

/-- **Over a chart, a combination of homogeneous forms of degree `n > 0` on `𝕃` which vanishes on
`L^⋆` is zero.** -/
theorem eq_zero_of_formsRestrict_eq_zero {p n : ℕ} (hn : 0 < n)
    {x : (D.totalFormsPushforward p).val.obj (op c.U.1)} (hx : x ∈ D.homogeneousSpan p n c.U.1)
    (h : (D.formsRestrict p).val.app (op c.U.1) x = 0) : x = 0 := by
  have h0 : D.restrictForms p c.U.1 (D.toForms p c.U.1 x) = 0 := h
  have hmem := c.formsLF_mem_of_mem_homogeneousSpan hx
  have h1 : c.formsLF p x = c.formsLK p (D.toForms p c.U.1 x) := rfl
  have hz := c.formsLFs_restrictForms p (c.formsLK p (D.toForms p c.U.1 x))
  rw [LinearEquiv.symm_apply_apply, h0, formsLFs_zero] at hz
  have h3 : c.formsLF p x = 0 :=
    (LaurentDeRham.transport_weightComparison (R := c.R) c.equiv c.baseChart.equiv
      c.jSharp_equiv n p hn).2 _ hmem (h1 ▸ hz.symm)
  have h4 : c.formsLK p (D.toForms p c.U.1 x) = 0 := h1 ▸ h3
  have h5 : D.toForms p c.U.1 x = 0 :=
    ((c.formsLK p).symm_apply_apply _).symm.trans
      ((congrArg (c.formsLK p).symm h4).trans (map_zero _))
  exact h5

end Situation.TotalChart

/-! ### The global comparison in positive weight -/

/-- **The restriction of forms is injective on `Ω^p_{𝕃/S, n}` for `n > 0`.** -/
theorem Situation.eq_zero_of_formsRestrict_eq_zero {p n : ℕ} (hn : 0 < n) {W : D.X.Opens}
    {x : (D.totalFormsPushforward p).val.obj (op W)} (hx : x ∈ (D.gradedTotalForms p n).obj (op W))
    (h : (D.formsRestrict p).val.app (op W) x = 0) : x = 0 := by
  have hmem : x ∈ (_root_.SheafOfModules.Submodule.ker (𝟙 (D.totalFormsPushforward p))).obj
      (op W) := by
    refine (_root_.SheafOfModules.Submodule.ker _).isSheaf x fun y hy => ?_
    obtain ⟨U, V, hUW, hyU, hU, hV, e, ⟨t⟩, hspan⟩ := D.exists_chart_mem_homogeneousSpan hx hy
    let c : D.TotalChart := ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, e⟩, t⟩
    refine ⟨U, homOfLE hUW, ?_, hyU⟩
    refine (_root_.SheafOfModules.Submodule.mem_ker _ _ _).2 ?_
    have hφ := PresheafOfModules.naturality_apply (D.formsRestrict p).val (homOfLE hUW).op x
    have h0 : (D.formsRestrict p).val.app (op c.U.1)
        ((D.totalFormsPushforward p).val.map (homOfLE hUW).op x) = 0 :=
      hφ.trans ((congrArg _ h).trans (map_zero _))
    exact c.eq_zero_of_formsRestrict_eq_zero hn hspan h0
  exact (_root_.SheafOfModules.Submodule.mem_ker _ _ _).1 hmem

/-- **The restriction of forms on the weight-`n` part**,
`Ω^p_{𝕃/S, n} ⟶ (L^⋆ → X)_* Ω^p_{L^⋆/S}`. -/
def Situation.gradedFormsRestrict (p n : ℕ) :
    (D.gradedTotalForms p n).toSheafOfModules ⟶ D.gradedAmbient p :=
  (D.gradedTotalForms p n).ι ≫ D.formsRestrict p

/-- The restriction of forms on the weight-`n` part is the restriction of forms on the underlying
section. -/
theorem Situation.gradedFormsRestrict_app (p n : ℕ) (X : D.X.Opensᵒᵖ)
    (a : (D.gradedTotalForms p n).toSheafOfModules.val.obj X) :
    (D.gradedFormsRestrict p n).val.app X a = (D.formsRestrict p).val.app X a.1 :=
  rfl

/-- **The restriction of forms is injective on `Ω^p_{𝕃/S, n}` for `n > 0`**, on sections. -/
theorem Situation.injective_gradedFormsRestrict_app {p n : ℕ} (hn : 0 < n) (X : D.X.Opensᵒᵖ) :
    Function.Injective ((D.gradedFormsRestrict p n).val.app X) := by
  intro a b hab
  have hsub : (D.formsRestrict p).val.app X (a.1 - b.1) = 0 :=
    (map_sub ((D.formsRestrict p).val.app X).hom a.1 b.1).trans (sub_eq_zero.2
      (((D.gradedFormsRestrict_app p n X a).symm.trans hab).trans
        (D.gradedFormsRestrict_app p n X b)))
  exact Subtype.ext (sub_eq_zero.1 (D.eq_zero_of_formsRestrict_eq_zero hn (W := X.unop)
    (Submodule.sub_mem _ a.2 b.2) hsub))

/-- **The restriction of forms on `Ω^p_{𝕃/S, n}`, `n > 0`, is a monomorphism.** -/
theorem Situation.mono_gradedFormsRestrict {p n : ℕ} (hn : 0 < n) :
    Mono (D.gradedFormsRestrict p n) where
  right_cancellation g h H := by
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
    ext z
    exact D.injective_gradedFormsRestrict_app hn U (congrArg (fun k => k.val.app U z) H)

/-- **The image of `Ω^p_{𝕃/S, n}` under the restriction of forms is `Ω^p_{L^⋆/S, n}`, for
`n > 0`.** -/
theorem Situation.imageSubmodule_gradedFormsRestrict {p n : ℕ} (hn : 0 < n) :
    Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (D.gradedFormsRestrict p n) =
      D.gradedLaurentForms p (n : ℤ) := by
  refine le_antisymm (fun X s hs => ?_) (fun X s hs => ?_)
  · refine (D.gradedLaurentForms p (n : ℤ)).isSheaf s
      (GrothendieckTopology.superset_covering _ (fun V g hg => ?_) hs)
    obtain ⟨m, hm⟩ := hg
    have h := D.gradedTotalForms_le_comap p n (op V) m.2
    exact (congrArg (· ∈ (D.gradedLaurentForms p (n : ℤ)).obj (op V)) hm).mp h
  · obtain ⟨W⟩ := X
    refine D.mem_of_forall_chart (M := D.gradedAmbient p) _ (W := W) s
      fun U V hUW hU hV e ⟨t⟩ => ?_
    let c : D.TotalChart := ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, e⟩, t⟩
    have hω : (D.gradedAmbient p).val.map (homOfLE hUW).op s ∈
        (D.gradedLaurentForms p (n : ℤ)).obj (op c.U.1) :=
      (D.gradedLaurentForms p (n : ℤ)).map (homOfLE hUW).op hs
    obtain ⟨x, hx, hxω⟩ := c.exists_restrictForms_eq hn hω
    have hm := Stacks.SheafOfModules.ImageSubsheaf.apply_mem_imageSubmodule
      (D.gradedFormsRestrict p n) (X := op c.U.1) ⟨D.ofForms p c.U.1 x, hx⟩
    exact (congrArg (· ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule
      (D.gradedFormsRestrict p n)).obj (op U)) hxω).mp hm

/-- For `n > 0` and `p ≥ 0`, the weight-`n` part of the pushed-forward relative `p`-forms of the
total space `𝕃` of `L` over `S` is the weight-`n` part of the pushed-forward relative `p`-forms of
`L^⋆` over `S`: `Ω^p_{𝕃/S, n} ≅ Ω^p_{L^⋆/S, n}`, through the restriction of forms along `L^⋆ ⊆ 𝕃`.

The printed statement reads `Ω^p_{L/X, n}`, a misprint for `Ω^p_{L/S, n}`: the forms relative to
`X` satisfy `Ω^p_{L/X, n} = 0` for `p ≥ 2` while `Ω^p_{L^⋆/S, n}` is in general nonzero, and the
use of this lemma in the proof of Tag 0FUK concerns the forms relative to `S`. -/
@[stacks 0FUH "clause (3): for `n > 0`, `Ω^p_{L/S, n} = Ω^p_{L^⋆/S, n}` (printed `L/X`, a misprint
for `L/S`)"]
def Situation.gradedFormsIsoLaurent (p : ℕ) {n : ℕ} (hn : 0 < n) :
    (D.gradedTotalForms p n).toSheafOfModules ≅
      (D.gradedLaurentForms p (n : ℤ)).toSheafOfModules :=
  have : @Mono (_root_.SheafOfModules.{u} D.X.ringCatSheaf) _ _ _ (D.gradedFormsRestrict p n) :=
    D.mono_gradedFormsRestrict hn
  Stacks.SheafOfModules.ImageSubsheaf.imageIso (D.gradedFormsRestrict p n) ≪≫
    eqToIso (congrArg _root_.SheafOfModules.Submodule.toSheafOfModules
      (D.imageSubmodule_gradedFormsRestrict hn))

/-- **The identification `Ω^p_{𝕃/S, n} ≅ Ω^p_{L^⋆/S, n}` is the restriction of forms.** -/
theorem Situation.gradedFormsIsoLaurent_hom_ι (p : ℕ) {n : ℕ} (hn : 0 < n) :
    (D.gradedFormsIsoLaurent p hn).hom ≫ (D.gradedLaurentForms p (n : ℤ)).ι =
      (D.gradedTotalForms p n).ι ≫ D.formsRestrict p := by
  have : @Mono (_root_.SheafOfModules.{u} D.X.ringCatSheaf) _ _ _ (D.gradedFormsRestrict p n) :=
    D.mono_gradedFormsRestrict hn
  have h := SheafOfModules.Submodule.eqToHom_ι (D.imageSubmodule_gradedFormsRestrict (p := p) hn)
  have h' := Stacks.SheafOfModules.ImageSubsheaf.toImage_ι (D.gradedFormsRestrict p n)
  exact (Category.assoc _ _ _).trans ((congrArg (fun k =>
    Stacks.SheafOfModules.ImageSubsheaf.toImage
      (D.gradedFormsRestrict p n) ≫ k) h).trans h')

end Stacks.LineBundle

end
