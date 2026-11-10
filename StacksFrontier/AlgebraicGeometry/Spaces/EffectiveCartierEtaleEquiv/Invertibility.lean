module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.LocalRing.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FibrePrincipalDictionary
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.InvertibleRankOneEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv.ChartConditions

/-!
# The chart conditions of Stacks 083C imply invertibility

Principal ideal sheaves on a scheme flat over an affine scheme and the trivialization of the
defining ideal sheaf on étale charts, which the implications from conditions (2), (3) and (4) of
Stacks 083C to condition (1) in `StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv`
use.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace Stacks.Divisors

universe u

/-! ### Principal ideal sheaves on a scheme flat over an affine scheme -/

/-- **A global function which is a nonzerodivisor near every point is a nonzerodivisor.** Being
killed by multiplication is a local condition, so an open cover of the scheme on whose members
the function restricts to a nonzerodivisor forces it to be one. -/
theorem mem_nonZeroDivisors_of_forall_exists_mem {Y : Scheme.{u}} (f : Γ(Y, ⊤))
    (h : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op f ∈ nonZeroDivisors Γ(Y, V)) :
    f ∈ nonZeroDivisors Γ(Y, ⊤) := by
  choose V hmem hnzd using h
  have hcover : (⊤ : Y.Opens) ≤ iSup V :=
    fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hmem y⟩
  have key : ∀ r : Γ(Y, ⊤), r * f = 0 → r = 0 := by
    intro r hr
    refine eq_of_locally_eq V ⊤ (fun y => homOfLE (le_top : V y ≤ ⊤)) hcover r 0 fun y => ?_
    rw [map_zero]
    refine (mul_right_mem_nonZeroDivisors_eq_zero_iff (hnzd y)).1 ?_
    rw [← map_mul, hr, map_zero]
  exact mem_nonZeroDivisors_iff.2 ⟨fun r hr => key r (by rw [mul_comm]; exact hr), key⟩

/-- Restricting a regular function killed by pullback along a morphism of schemes keeps it
killed. -/
theorem app_res_eq_zero {Z Y : Scheme.{u}} (j : Z ⟶ Y) {W W' : Y.Opens} (hle : W' ≤ W)
    {r : Γ(Y, W)} (hr : (j.app W).hom r = 0) :
    (j.app W').hom (Y.presheaf.map (homOfLE hle).op r) = 0 := by
  have hnat := ConcreteCategory.congr_hom (j.naturality (homOfLE hle).op) r
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hr, map_zero] at hnat
  exact hnat

/-- **A global function killed by a quasi-compact morphism is a multiple of a global function
generating its kernel near every point.** On each affine open of the cover the function is a
multiple of the restricted generator, uniquely so because the generator is a nonzerodivisor
there, and the quotients therefore glue. -/
theorem exists_mul_of_appTop_eq_zero {Z Y : Scheme.{u}} (j : Z ⟶ Y) [QuasiCompact j]
    (f : Γ(Y, ⊤))
    (h : ∀ y : Y, ∃ A : Y.affineOpens, y ∈ (A.1 : Set Y) ∧
      j.ker.ideal A = Ideal.span {Y.presheaf.map (homOfLE (le_top : A.1 ≤ ⊤)).op f} ∧
      Y.presheaf.map (homOfLE (le_top : A.1 ≤ ⊤)).op f ∈ nonZeroDivisors Γ(Y, A.1))
    (r : Γ(Y, ⊤)) (hr : j.appTop.hom r = 0) :
    ∃ c : Γ(Y, ⊤), r = c * f := by
  choose A hmem hgen hnzd using h
  have hcover : (⊤ : Y.Opens) ≤ iSup fun y => (A y).1 :=
    fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hmem y⟩
  have hdiv : ∀ y : Y, ∃ c : Γ(Y, (A y).1),
      Y.presheaf.map (homOfLE (le_top : (A y).1 ≤ ⊤)).op r =
        c * Y.presheaf.map (homOfLE (le_top : (A y).1 ≤ ⊤)).op f := by
    intro y
    have h0 : Y.presheaf.map (homOfLE (le_top : (A y).1 ≤ ⊤)).op r ∈ j.ker.ideal (A y) := by
      rw [Scheme.Hom.ker_apply]
      exact app_res_eq_zero j le_top hr
    rw [hgen y, Ideal.mem_span_singleton'] at h0
    obtain ⟨c, hc⟩ := h0
    exact ⟨c, hc.symm⟩
  choose c hc using hdiv
  have key : ∀ (y : Y) (O : Y.Opens) (i : O ⟶ (A y).1),
      Y.presheaf.map i.op (c y) *
          Y.presheaf.map (homOfLE (i.le.trans (le_top : (A y).1 ≤ ⊤))).op f =
        Y.presheaf.map (homOfLE (i.le.trans (le_top : (A y).1 ≤ ⊤))).op r := by
    intro y O i
    have hh : Y.presheaf.map i.op = Y.presheaf.map (homOfLE i.le).op := rfl
    rw [hh, ← res_res i.le (le_top : (A y).1 ≤ ⊤) r, hc y, map_mul, res_res]
  have hcompat : TopCat.Presheaf.IsCompatible Y.presheaf (fun y => (A y).1) c := by
    intro y z
    rw [← sub_eq_zero]
    have hnz : Y.presheaf.map (homOfLE
        ((TopologicalSpace.Opens.infLELeft (A y).1 (A z).1).le.trans
          (le_top : (A y).1 ≤ ⊤))).op f ∈
        nonZeroDivisors Γ(Y, (A y).1 ⊓ (A z).1) := by
      have hx := mem_nonZeroDivisors_res (A y).2 (hnzd y)
        (TopologicalSpace.Opens.infLELeft (A y).1 (A z).1).le
      rwa [res_res] at hx
    refine (mul_right_mem_nonZeroDivisors_eq_zero_iff hnz).1 ?_
    rw [sub_mul, key y _ (TopologicalSpace.Opens.infLELeft (A y).1 (A z).1),
      key z _ (TopologicalSpace.Opens.infLERight (A y).1 (A z).1)]
    exact sub_eq_zero.2 rfl
  obtain ⟨cc, hcc, -⟩ := existsUnique_gluing (fun y => (A y).1) ⊤
    (fun y => homOfLE (le_top : (A y).1 ≤ ⊤)) hcover c hcompat
  refine ⟨cc, eq_of_locally_eq (fun y => (A y).1) ⊤
    (fun y => homOfLE (le_top : (A y).1 ≤ ⊤)) hcover _ _ fun y => ?_⟩
  rw [map_mul, hcc y]
  exact hc y

/-- The pullback of a global function restricted to an open is its image under the restricted
map of sections. -/
theorem appLE_top_apply_eq_res_appTop {Y Y₀ : Scheme.{u}} (p : Y ⟶ Y₀) (A : Y.Opens)
    (f : Γ(Y₀, ⊤)) :
    (p.appLE ⊤ A le_top).hom f =
      Y.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op (p.appTop.hom f) := rfl

/-- **The inverse image of a principal ideal sheaf of an affine scheme, on an affine open.** On
an affine open of a scheme over an affine scheme the inverse image of the ideal sheaf of `(f)` is
generated by the restriction of the pullback of `f`. -/
theorem ideal_comap_ofIdealTop_span {Y Y₀ : Scheme.{u}} [IsAffine Y₀] (p : Y ⟶ Y₀)
    (f : Γ(Y₀, ⊤)) (A : Y.Opens) (hA : IsAffineOpen A) :
    ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).comap p).ideal ⟨A, hA⟩ =
      Ideal.span {Y.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op (p.appTop.hom f)} := by
  rw [ideal_comap_appLE _ p ⊤ (isAffineOpen_top Y₀) A hA le_top, ideal_ofIdealTop_top,
    Ideal.map_span, Set.image_singleton, appLE_top_apply_eq_res_appTop]

/-- **The pullback of a nonzerodivisor along a flat morphism to an affine scheme restricts to a
nonzerodivisor on every affine open.** -/
theorem isRegular_res_appTop_of_flat {Y Y₀ : Scheme.{u}} [IsAffine Y₀] (p : Y ⟶ Y₀) [Flat p]
    {f : Γ(Y₀, ⊤)} (hf : IsRegular f) (A : Y.Opens) (hA : IsAffineOpen A) :
    IsRegular (Y.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op (p.appTop.hom f)) := by
  let : Algebra Γ(Y₀, ⊤) Γ(Y, A) := (p.appLE ⊤ A le_top).hom.toAlgebra
  have : Module.Flat Γ(Y₀, ⊤) Γ(Y, A) := p.flat_appLE (isAffineOpen_top Y₀) hA le_top
  have hreg := isRegular_algebraMap_of_flat (R := Γ(Y₀, ⊤)) (C := Γ(Y, A)) hf
  rw [RingHom.algebraMap_toAlgebra, appLE_top_apply_eq_res_appTop] at hreg
  exact hreg

/-- **A quasi-compact morphism whose kernel is the inverse image of a principal ideal sheaf of
an affine scheme.** If `Y` is flat over an affine scheme `Y₀` and the kernel of `j : Z ⟶ Y` is
the inverse image of the ideal sheaf of a nonzerodivisor `f` of `Γ(Y₀, ⊤)`, then the pullback of
`f` is a nonzerodivisor on `Y` and every global function killed by `j` is a multiple of it. -/
theorem isRegular_and_ker_appTop_le_span_of_flat {Y Y₀ Z : Scheme.{u}} [IsAffine Y₀]
    (p : Y ⟶ Y₀) [Flat p] (j : Z ⟶ Y) [QuasiCompact j]
    {f : Γ(Y₀, ⊤)} (hf : IsRegular f)
    (hker : j.ker = (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).comap p) :
    IsRegular (p.appTop.hom f) ∧
      RingHom.ker j.appTop.hom ≤ Ideal.span {p.appTop.hom f} := by
  have hloc : ∀ y : Y, ∃ A : Y.affineOpens, y ∈ (A.1 : Set Y) ∧
      j.ker.ideal A = Ideal.span
        {Y.presheaf.map (homOfLE (le_top : A.1 ≤ ⊤)).op (p.appTop.hom f)} ∧
      Y.presheaf.map (homOfLE (le_top : A.1 ≤ ⊤)).op (p.appTop.hom f) ∈
        nonZeroDivisors Γ(Y, A.1) := by
    intro y
    obtain ⟨A, hA, hyA, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
    refine ⟨⟨A, hA⟩, hyA, ?_, (isRegular_res_appTop_of_flat p hf A hA).mem_nonZeroDivisors⟩
    rw [hker]
    exact ideal_comap_ofIdealTop_span p f A hA
  refine ⟨?_, fun r hr => ?_⟩
  · rw [isRegular_iff_mem_nonZeroDivisors]
    refine mem_nonZeroDivisors_of_forall_exists_mem _ fun y => ?_
    obtain ⟨A, hyA, -, hnzd⟩ := hloc y
    exact ⟨A.1, hyA, hnzd⟩
  · obtain ⟨c, hc⟩ := exists_mul_of_appTop_eq_zero j (p.appTop.hom f) hloc r hr
    exact Ideal.mem_span_singleton'.2 ⟨c, hc.symm⟩

end Stacks.Divisors

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Trivializing the defining ideal sheaf on a chart -/

/-- The kernel of the pullback of the closed immersion of `D` to a chart is the inverse image of
its kernel on a chart below which it lies. -/
private theorem ker_rep_snd_eq_comap_of_hom (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) {W V : SmallEtale B S hS X.1} (m : V ⟶ W) :
    ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd V.1.hom)).ker =
      (((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd W.1.hom)).ker).comap
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map m)) := by
  have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map m) ≫ W.1.hom = V.1.hom :=
    CostructuredArrow.w m.hom
  have h1 := schemeKer_snd_comp B S hS D W.1.hom ((SmallEtale.toOver B S hS X.1).map m)
  rwa [hw] at h1

/-- **The defining ideal at a chart lying over an affine chart on which it is generated by a
nonzerodivisor.** If the defining ideal of `D` at an affine étale chart `W` is generated by a
nonzerodivisor `f`, then at every chart over `W` it is generated by the pullback of `f`, which is
again a nonzerodivisor.

The chart ideal sheaf over `W` is the ideal sheaf of `(f)`, so over a chart `V ⟶ W` it is its
inverse image along an étale, hence flat, morphism of schemes; that inverse image is computed on
the affine opens of `V` by `Stacks.Divisors.ideal_comap_appLE`, and the two halves are then
`Stacks.Divisors.isRegular_and_ker_appTop_le_span_of_flat`.  The reverse inclusion is stability
of the defining ideals under étale restriction. -/
theorem isRegular_and_definingIdealAt_eq_span_etaleChartRestrict (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) {W V : SmallEtale B S hS X.1} (m : V ⟶ W)
    (haff : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left))
    (f : Γ((BigFppfOver.toScheme B S hS).obj W.1.left, ⊤)) (hf : IsRegular f)
    (hgen : definingIdealAt B S hS X D (op W) = Ideal.span {f}) :
    IsRegular (etaleChartRestrict B S hS m f) ∧
      definingIdealAt B S hS X D (op V) = Ideal.span {etaleChartRestrict B S hS m f} := by
  have hAW : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) := haff
  have hAW' : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj W)) := haff
  have hpe : Etale ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map m)) := etale_toScheme_toOver_map B S hS X.1 m
  have hpflat : Flat ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map m)) := inferInstance
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd V.1.hom)) := D.2.2.property_snd V.1.hom
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd V.1.hom)) :=
    inferInstance
  have hker : ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd V.1.hom)).ker =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).comap
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map m)) := by
    rw [ker_rep_snd_eq_comap_of_hom B S hS X D m,
      ker_rep_snd_eq_ofIdealTop_of_definingIdealAt_eq B S hS X D W haff _ hgen]
  obtain ⟨hreg, hle⟩ := Stacks.Divisors.isRegular_and_ker_appTop_le_span_of_flat
    ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map m))
    ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd V.1.hom)) hf hker
  have hkereq : definingIdealAt B S hS X D (op V) =
      RingHom.ker ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd V.1.hom)).appTop.hom :=
    definingIdealAt_eq_ker B S hS X D V
  have hmemf : f ∈ definingIdealAt B S hS X D (op W) :=
    hgen ▸ Ideal.mem_span_singleton_self f
  exact ⟨hreg, le_antisymm (fun x hx => hle (hkereq.le hx))
    (Ideal.span_le.2 (Set.singleton_subset_iff.2
      (definingIdealAt_map B S hS X D m.op f hmemf)))⟩

/-- **A nonzerodivisor generating the defining ideal at every chart over a given chart
trivializes the defining ideal sheaf there.** Multiplication by such a section is bijective over
every object of the slice site, so the morphism of sheaves of modules out of the structure sheaf
that it defines is an isomorphism. -/
theorem nonempty_unitIso_definingIdealSheaf_of_forall_isRegular_span
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (W : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (f : Γ((BigFppfOver.toScheme B S hS).obj W.1.left, ⊤))
    (hgen : definingIdealAt B S hS X D (op W) = Ideal.span {f})
    (h : ∀ (V : (smallEtaleRingedSite B S hS X.1 X.2).C) (m : V ⟶ W),
      IsRegular (etaleChartRestrict B S hS m f) ∧
        definingIdealAt B S hS X D (op V) = Ideal.span {etaleChartRestrict B S hS m f}) :
    Nonempty (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over W) ≅
      (definingIdealSheaf B S hS X D).toSheafOfModules.over W) := by
  let L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) :=
    (definingIdealSheaf B S hS X D).toSheafOfModules
  have hmem : f ∈ definingIdealAt B S hS X D (op W) :=
    hgen ▸ Ideal.mem_span_singleton_self f
  let s : L.val.obj (op W) := ⟨f, hmem⟩
  let sec : (L.over W).val.sections :=
    PresheafOfModules.sectionsMk (fun V => L.val.map V.unop.hom.op s) (by
      intro V V' t
      change L.val.map t.unop.left.op (L.val.map V.unop.hom.op s) = _
      rw [← L.val.map_comp_apply]
      change L.val.map (t.unop.left ≫ V.unop.hom).op s = _
      rw [t.unop.w])
  let φ : SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over W) ⟶
      L.over W := ⟨(L.over W).val.unitHomEquiv.symm sec⟩
  have hval : ∀ (V : (Over W)ᵒᵖ)
      (c : Γ((BigFppfOver.toScheme B S hS).obj V.unop.left.1.left, ⊤)),
      ((φ.val.app V c).val : Γ((BigFppfOver.toScheme B S hS).obj V.unop.left.1.left, ⊤)) =
        c * etaleChartRestrict B S hS V.unop.hom f := fun _ _ => rfl
  have hbij : ∀ V : (Over W)ᵒᵖ, Function.Bijective (φ.val.app V) := by
    intro V
    obtain ⟨hreg, hspan⟩ := h V.unop.left V.unop.hom
    refine ⟨fun a b hab =>
      hreg.right ((hval V a).symm.trans ((Subtype.ext_iff.1 hab).trans (hval V b))), fun y => ?_⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hspan.le y.property)
    exact ⟨c, Subtype.ext ((hval V c).trans hc)⟩
  have hiso : ∀ V : (Over W)ᵒᵖ, IsIso (φ.val.app V) := fun V =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij V)
  let ψ : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).over W)).val ≅ (L.over W).val :=
    PresheafOfModules.isoMk (fun V => @asIso _ _ _ _ (φ.val.app V) (hiso V))
      (fun _ _ t => φ.val.naturality t)
  exact ⟨(SheafOfModules.fullyFaithfulForget
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).over W)).preimageIso ψ⟩

/-- **An affine chart on which the defining ideal is generated by a nonzerodivisor, through any
point of any chart.** This is condition (3) of Stacks 083C read on one chart: the inverse image
of `D` there is an effective Cartier ideal sheaf, hence generated by a nonzerodivisor on an
affine open around any point, and that affine open is again an étale chart. -/
theorem exists_openChart_isRegular_span_definingIdealAt_of_etalePullbacks
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (hD : HasEffectiveCartierEtalePullbacks B S hS X D) (U : SmallEtale B S hS X.1)
    (z : (BigFppfOver.toScheme B S hS).obj U.1.left) :
    ∃ (V : SmallEtale B S hS X.1) (m : V ⟶ U)
      (g : Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) ∧ IsRegular g ∧
        definingIdealAt B S hS X D (op V) = Ideal.span {g} ∧
        ∃ z' : (BigFppfOver.toScheme B S hS).obj V.1.left,
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map m) z' = z := by
  have hK := (isSchemeEffectiveCartierPullback_iff B S hS X D U.1.left U.1.hom).1
    (hD U.1.left U.1.hom (isEtale_of_presheaf_etale B S hS U.2))
  obtain ⟨A, hA, hzA, -, g, hg, hgenA⟩ :=
    Stacks.Divisors.exists_basicOpen_isRegular_span_of_isEffectiveCartierDivisor _ hK z ⊤ trivial
  have hAff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (openChart B S hS X.1 U A).1.left) := hA
  have hker : ((BigFppfOver.toScheme B S hS).map
        (D.2.2.rep.snd (openChart B S hS X.1 U A).1.hom)).ker =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {A.topIso.inv.hom g}) := by
    rw [ker_rep_snd_eq_comap_of_hom B S hS X D (openChartInclusion B S hS X.1 U A),
      toScheme_map_toOver_map_openChartInclusion]
    exact Stacks.Divisors.comap_ι_eq_ofIdealTop_of_ideal_eq_span _ A hA g hgenA
  refine ⟨openChart B S hS X.1 U A, openChartInclusion B S hS X.1 U A, A.topIso.inv.hom g,
    hAff, Stacks.Divisors.isRegular_ringEquiv A.topIso.symm.commRingCatIsoToRingEquiv hg,
    definingIdealAt_eq_of_ker_rep_snd_eq B S hS X D _ hAff _ hker, ⟨z, hzA⟩, ?_⟩
  rw [toScheme_map_toOver_map_openChartInclusion]
  rfl

/-- **The charts on which the defining ideal sheaf is trivial cover every chart.** Under
condition (3) of Stacks 083C the affine charts on which the defining ideal is generated by a
nonzerodivisor trivialize the defining ideal sheaf, and one of them passes through every point
of the scheme underlying a given chart; a family of charts jointly surjective on those points
generates a covering sieve. -/
theorem sieve_ofArrows_nonempty_unitIso_definingIdealSheaf_mem (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (hD : HasEffectiveCartierEtalePullbacks B S hS X D)
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    Sieve.ofArrows
        (fun i : Σ V : (smallEtaleRingedSite B S hS X.1 X.2).C,
          { _m : V ⟶ U //
            Nonempty (SheafOfModules.unit
                ((Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedSite B S hS X.1 X.2).O).over V) ≅
              (definingIdealSheaf B S hS X D).toSheafOfModules.over V) } => i.1)
        (fun i => i.2.1) ∈ (smallEtaleRingedSite B S hS X.1 X.2).J U := by
  refine smallEtale_sieve_of_pointwise_covering B S hS X.1 U _ fun z => ?_
  obtain ⟨V, m, g, hAff, hg, hgen, z', hz'⟩ :=
    exists_openChart_isRegular_span_definingIdealAt_of_etalePullbacks B S hS X D hD U z
  exact ⟨V, m, Sieve.ofArrows_mk
    (fun i : Σ V : (smallEtaleRingedSite B S hS X.1 X.2).C,
      { _m : V ⟶ U //
        Nonempty (SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O).over V) ≅
          (definingIdealSheaf B S hS X D).toSheafOfModules.over V) } => i.1)
    (fun i => i.2.1)
    ⟨V, m, nonempty_unitIso_definingIdealSheaf_of_forall_isRegular_span B S hS X D V g hgen
      fun V' m' => isRegular_and_definingIdealAt_eq_span_etaleChartRestrict B S hS X D m'
        hAff g hg hgen⟩, z', hz'⟩

end AlgebraicGeometry.Space

end
