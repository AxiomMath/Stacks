module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk

/-!
# Torsion-free quasi-coherent modules on an integral scheme

Torsion freeness of a quasi-coherent module on an integral scheme is a local condition: it can
be tested at every stalk, or on the sections over every affine open. It is stable under
extensions, and every flat quasi-coherent module is torsion free.

## Main results

* `AlgebraicGeometry.isTorsionFree_iff_forall_stalk`: torsion freeness is detected at stalks.
* `AlgebraicGeometry.isTorsionFree_iff_forall_isAffineOpen`: torsion freeness is detected on
  the sections over affine opens.
* `AlgebraicGeometry.isTorsionFree_middle_of_shortExact`: torsion freeness passes to the middle
  term of a short exact sequence.
* `AlgebraicGeometry.isTorsionFree_of_isFlat`: a flat quasi-coherent module is torsion free.

## References

* [Stacks Project, Tag 0AXW](https://stacks.math.columbia.edu/tag/0AXW)
* [Stacks Project, Tag 0AXS](https://stacks.math.columbia.edu/tag/0AXS)
* [Stacks Project, Tag 0AXX](https://stacks.math.columbia.edu/tag/0AXX)
* [Stacks Project, Tag 0AXU](https://stacks.math.columbia.edu/tag/0AXU)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry

/-- A nonzero element of the stalk of the structure sheaf killing an element of the stalk of `F`
comes from sections `a ≠ 0`, `b` over an affine open with `a • b = 0` and `b` of the given germ. -/
private theorem exists_affine_smul_eq_zero_of_stalk
    {X : Scheme.{u}} [IsIntegral X] (F : X.Modules) (x : X)
    (r : X.presheaf.stalk x) (m : ↑(F.presheaf.stalk x)) (hr : r ≠ 0)
    (hkill :
      letI : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      r • m = 0) :
    ∃ (V : X.Opens) (hxV : x ∈ V), IsAffineOpen V ∧ ∃ (a : Γ(X, V)) (b : Γ(F, V)),
      a ≠ 0 ∧ a • b = 0 ∧ F.presheaf.germ V x hxV b = m := by
  let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  obtain ⟨W₁, hW₁, hxW₁, a, ha⟩ :=
    X.presheaf.exists_le_germ_eq r (show x ∈ (⊤ : X.Opens) from Set.mem_univ x)
  obtain ⟨W₂, hW₂, hxW₂, b, hb⟩ :=
    F.presheaf.exists_le_germ_eq m (show x ∈ (⊤ : X.Opens) from Set.mem_univ x)
  let W : X.Opens := W₁ ⊓ W₂
  have hxW : x ∈ W := ⟨hxW₁, hxW₂⟩
  let i₁ := homOfLE (inf_le_left : W ≤ W₁)
  let i₂ := homOfLE (inf_le_right : W ≤ W₂)
  let a₀ : Γ(X, W) := X.presheaf.map i₁.op a
  let b₀ : Γ(F, W) := F.presheaf.map i₂.op b
  have ha₀ : (X.presheaf.germ W x hxW).hom a₀ = r :=
    (X.presheaf.germ_res_apply i₁ x hxW a).trans ha
  have hb₀ : F.presheaf.germ W x hxW b₀ = m :=
    (F.presheaf.germ_res_apply i₂ x hxW b).trans hb
  have hkill₀ : F.presheaf.germ W x hxW (a₀ • b₀) = 0 := calc
    _ = (X.presheaf.germ W x hxW).hom a₀ • F.presheaf.germ W x hxW b₀ :=
      PresheafOfModules.germ_smul F.val x W hxW a₀ b₀
    _ = 0 := by rw [ha₀, hb₀, hkill]
  obtain ⟨W', hxW', iW'W, _, heq⟩ :=
    F.presheaf.germ_eq x hxW hxW (a₀ • b₀) 0 (by simpa using hkill₀)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW'⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW' W'.isOpen
  have hVW'le : V ≤ W' := hVW'
  let a' : Γ(X, W') := X.presheaf.map iW'W.op a₀
  let b' : Γ(F, W') := F.presheaf.map iW'W.op b₀
  let aV : Γ(X, V) := X.presheaf.map (homOfLE hVW'le).op a'
  let bV : Γ(F, V) := F.presheaf.map (homOfLE hVW'le).op b'
  have haV : (X.presheaf.germ V x hxV).hom aV = r :=
    ((X.presheaf.germ_res_apply (homOfLE hVW'le) x hxV a').trans
      (X.presheaf.germ_res_apply iW'W x hxW' a₀)).trans ha₀
  have hbV : F.presheaf.germ V x hxV bV = m :=
    ((F.presheaf.germ_res_apply (homOfLE hVW'le) x hxV b').trans
      (F.presheaf.germ_res_apply iW'W x hxW' b₀)).trans hb₀
  have haV_ne : aV ≠ 0 := fun hz => hr (by rw [← haV, hz, map_zero])
  have hkillW' : a' • b' = 0 := by
    show (X.presheaf.map iW'W.op a₀) • (F.presheaf.map iW'W.op b₀) = 0
    rw [← F.map_smul]
    simpa using heq
  have hkillV : aV • bV = 0 := by
    simpa only [F.map_smul, map_zero] using
      congrArg (F.presheaf.map (homOfLE hVW'le).op) hkillW'
  exact ⟨V, hxV, hV, aV, bV, haV_ne, hkillV, hbV⟩

/-- A quasi-coherent module on an integral scheme is torsion free precisely when its
stalk at every point is torsion free over the local ring at that point. -/
@[stacks 0AXW]
theorem isTorsionFree_iff_forall_stalk
    {X : Scheme.{u}} [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent] :
    IsTorsionFree F ↔
      ∀ x : X,
        letI : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) F.val x
        Module.IsTorsionFree (X.presheaf.stalk x) ↑(F.presheaf.stalk x) := by
  constructor
  · intro hF x
    let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    refine Module.isTorsionFree_iff_smul_eq_zero.mpr fun r m hkill =>
      or_iff_not_imp_left.mpr fun hr => ?_
    obtain ⟨V, hxV, -, aV, bV, haV_ne, hkillV, hbV⟩ :=
      exists_affine_smul_eq_zero_of_stalk F x r m hr hkill
    have htors : IsTorsionSection F bV := by
      intro y hy
      let : Module (X.presheaf.stalk y) ↑(F.presheaf.stalk y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      exact ⟨(X.presheaf.germ V y hy).hom aV,
        fun hay => haV_ne (germ_injective_of_isIntegral X y hy (by simpa using hay)),
        calc
          _ = (F.presheaf.germ V y hy) (aV • bV) :=
            (PresheafOfModules.germ_smul F.val y V hy aV bV).symm
          _ = 0 := by rw [hkillV, map_zero]⟩
    rw [← hbV, hF _ _ htors, map_zero]
  · refine fun hstalk => (isTorsionFree_iff F).2 fun U s hs =>
      TopCat.Presheaf.IsSheaf.section_ext (U := Opposite.op U) F.isSheaf fun x hx => ?_
    let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    obtain ⟨r, hr, hkill⟩ := hs x hx
    obtain ⟨V, hxV, iVU, iVU', heq⟩ := F.presheaf.germ_eq x hx hx s 0 (by
      simpa using ((Module.isTorsionFree_iff_smul_eq_zero.mp (hstalk x)) r
        (F.presheaf.germ U x hx s) hkill).resolve_left hr)
    refine ⟨V, iVU.le, hxV, ?_⟩
    convert heq using 1 <;> congr 1

private theorem germ_eq_zero_of_affine_sections_torsionFree
    {X : Scheme.{u}} [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    (hF : ∀ V : X.Opens, IsAffineOpen V →
      Module.IsTorsionFree Γ(X, V) Γ(F, V))
    {U : X.Opens} (s : Γ(F, U)) (x : X) (hx : x ∈ U)
    (hs : IsTorsionSection F s) :
    F.presheaf.germ U x hx s = 0 := by
  let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  obtain ⟨r, hr, hkill⟩ := hs x hx
  obtain ⟨V, hxV, hV, aV, bV, haV_ne, hmul, hbV⟩ :=
    exists_affine_smul_eq_zero_of_stalk F x r _ hr hkill
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : IsDomain Γ(X, V) := IsIntegral.component_integral V
  have hbVzero : bV = 0 := by
    apply (hF V hV).isSMulRegular ((isRegular_iff_ne_zero).2 haV_ne)
    simpa using hmul
  rw [← hbV, hbVzero, map_zero]

/-- A quasi-coherent module on an integral scheme is torsion free if and only if its
sections on every affine open are torsion free over the ring of functions there. -/
@[stacks 0AXS]
theorem isTorsionFree_iff_forall_isAffineOpen
    {X : Scheme.{u}} [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent] :
    IsTorsionFree F ↔
      ∀ U : X.Opens, IsAffineOpen U → Module.IsTorsionFree Γ(X, U) Γ(F, U) := by
  constructor
  · intro hF U hU
    by_cases hne : Nonempty U
    · have : IsDomain Γ(X, U) := IsIntegral.component_integral U
      refine ⟨fun r hr s t hst => sub_eq_zero.mp (hF _ _ fun x hx => ?_)⟩
      let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      exact ⟨(X.presheaf.germ U x hx).hom r,
        fun hrx => (isRegular_iff_ne_zero).mp hr
          (germ_injective_of_isIntegral X x hx (by simpa using hrx)),
        calc
          _ = (F.presheaf.germ U x hx) (r • (s - t)) :=
            (PresheafOfModules.germ_smul F.val x U hx r (s - t)).symm
          _ = 0 := by rw [smul_sub, sub_eq_zero.mpr hst, map_zero]⟩
    · exact ⟨fun r hr s t hst => TopCat.Presheaf.IsSheaf.section_ext (U := Opposite.op U)
        F.isSheaf fun x hx => (hne ⟨⟨x, hx⟩⟩).elim⟩
  · refine fun hF U s hs =>
      TopCat.Presheaf.IsSheaf.section_ext (U := Opposite.op U) F.isSheaf fun x hx => ?_
    obtain ⟨V, hxV, iVU, iVU', heq⟩ := F.presheaf.germ_eq x hx hx s 0 (by
      simpa using germ_eq_zero_of_affine_sections_torsionFree F hF s x hx hs)
    refine ⟨V, iVU.le, hxV, ?_⟩
    convert heq using 1 <;> congr 1

/-- A short exact extension of torsion-free quasi-coherent modules on an integral
scheme is torsion free. -/
@[stacks 0AXX]
lemma isTorsionFree_middle_of_shortExact {X : Scheme.{u}} [IsIntegral X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h₁ : IsTorsionFree S.X₁)
    (h₃ : IsTorsionFree S.X₃) :
    IsTorsionFree S.X₂ := by
  refine (isTorsionFree_iff_forall_stalk _).mpr fun x => ?_
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule S.X₁ x
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule S.X₂ x
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule S.X₃ x
  have : Module.IsTorsionFree _ (Stacks.SheafOfModules.FlatShortExact.abStalk S.X₁ x) :=
    (isTorsionFree_iff_forall_stalk S.X₁).mp h₁ x
  have : Module.IsTorsionFree _ (Stacks.SheafOfModules.FlatShortExact.abStalk S.X₃ x) :=
    (isTorsionFree_iff_forall_stalk S.X₃).mp h₃ x
  obtain ⟨f, g, hf, hfg, _⟩ := Stacks.SheafOfModules.FlatShortExact.stalkShortExact S hS x
  show Module.IsTorsionFree (X.presheaf.stalk x) (Stacks.SheafOfModules.FlatShortExact.abStalk
    S.X₂ x)
  exact isTorsionFree_of_injective_of_exact f g hf hfg

/-- A flat quasi-coherent module on an integral scheme is torsion free. -/
@[stacks 0AXU]
theorem isTorsionFree_of_isFlat {X : Scheme.{u}} [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent]
    (hF : SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F) :
    IsTorsionFree F := by
  refine (isTorsionFree_iff_forall_stalk F).2 fun x => ?_
  let : Module (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    F.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
  have : Module.Flat (X.presheaf.stalk x) ↑(F.presheaf.stalk x) :=
    (SheafOfModules.isFlat_iff_stalk_flat X.sheaf F).mp hF x
  exact Module.Flat.isTorsionFree (R := X.presheaf.stalk x) (M := ↑(F.presheaf.stalk x))

end AlgebraicGeometry
