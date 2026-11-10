module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedTwistAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistUnit.Basic
import StacksFrontier.AlgebraicGeometry.ClosedPushforward.IdealMultipleKernel
import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.IdealPowers
import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealSheafFiniteType
import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraModule
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDegreeZeroIso

/-!
# `ℐ_Z · 𝒪(d)` on a relative Proj, in the two spellings Tag 0801 needs

Tag 0801's graded ideal is the degreewise kernel of `ψ`, and `ψ` factors through the quotient of
the twists by the graded ideal generated in degree `0` by `ℐ_Z`
(`…RelativeProjTwists.closedGradedIdeal` at `…closedIdealDegreeZero`). The absolute ideal of
equations of a chart, on the other hand, asks a twisted section to vanish on `Z`, i.e. to die in
`i_* i^* 𝒪(d)`. The two are the same subsheaf of `𝒪(d)`, and this file proves it.

Both sides are `ℐ_Z · 𝒪(d)`, but they are *built* differently: one as a span of graded products
inside the algebra of twists, the other as the ideal-power multiple
`Stacks.Algebraization.idealPowerMultiple i.ker 1` cut out affine-locally on the relative Proj.
The identification rests on the degree-zero piece of the twists being the structure sheaf, which
is `Stacks.AlgebraicGeometry.RelativeProjTwistUnit.isIso_oneHom`: a degree-zero local section is
a local function times the algebra unit, so a *graded* product by it is a *scalar* product.

## Main results

* `Stacks.Algebraization.smul_mem_idealPowerMultiple_one`: scaling any local section of any module
  by a local section of `ℐ · 𝒪_X` lands in `ℐ · M`.
* `…RelativeProjTwists.closedIdealDegreeZero_eq_idealPowerMultiple`: **`ℐ_Z`, as a submodule of
  the degree-zero twist, is `ℐ_Z · 𝒪(0)`** — the definition is a kernel, and
  `…kernelSubmodule_unit_app_eq_idealMultiple` turns that kernel into an ideal-power multiple.
* `…RelativeProjTwists.comap_closedIdealDegreeZero_eq`: **`ℐ_Z` versus `i.ker`.** Under the
  identification of the degree-zero twist with the structure sheaf, `ℐ_Z` is the ideal subsheaf
  `ℐ_Z · 𝒪` of the structure sheaf; `…mem_closedIdealDegreeZero_iff_scalar_mem_ideal` reads that
  on an affine open, where the right-hand side is the ideal `i.ker` there.
* `…RelativeProjTwists.generatedByDegree_closedIdealDegreeZero_eq`: **the shape bridge.** The
  degree-`n` piece of the graded ideal generated in degree `0` by `ℐ_Z` is
  `ℐ_Z · 𝒪(n)` as an ideal-power multiple.
* `…RelativeProjTwists.restrictionHom_app_eq_zero_iff_restrictionToClosed`: **the consequence Tag
  0801 consumes.** A homogeneous local section of the twists dies in `(i_*𝒪_Z)(n)` exactly when
  it restricts to zero on `Z`.

## Implementation notes

**The degrees are compared heterogeneously.** `0 + n` and `n` are not definitionally equal
integers, so `SheafGradedAlgebra.one_mul` is an `HEq` and the generators of
`…RelativeProjGradedIdeal.IsGeneratedInDegree` are related to the sections of `𝒜_n` by an `HEq`
too. `heq_smul` below is the one transport needed: scaling respects such an identification.

**The scalar needs an explicit type ascription.** The degree-zero identification lands in
`SheafOfModules.unit (RingedSite.ofScheme X).ringSheaf`, whose sections are *definitionally*
`Γ(X, U)` but not syntactically so, and instance search does not cross that gap — the hazard the
local instances of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/IdealPowerQuasicoherent.lean` exist for.
The scalar is therefore introduced with `set c : Γ(…, U) := …`, and the two cancellations of the
identification against its inverse are instantiated at an explicit section before being rewritten
with: `rw` unifies only up to reducible transparency, so a lemma whose argument is stated at the
`Γ(…)` spelling cannot be matched against a term the comap produced at the unit-sheaf spelling.

**Quasi-coherence is not needed for `smul_mem_idealPowerMultiple_one`**: it is the defining
affine-local lower bound of `ℐ · M` together with affine-locality of membership, so it holds for
an arbitrary sheaf of modules.

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)

## Not done here

No Stacks tag is claimed here. **Tag 0801's relative `iso` clause is proved**, downstream, in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/VanishingPresentation.lean`: the
chart-level hypothesis the reductions of this file leave is discharged there by
`Stacks.AlgebraicGeometry.RelativeProjTwists.ker_eq_chartMap_ker`, and the whole of
`…RelativeProjGradedIdeal.VanishingIdealPresentation` is built as
`…RelativeProjTwists.vanishingIdealPresentation`, on no hypothesis beyond Tag 0801's own. Tag
0803 is registered with that presentation discharged in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/FiniteTypePresentationOffSupport.lean`.

What closed the clause, on top of the reductions here: the chart comparison
`…RelativeProjTwists.pullbackGlobalSections_degreeSection_eq_zero_iff`, which composes
`…RelativeProjTwists.TwistData.ψ_chart` with the base change of the unit `M ⟶ i_*i^*M` along an
arbitrary open immersion (`Stacks.AlgebraicGeometry.ChartUnit.app_unit_eq_zero_iff`) and with
`…RelativeProjTwists.restrictionHom_app_eq_zero_iff_restrictionToClosed`; the resulting equality
of homogeneous ideals `…RelativeProjTwists.sectionGradedIdeal_eq_idealOfClosedSubscheme`; and the
absolute case of Tag 0801 restated at an `AddSubgroup`-valued grading,
`Stacks.ProjChartKerQuotient.ker_eq_ker_projMap_quotientMk`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal
open Stacks.AlgebraicGeometry.RelativeProjTwistUnit

namespace Stacks.Algebraization

universe u

attribute [local instance] Stacks.Algebraization.sectionsModuleΓSheaf
  Stacks.Algebraization.sectionsModuleΓ
  AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-- **Multiplying a local section of any module by a local section of `ℐ · 𝒪_X` lands in
`ℐ · M`.** Membership is affine-local, and over an affine open the sections of `ℐ · 𝒪_X` are the
ideal itself while those of `ℐ · M` are `ℐ(U) · M(U)`. -/
public theorem smul_mem_idealPowerMultiple_one {X : Scheme.{u}} (I : X.IdealSheafData)
    (M : X.Modules) (U : X.Opens) {c : Γ(X, U)}
    (hc : c ∈ (idealPowerMultiple I 1 (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U))
    (b : Γ(M, U)) :
    c • b ∈ (idealPowerMultiple I 1 M).toSubmodule.obj (op U) := by
  refine mem_submodule_of_affine _ U _ fun V hiV => ?_
  have hle : V.1 ≤ U := leOfHom hiV
  have harr : hiV = homOfLE hle := Subsingleton.elim _ _
  have hcV : X.presheaf.map (homOfLE hle).op c ∈ I.ideal V := by
    have h := (idealPowerMultiple I 1
      (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.map (homOfLE hle).op hc
    rwa [idealModule_obj_affine I V] at h
  have hgen := (idealPowerMultiple_le_iff I 1 M (idealPowerMultiple I 1 M)).mp le_rfl V
  have hres : Stacks.restr M.val (homOfLE hle).op (c • b) =
      X.presheaf.map (homOfLE hle).op c • Stacks.restr M.val (homOfLE hle).op b :=
    Stacks.Blowup.restr_smul_gamma (F := M) hle c b
  have hfin := hgen (Submodule.smul_mem_smul (by rwa [pow_one])
    (Submodule.mem_top (x := Stacks.restr M.val (homOfLE hle).op b)))
  rw [harr]
  change Stacks.restr M.val (homOfLE hle).op (c • b) ∈
    (idealPowerMultiple I 1 M).toSubmodule.obj (op V.1)
  exact hres ▸ hfin

end Stacks.Algebraization

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- Scaling a homogeneous local section respects a heterogeneous identification of two degrees. -/
private theorem heq_smul {𝒜 : SheafGradedAlgebra S} {i j : ℤ} (h : i = j) (U : S.Opens)
    (r : Γ(S, U)) {b : Γ(𝒜.piece i, U)} {a : Γ(𝒜.piece j, U)} (hba : HEq b a) :
    HEq (r • b) (r • a) := by
  subst h
  rw [eq_of_heq hba]

/-- The graded product of `c • 1` with `a` is `c • a`, up to the identification `0 + m = m`. -/
private theorem mul_smul_one_heq (𝒜 : SheafGradedAlgebra S) (m : ℤ) (U : S.Opens) (c : Γ(S, U))
    (a : Γ(𝒜.piece m, U)) : HEq ((𝒜.mul 0 m).app U (c • 𝒜.one U) a) (c • a) := by
  rw [(𝒜.mul 0 m).map_smul_left U c (𝒜.one U) a]
  exact heq_smul (zero_add m) U c (𝒜.one_mul m U a)

variable (D : TwistData A) {Z : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme)

/-- **`ℐ_Z` is the ideal-power multiple `ℐ_Z · 𝒪(0)` of the degree-zero twist.** The ideal sheaf
of the closed subscheme inside the degree-zero twist was *defined* as the kernel of the
restriction `𝒪(0) ⟶ i_*i^*𝒪(0)`, and `…kernelSubmodule_unit_app_eq_idealMultiple` identifies
that kernel with `ℐ_Z · 𝒪(0)`. -/
theorem closedIdealDegreeZero_eq_idealPowerMultiple [IsClosedImmersion i] :
    closedIdealDegreeZero D i =
      Stacks.Algebraization.idealPowerMultiple i.ker 1 ((twistSheafGradedAlgebra D).piece 0) :=
  Stacks.Algebraization.kernelSubmodule_unit_app_eq_idealMultiple _ i

/-- The scalar of a local section of `ℐ_Z` lies in the ideal subsheaf `ℐ_Z · 𝒪`: the degree-zero
identification is a morphism of modules, so it carries `ℐ_Z · 𝒪(0)` into `ℐ_Z · 𝒪`. -/
private theorem scalar_mem_idealMultiple [IsClosedImmersion i]
    (V : (relativeProj A).scheme.Opensᵒᵖ)
    {f : Γ((twistSheafGradedAlgebra D).piece 0, V.unop)}
    (hf : f ∈ (closedIdealDegreeZero D i).toSubmodule.obj V) :
    ((pieceZeroIsoUnit D).hom.val.app V).hom f ∈
      (Stacks.Algebraization.idealPowerMultiple i.ker 1
        (SheafOfModules.unit (relativeProj A).scheme.ringCatSheaf)).toSubmodule.obj V := by
  rw [closedIdealDegreeZero_eq_idealPowerMultiple D i] at hf
  exact Stacks.Algebraization.idealPowerMultiple_le_sheafSubmoduleComap i.ker 1
    (pieceZeroIsoUnit D).hom _ le_rfl V hf

/-- A local section of `ℐ_Z · 𝒪` scales the algebra unit into `ℐ_Z`: the inverse of the
degree-zero identification carries `ℐ_Z · 𝒪` back into `ℐ_Z · 𝒪(0)`. -/
private theorem inv_scalar_mem_closedIdealDegreeZero [IsClosedImmersion i]
    (V : (relativeProj A).scheme.Opensᵒᵖ) {r : Γ((relativeProj A).scheme, V.unop)}
    (hr : r ∈ (Stacks.Algebraization.idealPowerMultiple i.ker 1
      (SheafOfModules.unit (relativeProj A).scheme.ringCatSheaf)).toSubmodule.obj V) :
    ((pieceZeroIsoUnit D).inv.val.app V).hom r ∈
      (closedIdealDegreeZero D i).toSubmodule.obj V := by
  rw [closedIdealDegreeZero_eq_idealPowerMultiple D i]
  exact Stacks.Algebraization.idealPowerMultiple_le_sheafSubmoduleComap i.ker 1
    (pieceZeroIsoUnit D).inv _ le_rfl V hr

/-- The degree-zero identification cancels against its inverse on a local section of the
degree-zero twist. -/
private theorem inv_hom_app_apply (V : (relativeProj A).scheme.Opensᵒᵖ)
    (f : Γ((twistSheafGradedAlgebra D).piece 0, V.unop)) :
    ((pieceZeroIsoUnit D).inv.val.app V).hom
      (((pieceZeroIsoUnit D).hom.val.app V).hom f) = f :=
  congrFun (congrArg (fun g => ⇑(ConcreteCategory.hom
    ((SheafOfModules.Hom.val g).app V))) (pieceZeroIsoUnit D).hom_inv_id) f

/-- The degree-zero identification cancels against its inverse on a local function. -/
private theorem hom_inv_app_apply (V : (relativeProj A).scheme.Opensᵒᵖ)
    (r : Γ((relativeProj A).scheme, V.unop)) :
    ((pieceZeroIsoUnit D).hom.val.app V).hom
      (((pieceZeroIsoUnit D).inv.val.app V).hom r) = r :=
  congrFun (congrArg (fun g => ⇑(ConcreteCategory.hom
    ((SheafOfModules.Hom.val g).app V))) (pieceZeroIsoUnit D).inv_hom_id) r

/-- **`ℐ_Z` versus the ideal sheaf of `Z`.** The ideal sheaf of the closed subscheme inside the
degree-zero twist corresponds, under the identification of that twist with the structure sheaf,
to the ideal subsheaf `ℐ_Z · 𝒪` of the structure sheaf — the ideal sheaf `i.ker` itself, by
`…idealPowerMultiple_unit_eq_kernel`.

This is the comparison that `…RelativeProjTwistUnit.isIso_oneHom` was needed for:
`closedIdealDegreeZero D i` is a submodule of the degree-zero twist while `i.ker` is a
`AlgebraicGeometry.Scheme.IdealSheafData`, and without the identification of the twist with the
structure sheaf the two live in unrelated places. -/
theorem comap_closedIdealDegreeZero_eq [IsClosedImmersion i] :
    AlgebraicGeometry.sheafSubmoduleComap (pieceZeroIsoUnit D).inv (closedIdealDegreeZero D i) =
      Stacks.Algebraization.idealPowerMultiple i.ker 1
        (SheafOfModules.unit (relativeProj A).scheme.ringCatSheaf) := by
  refine le_antisymm (fun V x hx => ?_) (fun V x hx => ?_)
  · have hcancel : ((pieceZeroIsoUnit D).hom.val.app V).hom
        (((pieceZeroIsoUnit D).inv.val.app V).hom x) = x := hom_inv_app_apply D V x
    have h := scalar_mem_idealMultiple D i V hx
    rwa [hcancel] at h
  · exact inv_scalar_mem_closedIdealDegreeZero D i V hx

/-- **`ℐ_Z` read on an affine open of the relative Proj.** A local section of the degree-zero
twist lies in `ℐ_Z` exactly when its scalar lies in the ideal cut out there by `Z`. -/
theorem mem_closedIdealDegreeZero_iff_scalar_mem_ideal [IsClosedImmersion i]
    (U : (relativeProj A).scheme.affineOpens)
    (f : Γ((twistSheafGradedAlgebra D).piece 0, U.1)) :
    f ∈ (closedIdealDegreeZero D i).toSubmodule.obj (op U.1) ↔
      ((pieceZeroIsoUnit D).hom.val.app (op U.1)).hom f ∈ i.ker.ideal U := by
  refine ⟨fun hf => ?_, fun hc => ?_⟩
  · rw [← Stacks.Algebraization.idealModule_obj_affine i.ker U]
    exact scalar_mem_idealMultiple D i (op U.1) hf
  · have hmem := inv_scalar_mem_closedIdealDegreeZero D i (op U.1)
      (by rw [Stacks.Algebraization.idealModule_obj_affine i.ker U]; exact hc)
    rwa [inv_hom_app_apply] at hmem

/-- **The shape bridge: `ℐ_Z · 𝒪(n)` computed in the graded algebra of twists is the
ideal-power multiple of the ideal sheaf of `Z`.** The left-hand side is the degree-`n` piece of
the graded ideal generated in degree `0` by `ℐ_Z`, whose generators are the products
`(𝒪(0) ⊗ 𝒪(n) ⟶ 𝒪(n))(f, a)` with `f` a local section of `ℐ_Z`; the right-hand side is the
subsheaf cut out affine-locally by `ℐ_Z(U) · 𝒪(n)(U)`.

The two agree because the degree-zero piece of the twists is the structure sheaf
(`…RelativeProjTwistUnit.isIso_oneHom`): a degree-zero local section `f` is `c` times the algebra
unit for a unique local function `c`, so the graded product `f · a` is the scalar product `c • a`,
and `f` lies in `ℐ_Z` exactly when `c` lies in `ℐ_Z · 𝒪`. -/
theorem generatedByDegree_closedIdealDegreeZero_eq [IsClosedImmersion i] (n : ℤ) :
    generatedByDegree (twistSheafGradedAlgebra D) (closedIdealDegreeZero D i) n =
      Stacks.Algebraization.idealPowerMultiple i.ker 1 ((twistSheafGradedAlgebra D).piece n) := by
  set 𝒜 := twistSheafGradedAlgebra D with h𝒜
  refine le_antisymm (generatedByDegree_le 𝒜 _ ?_) ?_
  · intro m hm U f hf a x hx
    obtain rfl : m = n := by omega
    set c : Γ((relativeProj A).scheme, U) :=
      ((pieceZeroIsoUnit D).hom.val.app (op U)).hom f with hc
    have hfc : f = c • 𝒜.one U :=
      (inv_hom_app_apply D (op U) f).symm.trans
        (SheafOfModules.GradedAlgebra.inv_pieceZeroIsoUnit_apply
          D.algebra (pieceZeroIsoUnit D) (pieceZeroIsoUnit_one D) (op U) c)
    have hxc : x = c • a := eq_of_heq (hx.trans (hfc ▸ mul_smul_one_heq 𝒜 m U c a))
    rw [hxc]
    exact Stacks.Algebraization.smul_mem_idealPowerMultiple_one i.ker (𝒜.piece m) U
      (scalar_mem_idealMultiple D i (op U) hf) a
  · refine (Stacks.Algebraization.idealPowerMultiple_le_iff i.ker 1 (𝒜.piece n) _).2 fun U => ?_
    rw [pow_one]
    refine Submodule.smul_le.2 fun r hr a _ => ?_
    set f := ((pieceZeroIsoUnit D).inv.val.app (op U.1)).hom r with hf
    have hfr : f = r • 𝒜.one U.1 :=
      SheafOfModules.GradedAlgebra.inv_pieceZeroIsoUnit_apply
        D.algebra (pieceZeroIsoUnit D) (pieceZeroIsoUnit_one D) (op U.1) r
    have hmem : f ∈ (closedIdealDegreeZero D i).toSubmodule.obj (op U.1) := by
      refine inv_scalar_mem_closedIdealDegreeZero D i (op U.1) ?_
      rw [Stacks.Algebraization.idealModule_obj_affine i.ker U]
      exact hr
    refine isGeneratedInDegree_generatedByDegree 𝒜 _ n n (zero_add n) U.1 f hmem a (r • a) ?_
    rw [hfr]
    exact (mul_smul_one_heq 𝒜 n U.1 r a).symm

/-- **A homogeneous local section of the twists dies in `(i_*𝒪_Z)(n)` exactly when it restricts
to zero on `Z`.** This is the form Tag 0801's chain consumes: its `ψ` factors through the
quotient by `ℐ_Z · 𝒪(n)`, while the absolute ideal of equations of a chart asks the twisted
section to vanish on `Z`, and the two conditions are here identified.

`…restrictionHom_app_eq_zero_iff` reads the left-hand side as membership in `ℐ_Z · 𝒪(n)` built as
a span of graded products; the shape bridge turns that into the ideal-power multiple, and
`…kernelSubmodule_unit_app_eq_idealMultiple` turns the ideal-power multiple into the kernel of the
restriction. -/
theorem restrictionHom_app_eq_zero_iff_restrictionToClosed [IsClosedImmersion i] (n : ℤ)
    (V : (relativeProj A).scheme.Opens) (a : Γ((twistSheafGradedAlgebra D).piece n, V)) :
    ((restrictionHom D (closedIdealDegreeZero D i)
          (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i)).app n).app V a
        = 0 ↔
      (restrictionToClosed i ((twistSheafGradedAlgebra D).piece n)).app V a = 0 := by
  rw [restrictionHom_app_eq_zero_iff]
  change a ∈ (generatedByDegree (twistSheafGradedAlgebra D)
    (closedIdealDegreeZero D i) n).toSubmodule.obj (op V) ↔ _
  rw [generatedByDegree_closedIdealDegreeZero_eq D i n,
    ← Stacks.Algebraization.kernelSubmodule_unit_app_eq_idealMultiple
      ((twistSheafGradedAlgebra D).piece n) i]
  exact AlgebraicGeometry.mem_kernelSubmodule_iff _ V a

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
