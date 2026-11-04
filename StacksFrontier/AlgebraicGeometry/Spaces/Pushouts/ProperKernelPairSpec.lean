module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleClopenPartFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverFromAffineChartsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraOverHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraSectionsCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded

/-!
# The relative spectrum `X'` of Stacks 0AGG

Let `g : Y ⟶ X` be a proper morphism of algebraic spaces over `S` with `X` locally Noetherian,
`R = Y ×_X Y` its kernel pair with projections `s, t : R ⟶ Y`, and `h = s ≫ g : R ⟶ X`. The
proof of Stacks 0AGG sets

`𝒜 = Equalizer(s♯, t♯ : g_* 𝒪_Y ⟶ h_* 𝒪_R)`, `X' = \underline{Spec}_X(𝒜)`,

and shows that `Y ⟶ X'` is the coequalizer of `s, t`. This file carries out the construction
and proves the finiteness of `X' ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.equalizerAlgebra`: the equalizer of two morphisms of
  algebra sheaves on the small étale site of an algebraic space, computed sectionwise.
* `AlgebraicGeometry.Space.kernelPairAlgebra`: the algebra `𝒜` above.
* `AlgebraicGeometry.Space.kernelPairSpec`: `X' = \underline{Spec}_X(𝒜)`, the bounded relative
  spectrum of Stacks 081W, with `AlgebraicGeometry.Space.kernelPairSpecπ : Y ⟶ X'` the morphism
  corresponding to the inclusion `𝒜 ⟶ g_* 𝒪_Y` and
  `AlgebraicGeometry.Space.kernelPairSpecCofork` the resulting cofork of `s, t`.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_equalizerAlgebra`: the equalizer of two
  morphisms of quasi-coherent algebra sheaves is quasi-coherent (its underlying module is a
  kernel, Stacks 03M1), so `𝒜` is quasi-coherent (with Stacks 03M9 for `g_* 𝒪_Y`, `h_* 𝒪_R`).
* `AlgebraicGeometry.Space.kernelPairSpecπ_equalizes`: `π` equalizes `s` and `t`.
* `AlgebraicGeometry.Space.isCoherent_pushforwardAlgebra`: `g_* 𝒪_Y` is coherent for `g` proper
  onto a locally Noetherian `X` (Stacks 08AR in degree `0`), and likewise `h_* 𝒪_R`
  (`AlgebraicGeometry.Space.isCoherent_pushforwardAlgebra_kernelPairOver`).
* `AlgebraicGeometry.Space.isFinite_kernelPairAlgebra`: `𝒜` is a finite `𝒪_X`-algebra: over an
  affine étale chart it is a submodule of the finite module `(g_* 𝒪_Y)(V)` over the Noetherian
  ring `𝒪_X(V)`.
* `AlgebraicGeometry.Space.isFinite_relativeSpecPointsπ`: the relative spectrum of a finite
  quasi-coherent algebra is finite over the base.
* `AlgebraicGeometry.Space.isFinite_kernelPairSpecToTarget`: clause (1) of Stacks 0AGG for `X'`.
* `AlgebraicGeometry.Space.properKernelPairCoequalizers_of_isColimit_kernelPairSpecCofork`:
  Stacks 0AGG, granted the coequalizer property of `X'`.

## What is not proved here

The coequalizer property of `X'` (the last two paragraphs of the source proof) is the hypothesis
`hcolim` of the last theorem. The source checks the two conditions of Stacks 0GHL for the diagram
`s, t : R ⇉ Y`. Condition (1) of the descent criterion of Stacks 0GHL, read for
the walking parallel pair, asks for an equivalence between the étale spaces over `X'` and the
pairs `(U_Y, U_R)` with *two* cartesian maps `U_R ⟶ U_Y` over `s` and `t`; such a pair is a
descent datum without its cocycle condition, and the comparison is not essentially surjective
in general (for `g = 𝟙` of a point, `U_Y = U_R` two points and the maps the identity and the
swap). The diagram has to be extended by `R ×_Y R` (the truncated Čech nerve of `π`) before
Stacks 0GG0 applies.

## Implementation notes

The equalizer is computed on sections, as the sub-presheaf of rings on which the two maps agree,
so that its sections are definitionally a subring of those of the source; the sheaf condition is
`Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget'` applied to that sub-presheaf. Its underlying
module is identified with the kernel of the difference of the two module maps by an explicit
limit cone, `AlgebraicGeometry.Space.AlgebraSheaf.isLimitUnderlyingModuleEqualizer`.

The size condition of the bounded relative spectrum is automatic: `𝒜` is a subalgebra of
`g_* 𝒪_Y`, which satisfies it for every `g`.

## References

* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 0GHL](https://stacks.math.columbia.edu/tag/0GHL)
* [Stacks Project, Tag 0GG0](https://stacks.math.columbia.edu/tag/0GG0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  {A C : AlgebraSheaf.{u, u} B S hS F hF} (φ ψ : A ⟶ C)

/-- The sections of `A` over `U` on which `φ` and `ψ` agree, as a subring. -/
abbrev equalizerSections (U : (SmallEtale B S hS F)ᵒᵖ) : Subring (A.right.obj.obj U) :=
  RingHom.eqLocus (φ.right.hom.app U).hom (ψ.right.hom.app U).hom

/-- The sections on which `φ` and `ψ` agree are stable under the restriction maps of `A`. -/
theorem map_mem_equalizerSections {U V : (SmallEtale B S hS F)ᵒᵖ} (i : U ⟶ V)
    {x : A.right.obj.obj U} (hx : x ∈ equalizerSections φ ψ U) :
    (A.right.obj.map i).hom x ∈ equalizerSections φ ψ V := by
  show (φ.right.hom.app V).hom ((A.right.obj.map i).hom x) =
    (ψ.right.hom.app V).hom ((A.right.obj.map i).hom x)
  rw [app_map φ i x, app_map ψ i x]
  exact congrArg (C.right.obj.map i).hom hx

/-- The presheaf of rings `U ↦ {a ∈ A(U) | φ a = ψ a}`, with the restriction maps of `A`. -/
def equalizerPresheaf : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (equalizerSections φ ψ U)
  map {U V} i := CommRingCat.ofHom
    (((A.right.obj.map i).hom.comp (equalizerSections φ ψ U).subtype).codRestrict
      (equalizerSections φ ψ V) fun a => map_mem_equalizerSections φ ψ i a.2)
  map_id U := by
    ext a
    change (A.right.obj.map (𝟙 U)).hom a.1 = a.1
    simp
  map_comp {U V W} i j := by
    ext a
    change (A.right.obj.map (i ≫ j)).hom a.1 =
      (A.right.obj.map j).hom ((A.right.obj.map i).hom a.1)
    simp

/-- The subfunctor of the sections of `A` on which `φ` and `ψ` agree. -/
def equalizerSubfunctor : Subfunctor A.sectionsPresheaf where
  obj U := {x | x ∈ equalizerSections φ ψ U}
  map i _ hx := map_mem_equalizerSections φ ψ i hx

/-- The equalizer presheaf is a sheaf of rings: in types it is the subfunctor of sections of
`A` on which `φ` and `ψ` agree, and a section of `A` on which they agree locally is one on which
they agree, the target being separated. -/
theorem isSheaf_equalizerPresheaf :
    Presheaf.IsSheaf (SmallEtale.topology B S hS F) (equalizerPresheaf φ ψ) := by
  refine Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget' _ _ ?_
  have hG : Presieve.IsSheaf (SmallEtale.topology B S hS F)
      (equalizerSubfunctor φ ψ).toFunctor := by
    refine ((equalizerSubfunctor φ ψ).isSheaf_iff A.isSheaf_sectionsPresheaf).2 ?_
    intro U s hs
    refine (C.isSheaf_sectionsPresheaf _ hs).isSeparatedFor.ext fun V f hf => ?_
    have hf' : (φ.right.hom.app (op V)).hom ((A.right.obj.map f.op).hom s) =
        (ψ.right.hom.app (op V)).hom ((A.right.obj.map f.op).hom s) := hf
    show (C.right.obj.map f.op).hom ((φ.right.hom.app U).hom s) =
      (C.right.obj.map f.op).hom ((ψ.right.hom.app U).hom s)
    rw [← app_map φ f.op s, ← app_map ψ f.op s]
    exact hf'
  exact Presieve.isSheaf_iso _ (NatIso.ofComponents (fun U => Iso.refl _) fun _ => rfl) hG

/-- **The equalizer of two morphisms of algebra sheaves.** Its sections over `U` are the
sections of `A` on which `φ` and `ψ` agree, and its structure-algebra map is that of `A`. -/
def equalizerAlgebra : AlgebraSheaf.{u, u} B S hS F hF where
  right := ⟨equalizerPresheaf φ ψ, isSheaf_equalizerPresheaf φ ψ⟩
  algebraMap U := (A.algebraMap U).codRestrict (equalizerSections φ ψ U) fun r => by
    change (φ.right.hom.app U).hom (A.algebraMap U r) = (ψ.right.hom.app U).hom (A.algebraMap U r)
    rw [φ.comm, ψ.comm]
  algebraMap_natural i r := Subtype.ext (A.algebraMap_natural i r)

/-- The inclusion of the equalizer. -/
def equalizerι : equalizerAlgebra φ ψ ⟶ A where
  right := ⟨{ app := fun U => CommRingCat.ofHom (equalizerSections φ ψ U).subtype
              naturality := fun _ _ _ => rfl }⟩
  comm _ _ := rfl

/-- The inclusion of the equalizer sends a section to its underlying section of `A`. -/
@[simp]
theorem equalizerι_app (U : (SmallEtale B S hS F)ᵒᵖ)
    (x : (equalizerAlgebra φ ψ).right.obj.obj U) :
    ((equalizerι φ ψ).right.hom.app U).hom x = x.1 :=
  rfl

/-- The inclusion of the equalizer equalizes `φ` and `ψ`. -/
theorem equalizerι_comp : equalizerι φ ψ ≫ φ = equalizerι φ ψ ≫ ψ := by
  refine Hom.ext (Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_)))
  ext x
  exact x.2

/-! ### Quasi-coherence of the equalizer -/

/-- The difference of the underlying module maps of `φ` and `ψ` vanishes on the equalizer. -/
theorem underlyingModuleMap_equalizerι_comp_sub :
    underlyingModuleMap (equalizerι φ ψ) ≫ (underlyingModuleMap φ - underlyingModuleMap ψ) =
      0 := by
  rw [Preadditive.comp_sub, sub_eq_zero]
  exact SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => x.2))

/-- The linear map into the sections of the equalizer induced by a map into the sections of
`A` which the difference of `φ` and `ψ` kills. -/
def equalizerLiftLinear {W : Modules.{u, u} B S hS F hF} (k : W ⟶ underlyingModule A)
    (hk : k ≫ (underlyingModuleMap φ - underlyingModuleMap ψ) = 0)
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    W.val.obj U →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.obj U]
      (underlyingModule (equalizerAlgebra φ ψ)).val.obj U where
  toFun x := ⟨k.val.app U x, by
    rw [Preadditive.comp_sub, sub_eq_zero] at hk
    exact congrArg (fun m : W ⟶ underlyingModule C => m.val.app U x) hk⟩
  map_add' x y := Subtype.ext (map_add (k.val.app U).hom x y)
  map_smul' r x := Subtype.ext ((k.val.app U).hom.map_smul r x)

/-- The morphism into the equalizer induced by a morphism into `A` which the difference of `φ`
and `ψ` kills. -/
def equalizerLift {W : Modules.{u, u} B S hS F hF} (k : W ⟶ underlyingModule A)
    (hk : k ≫ (underlyingModuleMap φ - underlyingModuleMap ψ) = 0) :
    W ⟶ underlyingModule (equalizerAlgebra φ ψ) :=
  show SheafOfModules.Hom _ _ from
  { val :=
    { app := fun U => ConcreteCategory.ofHom
        (C := ModuleCat ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O).obj.obj U))
        (equalizerLiftLinear φ ψ k hk U)
      naturality := fun {U V} i => by
        apply ModuleCat.hom_ext
        refine LinearMap.ext fun x => Subtype.ext ?_
        exact congrArg (fun m => m x) (congrArg ModuleCat.Hom.hom (k.val.naturality i)) } }

/-- **The underlying module of the equalizer is the kernel of the difference of the underlying
module maps.** -/
def isLimitUnderlyingModuleEqualizer :
    IsLimit (KernelFork.ofι (underlyingModuleMap (equalizerι φ ψ))
      (underlyingModuleMap_equalizerι_comp_sub φ ψ)) :=
  KernelFork.IsLimit.ofι _ _ (fun k hk => equalizerLift φ ψ k hk)
    (fun k hk => SheafOfModules.hom_ext
      (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => rfl)))
    (fun k hk m hm => by
      apply SheafOfModules.hom_ext
      refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact Subtype.ext (congrArg (fun n : _ ⟶ underlyingModule A => n.val.app U x) hm))

/-- **The equalizer of two morphisms of quasi-coherent algebra sheaves is quasi-coherent**: its
underlying module is the kernel of a morphism of quasi-coherent modules (Stacks 03M1). -/
theorem isQuasicoherent_equalizerAlgebra (hA : A.IsQuasicoherent) (hC : C.IsQuasicoherent) :
    (equalizerAlgebra φ ψ).IsQuasicoherent := by
  have : (underlyingModule A).IsQuasicoherentOnSite := hA
  have : (underlyingModule C).IsQuasicoherentOnSite := hC
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((kernelIsKernel _).conePointUniqueUpToIso (isLimitUnderlyingModuleEqualizer φ ψ))
    (isQuasicoherentOnSite_kernel_of_quasicoherent B S hS F hF _)

/-- The sections of the equalizer inject into those of `A`, so the equalizer of morphisms out of
a direct-image algebra has fewer sections than the cutoff over every chart. -/
theorem sectionsBelowCutoff_equalizerAlgebra {X : AlgebraicSpaces B S hS}
    {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ ψ : A ⟶ C)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A) :
    AlgebraSheaf.SectionsBelowCutoff B S hS (equalizerAlgebra φ ψ) := fun V =>
  lt_of_le_of_lt (Cardinal.mk_le_of_injective Subtype.val_injective) (hA V)

/-- Finiteness of the sections of the underlying module over `𝒪_F(V)` is finiteness of the
structure-algebra map at `V`: the two module structures on `A(V)` are both multiplication through
the structure-algebra map. -/
theorem finite_algebraMap_of_moduleFinite (A : AlgebraSheaf.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F)
    (h : Module.Finite (chartRing B S hS F hF V) (A.underlyingModule.val.obj (op V))) :
    RingHom.Finite (A.algebraMap (op V)) := by
  let := (A.algebraMap (op V)).toAlgebra
  obtain ⟨s, hs⟩ := h.fg_top
  let t : Set (A.right.obj.obj (op V)) := (s : Set (A.underlyingModule.val.obj (op V)))
  have key : ∀ y : A.underlyingModule.val.obj (op V),
      y ∈ Submodule.span (chartRing B S hS F hF V) (s : Set _) →
        (show A.right.obj.obj (op V) from y) ∈
          Submodule.span ((structureSheaf B S hS F hF).obj.obj (op V)) t := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul r y _ hy => exact Submodule.smul_mem _ r hy
  exact ⟨⟨s, Submodule.eq_top_iff'.2 fun x ↦ key x (hs ▸ Submodule.mem_top)⟩⟩

end AlgebraSheaf

/-! ### The relative spectrum of a finite algebra is finite -/

section FiniteRelativeSpec

variable {B S hS} {X : AlgebraicSpaces B S hS} (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)

/-- **The relative spectrum of a finite quasi-coherent algebra is finite over the base.** Over an
affine open `V` of an atlas `U ⟶ X`, an affine étale chart of `X`, the fibre of
`\underline{Spec}_X(𝒜) ⟶ X` is `Spec 𝒜(V) ⟶ V`, which is finite because `𝒜(V)` is a finite
`𝒪_X(V)`-algebra; finiteness being Zariski local on the target, the fibre over `U` is a finite
morphism of schemes, and finiteness descends along the surjective étale `U ⟶ X` (Stacks 03ZQ). -/
theorem isFinite_relativeSpecPointsπ (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A)
    (hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (relativeSpecPoints B S hS A))
    (hAq : A.IsQuasicoherent) (hfin : A.IsFinite) :
    IsFinite B S hS (relativeSpecPointsπ B S hS A) := by
  have hP := isAlgebraicSpace_relativeSpecPoints B S hS A hA hsheaf hAq
  obtain ⟨U, a, hs, he⟩ := X.2.exists_atlas
  let Uc : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk a, he⟩
  obtain ⟨V', hV'⟩ := AlgebraSheaf.exists_dominatingChart B S hS A Uc
  have hμ : max Cardinal.aleph0 (Cardinal.mk (A.right.obj.obj (op V'))) < B.cutoff :=
    max_lt B.aleph0_lt_cutoff (hA V')
  -- the affine opens of the atlas, as affine étale charts of `X`
  choose V u hu hurange hVaff using
    fun O => BigFppfOver.exists_affineOpen_restrict B S hS U O
  have hu' : ∀ O, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (u O)) := hu
  let Vc : ((BigFppfOver.toScheme B S hS).obj U).affineOpens → SmallEtale B S hS X.1 :=
    fun O => etaleChartOfIsEtale B S hS (yoneda.map (u O) ≫ Uc.obj.hom)
      (isEtale_yoneda_map_comp_of_isOpenImmersion B S hS Uc (u O))
  have hVc : ∀ O, IsAffine (chartScheme (Vc O)) := hVaff
  let π := relativeSpecPointsπ B S hS A
  have hpbU : IsPullback (pullback.fst π a) (pullback.snd π a) π a :=
    IsPullback.of_hasPullback π a
  have hpb : ∀ O, IsPullback (affineChartSpecToPoints B S hS A hA (Vc O)
      (exists_chartEval_eq B S hS A hAq (Vc O)))
      (yoneda.map (affineChartSpecHom B S hS A hA (Vc O))) π (yoneda.map (u O) ≫ a) :=
    fun O => isPullback_affineChartSpec B S hS A hA (Vc O)
      (injective_chartEval_of_isAffine B S hS A hAq (Vc O))
      (exists_chartEval_eq B S hS A hAq (Vc O))
  have hQp : ∀ O, _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (affineChartSpecHom B S hS A hA (Vc O))) := by
    intro O
    rw [toScheme_map_affineChartSpecHom]
    have : _root_.AlgebraicGeometry.IsFinite (Spec.map (chartAlgebraMap B S hS A (Vc O))) :=
      (_root_.AlgebraicGeometry.IsFinite.SpecMap_iff _).2 (hfin (Vc O) (hVaff O))
    exact inferInstanceAs (_root_.AlgebraicGeometry.IsFinite
      (Spec.map (chartAlgebraMap B S hS A (Vc O)) ≫ (chartScheme (Vc O)).isoSpec.inv))
  have hWsize : ∀ O, ((BigFppfOver.toScheme B S hS).obj
      (affineChartSpec B S hS A hA (Vc O))).size ≤
        max Cardinal.aleph0 (Cardinal.mk (A.right.obj.obj (op V'))) := by
    intro O
    show (Spec (A.right.obj.obj (op (Vc O)))).size ≤ _
    rw [Scheme.size_Spec]
    refine max_le_max le_rfl ?_
    let W : (chartScheme Uc).affineOpens :=
      ⟨((BigFppfOver.toScheme B S hS).map (u O)).opensRange,
        isAffineOpen_opensRange ((BigFppfOver.toScheme B S hS).map (u O))⟩
    obtain ⟨k, hk⟩ := hV' W
    have e := etaleChartIsoChartOpensOfIsOpenImmersion B S hS Uc (u O)
    calc Cardinal.mk (A.right.obj.obj (op (Vc O)))
        = Cardinal.mk (A.right.obj.obj (op ((chartOpens B S hS Uc).obj
            ((BigFppfOver.toScheme B S hS).map (u O)).opensRange))) :=
          Cardinal.mk_congr ((CategoryTheory.forget CommRingCat).mapIso
            (A.right.obj.mapIso e.op)).toEquiv.symm
      _ ≤ Cardinal.mk (A.right.obj.obj (op V')) := Cardinal.mk_le_of_surjective hk
  obtain ⟨Y₀, e, P, hP', hQP⟩ := exists_representing_over_of_openCover_of_size_le B S hS
    isZariskiLocalAtTarget_isFinite
    (BigFppfOver.isSheaf_pullback_yoneda_obj π a hsheaf X.2.isSheaf) (pullback.snd π a)
    hu' (fun y => by
      have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) := trivial
      rw [← iSup_affineOpens_eq_top] at hy
      obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact ⟨O, by rw [hurange O]; exact hO⟩)
    (fun O => IsPullback.of_right' (hpb O) hpbU) hQp hμ hWsize
  have hRI : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h2 : pullback.snd π a = e.hom ≫ yoneda.map P := by
    rw [← hP', Iso.hom_inv_id_assoc]
  exact (isFinite_iff_etaleLocal B S hS π hP X.2).2
    ⟨U, a, hs, he, isFinite_of_presheaf_isFinite
      (hf := by
        rw [h2]
        exact MorphismProperty.RespectsIso.precomp _ e.hom _
          ((presheaf_yoneda_map_iff B S hS inferInstance P).2 hQP))⟩

end FiniteRelativeSpec

/-! ### The relative spectrum of the equalizer of `s♯, t♯` -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section KernelPairSpec

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)

/-- The kernel pair `R = Y ×_X Y` of `g`, as an algebraic space over `X` through
`h = s ≫ g`. -/
abbrev kernelPairOver : Over X :=
  Over.mk (pullback.fst g g ≫ g)

/-- The first projection `s : R ⟶ Y`, as a morphism over `X`. -/
def kernelPairFstOver : kernelPairOver g ⟶ Over.mk g :=
  Over.homMk (pullback.fst g g)

/-- The second projection `t : R ⟶ Y`, as a morphism over `X`. -/
def kernelPairSndOver : kernelPairOver g ⟶ Over.mk g :=
  Over.homMk (pullback.snd g g) pullback.condition.symm

/-- The kernel pair `R = Y ×_X Y` with its two projections is a fibre product. -/
theorem isPullback_kernelPairOver :
    IsPullback (kernelPairFstOver g).left (kernelPairSndOver g).left g g :=
  IsPullback.of_hasPullback g g

/-- The `𝒪_X`-algebra map `s♯ : g_* 𝒪_Y ⟶ h_* 𝒪_R` induced by the first projection. It is
an irreducible definition so that the kernel does not unfold the direct-image map when it checks
statements about the equalizer below. -/
irreducible_def kernelPairFstMap :
    pushforwardAlgebra B S hS (Over.mk g) ⟶ pushforwardAlgebra B S hS (kernelPairOver g) :=
  pushforwardAlgebraMap B S hS (kernelPairFstOver g)

/-- The `𝒪_X`-algebra map `t♯ : g_* 𝒪_Y ⟶ h_* 𝒪_R` induced by the second projection. -/
irreducible_def kernelPairSndMap :
    pushforwardAlgebra B S hS (Over.mk g) ⟶ pushforwardAlgebra B S hS (kernelPairOver g) :=
  pushforwardAlgebraMap B S hS (kernelPairSndOver g)

/-- **The algebra `𝒜` of Stacks 0AGG**: the equalizer of the two `𝒪_X`-algebra maps
`s♯, t♯ : g_* 𝒪_Y ⟶ h_* 𝒪_R` induced by the projections of the kernel pair. -/
def kernelPairAlgebra : AlgebraSheaf.{u, u} B S hS X.1 X.2 :=
  AlgebraSheaf.equalizerAlgebra (kernelPairFstMap g) (kernelPairSndMap g)

/-- The inclusion `𝒜 ⟶ g_* 𝒪_Y`. -/
def kernelPairAlgebraι : kernelPairAlgebra g ⟶ pushforwardAlgebra B S hS (Over.mk g) :=
  AlgebraSheaf.equalizerι (kernelPairFstMap g) (kernelPairSndMap g)

/-- The inclusion `𝒜 ⟶ g_* 𝒪_Y` equalizes `s♯` and `t♯`. -/
theorem kernelPairAlgebraι_comp :
    kernelPairAlgebraι g ≫ kernelPairFstMap g = kernelPairAlgebraι g ≫ kernelPairSndMap g :=
  AlgebraSheaf.equalizerι_comp (kernelPairFstMap g) (kernelPairSndMap g)

variable {g}

/-- The morphism `h = s ≫ g : R ⟶ X` is proper when `g` is. -/
theorem isProper_kernelPairOver_hom (hg : IsProper B S hS g.hom) :
    IsProper B S hS (kernelPairOver g).hom.hom :=
  isProper_comp B S hS (pullback g g).property Y.property X.property _ _
    ((isProper_isStableUnderBaseChange B S hS).of_isPullback
      (IsPullback.of_hasPullback g g).flip hg) hg

/-- **`𝒜` is quasi-coherent**: `g_* 𝒪_Y` and `h_* 𝒪_R` are quasi-coherent by Stacks 03M9, `g`
and `h` being proper, and quasi-coherence passes to the equalizer by Stacks 03M1. -/
theorem isQuasicoherent_kernelPairAlgebra (hg : IsProper B S hS g.hom) :
    (kernelPairAlgebra g).IsQuasicoherent :=
  AlgebraSheaf.isQuasicoherent_equalizerAlgebra _ _
    (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS g hg.2.1.2
      (isQuasiSeparated_of_isSeparated B S hS hg.1))
    (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS (pullback.fst g g ≫ g)
      (isProper_kernelPairOver_hom hg).2.1.2
      (isQuasiSeparated_of_isSeparated B S hS (isProper_kernelPairOver_hom hg).1))

variable (g) in
/-- `𝒜` has fewer than the cutoff many sections over every chart, being a subalgebra of
`g_* 𝒪_Y`. -/
theorem sectionsBelowCutoff_kernelPairAlgebra :
    AlgebraSheaf.SectionsBelowCutoff B S hS (kernelPairAlgebra g) :=
  AlgebraSheaf.sectionsBelowCutoff_equalizerAlgebra _ _
    (sectionsBelowCutoff_pushforwardAlgebra B S hS (Over.mk g))

/-- `𝒜` as a quasi-coherent `𝒪_X`-algebra. -/
def kernelPairQuasicoherentAlgebra (hg : IsProper B S hS g.hom) : QuasicoherentAlgebra B S hS X :=
  ⟨kernelPairAlgebra g, isQuasicoherent_kernelPairAlgebra hg⟩

/-- **The space `X' = \underline{Spec}_X(𝒜)` of Stacks 0AGG**, affine over `X`. -/
def kernelPairSpec (hg : IsProper B S hS g.hom) : AffineOver B S hS X :=
  boundedRelativeSpec B S hS (kernelPairQuasicoherentAlgebra hg)
    (sectionsBelowCutoff_kernelPairAlgebra g)

/-- The identification of the direct image of `𝒪_{X'}` with `𝒜`. -/
def kernelPairSpecIso (hg : IsProper B S hS g.hom) :
    pushforwardAlgebra B S hS (kernelPairSpec hg).obj ≅ kernelPairAlgebra g :=
  pushforwardAlgebraBoundedRelativeSpecIso B S hS _ _

/-- The morphism `Y ⟶ X'` over `X`: under the mapping property of the relative spectrum it is
the inclusion `𝒜 ⟶ g_* 𝒪_Y`. -/
def kernelPairSpecπOver (hg : IsProper B S hS g.hom) : Over.mk g ⟶ (kernelPairSpec hg).obj :=
  (overHomEquivPushforwardAlgebraHom B S hS (Over.mk g) (kernelPairSpec hg)).symm
    ((kernelPairSpecIso hg).hom ≫ kernelPairAlgebraι g)

/-- The algebra map induced by `Y ⟶ X'` is the inclusion `𝒜 ⟶ g_* 𝒪_Y`, through the
identification of the direct image of `𝒪_{X'}` with `𝒜`. -/
theorem pushforwardAlgebraMap_kernelPairSpecπOver (hg : IsProper B S hS g.hom) :
    pushforwardAlgebraMap B S hS (kernelPairSpecπOver hg) =
      (kernelPairSpecIso hg).hom ≫ kernelPairAlgebraι g :=
  (overHomEquivPushforwardAlgebraHom B S hS (Over.mk g) (kernelPairSpec hg)).apply_symm_apply _

/-- The quotient morphism `π : Y ⟶ X'`. -/
def kernelPairSpecπ (hg : IsProper B S hS g.hom) : Y ⟶ (kernelPairSpec hg).obj.left :=
  (kernelPairSpecπOver hg).left

/-- The morphism `X' ⟶ X`. -/
def kernelPairSpecToTarget (hg : IsProper B S hS g.hom) : (kernelPairSpec hg).obj.left ⟶ X :=
  (kernelPairSpec hg).obj.hom

/-- The quotient morphism `π : Y ⟶ X'` followed by `X' ⟶ X` is `g`. -/
theorem kernelPairSpecπ_comp_toTarget (hg : IsProper B S hS g.hom) :
    kernelPairSpecπ hg ≫ kernelPairSpecToTarget hg = g :=
  Over.w (kernelPairSpecπOver hg)

/-- **`π` equalizes `s` and `t`.** Under the mapping property of the relative spectrum, the two
composites `R ⟶ X'` correspond to `𝒜 ⟶ g_* 𝒪_Y ⇉ h_* 𝒪_R`, which agree because `𝒜` is the
equalizer. -/
theorem kernelPairSpecπ_equalizes (hg : IsProper B S hS g.hom) :
    pullback.fst g g ≫ kernelPairSpecπ hg = pullback.snd g g ≫ kernelPairSpecπ hg := by
  have h : kernelPairFstOver g ≫ kernelPairSpecπOver hg =
      kernelPairSndOver g ≫ kernelPairSpecπOver hg := by
    refine (overHomEquivPushforwardAlgebraHom B S hS (kernelPairOver g)
      (kernelPairSpec hg)).injective ?_
    simp only [overHomEquivPushforwardAlgebraHom_apply, pushforwardAlgebraMap_comp,
      pushforwardAlgebraMap_kernelPairSpecπOver, Category.assoc, ← kernelPairFstMap_def,
      ← kernelPairSndMap_def, kernelPairAlgebraι_comp]
  exact congrArg CommaMorphism.left h

/-- The cofork `Y ⟶ X'` of the kernel pair of `g`. -/
abbrev kernelPairSpecCofork (hg : IsProper B S hS g.hom) :
    Cofork (pullback.fst g g) (pullback.snd g g) :=
  Cofork.ofπ (kernelPairSpecπ hg) (kernelPairSpecπ_equalizes hg)

/-- The relative spectrum `X'`, packaged as a coequalizer of the kernel pair once its cofork is
known to be a colimit. -/
def kernelPairSpecCoequalizer (hg : IsProper B S hS g.hom)
    (hcolim : IsColimit (kernelPairSpecCofork hg)) : KernelPairCoequalizer B S hS g where
  space := (kernelPairSpec hg).obj.left
  π := kernelPairSpecπ hg
  toTarget := kernelPairSpecToTarget hg
  fac := kernelPairSpecπ_comp_toTarget hg
  equalizes := kernelPairSpecπ_equalizes hg
  isColimit := hcolim

/-! ### Finiteness of `𝒜` over `𝒪_X` (Stacks 08AR) -/

attribute [local instance 5000] SheafOfModules.instAbelian

variable (g) in
/-- **`g_* 𝒪_Y` is coherent** for `g` proper onto a locally Noetherian `X`, by Stacks 08AR
(`AlgebraicGeometry.Space.isCoherent_higherDirectImage_of_isProper`) in degree `0`: `Y` is
locally Noetherian, being of finite type over `X`, so `𝒪_Y` is coherent (Stacks 07UB), and
`R^0 g_* = g_*`. -/
theorem isCoherent_pushforwardAlgebra (hg : IsProper B S hS g.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    IsCoherent B S hS X.1 X.2 (pushforwardAlgebra B S hS (Over.mk g)).underlyingModule := by
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  have hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Y.2 X.2 g.hom hg.2.1.1 hX
  have : Fact (HasEtaleLocalProperty B S hS Y.1
    (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) := ⟨hY⟩
  have h := isCoherent_higherDirectImage_of_isProper B S hS g hg hX _
    (isCoherent_structureSheaf B S hS Y.1 Y.2) 0
  rw [underlyingModule_pushforwardAlgebra]
  exact isCoherent_of_iso B S hS X.2
    ((modulePushforward B S hS g).rightDerivedZeroIsoSelf.app _) h

variable (g) in
/-- **`h_* 𝒪_R` is coherent** for `g` proper onto a locally Noetherian `X`, where
`h = s ≫ g : R = Y ×_X Y ⟶ X`: `h` is proper, so this is `isCoherent_pushforwardAlgebra` for
`h`. -/
theorem isCoherent_pushforwardAlgebra_kernelPairOver (hg : IsProper B S hS g.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    IsCoherent B S hS X.1 X.2 (pushforwardAlgebra B S hS (kernelPairOver g)).underlyingModule :=
  isCoherent_pushforwardAlgebra (pullback.fst g g ≫ g) (isProper_kernelPairOver_hom hg) hX

/-- **`𝒜` is a finite `𝒪_X`-algebra**: over an affine étale chart `V` of `X`, `𝒜(V)` is an
`𝒪_X(V)`-submodule of the finite module `(g_* 𝒪_Y)(V)` over the Noetherian ring `𝒪_X(V)`. -/
theorem isFinite_kernelPairAlgebra (hg : IsProper B S hS g.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    (kernelPairAlgebra g).IsFinite := by
  intro V hV
  have : IsAffine (chartScheme V) := hV
  have hC : RingHom.Finite ((pushforwardAlgebra B S hS (Over.mk g)).algebraMap (op V)) :=
    AlgebraSheaf.finite_algebraMap_of_moduleFinite _ V
      (moduleFinite_sections_of_isCoherent B S hS X.1 X.2 _
        (isCoherent_pushforwardAlgebra g hg hX) hV)
  have : IsLocallyNoetherian (chartScheme V) := isLocallyNoetherian_chartScheme B S hS X hX V
  have : IsNoetherianRing ((structureSheaf B S hS X.1 X.2).obj.obj (op V)) :=
    IsLocallyNoetherian.component_noetherian (X := chartScheme V)
      ⟨⊤, isAffineOpen_top (chartScheme V)⟩
  let := ((pushforwardAlgebra B S hS (Over.mk g)).algebraMap (op V)).toAlgebra
  let := ((kernelPairAlgebra g).algebraMap (op V)).toAlgebra
  have : Module.Finite ((structureSheaf B S hS X.1 X.2).obj.obj (op V))
      ((pushforwardAlgebra B S hS (Over.mk g)).right.obj.obj (op V)) := hC
  have := isNoetherian_of_isNoetherianRing_of_finite
    ((structureSheaf B S hS X.1 X.2).obj.obj (op V))
    ((pushforwardAlgebra B S hS (Over.mk g)).right.obj.obj (op V))
  let L : (kernelPairAlgebra g).right.obj.obj (op V)
      →ₗ[(structureSheaf B S hS X.1 X.2).obj.obj (op V)]
        (pushforwardAlgebra B S hS (Over.mk g)).right.obj.obj (op V) :=
    { toFun := fun a => ((kernelPairAlgebraι g).right.hom.app (op V)).hom a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => map_mul _ _ a }
  exact Module.Finite.of_injective L Subtype.val_injective

/-- **Clause (1) of Stacks 0AGG for `X'`**: `X' = \underline{Spec}_X(𝒜) ⟶ X` is finite. -/
theorem isFinite_kernelPairSpecToTarget (hg : IsProper B S hS g.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    IsFinite B S hS (kernelPairSpecToTarget hg).hom :=
  isFinite_relativeSpecPointsπ (kernelPairAlgebra g) (sectionsBelowCutoff_kernelPairAlgebra g)
    (isSheaf_relativeSpecPoints B S hS (kernelPairAlgebra g)) (isQuasicoherent_kernelPairAlgebra hg)
    (isFinite_kernelPairAlgebra hg hX)

end KernelPairSpec

/-! ### Stacks 0AGG, granted the coequalizer property of `X'` -/

/-- **Stacks 0AGG**, granted one input: the coequalizer property of the relative spectrum
`X' = \underline{Spec}_X(𝒜)` of the equalizer `𝒜` of
`s♯, t♯ : g_* 𝒪_Y ⟶ h_* 𝒪_R`, as `hcolim`. Everything else is proved: `X'` and `π : Y ⟶ X'` are
constructed, `π` equalizes the two projections of the kernel pair, `X' ⟶ X` is finite, and
clauses (2) to (5) hold for every coequalizer of the kernel pair
(`AlgebraicGeometry.Space.properKernelPairCoequalizers_of_exists_isFinite`).

`hcolim` is the last paragraph of the source proof: it goes through Stacks 0GHL, whose
condition (1) is the effectivity and full faithfulness of étale descent along the proper
surjective `π` (Stacks 0GG0 and 0GFW), and whose condition (2) is the computation of maps from
an affine étale chart of `X'` to an affine scheme (Properties of Spaces, Lemma 66.33.1, the
relative form of Stacks 05Z1). -/
theorem properKernelPairCoequalizers_of_isColimit_kernelPairSpecCofork
    (hcolim : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
      HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
      ∀ hg : IsProper B S hS g.hom, Nonempty (IsColimit (kernelPairSpecCofork hg))) :
    ProperKernelPairCoequalizers B S hS :=
  properKernelPairCoequalizers_of_exists_isFinite B S hS fun g hX hg =>
    let ⟨hc⟩ := hcolim g hX hg
    ⟨kernelPairSpecCoequalizer hg hc, isFinite_kernelPairSpecToTarget hg hX⟩

end AlgebraicGeometry.Space
