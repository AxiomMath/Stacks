module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AffineExtensionCore
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.CategoryTheory.Abelian.GraphKernelAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a module of finite presentation from a quasi-compact open of an affine space

Let `V` be an affine algebraic space, `j : P ⟶ V` an open immersion with `P` quasi-compact, `F` a
quasi-coherent `𝒪_V`-module, `G_P` an `𝒪_P`-module of finite presentation with `ψ : G_P ⟶ F|_P`,
and `m` a global section of `F` whose restriction to `P` comes from a global section `g` of
`G_P`.  `AlgebraicGeometry.Space.exists_isFinitePresentation_extension_of_isAffineSpace` extends
`G_P`, compatibly with `ψ`, to an `𝒪_V`-module of finite presentation mapping to `F` and hitting
`m`.  This is the affine step of EGA IV 1.7.7 (compare Stacks 01PI), in the form used by the
proof of Stacks 07V9.

## The proof

1. *The graph kernel.*  `Q = ker(F ⊞ j_*G_P ⟶ j_*(F|_P))`, the difference of the unit of the
   adjunction `j^* ⊣ j_*` and of `j_*ψ`, restricts to `G_P` over `P` compatibly with the maps to
   `F|_P`, because the counit is invertible along an open immersion
   (`Stacks.GraphKernel.graphKernelPullbackIso_hom_comp`).  It is quasi-coherent: `j` is
   quasi-compact (its target is affine and its source quasi-compact,
   `AlgebraicGeometry.Space.AffineExtension.isQuasiCompact_of_isAffineSpace`) and quasi-separated
   (a monomorphism), so Stacks 03M9 applies to the two direct images.  The pair `(m, g)` is a
   global section `q` of `Q` mapping to `m`; it is built from morphisms out of the unit modules
   through the adjunction, the hypothesis on `g` being exactly the compatibility needed.
2. *The affine step.*  `P` has a surjective étale chart `W` with affine underlying scheme, over
   which the sections of `Q|_P ≅ G_P` are finitely presented.  The terminal chart of `V` is affine,
   so `AlgebraicGeometry.Space.AffineExtension.exists_isFinitePresentation_bijective_of_isTerminal`
   gives `H` of finite presentation and `H ⟶ Q` hitting `q` and bijective on the sections over
   every affine chart of `V` mapping to `W`.
3. *Comparison over `P`.*  Every affine chart of `P` with a map to `W` gives such a chart of `V`,
   and these charts cover `P`, so `H|_P ⟶ Q|_P` is an isomorphism
   (`AlgebraicGeometry.Space.AffineExtension.isIso_of_bijective_app_of_coversTop`).

## References

* [Stacks Project, Tag 01PI](https://stacks.math.columbia.edu/tag/01PI)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Along an open immersion `j : P ⟶ V` with `P` quasi-compact and `V` affine, the graph kernel of
`ψ : G_P ⟶ F|_P` is quasi-coherent when `F` is quasi-coherent and `G_P` is of finite
presentation. -/
theorem isQuasicoherentOnSite_graphKernel_of_isAffineSpace
    {V P : AlgebraicSpaces B S hS} (hV : IsAffineSpace B S hS V.1) (j : P ⟶ V)
    (hj : IsOpenImmersion B S hS j.hom) (hP : IsQuasiCompactSpace B S hS P.1)
    (F : Modules.{u, u} B S hS V.1 V.2) (hF : F.IsQuasicoherentOnSite)
    (GP : Modules.{u, u} B S hS P.1 P.2) (hGP : GP.IsFinitePresentation)
    (ψ : GP ⟶ (etaleModulePullback.{u, u} B S hS j (isEtale_of_isOpenImmersion B S hS hj)).obj F) :
    (Stacks.GraphKernel.graphKernel
      (etaleModulePullbackAdjunction B S hS j (isEtale_of_isOpenImmersion B S hS hj)) F ψ
      ).IsQuasicoherentOnSite := by
  have hje : IsEtale B S hS j.hom := isEtale_of_isOpenImmersion B S hS hj
  have hjqc : IsQuasiCompact B S hS j.hom :=
    AffineExtension.isQuasiCompact_of_isAffineSpace B S hS P.2 hP hV j.hom
  have hjqs : IsQuasiSeparated B S hS j.hom :=
    isQuasiSeparated_of_mono B S hS j.hom (mono_of_presheaf_isOpenImmersion hj)
  exact (isQuasicoherentOnSite_kernel_and_cokernel B S hS V.1 V.2
    (Stacks.GraphKernel.graphKernelMap
      (etaleModulePullbackAdjunction B S hS j hje) F ψ)
    (SheafOfModules.IsQuasicoherentOnSite.biprod
      (fun M _ _ a h => Stacks.SheafOfModules.hasGlobalPresentation_overMap M a h) hF
      (isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS j hjqc hjqs GP
        (Stacks.SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentation GP)))
    (isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS j hjqc hjqs _
      (isQuasicoherentOnSite_etaleModulePullback B S hS j hje F hF))).1

/-- Along an open immersion `j : P ⟶ V` with `P` quasi-compact, the restriction of the unit module
of `V` is identified with the unit module of `P`, compatibly with restricting global sections. -/
theorem exists_isIso_unit_comparison {V P : AlgebraicSpaces B S hS} (j : P ⟶ V)
    (hj : IsOpenImmersion B S hS j.hom) (hP : IsQuasiCompactSpace B S hS P.1) :
    ∃ κ : SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS P.1 P.2).O) ⟶
        (etaleModulePullback.{u, u} B S hS j (isEtale_of_isOpenImmersion B S hS hj)).obj
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O)),
      IsIso κ ∧ ∀ (M : Modules.{u, u} B S hS V.1 V.2) (s : M.val.sections),
        ((etaleModulePullback.{u, u} B S hS j (isEtale_of_isOpenImmersion B S hS hj)).obj
          M).unitHomEquiv (κ ≫ (etaleModulePullback.{u, u} B S hS j
            (isEtale_of_isOpenImmersion B S hS hj)).map (M.unitHomEquiv.symm s)) =
          restrictSections B S hS j (isEtale_of_isOpenImmersion B S hS hj) s := by
  have hje : IsEtale B S hS j.hom := isEtale_of_isOpenImmersion B S hS hj
  let L := etaleModulePullback.{u, u} B S hS j hje
  obtain ⟨U, a, -, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS P.1 P.2).mp hP
  have hWcov := SmallEtale.coversTop_of_isSurjective B S hS P.1 P.2
    ⟨CostructuredArrow.mk a, presheaf_etale_of_isEtale B S hS haet⟩
    (isSurjective_of_presheafSurjective B S hS a hasurj)
  let OV := SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O)
  let κ := (L.obj OV).unitHomEquiv.symm (restrictSections B S hS j hje (OV.unitHomEquiv (𝟙 OV)))
  refine ⟨κ, ?_, fun M s => ?_⟩
  · refine AffineExtension.isIso_of_bijective_app_of_coversTop B S hS P.2 hWcov κ
      fun A _ _ => ?_
    have hid : ∀ b, κ.val.app (op A) b = b := fun b =>
      (AffineExtension.unitHomEquiv_symm_val_app _ _ (op A) b).trans
        (mul_one (M := chartRing B S hS P.1 P.2 A) b)
    exact ⟨fun b b' hbb => by rwa [hid, hid] at hbb, fun b => ⟨b, hid b⟩⟩
  · rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
    show restrictSections B S hS j hje (M.unitHomEquiv (𝟙 OV ≫ M.unitHomEquiv.symm s)) = _
    rw [Category.id_comp, Equiv.apply_symm_apply]

/-- Along an open immersion `j : P ⟶ V` with `P` quasi-compact, a global section `m` of `F` whose
restriction to `P` is the image of a global section of `G_P` under `ψ : G_P ⟶ F|_P` lifts to a
global section of the graph kernel of `ψ`. -/
theorem exists_graphKernel_sections_lift {V P : AlgebraicSpaces B S hS} (j : P ⟶ V)
    (hj : IsOpenImmersion B S hS j.hom) (hP : IsQuasiCompactSpace B S hS P.1)
    (F : Modules.{u, u} B S hS V.1 V.2) (GP : Modules.{u, u} B S hS P.1 P.2)
    (ψ : GP ⟶ (etaleModulePullback.{u, u} B S hS j (isEtale_of_isOpenImmersion B S hS hj)).obj F)
    (m : F.val.sections) (g : GP.val.sections)
    (hg : PresheafOfModules.sectionsMap ψ.val g =
      restrictSections B S hS j (isEtale_of_isOpenImmersion B S hS hj) m) :
    ∃ q : (Stacks.GraphKernel.graphKernel
        (etaleModulePullbackAdjunction B S hS j (isEtale_of_isOpenImmersion B S hS hj)) F ψ
        ).val.sections,
      PresheafOfModules.sectionsMap (Stacks.GraphKernel.graphKernelProjection
        (etaleModulePullbackAdjunction B S hS j (isEtale_of_isOpenImmersion B S hS hj)) F ψ).val
        q = m := by
  let L := etaleModulePullback.{u, u} B S hS j (isEtale_of_isOpenImmersion B S hS hj)
  let R := modulePushforward B S hS j
  let adj := etaleModulePullbackAdjunction B S hS j (isEtale_of_isOpenImmersion B S hS hj)
  let Q := Stacks.GraphKernel.graphKernel adj F ψ
  let p : Q ⟶ F := Stacks.GraphKernel.graphKernelProjection adj F ψ
  obtain ⟨κ, hκiso, hκs⟩ := exists_isIso_unit_comparison B S hS j hj hP
  let mh := F.unitHomEquiv.symm m
  let gh := GP.unitHomEquiv.symm g
  have hκm : κ ≫ L.map mh = gh ≫ ψ := (L.obj F).unitHomEquiv.injective <| by
    rw [hκs F m, SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
    exact hg.symm
  let x := adj.homEquiv _ _ (inv κ ≫ gh)
  have hx : mh ≫ adj.unit.app F = x ≫ R.map ψ := by
    have h1 : x ≫ R.map ψ = adj.homEquiv _ _ ((inv κ ≫ gh) ≫ ψ) :=
      (adj.homEquiv_naturality_right _ _).symm
    rw [h1, Category.assoc, ← hκm, IsIso.inv_hom_id_assoc, adj.homEquiv_unit,
      adj.unit_naturality]
  let qh : _ ⟶ Q := kernel.lift (Stacks.GraphKernel.graphKernelMap adj F ψ)
    (biprod.lift mh x) (by
      rw [Stacks.GraphKernel.graphKernelMap, biprod.lift_desc, Preadditive.comp_neg, hx,
        add_neg_cancel])
  have hqp : qh ≫ p = mh := by
    show kernel.lift _ _ _ ≫ kernel.ι _ ≫ biprod.fst = mh
    rw [kernel.lift_ι_assoc, biprod.lift_fst]
  refine ⟨Q.unitHomEquiv qh, ?_⟩
  show F.unitHomEquiv (qh ≫ p) = m
  rw [hqp, Equiv.apply_symm_apply]

/-- **Extension of a module of finite presentation from a quasi-compact open subspace of an
affine algebraic space, through a map to a quasi-coherent module, hitting a global section.**
Let `V` be affine, `j : P ⟶ V` an open immersion with `P` quasi-compact, `F` a quasi-coherent
`𝒪_V`-module, `G_P` an `𝒪_P`-module of finite presentation with `ψ : G_P ⟶ F|_P`, and `m` a
global section of `F` whose restriction to `P` is the image of a global section `g` of `G_P`.
Then there is an `𝒪_V`-module `H` of finite presentation with `ψ_V : H ⟶ F`, an identification
`H|_P ≅ G_P` under which `ψ_V|_P` is `ψ`, and a global section of `H` mapping to `m`. -/
@[sga "6 0 2.5" "special case"]
theorem exists_isFinitePresentation_extension_of_isAffineSpace
    {V P : AlgebraicSpaces B S hS} (hV : IsAffineSpace B S hS V.1) (j : P ⟶ V)
    (hj : IsOpenImmersion B S hS j.hom) (hP : IsQuasiCompactSpace B S hS P.1)
    (F : Modules.{u, u} B S hS V.1 V.2) (hF : F.IsQuasicoherentOnSite)
    (GP : Modules.{u, u} B S hS P.1 P.2) (hGP : GP.IsFinitePresentation)
    (ψ : GP ⟶ (etaleModulePullback.{u, u} B S hS j (isEtale_of_isOpenImmersion B S hS hj)).obj F)
    (m : F.val.sections) (g : GP.val.sections)
    (hg : PresheafOfModules.sectionsMap ψ.val g =
      restrictSections B S hS j (isEtale_of_isOpenImmersion B S hS hj) m) :
    ∃ (H : Modules.{u, u} B S hS V.1 V.2) (_ : H.IsFinitePresentation) (ψV : H ⟶ F)
      (θ : (etaleModulePullback.{u, u} B S hS j (isEtale_of_isOpenImmersion B S hS hj)).obj H ≅ GP)
      (h : H.val.sections),
      θ.hom ≫ ψ = (etaleModulePullback.{u, u} B S hS j
          (isEtale_of_isOpenImmersion B S hS hj)).map ψV ∧
        PresheafOfModules.sectionsMap ψV.val h = m := by
  have hje : IsEtale B S hS j.hom := isEtale_of_isOpenImmersion B S hS hj
  let L := etaleModulePullback.{u, u} B S hS j hje
  let R := modulePushforward B S hS j
  have hLadd : L.Additive := etaleModulePullback_additive B S hS j hje
  have hLlim : PreservesFiniteLimits L := preservesFiniteLimits_etaleModulePullback B S hS j hje
  have hff := fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj
  have hRfull : R.Full := hff.full
  have hRfaith : R.Faithful := hff.faithful
  let adj := etaleModulePullbackAdjunction B S hS j hje
  let Q := Stacks.GraphKernel.graphKernel adj F ψ
  let p : Q ⟶ F := Stacks.GraphKernel.graphKernelProjection adj F ψ
  let e₀ : L.obj Q ≅ GP := Stacks.GraphKernel.graphKernelPullbackIso adj F ψ
  have he₀ : e₀.hom ≫ ψ = L.map p := Stacks.GraphKernel.graphKernelPullbackIso_hom_comp adj F ψ
  have hQqc : Q.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_graphKernel_of_isAffineSpace B S hS hV j hj hP F hF GP hGP ψ
  obtain ⟨q, hq⟩ := exists_graphKernel_sections_lift B S hS j hj hP F GP ψ m g hg
  obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS P.1 P.2).mp hP
  let W : SmallEtale B S hS P.1 := ⟨CostructuredArrow.mk a, presheaf_etale_of_isEtale B S hS haet⟩
  have hWcov := SmallEtale.coversTop_of_isSurjective B S hS P.1 P.2 W
    (isSurjective_of_presheafSurjective B S hS a hasurj)
  let Φ := smallEtalePostcomp B S hS j hje
  have hW'a : IsAffine ((SmallEtale.toOver B S hS V.1 ⋙ BigFppfOver.toScheme B S hS).obj
    (Φ.obj W)) := hUaff
  have hLQfp : (L.obj Q).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation _).prop_of_iso e₀.symm hGP
  have hfpW : Module.FinitePresentation (chartRing B S hS V.1 V.2 (Φ.obj W))
      (Q.val.obj (op (Φ.obj W))) :=
    module_finitePresentation_sections_of_isFinitePresentationOnSite (L.obj Q)
      (Stacks.SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentation (L.obj Q))
      (AffineExtension.isFinitePresentationOnSite_of_isFinitePresentation B S hS P.2 _ hLQfp)
      W hUaff
  obtain ⟨T, hTaff, ⟨e⟩⟩ := hV
  have hT₀a : IsAffine ((SmallEtale.toOver B S hS V.1 ⋙ BigFppfOver.toScheme B S hS).obj
    (AffineExtension.affineChart B S hS e)) := hTaff
  obtain ⟨H, hH, ψQ, h, hh, hbij⟩ :=
    AffineExtension.exists_isFinitePresentation_bijective_of_isTerminal B S hS V.2
      (AffineExtension.isTerminal_affineChart B S hS e) hT₀a Q hQqc hW'a hfpW q
  have hiso : IsIso (L.map ψQ) :=
    AffineExtension.isIso_of_bijective_app_of_coversTop B S hS P.2 hWcov (L.map ψQ)
      fun A hA ⟨f⟩ => hbij (Φ.obj A) hA ⟨Φ.map f⟩
  refine ⟨H, hH, ψQ ≫ p, asIso (L.map ψQ) ≪≫ e₀, h, ?_, ?_⟩
  · rw [Iso.trans_hom, asIso_hom, Category.assoc, he₀, ← Functor.map_comp]
  · show PresheafOfModules.sectionsMap p.val (PresheafOfModules.sectionsMap ψQ.val h) = m
    rw [hh, hq]

end AlgebraicGeometry.Space

end
