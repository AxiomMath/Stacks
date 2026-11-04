module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleComap
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeSubmoduleEtaleChartAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective

/-!
# The induction step for dominating a finite type submodule over an étale chart

Let `(Uo ⊆ W, f : V ⟶ W)` be an elementary distinguished square of algebraic spaces with `W`
quasi-compact and quasi-separated, `Uo` quasi-compact and `V` affine.  This file proves that if
every finite type submodule of a quasi-coherent module restricted to a quasi-compact algebraic
space étale over `Uo`, respectively over `V`, is dominated by a finite type quasi-coherent
submodule of the module, then the same holds over `W`.

## Main definitions

* `AlgebraicGeometry.Space.DominationProperty`: the domination property of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.dominationProperty_of_isAffineSpace`: the affine case.
* `AlgebraicGeometry.Space.dominationProperty_of_isElementaryDistinguishedSquare`: the step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transport of finiteness along the comparisons of restricted submodules -/

/-- The restriction of a finite type quasi-coherent submodule along an étale morphism is a
finite type quasi-coherent submodule. -/
theorem isQuasicoherentOnSite_isFiniteType_etaleSubmoduleRestrict {X Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ X) (hg : IsEtale B S hS g.hom) {M : Modules.{u, u} B S hS X.1 X.2}
    (K : M.Submodule) (hq : K.toSheafOfModules.IsQuasicoherentOnSite)
    (hf : K.toSheafOfModules.IsFiniteType) :
    (etaleSubmoduleRestrict B S hS g hg K).toSheafOfModules.IsQuasicoherentOnSite ∧
      (etaleSubmoduleRestrict B S hS g hg K).toSheafOfModules.IsFiniteType :=
  ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
      (etaleSubmoduleRestrictIso B S hS g hg K).symm
      (isQuasicoherentOnSite_etaleModulePullback B S hS g hg _ hq),
    isFiniteType_of_iso' B S hS (etaleSubmoduleRestrictIso B S hS g hg K).symm
      (isFiniteType_etaleModulePullback B S hS g hg _ hf)⟩

/-- The restriction of a finite type submodule of `M|_Z` along an étale `k : Y ⟶ Z` over `X` is
of finite type. -/
theorem isFiniteType_etaleSubmoduleAlong {X Y Z : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS X.1 X.2} (k : Y ⟶ Z) (hk : IsEtale B S hS k.hom) (h : Z ⟶ X)
    (hh : IsEtale B S hS h.hom) (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS h hh).obj M).Submodule)
    (hN : N.toSheafOfModules.IsFiniteType) :
    (etaleSubmoduleAlong B S hS k hk h hh hkh N).toSheafOfModules.IsFiniteType :=
  isFiniteType_of_iso' B S hS (etaleSubmoduleAlongIso B S hS k hk h hh hkh N).symm
    (isFiniteType_etaleModulePullback B S hS k hk _ hN)

/-- Finite type is unchanged by reading a submodule of an étale pullback along a composite as a
submodule of the iterated étale pullback. -/
theorem isFiniteType_etaleSubmoduleCompToIter {X Y Z : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS X.1 X.2} (k : Y ⟶ Z) (hk : IsEtale B S hS k.hom) (h : Z ⟶ X)
    (hh : IsEtale B S hS h.hom) (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS (k ≫ h) hkh).obj M).Submodule)
    (hN : N.toSheafOfModules.IsFiniteType) :
    (etaleSubmoduleCompToIter B S hS k hk h hh hkh N).toSheafOfModules.IsFiniteType :=
  isFiniteType_of_iso' B S hS (etaleSubmoduleCompToIterIso B S hS k hk h hh hkh N).symm hN

/-- Containment of submodules of an étale pullback is unchanged by transport along an equality
of étale morphisms. -/
theorem etaleSubmoduleCongr_le_iff {X Y : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS X.1 X.2}
    {a b : Y ⟶ X} (hab : a = b) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (N N' : ((etaleModulePullback.{u, u} B S hS a ha).obj M).Submodule) :
    etaleSubmoduleCongr B S hS hab ha hb N ≤ etaleSubmoduleCongr B S hS hab ha hb N' ↔ N ≤ N' := by
  subst hab
  exact Iff.rfl

/-- Containment of submodules is unchanged by reading them along a composite. -/
theorem etaleSubmoduleIterToComp_le_iff {X Y Z : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS X.1 X.2} (k : Y ⟶ Z) (hk : IsEtale B S hS k.hom) (h : Z ⟶ X)
    (hh : IsEtale B S hS h.hom) (hkh : IsEtale B S hS (k ≫ h).hom)
    (N N' : ((etaleModulePullback.{u, u} B S hS k hk).obj
      ((etaleModulePullback.{u, u} B S hS h hh).obj M)).Submodule) :
    etaleSubmoduleIterToComp B S hS k hk h hh hkh N ≤
      etaleSubmoduleIterToComp B S hS k hk h hh hkh N' ↔ N ≤ N' := Iff.rfl

/-- **The supremum of two finite type quasi-coherent submodules is of finite type and
quasi-coherent**: it is the least upper bound produced by
`AlgebraicGeometry.Space.exists_submodule_sup_isQuasicoherentOnSite_isFiniteType`. -/
theorem isQuasicoherentOnSite_isFiniteType_sup {X : AlgebraicSpaces B S hS}
    {H : Modules.{u, u} B S hS X.1 X.2} (hH : H.IsQuasicoherentOnSite) (K₁ K₂ : H.Submodule)
    (h₁ : K₁.toSheafOfModules.IsQuasicoherentOnSite ∧ K₁.toSheafOfModules.IsFiniteType)
    (h₂ : K₂.toSheafOfModules.IsQuasicoherentOnSite ∧ K₂.toSheafOfModules.IsFiniteType) :
    (K₁ ⊔ K₂).toSheafOfModules.IsQuasicoherentOnSite ∧
      (K₁ ⊔ K₂).toSheafOfModules.IsFiniteType := by
  obtain ⟨K, hK, hle₁, hle₂, hmin⟩ :=
    exists_submodule_sup_isQuasicoherentOnSite_isFiniteType B S hS hH K₁ K₂ h₁ h₂
  exact (le_antisymm (hmin _ le_sup_left le_sup_right) (sup_le hle₁ hle₂)) ▸ hK

/-! ### The domination property -/

/-- **The domination property of an algebraic space `W`**: every finite type submodule of the
restriction of a quasi-coherent `𝒪_W`-module to a quasi-compact algebraic space étale over `W`
is contained in the restriction of a finite type quasi-coherent submodule of the module. -/
def DominationProperty (W : AlgebraicSpaces B S hS) : Prop :=
  ∀ (F : Modules.{u, u} B S hS W.1 W.2), F.IsQuasicoherentOnSite →
    ∀ (Y : AlgebraicSpaces B S hS) (g : Y ⟶ W) (hg : IsEtale B S hS g.hom),
      IsQuasiCompactSpace B S hS Y.1 →
      ∀ G : ((etaleModulePullback.{u, u} B S hS g hg).obj F).Submodule,
        G.toSheafOfModules.IsFiniteType →
          ∃ K : F.Submodule, (K.toSheafOfModules.IsQuasicoherentOnSite ∧
            K.toSheafOfModules.IsFiniteType) ∧ G ≤ etaleSubmoduleRestrict B S hS g hg K

/-- **The affine case of the domination property**, which is
`AlgebraicGeometry.Space.exists_isFiniteType_le_etaleSubmoduleRestrict_of_isAffineSpace`. -/
theorem dominationProperty_of_isAffineSpace (W : AlgebraicSpaces B S hS)
    (hWa : IsAffineSpace B S hS W.1) : DominationProperty B S hS W :=
  fun _ hF _ g hg hYqc G hG =>
    exists_isFiniteType_le_etaleSubmoduleRestrict_of_isAffineSpace B S hS hWa hF g hg hYqc G hG

/-! ### Sections of a fibre product of presheaves -/

/-- A pair of sections of the two factors of a fibre product of presheaves with the same image
in the base comes from a section of the fibre product. -/
theorem exists_pullback_obj_of_app_eq {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H)
    (g : G ⟶ H) (O : BigFppfOver B S hS) (a : F.obj (op O)) (b : G.obj (op O))
    (hab : f.app (op O) a = g.app (op O) b) :
    ∃ e : (pullback f g).obj (op O),
      (pullback.fst f g).app (op O) e = a ∧ (pullback.snd f g).app (op O) e = b := by
  have h : yonedaEquiv.symm a ≫ f = yonedaEquiv.symm b ≫ g := by
    apply yonedaEquiv.injective
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine ⟨yonedaEquiv (pullback.lift _ _ h), ?_, ?_⟩
  · rw [← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]
  · rw [← yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-! ### The induction step -/

/-- **Transport of a containment across a commuting square of étale morphisms.**  For
`k ≫ h = k' ≫ h'` with all four morphisms étale, a submodule of `M|_Z` read over `Y` is
contained in one of `M|_{Z'}` read over `Y` as soon as the corresponding containment holds for
the iterated restrictions over `Z'`. -/
theorem etaleSubmoduleCongr_etaleSubmoduleAlong_le_etaleSubmoduleAlong
    {X Z Z' Y : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS X.1 X.2}
    (k : Y ⟶ Z) (hk : IsEtale B S hS k.hom) (h : Z ⟶ X) (hh : IsEtale B S hS h.hom)
    (hkh : IsEtale B S hS (k ≫ h).hom)
    (k' : Y ⟶ Z') (hk' : IsEtale B S hS k'.hom) (h' : Z' ⟶ X) (hh' : IsEtale B S hS h'.hom)
    (hk'h' : IsEtale B S hS (k' ≫ h').hom) (hcomm : k ≫ h = k' ≫ h')
    (N : ((etaleModulePullback.{u, u} B S hS h hh).obj M).Submodule)
    (N' : ((etaleModulePullback.{u, u} B S hS h' hh').obj M).Submodule)
    (hle : etaleSubmoduleCompToIter B S hS k' hk' h' hh' hk'h'
        (etaleSubmoduleCongr B S hS hcomm hkh hk'h'
          (etaleSubmoduleAlong B S hS k hk h hh hkh N)) ≤
      etaleSubmoduleRestrict B S hS k' hk' N') :
    etaleSubmoduleCongr B S hS hcomm hkh hk'h' (etaleSubmoduleAlong B S hS k hk h hh hkh N) ≤
      etaleSubmoduleAlong B S hS k' hk' h' hh' hk'h' N' := by
  have h2 := (etaleSubmoduleIterToComp_le_iff B S hS k' hk' h' hh' hk'h' _ _).2 hle
  rwa [etaleSubmoduleIterToComp_compToIter, etaleSubmoduleIterToComp_restrict] at h2

/-- If `Z` has the domination property, a finite type submodule of `M|_Y` read over `Y₁` and
transported to the iterated restriction along `c : Y₁ ⟶ Z` is dominated by the restriction of a
finite type quasi-coherent submodule of `M|_Z`. -/
private theorem exists_le_etaleSubmoduleRestrict_of_dominationProperty
    {X Y Z Y₁ : AlgebraicSpaces B S hS} {F : Modules.{u, u} B S hS X.1 X.2}
    {h : Z ⟶ X} {hh : IsEtale B S hS h.hom}
    (hFZ : ((etaleModulePullback.{u, u} B S hS h hh).obj F).IsQuasicoherentOnSite)
    (hP : DominationProperty B S hS Z) (a : Y₁ ⟶ Y) (ha : IsEtale B S hS a.hom) (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) (hag : IsEtale B S hS (a ≫ g).hom) (c : Y₁ ⟶ Z)
    (hc : IsEtale B S hS c.hom) (hch : IsEtale B S hS (c ≫ h).hom) (hcomm : a ≫ g = c ≫ h)
    (hY₁ : IsQuasiCompactSpace B S hS Y₁.1)
    (G : ((etaleModulePullback.{u, u} B S hS g hg).obj F).Submodule)
    (hG : G.toSheafOfModules.IsFiniteType) :
    ∃ K : ((etaleModulePullback.{u, u} B S hS h hh).obj F).Submodule,
      (K.toSheafOfModules.IsQuasicoherentOnSite ∧ K.toSheafOfModules.IsFiniteType) ∧
        etaleSubmoduleCompToIter B S hS c hc h hh hch
          (etaleSubmoduleCongr B S hS hcomm hag hch (etaleSubmoduleAlong B S hS a ha g hg hag G))
          ≤ etaleSubmoduleRestrict B S hS c hc K :=
  hP _ hFZ Y₁ c hc hY₁ _
    (isFiniteType_etaleSubmoduleCompToIter B S hS c hc h hh hch _
      ((isFiniteType_etaleSubmoduleCongr_iff B S hS hcomm hag hch _).2
        (isFiniteType_etaleSubmoduleAlong B S hS a ha g hg hag G hG)))

/-- **The induction step for the domination property.**  Let `(Uo ⊆ W, f : V ⟶ W)` be an
elementary distinguished square with `W` quasi-compact and quasi-separated, `Uo` quasi-compact
and `V` affine.  If `Uo` and `V` have the domination property, so does `W`. -/
theorem dominationProperty_of_isElementaryDistinguishedSquare (hZ : B.Contains (⊤_ Scheme.{u}))
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hUoqc : IsQuasiCompactSpace B S hS Uo.toFunctor) (hVa : IsAffineSpace B S hS V)
    (hPU : DominationProperty B S hS (openSubspaceSpace B S hS Uo hsq.isOpenSubspace))
    (hPV : DominationProperty B S hS (edsEtale B S hS hsq)) :
    DominationProperty B S hS W := by
  classical
  intro F hF Y g hg hYqc G hG
  have hUo := hsq.isOpenSubspace
  let j := openSubspaceHom B S hS Uo hUo
  have hj : IsEtale B S hS j.hom := isEtale_openSubspaceHom B S hS Uo hUo
  let f := edsEtaleHom B S hS hsq
  have hf : IsEtale B S hS f.hom := isEtale_edsEtaleHom B S hS hsq
  have hVqc : IsQuasiCompactSpace B S hS V := IsAffineSpace.isQuasiCompactSpace hVa
  have hfqc : IsQuasiCompact B S hS fV :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hWqs hVqc fV
  have hgqc : IsQuasiCompact B S hS g.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hWqs hYqc g.hom
  have hFU : ((etaleModulePullback.{u, u} B S hS j hj).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS j hj F hF
  have hFV : ((etaleModulePullback.{u, u} B S hS f hf).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS f hf F hF
  -- the quasi-compact open subspace `Y₀ = g⁻¹(Uo)` of `Y`, étale over `Uo`
  let Y₀ : Subfunctor Y.1 := Uo.preimage g.hom
  have hY₀ : IsOpenSubspace B S hS Y₀ := isOpenSubspace_preimage B S hS g.hom Uo W.2 Y.2 hUo
  have hY₀qc : IsQuasiCompactSpace B S hS Y₀.toFunctor :=
    isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS W.2 Y.2 g.hom hgqc hUo hUoqc
  let ι : openSubspaceSpace B S hS (W := Y) Y₀ hY₀ ⟶ Y :=
    openSubspaceHom B S hS (W := Y) Y₀ hY₀
  have hι : IsEtale B S hS ι.hom := isEtale_openSubspaceHom B S hS (W := Y) Y₀ hY₀
  let σ : openSubspaceSpace B S hS (W := Y) Y₀ hY₀ ⟶ openSubspaceSpace B S hS Uo hUo :=
    ObjectProperty.homMk (Uo.fromPreimage g.hom)
  have e : σ ≫ j = ι ≫ g := ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι Uo g.hom)
  have hιg : IsEtale B S hS (ι ≫ g).hom := isEtale_comp B S hS hι hg
  have hσj : IsEtale B S hS (σ ≫ j).hom := e ▸ hιg
  have hσ : IsEtale B S hS σ.hom :=
    @isEtale_of_comp_mono B S hS _ _ _ σ.hom Uo.ι (Subfunctor.instMonoFunctorTypeι Uo) hσj
  -- the quasi-compact open subspace `V₀ = f⁻¹(Uo)` of `V`, étale over `Uo`
  let V₀ : Subfunctor (edsEtale B S hS hsq).1 := Uo.preimage fV
  have hV₀ : IsOpenSubspace B S hS V₀ :=
    isOpenSubspace_preimage B S hS fV Uo W.2 hsq.isAlgebraicSpace hUo
  have hV₀qc : IsQuasiCompactSpace B S hS V₀.toFunctor :=
    isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS W.2 hsq.isAlgebraicSpace fV hfqc hUo
      hUoqc
  let ι₁ : openSubspaceSpace B S hS (W := edsEtale B S hS hsq) V₀ hV₀ ⟶ edsEtale B S hS hsq :=
    openSubspaceHom B S hS (W := edsEtale B S hS hsq) V₀ hV₀
  have hι₁ : IsEtale B S hS ι₁.hom :=
    isEtale_openSubspaceHom B S hS (W := edsEtale B S hS hsq) V₀ hV₀
  let σ₁ : openSubspaceSpace B S hS (W := edsEtale B S hS hsq) V₀ hV₀ ⟶
      openSubspaceSpace B S hS Uo hUo := ObjectProperty.homMk (Uo.fromPreimage fV)
  have e₁ : σ₁ ≫ j = ι₁ ≫ f := ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι Uo fV)
  have hι₁f : IsEtale B S hS (ι₁ ≫ f).hom := isEtale_comp B S hS hι₁ hf
  have hσ₁j : IsEtale B S hS (σ₁ ≫ j).hom := e₁ ▸ hι₁f
  have hσ₁ : IsEtale B S hS σ₁.hom :=
    @isEtale_of_comp_mono B S hS _ _ _ σ₁.hom Uo.ι (Subfunctor.instMonoFunctorTypeι Uo) hσ₁j
  -- the fibre product `P = Y ×_W V`, étale over both factors
  have hPalg : IsAlgebraicSpace B S hS (pullback fV g.hom) :=
    isAlgebraicSpace_pullback B S hS fV g.hom hsq.isAlgebraicSpace Y.2 W.2
  have hPqc : IsQuasiCompactSpace B S hS (pullback fV g.hom) :=
    isQuasiCompactSpace_pullback B S hS hZ fV g.hom hsq.isAlgebraicSpace W.2 hVqc hYqc hWqs
  let q : (⟨pullback fV g.hom, hPalg⟩ : AlgebraicSpaces B S hS) ⟶ Y :=
    ObjectProperty.homMk (pullback.snd fV g.hom)
  have hq : IsEtale B S hS q.hom :=
    isEtale_pullback_snd B S hS Y.2 W.2 hsq.isAlgebraicSpace fV g.hom hsq.isEtale
  let r : (⟨pullback fV g.hom, hPalg⟩ : AlgebraicSpaces B S hS) ⟶ edsEtale B S hS hsq :=
    ObjectProperty.homMk (pullback.fst fV g.hom)
  have hr : IsEtale B S hS r.hom :=
    isEtale_pullback_fst B S hS hsq.isAlgebraicSpace W.2 Y.2 fV g.hom hg
  have eP : q ≫ g = r ≫ f := ObjectProperty.hom_ext _ pullback.condition.symm
  have hqg : IsEtale B S hS (q ≫ g).hom := isEtale_comp B S hS hq hg
  have hrf : IsEtale B S hS (r ≫ f).hom := eP ▸ hqg
  -- a finite type quasi-coherent submodule over `V` dominating `G` over `P`
  obtain ⟨B₀, hB₀, hB₀le⟩ := exists_le_etaleSubmoduleRestrict_of_dominationProperty B S hS hFV
    hPV q hq g hg hqg r hr hrf eP hPqc G hG
  -- a finite type quasi-coherent submodule over `Uo` dominating `G` over `Y₀`
  obtain ⟨A₁, hA₁, hA₁le⟩ := exists_le_etaleSubmoduleRestrict_of_dominationProperty B S hS hFU
    hPU ι hι g hg hιg σ hσ hσj e.symm hY₀qc G hG
  -- a finite type quasi-coherent submodule over `Uo` dominating `ℬ₀` over `V₀`
  obtain ⟨A₂, hA₂, hA₂le⟩ := exists_le_etaleSubmoduleRestrict_of_dominationProperty B S hS hFU
    hPU ι₁ hι₁ f hf hι₁f σ₁ hσ₁ hσ₁j e₁.symm hV₀qc B₀ hB₀.2
  have hA : (A₁ ⊔ A₂).toSheafOfModules.IsQuasicoherentOnSite ∧
      (A₁ ⊔ A₂).toSheafOfModules.IsFiniteType :=
    isQuasicoherentOnSite_isFiniteType_sup B S hS hFU A₁ A₂ hA₁ hA₂
  -- Stacks 0853: extend it to `W`
  obtain ⟨A', hA'q, hA'f, hA'⟩ := exists_etaleSubmodule_extension B S hS hZ W hWqc hWqs Uo hUo
    hUoqc F hF (A₁ ⊔ A₂) hA.1 hA.2
  -- `G` is dominated over `Y₀` by the restriction of `A'`
  have hGA : etaleSubmoduleAlong B S hS ι hι g hg hιg G ≤
      etaleSubmoduleRestrict B S hS (ι ≫ g) hιg A' := by
    rw [← etaleSubmoduleCongr_le_iff B S hS e.symm hιg hσj, etaleSubmoduleCongr_restrict,
      ← etaleSubmoduleAlong_restrict B S hS σ hσ j hj hσj A']
    exact etaleSubmoduleCongr_etaleSubmoduleAlong_le_etaleSubmoduleAlong B S hS ι hι g hg hιg
      σ hσ j hj hσj e.symm G _
      (hA₁le.trans (etaleSubmoduleRestrict_mono B S hS σ hσ (by rw [hA']; exact le_sup_left)))
  -- `ℬ₀` is dominated over `V₀` by the restriction of `A'`
  have hBA : etaleSubmoduleRestrict B S hS ι₁ hι₁ B₀ ≤
      etaleSubmoduleRestrict B S hS ι₁ hι₁ (etaleSubmoduleRestrict B S hS f hf A') := by
    rw [← etaleSubmoduleIterToComp_le_iff B S hS ι₁ hι₁ f hf hι₁f,
      etaleSubmoduleIterToComp_restrict B S hS ι₁ hι₁ f hf hι₁f B₀,
      etaleSubmoduleIterToComp_restrict B S hS ι₁ hι₁ f hf hι₁f
        (etaleSubmoduleRestrict B S hS f hf A'),
      etaleSubmoduleAlong_restrict B S hS ι₁ hι₁ f hf hι₁f A',
      ← etaleSubmoduleCongr_le_iff B S hS e₁.symm hι₁f hσ₁j, etaleSubmoduleCongr_restrict,
      ← etaleSubmoduleAlong_restrict B S hS σ₁ hσ₁ j hj hσ₁j A']
    exact etaleSubmoduleCongr_etaleSubmoduleAlong_le_etaleSubmoduleAlong B S hS ι₁ hι₁ f hf hι₁f
      σ₁ hσ₁ j hj hσ₁j e₁.symm B₀ _
      (hA₂le.trans (etaleSubmoduleRestrict_mono B S hS σ₁ hσ₁ (by rw [hA']; exact le_sup_right)))
  have hBres : etaleSubmoduleRestrict B S hS ι₁ hι₁ (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A') =
      etaleSubmoduleRestrict B S hS ι₁ hι₁ (etaleSubmoduleRestrict B S hS f hf A') :=
    etaleSubmoduleRestrict_sup_eq_right B S hS ι₁ hι₁ B₀ _ hBA
  have hBm : (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A').toSheafOfModules.IsQuasicoherentOnSite ∧
      (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A').toSheafOfModules.IsFiniteType :=
    isQuasicoherentOnSite_isFiniteType_sup B S hS hFV B₀ _ hB₀
      (isQuasicoherentOnSite_isFiniteType_etaleSubmoduleRestrict B S hS f hf A' hA'q hA'f)
  -- the germ sets of `ℬ` and of the restriction of `A'` to `Uo` agree over `Uo ×_W V`
  have hagree : EdsGermAgree B S hS hsq Uo hUo (etaleSubmoduleRestrict B S hS j hj A')
      (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A') := by
    intro x t u
    have hu := value_mem_of_geometricPointLift B S hS Uo hUo u
    have hmem : t.1 ∈ V₀.obj (op (x.val.siteObject B S hS W.1)) := by
      have h := t.2
      change fV.app _ t.1 = x.val.value at h
      show fV.app _ t.1 ∈ Uo.obj _
      rw [h]
      exact hu
    let t₁ : GeometricPointLift B S hS ι₁.hom (liftGeometricPoint B S hS f t) :=
      ⟨⟨t.1, hmem⟩, rfl⟩
    have halong : etaleSubmoduleAlong B S hS ι₁ hι₁ f hf hι₁f
        (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A') =
        etaleSubmoduleRestrict B S hS (ι₁ ≫ f) hι₁f A' := by
      rw [← etaleSubmoduleIterToComp_restrict B S hS ι₁ hι₁ f hf hι₁f
          (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A'), hBres,
        etaleSubmoduleIterToComp_restrict B S hS ι₁ hι₁ f hf hι₁f
          (etaleSubmoduleRestrict B S hS f hf A'),
        etaleSubmoduleAlong_restrict B S hS ι₁ hι₁ f hf hι₁f A']
    rw [etaleGermSet_etaleSubmoduleRestrict B S hS j hj A' u,
      ← etaleGermSet_along B S hS f hf ι₁ hι₁ hι₁f
        (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A') t t₁, halong,
      etaleGermSet_etaleSubmoduleRestrict B S hS (ι₁ ≫ f) hι₁f A']
  -- the glued submodule of `F`
  have hcompat := edsMemberSubmodule_compatible B S hS hsq Uo hUo le_rfl hagree
  have hKj := etaleSubmoduleRestrict_etaleSubmoduleGlue B S hS (edsMember B S hS hsq Uo hUo)
    (edsMemberHom B S hS hsq Uo hUo) (isEtale_edsMemberHom B S hS hsq Uo hUo) _ hcompat ⟨true⟩
  have hKf := etaleSubmoduleRestrict_etaleSubmoduleGlue B S hS (edsMember B S hS hsq Uo hUo)
    (edsMemberHom B S hS hsq Uo hUo) (isEtale_edsMemberHom B S hS hsq Uo hUo) _ hcompat ⟨false⟩
  have hcov : ∀ z : points B S hS W.1,
      z ∈ Set.range (pointsMap B S hS (openSubspaceSpace B S hS Uo hUo).1 j.hom) ∨
        z ∈ Set.range (pointsMap B S hS (edsEtale B S hS hsq).1 f.hom) := by
    intro z
    rcases points_covered_of_isElementaryDistinguishedSquare B S hS hsq z with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz
  obtain ⟨K, hKdef⟩ : ∃ K : F.Submodule, K = etaleSubmoduleGlue B S hS
      (edsMember B S hS hsq Uo hUo) (edsMemberHom B S hS hsq Uo hUo)
      (isEtale_edsMemberHom B S hS hsq Uo hUo)
      (edsMemberSubmodule B S hS hsq Uo hUo (etaleSubmoduleRestrict B S hS j hj A')
        (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A')) := ⟨_, rfl⟩
  have hKj' : etaleSubmoduleRestrict B S hS j hj K = etaleSubmoduleRestrict B S hS j hj A' := by
    rw [hKdef]
    exact hKj
  have hKf' : etaleSubmoduleRestrict B S hS f hf K =
      B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A' := by
    rw [hKdef]
    exact hKf
  refine ⟨K, ?_, ?_⟩
  · refine isQuasicoherentOnSite_isFiniteType_of_pair B S hS j f hj hf hcov K ?_ ?_
    · rw [hKj']
      exact isQuasicoherentOnSite_isFiniteType_etaleSubmoduleRestrict B S hS j hj A' hA'q hA'f
    · rw [hKf']
      exact hBm
  · -- the germ-set containments
    have hgermA : ∀ (x : GeometricPoint B S hS W.1) (t : GeometricPointLift B S hS j.hom x)
        (t' : GeometricPointLift B S hS g.hom x),
        etaleGermSet B S hS g hg G t' ⊆
          etaleGermSet B S hS j hj (etaleSubmoduleRestrict B S hS j hj A') t := by
      intro x t t'
      have hu := value_mem_of_geometricPointLift B S hS Uo hUo t
      have hmem : t'.1 ∈ Y₀.obj (op (x.val.siteObject B S hS W.1)) := by
        have h := t'.2
        change g.hom.app _ t'.1 = x.val.value at h
        show g.hom.app _ t'.1 ∈ Uo.obj _
        rw [h]
        exact hu
      let t₀ : GeometricPointLift B S hS ι.hom (liftGeometricPoint B S hS g t') :=
        ⟨⟨t'.1, hmem⟩, rfl⟩
      rw [etaleGermSet_etaleSubmoduleRestrict B S hS j hj A' t,
        ← etaleGermSet_along B S hS g hg ι hι hιg G t' t₀,
        ← etaleGermSet_etaleSubmoduleRestrict B S hS (ι ≫ g) hιg A'
          (GeometricPointLift.comp B S hS g ι t' t₀)]
      exact etaleGermSet_mono B S hS (ι ≫ g) hιg hGA _
    have hgermB : ∀ (x : GeometricPoint B S hS W.1) (t : GeometricPointLift B S hS f.hom x)
        (t' : GeometricPointLift B S hS g.hom x),
        etaleGermSet B S hS g hg G t' ⊆
          etaleGermSet B S hS f hf (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A') t := by
      intro x t t'
      obtain ⟨e₀, hfst, hsnd⟩ := exists_pullback_obj_of_app_eq B S hS fV g.hom
        (x.val.siteObject B S hS W.1) t.1 t'.1 (t.2.trans t'.2.symm)
      let tq : GeometricPointLift B S hS q.hom (liftGeometricPoint B S hS g t') := ⟨e₀, hsnd⟩
      let tr : GeometricPointLift B S hS r.hom (liftGeometricPoint B S hS f t) := ⟨e₀, hfst⟩
      have hkey : etaleSubmoduleCongr B S hS eP hqg hrf
          (etaleSubmoduleAlong B S hS q hq g hg hqg G) ≤
            etaleSubmoduleAlong B S hS r hr f hf hrf
              (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A') :=
        etaleSubmoduleCongr_etaleSubmoduleAlong_le_etaleSubmoduleAlong B S hS q hq g hg hqg
          r hr f hf hrf eP G _
          (hB₀le.trans (etaleSubmoduleRestrict_mono B S hS r hr le_sup_left))
      rw [← etaleGermSet_along B S hS g hg q hq hqg G t' tq,
        ← etaleGermSet_etaleSubmoduleCongr B S hS eP hqg hrf
          (etaleSubmoduleAlong B S hS q hq g hg hqg G)
          (GeometricPointLift.comp B S hS g q t' tq)
          (GeometricPointLift.comp B S hS f r t tr) rfl,
        ← etaleGermSet_along B S hS f hf r hr hrf _ t tr]
      exact etaleGermSet_mono B S hS (r ≫ f) hrf hkey _
    intro V' s hs
    refine (mem_etaleSubmoduleRestrict_obj B S hS g hg K V'.unop s).2 ?_
    rw [hKdef]
    refine (mem_etaleSubmoduleGlue_obj B S hS (edsMember B S hS hsq Uo hUo)
      (edsMemberHom B S hS hsq Uo hUo) (isEtale_edsMemberHom B S hS hsq Uo hUo)
      (edsMemberSubmodule B S hS hsq Uo hUo (etaleSubmoduleRestrict B S hS j hj A')
        (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A'))
      ((ringedSitePostcomp B S hS g hg).obj V'.unop) s).2 ?_
    rintro ⟨_ | _⟩ Z φ
    · exact map_mem_of_etaleGermSet_subset B S hS f hf g hg
        (B₀ ⊔ etaleSubmoduleRestrict B S hS f hf A') G hgermB Z V'.unop φ s hs
    · exact map_mem_of_etaleGermSet_subset B S hS j hj g hg
        (etaleSubmoduleRestrict B S hS j hj A') G hgermA Z V'.unop φ s hs

end AlgebraicGeometry.Space

end
