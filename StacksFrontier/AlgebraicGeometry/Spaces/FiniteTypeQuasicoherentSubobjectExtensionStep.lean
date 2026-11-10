module

public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceQuasiCompactOperations
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators

/-!
# The induction step for extending finite type quasi-coherent submodules

Let `(Uo ⊆ W, f : V ⟶ W)` be an elementary distinguished square (Stacks 08GM) with `W`
quasi-separated, `Uo` quasi-compact and `V` affine.  This file proves that if every
quasi-coherent submodule of finite type over a quasi-compact open of `Uo`, respectively of `V`,
extends to a quasi-coherent submodule of finite type of the ambient module, then the same holds
on `W`.  Together with the affine case and the induction principle of Stacks 08GP this proves
Stacks 0853.

## The argument

Let `ℱ` be a quasi-coherent `𝒪_W`-module, `U' ⊆ W` a quasi-compact open and `𝒢 ⊆ ℱ|_{U'}` a
quasi-coherent submodule of finite type.

* On `Uo`, the restriction of `𝒢` to `U' ∩ Uo` extends to `𝒜 ⊆ ℱ|_{Uo}`.
* On `V`, the restrictions of `𝒜` to `V₀ = f⁻¹(Uo)` and of `𝒢` to `V'' = f⁻¹(U')` agree on the
  overlap and glue to a submodule over the union `V₁ = V₀ ∪ V''`, quasi-coherent of finite type
  because it is so on `V₀` and on `V''`; it extends to `ℬ ⊆ ℱ|_V`.
* `𝒜` and `ℬ` agree over `Uo ×_W V`, so they glue to `𝒦 ⊆ ℱ`
  (`AlgebraicGeometry.Space.exists_etaleSubmodule_eds_glue`), quasi-coherent of finite type
  because it is so on the étale covering `{Uo, V}`, and `𝒦|_{U'} = 𝒢`.

All agreements are checked on germ sets at geometric points of `W`, with
`AlgebraicGeometry.Space.etaleGermSet_along` moving between the different restrictions.

## Main definitions

* `AlgebraicGeometry.Space.ExtensionProperty`: the extension property of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.extensionProperty_of_isAffineSpace`: the affine case.
* `AlgebraicGeometry.Space.extensionProperty_of_isElementaryDistinguishedSquare`: the step.

## References

* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The extension property of an algebraic space `Y`**: every quasi-coherent submodule of finite
type of the restriction of a quasi-coherent `𝒪_Y`-module to a quasi-compact open subspace is the
restriction of a quasi-coherent submodule of finite type of the module. -/
def ExtensionProperty (Y : AlgebraicSpaces B S hS) : Prop :=
  ∀ (F : Modules.{u, u} B S hS Y.1 Y.2), F.IsQuasicoherentOnSite →
    ∀ (U : Subfunctor Y.1) (hU : IsOpenSubspace B S hS U),
      IsQuasiCompactSpace B S hS U.toFunctor →
      ∀ G : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS U hU)
        (isEtale_openSubspaceHom B S hS U hU)).obj F).Submodule,
        G.toSheafOfModules.IsQuasicoherentOnSite → G.toSheafOfModules.IsFiniteType →
          ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
            K.toSheafOfModules.IsFiniteType ∧
            etaleSubmoduleRestrict B S hS _ (isEtale_openSubspaceHom B S hS U hU) K = G

/-- **The affine case of the extension property.** -/
theorem extensionProperty_of_isAffineSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    (V : AlgebraicSpaces B S hS) (hVa : IsAffineSpace B S hS V.1) :
    ExtensionProperty B S hS V :=
  fun F hF U hU hUqc G hGq hGf =>
    exists_etaleSubmodule_extension_of_isAffineSpace B S hS hZ V hVa U hU hUqc F hF G hGq hGf

/-- **Finite type is preserved by étale restriction.** -/
theorem isFiniteType_etaleModulePullback {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsFiniteType) :
    ((etaleModulePullback.{u, u} B S hS g hg).obj M).IsFiniteType :=
  let e := (modulePullbackIsoEtaleModulePullback B S hS g hg).app M
  have : Epi e.hom := ⟨fun a b hab => by simpa using congrArg (e.inv ≫ ·) hab⟩
  Stacks.SheafOfModules.isFiniteType_of_epi
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    e.hom
    (Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _
      (isFiniteTypeOnSite_modulePullback B S hS g _
        (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ hM)))

/-- **Quasi-coherence and finite type of a submodule are local on an étale covering.** -/
theorem isQuasicoherentOnSite_isFiniteType_of_etaleSubmoduleRestrict {X : AlgebraicSpaces B S hS}
    {I : Type u} (Yi : I → AlgebraicSpaces B S hS) (f : ∀ i, Yi i ⟶ X)
    (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    {M : Modules.{u, u} B S hS X.1 X.2} (K : M.Submodule)
    (h : ∀ i,
      (etaleSubmoduleRestrict B S hS (f i) (hf i) K).toSheafOfModules.IsQuasicoherentOnSite ∧
      (etaleSubmoduleRestrict B S hS (f i) (hf i) K).toSheafOfModules.IsFiniteType) :
    K.toSheafOfModules.IsQuasicoherentOnSite ∧ K.toSheafOfModules.IsFiniteType := by
  have := QuasiCoherentDescent.isCoverDense_memberFunctor B S hS Yi f hf hcov
  refine ⟨QuasiCoherentDescent.isQuasicoherentOnSite_of_forall_etaleModulePullback B S hS Yi f hf
    _ fun i => ?_, QuasiCoherentDescent.isFiniteType_of_forall_etaleModulePullback B S hS Yi f hf
    _ fun i => ?_⟩
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (etaleSubmoduleRestrictIso B S hS (f i) (hf i) K) (h i).1
  · let e := etaleSubmoduleRestrictIso B S hS (f i) (hf i) K
    have : Epi e.hom := ⟨fun g k hgk => by simpa using congrArg (e.inv ≫ ·) hgk⟩
    exact Stacks.SheafOfModules.isFiniteType_of_epi
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2).O))
      e.hom (h i).2

section TwoOpens

variable {W : AlgebraicSpaces B S hS} {U₁ U₂ : Subfunctor W.1}
  (hU₁ : IsOpenSubspace B S hS U₁) (hU₂ : IsOpenSubspace B S hS U₂)

/-- The two members of a pair of open subspaces. -/
def twoOpenMember : ULift.{u} Bool → AlgebraicSpaces B S hS
  | ⟨true⟩ => openSubspaceSpace B S hS U₁ hU₁
  | ⟨false⟩ => openSubspaceSpace B S hS U₂ hU₂

/-- The inclusions of the two members of a pair of open subspaces. -/
def twoOpenMemberHom : ∀ b, twoOpenMember B S hS hU₁ hU₂ b ⟶ W
  | ⟨true⟩ => openSubspaceHom B S hS U₁ hU₁
  | ⟨false⟩ => openSubspaceHom B S hS U₂ hU₂

/-- The inclusions of the two members of a pair of open subspaces are étale. -/
theorem isEtale_twoOpenMemberHom : ∀ b, IsEtale B S hS (twoOpenMemberHom B S hS hU₁ hU₂ b).hom
  | ⟨true⟩ => isEtale_openSubspaceHom B S hS U₁ hU₁
  | ⟨false⟩ => isEtale_openSubspaceHom B S hS U₂ hU₂

variable {F : Modules.{u, u} B S hS W.1 W.2}

/-- The submodules over the two members of a pair of open subspaces. -/
def twoOpenMemberSubmodule
    (G₁ : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS U₁ hU₁)
      (isEtale_openSubspaceHom B S hS U₁ hU₁)).obj F).Submodule)
    (G₂ : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS U₂ hU₂)
      (isEtale_openSubspaceHom B S hS U₂ hU₂)).obj F).Submodule) :
    ∀ b, ((etaleModulePullback.{u, u} B S hS (twoOpenMemberHom B S hS hU₁ hU₂ b)
      (isEtale_twoOpenMemberHom B S hS hU₁ hU₂ b)).obj F).Submodule
  | ⟨true⟩ => G₁
  | ⟨false⟩ => G₂

/-- **Glueing submodules over two open subspaces.**  Submodules over two open subspaces whose
germ sets agree at every geometric point lying in both are the restrictions of one submodule. -/
theorem exists_etaleSubmodule_twoOpen_glue
    (G₁ : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS U₁ hU₁)
      (isEtale_openSubspaceHom B S hS U₁ hU₁)).obj F).Submodule)
    (G₂ : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS U₂ hU₂)
      (isEtale_openSubspaceHom B S hS U₂ hU₂)).obj F).Submodule)
    (h : ∀ (x : GeometricPoint B S hS W.1)
      (t₁ : GeometricPointLift B S hS (openSubspaceHom B S hS U₁ hU₁).hom x)
      (t₂ : GeometricPointLift B S hS (openSubspaceHom B S hS U₂ hU₂).hom x),
      etaleGermSet B S hS _ (isEtale_openSubspaceHom B S hS U₁ hU₁) G₁ t₁ =
        etaleGermSet B S hS _ (isEtale_openSubspaceHom B S hS U₂ hU₂) G₂ t₂) :
    ∃ N : F.Submodule,
      etaleSubmoduleRestrict B S hS _ (isEtale_openSubspaceHom B S hS U₁ hU₁) N = G₁ ∧
        etaleSubmoduleRestrict B S hS _ (isEtale_openSubspaceHom B S hS U₂ hU₂) N = G₂ := by
  have hcomp : EtaleSubmoduleFamily.Compatible B S hS (twoOpenMember B S hS hU₁ hU₂)
      (twoOpenMemberHom B S hS hU₁ hU₂) (isEtale_twoOpenMemberHom B S hS hU₁ hU₂)
      (twoOpenMemberSubmodule B S hS hU₁ hU₂ G₁ G₂) := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ V V' φ n hn
    · refine map_mem_of_etaleGermSet_subset B S hS _ (isEtale_openSubspaceHom B S hS U₂ hU₂) _
        (isEtale_openSubspaceHom B S hS U₂ hU₂) G₂ G₂ (fun x t t' => ?_) V V' φ n hn
      have : Subsingleton (GeometricPointLift B S hS (openSubspaceHom B S hS U₂ hU₂).hom x) :=
        subsingleton_geometricPointLift_of_mono B S hS U₂.ι inferInstance x
      rw [Subsingleton.elim t' t]
    · exact map_mem_of_etaleGermSet_subset B S hS _ (isEtale_openSubspaceHom B S hS U₂ hU₂) _
        (isEtale_openSubspaceHom B S hS U₁ hU₁) G₂ G₁
        (fun x t t' => (h x t' t).le) V V' φ n hn
    · exact map_mem_of_etaleGermSet_subset B S hS _ (isEtale_openSubspaceHom B S hS U₁ hU₁) _
        (isEtale_openSubspaceHom B S hS U₂ hU₂) G₁ G₂
        (fun x t t' => (h x t t').ge) V V' φ n hn
    · refine map_mem_of_etaleGermSet_subset B S hS _ (isEtale_openSubspaceHom B S hS U₁ hU₁) _
        (isEtale_openSubspaceHom B S hS U₁ hU₁) G₁ G₁ (fun x t t' => ?_) V V' φ n hn
      have : Subsingleton (GeometricPointLift B S hS (openSubspaceHom B S hS U₁ hU₁).hom x) :=
        subsingleton_geometricPointLift_of_mono B S hS U₁.ι inferInstance x
      rw [Subsingleton.elim t' t]
  exact ⟨etaleSubmoduleGlue B S hS _ _ _ (twoOpenMemberSubmodule B S hS hU₁ hU₂ G₁ G₂),
    etaleSubmoduleRestrict_etaleSubmoduleGlue B S hS _ _ _ _ hcomp ⟨true⟩,
    etaleSubmoduleRestrict_etaleSubmoduleGlue B S hS _ _ _ _ hcomp ⟨false⟩⟩

end TwoOpens

/-- Finite type is invariant under isomorphism. -/
theorem isFiniteType_of_iso' {Y : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (e : M ≅ N) (h : M.IsFiniteType) : N.IsFiniteType :=
  have : Epi e.hom := ⟨fun a b hab => by simpa using congrArg (e.inv ≫ ·) hab⟩
  Stacks.SheafOfModules.isFiniteType_of_epi
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    e.hom h

/-- Quasi-coherence and finite type of the restriction of a submodule along `k` to a submodule
of the étale pullback, from those of the submodule. -/
theorem etaleSubmoduleAlong_isQuasicoherentOnSite_isFiniteType {X Y Z : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS X.1 X.2} (k : Y ⟶ Z) (hk : IsEtale B S hS k.hom)
    (h : Z ⟶ X) (hh : IsEtale B S hS h.hom) (hkh : IsEtale B S hS (k ≫ h).hom)
    (N : ((etaleModulePullback.{u, u} B S hS h hh).obj M).Submodule)
    (hNq : N.toSheafOfModules.IsQuasicoherentOnSite) (hNf : N.toSheafOfModules.IsFiniteType) :
    (etaleSubmoduleAlong B S hS k hk h hh hkh N).toSheafOfModules.IsQuasicoherentOnSite ∧
      (etaleSubmoduleAlong B S hS k hk h hh hkh N).toSheafOfModules.IsFiniteType :=
  ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
      (etaleSubmoduleAlongIso B S hS k hk h hh hkh N).symm
      (isQuasicoherentOnSite_etaleModulePullback B S hS k hk _ hNq),
    isFiniteType_of_iso' B S hS (etaleSubmoduleAlongIso B S hS k hk h hh hkh N).symm
      (isFiniteType_etaleModulePullback B S hS k hk _ hNf)⟩

/-- A geometric point lifts along the inclusion of an open subspace exactly when its section lies
in the subspace. -/
def openSubspaceLift {W : AlgebraicSpaces B S hS} (U : Subfunctor W.1)
    (hU : IsOpenSubspace B S hS U) {x : GeometricPoint B S hS W.1}
    (hx : x.val.value ∈ U.obj (op (x.val.siteObject B S hS W.1))) :
    GeometricPointLift B S hS (openSubspaceHom B S hS U hU).hom x :=
  ⟨⟨x.val.value, hx⟩, rfl⟩

/-- If a geometric point lifts along the inclusion of an open subspace, then its section lies
in the subspace. -/
theorem value_mem_of_geometricPointLift {W : AlgebraicSpaces B S hS} (U : Subfunctor W.1)
    (hU : IsOpenSubspace B S hS U) {x : GeometricPoint B S hS W.1}
    (t : GeometricPointLift B S hS (openSubspaceHom B S hS U hU).hom x) :
    x.val.value ∈ U.obj (op (x.val.siteObject B S hS W.1)) := by
  rw [← t.2]
  exact t.1.2

/-- The covering of the target of an elementary distinguished square by its open subspace and its
étale algebraic space. -/
theorem points_covered_of_isElementaryDistinguishedSquare {W : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) (x : points B S hS W.1) :
    x ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) ∨
      ∃ y : points B S hS V, pointsMap B S hS V fV y = x := by
  classical
  by_cases hx : x ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)
  · exact Or.inl hx
  · right
    let D := reducedClosedSubspace B S hS W.1 W.2
      (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ hsq.isClosedComplement
    have hxD : x ∈ Set.range (pointsMap B S hS D.toFunctor D.ι) := by
      rw [range_pointsMap_ι_reducedClosedSubspace]
      exact hx
    obtain ⟨z, rfl⟩ := hxD
    have : IsIso (D.fromPreimage fV) := hsq.isIsoOverComplement
    obtain ⟨p, hp⟩ := pointsMap_surjective_of_isIso B S hS (D.fromPreimage fV) z
    refine ⟨pointsMap B S hS (D.preimage fV).toFunctor (D.preimage fV).ι p, ?_⟩
    rw [← pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι, pointsMap_comp_apply, hp]

/-- The two members of a cover by two étale morphisms. -/
def pairMember (Y₁ Y₂ : AlgebraicSpaces B S hS) : ULift.{u} Bool → AlgebraicSpaces B S hS
  | ⟨true⟩ => Y₁
  | ⟨false⟩ => Y₂

/-- The morphisms of a cover by two étale morphisms. -/
def pairMemberHom {Y Y₁ Y₂ : AlgebraicSpaces B S hS} (g₁ : Y₁ ⟶ Y) (g₂ : Y₂ ⟶ Y) :
    ∀ b, pairMember B S hS Y₁ Y₂ b ⟶ Y
  | ⟨true⟩ => g₁
  | ⟨false⟩ => g₂

/-- **Quasi-coherence and finite type of a submodule are local on a cover by two étale
morphisms.** -/
theorem isQuasicoherentOnSite_isFiniteType_of_pair {Y Y₁ Y₂ : AlgebraicSpaces B S hS}
    (g₁ : Y₁ ⟶ Y) (g₂ : Y₂ ⟶ Y) (hg₁ : IsEtale B S hS g₁.hom) (hg₂ : IsEtale B S hS g₂.hom)
    (hcov : ∀ z : points B S hS Y.1, z ∈ Set.range (pointsMap B S hS Y₁.1 g₁.hom) ∨
      z ∈ Set.range (pointsMap B S hS Y₂.1 g₂.hom))
    {M : Modules.{u, u} B S hS Y.1 Y.2} (K : M.Submodule)
    (h₁ : (etaleSubmoduleRestrict B S hS g₁ hg₁ K).toSheafOfModules.IsQuasicoherentOnSite ∧
      (etaleSubmoduleRestrict B S hS g₁ hg₁ K).toSheafOfModules.IsFiniteType)
    (h₂ : (etaleSubmoduleRestrict B S hS g₂ hg₂ K).toSheafOfModules.IsQuasicoherentOnSite ∧
      (etaleSubmoduleRestrict B S hS g₂ hg₂ K).toSheafOfModules.IsFiniteType) :
    K.toSheafOfModules.IsQuasicoherentOnSite ∧ K.toSheafOfModules.IsFiniteType := by
  have hg : ∀ b, IsEtale B S hS (pairMemberHom B S hS g₁ g₂ b).hom
    | ⟨true⟩ => hg₁
    | ⟨false⟩ => hg₂
  refine isQuasicoherentOnSite_isFiniteType_of_etaleSubmoduleRestrict B S hS
    (pairMember B S hS Y₁ Y₂) (pairMemberHom B S hS g₁ g₂) hg
    ⟨Y.2, fun b => (pairMember B S hS Y₁ Y₂ b).2, hg, ?_⟩ K ?_
  · refine Set.eq_univ_iff_forall.mpr fun z => ?_
    rcases hcov z with hz | hz
    · exact Set.mem_iUnion.mpr ⟨⟨true⟩, hz⟩
    · exact Set.mem_iUnion.mpr ⟨⟨false⟩, hz⟩
  · rintro ⟨_ | _⟩
    · exact h₂
    · exact h₁

/-- **The induction step, over an open subspace containing the open of the square.**  Let
`(Uo ⊆ W, f : V ⟶ W)` be an elementary distinguished square with `W` quasi-separated and `V`
affine with the extension property, and let `U'' ⊇ Uo` be a quasi-compact open subspace.  Then
every quasi-coherent submodule of finite type over `U''` extends to `W`. -/
theorem extension_of_isElementaryDistinguishedSquare_of_le (hZ : B.Contains (⊤_ Scheme.{u}))
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1) (hVa : IsAffineSpace B S hS V)
    (hPV : ExtensionProperty B S hS (edsEtale B S hS hsq))
    (U'' : Subfunctor W.1) (hU'' : IsOpenSubspace B S hS U'') (hUoU'' : Uo ≤ U'')
    (hU''qc : IsQuasiCompactSpace B S hS U''.toFunctor)
    (F : Modules.{u, u} B S hS W.1 W.2) (hF : F.IsQuasicoherentOnSite)
    (G'' : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS U'' hU'')
      (isEtale_openSubspaceHom B S hS U'' hU'')).obj F).Submodule)
    (hG''q : G''.toSheafOfModules.IsQuasicoherentOnSite)
    (hG''f : G''.toSheafOfModules.IsFiniteType) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧
      etaleSubmoduleRestrict B S hS _ (isEtale_openSubspaceHom B S hS U'' hU'') K = G'' := by
  classical
  let f := edsEtaleHom B S hS hsq
  have hf : IsEtale B S hS f.hom := isEtale_edsEtaleHom B S hS hsq
  let j'' := openSubspaceHom B S hS U'' hU''
  have hj'' : IsEtale B S hS j''.hom := isEtale_openSubspaceHom B S hS U'' hU''
  let U''s := openSubspaceSpace B S hS U'' hU''
  have hVqc : IsQuasiCompactSpace B S hS V := by
    obtain ⟨T, hT, ⟨e⟩⟩ := hVa
    exact IsQuasiCompactSpace.of_iso B S hS (isQuasiCompactSpace_yoneda_of_isAffine B S hS T hT)
      e.symm
  have hG'' : G''.toSheafOfModules.IsQuasicoherentOnSite ∧ G''.toSheafOfModules.IsFiniteType :=
    ⟨hG''q, hG''f⟩
  let Vs := edsEtale B S hS hsq
  have hfqc : IsQuasiCompact B S hS fV :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hWqs hVqc fV
  let V₁ : Subfunctor Vs.1 := U''.preimage fV
  have hV₁ : IsOpenSubspace B S hS V₁ :=
    isOpenSubspace_preimage B S hS fV U'' W.2 hsq.isAlgebraicSpace hU''
  have hV₁qc : IsQuasiCompactSpace B S hS V₁.toFunctor :=
    isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS W.2 hsq.isAlgebraicSpace fV hfqc hU''
      hU''qc
  let ι₁ := openSubspaceHom B S hS (W := Vs) V₁ hV₁
  have hι₁ : IsEtale B S hS ι₁.hom := isEtale_openSubspaceHom B S hS (W := Vs) V₁ hV₁
  let σ₁ : openSubspaceSpace B S hS (W := Vs) V₁ hV₁ ⟶ U''s :=
    ObjectProperty.homMk (U''.fromPreimage fV)
  have e₁ : σ₁ ≫ j'' = ι₁ ≫ f := ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι U'' fV)
  have hι₁f : IsEtale B S hS (ι₁ ≫ f).hom := isEtale_comp B S hS hι₁ hf
  have hσ₁j : IsEtale B S hS (σ₁ ≫ j'').hom := e₁ ▸ hι₁f
  have hσ₁ : IsEtale B S hS σ₁.hom :=
    @isEtale_of_comp_mono B S hS _ _ _ σ₁.hom U''.ι (Subfunctor.instMonoFunctorTypeι U'') hσ₁j
  let CW := etaleSubmoduleCongr B S hS e₁ hσ₁j hι₁f
    (etaleSubmoduleAlong B S hS σ₁ hσ₁ j'' hj'' hσ₁j G'')
  let C := etaleSubmoduleCompToIter B S hS ι₁ hι₁ f hf hι₁f CW
  have hC : C.toSheafOfModules.IsQuasicoherentOnSite ∧ C.toSheafOfModules.IsFiniteType := by
    obtain ⟨h1, h2⟩ := etaleSubmoduleAlong_isQuasicoherentOnSite_isFiniteType B S hS σ₁ hσ₁ j''
      hj'' hσ₁j G'' hG''.1 hG''.2
    have h1' := (isQuasicoherentOnSite_etaleSubmoduleCongr_iff B S hS e₁ hσ₁j hι₁f _).2 h1
    have h2' := (isFiniteType_etaleSubmoduleCongr_iff B S hS e₁ hσ₁j hι₁f _).2 h2
    exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
      (etaleSubmoduleCompToIterIso B S hS ι₁ hι₁ f hf hι₁f CW).symm h1',
      isFiniteType_of_iso' B S hS (etaleSubmoduleCompToIterIso B S hS ι₁ hι₁ f hf hι₁f CW).symm h2'⟩
  obtain ⟨Bm, hBq, hBf, hB⟩ := hPV _ (isQuasicoherentOnSite_etaleModulePullback B S hS f hf F hF)
    V₁ hV₁ hV₁qc C hC.1 hC.2
  have hB' : etaleSubmoduleAlong B S hS ι₁ hι₁ f hf hι₁f Bm = CW :=
    congrArg (etaleSubmoduleIterToComp B S hS ι₁ hι₁ f hf hι₁f) hB
  have hagree : EdsGermAgree B S hS hsq U'' hU'' G'' Bm := by
    intro x t u
    have hu := value_mem_of_geometricPointLift B S hS U'' hU'' u
    have hmem : t.1 ∈ V₁.obj (op (x.val.siteObject B S hS W.1)) := by
      have h := t.2
      change fV.app _ t.1 = x.val.value at h
      change fV.app _ t.1 ∈ U''.obj _
      rw [h]
      exact hu
    let t₁ : GeometricPointLift B S hS ι₁.hom (liftGeometricPoint B S hS f t) :=
      ⟨⟨t.1, hmem⟩, rfl⟩
    let p : GeometricPointLift B S hS σ₁.hom (liftGeometricPoint B S hS j'' u) :=
      ⟨⟨t.1, hmem⟩, Subtype.ext (t.2.trans u.2.symm)⟩
    calc etaleGermSet B S hS f hf Bm t
        = etaleGermSet B S hS (ι₁ ≫ f) hι₁f (etaleSubmoduleAlong B S hS ι₁ hι₁ f hf hι₁f Bm)
            (GeometricPointLift.comp B S hS f ι₁ t t₁) :=
          (etaleGermSet_along B S hS f hf ι₁ hι₁ hι₁f Bm t t₁).symm
      _ = etaleGermSet B S hS (ι₁ ≫ f) hι₁f CW (GeometricPointLift.comp B S hS f ι₁ t t₁) := by
          rw [hB']
      _ = etaleGermSet B S hS (σ₁ ≫ j'') hσ₁j (etaleSubmoduleAlong B S hS σ₁ hσ₁ j'' hj'' hσ₁j G'')
            (GeometricPointLift.comp B S hS j'' σ₁ u p) :=
          etaleGermSet_etaleSubmoduleCongr B S hS e₁ hσ₁j hι₁f _ _ _ rfl
      _ = etaleGermSet B S hS j'' hj'' G'' u :=
          etaleGermSet_along B S hS j'' hj'' σ₁ hσ₁ hσ₁j G'' u p
  obtain ⟨K, hKj, hKf⟩ := exists_etaleSubmodule_eds_glue B S hS hsq U'' hU'' hUoU'' hagree
  refine ⟨K, ?_⟩
  have hK := isQuasicoherentOnSite_isFiniteType_of_pair B S hS j'' f hj'' hf ?_ K
    (by rw [hKj]; exact hG'') (by rw [hKf]; exact ⟨hBq, hBf⟩)
  · exact ⟨hK.1, hK.2, hKj⟩
  · intro z
    rcases points_covered_of_isElementaryDistinguishedSquare B S hS hsq z with hz | hz
    · left
      obtain ⟨w, hw⟩ := hz
      refine ⟨pointsMap B S hS _ (Subfunctor.homOfLe hUoU'') w, ?_⟩
      refine (pointsMap_comp_apply B S hS (Subfunctor.homOfLe hUoU'') U''.ι w).symm.trans ?_
      rw [Subfunctor.homOfLe_ι]
      exact hw
    · exact Or.inr hz

/-- **The induction step.**  Let `(Uo ⊆ W, f : V ⟶ W)` be an elementary distinguished square with
`W` quasi-separated, `Uo` quasi-compact and `V` affine.  If `Uo` and `V` have the extension
property, so does `W`. -/
theorem extensionProperty_of_isElementaryDistinguishedSquare (hZ : B.Contains (⊤_ Scheme.{u}))
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hUoqc : IsQuasiCompactSpace B S hS Uo.toFunctor) (hVa : IsAffineSpace B S hS V)
    (hPU : ExtensionProperty B S hS (openSubspaceSpace B S hS Uo hsq.isOpenSubspace))
    (hPV : ExtensionProperty B S hS (edsEtale B S hS hsq)) :
    ExtensionProperty B S hS W := by
  classical
  intro F hF U' hU' hU'qc G hGq hGf
  have hUo := hsq.isOpenSubspace
  let j := openSubspaceHom B S hS Uo hUo
  have hj : IsEtale B S hS j.hom := isEtale_openSubspaceHom B S hS Uo hUo
  let f := edsEtaleHom B S hS hsq
  have hf : IsEtale B S hS f.hom := isEtale_edsEtaleHom B S hS hsq
  let ι' := openSubspaceHom B S hS U' hU'
  have hι' : IsEtale B S hS ι'.hom := isEtale_openSubspaceHom B S hS U' hU'
  have hjqc : IsQuasiCompact B S hS Uo.ι :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hWqs hUoqc Uo.ι
  have hVqc : IsQuasiCompactSpace B S hS V := by
    obtain ⟨T, hT, ⟨e⟩⟩ := hVa
    exact IsQuasiCompactSpace.of_iso B S hS (isQuasiCompactSpace_yoneda_of_isAffine B S hS T hT)
      e.symm
  let U₀ : Subfunctor Uo.toFunctor := U'.preimage Uo.ι
  have hU₀ : IsOpenSubspace B S hS U₀ := isOpenSubspace_preimage B S hS Uo.ι U' W.2 hUo.1 hU'
  have hU₀qc : IsQuasiCompactSpace B S hS U₀.toFunctor :=
    isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS W.2 hUo.1 Uo.ι hjqc hU' hU'qc
  let Uos := openSubspaceSpace B S hS Uo hUo
  let k₀ : openSubspaceSpace B S hS (W := Uos) U₀ hU₀ ⟶ Uos :=
    openSubspaceHom B S hS (W := Uos) U₀ hU₀
  have hk₀ : IsEtale B S hS k₀.hom := isEtale_openSubspaceHom B S hS (W := Uos) U₀ hU₀
  let m₀ : openSubspaceSpace B S hS (W := Uos) U₀ hU₀ ⟶ openSubspaceSpace B S hS U' hU' :=
    ObjectProperty.homMk (U'.fromPreimage Uo.ι)
  have hkj : IsEtale B S hS (k₀ ≫ j).hom := isEtale_comp B S hS hk₀ hj
  have e₀ : k₀ ≫ j = m₀ ≫ ι' := ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι U' Uo.ι).symm
  have hmι : IsEtale B S hS (m₀ ≫ ι').hom := e₀ ▸ hkj
  have hm₀ : IsEtale B S hS m₀.hom := by
    have hmono : Mono U'.ι := Subfunctor.instMonoFunctorTypeι U'
    exact @isEtale_of_comp_mono B S hS _ _ _ m₀.hom U'.ι hmono hmι
  let G₀W := etaleSubmoduleCongr B S hS e₀.symm hmι hkj
    (etaleSubmoduleAlong B S hS m₀ hm₀ ι' hι' hmι G)
  let G₀ := etaleSubmoduleCompToIter B S hS k₀ hk₀ j hj hkj G₀W
  have hG₀ : G₀.toSheafOfModules.IsQuasicoherentOnSite ∧ G₀.toSheafOfModules.IsFiniteType := by
    obtain ⟨h1, h2⟩ := etaleSubmoduleAlong_isQuasicoherentOnSite_isFiniteType B S hS m₀ hm₀ ι'
      hι' hmι G hGq hGf
    have h1' := (isQuasicoherentOnSite_etaleSubmoduleCongr_iff B S hS e₀.symm hmι hkj _).2 h1
    have h2' := (isFiniteType_etaleSubmoduleCongr_iff B S hS e₀.symm hmι hkj _).2 h2
    exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
      (etaleSubmoduleCompToIterIso B S hS k₀ hk₀ j hj hkj G₀W).symm h1',
      isFiniteType_of_iso' B S hS (etaleSubmoduleCompToIterIso B S hS k₀ hk₀ j hj hkj G₀W).symm h2'⟩
  obtain ⟨A, hAq, hAf, hA⟩ := hPU _ (isQuasicoherentOnSite_etaleModulePullback B S hS j hj F hF)
    U₀ hU₀ hU₀qc G₀ hG₀.1 hG₀.2
  have hA' : etaleSubmoduleAlong B S hS k₀ hk₀ j hj hkj A = G₀W := by
    have := congrArg (etaleSubmoduleIterToComp B S hS k₀ hk₀ j hj hkj) hA
    exact this
  have hAG : ∀ (x : GeometricPoint B S hS W.1) (t₁ : GeometricPointLift B S hS j.hom x)
      (t₂ : GeometricPointLift B S hS ι'.hom x),
      etaleGermSet B S hS j hj A t₁ = etaleGermSet B S hS ι' hι' G t₂ := by
    intro x t₁ t₂
    have hx₂ := value_mem_of_geometricPointLift B S hS U' hU' t₂
    have hmem : t₁.1 ∈ U₀.obj (op (x.val.siteObject B S hS W.1)) := by
      have h := t₁.2
      change Uo.ι.app _ t₁.1 = x.val.value at h
      change Uo.ι.app _ t₁.1 ∈ U'.obj _
      rw [h]
      exact hx₂
    let p : GeometricPointLift B S hS k₀.hom (liftGeometricPoint B S hS j t₁) := ⟨⟨t₁.1, hmem⟩, rfl⟩
    let p' : GeometricPointLift B S hS m₀.hom (liftGeometricPoint B S hS ι' t₂) :=
      ⟨⟨t₁.1, hmem⟩, Subtype.ext (t₁.2.trans t₂.2.symm)⟩
    calc etaleGermSet B S hS j hj A t₁
        = etaleGermSet B S hS (k₀ ≫ j) hkj (etaleSubmoduleAlong B S hS k₀ hk₀ j hj hkj A)
            (GeometricPointLift.comp B S hS j k₀ t₁ p) :=
          (etaleGermSet_along B S hS j hj k₀ hk₀ hkj A t₁ p).symm
      _ = etaleGermSet B S hS (k₀ ≫ j) hkj G₀W (GeometricPointLift.comp B S hS j k₀ t₁ p) := by
          rw [hA']
      _ = etaleGermSet B S hS (m₀ ≫ ι') hmι (etaleSubmoduleAlong B S hS m₀ hm₀ ι' hι' hmι G)
            (GeometricPointLift.comp B S hS ι' m₀ t₂ p') :=
          etaleGermSet_etaleSubmoduleCongr B S hS e₀.symm hmι hkj _ _ _ rfl
      _ = etaleGermSet B S hS ι' hι' G t₂ := etaleGermSet_along B S hS ι' hι' m₀ hm₀ hmι G t₂ p'
  obtain ⟨NW, hNWj, hNWι⟩ := exists_etaleSubmodule_twoOpen_glue B S hS hUo hU' A G hAG
  obtain ⟨U'', hU'', hUoU'', hU'U'', hrange''⟩ :=
    exists_openSubspace_range_eq_union B S hS W.2 hUo hU'
  have hU''qc : IsQuasiCompactSpace B S hS U''.toFunctor := by
    refine isQuasiCompactSpace_of_isCompact_range B S hS W.2 hU'' ?_
    rw [hrange'']
    exact (isCompact_range_of_isQuasiCompactSpace B S hS hUo hUoqc).union
      (isCompact_range_of_isQuasiCompactSpace B S hS hU' hU'qc)
  let j'' := openSubspaceHom B S hS U'' hU''
  have hj'' : IsEtale B S hS j''.hom := isEtale_openSubspaceHom B S hS U'' hU''
  let G'' := etaleSubmoduleRestrict B S hS j'' hj'' NW
  let U''s := openSubspaceSpace B S hS U'' hU''
  let aUo : Uos ⟶ U''s := ObjectProperty.homMk (Subfunctor.homOfLe hUoU'')
  let aU' : openSubspaceSpace B S hS U' hU' ⟶ U''s :=
    ObjectProperty.homMk (Subfunctor.homOfLe hU'U'')
  have eUo : aUo ≫ j'' = j := ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι hUoU'')
  have eU' : aU' ≫ j'' = ι' := ObjectProperty.hom_ext _ (Subfunctor.homOfLe_ι hU'U'')
  have haUoj : IsEtale B S hS (aUo ≫ j'').hom := eUo ▸ hj
  have haU'j : IsEtale B S hS (aU' ≫ j'').hom := eU' ▸ hι'
  have haUo : IsEtale B S hS aUo.hom :=
    @isEtale_of_comp_mono B S hS _ _ _ aUo.hom U''.ι (Subfunctor.instMonoFunctorTypeι U'') haUoj
  have haU' : IsEtale B S hS aU'.hom :=
    @isEtale_of_comp_mono B S hS _ _ _ aU'.hom U''.ι (Subfunctor.instMonoFunctorTypeι U'') haU'j
  have hG'' : G''.toSheafOfModules.IsQuasicoherentOnSite ∧ G''.toSheafOfModules.IsFiniteType := by
    refine isQuasicoherentOnSite_isFiniteType_of_pair B S hS aUo aU' haUo haU' ?_ G'' ?_ ?_
    · intro z
      have hz : pointsMap B S hS U''.toFunctor U''.ι z ∈
          Set.range (pointsMap B S hS U''.toFunctor U''.ι) := Set.mem_range_self z
      rw [hrange''] at hz
      have hinj := pointsMap_injective_of_mono B S hS (U''.ι)
      rcases hz with ⟨w, hw⟩ | ⟨w, hw⟩
      · refine Or.inl ⟨w, hinj ((pointsMap_comp_apply B S hS aUo.hom U''.ι w).symm.trans ?_)⟩
        change pointsMap B S hS Uo.toFunctor (Subfunctor.homOfLe hUoU'' ≫ U''.ι) w = _
        rw [Subfunctor.homOfLe_ι]
        exact hw
      · refine Or.inr ⟨w, hinj ((pointsMap_comp_apply B S hS aU'.hom U''.ι w).symm.trans ?_)⟩
        change pointsMap B S hS U'.toFunctor (Subfunctor.homOfLe hU'U'' ≫ U''.ι) w = _
        rw [Subfunctor.homOfLe_ι]
        exact hw
    · have h1 :
          (etaleSubmoduleRestrict B S hS (aUo ≫ j'') haUoj
            NW).toSheafOfModules.IsQuasicoherentOnSite ∧
          (etaleSubmoduleRestrict B S hS (aUo ≫ j'') haUoj NW).toSheafOfModules.IsFiniteType := by
        rw [← isQuasicoherentOnSite_etaleSubmoduleCongr_iff B S hS eUo haUoj hj,
          ← isFiniteType_etaleSubmoduleCongr_iff B S hS eUo haUoj hj,
          etaleSubmoduleCongr_restrict, hNWj]
        exact ⟨hAq, hAf⟩
      exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
          (etaleSubmoduleIterToCompIso B S hS aUo haUo j'' hj'' haUoj
            (etaleSubmoduleRestrict B S hS aUo haUo G'')) h1.1,
        isFiniteType_of_iso' B S hS
          (etaleSubmoduleIterToCompIso B S hS aUo haUo j'' hj'' haUoj
            (etaleSubmoduleRestrict B S hS aUo haUo G'')) h1.2⟩
    · have h1 :
          (etaleSubmoduleRestrict B S hS (aU' ≫ j'') haU'j
            NW).toSheafOfModules.IsQuasicoherentOnSite ∧
          (etaleSubmoduleRestrict B S hS (aU' ≫ j'') haU'j NW).toSheafOfModules.IsFiniteType := by
        rw [← isQuasicoherentOnSite_etaleSubmoduleCongr_iff B S hS eU' haU'j hι',
          ← isFiniteType_etaleSubmoduleCongr_iff B S hS eU' haU'j hι',
          etaleSubmoduleCongr_restrict, hNWι]
        exact ⟨hGq, hGf⟩
      exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
          (etaleSubmoduleIterToCompIso B S hS aU' haU' j'' hj'' haU'j
            (etaleSubmoduleRestrict B S hS aU' haU' G'')) h1.1,
        isFiniteType_of_iso' B S hS
          (etaleSubmoduleIterToCompIso B S hS aU' haU' j'' hj'' haU'j
            (etaleSubmoduleRestrict B S hS aU' haU' G'')) h1.2⟩
  suffices hK : ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧ etaleSubmoduleRestrict B S hS j'' hj'' K = G'' by
    obtain ⟨K, hKq, hKf, hK⟩ := hK
    refine ⟨K, hKq, hKf, ?_⟩
    have h1 : etaleSubmoduleRestrict B S hS (aU' ≫ j'') haU'j K =
        etaleSubmoduleRestrict B S hS (aU' ≫ j'') haU'j NW := by
      rw [← etaleSubmoduleAlong_restrict B S hS aU' haU' j'' hj'' haU'j K, hK]
      rfl
    have h2 := congrArg (etaleSubmoduleCongr B S hS eU' haU'j hι') h1
    rw [etaleSubmoduleCongr_restrict, etaleSubmoduleCongr_restrict, hNWι] at h2
    exact h2
  exact extension_of_isElementaryDistinguishedSquare_of_le B S hS hZ hsq hWqs hVa hPV U'' hU''
    hUoU'' hU''qc F hF G'' hG''.1 hG''.2

end AlgebraicGeometry.Space

end
