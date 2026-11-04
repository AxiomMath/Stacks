module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.KoszulQuotient
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.SplittingTowerRecovery
public import StacksFrontier.AlgebraicGeometry.RelativeSegre.Projective
public import StacksFrontier.AlgebraicGeometry.SymProjectiveBundleTwist.Basic
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Bundle
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymMap
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.TensorFiniteness.RingedSpace
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# Projectivity of the layers of the splitting tower

Let `g : Y ⟶ X` be projective (Stacks 01W8) and `ℱ` a finite locally free `𝒪_Y`-module. If some
twist `ℱ ⊗ ℒ` by an invertible `𝒪_Y`-module is a quotient of `g^*𝒢` for a quasi-coherent
`𝒪_X`-module `𝒢` of finite type, then `𝐏(ℱ) ⟶ Y ⟶ X` is projective: `𝐏(ℱ) ≅ 𝐏(ℱ ⊗ ℒ)` over `Y`
(Stacks 02NC), the quotient gives a closed immersion `𝐏(ℱ ⊗ ℒ) ⟶ 𝐏(g^*𝒢)` over `Y`, and
`𝐏(g^*𝒢) ⟶ Y ⟶ X` is projective (`Stacks.RelativeSegre.isProjective_bundle_comp`). No
quasi-compactness of `X` is needed.

The hypothesis is `Stacks.Chow.IsTwistedPullbackQuotient g ℱ`. It holds for `g = id` and every
quasi-coherent `ℱ` of finite type, is stable under pullback, and passes from `ℱ` to the kernel
`𝒦` of the tautological surjection `ρ^*ℱ ⟶ 𝒪(1)` on `ρ : 𝐏(ℱ) ⟶ Y`: by the Koszul quotient
`ρ^*ℱ ⊗ ρ^*ℱ ⟶ 𝒦 ⊗ 𝒪(1)` (`Stacks.KoszulQuotient.exists_epi_tensorObj_kernel`),
`𝒦 ⊗ 𝒪(1) ⊗ ρ^*ℒ ⊗ ρ^*ℒ` is a quotient of `(g ∘ ρ)^*(𝒢 ⊗ 𝒢)`. These are exactly the modules
whose projective bundles the splitting tower of Stacks 02UL is built from.

## Main definitions

* `Stacks.Chow.IsTwistedPullbackQuotient`: a twist of `ℱ` is a quotient of a pullback along `g`
  of a quasi-coherent module of finite type.

## Main results

* `Stacks.Chow.isProjective_bundleProj_comp`: `𝐏(ℱ) ⟶ Y ⟶ X` is projective.
* `Stacks.Chow.isTwistedPullbackQuotient_id`, `Stacks.Chow.IsTwistedPullbackQuotient.pullback`,
  `Stacks.Chow.IsTwistedPullbackQuotient.kernel_bundleTautological`: the closure properties.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.SymGraded

universe u

/-- **A closed immersion followed by a projective morphism is projective** (Stacks 01W8): a
closed immersion into a projective bundle precomposed with a closed immersion is one. -/
theorem AlgebraicGeometry.IsProjective.isClosedImmersion_comp {X Y Z : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] {g : Y ⟶ X} (hg : IsProjective g) : IsProjective (i ≫ g) := by
  obtain ⟨E, hq, hft, hqc, k, _, rfl⟩ := hg
  exact ⟨E, hq, hft, hqc, i ≫ k, inferInstance, Category.assoc _ _ _⟩

namespace Stacks.Chow

variable {X Y : Scheme.{u}}

/-! ### The layer -/

/-- **The projective bundle of a twisted quotient of a pullback is projective over the base.**
Let `g : Y ⟶ X` be projective, `ℱ` a finite locally free `𝒪_Y`-module, `ℒ` an invertible
`𝒪_Y`-module and `𝒢` a quasi-coherent `𝒪_X`-module of finite type with an epimorphism
`g^*𝒢 ⟶ ℱ ⊗ ℒ`. Then `𝐏(ℱ) ⟶ Y ⟶ X` is projective (Stacks 01W8). -/
theorem isProjective_bundleProj_comp {g : Y ⟶ X} (hg : IsProjective g) (F : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (G : X.Modules)
    [G.IsQuasicoherent] (hG : G.IsFiniteType) (L : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (p : (Scheme.Modules.pullback g).obj G ⟶ Stacks.SymTwistChart.tensorObj F L) [Epi p] :
    IsProjective (bundleProj F ≫ g) := by
  have : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  have : ((Scheme.Modules.pullback g).obj G).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g G
  -- `𝐏(ℱ ⊗ ℒ) ≅ 𝐏(ℱ)` over `Y`
  obtain ⟨f, hf⟩ := Stacks.SymProjectiveBundleTwist.exists_iso_schemeProjectiveBundle_tensorObj F L
  -- the closed immersion `𝐏(ℱ ⊗ ℒ) ⟶ 𝐏(g^*𝒢)` over `Y`
  have hsurj := Stacks.Chow.GenuineChern.surjectiveOnAffineSections_schemeSheafGradedAlgebraHom p
    (isQuasicoherentPieces_of_isQuasicoherent _) (isQuasicoherentPieces_of_isQuasicoherent _)
  have hj := Stacks.AlgebraicGeometry.ProjBundleSurjection.isClosedImmersion_bundleMap hsurj
  have hjb := Stacks.AlgebraicGeometry.ProjBundleSurjection.bundleMap_comp_toBase hsurj
  have hP := Stacks.RelativeSegre.isProjective_bundle_comp hg G hG _ (Iso.refl _)
  have h1 : bundleProj F = f.inv ≫ schemeProjectiveBundleToBase (Stacks.SymTwistChart.tensorObj F L)
      (isQuasicoherentPieces_of_isQuasicoherent _) := by
    rw [← hf, Iso.inv_hom_id_assoc]
    rfl
  have key : bundleProj F ≫ g = (f.inv ≫ Stacks.AlgebraicGeometry.ProjBundleSurjection.bundleMap
      hsurj) ≫ (Stacks.RelativeSegre.bun ((Scheme.Modules.pullback g).obj G)).toBase ≫ g := by
    rw [h1, ← hjb]
    simp only [Category.assoc]
    rfl
  rw [key]
  exact @AlgebraicGeometry.IsProjective.isClosedImmersion_comp _ _ _ _
    (@IsClosedImmersion.comp _ _ _ f.inv _ inferInstance hj) _ hP

/-! ### Twisted quotients of pullbacks -/

/-- **`ℱ`, up to a twist, is a quotient of a pullback along `g`**: there are a quasi-coherent
`𝒪_X`-module `𝒢` of finite type, an invertible `𝒪_Y`-module `ℒ` and an epimorphism
`g^*𝒢 ⟶ ℱ ⊗ ℒ`. -/
def IsTwistedPullbackQuotient (g : Y ⟶ X) (F : Y.Modules) : Prop :=
  ∃ (G : X.Modules) (_ : G.IsQuasicoherent) (_ : G.IsFiniteType) (L : Y.Modules)
    (_ : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L)
    (p : (Scheme.Modules.pullback g).obj G ⟶ Stacks.SymTwistChart.tensorObj F L), Epi p

/-- **The projective bundle of a twisted quotient of a pullback is projective over the base**, in
terms of `Stacks.Chow.IsTwistedPullbackQuotient`. -/
theorem IsTwistedPullbackQuotient.isProjective_bundleProj_comp {g : Y ⟶ X} (hg : IsProjective g)
    {F : Y.Modules} [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
    (h : IsTwistedPullbackQuotient g F) : IsProjective (bundleProj F ≫ g) := by
  obtain ⟨G, _, hft, L, _, p, _⟩ := h
  exact Stacks.Chow.isProjective_bundleProj_comp hg F G hft L p

/-- **A quasi-coherent module of finite type is a twisted quotient of its own pullback along the
identity**, with the trivial twist. -/
theorem isTwistedPullbackQuotient_id (F : X.Modules) [F.IsQuasicoherent] (hF : F.IsFiniteType) :
    IsTwistedPullbackQuotient (𝟙 X) F := by
  let : MonoidalCategory X.Modules := Stacks.SheafOfModules.Strict.monoidalCategory X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf)
  refine ⟨F, inferInstance, hF, 𝟙_ X.Modules,
    Stacks.SheafOfModules.isInvertible_unit _ _,
    (Scheme.Modules.pullbackId X).hom.app F ≫ (ρ_ F).inv, ?_⟩
  infer_instance

/-- **Twisted quotients of pullbacks pull back**: if a twist of `ℱ` is a quotient of `g^*𝒢`, then
a twist of `k^*ℱ` is a quotient of `(g ∘ k)^*𝒢`. -/
theorem IsTwistedPullbackQuotient.pullback {g : Y ⟶ X} {F : Y.Modules}
    (h : IsTwistedPullbackQuotient g F) {Z : Scheme.{u}} (k : Z ⟶ Y) :
    IsTwistedPullbackQuotient (k ≫ g) ((Scheme.Modules.pullback k).obj F) := by
  obtain ⟨G, hq, hft, L, hL, p, _⟩ := h
  have hL' : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property L := hL
  refine ⟨G, hq, hft, (Scheme.Modules.pullback k).obj L,
    @Stacks.Modules.isInvertible_pullback _ _ k L hL',
    ((Scheme.Modules.pullbackComp k g).app G).inv ≫ (Scheme.Modules.pullback k).map p ≫
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k F L).hom, ?_⟩
  infer_instance

/-- Left whiskering preserves epimorphisms for the strict tensor product of `𝒪_Z`-modules. -/
private theorem epi_whiskerLeft_strict {Z : Scheme.{u}} (D : Z.Modules) {B C : Z.Modules}
    (f : B ⟶ C) [Epi f] :
    letI : MonoidalCategory Z.Modules := Stacks.SheafOfModules.Strict.monoidalCategory
      Z.sheaf.obj (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Z.sheaf)
    Epi (D ◁ f) := by
  let : MonoidalCategory Z.Modules := Stacks.SheafOfModules.Strict.monoidalCategory Z.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Z.sheaf)
  show Epi (D ◁ f)
  rw [show D ◁ f = ((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).obj D).map f
    from Stacks.SheafOfModules.Strict.whiskerLeft_eq_sheafTensor Z.sheaf D f]
  exact @preserves_epi_of_preservesColimit _ _ _ _ _ _ _ f
    (_root_.SheafOfModules.preservesColimitsOfSize_sheafTensor_obj Z.sheaf D _) _

/-- Right whiskering preserves epimorphisms for the strict tensor product of `𝒪_Z`-modules. -/
private theorem epi_whiskerRight_strict {Z : Scheme.{u}} (D : Z.Modules) {B C : Z.Modules}
    (f : B ⟶ C) [Epi f] :
    letI : MonoidalCategory Z.Modules := Stacks.SheafOfModules.Strict.monoidalCategory
      Z.sheaf.obj (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Z.sheaf)
    Epi (f ▷ D) := by
  let : MonoidalCategory Z.Modules := Stacks.SheafOfModules.Strict.monoidalCategory Z.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Z.sheaf)
  let : BraidedCategory Z.Modules := Stacks.SheafOfModules.Strict.braidedCategory Z.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Z.sheaf)
  show Epi (f ▷ D)
  have : Epi (D ◁ f) := epi_whiskerLeft_strict D f
  rw [show f ▷ D = (β_ B D).hom ≫ D ◁ f ≫ (β_ C D).inv by
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- The tautological twist `𝒪(1)` on `𝐏(ℱ)` is invertible for the strict tensor product. -/
private theorem isInvertible_bundleTwist_strict (F : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] :
    Stacks.SheafOfModules.IsInvertible (bundle F).sheaf.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf (bundle F).sheaf) (bundleTwist F) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (isInvertible_presheaf_of_isInvertible_sheaf (isInvertible_bundleTwist F))

/-- On `ρ : 𝐏(ℱ) ⟶ Y`, the module `𝒪(1) ⊗ (ρ^*ℒ ⊗ ρ^*ℒ)` is invertible for an invertible `ℒ`. -/
private theorem isInvertible_bundleTwist_tensorObj_pullback (F : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] {L : Y.Modules}
    (hL : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L) :
    Stacks.SheafOfModules.IsInvertible (bundle F).sheaf.obj (bundle F).ringCatSheaf.property
      (Stacks.SymTwistChart.tensorObj (bundleTwist F)
        (Stacks.SymTwistChart.tensorObj ((Scheme.Modules.pullback (bundleProj F)).obj L)
          ((Scheme.Modules.pullback (bundleProj F)).obj L))) := by
  have := isInvertible_bundleTwist_strict F
  have hL' : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property L := hL
  have : Stacks.SheafOfModules.IsInvertible (bundle F).sheaf.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf (bundle F).sheaf)
      ((Scheme.Modules.pullback (bundleProj F)).obj L) :=
    @Stacks.Modules.isInvertible_pullback _ _ (bundleProj F) L hL'
  have := Stacks.SheafOfModules.isInvertible_tensorSheaf (bundle F).sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf (bundle F).sheaf)
    ((Scheme.Modules.pullback (bundleProj F)).obj L)
    ((Scheme.Modules.pullback (bundleProj F)).obj L)
  exact Stacks.SheafOfModules.isInvertible_tensorSheaf (bundle F).sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf (bundle F).sheaf) (bundleTwist F) _

/-- **The tautological kernel of a twisted quotient of a pullback is again one.** Let
`ρ : 𝐏(ℱ) ⟶ Y` be the projective bundle of a finite locally free `𝒪_Y`-module `ℱ` and
`𝒦 = Ker(ρ^*ℱ ⟶ 𝒪(1))`. If `ℱ ⊗ ℒ` is a quotient of `g^*𝒢`, then
`𝒦 ⊗ (𝒪(1) ⊗ ρ^*ℒ ⊗ ρ^*ℒ)` is a quotient of `(g ∘ ρ)^*(𝒢 ⊗ 𝒢)`: the latter is
`ρ^*g^*𝒢 ⊗ ρ^*g^*𝒢` (Stacks 01CD), which maps onto `(ρ^*ℱ ⊗ ρ^*ℱ) ⊗ (ρ^*ℒ ⊗ ρ^*ℒ)`, and the
Koszul quotient `ρ^*ℱ ⊗ ρ^*ℱ ⟶ 𝒦 ⊗ 𝒪(1)` finishes. -/
theorem IsTwistedPullbackQuotient.kernel_bundleTautological {g : Y ⟶ X} {F : Y.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
    (h : IsTwistedPullbackQuotient g F) :
    IsTwistedPullbackQuotient (bundleProj F ≫ g) (kernel (bundleTautological F)) := by
  obtain ⟨G, hq, hft, L, hL, p, _⟩ := h
  let : MonoidalCategory (bundle F).Modules := Stacks.SheafOfModules.Strict.monoidalCategory
    (bundle F).sheaf.obj (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf (bundle F).sheaf)
  let : BraidedCategory (bundle F).Modules := Stacks.SheafOfModules.Strict.braidedCategory
    (bundle F).sheaf.obj (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf (bundle F).sheaf)
  -- the Koszul quotient `ρ^*ℱ ⊗ ρ^*ℱ ⟶ 𝒦 ⊗ 𝒪(1)`
  obtain ⟨κ, _⟩ := @Stacks.KoszulQuotient.exists_epi_tensorObj_kernel (bundle F) _ _
    (isInvertible_bundleTwist_strict F) (bundleTautological F) _
  have epiL : ∀ (D : (bundle F).Modules) {B C : (bundle F).Modules} (f : B ⟶ C) [Epi f],
      Epi (D ◁ f) := fun D _ _ f _ => epi_whiskerLeft_strict D f
  have epiR : ∀ (D : (bundle F).Modules) {B C : (bundle F).Modules} (f : B ⟶ C) [Epi f],
      Epi (f ▷ D) := fun D _ _ f _ => epi_whiskerRight_strict D f
  -- the pieces of the quotient map
  let ρ := bundleProj F
  let A := (Scheme.Modules.pullback ρ).obj F
  let Lρ := (Scheme.Modules.pullback ρ).obj L
  let gG := (Scheme.Modules.pullback g).obj G
  have m1 : Epi ((Scheme.Modules.pullback ρ).map p ⊗ₘ (Scheme.Modules.pullback ρ).map p) := by
    rw [MonoidalCategory.tensorHom_def]
    have := epiR ((Scheme.Modules.pullback ρ).obj gG) ((Scheme.Modules.pullback ρ).map p)
    have := epiL ((Scheme.Modules.pullback ρ).obj (Stacks.SymTwistChart.tensorObj F L))
      ((Scheme.Modules.pullback ρ).map p)
    infer_instance
  have m2 : Epi ((κ : A ⊗ A ⟶ kernel (bundleTautological F) ⊗ bundleTwist F) ▷ (Lρ ⊗ Lρ)) :=
    epiR _ κ
  have hft' : SheafOfModules.IsFiniteType.{u, u, u} (R := structureSheafRing X.toRingedSpace) G :=
    hft
  -- the quotient map, in steps
  let q₁ : (Scheme.Modules.pullback (ρ ≫ g)).obj (Stacks.SymTwistChart.tensorObj G G) ≅
      (Scheme.Modules.pullback ρ).obj gG ⊗ (Scheme.Modules.pullback ρ).obj gG :=
    ((Scheme.Modules.pullbackComp ρ g).app _).symm ≪≫
      (Scheme.Modules.pullback ρ).mapIso
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g G G) ≪≫
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso ρ gG gG
  let q₂ : (Scheme.Modules.pullback ρ).obj gG ⊗ (Scheme.Modules.pullback ρ).obj gG ⟶
      (A ⊗ Lρ) ⊗ (A ⊗ Lρ) :=
    ((Scheme.Modules.pullback ρ).map p ⊗ₘ (Scheme.Modules.pullback ρ).map p) ≫
      ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso ρ F L).hom ⊗ₘ
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso ρ F L).hom)
  let q₃ : (A ⊗ Lρ) ⊗ (A ⊗ Lρ) ⟶ kernel (bundleTautological F) ⊗ (bundleTwist F ⊗ (Lρ ⊗ Lρ)) :=
    tensorμ A Lρ A Lρ ≫
      ((κ : A ⊗ A ⟶ kernel (bundleTautological F) ⊗ bundleTwist F) ▷ (Lρ ⊗ Lρ)) ≫
      (α_ (kernel (bundleTautological F)) (bundleTwist F) (Lρ ⊗ Lρ)).hom
  have : IsIso (tensorμ A Lρ A Lρ) :=
    ⟨tensorδ _ _ _ _, tensorμ_tensorδ _ _ _ _, tensorδ_tensorμ _ _ _ _⟩
  have e₂ : Epi q₂ := by
    dsimp only [q₂]
    infer_instance
  have e₃ : Epi q₃ := epi_comp' inferInstance (epi_comp' m2 inferInstance)
  exact ⟨Stacks.SymTwistChart.tensorObj G G,
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace G G hq hq,
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isFiniteType X.toRingedSpace G G hft' hft',
    Stacks.SymTwistChart.tensorObj (bundleTwist F) (Stacks.SymTwistChart.tensorObj Lρ Lρ),
    isInvertible_bundleTwist_tensorObj_pullback F hL,
    q₁.hom ≫ q₂ ≫ q₃, epi_comp' inferInstance (epi_comp' e₂ e₃)⟩

end Stacks.Chow

end
