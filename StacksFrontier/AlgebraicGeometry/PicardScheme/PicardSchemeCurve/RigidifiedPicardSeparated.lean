module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RigidifiedPicardFunctor
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PointedCurveStructureSheaf
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.General.Approximation

/-!
# `Pic_{X/k, σ}` is separated for the Zariski topology

Let `k` be a field and `X` a smooth projective curve over `k` with a `k`-rational point `σ`. A
class in `Pic_{X/k, σ}(T) = Ker(σ_T^* : Pic(X_T) ⟶ Pic(T))` which vanishes on the members of an
open cover of `T` is zero. A trivialisation `β` of the class along `σ_T` normalises the local
trivialisations on the `X_{U_i}`: by [Stacks, Tag 0B9U] (`𝒪_{U} ≅ f_{U,*}𝒪_{X_U}` for every
`k`-scheme `U`) an isomorphism of invertible modules on `X_U` is determined by its restriction
along `σ_U`, so prescribing that restriction to be the one of `β` makes the local
trivialisations agree on the overlaps, and they glue (descent of morphisms along the open, hence
fpqc, cover `{X_{U_i} ⟶ X_T}`). This is the mechanism of [Stacks, Tag 0B9N]; it is the
separatedness used in the proof of [Stacks, Tag 0B9X].

## Main results

* `AlgebraicGeometry.RigidifiedPicard.eq_zero_of_forall_kernelMap_coverHom_eq_zero`: a class of
  `Pic_{X/k, σ}(T)` vanishing on an open cover of `T` vanishes.

## References

* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 0B9U](https://stacks.math.columbia.edu/tag/0B9U)
* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

namespace AlgebraicGeometry.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- The member `U_i` of an open cover of a `k`-scheme `T`, as a `k`-scheme. -/
abbrev coverObj (T : Over (Spec (.of k))) (𝒰 : T.left.OpenCover) (i : 𝒰.I₀) :
    Over (Spec (.of k)) :=
  Over.mk (𝒰.f i ≫ T.hom)

/-- The inclusion `U_i ⟶ T` of a member of an open cover, as a morphism of `k`-schemes. -/
abbrev coverHom (T : Over (Spec (.of k))) (𝒰 : T.left.OpenCover) (i : 𝒰.I₀) :
    coverObj T 𝒰 i ⟶ T :=
  Over.homMk (𝒰.f i)

/-- The overlap `U_i ×_T U_j` of two members of an open cover, as a `k`-scheme. -/
abbrev coverOverlap (T : Over (Spec (.of k))) (𝒰 : T.left.OpenCover) (i j : 𝒰.I₀) :
    Over (Spec (.of k)) :=
  Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)

/-- The first projection of an overlap. -/
abbrev coverOverlapFst (T : Over (Spec (.of k))) (𝒰 : T.left.OpenCover) (i j : 𝒰.I₀) :
    coverOverlap T 𝒰 i j ⟶ coverObj T 𝒰 i :=
  Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j))

/-- The second projection of an overlap. -/
abbrev coverOverlapSnd (T : Over (Spec (.of k))) (𝒰 : T.left.OpenCover) (i j : 𝒰.I₀) :
    coverOverlap T 𝒰 i j ⟶ coverObj T 𝒰 j :=
  Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j)) (pullback.condition_assoc _).symm

/-- The two composites `U_i ×_T U_j ⟶ U_i ⟶ T` and `U_i ×_T U_j ⟶ U_j ⟶ T` agree. -/
theorem coverOverlap_condition (T : Over (Spec (.of k))) (𝒰 : T.left.OpenCover) (i j : 𝒰.I₀) :
    coverOverlapFst T 𝒰 i j ≫ coverHom T 𝒰 i = coverOverlapSnd T 𝒰 i j ≫ coverHom T 𝒰 j := by
  ext
  exact pullback.condition

/-- The base change to `X` of an open cover of `T` is an fpqc covering family of `X_T`. -/
theorem baseChangeMap_coverHom_mem_fpqcPrecoverage (T : Over (Spec (.of k)))
    (𝒰 : T.left.OpenCover) :
    Presieve.ofArrows (fun i => pullback f (coverObj T 𝒰 i).hom)
        (fun i => baseChangeMap f (coverHom T 𝒰 i)) ∈
      Scheme.fpqcPrecoverage.{u} (pullback f T.hom) := by
  have h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fppfPrecoverage T.left :=
    Scheme.zariskiPrecoverage_le_fppfPrecoverage _ 𝒰.mem₀
  apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact Precoverage.mem_coverings_of_isPullback 𝒰.f h𝒰 (pullback.snd f T.hom)
    (fun i => baseChangeMap f (coverHom T 𝒰 i)) (fun i => pullback.snd f (coverObj T 𝒰 i).hom)
    fun i => Stacks.AlgebraicGeometry.Tag05JXGeneral.isPullback_baseChangeMap f _ _
      (coverHom T 𝒰 i).left (Over.w (coverHom T 𝒰 i)).symm

/-- The base change to `X` of the overlap square of an open cover is a pullback square. -/
theorem isPullback_baseChangeMap_coverOverlap (T : Over (Spec (.of k)))
    (𝒰 : T.left.OpenCover) (i j : 𝒰.I₀) :
    IsPullback (baseChangeMap f (coverOverlapFst T 𝒰 i j))
      (baseChangeMap f (coverOverlapSnd T 𝒰 i j))
      (baseChangeMap f (coverHom T 𝒰 i)) (baseChangeMap f (coverHom T 𝒰 j)) := by
  refine Stacks.Limits.isPullback_of_isPullback_vert
    (Stacks.AlgebraicGeometry.Tag05JXGeneral.isPullback_baseChangeMap f _ _
      (coverOverlapFst T 𝒰 i j).left (Over.w (coverOverlapFst T 𝒰 i j)).symm)
    (Stacks.AlgebraicGeometry.Tag05JXGeneral.isPullback_baseChangeMap f _ _
      (coverOverlapSnd T 𝒰 i j).left (Over.w (coverOverlapSnd T 𝒰 i j)).symm)
    (Stacks.AlgebraicGeometry.Tag05JXGeneral.isPullback_baseChangeMap f _ _
      (coverHom T 𝒰 i).left (Over.w (coverHom T 𝒰 i)).symm)
    (Stacks.AlgebraicGeometry.Tag05JXGeneral.isPullback_baseChangeMap f _ _
      (coverHom T 𝒰 j).left (Over.w (coverHom T 𝒰 j)).symm)
    (IsPullback.of_hasPullback (𝒰.f i) (𝒰.f j)) ?_
  rw [← baseChangeMap_comp, ← baseChangeMap_comp, coverOverlap_condition]

section Separated

variable [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]

include hσ in
/-- **A trivialisation along the section normalises a local trivialisation**: given an
isomorphism `β : σ_T^*ℳ ≅ σ_T^*𝒩` of the restrictions of two invertible modules on `X_T` along
`σ_T`, and `g : T' ⟶ T` over which `ℳ` and `𝒩` become isomorphic, there is an isomorphism of
their pullbacks to `X_{T'}` whose restriction along `σ_{T'}` is the restriction of `β`. -/
theorem exists_pullHom_section_eq {T T' : Over (Spec (.of k))}
    (M N : (pullback f T.hom).Modules)
    (hM : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
      (pullback f T.hom).ringCatSheaf.2 M)
    (hN : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
      (pullback f T.hom).ringCatSheaf.2 N)
    (β : (modulePullbackPseudofunctor.map (sectionAt f σ hσ T).op.toLoc).toFunctor.obj M ≅
      (modulePullbackPseudofunctor.map (sectionAt f σ hσ T).op.toLoc).toFunctor.obj N)
    (g : T' ⟶ T)
    (e : (modulePullbackPseudofunctor.map (baseChangeMap f g).op.toLoc).toFunctor.obj M ≅
      (modulePullbackPseudofunctor.map (baseChangeMap f g).op.toLoc).toFunctor.obj N) :
    ∃ ψ : (modulePullbackPseudofunctor.map (baseChangeMap f g).op.toLoc).toFunctor.obj M ≅
        (modulePullbackPseudofunctor.map (baseChangeMap f g).op.toLoc).toFunctor.obj N,
      pullHom ψ.hom (sectionAt f σ hσ T') _ _ rfl rfl =
        pullHom β.hom g.left _ _ (sectionAt_baseChangeMap f σ hσ g).symm
          (sectionAt_baseChangeMap f σ hσ g).symm := by
  have hsec : sectionAt f σ hσ T' ≫ pullback.snd f T'.hom = 𝟙 _ := pullback.lift_snd _ _ _
  have hc := isIso_c_baseChange_of_isCurve_of_section f σ hσ T'.hom
  have hbij := fun (A B : (pullback f T.hom).Modules)
      (hA : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
        (pullback f T.hom).ringCatSheaf.2 A)
      (hB : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
        (pullback f T.hom).ringCatSheaf.2 B)
      (eAB : (modulePullbackPseudofunctor.map (baseChangeMap f g).op.toLoc).toFunctor.obj A ≅
        (modulePullbackPseudofunctor.map (baseChangeMap f g).op.toLoc).toFunctor.obj B) =>
    Stacks.Picard.bijective_pullHom_section' (baseChangeMap f g) (baseChangeMap f g)
      (pullback.snd f T'.hom) (sectionAt f σ hσ T') hsec hc A B hA hB eAB _ _ rfl rfl
  obtain ⟨a, ha⟩ := (hbij M N hM hN e).surjective
    (pullHom β.hom g.left _ _ (sectionAt_baseChangeMap f σ hσ g).symm
      (sectionAt_baseChangeMap f σ hσ g).symm)
  obtain ⟨b, hb⟩ := (hbij N M hN hM e.symm).surjective
    (pullHom β.inv g.left _ _ (sectionAt_baseChangeMap f σ hσ g).symm
      (sectionAt_baseChangeMap f σ hσ g).symm)
  beta_reduce at ha hb
  have hMM := hbij M M hM hM (Iso.refl _)
  have hNN := hbij N N hN hN (Iso.refl _)
  refine ⟨⟨a, b, hMM.injective ?_, hNN.injective ?_⟩, ha⟩
  · change pullHom (a ≫ b) _ _ _ rfl rfl = pullHom (𝟙 _) _ _ _ rfl rfl
    rw [Stacks.Picard.pullHom_comp' a b (sectionAt f σ hσ T') _ _ _ rfl rfl rfl]
    rw [ha, hb, Stacks.Picard.pullHom_hom_comp_pullHom_inv β g.left _ _ _ _]
    exact (Stacks.Picard.pullHom_id' (F := modulePullbackPseudofunctor) M
      (baseChangeMap f g) (sectionAt f σ hσ T') _ rfl).symm
  · change pullHom (b ≫ a) _ _ _ rfl rfl = pullHom (𝟙 _) _ _ _ rfl rfl
    rw [Stacks.Picard.pullHom_comp' b a (sectionAt f σ hσ T') _ _ _ rfl rfl rfl]
    rw [ha, hb, Stacks.Picard.pullHom_inv_comp_pullHom_hom β g.left _ _ _ _]
    exact (Stacks.Picard.pullHom_id' (F := modulePullbackPseudofunctor) N
      (baseChangeMap f g) (sectionAt f σ hσ T') _ rfl).symm

include hσ in
/-- **Two normalised local isomorphisms agree on an overlap**: if `ψ_j` over `U_j ⟶ T` restrict
along the sections to the restriction of one `β` downstairs, then their pullbacks to any `W`
mapping to both (compatibly over `T`) agree, being determined by their restriction along `σ_W`
([Stacks, Tag 0B9U]). -/
theorem pullHom_eq_of_pullHom_section_eq {T : Over (Spec (.of k))}
    (M N : (pullback f T.hom).Modules)
    (hM : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
      (pullback f T.hom).ringCatSheaf.2 M)
    (hN : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
      (pullback f T.hom).ringCatSheaf.2 N)
    (β : (modulePullbackPseudofunctor.map (sectionAt f σ hσ T).op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map (sectionAt f σ hσ T).op.toLoc).toFunctor.obj N)
    {U₁ U₂ W : Over (Spec (.of k))} (g₁ : U₁ ⟶ T) (g₂ : U₂ ⟶ T)
    (ψ₁ : (modulePullbackPseudofunctor.map (baseChangeMap f g₁).op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map (baseChangeMap f g₁).op.toLoc).toFunctor.obj N)
    (ψ₂ : (modulePullbackPseudofunctor.map (baseChangeMap f g₂).op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map (baseChangeMap f g₂).op.toLoc).toFunctor.obj N)
    (hψ₁ : pullHom ψ₁ (sectionAt f σ hσ U₁) _ _ rfl rfl =
      pullHom β g₁.left _ _ (sectionAt_baseChangeMap f σ hσ g₁).symm
        (sectionAt_baseChangeMap f σ hσ g₁).symm)
    (hψ₂ : pullHom ψ₂ (sectionAt f σ hσ U₂) _ _ rfl rfl =
      pullHom β g₂.left _ _ (sectionAt_baseChangeMap f σ hσ g₂).symm
        (sectionAt_baseChangeMap f σ hσ g₂).symm)
    (p₁ : W ⟶ U₁) (p₂ : W ⟶ U₂) (hw : p₁ ≫ g₁ = p₂ ≫ g₂)
    (eW : (modulePullbackPseudofunctor.map (baseChangeMap f (p₁ ≫ g₁)).op.toLoc).toFunctor.obj M ≅
      (modulePullbackPseudofunctor.map (baseChangeMap f (p₁ ≫ g₁)).op.toLoc).toFunctor.obj N) :
    pullHom ψ₁ (baseChangeMap f p₁) (baseChangeMap f (p₁ ≫ g₁)) (baseChangeMap f (p₁ ≫ g₁))
        (baseChangeMap_comp f p₁ g₁).symm (baseChangeMap_comp f p₁ g₁).symm =
      pullHom ψ₂ (baseChangeMap f p₂) (baseChangeMap f (p₁ ≫ g₁)) (baseChangeMap f (p₁ ≫ g₁))
        (by rw [hw, baseChangeMap_comp]) (by rw [hw, baseChangeMap_comp]) := by
  have hsecW : sectionAt f σ hσ W ≫ pullback.snd f W.hom = 𝟙 _ := pullback.lift_snd _ _ _
  have h₀ : (p₁ ≫ g₁).left ≫ sectionAt f σ hσ T =
      sectionAt f σ hσ W ≫ baseChangeMap f (p₁ ≫ g₁) := (sectionAt_baseChangeMap f σ hσ _).symm
  have hA₁ : (p₁.left ≫ sectionAt f σ hσ U₁) ≫ baseChangeMap f g₁ =
      sectionAt f σ hσ W ≫ baseChangeMap f (p₁ ≫ g₁) := by
    rw [← sectionAt_baseChangeMap, baseChangeMap_comp, Category.assoc]
  have hA₂ : (p₂.left ≫ sectionAt f σ hσ U₂) ≫ baseChangeMap f g₂ =
      sectionAt f σ hσ W ≫ baseChangeMap f (p₁ ≫ g₁) := by
    rw [← sectionAt_baseChangeMap, hw, baseChangeMap_comp, Category.assoc]
  have hB₁ : p₁.left ≫ sectionAt f σ hσ U₁ ≫ baseChangeMap f g₁ =
      sectionAt f σ hσ W ≫ baseChangeMap f (p₁ ≫ g₁) := by rw [← Category.assoc, hA₁]
  have hB₂ : p₂.left ≫ sectionAt f σ hσ U₂ ≫ baseChangeMap f g₂ =
      sectionAt f σ hσ W ≫ baseChangeMap f (p₁ ≫ g₁) := by rw [← Category.assoc, hA₂]
  have hk₂ : p₂.left ≫ g₂.left = (p₁ ≫ g₁).left := by rw [hw]; rfl
  have e₁ := (Stacks.Picard.pullHom_pullHom_of_eq ψ₁ (baseChangeMap f p₁) _ _
      (baseChangeMap_comp f p₁ g₁).symm (baseChangeMap_comp f p₁ g₁).symm (sectionAt f σ hσ W)
      (p₁.left ≫ sectionAt f σ hσ U₁) (sectionAt_baseChangeMap f σ hσ p₁) _ _ rfl rfl
      hA₁ hA₁).trans
    ((Stacks.Picard.pullHom_pullHom_of_eq ψ₁ (sectionAt f σ hσ U₁) _ _ rfl rfl p₁.left
      (p₁.left ≫ sectionAt f σ hσ U₁) rfl _ _ hB₁ hB₁ hA₁ hA₁).symm.trans
    ((congrArg (fun φ => pullHom φ p₁.left _ _ hB₁ hB₁) hψ₁).trans
    (Stacks.Picard.pullHom_pullHom_of_eq β g₁.left _ _ _ _ p₁.left (p₁ ≫ g₁).left rfl _ _
      hB₁ hB₁ h₀ h₀)))
  have e₂ := (Stacks.Picard.pullHom_pullHom_of_eq ψ₂ (baseChangeMap f p₂) _ _
      (by rw [hw, baseChangeMap_comp]) (by rw [hw, baseChangeMap_comp]) (sectionAt f σ hσ W)
      (p₂.left ≫ sectionAt f σ hσ U₂) (sectionAt_baseChangeMap f σ hσ p₂) _ _ rfl rfl
      hA₂ hA₂).trans
    ((Stacks.Picard.pullHom_pullHom_of_eq ψ₂ (sectionAt f σ hσ U₂) _ _ rfl rfl p₂.left
      (p₂.left ≫ sectionAt f σ hσ U₂) rfl _ _ hB₂ hB₂ hA₂ hA₂).symm.trans
    ((congrArg (fun φ => pullHom φ p₂.left _ _ hB₂ hB₂) hψ₂).trans
    (Stacks.Picard.pullHom_pullHom_of_eq β g₂.left _ _ _ _ p₂.left (p₁ ≫ g₁).left hk₂ _ _
      hB₂ hB₂ h₀ h₀)))
  exact (Stacks.Picard.bijective_pullHom_section' (baseChangeMap f (p₁ ≫ g₁))
    (baseChangeMap f (p₁ ≫ g₁)) (pullback.snd f W.hom) (sectionAt f σ hσ W) hsecW
    (isIso_c_baseChange_of_isCurve_of_section f σ hσ W.hom) M N hM hN eW _ _ rfl
    rfl).injective (e₁.trans e₂.symm)

include hσ in
/-- **Normalised local isomorphisms agree on the overlaps of an open cover**: if `ψ_i` over
`U_i ⟶ T` restrict along the sections to the restriction of one `β`, then their pullbacks along
any `a₁ : Y ⟶ X_{U_{i₁}}` and `a₂ : Y ⟶ X_{U_{i₂}}` over the same `q : Y ⟶ X_T` agree. -/
theorem pullHom_coverHom_eq_of_pullHom_section_eq {T : Over (Spec (.of k))}
    (𝒰 : T.left.OpenCover) (M N : (pullback f T.hom).Modules)
    (hM : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
      (pullback f T.hom).ringCatSheaf.2 M)
    (hN : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
      (pullback f T.hom).ringCatSheaf.2 N)
    (β : (modulePullbackPseudofunctor.map (sectionAt f σ hσ T).op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map (sectionAt f σ hσ T).op.toLoc).toFunctor.obj N)
    (ψ : ∀ i, (modulePullbackPseudofunctor.map
        (baseChangeMap f (coverHom T 𝒰 i)).op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map (baseChangeMap f (coverHom T 𝒰 i)).op.toLoc).toFunctor.obj N)
    (hψ : ∀ i, pullHom (ψ i) (sectionAt f σ hσ (coverObj T 𝒰 i)) _ _ rfl rfl =
      pullHom β (coverHom T 𝒰 i).left _ _ (sectionAt_baseChangeMap f σ hσ (coverHom T 𝒰 i)).symm
        (sectionAt_baseChangeMap f σ hσ (coverHom T 𝒰 i)).symm)
    {i₁ i₂ : 𝒰.I₀}
    (eW : (modulePullbackPseudofunctor.map (baseChangeMap f
        (coverOverlapFst T 𝒰 i₁ i₂ ≫ coverHom T 𝒰 i₁)).op.toLoc).toFunctor.obj M ≅
      (modulePullbackPseudofunctor.map (baseChangeMap f
        (coverOverlapFst T 𝒰 i₁ i₂ ≫ coverHom T 𝒰 i₁)).op.toLoc).toFunctor.obj N)
    {Y : Scheme.{u}} (q : Y ⟶ pullback f T.hom) (a₁ : Y ⟶ pullback f (coverObj T 𝒰 i₁).hom)
    (a₂ : Y ⟶ pullback f (coverObj T 𝒰 i₂).hom)
    (ha₁ : a₁ ≫ baseChangeMap f (coverHom T 𝒰 i₁) = q)
    (ha₂ : a₂ ≫ baseChangeMap f (coverHom T 𝒰 i₂) = q) :
    pullHom (ψ i₁) a₁ q q ha₁ ha₁ = pullHom (ψ i₂) a₂ q q ha₂ ha₂ := by
  let p₁ := coverOverlapFst T 𝒰 i₁ i₂
  let p₂ := coverOverlapSnd T 𝒰 i₁ i₂
  have hw := coverOverlap_condition T 𝒰 i₁ i₂
  have hpb := isPullback_baseChangeMap_coverOverlap f T 𝒰 i₁ i₂
  let ℓ := hpb.lift a₁ a₂ (by rw [ha₁, ha₂])
  have hl₁ : ℓ ≫ baseChangeMap f p₁ = a₁ := hpb.lift_fst _ _ _
  have hl₂ : ℓ ≫ baseChangeMap f p₂ = a₂ := hpb.lift_snd _ _ _
  have hq : ℓ ≫ baseChangeMap f (p₁ ≫ coverHom T 𝒰 i₁) = q := by
    rw [baseChangeMap_comp, ← Category.assoc, hl₁, ha₁]
  have key := pullHom_eq_of_pullHom_section_eq f σ hσ M N hM hN β
    (coverHom T 𝒰 i₁) (coverHom T 𝒰 i₂) (ψ i₁) (ψ i₂) (hψ i₁) (hψ i₂) p₁ p₂ hw eW
  have h₂ : baseChangeMap f p₂ ≫ baseChangeMap f (coverHom T 𝒰 i₂) =
      baseChangeMap f (p₁ ≫ coverHom T 𝒰 i₁) := by rw [hw, baseChangeMap_comp]
  exact (Stacks.Picard.pullHom_pullHom_of_eq (ψ i₁) (baseChangeMap f p₁) _ _
      (baseChangeMap_comp f p₁ (coverHom T 𝒰 i₁)).symm
      (baseChangeMap_comp f p₁ (coverHom T 𝒰 i₁)).symm ℓ a₁ hl₁ q q hq hq ha₁ ha₁).symm.trans
    ((congrArg (fun φ => pullHom φ ℓ q q hq hq) key).trans
      (Stacks.Picard.pullHom_pullHom_of_eq (ψ i₂) (baseChangeMap f p₂) _ _ h₂ h₂ ℓ a₂ hl₂
        q q hq hq ha₂ ha₂))

include hσ in
/-- **`Pic_{X/k, σ}` is separated for the Zariski topology**: a class of `Pic_{X/k, σ}(T)` which
vanishes on every member of an open cover of `T` is zero. The local trivialisations are
normalised against a trivialisation along `σ_T` (`exists_pullHom_section_eq`); on an overlap
`U_i ×_T U_j` the two normalised trivialisations have the same restriction along the section,
hence agree ([Stacks, Tag 0B9U]), and they descend along the fpqc covering `{X_{U_i} ⟶ X_T}`. -/
theorem eq_zero_of_forall_kernelMap_coverHom_eq_zero (T : Over (Spec (.of k)))
    (𝒰 : T.left.OpenCover) (c : kernelAt f σ hσ T)
    (hc : ∀ i, kernelMap f σ hσ (coverHom T 𝒰 i) c = 0) : c = 0 := by
  classical
  apply Subtype.ext
  change c.1 = 0
  set N := Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace c.1
  have hLinv : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
      (pullback f T.hom).ringCatSheaf.2 N.obj := N.property
  have hOinv : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
      (pullback f T.hom).ringCatSheaf.2 (SheafOfModules.unit (pullback f T.hom).ringCatSheaf) :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  obtain ⟨β⟩ := Stacks.Picard.nonempty_pullHomIso_of_schemePullbackClass_eq_zero
    (sectionAt f σ hσ T) c.1 c.2
  have hloc : ∀ i, Stacks.Picard.schemePullbackClass (baseChangeMap f (coverHom T 𝒰 i)) c.1 = 0 :=
    fun i => congrArg Subtype.val (hc i)
  have etriv : ∀ {V : Over (Spec (.of k))} (i : 𝒰.I₀) (b' : V ⟶ coverObj T 𝒰 i),
      Nonempty ((modulePullbackPseudofunctor.map
          (baseChangeMap f b' ≫ baseChangeMap f (coverHom T 𝒰 i)).op.toLoc).toFunctor.obj N.obj ≅
        (modulePullbackPseudofunctor.map
          (baseChangeMap f b' ≫ baseChangeMap f (coverHom T 𝒰 i)).op.toLoc).toFunctor.obj
            (SheafOfModules.unit (pullback f T.hom).ringCatSheaf)) := by
    intro V i b'
    refine Stacks.Picard.nonempty_pullHomIso_of_schemePullbackClass_eq_zero _ c.1 ?_
    rw [← Stacks.Picard.schemePullbackClass_comp, hloc i]
    exact map_zero (Stacks.Picard.schemePullbackClassHom _)
  have hnorm : ∀ i : 𝒰.I₀, ∃ ψ : (modulePullbackPseudofunctor.map
          (baseChangeMap f (coverHom T 𝒰 i)).op.toLoc).toFunctor.obj N.obj ≅
        (modulePullbackPseudofunctor.map
          (baseChangeMap f (coverHom T 𝒰 i)).op.toLoc).toFunctor.obj
            (SheafOfModules.unit (pullback f T.hom).ringCatSheaf),
      pullHom ψ.hom (sectionAt f σ hσ (coverObj T 𝒰 i)) _ _ rfl rfl =
        pullHom β.hom (coverHom T 𝒰 i).left _ _
          (sectionAt_baseChangeMap f σ hσ (coverHom T 𝒰 i)).symm
          (sectionAt_baseChangeMap f σ hσ (coverHom T 𝒰 i)).symm := by
    intro i
    obtain ⟨e⟩ := etriv i (𝟙 _)
    rw [baseChangeMap_id, Category.id_comp] at e
    exact exists_pullHom_section_eq f σ hσ N.obj _ hLinv hOinv β (coverHom T 𝒰 i) e
  choose ψ hψ using hnorm
  have hfpqc := baseChangeMap_coverHom_mem_fpqcPrecoverage f T 𝒰
  have hLqc := Stacks.Picard.isQuasicoherent_of_isInvertible _ hLinv
  have hOqc := Stacks.Picard.isQuasicoherent_of_isInvertible _ hOinv
  rw [Stacks.Picard.eq_zero_iff_nonempty_iso_unit]
  refine Stacks.Picard.nonempty_iso_of_pullHom_hom_eq
    (fun i => baseChangeMap f (coverHom T 𝒰 i))
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hLqc hOqc)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hOqc hLqc)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hLqc hLqc)
    (Stacks.Picard.bijective_toDescentData_map_of_fpqc _ hfpqc _ _ hOqc hOqc) ψ ?_
  intro Y q i₁ i₂ a₁ a₂ ha₁ ha₂
  obtain ⟨eW⟩ := etriv i₁ (coverOverlapFst T 𝒰 i₁ i₂)
  rw [← baseChangeMap_comp] at eW
  exact pullHom_coverHom_eq_of_pullHom_section_eq f σ hσ 𝒰 N.obj _ hLinv hOinv β.hom
    (fun i => (ψ i).hom) hψ eW q a₁ a₂ ha₁ ha₂

end Separated

end AlgebraicGeometry.RigidifiedPicard

end
