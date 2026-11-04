module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ConstantBaseChangeSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeAmpleStageOfSchemeLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleResidueFieldRelocalize

/-!
# The fibre stage of Stacks 0D3D: a scheme on which `L` is ample

Let `φ : X ⟶ Y` be a morphism of directed inverse systems of algebraic spaces over `S`, with
affine transition morphisms, proper and of finite presentation stages `φᵢ`, and limits
`f : X_∞ ⟶ Y_∞`. Let `k : h_V ⟶ Y_∞` be a morphism from an affine scheme `V` (in the proof of
Stacks 0D3D: `Spec κ(u)`), and let `Lᵢ` be an invertible module on a stage `Xᵢ` whose pullback
to the fibre `X_∞ ×_{Y_∞} h_V` is ample over `h_V`. Then the pullback of `Lᵢ` to the fibre
`X_j ×_{Y_j} h_V` of some later stage is ample over `h_V`.

This is the sentence of the proof of Stacks 0D3D: "Hence `X_y = lim X_{i, y_i}` and after
shrinking `I` we may assume `X_{i, y_i}` is a scheme for all `i`, see Stacks 07SR. Hence for some
`i` we have `L_{i, y_i}` is ample on `X_{i, y_i}` by Stacks 09MT." The fibres form the system
`AlgebraicGeometry.Space.constantBaseChangeDescentSituation`, a situation of Stacks 084R whose
limit is the fibre of the limit; ampleness there makes that limit a scheme, Stacks 07SR makes a
stage of the fibre system a scheme, and
`AlgebraicGeometry.Space.exists_le_isRelativelyAmple_of_isRelativelyAmple_limit` is Stacks 09MT
on the later stages.

Stacks 07SR is stated under the chapter's standing convention of Section 70.2 (tag 07SD). The
theorem takes that convention as an abstract property `Conv` of inverse systems of presheaves,
Stacks 07SR for situations satisfying `Conv` (`h07SR`), and the consequence `hSF` of the
convention that the scheme the site sees as the limit of a system of schemes is their limit as
schemes.

## Main results

* `AlgebraicGeometry.Space.exists_le_isRelativelyAmple_fibre_of_isRelativelyAmple_fibre`: the
  statement above.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {X Y : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} {φ : X ⟶ Y} {cY : Cone Y}
  {V : BigFppfOver B S hS}

/-- **The fibre stage of Stacks 0D3D.** Let `φ : X ⟶ Y` be a morphism of directed systems of
algebraic spaces with affine transition morphisms and proper, finitely presented stages, with
limit `f : cX.pt ⟶ cY.pt`, let `k : h_V ⟶ cY.pt` with `V` affine, and let `Lᵢ` be an invertible
module on `Xᵢ` whose pullback is ample on every base change of `f` along `k`. Granted Stacks 07SR
and the scheme-limit property `hSF` for situations satisfying the convention `Conv`, and `Conv`
for the system of fibres `X_j ×_{Y_j} h_V`, the pullback of `Lᵢ` is ample on every base change
of some `φ_j`, `j ≥ i`, along `h_V ⟶ cY.pt ⟶ Y_j`. -/
theorem exists_le_isRelativelyAmple_fibre_of_isRelativelyAmple_fibre
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (Conv : ∀ {J : Type u} [Category.{u} J], (J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop)
    (h07SR : ∀ {I' : Type u} [Preorder I'] [IsDirected I' (· ≤ ·)]
      (D : DescentSituation B S hS hZ I'), Conv D.system →
        D.limitCone.pt.IsRepresentable → ∃ i, (D.system.obj (op i)).IsRepresentable)
    (hSF : ∀ {I' : Type u} [Preorder I'] [IsDirected I' (· ≤ ·)]
      (D : DescentSituation B S hS hZ I'), Conv D.system → ∀ i₀ : I',
        (D.system.obj (op i₀)).IsRepresentable →
        ∀ W : Over (op i₀) ⥤ BigFppfOver B S hS,
          Nonempty (W ⋙ yoneda ≅ Over.forget (op i₀) ⋙ D.system) →
            PreservesLimit W (BigFppfOver.toScheme B S hS))
    (hX : ∀ i : I, IsAlgebraicSpace B S hS (X.obj (op i)))
    (hXaff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (X.map g))
    (hY : ∀ i : I, IsAlgebraicSpace B S hS (Y.obj (op i)))
    (hYaff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (Y.map g))
    (hφ : ∀ i : I, IsProper B S hS (φ.app (op i)) ∧ IsFinitePresentation B S hS (φ.app (op i)))
    {cX : Cone X} (hcX : IsLimit cX) (hcY : IsLimit cY) (hXlim : IsAlgebraicSpace B S hS cX.pt)
    (hYlim : IsAlgebraicSpace B S hS cY.pt)
    (f : cX.pt ⟶ cY.pt) (hf : ∀ i, f ≫ cY.π.app i = cX.π.app i ≫ φ.app i)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (k : yoneda.obj V ⟶ cY.pt)
    (hconv : Conv (constantBaseChangeSystem φ k))
    (i : I) (Lᵢ : Modules.{u, u} B S hS (X.obj (op i)) (hX i))
    (hLᵢ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (X.obj (op i)))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (X.obj (op i)) (hX i)).O)).property Lᵢ)
    (hamp : ∀ ⦃X₀ : AlgebraicSpaces B S hS⦄ (p₀ : X₀ ⟶ ⟨cX.pt, hXlim⟩)
      (f₀ : X₀ ⟶ representedAlgebraicSpace B S hS V),
      IsPullback p₀ f₀ (ObjectProperty.homMk f : (⟨cX.pt, hXlim⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨cY.pt, hYlim⟩) (ObjectProperty.homMk k) →
        IsRelativelyAmple B S hS f₀ ((modulePullback B S hS
          (p₀ ≫ (ObjectProperty.homMk (cX.π.app (op i)) :
            (⟨cX.pt, hXlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X.obj (op i), hX i⟩))).obj Lᵢ)) :
    ∃ (j : I) (hj : i ≤ j), ∀ ⦃X₀ : AlgebraicSpaces B S hS⦄ (p₀ : X₀ ⟶ ⟨X.obj (op j), hX j⟩)
      (f₀ : X₀ ⟶ representedAlgebraicSpace B S hS V),
      IsPullback p₀ f₀ (ObjectProperty.homMk (φ.app (op j)) :
          (⟨X.obj (op j), hX j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y.obj (op j), hY j⟩)
        (ObjectProperty.homMk (k ≫ cY.π.app (op j))) →
        IsRelativelyAmple B S hS f₀ ((modulePullback B S hS
          (p₀ ≫ (ObjectProperty.homMk (X.map (homOfLE hj).op) :
            (⟨X.obj (op j), hX j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X.obj (op i), hX i⟩))).obj Lᵢ) := by
  let E := constantBaseChangeSystem φ k
  let c := constantBaseChangeMap (I := I) k
  have hK : IsAffineSpace B S hS (yoneda.obj V) := isAffineSpace_yoneda B S hS V hV
  let D := constantBaseChangeDescentSituation B S hS φ k hZ hX hXaff hY hYaff hK
    (fun i => (hφ i).2.2.1) (fun i => (hφ i).2.2.2) hcX hcY hXlim hYlim f hf
    (Classical.arbitrary I)
  have hEalg : ∀ j : I, IsAlgebraicSpace B S hS (E.obj (op j)) := D.algebraicSpace
  have hElim : IsAlgebraicSpace B S hS (limit E) := D.limitAlgebraicSpace
  let eL : limit E ≅ pullback f k := constantBaseChangeSystemLimitIso hcX hcY f hf
  have hsqL : ∀ i' : I, IsPullback
      (ObjectProperty.homMk (eL.hom ≫ pullback.fst f k) :
        (⟨limit E, hElim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨cX.pt, hXlim⟩)
      (ObjectProperty.homMk (limit.π E (op i') ≫ (pullback.snd φ c).app (op i')) :
        (⟨limit E, hElim⟩ : AlgebraicSpaces B S hS) ⟶
          representedAlgebraicSpace B S hS V)
      (ObjectProperty.homMk f : (⟨cX.pt, hXlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨cY.pt, hYlim⟩)
      (ObjectProperty.homMk k) := fun i' =>
    isPullback_homMk B S hS hXlim (isAlgebraicSpace_yoneda B S hS V) hYlim
      hElim
      (IsPullback.of_iso_pullback ⟨by
          rw [Category.assoc, pullback.condition, ← constantBaseChangeSystemLimitIso_hom_snd hcX
            hcY f hf (op i'), Category.assoc]⟩
        eL rfl (constantBaseChangeSystemLimitIso_hom_snd hcX hcY f hf (op i')))
  have hlimrep : (limit E).IsRepresentable := by
    have h₀ := (hamp _ _ (hsqL i)).1
    have _ : (yoneda.obj V).IsRepresentable := inferInstance
    exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _ h₀
  -- Stacks 07SR: a stage of the system of fibres is a scheme
  obtain ⟨i₁, hrep₁⟩ := h07SR D hconv hlimrep
  obtain ⟨i₂, hi₂, hi₁₂⟩ := exists_ge_ge i i₁
  have hrep₂ : (E.obj (op i₂)).IsRepresentable :=
    isRepresentable_obj_of_isAffineHom_map hEalg D.transition_affine hrep₁ (homOfLE hi₁₂).op
  let t₂ : (⟨E.obj (op i₂), hEalg i₂⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X.obj (op i), hX i⟩ :=
    ObjectProperty.homMk ((pullback.fst φ c).app (op i₂) ≫ X.map (homOfLE hi₂).op)
  let N := (modulePullback B S hS t₂).obj Lᵢ
  have hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (E.obj (op i₂)))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (E.obj (op i₂)) (hEalg i₂)).O)).property N :=
    Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS t₂) (L := Lᵢ) (hL := hLᵢ)
  have hπ : (ObjectProperty.homMk (eL.hom ≫ pullback.fst f k) :
        (⟨limit E, hElim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨cX.pt, hXlim⟩) ≫
      (ObjectProperty.homMk (cX.π.app (op i)) :
        (⟨cX.pt, hXlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X.obj (op i), hX i⟩) =
      (ObjectProperty.homMk (limit.π E (op i₂)) :
        (⟨limit E, hElim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨E.obj (op i₂), hEalg i₂⟩) ≫
        t₂ := by
    ext1
    change (eL.hom ≫ pullback.fst f k) ≫ cX.π.app (op i) =
      limit.π E (op i₂) ≫ (pullback.fst φ c).app (op i₂) ≫ X.map (homOfLE hi₂).op
    rw [Category.assoc, constantBaseChangeSystemLimitIso_hom_fst_π hcX hcY f hf (op i),
      ← limit.w E (homOfLE hi₂).op, Category.assoc, NatTrans.naturality]
  have hampL := hamp _ _ (hsqL i₂)
  rw [hπ] at hampL
  have hampcore : IsRelativelyAmple B S hS
      (ObjectProperty.homMk (limit.π E (op i₂) ≫ (pullback.snd φ c).app (op i₂)) :
        (⟨limit E, hElim⟩ : AlgebraicSpaces B S hS) ⟶
          representedAlgebraicSpace B S hS V)
      ((modulePullback B S hS (ObjectProperty.homMk (limit.π E (op i₂)) :
        (⟨limit E, hElim⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨E.obj (op i₂), hEalg i₂⟩)).obj N) :=
    (isRelativelyAmple_congr _ ((modulePullbackCompIso B S hS
      (ObjectProperty.homMk (limit.π E (op i₂)) :
        (⟨limit E, hElim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨E.obj (op i₂), hEalg i₂⟩) t₂).app Lᵢ)).2
      hampL
  -- Stacks 09MT on the stages of the system of fibres over `i₂`
  have hs : ∀ j : I, IsProper B S hS ((pullback.snd φ c).app (op j)) := fun j =>
    isProper_of_isPullback B S hS (hEalg j) (hX j) (isAlgebraicSpace_yoneda B S hS V) (hY j)
      (isPullback_constantBaseChangeSystem φ k (op j)) (hφ j).1
  obtain ⟨j, hj, hampj⟩ := exists_le_isRelativelyAmple_of_isRelativelyAmple_limit
    (pullback.snd φ c) hEalg D.transition_affine hs hV (limit.isLimit E) hElim
    i₂ hrep₂ (hSF D hconv i₂ hrep₂) N hN hampcore
  refine ⟨j, hi₂.trans hj, fun X₀ p₀ f₀ hsq => ?_⟩
  let tj : (⟨X.obj (op j), hX j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X.obj (op i), hX i⟩ :=
    ObjectProperty.homMk (X.map (homOfLE (hi₂.trans hj)).op)
  let fstj : (⟨E.obj (op j), hEalg j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X.obj (op j), hX j⟩ :=
    ObjectProperty.homMk ((pullback.fst φ c).app (op j))
  have hsqj : IsPullback fstj
      (ObjectProperty.homMk ((pullback.snd φ c).app (op j)) :
        (⟨E.obj (op j), hEalg j⟩ : AlgebraicSpaces B S hS) ⟶ representedAlgebraicSpace B S hS V)
      (ObjectProperty.homMk (φ.app (op j)) :
        (⟨X.obj (op j), hX j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y.obj (op j), hY j⟩)
      ((Iso.refl _).hom ≫ ObjectProperty.homMk (k ≫ cY.π.app (op j))) := by
    rw [Iso.refl_hom, Category.id_comp]
    exact isPullback_homMk B S hS (hX j) (isAlgebraicSpace_yoneda B S hS V) (hY j) (hEalg j)
      (isPullback_constantBaseChangeSystem φ k (op j))
  have hcompj : (ObjectProperty.homMk (E.map (homOfLE hj).op) :
        (⟨E.obj (op j), hEalg j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨E.obj (op i₂), hEalg i₂⟩) ≫ t₂ =
      fstj ≫ tj := by
    ext1
    change E.map (homOfLE hj).op ≫ (pullback.fst φ c).app (op i₂) ≫ X.map (homOfLE hi₂).op =
      (pullback.fst φ c).app (op j) ≫ X.map (homOfLE (hi₂.trans hj)).op
    rw [← Category.assoc, NatTrans.naturality, Category.assoc, ← X.map_comp]
    rfl
  have hampj' : IsRelativelyAmple B S hS
      (ObjectProperty.homMk ((pullback.snd φ c).app (op j)) :
        (⟨E.obj (op j), hEalg j⟩ : AlgebraicSpaces B S hS) ⟶ representedAlgebraicSpace B S hS V)
      ((modulePullback B S hS fstj).obj ((modulePullback B S hS tj).obj Lᵢ)) := by
    let tE : (⟨E.obj (op j), hEalg j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨E.obj (op i₂), hEalg i₂⟩ :=
      ObjectProperty.homMk (E.map (homOfLE hj).op)
    have e₁ : (modulePullback B S hS tE).obj ((modulePullback B S hS t₂).obj Lᵢ) ≅
        (modulePullback B S hS fstj).obj ((modulePullback B S hS tj).obj Lᵢ) :=
      (modulePullbackCompIso B S hS tE t₂).app Lᵢ ≪≫
        eqToIso (congrArg (fun (m : (⟨E.obj (op j), hEalg j⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨X.obj (op i), hX i⟩) => (modulePullback B S hS m).obj Lᵢ) hcompj) ≪≫
          ((modulePullbackCompIso B S hS fstj tj).app Lᵢ).symm
    exact (isRelativelyAmple_congr _ e₁).1 hampj
  have h := isRelativelyAmple_of_isPullback_of_isIso (Iso.refl _) hsqj hampj' hsq
  exact (isRelativelyAmple_congr _ ((modulePullbackCompIso B S hS p₀ tj).app Lᵢ)).1 h

end AlgebraicGeometry.Space

end
