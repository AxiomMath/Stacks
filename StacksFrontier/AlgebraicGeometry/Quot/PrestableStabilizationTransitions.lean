module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionTransitionLaws

/-!
# Transition maps between local stabilizations

Let `X ⟶ S` be a prestable family of curves whose fibres have genus `g ≥ 2`, `{φᵢ : Wᵢ ⟶ S}` a
family of schemes of the site over `S`, and `cᵢ : X ×_S Wᵢ ⟶ Yᵢ` morphisms to families of curves
over `Wᵢ` satisfying conditions (1) and (2) of Stacks 0E8A. Over `Wᵢ ×_S Wⱼ` the base changes of
`cᵢ` and `cⱼ` are two stabilizations of the same family, so by the uniqueness of the
stabilization they are related by an isomorphism; composing with the projection gives the
transition map `Ψᵢⱼ : Yᵢ ×_S Wⱼ ⟶ Yⱼ` over `Wⱼ`, compatible with the `cᵢ`. This is how the local
stabilizations are glued in the proof of Stacks 0E8A
(`AlgebraicGeometry.Space.exists_glued_contraction_of_transitions` takes these transition maps).

The uniqueness of the stabilization over the overlaps rests on Stacks 0E89, in the form
`AlgebraicGeometry.CurveFamily.extendsFibreIsoNearPoint`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.baseChangeAlong`: the base change `X ×_S T ⟶ T` of a family of
  curves along `T ⟶ S`, with total space the fibre product of algebraic spaces.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_iso_of_isPullback_of_hasStableContractionFibres`: two
  stabilizations over a common base change are isomorphic under it.
* `AlgebraicGeometry.CurveFamily.exists_transition_of_hasStableContractionFibres`: the transition
  map between two local stabilizations.
* `AlgebraicGeometry.CurveFamily.exists_glued_of_hasStableContractionFibres`: local stabilizations
  over an fppf covering of the base glue to an algebraic space `Q` over the base with a morphism
  `c : X ⟶ Q` restricting to them.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The base change of a family of curves** `X ⟶ S` along `t : T ⟶ S`, with total space the
fibre product `X ×_S T` of algebraic spaces. -/
abbrev baseChangeAlong (X : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (t : T ⟶ X.base) : CurveFamily B hZ :=
  X.ofIsPullback B hZ t _ _ (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
    (schemeSpaceMap t))

/-- The structure morphism of a family of curves, transported to an equal base, is of finite
type. -/
theorem isFiniteType_toBase_comp_eqToHom (Y : CurveFamily B hZ)
    {Q : BigFppfOver B integerBase hZ} (hb : Y.base = Q) :
    Space.IsFiniteType B integerBase hZ (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom := by
  subst hb
  simpa only [eqToHom_refl, Category.comp_id] using Y.proper.2.1

/-- **Two stabilizations over a common base change are isomorphic**. Let
`cₖ : Xₖ ⟶ Yₖ`, `k = 1, 2`, satisfy conditions (1) and (2) of Stacks 0E8A, and let `X'` be a base
change of both `X₁` (along `t₁ : T ⟶ S₁`) and `X₂` (along `t₂ : T ⟶ S₂`) with the same structure
morphism to `T`, prestable with fibres of genus `g ≥ 2`. Then the base changes `c'ₖ : X' ⟶ Y'ₖ`
of the `cₖ` are related by an isomorphism `Y'₁ ≅ Y'₂` over `T` under `X'`. -/
theorem exists_iso_of_isPullback_of_hasStableContractionFibres {X₁ X₂ Y₁ Y₂ : CurveFamily B hZ}
    {hb₁ : Y₁.base = X₁.base} {hb₂ : Y₂.base = X₂.base}
    {c₁ : X₁.total ⟶ Y₁.total} {c₂ : X₂.total ⟶ Y₂.total}
    (h1₁ : X₁.IsUniversalStructureContraction B hZ Y₁ hb₁ c₁)
    (h1₂ : X₂.IsUniversalStructureContraction B hZ Y₂ hb₂ c₂)
    (h2₁ : X₁.HasStableContractionFibres B hZ Y₁ hb₁ c₁)
    (h2₂ : X₂.HasStableContractionFibres B hZ Y₂ hb₂ c₂)
    {T : BigFppfOver B integerBase hZ} (t₁ : T ⟶ X₁.base) (t₂ : T ⟶ X₂.base)
    {XV : AlgebraicSpaces B integerBase hZ} {a₁ : XV ⟶ X₁.total} {a₂ : XV ⟶ X₂.total}
    {f : XV ⟶ schemeSpace T}
    (sq₁ : IsPullback a₁ f X₁.toBase (schemeSpaceMap t₁))
    (sq₂ : IsPullback a₂ f X₂.toBase (schemeSpaceMap t₂))
    (hXF : IsPrestableCurveFamily B hZ (X₁.ofIsPullback B hZ t₁ a₁ f sq₁)) {g : ℕ} (hg : 2 ≤ g)
    (hgen : (X₁.ofIsPullback B hZ t₁ a₁ f sq₁).HasFibresOfGenus g)
    {Y₁' Y₂' : AlgebraicSpaces B integerBase hZ} {pY₁ : Y₁' ⟶ Y₁.total}
    {fY₁ : Y₁' ⟶ schemeSpace T} {pY₂ : Y₂' ⟶ Y₂.total} {fY₂ : Y₂' ⟶ schemeSpace T}
    (sqY₁ : IsPullback pY₁ fY₁ (Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁)) (schemeSpaceMap t₁))
    (sqY₂ : IsPullback pY₂ fY₂ (Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂)) (schemeSpaceMap t₂))
    {c₁' : XV ⟶ Y₁'} {c₂' : XV ⟶ Y₂'} (hc₁₁ : c₁' ≫ pY₁ = a₁ ≫ c₁) (hc₁₂ : c₁' ≫ fY₁ = f)
    (hc₂₁ : c₂' ≫ pY₂ = a₂ ≫ c₂) (hc₂₂ : c₂' ≫ fY₂ = f) :
    ∃ e : Y₁' ≅ Y₂', c₁' ≫ e.hom = c₂' ∧ e.hom ≫ fY₂ = fY₁ := by
  have hb : ∀ {Z : AlgebraicSpaces B integerBase hZ} {c' : XV ⟶ Z} {fY : Z ⟶ schemeSpace T},
      c' ≫ fY = f → c' ≫ fY ≫ eqToHom (congrArg schemeSpace (rfl : T = T)) = f := fun h => by
    simpa only [eqToHom_refl, Category.comp_id] using h
  obtain ⟨e, he, heb, -⟩ := existsUnique_iso_of_hasStableContractionFibres
    (X := X₁.ofIsPullback B hZ t₁ a₁ f sq₁)
    (Y₁ := Y₁.ofIsPullback B hZ (t₁ ≫ eqToHom hb₁.symm) pY₁ fY₁
      (Y₁.isPullback_toBase_of_isPullback_toBase_comp_eqToHom hb₁ t₁ sqY₁))
    (Y₂ := Y₂.ofIsPullback B hZ (t₂ ≫ eqToHom hb₂.symm) pY₂ fY₂
      (Y₂.isPullback_toBase_of_isPullback_toBase_comp_eqToHom hb₂ t₂ sqY₂))
    (hb₁ := rfl) (hb₂ := rfl) hXF hg hgen (hb hc₁₂) (hb hc₂₂)
    (isUniversalStructureContraction_ofIsPullback t₁ sq₁ sqY₁ hc₁₁ hc₁₂ h1₁)
    (isUniversalStructureContraction_ofIsPullback t₂ sq₂ sqY₂ hc₂₁ hc₂₂ h1₂)
    (hasStableContractionFibres_ofIsPullback t₁ sq₁ sqY₁ hc₁₁ hc₁₂ h2₁)
    (hasStableContractionFibres_ofIsPullback t₂ sq₂ sqY₂ hc₂₁ hc₂₂ h2₂)
  refine ⟨e, he, ?_⟩
  rw [← Category.comp_id fY₂, ← Category.comp_id fY₁]
  exact heb

/-- **The transition map between two local stabilizations**. Let
`cᵢ : X ×_S Wᵢ ⟶ Yᵢ` and `cⱼ : X ×_S Wⱼ ⟶ Yⱼ` satisfy conditions (1) and (2) of Stacks 0E8A over
`Wᵢ` and `Wⱼ`. There is a morphism `Ψ : Yᵢ ×_S Wⱼ ⟶ Yⱼ` over `Wⱼ` taking the image under `cᵢ` of a
point of `X ×_S Wᵢ`, together with a point of `Wⱼ` with the same image in `S`, to the image
under `cⱼ` of the corresponding point of `X ×_S Wⱼ`. -/
theorem exists_transition_of_hasStableContractionFibres {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) {g : ℕ} (hg : 2 ≤ g)
    (hgen : X.HasFibresOfGenus g) {ι : Type v}
    {W : ι → BigFppfOver B integerBase hZ} (φ : ∀ i, W i ⟶ X.base) {Y : ι → CurveFamily B hZ}
    (hY : ∀ i, (Y i).base = W i)
    (c : ∀ i, AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ i)) ⟶
      (Y i).total)
    (hc : ∀ i, c i ≫ (Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i)) =
      ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (φ i)).hom))
    (h1 : ∀ i, (X.baseChangeAlong (φ i)).IsUniversalStructureContraction B hZ (Y i) (hY i) (c i))
    (h2 : ∀ i, (X.baseChangeAlong (φ i)).HasStableContractionFibres B hZ (Y i) (hY i) (c i))
    (i j : ι) :
    ∃ Ψ : pullback (((Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i))).hom ≫
        (schemeSpaceMap (φ i)).hom) (schemeSpaceMap (φ j)).hom ⟶ (Y j).total.obj,
      Ψ ≫ ((Y j).toBase ≫ eqToHom (congrArg schemeSpace (hY j))).hom = pullback.snd _ _ ∧
      ∀ {Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
        (x : Z ⟶ (AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase
          (schemeSpaceMap (φ i))).obj) (b : Z ⟶ (schemeSpace (W j)).obj)
        (h : x ≫ (pullback.snd X.toBase.hom (schemeSpaceMap (φ i)).hom) ≫
          (schemeSpaceMap (φ i)).hom = b ≫ (schemeSpaceMap (φ j)).hom)
        (h' : (x ≫ (c i).hom) ≫ ((Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i))).hom ≫
          (schemeSpaceMap (φ i)).hom = b ≫ (schemeSpaceMap (φ j)).hom),
        pullback.lift (x ≫ (c i).hom) b h' ≫ Ψ =
          Space.baseChangeMove (fun k => AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
            X.toBase (schemeSpaceMap (φ k))) x b h ≫ (c j).hom := by
  -- notation
  let gY : ∀ k, (Y k).total ⟶ schemeSpace (W k) :=
    fun k => (Y k).toBase ≫ eqToHom (congrArg schemeSpace (hY k))
  let X' : ∀ k, AlgebraicSpaces B integerBase hZ :=
    fun k => AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ k))
  let pX : ∀ k, X' k ⟶ X.total :=
    fun k => ObjectProperty.homMk (pullback.fst X.toBase.hom (schemeSpaceMap (φ k)).hom)
  let fX : ∀ k, X' k ⟶ schemeSpace (W k) :=
    fun k => ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (φ k)).hom)
  have hpX : ∀ k, IsPullback (pX k) (fX k) X.toBase (schemeSpaceMap (φ k)) := fun k =>
    AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ k))
  -- the overlap
  let V := pullback (φ i) (φ j)
  let tᵢ : V ⟶ W i := pullback.fst (φ i) (φ j)
  let tⱼ : V ⟶ W j := pullback.snd (φ i) (φ j)
  have ht : tᵢ ≫ φ i = tⱼ ≫ φ j := pullback.condition
  have hyV : IsPullback (schemeSpaceMap tᵢ).hom (schemeSpaceMap tⱼ).hom
      (schemeSpaceMap (φ i)).hom (schemeSpaceMap (φ j)).hom :=
    (IsPullback.of_hasPullback (φ i) (φ j)).map yoneda
  -- the base change of `X` to the overlap, through `Wᵢ` and through `Wⱼ`
  let XV := AlgebraicSpaces.fiberProduct B integerBase hZ (fX i) (schemeSpaceMap tᵢ)
  let a₁ : XV ⟶ X' i := ObjectProperty.homMk (pullback.fst (fX i).hom (schemeSpaceMap tᵢ).hom)
  let a₂ : XV ⟶ schemeSpace V :=
    ObjectProperty.homMk (pullback.snd (fX i).hom (schemeSpaceMap tᵢ).hom)
  have hXVi : IsPullback a₁ a₂ (fX i) (schemeSpaceMap tᵢ) :=
    AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ (fX i) (schemeSpaceMap tᵢ)
  have hXV : IsPullback (a₁ ≫ pX i) a₂ X.toBase (schemeSpaceMap (tⱼ ≫ φ j)) := by
    rw [← ht, schemeSpaceMap_comp]
    exact hXVi.paste_horiz (hpX i)
  let m : XV ⟶ X' j := (hpX j).lift (a₁ ≫ pX i) (a₂ ≫ schemeSpaceMap tⱼ) (by
    simpa only [Category.assoc, ← schemeSpaceMap_comp] using hXV.w)
  have hm₁ : m ≫ pX j = a₁ ≫ pX i := (hpX j).lift_fst _ _ _
  have hm₂ : m ≫ fX j = a₂ ≫ schemeSpaceMap tⱼ := (hpX j).lift_snd _ _ _
  have hXVj : IsPullback m a₂ (fX j) (schemeSpaceMap tⱼ) :=
    IsPullback.of_right (by rwa [hm₁, ← schemeSpaceMap_comp]) hm₂ (hpX j)
  -- the two local stabilizations over the overlap
  have hci : c i ≫ gY i = fX i := hc i
  have hcj : c j ≫ gY j = fX j := hc j
  let Yᵢ := AlgebraicSpaces.fiberProduct B integerBase hZ (gY i) (schemeSpaceMap tᵢ)
  let Yⱼ := AlgebraicSpaces.fiberProduct B integerBase hZ (gY j) (schemeSpaceMap tⱼ)
  have hYᵢ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ (gY i) (schemeSpaceMap tᵢ)
  have hYⱼ := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ (gY j) (schemeSpaceMap tⱼ)
  let cᵢ : XV ⟶ Yᵢ := Space.structureContractionBaseChange B integerBase hZ (c i) hci
    (schemeSpaceMap tᵢ)
  let cⱼ : XV ⟶ Yⱼ := hYⱼ.lift (m ≫ c j) a₂ (by rw [Category.assoc, hcj, hm₂])
  let yi₁ : Yᵢ ⟶ (Y i).total :=
    ObjectProperty.homMk (pullback.fst (gY i).hom (schemeSpaceMap tᵢ).hom)
  let yi₂ : Yᵢ ⟶ schemeSpace V :=
    ObjectProperty.homMk (pullback.snd (gY i).hom (schemeSpaceMap tᵢ).hom)
  let yj₁ : Yⱼ ⟶ (Y j).total :=
    ObjectProperty.homMk (pullback.fst (gY j).hom (schemeSpaceMap tⱼ).hom)
  let yj₂ : Yⱼ ⟶ schemeSpace V :=
    ObjectProperty.homMk (pullback.snd (gY j).hom (schemeSpaceMap tⱼ).hom)
  have hcᵢ₁ : cᵢ ≫ yi₁ = a₁ ≫ c i :=
    Space.structureContractionBaseChange_fst B integerBase hZ (c i) hci _
  have hcᵢ₂ : cᵢ ≫ yi₂ = a₂ := Space.structureContractionBaseChange_snd B integerBase hZ (c i) hci _
  have hcⱼ₁ : cⱼ ≫ yj₁ = m ≫ c j := hYⱼ.lift_fst _ _ _
  have hcⱼ₂ : cⱼ ≫ yj₂ = a₂ := hYⱼ.lift_snd _ _ _
  -- the families over the overlap
  have sqXi : IsPullback a₁ a₂ (X.baseChangeAlong (φ i)).toBase (schemeSpaceMap tᵢ) := hXVi
  have sqXj : IsPullback m a₂ (X.baseChangeAlong (φ j)).toBase (schemeSpaceMap tⱼ) := hXVj
  obtain ⟨e, he, heb⟩ := exists_iso_of_isPullback_of_hasStableContractionFibres (h1 i) (h1 j)
    (h2 i) (h2 j) tᵢ tⱼ sqXi sqXj
    (isPrestableCurveFamily_of_hom (X.homOfIsPullback B hZ (tⱼ ≫ φ j) (a₁ ≫ pX i) a₂ hXV) hX) hg
    (HasFibresOfGenus.of_hom (X.homOfIsPullback B hZ (tⱼ ≫ φ j) (a₁ ≫ pX i) a₂ hXV) hgen)
    hYᵢ hYⱼ hcᵢ₁ hcᵢ₂ hcⱼ₁ hcⱼ₂
  -- the transition map
  have hYᵢh : IsPullback yi₁.hom yi₂.hom (gY i).hom (schemeSpaceMap tᵢ).hom :=
    AlgebraicSpaces.isPullback_hom B integerBase hZ hYᵢ
  have hYⱼh : IsPullback yj₁.hom yj₂.hom (gY j).hom (schemeSpaceMap tⱼ).hom :=
    AlgebraicSpaces.isPullback_hom B integerBase hZ hYⱼ
  have hXVih : IsPullback a₁.hom a₂.hom (fX i).hom (schemeSpaceMap tᵢ).hom :=
    AlgebraicSpaces.isPullback_hom B integerBase hZ hXVi
  have homEq : ∀ {P Q : AlgebraicSpaces B integerBase hZ} {u v : P ⟶ Q}, u = v → u.hom = v.hom :=
    fun h => by rw [h]
  have heb' : e.hom.hom ≫ yj₂.hom = yi₂.hom := homEq heb
  have he' : cᵢ.hom ≫ e.hom.hom = cⱼ.hom := homEq he
  have hcᵢ₁' : cᵢ.hom ≫ yi₁.hom = a₁.hom ≫ (c i).hom := homEq hcᵢ₁
  have hcᵢ₂' : cᵢ.hom ≫ yi₂.hom = a₂.hom := homEq hcᵢ₂
  have hcⱼ₁' : cⱼ.hom ≫ yj₁.hom = m.hom ≫ (c j).hom := homEq hcⱼ₁
  have hm₁' : m.hom ≫ (pX j).hom = a₁.hom ≫ (pX i).hom := homEq hm₁
  have hm₂' : m.hom ≫ (fX j).hom = a₂.hom ≫ (schemeSpaceMap tⱼ).hom := homEq hm₂
  have hci' : (c i).hom ≫ (gY i).hom = (fX i).hom := homEq hci
  let P := pullback ((gY i).hom ≫ (schemeSpaceMap (φ i)).hom) (schemeSpaceMap (φ j)).hom
  let v : P ⟶ (schemeSpace V).obj :=
    hyV.lift (pullback.fst _ _ ≫ (gY i).hom) (pullback.snd _ _)
      ((Category.assoc _ _ _).trans pullback.condition)
  let k : P ⟶ Yᵢ.obj := hYᵢh.lift (pullback.fst _ _) v (hyV.lift_fst _ _ _).symm
  have hk₁ : k ≫ yi₁.hom = pullback.fst _ _ := hYᵢh.lift_fst _ _ _
  have hk₂ : k ≫ yi₂.hom = v := hYᵢh.lift_snd _ _ _
  refine ⟨k ≫ e.hom.hom ≫ yj₁.hom, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hYⱼh.w, reassoc_of% heb', reassoc_of% hk₂]
    exact hyV.lift_snd _ _ _
  · intro Z x b h h'
    let vZ : Z ⟶ (schemeSpace V).obj :=
      hyV.lift (x ≫ (fX i).hom) b ((Category.assoc _ _ _).trans h)
    have hvZ₁ : vZ ≫ (schemeSpaceMap tᵢ).hom = x ≫ (fX i).hom := hyV.lift_fst _ _ _
    have hvZ₂ : vZ ≫ (schemeSpaceMap tⱼ).hom = b := hyV.lift_snd _ _ _
    let z : Z ⟶ XV.obj := hXVih.lift x vZ hvZ₁.symm
    have hz₁ : z ≫ a₁.hom = x := hXVih.lift_fst _ _ _
    have hz₂ : z ≫ a₂.hom = vZ := hXVih.lift_snd _ _ _
    have step₁ : pullback.lift (x ≫ (c i).hom) b h' ≫ k = z ≫ cᵢ.hom := by
      apply hYᵢh.hom_ext
      · rw [Category.assoc, hk₁, pullback.lift_fst, Category.assoc, hcᵢ₁', reassoc_of% hz₁]
      · rw [Category.assoc, hk₂, Category.assoc, hcᵢ₂', hz₂]
        apply hyV.hom_ext
        · rw [Category.assoc, hyV.lift_fst, pullback.lift_fst_assoc, Category.assoc, hci', hvZ₁]
        · rw [Category.assoc, hyV.lift_snd, pullback.lift_snd, hvZ₂]
    have step₃ : z ≫ m.hom =
        Space.baseChangeMove (fun k => AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
          X.toBase (schemeSpaceMap (φ k))) x b h := by
      apply (AlgebraicSpaces.isPullback_hom B integerBase hZ (hpX j)).hom_ext
      · rw [Space.baseChangeMove_fst, Category.assoc, hm₁', reassoc_of% hz₁]
      · rw [Space.baseChangeMove_snd, Category.assoc, hm₂', reassoc_of% hz₂, hvZ₂]
    rw [reassoc_of% step₁, reassoc_of% he', hcⱼ₁', reassoc_of% step₃]

/-- **Gluing local stabilizations**. Let `X ⟶ S` be a prestable family of
curves with fibres of genus `g ≥ 2`, `{φᵢ : Wᵢ ⟶ S}` an fppf covering by schemes of the site, and
`cᵢ : X ×_S Wᵢ ⟶ Yᵢ` morphisms to families of curves over `Wᵢ` satisfying conditions (1) and (2)
of Stacks 0E8A. Then there are an algebraic space `Q` over `S` with `Yᵢ = Q ×_S Wᵢ` and a morphism
`c : X ⟶ Q` over `S` restricting to every `cᵢ`. -/
theorem exists_glued_of_hasStableContractionFibres {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) {g : ℕ} (hg : 2 ≤ g)
    (hgen : X.HasFibresOfGenus g) {ι : Type v}
    {W : ι → BigFppfOver B integerBase hZ} (φ : ∀ i, W i ⟶ X.base)
    (hcov : Space.IsFppfCovering B integerBase hZ (fun i => (schemeSpace (W i)).obj)
      (fun i => (schemeSpaceMap (φ i)).hom))
    {Y : ι → CurveFamily B hZ} (hY : ∀ i, (Y i).base = W i)
    (c : ∀ i, AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ i)) ⟶
      (Y i).total)
    (hc : ∀ i, c i ≫ (Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i)) =
      ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (φ i)).hom))
    (h1 : ∀ i, (X.baseChangeAlong (φ i)).IsUniversalStructureContraction B hZ (Y i) (hY i) (c i))
    (h2 : ∀ i, (X.baseChangeAlong (φ i)).HasStableContractionFibres B hZ (Y i) (hY i) (c i)) :
    ∃ (Q : AlgebraicSpaces B integerBase hZ) (q : Q ⟶ schemeSpace X.base)
      (r : ∀ i, (Y i).total ⟶ Q) (cQ : X.total ⟶ Q),
      (∀ i, IsPullback (r i) ((Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i))) q
        (schemeSpaceMap (φ i))) ∧ cQ ≫ q = X.toBase ∧
      ∀ i, (ObjectProperty.homMk (pullback.fst X.toBase.hom (schemeSpaceMap (φ i)).hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ i)) ⟶
          X.total) ≫ cQ = c i ≫ r i := by
  choose Ψ hΨ hψc using fun i j =>
    exists_transition_of_hasStableContractionFibres hX hg hgen φ hY c hc h1 h2 i j
  refine Space.exists_glued_contraction_of_transitions (S₀ := X.base) (W := W) (φ := φ)
    (X := X.total) (fX := X.toBase)
    (X' := fun i => AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (φ i)))
    (pX := fun i => ObjectProperty.homMk (pullback.fst X.toBase.hom (schemeSpaceMap (φ i)).hom))
    (fX' := fun i => ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (φ i)).hom))
    (Y := fun i => (Y i).total)
    (gY := fun i => (Y i).toBase ≫ eqToHom (congrArg schemeSpace (hY i)))
    (c := c) (Ψ := Ψ)
    (fun i => AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
      (schemeSpaceMap (φ i))) hc hΨ ?_ hcov ?_ ?_ ?_ ?_
  · exact fun i j _ x b h h' => hψc i j x b h h'
  · exact fun i => isSeparated_toBase_comp_eqToHom (Y i) (hY i)
  · exact fun i => isFiniteType_toBase_comp_eqToHom (Y i) (hY i)
  · exact fun i => isIso_structureSharp_of_isUniversalStructureContraction_self
      (X := X.baseChangeAlong (φ i)) (Y := Y i) (hc i) (h1 i)
  · exact fun i T' t => isIso_structureSharp_of_isUniversalStructureContraction
      (X := X.baseChangeAlong (φ i)) (Y := Y i) (hc i) (h1 i) T' t

end CurveFamily

end AlgebraicGeometry

end
