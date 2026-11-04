module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionDescentAlongCovering
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.TransitionMapDescentEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison

/-!
# The unit and cocycle laws for transition maps between contractions

Let `{φᵢ : Wᵢ ⟶ S}` be a family of schemes over a scheme `S` of the site, `X` an algebraic space
over `S` with base changes `X'ᵢ = X ×_S Wᵢ`, and `cᵢ : X'ᵢ ⟶ Yᵢ` morphisms over `Wᵢ` to algebraic
spaces separated over `Wᵢ`, every base change of which along a scheme has `𝒪 = c_*𝒪`. Let
`Ψᵢⱼ : Yᵢ ×_S Wⱼ ⟶ Yⱼ` be transition maps over `Wⱼ` compatible with the `cᵢ`: moving the image
under `cᵢ` of a point of `X'ᵢ` gives the image under `cⱼ` of the corresponding point of `X'ⱼ`.
Then the `Ψᵢⱼ` satisfy the unit and cocycle laws of a descent datum: in both laws the two sides
are morphisms out of a base change of some `Yᵢ` which agree after the base change of `cᵢ`, hence
agree (`AlgebraicGeometry.Space.eq_of_comp_eq_of_isIso_structureSharp`). When the `Wᵢ` form an
fppf covering and the `Yᵢ` are of finite type, the `Yᵢ` glue to an algebraic space `Q` over `S`
receiving a morphism from `X` that restricts to every `cᵢ`.

## Main results

* `AlgebraicGeometry.Space.transitionMove_self_of_isIso_structureSharp`: the unit law.
* `AlgebraicGeometry.Space.transitionMove_transitionMove_of_isIso_structureSharp`: the cocycle
  law.
* `AlgebraicGeometry.Space.exists_glued_contraction_of_transitions`: the `Yᵢ` and `cᵢ` glue to a
  morphism `X ⟶ Q` over `S`.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

open Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {ι : Type v} {S₀ : BigFppfOver B S hS} {W : ι → BigFppfOver B S hS} {φ : ∀ i, W i ⟶ S₀}
  {X : AlgebraicSpaces B S hS} {fX : X ⟶ schemeSpace S₀}
  {X' : ι → AlgebraicSpaces B S hS} {pX : ∀ i, X' i ⟶ X} {fX' : ∀ i, X' i ⟶ schemeSpace (W i)}
  (hpX : ∀ i, IsPullback (pX i) (fX' i) fX (schemeSpaceMap (φ i)))
  {Y : ι → AlgebraicSpaces B S hS} {gY : ∀ i, Y i ⟶ schemeSpace (W i)}
  {c : ∀ i, X' i ⟶ Y i} (hc : ∀ i, c i ≫ gY i = fX' i)
  {Ψ : ∀ i j, pullback ((gY i).hom ≫ (schemeSpaceMap (φ i)).hom) (schemeSpaceMap (φ j)).hom ⟶
    (Y j).obj}

/-- The point of `X'ⱼ` corresponding to a point `x` of `X'ᵢ` and a point `b` of `Wⱼ` with the same
image in `S`. -/
def baseChangeMove {i j : ι} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : Z ⟶ (X' i).obj)
    (b : Z ⟶ (schemeSpace (W j)).obj)
    (h : x ≫ (fX' i).hom ≫ (schemeSpaceMap (φ i)).hom = b ≫ (schemeSpaceMap (φ j)).hom) :
    Z ⟶ (X' j).obj :=
  (AlgebraicSpaces.isPullback_hom B S hS (hpX j)).lift (x ≫ (pX i).hom) b
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => x ≫ m) (AlgebraicSpaces.isPullback_hom B S hS (hpX i)).w).trans h))

/-- The point `baseChangeMove hpX x b h` of `X'ⱼ` maps to the same point of `X` as `x`. -/
@[reassoc (attr := simp)]
theorem baseChangeMove_fst {i j : ι} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : Z ⟶ (X' i).obj)
    (b : Z ⟶ (schemeSpace (W j)).obj)
    (h : x ≫ (fX' i).hom ≫ (schemeSpaceMap (φ i)).hom = b ≫ (schemeSpaceMap (φ j)).hom) :
    baseChangeMove hpX x b h ≫ (pX j).hom = x ≫ (pX i).hom :=
  (AlgebraicSpaces.isPullback_hom B S hS (hpX j)).lift_fst _ _ _

/-- The point `baseChangeMove hpX x b h` of `X'ⱼ` maps to `b` in `Wⱼ`. -/
@[reassoc (attr := simp)]
theorem baseChangeMove_snd {i j : ι} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : Z ⟶ (X' i).obj)
    (b : Z ⟶ (schemeSpace (W j)).obj)
    (h : x ≫ (fX' i).hom ≫ (schemeSpaceMap (φ i)).hom = b ≫ (schemeSpaceMap (φ j)).hom) :
    baseChangeMove hpX x b h ≫ (fX' j).hom = b :=
  (AlgebraicSpaces.isPullback_hom B S hS (hpX j)).lift_snd _ _ _

/-- Moving a point of `X'ᵢ` to its own image is the identity. -/
theorem baseChangeMove_self {i : ι} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : Z ⟶ (X' i).obj)
    (b : Z ⟶ (schemeSpace (W i)).obj) (hb : b = x ≫ (fX' i).hom)
    (h : x ≫ (fX' i).hom ≫ (schemeSpaceMap (φ i)).hom = b ≫ (schemeSpaceMap (φ i)).hom) :
    baseChangeMove hpX x b h = x :=
  (AlgebraicSpaces.isPullback_hom B S hS (hpX i)).hom_ext (baseChangeMove_fst hpX _ _ _)
    ((baseChangeMove_snd hpX _ _ _).trans hb)

/-- Moving twice is moving once. -/
theorem baseChangeMove_baseChangeMove {i j k : ι} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : Z ⟶ (X' i).obj) (b : Z ⟶ (schemeSpace (W j)).obj) (d : Z ⟶ (schemeSpace (W k)).obj)
    (h : x ≫ (fX' i).hom ≫ (schemeSpaceMap (φ i)).hom = b ≫ (schemeSpaceMap (φ j)).hom)
    (h' : baseChangeMove hpX x b h ≫ (fX' j).hom ≫ (schemeSpaceMap (φ j)).hom =
      d ≫ (schemeSpaceMap (φ k)).hom)
    (h'' : x ≫ (fX' i).hom ≫ (schemeSpaceMap (φ i)).hom = d ≫ (schemeSpaceMap (φ k)).hom) :
    baseChangeMove hpX (baseChangeMove hpX x b h) d h' = baseChangeMove hpX x d h'' :=
  (AlgebraicSpaces.isPullback_hom B S hS (hpX k)).hom_ext
    ((baseChangeMove_fst hpX _ _ _).trans
      ((baseChangeMove_fst hpX _ _ _).trans (baseChangeMove_fst hpX _ _ _).symm))
    ((baseChangeMove_snd hpX _ _ _).trans (baseChangeMove_snd hpX _ _ _).symm)

/-- `transitionMove` depends only on the two points. -/
theorem transitionMove_congr {U : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, U i ⟶ T}
    {V : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : ∀ i, V i ⟶ U i}
    {Φ : ∀ i j, pullback (g i ≫ f i) (f j) ⟶ V j} {i j : ι}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a a' : Z ⟶ V i} {b b' : Z ⟶ U j}
    (ha : a = a') (hb : b = b') (h : a ≫ g i ≫ f i = b ≫ f j) (h' : a' ≫ g i ≫ f i = b' ≫ f j) :
    transitionMove f g Φ a b h = transitionMove f g Φ a' b' h' := by
  subst ha hb
  rfl

include hc in
/-- The underlying morphisms of presheaves satisfy `cᵢ ≫ gYᵢ = fX'ᵢ`. -/
theorem hom_comp_hom_eq_of_contraction_over (i : ι) : (c i).hom ≫ (gY i).hom = (fX' i).hom :=
  congrArg (fun m => m.hom) (hc i)

variable (hΨ : ∀ i j, Ψ i j ≫ (gY j).hom = pullback.snd _ _)
  (hψc : ∀ (i j : ι) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : Z ⟶ (X' i).obj)
    (b : Z ⟶ (schemeSpace (W j)).obj)
    (h : x ≫ (fX' i).hom ≫ (schemeSpaceMap (φ i)).hom = b ≫ (schemeSpaceMap (φ j)).hom)
    (h' : (x ≫ (c i).hom) ≫ (gY i).hom ≫ (schemeSpaceMap (φ i)).hom =
      b ≫ (schemeSpaceMap (φ j)).hom),
    transitionMove (fun i => (schemeSpaceMap (φ i)).hom) (fun i => (gY i).hom) Ψ (x ≫ (c i).hom)
        b h' = baseChangeMove hpX x b h ≫ (c j).hom)

include hc hΨ hψc in
/-- **The unit law.** Moving a point of `Yᵢ` to its own image in `Wᵢ` does nothing. -/
theorem transitionMove_self_of_isIso_structureSharp
    (hsep : ∀ i, IsSeparated B S hS (gY i).hom)
    (hdom₀ : ∀ i, IsIso (structureSharp B S hS (c i))) (i : ι) :
    pullback.lift (𝟙 (Y i).obj) (gY i).hom (by simp) ≫ Ψ i i = 𝟙 (Y i).obj := by
  have := hdom₀ i
  have hcY := hom_comp_hom_eq_of_contraction_over hc i
  let m : Y i ⟶ Y i := ObjectProperty.homMk
    (pullback.lift (𝟙 (Y i).obj) (gY i).hom (by simp) ≫ Ψ i i)
  have hm : m = 𝟙 (Y i) := by
    refine eq_of_comp_eq_of_isIso_structureSharp B S hS (c i) (gY i) (hsep i) ?_ ?_
    · ext1
      show (pullback.lift _ _ _ ≫ Ψ i i) ≫ (gY i).hom = 𝟙 _ ≫ (gY i).hom
      rw [Category.assoc, hΨ, pullback.lift_snd, Category.id_comp]
    · ext1
      show (c i).hom ≫ transitionMove (fun i => (schemeSpaceMap (φ i)).hom)
          (fun i => (gY i).hom) Ψ (𝟙 _) (gY i).hom _ = (c i).hom ≫ 𝟙 _
      rw [comp_transitionMove]
      trans transitionMove (fun i => (schemeSpaceMap (φ i)).hom) (fun i => (gY i).hom) Ψ
        (𝟙 _ ≫ (c i).hom) (fX' i).hom (by rw [Category.id_comp, ← hcY, Category.assoc])
      · congr 1
      · rw [hψc i i (𝟙 _) (fX' i).hom (by rw [Category.id_comp]),
          baseChangeMove_self hpX (𝟙 _) _ (Category.id_comp _).symm, Category.id_comp,
          Category.comp_id]
  exact congrArg (fun k => k.hom) hm

include hc hΨ hψc in
/-- **The cocycle law.** Moving a point of `Yᵢ` to `Yⱼ` and then to `Yₖ` is moving it to `Yₖ`. -/
theorem transitionMove_transitionMove_of_isIso_structureSharp
    (hsep : ∀ i, IsSeparated B S hS (gY i).hom)
    (hdom : ∀ i (T' : BigFppfOver B S hS) (h : T' ⟶ W i),
      IsIso (structureSharp B S hS
        (structureContractionBaseChange B S hS (c i) (hc i) (schemeSpaceMap h))))
    (i j k : ι) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : Z ⟶ (Y i).obj)
    (b : Z ⟶ (schemeSpace (W j)).obj) (d : Z ⟶ (schemeSpace (W k)).obj)
    (hab : a ≫ (gY i).hom ≫ (schemeSpaceMap (φ i)).hom = b ≫ (schemeSpaceMap (φ j)).hom)
    (hac : a ≫ (gY i).hom ≫ (schemeSpaceMap (φ i)).hom = d ≫ (schemeSpaceMap (φ k)).hom) :
    transitionMove (fun i => (schemeSpaceMap (φ i)).hom) (fun i => (gY i).hom) Ψ
        (transitionMove (fun i => (schemeSpaceMap (φ i)).hom) (fun i => (gY i).hom) Ψ a b hab) d
        (by rw [transitionMove_comp_assoc hΨ, ← hab, hac]) =
      transitionMove (fun i => (schemeSpaceMap (φ i)).hom) (fun i => (gY i).hom) Ψ a d hac := by
  set F : ∀ i, (schemeSpace (W i)).obj ⟶ (schemeSpace S₀).obj :=
    fun i => (schemeSpaceMap (φ i)).hom with hF
  set G : ∀ i, (Y i).obj ⟶ (schemeSpace (W i)).obj := fun i => (gY i).hom with hG
  -- the triple overlap
  let V₁ := pullback (φ i) (φ j)
  let V := pullback (pullback.fst (φ i) (φ j) ≫ φ i) (φ k)
  let tᵢ : V ⟶ W i := pullback.fst _ _ ≫ pullback.fst (φ i) (φ j)
  let tⱼ : V ⟶ W j := pullback.fst _ _ ≫ pullback.snd (φ i) (φ j)
  let tₖ : V ⟶ W k := pullback.snd _ _
  have htij : tᵢ ≫ φ i = tⱼ ≫ φ j := by
    simp only [tᵢ, tⱼ, Category.assoc, pullback.condition]
  have htik : tᵢ ≫ φ i = tₖ ≫ φ k := by
    simp only [tᵢ, tₖ, Category.assoc]
    exact pullback.condition
  have hssm : ∀ {P Q R : BigFppfOver B S hS} (p : P ⟶ Q) (q : Q ⟶ R),
      (schemeSpaceMap p).hom ≫ (schemeSpaceMap q).hom = (schemeSpaceMap (p ≫ q)).hom :=
    fun p q => (yoneda.map_comp p q).symm
  -- the base change of `Yᵢ` to the triple overlap, and its universal points
  let YV := AlgebraicSpaces.fiberProduct B S hS (gY i) (schemeSpaceMap tᵢ)
  have hYV := AlgebraicSpaces.isPullback_hom B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (gY i) (schemeSpaceMap tᵢ))
  let y₁ : YV.obj ⟶ (Y i).obj := pullback.fst (gY i).hom (schemeSpaceMap tᵢ).hom
  let y₂ : YV.obj ⟶ (schemeSpace V).obj := pullback.snd (gY i).hom (schemeSpaceMap tᵢ).hom
  have hy : y₁ ≫ (gY i).hom = y₂ ≫ (schemeSpaceMap tᵢ).hom := hYV.w
  have hab₀ : y₁ ≫ G i ≫ F i = (y₂ ≫ (schemeSpaceMap tⱼ).hom) ≫ F j := by
    simp only [G, F]
    rw [← Category.assoc, hy, Category.assoc, Category.assoc, hssm, hssm, htij]
  have hac₀ : y₁ ≫ G i ≫ F i = (y₂ ≫ (schemeSpaceMap tₖ).hom) ≫ F k := by
    simp only [G, F]
    rw [← Category.assoc, hy, Category.assoc, Category.assoc, hssm, hssm, htik]
  let m₁ := transitionMove F G Ψ (transitionMove F G Ψ y₁ (y₂ ≫ (schemeSpaceMap tⱼ).hom) hab₀)
    (y₂ ≫ (schemeSpaceMap tₖ).hom) (by rw [transitionMove_comp_assoc hΨ, ← hab₀, hac₀])
  let m₂ := transitionMove F G Ψ y₁ (y₂ ≫ (schemeSpaceMap tₖ).hom) hac₀
  -- the two maps agree on the universal points
  have hm : m₁ = m₂ := by
    let cV := structureContractionBaseChange B S hS (c i) (hc i) (schemeSpaceMap tᵢ)
    have := hdom i V tᵢ
    let x₁ : (AlgebraicSpaces.fiberProduct B S hS (fX' i) (schemeSpaceMap tᵢ)).obj ⟶ (X' i).obj :=
      pullback.fst (fX' i).hom (schemeSpaceMap tᵢ).hom
    let x₂ : (AlgebraicSpaces.fiberProduct B S hS (fX' i) (schemeSpaceMap tᵢ)).obj ⟶
        (schemeSpace V).obj := pullback.snd (fX' i).hom (schemeSpaceMap tᵢ).hom
    have hx : x₁ ≫ (fX' i).hom = x₂ ≫ (schemeSpaceMap tᵢ).hom := pullback.condition
    have hc₁ : cV.hom ≫ y₁ = x₁ ≫ (c i).hom := by
      have := structureContractionBaseChange_fst B S hS (c i) (hc i) (schemeSpaceMap tᵢ)
      exact congrArg (fun m => m.hom) this
    have hc₂ : cV.hom ≫ y₂ = x₂ := by
      have := structureContractionBaseChange_snd B S hS (c i) (hc i) (schemeSpaceMap tᵢ)
      exact congrArg (fun m => m.hom) this
    have hxj : x₁ ≫ (fX' i).hom ≫ F i = (x₂ ≫ (schemeSpaceMap tⱼ).hom) ≫ F j := by
      simp only [F]
      rw [← Category.assoc, hx, Category.assoc, Category.assoc, hssm, hssm, htij]
    have hxk : x₁ ≫ (fX' i).hom ≫ F i = (x₂ ≫ (schemeSpaceMap tₖ).hom) ≫ F k := by
      simp only [F]
      rw [← Category.assoc, hx, Category.assoc, Category.assoc, hssm, hssm, htik]
    have hc₂j : cV.hom ≫ y₂ ≫ (schemeSpaceMap tⱼ).hom = x₂ ≫ (schemeSpaceMap tⱼ).hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hc₂)
    have hc₂k : cV.hom ≫ y₂ ≫ (schemeSpaceMap tₖ).hom = x₂ ≫ (schemeSpaceMap tₖ).hom :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hc₂)
    have hbj : baseChangeMove hpX x₁ (x₂ ≫ (schemeSpaceMap tⱼ).hom) hxj ≫ (fX' j).hom ≫
        (schemeSpaceMap (φ j)).hom =
          (x₂ ≫ (schemeSpaceMap tₖ).hom) ≫ (schemeSpaceMap (φ k)).hom := by
      rw [baseChangeMove_snd_assoc, ← hxj, hxk]
    have key : cV.hom ≫ m₁ = cV.hom ≫ m₂ := by
      simp only [m₁, m₂, comp_transitionMove, hc₁, hc₂j, hc₂k]
      have hP : (baseChangeMove hpX x₁ (x₂ ≫ (schemeSpaceMap tⱼ).hom) hxj ≫ (c j).hom) ≫
          G j ≫ F j = (x₂ ≫ (schemeSpaceMap tₖ).hom) ≫ F k := by
        rw [Category.assoc, ← Category.assoc (c j).hom]
        show _ ≫ ((c j).hom ≫ (gY j).hom) ≫ _ = _
        rw [hom_comp_hom_eq_of_contraction_over hc j]
        exact hbj
      trans transitionMove F G Ψ (baseChangeMove hpX x₁ (x₂ ≫ (schemeSpaceMap tⱼ).hom) hxj ≫
        (c j).hom) (x₂ ≫ (schemeSpaceMap tₖ).hom) hP
      · congr 1
        exact hψc i j x₁ _ hxj _
      · rw [hψc j k _ _ hbj, hψc i k x₁ (x₂ ≫ (schemeSpaceMap tₖ).hom) hxk,
          baseChangeMove_baseChangeMove]
    have hmm : (ObjectProperty.homMk m₁ : YV ⟶ Y k) = ObjectProperty.homMk m₂ := by
      refine eq_of_comp_eq_of_isIso_structureSharp B S hS cV (gY k) (hsep k) ?_ ?_
      · ext1
        show m₁ ≫ (gY k).hom = m₂ ≫ (gY k).hom
        rw [transitionMove_comp hΨ, transitionMove_comp hΨ]
      · ext1
        exact key
    exact congrArg (fun m => m.hom) hmm
  -- the general case factors through the universal points
  have sq₁ : IsPullback (schemeSpaceMap (pullback.fst (φ i) (φ j))).hom
      (schemeSpaceMap (pullback.snd (φ i) (φ j))).hom (schemeSpaceMap (φ i)).hom
      (schemeSpaceMap (φ j)).hom :=
    AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_map_of_faithful (ObjectProperty.ι _)
      ((IsPullback.of_hasPullback (φ i) (φ j)).map yoneda))
  have sq₂ : IsPullback (schemeSpaceMap (pullback.fst (pullback.fst (φ i) (φ j) ≫ φ i) (φ k))).hom
      (schemeSpaceMap tₖ).hom (schemeSpaceMap (pullback.fst (φ i) (φ j) ≫ φ i)).hom
      (schemeSpaceMap (φ k)).hom :=
    AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_map_of_faithful (ObjectProperty.ι _)
      ((IsPullback.of_hasPullback (pullback.fst (φ i) (φ j) ≫ φ i) (φ k)).map yoneda))
  let v₁ : Z ⟶ (schemeSpace V₁).obj := sq₁.lift (a ≫ (gY i).hom) b
    ((Category.assoc _ _ _).trans hab)
  have hv₁ : v₁ ≫ (schemeSpaceMap (pullback.fst (φ i) (φ j))).hom = a ≫ (gY i).hom :=
    sq₁.lift_fst _ _ _
  have hv₁' : v₁ ≫ (schemeSpaceMap (pullback.snd (φ i) (φ j))).hom = b := sq₁.lift_snd _ _ _
  let v : Z ⟶ (schemeSpace V).obj := sq₂.lift v₁ d (by
    rw [← hssm, ← Category.assoc, hv₁, Category.assoc]; exact hac)
  have hv : v ≫ (schemeSpaceMap (pullback.fst (pullback.fst (φ i) (φ j) ≫ φ i) (φ k))).hom =
      v₁ := sq₂.lift_fst _ _ _
  have hvk : v ≫ (schemeSpaceMap tₖ).hom = d := sq₂.lift_snd _ _ _
  have hvi : v ≫ (schemeSpaceMap tᵢ).hom = a ≫ (gY i).hom := by
    rw [show (schemeSpaceMap tᵢ).hom = _ ≫ _ from (hssm _ _).symm, ← Category.assoc, hv, hv₁]
  have hvj : v ≫ (schemeSpaceMap tⱼ).hom = b := by
    rw [show (schemeSpaceMap tⱼ).hom = _ ≫ _ from (hssm _ _).symm, ← Category.assoc, hv, hv₁']
  let w : Z ⟶ YV.obj := hYV.lift a v hvi.symm
  have hw₁ : w ≫ y₁ = a := hYV.lift_fst _ _ _
  have hw₂ : w ≫ y₂ = v := hYV.lift_snd _ _ _
  have e₂ : w ≫ y₂ ≫ (schemeSpaceMap tⱼ).hom = b :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (schemeSpaceMap tⱼ).hom) hw₂).trans hvj)
  have e₃ : w ≫ y₂ ≫ (schemeSpaceMap tₖ).hom = d :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (schemeSpaceMap tₖ).hom) hw₂).trans hvk)
  have hL : w ≫ m₁ = transitionMove F G Ψ (transitionMove F G Ψ a b hab) d
      (by rw [transitionMove_comp_assoc hΨ, ← hab, hac]) := by
    simp only [m₁, comp_transitionMove]
    congr 2
  have hR : w ≫ m₂ = transitionMove F G Ψ a d hac := by
    simp only [m₂, comp_transitionMove]
    congr 1
  exact hL.symm.trans ((congrArg (fun m => w ≫ m) hm).trans hR)

include hc hΨ hψc in
/-- **Gluing contractions along transition maps.** Let `{φᵢ : Wᵢ ⟶ S₀}` be an fppf covering, and
`cᵢ : X ×_{S₀} Wᵢ ⟶ Yᵢ` contractions over `Wᵢ` (structure map an isomorphism after every base
change along a scheme) to algebraic spaces separated and of finite type over `Wᵢ`, with
transition maps `Ψᵢⱼ` compatible with the `cᵢ`. Then there are an algebraic space `Q` over `S₀`
with `Yᵢ = Q ×_{S₀} Wᵢ` and a morphism `c : X ⟶ Q` over `S₀` restricting to every `cᵢ`. -/
theorem exists_glued_contraction_of_transitions
    (hcov : IsFppfCovering B S hS (fun i => (schemeSpace (W i)).obj)
      (fun i => (schemeSpaceMap (φ i)).hom))
    (hsep : ∀ i, IsSeparated B S hS (gY i).hom) (hft : ∀ i, IsFiniteType B S hS (gY i).hom)
    (hdom₀ : ∀ i, IsIso (structureSharp B S hS (c i)))
    (hdom : ∀ i (T' : BigFppfOver B S hS) (h : T' ⟶ W i),
      IsIso (structureSharp B S hS
        (structureContractionBaseChange B S hS (c i) (hc i) (schemeSpaceMap h)))) :
    ∃ (Q : AlgebraicSpaces B S hS) (q : Q ⟶ schemeSpace S₀) (r : ∀ i, Y i ⟶ Q) (cQ : X ⟶ Q),
      (∀ i, IsPullback (r i) (gY i) q (schemeSpaceMap (φ i))) ∧ cQ ≫ q = fX ∧
        ∀ i, pX i ≫ cQ = c i ≫ r i := by
  obtain ⟨Q₀, q₀, r₀, hQ, hpb, hmove⟩ := Descent.exists_glued_of_transitions hcov hΨ
    (fun i => (Y i).2) hft
    (transitionMove_self_of_isIso_structureSharp hpX hc hΨ hψc hsep hdom₀)
    (fun i j k _ a b d hab hac =>
      transitionMove_transitionMove_of_isIso_structureSharp hpX hc hΨ hψc hsep hdom i j k a b d
        hab hac)
  let Q : AlgebraicSpaces B S hS := ⟨Q₀, hQ⟩
  let q : Q ⟶ schemeSpace S₀ := ObjectProperty.homMk q₀
  let r : ∀ i, Y i ⟶ Q := fun i => ObjectProperty.homMk (r₀ i)
  have hpb' : ∀ i, IsPullback (r i) (gY i) q (schemeSpaceMap (φ i)) := fun i =>
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (hpb i)
  -- the covering of `X`
  have hφ : IsFpqcCovering B S hS (fun i => (schemeSpaceMap (φ i)).hom) :=
    isFpqcCovering_of_isFppfCovering B S hS _ _ hcov
  have hcovX : IsFpqcCovering B S hS (fun i => (pX i).hom) := by
    have h₁ := isFpqcCovering_pullback_fst B S hS (fun i => schemeSpace (W i))
      (fun i => schemeSpaceMap (φ i)) hφ X fX
    have h₂ := isFpqcCovering_isoComp B S hS (fun i => ((hpX i).isoPullback.hom).hom)
      (fun i => (pullback.fst fX (schemeSpaceMap (φ i))).hom) h₁
    convert h₂ using 2 with i
    exact congrArg (fun k : X' i ⟶ X => k.hom) (hpX i).isoPullback_hom_fst.symm
  have hagree : ∀ i j,
      (ObjectProperty.homMk (pullback.fst (pX i).hom (pX j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (pX i) (pX j) ⟶ X' i) ≫ (c i ≫ r i) =
      (ObjectProperty.homMk (pullback.snd (pX i).hom (pX j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (pX i) (pX j) ⟶ X' j) ≫ (c j ≫ r j) := by
    intro i j
    ext1
    let x : (AlgebraicSpaces.fiberProduct B S hS (pX i) (pX j)).obj ⟶ (X' i).obj :=
      pullback.fst (pX i).hom (pX j).hom
    let y : (AlgebraicSpaces.fiberProduct B S hS (pX i) (pX j)).obj ⟶ (X' j).obj :=
      pullback.snd (pX i).hom (pX j).hom
    have hxy : x ≫ (pX i).hom = y ≫ (pX j).hom := pullback.condition
    have hwi := (AlgebraicSpaces.isPullback_hom B S hS (hpX i)).w
    have hwj := (AlgebraicSpaces.isPullback_hom B S hS (hpX j)).w
    have h : x ≫ (fX' i).hom ≫ (schemeSpaceMap (φ i)).hom =
        (y ≫ (fX' j).hom) ≫ (schemeSpaceMap (φ j)).hom := by
      rw [← hwi, ← Category.assoc, hxy, Category.assoc, hwj, Category.assoc]
    have h' : (x ≫ (c i).hom) ≫ (gY i).hom ≫ (schemeSpaceMap (φ i)).hom =
        (y ≫ (fX' j).hom) ≫ (schemeSpaceMap (φ j)).hom := by
      rw [Category.assoc, ← Category.assoc (c i).hom, hom_comp_hom_eq_of_contraction_over hc i, h]
    have hb : baseChangeMove hpX x (y ≫ (fX' j).hom) h = y :=
      (AlgebraicSpaces.isPullback_hom B S hS (hpX j)).hom_ext
        ((baseChangeMove_fst hpX _ _ _).trans hxy) (baseChangeMove_snd hpX _ _ _)
    have hm := hmove i j (x ≫ (c i).hom) (y ≫ (fX' j).hom) h'
    rw [hψc i j x _ h h', hb] at hm
    show x ≫ (c i).hom ≫ r₀ i = y ≫ (c j).hom ≫ r₀ j
    rw [← Category.assoc, ← hm, Category.assoc]
  obtain ⟨cQ, hcQ, -⟩ := existsUnique_desc_of_fpqcCovering B S hS pX hcovX Q
    (fun i => c i ≫ r i) hagree
  refine ⟨Q, q, r, cQ, hpb', ?_, hcQ⟩
  obtain ⟨k, -, hk⟩ := existsUnique_desc_of_fpqcCovering B S hS pX hcovX (schemeSpace S₀)
    (fun i => pX i ≫ fX) (fun i j => by
      rw [← Category.assoc, ← Category.assoc,
        (AlgebraicSpaces.isPullback_fiberProduct B S hS (pX i) (pX j)).w])
  refine (hk _ fun i => ?_).trans (hk _ fun i => rfl).symm
  rw [← Category.assoc, hcQ, Category.assoc, (hpb' i).w, ← Category.assoc, hc, (hpX i).w]

end AlgebraicGeometry.Space

end
