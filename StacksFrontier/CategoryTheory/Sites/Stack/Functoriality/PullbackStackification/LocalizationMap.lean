module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackAdjunction
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyExistence
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeLocallyBijective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functor `Ψ : u_p 𝒮 ⥤ u_p 𝒮'` and the fibres of `u_p 𝒮`

Let `u : 𝒞 ⥤ 𝒟` be a functor and let `G : 𝒮 ⥤ 𝒮'` be a 1-morphism of fibred categories over
`𝒞`. The functor `Φ : u_pp 𝒮 ⥤ u_pp 𝒮'`, `(V, x, φ) ↦ (V, G x, φ)`, induces
`Ψ : u_p 𝒮 ⥤ u_p 𝒮'` on the localizations, and `Ψ` is a 1-morphism of fibred categories over
`𝒟`. We also describe the objects and isomorphisms of the fibres of `u_p 𝒮`, and write morphisms
of these fibres as fractions.

## Main definitions

* `CategoryTheory.commaMapOver`: the functor `Φ : u_pp 𝒮 ⥤ u_pp 𝒮'`.
* `CategoryTheory.pullbackLocalizationMap`: the functor `Ψ : u_p 𝒮 ⥤ u_p 𝒮'`.

## Main results

* `CategoryTheory.Comma.isFibredOneMorphism_pullbackLocalizationMap`: `Ψ` is a 1-morphism of
  fibred categories over `𝒟`.

## References

* [Stacks Project, Tag 04WR](https://stacks.math.columbia.edu/tag/04WR)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/-! ### The functor `Ψ : u_p 𝒮 ⥤ u_p 𝒮'` -/

section Aux

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {𝒮' : Type u₄} [Category.{v₄} 𝒮']

/-- The functor `Φ : u_pp 𝒮 ⥤ u_pp 𝒮'`, `(V, x, φ) ↦ (V, G x, φ)`, induced by a 1-morphism
`G : 𝒮 ⥤ 𝒮'` over the base. -/
@[sga "4 IV 9.5.2" "partial"]
abbrev commaMapOver (u : 𝒞 ⥤ 𝒟) {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}
    (hG : G ⋙ p' = p) : Comma (𝟭 𝒟) (p ⋙ u) ⥤ Comma (𝟭 𝒟) (p' ⋙ u) :=
  Comma.map (F₁ := 𝟭 𝒟) (F₂ := G) (F := 𝟭 𝒟) (𝟙 _)
    (eqToHom (by rw [Functor.comp_id, ← Functor.assoc, hG]))

variable (u : 𝒞 ⥤ 𝒟) {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} (hG : G ⋙ p' = p)

/-- The `𝒟`-component of `Φ Z` is that of `Z`. -/
lemma commaMapOver_obj_left (Z : Comma (𝟭 𝒟) (p ⋙ u)) :
    ((commaMapOver u hG).obj Z).left = Z.left := rfl

/-- The `𝒮'`-component of `Φ Z` is `G` of the `𝒮`-component of `Z`. -/
lemma commaMapOver_obj_right (Z : Comma (𝟭 𝒟) (p ⋙ u)) :
    ((commaMapOver u hG).obj Z).right = G.obj Z.right := rfl

/-- The `𝒟`-component of `Φ f` is that of `f`. -/
lemma commaMapOver_map_left {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    ((commaMapOver u hG).map f).left = f.left := rfl

/-- The `𝒮'`-component of `Φ f` is `G` of the `𝒮`-component of `f`. -/
lemma commaMapOver_map_right {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    ((commaMapOver u hG).map f).right = G.map f.right := rfl

/-- `Φ` commutes with the projections to `𝒟`. -/
lemma commaMapOver_comp_fst :
    commaMapOver u hG ⋙ Comma.fst (𝟭 𝒟) (p' ⋙ u) = Comma.fst (𝟭 𝒟) (p ⋙ u) := rfl

private lemma isStronglyCartesian_eqToHom_comp_eqToHom {E : Type u₁} [Category.{v₁} E]
    {F : Type u₂} [Category.{v₂} F] {π : F ⥤ E} {R R' T T' : E} {a b : F}
    (hR : R' = R) (hT : T = T') {g : R ⟶ T} {φ : a ⟶ b} (h : π.IsStronglyCartesian g φ) :
    π.IsStronglyCartesian (eqToHom hR ≫ g ≫ eqToHom hT) φ := by
  subst hR hT; simpa using h

/-- A morphism strongly cartesian over some morphism of the base lies in `stronglyCartesianOver`. -/
private lemma stronglyCartesianOver_of_isStronglyCartesian_aux {𝒮 : Type u₃} [Category.{v₃} 𝒮]
    {𝒞 : Type u₁} [Category.{v₁} 𝒞] {p : 𝒮 ⥤ 𝒞} {R S : 𝒞} {a b : 𝒮} {f : R ⟶ S} {φ : a ⟶ b}
    (h : p.IsStronglyCartesian f φ) : stronglyCartesianOver p φ := by
  have := h.toIsHomLift
  dsimp only [stronglyCartesianOver]
  rw [IsHomLift.fac' p f φ]
  exact isStronglyCartesian_eqToHom_comp_eqToHom _ _ h

/-- `Φ` carries the fraction class `R` of Stacks 04WF for `p` into the one for `p'`. -/
lemma idBaseStronglyCartesian_commaMapOver (hGG : p.IsFibredOneMorphism p' G)
    {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} {f : Z ⟶ Z'}
    (hf : Comma.idBaseStronglyCartesian p u f) :
    Comma.idBaseStronglyCartesian p' u ((commaMapOver u hGG.comp_eq).map f) :=
  ⟨hf.1, stronglyCartesianOver_of_isStronglyCartesian_aux (hGG.map_isStronglyCartesian _ _ hf.2)⟩

/-- The composite of `Φ` with the localization functor of `u_pp 𝒮'` inverts the fraction class
of `u_pp 𝒮`. -/
lemma isInvertedBy_commaMapOver_Q (hGG : p.IsFibredOneMorphism p' G) :
    (Comma.idBaseStronglyCartesian p u).IsInvertedBy
      (commaMapOver u hGG.comp_eq ⋙ (Comma.idBaseStronglyCartesian p' u).Q) := fun _ _ _ hf ↦
  Localization.inverts (Comma.idBaseStronglyCartesian p' u).Q _ _
    (idBaseStronglyCartesian_commaMapOver u hGG hf)

/-- The functor `Ψ : u_p 𝒮 ⥤ u_p 𝒮'` induced by a 1-morphism `G : 𝒮 ⥤ 𝒮'` of fibred categories
over `𝒞`. -/
noncomputable def pullbackLocalizationMap (hGG : p.IsFibredOneMorphism p' G) :
    Comma.pullbackLocalization p u ⥤ Comma.pullbackLocalization p' u :=
  Localization.Construction.lift
    (commaMapOver u hGG.comp_eq ⋙ (Comma.idBaseStronglyCartesian p' u).Q)
    (isInvertedBy_commaMapOver_Q u hGG)

/-- `Ψ` restricts along the localization functor of `u_pp 𝒮` to `Φ` followed by the localization
functor of `u_pp 𝒮'`. -/
lemma pullbackLocalizationMap_fac (hGG : p.IsFibredOneMorphism p' G) :
    (Comma.idBaseStronglyCartesian p u).Q ⋙ pullbackLocalizationMap u hGG =
      commaMapOver u hGG.comp_eq ⋙ (Comma.idBaseStronglyCartesian p' u).Q :=
  Localization.Construction.fac _ _

/-- `Ψ` sends `Q Z` to `Q' (Φ Z)`. -/
@[simp]
lemma pullbackLocalizationMap_obj (hGG : p.IsFibredOneMorphism p' G)
    (Z : Comma (𝟭 𝒟) (p ⋙ u)) :
    (pullbackLocalizationMap u hGG).obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z) =
      (Comma.idBaseStronglyCartesian p' u).Q.obj ((commaMapOver u hGG.comp_eq).obj Z) :=
  Functor.congr_obj (pullbackLocalizationMap_fac u hGG) Z

/-- `Ψ` sends `Q f` to `Q' (Φ f)`, up to the identifications of `pullbackLocalizationMap_obj`. -/
lemma pullbackLocalizationMap_map (hGG : p.IsFibredOneMorphism p' G)
    {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    (pullbackLocalizationMap u hGG).map ((Comma.idBaseStronglyCartesian p u).Q.map f) =
      eqToHom (pullbackLocalizationMap_obj u hGG Z) ≫
        (Comma.idBaseStronglyCartesian p' u).Q.map ((commaMapOver u hGG.comp_eq).map f) ≫
          eqToHom (pullbackLocalizationMap_obj u hGG Z').symm := by
  simpa using Functor.congr_hom (pullbackLocalizationMap_fac u hGG) f

/-- `Ψ` commutes with the projections to `𝒟`. -/
lemma pullbackLocalizationMap_comp_pullbackProj (hGG : p.IsFibredOneMorphism p' G) :
    pullbackLocalizationMap u hGG ⋙ Comma.pullbackProj p' u = Comma.pullbackProj p u :=
  Comma.pullbackProj_uniq p u _ <| by
    rw [← Functor.assoc, pullbackLocalizationMap_fac, Functor.assoc, Comma.pullbackProj_fac]
    rfl

/-- A functor `H : u_p 𝒮 ⥤ 𝒯` whose restriction along the localization functor is
`Φ ⋙ Q' ⋙ G'` is `Ψ ⋙ G'`. -/
lemma eq_pullbackLocalizationMap_comp {𝒯 : Type u₅} [Category.{v₅} 𝒯]
    (hGG : p.IsFibredOneMorphism p' G) (G' : Comma.pullbackLocalization p' u ⥤ 𝒯)
    (H : Comma.pullbackLocalization p u ⥤ 𝒯)
    (hH : (Comma.idBaseStronglyCartesian p u).Q ⋙ H =
      commaMapOver u hGG.comp_eq ⋙ (Comma.idBaseStronglyCartesian p' u).Q ⋙ G') :
    H = pullbackLocalizationMap u hGG ⋙ G' :=
  Localization.Construction.uniq _ _ <| by
    rw [hH]
    simp [← Functor.assoc, pullbackLocalizationMap_fac]

end Aux

/-! ### `Ψ` is a 1-morphism of fibred categories over `𝒟` -/

namespace Comma

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {𝒮' : Type u₄} [Category.{v₄} 𝒮']

variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)

section

variable [p.IsFibered] [HasNonemptyFiniteLimits 𝒞]

/-- A morphism of `u_pp 𝒮` whose `𝒮`-component is an `eqToHom` becomes strongly cartesian over
its own `𝒟`-component in `u_p 𝒮`. -/
lemma isStronglyCartesian_Q_of_right_eqToHom
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (g : Z ⟶ Z') (h : Z.right = Z'.right)
    (hg : g.right = eqToHom h) :
    (pullbackProj p u).IsStronglyCartesian g.left
      ((idBaseStronglyCartesian p u).Q.map g) := by
  obtain ⟨V, x, φ⟩ := Z
  obtain ⟨V', y, ψ⟩ := Z'
  dsimp only at h
  subst h
  have hgr : g.right = 𝟙 x := by simpa using hg
  obtain ⟨b, hb⟩ : ∃ b : V ⟶ V', g.left = b := ⟨g.left, rfl⟩
  have hφ : φ = b ≫ ψ := by
    have hw := g.w
    rw [hgr, hb] at hw
    simpa using hw.symm
  have hZ : (Comma.mk V x φ : Comma (𝟭 𝒟) (p ⋙ u)) =
      (Comma.mk V x (b ≫ ψ) : Comma (𝟭 𝒟) (p ⋙ u)) := by rw [hφ]
  have hfac : eqToHom hZ ≫
      baseChangeHom p u ((Comma.mk V' x ψ : Comma (𝟭 𝒟) (p ⋙ u))) b = g := by
    refine Comma.hom_ext _ _ ?_ ?_
    · rw [Comma.comp_left, eqToHom_left_comma, baseChangeHom_left, hb]
      simp
    · rw [Comma.comp_right, eqToHom_right_comma, baseChangeHom_right, hgr]
      simp
  rw [hb, ← hfac, Functor.map_comp]
  have hbc := isStronglyCartesian_Q_baseChangeHom p u hu
    ((Comma.mk V' x ψ : Comma (𝟭 𝒟) (p ⋙ u))) b
  have hlift : (pullbackProj p u).IsHomLift (𝟙 ((𝟭 𝒟).obj V))
      ((idBaseStronglyCartesian p u).Q.map (eqToHom hZ)) := by
    rw [eqToHom_map]
    exact IsHomLift.eqToHom_domain_lift_id _
      (pullbackProj_obj p u ((Comma.mk V x φ : Comma (𝟭 𝒟) (p ⋙ u))))
  have : IsIso ((idBaseStronglyCartesian p u).Q.map (eqToHom hZ)) := inferInstance
  have := hlift
  exact PullbackAdjunction.isStronglyCartesian_id_comp
    (Functor.IsStronglyCartesian.of_isIso (pullbackProj p u) (𝟙 ((𝟭 𝒟).obj V)) _) hbc

end

/-- Decorating the source and the target of a strongly cartesian morphism with `eqToHom`s does not
change the base morphism it is strongly cartesian over. -/
private lemma isStronglyCartesian_eqToHom_comp_map_eqToHom {ℰ : Type u₁} [Category.{v₁} ℰ]
    {𝒳 : Type u₂} [Category.{v₂} 𝒳] {P : 𝒳 ⥤ ℰ} {a a' b b' : 𝒳} (ha : a' = a) (hb : b = b')
    {R S : ℰ} {f : R ⟶ S} {φ : a ⟶ b} (h : P.IsStronglyCartesian f φ) :
    P.IsStronglyCartesian f (eqToHom ha ≫ φ ≫ eqToHom hb) := by
  subst ha hb; simpa using h

/-- `Ψ` is a 1-morphism of fibred categories over `𝒟`. -/
lemma isFibredOneMorphism_pullbackLocalizationMap {p' : 𝒮' ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}
    [p.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    (hGG : p.IsFibredOneMorphism p' G) :
    (pullbackProj p u).IsFibredOneMorphism (pullbackProj p' u)
      (pullbackLocalizationMap u hGG) := by
  refine PullbackAdjunction.isFibredOneMorphism_of_exists_lift _ _ _
    (pullbackLocalizationMap_comp_pullbackProj u hGG) ?_
  intro b V β
  obtain ⟨X, rfl⟩ : ∃ X, (idBaseStronglyCartesian p u).Q.obj X = b :=
    ⟨_, (Localization.Construction.objEquiv (idBaseStronglyCartesian p u)).apply_symm_apply b⟩
  have hX : (pullbackProj p u).obj ((idBaseStronglyCartesian p u).Q.obj X) = X.left :=
    pullbackProj_obj p u X
  obtain ⟨β', rfl⟩ : ∃ β' : V ⟶ X.left, β' ≫ eqToHom hX.symm = β := ⟨β ≫ eqToHom hX, by simp⟩
  refine ⟨_, (idBaseStronglyCartesian p u).Q.map (baseChangeHom p u X β'), ?_, ?_⟩
  · exact PullbackAdjunction.isStronglyCartesian_comp_eqToHom hX.symm β' _
      (isStronglyCartesian_Q_baseChangeHom p u hu X β')
  · have hsc : (pullbackProj p' u).IsStronglyCartesian β'
        ((idBaseStronglyCartesian p' u).Q.map
          ((commaMapOver u hGG.comp_eq).map (baseChangeHom p u X β'))) :=
      isStronglyCartesian_Q_of_right_eqToHom p' u hu
        ((commaMapOver u hGG.comp_eq).map (baseChangeHom p u X β')) rfl (by simp)
    rw [pullbackLocalizationMap_map]
    exact PullbackAdjunction.isStronglyCartesian_comp_eqToHom hX.symm β' _
      (isStronglyCartesian_eqToHom_comp_map_eqToHom _ _ hsc)

/-! ### Objects and isomorphisms of the fibres of `u_p 𝒮` -/

/-- A morphism strongly cartesian over some morphism of `𝒞` is strongly cartesian over its own
image, i.e. lies in `stronglyCartesianOver p` (Stacks 03WQ). -/
lemma stronglyCartesianOver_of_isStronglyCartesian {R S : 𝒞} {a b : 𝒮} {f : R ⟶ S}
    {φ : a ⟶ b} (h : p.IsStronglyCartesian f φ) : stronglyCartesianOver p φ :=
  stronglyCartesianOver_of_isStronglyCartesian_aux h

/-- The morphism `(V, a, ψ) ⟶ (V, b, ψ ∘ u(p(α)))` of `u_pp 𝒮` with identity `𝒟`-component
determined by a morphism `α : a ⟶ b` of `𝒮`. -/
def idBaseHom {a b : 𝒮} (α : a ⟶ b) {V : 𝒟} (ψ : V ⟶ u.obj (p.obj a)) :
    (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) ⟶
      (Comma.mk V b (ψ ≫ (p ⋙ u).map α) : Comma (𝟭 𝒟) (p ⋙ u)) where
  left := 𝟙 V
  right := α
  w := by simp

/-- The `𝒟`-component of `Comma.idBaseHom` is the identity. -/
@[simp]
lemma idBaseHom_left {a b : 𝒮} (α : a ⟶ b) {V : 𝒟} (ψ : V ⟶ u.obj (p.obj a)) :
    (idBaseHom p u α ψ).left = 𝟙 V := rfl

/-- The `𝒮`-component of `Comma.idBaseHom` is `α`. -/
@[simp]
lemma idBaseHom_right {a b : 𝒮} (α : a ⟶ b) {V : 𝒟} (ψ : V ⟶ u.obj (p.obj a)) :
    (idBaseHom p u α ψ).right = α := rfl

/-- `Comma.idBaseHom` lies in the right multiplicative system `R` of Stacks 04WF as soon as `α`
is strongly cartesian. -/
lemma idBaseStronglyCartesian_idBaseHom {a b : 𝒮} {α : a ⟶ b} (hα : stronglyCartesianOver p α)
    {V : 𝒟} (ψ : V ⟶ u.obj (p.obj a)) :
    idBaseStronglyCartesian p u (idBaseHom p u α ψ) := ⟨⟨rfl, by simp⟩, hα⟩

/-- The morphism `(V, c, ψ') ⟶ (V, a, ψ)` of `u_pp 𝒮` with identity `𝒟`-component determined by
a morphism `σ : c ⟶ a` of `𝒮` together with a factorisation `ψ = ψ' ∘ u(p σ)`. -/
def idBaseHomTo {c a : 𝒮} (σ : c ⟶ a) {V : 𝒟} (ψ' : V ⟶ u.obj (p.obj c))
    (ψ : V ⟶ u.obj (p.obj a)) (h : ψ' ≫ (p ⋙ u).map σ = ψ) :
    (Comma.mk V c ψ' : Comma (𝟭 𝒟) (p ⋙ u)) ⟶
      (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) where
  left := 𝟙 V
  right := σ
  w := by simpa using h.symm

/-- The `𝒟`-component of `Comma.idBaseHomTo` is the identity. -/
@[simp]
lemma idBaseHomTo_left {c a : 𝒮} (σ : c ⟶ a) {V : 𝒟} (ψ' : V ⟶ u.obj (p.obj c))
    (ψ : V ⟶ u.obj (p.obj a)) (h : ψ' ≫ (p ⋙ u).map σ = ψ) :
    (idBaseHomTo p u σ ψ' ψ h).left = 𝟙 V := rfl

/-- The `𝒮`-component of `Comma.idBaseHomTo` is `σ`. -/
@[simp]
lemma idBaseHomTo_right {c a : 𝒮} (σ : c ⟶ a) {V : 𝒟} (ψ' : V ⟶ u.obj (p.obj c))
    (ψ : V ⟶ u.obj (p.obj a)) (h : ψ' ≫ (p ⋙ u).map σ = ψ) :
    (idBaseHomTo p u σ ψ' ψ h).right = σ := rfl

/-- `Comma.idBaseHomTo` lies in the right multiplicative system `R` of Stacks 04WF as soon as `σ`
is strongly cartesian. -/
lemma idBaseStronglyCartesian_idBaseHomTo {c a : 𝒮} {σ : c ⟶ a}
    (hσ : stronglyCartesianOver p σ) {V : 𝒟} (ψ' : V ⟶ u.obj (p.obj c))
    (ψ : V ⟶ u.obj (p.obj a)) (h : ψ' ≫ (p ⋙ u).map σ = ψ) :
    idBaseStronglyCartesian p u (idBaseHomTo p u σ ψ' ψ h) := ⟨⟨rfl, by simp⟩, hσ⟩

/-- A morphism of `u_pp 𝒮` with identity `𝒟`-component is `Comma.idBaseHomTo` of its
`𝒮`-component. -/
private lemma exists_idBaseHomTo_eq_of_left_eq_id {V : 𝒟} {c a : 𝒮}
    {ψ' : V ⟶ u.obj (p.obj c)} {ψ : V ⟶ u.obj (p.obj a)}
    {s : (Comma.mk V c ψ' : Comma (𝟭 𝒟) (p ⋙ u)) ⟶ Comma.mk V a ψ} (hs : s.left = 𝟙 V) :
    ∃ hψ : ψ' ≫ (p ⋙ u).map s.right = ψ, idBaseHomTo p u s.right ψ' ψ hψ = s := by
  have hψ : ψ' ≫ (p ⋙ u).map s.right = ψ := by
    have hw := s.w
    rw [hs] at hw
    simpa using hw.symm
  exact ⟨hψ, Comma.hom_ext _ _ (by rw [idBaseHomTo_left, hs]) rfl⟩

/-- The object `Q(V, a, ψ)` of `u_p 𝒮`, read in the fibre over `V`. -/
noncomputable def fiberObj (V : 𝒟) (a : 𝒮) (ψ : V ⟶ u.obj (p.obj a)) :
    (pullbackProj p u).Fiber V :=
  Functor.Fiber.mk (pullbackProj_obj p u (Comma.mk V a ψ))

/-- The underlying object of `Comma.fiberObj p u V a ψ` is `Q(V, a, ψ)`. -/
@[simp]
lemma fiberObj_val (V : 𝒟) (a : 𝒮) (ψ : V ⟶ u.obj (p.obj a)) :
    (fiberObj p u V a ψ).1 =
      (idBaseStronglyCartesian p u).Q.obj (Comma.mk V a ψ) := rfl

/-- Every object of a fibre of `u_p 𝒮` is of the form `Q(V, a, ψ)`. -/
lemma exists_fiberObj_eq (V : 𝒟) (A : (pullbackProj p u).Fiber V) :
    ∃ (a : 𝒮) (ψ : V ⟶ u.obj (p.obj a)), A = fiberObj p u V a ψ := by
  obtain ⟨A, hA⟩ := A
  obtain ⟨Y, rfl⟩ : ∃ Y, (idBaseStronglyCartesian p u).Q.obj Y = A :=
    ⟨_, (Localization.Construction.objEquiv (idBaseStronglyCartesian p u)).apply_symm_apply A⟩
  obtain ⟨V₀, a, ψ⟩ := Y
  have hV : V₀ = V := (pullbackProj_obj p u (Comma.mk V₀ a ψ)).symm.trans hA
  subst hV
  exact ⟨a, ψ, rfl⟩

/-- A morphism of `u_pp 𝒮` between two objects with the same `𝒟`-component and with identity
`𝒟`-component lies over `𝟙 V` in `u_p 𝒮`. -/
lemma isHomLift_Q_map_idBaseHom {a b : 𝒮} (α : a ⟶ b) {V : 𝒟} (ψ : V ⟶ u.obj (p.obj a)) :
    (pullbackProj p u).IsHomLift (𝟙 V)
      ((idBaseStronglyCartesian p u).Q.map (idBaseHom p u α ψ)) := by
  refine IsHomLift.of_fac' _ _ _ (pullbackProj_obj p u (Comma.mk V a ψ))
    (pullbackProj_obj p u (Comma.mk V b (ψ ≫ (p ⋙ u).map α))) ?_
  rw [pullbackProj_map, idBaseHom_left]
  simp only [Category.id_comp, eqToHom_trans]
  rfl

/-- An isomorphism `α : a ≅ b` of `𝒮` gives an isomorphism of the fibre of `u_p 𝒮` over `V`
between `Q(V, a, ψ)` and `Q(V, b, ψ ∘ u(p(α)))`. -/
noncomputable def fiberObjIsoOfIso {a b : 𝒮} (α : a ⟶ b) [IsIso α] {V : 𝒟}
    (ψ : V ⟶ u.obj (p.obj a)) :
    fiberObj p u V a ψ ≅ fiberObj p u V b (ψ ≫ (p ⋙ u).map α) :=
  have : IsIso ((idBaseStronglyCartesian p u).Q.map (idBaseHom p u α ψ)) := by
    have : IsIso (idBaseHom p u α ψ) :=
      ⟨⟨⟨𝟙 V, inv α, by simp⟩, Comma.hom_ext _ _ (by simp) (by simp),
        Comma.hom_ext _ _ (by simp) (by simp)⟩⟩
    infer_instance
  Functor.Fiber.isoMk (asIso ((idBaseStronglyCartesian p u).Q.map (idBaseHom p u α ψ)))
    (isHomLift_Q_map_idBaseHom p u α ψ)

section

variable [p.IsFibered] [HasNonemptyFiniteLimits 𝒞]

/-- A strongly cartesian `α : a ⟶ b` of `𝒮` becomes an isomorphism of the fibre of `u_p 𝒮` over
`V` between `Q(V, a, ψ)` and `Q(V, b, ψ ∘ u(p(α)))`. -/
noncomputable def fiberObjIsoOfStronglyCartesian {a b : 𝒮} {α : a ⟶ b}
    (hα : stronglyCartesianOver p α) {V : 𝒟} (ψ : V ⟶ u.obj (p.obj a)) :
    fiberObj p u V a ψ ≅ fiberObj p u V b (ψ ≫ (p ⋙ u).map α) :=
  have : IsIso ((idBaseStronglyCartesian p u).Q.map (idBaseHom p u α ψ)) :=
    Localization.inverts _ (idBaseStronglyCartesian p u) _
      (idBaseStronglyCartesian_idBaseHom p u hα ψ)
  Functor.Fiber.isoMk (asIso ((idBaseStronglyCartesian p u).Q.map (idBaseHom p u α ψ)))
    (isHomLift_Q_map_idBaseHom p u α ψ)

/-- The chosen pullback of `Q(V, a, ψ)` along `β : V₁ ⟶ V` is isomorphic in the fibre to
`Q(V₁, a, β ∘ ψ)`. -/
noncomputable def pullbackFiberObjIso
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    (V : 𝒟) (a : 𝒮) (ψ : V ⟶ u.obj (p.obj a)) {V₁ : 𝒟} (β : V₁ ⟶ V) :
    haveI : (pullbackProj p u).IsFibered := isFibered_pullbackProj p u hu
    Functor.pullbackFiber (pullbackProj p u) (fiberObj p u V a ψ) β ≅
      fiberObj p u V₁ a (β ≫ ψ) :=
  haveI : (pullbackProj p u).IsFibered := isFibered_pullbackProj p u hu
  have := isStronglyCartesian_Q_baseChangeHom p u hu (Comma.mk V a ψ) β
  Functor.fiberIsoOfCartesian β
    (Functor.IsPreFibered.pullbackMap (fiberObj p u V a ψ).2 β)
    ((idBaseStronglyCartesian p u).Q.map (baseChangeHom p u (Comma.mk V a ψ) β))
    inferInstance inferInstance

/-- `Comma.pullbackFiberObjIso` carries the reindexing morphism to the chosen cartesian lift. -/
lemma pullbackFiberObjIso_hom_fac
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    (V : 𝒟) (a : 𝒮) (ψ : V ⟶ u.obj (p.obj a)) {V₁ : 𝒟} (β : V₁ ⟶ V) :
    haveI : (pullbackProj p u).IsFibered := isFibered_pullbackProj p u hu
    Functor.Fiber.fiberInclusion.map (pullbackFiberObjIso p u hu V a ψ β).hom ≫
        (idBaseStronglyCartesian p u).Q.map
          (baseChangeHom p u (Comma.mk V a ψ : Comma (𝟭 𝒟) (p ⋙ u)) β) =
      Functor.IsPreFibered.pullbackMap (fiberObj p u V a ψ).2 β :=
  have : (pullbackProj p u).IsFibered := isFibered_pullbackProj p u hu
  have := isStronglyCartesian_Q_baseChangeHom p u hu (Comma.mk V a ψ) β
  Functor.fiberIsoOfCartesian_hom_fac β _ _ inferInstance inferInstance

/-- Every morphism of `u_p 𝒮` is the image of a right fraction of `u_pp 𝒮`. -/
private lemma exists_rightFraction_map_comp
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    {X Y : Comma (𝟭 𝒟) (p ⋙ u)}
    (χ : (idBaseStronglyCartesian p u).Q.obj X ⟶ (idBaseStronglyCartesian p u).Q.obj Y) :
    ∃ ϕ : (idBaseStronglyCartesian p u).RightFraction X Y,
      (idBaseStronglyCartesian p u).Q.map ϕ.s ≫ χ = (idBaseStronglyCartesian p u).Q.map ϕ.f := by
  have := hasRightCalculusOfFractions_idBaseStronglyCartesian p u hu
  obtain ⟨ϕ, hϕ⟩ := Localization.exists_rightFraction (idBaseStronglyCartesian p u).Q
    (idBaseStronglyCartesian p u) χ
  exact ⟨ϕ, by rw [hϕ]; exact MorphismProperty.RightFraction.map_s_comp_map ϕ _ _⟩

omit [p.IsFibered] [HasNonemptyFiniteLimits 𝒞] in
/-- A right fraction whose denominator has `𝒟`-component an `eqToHom` is, after that
identification, one with identity `𝒟`-components. -/
private lemma exists_fraction_fiber_aux {V V'' : 𝒟} {a b c : 𝒮} {ψ : V ⟶ u.obj (p.obj a)}
    {ω : V ⟶ u.obj (p.obj b)} {ψ'' : V'' ⟶ u.obj (p.obj c)}
    {s : (Comma.mk V'' c ψ'' : Comma (𝟭 𝒟) (p ⋙ u)) ⟶ Comma.mk V a ψ}
    {f : (Comma.mk V'' c ψ'' : Comma (𝟭 𝒟) (p ⋙ u)) ⟶ Comma.mk V b ω}
    (hl : V'' = V) (hsl : s.left = eqToHom hl) (hsc : stronglyCartesianOver p s.right)
    {χ : (idBaseStronglyCartesian p u).Q.obj (Comma.mk V a ψ) ⟶
      (idBaseStronglyCartesian p u).Q.obj (Comma.mk V b ω)}
    (hχ : (pullbackProj p u).map χ = 𝟙 V)
    (hfac : (idBaseStronglyCartesian p u).Q.map s ≫ χ =
      (idBaseStronglyCartesian p u).Q.map f) :
    ∃ (c : 𝒮) (ψ' : V ⟶ u.obj (p.obj c)) (σ : c ⟶ a) (_ : stronglyCartesianOver p σ)
      (hψ : ψ' ≫ (p ⋙ u).map σ = ψ) (α : c ⟶ b) (hω : ψ' ≫ (p ⋙ u).map α = ω),
      (idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u σ ψ' ψ hψ) ≫ χ =
        (idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u α ψ' ω hω) := by
  subst hl
  have hsleft : s.left = 𝟙 V'' := by simpa using hsl
  obtain ⟨hψ, hse⟩ := exists_idBaseHomTo_eq_of_left_eq_id p u hsleft
  have hfleft : f.left = 𝟙 V'' := by
    have hd := congrArg (fun t ↦ (pullbackProj p u).map t) hfac
    simp only [Functor.map_comp, pullbackProj_map, hsleft] at hd
    rw [← hd, hχ]
    exact Category.id_comp _
  obtain ⟨hω, hfe⟩ := exists_idBaseHomTo_eq_of_left_eq_id p u hfleft
  refine ⟨c, ψ'', s.right, hsc, hψ, f.right, hω, ?_⟩
  rw [hse, hfe]
  exact hfac

omit [p.IsFibered] [HasNonemptyFiniteLimits 𝒞] in
/-- `Comma.idBaseHomTo` is compatible with composition in `𝒮`. -/
lemma idBaseHomTo_comp {c₂ c₁ a : 𝒮} (σ₂ : c₂ ⟶ c₁) (σ₁ : c₁ ⟶ a) {V : 𝒟}
    (ψ₂ : V ⟶ u.obj (p.obj c₂)) (ψ₁ : V ⟶ u.obj (p.obj c₁)) (ψ : V ⟶ u.obj (p.obj a))
    (h₂ : ψ₂ ≫ (p ⋙ u).map σ₂ = ψ₁) (h₁ : ψ₁ ≫ (p ⋙ u).map σ₁ = ψ) :
    idBaseHomTo p u σ₂ ψ₂ ψ₁ h₂ ≫ idBaseHomTo p u σ₁ ψ₁ ψ h₁ =
      idBaseHomTo p u (σ₂ ≫ σ₁) ψ₂ ψ
        (by rw [Functor.map_comp, ← Category.assoc, h₂, h₁]) :=
  Comma.hom_ext _ _ (by simp) (by simp)

/-- **Every morphism of a fibre of `u_p 𝒮` is a fraction with identity `𝒟`-components.** A
morphism `Q(V, a, ψ) ⟶ Q(V, b, ω)` of `u_p 𝒮` lying over `𝟙 V` is, after composition with the
image of a suitable element of the right multiplicative system `R` of Stacks 04WF, the image of a
morphism of `u_pp 𝒮`; and both that element and that morphism may be taken with identity
`𝒟`-component. Concretely: there are a factorisation `ψ = ψ' ∘ u(p σ)` of `ψ` through a strongly
cartesian `σ : c ⟶ a`, and a morphism `α : c ⟶ b` of `𝒮` with `ω = ψ' ∘ u(p α)`, such that
`Q(σ, id_V) ∘ χ = Q(α, id_V)`. -/
theorem exists_fraction_fiber
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    {V : 𝒟} {a b : 𝒮} (ψ : V ⟶ u.obj (p.obj a)) (ω : V ⟶ u.obj (p.obj b))
    (χ : (idBaseStronglyCartesian p u).Q.obj (Comma.mk V a ψ) ⟶
      (idBaseStronglyCartesian p u).Q.obj (Comma.mk V b ω))
    (hχ : (pullbackProj p u).map χ = 𝟙 V) :
    ∃ (c : 𝒮) (ψ' : V ⟶ u.obj (p.obj c)) (σ : c ⟶ a) (_ : stronglyCartesianOver p σ)
      (hψ : ψ' ≫ (p ⋙ u).map σ = ψ) (α : c ⟶ b) (hω : ψ' ≫ (p ⋙ u).map α = ω),
      (idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u σ ψ' ψ hψ) ≫ χ =
        (idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u α ψ' ω hω) := by
  obtain ⟨ϕ, hϕs⟩ := exists_rightFraction_map_comp p u hu χ
  obtain ⟨⟨hl, hsl⟩, hsc⟩ := ϕ.hs
  exact exists_fraction_fiber_aux p u (s := ϕ.s) (f := ϕ.f) hl hsl hsc hχ hϕs

omit [p.IsFibered] [HasNonemptyFiniteLimits 𝒞] in
/-- A right fraction whose denominator has `𝒟`-component an `eqToHom` and strongly cartesian
`𝒮`-component is, after that identification, one whose denominator has identity
`𝒟`-component. -/
private lemma exists_fraction_gen_aux {V V'' : 𝒟} {a c : 𝒮} {ψ : V ⟶ u.obj (p.obj a)}
    {ψ'' : V'' ⟶ u.obj (p.obj c)} {Y : Comma (𝟭 𝒟) (p ⋙ u)}
    {s : (Comma.mk V'' c ψ'' : Comma (𝟭 𝒟) (p ⋙ u)) ⟶ Comma.mk V a ψ}
    {f : (Comma.mk V'' c ψ'' : Comma (𝟭 𝒟) (p ⋙ u)) ⟶ Y}
    (hl : V'' = V) (hsl : s.left = eqToHom hl) (hsc : stronglyCartesianOver p s.right)
    {χ : (idBaseStronglyCartesian p u).Q.obj (Comma.mk V a ψ) ⟶
      (idBaseStronglyCartesian p u).Q.obj Y}
    (hfac : (idBaseStronglyCartesian p u).Q.map s ≫ χ =
      (idBaseStronglyCartesian p u).Q.map f) :
    ∃ (c' : 𝒮) (ψ' : V ⟶ u.obj (p.obj c')) (σ : c' ⟶ a) (_ : stronglyCartesianOver p σ)
      (hψ : ψ' ≫ (p ⋙ u).map σ = ψ)
      (g : (Comma.mk V c' ψ' : Comma (𝟭 𝒟) (p ⋙ u)) ⟶ Y),
      (idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u σ ψ' ψ hψ) ≫ χ =
        (idBaseStronglyCartesian p u).Q.map g := by
  subst hl
  obtain ⟨hψ, hse⟩ := exists_idBaseHomTo_eq_of_left_eq_id p u (by simpa using hsl)
  refine ⟨c, ψ'', s.right, hsc, hψ, f, ?_⟩
  rw [hse]
  exact hfac

/-- **Every morphism of `u_p 𝒮` is a fraction whose denominator has identity `𝒟`-component.**
The version of `Comma.exists_fraction_fiber` for a morphism between arbitrary objects: only the
denominator, not the numerator, is required to have identity `𝒟`-component. -/
theorem exists_fraction_gen
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    {X Y : Comma (𝟭 𝒟) (p ⋙ u)}
    (χ : (idBaseStronglyCartesian p u).Q.obj X ⟶ (idBaseStronglyCartesian p u).Q.obj Y) :
    ∃ (c : 𝒮) (ψ' : X.left ⟶ u.obj (p.obj c)) (σ : c ⟶ X.right)
      (_ : stronglyCartesianOver p σ) (hψ : ψ' ≫ (p ⋙ u).map σ = X.hom)
      (g : (Comma.mk X.left c ψ' : Comma (𝟭 𝒟) (p ⋙ u)) ⟶ Y),
      (idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u σ ψ' X.hom hψ) ≫ χ =
        (idBaseStronglyCartesian p u).Q.map g := by
  obtain ⟨ϕ, hϕs⟩ := exists_rightFraction_map_comp p u hu χ
  obtain ⟨⟨hl, hsl⟩, hsc⟩ := ϕ.hs
  exact exists_fraction_gen_aux p u (s := ϕ.s) (f := ϕ.f) hl hsl hsc hϕs

/-- **Two morphisms of a fibre of `u_p 𝒮` are fractions with a common denominator.** The version of
`Comma.exists_fraction_fiber` for two morphisms at once: one factorisation
`ψ = ψ' ∘ u(p σ)` through a strongly cartesian `σ : c ⟶ a` serves both, and the two numerators are
morphisms `α₁, α₂ : c ⟶ b` of `𝒮` compatible with `ω`. -/
theorem exists_common_fraction_fiber
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    {V : 𝒟} {a b : 𝒮} (ψ : V ⟶ u.obj (p.obj a)) (ω : V ⟶ u.obj (p.obj b))
    (n₁ n₂ : (idBaseStronglyCartesian p u).Q.obj (Comma.mk V a ψ) ⟶
      (idBaseStronglyCartesian p u).Q.obj (Comma.mk V b ω))
    (hn₁ : (pullbackProj p u).map n₁ = 𝟙 V) (hn₂ : (pullbackProj p u).map n₂ = 𝟙 V) :
    ∃ (c : 𝒮) (ψ' : V ⟶ u.obj (p.obj c)) (σ : c ⟶ a) (_ : stronglyCartesianOver p σ)
      (hψ : ψ' ≫ (p ⋙ u).map σ = ψ) (α₁ α₂ : c ⟶ b)
      (hω₁ : ψ' ≫ (p ⋙ u).map α₁ = ω) (hω₂ : ψ' ≫ (p ⋙ u).map α₂ = ω),
      (idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u σ ψ' ψ hψ) ≫ n₁ =
          (idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u α₁ ψ' ω hω₁) ∧
        (idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u σ ψ' ψ hψ) ≫ n₂ =
          (idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u α₂ ψ' ω hω₂) := by
  obtain ⟨c₁, ψ₁, σ₁, hσ₁, hψ₁, α₁, hω₁, e₁⟩ := exists_fraction_fiber p u hu ψ ω n₁ hn₁
  have hχ₂ : (pullbackProj p u).map
      ((idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u σ₁ ψ₁ ψ hψ₁) ≫ n₂) = 𝟙 V := by
    rw [Functor.map_comp, pullbackProj_map, idBaseHomTo_left, hn₂]
    exact Category.id_comp _
  obtain ⟨c₂, ψ₂, σ₂, hσ₂, hψ₂, α₂, hω₂, e₂⟩ :=
    exists_fraction_fiber p u hu ψ₁ ω
      ((idBaseStronglyCartesian p u).Q.map (idBaseHomTo p u σ₁ ψ₁ ψ hψ₁) ≫ n₂) hχ₂
  have hψσ : ψ₂ ≫ (p ⋙ u).map (σ₂ ≫ σ₁) = ψ := by
    rw [Functor.map_comp, ← Category.assoc, hψ₂, hψ₁]
  have hωα : ψ₂ ≫ (p ⋙ u).map (σ₂ ≫ α₁) = ω := by
    rw [Functor.map_comp, ← Category.assoc, hψ₂, hω₁]
  refine ⟨c₂, ψ₂, σ₂ ≫ σ₁, stronglyCartesianOver_comp p σ₂ σ₁ hσ₂ hσ₁, hψσ, σ₂ ≫ α₁, α₂,
    hωα, hω₂, ?_, ?_⟩
  · rw [← idBaseHomTo_comp p u σ₂ σ₁ ψ₂ ψ₁ ψ hψ₂ hψ₁, Functor.map_comp, Category.assoc, e₁,
      ← Functor.map_comp, idBaseHomTo_comp p u σ₂ α₁ ψ₂ ψ₁ ω hψ₂ hω₁]
  · rw [← idBaseHomTo_comp p u σ₂ σ₁ ψ₂ ψ₁ ψ hψ₂ hψ₁, Functor.map_comp, Category.assoc, e₂]

end

end Comma

end CategoryTheory

end
