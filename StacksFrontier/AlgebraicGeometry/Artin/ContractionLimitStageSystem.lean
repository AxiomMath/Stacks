module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitTowerRingCompletion
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageRingsLimit

/-!
# The descended system of a stage witness

A stage witness `q : V'_{k₀} ⟶ V_{k₀}` of an element over the limit `V = lim V_k` is base changed
to every later stage `k ⟶ k₀`: `V'_k = V_k ×_{V_{k₀}} V'_{k₀}`. With an ideal `I₀ ⊆ Γ(V_{k₀}, 𝒪)`
cutting out `Z_{k₀}` and its extensions `I_k = I₀ Γ(V_k, 𝒪)`, this file constructs the systems of
rings `k ↦ A_k^∧ = Γ(V_k, 𝒪)^∧_{I_k}` and
`k ↦ C_k^∧ = lim_n Γ(V'_k ×_{V_k} Spec (A_k / I_k^{n+1}), 𝒪)` over the stages, the natural
transformation `α : A_k^∧ ⟶ C_k^∧`, and the maps to the rings `A^∧` and `C^∧` of the limit.

## Main definitions

* `AlgebraicGeometry.Artin.LimitStages.stageSpace`, `stageHom`: the system `k ↦ V'_k`.
* `AlgebraicGeometry.Artin.LimitStages.completionSystem`, `towerSystem`, `alphaSystem`: the
  functors `k ↦ A_k^∧`, `k ↦ C_k^∧` on `(Over k₀)ᵒᵖ` and `α`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.LimitStages

open Space FormalSpace FormalDictionary FormalRing ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance]
  AlgebraicGeometry.Artin.FormalDictionary.instTopologicalSpaceAdicCompletion

/-- The scheme underlying a locally Noetherian object is locally Noetherian. -/
instance isLocallyNoetherian_obj (X : LocallyNoetherianOver B S hS) :
    _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj X.obj) :=
  X.property

/-- **The fibres of a proper algebraic space over an affine object are quasi-compact.** -/
theorem isQuasiCompactSpace_fibreSpace (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    {X : AlgebraicSpaces B S hS} (g : X.1 ⟶ yoneda.obj V) (hg : Space.IsProper B S hS g) (n : ℕ) :
    IsQuasiCompactSpace B S hS (fibreSpace V I (spaceHom V g) n).1 :=
  isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS V inferInstance
    (fibreSpace V I (spaceHom V g) n).2 (isAlgebraicSpace_yoneda B S hS V) _
    (universallyClosed_comp B S hS X.2 (isAlgebraicSpace_yoneda B S hS V) _ _
      (universallyClosed_of_isClosedImmersion B S hS (fibreSpace V I (spaceHom V g) n).2 X.2 _
        (fibreThickening V I (spaceHom V g) n).2.2) hg.2.2)

/-- **The zero locus of an extended ideal is the inverse image of the zero locus.** -/
theorem mem_preimage_iff_mem_zeroLocus_map {V V' : BigFppfOver B S hS} (v : V' ⟶ V)
    {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    (hZI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    (x : Space.points B S hS (yoneda.obj V')) :
    x ∈ Space.pointsMap B S hS _ (yoneda.map v) ⁻¹' Z ↔ Space.pointsToScheme B S hS V' x ∈
      ((BigFppfOver.toScheme B S hS).obj V').zeroLocus
        ((I.map ((BigFppfOver.toScheme B S hS).map v).appTop.hom :
          Ideal Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)) :
          Set Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)) := by
  rw [Set.mem_preimage, hZI, pointsToScheme_pointsMap, ← Set.mem_preimage,
    preimage_zeroLocus_ideal_map]

/-- The ring map `ULift R ⟶ ULift R'` of a ring map. -/
def uliftRingHom {R R' : Type u} [CommRing R] [CommRing R'] (f : R →+* R') :
    ULift.{u + 1} R →+* ULift.{u + 1} R' :=
  ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)

/-- `uliftRingHom f` acts as `f` on the underlying elements. -/
@[simp]
theorem uliftRingHom_down {R R' : Type u} [CommRing R] [CommRing R'] (f : R →+* R')
    (x : ULift.{u + 1} R) : (uliftRingHom f x).down = f x.down :=
  rfl

/-- The map of adic completions induced by `f` depends only on `f`, not on the proof that `f` maps
`J` into `J'`. -/
theorem completionRingHom_congr {A A' : Type u} [CommRing A] [CommRing A'] {f f' : A →+* A'}
    {J : Ideal A} {J' : Ideal A'} (e : f = f') (h : J.map f ≤ J') (h' : J.map f' ≤ J') :
    completionRingHom f h = completionRingHom f' h' := by
  subst e
  rfl

/-- The identity of `A` induces the identity of the `J`-adic completion of `A`. -/
theorem completionRingHom_id {A : Type u} [CommRing A] {J : Ideal A}
    (h : J.map (RingHom.id A) ≤ J) :
    completionRingHom (RingHom.id A) h = RingHom.id _ :=
  RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_completionRingHom]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
    rw [← hy, Ideal.quotientMap_mk]
    exact hy

/-- A ring map equal to the identity induces the identity of the lifted adic completion. -/
theorem uliftRingHom_completionRingHom_id {A : Type u} [CommRing A] {J : Ideal A} {f : A →+* A}
    (hf : f = RingHom.id A) (h : J.map f ≤ J) :
    uliftRingHom (completionRingHom f h) = RingHom.id _ := by
  subst hf
  rw [completionRingHom_id]
  rfl

/-- If `f'' = g ∘ f`, the map of lifted adic completions induced by `f''` is the composite of those
induced by `f` and `g`. -/
theorem uliftRingHom_completionRingHom_comp {A A' A'' : Type u} [CommRing A] [CommRing A']
    [CommRing A''] {J : Ideal A} {J' : Ideal A'} {J'' : Ideal A''} {f : A →+* A'} {g : A' →+* A''}
    {f'' : A →+* A''} (e : f'' = g.comp f) (hf : J.map f ≤ J') (hg : J'.map g ≤ J'')
    (h'' : J.map f'' ≤ J'') :
    uliftRingHom (completionRingHom f'' h'') =
      (uliftRingHom (completionRingHom g hg)).comp (uliftRingHom (completionRingHom f hf)) := by
  subst e
  rw [← completionRingHom_comp f hf g hg h'']
  rfl

variable {c : ContractionSituation B S hS} {I : Type u} [Category.{u} I]
  {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D} {ξ : Triple c κ.pt.obj}
  {w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat} {k₀ : I} (W : StageWitness c κ ξ w k₀)

/-- For a morphism `f : k' ⟶ k` over `k₀`, the composite `V_{k'} ⟶ V_k ⟶ V_{k₀}` is the structure
map of `k'`. -/
theorem map_left_hom_comp {k k' : Over k₀} (f : k' ⟶ k) :
    (D.map f.left).hom ≫ (D.map k.hom).hom = (D.map k'.hom).hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, ← D.map_comp, Over.w f]

/-- The ring maps on global sections of `f` and `g` compose to that of `f ≫ g`. -/
private theorem appTop_map_comp_of_comp_eq {V₁ V₂ V₃ : BigFppfOver B S hS} {f : V₁ ⟶ V₂}
    {g : V₂ ⟶ V₃} {h : V₁ ⟶ V₃} (e : f ≫ g = h) :
    ((BigFppfOver.toScheme B S hS).map f).appTop.hom.comp
        ((BigFppfOver.toScheme B S hS).map g).appTop.hom =
      ((BigFppfOver.toScheme B S hS).map h).appTop.hom := by
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ← Functor.map_comp, e]

/-- **The space `V'_k = V_k ×_{V_{k₀}} V'_{k₀}`.** -/
abbrev stageSpace (k : Over k₀) : AlgebraicSpaces B S hS :=
  ⟨pullback (yoneda.map (D.map k.hom).hom) W.q, (W.baseChange k.hom).isAlgebraicSpace_Y⟩

/-- `q_k : V'_k ⟶ V_k`. -/
abbrev stageQ (k : Over k₀) : (stageSpace W k).1 ⟶ yoneda.obj (D.obj k.left).obj :=
  pullback.fst _ _

/-- `q_k : V'_k ⟶ V_k` is proper. -/
theorem isProper_stageQ (k : Over k₀) : Space.IsProper B S hS (stageQ W k) :=
  (W.baseChange k.hom).isProper_q

/-- The transition `V'_{k'} ⟶ V'_k` of the system. -/
def stageHom {k k' : Over k₀} (f : k' ⟶ k) : (stageSpace W k').1 ⟶ (stageSpace W k).1 :=
  pullback.lift (pullback.fst _ _ ≫ yoneda.map (D.map f.left).hom) (pullback.snd _ _) (by
    rw [Category.assoc, ← Functor.map_comp, map_left_hom_comp, pullback.condition])

/-- The transition `V'_{k'} ⟶ V'_k` lies over the transition `V_{k'} ⟶ V_k`. -/
theorem stageHom_q {k k' : Over k₀} (f : k' ⟶ k) :
    stageHom W f ≫ stageQ W k = stageQ W k' ≫ yoneda.map (D.map f.left).hom :=
  pullback.lift_fst _ _ _

/-- The transition `V'_{k'} ⟶ V'_k` commutes with the projections to `V'_{k₀}`. -/
theorem stageHom_snd {k k' : Over k₀} (f : k' ⟶ k) :
    stageHom W f ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The transition along the identity of `k` is the identity of `V'_k`. -/
theorem stageHom_id (k : Over k₀) : stageHom W (𝟙 k) = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [stageHom, pullback.lift_fst, Category.id_comp, Over.id_left, D.map_id,
      ObjectProperty.FullSubcategory.id_hom, CategoryTheory.Functor.map_id, Category.comp_id]
  · rw [stageHom_snd, Category.id_comp]

/-- The transitions of the system `k ↦ V'_k` compose. -/
theorem stageHom_comp {k k' k'' : Over k₀} (f : k' ⟶ k) (f' : k'' ⟶ k') :
    stageHom W f' ≫ stageHom W f = stageHom W (f' ≫ f) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, stageHom_q, ← Category.assoc, stageHom_q, Category.assoc,
      ← Functor.map_comp, stageHom_q, Over.comp_left, D.map_comp,
      ObjectProperty.FullSubcategory.comp_hom]
  · rw [Category.assoc, stageHom_snd, stageHom_snd, stageHom_snd]

/-- `a_k : V' ⟶ V'_k`. -/
def stageA (k : Over k₀) : w.V' ⟶ (stageSpace W k).1 :=
  pullback.lift (w.p ≫ yoneda.map (κ.π.app k.left).hom) W.a (by
    rw [Category.assoc, ← Functor.map_comp, cone_π_hom_comp]
    exact W.isPullback_a.w)

/-- `a_k : V' ⟶ V'_k` lies over the projection `V ⟶ V_k`. -/
theorem stageA_q (k : Over k₀) :
    stageA W k ≫ stageQ W k = w.p ≫ yoneda.map (κ.π.app k.left).hom :=
  pullback.lift_fst _ _ _

/-- The composite of `a_k : V' ⟶ V'_k` with the projection to `V'_{k₀}` is the witness map. -/
theorem stageA_snd (k : Over k₀) : stageA W k ≫ pullback.snd _ _ = W.a :=
  pullback.lift_snd _ _ _

/-- The maps `a_k : V' ⟶ V'_k` are compatible with the transitions of the system. -/
theorem stageA_stageHom {k k' : Over k₀} (f : k' ⟶ k) :
    stageA W k' ≫ stageHom W f = stageA W k := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, stageHom_q, ← Category.assoc, stageA_q, Category.assoc,
      ← Functor.map_comp, stageA_q, cone_π_hom_comp]
  · rw [Category.assoc, stageHom_snd, stageA_snd, stageA_snd]

variable {W} (I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤))

/-- **The ideal `I_k = I₀ Γ(V_k, 𝒪)`.** -/
def stageIdeal (k : Over k₀) : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤) :=
  I₀.map ((BigFppfOver.toScheme B S hS).map (D.map k.hom).hom).appTop.hom

/-- For `f : k' ⟶ k` over `k₀`, the extension of `I_k` to `Γ(V_{k'}, 𝒪)` is `I_{k'}`. -/
theorem stageIdeal_map {k k' : Over k₀} (f : k' ⟶ k) :
    (stageIdeal I₀ k).map ((BigFppfOver.toScheme B S hS).map (D.map f.left).hom).appTop.hom =
      stageIdeal I₀ k' := by
  rw [stageIdeal, stageIdeal, Ideal.map_map, appTop_map_comp_of_comp_eq (map_left_hom_comp f)]

/-- For `f : k' ⟶ k` over `k₀`, the extension of `I_k` to `Γ(V_{k'}, 𝒪)` lies in `I_{k'}`. -/
theorem stageIdeal_map_le {k k' : Over k₀} (f : k' ⟶ k) :
    (stageIdeal I₀ k).map ((BigFppfOver.toScheme B S hS).map (D.map f.left).hom).appTop.hom ≤
      stageIdeal I₀ k' :=
  (stageIdeal_map I₀ f).le

/-- **The ideal `I = I₀ Γ(V, 𝒪)` of the limit.** -/
def limitIdeal : Ideal Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤) :=
  I₀.map ((BigFppfOver.toScheme B S hS).map (κ.π.app k₀).hom).appTop.hom

/-- The extension of `I_k` to `Γ(V, 𝒪)` is the ideal `I` of the limit. -/
theorem stageIdeal_map_limit (k : Over k₀) :
    (stageIdeal I₀ k).map ((BigFppfOver.toScheme B S hS).map (κ.π.app k.left).hom).appTop.hom =
      limitIdeal (κ := κ) I₀ := by
  rw [stageIdeal, limitIdeal, Ideal.map_map, appTop_map_comp_of_comp_eq (cone_π_hom_comp k.hom)]

variable {I₀} (hZI₀ : ∀ x, x ∈ W.Z ↔ Space.pointsToScheme B S hS (D.obj k₀).obj x ∈
  ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj).zeroLocus
    (I₀ : Set Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)))

include hZI₀ in
/-- If `I₀` cuts out `Z_{k₀}`, then `I_k` cuts out the closed subset `Z_k` of the base change to
`V_k`. -/
theorem stage_hZI (k : Over k₀) (x : Space.points B S hS (yoneda.obj (D.obj k.left).obj)) :
    x ∈ (W.baseChange k.hom).Z ↔ Space.pointsToScheme B S hS (D.obj k.left).obj x ∈
      ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj).zeroLocus
        (stageIdeal I₀ k : Set Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) :=
  mem_preimage_iff_mem_zeroLocus_map (D.map k.hom).hom hZI₀ x

include hZI₀ in
/-- If `I₀` cuts out `Z_{k₀}`, then the ideal `I` of the limit cuts out `Z ⊆ |V|`. -/
theorem limit_hZI (x : Space.points B S hS (yoneda.obj κ.pt.obj)) :
    x ∈ ξ.Z ↔ Space.pointsToScheme B S hS κ.pt.obj x ∈
      ((BigFppfOver.toScheme B S hS).obj κ.pt.obj).zeroLocus
        (limitIdeal (κ := κ) I₀ : Set Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)) := by
  rw [← W.preimage_Z]
  exact mem_preimage_iff_mem_zeroLocus_map (κ.π.app k₀).hom hZI₀ x

section Rings

variable (W) [hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj)]

omit hD in
/-- The ring map `Γ(V_k, 𝒪) ⟶ Γ(V_k, 𝒪)` of the identity of `k` is the identity. -/
theorem appTop_map_id_eq (k : Over k₀) :
    ((BigFppfOver.toScheme B S hS).map (D.map (𝟙 k : k ⟶ k).left).hom).appTop.hom =
      RingHom.id _ := by
  rw [Over.id_left, D.map_id, ObjectProperty.FullSubcategory.id_hom, CategoryTheory.Functor.map_id,
    Scheme.Hom.id_appTop, CommRingCat.hom_id]

omit hD in
/-- The ring maps on global sections of the transitions `V_{k''} ⟶ V_{k'} ⟶ V_k` compose. -/
theorem appTop_map_comp_eq {k k' k'' : Over k₀} (f : k' ⟶ k) (f' : k'' ⟶ k') :
    ((BigFppfOver.toScheme B S hS).map (D.map (f' ≫ f).left).hom).appTop.hom =
      ((BigFppfOver.toScheme B S hS).map (D.map f'.left).hom).appTop.hom.comp
        ((BigFppfOver.toScheme B S hS).map (D.map f.left).hom).appTop.hom := by
  exact (appTop_map_comp_of_comp_eq (by simp)).symm

variable (I₀) in
/-- **The system `k ↦ A_k^∧ = Γ(V_k, 𝒪)^∧_{I_k}`** (lifted to the universe of the tower rings). -/
def completionSystem : (Over k₀)ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj k := CommRingCat.of (ULift.{u + 1} (AdicCompletion (stageIdeal I₀ k.unop)
    Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.unop.left).obj, ⊤)))
  map f := CommRingCat.ofHom (uliftRingHom (completionRingHom
    ((BigFppfOver.toScheme B S hS).map (D.map f.unop.left).hom).appTop.hom
    (stageIdeal_map_le I₀ f.unop)))
  map_id k := CommRingCat.hom_ext (uliftRingHom_completionRingHom_id (appTop_map_id_eq k.unop) _)
  map_comp f g := CommRingCat.hom_ext (uliftRingHom_completionRingHom_comp
    (appTop_map_comp_eq f.unop g.unop) _ _ _)

variable (I₀) in
/-- **The system `k ↦ C_k^∧ = lim_n Γ(V'_k ×_{V_k} Spec (A_k / I_k^{n+1}), 𝒪)`.** -/
def towerSystem : (Over k₀)ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj k := CommRingCat.of (towerRing (stageIdeal I₀ k.unop) (stageQ W k.unop))
  map f := CommRingCat.ofHom (towerRingMap (D.map f.unop.left).hom (stageIdeal_map_le I₀ f.unop)
    (stageQ W _) (stageQ W _) (stageHom W f.unop) (stageHom_q W f.unop))
  map_id k := CommRingCat.hom_ext (towerRingMap_id _ _ _ _ _ (stageHom_id W k.unop))
  map_comp f g := CommRingCat.hom_ext (towerRingMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (stageHom_comp W f.unop g.unop)).symm

end Rings

section Alpha

variable (W) [hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj)]
  [hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj)]
  {I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)}
  (hZI₀ : ∀ x, x ∈ W.Z ↔ Space.pointsToScheme B S hS (D.obj k₀).obj x ∈
    ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj).zeroLocus
      (I₀ : Set Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)))

/-- The algebraic space `V'` of the witness over the limit. -/
abbrev limitSpace (w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat) : AlgebraicSpaces B S hS :=
  ⟨w.V', w.isAlgebraicSpace_V'⟩

/-- `p : V' ⟶ V`. -/
abbrev limitP (w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat) :
    (limitSpace w).1 ⟶ yoneda.obj κ.pt.obj :=
  w.p

/-- `V ⟶ V_k`. -/
abbrev limitMap (κ : Cone D) (k : Over k₀) : κ.pt.obj ⟶ (D.obj k.left).obj :=
  (κ.π.app k.left).hom

/-- **`α_k : A_k^∧ ⟶ C_k^∧`** at a stage. -/
def stageAlpha (k : Over k₀) :
    AdicCompletion (stageIdeal I₀ k) Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤) →+*
      towerRing (stageIdeal I₀ k) (stageQ W k) :=
  alpha (stageQ W k) (stage_hZI hZI₀ k)
    (isQuasiCompactSpace_fibreSpace _ _ _ (isProper_stageQ W k))

/-- **The natural transformation `α : A_k^∧ ⟶ C_k^∧`.** -/
def alphaSystem : completionSystem (D := D) I₀ ⟶ towerSystem W I₀ where
  app k := CommRingCat.ofHom ((stageAlpha W hZI₀ k.unop).comp ULift.ringEquiv.toRingHom)
  naturality X Y f := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    have h := congrArg (fun φ => φ x.down) (towerRingMap_comp_alpha (stageQ W X.unop)
      (stage_hZI hZI₀ X.unop) (isQuasiCompactSpace_fibreSpace _ _ _ (isProper_stageQ W X.unop))
      (D.map f.unop.left).hom (stageIdeal_map_le I₀ f.unop) (stageQ W Y.unop) (stageHom W f.unop)
      (stageHom_q W f.unop) (stage_hZI hZI₀ Y.unop)
      (isQuasiCompactSpace_fibreSpace _ _ _ (isProper_stageQ W Y.unop)))
    exact h.symm

/-- **`α : A^∧ ⟶ C^∧`** for the limit. -/
def limitAlpha :
    AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤) →+*
      towerRing (limitIdeal (κ := κ) I₀) (limitP w) :=
  alpha (limitP w) (limit_hZI hZI₀)
    (isQuasiCompactSpace_fibreSpace _ _ _ w.isProper_p)

variable (I₀) in
/-- The ring `A^∧` of the limit. -/
abbrev limitCompletion : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (AdicCompletion (limitIdeal (κ := κ) I₀)
    Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)))

variable (I₀) in
/-- The ring `C^∧` of the limit. -/
abbrev limitTower : CommRingCat.{u + 1} :=
  CommRingCat.of (towerRing (limitIdeal (κ := κ) I₀) (limitP w))

/-- `α` of the limit, as a morphism of `CommRingCat`. -/
def limitAlphaHom : limitCompletion (κ := κ) I₀ ⟶ limitTower (w := w) I₀ :=
  CommRingCat.ofHom ((limitAlpha W hZI₀).comp ULift.ringEquiv.toRingHom)

variable (I₀) in
/-- `A_k^∧ ⟶ A^∧`. -/
def completionToLimit (k : Over k₀) :
    (completionSystem (D := D) I₀).obj (op k) ⟶ limitCompletion (κ := κ) I₀ :=
  CommRingCat.ofHom (uliftRingHom (completionRingHom
    ((BigFppfOver.toScheme B S hS).map (limitMap κ k)).appTop.hom
    (stageIdeal_map_limit I₀ k).le))

variable (I₀) in
/-- `C_k^∧ ⟶ C^∧`. -/
def towerToLimit (k : Over k₀) : (towerSystem W I₀).obj (op k) ⟶ limitTower (w := w) I₀ :=
  CommRingCat.ofHom (towerRingMap (limitMap κ k)
    (stageIdeal_map_limit I₀ k).le (stageQ W k) (limitP w) (stageA W k) (stageA_q W k))

omit hD hpt in
/-- The maps `A_k^∧ ⟶ A^∧` are compatible with the transitions of `k ↦ A_k^∧`. -/
theorem completionSystem_map_comp_completionToLimit {k k' : Over k₀} (f : k' ⟶ k) :
    (completionSystem (D := D) I₀).map f.op ≫ completionToLimit (κ := κ) I₀ k' =
      completionToLimit I₀ k :=
  CommRingCat.hom_ext (uliftRingHom_completionRingHom_comp (appTop_map_comp_of_comp_eq
    (cone_π_hom_comp f.left)).symm _ _ _).symm

/-- The maps `C_k^∧ ⟶ C^∧` are compatible with the transitions `C_k^∧ ⟶ C_{k'}^∧`. -/
theorem towerRingMap_stageHom_comp_toLimit {k k' : Over k₀} (f : k' ⟶ k) :
    (towerRingMap (limitMap κ k') (stageIdeal_map_limit I₀ k').le (stageQ W k') (limitP w)
        (stageA W k') (stageA_q W k')).comp
      (towerRingMap (D.map f.left).hom (stageIdeal_map_le I₀ f) (stageQ W k) (stageQ W k')
        (stageHom W f) (stageHom_q W f)) =
      towerRingMap (limitMap κ k) (stageIdeal_map_limit I₀ k).le (stageQ W k) (limitP w)
        (stageA W k) (stageA_q W k) :=
  towerRingMap_comp (stageQ W k) (stageQ W k') (limitP w)
    (D.map f.left).hom (limitMap κ k') (limitMap κ k) (stageIdeal_map_le I₀ f)
    (stageIdeal_map_limit I₀ k').le (stageIdeal_map_limit I₀ k).le (stageHom W f) (stageA W k')
    (stageA W k) (stageHom_q W f) (stageA_q W k') (stageA_q W k) (stageA_stageHom W f)

omit hpt in
/-- The transition `C_k^∧ ⟶ C_{k'}^∧` of `towerSystem` is the map of tower rings induced by
`V'_{k'} ⟶ V'_k` over `V_{k'} ⟶ V_k`. -/
theorem towerSystem_map {k k' : Over k₀} (f : k' ⟶ k) :
    (towerSystem W I₀).map f.op = CommRingCat.ofHom (towerRingMap (D.map f.left).hom
      (stageIdeal_map_le I₀ f) (stageQ W k) (stageQ W k') (stageHom W f) (stageHom_q W f)) :=
  rfl

/-- The maps `α_k : A_k^∧ ⟶ C_k^∧` and `α : A^∧ ⟶ C^∧` commute with the maps `A_k^∧ ⟶ A^∧` and
`C_k^∧ ⟶ C^∧`. -/
theorem limitAlpha_comp_completionRingHom (k : Over k₀) :
    (limitAlpha W hZI₀).comp (completionRingHom
      ((BigFppfOver.toScheme B S hS).map (limitMap κ k)).appTop.hom
        (stageIdeal_map_limit I₀ k).le) =
      (towerRingMap (limitMap κ k) (stageIdeal_map_limit I₀ k).le (stageQ W k) (limitP w)
        (stageA W k) (stageA_q W k)).comp (stageAlpha W hZI₀ k) :=
  (towerRingMap_comp_alpha (stageQ W k) (stage_hZI hZI₀ k)
    (isQuasiCompactSpace_fibreSpace _ _ _ (isProper_stageQ W k)) (limitMap κ k)
    (stageIdeal_map_limit I₀ k).le (limitP w) (stageA W k)
    (stageA_q W k) (limit_hZI hZI₀) (isQuasiCompactSpace_fibreSpace _ _ _ w.isProper_p)).symm

/-- Elementwise form of `limitAlpha_comp_completionRingHom`. -/
theorem limitAlpha_completionRingHom_apply (k : Over k₀) (x) :
    limitAlpha W hZI₀ (completionRingHom
      ((BigFppfOver.toScheme B S hS).map (limitMap κ k)).appTop.hom
      (stageIdeal_map_limit I₀ k).le x) =
      towerRingMap (limitMap κ k) (stageIdeal_map_limit I₀ k).le (stageQ W k) (limitP w)
        (stageA W k) (stageA_q W k) (stageAlpha W hZI₀ k x) := by
  rw [← RingHom.comp_apply, limitAlpha_comp_completionRingHom, RingHom.comp_apply]

/-- For `x ∈ A_k^∧`, applying `α` to the image of `x` in `A^∧` agrees with mapping `α_k x` to
`C^∧`. -/
theorem limitAlpha_completionToLimit (k : Over k₀) (x : (completionSystem (D := D) I₀).obj (op k)) :
    (limitAlphaHom W hZI₀).hom ((completionToLimit I₀ k).hom x) =
      (towerToLimit W I₀ k).hom (((alphaSystem W hZI₀).app (op k)).hom x) :=
  congrArg (fun φ => φ x.down) (limitAlpha_comp_completionRingHom W hZI₀ k)

omit hpt in
/-- The component of `alphaSystem` at `k` acts as `α_k` on the underlying elements. -/
theorem alphaSystem_app_apply (k : Over k₀) (x : (completionSystem (D := D) I₀).obj (op k)) :
    ((alphaSystem W hZI₀).app (op k)).hom x = stageAlpha W hZI₀ k x.down :=
  rfl

omit hD in
/-- `limitAlphaHom` acts as `limitAlpha` on the underlying elements. -/
theorem limitAlphaHom_apply (y : limitCompletion (κ := κ) I₀) :
    (limitAlphaHom W hZI₀).hom y = limitAlpha W hZI₀ y.down :=
  rfl

variable (I₀) in
omit hD hpt in
/-- `A_k^∧ ⟶ A^∧` acts on underlying elements as the map of adic completions induced by
`Γ(V_k, 𝒪) ⟶ Γ(V, 𝒪)`. -/
theorem completionToLimit_apply_down (k : Over k₀) (x : (completionSystem (D := D) I₀).obj (op k)) :
    ((completionToLimit (κ := κ) I₀ k).hom x).down = completionRingHom
      ((BigFppfOver.toScheme B S hS).map (limitMap κ k)).appTop.hom (stageIdeal_map_limit I₀ k).le
        x.down :=
  rfl

variable (I₀) in
omit hD in
/-- The transition `A_k^∧ ⟶ A_{k'}^∧` acts on underlying elements as the map of adic completions
induced by `Γ(V_k, 𝒪) ⟶ Γ(V_{k'}, 𝒪)`. -/
theorem completionSystem_map_apply_down {k k' : Over k₀} (f : k' ⟶ k)
    (x : (completionSystem (D := D) I₀).obj (op k)) :
    (((completionSystem (D := D) I₀).map f.op).hom x).down = completionRingHom
      ((BigFppfOver.toScheme B S hS).map (D.map f.left).hom).appTop.hom (stageIdeal_map_le I₀ f)
        x.down :=
  rfl

end Alpha

end AlgebraicGeometry.Artin.LimitStages

end
