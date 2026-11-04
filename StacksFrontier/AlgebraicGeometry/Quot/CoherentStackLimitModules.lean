module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitDescentEq

/-!
# Stacks 07V7 for a system of base changes `X ×_Y T_j`, on the base changes themselves

In Situation 08KB let `T_j` be a cofiltered system of test schemes over `Y` with a cone `T`, such
that the system of base changes `X_j = X ×_Y T_j` and its cone `X_T = X ×_Y T` satisfy the
hypotheses of Stacks 07V7
(`AlgebraicGeometry.Space.finitePresentationModule_isColimit_of_isLimit`). Stacks 07V7 is stated
for the stage spaces `stageAlgebraicSpace` of a system of presheaves; this file states its three
clauses for the base changes `X_{T_j}` of Stacks 08KB and the induced morphisms of base changes,
which is the form the descent of objects and of morphisms of `Coh_{X/Y}` in the proof of
Stacks 08KD consumes. It also records the form of the fullness clause for isomorphisms: an
isomorphism between inverse images on `X_T` is the restriction of an isomorphism at some stage.

## Main results

* `AlgebraicGeometry.Space.moduleHomRestrict_regroup`: restriction along `g` of a morphism on an
  inverse image along `p ≫ κ` is the restriction of the corresponding morphism on the iterated
  inverse image along `p` of the inverse images along `κ`.
* `AlgebraicGeometry.Space.CoherentSituation.finitePresentationModule_isColimit_baseChange`:
  Stacks 07V7, its three clauses, for the base changes `X_{T_j}`.
* `AlgebraicGeometry.Space.CoherentSituation.exists_stage_iso_of_cone`: an isomorphism of
  inverse images of finitely presented modules to `X_T` is the restriction of an isomorphism at a
  later stage.

## Implementation notes

The stage spaces of Stacks 07V7 for the system of base changes are *definitionally*, but not
syntactically, the base changes `X_{T_j}`, and elaborating a morphism of modules across that
definitional equality does not finish. The proof therefore never compares modules on the two
spaces directly: it passes between them only through explicit identity morphisms of algebraic
spaces built with `CategoryTheory.ObjectProperty.homMk`, which are isomorphisms, and through
inverse images along them; see also the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackLimitDescentEq.lean`.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 08KD](https://stacks.math.columbia.edu/tag/08KD)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent (pullbackComparison pullbackComparison_trans_hom
  pullbackComparison_trans_inv)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Restriction commutes with regrouping an iterated inverse image.** For `κ : Z' ⟶ Z`, a
morphism `y` between the inverse images along `p` of the inverse images along `κ` of two modules
on `Z`, read as a morphism between their inverse images along `p ≫ κ`, restricts along `g` to the
reading of the restriction of `y` along `g`. -/
theorem moduleHomRestrict_regroup {Z Z' P Q : AlgebraicSpaces B S hS} (κ : Z' ⟶ Z)
    (g : Q ⟶ P) (p : P ⟶ Z') (r : Q ⟶ Z') (h : g ≫ p = r)
    {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (y : (modulePullback B S hS p).obj ((modulePullback B S hS κ).obj M) ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS κ).obj N))
    (h' : g ≫ p ≫ κ = r ≫ κ) :
    moduleHomRestrict M N g (p ≫ κ) (r ≫ κ) h'
        ((pullbackComparison B S hS p κ (p ≫ κ) rfl M).hom ≫ y ≫
          (pullbackComparison B S hS p κ (p ≫ κ) rfl N).inv) =
      (pullbackComparison B S hS r κ (r ≫ κ) rfl M).hom ≫
        moduleHomRestrict ((modulePullback B S hS κ).obj M) ((modulePullback B S hS κ).obj N)
          g p r h y ≫
        (pullbackComparison B S hS r κ (r ≫ κ) rfl N).inv := by
  subst h
  have t₁ := pullbackComparison_trans_hom B S hS g p κ (p ≫ κ) rfl (g ≫ p) rfl ((g ≫ p) ≫ κ)
    h' rfl M
  have t₂ := pullbackComparison_trans_inv B S hS g p κ (p ≫ κ) rfl (g ≫ p) rfl ((g ≫ p) ≫ κ)
    h' rfl N
  simp only [moduleHomRestrict, Functor.map_comp, Category.assoc]
  rw [reassoc_of% t₁, t₂]

/-- Restricting an identity gives an identity. -/
theorem moduleHomRestrict_id {Z P Q : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS Z.1 Z.2)
    (g : Q ⟶ P) (p : P ⟶ Z) (q : Q ⟶ Z) (h : g ≫ p = q) :
    moduleHomRestrict M M g p q h (𝟙 _) = 𝟙 _ := by
  simp [moduleHomRestrict]

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

section StageModules

variable {J : Type u} [Category.{u} J] (F : J ⥤ SchemesOver D.Y) (cT : Cone F)

/-- The projections of the base changes along a cone of test schemes are compatible with the
transition morphisms. -/
theorem relativeMap_cone_comp {j k : J} (e : k ⟶ j) :
    D.relativeMap (cT.π.app k) ≫ D.relativeMap (F.map e) = D.relativeMap (cT.π.app j) :=
  (baseChangeMap_comp D.f _ _).symm.trans (congrArg (baseChangeMap D.f) (cT.w e))

/-- The transition morphisms of the base changes along a system of test schemes compose. -/
theorem relativeMap_map_comp {j k l : J} (f : l ⟶ k) (e : k ⟶ j) :
    D.relativeMap (F.map f) ≫ D.relativeMap (F.map e) = D.relativeMap (F.map (f ≫ e)) := by
  rw [F.map_comp]
  exact (baseChangeMap_comp D.f _ _).symm

variable (hZ : B.Contains (⊤_ Scheme.{u})) [IsCofiltered J]
  (hAff : ∀ {j k : J} (e : j ⟶ k), IsAffineHom B S hS ((testBaseChangeSystem D.f F).map e))
  (hQc : ∀ j, IsQuasiCompactSpace B S hS ((testBaseChangeSystem D.f F).obj j))
  (hQs : ∀ j, IsAbsolutelyQuasiSeparated B S hS hZ ((testBaseChangeSystem D.f F).obj j))
  (hc : IsLimit ((baseChangeOver D.f ⋙ Over.forget D.X ⋙ ObjectProperty.ι _).mapCone cT))
  (hL : SiteContainsBaseChangeLimits B S hS (testBaseChangeSystem D.f F))

include hZ hAff hQc hQs hc hL in
/-- **Stacks 07V7 for the base changes `X_{T_j} = X ×_Y T_j`.** Let `T_j` be a cofiltered system
of test schemes over `Y` with a cone `T` whose system of base changes satisfies the hypotheses of
Stacks 07V7. Inverse image along the morphisms `X_T ⟶ X_{T_j}` of base changes is

1. faithful in the colimit sense,
2. full in the colimit sense, through the restriction of morphisms of inverse images, and
3. essentially surjective in the colimit sense

on finitely presented modules. -/
theorem finitePresentationModule_isColimit_baseChange :
    (∀ (j : J) (M N : Modules.{u, u} B S hS (D.space (F.obj j)).1 (D.space (F.obj j)).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite → ∀ φ ψ : M ⟶ N,
        (modulePullback B S hS (D.relativeMap (cT.π.app j))).map φ =
          (modulePullback B S hS (D.relativeMap (cT.π.app j))).map ψ →
        ∃ (k : J) (e : k ⟶ j), (modulePullback B S hS (D.relativeMap (F.map e))).map φ =
          (modulePullback B S hS (D.relativeMap (F.map e))).map ψ) ∧
    (∀ (j : J) (M N : Modules.{u, u} B S hS (D.space (F.obj j)).1 (D.space (F.obj j)).2),
      M.IsFinitePresentationOnSite → N.IsFinitePresentationOnSite →
      ∀ χ : (modulePullback B S hS (D.relativeMap (cT.π.app j))).obj M ⟶
          (modulePullback B S hS (D.relativeMap (cT.π.app j))).obj N,
        ∃ (k : J) (e : k ⟶ j) (ψ : (modulePullback B S hS (D.relativeMap (F.map e))).obj M ⟶
            (modulePullback B S hS (D.relativeMap (F.map e))).obj N),
          moduleHomRestrict M N (D.relativeMap (cT.π.app k)) (D.relativeMap (F.map e))
            (D.relativeMap (cT.π.app j)) (D.relativeMap_cone_comp F cT e) ψ = χ) ∧
    (∀ P : Modules.{u, u} B S hS (D.space cT.pt).1 (D.space cT.pt).2,
      P.IsFinitePresentationOnSite →
        ∃ (k : J) (Q : Modules.{u, u} B S hS (D.space (F.obj k)).1 (D.space (F.obj k)).2),
          Q.IsFinitePresentationOnSite ∧
            Nonempty (P ≅ (modulePullback B S hS (D.relativeMap (cT.π.app k))).obj Q)) := by
  let G := testBaseChangeSystem D.f F
  have hD : ∀ j, IsAlgebraicSpace B S hS (G.obj j) := fun j => (D.space (F.obj j)).2
  let cX := (baseChangeOver D.f ⋙ Over.forget D.X ⋙ ObjectProperty.ι _).mapCone cT
  have hX : IsAlgebraicSpace B S hS cX.pt := (D.space cT.pt).2
  obtain ⟨h₁, h₂, h₃⟩ :=
    finitePresentationModule_isColimit_of_isLimit B S hS hZ G hD cX hX hAff hQc hQs hc hL
  -- the identifications of the stage spaces of Stacks 07V7 with the base changes
  let κ : ∀ j, stageAlgebraicSpace B S hS G hD j ⟶ D.space (F.obj j) :=
    fun j => ObjectProperty.homMk (𝟙 _)
  let ι : ∀ j, D.space (F.obj j) ⟶ stageAlgebraicSpace B S hS G hD j :=
    fun j => ObjectProperty.homMk (𝟙 _)
  let κC : (⟨cX.pt, hX⟩ : AlgebraicSpaces B S hS) ⟶ D.space cT.pt := ObjectProperty.homMk (𝟙 _)
  let ιC : D.space cT.pt ⟶ (⟨cX.pt, hX⟩ : AlgebraicSpaces B S hS) := ObjectProperty.homMk (𝟙 _)
  have hκι : ∀ j, κ j ≫ ι j = 𝟙 _ := fun j => ObjectProperty.hom_ext _ (Category.comp_id _)
  have hικ : ∀ j, ι j ≫ κ j = 𝟙 _ := fun j => ObjectProperty.hom_ext _ (Category.comp_id _)
  have hκιC : κC ≫ ιC = 𝟙 _ := ObjectProperty.hom_ext _ (Category.comp_id _)
  have hικC : ιC ≫ κC = 𝟙 _ := ObjectProperty.hom_ext _ (Category.comp_id _)
  have hκi : ∀ j, IsIso (κ j) := fun j => ⟨ι j, hκι j, hικ j⟩
  have hκCi : IsIso κC := ⟨ιC, hκιC, hικC⟩
  have hcone : ∀ j, coneProjection B S hS G hD cX hX j ≫ κ j =
      κC ≫ D.relativeMap (cT.π.app j) := fun j =>
    ObjectProperty.hom_ext _ (by
      show cX.π.app j ≫ 𝟙 _ = 𝟙 _ ≫ (D.relativeMap (cT.π.app j)).hom
      rw [Category.comp_id, Category.id_comp]
      rfl)
  have htrans : ∀ {j k : J} (e : k ⟶ j),
      stageTransition B S hS G hD e ≫ κ j = κ k ≫ D.relativeMap (F.map e) :=
    fun {j k} e => ObjectProperty.hom_ext _ (by
      show G.map e ≫ 𝟙 _ = 𝟙 _ ≫ (D.relativeMap (F.map e)).hom
      rw [Category.comp_id, Category.id_comp]
      rfl)
  refine ⟨fun j M N hM hN φ ψ h => ?_, fun j M N hM hN χ => ?_, fun P hP => ?_⟩
  · -- faithfulness
    have hfaC := faithful_modulePullback_of_isIso κC
    have h' : (modulePullback B S hS (coneProjection B S hS G hD cX hX j)).map
          ((modulePullback B S hS (κ j)).map φ) =
        (modulePullback B S hS (coneProjection B S hS G hD cX hX j)).map
          ((modulePullback B S hS (κ j)).map ψ) := by
      apply map_map_eq_of_map_comp_eq B S hS
      rw [hcone j]
      exact map_comp_eq_of_map_map_eq B S hS _ _ (by rw [h])
    have hM' := isFinitePresentationOnSite_modulePullback B S hS (κ j) M hM
    have hN' := isFinitePresentationOnSite_modulePullback B S hS (κ j) N hN
    obtain ⟨k, e, hk⟩ := h₁ j _ _ hM' hN' _ _ h'
    refine ⟨k, e, ?_⟩
    have hk' := map_comp_eq_of_map_map_eq B S hS _ _ hk
    rw [htrans e] at hk'
    have hfa := faithful_modulePullback_of_isIso (κ k)
    exact (modulePullback B S hS (κ k)).map_injective (map_map_eq_of_map_comp_eq B S hS _ _ hk')
  · -- fullness
    have hκ : κC ≫ D.relativeMap (cT.π.app j) = coneProjection B S hS G hD cX hX j ≫ κ j :=
      (hcone j).symm
    let χ' := (pullbackComparison B S hS (coneProjection B S hS G hD cX hX j) (κ j)
        (coneProjection B S hS G hD cX hX j ≫ κ j) rfl M).inv ≫
      moduleHomRestrict M N κC (D.relativeMap (cT.π.app j))
        (coneProjection B S hS G hD cX hX j ≫ κ j) hκ χ ≫
      (pullbackComparison B S hS (coneProjection B S hS G hD cX hX j) (κ j)
        (coneProjection B S hS G hD cX hX j ≫ κ j) rfl N).hom
    have hM' := isFinitePresentationOnSite_modulePullback B S hS (κ j) M hM
    have hN' := isFinitePresentationOnSite_modulePullback B S hS (κ j) N hN
    obtain ⟨k, e, ψ', hψ'⟩ := h₂ j _ _ hM' hN' χ'
    have hι : ι k ≫ stageTransition B S hS G hD e ≫ κ j = D.relativeMap (F.map e) := by
      rw [htrans e, ← Category.assoc, hικ k, Category.id_comp]
    refine ⟨k, e, moduleHomRestrict M N (ι k) (stageTransition B S hS G hD e ≫ κ j)
      (D.relativeMap (F.map e)) hι
      ((pullbackComparison B S hS (stageTransition B S hS G hD e) (κ j)
          (stageTransition B S hS G hD e ≫ κ j) rfl M).hom ≫ ψ' ≫
        (pullbackComparison B S hS (stageTransition B S hS G hD e) (κ j)
          (stageTransition B S hS G hD e ≫ κ j) rfl N).inv), ?_⟩
    have hfaC := faithful_modulePullback_of_isIso κC
    apply moduleHomRestrict_injective κC (D.relativeMap (cT.π.app j))
      (coneProjection B S hS G hD cX hX j ≫ κ j) hκ
    rw [moduleHomRestrict_homRestrict, moduleHomRestrict_homRestrict]
    have hcp : (κC ≫ D.relativeMap (cT.π.app k)) ≫ ι k = coneProjection B S hS G hD cX hX k := by
      rw [← hcone k, Category.assoc, hκι k, Category.comp_id]
    rw [moduleHomRestrict_congr hcp,
      moduleHomRestrict_regroup (κ j) (coneProjection B S hS G hD cX hX k)
        (stageTransition B S hS G hD e) (coneProjection B S hS G hD cX hX j)
        (coneProjection_comp B S hS G hD cX hX e),
      hψ']
    simp only [χ', Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  · -- essential surjectivity
    obtain ⟨k, Q', hQ', ⟨α⟩⟩ := h₃ ((modulePullback B S hS κC).obj P)
      (isFinitePresentationOnSite_modulePullback B S hS κC P hP)
    have hπ : D.relativeMap (cT.π.app k) ≫ ι k = ιC ≫ coneProjection B S hS G hD cX hX k :=
      ObjectProperty.hom_ext _ (by
        show (D.relativeMap (cT.π.app k)).hom ≫ 𝟙 _ = 𝟙 _ ≫ cX.π.app k
        rw [Category.comp_id, Category.id_comp]
        rfl)
    exact ⟨k, (modulePullback B S hS (ι k)).obj Q',
      isFinitePresentationOnSite_modulePullback B S hS (ι k) Q' hQ',
      ⟨((modulePullbackIdIso B S hS (D.space cT.pt)).app P).symm ≪≫
        pullbackComparison B S hS ιC κC (𝟙 _) hικC P ≪≫
        (modulePullback B S hS ιC).mapIso α ≪≫
        (pullbackComparison B S hS ιC (coneProjection B S hS G hD cX hX k)
          (ιC ≫ coneProjection B S hS G hD cX hX k) rfl Q').symm ≪≫
        pullbackComparison B S hS (D.relativeMap (cT.π.app k)) (ι k)
          (ιC ≫ coneProjection B S hS G hD cX hX k) hπ Q'⟩⟩

include hZ hAff hQc hQs hc hL in
/-- **The fullness clause of Stacks 07V7 for isomorphisms.** An isomorphism between the inverse
images to `X_T` of two finitely presented modules on `X_{T_j}` is, at a later stage `T_k`, the
restriction of an isomorphism between the inverse images to `X_{T_k}`. -/
theorem exists_stage_iso_of_cone (j : J)
    (M N : Modules.{u, u} B S hS (D.space (F.obj j)).1 (D.space (F.obj j)).2)
    (hM : M.IsFinitePresentationOnSite) (hN : N.IsFinitePresentationOnSite)
    (χ : (modulePullback B S hS (D.relativeMap (cT.π.app j))).obj M ≅
      (modulePullback B S hS (D.relativeMap (cT.π.app j))).obj N) :
    ∃ (k : J) (e : k ⟶ j) (ψ : (modulePullback B S hS (D.relativeMap (F.map e))).obj M ≅
        (modulePullback B S hS (D.relativeMap (F.map e))).obj N),
      moduleHomRestrict M N (D.relativeMap (cT.π.app k)) (D.relativeMap (F.map e))
        (D.relativeMap (cT.π.app j)) (D.relativeMap_cone_comp F cT e) ψ.hom = χ.hom := by
  obtain ⟨h₁, h₂, -⟩ := D.finitePresentationModule_isColimit_baseChange F cT hZ hAff hQc hQs hc hL
  let R := fun {j k : J} (e : k ⟶ j) => D.relativeMap (F.map e)
  let π := fun j => D.relativeMap (cT.π.app j)
  obtain ⟨k₁, e₁, ψ₁, hψ₁⟩ := h₂ j M N hM hN χ.hom
  obtain ⟨k₂, e₂, ψ₂, hψ₂⟩ := h₂ j N M hN hM χ.inv
  obtain ⟨k₃, f₁, f₂, hf⟩ := IsCofiltered.cospan e₁ e₂
  let e₃ := f₁ ≫ e₁
  have hf₁ : R f₁ ≫ R e₁ = R e₃ := D.relativeMap_map_comp F f₁ e₁
  have hf₂ : R f₂ ≫ R e₂ = R e₃ := by
    rw [D.relativeMap_map_comp F f₂ e₂, ← hf]
  let ψ₁' := moduleHomRestrict M N (R f₁) (R e₁) (R e₃) hf₁ ψ₁
  let ψ₂' := moduleHomRestrict N M (R f₂) (R e₂) (R e₃) hf₂ ψ₂
  have hc₁ : moduleHomRestrict M N (π k₃) (R e₃) (π j) (D.relativeMap_cone_comp F cT e₃) ψ₁' =
      χ.hom := by
    rw [moduleHomRestrict_homRestrict,
      moduleHomRestrict_congr (D.relativeMap_cone_comp F cT f₁)]
    exact hψ₁
  have hc₂ : moduleHomRestrict N M (π k₃) (R e₃) (π j) (D.relativeMap_cone_comp F cT e₃) ψ₂' =
      χ.inv := by
    rw [moduleHomRestrict_homRestrict,
      moduleHomRestrict_congr (D.relativeMap_cone_comp F cT f₂)]
    exact hψ₂
  have hM₃ := isFinitePresentationOnSite_modulePullback B S hS (R e₃) M hM
  have hN₃ := isFinitePresentationOnSite_modulePullback B S hS (R e₃) N hN
  -- the two composites are identities at the cone point
  have hid₁ : (modulePullback B S hS (π k₃)).map (ψ₁' ≫ ψ₂') =
      (modulePullback B S hS (π k₃)).map (𝟙 _) := by
    rw [← moduleHomRestrict_eq_iff (π k₃) (R e₃) (π j) (D.relativeMap_cone_comp F cT e₃),
      moduleHomRestrict_comp, hc₁, hc₂, Iso.hom_inv_id, moduleHomRestrict_id]
  have hid₂ : (modulePullback B S hS (π k₃)).map (ψ₂' ≫ ψ₁') =
      (modulePullback B S hS (π k₃)).map (𝟙 _) := by
    rw [← moduleHomRestrict_eq_iff (π k₃) (R e₃) (π j) (D.relativeMap_cone_comp F cT e₃),
      moduleHomRestrict_comp, hc₁, hc₂, Iso.inv_hom_id, moduleHomRestrict_id]
  obtain ⟨k₄, e₄, h₄⟩ := h₁ k₃ _ _ hM₃ hM₃ _ _ hid₁
  obtain ⟨k₅, e₅, h₅⟩ := h₁ k₃ _ _ hN₃ hN₃ _ _ hid₂
  obtain ⟨k₆, g₄, g₅, hg⟩ := IsCofiltered.cospan e₄ e₅
  let e₆ := g₄ ≫ e₄
  have hR₄ : R e₆ = R g₄ ≫ R e₄ := (D.relativeMap_map_comp F g₄ e₄).symm
  have hR₅ : R e₆ = R g₅ ≫ R e₅ := by
    rw [D.relativeMap_map_comp F g₅ e₅]
    exact congrArg (fun t => D.relativeMap (F.map t)) hg
  have h₆₁ : (modulePullback B S hS (R e₆)).map (ψ₁' ≫ ψ₂') =
      (modulePullback B S hS (R e₆)).map (𝟙 _) := by
    rw [hR₄]
    exact map_comp_eq_of_map_map_eq B S hS _ _ (by rw [h₄])
  have h₆₂ : (modulePullback B S hS (R e₆)).map (ψ₂' ≫ ψ₁') =
      (modulePullback B S hS (R e₆)).map (𝟙 _) := by
    rw [hR₅]
    exact map_comp_eq_of_map_map_eq B S hS _ _ (by rw [h₅])
  have hR₆ : R e₆ ≫ R e₃ = R (e₆ ≫ e₃) := D.relativeMap_map_comp F e₆ e₃
  refine ⟨k₆, e₆ ≫ e₃,
    { hom := moduleHomRestrict M N (R e₆) (R e₃) (R (e₆ ≫ e₃)) hR₆ ψ₁'
      inv := moduleHomRestrict N M (R e₆) (R e₃) (R (e₆ ≫ e₃)) hR₆ ψ₂'
      hom_inv_id := by
        rw [← moduleHomRestrict_comp, ← moduleHomRestrict_id M (R e₆) (R e₃) (R (e₆ ≫ e₃)) hR₆,
          moduleHomRestrict_eq_iff]
        exact h₆₁
      inv_hom_id := by
        rw [← moduleHomRestrict_comp, ← moduleHomRestrict_id N (R e₆) (R e₃) (R (e₆ ≫ e₃)) hR₆,
          moduleHomRestrict_eq_iff]
        exact h₆₂ }, ?_⟩
  show moduleHomRestrict M N (π k₆) (R (e₆ ≫ e₃)) (π j) _
    (moduleHomRestrict M N (R e₆) (R e₃) (R (e₆ ≫ e₃)) hR₆ ψ₁') = χ.hom
  rw [moduleHomRestrict_homRestrict,
    moduleHomRestrict_congr (D.relativeMap_cone_comp F cT e₆)]
  exact hc₁

end StageModules

end CoherentSituation

end AlgebraicGeometry.Space

end
