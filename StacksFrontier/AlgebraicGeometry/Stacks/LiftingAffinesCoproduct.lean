module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesSingleDescentGlue
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackCoproductDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# Disjoint unions in the spaces-étale site, and smooth lifts over them (Stacks 0CJU)

A family of representable objects `N l` of the spaces-étale site of `W` whose representing objects
have a coproduct `V` in the big fppf site of `S` has a coproduct in the spaces-étale site: the
algebraic space represented by `V`, étale over `W`.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.sigmaRep`: the coproduct object.
* `AlgebraicGeometry.Space.SpacesEtale.sigmaRepι`: its inclusions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {W : AlgebraicSpaces B S hS}
  {L : Type u} (N : L → SpacesEtale B S hS W) (nN : L → BigFppfOver B S hS)
  (iN : ∀ l, yoneda.obj (nN l) ≅ (N l).obj.left.obj) {V : BigFppfOver B S hS}
  (c : ∀ l, nN l ⟶ V) (hV : IsColimit (Cofan.mk V c))

include hV

/-- The structure morphisms of the summands assemble into one out of the coproduct. -/
theorem exists_sigmaRepStr :
    ∃ v : yoneda.obj V ⟶ W.obj, ∀ l, yoneda.map (c l) ≫ v = (iN l).hom ≫ (N l).obj.hom.hom :=
  exists_hom_yoneda_of_isColimit_cofan
    (F := fun _ => (⟨W.obj, W.property.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)))
    (P := ⟨W.obj, W.property.isSheaf⟩) (fun _ => 𝟙 _) (fun l => (iN l).hom ≫ (N l).obj.hom.hom) hV

/-- The structure morphism of the coproduct to `W`. -/
def sigmaRepStr : yoneda.obj V ⟶ W.obj := (exists_sigmaRepStr N nN iN c hV).choose

/-- The structure morphism of the coproduct restricts on each summand to the structure morphism
of that summand. -/
theorem sigmaRepStr_fac (l : L) :
    yoneda.map (c l) ≫ sigmaRepStr N nN iN c hV = (iN l).hom ≫ (N l).obj.hom.hom :=
  (exists_sigmaRepStr N nN iN c hV).choose_spec l

/-- Every point of the vertex of a coproduct cofan is the image of a point of some summand. -/
private theorem exists_toScheme_map_cofan_eq (z : (BigFppfOver.toScheme B S hS).obj V) :
    ∃ l, ∃ y, (BigFppfOver.toScheme B S hS).map (c l) y = z :=
  Set.iUnion_eq_univ_iff.1 (iUnion_range_toScheme_map_cofan hV) z

/-- The inclusions of the summands form an étale covering. -/
theorem isEtaleCovering_yoneda_map :
    Space.IsEtaleCovering B S hS (fun l => yoneda.obj (nN l)) (fun l => yoneda.map (c l)) := by
  refine ⟨isAlgebraicSpace_yoneda B S hS V, fun l => isAlgebraicSpace_yoneda B S hS _,
    fun l => ?_, ?_⟩
  · have := isOpenImmersion_toScheme_map_cofan hV l
    exact isEtale_of_presheafEtaleProperty B S hS _
      ((presheaf_yoneda_map_etale_iff B S hS (c l)).2 inferInstance)
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨l, y, hy⟩ := Space.exists_pointsMap_yonedaMap_eq_of_jointly_surjective B S hS c
      (exists_toScheme_map_cofan_eq nN c hV) x
    exact ⟨l, y, hy⟩

/-- **The coproduct of the summands in the spaces-étale site.** -/
def sigmaRep : SpacesEtale B S hS W :=
  ⟨Over.mk (ObjectProperty.homMk (sigmaRepStr N nN iN c hV) :
    schemeSpace V ⟶ W), by
    let : MorphismProperty.IsLocalAtSource
        (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsEtale B S hS f.hom)
        (Topology.etale.precoverage.{u, u} B S hS) :=
      isEtale_isLocalAtSource_etale.{u, u} B S hS
    have hR : Presieve.ofArrows (fun l => schemeSpace (nN l))
        (fun l => (schemeSpaceMap (c l) :
          schemeSpace (nN l) ⟶
            schemeSpace V)) ∈
        Topology.etale.precoverage.{u, u} B S hS (schemeSpace V) :=
      ⟨L, _, _, rfl, isAlgebraicSpace_yoneda B S hS V, fun l => isAlgebraicSpace_yoneda B S hS _,
        isEtaleCovering_yoneda_map nN c hV⟩
    refine MorphismProperty.IsLocalAtSource.of_forall_comp
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsEtale B S hS f.hom) hR ?_
    rintro T g ⟨l⟩
    change IsEtale B S hS (yoneda.map (c l) ≫ sigmaRepStr N nN iN c hV)
    rw [sigmaRepStr_fac]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _) (N l).property⟩

/-- The inclusion of a summand into the coproduct, in the spaces-étale site. -/
def sigmaRepι (l : L) : N l ⟶ sigmaRep N nN iN c hV :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk ((iN l).inv ≫ yoneda.map (c l)))
    (ObjectProperty.hom_ext _ (by
      change ((iN l).inv ≫ yoneda.map (c l)) ≫ sigmaRepStr N nN iN c hV = (N l).obj.hom.hom
      rw [Category.assoc, sigmaRepStr_fac, Iso.inv_hom_id_assoc])))

/-- The underlying morphism of sheaves of the inclusion `sigmaRepι l` is `(iN l).inv` followed by
the image under the Yoneda embedding of `c l`. -/
theorem sigmaRepι_left_hom (l : L) :
    (sigmaRepι N nN iN c hV l).hom.left.hom = (iN l).inv ≫ yoneda.map (c l) := rfl

omit iN in
/-- The inclusions of the summands are injective on points. -/
theorem mono_cofan_inj (l : L) : Mono (c l) := by
  have := isOpenImmersion_toScheme_map_cofan hV l
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map (IsOpenImmersion.mono _)

omit iN in
/-- Points of two distinct summands with the same image lie over an empty scheme. -/
theorem isEmpty_of_comp_eq_cofan {k l : L} (hkl : k ≠ l) {T : BigFppfOver B S hS}
    (a : T ⟶ nN k) (b : T ⟶ nN l) (h : a ≫ c k = b ≫ c l) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj T) :=
  ⟨fun t => ne_toScheme_map_cofan hV hkl ((BigFppfOver.toScheme B S hS).map a t)
    ((BigFppfOver.toScheme B S hS).map b t) (by
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, h, Functor.map_comp,
        Scheme.Hom.comp_apply])⟩

omit iN in
/-- **Morphisms out of the represented coproduct are determined by their restrictions** to the
summands, which form an fpqc covering (Stacks 04P2, uniqueness). -/
theorem yoneda_hom_ext_of_cofan {Z : AlgebraicSpaces B S hS} {h h' : yoneda.obj V ⟶ Z.obj}
    (hh : ∀ l, yoneda.map (c l) ≫ h = yoneda.map (c l) ≫ h') : h = h' := by
  have hf := Space.isFpqcCovering_of_isEtaleCovering B S hS _ _ (isEtaleCovering_yoneda_map nN c hV)
  obtain ⟨H, -, huniq⟩ := Space.existsUnique_desc_of_fpqcCovering B S hS
    (X := fun l => schemeSpace (nN l))
    (Y := schemeSpace V)
    (fun l => (schemeSpaceMap (c l) :
      schemeSpace (nN l) ⟶ schemeSpace V))
    hf Z (fun l => ObjectProperty.homMk (yoneda.map (c l) ≫ h))
    (fun k l => ObjectProperty.hom_ext _ (by
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h) pullback.condition).trans
        (Category.assoc _ _ _))))
  have e₁ := huniq (ObjectProperty.homMk h) (fun l => rfl)
  have e₂ := huniq (ObjectProperty.homMk h') (fun l => ObjectProperty.hom_ext _ (hh l).symm)
  exact congrArg (fun k => k.hom) (e₁.trans e₂.symm)

/-- **The coproduct is a coproduct in the spaces-étale site**: the morphisms out of the
summands assemble into one out of the coproduct. -/
theorem exists_sigmaRep_desc (T : SpacesEtale B S hS W) (g : ∀ l, N l ⟶ T) :
    ∃ d : sigmaRep N nN iN c hV ⟶ T, ∀ l, sigmaRepι N nN iN c hV l ≫ d = g l := by
  obtain ⟨v, hv⟩ := exists_hom_yoneda_of_isColimit_cofan
    (F := fun l => (⟨(N l).obj.left.obj, (N l).obj.left.property.isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)))
    (P := ⟨T.obj.left.obj, T.obj.left.property.isSheaf⟩) (fun l => ⟨(g l).hom.left.hom⟩)
    (fun l => (iN l).hom) hV
  have hw : v ≫ T.obj.hom.hom = sigmaRepStr N nN iN c hV := by
    refine yoneda_hom_ext_of_cofan nN c hV fun l => ?_
    rw [← Category.assoc, hv l, sigmaRepStr_fac, Category.assoc]
    exact congrArg ((iN l).hom ≫ ·) (congrArg (fun k => k.hom) (Over.w (g l).hom))
  refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk v)
    (ObjectProperty.hom_ext _ hw)), fun l => ?_⟩
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
  change ((iN l).inv ≫ yoneda.map (c l)) ≫ v = (g l).hom.left.hom
  rw [Category.assoc, hv l, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Space.SpacesEtale

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Coproducts of the site are disjoint and stable under base change along a coproduct of
morphisms**: for coproducts `VN = ∐ nN l`, `VA = ∐ nA l` and morphisms `il l : nN l ⟶ nA l`
assembled into `incV : VN ⟶ VA`, the square of `nN l ⊆ VN` over `nA l ⊆ VA` is cartesian. -/
theorem BigFppfOver.isPullback_cofan_desc {L : Type u} {nN nA : L → BigFppfOver B S hS}
    {VN VA : BigFppfOver B S hS} {cN : ∀ l, nN l ⟶ VN} {cA : ∀ l, nA l ⟶ VA}
    (hVN : IsColimit (Cofan.mk VN cN)) (hVA : IsColimit (Cofan.mk VA cA))
    (il : ∀ l, nN l ⟶ nA l) (incV : VN ⟶ VA) (hinc : ∀ l, cN l ≫ incV = il l ≫ cA l) (l : L) :
    IsPullback (il l) (cN l) (cA l) incV := by
  have := isOpenImmersion_toScheme_map_cofan hVN l
  have hmA := Space.SpacesEtale.mono_cofan_inj nA cA hVA l
  have hmN := Space.SpacesEtale.mono_cofan_inj nN cN hVN l
  have hlift : ∀ (T : BigFppfOver B S hS) (a : T ⟶ nA l) (b : T ⟶ VN)
      (_ : a ≫ cA l = b ≫ incV), ∃ t : T ⟶ nN l, t ≫ cN l = b := by
    intro T a b hab
    have hrange : Set.range ((BigFppfOver.toScheme B S hS).map b) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map (cN l)) := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨m, y, hy⟩ := Space.SpacesEtale.exists_toScheme_map_cofan_eq nN cN hVN
        ((BigFppfOver.toScheme B S hS).map b x)
      by_cases hml : m = l
      · subst hml; exact ⟨y, hy⟩
      · exfalso
        refine ne_toScheme_map_cofan hVA hml ((BigFppfOver.toScheme B S hS).map (il m) y)
          ((BigFppfOver.toScheme B S hS).map a x) ?_
        have e₁ := congrArg (fun f => (BigFppfOver.toScheme B S hS).map f y) (hinc m)
        have e₂ := congrArg (fun f => (BigFppfOver.toScheme B S hS).map f x) hab
        simp only [Functor.map_comp, Scheme.Hom.comp_apply] at e₁ e₂
        rw [← e₁, hy, e₂]
    obtain ⟨ψ, hψ⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
      (IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map (cN l))
        ((BigFppfOver.toScheme B S hS).map b) hrange) (by
        have hw : B.inclusion.map (nN l).hom = (BigFppfOver.toScheme B S hS).map (cN l) ≫
            B.inclusion.map VN.hom := by
          rw [← Over.w (cN l), Functor.map_comp]; rfl
        rw [hw, ← Category.assoc, IsOpenImmersion.lift_fac]
        change B.inclusion.map b.left ≫ B.inclusion.map VN.hom = _
        rw [← Functor.map_comp, Over.w b])
    exact ⟨ψ, (BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, hψ, IsOpenImmersion.lift_fac])⟩
  choose lift hlift' using hlift
  refine IsPullback.of_isLimit' ⟨(hinc l).symm⟩ (PullbackCone.IsLimit.mk (hinc l).symm
    (fun s => lift _ s.fst s.snd s.condition) (fun s => ?_) (fun s => hlift' _ _ _ _)
    (fun s m h₁ h₂ => ?_))
  · rw [← cancel_mono (cA l), Category.assoc, ← hinc l, ← Category.assoc, hlift', s.condition]
  · rw [← cancel_mono (cN l), h₂, hlift']

end AlgebraicGeometry
