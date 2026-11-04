module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitDirectImageDegreeZeroColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleAffineSectionsSetColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitSetDescent

/-!
# Stacks 0EYM in degree zero for sheaves of sets, in adjoint form

Let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of schemes over a nonempty directed
set with affine transition morphisms, `g_i : X_i ⟶ S_i` a morphism of the first into the second
with every `g_i` quasi-compact and quasi-separated, `X = lim X_i`, `S = lim S_i`, and
`g : X ⟶ S` the limit morphism. Let `(F_i)` be a system of sheaves of **sets** on the `X_i`, and
`x_i : F_i ⟶ f_{i, *}𝓕` maps to the direct images of a sheaf of sets `𝓕` on `X`, compatible with
the transitions.

This file proves the degree-zero case of [Stacks, Tag 0EYM] for sheaves of sets,
`g_* 𝓕 = colim h_i^{-1} g_{i, *}F_i`, in its adjoint form, from the description of the sections of
`𝓕` over the base change to `X` of a quasi-compact quasi-separated étale `X_{i₀}`-scheme as the
filtered colimit of the sections of the `F_i`
(`Stacks.EtaleCohomology.LimitSetDirectImage.IsSectionsColimitAt`, which is [Stacks, Tag 09YQ] in
degree zero over that object): for every sheaf of sets `𝒢` on `S` and every family
`σ_i : g_{i, *}F_i ⟶ h_{i, *}𝒢` compatible with the transition maps of the direct images there is a
unique `χ : g_* 𝓕 ⟶ 𝒢` with `h_{i, *}χ ∘ π_i = σ_i`, `π_i` being the transposed cocone maps
`Stacks.EtaleCohomology.LimitDirectImage.projectionTranspose`.

The proof is the source's, and the one
`Stacks.EtaleCohomology.LimitHigherDirectImage.existsUnique_directImage_desc` runs for abelian
sheaves: a map out of `g_{i₀, *}f_{i₀, *}𝓕` is a compatible family of maps out of the
`g_{i₀, *}f_{i i₀, *}F_i`, by the colimit description of its sections over affine objects
(`Stacks.EtaleCohomology.existsUnique_desc_of_affineSetSections`), and the resulting maps at the
levels glue by the colimit half of [Stacks, Tag 0EYN] on `S`
(`Stacks.EtaleCohomology.AffineLimitCohomology.existsUnique_setDirectImageDescent`).

The same argument with `g` the identity of the system gives the universal property of
`𝓕 = colim f_i^{-1}F_i` itself from the colimit description of the sections over affine objects
(`Stacks.EtaleCohomology.LimitSetDirectImage.existsUnique_desc_of_sectionsColimit`).

## Main definitions

* `Stacks.EtaleCohomology.LimitSetDirectImage.IsSectionsColimitAt` — the sections of `𝓕` over the
  base change to `X` of an étale `X_{i₀}`-scheme are the filtered colimit of those of the `F_i`.
* `Stacks.EtaleCohomology.LimitSetDirectImage.IsSetDirectImageFamily` — the compatibility of a
  family of maps out of the direct images `g_{i, *}F_i`.

## Main results

* `Stacks.EtaleCohomology.LimitSetDirectImage.existsUnique_setDirectImage_desc` — **the
  degree-zero colimit assertion for sheaves of sets, in adjoint form.**
* `Stacks.EtaleCohomology.LimitSetDirectImage.existsUnique_desc_of_sectionsColimit` — the colimit
  presentation `𝓕 = colim f_i^{-1}F_i`, in adjoint form, from the colimit description of the
  sections over affine objects.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open Stacks.EtaleCohomology.SmallEtaleLimitCohomology Stacks.EtaleCohomology.LimitDirectImage

universe v u

namespace Stacks.EtaleCohomology.LimitSetDirectImage

section Sections

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] {D : Iᵒᵖ ⥤ Scheme.{max u v}}
  {c : Cone D} (F : EtaleSheafSystem D (Type (max u v + 1)))
  {𝓕 : Sheaf (smallEtaleTopology c.pt) (Type (max u v + 1))}
  (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj 𝓕)

/-- **The sections of `𝓕` over the base change to the limit of an étale `X_{i₀}`-scheme `W` are
the filtered colimit of the sections of the `F_i` over its base changes to the `X_i`, `i ≥ i₀`**:
every section is the image of a section of some `F_i` under the shifted leg
`Stacks.EtaleCohomology.LimitDirectImage.shiftLeg`, and two sections of `F_i` with the same image
have the same image under a shifted transition map
`Stacks.EtaleCohomology.LimitDirectImage.shiftTransition`. For `W` quasi-compact and
quasi-separated and `𝓕 = colim f_i^{-1}F_i` this is [Stacks, Tag 09YQ] in degree zero over `W`. -/
def IsSectionsColimitAt (i₀ : I) (W : (D.obj (op i₀)).Etale) : Prop :=
  (∀ s : ((smallEtalePushforward (c.π.app (op i₀)) (Type (max u v + 1))).obj 𝓕).obj.obj (op W),
      ∃ (k : (GeIndex i₀)ᵒᵖ)
        (t : ((systemPushforward D (Type (max u v + 1)) (geIndexToBase i₀ k)).obj
          (F.obj ((geIndexOpFunctor i₀).obj k))).obj.obj (op W)),
        (shiftLeg (c := c) x (geIndexToBase i₀ k)).hom.app (op W) t = s) ∧
    ∀ (k : (GeIndex i₀)ᵒᵖ)
      (t t' : ((systemPushforward D (Type (max u v + 1)) (geIndexToBase i₀ k)).obj
        (F.obj ((geIndexOpFunctor i₀).obj k))).obj.obj (op W)),
      (shiftLeg (c := c) x (geIndexToBase i₀ k)).hom.app (op W) t =
          (shiftLeg (c := c) x (geIndexToBase i₀ k)).hom.app (op W) t' →
        ∃ (k' : (GeIndex i₀)ᵒᵖ) (b : k' ⟶ k),
          (shiftTransition (Type (max u v + 1)) F.mapTranspose ((geIndexOpFunctor i₀).map b)
              (geIndexToBase i₀ k) (geIndexToBase i₀ k') (Subsingleton.elim _ _)).hom.app
              (op W) t =
            (shiftTransition (Type (max u v + 1)) F.mapTranspose ((geIndexOpFunctor i₀).map b)
              (geIndexToBase i₀ k) (geIndexToBase i₀ k') (Subsingleton.elim _ _)).hom.app
              (op W) t'

end Sections

section Level

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {DX DS : Iᵒᵖ ⥤ Scheme.{max u v}} (γ : DX ⟶ DS) {cX : Cone DX}
  (cS : Cone DS) (hcS : IsLimit cS)
  [∀ i : Iᵒᵖ, QuasiCompact (γ.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (γ.app i)]
  (F : EtaleSheafSystem DX (Type (max u v + 1)))
  {𝓕 : Sheaf (smallEtaleTopology cX.pt) (Type (max u v + 1))}
  (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (cX.π.app i) (Type (max u v + 1))).obj 𝓕)
  {𝒢 : Sheaf (smallEtaleTopology cS.pt) (Type (max u v + 1))}

/-- The compatibility of a family of maps out of the direct images `g_{i, *}F_i` of a system of
sheaves of sets with their transposed transition maps
`Stacks.EtaleCohomology.LimitDirectImage.directTransition`. -/
def IsSetDirectImageFamily
    (σ : ∀ i : Iᵒᵖ, directImage γ (Type (max u v + 1)) F i ⟶
      (smallEtalePushforward (cS.π.app i) (Type (max u v + 1))).obj 𝒢) : Prop :=
  ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j),
    σ j = directTransition γ (Type (max u v + 1)) F a ≫
      (systemPushforward DS (Type (max u v + 1)) a).map (σ i) ≫
        (coneProjectionComp (Type (max u v + 1)) cS a).hom.app 𝒢

/-- The transposed cocone maps `π_i : g_{i, *}F_i ⟶ h_{i, *}g_* 𝓕`. -/
abbrev setLegProjection :=
  projectionTranspose γ (Type (max u v + 1)) cX cS hcS F x

/-- The transposed cocone maps form an `IsSetDirectImageFamily`. -/
theorem isSetDirectImageFamily_setLegProjection
    (hx : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      x j = F.mapTranspose a ≫ (systemPushforward DX (Type (max u v + 1)) a).map (x i) ≫
        (coneProjectionComp (Type (max u v + 1)) cX a).hom.app 𝓕) :
    IsSetDirectImageFamily γ cS F (setLegProjection γ cS hcS F x) :=
  fun _ _ a => projectionTranspose_compat γ (Type (max u v + 1)) cX cS hcS F x hx a

variable {σ : ∀ i : Iᵒᵖ, directImage γ (Type (max u v + 1)) F i ⟶
  (smallEtalePushforward (cS.π.app i) (Type (max u v + 1))).obj 𝒢}

/-- **The factorisation at a level**, through the filtered colimit of sections over the base
changes of affine étale `S_{i₀}`-schemes to `X_{i₀}`. -/
theorem existsUnique_setLevelMap
    (hx : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      x j = F.mapTranspose a ≫ (systemPushforward DX (Type (max u v + 1)) a).map (x i) ≫
        (coneProjectionComp (Type (max u v + 1)) cX a).hom.app 𝓕)
    (hsec : ∀ (i₀ : I) (V : (DS.obj (op i₀)).AffineEtale),
      IsSectionsColimitAt F x i₀
        ((smallEtaleBaseChange (γ.app (op i₀))).obj ((AffineEtale.Spec _).obj V)))
    (hσ : IsSetDirectImageFamily γ cS F σ) (i₀ : I) :
    ∃! σ' : (smallEtalePushforward (γ.app (op i₀)) (Type (max u v + 1))).obj
        ((smallEtalePushforward (cX.π.app (op i₀)) (Type (max u v + 1))).obj 𝓕) ⟶
        (smallEtalePushforward (cS.π.app (op i₀)) (Type (max u v + 1))).obj 𝒢,
      ∀ k : (GeIndex i₀)ᵒᵖ,
        (smallEtalePushforward (γ.app (op i₀)) (Type (max u v + 1))).map
            (shiftLeg (c := cX) x (geIndexToBase i₀ k)) ≫ σ' =
          (transitionSquareIso γ (Type (max u v + 1)) (geIndexToBase i₀ k)).hom.app
              (F.obj ((geIndexOpFunctor i₀).obj k)) ≫
            shiftLeg (c := cS) σ (geIndexToBase i₀ k) := by
  refine existsUnique_desc_of_affineSetSections (X := DS.obj (op i₀)) (J := (GeIndex i₀)ᵒᵖ)
    (fun {j k} b => (smallEtalePushforward (γ.app (op i₀)) (Type (max u v + 1))).map
      (shiftTransition (Type (max u v + 1)) F.mapTranspose ((geIndexOpFunctor i₀).map b)
        (geIndexToBase i₀ j) (geIndexToBase i₀ k) (Subsingleton.elim _ _)))
    _ ?_ ?_ ?_ ?_ _ ?_
  · intro j j'
    obtain ⟨m, h₁, h₂⟩ := directed_of (· ≤ ·) j.unop.1 j'.unop.1
    exact ⟨op ⟨m, j.unop.2.trans h₁⟩, (homOfLE (show j.unop ≤ ⟨m, j.unop.2.trans h₁⟩ from h₁)).op,
      (homOfLE (show j'.unop ≤ ⟨m, j.unop.2.trans h₁⟩ from h₂)).op, trivial⟩
  · intro j k b
    refine ((smallEtalePushforward (γ.app (op i₀)) (Type (max u v + 1))).map_comp _
      _).symm.trans (congrArg (smallEtalePushforward (γ.app (op i₀))
        (Type (max u v + 1))).map ?_)
    exact shiftTransition_comp_shiftLeg F.mapTranspose x hx
      _ _ _ _
  · intro V s
    exact (hsec i₀ V).1 s
  · intro V k t t' ht
    exact (hsec i₀ V).2 k t t' ht
  · intro j k b
    have h₁ := shiftTransition_transitionSquareIso γ (Type (max u v + 1)) F
      ((geIndexOpFunctor i₀).map b) (geIndexToBase i₀ j) (geIndexToBase i₀ k)
      (Subsingleton.elim _ _)
    have h₂ := shiftTransition_comp_shiftLeg (c := cS)
      (directTransition γ (Type (max u v + 1)) F) σ (fun a => hσ a)
      ((geIndexOpFunctor i₀).map b) (geIndexToBase i₀ j) (geIndexToBase i₀ k)
      (Subsingleton.elim _ _)
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ shiftLeg (c := cS) σ
      (geIndexToBase i₀ k)) h₁).trans ((Category.assoc _ _ _).trans (congrArg
        ((transitionSquareIso γ (Type (max u v + 1)) (geIndexToBase i₀ j)).hom.app
          (F.obj ((geIndexOpFunctor i₀).obj j)) ≫ ·) h₂)))

/-- **The factorisation at a level, read on `S`.** For a compatible family `σ_i` there is a unique
`ρ : h_{i₀, *}g_* 𝓕 ⟶ h_{i₀, *}𝒢` such that, for every transition `a : i ⟶ i₀`, the shifted
transposed cocone map from `i` followed by `ρ` is the shifted `σ_i`. -/
theorem existsUnique_setLevelDescent
    (hx : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      x j = F.mapTranspose a ≫ (systemPushforward DX (Type (max u v + 1)) a).map (x i) ≫
        (coneProjectionComp (Type (max u v + 1)) cX a).hom.app 𝓕)
    (hsec : ∀ (i₀ : I) (V : (DS.obj (op i₀)).AffineEtale),
      IsSectionsColimitAt F x i₀
        ((smallEtaleBaseChange (γ.app (op i₀))).obj ((AffineEtale.Spec _).obj V)))
    (hσ : IsSetDirectImageFamily γ cS F σ) (i₀ : I) :
    ∃! ρ : (smallEtalePushforward (cS.π.app (op i₀)) (Type (max u v + 1))).obj
        ((smallEtalePushforward (LimitHigherDirectImage.limitMorphism γ cX cS hcS)
          (Type (max u v + 1))).obj 𝓕) ⟶
        (smallEtalePushforward (cS.π.app (op i₀)) (Type (max u v + 1))).obj 𝒢,
      ∀ {m : Iᵒᵖ} (a : m ⟶ op i₀),
        shiftLeg (c := cS) (setLegProjection γ cS hcS F x) a ≫ ρ = shiftLeg (c := cS) σ a := by
  obtain ⟨σ', hσ', hu⟩ := existsUnique_setLevelMap γ cS F x hx hsec hσ i₀
  have key : ∀ k : (GeIndex i₀)ᵒᵖ,
      (smallEtalePushforward (γ.app (op i₀)) (Type (max u v + 1))).map
          (shiftLeg (c := cX) x (geIndexToBase i₀ k)) ≫
        (projectionSquareIso γ (Type (max u v + 1)) cX cS hcS (op i₀)).hom.app 𝓕 =
      (transitionSquareIso γ (Type (max u v + 1)) (geIndexToBase i₀ k)).hom.app
          (F.obj ((geIndexOpFunctor i₀).obj k)) ≫
        shiftLeg (c := cS) (setLegProjection γ cS hcS F x) (geIndexToBase i₀ k) :=
    fun k => shiftLeg_projectionSquareIso γ (Type (max u v + 1)) cX cS hcS F x _
  refine ⟨(projectionSquareIso γ (Type (max u v + 1)) cX cS hcS (op i₀)).inv.app 𝓕 ≫ σ',
    fun {m} a => ?_, fun z hz => ?_⟩
  · have hall : ∀ k : (GeIndex i₀)ᵒᵖ,
        shiftLeg (c := cS) (setLegProjection γ cS hcS F x) (geIndexToBase i₀ k) ≫
            (projectionSquareIso γ (Type (max u v + 1)) cX cS hcS (op i₀)).inv.app 𝓕 ≫ σ' =
          shiftLeg (c := cS) σ (geIndexToBase i₀ k) := by
      intro k
      refine (cancel_epi ((transitionSquareIso γ (Type (max u v + 1))
        (geIndexToBase i₀ k)).hom.app (F.obj ((geIndexOpFunctor i₀).obj k)))).mp ?_
      calc _ = ((transitionSquareIso γ (Type (max u v + 1)) (geIndexToBase i₀ k)).hom.app
              (F.obj ((geIndexOpFunctor i₀).obj k)) ≫
            shiftLeg (c := cS) (setLegProjection γ cS hcS F x) (geIndexToBase i₀ k)) ≫
            (projectionSquareIso γ (Type (max u v + 1)) cX cS hcS (op i₀)).inv.app 𝓕 ≫ σ' :=
              (Category.assoc _ _ _).symm
        _ = ((smallEtalePushforward (γ.app (op i₀)) (Type (max u v + 1))).map
              (shiftLeg (c := cX) x (geIndexToBase i₀ k)) ≫
            (projectionSquareIso γ (Type (max u v + 1)) cX cS hcS (op i₀)).hom.app 𝓕) ≫
            (projectionSquareIso γ (Type (max u v + 1)) cX cS hcS (op i₀)).inv.app 𝓕 ≫ σ' := by
          rw [key k]
        _ = (smallEtalePushforward (γ.app (op i₀)) (Type (max u v + 1))).map
              (shiftLeg (c := cX) x (geIndexToBase i₀ k)) ≫ σ' := by
          rw [Category.assoc, Iso.hom_inv_id_app_assoc]
        _ = _ := hσ' k
    exact hall (op ⟨m.unop, leOfHom a.unop⟩)
  · have h : (projectionSquareIso γ (Type (max u v + 1)) cX cS hcS (op i₀)).hom.app 𝓕 ≫ z =
        σ' :=
      hu _ fun k => by rw [reassoc_of% (key k), hz]
    rw [← h]
    exact (Iso.inv_hom_id_app_assoc
      (projectionSquareIso γ (Type (max u v + 1)) cX cS hcS (op i₀)) 𝓕 z).symm

/-- **[Stacks, Tag 0EYM] in degree zero for sheaves of sets, in adjoint form.** Let `X = lim X_i`
and `S = lim S_i` with affine transition morphisms over a nonempty directed set, `g_i : X_i ⟶ S_i`
quasi-compact and quasi-separated with limit `g : X ⟶ S`, `(F_i)` a system of sheaves of sets on
the `X_i` and `x_i : F_i ⟶ f_{i, *}𝓕` compatible maps such that the sections of `𝓕` over the base
change to `X` of every `V ×_{S_{i₀}} X_{i₀}`, `V` affine étale over `S_{i₀}`, are the filtered
colimit of those of the `F_i`. Then for every sheaf of sets `𝒢` on `S` and every family
`σ_i : g_{i, *}F_i ⟶ h_{i, *}𝒢` compatible with the transition maps of the direct images there is
a unique `χ : g_* 𝓕 ⟶ 𝒢` with `h_{i, *}χ ∘ π_i = σ_i`. -/
theorem existsUnique_setDirectImage_desc (hcX : IsLimit cX)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    (hx : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      x j = F.mapTranspose a ≫ (systemPushforward DX (Type (max u v + 1)) a).map (x i) ≫
        (coneProjectionComp (Type (max u v + 1)) cX a).hom.app 𝓕)
    (hsec : ∀ (i₀ : I) (V : (DS.obj (op i₀)).AffineEtale),
      IsSectionsColimitAt F x i₀
        ((smallEtaleBaseChange (γ.app (op i₀))).obj ((AffineEtale.Spec _).obj V)))
    (hσ : IsSetDirectImageFamily γ cS F σ) :
    ∃! χ : (smallEtalePushforward (LimitHigherDirectImage.limitMorphism γ cX cS hcS)
        (Type (max u v + 1))).obj 𝓕 ⟶ 𝒢,
      ∀ i : Iᵒᵖ, setLegProjection γ cS hcS F x i ≫
        (smallEtalePushforward (cS.π.app i) (Type (max u v + 1))).map χ = σ i := by
  choose ρ hρ hρu using fun i₀ : I => existsUnique_setLevelDescent γ cS hcS F x hx hsec hσ i₀
  have hπ : IsSetDirectImageFamily γ cS F (setLegProjection γ cS hcS F x) :=
    isSetDirectImageFamily_setLegProjection γ cS hcS F x hx
  have hcompat : AffineLimitCohomology.IsSetDirectImageCompatible cS
      ((smallEtalePushforward (LimitHigherDirectImage.limitMorphism γ cX cS hcS)
        (Type (max u v + 1))).obj 𝓕)
      𝒢 (fun i => ρ i.unop) := by
    intro i j a
    refine (hρu j.unop _ (fun {m} a'' => ?_)).symm
    obtain ⟨n, h₁, h₂⟩ := directed_of (· ≤ ·) m.unop i.unop
    have s₁ := shiftTransition_comp_shiftLeg (c := cS)
      (directTransition γ (Type (max u v + 1)) F) (setLegProjection γ cS hcS F x)
      (fun a => hπ a)
      (homOfLE h₁).op a'' ((homOfLE h₂).op ≫ a) (Subsingleton.elim _ _)
    have s₂ := shiftTransition_comp_shiftLeg (c := cS)
      (directTransition γ (Type (max u v + 1)) F) σ (fun a => hσ a)
      (homOfLE h₁).op a'' ((homOfLE h₂).op ≫ a) (Subsingleton.elim _ _)
    have c₁ := shiftLeg_cancel (A := Type (max u v + 1)) (c := cS) (homOfLE h₂).op a
      ((homOfLE h₂).op ≫ a) rfl
      (setLegProjection γ cS hcS F x (op n)) (σ (op n)) (ρ i.unop)
      (by
        have h := hρ i.unop (homOfLE h₂).op
        simp only [shiftLeg, Category.assoc] at h
        exact h)
    rw [← s₁, ← s₂]
    exact (Category.assoc _ _ _).trans (congrArg (shiftTransition (Type (max u v + 1))
      (directTransition γ (Type (max u v + 1)) F) (homOfLE h₁).op a''
        ((homOfLE h₂).op ≫ a) (Subsingleton.elim _ _) ≫ ·) ((Category.assoc _ _ _).trans c₁))
  have hsmall : Small.{max u v} ↥(Set.range DS.obj ∪ {cS.pt} : Set Scheme.{max u v}) := by
    have : Small.{max u v} ↥(Set.range DS.obj) := small_range _
    infer_instance
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small
    (Set.range DS.obj ∪ {cS.pt} : Set Scheme.{max u v})
  obtain ⟨χ, hχ, hχu⟩ := AffineLimitCohomology.existsUnique_setDirectImageDescent DS cS B
    (fun i => hB _ (Or.inl ⟨i, rfl⟩)) (hB _ (Or.inr rfl)) hcS
    ((smallEtalePushforward (LimitHigherDirectImage.limitMorphism γ cX cS hcS)
      (Type (max u v + 1))).obj 𝓕)
    𝒢 (fun i => ρ i.unop) hcompat
  refine ⟨χ, fun i => ?_, fun χ' hχ' => hχu χ' fun i => ?_⟩
  · refine (congrArg (setLegProjection γ cS hcS F x i ≫ ·) (hχ i)).trans ?_
    refine (congrArg (· ≫ ρ i.unop) (hπ (𝟙 i))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (directTransition γ (Type (max u v + 1)) F (𝟙 i) ≫ ·)
      (hρ i.unop (𝟙 i))).trans (hσ (𝟙 i)).symm
  · refine hρu i.unop _ fun {m} a => ?_
    show shiftLeg (c := cS) (setLegProjection γ cS hcS F x) a ≫
        (smallEtalePushforward (cS.π.app (op i.unop)) (Type (max u v + 1))).map χ' =
      shiftLeg (c := cS) σ a
    have hn := (coneProjectionComp (Type (max u v + 1)) cS a).hom.naturality χ'
    dsimp only [Functor.comp_map] at hn
    simp only [shiftLeg, Category.assoc]
    rw [← hn, ← Functor.map_comp_assoc, hχ' m]

end Level

section Presentation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D} (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  (F : EtaleSheafSystem D (Type (max u v + 1)))
  {𝓕 : Sheaf (smallEtaleTopology c.pt) (Type (max u v + 1))}
  (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj 𝓕)
  (hx : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      x j = F.mapTranspose a ≫ (systemPushforward D (Type (max u v + 1)) a).map (x i) ≫
        (coneProjectionComp (Type (max u v + 1)) c a).hom.app 𝓕)
  (hsec : ∀ (i₀ : I) (V : (D.obj (op i₀)).AffineEtale),
      IsSectionsColimitAt F x i₀ ((AffineEtale.Spec _).obj V))
  {𝒦 : Sheaf (smallEtaleTopology c.pt) (Type (max u v + 1))}
  (τ : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj 𝒦)
  (hτ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      τ j = F.mapTranspose a ≫ (systemPushforward D (Type (max u v + 1)) a).map (τ i) ≫
        (coneProjectionComp (Type (max u v + 1)) c a).hom.app 𝒦)

include hx hsec hτ in
/-- **The factorisation at a level, for the presentation itself.** A compatible family
`τ_i : F_i ⟶ f_{i, *}𝒦` induces a unique `ρ : f_{i₀, *}𝓕 ⟶ f_{i₀, *}𝒦` such that, for every
transition `a : i ⟶ i₀`, the shifted leg from `i` followed by `ρ` is the shifted `τ_i`. -/
theorem existsUnique_presentationLevel (i₀ : I) :
    ∃! ρ : (smallEtalePushforward (c.π.app (op i₀)) (Type (max u v + 1))).obj 𝓕 ⟶
        (smallEtalePushforward (c.π.app (op i₀)) (Type (max u v + 1))).obj 𝒦,
      ∀ {m : Iᵒᵖ} (a : m ⟶ op i₀), shiftLeg (c := c) x a ≫ ρ = shiftLeg (c := c) τ a := by
  obtain ⟨ρ, hρ, hu⟩ := existsUnique_desc_of_affineSetSections (X := D.obj (op i₀))
    (J := (GeIndex i₀)ᵒᵖ)
    (fun {j k} b => shiftTransition (Type (max u v + 1)) F.mapTranspose
      ((geIndexOpFunctor i₀).map b) (geIndexToBase i₀ j) (geIndexToBase i₀ k)
      (Subsingleton.elim _ _))
    (fun k => shiftLeg (c := c) x (geIndexToBase i₀ k))
    (fun j j' => by
      obtain ⟨m, h₁, h₂⟩ := directed_of (· ≤ ·) j.unop.1 j'.unop.1
      exact ⟨op ⟨m, j.unop.2.trans h₁⟩,
        (homOfLE (show j.unop ≤ ⟨m, j.unop.2.trans h₁⟩ from h₁)).op,
        (homOfLE (show j'.unop ≤ ⟨m, j.unop.2.trans h₁⟩ from h₂)).op, trivial⟩)
    (fun {j k} b => shiftTransition_comp_shiftLeg F.mapTranspose x hx _ _ _ _)
    (fun V s => (hsec i₀ V).1 s) (fun V k t t' ht => (hsec i₀ V).2 k t t' ht)
    (fun k => shiftLeg (c := c) τ (geIndexToBase i₀ k))
    (fun {j k} b => shiftTransition_comp_shiftLeg F.mapTranspose τ hτ _ _ _ _)
  exact ⟨ρ, fun {m} a => hρ (op ⟨m.unop, leOfHom a.unop⟩),
    fun z hz => hu z fun k => hz (geIndexToBase i₀ k)⟩

include hc hx hsec hτ in
/-- **The colimit presentation `𝓕 = colim f_i^{-1}F_i` of a sheaf of sets, in adjoint form, from
the colimit description of its sections over affine objects.** Let `X = lim X_i` with affine
transition morphisms over a nonempty directed set, `(F_i)` a system of sheaves of sets on the
`X_i` and `x_i : F_i ⟶ f_{i, *}𝓕` compatible maps such that over every affine étale
`X_{i₀}`-scheme the sections of `𝓕` over its base change to `X` are the filtered colimit of those
of the `F_i`. Then every compatible family `τ_i : F_i ⟶ f_{i, *}𝒦` is `x_i` followed by
`f_{i, *}χ` for a unique `χ : 𝓕 ⟶ 𝒦`. -/
theorem existsUnique_desc_of_sectionsColimit :
    ∃! χ : 𝓕 ⟶ 𝒦, ∀ i : Iᵒᵖ,
      x i ≫ (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).map χ = τ i := by
  choose ρ hρ hρu using fun i₀ : I => existsUnique_presentationLevel F x hx hsec τ hτ i₀
  have hcompat : AffineLimitCohomology.IsSetDirectImageCompatible c 𝓕 𝒦
      (fun i => ρ i.unop) := by
    intro i j a
    refine (hρu j.unop _ (fun {m} a'' => ?_)).symm
    obtain ⟨n, h₁, h₂⟩ := directed_of (· ≤ ·) m.unop i.unop
    have s₁ := shiftTransition_comp_shiftLeg (c := c) F.mapTranspose x hx
      (homOfLE h₁).op a'' ((homOfLE h₂).op ≫ a) (Subsingleton.elim _ _)
    have s₂ := shiftTransition_comp_shiftLeg (c := c) F.mapTranspose τ hτ
      (homOfLE h₁).op a'' ((homOfLE h₂).op ≫ a) (Subsingleton.elim _ _)
    have c₁ := shiftLeg_cancel (A := Type (max u v + 1)) (c := c) (homOfLE h₂).op a
      ((homOfLE h₂).op ≫ a) rfl (x (op n)) (τ (op n)) (ρ i.unop)
      (by
        have h := hρ i.unop (homOfLE h₂).op
        simp only [shiftLeg, Category.assoc] at h
        exact h)
    rw [← s₁, ← s₂]
    exact (Category.assoc _ _ _).trans (congrArg (shiftTransition (Type (max u v + 1))
      F.mapTranspose (homOfLE h₁).op a''
        ((homOfLE h₂).op ≫ a) (Subsingleton.elim _ _) ≫ ·) ((Category.assoc _ _ _).trans c₁))
  have hsmall : Small.{max u v} ↥(Set.range D.obj ∪ {c.pt} : Set Scheme.{max u v}) := by
    have : Small.{max u v} ↥(Set.range D.obj) := small_range _
    infer_instance
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small
    (Set.range D.obj ∪ {c.pt} : Set Scheme.{max u v})
  obtain ⟨χ, hχ, hχu⟩ := AffineLimitCohomology.existsUnique_setDirectImageDescent D c B
    (fun i => hB _ (Or.inl ⟨i, rfl⟩)) (hB _ (Or.inr rfl)) hc 𝓕 𝒦 (fun i => ρ i.unop) hcompat
  refine ⟨χ, fun i => ?_, fun χ' hχ' => hχu χ' fun i => ?_⟩
  · refine (congrArg (x i ≫ ·) (hχ i)).trans ?_
    refine (congrArg (· ≫ ρ i.unop) (hx (𝟙 i))).trans ?_
    simp only [Category.assoc]
    have h := hρ i.unop (𝟙 i)
    simp only [shiftLeg, Category.assoc] at h
    rw [h]
    exact (hτ (𝟙 i)).symm
  · refine hρu i.unop _ fun {m} a => ?_
    show shiftLeg (c := c) x a ≫
        (smallEtalePushforward (c.π.app (op i.unop)) (Type (max u v + 1))).map χ' =
      shiftLeg (c := c) τ a
    have hn := (coneProjectionComp (Type (max u v + 1)) c a).hom.naturality χ'
    dsimp only [Functor.comp_map] at hn
    simp only [shiftLeg, Category.assoc]
    rw [← hn, ← Functor.map_comp_assoc, hχ' m]

end Presentation

end Stacks.EtaleCohomology.LimitSetDirectImage

end
