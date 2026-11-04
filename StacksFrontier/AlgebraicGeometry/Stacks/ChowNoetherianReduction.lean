module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Main
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowChangeOfBaseTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowNoetherianCase
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowNoetherianReductionInputs
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHigherDirectImagesQcqs
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements

/-!
# Chow's lemma for algebraic stacks over `Spec ℤ`, from the Noetherian case

The reduction of the proof of Chow's lemma for algebraic stacks (Stacks 0CQ8) to the Noetherian
case, over the base `Spec ℤ`, granted the statements of Stacks 0CQ2, Stacks 0CN4 and Stacks 0CPZ
(`AlgebraicGeometry.Stack.AlgebraicStacks.ClosedImmersionIntoFinitePresentationStatement`,
`...FinitePresentationStackDescendsStatement`, `...SeparatedAtFiniteStageStatement`): Stacks 0CQ2
reduces to finite presentation, Stacks 07SU writes the base as a limit of Noetherian algebraic
spaces, Stacks 0CN4 and Stacks 0CPZ bring the stack and its separatedness to a finite stage, and
the Noetherian case applies there.

## Main results

* `AlgebraicGeometry.Stack.isQuasiSeparatedOver_of_equivalenceOver_algebraicSpace`: a stack
  represented by an algebraic space quasi-separated over the base is quasi-separated over the base.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiSeparated_algebraicSpaceStack`: the
  algebraic stack of a quasi-separated algebraic space is quasi-separated (Stacks 03BS, 050D (8)).
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_overIntegers_of_statements`: Stacks 0CQ8
  over `Spec ℤ`, granted the three statements.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u})

/-- **A stack represented by an algebraic space quasi-separated over the base is quasi-separated
over the base** (Stacks 050D, part (4)): the structure morphism is represented by the morphism from
the algebraic space to the terminal presheaf, which is quasi-separated by Stacks 04ZI (6), so its
relative diagonal is quasi-compact. -/
theorem isQuasiSeparatedOver_of_equivalenceOver_algebraicSpace {S₀ : Scheme.{u}}
    (h₀ : B.Contains S₀) (𝒵 : AlgebraicStacks.{u, w} B S₀ h₀)
    {N : (BigFppfOver B S₀ h₀)ᵒᵖ ⥤ Type u} (hN : IsAlgebraicSpace B S₀ h₀ N)
    (hNqs : Space.IsQuasiSeparatedOver B S₀ h₀ N)
    (e : StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
      (presheafOfCategories (N ⋙ typeToCat)).p) :
    IsQuasiSeparatedOver.{u, w} B S₀ h₀ 𝒵 := by
  have hrep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S₀ h₀
    (schemeStack.{u, w} B S₀ h₀ (Over.mk (𝟙 (B.obj h₀)))).property ⟨N, hN, ⟨e⟩⟩
    (structureMorphism.{u, w} B S₀ h₀ 𝒵).hom
  have hstep : IsQuasiSeparated.{u, u, u + 1} B S₀ h₀
      (structureMorphism.{u, w} B S₀ h₀ 𝒵).hom :=
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S₀ h₀
      (Space.quasiSeparatedProperty B S₀ h₀)
      (structureMorphism.{u, w} B S₀ h₀ 𝒵).hom hrep
      N (yoneda.obj (Over.mk (𝟙 (B.obj h₀)))) hN
      (isAlgebraicSpace_yoneda B S₀ h₀ (Over.mk (𝟙 (B.obj h₀))))
      e (PresheafOfCategories.sliceElementsEquivalenceOver _)).2
      (Space.isQuasiSeparated_of_isQuasiSeparatedOver B S₀ h₀ hNqs _)
  refine (AlgebraicStacks.isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal B S₀ h₀
    (structureMorphism.{u, w} B S₀ h₀ 𝒵) hrep).2 ?_
  exact (isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S₀ h₀
    (structureMorphism.{u, w} B S₀ h₀ 𝒵) hrep).2 hstep

namespace AlgebraicStacks

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- **The algebraic stack of a quasi-separated algebraic space is quasi-separated** in the absolute
sense of Stacks 050D, part (8). Its view over `Spec ℤ` is represented by the view of the space
there, the lower-shriek extension
(`CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`), which is quasi-separated
over `Spec ℤ` by definition of absolute quasi-separatedness (Stacks 03BS). -/
theorem isAbsolutelyQuasiSeparated_algebraicSpaceStack (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ Y) :
    AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ
      (algebraicSpaceStack.{u, w} B S hS Y hY) := by
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  exact isQuasiSeparatedOver_of_equivalenceOver_algebraicSpace.{u, w} B hZ
    (changeBaseAlgebraicStacks.{u, w, w} B S (⊤_ Scheme.{u}) hS hZ g
      (algebraicSpaceStack.{u, w} B S hS Y hY))
    (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g Y hY) hYqs
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g Y)

/-- **The finite presentation step of the proof of Stacks 0CQ8, along a conventional Noetherian
approximation.** Let `Y` be an algebraic space with a Noetherian approximation `Y = lim Y_i`
satisfying the chapter's convention of Section 70.2, and `f : 𝒳 ⟶ Y` a separated 1-morphism of
finite presentation. Granted the statements of Stacks 0CN4 and Stacks 0CPZ under the convention,
if the conclusion of Chow's lemma holds for every separated 1-morphism of finite type to a
Noetherian algebraic space (`hN`), it holds for `f`.

The proof is that of
`AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_hasNoetherianApproximation`, whose
inputs are the two statements without the convention; Stacks 0CN4 writes `𝒳 ≃ Y ×_{Y_i} 𝒳ᵢ`,
Stacks 0CPZ makes `Y_{i₀} ×_{Y_i} 𝒳ᵢ ⟶ Y_{i₀}` separated, `hN` covers it and the cover base changes
to one of `f`. -/
private theorem HasChowCover.of_conventionalNoetherianApproximation
    (h0CN4 : FinitePresentationStackDescendsStatement.{u, w} B S hS)
    (h0CPZ : SeparatedAtFiniteStageStatement.{u, w} B S hS)
    (hN : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsNoetherian B S hS (BigFppfSite.contains_terminal B) Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f → IsFiniteType B S hS f → HasChowCover.{u, w} B S hS hY f)
    (hqs : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B) Y →
      AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS
        (BigFppfSite.contains_terminal B) (algebraicSpaceStack.{u, w} B S hS Y hY))
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j))
    (hAff : ∀ {j j' : Iᵒᵖ} (g : j ⟶ j'), Space.IsAffineHom B S hS (D.map g))
    (hDqc : ∀ j, Space.IsQuasiCompactSpace B S hS (D.obj j))
    (hDqs : ∀ j, Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B)
      (D.obj j))
    (hDN : ∀ j, Space.IsNoetherian B S hS (BigFppfSite.contains_terminal B) (D.obj j))
    (hconv : Space.SiteContainsBaseChangeLimits B S hS D)
    (hY : IsAlgebraicSpace B S hS (limit D))
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS (limit D) hY)
    (hsep : IsSeparated B S hS f) (hfp : IsFinitePresentation B S hS f) :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨i, 𝒳ᵢ, fᵢ, hfᵢ, e, ⟨he⟩⟩ := h0CN4 D hY hD (fun g => hAff g) hDqc hDqs hconv
    𝒳 f hfp
  let D' : Space.DescentSituation B S hS (BigFppfSite.contains_terminal B) I :=
    { system := D
      algebraicSpace := fun j => hD (op j)
      transition_affine := hAff
      quasiCompact := fun j => hDqc (op j)
      quasiSeparated := fun j => hDqs (op j)
      limitCone := limit.cone D
      isLimit := limit.isLimit D
      limitAlgebraicSpace := hY
      base := i.unop }
  -- the 2-fibre product `Y ×_{Y_i} 𝒳ᵢ` and its separatedness
  let P := twoFibreProductSquareAlgebraicStacks B S hS fᵢ
    (algebraicSpaceStackMap.{u, w} B S hS hY (hD i) (limit.π D i))
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _
  let T : Bicategory.TwoCommSq fᵢ
      (algebraicSpaceStackMap.{u, w} B S hS hY (hD i) (limit.π D i)) :=
    { pt := 𝒳
      fst := e.hom ≫ P.fst
      snd := e.hom ≫ P.snd
      iso := Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso e.hom P.iso ≪≫
        (Bicategory.associator _ _ _).symm }
  let a : Bicategory.TwoCommSq.PreHom T P :=
    { hom := e.hom
      isoFst := Iso.refl _
      isoSnd := Iso.refl _
      compat := by
        simp only [T, Iso.trans_hom, Iso.symm_hom, Bicategory.whiskerLeftIso_hom, Iso.refl_hom,
          Bicategory.id_whiskerRight, Category.id_comp, Category.comp_id,
          Category.assoc, Iso.inv_hom_id, Bicategory.associator] }
  have hT : Bicategory.IsTwoFibreProduct T :=
    Bicategory.isTwoFibreProduct_of_section hP (a.ofSection e.inv e.counit) e.hom e.unit.symm
  let d : Bicategory.TwoCommSq.PreHom P T := _root_.Quotient.out (hT.from P)
  have hd : Functor.IsEquivalence d.hom.hom.hom.toFunctor :=
    isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hP hT d
  have hPsep : IsSeparated B S hS P.snd :=
    isSeparated_of_equivalence B S hS f P.snd d.hom.hom.hom
      (algStackHomHomIso B S hS (Bicategory.whiskerLeftIso d.hom he.symm ≪≫ d.isoSnd.symm))
      hd hsep
  -- the stage `𝒳ᵢ` is quasi-compact and quasi-separated
  have h𝒳ᵢqc : IsQuasiCompactStack.{u, w} B S hS 𝒳ᵢ.val 𝒳ᵢ.property :=
    isQuasiCompactStack_of_isQuasiCompactMorphism B S hS fᵢ hfᵢ.2.1
      (isQuasiCompactStack_fibredCategory B S hS _ (hD i)
        (hDqc i) _)
  have h𝒳ᵢqs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS
      (BigFppfSite.contains_terminal B) 𝒳ᵢ :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS _ fᵢ
      (hqs _ (hD i) (hDqs i)) hfᵢ.2.2
  -- Stacks 0CPZ: separatedness at a finite stage `i₀ ≥ i`
  obtain ⟨i₀, h₀, hsep₀⟩ := h0CPZ D' hconv 𝒳ᵢ fᵢ h𝒳ᵢqc h𝒳ᵢqs hPsep
  have hY₀ : IsAlgebraicSpace B S hS (D.obj (op i₀)) := hD (op i₀)
  let t : D.obj (op i₀) ⟶ D.obj i := D.map (homOfLE h₀).op
  let Sq := twoFibreProductSquareAlgebraicStacks B S hS fᵢ
    (algebraicSpaceStackMap.{u, w} B S hS hY₀ (hD i) t)
  have hSq : Bicategory.IsTwoFibreProduct Sq :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _
  have hSqsep : IsSeparated B S hS Sq.snd := hsep₀ i₀ le_rfl
  have hSqft : IsFiniteType B S hS Sq.snd :=
    isFiniteType_of_isFinitePresentation B S hS _
      (isFinitePresentation_baseChange B S hS fᵢ _ Sq.swap
        (Bicategory.isTwoFibreProduct_swap hSq) hfᵢ)
  have h₀cover : HasChowCover.{u, w} B S hS hY₀ Sq.snd :=
    hN _ hY₀ (hDN (op i₀)) Sq.pt Sq.snd hSqsep hSqft
  -- pasting: `Y ×_{Y_i} 𝒳ᵢ = Y ×_{Y_{i₀}} (Y_{i₀} ×_{Y_i} 𝒳ᵢ)`
  have hπ : limit.π D i = limit.π D (op i₀) ≫ t := (limit.w D (homOfLE h₀).op).symm
  have hcomp : algebraicSpaceStackMap.{u, w} B S hS hY (hD i) (limit.π D i) =
      algebraicSpaceStackMap.{u, w} B S hS hY hY₀ (limit.π D (op i₀)) ≫
        algebraicSpaceStackMap.{u, w} B S hS hY₀ (hD i) t :=
    (congrArg (algebraicSpaceStackMap.{u, w} B S hS hY (hD i)) hπ).trans
      (algebraicSpaceStackMap_comp B S hS hY hY₀ (hD i) _ t)
  let Z := P.reindexSnd (eqToIso hcomp)
  have hZ : Bicategory.IsTwoFibreProduct Z := Bicategory.isTwoFibreProduct_reindexSnd _ hP
  exact HasChowCover.of_equivalence_twoFibreProduct B S hS hY hY₀ (limit.π D (op i₀)) Sq.snd
    (Bicategory.innerSq hSq Z) (isTwoFibreProduct_innerSq B S hS hSq hZ) f e he h₀cover

/-- **Stack maps of mutually inverse morphisms of algebraic spaces compose to the identity.** -/
private theorem algebraicSpaceStackMap_comp_eq_id
    {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (t : Y ⟶ Y') (s : Y' ⟶ Y) (h : t ≫ s = 𝟙 Y) :
    algebraicSpaceStackMap.{u, w} B S hS hY hY' t ≫
      algebraicSpaceStackMap.{u, w} B S hS hY' hY s = 𝟙 _ := by
  rw [← algebraicSpaceStackMap_comp_eq, h, algebraicSpaceStackMap_id_eq]

/-- **The 1-morphism induced by an isomorphism of algebraic spaces is an equivalence of the
underlying categories**, the stack map of the inverse being an inverse on the nose. -/
private theorem isEquivalence_homFunctor_algebraicSpaceStackMap_of_isIso
    {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (t : Y ⟶ Y') [IsIso t] :
    (CatFiberedInGroupoids.homFunctor
      (algebraicSpaceStackMap.{u, w} B S hS hY hY' t).hom).IsEquivalence := by
  have h₁ := algebraicSpaceStackMap_comp_eq_id.{u, w} B S hS hY' hY (inv t) t (IsIso.inv_hom_id t)
  have h₂ := algebraicSpaceStackMap_comp_eq_id.{u, w} B S hS hY hY' t (inv t) (IsIso.hom_inv_id t)
  exact (CategoryTheory.Equivalence.mk (CatFiberedInGroupoids.homFunctor
      (algebraicSpaceStackMap.{u, w} B S hS hY hY' t).hom)
    (CatFiberedInGroupoids.homFunctor (algebraicSpaceStackMap.{u, w} B S hS hY' hY (inv t)).hom)
    (eqToIso (congrArg (fun m => CatFiberedInGroupoids.homFunctor m.hom) h₂).symm)
    (eqToIso (congrArg (fun m => CatFiberedInGroupoids.homFunctor m.hom) h₁))).isEquivalence_functor

/-- **A Chow cover passes along an isomorphism of the target.** If `t : Y ⟶ Y'` is an
isomorphism of algebraic spaces and `f ≫ t` has a Chow cover, so does `f`: compose the proper
morphism of the cover with `t⁻¹`. -/
private theorem HasChowCover.of_comp_algebraicSpaceStackMap_of_isIso
    {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (t : Y ⟶ Y') [IsIso t]
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (h : HasChowCover.{u, w} B S hS hY' (f ≫ algebraicSpaceStackMap.{u, w} B S hS hY hY' t)) :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨X, Xbar, hX, hXbar, a, i, p, ha, has, hi, hp, ⟨ea⟩⟩ := h
  let Φ := algebraicSpaceStackMap.{u, w} B S hS hY hY' t
  let Ψ := algebraicSpaceStackMap.{u, w} B S hS hY' hY (inv t)
  have h₂ : Φ ≫ Ψ = 𝟙 _ :=
    algebraicSpaceStackMap_comp_eq_id.{u, w} B S hS hY hY' t (inv t) (IsIso.hom_inv_id t)
  refine ⟨X, Xbar, hX, hXbar, a, i, p ≫ inv t, ha, has, hi,
    Space.isProper_comp B S hS hXbar hY' hY p (inv t) hp (Space.isProper_of_isIso B S hS (inv t)),
    ⟨Bicategory.whiskerLeftIso a (Bicategory.rightUnitor f).symm ≪≫
      eqToIso (by rw [h₂]) ≪≫ Bicategory.whiskerLeftIso a (Bicategory.associator f Φ Ψ).symm ≪≫
      (Bicategory.associator a (f ≫ Φ) Ψ).symm ≪≫ Bicategory.whiskerRightIso ea Ψ ≪≫
      eqToIso ?_⟩⟩
  rw [← algebraicSpaceStackMap_comp_eq, Category.assoc]

/-- **Chow's lemma for algebraic stacks over `Spec ℤ` (Stacks 0CQ8), granted the statements of
Stacks 0CQ2, Stacks 0CN4 and Stacks 0CPZ.** Let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite
type from an algebraic stack over `Spec ℤ` to a quasi-compact quasi-separated algebraic space.
Then there are a proper surjective `X ⟶ 𝒳` from an algebraic space, an open immersion `X ⟶ X̄`
and a proper `X̄ ⟶ Y` making the triangle 2-commute.

By Stacks 0CQ2 it suffices that `f` be of finite presentation
(`AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_forall_isFinitePresentation`). Then
Stacks 07SU writes `Y` as a limit of Noetherian algebraic spaces with affine transition morphisms
satisfying the chapter's convention of Section 70.2
(`AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_etaleAtlas`), and Stacks 0CN4
and Stacks 0CPZ, under the convention, reduce to the Noetherian case, which is
`AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_isNoetherian`. -/
theorem hasChowCover_overIntegers_of_statements
    (h0CQ2 : ClosedImmersionIntoFinitePresentationStatement.{u, w} B (⊤_ Scheme.{u})
      B.contains_terminal)
    (h0CN4 : FinitePresentationStackDescendsStatement.{u, w} B (⊤_ Scheme.{u})
      B.contains_terminal)
    (h0CPZ : SeparatedAtFiniteStageStatement.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal)
    {Y : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Y)
    (hYqc : Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal
      B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal Y hY)
    (hsep : IsSeparated B (⊤_ Scheme.{u}) B.contains_terminal f)
    (hft : IsFiniteType B (⊤_ Scheme.{u}) B.contains_terminal f) :
    HasChowCover.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal hY f :=
  HasChowCover.of_forall_isFinitePresentation B (⊤_ Scheme.{u}) B.contains_terminal h0CQ2
    (fun Y hY hYqc hYqs _ f hsep hfp => by
      obtain ⟨U, a, -, has, hae⟩ :=
        (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (⊤_ Scheme.{u})
          B.contains_terminal _ hY).mp hYqc
      obtain ⟨A, hconv⟩ :=
        Space.hasConventionalNoetherianApproximation_of_etaleAtlas hY hYqc hYqs U a has hae
      let := A.preorder
      let := A.nonempty
      let := A.isDirected
      -- the limit of the system, identified with `Y`
      let eY : Y ≅ limit A.diagram := A.isLimit.conePointUniqueUpToIso (limit.isLimit A.diagram)
      have hL : IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal (limit A.diagram) :=
        isAlgebraicSpace_of_iso B (⊤_ Scheme.{u}) B.contains_terminal eY.symm hY
      let Φ := algebraicSpaceStackMap.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal hY hL eY.hom
      have hΦsep : IsSeparated B (⊤_ Scheme.{u}) B.contains_terminal Φ :=
        (isSeparated_algebraicSpaceStackMap_iff.{u, w} B (⊤_ Scheme.{u}) B.contains_terminal hY
          hL eY.hom).2 (Space.isSeparated_of_isIso B (⊤_ Scheme.{u}) B.contains_terminal eY.hom)
      have hΦfp : IsFinitePresentation B (⊤_ Scheme.{u}) B.contains_terminal Φ :=
        isFinitePresentation_of_isEquivalence_homFunctor B (⊤_ Scheme.{u}) B.contains_terminal Φ
          (isEquivalence_homFunctor_algebraicSpaceStackMap_of_isIso.{u, w} B (⊤_ Scheme.{u})
            B.contains_terminal hY hL eY.hom)
      refine HasChowCover.of_comp_algebraicSpaceStackMap_of_isIso B (⊤_ Scheme.{u})
        B.contains_terminal hY hL eY.hom f ?_
      exact HasChowCover.of_conventionalNoetherianApproximation B (⊤_ Scheme.{u})
        B.contains_terminal h0CN4 h0CPZ
        (fun _ hY hYN _ f hsep hft => hasChowCover_of_isNoetherian hY hYN f hsep hft)
        (fun _ hY hYqs => isAbsolutelyQuasiSeparated_algebraicSpaceStack B (⊤_ Scheme.{u})
          B.contains_terminal B.contains_terminal hY hYqs)
        A.diagram A.isAlgebraicSpace (fun g => A.isAffineHom_map g) A.isQuasiCompactSpace
        A.isAbsolutelyQuasiSeparated A.isNoetherian hconv hL (f ≫ Φ)
        (isSeparated_comp B (⊤_ Scheme.{u}) B.contains_terminal f Φ hsep hΦsep)
        (isFinitePresentation_comp B (⊤_ Scheme.{u}) B.contains_terminal f Φ hfp hΦfp))
    hY hYqc hYqs f hsep hft

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
