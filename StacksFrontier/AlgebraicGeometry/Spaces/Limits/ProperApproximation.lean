module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFilteredColimitOfApproximation
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedImage

/-!
# Approximating proper morphisms of algebraic spaces

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S` with `Y`
quasi-compact and quasi-separated. Stacks 0A0W asserts that `X` is a directed limit of algebraic
spaces `X_i` proper and of finite presentation over `Y`, with closed immersions as transition
morphisms and as projections `X ⟶ X_i`.

## Main results

* `AlgebraicGeometry.Space.exists_projectiveSchemeCover_toAffine`: Chow's lemma (Stacks 089J)
  over an affine object `U` of the site, in the form the proof of Stacks 0A0W uses it: a proper
  surjective morphism from a scheme `V` of the site, together with an immersion of `V` into a
  scheme `P` of the site which is proper over `U`.
* `AlgebraicGeometry.Space.exists_isProper_closedSubspace_toAffine`: the claim in the proof of
  Stacks 0A0W over an affine base.
* `AlgebraicGeometry.Space.exists_properApproximation_of_steps`: Stacks 0A0W, from the inputs of
  the staged Stacks 0872 and 0A0U and from Stacks 0A0T.
* `AlgebraicGeometry.Space.exists_isClosedImmersion_isProper_isFinitePresentation_of_isProper`:
  the closed immersion `X ⟶ X'` into a space proper and of finite presentation over `Y` that
  Stacks 0A0W provides, from the same three results.

## Implementation notes

As in the source, the space `X'` separated and of finite presentation over `Y` containing `X`
comes from Stacks 0873
(`AlgebraicGeometry.Space.exists_isSeparated_isFinitePresentation_closedImmersion_of_steps`),
and `X` is the limit of the closed subspaces `X_i ⊆ X'` of finite presentation that Stacks 0A0U
provides. Whether `X_i ⟶ Y` is proper is checked after base change to an affine surjective étale
chart of `Y` (Stacks 083R). Over an affine `U` the weak Chow lemma, read through the
equivalence of Stacks 04SG, gives a scheme `X''` with a proper surjection `π : X'' ⟶ X'` and an
immersion `X'' ⟶ ℙⁿ_U`; the preimage of `X` is proper over `U`, hence a closed subspace of
`ℙⁿ_U` (Stacks 04NX and 04CD), and Stacks 0A0T makes the preimages of the `X_i` closed in
`ℙⁿ_U` for `i` large, hence proper over `U`, which passes to `X_i` along the surjection
(Stacks 08AJ).

Stacks 0A0T is taken without a bound on the size of the index, as in the source: the index of
Stacks 0A0U, the finite type quasi-coherent subideals of an ideal sheaf, admits no such bound.

## References

* [Stacks Project, Tag 0A0W](https://stacks.math.columbia.edu/tag/0A0W)
* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 0A0T](https://stacks.math.columbia.edu/tag/0A0T)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Filter

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Chow's lemma over an affine object of the site -/

/-- The structural morphism to the representable presheaf of the lower-shriek extension of a
representable presheaf is the Yoneda image of the structure morphism, read through
`AlgebraicGeometry.relocalizedYonedaIso`. -/
theorem relocalizeToYoneda_yoneda_eq {W : Scheme.{u}} (hW : B.Contains W)
    (g : B.obj hW ⟶ B.obj hS) (V : BigFppfOver B W hW) :
    OverShriek.relocalizeToYoneda g (yoneda.obj V) =
      (relocalizedYonedaIso B (B.obj hW) (B.obj hS) g V).hom ≫
        yoneda.map (Over.homMk V.hom rfl : (Over.map g).obj V ⟶ Over.mk g) := by
  ext T x
  exact Over.OverMorphism.ext (Over.w x.1.2).symm

/-- **Chow's lemma over an affine object of the site, with the projective embedding.** Let
`q : Q ⟶ h_U` be a separated morphism of finite type from an algebraic space over `S` to the
presheaf represented by an affine object `U` of the site. Then there are an object `V` of the
site, a proper surjective morphism `ρ : h_V ⟶ Q`, an object `P` of the site, an immersion
`j : V ⟶ P` and a proper morphism `p : P ⟶ U` with `ρ ≫ q = h(j ≫ p)`.

This is Stacks 089J (`AlgebraicGeometry.Space.hasChowSchemeCover_of_isSeparated_isFiniteType`),
read over `U` as in
`AlgebraicGeometry.Space.exists_properSurjective_schemeCover_of_isProper_toAffine`
through the equivalence of Stacks 04SG, with the H-quasi-projective embedding of the cover kept:
`P` is the projective space `ℙⁿ_U`, an object of the site because it is of finite type over
`U`. -/
theorem exists_projectiveSchemeCover_toAffine
    (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (q : Q ⟶ yoneda.obj U) (hsep : IsSeparated B S hS q) (hft : IsFiniteType B S hS q) :
    ∃ (V : BigFppfOver B S hS) (ρ : yoneda.obj V ⟶ Q) (P : BigFppfOver B S hS)
      (j : V ⟶ P) (p : P ⟶ U),
      IsProper B S hS ρ ∧ IsSurjective B S hS ρ ∧ ρ ≫ q = yoneda.map (j ≫ p) ∧
        _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
        _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map p) := by
  classical
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  -- An isomorphic object of the site whose underlying scheme is literally a `Spec`.
  let A : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  let eT : Spec A ≅ (BigFppfOver.toScheme B S hS).obj U :=
    ((BigFppfOver.toScheme B S hS).obj U).isoSpec.symm
  have hA : B.Contains (Spec A) := (Scheme.size_congr eT).trans_lt U.left.property
  let εiso : B.obj hA ≅ U.left :=
    { hom := B.inclusion.preimage eT.hom
      inv := B.inclusion.preimage eT.inv
      hom_inv_id := B.inclusion.map_injective (by
        rw [CategoryTheory.Functor.map_comp, B.inclusion.map_preimage,
          B.inclusion.map_preimage, eT.hom_inv_id, CategoryTheory.Functor.map_id]
        rfl)
      inv_hom_id := B.inclusion.map_injective (by
        rw [CategoryTheory.Functor.map_comp, B.inclusion.map_preimage,
          B.inclusion.map_preimage, eT.inv_hom_id, CategoryTheory.Functor.map_id]
        rfl) }
  let g₀ : B.obj hA ⟶ B.obj hS := εiso.hom ≫ U.hom
  let U' : BigFppfOver B S hS := Over.mk g₀
  let θ : U' ≅ U := Over.isoMk εiso rfl
  let yθ : yoneda.obj U ≅ yoneda.obj U' := yoneda.mapIso θ.symm
  let q' : Q ⟶ yoneda.obj U' := q ≫ yθ.hom
  have hsep' : IsSeparated B S hS q' :=
    isSeparated_of_arrowIso B S hS q q' (𝟙 Q) yθ.hom (by simp [q']) hsep
  have hft' : IsFiniteType B S hS q' :=
    isFiniteType_of_arrowIso B S hS q q' (𝟙 Q) yθ.hom (by simp [q']) hft
  -- Read `(Q, q')` as an algebraic space over the smaller base `Spec A`.
  let P₀ : ObjectProperty
      (Over (yoneda.obj U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    fun Z => IsAlgebraicSpace B S hS Z.left
  let Qobj : SpacesOverSmallerBase B (Spec A) S hA hS g₀ := ⟨Over.mk q', hQ⟩
  let eqv := spacesOverSmallerBaseEquivalence B (Spec A) S hA hS g₀
  let Qt : AlgebraicSpaces B (Spec A) hA := eqv.inverse.obj Qobj
  let cIso : (spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt ≅ Qobj :=
    eqv.counitIso.app Qobj
  let cOver : ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1 ≅ (Over.mk q' :
      Over (yoneda.obj U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    (ObjectProperty.ι P₀).mapIso cIso
  let cLeft : ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1.left ≅ Q :=
    (Over.forget (yoneda.obj U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).mapIso cOver
  have hcw : cLeft.hom ≫ q' =
      ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1.hom := Over.w cOver.hom
  let fIso : (OverShriek.relocalizePresheafFunctor g₀).obj Qt.1 ≅
      ((spacesOverSmallerBaseFunctor B (Spec A) S hA hS g₀).obj Qt).1.left :=
    ((spacesOverSmallerBaseFunctorForgetIso B (Spec A) S hA hS g₀).app Qt).symm
  let lamIso : (OverShriek.relocalizePresheafFunctor g₀).obj Qt.1 ≅ Q := fIso ≪≫ cLeft
  let lam : (OverShriek.relocalizePresheafFunctor g₀).obj Qt.1 ⟶ Q := lamIso.hom
  have : IsIso lam := ⟨lamIso.inv, lamIso.hom_inv_id, lamIso.inv_hom_id⟩
  have hlam : lam ≫ q' = OverShriek.relocalizeToYoneda g₀ Qt.1 :=
    (Category.assoc fIso.hom cLeft.hom q').trans
      ((congrArg (fun z ↦ fIso.hom ≫ z) hcw).trans
        (relocalizeToYoneda_eq B (Spec A) S hA hS g₀ Qt))
  -- Separatedness and finite type of the structural morphism of `Q̃` over `Spec A`.
  have : IsIso (OverShriek.relocalizeToYoneda g₀
      (yoneda.obj (Over.mk (𝟙 (B.obj hA))) : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u)) :=
    isIso_relocalizeToYoneda_yonedaId B (Spec A) S hA hS g₀
  have hRel := relocalizeToYoneda_eq_map_toYonedaId B (Spec A) S hA hS g₀ Qt.1
  have hw : 𝟙 _ ≫ (OverShriek.relocalizePresheafFunctor g₀).map (toYonedaId B (Spec A) hA Qt.1) =
      (lam ≫ q') ≫ inv (OverShriek.relocalizeToYoneda g₀
        (yoneda.obj (Over.mk (𝟙 (B.obj hA))) : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u)) := by
    rw [hlam, ← hRel]
    simp
  have hstructSep : IsSeparated B (Spec A) hA (toYonedaId B (Spec A) hA Qt.1) :=
    isSeparated_of_relocalizeMap B (Spec A) S hA hS g₀ _ <|
      isSeparated_of_arrowIso B S hS (lam ≫ q') _ _ _ hw <|
        isSeparated_of_arrowIso B S hS q' (lam ≫ q') (inv lam) (𝟙 _) (by simp) hsep'
  have hstructFt : IsFiniteType B (Spec A) hA (toYonedaId B (Spec A) hA Qt.1) :=
    (isFiniteType_relocalize_iff B (Spec A) hA S hS g₀ _).mp <|
      isFiniteType_of_arrowIso B S hS (lam ≫ q') _ _ _ hw <|
        isFiniteType_of_arrowIso B S hS q' (lam ≫ q') (inv lam) (𝟙 _) (by simp) hft'
  -- Chow's lemma over `Spec A`.
  obtain ⟨V', p₁, hpProper, hpSurj, hqp⟩ :=
    hasChowSchemeCover_of_isSeparated_isFiniteType B A hA Qt.1 Qt.2
      (toYonedaId B (Spec A) hA Qt.1) hstructSep hstructFt
  obtain ⟨n, i, hi, -, hicomp⟩ := hqp
  -- The projective space over `Spec A`, as an object of the site over `S`.
  let P₀s : Scheme.{u} := projectiveSpaceOver n (Spec A)
  let str : P₀s ⟶ Spec A := projectiveSpaceOver n (Spec A) ↘ Spec A
  have hP : B.Contains P₀s :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact str hA
  let strB : B.obj hP ⟶ B.obj hA := B.inclusion.preimage str
  let P : BigFppfOver B S hS := Over.mk (strB ≫ g₀)
  let pOver : P ⟶ U' := Over.homMk strB rfl
  have hiV : B.inclusion.preimage i ≫ strB = V'.hom := B.inclusion.map_injective (by
    rw [CategoryTheory.Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
    exact hicomp)
  let jOver : (Over.map g₀).obj V' ⟶ P :=
    Over.homMk (B.inclusion.preimage i) (by
      change B.inclusion.preimage i ≫ strB ≫ g₀ = V'.hom ≫ g₀
      rw [← Category.assoc, hiV])
  let w₀ : (Over.map g₀).obj V' ⟶ U' := Over.homMk V'.hom rfl
  have hjp : jOver ≫ pOver = w₀ := Over.OverMorphism.ext hiV
  -- Carry the cover back to the base `S`.
  let yIso := relocalizedYonedaIso B (B.obj hA) (B.obj hS) g₀ V'
  refine ⟨(Over.map g₀).obj V',
    yIso.inv ≫ (OverShriek.relocalizePresheafFunctor g₀).map p₁ ≫ lam, P, jOver,
    pOver ≫ θ.hom, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isProper_isIso_comp_iff B S hS yIso.inv _).mpr
      ((isProper_comp_isIso_iff B S hS _ lam).mpr
        ((isProper_relocalize_iff B (Spec A) hA S hS g₀
          (isAlgebraicSpace_yoneda B (Spec A) hA V') Qt.2 p₁).mpr hpProper))
  · exact isSurjective_comp B S hS (isSurjective_of_isIso B S hS yIso.inv)
      (isSurjective_comp B S hS (isSurjective_relocalize B (Spec A) hA S hS g₀ p₁ hpSurj)
        (isSurjective_of_isIso B S hS lam))
  · have hq : q = q' ≫ yθ.inv := by simp [q']
    have hn := relocalizeToYoneda_naturality B (Spec A) S hA hS g₀ p₁
    rw [hq, Category.assoc, Category.assoc, reassoc_of% hlam, reassoc_of% hn,
      relocalizeToYoneda_yoneda_eq, Category.assoc, Iso.inv_hom_id_assoc,
      ← Category.assoc jOver pOver θ.hom, hjp]
    simp [yθ, w₀]
  · change _root_.AlgebraicGeometry.IsImmersion
      (B.inclusion.map (B.inclusion.preimage (X := V'.left) (Y := B.obj hP) i))
    rw [B.inclusion.map_preimage]
    exact hi
  · have : _root_.AlgebraicGeometry.IsProper str := isProper_projectiveSpaceOver n (Spec A)
    change _root_.AlgebraicGeometry.IsProper (B.inclusion.map (strB ≫ εiso.hom))
    rw [CategoryTheory.Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
    infer_instance

/-! ### The claim over an affine base -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The preimage of a subfunctor containing the intersection of a family contains the
intersection of the preimages of the family. -/
private theorem iInf_preimage_le_preimage {ι : Sort*} {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Z : ι → Subfunctor F) (W : Subfunctor F) (p : F' ⟶ F) (hge : (⨅ i, Z i) ≤ W) :
    (⨅ i, (Z i).preimage p) ≤ W.preimage p := by
  intro T x hx
  refine hge _ ?_
  rw [Subfunctor.iInf_obj, Set.mem_iInter] at hx ⊢
  exact hx

/-- A scheme of the site which is compact and quasi-separated gives a quasi-compact and
absolutely quasi-separated algebraic space. -/
private theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_yoneda (P : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj P)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj P)] :
    IsQuasiCompactSpace B S hS (yoneda.obj P) ∧
      IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj P) :=
  ⟨isQuasiCompact_yoneda_of_compact B S hS P inferInstance,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj P) hZ
      ⟨P, inferInstance, ⟨Functor.RepresentableBy.yoneda P⟩⟩⟩

/-- The morphism from the inverse system of an antitone family of subfunctors of `M` to the
constant system on `N` given by the composite of the inclusions with `g : M ⟶ N`. -/
private def closedSubspaceDiagramToConst {ι : Type u} [Preorder ι]
    {M N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : ι → Subfunctor M)
    (hZ : ∀ ⦃i j : ι⦄, i ≤ j → Z j ≤ Z i) (g : M ⟶ N) :
    closedSubspaceDiagram B S hS Z hZ ⟶ (Functor.const ιᵒᵖ).obj N where
  app a := (Z a.unop).ι ≫ g
  naturality a b φ := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
      closedSubspaceDiagram]
    rw [← Category.assoc, Subfunctor.homOfLe_ι]

/-- The projection of the cone of inclusions followed by `closedSubspaceDiagramToConst` is the
inclusion of its vertex followed by `g`. -/
private theorem closedSubspaceCone_π_app_comp {ι : Type u} [Preorder ι]
    {M N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : ι → Subfunctor M)
    (hZ : ∀ ⦃i j : ι⦄, i ≤ j → Z j ≤ Z i) (X : Subfunctor M) (hle : ∀ i, X ≤ Z i) (g : M ⟶ N)
    (a : ιᵒᵖ) :
    (closedSubspaceCone B S hS Z hZ X hle).π.app a ≫
      (closedSubspaceDiagramToConst B S hS Z hZ g).app a = X.ι ≫ g := by
  simp only [closedSubspaceCone, closedSubspaceDiagramToConst]
  rw [← Category.assoc, Subfunctor.homOfLe_ι]

/-- **The claim in the proof of Stacks 0A0W, over an affine base, from Stacks 0A0T.** Let
`q : M ⟶ h_U` be a separated morphism of finite type from a quasi-compact and quasi-separated
algebraic space to the presheaf represented by an affine object `U` of the site, and let `W`
be the intersection of a directed antitone family `(Z_i)` of closed subspaces of `M`. If
`W ⟶ h_U` is proper, then so is some `Z_i ⟶ h_U`.

This is the source's argument. Chow's lemma over `U`
(`AlgebraicGeometry.Space.exists_projectiveSchemeCover_toAffine`) gives a proper surjection
`π : h_V ⟶ M` from a scheme `V` of the site with an immersion `V ⟶ P` into a scheme `P` proper
over `U`. The inverse image of `W` in `V` is proper over `U`, hence proper over `P` (Stacks
04NX), hence a closed subspace of `h_P` (Stacks 04CD); so by Stacks 0A0T, taken without a bound
on the size of the index as in the source, the inverse image of some `Z_i` is a closed subspace
of `h_P`, hence proper over `U`, and `Z_i ⟶ h_U` is proper by Stacks 08AJ since the inverse
image of `Z_i` surjects onto it. -/
theorem exists_isProper_closedSubspace_toAffine
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    {M : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hM : IsAlgebraicSpace B S hS M)
    (hMqc : IsQuasiCompactSpace B S hS M) (hMqs : IsAbsolutelyQuasiSeparated B S hS hZ M)
    (q : M ⟶ yoneda.obj U) (hsep : IsSeparated B S hS q) (hft : IsFiniteType B S hS q)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (Z : I → ClosedSubspaces B S hS M) (hanti : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
    (W : ClosedSubspaces B S hS M) (hle : ∀ i, W.1 ≤ (Z i).1) (hge : (⨅ i, (Z i).1) ≤ W.1)
    (hW : IsProper B S hS (W.1.ι ≫ q))
    (h0A0T : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (c : Cone D) (_ : IsLimit c) (f : c.pt ⟶ Y)
      (_ : c.π ≫ t = (Functor.const Iᵒᵖ).map f),
      IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS c.pt →
      (∀ i, IsAlgebraicSpace B S hS (D.obj (op i))) →
      IsQuasiCompactSpace B S hS Y →
      IsAbsolutelyQuasiSeparated B S hS hZ Y →
      (∀ i, IsQuasiCompactSpace B S hS (D.obj (op i))) →
      (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i))) →
      (∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsClosedImmersion B S hS (D.map φ)) →
      (∀ i, IsLocallyOfFiniteType B S hS (t.app (op i))) →
      IsClosedImmersion B S hS f →
      ∀ᶠ i in atTop, IsClosedImmersion B S hS (t.app (op i))) :
    ∃ i, IsProper B S hS ((Z i).1.ι ≫ q) := by
  classical
  obtain ⟨V, ρ, P, j, p, hρp, hρs, hρq, hj, hp⟩ :=
    exists_projectiveSchemeCover_toAffine B S hS U hU hM q hsep hft
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hPa : IsAlgebraicSpace B S hS (yoneda.obj P) := isAlgebraicSpace_yoneda B S hS P
  have hUa : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  -- the inverse images in `V`
  let Z' : I → ClosedSubspaces B S hS (yoneda.obj V) := fun i =>
    ⟨(Z i).1.preimage ρ, isClosedSubspace_preimage B S hS ρ (Z i).1 hM hV (Z i).2⟩
  let W' : ClosedSubspaces B S hS (yoneda.obj V) :=
    ⟨W.1.preimage ρ, isClosedSubspace_preimage B S hS ρ W.1 hM hV W.2⟩
  have hanti' : ∀ ⦃i j : I⦄, i ≤ j → (Z' j).1 ≤ (Z' i).1 := fun _ _ h T _ hx => hanti h T hx
  have hle' : ∀ i, W'.1 ≤ (Z' i).1 := fun i T _ hx => hle i T hx
  have hge' : (⨅ i, (Z' i).1) ≤ W'.1 := iInf_preimage_le_preimage B S hS _ W.1 ρ hge
  obtain ⟨i₀⟩ := ‹Nonempty I›
  let D := closedSubspaceDiagram B S hS (fun i => (Z' i).1) hanti'
  let t := closedSubspaceDiagramToConst B S hS (fun i => (Z' i).1) hanti' (yoneda.map j)
  let c := closedSubspaceCone B S hS (fun i => (Z' i).1) hanti' W'.1 hle'
  have hc : IsLimit c := isLimitClosedSubspaceCone B S hS i₀ _ hanti' W'.1 hle' hge'
  have hcomm : c.π ≫ t = (Functor.const Iᵒᵖ).map (W'.1.ι ≫ yoneda.map j) := by
    ext a : 2
    exact closedSubspaceCone_π_app_comp B S hS _ hanti' W'.1 hle' _ a
  -- the inverse images of closed subspaces of `M` over their images
  have hjpq : yoneda.map j ≫ yoneda.map p = ρ ≫ q := by rw [hρq, Functor.map_comp]
  have hfrom : ∀ Y : ClosedSubspaces B S hS M,
      IsProper B S hS (Y.1.fromPreimage ρ) ∧ IsSurjective B S hS (Y.1.fromPreimage ρ) := by
    intro Y
    have sq := Subfunctor.isPullback_preimage ρ Y.1
    exact ⟨(isProper_isStableUnderBaseChange B S hS).of_isPullback
        (isPullback_homMk B S hS hV Y.2.1 hM
          (isClosedSubspace_preimage B S hS ρ Y.1 hM hV Y.2).1 sq.flip) hρp,
      surjective_pointsMap_of_isPullback B S hS sq.flip hρs⟩
  have hcompEq : ∀ Y : ClosedSubspaces B S hS M,
      ((Y.1.preimage ρ).ι ≫ yoneda.map j) ≫ yoneda.map p = Y.1.fromPreimage ρ ≫ Y.1.ι ≫ q := by
    intro Y
    rw [Category.assoc, hjpq, ← Category.assoc, ← Subfunctor.fromPreimage_ι, Category.assoc]
  -- the inverse image of `W` is a closed subspace of `h_P`
  have hjimm : IsImmersion B S hS (yoneda.map j) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsImmersion) j).2 hj
  have hpP : IsProper B S hS (yoneda.map p) := isProper_yoneda_map B S hS p hp
  have hWprop : IsProper B S hS (W'.1.ι ≫ yoneda.map j) := by
    refine isProper_of_comp_of_isSeparated B S hS W'.2.1 hPa hUa _ (yoneda.map p) ?_ hpP.1
    rw [hcompEq W]
    exact isProper_comp B S hS W'.2.1 W.2.1 hUa _ _ (hfrom W).1 hW
  have hWclosed : IsClosedImmersion B S hS (W'.1.ι ≫ yoneda.map j) := by
    refine (isClosedImmersion_iff_isClosed_range_pointsMap B S hS hPa _
      (isImmersion_comp B S hS _ _ (isImmersion_of_isClosedImmersion B S hS W'.2.2)
        hjimm)).mpr ?_
    have hcm := isClosed_of_universallyClosed B S hS hPa _ hWprop.2.2
    let := pointTopology B S hS W'.1.toFunctor
    let := pointTopology B S hS (yoneda.obj P)
    exact hcm.isClosed_range
  -- quasi-compactness and quasi-separatedness
  have : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map p) := hp
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj P) :=
    QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map p)
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj P) :=
    quasiSeparatedSpace_of_quasiSeparated ((BigFppfOver.toScheme B S hS).map p)
  obtain ⟨hPqc, hPqs⟩ := isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_yoneda B S hS hZ P
  have hVqc : IsQuasiCompactSpace B S hS (yoneda.obj V) :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hM hMqc hρp.2.1.2
  have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj V) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hV hMqs
      (isQuasiSeparated_of_isSeparated B S hS hρp.1)
  -- Stacks 0A0T
  have hZft : ∀ a, IsFiniteType B S hS ((Z a).1.ι ≫ q) := fun a =>
    isFiniteType_comp B S hS (Z a).2.1 hM hUa _ _
      (isFiniteType_of_isClosedImmersion B S hS _ (Z a).2.2) hft
  have hev := h0A0T D t c hc (W'.1.ι ≫ yoneda.map j) hcomm hPa W'.2.1
    (fun a => (Z' a).2.1) hPqc hPqs
    (fun a => isQuasiCompactSpace_of_isClosedImmersion B S hS hVqc _ (Z' a).2.2)
    (fun a => isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (Z' a).2.1 hVqs
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_isClosedImmersion B S hS _ (Z' a).2.2)))
    (fun φ => isClosedImmersion_closedSubspaceDiagram_map B S hS Z' hanti' φ)
    (fun a => by
      refine isLocallyOfFiniteType_of_comp B S hS (Z' a).2.1 hPa hUa _ (yoneda.map p) ?_
      change IsLocallyOfFiniteType B S hS
        ((((Z a).1.preimage ρ).ι ≫ yoneda.map j) ≫ yoneda.map p)
      rw [hcompEq (Z a)]
      exact (isFiniteType_comp B S hS (Z' a).2.1 (Z a).2.1 hUa _ _ (hfrom (Z a)).1.2.1
        (hZft a)).1)
    hWclosed
  obtain ⟨a, ha⟩ := hev.exists
  refine ⟨a, isProper_of_isSurjective_comp B S hS (Z' a).2.1 (Z a).2.1 hUa
    ((Z a).1.fromPreimage ρ) ((Z a).1.ι ≫ q) ?_ (hfrom (Z a)).2
    (isSeparated_comp B S hS _ _ (isSeparated_of_isClosedImmersion B S hS _ (Z a).2.2) hsep)
    (hZft a)⟩
  rw [← hcompEq (Z a)]
  exact (isProper_comp B S hS (Z' a).2.1 hPa hUa _ _
    (isProper_of_isClosedImmersion B S hS (Z' a).2.1 hPa _ ha) hpP).2.2

/-! ### Stacks 0A0W -/

/-- **The intersection of a limiting antitone family of subfunctors contains the vertex.** If the
cone of inclusions of `X` into an antitone family `(Z_i)` of subfunctors is a limit cone, then
`⋂ Z_i ≤ X`. -/
theorem iInf_le_of_isLimit_closedSubspaceCone {ι : Type u} [Preorder ι] [Nonempty ι]
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : ι → Subfunctor Y)
    (hZ : ∀ ⦃i j : ι⦄, i ≤ j → Z j ≤ Z i) (X : Subfunctor Y) (hle : ∀ i, X ≤ Z i)
    (hc : IsLimit (closedSubspaceCone B S hS Z hZ X hle)) : (⨅ i, Z i) ≤ X := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let c : Cone (closedSubspaceDiagram B S hS Z hZ) :=
    { pt := (⨅ i, Z i).toFunctor
      π := { app := fun i => Subfunctor.homOfLe (iInf_le Z i.unop)
             naturality := fun _ _ _ => rfl } }
  intro T x hx
  let y : (⨅ i, Z i).toFunctor.obj T := ⟨x, hx⟩
  have h : (hc.lift c ≫ X.ι).app T y = ((⨅ i, Z i).ι).app T y := by
    have := congrArg (fun φ => φ ≫ (Z i₀).ι) (hc.fac c (op i₀))
    simp only [c, closedSubspaceCone, Category.assoc, Subfunctor.homOfLe_ι] at this
    rw [this]
  rw [show x = ((hc.lift c).app T y).1 from h.symm]
  exact ((hc.lift c).app T y).2

/-- **Stacks 0A0W, from the staged Stacks 0872 and 0A0U and from Stacks 0A0T.** Let `f : X ⟶ Y`
be a proper morphism of algebraic spaces over `S` with `Y` quasi-compact and quasi-separated. Then
`X = lim X_i` is a directed limit of algebraic spaces `X_i` proper and of finite presentation
over `Y`, with closed immersions as transition morphisms and as projections `X ⟶ X_i`.

The arguments are the inputs of the staged Stacks 0872 and 0A0U and the statement of Stacks 0A0T
(without a bound on the size of the index, as in the source). Stacks 0872 enters through the
staged form
`exists_isFinitePresentation_isClosedImmersion_of_isLocallyOfFiniteType_of_noetherianApproximation`
below, whose one input `h07SU` is passed through. Stacks 0A0U is
`AlgebraicGeometry.Space.hasClosedSubspaceApproximation_of_noetherianApproximation`, from
`h07SU`. Stacks 0873, from these, gives a closed immersion `X ⟶ X'` with `X'` separated and of
finite presentation over `Y`; Stacks 0A0U writes `X = lim X_i` with `X_i ⊆ X'` closed and of
finite presentation; and some `X_i`, hence every later one, is proper over `Y`: after base change
to an affine surjective étale chart of `Y` this is
`AlgebraicGeometry.Space.exists_isProper_closedSubspace_toAffine`, and properness descends along
the chart by Stacks 083R. The system is that of the `X_i` on the
tail above such an index. -/
theorem exists_properApproximation_of_steps
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Z → IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Z)
    (h0A0T : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (c : Cone D) (_ : IsLimit c) (f : c.pt ⟶ Y)
      (_ : c.π ≫ t = (Functor.const Iᵒᵖ).map f),
      IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS c.pt →
      (∀ i, IsAlgebraicSpace B S hS (D.obj (op i))) →
      IsQuasiCompactSpace B S hS Y →
      IsAbsolutelyQuasiSeparated B S hS hZ Y →
      (∀ i, IsQuasiCompactSpace B S hS (D.obj (op i))) →
      (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i))) →
      (∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsClosedImmersion B S hS (D.map φ)) →
      (∀ i, IsLocallyOfFiniteType B S hS (t.app (op i))) →
      IsClosedImmersion B S hS f →
      ∀ᶠ i in atTop, IsClosedImmersion B S hS (t.app (op i))) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
      Nonempty (IsLimit (Cone.mk X π)) ∧ π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        (∀ i, IsAlgebraicSpace B S hS (D.obj (op i))) ∧
        (∀ i, IsProper B S hS (t.app (op i)) ∧ IsFinitePresentation B S hS (t.app (op i))) ∧
        (∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsClosedImmersion B S hS (D.map φ)) ∧
        (∀ i, IsClosedImmersion B S hS (π.app (op i))) := by
  classical
  -- Stacks 0873
  obtain ⟨X', f', i, hX'alg, hf'sep, hf'fp, hi, hif⟩ :=
    exists_isSeparated_isFinitePresentation_closedImmersion_of_steps B S hS hZ f hX hY hf.2.1
      hf.1 hYqc hYqs h07SU h0A0T
  have hX'qc : IsQuasiCompactSpace B S hS X' :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS f' hY hYqc hf'fp
  have hX'qs : IsAbsolutelyQuasiSeparated B S hS hZ X' :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX'alg hYqs hf'fp.2.2
  -- `X` as a closed subspace of `X'`, and Stacks 0A0U
  let Xc : ClosedSubspaces B S hS X' :=
    ⟨Subfunctor.range i, isClosedSubspace_range_of_isClosedImmersion B S hS i hX hi⟩
  have : Mono i := mono_of_isClosedImmersion B S hS i hi
  let e : X ≅ (Subfunctor.range i).toFunctor := asIso (Subfunctor.toRange i)
  have he : e.hom ≫ (Subfunctor.range i).ι = i := Subfunctor.toRange_ι i
  obtain ⟨A⟩ := hasClosedSubspaceApproximation_of_noetherianApproximation B S hS hZ h07SU
    ⟨X', hX'alg⟩ hX'qc hX'qs Xc
  let := A.indexPreorder
  let := A.indexDirected
  have : Nonempty A.index := ⟨A.point⟩
  have hge : (⨅ a, (A.stage a).1) ≤ Xc.1 :=
    iInf_le_of_isLimit_closedSubspaceCone B S hS _ A.stage_antitone Xc.1 A.le_stage A.isLimit
  have hXcf : IsProper B S hS (Xc.1.ι ≫ f') := by
    have hei : e.inv ≫ i = Xc.1.ι := by rw [Iso.inv_comp_eq, he]
    have : Xc.1.ι ≫ f' = e.inv ≫ f := by
      rw [← hei, Category.assoc, hif]
    rw [this]
    exact (isProper_isIso_comp_iff B S hS e.inv f).mpr hf
  -- an affine surjective étale chart of `Y`
  obtain ⟨V, g, hVaff, hgS, hgE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y hY).mp hYqc
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
  obtain ⟨hVqc, hVqs⟩ := isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_yoneda B S hS hZ V
  -- the base change `M = V ×_Y X'` and the inverse images of the subspaces of `X'`
  let M := pullback g f'
  have hM : IsAlgebraicSpace B S hS M := isAlgebraicSpace_pullback B S hS g f' hV hX'alg hY
  have hMqc : IsQuasiCompactSpace B S hS M :=
    isQuasiCompactSpace_pullback B S hS hZ g f' hV hY hVqc hX'qc hYqs
  have hMqs : IsAbsolutelyQuasiSeparated B S hS hZ M :=
    isAbsolutelyQuasiSeparated_pullback B S hS hZ g f' hV hX'alg hY hVqs hX'qs
  have hqsep : IsSeparated B S hS (pullback.fst g f') := isSeparated_pullbackFst B S hS g hf'sep
  have hqft : IsFiniteType B S hS (pullback.fst g f') :=
    ⟨isLocallyOfFiniteType_pullback_fst B S hS hX'alg hY
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf'fp.1) V g,
      isQuasiCompact_pullback_fst_of_snd B S hS f' g
        (isQuasiCompact_pullback_snd_of_isQuasiCompact B S hS hf'fp.2.1 V g)⟩
  let pre : ClosedSubspaces B S hS X' → ClosedSubspaces B S hS M := fun Y' =>
    ⟨Y'.1.preimage (pullback.snd g f'),
      isClosedSubspace_preimage B S hS (pullback.snd g f') Y'.1 hX'alg hM Y'.2⟩
  have hsq : ∀ Y' : ClosedSubspaces B S hS X', IsPullback (Y'.1.fromPreimage (pullback.snd g f'))
      ((pre Y').1.ι ≫ pullback.fst g f') (Y'.1.ι ≫ f') g := fun Y' =>
    (Subfunctor.isPullback_preimage (pullback.snd g f') Y'.1).paste_vert
      (IsPullback.of_hasPullback g f').flip
  -- properness over the chart
  have hWM : IsProper B S hS ((pre Xc).1.ι ≫ pullback.fst g f') :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_homMk B S hS Xc.2.1 hV hY (pre Xc).2.1 (hsq Xc)) hXcf
  obtain ⟨a₀, ha₀⟩ := exists_isProper_closedSubspace_toAffine B S hS hZ V hVaff hM hMqc hMqs
    (pullback.fst g f') hqsep hqft (fun a => pre (A.stage a))
    (fun a b h T x hx => A.stage_antitone h T hx) (pre Xc)
    (fun a T x hx => A.le_stage a T hx)
    (iInf_preimage_le_preimage B S hS _ Xc.1 _ hge)
    hWM h0A0T
  -- properness descends along the chart (Stacks 083R)
  have hprop₀ : IsProper B S hS ((A.stage a₀).1.ι ≫ f') := by
    have h41 := (isProper_tfae B S hS (A.stage a₀).2.1 hY ((A.stage a₀).1.ι ≫ f')).out 4 1
    refine h41.mp ⟨V, g, isSurjective_of_presheafSurjective B S hS g hgS, hgE, ?_⟩
    rw [← (hsq (A.stage a₀)).flip.isoPullback_inv_fst]
    exact (isProper_isIso_comp_iff B S hS _ _).mpr ha₀
  -- the system on the tail above `a₀`
  let J := {a : A.index // a₀ ≤ a}
  have : IsDirected J (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  have : Nonempty J := ⟨⟨a₀, le_rfl⟩⟩
  let Zt : J → ClosedSubspaces B S hS X' := fun a => A.stage a.1
  have hantit : ∀ ⦃a b : J⦄, a ≤ b → (Zt b).1 ≤ (Zt a).1 := fun a b h => A.stage_antitone h
  have hlet : ∀ a : J, Xc.1 ≤ (Zt a).1 := fun a => A.le_stage a.1
  have hget : (⨅ a : J, (Zt a).1) ≤ Xc.1 := by
    refine le_trans (le_iInf fun a => ?_) hge
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a a₀
    exact (iInf_le (fun b : J => (Zt b).1) ⟨c, hbc⟩).trans (A.stage_antitone hac)
  let D := closedSubspaceDiagram B S hS (fun a : J => (Zt a).1) hantit
  let t := closedSubspaceDiagramToConst B S hS (fun a : J => (Zt a).1) hantit f'
  let c₀ := closedSubspaceCone B S hS (fun a : J => (Zt a).1) hantit Xc.1 hlet
  have hc₀ : IsLimit c₀ := isLimitClosedSubspaceCone B S hS ⟨a₀, le_rfl⟩ _ hantit Xc.1 hlet hget
  let π : (Functor.const Jᵒᵖ).obj X ⟶ D :=
    { app := fun a => e.hom ≫ c₀.π.app a
      naturality := fun a b φ => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Category.assoc]
        rw [← c₀.w φ] }
  refine ⟨J, inferInstance, inferInstance, inferInstance, D, t, π, ⟨?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc₀.ofIsoLimit (Cone.ext e.symm (fun a => by simp [π]))
  · ext a : 2
    simp only [NatTrans.comp_app, Functor.const_map_app, π, Category.assoc]
    rw [closedSubspaceCone_π_app_comp, ← Category.assoc, he, hif]
  · exact fun a => (Zt a).2.1
  · intro a
    refine ⟨?_, (isFinitePresentation_comp_iff_of_isClosedImmersion B S hS (Zt a).2.1 hX'alg hY
      _ f' (Zt a).2.2 hf'fp).mpr (A.stage_isFinitePresentation a.1)⟩
    have : (Zt a).1.ι ≫ f' = Subfunctor.homOfLe (A.stage_antitone a.2) ≫
        (A.stage a₀).1.ι ≫ f' := by
      rw [← Category.assoc, Subfunctor.homOfLe_ι]
    change IsProper B S hS ((Zt a).1.ι ≫ f')
    rw [this]
    exact isProper_comp B S hS (Zt a).2.1 (A.stage a₀).2.1 hY _ _
      (isProper_of_isClosedImmersion B S hS (Zt a).2.1 (A.stage a₀).2.1 _
        (isClosedImmersion_homOfLe B S hS (Zt a) _)) hprop₀
  · exact fun φ => isClosedImmersion_closedSubspaceDiagram_map B S hS Zt hantit φ
  · intro a
    change IsClosedImmersion B S hS (e.hom ≫ Subfunctor.homOfLe (hlet a))
    exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS e.hom)
      (isClosedImmersion_homOfLe B S hS Xc _)

/-- **The closed immersion of Stacks 0A0W, from the staged Stacks 0872 and 0A0U and Stacks
0A0T.** A proper morphism `f : X ⟶ Y` of algebraic spaces over `S` with `Y` quasi-compact and
quasi-separated factors as a closed immersion `X ⟶ X'` followed by a morphism `X' ⟶ Y` that is
proper and of finite presentation: any member of the system of
`AlgebraicGeometry.Space.exists_properApproximation_of_steps`. -/
theorem exists_isClosedImmersion_isProper_isFinitePresentation_of_isProper
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Z → IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Z)
    (h0A0T : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y)
      (c : Cone D) (_ : IsLimit c) (f : c.pt ⟶ Y)
      (_ : c.π ≫ t = (Functor.const Iᵒᵖ).map f),
      IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS c.pt →
      (∀ i, IsAlgebraicSpace B S hS (D.obj (op i))) →
      IsQuasiCompactSpace B S hS Y →
      IsAbsolutelyQuasiSeparated B S hS hZ Y →
      (∀ i, IsQuasiCompactSpace B S hS (D.obj (op i))) →
      (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj (op i))) →
      (∀ {a b : Iᵒᵖ} (φ : a ⟶ b), IsClosedImmersion B S hS (D.map φ)) →
      (∀ i, IsLocallyOfFiniteType B S hS (t.app (op i))) →
      IsClosedImmersion B S hS f →
      ∀ᶠ i in atTop, IsClosedImmersion B S hS (t.app (op i))) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : X ⟶ X') (f' : X' ⟶ Y),
      IsAlgebraicSpace B S hS X' ∧ IsClosedImmersion B S hS i ∧ IsProper B S hS f' ∧
        IsFinitePresentation B S hS f' ∧ i ≫ f' = f := by
  obtain ⟨I, _, _, ⟨i₀⟩, D, t, π, _, hπt, hD, hprop, -, hπ⟩ :=
    exists_properApproximation_of_steps B S hS hZ f hX hY hf hYqc hYqs h07SU h0A0T
  exact ⟨D.obj (op i₀), π.app (op i₀), t.app (op i₀), hD i₀, hπ i₀, (hprop i₀).1,
    (hprop i₀).2, by simpa using congrArg (fun φ => φ.app (op i₀)) hπt⟩

end AlgebraicGeometry.Space

end
