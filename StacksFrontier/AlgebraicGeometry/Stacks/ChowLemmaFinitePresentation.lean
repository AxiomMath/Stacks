module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkBaseChangeNormalCompletion
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessPresentationToType
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance

/-!
# Chow's lemma for algebraic stacks: the finite presentation step

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism of finite presentation from an algebraic stack to an
algebraic space which is the limit of a Noetherian approximation `Y = lim Y_i` (the conclusion of
Stacks 07SU). This file carries out the paragraph "Assume `𝒳 ⟶ Y` is separated and of finite
presentation" of the proof of Stacks 0CQ8: by Stacks 0CN4 the stack `𝒳` is the base change
`Y ×_{Y_i} 𝒳ᵢ` of a 1-morphism `fᵢ : 𝒳ᵢ ⟶ Y_i` of finite presentation; by Stacks 0CPZ the base
change `Y_{i₀} ×_{Y_i} 𝒳ᵢ ⟶ Y_{i₀}` is separated for some `i₀ ≥ i`; it is of finite type and
`Y_{i₀}` is Noetherian, so the Noetherian case of Chow's lemma applies to it, and the cover
obtained there base changes along `Y ⟶ Y_{i₀}` to one of `f`.

## Main results

* `AlgebraicGeometry.Space.NoetherianApproximation.isQuasiCompactSpace` and
  `AlgebraicGeometry.Space.NoetherianApproximation.isNoetherian`: the stages of a Noetherian
  approximation are quasi-compact, and Noetherian. Both are read off the view of the stage over
  `Spec ℤ`, which is of finite type there, through the lower-shriek extension: quasi-compactness
  and étale-local properties of schemes are unchanged by it.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_hasNoetherianApproximation`: the
  conclusion of Stacks 0CQ8 for separated `f` of finite presentation over a space with a
  Noetherian approximation, from the Noetherian case.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 0CN4](https://stacks.math.columbia.edu/tag/0CN4)
* [Stacks Project, Tag 0CPZ](https://stacks.math.columbia.edu/tag/0CPZ)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space.NoetherianApproximation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The stages of a Noetherian approximation are quasi-compact.** The view of a stage over
`Spec ℤ` is of finite type over it, hence quasi-compact, and quasi-compactness of an algebraic
space is reflected by the lower-shriek extension along `S ⟶ Spec ℤ`. -/
theorem isQuasiCompactSpace (A : NoetherianApproximation B S hS hZ X)
    (j : letI := A.preorder; (A.I)ᵒᵖ) :
    letI := A.preorder
    IsQuasiCompactSpace B S hS (A.diagram.obj j) :=
  isQuasiCompactSpace_of_relocalize B S (⊤_ Scheme.{u}) hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) _
    (isQuasiCompactSpace_of_isFiniteType_terminal B hZ (A.isFiniteTypeOverIntegers j))

/-- **The stages of a Noetherian approximation are Noetherian.** A stage is quasi-compact by
`AlgebraicGeometry.Space.NoetherianApproximation.isQuasiCompactSpace` and quasi-separated by
definition; its view over `Spec ℤ` is of finite type over `Spec ℤ`, hence locally Noetherian, and
an étale-local property of schemes descends along the lower-shriek extension. -/
theorem isNoetherian (A : NoetherianApproximation B S hS hZ X)
    (j : letI := A.preorder; (A.I)ᵒᵖ) :
    letI := A.preorder
    IsNoetherian B S hS hZ (A.diagram.obj j) := by
  let := A.preorder
  exact ⟨A.isQuasiCompactSpace j, A.isAbsolutelyQuasiSeparated j,
    hasEtaleLocalProperty_of_relocalize B S (⊤_ Scheme.{u}) hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) _ (A.isAlgebraicSpace j)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isFiniteType_terminal B hZ
        (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ _ _ (A.isAlgebraicSpace j))
        (A.isFiniteTypeOverIntegers j))⟩

end AlgebraicGeometry.Space.NoetherianApproximation

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The finite presentation step of the proof of Stacks 0CQ8.** Let `Y` be an algebraic space
with a Noetherian approximation `Y = lim Y_i` and `f : 𝒳 ⟶ Y` a separated 1-morphism of finite
presentation. If the conclusion of Chow's lemma holds for every separated 1-morphism of finite
type from an algebraic stack to a Noetherian algebraic space (`hN`), it holds for `f`.

`h0CN4` is the source's statement of Stacks 0CN4, and `h0CPZ` is the source's
statement of Stacks 0CPZ (the latter without the descent of properness, Stacks 08K1, from which
it is proved). Other forms of these statements carry #I < cof cutoff, which the source
does not; this hypothesis is the source's statement.

`hqs` says that an algebraic space which is quasi-separated (Stacks 03BS) is quasi-separated as an
algebraic stack (Stacks 050D, part (8)); it is used once, to see that the finite stage `𝒳ᵢ` of
Stacks 0CN4 is quasi-compact and quasi-separated, as Stacks 0CPZ requires.

The proof is the source's. Stacks 0CN4 writes `𝒳 ≃ Y ×_{Y_i} 𝒳ᵢ` over `Y`; since `f` is
separated, so is `Y ×_{Y_i} 𝒳ᵢ ⟶ Y`, and Stacks 0CPZ, applied to the descent situation of the
approximation with distinguished index `i`, gives `i₀ ≥ i` with `Y_{i₀} ×_{Y_i} 𝒳ᵢ ⟶ Y_{i₀}`
separated. That 1-morphism is of finite presentation, as a base change of `fᵢ` (Stacks 06Q4),
hence of finite type, and `Y_{i₀}` is Noetherian, so `hN` gives a Chow cover of it. Pasting
identifies `Y ×_{Y_i} 𝒳ᵢ` with `Y ×_{Y_{i₀}} (Y_{i₀} ×_{Y_i} 𝒳ᵢ)` (Stacks 003Q), and the cover base
changes along `Y ⟶ Y_{i₀}` to one of `f`. -/
theorem HasChowCover.of_hasNoetherianApproximation
    (h0CN4 : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (_ : IsLimit c)
      (hX : IsAlgebraicSpace B S hS c.pt) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
      (_ : ∀ {i j : I} (f : i ⟶ j), Space.IsAffineHom B S hS (D.map f))
      (_ : ∀ i, Space.IsQuasiCompactSpace B S hS (D.obj i))
      (_ : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B)
        (D.obj i))
      (𝒳 : AlgebraicStacks.{u, w} B S hS)
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS c.pt hX),
      IsFinitePresentation B S hS f →
      ∃ (i : I) (𝒳ᵢ : AlgebraicStacks.{u, w} B S hS)
        (fᵢ : 𝒳ᵢ ⟶ algebraicSpaceStack.{u, w} B S hS (D.obj i) (hD i)),
        IsFinitePresentation B S hS fᵢ ∧
        ∃ e : Bicategory.Equivalence 𝒳 (twoFibreProductSquareAlgebraicStacks B S hS fᵢ
            (algebraicSpaceStackMap.{u, w} B S hS hX (hD i) (c.π.app i))).pt,
          Nonempty (e.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS fᵢ
            (algebraicSpaceStackMap.{u, w} B S hS hX (hD i) (c.π.app i))).snd ≅ f))
    (h0CPZ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : Space.DescentSituation B S hS (BigFppfSite.contains_terminal B) I)
      (𝒳₀ : AlgebraicStacks.{u, w} B S hS)
      (f₀ : 𝒳₀ ⟶ algebraicSpaceStack.{u, w} B S hS (D.system.obj (op D.base))
        (D.algebraicSpace D.base)),
      IsQuasiCompactStack.{u, w} B S hS 𝒳₀.val 𝒳₀.property →
      AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS
        (BigFppfSite.contains_terminal B) 𝒳₀ →
      IsSeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f₀
          (algebraicSpaceStackMap.{u, w} B S hS D.limitAlgebraicSpace (D.algebraicSpace D.base)
            (D.limitCone.π.app (op D.base)))).snd →
      ∃ (i₀ : I) (h₀ : D.base ≤ i₀), ∀ (i : I) (hi : i₀ ≤ i),
        IsSeparated B S hS
          (twoFibreProductSquareAlgebraicStacks B S hS f₀
            (algebraicSpaceStackMap.{u, w} B S hS (D.algebraicSpace i) (D.algebraicSpace D.base)
              (D.system.map (homOfLE (h₀.trans hi)).op))).snd)
    (hN : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsNoetherian B S hS (BigFppfSite.contains_terminal B) Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f → IsFiniteType B S hS f → HasChowCover.{u, w} B S hS hY f)
    (hqs : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B) Y →
      AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS
        (BigFppfSite.contains_terminal B) (algebraicSpaceStack.{u, w} B S hS Y hY))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hA : Space.HasNoetherianApproximation B S hS (BigFppfSite.contains_terminal B) Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hfp : IsFinitePresentation B S hS f) :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨A⟩ := hA
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  have : IsCofiltered (A.I)ᵒᵖ := A.isCofiltered_op
  obtain ⟨i, 𝒳ᵢ, fᵢ, hfᵢ, e, ⟨he⟩⟩ := h0CN4 A.diagram (Cone.mk Y A.π) A.isLimit hY
    A.isAlgebraicSpace (fun g => A.isAffineHom_map g) A.isQuasiCompactSpace
    A.isAbsolutelyQuasiSeparated 𝒳 f hfp
  let D : Space.DescentSituation B S hS (BigFppfSite.contains_terminal B) A.I :=
    { system := A.diagram
      algebraicSpace := fun j => A.isAlgebraicSpace (op j)
      transition_affine := A.isAffineHom_map
      quasiCompact := fun j => A.isQuasiCompactSpace (op j)
      quasiSeparated := fun j => A.isAbsolutelyQuasiSeparated (op j)
      limitCone := Cone.mk Y A.π
      isLimit := A.isLimit
      limitAlgebraicSpace := hY
      base := i.unop }
  -- the 2-fibre product `Y ×_{Y_i} 𝒳ᵢ` and its separatedness
  let P := twoFibreProductSquareAlgebraicStacks B S hS fᵢ
    (algebraicSpaceStackMap.{u, w} B S hS hY (A.isAlgebraicSpace i) (A.π.app i))
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _
  let T : Bicategory.TwoCommSq fᵢ
      (algebraicSpaceStackMap.{u, w} B S hS hY (A.isAlgebraicSpace i) (A.π.app i)) :=
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
          Bicategory.id_whiskerRight, Category.id_comp, Category.comp_id, Category.assoc,
          Iso.inv_hom_id, Bicategory.associator] }
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
      (isQuasiCompactStack_fibredCategory B S hS _ (A.isAlgebraicSpace i)
        (A.isQuasiCompactSpace i) _)
  have h𝒳ᵢqs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS
      (BigFppfSite.contains_terminal B) 𝒳ᵢ :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS _ fᵢ
      (hqs _ (A.isAlgebraicSpace i) (A.isAbsolutelyQuasiSeparated i)) hfᵢ.2.2
  -- Stacks 0CPZ: separatedness at a finite stage `i₀ ≥ i`
  obtain ⟨i₀, h₀, hsep₀⟩ := h0CPZ D 𝒳ᵢ fᵢ h𝒳ᵢqc h𝒳ᵢqs hPsep
  have hY₀ : IsAlgebraicSpace B S hS (A.diagram.obj (op i₀)) := A.isAlgebraicSpace (op i₀)
  let t : A.diagram.obj (op i₀) ⟶ A.diagram.obj i := A.diagram.map (homOfLE h₀).op
  let Sq := twoFibreProductSquareAlgebraicStacks B S hS fᵢ
    (algebraicSpaceStackMap.{u, w} B S hS hY₀ (A.isAlgebraicSpace i) t)
  have hSq : Bicategory.IsTwoFibreProduct Sq :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _
  have h₀cover : HasChowCover.{u, w} B S hS hY₀ Sq.snd :=
    hN _ hY₀ (A.isNoetherian (op i₀)) Sq.pt Sq.snd (hsep₀ i₀ le_rfl)
      (isFiniteType_of_isFinitePresentation B S hS _
        (isFinitePresentation_baseChange B S hS fᵢ _ Sq.swap
          (Bicategory.isTwoFibreProduct_swap hSq) hfᵢ))
  -- pasting: `Y ×_{Y_i} 𝒳ᵢ = Y ×_{Y_{i₀}} (Y_{i₀} ×_{Y_i} 𝒳ᵢ)`
  have hcomp : algebraicSpaceStackMap.{u, w} B S hS hY (A.isAlgebraicSpace i) (A.π.app i) =
      algebraicSpaceStackMap.{u, w} B S hS hY hY₀ (A.π.app (op i₀)) ≫
        algebraicSpaceStackMap.{u, w} B S hS hY₀ (A.isAlgebraicSpace i) t :=
    (congrArg (algebraicSpaceStackMap.{u, w} B S hS hY (A.isAlgebraicSpace i))
      (by simpa using A.π.naturality (homOfLE h₀).op : A.π.app i = A.π.app (op i₀) ≫ t)).trans
      (algebraicSpaceStackMap_comp B S hS hY hY₀ (A.isAlgebraicSpace i) _ t)
  exact HasChowCover.of_equivalence_twoFibreProduct B S hS hY hY₀ (A.π.app (op i₀)) Sq.snd
    (Bicategory.innerSq hSq (P.reindexSnd (eqToIso hcomp)))
    (isTwoFibreProduct_innerSq B S hS hSq (Bicategory.isTwoFibreProduct_reindexSnd _ hP))
    f e he h₀cover

end AlgebraicGeometry.Stack.AlgebraicStacks

end
