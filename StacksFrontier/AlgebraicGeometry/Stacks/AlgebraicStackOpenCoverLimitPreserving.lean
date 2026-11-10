module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackOpenCoverRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingObjectsFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingSetoidRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented

/-!
# An algebraic stack from algebraic restrictions over an open covering, limit preserving case

Let `𝒳` be a stack in groupoids over the big fppf site of `S` with diagonal representable by
algebraic spaces whose structure morphism to `(Sch/S)_fppf` is limit preserving on objects
(Stacks 06CU), for instance because `𝒳` is limit preserving (Stacks 07XL). Let `{U i ⟶ S}` be an
open covering. If every restriction `𝒳 ×_{(Sch/S)_fppf} (Sch/U i)_fppf` (Section 04X4) is an
algebraic stack, and the isomorphism classes of objects of `𝒳` over the spectra of fields of
cardinality at most `size S` are boundedly many, then `𝒳` is an algebraic stack. This is the
paragraph "Choose an affine open covering `S = ⋃ U_i` ... we set `W = ∐ W_i`" of the proof of
Stacks 0DLN, with the finiteness of the atlases `W_i ⟶ S` derived from limit preservation
instead of assumed.

## Main results

* `Stack.locallyOfFinitePresentation_of_isLimitPreservingOnObjects_toTerminalCFG`: a
  scheme `W` of the site whose structure 1-morphism `(Sch/W)_fppf ⟶ (Sch/S)_fppf` is limit
  preserving on objects is locally of finite presentation over `S`.
* `Stack.eq_of_terminalCFG`: two 1-morphisms to `(Sch/S)_fppf` are equal.
* `Stack.locallyOfFinitePresentation_of_isRelativelySmooth_restrictSquare`: a smooth
  1-morphism from `(Sch/W)_fppf` to the restriction of `𝒳` to an open of `S` has `W` locally of
  finite presentation over `S`.
* `Stack.isAlgebraicStack_of_isAlgebraicStack_restrictSquare_openCover`: the assembly, at the
  universes of the site.
* `Stack.isAlgebraicStack_of_isAlgebraicStack_restrictSquare_openCover_largeHoms`:
  the same for a category whose morphisms are not small, such as `Complexes_{X/B}` of Stacks 0DLE,
  through a small model of it.

## Implementation notes

The finiteness argument is the composite

`(Sch/W)_fppf ⟶ 𝒳 ×_{(Sch/S)} (Sch/U) ⟶ 𝒳 ⟶ (Sch/S)_fppf`

of 1-morphisms limit preserving on objects: the atlas because it is smooth (Stacks 04AJ and
Stacks 06CX), the projection because it is the base change (Stacks 06CV) of
`(Sch/U)_fppf ⟶ (Sch/S)_fppf`, which is locally of finite presentation (Stacks 06CX), and the
structure morphism of `𝒳` by hypothesis. Their composite is limit preserving on objects by
Stacks 06CW, and it is the structure 1-morphism of `(Sch/W)_fppf`, any two 1-morphisms to the
final object being equal. Stacks 06CX for that structure 1-morphism, read through the identity
chart of the final object, is local finite presentation of `W ⟶ S` (the form of Stacks 01ZC used
here). Limit preservation in the sense of Stacks 0CMR, and Stacks 0CMY, are not needed.

## References

* [Stacks Project, Tag 04X4](https://stacks.math.columbia.edu/tag/04X4)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CV](https://stacks.math.columbia.edu/tag/06CV)
* [Stacks Project, Tag 06CW](https://stacks.math.columbia.edu/tag/06CW)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A scheme whose structure 1-morphism is limit preserving on objects is locally of finite
presentation.** If `(Sch/W)_fppf ⟶ (Sch/S)_fppf` satisfies the condition of Stacks 06CU, then
`W ⟶ S` is locally of finite presentation.

By Stacks 06CX the structure 1-morphism is locally of finite presentation in the relative sense
of Stacks 03YK; it is the 1-morphism `(Sch/W)_fppf ⟶ (Sch/(S/S))_fppf` induced by `W ⟶ S/S`,
transported along the identification of `(Sch/S)_fppf` with the slice over its final object
(Stacks 0457, `AlgebraicGeometry.Stack.relativeProperty_of_equivalences_symm`), and for a
1-morphism of represented categories the relative property is the property of `yoneda.map` of
the underlying morphism of the site. -/
theorem locallyOfFinitePresentation_of_isLimitPreservingOnObjects_toTerminalCFG
    (W : BigFppfOver B S hS)
    (h : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS W) (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS (schemeFibredCategory B S hS W)))) :
    LocallyOfFinitePresentation (B.inclusion.map W.hom) := by
  have hrep := isRepresentableByAlgebraicSpaces_toTerminalCFG B S hS _
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  have h' := (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS _ _ _ hrep).1 h
  let T : BigFppfOver B S hS := topOver B S hS
  let g : W ⟶ T := homTopOver B S hS W
  let b : (terminalCFG B S hS).val ⥤ᵇ (schemeFibredCategory B S hS T).val :=
    { toFunctor :=
        { obj := fun V => Over.mk (Over.homMk (V := T) V.hom (by simp [T]))
          map := fun k => Over.homMk k (Over.OverMorphism.ext (Over.w k)) }
      w := rfl }
  have : Functor.IsEquivalence b.toFunctor :=
    ((Over.iteratedSliceEquiv T).symm.changeFunctor
      (NatIso.ofComponents (fun _ => Over.isoMk (Over.isoMk (Iso.refl _)))
        : Over.iteratedSliceBackward T ≅ b.toFunctor)).isEquivalence_functor
  have : Functor.IsEquivalence
      (BasedFunctor.id (schemeFibredCategory B S hS W).val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 (Over W)))
  let α : BasedFunctor.comp (BasedFunctor.id (schemeFibredCategory B S hS W).val)
        (schemeFibredCategoryMap B S hS g).hom ≅
      BasedFunctor.comp (toTerminalCFG B S hS (schemeFibredCategory B S hS W)) b := by
    refine BasedNatIso.mkNatIso
      (NatIso.ofComponents (fun x => Over.isoMk (Iso.refl _) ?_) ?_) ?_
    · exact Over.OverMorphism.ext ((Category.id_comp _).trans (Over.w x.hom).symm)
    · intro _ _ k
      exact Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
    · intro x
      refine IsHomLift.of_fac _ _ _ rfl rfl ?_
      change (𝟙 x.left : x.left ⟶ x.left) = 𝟙 x.left ≫ 𝟙 x.left ≫ 𝟙 x.left
      simp
  have hg : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.locallyOfFinitePresentationProperty B S hS) (schemeFibredCategoryMap B S hS g)
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g) :=
    relativeProperty_of_equivalences_symm B S hS
      (Space.locallyOfFinitePresentationProperty B S hS)
      (toTerminalCFG B S hS (schemeFibredCategory B S hS W))
      (schemeFibredCategoryMap B S hS g).hom
      (BasedFunctor.id (schemeFibredCategory B S hS W).val) b α h'
  have hy := (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.locallyOfFinitePresentationProperty B S hS) (schemeFibredCategoryMap B S hS g)
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g)
    (yoneda.obj W) (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS W)
    (isAlgebraicSpace_yoneda B S hS T)
    (PresheafOfCategories.sliceElementsEquivalenceOver W)
    (PresheafOfCategories.sliceElementsEquivalenceOver T)).1 hg
  change Space.IsLocallyOfFinitePresentation B S hS _ at hy
  rw [representingMap_schemeFibredCategoryMap] at hy
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget g).1 hy

/-- **Two 1-morphisms to `(Sch/S)_fppf` are equal**: a 1-morphism to the final category fibred in
groupoids is its source's structure functor. -/
theorem eq_of_terminalCFG {𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f g : 𝒵 ⟶ terminalCFG B S hS) : f = g := by
  rcases f with ⟨⟨F, hF⟩⟩
  rcases g with ⟨⟨G, hG⟩⟩
  have hFG : F = G := hF.trans hG.symm
  subst hFG
  rfl

/-- **An atlas of the restriction of a limit preserving stack to an open of `S` is locally of
finite presentation over `S`.** Let `𝒳` have structure 1-morphism to `(Sch/S)_fppf` limit
preserving on objects, let `U ⟶ S` be locally of finite presentation, and let
`c : (Sch/W)_fppf ⟶ 𝒳 ×_{(Sch/S)} (Sch/U)` be smooth. Then `W ⟶ S` is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_of_isRelativelySmooth_restrictSquare
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)))
    (U : BigFppfOver B S hS) (hU : LocallyOfFinitePresentation (B.inclusion.map U.hom))
    (W : BigFppfOver B S hS)
    (c : schemeFibredCategory B S hS W ⟶ (restrictSquare B S hS 𝒳 U).pt)
    (hc : IsRelativelySmooth B S hS c) :
    LocallyOfFinitePresentation (B.inclusion.map W.hom) := by
  let j := schemeFibredCategoryMap B S hS (homTopOver B S hS U)
  have hj : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS _ _ j :=
    (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS _ _ j
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS _)).2
      (hasRelativeProperty_schemeFibredCategoryMap.{u, u} B S hS
        (Space.locallyOfFinitePresentationProperty B S hS) _
        (Space.isLocallyOfFinitePresentation_yoneda_map B S hS _ hU))
  have hfst : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (restrictSquare B S hS 𝒳 U).pt 𝒳 (restrictSquare B S hS 𝒳 U).fst :=
    BigFppfOver.isLimitPreservingOnObjects_twoFibreProductSquareFst B S hS j
      (toTopOver B S hS 𝒳) hj
  have hcomp := BigFppfOver.isLimitPreservingOnObjects_comp B S hS _ _ _ c
    ((restrictSquare B S hS 𝒳 U).fst ≫
      Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))
    (isLimitPreservingOnObjects_of_isRelativelySmooth B S hS c hc)
    (BigFppfOver.isLimitPreservingOnObjects_comp B S hS _ _ _ _ _ hfst h𝒳)
  rw [eq_of_terminalCFG B S hS (c ≫ (restrictSquare B S hS 𝒳 U).fst ≫
      Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))
    (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS (schemeFibredCategory B S hS W)))]
    at hcomp
  exact locallyOfFinitePresentation_of_isLimitPreservingOnObjects_toTerminalCFG B S hS W hcomp

/-- **Stacks 0DLN, the reduction to an affine base, for a limit preserving stack.** Let `𝒳` be a
stack in groupoids over the big fppf site of `S` with diagonal representable by algebraic spaces
and structure morphism to `(Sch/S)_fppf` limit preserving on objects, and let `U i ⟶ S` be open
immersions covering `S`. If each restriction `𝒳 ×_{(Sch/S)_fppf} (Sch/U i)_fppf` is an algebraic
stack, and the isomorphism classes of objects of `𝒳` over the spectra of fields of cardinality
at most `size S` are bounded by a cardinal below the cutoff of the site, then `𝒳` is an
algebraic stack.

An atlas of each restriction is locally of finite presentation over `S`
(`AlgebraicGeometry.Stack.locallyOfFinitePresentation_of_isRelativelySmooth_restrictSquare`),
hence of finite type, and `AlgebraicGeometry.Stack.isAlgebraicStack_of_restrictSquare_openCover`
applies. -/
theorem isAlgebraicStack_of_isAlgebraicStack_restrictSquare_openCover
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (hstack : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hlim : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)))
    {ι : Type u} (U : ι → BigFppfOver B S hS)
    (hopen : ∀ i, AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (U i).hom))
    (hcover : ∀ s : S, ∃ i, s ∈ Set.range (B.inclusion.map (U i).hom))
    (halg : ∀ i, IsAlgebraicStack.{u, t} B S hS (restrictSquare B S hS 𝒳 (U i)).pt.val)
    (hsize : ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
      ∀ (V : BigFppfOver B S hS) (k : Type u) [Field k], V.left.1 = Spec (.of k) →
        Cardinal.mk k ≤ S.size →
        Cardinal.lift.{u, u + 1} (Cardinal.mk (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber V)))) ≤
          Cardinal.lift.{u + 1, u} κ) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  refine isAlgebraicStack_of_restrictSquare_openCover B S hS hstack hdiag U hopen hcover
    (fun i => ?_) hsize
  obtain ⟨_, _, _, W, a, hrep, ha⟩ := halg i
  have := hopen i
  let c : schemeFibredCategory B S hS W ⟶ (restrictSquare B S hS 𝒳 (U i)).pt :=
    Bicategory.InducedBicategory.mkHom a
  have hc : IsRelativelySmooth B S hS c := ⟨hrep, fun V y hy F hF he => (ha V y hy F hF he).2⟩
  have := locallyOfFinitePresentation_of_isRelativelySmooth_restrictSquare B S hS 𝒳 hlim (U i)
    inferInstance W c hc
  exact ⟨W, c, hc, ⟨hrep, fun V y hy F hF he => (ha V y hy F hF he).1⟩, inferInstance⟩

section LargeHoms

universe v

/-- **`AlgebraicGeometry.Stack.isAlgebraicStack_of_isAlgebraicStack_restrictSquare_openCover` for
a category whose morphisms are not small.** Let `𝒳` be a category fibred in groupoids over the
big fppf site of `S` whose total category has its morphisms in an arbitrary universe, such as
`Complexes_{X/B}` of Stacks 0DLE, a stack with diagonal representable by algebraic spaces which
is limit preserving (Stacks 07XL), and let `𝒴` be a category fibred in groupoids at the universes
of the site equivalent to `𝒳` over the site. If the restrictions
`𝒴 ×_{(Sch/S)_fppf} (Sch/U i)_fppf` to the members of an open covering of `S` are algebraic stacks
and the isomorphism classes of objects of `𝒳` over the spectra of fields of cardinality at most
`size S` are boundedly many, then `𝒳` is an algebraic stack.

The stack condition, the diagonal, limit preservation and the bound on isomorphism classes
transport from `𝒳` to `𝒴` along the equivalence, and algebraicity transports back by Stacks 03YQ
in independent universes. -/
theorem isAlgebraicStack_of_isAlgebraicStack_restrictSquare_openCover_largeHoms
    {𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS)}
    (hfib : 𝒳.p.IsFiberedInGroupoids)
    (hstack : 𝒳.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS (CatFiberedInGroupoids.mk 𝒳 hfib))
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, v} B S hS
      (CatFiberedInGroupoids.mk 𝒳 hfib))
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒴.val.p 𝒳.p)
    {ι : Type u} (U : ι → BigFppfOver B S hS)
    (hopen : ∀ i, AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (U i).hom))
    (hcover : ∀ s : S, ∃ i, s ∈ Set.range (B.inclusion.map (U i).hom))
    (halg : ∀ i, IsAlgebraicStack.{u, t} B S hS (restrictSquare B S hS 𝒴 (U i)).pt.val)
    (hsize : ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
      ∀ (V : BigFppfOver B S hS) (k : Type u) [Field k], V.left.1 = Spec (.of k) →
        Cardinal.mk k ≤ S.size →
        Cardinal.lift.{u, u + 1} (Cardinal.mk (Quotient (isIsomorphicSetoid (𝒳.p.Fiber V)))) ≤
          Cardinal.lift.{u + 1, u} κ) :
    IsAlgebraicStack.{u, w} B S hS 𝒳 := by
  classical
  let E : BasedCategory.Equivalence 𝒳 𝒴.val := e.symm.toBasedEquivalence
  have hfibs : 𝒴.val.p.IsFiberedInGroupoids := 𝒴.2
  have hstack' : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS) :=
    (BasedCategory.isStack_iff_of_equivalence E (BigFppfOver.topology B S hS)).mp hstack
  have h₃ : IsRepresentableFromSchemes B S hS (CatFiberedInGroupoids.mk 𝒳 hfib) :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS _).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS _).mp hdiag)
  have h₃' : IsRepresentableFromSchemes B S hS 𝒴 :=
    isRepresentableFromSchemes_of_equivalenceOver B S hS
      (𝒳 := CatFiberedInGroupoids.mk 𝒳 hfib) (𝒴 := 𝒴) E h₃
  have hdiag' : HasRepresentableDiagonal B S hS 𝒴 :=
    (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).mpr
      ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒴).mpr h₃')
  have hlim' : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒴 :=
    isLimitPreserving_of_equivalenceOver B S hS 𝒴 (CatFiberedInGroupoids.mk 𝒳 hfib) e hlim
  refine isAlgebraicStack_of_equivalenceOver B S hS e
    (isAlgebraicStack_of_isAlgebraicStack_restrictSquare_openCover B S hS hstack' hdiag'
      (isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B S hS 𝒴 hlim')
      U hopen hcover halg ?_)
  obtain ⟨κ, hκ, hbound⟩ := hsize
  refine ⟨κ, hκ, fun V k _ hV hk => (le_trans ?_ (hbound V k hV hk))⟩
  -- the isomorphism classes over `V` of `𝒴` inject into those of `𝒳`
  let G := Functor.fiberFunctorOfCompEq E.inverse.w V
  let H := Functor.fiberFunctorOfCompEq E.functor.w V
  let m : Quotient (isIsomorphicSetoid (𝒴.val.p.Fiber V)) →
      Quotient (isIsomorphicSetoid (𝒳.p.Fiber V)) :=
    Quotient.lift (fun z => Quotient.mk _ (G.obj z)) (fun z₁ z₂ ⟨φ⟩ =>
      Quotient.sound ⟨G.mapIso φ⟩)
  have hm : Function.Injective m := by
    intro c₁ c₂ h
    induction c₁ using Quotient.inductionOn with | h z₁ =>
    induction c₂ using Quotient.inductionOn with | h z₂ =>
    obtain ⟨φ⟩ := Quotient.exact h
    let c₁ : z₁.1 ⟶ E.functor.obj (E.inverse.obj z₁.1) := E.counitIso.inv.app z₁.1
    have hc₁ : 𝒴.val.p.IsHomLift (𝟙 V) c₁ := E.counitIso.inv.isHomLift z₁.2
    let c₂ : E.functor.obj (E.inverse.obj z₂.1) ⟶ z₂.1 := E.counitIso.hom.app z₂.1
    have hc₂ : 𝒴.val.p.IsHomLift (𝟙 V) c₂ := E.counitIso.hom.isHomLift z₂.2
    let c₃ : E.functor.obj (E.inverse.obj z₁.1) ⟶ E.functor.obj (E.inverse.obj z₂.1) :=
      Functor.Fiber.fiberInclusion.map (H.map φ.hom)
    have hc₃ : 𝒴.val.p.IsHomLift (𝟙 V) c₃ := (H.map φ.hom).2
    let ψ : z₁.1 ⟶ z₂.1 := c₁ ≫ c₃ ≫ c₂
    have hψ : 𝒴.val.p.IsHomLift (𝟙 V) ψ := by
      have : 𝒴.val.p.IsHomLift (𝟙 V) (c₃ ≫ c₂) := IsHomLift.comp_lift_id_left 𝒴.val.p (𝟙 V) c₂ c₃
      exact IsHomLift.comp_lift_id_left 𝒴.val.p (𝟙 V) (c₃ ≫ c₂) c₁
    exact Quotient.sound ⟨fiberIsoOfHomLift B S hS 𝒴.val.p hfibs V ψ hψ⟩
  exact Cardinal.lift_le.mpr (Cardinal.mk_le_of_injective hm)

end LargeHoms

end AlgebraicGeometry.Stack

end
