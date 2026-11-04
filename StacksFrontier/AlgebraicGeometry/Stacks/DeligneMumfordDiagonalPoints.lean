module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordRelativeInertiaConverse

/-!
# DM and quasi-DM read off the diagonal at diagonal points

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. By definition (**Stacks 04YW**) `f`
is DM when its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is unramified, which is tested along every
scheme-valued point `(x₁, x₂, α)` of `𝒳 ×_𝒴 𝒳`. This file proves that it suffices to test along
the *diagonal* points `(x, x, id)`, i.e. along `x ⋙ Δ_f` for scheme-valued points `x` of `𝒳`;
likewise for quasi-DM and local quasi-finiteness.

At a diagonal point the base change of `Δ_f` is the relative automorphism presheaf
`Isom_{𝒳/𝒴}(x, x)`, so the statement is a form of the direction (a) ⇒ (b) of parts (4) and (5)
of **Stacks 0CL0**, in which the relative inertia `I_{𝒳/𝒴} ⟶ 𝒳` is tested along `x` exactly
through that presheaf. The form here is the one in which the hypothesis is visibly local on `𝒳`:
it only ever mentions one object of `𝒳` at a time, never a pair, so it can be checked on the
members of a cover of `𝒳` by open substacks.

## Main definitions

* `AlgebraicGeometry.Stack.HasRelativePropertyAtPoint`: the test of **Stacks 03YK** for a
  property `P` at one scheme-valued point of the target.
* `AlgebraicGeometry.Stack.HasPropertyAtDiagonalPoints`: that test for the relative diagonal of
  `f`, at every diagonal point.

## Main results

* `AlgebraicGeometry.Stack.isDM_of_hasPropertyAtDiagonalPoints`: `f` is DM as soon as its
  relative diagonal is unramified at the diagonal points.
* `AlgebraicGeometry.Stack.isQuasiDM_of_hasPropertyAtDiagonalPoints`: `f` is quasi-DM as soon as
  its relative diagonal is locally quasi-finite at the diagonal points.
* `AlgebraicGeometry.Stack.hasPropertyAtDiagonalPoints_of_isDM` and
  `AlgebraicGeometry.Stack.hasPropertyAtDiagonalPoints_of_isQuasiDM`: the converses, which are
  specializations of the definitions.

## Implementation notes

The two proofs are those of
`AlgebraicGeometry.Stack.isDM_of_isRelativelyUnramified_relativeInertiaProjection` and
`AlgebraicGeometry.Stack.isQuasiDM_of_isLocallyQuasiFinite_relativeInertiaProjection` with the
first step removed: there the hypothesis on the inertia is carried, through **Stacks 0457** and
**Stacks 045C**, to the base change of `Δ_f` at the diagonal point `x₂ ⋙ Δ_f`, and that base
change is exactly what the hypothesis here is about. The rest — the shear identifying
`Isom^α ×_U Isom^α` with a base change of `Isom(x₂, x₂)`, and the descent along the
self-base-change — is unchanged.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

open CategoryTheory.TwoFibreProductOver.DiagonalFibre
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The test of Stacks 03YK at one point.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in
groupoids over the big fppf site of `S` *has `P` at the scheme-valued point `y` of `𝒴` with
values in `U`* when every algebraic space representing the base change of `f` along `y` has
structural morphism with `P`, read as a morphism of algebraic spaces over `S`. The relative
property `AlgebraicGeometry.Stack.HasRelativeProperty` is this at every point. -/
abbrev HasRelativePropertyAtPoint (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj) : Prop :=
  ∀ (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      (presheafOfCategories (F ⋙ typeToCat)).p) →
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))

/-- **The relative diagonal has `P` at the diagonal points.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S`, the relative diagonal `Δ_f` has `P` at every point `x ⋙ Δ_f` of
`𝒳 ×_𝒴 𝒳`, `x` a scheme-valued point of `𝒳`. -/
abbrev HasPropertyAtDiagonalPoints (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS) (x : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj),
    x ⋙ 𝒳.val.val.p = Over.map U.hom →
      HasRelativePropertyAtPoint B S hS P
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) U
        (x ⋙ CatFiberedInGroupoids.homFunctor
          (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom))

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- A DM 1-morphism has unramified relative diagonal at the diagonal points. -/
theorem hasPropertyAtDiagonalPoints_of_isDM (f : 𝒳 ⟶ 𝒴) (hf : IsDM B S hS f) :
    HasPropertyAtDiagonalPoints B S hS (Space.unramifiedMorphismProperty B S hS) f :=
  fun U x hx => hf.2 U _ (by rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p]; exact hx)

/-- A quasi-DM 1-morphism has locally quasi-finite relative diagonal at the diagonal points. -/
theorem hasPropertyAtDiagonalPoints_of_isQuasiDM (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsQuasiDM B S hS f) :
    HasPropertyAtDiagonalPoints B S hS (Space.locallyQuasiFiniteProperty B S hS) f :=
  fun U x hx => hf U _ (by rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p]; exact hx)

/-- The common core of the two diagonal-point criteria: if a property `Q` of schemes, tested on
étale charts, is stable under base change and descends along `pullback.snd g g`, then it holds at
every point of the relative diagonal as soon as it does at the diagonal points. -/
private theorem hasRelativePropertyAtPoint_of_diagonalPoints (Q : MorphismProperty Scheme.{u})
    (hbc : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      MorphismProperty.IsStableUnderBaseChange
        (fun ⦃F G : AlgebraicSpaces B T hT⦄ (k : F ⟶ G) =>
          Space.HoldsOnEveryEtaleChart B T hT Q k.hom))
    (hdesc : ∀ (T : Scheme.{u}) (hT : B.Contains T) {P V : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B T hT P → IsAlgebraicSpace B T hT V → ∀ g : P ⟶ V,
      Space.IsLocallyOfFiniteType B T hT g →
        Space.HoldsOnEveryEtaleChart B T hT Q (pullback.snd g g) →
        Space.HoldsOnEveryEtaleChart B T hT Q g)
    (f : 𝒳 ⟶ 𝒴)
    (h : HasPropertyAtDiagonalPoints B S hS
      (fun _ _ k => Space.HoldsOnEveryEtaleChart B S hS Q k.hom) f)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1} B S hS
        𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
    (hy : y ⋙ (twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1} B S hS
        𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p = Over.map U.hom) :
    HasRelativePropertyAtPoint B S hS (fun _ _ k => Space.HoldsOnEveryEtaleChart B S hS Q k.hom)
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) U y := by
  classical
  intro F hF hE
  have := (hbc S hS).respectsIso
  -- the fibre of the relative diagonal at `y`, and at the diagonal point of its second component
  obtain ⟨A, hA, ⟨eA⟩⟩ := isAlgebraicSpace_relVertHomPresheaf_of_isAlgebraicStack.{u, u, u + 1}
    B S hS 𝒳.val 𝒴.val f.hom 𝒳.2 𝒴.2 U y hy
  obtain ⟨A', hA', ⟨eA'⟩⟩ := isAlgebraicSpace_relVertHomPresheaf_of_isAlgebraicStack.{u, u, u + 1}
    B S hS 𝒳.val 𝒴.val f.hom 𝒳.2 𝒴.2 U (diagPoint y f.hom.hom.w)
    (diagPoint_comp_relProdP hy f.hom.hom.w)
  have hR : IsAlgebraicSpace B U.left.1 U.left.2
      (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids hy
        f.hom.hom.w) :=
    isAlgebraicSpace_of_iso B U.left.1 U.left.2
      (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso eA) hA
  have hG : IsAlgebraicSpace B U.left.1 U.left.2
      (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
        (diagPoint_comp_relProdP hy f.hom.hom.w) f.hom.hom.w) :=
    isAlgebraicSpace_of_iso B U.left.1 U.left.2
      (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso eA') hA'
  have hT : IsAlgebraicSpace B U.left.1 U.left.2
      (⊤_ ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B U.left.1 U.left.2
      (terminalIsTerminal.uniqueUpToIso
        (Over.mkIdTerminal.isTerminalObj yoneda (Over.mk (𝟙 (B.obj U.left.2)))))
      (isAlgebraicSpace_yoneda B U.left.1 U.left.2 (Over.mk (𝟙 (B.obj U.left.2))))
  -- the relative automorphism presheaf is unramified over `U`
  obtain ⟨e⟩ := (nonempty_equivalenceOver_fst_iff 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids (diagPoint_comp_relProdP hy f.hom.hom.w) f.hom.hom.w
    (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (diagPoint_comp_relProdP hy f.hom.hom.w) f.hom.hom.w)).mpr ⟨Iso.refl _⟩
  have hGS := h U (Y₂' y) (h2' hy) _ hG ⟨e⟩
  have hGU : Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q
      (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids (diagPoint_comp_relProdP hy f.hom.hom.w) f.hom.hom.w)) := by
    have h1 := (prop_algebraicSpaceMap_iff B S hS
      (fun _ _ k => Space.HoldsOnEveryEtaleChart B S hS Q k.hom) U
      _ hG).mp hGS
    have h2 := (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
      Q _).mp h1
    exact Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2
      (Over.mkIdTerminal.isTerminalObj yoneda (Over.mk (𝟙 (B.obj U.left.2)))) terminalIsTerminal
      (Space.toYonedaId B U.left.1 U.left.2 _) (terminal.from _) h2
  -- the shear: the self-fibre-product projection is a base change of it
  have hsndG : Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q
      (pullback.snd
        (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
          𝒳.val.isFiberedInGroupoids (diagPoint_comp_relProdP hy f.hom.hom.w) f.hom.hom.w))
        (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
          𝒳.val.isFiberedInGroupoids hy f.hom.hom.w))) := by
    have sq := IsPullback.of_hasPullback
      (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids (diagPoint_comp_relProdP hy f.hom.hom.w) f.hom.hom.w))
      (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids hy f.hom.hom.w))
    have sq' : IsPullback
        (ObjectProperty.homMk (pullback.fst _ _) :
          (⟨pullback _ _, isAlgebraicSpace_pullback B U.left.1 U.left.2 _ _ hG hR hT⟩ :
            AlgebraicSpaces B U.left.1 U.left.2) ⟶ ⟨_, hG⟩)
        (ObjectProperty.homMk (pullback.snd _ _)) (ObjectProperty.homMk (terminal.from _))
        (ObjectProperty.homMk (terminal.from _) : (⟨_, hR⟩ : AlgebraicSpaces B U.left.1 U.left.2) ⟶
          ⟨_, hT⟩) :=
      IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
    exact (hbc _ _).of_isPullback sq' hGU
  have hsnd : Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q
      (pullback.snd
        (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
          𝒳.val.isFiberedInGroupoids hy f.hom.hom.w))
        (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
          𝒳.val.isFiberedInGroupoids hy f.hom.hom.w))) :=
    have : MorphismProperty.RespectsIso
        (fun ⦃F G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u⦄ (k : F ⟶ G) =>
          Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q k) :=
      Space.holdsOnEveryEtaleChart_respectsIso_presheaf B U.left.1 U.left.2 Q
    (MorphismProperty.arrow_mk_iso_iff
      (P := fun ⦃F G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u⦄ (k : F ⟶ G) =>
        Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q k)
      (arrowIsoPullbackSndShear 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids hy
        f.hom.hom.w)).mpr hsndG
  -- descent along the self-base-change
  have hlft := isLocallyOfFiniteType_relVertHomPresheaf_of_isAlgebraicStack B S hS 𝒳.val 𝒴.val
    f.hom 𝒳.2 𝒴.2 U y hy
  have hRU := hdesc _ _ hR hT
    (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids hy f.hom.hom.w)) hlft hsnd
  -- back to the statement of Section 04XB
  obtain ⟨e₀⟩ := (nonempty_equivalenceOver_fst_iff 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids hy f.hom.hom.w F).mp hE
  refine (prop_algebraicSpaceMap_iff B S hS
    (fun _ _ k => Space.HoldsOnEveryEtaleChart B S hS Q k.hom) U F hF).mpr ?_
  refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
    Q F).mpr ?_
  refine Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2 terminalIsTerminal
    (Over.mkIdTerminal.isTerminalObj yoneda (Over.mk (𝟙 (B.obj U.left.2)))) (terminal.from F)
    (Space.toYonedaId B U.left.1 U.left.2 F) ?_
  exact (Space.holdsOnEveryEtaleChart_terminal_iff_of_iso B U.left.1 U.left.2
    Q
    (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso e₀)).mp hRU

/-- **DM from the diagonal points.** A 1-morphism of algebraic stacks over `S` whose relative
diagonal is unramified at every diagonal point is DM.

This is the argument of
`AlgebraicGeometry.Stack.isDM_of_isRelativelyUnramified_relativeInertiaProjection` from the point
where the relative automorphism presheaf has been shown to be unramified. -/
theorem isDM_of_hasPropertyAtDiagonalPoints (f : 𝒳 ⟶ 𝒴)
    (h : HasPropertyAtDiagonalPoints B S hS (Space.unramifiedMorphismProperty B S hS) f) :
    IsDM B S hS f :=
  ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f,
    hasRelativePropertyAtPoint_of_diagonalPoints B S hS _
      (fun T hT => Space.isUnramified_isStableUnderBaseChange B T hT)
      (fun T hT _ _ hP hV g hft hsnd =>
        Space.isUnramified_of_isUnramified_pullbackSnd B T hT hP hV g hft hsnd) f h⟩

/-- **Quasi-DM from the diagonal points.** A 1-morphism of algebraic stacks over `S` whose
relative diagonal is locally quasi-finite at every diagonal point is quasi-DM. -/
theorem isQuasiDM_of_hasPropertyAtDiagonalPoints (f : 𝒳 ⟶ 𝒴)
    (h : HasPropertyAtDiagonalPoints B S hS (Space.locallyQuasiFiniteProperty B S hS) f) :
    AlgebraicStacks.IsQuasiDM B S hS f :=
  fun U y hy => hasRelativePropertyAtPoint_of_diagonalPoints B S hS _
    (fun T hT => Space.isLocallyQuasiFinite_isStableUnderBaseChange B T hT)
    (fun T hT _ _ hP hV g hft hsnd =>
      Space.isLocallyQuasiFinite_of_isLocallyQuasiFinite_pullbackSnd B T hT hV hP g hft hsnd)
    f h U y hy

end AlgebraicGeometry.Stack

end
