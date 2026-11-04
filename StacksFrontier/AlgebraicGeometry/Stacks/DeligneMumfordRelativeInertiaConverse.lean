module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.PseudoTorsorProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SectionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordRelativeInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibreShear

/-!
# Stacks 0CL0, parts (4) and (5): the converses, and both parts in full

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Parts (4) and (5) of
**Stacks 0CL0** assert

* **(4)** `π : I_{𝒳/𝒴} ⟶ 𝒳` is unramified `↔` `f` is DM;
* **(5)** `π : I_{𝒳/𝒴} ⟶ 𝒳` is locally quasi-finite `↔` `f` is quasi-DM,

both conditions on `π` in the relative sense of Properties of Stacks, Section 04XB. The notion
`AlgebraicGeometry.Stack.IsRelativelyUnramified` and the two (b) ⇒ (a) halves,
`AlgebraicGeometry.Stack.isRelativelyUnramified_relativeInertiaProjection_of_isDM` and
`AlgebraicGeometry.Stack.isLocallyQuasiFinite_relativeInertiaProjection_of_isQuasiDM`, are in
`StacksFrontier/AlgebraicGeometry/Stacks/DeligneMumfordRelativeInertia.lean`. This file proves the
two (a) ⇒ (b) halves and states both parts with no hypothesis.

## What is proved

Both directions of both parts, with no hypothesis on `f` and none on the property tested.

The direction **(a) ⇒ (b)** is the source's own argument, run at a scheme-valued point
`(x₁, x₂, α)` of `𝒳 ×_𝒴 𝒳` over `U` but with the source's pseudo-torsor replaced by the one
consequence of it that is used. The base change of `Δ_f` at that point is the presheaf
`Isom^α_{𝒳/𝒴}(x₁, x₂)` of the square **Stacks 04XT**, and the base change of `π` along the point
`x₂` of `𝒳` is the relative automorphism presheaf `Isom_{𝒳/𝒴}(x₂, x₂)`, which the hypothesis on
`π` therefore makes unramified (resp. locally quasi-finite) over `U`. The shear
`(m, m') ↦ m'⁻¹ ≫ m` identifies `Isom^α ×_U Isom^α` with `Isom_{𝒳/𝒴}(x₂, x₂) ×_U Isom^α` over
the second factor, so the second projection of the self-fibre-product is a base change of
`Isom_{𝒳/𝒴}(x₂, x₂) ⟶ U` and has the property too; and a morphism of algebraic spaces which is
locally of finite type and whose self-base-change has the property has it itself. The source's
route — a pseudo-torsor (**Stacks 0CPK**) and Groupoids in Spaces, Lemma **0DSK** — needs the
group object of Lemma **06P6** and the representability half of **Stacks 06PP**; the shear needs
neither, and no Isom *space* enters at any point.

The section argument that settles the corresponding direction of part (3) is *not* what is used:
`Δ_{f,2}` is a section of `pr₁`, and unramifiedness and local quasi-finiteness are cancellable in
the first factor (`AlgebraicGeometry.Space.isUnramified_of_comp`, **Stacks 06G6**, and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_comp`, **Stacks 03XN**), so *every* section has
both properties and the hypothesis on `π` would go unused. What the section does contribute is
the last step above, inside
`AlgebraicGeometry.Space.isUnramified_of_isUnramified_pullbackSnd`: the relative diagonal of
`Isom^α ⟶ U` is a section of the projection, hence an open immersion, which is part (2) of
**Stacks 05W1**.

## Main results

* `AlgebraicGeometry.Stack.isDM_of_isRelativelyUnramified_relativeInertiaProjection` and
  `AlgebraicGeometry.Stack.isQuasiDM_of_isLocallyQuasiFinite_relativeInertiaProjection`: the
  (a) ⇒ (b) halves.
* `AlgebraicGeometry.Stack.isRelativelyUnramified_relativeInertiaProjection_iff_isDM_unconditional`
  and, in the same namespace,
  `isLocallyQuasiFinite_relativeInertiaProjection_iff_isQuasiDM_unconditional`: parts (4) and (5),
  with no hypothesis.

## Implementation notes

`AlgebraicGeometry.Stack.IsDM` bundles the representability of `Δ_f` by algebraic spaces as an
existential witness alongside the relative unramifiedness. For algebraic stacks that witness is
a theorem,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks`
(**Stacks 04XS**, part (1)), so it is supplied rather than assumed wherever `IsDM` has to be
produced.

**The two converses, step by step.** Introducing the Section 04XB data `U, Y, hY, F, hF` for
`Δ_f`:

* the hypothesis slot `Nonempty (StacksRepresentableCFG.EquivalenceOver ...)` becomes an
  isomorphism of `F` with `Isom^α_{𝒳/𝒴}(x₁, x₂)` by
  `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.nonempty_equivalenceOver_fst_iff`,
  whose `relVertHomPresheaf` *is* that presheaf;
* `relVertHomPresheaf` is an algebraic space over `U` by
  `AlgebraicGeometry.Stack.isAlgebraicSpace_relVertHomPresheaf_of_isAlgebraicStack` (part (1) of
  **Stacks 04XS**) and locally of finite type by
  `AlgebraicGeometry.Stack.isLocallyOfFiniteType_relVertHomPresheaf_of_isAlgebraicStack`
  (part (2));
* the same two statements at the *diagonal* point `x₂ ⋙ Δ_f`
  (`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.diagPoint`) give the relative
  automorphism presheaf, and the hypothesis on `π` is read there through **Stacks 0457** in the
  reverse form `AlgebraicGeometry.Stack.relativeProperty_of_equivalences_symm`, which turns it
  into the relative property of `pr₁`, followed by
  `AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver`, which identifies the base change
  of `pr₁` along `x₂` with the base change of `Δ_f` along `x₂ ⋙ Δ_f`;
* the shear square is
  `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.arrowIsoPullbackSndShear`;
* the descent along the self-base-change is
  `AlgebraicGeometry.Space.isUnramified_of_isUnramified_pullbackSnd` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/SectionOpenImmersion.lean` and
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isLocallyQuasiFinite_pullbackSnd` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/PseudoTorsorProperties.lean`, the
  second being the whole of **Stacks 0DSK**'s own argument in the locally quasi-finite case apart
  from the single line a torsor is used for;
* passing between the property of the representing space read over `U` and read over `S` is
  Stacks 04SG, in the form `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` and
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`, exactly as in
  `StacksFrontier/AlgebraicGeometry/Stacks/RelativeDiagonalFiniteType.lean`, which runs this same
  shape for local finite type and is the file the two proofs below imitate.

For the record, the pseudo-torsor route is not open in this library in any case: 0CPK's
pseudo-torsor assertion has no declaration, **Stacks 06PP** is formalized only as the sheaf
construction with representability expressly disclaimed, and
`AlgebraicGeometry.Stack.relativeIsomSubfunctor` (**Stacks 0CPJ**) is diagonal-only, so the
relative analogue of part (2) of **Stacks 04YP** would first need a twisted off-diagonal
subfunctor, which does not exist. Nothing below uses the group law
`CategoryTheory.RelativeInertia.composition` (**Stacks 050R**) or its missing group-object
axioms.

The two packaged morphism properties used below are the public
`AlgebraicGeometry.Space.unramifiedMorphismProperty` and
`AlgebraicGeometry.Space.locallyQuasiFiniteProperty`, imported from
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleChartTargetDescent.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiFiniteMorphismProperty.lean`; only the packaging is
used, never a hypothesis on it. Base-change stability of the two, **Stacks 03ZJ** and
**Stacks 03XL**, is proved as `AlgebraicGeometry.Space.isUnramified_isStableUnderBaseChange` and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_isStableUnderBaseChange` and is what carries the
property across the shear square.

## References

* [Stacks Project, Tag 03XN](https://stacks.math.columbia.edu/tag/03XN)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 050R](https://stacks.math.columbia.edu/tag/050R)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 06G6](https://stacks.math.columbia.edu/tag/06G6)
* [Stacks Project, Tag 06P6](https://stacks.math.columbia.edu/tag/06P6)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
* [Stacks Project, Tag 0CPJ](https://stacks.math.columbia.edu/tag/0CPJ)
* [Stacks Project, Tag 0CPK](https://stacks.math.columbia.edu/tag/0CPK)
* [Stacks Project, Tag 0DSK](https://stacks.math.columbia.edu/tag/0DSK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

open CategoryTheory.TwoFibreProductOver.DiagonalFibre
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Inertia

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The morphism property of algebraic spaces over `S` of holding on every étale chart for the
scheme morphism property `Q`. -/
private abbrev etaleChartProperty (Q : MorphismProperty Scheme.{u}) :
    MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ k => Space.HoldsOnEveryEtaleChart B S hS Q k.hom

/-- The common core of the two converses of Stacks 0CL0: if `Q` is stable under base change on
algebraic spaces and descends along the self-base-change of a morphism locally of finite type,
and the relative inertia projection of `f` has `Q` in the relative sense, then so does the
relative diagonal of `f`. -/
private theorem relativeProperty_relativeDiagonal_of_relativeInertiaProjection
    (Q : MorphismProperty Scheme.{u})
    (hBC : ∀ (S' : Scheme.{u}) (hS' : B.Contains S'),
      (etaleChartProperty B S' hS' Q).IsStableUnderBaseChange)
    (hdesc : ∀ {S' : Scheme.{u}} {hS' : B.Contains S'}
      {P V : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B S' hS' P → IsAlgebraicSpace B S' hS' V → ∀ g : P ⟶ V,
      Space.IsLocallyOfFiniteType B S' hS' g → Space.HoldsOnEveryEtaleChart B S' hS' Q
        (pullback.snd g g) → Space.HoldsOnEveryEtaleChart B S' hS' Q g)
    (f : 𝒳 ⟶ 𝒴) (hπ : RelativeProperty B S hS (etaleChartProperty B S hS Q)
      (relativeInertiaProjection B S hS f).hom) :
    RelativeProperty B S hS (etaleChartProperty B S hS Q)
      (relativeDiagonalAlgebraicStacks B S hS f).hom := by
  classical
  have := hBC S hS
  have hpr := @relativeProperty_of_equivalences_symm B S hS _ _ _ _
    (etaleChartProperty B S hS Q)
    (relativeInertiaProjection B S hS f).hom.hom
    (twoFibreProductSquareAlgebraicStacks B S hS
      (relativeDiagonalAlgebraicStacks B S hS f)
      (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom.hom
    (relativeInertiaToSecondRelativeDiagonal B S hS f.hom).hom
    (BasedFunctor.id 𝒳.val.val) (eqToIso rfl)
    (isEquivalence_relativeInertiaToSecondRelativeDiagonal B S hS f.hom)
    (isEquivalence_basedFunctorId B S hS 𝒳.val) hπ
  intro U y hy F hF hE
  have := hBC U.left.1 U.left.2
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
  -- the relative automorphism presheaf has `Q` over `U`
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, u, u + 1} B S hS
    𝒳.val (twoFibreProductAlgebraicStack B S hS f f).val 𝒳.val
    (relativeDiagonalAlgebraicStacks B S hS f).hom
    (relativeDiagonalAlgebraicStacks B S hS f).hom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (relativeDiagonalAlgebraicStacks B S hS f).hom
      (relativeDiagonalAlgebraicStacks B S hS f).hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (relativeDiagonalAlgebraicStacks B S hS f).hom
      (relativeDiagonalAlgebraicStacks B S hS f).hom)
    U (Y₂' y) (h2' hy)
  obtain ⟨e⟩ := (nonempty_equivalenceOver_fst_iff 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids (diagPoint_comp_relProdP hy f.hom.hom.w) f.hom.hom.w
    (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (diagPoint_comp_relProdP hy f.hom.hom.w) f.hom.hom.w)).mpr ⟨Iso.refl _⟩
  have hGS := hpr U (Y₂' y) (h2' hy) _ hG ⟨E.trans e⟩
  have hGU : Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q
      (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids (diagPoint_comp_relProdP hy f.hom.hom.w) f.hom.hom.w)) := by
    have h1 := (prop_algebraicSpaceMap_iff B S hS (etaleChartProperty B S hS Q) U _ hG).mp hGS
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
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := etaleChartProperty B U.left.1 U.left.2 Q) sq' hGU
  have hsnd : Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q
      (pullback.snd
        (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
          𝒳.val.isFiberedInGroupoids hy f.hom.hom.w))
        (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
          𝒳.val.isFiberedInGroupoids hy f.hom.hom.w))) :=
    have : MorphismProperty.RespectsIso
        (fun ⦃F G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u⦄ (k : F ⟶ G) =>
          Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q k) :=
      Space.holdsOnEveryEtaleChart_respectsIso_presheaf B U.left.1 U.left.2 _
    (MorphismProperty.arrow_mk_iso_iff
      (P := fun ⦃F G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u⦄ (k : F ⟶ G) =>
        Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 Q k)
      (arrowIsoPullbackSndShear 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids hy
        f.hom.hom.w)).mpr hsndG
  -- descent along the self-base-change
  have hRU := hdesc hR hT (terminal.from (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids hy f.hom.hom.w))
    (isLocallyOfFiniteType_relVertHomPresheaf_of_isAlgebraicStack B S hS 𝒳.val 𝒴.val
      f.hom 𝒳.2 𝒴.2 U y hy) hsnd
  -- back to the statement of Section 04XB
  obtain ⟨e₀⟩ := (nonempty_equivalenceOver_fst_iff 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids hy f.hom.hom.w F).mp hE
  refine (prop_algebraicSpaceMap_iff B S hS (etaleChartProperty B S hS Q) U F hF).mpr ?_
  refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
    Q F).mpr ?_
  refine Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2 terminalIsTerminal
    (Over.mkIdTerminal.isTerminalObj yoneda (Over.mk (𝟙 (B.obj U.left.2)))) (terminal.from F)
    (Space.toYonedaId B U.left.1 U.left.2 F) ?_
  exact (Space.holdsOnEveryEtaleChart_terminal_iff_of_iso B U.left.1 U.left.2 Q
    (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso e₀)).mp hRU

/-- **Stacks 0CL0, part (4), the direction (a) ⇒ (b).** If the relative inertia projection
`π : I_{𝒳/𝒴} ⟶ 𝒳` is unramified in the sense of Section 04XB then `f` is DM.

At a scheme-valued point `(x₁, x₂, α)` of `𝒳 ×_𝒴 𝒳` over `U` the base change of `Δ_f` is the
presheaf `Isom^α_{𝒳/𝒴}(x₁, x₂)` of **Stacks 04XT**, and the base change of `π` along the point
`x₂` of `𝒳` is the relative automorphism presheaf `Isom_{𝒳/𝒴}(x₂, x₂)`, which is therefore
unramified over `U`. The shear `(m, m') ↦ m'⁻¹ ≫ m` identifies the second projection of
`Isom^α ×_U Isom^α` with the base change of `Isom_{𝒳/𝒴}(x₂, x₂) ⟶ U`
(`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.arrowIsoPullbackSndShear`), so that
projection is unramified; `Isom^α ⟶ U` is locally of finite type by part (2) of **Stacks 04XS**,
and `AlgebraicGeometry.Space.isUnramified_of_isUnramified_pullbackSnd` — part (2) of
**Stacks 05W1** applied to the relative diagonal of `Isom^α ⟶ U`, which is a section of that
projection — concludes. -/
theorem isDM_of_isRelativelyUnramified_relativeInertiaProjection (f : 𝒳 ⟶ 𝒴)
    (hπ : IsRelativelyUnramified B S hS (relativeInertiaProjection B S hS f).hom) :
    IsDM B S hS f :=
  ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f,
    relativeProperty_relativeDiagonal_of_relativeInertiaProjection B S hS
      (@_root_.AlgebraicGeometry.Unramified.{u}) (Space.isUnramified_isStableUnderBaseChange B)
      (fun hP hV g => Space.isUnramified_of_isUnramified_pullbackSnd B _ _ hP hV g) f hπ⟩

/-- **Stacks 0CL0, part (5), the direction (a) ⇒ (b).** The quasi-DM twin of
`AlgebraicGeometry.Stack.isDM_of_isRelativelyUnramified_relativeInertiaProjection`: the same
shear identification, with
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isLocallyQuasiFinite_pullbackSnd` — the generic
half of **Stacks 0DSK** — in place of part (2) of Stacks 05W1. -/
theorem isQuasiDM_of_isLocallyQuasiFinite_relativeInertiaProjection (f : 𝒳 ⟶ 𝒴)
    (hπ : IsLocallyQuasiFinite B S hS (relativeInertiaProjection B S hS f).hom) :
    AlgebraicStacks.IsQuasiDM B S hS f :=
  relativeProperty_relativeDiagonal_of_relativeInertiaProjection B S hS
    (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} ⊓
      @_root_.AlgebraicGeometry.LocallyQuasiFinite.{u})
    (Space.isLocallyQuasiFinite_isStableUnderBaseChange B)
    (fun hP hV g => Space.isLocallyQuasiFinite_of_isLocallyQuasiFinite_pullbackSnd B _ _ hV hP g)
    f hπ

/-- **Stacks 0CL0, part (4).** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, the
relative inertia projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is unramified, in the relative sense of
Properties of Stacks, Section 04XB, exactly when `f` is DM.

The direction (b) ⇒ (a) is
`AlgebraicGeometry.Stack.isRelativelyUnramified_relativeInertiaProjection_of_isDM` and (a) ⇒ (b)
is `AlgebraicGeometry.Stack.isDM_of_isRelativelyUnramified_relativeInertiaProjection`; neither
places any hypothesis on `f`. -/
@[stacks 0CL0 "part (4): the relative inertia projection is unramified iff f is DM, both
  directions and with no hypothesis. The direction (b) implies (a) is Stacks 0457 and 045C at the
  packaged unramified property; the converse needs no pseudo-torsor, being an instance of
  isUnramified_of_isUnramified_pullbackSnd, because the shear identifies the self-fibre-product
  of a fibre of the relative diagonal with the base change of the relative automorphism presheaf
  the inertia projection is tested on"]
theorem isRelativelyUnramified_relativeInertiaProjection_iff_isDM_unconditional
    (f : 𝒳 ⟶ 𝒴) :
    IsRelativelyUnramified B S hS (relativeInertiaProjection B S hS f).hom ↔ IsDM B S hS f :=
  ⟨isDM_of_isRelativelyUnramified_relativeInertiaProjection B S hS f,
    isRelativelyUnramified_relativeInertiaProjection_of_isDM B S hS f⟩

/-- **Stacks 0CL0, part (5).** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, the
relative inertia projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is locally quasi-finite, in the relative sense of
Properties of Stacks, Section 04XB, exactly when `f` is quasi-DM.

The direction (b) ⇒ (a) is
`AlgebraicGeometry.Stack.isLocallyQuasiFinite_relativeInertiaProjection_of_isQuasiDM` and
(a) ⇒ (b) is
`AlgebraicGeometry.Stack.isQuasiDM_of_isLocallyQuasiFinite_relativeInertiaProjection`; neither
places any hypothesis on `f`. This is the part the proof of **Stacks 0DSN** cites. -/
@[stacks 0CL0 "part (5): the relative inertia projection is locally quasi-finite iff f is
  quasi-DM, both directions and with no hypothesis. The direction (b) implies (a) is Stacks 0457
  and 045C at the packaged locally-quasi-finite property; the converse is an instance of
  isLocallyQuasiFinite_of_isLocallyQuasiFinite_pullbackSnd, the generic half of Stacks 0DSK, fed
  by the shear identification rather than by a pseudo-torsor"]
theorem isLocallyQuasiFinite_relativeInertiaProjection_iff_isQuasiDM_unconditional
    (f : 𝒳 ⟶ 𝒴) :
    IsLocallyQuasiFinite B S hS (relativeInertiaProjection B S hS f).hom ↔
      AlgebraicStacks.IsQuasiDM B S hS f :=
  ⟨isQuasiDM_of_isLocallyQuasiFinite_relativeInertiaProjection B S hS f,
    isLocallyQuasiFinite_relativeInertiaProjection_of_isQuasiDM B S hS f⟩

end Inertia

end AlgebraicGeometry.Stack

end
