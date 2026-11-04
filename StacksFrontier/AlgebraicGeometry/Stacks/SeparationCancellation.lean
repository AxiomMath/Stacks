module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.GraphMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyCancel
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties

/-!
# Cancelling the second factor of a composite (Stacks 050M)

Stacks 050M has four assertions. Parts (1) and (2) say that if `g ∘ f` is Deligne–Mumford, resp.
quasi-DM, then so is `f`; parts (3) and (4) say the same for separatedness and
quasi-separatedness, each with the extra hypothesis that the relative diagonal of `g` has the
property in question. All four are proved here.

Parts (1) and (2) are proved by the factorisation `f ≅ Γ_f ≫ pr`, where `Γ_f : 𝒳 ⟶ 𝒳 ×_𝒵 𝒴` is
the graph of `f`
over `𝒵` (**Stacks 050I**) and `pr` is the second projection of the canonical 2-fibre product of
the cospan `(g ∘ f, g)`, which is the base change of `g ∘ f` along `g`. The projection has the
property in question by **Stacks 050F**, and the graph has it because it is representable by
algebraic spaces (Stacks 050I, part (1)) and the relative diagonal of a 1-morphism representable
by algebraic spaces is unramified, resp. locally quasi-finite — which is literally the DM, resp.
quasi-DM, condition of Stacks 04YW. Stacks 050K then composes the two.

The two cases differ only in which criterion for the diagonal of a representable 1-morphism is
used: part (2) uses **Stacks 04YQ**, part (5), which rests on the locally-quasi-finite half of
Stacks 0463; part (1) uses
`AlgebraicGeometry.Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`, which
rests on the unramified half of **Stacks 05W6**. Both read the diagonal as a monomorphism which is
locally of finite type.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_comp`: **Stacks 050M**, part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_comp`: **Stacks 050M**, part (2).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_comp_of_isSeparated_diagonal`:
  **Stacks 050M**, part (3).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_comp_of_isQuasiSeparated_diagonal`:
  **Stacks 050M**, part (4).
* `AlgebraicGeometry.Stack.AlgebraicStacks.prop_relativeDiagonal_cancel`: the argument behind
  parts (3) and (4), uniformly in the property `P` cancelled and in the property `Q` the
  hypothesis on the comparison 1-morphism is stated at.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_isEtale_over_base`: the Deligne–Mumford
  conjunct of **Stacks 0CIR**, read off part (1).

## Implementation notes

`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_iso` and `…isQuasiDM_of_iso` transport the two
conditions along a 2-isomorphism of the 1-morphism. Neither carries a Stacks tag: each is the
invariance statement `AlgebraicGeometry.Stack.isDM_of_equivalence`, resp.
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_equivalence`, at the identity equivalence of
the source, which is vocabulary rather than an assertion of any tag, exactly as those statements
and their siblings are untagged.

Parts (3) and (4) take the source's own route instead, and keep the source's hypothesis on the
relative diagonal of `g`. Reading that hypothesis instead as separatedness, resp.
quasi-separatedness, of `g` itself — which is what `AlgebraicGeometry.Stack.isProper_graph` and
`AlgebraicGeometry.Stack.isQuasiCompact_graph` consume — would be strictly stronger than the
source's, hence a weaker theorem, so no such statement is made. The route factors the relative
diagonal of `g ∘ f` as `Δ_f` followed by the comparison 1-morphism `i` of Stacks 050H, whose
separatedness, resp. quasi-separatedness, is exactly the hypothesis on `Δ_g`; the *cancellation*
of a relative property of Stacks 03YK across that factorisation — the counterpart of
`AlgebraicGeometry.Stack.prop_comp_of_atlasDescent` of **Stacks 045B** — is
`AlgebraicGeometry.Stack.prop_of_comp_of_spaceCancel`, and its space-level inputs are
**Stacks 04NX** part (2) for properness and **Stacks 03KS**/**Stacks 03KR** for quasi-compactness
and quasi-separatedness.

Parts (1) and (2) pass `⊤` for the property `Q`: the hypothesis on the comparison 1-morphism is
vacuous for unramifiedness and local quasi-finiteness, which cancel outright (**Stacks 06G6**,
**Stacks 03XN**), so they do not need `prop_relativeDiagonal_cancel` and are proved by the graph
factorisation above. Quasi-separatedness of Stacks 04YW is a conjunction of two conditions of
Stacks 04XB, so part (4) runs the cancellation twice, once at each, and states both halves in the
one declaration carrying the tag; the hypothesis on `Δ_g` is used by the quasi-compact half
alone.

## References

* [Stacks Project, Tag 03KR](https://stacks.math.columbia.edu/tag/03KR)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03XN](https://stacks.math.columbia.edu/tag/03XN)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
* [Stacks Project, Tag 06G6](https://stacks.math.columbia.edu/tag/06G6)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIR](https://stacks.math.columbia.edu/tag/0CIR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The quasi-DM condition of Stacks 04YW is invariant under a 2-isomorphism of the
1-morphism.** This is
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_equivalence` at the identity based functor
of the common source, the 2-isomorphism of underlying based functors being
`AlgebraicGeometry.Stack.algStackHomHomIso`. -/
theorem isQuasiDM_of_iso {𝒰 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} {q q' : 𝒰 ⟶ 𝒵}
    (e : q ≅ q') (h : IsQuasiDM B S hS q) : IsQuasiDM B S hS q' :=
  isQuasiDM_of_equivalence B S hS q q' (BasedFunctor.id 𝒰.val.val)
    (Stack.algStackHomHomIso B S hS e) Functor.isEquivalence_refl h

/-- **Stacks 050M, part (2).** If a composite `f ≫ g` of 1-morphisms of algebraic stacks over `S`
is quasi-DM, then `f` is quasi-DM.

`f` is 2-isomorphic to the graph of `f` over `𝒵` followed by the second projection of the
canonical 2-fibre product of the cospan `(f ≫ g, g)`
(`AlgebraicGeometry.Stack.graph_snd_iso`). That projection is the base change of `f ≫ g` along
`g`, so it is quasi-DM by Stacks 050F; the graph is representable by algebraic spaces by
Stacks 050I part (1), and the relative diagonal of such a 1-morphism is locally quasi-finite by
Stacks 04YQ part (5), which is the quasi-DM condition on the nose. Stacks 050K composes them. -/
@[stacks 050M "quasi_dm_first"]
theorem isQuasiDM_of_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hfg : IsQuasiDM B S hS (f ≫ g)) :
    IsQuasiDM B S hS f := by
  have hgraph : IsQuasiDM B S hS (Stack.graph B S hS f (f ≫ g) g (Iso.refl _)) :=
    (Stack.isLocallyQuasiFinite_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS _
      (Stack.isRepresentableByAlgebraicSpaces_graph B S hS f (f ≫ g) g (Iso.refl _))).2
  have hproj : IsQuasiDM B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) g).snd :=
    isQuasiDM_baseChange B S hS (f ≫ g) g hfg
  exact isQuasiDM_of_iso B S hS
    (Stack.graph_snd_iso B S hS f (f ≫ g) g (Iso.refl _)).symm
    (isQuasiDM_comp B S hS _ _ hgraph hproj)

/-- **The Deligne–Mumford condition of Stacks 04YW is invariant under a 2-isomorphism of the
1-morphism.** This is `AlgebraicGeometry.Stack.isDM_of_equivalence` at the identity based functor
of the common source, the 2-isomorphism of underlying based functors being
`AlgebraicGeometry.Stack.algStackHomHomIso`. -/
theorem isDM_of_iso {𝒰 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} {q q' : 𝒰 ⟶ 𝒵}
    (e : q ≅ q') (h : Stack.IsDM B S hS q) : Stack.IsDM B S hS q' :=
  Stack.isDM_of_equivalence B S hS q q' (BasedFunctor.id 𝒰.val.val)
    (Stack.algStackHomHomIso B S hS e) Functor.isEquivalence_refl h

/-- **Stacks 050M, part (1).** If a composite `f ≫ g` of 1-morphisms of algebraic stacks over `S`
is Deligne–Mumford, then `f` is Deligne–Mumford.

`f` is 2-isomorphic to the graph of `f` over `𝒵` followed by the second projection of the
canonical 2-fibre product of the cospan `(f ≫ g, g)`
(`AlgebraicGeometry.Stack.graph_snd_iso`). That projection is the base change of `f ≫ g` along
`g`, so it is Deligne–Mumford by Stacks 050F; the graph is representable by algebraic spaces by
Stacks 050I part (1), and a 1-morphism representable by algebraic spaces is Deligne–Mumford
because its relative diagonal is a monomorphism which is locally of finite type, hence unramified
by Stacks 05W6. Stacks 050K composes them. -/
@[stacks 050M "dm_first"]
theorem isDM_of_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hfg : Stack.IsDM B S hS (f ≫ g)) :
    Stack.IsDM B S hS f := by
  have hgraph : Stack.IsDM B S hS (Stack.graph B S hS f (f ≫ g) g (Iso.refl _)) :=
    Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS _
      (Stack.isRepresentableByAlgebraicSpaces_graph B S hS f (f ≫ g) g (Iso.refl _))
  have hproj : Stack.IsDM B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS (f ≫ g) g).snd :=
    isDM_baseChange B S hS (f ≫ g) g hfg
  exact isDM_of_iso B S hS
    (Stack.graph_snd_iso B S hS f (f ≫ g) g (Iso.refl _)).symm
    (isDM_comp B S hS _ _ hgraph hproj)

/-- **The Deligne–Mumford conjunct of Stacks 0CIR.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `𝒵` whose structural 1-morphism `p : 𝒳 ⟶ 𝒵` is étale is Deligne–Mumford.

Being over `𝒵` means `p ≅ f ≫ q`, so `f ≫ q` is Deligne–Mumford because `p` is étale, and
Stacks 050M, part (1), cancels the second factor. -/
@[stacks 0CIR "the Deligne-Mumford conjunct of the conclusion: a morphism between two stacks \
etale over a base is DM. The remaining conjunct of Tag 0CIL, the universal etale-smooth \
diagram condition, is not proved here"]
theorem isDM_of_isEtale_over_base {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒵) (q : 𝒴 ⟶ 𝒵) (η : p ≅ f ≫ q)
    (hp : Stack.IsEtale B S hS p) : Stack.IsDM B S hS f :=
  isDM_of_comp B S hS f q (isDM_of_iso B S hS η hp.1)

variable {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **The separation axioms of Stacks 04YW cancel the second factor of a composite, uniformly in
the properties `P` and `Q`.**

Let `P` and `Q` be properties of morphisms of algebraic spaces over `S`, with `P` stable under
base change and `Q` respecting isomorphisms, and suppose that `P` cancels against `Q`: a
composite `a ≫ b` with `P (a ≫ b)` and `Q b` has `P a`. If the relative diagonal `Δ_{f ≫ g}` of
a composite satisfies the condition of Stacks 04XB for `P`, and the comparison 1-morphism
`i : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳` satisfies it for `Q`, then the relative diagonal `Δ_f` of `f`
satisfies it for `P`.

This is the whole content of **Stacks 050M**: each of the four separation axioms of Stacks 04YW
is "`Δ_f` satisfies the condition of Stacks 04XB for `P`" at one such `P`, the hypothesis on `i`
is supplied from the hypothesis on `Δ_g` by the corresponding clause of **Stacks 050H**. It is
the mirror of `AlgebraicGeometry.Stack.AlgebraicStacks.prop_relativeDiagonal_comp`, which is
Stacks 050K: the factorization `Δ_{f ≫ g} = Δ_f ≫ i` is the same
(`AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal_comp`), and the cancellation step is
`AlgebraicGeometry.Stack.prop_of_comp_of_spaceCancel` in place of
`AlgebraicGeometry.Stack.prop_comp_of_atlasDescent`. -/
theorem prop_relativeDiagonal_cancel
    (P Q : CategoryTheory.MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] [Q.RespectsIso]
    (hcancel : ∀ {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (b : Y ⟶ Z),
      P (a ≫ b) → Q b → P a)
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hPfg : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.obj)
      (_hz : z ⋙ (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.p z
            (CatFiberedInGroupoids.homFunctor
              (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
                𝒵.val (f ≫ g).hom)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    (hQi : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.obj)
      (_hz : z ⋙ (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (twoFibreProduct B S hS f f).val.val.p
            (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.p z
            (CatFiberedInGroupoids.homFunctor (mapBase B S hS f f g).hom))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Q (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ (twoFibreProduct B S hS f f).val.val.obj)
      (_hy : y ⋙ (twoFibreProduct B S hS f f).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (twoFibreProduct B S hS f f).val.val.p y
            (CatFiberedInGroupoids.homFunctor
              (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
                𝒴.val f.hom)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  have hfac : _root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒵.val
        (f ≫ g).hom =
      (AlgebraicStacks.relativeDiagonal B S hS f).hom ≫ (mapBase B S hS f f g).hom := by
    rw [← Bicategory.InducedBicategory.bicategory_comp_hom]
    exact congrArg (fun q => q.hom) (relativeDiagonal_comp B S hS f g)
  have hrepr : IsRepresentableByAlgebraicSpaces B S hS
      ((AlgebraicStacks.relativeDiagonal B S hS f).hom ≫ (mapBase B S hS f f g).hom).hom := by
    rw [← hfac]
    exact isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS (f ≫ g)
  rw [hfac] at hPfg
  exact prop_of_comp_of_spaceCancel B S hS P Q hcancel
    (AlgebraicStacks.relativeDiagonal B S hS f).hom (mapBase B S hS f f g).hom
    (isRepresentableByAlgebraicSpaces_mapBase B S hS f f g) hrepr hPfg hQi

/-- **Stacks 050M, part (3).** If a composite of 1-morphisms of algebraic stacks over `S` is
separated and the relative diagonal `Δ_g` of its second factor is separated in the sense of
Stacks 04XB, then its first factor is separated.

The relative diagonal `Δ_{f ≫ g}` is `Δ_f` followed by the comparison 1-morphism `i`, it is
proper in the sense of Stacks 04XB because `f ≫ g` is separated, `i` is separated because `Δ_g`
is (**Stacks 050H**, part (3)), and properness of morphisms of algebraic spaces over `S` is
inherited by the first factor of a composite that has it whose second factor is separated
(**Stacks 04NX**, part (2)). -/
@[stacks 050M "part (3): a separated composite whose second factor has separated relative \
  diagonal has separated first factor"]
theorem isSeparated_of_comp_of_isSeparated_diagonal (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsSeparated B S hS (f ≫ g))
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒵.val g.hom)) :
    IsSeparated B S hS f := by
  -- The direct instance, so that instance search does not take a route through a locality
  -- instance at the fpqc precoverage, whose second universe it cannot determine.
  have : (Space.separatedProperty B S hS).RespectsIso :=
    (Space.separatedProperty_isStableUnderBaseChange B S hS).respectsIso
  exact prop_relativeDiagonal_cancel B S hS (Space.properProperty B S hS)
    (Space.separatedProperty B S hS)
    (fun {X Y Z} a b hab hb => Space.isProper_of_comp_of_isSeparated B S hS X.property
      Y.property Z.property a.hom b.hom hab hb)
    f g hfg (isSeparated_mapBase B S hS f f g hΔ)

/-- **Stacks 050M, part (4).** If a composite of 1-morphisms of algebraic stacks over `S` is
quasi-separated and the relative diagonal `Δ_g` of its second factor is quasi-separated in the
sense of Stacks 04XB, then its first factor is quasi-separated.

Quasi-separatedness of Stacks 04YW is the conjunction of two conditions of Stacks 04XB on the
relative diagonal — quasi-compactness and quasi-separatedness — and each half cancels the
comparison 1-morphism `i` at its own property. The hypothesis on `i` comes from the one on `Δ_g`
by **Stacks 050H**, part (2), and it is needed only by the quasi-compact half: quasi-compactness
of morphisms of algebraic spaces over `S` cancels against a quasi-separated second factor
(**Stacks 03KS**), while quasi-separatedness cancels outright (**Stacks 03KR**). -/
@[stacks 050M "part (4): a quasi-separated composite whose second factor has quasi-separated \
  relative diagonal has quasi-separated first factor"]
theorem isQuasiSeparated_of_comp_of_isQuasiSeparated_diagonal (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsQuasiSeparated B S hS (f ≫ g))
    (hΔ : Stack.IsQuasiSeparated.{u, u, u + 1} B S hS
      (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒴.val 𝒵.val g.hom)) :
    IsQuasiSeparated B S hS f := by
  have : (Space.quasiSeparatedProperty B S hS).IsStableUnderBaseChange :=
    Space.isQuasiSeparated_isStableUnderBaseChange B S hS
  have : (Space.quasiSeparatedProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨prop_relativeDiagonal_cancel B S hS (Space.quasiCompactProperty B S hS)
      (Space.quasiSeparatedProperty B S hS)
      (fun {X Y Z} a b hab hb => Space.isQuasiCompact_of_comp_of_isQuasiSeparated B S hS
        a.hom b.hom X.property Z.property hab hb)
      f g hfg.1 (isQuasiSeparated_mapBase B S hS f f g hΔ),
    prop_relativeDiagonal_cancel B S hS (Space.quasiSeparatedProperty B S hS) ⊤
      (fun {_X _Y _Z} a b hab _ => Space.isQuasiSeparated_of_comp B S hS a.hom b.hom hab)
      f g hfg.2 (fun _ _ _ _ _ _ => trivial)⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
