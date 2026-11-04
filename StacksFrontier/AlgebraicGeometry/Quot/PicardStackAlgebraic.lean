module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackHomUniverse

/-!
# The Picard stack is algebraic once the stack of coherent sheaves is (towards Stacks 0D04)

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, of finite presentation
and proper. Stacks 0D04 says that `Picardstack_{X/B}` is an algebraic stack. The source's proof
combines three results. Stacks 0D03 says the natural map `Pic_{X/B} ⟶ Coh_{X/B}` is representable
by open immersions. Stacks 05UM says a category with a 1-morphism representable by algebraic
spaces to an algebraic stack is algebraic. Stacks 09DS says `Coh_{X/B}` is algebraic, because
`f` is of finite presentation and, being proper, separated.

Stacks 0D03 is
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_and_isOpenImmersion_picardToCoherent`.
Stacks 05UM is available at every hom universe as
`AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse`.
That version is needed because the two categories have hom types one universe above the
schemes. Stacks 09DS is not in this library.
So this file proves the implication from the algebraicity of `Coh_{X/B}`. It also proves the
staged form of 0D04, which takes the statement of 09DS as the explicit hypothesis `h09DS`.
**Neither carries a tag.** Given 09DS, the staged form is Stacks 0D04.

It also records that both categories are locally small at the universe of the schemes, with no
hypothesis. Their hom types are pairs of a morphism of test schemes and a morphism of
`𝒪`-modules on an algebraic space, and modules on the small étale site of an algebraic space form
a locally small category. So `CategoryTheory.BasedCategory.shrinkHoms` gives small models of
both.

## Main results

* `AlgebraicGeometry.Space.locallySmall_coherentCFG` and
  `AlgebraicGeometry.Space.locallySmall_picardCFG`: the hom types of `Coh_{X/B}` and of
  `Pic_{X/B}` are `u`-small.
* `AlgebraicGeometry.Space.isAlgebraicStack_picardCFG_of_isAlgebraicStack_coherentCFG`: if
  `Coh_{X/B}` is an algebraic stack, so is `Pic_{X/B}`, for `f` flat, of finite presentation and
  proper.
* `AlgebraicGeometry.Space.isAlgebraicStack_picardCFG_of_h09DS`: the staged form of
  Stacks 0D04, taking the statement of Stacks 09DS as a hypothesis.

## References

* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0D03](https://stacks.math.columbia.edu/tag/0D03)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The `𝒪`-module homomorphisms between two modules on an algebraic space form a `u`-small
type: the small étale site is essentially small. -/
theorem small_modules_hom (X : AlgebraicSpaces B S hS) (M N : Modules.{u, u} B S hS X.1 X.2) :
    Small.{u} (M ⟶ N) :=
  (isGrothendieckAbelian_modules B S hS X.1 X.2).locallySmall.hom_small M N

/-- A type injecting into a sigma type of small types over a small base is small. -/
private theorem small_of_injective_sigma {α T : Type*} {G : T → Type*} [Small.{u} T]
    (hG : ∀ b, Small.{u} (G b)) (f : α → Σ b, G b) (hf : Function.Injective f) : Small.{u} α :=
  have (b : T) := hG b
  small_of_injective hf

/-- **The hom types of `Coh_{X/Y}` are `u`-small.** A morphism is a morphism of test schemes over
`Y` together with a morphism of `𝒪`-modules on the base change, and both range over small types. -/
theorem locallySmall_coherentCFG (D : CoherentSituation B S hS) :
    LocallySmall.{u} (coherentCFG D).val.obj where
  hom_small A A' := by
    refine small_of_injective_sigma
      (G := fun b : A.T ⟶ A'.T => (modulePullback B S hS (D.relativeMap b)).obj A'.F ⟶ A.F)
      (fun _ => small_modules_hom _ _ _) (fun m : CoherentHom A A' => ⟨m.base, m.fibre⟩) ?_
    rintro ⟨mb, mf, mi⟩ ⟨nb, nf, ni⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    cases eq_of_heq h
    rfl

/-- **The hom types of `Picardstack_{X/B}` are `u`-small.** A morphism is a morphism of test
schemes over the base together with a morphism of invertible modules on the base change. -/
theorem locallySmall_picardCFG (hc : ModulePushforwardCoherence B S hS)
    (s : PicardSituation B S hS) : LocallySmall.{u} (picardCFG hc s).val.obj where
  hom_small A C := by
    refine small_of_injective_sigma
      (G := fun b : A.T ⟶ C.T =>
        (modulePullback B S hS (baseChangeMap s.f b)).obj C.lineBundle ⟶ A.lineBundle)
      (fun _ => small_modules_hom _ _ _) (fun m : PicardHom A C => ⟨m.base, m.fibre⟩) ?_
    rintro ⟨mb, mf, mi⟩ ⟨nb, nf, ni⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    cases eq_of_heq h
    rfl

/-- **The Picard stack is algebraic once the stack of coherent sheaves is.** For `f : X ⟶ Y`
flat, of finite presentation (the standing data `D` of Situation 08KB) and proper, if
`Coh_{X/Y}` is an algebraic stack then so is `Pic_{X/Y}`. This is the source's proof of
Stacks 0D04 with its input Stacks 09DS left as the hypothesis: Stacks 0D03 makes
`Pic_{X/Y} ⟶ Coh_{X/Y}` representable by algebraic spaces, and Stacks 05UM concludes. -/
theorem isAlgebraicStack_picardCFG_of_isAlgebraicStack_coherentCFG
    (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom)
    (hCoh : Stack.IsAlgebraicStack.{u, w} B S hS (coherentCFG D).val) :
    Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val :=
  Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse B S hS
    (picardToCoherent D hflat hproper)
    (isRepresentableByAlgebraicSpaces_and_isOpenImmersion_picardToCoherent D hflat hproper).1
    hCoh

/-- **Stacks 0D04, staged on Stacks 09DS.** Let `f : X ⟶ Y` be flat, of finite presentation (the
standing data `D` of Situation 08KB) and proper. Then `Picardstack_{X/Y}` is an algebraic stack,
given the statement of Stacks 09DS as the hypothesis `h09DS`: for every morphism of finite
presentation that is separated, the stack of coherent sheaves is algebraic.

This lemma is unregistered: it takes the statement of Stacks 09DS as a hypothesis. A
proper morphism is separated, so `h09DS` applies to `D`. -/
theorem isAlgebraicStack_picardCFG_of_h09DS
    (h09DS : ∀ D' : CoherentSituation B S hS, IsSeparated B S hS D'.f.hom →
      Stack.IsAlgebraicStack.{u, w} B S hS (coherentCFG D').val)
    (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) :
    Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val :=
  isAlgebraicStack_picardCFG_of_isAlgebraicStack_coherentCFG D hflat hproper
    (h09DS D hproper.1)

end AlgebraicGeometry.Space

end
