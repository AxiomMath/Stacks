module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized

/-!
# Lower shriek along postcomposition agrees on underlying abelian sheaves

Let `f : T ⟶ S` be a morphism of a category `C`, let `u = Over.map f : C/T ⥤ C/S` be
postcomposition with `f`, and let the two slices carry topologies for which `u` is continuous
and cocontinuous, so that `u` induces a morphism of topoi `g : Sh(C/T) ⟶ Sh(C/S)` whose inverse
image is restriction along `u`. For a sheaf of rings `O` on `C/S` with `O_T = g^{-1} O`, lower
shriek on modules of Stacks 0797 then has the lower shriek of abelian sheaves as its underlying
abelian sheaf.

This is the hypothesis of the Stacks 0798 criterion
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_sliceEquivalence` verified for
postcomposition: the criterion asks every slice functor `Over.post u` of the functor of sites to
be an equivalence, and for `u = Over.map f` the slice of `C/T` at an object `x` and the slice of
`C/S` at `u(x)` are both the slice of `C` at the underlying object `x.left`.

## Main results

* `Stacks.SheafOfModules.isEquivalence_overPost_overMap`: every slice functor of
  postcomposition is an equivalence.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_overMap`: the comparison
  transformation of Stacks 0798 is invertible for postcomposition.
* `Stacks.SheafOfModules.overMapLowerShriekToSheafIso`: the resulting identification
  `g_!^{Ab} ∘ forget ≅ forget ∘ g_!`, stated for the lower shriek of Stacks 0797.

## Implementation notes

That `Over.post (Over.map f)` is an equivalence is proved by cancellation rather than by
exhibiting the functor: composing it with the slice functor of `Over.forget S` gives, on the
nose, the slice functor of `Over.forget T`, because `Over.post` is functorial in the functor
(`CategoryTheory.Over.post_comp`) and `Over.map f ⋙ Over.forget S = Over.forget T`. Both of
those slice functors are iterated-slice equivalences by
`Stacks.SheafOfModules.isEquivalence_overPost_overForget`, so the remaining factor is an
equivalence.

The identification of the two lower shrieks is stated for `Stacks.SheafOfModules.lowerShriek`,
the explicit sheafification-of-a-pushforward model of Stacks 0797, while the comparison
transformation of Stacks 0798 is stated for the abstract left adjoint
`SheafOfModules.pullback`; the two are interchanged by
`Stacks.SheafOfModules.lowerShriekIsoPullback`, the uniqueness isomorphism of a left adjoint.
That crossing is between two spellings of the *module* lower shriek and leaves the abelian side
alone, so it is a single whiskering and not a composite of crossings.

## References

* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory

universe r v v₁ u₁

namespace Stacks.SheafOfModules

/-- Every slice functor of postcomposition `Over.map f : C/T ⥤ C/S` is an equivalence: the
slice of `C/T` at `x` and the slice of `C/S` at `(Over.map f) x` are both the slice of `C` at
`x.left`.

Composing with the slice functor of `Over.forget S` gives the slice functor of `Over.forget T`
on the nose, and those two are iterated-slice equivalences. -/
theorem isEquivalence_overPost_overMap {C : Type u₁} [Category.{v₁} C] {T S : C} (f : T ⟶ S)
    (x : Over T) : (Over.post (X := x) (Over.map f)).IsEquivalence := by
  have : (Over.post (X := (Over.map f).obj x) (Over.forget S)).IsEquivalence :=
    isEquivalence_overPost_overForget S _
  have : (Over.post (X := x) (Over.map f) ⋙
      Over.post (X := (Over.map f).obj x) (Over.forget S)).IsEquivalence := by
    have h : Over.post (X := x) (Over.map f) ⋙
        Over.post (X := (Over.map f).obj x) (Over.forget S) =
        Over.post (X := x) (Over.forget T) := rfl
    rw [h]
    exact isEquivalence_overPost_overForget T x
  exact Functor.isEquivalence_of_comp_right _
    (Over.post (X := (Over.map f).obj x) (Over.forget S))

section OverMap

variable {C : Type u₁} [Category.{v₁} C] {T S : C} (f : T ⟶ S)
  (J : GrothendieckTopology (Over T)) (K : GrothendieckTopology (Over S))
  [(Over.map f).IsContinuous J K] [(Over.map f).IsCocontinuous J K]
  (O : Sheaf K RingCat.{r})
  [UnivLE.{r, v}] [UnivLE.{v₁, v}] [UnivLE.{max u₁ v₁, v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [(PresheafOfModules.pushforward.{v} (F := Over.map f)
    (𝟙 ((Over.map f).op ⋙ O.obj))).IsRightAdjoint]
  [∀ G : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{v}, (Over.map f).op.HasPointwiseLeftKanExtension G]

omit [(Over.map f).IsCocontinuous J K] in
/-- **The Stacks 0798 criterion holds for postcomposition.** The comparison transformation
between lower shriek of the underlying abelian sheaf and the underlying abelian sheaf of lower
shriek on modules is an isomorphism for `u = Over.map f : C/T ⥤ C/S`, the structure morphism of
rings being the identity of `g^{-1} O`. -/
theorem isIso_lowerShriekForgetComparison_overMap :
    IsIso (lowerShriekForgetComparison.{r, v} (Over.map f)
      (structureMap J K (Over.map f) O)) :=
  have : ∀ x : Over T, (Over.post (X := x) (Over.map f)).IsEquivalence :=
    isEquivalence_overPost_overMap f
  isIso_lowerShriekForgetComparison_of_sliceEquivalence J K (Over.map f) O

/-- **Lower shriek along postcomposition agrees on underlying abelian sheaves.** The underlying
abelian sheaf of `g_! M` is the lower shriek of abelian sheaves applied to the underlying
abelian sheaf of `M`, naturally in the sheaf of `g^{-1} O`-modules `M`.

The isomorphism is the comparison transformation of Stacks 0798, invertible by
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_overMap`, read through the uniqueness
isomorphism `Stacks.SheafOfModules.lowerShriekIsoPullback` of the two models of the module lower
shriek. -/
def overMapLowerShriekToSheafIso :
    _root_.SheafOfModules.toSheaf.{v} (inverseImageRing J K (Over.map f) O) ⋙
        (Over.map f).sheafPullback AddCommGrpCat.{v} J K ≅
      lowerShriek.{v} J K (Over.map f) O ⋙ _root_.SheafOfModules.toSheaf.{v} O :=
  haveI := isIso_lowerShriekForgetComparison_overMap f J K O
  asIso (lowerShriekForgetComparison.{r, v} (Over.map f)
      (structureMap J K (Over.map f) O)) ≪≫
    Functor.isoWhiskerRight (lowerShriekIsoPullback.{v} J K (Over.map f) O).symm
      (_root_.SheafOfModules.toSheaf.{v} O)

omit [(PresheafOfModules.pushforward.{v} (F := Over.map f)
    (𝟙 ((Over.map f).op ⋙ O.obj))).IsRightAdjoint]
  [∀ G : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{v}, (Over.map f).op.HasPointwiseLeftKanExtension G] in
/-- **Lower shriek on modules along postcomposition is right exact.** It is a left adjoint, so
it preserves all colimits. -/
theorem preservesFiniteColimits_lowerShriek_overMap :
    Limits.PreservesFiniteColimits (lowerShriek.{v} J K (Over.map f) O) :=
  have := (lowerShriekAdjunction.{v} J K (Over.map f) O).leftAdjoint_preservesColimits
  inferInstance

/-- **Lower shriek on modules along postcomposition is left exact as soon as lower shriek on
abelian sheaves is.** Forgetting the module structure preserves finite limits and reflects
them, and by `Stacks.SheafOfModules.overMapLowerShriekToSheafIso` the underlying abelian sheaf
of the module lower shriek is the abelian lower shriek of the underlying abelian sheaf. -/
theorem preservesFiniteLimits_lowerShriek_overMap
    [Limits.PreservesFiniteLimits
      ((Over.map f).sheafPullback AddCommGrpCat.{v} J K)] :
    Limits.PreservesFiniteLimits (lowerShriek.{v} J K (Over.map f) O) where
  preservesFiniteLimits I _ _ := by
    have : Limits.PreservesLimitsOfShape I
        (_root_.SheafOfModules.toSheaf.{v} (inverseImageRing J K (Over.map f) O) ⋙
          (Over.map f).sheafPullback AddCommGrpCat.{v} J K) :=
      Limits.comp_preservesLimitsOfShape _ _
    have : Limits.PreservesLimitsOfShape I
        (lowerShriek.{v} J K (Over.map f) O ⋙ _root_.SheafOfModules.toSheaf.{v} O) :=
      Limits.preservesLimitsOfShape_of_natIso
        (overMapLowerShriekToSheafIso.{r, v} f J K O)
    exact Limits.preservesLimitsOfShape_of_reflects_of_preserves _
      (_root_.SheafOfModules.toSheaf.{v} O)

end OverMap

end Stacks.SheafOfModules

end
