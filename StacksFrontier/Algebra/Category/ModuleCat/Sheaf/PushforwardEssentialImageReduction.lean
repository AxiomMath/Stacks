module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEssentialImage

/-!
# The essential image of the direct image of modules, given essential surjectivity

Let `i : (Sh(C), O) → (Sh(D), O')` be a morphism of ringed topoi whose structure map
`i^# : O' ⟶ i_*O` is locally surjective, and let `I ⊆ O'` be the sectionwise kernel of `i^#`.
If every sheaf of `i_*O`-modules is a direct image along `i`, then the essential image of
`i_* : Mod(O) ⥤ Mod(O')` is the class of `O'`-modules annihilated by `I`, as in Stacks 08M3.

## Main results

* `Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_essSurj`: the
  essential-image characterization of Stacks 08M3, conditional on essential surjectivity of
  `pushforwardModuleFunctor f O`.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

universe w v u v' u'

namespace Stacks.Sheaves.PushforwardEssentialImage

open Stacks.Sheaves.ToposPushforward

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})]

/-- **The essential image of the direct image of modules, given essential surjectivity over
`f_*O`.** For a morphism of topoi `f` and a locally surjective structure map
`fSharp : O' ⟶ f_*O`, a sheaf of `O'`-modules is in the essential image of the direct image on
modules exactly when the sectionwise kernel of `fSharp` annihilates it — provided every sheaf of
`f_*O`-modules is a direct image. -/
theorem essImage_pushforwardModules_iff_of_essSurj
    {f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))} {O : Sheaf J RingCat.{w}}
    {O' : Sheaf K RingCat.{w}} (fSharp : O' ⟶ pushforwardRingSheaf f O)
    [Sheaf.IsLocallySurjective fSharp]
    (hsurj : ∀ M : SheafOfModules.{w} (pushforwardRingSheaf f O),
      (pushforwardModuleFunctor f O).essImage M)
    (G : SheafOfModules.{w} O') :
    (pushforwardModules f O fSharp).essImage G ↔
      ∀ (X : Dᵒᵖ) (a : O'.obj.obj X), a ∈ RingHom.ker (fSharp.hom.app X).hom →
        ∀ m : G.val.obj X, a • m = 0 := by
  refine ⟨smul_eq_zero_of_essImage_pushforwardModules fSharp, fun hG ↦ ?_⟩
  obtain ⟨M, ⟨e⟩⟩ :=
    Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_of_smul_eq_zero fSharp G hG
  obtain ⟨F, ⟨e'⟩⟩ := hsurj M
  exact ⟨F, ⟨(SheafOfModules.restrictScalars fSharp).mapIso e' ≪≫ e⟩⟩

end Stacks.Sheaves.PushforwardEssentialImage

end
