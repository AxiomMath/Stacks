module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalAffine
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Nonvanishing

/-!
# The inverse image of a global section is natural in the module

`Stacks.SheafOfModules.modulePullbackSection` sends a global section of a sheaf of modules `L` on
a locally ringed space `X` to a global section of `f^*L` on `Y`, for `f : Y ⟶ X`.  This file
proves that the construction is **natural in `L`**: a morphism `ψ : L ⟶ L'` carries the inverse
image of `s` to the inverse image of the image of `s`.

The canonical identification `Stacks.AlgebraicGeometry.ModuleLimits.canHom` of an iterated
pullback with the pullback along the composite already has its naturality in the module, as
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_naturality`.  Combining the two gives the
naturality of the composite operation "pull a section back along `q` and read the iterated
pullback as the pullback along the composite", which is the shape in which the two halves of
[Stacks Project, Tag 01Z0] in `StacksFrontier/AlgebraicGeometry/AmpleLimit/Unconditional.lean` are
stated.

## Main results

* `Stacks.SheafOfModules.sections_eq_of_val_top_eq`: two global sections of a sheaf of modules on
  a ringed space that agree over `⊤` are equal.
* `Stacks.SheafOfModules.sectionsMap_modulePullbackSection`: **the naturality**, for a morphism
  of locally ringed spaces.
* `Stacks.SheafOfModules.sectionsMap_pullback_map_modulePullbackSection`: the same for a morphism
  of schemes, spelled with `AlgebraicGeometry.Scheme.Modules.pullback`.
* `Stacks.AlgebraicGeometry.ModuleLimits.sectionsMap_canHom_modulePullbackSection_naturality`:
  the canonical image of a section of `g^*M` in `pi^*M` is natural in `M`.

## References

* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace (structureRingSheaf pullbackUnit pullbackUnit_naturality)

universe u

namespace Stacks.SheafOfModules

/-- **A global section of a sheaf of modules is determined by its value over `⊤`.**  Every open
is below `⊤`, so the value of a section over any open is the restriction of its value over `⊤`. -/
theorem sections_eq_of_val_top_eq {Z : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureRingSheaf Z)) (s t : M.sections)
    (h : s.val (op ⊤) = t.val (op ⊤)) : s = t := by
  ext U
  rw [← PresheafOfModules.sections_property s (homOfLE (le_top : U.unop ≤ ⊤)).op,
    ← PresheafOfModules.sections_property t (homOfLE (le_top : U.unop ≤ ⊤)).op, h]

/-- **The inverse image of a global section is natural in the module.**  For `f : Y ⟶ X` a
morphism of locally ringed spaces and `ψ : L ⟶ L'` a morphism of sheaves of `𝒪_X`-modules, the
image under `f^*ψ` of the inverse image of a global section `s` of `L` is the inverse image of
the image of `s` under `ψ`.

Both sides are determined by their values over `⊤`, where the inverse image of a section is the
image of its value over `⊤` under the unit of `f^* ⊣ f_*`
(`Stacks.SheafOfModules.modulePullbackSection_eval_top`); so this is the naturality of that unit
in the module, `Stacks.RingedSpace.pullbackUnit_naturality`. -/
theorem sectionsMap_modulePullbackSection {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
    {L L' : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)} (ψ : L ⟶ L')
    (s : L.sections) :
    _root_.SheafOfModules.sectionsMap ((modulePullback f.toShHom).map ψ)
        (modulePullbackSection f L s)
      = modulePullbackSection f L' (_root_.SheafOfModules.sectionsMap ψ s) := by
  refine sections_eq_of_val_top_eq _ _ _ ?_
  have e : ∀ (N : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (t : N.sections),
      (modulePullbackSection f N t).val (op ⊤) = pullbackUnit f.toShHom N (op ⊤) (t.val (op ⊤)) :=
    modulePullbackSection_eval_top f
  change PresheafOfModules.Hom.app ((modulePullback f.toShHom).map ψ).val (op ⊤)
      ((modulePullbackSection f L s).val (op ⊤)) = _
  rw [e, e]
  exact pullbackUnit_naturality f.toShHom ψ (op ⊤) (s.val (op ⊤))

/-- **The inverse image of a global section of a module on a scheme is natural in the module**,
spelled with `AlgebraicGeometry.Scheme.Modules.pullback`.  This is
`Stacks.SheafOfModules.sectionsMap_modulePullbackSection` read through the definitional equality
of the two pullback functors. -/
theorem sectionsMap_pullback_map_modulePullbackSection {V W : Scheme.{u}} (q : V ⟶ W)
    {M M' : W.Modules} (ψ : M ⟶ M') (x : M.sections) :
    _root_.SheafOfModules.sectionsMap ((Scheme.Modules.pullback q).map ψ)
        (modulePullbackSection q.toLRSHom M x)
      = modulePullbackSection q.toLRSHom M' (_root_.SheafOfModules.sectionsMap ψ x) :=
  sectionsMap_modulePullbackSection q.toLRSHom ψ x

end Stacks.SheafOfModules

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- **The canonical image of a section is natural in the module.**  For `q ≫ g = pi` and
`ψ : M ⟶ M'` a morphism of modules on the common target, the canonical image in `pi^*M'` of the
image of a section `x` of `g^*M` under `g^*ψ` is the image under `pi^*ψ` of the canonical image of
`x` in `pi^*M`.

This is `Stacks.SheafOfModules.sectionsMap_pullback_map_modulePullbackSection` and
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_naturality`, in that order. -/
theorem sectionsMap_canHom_modulePullbackSection_naturality {V W X : Scheme.{u}} (q : V ⟶ W)
    (g : W ⟶ X) (pi : V ⟶ X) (hpi : q ≫ g = pi) {M M' : X.Modules} (ψ : M ⟶ M')
    (x : ((Scheme.Modules.pullback g).obj M).sections) :
    _root_.SheafOfModules.sectionsMap ((Scheme.Modules.pullback pi).map ψ)
          (_root_.SheafOfModules.sectionsMap (canHom q g pi hpi M)
            (Stacks.SheafOfModules.modulePullbackSection q.toLRSHom _ x))
      = _root_.SheafOfModules.sectionsMap (canHom q g pi hpi M')
          (Stacks.SheafOfModules.modulePullbackSection q.toLRSHom _
            (_root_.SheafOfModules.sectionsMap ((Scheme.Modules.pullback g).map ψ) x)) := by
  refine (_root_.SheafOfModules.sectionsMap_comp _ _ _).symm.trans
    ((congrArg (fun m => _root_.SheafOfModules.sectionsMap m _)
      (canHom_naturality q g pi hpi ψ).symm).trans
    ((_root_.SheafOfModules.sectionsMap_comp _ _ _).trans (congrArg _
      (Stacks.SheafOfModules.sectionsMap_pullback_map_modulePullbackSection q
        ((Scheme.Modules.pullback g).map ψ) x))))

end Stacks.AlgebraicGeometry.ModuleLimits

end
