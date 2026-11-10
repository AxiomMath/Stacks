module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassMap

/-!
# Base change of the fraction of Stacks 0G7Q

Let `g : X' ⟶ X` be a morphism of schemes, let `f : Fin c → Γ(X, 𝒪_X)` be a finite family of
global functions, write `f'ᵢ = g^♯(fᵢ)` for the pulled-back equations, and let `ℱ` be an
`𝒪_X`-module.  The fraction `s / (f₁ ⋯ f_c)` of [Stacks, Tag 0G7Q] is a map

`ℱ ⟶ ℱ_{1 … c}`

from the coefficient module to the top term of the extended alternating Čech complex of
[Stacks, Tag 0G7I].  This file proves that the construction is compatible with pullbacks: the
triangle formed by `g^*` of the fraction for `f`, the base-change comparison
`g^*(ℱ^•) ⟶ (g^*ℱ)^•` of `Stacks.Perfect.CechBaseChange.cplxBaseChange` and the fraction for
`f'` on `g^*ℱ` commutes.  This is the sentence the proof of [Stacks, Tag 0G7U] invokes to pass
from its second diagram to its first.

The content is that the denominator is pulled back to the denominator — `g^♯(f₁ ⋯ f_c)` is
`f'₁ ⋯ f'_c` — together with the fact already available for the numerator, that the comparison
is compatible with the augmentations `ℱ ⟶ j_{U,*}(ℱ|_U)`.

## Main results

* `Stacks.Perfect.CechFractionBaseChange.pullback_map_globalSmul`: inverse image is semilinear
  for multiplication by a global function, i.e. `g^*` of multiplication by `a` is multiplication
  by `g^♯(a)`.
* `Stacks.Perfect.CechFractionBaseChange.restrictedModuleBaseChange_fracFactor`: the fraction in
  one summand of the top Čech term is compatible with base change.
* `Stacks.Perfect.CechFractionBaseChange.cplxBaseChange_comp_fracTermTop`: **the map of
  [Stacks, Tag 0G7Q] is compatible with pullbacks.**

## Implementation notes

Multiplication by a global function is `Stacks.Perfect.FractionClass.globalSmul`, a natural
endomorphism of the identity functor on modules, whose component at a module is
`Stacks.Perfect.FractionClass.smulHom`; the three statements below are about that component,
which is the spelling the fraction is built from.

Semilinearity of the inverse image is deduced from semilinearity of the direct image,
`Stacks.Perfect.FractionClass.smulHom_pushforward`, which is sectionwise and therefore already
available: two maps out of an inverse image agree as soon as their transposes under
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` do, the transpose of `g^*` of
multiplication by `a` is multiplication by `a` followed by the unit (naturality of the unit),
and the transpose of multiplication by `g^♯(a)` becomes the same thing by semilinearity of the
direct image followed by naturality of multiplication by `a`.

The fraction in a summand is characterized by the identity saying that multiplying it back by
the product of the equations is the augmentation, and multiplication by that product is
invertible on the summand; so the compatibility is checked after composing with it, where it
becomes the compatibility of the comparison with the augmentations,
`Stacks.Perfect.CechBaseChange.restrictedModuleBaseChange_augR`.  Moving multiplication by the
pulled-back product across the comparison is naturality of multiplication, and recognizing the
pulled-back product as the inverse image of the product is `map_prod` together with
`pullback_map_globalSmul`.

The number of equations `c` is cased on in the last result, because
`Stacks.Perfect.FractionClass.fracTermTop` is: with no equations the top term is the
coefficient module itself, the fraction is the identity and the comparison is the identity too.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.ExtendedAlternatingCech (restrictedModule)
open Stacks.Perfect.FractionClass (smulHom smulHom_naturality smulHom_pushforward
  isIso_smulHom_equationsProd fracFactor fracFactor_comp_smulHom fracTerm fracTerm_comp_π
  fracTermTop)
open Stacks.Perfect.CechBaseChange (restrictedModuleBaseChange restrictedModuleBaseChange_augR
  prodTermBaseChange prodTermBaseChange_π cplxBaseChange)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechFractionBaseChange

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-! ### Semilinearity of the inverse image -/

/-- **Inverse image is semilinear for multiplication by a global function**: the inverse image
of multiplication by `a ∈ Γ(X, 𝒪_X)` on an `𝒪_X`-module is multiplication by `g^♯(a)` on the
inverse-image module.  Both sides are transposed along
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, where the statement becomes
semilinearity of the direct image. -/
public theorem pullback_map_globalSmul (a : Γ(X, ⊤)) (M : X.Modules) :
    (Scheme.Modules.pullback g).map (smulHom a M) =
      smulHom (g.appTop a) ((Scheme.Modules.pullback g).obj M) := by
  have hL : (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map ((Scheme.Modules.pullback g).map (smulHom a M)) =
      smulHom a M ≫ (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M :=
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality (smulHom a M)).symm
  have hR : (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map
          (smulHom (g.appTop a) ((Scheme.Modules.pullback g).obj M)) =
      smulHom a M ≫ (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M := by
    rw [← smulHom_pushforward g ((Scheme.Modules.pullback g).obj M) a]
    exact (smulHom_naturality a _).symm
  exact ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M
    ((Scheme.Modules.pullback g).obj M)).injective (hL.trans hR.symm)

/-! ### The fraction in one summand of the top Čech term -/

/-- **The fraction `s / (f₁ ⋯ f_c)` in one summand of the top Čech term is compatible with base
change.**  Multiplication by the product of the pulled-back equations is invertible on that
summand, so it is enough to check the identity after composing with it; there it is the
compatibility of the termwise comparison with the augmentations. -/
public theorem restrictedModuleBaseChange_fracFactor {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤))
    (F : X.Modules) (t : CechCochains.OrdIndex (I := Fin (n + 1)) n) :
    (Scheme.Modules.pullback g).map (fracFactor f F t) ≫ restrictedModuleBaseChange g f F n t =
      fracFactor (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) t := by
  have := isIso_smulHom_equationsProd (fun j => g.appTop (f j))
    ((Scheme.Modules.pullback g).obj F) t
  rw [← cancel_mono (smulHom (∏ i, g.appTop (f i))
      (restrictedModule (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) n t)),
    fracFactor_comp_smulHom, show (∏ i, g.appTop (f i)) = g.appTop (∏ i, f i) by rw [map_prod],
    Category.assoc, ← smulHom_naturality (g.appTop (∏ i, f i))
      (restrictedModuleBaseChange g f F n t),
    ← pullback_map_globalSmul g (∏ i, f i) (restrictedModule f F n t), ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, fracFactor_comp_smulHom,
    restrictedModuleBaseChange_augR]

/-! ### The fraction in the top Čech term -/

/-- **The construction of the map used in [Stacks, Tag 0G7Q] is compatible with pullbacks**: the
inverse image of the fraction `s / (f₁ ⋯ f_c)`, followed by the base-change comparison of the
extended alternating Čech complexes, is the fraction for the pulled-back equations on the
inverse-image module.  This is the step the proof of [Stacks, Tag 0G7U] uses to get its first
diagram out of its second. -/
public theorem cplxBaseChange_comp_fracTermTop {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules) :
    (Scheme.Modules.pullback g).map (fracTermTop f F) ≫ (cplxBaseChange g f F).f c =
      fracTermTop (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) := by
  cases c with
  | zero =>
    change (Scheme.Modules.pullback g).map (𝟙 F) ≫
        𝟙 ((Scheme.Modules.pullback g).obj F) = 𝟙 ((Scheme.Modules.pullback g).obj F)
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  | succ p =>
    change (Scheme.Modules.pullback g).map (fracTerm f F) ≫ prodTermBaseChange g f F p =
        fracTerm (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
    refine Limits.Pi.hom_ext _ _ fun t => ?_
    rw [Category.assoc, prodTermBaseChange_π, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, fracTerm_comp_π, fracTerm_comp_π,
      restrictedModuleBaseChange_fracFactor]

end Stacks.Perfect.CechFractionBaseChange

end
