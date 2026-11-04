module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.ComponentPresheafBaseChange

/-!
# The presheaf of components of a base change, as an isomorphism

Let `eA : 𝒜 ⥤ 𝒮` and `eB : ℬ ⥤ 𝒮` be morphisms of categories fibred in groupoids over `𝒞`, and let
`fst : 𝒜 ×_𝒮 ℬ ⥤ 𝒜` be the first projection of their 2-fibre product. The comparison
`Stacks.Sites.CoverDescent.componentPresheafFstHom : Ψ_𝒜(fst) ⟶ eA^* Ψ_𝒮(eB)` is bijective at
every object (`Stacks.Sites.CoverDescent.bijective_componentPresheafFstHom`), so it is an
isomorphism:

`Ψ_𝒜(fst) ≅ eA^* Ψ_𝒮(eB)`.

For `eB` the 1-morphism `(Sch/V) ⟶ 𝒴` named by an object `y` lying over the scheme `V`, `Ψ_𝒴(eB)`
is the representable presheaf of `y`, so the presheaf `x ↦ Hom_𝒴(eA(x), y)` corepresenting sections
over `y` of a direct image along `eA` is the presheaf of components of the projection
`𝒜 ×_𝒴 (Sch/V) ⟶ 𝒜`. That is how **Stacks 0775** (2) sees the cohomology of the 2-fibre product
`(Sch/V) ×_𝒴 𝒳` inside the cohomology of `𝒳`.

## Main definitions

* `Stacks.Sites.CoverDescent.componentPresheafFstIso`: the isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v

namespace Stacks.Sites.CoverDescent

variable {𝒞 𝒜 ℬ 𝒮 : Type (v + 1)} [Category.{v} 𝒞] [Category.{v} 𝒜] [Category.{v} ℬ]
  [Category.{v} 𝒮] (pA : 𝒜 ⥤ 𝒞) (pB : ℬ ⥤ 𝒞) (pS : 𝒮 ⥤ 𝒞) (eA : 𝒜 ⥤ 𝒮) (eB : ℬ ⥤ 𝒮)

/-- **`Ψ_𝒜(fst) ≅ eA^* Ψ_𝒮(eB)`** for morphisms `eA` and `eB` of categories fibred in groupoids:
the comparison `componentPresheafFstHom` as an isomorphism. -/
def componentPresheafFstIso (hA : pA.IsFiberedInGroupoids) (hB : pB.IsFiberedInGroupoids)
    (hS : pS.IsFiberedInGroupoids) (hpA : eA ⋙ pS = pA) (hpB : eB ⋙ pS = pB) :
    componentPresheaf (TwoFibreProductOver.fst pA pB pS eA eB) ≅ eA.op ⋙ componentPresheaf eB :=
  haveI : IsIso (componentPresheafFstHom pA pB pS eA eB) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (componentPresheafFstHom pA pB pS eA eB)
      fun a => (isIso_iff_bijective _).2
      (bijective_componentPresheafFstHom pA pB pS eA eB hA hB hS hpA hpB a)
  asIso (componentPresheafFstHom pA pB pS eA eB)

end Stacks.Sites.CoverDescent

end
