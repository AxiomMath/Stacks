module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforwardStalk.Basic

/-!
# The stalk of a finite pushforward is a finite algebra over the stalk of the base

The proof of [Stacks, Tag 0C1L] passes from the morphism `f : X' ⟶ X` to the local algebra
`A = 𝒪_{X, x} ⊂ (f_*𝒪_{X'})_x = B` at a point `x` where `f` fails to be an isomorphism, and
applies [Stacks, Tag 0C1I] to the fibre `B ⧸ m_A B`. That application needs `B` to be a
module-finite `A`-algebra, which is the hypothesis `Module.Finite A B` of
`Stacks.GlueSquishFactor.algEquiv_prod_or_dualNumber_of_minimal`. This file supplies it.

## Main results

* `Stacks.GlueSquishFactor.module_finite_stalk_pushforward` — for a finite morphism `f` and a
  point `x` of the target, `(f_*𝒪_{X'})_x` is a module-finite algebra over `𝒪_{X, x}`.

## Implementation notes

**`B` is a localisation, not a product.** It is tempting to expect
`(f_*𝒪_{X'})_x ≅ ∏_{x' ∈ f⁻¹(x)} 𝒪_{X', x'}` for a finite `f`, by analogy with the fact that
the fibre of a finite morphism is a finite discrete set. That is false, and already false in
the situation of [Stacks, Tag 0C1L]. Take `X'` the affine line over `k` and `f` the glueing of
the two points `0` and `1` of Example [Stacks, Tag 0C1J], and let `x` be the image point. The
opens of `X` containing `x` are the images of the opens of `X'` containing both `0` and `1`, so
`(f_*𝒪_{X'})_x` is the semilocal ring `k[t]_S` with `S = {g : g(0) ≠ 0 ∧ g(1) ≠ 0}`, a subring
of `k(t)` and hence a domain, whereas `𝒪_{X', 0} × 𝒪_{X', 1}` is not. The fibre `f⁻¹(x)` is
indeed two points, but they are not separated by any open of the form `f⁻¹V`, which is all the
colimit computing the stalk can see. What *is* a product of local rings is the fibre
`B ⧸ m_A B`, an artinian ring, and that is the object [Stacks, Tag 0C1I] classifies.

**What the stalk really is.** For an affine — in particular a finite — morphism, the stalk of
`f_*𝒪_{X'}` at a point `x` of an affine open `U` is the localisation of `Γ(X', f⁻¹U)` at the
image of the prime of `Γ(X, U)` corresponding to `x`:
`AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`. That is the correct form of
"the stalk of a pushforward along a finite morphism", and it is already in the library. The
present file is the one consequence of it that [Stacks, Tag 0C1L] needs, obtained by localising
the module-finiteness of `Γ(X, U) ⟶ Γ(X', f⁻¹U)` (`AlgebraicGeometry.IsFinite.finite_app`)
along `Module.Finite.of_isLocalizedModule`; the bridge from the localisation of rings to the
localisation of modules is `isLocalizedModule_iff_isLocalization`.

**The algebra structures.** `𝒪_{X, x}` acts on `(f_*𝒪_{X'})_x` through the map of stalks
induced by `f.c`, and the compatibility of that map with the germ maps out of `Γ(X, U)` —
`TopCat.Presheaf.stalkFunctor_map_germ_apply` — is the scalar tower that lets the localisation
argument run. All four algebra structures are introduced locally rather than as instances,
matching `AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C1I](https://stacks.math.columbia.edu/tag/0C1I)
* [Stacks Project, Tag 0C1J](https://stacks.math.columbia.edu/tag/0C1J)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.GlueSquishFactor

/-- **The stalk of a finite pushforward is module-finite over the stalk of the base.** For a
finite morphism `f : X' ⟶ X` and a point `x` of `X`, the stalk `(f_*𝒪_{X'})_x` is a
module-finite algebra over `𝒪_{X, x}`, the action being through the map of stalks induced by
`f`.

With `A = 𝒪_{X, x}` and `B = (f_*𝒪_{X'})_x` this is the finiteness hypothesis of
`Stacks.GlueSquishFactor.algEquiv_prod_or_dualNumber_of_minimal`, the local algebra of a
minimal step of [Stacks, Tag 0C1L]. Over an affine open `U` around `x` the stalk is the
localisation of `Γ(X', f⁻¹U)` at the prime of `Γ(X, U)` attached to `x`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_pushforwardStalk`), and `Γ(X', f⁻¹U)` is
module-finite over `Γ(X, U)` because `f` is; finiteness survives the localisation. -/
theorem module_finite_stalk_pushforward {X' X : Scheme.{u}} (f : X' ⟶ X) [IsFinite f] (x : X) :
    letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.c).hom.toAlgebra
    Module.Finite (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : Algebra Γ(X, U) Γ(X', f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : Module.Finite Γ(X, U) Γ(X', f ⁻¹ᵁ U) := IsFinite.finite_app f U hU
  let : Algebra Γ(X', f ⁻¹ᵁ U) ((f.base _* X'.presheaf).stalk x) :=
    ((f.base _* X'.presheaf).germ U x hx).hom.toAlgebra
  let : Algebra Γ(X, U) ((f.base _* X'.presheaf).stalk x) :=
    (((f.base _* X'.presheaf).germ U x hx).hom.comp (f.app U).hom).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(X', f ⁻¹ᵁ U) ((f.base _* X'.presheaf).stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk (⟨x, hx⟩ : U)
  let : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.c).hom.toAlgebra
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x)
      ((f.base _* X'.presheaf).stalk x) :=
    IsScalarTower.of_algebraMap_eq fun s =>
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.c s).symm
  have : IsLocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (IsScalarTower.toAlgHom Γ(X, U) Γ(X', f ⁻¹ᵁ U) _).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr (hU.isLocalization_pushforwardStalk f hx)
  exact Module.Finite.of_isLocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (IsScalarTower.toAlgHom Γ(X, U) Γ(X', f ⁻¹ᵁ U) _).toLinearMap

end Stacks.GlueSquishFactor

end
