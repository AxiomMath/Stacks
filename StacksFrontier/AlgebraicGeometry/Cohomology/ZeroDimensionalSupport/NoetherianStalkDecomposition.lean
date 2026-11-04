module

public import Mathlib.RingTheory.Length
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.ZeroDimensionalSupport
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing

/-!
# The stalk decomposition of the global sections, without properness over a field

Let `X` be a locally Noetherian scheme and `ℱ` a coherent `𝒪_X`-module whose support has
topological Krull dimension at most zero. Then the germ maps assemble into an isomorphism

`Γ(X, ℱ) ≅ ∏_{x ∈ Supp ℱ} ℱ_x`,

and when the support is moreover finite the length of `Γ(X, ℱ)` over a ring acting through
`Γ(X, 𝒪_X)` is the sum of the lengths of the stalks over that ring.

## Main results

* `AlgebraicGeometry.bijective_suppGermHom_of_isLocallyNoetherian` — the germ map onto the
  product of the stalks along the support is bijective.
* `AlgebraicGeometry.suppStalkPiAddEquivOfIsLocallyNoetherian` — the same, read as an
  isomorphism of additive groups.
* `AlgebraicGeometry.suppGermLinearMap` — the same germ map, read as a linear map over a base
  ring acting through `Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.length_globalSections_eq_sum_length_stalk` —
  `length_A Γ(X, ℱ) = ∑_{x ∈ T} length_A ℱ_x` for `T` a finite set equal to the support.

## Implementation notes

Both halves of the bijection are already proved in
`StacksFrontier/AlgebraicGeometry/Cohomology/ZeroDimensionalSupport/Vanishing.lean`, and both are
proved there for an arbitrary `X.Modules`: `AlgebraicGeometry.injective_suppGermHom` with no
hypothesis at all, and `AlgebraicGeometry.surjective_suppGermHom` from the support being closed
and each of its points isolated in it. What is new here is the discharge of those two hypotheses
from local Noetherianness and coherence, and the reading of the resulting bijection in lengths.
Closedness is `SheafOfModules.isClosed_supp` for a module of finite type, and the isolating open
is `AlgebraicGeometry.exists_open_neighborhood_meets_support_singleton`, which takes exactly
`[IsLocallyNoetherian X]`, `[ℱ.IsCoherent]` and the dimension bound.

The point of stating it this way is the hypotheses that are *absent*. The library's form of the
decomposition, `AlgebraicGeometry.suppStalkPiAddEquiv`, carries a proper morphism to the
spectrum of a field, which it uses only to make the scheme-theoretic support compact — that is,
to make the support *finite*, which the bijection itself does not need. Several consumers have a
locally Noetherian scheme and a finite support in hand but no field below: the blowup of a
two-dimensional regular local ring is proper over that local ring and not over any field, and
the decomposition `Γ(X, 𝒪_X(-dE)/ℐ𝒪_X) ≅ ⨁ 𝒪_X(-dE)_{x_i}/ℐ𝒪_{X,x_i}` in the proof of
[Stacks, Tag 0AGT] is of that kind. Where the finiteness of the support is genuinely needed —
in the length statement, which sums over it — it is taken as the hypothesis `hT` naming a
`Finset`, so that the finite set indexing the sum is the consumer's.

The isolating open is produced in the `∀ y` shape by
`AlgebraicGeometry.exists_open_neighborhood_meets_support_singleton` and consumed in the
`∩ = {x}` shape by `AlgebraicGeometry.surjective_suppGermHom`; one
`Set.eq_singleton_iff_unique_mem` moves between them.

**The base ring and the module structures.** `AlgebraicGeometry.suppGermHom` is assembled as an
`AddMonoidHom.pi` of germ maps, and a germ map out of `Γ(ℱ, ⊤)` is linear over `Γ(X, 𝒪_X)` only
semilinearly, along `Γ(X, 𝒪_X) ⟶ 𝒪_{X,x}`: there is no one ring over which the product of the
stalks is a module and the map is linear. A base ring `A` mapping to `Γ(X, 𝒪_X)` fixes this,
acting on `Γ(ℱ, ⊤)` through `A ⟶ Γ(X, 𝒪_X)` and on each stalk through
`A ⟶ Γ(X, 𝒪_X) ⟶ 𝒪_{X,x}`. Those two structures are not instances — they would be a diamond —
so they are introduced by `letI` inside each statement and repeated in its proof, a `let` in a
statement not being in scope in the body. Linearity is then exactly Mathlib's
`PresheafOfModules.germ_smul` at `⊤`. For a scheme over `Spec A` the `Algebra A Γ(X, 𝒪_X)`
instance to supply is the one induced by the structure morphism,
`((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra`, which is the spelling
`Stacks.Blowup.Colength.length_globalSections_ge_sum_length_stalkQuotient` uses.

## References

* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

universe u

/-- **The germ maps onto the stalks along the support are bijective for a coherent module with
zero-dimensional support on a locally Noetherian scheme.** No properness and no base field: the
surjectivity of `AlgebraicGeometry.suppGermHom` needs only that the support is closed and that
each of its points is isolated in it, and both follow from local Noetherianness together with
coherence. -/
theorem bijective_suppGermHom_of_isLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0) :
    Function.Bijective (suppGermHom F) := by
  have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  refine ⟨injective_suppGermHom F,
    surjective_suppGermHom F (_root_.SheafOfModules.isClosed_supp F) ?_⟩
  intro x hx
  obtain ⟨U, hxU, hU⟩ := exists_open_neighborhood_meets_support_singleton F hF ⟨x, hx⟩
  exact ⟨U, hxU, Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨hxU, hx⟩, fun y hy => hU y hy.1 hy.2⟩⟩

/-- **`Γ(X, ℱ) ≅ ∏_{x ∈ Supp ℱ} ℱ_x` for a coherent module with zero-dimensional support on a
locally Noetherian scheme.** This is `AlgebraicGeometry.suppStalkPiAddEquiv` with the proper
morphism to the spectrum of a field removed; see the module documentation. -/
def suppStalkPiAddEquivOfIsLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0) :
    Γ(F, ⊤) ≃+ ∀ x : ↥(_root_.SheafOfModules.supp F), (Scheme.Modules.presheaf F).stalk x.1 :=
  AddEquiv.ofBijective (suppGermHom F) (bijective_suppGermHom_of_isLocallyNoetherian F hF)

/-- **`AlgebraicGeometry.suppGermHom` is linear over any ring acting through `Γ(X, 𝒪_X)`**, the
base ring acting on a stalk through `A ⟶ Γ(X, 𝒪_X) ⟶ 𝒪_{X,x}`. Linearity is Mathlib's
`PresheafOfModules.germ_smul` at `⊤`. -/
def suppGermLinearMap {A : Type*} [CommRing A] {X : Scheme.{u}} [Algebra A ↑Γ(X, ⊤)]
    (F : X.Modules) :
    letI : Module A ↑Γ(F, ⊤) := Module.compHom _ (algebraMap A ↑Γ(X, ⊤))
    letI : ∀ x : X, Module A ↑((Scheme.Modules.presheaf F).stalk x) := fun x =>
      Module.compHom _ (((X.presheaf.Γgerm x).hom :
        ↑Γ(X, ⊤) →+* ↑(X.presheaf.stalk x)).comp (algebraMap A ↑Γ(X, ⊤)))
    ↑Γ(F, ⊤) →ₗ[A]
      ∀ x : ↥(_root_.SheafOfModules.supp F), ↑((Scheme.Modules.presheaf F).stalk x.1) :=
  letI : Module A ↑Γ(F, ⊤) := Module.compHom _ (algebraMap A ↑Γ(X, ⊤))
  letI : ∀ x : X, Module A ↑((Scheme.Modules.presheaf F).stalk x) := fun x =>
    Module.compHom _ (((X.presheaf.Γgerm x).hom :
      ↑Γ(X, ⊤) →+* ↑(X.presheaf.stalk x)).comp (algebraMap A ↑Γ(X, ⊤)))
  { toFun := suppGermHom F
    map_add' := (suppGermHom F).map_add
    map_smul' := fun a s => by
      funext x
      exact PresheafOfModules.germ_smul F.val x.1 ⊤ trivial (algebraMap A ↑Γ(X, ⊤) a) s }

/-- **The length of the global sections of a coherent module with finite support is the sum of
the lengths of its stalks**, over any ring acting through `Γ(X, 𝒪_X)`. The finite set `T` is the
support, and it indexes the sum; the hypotheses are local Noetherianness of `X`, coherence of
`ℱ` and a zero-dimensional support — no properness and no base field.

This is the length reading of `AlgebraicGeometry.bijective_suppGermHom_of_isLocallyNoetherian`:
the germ map is `A`-linear (`AlgebraicGeometry.suppGermLinearMap`), so the decomposition of the
sections as the product of the stalks is one of `A`-modules, and `Module.length_pi_of_fintype`
turns the product into the sum. -/
theorem length_globalSections_eq_sum_length_stalk {A : Type*} [CommRing A] {X : Scheme.{u}}
    [Algebra A ↑Γ(X, ⊤)] [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0)
    (T : Finset X) (hT : _root_.SheafOfModules.supp F = (T : Set X)) :
    letI : Module A ↑Γ(F, ⊤) := Module.compHom _ (algebraMap A ↑Γ(X, ⊤))
    letI : ∀ x : X, Module A ↑((Scheme.Modules.presheaf F).stalk x) := fun x =>
      Module.compHom _ (((X.presheaf.Γgerm x).hom :
        ↑Γ(X, ⊤) →+* ↑(X.presheaf.stalk x)).comp (algebraMap A ↑Γ(X, ⊤)))
    Module.length A ↑Γ(F, ⊤) =
      ∑ x ∈ T, Module.length A ↑((Scheme.Modules.presheaf F).stalk x) := by
  classical
  let : Module A ↑Γ(F, ⊤) := Module.compHom _ (algebraMap A ↑Γ(X, ⊤))
  let : ∀ x : X, Module A ↑((Scheme.Modules.presheaf F).stalk x) := fun x =>
    Module.compHom _ (((X.presheaf.Γgerm x).hom :
      ↑Γ(X, ⊤) →+* ↑(X.presheaf.stalk x)).comp (algebraMap A ↑Γ(X, ⊤)))
  have hfin : (_root_.SheafOfModules.supp F).Finite := hT ▸ T.finite_toSet
  let : Fintype ↥(_root_.SheafOfModules.supp F) := hfin.fintype
  have hbij : Function.Bijective (suppGermLinearMap (A := A) F) :=
    bijective_suppGermHom_of_isLocallyNoetherian F hF
  let e : ↑Γ(F, ⊤) ≃ₗ[A]
      ∀ x : ↥(_root_.SheafOfModules.supp F), ↑((Scheme.Modules.presheaf F).stalk x.1) :=
    LinearEquiv.ofBijective (suppGermLinearMap (A := A) F) hbij
  rw [e.length_eq, Module.length_pi_of_fintype]
  exact (Finset.sum_subtype T (fun x => by rw [hT, Finset.mem_coe])
    (fun x => Module.length A ↑((Scheme.Modules.presheaf F).stalk x))).symm

end AlgebraicGeometry

end
