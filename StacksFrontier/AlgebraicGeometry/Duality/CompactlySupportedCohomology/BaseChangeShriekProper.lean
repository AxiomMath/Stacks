module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BaseChangeShriekLifting
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProperPushforwardDeligne

/-!
# Compatibility of extension by zero with proper pushforward, for schemes

Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes, let `V ⊆ Y` be an open subscheme and
let `U = f^{-1}(V)`, so that there is a commutative square with open immersions `j : U ⟶ X` and
`j' : V ⟶ Y` and the induced `g : U ⟶ V`. The extension-by-zero functors of [Stacks, Tag 0G4N]
and the proper pushforwards then satisfy

`Rj'_! ∘ Rg_* ≅ Rf_* ∘ Rj_!`

as functors `D^b_{Coh}(𝒪_U) ⥤ Pro-D^b_{Coh}(𝒪_Y)`, where `Rf_*` acts on pro-objects termwise
(`CategoryTheory.ProSeq.map`). This is [Stacks, Tag 0G4W].

The proof is the source's first proof. For `K` in `D^b_{Coh}(𝒪_U)` with Deligne system `(K_n)`,
both `Rj'_! Rg_* K` and `Rf_* Rj_! K` restrict on `V` to the constant pro-object `Rg_* K`, the
second because `(Rf_* K_n)|_V = Rg_*(K_n|_U)` (flat base change, [Stacks, Tag 08FE]); and
`(Rf_* K_n)` is pro-isomorphic to a Deligne system
(`AlgebraicGeometry.proIsoDeligneSystem_properPushforward`), so by the uniqueness of Deligne
systems ([Stacks, Tag 0G2H]) it represents `Rj'_! Rg_* K`. The identification, natural in `K`, is
made at the level of functors of points by `CategoryTheory.baseChangeShriekOfLifting`.

## Main definitions

* `AlgebraicGeometry.extensionByZeroProperBaseChangeIso`: **[Stacks, Tag 0G4W]**.

## References

* [Stacks Project, Tag 0G4W](https://stacks.math.columbia.edu/tag/0G4W)
* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0G4W.** Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes, let
`V ⊆ Y` be open and let `U = f⁻¹(V)`, with `j : U ⟶ X`, `j' : V ⟶ Y` the open immersions and
`g : U ⟶ V` the restriction of `f`. There is a canonical isomorphism

`Rj'_! ∘ Rg_* ≅ Rf_* ∘ Rj_!`

of functors `D^b_{Coh}(𝒪_U) ⥤ Pro-D^b_{Coh}(𝒪_Y)`, where `Rj_!`, `Rj'_!` are the extensions by
zero of [Stacks, Tag 0G4N] and `Rf_*` acts on pro-objects termwise.

This is the source's first proof: for a Deligne system `(K_n)` with value `K` the system
`(Rf_* K_n)` is pro-isomorphic to a Deligne system
(`AlgebraicGeometry.proIsoDeligneSystem_properPushforward`), and its restriction to `V` is
constant with value `Rg_* K` by flat base change, so by the uniqueness of Deligne systems
(Stacks 0G2H) it represents `Rj'_! Rg_* K`; this identification is natural in `K`
(`CategoryTheory.baseChangeShriekOfLifting`). -/
@[stacks 0G4W]
public def extensionByZeroProperBaseChangeIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsNoetherian X] [IsNoetherian Y] (V : Y.Opens) :
    properPushforwardBoundedCoherent (f ∣_ V) ⋙ extensionByZeroOpenImmersion V.ι ≅
      extensionByZeroOpenImmersion (f ⁻¹ᵁ V).ι ⋙
        ProSeq.map (properPushforwardBoundedCoherent f) :=
  baseChangeShriekOfLifting (DeligneSystem.values (f ⁻¹ᵁ V).ι) (DeligneSystem.values V.ι)
    (properPushforwardBoundedCoherent f) (properPushforwardBoundedCoherent (f ∣_ V))
    (properPushforwardRestrictIso f V) fun K N =>
      (DeligneSystem.values V.ι).restrictionLifting_of_proIsoDeligne
        (proIsoDeligneSystem_iff.mp (proIsoDeligneSystem_properPushforward f V K)) N

end AlgebraicGeometry

end
