module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerExteriorPower
import StacksCore.Tactic.StacksAttribute

/-!
# The homology of a symmetric power is an exterior power

Let `C` be a small category with the chaotic topology, `B` a commutative ring and `F` a flat
`B̲`-module on `C` — a diagram `F : Cᵒᵖ ⥤ ModuleCat B`, every presheaf being a sheaf for the
chaotic topology — with `H_0(C, F) = 0`, and let `U_•` be a point resolution as in Tag 08Q9.
Remark 08SG asserts

`H_k(C, Sym^k_{B̲}(F)) = ∧^k_B(H_1(C, F))`,

and this file proves it over an arbitrary commutative ring `B`.

## Main results

* `Stacks.ChaoticSite.nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram`: the identity
  above.

## Implementation notes

The route is décalage, not the remark's own argument. The remark deduces the identity from the
statement that `H_k(C, Sym^k_{B̲}(F))` is the `S_k`-coinvariants of `H_1(C, F)^{⊗ k}` for the
permutation action multiplied by the sign character. That intermediate step is a *proof* erratum:
it is false for the coefficient ring `ℤ`, which is the theorem
`Stacks.ChaoticSite.not_quillenSignedCoinvariants_int` of
`StacksFrontier.Cotangent.QuillenSignedCoinvariantsErratum`, refuted at the polynomial site of the
surjection `ℤ[x] → ℤ`, `x ↦ 0`, with `k = 2`: there the sign-twisted coinvariants of `ℤ^{⊗ 2}`
are nonzero, `Stacks.SignedTensorPower.mk_tprod_one_ne_zero`, while `∧²_ℤ ℤ = 0`. The identity
itself holds over every `B`, and the proof used here is Illusie's and Quillen's décalage,
carried out by hand at the level of simplicial modules.

Concretely, by the module half of Tag 08Q9 the homology `H_l(C, -)` is the homology of the Moore
complex of the evaluation on `U_•`, so everything reduces to a statement about the simplicial
`B`-module `Y = F(U_•)`: degreewise flat, with `H_0(Y) = 0`. Let `D` be its reduced décalage.
Then `D` is degreewise flat and simplicially null-homotopic, and `D → Y` is degreewise surjective
because `H_0(Y) = 0`; let `W` be its kernel, so that `H_0(W) = H_1(Y)`. The relative Koszul
complex of `W ⊆ D`,

`0 → ∧^k W → ∧^{k-1}W ⊗ Sym^1 D → ⋯ → ∧^1 W ⊗ Sym^{k-1}D → ∧^0 W ⊗ Sym^k D → Sym^k Y → 0`,

is exact because `D/W = Y` is flat, and every term but the two ends carries a factor `Sym^q D`
with `q ≥ 1`, which inherits the null homotopy of `D` and therefore has acyclic Moore complex.
Dimension shifting `k` times along that resolution gives
`H_k(Sym^k Y) = H_0(∧^k W) = ∧^k(H_0 W) = ∧^k(H_1(Y))`, which is the remark. The core of the
argument is `Stacks.ChaoticSite.nonempty_linearEquiv_homology_symPow`.

## References

* [Stacks Project, Tag 08SG](https://stacks.math.columbia.edu/tag/08SG)
* [Stacks Project, Tag 08RD](https://stacks.math.columbia.edu/tag/08RD)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Stacks.ChaoticSite

universe u

/-- The sectionwise symmetric power of a diagram, evaluated on a cosimplicial object, is the
degreewise symmetric power of the evaluated simplicial module. -/
public lemma comp_symmetricPowerDiagram_eq (C : Type u) [SmallCategory C] (B : Type u)
    [CommRing B] (U : CosimplicialObject C) (F : Cᵒᵖ ⥤ ModuleCat.{u} B) (k : ℕ) :
    U.op ⋙ symmetricPowerDiagram C B F k =
      (U.op ⋙ F) ⋙ Stacks.ModuleCat.symPowFunctor B k :=
  rfl

/-- Let `C` be a small category with the chaotic topology, let `B` be a
commutative ring and let `F` be a flat `B̲`-module on `C` — a diagram `F : Cᵒᵖ ⥤ ModuleCat B`,
every presheaf being a sheaf for the chaotic topology, flat meaning that every module of
sections is flat — with `H_0(C, F) = 0`, and let `U_•` be a cosimplicial object of `C` which is a
point resolution as in Tag 08Q9. Then

`H_k(C, Sym^k_{B̲}(F)) ≅ ∧^k_B(H_1(C, F))`

for every `k`, where `H_l(C, -) = L_lπ_!` is the `l`th left derived functor of the colimit over
`Cᵒᵖ` read at linear coefficients, which is the definition of the homology of a category in
Tag 08PF.

No hypothesis is placed on `B`: in particular `2` need not be invertible. -/
@[stacks 08SG "H_k(C, Sym^k_{B̲}(F)) = ∧^k_B(H_1(C, F)) over an arbitrary commutative ring B, \
with no invertibility hypothesis on 2: C is any small category with the chaotic topology, \
H_l(C, -) is L_l of the colimit over Cᵒᵖ at linear coefficients, which is Tag 08PF's definition \
of the homology of a category, the flat B-module F on the chaotic site is the diagram F, flat \
meaning that every module of sections is flat, Sym^k is the sectionwise symmetric power, and U \
is a point resolution as in Tag 08Q9. The remark's own route through the sign-twisted \
S_k-coinvariants of H_1(C, F)^{⊗ k} is a proof erratum: that intermediate step is FALSE for the \
coefficient ring ℤ, which is the theorem \
Stacks.ChaoticSite.not_quillenSignedCoinvariants_int, refuted at the polynomial site of the \
surjection ℤ[x] → ℤ with k = 2. The proof here is Illusie's and Quillen's décalage, run at the \
Moore complex of F(U_•) over the relative Koszul resolution of Sym^k by the acyclic terms \
∧^p W ⊗ Sym^{k-p} D attached to the reduced décalage D and W = ker(D → F(U_•))."]
public theorem nonempty_linearEquiv_leftDerivedColim_symmetricPowerDiagram
    (C : Type u) [SmallCategory C] (B : Type u) [CommRing B]
    (U : CosimplicialObject C) (hU : IsPointResolution U)
    (F : Cᵒᵖ ⥤ ModuleCat.{u} B) (hF : ∀ X, Module.Flat B (F.obj X))
    (h₀ : IsZero (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 0).obj F))
    (k : ℕ) :
    Nonempty (↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived k).obj
        (symmetricPowerDiagram C B F k)) ≃ₗ[B]
      ⋀[B]^k ↥(((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 1).obj F)) := by
  have h₀' : IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
      (U.op ⋙ F)).homology 0) :=
    h₀.of_iso ((ModuleValued.moduleLeftDerivedColimitNatIso U hU 0).app F).symm
  obtain ⟨e⟩ := nonempty_linearEquiv_homology_symPow B (U.op ⋙ F) (fun n => hF _) h₀' k
  exact ⟨((ModuleValued.moduleLeftDerivedColimitNatIso U hU k).app
    (symmetricPowerDiagram C B F k)).toLinearEquiv.trans (e.trans
      (exteriorPowerCongr
        ((ModuleValued.moduleLeftDerivedColimitNatIso U hU 1).app F).toLinearEquiv.symm k))⟩

end Stacks.ChaoticSite

end
