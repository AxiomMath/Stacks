module

public import StacksFrontier.RingTheory.SpreadingOut.FlatModel.FiniteTypeModel
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel.DirectedModel
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel.UniverseTransport
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel.Packaged

/-!
# Flat models of a flat finitely presented module

Let `R → S` be of finite presentation and let `M` be a finitely presented `S`-module which is
flat over `R`. This file proves Stacks 02JO: the triple `(R → S, M)` is the base change of a
triple `(R₀ → S₀, M₀)` with `R₀` of finite type over `ℤ`, `S₀` of finite type over `R₀` and `M₀`
a finite `S₀`-module flat over `R₀`; such a flat model exists at a stage of any directed colimit
presentation of `R`; and a cartesian directed system of finitely presented models with colimit
`(R → S, M)` is flat at all sufficiently large stages.

## Main results

* `Module.Flat.exists_flat_models_and_eventually_flat`: Stacks 02JO, packaged as the three-part
  statement of the source and at the universe generality the source asserts.
* `Module.Flat.exists_finiteType_model`: Stacks 02JO (1).
* `Module.Flat.exists_finitePresentation_model_of_directed`: Stacks 02JO (2).
* `Module.Flat.eventually_flat_of_directed`: Stacks 02JO (3).
* `Module.Flat.exists_small_finiteType_model`, `Module.Flat.exists_small_finitePresentation_model`:
  a flat model may be replaced by an isomorphic model in prescribed universes.
* `Algebra.FiniteTypeSystem.exists_flat_stage`: in the directed system of finite type models of
  Stacks 00R1, the module is flat over the base at some stage.
* `AlgHom.exists_comp_eq_of_finitePresentation`, `LinearMap.exists_comp_eq_of_finitePresentation`:
  maps out of finitely presented algebras and modules into a directed colimit factor through a
  stage (the elementwise form of Stacks 00QO and 05LI).
* `Module.Flat.DirectedModel.isPushout_colimit`, `Module.Flat.DirectedModel.isBaseChange_colimit`:
  the colimit of a cartesian directed system is the base change of every stage.

## Implementation notes

Part (1) is the source's argument. Let `R_λ` run over the finite type `ℤ`-subalgebras of `R`
containing a ring of definition `R₀`, with `S_λ = R_λ ⊗_{R₀} S₀` and `M_λ = S_λ ⊗_{S₀} P`. For a
prime `q` of `S` the module `M_λ` is flat over `R_λ` at the prime under `q` for `λ` large
(`Algebra.FiniteTypeSystem.exists_flat_localized_stage`, which is 00R6 applied to the localized
system). The flat locus `U_λ ⊆ Spec(S_λ)` is open by 00RC over the Noetherian ring `R_λ`, and its
preimages `V_λ ⊆ Spec(S)` increase with `λ` and cover `Spec(S)`, which is quasi-compact, so one of
them is everything. The complement of `U_{λ₀}` is `V(I)` with `IS = S`, and `1 ∈ I S` is already
witnessed in some `S_λ`; for that `λ` the flat locus `U_λ` is all of `Spec(S_λ)`, so `M_λ` is flat
over `R_λ`. In (1) the rings `R` and `S` share a universe, as in 00R1
(`Algebra.exists_subring_finiteType_int_isPushout_isBaseChange`); `M` is arbitrary.

Part (2) lifts `R₀ → R` to a stage `R_λ` (`R₀` is of finite presentation over `ℤ`) and base changes
the model of (1) along `R₀ → R_λ`.

Part (3) follows the source as well, starting from the model of (2) at a stage `λ₀`. The structure
map `T → S` of the model lifts to some `S_{λ₁}`; the comparison map `R_{λ₁} ⊗_{R_{λ₀}} T → S_{λ₁}`
becomes an isomorphism over `R`, since both sides base change to `S` there
(`Module.Flat.DirectedModel.isPushout_colimit`), hence over some `R_μ` by Stacks 05N8, which makes
`S_μ = R_μ ⊗_{R_{λ₀}} T` (`Module.Flat.DirectedModel.exists_isStageModel`). The map of modules is
handled the same way with Stacks 05LI, giving `M_ν = S_ν ⊗_T P = R_ν ⊗_{R_{λ₀}} P`, which is flat
over `R_ν`; flatness then propagates to every later stage along the cartesian transition maps
(`Module.Flat.DirectedModel.flat_of_le`). The system of (3) is given elementwise: rings `A λ`,
`B λ` with `A λ`-algebra structures, modules `N λ` over `B λ`, transition maps (the module ones
semilinear), and legs to `R`, `S`, `M` exhibiting them as directed colimits. The condition that
`R_μ ⊗_{R_λ} S_λ → S_μ` is an isomorphism is stated as the transition square being a pushout in
`CommRingCat`, and the condition on the modules as `IsBaseChange`.

## References

* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
-/
