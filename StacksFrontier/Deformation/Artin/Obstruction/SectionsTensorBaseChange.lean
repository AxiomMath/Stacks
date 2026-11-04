module

public import StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorBaseChange.CartesianSquare
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorBaseChange.ProjectionFormula
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsTensorBaseChange.ChangeOfBase

/-!
# The direct image to `W` of `𝓕_A ⊗_A M`

Let `g : W → Spec Λ` be a scheme over `Λ`, `𝓕` a quasi-coherent `𝒪_W`-module and
`t : Spec A → Spec Λ` an affine scheme over `Λ`, with ring map `φ : Λ → A`. Write
`W_A = Spec A ×_{Spec Λ} W`, `π : W_A → Spec A` and `p : W_A → W` for the projections and
`𝓕_A = p^* 𝓕`. For an `A`-module `M` this file identifies
```
p_*(𝓕_A ⊗_A M) ≅ 𝓕 ⊗_Λ M
```
naturally in `M`, `M` being regarded as a `Λ`-module along `φ` on the right. So the terms
`𝓕_A ⊗_A M` of the obstruction theory of Stacks 07YH, formed on the varying spaces `W_A`, all
become modules on the single space `W`. The identification is the inverse of the projection
formula along the affine morphism `p` ([Stacks, Tag 0FZE]), followed by affine base change
`p_* π^* M̃ ≅ g^* t_* M̃` ([Stacks, Tag 02KG]) and `t_* M̃ ≅ (M|_Λ)~` ([Stacks, Tag 01I9]); none
of them needs a hypothesis on `W`.

It is compatible with change of base in two ways. In degree zero, the restriction of sections
along `W_{A'} → W_A` is, read on `W`, the map induced by `A → A'`. And for a thickening
`Spec A → Spec A'`, computing `𝓕_A ⊗_A M` on `W` directly or first on `W_{A'}` through
`𝓕_{A'} ⊗_{A'} M ≅ i_*(𝓕_A ⊗_A M)` gives the same `𝓕 ⊗_Λ M`.

## Main definitions

* `Deformation.Artin.SectionsSheaf.tensorBaseChangeIso` — **`p_*(𝓕_A ⊗_A M) ≅ 𝓕 ⊗_Λ M`**, and
  `tensorBaseChangeIsoGen` the same at an arbitrary cartesian square over `Spec φ`.
* `Deformation.Artin.SectionsSheaf.tensorBaseChangeSection` — a section of `𝓕_A` on `W_A`, read
  as a section of `𝓕 ⊗_Λ A` on `W`.
* `Deformation.Artin.SectionsSheaf.restrictScalarsHomOfComp` — a ring map `A → A'` under `Λ`, as
  a `Λ`-linear map.

## Main results

* `Deformation.Artin.SectionsSheaf.tensorBaseChangeIso_hom_naturality` — naturality in `M`.
* `Deformation.Artin.SectionsSheaf.tensorBaseChangeSection_restriction` — **the restriction maps
  of the functor of sections, read on `W`, are induced by the maps of base rings**; its
  sheaf-level form is `pushforward_reductionMapGen_comp_tensorBaseChangeUnitIsoGen`.
* `Deformation.Artin.SectionsSheaf.tensorBaseChangeIso_thickening` — **compatibility with the
  thickening identification** `pushforwardTensorSheafIsoOver`, and
  `tensorBaseChangeSection_thickening` its degree-zero form.
* `Deformation.Artin.SectionsSheaf.adjunctionTensorMap_comp_eq` — the projection formula along a
  composite factors through the projection formulas of the two morphisms.

## Implementation notes

Everything is proved at variable schemes and squares and instantiated at the fibre products only
at the end, and the instances use the `pullback.fst` spelling of the projections throughout
(`isPullback_fst_snd`), the spelling of `pushforwardTensorSheafIsoOver`: a comparison between two
spellings of one isomorphism inside a composite is what exhausts the budget (see the notes of
`SectionsThickeningSequence`). As in `SectionsBaseChangeTensor`, the chains are written in the
uncurried bifunctor spelling
`Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨_, _⟩)`, and every assembly is an
abstract lemma whose arrows are variables constrained by equations (`tensorChain_change`,
`tensorChain_thickening`), so that each spelling comparison is made once, where it is applied.
The functor `tensorSheafFunctor` tensors on the right, so its value on a morphism is a single
sheafified `PresheafOfModules.tensorHom` while the uncurried bifunctor composes two of them;
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map` is the one step that merges the pair, and
it is applied exactly where a chain is matched against `tensorSheafFunctor`.

The two compatibilities reduce to two facts. The first tensor factors are compatible along the
base (`firstFactor_unitObj_naturality`, `tensorBaseChangeFirstIso_comp_naturality`): both sides
are maps out of a pullback of an associated sheaf, so two adjoint transposes reduce them to maps
of modules out of `M`, which are compared on elements. The projection formula is compatible with
composition (`adjunctionTensorMap_unitObj_comp_reductionMapGen`, `adjunctionTensorMap_comp_eq`):
both sides are maps out of a tensor product of sheaves, which are compared on pure tensors. Inside
these proofs, a composite of morphisms is split with `modulesHom_comp_app_apply` before it is
compared with a nested application: leaving that to unification exhausts the heartbeat budget.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/
