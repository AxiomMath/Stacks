module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestrictOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedLocalStalk

/-!
# Clause (2) of Stacks 0FPG implies clause (3)

Let `(X, 𝒪_X)` be a ringed space all of whose stalks are local rings and let `M` be an object of
`D(𝒪_X)` admitting a locally finite invertible module decomposition — clause (2) of
Stacks 0FPG: a locally finite direct product decomposition `𝒪_X = ∏_{n ∈ ℤ} 𝒪_n`, invertible
`𝒪_n`-modules `ℋ^n`, and `M = ⨁ ℋ^n[-n]`. Then `M` satisfies clause (3): there is an open
covering of `X` on each member of which `M` is represented by an invertible module placed in a
single degree.

The covering is the one of `ProductDecomposition.exists_nhd_unique_factor`: around every point
exactly one factor `𝒪_{n₀}` survives. On such an open set `V`

* every term of the complex `⨁ ℋ^n[-n]` other than the `n₀`-th restricts to zero, so the
  restricted complex **is** `ℋ^{n₀}` in degree `n₀`
  (`nonempty_iso_single_restrict_of_subsingleton`), and
* `ℋ^{n₀}`, read as an `𝒪_X`-module and restricted to `V`, is an **invertible**
  `𝒪_X|_V`-module.

## Main results

* `Stacks.Cohomology.InvertibleDerived.isIso_restrictModules_map_factorProjection`: on an open
  set where only the `n₀`-th factor survives, the morphism of `𝒪_X`-modules
  `RingSheafProductFactor.factorProjection` restricts to an **isomorphism** — the surviving
  factor module is the structure sheaf there.
* `Stacks.Cohomology.InvertibleDerived.isInvertibleModule_restrictModules_toOXMod`: **the
  invertibility half of clause (3)**: an invertible `𝒪_{n₀}`-module, read as an `𝒪_X`-module and
  restricted to such a `V`, is an invertible `𝒪_X|_V`-module.
* `InvertibleDerived.hasLocalInvertibleDegree_of_hasInvertibleModuleDecomposition`: **the
  implication `(2) ⟹ (3)` of Stacks 0FPG**, under the source's hypothesis that every stalk is a
  local ring.

## Implementation notes

**The invertibility is proved by a tensor inverse, not by a local trivialization.** Tag 0B8K's
`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit` asks for a partner whose tensor
product with the module is the structure sheaf, and the partner is produced over the whole of `X`
by `RingSheafProductFactor.exists_tensorObj_iso_factorModule_of_isInvertibleModule`: there the
tensor product is the factor module `𝒪_{n₀}`, not the unit, which is why the restriction to `V`
is essential — only there is the factor module the structure sheaf. Restriction commutes with
the tensor product of sheaves of modules by
`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso`, so the three isomorphisms compose
with nothing left over; in particular no monoidal structure on the restriction functor and no
local-ring hypothesis are needed for this half. The local rings enter only through
`exists_nhd_unique_factor`, which is what produces `V`.

The restriction of the unit is the unit on the nose, so no comparison appears for it: the final
isomorphism of the chain is the inverse of the restricted `factorProjection`, whose target is
already the structure module of `X|_V`.

`isIso_restrictModules_map_factorProjection` is the ringed-space twin of
`ProductDecomposition.isIso_over_factorProjection`, which says the same thing on the slice site;
clause (3) is stated on the restricted space, so the twin is the one it consumes. Both come from
sectionwise bijectivity of the component map
(`ProductDecomposition.bijective_compHom_of_subsingleton`) through
`Stacks.SheafOfModules.isIso_of_bijective_app`.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.RingSheafProductFactor StrictlyPerfect
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}}

/-- An open set of an open subspace `V` of `X` has image an open set of `X` below `V`. -/
public theorem isOpenMap_functor_obj_le (V : Opens X.carrier)
    (W : Opens (X.restrict V.isOpenEmbedding).carrier) :
    V.isOpenEmbedding.isOpenMap.functor.obj W ≤ V := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- **Where only the `n₀`-th factor survives, that factor module is the structure sheaf.** The
morphism of sheaves of `𝒪_X`-modules `RingSheafProductFactor.factorProjection`, whose sections
map is the `n₀`-th component map, becomes an isomorphism after restriction to an open set `V` on
which every other factor has no sections: over every open set of `X|_V` it is bijective, by
`ProductDecomposition.bijective_compHom_of_subsingleton`. -/
public theorem isIso_restrictModules_map_factorProjection (D : ProductDecomposition X) {n₀ : ℤ}
    {V : Opens X.carrier}
    (hsub : ∀ n, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V))) :
    IsIso ((restrictModules X V).map (factorProjection D.productPresentation n₀)) := by
  refine Stacks.SheafOfModules.isIso_of_bijective_app _ fun W => ?_
  exact D.bijective_compHom_of_subsingleton hsub (isOpenMap_functor_obj_le V W.unop)

/-- **The invertibility half of clause (3) of Stacks 0FPG.** Let `𝒪_X = ∏_n 𝒪_n` be a direct
product decomposition of the structure sheaf of a ringed space, let `V` be an open set on which
every factor other than the `n₀`-th has no sections, and let `H` be an invertible
`𝒪_{n₀}`-module. Then `H`, read as an `𝒪_X`-module and restricted to `V`, is an invertible
`𝒪_X|_V`-module.

Tag 0B8K gives a partner `H'` with `H ⊗_{𝒪_X} H' ≅ 𝒪_{n₀}` as `𝒪_X`-modules; restriction
commutes with the tensor product, and on `V` the factor module `𝒪_{n₀}` is the structure sheaf,
so the restriction of `H` has a tensor inverse there. -/
public theorem isInvertibleModule_restrictModules_toOXMod (D : ProductDecomposition X) {n₀ : ℤ}
    {V : Opens X.carrier}
    (hsub : ∀ n, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V)))
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n₀)))
    (hH : Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n₀) H) :
    IsInvertibleModule (X.restrict V.isOpenEmbedding)
      ((restrictModules X V).obj ((D.toOXMod n₀).obj H)) := by
  obtain ⟨H', ⟨e⟩⟩ := exists_tensorObj_iso_factorModule_of_isInvertibleModule
    D.productPresentation n₀ H hH
  have := isIso_restrictModules_map_factorProjection D (n₀ := n₀) hsub
  refine (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).mpr
    ⟨(restrictModules X V).obj ((D.toOXMod n₀).obj H'), ⟨?_⟩⟩
  refine (Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso X V _ _).symm ≪≫ ?_
  refine (restrictModules X V).mapIso e ≪≫ ?_
  exact (asIso ((restrictModules X V).map (factorProjection D.productPresentation n₀))).symm

/-- **The implication `(2) ⟹ (3)` of Stacks 0FPG.** If every stalk of `𝒪_X` is a local ring and
`M` admits a locally finite invertible module decomposition — clause (2) — then `M` is
represented by a complex which, on each member of an open covering of `X`, is quasi-isomorphic to
an invertible module placed in a single degree — clause (3).

The complex is the one with `ℋ^n` in degree `n` and zero differentials, which represents
`⨁ ℋ^n[-n]`; the covering is the one of `ProductDecomposition.exists_nhd_unique_factor`, on whose
members the restricted complex is that single module
(`nonempty_iso_single_restrict_of_subsingleton`) and the module is
invertible (`isInvertibleModule_restrictModules_toOXMod`).

This is one implication between clauses of the tag and not the tag, so it carries no
`@[stacks]` attribute: the converse `(3) ⟹ (2)`, the equivalence `(1) ⟺ (2)`'s remaining
direction `(1) ⟹ (2)`, and the perfectness conclusion are stated elsewhere. -/
public theorem hasLocalInvertibleDegree_of_hasInvertibleModuleDecomposition
    [inst : HasDerivedCategory.{d} (Mod X.sheaf)] (M : DerivedModules X.sheaf)
    (hM : HasInvertibleModuleDecomposition X M)
    (hloc : ∀ x : X.carrier, IsLocalRing (X.presheaf.stalk x)) :
    HasLocalInvertibleDegree M := by
  obtain ⟨D, H, hinv, ⟨eM⟩⟩ := hM
  choose V n₀ hxV hsub using fun x : X.carrier => D.exists_nhd_unique_factor x (hloc x)
  refine ⟨CochainComplex.zeroDifferentialComplex fun n => (D.toOXMod n).obj (H n),
    ⟨X.carrier, V, le_antisymm le_top fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩, fun x => ?_⟩, ?_⟩
  · refine ⟨n₀ x, (restrictModules X (V x)).obj ((D.toOXMod (n₀ x)).obj (H (n₀ x))),
      isInvertibleModule_restrictModules_toOXMod D (hsub x) (H (n₀ x)) (hinv (n₀ x)), ?_⟩
    obtain ⟨e⟩ := nonempty_iso_single_restrict_of_subsingleton D H (hsub x)
    exact ⟨e.inv, quasiIso_of_isIso e.inv⟩
  · let _i1 : HasCoproducts.{u} (DerivedModules X.sheaf) :=
      Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
    let _i2 : PreservesColimitsOfShape (Discrete (ULift.{u} ℤ))
        (DerivedCategory.Q (C := Mod X.sheaf)) :=
      Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts _ _
    let _i3 : PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.Q (C := Mod X.sheaf)) :=
      preservesColimitsOfShape_discrete_shrink.{u} _ _
    exact ⟨(CochainComplex.derivedCoproductIso
      (fun n : ℤ => (D.toOXMod n).obj (H n))).symm ≪≫ eM.symm⟩

/-! ### The non-vanishing input of the converse `(3) ⟹ (2)` -/

/-- **A point whose stalk is a local ring forces nonzero sections on every neighbourhood.** A
local ring is nontrivial, and `1 = 0` over an open set containing the point would give `1 = 0`
in the stalk.

This is the non-vanishing engine of the converse `(3) ⟹ (2)` of Stacks 0FPG: there the degrees
`n_i` attached to the members of the covering have to agree on overlaps, and they do because a
disagreement would make the invertible module of clause (3) restrict to zero on a neighbourhood
of a point of the overlap, hence — through the tensor inverse of Tag 0B8K and
`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso`, exactly as in
`isInvertibleModule_restrictModules_toOXMod` — make the structure sheaf vanish there, which this
lemma forbids. -/
public theorem not_subsingleton_sections_of_isLocalRing_stalk (x : X.carrier)
    (hx : IsLocalRing (X.presheaf.stalk x)) {W : Opens X.carrier} (hxW : x ∈ W) :
    ¬ Subsingleton (X.presheaf.obj (op W)) := by
  intro h
  let := hx
  have h10 : (1 : X.presheaf.obj (op W)) = 0 := h.elim _ _
  have hg : X.presheaf.germ W x hxW (1 : X.presheaf.obj (op W))
      = X.presheaf.germ W x hxW (0 : X.presheaf.obj (op W)) := by rw [h10]
  rw [map_one, map_zero] at hg
  exact one_ne_zero hg

end Stacks.Cohomology.InvertibleDerived

end
