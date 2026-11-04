module

public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyEqualizerAffineCover
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyEtaleProductAffineCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Condition (4) of Stacks 0GN4 for the étale site of an algebraic stack

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`, and give its
total category the *étale* topology of **Stacks 06TP**. Condition (4) of **Stacks 0GN4** asks, for
two objects `x`, `x'` of that site lying over affine schemes and two parallel morphisms
`a, b : x ⟶ x'`, for a finite family `V_i` of such objects with morphisms `p_i : V_i ⟶ x`
equalizing `a` and `b` for which `∐_i h_{V_i}^# ⟶ Equalizer(h_a^#, h_b^#)` is a surjection of
*étale* sheaves of sets. This file proves that condition, with one member, for a stack which is
quasi-separated over a quasi-separated base scheme, and so completes the four conditions of
Stacks 0GN4 for the étale site and with them the second assertion of **Stacks 0GQV**.

**No new mathematics is needed, and none is written here.** The whole argument already lives in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEqualizerAffineCover.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEqualizerDictionary.lean`, proved there
once at an arbitrary topology `τ` on the underlying category of schemes of `B` with the
fibre-lifting property of a surjective smooth 1-morphism as a hypothesis. The object `V` is
produced by covering the 2-fibre product

```text
U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U
```

of the two **graphs** of `a` and of `b` by an affine scheme, and everything in that construction
except the final fibre-lifting step is topology-free: the graph presentation
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.graphFunctor`, the 2-Yoneda dictionary of
`StacksFrontier/CategoryTheory/TwoFibreProduct/TwoYonedaGraphs.lean`, and quasi-compactness of the
2-fibre product `AlgebraicGeometry.Stack.isQuasiCompactStack_equalizerTwoFibreProduct` mention no
topology at all. In particular quasi-separatedness of `𝒳` enters the étale case at the same single
step, through **Stacks 075S** part (3) at the two graphs.

The one step that reads the chosen topology is the last one, where the sections of the affine
smooth presentation of **Stacks 04YC** are read off a covering of the base: for the fppf topology
that is **Stacks 06QA**, which asks the 1-morphism to be surjective, flat and locally of finite
presentation, and for the étale topology it is **Stacks 06XH** part (2),
`AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`, which asks it to be surjective and
*smooth* — exactly what Stacks 04YC supplies. So the étale case asks nothing of the presentation
that the fppf case does not, and in particular no affine étale presentation of a quasi-compact
algebraic stack is required.

So what this file contains is two instantiations at `AlgebraicGeometry.etaleTopology`, the fppf
statements being the corresponding instantiations at `AlgebraicGeometry.BigFppfSite.topology`.

## Main results

* `AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift_etale`:
  **condition (4) for the étale site**, in the shape
  `AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale` consumes as its
  hypothesis `h_equalizer`.
* `AlgebraicGeometry.Stack`
  `.isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompact`:
  **Stacks 0GQV in the étale topology** for a quasi-compact algebraic stack quasi-separated over a
  quasi-separated base scheme, with all four conditions of Stacks 0GN4 discharged.

## References

* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] essentiallySmall_join hasSheafify_ab_join enoughInjectives_sheaf_join
  globalSections_additive_join

universe v₀ u₀

/-- Sheaves of sets on a site have coproducts over an index type in `Type`, built from the
colimits of the size of the join of the two universes of the site. The instance is needed to form
the finite coproducts of sheafified representables condition (4) of Stacks 0GN4 speaks of, and is
restated in this constructed form — rather than as the
`CategoryTheory.Limits.HasColimitsOfSize` at the join universe which the files proving
Stacks 0GN3 and Stacks 0GN4 install — because with the imports of this file the search that
descends from that statement to the coproduct over a finite index type does not terminate within
the elaborator's budget. Pinning the instance at the shape actually used costs nothing and is
local to this file. It is anonymous because the files this one imports export declarations of the
same name whose `instance` attribute is local to them. -/
local instance {C : Type u₀} [Category.{v₀} C]
    (J : GrothendieckTopology C) {ι : Type} (A : ι → Sheaf J (Type max u₀ v₀)) :
    HasCoproduct A :=
  letI : HasColimitsOfSize.{max u₀ v₀, max u₀ v₀} (Sheaf J (Type max u₀ v₀)) :=
    Sheaf.instHasColimitsOfSize
  letI : HasColimitsOfSize.{0, 0} (Sheaf J (Type max u₀ v₀)) := hasColimitsOfSizeShrink _
  inferInstance

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Condition (4) of Stacks 0GN4 for the étale site of an algebraic stack quasi-separated over a
quasi-separated base scheme**, in the shape
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale` consumes as its
hypothesis `h_equalizer`: for two objects `x`, `x'` of the étale site lying over affine schemes and
two morphisms `a, b : x ⟶ x'` there is a finite family of such objects, each with a morphism to `x`
equalizing `a` and `b`, whose sheafified representables jointly cover the equalizer of `h_a^#` and
`h_b^#`.

This is
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_associatedTopology` at the big étale
topology, its fibre-lifting hypothesis discharged by **Stacks 06XH** part (2),
`AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`, which reads the fibre lifts of a
surjective smooth 1-morphism off an *étale* covering of the base. The affine smooth presentation of
**Stacks 04YC** is smooth and surjective, which is exactly what that tag asks for, so the étale
case needs nothing of the presentation beyond what the fppf case needs — in particular no affine
étale presentation of a quasi-compact algebraic stack. The family has one member, as in the
source.

The fppf statement is the same result at
`AlgebraicGeometry.BigFppfSite.topology`,
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift`, where
**Stacks 06QA** discharges the hypothesis instead. -/
@[stacks 0GN4 "condition (4) for the étale site of an algebraic stack quasi-separated over a \
quasi-separated base scheme, with the collection B of Stacks 0GQV: the objects of the site lying \
over affine schemes; the family produced has one member, as in the source"]
theorem exists_fin_affineObjects_isLocallySurjective_equalizerLift_etale
    (hqsS : QuasiSeparatedSpace S) (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳) :
    ∀ {U U' : 𝒳.val.val.obj} (u v : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒳.val → U' ∈ affineObjects B S hS 𝒳.val →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ u = p i ≫ v),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map u)
              (g := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map v)
              ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda
                    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (hp i))) :=
  exists_fin_affineObjects_isLocallySurjective_equalizerLift_associatedTopology.{u, w}
    B S hS 𝒳 hqsS h𝒳 (etaleTopology B)
    fun _ _ f hsurj hsm => exists_etaleCovering_fibre_lift B S hS f hsurj hsm

/-- **Stacks 0GQV in the étale topology for a quasi-compact algebraic stack which is
quasi-separated over a quasi-separated base scheme.** Let `𝒳` be such a stack and give its total
category the étale topology of Stacks 06TP. Then `colim_i H^p(𝒳, F_i) ⟶ H^p(𝒳, colim_i F_i)` is an
isomorphism in every degree `p`, for every filtered diagram `F` of abelian étale sheaves on `𝒳`.

All four conditions of Stacks 0GN4 are discharged for the étale site: (1) from quasi-compactness by
`AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from_etale`, (2) for
every category fibred in groupoids by
`AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_etaleTopology`, (3) by
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift_etale` and (4) by
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift_etale` above.

The quasi-separatedness hypothesis is `AlgebraicGeometry.Stack.IsQuasiSeparatedOver` of `𝒳`
together with quasi-separatedness of the base scheme `S`, which is what Stacks 075S asks for and
what conditions (3) and (4) use. It is the same hypothesis the fppf assertion
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact`
carries, and for the same reason: quasi-compactness of the 2-fibre products the source covers by an
affine scheme is **Stacks 075S** part (3). -/
@[stacks 0GQV "the second assertion, in the étale topology, for a quasi-compact algebraic stack \
quasi-separated over a quasi-separated base scheme; all four conditions of 0GN4 proved"]
theorem isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompact
    (hqsS : QuasiSeparatedSpace S)
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳 : IsQuasiSeparatedOver.{u, w} B S hS 𝒳)
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiSeparatedOver.{u, w}
    B S hS 𝒳 hqsS hqc h𝒳
    (exists_fin_affineObjects_isLocallySurjective_equalizerLift_etale.{u, w} B S hS 𝒳 hqsS h𝒳)
    p F

end AlgebraicGeometry.Stack

end
