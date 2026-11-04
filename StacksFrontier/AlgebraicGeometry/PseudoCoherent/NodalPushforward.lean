module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeModuleDegrees
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero
public import StacksFrontier.RingTheory.NodalCurve

/-!
# Relative pseudo-coherence is not preserved by pushforward along a closed embedding

**Stacks erratum.** The statement recorded under the Stacks tag 09VG
is **false**, and this file proves it. The tag asserts: for `i : X ⟶ Y` a morphism of schemes over
a base `S`, with `X ⟶ S` and `Y ⟶ S` locally of finite type and with `i` a homeomorphism of `X`
onto a closed subset of `Y`, an object `E` of `D(𝒪_X)` is `m`-pseudo-coherent relative to `S` if
and only if `Ri_*E` is. The refutation is
`AlgebraicGeometry.Scheme.Hom.not_forall_isPseudoCoherentFrom_iff_derivedPushforward`.

No declaration in this file carries the tag 09VG, a refutation being the wrong thing to register
it on. The tag sits on the corrected statement,
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_reductionImmersion`
in `StacksFrontier/AlgebraicGeometry/PseudoCoherent/ReductionClosedPushforward.lean`, which is the
source's lemma with its topological hypothesis replaced by the one its proof actually uses: that
`i` be a closed immersion on reductions, equivalently that `A/rad(A) → B/rad(B)` be surjective.

That replacement is forced by where the source's proof goes wrong. The proof opens by saying that
the topological hypothesis "means that `A/rad(A) → B/rad(B)` is surjective", which is true only in
the reverse direction; that step was already refuted by
`AlgebraicGeometry.Scheme.Hom.not_isClosedImmersionOnReductions_specMap_complex` and
`AlgebraicGeometry.Scheme.Hom.not_forall_isClosedImmersionOnReductions`. What is refuted here is
the statement itself, not just its proof: the counterexample below satisfies the topological
hypothesis and fails the conclusion, so no repair of the argument can save the printed lemma.
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_chartComparison`
isolates what survives under the printed hypothesis, granted a comparison of charts outright.

## The counterexample

Let `k` be a field, let `A = {f ∈ k[s] ∣ f(0) = f(1)}` be the node (the affine line with `0` and
`1` glued) and let `B = k[s, 1/s]` be the affine line with `0` removed. Take

`S = Y = Spec A`,  `X = Spec B`,  `g = 𝟙`,  `f = i = Spec(A → B)`,  `E = 𝒪_X`,  `m = 0`.

* `f` and `g` are locally of finite type, because `B` is of finite type over `A`
  (`Stacks.NodalCurve.finiteTypeLocalizationAway`).
* `i` is a homeomorphism of `X` onto a closed subset of `Y` — in fact onto all of `Y`:
  `Stacks.NodalCurve.isClosedEmbedding_comap_localizationAway`. The point `(s)` of `Spec k[s]` is
  removed, but the node has already glued it to `(s − 1)`, which survives.
* `𝒪_X` **is** `0`-pseudo-coherent relative to `S`: by the degree-zero clause of Stacks 09UM this
  is finiteness of type of `𝒪_X`, which always holds
  (`AlgebraicGeometry.Scheme.Hom.isModulePseudoCoherentFrom_unit_zero`). This is the content of
  the chart `X ⟶ 𝔸²_S` given by `s` and `1/s` in the informal argument.
* `Ri_*𝒪_X` is **not** `0`-pseudo-coherent relative to `S`: `i` is affine, so `Ri_*𝒪_X = i_*𝒪_X`,
  and over `S = Spec A` the degree-zero clause of Stacks 09UM asks for `B` to be a finite
  `A`-module, which it is not (`Stacks.NodalCurve.not_moduleFinite_localizationAway`).

Every ring in sight is noetherian (`Stacks.NodalCurve.isNoetherianRingNodeRing`), so no
noetherian hypothesis repairs the tag.

## Main results

* `Stacks.NodalCurve.isPseudoCoherentFrom_structureSheaf`: the left-hand side holds.
* `Stacks.NodalCurve.not_isPseudoCoherentFrom_derivedPushforward_structureSheaf`: the right-hand
  side fails.
* `AlgebraicGeometry.Scheme.Hom.not_forall_isPseudoCoherentFrom_iff_derivedPushforward`: the tag,
  quantified exactly as it is stated, is false.

## Implementation notes

The derived pushforward in the statement is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward`, the same functor
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_chartComparison`
uses, so the refuted statement is literally the one that lemma proves under an extra hypothesis.
Since `i` is a closed embedding on spaces, `i_*` is exact
(`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward`) and the derived pushforward
is the derived functor of an exact functor
(`Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory`), which is what lets the
right-hand side be computed as a single sheaf.

Two spellings of the pushforward on modules occur,
`AlgebraicGeometry.Scheme.Modules.pushforward` of a morphism of schemes and
`RingedSpaceModuleAdjunction.modulePushforward` of the underlying morphism of ringed spaces;
instance search does not cross between them, so the exactness instance is transported by hand.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.9 (09VG)](https://stacks.math.columbia.edu/tag/09VG)
* [The Stacks Project, Lemma 36.61.8 (09UM)](https://stacks.math.columbia.edu/tag/09UM)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace Stacks.NodalCurve

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k]

/-! ### The two affine schemes -/

/-- The node ring `A = {f ∈ k[s] ∣ f(0) = f(1)}` as an object of `CommRingCat`. -/
public abbrev nodeRingCat : CommRingCat.{u} := CommRingCat.of (nodeRing k)

/-- The punctured affine line `B = k[s, 1/s]` as an object of `CommRingCat`. -/
public abbrev puncturedLineCat : CommRingCat.{u} :=
  CommRingCat.of (Localization.Away (X : Polynomial k))

/-- The inclusion `A → B` of the node ring into the punctured affine line. -/
public abbrev nodeToPuncturedLine : nodeRingCat k ⟶ puncturedLineCat k :=
  CommRingCat.ofHom (algebraMap (nodeRing k) (Localization.Away (X : Polynomial k)))

/-- The morphism `i : Spec B ⟶ Spec A`: the punctured affine line mapping onto the node. -/
public abbrev puncturedLineToNode : Spec (puncturedLineCat k) ⟶ Spec (nodeRingCat k) :=
  Spec.map (nodeToPuncturedLine k)

/-- `𝒪_X` for `X = Spec B`, as an object of the derived category of `𝒪_X`-modules. -/
public abbrev structureSheafObject : DerivedCategory (Spec (puncturedLineCat k)).Modules :=
  (DerivedCategory.singleFunctor (Spec (puncturedLineCat k)).Modules 0).obj
    (SheafOfModules.unit (Spec (puncturedLineCat k)).ringCatSheaf)

/-- `i : Spec B ⟶ Spec A` is locally of finite type, `B` being of finite type over `A`. -/
public instance locallyOfFiniteType_puncturedLineToNode :
    LocallyOfFiniteType (puncturedLineToNode k) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.2 inferInstance

/-- **`i` is a homeomorphism of `Spec B` onto a closed subset of `Spec A`.** This is
`Stacks.NodalCurve.isClosedEmbedding_comap_localizationAway` read on spectra, and it is the full
hypothesis of the statement recorded under Stacks 09VG. -/
public theorem isClosedEmbedding_base_puncturedLineToNode :
    Topology.IsClosedEmbedding (puncturedLineToNode k).base :=
  isClosedEmbedding_comap_localizationAway k

/-! ### The pushforward of the structure sheaf is not of finite type -/

/-- **`i_*𝒪_X` is not a sheaf of finite type on `Spec A`.** Pushing the structure sheaf forward
along `Spec` of a ring map gives the sheaf associated to the target ring viewed as a module over
the source (`AlgebraicGeometry.Scheme.Modules.pushforwardUnitTildeIso`), an associated sheaf is of
finite type exactly when its module is finite (`AlgebraicGeometry.tilde_isFiniteType_iff`), and `B`
is not a finite `A`-module. -/
public theorem not_isFiniteType_pushforward_unit :
    ¬ ((Scheme.Modules.pushforward (puncturedLineToNode k)).obj
        (SheafOfModules.unit (Spec (puncturedLineCat k)).ringCatSheaf)).IsFiniteType := by
  intro h
  have h2 := h.of_iso (Scheme.Modules.pushforwardUnitTildeIso (nodeToPuncturedLine k))
  have h3 := (tilde_isFiniteType_iff _).1 h2
  exact not_moduleFinite_localizationAway k (RingHom.finite_algebraMap.1 h3)

/-! ### The two sides of the statement recorded under Stacks 09VG -/

/-- **The left-hand side holds:** `𝒪_X` is `0`-pseudo-coherent relative to `S = Spec A` for
`f = i`. The structure sheaf is of finite type, which by the degree-zero clause of Stacks 09UM is
relative `0`-pseudo-coherence. -/
public theorem isPseudoCoherentFrom_structureSheaf :
    Scheme.Hom.IsPseudoCoherentFrom (puncturedLineToNode k) (structureSheafObject k) 0 :=
  Scheme.Hom.isModulePseudoCoherentFrom_unit_zero (puncturedLineToNode k)

/-- **The right-hand side fails:** `Ri_*𝒪_X` is not `0`-pseudo-coherent relative to
`S = Spec A` for `g = 𝟙`.

Since `i` is a closed embedding on spaces, `i_*` is exact, so `Ri_*𝒪_X` is `i_*𝒪_X` placed in
degree zero; the degree-zero clause of Stacks 09UM then turns relative `0`-pseudo-coherence over
the identity of `Spec A` into finiteness of type of `i_*𝒪_X`, which fails by
`Stacks.NodalCurve.not_isFiniteType_pushforward_unit`. -/
public theorem not_isPseudoCoherentFrom_derivedPushforward_structureSheaf :
    ¬ Scheme.Hom.IsPseudoCoherentFrom (𝟙 (Spec (nodeRingCat k)))
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        (puncturedLineToNode k).toLRSHom.toShHom).obj (structureSheafObject k)) 0 := by
  intro hR
  have hcol : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePushforward
        (puncturedLineToNode k).toLRSHom.toShHom) :=
    Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward _
      (isClosedEmbedding_base_puncturedLineToNode k)
  have hcol' : PreservesFiniteColimits (Scheme.Modules.pushforward (puncturedLineToNode k)) :=
    hcol
  have hR2 := Scheme.Hom.IsPseudoCoherentFrom.of_iso (𝟙 (Spec (nodeRingCat k))) hR
    ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
      (puncturedLineToNode k).toLRSHom.toShHom).app (structureSheafObject k))
  have hR3 := Scheme.Hom.IsPseudoCoherentFrom.of_iso (𝟙 (Spec (nodeRingCat k))) hR2
    ((Functor.mapDerivedCategorySingleFunctor
      (Scheme.Modules.pushforward (puncturedLineToNode k)) 0).app
      (SheafOfModules.unit (Spec (puncturedLineCat k)).ringCatSheaf))
  exact not_isFiniteType_pushforward_unit k
    ((Scheme.Hom.isModulePseudoCoherentFrom_zero_iff_isFiniteType
      (𝟙 (Spec (nodeRingCat k))) _).1 hR3)

end Stacks.NodalCurve

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **The statement recorded under the Stacks tag 09VG is false.** It is not the case that, for
every pair of morphisms `f : X ⟶ S` and `g : Y ⟶ S` locally of finite type and every morphism
`i : X ⟶ Y` over `S` which is a homeomorphism of `X` onto a closed subset of `Y`, every object `E`
of `D(𝒪_X)` and every integer `m`, relative `m`-pseudo-coherence of `E` is equivalent to relative
`m`-pseudo-coherence of `Ri_*E`.

**Stacks erratum.** The conclusion above is the negation of Stacks
09VG quantified exactly as the source states it, so this declaration refutes the printed lemma
rather than merely its proof. The witness: let `k` be a field, let `A = {h ∈ k[s] ∣ h(0) = h(1)}`
be the coordinate ring of the nodal curve — the affine line with the points `0` and `1` glued —
and let `B = k[s, 1/s]` be the affine line with the origin removed. Take

`S = Y = Spec A`,  `X = Spec B`,  `i = Spec(A → B)`,  `g = 𝟙`,  `E = 𝒪_X`,  `m = 0`.

Then `B` is of finite type over `A`, so the morphisms are locally of finite type, and `i` is a
homeomorphism of `X` onto the whole of `Y`, hence onto a closed subset
(`Stacks.NodalCurve.isClosedEmbedding_base_puncturedLineToNode`): the points `(s)` and `(s - 1)`
of `Spec k[s]` are glued in the node, and `(s)` is the one `B` omits. So the hypotheses hold. The
left-hand side holds (`Stacks.NodalCurve.isPseudoCoherentFrom_structureSheaf`) and the right-hand
side fails (`Stacks.NodalCurve.not_isPseudoCoherentFrom_derivedPushforward_structureSheaf`): by
the degree-zero criterion of Stacks 09UM each side is finiteness of type of a module, automatic
for `𝒪_X` on the left, and on the right the demand that `B` — which is `Ri_*𝒪_X = i_*𝒪_X`, the
pushforward being exact here — be a finite `A`-module, which would make `1/s` integral over
`k[s]`. Every ring here is noetherian and of finite type over a field, so no noetherian hypothesis
repairs the claim.

The tag is not registered on this declaration. It is registered on the corrected statement,
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_reductionImmersion`,
which replaces the topological hypothesis with surjectivity of `A/rad(A) → B/rad(B)` — the
hypothesis the source's proof actually uses. See the module documentation. -/
public theorem Scheme.Hom.not_forall_isPseudoCoherentFrom_iff_derivedPushforward
    (k : Type u) [Field k] :
    ¬ ∀ (X Y S : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f]
        [LocallyOfFiniteType g] (i : X ⟶ Y), i ≫ g = f →
        Topology.IsClosedEmbedding i.base →
        ∀ (E : DerivedCategory X.Modules) (m : ℤ),
          Scheme.Hom.IsPseudoCoherentFrom f E m ↔
            Scheme.Hom.IsPseudoCoherentFrom g
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
                i.toLRSHom.toShHom).obj E) m := fun hpin =>
  Stacks.NodalCurve.not_isPseudoCoherentFrom_derivedPushforward_structureSheaf k
    ((hpin (Spec (Stacks.NodalCurve.puncturedLineCat k)) (Spec (Stacks.NodalCurve.nodeRingCat k))
      (Spec (Stacks.NodalCurve.nodeRingCat k)) (Stacks.NodalCurve.puncturedLineToNode k) (𝟙 _)
      (Stacks.NodalCurve.puncturedLineToNode k) (Category.comp_id _)
      (Stacks.NodalCurve.isClosedEmbedding_base_puncturedLineToNode k)
      (Stacks.NodalCurve.structureSheafObject k) 0).1
      (Stacks.NodalCurve.isPseudoCoherentFrom_structureSheaf k))

end AlgebraicGeometry

end
