module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSliceBaseChangeAcyclic
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentDerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonBaseChangeAcyclic

/-!
# The comparison `ε : 𝒳_{affine, τ} ⟶ 𝒳_{affine}` and quasi-coherent objects (Stacks 0H0J)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids.  Its affine subcategory
`𝒳_{affine}` carries the chaotic topology (Stacks 0H09) and, for each of the topologies of
Stacks 0H0A, the associated affine topology `τ`; the structure sheaf `O` is a sheaf for every
such `τ`, and the identity of `𝒳_{affine}` is the comparison morphism of ringed sites
`ε : (𝒳_{affine, τ}, O) ⟶ (𝒳_{affine}, O)` of Cohomology on Sites, Section 0EWK.  On the chaotic
side a module is a presheaf of `O`-modules, `ε_*` is the forgetful functor and `ε^*` is
`τ`-sheafification.

**Stacks 0H0J** says that for the étale topology `ε` satisfies the assumptions and conclusions
of Stacks 0GZS: (1) the target topology is chaotic, which is how `ε` is built; (2) for every
object `x` of `𝒳_{affine}` and every K-flat complex `M^•` of `O(x)`-modules the canonical map
`M^• ⟶ RΓ((𝒳_{affine, τ}/x), (M^• ⊗_{O(x)} O_x)^#)` is a quasi-isomorphism; and consequently
`ε^*` and `Rε_*` are mutually quasi-inverse equivalences between `QC(𝒳) = QC(𝒳_{affine}, O)`
(Stacks 0H0H) and the full subcategory of `D(𝒳_{affine, τ}, O)` of the objects `K` with
`Rε_*K` in `QC(𝒳)`.

The proof is the source's.  Hypothesis (2) reduces, by
`Stacks.ModulesOnACategory.ChaoticComparison.isLocallyKFlatAcyclic_of_baseChange`, to the
statement that for every `O(x)`-module `N` the presheaf `N ⊗_{O(x)} O_x` on the slice
`𝒳_{affine, τ}/x` is a sheaf with vanishing higher cohomology; the slice is the big affine site
of the affine scheme `p(x)` (Stacks 075C), and that statement is the affine acyclicity of
quasi-coherent modules on it (Stacks 06Z0, 08GH, 0DDH in the source; here
`AlgebraicGeometry.Stack.AffineCategory.isSheaf_baseChange_affineSlice` and
`AlgebraicGeometry.Stack.AffineCategory.isZero_rightDerived_evaluation_baseChange_affineSlice`).
The conclusion is then Stacks 0GZS itself: the unit `M ⟶ Rε_*(ε^*M)` is invertible on `QC(𝒳)`
(`Stacks.ModulesOnACategory.ChaoticComparison.isIso_unit_of_isLocallyKFlatAcyclic`), so the
restricted adjunction `ε^* ⊣ Rε_*` is an adjoint equivalence
(`Stacks.ModulesOnACategory.ChaoticComparison.pullbackPushforwardEquivalence`).

Everything is stated once for each of the five topologies of Stacks 0H0A (a `SiteKind`), the
ringed site being `AlgebraicGeometry.Stack.AffineCategory.siteKindRingedSite`; Stacks 0H0J is the
instance at the étale topology, and Stacks 0H0X, the same statement for the fppf topology, the
instance there.

## Main results

* `AlgebraicGeometry.Stack.isLocallyKFlatAcyclic_affine` and
  `AlgebraicGeometry.Stack.isIso_unit_affine`: hypothesis (2) of Stacks 0GZS for
  `ε : 𝒳_{affine, τ} ⟶ 𝒳_{affine}`, and the invertibility of the unit on `QC(𝒳)` it gives.
* `AlgebraicGeometry.Stack.affineQuasiCoherentEquivalence`: the conclusion of Stacks 0GZS, the
  equivalence between `QC(𝒳)` and the objects `K` with `Rε_*K` quasi-coherent, with functor
  `ε^*` and inverse `Rε_*`.
* `AlgebraicGeometry.Stack.isLocallyKFlatAcyclic_affineEtale` and
  `AlgebraicGeometry.Stack.affineEtaleQuasiCoherentEquivalence`: **Stacks 0H0J**.
* `AlgebraicGeometry.Stack.isLocallyKFlatAcyclic_affineFppf` and
  `AlgebraicGeometry.Stack.affineFppfQuasiCoherentEquivalence`: **Stacks 0H0X**.

## References

* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
* [Stacks Project, Tag 0H0X](https://stacks.math.columbia.edu/tag/0H0X)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0H0H](https://stacks.math.columbia.edu/tag/0H0H)
* [Stacks Project, Tag 075C](https://stacks.math.columbia.edu/tag/075C)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : SiteKind)

/-- **Hypothesis (2) of Stacks 0GZS for `ε : 𝒳_{affine, τ} ⟶ 𝒳_{affine}`.** For every object
`x` of `𝒳_{affine}` and every K-flat complex `M^•` of `O(x)`-modules the canonical map
`M^• ⟶ RΓ((𝒳_{affine, τ}/x), (M^• ⊗_{O(x)} O_x)^#)` is a quasi-isomorphism. -/
theorem isLocallyKFlatAcyclic_affine :
    IsLocallyKFlatAcyclic.{t}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (AffineCategory.siteKindRingedSite B S hS p hp τ).O))
      (affineStructurePresheaf_comm B S hS p) :=
  isLocallyKFlatAcyclic_of_baseChange.{t} _ _
    (AffineCategory.isSheaf_baseChange_affineSlice.{u, v, w, t} B S hS hp τ)
    (AffineCategory.isZero_rightDerived_evaluation_baseChange_affineSlice.{u, v, w, t} B S hS hp τ)

/-- Under hypothesis (2) the unit `M ⟶ Rε_*(ε^*M)` is invertible at every `M` in `QC(𝒳)`. -/
theorem isIso_unit_affine (M : DMod.{t} (affineStructurePresheaf B S hS p))
    (hM : IsQuasiCoherentObject.{u, v, w, t} B S hS p M) :
    IsIso ((derivedEpsilonAdjunction.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp τ).O)).unit.app M) :=
  isIso_unit_of_isLocallyKFlatAcyclic.{t} _ _ (isLocallyKFlatAcyclic_affine B S hS p hp τ) M hM

/-- **The conclusion of Stacks 0GZS for `ε : 𝒳_{affine, τ} ⟶ 𝒳_{affine}`.** `ε^*` and `Rε_*`
are mutually quasi-inverse equivalences between `QC(𝒳)` (Stacks 0H0H) and the full subcategory
of `D(𝒳_{affine, τ}, O)` of the objects `K` with `Rε_*K` in `QC(𝒳)`: the functor of this
equivalence is `ε^*` and its inverse is `Rε_*`
(`AlgebraicGeometry.Stack.affineQuasiCoherentEquivalence_functor` and `_inverse`). -/
def affineQuasiCoherentEquivalence :
    quasiCoherentDerived.{u, v, w, t} B S hS p ≌
      (pushforwardProperty.{t}
        (Stacks.SheafOfModules.Tensor.ringSheaf (AffineCategory.siteKindRingedSite B S hS p hp τ).O)
        (IsQuasiCoherentObject.{u, v, w, t} B S hS p)).FullSubcategory :=
  pullbackPushforwardEquivalence.{t} _
    (IsQC.{t} (baseChangeDataOfComm.{u, w, v, t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp τ).O).obj
      (affineStructurePresheaf_comm B S hS p)))
    (isIso_unit_affine B S hS p hp τ)

/-- The functor of `AlgebraicGeometry.Stack.affineQuasiCoherentEquivalence` is `ε^*`. -/
theorem affineQuasiCoherentEquivalence_functor :
    (affineQuasiCoherentEquivalence B S hS p hp τ).functor =
      restrictedPullback.{t}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (AffineCategory.siteKindRingedSite B S hS p hp τ).O))
        (IsQC.{t} (baseChangeDataOfComm.{u, w, v, t}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (AffineCategory.siteKindRingedSite B S hS p hp τ).O).obj
          (affineStructurePresheaf_comm B S hS p)))
        (isIso_unit_affine B S hS p hp τ) :=
  rfl

/-- The inverse of `AlgebraicGeometry.Stack.affineQuasiCoherentEquivalence` is `Rε_*`. -/
theorem affineQuasiCoherentEquivalence_inverse :
    (affineQuasiCoherentEquivalence B S hS p hp τ).inverse =
      restrictedPushforward.{t}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (AffineCategory.siteKindRingedSite B S hS p hp τ).O))
        (IsQuasiCoherentObject.{u, v, w, t} B S hS p) :=
  rfl

/-! ### The étale topology: Stacks 0H0J -/

/-- **Stacks 0H0J, hypothesis (2) of Stacks 0GZS.** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category
fibred in groupoids and `ε : (𝒳_{affine, étale}, O) ⟶ (𝒳_{affine}, O)` the comparison morphism to
the associated affine site with its chaotic topology.  For every object `x` of `𝒳_{affine}` and
every K-flat complex `M^•` of `O(x)`-modules the canonical map
`M^• ⟶ RΓ((𝒳_{affine, étale}/x), (M^• ⊗_{O(x)} O_x)^#)` is a quasi-isomorphism.  (Hypothesis
(1) of Stacks 0GZS, that the target topology is chaotic, is the construction of `ε`: modules on
the chaotic site are presheaves of modules.) -/
@[stacks 0H0J "ε : 𝒳_{affine,étale} ⟶ 𝒳_{affine} satisfies the assumptions of Stacks 0GZS: \
hypothesis (2), the target being the chaotic site by construction"]
theorem isLocallyKFlatAcyclic_affineEtale :
    IsLocallyKFlatAcyclic.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .etale).O)
      (affineStructurePresheaf_comm B S hS p) :=
  isLocallyKFlatAcyclic_affine B S hS p hp .etale

/-- **Stacks 0H0J, the conclusion of Stacks 0GZS.** For a category fibred in groupoids
`p : 𝒳 ⥤ (Sch/S)_{fppf}` and the comparison `ε : (𝒳_{affine, étale}, O) ⟶ (𝒳_{affine}, O)`,
`ε^*` and `Rε_*` are mutually quasi-inverse equivalences between `QC(𝒳)` (Stacks 0H0H) and the
full subcategory of `D(𝒳_{affine, étale}, O)` of the objects `K` with `Rε_*K` in `QC(𝒳)`.  The
functor of the equivalence is `ε^*` and its inverse is `Rε_*`, both on the nose
(`AlgebraicGeometry.Stack.affineQuasiCoherentEquivalence_functor` and `_inverse`). -/
@[stacks 0H0J "ε : 𝒳_{affine,étale} ⟶ 𝒳_{affine} satisfies the conclusions of Stacks 0GZS: \
ε^* and Rε_* are mutually quasi-inverse equivalences between QC(𝒳) and the objects K of \
D(𝒳_{affine,étale}, O) with Rε_*K in QC(𝒳)"]
def affineEtaleQuasiCoherentEquivalence :
    quasiCoherentDerived.{u, v, w, t} B S hS p ≌
      (pushforwardProperty.{t}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (AffineCategory.siteKindRingedSite B S hS p hp .etale).O)
        (IsQuasiCoherentObject.{u, v, w, t} B S hS p)).FullSubcategory :=
  affineQuasiCoherentEquivalence B S hS p hp .etale

/-! ### The fppf topology: Stacks 0H0X -/

/-- **Stacks 0H0X, hypothesis (2) of Stacks 0GZS.** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category
fibred in groupoids and `ε : (𝒳_{affine, fppf}, O) ⟶ (𝒳_{affine}, O)` the comparison morphism to
the associated affine site with its chaotic topology.  For every object `x` of `𝒳_{affine}` and
every K-flat complex `M^•` of `O(x)`-modules the canonical map
`M^• ⟶ RΓ((𝒳_{affine, fppf}/x), (M^• ⊗_{O(x)} O_x)^#)` is a quasi-isomorphism.  (Hypothesis
(1) of Stacks 0GZS, that the target topology is chaotic, is the construction of `ε`: modules on
the chaotic site are presheaves of modules.) -/
@[stacks 0H0X "ε : 𝒳_{affine,fppf} ⟶ 𝒳_{affine} satisfies the assumptions of Stacks 0GZS: \
hypothesis (2), the target being the chaotic site by construction"]
theorem isLocallyKFlatAcyclic_affineFppf :
    IsLocallyKFlatAcyclic.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (AffineCategory.siteKindRingedSite B S hS p hp .fppf).O)
      (affineStructurePresheaf_comm B S hS p) :=
  isLocallyKFlatAcyclic_affine B S hS p hp .fppf

/-- **Stacks 0H0X, the conclusion of Stacks 0GZS.** For a category fibred in groupoids
`p : 𝒳 ⥤ (Sch/S)_{fppf}` and the comparison `ε : (𝒳_{affine, fppf}, O) ⟶ (𝒳_{affine}, O)`,
`ε^*` and `Rε_*` are mutually quasi-inverse equivalences between `QC(𝒳)` (Stacks 0H0H) and the
full subcategory of `D(𝒳_{affine, fppf}, O)` of the objects `K` with `Rε_*K` in `QC(𝒳)`.  The
functor of the equivalence is `ε^*` and its inverse is `Rε_*`, both on the nose
(`AlgebraicGeometry.Stack.affineQuasiCoherentEquivalence_functor` and `_inverse`). -/
@[stacks 0H0X "ε : 𝒳_{affine,fppf} ⟶ 𝒳_{affine} satisfies the conclusions of Stacks 0GZS: \
ε^* and Rε_* are mutually quasi-inverse equivalences between QC(𝒳) and the objects K of \
D(𝒳_{affine,fppf}, O) with Rε_*K in QC(𝒳)"]
def affineFppfQuasiCoherentEquivalence :
    quasiCoherentDerived.{u, v, w, t} B S hS p ≌
      (pushforwardProperty.{t}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (AffineCategory.siteKindRingedSite B S hS p hp .fppf).O)
        (IsQuasiCoherentObject.{u, v, w, t} B S hS p)).FullSubcategory :=
  affineQuasiCoherentEquivalence B S hS p hp .fppf

end AlgebraicGeometry.Stack

end

