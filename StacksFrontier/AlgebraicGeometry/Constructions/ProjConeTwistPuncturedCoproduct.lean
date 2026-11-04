module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecPuncturedConeCohomology
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedStandardOpenSum
public import StacksFrontier.AlgebraicGeometry.MeromorphicConstantModule.LocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum

/-!
# `(π|_U)_* 𝒪_U = ⨁_{m ∈ ℤ} 𝒪_P(m)`

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}` and let `U ⊆ L` be the punctured cone.
This file proves the identification

  `(π|_U)_* 𝒪_U ≅ ∐_{m ∈ ℤ} 𝒪_P(m)`

of [Stacks, Tag 0EKG] as an isomorphism of sheaves of `𝒪_P`-modules, the coproduct being the
categorical one — that is, the sheafification of the objectwise direct sum.

The route is the one the footnote of [Stacks, Tag 0EKG] indicates. The family of degreewise
inclusions glued in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjConeTwistPuncturedGlobalMap.lean` assembles into
a morphism `⨁_{m ∈ ℤ} 𝒪_P(m) ⟶ (π|_U)_* 𝒪_U` out of the *objectwise* direct sum, which over a
standard open of a positive-degree homogeneous element is the honest isomorphism
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSectionsEquivTwistSections`. Since the
standard opens of positive-degree homogeneous elements form a basis of `P`, that morphism is
locally bijective, so `Stacks.sheafifyIsoOfLocallyBijective` exhibits `(π|_U)_* 𝒪_U` as the
sheafification of the objectwise direct sum, and `Stacks.sheafifyDirectSumIso` identifies that
sheafification with the coproduct.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistDirectSumHom`: the family of degreewise
  inclusions as a morphism out of the objectwise direct sum of the twisting sheaves.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructureSheafifyIso`: `(π|_U)_* 𝒪_U` is
  the sheafification of the objectwise direct sum `⨁_{m ∈ ℤ} 𝒪_P(m)`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructureCoproductIso`: **the
  identification `(π|_U)_* 𝒪_U ≅ ∐_{m ∈ ℤ} 𝒪_P(m)`.**
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructurePushforwardCoproductIso`: the same
  isomorphism with its source written as the direct image of the structure sheaf of the punctured
  cone of `Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConeProj`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistDirectSumHom_app_of`: on a standard open
  of the basis the morphism out of the objectwise direct sum sends the `m`-th summand to the local
  degreewise inclusion.
* `Stacks.AlgebraicGeometry.ProjConeTwist.bijective_puncturedTwistDirectSumHom_app`: **over a
  standard open of a positive-degree homogeneous element that morphism is bijective.**

## Implementation notes

The bijectivity over a standard open is the statement that the morphism agrees there with the
additive equivalence `puncturedConeAlgebraSectionsEquivTwistSections`, read backwards. Two
additive maps out of a direct sum agree as soon as they agree on each summand
(`DirectSum.addHom_ext`), and on the `m`-th summand both are the local degreewise inclusion — the
left-hand side by `Stacks.inclHom_directSumDesc` together with
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom_app`, the right-hand side by
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSectionsEquivTwistSections_symm_of`.

Everything is indexed by `Stacks.AlgebraicGeometry.ProjTwistComparison.PositiveElem`, in which
the degree of the element is existentially quantified; the degree chosen by
`puncturedConeTwistStandardOpenApp` is the one at which the sections equivalence is read, so no
degree-independence is needed here.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The family of punctured degreewise inclusions as a single morphism out of the objectwise
direct sum** `⨁_{m ∈ ℤ} 𝒪_P(m) ⟶ (π|_U)_* 𝒪_U`. -/
@[stacks 0EKG "the family of degreewise inclusions O_P(m) -> (pi|_U)_* O_U as one morphism out \
of the objectwise direct sum over all integers m, for the truncation cone"]
def puncturedTwistDirectSumHom :
    Stacks.directSum (fun m : ℤ => (twistingSheaf 𝒜 m).val) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val :=
  Stacks.directSumDesc _ fun m => (puncturedTwistHom 𝒜 m).val

/-- **On a standard open of the basis the morphism out of the objectwise direct sum sends the
`m`-th summand to the local degreewise inclusion.** -/
theorem puncturedTwistDirectSumHom_app_of (m : ℤ) (p : PositiveElem 𝒜)
    (s : (twistingSheaf 𝒜 m).val.obj (op (positiveBasicOpen 𝒜 p))) :
    (puncturedTwistDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p))
        (DirectSum.of _ m s) =
      (puncturedConeTwistStandardOpenApp 𝒜 m p).hom s := by
  refine Eq.trans (congrArg (fun q : (twistingSheaf 𝒜 m).val ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val =>
        q.app (op (positiveBasicOpen 𝒜 p)) s)
    (Stacks.inclHom_directSumDesc (fun k : ℤ => (twistingSheaf 𝒜 k).val)
      (fun k => (puncturedTwistHom 𝒜 k).val) m)) ?_
  exact congrArg (fun φ : (twistingSheaf 𝒜 m).val.obj (op (positiveBasicOpen 𝒜 p)) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.obj
        (op (positiveBasicOpen 𝒜 p)) => φ.hom s) (puncturedTwistHom_app 𝒜 m p)

/-- **Over a standard open of a positive-degree homogeneous element the morphism out of the
objectwise direct sum is bijective.** It agrees there with the additive equivalence
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeAlgebraSectionsEquivTwistSections`, read
backwards. -/
@[stacks 0EKG "the morphism out of the objectwise direct sum of the twisting sheaves is \
bijective on the sections over a standard open of a positive-degree homogeneous element, for \
the punctured cone of the truncation algebra"]
theorem bijective_puncturedTwistDirectSumHom_app (p : PositiveElem 𝒜) :
    Function.Bijective
      ((puncturedTwistDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p))).hom := by
  have hdpos : 0 < Classical.choose p.2 := (Classical.choose_spec p.2).1
  have hmem : p.1 ∈ 𝒜 (Classical.choose p.2) := (Classical.choose_spec p.2).2
  have happ : ∀ z, (puncturedTwistDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p)) z =
      (puncturedConeAlgebraSectionsEquivTwistSections 𝒜 (Classical.choose p.2) hmem
        hdpos).symm z := by
    refine DFunLike.congr_fun (DirectSum.addHom_ext
      (f := Stacks.homToAddMonoidHom (fun k : ℤ => (twistingSheaf 𝒜 k).val)
        (puncturedTwistDirectSumHom 𝒜) (op (positiveBasicOpen 𝒜 p)))
      (g := (puncturedConeAlgebraSectionsEquivTwistSections 𝒜 (Classical.choose p.2) hmem
        hdpos).symm.toAddMonoidHom) fun k s => ?_)
    exact (puncturedTwistDirectSumHom_app_of 𝒜 k p s).trans
      (puncturedConeAlgebraSectionsEquivTwistSections_symm_of 𝒜 k (Classical.choose p.2) hmem
        hdpos s).symm
  have : ⇑((puncturedTwistDirectSumHom 𝒜).app (op (positiveBasicOpen 𝒜 p))).hom =
      ⇑(puncturedConeAlgebraSectionsEquivTwistSections 𝒜 (Classical.choose p.2) hmem
        hdpos).symm := funext happ
  rw [this]
  exact (puncturedConeAlgebraSectionsEquivTwistSections 𝒜 (Classical.choose p.2) hmem
    hdpos).symm.bijective

/-- **`(π|_U)_* 𝒪_U` is the sheafification of the objectwise direct sum `⨁_{m ∈ ℤ} 𝒪_P(m)`.**
The comparison morphism is bijective on the sections over every standard open of a
positive-degree homogeneous element, and those form a basis of `P`. -/
@[stacks 0EKG "the direct image of the structure sheaf of the punctured cone is the \
sheafification of the objectwise direct sum of all the twisting sheaves, for the truncation cone"]
def puncturedConeStructureSheafifyIso :
    (PresheafOfModules.sheafification (𝟙 _)).obj
        (Stacks.directSum fun m : ℤ => (twistingSheaf 𝒜 m).val) ≅
      Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜) :=
  Stacks.sheafifyIsoOfLocallyBijective (puncturedTwistDirectSumHom 𝒜)
    (Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallyInjective_of_injective_basis
      (Y := ProjectiveSpectrum.top 𝒜) (B := positiveBasicOpen 𝒜) _
      (isBasis_positiveBasicOpen 𝒜) fun p => (bijective_puncturedTwistDirectSumHom_app 𝒜 p).1)
    (Stacks.AlgebraicGeometry.MeromorphicConstantModule.isLocallySurjective_of_surjective_basis
      (Y := ProjectiveSpectrum.top 𝒜) (B := positiveBasicOpen 𝒜) _
      (isBasis_positiveBasicOpen 𝒜) fun p => (bijective_puncturedTwistDirectSumHom_app 𝒜 p).2)

/-- **`(π|_U)_* 𝒪_U ≅ ∐_{m ∈ ℤ} 𝒪_P(m)`**: the identification of [Stacks, Tag 0EKG] of the direct
image of the structure sheaf of the punctured cone with the coproduct, over all integers, of the
twisting sheaves of `P = Proj A`. -/
@[stacks 0EKG "the identification (pi|_U)_* O_U = the coproduct over all integers m of the \
twisting sheaves O_P(m), as sheaves of O_P-modules, for the punctured cone of the truncation \
algebra"]
def puncturedConeStructureCoproductIso :
    Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜) ≅
      ∐ fun m : ℤ => twistingSheaf 𝒜 m :=
  (puncturedConeStructureSheafifyIso 𝒜).symm ≪≫
    Stacks.sheafifyDirectSumIso fun m : ℤ => twistingSheaf 𝒜 m

/-- **`(π|_U)_* 𝒪_U ≅ ∐_{m ∈ ℤ} 𝒪_P(m)`**, with the source written as the direct image along
`Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConeProj` of the structure sheaf of the punctured
cone. This is the form in which the identification is consumed by the projection formula along
`π|_U`. -/
@[stacks 0EKG "the identification (pi|_U)_* O_U = the coproduct over all integers m of the \
twisting sheaves O_P(m), with the source written as the direct image along the punctured cone \
projection of the truncation cone data"]
def puncturedConeStructurePushforwardCoproductIso :
    (Scheme.Modules.pushforward
          (Stacks.AlgebraicGeometry.ProjAndSpec.puncturedConeProj (truncationConeData 𝒜))).obj
        (SheafOfModules.unit
          (Stacks.AlgebraicGeometry.ProjAndSpec.openUInL
            (truncationConeData 𝒜)).toScheme.ringCatSheaf) ≅
      ∐ fun m : ℤ => twistingSheaf 𝒜 m :=
  puncturedConeStructureCoproductIso 𝒜

end Stacks.AlgebraicGeometry.ProjConeTwist

end
