module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingHomothety
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSlice

/-!
# A dualizing complex is its own internal hom, on the slice site over an affine open

Let `X` be a locally Noetherian scheme, `K` a dualizing complex on `X` ([Stacks, Tag 0A87]) and
`U ⊆ X` an affine open. This file produces the isomorphism of *objects*

`R𝓗om_{𝒪_X|_U}(K|_U, K|_U) ≅ 𝒪_X|_U[0]`

on the slice site `Opens(X)/U`, which is the model in which restriction to a member of a
covering family of the site of opens of `X` is phrased.

Over `Spec Γ(X, U)` the computation is
`Stacks.Duality.derivedTildeDerivedSheafHomSelfUnitIso`: the derived homothety of a dualizing
complex over a Noetherian ring is invertible, so `R𝐻om_R(ω, ω)` is `R` in degree zero, and the
comparison of [Stacks, Tag 0A6H] (3)(a) carries that to `D(𝒪_{Spec R})`. It is carried to the
slice site by the two equivalences `Stacks.Duality.HasDualizingModelOn` seals, exactly as in
`Stacks.Duality.isIso_derivedSheafHomCounit_restrictD_of_isDualizingComplex`: the pullback along
`U ≅ Spec Γ(X, U)` and the equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv U` between
modules on the open subscheme and modules on the slice site. Along an equivalence carrying tensor
products to tensor products the derived internal hom is carried to the derived internal hom, and
each of the two equivalences carries the structure sheaf in degree zero to the structure sheaf in
degree zero — `Stacks.SheafOfModules.PullbackIsoTensor.pullbackDerivedUnitIso` and
`Stacks.SheafOfModules.OverEquivTensor.overEquivDerivedUnitIso` — which is what turns the
computation over the spectrum into the one over the slice site.

The last step is reflection: `overEquiv U` is an equivalence, so an isomorphism between the
images of two objects of `D(𝒪_X|_U)` comes from an isomorphism of those objects
(`CategoryTheory.Functor.preimageIso`).

## Main definitions

* `Stacks.Duality.restrictDDerivedSheafHomSelfUnitIso` — **the object isomorphism
  `R𝓗om_{𝒪_X|_U}(K|_U, K|_U) ≅ 𝒪_X|_U[0]`** on the slice site over an affine open `U`, for `K`
  a dualizing complex on a locally Noetherian scheme.

## Main results

* `Stacks.Duality.nonempty_restrictDDerivedSheafHomSelfUnitIso_of_iso` — the same with the
  dualizing model over `Γ(X, U)` and its isomorphism given, and no hypothesis on `X`.
* `Stacks.Duality.nonempty_restrictDDerivedSheafHomSelfUnitIso` — the existence statement the
  definition above chooses from.

## Implementation notes

The tensor unit of `AlgebraicGeometry.RingedSite.derivedTensorMonoidal` is the structure sheaf
in degree zero on the nose, that structure being
`Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal` and re-seating replacing the unit
by the target of `Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso`; the same holds for
`Stacks.SheafOfModules.derivedMonoidalStructure` over the spectrum. So the two unit comparisons
above are stated at the degree-zero inclusion of `SheafOfModules.unit` and need no further
comparison at either end.

The isomorphism is an isomorphism of *objects*. Nothing here states a compatibility with the
evaluation morphisms, and nothing is asked of one: the consumer is
`Stacks.SheafOfModules.isIso_map_derivedSheafHomothety_of_iso_derivedSheafHom`, for which a bare
isomorphism of objects suffices because the internal hom from `K|_U` to itself carries a
composition for which the homothety is a left unit.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry Stacks.SheafOfModules

universe u

-- Standard model only: `Stacks.SheafOfModules.derivedSheafHomothety`.
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

/-- **`R𝓗om(K|_U, K|_U) ≅ 𝒪_X|_U[0]` on the slice site over an affine open**, from a dualizing
model over `Γ(X, U)` and its isomorphism. This is the body of
`Stacks.Duality.nonempty_restrictDDerivedSheafHomSelfUnitIso`, stated with the Noetherian
hypothesis on `Γ(X, U)` as an instance argument and no hypothesis on `X`. -/
theorem nonempty_restrictDDerivedSheafHomSelfUnitIso_of_iso
    {W : Scheme.{u}} (V : W.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(W, V)]
    {ω : DerivedCategory (ModuleCat.{u} Γ(W, V))} (hω : Dualizing.IsDualizingComplex ω)
    (K : DerivedCategory W.Modules)
    (i : ((Scheme.Modules.overEquiv V).functor).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} W.ringCatSheaf V).mapDerivedCategory.obj K) ≅
      (tilde.functor Γ(W, V) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj ω) :
    letI := RingedSite.derivedTensorMonoidal ((ringedSite W.sheaf).over V)
    Nonempty (((RingedSite.derivedSheafHomBifunctor ((ringedSite W.sheaf).over V)).obj
          (op ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD
            (ringedSite W.sheaf) V).obj K))).obj
            ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K) ≅
      𝟙_ (DerivedCategory (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite W.sheaf).over V).O)))) := by
  let := RingedSite.derivedTensorMonoidal ((ringedSite W.sheaf).over V)
  have a := i ≪≫ (Dualizing.mapDerivedCategoryComp (tilde.functor Γ(W, V))
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom)).app ω ≪≫
    (PullbackIsoTensor.restrictFunctorDerivedIsoPullback hV.isoSpec.hom).app
      ((derivedTildeStructureSheafModules Γ(W, V)).obj ω)
  have h₁ := PullbackIsoTensor.exists_iso_and_isIso_derivedSheafHomCounit_iff
    hV.isoSpec.hom ((derivedTildeStructureSheafModules Γ(W, V)).obj ω)
      ((derivedTildeStructureSheafModules Γ(W, V)).obj ω)
  have h₂ := exists_iso_and_isIso_derivedSheafHomCounit_iff_of_iso V.toScheme.sheaf a a
  have h₃ := OverEquivTensor.exists_iso_and_isIso_derivedSheafHomCounit_iff W V
    ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K)
    ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K)
  have : (OverEquivTensor.overEquivMod W V).functor.mapDerivedCategory.IsEquivalence :=
    (OverEquivTensor.overEquivDerivedEquivalence W V).isEquivalence_functor
  refine ⟨Functor.preimageIso
    (F := (OverEquivTensor.overEquivMod W V).functor.mapDerivedCategory)
    (h₃.1.some ≪≫ h₂.1.some ≪≫ h₁.1.some.symm ≪≫
      (PullbackIsoTensor.pullbackEquivMod hV.isoSpec.hom).functor.mapDerivedCategory.mapIso
        (derivedTildeDerivedSheafHomSelfUnitIso Γ(W, V) hω) ≪≫
      PullbackIsoTensor.pullbackDerivedUnitIso hV.isoSpec.hom ≪≫
      (OverEquivTensor.overEquivDerivedUnitIso W V).symm)⟩

/-- **`R𝓗om(K|_U, K|_U) ≅ 𝒪_X|_U[0]` on the slice site over an affine open.** Let `X` be a
locally Noetherian scheme, `K` a dualizing complex on `X` ([Stacks, Tag 0A87]) and `U ⊆ X` an
affine open. Over the slice site `Opens(X)/U` the derived internal hom of `K|_U` with itself is
the tensor unit, the structure sheaf in degree zero.

Over `Spec Γ(X, U)` this is `Stacks.Duality.derivedTildeDerivedSheafHomSelfUnitIso`; it is
carried to the slice site along the pullback by `U ≅ Spec Γ(X, U)` and, reflected, along
`AlgebraicGeometry.Scheme.Modules.overEquiv U`. -/
theorem nonempty_restrictDDerivedSheafHomSelfUnitIso
    {W : Scheme.{u}} [IsLocallyNoetherian W] (V : W.Opens) (hV : IsAffineOpen V)
    (K : DerivedCategory W.Modules) (hK : IsDualizingComplex K) :
    letI := RingedSite.derivedTensorMonoidal ((ringedSite W.sheaf).over V)
    Nonempty (((RingedSite.derivedSheafHomBifunctor ((ringedSite W.sheaf).over V)).obj
          (op ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD
            (ringedSite W.sheaf) V).obj K))).obj
            ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K) ≅
      𝟙_ (DerivedCategory (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite W.sheaf).over V).O)))) := by
  have : IsNoetherianRing Γ(W, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨ω, hω, ⟨i⟩⟩ := exists_isDualizingComplex_iso_overFunctor_of_isDualizingComplex V K hV hK
  exact nonempty_restrictDDerivedSheafHomSelfUnitIso_of_iso V hV hω K i

/-- **The derived internal hom of a dualizing complex with itself, on the slice site over an
affine open, is the tensor unit.** This is
`Stacks.Duality.nonempty_restrictDDerivedSheafHomSelfUnitIso` with an isomorphism chosen, in the
shape the restricted homothety consumes: it is the last parameter of
`Stacks.SheafOfModules.isIso_map_derivedSheafHomothety_of_iso_derivedSheafHom`. -/
def restrictDDerivedSheafHomSelfUnitIso {W : Scheme.{u}} [IsLocallyNoetherian W] (V : W.Opens)
    (hV : IsAffineOpen V) (K : DerivedCategory W.Modules) (hK : IsDualizingComplex K) :
    letI := RingedSite.derivedTensorMonoidal ((ringedSite W.sheaf).over V)
    ((RingedSite.derivedSheafHomBifunctor ((ringedSite W.sheaf).over V)).obj
          (op ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD
            (ringedSite W.sheaf) V).obj K))).obj
          ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD (ringedSite W.sheaf) V).obj K) ≅
      𝟙_ (DerivedCategory (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((ringedSite W.sheaf).over V).O))) :=
  (nonempty_restrictDDerivedSheafHomSelfUnitIso V hV K hK).some

end Stacks.Duality

end
