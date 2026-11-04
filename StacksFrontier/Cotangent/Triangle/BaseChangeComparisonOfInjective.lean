module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.Triangle.BaseChangeComparison
public import StacksFrontier.Cotangent.Triangle.BaseChangeLegTensor

/-!
# Remark 08SE at the source's hypotheses

Let `A → B → C` be ring maps with `B → C` injective, let `P_•`, `Q_•` be the standard
resolutions of `B` and of `C` over `A`, `R_•` the standard resolution of `C` over `B`, `S_•` the
standard resolution of `B` over `B`, and put `Q̄_• = Q_• ⊗_{P_•} B` and `R̄_• = R_• ⊗_{S_•} B`.
[Stacks, Remark 08SE] says:

* `R̄_•` is a simplicial polynomial algebra over `B` and `R̄_• → C` is a resolution;
* the two maps
  `L_{C/B} = Ω[R_•⁄B] ⊗_{R_•} C ⟶ Ω[R̄_•⁄B] ⊗_{R̄_•} C ⟵ Ω[Q̄_•⁄B] ⊗_{Q̄_•} C`
  are quasi-isomorphisms;
* composing one with the inverse of the other identifies `Ω[Q̄_•⁄B] ⊗_{Q̄_•} C` with `L_{C/B}`.

The construction of the two maps, of the identification, and the proofs that the maps become
isomorphisms in `D(C)` once both augmentations are resolutions, are in
`StacksFrontier/Cotangent/Triangle/BaseChangeComparison.lean`. The facts that `Q̄_• → C` and
`R̄_• → C` are resolutions, which the source deduces from Cohomology on Sites, Lemma 08RX
applied to `𝒞 = Δ`, are proved in `StacksFrontier/Cotangent/Triangle/BaseChangeLegTensor.lean`
(`CommAlgCat.trivialKanFibrations_baseChangedStandardResolution_of_injective` and
`CommAlgCat.trivialKanFibrations_relativeBaseChange_of_injective`). This file combines the two, so
every statement below assumes exactly what the remark assumes: that `B → C` is injective.

## Main results

* `CommAlgCat.isResolution_relativeBaseChange_of_injective`: `R̄_• → C` is a resolution of `C`
  over `B`.
* `CommAlgCat.isIso_q_relativeBaseChangeCotangentLeg_of_injective`: the first map is a
  quasi-isomorphism.
* `CommAlgCat.isIso_q_baseChangedCotangentComparison_of_injective`: the second map is a
  quasi-isomorphism.
* `CommAlgCat.baseChangedCotangentComplexIsoOfInjective` (in `BaseChangeLegTensor.lean`, registered
  here): the identification.
* `CommAlgCat.baseChangedCotangentComplexIsoOfInjective_hom_comp` and
  `CommAlgCat.eq_baseChangedCotangentComplexIsoOfInjective`: the identification composed with the
  first map is the second, and it is the only isomorphism with this property.

## References

* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE)
* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B C : CommAlgCat.{u} A}

attribute [local instance] HasDerivedCategory.standard

/-- **`R̄_• = R_• ⊗_{S_•} B` is a resolution of `C` over `B`** when `B → C` is injective: each
`R̄_n` is a polynomial algebra over `B` and the augmentation `R̄_• → C` is a trivial Kan
fibration. `R̄_•` is the base-changed standard resolution at the base ring `B` and the map
`CommAlgCat.overBase f`, so this is
`CommAlgCat.isResolution_baseChangedStandardResolution_of_injective` there. -/
@[stacks 08SE "R_bullet ⊗_{S_bullet} B is a simplicial polynomial algebra over B and \
  R_bullet ⊗_{S_bullet} B → C is a resolution, for B → C injective"]
theorem isResolution_relativeBaseChange_of_injective (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    @IsResolution ↥B B.commRing ↥(relativeBaseChange f).right
      (relativeBaseChange f).right.commRing (relativeBaseChange f).right.algebra
      (relativeBaseChange f).left (relativeBaseChange f).hom :=
  isResolution_baseChangedStandardResolution_of_injective (overBase f) hf

/-- **The first map of Remark 08SE is a quasi-isomorphism**:
`L_{C/B} = Ω[R_•⁄B] ⊗_{R_•} C ⟶ Ω[R̄_•⁄B] ⊗_{R̄_•} C` becomes an isomorphism in `D(C)` for
`B → C` injective. -/
@[stacks 08SE "the map L_{C/B} = Omega[R_bullet/B] ⊗ C ⟶ Omega[R_bullet ⊗_{S_bullet} B / B] ⊗ C \
  is a quasi-isomorphism, for B → C injective"]
theorem isIso_q_relativeBaseChangeCotangentLeg_of_injective (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    IsIso (DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f)) :=
  isIso_q_relativeBaseChangeCotangentLeg f hf
    (trivialKanFibrations_relativeBaseChange_of_injective f hf)

/-- **The second map of Remark 08SE is a quasi-isomorphism**:
`Ω[Q̄_•⁄B] ⊗_{Q̄_•} C ⟶ Ω[R̄_•⁄B] ⊗_{R̄_•} C` becomes an isomorphism in `D(C)` for `B → C`
injective. -/
@[stacks 08SE "the map Omega[Q_bullet ⊗_{P_bullet} B / B] ⊗ C ⟶ \
  Omega[R_bullet ⊗_{S_bullet} B / B] ⊗ C is a quasi-isomorphism, for B → C injective"]
theorem isIso_q_baseChangedCotangentComparison_of_injective (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    IsIso (DerivedCategory.Q.map (baseChangedCotangentComparison f)) :=
  isIso_q_baseChangedCotangentComparison f hf
    (trivialKanFibrations_baseChangedStandardResolution_of_injective f hf)
    (trivialKanFibrations_relativeBaseChange_of_injective f hf)

add_to_stacks 08SE "the canonical identification of Omega[Q_bullet ⊗_{P_bullet} B / B] ⊗ C with \
  L_{C/B} = Omega[R_bullet/B] ⊗ C in D(C), for B → C injective: the second map of the comparison \
  followed by the inverse of the first"
  CommAlgCat.baseChangedCotangentComplexIsoOfInjective

/-- **The identification of Remark 08SE is the second map composed with the inverse of the
first**: followed by the first map it is the second. -/
@[stacks 08SE "the identification composed with the first map of the comparison is the second, \
  for B → C injective"]
theorem baseChangedCotangentComplexIsoOfInjective_hom_comp (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    (baseChangedCotangentComplexIsoOfInjective f hf).hom ≫
        DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f) =
      DerivedCategory.Q.map (baseChangedCotangentComparison f) :=
  baseChangedCotangentComplexIso_hom_comp f hf _ _

/-- **The identification of Remark 08SE is canonical**: it is the only isomorphism
`Ω[Q̄_•⁄B] ⊗_{Q̄_•} C ≅ L_{C/B}` in `D(C)` whose composite with the first map of the comparison is
the second. -/
@[stacks 08SE "uniqueness of the identification: the only isomorphism whose composite with the \
  first map of the comparison is the second, for B → C injective"]
theorem eq_baseChangedCotangentComplexIsoOfInjective (f : B ⟶ C)
    (hf : Function.Injective f.hom)
    (e : DerivedCategory.Q.obj
        (augmentedCotangentCochainComplex (baseChangedStandardResolution A f).hom) ≅
      DerivedCategory.Q.obj (cotangentComplex ↥B (algebraOver f)))
    (he : e.hom ≫ DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f) =
      DerivedCategory.Q.map (baseChangedCotangentComparison f)) :
    e = baseChangedCotangentComplexIsoOfInjective f hf :=
  eq_baseChangedCotangentComplexIso f hf _ _ e he

end CommAlgCat

end
