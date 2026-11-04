module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Comparison

/-!
# The extended Čech complex computes local cohomology with closed support

Let `A` be a Noetherian ring, let `f₁, …, f_r` generate an ideal `I ⊆ A`, and let
`Z = V(I) ⊆ Spec(A)`. For an `A`-module `M` the extended alternating Čech complex
$$ M \longrightarrow \bigoplus_i M_{f_i} \longrightarrow \bigoplus_{i < j} M_{f_i f_j}
   \longrightarrow \cdots \longrightarrow M_{f_1 \cdots f_r} $$
is isomorphic in `D(A)` to local cohomology `RΓ_Z(M)`, by an isomorphism carrying the
augmentation of the Čech complex onto the canonical map `RΓ_Z(M) → M`.

This is the second displayed isomorphism of [Stacks, Tag 0956], and it is the comparison
already built by the Čech model of chapter 51: both the Čech object and `RΓ_Z(M)` are
coreflections of `M` into the complexes with `I`-power-torsion cohomology, so there is a
unique isomorphism between them over `M`. What this file does is name that isomorphism at the
shape Tag 0956 asks for — the isomorphism bundled with its compatibility, which is exactly
what `Stacks.LocalCohomology.cechComparisonInv` and
`Stacks.LocalCohomology.cechComparisonInv_comp_counit` provide.

Noetherianness enters only through `Ideal.fg_of_isNoetherianRing`: the underlying comparison
needs no more than finite generation of `I`, which is why the general form is recorded first.

## Main results

* `Stacks.Duality.extendedCechIsoLocalCohomologyOfFG` — the isomorphism
  `C^•(f₁, …, f_r; M) ≅ RΓ_{V(I)}(M)` in `D(A)` for a finitely generated `I`, compatible with
  the canonical maps to `M`.
* `Stacks.Duality.extendedCechIsoLocalCohomology` — the same for a Noetherian ring, the form
  of [Stacks, Tag 0956].

## Implementation notes

Nothing is rebuilt here. The Čech complex, its image in `D(A)` and its augmentation are the
library's `Stacks.LocalCohomology.extendedCechComplex`, `extendedCechObject` and
`extendedCechAugmentationHom`, and the comparison is the library's `cechComparisonInv`, whose
characterizing identity is the compatibility asserted by the source.

## References

* [Stacks Project, Tag 0956](https://stacks.math.columbia.edu/tag/0956)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.Duality

/-- **The Čech model as an isomorphism over the module.** For a finitely generated ideal
`I = (f₁, …, f_r)` of `A` and an `A`-module `M`, the extended alternating Čech complex is
isomorphic in `D(A)` to local cohomology `RΓ_{V(I)}(M)`, by the unique isomorphism whose
composite with the counit is the Čech augmentation. -/
noncomputable def extendedCechIsoLocalCohomologyOfFG
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) {n : ℕ} (f : Fin n → A)
    (hf : I = Ideal.span (Set.range f)) :
    { e : Stacks.LocalCohomology.extendedCechObject f M ≅
        (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
          ((Dualizing.localCohomologyFunctor A I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) //
      e.hom ≫
        (Dualizing.localCohomologyAdjunction A I hI).counit.app
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) =
        Stacks.LocalCohomology.extendedCechAugmentationHom f M } :=
  ⟨((Stacks.LocalCohomology.localCohomologyIsoCech.{v} f I hI hf.symm).app M).symm,
    Stacks.LocalCohomology.cechComparisonInv_comp_counit f I hI hf.symm M⟩

/-- **Stacks 0956.** The extended Čech complex canonically computes local cohomology with
support in `V(I)`; the isomorphism respects the canonical maps to the original module. -/
-- NO `@[stacks 0956]` ATTRIBUTE HERE, DELIBERATELY. The covering set of 0956 has
-- 3 declarations and this library has 1: `compareTorsionFunctors_app_isIso` and
-- `derivedPowerTorsionIsoExtendedCech` are not proved, so an attribute here would mark the
-- whole of 0956 formalized on one third of its covering set. The attribute belongs here
-- once Stacks 0955(1) is proved and the other two declarations follow.
noncomputable def extendedCechIsoLocalCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{max u v} A) {n : ℕ} (f : Fin n → A)
    (hf : I = Ideal.span (Set.range f)) :
    { e : Stacks.LocalCohomology.extendedCechObject f M ≅
        (Dualizing.derivedPowerTorsionProperty A I
          (Ideal.fg_of_isNoetherianRing I)).ι.obj
          ((Dualizing.localCohomologyFunctor A I
            (Ideal.fg_of_isNoetherianRing I)).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) //
      e.hom ≫
        (Dualizing.localCohomologyAdjunction A I
          (Ideal.fg_of_isNoetherianRing I)).counit.app
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) =
        Stacks.LocalCohomology.extendedCechAugmentationHom f M } :=
  extendedCechIsoLocalCohomologyOfFG.{u, v} A I (Ideal.fg_of_isNoetherianRing I) M f hf

end Stacks.Duality

end
