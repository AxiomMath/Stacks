module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Comparison
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian

/-!
# The extended Čech complex sits between the two models of local cohomology

Let `A` be a Noetherian ring, let `I = (f₁, …, f_r)` be an ideal of `A` and let
`Z = V(I) ⊆ Spec(A)`. For an `A`-module `M` there are canonical isomorphisms
$$ R\Gamma_I(M) \longrightarrow
   \bigl(M \to \prod_{i_0} M_{f_{i_0}} \to \prod_{i_0 < i_1} M_{f_{i_0}f_{i_1}} \to \cdots
   \to M_{f_1 \cdots f_r}\bigr) \longrightarrow R\Gamma_Z(M) $$
in `D(A)`, the middle object being the extended alternating Čech complex on `f₁, …, f_r`. This
is [Stacks, Tag 0956]; taking `M = A` gives the displayed statement for the ring itself.

Both arrows are built from comparisons the library already owns, and both are pinned by their
compatibility with the structure maps onto `M⟦0⟧`.

* The second arrow is `Stacks.LocalCohomology.cechComparisonInv`: the Čech object and `RΓ_Z(M)`
  are both coreflections of `M⟦0⟧` into the objects with `I`-power-torsion cohomology, so the
  unique map carrying the Čech augmentation to the local-cohomology counit is invertible. Only
  finite generation of `I` is used.
* The first arrow is the canonical comparison `RΓ_I ⟶ RΓ_Z` of [Stacks, Tag 0A6U] followed by
  the inverse of the second. Over a Noetherian ring that comparison is invertible, which is
  part (3) of [Stacks, Tag 0955]
  (`Dualizing.TorsionCounit.isIso_compareTorsionFunctors_app`), and this is the only
  place Noetherianness enters.

## Main definitions

* `Stacks.LocalCohomology.derivedPowerTorsionObj` — `RΓ_I(M)` as an object of `D(A)`.
* `Stacks.LocalCohomology.derivedPowerTorsionObjCounit` — its structure map onto `M⟦0⟧`.
* `Stacks.LocalCohomology.derivedPowerTorsionToExtendedCech` — the first arrow
  `RΓ_I(M) ⟶ C^•(f₁, …, f_r; M)`.
* `Stacks.LocalCohomology.extendedCechComparison` — **Tag 0956**: the two isomorphisms together
  with the identities that pin them down.

## Main results

* `Stacks.LocalCohomology.derivedPowerTorsionToExtendedCech_comp_augmentation` — the first arrow
  carries the Čech augmentation to the derived torsion structure map.
* `Stacks.LocalCohomology.isIso_derivedPowerTorsionToExtendedCech` — the first arrow is
  invertible over a Noetherian ring.
* `Stacks.LocalCohomology.isIso_cechComparisonInv` — the second arrow is invertible over any
  ring with `I` finitely generated.
* `Stacks.LocalCohomology.extendedCechComparisonSelf` — the case `M = A`, the first displayed
  line of the source.

## Implementation notes

The comparison `RΓ_I ⟶ RΓ_Z` used here is `Dualizing.compareTorsionFunctors`, the
transformation of Tag 0A6U, whose components are characterized by factoring the derived torsion
counit through the local-cohomology counit; that characterization is what makes the first
arrow's compatibility provable. The universe convention is the one forced by
`Dualizing.derivedPowerTorsion`: the ring lives in `Type u` and the modules in `Type (max u v)`.

## References

* [Stacks Project, Tag 0956](https://stacks.math.columbia.edu/tag/0956)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0A6U](https://stacks.math.columbia.edu/tag/0A6U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-! ### Derived `I`-power torsion of a module, as an object of `D(A)` -/

/-- `RΓ_I(M)`: derived `I`-power torsion applied to the module `M` placed in degree zero, viewed
in `D(A)` through the inclusion of the objects with `I`-power-torsion cohomology. -/
abbrev derivedPowerTorsionObj (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) : DerivedCategory (ModuleCat.{max u v} A) :=
  (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
    ((Dualizing.derivedPowerTorsion.{u, v} A I hI ⋙
        Dualizing.powerTorsionComparison.{u, max u v} A I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M))

/-- The structure map `RΓ_I(M) ⟶ M⟦0⟧`, that is, the counit of [Stacks, Tag 0A6L] at `M⟦0⟧`
read through the comparison functor of [Stacks, Tag 0A6N]. -/
def derivedPowerTorsionObjCounit (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) :
    derivedPowerTorsionObj.{u, v} A I hI M ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M :=
  (Dualizing.powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI).hom.app
      ((Dualizing.derivedPowerTorsion.{u, v} A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) ≫
    (Dualizing.derivedPowerTorsionCounit.{u, v} A I hI).app
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)

/-! ### The first arrow of Tag 0956 -/

/-- **The first arrow of Tag 0956.** The canonical map from `RΓ_I(M)` to the extended
alternating Čech complex `C^•(f₁, …, f_r; M)`: the comparison `RΓ_I ⟶ RΓ_Z` of
[Stacks, Tag 0A6U], followed by the identification of `RΓ_Z(M)` with the Čech object. -/
def derivedPowerTorsionToExtendedCech (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    {r : ℕ} (f : Fin r → A) (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} A) :
    derivedPowerTorsionObj.{u, v} A I hI M ⟶ extendedCechObject f M :=
  (Dualizing.derivedPowerTorsionProperty A I hI).ι.map
      ((Dualizing.compareTorsionFunctors.{u, v} A I hI).app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) ≫
    cechComparisonHom f I hI hIf M

/-- The first arrow carries the Čech augmentation to the structure map of `RΓ_I(M)`, which is
what pins it down: the Čech augmentation is universal among maps out of an object with
`I`-power-torsion cohomology. -/
theorem derivedPowerTorsionToExtendedCech_comp_augmentation (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) {r : ℕ} (f : Fin r → A) (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} A) :
    derivedPowerTorsionToExtendedCech.{u, v} A I hI f hIf M ≫ extendedCechAugmentationHom f M =
      derivedPowerTorsionObjCounit.{u, v} A I hI M := by
  exact (Category.assoc _ _ _).trans
    ((congrArg _ (cechComparisonHom_comp_augmentation f I hI hIf M)).trans
      (Dualizing.compareTorsionFunctors_app_counit.{u, v} A I hI _))

/-- **The first arrow of Tag 0956 is invertible.** Over a Noetherian ring the comparison
`RΓ_I ⟶ RΓ_Z` is an isomorphism — part (3) of [Stacks, Tag 0955] — and the identification of
`RΓ_Z(M)` with the Čech object is one by construction. -/
theorem isIso_derivedPowerTorsionToExtendedCech (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) {r : ℕ} (f : Fin r → A) (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} A) :
    IsIso (derivedPowerTorsionToExtendedCech.{u, v} A I hI f hIf M) := by
  have h1 := Dualizing.TorsionCounit.isIso_compareTorsionFunctors_app.{u, v} A I hI
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _)
    ((localCohomologyIsoCech f I hI hIf).app M).isIso_hom

/-! ### The second arrow of Tag 0956 -/

/-- **The second arrow of Tag 0956 is invertible.** The map from the Čech object to `RΓ_Z(M)`
carrying the Čech augmentation to the local-cohomology counit is an isomorphism; this needs only
finite generation of `I`. -/
theorem isIso_cechComparisonInv {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    {r : ℕ} (f : Fin r → A) (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} A) :
    IsIso (cechComparisonInv f I hI hIf M) :=
  ((localCohomologyIsoCech f I hI hIf).app M).isIso_inv

/-! ### Tag 0956 -/

/-- **Stacks 0956.** Let `A` be a Noetherian ring, let `I = (f₁, …, f_r)` be an ideal of `A` and
let `Z = V(I)`. For every `A`-module `M` there are canonical isomorphisms
`RΓ_I(M) ≅ C^•(f₁, …, f_r; M) ≅ RΓ_Z(M)` in `D(A)`, the middle term being the extended
alternating Čech complex; the first carries the Čech augmentation to the structure map of
`RΓ_I(M)` and the second carries the local-cohomology counit back to the Čech augmentation,
which is what makes the pair canonical. -/
@[stacks 0956]
def extendedCechComparison (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (hIf : Ideal.span (Set.range f) = I)
    (M : ModuleCat.{max u v} A) :
    { e : (derivedPowerTorsionObj.{u, v} A I (Ideal.fg_of_isNoetherianRing I) M ≅
              extendedCechObject f M) ×
            (extendedCechObject f M ≅
              (localCohomologyOnModules.{u, max u v} A I
                (Ideal.fg_of_isNoetherianRing I)).obj M) //
        e.1.hom ≫ extendedCechAugmentationHom f M =
            derivedPowerTorsionObjCounit.{u, v} A I (Ideal.fg_of_isNoetherianRing I) M ∧
          e.2.hom ≫ (Dualizing.localCohomologyAdjunction A I
              (Ideal.fg_of_isNoetherianRing I)).counit.app
                ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) =
            extendedCechAugmentationHom f M } :=
  ⟨(@asIso _ _ _ _ _ (isIso_derivedPowerTorsionToExtendedCech.{u, v} A I
      (Ideal.fg_of_isNoetherianRing I) f hIf M),
    @asIso _ _ _ _ _ (isIso_cechComparisonInv.{u, v} I
      (Ideal.fg_of_isNoetherianRing I) f hIf M)),
    derivedPowerTorsionToExtendedCech_comp_augmentation.{u, v} A I
      (Ideal.fg_of_isNoetherianRing I) f hIf M,
    cechComparisonInv_comp_counit f I (Ideal.fg_of_isNoetherianRing I) hIf M⟩

/-- **Stacks 0956 for the ring itself**, the first displayed line of the source: the canonical
isomorphisms `RΓ_I(A) ≅ C^•(f₁, …, f_r; A) ≅ RΓ_Z(A)` in `D(A)`. This is the case `M = A` of
`Stacks.LocalCohomology.extendedCechComparison`. -/
def extendedCechComparisonSelf (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (hIf : Ideal.span (Set.range f) = I) :
    { e : (derivedPowerTorsionObj.{u, u} A I (Ideal.fg_of_isNoetherianRing I)
              (ModuleCat.of A A) ≅
              extendedCechObject f (ModuleCat.of A A)) ×
            (extendedCechObject f (ModuleCat.of A A) ≅
              (localCohomologyOnModules.{u, u} A I
                (Ideal.fg_of_isNoetherianRing I)).obj (ModuleCat.of A A)) //
        e.1.hom ≫ extendedCechAugmentationHom f (ModuleCat.of A A) =
            derivedPowerTorsionObjCounit.{u, u} A I (Ideal.fg_of_isNoetherianRing I)
              (ModuleCat.of A A) ∧
          e.2.hom ≫ (Dualizing.localCohomologyAdjunction A I
              (Ideal.fg_of_isNoetherianRing I)).counit.app
                ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) =
            extendedCechAugmentationHom f (ModuleCat.of A A) } :=
  extendedCechComparison.{u, u} A I f hIf (ModuleCat.of A A)

end Stacks.LocalCohomology

end
