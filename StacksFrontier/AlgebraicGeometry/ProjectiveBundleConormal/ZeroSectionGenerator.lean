module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.AffineGenerator
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generator formula for the conormal sheaf of the zero section of an affine bundle

`Stacks.ProjectiveBundleConormal.conormalZeroSectionTildeIso` identifies the conormal sheaf of the
zero section of the affine bundle `𝐀(K) = Spec (Sym_A K)` with `K^~`, and
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.AffineGenerator` supplies the generator
formula for its first factor — the base-change form `A ⊗_{Sym_A K} I` — but stops there. **This
file carries the formula across the second factor**, so that the conormal sheaf of the zero
section is `K^~` *with its normalisation*: the canonical global section named by an element `x` of
the augmentation ideal goes to the section of `K^~` named by the derivative
`SymmetricAlgebra.augDeriv x` of `x` at the origin.

That normalisation is what a consumer needs. The comparison of [Stacks, Tag 0B3V] clause 3 is
pinned by its effect on the generators of the ideal sheaf, so identifying its target with `K^~` is
only useful together with a description of where those generators go.

## Main results

* `Stacks.ClosedImmersion.AffineConormal.tildeConormalExtendScalars_hom_unit_toOpen`: **the
  generic formula.** For a ring map `φ : R ⟶ S`, an `R`-module `M`, an identification `Φ` of `M^~`
  with a sheaf `N` on `Spec R` and an identification `Ψ` of `S ⊗_R M` with an `S`-module `P`, the
  unit of `(Spec φ)^* ⊣ (Spec φ)_*` followed by `(Spec φ)^*Φ⁻¹`, the affine pullback comparison
  and `Ψ^~` carries `Φ` of the section named by `x : M` to the section of `P^~` named by
  `Ψ (1 ⊗ x)`.
* `Stacks.ProjectiveBundleConormal.conormalZeroSectionTildeIso_hom_unit_toOpen`: **the zero
  section of `𝐀(K)`**, where `Φ` is `Stacks.ProjectiveBundleConormal.zeroSectionIdealSheafIso`,
  `Ψ` is `Stacks.ProjectiveBundleConormal.augExtendScalarsIso`, and `Ψ (1 ⊗ x)` is the derivative
  at the origin by `Stacks.ProjectiveBundleConormal.augExtendHom_one_tmul`.

## Implementation notes

**Everything is a variable, including the module.** This is the device of
`Stacks.ClosedImmersion.AffineConormal.tildeConormal_hom_unit_toOpen`, carried one leg further,
and here it is not a convenience but the only thing that works.

`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.AffineGenerator` records that
restating its generator formula at the augmentation is beyond the kernel, because
`Stacks.ProjectiveBundleConormal.augIdealModule` is `ModuleCat.of _ (augIdeal A K)` where the
generic statement produces `ModuleCat.of _ (RingHom.ker (augRingHom A K).hom)`. **That obstruction
is reproduced here, and located.** Building the second leg on
`Stacks.ClosedImmersion.AffineConormal.surjConormalBaseChangeIso_hom_unit_toOpen` — whose module
slot is fixed to the `RingHom.ker` spelling — and then instantiating it at the augmentation is a
`(kernel) deterministic timeout`, even when the statement never mentions
`SymmetricAlgebra.augDeriv` and the only crossing is passing `augExtendScalarsIso` for `Ψ`: the
kernel is asked to identify the two spellings inside a whole `CategoryTheory.Iso` type and unfolds
`Sym_A(K)` doing it.

Taking the module `M` as a *variable* removes the crossing instead of paying it. The zero-section
instance is then read entirely in the development's own `augIdeal` vocabulary — `M` is
`augIdealModule A K`, `Φ` is `zeroSectionIdealSheafIso A K` and `Ψ` is `augExtendScalarsIso A K`,
each already stated at that spelling — and the only two reductions asked for are the delta-steps
on `conormalZeroSectionBaseChangeIso` and `surjConormalBaseChangeIso`. The whole file then checks
in under two seconds.

`conormalZeroSectionTildeIso_hom_val_app` names the two-fold split of the composite so that the
instantiation does not have to perform it inside a larger term; a two-fold `CategoryTheory.Iso`
split is `rfl` and free, which is why `conormalZeroSectionTildeIso` is built as one.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open RingedSpaceModuleAdjunction
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine
open scoped ChangeOfRings

universe u

namespace Stacks.ClosedImmersion.AffineConormal

/-- **`tilde.map` read on the canonical global sections**: the section named by `x` goes to the
section named by the image of `x`. This is `AlgebraicGeometry.tilde.toOpen_map_app` applied to an
element. -/
theorem tilde_map_toOpen_top {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : M) :
    ((tilde.functor R).map f).val.app (.op ⊤) (tilde.toOpen M ⊤ x) =
      tilde.toOpen N ⊤ (f x) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤) x

/-- **The generator formula for the affine pullback of a sheaf identified with `M^~`, read through
an identification of the base change.** Let `φ : R ⟶ S` be a ring map, `M` an `R`-module,
`Φ : M^~ ≅ N` an identification of `M^~` with a sheaf on `Spec R`, and
`Ψ : S ⊗_R M ≅ P` an identification of the base change with an `S`-module. Then the composite
carrying a global section of `N` to a global section of `P^~` — the unit of
`(Spec φ)^* ⊣ (Spec φ)_*`, then `(Spec φ)^*Φ⁻¹`, then the affine pullback comparison of
[Stacks Project, Tag 01I9], then `Ψ^~` — sends `Φ` of the section named by `x : M` to the section
named by `Ψ (1 ⊗ x)`.

This is `Stacks.ClosedImmersion.AffineConormal.tildeConormal_hom_unit_toOpen` with one more leg,
and like it every object is a variable; see the module docstring for why that is the whole
point. -/
theorem tildeConormalExtendScalars_hom_unit_toOpen (R S : CommRingCat.{u}) (φ : R ⟶ S)
    (M : ModuleCat.{u} R) {N : (Spec R).Modules} (Φ : tilde M ≅ N)
    {P : ModuleCat.{u} S} (Ψ : (ModuleCat.extendScalars φ.hom).obj M ≅ P) (x : M) :
    ((tilde.functor S).map Ψ.hom).val.app (.op ⊤)
        (((Scheme.Modules.pullback (Spec.map φ)).mapIso Φ.symm ≪≫
              (pullbackTildeIso R S φ).app M).hom.val.app (.op ⊤)
          (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app N).val.app
              (.op ⊤)
            (Φ.hom.val.app (.op ⊤) (tilde.toOpen M ⊤ x)))) =
      tilde.toOpen P ⊤ (Ψ.hom ((1 : S) ⊗ₜ[R, φ.hom] x)) :=
  (congrArg (fun z => ((tilde.functor S).map Ψ.hom).val.app (.op ⊤) z)
      (tildeConormal_hom_unit_toOpen R S φ M Φ x)).trans
    (tilde_map_toOpen_top Ψ.hom _)

end Stacks.ClosedImmersion.AffineConormal

namespace Stacks.ProjectiveBundleConormal

open SymmetricAlgebra
open scoped ChangeOfRings

variable (A K : Type u) [CommRing A] [AddCommGroup K] [Module A K]

/-- **`conormalZeroSectionTildeIso` read on a local section**: its two factors, applied in turn.
The composite is a two-fold `CategoryTheory.Iso.trans`, so the split is `rfl`; naming it keeps the
generator formula below from having to perform the split inside a larger term. -/
theorem conormalZeroSectionTildeIso_hom_val_app (V : (Spec (CommRingCat.of A)).Opensᵒᵖ)
    (z : (conormalSheaf (zeroSection A K).toLRSHom.toShHom).val.obj V) :
    (conormalZeroSectionTildeIso A K).hom.val.app V z =
      ((tilde.functor (CommRingCat.of A)).map (augExtendScalarsIso A K).hom).val.app V
        ((conormalZeroSectionBaseChangeIso A K).hom.val.app V z) :=
  rfl

/-- **The conormal sheaf of the zero section of `𝐀(K)` is `K^~`, normalised by the derivative at
the origin.** The canonical map from the ideal sheaf of the zero section to the pushforward of its
conormal sheaf — the unit of `(zeroSection)^* ⊣ (zeroSection)_*` — followed by
`Stacks.ProjectiveBundleConormal.conormalZeroSectionTildeIso` carries the global section of the
ideal sheaf named by `x` in the augmentation ideal to the global section of `K^~` named by
`SymmetricAlgebra.augDeriv x`.

Since that canonical map is an epimorphism of sheaves, this formula determines
`conormalZeroSectionTildeIso`: it is what makes the identification of the conormal sheaf of the
zero section with `K` *the* canonical one rather than one of many of its type, and it is the form
in which clause 3 of [Stacks, Tag 0B3V] consumes it on a chart.

It is `Stacks.ClosedImmersion.AffineConormal.tildeConormalExtendScalars_hom_unit_toOpen` at the
augmentation, with `Stacks.ProjectiveBundleConormal.augExtendHom_one_tmul` computing
`Ψ (1 ⊗ x)`. -/
@[ega "II 8.9.3" "clause j*(J)=L"]
theorem conormalZeroSectionTildeIso_hom_unit_toOpen (x : augIdealOf A K) :
    (conormalZeroSectionTildeIso A K).hom.val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (zeroSection A K)).unit.app
            (idealSheaf (zeroSection A K).toLRSHom.toShHom)).val.app (.op ⊤)
          ((zeroSectionIdealSheafIso A K).hom.val.app (.op ⊤)
            (tilde.toOpen (augIdealModule A K) ⊤ x))) =
      tilde.toOpen (ModuleCat.of (CommRingCat.of A) K) ⊤
        (augDeriv (x : SymmetricAlgebra A K)) :=
  (conormalZeroSectionTildeIso_hom_val_app A K _ _).trans
    ((tildeConormalExtendScalars_hom_unit_toOpen (symRing A K) (CommRingCat.of A)
          (augRingHom A K) (augIdealModule A K) (zeroSectionIdealSheafIso A K)
          (augExtendScalarsIso A K) x).trans
      (congrArg (fun y => tilde.toOpen (ModuleCat.of (CommRingCat.of A) K) ⊤ y)
        (augExtendHom_one_tmul A K x)))

end Stacks.ProjectiveBundleConormal

end
