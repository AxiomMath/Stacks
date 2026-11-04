module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.AffineZeroSection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections

/-!
# The generator formula for the conormal sheaf of an affine surjection

Let `φ : R ⟶ S` be a surjection of commutative rings, so that `Spec φ` is a closed immersion with
ideal sheaf `(ker φ)^~`. `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.AffineZeroSection`
builds the two identifications
`Stacks.ClosedImmersion.AffineConormal.surjIdealSheafIso` and
`Stacks.ClosedImmersion.AffineConormal.surjConormalBaseChangeIso` but, as its implementation notes
record, leaves the second computing on nothing: the generator formula a consumer needs was beyond
the elaborator's budget. **This file supplies it.**

## Main results

* `Stacks.ClosedImmersion.AffineConormal.surjConormalBaseChangeIso_hom_unit_toOpen`: **the
  generator formula.** The canonical map from the ideal sheaf to the pushforward of the conormal
  sheaf — the unit of `(Spec φ)^* ⊣ (Spec φ)_*` — carries the global section of the ideal sheaf
  determined by `x : ker φ` to `1 ⊗ x`.

Because that canonical map is an epimorphism of sheaves, this formula determines
`surjConormalBaseChangeIso`; it is what makes that isomorphism *the* canonical one rather than one
of many of its type.

## Implementation notes

The obstruction recorded in `AffineZeroSection` was real, and the way past it is to **never let
the elaborator see inside the isomorphism being inverted.**

`Stacks.ClosedImmersion.AffineConormal.surjConormalBaseChangeIso` has exactly the shape of
`Stacks.ClosedImmersion.AffineConormal.conormalTildeIso`, whose generator formula
`Stacks.ClosedImmersion.AffineConormal.conormalTildeIso_hom_unit_toOpen` does go through: a
`CategoryTheory.Functor.mapIso` of the inverse of an identification of a sheaf with some `M^~`,
followed by the affine pullback comparison. What separates them is only that the identification is
`Exists.choose` in the one case and a `CategoryTheory.Iso.trans` of kernels in the other, which the
elaborator unfolds.

So `Stacks.ClosedImmersion.AffineConormal.tildeConormal_hom_unit_toOpen` below states that formula
once and for all **with the identification `Φ : M^~ ≅ N` a variable**, writing the composite out
as the `CategoryTheory.Iso.trans` it is rather than naming it. Then the instantiation at
`surjIdealSheafIso` is a single application: the only reduction it asks for is one delta-step on
`surjConormalBaseChangeIso`, and `Φ` stays an opaque local. Inside the generic proof the two
cancellation steps — `Stacks.SheafOfModules.inv_val_app_hom_val_app` and the naturality of the
unit — are projections of a free variable, so they cost nothing.

**What this device does not reach.** One neighbouring statement remains out of budget,
and the failure is the *kernel*, not the elaborator — the term is built and then
`(kernel) deterministic timeout`.

The morphism-level pinning
`(surjIdealSheafIso φ hφ).hom ≫ idealSheafι (Spec φ)
= tilde.map (ker φ).subtype ≫ tildeSelf.hom`
**is proved**, as
`Stacks.ClosedImmersion.AffineConormal.surjIdealSheafIso_hom_comp_idealSheafι`, but not in the
most obvious shape. Stated about an explicit composite it is out of the kernel's
budget however the proof is assembled; stated about an existentially bound isomorphism it is
cheap, and `surjIdealSheafIso` is defined from that existence statement. See the implementation
notes of `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.AffineZeroSection` for the
details and for why the isomorphism being an `Exists.choose` is what makes both this pinning
and the generator formula above affordable.

* *Restating* the generator formula for the zero section of `𝐀(K) = Spec (Sym_A K)`, i.e. at
  `φ := Stacks.ProjectiveBundleConormal.augRingHom A K`, in the vocabulary of
  `Stacks.ProjectiveBundleConormal.conormalZeroSectionBaseChangeIso`. The obstruction is the type
  conversion and not the mathematics: `Stacks.ProjectiveBundleConormal.augIdealModule` is
  `ModuleCat.of _ (augIdeal A K)` where the generic statement produces
  `ModuleCat.of _ (RingHom.ker (augRingHom A K).hom)`, and asking the kernel to identify the two
  makes it unfold `Sym_A(K)`. A consumer needing the zero-section case should therefore **apply
  `surjConormalBaseChangeIso_hom_unit_toOpen` at `augRingHom A K` directly**, with
  `Stacks.ProjectiveBundleConormal.algebraMapInv_surjective` for surjectivity, and never restate
  it.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
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

/-! ### The generator formula with the ideal-sheaf identification a variable -/

/-- **The generator formula for the affine pullback of a sheaf identified with `M^~`.** Let
`φ : R ⟶ S` be a ring map, `M` an `R`-module and `Φ : M^~ ≅ N` an identification of `M^~` with a
sheaf `N` on `Spec R`. Then the composite that carries a global section of `N` to a global section
of `(S ⊗_R M)^~` — the unit of `(Spec φ)^* ⊣ (Spec φ)_*`, then `(Spec φ)^* Φ⁻¹`, then the affine
pullback comparison of [Stacks Project, Tag 01I9] — sends `Φ` of the section determined by `x : M`
to `1 ⊗ x`.

Every object here is a variable; see the module docstring for why that is the whole point. -/
theorem tildeConormal_hom_unit_toOpen (R S : CommRingCat.{u}) (φ : R ⟶ S) (M : ModuleCat.{u} R)
    {N : (Spec R).Modules} (Φ : tilde M ≅ N) (x : M) :
    ((Scheme.Modules.pullback (Spec.map φ)).mapIso Φ.symm ≪≫
          (pullbackTildeIso R S φ).app M).hom.val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app N).val.app (.op ⊤)
          (Φ.hom.val.app (.op ⊤) (tilde.toOpen M ⊤ x))) =
      tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤ ((1 : S) ⊗ₜ[R, φ.hom] x) := by
  have hinv : Φ.inv.val.app (.op ⊤) (Φ.hom.val.app (.op ⊤) (tilde.toOpen M ⊤ x)) =
      tilde.toOpen M ⊤ x :=
    Stacks.SheafOfModules.inv_val_app_hom_val_app Φ (.op ⊤) (tilde.toOpen M ⊤ x)
  have hnat : ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
        (tilde M)).val.app (.op ⊤)
        (Φ.inv.val.app (.op ⊤) (Φ.hom.val.app (.op ⊤) (tilde.toOpen M ⊤ x))) =
      ((Scheme.Modules.pullback (Spec.map φ)).map Φ.inv).val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app N).val.app (.op ⊤)
          (Φ.hom.val.app (.op ⊤) (tilde.toOpen M ⊤ x))) :=
    congr($((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality
        Φ.inv).val.app (.op ⊤) (Φ.hom.val.app (.op ⊤) (tilde.toOpen M ⊤ x)))
  exact (congrArg (fun z => ((pullbackTildeIso R S φ).hom.app M).val.app (.op ⊤) z)
    (hnat.symm.trans (congrArg
      (fun z => ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
        (tilde M)).val.app (.op ⊤) z) hinv))).trans
    (pullbackTildeIso_hom_app_unit_toOpen R S φ M x)

/-! ### The generator formula for a surjection -/

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : Function.Surjective φ.hom)

/-- **The generator formula for the conormal sheaf of `Spec φ`, for `φ : R ⟶ S` a surjection.**
The canonical map from the ideal sheaf to the pushforward of the conormal sheaf — the unit of
`(Spec φ)^* ⊣ (Spec φ)_*` — carries the global section of the ideal sheaf determined by
`x : ker φ` to `1 ⊗ x`.

Because that canonical map is an epimorphism of sheaves, this determines
`Stacks.ClosedImmersion.AffineConormal.surjConormalBaseChangeIso`; it is the normalisation
`AffineZeroSection` leaves open, and the one a consumer computes with. -/
theorem surjConormalBaseChangeIso_hom_unit_toOpen (x : RingHom.ker φ.hom) :
    (surjConormalBaseChangeIso φ hφ).hom.val.app (.op ⊤)
        (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            (idealSheaf (Spec.map φ).toLRSHom.toShHom)).val.app (.op ⊤)
          ((surjIdealSheafIso φ hφ).hom.val.app (.op ⊤)
            (tilde.toOpen (ModuleCat.of R (RingHom.ker φ.hom)) ⊤ x))) =
      tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj
        (ModuleCat.of R (RingHom.ker φ.hom))) ⊤ ((1 : S) ⊗ₜ[R, φ.hom] x) :=
  tildeConormal_hom_unit_toOpen R S φ (ModuleCat.of R (RingHom.ker φ.hom))
    (surjIdealSheafIso φ hφ) x

end Stacks.ClosedImmersion.AffineConormal

end
