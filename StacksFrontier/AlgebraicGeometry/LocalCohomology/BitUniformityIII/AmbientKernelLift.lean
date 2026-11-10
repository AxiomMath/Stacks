module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationsKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.EpiIso
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwists
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwistShiftMultiplication
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.AbutmentIsCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistSectionsCoeffAction
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 02OS] part (3) at `q = 0`: `𝒪_X(1)` is the ideal sheaf of the exceptional divisor

Let `A` be a commutative ring, `I ⊆ A` an ideal and `X = Proj(⨁ₙ Iⁿ)` the blowup of `Spec(A)`
in `I`. The exactness field `amb_shortExact` of
`Stacks.LocalCohomology.UniformityIII.GeometricInput` was reduced in
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/BlowupTwists.lean` to one
isomorphism for each `q`,

`IsIso (kernel.lift (thickeningTwistProj I 1 q) (ambientTwistMap I q) _)`,

which at `q = 0` says that `𝒪_X(1)` and the ideal sheaf `ℐ_Y = ker(𝒪_X ⟶ 𝒪_Y)` of the
exceptional divisor are the same subsheaf of `𝒪_X` — the identification `𝒪_X(1) = 𝒪_X(-Y)` of
[Stacks, Tag 02OS] part (3). This file reduces that `q = 0` clause to a **single surjectivity**
and supplies the half of the surjectivity that is about the twists.

## Main results

* `Stacks.LocalCohomology.UniformityIII.isIso_kernelLift_ambientTwistMap_zero_of_untwisted`:
  the `q = 0` clause follows from the **untwisted** statement, about
  `ambientTwistMapZero : 𝒪_X(1) ⟶ 𝒪_X` and `ker(𝒪_X ⟶ 𝒪_{Y₁})`. The twist is removed by
  `blowupTwistZeroIsoUnit` (`𝒪_X(0) ≅ 𝒪_X`) and `thickeningTwistZeroIso`
  (`𝒪_{Yₙ}(0) ≅ 𝒪_{Yₙ}`), whose compatibility with the restriction to the exceptional divisor
  is `thickeningTwistProj_zero_comp_thickeningTwistZeroIso`.
* `Stacks.LocalCohomology.UniformityIII.isIso_kernelLift_ambientTwistMap_zero_of_epi`: the
  `q = 0` clause follows from **`Epi` of the untwisted kernel lift alone**. Both source and
  target are invertible — `Stacks.Blowup.isInvertible_blowUpTwist` ([Stacks, Tag 02NS] part (2))
  for `𝒪_X(1)` and `isInvertible_kernel_thickeningProj_one` for `ℐ_Y` — and a surjection
  between invertible sheaves of modules is an isomorphism
  (`Stacks.SheafOfModules.isIso_of_epi_of_isInvertible`). So nothing about injectivity is left
  to prove.
* `Stacks.LocalCohomology.UniformityIII.isEffectiveCartierDivisor_thickeningIdeal_one`: the
  ideal sheaf the thickenings are built from is an effective Cartier divisor, which is what
  makes `ℐ_Y` invertible. This is [Stacks, Tag 02OS] part (2) for the affine blowup
  (`Stacks.Blowup.isEffectiveCartierDivisor_comap_toSpec_ofIdealTop`) at the spelling
  `thickeningIdeal I 1`.
* `Stacks.LocalCohomology.UniformityIII.exists_app_ambientTwistMap_eq_globalSmul`: **for every
  `q`, every open `V`, every `b ∈ I` and every section `c` of `𝒪_X(q)` over `V`, the multiple
  `b·c` is the image under `𝒪_X(q+1) ⟶ 𝒪_X(q)` of a section of `𝒪_X(q+1)`** — namely of
  `b⁽¹⁾·c`. No shrinking of `V` and no chart is involved: multiplication by the degree-one
  element `b⁽¹⁾` is a *global* morphism `𝒪_X(q) ⟶ 𝒪_X(q+1)`.

  This is the converse of `Stacks.Blowup.exists_restrict_appTwistShift_eq_smul`, which says
  that the image of a section lies in `I·𝒪_X(q)` near every point. Together the two say that
  the image of `𝒪_X(q+1) ⟶ 𝒪_X(q)` is exactly `I·𝒪_X(q)`.

## What is left for the `q = 0` clause, and in what shape

Exactly this: that the ideal sheaf of the exceptional divisor is *generated* by the pulled-back
elements of `I`, on sections over each affine open. Concretely, with
`ψ_V = (Stacks.Blowup.toSpec I).appLE ⊤ V le_top ∘ (Scheme.ΓSpecIso _).inv` the pullback of
coefficients to `V`, what is needed is

`RingHom.ker ((thickeningProj I 1).val.app (op V)) ≤ Ideal.map ψ_V I` for every affine open `V`,

and nothing more. The reason is that every generator is then hit:
`exists_app_ambientTwistMapZero_eq_mul` — the untwisted form of
`exists_app_ambientTwistMap_eq_globalSmul`, see the obstruction note below — puts `ψ_V b · c`
in the image of `ambientTwistMapZero` on sections over `V` for every `b ∈ I` and every `c`, so
the image is an ideal of `Γ(X, V)` containing `ψ_V '' I`, hence containing `Ideal.map ψ_V I`.
With that, `Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections` gives the `Epi` that
`isIso_kernelLift_ambientTwistMap_zero_of_epi` consumes: a section of `ker(𝒪_X ⟶ 𝒪_{Y₁})` over
`U` restricts, on an affine open `V ∋ x` inside `U`, to an element of that kernel, and
`Stacks.SheafOfModules.injective_app_kernel_ι` turns the resulting equality in `Γ(X, V)` back
into one in the kernel.

The two inputs for the missing containment are both available and neither needs a chart:
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app` identifies the kernel on sections
over an affine open with the ideal of the ideal-sheaf datum there, and
`Stacks.IdealSheaf.ideal_comap_appLE` computes that ideal for a `comap` as `Ideal.map` of the
ideal upstairs — at `⊤` of the affine base, through `pow_one`, that is `Ideal.map ψ_V I`.

## Obstruction note: the two spellings of the index of `𝒪_X(q+1)`

`blowupTwist I (q + 1)` is `twistingSheaf (reesGrading I) ((q + 1 : ℕ) : ℤ)`, while
`Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistShiftMap` produces
`twistingSheaf (reesGrading I) ((q : ℤ) + 1)`. The two are the same sheaf, and deciding it costs
nothing **on sections** — `twistSuccSection` is the identity function and elaborates
instantly — but it is unaffordable **on morphisms**: a statement containing
`reesDegOneScalarMap I q hb ≫ ambientTwistMap I q`, whose two factors are written at the two
spellings, exhausts the 200 000-heartbeat budget at `whnf` before its proof begins, and so does
any `∃ μ : blowupTwist I q ⟶ blowupTwist I (q + 1)` whose witness is the degree-one scalar map.
Making the scalar map `irreducible` does not help; the cost is in the two `Category` instances
of the two spellings of the category of sheaves of modules on a scheme, not in the morphism.

Everything below therefore moves *sections* across the two spellings and never morphisms, which
is why `exists_app_ambientTwistMap_eq_globalSmul` is stated with `.val.app` and an existential
over sections rather than as an equation of morphisms.

The same wall stops the untwisted form `exists_app_ambientTwistMapZero_eq_mul` named above,
for a second and independent reason: the carriers `(blowupScheme I).ringCatSheaf.obj.obj (op V)`
and `(SheafOfModules.unit _).val.obj (op V)` carry no `Mul` and no `Module` instance that
instance search finds — `Stacks.RegularSequence.globalSmulCenter` itself has to supply them with
`letI : CommRing (X.ringCatSheaf.obj.obj U) := inferInstanceAs (CommRing (X.presheaf.obj U))` —
so the product `ψ_V b · c` cannot be *written* at that spelling without the same `letI`, and the
`Scheme.Modules.Hom.app`/`Γ(M, U)` spelling, which does carry the instances, does not accept
`SheafOfModules.unit (blowupScheme I).ringCatSheaf` as its `M` because the module instance is
keyed on `M : X.Modules`.

## References

* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AlgebraicGeometry.ProjEulerSequence (twistingSheafZeroIsoUnit)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistedDegree_zero)
open Stacks.RegularSequence (globalSmulCenter)

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

section Unitors

variable {C : Type*} [Category C]

section Monoidal

variable [MonoidalCategory C]

/-- For `u : 𝟙_ C ⟶ F` and `e : X ≅ 𝟙_ C`, the composite `X ≅ 𝟙_ C ⊗ X ⟶ F ⊗ X ⟶ F ⊗ 𝟙_ C ≅ F`
built from the unitors, `u ▷ X` and `F ◁ e.hom` equals `e.hom ≫ u`. -/
theorem leftUnitor_inv_whiskerRight_whiskerLeft_rightUnitor {F X : C} (u : 𝟙_ C ⟶ F)
    (e : X ≅ 𝟙_ C) :
    ((λ_ X).inv ≫ u ▷ X) ≫ (F ◁ e.hom) ≫ (ρ_ F).hom = e.hom ≫ u :=
  calc ((λ_ X).inv ≫ u ▷ X) ≫ (F ◁ e.hom) ≫ (ρ_ F).hom
      = (λ_ X).inv ≫ (u ▷ X ≫ F ◁ e.hom) ≫ (ρ_ F).hom := by simp only [Category.assoc]
    _ = (λ_ X).inv ≫ (𝟙_ C ◁ e.hom ≫ u ▷ 𝟙_ C) ≫ (ρ_ F).hom := by
          rw [← MonoidalCategory.whisker_exchange]
    _ = ((λ_ X).inv ≫ 𝟙_ C ◁ e.hom) ≫ u ▷ 𝟙_ C ≫ (ρ_ F).hom := by simp only [Category.assoc]
    _ = (e.hom ≫ (λ_ (𝟙_ C)).inv) ≫ (ρ_ (𝟙_ C)).hom ≫ u := by
          rw [← MonoidalCategory.leftUnitor_inv_naturality,
            MonoidalCategory.rightUnitor_naturality]
    _ = e.hom ≫ u := by
          simp only [Category.assoc, MonoidalCategory.unitors_inv_equal, Iso.inv_hom_id_assoc]

end Monoidal

/-- A morphism followed by an isomorphism and its inverse is the morphism. -/
theorem comp_hom_comp_inv {W X Y : C} (f : W ⟶ X) (e : X ≅ Y) :
    (f ≫ e.hom) ≫ e.inv = 𝟙 W ≫ f := by
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

/-- A commuting square of isomorphisms, read with both isomorphisms inverted. -/
theorem comp_inv_eq_inv_comp_of_sq {W X Y Z : C} (e : W ≅ X) (d : Y ≅ Z) (g : W ⟶ Y)
    (p : X ⟶ Z) (h : g ≫ d.hom = e.hom ≫ p) : p ≫ d.inv = e.inv ≫ g := by
  have hg : g = e.hom ≫ p ≫ d.inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hg, Iso.inv_hom_id_assoc]

end Unitors

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The zeroth twist of the blowup is the structure sheaf. -/
def blowupTwistZeroIsoUnit :
    blowupTwist I 0 ≅ SheafOfModules.unit (blowupScheme I).ringCatSheaf := by
  rw [show blowupTwist I 0 = twistingSheaf (Stacks.Blowup.reesGrading I) (0 : ℤ) from
    congrArg (twistingSheaf (Stacks.Blowup.reesGrading I)) Nat.cast_zero]
  exact twistingSheafZeroIsoUnit (Stacks.Blowup.reesGrading I)

/-- `𝒪_{Yₙ}(0) = 𝒪_{Yₙ}`. -/
def thickeningTwistZeroIso (n : ℕ) : thickeningTwist I n 0 ≅ thickeningSheaf I n :=
  whiskerLeftIso (thickeningSheaf I n) (blowupTwistZeroIsoUnit I) ≪≫ ρ_ (thickeningSheaf I n)

/-- The canonical `𝒪_X(0) ⟶ 𝒪_{Yₙ}(0)` is the canonical `𝒪_X ⟶ 𝒪_{Yₙ}`. -/
theorem thickeningTwistProj_zero_comp_thickeningTwistZeroIso (n : ℕ) :
    thickeningTwistProj I n 0 ≫ (thickeningTwistZeroIso I n).hom =
      (blowupTwistZeroIsoUnit I).hom ≫ thickeningProj I n :=
  leftUnitor_inv_whiskerRight_whiskerLeft_rightUnitor (thickeningProj I n)
    (blowupTwistZeroIsoUnit I)

/-- The untwisted inclusion `𝒪_X(1) ⟶ 𝒪_X`: the canonical `𝒪_X(1) ⟶ 𝒪_X(0)` read through the
identification of the zeroth twist with the structure sheaf. -/
abbrev ambientTwistMapZero : blowupTwist I 1 ⟶ SheafOfModules.unit (blowupScheme I).ringCatSheaf :=
  ambientTwistMap I 0 ≫ (blowupTwistZeroIsoUnit I).hom

/-- The composite of the untwisted inclusion `𝒪_X(1) ⟶ 𝒪_X` with the restriction
`𝒪_X ⟶ 𝒪_{Y₁}` to the exceptional divisor is zero. -/
theorem ambientTwistMapZero_comp_thickeningProj_eq_zero :
    ambientTwistMapZero I ≫ thickeningProj I 1 = 0 :=
  calc ambientTwistMapZero I ≫ thickeningProj I 1
      = ambientTwistMap I 0 ≫ ((blowupTwistZeroIsoUnit I).hom ≫ thickeningProj I 1) :=
        Category.assoc _ _ _
    _ = ambientTwistMap I 0 ≫
          (thickeningTwistProj I 1 0 ≫ (thickeningTwistZeroIso I 1).hom) :=
        congrArg (fun φ : blowupTwist I 0 ⟶ thickeningSheaf I 1 => ambientTwistMap I 0 ≫ φ)
          (thickeningTwistProj_zero_comp_thickeningTwistZeroIso I 1).symm
    _ = (ambientTwistMap I 0 ≫ thickeningTwistProj I 1 0) ≫ (thickeningTwistZeroIso I 1).hom :=
        (Category.assoc _ _ _).symm
    _ = 0 ≫ (thickeningTwistZeroIso I 1).hom :=
        congrArg (fun φ : blowupTwist I 1 ⟶ thickeningTwist I 1 0 =>
            φ ≫ (thickeningTwistZeroIso I 1).hom)
          (ambientTwistMap_comp_thickeningTwistProj_eq_zero I 0)
    _ = 0 := zero_comp

/-- **The `q = 0` clause of the exactness field, reduced to the untwisted statement.** The
canonical lift of `ambientTwistMap I 0` to the kernel of the restriction to the exceptional
divisor is an isomorphism as soon as the untwisted `𝒪_X(1) ⟶ 𝒪_X` lifts to an isomorphism onto
the ideal sheaf `ℐ_Y = ker(𝒪_X ⟶ 𝒪_Y)`. -/
theorem isIso_kernelLift_ambientTwistMap_zero_of_untwisted
    (h : IsIso (kernel.lift (thickeningProj I 1) (ambientTwistMapZero I)
      (ambientTwistMapZero_comp_thickeningProj_eq_zero I))) :
    IsIso (kernel.lift (thickeningTwistProj I 1 0) (ambientTwistMap I 0)
      (ambientTwistMap_comp_thickeningTwistProj_eq_zero I 0)) := by
  refine Stacks.Cohomology.CechSpectral.isIso_kernelLift_of_iso
    (ambientTwistMapZero_comp_thickeningProj_eq_zero I)
    (ambientTwistMap_comp_thickeningTwistProj_eq_zero I 0)
    (Iso.refl _) (blowupTwistZeroIsoUnit I).symm (thickeningTwistZeroIso I 1).symm ?_ ?_ h
  · exact comp_hom_comp_inv (ambientTwistMap I 0) (blowupTwistZeroIsoUnit I)
  · exact comp_inv_eq_inv_comp_of_sq (blowupTwistZeroIsoUnit I) (thickeningTwistZeroIso I 1)
      (thickeningTwistProj I 1 0) (thickeningProj I 1)
      (thickeningTwistProj_zero_comp_thickeningTwistZeroIso I 1)

/-! ### Both subsheaves of `𝒪_X` are invertible -/

/-- **The exceptional divisor of the blowup is an effective Cartier divisor**, at the ideal
sheaf `thickeningIdeal I 1` the thickenings are built from. This is
`Stacks.Blowup.isEffectiveCartierDivisor_comap_toSpec` ([Stacks, Tag 02OS] part (2)) at the
ideal sheaf `Spec(A)` carries canonically, with the first power unwound by `pow_one`. -/
instance isEffectiveCartierDivisor_thickeningIdeal_one :
    Stacks.Divisors.IsEffectiveCartierDivisor (thickeningIdeal I 1) := by
  have hmc : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I =
      Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom I :=
    Stacks.IdealSheaf.ideal_map_hom_eq_comap_inv (Scheme.ΓSpecIso (CommRingCat.of A)).symm I
  change Stacks.Divisors.IsEffectiveCartierDivisor
    ((Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I)).comap
        (Stacks.Blowup.toSpec I) ^ 1)
  rw [pow_one, hmc]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_toSpec_ofIdealTop I

/-- **The ideal sheaf `ℐ_Y` of the exceptional divisor is invertible**, in the spelling
`Stacks.SheafOfModules.isIso_of_epi_of_isInvertible` consumes. It is
`Stacks.Divisors.isTensorInvertible_negativeTwist` at the effective Cartier divisor above, the
negative twist of a divisor being the kernel of `𝒪_X ⟶ 𝒪_{Yₙ}` on the nose. -/
@[sga "6 VII 3.1" "special case"]
theorem isInvertible_kernel_thickeningProj_one :
    Stacks.SheafOfModules.IsInvertible (blowupScheme I).toRingedSpace.presheaf
      (structureSheafRing (blowupScheme I).toRingedSpace).property
      (kernel (thickeningProj I 1)) :=
  Stacks.Divisors.isTensorInvertible_negativeTwist (thickeningIdeal I 1)

/-- **The untwisted `q = 0` clause, reduced to surjectivity.** The canonical lift
`𝒪_X(1) ⟶ ℐ_Y` is an isomorphism as soon as it is an epimorphism: both source and target are
invertible sheaves of modules, and a surjection between invertible sheaves is an isomorphism
(`Stacks.SheafOfModules.isIso_of_epi_of_isInvertible`). -/
theorem isIso_kernelLift_ambientTwistMapZero_of_epi
    (hepi : Epi (kernel.lift (thickeningProj I 1) (ambientTwistMapZero I)
      (ambientTwistMapZero_comp_thickeningProj_eq_zero I))) :
    IsIso (kernel.lift (thickeningProj I 1) (ambientTwistMapZero I)
      (ambientTwistMapZero_comp_thickeningProj_eq_zero I)) :=
  @Stacks.SheafOfModules.isIso_of_epi_of_isInvertible (blowupScheme I).toRingedSpace
    (blowupTwist I 1) (kernel (thickeningProj I 1)) _ hepi
    (Stacks.Blowup.isInvertible_blowUpTwist I ((1 : ℕ) : ℤ))
    (isInvertible_kernel_thickeningProj_one I)

/-- **The `q = 0` clause of the exactness field, reduced to surjectivity.** -/
theorem isIso_kernelLift_ambientTwistMap_zero_of_epi
    (hepi : Epi (kernel.lift (thickeningProj I 1) (ambientTwistMapZero I)
      (ambientTwistMapZero_comp_thickeningProj_eq_zero I))) :
    IsIso (kernel.lift (thickeningTwistProj I 1 0) (ambientTwistMap I 0)
      (ambientTwistMap_comp_thickeningTwistProj_eq_zero I 0)) :=
  isIso_kernelLift_ambientTwistMap_zero_of_untwisted I
    (isIso_kernelLift_ambientTwistMapZero_of_epi I hepi)

/-! ### Multiplication by an element of `I` factors through the twist

Every statement in this section is proved for a general `q`, and not only for the `q = 0` the
clause above needs. That is not generality for its own sake: at a numeral the index of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` has two spellings — `((1 : ℕ) : ℤ)`
from `blowupTwist I 1` and `((0 : ℕ) : ℤ) + 1` from
`Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistShiftMap` — and deciding that they agree
sends the unifier into `whnf` on the twisting sheaf itself, which exhausts the heartbeat budget.
With `q` a variable the same comparison is the one `ambientTwistMap` is already declared with,
and it costs nothing. -/

/-- Equal morphisms of sheaves of modules on a scheme act equally on sections. -/
private theorem app_eq_of_eq {X : Scheme} {M N : SheafOfModules X.ringCatSheaf} {f g : M ⟶ N}
    (h : f = g) (V : X.Opens) (c : M.val.obj (op V)) :
    f.val.app (op V) c = g.val.app (op V) c := by
  rw [h]

/-- **The global section of `𝒪_X` that `b : A` pulls back to** along the blowup morphism. -/
def pullbackCoeff (b : A) : Γ(blowupScheme I, ⊤) :=
  (Stacks.Blowup.toSpec I).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)

/-- **Multiplication by `b ∈ A` on `𝒪_X(q)` is multiplication by the global function `b` pulls
back to.** This is
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_zero_eq_globalSmulCenter` at
the degree-zero scalar `Stacks.Blowup.reesConst I b`, whose values at the points of the blowup
are supplied by `val_appTop_toSpec`. -/
theorem twistScalarSheafMap_reesConst_eq_globalSmulCenter (q : ℕ) (b : A) :
    twistScalarSheafMap (Stacks.Blowup.reesGrading I) 0 (q : ℤ) (q : ℤ)
        (twistedDegree_zero (q : ℤ))
        ⟨(Stacks.Blowup.reesConst I b : reesAlgebra I),
          SetLike.algebraMap_mem_graded (Stacks.Blowup.reesGrading I) b⟩ =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app (blowupTwist I q) :=
  Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_zero_eq_globalSmulCenter
    (Stacks.Blowup.reesGrading I) (q : ℤ) _ (pullbackCoeff I b)
    (fun x => val_appTop_toSpec I b x)

/-- **Multiplication by the degree-one element `b⁽¹⁾`** attached to `b ∈ I`, as a morphism
`𝒪_X(q) ⟶ 𝒪_X(q+1)`, at the integer spelling `(q : ℤ) + 1` of the target index that
`Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistShiftMap` produces.

It is made `irreducible` immediately below, for the reason the section docstring gives: the
unifier may not be allowed to unfold a morphism of twisting sheaves while deciding that the two
spellings of the index agree, or it descends into the twisting sheaf itself. With the morphism
opaque the comparison is the first-order one `Stacks.LocalCohomology.UniformityIII.ambientTwistMap`
is already declared with. -/
def reesDegOneScalarMap (q : ℕ) {b : A} (hb : b ∈ I) :
    twistingSheaf (Stacks.Blowup.reesGrading I) (q : ℤ) ⟶
      twistingSheaf (Stacks.Blowup.reesGrading I) ((q : ℤ) + 1) :=
  twistScalarSheafMap (Stacks.Blowup.reesGrading I) 1 (q : ℤ) ((q : ℤ) + 1)
    (Stacks.Blowup.reesTwistedDegree_one (q : ℤ))
    ⟨(Stacks.Blowup.reesDegOne I hb : reesAlgebra I),
      Stacks.Blowup.reesDegOne_mem_reesGrading I hb⟩

/-- **Multiplication by `b⁽¹⁾` followed by `Stacks.Blowup.twistShiftMap` is multiplication by
`b`.** This is `Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistShiftMap` ([Stacks,
Tag 02OS] part (3) at the level of morphisms of twisting sheaves) composed with the
identification of multiplication by a degree-zero scalar with a global function. Both factors
are written at the index spellings the two cited results produce, so no comparison of spellings
happens here. -/
theorem reesDegOneScalarMap_comp_twistShiftMap (q : ℕ) {b : A} (hb : b ∈ I) :
    reesDegOneScalarMap I q hb ≫ Stacks.Blowup.twistShiftMap I (q : ℤ) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app (blowupTwist I q) :=
  (Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistShiftMap I (q : ℤ) hb).trans
    (twistScalarSheafMap_reesConst_eq_globalSmulCenter I q b)

attribute [irreducible] reesDegOneScalarMap

/-- **A section of `𝒪_X(q+1)` read at the other spelling of the index.** The two spellings
`((q + 1 : ℕ) : ℤ)` and `((q : ℤ) + 1)` give the same sheaf; on *sections* deciding that costs
nothing, which is why every statement below moves sections rather than morphisms across them. -/
def twistSuccSection (q : ℕ)
    (V : Opens (ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I)))
    (s : (twistingSheaf (Stacks.Blowup.reesGrading I) ((q : ℤ) + 1)).val.obj (op V)) :
    (blowupTwist I (q + 1)).val.obj (op V) := s

/-- **Every multiple of a pulled-back element of `I` is in the image of `𝒪_X(q+1) ⟶ 𝒪_X(q)` on
sections**, over every open and with no shrinking: the multiple of `c` by `b ∈ I` is the image
of the multiple of `c` by the degree-one element `b⁽¹⁾`.

This is the converse half of `Stacks.Blowup.exists_restrict_appTwistShift_eq_smul`, which says
that the image of a section lies in `I·𝒪_X(q)` near every point. Together they say that the
image of `𝒪_X(q+1) ⟶ 𝒪_X(q)` is exactly `I·𝒪_X(q)`. -/
theorem exists_app_ambientTwistMap_eq_globalSmul (q : ℕ) {b : A} (hb : b ∈ I)
    (V : Opens (ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I)))
    (c : (blowupTwist I q).val.obj (op V)) :
    ∃ s : (blowupTwist I (q + 1)).val.obj (op V),
      (ambientTwistMap I q).val.app (op V) s =
        ((globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app
          (blowupTwist I q)).val.app (op V) c := by
  refine ⟨twistSuccSection I q V ((reesDegOneScalarMap I q hb).val.app (op V) c), ?_⟩
  change (Stacks.Blowup.twistShiftMap I (q : ℤ)).val.app (op V)
      ((reesDegOneScalarMap I q hb).val.app (op V) c) = _
  exact app_eq_of_eq (X := blowupScheme I) (reesDegOneScalarMap_comp_twistShiftMap I q hb) V c

/-! ### The ideal sheaf of the exceptional divisor is generated by the pulled-back coefficients -/

/-- **The pullback of coefficients to an open of the blowup**: the ring map
`A ⟶ Γ(X, V)` that reads an element of `A` as a function on `V`, through the blowup morphism
`X ⟶ Spec(A)`. On `V = ⊤` its values are the `pullbackCoeff` above. -/
def coeffPullback (V : (blowupScheme I).Opens) : CommRingCat.of A ⟶ Γ(blowupScheme I, V) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Stacks.Blowup.toSpec I).appLE ⊤ V le_top

/-- **The ideal of the exceptional divisor on an affine open is generated by the pulled-back
coefficients.** On sections over an affine open `V` of the blowup, the ideal-sheaf datum of the
first thickening `Y₁` is `Ideal.map (coeffPullback I V) I`.

No chart, no cover and no locality argument enters: the thickening is cut out by the inverse
image of the ideal `I` of the affine base, and `Stacks.IdealSheaf.ideal_comap_appLE` computes the
ideal of an inverse image on *any* affine open as an `Ideal.map`, with no principality and no
nonzerodivisor hypothesis. Taking the affine open of the base to be `⊤` turns that `Ideal.map`
into the one above, by `Ideal.map_map`. -/
theorem ideal_thickeningIdeal_one (V : (blowupScheme I).Opens) (hV : IsAffineOpen V) :
    (thickeningIdeal I 1).ideal ⟨V, hV⟩ = Ideal.map (coeffPullback I V).hom I := by
  change ((Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I)).comap
        (Stacks.Blowup.toSpec I) ^ 1).ideal ⟨V, hV⟩ = _
  rw [pow_one, Stacks.IdealSheaf.ideal_comap_appLE _ _
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ ⟨V, hV⟩ le_top,
    Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map, Ideal.map_map]
  congr 1

/-- The canonical `𝒪_X ⟶ 𝒪_{Y₁}` acts on sections over an open exactly as the comorphism of the
closed immersion `Y₁ ↪ X` does. -/
theorem app_thickeningProj_one (V : (blowupScheme I).Opens) (c : Γ(blowupScheme I, V)) :
    (thickeningProj I 1).val.app (op V) c =
      ((thickeningIdeal I 1).subschemeι.app V).hom c := rfl

/-- **The kernel of `𝒪_X ⟶ 𝒪_{Y₁}` on an affine open is generated by the pulled-back
coefficients.** This is the residue of [Stacks, Tag 02OS] part (3) at `q = 0`: the ideal sheaf of
the exceptional divisor is, on sections over each affine open `V`, the ideal generated by the
image of `I` under `coeffPullback I V`.

`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app` identifies the kernel with the
ideal-sheaf datum there, and `ideal_thickeningIdeal_one` computes that datum. The containment
`≤` is the half that the surjectivity of `𝒪_X(1) ⟶ ℐ_Y` needs; the reverse containment is free
and is recorded here too. -/
theorem ker_app_subschemeι_thickeningIdeal_one (V : (blowupScheme I).Opens)
    (hV : IsAffineOpen V) :
    RingHom.ker ((thickeningIdeal I 1).subschemeι.app V).hom =
      Ideal.map (coeffPullback I V).hom I :=
  (Scheme.IdealSheafData.ker_subschemeι_app (thickeningIdeal I 1) ⟨V, hV⟩).trans
    (ideal_thickeningIdeal_one I V hV)

/-- **The containment the surjectivity needs**, in the form it is used: a section of `𝒪_X` over
an affine open that dies on the exceptional divisor lies in the ideal generated by the
pulled-back elements of `I`. -/
theorem mem_map_coeffPullback_of_app_thickeningProj_one_eq_zero (V : (blowupScheme I).Opens)
    (hV : IsAffineOpen V) (c : Γ(blowupScheme I, V))
    (hc : (thickeningProj I 1).val.app (op V) c = 0) :
    c ∈ Ideal.map (coeffPullback I V).hom I :=
  (ker_app_subschemeι_thickeningIdeal_one I V hV).le
    (RingHom.mem_ker.mpr ((app_thickeningProj_one I V c).symm.trans hc))

/-! ### Every generator is hit, and the surjectivity -/

/-- **The untwisted form of `exists_app_ambientTwistMap_eq_globalSmul`.** Over every open `V`,
every `b ∈ I` and every section `c` of `𝒪_X`, the product `coeffPullback I V b * c` is the image
under `𝒪_X(1) ⟶ 𝒪_X` of a section of `𝒪_X(1)`.

The twisted statement is read through `blowupTwistZeroIsoUnit`: multiplication by a global
function is an element of the centre of the category of `𝒪_X`-modules, so it commutes with that
isomorphism, and on the structure sheaf it is multiplication in `Γ(X, V)`. -/
theorem exists_app_ambientTwistMapZero_eq_mul {b : A} (hb : b ∈ I)
    (V : (blowupScheme I).Opens) (c : Γ(blowupScheme I, V)) :
    ∃ s : Γ(blowupTwist I 1, V),
      (ambientTwistMapZero I).app V s = (coeffPullback I V).hom b * c := by
  have h := exists_app_ambientTwistMap_eq_globalSmul I 0 hb V
    ((blowupTwistZeroIsoUnit I).inv.val.app (op V) c)
  refine ⟨h.choose, ?_⟩
  have hs := h.choose_spec
  have hnat : (blowupTwistZeroIsoUnit I).hom ≫
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app
        (SheafOfModules.unit (blowupScheme I).ringCatSheaf) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app (blowupTwist I 0) ≫
        (blowupTwistZeroIsoUnit I).hom :=
    (globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).naturality
      (blowupTwistZeroIsoUnit I).hom
  have hid : (blowupTwistZeroIsoUnit I).hom.val.app (op V)
      ((blowupTwistZeroIsoUnit I).inv.val.app (op V) c) = c :=
    app_eq_of_eq (blowupTwistZeroIsoUnit I).inv_hom_id V c
  have hmove : ((globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app
        (SheafOfModules.unit (blowupScheme I).ringCatSheaf)).val.app (op V)
        ((blowupTwistZeroIsoUnit I).hom.val.app (op V)
          ((blowupTwistZeroIsoUnit I).inv.val.app (op V) c)) =
      (blowupTwistZeroIsoUnit I).hom.val.app (op V)
        (((globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app
          (blowupTwist I 0)).val.app (op V)
          ((blowupTwistZeroIsoUnit I).inv.val.app (op V) c)) :=
    app_eq_of_eq hnat V _
  change (blowupTwistZeroIsoUnit I).hom.val.app (op V)
      ((ambientTwistMap I 0).val.app (op V) h.choose) = _
  rw [hs, ← hmove, hid]
  rfl

/-- **The sections of `𝒪_X` over `V` that come from `𝒪_X(1)`**, as an ideal of `Γ(X, V)`: the
image of `𝒪_X(1) ⟶ 𝒪_X` on sections over `V` is closed under addition and under multiplication
by any section of `𝒪_X` over `V`, because `𝒪_X(1) ⟶ 𝒪_X` is a morphism of `𝒪_X`-modules. -/
def ambientTwistImageIdeal (V : (blowupScheme I).Opens) : Ideal Γ(blowupScheme I, V) where
  carrier := {x | ∃ s : Γ(blowupTwist I 1, V), (ambientTwistMapZero I).app V s = x}
  add_mem' hx hy :=
    ⟨hx.choose + hy.choose,
      (map_add ((ambientTwistMapZero I).app V).hom hx.choose hy.choose).trans
        (congrArg₂ (· + ·) hx.choose_spec hy.choose_spec)⟩
  zero_mem' := ⟨0, map_zero ((ambientTwistMapZero I).app V).hom⟩
  smul_mem' a _ hx :=
    ⟨a • hx.choose,
      (Scheme.Modules.Hom.app_smul (ambientTwistMapZero I) a hx.choose).trans
        (congrArg (fun y : Γ(blowupScheme I, V) => a * y) hx.choose_spec)⟩

/-- **Every pulled-back element of `I` is in the image of `𝒪_X(1) ⟶ 𝒪_X`**, hence so is the whole
ideal it generates. This is `exists_app_ambientTwistMapZero_eq_mul` at `c = 1`, read through the
fact that the image is an ideal. -/
theorem map_coeffPullback_le_ambientTwistImageIdeal (V : (blowupScheme I).Opens) :
    Ideal.map (coeffPullback I V).hom I ≤ ambientTwistImageIdeal I V :=
  Ideal.map_le_iff_le_comap.mpr fun b hb =>
    let h := exists_app_ambientTwistMapZero_eq_mul I hb V 1
    ⟨h.choose, h.choose_spec.trans (mul_one ((coeffPullback I V).hom b))⟩

/-- **`𝒪_X(1) ⟶ ℐ_Y` is an epimorphism.** A section of the ideal sheaf
`ℐ_Y = ker(𝒪_X ⟶ 𝒪_{Y₁})` over an open `U` restricts, on an affine open `V ∋ x` inside `U`, to
a section of `𝒪_X` killed by `𝒪_X ⟶ 𝒪_{Y₁}`; by
`mem_map_coeffPullback_of_app_thickeningProj_one_eq_zero` it lies in the ideal generated by the
pulled-back elements of `I`, and by `map_coeffPullback_le_ambientTwistImageIdeal` it is therefore
the image of a section of `𝒪_X(1)`. The resulting equality in `Γ(X, V)` is turned back into one
in `ℐ_Y` by `Stacks.SheafOfModules.injective_app_kernel_ι`. -/
theorem epi_kernelLift_ambientTwistMapZero :
    Epi (kernel.lift (thickeningProj I 1) (ambientTwistMapZero I)
      (ambientTwistMapZero_comp_thickeningProj_eq_zero I)) := by
  refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun U t x hxU => ?_
  obtain ⟨V, hVaff, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp (blowupScheme I).isBasis_affineOpens hxU
  refine ⟨V, hVU, hxV, ?_⟩
  have hc : (thickeningProj I 1).val.app (op V)
      ((kernel.ι (thickeningProj I 1)).val.app (op V)
        ((kernel (thickeningProj I 1)).val.map (homOfLE hVU).op t)) = 0 :=
    app_eq_of_eq (kernel.condition (thickeningProj I 1)) V _
  have himg := map_coeffPullback_le_ambientTwistImageIdeal I V
    (mem_map_coeffPullback_of_app_thickeningProj_one_eq_zero I V hVaff _ hc)
  refine ⟨himg.choose, Stacks.SheafOfModules.injective_app_kernel_ι
    (thickeningProj I 1) (op V) ?_⟩
  exact (app_eq_of_eq (kernel.lift_ι (thickeningProj I 1) (ambientTwistMapZero I)
    (ambientTwistMapZero_comp_thickeningProj_eq_zero I)) V _).trans himg.choose_spec

/-- **[Stacks, Tag 02OS] part (3) at `q = 0`, unconditionally**: the canonical lift of
`𝒪_X(1) ⟶ 𝒪_X(0)` to the kernel of the restriction to the exceptional divisor is an
isomorphism. Equivalently, `𝒪_X(1)` and `ℐ_Y = ker(𝒪_X ⟶ 𝒪_Y)` are the same subsheaf of `𝒪_X`,
which is the identification `𝒪_X(1) = 𝒪_X(-Y)`.

This closes the `q = 0` clause of the exactness field `amb_shortExact` of
`Stacks.LocalCohomology.UniformityIII.GeometricInput`. -/
theorem isIso_kernelLift_ambientTwistMap_zero :
    IsIso (kernel.lift (thickeningTwistProj I 1 0) (ambientTwistMap I 0)
      (ambientTwistMap_comp_thickeningTwistProj_eq_zero I 0)) :=
  isIso_kernelLift_ambientTwistMap_zero_of_epi I (epi_kernelLift_ambientTwistMapZero I)

end Stacks.LocalCohomology.UniformityIII

end
