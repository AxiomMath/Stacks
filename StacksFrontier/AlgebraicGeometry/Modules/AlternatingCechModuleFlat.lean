module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenStalkExactness
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Termwise flatness of the alternating Čech complex

Let `f : X ⟶ Spec A` be a separated morphism, let `F` be a quasi-coherent `𝒪_X`-module which
is flat over the base, and let `U : I → X.Opens` be a finite family of affine opens. This file
proves that every term of the alternating Čech complex of `F` with respect to `U` is a flat
`A`-module.

## Main results

* `Stacks.Cech.sections_flat`: the sections of `F` over an affine open are a flat `A`-module.
* `Stacks.Cech.inter_isAffineOpen`: a finite intersection of affine opens of a scheme separated
  over an affine base is affine.
* `Stacks.Cech.alternatingCechModuleComplex_flat`: every term of the alternating Čech complex
  is flat over `A`.

## Implementation notes

**The alternating cochains are flat because they are the *ordered* cochains.** The alternating
submodule is not visibly a direct summand of all cochains — antisymmetrisation would need
division by `p!` — so flatness is not read off the product. Instead Stacks 01FJ identifies the
alternating cochains with the cochains indexed by strictly increasing tuples, a *finite
product* of modules of sections, and finite products of flat modules are flat. Only the
*inverse* of that identification is needed here, and the inverse is the restriction of indices
`CechCochains.pi`, whose `A`-linearity is `rfl`; `LinearEquiv.ofBijective` then upgrades it to a
linear equivalence using only the additive bijectivity of Stacks 01FJ. Proving that
`CechCochains.c` itself is `A`-linear is therefore not needed. The strict order on `I` is chosen
in the proof — `linearOrderOfSTO WellOrderingRel` — since the statement does not mention it.

**Flatness of the sections.** `AlgebraicGeometry.IsFlatOver` is a condition on stalks, and the
passage to sections over an affine open is `AlgebraicGeometry.isFlatOver_tfae`, items (1) and
(2). That gives flatness over `Γ(Spec A, ⊤)` rather than over `A`, and the two are identified
by `AlgebraicGeometry.toSpecΓ`, an isomorphism; `Stacks.RingTheory.Flat.flat_of_ringEquiv`
transports flatness along it. The `RingEquiv` must be introduced by a `let` with an ascribed
type, because `toSpecΓ` presents its codomain in a different — `rfl`-equal — spelling from the
`Γ(Spec A, ⊤)` that `isFlatOver_tfae` produces, and the unpinned spelling is not the one the
`Module` instance is registered at.

**Affineness of the intersections.** `AlgebraicGeometry.IsAffineOpen.iInf` asks for the
diagonal of the morphism to the terminal scheme to be affine, i.e. for `X` to be separated
absolutely, whereas the hypothesis here is that `f` is separated. Since `Spec A` is affine it
is separated over the terminal scheme, and separatedness is stable under composition, so
factoring `terminal.from X` through `f` supplies the instance.

## References

* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Cech

/-! ### Two ingredients of independent interest -/

/-- A finite product of flat modules is flat. -/
theorem flat_pi_of_finite {R : Type*} [CommRing R] {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Flat R (M i)] :
    Module.Flat R (∀ i, M i) := by
  classical
  let := Fintype.ofFinite ι
  exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R)).symm

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

variable {I : Type u} (U : I → X.Opens) (F : X.Modules)

/-- **The sections of a flat quasi-coherent module over an affine open are flat over the
base.** -/
theorem sections_flat [F.IsQuasicoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (W : X.Opens) (hW : IsAffineOpen W) :
    letI := sectionsModule f F W
    Module.Flat A Γ(F, W) := by
  let := sectionsModule f F W
  let : Module Γ(Spec (CommRingCat.of A), ⊤) Γ(F, W) :=
    Module.compHom _ (f.appLE ⊤ W (by simp)).hom
  have h2 := ((isFlatOver_tfae f F).out 1 2).mp hflat
  have h : Module.Flat Γ(Spec (CommRingCat.of A), ⊤) Γ(F, W) :=
    h2 W hW ⊤ (isAffineOpen_top _) (by simp)
  let e : A ≃+* Γ(Spec (CommRingCat.of A), ⊤) :=
    (asIso (toSpecΓ (CommRingCat.of A))).commRingCatIsoToRingEquiv
  refine Stacks.RingTheory.Flat.flat_of_ringEquiv e.symm fun b x => ?_
  have key : (toSpecΓ (CommRingCat.of A)).hom (e.symm b) = b := e.apply_symm_apply b
  change (f.appLE ⊤ W (by simp)).hom b • x =
    (f.appLE ⊤ W (by simp)).hom ((toSpecΓ (CommRingCat.of A)).hom (e.symm b)) • x
  rw [key]

/-- **A finite intersection of affine opens of a scheme separated over an affine base is
affine.** -/
@[ega "IV 21.12.8" "more general"]
theorem inter_isAffineOpen [IsSeparated f] (hU : ∀ i, IsAffineOpen (U i)) {p : ℕ}
    (i : Fin (p + 1) → I) : IsAffineOpen (CechCochains.inter U i) := by
  have : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = f ≫ terminal.from (Spec (CommRingCat.of A)) from
      terminal.hom_ext _ _]
    infer_instance
  exact IsAffineOpen.iInf fun k => hU (i k)

/-! ### The ordered cochains as an `A`-module -/

section Ordered

variable [LinearOrder I]

/-- Degree-`p` ordered Čech cochains form an `A`-module, tuplewise. -/
@[instance_reducible]
def ordCochainModule (p : ℕ) : Module A (CechCochains.OrdCochain U F.presheaf p) :=
  letI : ∀ i : CechCochains.OrdIndex (I := I) p, Module A Γ(F, CechCochains.inter U i.1) :=
    fun _ => sectionsModule f F _
  inferInstanceAs
    (Module A (∀ i : CechCochains.OrdIndex (I := I) p, Γ(F, CechCochains.inter U i.1)))

/-- Restriction of a cochain to the strictly increasing tuples, as an `A`-linear map out of
the alternating cochains. -/
def piLinear (p : ℕ) :
    letI := cochainModule f U F p
    letI := ordCochainModule f U F p
    alternatingSubmodule f U F p →ₗ[A] CechCochains.OrdCochain U F.presheaf p :=
  letI := cochainModule f U F p
  letI := ordCochainModule f U F p
  { toFun := fun s => CechCochains.pi U F.presheaf p s.1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- `Stacks.Cech.piLinear` is bijective: this is the inverse half of Stacks 01FJ. -/
theorem piLinear_bijective (p : ℕ) : Function.Bijective (piLinear f U F p) :=
  (CechCochains.cAddEquiv U F.presheaf p).symm.bijective

/-- **Stacks 01FJ, `A`-linearly.** The alternating Čech cochains are the ordered Čech
cochains, as `A`-modules. -/
def ordLinearEquiv (p : ℕ) :
    letI := cochainModule f U F p
    letI := ordCochainModule f U F p
    alternatingSubmodule f U F p ≃ₗ[A] CechCochains.OrdCochain U F.presheaf p :=
  letI := cochainModule f U F p
  letI := ordCochainModule f U F p
  LinearEquiv.ofBijective (piLinear f U F p) (piLinear_bijective f U F p)

end Ordered

/-! ### Termwise flatness -/

/-- **Flatness over the base holds in every degree of the alternating Čech complex.** For a
quasi-coherent module which is flat over an affine base, and a finite family of affine opens
of a scheme separated over that base, every term of the alternating Čech complex is a flat
module over the base ring. -/
theorem alternatingCechModuleComplex_flat [Finite I] [IsSeparated f] [F.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) (hflat : IsFlatOver f.toLRSHom.toShHom F) (n : ℕ) :
    Module.Flat A ((alternatingCechModuleComplex f U F).X n) := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let := cochainModule f U F n
  let : ∀ i : CechCochains.OrdIndex (I := I) n, Module A Γ(F, CechCochains.inter U i.1) :=
    fun _ => sectionsModule f F _
  let := ordCochainModule f U F n
  have hsec : ∀ i : CechCochains.OrdIndex (I := I) n,
      Module.Flat A Γ(F, CechCochains.inter U i.1) :=
    fun i => sections_flat f F hflat _ (inter_isAffineOpen f U hU i.1)
  have hord : Module.Flat A (CechCochains.OrdCochain U F.presheaf n) :=
    flat_pi_of_finite fun i : CechCochains.OrdIndex (I := I) n => Γ(F, CechCochains.inter U i.1)
  exact Module.Flat.of_linearEquiv (ordLinearEquiv f U F n)

end Stacks.Cech

end

end
