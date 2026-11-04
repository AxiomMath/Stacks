module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AdicTowerSurjective
public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower

/-!
# The graded pieces of the `𝓘`-adic filtration, and the induction they drive

Let `X` be a scheme, `𝓘` a quasi-coherent ideal sheaf on it and `ℱ` a sheaf of modules. For
`n ≤ m` the graded piece `𝓘 ⁿ ℱ / 𝓘 ᵐ ℱ` sits in a short exact sequence

`0 ⟶ 𝓘 ⁿ ℱ / 𝓘 ᵐ ℱ ⟶ ℱ / 𝓘 ᵐ ℱ ⟶ ℱ / 𝓘 ⁿ ℱ ⟶ 0`

whose right-hand map is the exponent drop `Stacks.Algebraization.idealPowerQuotientDrop`. This
file builds that sequence and feeds it to
`StacksFrontier/AlgebraicGeometry/FormalFunctions/AdicTowerSurjective.lean`, whose inverse-limit
induction was stated with the vanishing hypothesis at `kernel (idealPowerQuotientDrop …)`: the
hypothesis now reads at the graded piece itself, which is the sheaf the proof of
[Stacks, Tag 0EXD] computes with.

## Main results

* `Stacks.Abelian.shortExact_of_cokernel_desc`: **the third isomorphism theorem with the composite
  presented by a variable.** For composable monomorphisms `u, v` and any `w` with `u ≫ v = w`, a
  pair of maps `B/A ⟶ M/A ⟶ M/B` satisfying the two universal-property equations is short exact.
* `Stacks.Cohomology.FormalFunctions.shortExact_adicGradedPieceShortComplex`: **the graded piece
  of the `𝓘`-adic filtration sits in a short exact sequence with the two adic quotients**, with
  the exponent drop as its right-hand map.
* `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyTowerMap_of_isZero_gradedPiece`:
  **`H⁰` of the exponent drop is surjective once `H¹` of the graded piece vanishes.**
* `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_of_isZero_gradedPiece`:
  **the `𝓘`-adic inverse-limit induction of [Stacks, Tag 0EXD], on the graded pieces.**

## Implementation notes

**The third isomorphism theorem is not reproved.** It is
`Stacks.Abelian.cokernelCompShortComplex_shortExact`, already in the library, for the composite
`u ≫ v`; what is added here is the presentation with the composite replaced by a variable `w`
together with the equation `u ≫ v = w`, and the two maps replaced by variables satisfying
`cokernel.π u ≫ f = v ≫ cokernel.π w` and `cokernel.π w ≫ g = cokernel.π v`.

**That presentation is the whole point, and it is a performance fix rather than a convenience.**
Instantiating the library version directly needs
`cokernel ((idealPowerMultiple 𝓘 n ℱ).ι ≫ (idealPowerMultiple 𝓘 m ℱ).ι)` to be the adic quotient
`cokernel (idealPowerMultiple 𝓘 m ℱ).ι`, which holds only propositionally — the factorization
`Stacks.Algebraization.submoduleInclusion_comp_ι` is `SheafOfModules.Submodule.homOfLE_ι`, not
definitional — and asking Lean for it is a *kernel deterministic timeout*, as is transporting the
short complex along a `cokernelIsoOfEq`. With `w`, `f`, `g` and the vanishing of `f ≫ g` all
variables, `subst` eliminates them one after the other and the proof is three rewrites; the
concrete instantiation then checks in seconds. The same shape — generalise the morphism to a
variable and carry the equation — is what
`AlgebraicGeometry.tildeVectPullbackIso_comp_app` uses against the same failure mode.

The ambient category is pinned as `(C := X.Modules)` at every `cokernel`, `cokernel.π` and
`cokernel.desc`, as in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/IdealPowerShortExact.lean`: `X.Modules` is a `def`
for `SheafOfModules X.ringCatSheaf` and the two presentations carry separately declared category
instances, which instance search does not cross.

No `@[stacks]` attribute: Tag 0942 is carried where the third isomorphism theorem is proved, and
Tag 0EXD asserts that `AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` is an
equivalence, of which this is one implication inside the essential-surjectivity half.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.Abelian

variable {D : Type u} [Category.{v} D] [Abelian D] {A B M : D}

/-- Maps `B/A ⟶ M/(A ≫ B)` and `M/(A ≫ B) ⟶ M/B` pinned by their universal properties are the
canonical ones. -/
private lemma eq_cokernelCompι_and_eq_cokernelCompπ (u : A ⟶ B) (v : B ⟶ M)
    {f : cokernel u ⟶ cokernel (u ≫ v)} {g : cokernel (u ≫ v) ⟶ cokernel v}
    (hf : cokernel.π u ≫ f = v ≫ cokernel.π (u ≫ v))
    (hg : cokernel.π (u ≫ v) ≫ g = cokernel.π v) :
    f = cokernelCompι u v ∧ g = cokernelCompπ u v :=
  ⟨by rw [← cancel_epi (cokernel.π u), hf, π_comp_cokernelCompι],
    by rw [← cancel_epi (cokernel.π (u ≫ v)), hg, π_comp_cokernelCompπ]⟩

section OfEq

variable (u : A ⟶ B) (v : B ⟶ M) {w : A ⟶ M} (hw : u ≫ v = w)
  {f : cokernel u ⟶ cokernel w} {g : cokernel w ⟶ cokernel v}
  (hf : cokernel.π u ≫ f = v ≫ cokernel.π w) (hg : cokernel.π w ≫ g = cokernel.π v)

include hw in
/-- The map `A ⟶ M / W` vanishes when `W` is presented by `w = u ≫ v`. -/
public lemma comp_cokernel_π_eq_zero : u ≫ v ≫ cokernel.π w = 0 := by
  subst hw
  rw [← Category.assoc]
  exact cokernel.condition _

include hw hf hg in
/-- The composite `B/A ⟶ M/A ⟶ M/B` vanishes, for maps pinned by their universal properties. -/
public lemma comp_eq_zero_of_cokernel_desc : f ≫ g = 0 := by
  subst hw
  obtain ⟨rfl, rfl⟩ := eq_cokernelCompι_and_eq_cokernelCompπ u v hf hg
  exact cokernelCompι_comp_cokernelCompπ u v

include hw hf hg in
/-- **The third isomorphism theorem, with the composite and the two maps presented by variables.**
For composable monomorphisms `u : A ⟶ B` and `v : B ⟶ M`, any `w` with `u ≫ v = w` and any pair
`f : B/A ⟶ M/W`, `g : M/W ⟶ M/B` satisfying the universal-property equations, the sequence
`0 → B/A → M/W → M/B → 0` is short exact.

This is `Stacks.Abelian.cokernelCompShortComplex_shortExact` with everything that would otherwise
have to be transported along a propositional equality turned into a variable. -/
public lemma shortExact_of_cokernel_desc [Mono u] [Mono v] (hz : f ≫ g = 0) :
    (ShortComplex.mk f g hz).ShortExact := by
  subst hw
  obtain ⟨rfl, rfl⟩ := eq_cokernelCompι_and_eq_cokernelCompπ u v hf hg
  exact cokernelCompShortComplex_shortExact u v

end OfEq

end Stacks.Abelian

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Algebraization

/-! ### The graded piece and its short exact sequence -/

section GradedPiece

variable {X : Scheme.{u}} (J : X.IdealSheafData) (M : X.Modules)

/-- **The inclusion of one step of the ideal-adic filtration into the previous one is a
monomorphism**, because it is followed by the inclusion of the larger step into the ambient module
to give the inclusion of the smaller one, which is a monomorphism. -/
public theorem mono_submoduleInclusion_idealPowerMultiple {m n : ℕ} (h : n ≤ m) :
    Mono (submoduleInclusion (idealPowerMultiple_antitone J M h)) := by
  have hm : Mono (submoduleInclusion (idealPowerMultiple_antitone J M h) ≫
      (idealPowerMultiple J n M).ι) := by
    rw [submoduleInclusion_comp_ι]
    infer_instance
  exact mono_of_mono _ ((idealPowerMultiple J n M).ι)

/-- **The map `𝓘 ⁿ M / 𝓘 ᵐ M ⟶ M / 𝓘 ᵐ M`** induced by the inclusion of `𝓘 ⁿ M` into `M`. -/
public def adicGradedPieceToQuotient {m n : ℕ} (h : n ≤ m) :
    cokernel (C := X.Modules) (submoduleInclusion (idealPowerMultiple_antitone J M h)) ⟶
      idealPowerQuotient J m M :=
  cokernel.desc (C := X.Modules) _ ((idealPowerMultiple J n M).ι ≫
      cokernel.π (C := X.Modules) ((idealPowerMultiple J m M).ι))
    (Stacks.Abelian.comp_cokernel_π_eq_zero _ _ (submoduleInclusion_comp_ι _))

/-- The map `𝓘 ⁿ M / 𝓘 ᵐ M ⟶ M / 𝓘 ᵐ M` followed by the exponent drop `M / 𝓘 ᵐ M ⟶ M / 𝓘 ⁿ M`
is zero. -/
public theorem adicGradedPieceToQuotient_comp_drop {m n : ℕ} (h : n ≤ m) :
    adicGradedPieceToQuotient J M h ≫ idealPowerQuotientDrop J h M = 0 :=
  Stacks.Abelian.comp_eq_zero_of_cokernel_desc
    (submoduleInclusion (idealPowerMultiple_antitone J M h))
    ((idealPowerMultiple J n M).ι) (submoduleInclusion_comp_ι _)
    (cokernel.π_desc (C := X.Modules) _ _ _) (idealPowerQuotientDrop_π J h M)

/-- **The graded piece of the `𝓘`-adic filtration sits in a short exact sequence with the two
adic quotients**, `0 ⟶ 𝓘 ⁿ M / 𝓘 ᵐ M ⟶ M / 𝓘 ᵐ M ⟶ M / 𝓘 ⁿ M ⟶ 0`, whose right-hand map is the
exponent drop. -/
public theorem shortExact_adicGradedPieceShortComplex {m n : ℕ} (h : n ≤ m) :
    (ShortComplex.mk (adicGradedPieceToQuotient J M h) (idealPowerQuotientDrop J h M)
      (adicGradedPieceToQuotient_comp_drop J M h)).ShortExact := by
  have := mono_submoduleInclusion_idealPowerMultiple J M h
  exact Stacks.Abelian.shortExact_of_cokernel_desc
    (u := submoduleInclusion (idealPowerMultiple_antitone J M h))
    (v := (idealPowerMultiple J n M).ι)
    (hw := submoduleInclusion_comp_ι _)
    (f := adicGradedPieceToQuotient J M h)
    (g := idealPowerQuotientDrop J h M)
    (cokernel.π_desc (C := X.Modules) _ _ _) (idealPowerQuotientDrop_π J h M)
    (adicGradedPieceToQuotient_comp_drop J M h)

end GradedPiece

/-! ### The induction, on the graded pieces -/

section Induction

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (F : X.Modules)

/-- **`H⁰` of the exponent drop is surjective once `H¹` of the graded piece vanishes.** The graded
piece is the left-hand term of `shortExact_adicGradedPieceShortComplex`, and the window
`R⁰Q X₂ ⟶ R⁰Q X₃ ⟶ R¹Q X₁` of the long exact sequence makes the first map an epimorphism when the
last object is zero.

This is `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyTowerMap_of_isZero` with its
hypothesis read at the graded piece rather than at the kernel of the drop. -/
public theorem surjective_adicCohomologyTowerMap_of_isZero_gradedPiece {m n : ℕ} (h : m ≤ n)
    (hz : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj
      (cokernel (C := X.Modules) (submoduleInclusion
        (idealPowerMultiple_antitone (baseIdealSheaf A I f) F h))))) :
    Function.Surjective (adicCohomologyTowerMap A f I F 0 m n h) := by
  obtain ⟨δ, -, hex⟩ := Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅
    (shortExact_adicGradedPieceShortComplex (baseIdealSheaf A I f) F h)
    (Stacks.Cohomology.AffineBase.moduleGlobalSections X)
  have he : Epi (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 0).map
      (ShortComplex.mk (adicGradedPieceToQuotient (baseIdealSheaf A I f) F h)
        (idealPowerQuotientDrop (baseIdealSheaf A I f) h F)
        (adicGradedPieceToQuotient_comp_drop (baseIdealSheaf A I f) F h)).g) :=
    ((hex 0).exact 1).epi_f (hz.eq_of_tgt _ _)
  have hsurj := (ModuleCat.epi_iff_surjective _).mp he
  exact hsurj

/-- **The `𝓘`-adic inverse-limit induction of [Stacks, Tag 0EXD], on the graded pieces.** If `H¹`
vanishes on every graded piece `𝓘 ⁿ ℱ / 𝓘 ᵐ ℱ` of the filtration, then
`H⁰(X, ℱ) ⟶ H⁰(X, ℱ / 𝓘 ⁿ ℱ)` is surjective for every `n`.

At `n = 1` this is the surjectivity of `H⁰(X', 𝒢) ⟶ H⁰(E, 𝒢|_E)` the source produces, from which
the map `α : 𝒪_{X'}^{⊕ r} ⟶ 𝒢` is chosen. The vanishing it asks for is the one the source gets
from `E = 𝐏¹_Z`: the graded pieces are annihilated by `𝓘` and so live on the exceptional line,
where globally generated quasi-coherent modules have no `H¹`. -/
public theorem surjective_adicCohomologyProj_of_isZero_gradedPiece [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper f) (hF : Stacks.SheafOfModules.IsCoherent F)
    (hz : ∀ (m n : ℕ) (h : m ≤ n),
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj
        (cokernel (C := X.Modules) (submoduleInclusion
          (idealPowerMultiple_antitone (baseIdealSheaf A I f) F h)))))
    (n : ℕ) : Function.Surjective (adicCohomologyProj A f I F 0 n) :=
  surjective_adicCohomologyProj_of_surjective_towerMap A f I F hX hF 0
    (fun m n h => surjective_adicCohomologyTowerMap_of_isZero_gradedPiece A f I F h (hz m n h)) n

end Induction

end Stacks.Cohomology.FormalFunctions

end
