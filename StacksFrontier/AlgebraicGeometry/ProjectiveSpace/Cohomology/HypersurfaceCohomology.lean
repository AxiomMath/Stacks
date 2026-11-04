module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.ProjChartKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoefficientScalars
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of a hypersurface in projective space

Let `k` be a field, let `F` be a nonzero homogeneous polynomial of degree `d` in `n + 1`
variables and let `Z ⊆ 𝐏ⁿ_k` be the closed subscheme it cuts out, that is, the closed subscheme
whose ideal sheaf is the zero scheme of the section of `𝒪(d)` attached to `F`. Tensoring the
sequence of [Stacks, Tag 0C6K] for that section with `𝒪(-d)` gives the short exact sequence

`0 ⟶ 𝒪(-d) ⟶ 𝒪 ⟶ i_* 𝒪_Z ⟶ 0`

on `𝐏ⁿ_k`, and the long exact sequence of [Stacks, Tag 0111] attached to it makes the connecting
morphism `H^q(𝐏ⁿ_k, i_* 𝒪_Z) ⟶ H^{q+1}(𝐏ⁿ_k, 𝒪(-d))` an isomorphism whenever `H^q(𝐏ⁿ_k, 𝒪)` and
`H^{q+1}(𝐏ⁿ_k, 𝒪)` both vanish. Composed with the comparison of [Stacks, Tag 089W] along the
closed immersion this reads

`H^q(Z, 𝒪_Z) ≅ H^{q+1}(𝐏ⁿ_k, 𝒪(-d))`,

an isomorphism of `k`-vector spaces. At `n = 2`, `q = 1` it is the boundary isomorphism from
which the genus of a plane curve is computed.

## Main results

* `AlgebraicGeometry.exists_shortExact_zeroScheme_unit_of_isRegularSection`: **the zero-scheme
  sequence of a regular section, trivialized** — for invertible `L`, `M` on a scheme `X`, a
  regular section `s` of `L` and a trivialization of `M ⊗ L`, the sequence
  `0 ⟶ M ⟶ 𝒪_X ⟶ i_* 𝒪_{Z(s)} ⟶ 0` is short exact.
* `AlgebraicGeometry.pullbackObjUnitIsoUnit` and `AlgebraicGeometry.zeroScheme_zero`: the
  inverse image of a structure sheaf is a structure sheaf, and the zero scheme of the zero
  section has zero ideal sheaf.
* `AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverFieldSubscheme`: the cohomology of
  a closed subscheme over the base field, read at the closed subscheme attached to its ideal
  sheaf.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistNegTensorIsoUnit`: `𝒪(-d) ⊗ 𝒪(d) ≅ 𝒪` on
  `Proj 𝒮` for `𝒮` generated in degree one.
* `Stacks.ProjectiveSpace.Cohomology.degreeSection_ne_zero`: the section of `𝒪(d)` attached to a
  nonzero homogeneous polynomial is nonzero.
* `Stacks.ProjectiveSpace.Cohomology.nonempty_iso_rightDerived_pushforward_unit_zeroScheme`: the
  boundary isomorphism `H^q(𝐏ⁿ_k, i_* 𝒪_Z) ≅ H^{q+1}(𝐏ⁿ_k, 𝒪(-d))` over the global functions.
* `Stacks.ProjectiveSpace.Cohomology.nonempty_structureSheafCohomologyIsoTwistCohomology`:
  **`H^q(Z, 𝒪_Z) ≅ H^{q+1}(𝐏ⁿ_k, 𝒪(-d))` as `k`-vector spaces**, and
  `finrank_structureSheafCohomology_eq_finrank_twistCohomology_neg`, the equality of dimensions.
* `Stacks.ProjectiveSpace.Cohomology.nonempty_iso_rightDerived_unit_pushforward_unit_zeroScheme`
  and `Stacks.ProjectiveSpace.Cohomology.nonempty_structureSheafCohomologyIsoTwistCohomologyZero`:
  the same long exact sequence read one step earlier — **`H^q(Z, 𝒪_Z) ≅ H^q(𝐏ⁿ_k, 𝒪)`** in the
  degrees where `𝒪(-d)` has no cohomology. At `n = 2`, `q = 0` and `d > 0` this computes the
  global functions of a plane curve.

## Implementation notes

**The shape of the sequence.** `AlgebraicGeometry.shortExact_zeroScheme_twist_of_isRegularSection`
produces `0 ⟶ M ⟶ M ⊗ L ⟶ i_* i^*(M ⊗ L) ⟶ 0`. The middle term is rewritten by the given
trivialization of `M ⊗ L` and the last term by the inverse image of a structure sheaf being a
structure sheaf, both on the sequence itself, by
`CategoryTheory.ShortComplex.shortExact_of_iso`. Only the three objects are used downstream, so
the two maps of the resulting sequence are not named. Keeping that step at an arbitrary scheme,
rather than at `Proj 𝒮` with `L = 𝒪(d)` and `M = 𝒪(-d)`, is what keeps its elaboration
affordable: the unification of `AlgebraicGeometry.zeroScheme`'s invertibility argument at a
twisting sheaf is expensive, and here it happens once, in the instantiation.

**Why the statements are existential.** The connecting morphism of the long exact sequence
depends on a chosen resolution of the sequence, so
`Stacks.Cohomology.RightDerivedDelta.nonempty_iso_rightDerived` returns `Nonempty` of an
isomorphism rather than an isomorphism; the statements here are in the same form, and the
dimension of the cohomology — which is all the genus needs — follows from it.

**Where `F ≠ 0` enters.** Only through the regularity of the section: on an integral scheme a
nonzero global section of an invertible module is a nonzerodivisor
(`AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero`), and `𝐏ⁿ_k` is integral. Without it
the first map of the sequence is not a monomorphism and there is no sequence; for `F = 0` the
zero scheme is all of `𝐏ⁿ_k` and the conclusion is false.

**Identifying the subscheme.** The sequence is about the zero scheme of the section, which is the
closed subscheme attached to an ideal sheaf; a given closed immersion `i` with that ideal sheaf
factors through it by an isomorphism `AlgebraicGeometry.IsClosedImmersion.lift`, and
`Stacks.Morphisms.pushforwardStructureSheafIsoUnit` carries the structure sheaf across that
isomorphism.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 0111](https://stacks.math.columbia.edu/tag/0111)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff X_mem_one)
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (twistMultiplicationIso)

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

/-- The tensor product sheaf of [Stacks, Tag 01CA] as a monoidal structure on the `𝒪_X`-modules
of a scheme, as in `StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist`. The
name differs from the one used there because `local` governs the attribute, not the name. -/
local instance Stacks.ProjectiveSpace.Cohomology.hypersurfaceModulesMonoidal
    (X : AlgebraicGeometry.Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

namespace AlgebraicGeometry

/-- **The inverse image of the structure sheaf is the structure sheaf**, at the scheme-level
spelling of the category of modules. This is `Stacks.PullbackAlgebra.pullbackUnitIso`, the
structure-sheaf clause of [Stacks, Tag 01CD]. -/
def pullbackObjUnitIsoUnit {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  Stacks.PullbackAlgebra.pullbackUnitIso i.toLRSHom.toShHom

/-- **The zero scheme of the zero section is the whole scheme**: its ideal sheaf is zero. On an
affine open the defining ideal of [Stacks, Tag 02OQ] is generated by the values of the section
under the local linear functionals, and those all vanish. -/
theorem zeroScheme_zero (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    zeroScheme X L (0 : Γ(L, ⊤)) = ⊥ := by
  refine le_antisymm (Scheme.IdealSheafData.le_def.2 fun U => ?_) bot_le
  refine le_trans (Scheme.IdealSheafData.ideal_ofIdeals_le _ U) ?_
  rw [Ideal.span_le]
  rintro a ⟨φ, rfl⟩
  simp

/-- Rewriting the middle and last terms of a complex with vanishing composite leaves the
composite vanishing. -/
private theorem comp_eq_zero_of_isoMiddle {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A B B' D D' : C} (f : A ⟶ B) (g : B ⟶ D) (w : f ≫ g = 0) (α : B ≅ B') (γ : D ⟶ D') :
    (f ≫ α.hom) ≫ α.inv ≫ g ≫ γ = 0 := by
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, w, zero_comp]

/-- **The last term of the trivialized zero-scheme sequence**: the inverse image of `M ⊗ L` on
the zero scheme of a section of `L` is the structure sheaf of that zero scheme, once `M ⊗ L` is
trivialized on the ambient scheme. -/
def zeroSchemePullbackIsoUnit (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (M : X.Modules) (α : (M ⊗ L : X.Modules) ≅ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        (M ⊗ L : X.Modules) ≅
      (SheafOfModules.unit (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf :
        (zeroScheme X L (s.eval (op ⊤))).subscheme.Modules) :=
  (Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).mapIso α ≪≫
    pullbackObjUnitIsoUnit (zeroScheme X L (s.eval (op ⊤))).subschemeι

/-- **The zero-scheme sequence of a regular section of an invertible module, trivialized.** Let
`L` and `M` be invertible modules on a scheme `X`, let `s` be a regular global section of `L`
([Stacks, Tag 01WY]) with zero scheme `Z(s)` and inclusion `i`, and let `α` trivialize `M ⊗ L`.
Then

`0 ⟶ M ⟶ 𝒪_X ⟶ i_* 𝒪_{Z(s)} ⟶ 0`

is short exact. -/
theorem exists_shortExact_zeroScheme_unit_of_isRegularSection (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (α : (M ⊗ L : X.Modules) ≅ SheafOfModules.unit X.ringCatSheaf) :
    ∃ (f : M ⟶ SheafOfModules.unit X.ringCatSheaf)
        (g : SheafOfModules.unit X.ringCatSheaf ⟶
          (Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
            (SheafOfModules.unit
              (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf))
        (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact := by
  obtain ⟨w₀, hse⟩ := shortExact_zeroScheme_twist_of_isRegularSection X L s hs M
  refine ⟨((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≫ α.hom,
    α.inv ≫ (Scheme.Modules.pullbackPushforwardAdjunction
        (zeroScheme X L (s.eval (op ⊤))).subschemeι).unit.app (M ⊗ L) ≫
      (Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).map
        (zeroSchemePullbackIsoUnit X L s M α).hom,
    comp_eq_zero_of_isoMiddle _ _ w₀ α _, ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ hse
  exact ShortComplex.isoMk (Iso.refl _) α
    ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).mapIso
      (zeroSchemePullbackIsoUnit X L s M α)) (Category.id_comp _)
    (Iso.hom_inv_id_assoc α _)

/-- **The cohomology of a closed subscheme over the base field, read at the canonical closed
subscheme attached to its ideal sheaf.** A closed immersion `i : Z ⟶ X` with `i.ker = J`
factors through `J.subschemeι` by an isomorphism of schemes
(`AlgebraicGeometry.IsClosedImmersion.lift`), along which the structure sheaf and the cohomology
over the base both travel. -/
def structureSheafCohomologyIsoCohomologyOverFieldSubscheme (k : Type u) [Field k]
    {X Z : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (i : Z ⟶ X) [IsClosedImmersion i]
    (J : X.IdealSheafData) (hJ : i.ker = J) (q : ℕ) :
    structureSheafCohomology (i ≫ p) q ≅
      cohomologyOverField k p ((Scheme.Modules.pushforward J.subschemeι).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf)) q :=
  have hjker : J.subschemeι.ker = i.ker := J.ker_subschemeι.trans hJ.symm
  have hφ : IsClosedImmersion.lift J.subschemeι i (le_of_eq hjker) ≫ J.subschemeι = i :=
    IsClosedImmersion.lift_fac _ _ _
  have _hiso : IsIso (IsClosedImmersion.lift J.subschemeι i (le_of_eq hjker)) :=
    IsClosedImmersion.isIso_of_ker_eq i J.subschemeι _ hφ hjker.symm
  let e : Z ≅ J.subscheme := asIso (IsClosedImmersion.lift J.subschemeι i (le_of_eq hjker))
  have hcomp : i ≫ p = e.hom ≫ (J.subschemeι ≫ p) :=
    (congrArg (fun m => m ≫ p) hφ.symm).trans (Category.assoc _ _ _)
  structureSheafCohomologyIsoCohomologyOverField k (i ≫ p) q ≪≫
    eqToIso (congrArg (fun m => cohomologyOverField k m (SheafOfModules.unit Z.ringCatSheaf) q)
      hcomp) ≪≫
    cohomologyOverFieldPushforwardIso k e.hom (J.subschemeι ≫ p)
      (SheafOfModules.unit Z.ringCatSheaf) q ≪≫
    cohomologyOverFieldIso k (J.subschemeι ≫ p)
      (Stacks.Morphisms.pushforwardStructureSheafIsoUnit e) q ≪≫
    cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k J.subschemeι p
      (SheafOfModules.unit J.subscheme.ringCatSheaf) q

end AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

section Twist

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **`𝒪(-d) ⊗ 𝒪(d) ≅ 𝒪` on `Proj 𝒮`**, for `𝒮` generated in degree one: Equation 01MO of
[Stacks, Tag 01MT] identifies the tensor product with `𝒪(-d + d) = 𝒪(0)`, which is the structure
sheaf. -/
def twistNegTensorIsoUnit (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (d : ℤ) :
    (twistingSheafModule 𝒮 (-d) ⊗ twistingSheafModule 𝒮 d :
        (AlgebraicGeometry.Proj 𝒮).Modules) ≅
      SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf :=
  twistMultiplicationIso 𝒮
      (Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top 𝒮 hgen) (-d) d ≪≫
    eqToIso (congrArg (twistingSheaf 𝒮) (neg_add_cancel d)) ≪≫
      Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit 𝒮

end Twist

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.ProjectiveSpace.Cohomology

open AlgebraicGeometry.ProjectiveSpectrum.Proj

/-! ### A nonzero homogeneous polynomial has a nonzero twisted section -/

/-- **The section of `𝒪(d)` on `𝐏ⁿ_R` attached to a nonzero homogeneous polynomial is
nonzero**, for `R` a domain. If the section vanished, a power of a variable would annihilate the
polynomial, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_eq_zero_of_degreeSection_eq_zero`. -/
theorem degreeSection_ne_zero (R : Type u) [CommRing R] [IsDomain R] (n d : ℕ)
    (F : polyGrading R n d) (hF : (F : MvPolynomial (Fin (n + 1)) R) ≠ 0) :
    degreeSection (polyGrading R n) d F ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_degreeSection_eq_zero (polyGrading R n) F h
    (X_mem_one R n 0)
  rcases mul_eq_zero.1 hm with hx | hx
  · exact pow_ne_zero m (MvPolynomial.X_ne_zero (R := R) (0 : Fin (n + 1))) hx
  · exact hF hx

/-! ### The vanishing of the cohomology of the structure sheaf, over the global functions -/

/-- Restriction of scalars reflects the zero module: the two modules have the same carrier. -/
private theorem isZero_of_isZero_restrictScalars {R' S' : Type u} [Ring R'] [Ring S']
    (f : R' →+* S') (A : ModuleCat.{u} S')
    (h : IsZero ((ModuleCat.restrictScalars f).obj A)) : IsZero A :=
  have hs : Subsingleton ((ModuleCat.restrictScalars f).obj A) :=
    ModuleCat.subsingleton_of_isZero h
  have : Subsingleton A := hs
  ModuleCat.isZero_of_subsingleton A

/-- **`H^q(𝐏ⁿ_k, 𝒪(d)) = 0` as a module over the global functions**, whenever it vanishes as a
`k`-module: restriction of scalars along
`Stacks.ProjectiveSpace.Cohomology.coeffScalar` does not change the carrier. -/
theorem isZero_rightDerived_sections_twistingSheaf (k : Type u) [Field k] (n q : ℕ) (d : ℤ)
    (h : IsZero (twistCohomology k n d q)) :
    IsZero (((Stacks.Cohomology.sectionsFunctor
        (AlgebraicGeometry.Proj (polyGrading k n)) ⊤).rightDerived q).obj
      (twistingSheafModule (polyGrading k n) d)) :=
  isZero_of_isZero_restrictScalars (coeffScalar k n) _ h

/-- **`H^q(𝐏ⁿ_k, 𝒪) = 0` as a module over the global functions**, whenever it vanishes as a
`k`-module. The structure sheaf is the zeroth twist, and restriction of scalars along
`Stacks.ProjectiveSpace.Cohomology.coeffScalar` does not change the carrier. -/
theorem isZero_rightDerived_sections_unit (k : Type u) [Field k] (n q : ℕ)
    (h : IsZero (twistCohomology k n 0 q)) :
    IsZero (((Stacks.Cohomology.sectionsFunctor
        (AlgebraicGeometry.Proj (polyGrading k n)) ⊤).rightDerived q).obj
      (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf)) :=
  (isZero_of_isZero_restrictScalars (coeffScalar k n) _ h).of_iso
    (((Stacks.Cohomology.sectionsFunctor
      (AlgebraicGeometry.Proj (polyGrading k n)) ⊤).rightDerived q).mapIso
        (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit
          (polyGrading k n)).symm)

/-! ### The boundary isomorphism -/

section Boundary

variable (k : Type u) [Field k] (n : ℕ)

/-- **The boundary isomorphism of a hypersurface in `𝐏ⁿ_k`, over the global functions.** For a
global section `s` of `𝒪(d)` whose value on the whole space is nonzero, with zero scheme `Z(s)`
and inclusion `i`, the long exact sequence of the twisted zero-scheme sequence has
`H^q(𝐏ⁿ_k, i_* 𝒪_{Z(s)})` isomorphic to `H^{q+1}(𝐏ⁿ_k, 𝒪(-d))` as soon as the two neighbouring
terms `H^q(𝐏ⁿ_k, 𝒪)` and `H^{q+1}(𝐏ⁿ_k, 𝒪)` vanish. -/
@[sga "7 XXII 6.2" "(6.2.5), partial"]
theorem nonempty_iso_rightDerived_pushforward_unit_zeroScheme (q : ℕ) (d : ℤ)
    (s : (twistingSheafModule (polyGrading k n) d).sections)
    (hs : s.eval (op ⊤) ≠ 0) (h₁ : IsZero (twistCohomology k n 0 q))
    (h₂ : IsZero (twistCohomology k n 0 (q + 1))) :
    Nonempty (((Stacks.Cohomology.sectionsFunctor
          (AlgebraicGeometry.Proj (polyGrading k n)) ⊤).rightDerived q).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward
            (zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
              (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι).obj
          (SheafOfModules.unit (zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
                (twistingSheafModule (polyGrading k n) d)
                (s.eval (op ⊤))).subscheme.ringCatSheaf :
            (zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
              (twistingSheafModule (polyGrading k n) d)
              (s.eval (op ⊤))).subscheme.Modules)) ≅
      ((Stacks.Cohomology.sectionsFunctor
          (AlgebraicGeometry.Proj (polyGrading k n)) ⊤).rightDerived (q + 1)).obj
        (twistingSheafModule (polyGrading k n) (-d))) := by
  have hgen := MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) k
  obtain ⟨f, g, w, hse⟩ := AlgebraicGeometry.exists_shortExact_zeroScheme_unit_of_isRegularSection
    (AlgebraicGeometry.Proj (polyGrading k n)) (twistingSheafModule (polyGrading k n) d) s
    (AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero
      (twistingSheafModule (polyGrading k n) d) s hs)
    (twistingSheafModule (polyGrading k n) (-d)) (twistNegTensorIsoUnit (polyGrading k n) hgen d)
  exact Stacks.Cohomology.RightDerivedDelta.nonempty_iso_rightDerived hse
    (Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading k n)) ⊤) q
    (isZero_rightDerived_sections_unit k n q h₁)
    (isZero_rightDerived_sections_unit k n (q + 1) h₂)

/-- **The restriction isomorphism of a hypersurface in `𝐏ⁿ_k`, over the global functions.** For a
global section `s` of `𝒪(d)` whose value on the whole space is nonzero, with zero scheme `Z(s)`
and inclusion `i`, the restriction map `H^q(𝐏ⁿ_k, 𝒪) ⟶ H^q(𝐏ⁿ_k, i_* 𝒪_{Z(s)})` of the twisted
zero-scheme sequence is an isomorphism as soon as the two terms `H^q(𝐏ⁿ_k, 𝒪(-d))` and
`H^{q+1}(𝐏ⁿ_k, 𝒪(-d))` at the sub-object vanish. -/
theorem nonempty_iso_rightDerived_unit_pushforward_unit_zeroScheme (q : ℕ) (d : ℤ)
    (s : (twistingSheafModule (polyGrading k n) d).sections)
    (hs : s.eval (op ⊤) ≠ 0) (h₁ : IsZero (twistCohomology k n (-d) q))
    (h₂ : IsZero (twistCohomology k n (-d) (q + 1))) :
    Nonempty (((Stacks.Cohomology.sectionsFunctor
          (AlgebraicGeometry.Proj (polyGrading k n)) ⊤).rightDerived q).obj
        (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf) ≅
      ((Stacks.Cohomology.sectionsFunctor
          (AlgebraicGeometry.Proj (polyGrading k n)) ⊤).rightDerived q).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward
            (zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
              (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι).obj
          (SheafOfModules.unit (zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
                (twistingSheafModule (polyGrading k n) d)
                (s.eval (op ⊤))).subscheme.ringCatSheaf :
            (zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
              (twistingSheafModule (polyGrading k n) d)
              (s.eval (op ⊤))).subscheme.Modules))) := by
  have hgen := MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) k
  obtain ⟨f, g, w, hse⟩ := AlgebraicGeometry.exists_shortExact_zeroScheme_unit_of_isRegularSection
    (AlgebraicGeometry.Proj (polyGrading k n)) (twistingSheafModule (polyGrading k n) d) s
    (AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero
      (twistingSheafModule (polyGrading k n) d) s hs)
    (twistingSheafModule (polyGrading k n) (-d)) (twistNegTensorIsoUnit (polyGrading k n) hgen d)
  have := Stacks.Cohomology.RightDerivedDelta.isIso_rightDerived_map_g hse
    (Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading k n)) ⊤) q
    (isZero_rightDerived_sections_twistingSheaf k n q (-d) h₁)
    (isZero_rightDerived_sections_twistingSheaf k n (q + 1) (-d) h₂)
  exact ⟨asIso (((Stacks.Cohomology.sectionsFunctor
    (AlgebraicGeometry.Proj (polyGrading k n)) ⊤).rightDerived q).map g)⟩

/-- A nonzero homogeneous polynomial gives a section of `𝒪(d)` with nonzero value on the whole
space, whose zero scheme is the ideal sheaf of the polynomial's section. -/
private theorem exists_section_eval_ne_zero_ideal_eq (d : ℕ) (F : polyGrading k n d)
    (hF : (F : MvPolynomial (Fin (n + 1)) k) ≠ 0)
    (J : (AlgebraicGeometry.Proj (polyGrading k n)).IdealSheafData)
    (hker : J = zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
      (twistingSheafModule (polyGrading k n) (d : ℤ))
      (degreeSection (polyGrading k n) d F)) :
    ∃ s : (twistingSheafModule (polyGrading k n) (d : ℤ)).sections, s.eval (op ⊤) ≠ 0 ∧
      J = zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
        (twistingSheafModule (polyGrading k n) (d : ℤ)) (s.eval (op ⊤)) :=
  have ht := Stacks.PresheafOfModules.sectionOfTop_val_top
    (twistingSheafModule (polyGrading k n) (d : ℤ)).val (degreeSection (polyGrading k n) d F)
  ⟨_, ht ▸ degreeSection_ne_zero k n d F hF, hker.trans (congrArg _ ht).symm⟩

/-- **The cohomology of a hypersurface in `𝐏ⁿ_k` is a twisted cohomology of `𝐏ⁿ_k`.** Let `F` be
a nonzero homogeneous polynomial of degree `d` and let `i : Z ⟶ 𝐏ⁿ_k` be a closed immersion whose
ideal sheaf is the zero scheme of the section of `𝒪(d)` attached to `F`. Then

`H^q(Z, 𝒪_Z) ≅ H^{q+1}(𝐏ⁿ_k, 𝒪(-d))`

as `k`-vector spaces, provided `H^q(𝐏ⁿ_k, 𝒪)` and `H^{q+1}(𝐏ⁿ_k, 𝒪)` vanish. -/
@[sga "7 XXII 6.2" "(6.2.5), partial"]
theorem nonempty_structureSheafCohomologyIsoTwistCohomology (q d : ℕ)
    {Z : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ AlgebraicGeometry.Proj (polyGrading k n)) [AlgebraicGeometry.IsClosedImmersion i]
    (F : polyGrading k n d) (hF : (F : MvPolynomial (Fin (n + 1)) k) ≠ 0)
    (hker : i.ker = zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
      (twistingSheafModule (polyGrading k n) (d : ℤ))
      (degreeSection (polyGrading k n) d F))
    (h₁ : IsZero (twistCohomology k n 0 q)) (h₂ : IsZero (twistCohomology k n 0 (q + 1))) :
    Nonempty (AlgebraicGeometry.structureSheafCohomology (i ≫ projToSpecCoeff k n) q ≅
      twistCohomology k n (-(d : ℤ)) (q + 1)) := by
  obtain ⟨s, hs, hJ⟩ := exists_section_eval_ne_zero_ideal_eq k n d F hF i.ker hker
  obtain ⟨δ⟩ := nonempty_iso_rightDerived_pushforward_unit_zeroScheme k n q (d : ℤ) s hs h₁ h₂
  exact ⟨AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverFieldSubscheme k
      (projToSpecCoeff k n) i _ hJ q ≪≫
    cohomologyOverFieldIsoRestrictScalarsCoeffScalar k n _ q ≪≫
    (ModuleCat.restrictScalars.{u} (coeffScalar k n)).mapIso δ⟩

/-- **The cohomology of a hypersurface in `𝐏ⁿ_k` is the untwisted cohomology of `𝐏ⁿ_k`**, in the
degrees where the twist `𝒪(-d)` has none. Let `F` be a nonzero homogeneous polynomial of degree
`d` and let `i : Z ⟶ 𝐏ⁿ_k` be a closed immersion whose ideal sheaf is the zero scheme of the
section of `𝒪(d)` attached to `F`. Then

`H^q(Z, 𝒪_Z) ≅ H^q(𝐏ⁿ_k, 𝒪)`

as `k`-vector spaces, provided `H^q(𝐏ⁿ_k, 𝒪(-d))` and `H^{q+1}(𝐏ⁿ_k, 𝒪(-d))` vanish. At `n = 2`,
`q = 0` and `d > 0` this is the computation of the global functions of a plane curve. -/
@[sga "7 XXII 6.2" "partial"]
theorem nonempty_structureSheafCohomologyIsoTwistCohomologyZero (q d : ℕ)
    {Z : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ AlgebraicGeometry.Proj (polyGrading k n)) [AlgebraicGeometry.IsClosedImmersion i]
    (F : polyGrading k n d) (hF : (F : MvPolynomial (Fin (n + 1)) k) ≠ 0)
    (hker : i.ker = zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
      (twistingSheafModule (polyGrading k n) (d : ℤ))
      (degreeSection (polyGrading k n) d F))
    (h₁ : IsZero (twistCohomology k n (-(d : ℤ)) q))
    (h₂ : IsZero (twistCohomology k n (-(d : ℤ)) (q + 1))) :
    Nonempty (AlgebraicGeometry.structureSheafCohomology (i ≫ projToSpecCoeff k n) q ≅
      twistCohomology k n 0 q) := by
  obtain ⟨s, hs, hJ⟩ := exists_section_eval_ne_zero_ideal_eq k n d F hF i.ker hker
  obtain ⟨ρ⟩ := nonempty_iso_rightDerived_unit_pushforward_unit_zeroScheme k n q (d : ℤ) s hs
    h₁ h₂
  exact ⟨AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverFieldSubscheme k
      (projToSpecCoeff k n) i _ hJ q ≪≫
    cohomologyOverFieldIsoRestrictScalarsCoeffScalar k n _ q ≪≫
    (ModuleCat.restrictScalars.{u} (coeffScalar k n)).mapIso ρ.symm ≪≫
    (ModuleCat.restrictScalars.{u} (coeffScalar k n)).mapIso
      (((Stacks.Cohomology.sectionsFunctor
          (AlgebraicGeometry.Proj (polyGrading k n)) ⊤).rightDerived q).mapIso
        (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit
          (polyGrading k n)).symm)⟩

/-- **The dimension over `k` of `H^q(Z, 𝒪_Z)` for a hypersurface `Z ⊆ 𝐏ⁿ_k` of degree `d`** is
that of `H^{q+1}(𝐏ⁿ_k, 𝒪(-d))`. -/
theorem finrank_structureSheafCohomology_eq_finrank_twistCohomology_neg (q d : ℕ)
    {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ AlgebraicGeometry.Proj (polyGrading k n))
    [AlgebraicGeometry.IsClosedImmersion i]
    (F : polyGrading k n d) (hF : (F : MvPolynomial (Fin (n + 1)) k) ≠ 0)
    (hker : i.ker = zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
      (twistingSheafModule (polyGrading k n) (d : ℤ))
      (degreeSection (polyGrading k n) d F))
    (h₁ : IsZero (twistCohomology k n 0 q)) (h₂ : IsZero (twistCohomology k n 0 (q + 1))) :
    Module.finrank k (AlgebraicGeometry.structureSheafCohomology (i ≫ projToSpecCoeff k n) q) =
      Module.finrank k (twistCohomology k n (-(d : ℤ)) (q + 1)) :=
  (nonempty_structureSheafCohomologyIsoTwistCohomology k n q d i F hF hker h₁
    h₂).some.toLinearEquiv.finrank_eq

end Boundary

end Stacks.ProjectiveSpace.Cohomology

end
