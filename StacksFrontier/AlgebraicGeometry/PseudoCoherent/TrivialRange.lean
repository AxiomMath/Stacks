module

public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTfae
public import StacksFrontier.Homology.PseudoCoherent.Relative.Module

/-!
# The range of degrees in which relative pseudo-coherence is automatic

Relative `m`-pseudo-coherence of a sheaf of modules, and relative `m`-pseudo-coherence of a
module over a finite-type algebra, both become vacuous once `m` is large: a complex concentrated
in degree zero has no cohomology in positive degrees, so the zero complex is already an
approximation to it in degrees above zero. This file makes that precise on both sides of the
comparison of Stacks 09VF and Stacks 09UJ, and deduces that the comparison carries no content
above degree zero.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_isZero_X`: a complex of
  `𝒪_X`-modules vanishing in all degrees at least `m` is `m`-pseudo-coherent (Stacks 08CB).
* `AlgebraicGeometry.Scheme.Hom.isModulePseudoCoherentFrom_of_pos`: for a morphism locally of
  finite type, *every* sheaf of modules is relatively `m`-pseudo-coherent for `0 < m`. This is
  the positive-degree clause of Stacks 09UM.
* `PseudoCoherence.isModuleRelativelyPseudoCoherentFrom_of_nonneg`: a finite module over a
  finite-type algebra is relatively `m`-pseudo-coherent for `0 ≤ m` (Stacks 065I).
* `AlgebraicGeometry.relativeStructureSheafComparison_of_nonpos`:
  `AlgebraicGeometry.RelativeStructureSheafComparison` — the comparison from which
  `AlgebraicGeometry.pseudoCoherent_tfae_of_relativeComparison` derives the three-condition form
  of Stacks 067Y — follows from its restriction to the degrees `m ≤ 0`. The comparison itself is
  proved outright in
  `StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafComparison`, so this reduction is a
  convenience rather than a step towards it.

## Implementation notes

The witness on the sheaf side is the zero complex, which is strictly perfect in the sense of
Stacks 08C4: its non-vanishing degrees form the empty set, and its terms, being zero, are
retracts of `𝒪_X ^ 0`. The whole space serves as the open on which the approximation is defined,
so the local clause of Stacks 08CB is satisfied by a one-member covering. Restriction to an open
subspace preserves zero objects, which is all that is needed to see that the restricted complex
still has vanishing terms in the relevant degrees.

On the ring side the degree-zero case is not vacuous but is still automatic: by Stacks 0675 it is
exactly finiteness of the module, which for the structure sheaf is finiteness of a ring over
itself. Monotonicity of relative `m`-pseudo-coherence in `m`, which is
`PseudoCoherence.IsRelativelyPseudoCoherentFrom.mono` below, then covers every `0 ≤ m` at once,
so the ring side is known in one more degree than the sheaf side.

Apart from the positive-degree clause of Stacks 09UM, none of the results here carries a `stacks`
tag: they are the trivial range of statements whose content lies elsewhere, and the tags of those
statements belong on the declarations that prove them in full. The positive-degree clause is an
exception because the trivial range *is* its whole content.

## References

* [The Stacks Project, Lemma 36.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.8 (09UM)](https://stacks.math.columbia.edu/tag/09UM)
* [The Stacks Project, Definition 15.82.4 (065I)](https://stacks.math.columbia.edu/tag/065I)
* [The Stacks Project, Lemma 15.82.5 (0675)](https://stacks.math.columbia.edu/tag/0675)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Definition 20.46.1 (08C4)](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace ZeroObject
open scoped AlgebraicGeometry

universe u

namespace HomologicalComplex

/-- Homology is a subquotient of the term in the same degree, so it vanishes wherever that term
does. -/
public theorem isZero_homology_of_isZero_X {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    (h : Limits.IsZero (K.X i)) : Limits.IsZero (K.homology i) :=
  (K.exactAt_iff_isZero_homology i).mp (ShortComplex.exact_of_isZero_X₂ (K.sc i) h)

/-- Every term of the zero complex is a zero object. -/
private theorem isZero_X_zero {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    [Limits.HasZeroObject C] {ι : Type*} {c : ComplexShape ι} (i : ι) :
    Limits.IsZero ((0 : HomologicalComplex C c).X i) :=
  (HomologicalComplex.eval C c i).map_isZero (Limits.isZero_zero (HomologicalComplex C c))

end HomologicalComplex

namespace StrictlyPerfect

/-- The zero complex of `𝒪_X`-modules is strictly perfect: no degree is non-zero, and the zero
module is a retract of `𝒪_X ^ 0`. -/
public theorem isStrictlyPerfect_zero {X : AlgebraicGeometry.RingedSpace.{u, u}} :
    IsStrictlyPerfect (0 : CochainComplex (OXMod.{u, u} X) ℤ) := by
  refine ⟨Set.Finite.subset Set.finite_empty fun i hi ↦ absurd ?_ hi, fun i ↦
    (isDirectSummandOfFiniteFree_iff_retract _).mpr ⟨0, ⟨⟨0, 0, ?_⟩⟩⟩⟩
  · exact HomologicalComplex.isZero_X_zero i
  · exact (HomologicalComplex.isZero_X_zero i).eq_of_src _ _

end StrictlyPerfect

namespace AlgebraicGeometry

namespace RingedSpace

/-- A complex of `𝒪_X`-modules all of whose terms in degrees at least `m` vanish is
`m`-pseudo-coherent in the sense of Stacks 08CB: the zero complex, on the whole space, is an
approximation to it in those degrees. -/
public theorem isPseudoCoherentComplexFrom_of_isZero_X {X : RingedSpace.{u, u}}
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) (m : ℤ)
    (h : ∀ j : ℤ, m ≤ j → IsZero (E.X j)) : IsPseudoCoherentComplexFrom E m := by
  intro _
  have key : ∀ j : ℤ, m ≤ j →
      IsZero ((restrictComplex E (⊤ : Opens X.carrier)).X j) :=
    fun j hj ↦ (restrictModules X ⊤).map_isZero (h j hj)
  refine ⟨⊤, trivial, 0, StrictlyPerfect.isStrictlyPerfect_zero, 0, fun j hj ↦ ?_, ?_⟩
  · exact (HomologicalComplex.isZero_homology_of_isZero_X _ _
      (HomologicalComplex.isZero_X_zero j)).isIso
      (HomologicalComplex.isZero_homology_of_isZero_X _ _ (key j hj.le)) _
  · exact (HomologicalComplex.isZero_homology_of_isZero_X _ _ (key m le_rfl)).epi _

/-- An object of the derived category of `𝒪_X`-modules concentrated in degree zero is
`m`-pseudo-coherent for every positive `m`: it is represented by a complex supported in degree
zero, which vanishes in all degrees at least `m`. -/
public theorem isPseudoCoherentFrom_singleFunctor_of_pos {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} X)]
    (A : StrictlyPerfect.OXMod.{u, u} X) {m : ℤ} (hm : 0 < m) :
    IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (StrictlyPerfect.OXMod.{u, u} X) 0).obj A) m := by
  refine ⟨(HomologicalComplex.single (StrictlyPerfect.OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj A,
    isPseudoCoherentComplexFrom_of_isZero_X _ m fun j hj ↦ ?_,
    ⟨eqToIso (DerivedCategory.Q_obj_single_obj (StrictlyPerfect.OXMod.{u, u} X) 0 A)⟩⟩
  exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)

end RingedSpace

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Modules

/-- For a closed immersion `i : U ⟶ Y` of schemes and a sheaf of `𝒪_U`-modules `A`, the local
condition of Stacks 09UI holds for `A` in degree zero and every positive `m`: the derived
pushforward along `i` is again concentrated in degree zero, because `i_*` is exact. -/
public theorem isPseudoCoherentFromAfterPushforward_singleFunctor_of_pos {U Y : Scheme.{u}}
    (i : U ⟶ Y) [IsClosedImmersion i] (A : U.Modules) {m : ℤ} (hm : 0 < m) :
    IsPseudoCoherentFromAfterPushforward i
      ((DerivedCategory.singleFunctor U.Modules 0).obj A) m := by
  rw [isPseudoCoherentFromAfterPushforward_iff]
  exact RingedSpace.IsPseudoCoherentFrom.of_iso.{u, u + 1}
    (RingedSpace.isPseudoCoherentFrom_singleFunctor_of_pos.{u} _ hm)
    ((Functor.mapDerivedCategorySingleFunctor (pushforward i) 0).app A).symm

end Scheme.Modules

namespace Scheme.Hom

/-- **Stacks 09UM, the positive degrees.** For a morphism of schemes locally of finite type,
every sheaf of `𝒪_X`-modules is relatively `m`-pseudo-coherent whenever `0 < m`.

The affine open covering of the base is the family of all affine opens, and over each member the
covering of its inverse image is the family of all affine opens of `X` contained in it; the
closed immersions into affine space are the ones produced by
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`, and the local condition at each
of them holds because the restriction of a sheaf of modules is still concentrated in degree
zero. -/
@[stacks 09UM "positive_degrees"]
public theorem isModulePseudoCoherentFrom_of_pos {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) {m : ℤ} (hm : 0 < m) :
    IsModulePseudoCoherentFrom f F m := by
  refine ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun V ↦ ?_⟩
  refine ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.affineOpens).1}, fun u ↦ u.1, ?_, fun u ↦ ?_⟩
  · refine le_antisymm (iSup_le fun u ↦ u.2) fun x hx ↦ ?_
    obtain ⟨W, hW, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hxW⟩
  · obtain ⟨n, i, hi, hover⟩ := exists_isClosedImmersion_affineSpace_resLE f V u.1 u.2
    have := hi
    exact ⟨u.2, n, i, hi, hover, Scheme.Modules.IsPseudoCoherentFromAfterPushforward.of_iso i
      (Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_of_pos i
        ((Scheme.Modules.restrictFunctor (u.1).1.ι).obj F) hm)
      ((Functor.mapDerivedCategorySingleFunctor
        (Scheme.Modules.restrictFunctor (u.1).1.ι) 0).app F).symm⟩

end Scheme.Hom

end AlgebraicGeometry

namespace PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

/-- Relative `m`-pseudo-coherence becomes weaker as `m` increases, because `m`-pseudo-coherence
over each polynomial presentation does
(`StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.mono`). -/
public theorem IsRelativelyPseudoCoherentFrom.mono {R : Type u} {A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] {K : DerivedCategory (ModuleCat.{u} A)}
    {m n : ℤ} (h : IsRelativelyPseudoCoherentFrom (R := R) K m) (hmn : m ≤ n) :
    IsRelativelyPseudoCoherentFrom (R := R) K n :=
  fun k α hα ↦ (h k α hα).mono hmn

/-- **The trivial range of Stacks 065I.** A finite module over a finite-type `R`-algebra is
relatively `m`-pseudo-coherent for every `0 ≤ m`.

In degree zero this is Stacks 0675, which identifies relative `0`-pseudo-coherence with
finiteness of the module; the remaining degrees follow by monotonicity in `m`. -/
public theorem isModuleRelativelyPseudoCoherentFrom_of_nonneg {R : Type u} {A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M] {m : ℤ} (hm : 0 ≤ m) :
    IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) M m :=
  IsRelativelyPseudoCoherentFrom.mono
    ((moduleRelativelyPseudoCoherent_iff_finiteness_and_resolutions (R := R) (A := A) M).1.mpr
      ‹Module.Finite A M›) hm

/-- A finite-type algebra is relatively `m`-pseudo-coherent as a module over itself for every
`0 ≤ m`, a ring being finite over itself.

Every instance argument of this statement occurs in its conclusion, which is what lets it be
applied against a goal whose algebra and finite-type structures are supplied by `let`
bindings, as in `AlgebraicGeometry.RelativeStructureSheafComparisonAt`. -/
public theorem isModuleRelativelyPseudoCoherentFrom_self_of_nonneg {R : Type u} {A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] {m : ℤ} (hm : 0 ≤ m) :
    IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) A m :=
  isModuleRelativelyPseudoCoherentFrom_of_nonneg A hm

end PseudoCoherence

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The comparison of Stacks 09VF and Stacks 09UJ at the structure sheaf, in a single degree:
`AlgebraicGeometry.RelativeStructureSheafComparison` is this statement for every witness of local
finiteness of type and every degree, as `AlgebraicGeometry.relativeStructureSheafComparison_iff`
records. -/
public abbrev RelativeStructureSheafComparisonAt {X S : Scheme.{u}} (f : X ⟶ S)
    (hft : LocallyOfFiniteType f) (m : ℤ) : Prop :=
  letI := hft
  Scheme.Hom.IsModulePseudoCoherentFrom f (SheafOfModules.unit X.ringCatSheaf) m ↔
    ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
      PseudoCoherence.IsModuleRelativelyPseudoCoherentFrom
        (R := Γ(S, V)) (A := Γ(X, U)) Γ(X, U) m

/-- `AlgebraicGeometry.RelativeStructureSheafComparison` is the degreewise comparison
`AlgebraicGeometry.RelativeStructureSheafComparisonAt` asserted for every degree. -/
public theorem relativeStructureSheafComparison_iff :
    RelativeStructureSheafComparison f ↔
      ∀ (hft : LocallyOfFiniteType f) (m : ℤ), RelativeStructureSheafComparisonAt f hft m :=
  Iff.rfl

/-- At every compatible pair of affine opens of a morphism locally of finite type, `Γ(X, U)` is
relatively `m`-pseudo-coherent as a module over itself with respect to `Γ(S, V)` whenever
`0 ≤ m`. This is the right-hand side of
`AlgebraicGeometry.RelativeStructureSheafComparisonAt` in those degrees.

The algebra and finite-type structures are repeated in the proof term so that they are available
to instance search there, exactly as they are in the statement. -/
public theorem isModuleRelativelyPseudoCoherentFrom_appLE_of_nonneg [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    {m : ℤ} (hm : 0 ≤ m) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
    PseudoCoherence.IsModuleRelativelyPseudoCoherentFrom
      (R := Γ(S, V)) (A := Γ(X, U)) Γ(X, U) m :=
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  PseudoCoherence.isModuleRelativelyPseudoCoherentFrom_self_of_nonneg hm

/-- **The comparison of Stacks 09VF and Stacks 09UJ at the structure sheaf has no content above
degree zero.** `AlgebraicGeometry.RelativeStructureSheafComparison f`, the hypothesis of
`AlgebraicGeometry.pseudoCoherent_tfae_of_relativeComparison`, follows from its restriction to
the degrees `m ≤ 0`. (It also holds outright, by
`AlgebraicGeometry.relativeStructureSheafComparison`; this lemma says where its content lies.)

In the degrees `0 < m` both sides hold outright: the left-hand side by
`AlgebraicGeometry.Scheme.Hom.isModulePseudoCoherentFrom_of_pos`, and the right-hand side by
`AlgebraicGeometry.isModuleRelativelyPseudoCoherentFrom_appLE_of_nonneg`. The right-hand side in
fact also holds at `m = 0`, so what the comparison still asserts at `m = 0` is exactly relative
`0`-pseudo-coherence of `𝒪_X` over `S`. -/
public theorem relativeStructureSheafComparison_of_nonpos
    (h : ∀ (hft : LocallyOfFiniteType f) (m : ℤ), m ≤ 0 →
      RelativeStructureSheafComparisonAt f hft m) :
    RelativeStructureSheafComparison f := by
  intro hft m
  rcases le_or_gt m 0 with hm | hm
  · exact h hft m hm
  · have := hft
    exact iff_of_true (Scheme.Hom.isModulePseudoCoherentFrom_of_pos f _ hm)
      fun U hU V hV e ↦
        isModuleRelativelyPseudoCoherentFrom_appLE_of_nonneg f U hU V hV e hm.le

end AlgebraicGeometry

end
