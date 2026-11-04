module

public import StacksFrontier.AlgebraicGeometry.Flatness.SheafFlatAffineSections
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AffineCechSections
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechComplexRepresentsSupport
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DerivedSupportInvertsAugmentation
public import StacksFrontier.RingTheory.Cech.FlatKoszulVanishing

/-!
# The extended alternating Čech complex of a flat module is exact off the number of equations

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions whose restrictions to
every affine open form a Koszul-regular sequence there, and let `ℱ` be a flat quasi-coherent
`𝒪_X`-module. The extended alternating Čech complex of `ℱ` along `f₁, …, f_c` is then exact in
every degree other than `c`, and the local cohomology sheaves of `ℱ` along the common zero locus
of the `fᵢ` vanish below degree `c`.

## Main results

* `Stacks.Perfect.KoszulFlatVanishing.exactAt_sections_of_isAffineOpen` — the complex of sections
  over an affine open is exact off degree `c`.
* `Stacks.Perfect.KoszulFlatVanishing.exactAt_of_ne` — the complex itself is exact off degree
  `c`.
* `Stacks.Perfect.KoszulFlatVanishing.isZero_homology_extend_of_lt` — **the cohomology sheaves of
  the integer-indexed extension vanish below degree `c`**.
* `Stacks.Perfect.KoszulFlatVanishing.isZero_homology_derivedSupportedSections_of_lt` — **the
  local cohomology sheaves along a closed subset cut out by `c` *global* Koszul-regular
  equations vanish below degree `c`**.

## References

* [Stacks Project, Tag 0G7P](https://stacks.math.columbia.edu/tag/0G7P)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G6L](https://stacks.math.columbia.edu/tag/0G6L)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.AffineCechSections
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.SheafOfModules.SupportedSections
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.KoszulFlatVanishing

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} {c : ℕ} {f : Fin c → Γ(X, ⊤)} {F : X.Modules} [F.IsQuasicoherent]

/-- The equations restricted to an open are the restrictions written with the section
notation. -/
public theorem eqn_eq_restrictOpen (V : X.Opens) (i : Fin c) :
    eqn f V i = TopCat.Presheaf.restrictOpen (f i) V le_top := rfl

variable (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
    (C := TopologicalSpace.Opens X.toTopCat)
    (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F)
  (hf : ∀ U : X.affineOpens,
    Koszul.IsKoszulRegular (fun i => TopCat.Presheaf.restrictOpen (f i) (U : X.Opens) le_top))
  (D : Stacks.Perfect.ExtendedAlternatingCech.ExtendedAlternatingCechData f F)

include hflat hf in
/-- **The complex of sections over an affine open is exact off degree `c`**, for a flat module
`ℱ` (`hflat`) and equations whose restrictions to every affine open are Koszul-regular (`hf`). -/
public theorem exactAt_sections_of_isAffineOpen {V : X.Opens} (hV : IsAffineOpen V)
    {p : ℕ} (hp : p ≠ c) :
    (((ExtendedAlternatingCech.moduleSectionsFunctor V).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.complex).ExactAt p := by
  have : Module.Flat Γ(X, V) Γ(F, V) := AlgebraicGeometry.flat_sections_of_isFlat F hflat hV
  have halg : IsZero ((_root_.Cech.cechComplex (eqn f V) Γ(F, V)).homology p) :=
    _root_.Cech.cechComplex_homology_isZero_of_isKoszulRegular_of_flat (eqn f V) Γ(F, V)
      (hf ⟨V, hV⟩) p hp
  have hmap : (((forget₂ (ModuleCat.{u} Γ(X, V)) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (_root_.Cech.cechComplex (eqn f V) Γ(F, V))).ExactAt p := by
    refine (HomologicalComplex.exactAt_iff_isZero_homology _ p).2 ?_
    refine IsZero.of_iso ?_ (Stacks.Perfect.CechSupportRepresentation.mapHomologyIso
      (forget₂ (ModuleCat.{u} Γ(X, V)) AddCommGrpCat.{u})
      (_root_.Cech.cechComplex (eqn f V) Γ(F, V)) p)
    exact Functor.map_isZero _ halg
  exact HomologicalComplex.ExactAt.of_iso hmap (complexIso f V F hV D).symm

include hflat hf in
/-- **The extended alternating Čech complex of a flat quasi-coherent module along a locally
Koszul-regular family of global equations is exact in every degree other than the number of
equations.** The hypotheses are the flatness `hflat` of `ℱ` and the Koszul-regularity `hf` of
the restricted equations on every affine open. -/
public theorem exactAt_of_ne {p : ℕ} (hp : p ≠ c) : D.complex.ExactAt p := by
  refine (SheafOfModules.exact_iff_stalkShortComplex_exact
    (structureSheafRing X.toRingedSpace) (D.complex.sc p)).2 fun x => ?_
  refine ExtendedAlternatingCech.stalkExact_of_sectionExact D.complex x p fun W₀ hxW₀ => ?_
  obtain ⟨V, hVaff, hxV, hVW₀⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxW₀
  exact ⟨V, hVW₀, hxV, exactAt_sections_of_isAffineOpen hflat hf D hVaff hp⟩

include hflat hf in
/-- **The cohomology sheaves of the integer-indexed extension vanish below the number of
equations**, for a flat module `ℱ` (`hflat`) and equations whose restrictions to every affine
open are Koszul-regular (`hf`). -/
public theorem isZero_homology_extend_of_lt {n : ℤ} (h : n < (c : ℤ)) :
    IsZero ((D.complex.extend ComplexShape.embeddingUpNat).homology n) := by
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ n).1 ?_
  rcases lt_or_ge n 0 with hn | hn
  · refine HomologicalComplex.extend_exactAt _ ComplexShape.embeddingUpNat n fun p => ?_
    have hp : ComplexShape.embeddingUpNat.f p = (p : ℤ) := rfl
    omega
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = (p : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    refine (HomologicalComplex.extend_exactAt_iff D.complex ComplexShape.embeddingUpNat
      (j := p) rfl).2 ?_
    exact exactAt_of_ne hflat hf D (by exact_mod_cast h.ne)

include hflat hf in
/-- **Local cohomology along global Koszul-regular equations vanishes below degree `c`.** If the
closed subset `Z` is the common zero locus of `c` global functions whose restrictions to the affine
opens are Koszul-regular sequences there, then the local cohomology sheaves of a flat
quasi-coherent `𝒪_X`-module vanish below degree `c`:

`ℋ ^i_Z(ℱ) = 0` for `i < c`. -/
public theorem isZero_homology_derivedSupportedSections_of_lt (i : ℤ) (hi : i < (c : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace
            (equationsClosedSet f)))) i).obj
      ((derivedSupportedSectionsOnClosed X.toRingedSpace
          (equationsClosedSet f)
          (isClosed_equationsClosedSet f)).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F))) := by
  let _ := pushforward_preservesFiniteLimits X.toRingedSpace
    (equationsClosedSet f)
  let _ := pushforward_preservesFiniteColimits X.toRingedSpace
    (equationsClosedSet f)
    (isClosed_equationsClosedSet f)
  obtain ⟨e⟩ := Stacks.Perfect.CechDerivedSupport.nonempty_cechIso_derivedSupportedSections f F
  refine Stacks.Perfect.DerivedSupportedSectionsValue.isZero_of_isZero_modulePushforward
    X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f) _ ?_
  refine IsZero.of_iso ?_ ((exactFunctorDerivedHomologyIso
    (modulePushforward (closedSubsetInclusion X.toRingedSpace
      (equationsClosedSet f))) i).app
      ((derivedSupportedSectionsOnClosed X.toRingedSpace
        (equationsClosedSet f)
        (isClosed_equationsClosedSet f)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors X.Modules i).app _)
  exact isZero_homology_extend_of_lt hflat hf
    (Stacks.Perfect.ExtendedAlternatingCech.extendedAlternatingCech f F) hi

end Stacks.Perfect.KoszulFlatVanishing

end
