module

public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmpleFamily
public import StacksFrontier.AlgebraicGeometry.PullbackExtension.Basic
public import StacksFrontier.AlgebraicGeometry.TensorSectionPower.Glue
public import StacksFrontier.AlgebraicGeometry.TensorSectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionPowerOpen
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafGeneral
public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.AffineSectionBasis
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication
public import StacksCore.Tactic.StacksAttribute

/-!
# Ample families of invertible modules and relatively ample invertible modules

Let `f : X ⟶ Y` be a morphism of schemes. If `Y` has an ample family of invertible modules and
some invertible `𝒪_X`-module is ample relative to `f`, then `X` has an ample family of invertible
modules.

The family produced on `X` is the one of the source: for `L` the `f`-ample module, `N i` a member
of the family on `Y` and exponents `n`, `m`, `k`, the module
`L^{⊗ m} ⊗ (f^*(N_i^{⊗ n}))^{⊗(k+1)} ⊗ (f^*(N_i^{⊗ n}))^{⊗(k+1)}`.

## Main definitions

* `Stacks.AmpleFamilyRelativeAmple.twistFamily`: the family of invertible modules on `X` built
  from an ample family on `Y` and an invertible module on `X`.

## Main results

* `Stacks.AmpleFamilyRelativeAmple.nonvanishingSet_eq_nonvanishingLocus`: the nonvanishing locus
  of a restriction-compatible family of sections is the nonvanishing locus of its value over
  `⊤`.
* `Stacks.AmpleFamilyRelativeAmple.isInvertible_tensorPow`: a natural-number tensor power of an
  invertible module on a scheme is invertible.
* `Stacks.AmpleFamilyRelativeAmple.quasiSeparatedSpace_of_isAmpleFamily`: a scheme with an ample
  family of invertible modules is a quasi-separated space.
* `Stacks.AmpleFamilyRelativeAmple.exists_section_affine_nonvanishingOpenOn_of_isAmple_restrict`:
  ampleness of the restriction of `L` to an open `W` produces a section of a tensor power of `L`
  over `W` whose nonvanishing locus is an affine open of `X` containing a prescribed point.
* `Stacks.AmpleFamilyRelativeAmple.exists_affine_nonvanishing_tensor`: every point of `X` lies
  in an affine nonvanishing locus of a global section of a member of `twistFamily`.
* `Stacks.AmpleFamilyRelativeAmple.isAmpleFamily_twistFamily`: `twistFamily` is an ample family.
* `Stacks.AmpleFamilyRelativeAmple.exists_isAmpleFamily`: **Stacks Tag 0GTP.**

## Implementation notes

The two hypotheses are read off the two tagged library notions. An ample family of invertible
modules is `AlgebraicGeometry.Scheme.IsAmpleFamily` (Tag 0FXR), whose sections are
restriction-compatible families and whose nonvanishing locus is the ringed-space one; relative
ampleness is `Stacks.RelativeAmple.IsRelativelyAmple` (Tag 01VH), which is stated over
`Stacks.Ample.IsAmple` and therefore over global sections and `Stacks.Ample.nonvanishingLocus`.
The two spellings of the nonvanishing locus are reconciled once and for all by
`nonvanishingSet_eq_nonvanishingLocus` below, out of
`Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_sectionsOfTop_iff'`.

**Why the exponent in the conclusion is `1`.** `AlgebraicGeometry.Scheme.tensorPow M 1` is `M` on
the nose, so a global section of a member of the family is already a section of a positive tensor
power of that member; the twisting is carried by the family itself rather than by the exponent,
exactly as in the source, where the section produced is a section of `f^*N^{⊗(n+1)} ⊗ L` and not
of a power of a single module.

**The route through Tag 01PW.** The source extends a section of `L` over `f^{-1}(Y_t)` to a
global section of `f^*N^{⊗ n} ⊗ L`. The form of Tag 01PW used here is
`Stacks.TensorSectionPower.exists_tensorSection_of_compactSpace`, which asks only that `X` be
quasi-compact and quasi-separated, that the twisting module be invertible and that the extended
module be quasi-coherent. Quasi-compactness of `X` comes from quasi-compactness of `f`, part of
relative ampleness, together with quasi-compactness of `Y`, part of having an ample family;
quasi-separatedness of `X` from
`Stacks.Tag087SPullbackExtension.quasiSeparated_of_isRelativelyAmple` together with
`quasiSeparatedSpace_of_isAmpleFamily` below.

**The final multiplication.** Tag 01PW pins the extension `ρ` only over `f^{-1}(Y_t)`, so its
nonvanishing locus can meet the complement; tensoring with the denominator `σ` produced by the
same lemma cuts the locus down to `f^{-1}(Y_t)`, which is the source's passage from `s'` to
`s'' = f^*t · s'`. That the nonvanishing locus of a tensor product of two global sections is the
intersection of the two is `Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection`.

**The section over the open.** Relative ampleness gives a global section of a tensor power of
`L|_{f^{-1}(Y_t)}` on the open subscheme, and what Tag 01PW consumes is a section of a tensor
power of `L` over the open `f^{-1}(Y_t)` of `X`. The passage is
`Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection`, with the comparison of the two
nonvanishing loci supplied by `Stacks.NonvanishingLocusRestrict` and `Stacks.SectionPowerOpen`,
and the identification of the tensor powers of the restriction with the restriction of the tensor
powers by `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` (Tag 01CD iterated).

## References

* [Stacks Project, Tag 0GTP](https://stacks.math.columbia.edu/tag/0GTP)
* [Stacks Project, Tag 0FXR](https://stacks.math.columbia.edu/tag/0FXR)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory
open Stacks.TensorSectionPower (powObj)
open Stacks.SectionExtension (resTop)
open Stacks.SectionTensorFormula (tensorSection)
open Stacks.NonvanishingLocusRestrict (mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection
  restrictSection_sectionOfRestrictGlobalSection)

universe u v

namespace Stacks.AmpleFamilyRelativeAmple

/-! ### The two spellings of the nonvanishing locus -/

/-- **The nonvanishing locus of a restriction-compatible family of sections is the nonvanishing
locus of its value over `⊤`.** The left-hand side is the spelling Stacks Tag 0FXR is stated over,
the right-hand side the one Stacks Tag 01PS and the rest of the ampleness theory use. -/
theorem nonvanishingSet_eq_nonvanishingLocus {X : Scheme.{u}} (M : X.Modules) (s : M.sections) :
    X.nonvanishingSet M s = nonvanishingLocus M (s.eval (op ⊤)) :=
  Eq.trans (AlgebraicGeometry.Scheme.nonvanishingSet_eq X M s)
    (Eq.trans
      (congrArg
        (Stacks.SheafOfModules.nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace) M)
        (Stacks.SheafOfModules.Invertible.sectionsOfTop_eval_top_self
          (X := X.toLocallyRingedSpace.toRingedSpace) M s).symm)
      (Set.ext fun y =>
        (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_sectionsOfTop_iff' M
          (s.eval (op ⊤)) y).symm))

/-- **The nonvanishing locus of a global section, read in the Tag 0FXR spelling.** This is
`Stacks.AmpleFamilyRelativeAmple.nonvanishingSet_eq_nonvanishingLocus` in the direction a
consumer producing an ample family needs it. -/
theorem nonvanishingSet_sectionsOfTop {X : Scheme.{u}} (M : X.Modules) (g : Γ(M, ⊤)) :
    X.nonvanishingSet M (Stacks.SheafOfModules.sectionsOfTop M g) = nonvanishingLocus M g :=
  Eq.trans (AlgebraicGeometry.Scheme.nonvanishingSet_eq X M _)
    (Set.ext fun y =>
      (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_sectionsOfTop_iff' M
        g y).symm)

/-! ### Natural-number tensor powers of an invertible module -/

/-- **A natural-number tensor power of an invertible module on a scheme is invertible.** The
zeroth power is the structure sheaf, the first is the module itself, and each further power is a
tensor product of the module with the preceding power. -/
theorem isInvertible_tensorPow (X : Scheme.{u}) (P : X.Modules)
    (h : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P) (n : ℕ) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (X.tensorPow P n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact Stacks.SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2
    | 1 => exact h
    | (k + 2) =>
      have := ih (k + 1) (by omega)
      exact Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf X.ringCatSheaf.2 P
        (X.tensorPow P (k + 1))

/-- A natural-number tensor power of an invertible module on a scheme is invertible, in the
spelling the ampleness theory is written over. -/
theorem isInvertibleModule_tensorPow (X : Scheme.{u}) (P : X.Modules)
    (h : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P) (n : ℕ) :
    IsInvertibleModule X (X.tensorPow P n) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
    (X.tensorPow P n)).mp (isInvertible_tensorPow X P h n)

/-! ### A scheme with an ample family is quasi-compact and quasi-separated -/

/-- **A scheme carrying an ample family of invertible modules is a quasi-separated space.** The
affine nonvanishing loci supplied pointwise by the family cover the scheme, and a cover by affine
nonvanishing opens of global sections of invertible modules gives quasi-separatedness, the
pairwise intersections being affine by Stacks Tag 01PV. -/
theorem quasiSeparatedSpace_of_isAmpleFamily {I : Type v} {Y : Scheme.{u}} {N : I → Y.Modules}
    (hN : Y.IsAmpleFamily N) : QuasiSeparatedSpace Y := by
  classical
  choose i n hn s U hU hmem haff using hN.exists_affine_nonvanishing
  have hinv : ∀ y : Y, Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Y.tensorPow (N (i y)) (n y)) :=
    fun y => isInvertible_tensorPow Y (N (i y)) (hN.isInvertible _) (n y)
  have hopen : ∀ y : Y, Stacks.SheafOfModules.nonvanishingOpen (X := Y.toRingedSpace)
      (Y.tensorPow (N (i y)) (n y)) (s y) = U y := fun y => (Opens.ext (hU y)).symm
  refine AlgebraicGeometry.Scheme.Modules.quasiSeparatedSpace_of_affine_nonvanishingOpen_cover
    (fun y : Y => Y.tensorPow (N (i y)) (n y)) s (fun y => hopen y ▸ haff y)
    (le_antisymm le_top fun y _ => Opens.mem_iSup.mpr ⟨y, hopen y ▸ hmem y⟩)

/-- A scheme carrying an ample family of invertible modules is quasi-compact. -/
theorem compactSpace_of_isAmpleFamily {I : Type v} {Y : Scheme.{u}} {N : I → Y.Modules}
    (hN : Y.IsAmpleFamily N) : CompactSpace Y := hN.compactSpace

/-! ### A section over an open from ampleness of the restriction -/

/-- **A section of a tensor power of `L` over an open `W`, with affine nonvanishing locus, from
ampleness of the restriction of `L` to `W`.** Ampleness on the open subscheme `W` produces a
global section of a tensor power of `L|_W` there; that section is the image of a section of the
corresponding tensor power of `L` over `W`, and the two nonvanishing loci correspond. -/
theorem exists_section_affine_nonvanishingOpenOn_of_isAmple_restrict {X : Scheme.{u}}
    (L : X.Modules) [IsInvertibleModule X L] (W : X.Opens)
    (hamp : IsAmple W.toScheme (Stacks.AmpleLocallyClosed.pullbackModule W.ι L))
    (x : X) (hx : x ∈ W) :
    ∃ (m : ℕ) (t : Γ(tensorPowModule X L (m : ℤ), W)),
      x ∈ Stacks.SectionPowerOpen.nonvanishingOpenOn (tensorPowModule X L (m : ℤ)) W t ∧
        IsAffineOpen (Stacks.SectionPowerOpen.nonvanishingOpenOn
          (tensorPowModule X L (m : ℤ)) W t) := by
  obtain ⟨m, -, σ, hσaff, hxσ⟩ :=
    Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen W.toScheme _ hamp ⟨x, hx⟩
  obtain ⟨σ', hσ'def⟩ :
      ∃ σ' : Γ(Stacks.AmpleLocallyClosed.pullbackModule W.ι (tensorPowModule X L (m : ℤ)), ⊤),
        σ' = ConcreteCategory.hom (Scheme.Modules.Hom.app
          (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso W.ι L m).symm.hom ⊤) σ :=
    ⟨_, rfl⟩
  have hEq : Stacks.NonvanishingOpen.nonvanishingOpen W.toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule W.ι (tensorPowModule X L (m : ℤ))) σ' =
      Stacks.AmpleTheory.powNonvanishingOpen W.toScheme
        (Stacks.AmpleLocallyClosed.pullbackModule W.ι L) m σ := by
    refine Opens.ext ?_
    rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen,
      Stacks.AmpleTheory.coe_powNonvanishingOpen, hσ'def]
    exact nonvanishingLocus_congr
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso W.ι L m).symm σ
  refine ⟨m, Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection W
    (tensorPowModule X L (m : ℤ)) σ', ?_, ?_⟩
  · refine (mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection W
      (tensorPowModule X L (m : ℤ)) σ' ⟨x, hx⟩).mp ?_
    rwa [← Stacks.NonvanishingOpen.coe_nonvanishingOpen, hEq]
  · rwa [Stacks.SectionPowerOpen.isAffineOpen_nonvanishingOpenOn_iff,
      restrictSection_sectionOfRestrictGlobalSection, hEq]

/-! ### The family produced on the source -/

/-- The index type of the family produced on the source of the morphism: a member of the family
on the target together with three exponents. -/
abbrev TwistIndex (I : Type v) : Type v := I × ULift.{v} ℕ × ULift.{v} ℕ × ULift.{v} ℕ

section Twist

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

/-- **The family of invertible modules on `X` attached to a family `N` on `Y` and a module `L` on
`X`**: at the index `(i, n, m, k)` the module
`L^{⊗ m} ⊗ (f^*(N_i^{⊗ n}))^{⊗(k+1)} ⊗ (f^*(N_i^{⊗ n}))^{⊗(k+1)}`. -/
def twistFamily {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Modules) [IsInvertibleModule X L]
    {I : Type v} (N : I → Y.Modules) (p : TwistIndex I) : X.Modules :=
  (tensorPowModule X L (p.2.2.1.down : ℤ) ⊗
      powObj (Stacks.AmpleLocallyClosed.pullbackModule f (Y.tensorPow (N p.1) p.2.1.down))
        p.2.2.2.down) ⊗
    powObj (Stacks.AmpleLocallyClosed.pullbackModule f (Y.tensorPow (N p.1) p.2.1.down))
      p.2.2.2.down

/-- Every member of `Stacks.AmpleFamilyRelativeAmple.twistFamily` is invertible: a tensor power
of `L`, the pullback of a tensor power of a member of the family on `Y`, and tensor products of
invertible modules. -/
theorem isInvertible_twistFamily {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Modules)
    [IsInvertibleModule X L] {I : Type v} (N : I → Y.Modules)
    (hN : ∀ i, Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (N i))
    (p : TwistIndex I) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (twistFamily f L N p) := by
  have : IsInvertibleModule Y (Y.tensorPow (N p.1) p.2.1.down) :=
    isInvertibleModule_tensorPow Y (N p.1) (hN p.1) p.2.1.down
  exact (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
    (twistFamily f L N p)).mpr
      (Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj _ _)

/-- **The pointwise clause of Stacks Tag 0FXR for the twisted family.** Every point of `X` lies
in an affine open of `X` which is the nonvanishing locus of a global section of a member of
`Stacks.AmpleFamilyRelativeAmple.twistFamily`.

This is the body of the proof of Stacks Tag 0GTP: the point's image lies in an affine
nonvanishing locus `Y_t` of a section of a power of a member of the family on `Y`; the pullback
of `t` has `f^{-1}(Y_t)` as its nonvanishing locus (Tag 0H78); `L` restricted to `f^{-1}(Y_t)` is
ample, giving a section of a power of `L` over `f^{-1}(Y_t)` with affine nonvanishing locus
containing the point; Tag 01PW extends it, after twisting, to a global section; and tensoring
with the denominator cuts the nonvanishing locus back down to `f^{-1}(Y_t)`. -/
theorem exists_affine_nonvanishing_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Modules)
    [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    {I : Type v} (N : I → Y.Modules) (hN : Y.IsAmpleFamily N)
    [CompactSpace X] [QuasiSeparatedSpace X] (x : X) :
    ∃ (i : I) (n m k : ℕ)
      (g : Γ((tensorPowModule X L (m : ℤ) ⊗
          powObj (Stacks.AmpleLocallyClosed.pullbackModule f (Y.tensorPow (N i) n)) k) ⊗
        powObj (Stacks.AmpleLocallyClosed.pullbackModule f (Y.tensorPow (N i) n)) k, ⊤))
      (U : X.Opens),
      (U : Set X) = nonvanishingLocus ((tensorPowModule X L (m : ℤ) ⊗
          powObj (Stacks.AmpleLocallyClosed.pullbackModule f (Y.tensorPow (N i) n)) k) ⊗
        powObj (Stacks.AmpleLocallyClosed.pullbackModule f (Y.tensorPow (N i) n)) k) g ∧
        x ∈ U ∧ IsAffineOpen U := by
  classical
  obtain ⟨i, n, -, s, V, hV, hyV, hVaff⟩ := hN.exists_affine_nonvanishing (f.base x)
  have hPa : IsInvertibleModule Y (Y.tensorPow (N i) n) :=
    isInvertibleModule_tensorPow Y (N i) (hN.isInvertible i) n
  -- the pullback of the section has `f⁻¹(V)` as nonvanishing locus, by Tag 0H78
  have hWQ : Stacks.NonvanishingOpen.nonvanishingOpen X
      (Stacks.AmpleLocallyClosed.pullbackModule f (Y.tensorPow (N i) n))
      (Stacks.NonvanishingPullback.pullbackGlobalSection f (Y.tensorPow (N i) n)
        (s.eval (op ⊤))) = f ⁻¹ᵁ V := Opens.ext <| by
    rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen,
      ← Stacks.NonvanishingPullback.preimage_nonvanishingLocus f (Y.tensorPow (N i) n)
        (s.eval (op ⊤)), ← nonvanishingSet_eq_nonvanishingLocus, ← hV]
    rfl
  -- ampleness of `L` over `f⁻¹(V)` gives a section of a power of `L` over it
  obtain ⟨m, t, hxt, hAff⟩ := exists_section_affine_nonvanishingOpenOn_of_isAmple_restrict L
    (f ⁻¹ᵁ V) (hL.isAmple_preimage f L V hVaff) x hyV
  have : (tensorPowModule X L (m : ℤ)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  -- Tag 01PW
  obtain ⟨k, σ₂, ρ, hW2, heq⟩ := Stacks.TensorSectionPower.exists_tensorSection_of_compactSpace
    (Stacks.AmpleLocallyClosed.pullbackModule f (Y.tensorPow (N i) n))
    (Stacks.NonvanishingPullback.pullbackGlobalSection f (Y.tensorPow (N i) n) (s.eval (op ⊤)))
    (tensorPowModule X L (m : ℤ)) (f ⁻¹ᵁ V) hWQ t
  have hW3 : ∀ y : X, y ∈ Stacks.NonvanishingOpen.nonvanishingOpen X _ σ₂ ↔ y ∈ f ⁻¹ᵁ V :=
    fun y => (SetLike.ext_iff.mp hW2 y).symm
  -- on `f⁻¹(V)`, the nonvanishing of `ρ` is that of `t` together with that of `σ₂`
  have key := fun (y : X) (hy : y ∈ (f ⁻¹ᵁ V : X.Opens)) =>
    Stacks.TensorSectionProduct.mem_nonvanishingLocus_iff_of_resTop_eq ρ t
      (resTop (f ⁻¹ᵁ V) σ₂) heq hy
  refine ⟨i, n, m, k, tensorSection _ _ ρ σ₂,
    Stacks.SectionPowerOpen.nonvanishingOpenOn (tensorPowModule X L (m : ℤ)) (f ⁻¹ᵁ V) t,
    ?_, hxt, hAff⟩
  rw [Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection,
    Stacks.SectionPowerOpen.coe_nonvanishingOpenOn]
  refine Set.ext fun y => ⟨fun ⟨hyW, hyt⟩ =>
    ⟨(key y hyW).mpr ⟨hyt, ?_⟩, (hW3 y).mpr hyW⟩, fun ⟨hyρ, hyσ⟩ =>
    ⟨(hW3 y).mp hyσ, ((key y ((hW3 y).mp hyσ)).mp hyρ).1⟩⟩
  rw [resTop, TopCat.Presheaf.Γgerm_res_apply (C := Ab.{u})
    (i := homOfLE (le_top : (f ⁻¹ᵁ V : X.Opens) ≤ ⊤))
    (powObj (Stacks.AmpleLocallyClosed.pullbackModule f (Y.tensorPow (N i) n)) k).presheaf
    y hyW σ₂]
  exact (hW3 y).mpr hyW

/-- **Stacks Tag 0FXR for the twisted family.** If `Y` has the ample family `N` and `L` is ample
relative to `f`, then `Stacks.AmpleFamilyRelativeAmple.twistFamily f L N` is an ample family of
invertible modules on `X`. -/
theorem isAmpleFamily_twistFamily {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Modules)
    [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    {I : Type v} (N : I → Y.Modules) (hN : Y.IsAmpleFamily N) :
    X.IsAmpleFamily (twistFamily f L N) := by
  have : CompactSpace Y := hN.compactSpace
  have : QuasiCompact f := hL.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_isAmpleFamily hN
  have : QuasiSeparated f :=
    Stacks.Tag087SPullbackExtension.quasiSeparated_of_isRelativelyAmple f L hL
  have : QuasiSeparatedSpace X := AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated f
  refine ⟨isInvertible_twistFamily f L N hN.isInvertible, ‹_›, fun x => ?_⟩
  obtain ⟨i, n, m, k, g, U, hU, hxU, hUaff⟩ := exists_affine_nonvanishing_tensor f L hL N hN x
  exact ⟨(i, ⟨n⟩, ⟨m⟩, ⟨k⟩), 1, le_rfl,
    Stacks.SheafOfModules.sectionsOfTop
      (X.tensorPow (twistFamily f L N (i, ⟨n⟩, ⟨m⟩, ⟨k⟩)) 1) g, U,
    hU.trans (nonvanishingSet_sectionsOfTop
      (X.tensorPow (twistFamily f L N (i, ⟨n⟩, ⟨m⟩, ⟨k⟩)) 1) g).symm, hxU, hUaff⟩

/-- **Stacks Tag 0GTP.** Let `f : X ⟶ Y` be a morphism of schemes. If `Y` has an ample family of
invertible modules and there is an invertible `𝒪_X`-module ample relative to `f`, then `X` has an
ample family of invertible modules. -/
@[stacks 0GTP]
theorem exists_isAmpleFamily {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type v} (N : I → Y.Modules)
    (hN : Y.IsAmpleFamily N)
    (hL : ∃ (L : X.Modules) (_ : IsInvertibleModule X L),
      Stacks.RelativeAmple.IsRelativelyAmple f L) :
    ∃ (J : Type v) (M : J → X.Modules), X.IsAmpleFamily M := by
  obtain ⟨L, hLinv, hL⟩ := hL
  exact ⟨TwistIndex I, twistFamily f L N, isAmpleFamily_twistFamily f L hL N hN⟩

end Twist

end Stacks.AmpleFamilyRelativeAmple

end
