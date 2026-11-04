module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedExtensionByZeroTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRelativeTensorUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedModule
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# The extension by zero of `A_U` is flat and K-flat

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras, let `U` be
an object of `C` and let `j : (Sh(C/U), O_U) ⟶ (Sh(C), O)` be the localization morphism. Write
`A_U = j^*A` for the restriction of `A` to the slice site, taken as a right differential graded
`A_U`-module by its own multiplication. This file proves conditions (1) and (2) of the source's
definition of a *good* right differential graded `A`-module for `j_!A_U`: it is flat as a graded
module, and it is K-flat.

## Main definitions

* `SheafOfModules.dgExtensionByZeroRegular` is `j_!A_U`, the extension by zero of `A_U`.

## Main results

* `SheafOfModules.dgExtensionByZeroRegular_isGradedFlat`: **Tag 0FSB, condition (1).** The graded
  module underlying `j_!A_U` is flat.
* `SheafOfModules.dgExtensionByZeroRegular_isKFlat`: **Tag 0FSB, condition (2).** `j_!A_U` is
  K-flat.

Condition (3), and with it the whole of Tag 0FSB, is
`SheafOfModules.dgExtensionByZeroRegular_isGoodToposBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodExtensionByZeroToposBaseChange.lean`, which
quotes the two results here for conditions (1) and (2).

## Implementation notes

**What is proved, and how.** "Good" is the three-condition notion of Tag 0FSA, formalized as
`SheafOfModules.DifferentialGradedModule.IsGood`: (1) flatness of the underlying graded module,
(2) K-flatness, (3) both after arbitrary base change. The two results here are exactly
conditions (1) and (2), in the library's own
`SheafOfModules.RelativeTensor.IsGradedFlat` and `SheafOfModules.RelativeTensor.IsKFlat`, which
are the first two conjuncts of `IsGood`.

The source argues from the identification
`j_!A_U ⊗_A N = j_!(A_U ⊗_{A_U} N|_U) = j_!(N_U)`, which this development has degreewise as
`SheafOfModules.extendTensorIso` (Tag 0FRB) and for complexes as
`SheafOfModules.dgExtendTensorIso` (Tag 0FRX), and then from the exactness of restriction to `U`
and of `j_!`. That is what is carried out: conditions (1) and (2) for `j_!A_U` over `(C, O)` are
transported from the corresponding conditions for `A_U` over the slice site, across the 0FRB
isomorphism and its 0FRX refinement, using
`CategoryTheory.ShortComplex.shortExact_iff_of_iso` and
`HomologicalComplex.ExactAt.of_iso`. The exactness of `j_!` is Tag 03DJ, available here as
`Stacks.Sites.ExtensionByZero.extensionByZero_exact`; the exactness of restriction is
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits` and
`..._preservesFiniteColimits`. Neither is assumed.

**Where condition (3) lives.** In
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodExtensionByZeroToposBaseChange.lean`, at the
source's own quantification over morphisms of ringed topoi, as the third conjunct of
`SheafOfModules.IsGoodToposBaseChange`. It is obtained there by identifying `j_!A_U` with the
free differential graded `A`-module on the sheaf represented by `U` in degree zero and quoting
Tag 0FSG, rather than by the source's route through Tags 03CR and 04J0; see the implementation
notes of that file. The three site-indexed readings of goodness —
`SheafOfModules.DifferentialGradedModule.IsGood`, `IsGoodCocontinuousBaseChange` and
`IsGoodSiteBaseChange` — quantify condition (3) over an arbitrary
`SheafOfModules.DifferentialGradedModule.PullbackData` along a bare functor of the two underlying
categories, which is a different family of base changes from the source's, and this file says
nothing about them.

**Both results are unconditional.** What the argument consumes on the slice
site — `SheafOfModules.RelativeTensor.IsGradedFlat` and `IsKFlat` of the regular module of `A_U`
over itself — is the identification `A_U ⊗_{A_U} N|_U = N|_U` that the source leaves unremarked,
and it is proved in this library as
`SheafOfModules.RelativeTensor.isGradedFlat_ofDifferentialGraded_regularModule` and
`SheafOfModules.RelativeTensor.isKFlat_regularModule`, both in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedRelativeTensorUnitor.lean`, from
the unit isomorphism `A ⊗_A N ≅ N` of the relative tensor product
(`SheafOfModules.RelativeTensor.dgUnitorIso`) built there. They are applied here in a term
position, so instance search runs in their own general context and never has to cross the two
spellings of the sheaf of rings discussed below.

**Universes.** Site, sheaf of rings and modules all live in one universe `u`. This matches the
library's own exactness results, which are what the proof consumes: Tag 03DJ
(`extensionByZero_exact`) is stated only for `C : Type u` with `Category.{u} C`, a sheaf of
rings in `RingCat.{u}` and modules in `SheafOfModules.{u}`, so a universe-general statement here
could not use it. The source imposes no universe discipline, so this is not a weakening of its
mathematics.

**The module `A_U`.** `SheafOfModules.DifferentialGradedModule.regularModule`, a sheaf of
differential graded algebras acting on itself on the right, is already in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeIdentity.lean`; it is reused
rather than restated.

## References

* [Stacks Project, Tag 0FSB](https://stacks.math.columbia.edu/tag/0FSB)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FRX](https://stacks.math.columbia.edu/tag/0FRX)
* [Stacks Project, Tag 0FRB](https://stacks.math.columbia.edu/tag/0FRB)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe u

namespace SheafOfModules

/-! ### Exactness of `j_!` and of restriction

Tag 03DJ and the exactness of restriction are already in the library. The lemmas of this section
only transport them to the two shapes the arguments below consume — short exactness of a short
complex, and acyclicity of a cochain complex. They are stated over
`Stacks.SheafOfModules.Tensor.ringSheaf O`, which
is the spelling the extension-by-zero development uses; the consumers below apply them to data
whose sheaf of rings is spelled `CategoryTheory.Sheaf.toRingCat J O`, which is the same sheaf of
rings but is not recognised as such by instance search, so resolving the instances here rather
than at the use sites is deliberate. -/

section Exactness

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u}) (U : C)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `j_!` preserves finite limits, by Tag 03DJ. -/
@[sga "4 XVII 5.1.1" "module version"]
private theorem extendSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (extendSheaf.{u} O U) :=
  ((exactFunctor_iff _).mp
    (Stacks.Sites.ExtensionByZero.extensionByZero_exact J
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U)).1

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `j_!` preserves finite colimits, by Tag 03DJ. -/
@[sga "4 IV 11.3.1" "partial", sga "4 XVII 5.1.1" "module version"]
private theorem extendSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (extendSheaf.{u} O U) :=
  ((exactFunctor_iff _).mp
    (Stacks.Sites.ExtensionByZero.extensionByZero_exact J
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U)).2

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restriction to `U` carries a zero composite to a zero composite. -/
private theorem restrict_comp_zero
    {M₁ M₂ M₃ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃) (hab : a ≫ b = 0) : a.over U ≫ b.over U = 0 :=
  ((ShortComplex.mk a b hab).map
    (overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U)).zero

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Restriction to `U` is exact**, in the form used below: it carries a short exact sequence of
sheaves of `O`-modules to a short exact sequence of sheaves of `O_U`-modules. -/
private theorem restrict_shortExact
    {M₁ M₂ M₃ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃) (hab : a ≫ b = 0) (hab' : a.over U ≫ b.over U = 0)
    (h : (ShortComplex.mk a b hab).ShortExact) :
    (ShortComplex.mk (a.over U) (b.over U) hab').ShortExact := by
  have hl := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U
  have hc := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U
  exact h.map_of_exact (overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Restriction to `U` preserves acyclicity**, being exact. -/
private theorem restrict_acyclic
    (K : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ℤ)
    (hK : K.Acyclic) :
    (((overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)
      U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  have hl := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U
  have hc := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U
  exact fun i => ShortComplex.Exact.map (hK i)
    (overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `j_!` carries a zero composite to a zero composite. -/
private theorem extend_comp_zero
    {K₁ K₂ K₃ : SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U)}
    (a : K₁ ⟶ K₂) (b : K₂ ⟶ K₃) (hab : a ≫ b = 0) :
    (extendSheaf.{u} O U).map a ≫ (extendSheaf.{u} O U).map b = 0 :=
  ((ShortComplex.mk a b hab).map (extendSheaf.{u} O U)).zero

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **`j_!` is exact** (Tag 03DJ), in the form used below: it carries a short exact sequence of
sheaves of `O_U`-modules to a short exact sequence of sheaves of `O`-modules. -/
@[sga "4 XVII 5.1.1" "module version"]
private theorem extend_shortExact
    {K₁ K₂ K₃ : SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U)}
    (a : K₁ ⟶ K₂) (b : K₂ ⟶ K₃) (hab : a ≫ b = 0)
    (hab' : (extendSheaf.{u} O U).map a ≫ (extendSheaf.{u} O U).map b = 0)
    (h : (ShortComplex.mk a b hab).ShortExact) :
    (ShortComplex.mk ((extendSheaf.{u} O U).map a)
      ((extendSheaf.{u} O U).map b) hab').ShortExact := by
  have hl := extendSheaf_preservesFiniteLimits.{u} O U
  have hc := extendSheaf_preservesFiniteColimits.{u} O U
  exact h.map_of_exact (extendSheaf.{u} O U)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **`j_!` preserves acyclicity**, being exact. -/
@[sga "4 XVII 5.1.1" "module version"]
private theorem extend_acyclic
    (K : CochainComplex
      (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U)) ℤ)
    (hK : K.Acyclic) :
    (((extendSheaf.{u} O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  have hl := extendSheaf_preservesFiniteLimits.{u} O U
  have hc := extendSheaf_preservesFiniteColimits.{u} O U
  exact fun i => ShortComplex.Exact.map (hK i) (extendSheaf.{u} O U)

end Exactness

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u}) (U : C)
  (A : DifferentialGradedAlgebra.{u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))

/-- **`j_!A_U`**, the extension by zero of the restriction `A_U = j^*A` of `A` to the slice site
at `U`, taken as a right differential graded `A_U`-module by its own multiplication. It is a
right differential graded `A`-module. -/
noncomputable abbrev dgExtensionByZeroRegular :
    DifferentialGradedModule.{u, u, u} A :=
  dgExtensionByZero.{u} O U A (DifferentialGradedModule.regularModule (A.over U))

variable [(J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Condition (1): `j_!A_U` is flat as a graded module -/

/-- **Tag 0FSB, condition (1).** The right graded `A`-module underlying `j_!A_U` is flat: it
carries every short exact sequence of left graded `A`-modules to a short exact sequence in every
degree.

The proof is the source's: by Tag 0FRB the functor `N ↦ j_!A_U ⊗_A N` is, in each degree, `j_!`
of `N ↦ A_U ⊗_{A_U} N|_U`, naturally in `N`; restriction and `j_!` are exact, and `A_U` is flat
over itself. -/
theorem dgExtensionByZeroRegular_isGradedFlat :
    RelativeTensor.IsGradedFlat
      (GradedModule.ofDifferentialGraded (dgExtensionByZeroRegular.{u} O U A)) := by
  have hsliceFlat : RelativeTensor.IsGradedFlat (J := J.over U) (Osharp := O.over U)
      (GradedModule.ofDifferentialGraded
        (DifferentialGradedModule.regularModule (A.over U))) :=
    RelativeTensor.isGradedFlat_ofDifferentialGraded_regularModule _
  intro N₁ N₂ N₃ f g hfg hSE n
  have hfgRes : ∀ k : ℤ, (LeftGradedModule.overMap f U).app k ≫
      (LeftGradedModule.overMap g U).app k = 0 := fun k =>
    restrict_comp_zero.{u} O U (f.app k) (g.app k) (hfg k)
  have hresSE : LeftGradedModule.ShortExact (LeftGradedModule.overMap f U)
      (LeftGradedModule.overMap g U) hfgRes := fun k =>
    restrict_shortExact.{u} O U (f.app k) (g.app k) (hfg k) (hfgRes k) (hSE k)
  obtain ⟨hsl, hslSE⟩ := hsliceFlat _ _ _ (LeftGradedModule.overMap f U)
    (LeftGradedModule.overMap g U) hfgRes hresSE n
  have hex := extend_comp_zero.{u} O U _ _ hsl
  have hexSE := extend_shortExact.{u} O U _ _ hsl hex hslSE
  have nat₁ := extendTensorHom_naturality_right.{u} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded (DifferentialGradedModule.regularModule (A.over U)))
    N₁ f n
  have nat₂ := extendTensorHom_naturality_right.{u} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded (DifferentialGradedModule.regularModule (A.over U)))
    N₂ g n
  have hz : RelativeTensor.gradedTensorMap (gradedExtensionByZero.{u} O U A.toGradedAlgebra
          (GradedModule.ofDifferentialGraded
            (DifferentialGradedModule.regularModule (A.over U)))) f n ≫
      RelativeTensor.gradedTensorMap (gradedExtensionByZero.{u} O U A.toGradedAlgebra
          (GradedModule.ofDifferentialGraded
            (DifferentialGradedModule.regularModule (A.over U)))) g n = 0 := by
    have : IsIso (extendTensorHom.{u} O U A.toGradedAlgebra
        (GradedModule.ofDifferentialGraded
          (DifferentialGradedModule.regularModule (A.over U))) N₃ n) :=
      inferInstanceAs (IsIso (extendTensorIso.{u} O U A.toGradedAlgebra
        (GradedModule.ofDifferentialGraded
          (DifferentialGradedModule.regularModule (A.over U))) N₃ n).hom)
    refine (cancel_mono (extendTensorHom.{u} O U A.toGradedAlgebra
      (GradedModule.ofDifferentialGraded
        (DifferentialGradedModule.regularModule (A.over U))) N₃ n)).mp ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (_ ≫= nat₂).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (nat₁ =≫ _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (_ ≫= hex).trans ?_
    exact comp_zero.trans zero_comp.symm
  refine ⟨hz, ?_⟩
  exact (ShortComplex.shortExact_iff_of_iso (ShortComplex.isoMk
    (extendTensorIso.{u} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded
      (DifferentialGradedModule.regularModule (A.over U))) N₁ n)
    (extendTensorIso.{u} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded
      (DifferentialGradedModule.regularModule (A.over U))) N₂ n)
    (extendTensorIso.{u} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded
      (DifferentialGradedModule.regularModule (A.over U))) N₃ n)
    nat₁.symm nat₂.symm)).mpr hexSE

/-! ### Condition (2): `j_!A_U` is K-flat -/

/-- **Tag 0FSB, condition (2).** `j_!A_U` is K-flat: `j_!A_U ⊗_A N` is acyclic for every acyclic
left differential graded `A`-module `N`.

The proof is the source's: by Tag 0FRX the complex `j_!A_U ⊗_A N` is `j_!(A_U ⊗_{A_U} N|_U)`;
restriction and `j_!` are exact, so they preserve acyclicity, and `A_U` is K-flat over
itself. -/
theorem dgExtensionByZeroRegular_isKFlat :
    RelativeTensor.IsKFlat (dgExtensionByZeroRegular.{u} O U A) := by
  have hsliceKFlat : RelativeTensor.IsKFlat (J := J.over U) (Osharp := O.over U)
      (DifferentialGradedModule.regularModule (A.over U)) :=
    RelativeTensor.isKFlat_regularModule _
  intro N hN
  have h1 : (N.over U).complex.Acyclic := restrict_acyclic.{u} O U N.complex hN
  have h2 := hsliceKFlat (N.over U) h1
  have h3 : (dgExtendSliceTensor.{u} O U A
      (DifferentialGradedModule.regularModule (A.over U)) N).Acyclic :=
    extend_acyclic.{u} O U _ h2
  exact fun i => (h3 i).of_iso (dgExtendTensorIso.{u} O U A
    (DifferentialGradedModule.regularModule (A.over U)) N).symm

end SheafOfModules

end
