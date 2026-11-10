module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SupportedQuotient.Basic

/-!
# The strict transform

Let `f : X ⟶ S` be a morphism of schemes, let `b : S' ⟶ S` be a second morphism and let `E` be a
quasi-coherent ideal sheaf on `S'`. Write `pr_X` and `pr_{S'}` for the two projections of the
base change `X ×_S S'`. The **strict transform** of a sheaf of `𝒪_X`-modules `F` is the quotient
of `pr_X^* F` by the submodule of sections supported on `pr_{S'}^{-1}(Supp E)`, and the strict
transform of `X` itself is the closed subscheme of `X ×_S S'` cut out by the ideal of sections of
the structure sheaf supported there.

Tag 080D states this for `b` the blowup of `S` in a closed subscheme `Z` and `E` the exceptional
ideal `b^{-1}Z`; the construction uses nothing about `b` or `E`, and is given here for an
arbitrary morphism and an arbitrary ideal sheaf, of which that is the instance. See the
implementation notes.

## Main definitions

* `Stacks.StrictTransform.baseChange`: the fibre product `X ×_S S'`.
* `Stacks.StrictTransform.exceptionalPreimage`: the closed subset `pr_{S'}^{-1}(Supp E)`, and
  `Stacks.StrictTransform.exceptionalComplement` its open complement.
* `Stacks.StrictTransform.sheaf`: tag 080D (1), the strict transform of a sheaf of modules, with
  its quotient map `Stacks.StrictTransform.π`.
* `Stacks.StrictTransform.ideal`: the quasi-coherent ideal of sections of the structure sheaf
  supported on `pr_{S'}^{-1}(Supp E)`, and `Stacks.StrictTransform.scheme`, tag 080D (2), the
  closed subscheme it cuts out.

## Main results

* `Stacks.StrictTransform.exists_iso`: the universal property. An epimorphism out of `pr_X^* F`
  which becomes an isomorphism away from `pr_{S'}^{-1}(Supp E)` and has no sections supported
  there *is* the strict transform.
* `Stacks.StrictTransform.isIso_restrictFunctor_map_π`,
  `Stacks.StrictTransform.supportedSections_sheaf_eq_zero` and
  `Stacks.StrictTransform.mono_unit_app_sheaf`: the three properties that characterization needs,
  for the strict transform itself.
* `Stacks.StrictTransform.ideal_eq_ker_ι`: the defining ideal of the strict transform of `X` is
  the kernel of the inclusion of the open complement of `pr_{S'}^{-1}(Supp E)`. Unconditionally;
  so the strict transform of `X` is the scheme-theoretic image of that open.
* `Stacks.StrictTransform.ideal_eq`: on an affine open the defining ideal is precisely the
  supported sections, provided the open complement of `pr_{S'}^{-1}(Supp E)` is retrocompact.
* `Stacks.StrictTransform.quasiCompact_exceptionalComplement_ι`: that proviso only concerns the
  centre, being inherited by base change from the complement of `Supp E` in `S'`;
  `Stacks.StrictTransform.quasiCompact_ι_of_isRetrocompact` is the retrocompactness criterion.
* `AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_unit_compl_iff_mem_ker`: a
  section of the structure sheaf is supported in the complement of an open `V` exactly when it is
  killed by restriction along `V.ι`.

## Implementation notes

The hypotheses of tag 080D are used in the Stacks Project only to see that the construction
behaves well, not to make it: `E` is an effective Cartier divisor (tag 02OS), hence
`pr_{S'}^{-1}E` is locally principal (tag 053P), hence its complement is retrocompact (tag 07ZT),
hence the supported sections form a *quasi-coherent* submodule (tag 07ZP).

**Tag 07ZT is in the repository, but it does not lift this obstruction on its own.** What is
proved is `Stacks.Divisors.isAffineHom_compl_of_isLocallyPrincipal` (which carries
`@[stacks 07ZT]`), giving
*affineness of the complement over the ambient scheme* — not the *retrocompactness* this chain
wants.  Retrocompactness would follow, an affine morphism being quasi-compact, but no such
statement is written.  Tag 053P remains absent.

**The blowup morphism is available.** The cartesian chart condition
`Stacks.RelativeProj.Situation.ChartsCartesian` (tag 01NO) taken by
`Stacks.RelativeProj.Situation.data` is discharged by
`Stacks.RelativeProj.Situation.chartsCartesian`, an unconditional theorem, so
`AlgebraicGeometry.blowUpToBase` and `AlgebraicGeometry.exceptionalIdeal` are
unconditional, and quasi-coherence at the blowup instance of these definitions is found by
instance search, through `Stacks.StrictTransform.isQuasicoherent_sheaf` and
`Stacks.StrictTransform.quasiCompact_ι_compl_support_exceptionalIdeal`
(`StacksFrontier/AlgebraicGeometry/StrictTransform/Quasicoherent.lean`). The definitions below
are nevertheless given for an arbitrary `b` and `E`, which is strictly more general than the tag
and specialises to it; what is still missing about blowups is tag 02OS, that a blowup is an
isomorphism away from its centre, which is where
`StacksFrontier/AlgebraicGeometry/StrictTransform/Iterated.lean` takes it as a hypothesis.

Retrocompactness is needed for exactly one statement, `Stacks.StrictTransform.ideal_eq`, because
`AlgebraicGeometry.Scheme.Hom.ker_apply` needs it: without it
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals` may saturate the given family of ideals
upwards. It is taken there as the hypothesis `QuasiCompact (exceptionalComplement f b E).ι`, which
`Stacks.StrictTransform.quasiCompact_ι_of_isRetrocompact` supplies from retrocompactness of the
open. For that reason `Stacks.StrictTransform.ideal_eq` carries no `@[stacks]` attribute while the
three definitions do.

Everything about the quotient comes from
`StacksFrontier/AlgebraicGeometry/SupportedQuotient/Basic.lean`, whose statements are phrased for
the complement `Vᶜ` of an *open* `V`. The subset here is instead written as a preimage, the form
tag 080D and its consumers use, and `(Vᶜ)ᶜ` is not syntactically `V`. The five
`..._of_compl_eq` lemmas below are therefore stated for a subset `Z` together with the hypothesis
`Z = Vᶜ` and proved by `subst`; applying them to a particular `Z` then needs no rewriting inside a
dependent type, which is what rewriting `exceptionalPreimage` into complement form directly would
require.

As recorded in the implementation notes of the file above, `AlgebraicGeometry.Scheme.Modules` is a
`def` rather than an `abbrev`, so the quotient must be formed from the named abbreviation
`AlgebraicGeometry.Scheme.Modules.supportedSectionsι` and not from
`(AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule _ _).ι`, whose type is recorded over
a syntactically different category instance.

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The quotient of `F` by the sections supported in a subset which is the complement of an open
`V` has monomorphic unit for the restriction adjunction along `V`. Complement form of
`AlgebraicGeometry.Scheme.Modules.mono_unit_app_cokernel_supportedSectionsι_compl`. -/
public lemma mono_unit_app_cokernel_supportedSectionsι_of_compl_eq (V : X.Opens) {Z : Set X}
    (hZ : Z = (V : Set X)ᶜ) (F : X.Modules) :
    Mono ((restrictAdjunction V.ι).unit.app (cokernel (supportedSectionsι Z F))) := by
  subst hZ
  exact mono_unit_app_cokernel_supportedSectionsι_compl V F

/-- The quotient map by the sections supported in a subset which is the complement of an open `V`
becomes an isomorphism after restriction to `V`. Complement form of
`AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_cokernel_π`. -/
public lemma isIso_restrictFunctor_map_cokernel_π_of_compl_eq (V : X.Opens) {Z : Set X}
    (hZ : Z = (V : Set X)ᶜ) (F : X.Modules) :
    IsIso ((restrictFunctor V.ι).map (cokernel.π (supportedSectionsι Z F))) := by
  subst hZ
  exact isIso_restrictFunctor_map_cokernel_π V F

/-- The quotient of `F` by the sections supported in a subset which is the complement of an open
`V` has no nonzero local sections supported in that subset. Complement form of
`AlgebraicGeometry.Scheme.Modules.supportedSections_compl_cokernel_eq_zero`. -/
public lemma supportedSections_cokernel_eq_zero_of_compl_eq (V : X.Opens) {Z : Set X}
    (hZ : Z = (V : Set X)ᶜ) (F : X.Modules) (U : X.Opens)
    (s : Γ(cokernel (supportedSectionsι Z F), U))
    (hs : s ∈ (supportedSectionsSubmodule Z
      (cokernel (supportedSectionsι Z F))).toSubmodule.obj (op U)) :
    s = 0 := by
  subst hZ
  exact supportedSections_compl_cokernel_eq_zero V F U s hs

/-- **The universal property of the quotient by the sections supported in a subset** which is the
complement of an open `V`. Complement form of
`AlgebraicGeometry.Scheme.Modules.exists_cokernelSupportedSectionsIso`. -/
public lemma exists_cokernelSupportedSectionsIso_of_compl_eq (V : X.Opens) {Z : Set X}
    (hZ : Z = (V : Set X)ᶜ) {F Q : X.Modules} (q : F ⟶ Q) [Epi q]
    [Mono ((restrictAdjunction V.ι).unit.app Q)] [Mono ((restrictFunctor V.ι).map q)] :
    ∃ e : cokernel (supportedSectionsι Z F) ≅ Q,
      cokernel.π (supportedSectionsι Z F) ≫ e.hom = q := by
  subst hZ
  exact exists_cokernelSupportedSectionsIso V q

/-- A section of the structure sheaf over `U` is supported in the complement of an open `V`
exactly when it lies in the kernel of the restriction map along the open immersion `V.ι`. -/
public lemma mem_supportedSectionsSubmodule_unit_compl_iff_mem_ker (V : X.Opens) (U : X.Opens)
    (s : Γ(X, U)) :
    s ∈ (supportedSectionsSubmodule (V : Set X)ᶜ
        (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U) ↔
      s ∈ RingHom.ker (V.ι.app U).hom := by
  have hQ : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U ⊓ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  have hmove (W : X.Opens) (i : W ≤ U) (hW : W = U ⊓ V) :
      (X.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op s = 0) ↔
        X.presheaf.map (homOfLE i).op s = 0 := by
    subst hW
    rfl
  have hcomp : (V.ι.appIso (V.ι ⁻¹ᵁ U)).inv.hom ((V.ι.app U).hom s) =
      X.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op s := by
    rw [← CommRingCat.comp_apply]
    exact congrArg (fun φ : Γ(X, U) ⟶ Γ(X, V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) ↦ φ.hom s)
      (Scheme.Hom.app_appIso_inv V.ι U)
  have hker : s ∈ RingHom.ker (V.ι.app U).hom ↔
      X.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op s = 0 := by
    rw [RingHom.mem_ker, hmove _ (V.ι.image_preimage_le U) hQ]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [← hcomp, h, map_zero]
    · exact (ConcreteCategory.bijective_of_isIso (V.ι.appIso (V.ι ⁻¹ᵁ U)).inv).1
        (by rw [hcomp, h, map_zero])
  exact (mem_supportedSectionsSubmodule_compl_iff_restrict_eq_zero V
    (SheafOfModules.unit X.ringCatSheaf) U s).trans hker.symm

/-- A section of the structure sheaf over `U` is supported in a subset which is the complement of
an open `V` exactly when it lies in the kernel of the restriction map along `V.ι`. Complement
form of
`AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_unit_compl_iff_mem_ker`. -/
public lemma mem_supportedSectionsSubmodule_unit_iff_mem_ker_of_compl_eq (V : X.Opens)
    {Z : Set X} (hZ : Z = (V : Set X)ᶜ) (U : X.Opens) (s : Γ(X, U)) :
    s ∈ (supportedSectionsSubmodule Z
        (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op U) ↔
      s ∈ RingHom.ker (V.ι.app U).hom := by
  subst hZ
  exact mem_supportedSectionsSubmodule_unit_compl_iff_mem_ker V U s

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.StrictTransform

open AlgebraicGeometry.Scheme.Modules hiding pullback

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (b : S' ⟶ S) (E : S'.IdealSheafData)

/-- The base change `X ×_S S'` on which the strict transform lives. -/
public abbrev baseChange : Scheme.{u} :=
  Limits.pullback f b

/-- The inverse image `pr_{S'}^{-1}(Supp E)` in `X ×_S S'` of the support of `E`. For `b` a
blowup and `E` its exceptional ideal this is the preimage of the exceptional divisor. -/
public abbrev exceptionalPreimage : Set (baseChange f b) :=
  (pullback.snd f b).base ⁻¹' E.support

/-- The open complement of `Stacks.StrictTransform.exceptionalPreimage`: the part of the base
change over which the strict transform changes nothing. -/
public abbrev exceptionalComplement : (baseChange f b).Opens :=
  pullback.snd f b ⁻¹ᵁ E.support.compl

/-- The inverse image `pr_{S'}^{-1}(Supp E)` is the complement of
`Stacks.StrictTransform.exceptionalComplement`. -/
public lemma exceptionalPreimage_eq_compl :
    exceptionalPreimage f b E = ((exceptionalComplement f b E : Set (baseChange f b)))ᶜ := by
  ext x
  simp

/-- An open whose complement is retrocompact has quasi-compact inclusion. -/
public lemma quasiCompact_ι_of_isRetrocompact {T : Scheme.{u}} (V : T.Opens)
    (hV : IsRetrocompact (V : Set T)) : QuasiCompact V.ι :=
  quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hV)

/-- The retrocompactness hypothesis of `Stacks.StrictTransform.ideal_eq` only concerns the
centre: if the complement of `Supp E` has quasi-compact inclusion into `S'`, then so does the
complement of `pr_{S'}^{-1}(Supp E)` in the base change, by base change along `pr_{S'}`. -/
public instance quasiCompact_exceptionalComplement_ι
    [QuasiCompact (Scheme.Opens.ι E.support.compl)] :
    QuasiCompact (exceptionalComplement f b E).ι := by
  have : QuasiCompact
      (pullback.fst (pullback.snd f b) (Scheme.Opens.ι E.support.compl)) :=
    quasiCompact_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (pullback.snd f b)
        (Scheme.Opens.ι E.support.compl)).flip inferInstance
  rw [← pullbackRestrictIsoRestrict_inv_fst (pullback.snd f b) E.support.compl]
  infer_instance

/-- **Stacks Project, Tag 080D (1).** The strict transform of a sheaf of `𝒪_X`-modules `F`: the
quotient of `pr_X^* F` by the submodule of sections supported on `pr_{S'}^{-1}(Supp E)`. -/
@[stacks 080D "strict transform of a module"]
public abbrev sheaf (F : X.Modules) : (baseChange f b).Modules :=
  cokernel (supportedSectionsι (exceptionalPreimage f b E)
    ((Scheme.Modules.pullback (pullback.fst f b)).obj F))

/-- The quotient map onto the strict transform. -/
public abbrev π (F : X.Modules) :
    (Scheme.Modules.pullback (pullback.fst f b)).obj F ⟶ sheaf f b E F :=
  cokernel.π _

/-- The quotient map onto the strict transform becomes an isomorphism away from
`pr_{S'}^{-1}(Supp E)`. -/
public lemma isIso_restrictFunctor_map_π (F : X.Modules) :
    IsIso ((restrictFunctor (exceptionalComplement f b E).ι).map (π f b E F)) :=
  isIso_restrictFunctor_map_cokernel_π_of_compl_eq _ (exceptionalPreimage_eq_compl f b E) _

/-- The strict transform has no nonzero local sections supported on `pr_{S'}^{-1}(Supp E)`. -/
public lemma supportedSections_sheaf_eq_zero (F : X.Modules) (U : (baseChange f b).Opens)
    (s : Γ(sheaf f b E F, U))
    (hs : s ∈ (supportedSectionsSubmodule (exceptionalPreimage f b E)
      (sheaf f b E F)).toSubmodule.obj (op U)) : s = 0 :=
  supportedSections_cokernel_eq_zero_of_compl_eq _ (exceptionalPreimage_eq_compl f b E) _ U s hs

/-- The unit of the restriction adjunction away from `pr_{S'}^{-1}(Supp E)` is a monomorphism on
the strict transform. -/
public lemma mono_unit_app_sheaf (F : X.Modules) :
    Mono ((restrictAdjunction (exceptionalComplement f b E).ι).unit.app (sheaf f b E F)) :=
  mono_unit_app_cokernel_supportedSectionsι_of_compl_eq _ (exceptionalPreimage_eq_compl f b E) _

/-- **The universal property of the strict transform.** An epimorphism out of `pr_X^* F` which
becomes an isomorphism away from `pr_{S'}^{-1}(Supp E)` and whose target has no sections supported
there is the quotient map onto the strict transform, compatibly. -/
public lemma exists_iso (F : X.Modules) {Q : (baseChange f b).Modules}
    (q : (Scheme.Modules.pullback (pullback.fst f b)).obj F ⟶ Q) [Epi q]
    [Mono ((restrictAdjunction (exceptionalComplement f b E).ι).unit.app Q)]
    [Mono ((restrictFunctor (exceptionalComplement f b E).ι).map q)] :
    ∃ e : sheaf f b E F ≅ Q, π f b E F ≫ e.hom = q :=
  exists_cokernelSupportedSectionsIso_of_compl_eq _ (exceptionalPreimage_eq_compl f b E) q

/-- The quasi-coherent ideal of sections of `𝒪_{X ×_S S'}` supported on
`pr_{S'}^{-1}(Supp E)`, assembled from its values on affine opens. -/
@[stacks 080D "ideal of the strict transform of a scheme"]
public def ideal : (baseChange f b).IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦
    (supportedSectionsSubmodule (exceptionalPreimage f b E)
      (SheafOfModules.unit (baseChange f b).ringCatSheaf)).toSubmodule.obj (op U.1)

/-- **Stacks Project, Tag 080D (2).** The strict transform of `X`: the closed subscheme of
`X ×_S S'` cut out by the ideal of sections supported on `pr_{S'}^{-1}(Supp E)`. -/
@[stacks 080D "strict transform of a scheme", sga "7 X 2.4" "more general"]
public abbrev scheme : Scheme.{u} :=
  (ideal f b E).subscheme

/-- The sections of the structure sheaf over `U` supported on `pr_{S'}^{-1}(Supp E)` form the
kernel of restriction to the open complement. -/
private theorem supportedSections_unit_eq_ker (U : (baseChange f b).Opens) :
    (supportedSectionsSubmodule (exceptionalPreimage f b E)
        (SheafOfModules.unit (baseChange f b).ringCatSheaf)).toSubmodule.obj (op U) =
      RingHom.ker ((exceptionalComplement f b E).ι.app U).hom :=
  Ideal.ext fun s ↦ mem_supportedSectionsSubmodule_unit_iff_mem_ker_of_compl_eq _
    (exceptionalPreimage_eq_compl f b E) U s

/-- The defining ideal of the strict transform of `X` is the kernel of the inclusion of the open
complement of `pr_{S'}^{-1}(Supp E)`; so the strict transform is the scheme-theoretic image of
that open. -/
@[sga "7 X 2.4" "more general"]
public lemma ideal_eq_ker_ι : ideal f b E = (exceptionalComplement f b E).ι.ker := by
  dsimp only [ideal, Scheme.Hom.ker]
  exact congrArg Scheme.IdealSheafData.ofIdeals
    (funext fun U ↦ supportedSections_unit_eq_ker f b E U.1)

/-- On an affine open the defining ideal of the strict transform of `X` consists precisely of the
sections supported on `pr_{S'}^{-1}(Supp E)`: nothing is lost in assembling the ideal from its
affine-local values. This is tag 080D's characterization of the defining ideal; it needs the
complement of `pr_{S'}^{-1}(Supp E)` to be retrocompact, which in the Stacks Project follows from
`E` being an effective Cartier divisor. -/
public theorem ideal_eq [QuasiCompact (exceptionalComplement f b E).ι]
    (U : (baseChange f b).affineOpens) :
    (ideal f b E).ideal U =
      (supportedSectionsSubmodule (exceptionalPreimage f b E)
        (SheafOfModules.unit (baseChange f b).ringCatSheaf)).toSubmodule.obj (op U.1) := by
  rw [ideal_eq_ker_ι, Scheme.Hom.ker_apply]
  exact (supportedSections_unit_eq_ker f b E U.1).symm

end Stacks.StrictTransform

end
