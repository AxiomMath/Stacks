module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSections

/-!
# The quotient by the sections supported in a closed subset

Let `X` be a scheme, `V ⊆ X` an open subset and `F` a sheaf of `𝒪_X`-modules. The sections of
`F` supported in the closed complement of `V` form a submodule
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule Vᶜ F` (tag 084L), and this file
identifies its quotient: the projection `F ⟶ F / Γ_{Vᶜ}(F)` is, up to a unique isomorphism,
*the* epimorphism out of `F` which becomes an isomorphism after restriction to `V` and whose
target has no nonzero local sections supported in `Vᶜ`.

That characterization is the engine of the strict transform of a quasi-coherent module along a
blowup (tag 080D) and of the comparison of iterated strict transforms (tag 080I), neither of
which can be stated in this repository yet; see the implementation notes. Nothing in this file
mentions blowups.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.supportedSectionsObj` and
  `AlgebraicGeometry.Scheme.Modules.supportedSectionsι`: the submodule of sections supported in
  a subset and its inclusion, with their types recorded as a sheaf of modules on the scheme and
  a morphism of such.
* `AlgebraicGeometry.Scheme.Modules.supportedQuotientToRestriction`: the map from the quotient
  into the pushforward of the restriction to `V`, induced by the fact that a section supported
  in `Vᶜ` restricts to zero on `V`.
* `Stacks.Abelian.isoOfEpiSameKernel`: two epimorphisms out of a common source whose kernels
  agree — in the sense that a morphism dies against one exactly when it dies against the
  other — have canonically isomorphic targets.

## Main results

* `AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_compl_iff_unit_app_eq_zero`:
  a section is supported in `Vᶜ` exactly when the unit of the restriction adjunction kills it.
* `AlgebraicGeometry.Scheme.Modules.isLimit_kernelFork_supportedSectionsι_compl`: the inclusion
  of the sections supported in `Vᶜ` *is* the kernel of that unit.
* `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_cokernel_π`: the quotient map
  becomes an isomorphism on `V`.
* `AlgebraicGeometry.Scheme.Modules.supportedSections_compl_cokernel_eq_zero`: the quotient has
  no nonzero local sections supported in `Vᶜ`.
* `AlgebraicGeometry.Scheme.Modules.exists_cokernelSupportedSectionsIso`: the universal
  property. Any epimorphism `q : F ⟶ Q` which restricts to an isomorphism on `V` and whose
  target has no sections supported in `Vᶜ` is the quotient map, compatibly.
* `AlgebraicGeometry.Scheme.Modules.supportedSections_eq_zero_of_mono`,
  `AlgebraicGeometry.Scheme.Modules.supportedSections_eq_zero_of_restrict` and
  `AlgebraicGeometry.Scheme.Modules.supportedSections_eq_zero_of_pullback`: having no nonzero
  sections supported in a subset passes to submodules, and is inherited by the restriction and
  the pullback along an open immersion, for the preimage of that subset.
* `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_pullback_map` and
  `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_le`: becoming an isomorphism
  over an open is inherited by pullback along an open immersion, and by smaller opens.

## Implementation notes

The whole file is organised around a single criterion: for a section `s` of `F` over `U`,

* `s` is supported in `Vᶜ`,
* the restriction of `s` to `U ⊓ V` is zero,
* `((restrictAdjunction V.ι).unit.app F).app U s = 0`

are equivalent, and the third is the one that composes. It turns the support condition into the
vanishing of a morphism of sheaves of modules, which is what makes the kernel computation, and
hence the universal property, available.

`AlgebraicGeometry.Scheme.Modules.supportedSectionsObj` and
`AlgebraicGeometry.Scheme.Modules.supportedSectionsι` exist for a technical reason worth
recording, since every construction below goes through them.
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule` is a
`SheafOfModules.Submodule`, and its `toSheafOfModules` and `ι` are stated over the site of
opens of `X` as that structure sees it. `AlgebraicGeometry.Scheme.Modules` is a `def`, not an
`abbrev`, so the category instance on `X.Modules` is a syntactically different term from the one
carried by `SheafOfModules.Submodule.ι`, even though the two are definitionally equal. Instance
search is syntactic, so `(supportedSectionsSubmodule Z F).ι ≫ φ = 0` does not elaborate: the
zero morphism cannot be found. Both declarations here are `abbrev`s whose type is *declared* to
be `X.Modules` and a morphism of `X.Modules`, which records the right instance once and for all
and is definitionally transparent to everything downstream.

That a monomorphism of `𝒪_X`-modules is injective on sections is
`Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono`, which is where this
repository already has it; the import of
`StacksFrontier/AlgebraicGeometry/CardinalGeneration/Basic.lean` is only for that lemma, and the
lemma deserves a general home rather than a file about Gabber's cardinal.

No `@[stacks]` attribute for tag 080I is claimed here. The cartesian chart condition
`Stacks.RelativeProj.Situation.ChartsCartesian` (tag 01NO) is not an extra hypothesis of
`Stacks.RelativeProj.Situation.data`: `Stacks.RelativeProj.Situation.chartsCartesian`
(`StacksFrontier/AlgebraicGeometry/RelativeProjSituation/ChartsCartesian.lean`) is an unconditional
theorem, so `AlgebraicGeometry.blowUp`, `AlgebraicGeometry.blowUpToBase` and
`AlgebraicGeometry.exceptionalIdeal` are unconditional constructions; and tag 080D is proved, as
`Stacks.StrictTransform.{sheaf, ideal, scheme}`
(`StacksFrontier/AlgebraicGeometry/StrictTransform/Basic.lean`), stated for an arbitrary second
morphism and an arbitrary ideal sheaf on its source.

What tag 080I needs beyond this file is therefore tag 080H, the comparison of the strict
transforms in a center and in its product with an effective Cartier divisor; the geometric
transport of the exceptional preimage across the identification of the two iterated base changes
(`Stacks.StrictTransform.iso_preimage_exceptionalPreimage`, proved in
`StacksFrontier/AlgebraicGeometry/StrictTransform/Iterated.lean`); and tag 02OS, that a blowup
is an isomorphism away from its centre, which is the one input of that transport that the
repository does not have. Given those, the Stacks proof of 080I runs as follows: both
`(p ∘ q)^*F ⟶ F''` and `(p ∘ q)^*F ⟶ G` are epimorphisms; they have the same kernel, because
each becomes an isomorphism off the union of the two centers, which is
`AlgebraicGeometry.Scheme.Modules.comp_eq_zero_iff_restrictFunctor_map_eq_zero` twice; and
`Stacks.Abelian.isoOfEpiSameKernel` concludes. Every step of that argument other than the
appeal to tag 080H is proved below.

## References

* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Abelian

/-- Two epimorphisms out of a common source with the same kernel — detected by the criterion
that a morphism into the source dies against one exactly when it dies against the other — have
isomorphic targets. -/
public def isoOfEpiSameKernel {C : Type*} [Category* C] [Abelian C]
    {A B D : C} (p : A ⟶ B) (q : A ⟶ D) [Epi p] [Epi q]
    (h : ∀ {W : C} (f : W ⟶ A), f ≫ p = 0 ↔ f ≫ q = 0) :
    B ≅ D :=
  ((ShortComplex.mk (kernel.ι p) p (kernel.condition p)).exact_of_f_is_kernel
      (kernelIsKernel p)).gIsCokernel.coconePointUniqueUpToIso
    ((ShortComplex.mk (kernel.ι p) q
      ((h (kernel.ι p)).mp (kernel.condition p))).exact_of_f_is_kernel
        (KernelFork.isLimitOfIsLimitOfIff' (kernelIsKernel p) q fun _ f ↦ h f)).gIsCokernel

/-- `Stacks.Abelian.isoOfEpiSameKernel` identifies the two epimorphisms. -/
public lemma isoOfEpiSameKernel_fac {C : Type*} [Category* C] [Abelian C]
    {A B D : C} (p : A ⟶ B) (q : A ⟶ D) [Epi p] [Epi q]
    (h : ∀ {W : C} (f : W ⟶ A), f ≫ p = 0 ↔ f ≫ q = 0) :
    p ≫ (isoOfEpiSameKernel p q h).hom = q := by
  unfold isoOfEpiSameKernel
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (s := CokernelCofork.ofπ p (kernel.condition p)) _ _ WalkingParallelPair.one

end Stacks.Abelian

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The sections of `F` supported in `Z`, as a sheaf of modules on `X`. This is
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule` with its type recorded as
`X.Modules`; see the implementation notes of this file for why that matters. -/
public abbrev supportedSectionsObj (Z : Set X) (F : X.Modules) : X.Modules :=
  (supportedSectionsSubmodule Z F).toSheafOfModules

/-- The inclusion of the sections of `F` supported in `Z`, as a morphism of sheaves of modules
on `X`. -/
public abbrev supportedSectionsι (Z : Set X) (F : X.Modules) : supportedSectionsObj Z F ⟶ F :=
  (supportedSectionsSubmodule Z F).ι

/-- The inclusion of the sections of `F` supported in `Z` is a monomorphism. -/
public instance mono_supportedSectionsι (Z : Set X) (F : X.Modules) :
    Mono (supportedSectionsι Z F) :=
  (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
    (PresheafOfModules.mono_of_injective fun _ ↦ Subtype.val_injective)

/-- A section of `F` over `U` is supported in the complement of an open `V` exactly when it
restricts to zero on `U ⊓ V`. -/
public lemma mem_supportedSectionsSubmodule_compl_iff_restrict_eq_zero
    (V : X.Opens) (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) :
    s ∈ (supportedSectionsSubmodule (V : Set X)ᶜ F).toSubmodule.obj (op U) ↔
      F.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op s = 0 := by
  rw [mem_supportedSectionsSubmodule_iff]
  constructor
  · intro hs
    apply TopCat.Presheaf.IsSheaf.section_ext F.isSheaf
    intro x hx
    have hz : F.presheaf.germ (U ⊓ V) x hx
        (F.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op s) =
        F.presheaf.germ (U ⊓ V) x hx 0 := by
      rw [TopCat.Presheaf.germ_res_apply, map_zero]
      exact hs x hx.1 (by simpa using hx.2)
    obtain ⟨W, hxW, i, j, h⟩ := F.presheaf.germ_eq x hx hx _ _ hz
    refine ⟨W, i.le, hxW, ?_⟩
    simpa only [Subsingleton.elim j (homOfLE i.le), Subsingleton.elim i (homOfLE i.le)] using h
  · intro hs x hx hxV
    show F.presheaf.germ U x hx s = 0
    rw [← TopCat.Presheaf.germ_res_apply F.presheaf
      (homOfLE (show U ⊓ V ≤ U from inf_le_left)) x ⟨hx, by simpa using hxV⟩, hs, map_zero]

/-- A section of `F` over `U` is supported in the complement of an open `V` exactly when the
unit of the restriction adjunction along `V` kills it. -/
public lemma mem_supportedSectionsSubmodule_compl_iff_unit_app_eq_zero
    (V : X.Opens) (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) :
    s ∈ (supportedSectionsSubmodule (V : Set X)ᶜ F).toSubmodule.obj (op U) ↔
      ((restrictAdjunction V.ι).unit.app F).app U s = 0 := by
  rw [mem_supportedSectionsSubmodule_compl_iff_restrict_eq_zero]
  show _ ↔ F.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op s = 0
  have h : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U ⊓ V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  have aux (W : X.Opens) (i : W ≤ U) (hW : W = U ⊓ V) :
      (F.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op s = 0) ↔
        F.presheaf.map (homOfLE i).op s = 0 := by
    subst W
    rfl
  exact aux _ _ h

/-- The inclusion of the sections supported in the complement of `V` is killed by the unit of
the restriction adjunction along `V`. -/
public lemma supportedSectionsι_compl_comp_unit (V : X.Opens) (F : X.Modules) :
    supportedSectionsι (V : Set X)ᶜ F ≫ (restrictAdjunction V.ι).unit.app F = 0 :=
  Scheme.Modules.hom_ext _ _ fun U ↦ by
    ext s
    exact (mem_supportedSectionsSubmodule_compl_iff_unit_app_eq_zero V F U s.1).mp s.2

/-- The sections supported in the complement of `V` are precisely the kernel of the unit of the
restriction adjunction along `V`. -/
public def isLimit_kernelFork_supportedSectionsι_compl (V : X.Opens) (F : X.Modules) :
    IsLimit (KernelFork.ofι (supportedSectionsι (V : Set X)ᶜ F)
      (supportedSectionsι_compl_comp_unit V F)) := by
  apply KernelFork.IsLimit.ofι'
  intro A k hk
  refine ⟨⟨{ app := fun U ↦ ModuleCat.ofHom ((k.val.app U).hom.codRestrict _ fun s ↦ ?_)
             naturality := ?_ }⟩, ?_⟩
  · refine (mem_supportedSectionsSubmodule_compl_iff_unit_app_eq_zero V F U.unop _).mpr ?_
    exact congrArg (fun t : A ⟶ (pushforward V.ι).obj (F.restrict V.ι) ↦ t.val.app U s) hk
  · intro U W i
    ext s
    exact Subtype.ext (PresheafOfModules.naturality_apply k.val i s)
  · rfl

/-- The map from the quotient of `F` by the sections supported in the complement of `V` into
the pushforward of the restriction of `F` to `V`. -/
public def supportedQuotientToRestriction (V : X.Opens) (F : X.Modules) :
    cokernel (supportedSectionsι (V : Set X)ᶜ F) ⟶ (pushforward V.ι).obj (F.restrict V.ι) :=
  cokernel.desc _ ((restrictAdjunction V.ι).unit.app F) (supportedSectionsι_compl_comp_unit V F)

/-- The quotient map by the sections supported in the complement of `V`, followed by
`supportedQuotientToRestriction`, is the unit of the restriction adjunction along `V`. -/
@[simp]
public lemma cokernel_π_comp_supportedQuotientToRestriction (V : X.Opens) (F : X.Modules) :
    cokernel.π (supportedSectionsι (V : Set X)ᶜ F) ≫ supportedQuotientToRestriction V F =
      (restrictAdjunction V.ι).unit.app F :=
  cokernel.π_desc _ _ _

/-- The quotient of `F` by the sections supported in the complement of `V` injects into the
pushforward of the restriction of `F` to `V`. -/
public lemma mono_supportedQuotientToRestriction (V : X.Opens) (F : X.Modules) :
    Mono (supportedQuotientToRestriction V F) :=
  ((ShortComplex.mk _ _ (supportedSectionsι_compl_comp_unit V F)).exact_of_f_is_kernel
    (isLimit_kernelFork_supportedSectionsι_compl V F)).mono_cokernelDesc

/-- The unit of the restriction adjunction along `V` is a monomorphism on the quotient of `F`
by the sections supported in the complement of `V`. -/
public lemma mono_unit_app_cokernel_supportedSectionsι_compl (V : X.Opens) (F : X.Modules) :
    Mono ((restrictAdjunction V.ι).unit.app (cokernel (supportedSectionsι (V : Set X)ᶜ F))) := by
  have : Mono (supportedQuotientToRestriction V F) := mono_supportedQuotientToRestriction V F
  have : IsIso ((restrictAdjunction V.ι).unit.app
    ((pushforward V.ι).obj (F.restrict V.ι))) := inferInstance
  have hnat : (restrictAdjunction V.ι).unit.app (cokernel (supportedSectionsι (V : Set X)ᶜ F)) ≫
      (restrictFunctor V.ι ⋙ pushforward V.ι).map (supportedQuotientToRestriction V F) =
      supportedQuotientToRestriction V F ≫
        (restrictAdjunction V.ι).unit.app ((pushforward V.ι).obj (F.restrict V.ι)) :=
    ((restrictAdjunction V.ι).unit.naturality (supportedQuotientToRestriction V F)).symm
  exact mono_of_mono_fac hnat

/-- The quotient of `F` by the sections supported in the complement of `V` has no nonzero local
sections supported in the complement of `V`. -/
public lemma supportedSections_compl_cokernel_eq_zero (V : X.Opens) (F : X.Modules)
    (U : X.Opens) (s : Γ(cokernel (supportedSectionsι (V : Set X)ᶜ F), U))
    (hs : s ∈ (supportedSectionsSubmodule (V : Set X)ᶜ
      (cokernel (supportedSectionsι (V : Set X)ᶜ F))).toSubmodule.obj (op U)) :
    s = 0 := by
  have := mono_unit_app_cokernel_supportedSectionsι_compl V F
  refine Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono
    ((restrictAdjunction V.ι).unit.app (cokernel (supportedSectionsι (V : Set X)ᶜ F))) U ?_
  exact ((mem_supportedSectionsSubmodule_compl_iff_unit_app_eq_zero V _ U s).mp hs).trans
    (map_zero _).symm

/-- The quotient map by the sections supported in the complement of `V` becomes an isomorphism
after restriction to `V`. -/
public lemma isIso_restrictFunctor_map_cokernel_π (V : X.Opens) (F : X.Modules) :
    IsIso ((restrictFunctor V.ι).map (cokernel.π (supportedSectionsι (V : Set X)ᶜ F))) := by
  have : IsIso ((restrictFunctor V.ι).map ((restrictAdjunction V.ι).unit.app F)) := inferInstance
  have hfac : (restrictFunctor V.ι).map (cokernel.π (supportedSectionsι (V : Set X)ᶜ F)) ≫
      (restrictFunctor V.ι).map (supportedQuotientToRestriction V F) =
      (restrictFunctor V.ι).map ((restrictAdjunction V.ι).unit.app F) := by
    rw [← Functor.map_comp, cokernel_π_comp_supportedQuotientToRestriction]
  have : Mono ((restrictFunctor V.ι).map (cokernel.π (supportedSectionsι (V : Set X)ᶜ F))) :=
    mono_of_mono_fac hfac
  exact isIso_of_mono_of_epi _

/-- Composing with a morphism that restricts to a monomorphism on `V`, and whose target has
monomorphic unit, detects vanishing on `V`. -/
public lemma comp_eq_zero_iff_restrictFunctor_map_eq_zero (V : X.Opens) {A B D : X.Modules}
    (q : A ⟶ B) [Mono ((restrictAdjunction V.ι).unit.app B)]
    [Mono ((restrictFunctor V.ι).map q)] (f : D ⟶ A) :
    f ≫ q = 0 ↔ (restrictFunctor V.ι).map f = 0 := by
  constructor
  · intro hf
    rw [← cancel_mono ((restrictFunctor V.ι).map q), zero_comp, ← Functor.map_comp, hf,
      Functor.map_zero]
  · intro hf
    have hnat : (f ≫ q) ≫ (restrictAdjunction V.ι).unit.app B =
        (restrictAdjunction V.ι).unit.app D ≫
          (restrictFunctor V.ι ⋙ pushforward V.ι).map (f ≫ q) :=
      (restrictAdjunction V.ι).unit.naturality (f ≫ q)
    rw [← cancel_mono ((restrictAdjunction V.ι).unit.app B), zero_comp, hnat]
    show (restrictAdjunction V.ι).unit.app D ≫
      (pushforward V.ι).map ((restrictFunctor V.ι).map (f ≫ q)) = 0
    simp [hf]

/-- **The universal property of the quotient by the sections supported in `Vᶜ`.** An
epimorphism out of `F` which becomes an isomorphism on `V` and whose target has monomorphic
unit is the quotient map, compatibly. -/
public lemma exists_cokernelSupportedSectionsIso (V : X.Opens) {F Q : X.Modules} (q : F ⟶ Q)
    [Epi q] [Mono ((restrictAdjunction V.ι).unit.app Q)]
    [Mono ((restrictFunctor V.ι).map q)] :
    ∃ e : cokernel (supportedSectionsι (V : Set X)ᶜ F) ≅ Q,
      cokernel.π (supportedSectionsι (V : Set X)ᶜ F) ≫ e.hom = q := by
  have := mono_unit_app_cokernel_supportedSectionsι_compl V F
  have := isIso_restrictFunctor_map_cokernel_π V F
  have h {W : X.Modules} (f : W ⟶ F) :
      f ≫ cokernel.π (supportedSectionsι (V : Set X)ᶜ F) = 0 ↔ f ≫ q = 0 :=
    (comp_eq_zero_iff_restrictFunctor_map_eq_zero V _ f).trans
      (comp_eq_zero_iff_restrictFunctor_map_eq_zero V q f).symm
  exact ⟨Stacks.Abelian.isoOfEpiSameKernel _ q h, Stacks.Abelian.isoOfEpiSameKernel_fac _ q h⟩

/-- A sheaf of modules with no nonzero local sections supported in the complement of `V` has
monomorphic unit for the restriction adjunction along `V`. -/
public lemma mono_unit_app_of_supportedSections_eq_zero (V : X.Opens) (F : X.Modules)
    (h : ∀ (U : X.Opens) (s : Γ(F, U)),
      s ∈ (supportedSectionsSubmodule (V : Set X)ᶜ F).toSubmodule.obj (op U) → s = 0) :
    Mono ((restrictAdjunction V.ι).unit.app F) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  refine (injective_iff_map_eq_zero _).mpr fun s hs ↦ ?_
  exact h U.unop s
    ((mem_supportedSectionsSubmodule_compl_iff_unit_app_eq_zero V F U.unop s).mpr hs)

/-- Having monomorphic unit transfers along an isomorphism. -/
public lemma mono_unit_app_of_iso (V : X.Opens) {F G : X.Modules} (e : F ≅ G)
    [Mono ((restrictAdjunction V.ι).unit.app F)] :
    Mono ((restrictAdjunction V.ι).unit.app G) := by
  have hmono : Mono ((𝟭 X.Modules).map e.inv ≫ (restrictAdjunction V.ι).unit.app F) :=
    inferInstance
  exact mono_of_mono_fac ((restrictAdjunction V.ι).unit.naturality e.inv).symm

/-- A morphism of sheaves of modules carries sections supported in a subset to sections
supported in that subset. -/
public lemma map_mem_supportedSectionsSubmodule {F G : X.Modules} (Z : Set X) (φ : F ⟶ G)
    (U : X.Opens) (s : Γ(F, U))
    (hs : s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U)) :
    φ.app U s ∈ (supportedSectionsSubmodule Z G).toSubmodule.obj (op U) := by
  rw [mem_supportedSectionsSubmodule_iff] at hs ⊢
  intro x hx hxZ
  have hz := hs x hx hxZ
  change F.presheaf.germ U x hx s = 0 at hz
  show G.presheaf.germ U x hx (φ.app U s) = 0
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ.mapPresheaf s).symm.trans ?_
  refine (congrArg _ hz).trans ?_
  exact map_zero _

/-- Having no nonzero sections supported in a subset passes to submodules. -/
public lemma supportedSections_eq_zero_of_mono {F G : X.Modules} (Z : Set X) (φ : F ⟶ G)
    (hφ : Mono φ)
    (hG : ∀ (U : X.Opens) (s : Γ(G, U)),
      s ∈ (supportedSectionsSubmodule Z G).toSubmodule.obj (op U) → s = 0)
    (U : X.Opens) (s : Γ(F, U))
    (hs : s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U)) : s = 0 := by
  have := hφ
  refine Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono φ U ?_
  exact (hG U (φ.app U s) (map_mem_supportedSectionsSubmodule Z φ U s hs)).trans (map_zero _).symm

/-- Having no nonzero sections supported in a subset is inherited by the restriction along an
open immersion, for the preimage of that subset. -/
public lemma supportedSections_eq_zero_of_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (Z : Set Y) (F : Y.Modules)
    (hF : ∀ (U : Y.Opens) (s : Γ(F, U)),
      s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) → s = 0)
    (U : X.Opens) (s : Γ(F.restrict f, U))
    (hs : s ∈ (supportedSectionsSubmodule (f.base ⁻¹' Z)
      (F.restrict f)).toSubmodule.obj (op U)) : s = 0 := by
  refine (AddCommGrpCat.mono_iff_injective (restrictAppIso f F U).hom).mp inferInstance ?_
  rw [map_zero]
  refine hF _ _ ?_
  rw [mem_supportedSectionsSubmodule_iff] at hs ⊢
  intro y hy hyZ
  obtain ⟨x, hx, rfl⟩ := hy
  have hz := hs x hx hyZ
  change (F.restrict f).presheaf.germ U x hx s = 0 at hz
  have h := congrArg (fun a : Γ(F.restrict f, U) ⟶ F.presheaf.stalk (f x) ↦ a s)
    (germ_restrictStalkNatIso_hom_app f x F hx)
  show F.presheaf.germ (f ''ᵁ U) (f x) _ ((restrictAppIso f F U).hom s) = 0
  refine h.symm.trans ?_
  show (restrictStalkNatIso f x).hom.app F ((F.restrict f).presheaf.germ U x hx s) = 0
  refine (congrArg _ hz).trans ?_
  exact map_zero _

/-- Having no nonzero sections supported in a subset is inherited by the pullback along an open
immersion, for the preimage of that subset. -/
public lemma supportedSections_eq_zero_of_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (Z : Set Y) (F : Y.Modules)
    (hF : ∀ (U : Y.Opens) (s : Γ(F, U)),
      s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) → s = 0)
    (U : X.Opens) (s : Γ((Scheme.Modules.pullback f).obj F, U))
    (hs : s ∈ (supportedSectionsSubmodule (f.base ⁻¹' Z)
      ((Scheme.Modules.pullback f).obj F)).toSubmodule.obj (op U)) : s = 0 :=
  supportedSections_eq_zero_of_mono _ ((restrictFunctorIsoPullback f).app F).inv
    inferInstance (supportedSections_eq_zero_of_restrict f Z F hF) U s hs

/-- Restricting to an open and then pulling back along an open immersion: if a morphism becomes
an isomorphism over `V`, its pullback becomes an isomorphism over the preimage of `V`. -/
public lemma isIso_restrictFunctor_map_pullback_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) {F G : Y.Modules} (q : F ⟶ G)
    [IsIso ((restrictFunctor V.ι).map q)] :
    IsIso ((restrictFunctor (f ⁻¹ᵁ V).ι).map ((Scheme.Modules.pullback f).map q)) := by
  have : IsIso ((Scheme.Modules.pullback V.ι).map q) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback V.ι) q).mp inferInstance
  have e : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (f ⁻¹ᵁ V).ι ≅
      Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.pullback (f ∣_ V) :=
    pullbackComp _ _ ≪≫ pullbackCongr (morphismRestrict_ι f V).symm ≪≫ (pullbackComp _ _).symm
  have : IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).map
      ((Scheme.Modules.pullback f).map q)) := (NatIso.isIso_map_iff e q).mpr (by
    show IsIso ((Scheme.Modules.pullback (f ∣_ V)).map ((Scheme.Modules.pullback V.ι).map q))
    infer_instance)
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι)
    ((Scheme.Modules.pullback f).map q)).mpr inferInstance

/-- Becoming an isomorphism over an open is inherited by smaller opens. -/
public lemma isIso_restrictFunctor_map_of_le {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
    {F G : X.Modules} (q : F ⟶ G) [IsIso ((restrictFunctor V.ι).map q)] :
    IsIso ((restrictFunctor U.ι).map q) := by
  have e : restrictFunctor U.ι ≅ restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h) :=
    restrictFunctorCongr (X.homOfLE_ι h).symm ≪≫ restrictFunctorComp _ _
  exact (NatIso.isIso_map_iff e q).mpr (by
    show IsIso ((restrictFunctor (X.homOfLE h)).map ((restrictFunctor V.ι).map q))
    infer_instance)

end AlgebraicGeometry.Scheme.Modules

end
