module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafComplexLocalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicReductions
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Modules
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SmallSiteSituation

/-!
# Global sections of a constant sheaf over a weakly contractible scheme

Let `X` be a weakly contractible affine scheme, `Λ` a commutative ring and `I ⊆ Λ` an ideal.
This file constructs the functor

`V : M ↦ Γ(X, \underline{M})`

from `Λ^∧`-modules to `Λ`-modules — restriction of scalars along `Λ → Λ^∧`, the constant sheaf
of `Λ`-modules on the small pro-étale site of `X`, and sections over the terminal object of that
site — and proves it **exact**.

This is the functor the source of Stacks 09C5 calls `Γ(X, -)` of the constant sheaf, whose
exactness is the only use that proof makes of weak contractibility of `X`. It is supplied here
as reusable infrastructure; see
`StacksFrontier/AlgebraicGeometry/ProEtale/LocallyConstantAdicModel.lean` for where Stacks 09C5
needs it and for what else that chain still lacks.

## Main results

* `Stacks.WeaklyContractible.surjective_app_of_iso`: surjectivity on sections over an object of
  a site transports along an isomorphism of objects.
* `Stacks.WeaklyContractible.preservesEpimorphisms_sheafSections_moduleCat`: sections over a
  weakly contractible object carry an epimorphism of sheaves of `Λ`-modules to a surjection.
* `Stacks.WeaklyContractible.preservesFiniteColimits_sheafSections_moduleCat`: hence those
  sections are right exact; with the left exactness already in the library
  (`Stacks.ConstantSheaf.sheafSections_preservesFiniteLimits`) they are exact. This is the
  `ModuleCat`-valued counterpart of Stacks 0946 (1),
  `Stacks.WeaklyContractible.exact_sheafSections_of_isWeaklyContractible`, which is stated for
  abelian sheaves.
* `AlgebraicGeometry.ProEtale.surjective_sections_terminal_of_isWContractible`: weak
  contractibility of the terminal object of `X.ProEt`, in the explicit surjectivity form and at
  an arbitrary value universe.
* `AlgebraicGeometry.ProEtale.constantGlobalSections`: the functor `V` above.
* `AlgebraicGeometry.ProEtale.isWContractible_globalSections_of_isWeaklyContractibleObj`: an
  affine scheme which is weakly contractible as an object of the big pro-étale site has
  w-contractible ring of global sections.
* `AlgebraicGeometry.ProEtale.additive_constantGlobalSections`,
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_constantGlobalSections`,
  `AlgebraicGeometry.ProEtale.preservesFiniteColimits_constantGlobalSections` and
  `ProEtale.preservesFiniteColimits_constantGlobalSections_of_isWeaklyContractibleObj` (in
  `AlgebraicGeometry`): `V` is additive and exact, the last taking weak contractibility in the
  big-site form.

## Implementation notes

Weak contractibility enters as `ProetaleWContractible.IsWContractible Γ(X, ⊤)`, the
w-contractibility of the ring of global sections, which is the form
`AlgebraicGeometry.Scheme.ProEt.surjective_sections_of_isWContractible` consumes and the form in
which the value universe of the test sheaves of sets is free. By Stacks 098H
(`ProetaleWContractible.main_theorem`) it is equivalent, for `X = Spec A`, to weak
contractibility of `X` as an object of the big pro-étale site, which is the form
`ProetaleWContractible.IsWeaklyContractibleObj` in which this library's statements about weakly
contractible schemes are phrased; `isWContractible_globalSections_of_isWeaklyContractibleObj`
performs that comparison for an arbitrary affine `X`, by transporting the big-site condition
along `AlgebraicGeometry.Scheme.isoSpec` first.

The sections are taken over `⊤_ X.ProEt`, the categorical terminal object, because that is the
object `AlgebraicGeometry.ProEtale.reductionSectionsSystem` of Stacks 09C5 uses.
`AlgebraicGeometry.ProEtale.isTerminalProEtId` identifies it, up to canonical isomorphism, with
the identity of `X`, which is the object the weak-contractibility input speaks about; the
transport is `Stacks.WeaklyContractible.surjective_app_of_iso`.

The module universe of the general statements is written `max u v m` for the site universes
`u`, `v`, which is the shape every sheafification instance of the library is stated at and the
only shape at which they are found by instance search; `max u v m` is also no restriction, every
universe containing the site universes being of that form. At the small pro-étale site, whose
objects lie in `Type (u + 1)` and whose morphisms lie in `Type u`, it specialises to
`max (u + 1) r w`, the universe of the module sections of
`AlgebraicGeometry.ProEtale.constantCoefficientRingedSite`.

Nothing here is tagged. Stacks 0946 (1) is already registered, for abelian sheaves, on
`Stacks.WeaklyContractible.exact_sheafSections_of_isWeaklyContractible`; the module-valued
counterpart below is the same mathematics in a different category and adds no content of that
tag.

## References

* [Stacks Project, Tag 0946](https://stacks.math.columbia.edu/tag/0946)
* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe m s v u r w

namespace Stacks.WeaklyContractible

/-- Surjectivity of a morphism of sheaves of sets on the sections over an object of the site
transports along an isomorphism of objects: a section over the second object is carried to the
first, lifted there, and the lift carried back. -/
theorem surjective_app_of_iso.{m', v', u'} {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} {F G : Sheaf J (Type m')} (φ : F ⟶ G) {U U' : C} (e : U ≅ U')
    (h : Function.Surjective (φ.hom.app (op U))) :
    Function.Surjective (φ.hom.app (op U')) := by
  intro s
  obtain ⟨t, ht⟩ := h (G.obj.map e.hom.op s)
  have ht' : φ.hom.app (op U) t = G.obj.map e.hom.op s := ht
  refine ⟨F.obj.map e.inv.op t, ?_⟩
  rw [NatTrans.naturality_apply φ.hom e.inv.op t]
  change G.obj.map e.inv.op (φ.hom.app (op U) t) = s
  rw [ht', ← types_comp_apply (G.obj.map e.hom.op) (G.obj.map e.inv.op), ← G.obj.map_comp,
    ← op_comp, e.inv_hom_id, op_id, G.obj.map_id, types_id_apply]

/-- **Sections over a weakly contractible object preserve epimorphisms.** An epimorphism of
sheaves of `Λ`-modules is locally surjective, local surjectivity is a property of the underlying
morphism of sheaves of sets, and over a weakly contractible object a locally surjective morphism
of sheaves of sets is surjective.

This is the module-valued form of the substance of Stacks 0946 (1); weak contractibility is
passed in the explicit form, tested on sheaves of sets valued in the universe of the module
sections. -/
theorem preservesEpimorphisms_sheafSections_moduleCat.{m', s', v', u'}
    {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C) (Λ : Type s') [Ring Λ]
    [HasSheafify J (ModuleCat.{max u' v' m'} Λ)]
    [J.WEqualsLocallyBijective (ModuleCat.{max u' v' m'} Λ)] (U : C)
    (hU : ∀ (F G : Sheaf J (Type (max u' v' m'))) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U))) :
    ((sheafSections J (ModuleCat.{max u' v' m'} Λ)).obj (op U)).PreservesEpimorphisms := by
  constructor
  intro F G f hf
  let S := sheafCompose J (forget (ModuleCat.{max u' v' m'} Λ))
  have hloc : Sheaf.IsLocallySurjective f :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{max u' v' m'} Λ) f).2 hf
  have hlocS : Sheaf.IsLocallySurjective (S.map f) := by
    let _ : Presheaf.IsLocallySurjective J f.hom := hloc
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight f.hom (forget (ModuleCat.{max u' v' m'} Λ)))
    infer_instance
  have hs : Function.Surjective ((S.map f).hom.app (op U)) :=
    hU (S.obj F) (S.obj G) (S.map f) hlocS
  change Epi (f.hom.app (op U))
  exact (ModuleCat.epi_iff_surjective _).2 hs

/-- **Sections over a weakly contractible object are right exact.** With the left exactness
`Stacks.ConstantSheaf.sheafSections_preservesFiniteLimits`, which holds over any object, this
says that sections over a weakly contractible object are an exact functor from sheaves of
`Λ`-modules to `Λ`-modules. -/
theorem preservesFiniteColimits_sheafSections_moduleCat.{m', s', v', u'}
    {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C) (Λ : Type s') [Ring Λ]
    [HasSheafify J (ModuleCat.{max u' v' m'} Λ)]
    [J.WEqualsLocallyBijective (ModuleCat.{max u' v' m'} Λ)] (U : C)
    (hU : ∀ (F G : Sheaf J (Type (max u' v' m'))) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U))) :
    PreservesFiniteColimits ((sheafSections J (ModuleCat.{max u' v' m'} Λ)).obj (op U)) := by
  let E := (sheafSections J (ModuleCat.{max u' v' m'} Λ)).obj (op U)
  let _ : PreservesFiniteLimits E :=
    Stacks.ConstantSheaf.sheafSections_preservesFiniteLimits J U
  let _ : E.Additive := Functor.additive_of_preserves_binary_products _
  let _ : E.PreservesEpimorphisms :=
    preservesEpimorphisms_sheafSections_moduleCat.{m', s', v', u'} J Λ U hU
  let _ : E.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels E
  exact Functor.preservesFiniteColimits_of_preservesHomology E

end Stacks.WeaklyContractible

namespace AlgebraicGeometry.ProEtale

open ProetaleWContractible

/-- **Weak contractibility of the terminal object of the small pro-étale site.** If `X` is affine
with w-contractible ring of global sections, then a locally surjective morphism of sheaves of
sets on `X.ProEt` is surjective on sections over the terminal object, in any universe of values.

The weak-contractibility input speaks about the identity of `X`, which is terminal by
`AlgebraicGeometry.ProEtale.isTerminalProEtId`; the conclusion is transported to `⊤_ X.ProEt`
along the canonical isomorphism of terminal objects. -/
theorem surjective_sections_terminal_of_isWContractible.{m', u'} (X : Scheme.{u'}) [IsAffine X]
    (hX : IsWContractible.{u', u'} Γ(X, ⊤))
    (F G : Sheaf (Scheme.ProEt.topology X) (Type m')) (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op (⊤_ X.ProEt))) := by
  have : IsAffine (Scheme.ProEt.mk (𝟙 X)).left := inferInstanceAs (IsAffine X)
  exact Stacks.WeaklyContractible.surjective_app_of_iso φ
    ((isTerminalProEtId X).uniqueUpToIso terminalIsTerminal)
    (Scheme.ProEt.surjective_sections_of_isWContractible (Scheme.ProEt.mk (𝟙 X)) hX F G φ hφ)

/-- **Weak contractibility of an affine scheme as an object of the big pro-étale site gives
w-contractibility of its ring of global sections.** Stacks 098H
(`ProetaleWContractible.main_theorem`) is the equivalence of the two conditions for the spectrum
of a ring; this transports the big-site condition from `X` to `Spec Γ(X, ⊤)` along
`AlgebraicGeometry.Scheme.isoSpec` first, so that it applies to any affine `X`. -/
theorem isWContractible_globalSections_of_isWeaklyContractibleObj (X : Scheme.{u}) [IsAffine X]
    (hX : IsWeaklyContractibleObj X) : IsWContractible.{u, u} Γ(X, ⊤) := by
  refine ((main_theorem (Γ(X, ⊤) : Type u)).out 2 1).mp ?_
  intro F G φ hφ
  exact Stacks.WeaklyContractible.surjective_app_of_iso φ X.isoSpec (hX F G φ hφ)

variable (X : Scheme.{u}) (Λ : Type r) [CommRing Λ]
  [HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)]
  [(Scheme.ProEt.topology X).WEqualsLocallyBijective (ModuleCat.{max (u + 1) r w} Λ)]

/-- **Global sections over a weakly contractible affine scheme are right exact.** -/
theorem preservesFiniteColimits_sheafSections_terminal [IsAffine X]
    (hX : IsWContractible.{u, u} Γ(X, ⊤)) :
    PreservesFiniteColimits
      ((sheafSections (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) r w} Λ)).obj (op (⊤_ X.ProEt))) :=
  Stacks.WeaklyContractible.preservesFiniteColimits_sheafSections_moduleCat.{max r w, r, u, u + 1}
    (Scheme.ProEt.topology X) Λ (⊤_ X.ProEt)
    (surjective_sections_terminal_of_isWContractible.{max (u + 1) r w, u} X hX)

variable (I : Ideal Λ)

/-- **The functor `V : M ↦ Γ(X, \underline{M})` of Stacks 09C5.** A `Λ^∧`-module is read as a
`Λ`-module along `Λ → Λ^∧`, made into the constant sheaf of `Λ`-modules on the small pro-étale
site of `X`, and evaluated on the terminal object of that site. -/
def constantGlobalSections :
    ModuleCat.{max (u + 1) r w} (AdicCompletion I Λ) ⥤ ModuleCat.{max (u + 1) r w} Λ :=
  ModuleCat.restrictScalars (algebraMap Λ (AdicCompletion I Λ)) ⋙
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ) ⋙
      (sheafSections (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) r w} Λ)).obj (op (⊤_ X.ProEt))

/-- `V` is additive. -/
instance additive_constantGlobalSections :
    (constantGlobalSections.{u, r, w} X Λ I).Additive := by
  unfold constantGlobalSections
  infer_instance

/-- `V` is left exact: each of its three factors is. -/
instance preservesFiniteLimits_constantGlobalSections :
    PreservesFiniteLimits (constantGlobalSections.{u, r, w} X Λ I) := by
  unfold constantGlobalSections
  exact comp_preservesFiniteLimits _ _

/-- **`V` is right exact, hence exact.** Restriction of scalars is exact, the constant sheaf
functor is a left adjoint, and sections over the terminal object are right exact because `X` is
weakly contractible. This is the exactness of `Γ(X, \underline{-})` that the proof of
Stacks 09C5 uses, and the only use that proof makes of weak contractibility of `X`. -/
theorem preservesFiniteColimits_constantGlobalSections [IsAffine X]
    (hX : IsWContractible.{u, u} Γ(X, ⊤)) :
    PreservesFiniteColimits (constantGlobalSections.{u, r, w} X Λ I) := by
  let _ : PreservesFiniteColimits
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) := by
    refine ⟨fun K _ _ => ?_⟩
    have h1 : PreservesColimitsOfShape K
        (presheafToSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) :=
      ((sheafificationAdjunction (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) r w} Λ)).leftAdjoint_preservesColimits).preservesColimitsOfShape
    have h2 : PreservesColimitsOfShape K
        (Functor.const (X.ProEt)ᵒᵖ (C := ModuleCat.{max (u + 1) r w} Λ)) := inferInstance
    exact @comp_preservesColimitsOfShape _ _ _ _ K _ _ _ _ _ h2 h1
  let _ : PreservesFiniteColimits
      ((sheafSections (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) r w} Λ)).obj (op (⊤_ X.ProEt))) :=
    preservesFiniteColimits_sheafSections_terminal.{u, r, w} X Λ hX
  unfold constantGlobalSections
  exact comp_preservesFiniteColimits _ _

/-- **`V` is exact under the big-site form of weak contractibility.** This is
`AlgebraicGeometry.ProEtale.preservesFiniteColimits_constantGlobalSections` with weak
contractibility of `X` in the form `ProetaleWContractible.IsWeaklyContractibleObj` of
Stacks 090L, which is how the chapter's statements about weakly contractible schemes — the
hypothesis `_hX` of
`AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_reductionSectionsSystem` among them — are
phrased in this library. -/
theorem preservesFiniteColimits_constantGlobalSections_of_isWeaklyContractibleObj [IsAffine X]
    (hX : IsWeaklyContractibleObj X) :
    PreservesFiniteColimits (constantGlobalSections.{u, r, w} X Λ I) :=
  preservesFiniteColimits_constantGlobalSections.{u, r, w} X Λ I
    (isWContractible_globalSections_of_isWeaklyContractibleObj X hX)

end AlgebraicGeometry.ProEtale

end
