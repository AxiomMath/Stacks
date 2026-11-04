module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.AffineModuleCancelBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData

/-!
# The affine comparison of modules and quasi-coherent modules is compatible with composition

For a ring map `φ : R ⟶ S` the natural isomorphism
`Stacks.Descent.extendScalarsCompTildeIso` identifies `(S ⊗[R] M)^~` with the pullback of `M^~`
along `Spec.map φ`.  This file proves that this family of isomorphisms is **compatible with
composition of ring maps**: for `φ : R ⟶ S` and `ψ : S ⟶ U` the two ways of comparing
`(U ⊗[S] (S ⊗[R] M))^~` with the pullback of `M^~` along `Spec.map (φ ≫ ψ)` — pulling back one
step at a time, or cancelling the two base changes first — agree.

This is the pseudonaturality coherence which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/AffineModuleBridge.lean` record as the one
missing, non-module-theoretic ingredient of the fullness half of Stacks 023S: it is what
identifies the comparison isomorphisms of `CategoryTheory.Pseudofunctor.DescentData.ofObj` —
components of `CategoryTheory.Pseudofunctor.mapComp'` for
`AlgebraicGeometry.modulePullbackPseudofunctor`, hence of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` — with the algebraic cancellation
`ModuleCat.cancelExtendScalars`.

## Main definitions

* `Stacks.Descent.specPullbackComp`: the comparison
  `Scheme.Modules.pullback (Spec.map φ) ⋙ Scheme.Modules.pullback (Spec.map ψ) ≅
  Scheme.Modules.pullback (Spec.map (φ ≫ ψ))`, namely
  `AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by the transport along
  `AlgebraicGeometry.Spec.map_comp`.  It is the inverse of a component of
  `CategoryTheory.Pseudofunctor.mapComp'` for
  `AlgebraicGeometry.modulePullbackPseudofunctor`, by
  `Stacks.Descent.galoisMapComp'_inv_app`.
* `Stacks.Descent.specPushforwardComp`: its right-adjoint counterpart, built from
  `AlgebraicGeometry.Scheme.Modules.pushforwardComp`.

## Main results

* `Stacks.Descent.adjunction_comp_assoc`: composition of adjunctions is associative.  Mathlib has
  the composition but not this; it is needed because the two whiskering lemmas for
  `CategoryTheory.conjugateEquiv` produce opposite bracketings.
* `Stacks.Descent.conjugateEquiv_comp_square`: **the abstract coherence.**  Given three
  "comparison" isomorphisms between composites of left adjoints, a cancellation of the two left
  adjoints upstairs and one downstairs, and the corresponding four conjugates, the composition
  square for the comparisons follows from the composition square for the conjugates.  Everything
  in this file is an instance of it.
* `Stacks.Descent.conjugateEquiv_extendScalarsCompTildeIso_hom`,
  `Stacks.Descent.conjugateEquiv_extendScalarsComp_inv`,
  `Stacks.Descent.conjugateEquiv_specPullbackComp_hom`: the three conjugates, respectively
  `Stacks.Descent.pushforwardSpecΓIso`, `ModuleCat.restrictScalarsComp` and
  `Stacks.Descent.specPushforwardComp`.  The first two hold because both isomorphisms are
  *defined* as conjugates; the third is
  `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`.
* `Stacks.Descent.pushforwardSpecΓIso_comp`: **the coherence on the pushforward side**, which is
  where all the content would sit if there were any: taking global sections of a pushforward
  along `Spec` of a ring map is the identity on sections, so the square commutes on the nose.
* `Stacks.Descent.extendScalarsCompTildeIso_comp`: **the coherence.**
* `Stacks.Descent.extendScalarsCompTildeIso_app_comp`: the same statement componentwise, with
  `ModuleCat.cancelExtendScalars` on the algebraic side, which is the form the comparison of
  descent data consumes.  The geometric factor is `Stacks.Descent.specPullbackComp`, which
  `Stacks.Descent.galoisMapComp'_inv_app` identifies with the inverse of the relevant
  component of `CategoryTheory.Pseudofunctor.mapComp'`.
* `Stacks.Descent.extendScalarsCompTildeIso_app_comp_of_eq`: the same, with the composite ring
  map replaced by an arbitrary ring map equal to it.  This is the form applicable at
  `Stacks.Descent.cancelExtendScalarsInr`, whose composite ring map is *named*
  `algebraMap R (B ⊗[R] B)` and is only propositionally equal to the composite.
* `Stacks.Descent.extendScalarsCompTildeIso_app_comp_tensorInl` and
  `Stacks.Descent.extendScalarsCompTildeIso_app_comp_tensorInr`: **the two instances the fullness
  half of Stacks 023S consumes**, at the two projections of
  `Stacks.Descent.specTensorChosenPullback`, with the algebraic factors literally
  `Stacks.Descent.cancelExtendScalarsInl` and `Stacks.Descent.cancelExtendScalarsInr` — the two
  isomorphisms with which `Stacks.Descent.existsUnique_baseChange_eq_of_tensorInl_eq_tensorInr`
  states the descent condition.
* `Stacks.Descent.algHom_comp_tensorInr`: the `CommRingCat`-level companion of
  `Stacks.Descent.algHom_comp_tensorInl`, which the second instance needs.

## Implementation notes

`Stacks.Descent.extendScalarsCompTildeIso` is by construction
`CategoryTheory.conjugateIsoEquiv` of `Stacks.Descent.pushforwardSpecΓIso`, and no lemma computes
that conjugate.  The point of this file is that **none is needed**: all five isomorphisms
entering the square are conjugates of known natural isomorphisms, and
`CategoryTheory.conjugateEquiv` is an *equivalence* which turns composition into composition
(`CategoryTheory.conjugateEquiv_comp`) and whiskering into whiskering
(`CategoryTheory.conjugateEquiv_whiskerLeft`, `CategoryTheory.conjugateEquiv_whiskerRight`).  So
the square may be checked after conjugating, where it becomes a square of pushforwards and
restrictions of scalars, all of which are the identity on global sections.

Two obstacles had to be removed.

The first is bracketing.  `CategoryTheory.conjugateEquiv_whiskerLeft` produces
`adj.comp (adj₁.comp adj₂)` while `CategoryTheory.conjugateEquiv_whiskerRight` produces
`(adj₁.comp adj₂).comp adj`, and the composite adjunctions are *not* definitionally equal — only
their underlying functors are.  `Stacks.Descent.adjunction_comp_assoc` fixes that, and is
consumed through `Stacks.Descent.conjugateEquiv_whiskerLeft_of_eq` and
`Stacks.Descent.conjugateEquiv_whiskerRight_of_eq`, which take the composite adjunction as a
variable together with an equation, so that the transport happens by `subst` rather than by
rewriting underneath `CategoryTheory.conjugateEquiv`.

The second is that the bracketing transport must happen with the adjunctions **abstract**.
Instantiated at `AlgebraicGeometry.tilde.adjunction`, the definitional unfolding of
`CategoryTheory.Adjunction.comp` costs a kernel deterministic timeout, exactly as recorded for
the `CategoryTheory.Pseudofunctor.DescentData`-to-`CategoryTheory.Cat` crossing in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/StandardAffineFamily.lean`.  So
`Stacks.Descent.conjugateEquiv_comp_square` is stated over nine abstract adjunctions and is
instantiated exactly once; its hypotheses mention only *two-fold* composites, which are
unambiguous, so the instantiation itself needs no defeq gymnastics.

`AlgebraicGeometry.Spec.map_comp` is not a definitional equality, so a transport along it appears
in `Stacks.Descent.specPullbackComp`.  On the pushforward side it is
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`, whose component is
`M.presheaf.map (eqToHom _).op`; at the global sections this is the identity, which is
`Stacks.Descent.moduleSpecΓFunctor_map_pushforwardCongr_inv_app`.

Two things deliberately *not* done, each because it costs a kernel deterministic timeout rather
than because it is false.

First, the geometric factor is left as `Stacks.Descent.specPullbackComp` and not re-spelled as
`CategoryTheory.Pseudofunctor.mapComp'` of `AlgebraicGeometry.modulePullbackPseudofunctor`.  The
restatement is one application of `Stacks.Descent.galoisMapComp'_inv_app`, and its
*type* elaborates and kernel-checks fine, but every proof of it tried — by `rw ... at`, and as a
term through `congrArg` — dies in the kernel: `modulePullbackPseudofunctor` is
`AlgebraicGeometry.Scheme.Modules.pseudofunctor.comp CategoryTheory.Bicategory.Adj.forget₁`, and
once a statement mixes an object written at `(Spec R).Modules` with one written at
`↑(modulePullbackPseudofunctor.obj _)` the kernel has to unfold that composite.  Consumers of
this file are already in the `CategoryTheory.Pseudofunctor.mapComp'` world, with their objects
typed there, so the rewrite is cheap where it belongs and expensive here.

Second, `Stacks.Descent.extendScalarsCompTildeIso_app_comp_of_eq` carries the transport along
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` as an explicit extra factor rather than folding
it into `Stacks.Descent.specPullbackComp`.  Folding it in makes the statement a `subst` away from
`Stacks.Descent.extendScalarsCompTildeIso_app_comp`, but discharging it that way forces a defeq
comparison of two `AlgebraicGeometry.Scheme.Modules.pullbackCongr` terms, and that is an
`eqToIso` of an equality of *functors* — an `Eq.rec` in a data position, which the kernel cannot
whnf.  This is the hazard recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/AffineModuleCancelBaseChange.lean`,
confirmed here.  With the factor kept separate the transport reduces: at `hχ = rfl` the proof
`congrArg Spec.map rfl` *is* `rfl`, so the factor is the identity by `rfl` and the `subst` proof
goes through.

No stacks attribute is placed in this file: nothing here proves a clause of a Stacks tag, and
`Stacks.Descent.StandardAffineFullness` is not discharged.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TensorProduct

universe u

namespace Stacks.Descent

section Abstract

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- **Composition of adjunctions is associative.**  Mathlib has
`CategoryTheory.Adjunction.comp` but no associativity for it, and the two whiskering lemmas for
`CategoryTheory.conjugateEquiv` produce opposite bracketings, so the two sides really have to be
identified.  They are *not* definitionally equal; both are determined by their unit, which is
`CategoryTheory.Adjunction.ext`. -/
theorem adjunction_comp_assoc {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) :
    (adj₁.comp adj₂).comp adj₃ = adj₁.comp (adj₂.comp adj₃) := by
  apply CategoryTheory.Adjunction.ext
  ext X
  simp [Adjunction.comp_unit_app]

/-- `CategoryTheory.conjugateEquiv_whiskerLeft` with the two composite adjunctions taken as
variables, so that a differently bracketed composite can be substituted into it.  This is the
device that makes the bracketing transport happen by `subst`; rewriting underneath
`CategoryTheory.conjugateEquiv` is not type-correct at `implicit` transparency. -/
theorem conjugateEquiv_whiskerLeft_of_eq {L₁ L₂ : B ⥤ C} {R₁ R₂ : C ⥤ B} {L : A ⥤ B} {R : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R)
    (c₁ : L ⋙ L₁ ⊣ R₁ ⋙ R) (c₂ : L ⋙ L₂ ⊣ R₂ ⋙ R)
    (h₁ : c₁ = adj.comp adj₁) (h₂ : c₂ = adj.comp adj₂) (τ : L₂ ⟶ L₁) :
    conjugateEquiv c₁ c₂ (Functor.whiskerLeft L τ) =
      Functor.whiskerRight (conjugateEquiv adj₁ adj₂ τ) R := by
  subst h₁; subst h₂; exact conjugateEquiv_whiskerLeft _ _ _ _

/-- `CategoryTheory.conjugateEquiv_whiskerRight` with the two composite adjunctions taken as
variables; see `Stacks.Descent.conjugateEquiv_whiskerLeft_of_eq`. -/
theorem conjugateEquiv_whiskerRight_of_eq {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {L : B ⥤ C} {R : C ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R)
    (c₁ : L₁ ⋙ L ⊣ R ⋙ R₁) (c₂ : L₂ ⋙ L ⊣ R ⋙ R₂)
    (h₁ : c₁ = adj₁.comp adj) (h₂ : c₂ = adj₂.comp adj) (τ : L₂ ⟶ L₁) :
    conjugateEquiv c₁ c₂ (Functor.whiskerRight τ L) =
      Functor.whiskerLeft R (conjugateEquiv adj₁ adj₂ τ) := by
  subst h₁; subst h₂; exact conjugateEquiv_whiskerRight _ _ _ _

end Abstract

section AbstractSquare

variable {MR MS MU QR QS QU : Type*} [Category MR] [Category MS] [Category MU]
  [Category QR] [Category QS] [Category QU]
  {Eφ : MR ⥤ MS} {Rφ : MS ⥤ MR} {Eψ : MS ⥤ MU} {Rψ : MU ⥤ MS} {Eχ : MR ⥤ MU} {Rχ : MU ⥤ MR}
  {TR : MR ⥤ QR} {GR : QR ⥤ MR} {TS : MS ⥤ QS} {GS : QS ⥤ MS} {TU : MU ⥤ QU} {GU : QU ⥤ MU}
  {Pφ : QR ⥤ QS} {Fφ : QS ⥤ QR} {Pψ : QS ⥤ QU} {Fψ : QU ⥤ QS} {Pc : QR ⥤ QU} {Fc : QU ⥤ QR}

/-- **The abstract coherence: a square of comparison isomorphisms between left adjoints commutes
as soon as the conjugate square does.**

Think of `Eφ`, `Eψ`, `Eχ` as extension of scalars along `φ`, `ψ` and their composite, of `TR`,
`TS`, `TU` as the three functors `M ↦ M^~`, and of `Pφ`, `Pψ`, `Pc` as the three pullback
functors; `iφ`, `iψ`, `iχ` are the comparisons between them, `ec` cancels the two extensions of
scalars and `pc` the two pullbacks.  The conclusion is that comparing one step at a time agrees
with cancelling first and comparing once.

Each of the five isomorphisms is between left adjoints, so each has a conjugate; the hypotheses
name those conjugates, and `hfin` is the resulting square between right adjoints.  Since
`CategoryTheory.conjugateEquiv` is injective, and turns composition into composition and
whiskering into whiskering, that is all that is needed.

The hypotheses mention only two-fold composite adjunctions, which are unambiguously bracketed;
all the rebracketing happens inside the proof, with the adjunctions abstract.  See the
implementation notes for why that matters. -/
theorem conjugateEquiv_comp_square
    (adjEφ : Eφ ⊣ Rφ) (adjEψ : Eψ ⊣ Rψ) (adjEχ : Eχ ⊣ Rχ)
    (adjTR : TR ⊣ GR) (adjTS : TS ⊣ GS) (adjTU : TU ⊣ GU)
    (adjPφ : Pφ ⊣ Fφ) (adjPψ : Pψ ⊣ Fψ) (adjPc : Pc ⊣ Fc)
    {iφ : Eφ ⋙ TS ≅ TR ⋙ Pφ} {jφ : Fφ ⋙ GR ≅ GS ⋙ Rφ}
    (hφ : conjugateEquiv (adjTR.comp adjPφ) (adjEφ.comp adjTS) iφ.hom = jφ.hom)
    {iψ : Eψ ⋙ TU ≅ TS ⋙ Pψ} {jψ : Fψ ⋙ GS ≅ GU ⋙ Rψ}
    (hψ : conjugateEquiv (adjTS.comp adjPψ) (adjEψ.comp adjTU) iψ.hom = jψ.hom)
    {iχ : Eχ ⋙ TU ≅ TR ⋙ Pc} {jχ : Fc ⋙ GR ≅ GU ⋙ Rχ}
    (hχ : conjugateEquiv (adjTR.comp adjPc) (adjEχ.comp adjTU) iχ.hom = jχ.hom)
    {ec : Eχ ≅ Eφ ⋙ Eψ} {rc : Rχ ≅ Rψ ⋙ Rφ}
    (hec : conjugateEquiv adjEχ (adjEφ.comp adjEψ) ec.inv = rc.hom)
    {pc : Pφ ⋙ Pψ ≅ Pc} {qc : Fψ ⋙ Fφ ≅ Fc}
    (hpc : conjugateEquiv adjPc (adjPφ.comp adjPψ) pc.hom = qc.inv)
    (hfin : Functor.whiskerRight qc.inv GR ≫ Functor.whiskerLeft Fψ jφ.hom ≫
        Functor.whiskerRight jψ.hom Rφ = jχ.hom ≫ Functor.whiskerLeft GU rc.hom) :
    Functor.whiskerLeft Eφ iψ.hom ≫ Functor.whiskerRight iφ.hom Pψ ≫
        Functor.whiskerLeft TR pc.hom =
      Functor.whiskerRight ec.inv TU ≫ iχ.hom := by
  refine (conjugateEquiv (adjTR.comp adjPc) (adjEφ.comp (adjEψ.comp adjTU))).injective ?_
  rw [← conjugateEquiv_comp _ ((adjEφ.comp adjTS).comp adjPψ) _,
    ← conjugateEquiv_comp _ ((adjTR.comp adjPφ).comp adjPψ) _,
    ← conjugateEquiv_comp _ (adjEχ.comp adjTU) _,
    conjugateEquiv_whiskerLeft_of_eq (adjTS.comp adjPψ) (adjEψ.comp adjTU) adjEφ
      ((adjEφ.comp adjTS).comp adjPψ) (adjEφ.comp (adjEψ.comp adjTU))
      (adjunction_comp_assoc adjEφ adjTS adjPψ) rfl,
    conjugateEquiv_whiskerRight_of_eq (adjTR.comp adjPφ) (adjEφ.comp adjTS) adjPψ _ _ rfl rfl,
    conjugateEquiv_whiskerLeft_of_eq adjPc (adjPφ.comp adjPψ) adjTR (adjTR.comp adjPc)
      ((adjTR.comp adjPφ).comp adjPψ) rfl (adjunction_comp_assoc adjTR adjPφ adjPψ),
    conjugateEquiv_whiskerRight_of_eq adjEχ (adjEφ.comp adjEψ) adjTU _ _ rfl
      (adjunction_comp_assoc adjEφ adjEψ adjTU).symm, hφ, hψ, hχ, hec, hpc]
  exact (Category.assoc _ _ _).trans hfin

end AbstractSquare

section Conjugates

variable {X Y Z : Scheme.{u}}

/-- The conjugate of the transport of pullbacks along an equality of morphisms is the transport
of pushforwards. -/
theorem conjugateEquiv_pullbackCongr_hom {f g : X ⟶ Y} (hfg : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g)
        (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackCongr hfg).hom =
      (Scheme.Modules.pushforwardCongr hfg).inv := by
  subst hfg
  refine Eq.trans (congrArg (fun t => CategoryTheory.conjugateEquiv
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f) t)
    (show (Scheme.Modules.pullbackCongr (rfl : f = f)).hom = 𝟙 _ from rfl)) ?_
  rw [CategoryTheory.conjugateEquiv_id]
  symm
  ext M : 2
  ext1
  simp

end Conjugates

section Comparison

variable {R S U : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ U)

/-- **The composition comparison for pullbacks along spectra of ring maps.**  Composing the
pullbacks along `Spec.map φ` and `Spec.map ψ` is the pullback along `Spec.map (φ ≫ ψ)`: this is
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, transported along
`AlgebraicGeometry.Spec.map_comp`, which is not a definitional equality. -/
def specPullbackComp :
    Scheme.Modules.pullback (Spec.map φ) ⋙ Scheme.Modules.pullback (Spec.map ψ) ≅
      Scheme.Modules.pullback (Spec.map (φ ≫ ψ)) :=
  Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ) ≪≫
    Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm

/-- **The composition comparison for pushforwards along spectra of ring maps**, the
right-adjoint counterpart of `Stacks.Descent.specPullbackComp`. -/
def specPushforwardComp :
    Scheme.Modules.pushforward (Spec.map ψ) ⋙ Scheme.Modules.pushforward (Spec.map φ) ≅
      Scheme.Modules.pushforward (Spec.map (φ ≫ ψ)) :=
  Scheme.Modules.pushforwardComp (Spec.map ψ) (Spec.map φ) ≪≫
    Scheme.Modules.pushforwardCongr (Spec.map_comp φ ψ).symm

/-- The two composition comparisons are conjugate. -/
theorem conjugateEquiv_specPullbackComp_hom :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (φ ≫ ψ)))
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ)))
        (specPullbackComp φ ψ).hom =
      (specPushforwardComp φ ψ).inv := by
  rw [specPullbackComp, Iso.trans_hom,
    ← conjugateEquiv_comp _
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ ≫ Spec.map φ)) _,
    conjugateEquiv_pullbackCongr_hom, Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom,
      specPushforwardComp,
    Iso.trans_inv]

/-- **The conjugate of the affine comparison is the comparison of global sections of a
pushforward.**  This holds because `Stacks.Descent.extendScalarsCompTildeIso` is *defined* as the
conjugate of `Stacks.Descent.pushforwardSpecΓIso`. -/
theorem conjugateEquiv_extendScalarsCompTildeIso_hom :
    conjugateEquiv (tilde.adjunction.comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction)
        (extendScalarsCompTildeIso φ).hom =
      (pushforwardSpecΓIso φ).hom := by
  rw [extendScalarsCompTildeIso]
  exact congrArg Iso.hom ((CategoryTheory.conjugateIsoEquiv _ _).apply_symm_apply _)

/-- **The conjugate of the cancellation of two extensions of scalars is the cancellation of two
restrictions of scalars.**  As for
`Stacks.Descent.conjugateEquiv_extendScalarsCompTildeIso_hom`, this holds because
`ModuleCat.extendScalarsComp` is defined as a conjugate. -/
theorem conjugateEquiv_extendScalarsComp_inv :
    conjugateEquiv (ModuleCat.extendRestrictScalarsAdj (φ ≫ ψ).hom)
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
          (ModuleCat.extendRestrictScalarsAdj ψ.hom))
        (ModuleCat.extendScalarsComp φ.hom ψ.hom).inv =
      (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom := by
  rw [ModuleCat.extendScalarsComp]
  exact congrArg Iso.inv ((CategoryTheory.conjugateIsoEquiv _ _).apply_symm_apply _)

end Comparison

section Sections

/-- **Transporting a pushforward along an equality of morphisms does nothing to global
sections.**  The component of `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` is
`M.presheaf.map (eqToHom _).op`, and over the whole space the two preimages are the same open,
so the transition map is the identity. -/
theorem moduleSpecΓFunctor_map_pushforwardCongr_inv_app {R : CommRingCat.{u}} {Y : Scheme.{u}}
    {f g : Y ⟶ Spec R} (hfg : f = g) (M : Y.Modules)
    (x : (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward g).obj M) : Type u)) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforwardCongr hfg).inv.app M) x = x := by
  subst hfg
  change (M.presheaf.map _) x = x
  rw [TopologicalSpace.Opens.mapIso_refl]
  simp
  rfl

variable {R S U : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ U)

/-- **The coherence on the pushforward side.**  Taking global sections of a pushforward along
`Spec` of a ring map and restricting scalars is compatible with composition of ring maps.  Both
sides are the identity on sections, which is the whole reason the coherence of
`Stacks.Descent.extendScalarsCompTildeIso` costs nothing: see
`Stacks.Descent.extendScalarsCompTildeIso_comp`. -/
theorem pushforwardSpecΓIso_comp :
    Functor.whiskerRight (specPushforwardComp φ ψ).inv moduleSpecΓFunctor ≫
        Functor.whiskerLeft (Scheme.Modules.pushforward (Spec.map ψ))
          (pushforwardSpecΓIso φ).hom ≫
        Functor.whiskerRight (pushforwardSpecΓIso ψ).hom (ModuleCat.restrictScalars φ.hom) =
      (pushforwardSpecΓIso (φ ≫ ψ)).hom ≫
        Functor.whiskerLeft moduleSpecΓFunctor
          (ModuleCat.restrictScalarsComp φ.hom ψ.hom).hom := by
  ext M : 2
  ext x
  change (pushforwardSpecΓIso ψ).hom.app M
      ((pushforwardSpecΓIso φ).hom.app _
        (moduleSpecΓFunctor.map
            ((Scheme.Modules.pushforwardComp (Spec.map ψ) (Spec.map φ)).inv.app M)
          (moduleSpecΓFunctor.map
            ((Scheme.Modules.pushforwardCongr (Spec.map_comp φ ψ).symm).inv.app M) x))) = _
  rw [moduleSpecΓFunctor_map_pushforwardCongr_inv_app]
  rfl

end Sections

section Coherence

variable {R S U : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ U)

/-- **The affine comparison is compatible with composition of ring maps.**

For `φ : R ⟶ S` and `ψ : S ⟶ U` the two ways of identifying `(U ⊗[S] (S ⊗[R] M))^~` with the
pullback of `M^~` along `Spec.map (φ ≫ ψ)` agree: comparing one base change at a time, with
`Stacks.Descent.extendScalarsCompTildeIso` at `ψ` and then at `φ`, and finally composing the two
pullbacks by `Stacks.Descent.specPullbackComp`, gives the same thing as first cancelling the two
extensions of scalars by `ModuleCat.extendScalarsComp` and then comparing once.

This is the pseudonaturality coherence for the family
`Stacks.Descent.extendScalarsCompTildeIso`.  It is proved by conjugating: all five isomorphisms
involved are conjugates of isomorphisms of the corresponding right adjoints — pushforwards,
global sections and restrictions of scalars — and there the square holds on sections, which is
`Stacks.Descent.pushforwardSpecΓIso_comp`. -/
theorem extendScalarsCompTildeIso_comp :
    Functor.whiskerLeft (ModuleCat.extendScalars φ.hom) (extendScalarsCompTildeIso ψ).hom ≫
        Functor.whiskerRight (extendScalarsCompTildeIso φ).hom
          (Scheme.Modules.pullback (Spec.map ψ)) ≫
        Functor.whiskerLeft (tilde.functor R) (specPullbackComp φ ψ).hom =
      Functor.whiskerRight (ModuleCat.extendScalarsComp φ.hom ψ.hom).inv (tilde.functor U) ≫
        (extendScalarsCompTildeIso (φ ≫ ψ)).hom :=
  conjugateEquiv_comp_square (ModuleCat.extendRestrictScalarsAdj φ.hom)
    (ModuleCat.extendRestrictScalarsAdj ψ.hom) (ModuleCat.extendRestrictScalarsAdj (φ ≫ ψ).hom)
    tilde.adjunction tilde.adjunction tilde.adjunction
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (φ ≫ ψ)))
    (conjugateEquiv_extendScalarsCompTildeIso_hom φ)
    (conjugateEquiv_extendScalarsCompTildeIso_hom ψ)
    (conjugateEquiv_extendScalarsCompTildeIso_hom (φ ≫ ψ))
    (conjugateEquiv_extendScalarsComp_inv φ ψ) (conjugateEquiv_specPullbackComp_hom φ ψ)
    (pushforwardSpecΓIso_comp φ ψ)

/-- Cancelling two extensions of scalars along the components of a composite of ring maps is
`ModuleCat.extendScalarsComp` read backwards: the transport along the equality of ring maps is
trivial when that equality is the definitional one. -/
theorem cancelExtendScalars_hom_eq (M : ModuleCat.{u} R) :
    (ModuleCat.cancelExtendScalars φ.hom ψ.hom (g := (φ ≫ ψ).hom) rfl M).hom =
      (ModuleCat.extendScalarsComp φ.hom ψ.hom).inv.app M := by
  have hid : (ModuleCat.extendScalarsCongr (f := ψ.hom.comp φ.hom) (g := (φ ≫ ψ).hom) rfl M).hom =
      𝟙 _ :=
    ModuleCat.ExtendScalars.hom_ext' fun x => by
      rw [ModuleCat.extendScalarsCongr_hom_oneTmul, ModuleCat.id_apply]
      rfl
  rw [ModuleCat.cancelExtendScalars, Iso.trans_hom, Iso.symm_hom, hid, Category.comp_id]
  rfl

/-- **The coherence, componentwise, in the vocabulary the comparison of descent data consumes.**

Transporting the comparison at `φ` along the pullback by `Spec.map ψ`, and then cancelling the
two pullbacks by `Stacks.Descent.specPullbackComp`, is the same as cancelling the two base
changes by `ModuleCat.cancelExtendScalars` and comparing once.

`Stacks.Descent.specPullbackComp` is the comparison isomorphism whose inverse is the relevant
component of `CategoryTheory.Pseudofunctor.mapComp'` for
`AlgebraicGeometry.modulePullbackPseudofunctor` — hence a transition morphism of
`CategoryTheory.Pseudofunctor.DescentData.ofObj` — by
`Stacks.Descent.galoisMapComp'_inv_app` of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/Galois.lean`, whose statement is exactly
`(Scheme.Modules.pullbackComp q p).hom ≫ (Scheme.Modules.pullbackCongr h).hom` applied at the
object.  That lemma is deliberately *not* used here, so that this file does not drag the Zariski
stack development into its import closure; the composition is one rewrite at the point of use.

This is `Stacks.Descent.extendScalarsCompTildeIso_comp` evaluated at `M`, with the algebraic
factor re-spelled by `Stacks.Descent.cancelExtendScalars_hom_eq`. -/
theorem extendScalarsCompTildeIso_app_comp (M : ModuleCat.{u} R) :
    (extendScalarsCompTildeIso ψ).hom.app ((ModuleCat.extendScalars φ.hom).obj M) ≫
        (Scheme.Modules.pullback (Spec.map ψ)).map
          ((extendScalarsCompTildeIso φ).hom.app M) ≫
        (specPullbackComp φ ψ).hom.app ((tilde.functor R).obj M) =
      (tilde.functor U).map
          (ModuleCat.cancelExtendScalars φ.hom ψ.hom (g := (φ ≫ ψ).hom) rfl M).hom ≫
        (extendScalarsCompTildeIso (φ ≫ ψ)).hom.app M := by
  have h := congrFun (congrArg NatTrans.app (extendScalarsCompTildeIso_comp φ ψ)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  rw [cancelExtendScalars_hom_eq]
  exact h

/-- **The coherence at an arbitrary naming of the composite ring map.**

`Stacks.Descent.extendScalarsCompTildeIso_app_comp` is stated at the composite `φ ≫ ψ`, but the
two cancellations the fullness half of Stacks 023S needs are
`Stacks.Descent.cancelExtendScalarsInl` and `Stacks.Descent.cancelExtendScalarsInr`, whose
composite ring map is *named* `algebraMap R (B ⊗[R] B)`: for the first inclusion that is
definitionally the composite, but for the second it is only
`Stacks.Descent.tensorInr_hom_comp_algHom_hom`, an honest proof.  So the statement is given here
with the composite as a variable `χ` and two equations, which is the form that can be applied at
either inclusion.

The hypothesis `hh` is redundant given `hχ` — it is `hχ` at the level of ring maps — but keeping
it separate is what lets the conclusion be spelled with the very
`ModuleCat.cancelExtendScalars` the caller already has; the two possible proofs of it are
definitionally equal by proof irrelevance, `ModuleCat.extendScalarsCongr` using its argument only
in a `map_smul'` field. -/
theorem extendScalarsCompTildeIso_app_comp_of_eq {χ : R ⟶ U} (hχ : φ ≫ ψ = χ)
    (hh : ψ.hom.comp φ.hom = χ.hom) (M : ModuleCat.{u} R) :
    (extendScalarsCompTildeIso ψ).hom.app ((ModuleCat.extendScalars φ.hom).obj M) ≫
        (Scheme.Modules.pullback (Spec.map ψ)).map
          ((extendScalarsCompTildeIso φ).hom.app M) ≫
        (specPullbackComp φ ψ).hom.app ((tilde.functor R).obj M) ≫
        (Scheme.Modules.pullbackCongr (congrArg Spec.map hχ)).hom.app
          ((tilde.functor R).obj M) =
      (tilde.functor U).map (ModuleCat.cancelExtendScalars φ.hom ψ.hom hh M).hom ≫
        (extendScalarsCompTildeIso χ).hom.app M := by
  subst hχ
  refine Eq.trans ?_ (extendScalarsCompTildeIso_app_comp φ ψ M)
  rw [show (Scheme.Modules.pullbackCongr (congrArg Spec.map (rfl : φ ≫ ψ = φ ≫ ψ))).hom.app
      ((tilde.functor R).obj M) = 𝟙 _ from rfl, Category.comp_id]

end Coherence

section Inclusions

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The inclusion `b ↦ 1 ⊗ b` composed with `algebraMap R B` is `algebraMap R (B ⊗[R] B)`, as a
morphism of `CommRingCat`.  The counterpart `Stacks.Descent.algHom_comp_tensorInl` for the first
inclusion holds by `rfl`; this one does not. -/
theorem algHom_comp_tensorInr :
    algHom R B ≫ tensorInr R B = CommRingCat.ofHom (algebraMap R (B ⊗[R] B)) :=
  CommRingCat.hom_ext (tensorInr_hom_comp_algHom_hom R B)

/-- **The coherence at the first projection of `Spec (B ⊗[R] B)`.**  This is
`Stacks.Descent.extendScalarsCompTildeIso_app_comp_of_eq` at `φ = algHom R B` and
`ψ = tensorInl R B`, so that the algebraic factor is literally
`Stacks.Descent.cancelExtendScalarsInl`: the comparison between the geometric transition
morphism of `CategoryTheory.Pseudofunctor.DescentData.ofObj` over the chosen pullback
`Stacks.Descent.specTensorChosenPullback` and the algebraic cancellation with which
`Stacks.Descent.existsUnique_baseChange_eq_of_tensorInl_eq_tensorInr` states the descent
condition. -/
theorem extendScalarsCompTildeIso_app_comp_tensorInl (M : ModuleCat.{u} (CommRingCat.of R)) :
    (extendScalarsCompTildeIso (tensorInl R B)).hom.app
          ((ModuleCat.extendScalars (algHom R B).hom).obj M) ≫
        (Scheme.Modules.pullback (Spec.map (tensorInl R B))).map
          ((extendScalarsCompTildeIso (algHom R B)).hom.app M) ≫
        (specPullbackComp (algHom R B) (tensorInl R B)).hom.app ((tilde.functor _).obj M) ≫
        (Scheme.Modules.pullbackCongr
            (congrArg Spec.map (algHom_comp_tensorInl R B))).hom.app ((tilde.functor _).obj M) =
      (tilde.functor (CommRingCat.of (B ⊗[R] B))).map (cancelExtendScalarsInl R B M).hom ≫
        (extendScalarsCompTildeIso (CommRingCat.ofHom (algebraMap R (B ⊗[R] B)))).hom.app M :=
  extendScalarsCompTildeIso_app_comp_of_eq (algHom R B) (tensorInl R B)
    (algHom_comp_tensorInl R B) (tensorInl_hom_comp_algHom_hom R B) M

/-- **The coherence at the second projection of `Spec (B ⊗[R] B)`**, the companion of
`Stacks.Descent.extendScalarsCompTildeIso_app_comp_tensorInl` with
`Stacks.Descent.cancelExtendScalarsInr`. -/
theorem extendScalarsCompTildeIso_app_comp_tensorInr (M : ModuleCat.{u} (CommRingCat.of R)) :
    (extendScalarsCompTildeIso (tensorInr R B)).hom.app
          ((ModuleCat.extendScalars (algHom R B).hom).obj M) ≫
        (Scheme.Modules.pullback (Spec.map (tensorInr R B))).map
          ((extendScalarsCompTildeIso (algHom R B)).hom.app M) ≫
        (specPullbackComp (algHom R B) (tensorInr R B)).hom.app ((tilde.functor _).obj M) ≫
        (Scheme.Modules.pullbackCongr
            (congrArg Spec.map (algHom_comp_tensorInr R B))).hom.app ((tilde.functor _).obj M) =
      (tilde.functor (CommRingCat.of (B ⊗[R] B))).map (cancelExtendScalarsInr R B M).hom ≫
        (extendScalarsCompTildeIso (CommRingCat.ofHom (algebraMap R (B ⊗[R] B)))).hom.app M :=
  extendScalarsCompTildeIso_app_comp_of_eq (algHom R B) (tensorInr R B)
    (algHom_comp_tensorInr R B) (tensorInr_hom_comp_algHom_hom R B) M

end Inclusions

end Stacks.Descent

end

end
