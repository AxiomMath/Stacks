module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorObstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafQuasicoherence
public import StacksFrontier.Deformation.ToposThickening.IdealProductSequence

/-!
# Lifts of an object of `Coh_{X/Y}` across a first order thickening, as flat lifts

Let `D = (f : X ⟶ Y)` be the standing data of Stacks 08KB, let `ξ = (T, 𝒢)` be an object of
`Coh_{X/Y}` and let `h : T ⟶ T'` be a first order thickening of schemes over `Y`. A lift of `ξ`
to `T'` is an object `(T', 𝒢')` of `Coh_{X/Y}` together with a morphism `ξ ⟶ (T', 𝒢')` of
`Coh_{X/Y}` over `h`, that is, a quasi-coherent `𝒪_{X_{T'}}`-module `𝒢'` of finite
presentation, flat over `T'` and with support proper over `T'`, together with an isomorphism
`(X_h)^*𝒢' ≅ 𝒢`. These are the lifts in terms of which the source computes the tangent spaces
and infinitesimal automorphisms of `Coh_{X/Y}` (the proofs of Stacks 08W8 and Stacks 08WA), by
reading them as the flat lifts of Stacks 08VW across the first order thickening of ringed topoi
`X_T ⊂ X_{T'}`.

This file sets up the square of ringed topoi and sends a lift of `ξ` to a flat lift of `𝒢` in
the sense of `Deformation.ToposThickening.FlatLift`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.relativeSquareSituation`: the situation of the
  functor of quotients with the morphism of `D` and the zero module. The relative square of
  `StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorRelativeSquare.lean`, its strictness and its
  flatness comparisons depend on the morphism only, and this is how they are read for `D`.
* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift`: a lift of `ξ` across `h`.
* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.toObject` and
  `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.toHom`: the object of `Coh_{X/Y}` over
  `T'` and the morphism of `Coh_{X/Y}` over `h` it consists of.
* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.toFlatLift`: the flat lift of
  `𝒢` across `X_T ⊂ X_{T'}` attached to a lift: the module `𝒢'` with the map
  `𝒢' ⟶ i_*i^*𝒢' ≅ i_*𝒢`.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08W8](https://stacks.math.columbia.edu/tag/08W8)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **The situation of the functor of quotients carrying the morphism of `D`.** Its module is
zero; nothing below uses it. The relative square of
`AlgebraicGeometry.Space.QuotientSituation.relativeSquare_comm`, its first order thickenings, its
strictness (`AlgebraicGeometry.Space.QuotientSituation.isStrict_relativeSquare`) and the
comparisons of flatness over the test schemes depend on the morphism `f : X ⟶ Y` only, and its
base changes, projections and morphisms of base changes are those of `D` by definition. -/
abbrev relativeSquareSituation : QuotientSituation B S hS where
  X := D.X
  Y := D.Y
  f := D.f
  F := 0
  quasicoherent := isQuasicoherentOnSite_of_isZero B S hS _ _ (isZero_zero _)

/-- **A lift of an object of `Coh_{X/Y}` across a morphism of test schemes.** For an object
`ξ = (T, 𝒢)` of `Coh_{X/Y}` and a morphism `h : T ⟶ T'` of schemes over `Y`: an object
`(T', 𝒢')` of `Coh_{X/Y}` over `T'` — a quasi-coherent `𝒪_{X_{T'}}`-module of finite
presentation, flat over `T'`, with support proper over `T'` — together with an isomorphism
`(X_h)^*𝒢' ≅ 𝒢`, that is, a morphism `ξ ⟶ (T', 𝒢')` of `Coh_{X/Y}` over `h`. -/
structure ThickeningLift (ξ : CoherentObject D) {T' : SchemesOver D.Y} (h : ξ.T ⟶ T') where
  /-- The lifted module on `X_{T'}`. -/
  F : Modules.{u, u} B S hS (D.space T').1 (D.space T').2
  /-- It is quasi-coherent (Stacks 03G9). -/
  quasicoherent : F.IsQuasicoherentOnSite
  /-- It is of finite presentation (Stacks 03DL). -/
  finitePresentation : F.IsFinitePresentationOnSite
  /-- It is flat over `T'` (Stacks 05VV). -/
  flat : IsFlatOver B S hS (D.space T').2 (D.projection T').hom F
  /-- Its support is a closed subset proper over `T'` (Stacks 0CZD). -/
  properSupport : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T').hom)
      (hU : IsClosed (D.support T' F)),
      IsProperOver B S hS (D.space T').2
        ((schemeSpaceFunctor B S hS).obj T'.left).2 (D.projection T').hom hp (D.support T' F) hU
  /-- The comparison of its inverse image along `X_h` with the module of `ξ`. -/
  fibre : (modulePullback B S hS (D.relativeMap h)).obj F ⟶ ξ.F
  /-- The comparison is an isomorphism. -/
  isIso_fibre : IsIso fibre

/-- The module `𝒢` of `ξ`, read as a module on the small étale ringed topos of `X_T`, the source
of the thickening `X_T ⊂ X_{T'}`. -/
abbrev objectToposModule {D : CoherentSituation B S hS} (ξ : CoherentObject D) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O) :=
  ξ.F

/-- **The inverse image of `𝒪`-modules along `X_g` is the pullback of modules along the morphism
of small étale ringed topoi of `X_g`** (Stacks 03G8, 03D6), as an equality of functors. It holds by
definition, but checking it costs the elaborator enough that it is recorded once here and used
through `AlgebraicGeometry.Space.CoherentSituation.relativeMapPullbackIso`. -/
theorem modulePullback_relativeMap_eq_toposPullback {T₁ T₂ : SchemesOver D.Y} (g : T₁ ⟶ T₂) :
    modulePullback B S hS (D.relativeMap g) =
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap g)).toRingedToposModulesHom.pullbackModules :=
  rfl

/-- The identification of the inverse image along `X_g` with the pullback of modules along the
morphism of small étale ringed topoi of `X_g`. -/
def relativeMapPullbackIso {T₁ T₂ : SchemesOver D.Y} (g : T₁ ⟶ T₂) :
    modulePullback B S hS (D.relativeMap g) ≅
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap g)).toRingedToposModulesHom.pullbackModules :=
  eqToIso (D.modulePullback_relativeMap_eq_toposPullback g)

namespace ThickeningLift

attribute [instance] isIso_fibre

variable {D} {ξ : CoherentObject D} {T' : SchemesOver D.Y} {h : ξ.T ⟶ T'}

/-- The object `(T', 𝒢')` of `Coh_{X/Y}` of a lift. -/
abbrev toObject (L : D.ThickeningLift ξ h) : CoherentObject D where
  T := T'
  F := L.F
  quasicoherent := L.quasicoherent
  finitePresentation := L.finitePresentation
  flat := L.flat
  properSupport := L.properSupport

/-- The morphism `ξ ⟶ (T', 𝒢')` of `Coh_{X/Y}` over `h` of a lift. -/
abbrev toHom (L : D.ThickeningLift ξ h) : CoherentHom ξ L.toObject where
  base := h
  fibre := L.fibre
  isIso_fibre := L.isIso_fibre

/-- A lift of `ξ` from a morphism of `Coh_{X/Y}` out of `ξ` over `h`. -/
abbrev ofHom {ξ' : CoherentObject D} (m : CoherentHom ξ ξ') (hT : ξ'.T = T')
    (hm : m.base ≫ eqToHom hT = h) : D.ThickeningLift ξ h := by
  subst hT
  simp only [eqToHom_refl, Category.comp_id] at hm
  subst hm
  exact
    { F := ξ'.F
      quasicoherent := ξ'.quasicoherent
      finitePresentation := ξ'.finitePresentation
      flat := ξ'.flat
      properSupport := ξ'.properSupport
      fibre := m.fibre
      isIso_fibre := m.isIso_fibre }

/-- The lifted module of a lift, read as a module on the small étale ringed topos of `X_{T'}`. -/
abbrev toposModule (L : D.ThickeningLift ξ h) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O) :=
  L.F

/-- The comparison `i^*𝒢' ≅ 𝒢` of a lift, with the inverse image read as the pullback of modules
along the morphism of small étale ringed topoi of `X_h`, through
`AlgebraicGeometry.Space.CoherentSituation.relativeMapPullbackIso`. -/
def toposFibre (L : D.ThickeningLift ξ h) :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toRingedToposModulesHom.pullbackModules.obj
      L.toposModule ⟶ objectToposModule ξ :=
  (D.relativeMapPullbackIso h).inv.app L.F ≫ L.fibre

/-- The comparison `i^*𝒢' ⟶ 𝒢` of a lift, read through the small étale ringed topoi, is an
isomorphism. -/
instance isIso_toposFibre (L : D.ThickeningLift ξ h) : IsIso L.toposFibre :=
  @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv ((D.relativeMapPullbackIso h).app L.F))
    L.isIso_fibre

/-- A map of lifted modules compatible with the comparisons is compatible with the comparisons
read through the morphism of small étale ringed topoi. -/
theorem toposFibre_naturality {L₁ L₂ : D.ThickeningLift ξ h} (e : L₁.F ⟶ L₂.F)
    (he : (modulePullback B S hS (D.relativeMap h)).map e ≫ L₂.fibre = L₁.fibre) :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toRingedToposModulesHom.pullbackModules.map e ≫
      L₂.toposFibre = L₁.toposFibre :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ L₂.fibre) ((D.relativeMapPullbackIso h).inv.naturality e)).trans
      ((Category.assoc _ _ _).trans (congrArg ((D.relativeMapPullbackIso h).inv.app L₁.F ≫ ·) he)))

/-- Two lifts are *isomorphic* when an isomorphism of the lifted modules is compatible with the
two comparisons; this is an isomorphism of the two objects over `T'` of `Coh_{X/Y}` under `ξ`
lying over the identity of `T'`. -/
def IsIsomorphic (L₁ L₂ : D.ThickeningLift ξ h) : Prop :=
  ∃ e : L₁.F ≅ L₂.F, (modulePullback B S hS (D.relativeMap h)).map e.hom ≫ L₂.fibre = L₁.fibre

/-- Isomorphism of lifts is an equivalence relation. -/
def setoid (D : CoherentSituation B S hS) (ξ : CoherentObject D) {T' : SchemesOver D.Y}
    (h : ξ.T ⟶ T') : Setoid (D.ThickeningLift ξ h) where
  r := IsIsomorphic
  iseqv :=
    { refl := fun L => ⟨Iso.refl L.F, by
        rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]⟩
      symm := fun {L₁ L₂} ⟨e, he⟩ => ⟨e.symm, by
        rw [← he, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.id_comp]⟩
      trans := fun {L₁ L₂ L₃} ⟨e, he⟩ ⟨e', he'⟩ => ⟨e ≪≫ e', by
        rw [Iso.trans_hom, CategoryTheory.Functor.map_comp, Category.assoc, he', he]⟩ }

end ThickeningLift

/-- The isomorphism classes of lifts of `ξ` across `h`. -/
abbrev ThickeningLiftClass (ξ : CoherentObject D) {T' : SchemesOver D.Y} (h : ξ.T ⟶ T') :
    Type _ :=
  Quotient (ThickeningLift.setoid D ξ h)

section FlatLift

variable {D} {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- The module `𝒢` of `ξ`, read on `X_{T'}` as a module over the direct image of `𝒪_{X_T}`
along the thickening `X_T ⊂ X_{T'}`: the presentation of `𝒪_{X_T}`-modules of the flat lifts of
`Deformation.ToposThickening.FlatLift`. -/
abbrev thickenedModule (ξ : CoherentObject D) {T' : SchemesOver D.Y} (h : ξ.T ⟶ T') :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)) :=
  (pushforwardModuleFunctor
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h)).toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)).obj
    (objectToposModule ξ)

/-- The map `𝒢' ⟶ i_*i^*𝒢' ≅ i_*𝒢` of a lift: the unit of `i^* ⊣ i_*` along the thickening
`i : X_T ⊂ X_{T'}` followed by the direct image of the comparison `i^*𝒢' ≅ 𝒢`. -/
def ThickeningLift.toThickened (L : D.ThickeningLift ξ h) :
    L.toposModule ⟶
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).pushforwardModules.obj (objectToposModule ξ) :=
  (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).pullbackAdjPushforwardModulesViaComparison.unit.app
      L.toposModule ≫
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).pushforwardModules.map L.toposFibre

/-- The map `𝒢' ⟶ i_*𝒢` of a lift is the unit of `i^* ⊣ i_*` at `𝒢'` followed by the direct
image of the comparison `i^*𝒢' ≅ 𝒢`. -/
theorem ThickeningLift.toThickened_eq (L : D.ThickeningLift ξ h) :
    L.toThickened h =
      (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).pullbackAdjPushforwardModulesViaComparison.unit.app
          L.toposModule ≫
        (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h)).pushforwardModules.map L.toposFibre :=
  rfl

/-- The map `𝒢' ⟶ i_*𝒢` of a lift kills the ideal product `I·𝒢'`. -/
theorem ThickeningLift.idealProduct_comp_toThickened (L : D.ThickeningLift ξ h) :
    (idealProductSubmodule (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      L.toposModule).ι ≫ L.toThickened h = 0 := by
  rw [ThickeningLift.toThickened, ← Category.assoc,
    idealProductSubmodule_unit_comp_zero
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh) L.toposModule,
    zero_comp]

/-- The sequence `0 ⟶ I·𝒢' ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0` of a lift is short exact: it is the ideal-product
sequence of `𝒢'` (`Deformation.ToposThickening.idealProductShortComplex_shortExact`) followed by
the direct image of the isomorphism `i^*𝒢' ≅ 𝒢`. -/
theorem ThickeningLift.shortExact_toThickened (L : D.ThickeningLift ξ h) :
    (ShortComplex.mk _ _ (L.idealProduct_comp_toThickened h hh)).ShortExact := by
  have h₀ := idealProductShortComplex_shortExact
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh) L.toposModule
  refine ShortComplex.shortExact_of_iso ?_ h₀
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).pushforwardModules.mapIso
      (asIso L.toposFibre)) ?_ ?_
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · simp only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, asIso_hom,
      idealProductShortComplex, ThickeningLift.toThickened]

/-- **The flat lift attached to a lift of `ξ`.** The lifted module `𝒢'`, with the unit
`𝒢' ⟶ i_*i^*𝒢'` of the adjunction `i^* ⊣ i_*` along the thickening `i : X_T ⊂ X_{T'}` followed by
the direct image of the comparison `i^*𝒢' ≅ 𝒢`. Flatness over `T'` is flatness over the base
`(X_{T'}, f'⁻¹𝒪_{T'})` of the relative square. -/
def ThickeningLift.toFlatLift (L : D.ThickeningLift ξ h) :
    FlatLift.{u, u + 1, u, u, u + 1, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh) (thickenedModule ξ h) where
  module' := L.toposModule
  π := L.toThickened h
  idealProduct_comp := L.idealProduct_comp_toThickened h hh
  isFlat := by
    have := L.quasicoherent
    exact (isFlat_restrictScalars_relBaseRight_iff
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')) L.toposModule).2
      ((isFlatOver_iff_isFlat_restrictScalars B S hS (D.relativeSquareSituation.projection T')
        L.F).1 L.flat)
  shortExact := L.shortExact_toThickened h hh

end FlatLift

end AlgebraicGeometry.Space.CoherentSituation

end
