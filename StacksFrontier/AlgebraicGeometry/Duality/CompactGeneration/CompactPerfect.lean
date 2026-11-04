module

public import StacksFrontier.Algebra.Homology.QuasiIsoRoof
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedCompactGeneration
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeBoundedComplex
public import StacksFrontier.Homology.Perfect.CompactObjectAnyModel
public import StacksFrontier.Homology.PseudoCoherentRelative.StrictlyPerfectRestrict
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.AffineFiniteProjective
import StacksCore.Algebra.Homology.QuasiIso
import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.CompactAndPerfectLocallySmall
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RepresentativeIndependence

/-!
# Compact and perfect objects of `D_QCoh(𝒪_X)`

For a quasi-compact quasi-separated scheme `X`, an object of `D_QCoh(𝒪_X)` is compact if and only
if it is perfect ([Stacks, Tag 09M1]), in every model of the derived category of `𝒪_X`-modules.

## Main definitions

* `Stacks.Duality.CompactPerfect.HasStrictModel`: a strictly perfect model of a complex along an
  open immersion of schemes, a roof of quasi-isomorphisms; it mentions no derived category.

## Main results

* `Stacks.Duality.isCompactObject_iff_isPerfect` — [Stacks, Tag 09M1], in every model of
  `D(𝒪_X)`.
* `Stacks.Duality.isPerfect_of_isCompactObject`, `Stacks.Duality.isCompactObject_of_isPerfect` —
  its two directions.
* `Stacks.Duality.isBounded_of_isCompactObject`, `Stacks.Duality.isBoundedBelow_of_isCompactObject`,
  `Stacks.Duality.isPseudoCoherent_of_isCompactObject` — consequences for compact objects.
* `Stacks.Duality.CompactPerfect.isPerfect_derivedRestrict` — restriction along an open immersion
  of schemes preserves perfectness.
* `Stacks.Duality.CompactPerfect.isPerfectComplex_of_forall_isPerfectComplex_restrictComplex` and
  `Stacks.Duality.CompactPerfect.isPerfect_of_isPerfect_derivedRestrict` — perfectness is local on
  a scheme.

## Implementation notes

The argument is the source's, carried out on complexes. The affine case `Spec R` goes through
derived sheafification `D(R) ≌ D_QCoh(𝒪_{Spec R})` ([Stacks, Tag 06Z0]), [Stacks, Tag 07LT] and
[Stacks, Tag 08EB]. Perfectness is read through strictly perfect models on open subschemes. Such
a model is a roof of quasi-isomorphisms between a strictly perfect complex and the restriction
of a representative, so it travels along open immersions of schemes, in particular along
`IsAffineOpen.isoSpec`, and perfectness is read off it at the level of complexes
(`AlgebraicGeometry.RingedSpace.isPerfectComplex_of_local_roofs`). In every model of `D(𝒪_W)` it
is an isomorphism `Q(P) ≅ Q(E|_W)`
(`Stacks.Duality.CompactPerfect.hasStrictModel_iff_nonempty_iso`).

Compact implies perfect because restriction to an affine open preserves compactness; perfect
implies compact because compactness is local for a cover by two quasi-compact opens, by
induction on an affine cover. Both steps use the adjunction between restriction to an open and
derived direct image on `D_QCoh`, and the commutation of derived direct image with direct sums
([Stacks, Tag 08DZ]), which are available at the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. The statements hold in every model of
`D(𝒪_X)`: their proofs carry compactness to the locally small model
(`Stacks.Duality.CompactPerfect.exists_isCompactObject_iff_of_model`) and use the locally small
models of the open subschemes and rings that occur, which the statements do not mention.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated StrictlyPerfect

universe u w w' t

namespace Stacks.Duality.CompactPerfect

open Stacks.Duality.OpenImmersion Stacks.Duality.QcqsGeneration

/-! ### The affine case -/

attribute [local instance] ModuleCat.hasDerivedCategory in
/-- **A compact object of `D_QCoh(𝒪_{Spec R})` has a strictly perfect model**, in any model of
`D(𝒪_{Spec R})`. It is the derived sheafification of a compact, hence perfect
([Stacks, Tag 07LT]), object of `D(R)`, that is of a bounded complex of finite projective modules,
whose sheafification is strictly perfect. The derived category of `R`-modules is taken at its
locally small model `ModuleCat.hasDerivedCategory`. -/
theorem exists_isStrictlyPerfect_iso_of_isCompactObject_spec (R : CommRingCat.{u})
    [HasDerivedCategory.{w} (Spec R).Modules]
    (K : Stacks.Duality.quasiCoherentDerivedCategory (Spec R)) (hK : IsCompactObject.{u} K) :
    ∃ P : CochainComplex (OXMod.{u, u} (Spec R).toRingedSpace) ℤ, IsStrictlyPerfect P ∧
      Nonempty ((DerivedCategory.Q (C := (Spec R).Modules)).obj P ≅ K.obj) := by
  let M := (derivedTilde R).objPreimage K
  let eM : (derivedTilde R).obj M ≅ K := (derivedTilde R).objObjPreimageIso K
  have hM : IsCompactObject.{u} M :=
    (isCompactObject_iff_isCompactObject_obj (derivedTilde R) M).mpr
      (isCompactObject_of_iso eM hK)
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨eP⟩⟩ :=
    (StacksDraft.Perfect.AnyModel.isPerfect_iff_isCompactObject_max.{u, u} M).mpr hM
  refine ⟨((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    Stacks.AffineTilde.isStrictlyPerfect_tildeComplex_of_projective P ?_ fun i => ⟨hf i, hp i⟩,
    ⟨?_⟩⟩
  · refine (Set.finite_Icc a b).subset fun i hi => ?_
    simp only [Set.mem_ofPred_eq] at hi
    by_contra h
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · exact hi (P.isZero_of_isStrictlyGE a i h)
    · exact hi (P.isZero_of_isStrictlyLE b i h)
  · exact ((derivedTildeFactors R).app P).symm ≪≫
      (ObjectProperty.ι _).mapIso ((derivedTilde R).mapIso eP.symm ≪≫ eM)

/-! ### Strictly perfect models along open immersions of schemes -/

section StrictModel

/-- The restriction of a complex of `𝒪_X`-modules along an open immersion of schemes. -/
abbrev restrictComplex {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (E : CochainComplex X.Modules ℤ) : CochainComplex W.Modules ℤ :=
  ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj E

/-- `E` has a **strictly perfect model along** the open immersion `j : W ⟶ X`: a strictly perfect
complex on `W` and the restriction of `E` along `j` are joined by a roof of quasi-isomorphisms. In
every model of `D(𝒪_W)` this is an isomorphism `Q(P) ≅ Q(E|_W)`
(`Stacks.Duality.CompactPerfect.hasStrictModel_iff_nonempty_iso`); no model is chosen. -/
def HasStrictModel {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (E : CochainComplex X.Modules ℤ) : Prop :=
  ∃ P : CochainComplex W.Modules ℤ, IsStrictlyPerfect (X := W.toRingedSpace) P ∧
    CochainComplex.QuasiIsoRoof P (restrictComplex j E)

/-- **A strictly perfect model is an isomorphism in the derived category.** In any model of
`D(𝒪_W)`, `E` has a strictly perfect model along `j` exactly when `Q(P) ≅ Q(E|_W)` for a
strictly perfect complex `P` (`CochainComplex.quasiIsoRoof_iff_nonempty_iso`). -/
theorem hasStrictModel_iff_nonempty_iso {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    [HasDerivedCategory.{w} W.Modules] (E : CochainComplex X.Modules ℤ) :
    HasStrictModel j E ↔ ∃ P : CochainComplex W.Modules ℤ,
      IsStrictlyPerfect (X := W.toRingedSpace) P ∧
        Nonempty ((DerivedCategory.Q (C := W.Modules)).obj P ≅
          (DerivedCategory.Q (C := W.Modules)).obj (restrictComplex j E)) :=
  exists_congr fun P => and_congr_right fun _ =>
    CochainComplex.quasiIsoRoof_iff_nonempty_iso P (restrictComplex j E)

/-- A quasi-isomorphism from a strictly perfect complex onto the restriction of `E` along `j` is a
strictly perfect model of `E` along `j`. -/
theorem HasStrictModel.of_quasiIso {W X : Scheme.{u}} {j : W ⟶ X} [IsOpenImmersion j]
    {E : CochainComplex X.Modules ℤ} (P : CochainComplex W.Modules ℤ)
    (hP : IsStrictlyPerfect (X := W.toRingedSpace) P) (q : P ⟶ restrictComplex j E)
    (hq : QuasiIso q) :
    HasStrictModel j E :=
  ⟨P, hP, .of_quasiIso q hq⟩

/-- Restriction along a composite of open immersions is restriction along the two in turn. -/
def restrictComplexCompIso {W' W X : Scheme.{u}} (g : W' ⟶ W) (j : W ⟶ X) [IsOpenImmersion g]
    [IsOpenImmersion j] (E : CochainComplex X.Modules ℤ) :
    restrictComplex (g ≫ j) E ≅ restrictComplex g (restrictComplex j E) :=
  (NatIso.mapHomologicalComplex (Scheme.Modules.restrictFunctorComp g j)
    (ComplexShape.up ℤ)).app E

/-- A strictly perfect model along `j` restricts to one along `g ≫ j`: restriction along `g` is
exact, so it carries the roof of quasi-isomorphisms to one, and it preserves strict
perfectness. -/
theorem HasStrictModel.comp {W' W X : Scheme.{u}} (g : W' ⟶ W) (j : W ⟶ X) [IsOpenImmersion g]
    [IsOpenImmersion j] {E : CochainComplex X.Modules ℤ} (h : HasStrictModel j E) :
    HasStrictModel (g ≫ j) E := by
  obtain ⟨P, hP, hr⟩ := h
  exact ⟨_, Scheme.Modules.isStrictlyPerfect_restrictFunctor g hP,
    (hr.map (Scheme.Modules.restrictFunctor g)).precomp_right_iso (restrictComplexCompIso g j E)⟩

/-- `Stacks.Duality.CompactPerfect.HasStrictModel` depends on the open immersion only up to
equality. -/
theorem HasStrictModel.congr {W X : Scheme.{u}} {j j' : W ⟶ X} [IsOpenImmersion j]
    [IsOpenImmersion j'] {E : CochainComplex X.Modules ℤ} (h : HasStrictModel j E)
    (e : j = j') : HasStrictModel j' E := by
  subst e
  exact h

/-- A strictly perfect model along `g ≫ j` is one along `g` of the restriction along `j`. -/
theorem HasStrictModel.of_comp {W' W X : Scheme.{u}} (g : W' ⟶ W) (j : W ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion j] {E : CochainComplex X.Modules ℤ}
    (h : HasStrictModel (g ≫ j) E) : HasStrictModel g (restrictComplex j E) :=
  h.imp fun _ ⟨hP, hr⟩ =>
    ⟨hP, hr.precomp_right_iso (restrictComplexCompIso g j E).symm⟩

/-- A strictly perfect model along `g` of the restriction along `j` is one along `g ≫ j`. -/
theorem HasStrictModel.to_comp {W' W X : Scheme.{u}} (g : W' ⟶ W) (j : W ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion j] {E : CochainComplex X.Modules ℤ}
    (h : HasStrictModel g (restrictComplex j E)) : HasStrictModel (g ≫ j) E :=
  h.imp fun _ ⟨hP, hr⟩ =>
    ⟨hP, hr.precomp_right_iso (restrictComplexCompIso g j E)⟩

/-- The ringed-space restriction of a complex to an open subscheme is the restriction along the
inclusion. -/
def restrictModulesComplexIso {X : Scheme.{u}} (U : X.Opens) (E : CochainComplex X.Modules ℤ) :
    ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u} X.toRingedSpace
      U).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ≅ restrictComplex U.ι E :=
  have h : (Scheme.Modules.restrictFunctor U.ι).PreservesZeroMorphisms := inferInstance
  (@NatIso.mapHomologicalComplex _ _ _ _ _ _ _ _ _
    (AlgebraicGeometry.RingedSpace.restrictModules_preservesZeroMorphisms X.toRingedSpace U) h
    (AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor X U)
    (ComplexShape.up ℤ)).app E

/-- **A complex with strictly perfect models on open subschemes near every point is perfect**:
each model is a roof of quasi-isomorphisms to the restriction of the complex to an open subspace,
and such roofs make it a perfect complex
(`AlgebraicGeometry.RingedSpace.isPerfectComplex_of_local_roofs`). -/
theorem isPerfectComplex_of_hasStrictModel {X : Scheme.{u}} {E : CochainComplex X.Modules ℤ}
    (h : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ HasStrictModel O.ι E) :
    AlgebraicGeometry.RingedSpace.IsPerfectComplex (X := X.toRingedSpace) E :=
  AlgebraicGeometry.RingedSpace.isPerfectComplex_of_local_roofs fun x => by
    obtain ⟨O, hxO, P, hP, hr⟩ := h x
    exact ⟨O, hxO, P, hP, hr.precomp_right_iso (restrictModulesComplexIso O E)⟩

/-- **A perfect complex has strictly perfect models on open subschemes near every point**: near
the point it receives a quasi-isomorphism from a strictly perfect complex on an open subspace,
which is one onto its restriction along the inclusion of the open subscheme. -/
theorem hasStrictModel_of_isPerfectComplex {X : Scheme.{u}} {E : CochainComplex X.Modules ℤ}
    (hE : AlgebraicGeometry.RingedSpace.IsPerfectComplex (X := X.toRingedSpace) E) (x : X) :
    ∃ O : X.Opens, x ∈ O ∧ HasStrictModel O.ι E := by
  obtain ⟨O, hxO, P, hP, q, hq⟩ := hE.exists_local x
  exact ⟨O, hxO, .of_quasiIso P hP (q ≫ (restrictModulesComplexIso O E).hom)
    ((quasiIso_iff_isIso_homologyMap _).2 fun j => isIso_homologyMap_comp _ _ j
      ((quasiIso_iff_isIso_homologyMap q).1 hq j) (isIso_homologyMap_iso_hom _ j))⟩

/-- **Perfectness from strictly perfect models on open subschemes.** If `K ≅ Q(E)` and near every
point the restriction of `E` to an open subscheme has a strictly perfect model, `K` is perfect:
`E` is a perfect complex (`Stacks.Duality.CompactPerfect.isPerfectComplex_of_hasStrictModel`). -/
theorem isPerfect_of_hasStrictModel {X : Scheme.{u}} [h : HasDerivedCategory.{w} X.Modules]
    (K : DerivedCategory X.Modules) (E : CochainComplex X.Modules ℤ)
    (eE : (DerivedCategory.Q (C := X.Modules)).obj E ≅ K)
    (hE : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ HasStrictModel O.ι E) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h K :=
  ⟨E, isPerfectComplex_of_hasStrictModel hE, ⟨eE⟩⟩

/-- **A perfect object has strictly perfect models on open subschemes** near every point: the
representative `E` is a perfect complex ([Stacks, Tag 08CN]). -/
theorem hasStrictModel_of_isPerfect {X : Scheme.{u}} [h : HasDerivedCategory.{w} X.Modules]
    (K : DerivedCategory X.Modules) (E : CochainComplex X.Modules ℤ)
    (eE : (DerivedCategory.Q (C := X.Modules)).obj E ≅ K)
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h K) (x : X) :
    ∃ O : X.Opens, x ∈ O ∧ HasStrictModel O.ι E := by
  let : HasDerivedCategory.{w} (OXMod.{u, u} X.toRingedSpace) := h
  exact hasStrictModel_of_isPerfectComplex
    (AlgebraicGeometry.RingedSpace.isPerfectComplex_of_isPerfect_representation hK ⟨eE⟩) x

end StrictModel

/-! ### Compactness at different models -/

section Model

/-- **Compactness in `D_QCoh(𝒪_X)` does not depend on the model.** An object of `D_QCoh(𝒪_X)` at
one model of `D(𝒪_X)`, represented by a complex `E`, has a counterpart at any other model,
represented by the same complex, which is compact exactly when the object is: the comparison
equivalence of the two models restricts to `D_QCoh(𝒪_X)`
(`StacksDraft.DerivedModel.derivedCategoryBModelEquiv`) and is additive. -/
theorem exists_isCompactObject_iff_of_model {X : Scheme.{u}}
    (h₁ : HasDerivedCategory.{w} X.Modules) (h₂ : HasDerivedCategory.{w'} X.Modules)
    (K : @Stacks.Duality.quasiCoherentDerivedCategory X h₁) {E : CochainComplex X.Modules ℤ}
    (eE : (@DerivedCategory.Q _ _ _ h₁).obj E ≅ K.obj) :
    ∃ K' : @Stacks.Duality.quasiCoherentDerivedCategory X h₂,
      Nonempty ((@DerivedCategory.Q _ _ _ h₂).obj E ≅ K'.obj) ∧
        (IsCompactObject.{t} K ↔ IsCompactObject.{t} K') := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (C := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) :=
    inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms
  let F := (StacksDraft.DerivedModel.derivedCategoryBModelEquiv (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) h₁ h₂).functor
  have : F.Additive := StacksDraft.DerivedModel.derivedCategoryBModelEquiv_functor_additive _ h₁ h₂
  exact ⟨F.obj K, ⟨((StacksDraft.DerivedModel.modelCompQIso h₁ h₂).app E).symm ≪≫
    (StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor.mapIso eE⟩,
    isCompactObject_iff_isCompactObject_obj F K⟩

/-- **Whether the perfect objects of `D_QCoh(𝒪_X)` are compact does not depend on the model** of
`D(𝒪_X)`: perfectness and compactness of an object at one model are those of its counterpart at
any other (`Stacks.Duality.CompactPerfect.exists_isCompactObject_iff_of_model`). -/
theorem isCompactObject_of_isPerfect_of_model {X : Scheme.{u}}
    (h₁ : HasDerivedCategory.{w} X.Modules) (h₂ : HasDerivedCategory.{w'} X.Modules)
    (H : ∀ L : @Stacks.Duality.quasiCoherentDerivedCategory X h₁,
      @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h₁ L.obj →
        IsCompactObject.{t} L)
    (K : @Stacks.Duality.quasiCoherentDerivedCategory X h₂)
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h₂ K.obj) :
    IsCompactObject.{t} K := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := hK
  obtain ⟨K', ⟨eE'⟩, hc⟩ := exists_isCompactObject_iff_of_model h₂ h₁ K eE
  exact hc.2 (H K' ⟨E, hE, ⟨eE'⟩⟩)

end Model

/-! ### Compact implies perfect -/

section CompactPerfect

/-- The restriction of `Q(E)` along an open immersion is `Q` of the restriction of `E`. -/
def derivedRestrictQIso {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} W.Modules]
    (E : CochainComplex X.Modules ℤ) :
    (derivedRestrict j).obj ((DerivedCategory.Q (C := X.Modules)).obj E) ≅
      (DerivedCategory.Q (C := W.Modules)).obj (restrictComplex j E) :=
  (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app E

attribute [local instance] Scheme.Modules.hasDerivedCategory in
/-- **A compact object restricts, on an affine open, to an object with a strictly perfect
model**, in any model of `D(𝒪_X)`. Compactness carries over to the locally small model
(`Stacks.Duality.CompactPerfect.exists_isCompactObject_iff_of_model`); there restriction to the
affine open is left adjoint to a functor commuting with direct sums ([Stacks, Tag 08DZ]), so it
preserves compactness, and the affine case applies. -/
theorem hasStrictModel_of_isCompactObject {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [h : HasDerivedCategory.{w} X.Modules]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hK : IsCompactObject.{u} K) (E : CochainComplex X.Modules ℤ)
    (eE : (DerivedCategory.Q (C := X.Modules)).obj E ≅ K.obj) {V : X.Opens}
    (hV : IsAffineOpen V) : HasStrictModel V.ι E := by
  obtain ⟨K₀, ⟨eE₀⟩, hc⟩ :=
    exists_isCompactObject_iff_of_model h (Scheme.Modules.hasDerivedCategory X) K eE
  replace hK := hc.1 hK
  clear hc eE K h
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward hV.fromSpec
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs hV.fromSpec)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward hV.fromSpec
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_isStrictlyPerfect_iso_of_isCompactObject_spec _ _
    (isCompactObject_map_of_adjunction (restrictedDerivedRestrictAdjunction hV.fromSpec) hK)
  have h : HasStrictModel hV.fromSpec E := (hasStrictModel_iff_nonempty_iso _ _).2
    ⟨P, hP, ⟨eP ≪≫ (derivedRestrict hV.fromSpec).mapIso eE₀.symm ≪≫
      derivedRestrictQIso hV.fromSpec E⟩⟩
  exact (h.comp hV.isoSpec.hom).congr hV.isoSpec_hom_fromSpec

/-- **[Stacks, Tag 09M1], compact implies perfect.** On a quasi-compact quasi-separated scheme a
compact object of `D_QCoh(𝒪_X)` is a perfect object of `D(𝒪_X)`, in any model of `D(𝒪_X)`. -/
theorem _root_.Stacks.Duality.isPerfect_of_isCompactObject {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [h : HasDerivedCategory.{w} X.Modules]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) (hK : IsCompactObject.{u} K) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h K.obj := by
  let E := (DerivedCategory.Q (C := X.Modules)).objPreimage K.obj
  let eE : (DerivedCategory.Q (C := X.Modules)).obj E ≅ K.obj :=
    (DerivedCategory.Q (C := X.Modules)).objObjPreimageIso K.obj
  refine isPerfect_of_hasStrictModel K.obj E eE fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  exact ⟨V, hxV, hasStrictModel_of_isCompactObject K hK E eE hV⟩

end CompactPerfect

/-! ### Boundedness and pseudo-coherence of compact objects -/

section Bounded

/-- A quasi-compact scheme is covered by finitely many affine opens, indexed by `Fin m`. -/
private theorem exists_affineOpen_cover_fin (X : Scheme.{u}) [CompactSpace X] :
    ∃ (m : ℕ) (V : Fin m → X.Opens), (∀ i, IsAffineOpen (V i)) ∧ (⨆ i, V i) = ⊤ := by
  obtain ⟨s, hs, hX⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  let t := hs.toFinset
  let e := t.equivFin
  refine ⟨t.card, fun i => ((e.symm i).1 : X.Opens), fun i => (e.symm i).1.2, ?_⟩
  rw [hX]
  refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun W hW => ?_)
  · exact le_iSup₂ (f := fun (W : X.affineOpens) (_ : W ∈ s) => (W : X.Opens)) (e.symm i).1
      (hs.mem_toFinset.mp (e.symm i).2)
  · exact le_trans (le_of_eq rfl) (le_iSup (fun i => ((e.symm i).1 : X.Opens))
      (e ⟨W, hs.mem_toFinset.mpr hW⟩) |>.trans' (by simp))

/-- The restriction along `j` of a complex with a strictly perfect model along `j` has bounded
cohomology: the roof of quasi-isomorphisms identifies it with the cohomology of a bounded
complex. -/
theorem exists_bounds_restrictComplex_of_hasStrictModel {W X : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] {E : CochainComplex X.Modules ℤ} (h : HasStrictModel j E) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero ((restrictComplex j E).homology n) := by
  obtain ⟨P, hP, hr⟩ := h
  obtain ⟨G, f, s, hf, hs⟩ := CochainComplex.quasiIsoRoof_iff.1 hr
  obtain ⟨a, ha⟩ := hP.bounded.bddBelow
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  refine ⟨a, b, fun n hn => ?_⟩
  have hPn : IsZero (P.X n) := by
    by_contra hz
    rcases hn with hn | hn
    · exact absurd (ha hz) (not_le.mpr hn)
    · exact absurd (hb hz) (not_le.mpr hn)
  exact (ShortComplex.isZero_homology_of_isZero_X₂ (P.sc n) hPn).of_iso
    (isoOfQuasiIsoAt s n ≪≫ (isoOfQuasiIsoAt f n).symm)

/-- A complex with a strictly perfect model along `j` has bounded cohomology after restriction
along `j`. -/
theorem exists_bounds_of_hasStrictModel {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    [HasDerivedCategory.{w} X.Modules] {E : CochainComplex X.Modules ℤ}
    (h : HasStrictModel j E) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero ((Scheme.Modules.restrictFunctor j).obj
      ((DerivedCategory.homologyFunctor X.Modules n).obj
        ((DerivedCategory.Q (C := X.Modules)).obj E))) := by
  obtain ⟨a, b, hab⟩ := exists_bounds_restrictComplex_of_hasStrictModel j h
  exact ⟨a, b, fun n hn => (hab n hn).of_iso ((Scheme.Modules.restrictFunctor j).mapIso
    ((DerivedCategory.homologyFunctorFactors X.Modules n).app E) ≪≫
      ((E.sc n).mapHomologyIso (Scheme.Modules.restrictFunctor j)).symm)⟩

/-- **A compact object of `D_QCoh(𝒪_X)` has bounded cohomology**, for `X` quasi-compact and
quasi-separated: on each member of a finite affine cover it has a strictly perfect model. -/
theorem _root_.Stacks.Duality.exists_bounds_of_isCompactObject {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [HasDerivedCategory.{w} X.Modules]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) (hK : IsCompactObject.{u} K) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj K.obj) := by
  let E := (DerivedCategory.Q (C := X.Modules)).objPreimage K.obj
  let eE : (DerivedCategory.Q (C := X.Modules)).obj E ≅ K.obj :=
    (DerivedCategory.Q (C := X.Modules)).objObjPreimageIso K.obj
  obtain ⟨m, V, hV, hX⟩ := exists_affineOpen_cover_fin X
  have hb : ∀ i, ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((Scheme.Modules.restrictFunctor (V i).ι).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj
          ((DerivedCategory.Q (C := X.Modules)).obj E))) := fun i =>
    exists_bounds_of_hasStrictModel _ (hasStrictModel_of_isCompactObject K hK E eE (hV i))
  choose a b hab using hb
  have hle : ∀ (f : Fin m → ℤ) i, |f i| ≤ ∑ j, |f j| := fun f i =>
    Finset.single_le_sum (f := fun j => |f j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  refine ⟨-∑ i, |a i|, ∑ i, |b i|, fun n hn => ?_⟩
  refine (isZero_of_forall_isZero_stalk _ fun x => ?_).of_iso
    ((DerivedCategory.homologyFunctor X.Modules n).mapIso eE.symm)
  have hx : x ∈ ⨆ i, V i := hX ▸ trivial
  obtain ⟨i, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine (Scheme.Modules.isZero_restrict_iff_forall_isZero_stalk (V i) _).1 (hab i n ?_) x hx
  rcases hn with hn | hn
  · exact Or.inl (by linarith [hle a i, neg_abs_le (a i)])
  · exact Or.inr (by linarith [hle b i, le_abs_self (b i)])

/-- **A compact object of `D_QCoh(𝒪_X)` is bounded below**, for `X` quasi-compact and
quasi-separated. -/
theorem _root_.Stacks.Duality.isBoundedBelow_of_isCompactObject {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [HasDerivedCategory.{w} X.Modules]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) (hK : IsCompactObject.{u} K) :
    DerivedCategoryB.IsBoundedBelow K.obj := by
  obtain ⟨a, b, h⟩ := exists_bounds_of_isCompactObject K hK
  exact ⟨a, fun n hn => h n (Or.inl hn)⟩

/-- **A compact object of `D_QCoh(𝒪_X)` is bounded**, for `X` quasi-compact and
quasi-separated. -/
theorem _root_.Stacks.Duality.isBounded_of_isCompactObject {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [HasDerivedCategory.{w} X.Modules]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) (hK : IsCompactObject.{u} K) :
    DerivedCategoryB.IsBounded K.obj := by
  obtain ⟨a, b, h⟩ := exists_bounds_of_isCompactObject K hK
  exact ⟨⟨a, fun n hn => h n (Or.inl hn)⟩, ⟨b, fun n hn => h n (Or.inr hn)⟩⟩

/-- **A compact object of `D_QCoh(𝒪_X)` is pseudo-coherent**, for `X` quasi-compact and
quasi-separated: it is perfect. -/
theorem _root_.Stacks.Duality.isPseudoCoherent_of_isCompactObject {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [h : HasDerivedCategory.{w} X.Modules]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) (hK : IsCompactObject.{u} K) :
    @AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent X.toRingedSpace h K.obj :=
  letI : HasDerivedCategory.{w} (OXMod.{u, u} X.toRingedSpace) := h
  Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect _
    (isPerfect_of_isCompactObject K hK)

end Bounded

/-! ### Perfect implies compact -/

section PerfectCompact

attribute [local instance] ModuleCat.hasDerivedCategory in
/-- **The affine case of perfect implies compact**, in any model of `D(𝒪_{Spec R})`. A perfect
object of `D_QCoh(𝒪_{Spec R})` is compact: it is the sheafification of an object of `D(R)`
which is perfect by [Stacks, Tag 08EB], hence compact by [Stacks, Tag 07LT]
(`AlgebraicGeometry.isCompactObject_iff_isPerfect_spec_of_model`). The derived category of
`R`-modules is taken at its locally small model `ModuleCat.hasDerivedCategory`. -/
theorem isCompactObject_of_isPerfect_spec (R : CommRingCat.{u})
    [h : HasDerivedCategory.{w} (Spec R).Modules]
    (K : Stacks.Duality.quasiCoherentDerivedCategory (Spec R))
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect (Spec R).toRingedSpace h K.obj) :
    IsCompactObject.{u} K :=
  (isCompactObject_iff_isPerfect_spec_of_model R K).2 hK

/-- **Restriction along an open immersion of schemes preserves perfectness**, in any models of
the two derived categories. Near a point of the source, a strictly perfect model of the object on
an open subscheme of the target restricts to one on its preimage. -/
theorem isPerfect_derivedRestrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [hX : HasDerivedCategory.{w} X.Modules] [hU : HasDerivedCategory.{w} U.Modules]
    (K : DerivedCategory X.Modules)
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace hX K) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect U.toRingedSpace hU
      ((derivedRestrict j).obj K) := by
  let E := (DerivedCategory.Q (C := X.Modules)).objPreimage K
  let eE : (DerivedCategory.Q (C := X.Modules)).obj E ≅ K :=
    (DerivedCategory.Q (C := X.Modules)).objObjPreimageIso K
  refine isPerfect_of_hasStrictModel _ (restrictComplex j E)
    ((derivedRestrictQIso j E).symm ≪≫ (derivedRestrict j).mapIso eE) fun y => ?_
  obtain ⟨O, hyO, hO⟩ := hasStrictModel_of_isPerfect K E eE hK (j y)
  refine ⟨j ⁻¹ᵁ O, hyO, HasStrictModel.of_comp _ _ ?_⟩
  exact (hO.comp (j ∣_ O)).congr (morphismRestrict_ι j O)

/-- **Perfectness of a complex is local on a scheme.** If every point of `X` has an open
neighbourhood `O` on which the restriction of `E` is a perfect complex, then `E` is a perfect
complex: a strictly perfect model of the restriction near a point is one of `E` along the image
of its open in `X`. -/
theorem isPerfectComplex_of_forall_isPerfectComplex_restrictComplex {X : Scheme.{u}}
    {E : CochainComplex X.Modules ℤ}
    (h : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧
      AlgebraicGeometry.RingedSpace.IsPerfectComplex (X := O.toScheme.toRingedSpace)
        (restrictComplex O.ι E)) :
    AlgebraicGeometry.RingedSpace.IsPerfectComplex (X := X.toRingedSpace) E := by
  refine isPerfectComplex_of_hasStrictModel fun x => ?_
  obtain ⟨O, hxO, hO⟩ := h x
  obtain ⟨O', hxO', hO'⟩ := hasStrictModel_of_isPerfectComplex hO ⟨x, hxO⟩
  refine ⟨O.ι ''ᵁ O', ⟨⟨x, hxO⟩, hxO', rfl⟩, ?_⟩
  have h₁ := (HasStrictModel.to_comp O'.ι O.ι hO').congr (O.ι.isoImage_hom_ι O').symm
  exact (h₁.comp (O.ι.isoImage O').inv).congr (by simp)

/-- **Perfectness is local on a scheme.** If every point of `X` has an open neighbourhood `O`
such that the restriction of `K` to the open subscheme `O` is perfect, then `K` is perfect: the
restrictions of a representative are perfect complexes ([Stacks, Tag 08CN]), so the
representative is one
(`Stacks.Duality.CompactPerfect.isPerfectComplex_of_forall_isPerfectComplex_restrictComplex`). -/
theorem isPerfect_of_isPerfect_derivedRestrict {X : Scheme.{u}}
    [hX : HasDerivedCategory.{w} X.Modules]
    [hO : ∀ O : X.Opens, HasDerivedCategory.{w} O.toScheme.Modules] (K : DerivedCategory X.Modules)
    (h : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧
      @Stacks.Cohomology.PerfectComplexes.IsPerfect O.toScheme.toRingedSpace (hO O)
        ((derivedRestrict O.ι).obj K)) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace hX K := by
  let E := (DerivedCategory.Q (C := X.Modules)).objPreimage K
  let eE : (DerivedCategory.Q (C := X.Modules)).obj E ≅ K :=
    (DerivedCategory.Q (C := X.Modules)).objObjPreimageIso K
  refine ⟨E, isPerfectComplex_of_forall_isPerfectComplex_restrictComplex fun x => ?_, ⟨eE⟩⟩
  obtain ⟨O, hxO, hK⟩ := h x
  have e := (derivedRestrictQIso O.ι E).symm ≪≫ (derivedRestrict O.ι).mapIso eE
  exact ⟨O, hxO, @AlgebraicGeometry.RingedSpace.isPerfectComplex_of_isPerfect_representation
    _ (hO O) _ hK _ ⟨e⟩⟩

attribute [local instance] Scheme.Modules.hasDerivedCategory in
/-- **Perfect implies compact for a cover by a quasi-compact open and an affine open**, in any
models of the derived categories. If `X = W ∪ V` with `W` quasi-compact and `V` affine, and
perfect objects of `D_QCoh(𝒪_W)` are compact, then so are those of `D_QCoh(𝒪_X)`: at the locally
small models, to which both statements carry over
(`Stacks.Duality.CompactPerfect.isCompactObject_of_isPerfect_of_model`), compactness is local for
the two restrictions. -/
theorem isCompactObject_of_isPerfect_of_sup_affine {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [hX : HasDerivedCategory.{w} X.Modules] (W : X.Opens)
    (hW : IsCompact (W : Set X)) [hW' : HasDerivedCategory.{w'} W.toScheme.Modules]
    {V : X.Opens} (hV : IsAffineOpen V) (hcov : ∀ x : X, x ∈ W ∨ x ∈ V)
    (hWc : ∀ L : Stacks.Duality.quasiCoherentDerivedCategory W.toScheme,
      @Stacks.Cohomology.PerfectComplexes.IsPerfect W.toScheme.toRingedSpace hW' L.obj →
        IsCompactObject.{u} L)
    (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace hX K.obj) :
    IsCompactObject.{u} K := by
  have hWc₀ := isCompactObject_of_isPerfect_of_model hW'
    (Scheme.Modules.hasDerivedCategory W.toScheme) hWc
  refine isCompactObject_of_isPerfect_of_model (Scheme.Modules.hasDerivedCategory X) hX ?_ K hK
  clear hWc hK K hW' hX
  intro K hK
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  let jA := W.ι
  let jB := hV.fromSpec
  have hC : IsCompact ((jB ⁻¹ᵁ W : (Spec Γ(X, V)).Opens) : Set (Spec Γ(X, V))) :=
    jB.isCompact_preimage hW
  have : CompactSpace (jB ⁻¹ᵁ W).toScheme := isCompact_iff_compactSpace.mp hC
  let adjA := restrictedDerivedRestrictAdjunction jA
  let adjB := restrictedDerivedRestrictAdjunction jB
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jA
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jA)).CommShift ℤ :=
    adjA.rightAdjointCommShift ℤ
  have : (Stacks.Duality.quasiCoherentDerivedPushforward jA
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jA)).Additive :=
    adjA.right_adjoint_additive
  have : (Stacks.Duality.quasiCoherentDerivedPushforward jB
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jB)).Additive :=
    adjB.right_adjoint_additive
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward jA
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jA)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward jA
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward jB
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jB)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward jB
  have hker : ∀ N : Stacks.Duality.quasiCoherentDerivedCategory X,
      IsZero ((restrictedDerivedRestrict jB).obj N) → IsIso (adjA.unit.app N) := by
    intro N hN
    refine Stacks.Duality.SupportedGeneration.isIso_unit_of_isZero_restrict_two jA jB
      (jB ∣_ W) (jB ⁻¹ᵁ W).ι (isPullback_morphismRestrict jB W) (fun x => ?_) N hN
    rcases hcov x with h | h
    · exact Or.inl ⟨⟨x, h⟩, rfl⟩
    · right
      have h' : x ∈ Set.range jB := by
        rw [hV.range_fromSpec]
        exact h
      exact h'
  exact isCompactObject_of_isCompactObject_restrict adjA adjB hker K
    (hWc₀ _ (isPerfect_derivedRestrict jA K.obj hK))
    (isCompactObject_of_isPerfect_spec _ _ (isPerfect_derivedRestrict jB K.obj hK))

attribute [local instance] Scheme.Modules.hasDerivedCategory in
/-- Perfect implies compact for a quasi-compact quasi-separated scheme covered by `m` affine
opens, by induction on `m`, in any model of `D(𝒪_X)` whose morphisms live in `Type u`. The
induction passes through open subschemes, whose derived categories are taken at their locally
small models; this fixes the universe of the model. -/
theorem isCompactObject_of_isPerfect_of_affineCover : ∀ (m : ℕ) {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [h : HasDerivedCategory.{u} X.Modules] (V : Fin m → X.Opens),
    (∀ i, IsAffineOpen (V i)) → (⨆ i, V i) = ⊤ →
      ∀ K : Stacks.Duality.quasiCoherentDerivedCategory X,
        @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h K.obj →
          IsCompactObject.{u} K
  | 0, X, _, _, h, V, _, hcov, K, _ => by
      have hK : IsZero K := by
        refine isZero_fullSubcategory_of_isZero_obj
          ((DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun n =>
            isZero_of_forall_isZero_stalk _ fun x => ?_)
        have hx : x ∈ (⊤ : X.Opens) := trivial
        rw [← hcov] at hx
        simp at hx
      constructor
      intro I _ E _
      exact ⟨fun _ _ _ => DFinsupp.ext fun _ => hK.eq_of_src _ _,
        fun _ => ⟨0, hK.eq_of_src _ _⟩⟩
  | m + 1, X, _, _, h, V, hV, hcov, K, hK => by
      let W : X.Opens := ⨆ i : Fin m, V i.castSucc
      have hWc : IsCompact (W : Set X) := by
        rw [TopologicalSpace.Opens.coe_iSup]
        exact isCompact_iUnion fun i => (hV _).isCompact
      have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hWc
      have : QuasiSeparatedSpace W.toScheme := W.ι.isOpenEmbedding.quasiSeparatedSpace
      refine isCompactObject_of_isPerfect_of_sup_affine W hWc (hV (Fin.last m)) (fun x => ?_)
        (isCompactObject_of_isPerfect_of_affineCover m (fun i => W.ι ⁻¹ᵁ V i.castSucc)
          (fun i => (hV i.castSucc).preimage_of_isOpenImmersion W.ι (by
            rw [Scheme.Opens.opensRange_ι]
            exact le_iSup (fun i : Fin m => V i.castSucc) i))
          (by
            rw [← Scheme.Hom.preimage_iSup]
            exact Scheme.Opens.ι_preimage_self W)) K hK
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨i, hi⟩ := hx
      exact Fin.lastCases (motive := fun i => x ∈ V i → x ∈ W ∨ x ∈ V (Fin.last m))
        (fun h => Or.inr h) (fun j h => Or.inl (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, h⟩)) i hi

attribute [local instance] Scheme.Modules.hasDerivedCategory in
/-- **[Stacks, Tag 09M1], perfect implies compact.** On a quasi-compact quasi-separated scheme a
perfect object of `D(𝒪_X)` with quasi-coherent cohomology is a compact object of
`D_QCoh(𝒪_X)`, in any model of `D(𝒪_X)`: at the locally small model this is the induction on an
affine cover, and it carries over to every model
(`Stacks.Duality.CompactPerfect.isCompactObject_of_isPerfect_of_model`). -/
theorem _root_.Stacks.Duality.isCompactObject_of_isPerfect {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [h : HasDerivedCategory.{w} X.Modules]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hK : @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h K.obj) :
    IsCompactObject.{u} K := by
  refine isCompactObject_of_isPerfect_of_model (Scheme.Modules.hasDerivedCategory X) h ?_ K hK
  clear hK K h
  intro K hK
  obtain ⟨m, V, hV, hX⟩ := exists_affineOpen_cover_fin X
  exact isCompactObject_of_isPerfect_of_affineCover m V hV hX K hK

/-- **[Stacks, Tag 09M1].** On a quasi-compact quasi-separated scheme `X`, an object of
`D_QCoh(𝒪_X)` is compact if and only if it is a perfect object of `D(𝒪_X)`, in any model of
`D(𝒪_X)`. -/
@[stacks 09M1]
theorem _root_.Stacks.Duality.isCompactObject_iff_isPerfect {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [h : HasDerivedCategory.{w} X.Modules]
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) :
    IsCompactObject.{u} K ↔ @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace h K.obj :=
  ⟨Stacks.Duality.isPerfect_of_isCompactObject K, Stacks.Duality.isCompactObject_of_isPerfect K⟩

end PerfectCompact

end Stacks.Duality.CompactPerfect

end
