module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.CechUnitSplitting
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.InjectivityOfUnit
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperSupportGlobalSectionsPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpen
public import StacksFrontier.AlgebraicGeometry.DerivedTildeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# The direct image of the structure sheaf of a proper flat family with `H⁰` of fibres trivial

[Stacks, Tag 0E62]: let `f : X ⟶ S` be proper, flat and of finite presentation, with
`κ(s) = H⁰(X_s, 𝒪_{X_s})` for all `s ∈ S`. Then (a) `f_*𝒪_X = 𝒪_S`, and this holds after any base
change, and (b) locally on `S` we have `Rf_*𝒪_X ≅ 𝒪_S ⊕ P` in `D(𝒪_S)` with `P` perfect of Tor
amplitude in `[1, ∞)`.

## Main results

* `…ProperFlatStructureSheafSplitting.properFlat_structureSheaf_splitting`: **[Stacks, Tag 0E62]**.
* `…ProperFlatStructureSheafSplitting.isIso_c_of_isPullback`: part (a), for every cartesian square.
* `…ProperFlatStructureSheafSplitting.exists_openImmersion_splitting`: part (b).
* `…ProperFlatStructureSheafSplitting.exists_away_patch`: both parts over an affine chart
  `Spec A ⟶ S`, after inverting one element of `A`.
* `…ProperFlatStructureSheafSplitting.nonempty_derivedPushforward_iso_tilde_cech`: on an affine
  base, `Rf_*(F[0])` is the sheaf associated to the Čech model of `RΓ(X, F)`.
* `…ProperFlatStructureSheafSplitting.bijective_baseRingHom_of_fibre`: the fibre hypothesis read on
  an arbitrary base change of an affine chart to a residue field.

## Implementation notes

The source's proof reads cohomology and base change ([Stacks, Tag 0B91]) to get `E = Rf_*𝒪_X`
perfect with formation commuting with base change, and then runs the algebra of
More on Algebra, Lemma 0A1U. Here both inputs are made concrete on an affine chart `Spec A`:
perfectness of `RΓ(X_A, 𝒪)` in `D(A)` is [Stacks, Tag 0A1H]
(`ProperSupportGlobalSectionsPerfect.isPerfect_derivedGlobalSectionsOverBase_of_properSupport`),
and base change is the Čech base-change isomorphism of [Stacks, Tag 07VK] (2), which carries the
cochain of the function `1` to the cochain of its pullback. The algebra is
`Stacks.AlgebraicGeometry.ProperFlatFamilyCech.exists_away_unitSplitting`.

Part (b) is stated through open immersions `ι : V ⟶ S` covering `S` (here `V = Spec A_h`), with the
restriction of `Rf_*𝒪_X` along `ι`; this is the same as an open covering of `S` since an open
immersion is an isomorphism onto its open image. The Tor amplitude of `P` is recorded as an
interval `[1, b]` for some `b`, which is stronger than `[1, ∞)`.

Part (a) is checked on sections: injectivity on every open holds for any flat surjective morphism
(`Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.injective_app_of_flat_of_surjective`), and
surjectivity is local (`TopCat.Presheaf.app_surjective_of_injective_of_locally_surjective`); over
an affine open `W` of `S'` lying over a chart `Spec A_h` the global functions on `f'⁻¹W` are free
of rank one over `Γ(S', W)`, so the structure map is bijective
(`RingHom.bijective_of_linearEquiv_self`).

## References

* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
open Stacks.AlgebraicGeometry.ProperFlatFamilyCech
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatStructureSheafSplitting

attribute [local instance 10000] HasDerivedCategory.standard

section Bridge

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`Rf_*(F[0])` on an affine base is the sheaf associated to the Čech model.** -/
theorem nonempty_derivedPushforward_iso_tilde_cech [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k))) :
    Nonempty ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      (tilde.functor (CommRingCat.of A)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (baseAlternatingCechComplex f U hU F))) := by
  let W := (DerivedCategory.singleFunctor X.Modules 0).obj F
  let T := (derivedPushforward f.toLRSHom.toShHom).obj W
  have hT : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules n).obj
      T).IsQuasicoherent :=
    isQuasicoherent_derivedPushforward f
      ⟨W, Stacks.Thickenings.isQuasicoherent_homology_singleFunctor_obj _ F inferInstance⟩
  obtain ⟨M0, ⟨e0⟩⟩ := StandardModel.exists_iso_mapDerivedCategory (CommRingCat.of A) T hT
  have hu := StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit (CommRingCat.of A)
  have eM : M0 ≅ (derivedGlobalSectionsOver f).obj W :=
    asIso ((derivedTildeGlobalSectionsAdjunction (CommRingCat.of A)).val.unit.app M0) ≪≫
      (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).mapIso
        ((derivedTildeCompι (CommRingCat.of A)).app M0 ≪≫ e0) ≪≫
      ((derivedGlobalSectionsOverPushforwardIso f).app W).symm
  have eC : DerivedCategory.Q.obj (baseAlternatingCechComplex f U hU F) ≅ M0 :=
    alternatingCechIsoDerivedGlobalSectionsOverBase f U hU F haff ≪≫
      Stacks.AlgebraicGeometry.ProperSupportGlobalSectionsPerfect.derivedGlobalSectionsOverBaseIso
        f F ≪≫ eM.symm
  exact ⟨e0.symm ≪≫ (tilde.functor (CommRingCat.of A)).mapDerivedCategory.mapIso eC.symm⟩

end Bridge

section Unit

/-- `f_* 𝒪_X = 𝒪_Y` is unchanged by postcomposition with an isomorphism of schemes. -/
theorem isIso_c_comp_isIso {X Y Z : Scheme.{u}} (p : X ⟶ Y) (e : Y ⟶ Z) [IsIso e]
    (h : IsIso p.c) : IsIso (p ≫ e).c := by
  rw [Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_app] at h ⊢
  intro U
  rw [Scheme.Hom.comp_app]
  exact IsIso.comp_isIso' inferInstance (h _)

end Unit

section FibreTransfer

open Stacks.AlgebraicGeometry.ProperFlatFamilyUnit

/-- The structure map of `X` over `Spec R` on the top open is the one on global functions. -/
private theorem baseRingHom_top_eq_globalRingHom {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Spec (.of R)) : Stacks.Cech.baseRingHom f ⊤ = Stacks.Cech.globalRingHom f := by
  rw [Stacks.Cech.baseRingHom, show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 ⊤ from
    Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The source's fibre hypothesis, read on the base change of an affine chart to a residue
field.** If `κ(s) → H⁰(X_s, 𝒪)` is bijective for every `s`, then for an open immersion
`j : Spec A ⟶ S`, a prime `p` of `A` and any cartesian square exhibiting `X'` as the base change
of `X_A = X ×_S Spec A` to `κ(p)`, the structure map `κ(p) → Γ(X', 𝒪)` is bijective. -/
theorem bijective_baseRingHom_of_fibre {X S : Scheme.{u}} (f : X ⟶ S)
    (hfib : ∀ s : S, Function.Bijective ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
      (f.fiberToSpecResidueField s).appTop))
    {A : Type u} [CommRing A] (j : Spec (.of A) ⟶ S) [IsOpenImmersion j] {XA : Scheme.{u}}
    {fA : XA ⟶ Spec (.of A)} {gA : XA ⟶ X} (hA : IsPullback gA fA f j)
    (p : Ideal A) [p.IsPrime] {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of p.ResidueField)}
    {g' : X' ⟶ XA}
    (hsq : IsPullback g' f' fA (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))) :
    Function.Bijective (Stacks.Cech.baseRingHom f' ⊤) := by
  let x : Spec (.of A) := ⟨p, inferInstance⟩
  let s := j x
  let e : Spec (.of p.ResidueField) ⟶ Spec (S.residueField s) :=
    Spec.map (Scheme.Spec.residueFieldIso (.of A) x).hom ≫ Spec.map (j.residueFieldMap x)
  have : IsIso e := IsIso.comp_isIso
  have he : Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)) ≫ j =
      e ≫ S.fromSpecResidueField s := by
    change _ = Spec.map (Scheme.Spec.residueFieldIso (.of A) x).hom ≫
      (Spec.map (j.residueFieldMap x) ≫ S.fromSpecResidueField (j x))
    rw [j.SpecMap_residueFieldMap_fromSpecResidueField x,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of A) x,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hout : IsPullback (g' ≫ gA) f' f (e ≫ S.fromSpecResidueField s) := by
    rw [← he]
    exact hsq.paste_horiz hA
  have hl : IsPullback (𝟙 (f.fiber s)) (f.fiberToSpecResidueField s ≫ inv e)
      (f.fiberToSpecResidueField s) e :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hfibsq : IsPullback (𝟙 (f.fiber s) ≫ f.fiberι s) (f.fiberToSpecResidueField s ≫ inv e) f
      (e ≫ S.fromSpecResidueField s) :=
    hl.paste_horiz (IsPullback.of_hasPullback f (S.fromSpecResidueField s))
  have h3 : IsIso f'.c := by
    rw [← IsPullback.isoIsPullback_hom_snd _ _ hout hfibsq]
    exact isIso_c_comp _ _ (isIso_c_comp_isIso _ _
      ((isIso_fiberToSpecResidueField_unit_iff_isIso_c f s).1
        ((isIso_fiberToSpecResidueField_unit_iff f s).2 (hfib s))))
  rw [baseRingHom_top_eq_globalRingHom]
  exact ((isIso_c_iff_bijective_appTop f').1 h3).comp
    (ConcreteCategory.bijective_of_isIso (toSpecΓ (.of p.ResidueField)))

end FibreTransfer

section Patch

/-- **The Čech model of `RΓ(X, 𝒪_X)` of a proper flat family over an affine base is perfect**
([Stacks, Tag 0A1H]). -/
private theorem isPerfect_baseAlternatingCechComplex_unit {A : Type u} [CommRing A]
    {XA : Scheme.{u}} (fA : XA ⟶ Spec (.of A)) [IsProper fA] [Flat fA]
    [LocallyOfFinitePresentation fA]
    {I : Type u} [LinearOrder I] (U : I → XA.Opens) (hU : (⊤ : XA.Opens) = ⨆ i, U i)
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k))) :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (baseAlternatingCechComplex fA U hU (Scheme.unitModule XA))) :=
  have : (Scheme.unitModule XA).IsFinitePresentation :=
    inferInstanceAs (SheafOfModules.unit XA.ringCatSheaf).IsFinitePresentation
  StacksDraft.Perfect.isPerfect_of_iso
    (alternatingCechIsoDerivedGlobalSectionsOverBase fA U hU _ haff)
    (ProperSupportGlobalSectionsPerfect.isPerfect_derivedGlobalSectionsOverBase_of_properSupport
      fA _ (Stacks.Cohomology.PerfectPushforward.isFlatOver_structureModule fA)
      ⟨⊤, Stacks.Cohomology.PerfectPushforward.isProperOver_top_of_isProper fA,
        fun _ _ => trivial⟩)

/-- The sheaf associated to a bounded complex of finite free `R`-modules in degrees `[1, b]` is
perfect of Tor amplitude in `[1, b]`. -/
private theorem isPerfect_and_hasTorAmplitude_tilde {R : Type u} [CommRing R]
    (T : CochainComplex (ModuleCat.{u} R) ℤ) {b : ℤ} (hT1 : T.IsStrictlyGE 1)
    (hTb : T.IsStrictlyLE b) (hTfree : ∀ i, Module.Free R (T.X i))
    (hTfin : ∀ i, Module.Finite R (T.X i)) :
    RingedSpace.IsPerfect (X := (Spec (.of R)).toRingedSpace)
        ((tilde.functor (CommRingCat.of R)).mapDerivedCategory.obj (DerivedCategory.Q.obj T)) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude (Spec (.of R)).toRingedSpace
        ((tilde.functor (CommRingCat.of R)).mapDerivedCategory.obj (DerivedCategory.Q.obj T))
        1 b := by
  have hTproj : ∀ i, Module.Projective R (T.X i) := fun i => have := hTfree i; inferInstance
  have hTflat : ∀ i, Module.Flat R (T.X i) := fun i => have := hTfree i; inferInstance
  exact ⟨(isPerfect_tilde_iff (R := .of R) (DerivedCategory.Q.obj T)).2
      ⟨T, 1, b, hT1, hTb, hTfin, hTproj, ⟨Iso.refl _⟩⟩,
    (hasTorAmplitude_tilde_iff (R := .of R) (DerivedCategory.Q.obj T) 1 b).2
      ((StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative R
        (DerivedCategory.Q.obj T) 1 b).2 ⟨T, hTflat, hT1, hTb, ⟨Iso.refl _⟩⟩)⟩

/-- **Base change of a splitting of the Čech model.** If the base change along `α : A →+* B` of
the Čech model of `RΓ(X_A, 𝒪)` splits as `B ⊕ T`, then for every base change `X_B ⟶ Spec B` of
`X_A`, `R(f_B)_*𝒪 ≅ 𝒪 ⊕ T~`. -/
private theorem nonempty_derivedPushforward_unit_iso_biprod_of_isPullback {A B : Type u}
    [CommRing A] [CommRing B] (α : A →+* B) {XA : Scheme.{u}} (fA : XA ⟶ Spec (.of A)) [IsProper fA]
    {I : Type u} [Finite I] [LinearOrder I] (U : I → XA.Opens) (hU : (⊤ : XA.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) {T : CochainComplex (ModuleCat.{u} B) ℤ}
    (eC : DerivedCategory.Q.obj (extendScalarsComplex α
        (baseAlternatingCechComplex fA U hU (Scheme.unitModule XA))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B) ⊞
        DerivedCategory.Q.obj T)
    {Xh : Scheme.{u}} {fh : Xh ⟶ Spec (.of B)} {gh : Xh ⟶ XA}
    (hsq : IsPullback gh fh fA (Spec.map (CommRingCat.ofHom α))) :
    Nonempty ((derivedPushforward fh.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor Xh.Modules 0).obj (Scheme.unitModule Xh)) ≅
      ((DerivedCategory.singleFunctor (Spec (.of B)).Modules 0).obj
          (Scheme.unitModule (Spec (.of B))) ⊞
        (tilde.functor (CommRingCat.of B)).mapDerivedCategory.obj (DerivedCategory.Q.obj T) :
        DerivedCategory (Spec (.of B)).Modules)) := by
  classical
  let F := Scheme.unitModule XA
  let C := baseAlternatingCechComplex fA U hU F
  let R : CommRingCat.{u} := .of B
  let P := (tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj T)
  have : IsProper fh := MorphismProperty.of_isPullback hsq inferInstance
  let U' : I → Xh.Opens := fun i => gh ⁻¹ᵁ U i
  have hU' : (⊤ : Xh.Opens) = ⨆ i, U' i := top_eq_iSup_preimage gh U hU
  obtain ⟨eB⟩ := nonempty_derivedPushforward_iso_tilde_cech fh (Scheme.unitModule Xh) U' hU'
    (iInf_preimage_isAffineOpen α hsq U hUaff)
  let eCech : DerivedCategory.Q.obj (baseAlternatingCechComplex fh U' hU'
      (Scheme.unitModule Xh)) ≅ DerivedCategory.Q.obj (extendScalarsComplex α C) :=
    DerivedCategory.Q.mapIso
      ((baseAlternatingCechComplexMapIso fh U' hU' (Scheme.Modules.pullbackUnitIso gh)).symm ≪≫
        (baseAlternatingCechComplexBaseChangeIso α hsq F U hU hUaff).symm)
  have : PreservesBinaryBiproducts (tilde.functor R).mapDerivedCategory :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let e1 : (tilde.functor R).mapDerivedCategory.obj
      (DerivedCategory.Q.obj (extendScalarsComplex α C)) ≅
      ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj (Scheme.unitModule (Spec R)) ⊞ P :
        DerivedCategory (Spec R).Modules) :=
    (tilde.functor R).mapDerivedCategory.mapIso eC ≪≫
      (tilde.functor R).mapDerivedCategory.mapBiprod _ _ ≪≫
      biprod.mapIso (((tilde.functor R).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (tildeSelf (R := R))) (Iso.refl _)
  exact ⟨eB ≪≫ (tilde.functor R).mapDerivedCategory.mapIso eCech ≪≫ e1⟩

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
  (hfib : ∀ s : S, Function.Bijective ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
    (f.fiberToSpecResidueField s).appTop))

include hfib in
/-- **The splitting on an affine chart.** For an open immersion `j : Spec A ⟶ S` and a prime `p`
of `A` there is `h ∉ p` such that

* for every `A`-algebra `B` in which `h` is invertible and every base change `X'' ⟶ Spec B` of
  `X_A = X ×_S Spec A`, the structure map `B → Γ(X'', 𝒪)` is bijective, and
* there is a perfect `P` on `Spec A_h` of Tor amplitude in `[1, b]` such that for every base
  change `X_h ⟶ Spec A_h` of `X_A`, `R(f_h)_*𝒪 ≅ 𝒪 ⊕ P`. -/
theorem exists_away_patch {A : Type u} [CommRing A] (j : Spec (.of A) ⟶ S) [IsOpenImmersion j]
    {XA : Scheme.{u}} {fA : XA ⟶ Spec (.of A)} {gA : XA ⟶ X} (hA : IsPullback gA fA f j)
    (p : Ideal A) [p.IsPrime] :
    ∃ h : A, h ∉ p ∧
      (∀ {B : Type u} [CommRing B] (φ : A →+* B), IsUnit (φ h) →
        ∀ {X'' : Scheme.{u}} {f'' : X'' ⟶ Spec (.of B)} {g'' : X'' ⟶ XA}
          (_ : IsPullback g'' f'' fA (Spec.map (CommRingCat.ofHom φ))),
          Function.Bijective (Stacks.Cech.baseRingHom f'' ⊤)) ∧
      ∃ (P : DerivedCategory (Spec (.of (Localization.Away h))).Modules),
        RingedSpace.IsPerfect (X := (Spec (.of (Localization.Away h))).toRingedSpace) P ∧
        (∃ b : ℤ, Stacks.Cohomology.TorAmplitude.HasTorAmplitude
          (Spec (.of (Localization.Away h))).toRingedSpace P 1 b) ∧
        ∀ {Xh : Scheme.{u}} {fh : Xh ⟶ Spec (.of (Localization.Away h))} {gh : Xh ⟶ XA}
          (_ : IsPullback gh fh fA
            (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away h))))),
          Nonempty ((derivedPushforward fh.toLRSHom.toShHom).obj
              ((DerivedCategory.singleFunctor Xh.Modules 0).obj (Scheme.unitModule Xh)) ≅
            ((DerivedCategory.singleFunctor (Spec (.of (Localization.Away h))).Modules 0).obj
                (Scheme.unitModule (Spec (.of (Localization.Away h)))) ⊞ P :
              DerivedCategory (Spec (.of (Localization.Away h))).Modules)) := by
  classical
  have : IsProper fA := MorphismProperty.of_isPullback hA inferInstance
  have : Flat fA := MorphismProperty.of_isPullback hA inferInstance
  have : LocallyOfFinitePresentation fA := MorphismProperty.of_isPullback hA inferInstance
  obtain ⟨I, _, _, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper fA
  let F := Scheme.unitModule XA
  have hflat : IsFlatOver fA.toLRSHom.toShHom F :=
    Stacks.Cohomology.PerfectPushforward.isFlatOver_structureModule fA
  have hperf := isPerfect_baseAlternatingCechComplex_unit fA U hU haff
  have hsqκ := IsPullback.of_hasPullback fA
    (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))
  have hb := bijective_baseRingHom_of_fibre f hfib j hA p hsqκ
  obtain ⟨h, hh, ha, T, b, hT1, hTb, hTfree, hTfin, ⟨eC⟩⟩ :=
    exists_away_unitSplitting fA hflat U hU hUaff
      (StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _ hperf) p
      (finrank_homology_zero_extendScalars_residueField fA U hU hUaff p hsqκ hb)
      (one_tmul_unitCochain_ne_zero fA U hU hUaff p hsqκ hb)
  refine ⟨h, hh, ?_, ?_⟩
  · intro B _ φ hφ X'' f'' g'' hsq
    obtain ⟨e⟩ := ha φ hφ hsq
    let := Stacks.Cech.sectionsModule f'' ((Scheme.Modules.pullback g'').obj F) ⊤
    let := Stacks.Cech.sectionsModule f'' (Scheme.unitModule X'') ⊤
    let e' : Γ(Scheme.unitModule X'', ⊤) ≃ₗ[B] B := (pullbackUnitSectionsEquiv f'' g'').symm ≪≫ₗ e
    let : Module B Γ(X'', ⊤) := Stacks.Cech.sectionsModule f'' (Scheme.unitModule X'') ⊤
    exact RingHom.bijective_of_linearEquiv_self (Stacks.Cech.baseRingHom f'' ⊤).hom
      (fun c r => rfl) e'
  · obtain ⟨hP, hPb⟩ := isPerfect_and_hasTorAmplitude_tilde T hT1 hTb hTfree hTfin
    exact ⟨_, hP, ⟨b, hPb⟩, fun hsq =>
      nonempty_derivedPushforward_unit_iso_biprod_of_isPullback _ fA U hU hUaff eC hsq⟩

end Patch

section Global

open Stacks.AlgebraicGeometry.ProperFlatFamilyUnit

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
  (hfib : ∀ s : S, Function.Bijective ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
    (f.fiberToSpecResidueField s).appTop))

/-- Every point of a scheme lies in the image of an open immersion from the spectrum of a ring. -/
theorem exists_affine_chart (s : S) :
    ∃ (A : Type u) (_ : CommRing A) (j : Spec (.of A) ⟶ S) (_ : IsOpenImmersion j)
      (x : Spec (.of A)), j x = s := by
  obtain ⟨_, ⟨U, hU', rfl⟩, hsU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hU : IsAffineOpen U := hU'
  obtain ⟨x, hx⟩ : s ∈ Set.range hU.fromSpec := by rwa [IsAffineOpen.range_fromSpec]
  exact ⟨Γ(S, U), inferInstance, hU.fromSpec, inferInstance, x, hx⟩

/-- A point of `Spec A` outside `V(h)` is in the image of `Spec A_h`. -/
theorem mem_range_specMap_away {A : Type u} [CommRing A] (x : Spec (.of A)) {h : A}
    (hh : h ∉ x.asIdeal) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away h)))) := by
  have hx : x ∈ (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum A)) := hh
  rwa [← PrimeSpectrum.localization_away_comap_range (Localization.Away h) h] at hx

include hfib in
/-- **Part (b) of [Stacks, Tag 0E62], locally.** -/
theorem exists_openImmersion_splitting (s : S) :
    ∃ (V : Scheme.{u}) (ι : V ⟶ S) (_ : IsOpenImmersion ι) (P : DerivedCategory V.Modules),
      s ∈ Set.range ι ∧ RingedSpace.IsPerfect (X := V.toRingedSpace) P ∧
      (∃ b : ℤ, Stacks.Cohomology.TorAmplitude.HasTorAmplitude V.toRingedSpace P 1 b) ∧
      Nonempty ((Scheme.Modules.restrictFunctor ι).mapDerivedCategory.obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj (Scheme.unitModule X))) ≅
        ((DerivedCategory.singleFunctor V.Modules 0).obj (Scheme.unitModule V) ⊞ P :
          DerivedCategory V.Modules)) := by
  obtain ⟨A, _, j, _, x, hx⟩ := exists_affine_chart s
  have hA := IsPullback.of_hasPullback f j
  have : x.asIdeal.IsPrime := x.isPrime
  obtain ⟨h, hh, -, P, hP, hPb, hsplit⟩ := exists_away_patch f hfib j hA x.asIdeal
  let ι := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away h)))
  have hsqh := IsPullback.of_hasPullback (pullback.snd f j) ι
  have hout := hsqh.paste_horiz hA
  have : (Scheme.unitModule X).IsFinitePresentation :=
    inferInstanceAs (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation
  obtain ⟨eR⟩ := AlgebraicGeometry.ProperFlatRankOpen.openImmersionBaseChangeDerivedPushforward
    f (ι ≫ j) (pullback.snd (pullback.snd f j) ι) _ hout
    (FinitePresentation.mk inferInstance inferInstance inferInstance) inferInstance
    (Scheme.unitModule X) inferInstance
    (Stacks.Cohomology.PerfectPushforward.isFlatOver_structureModule f)
  obtain ⟨eS⟩ := hsplit hsqh
  obtain ⟨y, hy⟩ := mem_range_specMap_away x hh
  refine ⟨_, ι ≫ j, inferInstance, P, ⟨y, ?_⟩, hP, hPb, ⟨eR ≪≫
    (derivedPushforward (pullback.snd (pullback.snd f j) ι).toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (Scheme.Modules.pullbackUnitIso _)) ≪≫ eS⟩⟩
  rw [Scheme.Hom.comp_apply, hy, hx]

/-- If the structure map of `f'⁻¹W ⟶ Spec Γ(S', W)` on global functions is bijective, then
`f'.app W` is bijective. -/
private theorem bijective_app_of_bijective_baseRingHom_restrict {X' S' : Scheme.{u}} (f' : X' ⟶ S')
    {W : S'.Opens} (hW : IsAffineOpen W)
    (hb : Function.Bijective (Stacks.Cech.baseRingHom ((f' ∣_ W) ≫ hW.isoSpec.hom) ⊤)) :
    Function.Bijective (f'.app W) := by
  rw [baseRingHom_top_eq_globalRingHom] at hb
  have hiso : IsIso (Stacks.Cech.globalRingHom ((f' ∣_ W) ≫ hW.isoSpec.hom)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  unfold Stacks.Cech.globalRingHom at hiso
  rw [Scheme.Hom.comp_appTop, morphismRestrict_appTop] at hiso
  have : IsIso hW.isoSpec.hom.appTop := inferInstanceAs (IsIso (hW.isoSpec.hom.app ⊤))
  have : IsIso (hW.isoSpec.hom.appTop ≫ f'.app (W.ι ''ᵁ ⊤) ≫
      X'.presheaf.map (eqToHom (image_morphismRestrict_preimage f' W ⊤)).op) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ (toSpecΓ _) _ inferInstance hiso
  have : IsIso (f'.app (W.ι ''ᵁ ⊤) ≫
      X'.presheaf.map (eqToHom (image_morphismRestrict_preimage f' W ⊤)).op) :=
    IsIso.of_isIso_comp_left (hW.isoSpec.hom.appTop) _
  have : IsIso (f'.app (W.ι ''ᵁ ⊤)) := IsIso.of_isIso_comp_right _
    (X'.presheaf.map (eqToHom (image_morphismRestrict_preimage f' W ⊤)).op)
  rw [← Scheme.Opens.ι_image_top W]
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

include hfib in
/-- **The structure map is bijective over small affine opens of any base change.** -/
theorem exists_nhds_bijective_app {X' S' : Scheme.{u}} {g : S' ⟶ S} {f' : X' ⟶ S'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (x : S') :
    ∃ O : S'.Opens, x ∈ O ∧ ∀ W : S'.Opens, IsAffineOpen W → W ≤ O →
      Function.Bijective (f'.app W) := by
  obtain ⟨A, _, j, _, x0, hx0⟩ := exists_affine_chart (g x)
  have hA := IsPullback.of_hasPullback f j
  have : x0.asIdeal.IsPrime := x0.isPrime
  obtain ⟨h, hh, ha, -⟩ := exists_away_patch f hfib j hA x0.asIdeal
  let ι := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away h)))
  let jh := ι ≫ j
  refine ⟨g ⁻¹ᵁ jh.opensRange, ?_, fun W hW hWO => ?_⟩
  · obtain ⟨y, hy⟩ := mem_range_specMap_away x0 hh
    change g x ∈ Set.range jh
    exact ⟨y, by rw [Scheme.Hom.comp_apply, hy, hx0]⟩
  · let iW := hW.fromSpec
    have hrange : Set.range (iW ≫ g) ⊆ Set.range jh := by
      rintro _ ⟨y, rfl⟩
      have hy : iW y ∈ W := by
        rw [← SetLike.mem_coe, ← hW.range_fromSpec]
        exact ⟨y, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hWO hy
    let lift := IsOpenImmersion.lift jh (iW ≫ g) hrange
    have hlift : lift ≫ jh = iW ≫ g := IsOpenImmersion.lift_fac _ _ _
    let ψ := Spec.preimage lift
    let φ : A →+* Γ(S', W) := ψ.hom.comp (algebraMap A (Localization.Away h))
    have hφ : IsUnit (φ h) := (IsLocalization.Away.algebraMap_isUnit h).map ψ.hom
    have hbase : iW ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ j := by
      rw [← hlift, ← Spec.map_preimage lift]
      change Spec.map ψ ≫ ι ≫ j = _
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    let k := (f' ⁻¹ᵁ W).ι
    let f'' := (f' ∣_ W) ≫ hW.isoSpec.hom
    have h2 : IsPullback (𝟙 (f' ⁻¹ᵁ W).toScheme) f'' (f' ∣_ W) hW.isoSpec.inv :=
      IsPullback.of_horiz_isIso ⟨by simp [f'']⟩
    have hk : IsPullback (𝟙 _ ≫ k) f'' f' (hW.isoSpec.inv ≫ W.ι) :=
      h2.paste_horiz (isPullback_morphismRestrict f' W).flip
    rw [Category.id_comp, IsAffineOpen.isoSpec_inv_ι] at hk
    have hout := hk.paste_horiz sq
    rw [hbase] at hout
    let g'' := hA.lift (k ≫ g') (f'' ≫ Spec.map (CommRingCat.ofHom φ))
      (by rw [hout.w]; simp only [f'', Category.assoc])
    have hsq'' : IsPullback g'' f'' (pullback.snd f j) (Spec.map (CommRingCat.ofHom φ)) :=
      IsPullback.of_right (by rwa [hA.lift_fst]) (hA.lift_snd _ _ _) hA
    exact bijective_app_of_bijective_baseRingHom_restrict f' hW (ha φ hφ hsq'')

include hfib in
/-- **Part (a) of [Stacks, Tag 0E62], after an arbitrary base change.** -/
theorem isIso_c_of_isPullback {X' S' : Scheme.{u}} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) : IsIso f'.c := by
  rw [isIso_c_iff]
  intro V
  have : Flat f' := MorphismProperty.of_isPullback sq inferInstance
  have : Surjective f := surjective_of_forall_isIso_fiber_unit f
    (fun s => (isIso_fiberToSpecResidueField_unit_iff f s).2 (hfib s))
  have : Surjective f' := MorphismProperty.of_isPullback sq inferInstance
  have hinj : ∀ U : S'.Opens, Function.Injective (f'.app U) :=
    injective_app_of_flat_of_surjective f'
  refine ⟨hinj V, ?_⟩
  let G : TopCat.Sheaf CommRingCat.{u} S' := (TopCat.Sheaf.pushforward _ f'.base).obj X'.sheaf
  let φ : S'.sheaf ⟶ G := ⟨f'.c⟩
  refine TopCat.Presheaf.app_surjective_of_injective_of_locally_surjective φ V
    (fun x _ => TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
      (f := φ.1) hinj x) (fun t x hx => ?_)
  obtain ⟨O, hxO, hO⟩ := exists_nhds_bijective_app f hfib sq x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWsub⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_inter hxO hx) (O ⊓ V).isOpen
  have hWV : W ≤ V := fun y hy => (hWsub hy).2
  obtain ⟨s, hs⟩ := (hO W hW fun y hy => (hWsub hy).1).2 (G.1.map (homOfLE hWV).op t)
  exact ⟨W, hxW, homOfLE hWV, s, hs⟩

end Global

section Main

open Stacks.AlgebraicGeometry.ProperFlatFamilyUnit

/-- **[Stacks, Tag 0E62].** Let `f : X ⟶ S` be a morphism of schemes which is proper, flat and of
finite presentation, and assume that for every `s ∈ S` the canonical map
`κ(s) → H⁰(X_s, 𝒪_{X_s})` is bijective. Then

* (a) `f_*𝒪_X = 𝒪_S`, and this holds after any base change: for every cartesian square
  `X' = X ×_S S'` the comparison `𝒪_{S'} ⟶ f'_*𝒪_{X'}` of sheaves of rings is an isomorphism;
* (b) locally on `S` we have `Rf_*𝒪_X ≅ 𝒪_S ⊕ P` in `D(𝒪_S)` with `P` perfect of Tor amplitude
  in `[1, ∞)`: every point of `S` lies in the image of an open immersion `ι : V ⟶ S` over which
  the restriction of `Rf_*𝒪_X` is isomorphic to `𝒪_V ⊕ P` with `P` a perfect object of `D(𝒪_V)`
  of Tor amplitude in `[1, b]` for some `b`. -/
@[stacks 0E62]
theorem properFlat_structureSheaf_splitting {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    (hfp : FinitePresentation f)
    (hfib : ∀ s : S, Function.Bijective ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
      (f.fiberToSpecResidueField s).appTop)) :
    (IsIso f.c ∧
      ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
        IsPullback g' f' f g → IsIso f'.c) ∧
    ∀ s : S, ∃ (V : Scheme.{u}) (ι : V ⟶ S) (_ : IsOpenImmersion ι)
      (P : DerivedCategory V.Modules),
      s ∈ Set.range ι ∧ RingedSpace.IsPerfect (X := V.toRingedSpace) P ∧
      (∃ b : ℤ, Stacks.Cohomology.TorAmplitude.HasTorAmplitude V.toRingedSpace P 1 b) ∧
      Nonempty ((Scheme.Modules.restrictFunctor ι).mapDerivedCategory.obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj (Scheme.unitModule X))) ≅
        ((DerivedCategory.singleFunctor V.Modules 0).obj (Scheme.unitModule V) ⊞ P :
          DerivedCategory V.Modules)) :=
  have : LocallyOfFinitePresentation f := hfp.1
  ⟨⟨isIso_c_of_isPullback f hfib
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 X) f f (𝟙 S)),
      fun _ _ _ sq => isIso_c_of_isPullback f hfib sq⟩,
    exists_openImmersion_splitting f hfib⟩

end Main

end Stacks.AlgebraicGeometry.ProperFlatStructureSheafSplitting

end
