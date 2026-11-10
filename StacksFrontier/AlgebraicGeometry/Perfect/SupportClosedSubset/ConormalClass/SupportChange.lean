module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.AugmentedLift
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedSectionsRestriction

/-!
# Changing the closed subset of the local cohomology

Let `X` be a ringed space and `T ⊆ T'` closed subsets.  A section supported on `T` is supported
on `T'`, so the sheaf `i_*ℋ_T(ℱ)` of sections supported on `T` is a subsheaf of `i_*ℋ_{T'}(ℱ)`,
naturally in `ℱ`.  Deriving this inclusion gives a transformation

`θ : i_* R𝓗_T ⟶ i_* R𝓗_{T'}`

compatible with the two maps to the identity of Stacks 0G72.  Over an open `U` with
`U ∩ T' ⊆ T` the two subsheaves agree, and so `θ` is invertible on cohomology sheaves after
restriction to `U`.

## Main definitions

* `Stacks.Perfect.ConormalClass.supportedSectionsInclusion`: the inclusion
  `i_*ℋ_T(ℱ) ⟶ i_*ℋ_{T'}(ℱ)`.
* `Stacks.Perfect.ConormalClass.supportChange`: the derived transformation `θ`.

## Main results

* `Stacks.Perfect.ConormalClass.supportChange_comp_counit`: `θ` is compatible with the maps to
  the identity.
* `Stacks.Perfect.ConormalClass.supportChange_comp`: `θ` is transitive.
* `Stacks.Perfect.ConormalClass.isIso_res_homology_supportChange`: `θ` is invertible on
  cohomology sheaves over an open meeting `T'` only inside `T`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.SupportedSections
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward
  derivedSupportedPushforwardUnit)

universe u

namespace Stacks.Perfect.ConormalClass

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The inclusion of the sheaves of supported sections -/

section Inclusion

variable (X : RingedSpace.{u, u}) {T T' : Set X.carrier} (hTT' : T ⊆ T')

/-- **The inclusion of the sections supported on `T` into the sections supported on `T'`.** -/
def supportedSectionsInclusion (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (supportedSectionsFunctor X T).obj M ⟶ (supportedSectionsFunctor X T').obj M :=
  ⟨PresheafOfModules.homMk
    { app := fun _ => AddCommGrpCat.ofHom <| AddMonoidHom.mk'
        (fun s => ⟨s.1, fun _ hx => ⟨hTT' (s.2 hx).1, (s.2 hx).2⟩⟩) (fun _ _ => rfl)
      naturality := fun _ _ _ => rfl }
    (fun _ _ _ => rfl)⟩

/-- The inclusion is compatible with the inclusions into the module. -/
@[reassoc (attr := simp)]
theorem supportedSectionsInclusion_comp_ι (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    supportedSectionsInclusion X hTT' M ≫ supportedSectionsSheafι T' M =
      supportedSectionsSheafι T M :=
  rfl

/-- The inclusion as a natural transformation. -/
def supportedSectionsInclusionNat :
    supportedSectionsFunctor X T ⟶ supportedSectionsFunctor X T' where
  app M := supportedSectionsInclusion X hTT' M
  naturality _ _ _ := rfl

/-- The inclusion for `T ⊆ T'` followed by the inclusion of the sections supported on `T'` into
the identity functor is the inclusion of the sections supported on `T`. -/
theorem supportedSectionsInclusionNat_comp :
    supportedSectionsInclusionNat X hTT' ≫ supportedSectionsSubsheafInclusion X T' =
      supportedSectionsSubsheafInclusion X T :=
  rfl

/-- For `T ⊆ T' ⊆ T''`, the inclusion for `T ⊆ T'` followed by the inclusion for `T' ⊆ T''` is
the inclusion for `T ⊆ T''`. -/
theorem supportedSectionsInclusionNat_trans {T'' : Set X.carrier} (hT'T'' : T' ⊆ T'') :
    supportedSectionsInclusionNat X hTT' ≫ supportedSectionsInclusionNat X hT'T'' =
      supportedSectionsInclusionNat X (hTT'.trans hT'T'') :=
  rfl

end Inclusion

/-! ### The derived transformation -/

section Derived

variable (X : RingedSpace.{u, u}) {T T' : Set X.carrier} (hT : IsClosed T) (hT' : IsClosed T')
  (hTT' : T ⊆ T')

/-- **The change of support `i_* R𝓗_T ⟶ i_* R𝓗_{T'}`** for `T ⊆ T'`, the derived inclusion of the
sections supported on `T` into those supported on `T'`. -/
def supportChange : derivedSupportedPushforward X T hT ⟶ derivedSupportedPushforward X T' hT' :=
  Functor.rightDerivedNatTrans _ _ (derivedSupportedPushforwardUnit X T hT)
    (derivedSupportedPushforwardUnit X T' hT')
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory (supportedSectionsInclusionNat X hTT')
      (ComplexShape.up ℤ)) DerivedCategory.Qh)

/-- The change of support is the derived inclusion. -/
theorem supportChange_fac :
    derivedSupportedPushforwardUnit X T hT ≫
        Functor.whiskerLeft DerivedCategory.Qh (supportChange X hT hT' hTT') =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory (supportedSectionsInclusionNat X hTT')
          (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        derivedSupportedPushforwardUnit X T' hT' :=
  Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

/-- **The change of support is compatible with the maps `i_* R𝓗_T ⟶ 𝟭` of Stacks 0G72.** -/
theorem supportChange_comp_counit :
    supportChange X hT hT' hTT' ≫
        derivedSupportedSectionsToId X T' (derivedSupportedPushforward X T' hT')
          (derivedSupportedPushforwardUnit X T' hT') =
      derivedSupportedSectionsToId X T (derivedSupportedPushforward X T hT)
        (derivedSupportedPushforwardUnit X T hT) := by
  refine Functor.rightDerived_ext _ (derivedSupportedPushforwardUnit X T hT)
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) _ _ _ ?_
  rw [Functor.whiskerLeft_comp, ← Category.assoc, supportChange_fac, Category.assoc,
    derivedSupportedSectionsToId_fac, derivedSupportedSectionsToId_fac, ← Category.assoc,
    ← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp,
    supportedSectionsInclusionNat_comp]

/-- **The change of support is transitive.** -/
theorem supportChange_comp {T'' : Set X.carrier} (hT'' : IsClosed T'') (hT'T'' : T' ⊆ T'') :
    supportChange X hT hT' hTT' ≫ supportChange X hT' hT'' hT'T'' =
      supportChange X hT hT'' (hTT'.trans hT'T'') := by
  rw [supportChange, supportChange, supportChange, Functor.rightDerivedNatTrans_comp,
    ← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp,
    supportedSectionsInclusionNat_trans]

end Derived

/-! ### Over an open meeting `T'` only inside `T` -/

section Restriction

variable {X : Scheme.{u}} {T T' : Set X} (hTT' : T ⊆ T') (U : X.Opens)
  (hU : ∀ x ∈ U, x ∈ T' → x ∈ T)

include hU in
/-- **Over an open meeting `T'` only inside `T`, the sections supported on `T` and on `T'`
agree**: the restriction of the inclusion is an isomorphism. -/
theorem isIso_res_supportedSectionsInclusion (M : X.Modules) :
    IsIso ((res U).map (supportedSectionsInclusion X.toRingedSpace hTT' M)) := by
  obtain ⟨e, he⟩ := Stacks.Perfect.SupportedSectionsRestriction.exists_iso_of_injective_same_range
    ((res U).map (supportedSectionsSheafι T M)) ((res U).map (supportedSectionsSheafι T' M))
    (fun V => (supportedSectionsSheaf T M).2.2.1 (op (U.ι ''ᵁ unop V)))
    (fun V => (supportedSectionsSheaf T' M).2.2.1 (op (U.ι ''ᵁ unop V)))
    (fun V => by
      ext s
      refine (mem_supportedSectionsSheafι_range_iff T M (op (U.ι ''ᵁ unop V)) s).trans ?_
      refine Iff.trans ?_
        (mem_supportedSectionsSheafι_range_iff T' M (op (U.ι ''ᵁ unop V)) s).symm
      refine ⟨fun h x hx => ⟨hTT' (h hx).1, (h hx).2⟩,
        fun h x hx => ⟨hU x ?_ (h hx).1, (h hx).2⟩⟩
      obtain ⟨y, -, rfl⟩ := (h hx).2
      exact y.2)
  have heq : (res U).map (supportedSectionsInclusion X.toRingedSpace hTT' M) = e.hom := by
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
    refine (supportedSectionsSheaf T' M).2.2.1 (op (U.ι ''ᵁ V)) ?_
    exact (congrArg (fun φ => (φ.app V : _ → _) s) he).symm
  rw [heq]
  exact e.isIso_hom

/-- A map of complexes which is an isomorphism after restriction to an open in every degree is an
isomorphism on cohomology sheaves after restriction to that open. -/
theorem isIso_res_homologyMap_of_isIso {K L : CochainComplex X.Modules ℤ} (φ : K ⟶ L)
    (hφ : ∀ n, IsIso ((res U).map (φ.f n))) (p : ℤ) :
    IsIso ((res U).map (HomologicalComplex.homologyMap φ p)) := by
  set f := (res U).mapShortComplex.map
      ((HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℤ) p).map φ)
  have h1 : IsIso f.τ₁ := hφ _
  have h2 : IsIso f.τ₂ := hφ _
  have h3 : IsIso f.τ₃ := hφ _
  have hsc : IsIso f := ShortComplex.isIso_of_isIso _
  have : (res U).map (HomologicalComplex.homologyMap φ p) =
      ((K.sc p).mapHomologyIso (res U)).inv ≫
        ShortComplex.homologyMap ((res U).mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℤ) p).map φ)) ≫
          ((L.sc p).mapHomologyIso (res U)).hom := by
    rw [ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℤ) p).map φ) (res U),
      Iso.inv_hom_id_assoc]
    rfl
  rw [this]
  exact IsIso.comp_isIso' (Iso.isIso_inv _)
    (IsIso.comp_isIso' (ShortComplex.isIso_homologyMap_of_iso f) (Iso.isIso_hom _))

include hU in
/-- Over such an open, the inclusion of the complexes of supported sections of a complex is an
isomorphism on cohomology sheaves. -/
theorem isIso_res_homologyMap_supportedSectionsInclusion (J : CochainComplex X.Modules ℤ)
    (p : ℤ) :
    IsIso ((res U).map (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (supportedSectionsInclusionNat X.toRingedSpace hTT')
        (ComplexShape.up ℤ)).app J) p)) :=
  isIso_res_homologyMap_of_isIso U
    (K := ((supportedSectionsFunctor X.toRingedSpace T).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J)
    (L := ((supportedSectionsFunctor X.toRingedSpace T').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J)
    ((NatTrans.mapHomologicalComplex (supportedSectionsInclusionNat X.toRingedSpace hTT')
        (ComplexShape.up ℤ)).app J)
    (fun n => isIso_res_supportedSectionsInclusion hTT' U hU (J.X n)) p

/-- A map of complexes which is an isomorphism after restriction to an open in every degree
induces, through the homotopy category, an isomorphism on cohomology sheaves in the derived
category after restriction to that open. -/
theorem isIso_res_homology_Qh_map_of_isIso {K L : CochainComplex X.Modules ℤ} (φ : K ⟶ L)
    (hφ : ∀ n, IsIso ((res U).map (φ.f n))) (p : ℤ) :
    IsIso ((res U).map ((DerivedCategory.homologyFunctor X.Modules p).map
      (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map φ)))) := by
  set g := (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map φ
  have e1 := NatIso.naturality_2 (DerivedCategory.homologyFunctorFactorsh X.Modules p) g
  have e2 := NatIso.naturality_2
    (HomotopyCategory.homologyFunctorFactors X.Modules (ComplexShape.up ℤ) p) φ
  rw [Functor.comp_map] at e1 e2
  rw [← e1, ← e2]
  have hm : IsIso ((res U).map
      ((HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) p).map φ)) :=
    isIso_res_homologyMap_of_isIso U φ hφ p
  simp only [Functor.map_comp]
  infer_instance

include hU in
/-- **Over an open meeting `T'` only inside `T`, the change of support is an isomorphism on
cohomology sheaves**, at a K-injective complex. -/
theorem isIso_res_homology_supportChange_of_isKInjective (hT : IsClosed T) (hT' : IsClosed T')
    (J : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    [J.IsKInjective] (p : ℤ) :
    IsIso ((res U).map ((DerivedCategory.homologyFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) p).map
      ((supportChange X.toRingedSpace hT hT' hTT').app
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J))))) := by
  let G := DerivedCategory.homologyFunctor
    (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) p ⋙ res U
  set Jh := (HomotopyCategory.quotient
    (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (ComplexShape.up ℤ)).obj J
  have hα : IsIso ((derivedSupportedPushforwardUnit X.toRingedSpace T hT).app Jh) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ J
  have hα' : IsIso ((derivedSupportedPushforwardUnit X.toRingedSpace T' hT').app Jh) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ J
  have hfac := Functor.rightDerivedNatTrans_app _ _
    (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
    (derivedSupportedPushforwardUnit X.toRingedSpace T' hT')
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory
      (supportedSectionsInclusionNat X.toRingedSpace hTT') (ComplexShape.up ℤ))
      DerivedCategory.Qh)
    Jh
  have hm : IsIso (G.map ((Functor.whiskerRight (NatTrans.mapHomotopyCategory
      (supportedSectionsInclusionNat X.toRingedSpace hTT') (ComplexShape.up ℤ))
        DerivedCategory.Qh).app Jh)) :=
    isIso_res_homology_Qh_map_of_isIso U
      ((NatTrans.mapHomologicalComplex (supportedSectionsInclusionNat X.toRingedSpace hTT')
        (ComplexShape.up ℤ)).app J)
      (fun n => isIso_res_supportedSectionsInclusion hTT' U hU (J.X n)) p
  have h1 := congrArg G.map hfac
  rw [G.map_comp, G.map_comp] at h1
  have h2 : IsIso (G.map ((derivedSupportedPushforwardUnit X.toRingedSpace T hT).app Jh) ≫
      G.map ((supportChange X.toRingedSpace hT hT' hTT').app (DerivedCategory.Qh.obj Jh))) := by
    rw [supportChange, h1]
    exact IsIso.comp_isIso' hm inferInstance
  change IsIso
    (G.map ((supportChange X.toRingedSpace hT hT' hTT').app (DerivedCategory.Qh.obj Jh)))
  exact IsIso.of_isIso_comp_left
    (G.map ((derivedSupportedPushforwardUnit X.toRingedSpace T hT).app Jh)) _

include hU in
/-- **Over an open meeting `T'` only inside `T`, the change of support is an isomorphism on
cohomology sheaves.** -/
theorem isIso_res_homology_supportChange (hT : IsClosed T) (hT' : IsClosed T')
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (p : ℤ) :
    IsIso ((res U).map ((DerivedCategory.homologyFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) p).map
      ((supportChange X.toRingedSpace hT hT' hTT').app K))) := by
  let G := DerivedCategory.homologyFunctor
    (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) p ⋙ res U
  obtain ⟨J, q, hJ, hq⟩ :=
    Stacks.Cohomology.SupportedComplexes.exists_isKInjective_quasiIso_moduleSheaves
      X.toRingedSpace (DerivedCategory.Q.objPreimage K)
  have hQq : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) q).2 hq
  let e : K ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J) :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫ asIso (DerivedCategory.Q.map q) ≪≫
      ((DerivedCategory.quotientCompQhIso _).app J).symm
  have heq : (supportChange X.toRingedSpace hT hT' hTT').app K =
      (derivedSupportedPushforward X.toRingedSpace T hT).map e.hom ≫
        (supportChange X.toRingedSpace hT hT' hTT').app _ ≫
          (derivedSupportedPushforward X.toRingedSpace T' hT').map e.inv := by
    rw [← Category.assoc, (supportChange X.toRingedSpace hT hT' hTT').naturality e.hom,
      Category.assoc, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  change IsIso (G.map ((supportChange X.toRingedSpace hT hT' hTT').app K))
  rw [heq, G.map_comp, G.map_comp]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso'
    (isIso_res_homology_supportChange_of_isKInjective hTT' U hU hT hT' J p) inferInstance)

end Restriction

/-! ### Compatibility with the canonical maps of supported complexes -/

section Lift

variable {X : Scheme.{u}} {F : X.Modules} (L : CochainComplex X.Modules ℕ) (a : L.X 0 ⟶ F)
  {T T' : Set X} (hT : IsClosed T) (hT' : IsClosed T') (hTT' : T ⊆ T')
  (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T
    (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)))

include hTT' in
/-- A complex supported on `T` is supported on any larger `T'`. -/
theorem cohomologySupportedOn_mono' {K : DerivedCategory X.Modules}
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T K) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T' K :=
  fun i x hx => hK i x fun h => hx (hTT' h)

/-- **The change of support carries the canonical map of a complex supported on `T` to its
canonical map as a complex supported on `T'`.** -/
theorem augLift_comp_supportChange :
    augLift L a hT hL ≫ (supportChange X.toRingedSpace hT hT' hTT').app
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) =
      augLift L a hT' (cohomologySupportedOn_mono' hTT' hL) := by
  have hL' := cohomologySupportedOn_mono' hTT' hL
  have hc :=
    congrArg (fun τ => τ.app (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat)))
    (supportChange_comp_counit X.toRingedSpace hT hT' hTT')
  simp only [NatTrans.comp_app] at hc
  refine ((@asIso _ _ _ _ _ (isIso_supportPushCounit_of_supported L hT hL)).cancel_iso_hom_left
    _ _).mp ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun ψ => ψ ≫ (supportChange X.toRingedSpace hT hT' hTT').app
    ((DerivedCategory.singleFunctor X.Modules 0).obj F))
    (supportPushCounit_comp_augLift L a hT hL)).trans ?_
  refine ((supportChange X.toRingedSpace hT hT' hTT').naturality (augQ L a)).trans ?_
  refine (congrArg (fun ψ => (supportChange X.toRingedSpace hT hT' hTT').app _ ≫ ψ)
    (supportPushCounit_comp_augLift L a hT' hL').symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (fun ψ => ψ ≫ augLift L a hT' hL') hc

/-- The change of support on the cohomology sheaves of `i_* R𝓗(ℱ)`. -/
def supportChangeH (F : X.Modules) (p : ℤ) :
    Stacks.Perfect.SupportedFraction.supportCohomologySheaf hT F p ⟶
      Stacks.Perfect.SupportedFraction.supportCohomologySheaf hT' F p :=
  (DerivedCategory.homologyFunctor X.Modules p).map
    ((supportChange X.toRingedSpace hT hT' hTT').app
      ((DerivedCategory.singleFunctor X.Modules 0).obj F))

/-- **The change of support carries the class of a cocycle of a complex supported on `T` to its
class as a complex supported on `T'`.** -/
theorem augClass_comp_supportChangeH (p : ℕ) {M : X.Modules} (u : M ⟶ L.X p)
    (hu : u ≫ L.d p (p + 1) = 0) :
    augClass L a hT hL p u hu ≫ supportChangeH hT hT' hTT' F (p : ℤ) =
      augClass L a hT' (cohomologySupportedOn_mono' hTT' hL) p u hu := by
  refine (Category.assoc _ _ _).trans (congrArg (fun ψ => _ ≫ ψ) ?_)
  refine (Category.assoc _ _ _).trans
    (congrArg (fun ψ => (derivedHomologyExtendIso L p).inv ≫ ψ) ?_)
  exact ((DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map_comp _ _).symm.trans
    (congrArg (DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map
      (augLift_comp_supportChange L a hT hT' hTT' hL))

/-- The change of support on cohomology sheaves is transitive. -/
theorem supportChangeH_comp {T'' : Set X} (hT'' : IsClosed T'') (hT'T'' : T' ⊆ T'')
    (F : X.Modules) (p : ℤ) :
    supportChangeH hT hT' hTT' F p ≫ supportChangeH hT' hT'' hT'T'' F p =
      supportChangeH hT hT'' (hTT'.trans hT'T'') F p :=
  ((DerivedCategory.homologyFunctor X.Modules p).map_comp _ _).symm.trans
    (congrArg (DerivedCategory.homologyFunctor X.Modules p).map
      (congrArg (fun τ => τ.app ((DerivedCategory.singleFunctor X.Modules 0).obj F))
        (supportChange_comp X.toRingedSpace hT hT' hTT' hT'' hT'T'')))

end Lift

end Stacks.Perfect.ConormalClass
