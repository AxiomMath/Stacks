module

public import StacksFrontier.Homology.Perfect.NilpotentLifting
public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayamaModels
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsModelComp
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# Lifting a finite projective complex across a henselian surjection, in any model

Let `p : R →+* S` be a surjection of commutative rings whose kernel `I` makes `(R, I)` a
henselian pair, and let `K` be a pseudo-coherent object of `D(R)`. Stacks 0BCE lifts a bounded
above complex `F` of finite projective `S`-modules representing `K ⊗ᴸ_R S` to a bounded above
complex `P` of finite projective `R`-modules representing `K`. The form in which the proof of
Stacks 0DL7 uses it is sharper: for a prescribed identification `e : F ≅ K ⊗ᴸ_R S`, the lift comes
with `ψ : P ⊗_R S ≅ F` and `P ≅ K` under which `e` is the derived extension of scalars of `P ≅ K`.

`StacksDraft.Perfect.exists_boundedAbove_finiteProjective_lift_representing_iso_of_datum` proves
this for the quotient map `R → R ⧸ I` at the standard models of the derived categories. This file
removes both restrictions: the models of `D(R)` and `D(S)` are arbitrary, derived extension of
scalars is any total left derived functor of degreewise extension of scalars, and `p` is any
surjection.

## Main results

* `StacksDraft.Perfect.exists_finiteProjective_lift_iso_quotient_of_isLeftDerivedFunctor`: the
  statement for `R → R ⧸ I` in arbitrary models.
* `StacksDraft.Perfect.exists_finiteProjective_lift_iso_of_surjective`: the statement for an
  arbitrary surjection `p` in arbitrary models.

## Implementation notes

The model change compares the given derived functor `G` with the chosen one `T` at the standard
models through the comparison equivalences `Ψ` of `D(R)` and `J` of `D(R ⧸ I)`: the functor
`Ψ ⋙ T ⋙ J⁻¹` maps to `G` by the universal property of `G`, and the map is invertible because
both are computed by K-flat complexes.

The change of ring replaces `S` by `R ⧸ I` through restriction of scalars along the isomorphism
`R ⧸ I ≃+* S`, which is an exact equivalence, and identifies `S ⊗_R - `, restricted to `R ⧸ I`,
with `R ⧸ I ⊗_R -` by conjugating the composite of restrictions of scalars.

## References

* [Stacks Project, Tag 0BCE](https://stacks.math.columbia.edu/tag/0BCE)
* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars
  StacksDraft.DerivedModel StacksDraft.PseudoCoherence

universe w w' w'' u

namespace StacksDraft.Perfect

section Quotient

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The chosen derived extension of scalars along `R → R ⧸ I` at the standard models. -/
abbrev standardQuotientDerivedExtension :
    @TotalDerivedExtensionScalars.{u, u, u} R (R ⧸ I) _ _ (Ideal.Quotient.mk I)
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) :=
  @totalDerivedExtensionScalars.{u, u, u} R (R ⧸ I) _ _ (Ideal.Quotient.mk I)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)

/-- The functor of `standardQuotientDerivedExtension`, with both models spelled out. -/
abbrev standardQuotientDerivedExtensionFunctor :=
  @TotalDerivedExtensionScalars.functor R (R ⧸ I) _ _ (Ideal.Quotient.mk I)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (standardQuotientDerivedExtension I)

/-- The comparison of `standardQuotientDerivedExtension`, with both models spelled out. -/
abbrev standardQuotientDerivedExtensionComparison :
    @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (ModuleCat.{u} R)) ⋙
        standardQuotientDerivedExtensionFunctor I ⟶
      (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
        @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (ModuleCat.{u} (R ⧸ I))) :=
  @TotalDerivedExtensionScalars.comparison R (R ⧸ I) _ _ (Ideal.Quotient.mk I)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (standardQuotientDerivedExtension I)

/-- The comparison of `standardQuotientDerivedExtension` is invertible at a K-flat complex. -/
theorem isIso_standardQuotientDerivedExtensionComparison_app
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (hM : CochainComplex.KFlat.{u, u} M) :
    IsIso ((standardQuotientDerivedExtensionComparison I).app M) :=
  @TotalDerivedExtensionScalars.comparison_isIso_of_kFlat R (R ⧸ I) _ _ (Ideal.Quotient.mk I)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (standardQuotientDerivedExtension I) M hM

variable [h₁ : HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [h₂ : HasDerivedCategory.{w'} (ModuleCat.{u} (R ⧸ I))]

/-- The chosen derived extension of scalars along `R → R ⧸ I` at the standard models, read in the
given models through the comparison equivalences. -/
abbrev transportedQuotientDerivedExtension :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} (R ⧸ I)) :=
  (modelEquiv h₁ (HasDerivedCategory.standard _)).functor ⋙
    standardQuotientDerivedExtensionFunctor I ⋙
      (modelEquiv h₂ (HasDerivedCategory.standard _)).inverse

/-- The comparison of `transportedQuotientDerivedExtension` with degreewise extension of
scalars: the comparison of the chosen model, conjugated by the comparisons of the models. -/
def transportedQuotientDerivedExtensionComparison :
    DerivedCategory.Q ⋙ transportedQuotientDerivedExtension I ⟶
      (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q where
  app X := (modelEquiv h₂ (HasDerivedCategory.standard _)).inverse.map
      ((standardQuotientDerivedExtensionFunctor I).map
          ((modelCompQIso h₁ (HasDerivedCategory.standard _)).hom.app X) ≫
        (standardQuotientDerivedExtensionComparison I).app X) ≫
    (modelInverseCompQIso h₂ (HasDerivedCategory.standard _)).hom.app
      (((ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X)
  naturality X Y f := by
    have h₁' : (modelEquiv h₁ (HasDerivedCategory.standard _)).functor.map
          (DerivedCategory.Q.map f) ≫
        (modelCompQIso h₁ (HasDerivedCategory.standard _)).hom.app Y =
        (modelCompQIso h₁ (HasDerivedCategory.standard _)).hom.app X ≫
          (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (ModuleCat.{u} R))).map f :=
      (modelCompQIso h₁ (HasDerivedCategory.standard _)).hom.naturality f
    have h₂' : (standardQuotientDerivedExtensionFunctor I).map
          ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (ModuleCat.{u} R))).map f) ≫
        (standardQuotientDerivedExtensionComparison I).app Y =
        (standardQuotientDerivedExtensionComparison I).app X ≫
          (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (ModuleCat.{u} (R ⧸ I)))).map
            (((ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f) :=
      (standardQuotientDerivedExtensionComparison I).naturality f
    have h₃' := (modelInverseCompQIso h₂ (HasDerivedCategory.standard _)).hom.naturality
      (((ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)
    have key : (standardQuotientDerivedExtensionFunctor I).map
          ((modelEquiv h₁ (HasDerivedCategory.standard _)).functor.map (DerivedCategory.Q.map f)) ≫
        ((standardQuotientDerivedExtensionFunctor I).map
            ((modelCompQIso h₁ (HasDerivedCategory.standard _)).hom.app Y) ≫
          (standardQuotientDerivedExtensionComparison I).app Y) =
        ((standardQuotientDerivedExtensionFunctor I).map
            ((modelCompQIso h₁ (HasDerivedCategory.standard _)).hom.app X) ≫
          (standardQuotientDerivedExtensionComparison I).app X) ≫
          (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (ModuleCat.{u} (R ⧸ I)))).map
            (((ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f) := by
      rw [← Category.assoc, ← Functor.map_comp, h₁', Functor.map_comp, Category.assoc, h₂',
        Category.assoc]
    have key' := congrArg (fun g ↦ (modelEquiv h₂ (HasDerivedCategory.standard _)).inverse.map g ≫
      (modelInverseCompQIso h₂ (HasDerivedCategory.standard _)).hom.app
        (((ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Y)) key
    simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc] at key' h₃' ⊢
    rw [key', h₃']

/-- The value of `transportedQuotientDerivedExtensionComparison` at a cochain complex. -/
theorem transportedQuotientDerivedExtensionComparison_app
    (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (transportedQuotientDerivedExtensionComparison I).app X =
      (modelEquiv h₂ (HasDerivedCategory.standard _)).inverse.map
          ((standardQuotientDerivedExtensionFunctor I).map
              ((modelCompQIso h₁ (HasDerivedCategory.standard _)).hom.app X) ≫
            (standardQuotientDerivedExtensionComparison I).app X) ≫
        (modelInverseCompQIso h₂ (HasDerivedCategory.standard _)).hom.app
          (((ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) :=
  rfl

/-- `transportedQuotientDerivedExtensionComparison` is invertible at a K-flat complex. -/
theorem isIso_transportedQuotientDerivedExtensionComparison_app
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (hM : CochainComplex.KFlat.{u, u} M) :
    IsIso ((transportedQuotientDerivedExtensionComparison I).app M) := by
  have hT := isIso_standardQuotientDerivedExtensionComparison_app I M hM
  have h : IsIso ((standardQuotientDerivedExtensionFunctor I).map
      ((modelCompQIso h₁ (HasDerivedCategory.standard _)).hom.app M) ≫
        (standardQuotientDerivedExtensionComparison I).app M) :=
    IsIso.comp_isIso' inferInstance hT
  rw [transportedQuotientDerivedExtensionComparison_app]
  infer_instance

variable (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} (R ⧸ I)))
  (β : DerivedCategory.Q ⋙ G ⟶
    (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]

/-- The comparison of the transported chosen derived extension of scalars with `G`, from the
universal property of `G`. -/
def transportedQuotientDerivedExtensionLift : transportedQuotientDerivedExtension I ⟶ G :=
  G.leftDerivedLift β (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _
    (transportedQuotientDerivedExtensionComparison I)

/-- The defining equation of `transportedQuotientDerivedExtensionLift`. -/
@[reassoc]
theorem transportedQuotientDerivedExtensionLift_fac (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (transportedQuotientDerivedExtensionLift I G β).app (DerivedCategory.Q.obj X) ≫ β.app X =
      (transportedQuotientDerivedExtensionComparison I).app X :=
  G.leftDerived_fac_app β (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _
    (transportedQuotientDerivedExtensionComparison I) X

/-- `transportedQuotientDerivedExtensionLift` is an isomorphism. -/
instance isIso_transportedQuotientDerivedExtensionLift :
    IsIso (transportedQuotientDerivedExtensionLift I G β) := by
  refine StacksDraft.DerivedExtensionScalarsModelComp.isIso_of_isIso_app_kFlat.{u, u, w} _ ?_
  intro M hM
  let : (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (Ideal.Quotient.mk I)).left_adjoint_additive
  have hβ : IsIso (β.app M) :=
    CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{u, u, u}
      (Ideal.Quotient.mk I) G β M hM
  have hc := isIso_transportedQuotientDerivedExtensionComparison_app I M hM
  rw [← transportedQuotientDerivedExtensionLift_fac I G β M] at hc
  exact IsIso.of_isIso_comp_right _ (β.app M)

/-- **Stacks 0BCE with a prescribed identification, for `R → R ⧸ I` in arbitrary models.** Let
`(R, I)` be a henselian pair, `G` any total left derived functor of degreewise extension of
scalars `D(R) ⥤ D(R ⧸ I)`, `K` a pseudo-coherent object of `D(R)`, and `e : E ≅ G K` an
identification with a bounded above complex of finite projective `R ⧸ I`-modules. Then there are
a bounded above complex `P` of finite projective `R`-modules, an isomorphism of complexes
`eRed : P ⊗_R R ⧸ I ≅ E` and an isomorphism `eK : P ≅ K` in `D(R)` such that the comparison of
`G` at `P`, followed by `eRed` and `e`, is `G eK`. -/
theorem exists_finiteProjective_lift_iso_quotient_of_isLeftDerivedFunctor
    (hI : HenselianPair R I) (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsPseudoCoherentIn K)
    (E : CochainComplex (ModuleCat.{u} (R ⧸ I)) ℤ) (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i, Module.Finite (R ⧸ I) (E.X i) ∧ Module.Projective (R ⧸ I) (E.X i))
    (e : DerivedCategory.Q.obj E ≅ G.obj K) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧ (∃ b, P.IsStrictlyLE b) ∧
      ∃ eRed : ((ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ≅ E,
      ∃ eK : DerivedCategory.Q.obj P ≅ K,
        β.app P ≫ DerivedCategory.Q.map eRed.hom ≫ e.hom = G.map eK.hom := by
  have hK₀ := (isPseudoCoherentIn_iff_isPseudoCoherent K (HasDerivedCategory.standard _)).1 hK
  let e₀ : (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (ModuleCat.{u} (R ⧸ I)))).obj E ≅
      (standardQuotientDerivedExtensionFunctor I).obj
        ((modelEquiv h₁ (HasDerivedCategory.standard _)).functor.obj K) :=
    (modelEquiv h₂ (HasDerivedCategory.standard _)).inverse.preimageIso
      ((modelInverseCompQIso h₂ (HasDerivedCategory.standard _)).app E ≪≫ e ≪≫
        (asIso ((transportedQuotientDerivedExtensionLift I G β).app K)).symm)
  have he₀ : (modelEquiv h₂ (HasDerivedCategory.standard _)).inverse.map e₀.hom =
      (modelInverseCompQIso h₂ (HasDerivedCategory.standard _)).hom.app E ≫ e.hom ≫
        inv ((transportedQuotientDerivedExtensionLift I G β).app K) := by
    simp [e₀]
  obtain ⟨P, hP, hPbdd, eRed, eK₀, hcompat⟩ :=
    exists_boundedAbove_finiteProjective_lift_representing_iso_of_datum.{u, u} I
      (standardQuotientDerivedExtension I) _ E hEbdd hEterms e₀ hK₀ hI
  let eK : DerivedCategory.Q.obj P ≅ K :=
    (modelEquiv h₁ (HasDerivedCategory.standard _)).functor.preimageIso
    ((modelCompQIso h₁ (HasDerivedCategory.standard _)).app P ≪≫ eK₀)
  have heK : (transportedQuotientDerivedExtension I).map eK.hom =
      (modelEquiv h₂ (HasDerivedCategory.standard _)).inverse.map
        ((standardQuotientDerivedExtensionFunctor I).map
          ((modelCompQIso h₁ (HasDerivedCategory.standard _)).hom.app P ≫ eK₀.hom)) := by
    simp [eK]
  have hι : (modelEquiv h₂ (HasDerivedCategory.standard _)).inverse.map
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (ModuleCat.{u} (R ⧸ I)))).map
          eRed.hom) ≫ (modelInverseCompQIso h₂ (HasDerivedCategory.standard _)).hom.app E =
      (modelInverseCompQIso h₂ (HasDerivedCategory.standard _)).hom.app
          (((ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫ DerivedCategory.Q.map eRed.hom :=
    (modelInverseCompQIso h₂ (HasDerivedCategory.standard _)).hom.naturality eRed.hom
  have hcompat' : (standardQuotientDerivedExtensionComparison I).app P ≫
      (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard (ModuleCat.{u} (R ⧸ I)))).map
        eRed.hom ≫ e₀.hom = (standardQuotientDerivedExtensionFunctor I).map eK₀.hom :=
    hcompat
  refine ⟨P, hP, hPbdd, eRed, eK, ?_⟩
  rw [← cancel_epi ((transportedQuotientDerivedExtensionLift I G β).app (DerivedCategory.Q.obj P)),
    ← (transportedQuotientDerivedExtensionLift I G β).naturality eK.hom,
    transportedQuotientDerivedExtensionLift_fac_assoc,
    transportedQuotientDerivedExtensionComparison_app, heK,
    Functor.map_comp (standardQuotientDerivedExtensionFunctor I), ← hcompat']
  simp only [Functor.map_comp, Category.assoc, he₀, IsIso.inv_hom_id, Category.comp_id,
    reassoc_of% hι]

end Quotient

section Surjection

variable {R S : Type u} [CommRing R] [CommRing S] (p : R →+* S) (hp : Function.Surjective p)

/-- Extension of scalars along a surjection `p : R →+* S`, followed by restriction of scalars
along `R ⧸ ker p ≃+* S`, is extension of scalars along `R → R ⧸ ker p`: the two functors have
the same right adjoint, restriction of scalars along `R → R ⧸ ker p`. -/
def extendScalarsRestrictQuotientKerIso :
    ModuleCat.extendScalars.{u, u, u} p ⋙
        ModuleCat.restrictScalars.{u} (RingHom.quotientKerEquivOfSurjective hp).toRingHom ≅
      ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk (RingHom.ker p)) :=
  (conjugateIsoEquiv
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (Ideal.Quotient.mk (RingHom.ker p)))
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} p).comp
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (RingHom.quotientKerEquivOfSurjective hp)).toAdjunction)).symm
    (ModuleCat.restrictScalarsComp'.{u} p (RingHom.quotientKerEquivOfSurjective hp).symm.toRingHom
      (Ideal.Quotient.mk (RingHom.ker p)) (RingHom.quotientKerEquivOfSurjective_symm_comp hp).symm)

/-- Restriction of scalars along a ring isomorphism carries finite modules to finite modules. -/
theorem finite_restrictScalars_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (ε : A ≃+* B)
    (M : ModuleCat.{u} B) [Module.Finite B M] :
    Module.Finite A ((ModuleCat.restrictScalars.{u} ε.toRingHom).obj M) :=
  Module.Finite.of_surjective (σ := ε.symm.toRingHom)
    (M := M) (P := (ModuleCat.restrictScalars.{u} ε.toRingHom).obj M)
    { toFun := fun m ↦ m
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun b m ↦ by
        change b • m = ε (ε.symm b) • m
        rw [ε.apply_symm_apply] }
    (fun m ↦ ⟨m, rfl⟩)

/-- Restriction of scalars along a ring isomorphism carries projective modules to projective
modules. -/
theorem projective_restrictScalars_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (ε : A ≃+* B) (M : ModuleCat.{u} B) [Module.Projective B M] :
    Module.Projective A ((ModuleCat.restrictScalars.{u} ε.toRingHom).obj M) := by
  have : Projective M := inferInstance
  have : Projective ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv ε).functor.obj M) :=
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv ε).map_projective_iff M).2 inferInstance
  change Module.Projective A ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv ε).functor.obj M)
  infer_instance

/-- Restriction of scalars along `R ⧸ ker p ≃+* S`. -/
abbrev quotientKerRestriction : ModuleCat.{u} S ⥤ ModuleCat.{u} (R ⧸ RingHom.ker p) :=
  ModuleCat.restrictScalars.{u} (RingHom.quotientKerEquivOfSurjective hp).toRingHom

/-- `extendScalarsRestrictQuotientKerIso` applied degreewise to cochain complexes. -/
def quotientKerExtensionComplexIso :
    (ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (quotientKerRestriction p hp).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk (RingHom.ker p))).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  letI : (ModuleCat.extendScalars.{u, u, u} p).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} p).left_adjoint_additive
  letI : (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk (RingHom.ker p))).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (Ideal.Quotient.mk (RingHom.ker p))).left_adjoint_additive
  Functor.mapHomologicalComplexCompIso (extendScalarsRestrictQuotientKerIso p hp)
    (ComplexShape.up ℤ)

section Models

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]
  [HasDerivedCategory.{w'} (ModuleCat.{u} (R ⧸ RingHom.ker p))]

/-- Degreewise extension of scalars along `p`, localized and then restricted to `R ⧸ ker p`, is
degreewise extension of scalars along `R → R ⧸ ker p`, localized. -/
def quotientKerExtensionDerivedIso :
    ((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ (quotientKerRestriction p hp).mapDerivedCategory ≅
      (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk (RingHom.ker p))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (quotientKerRestriction p hp).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (quotientKerExtensionComplexIso p hp) DerivedCategory.Q

/-- The value of `quotientKerExtensionDerivedIso` at a cochain complex. -/
theorem quotientKerExtensionDerivedIso_hom_app
    (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (quotientKerExtensionDerivedIso p hp).hom.app X =
      (quotientKerRestriction p hp).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((quotientKerExtensionComplexIso p hp).hom.app X) := by
  simp [quotientKerExtensionDerivedIso]

include hp in
/-- `StacksDraft.Perfect.exists_finiteProjective_lift_iso_of_surjective`, with an auxiliary model
of `D(R ⧸ ker p)` through which the statement is reduced to the quotient map. -/
theorem exists_finiteProjective_lift_iso_of_surjective_of_models
    (hI : HenselianPair R (RingHom.ker p)) [HasDerivedCategory.{w''} (ModuleCat.{u} R)]
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (β : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsPseudoCoherentIn K)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (hFbdd : ∃ b, F.IsStrictlyLE b)
    (hFterms : ∀ i, Module.Finite S (F.X i) ∧ Module.Projective S (F.X i))
    (e : DerivedCategory.Q.obj F ≅ G.obj K) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧ (∃ b, P.IsStrictlyLE b) ∧
      ∃ ψ : ((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ≅ F,
      ∃ eK : DerivedCategory.Q.obj P ≅ K,
        β.app P ≫ DerivedCategory.Q.map ψ.hom ≫ e.hom = G.map eK.hom := by
  have : (quotientKerRestriction p hp).mapDerivedCategory.IsEquivalence :=
    StacksDraft.DerivedRingIso.isEquivalence_mapDerivedCategory _ _
      (StacksDraft.DerivedRingIso.restrictScalarsUnitOfInv
        (RingHom.quotientKerEquivOfSurjective hp).symm.toRingHom
        (RingHom.quotientKerEquivOfSurjective hp).toRingHom
        (fun x ↦ (RingHom.quotientKerEquivOfSurjective hp).apply_symm_apply x))
      (StacksDraft.DerivedRingIso.restrictScalarsCounitOfInv
        (RingHom.quotientKerEquivOfSurjective hp).symm.toRingHom
        (RingHom.quotientKerEquivOfSurjective hp).toRingHom
        (fun y ↦ (RingHom.quotientKerEquivOfSurjective hp).symm_apply_apply y))
  have : ((quotientKerRestriction p hp).mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence :=
    StacksDraft.DerivedRingIso.isEquivalence_mapHomologicalComplex_restrictScalars
      (RingHom.quotientKerEquivOfSurjective hp).symm.toRingHom
      (RingHom.quotientKerEquivOfSurjective hp).toRingHom
      (fun x ↦ (RingHom.quotientKerEquivOfSurjective hp).apply_symm_apply x)
      (fun y ↦ (RingHom.quotientKerEquivOfSurjective hp).symm_apply_apply y)
  have : (quotientKerRestriction p hp).mapDerivedCategory.IsRightAdjoint :=
    (quotientKerRestriction p hp).mapDerivedCategory.asEquivalence.symm.toAdjunction.isRightAdjoint
  let β' : DerivedCategory.Q ⋙ (G ⋙ (quotientKerRestriction p hp).mapDerivedCategory) ⟶
      (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk (RingHom.ker p))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight β (quotientKerRestriction p hp).mapDerivedCategory) ≫
      (quotientKerExtensionDerivedIso p hp).hom
  have : (G ⋙ (quotientKerRestriction p hp).mapDerivedCategory).IsLeftDerivedFunctor β'
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
    have h₀ : (G ⋙ (quotientKerRestriction p hp).mapDerivedCategory).IsLeftDerivedFunctor
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight β (quotientKerRestriction p hp).mapDerivedCategory)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := inferInstance
    rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension] at h₀ ⊢
    exact (Functor.isRightKanExtension_iff_of_iso₂ _ β' (quotientKerExtensionDerivedIso p hp)
      (Iso.refl _) (by simp [β'])).1 h₀
  have hF₀bdd : ∃ b, CochainComplex.IsStrictlyLE
      (((quotientKerRestriction p hp).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) b := by
    obtain ⟨b, hb⟩ := hFbdd
    exact ⟨b, inferInstance⟩
  have hF₀terms : ∀ i, Module.Finite (R ⧸ RingHom.ker p)
      ((((quotientKerRestriction p hp).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X i) ∧
      Module.Projective (R ⧸ RingHom.ker p)
        ((((quotientKerRestriction p hp).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X i) :=
    fun i ↦ by
      have := (hFterms i).1
      have := (hFterms i).2
      exact ⟨finite_restrictScalars_ringEquiv _ (F.X i),
        projective_restrictScalars_ringEquiv _ (F.X i)⟩
  obtain ⟨P, hP, hPbdd, eRed, eK, hc⟩ :=
    exists_finiteProjective_lift_iso_quotient_of_isLeftDerivedFunctor (RingHom.ker p)
      (G ⋙ (quotientKerRestriction p hp).mapDerivedCategory) β' hI K hK _ hF₀bdd hF₀terms
      (((quotientKerRestriction p hp).mapDerivedCategoryFactors.app F).symm ≪≫
        (quotientKerRestriction p hp).mapDerivedCategory.mapIso e)
  refine ⟨P, hP, hPbdd, ((quotientKerRestriction p hp).mapHomologicalComplex
    (ComplexShape.up ℤ)).preimageIso ((quotientKerExtensionComplexIso p hp).app P ≪≫ eRed), eK,
    (quotientKerRestriction p hp).mapDerivedCategory.map_injective ?_⟩
  change _ = (G ⋙ (quotientKerRestriction p hp).mapDerivedCategory).map eK.hom
  have hβ' : β'.app P = (quotientKerRestriction p hp).mapDerivedCategory.map (β.app P) ≫
      (quotientKerExtensionDerivedIso p hp).hom.app P := by
    simp [β']
  have hQψ : ∀ {X Y : CochainComplex (ModuleCat.{u} S) ℤ} (f : X ⟶ Y),
      (quotientKerRestriction p hp).mapDerivedCategory.map (DerivedCategory.Q.map f) =
        (quotientKerRestriction p hp).mapDerivedCategoryFactors.hom.app X ≫
          DerivedCategory.Q.map
            (((quotientKerRestriction p hp).mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫
          (quotientKerRestriction p hp).mapDerivedCategoryFactors.inv.app Y := fun f ↦ by
    rw [← (quotientKerRestriction p hp).mapDerivedCategoryFactors_hom_naturality_assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [← hc, hβ', quotientKerExtensionDerivedIso_hom_app, Functor.map_comp, Functor.map_comp,
    hQψ, Functor.preimageIso_hom, Functor.map_preimage]
  simp

end Models

include hp in
/-- **Stacks 0BCE with a prescribed identification, along a surjection, in arbitrary models.**
Let `p : R →+* S` be surjective with kernel `I` such that `(R, I)` is a henselian pair, `G` any
total left derived functor of degreewise extension of scalars `D(R) ⥤ D(S)`, `K` a
pseudo-coherent object of `D(R)`, and `e : F ≅ G K` an identification with a bounded above
complex of finite projective `S`-modules. Then there are a bounded above complex `P` of finite
projective `R`-modules, an isomorphism of complexes `ψ : P ⊗_R S ≅ F` and an isomorphism
`eK : P ≅ K` in `D(R)` such that the comparison of `G` at `P`, followed by `ψ` and `e`, is
`G eK`. This is the form of Stacks 0BCE used in the proof of Stacks 0DL7: "`α` is represented by
an isomorphism `E^• ⊗_A B ≅ P^• ⊗_{B'} B`". -/
theorem exists_finiteProjective_lift_iso_of_surjective
    (hI : HenselianPair R (RingHom.ker p))
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w'} (ModuleCat.{u} S)]
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (β : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsPseudoCoherentIn K)
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (hFbdd : ∃ b, F.IsStrictlyLE b)
    (hFterms : ∀ i, Module.Finite S (F.X i) ∧ Module.Projective S (F.X i))
    (e : DerivedCategory.Q.obj F ≅ G.obj K) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧ (∃ b, P.IsStrictlyLE b) ∧
      ∃ ψ : ((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ≅ F,
      ∃ eK : DerivedCategory.Q.obj P ≅ K,
        β.app P ≫ DerivedCategory.Q.map ψ.hom ≫ e.hom = G.map eK.hom :=
  @exists_finiteProjective_lift_iso_of_surjective_of_models _ _ _ _ p hp _
    (HasDerivedCategory.standard _) hI _ G β _ K hK F hFbdd hFterms e

end Surjection

end StacksDraft.Perfect
