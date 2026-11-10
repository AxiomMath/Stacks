module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.Excision
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.SquareLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.SquareQcqs
public import
    StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.EtaleShriekRestrictionStalks
public import StacksFrontier.CategoryTheory.Triangulated.ExcisionGluingShriek

/-!
# Glueing objects and morphisms of `D(𝒪_W)` along an elementary distinguished square

Let `(U ⊆ W, j : V ⟶ W)` be an elementary distinguished square of algebraic spaces over a scheme
`S`, with intersection `P = U ×_W V`.  Restriction to the three pieces is the derived pullback
`Lj^*` along the étale morphisms of the square, and the two ways of restricting to `P` are
identified by the canonical pseudofunctoriality of derived pullback,
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`.  This file proves:

* objects `A` of `D(𝒪_U)` and `B` of `D(𝒪_V)` with an isomorphism `c : A|_P ≅ B|_P` are glued by
  an object `E` of `D(𝒪_W)` and isomorphisms `E|_U ≅ A`, `E|_V ≅ B` compatible with `c`;
* morphisms `F|_U ⟶ E|_U` and `F|_V ⟶ E|_V` agreeing on `P` are the restrictions of a morphism
  `F ⟶ E`;
* a morphism restricting to isomorphisms on `U` and on `V` is an isomorphism.

The first two are the two assertions of [Stacks, Tag 08HB].  They are the instance, at the
square, of the abstract glueing
`CategoryTheory.Pretriangulated.exists_glue_of_shriekExcision` and
`CategoryTheory.Pretriangulated.exists_hom_of_shriekExcision` through extensions by zero.  The
inputs are:

* the units of extension by zero along the two open immersions `U ⟶ W` and `P ⟶ V` are
  invertible (`AlgebraicGeometry.Space.isIso_etaleModuleLowerShriekAdjunction_unit_app_of_mono`);
* the base change map of extension by zero along `V ⟶ W` is the mate of the identification of
  the square (`AlgebraicGeometry.Space.DerivedPullbackComposition.extensionByZeroBaseChange`),
  and it is invertible for a cartesian square
  (`AlgebraicGeometry.Space.isIso_extensionByZeroBaseChange_canonical_app_of_isPullback`,
  [Stacks, Tag 08HA]);
* excision, clause (2)(a) of [Stacks, Tag 08GG]
  (`AlgebraicGeometry.Space.isIso_derivedUnit_edsEtale_of_isZero_restrict`), and the locality of
  vanishing for the square (`AlgebraicGeometry.Space.isZero_of_isZero_derivedRestrict_eds`).

## Main results

* `AlgebraicGeometry.Space.isIso_unit_etaleDerivedLowerShriekAdjunction_of_mono`: for an étale
  monomorphism the unit of `u_! ⊣ Lu^*` is invertible.
* `AlgebraicGeometry.Space.isIso_of_isIso_derivedPullback_eds`: isomorphisms are detected on the
  two pieces of the square.
* `AlgebraicGeometry.Space.exists_glue_derivedPullback_eds`: glueing objects.
* `AlgebraicGeometry.Space.exists_hom_derivedPullback_eds`: glueing morphisms.

## References

* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 08HA](https://stacks.math.columbia.edu/tag/08HA)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The unit of `u_! ⊣ Lu^*` at `E` is the unit of the underlying adjunction on derived
categories, followed by the identification of the derived pullbacks. -/
private theorem unit_app_etaleDerivedLowerShriekAdjunction_eq {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsEtale B S hS f.hom) (E) :
    (etaleDerivedLowerShriekAdjunction B S hS f hf).unit.app E =
      (Adjunction.mapDerivedCategory (F := etaleExtensionByZero B S hS f hf)
        (G := etaleRestriction B S hS f hf)
          (etaleModuleLowerShriekAdjunction B S hS f hf)).unit.app E ≫
        (smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS f hf).symm.hom.app _ := by
  rw [← Adjunction.homEquiv_id, etaleDerivedLowerShriekAdjunction,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]

/-- **For an étale monomorphism the unit of derived extension by zero is invertible**: an object
of `D(𝒪_Y)` is the derived pullback of its extension by zero along an étale monomorphism
`f : Y ⟶ X`, the unit being invertible on every cohomology sheaf. -/
theorem isIso_unit_etaleDerivedLowerShriekAdjunction_of_mono {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsEtale B S hS f.hom) [Mono f.hom] :
    IsIso (etaleDerivedLowerShriekAdjunction B S hS f hf).unit := by
  suffices ∀ E, IsIso ((etaleDerivedLowerShriekAdjunction B S hS f hf).unit.app E) from
    NatIso.isIso_of_isIso_app _
  intro E
  have h₁ : IsIso ((Adjunction.mapDerivedCategory (F := etaleExtensionByZero B S hS f hf)
        (G := etaleRestriction B S hS f hf)
            (etaleModuleLowerShriekAdjunction B S hS f hf)).unit.app E) :=
    Dualizing.PowerTorsionBaseChange.mapDerivedAdjunction_unit_isIso _ E
      fun _ => isIso_etaleModuleLowerShriekAdjunction_unit_app_of_mono B S hS f hf _
  rw [unit_app_etaleDerivedLowerShriekAdjunction_eq]
  infer_instance

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **Vanishing in `D(𝒪_W)` is local for the square**, read through derived pullbacks. -/
theorem isZero_of_isZero_derivedPullback_eds
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
    (hU : IsZero ((smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj E))
    (hV : IsZero ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj E)) :
    IsZero E :=
  isZero_of_isZero_derivedRestrict_eds B S hS hsq E
    (hU.of_iso ((smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS _
      (isEtale_edsOpenHom B S hS hsq)).app E).symm)
    (hV.of_iso ((smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS _
      (isEtale_edsEtaleHom B S hS hsq)).app E).symm)

/-- **A morphism of `D(𝒪_W)` restricting to isomorphisms on `U` and on `V` is an
isomorphism.** -/
theorem isIso_of_isIso_derivedPullback_eds
    {F E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W))}
    (φ : F ⟶ E)
    (hU : IsIso ((smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).map φ))
    (hV : IsIso ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).map φ)) :
    IsIso φ :=
  isIso_of_isIso_map_of_isZero (isZero_of_isZero_derivedPullback_eds hsq) φ hU hV

/-- Excision in the spelling of derived pullbacks: for `N` in `D(𝒪_V)` restricting to zero on
`P`, the unit `N ⟶ Lj^*(j_! N)` of extension by zero along `j : V ⟶ W` is invertible. -/
theorem isIso_unit_app_etaleDerivedLowerShriekAdjunction_edsEtale
    (N : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (hN : IsZero ((smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq)).obj N)) :
    IsIso ((etaleDerivedLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).unit.app N) := by
  have h₁ := isIso_derivedUnit_edsEtale_of_isZero_restrict B S hS hsq N
    ((forall_isZero_restrict_homology_iff B S hS hsq N).2
      (hN.of_iso ((smallEtaleDerivedModulePullbackIsoOfIsEtale B S hS _
        (isEtale_edsSnd B S hS hsq)).app N).symm))
  rw [unit_app_etaleDerivedLowerShriekAdjunction_eq]
  exact IsIso.comp_isIso' h₁ inferInstance

/-- Excision for the open subspace: for `N` in `D(𝒪_V)` restricting to zero on `P`, its extension
by zero along `j : V ⟶ W` restricts to zero on `U`, by base change of extension by zero. -/
theorem isZero_derivedPullback_edsOpen_etaleExtensionByZero
    (N : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (hN : IsZero ((smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq)).obj N)) :
    IsZero ((smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj
      ((etaleExtensionByZero B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj N)) := by
  have h := isIso_extensionByZeroBaseChange_canonical_app_of_isPullback
    (edsFst B S hS hsq) (edsOpenHom B S hS hsq) (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq)
    (isPullback_edsInter B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
    (isEtale_edsFst B S hS hsq) N
  exact (((etaleExtensionByZero B S hS (edsFst B S hS hsq)
    (isEtale_edsFst B S hS hsq)).mapDerivedCategory.map_isZero hN)).of_iso
      (@asIso _ _ _ _ _ h).symm

/-- The base change map of extension by zero along `V ⟶ W` is the mate of the identification of
the two restrictions to `P`: its transpose is the restriction of the unit at `U`, followed by
that identification. -/
theorem unit_app_comp_map_extensionByZeroBaseChange_eds
    (A : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsOpen B S hS hsq)))) :
    (etaleDerivedLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).unit.app
        ((smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq)).obj A) ≫
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq)).map
        (((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange
          (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq) (edsFst B S hS hsq)
          (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) (isEtale_edsSnd B S hS hsq)
          (isPullback_edsInter B S hS hsq).flip.w).app A) =
      (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq)).map
          ((etaleDerivedLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
            (isEtale_edsOpenHom B S hS hsq)).unit.app A) ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq)
          (edsEtaleHom B S hS hsq) (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
          (isPullback_edsInter B S hS hsq).flip.w).hom.app
          ((etaleExtensionByZero B S hS (edsOpenHom B S hS hsq)
            (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj A) :=
  (Adjunction.unit_comp_map_eq_iff _ _ _).2
    (DerivedPullbackComposition.extensionByZeroBaseChange_app _ _ _ _ _ _ _ _ A)

/-- The base change map of extension by zero along `V ⟶ W` is invertible
([Stacks, Tag 08HA]), the square being cartesian. -/
theorem isIso_extensionByZeroBaseChange_eds_app (A : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsOpen B S hS hsq)))) :
    IsIso (((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange
      (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq) (edsFst B S hS hsq)
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) (isEtale_edsSnd B S hS hsq)
      (isPullback_edsInter B S hS hsq).flip.w).app A) :=
  isIso_extensionByZeroBaseChange_canonical_app_of_isPullback _ _ _ _
    (isPullback_edsInter B S hS hsq).flip (isEtale_edsOpenHom B S hS hsq)
    (isEtale_edsSnd B S hS hsq) A

/-- **Glueing objects of `D(𝒪_W)` along an elementary distinguished square**, the first
assertion of [Stacks, Tag 08HB] with the compatibility of the glueing isomorphisms: objects `A`
of `D(𝒪_U)` and `Bo` of `D(𝒪_V)` with an isomorphism `c : A|_P ≅ Bo|_P` are glued by an object
`E` of `D(𝒪_W)` and isomorphisms `f : E|_U ≅ A` and `g : E|_V ≅ Bo` such that `c ∘ f|_P` is
`g|_P` read through the identification of the two restrictions of `E` to `P`. -/
theorem exists_glue_derivedPullback_eds
    (A : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsOpen B S hS hsq))))
    (Bo : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (c : (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq)).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq)).obj Bo) :
    ∃ (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
      (f : (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj E ≅ A)
      (g : (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj E ≅ Bo),
      (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq)).map f.hom ≫ c.hom =
        ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq)
          (edsEtaleHom B S hS hsq) (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
          (isPullback_edsInter B S hS hsq).flip.w).hom.app E ≫
        (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq)).map g.hom := by
  have := isIso_unit_etaleDerivedLowerShriekAdjunction_of_mono (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
  have := isIso_unit_etaleDerivedLowerShriekAdjunction_of_mono (edsSnd B S hS hsq)
    (isEtale_edsSnd B S hS hsq)
  have := isIso_extensionByZeroBaseChange_eds_app hsq
  exact exists_glue_of_shriekExcision
    (etaleDerivedLowerShriekAdjunction B S hS _ (isEtale_edsOpenHom B S hS hsq))
    (etaleDerivedLowerShriekAdjunction B S hS _ (isEtale_edsEtaleHom B S hS hsq))
    (etaleDerivedLowerShriekAdjunction B S hS _ (isEtale_edsSnd B S hS hsq))
    ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq)
      (edsEtaleHom B S hS hsq) (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
      (isPullback_edsInter B S hS hsq).flip.w)
    ((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange
      (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq) (edsFst B S hS hsq)
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) (isEtale_edsSnd B S hS hsq)
      (isPullback_edsInter B S hS hsq).flip.w)
    (unit_app_comp_map_extensionByZeroBaseChange_eds hsq)
    (isZero_derivedPullback_edsOpen_etaleExtensionByZero hsq)
    (isIso_unit_app_etaleDerivedLowerShriekAdjunction_edsEtale hsq) A Bo c

/-- **Glueing morphisms of `D(𝒪_W)` along an elementary distinguished square**, the second
assertion of [Stacks, Tag 08HB]: morphisms `φ_U : F|_U ⟶ E|_U` and `φ_V : F|_V ⟶ E|_V` whose
restrictions to `P` agree, through the identification of the two restrictions to `P`, are the
restrictions of a morphism `F ⟶ E`. -/
theorem exists_hom_derivedPullback_eds
    {F E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W))}
    (φU : (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj F ⟶
      (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj E)
    (φV : (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj F ⟶
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj E)
    (hagree : (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq)).map φU ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq)
          (edsEtaleHom B S hS hsq) (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
          (isPullback_edsInter B S hS hsq).flip.w).hom.app E =
      ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq)
          (edsEtaleHom B S hS hsq) (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
          (isPullback_edsInter B S hS hsq).flip.w).hom.app F ≫
        (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq)).map φV) :
    ∃ φ : F ⟶ E, (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).map φ = φU ∧
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).map φ = φV := by
  have := isIso_unit_etaleDerivedLowerShriekAdjunction_of_mono (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
  have := isIso_extensionByZeroBaseChange_eds_app hsq
  exact exists_hom_of_shriekExcision
    (etaleDerivedLowerShriekAdjunction B S hS _ (isEtale_edsOpenHom B S hS hsq))
    (etaleDerivedLowerShriekAdjunction B S hS _ (isEtale_edsEtaleHom B S hS hsq))
    (etaleDerivedLowerShriekAdjunction B S hS _ (isEtale_edsSnd B S hS hsq))
    ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq)
      (edsEtaleHom B S hS hsq) (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
      (isPullback_edsInter B S hS hsq).flip.w)
    ((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange
      (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq) (edsFst B S hS hsq)
      (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) (isEtale_edsSnd B S hS hsq)
      (isPullback_edsInter B S hS hsq).flip.w)
    (unit_app_comp_map_extensionByZeroBaseChange_eds hsq)
    (isZero_derivedPullback_edsOpen_etaleExtensionByZero hsq)
    (isIso_unit_app_etaleDerivedLowerShriekAdjunction_edsEtale hsq)
    (isZero_of_isZero_derivedPullback_eds hsq) φU φV hagree

end Square

end AlgebraicGeometry.Space

end

