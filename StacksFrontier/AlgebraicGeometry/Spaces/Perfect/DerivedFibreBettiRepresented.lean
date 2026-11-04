module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.PerfectToPseudoCoherentGeneral
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSectionsIso
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldModules
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Derived fibres on a scheme regarded as an algebraic space

Let `T` be a scheme in the big fppf site over `S` and let `ω` be an object of `D(𝒪_T)`.  The
algebraic space `h_T` represented by `T` has the small étale site of `T` as its small étale site,
and `ε^*ω` is an object of `D(𝒪_{h_T})`, where `ε^*` is the associated-module functor of
Stacks 03DU (4) on derived categories.  A field-valued point `p : Spec(k) ⟶ h_T` is a morphism of
schemes `r : Spec(k) ⟶ T`.  This file proves that the étale derived fibre of `ε^*ω` at `p` is the
Zariski derived fibre of `ω` along `r`:

`dim_k H^n(Lp^*(ε^*ω)) = dim_k H^n(Lr^*ω) = dim_{κ(t)} H^n(ω ⊗^𝐋 κ(t))`,

`t` being the image of the closed point.  Consequently, for an object `K` of `D(𝒪_Y)` with
quasi-coherent cohomology on an algebraic space `Y` — in particular for a perfect `K` — the
derived-fibre Betti numbers at a field-valued point depend only on the point of `|Y|` it
represents (Stacks 03BU).

## Main results

* `AlgebraicGeometry.Space.derivedFibreBettiAt_representedDerivedAssociatedModule`: the étale
  derived fibre of `ε^*ω` at a field-valued point is the Zariski derived fibre of `ω` at the
  underlying point of the scheme.
* `AlgebraicGeometry.Space.derivedCategoryB_of_isPerfect`: a perfect object of `D(𝒪_Y)` has
  quasi-coherent cohomology.
* `AlgebraicGeometry.Space.derivedFibreBettiAt_eq_of_class_eq`: for `K` with quasi-coherent
  cohomology, two field-valued points representing the same point of `|Y|` have the same
  derived-fibre Betti numbers.
* `AlgebraicGeometry.Space.derivedFibreBetti_class` and
  `AlgebraicGeometry.Space.derivedFibreEuler_class`: the Betti numbers and the Euler
  characteristic of such a `K` at the class of a field-valued point are computed at that point.

## Implementation notes

The comparison of derived fibres has three steps.  First, `Lp^*(ε^*ω) ≅ ε^*(Lr^*ω)`: a K-flat
complex with flat terms representing `ω` is carried by `ε^*` to one representing `ε^*ω`
(`AlgebraicGeometry.Space.isKFlat_representedAssociatedModule`), so both derived pullbacks are
computed degreewise and the degreewise square
`AlgebraicGeometry.Space.representedAssociatedModulePullbackComplexIso` applies.  Second, `ε^*`
is exact and commutes with cohomology.  Third, the sections over the identity chart of `ε^*G`
for a quasi-coherent `G` are the global sections of `G`, compatibly with the action of
`Γ(T, 𝒪_T)` (`AlgebraicGeometry.Space.representedAssociatedModuleIdChartAddEquiv_smul`); over a
field every module is quasi-coherent.  The passage from `r` to the residue field `κ(t)` is the
invariance of dimension under extension of the field,
`AlgebraicGeometry.SpecField.finrank_derivedPullback`.

The comparison needs no hypothesis on `ω`.  On an arbitrary algebraic space the independence of
the representative uses that `Lp^*K` has quasi-coherent cohomology (Stacks 08F4), so that by
Stacks 071Q it is `ε^*ω` on the field spectrum.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry

/-! ### Modules on the spectrum of a field -/

variable {R : CommRingCat.{u}}

/-- The `R`-module structure of the global sections of an `𝒪_{Spec R}`-module is the action of
`Γ(Spec R, 𝒪)` through `Γ(Spec R, 𝒪) ≅ R`. -/
theorem moduleSpecΓFunctor_obj_smul (M : (Spec R).Modules) (c : R)
    (y : (moduleSpecΓFunctor (R := R)).obj M) :
    c • y = (show (Spec R).ringCatSheaf.val.obj (Opposite.op ⊤) from (Scheme.ΓSpecIso R).inv c) •
      (show (SheafOfModules.evaluation (Spec R).ringCatSheaf (Opposite.op ⊤)).obj M from y) :=
  rfl

/-- **Every module on the spectrum of a field is quasi-coherent**: it is the sheaf associated to
its module of global sections (`AlgebraicGeometry.SpecField.isIso_fromTildeΓ`). -/
theorem SpecField.isQuasicoherent (hR : IsField R) (M : (Spec R).Modules) : M.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ M.fromTildeΓ (SpecField.isIso_fromTildeΓ hR M))
    (inferInstance : (tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤))).IsQuasicoherent)

namespace DerivedFibreBetti

/- The standard model of the derived category is forced by
`AlgebraicGeometry.SpecField.finrank_derivedPullback`. -/
attribute [local instance 10000] HasDerivedCategory.standard

/-- **The derived fibre along a field-valued point of a scheme.**  For a morphism
`r : Spec(K) ⟶ X` from the spectrum of a field, with image `x` of the closed point, the
dimension over `K` of `H^i(Lr^*E)` is the dimension over `κ(x)` of `H^i(E ⊗^𝐋 κ(x))`: `r` factors
through `Spec κ(x)` and extension of the field does not change dimensions. -/
theorem finrank_derivedPullback_specField {X : Scheme.{u}} {K : Type u} [Field K]
    (r : Spec (.of K) ⟶ X) (E : DerivedCategory X.Modules) (i : ℤ) :
    Module.finrank K ((moduleSpecΓFunctor (R := .of K)).obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj
          ((derivedPullback r.toLRSHom.toShHom).obj E))) =
      Module.finrank (X.residueField (r (IsLocalRing.closedPoint K)))
        ((moduleSpecΓFunctor (R := X.residueField (r (IsLocalRing.closedPoint K)))).obj
          ((DerivedCategory.homologyFunctor
              (Spec (X.residueField (r (IsLocalRing.closedPoint K)))).Modules i).obj
            ((derivedPullback
              (X.fromSpecResidueField (r (IsLocalRing.closedPoint K))).toLRSHom.toShHom).obj
                E))) := by
  set x := r (IsLocalRing.closedPoint K)
  let φ : X.residueField x ⟶ CommRingCat.of K := X.descResidueField (Scheme.stalkClosedPointTo r)
  have hfac : Spec.map φ ≫ X.fromSpecResidueField x = r :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X r
  have hsh : (Spec.map φ).toLRSHom.toShHom ≫ (X.fromSpecResidueField x).toLRSHom.toShHom =
      r.toLRSHom.toShHom := by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
      congrArg (fun k : Spec (.of K) ⟶ X => k.toLRSHom.toShHom) hfac
  have := SpecField.hasLeftDerivedFunctor_pullbackOnHomotopy_SpecMap
    (Field.toIsField (X.residueField x)) (Field.toIsField K) φ
  let e : (derivedPullback r.toLRSHom.toShHom).obj E ≅
      (derivedPullback (Spec.map φ).toLRSHom.toShHom).obj
        ((derivedPullback (X.fromSpecResidueField x).toLRSHom.toShHom).obj E) :=
    (eqToIso (congrArg (fun k => (derivedPullback.{u, u + 1, u + 1} k).obj E) hsh)).symm ≪≫
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (Spec.map φ).toLRSHom.toShHom (X.fromSpecResidueField x).toLRSHom.toShHom).app E).symm
  refine (((moduleSpecΓFunctor (R := .of K)).mapIso
    ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).mapIso
      e)).toLinearEquiv.finrank_eq).trans ?_
  exact SpecField.finrank_derivedPullback (Field.toIsField _) (Field.toIsField K) φ _ i

end DerivedFibreBetti

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
/- The standard model of the derived category is forced by
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Sections of `ε^*G` over the identity chart -/

section Sections

variable (T : BigFppfOver B S hS) (G : ((BigFppfOver.toScheme B S hS).obj T).Modules)
  [G.IsQuasicoherent]

/-- **The sections of `ε^*G` over the identity chart are the global sections of `G`**, for a
quasi-coherent `𝒪_T`-module `G`: the identity chart of `h_T` corresponds to the identity of `T`
in the small étale site of `T`, over which the sections of the associated module are
`Γ(T, id^*G)` (Stacks 03FH (1), `AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections`). -/
def representedAssociatedModuleIdChartAddEquiv :
    ((SheafOfModules.evaluation (ringedToposStructureRingSheaf B S hS (schemeSpace T))
      (Opposite.op (idChart B S hS T))).obj
      ((representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj G)) ≃+
      ((SheafOfModules.evaluation _ (Opposite.op ⊤)).obj G) :=
  let X := (BigFppfOver.toScheme B S hS).obj T
  let W := (representedSmallEtaleEquivalence B S hS T).functor.obj (idChart B S hS T)
  let e₁ := ((SheafOfModules.evaluation _ (Opposite.op W)).mapIso
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections (associatedBigEtaleSite B)
      X T.left.property G)).toLinearEquiv
  let TX := Opposite.op ((_root_.AlgebraicGeometry.SmallEtale.toOver (associatedBigEtaleSite B)
        X T.left.property).obj W)
  let e₂ := ((quasiCoherentPresheaf _ G).objIso TX).addCommGroupIsoToAddEquiv
  let e₃ := ((SheafOfModules.evaluation _ (Opposite.op (⊤ : X.Opens))).mapIso
    ((Scheme.Modules.pullbackId X).app G)).toLinearEquiv
  e₁.toAddEquiv.trans (e₂.trans e₃.toAddEquiv)

/-- The identification `AlgebraicGeometry.Space.representedAssociatedModuleIdChartAddEquiv` is
`Γ(T, 𝒪_T)`-linear. -/
theorem representedAssociatedModuleIdChartAddEquiv_smul
    (r : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (a : (SheafOfModules.evaluation (ringedToposStructureRingSheaf B S hS (schemeSpace T))
      (Opposite.op (idChart B S hS T))).obj
      ((representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj G)) :
    representedAssociatedModuleIdChartAddEquiv B S hS T G
        ((show (ringedToposStructureRingSheaf B S hS (schemeSpace T)).val.obj
          (Opposite.op (idChart B S hS T)) from r) • a) =
      (show ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.val.obj (Opposite.op ⊤) from r) •
        representedAssociatedModuleIdChartAddEquiv B S hS T G a := by
  let X := (BigFppfOver.toScheme B S hS).obj T
  let W := (representedSmallEtaleEquivalence B S hS T).functor.obj (idChart B S hS T)
  let e₁ := ((SheafOfModules.evaluation _ (Opposite.op W)).mapIso
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections (associatedBigEtaleSite B)
      X T.left.property G)).toLinearEquiv
  let TX := Opposite.op ((_root_.AlgebraicGeometry.SmallEtale.toOver (associatedBigEtaleSite B)
        X T.left.property).obj W)
  let e₂ := ((quasiCoherentPresheaf _ G).objIso TX).addCommGroupIsoToAddEquiv
  let e₃ := ((SheafOfModules.evaluation _ (Opposite.op (⊤ : X.Opens))).mapIso
    ((Scheme.Modules.pullbackId X).app G)).toLinearEquiv
  exact (congrArg (fun x => e₃ (e₂ x)) (e₁.map_smul r a)).trans
    ((congrArg e₃ ((e₂.linearEquiv Γ(TX.unop.left, ⊤)).map_smul r (e₁ a))).trans
      (e₃.map_smul r (e₂ (e₁ a))))

end Sections

/-! ### Derived pullback between represented spaces and `ε^*` -/

/-- **Derived pullback along a morphism of represented spaces commutes with `ε^*`.**  For
`g : T' ⟶ T` in the big fppf site with underlying morphism of schemes `r`, and `ω ∈ D(𝒪_T)`,
`Lh^*(ε^*ω) ≅ ε^*(Lr^*ω)`, where `h : h_{T'} ⟶ h_T`.  A K-flat complex with flat terms
representing `ω` computes both sides degreewise. -/
theorem nonempty_derivedPullback_representedDerivedAssociatedModule_iso
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (ω : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS (schemeSpaceMap g)).obj
        ((representedDerivedAssociatedModule B S hS T).obj ω) ≅
      (representedDerivedAssociatedModule B S hS T').obj
        ((derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj ω)) := by
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
    (representedSpaceMap B S hS g)
  obtain ⟨K, k, hK, hKf, hk, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution
    ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace (DerivedCategory.Q.objPreimage ω)
  have := hk
  let eK : DerivedCategory.Q.obj K ≅ ω :=
    asIso (DerivedCategory.Q.map k) ≪≫ DerivedCategory.Q.objObjPreimageIso ω
  let M := ((representedAssociatedModule B S hS T
    (isAlgebraicSpace_yoneda B S hS T)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let eM : (representedDerivedAssociatedModule B S hS T).obj ω ≅ DerivedCategory.Q.obj M :=
    (representedDerivedAssociatedModule B S hS T).mapIso eK.symm ≪≫
      (representedAssociatedModule B S hS T
        (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategoryFactors.app K
  have hM : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) :=
    isKFlat_representedAssociatedModule B S hS T K ⟨hK, hKf⟩
  let e₁ := (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).mapIso eM ≪≫
    derivedPullbackObjIsoOfIsKFlat B S hS (representedSpaceMap B S hS g) M hM
  have e₂ : Nonempty (DerivedCategory.Q.obj
      (((smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS g)).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) ≅ DerivedCategory.Q.obj
      (((modulePullback B S hS (representedSpaceMap B S hS g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) :=
    (@mapHomologicalComplex_obj_congr _ _ _ _ _ _ _ _
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (pullbackModules_smallEtaleRingedToposHom_additive B S hS (representedSpaceMap B S hS g)))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
        (modulePullback B S hS (representedSpaceMap B S hS g))
        (modulePullback_additive (representedSpaceMap B S hS g)))
      (pullbackModules_eq_modulePullback B S hS (representedSpaceMap B S hS g)) M
      (fun C => Nonempty (DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj
      (((modulePullback B S hS (representedSpaceMap B S hS g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)))).2 ⟨Iso.refl _⟩
  let G := ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let e₃ := representedAssociatedModulePullbackComplexIso B S hS g K
  let e₄ : G ≅ (((RingedSpaceModuleAdjunction.modulePullback
      ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (Stacks.ProjectiveBundleQuotients.pullbackIso
        ((BigFppfOver.toScheme B S hS).map g)).app (K.X i))
      (fun i j _ => ((Stacks.ProjectiveBundleQuotients.pullbackIso
        ((BigFppfOver.toScheme B S hS).map g)).hom.naturality (K.d i j)).symm)
  let e₅ : (derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj ω ≅
      DerivedCategory.Q.obj G :=
    (derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).mapIso eK.symm ≪≫
      Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat
        ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom K hK ≪≫
      DerivedCategory.Q.mapIso e₄.symm
  exact ⟨e₁ ≪≫ e₂.some ≪≫ DerivedCategory.Q.mapIso e₃ ≪≫
    ((representedAssociatedModule B S hS T'
      (isAlgebraicSpace_yoneda B S hS T')).mapDerivedCategoryFactors.app G).symm ≪≫
    (representedDerivedAssociatedModule B S hS T').mapIso e₅.symm⟩

/-! ### The derived fibre of `ε^*ω` -/

/-- **The étale derived fibre of `ε^*ω` is the Zariski derived fibre of `ω`.**  For a
field-valued point `p : Spec(k) ⟶ h_T` with underlying morphism of schemes `r : Spec(k) ⟶ T`,
`dim_k H^n(Lp^*(ε^*ω)) = dim_k Γ(Spec k, H^n(Lr^*ω))`. -/
theorem derivedFibreBettiAt_representedDerivedAssociatedModule_eq_finrank (T : BigFppfOver B S hS)
    (ω : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules) (n : ℤ)
    (p : FieldValuedPoint B S hS (schemeSpace T).1) :
    derivedFibreBettiAt (schemeSpace T) ((representedDerivedAssociatedModule B S hS T).obj ω) n p =
      Module.finrank p.carrier ((moduleSpecΓFunctor (R := .of p.carrier)).obj
        ((DerivedCategory.homologyFunctor (Spec (.of p.carrier)).Modules n).obj
          ((derivedPullback
            ((BigFppfOver.toScheme B S hS).map p.value).toLRSHom.toShHom).obj ω))) := by
  let T' := p.siteObject
  let G := (DerivedCategory.homologyFunctor (Spec (.of p.carrier)).Modules n).obj
    ((derivedPullback ((BigFppfOver.toScheme B S hS).map p.value).toLRSHom.toShHom).obj ω)
  have : G.IsQuasicoherent := SpecField.isQuasicoherent (Field.toIsField p.carrier) G
  obtain ⟨I1⟩ := nonempty_derivedPullback_representedDerivedAssociatedModule_iso B S hS p.value ω
  let I2 := (DerivedCategory.homologyFunctor _ n).mapIso I1 ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T')) n).app
        ((derivedPullback ((BigFppfOver.toScheme B S hS).map p.value).toLRSHom.toShHom).obj ω)
  let e₁' := ((SheafOfModules.evaluation (ringedToposStructureRingSheaf B S hS (schemeSpace T'))
    (Opposite.op (idChart B S hS T'))).mapIso I2).toLinearEquiv
  let e₂' := representedAssociatedModuleIdChartAddEquiv B S hS T' G
  let E : (ModuleCat.restrictScalars p.fieldToSections.hom).obj
      ((SheafOfModules.evaluation (ringedToposStructureRingSheaf B S hS (schemeSpace T'))
        (Opposite.op (idChart B S hS T'))).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (schemeSpace T'))) n).obj
          ((smallEtaleDerivedModulePullback B S hS p.toSpace).obj
            ((representedDerivedAssociatedModule B S hS T).obj ω)))) ≃ₗ[p.carrier]
      (moduleSpecΓFunctor (R := .of p.carrier)).obj G :=
    { toAddEquiv := e₁'.toAddEquiv.trans e₂'
      map_smul' := fun c a =>
        ((congrArg e₂' (e₁'.map_smul ((Scheme.ΓSpecIso (.of p.carrier)).inv c) a)).trans
          (representedAssociatedModuleIdChartAddEquiv_smul B S hS T' G
            ((Scheme.ΓSpecIso (.of p.carrier)).inv c) (e₁' a))).trans
          (moduleSpecΓFunctor_obj_smul G c (e₂' (e₁' a))).symm }
  exact E.finrank_eq


/-- **The étale derived fibre of `ε^*ω` at a field-valued point is the derived fibre of `ω` at
the underlying point of `T`.**  For a field-valued point `p` of `h_T` with underlying point `t`
of the scheme `T` (`AlgebraicGeometry.Space.schemePoint`),
`dim_k H^n(Lp^*(ε^*ω)) = dim_{κ(t)} H^n(ω ⊗^𝐋 κ(t))`.  No hypothesis on `ω` is needed. -/
theorem derivedFibreBettiAt_representedDerivedAssociatedModule (T : BigFppfOver B S hS)
    (ω : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules) (n : ℤ)
    (p : FieldValuedPoint B S hS (schemeSpace T).1) :
    derivedFibreBettiAt (schemeSpace T) ((representedDerivedAssociatedModule B S hS T).obj ω) n p =
      Module.finrank (((BigFppfOver.toScheme B S hS).obj T).residueField (schemePoint B S hS T p))
        ((moduleSpecΓFunctor
          (R := ((BigFppfOver.toScheme B S hS).obj T).residueField (schemePoint B S hS T p))).obj
          ((DerivedCategory.homologyFunctor
              (Spec (((BigFppfOver.toScheme B S hS).obj T).residueField
                (schemePoint B S hS T p))).Modules n).obj
            ((derivedPullback (((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField
              (schemePoint B S hS T p)).toLRSHom.toShHom).obj ω))) :=
  (derivedFibreBettiAt_representedDerivedAssociatedModule_eq_finrank B S hS T ω n p).trans
    (DerivedFibreBetti.finrank_derivedPullback_specField
      ((BigFppfOver.toScheme B S hS).map p.value) ω n)

/-- The étale derived-fibre Betti numbers of `ε^*ω` are the derived-fibre Betti numbers of `ω`
read through the identification `|h_T| ≅ |T|` of Stacks 03BX: this is
`AlgebraicGeometry.Space.derivedFibreBettiAt_representedDerivedAssociatedModule` in the spelling
of `AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti`. -/
theorem derivedFibreBettiAt_representedDerivedAssociatedModule_eq_derivedFiberBetti
    (T : BigFppfOver B S hS) (ω : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hω : RingedSpace.IsPseudoCoherent (X := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace) ω)
    (n : ℤ) (p : FieldValuedPoint B S hS (schemeSpace T).1) :
    derivedFibreBettiAt (schemeSpace T) ((representedDerivedAssociatedModule B S hS T).obj ω) n p =
      DerivedFibreBetti.derivedFiberBetti _ ω hω n (schemePoint B S hS T p) :=
  derivedFibreBettiAt_representedDerivedAssociatedModule B S hS T ω n p

/-! ### Independence of the representative -/

/-- **A perfect object of `D(𝒪_Y)` has quasi-coherent cohomology**: it is `m`-pseudo-coherent
for every `m` (`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isPerfect_general`), and
the cohomology of an `m`-pseudo-coherent object above degree `m` is quasi-coherent
(Stacks 08JL). -/
theorem derivedCategoryB_of_isPerfect (Y : AlgebraicSpaces B S hS)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) K :=
  fun i => isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional B S hS Y.1 Y.2 K
    (i - 1) i (RingedSite.isPseudoCoherentFrom_of_isPerfect_general _ hK (i - 1)) (by omega)

variable (Y : AlgebraicSpaces B S hS)

/-- The field-valued point of `h_V` given by a morphism `W ⟶ V` from the field spectrum `W` of a
field-valued point. -/
def FieldValuedPoint.toSchemeSpace (q : FieldValuedPoint B S hS Y.1) {V : BigFppfOver B S hS}
    (f : q.siteObject ⟶ V) : FieldValuedPoint B S hS (schemeSpace V).1 where
  carrier := q.carrier
  contained := q.contained
  toBase := q.toBase
  value := f

/-- Applying a field-valued point `p` of `Y` to a morphism `f` of field spectra into its own
field spectrum gives the restriction of `p` along `f`. -/
theorem FieldValuedPoint.map_toSchemeSpace (p q : FieldValuedPoint B S hS Y.1)
    (f : q.siteObject ⟶ p.siteObject) (hf : Y.1.map f.op p.value = q.value) :
    (q.toSchemeSpace B S hS Y f).map B S hS (schemeSpace p.siteObject).1 p.toSpace.hom = q := by
  cases q with
  | mk c ct tb v =>
    exact congrArg (fun w => ({ carrier := c, contained := ct, toBase := tb, value := w } :
      FieldValuedPoint B S hS Y.1)) hf

/-- **Restricting a field-valued point to an extension field does not change the derived-fibre
Betti numbers**, for an object `K` of `D(𝒪_Y)` with quasi-coherent cohomology.

Both points factor through `p : Spec(k) ⟶ Y`, so both Betti numbers are those of `Lp^*K` on
`Spec(k)` (`AlgebraicGeometry.Space.derivedFibreBettiAt_derivedPullback`).  The object `Lp^*K`
has quasi-coherent cohomology (Stacks 08F4), hence is `ε^*ω` on the field spectrum (Stacks 071Q),
and the derived fibres of `ε^*ω` at the two points are both the derived fibre of `ω` at the
unique point of `Spec(k)`
(`AlgebraicGeometry.Space.derivedFibreBettiAt_representedDerivedAssociatedModule`). -/
theorem derivedFibreBettiAt_eq_of_dominates
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) K)
    (n : ℤ) {p q : FieldValuedPoint B S hS Y.1}
    (h : FieldValuedPoint.Dominates B S hS Y.1 q p) :
    derivedFibreBettiAt Y K n q = derivedFibreBettiAt Y K n p := by
  obtain ⟨f, hf⟩ := h
  let V := p.siteObject
  have hL := derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS p.toSpace K hK
  obtain ⟨ω, -, ⟨e⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS V _ hL
  have hV : Subsingleton ((BigFppfOver.toScheme B S hS).obj V) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have key : ∀ (q' : FieldValuedPoint B S hS Y.1) (f : q'.siteObject ⟶ V)
      (hf : Y.1.map f.op p.value = q'.value), derivedFibreBettiAt Y K n q' =
        derivedFibreBettiAt (schemeSpace V)
          ((representedDerivedAssociatedModule B S hS V).obj ω) n (q'.toSchemeSpace B S hS Y f) :=
    fun q' f hf => by
      rw [derivedFibreBettiAt_congr (schemeSpace V) e, derivedFibreBettiAt_derivedPullback]
      exact congrArg _ (FieldValuedPoint.map_toSchemeSpace B S hS Y p q' f hf).symm
  rw [key q f hf, key p (𝟙 V) (FunctorToTypes.map_id_apply _ _),
    derivedFibreBettiAt_representedDerivedAssociatedModule,
    derivedFibreBettiAt_representedDerivedAssociatedModule]
  generalize schemePoint B S hS V (q.toSchemeSpace B S hS Y f) = x
  generalize schemePoint B S hS V (p.toSchemeSpace B S hS Y (𝟙 V)) = y
  obtain rfl := Subsingleton.elim x y
  rfl

/-- **Stacks 03BU for derived fibres.**  For an object `K` of `D(𝒪_Y)` with quasi-coherent
cohomology, two field-valued points of `Y` representing the same point of `|Y|` have the same
derived-fibre Betti numbers. -/
theorem derivedFibreBettiAt_eq_of_class_eq
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) K)
    (n : ℤ) {p q : FieldValuedPoint B S hS Y.1}
    (h : p.class B S hS Y.1 = q.class B S hS Y.1) :
    derivedFibreBettiAt Y K n p = derivedFibreBettiAt Y K n q := by
  obtain ⟨r, hp, hq⟩ := (FieldValuedPoint.class_eq_class_iff B S hS Y.1 p q).1 h
  rw [← derivedFibreBettiAt_eq_of_dominates B S hS Y K hK n hp,
    derivedFibreBettiAt_eq_of_dominates B S hS Y K hK n hq]

/-- For an object `K` of `D(𝒪_Y)` with quasi-coherent cohomology, the derived-fibre Betti number
at the class of a field-valued point is computed at that point. -/
theorem derivedFibreBetti_class
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) K)
    (n : ℤ) (p : FieldValuedPoint B S hS Y.1) :
    derivedFibreBetti Y K n (p.class B S hS Y.1) = derivedFibreBettiAt Y K n p :=
  derivedFibreBettiAt_eq_of_class_eq B S hS Y K hK n (Quot.out_eq (p.class B S hS Y.1))

/-- For an object `K` of `D(𝒪_Y)` with quasi-coherent cohomology, the derived-fibre Euler
characteristic at the class of a field-valued point is computed at that point. -/
theorem derivedFibreEuler_class
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) K)
    (p : FieldValuedPoint B S hS Y.1) :
    derivedFibreEuler Y K (p.class B S hS Y.1) =
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (derivedFibreBettiAt Y K n p : ℤ) := by
  simp only [derivedFibreEuler_apply, derivedFibreBetti_class B S hS Y K hK]

/-- **Independence of the representative, for a perfect object.**  For a perfect `K`, two
field-valued points of `Y` representing the same point of `|Y|` have the same derived-fibre
Betti numbers; a perfect object has quasi-coherent cohomology
(`AlgebraicGeometry.Space.derivedCategoryB_of_isPerfect`). -/
theorem derivedFibreBettiAt_eq_of_class_eq_of_isPerfect
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K)
    (n : ℤ) {p q : FieldValuedPoint B S hS Y.1}
    (h : p.class B S hS Y.1 = q.class B S hS Y.1) :
    derivedFibreBettiAt Y K n p = derivedFibreBettiAt Y K n q :=
  derivedFibreBettiAt_eq_of_class_eq B S hS Y K (derivedCategoryB_of_isPerfect B S hS Y K hK) n h

end Space

end AlgebraicGeometry

end
