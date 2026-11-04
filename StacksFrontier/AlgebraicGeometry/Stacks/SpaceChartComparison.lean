module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseFibrationModulesEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSliceCounitDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointwisePresentationHomRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescentComparison

/-!
# Comparison maps of equation 076R into the category of an algebraic space

For a morphism of algebraic spaces `h : X ⟶ Y` and a module `M` on the fppf site of `𝒮_Y`, the
comparison map `h_small^*(M|_{Y_étale}) ⟶ h^*M|_{X_étale}` of equation 076R and its naturality,
transport and composition laws.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

section Spaces

variable {X Y Z : AlgebraicSpaces C S hS}

/-- The identity functor of `𝒮_X` is a fibred 1-morphism over `spaceProj X`. -/
theorem isFibredOneMorphism_spaceId (X : AlgebraicSpaces C S hS) :
    (spaceProj X).IsFibredOneMorphism (spaceProj X) (𝟭 _) :=
  Functor.IsFibredOneMorphism.id _

/-- The étale topology on `𝒮_X` is coarser than the fppf topology. -/
theorem spaceEtale_le_fppf (X : AlgebraicSpaces C S hS) :
    BigFppfOver.associatedTopology C S hS (spaceProj X) .etale ≤
      BigFppfOver.associatedTopology C S hS (spaceProj X) .fppf :=
  BigFppfOver.associatedTopology_le_fppf C S hS (spaceProj X) .etale

/-- Restriction to the small étale site of `X` preserves quasi-coherent modules on `𝒮_X`. -/
theorem spaceRestrictionPreservesQuasicoherent (X : AlgebraicSpaces C S hS) :
    Space.RestrictionPreservesQuasicoherent.{u, u + 1, u, u} C S hS X (spaceProj X)
      (isFiberedInGroupoids_spaceProj X) (spacePresentation X) :=
  Space.restrictionPreservesQuasicoherent C S hS X _ (isFiberedInGroupoids_spaceProj X)
    (spacePresentation X)

/-- The functor `𝒮_X ⥤ 𝒮_Y` attached to `h` commutes with the projections to the base. -/
theorem spaceFunctor_comp_spaceProj (h : X ⟶ Y) :
    spaceFunctor h ⋙ spaceProj Y = spaceProj X :=
  (associatedMap C S hS h.hom).1.hom.w

/-- The topology of `C` is coarser than itself. -/
theorem topology_le_self (C : BigFppfSite.{u}) : C.topology ≤ C.topology := le_rfl

/-- The structure sheaf of rings of the fppf site of `𝒮_X`. -/
abbrev spaceRing (X : AlgebraicSpaces C S hS) :=
  FibredSite.ringStructureSheafCore C S hS (spaceProj X) (isFiberedInGroupoids_spaceProj X) .fppf

/-- A module on the fppf site of `𝒮_X`, read on the coarser étale site. -/
abbrev spaceEtale (M : SheafOfModules.{u} (spaceRing X)) :=
  (Stacks.Sites.CoarserTopology.modulePushforward
    (spaceEtale_le_fppf X) _).obj M

/-- `M ↦ M|_{Y_étale}`. -/
abbrev selfChartRestriction (M : SheafOfModules.{u} (spaceRing Y)) :
    Space.Modules.{u, u} C S hS Y.1 Y.2 :=
  Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Y) (spaceProj Y)
    (isFiberedInGroupoids_spaceProj Y) (isFiberedInGroupoids_spaceProj Y)
    (spacePresentation Y) (𝟭 _) (isFibredOneMorphism_spaceId Y) (spaceEtale M)

/-- The restriction functor of Stacks 0GQD for `𝒮_Y`. -/
abbrev spaceQuasicoherentRestriction (Y : AlgebraicSpaces C S hS) :=
  Space.quasicoherentRestriction.{u, u + 1, u, u} C S hS Y (spaceProj Y)
    (isFiberedInGroupoids_spaceProj Y) (spacePresentation Y)
    (spaceRestrictionPreservesQuasicoherent Y)

/-- The restriction functor `spaceQuasicoherentRestriction Y` is an equivalence of categories. -/
instance (Y : AlgebraicSpaces C S hS) : (spaceQuasicoherentRestriction Y).IsEquivalence :=
  Space.isEquivalence_quasicoherentRestriction_unconditional C S hS Y _
    (isFiberedInGroupoids_spaceProj Y) (spacePresentation Y)

/-- `ψ ↦ ψ|_{Y_étale}`. -/
abbrev selfChartRestrictionMap {M M' : SheafOfModules.{u} (spaceRing Y)} (ψ : M ⟶ M') :
    selfChartRestriction M ⟶ selfChartRestriction M' :=
  Space.etaleRestrictedModuleInverseImageMap C S hS (spaceProj Y) (spaceProj Y)
    (isFiberedInGroupoids_spaceProj Y) (isFiberedInGroupoids_spaceProj Y)
    (spacePresentation Y) (𝟭 _) (isFibredOneMorphism_spaceId Y)
    ((Stacks.Sites.CoarserTopology.modulePushforward
      (spaceEtale_le_fppf Y) _).map ψ)

/-- On morphisms, `spaceQuasicoherentRestriction Y` is `selfChartRestrictionMap`. -/
theorem spaceQuasicoherentRestriction_map_hom
    {M M' : FibredSite.quasicoherentModules.{u, u + 1, u, u} C S hS (spaceProj Y)
      (isFiberedInGroupoids_spaceProj Y)} (ψ : M ⟶ M') :
    ((spaceQuasicoherentRestriction Y).map ψ).hom = selfChartRestrictionMap ψ.hom := rfl

/-- `M ↦ h^*M|_{X_étale}`. -/
abbrev spaceEtaleInverseImage (h : X ⟶ Y) (M : SheafOfModules.{u} (spaceRing Y)) :
    Space.Modules.{u, u} C S hS X.1 X.2 :=
  Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) (spaceProj Y)
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
    (spacePresentation X) (spaceFunctor h) (isFibredOneMorphism_spaceFunctor h) (spaceEtale M)

/-- `ψ ↦ h^*ψ|_{X_étale}`. -/
abbrev spaceEtaleInverseImageMap (h : X ⟶ Y) {M M' : SheafOfModules.{u} (spaceRing Y)}
    (ψ : M ⟶ M') : spaceEtaleInverseImage h M ⟶ spaceEtaleInverseImage h M' :=
  Space.etaleRestrictedModuleInverseImageMap C S hS (spaceProj X) (spaceProj Y)
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
    (spacePresentation X) (spaceFunctor h) (isFibredOneMorphism_spaceFunctor h)
    ((Stacks.Sites.CoarserTopology.modulePushforward
      (spaceEtale_le_fppf Y) _).map ψ)

/-- The inverse image `h^*M` of a module on `𝒮_Y` along the 1-morphism attached to `h`. -/
abbrev spacePullback (h : X ⟶ Y) :
    SheafOfModules.{u} (spaceRing Y) ⥤ SheafOfModules.{u} (spaceRing X) :=
  modulePullback C S hS (spaceProj X) (spaceProj Y) (isFiberedInGroupoids_spaceProj X)
    (isFiberedInGroupoids_spaceProj Y) (spaceFunctor h) (spaceFunctor_comp_spaceProj h)
    C.topology (topology_le_self C)

/-- The components of the inverse right unitor of `spaceFunctor h` lie over identities. -/
theorem isHomLift_spaceRightUnitor_inv_app (h : X ⟶ Y) (Z : spaceCat X) :
    (spaceProj Y).IsHomLift (𝟙 ((spaceProj Y).obj ((spaceFunctor h).obj Z)))
      ((Functor.rightUnitor (spaceFunctor h)).inv.app Z) :=
  IsHomLift.id rfl

/-- **The comparison map of equation 076R into `𝒮_Y`**, along `h : X ⟶ Y` and a 2-isomorphism
`φ : h ⋙ 𝟭 ≅ f`: `h_small^*(M|_{Y_étale}) ⟶ f^*M|_{X_étale}`. -/
abbrev spaceComparison (h : X ⟶ Y) (f : spaceCat X ⥤ spaceCat Y)
    (hf : (spaceProj X).IsFibredOneMorphism (spaceProj Y) f) (φ : spaceFunctor h ⋙ 𝟭 _ ≅ f)
    (hφ : ∀ Z, (spaceProj Y).IsHomLift (𝟙 ((spaceProj Y).obj (f.obj Z))) (φ.inv.app Z))
    (M : SheafOfModules.{u} (spaceRing Y)) :=
  Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj Y) (spaceProj Y)
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
    (spacePresentation X) (spacePresentation Y) (spaceFunctor h) f (𝟭 _) hf
    (isFibredOneMorphism_spaceId Y) φ h (spaceFunctorChartIso h)
    (isFiberedInGroupoids_spaceProj Y) hφ (isHomLift_spaceFunctorChartIso_hom_app h) (spaceEtale M)

/-- **The comparison map of equation 076R for a morphism of algebraic spaces**,
`h_small^*(M|_{Y_étale}) ⟶ h^*M|_{X_étale}`. -/
abbrev spaceEtaleInverseImageComparison (h : X ⟶ Y) (M : SheafOfModules.{u} (spaceRing Y)) :
    (Space.modulePullback C S hS h).obj (selfChartRestriction M) ⟶ spaceEtaleInverseImage h M :=
  spaceComparison h (spaceFunctor h) (isFibredOneMorphism_spaceFunctor h)
    (Functor.rightUnitor _) (isHomLift_spaceRightUnitor_inv_app h) M

/-- The composite `spaceFunctor h ⋙ spaceFunctor k` is a fibred 1-morphism. -/
theorem isFibredOneMorphism_spaceFunctor_comp (h : X ⟶ Y) (k : Y ⟶ Z) :
    (spaceProj X).IsFibredOneMorphism (spaceProj Z) (spaceFunctor h ⋙ spaceFunctor k) :=
  isFibredOneMorphism_spaceFunctor (h ≫ k)

/-- The components of the identity isomorphism of `spaceFunctor h ⋙ spaceFunctor k` lie over
identities. -/
theorem isHomLift_spaceRefl_inv_app (h : X ⟶ Y) (k : Y ⟶ Z) (W : spaceCat X) :
    (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj ((spaceFunctor h ⋙ spaceFunctor k).obj W)))
      ((Iso.refl (spaceFunctor h ⋙ spaceFunctor k)).inv.app W) :=
  IsHomLift.id rfl

/-- `M ↦ (h ⋙ k)^*M|_{X_étale}`, along the composite of the two 1-morphisms. -/
abbrev spaceEtaleInverseImage₂ (h : X ⟶ Y) (k : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :
    Space.Modules.{u, u} C S hS X.1 X.2 :=
  Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) (spaceProj Z)
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z)
    (spacePresentation X) (spaceFunctor h ⋙ spaceFunctor k)
    (isFibredOneMorphism_spaceFunctor_comp h k) (spaceEtale M)

/-- The comparison map of equation 076R along `h : X ⟶ Y` for the triangle `h ⋙ k = h ⋙ k`
with `k : Y ⟶ Z`: `h_small^*(k^*M|_{Y_étale}) ⟶ (h ≫ k)^*M|_{X_étale}`. -/
def spaceArrowComparison (h : X ⟶ Y) (k : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :
    (Space.modulePullback C S hS h).obj (spaceEtaleInverseImage k M) ⟶
      spaceEtaleInverseImage (h ≫ k) M :=
  Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj Y) (spaceProj Z)
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
    (spacePresentation X) (spacePresentation Y) (spaceFunctor h) (spaceFunctor h ⋙ spaceFunctor k)
    (spaceFunctor k) (isFibredOneMorphism_spaceFunctor_comp h k)
    (isFibredOneMorphism_spaceFunctor k) (Iso.refl _) h (spaceFunctorChartIso h)
    (isFiberedInGroupoids_spaceProj Z) (isHomLift_spaceRefl_inv_app h k)
    (isHomLift_spaceFunctorChartIso_hom_app h) (spaceEtale M)

/-- `k^*M|_{Y_étale}` is the restriction to `Y_étale` of the module `k^*M` on `𝒮_Y`. -/
theorem spaceEtaleInverseImage_eq (k : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :
    spaceEtaleInverseImage k M = selfChartRestriction ((spacePullback k).obj M) := rfl

/-- The transport along `spaceEtaleInverseImage_eq` acts as the identity on sections. -/
theorem eqToHom_spaceChartRestriction_eq_val_app (k : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z))
    (W : (Space.SmallEtale C S hS Y.1)ᵒᵖ) (x : (spaceEtaleInverseImage k M).val.obj W) :
    (eqToHom (spaceEtaleInverseImage_eq k M)).val.app W x = x := rfl

/-- The inverse transport along `spaceEtaleInverseImage_eq` acts as the identity on sections. -/
theorem eqToHom_spaceChartRestriction_eq_symm_val_app (k : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z)) (W : (Space.SmallEtale C S hS Y.1)ᵒᵖ)
    (x : (selfChartRestriction ((spacePullback k).obj M)).val.obj W) :
    (eqToHom (spaceEtaleInverseImage_eq k M).symm).val.app W x = x := rfl

/-- `(h ≫ k)^*M|_{X_étale} = h^*(k^*M)|_{X_étale}`. -/
theorem spaceEtaleInverseImage_comp (h : X ⟶ Y) (k : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :
    spaceEtaleInverseImage (h ≫ k) M = spaceEtaleInverseImage h ((spacePullback k).obj M) := rfl

/-- The comparison map is natural in the module. -/
theorem spaceEtaleInverseImageComparison_naturality (h : X ⟶ Y)
    {M M' : SheafOfModules.{u} (spaceRing Y)}
    (ψ : M ⟶ M') :
    spaceEtaleInverseImageComparison h M ≫ spaceEtaleInverseImageMap h ψ =
      (Space.modulePullback C S hS h).map (selfChartRestrictionMap ψ) ≫
        spaceEtaleInverseImageComparison h M' :=
  Space.comparisonAlgebraicSpacesModules_naturality C S hS (spaceProj X) (spaceProj Y) (spaceProj Y)
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
    (spacePresentation X) (spacePresentation Y) (spaceFunctor h) (spaceFunctor h) (𝟭 _)
    (isFibredOneMorphism_spaceFunctor h) (isFibredOneMorphism_spaceId _)
    (Functor.rightUnitor _) h (spaceFunctorChartIso h) (isFiberedInGroupoids_spaceProj Y)
    (isHomLift_spaceRightUnitor_inv_app h) (isHomLift_spaceFunctorChartIso_hom_app h)
    ((Stacks.Sites.CoarserTopology.modulePushforward
      (spaceEtale_le_fppf Y) _).map ψ)

/-- **Transporting the comparison map along an equality of morphisms.** -/
theorem pullbackTransport_comp_spaceChartRestrictionComparison {k₁ k₂ : X ⟶ Y} (e : k₁ = k₂)
    (M : SheafOfModules.{u} (spaceRing Y)) :
    Space.pullbackTransport (selfChartRestriction M) e ≫ spaceEtaleInverseImageComparison k₂ M =
      spaceEtaleInverseImageComparison k₁ M ≫
        eqToHom (congrArg (fun k => spaceEtaleInverseImage k M) e) := by
  subst e
  simp [Space.pullbackTransport]

/-- The comparison map of the composite triangle of Stacks 075D (1) is the comparison map along
the composite. -/
theorem spaceEtaleInverseImageComparison_compTriangle (h : X ⟶ Y) (k : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj Z) (spaceProj Z)
      (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z)
      (spacePresentation X) (spacePresentation Z) (spaceFunctor h ⋙ spaceFunctor k)
      (spaceFunctor h ⋙ spaceFunctor k) (𝟭 _) (isFibredOneMorphism_spaceFunctor_comp h k)
      (isFibredOneMorphism_spaceId _)
      (Space.compTriangleIso (spaceFunctor h) (spaceFunctor k) (spaceFunctor h ⋙ spaceFunctor k)
        (spaceFunctor k) (𝟭 _) (Iso.refl _) (Functor.rightUnitor _)) (h ≫ k)
      (Space.comparisonChartFunctorIsoComp C S hS (spaceProj X) (spaceProj Y) (spaceProj Z)
        (spacePresentation X) (spacePresentation Y) (spacePresentation Z) (spaceFunctor h)
        (spaceFunctor k) h k (spaceFunctorChartIso h) (spaceFunctorChartIso k))
      (isFiberedInGroupoids_spaceProj Z)
      (Space.isHomLift_compTriangleIso_inv_app C S hS (spaceProj Z) (spaceFunctor h)
        (spaceFunctor k) (spaceFunctor h ⋙ spaceFunctor k) (spaceFunctor k) (𝟭 _) (Iso.refl _)
        (Functor.rightUnitor _) (isHomLift_spaceRefl_inv_app h k)
        (isHomLift_spaceRightUnitor_inv_app k))
      (Space.isHomLift_comparisonChartFunctorIsoComp_hom_app C S hS (spaceProj X) (spaceProj Y)
        (spaceProj Z) (spacePresentation X) (spacePresentation Y) (spacePresentation Z)
        (spaceFunctor h) (spaceFunctor k) h k (spaceFunctorChartIso h) (spaceFunctorChartIso k)
        (isFibredOneMorphism_spaceFunctor k) (isHomLift_spaceFunctorChartIso_hom_app h)
        (isHomLift_spaceFunctorChartIso_hom_app k)) (spaceEtale M) =
    spaceComparison (h ≫ k) (spaceFunctor h ⋙ spaceFunctor k)
      (isFibredOneMorphism_spaceFunctor_comp h k) (Functor.rightUnitor (spaceFunctor (h ≫ k)))
      (isHomLift_spaceRightUnitor_inv_app (h ≫ k)) M :=
  Space.comparisonAlgebraicSpacesModules_congr_of_faithful (e := rfl) (hφφ' := fun _ => rfl)
    ..

/-- **The composition law of Stacks 075D (1) for the comparison maps into `𝒮_Z`.** -/
theorem spaceEtaleInverseImageComparison_comp (h : X ⟶ Y) (k : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    (Space.modulePullback C S hS h).map (spaceEtaleInverseImageComparison k M) ≫
      Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj Y) (spaceProj Z)
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
        (spacePresentation X) (spacePresentation Y) (spaceFunctor h)
        (spaceFunctor h ⋙ spaceFunctor k) (spaceFunctor k)
        (isFibredOneMorphism_spaceFunctor_comp h k) (isFibredOneMorphism_spaceFunctor k)
        (Iso.refl _) h (spaceFunctorChartIso h) (isFiberedInGroupoids_spaceProj Z)
        (isHomLift_spaceRefl_inv_app h k) (isHomLift_spaceFunctorChartIso_hom_app h)
        (spaceEtale M) =
      (Space.modulePullbackCompIso C S hS h k).hom.app
          (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
            (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
            (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId _) (spaceEtale M)) ≫
        spaceComparison (h ≫ k) (spaceFunctor h ⋙ spaceFunctor k)
          (isFibredOneMorphism_spaceFunctor_comp h k) (Functor.rightUnitor (spaceFunctor (h ≫ k)))
          (isHomLift_spaceRightUnitor_inv_app (h ≫ k)) M := by
  rw [← spaceEtaleInverseImageComparison_compTriangle]
  exact Space.comparisonAlgebraicSpacesModules_comp_compTriangleIso
    (hb₁ := isFibredOneMorphism_spaceFunctor k) ..

example (h : X ⟶ Y) (k : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :
    spaceEtaleInverseImageComparison (h ≫ k) M =
      spaceComparison (h ≫ k) (spaceFunctor h ⋙ spaceFunctor k)
          (isFibredOneMorphism_spaceFunctor_comp h k) (Functor.rightUnitor _)
          (isHomLift_spaceRightUnitor_inv_app (h ≫ k)) M := rfl

/-- The transport along `spaceEtaleInverseImage_comp` acts as the identity on sections. -/
theorem eqToHom_spaceChartRestriction_comp_val_app (h : X ⟶ Y) (k : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z)) (W : (Space.SmallEtale C S hS X.1)ᵒᵖ)
    (x : (spaceEtaleInverseImage (h ≫ k) M).val.obj W) :
    (eqToHom (spaceEtaleInverseImage_comp h k M)).val.app W x = x := rfl

/-- The restriction maps of `k^*M` are those of `M` along the images under `k`. -/
theorem spaceEtale_spacePullback_map_apply (k : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z))
    {A B : spaceCat Y} (f : A ⟶ B)
    (x : (spaceEtale ((spacePullback k).obj M)).val.obj (op B)) :
    (spaceEtale ((spacePullback k).obj M)).val.map f.op x =
      (spaceEtale M).val.map ((spaceFunctor k).map f).op x := rfl

/-- The image under `spaceFunctor k` of the comparison morphism along `h` is the comparison
morphism for the triangle `h ⋙ k = h ⋙ k`. -/
theorem spaceFunctor_map_comparisonMorphism (h : X ⟶ Y) (k : Y ⟶ Z)
    (d : Space.ChartDiagram C S hS X.1 Y.1 h.hom) :
    (spaceFunctor k).map (Space.comparisonMorphism C S hS (spaceProj X) (spaceProj Y)
        (spacePresentation X) (spacePresentation Y) (spaceFunctor h) (spaceFunctor h) (𝟭 _)
        (Functor.rightUnitor _) h (spaceFunctorChartIso h) d) =
      (Space.comparisonMorphism C S hS (spaceProj X) (spaceProj Y) (spacePresentation X)
        (spacePresentation Y) (spaceFunctor h) (spaceFunctor h ⋙ spaceFunctor k) (spaceFunctor k)
        (Iso.refl _) h (spaceFunctorChartIso h) d) := by
  simp [Space.comparisonMorphism]

end Spaces




end AlgebraicGeometry.Stack
