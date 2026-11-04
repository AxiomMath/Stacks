module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentability
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedOfKFlatAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackQuasiCoherentBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangePresheaf
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived pullback along the morphism of sites of a terminal object

Let `C` be a category with a terminal object `X`, viewed as a site with the chaotic topology, and
let `O : Cᵒᵖ ⥤ RingCat` be a sheaf of rings whose section rings are commutative; write `R = O(X)`.
The unique functor `C ⥤ pt` is the obvious morphism of sites `f : (C, O) → (pt, R)`, whose
pushforward is `Rf_* = RΓ(X, -)`. Its derived pullback `Lf^* : D(R) ⥤ D(O)` is the total left
derived functor of the base change `M ↦ (U ↦ O(U) ⊗_R M)` of
`Stacks.TerminalBaseChange.baseChangePresheaf`.

This file constructs `Lf^*`, the adjunction `Lf^* ⊣ Rf_*`, and the computation
`RΓ(U, Lf^*P) ≅ P ⊗^L_R O(U)` of its derived sections.

## Main definitions

* `Lpullback`: the derived pullback `Lf^*`.
* `pullbackAdj`: the adjunction `Lf^* ⊣ RΓ(X, -)`.
* `sectionsAdj`: the derived sections `RΓ(U, Lf^*-)` as a left adjoint of derived restriction of
  scalars along `ρ_U : R → O(U)`.
* `pullbackIso`: the isomorphism `RΓ(U, Lf^*P) ≅ P ⊗^L_R O(U)`.
* `morphismOfSites`: the morphism of sites `f`, at the canonical base-change datum.

## References

* [The Stacks Project, Tag 0GZ1](https://stacks.math.columbia.edu/tag/0GZ1)
* [The Stacks Project, Tag 0H0R](https://stacks.math.columbia.edu/tag/0H0R)
* [The Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [The Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.CartesianObjects (dRestrictCompIso)
open Stacks.TerminalBaseChange

universe w u v r

namespace Stacks.ModulesOnACategory.TerminalMorphismOfSites

-- The section categories use the standard model of the derived category, as in
-- `BrownRepresentability`; `D(O)` keeps its small-Hom model, which the higher priority selects
-- when the morphism universe is still to be determined.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000]
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

/-- The quasi-isomorphisms of cochain complexes of modules over the section ring `O(Y)`. -/
abbrev sectionsQuasiIso (Y : Cᵒᵖ) :
    MorphismProperty (CochainComplex (ModuleCat.{max u v r w} (O.obj Y)) ℤ) :=
  HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)

/-- A morphism of complexes of presheaves of modules is a quasi-isomorphism as soon as it is one
over every object of the site: the derived sections functors `RΓ(U, -)` are jointly
conservative. -/
theorem quasiIso_of_quasiIso_evaluation
    {K K' : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ} (φ : K ⟶ K')
    (h : ∀ U : Cᵒᵖ, QuasiIso (((PresheafOfModules.evaluation.{max u v r w} O U
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ := by
  refine (DerivedCategory.isIso_Q_map_iff_quasiIso (PresheafOfModules.{max u v r w} O) φ).1 ?_
  refine RGamma_jointly_conservative.{w} (O := O) (DerivedCategory.Q.map φ) fun U => ?_
  have h' : IsIso ((((PresheafOfModules.evaluation.{max u v r w} O U).mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q).map φ) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v r w} (O.obj U)) _).2 (h U)
  exact (NatIso.isIso_map_iff
    (PresheafOfModules.evaluation.{max u v r w} O U).mapDerivedCategoryFactors φ).2 h'

variable [CommSections O] {X : C} (hX : IsTerminal X)

/-- Over an object `U` the base change presheaf is extension of scalars along `ρ_U`, so it carries
a quasi-isomorphism between K-flat complexes of `R`-modules to a quasi-isomorphism. -/
theorem quasiIso_baseChangePresheaf_evaluation_map (U : Cᵒᵖ) :
    ∀ {K K' : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ} (f : K ⟶ K'),
      QuasiIso f → CochainComplex.KFlat.{r, max u v r w} K →
      CochainComplex.KFlat.{r, max u v r w} K' →
      QuasiIso ((((baseChangePresheaf.{max u v w} O hX) ⋙
        PresheafOfModules.evaluation.{max u v r w} O U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) := fun f hf hK hK' =>
  have := hf
  CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat.{r, r,
    max u v r w} (rho O hX U) f hK hK'

/-- **The K-flat criterion for base change along a terminal object.** Base change carries a
quasi-isomorphism between K-flat complexes of `R`-modules to a quasi-isomorphism of complexes of
presheaves of `O`-modules. -/
theorem quasiIso_baseChangePresheaf_map :
    ∀ {K K' : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ} (f : K ⟶ K'),
      QuasiIso f → CochainComplex.KFlat.{r, max u v r w} K →
      CochainComplex.KFlat.{r, max u v r w} K' →
      QuasiIso (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) :=
  fun f hf hK hK' =>
    quasiIso_of_quasiIso_evaluation.{w} O _ fun U =>
      quasiIso_baseChangePresheaf_evaluation_map.{w} O hX U f hf hK hK'

/-- Degreewise base change along the canonical maps out of the terminal object, read in
`D(O)`. -/
abbrev baseChangePresheafQ :
    CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ ⥤ DMod.{w} O :=
  (baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- The total left derived functor of base change along a terminal object exists, by the K-flat
resolutions of [Stacks 06Y4]. -/
@[sga "4 XVII 4.1.2" "partial"]
instance hasLeftDerivedFunctor_baseChangePresheafQ :
    (baseChangePresheafQ.{w} O hX).HasLeftDerivedFunctor
      (sectionsQuasiIso.{w} O (Opposite.op X)) :=
  CochainComplex.KFlatAdjunction.hasLeftDerivedFunctor (baseChangePresheaf.{max u v w} O hX)
    (quasiIso_baseChangePresheaf_map.{w} O hX)

/-- **The derived pullback `Lf^* : D(R) ⥤ D(O)`** along the obvious morphism of sites
`f : (C, O) → (pt, R)`, `R = O(X)`: the total left derived functor of base change along the
canonical maps out of the terminal object. -/
abbrev Lpullback :
    DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ⥤ DMod.{w} O :=
  (baseChangePresheafQ.{w} O hX).totalLeftDerived DerivedCategory.Q
    (sectionsQuasiIso.{w} O (Opposite.op X))

/-- The comparison exhibiting `Lf^*` as the total left derived functor of degreewise base
change. -/
abbrev LpullbackComparison :
    DerivedCategory.Q ⋙ Lpullback.{w} O hX ⟶ baseChangePresheafQ.{w} O hX :=
  (baseChangePresheafQ.{w} O hX).totalLeftDerivedCounit DerivedCategory.Q
    (sectionsQuasiIso.{w} O (Opposite.op X))

/-- **The adjunction `Lf^* ⊣ Rf_*`**, where `Rf_* = RΓ(X, -)`: base change along a terminal object
is left adjoint to evaluation at `op X`, and that adjunction survives deriving. -/
def pullbackAdj : Lpullback.{w} O hX ⊣ RGamma.{w} O (Opposite.op X) :=
  CochainComplex.KFlatAdjunction.derivedAdjunction (baseChangePresheaf.{max u v w} O hX)
    (quasiIso_baseChangePresheaf_map.{w} O hX) (baseChangeAdj.{max u v w} O hX)
    (Lpullback.{w} O hX) (LpullbackComparison.{w} O hX)

/-- Extension of scalars along the canonical map `ρ_U : R → O(U)` is additive, being a left
adjoint. -/
instance extendScalarsRho_additive (U : Cᵒᵖ) :
    (ModuleCat.extendScalars.{r, r, max u v r w} (rho O hX U)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{max u v r w, r, r} (rho O hX U)).left_adjoint_additive

/-- The comparison exhibiting the derived sections `RΓ(U, Lf^*-)` as the total left derived functor
of extension of scalars along `ρ_U`. -/
abbrev sectionsComparison (U : Cᵒᵖ) :
    DerivedCategory.Q ⋙ (Lpullback.{w} O hX ⋙ RGamma.{w} O U) ⟶
      (ModuleCat.extendScalars.{r, r, max u v r w} (rho O hX U)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  CochainComplex.KFlatAdjunction.postcompComparison.{r, max u v r w}
      (baseChangePresheaf.{max u v w} O hX) (PresheafOfModules.evaluation.{max u v r w} O U)
      (Lpullback.{w} O hX) (LpullbackComparison.{w} O hX) ≫
    Functor.whiskerRight (CategoryTheory.NatIso.mapHomologicalComplex
      (baseChangeEvaluationIso.{max u v w} O hX U) (ComplexShape.up ℤ)).hom DerivedCategory.Q

/-- The derived sections `RΓ(U, Lf^*-)` are a model of the total left derived functor of extension
of scalars along `ρ_U`: derived functors are absolute, and over `U` base change is extension of
scalars along `ρ_U`. -/
instance isLeftDerivedFunctor_sectionsComparison (U : Cᵒᵖ) :
    (Lpullback.{w} O hX ⋙ RGamma.{w} O U).IsLeftDerivedFunctor (sectionsComparison.{w} O hX U)
      (sectionsQuasiIso.{w} O (Opposite.op X)) := by
  have := CochainComplex.KFlatAdjunction.isLeftDerivedFunctor_postcompMapDerivedCategory.{r,
      max u v r w}
    (baseChangePresheaf.{max u v w} O hX) (quasiIso_baseChangePresheaf_map.{w} O hX)
    (PresheafOfModules.evaluation.{max u v r w} O U) (Lpullback.{w} O hX)
    (LpullbackComparison.{w} O hX)
  exact CochainComplex.KFlatAdjunction.isLeftDerivedFunctor_of_natIso.{r, max u v r w}
    (baseChangePresheaf.{max u v w} O hX ⋙ PresheafOfModules.evaluation.{max u v r w} O U)
    (quasiIso_baseChangePresheaf_evaluation_map.{w} O hX U)
    (baseChangeEvaluationIso.{max u v w} O hX U) (Lpullback.{w} O hX ⋙ RGamma.{w} O U)
    (CochainComplex.KFlatAdjunction.postcompComparison.{r, max u v r w}
      (baseChangePresheaf.{max u v w} O hX) (PresheafOfModules.evaluation.{max u v r w} O U)
      (Lpullback.{w} O hX) (LpullbackComparison.{w} O hX))

/-- **The derived sections of `Lf^*` as a left adjoint.** The derived sections `RΓ(U, Lf^*-)` are
left adjoint to derived restriction of scalars along the canonical map `ρ_U : R → O(U)`. -/
def sectionsAdj (U : C) :
    Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U) ⊣ DRestrict.{w} O (hX.from U).op :=
  CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{r, r, max u v r w}
    (rho O hX (Opposite.op U)) (Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U))
    (sectionsComparison.{w} O hX (Opposite.op U))

/-- `RΓ(U, Lf^*P) ≅ P ⊗^L_R O(U)` naturally in `P`, the base change being along the unique
restriction `R = O(X) → O(U)`. Both sides are left adjoints of derived restriction of scalars
along that map, so they agree by uniqueness of left adjoints. -/
def pullbackIso (bc : BaseChangeData.{w} O) (U : C) :
    Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U) ≅ bc.baseChange (hX.from U).op :=
  (sectionsAdj.{w} O hX U).leftAdjointUniq (bc.baseChangeAdj (hX.from U).op)


omit [CommSections O] in
/-- **The mate of a map of sections, computed from two left adjoints of derived restriction of
scalars.** If the adjoint transpose of `psi` under `adjV`, read through the composition
isomorphism of derived restriction of scalars, is the unit of `adjU`, then the mate of `psi`
under the base-change adjunction is the canonical composite of base-change comparisons.

The hypothesis `hcomp` says that the composition isomorphism `baseChangeComp` of `bc` is the one
conjugate to the composition isomorphism `dRestrictCompIso` of derived restriction of scalars. -/
lemma mate_eq_of_unit_eq (bc : BaseChangeData.{w} O) {Z U V : Cᵒᵖ}
    (b : Z ⟶ V) (a : V ⟶ U) (c : Z ⟶ U) (hc : b ≫ a = c)
    (hcomp : (conjugateEquiv ((bc.baseChangeAdj b).comp (bc.baseChangeAdj a))
        (bc.baseChangeAdj (b ≫ a))).symm (dRestrictCompIso.{r, u, v, w} O b a).hom =
      (bc.baseChangeComp b a).hom)
    {FV : DerivedCategory (ModuleCat.{max u v r w} (O.obj Z)) ⥤
      DerivedCategory (ModuleCat.{max u v r w} (O.obj V))}
    {FU : DerivedCategory (ModuleCat.{max u v r w} (O.obj Z)) ⥤
      DerivedCategory (ModuleCat.{max u v r w} (O.obj U))}
    (adjV : FV ⊣ DRestrict.{w} O b) (adjU : FU ⊣ DRestrict.{w} O c)
    (P : DerivedCategory (ModuleCat.{max u v r w} (O.obj Z)))
    (psi : FV.obj P ⟶ (DRestrict.{w} O a).obj (FU.obj P))
    (hpsi : adjV.unit.app P ≫ (DRestrict.{w} O b).map psi ≫
        (dRestrictCompIso.{r, u, v, w} O b a).hom.app (FU.obj P) ≫
          eqToHom (by rw [hc]; rfl) = adjU.unit.app P) :
    psi = (adjV.leftAdjointUniq (bc.baseChangeAdj b)).hom.app P ≫
      (bc.baseChangeAdj a).unit.app ((bc.baseChange b).obj P) ≫
        (DRestrict.{w} O a).map ((bc.baseChangeComp b a).inv.app P ≫ eqToHom (by rw [hc]) ≫
          (adjU.leftAdjointUniq (bc.baseChangeAdj c)).inv.app P) := by
  subst hc
  have hcu : ((bc.baseChangeAdj b).comp (bc.baseChangeAdj a)).unit.app P =
      (bc.baseChangeAdj b).unit.app P ≫
        (DRestrict.{w} O b).map ((bc.baseChangeAdj a).unit.app ((bc.baseChange b).obj P)) :=
    Adjunction.comp_unit_app _ _ P
  rw [eqToHom_refl, Category.comp_id] at hpsi
  have key : adjV.unit.app P ≫ (DRestrict.{w} O b).map
      ((adjV.leftAdjointUniq (bc.baseChangeAdj b)).hom.app P ≫
        (bc.baseChangeAdj a).unit.app ((bc.baseChange b).obj P) ≫
          (DRestrict.{w} O a).map ((bc.baseChangeComp b a).inv.app P ≫
            (adjU.leftAdjointUniq (bc.baseChangeAdj (b ≫ a))).inv.app P)) ≫
      (dRestrictCompIso.{r, u, v, w} O b a).hom.app (FU.obj P) = adjU.unit.app P := by
    rw [Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (Adjunction.unit_leftAdjointUniq_hom_app adjV (bc.baseChangeAdj b) P),
      ← reassoc_of% hcu, ← Functor.comp_map,
      (dRestrictCompIso.{r, u, v, w} O b a).hom.naturality,
      reassoc_of% (unit_conjugateEquiv_symm ((bc.baseChangeAdj b).comp (bc.baseChangeAdj a))
        (bc.baseChangeAdj (b ≫ a)) (dRestrictCompIso.{r, u, v, w} O b a).hom P), hcomp]
    simp only [← Functor.map_comp, Iso.hom_inv_id_app_assoc]
    rw [← Adjunction.unit_leftAdjointUniq_hom_app adjU (bc.baseChangeAdj (b ≫ a)) P]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  apply (adjV.homEquiv P _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← Iso.cancel_iso_hom_right _ _ ((dRestrictCompIso.{r, u, v, w} O b a).app (FU.obj P))]
  simp only [Iso.app_hom, Category.assoc, eqToHom_refl, Category.id_comp]
  rw [hpsi, key]

/-- The unit of `sectionsAdj` on a localized complex: composed with the comparison exhibiting
`RΓ(U, Lf^*-)` as the total left derived functor of extension of scalars along `ρ_U`, it is the
degreewise unit of extension and restriction of scalars. -/
lemma sectionsAdj_unit_app_Q (W : C)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    (sectionsAdj.{w} O hX W).unit.app (DerivedCategory.Q.obj K) ≫
        (DRestrict.{w} O (hX.from W).op).map
          ((sectionsComparison.{w} O hX (Opposite.op W)).app K) =
      DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{max u v r w, r, r}
            (rho O hX (Opposite.op W))).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K) ≫
        (ModuleCat.restrictScalars.{max u v r w}
            (rho O hX (Opposite.op W))).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{r, r, max u v r w}
            (rho O hX (Opposite.op W))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  have := CochainComplex.KFlatAdjunction.isLeftDerivedFunctor_postcomp.{r, max u v r w}
    (ModuleCat.extendScalars.{r, r, max u v r w} (rho O hX (Opposite.op W)))
    (quasiIso_baseChangePresheaf_evaluation_map.{w} O hX (Opposite.op W))
    (Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op W))
    (sectionsComparison.{w} O hX (Opposite.op W))
    (ModuleCat.restrictScalars.{max u v r w} (rho O hX (Opposite.op W))).mapDerivedCategory
  exact Adjunction.derivedη_fac_app _ (sectionsQuasiIso.{w} O (Opposite.op X)) _ _ K

omit [CommSections O] in
/-- **Naturality of the canonical derived restriction map.** The restriction maps
`RΓ(V, -) ⟶ DRestrict (RΓ(U, -))` form a natural transformation, being the components of
`restrictionD` followed by the composition-compatibility isomorphism. -/
lemma restrictionMap_naturality {U V : Cᵒᵖ} (a : V ⟶ U) {K L : DMod.{w} O} (g : K ⟶ L) :
    (RGamma.{w} O V).map g ≫ restrictionMap.{w} O a L =
      restrictionMap.{w} O a K ≫ (DRestrict.{w} O a).map ((RGamma.{w} O U).map g) :=
  (restrictionD.{w} O a ≫ (RGammaRestrictIso.{w} O a).hom).naturality g

omit [CommSections O] in
/-- On a localized complex the derived restriction transformation is the degreewise restriction
of sections, read through the factorizations of the two derived functors it connects: this is the
defining property of the lift of `PresheafOfModules.restriction` through the localization. -/
lemma restrictionD_app_Q {U V : Cᵒᵖ} (a : V ⟶ U)
    (M : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    (restrictionD.{w} O a).app (DerivedCategory.Q.obj M) =
      (PresheafOfModules.evaluation.{max u v r w} O V).mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (PresheafOfModules.restriction O a) (ComplexShape.up ℤ)).app M) ≫
          (PresheafOfModules.evaluation.{max u v r w} O U ⋙
            ModuleCat.restrictScalars.{max u v r w}
              (O.map a).hom).mapDerivedCategoryFactors.inv.app M := by
  rw [restrictionD]
  simp only [Localization.liftNatTrans_app, Functor.whiskerRight_app]
  rfl

/-- The comparison exhibiting the derived sections of `Lf^*` as a total left derived functor,
evaluated at a complex: the comparison of `Lf^*` itself, pushed to the sections over `W`, then
the identification of the sections of the base change presheaf with extension of scalars. -/
lemma sectionsComparison_app (W : Cᵒᵖ)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    (sectionsComparison.{w} O hX W).app K =
      (RGamma.{w} O W).map ((LpullbackComparison.{w} O hX).app K) ≫
        (CochainComplex.KFlatAdjunction.mapCompMapDerivedCategoryIso.{r, max u v r w}
            (baseChangePresheaf.{max u v w} O hX)
            (PresheafOfModules.evaluation.{max u v r w} O W)).hom.app K ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (baseChangeEvaluationIso.{max u v w} O hX W) (ComplexShape.up ℤ)).hom.app K) := by
  simp only [NatTrans.comp_app, CochainComplex.KFlatAdjunction.postcompComparison_app,
    Functor.whiskerRight_app, Category.assoc]

/-- **The restriction map on the derived sections of `Lf^*`, moved across the comparison.**
Naturality of the canonical derived restriction map carries it from the derived pullback of a
localized complex to the localization of the degreewise base change, at the cost of the
comparison of `Lf^*` with degreewise base change on both sides. -/
lemma restrictionMap_Lpullback_app_Q {U V : Cᵒᵖ} (a : V ⟶ U)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    restrictionMap.{w} O a ((Lpullback.{w} O hX).obj (DerivedCategory.Q.obj K)) ≫
        (DRestrict.{w} O a).map ((sectionsComparison.{w} O hX U).app K) =
      (RGamma.{w} O V).map ((LpullbackComparison.{w} O hX).app K) ≫
        restrictionMap.{w} O a ((baseChangePresheafQ.{w} O hX).obj K) ≫
          (DRestrict.{w} O a).map
            ((CochainComplex.KFlatAdjunction.mapCompMapDerivedCategoryIso.{r, max u v r w}
                (baseChangePresheaf.{max u v w} O hX)
                (PresheafOfModules.evaluation.{max u v r w} O U)).hom.app K ≫
              DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
                (baseChangeEvaluationIso.{max u v w} O hX U) (ComplexShape.up ℤ)).hom.app K)) := by
  rw [sectionsComparison_app, Functor.map_comp, ← Category.assoc,
    ← restrictionMap_naturality, Category.assoc]

omit [CommSections O] in
/-- Uniqueness of maps to the terminal object: the canonical map out of `op X` to `op U` is the
canonical map to `op V` followed by any `a : op V ⟶ op U`. -/
lemma from_op_comp {U V : C} (a : Opposite.op V ⟶ Opposite.op U) :
    (hX.from V).op ≫ a = (hX.from U).op :=
  Quiver.Hom.unop_inj (hX.hom_ext _ _)

/-- Derived restriction of scalars along `a : op V ⟶ op U` followed by derived restriction of
scalars along the canonical map out of the terminal object to `op V` is derived restriction of
scalars along the canonical map to `op U`. -/
def dRestrictTerminalIso {U V : C} (a : Opposite.op V ⟶ Opposite.op U) :
    DRestrict.{w} O a ⋙ DRestrict.{w} O (hX.from V).op ≅ DRestrict.{w} O (hX.from U).op :=
  dRestrictCompIso.{r, u, v, w} O (hX.from V).op a ≪≫
    eqToIso (congrArg (fun g : Opposite.op X ⟶ Opposite.op U => DRestrict.{w} O g)
      (from_op_comp hX a))

omit [CommSections O] in
/-- `dRestrictTerminalIso` is the composition isomorphism of derived restriction of scalars
followed by the transport along the terminal-object identity. -/
lemma dRestrictTerminalIso_hom_app {U V : C} (a : Opposite.op V ⟶ Opposite.op U)
    (N : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op U)))) :
    (dRestrictTerminalIso.{w} O hX a).hom.app N =
      (dRestrictCompIso.{r, u, v, w} O (hX.from V).op a).hom.app N ≫
        eqToHom (Functor.congr_obj
          (congrArg (fun g : Opposite.op X ⟶ Opposite.op U => DRestrict.{w} O g)
            (from_op_comp hX a)) N) := by
  rw [dRestrictTerminalIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]

/-- The canonical derived restriction maps on the derived sections of the derived pullback,
assembled into a natural transformation in the variable of `D(R)`. -/
def pullbackRestrictionNat {U V : C} (a : Opposite.op V ⟶ Opposite.op U) :
    Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op V) ⟶
      (Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U)) ⋙ DRestrict.{w} O a :=
  Functor.whiskerLeft (Lpullback.{w} O hX)
    (restrictionD.{w} O a ≫ (RGammaRestrictIso.{w} O a).hom)

/-- The unit of the derived sections adjunction over `V`, followed by the canonical derived
restriction map along `a` and the composition isomorphism of derived restriction of scalars. It
is a natural transformation with the same source and target as the unit over `U`. -/
def unitRestrictionNat {U V : C} (a : Opposite.op V ⟶ Opposite.op U) :
    𝟭 (DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X)))) ⟶
      (Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U)) ⋙
        DRestrict.{w} O (hX.from U).op :=
  (sectionsAdj.{w} O hX V).unit ≫
    Functor.whiskerRight (pullbackRestrictionNat.{w} O hX a)
      (DRestrict.{w} O (hX.from V).op) ≫
    (Functor.associator (Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U))
      (DRestrict.{w} O a) (DRestrict.{w} O (hX.from V).op)).hom ≫
    Functor.whiskerLeft (Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U))
      (dRestrictTerminalIso.{w} O hX a).hom

/-- The components of `unitRestrictionNat`. -/
lemma unitRestrictionNat_app {U V : C} (a : Opposite.op V ⟶ Opposite.op U)
    (P : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X)))) :
    (unitRestrictionNat.{w} O hX a).app P =
      (sectionsAdj.{w} O hX V).unit.app P ≫
        (DRestrict.{w} O (hX.from V).op).map
            (restrictionMap.{w} O a ((Lpullback.{w} O hX).obj P)) ≫
          (dRestrictTerminalIso.{w} O hX a).hom.app
            ((Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U)).obj P) := by
  simp only [unitRestrictionNat, pullbackRestrictionNat, restrictionMap, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp]

/-- The comparison exhibiting `RΓ(U, Lf^*-)` followed by derived restriction of scalars along
`ρ_U` as a model of the total left derived functor of extension of scalars along `ρ_U` followed
by derived restriction of scalars. -/
def sectionsRestrictComparison (U : C) :
    DerivedCategory.Q ⋙ ((Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U)) ⋙
        DRestrict.{w} O (hX.from U).op) ⟶
      (ModuleCat.extendScalars.{r, r, max u v r w}
          (rho O hX (Opposite.op U))).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⋙ DRestrict.{w} O (hX.from U).op :=
  (Functor.associator DerivedCategory.Q (Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U))
      (DRestrict.{w} O (hX.from U).op)).inv ≫
    Functor.whiskerRight (sectionsComparison.{w} O hX (Opposite.op U))
      (DRestrict.{w} O (hX.from U).op)

/-- The components of `sectionsRestrictComparison`. -/
lemma sectionsRestrictComparison_app (U : C)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    (sectionsRestrictComparison.{w} O hX U).app K =
      (DRestrict.{w} O (hX.from U).op).map
        ((sectionsComparison.{w} O hX (Opposite.op U)).app K) := by
  rw [sectionsRestrictComparison, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp]

/-- **Absoluteness of the derived sections of `Lf^*`.** Derived sections over `U` followed by
derived restriction of scalars along `ρ_U` are again a model of a total left derived functor. -/
lemma isLeftDerivedFunctor_sectionsRestrictComparison (U : C) :
    ((Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U)) ⋙
      DRestrict.{w} O (hX.from U).op).IsLeftDerivedFunctor
      (sectionsRestrictComparison.{w} O hX U) (sectionsQuasiIso.{w} O (Opposite.op X)) :=
  CochainComplex.KFlatAdjunction.isLeftDerivedFunctor_postcomp.{r, max u v r w}
    (ModuleCat.extendScalars.{r, r, max u v r w} (rho O hX (Opposite.op U)))
    (quasiIso_baseChangePresheaf_evaluation_map.{w} O hX (Opposite.op U))
    (Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U))
    (sectionsComparison.{w} O hX (Opposite.op U))
    (ModuleCat.restrictScalars.{max u v r w} (rho O hX (Opposite.op U))).mapDerivedCategory

open scoped ChangeOfRings in
/-- **The degreewise compatibility of the units of extension and restriction of scalars with the
restriction maps of the base change presheaf.** For an `R`-module `M` the map `m ↦ 1 ⊗ m` into
`O(V) ⊗_R M`, followed by the restriction `O(V) ⊗_R M → O(U) ⊗_R M` of the base change presheaf
along `a : op V ⟶ op U`, is the map `m ↦ 1 ⊗ m` into `O(U) ⊗_R M`, the two sides being compared
by the composition isomorphism of restriction of scalars along `R → O(V) → O(U)`. -/
lemma extendRestrictScalarsAdj_unit_comp_baseChangePresheaf_map {U V : Cᵒᵖ} (a : V ⟶ U)
    (M : ModuleCat.{max u v r w} (O.obj (Opposite.op X))) :
    (ModuleCat.extendRestrictScalarsAdj.{max u v r w, r, r} (rho O hX V)).unit.app M ≫
        (ModuleCat.restrictScalars.{max u v r w} (rho O hX V)).map
            (((baseChangePresheaf.{max u v w} O hX).obj M).map a) ≫
          (ModuleCat.restrictScalarsComp'.{max u v r w} (rho O hX V) (O.map a).hom
              (rho O hX U) (rho_comp O hX a).symm).inv.app
            ((ModuleCat.extendScalars.{r, r, max u v r w} (rho O hX U)).obj M) =
      (ModuleCat.extendRestrictScalarsAdj.{max u v r w, r, r} (rho O hX U)).unit.app M := by
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  show ((O.map a).hom (1 : O.obj V)) ⊗ₜ[O.obj (Opposite.op X), rho O hX U] m
      = (1 : O.obj U) ⊗ₜ[O.obj (Opposite.op X), rho O hX U] m
  rw [map_one]

/-- Degreewise, the identification of the sections of the base change presheaf with extension of
scalars is the identity: the two presheaves of modules agree in each degree and over each
object. -/
lemma baseChangeEvaluation_mapHomologicalComplex_hom_app (W : Cᵒᵖ)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    (NatIso.mapHomologicalComplex (baseChangeEvaluationIso.{max u v w} O hX W)
      (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := by
  ext i
  simp

/-- The identification of the sections of the base change presheaf with extension of scalars is
the identity of the derived category. -/
lemma Q_map_baseChangeEvaluation_mapHomologicalComplex_hom_app (W : Cᵒᵖ)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (baseChangeEvaluationIso.{max u v w} O hX W) (ComplexShape.up ℤ)).hom.app K) = 𝟙 _ :=
  (congrArg (fun g => DerivedCategory.Q.map g)
    (baseChangeEvaluation_mapHomologicalComplex_hom_app.{w} O hX W K)).trans
      (DerivedCategory.Q.map_id _)

/-- Degreewise base change followed by the sections over `W`, localized, is the localization of
the degreewise sections of the base change presheaf: the comparison is the canonical factorization
of the derived functor of evaluation. -/
lemma mapCompMapDerivedCategoryIso_hom_app (W : Cᵒᵖ)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    (CochainComplex.KFlatAdjunction.mapCompMapDerivedCategoryIso.{r, max u v r w}
        (baseChangePresheaf.{max u v w} O hX)
        (PresheafOfModules.evaluation.{max u v r w} O W)).hom.app K =
      (PresheafOfModules.evaluation.{max u v r w} O W).mapDerivedCategoryFactors.hom.app
        (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := by
  have h : (mapHomologicalComplexCompIso
      (Iso.refl (baseChangePresheaf.{max u v w} O hX ⋙
        PresheafOfModules.evaluation.{max u v r w} O W))
      (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := by
    ext i
    simp
  simp [CochainComplex.KFlatAdjunction.mapCompMapDerivedCategoryIso, h]

/-- The comparison exhibiting the derived sections of `Lf^*` as a total left derived functor, on a
localized complex: the comparison of `Lf^*` pushed to the sections over `W`, followed by the
canonical factorization of the derived functor of evaluation. -/
lemma sectionsComparison_app_Q (W : Cᵒᵖ)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    (sectionsComparison.{w} O hX W).app K =
      (RGamma.{w} O W).map ((LpullbackComparison.{w} O hX).app K) ≫
        (PresheafOfModules.evaluation.{max u v r w} O W).mapDerivedCategoryFactors.hom.app
          (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) := by
  rw [sectionsComparison_app, mapCompMapDerivedCategoryIso_hom_app,
    Q_map_baseChangeEvaluation_mapHomologicalComplex_hom_app]
  exact congrArg (CategoryStruct.comp _) (Category.comp_id _)

/-- The components of `unitRestrictionNat`, with the transport along the terminal-object identity
moved across a map of the derived sections over `U`. -/
lemma unitRestrictionNat_app_comp {U V : C} (a : Opposite.op V ⟶ Opposite.op U)
    (P : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X))))
    {N : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op U)))}
    (g : (Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U)).obj P ⟶ N) :
    (unitRestrictionNat.{w} O hX a).app P ≫ (DRestrict.{w} O (hX.from U).op).map g =
      (sectionsAdj.{w} O hX V).unit.app P ≫
        (DRestrict.{w} O (hX.from V).op).map
            (restrictionMap.{w} O a ((Lpullback.{w} O hX).obj P) ≫ (DRestrict.{w} O a).map g) ≫
          (dRestrictTerminalIso.{w} O hX a).hom.app N := by
  rw [unitRestrictionNat_app, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (dRestrictTerminalIso.{w} O hX a).hom.naturality g, Functor.comp_map]

/-- The two identifications occurring in the comparison of the derived sections of `Lf^*`,
composed: the sections of the degreewise base change are the localization of the degreewise
sections, which are extension of scalars. -/
lemma mapCompMapDerivedCategoryIso_hom_app_comp (W : Cᵒᵖ)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    (CochainComplex.KFlatAdjunction.mapCompMapDerivedCategoryIso.{r, max u v r w}
          (baseChangePresheaf.{max u v w} O hX)
          (PresheafOfModules.evaluation.{max u v r w} O W)).hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (baseChangeEvaluationIso.{max u v w} O hX W) (ComplexShape.up ℤ)).hom.app K) =
      (PresheafOfModules.evaluation.{max u v r w} O W).mapDerivedCategoryFactors.hom.app
        (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := by
  rw [mapCompMapDerivedCategoryIso_hom_app,
    Q_map_baseChangeEvaluation_mapHomologicalComplex_hom_app]
  exact Category.comp_id _

/-- The canonical derived restriction map on the localization of a complex of base changes, read
through the canonical factorization of the derived functor of evaluation over `U`: the
factorizations over `U` cancel and only the degreewise restriction of sections is left. -/
lemma restrictionMap_baseChange_app_Q {U V : Cᵒᵖ} (a : V ⟶ U)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    restrictionMap.{w} O a (DerivedCategory.Q.obj
          (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≫
        (DRestrict.{w} O a).map
          ((PresheafOfModules.evaluation.{max u v r w} O U).mapDerivedCategoryFactors.hom.app
            (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) =
      (PresheafOfModules.evaluation.{max u v r w} O V).mapDerivedCategoryFactors.hom.app
          (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (PresheafOfModules.restriction O a) (ComplexShape.up ℤ)).app
          (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≫
          (ModuleCat.restrictScalars.{max u v r w}
              (O.map a).hom).mapDerivedCategoryFactors.inv.app
            (((PresheafOfModules.evaluation.{max u v r w} O U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)) := by
  rw [restrictionMap_Q]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact congrArg (CategoryStruct.comp _) (congrArg (CategoryStruct.comp _)
    ((congrArg (CategoryStruct.comp _) ((DRestrict.{w} O a).map_id _)).trans
      (Category.comp_id _)))

/-- **The canonical derived restriction map on the derived sections of `Lf^*`, computed on a
localized complex.** Moved across the comparisons exhibiting those sections as a total left derived
functor, the restriction map becomes the degreewise restriction of sections of the base change
presheaf, read through the canonical factorizations of the derived functors of evaluation over `V`
and of restriction of scalars along `a`. -/
lemma restrictionMap_Lpullback_sectionsComparison {U V : C}
    (a : Opposite.op V ⟶ Opposite.op U)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    restrictionMap.{w} O a ((Lpullback.{w} O hX).obj (DerivedCategory.Q.obj K)) ≫
        (DRestrict.{w} O a).map ((sectionsComparison.{w} O hX (Opposite.op U)).app K) =
      (RGamma.{w} O (Opposite.op V)).map ((LpullbackComparison.{w} O hX).app K) ≫
        (PresheafOfModules.evaluation.{max u v r w} O (Opposite.op V)
            ).mapDerivedCategoryFactors.hom.app
          (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
              (PresheafOfModules.restriction O a) (ComplexShape.up ℤ)).app
            (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ≫
            (ModuleCat.restrictScalars.{max u v r w}
                (O.map a).hom).mapDerivedCategoryFactors.inv.app
              (((PresheafOfModules.evaluation.{max u v r w} O (Opposite.op U)
                  ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K)) := by
  simp only [restrictionMap_Lpullback_app_Q, mapCompMapDerivedCategoryIso_hom_app_comp]
  exact congrArg (CategoryStruct.comp _) (restrictionMap_baseChange_app_Q.{w} O hX a K)

omit [CommSections O] in
/-- **The composition isomorphism of derived restriction of scalars on a localized complex.**
Transported along an equation `f ≫ g = c` of morphisms of the site, it is assembled from the
canonical factorizations of the derived functors of restriction of scalars along `f`, along `g`
and along `c`, together with the degreewise composition isomorphism of restriction of scalars. -/
lemma dRestrictCompIso_hom_app_Q {U V W : Cᵒᵖ} (f : W ⟶ V) (g : V ⟶ U) (c : W ⟶ U)
    (hc : f ≫ g = c) (hfg : (O.map c).hom = (O.map g).hom.comp (O.map f).hom)
    (L : CochainComplex (ModuleCat.{max u v r w} (O.obj U)) ℤ) :
    (dRestrictCompIso.{r, u, v, w} O f g).hom.app (DerivedCategory.Q.obj L) ≫
        eqToHom (Functor.congr_obj (congrArg (fun h : W ⟶ U => DRestrict.{w} O h) hc)
          (DerivedCategory.Q.obj L)) =
      (DRestrict.{w} O f).map
          ((ModuleCat.restrictScalars.{max u v r w}
            (O.map g).hom).mapDerivedCategoryFactors.hom.app L) ≫
        (ModuleCat.restrictScalars.{max u v r w}
            (O.map f).hom).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars.{max u v r w} (O.map g).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (ModuleCat.restrictScalarsComp'.{max u v r w} (O.map f).hom (O.map g).hom
                (O.map c).hom hfg) (ComplexShape.up ℤ)).inv.app L) ≫
            (ModuleCat.restrictScalars.{max u v r w}
              (O.map c).hom).mapDerivedCategoryFactors.inv.app L := by
  subst hc
  rw [eqToHom_refl, Category.comp_id]
  have h : (dRestrictCompIso.{r, u, v, w} O f g).hom.app (DerivedCategory.Q.obj L) =
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
            (ModuleCat.restrictScalars.{max u v r w} (O.map g).hom)
            (ModuleCat.restrictScalars.{max u v r w} (O.map f).hom)).inv.app
          (DerivedCategory.Q.obj L) ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
            (ModuleCat.restrictScalarsComp'.{max u v r w} (O.map f).hom (O.map g).hom
              (O.map (f ≫ g)).hom hfg)).inv.app (DerivedCategory.Q.obj L) := rfl
  have h' : (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (ModuleCat.restrictScalarsComp'.{max u v r w} (O.map f).hom (O.map g).hom
          (O.map (f ≫ g)).hom hfg)).inv.app (DerivedCategory.Q.obj L) =
      (ModuleCat.restrictScalars.{max u v r w} (O.map g).hom ⋙
          ModuleCat.restrictScalars.{max u v r w}
            (O.map f).hom).mapDerivedCategoryFactors.hom.app L ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (ModuleCat.restrictScalarsComp'.{max u v r w} (O.map f).hom (O.map g).hom
              (O.map (f ≫ g)).hom hfg) (ComplexShape.up ℤ)).inv.app L) ≫
          (ModuleCat.restrictScalars.{max u v r w}
            (O.map (f ≫ g)).hom).mapDerivedCategoryFactors.inv.app L := by
    simp [Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso,
      Localization.Lifting.iso]
  rw [h, Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q, h']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- **`dRestrictTerminalIso` on a localized complex.** It is assembled from the canonical
factorizations of the derived functors of restriction of scalars along `a`, along `ρ_V` and along
`ρ_U`, and the degreewise composition isomorphism of restriction of scalars along
`R → O(V) → O(U)`. -/
lemma dRestrictTerminalIso_hom_app_Q {U V : C} (a : Opposite.op V ⟶ Opposite.op U)
    (L : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op U))) ℤ) :
    (dRestrictTerminalIso.{w} O hX a).hom.app (DerivedCategory.Q.obj L) =
      (DRestrict.{w} O (hX.from V).op).map
          ((ModuleCat.restrictScalars.{max u v r w}
            (O.map a).hom).mapDerivedCategoryFactors.hom.app L) ≫
        (ModuleCat.restrictScalars.{max u v r w}
            (rho O hX (Opposite.op V))).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (ModuleCat.restrictScalarsComp'.{max u v r w} (rho O hX (Opposite.op V))
                (O.map a).hom (rho O hX (Opposite.op U)) (rho_comp O hX a).symm)
              (ComplexShape.up ℤ)).inv.app L) ≫
            (ModuleCat.restrictScalars.{max u v r w}
              (rho O hX (Opposite.op U))).mapDerivedCategoryFactors.inv.app L := by
  rw [dRestrictTerminalIso_hom_app]
  exact dRestrictCompIso_hom_app_Q.{w} O (hX.from V).op a (hX.from U).op (from_op_comp hX a)
    (rho_comp O hX a).symm L

/-- **The degreewise compatibility of the units of extension and restriction of scalars with the
restriction maps, on complexes.** The componentwise statement of
`extendRestrictScalarsAdj_unit_comp_baseChangePresheaf_map`. -/
lemma mapHomologicalComplex_unit_comp_restriction {U V : C}
    (a : Opposite.op V ⟶ Opposite.op U)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj.{max u v r w, r, r}
            (rho O hX (Opposite.op V))).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K ≫
        ((ModuleCat.restrictScalars.{max u v r w} (rho O hX (Opposite.op V))
            ).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O a)
              (ComplexShape.up ℤ)).app
              (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)) ≫
          (NatIso.mapHomologicalComplex
              (ModuleCat.restrictScalarsComp'.{max u v r w} (rho O hX (Opposite.op V))
                (O.map a).hom (rho O hX (Opposite.op U)) (rho_comp O hX a).symm)
              (ComplexShape.up ℤ)).inv.app
            (((ModuleCat.extendScalars.{r, r, max u v r w}
              (rho O hX (Opposite.op U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      ((ModuleCat.extendRestrictScalarsAdj.{max u v r w, r, r}
        (rho O hX (Opposite.op U))).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K :=
  HomologicalComplex.hom_ext _ _ fun i =>
    extendRestrictScalarsAdj_unit_comp_baseChangePresheaf_map.{w} O hX a (K.X i)

omit [CommSections O] in
/-- Cancelling the component of an isomorphism of functors against its inverse at the end of a
composite of three morphisms. -/
lemma comp_inv_app_comp_hom_app {D₁ D₂ : Type*} [Category D₁] [Category D₂] {F G : D₁ ⥤ D₂}
    (e : F ≅ G) (Y : D₁) {Z₀ Z₁ Z₂ : D₂} (g₁ : Z₀ ⟶ Z₁) (g₂ : Z₁ ⟶ Z₂) (g₃ : Z₂ ⟶ G.obj Y) :
    (g₁ ≫ g₂ ≫ g₃ ≫ e.inv.app Y) ≫ e.hom.app Y = g₁ ≫ g₂ ≫ g₃ := by
  simp

/-- **The derived restriction map on a localized complex, moved past the comparison with extension
of scalars.** The restriction map along `a` on the derived sections of `Lf^*` at a localized
complex, followed by the comparison exhibiting those sections over `U` as extension of scalars and
then by the canonical factorization of the derived functor of restriction of scalars along `a`, is
the comparison over `V` followed by the degreewise restriction of sections of the base change
presheaf. -/
lemma restrictionMap_comp_restrictScalarsFactors_hom_app {U V : C}
    (a : Opposite.op V ⟶ Opposite.op U)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    (restrictionMap.{w} O a ((Lpullback.{w} O hX).obj (DerivedCategory.Q.obj K)) ≫
          (DRestrict.{w} O a).map ((sectionsComparison.{w} O hX (Opposite.op U)).app K)) ≫
        (ModuleCat.restrictScalars.{max u v r w}
            (O.map a).hom).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{r, r, max u v r w}
            (rho O hX (Opposite.op U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (sectionsComparison.{w} O hX (Opposite.op V)).app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (PresheafOfModules.restriction O a) (ComplexShape.up ℤ)).app
          (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) := by
  refine (congrArg (· ≫ (ModuleCat.restrictScalars.{max u v r w}
        (O.map a).hom).mapDerivedCategoryFactors.hom.app
      (((ModuleCat.extendScalars.{r, r, max u v r w}
        (rho O hX (Opposite.op U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (restrictionMap_Lpullback_sectionsComparison.{w} O hX a K)).trans ?_
  refine (comp_inv_app_comp_hom_app (ModuleCat.restrictScalars.{max u v r w}
      (O.map a).hom).mapDerivedCategoryFactors
    (((ModuleCat.extendScalars.{r, r, max u v r w}
      (rho O hX (Opposite.op U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    _ _ _).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (sectionsComparison_app_Q.{w} O hX (Opposite.op V) K).symm)

omit [CommSections O] in
/-- Two factorizations of one morphism have the same image under a functor, up to a common
postcomposition. -/
lemma map_comp_congr_assoc {E D : Type*} [Category E] [Category D] (M : E ⥤ D)
    {P₀ P₁ P₁' P₂ : E} {T : D} (p : P₀ ⟶ P₁) (q : P₁ ⟶ P₂) (p' : P₀ ⟶ P₁') (q' : P₁' ⟶ P₂)
    (h : p ≫ q = p' ≫ q') (t : M.obj P₂ ⟶ T) :
    M.map p ≫ M.map q ≫ t = M.map p' ≫ M.map q' ≫ t := by
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc]

omit [CommSections O] in
/-- **A diagram chase.** Given a morphism `u ≫ m` factored as `e₁ ≫ i₁`, a morphism `i₁ ≫ n`
factored as `e₂ ≫ i₂`, a retraction `h` of `i₂` and a factorization of `eta` as `e₁ ≫ e₂ ≫ q`,
the composite `u ≫ m ≫ n ≫ h ≫ q` is `eta`. -/
lemma comp_eq_of_factorizations {D : Type*} [Category D] {A B₀ B₁ B₂ C₁ C₂ B₄ B₅ : D}
    (u : A ⟶ B₀) (m : B₀ ⟶ B₁) (n : B₁ ⟶ B₂) (h : B₂ ⟶ C₂) (q : C₂ ⟶ B₄) (k : B₄ ⟶ B₅)
    (e₁ : A ⟶ C₁) (i₁ : C₁ ⟶ B₁) (e₂ : C₁ ⟶ C₂) (i₂ : C₂ ⟶ B₂) (eta : A ⟶ B₄)
    (F1 : u ≫ m = e₁ ≫ i₁) (F2 : i₁ ≫ n = e₂ ≫ i₂) (F3 : i₂ ≫ h = 𝟙 C₂)
    (F4 : e₁ ≫ e₂ ≫ q = eta) :
    u ≫ m ≫ n ≫ h ≫ q ≫ k = eta ≫ k := by
  rw [← F4, reassoc_of% F1, reassoc_of% F2, reassoc_of% F3, Category.assoc, Category.assoc]

/-- **The restriction map on the derived sections of `Lf^*` at a localized complex, followed by the
transport along the terminal-object identity.** The composite is the comparison over `V` and the
degreewise restriction of sections, read through the canonical factorizations of the derived
functors of restriction of scalars along `a` and along `ρ_V`, and the degreewise composition
isomorphism of restriction of scalars along `R → O(V) → O(U)`. -/
lemma map_restrictionMap_comp_dRestrictTerminalIso_hom_app_Q {U V : C}
    (a : Opposite.op V ⟶ Opposite.op U)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    (DRestrict.{w} O (hX.from V).op).map
          (restrictionMap.{w} O a ((Lpullback.{w} O hX).obj (DerivedCategory.Q.obj K)) ≫
            (DRestrict.{w} O a).map ((sectionsComparison.{w} O hX (Opposite.op U)).app K)) ≫
        (dRestrictTerminalIso.{w} O hX a).hom.app (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{r, r, max u v r w}
            (rho O hX (Opposite.op U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      (DRestrict.{w} O (hX.from V).op).map
          ((sectionsComparison.{w} O hX (Opposite.op V)).app K) ≫
        (DRestrict.{w} O (hX.from V).op).map (DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O a)
              (ComplexShape.up ℤ)).app
              (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K))) ≫
          (ModuleCat.restrictScalars.{max u v r w}
              (rho O hX (Opposite.op V))).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              (((ModuleCat.extendScalars.{r, r, max u v r w}
                (rho O hX (Opposite.op U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
                (ModuleCat.restrictScalarsComp'.{max u v r w} (rho O hX (Opposite.op V))
                  (O.map a).hom (rho O hX (Opposite.op U)) (rho_comp O hX a).symm)
                (ComplexShape.up ℤ)).inv.app
              (((ModuleCat.extendScalars.{r, r, max u v r w}
                (rho O hX (Opposite.op U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
              (ModuleCat.restrictScalars.{max u v r w}
                  (rho O hX (Opposite.op U))).mapDerivedCategoryFactors.inv.app
                (((ModuleCat.extendScalars.{r, r, max u v r w}
                  (rho O hX (Opposite.op U))).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K) := by
  rw [dRestrictTerminalIso_hom_app_Q]
  exact map_comp_congr_assoc (DRestrict.{w} O (hX.from V).op) _ _ _ _
    (restrictionMap_comp_restrictScalarsFactors_hom_app.{w} O hX a K) _

omit [CommSections O] in
/-- A functor applied to a composite of three morphisms. -/
lemma map_comp₃ {E D : Type*} [Category E] [Category D] (F : E ⥤ D) {Z₀ Z₁ Z₂ Z₃ : E}
    (f : Z₀ ⟶ Z₁) (g : Z₁ ⟶ Z₂) (h : Z₂ ⟶ Z₃) (k : Z₀ ⟶ Z₃) (hk : f ≫ g ≫ h = k) :
    F.map f ≫ F.map g ≫ F.map h = F.map k := by
  rw [← hk, F.map_comp, F.map_comp]

/-- **The two natural transformations agree on a localized complex, after the comparison.**
Composed with the comparison exhibiting the derived sections over `U` followed by derived
restriction of scalars along `ρ_U` as a total left derived functor, the unit of the derived
sections adjunction over `V` corrected by the restriction map agrees with the unit over `U`. -/
lemma unitRestrictionNat_app_Q_comp {U V : C} (a : Opposite.op V ⟶ Opposite.op U)
    (K : CochainComplex (ModuleCat.{max u v r w} (O.obj (Opposite.op X))) ℤ) :
    (unitRestrictionNat.{w} O hX a).app (DerivedCategory.Q.obj K) ≫
        (sectionsRestrictComparison.{w} O hX U).app K =
      (sectionsAdj.{w} O hX U).unit.app (DerivedCategory.Q.obj K) ≫
        (sectionsRestrictComparison.{w} O hX U).app K := by
  rw [sectionsRestrictComparison_app,
    unitRestrictionNat_app_comp.{w} O hX a (DerivedCategory.Q.obj K)
      (N := DerivedCategory.Q.obj (((ModuleCat.extendScalars.{r, r, max u v r w}
        (rho O hX (Opposite.op U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      ((sectionsComparison.{w} O hX (Opposite.op U)).app K),
    map_restrictionMap_comp_dRestrictTerminalIso_hom_app_Q, sectionsAdj_unit_app_Q.{w} O hX U K]
  have hnat := ((ModuleCat.restrictScalars.{max u v r w}
      (rho O hX (Opposite.op V))).mapDerivedCategoryFactors.inv.naturality
    ((NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O a)
      (ComplexShape.up ℤ)).app
      (((baseChangePresheaf.{max u v w} O hX).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))).symm
  exact comp_eq_of_factorizations _ _ _ _ _ _ _ _ _ _ _ (sectionsAdj_unit_app_Q.{w} O hX V K) hnat
    (Iso.inv_hom_id_app _ _)
    (map_comp₃ DerivedCategory.Q _ _ _ _
      (mapHomologicalComplex_unit_comp_restriction.{w} O hX a K))

/-- The restriction of `unitRestrictionNat` and of the unit over `U` along the localization agree
after the comparison exhibiting the target as a total left derived functor. -/
lemma unitRestrictionNat_whiskerLeft_comp {U V : C} (a : Opposite.op V ⟶ Opposite.op U) :
    Functor.whiskerLeft DerivedCategory.Q (unitRestrictionNat.{w} O hX a) ≫
        sectionsRestrictComparison.{w} O hX U =
      Functor.whiskerLeft DerivedCategory.Q (sectionsAdj.{w} O hX U).unit ≫
        sectionsRestrictComparison.{w} O hX U := by
  ext K
  exact unitRestrictionNat_app_Q_comp.{w} O hX a K

/-- **The unit of the derived sections adjunction is compatible with the restriction maps.** The
unit over `V`, followed by the canonical derived restriction map along `a` and the composition
isomorphism of derived restriction of scalars, is the unit over `U`: both are natural
transformations into a total left derived functor agreeing on localized complexes. -/
lemma unitRestrictionNat_eq {U V : C} (a : Opposite.op V ⟶ Opposite.op U) :
    unitRestrictionNat.{w} O hX a = (sectionsAdj.{w} O hX U).unit := by
  have := isLeftDerivedFunctor_sectionsRestrictComparison.{w} O hX U
  exact Functor.leftDerived_ext _ (sectionsRestrictComparison.{w} O hX U)
    (sectionsQuasiIso.{w} O (Opposite.op X)) _ _ _
    (unitRestrictionNat_whiskerLeft_comp.{w} O hX a)

/-- The adjoint transpose under the derived sections adjunction over `V` of the canonical derived
restriction map on `RΓ(U, Lf^*P)` is the unit of the derived sections adjunction over `U`. -/
lemma unit_restriction_compat {U V : C} (a : Opposite.op V ⟶ Opposite.op U)
    (P : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X)))) :
    (sectionsAdj.{w} O hX V).unit.app P ≫
        (DRestrict.{w} O (hX.from V).op).map
            (restrictionMap.{w} O a ((Lpullback.{w} O hX).obj P)) ≫
          (dRestrictCompIso.{r, u, v, w} O (hX.from V).op a).hom.app
              ((Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U)).obj P) ≫
            eqToHom (Functor.congr_obj
              (congrArg (fun g : Opposite.op X ⟶ Opposite.op U => DRestrict.{w} O g)
                (from_op_comp hX a))
              ((Lpullback.{w} O hX ⋙ RGamma.{w} O (Opposite.op U)).obj P)) =
      (sectionsAdj.{w} O hX U).unit.app P := by
  rw [← unitRestrictionNat_eq.{w} O hX a, unitRestrictionNat_app,
    dRestrictTerminalIso_hom_app]

/-- **The canonical comparison map at `Lf^*P` is the base-change-of-base-change isomorphism.**
This is the compatibility of `pullbackIso` with the canonical restriction maps. -/
lemma comparisonCompat (bc : BaseChangeData.{w} O)
    (hcomp : ∀ {Z V' U' : Cᵒᵖ} (b : Z ⟶ V') (a : V' ⟶ U'),
      (conjugateEquiv ((bc.baseChangeAdj b).comp (bc.baseChangeAdj a))
          (bc.baseChangeAdj (b ≫ a))).symm (dRestrictCompIso.{r, u, v, w} O b a).hom =
        (bc.baseChangeComp b a).hom)
    {U V : C} (a : Opposite.op V ⟶ Opposite.op U)
    (P : DerivedCategory (ModuleCat.{max u v r w} (O.obj (Opposite.op X)))) :
    comparison.{w} bc a ((Lpullback.{w} O hX).obj P) =
      pullbackComparisonIso.{w} bc hX (Lpullback.{w} O hX) (pullbackIso.{w} O hX bc) a P := by
  have h := mate_eq_of_unit_eq.{w} O bc (hX.from V).op a (hX.from U).op (from_op_comp hX a)
    (hcomp _ a) (sectionsAdj.{w} O hX V) (sectionsAdj.{w} O hX U) P
    (restrictionMap.{w} O a ((Lpullback.{w} O hX).obj P))
    (unit_restriction_compat.{w} O hX a P)
  rw [comparison, Equiv.symm_apply_eq, h, Adjunction.homEquiv_unit, pullbackComparisonIso]
  conv_rhs => rw [Functor.map_comp]
  rw [reassoc_of% ((bc.baseChangeAdj a).unit_naturality
    ((pullbackIso.{w} O hX bc V).hom.app P))]
  rfl

/-- **The morphism of sites `f : (C, O) → (pt, R)` of a terminal object `X`, with `R = O(X)`, at a
base-change datum whose composition isomorphism is the canonical one.** The derived pullback is the
total left derived functor of base change along the canonical maps out of `X`, the adjunction is
`pullbackAdj`, the computation of its derived sections is `pullbackIso`, and the compatibility with
the canonical comparison maps is `comparisonCompat`. -/
def morphismOfSitesOfComp (bc : BaseChangeData.{w} O)
    (hcomp : ∀ {Z V' U' : Cᵒᵖ} (b : Z ⟶ V') (a : V' ⟶ U'),
      (conjugateEquiv ((bc.baseChangeAdj b).comp (bc.baseChangeAdj a))
          (bc.baseChangeAdj (b ≫ a))).symm (dRestrictCompIso.{r, u, v, w} O b a).hom =
        (bc.baseChangeComp b a).hom) :
    MorphismOfSites.{w} bc X hX where
  Lpullback := Lpullback.{w} O hX
  adj := pullbackAdj.{w} O hX
  pullbackIso := pullbackIso.{w} O hX bc
  comparisonCompat a P := comparisonCompat.{w} O hX bc hcomp a P

end Stacks.ModulesOnACategory.TerminalMorphismOfSites

namespace Stacks.ModulesOnACategory.TerminalMorphismOfSites

open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

/-- If all section rings of `O` are commutative, then `O` satisfies `CommSections`. -/
lemma commSections_of_comm (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x) :
    Stacks.TerminalBaseChange.CommSections O := ⟨hO⟩

variable (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x) {X : C} (hX : IsTerminal X)

/-- **The morphism of sites `f : (C, O) → (pt, O(X))` of a terminal object `X`, at the canonical
base-change datum `baseChangeDataOfComm`.** The derived pullback `Lf^*` is the total left derived
functor `Lpullback` of base change along the canonical maps out of `X`, with the adjunction to
`RΓ(X, -)`, the computation of its derived sections, and the compatibility of that computation
with the canonical comparison maps. -/
def morphismOfSites : MorphismOfSites.{w} (baseChangeDataOfComm.{r, v, u, w} O hO) X hX :=
  letI := commSections_of_comm O hO
  morphismOfSitesOfComp.{w} O hX (baseChangeDataOfComm.{r, v, u, w} O hO) fun _ _ => rfl

end Stacks.ModulesOnACategory.TerminalMorphismOfSites

end
