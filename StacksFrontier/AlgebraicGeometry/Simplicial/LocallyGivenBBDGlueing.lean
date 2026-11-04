module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenPullbackSummands
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.StructureSheafAugmentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleBoundedBelowEquivalenceUnconditional
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleCohomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PrescribedLowDegrees
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismOfSites
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
import StacksCore.Tactic.StacksAttribute

/-!
# The BBD glueing lemma

This file proves **Stacks 0DCB**. In Situation 0DC9, assume

1. `C` has equalizers and fibre products,
2. there is a morphism of sites `f : C ⟶ D` given by a continuous functor `u : D ⥤ C` such that
   `D` has equalizers and fibre products and `u` commutes with them, `B` is a full subcategory of
   `D` with `u : B ⥤ C` the restriction of `u`, and every object of `D` has a covering whose
   members are objects of `B`,
3. for all `U` in `B` all negative self-exts of `E_U` in `D(O_{u(U)})` are zero, and
4. there is a `t ∈ ℤ` with `H^i(E_U) = 0` for `i < t` and all `U`.

Then there exists a solution unique up to unique isomorphism.

## Main results

* `AlgebraicGeometry.RingedSite.LocallyGiven.exists_unique_solution`: **Stacks 0DCB**.

## Implementation notes

The proof is the source's. A hypercovering `L` of `D` with `L_0 ⊇ {U}_{U ∈ B}` and, for every
arrow `a : U ⟶ V` of `B`, a summand `U` of `L_1` with faces `a` and `id_U`
(`Stacks.CategoryTheory.Hypercovering.exists_hypercoveringOfTerminal_fullSubcategory`) is carried
to a hypercovering `K = u(L)` of `C` by Stacks 0DAY. Stacks 0DCA gives a cartesian `E` in `D(O)`
on `(C/K)_total` restricting to the `E_{U_{n,i}}`; hypothesis (4) puts `E` in `D^+`, and by
Stacks 0DA2 `E ≅ La^*F` with `F = Ra_*E`. The identifications `ρ_U` are read off the degree-zero
summands, and their compatibility off the degree-one summands, through the identification of the
summands of `La^*F` with the restrictions of `F`
(`AlgebraicGeometry.RingedSite.LocallyGiven.pullbackSummandIso_transition`). Uniqueness is the
uniqueness of Stacks 0DCA and the full faithfulness of `La^*` (Stacks 0DA0).

Rather than the identity arrows `id_U` of the source's argument — whose `ρ_{id}` would have to be
identified with the identity — every identification is transported along arrows of `B` with the
cocycle condition (`AlgebraicGeometry.RingedSite.LocallyGiven.transport`), and the two faces of a
degree-one summand give the compatibility directly.

## References

* [Stacks Project, Tag 0DCB](https://stacks.math.columbia.edu/tag/0DCB)
* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
* [Stacks Project, Tag 0DC9](https://stacks.math.columbia.edu/tag/0DC9)
* [Stacks Project, Tag 0DAX](https://stacks.math.columbia.edu/tag/0DAX)
* [Stacks Project, Tag 0DAY](https://stacks.math.columbia.edu/tag/0DAY)
* [Stacks Project, Tag 0DA2](https://stacks.math.columbia.edu/tag/0DA2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSemiRepresentable Stacks.CategoryTheory.Hypercovering Simplicial

universe u uB vB

namespace CategoryTheory

/-- **A transition compatibility of restriction identifications transports identifications of
the summands.** Given the compatibility `h` of a transition `dT` with identifications `Ψn`, `Ψm`,
`dπ`, `ω`, an isomorphism `ε : La(F) ≅ E` and identifications `σn`, `σm` of the summands of `E`
compatible with `dT` along `ρ`, the composite identifications
`τ = Ψ⁻¹ ≫ (summand of ε) ≫ σ` satisfy `τn = ω⁻¹ ≫ Rb(τm) ≫ ρ`. -/
theorem transport_of_transition {DC DT Dm Dn DUn DUm : Type*} [Category DC] [Category DT]
    [Category Dm] [Category Dn] [Category DUn] [Category DUm]
    (La : DC ⥤ DT) (Cm : DT ⥤ Dm) (Cn : DT ⥤ Dn) (LP : Dm ⥤ Dn) (Sn : Dn ⥤ DUn)
    (Sm : Dm ⥤ DUm) (Rb : DUm ⥤ DUn) (OU : DC ⥤ DUn) (OU' : DC ⥤ DUm)
    (dT : Cm ⋙ LP ⟶ Cn) (Ψn : La ⋙ Cn ⋙ Sn ≅ OU) (Ψm : La ⋙ Cm ⋙ Sm ≅ OU')
    (dπ : LP ⋙ Sn ≅ Sm ⋙ Rb) (ω : OU' ⋙ Rb ≅ OU)
    (h : ∀ F : DC, Sn.map (dT.app (La.obj F)) ≫ Ψn.hom.app F =
      dπ.hom.app (Cm.obj (La.obj F)) ≫ Rb.map (Ψm.hom.app F) ≫ ω.hom.app F)
    {F : DC} {E : DT} (ε : La.obj F ≅ E) {En : DUn} {Em : DUm}
    (σn : Sn.obj (Cn.obj E) ≅ En) (σm : Sm.obj (Cm.obj E) ≅ Em) (ρ : Rb.obj Em ≅ En)
    (hσ : Sn.map (dT.app E) ≫ σn.hom = dπ.hom.app (Cm.obj E) ≫ Rb.map σm.hom ≫ ρ.hom) :
    ((Ψn.app F).symm ≪≫ Sn.mapIso (Cn.mapIso ε) ≪≫ σn).hom =
      ω.inv.app F ≫ Rb.map ((Ψm.app F).symm ≪≫ Sm.mapIso (Cm.mapIso ε) ≪≫ σm).hom ≫ ρ.hom := by
  have h₁ : ω.hom.app F ≫ Ψn.inv.app F =
      Rb.map (Ψm.inv.app F) ≫ dπ.inv.app (Cm.obj (La.obj F)) ≫ Sn.map (dT.app (La.obj F)) := by
    rw [← cancel_epi (Rb.map (Ψm.hom.app F)), ← cancel_epi (dπ.hom.app (Cm.obj (La.obj F)))]
    simp only [← Category.assoc, ← h]
    simp [← Functor.map_comp]
  have h₂ := dT.naturality ε.hom
  have h₃ := dπ.hom.naturality (Cm.map ε.hom)
  simp only [Functor.comp_map] at h₂ h₃
  rw [← cancel_epi (ω.hom.app F), Iso.hom_inv_id_app_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  calc ω.hom.app F ≫ Ψn.inv.app F ≫ Sn.map (Cn.map ε.hom) ≫ σn.hom
      = Rb.map (Ψm.inv.app F) ≫ dπ.inv.app (Cm.obj (La.obj F)) ≫
          Sn.map (dT.app (La.obj F)) ≫ Sn.map (Cn.map ε.hom) ≫ σn.hom := by
        rw [reassoc_of% h₁]
    _ = Rb.map (Ψm.inv.app F) ≫ dπ.inv.app (Cm.obj (La.obj F)) ≫
          Sn.map (LP.map (Cm.map ε.hom)) ≫ Sn.map (dT.app E) ≫ σn.hom := by
        rw [← Sn.map_comp_assoc, ← h₂, Sn.map_comp_assoc]
    _ = Rb.map (Ψm.inv.app F) ≫ dπ.inv.app (Cm.obj (La.obj F)) ≫
          Sn.map (LP.map (Cm.map ε.hom)) ≫ dπ.hom.app (Cm.obj E) ≫ Rb.map σm.hom ≫ ρ.hom := by
        rw [hσ]
    _ = Rb.map (Ψm.inv.app F) ≫ Rb.map (Sm.map (Cm.map ε.hom)) ≫ Rb.map σm.hom ≫ ρ.hom := by
        rw [reassoc_of% h₃, Iso.inv_hom_id_app_assoc]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

attribute [local instance] HasDerivedCategory.standard

/-- **A sheaf of `O`-modules on the total site vanishes if its restrictions to all components
do.** -/
theorem isZero_of_forall_isZero_componentModulesRestriction (M : (S.totalRingedTopos O).Modules)
    (h : ∀ n, IsZero ((S.componentModulesRestriction O n).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun Y ↦ ?_)
  obtain ⟨X⟩ := Y
  rw [← S.inclusion_obj_totalObjFibre X]
  have e : (S.componentModulesRestriction O (S.totalObjDegree X)).map (𝟙 M) =
      (S.componentModulesRestriction O (S.totalObjDegree X)).map 0 := by
    rw [Functor.map_id, Functor.map_zero]
    exact (h _).eq_of_src _ _
  exact ModuleCat.hom_ext (LinearMap.ext fun x ↦
    congrArg (fun t ↦ (t.val.app (op (S.totalObjFibre X))).hom x) e)

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSemiRepresentable

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- **A sheaf of `O_n`-modules vanishes if its restrictions to all summands `C/U_{n,i}` do**, the
summand restrictions forming an equivalence with the product (Stacks 0D9U). -/
theorem isZero_of_forall_isZero_summandRestriction (n : SimplexCategory)
    (Z : SheafOfModules.{u} (componentRing X K n))
    (h : ∀ i, IsZero ((summandRestriction X K n i).obj Z)) : IsZero Z := by
  rw [IsZero.iff_id_eq_zero]
  apply (Functor.pi' (summandRestriction X K n)).map_injective
  funext i
  show (summandRestriction X K n i).map (𝟙 Z) = (summandRestriction X K n i).map 0
  rw [Functor.map_id, Functor.map_zero]
  exact (h i).eq_of_src _ _

end CategoryTheory.SimplicialSemiRepresentable

namespace AlgebraicGeometry.RingedSite.LocallyGiven

section Hypercovering

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (O : Sheaf P.toGrothendieck CommRingCat.{u}) (Y : HypercoveringOfTerminal.{u} P)

/-- **Stacks 0DA2, essential surjectivity, for the augmentation with the restricted structure
sheaf of a hypercovering**: the counit `La^*Ra_*E ⟶ E` is invertible on `D⁺_𝒜(O)`. -/
theorem isIso_structureCounit_of_hypercovering
    (E : DerivedCategory ((situation P.toGrothendieck Y.toSimplicialObject).totalRingedTopos
      (structureSheaf (pretopologyRingedSite P O) Y.toSimplicialObject)).Modules)
    (hE : RingedToposHom.derivedPlusProperty
      (X := (situation P.toGrothendieck Y.toSimplicialObject).totalRingedTopos
        (structureSheaf (pretopologyRingedSite P O) Y.toSimplicialObject))
      ((situation P.toGrothendieck Y.toSimplicialObject).IsModuleFiberTransitionIso
        (structureSheaf (pretopologyRingedSite P O) Y.toSimplicialObject)) E) :
    IsIso ((RingedToposHom.derivedAdjunctionOfIsIsoFSharp
      (structureAugmentation (pretopologyRingedSite P O)
        Y.toSimplicialObject).totalRingedHom).counit.app E) := by
  refine SimplicialSiteSituation.RingedAugmentation.isIso_derivedCounit_app_of_hypercovering Y
    (structureAugmentation (pretopologyRingedSite P O) Y.toSimplicialObject) E ?_
  convert hE using 3
  dsimp only [structureAugmentation_O]
  exact Iff.rfl

end Hypercovering

end AlgebraicGeometry.RingedSite.LocallyGiven

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent
  RingedSite.overFunctor_preservesFiniteLimits' RingedSite.overFunctor_preservesFiniteColimits'

namespace AlgebraicGeometry.RingedSite.LocallyGiven

attribute [local instance] LocallyGiven.category

/-- Sheafification is available in any module universe containing the site. -/
local instance (priority := 100) bbdGlueingSheafification.{uM, w, v}
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{w, uM}] [UnivLE.{v, uM}] : HasSheafify J AddCommGrpCat.{uM} :=
  hasSheafifyEssentiallySmallSite.{v, uM, w, uM + 1, uM} J _

/-- In the module universe, sheafification equivalences are the locally bijective maps. -/
local instance (priority := 100) bbdGlueingLocallyBijective.{uM, w, v}
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{w, uM}] [UnivLE.{v, uM}] : J.WEqualsLocallyBijective AddCommGrpCat.{uM} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, uM, w, uM + 1, uM} J

section Transport

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  (G : LocallyGiven.{0, u, u, u, uB, vB} X)

/-- **The comparisons `(F|_{C/U})|_{C/V} = F|_{C/V}` compose**: along `b : W ⟶ V` and `c : V ⟶ U`
of `B`, the comparison along `u(b ∘ c)` is the comparison along `u(c)` restricted to `u(W)`
followed by the comparison along `u(b)`, through the comparison of restrictions of
Situation 0DC9. -/
theorem derivedOverFunctorMapIso_comp {W V U : G.B} (b : W ⟶ V) (c : V ⟶ U)
    (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (G.restrictionComp b c).inv.app ((derivedOverFunctor X (G.u.obj U)).obj N) ≫
        (derivedOverFunctorMapIso X (G.u.map (b ≫ c))).hom.app N =
      (G.restriction b).map ((derivedOverFunctorMapIso X (G.u.map c)).hom.app N) ≫
        (derivedOverFunctorMapIso X (G.u.map b)).hom.app N :=
  let := G.restrictionAdditive b
  let := G.restrictionAdditive c
  let := G.restrictionAdditive (b ≫ c)
  have := overMap_preservesFiniteLimits.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G.u.map b)
  have := overMap_preservesFiniteColimits.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G.u.map b)
  have := overMap_preservesFiniteLimits.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G.u.map c)
  have := overMap_preservesFiniteColimits.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G.u.map c)
  have := overMap_preservesFiniteLimits.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G.u.map (b ≫ c))
  have := overMap_preservesFiniteColimits.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G.u.map (b ≫ c))
  CategoryTheory.derivedCompLiftIso_comp
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.obj U))
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.obj V))
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.obj W))
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.map c))
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.map b))
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.map (b ≫ c)))
    (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.map c))
    (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (G.u.map b))
    (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.map (b ≫ c)))
    (G.restrictionCompOrdinary b c).symm (G.restrictionComp b c)
    (G.restrictionComp_inv_isInducedBy b c)
    (fun M ↦ SheafOfModules.FixesSections.ext
      (SheafOfModules.FixesSections.comp
        (SheafOfModules.FixesSections.inv ((G.restrictionCompOrdinary b c).app _)
          (G.restrictionCompOrdinary_hom_app_fixesSections b c _))
        (overFunctorMap_hom_app_fixesSections X (G.u.map (b ≫ c)) M))
      (SheafOfModules.FixesSections.comp
        (overMap_map_fixesSections X (G.u.map b)
          (overFunctorMap_hom_app_fixesSections X (G.u.map c) M))
        (overFunctorMap_hom_app_fixesSections X (G.u.map b) M))) N

/-- **Transport of an identification along an arrow of `B`**: from `F|_{C/u(U)} ≅ E_U` and
`c : V ⟶ U`, the identification `F|_{C/u(V)} = (F|_{C/u(U)})|_{C/u(V)} ≅ E_U|_{C/u(V)} ≅ E_V`,
the last map being `ρ_c`. -/
def transport {V U : G.B} (c : V ⟶ U)
    {F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (τ : (derivedOverFunctor X (G.u.obj U)).obj F ≅ G.obj U) :
    (derivedOverFunctor X (G.u.obj V)).obj F ≅ G.obj V :=
  ((derivedOverFunctorMapIso X (G.u.map c)).app F).symm ≪≫ (G.restriction c).mapIso τ ≪≫ G.rho c

/-- **Transport along a composite is the composite of the transports**, by the cocycle
condition of Situation 0DC9. -/
theorem transport_comp {W V U : G.B} (b : W ⟶ V) (c : V ⟶ U)
    {F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (τ : (derivedOverFunctor X (G.u.obj U)).obj F ≅ G.obj U) :
    G.transport (b ≫ c) τ = G.transport b (G.transport c τ) := by
  have e : ((G.restrictionComp b c).app ((derivedOverFunctor X (G.u.obj U)).obj F)).symm ≪≫
      (derivedOverFunctorMapIso X (G.u.map (b ≫ c))).app F =
      (G.restriction b).mapIso ((derivedOverFunctorMapIso X (G.u.map c)).app F) ≪≫
        (derivedOverFunctorMapIso X (G.u.map b)).app F :=
    Iso.ext (G.derivedOverFunctorMapIso_comp b c F)
  have h' : (derivedOverFunctorMapIso X (G.u.map (b ≫ c))).inv.app F ≫
      (G.restrictionComp b c).hom.app ((derivedOverFunctor X (G.u.obj U)).obj F) =
      (derivedOverFunctorMapIso X (G.u.map b)).inv.app F ≫
        (G.restriction b).map ((derivedOverFunctorMapIso X (G.u.map c)).inv.app F) := by
    simpa using congrArg Iso.inv e
  have nat := (G.restrictionComp b c).hom.naturality τ.hom
  ext
  simp only [transport, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    G.cocycle b c, Functor.map_comp, Category.assoc]
  rw [reassoc_of% nat, ← Category.assoc ((derivedOverFunctorMapIso X (G.u.map (b ≫ c))).inv.app F),
    h']
  simp only [Category.assoc]

end Transport

section Bound

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  (G : LocallyGiven.{0, u, u, u, uB, vB} X) (L : SimplicialObject (FormalCoproduct.{u} G.B))

variable {G L} in
/-- **An object of `D(O)` restricting to uniformly bounded below objects is bounded below.** -/
theorem SummandIdentification.isBoundedBelow
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules} (σ : G.SummandIdentification L E)
    (hbound : ∃ t : ℤ, ∀ (U : G.B) (q : ℤ), q < t → IsZero
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (G.u.obj U))) q).obj
          (G.obj U))) :
    DerivedCategoryB.IsBoundedBelow E := by
  obtain ⟨t, ht⟩ := hbound
  refine ⟨t, fun q hq ↦ ?_⟩
  refine (situation X.J (G.image L)).isZero_of_forall_isZero_componentModulesRestriction
    (structureSheaf X (G.image L)) _ fun n ↦ ?_
  refine isZero_of_forall_isZero_summandRestriction X (G.image L) n _ fun i ↦ ?_
  refine (ht ((L.obj (op n)).obj i) q hq).of_iso ?_
  have : (G.summandRestrictionB L n i).Additive := G.summandRestrictionB_additive L n i
  have : PreservesFiniteLimits (G.summandRestrictionB L n i) :=
    G.summandRestrictionB_preservesFiniteLimits L n i
  have : PreservesFiniteColimits (G.summandRestrictionB L n i) :=
    G.summandRestrictionB_preservesFiniteColimits L n i
  exact (G.summandRestrictionB L n i).mapIso
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        ((situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L)) n)
        q).app E).symm ≪≫
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (G.summandRestrictionB L n i) q).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso (σ.iso n i)

variable {G L} in
/-- **An object of `D(O)` with a summandwise identification is cartesian**: its simplicial
system is isomorphic to the cartesian system of the locally given objects. -/
theorem SummandIdentification.isCartesian
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules} (σ : G.SummandIdentification L E) :
    (situation X.J (G.image L)).IsCartesianDerivedModule (structureSheaf X (G.image L)) E := by
  intro m n φ
  have hn := σ.systemIso.hom.naturality φ
  have hloc := G.localSystem_cartesian L φ
  let em :=
    (CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation m).mapIso
      σ.systemIso
  let en :=
    (CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem.evaluation n).mapIso
      σ.systemIso
  have : IsIso (((situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L))
      E).map φ ≫ en.hom) := by
    show IsIso (((situation X.J (G.image L)).derivedModuleSystem (structureSheaf X (G.image L))
      E).map φ ≫ σ.systemIso.hom.app n)
    rw [hn]
    have : IsIso (((situation X.J (G.image L)).derivedTransitionPullback
        (structureSheaf X (G.image L)) φ).map (σ.systemIso.hom.app m)) :=
      Functor.map_isIso _ em.hom
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ en.hom (Iso.isIso_hom en) this

/-- **The cohomology sheaves of a cartesian object of `D(O)` are cartesian** (Stacks 0D7L (2)),
in the form `IsModuleFiberTransitionIso`. -/
theorem homology_isModuleFiberTransitionIso
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules}
    (hE : (situation X.J (G.image L)).IsCartesianDerivedModule (structureSheaf X (G.image L)) E)
    (q : ℤ) :
    (situation X.J (G.image L)).IsModuleFiberTransitionIso (structureSheaf X (G.image L))
      ((DerivedCategory.homologyFunctor ((situation X.J (G.image L)).totalRingedTopos
        (structureSheaf X (G.image L))).Modules q).obj E) :=
  ((situation X.J (G.image L)).isModuleFiberTransitionIso_iff_isCartesianModule
    (structureSheaf X (G.image L)) _).2
    (((situation X.J (G.image L)).isCartesianDerivedModule_iff_forall_isCartesianModule_homology
      (structureSheaf X (G.image L))
      (fun _ i ↦ transitionRingedToposHom_isFlat X (G.image L) (SimplexCategory.δ i)) E).1 hE q)

end Bound


section Solutions

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  (G : LocallyGiven.{0, u, u, u, uB, vB} X)

omit [X.J.toCoverage.HasPullbacks] in
variable {G} in
/-- The identification of a solution at `V` is the transport of that at `U` along `c : V ⟶ U`. -/
theorem Solution.iso_eq_transport (S : G.Solution) {V U : G.B} (c : V ⟶ U) :
    S.iso V = G.transport c (S.iso U) :=
  Iso.ext (S.comm c).symm

omit [X.J.toCoverage.HasPullbacks] in
/-- Transport commutes with morphisms of the glued objects. -/
theorem transport_naturality {V U : G.B} (c : V ⟶ U)
    {F F' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : F ⟶ F') (τ : (derivedOverFunctor X (G.u.obj U)).obj F ≅ G.obj U)
    (τ' : (derivedOverFunctor X (G.u.obj U)).obj F' ≅ G.obj U)
    (h : (derivedOverFunctor X (G.u.obj U)).map e ≫ τ'.hom = τ.hom) :
    (derivedOverFunctor X (G.u.obj V)).map e ≫ (G.transport c τ').hom = (G.transport c τ).hom := by
  have hn := (derivedOverFunctorMapIso X (G.u.map c)).inv.naturality e
  simp only [Functor.comp_map] at hn
  simp only [transport, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, h]

end Solutions

section SolutionOfPullback

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  (G : LocallyGiven.{0, u, u, u, uB, vB} X) (L : SimplicialObject (FormalCoproduct.{u} G.B))
  (c : ∀ U : G.B, (FormalCoproduct.incl G.B).obj U ⟶ L.obj (op ⦋0⦌))

/-- **An object `E` glued from the `E_{U_{n,i}}` that is `La^*F` gives a solution `F`**: given
`L` with `L_0 ⊇ {U}_{U ∈ B}` (the arrows `c U`) and, for every arrow `a : U ⟶ V` of `B`, a summand
`U` of `L_1` with faces `a` and `id_U`, an identification `σ` of the summandwise restrictions of
`E` with the locally given objects compatible with the `ρ_a` (Stacks 0DCA) and an isomorphism
`ε : La^*F ≅ E`, the identifications `ρ_U : F|_{C/u(U)} ≅ E_U` read off `L_0` are compatible
along the arrows of `B`, read off `L_1`. This is the common last step of the proofs of Stacks
0DCB and 0DCC. -/
theorem nonempty_solution_of_structurePullback_iso
    (hc : ∀ {U V : G.B} (a : U ⟶ V), ∃ e : (FormalCoproduct.incl G.B).obj U ⟶ L.obj (op ⦋1⦌),
      e ≫ L.map (SimplexCategory.δ 0).op = (FormalCoproduct.incl G.B).map a ≫ c V ∧
        e ≫ L.map (SimplexCategory.δ 1).op = c U)
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules} (σ : G.SummandIdentification L E)
    {F : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (ε : (G.structurePullback L).obj F ≅ E) :
    Nonempty G.Solution := by
  let τ : ∀ (n : SimplexCategory) (j : (L.obj (op n)).I),
      (derivedOverFunctor X (G.u.obj ((L.obj (op n)).obj j))).obj F ≅
        G.obj ((L.obj (op n)).obj j) := fun n j ↦
    ((G.pullbackSummandIso L n j).app F).symm ≪≫
      (G.summandDerivedRestriction L n j).mapIso
        (((situation X.J (G.image L)).derivedComponentModuleRestriction
          (structureSheaf X (G.image L)) n).mapIso ε) ≪≫ σ.iso n j
  have hT : ∀ {m n : SimplexCategory} (φ : m ⟶ n) (j : (L.obj (op n)).I),
      τ n j = G.transport ((L.map φ.op).φ j) (τ m ((L.map φ.op).f j)) := by
    intro m n φ j
    refine Iso.ext ?_
    exact CategoryTheory.transport_of_transition (G.structurePullback L)
      ((situation X.J (G.image L)).derivedComponentModuleRestriction
        (structureSheaf X (G.image L)) m)
      ((situation X.J (G.image L)).derivedComponentModuleRestriction
        (structureSheaf X (G.image L)) n)
      ((situation X.J (G.image L)).derivedTransitionPullback
        (structureSheaf X (G.image L)) φ)
      (G.summandDerivedRestriction L n j) (G.summandDerivedRestriction L m ((L.map φ.op).f j))
      (G.restriction ((L.map φ.op).φ j))
      (derivedOverFunctor X (G.u.obj ((L.obj (op n)).obj j)))
      (derivedOverFunctor X
        (G.u.obj ((L.obj (op m)).obj ((L.map φ.op).f j))))
      ((situation X.J (G.image L)).derivedComponentModuleTransition
        (structureSheaf X (G.image L)) φ)
      (G.pullbackSummandIso L n j) (G.pullbackSummandIso L m ((L.map φ.op).f j))
      (G.summandDerivedPullbackIso L φ j)
      (derivedOverFunctorMapIso X (G.u.map ((L.map φ.op).φ j)))
      (G.pullbackSummandIso_transition L φ j) ε (σ.iso n j) (σ.iso m ((L.map φ.op).f j))
      (G.rho ((L.map φ.op).φ j)) (σ.comm φ j)
  let Θ : ∀ {n : SimplexCategory} {W : G.B},
      ((FormalCoproduct.incl G.B).obj W ⟶ L.obj (op n)) →
        ((derivedOverFunctor X (G.u.obj W)).obj F ≅ G.obj W) :=
    fun {n W} γ ↦ G.transport (γ.φ PUnit.unit) (τ n (γ.f PUnit.unit))
  have hΘ : ∀ {m n : SimplexCategory} (φ : m ⟶ n) {W : G.B}
      (γ : (FormalCoproduct.incl G.B).obj W ⟶ L.obj (op n)), Θ (γ ≫ L.map φ.op) = Θ γ := by
    intro m n φ W γ
    show G.transport (γ.φ PUnit.unit ≫ (L.map φ.op).φ (γ.f PUnit.unit))
        (τ m ((L.map φ.op).f (γ.f PUnit.unit))) =
      G.transport (γ.φ PUnit.unit) (τ n (γ.f PUnit.unit))
    exact (G.transport_comp _ _ _).trans (congrArg (G.transport (γ.φ PUnit.unit)) (hT φ _).symm)
  refine ⟨{ obj := F, iso := fun U ↦ Θ (c U), comm := fun {V U} a ↦ ?_ }⟩
  obtain ⟨e, he₀, he₁⟩ := hc a
  have h₁ : Θ (c V) = G.transport a (Θ (c U)) := by
    rw [← he₁, hΘ, ← hΘ (SimplexCategory.δ 0) e, he₀]
    show G.transport (a ≫ (c U).φ PUnit.unit) (τ _ ((c U).f PUnit.unit)) = _
    exact G.transport_comp _ _ _
  rw [h₁]
  rfl

end SolutionOfPullback

section Main

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (PC : Pretopology C)
  (O : Sheaf PC.toGrothendieck CommRingCat.{u})
  (G : LocallyGiven.{0, u, u, u, u, u} (pretopologyRingedSite PC O))
  (L : SimplicialObject (FormalCoproduct.{u} G.B))
  (c : ∀ U : G.B, (FormalCoproduct.incl G.B).obj U ⟶ L.obj (op ⦋0⦌))

/-- **Existence in Stacks 0DCB**, given the hypercovering `u(L)` of the proof. -/
theorem nonempty_solution_of_hypercovering
    (hc : ∀ {U V : G.B} (a : U ⟶ V), ∃ e : (FormalCoproduct.incl G.B).obj U ⟶ L.obj (op ⦋1⦌),
      e ≫ L.map (SimplexCategory.δ 0).op = (FormalCoproduct.incl G.B).map a ≫ c V ∧
        e ≫ L.map (SimplexCategory.δ 1).op = c U)
    (Y : HypercoveringOfTerminal.{u} PC) (hY : Y.toSimplicialObject = G.image L)
    (hneg : ∀ (U : G.B) (t : ℤ), 0 < t →
      ∀ g : (shiftFunctor (LocalDerivedCategory.{0} (pretopologyRingedSite PC O) (G.u.obj U)) t).obj
        (G.obj U) ⟶ G.obj U, g = 0)
    (hbound : ∃ t : ℤ, ∀ (U : G.B) (q : ℤ), q < t → IsZero
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf O).over (G.u.obj U))) q).obj (G.obj U))) :
    Nonempty G.Solution := by
  obtain ⟨K', a₀, a₁, a₂, a₃⟩ := Y
  dsimp only at hY
  subst hY
  let Y : HypercoveringOfTerminal.{u} PC := ⟨G.image L, a₀, a₁, a₂, a₃⟩
  obtain ⟨⟨E, hE, ⟨σ⟩⟩, -⟩ := G.exists_unique_cartesian_summandIdentification L hneg
  have hiso := isIso_structureCounit_of_hypercovering PC O Y E (by
    refine ⟨?_, fun q ↦ ?_⟩
    · convert σ.isBoundedBelow hbound using 1
    · convert G.homology_isModuleFiberTransitionIso L hE q using 1)
  exact G.nonempty_solution_of_structurePullback_iso L c hc σ
    (asIso ((RingedToposHom.derivedAdjunctionOfIsIsoFSharp (G.augmentationHom L)).counit.app E))

include c in
/-- **Uniqueness in Stacks 0DCB**, given the hypercovering `u(L)` of the proof: two solutions are
identified by exactly one isomorphism compatible with their identifications. -/
theorem existsUnique_compatibleIso_of_hypercovering
    (Y : HypercoveringOfTerminal.{u} PC) (hY : Y.toSimplicialObject = G.image L)
    (hneg : ∀ (U : G.B) (t : ℤ), 0 < t →
      ∀ g : (shiftFunctor (LocalDerivedCategory.{0} (pretopologyRingedSite PC O) (G.u.obj U)) t).obj
        (G.obj U) ⟶ G.obj U, g = 0)
    (S S' : G.Solution) : ∃! e : S.obj ≅ S'.obj, Solution.IsCompatibleIso G e := by
  obtain ⟨K', a₀, a₁, a₂, a₃⟩ := Y
  dsimp only at hY
  subst hY
  let Y : HypercoveringOfTerminal.{u} PC := ⟨G.image L, a₀, a₁, a₂, a₃⟩
  obtain ⟨-, huniq⟩ := G.exists_unique_cartesian_summandIdentification L hneg
  let σ := S.summandIdentification L
  let σ' := S'.summandIdentification L
  obtain ⟨ε, hε, hεu⟩ := huniq _ _ σ.isCartesian σ'.isCartesian σ σ'
  let hff : (G.structurePullback L).FullyFaithful :=
    SimplicialSiteSituation.RingedAugmentation.derivedPullbackFullyFaithfulOfHypercovering Y
      (structureAugmentation (pretopologyRingedSite PC O) Y.toSimplicialObject)
  have hn : ∀ (e : S.obj ⟶ S'.obj) (n : SimplexCategory) (i : (L.obj (op n)).I),
      (G.summandDerivedRestriction L n i).map
        (((situation PC.toGrothendieck (G.image L)).derivedComponentModuleRestriction
          (structureSheaf (pretopologyRingedSite PC O) (G.image L)) n).map
            ((G.structurePullback L).map e)) ≫ (G.pullbackSummandIso L n i).hom.app S'.obj =
      (G.pullbackSummandIso L n i).hom.app S.obj ≫
        (derivedOverFunctor (pretopologyRingedSite PC O) (G.u.obj ((L.obj (op n)).obj i))).map e :=
    fun e n i ↦ (G.pullbackSummandIso L n i).hom.naturality e
  have fwd : ∀ e : S.obj ≅ S'.obj, Solution.IsCompatibleIso G e →
      ∀ (n : SimplexCategory) (i : (L.obj (op n)).I),
        (G.summandDerivedRestriction L n i).map
          (((situation PC.toGrothendieck (G.image L)).derivedComponentModuleRestriction
            (structureSheaf (pretopologyRingedSite PC O) (G.image L)) n).map
              ((G.structurePullback L).map e.hom)) ≫ (σ'.iso n i).hom = (σ.iso n i).hom := by
    intro e he n i
    show _ ≫ (G.pullbackSummandIso L n i).hom.app S'.obj ≫ (S'.iso _).hom =
      (G.pullbackSummandIso L n i).hom.app S.obj ≫ (S.iso _).hom
    rw [reassoc_of% hn e.hom n i, he]
  refine ⟨hff.preimageIso ε, fun U ↦ ?_, fun e he ↦ ?_⟩
  · let j := (c U).f PUnit.unit
    have h₀ := hε ⦋0⦌ j
    have hn' := hn (hff.preimageIso ε).hom ⦋0⦌ j
    rw [show (G.structurePullback L).map (hff.preimageIso ε).hom = ε.hom from
      hff.map_preimage ε.hom] at hn'
    have hj : (derivedOverFunctor (pretopologyRingedSite PC O)
          (G.u.obj ((L.obj (op ⦋0⦌)).obj j))).map (hff.preimageIso ε).hom ≫
        (S'.iso ((L.obj (op ⦋0⦌)).obj j)).hom = (S.iso ((L.obj (op ⦋0⦌)).obj j)).hom := by
      refine (Iso.cancel_iso_hom_left ((G.pullbackSummandIso L ⦋0⦌ j).app S.obj) _ _).1 ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (S'.iso _).hom) hn'.symm).trans
        ((Category.assoc _ _ _).trans h₀))
    have key := G.transport_naturality ((c U).φ PUnit.unit) (hff.preimageIso ε).hom _ _ hj
    rw [← S.iso_eq_transport, ← S'.iso_eq_transport] at key
    exact key
  · have h := hεu ((G.structurePullback L).mapIso e) (fwd e he)
    refine Iso.ext (hff.map_injective ?_)
    exact (congrArg Iso.hom h).trans (hff.map_preimage ε.hom).symm

end Main


section BBD

/-- **Stacks 0DCB (BBD glueing lemma).** In Situation 0DC9 — a ringed site `(C, O_C)`, a category
`B` with a functor `u : B ⥤ C`, objects `E_U` of `D(O_{u(U)})` and isomorphisms
`ρ_a : E_U|_{C/u(V)} ⟶ E_V` satisfying the cocycle condition — assume

1. `C` has equalizers and fibre products;
2. there is a morphism of sites `f : C ⟶ D` given by a continuous functor `u : D ⥤ C` (here
   `f`, with `IsMorphismOfSites`), such that `D` has equalizers and fibre products and `u`
   commutes with them, `B` is a full subcategory of `D` (a fully faithful `i : B ⥤ D`) with
   `u : B ⥤ C` the restriction of `u` (`i ⋙ f = G.u`), and every object of `D` has a covering
   whose members are objects of `B`;
3. for all `U` in `B` all negative self-exts of `E_U` in `D(O_{u(U)})` are zero, that is,
   every map `E_U[t] ⟶ E_U` with `t > 0` vanishes;
4. there exists `t ∈ ℤ` with `H^i(E_U) = 0` for `i < t` and all `U`.

Then there exists a solution `(E, ρ_U)`, and it is unique up to unique isomorphism: between two
solutions there is exactly one isomorphism compatible with their identifications `ρ_U`. -/
@[stacks 0DCB]
theorem exists_unique_solution {X : RingedSite.{u, u, u}} [HasEqualizers X.C] [HasPullbacks X.C]
    (G : LocallyGiven.{0, u, u, u, u, u} X)
    {D : Type u} [SmallCategory D] [HasEqualizers D] [HasPullbacks D] (P : Pretopology D)
    (f : D ⥤ X.C) [IsMorphismOfSites.{u} f P.toGrothendieck X.J]
    [PreservesLimitsOfShape WalkingParallelPair f] [PreservesLimitsOfShape WalkingCospan f]
    (i : G.B ⥤ D) [i.Full] [i.Faithful] (hi : i ⋙ f = G.u)
    (hcover : ∀ V : D, ∃ (ι : Type u) (U : ι → G.B) (g : ∀ k, i.obj (U k) ⟶ V),
      Presieve.ofArrows (fun k ↦ i.obj (U k)) g ∈ P V)
    (hneg : ∀ (U : G.B) (t : ℤ), 0 < t →
      ∀ g : (shiftFunctor (LocalDerivedCategory.{0} X (G.u.obj U)) t).obj (G.obj U) ⟶ G.obj U,
        g = 0)
    (hbound : ∃ t : ℤ, ∀ (U : G.B) (q : ℤ), q < t → IsZero
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (G.u.obj U))) q).obj (G.obj U))) :
    Nonempty G.Solution ∧
      ∀ S S' : G.Solution, ∃! e : S.obj ≅ S'.obj, Solution.IsCompatibleIso G e := by
  obtain ⟨C, J, O⟩ := X
  have : HasPullbacks C := ‹HasPullbacks _›
  have : HasEqualizers C := ‹HasEqualizers _›
  revert O
  obtain ⟨PC, hPC⟩ : ∃ PC : Pretopology C, PC.toGrothendieck = J :=
    ⟨J.toPretopology, (Pretopology.gi (C := C)).l_u_eq J⟩
  subst hPC
  intro O _ _ G f _ _ _ i _ _ hi hcover hneg hbound
  obtain ⟨L, H, hH, c, hc⟩ := exists_hypercoveringOfTerminal_fullSubcategory P i
    (Functor.FullyFaithful.ofFullyFaithful i) hcover
  obtain ⟨Y, hY⟩ := exists_hypercovering_of_map PC P f H
  have hYL : Y.toSimplicialObject = G.image L := by
    rw [hY, hH, LocallyGiven.image, ← hi]
    rfl
  exact ⟨nonempty_solution_of_hypercovering PC O G L c hc Y hYL hneg hbound,
    existsUnique_compatibleIso_of_hypercovering PC O G L c Y hYL hneg⟩

end BBD

end AlgebraicGeometry.RingedSite.LocallyGiven

end
