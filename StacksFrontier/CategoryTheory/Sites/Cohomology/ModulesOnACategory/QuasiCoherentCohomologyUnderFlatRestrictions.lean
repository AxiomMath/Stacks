module

public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentability
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOnAChaoticSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Quasi-coherent cohomology of derived modules on a category

Let `C` be a category viewed as a site with the chaotic topology and let `O` be a sheaf of rings
on `C`.  The subcategory `QC(O) ⊆ D(O)` consists of the objects `K` for which every canonical
derived base-change map `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an isomorphism, while
`D_QCoh(O) ⊆ D(O)` consists of the objects all of whose cohomology sheaves are quasi-coherent.
When all restriction homomorphisms `O(V) → O(U)` of `O` are flat the two subcategories agree.

The reason is that for a flat restriction homomorphism derived base change is exact, so it
commutes with cohomology: the canonical map on `K` is an isomorphism exactly when the canonical
map `H^n(K)(V) ⊗_{O(V)} O(U) ⟶ H^n(K)(U)` of sections is an isomorphism for every `n`.  The
latter condition on a module is quasi-coherence on the chaotic site.

## Main definitions

* `Stacks.ModulesOnACategory.QuasiCoherentCohomology.hasQuasicoherentCohomology`: the object
  condition cutting out `D_QCoh(O)`, namely that every cohomology sheaf is quasi-coherent in the
  sense of `SheafOfModules.IsQuasicoherentOnSite`.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentCohomology.isQC_iff_hasQuasicoherentCohomology`: on a
  ringed site with the chaotic topology and flat restriction homomorphisms, `QC(O)` and
  `D_QCoh(O)` have the same objects.

## Implementation notes

The cohomology sheaves of an object of `D(O)` are produced as presheaves of modules, and the
sheaf condition is carried as an existential in `hasQuasicoherentCohomology`.  On the chaotic
site it is automatic, by `CategoryTheory.Presheaf.isSheaf_bot`, so the existential costs
nothing; keeping it rather than substituting that proof means the predicate is stated for an
arbitrary site and does not transport the cohomology presheaf along the hypothesis `J = ⊥`.

The derived base-change datum of `QuasiCoherentEquivalence.BaseChangeData` is a parameter, as
it is for `QuasiCoherentEquivalence.IsQC`; a left adjoint of derived restriction of scalars is
unique up to unique isomorphism, so the condition does not depend on the choice, and the proof
establishes that independence where it is needed.  Derived base change is compared with the
extension of scalars whose exactness flatness supplies, and the comparison criterion behind
the main result quantifies over an arbitrary exact left adjoint of restriction of scalars
rather than naming `ModuleCat.extendScalars`, so that commutativity of the section rings is
used only where the structure sheaf really is a sheaf of commutative rings.

Quasi-coherence of the cohomology sheaves is taken from
`Stacks.ModulesOnACategory.isQuasicoherentOnSite_iff_isUniversalArrow`, which states it as the
universal property of the restriction maps; `CategoryTheory.Functor.isUniversalArrow_iff_isIso`
turns that into invertibility of the base-change map of sections.

## References

* [Stacks Project, Tag 0GZR](https://stacks.math.columbia.edu/tag/0GZR)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

namespace Stacks.ModulesOnACategory.QuasiCoherentCohomology

universe w u v r

section Mate

variable {A B : Type*} [Category A] [Category B]

/-- Whether the adjoint transpose of a morphism `f : X ⟶ G.obj Y` is an isomorphism does not
depend on which left adjoint of `G` is used to form it: two left adjoints of `G` are canonically
isomorphic, and the two transposes differ by that isomorphism. -/
public lemma isIso_homEquiv_symm_iff {F F' : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) (adj' : F' ⊣ G)
    {X : A} {Y : B} (f : X ⟶ G.obj Y) :
    IsIso ((adj.homEquiv X Y).symm f) ↔ IsIso ((adj'.homEquiv X Y).symm f) := by
  have h : (adj.homEquiv X Y).symm f =
      (adj.leftAdjointUniq adj').hom.app X ≫ (adj'.homEquiv X Y).symm f := by
    simp only [Adjunction.homEquiv_counit]
    rw [← adj'.leftAdjointUniq_hom_app_counit adj Y]
    simp only [← Category.assoc]
    rw [← NatTrans.naturality]
    simp
  rw [h]
  exact isIso_comp_left_iff _ _

end Mate

section Derived

variable {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Category B] [Abelian B] [HasDerivedCategory B]

/-- A component of `derivedNatTrans _ _ α` is an isomorphism exactly when `α` is an isomorphism
on every cohomology object: the derived category detects isomorphisms through cohomology, and an
exact functor computes the cohomology of a complex objectwise. -/
private lemma isIso_mapDerivedNatTrans_iff {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (α : F ⟶ G) (K : DerivedCategory A) :
    IsIso ((derivedNatTrans _ _ α).app K) ↔
      ∀ n : ℤ, IsIso (α.app ((DerivedCategory.homologyFunctor A n).obj K)) := by
  have e : DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K) ≅ K :=
    DerivedCategory.Q.objObjPreimageIso K
  rw [← NatTrans.isIso_app_iff_of_iso (derivedNatTrans _ _ α) e]
  have he (n : ℤ) := NatTrans.isIso_app_iff_of_iso α
    ((DerivedCategory.homologyFunctor A n).mapIso e)
  simp only [← he]
  simp only [derivedNatTrans, Localization.liftNatTrans_app, whiskerRight_app,
    isIso_comp_left_iff, isIso_comp_right_iff, DerivedCategory.isIso_Q_map_iff_quasiIso,
    quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap]
  refine forall_congr' fun n ↦ ?_
  have hn := NatTrans.isIso_app_iff_of_iso α
    ((DerivedCategory.homologyFunctorFactors A n).app (DerivedCategory.Q.objPreimage K))
  dsimp only [Functor.comp_obj] at hn
  rw [hn]
  show IsIso (ShortComplex.homologyMap
    (((DerivedCategory.Q.objPreimage K).sc n).mapNatTrans α)) ↔ _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]
  rfl

/-- The adjoint transpose, for the derived form of an adjunction, of a morphism
`Q(f) ≫ G.mapDerivedCategoryFactors.inv` coming from a morphism `f` of complexes: it is the
image under `Q` of the adjoint transpose of `f`, up to the canonical factorization of the derived
functor of the left adjoint. -/
private lemma mapDerivedCategory_homEquiv_symm {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G)
    (P : CochainComplex A ℤ) (T : CochainComplex B ℤ)
    (f : P ⟶ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj T) :
    (((Adjunction.mapDerivedCategory adj).homEquiv
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T)).symm
        (DerivedCategory.Q.map f ≫ G.mapDerivedCategoryFactors.inv.app T)) =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv
          P T).symm f) := by
  simp only [Adjunction.homEquiv_counit]
  dsimp only [Adjunction.mapDerivedCategory]
  rw [Adjunction.localization_counit_app]
  dsimp only [CatCommSq.iso, Iso.symm_inv]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  exact F.mapDerivedCategoryFactors_hom_naturality_assoc f _

end Derived

section Comparison

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

attribute [local instance] HasDerivedCategory.standard

/-- The canonical base-change map on sections: for `a : V ⟶ U` in `Cᵒᵖ` and a left adjoint `E`
of restriction of scalars along `O(V) → O(U)`, the adjoint transpose of the restriction map
`M(V) ⟶ M(U)`, natural in the presheaf of modules `M`.  For `E` the extension of scalars this is
the map `M(V) ⊗_{O(V)} O(U) ⟶ M(U)`. -/
public def sectionsBaseChange {U V : Cᵒᵖ} (a : V ⟶ U)
    {E : ModuleCat.{max u v r w} (O.obj V) ⥤ ModuleCat.{max u v r w} (O.obj U)}
    (adj : E ⊣ ModuleCat.restrictScalars.{max u v r w} (O.map a).hom) :
    PresheafOfModules.evaluation.{max u v r w} O V ⋙ E ⟶
      PresheafOfModules.evaluation.{max u v r w} O U where
  app M := (adj.homEquiv _ _).symm (M.map a)
  naturality {M N} φ :=
    ((adj.homEquiv_naturality_left_symm
        ((PresheafOfModules.evaluation.{max u v r w} O V).map φ) (N.map a)).symm.trans
      ((congrArg (fun x ↦ (adj.homEquiv (M.obj V) (N.obj U)).symm x)
          ((PresheafOfModules.restriction O a).naturality φ)).trans
        (adj.homEquiv_naturality_right_symm (M.map a)
          ((PresheafOfModules.evaluation.{max u v r w} O U).map φ))))

/-- On a complex of `O`-modules, the adjoint transpose of the restriction map of complexes agrees
degreewise with the base-change map of sections, hence is that map applied degreewise. -/
private lemma homEquiv_symm_mapHomologicalComplex_restriction {U V : Cᵒᵖ} (a : V ⟶ U)
    {E : ModuleCat.{max u v r w} (O.obj V) ⥤ ModuleCat.{max u v r w} (O.obj U)}
    [E.Additive] (adj : E ⊣ ModuleCat.restrictScalars.{max u v r w} (O.map a).hom)
    (P : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv
          (((PresheafOfModules.evaluation.{max u v r w} O V).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((PresheafOfModules.evaluation.{max u v r w} O U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)).symm
        ((NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O a)
          (ComplexShape.up ℤ)).app P) =
      (NatTrans.mapHomologicalComplex (sectionsBaseChange.{w} O a adj)
        (ComplexShape.up ℤ)).app P :=
  rfl

/-- The derived comparison map at an object of the form `Q(P)` is an isomorphism exactly when the
derived base-change map of sections is, both being the image under `Q` of the same map of
complexes up to isomorphism. -/
private lemma isIso_comparison_Q_iff {U V : Cᵒᵖ} (a : V ⟶ U)
    {E : ModuleCat.{max u v r w} (O.obj V) ⥤ ModuleCat.{max u v r w} (O.obj U)}
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (adj : E ⊣ ModuleCat.restrictScalars.{max u v r w} (O.map a).hom)
    (bc : BaseChangeData.{w} O) (P : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    IsIso (comparison.{w} bc a (DerivedCategory.Q.obj P)) ↔
      IsIso ((derivedNatTrans _ _ (sectionsBaseChange.{w} O a adj)).app
        (DerivedCategory.Q.obj P)) := by
  unfold comparison
  rw [isIso_homEquiv_symm_iff (bc.baseChangeAdj a) (Adjunction.mapDerivedCategory adj),
    restrictionMap_Q]
  simp only [← Category.assoc, Adjunction.homEquiv_naturality_right_symm, isIso_comp_right_iff]
  rw [Category.assoc, Adjunction.homEquiv_naturality_left_symm, isIso_comp_left_iff]
  dsimp only [Functor.comp_obj]
  rw [mapDerivedCategory_homEquiv_symm, homEquiv_symm_mapHomologicalComplex_restriction]
  simp only [derivedNatTrans, Localization.liftNatTrans_app, whiskerRight_app,
    isIso_comp_left_iff, isIso_comp_right_iff]

/-- **The derived criterion.** Let `a : V ⟶ U` in `Cᵒᵖ`, let `E` be an exact left adjoint of
restriction of scalars along `O(V) → O(U)` — for a flat restriction homomorphism, extension of
scalars is one — and let `bc` be a derived base-change datum for `O`.  Then the canonical
comparison map `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an isomorphism exactly when the
base-change map of sections is an isomorphism on every cohomology sheaf of `K`. -/
public lemma isIso_comparison_iff {U V : Cᵒᵖ} (a : V ⟶ U)
    {E : ModuleCat.{max u v r w} (O.obj V) ⥤ ModuleCat.{max u v r w} (O.obj U)}
    [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (adj : E ⊣ ModuleCat.restrictScalars.{max u v r w} (O.map a).hom)
    (bc : BaseChangeData.{w} O) (K : DMod.{w} O) :
    IsIso (comparison.{w} bc a K) ↔
      ∀ n : ℤ, IsIso ((sectionsBaseChange.{w} O a adj).app
        ((DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} O) n).obj K)) := by
  refine Iff.trans ?_ (isIso_mapDerivedNatTrans_iff (sectionsBaseChange.{w} O a adj) K)
  rw [show comparison.{w} bc a K = (comparisonNatTrans.{w} bc a).app K from rfl,
    ← NatTrans.isIso_app_iff_of_iso (comparisonNatTrans.{w} bc a)
      (DerivedCategory.Q.objObjPreimageIso K),
    ← NatTrans.isIso_app_iff_of_iso (derivedNatTrans _ _ (sectionsBaseChange.{w} O a adj))
      (DerivedCategory.Q.objObjPreimageIso K)]
  exact isIso_comparison_Q_iff O a adj bc _

end Comparison

section RingedSite

open _root_.AlgebraicGeometry

/-- The sections of the sheaf of rings underlying the structure sheaf of a ringed site form a
commutative ring.  The underlying ring structure is the one that `RingCat` supplies, so that
this is compatible with the categories of modules over the section rings. -/
@[instance_reducible]
private instance sectionCommRing (X : RingedSite.{u, v, r}) (U : X.Cᵒᵖ) :
    CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) :=
  { (inferInstance : Ring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) with
    mul_comm := fun x y ↦
      mul_comm (show X.O.obj.obj U from x) (show X.O.obj.obj U from y) }

/-- Extension of scalars along the restriction homomorphism of `a : V ⟶ U` in `Cᵒᵖ`, as a left
adjoint of restriction of scalars. -/
private def extendScalarsAdj (X : RingedSite.{u, v, r}) {U V : X.Cᵒᵖ} (a : V ⟶ U) :
    ModuleCat.extendScalars.{r, r, max u v r w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map a).hom ⊣
      ModuleCat.restrictScalars.{max u v r w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map a).hom :=
  ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map a).hom

/-- Extension of scalars is additive, being a left adjoint between additive categories. -/
private instance extendScalarsAdditive (X : RingedSite.{u, v, r}) {U V : X.Cᵒᵖ} (a : V ⟶ U) :
    (ModuleCat.extendScalars.{r, r, max u v r w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map a).hom).Additive :=
  extendScalars_additive.{r, r, max u v r w} _

/-- Extension of scalars preserves finite colimits, being a left adjoint. -/
private instance extendScalarsPreservesFiniteColimits (X : RingedSite.{u, v, r})
    {U V : X.Cᵒᵖ} (a : V ⟶ U) :
    PreservesFiniteColimits
      (ModuleCat.extendScalars.{r, r, max u v r w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map a).hom) := by
  have : PreservesColimitsOfSize.{0, 0}
      (ModuleCat.extendScalars.{r, r, max u v r w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map a).hom) :=
    (extendScalarsAdj.{w} X a).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- An object of `D(O)` on a ringed site has quasi-coherent cohomology when every one of its
cohomology sheaves is quasi-coherent in the sense of `SheafOfModules.IsQuasicoherentOnSite`.
This is the object condition cutting out the subcategory `D_QCoh(O) ⊆ D(O)`. -/
def hasQuasicoherentCohomology (X : RingedSite.{u, v, r})
    (K : DMod.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) : Prop :=
  ∀ n : ℤ, ∃ hM : Presheaf.IsSheaf X.J ((DerivedCategory.homologyFunctor
      (PresheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) n).obj
        K).presheaf,
    (⟨_, hM⟩ : SheafOfModules.{max u v r w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).IsQuasicoherentOnSite

/-- **Quasi-coherent cohomology under flat restrictions.** Let `C` be a category viewed as a
site with the chaotic topology, let `O` be its sheaf of rings, and assume that for every
morphism `U → V` of `C` the restriction homomorphism `O(V) → O(U)` is flat.  Then an object of
`D(O)` lies in `QC(O)` exactly when all of its cohomology sheaves are quasi-coherent, that is,
`QC(O) = D_QCoh(O)`. -/
@[stacks 0GZR]
theorem isQC_iff_hasQuasicoherentCohomology (X : RingedSite.{u, v, r}) (hX : X.J = ⊥)
    (hflat : ∀ {U V : X.Cᵒᵖ} (a : V ⟶ U), RingHom.Flat (X.O.obj.map a).hom)
    (bc : BaseChangeData.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (K : DMod.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :
    IsQC.{w} bc K ↔ hasQuasicoherentCohomology.{w} X K := by
  have hpl : ∀ {U V : X.Cᵒᵖ} (a : V ⟶ U), PreservesFiniteLimits
      (ModuleCat.extendScalars.{r, r, max u v r w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map a).hom) :=
    fun a ↦ extendScalars_preservesFiniteLimits_of_flat'.{r, max u v w} _ (hflat a)
  constructor
  · intro h n
    -- `X.J` occurs in the type of `X.ringSheaf`, so the sheaf condition is transported along
    -- `hX` with an explicit motive rather than by rewriting.
    refine ⟨hX.symm.subst (motive := fun J ↦ Presheaf.IsSheaf J
      ((DerivedCategory.homologyFunctor
        (PresheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) n).obj
          K).presheaf)
      (Presheaf.isSheaf_bot _), ?_⟩
    rw [Stacks.ModulesOnACategory.isQuasicoherentOnSite_iff_isUniversalArrow.{u, v, r, w} hX]
    intro U V a
    exact (Functor.isUniversalArrow_iff_isIso (extendScalarsAdj.{w} X a) _).mpr
      ((isIso_comparison_iff _ a _ bc K).mp (h a) n)
  · intro h U V a
    refine (isIso_comparison_iff _ a (extendScalarsAdj.{w} X a) bc K).mpr fun n ↦ ?_
    obtain ⟨hM, hQC⟩ := h n
    rw [Stacks.ModulesOnACategory.isQuasicoherentOnSite_iff_isUniversalArrow.{u, v, r, w}
      hX] at hQC
    exact (Functor.isUniversalArrow_iff_isIso (extendScalarsAdj.{w} X a) _).mp (hQC a)

end RingedSite

end Stacks.ModulesOnACategory.QuasiCoherentCohomology

end
