module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DegreeZero.GaloisInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.AddCommGrpModuleBridge
import StacksCore.Tactic.StacksAttribute

/-!
# Global sections of an abelian étale sheaf over a field are the invariants of its Galois module

Let `K` be a field, let `sbar` be a geometric point of `Spec K` and let `G` be the absolute
Galois group at `sbar`.  Tag 04JQ identifies abelian sheaves on the small étale site of
`Spec K` with discrete `G`-modules by taking the stalk at `sbar`.  This file states that
identification in the category `ContinuousGModule G` in which this library's continuous group
cohomology (Tag 04JR, `continuousGroupCohomology`) takes its coefficients, and upgrades the
degree-zero comparison of Tag 03QU part (2) from a bijection at each sheaf to an isomorphism of
two functors `Sheaf(Spec(K)ₑₜ) ⥤ Ab`: global sections, and the `G`-invariants of the associated
module.

## Main definitions

* `CategoryTheory.addInvariantsFunctor` — the invariants of an action of a monoid on an abelian
  group, as a functor, with `CategoryTheory.continuousGAddCommGrpInvariants` its restriction to
  discrete continuous modules in the abelian-group encoding.
* `AlgebraicGeometry.etaleContinuousGModuleEquivalence` — the stalk equivalence of Tag 04JQ, with
  values in the coefficient category of continuous group cohomology.
* `AlgebraicGeometry.etaleGlobalSectionsNatTrans` — taking germs at the geometric point, as a
  natural transformation from global sections to the invariants of the Galois module.

## Main results

* `AlgebraicGeometry.etaleGlobalSectionsIsoInvariants` and
  `AlgebraicGeometry.etaleGlobalSectionsIsoContinuousGModuleInvariants` — **Tag 03QU part (2) as
  an isomorphism of functors**, in the two encodings of discrete `G`-modules.
* `AlgebraicGeometry.etaleGammaIsoGaloisInvariants` and
  `AlgebraicGeometry.etaleGammaIsoContinuousGModuleInvariants` — the same with the global
  sections functor `CategoryTheory.Sheaf.Γ` of the site in place of sections over the final
  object, which is the functor the right derived functors of parts (1) and (3) are taken of.
* `AlgebraicGeometry.abelianEtaleStalkFunctor_map_germ` — a morphism of abelian sheaves carries a
  germ to a germ, which is what makes the comparison natural.
* `CategoryTheory.continuousGModuleEquivContinuousGAddCommGrp_comp_invariants` — the two encodings
  compute the same invariants, on the nose.

## Implementation notes

The functorial form is what the positive-degree statements of Tag 03QU need and what the
objectwise bijection `AlgebraicGeometry.bijective_etaleGlobalSectionAbelianGerm` does not
provide: parts (1) and (3) compare the right derived functors of global sections and of
invariants, and a derived functor sees only the functor. Naturality of the germ map is naturality
of a colimit inclusion in the diagram (`CategoryTheory.Limits.ι_colimMap`), composed with
naturality of the stalk comparison `abelianEtaleStalkEquivalenceIso`.

Invariants are taken by `CategoryTheory.addInvariantsFunctor`, built from the `AddSubgroup`
`CategoryTheory.Action.addInvariants` that the degree-zero comparison already uses. Through the
equivalence of the two encodings of discrete `G`-modules
(`CategoryTheory.continuousGModuleEquivContinuousGAddCommGrp`) it is `continuousGModuleInvariants`
definitionally, so no comparison of the two notions of invariants is needed.

Parts (1) and (3) of Tag 03QU are the functorial comparison here right derived, and they are
proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.EtaleGaloisCohomologyComparison`
as `AlgebraicGeometry.etaleDerivedGlobalSectionsIsoDerivedGaloisInvariants` and
`AlgebraicGeometry.etaleSheafCohomologyIsoContinuousGroupCohomologyFunctor`, at the
coefficient universe `AddCommGrpCat.{u + 1}` that the identification of sheaf cohomology with
derived global sections needs. Two inputs it takes are general and were available all along:
abelian sheaves on `SmallEtale B S hS` are a Grothendieck abelian category at that coefficient
universe, hence have enough injectives there, and
`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH` identifies Mathlib's
`CategoryTheory.Sheaf.H` — which is `Ext` out of the constant abelian sheaf — with the right
derived functors of global sections on a site whose objects live above its morphisms. That
module also carries the comparison over to Mathlib's small étale site, the two sites having the
same sheaves, as
`AlgebraicGeometry.smallEtaleSheafCohomologyIsoContinuousGroupCohomologyFunctor`.

The further input the vanishing theorems above the tag need is only partly available:
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupStalk`
identifies the stalk of `Stacks.Kummer.multiplicativeSheaf` with the units of the separable
closure as an isomorphism of abelian groups
(`AlgebraicGeometry.multiplicativeStalkIsoUnits`) and proves germ evaluation Galois equivariant
(`AlgebraicGeometry.multiplicativeSectionEval_galoisFiberAction`), but does not package those
into an isomorphism of discrete Galois modules, and
`Stacks.GaloisCohomology.unitsContinuousGModule` lives one coefficient universe below the one
this comparison consumes; see that module's documentation for both gaps.

## References

* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory

/-- **The invariants of an action of a monoid on an abelian group, as a functor.**  An
equivariant map carries an invariant element to an invariant element. -/
def addInvariantsFunctor (G : Type*) [Monoid G] :
    Action AddCommGrpCat.{w} G ⥤ AddCommGrpCat.{w} where
  obj M := AddCommGrpCat.of M.addInvariants
  map {M N} f := AddCommGrpCat.ofHom
    { toFun := fun x => ⟨ConcreteCategory.hom f.hom x.1, fun σ => by
        have h := ConcreteCategory.congr_hom (f.comm σ) x.1
        simp only [ConcreteCategory.comp_apply] at h
        rw [← h, (M.mem_addInvariants x.1).1 x.2 σ]⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The invariants functor acts on an invariant element by the underlying equivariant map. -/
theorem addInvariantsFunctor_map_coe {G : Type*} [Monoid G]
    {M N : Action AddCommGrpCat.{w} G} (f : M ⟶ N) (x : ↥M.addInvariants) :
    (ConcreteCategory.hom ((addInvariantsFunctor.{w} G).map f) x).1 =
      ConcreteCategory.hom f.hom x.1 := rfl

/-- **The invariants of a discrete continuous `G`-module in the abelian-group encoding**, as a
functor to abelian groups. -/
def continuousGAddCommGrpInvariants (G : Type u) [Group G] [TopologicalSpace G] :
    ContinuousGAddCommGrp.{u, w} G ⥤ AddCommGrpCat.{w} :=
  ContinuousGAddCommGrp.toAction G ⋙ addInvariantsFunctor.{w} G

/-- **The two encodings of discrete `G`-modules compute the same invariants.**  Forgetting the
`ℤ`-module structure and taking invariant elements is `continuousGModuleInvariants`. -/
theorem continuousGModuleEquivContinuousGAddCommGrp_comp_invariants
    (G : Type u) [Group G] [TopologicalSpace G] :
    (continuousGModuleEquivContinuousGAddCommGrp.{u, w} G).functor ⋙
        continuousGAddCommGrpInvariants.{u, w} G =
      continuousGModuleInvariants.{u, w} G := rfl

end CategoryTheory

namespace AlgebraicGeometry

section Germ

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **A morphism of abelian étale sheaves carries the germ of a section to the germ of its
image.**  The stalk is a colimit over the pointed étale neighbourhoods and the germ is a colimit
inclusion, which is natural in the diagram. -/
theorem abelianEtaleStalkFunctor_map_germ
    {F F' : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max u v}} (φ : F ⟶ F')
    (U : (geometricPointFiber B S hS s).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    ConcreteCategory.hom ((abelianEtaleStalkFunctor.{u, v} B S hS s).map φ)
        (abelianEtaleStalkGerm.{u, v} B S hS s F U t) =
      abelianEtaleStalkGerm.{u, v} B S hS s F' U
        (ConcreteCategory.hom (((sheafToPresheaf _ _).map φ).app (op U.1)) t) :=
  ConcreteCategory.congr_hom
    (Limits.ι_colimMap (Functor.whiskerLeft
      (Functor.Elements.π (geometricPointFiber B S hS s)).op
      ((sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max u v}).map φ)) (op U)) t

end Germ

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- Read in the abelian stalk, the additive germ of a global section is its germ at the final
pointed étale neighbourhood. -/
theorem etaleGaloisModuleAddEquivStalk_globalSectionAbelianGerm
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})
    (t : (F.obj.obj (op (SmallEtale.final B (Spec (.of K)) hK)) : _)) :
    etaleGaloisModuleAddEquivStalk.{u, v} B K hK sbar F
        (etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F t) =
      abelianEtaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F
        (finalPointedNeighborhood B K hK sbar) t := by
  rw [etaleGlobalSectionAbelianGerm_apply.{u, v} B K hK sbar F t]
  exact etaleGaloisModuleAddEquivStalk_germ.{u, v} B K hK sbar F
    (finalPointedNeighborhood B K hK sbar) t

/-- **Taking germs at the geometric point, as a natural transformation** from the global sections
of an abelian étale sheaf over a field to the Galois invariants of its module of Tag 04JQ. -/
def etaleGlobalSectionsNatTrans :
    (sheafSections (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v}).obj
        (op (SmallEtale.final B (Spec (.of K)) hK)) ⟶
      (abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor ⋙
        continuousGAddCommGrpInvariants.{u, max u v}
          (GeometricPoint.absoluteGaloisGroup sbar) where
  app F := AddCommGrpCat.ofHom
    ((etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F).codRestrict
      (etaleStalkGaloisInvariants.{u, v} B K hK sbar F)
      (etaleGlobalSectionAbelianGerm_mem.{u, v} B K hK sbar F))
  naturality {F F'} φ := by
    ext t
    apply Subtype.ext
    change etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F'
        (ConcreteCategory.hom
          (((sheafToPresheaf _ _).map φ).app (op (SmallEtale.final B (Spec (.of K)) hK))) t) =
      ConcreteCategory.hom
        ((ContinuousGAddCommGrp.forget (GeometricPoint.absoluteGaloisGroup sbar)).map
          ((abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor.map φ))
        (etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F t)
    have hnat := NatTrans.naturality_apply
      (abelianEtaleStalkEquivalenceIso.{u, v} B K hK sbar).hom φ
      (etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F t)
    refine (etaleGaloisModuleAddEquivStalk.{u, v} B K hK sbar F').injective ?_
    exact (etaleGaloisModuleAddEquivStalk_globalSectionAbelianGerm.{u, v} B K hK sbar F' _).trans
      (((abelianEtaleStalkFunctor_map_germ.{u, v} B (Spec (.of K)) hK sbar φ
            (finalPointedNeighborhood B K hK sbar) t).symm.trans
          (congrArg (ConcreteCategory.hom
              ((abelianEtaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ))
            (etaleGaloisModuleAddEquivStalk_globalSectionAbelianGerm.{u, v}
              B K hK sbar F t).symm)).trans hnat.symm)

/-- The germ comparison is an isomorphism at each abelian sheaf: this is Tag 04JM for the
underlying sheaf of sets. -/
instance isIso_etaleGlobalSectionsNatTrans_app
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v}) :
    IsIso ((etaleGlobalSectionsNatTrans.{u, v} B K hK sbar).app F) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F

/-- **Stacks Project, Tag 03QU, part (2), as an isomorphism of functors.**  Over a field, global
sections of an abelian étale sheaf and the Galois invariants of its module of Tag 04JQ are
isomorphic functors to abelian groups, by taking germs at the geometric point. -/
@[stacks 03QU "part (2), as a natural isomorphism of functors, in the abelian-group encoding of \
discrete Galois modules"]
def etaleGlobalSectionsIsoInvariants :
    (sheafSections (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v}).obj
        (op (SmallEtale.final B (Spec (.of K)) hK)) ≅
      (abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor ⋙
        continuousGAddCommGrpInvariants.{u, max u v}
          (GeometricPoint.absoluteGaloisGroup sbar) :=
  haveI := NatIso.isIso_of_isIso_app (etaleGlobalSectionsNatTrans.{u, v} B K hK sbar)
  asIso (etaleGlobalSectionsNatTrans.{u, v} B K hK sbar)

/-- The functorial comparison of Tag 03QU part (2) is taking germs at the geometric point. -/
theorem etaleGlobalSectionsIsoInvariants_hom_app_coe
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})
    (t : (F.obj.obj (op (SmallEtale.final B (Spec (.of K)) hK)) : _)) :
    (ConcreteCategory.hom ((etaleGlobalSectionsIsoInvariants.{u, v} B K hK sbar).hom.app F)
        t).1 = etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F t := rfl

/-- **The stalk equivalence of Tag 04JQ, in the coefficient category of continuous group
cohomology.**  Abelian sheaves on the small étale site of the spectrum of a field are the
discrete modules over the absolute Galois group in which Tag 04JR takes its coefficients. -/
@[sga "4 VIII 2.2" "partial"]
def etaleContinuousGModuleEquivalence :
    Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v} ≌
      ContinuousGModule.{u, max u v} (GeometricPoint.absoluteGaloisGroup sbar) :=
  (abelianEtaleStalkEquivalence.{u, v} B K hK sbar).trans
    (continuousGModuleEquivContinuousGAddCommGrp.{u, max u v}
      (GeometricPoint.absoluteGaloisGroup sbar)).symm

/-- **Stacks Project, Tag 03QU, part (2), as an isomorphism of functors, in the vocabulary of
continuous group cohomology.**  Global sections of an abelian étale sheaf over a field are the
`continuousGModuleInvariants` of the discrete Galois module of Tag 04JQ. -/
@[stacks 03QU "part (2), as a natural isomorphism of functors, in the coefficient category of \
continuousGroupCohomology"]
def etaleGlobalSectionsIsoContinuousGModuleInvariants :
    (sheafSections (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v}).obj
        (op (SmallEtale.final B (Spec (.of K)) hK)) ≅
      (etaleContinuousGModuleEquivalence.{u, v} B K hK sbar).functor ⋙
        continuousGModuleInvariants.{u, max u v}
          (GeometricPoint.absoluteGaloisGroup sbar) :=
  etaleGlobalSectionsIsoInvariants.{u, v} B K hK sbar ≪≫
    Functor.isoWhiskerLeft (abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor
        ((Functor.leftUnitor _).symm ≪≫
          Functor.isoWhiskerRight
            (continuousGModuleEquivContinuousGAddCommGrp.{u, max u v}
              (GeometricPoint.absoluteGaloisGroup sbar)).counitIso.symm
            (continuousGAddCommGrpInvariants.{u, max u v}
              (GeometricPoint.absoluteGaloisGroup sbar)) ≪≫
          Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm

/-- **Stacks Project, Tag 03QU, part (2), functorially, for the global sections functor of the
site.**  The global sections functor `CategoryTheory.Sheaf.Γ` of the small étale site of the
spectrum of a field is the functor of Galois invariants of the module of Tag 04JQ, in the
abelian-group encoding of discrete Galois modules.  This is
`AlgebraicGeometry.etaleGlobalSectionsIsoInvariants` with sections over the final object
rewritten as global sections. -/
@[stacks 03QU "part (2), as an isomorphism of functors on the global sections functor"]
def etaleGammaIsoGaloisInvariants
    [HasSheafify (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v}] :
    Sheaf.Γ (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v} ≅
      (abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor ⋙
        continuousGAddCommGrpInvariants.{u, max u v}
          (GeometricPoint.absoluteGaloisGroup sbar) :=
  Sheaf.ΓNatIsoSheafSections _ _ (SmallEtale.finalIsTerminal B (Spec (.of K)) hK) ≪≫
    etaleGlobalSectionsIsoInvariants.{u, v} B K hK sbar

/-- **Stacks Project, Tag 03QU, part (2), functorially and in the module encoding, for the global
sections functor of the site.**  The global sections functor `CategoryTheory.Sheaf.Γ` of the
small étale site of the spectrum of a field is the stalk equivalence of Tag 04JQ followed by the
functor of `G`-invariants of discrete modules over the absolute Galois group. -/
@[stacks 03QU "part (2), as an isomorphism of functors with the module invariants"]
def etaleGammaIsoContinuousGModuleInvariants
    [HasSheafify (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v}] :
    Sheaf.Γ (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v} ≅
      (etaleContinuousGModuleEquivalence.{u, v} B K hK sbar).functor ⋙
        continuousGModuleInvariants.{u, max u v}
          (GeometricPoint.absoluteGaloisGroup sbar) :=
  Sheaf.ΓNatIsoSheafSections _ _ (SmallEtale.finalIsTerminal B (Spec (.of K)) hK) ≪≫
    etaleGlobalSectionsIsoContinuousGModuleInvariants.{u, v} B K hK sbar

add_to_stacks 04JQ "the stalk equivalence in the coefficient category of continuous group \
cohomology" AlgebraicGeometry.etaleContinuousGModuleEquivalence

end AlgebraicGeometry

end
