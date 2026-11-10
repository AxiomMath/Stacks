module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.AbelianSheafStalk
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Degree-zero étale cohomology over a field is the group of Galois invariants

Let `K` be a field, let `sbar` be a geometric point of `Spec K` and let `G` be the absolute
Galois group at `sbar`.  Tag 04JQ identifies abelian sheaves on the small étale site of
`Spec K` with discrete `G`-modules, by taking the stalk at `sbar`.  If the abelian sheaf `F`
corresponds in this way to the `G`-module `M`, then the degree-zero étale cohomology of
`Spec K` with coefficients in `F` is the group `M ^ G` of Galois invariants of `M`.

## Main definitions

* `AlgebraicGeometry.etaleGaloisModule` — the discrete Galois module of Tag 04JQ attached to an
  abelian sheaf on the small étale site of the spectrum of a field.
* `AlgebraicGeometry.etaleStalkGaloisInvariants` — the invariants `M ^ G`, as a subgroup of the
  underlying abelian group of that module.
* `AlgebraicGeometry.etaleGlobalSectionAbelianGerm` — the germ at the geometric point of a
  global section of the sheaf, as an additive map to the Galois module.

## Main results

* `AlgebraicGeometry.etaleH0AddEquivGaloisInvariants` — degree-zero étale cohomology of the
  spectrum of a field is the group of Galois invariants of the associated module, as an
  isomorphism of abelian groups.
* `AlgebraicGeometry.etaleH0AddEquivGaloisInvariants_coe` — that isomorphism carries a
  cohomology class to the germ at the geometric point of the corresponding global section.
* `AlgebraicGeometry.bijective_etaleGlobalSectionAbelianGerm` — the additive germ map is a
  bijection from the global sections onto the invariants.

## References

* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)
* [Stacks Project, Tag 04JM](https://stacks.math.columbia.edu/tag/04JM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory

/-- **The invariants of an action of a monoid on an abelian group**: the subgroup of elements
fixed by every element of the monoid. -/
def Action.addInvariants {G : Type*} [Monoid G] (M : Action AddCommGrpCat.{w} G) :
    AddSubgroup (M.V : Type w) where
  carrier := {x | ∀ σ : G, ConcreteCategory.hom (M.ρ σ).asHom x = x}
  zero_mem' := fun _ ↦ map_zero _
  add_mem' := fun ha hb σ ↦ by rw [map_add, ha σ, hb σ]
  neg_mem' := fun ha σ ↦ by rw [map_neg, ha σ]

/-- An element of an abelian group with a monoid action is invariant exactly when every element
of the monoid fixes it. -/
theorem Action.mem_addInvariants {G : Type*} [Monoid G] (M : Action AddCommGrpCat.{w} G)
    (x : (M.V : Type w)) :
    x ∈ M.addInvariants ↔ ∀ σ : G, ConcreteCategory.hom (M.ρ σ).asHom x = x :=
  Iff.rfl

end CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))
  (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})

/-- The sheaf of sets underlying an abelian sheaf on the small étale site of the spectrum of a
field. -/
abbrev abelianEtaleSheafOfSets : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK :=
  (sheafCompose (SmallEtale.topology B (Spec (.of K)) hK)
    (CategoryTheory.forget AddCommGrpCat.{max u v})).obj F

/-- **The discrete Galois module of an abelian étale sheaf**, that is, the module `M` attached
to the sheaf `F` by the stalk equivalence of Tag 04JQ. -/
abbrev etaleGaloisModule := (abelianEtaleStalkEquivalence.{u, v} B K hK sbar).functor.obj F

/-- The identification of the underlying abelian group of the Galois module of an abelian étale
sheaf with the abelian-group-valued stalk of that sheaf. -/
def etaleGaloisModuleAddEquivStalk :
    ((etaleGaloisModule.{u, v} B K hK sbar F).obj.obj.V : _) ≃+
      ((abelianEtaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F : _) :=
  Iso.addCommGroupIsoToAddEquiv ((abelianEtaleStalkEquivalenceIso.{u, v} B K hK sbar).app F)

/-- The identification of the Galois module with the abelian stalk carries the germ of a
section, taken in the underlying sheaf of sets, to its germ taken in abelian groups. -/
theorem etaleGaloisModuleAddEquivStalk_germ
    (U : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    etaleGaloisModuleAddEquivStalk.{u, v} B K hK sbar F
        (etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
          (abelianEtaleSheafOfSets.{u, v} B K hK F) U t) =
      abelianEtaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F U t :=
  abelianEtaleStalkForgetIso_germ.{u, v} B (Spec (.of K)) hK sbar F U t

/-- The inverse of the identification with the abelian stalk sends an abelian germ to the germ of
the underlying sheaf of sets. -/
private theorem etaleGaloisModuleAddEquivStalk_symm_abelianEtaleStalkGerm
    (U : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    (etaleGaloisModuleAddEquivStalk.{u, v} B K hK sbar F).symm
        (abelianEtaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F U t) =
      etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
        (abelianEtaleSheafOfSets.{u, v} B K hK F) U t :=
  (etaleGaloisModuleAddEquivStalk.{u, v} B K hK sbar F).symm_apply_eq.mpr
    (etaleGaloisModuleAddEquivStalk_germ.{u, v} B K hK sbar F U t).symm

/-- The Galois action on the module of Tag 04JQ is the Galois action on the stalk of the
underlying sheaf of sets. -/
theorem etaleGaloisModule_rho_apply (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (x : ((etaleGaloisModule.{u, v} B K hK sbar F).obj.obj.V : _)) :
    ConcreteCategory.hom ((etaleGaloisModule.{u, v} B K hK sbar F).obj.obj.ρ σ).asHom x =
      ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar
        (abelianEtaleSheafOfSets.{u, v} B K hK F) σ) x :=
  rfl

/-- **The Galois action of Tag 04JQ, read on the abelian stalk, moves germs to germs at the
translated lift.**  Transporting the action on the module of Tag 04JQ along the identification
`AlgebraicGeometry.etaleGaloisModuleAddEquivStalk` of its carrier with the abelian-group-valued
stalk, the germ at the geometric point of a section over a pointed étale neighbourhood goes to
the germ of the same section at the Galois translate of the lift. -/
theorem etaleGaloisModuleAddEquivStalk_rho_abelianEtaleStalkGerm
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (U : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    etaleGaloisModuleAddEquivStalk.{u, v} B K hK sbar F
        (ConcreteCategory.hom ((etaleGaloisModule.{u, v} B K hK sbar F).obj.obj.ρ σ).asHom
          ((etaleGaloisModuleAddEquivStalk.{u, v} B K hK sbar F).symm
            (abelianEtaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F U t))) =
      abelianEtaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F
        (Functor.elementsMk _ U.1 (galoisFiberAction B K hK sbar σ U.2)) t := by
  rw [etaleGaloisModuleAddEquivStalk_symm_abelianEtaleStalkGerm]
  exact (congrArg (etaleGaloisModuleAddEquivStalk.{u, v} B K hK sbar F)
      ((etaleGaloisModule_rho_apply.{u, v} B K hK sbar F σ _).trans
        (etaleStalkSmul_germ.{u, v} B K hK sbar
          (abelianEtaleSheafOfSets.{u, v} B K hK F) σ U t))).trans
    (etaleGaloisModuleAddEquivStalk_germ.{u, v} B K hK sbar F
      (Functor.elementsMk _ U.1 (galoisFiberAction B K hK sbar σ U.2)) t)

/-- **The Galois invariants `M ^ G` of the module attached to an abelian étale sheaf over a
field**: the elements of the module on which every element of the absolute Galois group acts as
the identity, as a subgroup. -/
def etaleStalkGaloisInvariants :
    AddSubgroup ((etaleGaloisModule.{u, v} B K hK sbar F).obj.obj.V : _) :=
  (etaleGaloisModule.{u, v} B K hK sbar F).obj.obj.addInvariants

/-- An element of the Galois module is invariant exactly when it is fixed by every element of
the absolute Galois group. -/
theorem mem_etaleStalkGaloisInvariants
    (x : ((etaleGaloisModule.{u, v} B K hK sbar F).obj.obj.V : _)) :
    x ∈ etaleStalkGaloisInvariants.{u, v} B K hK sbar F ↔
      ∀ σ : GeometricPoint.absoluteGaloisGroup sbar,
        ConcreteCategory.hom ((etaleGaloisModule.{u, v} B K hK sbar F).obj.obj.ρ σ).asHom x = x :=
  Action.mem_addInvariants _ x

/-- **The germ at the geometric point of a global section of an abelian étale sheaf over a
field**, as an additive map to the Galois module of Tag 04JQ.  It is the inclusion of the
sections over the final étale object into the stalk, a colimit inclusion in abelian groups,
read through the identification of the Galois module with the abelian stalk. -/
def etaleGlobalSectionAbelianGerm :
    ((F.obj.obj (op (SmallEtale.final B (Spec (.of K)) hK))) : _) →+
      ((etaleGaloisModule.{u, v} B K hK sbar F).obj.obj.V : _) :=
  (etaleGaloisModuleAddEquivStalk.{u, v} B K hK sbar F).symm.toAddMonoidHom.comp
    (ConcreteCategory.hom (colimit.ι
      ((Functor.Elements.π (geometricPointFiber B (Spec (.of K)) hK sbar)).op ⋙
        (sheafToPresheaf _ _).obj F) (op (finalPointedNeighborhood B K hK sbar))))

/-- The additive germ map is the germ map of the underlying sheaf of sets. -/
theorem etaleGlobalSectionAbelianGerm_apply
    (t : ((F.obj.obj (op (SmallEtale.final B (Spec (.of K)) hK))) : _)) :
    etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F t =
      etaleGlobalSectionGerm.{u, v} B K hK sbar
        (abelianEtaleSheafOfSets.{u, v} B K hK F) t := by
  exact etaleGaloisModuleAddEquivStalk_symm_abelianEtaleStalkGerm.{u, v} B K hK sbar F
    (finalPointedNeighborhood B K hK sbar) t

/-- The germ of a global section is a Galois invariant. -/
theorem etaleGlobalSectionAbelianGerm_mem
    (t : ((F.obj.obj (op (SmallEtale.final B (Spec (.of K)) hK))) : _)) :
    etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F t ∈
      etaleStalkGaloisInvariants.{u, v} B K hK sbar F := by
  refine (mem_etaleStalkGaloisInvariants.{u, v} B K hK sbar F _).mpr (fun σ ↦ ?_)
  rw [etaleGaloisModule_rho_apply, etaleGlobalSectionAbelianGerm_apply]
  exact etaleStalkSmul_etaleGlobalSectionGerm.{u, v} B K hK sbar
    (abelianEtaleSheafOfSets.{u, v} B K hK F) σ t

/-- **Taking germs at the geometric point is a bijection from the global sections of an abelian
étale sheaf over a field onto the Galois invariants of its module.** -/
theorem bijective_etaleGlobalSectionAbelianGerm :
    Function.Bijective
      (fun t : ((F.obj.obj (op (SmallEtale.final B (Spec (.of K)) hK))) : _) ↦
        (⟨etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F t,
            etaleGlobalSectionAbelianGerm_mem.{u, v} B K hK sbar F t⟩ :
          ↥(etaleStalkGaloisInvariants.{u, v} B K hK sbar F))) := by
  have h := bijective_etaleGlobalSectionGerm.{u, v} B K hK sbar
    (abelianEtaleSheafOfSets.{u, v} B K hK F)
  refine ⟨fun t t' htt' ↦ h.1 (Subtype.ext ?_), fun y ↦ ?_⟩
  · exact ((etaleGlobalSectionAbelianGerm_apply.{u, v} B K hK sbar F t).symm.trans
      (congrArg Subtype.val htt')).trans
        (etaleGlobalSectionAbelianGerm_apply.{u, v} B K hK sbar F t')
  · obtain ⟨t, ht⟩ := h.2 ⟨y.1, fun σ ↦
      (mem_etaleStalkGaloisInvariants.{u, v} B K hK sbar F y.1).mp y.2 σ⟩
    exact ⟨t, Subtype.ext ((etaleGlobalSectionAbelianGerm_apply.{u, v} B K hK sbar F t).trans
      (congrArg Subtype.val ht))⟩

/-- The global sections of an abelian étale sheaf over a field are the Galois invariants of its
module, as an isomorphism of abelian groups. -/
def etaleGlobalSectionsAddEquivGaloisInvariants :
    ((F.obj.obj (op (SmallEtale.final B (Spec (.of K)) hK))) : _) ≃+
      ↥(etaleStalkGaloisInvariants.{u, v} B K hK sbar F) :=
  AddEquiv.ofBijective
    ((etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F).codRestrict
      (etaleStalkGaloisInvariants.{u, v} B K hK sbar F)
      (etaleGlobalSectionAbelianGerm_mem.{u, v} B K hK sbar F))
    (bijective_etaleGlobalSectionAbelianGerm.{u, v} B K hK sbar F)

/-- Let `K` be a field, let `sbar` be a geometric point of `Spec K` with absolute Galois group
`G`, and let `F` be an abelian sheaf on the small étale site of `Spec K` corresponding to the
`G`-module `M`.  Then the degree-zero étale cohomology of `Spec K` with coefficients in `F` is
the group `M ^ G` of Galois invariants. -/
@[stacks 03QU "part (2)"]
def etaleH0AddEquivGaloisInvariants
    [HasSheafify (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})] :
    Sheaf.H.{w, max u v} F 0 ≃+ ↥(etaleStalkGaloisInvariants.{u, v} B K hK sbar F) :=
  (Sheaf.H.equiv₀ F (SmallEtale.finalIsTerminal B (Spec (.of K)) hK)).trans
    (etaleGlobalSectionsAddEquivGaloisInvariants.{u, v} B K hK sbar F)

/-- The identification of degree-zero étale cohomology with the Galois invariants is taking
germs at the geometric point: a cohomology class is sent to the germ of the global section which
represents it. -/
@[stacks 03QU "part (2), the comparison is taking germs at the geometric point"]
theorem etaleH0AddEquivGaloisInvariants_coe
    [HasSheafify (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})]
    (x : Sheaf.H.{w, max u v} F 0) :
    (etaleH0AddEquivGaloisInvariants B K hK sbar F x).1 =
      etaleGlobalSectionGerm.{u, v} B K hK sbar (abelianEtaleSheafOfSets.{u, v} B K hK F)
        (Sheaf.H.equiv₀ F (SmallEtale.finalIsTerminal B (Spec (.of K)) hK) x) :=
  etaleGlobalSectionAbelianGerm_apply.{u, v} B K hK sbar F _

/-- Read in the abelian-group-valued stalk, the identification of degree-zero étale cohomology
with the Galois invariants sends a cohomology class to the germ, at the final pointed étale
neighbourhood, of the global section which represents it. -/
@[stacks 03QU "part (2), the comparison in the abelian stalk"]
theorem etaleH0AddEquivGaloisInvariants_abelianEtaleStalkGerm
    [HasSheafify (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max u v})]
    (x : Sheaf.H.{w, max u v} F 0) :
    etaleGaloisModuleAddEquivStalk.{u, v} B K hK sbar F
        (etaleH0AddEquivGaloisInvariants B K hK sbar F x).1 =
      abelianEtaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F
        (finalPointedNeighborhood B K hK sbar)
        (Sheaf.H.equiv₀ F (SmallEtale.finalIsTerminal B (Spec (.of K)) hK) x) := by
  rw [etaleH0AddEquivGaloisInvariants_coe]
  exact etaleGaloisModuleAddEquivStalk_germ.{u, v} B K hK sbar F
    (finalPointedNeighborhood B K hK sbar) _

end AlgebraicGeometry

end
