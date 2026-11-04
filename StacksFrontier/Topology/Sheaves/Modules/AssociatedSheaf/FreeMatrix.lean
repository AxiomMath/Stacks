module

public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Free

/-!
# Matrices over the structure sheaf and associated sheaves

Let `(X, 𝒪_X)` be a ringed space and `α : R → Γ(X, 𝒪_X)` a ring homomorphism. A morphism of free
sheaves of `𝒪_X`-modules is construction (3) of Stacks 01BH applied to a morphism of free
`R`-modules as soon as the two agree, column by column, on the basis sections over the whole
space. When the columns of the morphism are finite combinations of the basis sections with
coefficients in `Γ(X, 𝒪_X)`, its cokernel is therefore the sheaf associated to a
`Γ(X, 𝒪_X)`-module.

## Main definitions

* `Stacks.AssociatedSheaf.unitTop`, `Stacks.AssociatedSheaf.freeUnitTop`: the unit section of the
  structure sheaf over the whole space, in the unit sheaf of modules and in the `i`-th summand of
  a free sheaf of modules.
* `Stacks.AssociatedSheaf.unitEntry`: the global section of the structure sheaf attached to an
  endomorphism of the unit sheaf of modules.
* `Stacks.AssociatedSheaf.smulTop`: scalar multiplication on the sections over the whole space.

## Main results

* `Stacks.AssociatedSheaf.unit_hom_ext_of_app_terminal`: a morphism out of the unit sheaf of
  modules is determined by the image of `1` over a terminal object of the site.
* `Stacks.AssociatedSheaf.freeIsoAssociatedSheaf_hom_comm`: the column-by-column criterion for a
  morphism of free sheaves of modules to come from a morphism of free modules.
* `Stacks.AssociatedSheaf.exists_associatedSheaf_iso_of_unit_matrix`: the cokernel of a morphism
  with finite columns is an associated sheaf.

## Implementation notes

`smulTop` and `unitEntry` exist to carry the identification of the sections of the structure sheaf
with the scalars in their own result types. Writing the scalar action inline instead asks the
elaborator to unify the ring of `Y.val.obj (op ⊤)` with `X.presheaf.obj (op ⊤)` across
`structureSheafRing`, which is semireducible, so the instance search fails on a
goal that displays correctly.

Construction (2) of Stacks 01BH is not used, and neither is its comparison with construction (3).
The identification of a free sheaf of modules with the associated sheaf of a free module
(`freeIsoAssociatedSheaf`) together with the fact that construction (3) is a left adjoint
(`associatedSheafAdjunction`, Stacks 01BH(4)) is all that is needed.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01BK](https://stacks.math.columbia.edu/tag/01BK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.AssociatedSheaf

universe w v₁ u₁ u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective
  isLeftAdjoint_associatedSheafFunctor

section Terminal
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {Rc : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A morphism out of the unit sheaf of modules is determined by the image of `1` over a terminal
object of the site. -/
lemma unit_hom_ext_of_app_terminal {M : SheafOfModules.{u} Rc} (T : C) (hT : IsTerminal T)
    {f g : SheafOfModules.unit Rc ⟶ M}
    (h : f.val.app (op T) (1 : Rc.obj.obj (op T)) =
      g.val.app (op T) (1 : Rc.obj.obj (op T))) : f = g := by
  refine (SheafOfModules.unitHomEquiv M).injective ?_
  ext W
  rw [← (M.unitHomEquiv f).property (hT.from W.unop).op,
    ← (M.unitHomEquiv g).property (hT.from W.unop).op]
  exact congrArg (M.val.map (hT.from W.unop).op) h

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Evaluating a finite sum of morphisms of sheaves of modules on a section. -/
lemma sum_val_app_apply {M N : SheafOfModules.{u} Rc} {ι : Type w} (t : Finset ι)
    (φ : ι → (M ⟶ N)) (W : Cᵒᵖ) (x : M.val.obj W) :
    (∑ i ∈ t, φ i).val.app W x = ∑ i ∈ t, (φ i).val.app W x := by
  classical
  induction t using Finset.induction with
  | empty => simp [show ((0 : M ⟶ N)).val = 0 from rfl]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl

end Terminal

variable (X : RingedSpace.{u, u})

/-- The unit section of the structure sheaf over the whole space, read in the unit sheaf of
modules. -/
abbrev unitTop : (SheafOfModules.unit (structureSheafRing X)).val.obj (op ⊤) :=
  (1 : (structureSheafRing X).obj.obj (op ⊤))

/-- The unit section of the structure sheaf in the `i`-th summand of the free sheaf of modules on
`I`, over the whole space. -/
abbrev freeUnitTop {I : Type u} (i : I) :
    (SheafOfModules.free (R := structureSheafRing X) I).val.obj (op ⊤) :=
  (SheafOfModules.ιFree (R := structureSheafRing X) i).val.app (op ⊤)
    (unitTop X)

/-- Scalar multiplication on the sections of `Y` over the whole space, at its module structure
over the sections of the structure sheaf. -/
abbrev smulTop (Y : SheafOfModules.{u} (structureSheafRing X))
    (ρ : (structureSheafRing X).obj.obj (op ⊤)) (y : Y.val.obj (op ⊤)) :
    Y.val.obj (op ⊤) := ρ • y

/-- The global section of the structure sheaf attached to an endomorphism of the unit sheaf of
modules. The endomorphism is recovered from it, since `⊤` is terminal. -/
abbrev unitEntry (b : SheafOfModules.unit (structureSheafRing X) ⟶
    SheafOfModules.unit (structureSheafRing X)) :
    (structureSheafRing X).obj.obj (op ⊤) :=
  b.val.app (op ⊤) (unitTop X)

/-- A global section of the structure sheaf acting on the unit section of the unit sheaf of
modules is that section itself. -/
lemma smulTop_unitTop (ρ : (structureSheafRing X).obj.obj (op ⊤)) :
    smulTop X (SheafOfModules.unit (structureSheafRing X)) ρ (unitTop X) = ρ :=
  mul_one ρ

variable {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- Scalar multiplication on global sections with scalars restricted along `α` is multiplication
by the image of the scalar. -/
lemma smul_globalSections (Y : SheafOfModules.{u} (structureSheafRing X))
    (r : R) (y : (globalSectionsFunctor.{u, u} X α).obj Y) :
    (r • y : (globalSectionsFunctor.{u, u} X α).obj Y) = smulTop X Y (α r) y :=
  congrArg (fun s : (structureSheafRing X).obj.obj (op ⊤) ↦ smulTop X Y s y)
    (globalSectionsMap_app_top_apply X α r)

/-- The comparison `freeIsoAssociatedSheaf` followed by construction (3) applied to a map of
modules carries the `i`-th basis section to the image of `Finsupp.single i 1`. -/
lemma map_freeIsoAssociatedSheaf_hom_app_top {I : Type u} {N : ModuleCat.{u} R}
    (g : (ModuleCat.free R).obj I ⟶ N) (i : I) :
    ((associatedSheafFunctor.{u, u} X α).map g).val.app (op ⊤)
        ((freeIsoAssociatedSheaf X α I).hom.val.app (op ⊤) (freeUnitTop X i)) =
      (associatedSheafAdjunction.{u, u} X α).unit.app N (g (Finsupp.single i 1)) := by
  rw [freeIsoAssociatedSheaf_hom_app_top]
  exact congrArg (fun (φ : (ModuleCat.free R).obj I ⟶ (globalSectionsFunctor.{u, u} X α).obj _) ↦
    φ (Finsupp.single i 1)) ((associatedSheafAdjunction.{u, u} X α).unit_naturality g)


/-- An endomorphism of the unit sheaf of modules followed by the `i`-th basis section of the
comparison with the associated sheaf of a free module: the endomorphism acts as its global
section. -/
lemma unitEntry_comp_freeIsoAssociatedSheaf_app_top {I : Type u}
    (b : SheafOfModules.unit (structureSheafRing X) ⟶
      SheafOfModules.unit (structureSheafRing X)) (i : I) :
    (b ≫ SheafOfModules.ιFree i ≫ (freeIsoAssociatedSheaf X α I).hom).val.app (op ⊤)
        (1 : (structureSheafRing X).obj.obj (op ⊤)) =
      smulTop X _ (unitEntry X b)
        ((associatedSheafAdjunction.{u, u} X α).unit.app ((ModuleCat.free R).obj I)
          (Finsupp.single i (1 : R))) := by
  rw [← freeIsoAssociatedSheaf_hom_app_top X α I i]
  show (SheafOfModules.ιFree i ≫ (freeIsoAssociatedSheaf X α I).hom).val.app (op ⊤)
      (unitEntry X b) = smulTop X _ (unitEntry X b)
      ((SheafOfModules.ιFree i ≫ (freeIsoAssociatedSheaf X α I).hom).val.app (op ⊤) (unitTop X))
  conv_lhs => rw [← smulTop_unitTop X (unitEntry X b)]
  exact ((SheafOfModules.ιFree i ≫
    (freeIsoAssociatedSheaf X α I).hom).val.app (op ⊤)).hom.map_smul _ _

/-- A morphism of free sheaves of `𝒪_X`-modules is construction (3) of a morphism of free
modules, read through `freeIsoAssociatedSheaf`, as soon as the two agree column by column on the
basis sections over the whole space. -/
lemma freeIsoAssociatedSheaf_hom_comm {I J : Type u}
    (f : SheafOfModules.free (R := structureSheafRing X) J ⟶
      SheafOfModules.free I)
    (g : (ModuleCat.free R).obj J ⟶ (ModuleCat.free R).obj I)
    (h : ∀ j : J, (SheafOfModules.ιFree j ≫ f ≫
        (freeIsoAssociatedSheaf X α I).hom).val.app (op ⊤) (unitTop X) =
      (associatedSheafAdjunction.{u, u} X α).unit.app ((ModuleCat.free R).obj I)
        (g (Finsupp.single j (1 : R)))) :
    f ≫ (freeIsoAssociatedSheaf X α I).hom =
      (freeIsoAssociatedSheaf X α J).hom ≫ (associatedSheafFunctor.{u, u} X α).map g := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan J) _ _ (fun j ↦ ?_)
  rw [SheafOfModules.freeCofan_inj]
  exact unit_hom_ext_of_app_terminal ⊤ isTerminalTop
    ((h j).trans (map_freeIsoAssociatedSheaf_hom_app_top X α g j).symm)

/-- **Stacks 01BK, the construction-(2) input.** A morphism of free sheaves of
`𝒪_X`-modules each of whose columns is a finite combination of the basis sections, with
coefficients global sections of the structure sheaf, has for cokernel the sheaf associated to a
module over the global sections: namely the cokernel of the matrix read in `ModuleCat`.

Construction (2) of Stacks 01BH is not needed for this, and neither is its comparison with
construction (3): the free sheaves are identified with associated sheaves of free modules by
`freeIsoAssociatedSheaf`, the matrix is lifted to a map of free modules through that
identification, and construction (3) preserves the cokernel because it is a left adjoint. -/
theorem exists_associatedSheaf_iso_of_unit_matrix {I J : Type u}
    (f : SheafOfModules.free (R := structureSheafRing X) J ⟶
      SheafOfModules.free I)
    (hf : ∀ j : J, ∃ (t : Finset I)
      (a : I → (SheafOfModules.unit (structureSheafRing X) ⟶
        SheafOfModules.unit (structureSheafRing X))),
      SheafOfModules.ιFree j ≫ f = ∑ i ∈ t, a i ≫ SheafOfModules.ιFree i) :
    ∃ M : ModuleCat.{u} (X.presheaf.obj (op ⊤)),
      Nonempty (cokernel f ≅
        associatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤))) M) := by
  classical
  choose T a ha using hf
  let c : J → I → (X.presheaf.obj (op ⊤) : Type u) := fun j i ↦ unitEntry X (a j i)
  let e : I → ((ModuleCat.free (X.presheaf.obj (op ⊤))).obj I : Type u) :=
    fun i ↦ ModuleCat.freeMk i
  let v : J → ((ModuleCat.free (X.presheaf.obj (op ⊤))).obj I : Type u) :=
    fun j ↦ ∑ i ∈ T j, c j i • e i
  let g : (ModuleCat.free (X.presheaf.obj (op ⊤))).obj J ⟶
      (ModuleCat.free (X.presheaf.obj (op ⊤))).obj I := ModuleCat.freeDesc (↾v)
  have hu : ∀ j : J, (associatedSheafAdjunction.{u, u} X
        (RingHom.id (X.presheaf.obj (op ⊤)))).unit.app
          ((ModuleCat.free (X.presheaf.obj (op ⊤))).obj I) (g (ModuleCat.freeMk j)) =
      ∑ i ∈ T j, smulTop X _ (c j i) ((associatedSheafAdjunction.{u, u} X
        (RingHom.id (X.presheaf.obj (op ⊤)))).unit.app
          ((ModuleCat.free (X.presheaf.obj (op ⊤))).obj I) (e i)) := by
    intro j
    rw [show g (ModuleCat.freeMk j) = ∑ i ∈ T j, c j i • e i from ModuleCat.freeDesc_apply _ j,
      map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_globalSections X (RingHom.id (X.presheaf.obj (op ⊤))) _ (c j i),
      RingHom.id_apply]
  have hL : ∀ j : J, SheafOfModules.ιFree j ≫ f ≫
      (freeIsoAssociatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤))) I).hom =
      ∑ i ∈ T j, a j i ≫ SheafOfModules.ιFree i ≫
        (freeIsoAssociatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤))) I).hom := by
    intro j
    rw [← Category.assoc, ha j, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun i _ ↦ Category.assoc _ _ _
  have hcomm := freeIsoAssociatedSheaf_hom_comm X (RingHom.id (X.presheaf.obj (op ⊤))) f g
    (fun j ↦ by
      refine Eq.trans ?_ (hu j).symm
      rw [hL j, sum_val_app_apply]
      exact Finset.sum_congr rfl fun i _ ↦
        unitEntry_comp_freeIsoAssociatedSheaf_app_top X
          (RingHom.id (X.presheaf.obj (op ⊤))) (a j i) i)
  exact ⟨cokernel g, ⟨cokernel.mapIso f _
      (freeIsoAssociatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤))) J)
      (freeIsoAssociatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤))) I) hcomm ≪≫
    (PreservesCokernel.iso
      (associatedSheafFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤)))) g).symm⟩⟩

end Stacks.AssociatedSheaf
