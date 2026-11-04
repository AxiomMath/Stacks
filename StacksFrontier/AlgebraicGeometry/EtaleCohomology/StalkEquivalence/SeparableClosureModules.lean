module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DegreeZero.GaloisInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.UnibranchContinuousModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.AddCommGrpModuleBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Shapiro
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.FieldTheory.Galois.SeparableClosureGaloisGroup
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.PrimePowerTorsionMultiplication
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian étale sheaves on the spectrum of a field as discrete Galois modules

Let `F` be a field and `E` a separable closure of `F`. Abelian sheaves on the small étale site of
`Spec F` are equivalent to discrete `Gal(E/F)`-modules. Under this equivalence

* global sections are Galois invariants,
* the constant sheaf on an abelian group `A` is the module `A` with the trivial action,
* étale cohomology `Hⁿ(Spec F, 𝓕)`, that is `Extⁿ` out of the constant sheaf `ℤ`, is
  `Extⁿ` out of the trivial module `ℤ` in discrete modules, which is Galois cohomology,
* `ℓ`-power torsion sheaves correspond to `ℓ`-power torsion modules.

This is [Stacks, Tag 03QU] for Mathlib's small étale site and an arbitrary separable closure.

## Main definitions

* `AlgebraicGeometry.fieldGaloisContinuousMulEquiv`: the absolute Galois group at the geometric
  point of `Spec F` given by an algebraic closure is `Gal(E/F)`.
* `AlgebraicGeometry.fieldEtaleSheafEquiv`: the equivalence of abelian sheaves on the small
  étale site of `Spec F` with discrete `Gal(E/F)`-modules.
* `AlgebraicGeometry.fieldEtaleSheafEquivΓIso`: global sections are invariants.
* `AlgebraicGeometry.fieldEtaleSheafEquivConstantIso`: constant sheaves are trivial modules.
* `AlgebraicGeometry.fieldEtaleExtIso`: `Ext` out of `ℤ` on both sides agree.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_iff`: vanishing of étale cohomology is vanishing of
  Galois cohomology.
* `AlgebraicGeometry.exists_pow_smul_fieldEtaleSheafEquiv_eq_zero` and
  `AlgebraicGeometry.isPrimePowerTorsion_fieldEtaleSheafEquiv_inverse`: torsion is preserved.
* `AlgebraicGeometry.subsingleton_ext_trivialGModule_iff`: cohomology with trivial coefficients
  is invariant under isomorphisms of topological groups.

## Implementation notes

The equivalence is the composite of the identification of Mathlib's small étale site with the
small étale site of Stacks 021B (`AlgebraicGeometry.Scheme.smallEtaleSheafEquiv`), the stalk
equivalence at the geometric point given by an algebraic closure
(`AlgebraicGeometry.abelianEtaleStalkEquivalence`, Stacks 04JQ), the passage from abelian groups
to `ℤ`-modules with a continuous action, and restriction along the identification of absolute
Galois groups. The identification of constant sheaves with trivial modules is obtained from that
of global sections with invariants by uniqueness of left adjoints, the constant sheaf functor
being left adjoint to global sections and the trivial module functor left adjoint to invariants.

## References

* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry

variable (F : Type u) [Field F] (E : Type u) [Field E] [Algebra F E] [IsSepClosure F E]

/-- The residue field of `Spec F` at the image of the geometric point given by an algebraic
closure, identified with `F`. -/
def fieldResidueRingEquiv :
    F ≃+* (Spec (.of F)).residueField ((GeometricPoint.ofAlgebraicClosure F).hom default) :=
  (Scheme.Spec.preimageIso
    (residuePointIso F (GeometricPoint.ofAlgebraicClosure F))).unop.commRingCatIsoToRingEquiv

/-- The absolute Galois group at the geometric point of `Spec F` given by an algebraic closure
is the Galois group of any separable closure of `F`. -/
def fieldGaloisContinuousMulEquiv :
    Gal(E/F) ≃ₜ* GeometricPoint.absoluteGaloisGroup (GeometricPoint.ofAlgebraicClosure F) :=
  letI := GeometricPoint.residueFieldAlgebra (GeometricPoint.ofAlgebraicClosure F)
  haveI := separableClosure.isSepClosure
    ((Spec (.of F)).residueField ((GeometricPoint.ofAlgebraicClosure F).hom default))
    (GeometricPoint.ofAlgebraicClosure F).residueField
  IsSepClosure.galContinuousMulEquiv E (GeometricPoint.separableClosure
    (GeometricPoint.ofAlgebraicClosure F)) (fieldResidueRingEquiv F)

/-- **Abelian sheaves on the small étale site of the spectrum of a field are discrete Galois
modules.** -/
@[sga "4 VIII 2.2" "partial"]
def fieldEtaleSheafEquiv :
    Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ≌
      ContinuousGModule.{u, max (u + 1) v} Gal(E/F) :=
  (Scheme.smallEtaleSheafEquiv (Spec (.of F)) AddCommGrpCat.{max (u + 1) v}).symm.trans
    ((abelianEtaleStalkEquivalence.{u, max (u + 1) v} (BigEtaleSite.containing (Spec (.of F))) F
      (BigEtaleSite.contains_containing _) (GeometricPoint.ofAlgebraicClosure F)).trans
      ((continuousGModuleEquivContinuousGAddCommGrp _).symm.trans
        (Stacks.GroupCohomology.continuousModuleResEquiv ℤ (fieldGaloisContinuousMulEquiv F E))))

section Restriction

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
  [TopologicalSpace G'] [IsTopologicalGroup G'] (e : G ≃ₜ* G')

/-- The inverse of restriction along an isomorphism of topological groups `e : G ≃ₜ* G'` sends
the trivial `G`-module `A` to the trivial `G'`-module `A`. -/
def continuousModuleResEquivTrivialIso (A : Type (max (u + 1) v)) [AddCommGroup A] :
    (Stacks.GroupCohomology.continuousModuleResEquiv.{0, u, u, max (u + 1) v} ℤ e).inverse.obj
        (Stacks.GroupCohomology.trivialGModule G A) ≅
      Stacks.GroupCohomology.trivialGModule G' A where
  hom := (Stacks.GroupCohomology.gModuleHomEquiv G' _ _).symm ⟨AddMonoidHom.id _, fun _ _ ↦ rfl⟩
  inv := (Stacks.GroupCohomology.gModuleHomEquiv G' _ _).symm ⟨AddMonoidHom.id _, fun _ _ ↦ rfl⟩
  hom_inv_id := Stacks.GroupCohomology.hom_ext fun _ ↦ rfl
  inv_hom_id := Stacks.GroupCohomology.hom_ext fun _ ↦ rfl

/-- Restriction along an isomorphism of topological groups `e : G ≃ₜ* G'` sends the trivial
`G'`-module `A` to the trivial `G`-module `A`. -/
def continuousModuleResEquivFunctorTrivialIso (A : Type (max (u + 1) v)) [AddCommGroup A] :
    (Stacks.GroupCohomology.continuousModuleResEquiv.{0, u, u, max (u + 1) v} ℤ e).functor.obj
        (Stacks.GroupCohomology.trivialGModule G' A) ≅
      Stacks.GroupCohomology.trivialGModule G A where
  hom := (Stacks.GroupCohomology.gModuleHomEquiv G _ _).symm ⟨AddMonoidHom.id _, fun _ _ ↦ rfl⟩
  inv := (Stacks.GroupCohomology.gModuleHomEquiv G _ _).symm ⟨AddMonoidHom.id _, fun _ _ ↦ rfl⟩
  hom_inv_id := Stacks.GroupCohomology.hom_ext fun _ ↦ rfl
  inv_hom_id := Stacks.GroupCohomology.hom_ext fun _ ↦ rfl

include e in
/-- **Cohomology with trivial coefficients is invariant under isomorphisms of topological
groups.** -/
theorem subsingleton_ext_trivialGModule_iff (A : Type (max (u + 1) v)) [AddCommGroup A] (n : ℕ)
    [HasExt.{max (u + 1) v} (ContinuousGModule.{u, max (u + 1) v} G)]
    [HasExt.{max (u + 1) v} (ContinuousGModule.{u, max (u + 1) v} G')] :
    Subsingleton (Abelian.Ext
        (Stacks.GroupCohomology.trivialGModule.{u, max (u + 1) v} G (ULift.{max (u + 1) v} ℤ))
        (Stacks.GroupCohomology.trivialGModule G A) n) ↔
      Subsingleton (Abelian.Ext
        (Stacks.GroupCohomology.trivialGModule.{u, max (u + 1) v} G' (ULift.{max (u + 1) v} ℤ))
        (Stacks.GroupCohomology.trivialGModule G' A) n) := by
  have : EnoughInjectives (ContinuousGModule.{u, max (u + 1) v} G) :=
    continuousGModuleEnoughInjectives.{u, max (u + 1) v} _
  have : EnoughInjectives (ContinuousGModule.{u, max (u + 1) v} G') :=
    continuousGModuleEnoughInjectives.{u, max (u + 1) v} _
  set R := Stacks.GroupCohomology.continuousModuleResEquiv.{0, u, u, max (u + 1) v} ℤ e
  have : R.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : R.symm.functor.Additive := R.toAdjunction.right_adjoint_additive
  let i := Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso R.symm.toAdjunction
    (continuousModuleResEquivTrivialIso.{v} e (ULift.{max (u + 1) v} ℤ)) n
  have j := (i.app (Stacks.GroupCohomology.trivialGModule G' A)).trans
    ((Abelian.extFunctorObj _ n).mapIso (continuousModuleResEquivFunctorTrivialIso.{v} e A))
  exact j.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.symm

end Restriction

section GlobalSections

/-- The invariants of an abelian group with a continuous action, as a functor. -/
def continuousGAddCommGrpInvariants (G : Type u) [Group G] [TopologicalSpace G] :
    ContinuousGAddCommGrp.{u, max (u + 1) v} G ⥤ AddCommGrpCat.{max (u + 1) v} where
  obj M := AddCommGrpCat.of M.obj.obj.addInvariants
  map {M _} f := AddCommGrpCat.ofHom
    ((f.hom.hom.hom.hom.comp M.obj.obj.addInvariants.subtype).codRestrict _ fun x σ ↦
      (ConcreteCategory.congr_hom (f.hom.hom.comm σ) (x : M.obj.obj.V)).symm.trans
        (congrArg f.hom.hom.hom.hom (x.2 σ)))
  map_id _ := rfl
  map_comp _ _ := rfl

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- The germ of a global section is natural in the sheaf. -/
lemma etaleGlobalSectionAbelianGerm_naturality
    {F₁ F₂ : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max (u + 1) v}}
    (f : F₁ ⟶ F₂) (t : F₁.obj.obj (op (SmallEtale.final B (Spec (.of K)) hK))) :
    etaleGlobalSectionAbelianGerm.{u, max (u + 1) v} B K hK sbar F₂ (f.hom.app _ t) =
      ((abelianEtaleStalkEquivalence.{u, max (u + 1) v} B K hK sbar).functor.map f).hom.hom.hom
        (etaleGlobalSectionAbelianGerm.{u, max (u + 1) v} B K hK sbar F₁ t) := by
  have hnat := ConcreteCategory.congr_hom
    ((abelianEtaleStalkEquivalenceIso.{u, max (u + 1) v} B K hK sbar).inv.naturality f)
    (ConcreteCategory.hom (colimit.ι
      ((CategoryOfElements.π (geometricPointFiber B (Spec (.of K)) hK sbar)).op ⋙
        (sheafToPresheaf _ _).obj F₁) (op (finalPointedNeighborhood B K hK sbar))) t)
  refine Eq.trans ?_ hnat
  have hι := ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft
    (CategoryOfElements.π (geometricPointFiber B (Spec (.of K)) hK sbar)).op f.hom)
    (op (finalPointedNeighborhood B K hK sbar))) t
  exact congrArg (fun y ↦ ConcreteCategory.hom
    ((abelianEtaleStalkEquivalenceIso.{u, max (u + 1) v} B K hK sbar).inv.app F₂) y) hι.symm

/-- **Global sections of an abelian sheaf on the small étale site of a field are the invariants of
the associated Galois module**, naturally in the sheaf. -/
def globalSectionsIsoInvariants :
    (sheafSections (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{max (u + 1) v}).obj
        (op (SmallEtale.final B (Spec (.of K)) hK)) ≅
      (abelianEtaleStalkEquivalence.{u, max (u + 1) v} B K hK sbar).functor ⋙
        continuousGAddCommGrpInvariants.{v, u} (GeometricPoint.absoluteGaloisGroup sbar) :=
  NatIso.ofComponents
    (fun F' ↦ (etaleGlobalSectionsAddEquivGaloisInvariants.{u, max (u + 1) v} B K hK sbar
      F').toAddCommGrpIso)
    (fun {F₁ F₂} f ↦ by
      ext t
      exact Subtype.ext (etaleGlobalSectionAbelianGerm_naturality B K hK sbar f t))

/-- Forgetting the `ℤ`-module structure does not change invariants. -/
def continuousGAddCommGrpInvariantsIso (G : Type u) [Group G] [TopologicalSpace G] :
    (continuousGModuleEquivContinuousGAddCommGrp.{u, max (u + 1) v} G).functor ⋙
        continuousGAddCommGrpInvariants.{v, u} G ≅
      continuousGModuleInvariants.{u, max (u + 1) v} G :=
  NatIso.ofComponents (fun _ ↦ AddEquiv.toAddCommGrpIso
    { toFun x := ⟨x.1, x.2⟩
      invFun y := ⟨y.1, y.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }) (fun _ ↦ rfl)

/-- Invariants of discrete modules, after restriction along an isomorphism of topological
groups. -/
def continuousGModuleInvariantsResIso {G H : Type u} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (e : G ≃ₜ* H) :
    continuousGModuleInvariants.{u, max (u + 1) v} H ≅
      (Stacks.GroupCohomology.continuousModuleResEquiv.{0, u, u, max (u + 1) v} ℤ e).functor ⋙
        continuousGModuleInvariants.{u, max (u + 1) v} G :=
  NatIso.ofComponents (fun M ↦ AddEquiv.toAddCommGrpIso
    { toFun x := ⟨x.1, fun σ ↦ x.2 (e σ)⟩
      invFun y := ⟨y.1, fun τ ↦ by
        obtain ⟨σ, rfl⟩ := e.surjective τ
        exact y.2 σ⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }) (fun _ ↦ rfl)

end GlobalSections

section Assembly

variable (F : Type u) [Field F] (E : Type u) [Field E] [Algebra F E] [IsSepClosure F E]

/-- The image of the final object of the small étale site of Stacks 021B in Mathlib's small
étale site is final. -/
def SmallEtale.toEtaleSiteFinalIsTerminal (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    IsTerminal ((SmallEtale.toEtaleSite B S hS).obj (SmallEtale.final B S hS)) :=
  haveI := (inferInstance : MorphismProperty.IsMultiplicative @Etale).toContainsIdentities
  (show IsTerminal (Scheme.Etale.mk (𝟙 S)) from MorphismProperty.Over.mkIdTerminal _ _).ofIso
    (MorphismProperty.Over.isoMk (Iso.refl _) (by simp [SmallEtale.toEtaleSite,
      SmallEtale.final]))

/-- **Global sections of an abelian sheaf on the small étale site of a field are the Galois
invariants of the associated module**, naturally in the sheaf. -/
def fieldEtaleSheafEquivΓIso :
    Sheaf.Γ (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ≅
      (fieldEtaleSheafEquiv.{v} F E).functor ⋙
        continuousGModuleInvariants.{u, max (u + 1) v} Gal(E/F) :=
  Sheaf.ΓNatIsoSheafSections _ _ (SmallEtale.toEtaleSiteFinalIsTerminal _ _ _) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl) ≪≫
    Functor.isoWhiskerLeft
      (Scheme.smallEtaleSheafEquiv (Spec (.of F)) AddCommGrpCat.{max (u + 1) v}).inverse
      (globalSectionsIsoInvariants.{v} _ F _ (GeometricPoint.ofAlgebraicClosure F) ≪≫
        Functor.isoWhiskerLeft _
          ((Functor.leftUnitor _).symm ≪≫
            Functor.isoWhiskerRight
              (continuousGModuleEquivContinuousGAddCommGrp.{u, max (u + 1) v} _).counitIso.symm
              _ ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (continuousGAddCommGrpInvariantsIso.{v} _) ≪≫
            Functor.isoWhiskerLeft _
              (continuousGModuleInvariantsResIso.{v} (fieldGaloisContinuousMulEquiv F E))))

/-- **Constant sheaves on the small étale site of a field are the trivial Galois modules.** -/
def fieldEtaleSheafEquivConstantIso :
    constantSheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
        (fieldEtaleSheafEquiv.{v} F E).functor ≅
      Stacks.GroupCohomology.trivialFunctor.{u, max (u + 1) v} Gal(E/F) :=
  (((constantSheafΓAdj _ _).comp (fieldEtaleSheafEquiv.{v} F E).toAdjunction).ofNatIsoRight
    (Functor.isoWhiskerLeft _ (fieldEtaleSheafEquivΓIso.{v} F E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (fieldEtaleSheafEquiv.{v} F E).counitIso _ ≪≫
      Functor.leftUnitor _)).leftAdjointUniq
    (Stacks.GroupCohomology.trivialFunctorAdjunction _)

/-- The sheaf corresponding to a trivial Galois module is the constant sheaf. -/
def fieldEtaleSheafEquivInverseTrivialIso (A : AddCommGrpCat.{max (u + 1) v}) :
    (fieldEtaleSheafEquiv.{v} F E).inverse.obj
        ((Stacks.GroupCohomology.trivialFunctor.{u, max (u + 1) v} Gal(E/F)).obj A) ≅
      (constantSheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A :=
  (fieldEtaleSheafEquiv.{v} F E).inverse.mapIso
      ((fieldEtaleSheafEquivConstantIso.{v} F E).app A).symm ≪≫
    (fieldEtaleSheafEquiv.{v} F E).unitIso.symm.app _

/-- The restriction of an `ℓ`-power torsion sheaf on Mathlib's small étale site to the small étale
site of Stacks 021B is `ℓ`-power torsion. -/
theorem SmallEtale.isPrimePowerTorsion_sheafEquiv_inverse (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {ℓ : ℕ} (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.IsPrimePowerTorsion _ ℓ G) :
    Stacks.Torsion.IsPrimePowerTorsion _ ℓ
      ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{max (u + 1) v}).inverse.obj G) := by
  intro U t
  obtain ⟨R, hR, hann⟩ := hG ((SmallEtale.toEtaleSite B S hS).obj U) t
  exact ⟨R.functorPullback (SmallEtale.toEtaleSite B S hS),
    (Functor.IsDenseSubsite.functorPushforward_mem_iff).mp
      (Functor.IsCoverDense.functorPullback_pushforward_covering ⟨R, hR⟩),
    fun V f hf ↦ hann _ _ hf⟩

/-- **The stalks of an `ℓ`-power torsion abelian sheaf are `ℓ`-power torsion.** -/
theorem exists_pow_smul_abelianEtaleStalk_eq_zero (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (s : GeometricPoint S) {ℓ : ℕ}
    (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.IsPrimePowerTorsion _ ℓ G)
    (y : (abelianEtaleStalkFunctor.{u, max (u + 1) v} B S hS s).obj G) :
    ∃ k : ℕ, ℓ ^ k • y = 0 := by
  have := forget_preservesFiberColimits.{u, max (u + 1) v} B S hS s
  set D := (CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ G.obj
  obtain ⟨j, t, rfl⟩ := Limits.Concrete.colimit_exists_rep D y
  obtain ⟨⟨U, p⟩⟩ := j
  obtain ⟨R, hR, hann⟩ := hG U t
  obtain ⟨V, f, hf, q, hq⟩ := (geometricPointSitePoint B S hS s).jointly_surjective R hR p
  obtain ⟨r, -, hr⟩ := hann V f hf
  refine ⟨r, ?_⟩
  have hw : ConcreteCategory.hom (colimit.ι D (op ⟨U, p⟩)) t =
      ConcreteCategory.hom (colimit.ι D (op ⟨V, q⟩)) (ConcreteCategory.hom (G.obj.map f.op) t) :=
    (ConcreteCategory.congr_hom (colimit.w D
      (CategoryOfElements.homMk ⟨V, q⟩ ⟨U, p⟩ f hq).op) t).symm
  rw [hw]
  have h := map_nsmul (ConcreteCategory.hom (colimit.ι D (op ⟨V, q⟩))) (ℓ ^ r)
    (ConcreteCategory.hom (G.obj.map f.op) t)
  rw [hr, map_zero] at h
  exact h.symm

/-- If the image of `x` under an additive equivalence is `ℓ`-power torsion, so is `x`. -/
private theorem exists_pow_smul_eq_zero_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (ψ : A ≃+ B) {ℓ : ℕ} (x : A) (h : ∃ k : ℕ, ℓ ^ k • ψ x = 0) : ∃ k : ℕ, ℓ ^ k • x = 0 :=
  h.imp fun _ hk ↦ ψ.injective ((map_nsmul ψ _ x).trans (hk.trans (map_zero ψ).symm))

/-- The Galois module of an `ℓ`-power torsion sheaf of Stacks 021B is `ℓ`-power torsion. -/
theorem exists_pow_smul_abelianEtaleStalkEquivalence_eq_zero (B : BigEtaleSite.{u})
    (hK : B.Contains (Spec (.of F))) (sbar : GeometricPoint (Spec (.of F))) {ℓ : ℕ}
    (G : Sheaf (SmallEtale.topology B (Spec (.of F)) hK) AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.IsPrimePowerTorsion _ ℓ G)
    (x : ((abelianEtaleStalkEquivalence.{u, max (u + 1) v} B F hK sbar).functor.obj G).obj.obj.V) :
    ∃ k : ℕ, ℓ ^ k • x = 0 := by
  exact exists_pow_smul_eq_zero_of_addEquiv
    (etaleGaloisModuleAddEquivStalk.{u, max (u + 1) v} B F hK sbar G) x
    (exists_pow_smul_abelianEtaleStalk_eq_zero.{v} B _ hK sbar G hG _)

/-- Changing the encoding of a discrete module preserves `ℓ`-power torsion. -/
theorem exists_pow_smul_continuousGModuleEquiv_inverse_eq_zero {G : Type u} [Group G]
    [TopologicalSpace G] {ℓ : ℕ} (Y : ContinuousGAddCommGrp.{u, max (u + 1) v} G)
    (hY : ∀ y : Y.obj.obj.V, ∃ k : ℕ, ℓ ^ k • y = 0)
    (x : ((continuousGModuleEquivContinuousGAddCommGrp.{u, max (u + 1) v} G).inverse.obj
      Y).obj.obj.V) : ∃ k : ℕ, ℓ ^ k • x = 0 := by
  let ψ := ((ContinuousGAddCommGrp.forget G).mapIso
    ((continuousGModuleEquivContinuousGAddCommGrp.{u, max (u + 1) v} G).counitIso.app
      Y)).addCommGroupIsoToAddEquiv
  exact exists_pow_smul_eq_zero_of_addEquiv ψ x (hY _)

/-- **An `ℓ`-power torsion abelian sheaf on the small étale site of a field corresponds to an
`ℓ`-power torsion Galois module.** -/
theorem exists_pow_smul_fieldEtaleSheafEquiv_eq_zero {ℓ : ℕ}
    (G : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : Stacks.Torsion.IsPrimePowerTorsion _ ℓ G)
    (x : ((fieldEtaleSheafEquiv.{v} F E).functor.obj G).obj.obj.V) :
    ∃ k : ℕ, ℓ ^ k • x = 0 :=
  exists_pow_smul_continuousGModuleEquiv_inverse_eq_zero.{v} _
    (exists_pow_smul_abelianEtaleStalkEquivalence_eq_zero.{v} F _ _ _ _
      (SmallEtale.isPrimePowerTorsion_sheafEquiv_inverse.{v} _ _ _ G hG)) x

/-- The sheaf corresponding to a Galois module killed by `ℓ` is killed by `ℓ`. -/
theorem nsmul_id_fieldEtaleSheafEquiv_inverse_eq_zero {ℓ : ℕ}
    (M : ContinuousGModule.{u, max (u + 1) v} Gal(E/F)) (hM : ∀ x : M.obj.obj.V, ℓ • x = 0) :
    ℓ • 𝟙 ((fieldEtaleSheafEquiv.{v} F E).inverse.obj M) = 0 := by
  have : (fieldEtaleSheafEquiv.{v} F E).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  rw [← (fieldEtaleSheafEquiv.{v} F E).inverse.map_id, ← Functor.map_nsmul,
    show ℓ • 𝟙 M = 0 from Stacks.GroupCohomology.hom_ext fun x ↦ hM x, Functor.map_zero]

/-- The sheaf corresponding to a Galois module killed by `ℓ` is `ℓ`-power torsion. -/
theorem isPrimePowerTorsion_fieldEtaleSheafEquiv_inverse {ℓ : ℕ}
    (M : ContinuousGModule.{u, max (u + 1) v} Gal(E/F)) (hM : ∀ x : M.obj.obj.V, ℓ • x = 0) :
    Stacks.Torsion.IsPrimePowerTorsion _ ℓ ((fieldEtaleSheafEquiv.{v} F E).inverse.obj M) :=
  Stacks.Torsion.isPrimePowerTorsion_of_nsmul_id_eq_zero _
    (nsmul_id_fieldEtaleSheafEquiv_inverse_eq_zero.{v} F E M hM)

section Ext

variable [HasExt.{max (u + 1) v}
    (Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{max (u + 1) v} (ContinuousGModule.{u, max (u + 1) v} Gal(E/F))]

/-- **Étale cohomology of the spectrum of a field is Galois cohomology**, in the form of `Ext`
out of the constant sheaf `ℤ`, respectively out of the trivial module `ℤ`, naturally in the
sheaf. -/
def fieldEtaleExtIso (n : ℕ) :
    Abelian.extFunctorObj ((constantSheaf (Spec (.of F)).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) n ≅
      (fieldEtaleSheafEquiv.{v} F E).functor ⋙
        Abelian.extFunctorObj (Stacks.GroupCohomology.trivialGModule.{u, max (u + 1) v} Gal(E/F)
          (ULift.{max (u + 1) v} ℤ)) n :=
  haveI : EnoughInjectives (ContinuousGModule.{u, max (u + 1) v} Gal(E/F)) :=
    continuousGModuleEnoughInjectives.{u, max (u + 1) v} _
  haveI : (fieldEtaleSheafEquiv.{v} F E).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (fieldEtaleSheafEquiv.{v} F E).symm.functor.Additive :=
    (fieldEtaleSheafEquiv.{v} F E).toAdjunction.right_adjoint_additive
  Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso
    (fieldEtaleSheafEquiv.{v} F E).symm.toAdjunction
    (fieldEtaleSheafEquivInverseTrivialIso.{v} F E _) n

end Ext

/-- **Vanishing of étale cohomology of the spectrum of a field is vanishing of Galois
cohomology** of the associated module, for any choice of `Ext` groups of étale sheaves. -/
theorem subsingleton_sheafH_iff
    [HasExt.{max (u + 1) v} (ContinuousGModule.{u, max (u + 1) v} Gal(E/F))]
    [h : HasExt (Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (G : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (n : ℕ) :
    Subsingleton (Sheaf.H G n) ↔
      Subsingleton (Abelian.Ext (Stacks.GroupCohomology.trivialGModule.{u, max (u + 1) v}
        Gal(E/F) (ULift.{max (u + 1) v} ℤ)) ((fieldEtaleSheafEquiv.{v} F E).functor.obj G) n) := by
  let h' : HasExt.{max (u + 1) v}
      (Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    hasExt_of_enoughInjectives _
  exact ((@Abelian.Ext.chgUniv _ _ _ h h' _ _ n).trans
    ((fieldEtaleExtIso.{v} F E n).app G).addCommGroupIsoToAddEquiv.toEquiv).subsingleton_congr

end Assembly

end AlgebraicGeometry

end
