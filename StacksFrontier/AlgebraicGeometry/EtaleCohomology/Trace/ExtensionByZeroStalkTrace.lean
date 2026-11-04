module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# Stalks of an extension by zero at rational points

For an open immersion `j : U ⟶ X` and a sheaf of `Λ`-modules `K` on `U_étale`, the stalk of
`j_! K` at the geometric point over a rational point `x = j(u)` is the stalk of `K` at the
geometric point over `u`, compatibly with the geometric Frobenius `π_x` of [Stacks, Tag 03SW], and
it vanishes at a rational point off `U`.  This identifies the stalk side of the trace formula of
[Stacks, Tag 03UG] for `j_! K` on a compactification with the one for `K`.

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroStalkIso`, `extensionByZeroStalkComplexIso`.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero`
* `Stacks.EtaleCohomology.isZero_rationalPointStalkComplex_extensionByZero`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]

/-- `j^{-1} j_! ≅ 𝟭` for an open immersion `j`. -/
def extensionByZeroInverseImageIso :
    etaleModuleExtensionByZero.{u, r} Λ j ⋙ etaleModuleInverseImage.{u, r} Λ j ≅
      𝟭 (EtaleModules.{u, r} Λ U) :=
  Functor.isoWhiskerLeft _ (etaleModuleInverseImageRestrictionIso.{u, r} Λ j) ≪≫
    (asIso (etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit).symm

variable (u' : Spec (.of k) ⟶ U) (x : Spec (.of k) ⟶ X) (hx : u' ≫ j = x)

include hx in
/-- **The stalk of an extension by zero at a rational point of the open**: `(j_! K)_{x̄} ≅ K_{ū}`
for `x = j(u)`, naturally in `K`. -/
def extensionByZeroStalkIso :
    etaleModuleExtensionByZero.{u, r} Λ j ⋙ rationalPointStalkFunctor.{u, r} Λ K x ≅
      rationalPointStalkFunctor.{u, r} Λ K u' :=
  Functor.isoWhiskerLeft _ (rationalPointStalkPullbackIso Λ j K u' x hx).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extensionByZeroInverseImageIso Λ j) _ ≪≫
    Functor.leftUnitor _

include hx in
/-- The stalk isomorphism of an extension by zero intertwines the geometric Frobenius. -/
theorem geometricFrobeniusStalkFunctor_comp_extensionByZeroStalkIso_hom [Fintype k]
    (p q : ℕ) [Fact p.Prime] [CharP K p] (hcard : Fintype.card k = p ^ q)
    (M : EtaleModules.{u, r} Λ U) :
    (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) K p q hcard x).app
        ((etaleModuleExtensionByZero.{u, r} Λ j).obj M) ≫
      (extensionByZeroStalkIso Λ j K u' x hx).hom.app M =
    (extensionByZeroStalkIso Λ j K u' x hx).hom.app M ≫
      (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) K p q hcard u').app M := by
  have h₁ := geometricFrobeniusStalkFunctor_comp_rationalPointStalkPullbackIso_hom Λ j K u' x hx
    p q hcard ((etaleModuleExtensionByZero.{u, r} Λ j).obj M)
  have h₂ :=
    (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) K p q hcard u').naturality
      ((extensionByZeroInverseImageIso Λ j).hom.app M)
  simp only [extensionByZeroStalkIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  exact frobeniusStalkIsoChase h₁ (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _) h₂.symm

include hx in
/-- The stalk of an extension by zero at a rational point of the open, degreewise on a bounded
below complex. -/
def extensionByZeroStalkComplexIso (M : CochainComplex.Plus (EtaleModules.{u, r} Λ U)) :
    rationalPointStalkComplex.{u, r} Λ K x
        ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj M) ≅
      rationalPointStalkComplex.{u, r} Λ K u' M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (extensionByZeroStalkIso Λ j K u' x hx).app (M.obj.X n))
    (fun a b _ => ((extensionByZeroStalkIso Λ j K u' x hx).hom.naturality (M.obj.d a b)).symm)

include hx in
/-- **The local trace of an extension by zero at a rational point of the open** is the local
trace there. -/
theorem perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero [Fintype k] (p q : ℕ)
    [Fact p.Prime] [CharP K p] (hcard : Fintype.card k = p ^ q)
    (M : CochainComplex.Plus (EtaleModules.{u, r} Λ U))
    (hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r}
      Λ K x ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj M))))
    (hU : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ K u' M))) :
    CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hX⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ K p q hcard x
          ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj M))) =
      CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hU⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ K p q hcard u' M)) := by
  refine CategoryTheory.FilteredDerived.perfectDerivedTrace_congr Λ _ _
    (DerivedCategory.Q.mapIso (extensionByZeroStalkComplexIso Λ j K u' x hx M)) _ _ ?_
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  exact geometricFrobeniusStalkFunctor_comp_extensionByZeroStalkIso_hom Λ j K u' x hx p q hcard
    (M.obj.X n)

/-- **The stalk of an extension by zero vanishes at a rational point off the open.** -/
theorem isZero_rationalPointStalkFunctor_obj_extensionByZero (x : Spec (.of k) ⟶ X)
    (hx : x default ∉ Set.range j) (M : EtaleModules.{u, r} Λ U) :
    IsZero ((rationalPointStalkFunctor.{u, r} Λ K x).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj M)) := by
  have hd : Disjoint (Set.range x) (Set.range j) := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩
    have : t = default := Subsingleton.elim _ _
    exact this ▸ hx
  refine IsZero.of_iso ?_ ((rationalPointStalkPullbackIso Λ x K (𝟙 _) x
    (Category.id_comp _)).app _).symm
  exact Functor.map_isZero (rationalPointStalkFunctor.{u, r} Λ K (𝟙 _))
    (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ x j hd M)

/-- The stalk complex of an extension by zero vanishes at a rational point off the open. -/
theorem isZero_rationalPointStalkComplex_extensionByZero (x : Spec (.of k) ⟶ X)
    (hx : x default ∉ Set.range j) (M : CochainComplex.Plus (EtaleModules.{u, r} Λ U)) :
    IsZero (rationalPointStalkComplex.{u, r} Λ K x
      ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.obj M)) := by
  rw [IsZero.iff_id_eq_zero]
  ext n : 1
  exact (isZero_rationalPointStalkFunctor_obj_extensionByZero Λ j K x hx (M.obj.X n)).eq_of_src _ _

end Stacks.EtaleCohomology

end
