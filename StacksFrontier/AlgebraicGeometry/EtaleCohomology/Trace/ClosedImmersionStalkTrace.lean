module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PullbackStalkFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace

/-!
# Stalks of a direct image along a closed immersion at rational points

For a closed immersion `i : Z ⟶ Y` and a sheaf of `Λ`-modules `M` on `Z_étale`, the stalk of
`i_* M` at the geometric point over a rational point `x = i(z)` is the stalk of `M` at the one
over `z`, compatibly with the geometric Frobenius of [Stacks, Tag 03SW], and it vanishes at a
rational point off `Z`.

## Main definitions

* `Stacks.EtaleCohomology.closedImmersionStalkIso`: `(i_* M)_{x̄} ≅ M_{z̄}` for `x = i(z)`,
  naturally in `M`.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_rationalPointStalkFrobenius_directImage`: the local
  trace of the Frobenius on the stalk complex of `i_* M` at `x = i(z)` is the one of `M` at `z`.
* `Stacks.EtaleCohomology.isZero_rationalPointStalkComplex_directImage`: the stalk complex of
  `i_* M` vanishes at a rational point off `Z`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {Z Y : Scheme.{u}} (i : Z ⟶ Y)
  [IsClosedImmersion i] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
  (z : Spec (.of k) ⟶ Z) (x : Spec (.of k) ⟶ Y) (hx : z ≫ i = x)

/-- For a closed immersion `i`, the counit `i⁻¹ i_* ⟶ 𝟭` of the adjunction between inverse and
direct image of étale sheaves of `Λ`-modules is an isomorphism. -/
instance isIso_etaleModuleInverseImageAdj_counit :
    IsIso (etaleModuleInverseImageAdj.{u, r} Λ i).counit := by
  let ff := etaleModuleDirectImageFullyFaithful.{u, r} Λ i
  let _ := ff.full
  let _ := ff.faithful
  infer_instance

include hx in
/-- **The stalk of a direct image along a closed immersion at a rational point of the closed
subscheme**: `(i_* M)_{x̄} ≅ M_{z̄}` for `x = i(z)`, naturally in `M`. -/
def closedImmersionStalkIso :
    etaleModuleDirectImage.{u, r} Λ i ⋙ rationalPointStalkFunctor.{u, r} Λ K x ≅
      rationalPointStalkFunctor.{u, r} Λ K z :=
  Functor.isoWhiskerLeft _ (rationalPointStalkPullbackIso Λ i K z x hx).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (etaleModuleInverseImageAdj.{u, r} Λ i).counit) _ ≪≫
    Functor.leftUnitor _

/-- If `e` intertwines `π'` with `π`, `e'` is inverse to `e`, and `c` intertwines `π'` with `πD`,
then `e' ≫ c ≫ 𝟙 D` intertwines `π` with `πD`. -/
lemma frobeniusStalkIsoChase {C : Type*} [Category* C] {A B D : C} {π' : A ⟶ A} {e : A ⟶ B}
    {e' : B ⟶ A} {π : B ⟶ B} {c : A ⟶ D} {πD : D ⟶ D} (h₁ : π' ≫ e = e ≫ π)
    (hi : e' ≫ e = 𝟙 B) (hi' : e ≫ e' = 𝟙 A) (h₂ : π' ≫ c = c ≫ πD) :
    π ≫ e' ≫ c ≫ 𝟙 D = (e' ≫ c ≫ 𝟙 D) ≫ πD := by
  simp only [Category.comp_id]
  have : π ≫ e' = e' ≫ π' := by
    rw [← Category.id_comp (π ≫ e'), ← hi, Category.assoc, ← reassoc_of% h₁, hi',
      Category.comp_id]
  rw [reassoc_of% this, h₂, Category.assoc]

include hx in
/-- The stalk isomorphism of a closed immersion intertwines the geometric Frobenius. -/
theorem geometricFrobeniusStalkFunctor_comp_closedImmersionStalkIso_hom [Fintype k]
    (p q : ℕ) [Fact p.Prime] [CharP K p] (hcard : Fintype.card k = p ^ q)
    (M : EtaleModules.{u, r} Λ Z) :
    (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) K p q hcard x).app
        ((etaleModuleDirectImage.{u, r} Λ i).obj M) ≫
      (closedImmersionStalkIso Λ i K z x hx).hom.app M =
    (closedImmersionStalkIso Λ i K z x hx).hom.app M ≫
      (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) K p q hcard z).app M := by
  have h₁ := geometricFrobeniusStalkFunctor_comp_rationalPointStalkPullbackIso_hom Λ i K z x hx
    p q hcard ((etaleModuleDirectImage.{u, r} Λ i).obj M)
  have h₂ := (geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) K p q hcard z).naturality
    ((etaleModuleInverseImageAdj.{u, r} Λ i).counit.app M)
  simp only [closedImmersionStalkIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    asIso_hom, Category.id_comp]
  exact frobeniusStalkIsoChase h₁ (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _) h₂.symm

include hx in
/-- The stalk of a direct image along a closed immersion at a rational point of the closed
subscheme, degreewise on a bounded below complex. -/
def closedImmersionStalkComplexIso (M : CochainComplex.Plus (EtaleModules.{u, r} Λ Z)) :
    rationalPointStalkComplex.{u, r} Λ K x
        ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj M) ≅
      rationalPointStalkComplex.{u, r} Λ K z M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (closedImmersionStalkIso Λ i K z x hx).app (M.obj.X n))
    (fun a b _ => ((closedImmersionStalkIso Λ i K z x hx).hom.naturality (M.obj.d a b)).symm)

include hx in
/-- **The local trace of a direct image along a closed immersion at a rational point of the
closed subscheme** is the local trace there. -/
theorem perfectDerivedTrace_rationalPointStalkFrobenius_directImage [Fintype k] (p q : ℕ)
    [Fact p.Prime] [CharP K p] (hcard : Fintype.card k = p ^ q)
    (M : CochainComplex.Plus (EtaleModules.{u, r} Λ Z))
    (hY : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r}
      Λ K x ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj M))))
    (hZ : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ K z M))) :
    CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hY⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ K p q hcard x
          ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj M))) =
      CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, hZ⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ K p q hcard z M)) := by
  refine CategoryTheory.FilteredDerived.perfectDerivedTrace_congr Λ _ _
    (DerivedCategory.Q.mapIso (closedImmersionStalkComplexIso Λ i K z x hx M)) _ _ ?_
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  exact geometricFrobeniusStalkFunctor_comp_closedImmersionStalkIso_hom Λ i K z x hx p q hcard
    (M.obj.X n)

/-- **The stalk of a direct image along a closed immersion vanishes at a rational point off the
closed subscheme.** -/
theorem isZero_rationalPointStalkFunctor_obj_directImage (x : Spec (.of k) ⟶ Y)
    (hx : x default ∉ Set.range i) (M : EtaleModules.{u, r} Λ Z) :
    IsZero ((rationalPointStalkFunctor.{u, r} Λ K x).obj
      ((etaleModuleDirectImage.{u, r} Λ i).obj M)) := by
  let U : Y.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hxU : Set.range x ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact Subsingleton.elim t default ▸ hx
  let x' : Spec (.of k) ⟶ U := IsOpenImmersion.lift U.ι x (by rw [U.range_ι]; exact hxU)
  have hx' : x' ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  exact (Functor.map_isZero (rationalPointStalkFunctor.{u, r} Λ K x')
    (isZero_etaleModuleInverseImage_directImage Λ i U.ι U.range_ι M)).of_iso
    ((rationalPointStalkPullbackIso Λ U.ι K x' x hx').app _).symm

/-- The stalk complex of a direct image along a closed immersion vanishes at a rational point off
the closed subscheme. -/
theorem isZero_rationalPointStalkComplex_directImage (x : Spec (.of k) ⟶ Y)
    (hx : x default ∉ Set.range i) (M : CochainComplex.Plus (EtaleModules.{u, r} Λ Z)) :
    IsZero (rationalPointStalkComplex.{u, r} Λ K x
      ((etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus.obj M)) := by
  rw [IsZero.iff_id_eq_zero]
  ext n : 1
  exact (isZero_rationalPointStalkFunctor_obj_directImage Λ i K x hx (M.obj.X n)).eq_of_src _ _

end Stacks.EtaleCohomology

end
