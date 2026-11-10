module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.AffineCore
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.RingHeart

/-!
# Maps of extended complexes along a directed system of rings

Let `R ⟶ A_j` be a directed system of `R`-algebras with colimit `A`, and let `C`, `C'` be
complexes of `R`-modules with `C` bounded and of finitely presented terms. In the homotopy
category, the maps `A ⊗_R C ⟶ A ⊗_R C'` are the filtered colimit of the maps
`A_j ⊗_R C ⟶ A_j ⊗_R C'`: every map over `A` is `A ⊗_{A_j} v` for a chain map `v` at some stage,
and two chain maps `C ⟶ C'` whose extensions agree over `A` up to homotopy already do so at a
stage. This is the ring-level input of the full faithfulness of Stacks 09RI–09RJ over affine
stages: transposing along extension of scalars turns maps out of `A_j ⊗_R C` into maps
`C ⟶ A_j ⊗_R C'` of complexes of `R`-modules, to which
`Stacks.LimitHomDescent.isStagesColimit_homotopy` applies.

## Main results

* `Stacks.LimitHomDescent.Affine.RingSystem.exists_le_Qh_map_ext_eq`: eventual injectivity.
* `Stacks.LimitHomDescent.Affine.RingSystem.exists_Qh_map_ext_eq`: every map over the colimit
  comes from a stage.

## References

* [Stacks Project, Tag 09RE](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.FilteredColimitHom (Qh)
open scoped ChangeOfRings TensorProduct

universe v u

namespace Stacks.LimitHomDescent.Affine

variable {R A : CommRingCat.{u}}

/-- The unit `C' ⟶ A ⊗_R C'` of extension of scalars, degreewise on complexes. -/
abbrev unitCx (f : R ⟶ A) (C' : CochainComplex (ModuleCat.{u} R) ℤ) :
    C' ⟶ ((ModuleCat.restrictScalars.{u} f.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((ext f).obj C') :=
  (Adjunction.mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom)
    (ComplexShape.up ℤ)).unit.app C'

/-- **The transpose of `A ⊗_R u` is `u` followed by the unit.** -/
theorem homEquiv_ext_map (f : R ⟶ A) {C C' : CochainComplex (ModuleCat.{u} R) ℤ} (u : C ⟶ C') :
    (Adjunction.mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom)
      (ComplexShape.up ℤ)).homEquiv C ((ext f).obj C') ((ext f).map u) = u ≫ unitCx f C' := by
  rw [Adjunction.homEquiv_unit]
  exact ((Adjunction.mapHomologicalComplexAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom)
      (ComplexShape.up ℤ)).unit.naturality u).symm

/-- **Two maps `A ⊗_R C ⟶ A ⊗_R C'` agree in the homotopy category as soon as their transposes
do.** -/
theorem Qh_map_ext_eq_of_comp_unitCx (f : R ⟶ A) {C C' : CochainComplex (ModuleCat.{u} R) ℤ}
    (u w : C ⟶ C') (h : (Qh R).map (u ≫ unitCx f C') = (Qh R).map (w ≫ unitCx f C')) :
    (Qh A).map ((ext f).map u) = (Qh A).map ((ext f).map w) := by
  let adj := Adjunction.mapHomologicalComplexAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom) (ComplexShape.up ℤ)
  have tri : ∀ v : C ⟶ C', (ext f).map (v ≫ unitCx f C') ≫ adj.counit.app ((ext f).obj C') =
      (ext f).map v := fun v => by
    rw [Functor.map_comp, Category.assoc]
    exact (congrArg ((ext f).map v ≫ ·) (adj.left_triangle_components C')).trans
      (Category.comp_id _)
  have H := ((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomotopy
    (HomotopyCategory.homotopyOfEq _ _ h)).compRight (adj.counit.app ((ext f).obj C'))
  rw [tri, tri] at H
  exact HomotopyCategory.eq_of_homotopy _ _ H

/-- **The transpose of `Qh (A ⊗_R u)` is `Qh u` followed by the unit**, in the homotopy
category. -/
theorem Qh_map_comp_unitCx_of_Qh_map_ext_eq (f : R ⟶ A) {C C' : CochainComplex (ModuleCat.{u} R) ℤ}
    (u w : C ⟶ C') (h : (Qh A).map ((ext f).map u) = (Qh A).map ((ext f).map w)) :
    (Qh R).map (u ≫ unitCx f C') = (Qh R).map (w ≫ unitCx f C') := by
  let adj := Adjunction.mapHomologicalComplexAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom) (ComplexShape.up ℤ)
  have H := ((ModuleCat.restrictScalars.{u} f.hom).mapHomotopy
    (HomotopyCategory.homotopyOfEq _ _ h)).compLeft (adj.unit.app C)
  have e : ∀ v : C ⟶ C', adj.unit.app C ≫
      ((ModuleCat.restrictScalars.{u} f.hom).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((ext f).map v) = v ≫ unitCx f C' :=
    fun v => (adj.unit.naturality v).symm
  rw [e, e] at H
  exact HomotopyCategory.eq_of_homotopy _ _ H

/-- `A' ⊗_A (A ⊗_R C) ≅ A' ⊗_R C` along a factorisation `f ≫ β = f'`, degreewise. -/
def extCompIsoOf {A' : CommRingCat.{u}} (f : R ⟶ A) (β : A ⟶ A') (f' : R ⟶ A') (h : f ≫ β = f')
    (C : CochainComplex (ModuleCat.{u} R) ℤ) : (ext β).obj ((ext f).obj C) ≅ (ext f').obj C :=
  extComp f β C ≪≫ eqToIso (by rw [h])

/-- **Transposing along extension of scalars carries `tau` to extension of scalars along `β`**,
for a factorisation `f ≫ β = f'`. -/
theorem transposeCx_comp_tau {A' : CommRingCat.{u}} (f : R ⟶ A) (f' : R ⟶ A') (β : A ⟶ A')
    (h : f ≫ β = f') {P N : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : P ⟶ ((resExt f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :
    transposeCx f' (Z := (ext f').obj N)
        (g ≫ (NatTrans.mapHomologicalComplex (tau f f' β h) (ComplexShape.up ℤ)).app N) =
      (extCompIsoOf f β f' h P).inv ≫ (ext β).map (transposeCx f (Z := (ext f).obj N) g) ≫
        (extCompIsoOf f β f' h N).hom := by
  subst h
  simpa [extCompIsoOf, tau_rfl] using transposeCx_comp_tau₀ f β g

/-- Transposition along extension of scalars respects homotopy. -/
theorem Qh_map_transposeCx_eq (f : R ⟶ A) {P N : CochainComplex (ModuleCat.{u} R) ℤ}
    (g g' : P ⟶ ((ModuleCat.restrictScalars.{u} f.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((ext f).obj N)) (h : (Qh R).map g = (Qh R).map g') :
    (Qh A).map (transposeCx f (Z := (ext f).obj N) g) =
      (Qh A).map (transposeCx f (Z := (ext f).obj N) g') := by
  let adj := Adjunction.mapHomologicalComplexAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom) (ComplexShape.up ℤ)
  have e : ∀ k : P ⟶ ((ModuleCat.restrictScalars.{u} f.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((ext f).obj N),
      transposeCx f (Z := (ext f).obj N) k = (ext f).map k ≫ adj.counit.app _ :=
    fun k => adj.homEquiv_counit _ _ k
  rw [e, e]
  exact HomotopyCategory.eq_of_homotopy _ _ (((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomotopy
    (HomotopyCategory.homotopyOfEq _ _ h)).compRight _)

namespace RingSystem

variable {J : Type v} [Preorder J] (S : RingSystem.{v, u} R J)

/-- The unit `C' ⟶ A_i ⊗_R C'` followed by the transition map `A_i ⊗_R C' ⟶ A_j ⊗_R C'` is the
unit `C' ⟶ A_j ⊗_R C'`. -/
theorem unitCx_comp_tcx {i j : J} (h : i ≤ j) (C' : CochainComplex (ModuleCat.{u} R) ℤ) :
    unitCx (S.φ i) C' ≫ S.tcx C' h = unitCx (S.φ j) C' := by
  ext n x
  change (tau (S.φ i) (S.φ j) (S.β h) (S.φ_β h)).app (C'.X n) ((1 : S.A i) ⊗ₜ[R, (S.φ i).hom] x) =
    (1 : S.A j) ⊗ₜ[R, (S.φ j).hom] x
  rw [tau_app_tmul, map_one]

/-- The unit `C' ⟶ A_j ⊗_R C'` followed by the map `A_j ⊗_R C' ⟶ A ⊗_R C'` to the colimit is the
unit `C' ⟶ A ⊗_R C'`. -/
theorem unitCx_comp_ιcx (j : J) (C' : CochainComplex (ModuleCat.{u} R) ℤ) :
    unitCx (S.φ j) C' ≫ S.ιcx C' j = unitCx S.φlim C' := by
  ext n x
  change (tau (S.φ j) S.φlim (S.γ j) (S.φ_γ j)).app (C'.X n) ((1 : S.A j) ⊗ₜ[R, (S.φ j).hom] x) =
    (1 : S.lim) ⊗ₜ[R, S.φlim.hom] x
  rw [tau_app_tmul, map_one]

/-- Maps in the homotopy category from `C` into the stages `A_j ⊗_R C'` form a filtered colimit
over `A ⊗_R C'`. -/
private theorem isStagesColimit_homotopy_stageCx [IsDirected J (· ≤ ·)] [Nonempty J]
    (hcol : Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : S.A i) => S.β h x)
      (fun j (x : S.A j) => S.γ j x))
    {C C' : CochainComplex (ModuleCat.{u} R) ℤ} (hC : {n : ℤ | ¬ IsZero (C.X n)}.Finite)
    (hfp : ∀ n : ℤ, Module.FinitePresentation R (C.X n)) :
    Stacks.IsStagesColimit
      (fun i j (h : i ≤ j) (ψ : (Qh R).obj C ⟶ (Qh R).obj (S.stageCx C' i)) =>
        ψ ≫ (Qh R).map (S.tcx C' h))
      (fun j (ψ : (Qh R).obj C ⟶ (Qh R).obj (S.stageCx C' j)) =>
        ψ ≫ (Qh R).map (S.ιcx C' j)) := by
  have hst := S.isStagesColimit_stageCx C' hcol
  exact isStagesColimit_homotopy (E := C) (fun _ _ _ h h' => S.tcx_comp C' h h')
    (fun _ _ h => S.tcx_ιcx C' h)
    (fun n x => (hst n).exists_stage x)
    (fun n j y hy => (hst n).exists_trans_eq j y 0 (hy.trans (map_zero _).symm) |>.imp
      fun k => Exists.imp fun _ hk => hk.trans (map_zero _))
    hC.toFinset (fun n hn => Or.inl (by simpa using hn)) hfp

variable [IsDirected J (· ≤ ·)] [Nonempty J]
  (hcol : Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : S.A i) => S.β h x)
    (fun j (x : S.A j) => S.γ j x))
  {C C' : CochainComplex (ModuleCat.{u} R) ℤ} (hC : {n : ℤ | ¬ IsZero (C.X n)}.Finite)
  (hfp : ∀ n : ℤ, Module.FinitePresentation R (C.X n))

include hcol hC hfp in
/-- **Eventual injectivity**: two chain maps `u, w : C ⟶ C'` whose extensions to the colimit `A`
agree in the homotopy category already have homotopic extensions to some stage `A_j`. -/
theorem exists_le_Qh_map_ext_eq (u w : C ⟶ C')
    (h : (Qh S.lim).map ((ext S.φlim).map u) = (Qh S.lim).map ((ext S.φlim).map w)) :
    ∃ j : J, (Qh (S.A j)).map ((ext (S.φ j)).map u) = (Qh (S.A j)).map ((ext (S.φ j)).map w) := by
  obtain ⟨j₀⟩ := ‹Nonempty J›
  have h' := Qh_map_comp_unitCx_of_Qh_map_ext_eq S.φlim u w h
  rw [← S.unitCx_comp_ιcx j₀, ← Category.assoc, ← Category.assoc, Functor.map_comp,
    Functor.map_comp (Qh R) (w ≫ unitCx (S.φ j₀) C')] at h'
  obtain ⟨k, hk, hk'⟩ := (S.isStagesColimit_homotopy_stageCx hcol hC hfp).exists_trans_eq _ _ _ h'
  refine ⟨k, Qh_map_ext_eq_of_comp_unitCx (S.φ k) u w ?_⟩
  rwa [← S.unitCx_comp_tcx hk, ← Category.assoc, ← Category.assoc, Functor.map_comp,
    Functor.map_comp (Qh R) (w ≫ unitCx (S.φ j₀) C')]

include hcol hC hfp in
/-- **Every map over the colimit comes from a stage**: a chain map `v : A ⊗_R C ⟶ A ⊗_R C'` is,
in the homotopy category, `A ⊗_{A_j} t` for a chain map `t : A_j ⊗_R C ⟶ A_j ⊗_R C'` at some
stage `j`. -/
theorem exists_Qh_map_ext_eq (v : (ext S.φlim).obj C ⟶ (ext S.φlim).obj C') :
    ∃ (j : J) (t : (ext (S.φ j)).obj C ⟶ (ext (S.φ j)).obj C'),
      (Qh S.lim).map ((extCompIsoOf (S.φ j) (S.γ j) S.φlim (S.φ_γ j) C).inv ≫
        (ext (S.γ j)).map t ≫ (extCompIsoOf (S.φ j) (S.γ j) S.φlim (S.φ_γ j) C').hom) =
        (Qh S.lim).map v := by
  let adj := Adjunction.mapHomologicalComplexAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} S.φlim.hom) (ComplexShape.up ℤ)
  let v' : C ⟶ S.limCx C' := adj.homEquiv _ _ v
  obtain ⟨j, ψ, hψ⟩ :=
    (S.isStagesColimit_homotopy_stageCx hcol hC hfp).exists_stage ((Qh R).map v')
  obtain ⟨t₀, rfl⟩ := (Qh R).map_surjective ψ
  refine ⟨j, transposeCx (S.φ j) (Z := (ext (S.φ j)).obj C') t₀, ?_⟩
  rw [← transposeCx_comp_tau]
  have hv : transposeCx S.φlim (Z := (ext S.φlim).obj C') v' = v :=
    (adj.homEquiv _ _).symm_apply_apply v
  rw [← hv]
  exact Qh_map_transposeCx_eq S.φlim _ _ (((Qh R).map_comp _ _).trans hψ)

end RingSystem

end Stacks.LimitHomDescent.Affine

end
