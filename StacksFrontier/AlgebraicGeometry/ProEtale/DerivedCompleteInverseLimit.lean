module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteCohomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# Inverse limits of derived-complete sheaves

On a site every object of which has a covering by weakly contractible objects, the inverse
limit of a countable inverse system of sheaves of modules that are derived complete along a
sheaf of ideals is itself derived complete.

The system is regarded in the derived category, where it has a derived limit `L`; derived
completeness of `L` is tested on derived sections over a weakly contractible object, and there
the derived limit is preserved, because evaluation is exact and preserves countable products.
Derived completeness passes to a derived limit by the Milnor triangle. Finally `L` is identified
with the inverse limit of the system: the derived limit's cohomology sequence has vanishing
outer terms, since each term of the system sits in degree zero.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_limit`: completeness of the inverse limit.

## Implementation notes

The sheaves are regarded as objects of the derived category in degree zero. The result is
stated for an arbitrary ringed site and sheaf of ideals: the Noetherian hypothesis on a
constant coefficient ring does not enter the inverse-limit argument.

Countable products of sheaves of modules are exact on such a site, which is Stacks 0947(4);
that is what gives the derived category its countable products, and it replaces an appeal to
the axiom AB4*.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
  AlgebraicGeometry AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

universe u v t w

namespace AlgebraicGeometry.RingedSite

private lemma isDerivedLimit_map_of_preservesProduct
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated]
    (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    [PreservesLimit (Discrete.functor (fun n : ℕ => F.obj ⟨n⟩)) G]
    [HasProduct fun n : ℕ => (F ⋙ G).obj ⟨n⟩]
    (L : C) (hL : IsDerivedLimit F L) : IsDerivedLimit (F ⋙ G) (G.obj L) := by
  let : HasProduct (fun n : ℕ => G.obj (F.obj ⟨n⟩)) :=
    (inferInstance : HasProduct fun n : ℕ => (F ⋙ G).obj ⟨n⟩)
  obtain ⟨p, δ, hT⟩ := hL
  let e := asIso (piComparison G (fun n : ℕ => F.obj ⟨n⟩))
  let d : (∏ᶜ fun n : ℕ => F.obj ⟨n⟩) ⟶ ∏ᶜ fun n : ℕ => F.obj ⟨n⟩ :=
    Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let d' : (∏ᶜ fun n : ℕ => G.obj (F.obj ⟨n⟩)) ⟶ ∏ᶜ fun n : ℕ => G.obj (F.obj ⟨n⟩) :=
    Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => G.obj (F.obj ⟨n⟩)) n -
      Pi.π (fun n : ℕ => G.obj (F.obj ⟨n⟩)) (n + 1) ≫
        G.map (F.map (homOfLE (Nat.le_succ n)).op)
  have hmap : G.map d ≫ e.hom = e.hom ≫ d' := by
    refine Pi.hom_ext _ _ fun n => ?_
    dsimp [e, d, d']
    simp only [Category.assoc, piComparison_comp_π, Pi.lift_comp_π, Preadditive.comp_sub]
    rw [← G.map_comp, Pi.lift_comp_π, G.map_sub, G.map_comp, ← Category.assoc,
      piComparison_comp_π]
  refine ⟨G.map p ≫ e.hom, e.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app L, ?_⟩
  apply isomorphic_distinguished _ (G.map_distinguished _ hT)
  refine Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
  · show (G.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ G.map p
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · show d' ≫ e.inv = e.inv ≫ G.map d
    rw [← cancel_epi e.hom, e.hom_inv_id_assoc, ← Category.assoc, ← hmap,
      Category.assoc, e.hom_inv_id, Category.comp_id]
  · dsimp [Functor.mapTriangle]
    rw [(shiftFunctor D (1 : ℤ)).map_id]
    simp only [Category.comp_id]

private theorem isDerivedCompleteAt_of_distTriang
    {A : Type*} [CommSemiring A] {C : Type*} [Category C] [Preadditive C]
    [Linear A C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasProductsOfShape ℕ C] [(shiftFunctor C (1 : ℤ)).Linear A]
    {T : Triangle C} (hT : T ∈ distTriang C) {f : A}
    (h₂ : IsDerivedCompleteAt T.obj₂ f) (h₃ : IsDerivedCompleteAt T.obj₃ f) :
    IsDerivedCompleteAt T.obj₁ f := by
  rw [isDerivedCompleteAt_iff_isIso]
  have hPTdist := productTriangle_distinguished (J := ℕ) (fun _ : ℕ => T) (fun _ => hT)
  let φ : productTriangle (fun _ : ℕ => T) ⟶ productTriangle (fun _ : ℕ => T) :=
    Triangle.homMk (productTriangle (fun _ : ℕ => T)) (productTriangle (fun _ : ℕ => T))
      (oneSubSmulShift T.obj₁ f) (oneSubSmulShift T.obj₂ f) (oneSubSmulShift T.obj₃ f)
      (by rw [productTriangle_mor₁]; exact (oneSubSmulShift_naturality f _).symm)
      (by rw [productTriangle_mor₂]; exact (oneSubSmulShift_naturality f _).symm)
      (by
        rw [productTriangle_mor₃]
        show (Limits.Pi.map (fun _ : ℕ => T.mor₃) ≫
            inv (piComparison (shiftFunctor C (1 : ℤ)) (fun _ : ℕ => T.obj₁))) ≫
              (shiftFunctor C (1 : ℤ)).map (oneSubSmulShift T.obj₁ f)
          = oneSubSmulShift T.obj₃ f ≫
            (Limits.Pi.map (fun _ : ℕ => T.mor₃) ≫
              inv (piComparison (shiftFunctor C (1 : ℤ)) (fun _ : ℕ => T.obj₁)))
        set pc := piComparison (shiftFunctor C (1 : ℤ)) (fun _ : ℕ => T.obj₁)
        have hshift' :
            oneSubSmulShift ((shiftFunctor C (1 : ℤ)).obj T.obj₁) f ≫ inv pc
                = inv pc ≫ (shiftFunctor C (1 : ℤ)).map (oneSubSmulShift T.obj₁ f) := by
          rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
          exact piComparison_comp_oneSubSmulShift T.obj₁ f
        rw [Category.assoc, ← hshift', ← Category.assoc,
          ← oneSubSmulShift_naturality f T.mor₃, Category.assoc])
  exact isIso₁_of_isIso₂₃ φ hPTdist hPTdist
    (isDerivedCompleteAt_iff_isIso.mp h₂) (isDerivedCompleteAt_iff_isIso.mp h₃)

private theorem isDerivedCompleteAt_of_isDerivedLimit
    {A : Type*} [CommSemiring A] {C : Type*} [Category C] [Preadditive C]
    [Linear A C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasProductsOfShape ℕ C] [(shiftFunctor C (1 : ℤ)).Linear A]
    (F : ℕᵒᵖ ⥤ C) (L : C) (hL : IsDerivedLimit F L) {f : A}
    (hF : ∀ n : ℕ, IsDerivedCompleteAt (F.obj ⟨n⟩) f) :
    IsDerivedCompleteAt L f := by
  obtain ⟨_, _, hT⟩ := hL
  exact isDerivedCompleteAt_of_distTriang hT (isDerivedCompleteAt_pi hF)
    (isDerivedCompleteAt_pi hF)

private lemma homology_single_isZero
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (M : A) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor A n).obj
      ((DerivedCategory.singleFunctor A 0).obj M)) :=
  (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M n hn).of_iso
    ((DerivedCategory.homologyFunctorFactors A n).app ((CochainComplex.singleFunctor A 0).obj M))

/-- The degree-zero cohomology of a derived limit of a countable system placed in degree zero
is the inverse limit of the system. -/
private theorem nonempty_homologyZero_iso_limit_of_isDerivedLimit
    {A : Type*} [Category A] [Abelian A] [HasProductsOfShape ℕ A]
    [HasExactLimitsOfShape (Discrete ℕ) A] [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory A]
    [HasProductsOfShape ℕ (DerivedCategory A)] (F : ℕᵒᵖ ⥤ A) (L : DerivedCategory A)
    (hL : IsDerivedLimit (F ⋙ DerivedCategory.singleFunctor A 0) L) :
    Nonempty ((DerivedCategory.homologyFunctor A 0).obj L ≅ limit F) := by
  let K : ℕᵒᵖ ⥤ DerivedCategory A := F ⋙ DerivedCategory.singleFunctor A 0
  obtain ⟨_, _, _, hs⟩ := DerivedCategory.isDerivedLimit_homology_shortExact K L hL
  have hs0 := hs 0
  dsimp only at hs0
  obtain ⟨_, i, q, _, _, _, _, hshort⟩ := hs0
  let Hprev := DerivedCategory.homologyFunctor A (-1)
  have hP : IsZero (∏ᶜ fun n : ℕ => Hprev.obj (K.obj ⟨n⟩)) :=
    (limit.isLimit _).isZero_pt (Functor.isZero _ fun n =>
      homology_single_isZero (F.obj (Opposite.op n.as)) (-1) (by norm_num))
  let δ : (∏ᶜ fun n : ℕ => Hprev.obj (K.obj ⟨n⟩)) ⟶
      ∏ᶜ fun n : ℕ => Hprev.obj (K.obj ⟨n⟩) :=
    Pi.lift fun n : ℕ =>
      Pi.π (fun n : ℕ => Hprev.obj (K.obj ⟨n⟩)) n -
        Pi.π (fun n : ℕ => Hprev.obj (K.obj ⟨n⟩)) (n + 1) ≫
          Hprev.map (K.map (homOfLE (Nat.le_succ n)).op)
  have : IsIso q := hshort.isIso_g_iff.2 (IsZero.of_epi (cokernel.π δ) hP)
  let H0 := DerivedCategory.homologyFunctor A 0
  let hSysIso : (K ⋙ H0) ≅ F :=
    (Functor.associator F (DerivedCategory.singleFunctor A 0) H0) ≪≫
      Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0) ≪≫
      Functor.rightUnitor F
  exact ⟨asIso q ≪≫ HasLimit.isoOfNatIso hSysIso⟩

open scoped IsMulCommutative in
/-- **The inverse limit of a countable system of derived-complete sheaves of modules is derived
complete**, on a ringed site equipped with a covering collection of objects which test
surjectivity of sheaves of sets valued in the module universe, on the site and on each of its
slices.

The weakly contractible objects enter only through that collection, so the statement reaches a
site whose objects outnumber its morphisms — the small pro-étale site of a scheme among them —
where weak contractibility cannot be tested at the morphism universe at all. -/
@[stacks 099Q "inverse_limits, at a sliced situation of testing objects"]
public theorem isDerivedComplete_limit_of_slicedObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : Stacks.WeaklyContractible.SlicedObjectsSituation.{w, v, u, max u v}
      X.C X.J)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : ℕᵒᵖ ⥤ SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : ∀ n : ℕ, AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (F.obj ⟨n⟩))) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (limit F)) := by
  classical
  let A := SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let : Abelian A := inferInstance
  let : HasExactLimitsOfShape (Discrete ℕ) A :=
    Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat.{max u v}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) hX.B hX.hasEnoughObjects
      fun _ hU => hX.isWeaklyContractible hU
  let : HasProductsOfShape ℕ (DerivedCategory A) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let K : ℕᵒᵖ ⥤ DerivedCategory A :=
    F ⋙ DerivedCategory.singleFunctor A 0
  obtain ⟨L, hL⟩ := exists_isDerivedLimit K
  have hLcomplete : AlgebraicGeometry.RingedSite.IsDerivedComplete X I L := by
    apply (isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation X hX I L).mpr
    intro U hU
    let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (Opposite.op U)
    let : IsMulCommutative R := by
      show IsMulCommutative (X.O.obj.obj (Opposite.op U))
      infer_instance
    let : CommRing R := inferInstance
    let G := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (Opposite.op U)
    let : G.Additive := ⟨fun {_ _} _ _ => rfl⟩
    let : PreservesFiniteLimits G := inferInstance
    let : G.PreservesZeroMorphisms := inferInstance
    let : G.PreservesHomology := Functor.preservesHomology_of_map_exact G fun T hT =>
      evaluation_map_exact_of_weaklyContractibleObjectsSituation X
        hX.toWeaklyContractibleObjectsSituation U hU T hT
    let : PreservesFiniteColimits G :=
      Functor.preservesFiniteColimits_of_preservesHomology G
    let : HasProductsOfShape ℕ (ModuleCat.{max u v} R) := inferInstance
    let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} R) :=
      StacksDraft.Perfect.moduleCat_hasExactLimitsOfShape_discrete_nat
    let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let D := G.mapDerivedCategory
    let : PreservesLimitsOfShape (Discrete ℕ) G := inferInstance
    let : PreservesLimitsOfShape (Discrete ℕ) D :=
      Functor.preservesProducts_mapDerivedCategory ℕ G
    let : PreservesLimit (Discrete.functor (fun n : ℕ => K.obj ⟨n⟩)) D := inferInstance
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun f hf => ?_⟩
    refine isDerivedCompleteAt_of_isDerivedLimit (K ⋙ D) (D.obj L)
      (isDerivedLimit_map_of_preservesProduct D K L hL) (f := f) fun n => ?_
    obtain ⟨_, _, _, _, hn⟩ :=
      (AlgebraicGeometry.RingedSite.isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation
        X hX I ((DerivedCategory.singleFunctor A 0).obj (F.obj ⟨n⟩))).mp (hF n) U hU
    exact hn f hf
  obtain ⟨e⟩ := nonempty_homologyZero_iso_limit_of_isDerivedLimit (A := A) F L hL
  exact (AlgebraicGeometry.RingedSite.isDerivedComplete_iff_of_iso X I
    ((DerivedCategory.singleFunctor A 0).mapIso e)).mp
      ((AlgebraicGeometry.RingedSite.isDerivedComplete_iff_homology_of_slicedObjectsSituation
        X I hX L).mp hLcomplete 0)

/-- The inverse limit of a countable system of derived-complete sheaves is derived complete. -/
@[stacks 099Q "inverse_limits"]
public theorem isDerivedComplete_limit
    (X : RingedSite.{u, v, max u v})
    [Small.{v} X.C] [HasSheafify X.J (Type v)]
    (hX : X.J.HasEnoughWeaklyContractibleObjects)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (F : ℕᵒᵖ ⥤ SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hF : ∀ n : ℕ, AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (F.obj ⟨n⟩))) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (limit F)) :=
  isDerivedComplete_limit_of_slicedObjectsSituation X
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of
      ⟨fun U => X.J.IsWeaklyContractible U, fun {_} hU => hU, hX⟩
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I F hF

end AlgebraicGeometry.RingedSite

end
