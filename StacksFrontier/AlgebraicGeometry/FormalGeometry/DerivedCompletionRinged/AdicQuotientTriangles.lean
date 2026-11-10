module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientFactorization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealTensorVanishing
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Derived tensor products with short exact sequences through the structure sheaf

Let `(𝒞, 𝒪)` be a ringed site and `K ∈ D(𝒪)`. A short exact sequence `0 → P → 𝒪 → Q → 0` of
sheaves of `𝒪`-modules, tensored with `K`, is a distinguished triangle
`K ⊗^𝐋 P ⟶ K ⟶ K ⊗^𝐋 Q ⟶ (K ⊗^𝐋 P)[1]`, the middle term identified with `K` by the unit law.
This file records these triangles, the naturality of their connecting maps in the sequence, and
two facts about the reductions `K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ` at a single complex `K = M[0]` killed by `ℐ`:
the reduction is a split monomorphism, and it dies under a map `𝒪/ℐⁿ ⟶ 𝒪` that is
multiplication by a section killing `M`. These are the inputs of
`AlgebraicGeometry.RingedSite.not_isIso_derivedCompletionComparison_of_periodicPresentation`.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorShortExactδ`: the connecting map.

## Main results

* `AlgebraicGeometry.RingedSite.tensorShortExact_distinguished`: the triangle is distinguished.
* `AlgebraicGeometry.RingedSite.tensorShortExactδ_naturality`: the connecting maps are natural.
* `AlgebraicGeometry.RingedSite.isSplitMono_adicQuotientReduction_single`: the reduction of
  `M[0]` modulo `ℐⁿ` is a split monomorphism when the sections of `ℐⁿ` kill `M`.
* `AlgebraicGeometry.RingedSite.adicQuotientReduction_comp_eq_zero`: the reduction dies under a
  map `𝒪/ℐⁿ ⟶ 𝒪` which composed with the projection is multiplication by a section killing `M`.

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u})
  (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

section Triangles

variable {P Q : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  {f : P ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  {g : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ Q}
  {w : f ≫ g = 0} (hS : (ShortComplex.mk f g w).ShortExact)

/-- The connecting map of the derived tensor product of `K` with a short exact sequence. -/
def tensorShortExactδ :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        ((DerivedCategory.singleFunctor _ 0).obj Q) ⟶
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        ((DerivedCategory.singleFunctor _ 0).obj P))⟦(1 : ℤ)⟧ :=
  (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).mapTriangle.obj
    hS.singleTriangle).mor₃

/-- **The derived tensor product of `K` with `0 → P → 𝒪 → Q → 0` is distinguished**, its middle
term identified with `K` by the unit law. -/
theorem tensorShortExact_distinguished :
    Triangle.mk
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
            ((DerivedCategory.singleFunctor _ 0).map f) ≫
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).unitIso K).hom)
        (((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).unitIso K).inv ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
            ((DerivedCategory.singleFunctor _ 0).map g))
        (tensorShortExactδ X K hS) ∈
      distTriang
        (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) := by
  refine isomorphic_distinguished _
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map_distinguished _
      hS.singleTriangle_distinguished) _
    (Triangle.isoMk _ _ (Iso.refl _)
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).unitIso K).symm (Iso.refl _)
      ?_ ?_ ?_)
  · exact (Category.assoc _ _ _).trans ((congrArg _ (Iso.hom_inv_id _)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  · exact Category.comp_id _
  · exact ((congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)).trans
      (Category.id_comp _).symm

variable {P' Q' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  {f' : P' ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  {g' : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ Q'}
  {w' : f' ≫ g' = 0} (hS' : (ShortComplex.mk f' g' w').ShortExact)

/-- **The connecting maps are natural in the short exact sequence.** -/
theorem tensorShortExactδ_naturality (φ : ShortComplex.mk f g w ⟶ ShortComplex.mk f' g' w') :
    tensorShortExactδ X K hS ≫
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
          ((DerivedCategory.singleFunctor _ 0).map φ.τ₁))⟦(1 : ℤ)⟧' =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
          ((DerivedCategory.singleFunctor _ 0).map φ.τ₃) ≫ tensorShortExactδ X K hS' :=
  (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).mapTriangle.map
    (ShortComplex.ShortExact.singleTriangle.map hS hS' φ)).comm₃

end Triangles

section Reduction

/-- If a natural transformation is monic at the target of `f`, then `f` is killed by its source
functor as soon as it is killed by its target functor. -/
private theorem map_eq_zero_of_app_mono {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] {F G : C ⥤ D} (α : F ⟶ G) {A B : C} (f : A ⟶ B) [Mono (α.app B)]
    (h : G.map f = 0) : F.map f = 0 := by
  rw [← cancel_mono (α.app B), zero_comp, α.naturality, h, comp_zero]

/-- **The derived tensor product of `M[0]` with a map of modules into `𝒪` vanishes as soon as
the ordinary tensor product does.** The canonical map to the total tensor complex is natural, and
it is invertible at `𝒪[0]`, which is K-flat. -/
theorem tensor_single_map_single_eq_zero
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {P : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : P ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hf : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).map f = 0) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)).map
      ((DerivedCategory.singleFunctor _ 0).map f) = 0 := by
  let T := Stacks.SheafOfModules.canonicalDerivedTensorProduct X
  let sM := (HomologicalComplex.single
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ComplexShape.up ℤ) 0).obj M
  let sU := (HomologicalComplex.single
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  let sf := (HomologicalComplex.single
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ComplexShape.up ℤ) 0).map f
  have hnat := T.toTensor_naturality (𝟙 sM) sf
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at hnat
  have hiso : IsIso (T.toTensor sM sU) := by
    rw [T.toTensor_eq_comparisonRight _ _ (Stacks.SheafOfModules.isKFlat_single_unit X.O)]
    infer_instance
  have hzero : HomologicalComplex.mapBifunctorMap (𝟙 sM) sf
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) = 0 := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    rw [HomologicalComplex.zero_f]
    refine HomologicalComplex.mapBifunctor.hom_ext fun i j hij => ?_
    rw [HomologicalComplex.ι_mapBifunctorMap, comp_zero]
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · subst hi hj
        have e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
        have h0 : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (sM.X 0)).map f = 0 :=
          map_eq_zero_of_app_mono ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map e.hom) f hf
        rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
          Category.id_comp, HomologicalComplex.single_map_f_self, Functor.map_comp,
          Functor.map_comp, h0, zero_comp, comp_zero, zero_comp]
      · exact (HomologicalComplex.isZero_obj_obj_single_obj_X
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) M P i j (Or.inr hj)).eq_of_src _ _
    · exact (HomologicalComplex.isZero_obj_obj_single_obj_X
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) M P i j (Or.inl hi)).eq_of_src _ _
  rw [← cancel_mono (T.toTensor sM sU), zero_comp]
  refine hnat.trans ?_
  exact (congrArg (fun z => T.toTensor sM _ ≫ z)
    ((congrArg (fun z => DerivedCategory.Q.map z) hzero).trans
      (CategoryTheory.Functor.map_zero DerivedCategory.Q _ _))).trans comp_zero

variable (I : SheafOfModules.Submodule
  (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **The reduction of `M[0]` modulo `ℐⁿ` is a split monomorphism** when the sections of `ℐⁿ`
kill those of `M`: tensored with `M`, the inclusion `ℐⁿ ⟶ 𝒪` vanishes, so the triangle of
`0 → ℐⁿ → 𝒪 → 𝒪/ℐⁿ → 0` splits. -/
theorem isSplitMono_adicQuotientReduction_single
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℕ)
    (hM : ∀ (U : X.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U),
      a ∈ (Stacks.Sites.idealPow I n).obj U → ∀ g : M.val.obj U, a • g = 0) :
    IsSplitMono (adicQuotientReduction X I ((DerivedCategory.singleFunctor _ 0).obj M) n) := by
  have hord : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).map
      (Stacks.Sites.idealPow I n).ι = 0 := by
    refine map_eq_zero_of_app_mono
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app M)
      (Stacks.Sites.idealPow I n).ι ?_
    exact Stacks.Sites.sheafTensor_map_idealι_app_eq_zero _ M hM
  have hS : (ShortComplex.mk (Stacks.Sites.idealPow I n).ι
      (Stacks.Sites.adicQuotientModuleπ (X := X) I n)
      (Stacks.Sites.ι_comp_adicQuotientModuleπ (X := X) I n)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _) inferInstance
      (Stacks.Sites.epi_adicQuotientModuleπ (X := X) I n)
  have hmor : (Triangle.mk
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)).map
          ((DerivedCategory.singleFunctor _ 0).map (Stacks.Sites.idealPow I n).ι) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).unitIso _).hom)
      (adicQuotientReduction X I ((DerivedCategory.singleFunctor _ 0).obj M) n)
      (tensorShortExactδ X _ hS)).mor₁ ≫ 𝟙 _ = 0 := by
    change (_ ≫ _) ≫ 𝟙 _ = 0
    rw [tensor_single_map_single_eq_zero X M _ hord, zero_comp, zero_comp]
  obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _
    (tensorShortExact_distinguished X ((DerivedCategory.singleFunctor _ 0).obj M) hS) (𝟙 _) hmor
  exact IsSplitMono.mk' ⟨r, hr.symm⟩

attribute [local instance] linearCatCenterRingSheaf

/-- **The reduction of `M[0]` dies under multiplication by a section killing `M`.** If
`φ : 𝒪/ℐⁿ ⟶ 𝒪` composed with the projection is multiplication by a family `a` of local
sections, and `a` kills `M`, then `M[0] ⟶ M[0] ⊗^𝐋 𝒪/ℐⁿ ⟶ M[0] ⊗^𝐋 𝒪 ≅ M[0]` vanishes: the
composite is multiplication by `a` on `M[0]`. -/
theorem adicQuotientReduction_comp_eq_zero
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℕ)
    (φ : Stacks.Sites.adicQuotientModule (X := X) I n ⟶
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj ⋙ forget RingCat.{u}).sections)
    (hφ : Stacks.Sites.adicQuotientModuleπ (X := X) I n ≫ φ =
      (Stacks.SheafOfModules.globalSectionToEnd
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a).asHom.app
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (ha : (Stacks.SheafOfModules.globalSectionToEnd
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a).asHom.app M = 0) :
    adicQuotientReduction X I ((DerivedCategory.singleFunctor _ 0).obj M) n ≫
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            ((DerivedCategory.singleFunctor _ 0).obj M)).map
            ((DerivedCategory.singleFunctor _ 0).map φ) ≫
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).unitIso _).hom) = 0 := by
  let c := Stacks.SheafOfModules.globalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  let F := (Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M)
  let U := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  have hc : ∀ N, (DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map (c.asHom.app N) =
      c • 𝟙 ((DerivedCategory.singleFunctor _ 0).obj N) := fun N => by
    have hmapS := CategoryTheory.Functor.map_smul
      (F := DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0) c
      (𝟙 N)
    rw [CategoryTheory.Functor.map_id] at hmapS
    rw [← hmapS]
    exact congrArg _ (Category.comp_id _).symm
  have hsingle : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
      (c.asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) =
        c • 𝟙 U :=
    hc _
  have hlin : F.map (c • 𝟙 U) = c • 𝟙 (F.obj U) :=
    Stacks.SheafOfModules.Tensor.derivedTensor_map_globalSectionToEnd X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) a _ U
  have hM : c • 𝟙 ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj M) =
      0 := by
    rw [← hc M, ha, Functor.map_zero]
  rwa [adicQuotientReduction, Category.assoc, ← Category.assoc (F.map _), ← F.map_comp,
    ← Functor.map_comp, hφ, hsingle, hlin, Linear.smul_comp, Category.id_comp,
    Linear.comp_smul, Iso.inv_hom_id]

end Reduction

end AlgebraicGeometry.RingedSite
