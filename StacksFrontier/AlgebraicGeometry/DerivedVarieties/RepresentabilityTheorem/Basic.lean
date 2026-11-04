module

public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Opposite.OpOp
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.Finiteness.Small
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.RepresentabilityTheorem.Filtered

/-!
# A representability theorem on the compact objects

Let `D` be a compactly generated `k`-linear triangulated category with arbitrary direct sums.
Every `k`-linear cohomological functor from the opposite of the full subcategory of compact
objects of `D` to `k`-vector spaces whose values are finite-dimensional is the restriction of a
representable functor on `D`. This is Van den Bergh's representability theorem, and the proof
goes by extending the functor along the inclusion of the compact objects by a pointwise left Kan
extension, checking that the extension is still cohomological and takes arbitrary direct sums to
products, and then applying Brown representability.

## Main results

* `CategoryTheory.compactObjectsIsTriangulated`: the compact objects of a triangulated category
  with arbitrary direct sums form a triangulated subcategory.
* `CategoryTheory.exists_iso_comp_linearYoneda_of_finiteDimensional` is the representability
  theorem.
* `CategoryTheory.exists_iso_comp_linearYoneda_of_isCompactObject_obj`: the same for a functor on
  any triangulated category embedded fully faithfully, exactly and linearly among the compact
  objects; the embedded objects need not generate.

## Implementation notes

The full subcategory of compact objects is
`CategoryTheory.ObjectProperty.FullSubcategory (CategoryTheory.IsCompactObject (C := D))`; its
triangulated structure is registered as an instance so that
`CategoryTheory.Functor.IsHomological` applies to its opposite directly. The conclusion retains
the natural isomorphism of `k`-module-valued functors rather than giving only objectwise
equivalences. Values in the dual are taken in a small model of the dual space, so that the
colimits used by the Kan extension stay in the morphism universe.

## References

* [Stacks Project, Tag 0FYG](https://stacks.math.columbia.edu/tag/0FYG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated.Opposite
  CategoryTheory.Pretriangulated ZeroObject
open Opposite

namespace CategoryTheory

universe u v w

private noncomputable def moduleDual (k : Type w) [Field k] :
    (ModuleCat.{v} k)ᵒᵖ ⥤ ModuleCat.{max v w} k where
  obj M := ModuleCat.of k (Module.Dual k M.unop)
  map f := ModuleCat.ofHom f.unop.hom.dualMap
  map_id M := by
    apply ModuleCat.hom_ext
    ext x y
    rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    ext x y
    rfl

/-- The dual of a module over `k` is `v`-small when `k` is. -/
private instance small_moduleDual (k : Type w) [Field k] [Small.{v} k]
    (M : ModuleCat.{v} k) : Small.{v} (Module.Dual k M) :=
  small_of_injective (f := fun f : Module.Dual k M => (f : M → k)) DFunLike.coe_injective

private noncomputable abbrev moduleDualSmallObj (k : Type w) [Field k] [Small.{v} k]
    (M : ModuleCat.{v} k) : ModuleCat.{v} k :=
  ModuleCat.of k (Shrink.{v} (Module.Dual k M))

private noncomputable def moduleDualSmallMap (k : Type w) [Field k] [Small.{v} k]
    {M N : ModuleCat.{v} k}
    (f : M ⟶ N) : moduleDualSmallObj k N ⟶ moduleDualSmallObj k M :=
  ModuleCat.ofHom ((Shrink.linearEquiv.{v} k (Module.Dual k M)).symm.toLinearMap.comp <|
    f.hom.dualMap.comp (Shrink.linearEquiv.{v} k (Module.Dual k N)).toLinearMap)

private noncomputable def moduleDualSmall (k : Type w) [Field k] [Small.{v} k] :
    (ModuleCat.{v} k)ᵒᵖ ⥤ ModuleCat.{v} k where
  obj M := moduleDualSmallObj k M.unop
  map f := moduleDualSmallMap k f.unop
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (Shrink.linearEquiv.{v} k (Module.Dual k (↑(unop M)))).injective
    ext y
    simp [moduleDualSmallMap, ModuleCat.hom_id]
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (Shrink.linearEquiv.{v} k (Module.Dual k (↑(unop Z)))).injective
    ext y
    simp [moduleDualSmallMap, ModuleCat.hom_comp]

private noncomputable def doubleDualSmallLinearEquiv (k : Type w) [Field k]
    [Small.{v} k] (M : ModuleCat.{v} k) [FiniteDimensional k M] :
    M ≃ₗ[k] moduleDualSmallObj k (moduleDualSmallObj k M) := by
  letI : Small.{v} (Module.Dual k (moduleDualSmallObj k M)) :=
    small_moduleDual k (moduleDualSmallObj k M)
  exact (Module.evalEquiv k M).trans
    ((Shrink.linearEquiv k (Module.Dual k M)).dualMap.trans
      (Shrink.linearEquiv k (Module.Dual k (moduleDualSmallObj k M))).symm)

private lemma doubleDualSmallLinearEquiv_natural (k : Type w) [Field k]
    [Small.{v} k] {M N : ModuleCat.{v} k} [FiniteDimensional k M]
    [FiniteDimensional k N] (f : M ⟶ N) :
    (moduleDualSmallMap k (moduleDualSmallMap k f)).hom.comp
        (doubleDualSmallLinearEquiv k M).toLinearMap =
      (doubleDualSmallLinearEquiv k N).toLinearMap.comp f.hom := by
  ext x
  let : Small.{v} (Module.Dual k (moduleDualSmallObj k N)) :=
    small_moduleDual k (moduleDualSmallObj k N)
  apply (Shrink.linearEquiv.{v} k
    (Module.Dual k (moduleDualSmallObj k N))).injective
  ext z
  simp [doubleDualSmallLinearEquiv, moduleDualSmallMap, moduleDualSmallObj,
    LinearMap.comp_apply, LinearMap.dualMap_apply]

private noncomputable def moduleDualSmall_forgetIsoApp (k : Type w) [Field k]
    [Small.{v} k] (M : (ModuleCat.{v} k)ᵒᵖ) :
    (moduleDualSmall k ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat).obj M ≅
      (preadditiveYoneda.obj (ModuleCat.of k (Shrink.{v} k))).obj M := by
  classical
  let e₂ : (Module.Dual k M.unop) ≃+ (M.unop →ₗ[k] Shrink.{v} k) :=
    { toFun := fun f => (Shrink.linearEquiv.{v} k k).symm.toLinearMap.comp f
      invFun := fun f => (Shrink.linearEquiv.{v} k k).toLinearMap.comp f
      left_inv f := by ext; simp
      right_inv f := by ext; simp
      map_add' f g := by ext; simp }
  exact ((Shrink.linearEquiv.{v} k (Module.Dual k M.unop)).toAddEquiv.trans
    (e₂.trans (ModuleCat.homAddEquiv (M := M.unop)
      (N := ModuleCat.of k (Shrink.{v} k))).symm)).toAddCommGrpIso

private lemma moduleDualSmall_forgetIsoApp_apply (k : Type w) [Field k]
    [Small.{v} k] (M : (ModuleCat.{v} k)ᵒᵖ)
    [Small.{v} (Module.Dual k M.unop)]
    (x : Shrink.{v} (Module.Dual k M.unop)) (y : M.unop) :
    ModuleCat.Hom.hom (ConcreteCategory.hom (moduleDualSmall_forgetIsoApp k M).hom x) y =
      ((Shrink.linearEquiv.{v} k k).symm.toLinearMap.comp
        ((Shrink.linearEquiv.{v} k (Module.Dual k M.unop)).toLinearMap x)) y := by
  change (Shrink.linearEquiv.{v} k k).symm
      (((Shrink.linearEquiv.{v} k (Module.Dual k M.unop)).toLinearMap x) y) = _
  rfl

private noncomputable def moduleDualSmall_forgetIso (k : Type w) [Field k] [Small.{v} k] :
    moduleDualSmall k ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat ≅
      preadditiveYoneda.obj (ModuleCat.of k (Shrink.{v} k)) := by
  refine NatIso.ofComponents (moduleDualSmall_forgetIsoApp k) ?_
  intro M N f
  ext x
  apply ModuleCat.hom_ext
  ext y
  simp only [AddCommGrpCat.comp_apply]
  congr 1
  rw [moduleDualSmall_forgetIsoApp_apply k N
    ((ConcreteCategory.hom ((moduleDualSmall k ⋙
      forget₂ (ModuleCat.{v} k) AddCommGrpCat).map f)) x) y]
  change _ = ModuleCat.Hom.hom (ConcreteCategory.hom (moduleDualSmall_forgetIsoApp k M).hom x)
    (f.unop.hom y)
  rw [moduleDualSmall_forgetIsoApp_apply k M x (f.unop.hom y)]
  change (Shrink.linearEquiv k k).symm
      (((Shrink.linearEquiv k (Module.Dual k N.unop))
        ((Shrink.linearEquiv k (Module.Dual k N.unop)).symm
          (f.unop.hom.dualMap ((Shrink.linearEquiv k (Module.Dual k M.unop)) x))) y)) =
    (Shrink.linearEquiv k k).symm
      (((Shrink.linearEquiv k (Module.Dual k M.unop)) x) (f.unop.hom y))
  simp [LinearMap.dualMap_apply]

private noncomputable instance moduleDualSmall_preservesZeroMorphisms (k : Type w) [Field k]
    [Small.{v} k] : (moduleDualSmall k).PreservesZeroMorphisms where
  map_zero M N := by
    apply ModuleCat.hom_ext
    change (moduleDualSmallMap k (0 : N.unop ⟶ M.unop)).hom = 0
    apply LinearMap.ext
    intro x
    dsimp [moduleDualSmallMap]
    apply (Shrink.linearEquiv.{v} k (Module.Dual k N.unop)).injective
    ext y
    simp

private lemma exact_dualMap {k : Type w} [Field k] {A B C : Type v}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module k A] [Module k B] [Module k C]
    {f : A →ₗ[k] B} {g : B →ₗ[k] C} (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff] at h ⊢
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, h]

private lemma exact_moduleDualSmallMap (k : Type w) [Field k] [Small.{v} k]
    {A B C : ModuleCat.{v} k} (f : A ⟶ B) (g : B ⟶ C)
    (h : Function.Exact f.hom g.hom) :
    Function.Exact (moduleDualSmallMap k g).hom (moduleDualSmallMap k f).hom := by
  let eA := Shrink.linearEquiv.{v} k (Module.Dual k A)
  let eB := Shrink.linearEquiv.{v} k (Module.Dual k B)
  let eC := Shrink.linearEquiv.{v} k (Module.Dual k C)
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := eC.symm) (e₂ := eB.symm) (e₃ := eA.symm) ?_ ?_ (exact_dualMap h)
  · ext x y
    simp [moduleDualSmallMap, eB, eC, LinearMap.comp_apply]
  · ext x y
    simp [moduleDualSmallMap, eA, eB, LinearMap.comp_apply]

private lemma exact_op_map_moduleDualSmall (k : Type w) [Field k] [Small.{v} k]
    {S : ShortComplex (ModuleCat.{v} k)} (hS : S.Exact) :
    (S.op.map (moduleDualSmall k)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS
  exact exact_moduleDualSmallMap k S.f S.g hS

private noncomputable def moduleDualComp {C : Type u} [Category.{v} C]
    (k : Type w) [Field k] [Small.{v} k] (F : Cᵒᵖ ⥤ ModuleCat.{v} k) :
    C ⥤ ModuleCat.{v} k :=
  (opOpEquivalence C).inverse ⋙ F.op ⋙ moduleDualSmall k

private lemma homological_op_dual {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (k : Type w) [Field k] [Small.{v} k]
    (F : Cᵒᵖ ⥤ ModuleCat.{v} k) [F.IsHomological] :
    (moduleDualComp k F).IsHomological := by
  refine { map_zero := ?_, exact := ?_ }
  · intro X Y
    simp [moduleDualComp]
    rfl
  · intro T hT
    let S := Pretriangulated.shortComplexOfDistTriangle T hT
    change ((S.op.map F).op.map (moduleDualSmall k)).Exact
    exact exact_op_map_moduleDualSmall k (F.map_distinguished_op_exact T hT)

private noncomputable def moduleDualComp_forgetIso {C : Type u} [Category.{v} C]
    {k : Type w} [Field k] [Small.{v} k] (F : Cᵒᵖ ⥤ ModuleCat.{v} k) :
    moduleDualComp k F ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat ≅
      (opOpEquivalence C).inverse ⋙ F.op ⋙
        preadditiveYoneda.obj (ModuleCat.of k (Shrink.{v} k)) := by
  refine NatIso.ofComponents (fun X =>
    (moduleDualSmall_forgetIso k).app ((F.op).obj ((opOpEquivalence C).inverse.obj X))) ?_
  intro X Y f
  simpa [moduleDualComp, Functor.comp_map] using
    (moduleDualSmall_forgetIso k).hom.naturality
      ((F.op).map ((opOpEquivalence C).inverse.map f))

private lemma small_field_of_nontrivial_module (k : Type w) [Field k]
    (M : Type v) [AddCommGroup M] [Module k M] (hM : Nontrivial M) : Small.{v} k := by
  obtain ⟨x, y, hxy⟩ := hM.exists_pair_ne
  exact small_of_injective (smul_left_injective k (sub_ne_zero.mpr hxy))

private lemma compact_zero {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] :
    IsCompactObject.{v} (0 : C) := by
  constructor
  intro I _ E _
  exact ⟨fun a b _ => DFinsupp.ext fun i => (isZero_zero C).eq_of_src _ _,
    fun _ => ⟨0, (isZero_zero C).eq_of_src _ _⟩⟩

/-- A subgroup containing all the legs of a colimit cocone is the whole colimit object. -/
private lemma subgroup_eq_top_of_isColimit {J : Type*} [Category* J]
    {F : J ⥤ AddCommGrpCat.{v}} {c : Cocone F} (hc : IsColimit c)
    (S : AddSubgroup c.pt)
    (hS : ∀ (j : J) (x : F.obj j), ConcreteCategory.hom (c.ι.app j) x ∈ S) :
    S = ⊤ := by
  have h : AddCommGrpCat.ofHom (QuotientAddGroup.mk' S) = 0 := by
    refine hc.hom_ext fun j ↦ ?_
    ext x
    exact (QuotientAddGroup.eq_zero_iff _).2 (hS j x)
  ext a
  simpa [QuotientAddGroup.eq_zero_iff] using ConcreteCategory.congr_hom h a

private lemma exists_sum_comp_sigmaι
    {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{v} D]
    (K : D) [IsCompactObject.{v} K] {J : Type v} (E : J → D) (α : K ⟶ ∐ E) :
    ∃ (S : Finset J) (β : ∀ j, K ⟶ E j), α = ∑ j ∈ S, β j ≫ Sigma.ι E j := by
  classical
  obtain ⟨b, hb⟩ := (IsCompactObject.bijective_toAddMonoid_rightComp_sigmaι (K := K) E).2 α
  refine ⟨b.support, fun j => b j, ?_⟩
  calc
    α = DirectSum.toAddMonoid (fun j => Preadditive.rightComp K (Sigma.ι E j)) b := hb.symm
    _ = ∑ j ∈ b.support, b j ≫ Sigma.ι E j := by
      conv_lhs => rw [← DirectSum.sum_support_of b]
      simp [Preadditive.rightComp]


private lemma isIso_sigmaComparison_for_compact
    {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{v} D]
    (K : D) [IsCompactObject.{v} K] {J : Type v} (E : J → D) :
    IsIso (sigmaComparison (preadditiveCoyoneda.obj (op K)) E) := by
  classical
  have hbij : Function.Bijective
      (DirectSum.toAddMonoid fun i => Preadditive.rightComp K (Limits.Sigma.ι E i)) :=
    IsCompactObject.bijective_toAddMonoid_rightComp_sigmaι E
  let α : (DirectSum J fun i => (K ⟶ E i)) ≃+ (K ⟶ ∐ E) := AddEquiv.ofBijective _ hbij
  have hα : ∀ (i : J) (g : K ⟶ E i), α (DirectSum.of _ i g) = g ≫ Limits.Sigma.ι E i := by
    intro i g
    change (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι E j))
      (DirectSum.of _ i g) = _
    rw [DirectSum.toAddMonoid_of]
    rfl
  let ι₀ : ∀ i : J, (K ⟶ E i) →+
      (((∐ fun i => (preadditiveCoyoneda.obj (op K)).obj (E i)) : AddCommGrpCat.{v}) : Type v) :=
    fun i => (Limits.Sigma.ι (fun i => (preadditiveCoyoneda.obj (op K)).obj (E i)) i).hom
  let β : (DirectSum J fun i => (K ⟶ E i)) →+
      (((∐ fun i => (preadditiveCoyoneda.obj (op K)).obj (E i)) : AddCommGrpCat.{v}) : Type v) :=
    DirectSum.toAddMonoid ι₀
  have hβ : ∀ (i : J) (g : K ⟶ E i), β (DirectSum.of _ i g) = ι₀ i g :=
    fun i g => DirectSum.toAddMonoid_of ι₀ i g
  have hsc : ∀ (i : J) (g : K ⟶ E i),
      (sigmaComparison (preadditiveCoyoneda.obj (op K)) E).hom (ι₀ i g)
        = g ≫ Limits.Sigma.ι E i := by
    intro i g
    change ((Limits.Sigma.ι (fun i => (preadditiveCoyoneda.obj (op K)).obj (E i)) i) ≫
      sigmaComparison (preadditiveCoyoneda.obj (op K)) E).hom g = _
    rw [ι_comp_sigmaComparison]
    rfl
  have key : ∀ x, (sigmaComparison (preadditiveCoyoneda.obj (op K)) E).hom (β x) = α x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero =>
      simp only [map_zero]
      rfl
    | of i g => rw [hβ, hsc, hα]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      rfl
  have hβsurj : Function.Surjective β := by
    intro z
    have hc := colimit.isColimit (Discrete.functor
      (fun i => (preadditiveCoyoneda.obj (op K)).obj (E i)))
    have hS := subgroup_eq_top_of_isColimit hc β.range
      (fun j x => ⟨DirectSum.of _ j.as x, hβ j.as x⟩)
    exact (hS ▸ AddSubgroup.mem_top z : z ∈ β.range)
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b hab => ?_, fun f => ?_⟩
  · obtain ⟨a', rfl⟩ := hβsurj a
    obtain ⟨b', rfl⟩ := hβsurj b
    rw [key, key] at hab
    exact congrArg β (hbij.1 hab)
  · obtain ⟨a', ha'⟩ := hbij.2 f
    exact ⟨β a', (key a').trans ha'⟩

private lemma compact_preserves_discrete_nat
    {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{v} D]
    (K : D) [IsCompactObject.{v} K] :
    PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K)) := by
  have := ObjectProperty.preservesColimitsOfShape_discrete_of_isCompactObject K (ULift.{v} ℕ)
  exact preservesColimitsOfShape_of_equiv
    (Discrete.equivalence (Equiv.ulift : ULift.{v} ℕ ≃ ℕ)) _

private lemma exists_stage_of_filtered_colimit {J : Type*} [Category* J] [IsFiltered J]
    {G : J ⥤ AddCommGrpCat.{v}} {c : Cocone G} (hc : IsColimit c) (a : c.pt) :
    ∃ (j : J) (x : G.obj j), ConcreteCategory.hom (c.ι.app j) x = a := by
  have : Nonempty J := IsFiltered.nonempty
  let S : AddSubgroup c.pt :=
    { carrier := {a | ∃ (j : J) (x : G.obj j), ConcreteCategory.hom (c.ι.app j) x = a}
      zero_mem' := ⟨Classical.arbitrary J, 0, map_zero _⟩
      add_mem' := by
        rintro a b ⟨j, x, rfl⟩ ⟨j', y, rfl⟩
        refine ⟨IsFiltered.max j j', G.map (IsFiltered.leftToMax j j') x +
          G.map (IsFiltered.rightToMax j j') y, ?_⟩
        have h1 := ConcreteCategory.congr_hom (c.w (IsFiltered.leftToMax j j')) x
        have h2 := ConcreteCategory.congr_hom (c.w (IsFiltered.rightToMax j j')) y
        simp only [ConcreteCategory.comp_apply] at h1 h2
        rw [map_add, h1, h2]
      neg_mem' := by
        rintro a ⟨j, x, rfl⟩
        exact ⟨j, -x, map_neg _ _⟩ }
  have hS : S = ⊤ := subgroup_eq_top_of_isColimit hc S (fun j x ↦ ⟨j, x, rfl⟩)
  exact (hS ▸ AddSubgroup.mem_top a : a ∈ S)

/-- A colimit of `k`-modules over a filtered category stays a colimit of types after restricting
to a small final subcategory and forgetting the module structure. -/
private noncomputable def isColimitForgetMapCoconeWhisker
    {J : Type u} [Category.{v} J] [IsFiltered J] [LocallySmall.{v} J]
    [FinallySmall.{v} J] {k : Type w} [Field k]
    {F : J ⥤ ModuleCat.{v} k} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((forget AddCommGrpCat).mapCocone
      ((forget₂ (ModuleCat.{v} k) AddCommGrpCat).mapCocone
        (c.whisker (FinallySmall.fromFilteredFinalModel.{v} J)))) :=
  isColimitOfPreserves _ (isColimitOfPreserves _
    ((Functor.Final.isColimitWhiskerEquiv _ c).symm hc))

private lemma exists_stage_of_filtered_module_colimit
    {J : Type u} [Category.{v} J] [IsFiltered J] [LocallySmall.{v} J]
    [FinallySmall.{v} J] {k : Type w} [Field k] [Small.{v} k]
    {F : J ⥤ ModuleCat.{v} k} {c : Cocone F} (hc : IsColimit c) (z : c.pt) :
    ∃ (j : J) (x : F.obj j), c.ι.app j x = z := by
  obtain ⟨j, x, hx⟩ :=
    Types.jointly_surjective_of_isColimit (isColimitForgetMapCoconeWhisker hc) z
  exact ⟨_, x, hx⟩

private lemma exists_stage_map_zero_of_filtered_module_colimit
    {J : Type u} [Category.{v} J] [IsFiltered J] [LocallySmall.{v} J]
    [FinallySmall.{v} J] {k : Type w} [Field k] [Small.{v} k]
    {F : J ⥤ ModuleCat.{v} k} {c : Cocone F} (hc : IsColimit c)
    {j : J} (x : F.obj j) (hx : c.ι.app j x = 0) :
    ∃ (j' : J) (f : j ⟶ j'), F.map f x = 0 := by
  let e := FinallySmall.fromFilteredFinalModel.{v} J
  let : e.Final := inferInstance
  let j₀ := Functor.Final.lift e j
  let f₀ : j ⟶ e.obj j₀ := Functor.Final.homToLift e j
  let x₀ := F.map f₀ x
  have hx₀ : (c.whisker e).ι.app j₀ x₀ = 0 := by
    have h := ConcreteCategory.congr_hom (c.w f₀) x
    change c.ι.app (e.obj j₀) (F.map f₀ x) = 0
    exact h.trans hx
  have hEq : ((forget (ModuleCat.{v} k)).mapCocone (c.whisker e)).ι.app j₀ x₀ =
      ((forget (ModuleCat.{v} k)).mapCocone (c.whisker e)).ι.app j₀ 0 := by
    simpa using hx₀
  obtain ⟨j₁, f₁, hf₁⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitForgetMapCoconeWhisker hc) x₀ 0).mp hEq
  refine ⟨e.obj j₁, f₀ ≫ e.map f₁, ?_⟩
  have hf₁' : F.map (e.map f₁) x₀ = 0 := by
    change (ConcreteCategory.hom (F.map (e.map f₁))) x₀ = 0
    change (ConcreteCategory.hom (F.map (e.map f₁))) x₀ =
      (ConcreteCategory.hom (F.map (e.map f₁))) 0 at hf₁
    simpa using hf₁
  change F.map (f₀ ≫ e.map f₁) x = 0
  rw [Functor.map_comp]
  simp only [ConcreteCategory.comp_apply, hf₁', x₀]

/-- Elements of the colimit defining the pointwise left Kan extension of a module-valued functor
come from a stage, and elements killed by the colimit leg are killed by a further morphism. -/
private lemma exists_stage_costructuredArrow
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [EssentiallySmall.{v} C]
    (L : C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
    {k : Type w} [Field k] [Small.{v} k]
    (G : C ⥤ ModuleCat.{v} k) [L.HasPointwiseLeftKanExtension G] (Y : D) :
    (∀ y : (colimit (CostructuredArrow.proj L Y ⋙ G) : ModuleCat.{v} k),
      ∃ (j : CostructuredArrow L Y) (x : G.obj j.left),
        colimit.ι (CostructuredArrow.proj L Y ⋙ G) j x = y) ∧
    ∀ (j : CostructuredArrow L Y) (x : G.obj j.left),
      colimit.ι (CostructuredArrow.proj L Y ⋙ G) j x = 0 →
        ∃ (j' : CostructuredArrow L Y) (f : j ⟶ j'),
          (CostructuredArrow.proj L Y ⋙ G).map f x = 0 := by
  have : IsFiltered (CostructuredArrow L Y) := isFiltered_costructuredArrow L Y
  have : FinallySmall.{v} (CostructuredArrow L Y) :=
    finallySmall_of_essentiallySmall (CostructuredArrow L Y)
  have : LocallySmall.{v} (CostructuredArrow L Y) :=
    locallySmall_of_faithful.{v} (CostructuredArrow.proj L Y)
  let hc := colimit.isColimit (CostructuredArrow.proj L Y ⋙ G)
  exact ⟨exists_stage_of_filtered_module_colimit hc,
    fun _ x hx => exists_stage_map_zero_of_filtered_module_colimit hc x hx⟩

private lemma pointwiseLeftKanExtension_preservesCoproducts
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasCoproducts.{v} D]
    [LocallySmall.{v} D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{v} C] [EssentiallySmall.{v} C]
    (L : C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
    {k : Type w} [Field k] [Small.{v} k]
    (G : C ⥤ ModuleCat.{v} k) [L.HasPointwiseLeftKanExtension G]
    (hcompact : ∀ X : C, IsCompactObject.{v} (L.obj X))
    (hF : (L.pointwiseLeftKanExtension G).IsHomological) :
    ∀ (α : Type v), PreservesColimitsOfShape (Discrete α)
      (L.pointwiseLeftKanExtension G) := by
  classical
  let F := L.pointwiseLeftKanExtension G
  let : F.IsHomological := hF
  let : F.Additive := inferInstance
  intro α
  constructor
  intro A
  let E : α → D := A.obj ∘ Discrete.mk
  let e := ModuleCat.coprodIsoDirectSum (fun i => F.obj (E i))
  let g : DirectSum α (fun i => F.obj (E i)) →ₗ[k] F.obj (∐ E) :=
    (e.inv ≫ sigmaComparison F E).hom
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply DirectSum.ext_component k
      intro i
      let p : ∐ E ⟶ E i := Sigma.desc fun j =>
        if h : j = i then eqToHom (congrArg E h) else 0
      have hpi : sigmaComparison F E ≫ F.map p =
          e.hom ≫ ModuleCat.ofHom
            (DirectSum.component k α (fun j : α => F.obj (E j)) i) := by
        apply Sigma.hom_ext
        intro j
        ext x
        rw [ι_comp_sigmaComparison_assoc, ← F.map_comp]
        rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
        by_cases hji : j = i
        · subst j
          simp [p]
        · simp [p, hji, DirectSum.component.of]
      have hproj : e.inv ≫ sigmaComparison F E ≫ F.map p =
          ModuleCat.ofHom (DirectSum.component k α (fun j : α => F.obj (E j)) i) := by
        rw [hpi, Iso.inv_hom_id_assoc]
      have hcoord := congrArg (fun z => (F.map p).hom z) hxy
      change (e.inv ≫ sigmaComparison F E ≫ F.map p).hom x =
        (e.inv ≫ sigmaComparison F E ≫ F.map p).hom y at hcoord
      rw [hproj] at hcoord
      change DirectSum.component k α (fun j : α => F.obj (E j)) i x =
        DirectSum.component k α (fun j : α => F.obj (E j)) i y
      exact hcoord
    · intro y
      let c := colimit.cocone (CostructuredArrow.proj L (∐ E) ⋙ G)
      let hp := Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L G
      let y' := (hp (∐ E)).isoColimit.hom y
      obtain ⟨j, x, hx⟩ := (exists_stage_costructuredArrow L G (∐ E)).1 y'
      let : IsCompactObject.{v} (L.obj j.left) := hcompact j.left
      obtain ⟨S, β, hβ⟩ := exists_sum_comp_sigmaι (K := L.obj j.left) E j.hom
      let x₀ := (Functor.pointwiseLeftKanExtensionUnit L G).app j.left x
      let z : DirectSum α (fun i => F.obj (E i)) :=
        ∑ i ∈ S, DirectSum.of (fun i => F.obj (E i)) i
          (ConcreteCategory.hom (F.map (β i)) x₀)
      refine ⟨z, ?_⟩
      have hleg : y = ConcreteCategory.hom (F.map j.hom) x₀ := by
        have hh := ConcreteCategory.congr_hom ((hp (∐ E)).ι_isoColimit_inv j) x
        have hx' := congrArg (ConcreteCategory.hom (hp (∐ E)).isoColimit.inv) hx.symm
        have hy' := ConcreteCategory.congr_hom
          ((hp (∐ E)).isoColimit.hom_inv_id) y
        calc
          y = (ConcreteCategory.hom (hp (∐ E)).isoColimit.inv)
              ((ConcreteCategory.hom (hp (∐ E)).isoColimit.hom) y) := hy'.symm
          _ = (ConcreteCategory.hom (hp (∐ E)).isoColimit.inv)
              ((ConcreteCategory.hom (c.ι.app j)) x) := by simpa [y', c] using hx'
          _ = ConcreteCategory.hom (F.map j.hom) x₀ := by
            change (ConcreteCategory.hom (c.ι.app j ≫ (hp (∐ E)).isoColimit.inv)) x =
              (ConcreteCategory.hom
                ((Functor.pointwiseLeftKanExtensionUnit L G).app j.left ≫ F.map j.hom)) x
            exact hh
      change ConcreteCategory.hom (sigmaComparison F E)
        (ConcreteCategory.hom e.inv z) = y
      rw [hleg, hβ]
      have hterm (i : α) (v : F.obj (E i)) :
          (ConcreteCategory.hom (sigmaComparison F E))
              ((ConcreteCategory.hom e.inv) (DirectSum.of (fun i => F.obj (E i)) i v)) =
            (ConcreteCategory.hom (F.map (Sigma.ι E i))) v := by
        have hcomp :
            ModuleCat.ofHom (DirectSum.lof k α (fun i => F.obj (E i)) i) ≫
                e.inv ≫ sigmaComparison F E = F.map (Sigma.ι E i) := by
          have hinv :
              ModuleCat.ofHom (DirectSum.lof k α (fun i => F.obj (E i)) i) ≫ e.inv =
                Sigma.ι (fun i => F.obj (E i)) i := by
            dsimp [e]
            exact ModuleCat.lof_coprodIsoDirectSum_inv
              (Z := fun j => F.obj (E j)) i
          rw [← Category.assoc, hinv, ι_comp_sigmaComparison]
        have hv := ConcreteCategory.congr_hom hcomp v
        simpa [ConcreteCategory.comp_apply, DirectSum.lof_eq_of] using hv
      simp [z, e, F.map_sum, map_sum, hterm]
  have : IsIso (ModuleCat.ofHom g) := (ConcreteCategory.isIso_iff_bijective _).mpr hg
  have : IsIso (sigmaComparison F E) := by
    have : IsIso (e.hom ≫ ModuleCat.ofHom g) := inferInstance
    simpa [g, e] using this
  have : PreservesColimit (Discrete.functor E) F :=
    PreservesCoproduct.of_iso_comparison _ _
  exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm


private noncomputable def extensionConeObj {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {P Q : ObjectProperty C}
    (a : Σ Y : Subtype P, Σ Z : Subtype Q, (Z.1 ⟶ Y.1⟦(1 : ℤ)⟧)) : C :=
  Classical.choose (Pretriangulated.distinguished_cocone_triangle a.2.2)

private noncomputable def extensionConeMor₁ {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {P Q : ObjectProperty C}
    (a : Σ Y : Subtype P, Σ Z : Subtype Q, (Z.1 ⟶ Y.1⟦(1 : ℤ)⟧)) :
    a.1.1⟦(1 : ℤ)⟧ ⟶ extensionConeObj a :=
  Classical.choose (by
    dsimp [extensionConeObj]
    exact Classical.choose_spec (Pretriangulated.distinguished_cocone_triangle a.2.2))

private noncomputable def extensionConeMor₂ {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {P Q : ObjectProperty C}
    (a : Σ Y : Subtype P, Σ Z : Subtype Q, (Z.1 ⟶ Y.1⟦(1 : ℤ)⟧)) :
    extensionConeObj a ⟶ a.2.1.1⟦(1 : ℤ)⟧ :=
  Classical.choose (by
    dsimp [extensionConeObj, extensionConeMor₁]
    exact Classical.choose_spec
        (Classical.choose_spec (Pretriangulated.distinguished_cocone_triangle
        a.2.2)))

private lemma extensionCone_distinguished {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {P Q : ObjectProperty C}
    (a : Σ Y : Subtype P, Σ Z : Subtype Q, (Z.1 ⟶ Y.1⟦(1 : ℤ)⟧)) :
      Pretriangulated.Triangle.mk a.2.2 (extensionConeMor₁ a) (extensionConeMor₂ a) ∈
      Pretriangulated.distinguishedTriangles := by
  dsimp [extensionConeObj, extensionConeMor₁, extensionConeMor₂]
  exact Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Pretriangulated.distinguished_cocone_triangle a.2.2)))

private noncomputable def extensionConeFamily {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {P Q : ObjectProperty C}
    (a : Σ Y : Subtype P, Σ Z : Subtype Q, (Z.1 ⟶ Y.1⟦(1 : ℤ)⟧)) : C :=
  (shiftFunctor C (-1)).obj (extensionConeObj a)

private lemma essentiallySmall_extensionProduct_of_small
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{v} C] {P Q : ObjectProperty C}
    [ObjectProperty.Small.{v} P] [ObjectProperty.Small.{v} Q] :
    ObjectProperty.EssentiallySmall.{v} (ObjectProperty.extensionProduct P Q) := by
  classical
  let α := Σ Y : Subtype P, Σ Z : Subtype Q, (Z.1 ⟶ Y.1⟦(1 : ℤ)⟧)
  let E : α → C := fun a => extensionConeFamily a
  have : Small.{v} α := by infer_instance
  refine ⟨ObjectProperty.ofObj E, inferInstance, ?_⟩
  intro X hX
  obtain ⟨Y, Z, f, g, h, hT, hY, hZ⟩ := hX
  let a : α := ⟨⟨Y, hY⟩, ⟨Z, hZ⟩, h⟩
  let T := Pretriangulated.Triangle.mk f g h
  have hT₁ : T.rotate.rotate ∈ Pretriangulated.distinguishedTriangles :=
    Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang T hT)
  let T' := Pretriangulated.Triangle.mk a.2.2 (extensionConeMor₁ a) (extensionConeMor₂ a)
  have hT₂ : T' ∈ Pretriangulated.distinguishedTriangles := extensionCone_distinguished a
  obtain ⟨c, hc₁, hc₂⟩ := Pretriangulated.complete_distinguished_triangle_morphism
    (T.rotate.rotate) T' hT₁ hT₂ (𝟙 Z) (𝟙 (Y⟦(1 : ℤ)⟧)) (by
      change h ≫ 𝟙 (Y⟦(1 : ℤ)⟧) = 𝟙 Z ≫ h
      simp)
  let φ := Pretriangulated.Triangle.homMk (T.rotate.rotate) T'
    (𝟙 Z) (𝟙 (Y⟦(1 : ℤ)⟧)) c (by
      change h ≫ 𝟙 (Y⟦(1 : ℤ)⟧) = 𝟙 Z ≫ h
      simp) hc₁ hc₂
  have hφ : IsIso φ.hom₃ := Pretriangulated.isIso₃_of_isIso₁₂ φ hT₁ hT₂
    (inferInstanceAs (IsIso (𝟙 Z))) (inferInstanceAs (IsIso (𝟙 (Y⟦(1 : ℤ)⟧))))
  have : IsIso c := hφ
  have e₁' : T.rotate.rotate.obj₃ ≅ T'.obj₃ := asIso c
  have e₁ : X⟦(1 : ℤ)⟧ ≅ extensionConeObj a := by
    simpa [T, T', a] using e₁'
  have e₂ : X⟦(1 : ℤ)⟧⟦(-1 : ℤ)⟧ ≅ extensionConeFamily a :=
    (shiftFunctor C (-1)).mapIso e₁
  have e₃ : X ≅ extensionConeFamily a :=
    ((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by norm_num)).app X).symm ≪≫ e₂
  rw [ObjectProperty.prop_isoClosure_iff]
  exact ⟨extensionConeFamily a, ObjectProperty.ofObj_apply E a, ⟨e₃⟩⟩

private lemma essentiallySmall_extensionProduct
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{v} C] {P Q : ObjectProperty C}
    [ObjectProperty.EssentiallySmall.{v} P] [ObjectProperty.EssentiallySmall.{v} Q] :
    ObjectProperty.EssentiallySmall.{v} (ObjectProperty.extensionProduct P Q) := by
  obtain ⟨P₀, hP₀, hP₁, hP₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{v} P
  obtain ⟨Q₀, hQ₀, hQ₁, hQ₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{v} Q
  have h : ObjectProperty.extensionProduct P Q ≤
      ObjectProperty.extensionProduct P₀ Q₀ := by
    calc
      ObjectProperty.extensionProduct P Q ≤
          ObjectProperty.extensionProduct P₀.isoClosure Q₀.isoClosure :=
        (ObjectProperty.monotone_extensionProduct_left _ hP₂).trans
          (ObjectProperty.monotone_extensionProduct_right _ hQ₂)
      _ = ObjectProperty.extensionProduct P₀ Q₀ := by
        rw [ObjectProperty.extensionProduct_isoClosure_left,
          ObjectProperty.extensionProduct_isoClosure_right]
  have : ObjectProperty.EssentiallySmall.{v}
      (ObjectProperty.extensionProduct P₀ Q₀) :=
    essentiallySmall_extensionProduct_of_small (P := P₀) (Q := Q₀)
  exact ObjectProperty.EssentiallySmall.of_le h


private lemma essentiallySmall_shiftClosure
    {C : Type u} [Category.{v} C] [HasShift C ℤ] {P : ObjectProperty C}
    [ObjectProperty.EssentiallySmall.{v} P] :
    ObjectProperty.EssentiallySmall.{v} (P.shiftClosure ℤ) := by
  classical
  obtain ⟨Q, hQ, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le'.{v} P
  let E : Subtype Q × ℤ → C := fun a ↦ a.1.1⟦a.2⟧
  have : Small.{v} (Subtype Q × ℤ) := inferInstance
  refine ⟨ObjectProperty.ofObj E, inferInstance, ?_⟩
  intro X hX
  obtain ⟨Y, n, e, hY⟩ := hX
  obtain ⟨Z, hZ, ⟨i⟩⟩ := hP Y hY
  refine ⟨E (⟨Z, hZ⟩, n), ObjectProperty.ofObj_apply E (⟨Z, hZ⟩, n), ?_⟩
  exact ⟨e ≪≫ (shiftFunctor C n).mapIso i⟩

private lemma closedUnderFiniteCoproducts_of_triangulated
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [HasCoproducts.{v} C]
    {P : ObjectProperty C} [P.IsClosedUnderIsomorphisms] [P.IsTriangulated] :
    P.IsClosedUnderFiniteCoproducts :=
  ⟨fun _ _ ↦ P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _⟩

private theorem triangEnvelope_eq_compactObjects_of_generators
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    [HasCoproducts.{v} D] {ι : Type v} (E : ι → D) (hι : Nonempty ι)
    (hEc : ∀ i, IsCompactObject.{v} (E i))
    (hGen : (ObjectProperty.ofObj E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.ofObj E).triangEnvelope = IsCompactObject.{v} (C := D) := by
  classical
  have : (ObjectProperty.ofObj E).Nonempty := by
    obtain ⟨i⟩ := hι
    exact ⟨E i, ObjectProperty.ofObj_apply E i⟩
  have : ObjectProperty.IsStableUnderRetracts (IsCompactObject.{v} (C := D)) :=
    ⟨fun r h ↦ isCompactObject_of_retract h r.i r.r r.retract⟩
  have : ObjectProperty.IsTriangulated (IsCompactObject.{v} (C := D)) :=
    (isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := D)).2.1
  have hle : (ObjectProperty.ofObj E).triangEnvelope ≤ IsCompactObject.{v} (C := D) := by
    rw [ObjectProperty.triangEnvelope_le_iff]
    intro X hX
    obtain ⟨i⟩ := hX
    exact hEc i
  refine le_antisymm hle ?_
  intro X hX
  have hcompact : IsCompactObject.{v} X := hX
  obtain ⟨F, hcolim, hF₀, hFstep⟩ :=
    Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated E hGen X
  obtain ⟨p, q, hT⟩ := hcolim
  have := compact_preserves_discrete_nat X
  obtain ⟨e, he⟩ :=
    exists_iso_colimit_preadditiveCoyoneda_of_isHomotopyColimit F X p q hT
  obtain ⟨n, a, ha⟩ := exists_stage_of_filtered_colimit
    (colimit.isColimit (F ⋙ preadditiveCoyoneda.obj (op X)))
    (ConcreteCategory.hom e.inv (𝟙 X))
  have hfac : a ≫ (Limits.Sigma.ι F.obj n ≫ p) = 𝟙 X := by
    have hι : ConcreteCategory.hom
        (colimit.ι (F ⋙ preadditiveCoyoneda.obj (op X)) n) a = ConcreteCategory.hom e.inv (𝟙 X) :=
      ha
    have key : ConcreteCategory.hom e.hom
        (ConcreteCategory.hom (colimit.ι (F ⋙ preadditiveCoyoneda.obj (op X)) n) a) = 𝟙 X :=
      hι ▸ Iso.inv_hom_id_apply e (𝟙 X)
    have h1 := ConcreteCategory.congr_hom (he n) a
    simp only [ConcreteCategory.comp_apply] at h1
    exact h1.symm.trans key
  obtain ⟨s, Z, hZ, α, b, hab⟩ :=
    exists_fac_triangEnvelope_of_isCompactObject E hF₀
      (fun m ↦ by
        obtain ⟨Y, hY, f, g, hT⟩ := hFstep m
        exact ⟨Y, hY, f, F.map (homOfLE (Nat.le_succ m)), g, hT⟩) a
  have hZE : (ObjectProperty.ofObj E).triangEnvelope Z := by
    have hle' : (ObjectProperty.singleton (∐ fun i : s ↦ E i)).triangEnvelope ≤
        (ObjectProperty.ofObj E).triangEnvelope := by
      rw [ObjectProperty.triangEnvelope_le_iff]
      intro Y hY
      rw [ObjectProperty.singleton_iff] at hY
      subst Y
      have : ((ObjectProperty.ofObj E).triangEnvelope).IsClosedUnderFiniteCoproducts :=
        closedUnderFiniteCoproducts_of_triangulated
      exact ObjectProperty.prop_coproduct
        (P := (ObjectProperty.ofObj E).triangEnvelope)
        (f := fun i : s ↦ E i)
        (fun i ↦ ObjectProperty.le_triangEnvelope _ _ (ObjectProperty.ofObj_apply E i))
    exact hle' _ hZ
  have hRetract : Retract X Z :=
    { i := α
      r := b ≫ Limits.Sigma.ι F.obj n ≫ p
      retract := by rw [← Category.assoc, hab, hfac] }
  exact ObjectProperty.prop_of_retract _ hRetract hZE

private lemma pointwiseLeftKanExtension_isHomological
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [LocallySmall.{v} C]
    [EssentiallySmall.{v} C] [LocallySmall.{v} D]
    (L : C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
    {k : Type w} [Field k] [Small.{v} k]
    (G : C ⥤ ModuleCat.{v} k) [G.IsHomological]
    [L.HasPointwiseLeftKanExtension G] :
    (L.pointwiseLeftKanExtension G).IsHomological := by
  let F := L.pointwiseLeftKanExtension G
  -- `F.obj Y` is `colimit (CostructuredArrow.proj L Y ⋙ G)`, and the only thing the argument
  -- below uses about `F` is how its action on a morphism meets those colimit legs. Any other
  -- step that touches it meets `(CostructuredArrow.proj L Y ⋙ G).obj j` against
  -- `G.obj j.left`, which neither `rewrite` nor `simp` can cross; so the leg is ascribed once,
  -- with its type written in terms of `F`, and the leg identity proved once.
  let ιF : ∀ (Y : D) (j : CostructuredArrow L Y), G.obj j.left ⟶ F.obj Y :=
    fun Y j => colimit.ι (CostructuredArrow.proj L Y ⋙ G) j
  have hιF : ∀ (Y₁ Y₂ : D) (f : Y₁ ⟶ Y₂) (j : CostructuredArrow L Y₁),
      ιF Y₁ j ≫ F.map f = ιF Y₂ ((CostructuredArrow.map f).obj j) :=
    fun _ _ _ _ => colimit.ι_desc _ _
  have hFzero : F.PreservesZeroMorphisms := by
    constructor
    intro X Y
    apply colimit.hom_ext
    intro j
    have hz : ιF Y ((CostructuredArrow.map (0 : X ⟶ Y)).obj j) = 0 := by
      let j₀ : CostructuredArrow L Y := CostructuredArrow.mk (0 : L.obj (0 : C) ⟶ Y)
      let ψ : (CostructuredArrow.map (0 : X ⟶ Y)).obj j ⟶ j₀ :=
        CostructuredArrow.homMk 0 (by simp)
      have h := colimit.w (CostructuredArrow.proj L Y ⋙ G) ψ
      ext x
      have h' := ConcreteCategory.congr_hom h x
      simp [ψ, j₀, Functor.map_zero] at h'
      exact h'.symm
    exact (hιF X Y 0 j).trans (hz.trans (Limits.comp_zero).symm)
  let : F.PreservesZeroMorphisms := hFzero
  refine { map_zero := hFzero.map_zero, exact := ?_ }
  · intro T hT
    let S := Pretriangulated.shortComplexOfDistTriangle T hT
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro y
    constructor
    · intro hy
      let c₂ := colimit.cocone (CostructuredArrow.proj L T.obj₂ ⋙ G)
      let c₃ := colimit.cocone (CostructuredArrow.proj L T.obj₃ ⋙ G)
      obtain ⟨j₂, x, hx⟩ := (exists_stage_costructuredArrow L G T.obj₂).1 y
      let j₂₃ := (CostructuredArrow.map T.mor₂).obj j₂
      have hmap₂ : ∀ z, ConcreteCategory.hom (F.map T.mor₂) (c₂.ι.app j₂ z) =
          ConcreteCategory.hom (c₃.ι.app j₂₃) z := fun z =>
        ConcreteCategory.congr_hom (hιF T.obj₂ T.obj₃ T.mor₂ j₂) z
      have hzero : ConcreteCategory.hom (F.map T.mor₂) y = 0 := hy
      -- A chain of typed `have`s rather than a `calc`: inside `calc` the intermediate
      -- relations stay metavariables, and `Trans` cannot be synthesised because the two
      -- sides are stated at two spellings of `F.obj T.obj₂`.
      have hzero' : ConcreteCategory.hom (c₃.ι.app j₂₃) x = 0 :=
        ((hmap₂ x).symm.trans
          (congrArg (ConcreteCategory.hom (F.map T.mor₂)) hx)).trans hzero
      obtain ⟨j₃, φ, hφ⟩ := (exists_stage_costructuredArrow L G T.obj₃).2 j₂₃ x hzero'
      let u : j₂.left ⟶ j₃.left := φ.left
      have hu : G.map u x = 0 := hφ
      obtain ⟨K, fK, hK, hTK⟩ :=
        Pretriangulated.distinguished_cocone_triangle₁ u
      let T' := Pretriangulated.Triangle.mk fK u hK
      have hGexact := G.map_distinguished_exact T' hTK
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hGexact
      obtain ⟨z, hz⟩ := (hGexact x).mp hu
      let a : L.obj j₂.left ⟶ T.obj₂ := j₂.hom
      let b : L.obj j₃.left ⟶ T.obj₃ := j₃.hom
      have hTK' : (L.mapTriangle.obj T') ∈ Pretriangulated.distinguishedTriangles :=
        L.map_distinguished T' hTK
      have hab : (L.map u) ≫ b = a ≫ T.mor₂ := by
        simp [a, b, u, j₂₃]
      obtain ⟨a₀, ha₁, _⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
        (L.mapTriangle.obj T') T hTK' hT a b hab
      let j₁' : CostructuredArrow L T.obj₁ := CostructuredArrow.mk a₀
      let j₂'' := (CostructuredArrow.map T.mor₁).obj j₁'
      -- `ha₁` is stated at `(L.mapTriangle.obj T').mor₁`; re-ascribing it to `L.map fK` is a
      -- term-level defeq that `simp` cannot perform.
      have ha₁' : L.map fK ≫ j₂.hom = a₀ ≫ T.mor₁ := ha₁
      let ψ : j₂'' ⟶ j₂ := CostructuredArrow.homMk fK ha₁'
      let c₁ := colimit.cocone (CostructuredArrow.proj L T.obj₁ ⋙ G)
      refine ⟨ConcreteCategory.hom (c₁.ι.app j₁') z, ?_⟩
      · have hstage₁ : ConcreteCategory.hom (F.map T.mor₁)
            (ConcreteCategory.hom (c₁.ι.app j₁') z) =
              ConcreteCategory.hom (c₂.ι.app j₂'') z :=
          ConcreteCategory.congr_hom (hιF T.obj₁ T.obj₂ T.mor₁ j₁') z
        have hw := colimit.w (CostructuredArrow.proj L T.obj₂ ⋙ G) ψ
        have hw' := ConcreteCategory.congr_hom hw z
        change ConcreteCategory.hom (G.map fK ≫ c₂.ι.app j₂) z =
          ConcreteCategory.hom (c₂.ι.app j₂'') z at hw'
        have hz' : (ConcreteCategory.hom (G.map fK)) z = x := hz
        change (ConcreteCategory.hom (c₂.ι.app j₂))
            ((ConcreteCategory.hom (G.map fK)) z) =
          (ConcreteCategory.hom (c₂.ι.app j₂'')) z at hw'
        rw [hz'] at hw'
        have hy' : ConcreteCategory.hom (c₂.ι.app j₂) x = y := hx
        rw [hy'] at hw'
        exact hstage₁.trans hw'.symm
    · rintro ⟨x, rfl⟩
      change ConcreteCategory.hom (F.map T.mor₂)
        (ConcreteCategory.hom (F.map T.mor₁) x) = 0
      have hcomp : F.map T.mor₁ ≫ F.map T.mor₂ = 0 := by
        rw [← Functor.map_comp, Pretriangulated.comp_distTriang_mor_zero₁₂ T hT,
          Functor.map_zero]
      -- `simp` cannot normalise this goal, whose type is not type-correct at `instances`
      -- transparency; the composite-application identity is `rfl` in `ModuleCat`, so `exact`
      -- absorbs it directly.
      exact ConcreteCategory.congr_hom hcomp x

private lemma essentiallySmall_compactObjects
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    [HasCoproducts.{v} D] [LocallySmall.{v} D]
    (hD : Pretriangulated.IsCompactlyGenerated.{v} D) :
    ObjectProperty.EssentiallySmall.{v} (IsCompactObject.{v} (C := D)) := by
  classical
  obtain ⟨ι, E, hEc, hGen⟩ := hD
  let E' : ι ⊕ PUnit.{v + 1} → D := Sum.elim E (fun _ ↦ (0 : D))
  have hι' : Nonempty (ι ⊕ PUnit.{v + 1}) := ⟨Sum.inr PUnit.unit⟩
  have hEc' : ∀ i, IsCompactObject.{v} (E' i) := by
    intro i
    cases i with
    | inl i => exact hEc i
    | inr i => exact compact_zero
  have hGen' : (ObjectProperty.ofObj E').IsWeakTriangulatedGenerator := by
    intro X hX
    apply hGen X
    intro A f hA
    obtain ⟨B, n, e, hB⟩ := hA
    obtain ⟨i⟩ := hB
    have hA' : (ObjectProperty.ofObj E').shiftClosure ℤ (E i⟦n⟧) :=
      ⟨E' (Sum.inl i), n, Iso.refl _, ObjectProperty.ofObj_apply E' (Sum.inl i)⟩
    simpa using e.hom ≫= hX (e.inv ≫ f) hA'
  have : Small.{v} (ι ⊕ PUnit.{v + 1}) := inferInstance
  have : ObjectProperty.EssentiallySmall.{v} (ObjectProperty.ofObj E') := inferInstance
  have hShift : ObjectProperty.EssentiallySmall.{v}
      ((ObjectProperty.ofObj E').shiftClosure ℤ) := essentiallySmall_shiftClosure
  have hBase : ObjectProperty.EssentiallySmall.{v}
      (((ObjectProperty.ofObj E').shiftClosure ℤ).binaryProductsClosure.retractClosure) := by
    let : ObjectProperty.EssentiallySmall.{v} ((ObjectProperty.ofObj E').shiftClosure ℤ) := hShift
    have : ObjectProperty.EssentiallySmall.{v}
        (((ObjectProperty.ofObj E').shiftClosure ℤ).binaryProductsClosure) := by
      unfold ObjectProperty.binaryProductsClosure
      infer_instance
    let : ObjectProperty.EssentiallySmall.{v}
        (((ObjectProperty.ofObj E').shiftClosure ℤ).binaryProductsClosure) := this
    infer_instance
  let : ObjectProperty.EssentiallySmall.{v}
      (((ObjectProperty.ofObj E').shiftClosure ℤ).binaryProductsClosure.retractClosure) := hBase
  have hEnv : (ObjectProperty.ofObj E').triangEnvelope =
      IsCompactObject.{v} (C := D) :=
    triangEnvelope_eq_compactObjects_of_generators E' hι' hEc' hGen'
  have hIter : ∀ n : ℕ, ObjectProperty.EssentiallySmall.{v}
      ((ObjectProperty.ofObj E').triangEnvelopeIter n) := by
    intro n
    induction n with
    | zero =>
      rw [ObjectProperty.triangEnvelopeIter_zero]
      exact hBase
    | succ n ih =>
      rw [ObjectProperty.triangEnvelopeIter_succ]
      let : ObjectProperty.EssentiallySmall.{v}
          ((ObjectProperty.ofObj E').triangEnvelopeIter n) := ih
      have hProd : ObjectProperty.EssentiallySmall.{v}
          (ObjectProperty.extensionProduct
            (((ObjectProperty.ofObj E').shiftClosure ℤ).binaryProductsClosure.retractClosure)
            ((ObjectProperty.ofObj E').triangEnvelopeIter n)) :=
        essentiallySmall_extensionProduct
      let : ObjectProperty.EssentiallySmall.{v}
          (ObjectProperty.extensionProduct
            (((ObjectProperty.ofObj E').shiftClosure ℤ).binaryProductsClosure.retractClosure)
            ((ObjectProperty.ofObj E').triangEnvelopeIter n)) := hProd
      infer_instance
  have : ObjectProperty.EssentiallySmall.{v} ((ObjectProperty.ofObj E').triangEnvelope) := by
    change ObjectProperty.EssentiallySmall.{v}
      (⨆ n : ℕ, (ObjectProperty.ofObj E').triangEnvelopeIter n)
    let : ∀ n : ℕ, ObjectProperty.EssentiallySmall.{v}
        ((ObjectProperty.ofObj E').triangEnvelopeIter n) := hIter
    infer_instance
  rw [← hEnv]
  infer_instance

/-- The triangulated structure on the full subcategory of compact objects, exposed as an
instance so that cohomological functors on that subcategory can be stated directly. -/
instance compactObjectsIsTriangulated
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasCoproducts.{v} D] :
    ObjectProperty.IsTriangulated (IsCompactObject.{v} (C := D)) :=
  (isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
    (D := D)).2.1

/-- A functor with subsingleton values is represented by the zero object. -/
private lemma exists_iso_comp_linearYoneda_zero_of_subsingleton
    (k : Type w) [Field k]
    {D : Type u} [Category.{v} D] [Preadditive D] [CategoryTheory.Linear k D] [HasZeroObject D]
    {C : Type u} [Category.{v} C] (L : C ⥤ D) (H : Cᵒᵖ ⥤ ModuleCat.{v} k)
    (hall : ∀ X, Subsingleton (H.obj X)) :
    Nonempty (H ≅ L.op ⋙ (linearYoneda k D).obj 0) := by
  refine ⟨?_⟩
  let G := L.op ⋙ (linearYoneda k D).obj (0 : D)
  refine NatIso.ofComponents (fun X ↦ ?_) (by
    intro X Y f
    have hX : IsZero (H.obj X) := ModuleCat.isZero_iff_subsingleton.mpr (hall X)
    let : Unique (H.obj X ⟶ G.obj Y) := (hX.unique_to (G.obj Y)).some
    exact Subsingleton.elim _ _)
  have hX : IsZero (H.obj X) := ModuleCat.isZero_iff_subsingleton.mpr (hall X)
  have hG : IsZero (G.obj X) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (L.obj (unop X) ⟶ (0 : D))
    let : Unique (L.obj (unop X) ⟶ (0 : D)) := (isZero_zero D).unique_from _ |>.some
    infer_instance
  exact hX.isoZero ≪≫ hG.isoZero.symm

/-- A natural isomorphism of underlying additive-group-valued functors between a
`k`-linear functor and a restricted `linearYoneda` functor is `k`-linear. -/
private noncomputable def linearIsoOfForget₂Iso
    (k : Type w) [Field k]
    {D : Type u} [Category.{v} D] [Preadditive D] [CategoryTheory.Linear k D]
    {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear k C]
    (L : C ⥤ D) [L.Additive] [L.Linear k] (H : Cᵒᵖ ⥤ ModuleCat.{v} k)
    (hHlinear : ∀ {X Y} (f : X ⟶ Y) (r : k), H.map ((r • f.unop).op) = r • H.map f)
    (Y : D)
    (hAddIso : H ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat ≅
      L.op ⋙ ((linearYoneda k D).obj Y ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat)) :
    H ≅ L.op ⋙ (linearYoneda k D).obj Y := by
  have hAppBijective (X : Cᵒᵖ) :
      Function.Bijective (ConcreteCategory.hom (hAddIso.hom.app X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact NatIso.ofComponents (fun X => by
      let M : ModuleCat.{v} k :=
        ((linearYoneda k D).obj Y).obj (op (L.obj (unop X)))
      letI : Module k M := inferInstance
      letI : Module k ((L.op ⋙ ((linearYoneda k D).obj Y ⋙
          forget₂ (ModuleCat.{v} k) AddCommGrpCat)).obj X) := by
        change Module k (↑M)
        infer_instance
      let ℓ : H.obj X →ₗ[k] (L.op ⋙ (linearYoneda k D).obj Y).obj X :=
        { toFun := ConcreteCategory.hom (hAddIso.hom.app X)
          map_add' := map_add (ConcreteCategory.hom (hAddIso.hom.app X))
          map_smul' := by
            intro r x
            let fr : X ⟶ X := (r • 𝟙 (unop X)).op
            have hscalar : H.map fr = r • 𝟙 (H.obj X) := by
              simpa [fr] using hHlinear (𝟙 X) r
            have hnat := hAddIso.hom.naturality fr
            have hnat' := ConcreteCategory.congr_hom hnat x
            simp only [Functor.comp_map, AddCommGrpCat.comp_apply] at hnat'
            rw [hscalar] at hnat'
            have htarget : ConcreteCategory.hom
                ((forget₂ (ModuleCat.{v} k) AddCommGrpCat).map
                  (((linearYoneda k D).obj Y).map (L.op.map fr)))
                (ConcreteCategory.hom (hAddIso.hom.app X) x) =
                (r • (ConcreteCategory.hom (hAddIso.hom.app X) x : M) : M) := by
              change L.map fr.unop ≫
                  ConcreteCategory.hom (hAddIso.hom.app X) x = _
              -- `L` is `k`-linear, so `L.map fr.unop` is `r • 𝟙 (L.obj (unop X))`. The
              -- element is typed `↑M` rather than `_ ⟶ Y`, though, so `rewrite` cannot see
              -- the composition; the identity is proved once for a morphism-typed variable.
              have hsmul : ∀ g : L.obj (unop X) ⟶ Y,
                  L.map fr.unop ≫ g = r • g := by
                intro g
                rw [show fr.unop = r • 𝟙 (unop X) from rfl, Functor.map_smul,
                  Functor.map_id, Linear.smul_comp, Category.id_comp]
              exact hsmul _
            calc
              _ = ConcreteCategory.hom
                  ((forget₂ (ModuleCat.{v} k) AddCommGrpCat).map
                    (((linearYoneda k D).obj Y).map (L.op.map fr)))
                  (ConcreteCategory.hom (hAddIso.hom.app X) x) := by
                simpa [ModuleCat.forget₂_map, ModuleCat.hom_smul,
                  ModuleCat.hom_id] using hnat'
              _ = _ := htarget }
      exact (LinearEquiv.ofBijective ℓ (hAppBijective X)).toModuleIso)
    (by
      intro X X' f
      ext x
      exact ConcreteCategory.congr_hom (hAddIso.hom.naturality f) x)

/-- A functor with finite-dimensional values is isomorphic to its double dual. -/
private noncomputable def doubleDualSmallIso (k : Type w) [Field k] [Small.{v} k]
    {C : Type u} [Category.{v} C] (H : Cᵒᵖ ⥤ ModuleCat.{v} k)
    (hH : ∀ X, FiniteDimensional k (H.obj X)) :
    H ≅ (moduleDualComp k H).op ⋙ moduleDualSmall k := by
  refine NatIso.ofComponents (fun X => by
    letI : FiniteDimensional k (H.obj X) := hH X
    exact (doubleDualSmallLinearEquiv k (H.obj X)).toModuleIso) ?_
  intro X X' f
  let : FiniteDimensional k (H.obj X) := hH X
  let : FiniteDimensional k (H.obj X') := hH X'
  apply ModuleCat.hom_ext
  change (doubleDualSmallLinearEquiv k (H.obj X')).toLinearMap.comp (H.map f).hom =
    (moduleDualSmallMap k (moduleDualSmallMap k (H.map f))).hom.comp
      (doubleDualSmallLinearEquiv k (H.obj X)).toLinearMap
  exact (doubleDualSmallLinearEquiv_natural k (H.map f)).symm

/-- A functor from an essentially small pretriangulated category to vector spaces has a pointwise
left Kan extension along any triangulated functor. -/
private lemma hasPointwiseLeftKanExtension_of_isTriangulated
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [EssentiallySmall.{v} C]
    (L : C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
    {k : Type w} [Field k] [Small.{v} k] (G : C ⥤ ModuleCat.{v} k) :
    L.HasPointwiseLeftKanExtension G := by
  intro Y
  let J := CostructuredArrow L Y
  have : IsFiltered J := isFiltered_costructuredArrow L Y
  have : FinallySmall.{v} J := finallySmall_of_essentiallySmall J
  have : LocallySmall.{v} J := locallySmall_of_faithful.{v} (CostructuredArrow.proj L Y)
  exact Functor.Final.hasColimit_of_comp (FinallySmall.fromFilteredFinalModel.{v} J)

/-- Forgetting the linear structure of a homological functor to vector spaces leaves it
homological. -/
private lemma isHomological_comp_forget₂
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {k : Type w} [Field k] (F : D ⥤ ModuleCat.{v} k) [F.IsHomological] :
    (F ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat).IsHomological := by
  refine { map_zero := ?_, exact := ?_ }
  · intro X Y
    change (forget₂ (ModuleCat.{v} k) AddCommGrpCat).map (F.map (0 : X ⟶ Y)) = 0
    ext x
    simp
  · intro T hT
    have hExact := F.map_distinguished_exact T hT
    rw [ShortComplex.ab_exact_iff_function_exact]
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hExact
    simpa using hExact

/-- **The representability theorem along a fully faithful exact functor with compact values.**
Let `D` be a compactly generated `k`-linear triangulated category with arbitrary direct sums, let
`C` be a `k`-linear triangulated category and let `L : C ⥤ D` be a fully faithful exact `k`-linear
functor all of whose values are compact. Every `k`-linear cohomological functor
`H : Cᵒᵖ ⥤ Vect_k` whose values are finite-dimensional is `L^* Hom_D(-, Y)` for an object `Y` of
`D`.

This is [Stacks, Tag 0FYG] with the inclusion of the full subcategory of *all* compact objects
replaced by `L`, and the proof is the same: the pointwise left Kan extension along `L` of the dual
functor is cohomological because the categories of arrows from the image of `L` are filtered
([Stacks, Tag 0FYF], which uses only that `L` is exact), it carries direct sums to direct sums
because the values of `L` are compact, and Brown representability applies to its dual. `C` is
essentially small because `L` embeds it fully faithfully among the compact objects. The tag
itself is the case of the inclusion of the compact objects,
`exists_iso_comp_linearYoneda_of_finiteDimensional`. The generality is what [Stacks, Tag 0FYH]
consumes, where `C` is the category of perfect objects, which is known to consist of compact
objects without being known to exhaust them, and need not contain a set of generators. -/
theorem exists_iso_comp_linearYoneda_of_isCompactObject_obj
    (k : Type w) [Field k]
    (D : Type u) [Category.{v} D] [Preadditive D] [CategoryTheory.Linear k D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{v} D]
    (hD : Pretriangulated.IsCompactlyGenerated.{v} D)
    (C : Type u) [Category.{v} C] [Preadditive C] [CategoryTheory.Linear k C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (L : C ⥤ D) [L.Full] [L.Faithful] [L.CommShift ℤ] [L.IsTriangulated] [L.Linear k]
    (hL : ∀ X : C, IsCompactObject.{v} (L.obj X))
    (H : Cᵒᵖ ⥤ ModuleCat.{v} k)
    [H.IsHomological]
    (hHlinear : ∀ {X Y} (f : X ⟶ Y) (r : k), H.map ((r • f.unop).op) = r • H.map f)
    (hH : ∀ X, FiniteDimensional k (H.obj X)) :
    ∃ Y : D, Nonempty (H ≅ L.op ⋙ (linearYoneda k D).obj Y) := by
  classical
  by_cases hall : ∀ X, Subsingleton (H.obj X)
  · exact ⟨0, exists_iso_comp_linearYoneda_zero_of_subsingleton k L H hall⟩
  · push Not at hall
    obtain ⟨X, hX⟩ := hall
    let : Small.{v} k := small_field_of_nontrivial_module k (H.obj X) hX
    let : ObjectProperty.EssentiallySmall.{v} (IsCompactObject.{v} (C := D)) :=
      essentiallySmall_compactObjects hD
    obtain ⟨ιGen, E, hEc, hGen⟩ := hD
    let G : C ⥤ ModuleCat.{v} k := moduleDualComp k H
    let : G.IsHomological := homological_op_dual k H
    let : EssentiallySmall.{v}
        (ObjectProperty.FullSubcategory (IsCompactObject.{v} (C := D))) := inferInstance
    let : EssentiallySmall.{v} C :=
      essentiallySmall_of_fully_faithful (ObjectProperty.lift _ L hL)
    have := hasPointwiseLeftKanExtension_of_isTriangulated L G
    let F := L.pointwiseLeftKanExtension G
    have hFpoint : (Functor.LeftExtension.mk F
        (Functor.pointwiseLeftKanExtensionUnit L G)).IsPointwiseLeftKanExtension :=
      Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L G
    let : F.IsHomological := pointwiseLeftKanExtension_isHomological L G
    have hFcoprod : ∀ (α : Type v), PreservesColimitsOfShape (Discrete α) F :=
      pointwiseLeftKanExtension_preservesCoproducts L G hL inferInstance
    have hEcoprod : ∀ (i : ιGen) (α : Type v),
        PreservesColimitsOfShape (Discrete α)
          (preadditiveCoyoneda.obj (op (E i))) := by
      intro i α
      have := hEc i
      exact ObjectProperty.preservesColimitsOfShape_discrete_of_isCompactObject (E i) α
    let : (opOpEquivalence D).functor.CommShift ℤ :=
      Pretriangulated.instCommShiftOppositeFunctorOpOpEquivalenceInt
    let : (opOpEquivalence D).functor.IsTriangulated := inferInstance
    let Fopop : (Dᵒᵖ)ᵒᵖ ⥤ ModuleCat.{v} k := (opOpEquivalence D).functor ⋙ F
    let : Fopop.IsHomological := inferInstance
    let Fdual : Dᵒᵖ ⥤ ModuleCat.{v} k := F.op ⋙ moduleDualSmall k
    let : Fdual.IsHomological := by
      change (moduleDualComp k Fopop).IsHomological
      exact homological_op_dual k Fopop
    let HB := Fdual ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat
    have : HB.IsHomological := isHomological_comp_forget₂ Fdual
    let K := ModuleCat.of k (Shrink.{v} k)
    have hHBiso : HB ≅ F.op ⋙ preadditiveYoneda.obj K := by
      refine NatIso.ofComponents (fun X =>
        moduleDualSmall_forgetIsoApp k ((F.op).obj X)) ?_
      intro X Y f
      simpa [HB, Fdual, moduleDualComp, Fopop, opOpEquivalence, opOp,
        unopUnop, K, moduleDualSmall_forgetIso] using
        (moduleDualSmall_forgetIso k).hom.naturality ((F.op).map f)
    have hHBpres : ∀ (α : Type v), PreservesLimitsOfShape (Discrete α) HB := by
      intro α
      have := hFcoprod α
      have : PreservesColimitsOfShape ((Discrete α)ᵒᵖ) F :=
        preservesColimitsOfShape_of_equiv (Discrete.opposite α).symm F
      have : PreservesLimitsOfShape (Discrete α) F.op := preservesLimitsOfShape_op (Discrete α) F
      exact preservesLimitsOfShape_of_natIso hHBiso.symm
    obtain ⟨Y, ⟨e⟩⟩ :=
      Pretriangulated.exists_iso_preadditiveYoneda_of_compactlyGenerated E hGen HB
    have hUnitComponentIso (X : C) :
        IsIso ((Functor.pointwiseLeftKanExtensionUnit L G).app X) :=
      (hFpoint (L.obj X)).isIso_hom_app
    have hUnitIso : G ≅ L ⋙ F :=
      NatIso.ofComponents (fun X => asIso
        ((Functor.pointwiseLeftKanExtensionUnit L G).app X))
        (fun f => (Functor.pointwiseLeftKanExtensionUnit L G).naturality f)
    let hDualRestrIso : G.op ⋙ moduleDualSmall k ≅ L.op ⋙ Fdual := by
      refine NatIso.ofComponents (fun X =>
        ((moduleDualSmall k).mapIso (hUnitIso.app (unop X)).op).symm) ?_
      intro X X' f
      have hnat := hUnitIso.inv.naturality f.unop
      have hmap := congrArg (fun g => (moduleDualSmall k).map g.op) hnat
      simpa [moduleDualSmall, moduleDualSmallMap, Fdual, Category.assoc,
        Functor.comp_map] using hmap.symm
    let hFinalModuleIso : H ≅ L.op ⋙ Fdual := doubleDualSmallIso k H hH ≪≫ hDualRestrIso
    -- It remains to lift the additive-group representability isomorphism to the
    -- required `k`-linear natural isomorphism on compact objects, using the
    -- finite-dimensional double-dual equivalence.
    let hAddIso : H ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat ≅
        L.op ⋙ ((linearYoneda k D).obj Y ⋙
          forget₂ (ModuleCat.{v} k) AddCommGrpCat) := by
      calc
        H ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat ≅
            (L.op ⋙ Fdual) ⋙ forget₂ (ModuleCat.{v} k) AddCommGrpCat :=
          Functor.isoWhiskerRight hFinalModuleIso _
        _ ≅ L.op ⋙ preadditiveYoneda.obj Y :=
          Functor.isoWhiskerLeft L.op e
        _ = L.op ⋙ ((linearYoneda k D).obj Y ⋙
            forget₂ (ModuleCat.{v} k) AddCommGrpCat) := by
          congr 1
    exact ⟨Y, ⟨linearIsoOfForget₂Iso k L H hHlinear Y hAddIso⟩⟩

/-- **Stacks Project, Tag 0FYG.** A finite-dimensional linear cohomological functor on the
compact objects of a compactly generated triangulated category is represented by an object of
the ambient category. -/
@[stacks 0FYG]
theorem exists_iso_comp_linearYoneda_of_finiteDimensional
    (k : Type w) [Field k]
    (D : Type u) [Category.{v} D] [Preadditive D] [CategoryTheory.Linear k D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{v} D]
    (hD : Pretriangulated.IsCompactlyGenerated.{v} D)
    (H : (ObjectProperty.FullSubcategory (IsCompactObject.{v} (C := D)))ᵒᵖ ⥤
      ModuleCat.{v} k)
    [H.IsHomological]
    (hHlinear : ∀ {X Y} (f : X ⟶ Y) (r : k), H.map ((r • f.unop).op) = r • H.map f)
    (hH : ∀ X, FiniteDimensional k (H.obj X)) :
    ∃ Y : D, Nonempty
      (H ≅ (ObjectProperty.ι (IsCompactObject.{v} (C := D))).op ⋙
        (linearYoneda k D).obj Y) :=
  exists_iso_comp_linearYoneda_of_isCompactObject_obj k D hD _
    (ObjectProperty.ι (IsCompactObject.{v} (C := D))) (fun X => X.property) H hHlinear hH

end CategoryTheory
