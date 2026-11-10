module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.SectionsOnASubsingletonSpace
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Isomorphisms detected by derived global sections on a space with one point

On a ringed space `Z` whose underlying space has at most one point, derived global sections
`RΓ(Z, -)` detect isomorphisms: a morphism of `D(𝒪_Z)` inducing isomorphisms on all the cohomology
modules of its derived global sections is an isomorphism. Over a field of global functions this
gives the criterion used for the fibre of a Leray--Hirsch situation ([Stacks, Tag 0FMP]): a direct
sum of morphisms `d_i : P_i ⟶ E`, out of objects `P_i` whose derived global sections are a line
spanned by `g_i` in the single degree `n_i`, is an isomorphism as soon as the classes
`d_i(g_i)` form a basis of the total cohomology `⨁_j H^j(Z, E)`.

## Main results

* `Stacks.Cohomology.OnePointDetection.isIso_of_forall_isIso_homology_sections`: derived global
  sections on a space with at most one point detect isomorphisms.
* `Stacks.Cohomology.OnePointDetection.isIso_biproduct_desc_of_basis`: the basis criterion, for an
  arbitrary family of additive functors to vector spaces that jointly detect isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.DerivedSectionsLeray

universe u

namespace Stacks.Cohomology.OnePointDetection

attribute [local instance] HasDerivedCategory.standard

/-! ### The basis criterion -/

section Basis

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C]
  {R : Type u} [Field R] (H : ℤ → C ⥤ ModuleCat.{u} R) [∀ k, (H k).Additive]

/-- **A direct sum of morphisms out of lines is an isomorphism once the classes form a basis.**
Let `H^k`, `k ∈ ℤ`, be additive functors to `R`-vector spaces which jointly detect isomorphisms.
Let `d_i : P_i ⟶ E` be morphisms such that the total cohomology `⨁_k H^k(P_i)` is spanned by a
class `g_i` in degree `n_i`. If the classes `d_i(g_i)` form a basis of `⨁_k H^k(E)`, then
`⨁ d_i : ⨁ P_i ⟶ E` is an isomorphism. -/
theorem isIso_biproduct_desc_of_basis
    (hF : ∀ {A B : C} (φ : A ⟶ B), (∀ j : ℤ, IsIso ((H j).map φ)) → IsIso φ)
    {N : ℕ} (n : Fin N → ℤ) (P : Fin N → C) (E : C) (d : ∀ i, P i ⟶ E)
    (g : ∀ i, (H (n i)).obj (P i))
    (hspan : ∀ (i : Fin N) (j : ℤ) (x : (H j).obj (P i)),
      ∃ c : R, DirectSum.lof R ℤ (fun k => (H k).obj (P i)) j x =
        c • DirectSum.lof R ℤ (fun k => (H k).obj (P i)) (n i) (g i))
    (b : Module.Basis (Fin N) R (DirectSum ℤ fun k => (H k).obj E))
    (hb : ∀ i, b i = DirectSum.lof R ℤ (fun k => (H k).obj E) (n i)
      (((H (n i)).map (d i)).hom (g i))) :
    IsIso (biproduct.desc d) := by
  classical
  let TP : ℤ → Type u := fun k => (H k).obj (⨁ P)
  let TE : ℤ → Type u := fun k => (H k).obj E
  let φ : ∀ k, TP k →ₗ[R] TE k := fun k => ((H k).map (biproduct.desc d)).hom
  let Φ := DirectSum.lmap φ
  -- the images of the generators
  let e : Fin N → DirectSum ℤ TP := fun i =>
    DirectSum.lof R ℤ TP (n i) (((H (n i)).map (biproduct.ι P i)).hom (g i))
  have hΦe : ∀ i, Φ (e i) = b i := by
    intro i
    rw [hb i, DirectSum.lmap_lof]
    congr 1
    change ((H (n i)).map (biproduct.ι P i) ≫ (H (n i)).map (biproduct.desc d)).hom
      (g i) = _
    rw [← Functor.map_comp, biproduct.ι_desc]
  -- the generators span
  have hspanP : ∀ x : DirectSum ℤ TP, x ∈ Submodule.span R (Set.range e) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | of k y =>
      have hy : y = ∑ i, ((H k).map (biproduct.ι P i)).hom
          (((H k).map (biproduct.π P i)).hom y) := by
        have h := congrArg (fun z => ((H k).map z).hom y) (biproduct.total (f := P))
        simp only [CategoryTheory.Functor.map_id, (H k).map_sum,
          ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_id, LinearMap.id_apply,
          Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
        exact h.symm
      rw [← DirectSum.lof_eq_of R, hy, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨c, hc⟩ := hspan i k (((H k).map (biproduct.π P i)).hom y)
      have := congrArg (DirectSum.lmap fun k => ((H k).map (biproduct.ι P i)).hom) hc
      rw [DirectSum.lmap_lof, map_smul, DirectSum.lmap_lof] at this
      rw [this]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
  have hbij : Function.Bijective Φ := by
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hspanP x)
      obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hspanP y)
      simp only [map_sum, map_smul, hΦe] at hxy
      rw [← b.equivFun_symm_apply, ← b.equivFun_symm_apply] at hxy
      rw [b.equivFun.symm.injective hxy]
    · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (b.mem_span y)
      exact ⟨∑ i, c i • e i, by simp only [map_sum, map_smul, hΦe]⟩
  exact hF _ fun k => (ConcreteCategory.isIso_iff_bijective _).2
    ⟨(DirectSum.lmap_injective φ).1 hbij.1 k, (DirectSum.lmap_surjective φ).1 hbij.2 k⟩

end Basis

/-! ### Detection on a space with at most one point -/

section OnePoint

variable (Z : AlgebraicGeometry.RingedSpace.{u, u}) [Subsingleton Z.carrier]

/-- An open subset of a space with at most one point is empty or everything. -/
theorem eq_bot_or_eq_top (U : Opens Z.carrier) : U = ⊥ ∨ U = ⊤ := by
  by_cases h : ∃ z, z ∈ U
  · obtain ⟨z, hz⟩ := h
    refine Or.inr (eq_top_iff.2 fun w _ => ?_)
    rwa [Subsingleton.elim w z]
  · exact Or.inl (eq_bot_iff.2 fun w hw => (h ⟨w, hw⟩).elim)

/-- **Sections over the whole space reflect isomorphisms of sheaves of modules on a space with at
most one point.** On the empty open the modules are modules over the zero ring. -/
theorem isIso_of_isIso_sections {M M' : SheafOfModules.{u} (structureSheafRing Z)} (ψ : M ⟶ M')
    (h : IsIso ((sectionsOverOpen Z ⊤).map ψ)) : IsIso ψ := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (structureSheafRing Z)),
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf (Opens.grothendieckTopology Z.carrier) _),
    NatTrans.isIso_iff_isIso_app]
  intro U
  rcases eq_bot_or_eq_top Z U.unop with hU | hU
  · have hR := Stacks.Cohomology.SubsingletonSections.subsingleton_structureSheafRing_bot Z
    obtain rfl : U = op ⊥ := congrArg op hU
    have key : ∀ N : SheafOfModules.{u} (structureSheafRing Z), Subsingleton (N.val.obj (op ⊥)) :=
      fun N => Stacks.AssociatedSheaf.subsingleton_of_subsingleton_ring
        (S := (structureSheafRing Z).obj.obj (op (⊥ : Opens Z.carrier)))
    have := key M
    have := key M'
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (ψ.val.app (op ⊥))
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · obtain rfl : U = op ⊤ := congrArg op hU
    exact inferInstanceAs (IsIso ((forget₂ (ModuleCat.{u} ((structureSheafRing Z).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).map ((sectionsOverOpen Z ⊤).map ψ)))

/-- **Derived global sections on a space with at most one point detect isomorphisms.** -/
theorem isIso_of_forall_isIso_homology_sections
    {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))} (φ : A ⟶ B)
    (h : ∀ j : ℤ, IsIso ((DerivedCategory.homologyFunctor _ j).map
      ((derivedSectionsOverOpen Z ⊤).map φ))) :
    IsIso φ := by
  refine (DerivedCategory.isIso_iff _ φ).2 fun j => isIso_of_isIso_sections Z _ ?_
  have h₁ := (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (Stacks.Cohomology.SubsingletonSections.derivedSectionsOverOpenIso Z ⊤)
    (DerivedCategory.homologyFunctor _ j)) φ).1 (h j)
  exact (NatIso.isIso_map_iff (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
    (sectionsOverOpen Z ⊤) j) φ).1 h₁

/-- **The cohomology of the structure sheaf in degree `n`, on a space with at most one point**:
derived global sections are global sections, so `H^j(Z, 𝒪_Z[-n])` is the homology in degree `j` of
the complex `Γ(Z, 𝒪_Z)` placed in degree `n`. -/
def homologySectionsSingleIso (n j : ℤ) (M : SheafOfModules.{u} (structureSheafRing Z)) :
    (DerivedCategory.homologyFunctor _ j).obj ((derivedSectionsOverOpen Z ⊤).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj M))) ≅
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj
        ((sectionsOverOpen Z ⊤).obj M)).homology j :=
  (DerivedCategory.homologyFunctor _ j).mapIso
      ((Stacks.Cohomology.SubsingletonSections.derivedSectionsOverOpenIso Z ⊤).app _ ≪≫
        (sectionsOverOpen Z ⊤).mapDerivedCategoryFactors.app _ ≪≫
        DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
          (sectionsOverOpen Z ⊤) (ComplexShape.up ℤ) n).app M)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ j).app _

/-- Away from the degree it sits in, `𝒪_Z[-n]` has no cohomology on a space with at most one
point. -/
theorem isZero_homologySections_single (n j : ℤ) (h : j ≠ n)
    (M : SheafOfModules.{u} (structureSheafRing Z)) :
    IsZero ((DerivedCategory.homologyFunctor _ j).obj ((derivedSectionsOverOpen Z ⊤).obj
      (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj M)))) :=
  (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) n
    ((sectionsOverOpen Z ⊤).obj M) j h).of_iso
    (homologySectionsSingleIso Z n j M)

/-- In the degree it sits in, `H^n(Z, M[-n]) ≅ Γ(Z, M)` on a space with at most one point. -/
def homologySectionsSingleSelfIso (n : ℤ) (M : SheafOfModules.{u} (structureSheafRing Z)) :
    (DerivedCategory.homologyFunctor _ n).obj ((derivedSectionsOverOpen Z ⊤).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj M))) ≅
      (sectionsOverOpen Z ⊤).obj M :=
  homologySectionsSingleIso Z n n M ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _

end OnePoint

end Stacks.Cohomology.OnePointDetection

end
