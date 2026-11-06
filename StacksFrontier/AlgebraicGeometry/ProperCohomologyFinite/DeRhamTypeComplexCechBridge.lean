module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering

/-!
# The Čech complex of a sheaf of modules after restricting the sheaf of rings

Let `ψ : O' ⟶ O` be a morphism of sheaves of rings on a topological space and let `N` be a sheaf
of `O`-modules. The module-valued Čech complex of a cover of an open `V`, computed for `N` read as
a sheaf of `O'`-modules, is the Čech complex of `N` with its `O(V)`-modules read as
`O'(V)`-modules along `ψ_V`. Both complexes are, degreewise, products of the same groups of
sections; only the rings acting on them differ, and they act compatibly because `ψ` is a
morphism of presheaves of rings.

## Main definitions

* `AlgebraicGeometry.DeRhamTypeComplex.cechComplexFunctorCompIso`: an additive,
  product-preserving functor on coefficients commutes with Mathlib's Čech complex.
* `AlgebraicGeometry.DeRhamTypeComplex.sectionsPresheafRestrictScalarsIso`: the presheaf of
  sections over `V` of `N` read over `O'` is that of `N` read along `ψ_V`.
* `AlgebraicGeometry.DeRhamTypeComplex.cechComplexRestrictScalarsIso`: the comparison of the two
  Čech complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v v' u u'

namespace AlgebraicGeometry.DeRhamTypeComplex

/-! ### Changing the coefficient category of Mathlib's Čech complex -/

section Coefficients

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} (U : ι → C)
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
  {A' : Type*} [Category* A'] [HasProducts.{w} A'] [Preadditive A']
  (Φ : A ⥤ A') [Φ.Additive] [∀ J : Type w, PreservesLimitsOfShape (Discrete J) Φ]

/-- **An additive, product-preserving functor on coefficients commutes with the Čech complex**:
in each degree the Čech complex is a product of values of the presheaf, which `Φ` preserves, and
its differential is an alternating sum of maps between such products, which `Φ` preserves as it
is additive. -/
def cechComplexFunctorCompIso (P : Cᵒᵖ ⥤ A) :
    (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ Φ) := by
  let E := (Limits.FormalCoproduct.mk _ U).cech
  let T : CosimplicialObject A := E.rightOp ⋙ (FormalCoproduct.evalOp.{w} C A).obj P
  let e₀ : (FormalCoproduct.evalOp.{w} C A).obj P ⋙ Φ ≅
      (FormalCoproduct.evalOp.{w} C A').obj (P ⋙ Φ) :=
    NatIso.ofComponents (fun Y ↦ PreservesProduct.iso Φ (fun i ↦ P.obj (op (Y.unop.obj i))))
      (by
        intro Y Z f
        apply Pi.hom_ext
        intro i
        dsimp only [Functor.comp_map, Functor.comp_obj, FormalCoproduct.evalOp]
        simp only [PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π,
          Pi.lift_comp_π, Pi.lift_comp_π_assoc, piComparison_comp_π_assoc, ← Φ.map_comp])
  let e : T ⋙ Φ ≅ E.rightOp ⋙ (FormalCoproduct.evalOp.{w} C A').obj (P ⋙ Φ) :=
    Functor.isoWhiskerLeft E.rightOp e₀
  let e' : (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj P) ≅
      (AlgebraicTopology.alternatingCofaceMapComplex A').obj (T ⋙ Φ) := by
    refine HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _) ?_
    intro i j hij
    obtain rfl : i + 1 = j := hij
    change 𝟙 _ ≫ (AlgebraicTopology.AlternatingCofaceMapComplex.obj (T ⋙ Φ)).d i (i + 1) =
      Φ.map ((AlgebraicTopology.AlternatingCofaceMapComplex.obj T).d i (i + 1)) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    symm
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
    rfl
  exact e' ≪≫ (AlgebraicTopology.alternatingCofaceMapComplex A').mapIso e

end Coefficients

/-! ### The presheaf of sections over an open after restricting the sheaf of rings -/

section RestrictScalars

open Stacks.Cohomology.CechSheaf

variable {X : Type u} [TopologicalSpace X]
  {O' O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (ψ : O' ⟶ O) (V : Opens X)

/-- **A group of sections of `N` carries the same `O'(V)`-action whether `N` is read over `O'` or
its sections are read along `ψ_V`**: on a section over `W ⊆ V` the two actions of `r ∈ O'(V)`
are through `ψ_W ∘ (O'(V) → O'(W))` and `(O(V) → O(W)) ∘ ψ_V`, which agree because `ψ` commutes
with the restriction maps of the two sheaves of rings. -/
def sectionsRestrictScalarsLinearEquiv (N : SheafOfModules.{u} O) (W : (Over V)ᵒᵖ) :
    (sectionsPresheaf V ((SheafOfModules.restrictScalars.{u} ψ).obj N)).obj W ≃ₗ[SectionRing O' V]
      (sectionsPresheaf V N ⋙ ModuleCat.restrictScalars (ψ.hom.app (op V)).hom).obj W where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' r x := by
    rw [RingHom.id_apply]
    change (ψ.hom.app (op (unop W).left)).hom
        ((O'.obj.map ((Over.forget V).map
          ((IsTerminal.op (Over V) Over.mkIdTerminal).to W).unop).op).hom r) •
          (show N.val.obj (op (unop W).left) from x) =
      (O.obj.map ((Over.forget V).map
          ((IsTerminal.op (Over V) Over.mkIdTerminal).to W).unop).op).hom
        ((ψ.hom.app (op V)).hom r) • (show N.val.obj (op (unop W).left) from x)
    have h : O'.obj.map ((Over.forget V).map
          ((IsTerminal.op (Over V) Over.mkIdTerminal).to W).unop).op ≫
        ψ.hom.app (op (unop W).left) = ψ.hom.app (op V) ≫
          O.obj.map ((Over.forget V).map
            ((IsTerminal.op (Over V) Over.mkIdTerminal).to W).unop).op :=
      ψ.hom.naturality _
    rw [← RingCat.comp_apply, ← RingCat.comp_apply, h]
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Sections over the opens of `V` do not see a restriction of the sheaf of rings**, except
through the ring acting: for a sheaf of `O`-modules `N`, the presheaf of `O'(V)`-modules of
sections of `N` read as a sheaf of `O'`-modules is the presheaf of `O(V)`-modules of sections of
`N`, read along `ψ_V`. -/
def sectionsPresheafRestrictScalarsIso (N : SheafOfModules.{u} O) :
    sectionsPresheaf V ((SheafOfModules.restrictScalars.{u} ψ).obj N) ≅
      sectionsPresheaf V N ⋙ ModuleCat.restrictScalars (ψ.hom.app (op V)).hom :=
  NatIso.ofComponents (fun W => (sectionsRestrictScalarsLinearEquiv ψ V N W).toModuleIso)
    (fun _ => rfl)

/-- Restriction of scalars preserves products: a product of modules is computed on the
underlying abelian groups, which restriction of scalars does not change. -/
instance preservesLimitsOfShape_discrete_restrictScalars {R R' : Type u} [Ring R] [Ring R']
    (φ : R →+* R') (J : Type u) :
    PreservesLimitsOfShape (Discrete J) (ModuleCat.restrictScalars.{u} φ) :=
  ⟨fun {_} => inferInstance⟩

/-- **The Čech complex of `N` read over `O'` is the Čech complex of `N` read along `ψ_V`**: the
presheaves of sections agree by `sectionsPresheafRestrictScalarsIso`, and restriction of scalars,
being additive and product-preserving, commutes with the Čech complex. -/
def cechComplexRestrictScalarsIso {I : Type u} (Ui : I → Opens X) (hU : V = ⨆ i, Ui i)
    (N : SheafOfModules.{u} O) :
    cechComplex.{u, u, u, u} V Ui hU ((SheafOfModules.restrictScalars.{u} ψ).obj N) ≅
      ((ModuleCat.restrictScalars (ψ.hom.app (op V)).hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cechComplex.{u, u, u, u} V Ui hU N) :=
  (cechComplexFunctor (fun i ↦ coverObject Ui hU i)).mapIso
      (sectionsPresheafRestrictScalarsIso ψ V N) ≪≫
    (cechComplexFunctorCompIso (fun i ↦ coverObject Ui hU i)
      (ModuleCat.restrictScalars (ψ.hom.app (op V)).hom) (sectionsPresheaf V N)).symm

end RestrictScalars

end AlgebraicGeometry.DeRhamTypeComplex

end
