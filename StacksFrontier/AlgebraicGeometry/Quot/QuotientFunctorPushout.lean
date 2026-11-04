module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutFlatInjective

/-!
# The functor of quotients on a pushout along a thickening

Stacks 08IW: in Situation 082M, for a pushout `Y' = Y ⨿_Z Z'` of schemes over `B` along a
thickening `Z ⟶ Z'` and an affine morphism `Z ⟶ Y`, the natural map
`Q_{F/X/B}(Y') ⟶ Q_{F/X/B}(Y) ×_{Q_{F/X/B}(Z)} Q_{F/X/B}(Z')` is bijective, and likewise for
`Q^{fp}` when `X ⟶ B` is locally of finite presentation.

## References

* [Stacks Project, Tag 08IW](https://stacks.math.columbia.edu/tag/08IW)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

section Pushout

variable {Z Z' Y₀ Y' : SchemesOver D.Y} (i : Z ⟶ Z') (f : Z ⟶ Y₀) (g : Z' ⟶ Y') (h : Y₀ ⟶ Y')
  (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map i.left)
    ((BigFppfOver.toScheme B S hS).map f.left) ((BigFppfOver.toScheme B S hS).map g.left)
    ((BigFppfOver.toScheme B S hS).map h.left))

include hpo in
/-- The pushout square commutes in the category of test schemes over the base. -/
theorem pushout_w : f ≫ h = i ≫ g :=
  CostructuredArrow.hom_ext _ _ ((BigFppfOver.toScheme B S hS).map_injective (by
    rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left, Functor.map_comp,
      Functor.map_comp]
    exact hpo.w.symm))

include hpo in
/-- **The situation of Stacks 08KV for the base changes of `X ⟶ B`** to the four corners of the
pushout `Y' = Y ⊔_Z Z'` of test schemes. -/
theorem toThickeningPushoutSpaces
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i.left))
    (hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f.left)) :
    ThickeningPushoutSpaces i.left f.left g.left h.left (D.projection Y') (D.projection Y₀)
      (D.projection Z') (D.projection Z) (D.relativeMap h) (D.relativeMap g) (D.relativeMap f)
      (D.relativeMap i) where
  isPushout := hpo
  isThickening := hi
  isAffineHom := hf
  isPullback_a := isPullback_baseChangeMap D.f h
  isPullback_b := isPullback_baseChangeMap D.f g
  isPullback_c := isPullback_baseChangeMap D.f f
  comm_d := baseChangeMap_comp_inclusion D.f i
  comm := (baseChangeMap_comp D.f f h).symm.trans
    ((congrArg (baseChangeMap D.f) (D.pushout_w i f g h hpo)).trans (baseChangeMap_comp D.f i g))

/-- **The natural map `Q(Y') ⟶ Q(Y) ×_{Q(Z)} Q(Z')`** of Stacks 08IW: a quotient over the
pushout goes to its two pullbacks, which agree over `Z`. -/
def quotientsPushoutMap :
    D.quotientsFunctor.obj (op Y') →
      Types.PullbackObj (D.quotientsFunctor.map f.op) (D.quotientsFunctor.map i.op) :=
  fun K => ⟨(D.quotientsFunctor.map h.op K, D.quotientsFunctor.map g.op K), by
    change (D.quotientsFunctor.map h.op ≫ D.quotientsFunctor.map f.op) K =
      (D.quotientsFunctor.map g.op ≫ D.quotientsFunctor.map i.op) K
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      D.pushout_w i f g h hpo]⟩

end Pushout

/-! ### Injectivity -/

section Injective

/-- If two submodules of `F_T` have the same pullback along `k : T' ⟶ T`, the inverse image along
`X_{T'} ⟶ X_T` kills the composite of the inclusion of the first with the projection onto the
quotient by the second. -/
theorem map_arrow_comp_cokernel_π_eq_zero {T' T : SchemesOver D.Y} (k : T' ⟶ T)
    (K₁ K₂ : Subobject (D.baseChangeModule T))
    (hk : D.quotientPullback k K₁ = D.quotientPullback k K₂) :
    (modulePullback B S hS (D.relativeMap k)).map (K₁.arrow ≫ cokernel.π K₂.arrow) = 0 := by
  let e := D.baseChangeComparison k
  have hk' : kernelSubobject (e.hom.app D.F ≫
        (modulePullback B S hS (D.relativeMap k)).map (cokernel.π K₁.arrow)) =
      kernelSubobject (e.hom.app D.F ≫
        (modulePullback B S hS (D.relativeMap k)).map (cokernel.π K₂.arrow)) := hk
  let y := (modulePullback B S hS (D.relativeMap k)).map K₁.arrow ≫ e.inv.app D.F
  have hy : y ≫ (e.hom.app D.F ≫
      (modulePullback B S hS (D.relativeMap k)).map (cokernel.π K₁.arrow)) = 0 := by
    simp only [y, Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
      cokernel.condition, Functor.map_zero]
  have hy₂ := (kernelSubobject_factors_iff _ y).1 (hk' ▸ kernelSubobject_factors _ y hy)
  simpa only [y, Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp] using hy₂

variable {Z Z' Y₀ Y' : SchemesOver D.Y} (i : Z ⟶ Z') (f : Z ⟶ Y₀) (g : Z' ⟶ Y') (h : Y₀ ⟶ Y')
  (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map i.left)
    ((BigFppfOver.toScheme B S hS).map f.left) ((BigFppfOver.toScheme B S hS).map g.left)
    ((BigFppfOver.toScheme B S hS).map h.left))
  (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i.left))
  (hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f.left))

include hpo hi hf in
/-- **A quotient over the pushout is determined by its two pullbacks** (the injectivity half of
Stacks 08IW): if two submodules of `F_{Y'}` have the same pullbacks to `Y` and to `Z'`, and the
quotient by the second is quasi-coherent and flat over `Y'`, the first is contained in the
second. -/
theorem le_of_quotientPullback_eq (K₁ K₂ : Subobject (D.baseChangeModule Y'))
    (hK₂ : K₂ ∈ D.quotients Y') (hh : D.quotientPullback h K₁ = D.quotientPullback h K₂)
    (hg : D.quotientPullback g K₁ = D.quotientPullback g K₂) : K₁ ≤ K₂ := by
  have hs : K₁.arrow ≫ cokernel.π K₂.arrow = 0 :=
    (D.toThickeningPushoutSpaces i f g h hpo hi hf).eq_zero_of_modulePullback_map_eq_zero
      (M := D.quotientModule Y' K₂) hK₂.1 hK₂.2 _
      (D.map_arrow_comp_cokernel_π_eq_zero h K₁ K₂ hh)
      (D.map_arrow_comp_cokernel_π_eq_zero g K₁ K₂ hg)
  exact (le_kernelSubobject _ K₁ hs).trans (kernelSubobject_cokernel_π K₂).le

include hpo hi hf in
/-- **The injectivity half of Stacks 08IW.** -/
theorem quotientsPushoutMap_injective :
    Function.Injective (D.quotientsPushoutMap i f g h hpo) := by
  intro K₁ K₂ he
  have h₁ := congrArg (fun p => (p.1.1 : D.quotients Y₀).1) he
  have h₂ := congrArg (fun p => (p.1.2 : D.quotients Z').1) he
  exact Subtype.ext (le_antisymm
    (D.le_of_quotientPullback_eq i f g h hpo hi hf K₁.1 K₂.1 K₂.2 h₁ h₂)
    (D.le_of_quotientPullback_eq i f g h hpo hi hf K₂.1 K₁.1 K₁.2 h₁.symm h₂.symm))

end Injective

end QuotientSituation

end AlgebraicGeometry.Space

end
