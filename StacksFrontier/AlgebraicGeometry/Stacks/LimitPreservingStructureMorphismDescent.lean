module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRelativeDescentFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism

/-!
# Limit preservation of an algebraic stack from its structure morphism

Let `𝒳` be an algebraic stack over `S` whose structure morphism `𝒳 ⟶ S` of Stacks 050D is
locally of finite type and limit preserving on objects (Stacks 06CU). Then `𝒳` is limit
preserving in the sense of Artin's Axioms, Definition 07XL: the comparison
`colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an equivalence for every cofiltered limit `T = lim Tᵢ` of affine schemes
over `S`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLimitPreserving_artin_of_structureMorphism`.

## Implementation notes

The comparison is an equivalence exactly when the three stage descent conditions of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent` hold. They are the relative
conditions for the structure morphism, read in a target whose fibres are trivial: the algebraic
stack represented by `S` is the slice of the big fppf site over its terminal object, so above
any morphism of the site there is exactly one morphism between any two of its objects. Descent of
objects is limit preservation on objects of the structure morphism; descent of morphisms and of
equalities is relative descent (`AlgebraicGeometry.Stack.RelativeDescentHom`,
`AlgebraicGeometry.Stack.RelativeDescentEq`) for it, which holds because it is locally of finite
type.

## References

* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 0CMX](https://stacks.math.columbia.edu/tag/0CMX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Above every morphism of the site there is a morphism of the category fibred in groupoids
represented by `S`.** Its total category is the slice of the big fppf site of `S` over the terminal
object `𝟙 S`, into which every object has exactly one morphism. -/
theorem exists_isHomLift_schemeFibredCategory_id
    (a b : (schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS)))).val.obj)
    {R T : BigFppfOver B S hS} (g : R ⟶ T)
    (ha : (schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS)))).val.p.obj a = R)
    (hb : (schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS)))).val.p.obj b = T) :
    ∃ φ : a ⟶ b,
      (schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS)))).val.p.IsHomLift g φ := by
  let k : a.left ⟶ b.left := eqToHom ha ≫ g ≫ eqToHom hb.symm
  exact ⟨Over.homMk k (Over.mkIdTerminal.hom_ext _ _), IsHomLift.of_fac' _ g _ ha hb rfl⟩

/-- **Morphisms of the category fibred in groupoids represented by `S` are determined by their
image in the site.** Its structure functor is the forgetful functor of a slice, which is
faithful. -/
theorem eq_of_isHomLift_schemeFibredCategory_id
    {a b : (schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS)))).val.obj}
    {R T : BigFppfOver B S hS} (g : R ⟶ T) (φ ψ : a ⟶ b)
    (hφ : (schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS)))).val.p.IsHomLift g φ)
    (hψ : (schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS)))).val.p.IsHomLift g ψ) :
    φ = ψ := by
  apply (Over.forget (Over.mk (𝟙 (B.obj hS)))).map_injective
  exact (IsHomLift.fac' (schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS)))).val.p g φ).trans
    (IsHomLift.fac' _ g ψ).symm

/-- **An algebraic stack whose structure morphism is locally of finite type and limit preserving
on objects is limit preserving in the sense of Stacks 07XL.** The three stage descent conditions
for `𝒳` are limit preservation on objects and relative descent of morphisms and of equalities for
the structure morphism, the conditions on the target being vacuous. -/
theorem isLimitPreserving_artin_of_structureMorphism (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hobj : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳.val
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
      (structureMorphism B S hS 𝒳).hom)
    (hf : IsLocallyOfFiniteType B S hS (structureMorphism B S hS 𝒳)) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳.val := by
  intro I _ _ D c hc
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.2.isFibered
  let inc := BigAffineFppf.inclusion B S hS
  let 𝒮 := schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))
  let F := CatFiberedInGroupoids.homFunctor (structureMorphism B S hS 𝒳).hom
  have hF : F ⋙ 𝒮.val.val.p = 𝒳.val.val.p :=
    CatFiberedInGroupoids.homFunctor_comp_p (structureMorphism B S hS 𝒳).hom
  have hFobj : ∀ x : 𝒳.val.val.obj, 𝒮.val.val.p.obj (F.obj x) = 𝒳.val.val.p.obj x :=
    fun x => Functor.congr_obj hF x
  have hFmap : ∀ {x y : 𝒳.val.val.obj} {R T : BigFppfOver B S hS} (g : R ⟶ T) (φ : x ⟶ y),
      𝒳.val.val.p.IsHomLift g φ → 𝒮.val.val.p.IsHomLift g (F.map φ) := by
    intro x y R T g φ _
    exact Functor.isHomLift_map_of_comp_eq hF g φ
  have hp : 𝒳.val.val.p.IsFiberedInGroupoids := 𝒳.val.2
  have hHom := relativeDescentHom_of_isLocallyOfFiniteType B S hS
    (structureMorphism B S hS 𝒳) hf D c hc
  have hEq := relativeDescentEq_of_isLocallyOfFiniteType B S hS
    (structureMorphism B S hS 𝒳) hf D c hc
  refine { faithful := ?_, full := ?_, essSurj := ?_ }
  · exact Deformation.Artin.faithful_of_descentEq _ hp _ _ fun i b₁ b₂ x δ hδ m m' hm hm' hmm =>
      hEq i b₁ b₂ x δ hδ m m' hm hm' hmm
        (eq_of_isHomLift_schemeFibredCategory_id B S hS _ _ _ (hFmap _ m hm) (hFmap _ m' hm'))
  · refine Deformation.Artin.full_of_descentHom _ hp _ _ ?_
    intro i xi yi x y δ ε hδ hε φ hφ
    obtain ⟨β, hβ⟩ := exists_isHomLift_schemeFibredCategory_id B S hS (F.obj xi.1) (F.obj yi.1)
      (𝟙 (inc.obj (D.obj i))) ((hFobj _).trans xi.2) ((hFobj _).trans yi.2)
    have hw : F.map φ ≫ F.map ε = F.map δ ≫ β := by
      have h₁ : 𝒮.val.val.p.IsHomLift (𝟙 (inc.obj c.pt)) (F.map φ) := hFmap _ φ hφ
      have h₂ : 𝒮.val.val.p.IsHomLift (inc.map (c.π.app i)) (F.map ε) := hFmap _ ε hε
      have h₃ : 𝒮.val.val.p.IsHomLift (inc.map (c.π.app i)) (F.map δ) := hFmap _ δ hδ
      have hl := IsHomLift.comp (p := 𝒮.val.val.p) (𝟙 (inc.obj c.pt)) (inc.map (c.π.app i))
        (F.map φ) (F.map ε)
      have hr := IsHomLift.comp (p := 𝒮.val.val.p) (inc.map (c.π.app i))
        (𝟙 (inc.obj (D.obj i))) (F.map δ) β
      rw [Category.id_comp] at hl
      rw [Category.comp_id] at hr
      exact eq_of_isHomLift_schemeFibredCategory_id B S hS _ _ _ hl hr
    obtain ⟨k, s, b₁, b₂, d₁, d₂, ε', m, hd₁, hd₂, hε', hm, h₁, h₂, -⟩ :=
      hHom i xi yi x y δ ε hδ hε β hβ φ hφ hw
    exact ⟨k, s, b₁, b₂, d₁, d₂, ε', m, hd₁, hd₂, hε', hm, h₁, h₂⟩
  · refine Deformation.Artin.essSurj_of_descentObj _ hp _ _ ?_
    intro x
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
    let y₀ : 𝒮.val.val.obj := Over.mk (Over.mkIdTerminal.from (inc.obj (D.obj i)))
    let y : 𝒮.val.val.p.Fiber (inc.obj (D.obj i)) := ⟨y₀, rfl⟩
    obtain ⟨γ, hγ⟩ := exists_isHomLift_schemeFibredCategory_id B S hS (F.obj x.1) y.1
      (inc.map (c.π.app i)) ((hFobj _).trans x.2) rfl
    have hγc : 𝒮.val.val.p.IsStronglyCartesian (inc.map (c.π.app i)) γ :=
      𝒮.val.2.isStronglyCartesian_homLift _ _
    obtain ⟨k, s, x', xU, δ, β, -, hδ, hβ, hβiso, -, -⟩ :=
      hobj I D c hc i y x γ hγc
    refine ⟨k, x', inv β ≫ δ, ?_⟩
    have := hδ.toIsHomLift
    have h := IsHomLift.comp (p := 𝒳.val.val.p) (𝟙 (inc.obj c.pt)) (inc.map (c.π.app k))
      (inv β) δ
    rwa [Category.id_comp] at h

end AlgebraicGeometry.Stack.AlgebraicStacks

end
