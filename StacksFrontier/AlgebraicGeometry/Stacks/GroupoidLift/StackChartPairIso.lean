module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackChartOver

/-!
# The two objects of a chart over `Spec (P ⊗ P)`

For a chart `a : (Sch/U₀) ⟶ 𝒳` and `ι : Spec P ⟶ U₀`, the two objects `ξ v₀`, `ξ vₗ` of `𝒳` over
`Spec (P ⊗ P)` are isomorphic as soon as some object maps to `a(1_{U₀})` (up to a vertical
isomorphism) over both points `ι ∘ Spec v₀` and `ι ∘ Spec vₗ`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.nonempty_pairObj_iso`). This is how the
finiteness of the space of arrows is obtained from the finiteness of the inertia in the lifting
lemmas of `StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.LiftCover`.

When `𝒳` is locally of finite presentation over `S` the space of arrows of every chart is locally
of finite presentation (`StackChart.isLocallyOfFinitePresentation_arrSpace_of_structureMorphism`).
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack

universe u t

namespace GroupoidLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)

namespace StackChart

/-- **The two objects of a chart over `Spec (P ⊗ P)` are isomorphic as soon as they receive a
common object.** If `ε : a(1_{U₀}) ⟶ z` lies over the identity and an object `o` has two arrows
`s₀`, `s₁` to `z` lying over the two points `ι ∘ Spec v₀`, `ι ∘ Spec vₗ` of `U₀`, then `ξ v₀` and
`ξ vₗ` are isomorphic in the fibre over `Spec (P ⊗ P)`: both are the pullback of `z` along the
respective point, and `o` maps vertically to each. -/
theorem nonempty_pairObj_iso {o z : 𝒳.val.obj}
    (ε : (CatFiberedInGroupoids.homFunctor a).obj (Over.mk (𝟙 U₀)) ⟶ z)
    (hε : 𝒳.val.p.IsHomLift (𝟙 U₀) ε) (s₀ s₁ : o ⟶ z)
    (hs₀ : 𝒳.val.p.IsHomLift (pt ι (vtx₀ P)).hom s₀)
    (hs₁ : 𝒳.val.p.IsHomLift (pt ι (vtx₁ P)).hom s₁) :
    Nonempty (pairObj₁ a ι ≅ pairObj₀ a ι) := by
  have hp := 𝒳.isFiberedInGroupoids
  have ho : 𝒳.val.p.obj o = specOver (pairAlg P) :=
    IsHomLift.domain_eq 𝒳.val.p (pt ι (vtx₀ P)).hom s₀
  let o' : 𝒳.val.p.Fiber (specOver (pairAlg P)) := ⟨o, ho⟩
  have key : ∀ (v : P.obj →ₐ[ringOf B S hS T'] (pairAlg P).obj) (s : o ⟶ z)
      (_ : 𝒳.val.p.IsHomLift (pt ι v).hom s),
      ∃ φ : o' ⟶ ξF a ι v, True := by
    intro v s hs
    let t := (CatFiberedInGroupoids.homFunctor a).map (Over.mkIdTerminal.from (pt ι v)) ≫ ε
    have := hε
    have hmap : 𝒳.val.p.IsHomLift (pt ι v).hom
        ((CatFiberedInGroupoids.homFunctor a).map (Over.mkIdTerminal.from (pt ι v))) :=
      Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal 𝒳.val.p U₀ a.hom (pt ι v)
    have ht : 𝒳.val.p.IsHomLift (pt ι v).hom t :=
      IsHomLift.comp_lift_id_right 𝒳.val.p (pt ι v).hom _ ε
    have : 𝒳.val.p.IsStronglyCartesian (pt ι v).hom t := hp.isStronglyCartesian_homLift _ _
    have := hs
    exact ⟨⟨Functor.IsStronglyCartesian.map 𝒳.val.p (pt ι v).hom t (Category.id_comp _).symm s,
      Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ _⟩, trivial⟩
  obtain ⟨φ₀, -⟩ := key (vtx₀ P) s₀ hs₀
  obtain ⟨φ₁, -⟩ := key (vtx₁ P) s₁ hs₁
  have := (hp.fiber_isGroupoid (specOver (pairAlg P))).all_isIso φ₀
  have := (hp.fiber_isGroupoid (specOver (pairAlg P))).all_isIso φ₁
  exact ⟨(asIso φ₁).symm ≪≫ asIso φ₀⟩

/-- Over a stack locally of finite presentation over `S`, the space of arrows of every chart over
an affine `T'` is locally of finite presentation (whatever the two chart objects are). -/
theorem isLocallyOfFinitePresentation_arrSpace_of_structureMorphism
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (f : 𝒳 ⟶ schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f) :
    Space.IsLocallyOfFinitePresentation B S hS (OverShriek.presheafToYoneda (pairIsom a ι)) :=
  isLocallyOfFinitePresentation_arrSpace a ι h𝒳 f hf
    (sameImage_pairObj f (Over.mkIdTerminal.from T') (Over.mkIdTerminal.hom_ext _ _))


end StackChart

open StackChart

variable (B S hS) in
/-- **The spaces of arrows of the charts of `𝒳` with isomorphic chart objects are locally of
finite presentation.** For every affine `T₀`, every chart `a : (Sch/U₀) ⟶ 𝒳` and every
`ι : Spec P ⟶ U₀` with `P` an algebra over `Γ(T₀)` such that the two objects `ξ v₀`, `ξ vₗ` over
`Spec (P ⊗ P)` are isomorphic, the space of arrows is locally of finite presentation over
`Spec (P ⊗ P)`. It holds when `𝒳` is locally of finite presentation over `S`
(`arrowSpacesLocallyOfFinitePresentation_of_structureMorphism`) and when the inertia of `𝒳` is
locally of finite presentation (`arrowSpacesLocallyOfFinitePresentation_of_inertia`). -/
def ArrowSpacesLocallyOfFinitePresentation
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) : Prop :=
  ∀ {T₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
    {P : SmallAlg (ringOf B S hS T₀) B.cutoff} (ι : specOver P ⟶ U₀),
    Nonempty (pairObj₁ a ι ≅ pairObj₀ a ι) →
      Space.IsLocallyOfFinitePresentation B S hS (OverShriek.presheafToYoneda (pairIsom a ι))

/-- The space of arrows of a chart with isomorphic chart objects is locally of finite
presentation, read off `ArrowSpacesLocallyOfFinitePresentation`. -/
theorem ArrowSpacesLocallyOfFinitePresentation.isLocallyOfFinitePresentation
    (h : ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳)
    (hθ : Nonempty (pairObj₁ a ι ≅ pairObj₀ a ι)) :
    Space.IsLocallyOfFinitePresentation B S hS (OverShriek.presheafToYoneda (pairIsom a ι)) := by
  unfold ArrowSpacesLocallyOfFinitePresentation at h
  exact h a ι hθ

/-- Over a stack locally of finite presentation over `S` the spaces of arrows of all charts are
locally of finite presentation. -/
theorem arrowSpacesLocallyOfFinitePresentation_of_structureMorphism
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (f : 𝒳 ⟶ schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f) :
    ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳 := by
  unfold ArrowSpacesLocallyOfFinitePresentation
  intro T₀ _ U₀ a P ι _
  exact StackChart.isLocallyOfFinitePresentation_arrSpace_of_structureMorphism a ι h𝒳 f hf

end GroupoidLift

end AlgebraicGeometry.Stack

end
