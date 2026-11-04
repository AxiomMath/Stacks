module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackObjGlue

/-!
# The canonical comparison of two solutions of a descent problem

Fix a descent datum `D` relative to an h covering family of an object `U` of the big h category
over `S`.  Two solutions of `D` over two morphisms `W₀ ⟶ U` and `W₁ ⟶ U`
(`AlgebraicGeometry.BigHOver.DescentSolution`) are compared, over any object mapping to both
compatibly over `U`, by a unique morphism
(`AlgebraicGeometry.BigHOver.DescentSolution.existsUnique_isCmp`).  This file names that morphism
and records the three identities it satisfies, which is the form in which the comparison is used:
as the gluing isomorphism of a descent datum assembled out of local solutions, and as the
isomorphism over the exceptional corner of a cartesian square that the essential surjectivity half
of conditions (2) and (3) of Stacks 0EX9 consumes.

That the comparison is an *isomorphism* and not merely a morphism is where the fibres being
groupoids is used, exactly as in
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_covering`: condition (1) of Stacks 0EX9
asserts a stack in groupoids, so `CategoryTheory.Functor.IsFiberedInGroupoids.fiber_isGroupoid`
applies.

## Main definitions

* `AlgebraicGeometry.BigHOver.DescentSolution.cmpIso`: the canonical comparison of two solutions,
  as an isomorphism of the fibre over the common object.

## Main results

* `AlgebraicGeometry.BigHOver.DescentSolution.isCmp_cmpIso`: it compares the two solutions.
* `AlgebraicGeometry.BigHOver.DescentSolution.eq_cmpIso_hom_of_isCmp`: it is the only morphism
  that does.
* `AlgebraicGeometry.BigHOver.DescentSolution.cmpIso_hom_self`,
  `AlgebraicGeometry.BigHOver.DescentSolution.cmpIso_hom_trans` and
  `AlgebraicGeometry.BigHOver.DescentSolution.cmpIso_hom_baseChange`: the comparison of a solution
  with itself is the identity, the comparisons compose, and they are compatible with base change.
  These are the three axioms of a descent datum for the pullback pseudofunctor, which is how a
  family of solutions over a covering is turned into one.
* `AlgebraicGeometry.BigHOver.DescentSolution.isCmp_of_covering`: being a comparison is local on
  the common object.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : Type t} [Category.{v} 𝒳] {p : 𝒳 ⥤ BigHOver B S hS} [p.IsFibered]
variable {U : BigHOver B S hS} {I : Type (u + 1)} {V : I → BigHOver B S hS} {f : ∀ i, V i ⟶ U}
variable {D : (Functor.IsFibered.pullbackPseudofunctor p).DescentData f}

namespace DescentSolution

variable (h1 : IsZariskiStackInGroupoids B S hS p)
  (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
  (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
  (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
  (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)

/-- **The canonical comparison of two solutions of `D`**, over an object mapping to both of their
sources compatibly over `U`.

Existence is `AlgebraicGeometry.BigHOver.DescentSolution.exists_isCmp`; that the comparison is an
isomorphism is because the fibres of a category fibred in groupoids are groupoids. -/
public def cmpIso {T W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U} {F' : T ⟶ U}
    (s : DescentSolution D F₀) {γ₀ : T ⟶ W₀} (hγ₀ : γ₀ ≫ F₀ = F')
    (s' : DescentSolution D F₁) {γ₁ : T ⟶ W₁} (hγ₁ : γ₁ ≫ F₁ = F') :
    Functor.pullbackFiber p s.obj γ₀ ≅ Functor.pullbackFiber p s'.obj γ₁ :=
  have : IsGroupoid (p.Fiber T) := h1.isFiberedInGroupoids.fiber_isGroupoid T
  have : IsIso (exists_isCmp h1 h2 h3 h4 hf s hγ₀ s' hγ₁).choose := IsGroupoid.all_isIso _
  asIso (exists_isCmp h1 h2 h3 h4 hf s hγ₀ s' hγ₁).choose

/-- `AlgebraicGeometry.BigHOver.DescentSolution.cmpIso` compares the two solutions. -/
public theorem isCmp_cmpIso {T W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U} {F' : T ⟶ U}
    (s : DescentSolution D F₀) {γ₀ : T ⟶ W₀} (hγ₀ : γ₀ ≫ F₀ = F')
    (s' : DescentSolution D F₁) {γ₁ : T ⟶ W₁} (hγ₁ : γ₁ ≫ F₁ = F') :
    IsCmp s γ₀ s' γ₁ (cmpIso h1 h2 h3 h4 hf s hγ₀ s' hγ₁).hom :=
  (exists_isCmp h1 h2 h3 h4 hf s hγ₀ s' hγ₁).choose_spec

/-- **`AlgebraicGeometry.BigHOver.DescentSolution.cmpIso` is the only comparison.** -/
public theorem eq_cmpIso_hom_of_isCmp {T W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U}
    {F' : T ⟶ U} {s : DescentSolution D F₀} {γ₀ : T ⟶ W₀} (hγ₀ : γ₀ ≫ F₀ = F')
    {s' : DescentSolution D F₁} {γ₁ : T ⟶ W₁} (hγ₁ : γ₁ ≫ F₁ = F')
    {m : Functor.pullbackFiber p s.obj γ₀ ⟶ Functor.pullbackFiber p s'.obj γ₁}
    (hm : IsCmp s γ₀ s' γ₁ m) : m = (cmpIso h1 h2 h3 h4 hf s hγ₀ s' hγ₁).hom :=
  IsCmp.eq h1 h2 h3 h4 hf hγ₀ hγ₁ hm (isCmp_cmpIso h1 h2 h3 h4 hf s hγ₀ s' hγ₁)

/-- The comparison of a solution with itself along one and the same morphism is the identity. -/
public theorem cmpIso_hom_self {T W₀ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F' : T ⟶ U}
    (s : DescentSolution D F₀) {γ₀ : T ⟶ W₀} (hγ₀ : γ₀ ≫ F₀ = F') :
    (cmpIso h1 h2 h3 h4 hf s hγ₀ s hγ₀).hom = 𝟙 _ :=
  (eq_cmpIso_hom_of_isCmp h1 h2 h3 h4 hf hγ₀ hγ₀ (isCmp_id s γ₀)).symm

/-- **The comparisons of three solutions compose**, which is the cocycle condition of the descent
datum a family of solutions over a covering assembles into. -/
public theorem cmpIso_hom_trans {T W₀ W₁ W₂ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U}
    {F₂ : W₂ ⟶ U} {F' : T ⟶ U} (s : DescentSolution D F₀) {γ₀ : T ⟶ W₀} (hγ₀ : γ₀ ≫ F₀ = F')
    (s' : DescentSolution D F₁) {γ₁ : T ⟶ W₁} (hγ₁ : γ₁ ≫ F₁ = F')
    (s'' : DescentSolution D F₂) {γ₂ : T ⟶ W₂} (hγ₂ : γ₂ ≫ F₂ = F') :
    (cmpIso h1 h2 h3 h4 hf s hγ₀ s' hγ₁).hom ≫ (cmpIso h1 h2 h3 h4 hf s' hγ₁ s'' hγ₂).hom =
      (cmpIso h1 h2 h3 h4 hf s hγ₀ s'' hγ₂).hom :=
  eq_cmpIso_hom_of_isCmp h1 h2 h3 h4 hf hγ₀ hγ₂
    (IsCmp.comp hγ₀ hγ₁ (isCmp_cmpIso h1 h2 h3 h4 hf s hγ₀ s' hγ₁)
      (isCmp_cmpIso h1 h2 h3 h4 hf s' hγ₁ s'' hγ₂))

/-- **The comparisons are compatible with base change**, which is the base-change axiom of the
descent datum a family of solutions over a covering assembles into. -/
public theorem cmpIso_hom_baseChange {T T' W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U}
    {F' : T ⟶ U} {F'' : T' ⟶ U} (s : DescentSolution D F₀) {γ₀ : T ⟶ W₀} (hγ₀ : γ₀ ≫ F₀ = F')
    (s' : DescentSolution D F₁) {γ₁ : T ⟶ W₁} (hγ₁ : γ₁ ≫ F₁ = F') (γ : T' ⟶ T)
    (δ₀ : T' ⟶ W₀) (hδ₀ : γ ≫ γ₀ = δ₀) (δ₁ : T' ⟶ W₁) (hδ₁ : γ ≫ γ₁ = δ₁)
    (hd₀ : δ₀ ≫ F₀ = F'') (hd₁ : δ₁ ≫ F₁ = F'') :
    Functor.baseChangeFiberMor (cmpIso h1 h2 h3 h4 hf s hγ₀ s' hγ₁).hom γ δ₀ hδ₀ δ₁ hδ₁ =
      (cmpIso h1 h2 h3 h4 hf s hd₀ s' hd₁).hom :=
  eq_cmpIso_hom_of_isCmp h1 h2 h3 h4 hf hd₀ hd₁
    (IsCmp.baseChange (isCmp_cmpIso h1 h2 h3 h4 hf s hγ₀ s' hγ₁) γ δ₀ hδ₀ δ₁ hδ₁)

include h1 h2 h3 h4 hf in
/-- **Being a comparison of two solutions is local on the common object.**  A morphism whose base
change to every member of an h covering family of the common object is a comparison is itself a
comparison: the canonical comparison has the same base changes, so the two agree by
`AlgebraicGeometry.BigHOver.eq_of_pullbackFiberHom_eq_of_covering`. -/
public theorem isCmp_of_covering {T W₀ W₁ : BigHOver B S hS} {F₀ : W₀ ⟶ U} {F₁ : W₁ ⟶ U}
    {F' : T ⟶ U} (s : DescentSolution D F₀) {γ₀ : T ⟶ W₀} (hγ₀ : γ₀ ≫ F₀ = F')
    (s' : DescentSolution D F₁) {γ₁ : T ⟶ W₁} (hγ₁ : γ₁ ≫ F₁ = F')
    {m : Functor.pullbackFiber p s.obj γ₀ ⟶ Functor.pullbackFiber p s'.obj γ₁}
    {L : Type (u + 1)} {Tl : L → BigHOver B S hS} (τ : ∀ l, Tl l ⟶ T)
    (hcov : Sieve.ofArrows Tl τ ∈ BigHOver.topology B S hS T)
    (hloc : ∀ (l : L) (δ₀ : Tl l ⟶ W₀) (hδ₀ : τ l ≫ γ₀ = δ₀) (δ₁ : Tl l ⟶ W₁)
      (hδ₁ : τ l ≫ γ₁ = δ₁), IsCmp s δ₀ s' δ₁ (Functor.baseChangeFiberMor m (τ l) δ₀ hδ₀ δ₁ hδ₁)) :
    IsCmp s γ₀ s' γ₁ m := by
  have hkey : m = (cmpIso h1 h2 h3 h4 hf s hγ₀ s' hγ₁).hom := by
    refine eq_of_pullbackFiberHom_eq_of_covering h1 h2 h3 h4 m _ τ hcov fun l ↦ ?_
    refine pullbackFiberHom_eq_of_baseChangeFiberMor_eq' m _ (τ l)
      (mx := τ l ≫ γ₀) rfl (my := τ l ≫ γ₁) rfl ?_
    have hb₀ : (τ l ≫ γ₀) ≫ F₀ = τ l ≫ F' := by rw [Category.assoc, hγ₀]
    have hb₁ : (τ l ≫ γ₁) ≫ F₁ = τ l ≫ F' := by rw [Category.assoc, hγ₁]
    exact IsCmp.eq h1 h2 h3 h4 hf hb₀ hb₁ (hloc l _ rfl _ rfl)
      (IsCmp.baseChange (isCmp_cmpIso h1 h2 h3 h4 hf s hγ₀ s' hγ₁) (τ l) _ rfl _ rfl)
  rw [hkey]
  exact isCmp_cmpIso h1 h2 h3 h4 hf s hγ₀ s' hγ₁

end DescentSolution

end BigHOver

end AlgebraicGeometry

end
