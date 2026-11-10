module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Criterion
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.CategoryTheory.Sites.Stack.FaithfulGroupoidDescent
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# A 2-fibre product with a stack along a representable morphism is a stack (Stacks 0CKY)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳`, `𝒴`, `𝒵` be categories fibred
in groupoids over the big fppf site of `S`. If `f : 𝒳 ⟶ 𝒵` is representable by algebraic spaces
and `𝒴` is a stack in groupoids, then the 2-fibre product `𝒳 ×_𝒵 𝒴` is a stack in groupoids.

The proof is the one in the source. Representability by algebraic spaces is stable under base
change (Stacks 0302), so the projection `𝒳 ×_𝒵 𝒴 ⟶ 𝒴` is representable by algebraic spaces and
the statement reduces to: a category fibred in groupoids admitting a 1-morphism representable by
algebraic spaces into a stack in groupoids is itself a stack in groupoids. That reduction is
Stacks 0CKJ, whose faithfulness hypothesis and sheaf hypothesis are the two clauses of the
criterion of Stacks 02ZY: the presheaf of isomorphism classes of pairs is an algebraic space
over each scheme-valued point of the target, hence an fppf sheaf, and its sections and
restriction maps are exactly the pairs and the restriction relation that Stacks 0CKJ quantifies
over.

## Main results

* `AlgebraicGeometry.Stack.isStack_of_isRepresentableByAlgebraicSpaces`: a category fibred in
  groupoids with a 1-morphism representable by algebraic spaces into a stack is a stack. This is
  the stack-in-groupoids clause of **Stacks 05UN**.
* `AlgebraicGeometry.Stack.isStack_of_isTwoFibreProduct`: **Stacks 0CKY**.

## Implementation notes

"Stack in groupoids over the big fppf site of `S`" is read in the rendering of Stacks 02ZJ (3)
used by `CategoryTheory.Functor.isStack_of_faithful_of_isSheaf`: a category fibred in groupoids
(`CategoryTheory.Functor.IsFiberedInGroupoids`) whose structure functor is a stack
(`CategoryTheory.Functor.IsStack`). The fibred-in-groupoids half is carried by the bundling into
`CategoryTheory.CatFiberedInGroupoids`, so the content a hypothesis or a conclusion adds is
`CategoryTheory.Functor.IsStack` alone.

Stacks 0CKY is stated for an abstract 2-fibre product square of the 2-category of categories
fibred in groupoids rather than for the 2-fibre product of the source. The reason is the one
recorded for `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`: the
criterion of Stacks 02ZY is stated for a 1-morphism whose source and target carry the same
universes, while the 2-fibre product of a cospan has a strictly larger object universe than the
cospan. The universes are therefore those at which the 2-category is closed under forming the
2-fibre product, where `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` supplies a
square and the statement applies to the 2-fibre product of the source as well.

The two hypotheses of Stacks 0CKJ are supplied from the criterion of Stacks 02ZY as follows. Its
clause (1) is faithfulness of the fibre functors of `f`, which is faithfulness of
`𝒳_U ⥤ 𝒳 ⥤ 𝒴` because the inclusion of a fibre is faithful. Its clause (2) says that the
presheaf of isomorphism classes of pairs on the big fppf site of `U` is an algebraic space; being
an algebraic space it is a sheaf, and transporting along the equivalence between the iterated
slice over an object and the big fppf site of its underlying scheme turns that into the sheaf
condition for the localized topology on the slice. The sections of that presheaf over `h : V ⟶ U`
are the isomorphism classes of pairs `(x, φ : h^* y ⟶ F(x))`, and a morphism `F(x) ⟶ y` of the
total category lying over `h` determines such a pair by factoring through the chosen cartesian
lift of `h` at `y`; that correspondence, its compatibility with restriction, its injectivity and
its surjectivity are the four facts from which the separatedness and gluing hypotheses of
Stacks 0CKJ are read off.

Objects and morphisms of a fibre are spelled through `CategoryTheory.Functor.Fiber.mk`,
`CategoryTheory.Functor.Fiber.homMk`, `CategoryTheory.Functor.Fiber.mapOfComp` and
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor`, whose values agree with the objects and
the morphisms they are composed with only after those definitions are unfolded; and an object of
the 2-category of categories fibred in groupoids is an element of a subtype of
`CategoryTheory.Bicategory.InducedBicategory`, so the projection `𝒳.val` is likewise only
meaningful once that definition is unfolded. Hence the `implicit_reducible` list at the top of the
file. Without it a goal mentioning `𝒳.val.p`, or a composite such as
`ψ ≫ (c.sliceFunctor y).map k`, is not type-correct at `implicit` transparency;
`Lean.Meta.kabstract` then declines to abstract any subterm of it, so `rw` reports "did not find
an occurrence", `calc` cannot assemble its steps, and instance search does not see that a
`CategoryTheory.Functor.Fiber.homMk` lands in a groupoid. This is the same obstruction that
`CategoryTheory.CatFiberedInGroupoids.based` is there to avoid at statement level.

## References

* [Stacks Project, Tag 0CKY](https://stacks.math.columbia.edu/tag/0CKY)
* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 0CKJ](https://stacks.math.columbia.edu/tag/0CKJ)
* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.homMk CategoryTheory.Functor.Fiber.inducedFunctor
  CategoryTheory.Functor.Fiber.mapOfComp
  CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor
  CategoryTheory.Bicategory.InducedBicategory

namespace AlgebraicGeometry.Stack

universe u v w

/-- The presheaf of isomorphism classes of pairs attached to an object of the target over a
scheme is a sheaf for the localized fppf topology on the slice, as soon as it is an algebraic
space over that scheme. -/
private lemma pairIsoClass_isSheaf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U)
    (hpair : AlgebraicGeometry.IsAlgebraicSpacePairIsoClassPresheaf B S hS f c U y) :
    Presheaf.IsSheaf ((AlgebraicGeometry.BigFppfOver.topology B S hS).over U)
      (PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
        𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)) := by
  dsimp [AlgebraicGeometry.IsAlgebraicSpacePairIsoClassPresheaf] at hpair
  obtain ⟨F, hF, e, he⟩ := hpair
  let P := U.iteratedSliceBackward.op ⋙
    PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
      𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)
  let F' := F ⋙ CategoryTheory.uliftFunctor.{max (u + 1) (max w v), u}
  have hF' : Presheaf.IsSheaf
      (AlgebraicGeometry.BigFppfOver.topology B U.left.1 U.left.2) F' :=
    Presheaf.isSheaf_comp_of_isSheaf
      (AlgebraicGeometry.BigFppfOver.topology B U.left.1 U.left.2) F
      CategoryTheory.uliftFunctor.{max (u + 1) (max w v), u} hF.isSheaf
  have hP : Presheaf.IsSheaf
      (AlgebraicGeometry.BigFppfOver.topology B U.left.1 U.left.2) P := by
    let η : P ≅ F' := NatIso.ofComponents (fun V =>
      Equiv.toIso ((e V).trans
        (Equiv.ulift.{max (u + 1) (max w v), u}).symm)) (by
      intro V W g
      ext a
      exact congrArg ULift.up (he g a))
    exact (Presheaf.isSheaf_of_iso_iff η).2 hF'
  let ι := U.iteratedSliceEquiv
  have hQ : Presheaf.IsSheaf ((AlgebraicGeometry.BigFppfOver.topology B S hS).over U)
      (ι.functor.op ⋙ P) := by
    let : ι.functor.IsContinuous
        ((AlgebraicGeometry.BigFppfOver.topology B S hS).over U)
        (AlgebraicGeometry.BigFppfOver.topology B U.left.1 U.left.2) := by
      change U.iteratedSliceForward.IsContinuous
        ((B.topology.over (B.obj hS)).over U) (B.topology.over U.left)
      infer_instance
    exact ι.functor.op_comp_isSheaf_of_isSheaf
      ((AlgebraicGeometry.BigFppfOver.topology B S hS).over U)
      (AlgebraicGeometry.BigFppfOver.topology B U.left.1 U.left.2) P hP
  have η : ι.functor.op ⋙ P ≅
      PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
        𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f) := by
    dsimp [P, ι, Over.iteratedSliceEquiv]
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (CategoryTheory.Equivalence.op (U.iteratedSliceEquiv)).unitIso.symm _ ≪≫
        Functor.leftUnitor _
  exact (Presheaf.isSheaf_of_iso_iff η).1 hQ

/-- The section of the pair-class presheaf determined by a morphism over a base arrow. -/
private noncomputable def pairIsoClassOfHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (h𝒳 : 𝒳.val.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.val.p.IsFiberedInGroupoids)
    (hF : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (g : V ⟶ U)
    (y : 𝒴.val.p.Fiber U) (x : 𝒳.val.p.Fiber V)
    (β : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ y.1)
    (hβ : 𝒴.val.p.IsHomLift g β) :
    (PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
      𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)).obj
        (Opposite.op (Over.mk g)) := by
  let ψ := CategoryTheory.Functor.IsStronglyCartesian.map
    𝒴.val.p g (c.map g y) (g := 𝟙 V) (f' := g) (by simp) β
  let : 𝒴.val.p.IsHomLift (𝟙 V) ψ :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift
      𝒴.val.p g (c.map g y) (g := 𝟙 V) (f' := g) (by simp) β
  let : IsGroupoid (𝒴.val.p.Fiber V) := h𝒴.fiber_isGroupoid V
  let xF := (CategoryTheory.Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor f) hF V).obj x
  let ψf : xF ⟶ c.obj g y := CategoryTheory.Functor.Fiber.homMk 𝒴.val.p V ψ
  exact PairIsoClass.mk (CatFiberedInGroupoids.homFunctor f) c y h𝒳 h𝒴 hF x
    (CategoryTheory.Functor.Fiber.fiberInclusion.map (inv ψf)) (inv ψf).2

private lemma comp_eq_comp_of_section {C : Type*} [Category C] {P Q R T : C}
    {α : P ⟶ Q} {ψ' : Q ⟶ P} {a : Q ⟶ R} {ψ : R ⟶ T} {δ : T ⟶ R} {s : P ⟶ T}
    (h₁ : α ≫ ψ' = 𝟙 P) (h₂ : ψ ≫ δ = 𝟙 R) (h : a ≫ ψ = ψ' ≫ s) : s ≫ δ = α ≫ a :=
  calc s ≫ δ = (α ≫ ψ') ≫ s ≫ δ := by rw [h₁, Category.id_comp]
    _ = α ≫ (a ≫ ψ) ≫ δ := by
      rw [h]
      simp only [Category.assoc]
    _ = α ≫ a := by rw [Category.assoc, h₂, Category.comp_id]

private lemma comp_eq_of_retraction {C : Type*} [Category C] {P Q T Z : C}
    {ψ : P ⟶ T} {δ : T ⟶ P} {a : P ⟶ Q} {α : T ⟶ Q} {ψ' : Q ⟶ T} {m : T ⟶ Z}
    {β : P ⟶ Z} {β' : Q ⟶ Z} (h₁ : ψ ≫ δ = 𝟙 P) (h₂ : α ≫ ψ' = 𝟙 T) (h : δ ≫ a = α)
    (hβ : ψ ≫ m = β) (hβ' : ψ' ≫ m = β') : a ≫ β' = β := by
  subst hβ hβ'
  calc a ≫ ψ' ≫ m = (ψ ≫ δ) ≫ a ≫ ψ' ≫ m := by rw [h₁, Category.id_comp]
    _ = ψ ≫ (δ ≫ a) ≫ ψ' ≫ m := by simp only [Category.assoc]
    _ = ψ ≫ m := by rw [h, ← Category.assoc α, h₂, Category.id_comp]

private lemma comp_eq_of_section {C : Type*} [Category C] {P Q T : C}
    {δ : T ⟶ P} {ψ : P ⟶ T} {a : P ⟶ Q} {ψ' : Q ⟶ T} {δ' : T ⟶ Q}
    (h₁ : δ ≫ ψ = 𝟙 T) (h₂ : ψ' ≫ δ' = 𝟙 Q) (h : a ≫ ψ' = ψ) : δ ≫ a = δ' :=
  calc δ ≫ a = δ ≫ a ≫ ψ' ≫ δ' := by rw [h₂, Category.comp_id]
    _ = δ' := by rw [← Category.assoc a, h, ← Category.assoc, h₁, Category.id_comp]

private lemma fiberInclusion_inv_homMk_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hF : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p)
    {V : AlgebraicGeometry.BigFppfOver B S hS} [IsGroupoid (𝒴.val.p.Fiber V)]
    (x : 𝒳.val.p.Fiber V) (T : 𝒴.val.p.Fiber V)
    (ψ : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ T.1) [𝒴.val.p.IsHomLift (𝟙 V) ψ] :
    Functor.Fiber.fiberInclusion.map (inv (Functor.Fiber.homMk 𝒴.val.p V ψ :
      (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) hF V).obj x
        ⟶ T)) ≫ ψ = 𝟙 T.1 := by
  let φ : (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f)
    hF V).obj x ⟶ T := Functor.Fiber.homMk 𝒴.val.p V ψ
  change Functor.Fiber.fiberInclusion.map (inv φ) ≫ Functor.Fiber.fiberInclusion.map φ = _
  rw [← Functor.map_comp, IsIso.inv_hom_id]
  exact CategoryTheory.Functor.map_id _ _

private lemma comp_fiberInclusion_inv_homMk
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hF : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p)
    {V : AlgebraicGeometry.BigFppfOver B S hS} [IsGroupoid (𝒴.val.p.Fiber V)]
    (x : 𝒳.val.p.Fiber V) (T : 𝒴.val.p.Fiber V)
    (ψ : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ T.1) [𝒴.val.p.IsHomLift (𝟙 V) ψ] :
    ψ ≫ Functor.Fiber.fiberInclusion.map (inv (Functor.Fiber.homMk 𝒴.val.p V ψ :
      (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f) hF V).obj x
        ⟶ T)) = 𝟙 ((CatFiberedInGroupoids.homFunctor f).obj x.1) := by
  let φ : (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f)
    hF V).obj x ⟶ T := Functor.Fiber.homMk 𝒴.val.p V ψ
  change Functor.Fiber.fiberInclusion.map φ ≫ Functor.Fiber.fiberInclusion.map (inv φ) = _
  rw [← Functor.map_comp, IsIso.hom_inv_id]
  exact CategoryTheory.Functor.map_id _ _

private lemma obj_eq_of_isHomLift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    {V W : AlgebraicGeometry.BigFppfOver B S hS} (g : W ⟶ V) {x : 𝒳.val.obj} {y : 𝒴.val.obj}
    (β : (CatFiberedInGroupoids.homFunctor f).obj x ⟶ y) [𝒴.val.p.IsHomLift g β] :
    𝒳.val.p.obj x = W := by
  have hcomp : 𝒴.val.p.obj ((CatFiberedInGroupoids.homFunctor f).obj x) = 𝒳.val.p.obj x := by
    simp
  exact hcomp.symm.trans (CategoryTheory.IsHomLift.domain_eq 𝒴.val.p g β)

/-- Restricting the section of the pair-class presheaf attached to `β : F(x) ⟶ y` along a base
arrow `g` gives the section attached to any morphism `β'` obtained from `β` by precomposing with
a lift of `g`. -/
private lemma pairIsoClassOfHom_restrict
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (h𝒳 : 𝒳.val.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.val.p.IsFiberedInGroupoids)
    (hF : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p)
    {U V W : AlgebraicGeometry.BigFppfOver B S hS} (h : V ⟶ U) (g : W ⟶ V)
    (y : 𝒴.val.p.Fiber U) (x : 𝒳.val.p.Fiber V) (z : 𝒳.val.p.Fiber W)
    (χ : z.1 ⟶ x.1) (hχ : 𝒳.val.p.IsHomLift g χ)
    (β : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ y.1)
    (hβ : 𝒴.val.p.IsHomLift h β)
    (β' : (CatFiberedInGroupoids.homFunctor f).obj z.1 ⟶ y.1)
    (hβ' : 𝒴.val.p.IsHomLift (g ≫ h) β')
    (hcomp : (CatFiberedInGroupoids.homFunctor f).map χ ≫ β = β') :
    let P := PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
      𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)
    P.map ((Over.homMk g (by rfl) :
      (Over.mk (g ≫ h) : Over U) ⟶ Over.mk h).op)
      (pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF h y x β hβ) =
      pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF (g ≫ h) y z β' hβ' := by
  dsimp
  let F := CatFiberedInGroupoids.homFunctor f
  let q := 𝒴.val.p
  let ψ := CategoryTheory.Functor.IsStronglyCartesian.map q h (c.map h y)
    (g := 𝟙 V) (f' := h) (by simp) β
  let ψ' := CategoryTheory.Functor.IsStronglyCartesian.map q (g ≫ h) (c.map (g ≫ h) y)
    (g := 𝟙 W) (f' := g ≫ h) (by simp) β'
  let k : (Over.mk (g ≫ h) : Over U) ⟶ Over.mk h := Over.homMk g (by rfl)
  let : q.IsHomLift (𝟙 V) ψ :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift q h (c.map h y)
      (g := 𝟙 V) (f' := h) (by simp) β
  let : q.IsHomLift (𝟙 W) ψ' :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift q (g ≫ h) (c.map (g ≫ h) y)
      (g := 𝟙 W) (f' := g ≫ h) (by simp) β'
  let : q.IsHomLift g ((c.sliceFunctor y).map k) := by
    simpa [k] using
      (CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor_map_isHomLift c y k)
  let : q.IsHomLift g (F.map χ) :=
    (CategoryTheory.Functor.isHomLift_map_iff_of_comp_eq 𝒳.val.p q F hF g χ).2 hχ
  let : q.IsHomLift g (F.map χ ≫ ψ) := by infer_instance
  let : q.IsHomLift g (ψ' ≫ (c.sliceFunctor y).map k) :=
    CategoryTheory.IsHomLift.comp_lift_id_left q g ((c.sliceFunctor y).map k) ψ'
  have hfac : F.map χ ≫ ψ = ψ' ≫ (c.sliceFunctor y).map k :=
    CategoryTheory.Functor.IsStronglyCartesian.ext q h (c.map h y) g (by
      calc
        (F.map χ ≫ ψ) ≫ c.map h y = F.map χ ≫ β := by
          simpa [Category.assoc] using congrArg (fun t => F.map χ ≫ t)
            (CategoryTheory.Functor.IsStronglyCartesian.fac q h (c.map h y)
              (by simp) β)
        _ = β' := hcomp
        _ = ψ' ≫ c.map (g ≫ h) y :=
          (CategoryTheory.Functor.IsStronglyCartesian.fac q (g ≫ h)
            (c.map (g ≫ h) y) (by simp) β').symm
        _ = (ψ' ≫ (c.sliceFunctor y).map k) ≫ c.map h y := by
          simpa [Category.assoc] using congrArg (fun t => ψ' ≫ t)
            (CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor_map_fac c y k).symm)
  let : IsGroupoid (q.Fiber V) := h𝒴.fiber_isGroupoid V
  let : IsGroupoid (q.Fiber W) := h𝒴.fiber_isGroupoid W
  let xF := (CategoryTheory.Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F hF V).obj x
  let zF := (CategoryTheory.Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F hF W).obj z
  let ψf : xF ⟶ c.obj h y := CategoryTheory.Functor.Fiber.homMk q V ψ
  let ψ'f : zF ⟶ c.obj (g ≫ h) y := CategoryTheory.Functor.Fiber.homMk q W ψ'
  exact PairIsoClass.presheaf_map_mk F c y h𝒳 h𝒴 hF k
    x (CategoryTheory.Functor.Fiber.fiberInclusion.map (inv ψf))
    (inv ψf).2 z (CategoryTheory.Functor.Fiber.fiberInclusion.map (inv ψ'f))
    (inv ψ'f).2 χ hχ (comp_eq_comp_of_section
      (fiberInclusion_inv_homMk_comp B S hS f hF z (c.obj (g ≫ h) y) ψ')
      (comp_fiberInclusion_inv_homMk B S hS f hF x (c.obj h y) ψ) hfac)

/-- Two morphisms `F(x) ⟶ y` and `F(x') ⟶ y` over the same base arrow determine the same
section of the pair-class presheaf exactly when they differ by a vertical morphism `x ⟶ x'`. -/
private lemma pairIsoClassOfHom_eq_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (h𝒳 : 𝒳.val.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.val.p.IsFiberedInGroupoids)
    (hF : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (g : V ⟶ U)
    (y : 𝒴.val.p.Fiber U) (x x' : 𝒳.val.p.Fiber V)
    (β : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ y.1)
    (hβ : 𝒴.val.p.IsHomLift g β)
    (β' : (CatFiberedInGroupoids.homFunctor f).obj x'.1 ⟶ y.1)
    (hβ' : 𝒴.val.p.IsHomLift g β') :
    pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF g y x β hβ =
      pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF g y x' β' hβ' ↔
      ∃ e : x.1 ⟶ x'.1, 𝒳.val.p.IsHomLift (𝟙 V) e ∧
        (CatFiberedInGroupoids.homFunctor f).map e ≫ β' = β := by
  let F := CatFiberedInGroupoids.homFunctor f
  let q := 𝒴.val.p
  let ψ := CategoryTheory.Functor.IsStronglyCartesian.map q g (c.map g y)
    (g := 𝟙 V) (f' := g) (by simp) β
  let ψ' := CategoryTheory.Functor.IsStronglyCartesian.map q g (c.map g y)
    (g := 𝟙 V) (f' := g) (by simp) β'
  let : q.IsHomLift (𝟙 V) ψ :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift q g (c.map g y)
      (g := 𝟙 V) (f' := g) (by simp) β
  let : q.IsHomLift (𝟙 V) ψ' :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift q g (c.map g y)
      (g := 𝟙 V) (f' := g) (by simp) β'
  have hβfac : ψ ≫ c.map g y = β :=
    CategoryTheory.Functor.IsStronglyCartesian.fac q g (c.map g y) (by simp) β
  have hβ'fac : ψ' ≫ c.map g y = β' :=
    CategoryTheory.Functor.IsStronglyCartesian.fac q g (c.map g y) (by simp) β'
  let : IsGroupoid (q.Fiber V) := h𝒴.fiber_isGroupoid V
  let xF := (CategoryTheory.Functor.Fiber.mapOfComp 𝒳.val.p q F hF V).obj x
  let x'F := (CategoryTheory.Functor.Fiber.mapOfComp 𝒳.val.p q F hF V).obj x'
  let ψf : xF ⟶ c.obj g y := CategoryTheory.Functor.Fiber.homMk q V ψ
  let ψ'f : x'F ⟶ c.obj g y := CategoryTheory.Functor.Fiber.homMk q V ψ'
  unfold pairIsoClassOfHom
  rw [PairIsoClass.mk_eq_mk_iff]
  constructor
  · rintro ⟨e, he⟩
    let e' := CategoryTheory.Functor.Fiber.fiberInclusion.map e.hom
    refine ⟨e', e.hom.2, ?_⟩
    have he' : CategoryTheory.Functor.Fiber.fiberInclusion.map (inv ψf) ≫
        F.map e' = CategoryTheory.Functor.Fiber.fiberInclusion.map (inv ψ'f) := he
    exact comp_eq_of_retraction (comp_fiberInclusion_inv_homMk B S hS f hF x (c.obj g y) ψ)
      (fiberInclusion_inv_homMk_comp B S hS f hF x' (c.obj g y) ψ') he' hβfac hβ'fac
  · rintro ⟨e, he, hcomp⟩
    let eF := CategoryTheory.Functor.Fiber.homMk 𝒳.val.p V e
    have : IsGroupoid (𝒳.val.p.Fiber V) := h𝒳.fiber_isGroupoid V
    let eIso : x ≅ x' := asIso eF
    refine ⟨eIso, ?_⟩
    have hψ : F.map (CategoryTheory.Functor.Fiber.fiberInclusion.map eF) ≫ ψ' = ψ :=
      CategoryTheory.Functor.IsStronglyCartesian.ext q g (c.map g y) (𝟙 V) (by
        rw [Category.assoc, hβ'fac, hβfac]
        exact hcomp)
    change CategoryTheory.Functor.Fiber.fiberInclusion.map (inv ψf) ≫
      F.map (CategoryTheory.Functor.Fiber.fiberInclusion.map eF) =
      CategoryTheory.Functor.Fiber.fiberInclusion.map (inv ψ'f)
    exact comp_eq_of_section (fiberInclusion_inv_homMk_comp B S hS f hF x (c.obj g y) ψ)
      (comp_fiberInclusion_inv_homMk B S hS f hF x' (c.obj g y) ψ') hψ

/-- Every section of the pair-class presheaf over `h : V ⟶ U` is the one attached to some
morphism `F(x) ⟶ y` lying over `h`. -/
private lemma pairIsoClassOfHom_surjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (h𝒳 : 𝒳.val.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.val.p.IsFiberedInGroupoids)
    (hF : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (h : V ⟶ U)
    (y : 𝒴.val.p.Fiber U)
    (a : (PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
      𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)).obj
        (Opposite.op (Over.mk h))) :
    ∃ (x : 𝒳.val.p.Fiber V) (β : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ y.1)
      (hβ : 𝒴.val.p.IsHomLift h β),
      pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF h y x β hβ = a := by
  let F := CatFiberedInGroupoids.homFunctor f
  let q := 𝒴.val.p
  obtain ⟨x, φ, hφ, hmk⟩ := PairIsoClass.mk_surjective
    (F := F) (c := c) (y := y) (h𝒳 := 𝒳.2) (h𝒴 := 𝒴.2)
      (hF := CatFiberedInGroupoids.homFunctor_comp_p f) a
  let : q.IsHomLift (𝟙 V) φ := hφ
  let xF := (CategoryTheory.Functor.Fiber.mapOfComp 𝒳.val.p q F hF V).obj x
  let φF : c.obj h y ⟶ xF := CategoryTheory.Functor.Fiber.homMk q V φ
  have : IsGroupoid (q.Fiber V) := h𝒴.fiber_isGroupoid V
  let β := CategoryTheory.Functor.Fiber.fiberInclusion.map (inv φF) ≫ c.map h y
  have hβ : q.IsHomLift h β := by
    let : q.IsHomLift (𝟙 V) (CategoryTheory.Functor.Fiber.fiberInclusion.map (inv φF)) :=
      (inv φF).2
    let : q.IsHomLift h (c.map h y) := by infer_instance
    infer_instance
  let ψ := CategoryTheory.Functor.IsStronglyCartesian.map q h (c.map h y)
    (g := 𝟙 V) (f' := h) (by simp) β
  have hψ : q.IsHomLift (𝟙 V) ψ :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift q h (c.map h y)
      (g := 𝟙 V) (f' := h) (by simp) β
  let ψF : xF ⟶ c.obj h y :=
    CategoryTheory.Functor.Fiber.homMk q V ψ
  have hψraw : ψ = CategoryTheory.Functor.Fiber.fiberInclusion.map (inv φF) := by
    apply CategoryTheory.Functor.IsStronglyCartesian.ext q h (c.map h y) (𝟙 V)
    calc
      ψ ≫ c.map h y = β :=
        CategoryTheory.Functor.IsStronglyCartesian.fac q h (c.map h y) (by simp) β
      _ = CategoryTheory.Functor.Fiber.fiberInclusion.map (inv φF) ≫ c.map h y := rfl
  have hψF' : ψF = inv φF := CategoryTheory.Functor.Fiber.hom_ext hψraw
  have hψφ : ψF ≫ φF = 𝟙 _ := by
    rw [hψF']
    simp
  have hInv : inv ψF = φF := IsIso.inv_eq_of_hom_inv_id hψφ
  refine ⟨x, β, hβ, ?_⟩
  have hcls : pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF h y x β hβ =
      PairIsoClass.mk F c y h𝒳 h𝒴 hF x φ hφ := by
    have hrawinv : CategoryTheory.Functor.Fiber.fiberInclusion.map (inv ψF) = φ := by
      rw [hInv]
      simp [φF]
    unfold pairIsoClassOfHom
    rw [PairIsoClass.mk_eq_mk_iff]
    refine ⟨Iso.refl x, ?_⟩
    rw [hrawinv]
    have hId : CategoryTheory.Functor.Fiber.fiberInclusion.map
        (Iso.refl x).hom = 𝟙 x.1 := rfl
    rw [hId]
    simp
  exact hcls.trans hmk

/-- The isomorphism of the slice over `U` between two objects given by equal structure
morphisms. -/
private def overHomEqIso {C : Type u} [Category.{v} C] {U : C} {Z : Over U}
    (f : Z.left ⟶ U) (hf : Z.hom = f) : Z ≅ Over.mk f where
  hom := Over.homMk (𝟙 Z.left) (by simpa using hf.symm)
  inv := Over.homMk (𝟙 Z.left) (by simpa using hf)
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

/-- Two sections of the pair-class presheaf restrict to the same section along a base arrow `g`
as soon as the two morphisms they come from agree after precomposition with a common lift of
`g`. -/
private lemma pairIsoClassOfHom_restrict_eq_of_common
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (h𝒳 : 𝒳.val.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.val.p.IsFiberedInGroupoids)
    (hF : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p)
    {U V W : AlgebraicGeometry.BigFppfOver B S hS} (h : V ⟶ U) (g : W ⟶ V)
    (y : 𝒴.val.p.Fiber U) (x x' : 𝒳.val.p.Fiber V) (z : 𝒳.val.p.Fiber W)
    (χ : z.1 ⟶ x.1) (hχ : 𝒳.val.p.IsHomLift g χ)
    (χ' : z.1 ⟶ x'.1) (hχ' : 𝒳.val.p.IsHomLift g χ')
    (β : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ y.1)
    (hβ : 𝒴.val.p.IsHomLift h β)
    (β' : (CatFiberedInGroupoids.homFunctor f).obj x'.1 ⟶ y.1)
    (hβ' : 𝒴.val.p.IsHomLift h β')
    (hcomp : (CatFiberedInGroupoids.homFunctor f).map χ ≫ β =
      (CatFiberedInGroupoids.homFunctor f).map χ' ≫ β') :
    let P := PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
      𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)
    P.map ((Over.homMk g (by rfl) :
      (Over.mk (g ≫ h) : Over U) ⟶ Over.mk h).op)
      (pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF h y x β hβ) =
    P.map ((Over.homMk g (by rfl) :
      (Over.mk (g ≫ h) : Over U) ⟶ Over.mk h).op)
      (pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF h y x' β' hβ') := by
  dsimp
  let F := CatFiberedInGroupoids.homFunctor f
  let β₁ := F.map χ ≫ β
  let β₂ := F.map χ' ≫ β'
  have hβ₁ : 𝒴.val.p.IsHomLift (g ≫ h) β₁ := by infer_instance
  have hβ₂ : 𝒴.val.p.IsHomLift (g ≫ h) β₂ := by infer_instance
  have h₁ := pairIsoClassOfHom_restrict B S hS f c h𝒳 h𝒴 hF h g y x z χ hχ β hβ
    β₁ hβ₁ rfl
  have h₂ := pairIsoClassOfHom_restrict B S hS f c h𝒳 h𝒴 hF h g y x' z χ' hχ' β' hβ'
    β₂ hβ₂ rfl
  rw [h₁, h₂]
  change pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF (g ≫ h) y z β₁ hβ₁ =
    pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF (g ≫ h) y z β₂ hβ₂
  congr 1

/-- A sheaf for the localized topology on the slice over `U` satisfies the sheaf condition for the
slice sieve attached to a covering sieve of the source of `h : V ⟶ U`. -/
private lemma isSheafFor_overEquiv_symm
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (h : V ⟶ U)
    {P : (Over U)ᵒᵖ ⥤ Type w} (hP : Presheaf.IsSheaf
      ((AlgebraicGeometry.BigFppfOver.topology B S hS).over U) P)
    {R : Sieve V} (hR : R ∈ AlgebraicGeometry.BigFppfOver.topology B S hS V) :
    Presieve.IsSheafFor P ((Sieve.overEquiv (Over.mk h)).symm R).arrows :=
  ((isSheaf_iff_isSheaf_of_type _ P).mp hP) _
    (GrothendieckTopology.overEquiv_symm_mem_over
      (AlgebraicGeometry.BigFppfOver.topology B S hS) (Over.mk h) R hR)

/-- Separatedness of the pair-class presheaf: two morphisms `F(x) ⟶ y`, `F(x') ⟶ y` over the
same base arrow which agree locally on a covering sieve determine the same section. -/
private lemma pairIsoClass_sheaf_separated
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (h𝒳 : 𝒳.val.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.val.p.IsFiberedInGroupoids)
    (hF : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (y : 𝒴.val.p.Fiber U)
    (hP : Presheaf.IsSheaf ((AlgebraicGeometry.BigFppfOver.topology B S hS).over U)
      (PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
        𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)))
    (h : V ⟶ U) {R : Sieve V}
    (hR : R ∈ AlgebraicGeometry.BigFppfOver.topology B S hS V)
    (x x' : 𝒳.val.p.Fiber V)
    (β : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ y.1)
    (hβ : 𝒴.val.p.IsHomLift h β)
    (β' : (CatFiberedInGroupoids.homFunctor f).obj x'.1 ⟶ y.1)
    (hβ' : 𝒴.val.p.IsHomLift h β')
    (hloc : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V), R g →
      ∃ (z : 𝒳.val.p.Fiber W) (χ : z.1 ⟶ x.1) (χ' : z.1 ⟶ x'.1),
        𝒳.val.p.IsHomLift g χ ∧ 𝒳.val.p.IsHomLift g χ' ∧
          (CatFiberedInGroupoids.homFunctor f).map χ ≫ β =
            (CatFiberedInGroupoids.homFunctor f).map χ' ≫ β') :
    pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF h y x β hβ =
      pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF h y x' β' hβ' := by
  let P := PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
    𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)
  let A : Over U := Over.mk h
  apply (isSheafFor_overEquiv_symm B S hS h hP hR).isSeparatedFor.ext
  intro Z k hk
  have hg : R k.left := (Sieve.overEquiv_symm_iff R k).mp hk
  obtain ⟨z, χ, χ', hχ, hχ', hcomp⟩ := hloc k.left hg
  let e := overHomEqIso (k.left ≫ h) (Over.w k).symm
  let kc : (Over.mk (k.left ≫ h) : Over U) ⟶ A := Over.homMk k.left (by rfl)
  have hfactor : e.hom ≫ kc = k := by
    apply Over.OverMorphism.ext
    change (𝟙 Z.left ≫ k.left) = k.left
    simp
  have hlocal := pairIsoClassOfHom_restrict_eq_of_common B S hS f c h𝒳 h𝒴 hF h
    k.left y x x' z χ hχ χ' hχ' β hβ β' hβ' hcomp
  rw [← hfactor]
  simp only [op_comp, Functor.map_comp, types_comp_apply]
  exact congrArg (P.map e.hom.op) hlocal

/-- Two morphisms `F(x) ⟶ y`, `F(x') ⟶ y` over the same base arrow which agree locally on a
covering sieve differ by a vertical morphism `x ⟶ x'`, as soon as the pair-class presheaves are
algebraic spaces. -/
private lemma exists_vertical_of_locally_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (hpair : ∀ (U : AlgebraicGeometry.BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      AlgebraicGeometry.IsAlgebraicSpacePairIsoClassPresheaf B S hS f c U y)
    (y : 𝒴.val.obj) {V : AlgebraicGeometry.BigFppfOver B S hS} (h : V ⟶ 𝒴.val.p.obj y)
    {R : Sieve V} (hR : R ∈ AlgebraicGeometry.BigFppfOver.topology B S hS V)
    {x x' : 𝒳.val.obj} (β : (CatFiberedInGroupoids.homFunctor f).obj x ⟶ y)
    (β' : (CatFiberedInGroupoids.homFunctor f).obj x' ⟶ y)
    (hβ : 𝒴.val.p.IsHomLift h β) (hβ' : 𝒴.val.p.IsHomLift h β')
    (hloc : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V), R g →
      ∃ (z : 𝒳.val.obj) (χ : z ⟶ x) (χ' : z ⟶ x'),
        𝒳.val.p.IsHomLift g χ ∧ 𝒳.val.p.IsHomLift g χ' ∧
          (CatFiberedInGroupoids.homFunctor f).map χ ≫ β =
            (CatFiberedInGroupoids.homFunctor f).map χ' ≫ β') :
    ∃ e : x ⟶ x', 𝒳.val.p.IsHomLift (𝟙 V) e ∧
      (CatFiberedInGroupoids.homFunctor f).map e ≫ β' = β := by
  let U := 𝒴.val.p.obj y
  let yF : 𝒴.val.p.Fiber U := ⟨y, rfl⟩
  let xF : 𝒳.val.p.Fiber V := ⟨x, obj_eq_of_isHomLift B S hS f h β⟩
  let x'F : 𝒳.val.p.Fiber V := ⟨x', obj_eq_of_isHomLift B S hS f h β'⟩
  refine (pairIsoClassOfHom_eq_iff B S hS f c 𝒳.2 𝒴.2
    (CatFiberedInGroupoids.homFunctor_comp_p f) h yF xF x'F β hβ β' hβ').mp
    (pairIsoClass_sheaf_separated B S hS f c 𝒳.2 𝒴.2
      (CatFiberedInGroupoids.homFunctor_comp_p f) yF
      (pairIsoClass_isSheaf B S hS f c U yF (hpair U yF)) h hR xF x'F β hβ β' hβ' ?_)
  intro W g hg
  obtain ⟨z, χ, χ', hχ, hχ', hcomp⟩ := hloc g hg
  exact ⟨⟨z, CategoryTheory.IsHomLift.domain_eq 𝒳.val.p g χ⟩, χ, χ', hχ, hχ', hcomp⟩

/-- The family of sections of the pair-class presheaf over the slice sieve of `R` attached to
a family of morphisms `F(x_g) ⟶ y` lying over the arrows `g ≫ h` of `R`. -/
private noncomputable def pairIsoClassFamily
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (y : 𝒴.val.p.Fiber U) (h : V ⟶ U)
    (R : Sieve V)
    (xs : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V), R g → 𝒳.val.obj)
    (fs : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g),
      (CatFiberedInGroupoids.homFunctor f).obj (xs g hg) ⟶ y.1)
    (hfs : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g),
      𝒴.val.p.IsHomLift (g ≫ h) (fs g hg)) :
    Presieve.FamilyOfElements
      (PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
        𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f))
      ((Sieve.overEquiv (Over.mk h)).symm R).arrows := fun _ k hk =>
  (PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
    𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)).map
    (overHomEqIso (k.left ≫ h) (Over.w k).symm).hom.op
    (pairIsoClassOfHom B S hS f c 𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)
      (k.left ≫ h) y
      ⟨xs k.left ((Sieve.overEquiv_symm_iff R k).mp hk), obj_eq_of_isHomLift B S hS f
        (k.left ≫ h) (fs k.left ((Sieve.overEquiv_symm_iff R k).mp hk))⟩
      (fs k.left ((Sieve.overEquiv_symm_iff R k).mp hk))
      (hfs k.left ((Sieve.overEquiv_symm_iff R k).mp hk)))

/-- The family of sections attached to a family of morphisms `F(x_g) ⟶ y` which is compatible
along lifts of the arrows of the sieve is a compatible family. -/
private lemma pairIsoClassFamily_compatible
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (y : 𝒴.val.p.Fiber U) (h : V ⟶ U)
    (R : Sieve V)
    (xs : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V), R g → 𝒳.val.obj)
    (fs : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g),
      (CatFiberedInGroupoids.homFunctor f).obj (xs g hg) ⟶ y.1)
    (hfs : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g),
      𝒴.val.p.IsHomLift (g ≫ h) (fs g hg))
    (hcompat : ∀ ⦃W W' : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g)
      (k : W' ⟶ W), ∃ χ : xs (k ≫ g) (R.downward_closed hg k) ⟶ xs g hg,
        𝒳.val.p.IsHomLift k χ ∧ (CatFiberedInGroupoids.homFunctor f).map χ ≫ fs g hg =
          fs (k ≫ g) (R.downward_closed hg k)) :
    (pairIsoClassFamily B S hS f c y h R xs fs hfs).Compatible := by
  let hF := CatFiberedInGroupoids.homFunctor_comp_p f
  let P := PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y 𝒳.2 𝒴.2 hF
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Z Z' k l hk
  let g := k.left
  let g' := l.left ≫ g
  have hg : R g := (Sieve.overEquiv_symm_iff R k).mp hk
  have hg' : R g' := R.downward_closed hg l.left
  let e := overHomEqIso (g ≫ h) (Over.w k).symm
  let e' := overHomEqIso (g' ≫ h) (Over.w (l ≫ k)).symm
  let klocal : (Over.mk (g' ≫ h) : Over U) ⟶ Over.mk (g ≫ h) :=
    Over.homMk l.left (by dsimp [g']; simp [Category.assoc])
  have hdiag : l ≫ e.hom = e'.hom ≫ klocal := by
    apply Over.OverMorphism.ext
    change (l.left ≫ 𝟙 Z.left) = 𝟙 Z'.left ≫ l.left
    simp
  have hx := obj_eq_of_isHomLift B S hS f (g ≫ h) (fs g hg)
  have hx' := obj_eq_of_isHomLift B S hS f (g' ≫ h) (fs g' hg')
  obtain ⟨χ₀, hχ₀, hcomp₀⟩ := hcompat g hg l.left
  have hloc := pairIsoClassOfHom_restrict B S hS f c 𝒳.2 𝒴.2 hF (g ≫ h) l.left y
    ⟨xs g hg, hx⟩ ⟨xs g' hg', hx'⟩ χ₀ hχ₀ (fs g hg) (hfs g hg) (fs g' hg') (hfs g' hg') hcomp₀
  have hmap : P.map l.op (P.map e.hom.op
        (pairIsoClassOfHom B S hS f c 𝒳.2 𝒴.2 hF (g ≫ h) y ⟨xs g hg, hx⟩
          (fs g hg) (hfs g hg))) =
      P.map e'.hom.op
        (pairIsoClassOfHom B S hS f c 𝒳.2 𝒴.2 hF (g' ≫ h) y ⟨xs g' hg', hx'⟩
          (fs g' hg') (hfs g' hg')) := by
    calc
      P.map l.op (P.map e.hom.op
          (pairIsoClassOfHom B S hS f c 𝒳.2 𝒴.2 hF (g ≫ h) y ⟨xs g hg, hx⟩
            (fs g hg) (hfs g hg))) =
          P.map (e'.hom ≫ klocal).op
            (pairIsoClassOfHom B S hS f c 𝒳.2 𝒴.2 hF (g ≫ h) y ⟨xs g hg, hx⟩
              (fs g hg) (hfs g hg)) := by
        rw [← hdiag]
        simp only [op_comp, Functor.map_comp, types_comp_apply]
      _ = P.map e'.hom.op
            (pairIsoClassOfHom B S hS f c 𝒳.2 𝒴.2 hF (g' ≫ h) y ⟨xs g' hg', hx'⟩
              (fs g' hg') (hfs g' hg')) := by
        simp only [op_comp, Functor.map_comp, types_comp_apply]
        exact congrArg (P.map e'.hom.op) hloc
  simpa [pairIsoClassFamily, Category.assoc] using hmap.symm

/-- If the restriction along `g` of the section attached to `β₀ : F(x₀) ⟶ y` is the section
attached to `β : F(x) ⟶ y`, then `β` factors as `β₀` precomposed with a lift of `g`. -/
private lemma exists_isHomLift_of_pairIsoClassOfHom_restrict
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (h𝒳 : 𝒳.val.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.val.p.IsFiberedInGroupoids)
    (hF : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p)
    {U V W : AlgebraicGeometry.BigFppfOver B S hS} (h : V ⟶ U) (g : W ⟶ V)
    (y : 𝒴.val.p.Fiber U) (x₀ : 𝒳.val.p.Fiber V) (x : 𝒳.val.p.Fiber W)
    (β₀ : (CatFiberedInGroupoids.homFunctor f).obj x₀.1 ⟶ y.1)
    (hβ₀ : 𝒴.val.p.IsHomLift h β₀)
    (β : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ y.1)
    (hβ : 𝒴.val.p.IsHomLift (g ≫ h) β)
    (heq : (PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
      𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)).map
        ((Over.homMk g (by rfl) : (Over.mk (g ≫ h) : Over U) ⟶ Over.mk h).op)
        (pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF h y x₀ β₀ hβ₀) =
      pairIsoClassOfHom B S hS f c h𝒳 h𝒴 hF (g ≫ h) y x β hβ) :
    ∃ χ : x.1 ⟶ x₀.1, 𝒳.val.p.IsHomLift g χ ∧
      (CatFiberedInGroupoids.homFunctor f).map χ ≫ β₀ = β := by
  let F := CatFiberedInGroupoids.homFunctor f
  obtain ⟨z₀, χ, hχ⟩ := h𝒳.exists_lift g x₀.1 x₀.2
  let z : 𝒳.val.p.Fiber W := ⟨z₀, CategoryTheory.IsHomLift.domain_eq 𝒳.val.p g χ⟩
  have hrest := pairIsoClassOfHom_restrict B S hS f c h𝒳 h𝒴 hF h g y
    x₀ z χ hχ β₀ hβ₀ (F.map χ ≫ β₀) (by infer_instance) rfl
  obtain ⟨e, heLift, he⟩ := (pairIsoClassOfHom_eq_iff B S hS f c h𝒳 h𝒴 hF
    (g ≫ h) y z x (F.map χ ≫ β₀) (by infer_instance) β hβ).mp (hrest.symm.trans heq)
  let : IsGroupoid (𝒳.val.p.Fiber W) := h𝒳.fiber_isGroupoid W
  let eF : z ⟶ x := CategoryTheory.Functor.Fiber.homMk 𝒳.val.p W e
  let eIso : z ≅ x := asIso eF
  have heUnderlying : CategoryTheory.Functor.Fiber.fiberInclusion.map eIso.hom = e :=
    CategoryTheory.Functor.Fiber.fiberInclusion_homMk 𝒳.val.p W e
  let einv := CategoryTheory.Functor.Fiber.fiberInclusion.map eIso.inv
  refine ⟨einv ≫ χ, ?_, ?_⟩
  · let : 𝒳.val.p.IsHomLift (𝟙 W) einv := eIso.inv.2
    infer_instance
  · calc
      F.map (einv ≫ χ) ≫ β₀ = F.map einv ≫ (F.map χ ≫ β₀) := by
        simp [Functor.map_comp, Category.assoc]
      _ = F.map einv ≫ (F.map e ≫ β) :=
        congrArg (fun t => F.map einv ≫ t) he.symm
      _ = β := by
        have hcancel : F.map einv ≫ F.map e = 𝟙 _ := by
          rw [← Functor.map_comp, ← heUnderlying, ← Functor.map_comp]
          simp [eIso, CategoryTheory.Functor.Fiber.fiberInclusion]
        rw [← Category.assoc, hcancel]
        simp

/-- Gluing for the pair-class presheaf: a family of morphisms `F(x_g) ⟶ y` over the arrows of a
covering sieve, compatible along lifts, comes from a single morphism `F(x₀) ⟶ y`, as soon as
the pair-class presheaves are algebraic spaces. -/
private lemma exists_glue_of_compatible
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (hpair : ∀ (U : AlgebraicGeometry.BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      AlgebraicGeometry.IsAlgebraicSpacePairIsoClassPresheaf B S hS f c U y)
    (y : 𝒴.val.obj) {V : AlgebraicGeometry.BigFppfOver B S hS} (h : V ⟶ 𝒴.val.p.obj y)
    {R : Sieve V} (hR : R ∈ AlgebraicGeometry.BigFppfOver.topology B S hS V)
    (xs : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V), R g → 𝒳.val.obj)
    (fs : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g),
      (CatFiberedInGroupoids.homFunctor f).obj (xs g hg) ⟶ y)
    (hfs : ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g),
      𝒴.val.p.IsHomLift (g ≫ h) (fs g hg))
    (hcompat : ∀ ⦃W W' : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V) (hg : R g)
      (k : W' ⟶ W), ∃ χ : xs (k ≫ g) (R.downward_closed hg k) ⟶ xs g hg,
        𝒳.val.p.IsHomLift k χ ∧ (CatFiberedInGroupoids.homFunctor f).map χ ≫ fs g hg =
          fs (k ≫ g) (R.downward_closed hg k)) :
    ∃ (x₀ : 𝒳.val.obj) (β₀ : (CatFiberedInGroupoids.homFunctor f).obj x₀ ⟶ y),
      𝒴.val.p.IsHomLift h β₀ ∧ ∀ ⦃W : AlgebraicGeometry.BigFppfOver B S hS⦄ (g : W ⟶ V)
        (hg : R g), ∃ χ : xs g hg ⟶ x₀, 𝒳.val.p.IsHomLift g χ ∧
          (CatFiberedInGroupoids.homFunctor f).map χ ≫ β₀ = fs g hg := by
  let hF := CatFiberedInGroupoids.homFunctor_comp_p f
  let U := 𝒴.val.p.obj y
  let yF : 𝒴.val.p.Fiber U := ⟨y, rfl⟩
  let P := PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c yF 𝒳.2 𝒴.2 hF
  let A : Over U := Over.mk h
  let R' := (Sieve.overEquiv A).symm R
  have hRS := isSheafFor_overEquiv_symm B S hS h
    (pairIsoClass_isSheaf B S hS f c U yF (hpair U yF)) hR
  let sec := pairIsoClassFamily B S hS f c yF h R xs fs hfs
  have hsec : sec.Compatible := pairIsoClassFamily_compatible B S hS f c yF h R xs fs hfs hcompat
  let a := hRS.amalgamate sec hsec
  have ha : sec.IsAmalgamation a := hRS.isAmalgamation hsec
  obtain ⟨x₀, β₀, hβ₀, hclass⟩ := pairIsoClassOfHom_surjective
    B S hS f c 𝒳.2 𝒴.2 hF h yF a
  refine ⟨x₀.1, β₀, hβ₀, ?_⟩
  intro W g hg
  let k : (Over.mk (g ≫ h) : Over U) ⟶ A := Over.homMk g (by rfl)
  have hk : R' k := (Sieve.overEquiv_symm_iff R k).mpr hg
  have hx := obj_eq_of_isHomLift B S hS f (g ≫ h) (fs g hg)
  refine exists_isHomLift_of_pairIsoClassOfHom_restrict B S hS f c 𝒳.2 𝒴.2 hF h g yF
    x₀ ⟨xs g hg, hx⟩ β₀ hβ₀ (fs g hg) (hfs g hg) ?_
  calc
    P.map k.op (pairIsoClassOfHom B S hS f c 𝒳.2 𝒴.2 hF h yF x₀ β₀ hβ₀) =
        P.map k.op a := congrArg (P.map k.op) hclass
    _ = sec k hk := ha k hk
    _ = pairIsoClassOfHom B S hS f c 𝒳.2 𝒴.2 hF (g ≫ h) yF
          ⟨xs g hg, hx⟩ (fs g hg) (hfs g hg) := by
      change P.map (𝟙 (Over.mk (g ≫ h))).op _ = _
      rw [op_id, P.map_id]
      rfl

/-- **Stacks 05UN, the stack-in-groupoids clause.** A category fibred in groupoids over the big
fppf site of `S` admitting a 1-morphism representable by algebraic spaces into a stack in
groupoids is itself a stack in groupoids.

This is the source's own proof of that clause: the criterion of Stacks 02ZY turns
representability by algebraic spaces into the faithfulness and sheaf hypotheses of
Stacks 0CKJ. -/
@[stacks 05UN "the stack-in-groupoids clause"]
theorem isStack_of_isRepresentableByAlgebraicSpaces
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (h𝒴 : 𝒴.val.p.IsStack (AlgebraicGeometry.BigFppfOver.topology B S hS)) :
    𝒳.val.p.IsStack (AlgebraicGeometry.BigFppfOver.topology B S hS) := by
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let c := CategoryTheory.Functor.chosenPullbacks 𝒴.val.p
  have hcrit :=
    (AlgebraicGeometry.isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS f c).mp hf
  have hfaith : ∀ U : AlgebraicGeometry.BigFppfOver B S hS,
      (CategoryTheory.Functor.Fiber.fiberInclusion
        (p := 𝒳.val.p) (S := U) ⋙
        CatFiberedInGroupoids.homFunctor f).Faithful := by
    intro U
    have : (CategoryTheory.Functor.Fiber.mapOfComp
        𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f)
        (CatFiberedInGroupoids.homFunctor_comp_p f) U).Faithful := hcrit.1 U
    rw [← CategoryTheory.Functor.Fiber.mapOfComp_comp_fiberInclusion
      (𝒳.val.p) 𝒴.val.p (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f) U]
    infer_instance
  refine CategoryTheory.Functor.isStack_of_faithful_of_isSheaf
    𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f) h𝒴 hfaith ?_ ?_
  · intro y V h R hR x x' β β' hβ hβ' hloc
    exact exists_vertical_of_locally_eq B S hS f c hcrit.2 y h hR β β' hβ hβ' hloc
  · intro y V h R hR xs fs hfs hcompat
    exact exists_glue_of_compatible B S hS f c hcrit.2 y h hR xs fs hfs hcompat

/-- **Stacks 0CKY.** Let `𝒳 ⟶ 𝒵` and `𝒴 ⟶ 𝒵` be 1-morphisms of categories fibred in groupoids
over the big fppf site of `S`. If `𝒳 ⟶ 𝒵` is representable by algebraic spaces and `𝒴` is a
stack in groupoids, then the 2-fibre product `𝒳 ×_𝒵 𝒴` is a stack in groupoids. -/
@[stacks 0CKY]
theorem isStack_of_isTwoFibreProduct
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵)
    (P : Bicategory.TwoCommSq f g)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (h𝒴 : 𝒴.val.p.IsStack (AlgebraicGeometry.BigFppfOver.topology B S hS)) :
    P.pt.val.p.IsStack (AlgebraicGeometry.BigFppfOver.topology B S hS) :=
  isStack_of_isRepresentableByAlgebraicSpaces B S hS P.snd
    (isRepresentableByAlgebraicSpaces_baseChange.{u, v, w} B S hS 𝒳 𝒵 𝒴 f g
      P.swap (Bicategory.isTwoFibreProduct_swap hP) hf) h𝒴

end AlgebraicGeometry.Stack

end
