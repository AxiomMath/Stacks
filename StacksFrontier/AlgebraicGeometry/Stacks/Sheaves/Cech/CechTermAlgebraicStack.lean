module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.CechNerveStackProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# The terms of the relative Čech nerve of a 1-morphism of algebraic stacks are algebraic

Let `c : 𝒰 ⟶ 𝒳` be a `1`-morphism of algebraic stacks over `S`. The degree `n` term of its
relative Čech nerve is the category `Stacks.RelativeCech.Tuple 𝒳.p (homFunctor c) n` of
`n + 1` objects of `𝒰` over a common object of `𝒳`, fibred over the base by the projection to
`𝒳` followed by the structure functor of `𝒳`. It is an algebraic stack: in degree `0` it is
equivalent to `𝒰` and in degree `n + 1` to the 2-fibre product `𝒰 ×_𝒳 𝒰ₙ`. When `c` is smooth,
so is the projection of each term to `𝒳`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.cechTerm`: the degree `n` term, as an algebraic stack
  over `S` whose structure functor is literally `Tuple.projection ⋙ 𝒳.val.val.p`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.cechProjection`: its projection to `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isAlgebraicStack_cechTermBased`: each term of the
  relative Čech nerve is an algebraic stack.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_cechProjection`: for `c` smooth, the
  projections of the relative Čech nerve are smooth.

## References

* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 06X3](https://stacks.math.columbia.edu/tag/06X3)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (c : 𝒰 ⟶ 𝒳)

/-- The degree `n` term of the relative Čech nerve of `c`, as a category over the big fppf site:
the category of tuples, fibred by the projection to `𝒳` followed by the structure functor. -/
abbrev cechTermBased (n : ℕ) : BasedCategory.{u, u + 1} (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
    (CatFiberedInGroupoids.homFunctor c.hom) n ⋙ 𝒳.val.val.p)

/-- The structure functor of the degree `n` term is fibred in groupoids. -/
theorem isFiberedInGroupoids_cechTermBased (n : ℕ) :
    (cechTermBased B S hS c n).p.IsFiberedInGroupoids :=
  Stacks.RelativeCech.tupleProjection_comp_isFiberedInGroupoids B S hS _ _ _
    𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      c.hom.hom.w) n

/-- In degree `0`, the tuple consisting of a single object of `𝒰` with the identity comparison:
a 1-morphism over the base from `𝒰` to the degree `0` term, strictly, since the target of that
tuple is the image of the object in `𝒳`. -/
def cechTermSingle : 𝒰.val.val ⥤ᵇ cechTermBased B S hS c 0 where
  toFunctor :=
    { obj := fun x =>
        { target := (CatFiberedInGroupoids.homFunctor c.hom).obj x
          source := fun _ => x
          comparison := fun _ => Iso.refl _
          comparison_lift := fun _ => IsHomLift.id rfl }
      map := fun {x y} k =>
        { target := (CatFiberedInGroupoids.homFunctor c.hom).map k
          source := fun _ => k
          comparison_naturality := fun _ => by simp }
      map_id := fun _ => Stacks.Cech.tupleHom_ext (CategoryTheory.Functor.map_id _ _) rfl
      map_comp := fun _ _ => Stacks.Cech.tupleHom_ext (CategoryTheory.Functor.map_comp _ _ _) rfl }
  w := c.hom.hom.w

/-- Reading off the unique coordinate undoes `cechTermSingle`. -/
theorem cechTermSingle_comp_coordinate :
    (cechTermSingle B S hS c).toFunctor ⋙
        Stacks.RelativeCech.Tuple.coordinate 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor c.hom) (0 : Fin 1) = 𝟭 _ :=
  rfl

/-- `cechTermSingle` is an equivalence of categories. -/
theorem isEquivalence_cechTermSingle :
    (cechTermSingle B S hS c).toFunctor.IsEquivalence := by
  have h0 := Stacks.RelativeCech.isEquivalence_coordinate_zero 𝒳.val.val.p
    (CatFiberedInGroupoids.homFunctor c.hom)
  have h1 : ((cechTermSingle B S hS c).toFunctor ⋙
      Stacks.RelativeCech.Tuple.coordinate 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor c.hom) (0 : Fin 1)).IsEquivalence := by
    rw [cechTermSingle_comp_coordinate]
    infer_instance
  exact @Functor.isEquivalence_of_comp_right _ _ _ _ _ _ _ _ h0 h1

/-- The 2-fibre product `𝒰 ×_𝒳 𝒰ₙ`, as a category over the base fibred by its canonical structure
functor. -/
abbrev cechTermFibreProductBased (n : ℕ) : BasedCategory.{u, u + 1} (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
    (CatFiberedInGroupoids.homFunctor c.hom ⋙ 𝒳.val.val.p)
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor c.hom) n ⋙ 𝒳.val.val.p)
    𝒳.val.val.p (CatFiberedInGroupoids.homFunctor c.hom)
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor c.hom) n))

/-- Prepending a coordinate is a 1-morphism over the base from `𝒰 ×_𝒳 𝒰ₙ` to `𝒰ₙ₊₁`. -/
def cechTermPrepend (n : ℕ) :
    cechTermFibreProductBased B S hS c n ⥤ᵇ cechTermBased B S hS c (n + 1) where
  toFunctor := Stacks.RelativeCech.fibreProductToNerve 𝒳.val.val.p
    (CatFiberedInGroupoids.homFunctor c.hom) n
  w := TwoFibreProductOver.snd_comp_eq

/-- **The terms of the relative Čech nerve of a 1-morphism of algebraic stacks are algebraic
stacks.** -/
theorem isAlgebraicStack_cechTermBased (n : ℕ) :
    IsAlgebraicStack.{u, w} B S hS (cechTermBased B S hS c n) := by
  induction n with
  | zero =>
    exact (isAlgebraicStack_iff_of_isEquivalence.{u, u, u + 1, w} B S hS
      (cechTermSingle B S hS c) 𝒰.val.isFiberedInGroupoids
      (isFiberedInGroupoids_cechTermBased B S hS c 0)
      (isEquivalence_cechTermSingle B S hS c)).1 𝒰.property
  | succ n ih =>
    obtain ⟨_, h𝒳stack, h𝒳diag, -⟩ := 𝒳.property
    have h𝒰 : IsAlgebraicStack.{u, w} B S hS
        (BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor c.hom ⋙ 𝒳.val.val.p)) := by
      rw [CatFiberedInGroupoids.homFunctor_comp_p]
      exact 𝒰.property
    have hFP : IsAlgebraicStack.{u, w} B S hS (cechTermFibreProductBased B S hS c n) :=
      isAlgebraicStack_twoFibreProduct B S hS
        (BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor c.hom ⋙ 𝒳.val.val.p))
        (cechTermBased B S hS c n) 𝒳.val.val
        ⟨CatFiberedInGroupoids.homFunctor c.hom, rfl⟩
        ⟨Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
          (CatFiberedInGroupoids.homFunctor c.hom) n, rfl⟩
        h𝒳stack h𝒳diag h𝒰 ih
    exact (isAlgebraicStack_iff_of_isEquivalence.{u, u, u + 1, w} B S hS
      (cechTermPrepend B S hS c n) hFP.1
      (isFiberedInGroupoids_cechTermBased B S hS c (n + 1))
      (Stacks.RelativeCech.isEquivalence_fibreProductToNerve _ _ n)).1 hFP

/-- The degree `n` term of the relative Čech nerve of `c`, as an algebraic stack over `S`. Its
structure functor is literally the projection to `𝒳` followed by the structure functor of `𝒳`. -/
abbrev cechTerm (n : ℕ) : AlgebraicStacks.{u, w} B S hS :=
  ⟨CatFiberedInGroupoids.mk (cechTermBased B S hS c n)
    (isFiberedInGroupoids_cechTermBased B S hS c n), isAlgebraicStack_cechTermBased B S hS c n⟩

/-- The projection of the degree `n` term of the relative Čech nerve of `c` to `𝒳`. -/
abbrev cechProjection (n : ℕ) : cechTerm B S hS c n ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor c.hom) n, rfl⟩)

/-- **Smoothness cancels against an equivalence on the left.** If `e ≫ φ` is smooth and the
functor underlying `e` is an equivalence, then `φ` is smooth. -/
theorem isSmooth_of_isEquivalence_comp {𝒜 𝒦 𝒲 : AlgebraicStacks.{u, w} B S hS}
    (e : 𝒜 ⟶ 𝒦) (φ : 𝒦 ⟶ 𝒲)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom))
    (heφ : AlgebraicStacks.IsSmooth B S hS (e ≫ φ)) : AlgebraicStacks.IsSmooth B S hS φ := by
  obtain ⟨F, hF, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒜.val.val.p 𝒦.val.val.p
      𝒜.val.isFiberedInGroupoids 𝒦.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor e.hom) (CatFiberedInGroupoids.homFunctor_comp_p e.hom) he
  let j : 𝒦 ⟶ 𝒜 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩)
  have hj : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor j.hom) :=
    (CategoryTheory.Equivalence.mk (CatFiberedInGroupoids.homFunctor e.hom) F η.symm
      ε).isEquivalence_inverse
  have hje : j ≫ e ≅ 𝟙 𝒦 :=
    Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
      (BasedNatIso.mkNatIso ε hε))
  exact AlgebraicStacks.isSmooth_of_twoIso B S hS
    ((Bicategory.associator j e φ).symm ≪≫ Bicategory.whiskerRightIso hje φ ≪≫
      Bicategory.leftUnitor φ)
    (AlgebraicStacks.isSmooth_comp B S hS j _
      (AlgebraicStacks.isSmooth_of_isEquivalence B S hS j hj) heφ)

/-- The source of `c`, refibred over the base by the strict presentation
`homFunctor c ⋙ 𝒳.val.val.p` of its structure functor. -/
abbrev strictSource : AlgebraicStacks.{u, w} B S hS :=
  ⟨CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor c.hom ⋙ 𝒳.val.val.p))
    (by rw [CatFiberedInGroupoids.homFunctor_comp_p]; exact 𝒰.val.isFiberedInGroupoids),
    AlgebraicGeometry.Stack.isAlgebraicStack_ofFunctor_homFunctor_comp B S hS c⟩

/-- `c`, out of the strict presentation of its source. -/
abbrev strictHom : strictSource B S hS c ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨c.hom.hom.toFunctor, rfl⟩)

/-- The identity functor, as a 1-morphism from the strict presentation of the source of `c` to
the source of `c`. -/
abbrev strictSourceEquiv : strictSource B S hS c ⟶ 𝒰 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨𝟭 _, (CatFiberedInGroupoids.homFunctor_comp_p c.hom).symm⟩)

/-- `c` out of the strict presentation of its source is smooth when `c` is. -/
theorem isSmooth_strictHom (hc : AlgebraicStacks.IsSmooth B S hS c) :
    AlgebraicStacks.IsSmooth B S hS (strictHom B S hS c) :=
  AlgebraicStacks.isSmooth_of_twoIso B S hS (Iso.refl _)
    (AlgebraicStacks.isSmooth_comp B S hS (strictSourceEquiv B S hS c) c
      (AlgebraicStacks.isSmooth_of_isEquivalence B S hS _
        (inferInstanceAs (𝟭 _).IsEquivalence)) hc)

/-- The 1-morphism `𝒰 ⟶ 𝒰₀` sending an object to the tuple it forms alone. -/
abbrev cechSingleHom : 𝒰 ⟶ cechTerm B S hS c 0 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (cechTermSingle B S hS c))

/-- The 1-morphism `𝒰 ×_𝒳 𝒰ₙ ⟶ 𝒰ₙ₊₁` prepending a coordinate. -/
abbrev cechPrependHom (n : ℕ) :
    twoFibreProductAlgebraicStack B S hS (strictHom B S hS c) (cechProjection B S hS c n) ⟶
      cechTerm B S hS c (n + 1) :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (cechTermPrepend B S hS c n))

/-- **The projections of the relative Čech nerve of a smooth 1-morphism are smooth.** -/
theorem isSmooth_cechProjection (hc : AlgebraicStacks.IsSmooth B S hS c) (n : ℕ) :
    AlgebraicStacks.IsSmooth B S hS (cechProjection B S hS c n) := by
  induction n with
  | zero =>
    exact isSmooth_of_isEquivalence_comp B S hS (cechSingleHom B S hS c) _
      (isEquivalence_cechTermSingle B S hS c) hc
  | succ n ih =>
    have hsnd : AlgebraicStacks.IsSmooth B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS (strictHom B S hS c)
          (cechProjection B S hS c n)).snd :=
      AlgebraicStacks.isSmooth_baseChange B S hS (strictHom B S hS c)
        (cechProjection B S hS c n)
        (twoFibreProductSquareAlgebraicStacks B S hS _ _).swap
        (Bicategory.isTwoFibreProduct_swap
          (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _))
        (isSmooth_strictHom B S hS c hc)
    have hcomp := AlgebraicStacks.isSmooth_comp B S hS _ _ hsnd ih
    have hcomp' : AlgebraicStacks.IsSmooth B S hS
        (cechPrependHom B S hS c n ≫ cechProjection B S hS c (n + 1)) := hcomp
    exact isSmooth_of_isEquivalence_comp B S hS (cechPrependHom B S hS c n) _
      (Stacks.RelativeCech.isEquivalence_fibreProductToNerve _ _ n) hcomp'

end AlgebraicGeometry.Stack.AlgebraicStacks

end
