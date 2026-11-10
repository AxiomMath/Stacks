module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidTransport
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise

/-!
# Algebraicity is invariant under equivalence over the site

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳`, `𝒴` be categories over the big
fppf site of `S` which are equivalent as categories over that site. Then `𝒳` is an algebraic
stack if and only if `𝒴` is, and `𝒳` is a Deligne-Mumford stack if and only if `𝒴` is.

As a consequence, the final object of the 2-category of categories over the site is an algebraic
stack, and the product `𝒳 × 𝒴` of two algebraic stacks over `S`, the 2-fibre product over that
final object, is an algebraic stack and is a product in the 2-category of algebraic stacks over
`S`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.terminalStack`: the final object of the 2-category of
  algebraic stacks over `S`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.toTerminalStack`: the structure 1-morphism of an
  algebraic stack to the final object.
* `AlgebraicGeometry.Stack.AlgebraicStacks.productSquare`: the canonical square of the cospan of
  those two structure 1-morphisms, read in the 2-category of algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.product`: its apex, the product `𝒳 × 𝒴` as an object of
  the 2-category of algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_iff_of_equivalence`: two categories over the site
  which are equivalent over the site are algebraic stacks at the same time.
* `AlgebraicGeometry.Stack.isDeligneMumfordStack_iff_of_equivalence`: two categories over the
  site which are equivalent over the site are Deligne-Mumford stacks at the same time.
* `AlgebraicGeometry.Stack.isAlgebraicStack_iff_of_isEquivalence`: the same for algebraic stacks,
  with the equivalence given as a single 1-morphism over the site whose underlying functor is an
  equivalence.
* `AlgebraicGeometry.Stack.isAlgebraicStack_terminal`: the final object of the 2-category of
  categories over the site is an algebraic stack.
* `AlgebraicGeometry.Stack.isAlgebraicStack_product`: the product of two algebraic stacks over `S`
  is an algebraic stack.
* `AlgebraicGeometry.Stack.AlgebraicStacks.product_val`: the apex of the product square is the
  product of the underlying categories fibred in groupoids.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_productSquare`: the product of two
  algebraic stacks over `S` is a product in the 2-category of algebraic stacks over `S`.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04TE](https://stacks.math.columbia.edu/tag/04TE)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v t v₁ t₁ w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The unit of an equivalence `e` over the site, whiskered by a 1-morphism `f` into its source:
an isomorphism `f ≅ (f ⋙ e.functor) ⋙ e.inverse` of 1-morphisms over the site. -/
noncomputable def whiskerUnitIso
    {𝒳 𝒴 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳 𝒴)
    {𝒵 : BasedCategory.{v₁, t₁} (BigFppfOver B S hS)} (f : 𝒵 ⥤ᵇ 𝒳) :
    BasedFunctor.comp (BasedFunctor.id 𝒵) f ≅
      BasedFunctor.comp (BasedFunctor.comp f e.functor) e.inverse :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft f.toFunctor
      (BasedFunctor.toFunctorIso e.functor e.inverse e.unitIso).symm)
    (fun a => e.unitIso.inv.isHomLift (f.w_obj a))

/-- A category over the big fppf site of `S` equivalent over that site to an algebraic stack is an
algebraic stack. -/
theorem isAlgebraicStack_of_equivalence
    {𝒳 𝒴 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳 𝒴)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳) :
    IsAlgebraicStack.{u, w} B S hS 𝒴 := by
  obtain ⟨hfib, hst, hdiag, U, f, -, hprops⟩ := h𝒳
  have hfib' : 𝒴.p.IsFiberedInGroupoids :=
    (BasedCategory.isFiberedInGroupoids_iff_of_equivalence e).1 hfib
  have hst' : 𝒴.p.IsStack (BigFppfOver.topology B S hS) :=
    (BasedCategory.isStack_iff_of_equivalence e (BigFppfOver.topology B S hS)).1 hst.1
  have hinv : Functor.IsEquivalence e.inverse.toFunctor :=
    e.symm.equiv.isEquivalence_functor
  have hidU : Functor.IsEquivalence (BasedFunctor.id (schemeFibredCategory B S hS U).val).toFunctor
    := inferInstanceAs (Functor.IsEquivalence (𝟭 (schemeFibredCategory B S hS U).val.obj))
  have h₃ : IsRepresentableFromSchemes B S hS (CatFiberedInGroupoids.mk 𝒳 hfib) :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS
        (CatFiberedInGroupoids.mk 𝒳 hfib)).1
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
        (CatFiberedInGroupoids.mk 𝒳 hfib)).1 hdiag)
  have h₃' : IsRepresentableFromSchemes B S hS (CatFiberedInGroupoids.mk 𝒴 hfib') := fun V x ↦
    (isRepresentableByAlgebraicSpaces_iff_of_equivalence_target B S hS
      (𝒳 := schemeFibredCategory B S hS V) (𝒴' := CatFiberedInGroupoids.mk 𝒴 hfib')
      (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
      (BasedFunctor.comp x e.inverse) x e.inverse (Iso.refl _)).1
      (h₃ V (BasedFunctor.comp x e.inverse))
  refine ⟨hfib', ⟨hst', hst'.isStackInGroupoids hfib'⟩,
    (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
        (CatFiberedInGroupoids.mk 𝒴 hfib')).2
      ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS
        (CatFiberedInGroupoids.mk 𝒴 hfib')).2 h₃'),
    U, BasedFunctor.comp f e.functor, h₃' U (BasedFunctor.comp f e.functor),
    fun V y hy F hF hE => ⟨?_, ?_⟩⟩
  · exact relativeProperty_of_equivalences B S hS (Space.surjectiveMorphismProperty B S hS)
      (𝒳' := schemeFibredCategory B S hS U) (𝒴' := CatFiberedInGroupoids.mk 𝒴 hfib')
      (𝒳 := schemeFibredCategory B S hS U) (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
      (BasedFunctor.comp f e.functor) f (BasedFunctor.id _) e.inverse
      (whiskerUnitIso B S hS e f)
      (fun V y hy F hF h => (hprops V y hy F hF h).1) V y hy F hF hE
  · exact relativeProperty_of_equivalences B S hS (Space.smoothMorphismProperty B S hS)
      (𝒳' := schemeFibredCategory B S hS U) (𝒴' := CatFiberedInGroupoids.mk 𝒴 hfib')
      (𝒳 := schemeFibredCategory B S hS U) (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
      (BasedFunctor.comp f e.functor) f (BasedFunctor.id _) e.inverse
      (whiskerUnitIso B S hS e f)
      (fun V y hy F hF h => (hprops V y hy F hF h).2) V y hy F hF hE

/-- Two categories over the big fppf site of `S` which are equivalent as categories over that
site are algebraic stacks at the same time. -/
@[stacks 03YQ "algebraic_stack_iff_of_equivalence"]
theorem isAlgebraicStack_iff_of_equivalence
    {𝒳 𝒴 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳 𝒴) :
    IsAlgebraicStack.{u, w} B S hS 𝒳 ↔ IsAlgebraicStack.{u, w} B S hS 𝒴 :=
  ⟨isAlgebraicStack_of_equivalence.{u, v, t, w} B S hS e,
    isAlgebraicStack_of_equivalence.{u, v, t, w} B S hS e.symm⟩

/-- A category over the big fppf site of `S` equivalent over that site to a Deligne-Mumford stack
is a Deligne-Mumford stack. -/
theorem isDeligneMumfordStack_of_equivalence
    {𝒳 𝒴 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳 𝒴)
    (h𝒳 : IsDeligneMumfordStack.{u, w} B S hS 𝒳) :
    IsDeligneMumfordStack.{u, w} B S hS 𝒴 := by
  obtain ⟨halg, hfib, U, f, hrep, hprops⟩ := h𝒳
  have hfib' : 𝒴.p.IsFiberedInGroupoids :=
    (BasedCategory.isFiberedInGroupoids_iff_of_equivalence e).1 hfib
  have hinv : Functor.IsEquivalence e.inverse.toFunctor :=
    e.symm.equiv.isEquivalence_functor
  have hidU : Functor.IsEquivalence (BasedFunctor.id (schemeFibredCategory B S hS U).val).toFunctor
    := inferInstanceAs (Functor.IsEquivalence (𝟭 (schemeFibredCategory B S hS U).val.obj))
  have hrep' : IsRepresentableByAlgebraicSpaces B S hS
      (BasedFunctor.comp f.hom e.functor) :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalence_target B S hS
      (𝒳 := schemeFibredCategory B S hS U)
      (𝒴' := CatFiberedInGroupoids.mk 𝒴 hfib')
      (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
      f.hom (BasedFunctor.comp f.hom e.functor) e.inverse
      (whiskerUnitIso B S hS e f.hom)).1 hrep
  refine ⟨isAlgebraicStack_of_equivalence.{u, u, u + 1, w} B S hS e halg, hfib',
    U, Bicategory.InducedBicategory.mkHom (BasedFunctor.comp f.hom e.functor), hrep',
    fun V y hy F hF hE => ⟨?_, ?_⟩⟩
  · exact relativeProperty_of_equivalences B S hS (Space.surjectiveMorphismProperty B S hS)
      (𝒳' := schemeFibredCategory B S hS U) (𝒴' := CatFiberedInGroupoids.mk 𝒴 hfib')
      (𝒳 := schemeFibredCategory B S hS U) (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
      (BasedFunctor.comp f.hom e.functor) f.hom (BasedFunctor.id _) e.inverse
      (whiskerUnitIso B S hS e f.hom)
      (fun V y hy F hF h => (hprops V y hy F hF h).1) V y hy F hF hE
  · exact relativeProperty_of_equivalences B S hS (Space.etaleMorphisms B S hS)
      (𝒳' := schemeFibredCategory B S hS U) (𝒴' := CatFiberedInGroupoids.mk 𝒴 hfib')
      (𝒳 := schemeFibredCategory B S hS U) (𝒴 := CatFiberedInGroupoids.mk 𝒳 hfib)
      (BasedFunctor.comp f.hom e.functor) f.hom (BasedFunctor.id _) e.inverse
      (whiskerUnitIso B S hS e f.hom)
      (fun V y hy F hF h => (hprops V y hy F hF h).2) V y hy F hF hE

/-- Two categories over the big fppf site of `S` which are equivalent as categories over that
site are Deligne-Mumford stacks at the same time. -/
@[stacks 03YQ "deligne_mumford_iff_of_equivalence"]
theorem isDeligneMumfordStack_iff_of_equivalence
    {𝒳 𝒴 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳 𝒴) :
    IsDeligneMumfordStack.{u, w} B S hS 𝒳 ↔ IsDeligneMumfordStack.{u, w} B S hS 𝒴 :=
  ⟨isDeligneMumfordStack_of_equivalence.{u, w} B S hS e,
    isDeligneMumfordStack_of_equivalence.{u, w} B S hS e.symm⟩

/-- A 1-morphism `a : 𝒳 ⥤ᵇ 𝒴` of categories fibred in groupoids over the big fppf site of `S`
whose underlying functor is an equivalence of categories exhibits `𝒳` and `𝒴` as algebraic stacks
at the same time. -/
theorem isAlgebraicStack_iff_of_isEquivalence
    {𝒳 𝒴 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (a : 𝒳 ⥤ᵇ 𝒴) (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (ha : Functor.IsEquivalence a.toFunctor) :
    IsAlgebraicStack.{u, w} B S hS 𝒳 ↔ IsAlgebraicStack.{u, w} B S hS 𝒴 := by
  obtain ⟨F, hF, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒳.p 𝒴.p h𝒳 h𝒴 a.toFunctor a.w ha
  exact isAlgebraicStack_iff_of_equivalence.{u, v, t, w} B S hS
    { functor := a
      inverse := ⟨F, hF⟩
      unitIso := BasedNatIso.mkNatIso η hη
      counitIso := BasedNatIso.mkNatIso ε hε }

/-- The final object of the 2-category of categories over the big fppf site of `S`, the identity
functor of the site, is an algebraic stack. -/
theorem isAlgebraicStack_terminal :
    IsAlgebraicStack.{u, w} B S hS (BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS))) := by
  classical
  set T : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS)) with hT
  have hterm : Limits.IsTerminal T := Over.mkIdTerminal
  refine isAlgebraicStack_of_equivalence.{u, u, u + 1, w} B S hS ?_
    (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS T)
  exact
    { functor := ⟨(Over.equivalenceOfIsTerminal hterm).functor, rfl⟩
      inverse := ⟨(Over.equivalenceOfIsTerminal hterm).inverse, rfl⟩
      unitIso := BasedNatIso.mkNatIso (Over.equivalenceOfIsTerminal hterm).unitIso.symm (by
        intro a
        change (Over.forget T).IsHomLift (𝟙 a.left) _
        apply CategoryTheory.IsHomLift.of_fac' _ _ _ rfl rfl
        simp only [Over.equivalenceOfIsTerminal, Functor.id_obj, Functor.comp_obj,
          Over.forget_obj, Over.mk_left, Iso.symm_hom, eqToHom_refl]
        rfl)
      counitIso := BasedNatIso.mkNatIso (Over.equivalenceOfIsTerminal hterm).counitIso (by
        intro a
        apply CategoryTheory.IsHomLift.of_fac' _ _ _ rfl rfl
        simp only [Over.equivalenceOfIsTerminal, Functor.id_obj, Functor.comp_obj,
          Over.forget_obj, Over.mk_left, eqToHom_refl]
        rfl) }

/-- The product `CategoryTheory.CatFiberedInGroupoids.product 𝒳 𝒴` of two algebraic stacks over
`S` is an algebraic stack. -/
theorem isAlgebraicStack_product
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val) :
    IsAlgebraicStack.{u, w} B S hS (CatFiberedInGroupoids.product 𝒳 𝒴).val := by
  obtain ⟨hTfib, hTst, hTdiag, hTatlas⟩ := isAlgebraicStack_terminal.{u, w} B S hS
  exact isAlgebraicStack_twoFibreProduct.{u, w} B S hS 𝒳.val 𝒴.val
    (BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
    ⟨𝒳.val.p, Functor.comp_id 𝒳.val.p⟩ ⟨𝒴.val.p, Functor.comp_id 𝒴.val.p⟩
    hTst hTdiag h𝒳 h𝒴

namespace AlgebraicStacks

/-- The final object of the 2-category of algebraic stacks over `S`: the big fppf site of `S`
with the identity as structure functor. -/
def terminalStack : AlgebraicStacks.{u, w} B S hS :=
  ⟨terminalCFG B S hS, isAlgebraicStack_terminal.{u, w} B S hS⟩

/-- The structure 1-morphism of an algebraic stack over `S` to the final object
`AlgebraicGeometry.Stack.AlgebraicStacks.terminalStack`, as a 1-morphism of the 2-category of
algebraic stacks. -/
def toTerminalStack (𝒳 : AlgebraicStacks.{u, w} B S hS) : 𝒳 ⟶ terminalStack B S hS :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳.val))

/-- The canonical square over the cospan of structure 1-morphisms of two algebraic stacks over `S`
to the final object, read in the 2-category of algebraic stacks. -/
def productSquare (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) :
    Bicategory.TwoCommSq (toTerminalStack B S hS 𝒳) (toTerminalStack B S hS 𝒴) :=
  twoFibreProductSquare B S hS (toTerminalStack B S hS 𝒳) (toTerminalStack B S hS 𝒴)

/-- The product `𝒳 × 𝒴` of two algebraic stacks over `S`, as an object of the 2-category of
algebraic stacks: the apex of `AlgebraicGeometry.Stack.AlgebraicStacks.productSquare`. -/
def product (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) : AlgebraicStacks.{u, w} B S hS :=
  (productSquare B S hS 𝒳 𝒴).pt

/-- The apex of `AlgebraicGeometry.Stack.AlgebraicStacks.productSquare` is the product of the
underlying categories fibred in groupoids. -/
theorem product_val (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) :
    (product B S hS 𝒳 𝒴).val = CatFiberedInGroupoids.product 𝒳.val 𝒴.val :=
  rfl

/-- The product `𝒳 ×_{(Sch/S)_fppf} 𝒴` of two algebraic stacks over `S` is a product in the
2-category of algebraic stacks over `S`: the canonical square
`AlgebraicGeometry.Stack.AlgebraicStacks.productSquare` over the cospan of structure 1-morphisms
to the final object is a 2-fibre product in that 2-category. -/
@[stacks 04TE]
noncomputable def isTwoFibreProduct_productSquare (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) :
    Bicategory.IsTwoFibreProduct (productSquare B S hS 𝒳 𝒴) :=
  isTwoFibreProduct_twoFibreProductSquare B S hS (toTerminalStack B S hS 𝒳)
    (toTerminalStack B S hS 𝒴)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
