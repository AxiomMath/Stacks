module

public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyEtaleEqualizerAffineCover
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStackAbsolute
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a quasi-compact and quasi-separated algebraic stack commutes with filtered colimits

Let `𝒳` be a quasi-compact and quasi-separated algebraic stack. **Stacks 0GQV** asserts that
`colim_i H^p(𝒳, F_i) ⟶ H^p(𝒳, colim_i F_i)` is an isomorphism for every filtered diagram of
abelian sheaves on `𝒳`, both in the fppf topology and in the étale topology. The proof checks the
four conditions of **Stacks 0GN4** for the collection of objects of the site lying over affine
schemes. Conditions (3) and (4) are about 2-fibre products that the source covers by an affine
scheme, and the quasi-compactness of those 2-fibre products is **Stacks 075S**.

The over-the-base statement of Stacks 075S,
`AlgebraicGeometry.Stack.isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProduct`, asks for
the base scheme `S` of the big fppf site to be quasi-separated, and so do the statements of
conditions (3) and (4) built on it,
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift`
and `AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift`. The
source asks nothing of a base scheme. This file reruns the same arguments with quasi-separatedness
of `𝒳` read absolutely, in the sense of **Stacks 050D** part (8), and Stacks 075S part (1) in its
absolute form, `AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactStack_absolute`,
which cancels the structure morphism to `Spec ℤ` as the source does. The result is Stacks 0GQV
under the source's own hypotheses.

## Main results

* `AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift_absolute` and
  `AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift_etale_absolute`:
  condition (2)(c) of **Stacks 0GMS** (condition (3) of Stacks 0GN4) for the fppf and the étale
  site of a quasi-separated algebraic stack.
* `AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift_absolute` and
  `AlgebraicGeometry.Stack`
  `.exists_fin_affineObjects_isLocallySurjective_equalizerLift_etale_absolute`:
  condition (4) of Stacks 0GN4 for the fppf and the étale site of a quasi-separated algebraic
  stack.
* `AlgebraicGeometry.Stack`
  `.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact_absolute`:
  **Stacks 0GQV**, first assertion: the fppf topology.
* `AlgebraicGeometry.Stack`
  `.isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompact_absolute`:
  **Stacks 0GQV**, second assertion: the étale topology.

## Implementation notes

The 2-fibre product of the 2-Yoneda 1-morphisms of two objects lying over affine schemes is shown
to be quasi-compact by Stacks 075S part (1) at the second 1-morphism, applied to the first, and
quasi-separated by **Stacks 050L** part (8) at the composite of the projection with the second
1-morphism; both 2-Yoneda 1-morphisms are quasi-separated by **Stacks 050N** part (8). The
2-fibre product of the two graphs of a parallel pair, which condition (4) is about, is then
quasi-compact by Stacks 075S part (1) again. Everything else is the argument of the over-the-base
statements, unchanged.

## References

* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] essentiallySmall_join hasSheafify_ab_join enoughInjectives_sheaf_join
  globalSections_additive_join

universe v₀ u₀

/-- Sheaves of sets on a site have coproducts over an index type in `Type`, built from the
colimits of the size of the join of the two universes of the site; the finite coproducts of
sheafified representables the conditions of Stacks 0GN4 speak of are formed with it. It is
anonymous because the files this one imports export declarations of the same name whose
`instance` attribute is local to them. -/
local instance {C : Type u₀} [Category.{v₀} C]
    (J : GrothendieckTopology C) {ι : Type} (A : ι → Sheaf J (Type max u₀ v₀)) :
    HasCoproduct A :=
  letI : HasColimitsOfSize.{max u₀ v₀, max u₀ v₀} (Sheaf J (Type max u₀ v₀)) :=
    Sheaf.instHasColimitsOfSize
  letI : HasColimitsOfSize.{0, 0} (Sheaf J (Type max u₀ v₀)) := hasColimitsOfSizeShrink _
  inferInstance

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section AffineQuadruple

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The 2-Yoneda 1-morphism of an object lying over an affine scheme, out of a quasi-separated
algebraic stack, is quasi-separated.**

**Stacks 050N** part (8): the source of the 1-morphism is
`AlgebraicGeometry.Stack.schemeStack` at an affine object on the nose, hence quasi-separated over
`S` by `AlgebraicGeometry.Stack.isQuasiSeparatedOver_schemeStack_of_isAffine`, and what the tag
asks of the relative diagonal of the structure morphism of the target is the second conjunct of
quasi-separatedness of `𝒳` over `S`, which **Stacks 050N** part (4) reads off absolute
quasi-separatedness of `𝒳`. Nothing is asked of `S`. -/
theorem isQuasiSeparated_objectMorphismAlgebraicStacks_of_isAffineObject
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    {y : 𝒳.val.val.obj} (hy : IsAffineObject B S hS 𝒳.val.val.p y) :
    AlgebraicStacks.IsQuasiSeparated.{u, w} B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y) :=
  AlgebraicStacks.isQuasiSeparated_of_isQuasiSeparatedOver B S hS
    (objectMorphismAlgebraicStacks B S hS 𝒳 y)
    (isQuasiSeparatedOver_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj y) hy)
    (AlgebraicStacks.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ 𝒳 h𝒳).2

/-- **The 2-fibre product of the 2-Yoneda 1-morphisms of two objects lying over affine schemes is
a quasi-compact algebraic stack *and* is quasi-separated**, for a quasi-separated algebraic stack.
Both conditions on `𝒳` and both conclusions are read absolutely, in the sense of **Stacks 050D**
part (8), and nothing is asked of the base scheme of the big fppf site.

The quasi-compact conjunct is **Stacks 075S** part (1) at the second 2-Yoneda 1-morphism, applied
to the first: quasi-compactness of a 1-morphism is Stacks 050U, the condition that every base
change of it by a quasi-compact algebraic stack be quasi-compact, and the slice at an affine object
is quasi-compact by `AlgebraicGeometry.Stack.isQuasiCompactStack_schemeStack_of_isAffine`. So the
only hypothesis consumed is absolute quasi-separatedness of `𝒳`; in particular absolute
quasi-separatedness of the two slices, which part (3) of the same tag would ask for, is not needed.

The quasi-separated conjunct is **Stacks 050L** part (8) at the composite
`𝒳_y ×_𝒳 𝒳_{y'} ⟶ 𝒳_{y'} ⟶ 𝒳`: the projection is a base change of the first 2-Yoneda
1-morphism (**Stacks 050F**) and both 2-Yoneda 1-morphisms are quasi-separated by
`AlgebraicGeometry.Stack.isQuasiSeparated_objectMorphismAlgebraicStacks_of_isAffineObject`, so the
composite is quasi-separated by **Stacks 050K** and carries absolute quasi-separatedness back from
`𝒳`.

That conjunct is the one condition (4) of Stacks 0GN4 needs and condition (3) does not:
condition (3) is discharged from the quasi-compact conjunct alone, but condition (4) base-changes
along a 1-morphism whose *target* is this 2-fibre product rather than `𝒳`, and Stacks 075S
part (1) asks for quasi-separatedness of the target. It is used in that way by
`AlgebraicGeometry.Stack.isQuasiCompactStack_equalizerTwoFibreProduct_absolute` below, and that
is why the conclusion has to be the absolute reading: the over-the-base one is not an input to
Stacks 075S part (1) in the form that asks nothing of `S`. -/
theorem isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProductAlgebraicStack_objMor
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    {y y' : 𝒳.val.val.obj} (hy : IsAffineObject B S hS 𝒳.val.val.p y)
    (hy' : IsAffineObject B S hS 𝒳.val.val.p y') :
    IsQuasiCompactStack.{u, w} B S hS
        (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')).val
        (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')).property ∧
      AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ
        (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')) :=
  ⟨isQuasiCompactMorphism_of_isQuasiCompactStack_absolute.{u, w} B S hS hZ
      (objectMorphismAlgebraicStacks B S hS 𝒳 y')
      (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj y') hy') h𝒳
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y))
      (objectMorphismAlgebraicStacks B S hS 𝒳 y)
      (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj y) hy),
    AlgebraicStacks.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
      ((twoFibreProductSquareAlgebraicStacks B S hS
          (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')).snd ≫
        objectMorphismAlgebraicStacks B S hS 𝒳 y') h𝒳
      (AlgebraicStacks.isQuasiSeparated_comp B S hS _ _
        (AlgebraicStacks.isQuasiSeparated_baseChange B S hS
          (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')
          (isQuasiSeparated_objectMorphismAlgebraicStacks_of_isAffineObject.{u, w}
            B S hS 𝒳 hZ h𝒳 hy))
        (isQuasiSeparated_objectMorphismAlgebraicStacks_of_isAffineObject.{u, w}
          B S hS 𝒳 hZ h𝒳 hy'))⟩

/-- **The 2-fibre product of the 2-Yoneda 1-morphisms of two objects lying over affine schemes is
a quasi-compact algebraic stack**, for a quasi-separated algebraic stack. This is the first
conjunct of
`AlgebraicGeometry.Stack`
`.isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProductAlgebraicStack_objMor`. -/
theorem isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism_absolute
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    {y y' : 𝒳.val.val.obj} (hy : IsAffineObject B S hS 𝒳.val.val.p y)
    (hy' : IsAffineObject B S hS 𝒳.val.val.p y') :
    IsQuasiCompactStack.{u, w} B S hS
        (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')).val
        (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
          (objectMorphismAlgebraicStacks B S hS 𝒳 y')).property :=
  (isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProductAlgebraicStack_objMor.{u, w}
    B S hS 𝒳 hZ h𝒳 hy hy').1

/-- **The 2-fibre product of the 2-Yoneda 1-morphisms of two objects lying over affine schemes is
quasi-separated**, for a quasi-separated algebraic stack, both read absolutely. This is the second
conjunct of
`AlgebraicGeometry.Stack`
`.isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProductAlgebraicStack_objMor`, and it
is the input condition (4) of Stacks 0GN4 needs in order to apply Stacks 075S part (1) to a
1-morphism whose target is that 2-fibre product. -/
theorem isAbsolutelyQuasiSeparated_twoFibreProductAlgebraicStack_objectMorphism
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    {y y' : 𝒳.val.val.obj} (hy : IsAffineObject B S hS 𝒳.val.val.p y)
    (hy' : IsAffineObject B S hS 𝒳.val.val.p y') :
    AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ
      (twoFibreProductAlgebraicStack B S hS (objectMorphismAlgebraicStacks B S hS 𝒳 y)
        (objectMorphismAlgebraicStacks B S hS 𝒳 y')) :=
  (isQuasiCompactStack_and_isAbsolutelyQuasiSeparated_twoFibreProductAlgebraicStack_objMor.{u, w}
    B S hS 𝒳 hZ h𝒳 hy hy').2

/-- **Condition (2)(c) of Stacks 0GMS for the fppf site of a quasi-separated algebraic stack**, in
the shape
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf` consumes as its
hypothesis `h_product`: for two objects `x`, `x'` of the site lying over affine schemes there is a
finite family of such objects, with a morphism to `x` and a morphism to `x'` from each, whose
sheafified representables jointly cover `h_x^# ⨯ h_{x'}^#`.

The family has one member, as in the source. It is the object the quadruple of
`AlgebraicGeometry.Stack.exists_quadruple_dominating` classifies, with the two morphisms that
quadruple classifies, and the covering assertion is
`AlgebraicGeometry.Stack`
`.isLocallySurjective_prodLift_fppfTopology_of_exists_quadruple_dominating_base`.
Quasi-compactness of the 2-fibre product, which is what produces the quadruple, is
`AlgebraicGeometry.Stack`
`.isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism_absolute`.

This checks hypothesis (2)(c) of Stacks 0GMS on this site: it applies the remark (whose
cases are formalized in `StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects`
and `…CoveringSetFromCoversTop`) and is not a statement of it, so it carries no
`@[stacks 0GMS]` attribute. -/
theorem exists_fin_affineObjects_isLocallySurjective_prodLift_absolute
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳) :
    ∀ U ∈ affineObjects B S hS 𝒳.val, ∀ U' ∈ affineObjects B S hS 𝒳.val,
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
            Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
              prod.lift ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (p i))
                ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (q i))) := by
  intro U hU U' hU'
  obtain ⟨Q, hQaff, hQ⟩ := exists_quadruple_dominating B S hS 𝒳
    (isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism_absolute B S hS 𝒳 hZ h𝒳
      hU hU')
  exact ⟨1, fun _ => quadObj B S hS 𝒳.val Q, fun _ => hQaff,
    fun _ => quadFst B S hS 𝒳.val Q, fun _ => quadSnd B S hS 𝒳.val Q,
    isLocallySurjective_prodLift_fppfTopology_of_exists_quadruple_dominating_base B S hS 𝒳.val
      Q hQ⟩

/-- **Stacks 0GQV in the fppf topology for a quasi-compact and quasi-separated algebraic stack,
from condition (4) of Stacks 0GN4 alone.**

This is
`AlgebraicGeometry.Stack`
`.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompactStack`
with its condition (3) discharged by
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift_absolute`.
Condition (4), the
corresponding assertion for the equalizer of two parallel morphisms, remains a hypothesis here
because the quadruple does not give it: the 2-fibre product it is about is not the one
of two 2-Yoneda 1-morphisms but the one of the two *graphs* of `a` and `b` over that one. It is
proved, for a quasi-separated stack, as
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift_absolute`
below, and discharging it turns this result into the full fppf assertion of Stacks 0GQV,
`AlgebraicGeometry.Stack`
`.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact_absolute`. -/
theorem isIso_colimit_post_rightDerived_globalSections_fppf_of_isAbsolutelyQuasiSeparated
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    (h_equalizer : ∀ {U U' : 𝒳.val.val.obj} (a b : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒳.val → U' ∈ affineObjects B S hS 𝒳.val →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map a)
              (g := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map b)
              ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (hp i))))
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (fppfTopology B S hS 𝒳.val) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (fppfTopology B S hS 𝒳.val) Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompactStack.{u, w} B S hS 𝒳 hqc
    (exists_fin_affineObjects_isLocallySurjective_prodLift_absolute B S hS 𝒳 hZ h𝒳) h_equalizer p F

section Topology

variable (τ : GrothendieckTopology B.Schemes)

/-- **Condition (2)(c) of Stacks 0GMS at an arbitrary topology of Stacks 06TP in which a
surjective smooth 1-morphism admits fibre lifts**, for a quasi-separated algebraic stack: for two
objects `x`, `x'` of the site lying over affine schemes there
is a finite family of such objects, with a morphism to `x` and a morphism to `x'` from each, whose
sheafified representables jointly cover `h_x^# ⨯ h_{x'}^#`.

The family has one member, as in the source. It is the object the quadruple of
`AlgebraicGeometry.Stack.exists_quadruple_dominating_associatedTopology` classifies, with the two
morphisms that quadruple classifies, and the covering assertion is
`AlgebraicGeometry.Stack`
`.isLocallySurjective_prodLift_associatedTopology_of_exists_quadruple_dominating_base`.
Quasi-compactness of the 2-fibre product, which is what produces the quadruple, is
`AlgebraicGeometry.Stack`
`.isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism_absolute`, and is
where quasi-separatedness enters, through **Stacks 075S** part (1) in its absolute form. -/
theorem exists_fin_affineObjects_isLocallySurjective_prodLift_associatedTopology_absolute
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    (h_lift : ∀ (𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒲),
      IsSurjective B S hS f → AlgebraicStacks.IsSmooth B S hS f →
      ∀ (U : BigFppfOver B S hS) (z : 𝒲.val.val.p.Fiber U),
        ∃ R ∈ τ.over (B.obj hS) U,
          ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
            ∃ (a : 𝒵.val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor f.hom).obj a ⟶ z.1),
              𝒲.val.val.p.IsHomLift k α) :
    ∀ U ∈ affineObjects B S hS 𝒳.val, ∀ U' ∈ affineObjects B S hS 𝒳.val,
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
            Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
              prod.lift
                ((Sheaf.sheafifiedYoneda
                  (associatedTopology B S hS 𝒳.val.val.p τ)).map (p i))
                ((Sheaf.sheafifiedYoneda
                  (associatedTopology B S hS 𝒳.val.val.p τ)).map (q i))) := by
  intro U hU U' hU'
  obtain ⟨Q, hQaff, hQ⟩ := exists_quadruple_dominating_associatedTopology B S hS 𝒳 τ
    (isQuasiCompactStack_twoFibreProductAlgebraicStack_objectMorphism_absolute B S hS 𝒳 hZ h𝒳
      hU hU')
    h_lift
  exact ⟨1, fun _ => quadObj B S hS 𝒳.val Q, fun _ => hQaff,
    fun _ => quadFst B S hS 𝒳.val Q, fun _ => quadSnd B S hS 𝒳.val Q,
    isLocallySurjective_prodLift_associatedTopology_of_exists_quadruple_dominating_base
      B S hS 𝒳.val τ Q hQ⟩

/-- **Condition (2)(c) of Stacks 0GMS for the étale site of a quasi-separated algebraic stack**,
in the shape
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale` consumes as its
hypothesis `h_product`: for two objects `x`, `x'` of the étale site lying over affine schemes
there is a finite family of such objects, with a morphism to `x` and a morphism to `x'` from each,
whose sheafified representables jointly cover `h_x^# ⨯ h_{x'}^#`.

This is
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_prodLift_associatedTopology_absolute`
at the big étale
topology, its fibre-lifting hypothesis discharged by **Stacks 06XH** part (2),
`AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`, which reads the fibre lifts of a
surjective smooth 1-morphism off an *étale* covering of the base. The affine smooth presentation
of **Stacks 04YC** is smooth and surjective, which is exactly what that tag asks for, so the
étale case needs nothing of the presentation beyond what the fppf case needs — in particular no
affine étale presentation of a quasi-compact algebraic stack. The family has one member, as in the
source.

This checks hypothesis (2)(c) of Stacks 0GMS on this site: it applies the remark (whose
cases are formalized in `StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects`
and `…CoveringSetFromCoversTop`) and is not a statement of it, so it carries no
`@[stacks 0GMS]` attribute. -/
theorem exists_fin_affineObjects_isLocallySurjective_prodLift_etale_absolute
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳) :
    ∀ U ∈ affineObjects B S hS 𝒳.val, ∀ U' ∈ affineObjects B S hS 𝒳.val,
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
            Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
              prod.lift
                ((Sheaf.sheafifiedYoneda
                  (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (p i))
                ((Sheaf.sheafifiedYoneda
                  (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (q i))) :=
  exists_fin_affineObjects_isLocallySurjective_prodLift_associatedTopology_absolute B S hS 𝒳
    (etaleTopology B) hZ h𝒳
    fun _ _ f hsurj hsm => exists_etaleCovering_fibre_lift B S hS f hsurj hsm

/-- **The second assertion of Stacks 0GQV, in the étale topology, for a quasi-compact and
quasi-separated algebraic stack, from condition (4) of Stacks 0GN4 alone.**

This is `AlgebraicGeometry.Stack`
`.isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompactStack`
with its condition (3) discharged by
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_prodLift_etale_absolute`. Condition
(4), the corresponding assertion for the equalizer of two parallel morphisms, is still assumed:
the 2-fibre product the source covers by an affine scheme in that case is the one of a single
1-morphism against the diagonal, not of two 2-Yoneda 1-morphisms, so the quadruple does not
discharge it, in this topology any more than in the fppf one. So this is not yet the full
second assertion of Stacks 0GQV. -/
theorem isIso_colimit_post_rightDerived_globalSections_etale_of_isAbsolutelyQuasiSeparated
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    (h_equalizer : ∀ {U U' : 𝒳.val.val.obj} (a b : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒳.val → U' ∈ affineObjects B S hS 𝒳.val →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map a)
              (g := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map b)
              ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda
                    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (hp i))))
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompactStack.{u, w} B S hS 𝒳 hqc
    (exists_fin_affineObjects_isLocallySurjective_prodLift_etale_absolute B S hS 𝒳 hZ h𝒳)
    h_equalizer p F


end Topology

/-- **Stacks 0GQV in the fppf topology for a quasi-compact and quasi-separated algebraic stack,
from one geometric statement.**

This is
`AlgebraicGeometry.Stack`
`.isIso_colimit_post_rightDerived_globalSections_fppf_of_isAbsolutelyQuasiSeparated`
with its condition (4) discharged by
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_of_dominating_of_topology`,
whose hypothesis is repeated here verbatim. Condition (3) of Stacks 0GN4 is
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift_absolute` above
and conditions (1) and (2) are discharged in
`AlgebraicGeometry.Stack`
`.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompactStack`,
so `h_affine_dominating` is the
*only* thing standing between this and the full assertion of Stacks 0GQV in the fppf topology. It
is proved as `AlgebraicGeometry.Stack.exists_affine_dominating_absolute` below, where this
result with it discharged is
`AlgebraicGeometry.Stack`
`.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact_absolute`;
see the module documentation for what it asks. -/
theorem isIso_colimit_post_rightDerived_globalSections_fppf_absolute_of_exists_affine_dominating
    (𝒴 : AlgebraicStacks.{u, w} B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒴.val 𝒴.property)
    (h𝒴 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒴)
    (h_affine_dominating : ∀ {x x' : 𝒴.val.val.obj} (a b : x ⟶ x'),
      x ∈ affineObjects B S hS 𝒴.val → x' ∈ affineObjects B S hS 𝒴.val →
      ∃ (V : 𝒴.val.val.obj) (pV : V ⟶ x), V ∈ affineObjects B S hS 𝒴.val ∧
        pV ≫ a = pV ≫ b ∧
        ∀ (y : 𝒴.val.val.obj) (α : y ⟶ x), α ≫ a = α ≫ b →
          ∃ R ∈ BigFppfOver.topology B S hS (𝒴.val.val.p.obj y),
            ∀ ⦃T : BigFppfOver B S hS⦄ ⦃k : T ⟶ 𝒴.val.val.p.obj y⦄, R.arrows k →
              ∃ (w : 𝒴.val.val.obj) (g : w ⟶ y) (r : w ⟶ V),
                𝒴.val.val.p.IsHomLift k g ∧ r ≫ pV = g ≫ α)
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (fppfTopology B S hS 𝒴.val) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (fppfTopology B S hS 𝒴.val) Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_fppf_of_isAbsolutelyQuasiSeparated.{u, w}
    B S hS 𝒴 hZ hqc h𝒴
    (exists_fin_affineObjects_isLocallySurjective_equalizerLift_of_dominating_of_topology.{u, w}
      B S hS 𝒴 B.topology h_affine_dominating)
    p F


end AffineQuadruple

section AffineEqualizer

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

variable {x x' : 𝒳.val.val.obj} (a b : x ⟶ x')

/-- **The 2-fibre product of the two graphs of a parallel pair of morphisms between objects lying
over affine schemes is a quasi-compact algebraic stack**, for a quasi-separated algebraic stack,
quasi-separatedness read absolutely as in **Stacks 050D** part (8). Nothing is asked of the base
scheme of the big fppf site.

This is **Stacks 075S** part (1) in its absolute form at the second graph, applied to the first,
and it asks nothing of the two 1-morphisms: their common source is the slice at an affine object,
which is `AlgebraicGeometry.Stack.schemeStack` there on the nose, hence quasi-compact by
`AlgebraicGeometry.Stack.isQuasiCompactStack_schemeStack_of_isAffine`; and their common target is
quasi-separated by
`AlgebraicGeometry.Stack.isAbsolutelyQuasiSeparated_twoFibreProductAlgebraicStack_objectMorphism`.
Quasi-compactness of a 1-morphism is **Stacks 050U**, so applying it at the first graph — whose
source is the same quasi-compact slice — is exactly the 2-fibre product wanted.

That last input is the one condition (4) needs and condition (3) does not, and it is where
quasi-separatedness of `𝒳` enters the proof of condition (4) — a step the source does not
record. -/
theorem isQuasiCompactStack_equalizerTwoFibreProduct_absolute (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    (hx : IsAffineObject B S hS 𝒳.val.val.p x)
    (hx' : IsAffineObject B S hS 𝒳.val.val.p x') :
    IsQuasiCompactStack.{u, w} B S hS (equalizerTwoFibreProduct B S hS 𝒳 a b).val
      (equalizerTwoFibreProduct B S hS 𝒳 a b).property :=
  isQuasiCompactMorphism_of_isQuasiCompactStack_absolute.{u, w} B S hS hZ
    (graphAlgebraicStacks B S hS 𝒳 b)
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj x) hx)
    (isAbsolutelyQuasiSeparated_twoFibreProductAlgebraicStack_objectMorphism.{u, w}
      B S hS 𝒳 hZ h𝒳 hx hx')
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x))
    (graphAlgebraicStacks B S hS 𝒳 a)
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS (𝒳.val.val.p.obj x) hx)

end AffineEqualizer

section Condition

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The geometric statement condition (4) of Stacks 0GN4 was reduced to**, for a quasi-separated
algebraic stack and any topology of Stacks 06TP in which a surjective smooth 1-morphism admits
fibre lifts: for two objects `x`, `x'` of the site lying over affine schemes and two morphisms
`a, b : x ⟶ x'`, there is an object `V` lying over an affine scheme together with a morphism
`p_V : V ⟶ x` satisfying `p_V ≫ a = p_V ≫ b`, such that every morphism `α : y ⟶ x` of the site
with `α ≫ a = α ≫ b` carries a covering sieve of the scheme `y` lies over, over each member `k` of
which there are `g : w ⟶ y` lying over `k` and `r : w ⟶ V` with `r ≫ p_V = g ≫ α`.

This is the hypothesis `h_affine_dominating` of
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_of_dominating_of_topology`, and
with it condition (4) is proved — at the fppf topology with the fibre-lifting hypothesis discharged
by **Stacks 06QA**, and at the étale topology by **Stacks 06XH** part (2).

Quasi-separatedness enters only through
`AlgebraicGeometry.Stack`
`.isQuasiCompactStack_equalizerTwoFibreProduct_absolute`, which mentions no topology.

`V` is the object of the site the dominating object of
`AlgebraicGeometry.Stack.exists_graph_dominating_associatedTopology` classifies, and `p_V` the
equalizing morphism it classifies. For an equalizing `α : y ⟶ x`, the dictionary
`CategoryTheory.TwoFibreProductOver.TwoYonedaGraph.exists_objOf_of_equalizing_hom` produces an
object `P` of the 2-fibre product classifying `α` over the scheme `y` lies over, together with a
vertical identification `e` of `y` with the object `P` classifies; the covering the dominating
object carries at `P` is the covering sought, and over each of its members `k` the dominating
datum gives `ψ : P' ⟶ P` and `χ : P' ⟶ Q`, whence `g` is the morphism `ψ` induces followed by
`e⁻¹` — lying over `k` because the morphism `ψ` induces does, by
`AlgebraicGeometry.Stack.isHomLift_equalizerMap`, and `e⁻¹` is vertical — and `r` the morphism
`χ` induces. -/
theorem exists_affine_dominating_absolute (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    (τ : GrothendieckTopology B.Schemes)
    (h_lift : ∀ (𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒲),
      IsSurjective B S hS f → AlgebraicStacks.IsSmooth B S hS f →
      ∀ (U : BigFppfOver B S hS) (z : 𝒲.val.val.p.Fiber U),
        ∃ R ∈ τ.over (B.obj hS) U,
          ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
            ∃ (c : 𝒵.val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor f.hom).obj c ⟶ z.1),
              𝒲.val.val.p.IsHomLift k α) :
    ∀ {x x' : 𝒳.val.val.obj} (a b : x ⟶ x'),
      x ∈ affineObjects B S hS 𝒳.val → x' ∈ affineObjects B S hS 𝒳.val →
      ∃ (V : 𝒳.val.val.obj) (pV : V ⟶ x), V ∈ affineObjects B S hS 𝒳.val ∧
        pV ≫ a = pV ≫ b ∧
        ∀ (y : 𝒳.val.val.obj) (α : y ⟶ x), α ≫ a = α ≫ b →
          ∃ R ∈ τ.over (B.obj hS) (𝒳.val.val.p.obj y),
            ∀ ⦃T : BigFppfOver B S hS⦄ ⦃k : T ⟶ 𝒳.val.val.p.obj y⦄, R.arrows k →
              ∃ (w : 𝒳.val.val.obj) (g : w ⟶ y) (r : w ⟶ V),
                𝒳.val.val.p.IsHomLift k g ∧ r ≫ pV = g ≫ α := by
  intro x x' a b hx hx'
  obtain ⟨Q, hQaff, hQ⟩ := exists_graph_dominating_associatedTopology B S hS 𝒳 a b τ
    (isQuasiCompactStack_equalizerTwoFibreProduct_absolute B S hS 𝒳 a b hZ h𝒳 hx hx') h_lift
  refine ⟨equalizerObj B S hS 𝒳 a b Q, equalizerHom B S hS 𝒳 a b Q, hQaff,
    equalizerHom_comp_eq B S hS 𝒳 a b Q, ?_⟩
  intro y α hα
  obtain ⟨P, e, hbase, hvert, hfac⟩ :=
    TwoFibreProductOver.TwoYonedaGraph.exists_objOf_of_equalizing_hom
      𝒳.val.isFiberedInGroupoids (fibreObj B S hS 𝒳.val x) (fibreObj B S hS 𝒳.val x')
      (𝒳.val.val.p.map a) a (𝒳.val.val.p.map b) b α hα
  rw [← hbase] at hvert ⊢
  obtain ⟨R, hR, hlift⟩ := hQ P
  refine ⟨R, hR, ?_⟩
  intro T k hk
  obtain ⟨P', ψ, χ, hψ⟩ := hlift hk
  have := hvert
  have := hψ
  have e1 : equalizerMap B S hS 𝒳 a b χ ≫ equalizerHom B S hS 𝒳 a b Q =
      equalizerHom B S hS 𝒳 a b P' := equalizerMap_comp_equalizerHom B S hS 𝒳 a b χ
  have e2 : equalizerMap B S hS 𝒳 a b ψ ≫ equalizerHom B S hS 𝒳 a b P =
      equalizerHom B S hS 𝒳 a b P' := equalizerMap_comp_equalizerHom B S hS 𝒳 a b ψ
  have h4 : e.inv ≫ α = equalizerHom B S hS 𝒳 a b P := (Iso.inv_comp_eq e).2 hfac.symm
  have e3 : (equalizerMap B S hS 𝒳 a b ψ ≫ e.inv) ≫ α =
      equalizerMap B S hS 𝒳 a b ψ ≫ equalizerHom B S hS 𝒳 a b P := by
    rw [Category.assoc, h4]
  exact ⟨equalizerObj B S hS 𝒳 a b P', equalizerMap B S hS 𝒳 a b ψ ≫ e.inv,
    equalizerMap B S hS 𝒳 a b χ, inferInstance, e1.trans (e2.symm.trans e3.symm)⟩

/-- **Condition (4) of Stacks 0GN4 at an arbitrary topology of Stacks 06TP in which a surjective
smooth 1-morphism admits fibre lifts**, for a quasi-separated algebraic stack: for two objects
`x`, `x'` of the site lying over affine schemes and two morphisms `a, b : x ⟶ x'` there is a finite
family of objects lying over affine schemes, each with a morphism to `x` equalizing `a` and `b`,
whose sheafified representables jointly cover the equalizer of `h_a^#` and `h_b^#`.

The family has one member, as in the source: the object the dominating object of
`AlgebraicGeometry.Stack.exists_graph_dominating_associatedTopology` classifies, with the
equalizing morphism it classifies. This is
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_of_dominating_of_topology`
with its hypothesis discharged by `AlgebraicGeometry.Stack.exists_affine_dominating_absolute`.

The fppf statement
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_absolute` is its value at
`AlgebraicGeometry.BigFppfSite.topology`, and the étale one
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_etale_absolute` its value
at `AlgebraicGeometry.etaleTopology`. -/
theorem exists_fin_affineObjects_isLocallySurjective_equalizerLift_associatedTopology_absolute
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    (τ : GrothendieckTopology B.Schemes)
    (h_lift : ∀ (𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒲),
      IsSurjective B S hS f → AlgebraicStacks.IsSmooth B S hS f →
      ∀ (U : BigFppfOver B S hS) (z : 𝒲.val.val.p.Fiber U),
        ∃ R ∈ τ.over (B.obj hS) U,
          ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
            ∃ (c : 𝒵.val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor f.hom).obj c ⟶ z.1),
              𝒲.val.val.p.IsHomLift k α) :
    ∀ {x x' : 𝒳.val.val.obj} (a b : x ⟶ x'),
      x ∈ affineObjects B S hS 𝒳.val → x' ∈ affineObjects B S hS 𝒳.val →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ x) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p τ)).map a)
              (g := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p τ)).map b)
              ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p τ)).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda
                    (associatedTopology B S hS 𝒳.val.val.p τ)).map (hp i))) :=
  exists_fin_affineObjects_isLocallySurjective_equalizerLift_of_dominating_of_topology.{u, w}
    B S hS 𝒳 τ (exists_affine_dominating_absolute.{u, w} B S hS 𝒳 hZ h𝒳 τ h_lift)

/-- **Condition (4) of Stacks 0GN4 for the fppf site of a quasi-separated algebraic stack**, in
the shape
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf` consumes as its
hypothesis `h_equalizer`: for two objects `x`, `x'` of the site lying over affine schemes and two
morphisms `a, b : x ⟶ x'` there is a finite family of objects lying over affine schemes, each with
a morphism to `x` equalizing `a` and `b`, whose sheafified representables jointly cover the
equalizer of `h_a^#` and `h_b^#`.

The family has one member, as in the source: the object the dominating object of
`AlgebraicGeometry.Stack.exists_graph_dominating` classifies, with the equalizing morphism it
classifies. This is
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_associatedTopology_absolute`
at the big fppf
topology of `B`, its fibre-lifting hypothesis discharged by **Stacks 06QA**,
`AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift`. -/
theorem exists_fin_affineObjects_isLocallySurjective_equalizerLift_absolute
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳) :
    ∀ {x x' : 𝒳.val.val.obj} (a b : x ⟶ x'),
      x ∈ affineObjects B S hS 𝒳.val → x' ∈ affineObjects B S hS 𝒳.val →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ x) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map a)
              (g := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map b)
              ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).map (hp i))) :=
  exists_fin_affineObjects_isLocallySurjective_equalizerLift_associatedTopology_absolute.{u, w}
    B S hS 𝒳 hZ h𝒳 B.topology
    fun _ _ f hsurj hsm => exists_fppfCovering_fibre_lift B S hS f hsurj
      (AlgebraicStacks.isFlat_of_isSmooth B S hS f hsm)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS f hsm)

/-- **Stacks 0GQV in the fppf topology: on a quasi-compact and quasi-separated algebraic stack,
cohomology commutes with filtered colimits.** Let `𝒳` be such a stack and give its total category
the fppf topology of Stacks 06TP. Then `colim_i H^p(𝒳, F_i) ⟶ H^p(𝒳, colim_i F_i)` is an
isomorphism in every degree `p`, for every filtered diagram `F` of abelian fppf sheaves on `𝒳`.

The hypotheses are the source's and nothing more: quasi-compactness in the sense of **Stacks 04YB**
and quasi-separatedness in the *absolute* sense of **Stacks 050D** part (8), quasi-separatedness
over `Spec ℤ`. In particular nothing is asked of the base scheme `S` of the big fppf site, which
the source has no notion of; the containment of the terminal scheme that the absolute notion is
stated with is discharged by `AlgebraicGeometry.BigFppfSite.contains_terminal` rather than assumed.

All four conditions of Stacks 0GN4 are discharged: (1) from quasi-compactness by
`AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from`, (2) for every
category fibred in groupoids by
`AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_fppfTopology`, (3) by
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift_absolute` and (4) by
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift_absolute`
above.

Conditions (3) and (4) need the 2-fibre products the source covers by an affine to be
quasi-compact, and that is **Stacks 075S**. The repository's over-the-base statement of that tag,
`AlgebraicGeometry.Stack.isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProduct`, cannot
serve: the proof of its part (1) cancels the structure morphism to `S`, so it needs that morphism
to be quasi-compact for a quasi-compact `𝒳`, which is
`AlgebraicGeometry.Stack.compactSpace_prod_of_quasiSeparatedSpace` — compactness of `V ×_S T` for
affine objects `V`, `T` of the site — and that fails over a base scheme which is not
quasi-separated, two affine opens of such a scheme being free to meet in a non-quasi-compact open.
So it carries `QuasiSeparatedSpace S`, which the source does not ask for.

What is used instead is the absolute form,
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactStack_absolute`, which cancels the
structure morphism to `Spec ℤ` as the source does. It is proved by running the over-the-base
statement at the terminal base, where `QuasiSeparatedSpace` is free — the terminal scheme is
affine — and carrying its conclusion back to `S` along Construction A of **Stacks 04X5**. That
passage is two results:
`AlgebraicGeometry.Stack.changeBaseTwoFibreProductInv`, which identifies the 2-fibre product of the
views with the view of the 2-fibre product, and
`AlgebraicGeometry.Stack.isQuasiCompactStack_changeBaseAlgebraicStack_iff`, which descends
quasi-compactness from the view to the stack itself through the presentation characterisation of
**Stacks 04YC** and the bijection
`AlgebraicGeometry.Stack.changeBasePointsEquiv` on the point sets of Stacks 04XG. -/
@[stacks 0GQV "the first assertion, in the fppf topology; all four conditions of 0GN4 proved, \
under the source's own hypotheses -- quasi-compactness of the stack and its absolute \
quasi-separatedness, with nothing asked of the base scheme of the site"]
theorem isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact_absolute
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳qs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS B.contains_terminal 𝒳)
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (fppfTopology B S hS 𝒳.val) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (fppfTopology B S hS 𝒳.val) Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_fppf_of_isAbsolutelyQuasiSeparated.{u, w}
    B S hS 𝒳 B.contains_terminal hqc h𝒳qs
    (exists_fin_affineObjects_isLocallySurjective_equalizerLift_absolute.{u, w} B S hS 𝒳
      B.contains_terminal h𝒳qs)
    p F


end Condition

section EtaleCondition

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Condition (4) of Stacks 0GN4 for the étale site of an algebraic stack quasi-separated over a
quasi-separated algebraic stack**, in the shape
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale` consumes as its
hypothesis `h_equalizer`: for two objects `x`, `x'` of the étale site lying over affine schemes and
two morphisms `a, b : x ⟶ x'` there is a finite family of such objects, each with a morphism to `x`
equalizing `a` and `b`, whose sheafified representables jointly cover the equalizer of `h_a^#` and
`h_b^#`.

This is
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_associatedTopology_absolute`
at the big étale
topology, its fibre-lifting hypothesis discharged by **Stacks 06XH** part (2),
`AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`, which reads the fibre lifts of a
surjective smooth 1-morphism off an *étale* covering of the base. The affine smooth presentation of
**Stacks 04YC** is smooth and surjective, which is exactly what that tag asks for, so the étale
case needs nothing of the presentation beyond what the fppf case needs — in particular no affine
étale presentation of a quasi-compact algebraic stack. The family has one member, as in the
source.

The fppf statement is the same result at
`AlgebraicGeometry.BigFppfSite.topology`,
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift_absolute`,
where **Stacks 06QA** discharges the hypothesis instead. -/
theorem exists_fin_affineObjects_isLocallySurjective_equalizerLift_etale_absolute
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h𝒳 : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳) :
    ∀ {U U' : 𝒳.val.val.obj} (u v : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒳.val → U' ∈ affineObjects B S hS 𝒳.val →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ u = p i ≫ v),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map u)
              (g := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map v)
              ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda
                    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).map (hp i))) :=
  exists_fin_affineObjects_isLocallySurjective_equalizerLift_associatedTopology_absolute.{u, w}
    B S hS 𝒳 hZ h𝒳 (etaleTopology B)
    fun _ _ f hsurj hsm => exists_etaleCovering_fibre_lift B S hS f hsurj hsm

/-- **The second assertion of Stacks 0GQV: the same statement in the étale topology.** Let `𝒳` be
a quasi-compact and quasi-separated algebraic stack and give its total category the étale topology
of Stacks 06TP. Then `colim_i H^p(𝒳, F_i) ⟶ H^p(𝒳, colim_i F_i)` is an isomorphism in every
degree `p`, for every filtered diagram `F` of abelian étale sheaves on `𝒳`.

All four conditions of Stacks 0GN4 are discharged for the étale site: (1) from quasi-compactness by
`AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from_etale`, (2) for
every category fibred in groupoids by
`AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_etaleTopology`, (3) by
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_prodLift_etale_absolute` and (4) by
`AlgebraicGeometry.Stack`
`.exists_fin_affineObjects_isLocallySurjective_equalizerLift_etale_absolute` above.

The hypotheses are the ones the fppf assertion
`AlgebraicGeometry.Stack`
`.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact_absolute`
carries, and they are the source's: quasi-compactness in the sense of **Stacks 04YB** and
quasi-separatedness in the *absolute* sense of **Stacks 050D** part (8). Nothing is asked of the
base scheme `S` of the big fppf site, and the containment of the terminal scheme the absolute
notion is stated with is discharged by `AlgebraicGeometry.BigFppfSite.contains_terminal` rather
than assumed.

The two topologies agree on where quasi-separatedness is used, and on what form of it: conditions
(3) and (4) are about the 2-fibre products the source covers by an affine scheme and not about the
topology, so both reach **Stacks 075S** and both take it in the absolute form
`AlgebraicGeometry.Stack.isQuasiCompactMorphism_of_isQuasiCompactStack_absolute`, which cancels the
structure morphism to `Spec ℤ` as the source does rather than the one to `S`. See the docstring of
the fppf assertion for why the over-the-base statement of Stacks 075S cannot serve, and
`StacksFrontier/AlgebraicGeometry/Stacks/QuasiCompactQuasiSeparatedStackAbsolute.lean` for how the
absolute form is proved from it. -/
@[stacks 0GQV "the second assertion, in the étale topology; all four conditions of 0GN4 \
proved, under the source's own hypotheses -- quasi-compactness of the stack and its absolute \
quasi-separatedness, with nothing asked of the base scheme of the site"]
theorem isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompact_absolute
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h𝒳qs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS B.contains_terminal 𝒳)
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_etale_of_isAbsolutelyQuasiSeparated.{u, w}
    B S hS 𝒳 B.contains_terminal hqc h𝒳qs
    (exists_fin_affineObjects_isLocallySurjective_equalizerLift_etale_absolute.{u, w} B S hS 𝒳
      B.contains_terminal h𝒳qs)
    p F


end EtaleCondition

end AlgebraicGeometry.Stack

end
