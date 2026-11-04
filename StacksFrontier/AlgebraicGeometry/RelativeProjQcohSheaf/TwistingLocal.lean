module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski

/-!
# The two laws of the map `ψ` of a quadruple are local on the test scheme

A glueing argument for the functor `F_d` of Section 01NS has to produce the map `ψ` of a
quadruple over a test scheme `T` out of the maps given on the members of an open covering of
`T`. The homogeneous components are glued as morphisms of sheaves of modules; what then has to
be checked of the glued family is the multiplicativity `Twisting.app_mul` and the unit law
`Twisting.app_one`. Both are **equations of morphisms of sheaves of modules on `T`**, so both
are local, and this file records that in the shape the glueing meets them.

## Why no compatibility of restriction with the monoidal structure is needed

Separatedness of morphisms of sheaves of modules is available in two forms:
`Stacks.Descent.hom_ext_of_restrictFunctor_map_eq` for `AlgebraicGeometry.Scheme.Modules.restrict`
and `Stacks.Descent.hom_ext_of_pullback_map_eq` for the inverse image. The second is the one to
use here: the two laws are written with the comparison `f^*(X ⊗ Y) ≅ f^*X ⊗ f^*Y` of Tag 01CD
and with the multiplication of the Laurent algebra, and it is the **inverse image**, not the
restriction, for which this repository has the compatibility with both — the monoidality of
Tag 01CD (`Stacks.PullbackTensorCoherence.pullbackTensorComparison_comp`,
`...pullbackUnitComparison_comp`) and the multiplicativity of the comparison of integral tensor
powers of Tag 01CU
(`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback_mul`). So the locality step
asks nothing of `restrictFunctor`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullbackFamily`: the degreewise pullback of an
  **arbitrary** family of homogeneous components, which is
  `...RelativeProjQcohSheaf.Twisting.pullbackApp` with the two laws of a `Twisting` not assumed.
  A glueing argument holds such a family before it knows the laws.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullbackMulConj`: the isomorphism conjugating
  the source of the multiplicativity law of a family into the source of the multiplicativity law
  of its degreewise pullback.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.hom_ext_of_pullbackFamily_eq`: **a family of
  homogeneous components is determined by its degreewise pullbacks along a covering family of
  open immersions.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.mul_of_pullback_map_cover` and
  `...one_of_pullback_map_cover`: **the multiplicativity and the unit law of a family are local
  on the test scheme**, in the inverse-image form of separatedness.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullbackFamily_mul_iff`: **the
  multiplicativity of the degreewise pullback of a family is equivalent to the inverse image of
  the multiplicativity of the family.** The two laws differ by the isomorphism `pullbackMulConj`
  on the source and the comparison of the integral tensor powers of Tag 01CU on the target.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.mul_of_pullbackFamily_mul_cover`: **the
  multiplicativity of a family follows from the multiplicativity of its degreewise pullbacks
  along a covering family of open immersions** — `mul_of_pullback_map_cover` in the shape a
  glueing argument meets it.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullbackFamily_one_iff`: **the unit law of the
  degreewise pullback of a family is equivalent to the inverse image of the unit law of the
  family**, with
  `...RelativeProjQcohSheaf.one_of_pullbackFamily_one_cover` the matching locality statement. The
  two conjugations are `...RelativeProjQcohSheaf.pullbackUnitComparison_comp_family_one` and
  `...pullbackUnitComparison_comp_oneHom_laurent_pullback`, and
  `...RelativeProjQcohSheaf.map_oneHom_comp_family_zero` is the `inv`-free form of the law for a
  family whose two laws are not assumed.

## How the two shapes of the multiplicativity law are reconciled

`mul_of_pullback_map_cover` asks for the inverse image *of the equation*. What a glueing argument
has instead is the equation satisfied by the family over each member of the covering, i.e. the
multiplicativity of `pullbackFamily app (g k)`. The passage from the one to the other is the
chain of `...RelativeProjQcohSheaf.Twisting.pullbackApp_mul` read as an equivalence rather than
an implication, and that is `pullbackFamily_mul_iff`: both sides of the law for the pulled-back
family are the inverse image of the corresponding side of the law for the family, conjugated by
`pullbackMulConj` and by `laurentPullback`, so each law is a cancellation away from the other.
The two conjugations are `pullbackMulConj_lhs` (the naturality of the comparison of Tag 01CD
followed by the multiplicativity of the comparison of Tag 01CU) and `pullbackMulConj_rhs`
(`...RelativeProjQcohSheaf.inv_pullbackTensorComparison_comp_map_comp_compComparison`, itself
the compatibility of the contraction of an iterated pullback with the comparison of Tag 01CD
followed by its naturality). No new mathematics enters.

`pullbackFamily_one_iff` is the same reconciliation for the unit law, and it is the computation
inside `...RelativeProjQcohSheaf.Twisting.pullbackApp_one` read as an equivalence rather than an
implication: there the law of `ψ` is used to conclude the law of its pullback, here neither law is
assumed and the two are shown to differ by three isomorphisms — the structure-sheaf comparison of
`g ∘ f`, the contraction of the iterated pullback at the monoidal unit, and the comparison of the
integral tensor powers in degree zero. The conjugations are the two theorems named above; the
cancellations are collected in the private helpers `eq_iff_of_unitConj` and
`unitConj_of_comp_eq`, which are stated in a bare category because a goal mixing the two
`rfl`-equal spellings of the structure sheaf is not type-correct at `implicit` transparency.

## No tag is claimed

Nothing here states a clause of a tag.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence

universe v u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T' T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The degreewise pullback of a family of homogeneous components**, with the two laws of a
`...RelativeProjQcohSheaf.Twisting` not assumed: the contraction of the iterated pullback,
followed by the pullback of the component, followed by the comparison of the integral tensor
powers of Tag 01CU. For the family of a `Twisting` this is
`...RelativeProjQcohSheaf.Twisting.pullbackApp`, by `rfl`. -/
def pullbackFamily
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (g : T' ⟶ T) (i : ℤ) :
    (pullbackFunctor (ringedSpaceHom (g ≫ f))).obj (A.piece (i * d)) ⟶
      (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).piece i :=
  compComparison g f (A.piece (i * d)) ≫
    (pullbackFunctor (ringedSpaceHom g)).map (app i) ≫ laurentPullback g L i

/-- The degreewise pullback of the family of a `...RelativeProjQcohSheaf.Twisting` is the
pullback of its map. -/
theorem pullbackFamily_app (ψ : Twisting f A d L) (g : T' ⟶ T) (i : ℤ) :
    pullbackFamily ψ.app g i = ψ.pullbackApp g i :=
  rfl

/-- **The isomorphism conjugating the multiplicativity law of a family into the multiplicativity
law of its degreewise pullback.** It is the tensor product of the two contractions of the
iterated pullback, followed by the inverse of the comparison of Tag 01CD along `g`; both are
isomorphisms. -/
def pullbackMulConj (g : T' ⟶ T) (i j : ℤ) :
    MonoidalCategoryStruct.tensorObj
        ((pullbackFunctor (ringedSpaceHom (g ≫ f))).obj (A.piece (i * d)))
        ((pullbackFunctor (ringedSpaceHom (g ≫ f))).obj (A.piece (j * d))) ⟶
      (pullbackFunctor (ringedSpaceHom g)).obj
        (MonoidalCategoryStruct.tensorObj
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)))
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (j * d)))) :=
  MonoidalCategoryStruct.tensorHom (compComparison g f (A.piece (i * d)))
      (compComparison g f (A.piece (j * d))) ≫
    inv (pullbackTensorComparison (ringedSpaceHom g)
      ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)))
      ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (j * d))))

/-- The morphism `pullbackMulConj g i j` is an isomorphism. -/
instance isIso_pullbackMulConj (g : T' ⟶ T) (i j : ℤ) :
    IsIso (pullbackMulConj (f := f) (A := A) (d := d) g i j) := by
  rw [pullbackMulConj]
  infer_instance

/-- **The left-hand side of the multiplicativity law is conjugated by `pullbackMulConj`.** The
tensor product of the degreewise pullbacks of two components, followed by the multiplication of
the Laurent algebra of `g^*L`, is the inverse image of the tensor product of the components
followed by the multiplication of the Laurent algebra of `L`, conjugated by `pullbackMulConj`
and by the comparison of the integral tensor powers of Tag 01CU.

This is the naturality of the comparison of Tag 01CD
(`...RelativeProjQcohSheaf.pullbackTensorComparison_naturality_tensorHom`) followed by the
multiplicativity of the comparison of Tag 01CU
(`...RelativeProjQcohSheaf.laurentPullback_mul`). -/
theorem pullbackMulConj_lhs
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (g : T' ⟶ T) (i j : ℤ) :
    MonoidalCategoryStruct.tensorHom (pullbackFamily app g i) (pullbackFamily app g j) ≫
        (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).mulSheaf i j =
      pullbackMulConj g i j ≫
        (pullbackFunctor (ringedSpaceHom g)).map
          (MonoidalCategoryStruct.tensorHom (app i) (app j) ≫ (laurent L).mulSheaf i j) ≫
        laurentPullback g L (i + j) := by
  have core : pullbackTensorComparison (ringedSpaceHom g)
        ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)))
        ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (j * d))) ≫
      (MonoidalCategoryStruct.tensorHom ((pullbackFunctor (ringedSpaceHom g)).map (app i))
          ((pullbackFunctor (ringedSpaceHom g)).map (app j)) ≫
        MonoidalCategoryStruct.tensorHom (laurentPullback g L i) (laurentPullback g L j) ≫
          laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j) =
      (pullbackFunctor (ringedSpaceHom g)).map
          (MonoidalCategoryStruct.tensorHom (app i) (app j) ≫ laurentMul L i j) ≫
        laurentPullback g L (i + j) := by
    rw [← Category.assoc, ← pullbackTensorComparison_naturality_tensorHom (ringedSpaceHom g)
      (app i) (app j), Category.assoc, laurentPullback_mul g L i j,
      CategoryTheory.Functor.map_comp, Category.assoc]
  rw [laurent_mulSheaf_eq, laurent_mulSheaf_eq, pullbackMulConj, pullbackFamily, pullbackFamily,
    ← MonoidalCategory.tensorHom_comp_tensorHom, ← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [(IsIso.inv_comp_eq _).mpr core.symm]

/-- **The right-hand side of the multiplicativity law is conjugated by `pullbackMulConj`.** The
inverse image along `g` of the morphism built from the multiplication of `𝒜^{(d)}` and the
component in degree `i + j` is that same morphism for the pulled-back family, conjugated by
`pullbackMulConj` and by the comparison of the integral tensor powers of Tag 01CU.

This is the compatibility of the contraction of an iterated pullback with the comparison of
Tag 01CD (`...RelativeProjQcohSheaf.inv_pullbackTensorComparison_comp_compComparison`) followed
by its naturality (`...RelativeProjQcohSheaf.compComparison_naturality`). -/
theorem pullbackMulConj_rhs
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (g : T' ⟶ T) (i j : ℤ) :
    inv (pullbackTensorComparison (ringedSpaceHom (g ≫ f)) (A.piece (i * d))
          (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom (g ≫ f))).map
          (A.mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
        pullbackFamily app g (i + j) =
      pullbackMulConj g i j ≫
        (pullbackFunctor (ringedSpaceHom g)).map
          (inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d))
                (A.piece (j * d))) ≫
            (pullbackFunctor (ringedSpaceHom f)).map
              (A.mulSheaf (i * d) (j * d) ≫
                eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
            app (i + j)) ≫
        laurentPullback g L (i + j) := by
  rw [pullbackMulConj, pullbackFamily]
  exact inv_pullbackTensorComparison_comp_map_comp_compComparison g f
    (A.mulSheaf (i * d) (j * d) ≫
      eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d)))
    (app (i + j)) (laurentPullback g L (i + j))

/-- **The multiplicativity of the degreewise pullback of a family of homogeneous components is
equivalent to the inverse image of the multiplicativity of the family.** The two laws differ by
the isomorphism `pullbackMulConj` on the source and the comparison of the integral tensor powers
of Tag 01CU on the target, so each is a cancellation away from the other.

This is the hypothesis of `...RelativeProjQcohSheaf.mul_of_pullback_map_cover` restated in the
shape a glueing argument has it: a glueing argument knows the multiplicativity of the pulled-back
family over each member of the covering, and this says that that is the same information as the
inverse image of the equation. -/
theorem pullbackFamily_mul_iff
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (g : T' ⟶ T) (i j : ℤ) :
    (MonoidalCategoryStruct.tensorHom (pullbackFamily app g i) (pullbackFamily app g j) ≫
          (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).mulSheaf i j =
        inv (pullbackTensorComparison (ringedSpaceHom (g ≫ f)) (A.piece (i * d))
              (A.piece (j * d))) ≫
          (pullbackFunctor (ringedSpaceHom (g ≫ f))).map
            (A.mulSheaf (i * d) (j * d) ≫
              eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
          pullbackFamily app g (i + j)) ↔
      (pullbackFunctor (ringedSpaceHom g)).map
          (MonoidalCategoryStruct.tensorHom (app i) (app j) ≫ (laurent L).mulSheaf i j) =
        (pullbackFunctor (ringedSpaceHom g)).map
          (inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d))
                (A.piece (j * d))) ≫
            (pullbackFunctor (ringedSpaceHom f)).map
              (A.mulSheaf (i * d) (j * d) ≫
                eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
            app (i + j)) := by
  rw [pullbackMulConj_lhs app g i j, pullbackMulConj_rhs app g i j,
    cancel_epi (pullbackMulConj (f := f) (A := A) (d := d) g i j),
    cancel_mono (laurentPullback g L (i + j))]

/-- **The degreewise pullback along one open immersion determines the component.** The two
comparisons through which the pullback of a family is built are isomorphisms, so this is the
faithfulness of nothing at all: it is a cancellation. -/
theorem pullback_map_eq_of_pullbackFamily_eq
    {app app' : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i}
    (g : T' ⟶ T) (i : ℤ) (h : pullbackFamily app g i = pullbackFamily app' g i) :
    (pullbackFunctor (ringedSpaceHom g)).map (app i) =
      (pullbackFunctor (ringedSpaceHom g)).map (app' i) := by
  rw [pullbackFamily, pullbackFamily] at h
  exact (cancel_mono (laurentPullback g L i)).mp ((cancel_epi (compComparison g f _)).mp h)

/-- **A family of homogeneous components is determined by its degreewise pullbacks along a
covering family of open immersions.** This is the uniqueness half of the glueing of the map `ψ`
of a quadruple: `Stacks.Descent.hom_ext_of_pullback_map_eq` applied in each degree, after the
two comparisons have been cancelled. -/
theorem hom_ext_of_pullbackFamily_eq
    {app app' : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i}
    {I : Type v} {X : I → Scheme.{u}} (g : ∀ k, X k ⟶ T) [∀ k, IsOpenImmersion (g k)]
    (hg : ⨆ k, (g k).opensRange = ⊤)
    (h : ∀ (k : I) (i : ℤ), pullbackFamily app (g k) i = pullbackFamily app' (g k) i) (i : ℤ) :
    app i = app' i :=
  Stacks.Descent.hom_ext_of_pullback_map_eq g hg fun k ↦
    pullback_map_eq_of_pullbackFamily_eq (g k) i (h k i)

/-- **The multiplicativity of a family of homogeneous components is local on the test scheme.**
The law `Twisting.app_mul` is an equation of morphisms of sheaves of modules on `T`, so it holds
as soon as its inverse image along each member of a covering family of open immersions holds.

No compatibility of `AlgebraicGeometry.Scheme.Modules.restrictFunctor` with the comparison of
Tag 01CD or with the multiplication of the Laurent algebra is involved: separatedness is used in
the inverse-image form `Stacks.Descent.hom_ext_of_pullback_map_eq`, which is the form in which
the monoidal coherence of the inverse image is available. -/
theorem mul_of_pullback_map_cover
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    {I : Type v} {X : I → Scheme.{u}} (g : ∀ k, X k ⟶ T) [∀ k, IsOpenImmersion (g k)]
    (hg : ⨆ k, (g k).opensRange = ⊤) (i j : ℤ)
    (h : ∀ k : I, (pullbackFunctor (ringedSpaceHom (g k))).map
          (MonoidalCategoryStruct.tensorHom (app i) (app j) ≫ (laurent L).mulSheaf i j) =
        (pullbackFunctor (ringedSpaceHom (g k))).map
          (inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d))
                (A.piece (j * d))) ≫
            (pullbackFunctor (ringedSpaceHom f)).map
              (A.mulSheaf (i * d) (j * d) ≫
                eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
            app (i + j))) :
    MonoidalCategoryStruct.tensorHom (app i) (app j) ≫ (laurent L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (A.mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
        app (i + j) :=
  Stacks.Descent.hom_ext_of_pullback_map_eq g hg h

/-- **The multiplicativity of a family of homogeneous components follows from the
multiplicativity of its degreewise pullbacks along a covering family of open immersions.** This
is `...RelativeProjQcohSheaf.mul_of_pullback_map_cover` in the shape a glueing argument meets it:
what is given over each member of the covering is the law `Twisting.app_mul` for the pulled-back
family, and `...RelativeProjQcohSheaf.pullbackFamily_mul_iff` turns that into the inverse image
of the law for the family itself. -/
theorem mul_of_pullbackFamily_mul_cover
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    {I : Type v} {X : I → Scheme.{u}} (g : ∀ k, X k ⟶ T) [∀ k, IsOpenImmersion (g k)]
    (hg : ⨆ k, (g k).opensRange = ⊤) (i j : ℤ)
    (h : ∀ k : I,
      MonoidalCategoryStruct.tensorHom (pullbackFamily app (g k) i)
            (pullbackFamily app (g k) j) ≫
          (laurent ((pullbackFunctor (ringedSpaceHom (g k))).obj L)).mulSheaf i j =
        inv (pullbackTensorComparison (ringedSpaceHom (g k ≫ f)) (A.piece (i * d))
              (A.piece (j * d))) ≫
          (pullbackFunctor (ringedSpaceHom (g k ≫ f))).map
            (A.mulSheaf (i * d) (j * d) ≫
              eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
          pullbackFamily app (g k) (i + j)) :
    MonoidalCategoryStruct.tensorHom (app i) (app j) ≫ (laurent L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (A.mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
        app (i + j) :=
  mul_of_pullback_map_cover app g hg i j fun k =>
    (pullbackFamily_mul_iff app (g k) i j).mp (h k)

/-- **The unit law of a family of homogeneous components is local on the test scheme.** Both
sides of `Twisting.app_one` are morphisms out of the monoidal unit of the category of sheaves of
modules on `T`, so the law holds as soon as its inverse image along each member of a covering
family of open immersions holds. -/
theorem one_of_pullback_map_cover
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    {I : Type v} {X : I → Scheme.{u}} (g : ∀ k, X k ⟶ T) [∀ k, IsOpenImmersion (g k)]
    (hg : ⨆ k, (g k).opensRange = ⊤)
    (h : ∀ k : I, (pullbackFunctor (ringedSpaceHom (g k))).map
          (Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
            (pullbackFunctor (ringedSpaceHom f)).map
              (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
            app 0) =
        (pullbackFunctor (ringedSpaceHom (g k))).map
          (SheafOfModules.GradedAlgebra.oneHom (laurent L))) :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
        app 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent L) :=
  Stacks.Descent.hom_ext_of_pullback_map_eq g hg h

/-! ### The unit law of the degreewise pullback of a family -/

/-- **Two morphisms out of the monoidal unit agree exactly when the two morphisms they are
conjugated into do**, in a bare category with every object and morphism free: if `u ≫ a` and
`u ≫ b` factor as `α ≫ (β ≫ n) ≫ l` and `α ≫ (β ≫ i) ≫ l` through isomorphisms `u`, `α`, `β`
and `l`, then `a = b ↔ n = i`.

Stated abstractly and applied by `exact` for the reason the sibling statements of this directory
record: the goals of the unit law mix the two `rfl`-equal, syntactically distinct spellings
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` and
`Stacks.RingedSpace.structureRingSheaf` of the structure sheaf, so they are not type-correct at
`implicit` transparency and no `rw` applies to them. -/
private theorem eq_iff_of_unitConj {C : Type*} [Category C] {X Y Z Z' W W' : C}
    (α : X ⟶ Y) (β : Y ⟶ Z) (l : Z' ⟶ W') (u : X ⟶ W)
    (hα : IsIso α) (hβ : IsIso β) (hl : IsIso l) (hu : IsIso u)
    (n i : Z ⟶ Z') (a b : W ⟶ W')
    (ha : u ≫ a = α ≫ (β ≫ n) ≫ l) (hb : u ≫ b = α ≫ (β ≫ i) ≫ l) :
    a = b ↔ n = i := by
  have := hα
  have := hβ
  have := hl
  have := hu
  rw [← cancel_epi u, ha, hb, cancel_epi α, cancel_mono l, cancel_epi β]

/-- **Conjugating the right-hand side of a unit law**: if `n ≫ l` and `γ ≫ b` agree and
`α ≫ β ≫ γ` is `u`, then `u ≫ b` is `α ≫ (β ≫ n) ≫ l`. Every object and morphism is free, for
the reason `...RelativeProjQcohSheaf.eq_iff_of_unitConj` records. -/
private theorem unitConj_of_comp_eq {C : Type*} [Category C] {X Y Z Z' W W' : C}
    (α : X ⟶ Y) (β : Y ⟶ Z) (γ : Z ⟶ W) (n : Z ⟶ Z') (l : Z' ⟶ W') (u : X ⟶ W) (b : W ⟶ W')
    (hnl : n ≫ l = γ ≫ b) (hu : α ≫ β ≫ γ = u) :
    u ≫ b = α ≫ (β ≫ n) ≫ l := by
  rw [← hu, Category.assoc, Category.assoc, Category.assoc, hnl]

/-- **The unit law of a family of homogeneous components with the global unit of `f^*𝒜` replaced
by its `inv`-free form**, the two laws of a `...RelativeProjQcohSheaf.Twisting` not assumed: the
inverse image of the global unit of `𝒜` followed by the degree-zero component of the family is
the structure-sheaf comparison of Tag 01CD followed by the law's left-hand side.

For the family of a `Twisting` the right-hand side is the global unit of the Laurent algebra and
this is `...RelativeProjQcohSheaf.Twisting.map_oneHom_comp_app_zero`; here nothing is assumed, so
the law itself survives on the right. The only input is
`Stacks.PullbackStrictUnit.pullbackUnitComparison_comp_pullbackOne`. -/
theorem map_oneHom_comp_family_zero
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i) :
    (pullbackFunctor (ringedSpaceHom f)).map
          (SheafOfModules.GradedAlgebra.oneHom A ≫
            eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ app 0 =
      pullbackUnitComparison (ringedSpaceHom f) ≫
        Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
          (pullbackFunctor (ringedSpaceHom f)).map
            (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ app 0 :=
  (congrArg (fun z => z ≫ app 0)
      (CategoryTheory.Functor.map_comp (pullbackFunctor (ringedSpaceHom f))
        (SheafOfModules.GradedAlgebra.oneHom A)
        (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => z ≫ ((pullbackFunctor (ringedSpaceHom f)).map
            (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ app 0))
          (Stacks.PullbackStrictUnit.pullbackUnitComparison_comp_pullbackOne
            (ringedSpaceHom f) A).symm).trans
        (Category.assoc _ _ _)))

/-- **The left-hand side of the unit law of the degreewise pullback of a family is conjugated by
the contraction of the iterated inverse image.** Composing with the structure-sheaf comparison of
`g ∘ f`, which is an isomorphism, the law's left-hand side for `pullbackFamily app g` is the
inverse image along `g` of the left-hand side for `app`, conjugated by the contraction
`...RelativeProjQcohSheaf.compComparison` at the monoidal unit and by the comparison of the
integral tensor powers of Tag 01CU in degree zero.

This is the computation inside `...RelativeProjQcohSheaf.Twisting.pullbackApp_one` with the law
itself not used: the naturality `...RelativeProjQcohSheaf.compComparison_naturality` of the
contraction and `Stacks.PullbackStrictUnit.pullbackUnitComparison_comp_pullbackOne`, and nothing
else. -/
theorem pullbackUnitComparison_comp_family_one
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (g : T' ⟶ T) :
    pullbackUnitComparison (ringedSpaceHom (g ≫ f)) ≫
        Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom (g ≫ f)) A ≫
          (pullbackFunctor (ringedSpaceHom (g ≫ f))).map
            (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
          pullbackFamily app g 0 =
      compComparison g f (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))) ≫
        ((pullbackFunctor (ringedSpaceHom g)).map
              (pullbackUnitComparison (ringedSpaceHom f)) ≫
            (pullbackFunctor (ringedSpaceHom g)).map
              (Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
                (pullbackFunctor (ringedSpaceHom f)).map
                  (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ app 0)) ≫
          laurentPullback g L 0 := by
  rw [← map_oneHom_comp_family_zero (pullbackFamily app g), pullbackFamily, ← Category.assoc,
    ← compComparison_naturality, Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    map_oneHom_comp_family_zero app, Functor.map_comp, Category.assoc]

/-- **The right-hand side of the unit law is conjugated by the same isomorphisms.** The global
unit of the Laurent algebra of `g^*L`, composed with the structure-sheaf comparison of `g ∘ f`,
is the inverse image of the global unit of the Laurent algebra of `L` conjugated by the
contraction of the iterated inverse image and by the comparison of the integral tensor powers in
degree zero.

Nothing about a family enters: both units are the identity of the structure sheaf
(`...RelativeProjQcohSheaf.oneHom_laurent`), the comparison of the integral tensor powers in
degree zero is the structure-sheaf comparison (`...RelativeProjQcohSheaf.laurentPullback_zero`),
and what is left is the unit coherence `...RelativeProjQcohSheaf.compComparison_unit` of the
contraction. -/
theorem pullbackUnitComparison_comp_oneHom_laurent_pullback (g : T' ⟶ T) :
    pullbackUnitComparison (ringedSpaceHom (g ≫ f)) ≫
        SheafOfModules.GradedAlgebra.oneHom
          (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)) =
      compComparison g f (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))) ≫
        ((pullbackFunctor (ringedSpaceHom g)).map
              (pullbackUnitComparison (ringedSpaceHom f)) ≫
            (pullbackFunctor (ringedSpaceHom g)).map
              (SheafOfModules.GradedAlgebra.oneHom (laurent L))) ≫
          laurentPullback g L 0 :=
  unitConj_of_comp_eq
    (compComparison g f (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))))
    ((pullbackFunctor (ringedSpaceHom g)).map (pullbackUnitComparison (ringedSpaceHom f)))
    (pullbackUnitComparison (ringedSpaceHom g))
    ((pullbackFunctor (ringedSpaceHom g)).map
      (SheafOfModules.GradedAlgebra.oneHom (laurent L)))
    (laurentPullback g L 0) (pullbackUnitComparison (ringedSpaceHom (g ≫ f)))
    (SheafOfModules.GradedAlgebra.oneHom
      (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)))
    (((congrArg (fun z => (pullbackFunctor (ringedSpaceHom g)).map z ≫
              laurentPullback g L 0) (oneHom_laurent L)).trans
          ((congrArg (fun z => z ≫ laurentPullback g L 0)
                (CategoryTheory.Functor.map_id (pullbackFunctor (ringedSpaceHom g))
                  (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))))).trans
            ((Category.id_comp (laurentPullback g L 0)).trans
              (laurentPullback_zero g L)))).trans
      ((Category.comp_id (pullbackUnitComparison (ringedSpaceHom g))).symm.trans
        (congrArg (fun z => pullbackUnitComparison (ringedSpaceHom g) ≫ z)
          (oneHom_laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).symm)))
    (compComparison_unit g f)

/-- **The unit law of the degreewise pullback of a family of homogeneous components is equivalent
to the inverse image of the unit law of the family.** This is
`...RelativeProjQcohSheaf.pullbackFamily_mul_iff` for the other law: the hypothesis of
`...RelativeProjQcohSheaf.one_of_pullback_map_cover` restated in the shape a glueing argument has
it, which is the law `...Twisting.app_one` satisfied by the pulled-back family over each member of
the covering.

Both sides of the law are conjugated by the same three isomorphisms — the structure-sheaf
comparison of `g ∘ f`, the contraction of the iterated inverse image at the monoidal unit, and
the comparison of the integral tensor powers in degree zero — by
`...RelativeProjQcohSheaf.pullbackUnitComparison_comp_family_one` and
`...pullbackUnitComparison_comp_oneHom_laurent_pullback`, so each law is a cancellation away from
the other. -/
theorem pullbackFamily_one_iff
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    (g : T' ⟶ T) :
    (Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom (g ≫ f)) A ≫
          (pullbackFunctor (ringedSpaceHom (g ≫ f))).map
            (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
          pullbackFamily app g 0 =
        SheafOfModules.GradedAlgebra.oneHom
          (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L))) ↔
      (pullbackFunctor (ringedSpaceHom g)).map
          (Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
            (pullbackFunctor (ringedSpaceHom f)).map
              (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ app 0) =
        (pullbackFunctor (ringedSpaceHom g)).map
          (SheafOfModules.GradedAlgebra.oneHom (laurent L)) :=
  eq_iff_of_unitConj
    (compComparison g f (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))))
    ((pullbackFunctor (ringedSpaceHom g)).map (pullbackUnitComparison (ringedSpaceHom f)))
    (laurentPullback g L 0) (pullbackUnitComparison (ringedSpaceHom (g ≫ f)))
    (isIso_compComparison g f _) inferInstance (isIso_laurentPullback g L 0) inferInstance
    _ _ _ _
    (pullbackUnitComparison_comp_family_one app g)
    (pullbackUnitComparison_comp_oneHom_laurent_pullback g)

/-- **The unit law of a family of homogeneous components follows from the unit law of its
degreewise pullbacks along a covering family of open immersions.** This is
`...RelativeProjQcohSheaf.one_of_pullback_map_cover` in the shape a glueing argument meets it, and
it is to that statement what `...RelativeProjQcohSheaf.mul_of_pullbackFamily_mul_cover` is to
`...mul_of_pullback_map_cover`: what is given over each member of the covering is the law
`...Twisting.app_one` for the pulled-back family, and
`...RelativeProjQcohSheaf.pullbackFamily_one_iff` turns that into the inverse image of the law for
the family itself. -/
theorem one_of_pullbackFamily_one_cover
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    {I : Type v} {X : I → Scheme.{u}} (g : ∀ k, X k ⟶ T) [∀ k, IsOpenImmersion (g k)]
    (hg : ⨆ k, (g k).opensRange = ⊤)
    (h : ∀ k : I,
      Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom (g k ≫ f)) A ≫
          (pullbackFunctor (ringedSpaceHom (g k ≫ f))).map
            (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
          pullbackFamily app (g k) 0 =
        SheafOfModules.GradedAlgebra.oneHom
          (laurent ((pullbackFunctor (ringedSpaceHom (g k))).obj L))) :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
        app 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent L) :=
  one_of_pullback_map_cover app g hg fun k => (pullbackFamily_one_iff app (g k)).mp (h k)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
