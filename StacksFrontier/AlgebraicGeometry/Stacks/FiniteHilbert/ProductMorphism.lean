module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# The 1-morphism of Equation 05WD, and the Isom space of Stacks 05YH

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. `StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram`
builds the two legs `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` and `ℋ_d(𝒳/𝒴) ⟶ 𝒴` of the diagram of Stacks 05WD
separately. Equation 05WD is about their *pairing*

`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴`,

which this file constructs, together with the identification of its two components with the two
legs. The product is the one of the 2-category of categories fibred in groupoids over the site:
the 2-fibre product over the final object `𝟭 (Sch/S)_fppf`, which is
`AlgebraicGeometry.Stack.terminalCFG`, exactly as
`CategoryTheory.CatFiberedInGroupoids.product` forms it.

The file also records the one step of the proof of Stacks 05YH that the library can already
take: the production of the Isom space `I = Isom_𝒴(y|_Z, F x)` as an algebraic space over the
cover `Z`, out of the hypothesis of Stacks 05YH that the diagonal of `𝒴` is representable by
algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Stack.absoluteHilbertTargetProductProjection` and
  `AlgebraicGeometry.Stack.absoluteHilbertTargetProduct`: the product `ℋ_d(𝒳) × 𝒴` over the big
  fppf site, as a category over that site.
* `AlgebraicGeometry.Stack.forgetToProduct`: **Stacks 05WD**, the 1-morphism of the equation,
  `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴`.
* `AlgebraicGeometry.Stack.targetCFG`: the target stack `𝒴`, viewed as an object of the
  2-category of categories fibred in groupoids over the site, so that
  `AlgebraicGeometry.Stack.HasRepresentableDiagonal` may be stated for it.
* `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpacesForgetToProduct`: the conclusion of
  **Stacks 05YH**, as a proposition. It carries no tag: the implication is not proved here.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInGroupoids_absoluteHilbertTargetProductProjection`: the
  product `ℋ_d(𝒳) × 𝒴` is fibred in groupoids over the site.
* `AlgebraicGeometry.Stack.forgetToProduct_comp_fst` and
  `AlgebraicGeometry.Stack.forgetToProduct_comp_snd`: the two components of the 1-morphism of
  Equation 05WD are the two legs built in
  `StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram`, on the nose.
* `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_isomPresheaf_cover`: the Isom space of the
  proof of Stacks 05YH is an algebraic space over the cover.

## What is and is not proved

Proved, and tagged: the clause of **Stacks 05WD** that the two legs pair into a single
1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` over the site, together with the two triangles that say
its components are the legs. The pairing is `CategoryTheory.TwoFibreProductOver.lift` of the two
legs along the comparison 2-cell between their composites into the site; that 2-cell is an
`eqToHom`, because both composites *equal* the structure functor of `ℋ_d(𝒳/𝒴)`, and it is
vertical, which is what makes the pairing a 1-morphism into the 2-fibre product over
`𝟭 (Sch/S)_fppf` rather than merely into the product of plain categories.

Proved, and untagged because it is one step of a proof rather than a statement of the source:
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_isomPresheaf_cover`. It is Stacks 045G, the
equivalence of its conditions (1) and (2), read at the cover `Z` of an object of `ℋ_d(𝒳)` and at
the two objects of the fibre of `𝒴` over `Z` that the fibre computation of Stacks 05YH compares.

**Not proved: Stacks 05YH itself.** Its conclusion is
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpacesForgetToProduct`, which carries no tag.
Two things are missing, in this order.

1. *The fibre identification.* For a scheme-valued point of `ℋ_d(𝒳) × 𝒴` over `U` — that is, a
   degree-`d` finite locally free cover `Z ⟶ U`, an object `x` of `𝒳` over `Z` and an object `y`
   of `𝒴` over `U` — the 2-fibre product of `AlgebraicGeometry.Stack.forgetToProduct` with that
   point is the restriction of scalars `Res_{Z/U}(I)` of the Isom space
   `I = Isom_𝒴(y|_Z, F x)` produced by
   `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_isomPresheaf_cover`: an object of the fibre
   over `U' ⟶ U` is a choice of identification of `F x` with `y|_Z` after base change, i.e. a
   section over `U'` of `I ⟶ Z`. This is the analogue, for this 1-morphism, of
   `AlgebraicGeometry.Stack.FiniteHilbert.Object.nonempty_equivalenceOver_sectionSpace` in
   `StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FibreSectionSpace`, and it is the bulk of
   the work. It must not be carried as a hypothesis: a hypothesis identifying every fibre with a
   restriction of scalars, together with Stacks 05YF, is jointly equivalent to the conclusion,
   and would leave the diagonal hypothesis of Stacks 05YH unused.
2. *The 2-Yoneda normalisation over the product.* `AlgebraicGeometry.Stack` has the
   normalisation for 1-morphisms whose *target* is `ℋ_d(𝒳/𝒴)`; Stacks 05YH needs the one for
   1-morphisms whose target is `ℋ_d(𝒳) × 𝒴`, so that an arbitrary scheme-valued point of the
   product reduces to the universal family of an object of the product. The input is the same
   Stacks 02Y4 argument, applied to
   `AlgebraicGeometry.Stack.isFiberedInGroupoids_absoluteHilbertTargetProductProjection`.

Once both are available, Stacks 05YH follows with Stacks 05YF — that a restriction of scalars
along a finite locally free cover is an algebraic space — as its only carried input, which is
how the companion tag Stacks 05YJ is keyed.

## Implementation notes

The product is written as `CategoryTheory.BasedCategory.ofFunctor` of
`CategoryTheory.TwoFibreProductOver.structureFunctor` over `𝟭 (Sch/S)_fppf`, rather than as
`CategoryTheory.CatFiberedInGroupoids.product`, for the same reason as
`AlgebraicGeometry.Stack.HasRepresentableDiagonal`: that product asks its two factors to be
objects of one `CategoryTheory.CatFiberedInGroupoids`, hence to have the same object and
morphism universes, while `ℋ_d(𝒳)` is a structure built out of the site *and* `𝒳` and so lives
one universe higher than `𝒴`. The two constructions agree whenever the universes do.

`CategoryTheory.BasedCategory.ofFunctor` is semireducible, so the category instance on
`absoluteHilbertCategory.obj` is not the one instance search finds on
`AbsoluteHilbert.Object B S hS d 𝒳`; everything here is therefore stated with the projections
`absoluteHilbertCategory.p` and `finiteHilbertCategory.p` rather than with
`absoluteHilbertProjection` and `finiteHilbertProjection`, and the two based categories are made
`implicit_reducible` locally so that `rw` can operate on goals mentioning their objects.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 05YH](https://stacks.math.columbia.edu/tag/05YH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] BasedCategory.ofFunctor absoluteHilbertCategory
  finiteHilbertCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- The structure functor of the product `ℋ_d(𝒳) × 𝒴` over the big fppf site. -/
def absoluteHilbertTargetProductProjection :
    TwoFibreProductOver
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      𝒴.toBasedCategory.p (𝟭 (BigFppfOver B S hS))
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      𝒴.toBasedCategory.p ⥤ BigFppfOver B S hS :=
  TwoFibreProductOver.structureFunctor _ _ _ _ _

/-- The product `ℋ_d(𝒳) × 𝒴` as a category over the big fppf site. -/
def absoluteHilbertTargetProduct : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor
    (absoluteHilbertTargetProductProjection
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴))

/-- **The product `ℋ_d(𝒳) × 𝒴` is fibred in groupoids** over the big fppf site. -/
theorem isFiberedInGroupoids_absoluteHilbertTargetProductProjection :
    (absoluteHilbertTargetProductProjection
      (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    isFiberedInGroupoids_absoluteHilbertProjection
    𝒴.isStackInGroupoids.isFiberedInGroupoids Functor.isFiberedInGroupoids_id
    (Functor.comp_id _) (Functor.comp_id _)

/-- The comparison equality of the two legs of Equation 05WD: both are 1-morphisms over the
site with the same source, so the two composites into the site agree. -/
theorem forgetRelativeStructure_w_trans_forgetTarget_w_symm :
    (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)).toFunctor ⋙
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p =
    (forgetTarget (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)).toFunctor ⋙ 𝒴.toBasedCategory.p :=
  forgetRelativeStructure.w.trans forgetTarget.w.symm

/-- The comparison 2-cell of the pairing of the two legs of Equation 05WD is vertical: it is an
`eqToHom` of the site, whose source already lies over the base object. -/
theorem isHomLift_forgetProductComparison (P : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) :
    (𝟭 (BigFppfOver B S hS)).IsHomLift (𝟙 P.U)
      ((eqToIso (forgetRelativeStructure_w_trans_forgetTarget_w_symm
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F))).hom.app P) := by
  have h := Functor.congr_obj (forgetRelativeStructure_w_trans_forgetTarget_w_symm
    (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)) P
  rw [eqToIso.hom, eqToHom_app]
  exact IsHomLift.eqToHom_domain_lift_id h rfl

/-- **Stacks 05WD.** The 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of the equation: the pairing of
the two legs `AlgebraicGeometry.Stack.forgetRelativeStructure` and
`AlgebraicGeometry.Stack.forgetTarget`. -/
@[stacks 05WD "the 1-morphism of the equation, as the pairing of the two legs"]
noncomputable def forgetToProduct :
    finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) ⥤ᵇ
      absoluteHilbertTargetProduct
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) where
  toFunctor :=
    TwoFibreProductOver.lift
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      𝒴.toBasedCategory.p (𝟭 (BigFppfOver B S hS))
      (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
      𝒴.toBasedCategory.p
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
      (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)).toFunctor
      (forgetTarget (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)).toFunctor
      forgetRelativeStructure.w forgetTarget.w
      (eqToIso (forgetRelativeStructure_w_trans_forgetTarget_w_symm
        (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)))
      isHomLift_forgetProductComparison
  w := TwoFibreProductOver.lift_comp_structureFunctor ..

/-- **The first component of the 1-morphism of Equation 05WD is the first leg**: the pairing
followed by the projection to `ℋ_d(𝒳)` is
`AlgebraicGeometry.Stack.forgetRelativeStructure`, on the nose. -/
theorem forgetToProduct_comp_fst :
    (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)).toFunctor ⋙
      TwoFibreProductOver.fst
        (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
        𝒴.toBasedCategory.p (𝟭 (BigFppfOver B S hS))
        (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
        𝒴.toBasedCategory.p =
    (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
      (F := F)).toFunctor :=
  rfl

/-- **The second component of the 1-morphism of Equation 05WD is the second leg**: the pairing
followed by the projection to `𝒴` is `AlgebraicGeometry.Stack.forgetTarget`, on the nose. -/
theorem forgetToProduct_comp_snd :
    (forgetToProduct (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)).toFunctor ⋙
      TwoFibreProductOver.snd
        (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
        𝒴.toBasedCategory.p (𝟭 (BigFppfOver B S hS))
        (absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)).p
        𝒴.toBasedCategory.p =
    (forgetTarget (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)).toFunctor :=
  rfl

/-! ### The Isom space over the cover -/

/-- The image under `F` of the object of `𝒳` carried by an object of `ℋ_d(𝒳)` lies over the
cover. -/
theorem AbsoluteHilbert.Object.obj_map_over (P : AbsoluteHilbert.Object B S hS d 𝒳) :
    𝒴.toBasedCategory.p.obj (F.obj P.x) = P.Z :=
  (BasedFunctor.w_obj F P.x).trans P.x_over

/-- The target stack `𝒴`, viewed as an object of the 2-category of categories fibred in
groupoids over the big fppf site of `S`. -/
abbrev targetCFG : CatFiberedInGroupoids.{u, v₂, u + 1, u₂} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk 𝒴.toBasedCategory 𝒴.isStackInGroupoids.isFiberedInGroupoids

/-- **The Isom space of the proof of Stacks 05YH is an algebraic space over the cover.** Let
`P = (Z ⟶ U, x)` be an object of `ℋ_d(𝒳)` and let `yZ` be an object of `𝒴` over the cover `Z`
— for instance a restriction `y|_Z` of an object `y` of `𝒴` over `U`. If the diagonal of `𝒴` is
representable by algebraic spaces, then `Isom_𝒴(yZ, F x)` is an algebraic space over `Z`.

This is the one place where the hypothesis of Stacks 05YH on the diagonal of `𝒴` enters: it is
Stacks 045G, the equivalence of its conditions (1) and (2)
(`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`), read at
the cover `Z` and at the pair of objects of the fibre of `𝒴` over `Z` consisting of `yZ` and of
the image under `F` of the object of `𝒳` carried by `P`. -/
theorem exists_isAlgebraicSpace_isomPresheaf_cover [𝒴.toBasedCategory.p.IsFibered]
    (hΔ : HasRepresentableDiagonal B S hS (targetCFG (𝒴 := 𝒴)))
    (P : AbsoluteHilbert.Object B S hS d 𝒳) (yZ : 𝒴.toBasedCategory.obj)
    (hyZ : 𝒴.toBasedCategory.p.obj yZ = P.Z) :
    ∃ A : (BigFppfOver B P.Z.left.1 P.Z.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B P.Z.left.1 P.Z.left.2 A ∧
        Nonempty (A ⋙ uliftFunctor.{v₂, u} ≅
          ((Over.iteratedSliceBackward P.Z).op ⋙ 𝒴.toBasedCategory.p.isomPresheaf
              (Functor.Fiber.mk hyZ)
              (Functor.Fiber.mk (AbsoluteHilbert.Object.obj_map_over (𝒴 := 𝒴) (F := F) P))) ⋙
            uliftFunctor.{u, v₂}) :=
  (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS _).1 hΔ P.Z _ _

/-! ### The statement of Stacks 05YH -/

/-- **The conclusion of Stacks 05YH**, as a proposition: the 1-morphism
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 05WD is representable by algebraic spaces, in the sense of
Stacks 02ZW.

Stacks 05YH asserts this under the hypothesis
`AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS (AlgebraicGeometry.Stack.targetCFG)`,
that the diagonal `𝒴 ⟶ 𝒴 × 𝒴` is representable by algebraic spaces. **That implication is not
proved in this library**; this name records the goal, and the module documentation records
exactly what is missing. -/
abbrev IsRepresentableByAlgebraicSpacesForgetToProduct : Prop :=
  IsRepresentableByAlgebraicSpaces B S hS
    (forgetToProduct (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))

end AlgebraicGeometry.Stack

end
