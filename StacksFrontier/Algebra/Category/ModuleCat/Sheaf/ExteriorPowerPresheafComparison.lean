module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymExtPowFunctorial

/-!
# The exterior-power comparison of Tag 01CG for a presheaf source

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `A` a sheaf of graded
algebras over the underlying sheaf of rings, carrying a square-zero degree-one generator.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison` builds the comparison
morphism `Stacks.GradedAlgebra.extCmp` out of the presheaf of sectionwise exterior powers of an
arbitrary presheaf of `O♯`-modules `F`, and identifies it with the sheafification unit followed by
a degreewise isomorphism — but **only when `F` is the presheaf of sections `M.val` of a sheaf of
modules `M`** and `A` is an exterior algebra of that `M`
(`SheafOfModules.extPowCmp_eq_sheafifyUnit_comp`).

This file removes that restriction. For an arbitrary presheaf of modules `F` and a graded algebra
`A` that is an exterior algebra of the **sheafification** of `F`, the comparison morphism out of
`PresheafOfModules.extPow n F` is again the sheafification unit followed by a degreewise
isomorphism, hence locally injective. The sheaf case is recovered by taking `F := M.val`, whose
sheafification is `M` up to `SheafOfModules.sheafifySectionsIso`.

The reason the general form is needed is that the comparisons arising in practice have a presheaf
source that is *not* of the form `M.val`: the presheaf of sectionwise Kähler differentials of a
morphism of sheaves of rings is one, and the de Rham differential of Tag 0FKM is descended along
the comparison morphism out of its exterior powers.

## Main definitions

* `SheafOfModules.exteriorDescPresheaf`: the unital homomorphism of sheaves of graded algebras
  from the sheafified sectionwise exterior algebra of a presheaf of modules `F` to any exterior
  algebra of the sheafification of `F`.
* `SheafOfModules.exteriorPieceIsoPresheaf`: its degreewise isomorphism.

## Main results

* `Stacks.GradedAlgebra.GenSquareZero.comp`: a square-zero degree-one generator stays square-zero
  when precomposed with a morphism of presheaves of modules. This is the presheaf-level
  counterpart of `SheafOfModules.GradedAlgebra.squareZero_comp`.
* `Stacks.GradedAlgebra.extPowMap_comp_extCmp`: **the comparison morphism is natural in the
  source presheaf.** Precomposing with `PresheafOfModules.extPowMap n f` is the same as
  precomposing the degree-one generator with `f`. This is what reduces a composite
  `extPow n G ⟶ extPow n F ⟶ A.piece n` to a single comparison morphism.
* `SheafOfModules.exteriorDescPresheaf_gen`: the comparison homomorphism carries the degree-one
  generator of the sheafified sectionwise exterior algebra, read on the unit-image of a local
  section of `F`, to the given degree-one generator of `A`.
* `SheafOfModules.extCmp_eq_sheafifyUnit_comp`: **the comparison morphism out of the sectionwise
  exterior powers of an arbitrary presheaf of modules is the sheafification unit followed by a
  degreewise isomorphism.** This is `SheafOfModules.extPowCmp_eq_sheafifyUnit_comp` with the
  hypothesis that the source is the presheaf of sections of a sheaf of modules removed.
* `SheafOfModules.isLocallyInjective_extCmp`: **that comparison morphism is locally injective.**
  Local injectivity does not follow from the spanning argument that gives local surjectivity; it
  is exactly what the factorization above supplies.

## Implementation notes

**What is general and what is pinned.** `Stacks.GradedAlgebra.extPowMap_comp_extCmp` holds for a
general site, a general presheaf of commutative rings and the module universe `max w a` of
`PresheafOfModules.extPow`, exactly as the comparison morphism itself does. The identification
with the sheafification unit is pinned to the equal-universe case `GradedAlgebra.{w, w}`, because
`SheafOfModules.sectionwiseExteriorAlgebra` and
`SheafOfModules.isExteriorAlgebra_sectionwiseExteriorAlgebra` exist only there; this is the same
pin `ExteriorPowerComparison` records, and nothing is narrowed relative to it.

**The scalar morphism is the identity, and that is forced, not chosen.** The sheafification
morphism of the ring presheaf is `𝟙 O♯.obj`: `PresheafOfModules.extPow n F` and `(A.piece n).val`
must be presheaves of modules over the *same* presheaf of rings for the comparison morphism to be
a morphism of presheaves of modules at all, and `A` lives over `CategoryTheory.Sheaf.toRingCat J
O♯`. Written with a general scalar morphism `a : O ⟶ O♯.obj` the statement does not even typecheck
— `PresheafOfModules.sheafifyRestrict` carries a `PresheafOfModules.restrictScalars a` that the
degreewise isomorphism does not, and the two agree only for `a = 𝟙`.

**The relation between the two generators is a hypothesis, not a construction.** The presheaf-level
generator `gen : F ⟶ (A.piece 1).val` and the sheaf-level generator
`g : (moduleSheafification J (𝟙 O♯.obj)).obj F ⟶ A.piece 1` are related by
`SheafOfModules.extCmp_eq_sheafifyUnit_comp`'s hypothesis `hcompat`, which says that `g` read on
the unit-image of a local section is `gen`. Taking `gen` to be the composite of the unit with `g`
would force the `PresheafOfModules.sheafifyRestrict` spelling on the source of `gen`, and the
consumers hold a morphism whose ascribed codomain is a `.val`; stating the compatibility
elementwise lets a consumer discharge it by `rfl`.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Sheaf

universe v u w a

namespace Stacks.GradedAlgebra

/-! ### Naturality of the comparison morphism in the source presheaf -/

section Naturality

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (A : Stacks.GradedAlgebra Pc) {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (gen : F ⟶ Pc 1)

/-- A square-zero degree-one generator stays square-zero when precomposed with a morphism of
presheaves of modules: the sections in the image of `f ≫ gen` are among those in the image of
`gen`. This is the presheaf-level counterpart of
`SheafOfModules.GradedAlgebra.squareZero_comp`. -/
theorem GenSquareZero.comp (hs : A.GenSquareZero gen) (f : G ⟶ F) :
    A.GenSquareZero (f ≫ gen) :=
  fun X x => hs X (f.app X x)

/-- **The comparison morphism is natural in the source presheaf of modules.** Composing the
sectionwise exterior power of `f : G ⟶ F` with the comparison morphism determined by a generator
`gen : F ⟶ Pc 1` gives the comparison morphism determined by `f ≫ gen`.

Both sides are determined by their values on wedges of `n` degree-one generators
(`ExteriorAlgebra.powExtₛₗ`), where `PresheafOfModules.extPowMap` carries a wedge to the wedge of
the images (`PresheafOfModules.extPowMap_app_ιMulti`) and the comparison carries a wedge to the
ordered product of the images of its factors
(`Stacks.GradedAlgebra.extCmpSections_ιMulti`). -/
theorem extPowMap_comp_extCmp (hs : A.GenSquareZero gen) (n : ℕ) (f : G ⟶ F) :
    PresheafOfModules.extPowMap n f ≫ A.extCmp gen hs n =
      A.extCmp (f ≫ gen) (GenSquareZero.comp A gen hs f) n := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext ?_
  refine ExteriorAlgebra.powExtₛₗ fun s => ?_
  have h1 : PresheafOfModules.extPowSections n F X
      ((PresheafOfModules.extPowMap n f).app X
        (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n s)) =
      exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n fun i => f.app X (s i) := by
    refine Subtype.ext ?_
    refine Eq.trans (PresheafOfModules.extPowMap_app_ιMulti n f X s _
      (exteriorPower.ιMulti_apply_coe _ n s)) ?_
    exact (exteriorPower.ιMulti_apply_coe _ n _).symm
  refine Eq.trans (congrArg (A.extCmpSections gen hs n X) h1) ?_
  refine Eq.trans (A.extCmpSections_ιMulti gen hs n X _) ?_
  exact (A.extCmpSections_ιMulti (f ≫ gen) (GenSquareZero.comp A gen hs f) n X s).symm

end Naturality

end Stacks.GradedAlgebra

namespace SheafOfModules

open PresheafOfModules CategoryTheory.Sheaf

/-! ### The comparison morphism out of an arbitrary presheaf of modules -/

section PresheafComparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (Osharp.obj ⋙ forget₂ CommRingCat RingCat))
  (A : GradedAlgebra.{w, w} (toRingCat J Osharp))
  (g : (moduleSheafification J (𝟙 Osharp.obj)).obj F ⟶ A.piece 1)
  (gen : F ⟶ (A.piece 1).val)

/-- **The comparison homomorphism of sheaves of graded algebras** from the sheafified sectionwise
exterior algebra of a presheaf of modules `F` to an exterior algebra `A` of the sheafification of
`F`. It is the unique unital homomorphism carrying one degree-one generator to the other.

This is `SheafOfModules.exteriorDesc` with the source presheaf no longer required to be the
presheaf of sections of a sheaf of modules; there the transport along
`SheafOfModules.sheafifySectionsIso` is what makes `A` an exterior algebra of the sheafification,
and here that is the hypothesis `hA`. -/
noncomputable def exteriorDescPresheaf (hA : GradedAlgebra.IsExteriorAlgebra A g) :
    GradedAlgebra.UnitalHom (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) F) A :=
  (isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) F).desc A g hA.1

/-- **The degreewise isomorphism** between the sheafified sectionwise exterior powers of a
presheaf of modules `F` and the homogeneous pieces of an exterior algebra of the sheafification of
`F`: two sheaves of graded algebras universal for square-zeroness of the degree-one generator are
isomorphic in every degree. -/
noncomputable def exteriorPieceIsoPresheaf (hA : GradedAlgebra.IsExteriorAlgebra A g) (n : ℤ) :
    (sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) F).piece n ≅ A.piece n :=
  (isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) F).pieceIso hA n

/-- The forward map of `SheafOfModules.exteriorPieceIsoPresheaf` in degree `n` is the degree-`n`
component of `SheafOfModules.exteriorDescPresheaf`. -/
theorem exteriorPieceIsoPresheaf_hom (hA : GradedAlgebra.IsExteriorAlgebra A g) (n : ℤ) :
    (exteriorPieceIsoPresheaf F A g hA n).hom = (exteriorDescPresheaf F A g hA).app n := rfl

/-- The comparison homomorphism carries the degree-one generator of the sheafified sectionwise
exterior algebra to the degree-one generator of `A`, on the unit-image of a local section of the
source presheaf. -/
theorem exteriorDescPresheaf_gen (hA : GradedAlgebra.IsExteriorAlgebra A g)
    (hcompat : ∀ (X : Cᵒᵖ) (m : F.obj X),
      g.val.app X (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) F) X m) = gen.app X m)
    (X : Cᵒᵖ) (m : F.obj X) :
    ((exteriorDescPresheaf F A g hA).app 1).val.app X
        ((sectionwiseExteriorAlgebraGen J (𝟙 Osharp.obj) F).val.app X
          (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) F) X m)) =
      gen.app X m :=
  (_root_.SheafOfModules.hom_congr_app_apply
    ((isExteriorAlgebra_sectionwiseExteriorAlgebra J (𝟙 Osharp.obj) F).desc_extends A g hA.1)
    X _).trans (hcompat X m)

/-- **The comparison morphism of Tag 01CG out of an arbitrary presheaf of modules is the
sheafification unit followed by a degreewise isomorphism.**

Both sides are determined by their values on wedges of `n` degree-one generators
(`ExteriorAlgebra.powExtₛₗ`). There the left-hand side is the ordered product of the images of
those generators under `gen` (`Stacks.GradedAlgebra.extCmpSections_ιMulti`), and the right-hand
side is the image under the comparison homomorphism of the ordered product of the unit-images
(`SheafOfModules.sheafifyUnit_extPow_ιMulti`), which is the same ordered product because a unital
homomorphism preserves ordered products
(`SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd`) and carries one generator to the
other (`SheafOfModules.exteriorDescPresheaf_gen`).

This is `SheafOfModules.extPowCmp_eq_sheafifyUnit_comp` for a source presheaf that need not be
the presheaf of sections of a sheaf of modules. -/
theorem extCmp_eq_sheafifyUnit_comp
    (hgen : Stacks.GradedAlgebra.GenSquareZero A.toPresheafGradedAlgebra gen)
    (hA : GradedAlgebra.IsExteriorAlgebra A g)
    (hcompat : ∀ (X : Cᵒᵖ) (m : F.obj X),
      g.val.app X (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) F) X m) = gen.app X m)
    (n : ℕ) :
    A.toPresheafGradedAlgebra.extCmp gen hgen n =
      sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (extPow n F) ≫
        (_root_.SheafOfModules.forget (toRingCat J Osharp)).map
          (exteriorPieceIsoPresheaf F A g hA (n : ℤ)).hom := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext ?_
  refine ExteriorAlgebra.powExtₛₗ fun s => ?_
  refine Eq.trans (Stacks.GradedAlgebra.extCmpSections_ιMulti A.toPresheafGradedAlgebra gen
    hgen n X s) ?_
  refine Eq.symm (Eq.trans (congrArg
    (fun z => ((exteriorDescPresheaf F A g hA).app (n : ℤ)).val.app X z)
    (sheafifyUnit_extPow_ιMulti (𝟙 Osharp.obj) F n X s)) ?_)
  refine Eq.trans (GradedAlgebra.UnitalHom.app_homogeneousProd
    (exteriorDescPresheaf F A g hA) X n _) ?_
  exact congrArg (A.toPresheafGradedAlgebra.homogeneousProd X n)
    (funext fun i => exteriorDescPresheaf_gen F A g gen hA hcompat X (s i))

/-- **The comparison morphism of Tag 01CG out of an arbitrary presheaf of modules is locally
injective.** A sheafification unit is locally injective and an isomorphism is locally injective,
so the factorization `SheafOfModules.extCmp_eq_sheafifyUnit_comp` gives it.

This does not follow from the local surjectivity of the comparison, which is a spanning argument:
local injectivity is a genuinely different statement, and the factorization is what supplies
it. -/
theorem isLocallyInjective_extCmp
    (hgen : Stacks.GradedAlgebra.GenSquareZero A.toPresheafGradedAlgebra gen)
    (hA : GradedAlgebra.IsExteriorAlgebra A g)
    (hcompat : ∀ (X : Cᵒᵖ) (m : F.obj X),
      g.val.app X (Hom.app (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) F) X m) = gen.app X m)
    (n : ℕ) :
    Presheaf.IsLocallyInjective J
      ((toPresheaf (toRingCat J Osharp).obj).map
        (A.toPresheafGradedAlgebra.extCmp gen hgen n)) := by
  have hfac : (toPresheaf (toRingCat J Osharp).obj).map
        (sheafifyUnit (toRingCatMap J (𝟙 Osharp.obj)) (extPow n F)) ≫
      (toPresheaf (toRingCat J Osharp).obj).map
        ((_root_.SheafOfModules.forget (toRingCat J Osharp)).map
          (exteriorPieceIsoPresheaf F A g hA (n : ℤ)).hom) =
      (toPresheaf (toRingCat J Osharp).obj).map
        (A.toPresheafGradedAlgebra.extCmp gen hgen n) :=
    ((toPresheaf (toRingCat J Osharp).obj).map_comp _ _).symm.trans
      (congrArg (fun h => (toPresheaf (toRingCat J Osharp).obj).map h)
        (extCmp_eq_sheafifyUnit_comp F A g gen hgen hA hcompat n).symm)
  have hiso : Presheaf.IsLocallyInjective J
      ((toPresheaf (toRingCat J Osharp).obj).map
        ((_root_.SheafOfModules.forget (toRingCat J Osharp)).map
          (exteriorPieceIsoPresheaf F A g hA (n : ℤ)).hom)) := inferInstance
  exact Stacks.TensorCoherence.isLocallyInjective_of_fac _ _ hfac inferInstance hiso

end PresheafComparison

end SheafOfModules

end
