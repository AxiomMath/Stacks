module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheafCondition
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.RestrictScalars
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of the derived-complete objects under restriction of scalars

Let `𝒞` be a site, let `𝒪 ⟶ 𝒪'` be a homomorphism of sheaves of commutative rings and let
`ℐ ⊂ 𝒪` be a sheaf of ideals. [Stacks, Tag 099C] asserts that the inverse image of
`D_comp(𝒪, ℐ)` under the restriction functor `D(𝒪') ⟶ D(𝒪)` is `D_comp(𝒪', ℐ𝒪')`. One
inclusion is
`Stacks.SheafOfModules.DerivedRestrictScalars.isDerivedComplete_restrictScalars_of_extendIdeal`
of `StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/RestrictScalars.lean`.
This file proves the other one and assembles the inverse-image equality.

## Main results

* `isDerivedCompleteAt_of_map_of_smul_id`: an additive functor which preserves countable
  products, reflects isomorphisms and matches two scalars reflects derived completeness at them.
* `Stacks.SheafOfModules.DerivedRestrictScalars.isDerivedCompleteAtSection_image`: if the
  restriction of `E` to `𝒪` satisfies `T(E|_U, f) = 0` for a section `f` of `𝒪` over `U`, then
  `E` itself satisfies `T(E|_U, f') = 0` for the image `f'` of `f` in `𝒪'`.
* `Stacks.SheafOfModules.DerivedRestrictScalars.isDerivedComplete_of_restrictScalars`: the
  inclusion the inverse image of `D_comp(𝒪, ℐ) ⊆ D_comp(𝒪', ℐ𝒪')`.
* `Stacks.SheafOfModules.DerivedRestrictScalars.isDerivedComplete_restrictScalars_iff`:
  **[Stacks, Tag 099C]**, the inverse image of `D_comp(𝒪, ℐ)` under restriction of scalars is
  `D_comp(𝒪', ℐ𝒪')`.

## Implementation notes

*The two steps.* A section of `ℐ𝒪'` over `U` is not in general the image of a section of `ℐ`,
since `ℐ𝒪'` is the *smallest* sheaf of ideals of `𝒪'` containing that image. So the inclusion
proved here splits into a sectionwise transfer and a closure statement.

1. *The transfer.* For `f` a section of `𝒪` over `U` with image `f'` in `𝒪'`, the two
   difference maps `1 - f·shift` and `1 - f'·shift` correspond through the comparison of the
   countable products of the two derived categories, which is invertible because restriction of
   scalars preserves those products
   (`Stacks.SheafOfModules.DerivedRestrictScalars.preservesProducts_mapDerivedCategory`). The
   forward inclusion reads that correspondence as transporting invertibility *along* the
   functor; here it is read backwards, so an extra input is needed: restriction of scalars on
   derived categories must *reflect* invertibility. That holds because restriction of scalars
   does not change the underlying sheaf of abelian groups
   (`Stacks.AlgebraicGeometry.QcohOverAlgebra.reflectsIsomorphisms_restrictScalars`) and an
   exact functor which reflects isomorphisms induces a conservative functor on derived
   categories (`CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory`).
2. *The closure.* The sections at which `E` is derived complete form a sheaf of ideals in `𝒪'`,
   which is [Stacks, Tag 0998] — `AlgebraicGeometry.RingedSite.derivedCompleteIdealSheaf`. Step
   1 says that this sheaf of ideals contains the image of `ℐ`, so by
   `AlgebraicGeometry.RingedSite.extendIdeal_le` it contains `ℐ𝒪'`; that is the conclusion.

*Universes.* As in `RestrictScalars.lean`, the statements are for a site `𝒞 : Type u` with
`Category.{u} 𝒞` and sheaves of modules in universe `u`, that is for `RingedSite.{u, u, u}`:
`Stacks.SheafOfModules.DerivedRestrictScalars.preservesProducts_mapDerivedCategory` is available
only there, and `AlgebraicGeometry.RingedSite.derivedCompleteIdealSheaf` is stated there too.

## References

* [Stacks Project, Tag 099C](https://stacks.math.columbia.edu/tag/099C)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 0924](https://stacks.math.columbia.edu/tag/0924)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

section Transfer

variable {A A' : Type*} [CommSemiring A] [CommSemiring A']
  {D D' : Type*} [Category D] [Category D'] [Preadditive D] [Preadditive D']
  [Linear A D] [Linear A' D'] [HasProductsOfShape ℕ D] [HasProductsOfShape ℕ D']

/-- `T(G L, a) = 0` implies `T(L, a') = 0` for an additive functor `G` which preserves countable
products, reflects isomorphisms, and takes multiplication by `a'` to multiplication by `a`. This
is the converse of `isDerivedCompleteAt_map_of_smul_id`: that lemma identifies `G (1 - a'·shift)`
with `1 - a·shift` on `G L` through the comparison of the countable products, so `T(G L, a) = 0`
makes `G (1 - a'·shift)` invertible, and a conservative `G` returns the invertibility of
`1 - a'·shift` itself. -/
theorem isDerivedCompleteAt_of_map_of_smul_id (G : D' ⥤ D) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G] [G.ReflectsIsomorphisms] {L : D'} {a' : A'} {a : A}
    (hsmul : G.map (a' • 𝟙 L) = a • 𝟙 (G.obj L)) (h : IsDerivedCompleteAt (G.obj L) a) :
    IsDerivedCompleteAt L a' :=
  have := AlgebraicGeometry.RingedSite.isIso_map_oneSubSmulShift_of_isDerivedCompleteAt G hsmul h
  isDerivedCompleteAt_iff_isIso.2 (isIso_of_reflects_iso (oneSubSmulShift L a') G)

end Transfer

namespace Stacks.SheafOfModules.DerivedRestrictScalars

open _root_.AlgebraicGeometry
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O O' : Sheaf J CommRingCat.{u}}

/-- **The sectionwise transfer of [Stacks, Tag 099C], in the direction of the converse
inclusion.** Let `f` be a section of `𝒪` over `U` and `f'` its image in `𝒪'`. If the restriction
of `E` to a complex of `𝒪`-modules satisfies `T(E|_U, f) = 0`, then `E` satisfies
`T(E|_U, f') = 0`.

Restriction of scalars commutes with restriction to the slice site over `U` and carries
multiplication by `f'` to multiplication by `f`, so the two difference maps `1 - f·shift`
correspond through the comparison of the countable products of the derived categories, which is
invertible. The hypothesis therefore makes the *image* of `1 - f'·shift` invertible, and
restriction of scalars on derived categories is conservative, so `1 - f'·shift` is itself
invertible. -/
theorem isDerivedCompleteAtSection_image (α : O ⟶ O')
    (E : DerivedCategory
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O').O))))
    (U : C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O)).obj.obj (op U))
    (hf : RingedSite.IsDerivedCompleteAtSection (ringedSite J O)
      ((_root_.SheafOfModules.restrictScalars.{u}
        (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj E) U f) :
    RingedSite.IsDerivedCompleteAtSection (ringedSite J O') E U
      ((ringSheafHom (O := O) (O' := O') α).hom.app (op U) f) := by
  let R := ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O)).over U
  let A := _root_.SheafOfModules.{u} R
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
  let : ∀ W : (Over U)ᵒᵖ, IsMulCommutative (R.obj.obj W) := fun W ↦ by
    show IsMulCommutative (O.obj.obj (op W.unop.left))
    infer_instance
  let R' := ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O').O)).over U
  let A' := _root_.SheafOfModules.{u} R'
  let : Linear (CatCenter A') A' := Linear.ofRingMorphism (RingHom.id (CatCenter A'))
  let : ∀ W : (Over U)ᵒᵖ, IsMulCommutative (R'.obj.obj W) := fun W ↦ by
    show IsMulCommutative (O'.obj.obj (op W.unop.left))
    infer_instance
  have hProd : HasProductsOfShape ℕ (DerivedCategory A) :=
    RingedSite.hasProductsOfShape_nat_derivedCategory_over.{u, u, u} (ringedSite J O) U
  have hProd' : HasProductsOfShape ℕ (DerivedCategory A') :=
    RingedSite.hasProductsOfShape_nat_derivedCategory_over.{u, u, u} (ringedSite J O') U
  have hLim : PreservesFiniteLimits
      (_root_.SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O)) U) :=
    _root_.Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U
  have hColim : PreservesFiniteColimits
      (_root_.SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O)) U) :=
    _root_.Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U
  have hLim' : PreservesFiniteLimits
      (_root_.SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O').O)) U) :=
    _root_.Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U
  have hColim' : PreservesFiniteColimits
      (_root_.SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O').O)) U) :=
    _root_.Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U
  let φ :=(J.overPullback RingCat.{u} U).map (ringSheafHom (O := O) (O' := O') α)
  let AU := _root_.SheafOfModules.restrictScalars.{u} φ
  have hpres : PreservesLimitsOfShape (Discrete ℕ) AU.mapDerivedCategory :=
    preservesProducts_mapDerivedCategory ((J.overPullback CommRingCat.{u} U).map α)
  have hreflAU : AU.ReflectsIsomorphisms :=
    AlgebraicGeometry.QcohOverAlgebra.reflectsIsomorphisms_restrictScalars φ
  have hrefl : AU.mapDerivedCategory.ReflectsIsomorphisms :=
    Functor.reflectsIsomorphisms_mapDerivedCategory AU
  have hsmul := mapDerivedCategory_map_smul_id AU
    (show CatCenter (_root_.SheafOfModules.{u} R') from
      Stacks.SheafOfModules.terminalSectionToEnd R' (Over.mk (𝟙 U)) Over.mkIdTerminal
        (φ.hom.app (op (Over.mk (𝟙 U))) f))
    (show CatCenter (_root_.SheafOfModules.{u} R) from
      Stacks.SheafOfModules.terminalSectionToEnd R (Over.mk (𝟙 U)) Over.mkIdTerminal f)
    (fun Z => by
      refine HomologicalComplex.hom_ext _ _ fun n => ?_
      show AU.map ((Stacks.SheafOfModules.terminalSectionToEnd R' (Over.mk (𝟙 U))
            Over.mkIdTerminal (φ.hom.app (op (Over.mk (𝟙 U))) f)).asHom.app (Z.X n) ≫ 𝟙 (Z.X n)) =
          (Stacks.SheafOfModules.terminalSectionToEnd R (Over.mk (𝟙 U)) Over.mkIdTerminal
            f).asHom.app (AU.obj (Z.X n)) ≫ 𝟙 (AU.obj (Z.X n))
      refine (congrArg (fun g => AU.map g) (Category.comp_id _)).trans ?_
      exact (RingedSite.restrictScalars_map_terminalSectionToEnd φ
        (Over.mk (𝟙 U)) Over.mkIdTerminal f (Z.X n)).trans (Category.comp_id _).symm)
  exact isDerivedCompleteAt_of_map_of_smul_id AU.mapDerivedCategory (hsmul _)
    ((RingedSite.isDerivedCompleteAt_iff_of_iso
      (((mapDerivedCategoryCompIso
          (_root_.SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O').O)) U)
          AU).app E).symm ≪≫
        (mapDerivedCategoryCompIso
          (_root_.SheafOfModules.restrictScalars.{u} (ringSheafHom (O := O) (O' := O') α))
          (_root_.SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O)) U)).app E) _).mpr hf)

/-- **[Stacks, Tag 099C], the inclusion `D_comp(𝒪', ℐ𝒪') ⊇` the inverse image of
`D_comp(𝒪, ℐ)`.** A complex of `𝒪'`-modules whose restriction to a complex of `𝒪`-modules is
derived complete along a sheaf of ideals `ℐ ⊂ 𝒪` is itself derived complete along the extension
`ℐ𝒪'`.

The sections of `𝒪'` at which `E` is derived complete form a sheaf of ideals
(`AlgebraicGeometry.RingedSite.derivedCompleteIdealSheaf`, [Stacks, Tag 0998]), and
`isDerivedCompleteAtSection_image` says that it contains the image of `ℐ`. Since `ℐ𝒪'` is the
smallest sheaf of ideals of `𝒪'` containing that image
(`AlgebraicGeometry.RingedSite.extendIdeal_le`), it contains `ℐ𝒪'`. -/
theorem isDerivedComplete_of_restrictScalars (α : O ⟶ O')
    (I : _root_.SheafOfModules.Submodule
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))))
    (E : DerivedCategory
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O').O))))
    (h : RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O) I
      ((_root_.SheafOfModules.restrictScalars.{u}
        (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj E)) :
    RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O')
      (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I) E := by
  rw [RingedSite.isDerivedComplete_iff_forall_isDerivedCompleteAtSection] at h ⊢
  have hle : RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I ≤
      RingedSite.derivedCompleteIdealSheaf (ringedSite J O') E :=
    RingedSite.extendIdeal_le (ringSheafHom (O := O) (O' := O') α) I _ fun V g hg ↦
      (RingedSite.mem_derivedCompleteIdealSheaf_iff (ringedSite J O') E V.unop _).2
        (isDerivedCompleteAtSection_image α E V.unop g (h V.unop g hg))
  intro U g hg
  exact (RingedSite.mem_derivedCompleteIdealSheaf_iff (ringedSite J O') E U g).1
    (PresheafOfModules.Submodule.le_iff.mp
      (_root_.SheafOfModules.Submodule.le_iff.mp hle) (op U) hg)

/-- **[Stacks, Tag 099C].** For a homomorphism `𝒪 ⟶ 𝒪'` of sheaves of commutative rings on a
site and a sheaf of ideals `ℐ ⊂ 𝒪`, a complex of `𝒪'`-modules restricts to a complex of
`𝒪`-modules derived complete along `ℐ` if and only if it is derived complete along `ℐ𝒪'`. That
is, the inverse image of `D_comp(𝒪, ℐ)` under the restriction functor `D(𝒪') ⟶ D(𝒪)` is
`D_comp(𝒪', ℐ𝒪')`. -/
@[stacks 099C]
theorem isDerivedComplete_restrictScalars_iff (α : O ⟶ O')
    (I : _root_.SheafOfModules.Submodule
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O).O))))
    (E : DerivedCategory
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite J O').O)))) :
    RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O) I
        ((_root_.SheafOfModules.restrictScalars.{u}
          (ringSheafHom (O := O) (O' := O') α)).mapDerivedCategory.obj E) ↔
      RingedSite.IsDerivedComplete.{u, u, u, u} (ringedSite J O')
        (RingedSite.extendIdeal (ringSheafHom (O := O) (O' := O') α) I) E :=
  ⟨isDerivedComplete_of_restrictScalars α I E,
    isDerivedComplete_restrictScalars_of_extendIdeal α I E⟩

end Stacks.SheafOfModules.DerivedRestrictScalars

end
