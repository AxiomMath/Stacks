module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackIncl
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerSucc

/-!
# The pullback comparison respects the ideal inclusion in every integer degree

Let `f : X ⟶ Y` be a morphism of ringed spaces, `I` an invertible sheaf of `𝒪_Y`-modules and
`ι : I ⟶ 𝒪_Y`. `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullback` constructs the
interchange `f^*(I^{⊗ n} ⊗ M) ≅ (f^*I)^{⊗ n} ⊗ f^*M` in every integer degree, and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackIncl` proves that the degree-`1`
comparison of Stacks 01CD carries the degree-`0` ideal inclusion on `Y` to the one on `X`. This
file puts the two together: the interchange respects the inclusion of consecutive ideal powers
in **every integer degree**, which is the square the degreewise comparison of décalages needs.

Nothing new is proved about the comparison here. The whole content is
`Stacks.Equivalence.powIntertwineObj_incl`, which lifts the degree-`0` compatibility to every
integer degree; what this file supplies is the data that transport takes — the ideal inclusion
as a natural transformation `- ⊗ I ⟶ 𝟭` — and the observation that the interchange and the
inclusions are exactly the transport's output, with no conversion.

## Main definitions

* `Stacks.IdealTorsion.Eta.idealInclNatTrans`: **the ideal inclusion as a natural transformation**
  `- ⊗ I ⟶ 𝟭`.

## Main results

* `Stacks.IdealTorsion.Eta.tensorRightFunctor_map_toTensorSheafSection`: tensoring a morphism on
  the right by `I`, on the sheafification-unit image of a pure tensor.
* `Stacks.IdealTorsion.Eta.idealPowerIncl_zero_natural`: **the degree-`0` ideal inclusion is
  natural in the module.**
* `Stacks.IdealTorsion.Eta.map_idealPowerIncl`: **the interchange of a pullback with an integer
  invertible ideal power respects the inclusion of consecutive ideal powers, in every integer
  degree.**

## Implementation notes

**Why the inclusion is written out rather than as `idealPowerIncl`.** The transport's conclusion
is stated in terms of `(powSuccIso e n M).inv ≫ a.app ((e ^ n) M)`, and `idealPowerIncl Z I ι n M`
*is* that composite — but only up to the identity morphism that the degree-`0` successor
comparison contributes, since `powSuccIso e 0 P` is `Iso.refl` and `a.app P` is
`idealPowerIncl Z I ι 0 P = 𝟙 ≫ (ι ⊗ 1) ≫ (right unitor)`. Removing that `𝟙` is
`Category.id_comp`, which is a *proof* in a general category, not a reduction; discharging it
here means checking a definitional equality that unfolds `idealPowerIncl` and then the
composition of `SheafOfModules`, `PresheafOfModules` and `ModuleCat` down to `LinearMap.comp`.
That check exceeds the default heartbeat limit in each of the following three spellings
(`rfl` on the unfolded definition; the same with the equivalence instance written exactly as
`idealPowerIncl`'s body writes it; and `(Category.id_comp _).symm` inside the naturality field).
Raising the limit is not permitted in this file, so `map_idealIncl` is stated in the transport's
own spelling, where it is the transport's conclusion verbatim and needs no conversion at all.

Restating `map_idealIncl` with `idealPowerIncl Y I ι n M` on the left and
`idealPowerIncl X (f^*I) (f^*ι) n (f^*M)` on the right is therefore pure bookkeeping, and the one
input it needs is

`idealPowerIncl Z I ι n M = (powSuccIso e n M).inv ≫ idealPowerIncl Z I ι 0 (I^{⊗ n} ⊗ M)`,

which is `Category.id_comp` at the degree-`0` successor comparison. It belongs next to
`idealPowerIncl` itself, where the definition is in scope and the heartbeat budget can be set.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
-/

@[expose] public section

/- The same locally-unfoldable links as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullback`: without them instance search
does not see through the spelling `structureSheaf Z.sheaf` of the structure sheaf of rings. -/
attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory

open scoped TensorProduct

open Stacks.SheafOfModules.Invertible (
  tensorProductRightUnitor)

open Stacks.RingedSpace (pullbackFunctor comparisonBifunctorIso structureRingSheaf)

open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)

universe u

namespace Stacks.IdealTorsion.Eta

/- The monoidal structure of Tag 01CA, which is the one the section formulas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence` are stated over. -/
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable (Z : RingedSpace.{u})

/-- **Tensoring a morphism on the right by `I`, on the sheafification-unit image of a pure
tensor.** It acts on the first factor and leaves the second alone, which is the naturality of
the sheafification unit at the presheaf-level right whiskering. -/
theorem tensorRightFunctor_map_toTensorSheafSection
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
    {M N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))} (g : M ⟶ N)
    (U : (Opens Z.carrier)ᵒᵖ) (m : M.val.obj U) (b : I.val.obj U) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).flip.obj I).map
        g).val.app U).hom
        (toTensorSheafSection Z M I U (m ⊗ₜ[Z.presheaf.obj U] b)) =
      toTensorSheafSection Z N I U ((g.val.app U).hom m ⊗ₜ[Z.presheaf.obj U] b) := by
  let adj := (PresheafOfModules.sheafificationAdjunction.{u}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))).obj))
  -- The naturality square of the sheafification unit, read on the pure tensor. The goal is not
  -- type-correct at `implicit` transparency, so the section is extracted with `congrArg` and
  -- the two spellings of the tensor product are crossed by `exact`.
  exact (congrArg (fun k => (k.app U).hom (m ⊗ₜ[Z.presheaf.obj U] b))
    (adj.unit.naturality (g.val ▷ I.val))).symm

/-- **The degree-`0` ideal inclusion is natural in the module.** Both sides are morphisms out of
a tensor product sheaf, hence determined by their values on the local pure tensors; there the
left-hand side applies `g` to the first factor and then multiplies by the ideal section, and the
right-hand side multiplies first, the two agreeing by the semilinearity of `g`. -/
theorem idealPowerIncl_zero_natural
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))).property I]
    {M N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))} (g : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).flip.obj I).map g ≫
        idealPowerIncl Z I ι 0 N = idealPowerIncl Z I ι 0 M ≫ g :=
  (idealPowerIncl_natural Z I ι 0 g).symm

/-- **The ideal inclusion as a natural transformation** `- ⊗ I ⟶ 𝟭`, whose component at `M` is
the degree-`0` ideal inclusion. This is the datum `a` that
`Stacks.Equivalence.powIntertwineObj_incl` takes, and from which the inclusion in every integer
degree is built. -/
noncomputable def idealInclNatTrans
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))).property I] :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).flip.obj I ⟶
      𝟭 (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))) where
  app M := idealPowerIncl Z I ι 0 M
  naturality _ _ g := idealPowerIncl_zero_natural Z I ι g

/-- The component of `idealInclNatTrans` is the degree-`0` ideal inclusion, by construction. -/
theorem idealInclNatTrans_app
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))).property I]
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))) :
    (idealInclNatTrans Z I ι).app M = idealPowerIncl Z I ι 0 M :=
  rfl

/-! ### The compatibility in every integer degree -/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- Tensoring on the right by an invertible module is an equivalence, restated at the spelling
of the structure sheaf used by `EtaSheaf.lean` so that instance search finds it without
unfolding. This is the same declaration, for the same reason, as the one in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullback`, which is `private` there and so
is not in scope here. -/
private noncomputable instance isEquivalence_tensorRightFunctorObj' (W : RingedSpace.{u})
    (L : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk W.presheaf W.IsSheaf))))
    [Stacks.SheafOfModules.IsInvertible W.sheaf.obj ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk W.presheaf W.IsSheaf))).property L] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (CategoryTheory.ObjectProperty.FullSubcategory.mk W.presheaf W.IsSheaf)).flip.obj
        L).IsEquivalence :=
  Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence W.sheaf.obj
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk W.presheaf W.IsSheaf))).property L

/-- **The interchange of a pullback with an integer invertible ideal power respects the
inclusion of consecutive ideal powers, in every integer degree.**

This is `Stacks.Equivalence.powIntertwineObj_incl` instantiated at the two tensor
autoequivalences, the pullback functor, the canonical comparison of Stacks 01CD as the
degree-`1` comparison, and `idealInclNatTrans` on `Y` and on `X` as the two natural
transformations to the identity. Its hypothesis `ha` — that the comparison carries the one
inclusion to the other — is
`Stacks.IdealTorsion.Eta.comparisonBifunctorIso_app_hom_comp_idealPowerIncl_zero`, the
degree-`0` case; no further input is needed, since the transport supplies every other degree.

The inclusion is written here as the successor comparison followed by `idealInclNatTrans`, which
is the form the transport produces. That composite is `idealPowerIncl Y I ι n M` up to the
identity contributed by the degree-`0` successor comparison; see the implementation notes. The
interchange itself needs no conversion: `pullbackIdealPowerIso` *is*
`Stacks.Equivalence.powIntertwineObj` at this data, by definition. -/
theorem map_idealIncl
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Y.presheaf Y.IsSheaf))))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Y.presheaf Y.IsSheaf))))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Y.presheaf Y.IsSheaf))).property I]
    (n : ℤ) (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Y.presheaf Y.IsSheaf)))) :
    (pullbackFunctor f).map
        ((Stacks.Equivalence.powSuccIso
            (@Functor.asEquivalence _ _ _ _
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                (CategoryTheory.ObjectProperty.FullSubcategory.mk Y.presheaf Y.IsSheaf)).flip.obj I)
              (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence Y.sheaf.obj
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  (CategoryTheory.ObjectProperty.FullSubcategory.mk Y.presheaf Y.IsSheaf)).property
                    I))
            n M).inv ≫
          (idealInclNatTrans Y I ι).app
            (((@Functor.asEquivalence _ _ _ _
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                (CategoryTheory.ObjectProperty.FullSubcategory.mk Y.presheaf Y.IsSheaf)).flip.obj I)
              (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence Y.sheaf.obj
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  (CategoryTheory.ObjectProperty.FullSubcategory.mk Y.presheaf Y.IsSheaf)).property
                    I))
              ^ n).functor.obj M)) ≫
        (pullbackIdealPowerIso f I n M).hom =
      (pullbackIdealPowerIso f I (n + 1) M).hom ≫
        (Stacks.Equivalence.powSuccIso
            (@Functor.asEquivalence _ _ _ _
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj
                  ((pullbackFunctor f).obj I))
              (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence X.sheaf.obj
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).property
                    ((pullbackFunctor f).obj I)))
            n ((pullbackFunctor f).obj M)).inv ≫
          (idealInclNatTrans X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)).app
            (((@Functor.asEquivalence _ _ _ _
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj
                  ((pullbackFunctor f).obj I))
              (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence X.sheaf.obj
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).property
                    ((pullbackFunctor f).obj I)))
              ^ n).functor.obj
                ((pullbackFunctor f).obj M)) :=
  Stacks.Equivalence.powIntertwineObj_incl
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk Y.presheaf Y.IsSheaf)).flip.obj I)
      (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence Y.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk Y.presheaf Y.IsSheaf)).property
            I))
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj
          ((pullbackFunctor f).obj I))
      (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).property
            ((pullbackFunctor f).obj I)))
    (pullbackFunctor f)
    (fun P ↦ (comparisonBifunctorIso f).app (P, I))
    (idealInclNatTrans Y I ι)
    (idealInclNatTrans X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι))
    (fun P ↦ comparisonBifunctorIso_app_hom_comp_idealPowerIncl_zero f I ι P) n M

end Stacks.IdealTorsion.Eta

end
