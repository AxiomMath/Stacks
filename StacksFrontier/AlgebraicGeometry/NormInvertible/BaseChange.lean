module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.ChartGeneratorRatio
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Recognition
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorAdditive
public import StacksFrontier.AlgebraicGeometry.NormBaseChange.Rank
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper

/-!
# The norm of an invertible module commutes with base change

Consider a cartesian square of schemes
```
X' --g'--> X
|f'        |f
v          v
Y' --g-->  Y
```
with `f` finite, carrying a norm `N` on functions, and `f'` carrying a norm `N'` compatible with
`N` around the square: `N'(g'^♯ s) = g^♯ (N s)`. Then for every invertible `𝒪_X`-module `ℒ`

  `g^*(Norm_f ℒ) ≅ Norm_{f'}(g'^*ℒ)`.

For the canonical norm of a finite locally free morphism of constant rank `d > 0` (Tag 0BD2) the
compatibility is the base-change clause of that tag,
`Stacks.Divisors.finiteLocallyFreeNormOfRank_baseChange`, so the isomorphism holds with no
hypothesis beyond the square: `Stacks.Divisors.pullbackPicardClass_normInvertible_baseChange`.

This is the statement "norm commutes with base change" used, for instance, in the last paragraph
of the proof of Stacks 0FH9, where `𝒩' = Norm_{id_T × π}(ℒ'₁)` has fibre `Norm_π(ℒ'₁|_{t × Xⁿ})`
over a point `t` of `T`.

## The comparison

Both sides are compared on the cover of `Y'` by the preimages `g⁻¹U` of the norm charts `U` of
`ℒ`, with `Stacks.SheafOfModules.isoOfChartGenerators`. On `g⁻¹U` the left side carries the
pulled-back chart generator of the glued module `Norm_f ℒ`, whose transition units are the
pullbacks of the normed transition units of `ℒ`; the right side carries the norm of the
pulled-back chart generator of `ℒ`, whose transition units are the `N'`-norms of the pullbacks of
the transition units of `ℒ`. The compatibility of the two norms makes these equal.

## Main results

* `Stacks.Divisors.pullbackNormInvertibleIso`: the isomorphism, for norms compatible around a
  cartesian square.
* `Stacks.Divisors.pullbackPicardClass_normInvertible_baseChange`: for the canonical norm of
  constant rank, as an equality of Picard classes.
* `Stacks.Divisors.picardClass_normInvertible_eq_zero`: the norm of a trivial invertible module
  is trivial.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.SheafOfModules
open Stacks.Norm (MorphismNorm MorphismNormMap)

universe u

namespace Stacks.Divisors

variable {X Y X' Y' : Scheme.{u}}

/-- The norm of a local generator, restricted, is the norm of the restricted generator. -/
theorem generatorRestrict_normGenerator' (f : X ⟶ Y) (N : MorphismNormMap f) (L : X.Modules)
    (hL : HasTrivializingTargetCover f L) {W V : Y.Opens} (h : V ≤ W)
    (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)) :
    generatorRestrict (X := Y.toRingedSpace) (normInvertible f N L) h
        (normGenerator f N L hL W s) =
      normGenerator f N L hL V
        (generatorRestrict (X := X.toRingedSpace) L ((Opens.map f.base).map (homOfLE h)).le s) :=
  (Subtype.ext (normGenerator_restrict f N L hL h s)).symm

/-- The preimage under `f'` of the preimage under `g` lies in the preimage under `g'` of the
preimage under `f`, around a commutative square. -/
theorem preimage_le_preimage_of_comp_eq {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (w : g' ≫ f = f' ≫ g) {U : Y.Opens} {A : Y'.Opens} (hA : A ≤ g ⁻¹ᵁ U) :
    f' ⁻¹ᵁ A ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro x hx
  show f (g' x) ∈ U
  rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  exact hA hx

/-- The transition unit of two pulled-back generators over an open inside the preimage is the
`AlgebraicGeometry.Scheme.Hom.appLE` of the transition unit upstairs. -/
theorem generatorRatioUnit_restrict_pullbackGenerator' (f : X ⟶ Y) (L : Y.Modules)
    (hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L)
    {U : Y.Opens} {A : X.Opens} (h : A ≤ f ⁻¹ᵁ U) (s t : GeneratorSections Y.toRingedSpace L U) :
    generatorRatioUnit ((modulePullback f.toLRSHom.toShHom).obj L) A
        (generatorRestrict _ h (pullbackGenerator f L hL U s))
        (generatorRestrict _ h (pullbackGenerator f L hL U t)) =
      Units.map (f.appLE U A h).hom.toMonoidHom (generatorRatioUnit L U s t) :=
  (generatorRatioUnit_restrict _ h (pullbackGenerator f L hL U s)
      (pullbackGenerator f L hL U t)).trans
    ((congrArg (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom)
      (generatorRatioUnit_pullbackGenerator f L hL U s t)).trans rfl)

/-- **The norm of an invertible module commutes with base change**, for norms compatible around a
cartesian square: `g^*(Norm_f ℒ) ≅ Norm_{f'}(g'^*ℒ)`. The compatibility `hN` says that the norm of
a pulled-back function is the pullback of the norm. -/
def pullbackNormInvertibleIso (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y)
    (w : g' ≫ f = f' ≫ g) (N : MorphismNormMap f) (N' : MorphismNormMap f')
    (hN : ∀ (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)),
      N'.app (g ⁻¹ᵁ U) (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U))
        (preimage_le_preimage_of_comp_eq w le_rfl) s) = g.app U (N.app U s))
    (L : X.Modules)
    (hLinv : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L)
    (hL : HasTrivializingTargetCover f L)
    (hL' : HasTrivializingTargetCover f' ((modulePullback g'.toLRSHom.toShHom).obj L)) :
    (modulePullback g.toLRSHom.toShHom).obj (normInvertible f N L) ≅
      normInvertible f' N' ((modulePullback g'.toLRSHom.toShHom).obj L) := by
  classical
  have hNinv : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property
      (normInvertible f N L) :=
    isInvertible_normInvertible f N L hL
  have hcov : (⊤ : Y.Opens) ≤ ⨆ i : NormChart f L, i.val := normChart_cover hL
  have hcov' : (⊤ : Y'.Opens) ≤ ⨆ i : NormChart f L, g ⁻¹ᵁ (i.val : Y.Opens) := by
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov (show g.base x ∈ (⊤ : Y.Opens) from trivial))
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  let L' := (modulePullback g'.toLRSHom.toShHom).obj L
  -- the generator of `g'^*ℒ` over `f'⁻¹(g⁻¹U)` coming from a chart `U` of `ℒ`
  let s' : ∀ i : NormChart f L, GeneratorSections X'.toRingedSpace L'
      (f' ⁻¹ᵁ (g ⁻¹ᵁ (i.val : Y.Opens))) := fun i =>
    generatorRestrict _ (preimage_le_preimage_of_comp_eq w le_rfl)
      (pullbackGenerator g' L hLinv (f ⁻¹ᵁ (i.val : Y.Opens)) (normChartSourceGenerator f L i))
  refine isoOfChartGenerators _ _
    (fun i : NormChart f L => pullbackGenerator g (normInvertible f N L) hNinv
      (i.val : Y.Opens) ((normTransitionCocycle f N L).chartGenerator hcov i))
    (fun i : NormChart f L => normGenerator f' N' L' hL' (g ⁻¹ᵁ (i.val : Y.Opens)) (s' i))
    ?_ hcov'
  intro i j A hi hj
  let W : Y.Opens := i.val ⊓ j.val
  have hiW : W ≤ i.val := inf_le_left
  have hjW : W ≤ j.val := inf_le_right
  have hAB : A ≤ g ⁻¹ᵁ W := by
    change A ≤ g ⁻¹ᵁ (i.val ⊓ j.val)
    rw [Scheme.Hom.preimage_inf]; exact le_inf hi hj
  have hBi : g ⁻¹ᵁ W ≤ g ⁻¹ᵁ (i.val : Y.Opens) := ((Opens.map g.base).map (homOfLE hiW)).le
  have hBj : g ⁻¹ᵁ W ≤ g ⁻¹ᵁ (j.val : Y.Opens) := ((Opens.map g.base).map (homOfLE hjW)).le
  -- the pulled-back side
  have hP : generatorRatioUnit
        ((modulePullback g.toLRSHom.toShHom).obj (normInvertible f N L)) A
        (generatorRestrict _ hj (pullbackGenerator g (normInvertible f N L) hNinv
          (j.val : Y.Opens) ((normTransitionCocycle f N L).chartGenerator hcov j)))
        (generatorRestrict _ hi (pullbackGenerator g (normInvertible f N L) hNinv
          (i.val : Y.Opens) ((normTransitionCocycle f N L).chartGenerator hcov i))) =
      Units.map (g.appLE W A hAB).hom.toMonoidHom
        (normUnitsMap f N W
          (generatorRatioUnit L (f ⁻¹ᵁ W)
            (normChartGeneratorOver f L j W hjW) (normChartGeneratorOver f L i W hiW))) :=
    (congrArg₂ (generatorRatioUnit _ A)
        ((generatorRestrict_trans _ hBj hAB _).symm.trans
          (congrArg (generatorRestrict _ hAB)
            (pullbackGenerator_restrict g (normInvertible f N L) hNinv hjW
              ((normTransitionCocycle f N L).chartGenerator hcov j))))
        ((generatorRestrict_trans _ hBi hAB _).symm.trans
          (congrArg (generatorRestrict _ hAB)
            (pullbackGenerator_restrict g (normInvertible f N L) hNinv hiW
              ((normTransitionCocycle f N L).chartGenerator hcov i))))).trans
      ((generatorRatioUnit_restrict_pullbackGenerator' g (normInvertible f N L) hNinv hAB
          _ _).trans
        (congrArg (Units.map (g.appLE W A hAB).hom.toMonoidHom)
          ((normTransitionCocycle f N L).generatorRatioUnit_chartGenerator hcov i j hiW hjW)))
  -- the normed side: restrict the normed generators to `A`
  have hkA : f' ⁻¹ᵁ A ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ W) := preimage_le_preimage_of_comp_eq w hAB
  have hs'A : ∀ (k : NormChart f L) (hkW : W ≤ k.val) (hk : A ≤ g ⁻¹ᵁ (k.val : Y.Opens)),
      generatorRestrict (X := X'.toRingedSpace) L' ((Opens.map f'.base).map (homOfLE hk)).le
          (s' k) =
        generatorRestrict _ hkA
          (pullbackGenerator g' L hLinv (f ⁻¹ᵁ W) (normChartGeneratorOver f L k W hkW)) := by
    intro k hkW hk
    have hle : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ (k.val : Y.Opens) := ((Opens.map f.base).map (homOfLE hkW)).le
    calc _ = generatorRestrict L' (le_trans ((Opens.map f'.base).map (homOfLE hk)).le
            (preimage_le_preimage_of_comp_eq w le_rfl))
          (pullbackGenerator g' L hLinv (f ⁻¹ᵁ (k.val : Y.Opens))
            (normChartSourceGenerator f L k)) := generatorRestrict_trans _ _ _ _
      _ = generatorRestrict L' hkA (generatorRestrict L'
            ((Opens.map g'.base).map (homOfLE hle)).le
            (pullbackGenerator g' L hLinv (f ⁻¹ᵁ (k.val : Y.Opens))
              (normChartSourceGenerator f L k))) := (generatorRestrict_trans _ _ _ _).symm
      _ = _ := congrArg (generatorRestrict L' hkA)
            (pullbackGenerator_restrict g' L hLinv hle (normChartSourceGenerator f L k))
  have hQ : generatorRatioUnit (normInvertible f' N' L') A
        (generatorRestrict _ hj (normGenerator f' N' L' hL' (g ⁻¹ᵁ (j.val : Y.Opens)) (s' j)))
        (generatorRestrict _ hi (normGenerator f' N' L' hL' (g ⁻¹ᵁ (i.val : Y.Opens)) (s' i))) =
      normUnitsMap f' N' A
        (Units.map (g'.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ A) hkA).hom.toMonoidHom
          (generatorRatioUnit L (f ⁻¹ᵁ W)
            (normChartGeneratorOver f L j W hjW) (normChartGeneratorOver f L i W hiW))) :=
    (congrArg₂ (generatorRatioUnit _ A)
        (generatorRestrict_normGenerator' f' N' L' hL' hj (s' j))
        (generatorRestrict_normGenerator' f' N' L' hL' hi (s' i))).trans
      ((generatorRatioUnit_normGenerator f' N' L' hL' A _ _).trans
        (congrArg (normUnitsMap f' N' A)
          ((congrArg₂ (generatorRatioUnit L' (f' ⁻¹ᵁ A)) (hs'A j hjW hj) (hs'A i hiW hi)).trans
            (generatorRatioUnit_restrict_pullbackGenerator' g' L hLinv hkA _ _))))
  refine hQ.trans (Eq.trans ?_ hP.symm)
  -- the compatibility of the two norms, restricted from `g⁻¹W` to `A`
  refine Units.ext ?_
  change N'.app A ((g'.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ A) hkA).hom _) =
    (g.appLE W A hAB).hom (N.app W _)
  set x := (generatorRatioUnit L (f ⁻¹ᵁ W)
    (normChartGeneratorOver f L j W hjW) (normChartGeneratorOver f L i W hiW)).val
  have h1 : ∀ y : Γ(X, f ⁻¹ᵁ W), (g'.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ A) hkA).hom y =
      (X'.presheaf.map ((Opens.map f'.base).map (homOfLE hAB)).op).hom
        ((g'.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ (g ⁻¹ᵁ W))
          (preimage_le_preimage_of_comp_eq w le_rfl)).hom y) := fun y => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  refine (congrArg (N'.app A) (h1 x)).trans ?_
  rw [N'.naturality]
  refine (congrArg (fun z => (Y'.presheaf.map (homOfLE hAB).op).hom z) (hN W x)).trans ?_
  change (g.app W ≫ Y'.presheaf.map (homOfLE hAB).op).hom (N.app W x) = _
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

/-- **The canonical norm of constant rank commutes with base change**, on Picard classes. Around a
cartesian square with `f` (hence `f'`) finite locally free of rank `d > 0`, and for every
invertible `ℒ` on `X`,

  `[g^*(Norm_f ℒ)] = [Norm_{f'}(g'^*ℒ)]`   in   `Pic(Y')`,

with `Norm` the canonical norm of Tag 0BD2 on both sides. -/
theorem pullbackPicardClass_normInvertible_baseChange (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (g : Y' ⟶ Y) (d : ℕ) [Morphisms.IsFiniteLocallyFreeOfRank f d]
    [Morphisms.IsFiniteLocallyFreeOfRank f' d] (hd : 0 < d) (sq : IsPullback g' f' f g)
    (L : X.Modules) (hL : IsInvertible X.presheaf X.ringCatIsSheaf L) :
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank f d
    haveI := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank f' d
    haveI := hL
    pullbackPicardClass g
        (normInvertible f (finiteLocallyFreeNormOfRank f d hd).1.toMorphismNormMap L)
        (isInvertible_normInvertible f _ L
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible f L hL)) =
      Y'.picardClass
        (normInvertible f' (finiteLocallyFreeNormOfRank f' d hd).1.toMorphismNormMap
          ((modulePullback g'.toLRSHom.toShHom).obj L))
        (isInvertible_normInvertible f' _ _
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible f' _
            (Stacks.RingedSpace.modulePullback_isInvertible _ L))) := by
  have := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank f d
  have := Morphisms.isFinite_of_isFiniteLocallyFreeOfRank f' d
  have := hL
  refine (Y'.picardClass_eq_iff _ _ _ _).mpr ⟨pullbackNormInvertibleIso f f' g' g sq.w _ _
    (fun U s => finiteLocallyFreeNormOfRank_app_baseChange f f' g' g d hd sq U s) L hL
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible f L hL)
    (hasTrivializingTargetCover_of_isFinite_of_isInvertible f' _
      (Stacks.RingedSpace.modulePullback_isInvertible _ L))⟩

/-- **The norm of a trivial invertible module is trivial**, for a finite morphism with a norm of
some degree: the norm is additive on Picard classes (Tag 0BCY). -/
theorem picardClass_normInvertible_eq_zero (f : X ⟶ Y) [IsFinite f] {d : ℕ}
    (N : MorphismNorm f d) (L : X.Modules) (hL : IsInvertible X.presheaf X.ringCatIsSheaf L)
    (h0 : X.picardClass L hL = 0) :
    Y.picardClass (normInvertible f N.toMorphismNormMap L)
        (isInvertible_normInvertible f N.toMorphismNormMap L
          (hasTrivializingTargetCover_of_isFinite_of_isInvertible f L hL)) = 0 := by
  obtain ⟨F, hF⟩ := exists_normPicardAddMonoidHom f N
  exact (hF L hL).symm.trans ((congrArg F h0).trans (map_zero F))

end Stacks.Divisors

end
