module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerShortComplex
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# Tensoring a dimension layer by a finite locally free module

Let `X` be a scheme and `ℱ` a finite locally free `𝒪_X`-module. Such an `ℱ` is flat, so a short
exact sequence of `𝒪_X`-modules stays short exact after tensoring on the right by `ℱ`. An
invertible `ℒ` is finite locally free of rank one, so the same holds for `ℒ`. For `X` locally of
finite type over the base of a Chow situation and a short exact sequence of coherent modules
whose three terms lie in the layer `Coh_{≤b}(𝒪_X)`, the three twists `Stacks.Chow.layerMkTensor`
again lie in that layer, and their classes in the Grothendieck group of a layer are additive
along the original sequence.

## Main results

* `Stacks.Chow.exists_shortExact_tensorModules_of_isFiniteLocallyFree`: tensoring by a finite
  locally free module carries a short exact sequence of `𝒪_X`-modules to a short exact sequence.
* `Stacks.Chow.exists_shortExact_tensorModules`: the same for an invertible module.
* `Stacks.Chow.coherentDimensionKZeroMk_layerMkTensor_add_of_modules`: additivity of the classes
  of the twists in the Grothendieck group of a layer.

## References

* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU)
* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
* [Stacks Project, Tag 02SX](https://stacks.math.columbia.edu/tag/02SX)
* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### Exactness of tensoring by a finite locally free module -/

/-- A short exact sequence `0 ⟶ A ⟶ B ⟶ D ⟶ 0` of `𝒪_X`-modules stays short exact after
tensoring on the right by a finite locally free `ℱ`. -/
theorem exists_shortExact_tensorModules_of_isFiniteLocallyFree {A B D : X.Modules} (F : X.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (u : A ⟶ B) (v : B ⟶ D) (w : u ≫ v = 0) (h : (ShortComplex.mk u v w).ShortExact) :
    ∃ (u' : tensorModules A F ⟶ tensorModules B F)
      (v' : tensorModules B F ⟶ tensorModules D F) (w' : u' ≫ v' = 0),
      (ShortComplex.mk u' v' w').ShortExact := by
  have := h.mono_f
  have := h.epi_g
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) F :=
    Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree F (hM := hF)
  exact Scheme.Modules.tensorObj_shortExact u v w h.exact F
    (Scheme.Modules.isFlat_of_isFiniteLocallyFree F)

/-- A short exact sequence `0 ⟶ A ⟶ B ⟶ D ⟶ 0` of `𝒪_X`-modules stays short exact after
tensoring on the right by an invertible `ℒ`. -/
theorem exists_shortExact_tensorModules {A B D : X.Modules} (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (u : A ⟶ B) (v : B ⟶ D) (w : u ≫ v = 0) (h : (ShortComplex.mk u v w).ShortExact) :
    ∃ (u' : tensorModules A L ⟶ tensorModules B L)
      (v' : tensorModules B L ⟶ tensorModules D L) (w' : u' ≫ v' = 0),
      (ShortComplex.mk u' v' w').ShortExact :=
  exists_shortExact_tensorModules_of_isFiniteLocallyFree L
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u} L 1
      (hM := Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible X L hL))
    u v w h

/-! ### Additivity of the twisted classes -/

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-- Given a short exact sequence `0 ⟶ A ⟶ B ⟶ D ⟶ 0` of coherent `𝒪_X`-modules whose three
supports have delta-dimension at most `b`, and an invertible `ℒ`, the class of `B ⊗ ℒ` in the
Grothendieck group of the layer `(a, b]` is the sum of the classes of `A ⊗ ℒ` and `D ⊗ ℒ`. -/
theorem coherentDimensionKZeroMk_layerMkTensor_add_of_modules (a b : ℤ) {A B D : X.Modules}
    [A.IsCoherent] [B.IsCoherent] [D.IsCoherent] (u : A ⟶ B) (v : B ⟶ D) (w : u ≫ v = 0)
    (h : (ShortComplex.mk u v w).ShortExact) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hA : schemeDeltaDimension C ((reducedSupport A).subschemeι ≫ f) ≤ (b : EInt))
    (hB : schemeDeltaDimension C ((reducedSupport B).subschemeι ≫ f) ≤ (b : EInt))
    (hD : schemeDeltaDimension C ((reducedSupport D).subschemeι ≫ f) ≤ (b : EInt)) :
    coherentDimensionKZeroMk C f a b (layerMkTensor C f b B L hL hB) =
      coherentDimensionKZeroMk C f a b (layerMkTensor C f b A L hL hA) +
        coherentDimensionKZeroMk C f a b (layerMkTensor C f b D L hL hD) := by
  obtain ⟨u', v', w', h'⟩ := exists_shortExact_tensorModules L hL u v w h
  exact coherentDimensionKZeroMk_add_of_modules C f a b
    (A := layerMkTensor C f b A L hL hA) (B := layerMkTensor C f b B L hL hB)
    (D := layerMkTensor C f b D L hL hD) u' v' w' h'

end Stacks.Chow

end
