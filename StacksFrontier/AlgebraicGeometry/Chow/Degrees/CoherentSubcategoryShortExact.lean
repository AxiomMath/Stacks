module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass

/-!
# Short exact sequences in a full subcategory of coherent modules

`Stacks.Chow.exists_shortExact_of_shortExact_obj`: for an object property `P` of the coherent
`𝒪_X`-modules that is a Serre class, a short exact sequence of `𝒪_X`-modules whose three terms
are objects of `P` is a short exact sequence of the full subcategory `P`: the inclusion of `P`
into all `𝒪_X`-modules is fully faithful, so the two maps lift and the inclusion reflects short
exactness. This is the argument of the private lemma `shortExact_preimage` of
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass`, stated for an
arbitrary such `P` rather than for `Coh_{≤k}(X)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### Short exact sequences in a full subcategory of coherent modules -/

/-- **A short exact sequence of `𝒪_X`-modules between objects of a full subcategory of `Coh(X)`
is one of that subcategory.** For an object property `P` of the coherent `𝒪_X`-modules, the
inclusion of `P` into all `𝒪_X`-modules is fully faithful, so the two maps lift and the inclusion
reflects short exactness. -/
theorem exists_shortExact_of_shortExact_obj
    {P : ObjectProperty (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)}
    [P.IsSerreClass] (A₁ A₂ A₃ : P.FullSubcategory)
    (u : A₁.obj.obj ⟶ A₂.obj.obj) (v : A₂.obj.obj ⟶ A₃.obj.obj) (w : u ≫ v = 0)
    (hS : (ShortComplex.mk u v w).ShortExact) :
    ∃ (u' : A₁ ⟶ A₂) (v' : A₂ ⟶ A₃) (w' : u' ≫ v' = 0),
      (ShortComplex.mk u' v' w').ShortExact := by
  have FF : (P.ι ⋙ (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι).FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)
  have hu := FF.map_preimage u
  have hv := FF.map_preimage v
  have w' : FF.preimage u ≫ FF.preimage v = 0 := by
    refine FF.map_injective ?_
    rw [CategoryTheory.Functor.map_comp, hu, hv, w, CategoryTheory.Functor.map_zero]
  have e : (ShortComplex.mk (FF.preimage u) (FF.preimage v) w').map
      (P.ι ⋙ (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι) ≅
      ShortComplex.mk u v w :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simpa using hu.symm)
      (by simpa using hv.symm)
  exact ⟨FF.preimage u, FF.preimage v, w',
    CategoryTheory.ShortExact.reflects_shortExact_of_faithful _
      (ShortComplex.shortExact_of_iso e.symm hS)⟩

end Stacks.Chow

end
