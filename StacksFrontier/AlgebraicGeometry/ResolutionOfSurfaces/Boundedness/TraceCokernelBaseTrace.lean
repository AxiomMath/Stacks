module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperDualityTransportAffineBase

/-!
# The trace `Γ(X, ω_X^•) ⟶ ω_A^•` over an affine base

Let `A` be a Noetherian ring and `f : X ⟶ Spec A` a proper morphism, and let `ω_A^•` be an object
of `D(A)`. Write `ω_X^• = f^×(ω̃_A^•)` for the relative dualizing complex of [Stacks, Tag 0AWI].
This file constructs the trace

`RΓ(X, ω_X^•) ⟶ ω_A^•`

of [Stacks, Tag 0AWG] over the affine base, and proves that composing with it is the duality
bijection

`Hom_{D_QCoh(𝒪_X)}(L, ω_X^•) ≃ Hom_{D(A)}(RΓ(X, L), ω_A^•)`.

## Main definitions

All in the namespace `Stacks.Duality`.

* `baseTrace` — the trace `RΓ(X, ω_X^•) ⟶ ω_A^•`.

## Main results

* `bijective_derivedGlobalSectionsOver_map_comp_baseTrace` — the displayed bijection.

## The construction

The counit of `Rf_* ⊣ f^×` at `ω̃_A^•` is the sheafy trace
`Rf_* ω_X^• ⟶ ω̃_A^•` (`Stacks.Duality.relativeDualizingComplexTrace`), a morphism of
`D_QCoh(𝒪_{Spec A})`. Pushing it down to `D(A)` costs two of the four spelling reconciliations of
`Duality/ProperDualityTransportAffineBase.lean`: Leray (`standardLerayIso`) identifies
`RΓ(X, ω_X^•)` with `RΓ(Spec A, Rf_* ω_X^•)`, and the unit of the derived Spec–Γ equivalence
(`standardTildeGlobalSectionsUnitIso`) identifies `RΓ(Spec A, ω̃_A^•)` back with `ω_A^•`. Nothing
crosses between models: `Stacks.Duality.relativeDualizingComplexTrace` carries a free
`HasDerivedCategory` binder and `Stacks.Duality.properRightAdjoint` instantiates it at
`CategoryTheory.HasDerivedCategory.standard`, which is the model everything here is read at, and
`Stacks.Duality.properRightAdjoint_obj_eq_relativeDualizingComplex` records that the two spellings
of `ω_X^•` are the same term.

The bijection is then the adjunction `Rf_* ⊣ f^×` read on Hom-sets
(`Stacks.Duality.relativeDualizingComplexHomEquiv`), composed with the full faithfulness of
`D_QCoh(𝒪_{Spec A}) ↪ D(𝒪_{Spec A})`, the full faithfulness of
`AlgebraicGeometry.derivedGlobalSectionsQuasicoherent` — which is an equivalence at the standard
model by `standardTildeEquivalenceInverseIso` — and the two isomorphisms above.

The trace of a proper morphism of schemes of [Stacks, Tag 0AWG] is `Stacks.Duality.qcqsTrace`;
`baseTrace` is its reading over an affine base, the composite of that adjunction with
[Stacks, Tag 06Z0] and [Stacks, Tag 0D5W].

## Implementation notes

The locally small instances of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` arrive
through the imports as *global* instances, so they outrank a file-level local instance; they are
erased here rather than outweighed, exactly as `Duality/ProperDualityTransportAffineBase.lean`
does.

Inside the erasure section two `CategoryTheory.CategoryStruct` paths for
`DerivedCategory (Spec A).Modules` coexist, and goals mentioning `standardLerayIso` are reported
not type-correct under implicit transparency; `simp` and `rw` therefore fail to match even
`CategoryTheory.Category.assoc`. Every rewrite below is consequently supplied as an explicitly
typed `have`, which does fire.

`CategoryTheory.ObjectProperty.fullyFaithfulι` is applied with its object property written out:
left as a placeholder it does not unify here, the two occurrences being at different schemes.

## References

* [Stacks Project, Tag 0AWG](https://stacks.math.columbia.edu/tag/0AWG)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [IsProper f] [CompactSpace X] [QuasiSeparatedSpace X]

/-- **The trace `RΓ(X, ω_X^•) ⟶ ω_A^•` of [Stacks, Tag 0AWG] over an affine base.** For
`f : X ⟶ Spec A` proper and `ω_A^•` an object of `D(A)`, with `ω_X^• = f^×(ω̃_A^•)` the relative
dualizing complex of [Stacks, Tag 0AWI].

This is the counit of `Rf_* ⊣ f^×` at `ω̃_A^•`, read in `D(A)` through Leray
(`standardLerayIso`) on the source and the unit of the derived Spec–Γ equivalence
(`standardTildeGlobalSectionsUnitIso`) on the target. -/
def baseTrace (ωA : DerivedCategory (ModuleCat.{u} A)) :
    (derivedGlobalSectionsOver f).obj
        ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj ⟶ ωA :=
  (standardLerayIso f (StandardModel.isQuasicoherent_homology_derivedPushforward f) _).hom ≫
    (derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).map
      (relativeDualizingComplexTrace f _ ((derivedTilde (CommRingCat.of A)).obj ωA)).hom ≫
    (standardTildeGlobalSectionsUnitIso A ωA).inv

omit [IsProper f] in
/-- **The duality bijection `Hom_X(L, ω_X^•) ≃ Hom_{D(A)}(RΓ(X, L), ω_A^•)`.** For `L` in
`D_QCoh(𝒪_X)` a morphism `L ⟶ ω_X^•` is determined by the morphism
`RΓ(X, L) ⟶ RΓ(X, ω_X^•) ⟶ ω_A^•` of `D(A)` it induces, and every such morphism arises.

This is the adjunction `Rf_* ⊣ f^×` on Hom-sets
(`Stacks.Duality.relativeDualizingComplexHomEquiv`) read in `D(A)`: the inclusion of
`D_QCoh(𝒪_X)` and the equivalence `AlgebraicGeometry.derivedGlobalSectionsQuasicoherent` of
[Stacks, Tag 06Z0] are fully faithful, and Leray and the unit of that equivalence identify the
two ends with `RΓ(X, L)` and `ω_A^•`. -/
theorem bijective_derivedGlobalSectionsOver_map_comp_baseTrace
    (ωA : DerivedCategory (ModuleCat.{u} A)) (L : quasiCoherentDerivedCategory X) :
    Function.Bijective (fun g : L.obj ⟶
        ((properRightAdjoint f).obj ((derivedTilde (CommRingCat.of A)).obj ωA)).obj ↦
      (derivedGlobalSectionsOver f).map g ≫ baseTrace f ωA) := by
  have := StandardModel.derivedGlobalSectionsQuasicoherent_isEquivalence (CommRingCat.of A)
  set hpush := StandardModel.isQuasicoherent_homology_derivedPushforward f with hhp
  set ωt := (derivedTilde (CommRingCat.of A)).obj ωA with hωt
  set G := derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A))) with hG
  let e₁ := (ObjectProperty.fullyFaithfulι (DerivedCategoryB.derivedCategoryB
    (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf))).homEquiv
      (X := L) (Y := (properRightAdjoint f).obj ωt)
  let e₂ := relativeDualizingComplexHomEquiv f hpush ωt L
  let e₃ := (Functor.FullyFaithful.ofFullyFaithful
    (derivedGlobalSectionsQuasicoherent (CommRingCat.of A))).homEquiv
      (X := (quasiCoherentDerivedPushforward f hpush).obj L) (Y := ωt)
  let e₄ := Iso.homCongr (standardLerayIso f hpush L).symm
    (standardTildeGlobalSectionsUnitIso A ωA).symm
  have hbij := (e₁.symm.trans (e₂.trans (e₃.trans e₄))).bijective
  convert hbij using 1
  funext g
  have hnat : (derivedGlobalSectionsOver f).map g ≫
        (standardLerayIso f hpush ((properRightAdjoint f).obj ωt)).hom =
      (standardLerayIso f hpush L).hom ≫ G.map ((derivedPushforward f).map g) :=
    (derivedGlobalSectionsOverPushforwardIso f).hom.naturality g
  have hmc : G.map ((derivedPushforward f).map g ≫
        (relativeDualizingComplexTrace f hpush ωt).hom) =
      G.map ((derivedPushforward f).map g) ≫
        G.map ((relativeDualizingComplexTrace f hpush ωt).hom) :=
    G.map_comp _ _
  have ha₁ : ((standardLerayIso f hpush L).hom ≫ G.map ((derivedPushforward f).map g)) ≫
        (G.map ((relativeDualizingComplexTrace f hpush ωt).hom) ≫
          (standardTildeGlobalSectionsUnitIso A ωA).inv) =
      (standardLerayIso f hpush L).hom ≫ (G.map ((derivedPushforward f).map g) ≫
        (G.map ((relativeDualizingComplexTrace f hpush ωt).hom) ≫
          (standardTildeGlobalSectionsUnitIso A ωA).inv)) :=
    Category.assoc _ _ _
  have ha₂ : G.map ((derivedPushforward f).map g) ≫
        (G.map ((relativeDualizingComplexTrace f hpush ωt).hom) ≫
          (standardTildeGlobalSectionsUnitIso A ωA).inv) =
      (G.map ((derivedPushforward f).map g) ≫
        G.map ((relativeDualizingComplexTrace f hpush ωt).hom)) ≫
          (standardTildeGlobalSectionsUnitIso A ωA).inv :=
    (Category.assoc _ _ _).symm
  calc (derivedGlobalSectionsOver f).map g ≫ baseTrace f ωA
      = ((derivedGlobalSectionsOver f).map g ≫
            (standardLerayIso f hpush ((properRightAdjoint f).obj ωt)).hom) ≫
          (G.map ((relativeDualizingComplexTrace f hpush ωt).hom) ≫
            (standardTildeGlobalSectionsUnitIso A ωA).inv) :=
        (Category.assoc ((derivedGlobalSectionsOver f).map g)
          (standardLerayIso f hpush ((properRightAdjoint f).obj ωt)).hom
          (G.map ((relativeDualizingComplexTrace f hpush ωt).hom) ≫
            (standardTildeGlobalSectionsUnitIso A ωA).inv)).symm
    _ = ((standardLerayIso f hpush L).hom ≫ G.map ((derivedPushforward f).map g)) ≫
          (G.map ((relativeDualizingComplexTrace f hpush ωt).hom) ≫
            (standardTildeGlobalSectionsUnitIso A ωA).inv) :=
        congrArg (· ≫ (G.map ((relativeDualizingComplexTrace f hpush ωt).hom) ≫
          (standardTildeGlobalSectionsUnitIso A ωA).inv)) hnat
    _ = (standardLerayIso f hpush L).hom ≫ (G.map ((derivedPushforward f).map g) ≫
          G.map ((relativeDualizingComplexTrace f hpush ωt).hom)) ≫
          (standardTildeGlobalSectionsUnitIso A ωA).inv :=
        ha₁.trans (congrArg (fun t => (standardLerayIso f hpush L).hom ≫ t) ha₂)
    _ = (standardLerayIso f hpush L).hom ≫ G.map ((derivedPushforward f).map g ≫
          (relativeDualizingComplexTrace f hpush ωt).hom) ≫
          (standardTildeGlobalSectionsUnitIso A ωA).inv :=
        congrArg (fun t => (standardLerayIso f hpush L).hom ≫ t ≫
          (standardTildeGlobalSectionsUnitIso A ωA).inv) hmc.symm

end Stacks.Duality

end
