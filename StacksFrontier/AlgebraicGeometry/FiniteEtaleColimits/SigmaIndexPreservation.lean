module

public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.BaseChangeCoproducts
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleColimits

/-!
# A coproduct-preserving functor preserves the étale-local coequalizers of Tag 0BN9

Let `A` be an object of a category and let `σ τ : κ → ι` be two maps of index types. The
coequalizer of the two induced morphisms `∐_{j : κ} A ⇉ ∐_{i : ι} A` is the coproduct
`∐_{t : IndexCoeq σ τ} A` indexed by the coequalizer of the index maps
(`Stacks.FundamentalGroup.isColimitSigmaIndexCofork`). That is the diagram the proof of Stacks
Tag 0BN9 reduces to after an étale covering on which both covers split, and it is the diagram
displayed in the proof of Tag 0BNA.

This file proves that a functor preserving the coproducts indexed by `ι` and by `IndexCoeq σ τ`
preserves that coequalizer; preservation of the coproduct indexed by `κ` is not needed. Since they
preserve finite coproducts, the base-change functor `FÉt_Y ⥤ FÉt_X` of a morphism of schemes and
the geometric fibre functor preserve these coequalizers.

## Main definitions

* `Stacks.FundamentalGroup.mapSigmaDesc` — the morphism out of the image of a coproduct of a
  constant family determined by a family of morphisms out of the image of the object.

## Main results

* `Stacks.FundamentalGroup.map_sigma_hom_ext` — the images of the components of a coproduct of a
  constant family are jointly epimorphic, for a functor preserving that coproduct.
* `Stacks.FundamentalGroup.isColimitMapSigmaIndexCofork` — the image under a coproduct-preserving
  functor of the index-coequalizer cofork is a coequalizer.
* `Stacks.FundamentalGroup.preservesColimit_parallelPair_sigmaIndexMap` — the same statement as
  a `PreservesColimit` instance.
* `Stacks.FundamentalGroup.preservesColimit_parallelPair_sigmaIndexMap_finiteEtaleBaseChange`
  and
  `Stacks.FundamentalGroup.preservesColimit_parallelPair_sigmaIndexMap_finiteEtaleFiberFunctor`
  — base change of finite étale covers and the geometric fibre functor preserve the étale-local
  coequalizers of Tag 0BN9.

## References

* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
* [Stacks Project, Tag 0BNA](https://stacks.math.columbia.edu/tag/0BNA)
* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.FundamentalGroup

/-! ### Images of coproducts of a constant family -/

section Const

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (A : C) (β : Type*) (F : C ⥤ D)
  [HasCoproduct fun _ : β ↦ A] [PreservesColimitsOfShape (Discrete β) F]

/-- The image under a functor of the cofan exhibiting `∐_{b : β} A` as a coproduct is again a
colimit, when the functor preserves coproducts indexed by `β`. -/
def isColimitMapCofanConst :
    IsColimit (F.mapCocone (Cofan.mk (∐ fun _ : β ↦ A) (Sigma.ι fun _ : β ↦ A))) :=
  isColimitOfPreserves F (coproductIsCoproduct _)

/-- The images of the components of a coproduct of a constant family are jointly epimorphic, for
a functor preserving that coproduct. -/
theorem map_sigma_hom_ext {W : D} {m m' : F.obj (∐ fun _ : β ↦ A) ⟶ W}
    (h : ∀ b, F.map (Sigma.ι (fun _ : β ↦ A) b) ≫ m =
      F.map (Sigma.ι (fun _ : β ↦ A) b) ≫ m') :
    m = m' :=
  (isColimitMapCofanConst A β F).hom_ext fun b ↦ h b.as

/-- The morphism out of the image of a coproduct of a constant family determined by a family of
morphisms out of the image of the object, for a functor preserving that coproduct. -/
def mapSigmaDesc {W : D} (g : β → (F.obj A ⟶ W)) : F.obj (∐ fun _ : β ↦ A) ⟶ W :=
  (isColimitMapCofanConst A β F).desc { pt := W, ι := Discrete.natTrans fun b ↦ g b.as }

/-- The image of the component of `∐_{b : β} A` at `b`, followed by `mapSigmaDesc A β F g`, is
`g b`. -/
@[simp]
theorem map_ι_comp_mapSigmaDesc {W : D} (g : β → (F.obj A ⟶ W)) (b : β) :
    F.map (Sigma.ι (fun _ : β ↦ A) b) ≫ mapSigmaDesc A β F g = g b :=
  (isColimitMapCofanConst A β F).fac _ ⟨b⟩

end Const

/-! ### Preservation of the index-coequalizer cofork -/

section Preservation

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (A : C) {ι κ : Type*}
  (σ τ : κ → ι) (F : C ⥤ D) [HasCoproduct fun _ : κ ↦ A] [HasCoproduct fun _ : ι ↦ A]

/-- The components of `∐_{i : ι} A` take equal values at `σ j` and `τ j` under the image of a
cofork on the two images of the index-induced morphisms. -/
theorem map_ι_comp_π_eq
    (s : Cofork (F.map (sigmaIndexMap A σ)) (F.map (sigmaIndexMap A τ))) (j : κ) :
    F.map (Sigma.ι (fun _ : ι ↦ A) (σ j)) ≫ Cofork.π s =
      F.map (Sigma.ι (fun _ : ι ↦ A) (τ j)) ≫ Cofork.π s := by
  simpa only [← Category.assoc, ← F.map_comp, ι_sigmaIndexMap] using
    F.map (Sigma.ι (fun _ : κ ↦ A) j) ≫= s.condition

variable [HasCoproduct fun _ : IndexCoeq σ τ ↦ A]

/-- The component of `∐_{i : ι} A` at `i`, followed by the projection onto the coproduct indexed
by the coequalizer of the index maps, is the component at the class of `i`. -/
@[simp]
theorem ι_comp_sigmaIndexCofork_π (i : ι) :
    Sigma.ι (fun _ : ι ↦ A) i ≫ Cofork.π (sigmaIndexCofork A σ τ) =
      Sigma.ι (fun _ : IndexCoeq σ τ ↦ A) (toIndexCoeq σ τ i) :=
  Sigma.ι_desc _ _

/-- The image of the index-coequalizer cofork under a functor is again a cofork. -/
theorem map_sigmaIndexCofork_condition :
    F.map (sigmaIndexMap A σ) ≫ F.map (Cofork.π (sigmaIndexCofork A σ τ)) =
      F.map (sigmaIndexMap A τ) ≫ F.map (Cofork.π (sigmaIndexCofork A σ τ)) := by
  rw [← F.map_comp, ← F.map_comp, (sigmaIndexCofork A σ τ).condition]

/-- The image of the index-coequalizer cofork under a functor, as a cofork on the images of the
two index-induced morphisms. -/
@[reducible] def mapSigmaIndexCofork :
    Cofork (F.map (sigmaIndexMap A σ)) (F.map (sigmaIndexMap A τ)) :=
  Cofork.ofπ (F.map (Cofork.π (sigmaIndexCofork A σ τ)))
    (map_sigmaIndexCofork_condition A σ τ F)

/-- The projection of the image cofork `mapSigmaIndexCofork A σ τ F` is the image under `F` of
the projection of the index-coequalizer cofork. -/
@[simp]
theorem mapSigmaIndexCofork_π :
    Cofork.π (mapSigmaIndexCofork A σ τ F) = F.map (Cofork.π (sigmaIndexCofork A σ τ)) :=
  rfl

/-- The image of the component of `∐_{i : ι} A` at `i`, followed by the projection of the image
cofork, is the image of the component at the class of `i`. -/
@[reassoc]
theorem ι_comp_mapSigmaIndexCofork_π (i : ι) :
    F.map (Sigma.ι (fun _ : ι ↦ A) i) ≫ Cofork.π (mapSigmaIndexCofork A σ τ F) =
      F.map (Sigma.ι (fun _ : IndexCoeq σ τ ↦ A) (toIndexCoeq σ τ i)) := by
  rw [mapSigmaIndexCofork_π, ← F.map_comp, ι_comp_sigmaIndexCofork_π]

variable [PreservesColimitsOfShape (Discrete ι) F]
  [PreservesColimitsOfShape (Discrete (IndexCoeq σ τ)) F]

/-- **A coproduct-preserving functor preserves the étale-local coequalizer of Stacks 0BN9.** The
image under `F` of the cofork `∐_{j : κ} A ⇉ ∐_{i : ι} A ⟶ ∐_{t : IndexCoeq σ τ} A` is a
coequalizer, as soon as `F` preserves the coproducts indexed by `ι` and by `IndexCoeq σ τ`. -/
def isColimitMapSigmaIndexCofork : IsColimit (mapSigmaIndexCofork A σ τ F) := by
  refine Cofork.IsColimit.mk (mapSigmaIndexCofork A σ τ F)
    (fun s ↦ mapSigmaDesc A (IndexCoeq σ τ) F (indexCoeqLift
      (fun i ↦ F.map (Sigma.ι (fun _ : ι ↦ A) i) ≫ Cofork.π s) (map_ι_comp_π_eq A σ τ F s)))
    (fun s ↦ ?_) (fun s m hm ↦ ?_)
  · refine map_sigma_hom_ext A ι F fun i ↦ ?_
    rw [ι_comp_mapSigmaIndexCofork_π_assoc, map_ι_comp_mapSigmaDesc,
      indexCoeqLift_toIndexCoeq]
  · refine map_sigma_hom_ext A (IndexCoeq σ τ) F (indexCoeq_ind fun i ↦ ?_)
    rw [map_ι_comp_mapSigmaDesc, indexCoeqLift_toIndexCoeq,
      ← ι_comp_mapSigmaIndexCofork_π_assoc, hm]

/-- **A coproduct-preserving functor preserves the étale-local coequalizers of Stacks 0BN9**, as
a `PreservesColimit` instance. -/
instance preservesColimit_parallelPair_sigmaIndexMap :
    PreservesColimit (parallelPair (sigmaIndexMap A σ) (sigmaIndexMap A τ)) F :=
  preservesColimit_of_preserves_colimit_cocone (isColimitSigmaIndexCofork A σ τ)
    ((isColimitMapCoconeCoforkEquiv F (sigmaIndexCofork A σ τ).condition).symm
      (isColimitMapSigmaIndexCofork A σ τ F))

end Preservation

/-! ### The two geometric consequences -/

section Geometric

universe u

/-- **Base change preserves the étale-local coequalizers of Stacks 0BN9.** For a morphism
`f : X ⟶ Y` of schemes, a finite étale cover `A` of `Y` and maps `σ τ : κ → ι` of finite index
types, the base-change functor `FÉt_Y ⥤ FÉt_X` preserves the coequalizer of the two
index-induced morphisms `∐_{j : κ} A ⇉ ∐_{i : ι} A`. -/
instance preservesColimit_parallelPair_sigmaIndexMap_finiteEtaleBaseChange
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : FiniteEtaleOver Y) {ι κ : Type*} [Finite ι] [Finite κ]
    (σ τ : κ → ι) :
    PreservesColimit (parallelPair (sigmaIndexMap A σ) (sigmaIndexMap A τ))
      (finiteEtaleBaseChange f) :=
  preservesColimit_parallelPair_sigmaIndexMap A σ τ _

/-- **The geometric fibre functor preserves the étale-local coequalizers of Stacks 0BN9.** For a
geometric point `x` of a scheme `X`, a finite étale cover `A` of `X` and maps `σ τ : κ → ι` of
finite index types, the fibre functor at `x` preserves the coequalizer of the two index-induced
morphisms `∐_{j : κ} A ⇉ ∐_{i : ι} A`. -/
theorem preservesColimit_parallelPair_sigmaIndexMap_finiteEtaleFiberFunctor {X : Scheme.{u}}
    (x : GeometricPoint X) (A : FiniteEtaleOver X) {ι κ : Type*} [Finite ι] [Finite κ]
    (σ τ : κ → ι) :
    PreservesColimit (parallelPair (sigmaIndexMap A σ) (sigmaIndexMap A τ))
      (finiteEtaleFiberFunctor x) :=
  have := preservesFiniteCoproducts_finiteEtaleFiberFunctor x
  preservesColimit_parallelPair_sigmaIndexMap A σ τ _

end Geometric

end Stacks.FundamentalGroup

end
