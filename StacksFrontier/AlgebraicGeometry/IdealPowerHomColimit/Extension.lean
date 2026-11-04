module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.BiproductQuasicoherent
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Restriction
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# Extending a morphism defined over an open to a finite-type model over the whole scheme

Let `X` be a quasi-compact and quasi-separated scheme, `G` and `F` quasi-coherent `𝒪_X`-modules,
`V ⊆ X` a quasi-compact open with `G|_V` of finite type, and `φ : G|_V ⟶ F|_V` an `𝒪_V`-module map.
Then `φ` extends to `X` after replacing `G` by a finite-type quasi-coherent module which agrees
with it over `V`: there are `K`, a map `p : K ⟶ G` which is an isomorphism over `V`, and a map
`q : K ⟶ F` with `p|_V ≫ φ = q|_V`.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictGraph` is the graph of `φ`, a monomorphism
  `G|_V ⟶ (G ⊞ F)|_V`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictGraph_comp_fst` and
  `restrictGraph_comp_snd`: the graph of `φ` projects to the identity and to `φ`.
* `Stacks.AlgebraicGeometry.IdealPowerHomColimit.exists_finiteType_model_of_restrictHom`: the
  extension statement above.
* `Stacks.AlgebraicGeometry.IdealPowerHomColimit.exists_finiteType_model_of_restrictHom'`: the same
  with the finite-type hypothesis placed on `G` rather than on `G|_V`.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerHomColimit

variable {X : Scheme.{u}}

/-- Restriction along an open immersion preserves binary biproducts. -/
public instance preservesBinaryBiproduct_restrictFunctor (V : X.Opens) (G F : X.Modules) :
    PreservesBinaryBiproduct G F (Scheme.Modules.restrictFunctor V.ι) :=
  preservesBinaryBiproduct_of_preservesBinaryCoproduct _

section Graph

variable (V : X.Opens) {G F : X.Modules}

/-- The graph of a morphism `φ : G|_V ⟶ F|_V`, as a morphism `G|_V ⟶ (G ⊞ F)|_V`.

It is `(𝟙, φ)` read through the comparison isomorphism identifying the restriction of the biproduct
with the biproduct of the restrictions. -/
public noncomputable def restrictGraph (φ : G.restrict V.ι ⟶ F.restrict V.ι) :
    G.restrict V.ι ⟶ (G ⊞ F).restrict V.ι :=
  biprod.lift (𝟙 (G.restrict V.ι)) φ ≫
    ((Scheme.Modules.restrictFunctor V.ι).mapBiprod G F).inv

/-- The comparison isomorphism for the restriction of a biproduct is compatible with the first
projection. -/
public lemma mapBiprod_inv_comp_map_fst :
    ((Scheme.Modules.restrictFunctor V.ι).mapBiprod G F).inv ≫
        (Scheme.Modules.restrictFunctor V.ι).map (biprod.fst : G ⊞ F ⟶ G) =
      biprod.fst := by
  rw [show (Scheme.Modules.restrictFunctor V.ι).map (biprod.fst : G ⊞ F ⟶ G) =
      ((Scheme.Modules.restrictFunctor V.ι).mapBiprod G F).hom ≫ biprod.fst from by
    rw [Functor.mapBiprod_hom, biprod.lift_fst], Iso.inv_hom_id_assoc]

/-- The comparison isomorphism for the restriction of a biproduct is compatible with the second
projection. -/
public lemma mapBiprod_inv_comp_map_snd :
    ((Scheme.Modules.restrictFunctor V.ι).mapBiprod G F).inv ≫
        (Scheme.Modules.restrictFunctor V.ι).map (biprod.snd : G ⊞ F ⟶ F) =
      biprod.snd := by
  rw [show (Scheme.Modules.restrictFunctor V.ι).map (biprod.snd : G ⊞ F ⟶ F) =
      ((Scheme.Modules.restrictFunctor V.ι).mapBiprod G F).hom ≫ biprod.snd from by
    rw [Functor.mapBiprod_hom, biprod.lift_snd], Iso.inv_hom_id_assoc]

/-- The graph of `φ` projects to the identity of `G|_V`. -/
public lemma restrictGraph_comp_fst (φ : G.restrict V.ι ⟶ F.restrict V.ι) :
    restrictGraph V φ ≫
        (Scheme.Modules.restrictFunctor V.ι).map (biprod.fst : G ⊞ F ⟶ G) =
      𝟙 (G.restrict V.ι) := by
  rw [restrictGraph, Category.assoc, mapBiprod_inv_comp_map_fst, biprod.lift_fst]

/-- The graph of `φ` projects to `φ`. -/
public lemma restrictGraph_comp_snd (φ : G.restrict V.ι ⟶ F.restrict V.ι) :
    restrictGraph V φ ≫
        (Scheme.Modules.restrictFunctor V.ι).map (biprod.snd : G ⊞ F ⟶ F) = φ := by
  rw [restrictGraph, Category.assoc, mapBiprod_inv_comp_map_snd, biprod.lift_snd]

/-- The graph of `φ` is a monomorphism. -/
public instance mono_restrictGraph (φ : G.restrict V.ι ⟶ F.restrict V.ι) :
    Mono (restrictGraph V φ) :=
  mono_of_mono_fac (restrictGraph_comp_fst V φ)

end Graph

/-- On a quasi-compact, quasi-separated scheme, a morphism `φ : G|_V ⟶ F|_V` defined over a
quasi-compact open `V` on which `G` is of finite type extends to the whole scheme after replacing
`G` by a finite-type quasi-coherent module `K` which agrees with `G` over `V`: there is `p : K ⟶ G`
restricting to an isomorphism over `V`, and `q : K ⟶ F` with `p|_V ≫ φ = q|_V`.
-/
public theorem exists_finiteType_model_of_restrictHom [CompactSpace X] [QuasiSeparatedSpace X]
    (G F : X.Modules) [G.IsQuasicoherent] [F.IsQuasicoherent] (V : X.Opens)
    (hV : IsCompact (V : Set X)) [(G.restrict V.ι).IsFiniteType]
    (φ : G.restrict V.ι ⟶ F.restrict V.ι) :
    ∃ (K : X.Modules) (_ : K.IsQuasicoherent) (_ : K.IsFiniteType) (p : K ⟶ G) (q : K ⟶ F),
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map p) ∧
        (Scheme.Modules.restrictFunctor V.ι).map p ≫ φ =
          (Scheme.Modules.restrictFunctor V.ι).map q := by
  have := AlgebraicGeometry.directSum_isQuasicoherent_scheme G F
  have hQ : (Subobject.mk (restrictGraph V φ) : V.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (restrictGraph V φ)).symm inferInstance
  have hT : (Subobject.mk (restrictGraph V φ) : V.toScheme.Modules).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (Subobject.underlyingIso (restrictGraph V φ)).symm
  obtain ⟨K, hKqc, hKft, e, he⟩ :=
    AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension (G ⊞ F) V hV
      (Subobject.mk (restrictGraph V φ))
  have harrow : (Scheme.Modules.restrictFunctor V.ι).map
      (K.arrow : (K : X.Modules) ⟶ G ⊞ F) =
      (e.hom ≫ (Subobject.underlyingIso (restrictGraph V φ)).hom) ≫ restrictGraph V φ := by
    rw [he, Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
  have hp : (Scheme.Modules.restrictFunctor V.ι).map (K.arrow ≫ biprod.fst) =
      e.hom ≫ (Subobject.underlyingIso (restrictGraph V φ)).hom := by
    rw [Functor.map_comp, harrow, Category.assoc, restrictGraph_comp_fst, Category.comp_id]
  have hq : (Scheme.Modules.restrictFunctor V.ι).map (K.arrow ≫ biprod.snd) =
      (e.hom ≫ (Subobject.underlyingIso (restrictGraph V φ)).hom) ≫ φ := by
    rw [Functor.map_comp, harrow, Category.assoc, restrictGraph_comp_snd]
  exact ⟨K, hKqc, hKft, K.arrow ≫ biprod.fst, K.arrow ≫ biprod.snd, hp ▸ inferInstance,
    by rw [hp, hq]⟩

/-- `exists_finiteType_model_of_restrictHom` with the finite-type hypothesis placed on `G` rather
than on `G|_V`. -/
public theorem exists_finiteType_model_of_restrictHom' [CompactSpace X]
    [QuasiSeparatedSpace X] (G F : X.Modules) [G.IsQuasicoherent] [G.IsFiniteType]
    [F.IsQuasicoherent] (V : X.Opens) (hV : IsCompact (V : Set X))
    (φ : G.restrict V.ι ⟶ F.restrict V.ι) :
    ∃ (K : X.Modules) (_ : K.IsQuasicoherent) (_ : K.IsFiniteType) (p : K ⟶ G) (q : K ⟶ F),
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map p) ∧
        (Scheme.Modules.restrictFunctor V.ι).map p ≫ φ =
          (Scheme.Modules.restrictFunctor V.ι).map q := by
  have : ((Scheme.Modules.pullback V.ι).obj G).IsFiniteType :=
    @SheafOfModules.pullback_isFiniteType _ _ V.ι.toLRSHom.toShHom G ‹_›
  have : (G.restrict V.ι).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app G).symm
  exact exists_finiteType_model_of_restrictHom G F V hV φ

end Stacks.AlgebraicGeometry.IdealPowerHomColimit

end
