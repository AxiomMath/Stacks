module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentability
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOnAChaoticSite

/-!
# Quasi-coherence of the top cohomology module of a derived module on a category

Let `C` be a category viewed as a site with the chaotic topology and let `O` be its sheaf of
rings.  The subcategory `QC(O) ⊆ D(O)` consists of the objects `M` for which every canonical
derived base-change map `RΓ(V, M) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, M)` is an isomorphism.  If `M` lies
in `QC(O)` and has no cohomology above a degree `b`, then the cohomology module `H^b(M)` is
quasi-coherent.

The reason is that between an object of `D(O(U))` in degrees `≤ b` and an object in degrees
`≥ b`, taking cohomology in degree `b` is bijective on morphisms.  Since `M` is in degrees
`≤ b`, so is `RΓ(U, M)` for every `U`, evaluation being exact; hence the universal property of
`RΓ(V, M) ⟶ RΓ(U, M)` for derived restriction of scalars, which is what membership in `QC(O)`
says, descends to the universal property of `H^b(M)(V) ⟶ H^b(M)(U)` for restriction of
scalars.  That condition on a module is quasi-coherence on the chaotic site.

## Main results

* `Stacks.ModulesOnACategory.TopCohomology.isQuasicoherentOnSite_topHomology`: on a site with
  the chaotic topology, the top cohomology module of an object of `QC(O)` is quasi-coherent.

## Implementation notes

The cohomology module of an object of `D(O)` is produced as a presheaf of modules, and the
sheaf condition is carried as an existential in the conclusion.  On the chaotic site it is
automatic, by `CategoryTheory.Presheaf.isSheaf_bot`; keeping the existential rather than
substituting that proof avoids sheafifying, which would tie the universe of the module to the
universe of the ring.

The derived base-change datum of `QuasiCoherentEquivalence.BaseChangeData` is a parameter, as
it is for `QuasiCoherentEquivalence.IsQC`; a left adjoint of derived restriction of scalars is
unique up to unique isomorphism, so the condition does not depend on the choice.

Quasi-coherence is taken from
`Stacks.ModulesOnACategory.isQuasicoherentOnSite_iff_isUniversalArrow`, which states it as the
universal property of the restriction maps, so that no left adjoint of restriction of scalars
has to be named and the section rings need not be commutative; accordingly the result is stated
for an arbitrary sheaf of rings and not for the structure sheaf of a ringed site.  The passage
from the derived universal property to the one on cohomology rests on
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, the comparison of an exact functor with
the cohomology of the derived category, and on its compatibility with the canonical derived
restriction maps, which is checked on complexes.

## References

* [Stacks Project, Tag 0GZQ](https://stacks.math.columbia.edu/tag/0GZQ)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

namespace Stacks.ModulesOnACategory.TopCohomology

universe w u v r

section Bookkeeping

variable {E : Type*} [Category E]

/-- Cancelling a trailing identity.  It is stated in this shape so that it can be applied by
`exact` to a goal in which the identity is indexed by a different, definitionally equal,
spelling of its object. -/
private lemma comp_comp_id {W X Y : E} (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ≫ 𝟙 Y = f ≫ g := by
  rw [Category.comp_id]

end Bookkeeping

section Abstract

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]

/-- The cohomology comparison for a composite of two exact functors is the composite of the two
comparisons: both are the canonical isomorphism attached to the left homology datum of the
short complex, transported first along `F` and then along `G`. -/
private lemma mapHomologyIso_comp (T : ShortComplex A)
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (T.mapHomologyIso (F ⋙ G)).hom =
      ((T.map F).mapHomologyIso G).hom ≫ G.map (T.mapHomologyIso F).hom := by
  have hsplit : ((T.map F).mapHomologyIso G).hom =
      ((T.homologyData.left.map F).map G).homologyIso.hom ≫
        G.map (T.mapHomologyIso F).inv :=
    congrArg Iso.hom ((T.homologyData.left.map F).mapHomologyIso_eq G)
  have hcancel : G.map (T.mapHomologyIso F).inv ≫ G.map (T.mapHomologyIso F).hom =
      𝟙 (G.obj (F.obj T.homology)) := by
    rw [← G.map_comp, Iso.inv_hom_id, G.map_id]
  have hG : ((T.map F).mapHomologyIso G).hom ≫ G.map (T.mapHomologyIso F).hom =
      ((T.homologyData.left.map F).map G).homologyIso.hom :=
    (congrArg (fun k ↦ k ≫ G.map (T.mapHomologyIso F).hom) hsplit).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k ↦ ((T.homologyData.left.map F).map G).homologyIso.hom ≫ k)
          hcancel).trans (Category.comp_id _)))
  rw [hG]
  have hcomm :=
    (({ φK := 𝟙 _
        φH := 𝟙 _
        commi := (Category.id_comp _).trans (Category.comp_id _).symm
        commf' := by
          simp only [ShortComplex.LeftHomologyData.map_f']
          exact (Category.comp_id _).trans (Category.id_comp _).symm
        commπ := (Category.comp_id _).trans (Category.id_comp _).symm } :
      ShortComplex.LeftHomologyMapData (𝟙 (T.map (F ⋙ G)))
        (T.homologyData.left.map (F ⋙ G))
        (show (T.map (F ⋙ G)).LeftHomologyData from
          (T.homologyData.left.map F).map G))).homologyMap_comm
  have h := hcomm.symm
  simp only [ShortComplex.homologyMap_id, Category.id_comp] at h
  exact (Category.comp_id _).symm.trans h

/-- **The compatibility of the cohomology comparisons with a natural transformation.**  Let
`τ : F ⟶ G ⋙ H` be a natural transformation of exact functors.  On the cohomology of a short
complex `T`, the map induced by `τ` is carried to `τ` itself by the cohomology comparisons of
`F`, of `G` and of `H`. -/
private lemma homologyMap_mapNatTrans_comp (T : ShortComplex A)
    (F : A ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : B ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (τ : F ⟶ G ⋙ H) :
    ShortComplex.homologyMap (T.mapNatTrans τ) ≫
        ((T.map G).mapHomologyIso H).hom ≫ H.map (T.mapHomologyIso G).hom =
      (T.mapHomologyIso F).hom ≫ τ.app T.homology := by
  rw [ShortComplex.homologyMap_mapNatTrans, ← mapHomologyIso_comp]
  simp

/-- **The compatibility of the cohomology comparisons on complexes with a natural
transformation.**  For `τ : F ⟶ G ⋙ H` with `F`, `G` and `H` exact, the map induced by `τ` on
the degree-`n` cohomology of a complex is carried to `τ` by the cohomology comparisons. -/
lemma homologyIso_mapNatTrans_compat
    (F : A ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : B ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (τ : F ⟶ G ⋙ H) {ι : Type*} (c : ComplexShape ι) (n : ι) (K : HomologicalComplex A c) :
    (HomologicalComplex.homologyFunctor D c n).map
        ((NatTrans.mapHomologicalComplex τ c).app K) ≫
      (H.mapHomologicalComplexHomologyIso c n).hom.app ((G.mapHomologicalComplex c).obj K) ≫
      H.map ((G.mapHomologicalComplexHomologyIso c n).hom.app K) =
    (F.mapHomologicalComplexHomologyIso c n).hom.app K ≫
      τ.app ((HomologicalComplex.homologyFunctor A c n).obj K) :=
  homologyMap_mapNatTrans_comp
    ((HomologicalComplex.shortComplexFunctor A c n).obj K) F G H τ

section Derived

variable [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]

/-- The cohomology comparison of an exact functor, evaluated on the image of a complex in the
derived category: it is the comparison on complexes, conjugated by the canonical factorizations
of the derived functor and of the cohomology functors. -/
private lemma mapDerivedCategoryHomologyIso_hom_app_Q (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) (K : CochainComplex A ℤ) :
    (F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor B n).map (F.mapDerivedCategoryFactors.hom.app K) ≫
      (DerivedCategory.homologyFunctorFactors B n).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
      F.map ((DerivedCategory.homologyFunctorFactors A n).inv.app K) := by
  simp [Functor.mapDerivedCategoryHomologyIso, Functor.mapDerivedCategoryHomologyIsoAux,
    Localization.Lifting.iso]

/-- The comparison `H^n(F(Q K)) ≅ F(H^n(Q K))` for an exact functor, precomposed with the image
under cohomology of the canonical factorization of the derived functor, is the comparison on
complexes, conjugated by the canonical factorizations of the cohomology functors. -/
private lemma homologyFunctor_map_mapDerivedCategoryFactors_inv (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : CochainComplex A ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor B n).map (F.mapDerivedCategoryFactors.inv.app K) ≫
      (F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K) =
    (DerivedCategory.homologyFunctorFactors B n).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
      F.map ((DerivedCategory.homologyFunctorFactors A n).inv.app K) := by
  rw [mapDerivedCategoryHomologyIso_hom_app_Q, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Between an object of the derived category in degrees `≤ b` and one in degrees `≥ b`, taking
cohomology in degree `b` is bijective on morphisms. -/
private lemma bijective_homologyFunctor_map (P Z : DerivedCategory A) (b : ℤ)
    [P.IsLE b] [Z.IsGE b] :
    Function.Bijective (fun f : P ⟶ Z ↦ (DerivedCategory.homologyFunctor A b).map f) := by
  have h := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    P Z b b 0 b (zero_add b) le_rfl
  have hz : Function.Bijective
      (fun f : P ⟶ Z ↦ f ≫ (shiftFunctorZero (DerivedCategory A) ℤ).inv.app Z) := by
    refine ⟨fun f₁ f₂ hf ↦ ?_, fun f ↦ ⟨f ≫ (shiftFunctorZero (DerivedCategory A) ℤ).hom.app Z,
      by simp⟩⟩
    simpa using congrArg (fun k ↦ k ≫ (shiftFunctorZero (DerivedCategory A) ℤ).hom.app Z) hf
  simpa [Function.comp_def, Functor.shiftMap, ← Functor.map_comp,
    DerivedCategory.shift_homologyFunctor] using h.comp hz

/-- Postcomposing the cohomology in degree `b` with an isomorphism is still bijective on
morphisms from an object in degrees `≤ b` to one in degrees `≥ b`. -/
private lemma bijective_homologyFunctor_map_comp_iso (P Z : DerivedCategory A) (b : ℤ)
    [P.IsLE b] [Z.IsGE b] {W : A} (e : (DerivedCategory.homologyFunctor A b).obj Z ≅ W) :
    Function.Bijective (fun f : P ⟶ Z ↦ (DerivedCategory.homologyFunctor A b).map f ≫ e.hom) :=
  (show Function.Bijective (fun k : (DerivedCategory.homologyFunctor A b).obj P ⟶
      (DerivedCategory.homologyFunctor A b).obj Z ↦ k ≫ e.hom) from
    ⟨fun f g h ↦ by simpa using h, fun g ↦ ⟨g ≫ e.inv, by simp⟩⟩).comp
    (bijective_homologyFunctor_map P Z b)

/-- An exact functor carries an object in degrees `≥ b` to an object in degrees `≥ b`. -/
private lemma isGE_mapDerivedCategory_obj (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : DerivedCategory A) (b : ℤ)
    [P.IsGE b] : (F.mapDerivedCategory.obj P).IsGE b := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (F.map_isZero (P.isZero_of_isGE b i hi)).of_iso
    ((F.mapDerivedCategoryHomologyIso i).app P)

/-- **Descending a derived universal arrow to cohomology.**  Let `F` be exact, let `T` be an
object of `D(A)` in degrees `≤ b` and let `P` be an object of `D(B)` in degrees `≤ b`.  If a
morphism `g : P ⟶ F(T)` is universal for `F.mapDerivedCategory`, then the induced morphism
`H^b(P) ⟶ F(H^b(T))` is universal for `F`.

Indeed a morphism `H^b(T) ⟶ Z` is the same as a morphism `T ⟶ Z[-b]` in `D(A)`, because `T` is
in degrees `≤ b` and `Z[-b]` is in degrees `≥ b`, and likewise on the side of `B`, where
`F(Z[-b])` is still in degrees `≥ b`. -/
private lemma isUniversalArrow_homologyFunctor_map (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : DerivedCategory B) (T : DerivedCategory A) (b : ℤ) [P.IsLE b] [T.IsLE b]
    (g : P ⟶ F.mapDerivedCategory.obj T) (hg : F.mapDerivedCategory.IsUniversalArrow g) :
    F.IsUniversalArrow ((DerivedCategory.homologyFunctor B b).map g ≫
      (F.mapDerivedCategoryHomologyIso b).hom.app T) := by
  intro Z
  have hGE : (F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A b).obj Z)).IsGE b :=
    isGE_mapDerivedCategory_obj F _ b
  have ht : Function.Bijective (fun f : T ⟶ (DerivedCategory.singleFunctor A b).obj Z ↦
      ((DerivedCategory.homologyFunctor A b).map f ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso A b).hom.app Z :
          (DerivedCategory.homologyFunctor A b).obj T ⟶ Z)) :=
    bijective_homologyFunctor_map_comp_iso T _ b
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).app Z)
  refine (Function.Bijective.of_comp_iff _ ht).mp ?_
  have hright : Function.Bijective
      (fun f : P ⟶ F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A b).obj Z) ↦
        ((DerivedCategory.homologyFunctor B b).map f ≫
          (F.mapDerivedCategoryHomologyIso b).hom.app
            ((DerivedCategory.singleFunctor A b).obj Z) ≫
          F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).hom.app Z) :
            (DerivedCategory.homologyFunctor B b).obj P ⟶ F.obj Z)) :=
    bijective_homologyFunctor_map_comp_iso P _ b
      ((F.mapDerivedCategoryHomologyIso b).app ((DerivedCategory.singleFunctor A b).obj Z) ≪≫
        F.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).app Z))
  convert hright.comp (hg ((DerivedCategory.singleFunctor A b).obj Z)) using 1
  funext f
  have hn : (DerivedCategory.homologyFunctor B b).map (F.mapDerivedCategory.map f) ≫
      (F.mapDerivedCategoryHomologyIso b).hom.app
        ((DerivedCategory.singleFunctor A b).obj Z) =
      (F.mapDerivedCategoryHomologyIso b).hom.app T ≫
        F.map ((DerivedCategory.homologyFunctor A b).map f) :=
    (F.mapDerivedCategoryHomologyIso b).hom.naturality f
  dsimp only [Function.comp_def]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

section Comparison

variable [HasDerivedCategory.{w₃} D]

/-- **The compatibility square on the image of a complex.**  Let `τ : F ⟶ G ⋙ H` be a natural
transformation of exact functors.  The derived restriction map built from `τ` by lifting it
through the localization is carried to `τ` itself, on the cohomology of a complex, by the
cohomology comparisons of `F`, of `G` and of `H`. -/
private lemma compat_Q (F : A ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (H : B ⥤ D) [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] (τ : F ⟶ G ⋙ H) (n : ℤ) (K : CochainComplex A ℤ) :
    (DerivedCategory.homologyFunctor D n).map
        (F.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
          H.mapDerivedCategoryFactors.inv.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app K)) ≫
      (H.mapDerivedCategoryHomologyIso n).hom.app
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      H.map ((G.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K)) =
    (F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K) ≫
      τ.app ((DerivedCategory.homologyFunctor A n).obj (DerivedCategory.Q.obj K)) := by
  have h1 : (DerivedCategory.homologyFunctor D n).map
        (H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app K)) ≫
      (H.mapDerivedCategoryHomologyIso n).hom.app
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) =
      (H.mapDerivedCategoryHomologyIso n).hom.app
        (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      H.map ((DerivedCategory.homologyFunctor B n).map
        (G.mapDerivedCategoryFactors.inv.app K)) :=
    (H.mapDerivedCategoryHomologyIso n).hom.naturality _
  have h2 := homologyFunctor_map_mapDerivedCategoryFactors_inv H
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n
  have h3 := homologyFunctor_map_mapDerivedCategoryFactors_inv G K n
  have h4 : H.map ((DerivedCategory.homologyFunctorFactors B n).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      H.map ((DerivedCategory.homologyFunctor B n).map
        (G.mapDerivedCategoryFactors.inv.app K)) ≫
      H.map ((G.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K)) =
      H.map ((G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K) ≫
      H.map (G.map ((DerivedCategory.homologyFunctorFactors A n).inv.app K)) := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc, h3,
      Iso.inv_hom_id_app_assoc, Functor.map_comp]
  have h5 : (DerivedCategory.homologyFunctor D n).map
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K)) ≫
      (DerivedCategory.homologyFunctorFactors D n).hom.app
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      (DerivedCategory.homologyFunctorFactors D n).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) :=
    (DerivedCategory.homologyFunctorFactors D n).hom.naturality _
  have h6 : F.map ((DerivedCategory.homologyFunctorFactors A n).inv.app K) ≫
      τ.app ((DerivedCategory.homologyFunctor A n).obj (DerivedCategory.Q.obj K)) =
      τ.app ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).obj K) ≫
      H.map (G.map ((DerivedCategory.homologyFunctorFactors A n).inv.app K)) :=
    τ.naturality _
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, h4, mapDerivedCategoryHomologyIso_hom_app_Q,
    reassoc_of% h5, reassoc_of% homologyIso_mapNatTrans_compat]
  simp only [Category.assoc]
  rw [h6]

end Comparison

end Derived

end Abstract

section Compatibility

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

attribute [local instance] HasDerivedCategory.standard

/-- The canonical derived restriction map on an object of the form `Q(K)` for a complex `K` of
`O`-modules: it is the image under `Q` of the restriction map of complexes, up to the canonical
factorizations of the derived functors of evaluation and of restriction of scalars. -/
private lemma restrictionD_app_Q {U V : Cᵒᵖ} (a : V ⟶ U)
    (K : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    (restrictionD.{w} O a).app (DerivedCategory.Q.obj K) ≫
        (RGammaRestrictIso.{w} O a).hom.app (DerivedCategory.Q.obj K) =
      (PresheafOfModules.evaluation.{max u v r w} O V).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (PresheafOfModules.restriction O a) (ComplexShape.up ℤ)).app K) ≫
      (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapDerivedCategoryFactors.inv.app
        (((PresheafOfModules.evaluation.{max u v r w} O U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      (DRestrict.{w} O a).map
        ((PresheafOfModules.evaluation.{max u v r w} O U).mapDerivedCategoryFactors.inv.app
          K) := by
  simp only [restrictionD, Localization.liftNatTrans_app, comp_obj,
    Localization.Lifting.iso, whiskerRight_app, RGammaRestrictIso, Localization.liftNatIso,
    liftComp, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Iso.trans_inv, Iso.symm_inv,
    isoWhiskerLeft_inv, Category.assoc, isoWhiskerRight_inv, NatTrans.comp_app,
    associator_hom_app, whiskerLeft_app, associator_inv_app, Category.comp_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, NatIso.cancel_natIso_hom_left]
  exact congrArg (_ ≫ ·) (Category.id_comp _)

/-- **Compatibility of the cohomology comparison with the derived restriction maps.**  The
canonical identification `H^b(RΓ(U, -)) ≅ H^b(-)(U)` carries the canonical derived restriction
map `RΓ(V, M) ⟶ RΓ(U, M)` to the restriction map `H^b(M)(V) ⟶ H^b(M)(U)` of the cohomology
module.  Both sides are natural in `M`, so it suffices to check this on complexes. -/
private lemma compat_natTrans (b : ℤ) {U V : Cᵒᵖ} (a : V ⟶ U) :
    Functor.whiskerRight (restrictionD.{w} O a ≫ (RGammaRestrictIso.{w} O a).hom)
          (DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj V)) b) ≫
        (Functor.associator (RGamma.{w} O U) (DRestrict.{w} O a)
          (DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj V)) b)).hom ≫
        Functor.whiskerLeft (RGamma.{w} O U)
          ((ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapDerivedCategoryHomologyIso
            b).hom ≫
        (Functor.associator (RGamma.{w} O U)
          (DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) b)
          (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom)).inv ≫
        Functor.whiskerRight
          ((PresheafOfModules.evaluation.{max u v r w} O U).mapDerivedCategoryHomologyIso b).hom
          (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom) =
      ((PresheafOfModules.evaluation.{max u v r w} O V).mapDerivedCategoryHomologyIso b).hom ≫
        Functor.whiskerLeft
            (DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} O) b)
            (PresheafOfModules.restriction O a) ≫
          (Functor.associator
            (DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} O) b)
            (PresheafOfModules.evaluation.{max u v r w} O U)
            (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom)).inv := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (PresheafOfModules.{max u v r w} O) (ComplexShape.up ℤ))
    fun K ↦ ?_
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    associator_hom_app, associator_inv_app, Functor.comp_obj, Category.id_comp,
    PresheafOfModules.restriction_app]
  rw [restrictionD_app_Q]
  exact (compat_Q (PresheafOfModules.evaluation.{max u v r w} O V)
    (PresheafOfModules.evaluation.{max u v r w} O U)
    (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom)
    (PresheafOfModules.restriction O a) b K).trans (comp_comp_id _ _).symm

/-- **Compatibility of the cohomology comparison with the derived restriction maps.**  Stated
on a single object of the derived category. -/
private lemma homology_restrictionMap_compat (M : DMod.{w} O) (b : ℤ) {U V : Cᵒᵖ} (a : V ⟶ U) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj V)) b).map
        (restrictionMap.{w} O a M) ≫
      ((ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapDerivedCategoryHomologyIso
          b).hom.app ((RGamma.{w} O U).obj M) ≫
      (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).map
        (((PresheafOfModules.evaluation.{max u v r w} O U).mapDerivedCategoryHomologyIso
          b).hom.app M) =
    ((PresheafOfModules.evaluation.{max u v r w} O V).mapDerivedCategoryHomologyIso
        b).hom.app M ≫
      ((DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} O) b).obj M).map a := by
  have h := congr_app (compat_natTrans.{w} O b a) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    associator_hom_app, associator_inv_app, Functor.comp_obj, Category.id_comp,
    PresheafOfModules.restriction_app] at h
  exact h.trans (comp_comp_id _ _)

end Compatibility

section Main

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}}

attribute [local instance] HasDerivedCategory.standard

/-- **Quasi-coherence of the top cohomology module.**  Let `C` be a category viewed as a site
with the chaotic topology and let `O` be its sheaf of rings.  If `M` is an object of `QC(O)`
and `b` is an integer such that `H^i(M) = 0` for all `i > b`, then `H^b(M)` is a quasi-coherent
module on `(C, O)`. -/
@[stacks 0GZQ]
theorem isQuasicoherentOnSite_topHomology (hJ : J = ⊥) (bc : BaseChangeData.{w} R.obj)
    (M : DMod.{w} R.obj) (hM : IsQC.{w} bc M) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (PresheafOfModules.{max u v r w} R.obj) i).obj M)) :
    ∃ hsh : Presheaf.IsSheaf J ((DerivedCategory.homologyFunctor
        (PresheafOfModules.{max u v r w} R.obj) b).obj M).presheaf,
      (⟨_, hsh⟩ : SheafOfModules.{max u v r w} R).IsQuasicoherentOnSite := by
  -- `J` occurs in the type of `R`, so the sheaf condition is transported along `hJ` with an
  -- explicit motive rather than by rewriting.
  refine ⟨hJ.symm.subst (motive := fun J ↦ Presheaf.IsSheaf J
    ((DerivedCategory.homologyFunctor
      (PresheafOfModules.{max u v r w} R.obj) b).obj M).presheaf)
    (Presheaf.isSheaf_bot _), ?_⟩
  have hMLE : M.IsLE b := by rw [DerivedCategory.isLE_iff]; exact hvan
  rw [Stacks.ModulesOnACategory.isQuasicoherentOnSite_iff_isUniversalArrow.{u, v, r, w} hJ]
  intro U V a
  have hLEV : ((RGamma.{w} R.obj V).obj M).IsLE b :=
    Stacks.Homology.isLE_mapDerivedCategory_obj
      (PresheafOfModules.evaluation.{max u v r w} R.obj V) M b
  have hLEU : ((RGamma.{w} R.obj U).obj M).IsLE b :=
    Stacks.Homology.isLE_mapDerivedCategory_obj
      (PresheafOfModules.evaluation.{max u v r w} R.obj U) M b
  refine Functor.IsUniversalArrow.of_iso
    (((PresheafOfModules.evaluation.{max u v r w} R.obj
      V).mapDerivedCategoryHomologyIso b).app M)
    (((PresheafOfModules.evaluation.{max u v r w} R.obj
      U).mapDerivedCategoryHomologyIso b).app M) ?_
    (isUniversalArrow_homologyFunctor_map
      (ModuleCat.restrictScalars.{max u v r w} (R.obj.map a).hom) _ _ b
      (restrictionMap.{w} R.obj a M)
      ((Functor.isUniversalArrow_iff_isIso (bc.baseChangeAdj a)
        (restrictionMap.{w} R.obj a M)).2 (hM a)))
  exact (Category.assoc _ _ _).trans (homology_restrictionMap_compat.{w} R.obj M b a)

end Main

end Stacks.ModulesOnACategory.TopCohomology

end
