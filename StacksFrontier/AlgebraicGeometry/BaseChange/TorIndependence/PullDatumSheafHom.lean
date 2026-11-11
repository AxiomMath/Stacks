module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.CoverRepresentatives
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeComparisonMaps
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackLocality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackStrictlyPerfect

/-!
# Pulling back the base-change comparison for a derived internal hom

Let

```
Z' --j'--> X'
|          |
gZ         g'
v          v
Z  --j---> X
```

be a commutative square of ringed spaces, `E, K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and
`φ : L(g')^*K ⟶ K'`. The comparison of Stacks 0DJA for a derived internal hom,

`c : L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`,

pulled back along the square (`Stacks.Cohomology.BaseChangeCover.pullDatum`), is identified with
the comparison for the restricted datum,

`L(g_Z)^*R𝓗om(Lj^*E, Lj^*K) ⟶ R𝓗om(L(g_Z)^*Lj^*E, L(j')^*K')`,

taken at the pulled-back `φ`, through the canonical maps of Stacks 08I3 along `j` and `j'`. When
`j` and `j'` are open immersions those two maps are invertible, so condition (1) of Stacks 0DJ8 for
the one datum is condition (1) for the other.

## Main definitions

* `Stacks.Cohomology.BaseChangeCover.squareComparison`: the comparison
  `L(g_Z)^*Lj^* ≅ L(j')^*L(g')^*` of the two iterated derived pullbacks around the square.

## Main results

* `Stacks.Cohomology.BaseChangeCover.pullDatum_baseChangeSheafHomComparison`: the
  identification above.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.Cohomology.BaseChangeCover

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange Stacks.Cohomology.DerivedInternalHomPullback
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

/-- The bookkeeping behind `pullDatum_baseChangeSheafHomComparison`, in an arbitrary category
with a bifunctor `H`: two comparison maps written along two factorizations of the same composite,
related by the transport `hC` between the two composites, agree after the identifications. -/
private theorem comparison_square_aux {𝒟 : Type*} [Category 𝒟] (H : 𝒟ᵒᵖ ⥤ 𝒟 ⥤ 𝒟)
    {R₁ R₂ R₃ R₄ E₁ E₂ E₃ E₄ K₁ K₂ K₃ K₄ P₀ W T K'' : 𝒟}
    (γ₁R : R₁ ≅ R₂) (γ₁E : E₁ ≅ E₂) (γ₁K : K₁ ≅ K₂)
    (ηR : R₂ ≅ R₃) (ηE : E₂ ≅ E₃) (ηK : K₂ ≅ K₃)
    (γ₂R : R₄ ≅ R₃) (γ₂E : E₄ ≅ E₃) (γ₂K : K₄ ≅ K₃)
    (m₁ : R₂ ⟶ (H.obj (op E₂)).obj K₂) (m₂ : R₃ ⟶ (H.obj (op E₃)).obj K₃)
    (xa : R₁ ⟶ P₀) (xb : P₀ ⟶ (H.obj (op E₁)).obj K₁)
    (a : R₄ ⟶ W) (mW : W ⟶ (H.obj (op E₄)).obj K₄)
    (hA : m₁ = γ₁R.inv ≫ (xa ≫ xb) ≫ (H.map γ₁E.inv.op).app K₁ ≫
      (H.obj (op E₂)).map γ₁K.hom)
    (hB : m₂ = γ₂R.inv ≫ (a ≫ mW) ≫ (H.map γ₂E.inv.op).app K₄ ≫
      (H.obj (op E₃)).map γ₂K.hom)
    (hC : ηR.hom ≫ m₂ = m₁ ≫ (H.map ηE.inv.op).app K₂ ≫ (H.obj (op E₃)).map ηK.hom)
    (σR : R₁ ⟶ R₄) (hσR : σR = γ₁R.hom ≫ ηR.hom ≫ γ₂R.inv)
    (σE : E₁ ⟶ E₄) (hσE : σE = γ₁E.hom ≫ ηE.hom ≫ γ₂E.inv)
    (σK : K₁ ⟶ K₄) (hσK : σK = γ₁K.hom ≫ ηK.hom ≫ γ₂K.inv)
    (b : W ⟶ T) (mT : T ⟶ (H.obj (op E₄)).obj K'') (φ₁ : K₄ ⟶ K'')
    (hN : b ≫ mT = mW ≫ (H.obj (op E₄)).map φ₁)
    (pE : R₁ ⟶ T) (hpE : pE = σR ≫ a ≫ b) (pK : K₁ ⟶ K'') (hpK : pK = σK ≫ φ₁)
    (cU : P₀ ⟶ (H.obj (op E₁)).obj K'') (hcU : cU = xb ≫ (H.obj (op E₁)).map pK) :
    pE ≫ mT ≫ (H.map σE.op).app K'' = xa ≫ cU := by
  subst hpE hpK hcU hσR hσE hσK
  have aux : (H.map γ₂E.inv.op).app K₄ ≫ (H.map γ₂E.hom.op).app K₄ = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, ← op_comp, Iso.hom_inv_id,
      op_id, CategoryTheory.Functor.map_id, NatTrans.id_app]
  have hB' : γ₂R.inv ≫ a ≫ mW =
      m₂ ≫ (H.obj (op E₃)).map γ₂K.inv ≫ (H.map γ₂E.hom.op).app K₄ := by
    rw [hB]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc (H.obj (op E₃)) γ₂K.hom γ₂K.inv, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, aux, Category.comp_id]
  have hA' : γ₁R.hom ≫ m₁ =
      xa ≫ xb ≫ (H.map γ₁E.inv.op).app K₁ ≫ (H.obj (op E₂)).map γ₁K.hom := by
    rw [hA, Iso.hom_inv_id_assoc, Category.assoc]
  have hnat : (H.obj (op E₄)).map φ₁ ≫
      (H.map (γ₁E.hom ≫ ηE.hom ≫ γ₂E.inv).op).app K'' =
      (H.map (γ₁E.hom ≫ ηE.hom ≫ γ₂E.inv).op).app K₄ ≫ (H.obj (op E₁)).map φ₁ :=
    (H.map (γ₁E.hom ≫ ηE.hom ≫ γ₂E.inv).op).naturality φ₁
  calc ((γ₁R.hom ≫ ηR.hom ≫ γ₂R.inv) ≫ a ≫ b) ≫ mT ≫
        (H.map (γ₁E.hom ≫ ηE.hom ≫ γ₂E.inv).op).app K''
      = γ₁R.hom ≫ ηR.hom ≫ (γ₂R.inv ≫ a ≫ mW) ≫
          (H.map (γ₁E.hom ≫ ηE.hom ≫ γ₂E.inv).op).app K₄ ≫ (H.obj (op E₁)).map φ₁ := by
        simp only [Category.assoc]
        rw [reassoc_of% hN, hnat]
    _ = (γ₁R.hom ≫ m₁) ≫ (H.map ηE.inv.op).app K₂ ≫ (H.obj (op E₃)).map ηK.hom ≫
          (H.obj (op E₃)).map γ₂K.inv ≫ (H.map γ₂E.hom.op).app K₄ ≫
          (H.map (γ₁E.hom ≫ ηE.hom ≫ γ₂E.inv).op).app K₄ ≫ (H.obj (op E₁)).map φ₁ := by
        rw [hB']
        simp only [Category.assoc]
        rw [reassoc_of% hC]
    _ = xa ≫ xb ≫ (H.obj (op E₁)).map ((γ₁K.hom ≫ ηK.hom ≫ γ₂K.inv) ≫ φ₁) := by
        rw [hA']
        simp only [Category.assoc]
        congr 2
        simp only [Category.assoc, ← NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc,
          ← CategoryTheory.Functor.map_comp, ← op_comp, Iso.inv_hom_id, Category.comp_id]
        simp

/-- The composite of two isomorphisms of functors with a transport, at an object. -/
private theorem iso_app_trans_symm_hom {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    {F G G' H₀ : 𝒞 ⥤ 𝒟} (γ₁ : F ≅ G) (γ₂ : H₀ ≅ G') (e : G' = G) (A : 𝒞) :
    (γ₁.app A ≪≫ (γ₂ ≪≫ eqToIso e).symm.app A).hom =
      γ₁.hom.app A ≫ eqToHom (congrArg (fun T : 𝒞 ⥤ 𝒟 => T.obj A) e.symm) ≫ γ₂.inv.app A := by
  subst e
  simp

/-- A map out of the image of an object under a family of functors transports along an equality
of the indices, by the transports of its source and target. -/
private theorem eqToHom_comp_family {α : Sort*} {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (H : 𝒟ᵒᵖ ⥤ 𝒟 ⥤ 𝒟) (L : α → 𝒞 ⥤ 𝒟) (R A M : 𝒞)
    (m : ∀ h, (L h).obj R ⟶ (H.obj (op ((L h).obj A))).obj ((L h).obj M)) {h₁ h₂ : α}
    (e : h₁ = h₂) :
    eqToHom (congrArg (fun q => (L q).obj R) e) ≫ m h₂ =
      m h₁ ≫ (H.map (eqToHom (congrArg (fun q => (L q).obj A) e.symm)).op).app _ ≫
        (H.obj (op ((L h₂).obj A))).map (eqToHom (congrArg (fun q => (L q).obj M) e)) := by
  subst e
  simp

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {Z' Z X' X : RingedSpace.{u, u}} (gZ : Z' ⟶ Z) (j' : Z' ⟶ X') (j : Z ⟶ X)
  (g' : X' ⟶ X) (w : gZ ≫ j = j' ≫ g')

/-- **The comparison of the two iterated derived pullbacks around a commutative square**,
`L(g_Z)^*Lj^* ≅ L(g_Z ≫ j)^* = L(j' ≫ g')^* ≅ L(j')^*L(g')^*`, at an object. It is the part of
`pullDatum` that does not involve the datum. -/
def squareComparison (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullback gZ).obj ((derivedPullback j).obj A) ≅
      (derivedPullback j').obj ((derivedPullback g').obj A) :=
  (derivedPullbackCompIsoCanonical gZ j).app A ≪≫
    (derivedPullbackCompIsoLeft gZ j' j g' w).symm.app A

/-- The comparison of the two iterated derived pullbacks, written with the transport along the
commutativity of the square at the object. -/
theorem squareComparison_hom_eq (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (squareComparison gZ j' j g' w A).hom =
      (derivedPullbackCompIsoCanonical gZ j).hom.app A ≫
        eqToHom (congrArg (fun q : Z' ⟶ X => (derivedPullback q).obj A) w) ≫
        (derivedPullbackCompIsoCanonical j' g').inv.app A :=
  iso_app_trans_symm_hom (derivedPullbackCompIsoCanonical gZ j)
    (derivedPullbackCompIsoCanonical j' g') (congrArg (fun q : Z' ⟶ X => derivedPullback q) w.symm)
    A

/-- The canonical map of Tag 08I3 along a morphism transports along an equality of morphisms. -/
private theorem derivedPullbackSheafHomMap_congr {h₁ h₂ : Z' ⟶ X} (e : h₁ = h₂)
    (A M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) :
    eqToHom (congrArg (fun q : Z' ⟶ X => (derivedPullback q).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op A)).obj M)) e) ≫
      derivedPullbackSheafHomMap h₂ A M =
    derivedPullbackSheafHomMap h₁ A M ≫
      ((Stacks.SheafOfModules.derivedSheafHom Z'.sheaf).map
        (eqToHom (congrArg (fun q : Z' ⟶ X => (derivedPullback q).obj A) e.symm)).op).app _ ≫
      ((Stacks.SheafOfModules.derivedSheafHom Z'.sheaf).obj (op ((derivedPullback h₂).obj A))).map
        (eqToHom (congrArg (fun q : Z' ⟶ X => (derivedPullback q).obj M) e)) := by
  exact eqToHom_comp_family (Stacks.SheafOfModules.derivedSheafHom Z'.sheaf)
    (fun q : Z' ⟶ X => derivedPullback q) _ A M (fun h => derivedPullbackSheafHomMap h A M) e

/-- **The pulled-back comparison for a derived internal hom.** For a commutative square
`g_Z ≫ j = j' ≫ g'` of ringed spaces, the comparison
`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')` at `φ`, pulled back along the square and followed by
the map of Tag 08I3 along `j'` and the comparison of the two iterated pullbacks of `E`, is the
derived pullback along `g_Z` of the map of Tag 08I3 along `j` followed by the comparison for the
restricted datum `(Lj^*E, Lj^*K, L(j')^*K')` at the pulled-back `φ`. -/
theorem pullDatum_baseChangeSheafHomComparison
    (E K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback g').obj K ⟶ K') :
    pullDatum gZ j' j g' w (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K)
        (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
          (op ((derivedPullback g').obj E))).obj K')
        (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison g' E K K' φ) ≫
      derivedPullbackSheafHomMap j' ((derivedPullback g').obj E) K' ≫
      ((Stacks.SheafOfModules.derivedSheafHom Z'.sheaf).map
        (squareComparison gZ j' j g' w E).hom.op).app ((derivedPullback j').obj K') =
    (derivedPullback gZ).map (derivedPullbackSheafHomMap j E K) ≫
      Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison gZ
        ((derivedPullback j).obj E) ((derivedPullback j).obj K) ((derivedPullback j').obj K')
        (pullDatum gZ j' j g' w K K' φ) := by
  let R := ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K
  have hpE : pullDatum gZ j' j g' w R
      (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
        (op ((derivedPullback g').obj E))).obj K')
      (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison g' E K K' φ) =
      (squareComparison gZ j' j g' w R).hom ≫
        (derivedPullback j').map (derivedPullbackSheafHomMap g' E K) ≫
        (derivedPullback j').map (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
          (op ((derivedPullback g').obj E))).map φ) :=
    (congrArg (fun t => (derivedPullbackCompIsoCanonical gZ j).hom.app R ≫
      (derivedPullbackCompIsoLeft gZ j' j g' w).inv.app R ≫ t)
      (CategoryTheory.Functor.map_comp (derivedPullback j') _ _)).trans (Category.assoc _ _ _).symm
  have hpK : pullDatum gZ j' j g' w K K' φ =
      (squareComparison gZ j' j g' w K).hom ≫ (derivedPullback j').map φ :=
    (Category.assoc _ _ _).symm
  have hcU : Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison gZ
        ((derivedPullback j).obj E) ((derivedPullback j).obj K) ((derivedPullback j').obj K')
        (pullDatum gZ j' j g' w K K' φ) =
      derivedPullbackSheafHomMap gZ ((derivedPullback j).obj E) ((derivedPullback j).obj K) ≫
        ((Stacks.SheafOfModules.derivedSheafHom Z'.sheaf).obj
          (op ((derivedPullback gZ).obj ((derivedPullback j).obj E)))).map
          (pullDatum gZ j' j g' w K K' φ) := rfl
  exact comparison_square_aux (Stacks.SheafOfModules.derivedSheafHom Z'.sheaf)
    ((derivedPullbackCompIsoCanonical gZ j).app R)
    ((derivedPullbackCompIsoCanonical gZ j).app E) ((derivedPullbackCompIsoCanonical gZ j).app K)
    (eqToIso (congrArg (fun q : Z' ⟶ X => (derivedPullback q).obj R) w))
    (eqToIso (congrArg (fun q : Z' ⟶ X => (derivedPullback q).obj E) w))
    (eqToIso (congrArg (fun q : Z' ⟶ X => (derivedPullback q).obj K) w))
    ((derivedPullbackCompIsoCanonical j' g').app R)
    ((derivedPullbackCompIsoCanonical j' g').app E) ((derivedPullbackCompIsoCanonical j' g').app K)
    (derivedPullbackSheafHomMap (gZ ≫ j) E K) (derivedPullbackSheafHomMap (j' ≫ g') E K)
    ((derivedPullback gZ).map (derivedPullbackSheafHomMap j E K))
    (derivedPullbackSheafHomMap gZ ((derivedPullback j).obj E) ((derivedPullback j).obj K))
    ((derivedPullback j').map (derivedPullbackSheafHomMap g' E K))
    (derivedPullbackSheafHomMap j' ((derivedPullback g').obj E) ((derivedPullback g').obj K))
    (derivedPullbackSheafHomMap_comp gZ j E K) (derivedPullbackSheafHomMap_comp j' g' E K)
    (derivedPullbackSheafHomMap_congr w E K)
    _ (squareComparison_hom_eq gZ j' j g' w R)
    _ (squareComparison_hom_eq gZ j' j g' w E)
    _ (squareComparison_hom_eq gZ j' j g' w K)
    _ _ _ (derivedPullbackSheafHomMap_naturality_target j' ((derivedPullback g').obj E) φ)
    _ hpE _ hpK _ hcU

end Stacks.Cohomology.BaseChangeCover

end
