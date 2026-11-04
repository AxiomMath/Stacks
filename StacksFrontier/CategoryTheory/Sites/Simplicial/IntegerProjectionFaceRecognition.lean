module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerProjectionFaceDerived
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedAdjunctionCounit

/-!
# The face identity of Stacks 0D9K

Let `S` be a simplicial-site situation and `K` an object of the derived category of abelian
sheaves on the total site. For a cartesian `K` and `φ : p ⟶ q`, this file proves the face
identity of the proof of Stacks 0D9K,

  `integerProjection K q ≫ (- ⊗^L integerFace φ) = realizationTermMap φ ≫ integerProjection K p`:

the comparison of Stacks 0D9E (1) in degree `q` followed by the derived tensor product with the
structure map of the integral resolution of Stacks 09WI agrees with the transition of the
realization complex of Stacks 0D9L followed by the comparison in degree `p`.

All names are in the namespace `CategoryTheory.SimplicialSiteSituation`.

## Main results

* `derivedTransition_comp_integerProjection_comp_derivedTensorFace_eq_transpose`: composed with
  `g_{q!}` of the derived transition, the left-hand side of the face identity is the transpose
  along the derived adjunction `g_{q!} ⊣ g_q^{-1}` of the unit followed by the derived
  transition, followed by the comparison in degree `p`.
* `integerProjection_comp_derivedTensorFace_eq_realizationTermMap`: the face identity of
  Stacks 0D9K, for a cartesian `K`.

## Implementation notes

The composites to be compared mix the spellings `(g_p^{-1} ⋙ f_φ^{-1}) ⋙ g_{q!}`,
`(g_p^{-1} ⋙ g_{p!}g_q^{-1}) ⋙ g_{q!}` and `(g_p^{-1}g_{p!}) ⋙ (g_q^{-1}g_{q!})` of one functor,
which agree only at default transparency, so no rewrite reassociates them in place. The
reassociation is therefore stated for abstract morphisms and an abstract functor `Φ` standing
for `g_{q!}`, and its coherence input is `CategoryTheory.derivedCompIso_four`. The factors it
matches are those of the sheaf-level transformation: `g_{q!}` of the leg of the sum formula of
Stacks 09WG, the counit of `g_{q!} ⊣ g_q^{-1}`, a right unitor, and the comparison in degree `p`.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.AbelianSheaves
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- Reassociation of a composite through a functor `Φ : Y ⥤ Z`: given the splittings
`hsplitA`, `hsplitB`, `hmid`, `hg`, `hru`, the inverse pairs `hb`, `hl`, `hah`, `hch`, the
naturality squares `hw`, `hwl`, `hnat` and the coherence `hfour`, the two composites agree. -/
private theorem face_chain {Y Z : Type*} [Category Y] [Category Z] (Φ : Y ⥤ Z)
    {y₀ y₁ y₂ y₃ y₄ y₅ : Y} {z₀ z₁ z₂ z₃ z₄ z₅ z₆ : Z}
    {chi : y₀ ⟶ y₂} {ch : y₂ ⟶ y₀} {v : y₂ ⟶ y₃} {ah : y₃ ⟶ y₁} {ai : y₁ ⟶ y₃}
    {u : y₀ ⟶ y₁} {pr : y₁ ⟶ y₄} {qr : y₄ ⟶ y₅}
    {l : Φ.obj y₂ ⟶ z₀} {l' : z₀ ⟶ Φ.obj y₂}
    {big : z₀ ⟶ z₃} {n₁ : z₀ ⟶ z₁} {n₁₂ : z₁ ⟶ z₃} {n₂ : z₁ ⟶ z₂} {n₃ : z₂ ⟶ z₃}
    {tail : z₃ ⟶ z₄} {b : Φ.obj y₃ ⟶ z₁} {b' : z₁ ⟶ Φ.obj y₃}
    {c : z₁ ⟶ z₅} {g : z₅ ⟶ z₂} {ru : z₂ ⟶ z₂} {d : z₅ ⟶ Φ.obj y₅} {e : Φ.obj y₅ ⟶ z₂}
    {r : Φ.obj y₄ ⟶ z₆} {r' : z₆ ⟶ z₂}
    (hsplitA : big = n₁ ≫ n₁₂) (hsplitB : n₁₂ = n₂ ≫ n₃)
    (hmid : n₂ = c ≫ g ≫ ru) (hg : g = d ≫ e) (hru : ru = 𝟙 z₂)
    (hw : n₁ ≫ b' = l' ≫ Φ.map v) (hb : b' ≫ b = 𝟙 z₁) (hl : l ≫ l' = 𝟙 (Φ.obj y₂))
    (hwl : v ≫ ah = ch ≫ u) (hah : ah ≫ ai = 𝟙 y₃) (hch : chi ≫ ch = 𝟙 y₀)
    (hfour : Φ.map ai ≫ b ≫ c ≫ d = Φ.map pr ≫ Φ.map qr)
    (hnat : Φ.map qr ≫ e = r ≫ r') :
    Φ.map chi ≫ l ≫ big ≫ tail = (Φ.map (u ≫ pr) ≫ r) ≫ r' ≫ n₃ ≫ tail := by
  have hv : chi ≫ v = u ≫ ai := by
    rw [← Category.comp_id (chi ≫ v), ← hah, ← Category.assoc, Category.assoc chi, hwl,
      ← Category.assoc, hch, Category.id_comp]
  have hmapv : Φ.map chi ≫ Φ.map v = Φ.map u ≫ Φ.map ai := by
    rw [← Φ.map_comp, ← Φ.map_comp, hv]
  have hn : n₁ = (l' ≫ Φ.map v) ≫ b := by
    rw [← hw, Category.assoc, hb, Category.comp_id]
  have hfour' : Φ.map ai ≫ b ≫ c ≫ d ≫ e = Φ.map pr ≫ r ≫ r' := by
    rw [← hnat]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ e) hfour
  calc Φ.map chi ≫ l ≫ big ≫ tail
      = Φ.map u ≫ (Φ.map ai ≫ b ≫ c ≫ d ≫ e) ≫ n₃ ≫ tail := by
        rw [hsplitA, hsplitB, hn, hmid, hg, hru, Category.comp_id]
        simp only [Category.assoc]
        rw [← Category.assoc l l', hl, Category.id_comp, ← Category.assoc (Φ.map chi), hmapv,
          Category.assoc]
    _ = Φ.map u ≫ (Φ.map pr ≫ r ≫ r') ≫ n₃ ≫ tail := by rw [hfour']
    _ = (Φ.map (u ≫ pr) ≫ r) ≫ r' ≫ n₃ ≫ tail := by
        rw [Φ.map_comp]
        simp only [Category.assoc]

section Standard

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u})

/-- Composed with `g_{q!}` of the derived transition of Stacks 07TF, the comparison of
Stacks 0D9E in degree `q` followed by the derived tensor product with the structure map of the
integral resolution at `φ : p ⟶ q` is the transpose along the derived adjunction
`g_{q!} ⊣ g_q^{-1}` of the unit of `g_{p!} ⊣ g_p^{-1}` followed by the derived transition,
followed by the comparison in degree `p`. -/
theorem derivedTransition_comp_integerProjection_comp_derivedTensorFace_eq_transpose
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))
    {p q : SimplexCategory} (φ : p ⟶ q) :
    (S.componentLowerShriekDerived q).map ((derivedTransition S φ).app K) ≫
        S.integerProjection K q ≫
          ((derivedTensor S.totalTopology).map
            ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
              (integerFace S φ))).app K =
      ((S.componentLowerShriekDerivedAdjunction q).homEquiv
          ((derivedInverseImage S φ).obj ((derivedComponent S p).obj K))
          ((S.componentLowerShriekDerived p).obj ((derivedComponent S p).obj K))).symm
          ((derivedInverseImage S φ).map
              ((S.componentLowerShriekDerivedAdjunction p).unit.app
                ((derivedComponent S p).obj K)) ≫
            (derivedTransition S φ).app
              ((S.componentLowerShriekDerived p).obj ((derivedComponent S p).obj K))) ≫
        S.integerProjection K p := by
  have hsplitA := congr_app (derivedNatTrans_comp
    ((S.restrictAb p ⋙ abelianTransition S φ) ⋙ componentLowerShriekAb S q)
    ((S.restrictAb p ⋙ componentLowerShriekAb S p ⋙ S.restrictAb q) ⋙
      componentLowerShriekAb S q)
    (integerTensorAb S p)
    (Functor.whiskerRight
      (Functor.whiskerLeft (S.restrictAb p)
        (Functor.whiskerRight (S.componentLowerShriekAbAdjunction' p).unit
            (abelianTransition S φ) ≫
          Functor.whiskerLeft (componentLowerShriekAb S p) (S.abelianTransitionOfFiber' φ)))
      (componentLowerShriekAb S q))
    (Functor.whiskerLeft (S.restrictAb p ⋙ componentLowerShriekAb S p)
        (S.componentLowerShriekAbAdjunction' q).counit ≫
      (Functor.rightUnitor (S.restrictAb p ⋙ componentLowerShriekAb S p)).hom ≫
        integerProjectionSheaf S p)) K
  have hsplitB := congr_app (Eq.trans
    (congrArg (derivedNatTrans
      ((S.restrictAb p ⋙ componentLowerShriekAb S p ⋙ S.restrictAb q) ⋙
        componentLowerShriekAb S q)
      (integerTensorAb S p))
      (Category.assoc
        (Functor.whiskerLeft (S.restrictAb p ⋙ componentLowerShriekAb S p)
          (S.componentLowerShriekAbAdjunction' q).counit)
        (Functor.rightUnitor (S.restrictAb p ⋙ componentLowerShriekAb S p)).hom
        (integerProjectionSheaf S p)).symm)
    (derivedNatTrans_comp
      ((S.restrictAb p ⋙ componentLowerShriekAb S p ⋙ S.restrictAb q) ⋙
        componentLowerShriekAb S q)
      (S.restrictAb p ⋙ componentLowerShriekAb S p)
      (integerTensorAb S p)
      (Functor.whiskerLeft (S.restrictAb p ⋙ componentLowerShriekAb S p)
          (S.componentLowerShriekAbAdjunction' q).counit ≫
        (Functor.rightUnitor (S.restrictAb p ⋙ componentLowerShriekAb S p)).hom)
      (integerProjectionSheaf S p))) K
  have hmid := congr_app (derivedNatTrans_whiskerLeft_comp_rightUnitor
    (S.restrictAb p ⋙ componentLowerShriekAb S p)
    (S.restrictAb q ⋙ componentLowerShriekAb S q)
    (S.componentLowerShriekAbAdjunction' q).counit) K
  have hg := congr_app (derivedNatTrans_counit (S.componentLowerShriekAbAdjunction' q))
    ((S.restrictAb p ⋙ componentLowerShriekAb S p).mapDerivedCategory.obj K)
  have hw := congr_app (derivedCompIso_refl_hom_whiskerRight
    (S.restrictAb p ⋙ abelianTransition S φ)
    (S.restrictAb p ⋙ componentLowerShriekAb S p ⋙ S.restrictAb q)
    (componentLowerShriekAb S q)
    (Functor.whiskerLeft (S.restrictAb p)
      (Functor.whiskerRight (S.componentLowerShriekAbAdjunction' p).unit
          (abelianTransition S φ) ≫
        Functor.whiskerLeft (componentLowerShriekAb S p) (S.abelianTransitionOfFiber' φ)))) K
  have hwl := congr_app (derivedCompIso_refl_hom_whiskerLeft (S.restrictAb p)
    (abelianTransition S φ) (componentLowerShriekAb S p ⋙ S.restrictAb q)
    (Functor.whiskerRight (S.componentLowerShriekAbAdjunction' p).unit
        (abelianTransition S φ) ≫
      Functor.whiskerLeft (componentLowerShriekAb S p) (S.abelianTransitionOfFiber' φ))) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hsplitA hsplitB hmid hg hw hwl
  have hru : (Functor.rightUnitor
      (S.restrictAb p ⋙ componentLowerShriekAb S p).mapDerivedCategory).hom.app K = 𝟙 _ := rfl
  have hnat := (S.componentLowerShriekDerivedAdjunction q).counit.naturality
    ((derivedCompIso (S.restrictAb p) (componentLowerShriekAb S p)
      (S.restrictAb p ⋙ componentLowerShriekAb S p) (Iso.refl _)).inv.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hnat
  simp only [Adjunction.homEquiv_counit]
  rw [derivedTransition_comp_integerProjection_comp_derivedTensorFace_eq_leg,
    derivedInverseImage_map_unit_comp_derivedTransition, integerProjection]
  exact face_chain (componentLowerShriekAb S q).mapDerivedCategory hsplitA hsplitB hmid hg hru
    hw (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _) hwl (Iso.hom_inv_id_app _ _)
    (Iso.inv_hom_id_app _ _)
    (derivedCompIso_four (S.restrictAb p) (componentLowerShriekAb S p) (S.restrictAb q)
      (componentLowerShriekAb S q) K)
    hnat

/-- **The face identity of Stacks 0D9K.** For a cartesian object `K` of the derived category of
abelian sheaves on the total site, the comparison of Stacks 0D9E (1) in degree `q` followed by
the derived tensor product with the structure map of the integral resolution of Stacks 09WI at
`φ : p ⟶ q` is the transition of the realization complex of Stacks 0D9L of the associated
simplicial system of Stacks 0D9H, followed by the comparison in degree `p`. -/
theorem integerProjection_comp_derivedTensorFace_eq_realizationTermMap
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) (hK : S.IsCartesianDerived K)
    {p q : SimplexCategory} (φ : p ⟶ q) :
    S.integerProjection K q ≫
        ((derivedTensor S.totalTopology).map
          ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
            (integerFace S φ))).app K =
      realizationTermMap (S.associatedDerivedSystem K)
          (S.associatedDerivedSystem_cartesian K hK) φ ≫
        S.integerProjection K p :=
  S.integerProjection_comp_derivedTensorFace_eq_realizationTermMap_of_comp K hK φ
    (S.derivedTransition_comp_integerProjection_comp_derivedTensorFace_eq_transpose K φ)

end Standard

end CategoryTheory.SimplicialSiteSituation

end
