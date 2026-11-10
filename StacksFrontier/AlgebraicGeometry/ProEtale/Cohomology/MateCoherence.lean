module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation

/-!
# Coherence of the mates correspondence

The mates correspondence `CategoryTheory.mateEquiv` turns a 2-square of functors whose horizontal
sides are left adjoints into a 2-square whose horizontal sides are the corresponding right
adjoints. This file records three coherence statements about it.

The first is a computation: for a cartesian square, the mate of the square of post-composition
functors on slices (`CategoryTheory.overMapCommSquare`) with respect to the adjunctions
`CategoryTheory.Over.mapPullbackAdj` along the vertical arrows is the inverse of
`CategoryTheory.overPullbackBaseChangeIso`.

The other two say that taking mates commutes with two ways of producing adjunctions:
restriction of an adjunction along fully faithful inclusions
(`CategoryTheory.Adjunction.restrictFullyFaithful`), and the pushforward of an adjunction between
continuous functors of sites to the categories of sheaves
(`CategoryTheory.Adjunction.sheafPushforwardContinuous`).

## Main definitions

* `CategoryTheory.overMapCommSquare`: for a commuting square, the square of post-composition
  functors on slices.

## Main results

* `CategoryTheory.mateEquiv_overMapCommSquare`: for a cartesian square, the mate of
  `CategoryTheory.overMapCommSquare` with respect to the adjunctions
  `CategoryTheory.Over.mapPullbackAdj` along the vertical arrows is the inverse of
  `CategoryTheory.overPullbackBaseChangeIso`.
* `CategoryTheory.mateEquiv_sheafPushforwardContinuousNatTrans`: taking mates commutes with
  `CategoryTheory.Adjunction.sheafPushforwardContinuous`.
* `CategoryTheory.mateEquiv_restrictFullyFaithful_app`: taking mates commutes with
  `CategoryTheory.Adjunction.restrictFullyFaithful`, in the sense that the two mates agree after
  transport along the given commutation isomorphisms.
* `CategoryTheory.Adjunction.map_comm_restrictFullyFaithful_counit`: the transposed form of
  `CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app`.
* `CategoryTheory.isIso_sheafPushforwardContinuousNatTrans`: the pushforward to sheaves of an
  invertible transformation is invertible.
* `CategoryTheory.comp_comp_eq_comp_comp_of_eq_id` and
  `CategoryTheory.isIso_of_comp_comp_eq_comp_comp`: an equation, and an invertibility
  statement, between composites whose outer factors are identities.

## References

* [Stacks Project, Tag 09AA](https://stacks.math.columbia.edu/tag/09AA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An equality of morphisms, composed on each side with two morphisms that are identities: if
`a = b` and `u = 𝟙 X`, `u' = 𝟙 X`, `v = 𝟙 Y`, `v' = 𝟙 Y`, then `u ≫ u' ≫ a = b ≫ v ≫ v'`. -/
theorem comp_comp_eq_comp_comp_of_eq_id {C : Type*} [Category C] {X Y : C}
    {u u' : X ⟶ X} {v v' : Y ⟶ Y} {a b : X ⟶ Y} (hab : a = b)
    (hu : u = 𝟙 X) (hu' : u' = 𝟙 X) (hv : v = 𝟙 Y) (hv' : v' = 𝟙 Y) :
    u ≫ u' ≫ a = b ≫ v ≫ v' := by
  simp [hu, hu', hv, hv', hab]

/-- Invertibility read off from an equation between two composites whose outer factors are
identities: if `u ≫ v ≫ a = b ≫ w ≫ w'` with `u`, `v`, `w`, `w'` identities and `b` invertible,
then `a` is invertible. The four identities are given as hypotheses `u = 𝟙 W`, `v = 𝟙 W`,
`w = 𝟙 Z`, `w' = 𝟙 Z`. -/
theorem isIso_of_comp_comp_eq_comp_comp {C : Type*} [Category C] {W Z : C}
    {u v : W ⟶ W} {w w' : Z ⟶ Z} {b : W ⟶ Z} (a : W ⟶ Z) (hb : IsIso b)
    (hu : u = 𝟙 W) (hv : v = 𝟙 W) (hw : w = 𝟙 Z) (hw' : w' = 𝟙 Z)
    (he : u ≫ v ≫ a = b ≫ w ≫ w') : IsIso a := by
  simp only [hu, hv, hw, hw', Category.id_comp, Category.comp_id] at he
  rwa [he]

section OverBeckChevalley

variable {C : Type*} [Category C] [Limits.HasPullbacks C] {T' T S' S : C}
  (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S) (hw : g' ≫ f = f' ≫ g)

/-- For a commuting square `g' ≫ f = f' ≫ g`, the two composites of post-composition functors
on slices agree: both are post-composition with the diagonal of the square. -/
def overMapCommSquare : Over.map g' ⋙ Over.map f ≅ Over.map f' ⋙ Over.map g :=
  (Over.mapComp g' f).symm ≪≫ eqToIso (congrArg Over.map hw) ≪≫ Over.mapComp f' g

/-- For a cartesian square, the mate of `CategoryTheory.overMapCommSquare` with respect to the
adjunctions `CategoryTheory.Over.mapPullbackAdj` along the two vertical arrows is the inverse of
`CategoryTheory.overPullbackBaseChangeIso`. -/
theorem mateEquiv_overMapCommSquare (h : IsPullback g' f' f g) :
    mateEquiv (Over.mapPullbackAdj f') (Over.mapPullbackAdj f)
        (TwoSquare.mk _ _ _ _ (overMapCommSquare g' f' f g h.w).hom) =
      TwoSquare.mk _ _ _ _ (overPullbackBaseChangeIso g' f' f g h).inv := by
  ext X
  apply pullback.hom_ext
  · simp [overMapCommSquare, overPullbackBaseChangeIso]
  · simp [overMapCommSquare, overPullbackBaseChangeIso]

end OverBeckChevalley

section SheafPushforward

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ t u

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
  {A : Type u} [Category.{t} A]
  {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
  {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  (J₃ : GrothendieckTopology C₃) (J₄ : GrothendieckTopology C₄)
  [L₁.IsContinuous J₁ J₂] [R₁.IsContinuous J₂ J₁]
  [L₂.IsContinuous J₃ J₄] [R₂.IsContinuous J₄ J₃]
  [G.IsContinuous J₁ J₃] [H.IsContinuous J₂ J₄]

/-- Taking mates commutes with pushforward to sheaves. Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be
adjunctions between sites, all four functors being continuous, and let `G`, `H` be continuous
functors forming a 2-square `α` with `L₁` and `L₂`. Pushing forward to sheaves reverses all four
sides of the square, and the mate of the pushed-forward square is the pushforward of the mate
of `α`. -/
theorem mateEquiv_sheafPushforwardContinuousNatTrans (α : TwoSquare G L₁ L₂ H) :
    letI := Functor.isContinuous_comp G L₂ J₁ J₃ J₄
    letI := Functor.isContinuous_comp L₁ H J₁ J₂ J₄
    letI := Functor.isContinuous_comp R₁ G J₂ J₁ J₃
    letI := Functor.isContinuous_comp H R₂ J₂ J₄ J₃
    mateEquiv (adj₂.sheafPushforwardContinuous (E := A) J₃ J₄)
        (adj₁.sheafPushforwardContinuous (E := A) J₁ J₂)
        (TwoSquare.mk (H.sheafPushforwardContinuous A J₂ J₄)
          (L₂.sheafPushforwardContinuous A J₃ J₄)
          (L₁.sheafPushforwardContinuous A J₁ J₂)
          (G.sheafPushforwardContinuous A J₁ J₃)
          (Functor.sheafPushforwardContinuousNatTrans α A J₁ J₄)) =
      TwoSquare.mk (R₂.sheafPushforwardContinuous A J₄ J₃)
        (G.sheafPushforwardContinuous A J₁ J₃)
        (H.sheafPushforwardContinuous A J₂ J₄)
        (R₁.sheafPushforwardContinuous A J₂ J₁)
        (Functor.sheafPushforwardContinuousNatTrans
          (mateEquiv adj₁ adj₂ α) A J₂ J₃) := by
  ext X
  simp
  rfl

/-- The pushforward to sheaves of an invertible natural transformation of continuous functors of
sites is invertible. -/
theorem isIso_sheafPushforwardContinuousNatTrans {F F' : C₁ ⥤ C₂} (τ : F ⟶ F') [IsIso τ]
    [F.IsContinuous J₁ J₂] [F'.IsContinuous J₁ J₂] :
    IsIso (Functor.sheafPushforwardContinuousNatTrans τ A J₁ J₂) :=
  inferInstanceAs (IsIso (Iso.hom
    (Functor.sheafPushforwardContinuousIso (asIso τ) A J₁ J₂).symm))

end SheafPushforward

section Restrict

variable {C C' D D' E E' F F' : Type*}
  [Category C] [Category C'] [Category D] [Category D'] [Category E] [Category E']
  [Category F] [Category F']
  {iC : C ⥤ C'} {iD : D ⥤ D'} {iE : E ⥤ E'} {iF : F ⥤ F'}
  (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
  (hiE : iE.FullyFaithful) (hiF : iF.FullyFaithful)
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₁' : C' ⥤ D'} {R₁' : D' ⥤ C'}
  {L₂ : E ⥤ F} {R₂ : F ⥤ E} {L₂' : E' ⥤ F'} {R₂' : F' ⥤ E'}
  {G : C ⥤ E} {H : D ⥤ F} {G' : C' ⥤ E'} {H' : D' ⥤ F'}
  (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
  (c₁₁ : iC ⋙ L₁' ≅ L₁ ⋙ iD) (c₂₁ : iD ⋙ R₁' ≅ R₁ ⋙ iC)
  (c₁₂ : iE ⋙ L₂' ≅ L₂ ⋙ iF) (c₂₂ : iF ⋙ R₂' ≅ R₂ ⋙ iE)
  (cG : iC ⋙ G' ≅ G ⋙ iE) (cH : iD ⋙ H' ≅ H ⋙ iF)

/-- Transposed form of `CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app`: the
counit of a restricted adjunction, mapped into the ambient category, is obtained from the counit
of the ambient adjunction by transport along the two commutation isomorphisms. -/
theorem Adjunction.map_comm_restrictFullyFaithful_counit (X : D) :
    L₁'.map (c₂₁.inv.app X) ≫ adj₁'.counit.app (iD.obj X) =
      c₁₁.hom.app (R₁.obj X) ≫
        iD.map ((adj₁'.restrictFullyFaithful hiC hiD c₁₁ c₂₁).counit.app X) := by
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  simp

/-- Taking mates commutes with restriction along fully faithful inclusions. Let `adj₁'` and
`adj₂'` be adjunctions, restricted along fully faithful `iC`, `iD` and `iE`, `iF` to adjunctions
`adj₁` and `adj₂` by `CategoryTheory.Adjunction.restrictFullyFaithful`, and let `α`, `α'` be
2-squares for the restricted and the ambient adjunctions which are compatible in the sense of
`hα`. Then the mate of `α` agrees, componentwise and after transport along the commutation
isomorphisms, with the mate of `α'`. -/
theorem mateEquiv_restrictFullyFaithful_app
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁' L₂' H')
    (hα : ∀ c : C, L₂'.map (cG.hom.app c) ≫ c₁₂.hom.app (G.obj c) ≫
        iF.map (α.app c) =
      α'.app (iC.obj c) ≫ H'.map (c₁₁.hom.app c) ≫ cH.hom.app (L₁.obj c))
    (d : D) :
    G'.map (c₂₁.hom.app d) ≫ cG.hom.app (R₁.obj d) ≫
        iE.map ((mateEquiv (adj₁'.restrictFullyFaithful hiC hiD c₁₁ c₂₁)
          (adj₂'.restrictFullyFaithful hiE hiF c₁₂ c₂₂) α).app d) =
      (mateEquiv adj₁' adj₂' α').app (iD.obj d) ≫ R₂'.map (cH.hom.app d) ≫
        c₂₂.hom.app (H.obj d) := by
  have nat12 : ∀ {Y Y' : E} (φ : Y ⟶ Y'),
      L₂'.map (iE.map φ) ≫ c₁₂.hom.app Y' = c₁₂.hom.app Y ≫ iF.map (L₂.map φ) :=
    fun φ => c₁₂.hom.naturality φ
  have natα' : ∀ {X Y : C'} (χ : X ⟶ Y),
      L₂'.map (G'.map χ) ≫ α'.app Y = α'.app X ≫ H'.map (L₁'.map χ) :=
    fun χ => α'.naturality χ
  have natH : ∀ {X Y : D} (ψ : X ⟶ Y),
      cH.hom.app X ≫ iF.map (H.map ψ) = H'.map (iD.map ψ) ≫ cH.hom.app Y :=
    fun ψ => (cH.hom.naturality ψ).symm
  rw [← cancel_mono (c₂₂.inv.app (H.obj d))]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  apply (adj₂'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Functor.map_id, Category.id_comp, Functor.comp_obj]
  rw [Adjunction.map_comm_restrictFullyFaithful_counit hiE hiF adj₂' c₁₂ c₂₂ (H.obj d),
    reassoc_of% nat12, ← Functor.map_comp iF,
    mateEquiv_counit, Functor.map_comp, reassoc_of% hα (R₁.obj d),
    reassoc_of% natα', natH, Adjunction.map_restrictFullyFaithful_counit_app]
  simp

end Restrict

end CategoryTheory

end
