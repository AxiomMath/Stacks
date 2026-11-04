module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNatTransDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapCompatibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.IntegralSquareLimitSetup
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChangeHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSystemCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeOverField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteEtaleCompactification

/-!
# Smooth base change along a limit of smooth schemes, from smooth base change

The source deduces [Stacks, Tag 0F09] (`Stacks.EtaleCohomology.SmoothLimitBaseChange`) from the
smooth base change theorem [Stacks, Tag 0EYU] and the passage to the limit [Stacks, Tag 0EZT].
This file carries out that deduction. Smooth base change itself is not available in this
repository, so its statement enters as an explicit argument, the proposition
`Stacks.EtaleCohomology.SmoothBaseChangeForSheaves`, and **nothing here is registered**: once the
proposition is proved, `Stacks.EtaleCohomology.smoothLimitBaseChange_of_smoothBaseChangeForSheaves`
discharges `Stacks.EtaleCohomology.SmoothLimitBaseChange` in one step.

The argument is the source's.

* For an abelian sheaf `G` on `X` with stalks torsion of orders invertible on `S`, and every `q`,
  `g^{-1}R^q f_*G = R^q f'_*(g')^{-1}G`
  (`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_of_smoothLimit`). This is
  [Stacks, Tag 0EZT] (2) for the inverse system of cartesian squares
  `S_i ← S_i ×_S X` over `S ← X` (constant in the bottom row), whose levels satisfy base change
  by smooth base change, `S_i ⟶ S` being smooth; the system of sheaves is the constant system of
  inverse images of `G`.
* For `E ∈ D⁺(X_étale)` whose cohomology sheaves are such sheaves, the base change map at `E` is an
  isomorphism: it is so at every cohomology sheaf placed in degree zero, by the first step and
  `Stacks.EtaleCohomology.BaseChangeOverField.isIso_smallEtaleDerivedBaseChangeAb_app_single_iff`,
  and a shift-compatible transformation between triangulated functors preserving `D^{≥m}` which
  is invertible on the cohomology objects of a bounded below object is invertible at it
  (`DerivedCategory.Plus.isIso_app_of_isGE_of_isIso_app_single`). This replaces the comparison of
  the spectral sequences of [Stacks, Tag 015J] in the source.

## Main definitions

* `Stacks.EtaleCohomology.SmoothBaseChangeForSheaves` — the assertion of [Stacks, Tag 0EYU].

## Main results

* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_of_smoothLimit` — the sheaf case of
  [Stacks, Tag 0F09], from smooth base change.
* `Stacks.EtaleCohomology.smoothLimitBaseChange_of_smoothBaseChangeForSheaves` —
  [Stacks, Tag 0F09], from smooth base change.

## References

* [Stacks Project, Tag 0F09](https://stacks.math.columbia.edu/tag/0F09)
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- `smallEtaleDerivedBaseChangeAb` (BaseChangeHigher/BaseChangeCondition.lean) is built under the
-- standard model, so its components live in the standard bounded below derived categories.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- **The assertion of the smooth base change theorem, [Stacks, Tag 0EYU].** For a cartesian
square `h ≫ f = e ≫ g` of schemes with `f` smooth and `g` quasi-compact and quasi-separated, the
base change map `f^{-1}R^q g_*ℱ ⟶ R^q h_*e^{-1}ℱ` is an isomorphism for every `q` and every
abelian sheaf `ℱ` on `T_étale` whose stalks are torsion of orders invertible on `S`.

This is a proposition, not a theorem: it is not proved in this repository. -/
def SmoothBaseChangeForSheaves : Prop :=
  ∀ ⦃X S T Y : Scheme.{u}⦄ (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
    (sq : IsPullback h e f g), Smooth f → QuasiCompact g → QuasiSeparated g →
    ∀ (q : ℕ) (ℱ : Sheaf (smallEtaleTopology T) Ab.{u + 1}), HasTorsionOrdersInvertibleOn S ℱ →
      IsIso ((higherBaseChangeMapAb f g h e sq.w q).app ℱ)

/-- Having stalks which are torsion of orders invertible on `S` is invariant under isomorphism. -/
theorem HasTorsionOrdersInvertibleOn.of_iso {S X : Scheme.{u}}
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (e : F ≅ G)
    (hF : HasTorsionOrdersInvertibleOn S F) : HasTorsionOrdersInvertibleOn S G := by
  intro U x
  obtain ⟨R, hR, hRx⟩ := hF U (e.inv.hom.app _ x)
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨n, hn, hnx⟩ := hRx V f hf
  refine ⟨n, hn, ?_⟩
  have hid : e.hom.hom.app _ (e.inv.hom.app _ x) = x := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
    simp
  have hn := congrArg (fun φ => φ (e.inv.hom.app _ x))
    (congrArg ConcreteCategory.hom (e.hom.hom.naturality f.op))
  simp only [ConcreteCategory.comp_apply] at hn
  have h₁ : G.obj.map f.op x = e.hom.hom.app _ (F.obj.map f.op (e.inv.hom.app _ x)) := by
    rw [hn, hid]
  rw [h₁, ← map_nsmul, hnx, map_zero]

/-- The transitions of the base change of an inverse system of schemes over `S` along `X ⟶ S` are
affine if those of the system are: each is a base change of a transition. -/
theorem isAffineHom_baseChangeDiagram_map {I : Type u} [Preorder I] {S X : Scheme.{u}}
    (D : Iᵒᵖ ⥤ Scheme.{u}) (p : D ⟶ (Functor.const Iᵒᵖ).obj S) (f : X ⟶ S) {i j : Iᵒᵖ}
    (a : i ⟶ j) [IsAffineHom (D.map a)] :
    IsAffineHom ((baseChangeDiagram D p f).map a) := by
  have e₁ : (baseChangeDiagram D p f).map a ≫ (baseChangeStructureMap D p f).app j =
      (baseChangeStructureMap D p f).app i :=
    baseChangeDiagram_map_snd D p f a
  have e₂ : D.map a ≫ p.app j = p.app i := map_comp_structureMap D p a
  have s := (isPullback_baseChangeStage D p f i).flip
  rw [← e₁, ← e₂] at s
  have hsq := IsPullback.of_right s (baseChangeDiagram_map_fst D p f a)
    (isPullback_baseChangeStage D p f j).flip
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) hsq.flip inferInstance

open LimitBaseChange LimitHigherDirectImage SmallEtaleLimitCohomology in
/-- **The sheaf case of [Stacks, Tag 0F09], from smooth base change.** Let `S' = lim S_i` be a
directed inverse limit of schemes `S_i` smooth over `S` with affine transition morphisms, let
`f : X ⟶ S` be quasi-compact and quasi-separated and `X' = X ×_S S'`. For every abelian sheaf `G`
on `X_étale` whose stalks are torsion of orders invertible on `S`, and every `q`, the base change
map `g^{-1}R^q f_*G ⟶ R^q f'_*(g')^{-1}G` is an isomorphism, granted smooth base change.

This is [Stacks, Tag 0EZT] (2) for the inverse system of cartesian squares
`S_i ← S_i ×_S X` over `S ← X`, whose limit is the given square by
`Stacks.EtaleCohomology.isLimit_of_isPullback_stages`, with the constant system of inverse images
of `G`; its levels satisfy base change by smooth base change. -/
theorem isIso_higherBaseChangeMapAb_of_smoothLimit (hsbc : SmoothBaseChangeForSheaves.{u})
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {S : Scheme.{u}}
    (D : Iᵒᵖ ⥤ Scheme.{u}) (p : D ⟶ (Functor.const Iᵒᵖ).obj S) (hp : ∀ i, Smooth (p.app i))
    (haff : ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j), IsAffineHom (D.map a)) (c : Cone D) (hc : IsLimit c)
    (g : c.pt ⟶ S) (hg : ∀ i, c.π.app i ≫ p.app i = g) {X X' : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (f' : X' ⟶ c.pt) (g' : X' ⟶ X)
    (sq : IsPullback f' g' g f) (q : ℕ) (G : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (hG : HasTorsionOrdersInvertibleOn S G) :
    IsIso ((higherBaseChangeMapAb g f f' g' sq.w q).app G) := by
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := fun a => haff a
  have : ∀ (Y : Scheme.{u}) {i j : Iᵒᵖ} (a : i ⟶ j),
      IsAffineHom (((Functor.const Iᵒᵖ).obj Y).map a) :=
    fun Y _ _ _ => inferInstanceAs (IsAffineHom (𝟙 Y))
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom ((baseChangeDiagram D p f).map a) :=
    fun a => isAffineHom_baseChangeDiagram_map D p f a
  have : ∀ i : Iᵒᵖ, QuasiCompact (((Functor.const Iᵒᵖ).map f).app i) :=
    fun _ => inferInstanceAs (QuasiCompact f)
  have : ∀ i : Iᵒᵖ, QuasiSeparated (((Functor.const Iᵒᵖ).map f).app i) :=
    fun _ => inferInstanceAs (QuasiSeparated f)
  have hw : ∀ j, (f' ≫ c.π.app j) ≫ p.app j = g' ≫ f := fun j => by
    rw [Category.assoc, hg j, sq.w]
  have hcY : IsLimit (Cone.mk X' (baseChangeProjection D p f c.π f' g' hw)) :=
    isLimit_of_isPullback_stages (isPullback_baseChangeStage D p f) sq hg
      (baseChangeProjection_comp_structureMap D p f c.π f' g' hw)
      (baseChangeProjection_comp_horizontal D p f c.π f' g' hw) hc
  have hs : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (fun _ => 𝟙 X : ∀ i : Iᵒᵖ, ((Functor.const Iᵒᵖ).obj X).obj i ⟶ X) i =
        ((Functor.const Iᵒᵖ).obj X).map a ≫
          (fun _ => 𝟙 X : ∀ i : Iᵒᵖ, ((Functor.const Iᵒᵖ).obj X).obj i ⟶ X) j :=
    fun _ => (Category.id_comp _).symm
  have hsc : ∀ i : Iᵒᵖ, 𝟙 X = conePi (constCone Iᵒᵖ X) i ≫ 𝟙 X := fun _ =>
    (Category.id_comp _).symm
  obtain ⟨hcompat, hpres⟩ := (isColimitPresentation_iff _ _ _).mp
    (isColimitPresentation_pullbackSystem (c := constCone Iᵒᵖ X) G (fun _ => 𝟙 X) hs (𝟙 X) hsc)
  have key := isIso_higherBaseChangeMapAb_of_isLimit p ((Functor.const Iᵒᵖ).map f)
    (baseChangeHorizontal D p f) (baseChangeStructureMap D p f) g f f' g'
    (isPullback_baseChangeStage D p f) hc (isLimitConstCone Iᵒᵖ S) (isLimitConstCone Iᵒᵖ X)
    hcY (fun i => (Category.comp_id _).trans (hg i).symm)
    (fun i => (Category.comp_id _).trans (Category.id_comp _).symm) (fun i =>
      (baseChangeProjection_comp_horizontal D p f c.π f' g' hw i).symm)
    (fun i => (Category.comp_id _).trans
      (baseChangeProjection_comp_structureMap D p f c.π f' g' hw i).symm) q _
    (pullbackSystem G (fun _ => 𝟙 X) hs) _ (fun a => (isCompatibleFamily_iff _ _ _).mp hcompat a)
    hpres
    (fun i => hsbc _ _ _ _ (isPullback_baseChangeStage D p f i) (hp i) inferInstance
      inferInstance q _ (hG.of_iso ((etaleAbelianInverseImageIdIso X).app G).symm))
  exact (NatTrans.isIso_app_iff_of_iso (higherBaseChangeMapAb g f f' g' sq.w q)
    ((etaleAbelianInverseImageIdIso X).app G)).mp key

/-- **[Stacks, Tag 0F09], from smooth base change.** The assertion
`Stacks.EtaleCohomology.SmoothLimitBaseChange` holds as soon as the smooth base change theorem
`Stacks.EtaleCohomology.SmoothBaseChangeForSheaves` does.

For `E ∈ D⁺(X_étale)` whose cohomology sheaves have stalks which are torsion of orders invertible
on `S`, the base change map at each cohomology sheaf placed in degree zero is an isomorphism by
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_of_smoothLimit` in every degree, and the base
change map, a shift-compatible transformation between triangulated functors carrying `D^{≥m}`
into `D^{≥m}`, is then an isomorphism at the bounded below object `E`. -/
theorem smoothLimitBaseChange_of_smoothBaseChangeForSheaves
    (hsbc : SmoothBaseChangeForSheaves.{u}) : SmoothLimitBaseChange.{u} := by
  intro I _ _ _ S D p hp haff c hc g hg X X' f _ _ f' g' sq E hE
  have := commShift_smallEtaleDerivedBaseChangeAb g f f' g' sq.w
  obtain ⟨a, ha⟩ := E.property
  have : E.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff E a).mp ha
  refine DerivedCategory.Plus.isIso_app_of_isGE_of_isIso_app_single
    (smallEtaleDerivedBaseChangeAb g f f' g' sq.w) ?_ ?_ E a inferInstance fun n => ?_
  · intro L m hL
    have := hL
    have := (smallEtalePushforwardAb f).isGE_rightDerivedFunctorPlus_obj L m
    exact (smallEtalePullbackAb g).isGE_rightDerivedFunctorPlus_obj _ m
  · intro L m hL
    have := hL
    have := (smallEtalePullbackAb g').isGE_rightDerivedFunctorPlus_obj L m
    exact (smallEtalePushforwardAb f').isGE_rightDerivedFunctorPlus_obj _ m
  · exact (BaseChangeOverField.isIso_smallEtaleDerivedBaseChangeAb_app_single_iff g f f' g' sq.w
      _).2 fun q => isIso_higherBaseChangeMapAb_of_smoothLimit hsbc D p hp haff c hc g hg f f' g'
        sq q _ (hE n)

end Stacks.EtaleCohomology

end
