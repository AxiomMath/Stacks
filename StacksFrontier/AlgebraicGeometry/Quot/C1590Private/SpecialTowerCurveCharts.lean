module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerDescent
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerSpecTower
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartEtaleCovers
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartTowerEffective
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartDatumThickening
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesFormalEffective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LiftAlongAffineStages

/-!
# Local effectivity data for towers of families of curves

Let `Wₙ ⟶ V` be an étale limit tower (`AlgebraicGeometry.C1590Private.IsEtaleLimitTower`) whose
first level is locally Noetherian and whose levels are square-zero thickenings of the first, and
let `y₀ → y₁ → ⋯` be families of curves over the levels, the transition morphisms lying over those
of the tower. This file produces local effectivity data for the tower
(`AlgebraicGeometry.C1590Private.TowerChartData`): an étale covering of `V` by affines `Qᵢ`,
families of curves `Ŷᵢ` over `Qᵢ`, and compatible morphisms from the restricted levels to the `Ŷᵢ`.
This is the chart step of piece (G) of the special-tower route to Stacks 0D5A; the descent of the
local limit families is `AlgebraicGeometry.C1590Private.TowerChartData.towerIsEffective`.

## The construction, around a point of `W₀`

* Piece (C) (`AlgebraicGeometry.C1590Private.hasTwoChartEtaleCovers`) gives an affine étale chart
  `U ⟶ W₀` through the point, over which `y₀` is a scheme `Z` with a good two-chart datum.
* The chart lifts to an affine `Q` étale over `V` with `U = Q ×_V W₀` (Stacks 039R,
  `AlgebraicGeometry.FormalSpace.exists_isPullback_affine_etale_lift_of_isThickening`).
* The chosen base changes `yₙ|_{Q ×_V Wₙ}` form a tower of families over an étale limit tower over
  `Q`; the first is `Z`, so all of them are schemes (Stacks 05ZR,
  `AlgebraicGeometry.CurveFamily.isRepresentable_total_of_hom`).
* Their rings `R'ₙ = Γ(Q ×_V Wₙ)` form a tower with surjective transition maps, square-zero kernels
  over `R'₀` (by the pushout along the étale `Q ⟶ V`) and Noetherian `R'₀`; the datum moves to the
  first level by (D) along an isomorphism. Piece (E)
  (`AlgebraicGeometry.C1590Private.twoChartTowerEffective`) gives a flat proper
  `Y ⟶ Spec (lim R'ₙ)` restricting to the levels, and `lim R'ₙ = Γ(Q)` because the tower is an
  étale limit tower.
* `Y ⟶ Q` is a family of curves: its fibres are homeomorphic to those of the first level.

## Main results

* `AlgebraicGeometry.C1590Private.nonempty_towerChartData_curves`.
* `AlgebraicGeometry.C1590Private.TowerCharts.exists_limit_chart`: the limit family over one
  chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Functor
open Deformation.Artin.SquareZeroTower

universe u

namespace AlgebraicGeometry.C1590Private

/-! ### The scheme of a family of curves whose total space is a scheme -/

namespace CurveFamilyScheme

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

variable {x : CurveFamily B hZ} (hx : x.total.obj.IsRepresentable)

/-- The identification of the algebraic space of `CurveFamily.totalSite hx` with the total
space. -/
def totalSpaceIso : schemeSpace (CurveFamily.totalSite hx) ≅ x.total :=
  ObjectProperty.isoMk _ (CurveFamily.totalSiteIso hx)

/-- `totalSpaceIso` lies over the projection of the total space to the base. -/
theorem totalSpaceIso_hom_toBase :
    (totalSpaceIso hx).hom ≫ x.toBase = schemeSpaceMap (CurveFamily.totalSiteToBase hx) :=
  ObjectProperty.hom_ext _ (CurveFamily.yoneda_map_totalSiteToBase hx).symm

/-- The total space of `x` is the base change of `CurveFamily.totalSite hx` along the identity
of the base. -/
theorem isPullback_totalSpaceIso :
    IsPullback (totalSpaceIso hx).hom (schemeSpaceMap (CurveFamily.totalSiteToBase hx)) x.toBase
      (schemeSpaceMap (𝟙 x.base)) := by
  have : IsIso (schemeSpaceMap (𝟙 x.base)) :=
    inferInstanceAs (IsIso ((schemeSpaceFunctor B integerBase hZ).map (𝟙 _)))
  refine IsPullback.of_horiz_isIso ⟨ObjectProperty.hom_ext _ ?_⟩
  show (CurveFamily.totalSiteIso hx).hom ≫ x.toBase.hom =
    yoneda.map (CurveFamily.totalSiteToBase hx) ≫ yoneda.map (𝟙 _)
  rw [CategoryTheory.Functor.map_id, CurveFamily.yoneda_map_totalSiteToBase]
  exact (Category.comp_id _).symm

/-- The fibres of the scheme of a family of curves over its base have dimension at most `1`. -/
theorem topologicalKrullDim_fiber_totalSiteToBase_le (s : (𝒯).obj x.base) :
    topologicalKrullDim (((𝒯).map (CurveFamily.totalSiteToBase hx)).fiber s) ≤
      ((1 : ℕ) : WithBot ℕ∞) :=
  x.topologicalKrullDim_fiber_toScheme_map_le_of_isPullback (isPullback_totalSpaceIso hx)
    (by rw [CategoryTheory.Functor.map_id]; infer_instance) s

variable {x' : CurveFamily B hZ} (hx' : x'.total.obj.IsRepresentable) (φ : x ⟶ x')

/-- `totalSpaceIso` is natural in morphisms of families of curves. -/
theorem totalSpaceIso_hom_totalMap :
    (totalSpaceIso hx).hom ≫ φ.totalMap =
      schemeSpaceMap (CurveFamily.totalSiteMap hx' hx φ) ≫ (totalSpaceIso hx').hom :=
  ObjectProperty.hom_ext _ (by
    show (CurveFamily.totalSiteIso hx).hom ≫ φ.totalMap.hom =
      yoneda.map (CurveFamily.totalSiteMap hx' hx φ) ≫ (CurveFamily.totalSiteIso hx').hom
    simp only [CurveFamily.yoneda_map_totalSiteMap, Category.assoc, Iso.inv_hom_id,
      Category.comp_id])

end CurveFamilyScheme

/-- The base ring map of `f ≫ Y.toSpecΓ` is `f` on global sections. -/
theorem baseOfSpec_comp_toSpecΓ {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TwoChartDatum.baseOfSpec (X := X) (R := Γ(Y, ⊤)) (f ≫ Y.toSpecΓ) = f.appTop.hom := by
  ext r
  simp only [TwoChartDatum.baseOfSpec, Scheme.Hom.comp_appTop, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.toSpecΓ_appTop,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]


/-- **Fibre dimensions along a thickening.** In a commutative square `j ≫ g = h₀ ≫ a` with `j` a
surjective embedding and `a` bijective on points (as for the base change of a thickening), the
fibres of `g` are homeomorphic to those of `h₀`, so a bound on the dimension of the fibres of `h₀`
bounds those of `g`. -/
theorem topologicalKrullDim_fiber_le_of_comm {X₀ Y S₀ S : Scheme.{u}} (j : X₀ ⟶ Y) (h₀ : X₀ ⟶ S₀)
    (g : Y ⟶ S) (a : S₀ ⟶ S) (hw : j ≫ g = h₀ ≫ a) (hj : Topology.IsEmbedding j)
    (hjs : Function.Surjective j) (ha : Function.Injective a) (has : Function.Surjective a)
    {d : WithBot ℕ∞} (hfib : ∀ s₀, topologicalKrullDim (h₀.fiber s₀) ≤ d) (s : S) :
    topologicalKrullDim (g.fiber s) ≤ d := by
  obtain ⟨s₀, rfl⟩ := has s
  have hw' : ∀ x, g (j x) = a (h₀ x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
  have himage : j '' (h₀ ⁻¹' {s₀}) = g ⁻¹' {a s₀} := by
    ext z
    obtain ⟨x, rfl⟩ := hjs z
    simp only [hj.injective.mem_set_image, Set.mem_preimage, Set.mem_singleton_iff, hw', ha.eq_iff]
  calc topologicalKrullDim (g.fiber (a s₀))
      = topologicalKrullDim (g ⁻¹' {a s₀}) :=
        IsHomeomorph.topologicalKrullDim_eq _ (g.fiberHomeo _).isHomeomorph
    _ = topologicalKrullDim (j '' (h₀ ⁻¹' {s₀})) := by rw [himage]
    _ = topologicalKrullDim (h₀ ⁻¹' {s₀}) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (hj.homeomorphImage _).isHomeomorph).symm
    _ = topologicalKrullDim (h₀.fiber s₀) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (h₀.fiberHomeo _).isHomeomorph).symm
    _ ≤ d := hfib s₀

/-! ### The base change of a tower of families of curves to an affine étale chart of its top -/

namespace TowerCharts

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- Pullback squares along an equality of corners. -/
theorem isPullback_eqToHom_comp {C : Type*} [Category C] {P P' X Y Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (hP : P' = P) :
    IsPullback (eqToHom hP ≫ fst) (eqToHom hP ≫ snd) f g := by
  subst hP
  simpa using h

/-- A commuting square of composites of a tower's transition maps. -/
theorem towerToLevel_comm {W W' : ℕ → BigFppfOver B integerBase hZ} {ℓ : ∀ n, W n ⟶ W (n + 1)}
    {c : ∀ n, W' n ⟶ W' (n + 1)} (b : ∀ n, W' n ⟶ W n) (h : ∀ n, c n ≫ b (n + 1) = b n ≫ ℓ n)
    (n : ℕ) : towerToLevel c n ≫ b n = b 0 ≫ towerToLevel ℓ n := by
  induction n with
  | zero => simp [towerToLevel]
  | succ n ih => rw [towerToLevel, Category.assoc, h n, ← Category.assoc, ih, Category.assoc]; rfl

variable [(curvesProjectionOver B hZ).IsFibered]
  {V : BigFppfOver B integerBase hZ} {y : ℕ → CurveFamily B hZ}
  {κ : ∀ n, (y n).base ⟶ V} {ℓ : ∀ n, (y n).base ⟶ (y (n + 1)).base}
  (hW : IsEtaleLimitTower (fun n => (y n).base) κ ℓ)
  (t : ∀ n, y n ⟶ y (n + 1)) (ht : ∀ n, (curvesProjectionOver B hZ).IsHomLift (ℓ n) (t n))
  {Q : BigFppfOver B integerBase hZ} (e : Q ⟶ V)

variable (κ) in
/-- The chosen base change of the `n`-th member of the tower to `Q ×_V Wₙ`. -/
abbrev lev (n : ℕ) : CurveFamily B hZ :=
  (pullbackFiber (curvesProjectionOver B hZ) ⟨y n, rfl⟩ (pullback.snd e (κ n))).1

variable (κ) in
/-- The base of the `n`-th level of the base change is `Q ×_V Wₙ`. -/
theorem lev_base (n : ℕ) : (lev κ e n).base = pullback e (κ n) :=
  (pullbackFiber (curvesProjectionOver B hZ) ⟨y n, rfl⟩ (pullback.snd e (κ n))).2

variable (κ) in
/-- The chosen cartesian morphism from the base change to the `n`-th member. -/
abbrev levπ (n : ℕ) : lev κ e n ⟶ y n :=
  IsPreFibered.pullbackMap (p := curvesProjectionOver B hZ)
    (rfl : (curvesProjectionOver B hZ).obj (y n) = (y n).base) (pullback.snd e (κ n))

/-- `levπ` is cartesian. -/
instance levπ_isCartesian (n : ℕ) :
    (curvesProjectionOver B hZ).IsCartesian (pullback.snd e (κ n)) (levπ κ e n) :=
  IsPreFibered.pullbackMap.IsCartesian _ _

/-- `levπ` lies over the second projection of `Q ×_V Wₙ`. -/
instance levπ_isHomLift (n : ℕ) :
    (curvesProjectionOver B hZ).IsHomLift (pullback.snd e (κ n)) (levπ κ e n) :=
  (levπ_isCartesian e n).toIsHomLift

/-- `levπ` is strongly cartesian. -/
instance levπ_isStronglyCartesian (n : ℕ) :
    (curvesProjectionOver B hZ).IsStronglyCartesian (pullback.snd e (κ n)) (levπ κ e n) :=
  IsFibered.isStronglyCartesian_of_isCartesian _ _ _

omit [(curvesProjectionOver B hZ).IsFibered] in
/-- The base map of a morphism of families of curves lying over `g` is `g`, up to the
identifications of the bases. -/
theorem baseMap_of_isHomLift {x x' : CurveFamily B hZ} {T T' : BigFppfOver B integerBase hZ}
    (g : T ⟶ T') (φ : x ⟶ x') [(curvesProjectionOver B hZ).IsHomLift g φ] (hx : x.base = T)
    (hx' : x'.base = T') :
    φ.baseMap = eqToHom hx ≫ g ≫ eqToHom hx'.symm :=
  IsHomLift.fac' (curvesProjectionOver B hZ) g φ

/-- The base map of `levπ` is the second projection of `Q ×_V Wₙ`. -/
theorem levπ_baseMap (n : ℕ) :
    (levπ κ e n).baseMap = eqToHom (lev_base κ e n) ≫ pullback.snd e (κ n) := by
  simpa using baseMap_of_isHomLift (pullback.snd e (κ n)) (levπ κ e n) (lev_base κ e n) rfl

omit [(curvesProjectionOver B hZ).IsFibered] in
include ht in
/-- The base map of a transition morphism of the tower of families is the transition map of the
base tower. -/
theorem t_baseMap (n : ℕ) : (t n).baseMap = ℓ n := by
  have := ht n
  simpa using baseMap_of_isHomLift (ℓ n) (t n) rfl rfl

omit [(curvesProjectionOver B hZ).IsFibered] in
include hW in
/-- The second projections of the base changes commute with the transition maps. -/
theorem snd_comp_ℓ (n : ℕ) :
    pullback.snd e (κ n) ≫ ℓ n = towerPullbackMap hW e n ≫ pullback.snd e (κ (n + 1)) := by
  simp [towerPullbackMap]

/-- The transition maps of the base change of the tower. -/
def levT (n : ℕ) : lev κ e n ⟶ lev κ e (n + 1) :=
  haveI := ht n
  IsStronglyCartesian.map (curvesProjectionOver B hZ) (pullback.snd e (κ (n + 1)))
    (levπ κ e (n + 1)) (snd_comp_ℓ hW e n)
    (levπ κ e n ≫ t n)

/-- `levT` lies over the transition map of the base change of the base tower. -/
instance levT_isHomLift (n : ℕ) :
    (curvesProjectionOver B hZ).IsHomLift (towerPullbackMap hW e n) (levT hW t ht e n) := by
  have := ht n
  unfold levT
  infer_instance

/-- `levT` commutes with the projections `levπ` and the transition morphisms of the tower. -/
theorem levT_fac (n : ℕ) : levT hW t ht e n ≫ levπ κ e (n + 1) = levπ κ e n ≫ t n := by
  have := ht n
  unfold levT
  exact IsStronglyCartesian.fac _ _ _ _ _

/-- `levT` is the unique morphism over the transition map of the base change commuting with the
projections `levπ`. -/
theorem levT_uniq (n : ℕ) (w : lev κ e n ⟶ lev κ e (n + 1))
    [(curvesProjectionOver B hZ).IsHomLift (towerPullbackMap hW e n) w]
    (hw : w ≫ levπ κ e (n + 1) = levπ κ e n ≫ t n) :
    w = levT hW t ht e n := by
  have := ht n
  exact IsStronglyCartesian.map_uniq _ _ _ _ _ w hw

variable (κ) in
/-- The projection of the `n`-th level of the base change to `Q`. -/
def levA (n : ℕ) : (lev κ e n).base ⟶ Q := eqToHom (lev_base κ e n) ≫ pullback.fst e (κ n)

/-- The base map of `levT` is the transition map of the base change of the base tower. -/
theorem levT_baseMap (n : ℕ) : (levT hW t ht e n).baseMap =
    eqToHom (lev_base κ e n) ≫ towerPullbackMap hW e n ≫ eqToHom (lev_base κ e (n + 1)).symm :=
  baseMap_of_isHomLift _ _ (lev_base κ e n) (lev_base κ e (n + 1))

/-- The transition maps of the bases of the levels commute with the projections to `Q`. -/
theorem levT_baseMap_levA (n : ℕ) :
    (levT hW t ht e n).baseMap ≫ levA κ e (n + 1) = levA κ e n := by
  simp [levT_baseMap, levA, towerPullbackMap]

/-- The transition maps of the bases of the levels commute with the base maps of `levπ`. -/
theorem levT_baseMap_levπ (n : ℕ) :
    (levT hW t ht e n).baseMap ≫ (levπ κ e (n + 1)).baseMap = (levπ κ e n).baseMap ≫ ℓ n := by
  have h := congrArg CurveFamily.Hom.baseMap (levT_fac hW t ht e n)
  rw [← t_baseMap t ht n]
  exact h

/-- The base of the `n`-th level is the pullback of `e` and `κ n`. -/
theorem isPullback_lev (n : ℕ) : IsPullback (levA κ e n) (levπ κ e n).baseMap e (κ n) := by
  rw [levπ_baseMap]
  exact isPullback_eqToHom_comp (IsPullback.of_hasPullback e (κ n)) (lev_base κ e n)

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- `isPullback_lev` on underlying schemes. -/
theorem isPullback_lev_toScheme (n : ℕ) :
    IsPullback ((𝒯).map (levA κ e n)) ((𝒯).map (levπ κ e n).baseMap) ((𝒯).map e)
      ((𝒯).map (κ n)) :=
  (isPullback_lev e n).map 𝒯

/-- The base change of the tower to an affine `Q` étale over its top is an étale limit tower over
`Q`. -/
theorem isEtaleLimitTower_lev (he : Etale ((𝒯).map e)) (hQ : IsAffine ((𝒯).obj Q)) :
    IsEtaleLimitTower (fun n => (lev κ e n).base) (levA κ e)
      (fun n => (levT hW t ht e n).baseMap) :=
  hW.of_isPullback e he hQ _ _ _ _ (isPullback_lev_toScheme e) (levT_baseMap_levA hW t ht e)
    (levT_baseMap_levπ hW t ht e)

/-! #### The first level is the chart -/

section Chart

variable {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ (y 0).base} {qZ : Z ⟶ U}
  {pZ : schemeSpace Z ⟶ (y 0).total}
  (hpbZ : IsPullback pZ (schemeSpaceMap qZ) (y 0).toBase (schemeSpaceMap φ))
  {b : U ⟶ Q} (hb : IsPullback b φ e (κ 0))

/-- The base of the first level of the base change is the chart `U`. -/
def levIso0 : (lev κ e 0).base ≅ U := (isPullback_lev e 0).isoIsPullback _ _ hb

/-- `levIso0` is compatible with the maps to the first level of the tower. -/
theorem levIso0_hom_φ : (levIso0 e hb).hom ≫ φ = (levπ κ e 0).baseMap :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- `levIso0` is compatible with the maps to `Q`. -/
theorem levIso0_hom_b : (levIso0 e hb).hom ≫ b = levA κ e 0 :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

include hpbZ in
/-- The chart scheme `Z` is the base change of `y₀` along the base map of `levπ κ e 0`. -/
theorem isPullback_chart0 :
    IsPullback pZ (schemeSpaceMap qZ ≫ schemeSpaceMap (levIso0 e hb).inv) (y 0).toBase
      (schemeSpaceMap (levπ κ e 0).baseMap) := by
  refine hpbZ.of_iso (Iso.refl _) (Iso.refl _)
    ((schemeSpaceFunctor B integerBase hZ).mapIso (levIso0 e hb)).symm (Iso.refl _)
    (by simp) (by rw [Iso.refl_hom, Category.id_comp]; rfl) (by simp) ?_
  rw [← levIso0_hom_φ e hb]
  show (schemeSpaceFunctor B integerBase hZ).map φ ≫ 𝟙 _ =
    (schemeSpaceFunctor B integerBase hZ).map (levIso0 e hb).inv ≫
      (schemeSpaceFunctor B integerBase hZ).map ((levIso0 e hb).hom ≫ φ)
  rw [← Functor.map_comp, Iso.inv_hom_id_assoc, Category.comp_id]

/-- The total space of the first level of the base change is the chart scheme `Z`. -/
def totalIso0 : schemeSpace Z ≅ (lev κ e 0).total :=
  (isPullback_chart0 e hpbZ hb).isoIsPullback _ _ (levπ κ e 0).cartesian

/-- `totalIso0` is compatible with the projections to the bases. -/
theorem totalIso0_hom_toBase :
    (totalIso0 e hpbZ hb).hom ≫ (lev κ e 0).toBase =
      schemeSpaceMap qZ ≫ schemeSpaceMap (levIso0 e hb).inv :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

include hpbZ hb in
/-- The total space of the first level of the base change is representable. -/
theorem isRepresentable_lev_zero : (lev κ e 0).total.obj.IsRepresentable :=
  have : (yoneda.obj Z).IsRepresentable := inferInstance
  isRepresentable_of_natIso (yoneda.obj Z) ((ObjectProperty.ι _).mapIso (totalIso0 e hpbZ hb))

include hW t ht hpbZ hb in
/-- The total spaces of all levels of the base change are representable: each level is a
thickening of the first. -/
theorem isRepresentable_lev (he : Etale ((𝒯).map e)) (hQ : IsAffine ((𝒯).obj Q)) (n : ℕ) :
    (lev κ e n).total.obj.IsRepresentable := by
  induction n with
  | zero => exact isRepresentable_lev_zero e hpbZ hb
  | succ n ih =>
    exact CurveFamily.isRepresentable_total_of_hom (levT hW t ht e n)
      ((isEtaleLimitTower_lev hW t ht e he hQ).isThickening_ℓ n) ih

end Chart

/-! #### The tower of rings and of schemes over the levels -/

section Tower

variable (κ) in
/-- The ring of global sections of the `n`-th level of the base change. -/
abbrev ringLev (n : ℕ) : Type u := Γ((𝒯).obj (lev κ e n).base, ⊤)

/-- The transition maps of the rings of the levels. -/
def ringT (n : ℕ) : ringLev κ e (n + 1) →+* ringLev κ e n :=
  ((𝒯).map (levT hW t ht e n).baseMap).appTop.hom

/-- The composite of the transition maps of the rings is the map on global sections of the
composite of the transition maps of the bases. -/
theorem toBase_ringT (n : ℕ) :
    toBase (ringT hW t ht e) n =
      ((𝒯).map (towerToLevel (fun n => (levT hW t ht e n).baseMap) n)).appTop.hom := by
  induction n with
  | zero =>
    simp only [towerToLevel, CategoryTheory.Functor.map_id]
    rfl
  | succ n ih =>
    ext r
    simp only [toBase_succ, towerToLevel, Functor.map_comp, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply, ih]
    rfl

/-- The composite transition maps of the bases of the levels commute with the base maps of
`levπ`. -/
theorem towerToLevel_levπ (n : ℕ) :
    towerToLevel (fun n => (levT hW t ht e n).baseMap) n ≫ (levπ κ e n).baseMap =
      (levπ κ e 0).baseMap ≫ towerToLevel ℓ n :=
  towerToLevel_comm (fun n => (levπ κ e n).baseMap) (levT_baseMap_levπ hW t ht e) n

/-- The first level sits in the `n`-th as the base change of `W₀ ⟶ Wₙ`. -/
theorem isPullback_towerToLevel (he : Etale ((𝒯).map e)) (hQ : IsAffine ((𝒯).obj Q)) (n : ℕ) :
    IsPullback ((𝒯).map (towerToLevel (fun n => (levT hW t ht e n).baseMap) n))
      ((𝒯).map (levπ κ e 0).baseMap) ((𝒯).map (levπ κ e n).baseMap)
      ((𝒯).map (towerToLevel ℓ n)) := by
  refine IsPullback.of_right ?_ (by rw [← Functor.map_comp, ← Functor.map_comp,
    towerToLevel_levπ]) (isPullback_lev_toScheme e n)
  rw [← Functor.map_comp, ← Functor.map_comp,
    (isEtaleLimitTower_lev hW t ht e he hQ).towerToLevel_comp n, hW.towerToLevel_comp n]
  exact isPullback_lev_toScheme e 0

/-- The transition maps of the rings of the levels are surjective. -/
theorem ringT_surjective (haff : ∀ n, IsAffine ((𝒯).obj (lev κ e n).base))
    (he : Etale ((𝒯).map e)) (hQ : IsAffine ((𝒯).obj Q)) (n : ℕ) :
    Function.Surjective (ringT hW t ht e n) := by
  have := haff (n + 1)
  have := ((isEtaleLimitTower_lev hW t ht e he hQ).isThickening_ℓ n).1
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine _).2

/-- The kernels of the maps from the rings of the levels to the first one are square-zero. -/
theorem ker_toBase_ringT_sq (haff : ∀ n, IsAffine ((𝒯).obj (lev κ e n).base))
    (haffW : ∀ n, IsAffine ((𝒯).obj (y n).base)) (he : Etale ((𝒯).map e))
    (hQ : IsAffine ((𝒯).obj Q))
    (hsq : ∀ n, RingHom.ker ((𝒯).map (towerToLevel ℓ n)).appTop.hom ^ 2 = ⊥) (n : ℕ) :
    RingHom.ker (toBase (ringT hW t ht e) n) ^ 2 = ⊥ := by
  have := haff n
  have := haffW n
  have := haffW 0
  rw [toBase_ringT]
  have hpo := isPushout_appTop_of_isPullback (isPullback_towerToLevel hW t ht e he hQ n)
  have := (hW.isThickening_towerToLevel n).1
  obtain ⟨-, hker⟩ := surjective_and_ker_eq_of_isPushout hpo
    (IsClosedImmersion.isAffine_surjective_of_isAffine _).2
  rw [hker, ← Ideal.map_pow, hsq n, Ideal.map_bot]

/-- The ring of the first level is Noetherian. -/
theorem isNoetherianRing_ringLev_zero (he : Etale ((𝒯).map e))
    (hnoeth : IsLocallyNoetherian ((𝒯).obj (y 0).base))
    (haff0 : IsAffine ((𝒯).obj (lev κ e 0).base)) : IsNoetherianRing (ringLev κ e 0) := by
  have : Etale ((𝒯).map e) := he
  have : Etale ((𝒯).map (levπ κ e 0).baseMap) :=
    MorphismProperty.of_isPullback (isPullback_lev_toScheme e 0) he
  have : IsLocallyNoetherian ((𝒯).obj (lev κ e 0).base) :=
    LocallyOfFiniteType.isLocallyNoetherian ((𝒯).map (levπ κ e 0).baseMap)
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

variable (hrep : ∀ n, (lev κ e n).total.obj.IsRepresentable)

variable (κ) in
/-- The scheme of the `n`-th level of the base change. -/
abbrev schemeLev (n : ℕ) : Scheme.{u} := (𝒯).obj (CurveFamily.totalSite (hrep n))

variable (κ) in
/-- The structure morphism of the `n`-th level, to the spectrum of its ring. -/
def schemeπ (n : ℕ) : schemeLev κ e hrep n ⟶ Spec (.of (ringLev κ e n)) :=
  (𝒯).map (CurveFamily.totalSiteToBase (hrep n)) ≫ ((𝒯).obj (lev κ e n).base).toSpecΓ

/-- The transition maps of the schemes of the levels. -/
def schemeι (n : ℕ) : schemeLev κ e hrep n ⟶ schemeLev κ e hrep (n + 1) :=
  (𝒯).map (CurveFamily.totalSiteMap (hrep (n + 1)) (hrep n) (levT hW t ht e n))

/-- Each level of schemes is the base change of the next along the map of spectra of the
transition map of rings. -/
theorem isPullback_scheme (haff : ∀ n, IsAffine ((𝒯).obj (lev κ e n).base)) (n : ℕ) :
    IsPullback (schemeι hW t ht e hrep n) (schemeπ κ e hrep n) (schemeπ κ e hrep (n + 1))
      (Spec.map (CommRingCat.ofHom (ringT hW t ht e n))) := by
  have := haff n
  have := haff (n + 1)
  refine ((CurveFamily.isPullback_totalSite (hrep (n + 1)) (hrep n)
    (levT hW t ht e n)).map 𝒯).paste_vert ?_
  exact IsPullback.of_vert_isIso ⟨Scheme.toSpecΓ_naturality _⟩

/-- The structure morphisms of the levels are flat. -/
theorem flat_schemeπ (haff : ∀ n, IsAffine ((𝒯).obj (lev κ e n).base)) (n : ℕ) :
    Flat (schemeπ κ e hrep n) := by
  have := haff n
  have := CurveFamily.flat_toScheme_map_totalSiteToBase (hrep n)
  unfold schemeπ
  infer_instance

/-- The structure morphisms of the levels are proper. -/
theorem isProper_schemeπ (haff : ∀ n, IsAffine ((𝒯).obj (lev κ e n).base)) (n : ℕ) :
    IsProper (schemeπ κ e hrep n) := by
  have := haff n
  have := CurveFamily.isProper_toScheme_map_totalSiteToBase (hrep n)
  unfold schemeπ
  infer_instance

/-- The structure morphisms of the levels are locally of finite presentation. -/
theorem locallyOfFinitePresentation_schemeπ (haff : ∀ n, IsAffine ((𝒯).obj (lev κ e n).base))
    (n : ℕ) : LocallyOfFinitePresentation (schemeπ κ e hrep n) := by
  have := haff n
  have := CurveFamily.locallyOfFinitePresentation_toScheme_map_totalSiteToBase (hrep n)
  unfold schemeπ
  infer_instance

end Tower

/-! #### The good two-chart datum on the first level -/

section Datum

variable {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ (y 0).base} {qZ : Z ⟶ U}
  {pZ : schemeSpace Z ⟶ (y 0).total}
  (hpbZ : IsPullback pZ (schemeSpaceMap qZ) (y 0).toBase (schemeSpaceMap φ))
  {b : U ⟶ Q} (hb : IsPullback b φ e (κ 0))
  (hrep : ∀ n, (lev κ e n).total.obj.IsRepresentable)

/-- The chart scheme `Z` is the scheme of the first level. -/
def chartIso : Z ≅ CurveFamily.totalSite (hrep 0) :=
  Yoneda.fullyFaithful.preimageIso
    ((ObjectProperty.ι _).mapIso (totalIso0 e hpbZ hb) ≪≫ (CurveFamily.totalSiteIso (hrep 0)).symm)

/-- `chartIso` is compatible with the projections to the bases. -/
theorem chartIso_hom_hom :
    (chartIso e hpbZ hb hrep).hom ≫ CurveFamily.totalSiteToBase (hrep 0) =
      qZ ≫ (levIso0 e hb).inv := by
  apply yoneda.map_injective
  rw [Functor.map_comp, CurveFamily.yoneda_map_totalSiteToBase, Functor.map_comp]
  have h1 : yoneda.map (chartIso e hpbZ hb hrep).hom =
      (totalIso0 e hpbZ hb).hom.hom ≫ (CurveFamily.totalSiteIso (hrep 0)).inv :=
    Yoneda.fullyFaithful.map_preimage _
  have h2 := congrArg (fun k => k.hom) (totalIso0_hom_toBase e hpbZ hb)
  rw [h1]
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun k => (totalIso0 e hpbZ hb).hom.hom ≫ k) (Iso.inv_hom_id_assoc _ _))).trans h2

include hpbZ hb in
/-- **The good two-chart datum of the chart moves to the first level of the base change.** -/
theorem exists_isGood_schemeLev_zero (haff : ∀ n, IsAffine ((𝒯).obj (lev κ e n).base))
    (D : TwoChartDatum ((𝒯).obj Z)) (hD : D.IsGood ((𝒯).map qZ).appTop.hom) :
    ∃ D' : TwoChartDatum (schemeLev κ e hrep 0),
      D'.IsGood (TwoChartDatum.baseOfSpec (schemeπ κ e hrep 0)) := by
  have := haff 0
  set ε := levIso0 e hb
  let g : ringLev κ e 0 →+* Γ((𝒯).obj U, ⊤) := ((𝒯).map ε.inv).appTop.hom
  have : IsIso ((𝒯).map ε.inv).appTop := inferInstanceAs (IsIso (((𝒯).map ε.inv).app ⊤))
  have hbij : Function.Bijective g := ConcreteCategory.bijective_of_isIso ((𝒯).map ε.inv).appTop
  have hker : RingHom.ker g = ⊥ := (RingHom.injective_iff_ker_eq_bot g).1 hbij.1
  have hker2 : RingHom.ker g ^ 2 = ⊥ := by rw [hker]; simp
  let πZ : (𝒯).obj Z ⟶ Spec (.of Γ((𝒯).obj U, ⊤)) := (𝒯).map qZ ≫ ((𝒯).obj U).toSpecΓ
  have : IsIso (Spec.map (CommRingCat.ofHom g)) :=
    inferInstanceAs (IsIso (Spec.map ((𝒯).map ε.inv).appTop))
  have hsq : IsPullback ((𝒯).map (chartIso e hpbZ hb hrep).hom) πZ (schemeπ κ e hrep 0)
      (Spec.map (CommRingCat.ofHom g)) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    have h := chartIso_hom_hom e hpbZ hb hrep
    show (𝒯).map (chartIso e hpbZ hb hrep).hom ≫ (𝒯).map (CurveFamily.totalSiteToBase (hrep 0)) ≫
      ((𝒯).obj (lev κ e 0).base).toSpecΓ = ((𝒯).map qZ ≫ ((𝒯).obj U).toSpecΓ) ≫
        Spec.map ((𝒯).map ε.inv).appTop
    rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc,
      Category.assoc, Scheme.toSpecΓ_naturality]
  have hflat := flat_schemeπ e hrep haff 0
  have hDπ : D.IsGood (TwoChartDatum.baseOfSpec πZ) := by
    rw [baseOfSpec_comp_toSpecΓ]
    exact hD
  obtain ⟨D', hU', hV', h1, h2, h3, h4⟩ :=
    twoChartDatumLifts _ _ g hbij.2 hker2 _ _ πZ (schemeπ κ e hrep 0) _ hsq hflat D hDπ
  exact ⟨D', (twoChartGoodOfThickening _ _ g hbij.2 hker2 _ _ πZ _ _ hsq hflat D D' hU' hV'
    h1 h2 h3 h4 hDπ).1⟩

end Datum

/-! #### The limit object over the chart -/

section Effective

/-- Global sections over `Q`, as compatible systems of sections over the levels. -/
def limitRingHom : Γ((𝒯).obj Q, ⊤) →+* limit (ringT hW t ht e) :=
  (RingHom.pi fun n => ((𝒯).map (levA κ e n)).appTop.hom).codRestrict _ fun g n => by
    change ringT hW t ht e n (((𝒯).map (levA κ e (n + 1))).appTop g) =
      ((𝒯).map (levA κ e n)).appTop g
    rw [ringT, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Functor.map_comp,
      levT_baseMap_levA]

/-- Global sections over `Q` are the limit of the rings of the levels. -/
theorem limitRingHom_bijective (he : Etale ((𝒯).map e)) (hQ : IsAffine ((𝒯).obj Q)) :
    Function.Bijective (limitRingHom hW t ht e) := by
  have hWQ := isEtaleLimitTower_lev hW t ht e he hQ
  have hid : Etale ((𝒯).map (𝟙 Q)) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  have hpb : ∀ n, IsPullback ((𝒯).map (levA κ e n)) ((𝒯).map (𝟙 _)) ((𝒯).map (𝟙 Q))
      ((𝒯).map (levA κ e n)) := fun n => by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact IsPullback.id_vert _
  have key := fun (s : ∀ n, ringLev κ e n) (hs : ∀ n, ringT hW t ht e n (s (n + 1)) = s n) =>
    hWQ.existsUnique (𝟙 Q) hid hQ (fun n => (lev κ e n).base) (levA κ e) (fun n => 𝟙 _)
      (fun n => (levT hW t ht e n).baseMap) hpb (levT_baseMap_levA hW t ht e) (fun n => by simp)
      s hs
  refine ⟨fun g g' h => ?_, fun s => ?_⟩
  · obtain ⟨g₀, -, hu⟩ := key (limitRingHom hW t ht e g).1 (limitRingHom hW t ht e g).2
    refine (hu g fun n => rfl).trans (hu g' fun n => ?_).symm
    exact (congrFun (congrArg Subtype.val h) n).symm
  · obtain ⟨g₀, hg₀, -⟩ := key s.1 s.2
    exact ⟨g₀, Subtype.ext (funext hg₀)⟩

include ht in
/-- **The limit object over an affine étale chart of the top.** Given the representability of the
levels of the base change of the tower to `Q` and a good two-chart datum on its first level, (E)
produces a family of curves `Ŷ` over `Q` with compatible morphisms from the levels. -/
theorem exists_limit_chart (he : Etale ((𝒯).map e)) (hQ : IsAffine ((𝒯).obj Q))
    (hsq : ∀ n, RingHom.ker ((𝒯).map (towerToLevel ℓ n)).appTop.hom ^ 2 = ⊥)
    (hnoeth : IsLocallyNoetherian ((𝒯).obj (y 0).base))
    (haffW : ∀ n, IsAffine ((𝒯).obj (y n).base))
    (haff : ∀ n, IsAffine ((𝒯).obj (lev κ e n).base))
    (hrep : ∀ n, (lev κ e n).total.obj.IsRepresentable)
    (D : TwoChartDatum (schemeLev κ e hrep 0))
    (hD : D.IsGood (TwoChartDatum.baseOfSpec (schemeπ κ e hrep 0))) :
    ∃ (Ŷ : CurveFamily B hZ) (_ : (curvesProjectionOver B hZ).obj Ŷ = Q)
      (j : ∀ n, lev κ e n ⟶ Ŷ),
      (∀ n, (curvesProjectionOver B hZ).IsHomLift (pullback.fst e (κ n)) (j n)) ∧
      ∀ n (w : lev κ e n ⟶ lev κ e (n + 1)),
        (curvesProjectionOver B hZ).IsHomLift (towerPullbackMap hW e n) w →
        w ≫ levπ κ e (n + 1) = levπ κ e n ≫ t n → w ≫ j (n + 1) = j n := by
  have := hQ
  have hfR := ringT_surjective hW t ht e haff he hQ
  have hsqR := ker_toBase_ringT_sq hW t ht e haff haffW he hQ hsq
  obtain ⟨Y, πY, jE, hflatY, hpropY, hlfpY, hpbY, hcompY⟩ :=
    twoChartTowerEffective (fun n => ringLev κ e n) (ringT hW t ht e) hfR hsqR
      (isNoetherianRing_ringLev_zero e he hnoeth (haff 0))
      (schemeLev κ e hrep) (schemeπ κ e hrep) (schemeι hW t ht e hrep)
      (isPullback_scheme hW t ht e hrep haff) (flat_schemeπ e hrep haff)
      (isProper_schemeπ e hrep haff 0) (locallyOfFinitePresentation_schemeπ e hrep haff 0) D hD
  have hθ := limitRingHom_bijective hW t ht e he hQ
  have : IsIso (CommRingCat.ofHom (limitRingHom hW t ht e)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hθ
  let ψ : Spec (.of (limit (ringT hW t ht e))) ⟶ (𝒯).obj Q :=
    Spec.map (CommRingCat.ofHom (limitRingHom hW t ht e)) ≫ ((𝒯).obj Q).isoSpec.inv
  let gY : Y ⟶ (𝒯).obj Q := πY ≫ ψ
  have := hpropY
  have := hflatY
  have := hlfpY
  have hY : B.Contains Y := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact gY Q.left.2
  let T : BigFppfOver B integerBase hZ := CurveFamily.ofScheme Y hY
  let gS : T ⟶ Q := CurveFamily.homOfScheme gY
  have hsq' : ∀ n, IsPullback (jE n) ((𝒯).map (CurveFamily.totalSiteToBase (hrep n)))
      gY ((𝒯).map (levA κ e n)) := by
    intro n
    have := haff n
    refine (hpbY n).of_iso (Iso.refl _) (Iso.refl _)
      (asIso ((𝒯).obj (lev κ e n).base).toSpecΓ).symm (asIso ψ) (by simp) ?_ (by simp [gY]) ?_
    · simp [schemeπ]
    · have h1 : CommRingCat.ofHom (limitRingHom hW t ht e) ≫
          CommRingCat.ofHom (towerLimitProj (ringT hW t ht e) n) =
            ((𝒯).map (levA κ e n)).appTop := rfl
      show Spec.map _ ≫ Spec.map _ ≫ _ = _
      rw [← Category.assoc, ← Spec.map_comp, h1, Scheme.isoSpec_inv_naturality]
      rfl
  have hWQ := isEtaleLimitTower_lev hW t ht e he hQ
  have hj0 : Stacks.Thickenings.IsThickening (jE 0) :=
    Stacks.Thickenings.isThickening_of_isPullback (hpbY 0)
      (isThickening_specMap_of_isNilpotent _ (towerLimitProj_zero_surjective _ hfR)
        (fun _ hr => isNilpotent_of_towerLimitProj_zero _ hsqR hr))
  have hfib : ∀ s, topologicalKrullDim (((𝒯).map gS).fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    have := hj0.1
    have := hWQ.isThickening_zero.1
    exact topologicalKrullDim_fiber_le_of_comm (jE 0) _ gY _ (hsq' 0).w
      (jE 0).isClosedEmbedding.isEmbedding hj0.2
      ((𝒯).map (levA κ e 0)).isClosedEmbedding.isEmbedding.injective hWQ.isThickening_zero.2
      (CurveFamilyScheme.topologicalKrullDim_fiber_totalSiteToBase_le (hrep 0))
  let Ŷ : CurveFamily B hZ := CurvesFormal.curveFamilyOfFiberDimensionLE B hZ gS
    (inferInstanceAs (Flat gY)) (inferInstanceAs (IsProper gY))
    (inferInstanceAs (LocallyOfFinitePresentation gY)) hfib
  have hS : ∀ n, IsPullback
      (CurveFamily.homOfScheme (jE n) : CurveFamily.totalSite (hrep n) ⟶ T)
      (CurveFamily.totalSiteToBase (hrep n)) gS (levA κ e n) := fun n =>
    CurveFamily.isPullback_of_isPullback_toScheme_map ((𝒯).map_injective (hsq' n).w) (hsq' n)
  let j : ∀ n, lev κ e n ⟶ Ŷ := fun n =>
    { baseMap := levA κ e n
      totalMap := (CurveFamilyScheme.totalSpaceIso (hrep n)).inv ≫
        schemeSpaceMap (CurveFamily.homOfScheme (jE n) : CurveFamily.totalSite (hrep n) ⟶ T)
      cartesian := by
        refine (CurveFamily.isPullback_schemeSpaceMap_of_isPullback (hS n)).of_iso
          (CurveFamilyScheme.totalSpaceIso (hrep n)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm) ?_
          ((Category.comp_id _).trans (Category.id_comp _).symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm)
        rw [Iso.refl_hom, Category.comp_id, CurveFamilyScheme.totalSpaceIso_hom_toBase] }
  refine ⟨Ŷ, rfl, j, fun n => ?_, fun n w hw hfac => ?_⟩
  · refine IsHomLift.of_fac' _ _ _ (lev_base κ e n) rfl ?_
    show levA κ e n = _
    rw [levA]
    congr 1
  · have := hw
    rw [levT_uniq hW t ht e n w hfac]
    refine CurveFamily.Hom.ext (levT_baseMap_levA hW t ht e n) ?_
    show (levT hW t ht e n).totalMap ≫ (CurveFamilyScheme.totalSpaceIso (hrep (n + 1))).inv ≫
        schemeSpaceMap (CurveFamily.homOfScheme (jE (n + 1)) :
          CurveFamily.totalSite (hrep (n + 1)) ⟶ T) =
      (CurveFamilyScheme.totalSpaceIso (hrep n)).inv ≫
        schemeSpaceMap (CurveFamily.homOfScheme (jE n) : CurveFamily.totalSite (hrep n) ⟶ T)
    have h1 : (levT hW t ht e n).totalMap ≫ (CurveFamilyScheme.totalSpaceIso (hrep (n + 1))).inv =
        (CurveFamilyScheme.totalSpaceIso (hrep n)).inv ≫
          schemeSpaceMap (CurveFamily.totalSiteMap (hrep (n + 1)) (hrep n) (levT hW t ht e n)) := by
      rw [Iso.comp_inv_eq, Category.assoc, ← CurveFamilyScheme.totalSpaceIso_hom_totalMap,
        Iso.inv_hom_id_assoc]
    have h2 : CurveFamily.totalSiteMap (hrep (n + 1)) (hrep n) (levT hW t ht e n) ≫
        (CurveFamily.homOfScheme (jE (n + 1)) : CurveFamily.totalSite (hrep (n + 1)) ⟶ T) =
        CurveFamily.homOfScheme (jE n) :=
      (𝒯).map_injective (by rw [Functor.map_comp]; exact hcompY n)
    rw [← Category.assoc, h1, Category.assoc, ← schemeSpaceMap_comp, h2]

end Effective

end TowerCharts

/-! ### Local effectivity data for towers of families of curves -/

section Main

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

open TowerCharts in
/-- **Local effectivity data for a tower of families of curves over an étale limit tower.** Let
`Wₙ ⟶ V` be an étale limit tower whose first level is locally Noetherian and whose levels are
square-zero thickenings of the first (`Ker(Γ(Wₙ) → Γ(W₀))² = 0`), and let `y₀ → y₁ → ⋯` be
families of curves over the levels with transition morphisms over those of the tower. Then the
tower has local effectivity data (`AlgebraicGeometry.C1590Private.TowerChartData`): an étale
covering of `V` by affines `Qᵢ`, families of curves `Ŷᵢ` over `Qᵢ`, and compatible morphisms from
the restricted levels.

Around every point of `W₀` there is an étale chart `U ⟶ W₀` over which `y₀` is a scheme with a good
two-chart datum (piece (C), `AlgebraicGeometry.C1590Private.hasTwoChartEtaleCovers`). The chart
lifts to an affine `Q` étale over `V` (Stacks 039R), the levels of the tower over `Q` are schemes
(Stacks 05ZR), their rings form a tower with square-zero kernels whose limit is `Γ(Q)` (the
tower is an étale limit tower), and piece (E)
(`AlgebraicGeometry.C1590Private.twoChartTowerEffective`) gives the limit family over `Q`. -/
theorem nonempty_towerChartData_curves [(curvesProjectionOver B hZ).IsFibered]
    {V : BigFppfOver B integerBase hZ} {y : ℕ → CurveFamily B hZ}
    {κ : ∀ n, (y n).base ⟶ V} {ℓ : ∀ n, (y n).base ⟶ (y (n + 1)).base}
    (hW : IsEtaleLimitTower (fun n => (y n).base) κ ℓ)
    (t : ∀ n, y n ⟶ y (n + 1)) (ht : ∀ n, (curvesProjectionOver B hZ).IsHomLift (ℓ n) (t n))
    (hsq : ∀ n, RingHom.ker ((𝒯).map (towerToLevel ℓ n)).appTop.hom ^ 2 = ⊥)
    (hnoeth : IsLocallyNoetherian ((𝒯).obj (y 0).base)) :
    Nonempty (TowerChartData (curvesProjectionOver B hZ) hW y (fun _ => rfl) t) := by
  have := hW.isAffine
  have := hW.isThickening_zero.1
  have haffW0 : IsAffine ((𝒯).obj (y 0).base) := isAffine_of_isAffineHom ((𝒯).map (κ 0))
  have haffW : ∀ n, IsAffine ((𝒯).obj (y n).base) := fun n =>
    Stacks.Thickenings.isAffine_of_isThickening (hW.isThickening_towerToLevel n)
  -- an étale chart with a good two-chart datum through every point of `W₀`
  have hC := fun s => hasTwoChartEtaleCovers B hZ (y 0) haffW0 hnoeth s
  choose U Z φ qZ pZ hφ hs hU hpbZ D hD using hC
  -- its lift to an affine étale chart of `V`
  have hL := fun s => FormalSpace.exists_isPullback_affine_etale_lift_of_isThickening (κ 0)
    hW.isThickening_zero (U s) (hU s) (φ s) (hφ s)
  choose Q e b hQ he hb using hL
  -- the limit family over each chart
  have hY : ∀ s, ∃ (Ŷ : CurveFamily B hZ) (_ : (curvesProjectionOver B hZ).obj Ŷ = Q s)
      (j : ∀ n, lev κ (e s) n ⟶ Ŷ),
      (∀ n, (curvesProjectionOver B hZ).IsHomLift (pullback.fst (e s) (κ n)) (j n)) ∧
      ∀ n (w : lev κ (e s) n ⟶ lev κ (e s) (n + 1)),
        (curvesProjectionOver B hZ).IsHomLift (towerPullbackMap hW (e s) n) w →
        w ≫ levπ κ (e s) (n + 1) = levπ κ (e s) n ≫ t n → w ≫ j (n + 1) = j n := by
    intro s
    have hWQ := isEtaleLimitTower_lev hW t ht (e s) (he s) (hQ s)
    have := hU s
    have haff0 : IsAffine ((𝒯).obj (lev κ (e s) 0).base) :=
      IsAffine.of_isIso ((𝒯).map (levIso0 (e s) (hb s)).hom)
    have haff : ∀ n, IsAffine ((𝒯).obj (lev κ (e s) n).base) := fun n =>
      Stacks.Thickenings.isAffine_of_isThickening (hWQ.isThickening_towerToLevel n)
    have hrep := isRepresentable_lev hW t ht (e s) (hpbZ s) (hb s) (he s) (hQ s)
    obtain ⟨D', hD'⟩ := exists_isGood_schemeLev_zero (e s) (hpbZ s) (hb s) hrep haff (D s) (hD s)
    exact exists_limit_chart hW t ht (e s) (he s) (hQ s) hsq hnoeth haffW haff hrep D' hD'
  choose Ŷ hŶ j hj hcompat using hY
  refine ⟨{ I := (𝒯).obj (y 0).base
            Q := Q
            q := e
            etale := he
            isAffine := hQ
            covers := fun v => ?_
            Y := Ŷ
            hY := hŶ
            j := j
            isHomLift_j := hj
            compat := fun i n u hu hc => ?_ }⟩
  · obtain ⟨s, rfl⟩ := hW.isThickening_zero.2 v
    obtain ⟨x, hx⟩ := hs s
    refine ⟨s, (𝒯).map (b s) x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, (hb s).w, Functor.map_comp,
      Scheme.Hom.comp_apply, hx]
  · have := hu
    exact hcompat i n u hu hc

end Main

end AlgebraicGeometry.C1590Private

end
