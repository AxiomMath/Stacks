module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizedBlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsResidualSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.NormalizedBlowupEtaleBaseChange

/-!
# Restricting a sequence of normalized blowups to the chosen étale neighbourhoods

Let `X` be a decent algebraic space over a scheme `S` with pairwise distinct closed points
`x₁, …, xₙ` and chosen elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` (Stacks 0BH9), and
assume `X` is normal. A sequence

`Zₘ ⟶ Zₘ₋₁ ⟶ … ⟶ Z₁ ⟶ Z₀ = X`

of normalized blowings up at closed points lying over `{x₁, …, xₙ}` restricts, over each `Uᵢ`, to
a sequence of normalized blowings up of `Uᵢ` at closed points lying over `uᵢ`: a step centred at a
point over `xᵢ` base changes to the normalized blowing up at the unique point above it, and a step
centred at a point over `x_k` with `k ≠ i` base changes to an isomorphism, the base change being
normal. This is the "only if" half of the normal form of Stacks 0BHL.

The normality of `X` cannot be dropped: a normalized blowing up of `X` at `x_k` normalizes `X`
everywhere, so over a neighbourhood `Uᵢ`, `i ≠ k`, of a non-normal point it base changes to the
normalization of `Uᵢ`, which need not be a sequence of normalized blowings up at points over `uᵢ`.

## Main results

* `IsNormalizationOfBlowupAtClosedPoint.isNormalizedBlowupAtClosedPoint` and its converse compare
  the two formulations of Stacks 0BHJ in the library.
* `NormalizedBlowupFactorization.ofEq` and `NormalizedBlowupFactorization.isoComp` transport a
  factorization along an equality of morphisms and along an isomorphism of the source.
* `ClosedPointNeighborhoods.nonempty_localNormalizedBlowupFactorization_of_isPullback`:
  the restriction of a sequence of normalized blowings up of a normal `X` to a neighbourhood.

## References

* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BHJ](https://stacks.math.columbia.edu/tag/0BHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_NormalizedBlowupFactorizationRestriction
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The two formulations of the normalized blowing up -/

/-- A normalization of a blowing up at a closed point, followed by that blowing up, is the
normalized blowing up at the point in the sense of Stacks 0BHJ. -/
theorem IsNormalizationOfBlowupAtClosedPoint.isNormalizedBlowupAtClosedPoint
    {X Y : AlgebraicSpaces B S hS} (hX : IsDecentSpace B S hS X.obj)
    (hXfin : HasLocallyFiniteIrreducibleComponents B S hS X.obj) {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (h : IsNormalizationOfBlowupAtClosedPoint B S hS z hz f) :
    IsNormalizedBlowupAtClosedPoint B S hS hX hXfin z hz f := by
  obtain ⟨X', b, hb, N, e, he⟩ := h
  refine ⟨X', b, hb, N, ObjectProperty.isoMk _ e, ?_⟩
  apply ObjectProperty.hom_ext
  exact he.symm

/-- The normalized blowing up at a closed point in the sense of Stacks 0BHJ is a normalization of
a blowing up at the point, followed by that blowing up. -/
theorem IsNormalizedBlowupAtClosedPoint.isNormalizationOfBlowupAtClosedPoint
    {X Y : AlgebraicSpaces B S hS} {hX : IsDecentSpace B S hS X.obj}
    {hXfin : HasLocallyFiniteIrreducibleComponents B S hS X.obj} {z : points B S hS X.obj}
    {hz : IsClosed ({z} : Set (points B S hS X.obj))} {f : Y ⟶ X}
    (h : IsNormalizedBlowupAtClosedPoint B S hS hX hXfin z hz f) :
    IsNormalizationOfBlowupAtClosedPoint B S hS z hz f := by
  obtain ⟨X', b, hb, N, e, he⟩ := h
  exact ⟨X', b, hb, N, (ObjectProperty.ι _).mapIso e,
    (congrArg (fun k => k.hom) he).symm⟩

/-! ### Transporting a factorization -/

namespace NormalizedBlowupFactorization

variable {X Y Y' : AlgebraicSpaces B S hS}

/-- A factorization of a morphism is one of any morphism equal to it. -/
def ofEq {T : Set (points B S hS X.obj)} {f f' : Y ⟶ X}
    (F : NormalizedBlowupFactorization B S hS T f) (h : f = f') :
    NormalizedBlowupFactorization B S hS T f' :=
  h ▸ F

/-- A factorization of `f` gives one of `e.hom ≫ f` for an isomorphism `e` of the source. -/
def isoComp {T : Set (points B S hS X.obj)} {f : Y ⟶ X}
    (F : NormalizedBlowupFactorization B S hS T f) (e : Y' ≅ Y) :
    NormalizedBlowupFactorization B S hS T (e.hom ≫ f) :=
  F.comp (ofIso _ e)

end NormalizedBlowupFactorization

/-- Normality of an algebraic space transports along an isomorphism of algebraic spaces. -/
theorem isNormal_of_iso {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)
    (h : Space.IsNormal B S hS Y.obj) : Space.IsNormal B S hS X.obj :=
  hasEtaleLocalProperty_of_isEtale B S hS X.property Y.property
    (isEtale_of_iso B S hS ((ObjectProperty.ι _).mapIso e)) h

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The base change `Z ×_X Uᵢ ⟶ Uᵢ` of a morphism `p : Z ⟶ X` to the `i`th neighbourhood, as a
morphism of algebraic spaces. -/
abbrev restrictionHom (i : Fin n) {Z : AlgebraicSpaces B S hS} (p : Z ⟶ D.space) :
    AlgebraicSpaces.fiberProduct B S hS p (D.toSpaceHom i) ⟶ D.neighborhoodSpace i :=
  ObjectProperty.homMk (pullback.snd p.hom (D.toSpaceHom i).hom)

/-- The projection `Z ×_X Uᵢ ⟶ Z`, as a morphism of algebraic spaces. -/
abbrev restrictionFst (i : Fin n) {Z : AlgebraicSpaces B S hS} (p : Z ⟶ D.space) :
    AlgebraicSpaces.fiberProduct B S hS p (D.toSpaceHom i) ⟶ Z :=
  ObjectProperty.homMk (pullback.fst p.hom (D.toSpaceHom i).hom)

/-- A factorization of the canonical base change to `Uᵢ` gives one of the second projection of
any cartesian square over `p` and `Uᵢ ⟶ X`. -/
theorem nonempty_localNormalizedBlowupFactorization_of_isPullback (i : Fin n)
    {Z P : AlgebraicSpaces B S hS} {p : Z ⟶ D.space} {ψ : P ⟶ Z}
    {π : P ⟶ D.neighborhoodSpace i} (sq : IsPullback ψ π p (D.toSpaceHom i))
    (h : Nonempty (D.LocalNormalizedBlowupFactorization i (D.restrictionHom i p))) :
    Nonempty (D.LocalNormalizedBlowupFactorization i π) := by
  obtain ⟨F⟩ := h
  have hP := AlgebraicSpaces.isPullback_fiberProduct B S hS p (D.toSpaceHom i)
  exact ⟨(F.isoComp (hP.isoIsPullback _ _ sq).symm).ofEq (hP.isoIsPullback_inv_snd _ _ sq)⟩

/-- The base change of `b ≫ p` to `Uᵢ` is the base change along `Z ×_X Uᵢ ⟶ Z` of `b`, followed
by the base change of `p`. -/
theorem exists_iso_restrictionHom_comp (i : Fin n) {Z Z' : AlgebraicSpaces B S hS}
    (p : Z ⟶ D.space) (b : Z' ⟶ Z) :
    ∃ e : AlgebraicSpaces.fiberProduct B S hS (b ≫ p) (D.toSpaceHom i) ≅
        AlgebraicSpaces.fiberProduct B S hS (D.restrictionFst i p) b,
      e.hom ≫ (ObjectProperty.homMk (pullback.fst (D.restrictionFst i p).hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS (D.restrictionFst i p) b ⟶ _) ≫
          D.restrictionHom i p = D.restrictionHom i (b ≫ p) := by
  let ε : pullback (b.hom ≫ p.hom) (D.toSpaceHom i).hom ≅
      pullback (pullback.fst p.hom (D.toSpaceHom i).hom) b.hom :=
    (pullbackRightPullbackFstIso p.hom (D.toSpaceHom i).hom b.hom).symm ≪≫ pullbackSymmetry _ _
  refine ⟨ObjectProperty.isoMk _ ε, ?_⟩
  apply ObjectProperty.hom_ext
  change ε.hom ≫ pullback.fst (pullback.fst p.hom (D.toSpaceHom i).hom) b.hom ≫
    pullback.snd p.hom (D.toSpaceHom i).hom = pullback.snd (b.hom ≫ p.hom) (D.toSpaceHom i).hom
  simp only [ε, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [pullbackSymmetry_hom_comp_fst_assoc, pullbackRightPullbackFstIso_inv_snd_snd]

/-- The projection `Z ×_X Uᵢ ⟶ Z` is étale. -/
private theorem isEtale_restrictionFst (i : Fin n) {Z : AlgebraicSpaces B S hS}
    (p : Z ⟶ D.space) : IsEtale B S hS (D.restrictionFst i p).hom :=
  isEtale_pullback_fst B S hS Z.property D.space.property (D.neighborhoodSpace i).property
    _ _ (D.neighborhood i).etale_toSpace

/-- A factorization of the composite of `pullback.fst` of `ψ` and `b` with the base change of `p`
gives one of the base change of `b ≫ p`. -/
private theorem nonempty_restriction_comp_of_factorization (i : Fin n)
    {Z Z' : AlgebraicSpaces B S hS} (p : Z ⟶ D.space) (b : Z' ⟶ Z)
    (G : D.LocalNormalizedBlowupFactorization i
      ((ObjectProperty.homMk (pullback.fst (D.restrictionFst i p).hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS (D.restrictionFst i p) b ⟶ _) ≫
        D.restrictionHom i p)) :
    Nonempty (D.LocalNormalizedBlowupFactorization i (D.restrictionHom i (b ≫ p))) := by
  obtain ⟨e, he⟩ := D.exists_iso_restrictionHom_comp i p b
  exact ⟨(G.isoComp e).ofEq he⟩

/-- **One step of the restriction, at the neighbourhood of the centre.** If `b : Z' ⟶ Z` is the
normalized blowing up at a closed point `z` lying over `xᵢ`, then the base change of `Z'` to `Uᵢ`
is obtained from that of `Z` by a normalized blowing up at a closed point over `uᵢ`. -/
theorem nonempty_localNormalizedBlowupFactorization_comp_of_eq (i : Fin n)
    {Z Z' : AlgebraicSpaces B S hS} (p : Z ⟶ D.space) {hZ : IsDecentSpace B S hS Z.obj}
    {hZfin : HasLocallyFiniteIrreducibleComponents B S hS Z.obj} {z : points B S hS Z.obj}
    {hz : IsClosed ({z} : Set (points B S hS Z.obj))} {b : Z' ⟶ Z}
    (hb : IsNormalizedBlowupAtClosedPoint B S hS hZ hZfin z hz b)
    (hzx : pointsMap B S hS Z.obj p.hom z = D.point i)
    (F : D.LocalNormalizedBlowupFactorization i (D.restrictionHom i p)) :
    Nonempty (D.LocalNormalizedBlowupFactorization i (D.restrictionHom i (b ≫ p))) := by
  set P := AlgebraicSpaces.fiberProduct B S hS p (D.toSpaceHom i)
  set ψ := D.restrictionFst i p
  have hψ := D.isEtale_restrictionFst i p
  obtain ⟨t, htz, htu⟩ := exists_point_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS p (D.toSpaceHom i)) z (D.neighborhoodPoint i)
    (hzx.trans (D.pointsMap_toSpaceHom_neighborhoodPoint i).symm)
  have hfib : pointsMap B S hS P.obj ψ.hom ⁻¹' {z} = {t} := by
    ext t'
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro ht'
      refine (pointsMap_fst_injOn_of_isIso_fromPreimage (D.toSpaceHom i).hom p.hom
        (D.pointSubspace i) (D.isIso_fromPreimage_pointSubspace i)
        (D.range_pointsMap_ι_pointSubspace i) (t := t') ?_ ?_)
      · change pointsMap B S hS Z.obj p.hom (pointsMap B S hS P.obj ψ.hom t') = D.point i
        rw [ht', hzx]
      · change pointsMap B S hS P.obj ψ.hom t' = pointsMap B S hS P.obj ψ.hom t
        rw [ht', htz]
    · rintro rfl
      exact htz
  have ht : IsClosed ({t} : Set (points B S hS P.obj)) := by
    rw [← hfib]
    exact hz.preimage (continuous_pointsMap B S hS _)
  have hP : IsDecentSpace B S hS P.obj :=
    isDecentSpace_of_isEtale B S hS ψ.hom P.property Z.property hψ hZ
  have hPfin : HasLocallyFiniteIrreducibleComponents B S hS P.obj :=
    hasLocallyFiniteIrreducibleComponents_of_isEtale B S hS hZfin hψ
  have hq := (isNormalizationOfBlowupAtClosedPoint_fiberProduct_of_isEtale hψ ht hfib
    hb.isNormalizationOfBlowupAtClosedPoint).isNormalizedBlowupAtClosedPoint hP hPfin
  exact D.nonempty_restriction_comp_of_factorization i p b
    (F.comp (NormalizedBlowupFactorization.ofBlowup _ hq (by simpa using htu)))

/-- **One step of the restriction, at a neighbourhood missing the centre.** If `Z` is normal and
`b : Z' ⟶ Z` is the normalized blowing up at a closed point `z` lying over `x_k` with `k ≠ i`, then
the base change of `Z'` to `Uᵢ` is that of `Z`. -/
theorem nonempty_localNormalizedBlowupFactorization_comp_of_ne (i k : Fin n) (hik : i ≠ k)
    {Z Z' : AlgebraicSpaces B S hS} (p : Z ⟶ D.space) (hZn : Space.IsNormal B S hS Z.obj)
    {hZ : IsDecentSpace B S hS Z.obj}
    {hZfin : HasLocallyFiniteIrreducibleComponents B S hS Z.obj} {z : points B S hS Z.obj}
    {hz : IsClosed ({z} : Set (points B S hS Z.obj))} {b : Z' ⟶ Z}
    (hb : IsNormalizedBlowupAtClosedPoint B S hS hZ hZfin z hz b)
    (hzx : pointsMap B S hS Z.obj p.hom z = D.point k)
    (F : D.LocalNormalizedBlowupFactorization i (D.restrictionHom i p)) :
    Nonempty (D.LocalNormalizedBlowupFactorization i (D.restrictionHom i (b ≫ p))) := by
  set P := AlgebraicSpaces.fiberProduct B S hS p (D.toSpaceHom i)
  set ψ := D.restrictionFst i p
  have hψ := D.isEtale_restrictionFst i p
  have hPn : Space.IsNormal B S hS P.obj :=
    hasEtaleLocalProperty_of_isEtale B S hS P.property Z.property hψ hZn
  have hfib : pointsMap B S hS P.obj ψ.hom ⁻¹' {z} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun t ht => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ht
    have h1 := congrArg (fun m => pointsMap B S hS _ m.hom t)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS p (D.toSpaceHom i)).w
    simp only [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp_apply] at h1
    refine D.map_ne_point i k hik _ (h1.symm.trans ?_)
    change pointsMap B S hS Z.obj p.hom (pointsMap B S hS _ ψ.hom t) = _
    rw [ht, hzx]
  have hiso : IsIso (pullback.fst ψ.hom b.hom) :=
    isIso_fiberProduct_of_isNormalizationOfBlowupAtClosedPoint hψ hPn hfib
      hb.isNormalizationOfBlowupAtClosedPoint
  let q : AlgebraicSpaces.fiberProduct B S hS ψ b ≅ P :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ (pullback.fst ψ.hom b.hom) hiso)
  exact D.nonempty_restriction_comp_of_factorization i p b (F.isoComp q)

/-- **The restriction of a sequence of normalized blowings up of a normal `X`.** If `X` is
normal and `t` is a tower `Zₘ ⟶ … ⟶ Z₀ = X` of normalized blowings up at closed points lying
over `{x₁, …, xₙ}`, then its top is normal and, for each `i`, the base change `Zₘ ×_X Uᵢ ⟶ Uᵢ` is
a sequence of normalized blowings up at closed points lying over `uᵢ`. -/
theorem isNormal_and_nonempty_localNormalizedBlowupFactorization
    (hXn : Space.IsNormal B S hS D.space.obj) :
    ∀ {Z : AlgebraicSpaces B S hS} (t : NormalizedBlowupTower B S hS D.space Z),
      t.CentersOver (Set.range D.point) →
        Space.IsNormal B S hS Z.obj ∧
          ∀ i, Nonempty (D.LocalNormalizedBlowupFactorization i (D.restrictionHom i t.proj))
  | _, .base e, _ => by
      refine ⟨isNormal_of_iso e hXn, fun i => ?_⟩
      have := (AlgebraicSpaces.isPullback_fiberProduct B S hS e.hom
        (D.toSpaceHom i)).isIso_snd_of_isIso
      exact ⟨NormalizedBlowupFactorization.ofIso _ (asIso (D.restrictionHom i e.hom))⟩
  | _, .step t hZ hZfin b z hz hb, hc => by
      obtain ⟨hct, k, hk⟩ := hc
      obtain ⟨hZn, hF⟩ := isNormal_and_nonempty_localNormalizedBlowupFactorization hXn t hct
      refine ⟨hb.isNormal, fun i => ?_⟩
      obtain ⟨F⟩ := hF i
      obtain rfl | hik := eq_or_ne i k
      · exact D.nonempty_localNormalizedBlowupFactorization_comp_of_eq i t.proj hb hk.symm F
      · exact D.nonempty_localNormalizedBlowupFactorization_comp_of_ne i k hik t.proj hZn hb
          hk.symm F

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
