module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparationLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.CoincidenceLocusAlongPairs
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.InfinitesimalNeighbourhoodNullstellensatz

/-!
# Separating the off-diagonal from the boundary by one blowup

Let `π : X ⟶ Y` be a morphism of algebraic spaces and let `Ō ⊆ X ×_Y X` be a Noetherian closed
subspace, the closure of the off-diagonal part `O` of `U₁ ×_U U₁` in the repaired proof of
Stacks 0F4B. Let `D` (the closure of `f⁻¹ Z₁`) and `∂` (the boundary `X ∖ V₁`) be closed
subspaces of `X`, and suppose that a point of `Ō` with both coordinates in `D` has both
coordinates in `∂` (Step 1 of the proof of `(H)`). By the Nullstellensatz on `Ō` there is `M`
with `q₁⁻¹ D ∩ q₂⁻¹ D ⊆ qᵢ⁻¹(∂⁽ᴹ⁾)`, and after the blowup `β : X' ⟶ X` along
`D ∩ ∂⁽ᴹ⁾` no point over `Ō` in the closure of `O` has both coordinates outside the coincidence
locus of `β⁻¹ D` and the exceptional divisor. This is condition `(H)` of the repair.

## Main results

* `AlgebraicGeometry.Space.exists_mem_coincidenceLocus_or_of_isBlowupAlong`: the statement
  above, for any algebraic space `P'` with maps to `X'` lying over `X ×_Y X`.

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section PointTopology

attribute [local instance] pointTopology

/-- **One blowup separates the off-diagonal from the boundary.** Let `π : X ⟶ Y` be a morphism of
algebraic spaces, `P = X ×_Y X`, and `Ō ⊆ P` a Noetherian closed subspace. Let `D` and `∂` be
closed subspaces of `X` such that a point of `Ō` with both coordinates in `D` has both coordinates
in `∂`, and let `O ⊆ |Ō|` be relatively open with both coordinates off `∂`. Then there is `M`
such that for every blowup `β : X' ⟶ X` along `D ∩ ∂⁽ᴹ⁾` and every point `w'` of `X' ×_Y X'`
over `Ō` in the closure of the points over `O`, one of the coordinates of `w'` lies in the
coincidence locus of `β⁻¹ D` and `β⁻¹(D ∩ ∂⁽ᴹ⁾)`.

The integer `M` comes from the Nullstellensatz on `Ō`, and the conclusion is
`AlgebraicGeometry.Space.mem_coincidenceLocus_or_of_mem_closure` on the inverse image of `Ō`. -/
theorem exists_mem_coincidenceLocus_or_of_isBlowupAlong (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y X : AlgebraicSpaces B S hS} (π : X ⟶ Y)
    (Ob : ClosedSubspaces B S hS (pullback π.hom π.hom))
    (hObN : IsNoetherian B S hS hZ Ob.1.toFunctor) (D Yb : ClosedSubspaces B S hS X.1)
    (H1 : ∀ w ∈ subspacePointSet B S hS _ Ob.1,
      pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∈ subspacePointSet B S hS X.1 D.1 →
      pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∈ subspacePointSet B S hS X.1 D.1 →
      pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∈ subspacePointSet B S hS X.1 Yb.1 ∧
        pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∈ subspacePointSet B S hS X.1 Yb.1)
    {O A : Set (points B S hS (pullback π.hom π.hom))} (hA : IsOpen A)
    (hOA : O = subspacePointSet B S hS _ Ob.1 ∩ A)
    (hO₁ : ∀ w ∈ O, pointsMap B S hS _ (pullback.fst π.hom π.hom) w ∉
      subspacePointSet B S hS X.1 D.1)
    (hO₂ : ∀ w ∈ O, pointsMap B S hS _ (pullback.snd π.hom π.hom) w ∉
      subspacePointSet B S hS X.1 D.1) :
    ∃ M : ℕ, ∀ {X' : AlgebraicSpaces B S hS} (β : X' ⟶ X),
      IsBlowupAlong B S hS (schemeTheoreticIntersection B S hS X.1 X.2 D
        (infinitesimalNeighbourhood B S hS X Yb M)) β →
      ∀ {P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS P')
        (_ : IsNoetherian B S hS hZ P') (c₁ c₂ : P' ⟶ X'.1) (ρ : P' ⟶ pullback π.hom π.hom),
        ρ ≫ pullback.fst π.hom π.hom = c₁ ≫ β.hom → ρ ≫ pullback.snd π.hom π.hom = c₂ ≫ β.hom →
      ∀ w' : points B S hS P', pointsMap B S hS P' ρ w' ∈ subspacePointSet B S hS _ Ob.1 →
        w' ∈ closure (pointsMap B S hS P' ρ ⁻¹' O) →
        pointsMap B S hS P' c₁ w' ∈
            coincidenceLocus B S hS X' (preimageClosedSubspace β D)
              (preimageClosedSubspace β (schemeTheoreticIntersection B S hS X.1 X.2 D
                (infinitesimalNeighbourhood B S hS X Yb M))) ∨
          pointsMap B S hS P' c₂ w' ∈
            coincidenceLocus B S hS X' (preimageClosedSubspace β D)
              (preimageClosedSubspace β (schemeTheoreticIntersection B S hS X.1 X.2 D
                (infinitesimalNeighbourhood B S hS X Yb M))) := by
  classical
  let ObS : AlgebraicSpaces B S hS := ⟨Ob.1.toFunctor, Ob.2.1⟩
  let q₁ : ObS ⟶ X := ObjectProperty.homMk (Ob.1.ι ≫ pullback.fst π.hom π.hom)
  let q₂ : ObS ⟶ X := ObjectProperty.homMk (Ob.1.ι ≫ pullback.snd π.hom π.hom)
  let Z₀ := schemeTheoreticIntersection B S hS ObS.1 ObS.2 (preimageClosedSubspace q₁ D)
    (preimageClosedSubspace q₂ D)
  have hq₁ : ∀ z, pointsMap B S hS _ q₁.hom z =
      pointsMap B S hS _ (pullback.fst π.hom π.hom) (pointsMap B S hS _ Ob.1.ι z) := fun z =>
    pointsMap_comp_apply B S hS _ _ z
  have hq₂ : ∀ z, pointsMap B S hS _ q₂.hom z =
      pointsMap B S hS _ (pullback.snd π.hom π.hom) (pointsMap B S hS _ Ob.1.ι z) := fun z =>
    pointsMap_comp_apply B S hS _ _ z
  have hpre : ∀ (q : ObS ⟶ X) (T : ClosedSubspaces B S hS X.1) z,
      z ∈ subspacePointSet B S hS ObS.1 (preimageClosedSubspace q T).1 ↔
        pointsMap B S hS _ q.hom z ∈ subspacePointSet B S hS X.1 T.1 := fun q T z => by
    change z ∈ subspacePointSet B S hS ObS.1 (T.1.preimage q.hom) ↔ _
    rw [subspacePointSet_preimage]
    rfl
  have hH : ∀ z ∈ subspacePointSet B S hS ObS.1 Z₀.1,
      pointsMap B S hS _ q₁.hom z ∈ subspacePointSet B S hS X.1 Yb.1 ∧
        pointsMap B S hS _ q₂.hom z ∈ subspacePointSet B S hS X.1 Yb.1 := fun z hz => by
    change z ∈ subspacePointSet B S hS ObS.1
      ((preimageClosedSubspace q₁ D).1 ⊓ (preimageClosedSubspace q₂ D).1) at hz
    rw [subspacePointSet_inf] at hz
    have h₁ := (hpre q₁ D z).1 hz.1
    have h₂ := (hpre q₂ D z).1 hz.2
    rw [hq₁] at h₁ ⊢
    rw [hq₂] at h₂ ⊢
    exact H1 _ ⟨z, rfl⟩ h₁ h₂
  obtain ⟨M₁, hM₁⟩ := exists_le_preimage_infinitesimalNeighbourhood B S hS hZ hObN q₁ Z₀ Yb
    (fun z hz => (hpre q₁ Yb z).2 (hH z hz).1)
  obtain ⟨M₂, hM₂⟩ := exists_le_preimage_infinitesimalNeighbourhood B S hS hZ hObN q₂ Z₀ Yb
    (fun z hz => (hpre q₂ Yb z).2 (hH z hz).2)
  refine ⟨max M₁ M₂, ?_⟩
  intro X' β hβ P' hP' hP'N c₁ c₂ ρ hρ₁ hρ₂ w' hw'Ob hw'
  set Yb' := infinitesimalNeighbourhood B S hS X Yb (max M₁ M₂)
  -- the inverse image of `Ō` in `P'`
  let PA : AlgebraicSpaces B S hS := ⟨P', hP'⟩
  let Pfib : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS π π
  let ρA : PA ⟶ Pfib := ObjectProperty.homMk ρ
  let Wc := preimageClosedSubspace ρA Ob
  let WS : AlgebraicSpaces B S hS := ⟨Wc.1.toFunctor, Wc.2.1⟩
  have hWN : IsNoetherian B S hS hZ WS.1 := isNoetherian_closedSubfunctor B S hS hZ PA hP'N Wc.2
  let c₁' : WS ⟶ X' := ObjectProperty.homMk (Wc.1.ι ≫ c₁)
  let c₂' : WS ⟶ X' := ObjectProperty.homMk (Wc.1.ι ≫ c₂)
  let κ : WS ⟶ ObS := ObjectProperty.homMk (Ob.1.fromPreimage ρ)
  have hκ : ∀ (c : P' ⟶ X'.1) (pr : pullback π.hom π.hom ⟶ X.1), ρ ≫ pr = c ≫ β.hom →
      ∀ U x, (Ob.1.ι ≫ pr).app U (κ.hom.app U x) = β.hom.app U ((Wc.1.ι ≫ c).app U x) := by
    intro c pr h U x
    have h' : Ob.1.fromPreimage ρ ≫ Ob.1.ι ≫ pr = (Wc.1.ι ≫ c) ≫ β.hom := by
      rw [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc, h, Category.assoc]
      rfl
    exact CategoryTheory.congr_fun (NatTrans.congr_app h' U) x
  set C := preimageClosedSubspace β D
  set L := preimageClosedSubspace β Yb'
  have hEeq : schemeTheoreticIntersection B S hS X'.1 X'.2 C L =
      preimageClosedSubspace β (schemeTheoreticIntersection B S hS X.1 X.2 D Yb') :=
    Subtype.ext rfl
  have hE :
      IsEffectiveCartierDivisor B S hS X' (schemeTheoreticIntersection B S hS X'.1 X'.2 C L) :=
    isEffectiveCartierDivisor_of_subfunctor_eq rfl hβ.isPullbackDefined
  have hk₁ : ∀ U x, q₁.hom.app U (κ.hom.app U x) = β.hom.app U (c₁'.hom.app U x) :=
    hκ c₁ _ hρ₁
  have hk₂ : ∀ U x, q₂.hom.app U (κ.hom.app U x) = β.hom.app U (c₂'.hom.app U x) :=
    hκ c₂ _ hρ₂
  have hZ₀mem : ∀ U x, x ∈ ((preimageClosedSubspace c₁' C).1 ⊓
      (preimageClosedSubspace c₂' C).1).obj U → κ.hom.app U x ∈ Z₀.1.obj U := by
    intro U x hx
    refine ⟨?_, ?_⟩
    · change q₁.hom.app U (κ.hom.app U x) ∈ D.1.obj U
      rw [hk₁]
      exact hx.1
    · change q₂.hom.app U (κ.hom.app U x) ∈ D.1.obj U
      rw [hk₂]
      exact hx.2
  have h₁ : (preimageClosedSubspace c₁' C).1 ⊓ (preimageClosedSubspace c₂' C).1 ≤
      (preimageClosedSubspace c₁' L).1 := fun U x hx => by
    change β.hom.app U (c₁'.hom.app U x) ∈ Yb'.1.obj U
    rw [← hk₁]
    exact infinitesimalNeighbourhood_antitone B S hS X Yb (le_max_left M₁ M₂) U
      (hM₁ U (hZ₀mem U x hx))
  have h₂ : (preimageClosedSubspace c₁' C).1 ⊓ (preimageClosedSubspace c₂' C).1 ≤
      (preimageClosedSubspace c₂' L).1 := fun U x hx => by
    change β.hom.app U (c₂'.hom.app U x) ∈ Yb'.1.obj U
    rw [← hk₂]
    exact infinitesimalNeighbourhood_antitone B S hS X Yb (le_max_right M₁ M₂) U
      (hM₂ U (hZ₀mem U x hx))
  -- the open set of `W` over `O`
  let e := pointsMap B S hS WS.1 Wc.1.ι
  have hemb : Topology.IsEmbedding e := isEmbedding_pointsMap_of_isImmersion B S hS hP' Wc.1.ι
    (isImmersion_of_isClosedImmersion B S hS Wc.2.2)
  have hrange : Set.range e = pointsMap B S hS P' ρ ⁻¹' subspacePointSet B S hS _ Ob.1 :=
    subspacePointSet_preimage B S hS ρ Ob.1
  have hOsub : pointsMap B S hS P' ρ ⁻¹' O ⊆ Set.range e := by
    rw [hrange, hOA]
    exact fun w hw => hw.1
  set O' := e ⁻¹' (pointsMap B S hS P' ρ ⁻¹' O) with hO'
  have hO'open : IsOpen O' := by
    have h : O' = e ⁻¹' (pointsMap B S hS P' ρ ⁻¹' A) := by
      ext w
      simp only [O', Set.mem_preimage, hOA, Set.mem_inter_iff]
      exact ⟨fun h => h.2, fun h => ⟨hrange.subset (Set.mem_range_self w), h⟩⟩
    rw [h]
    exact (hA.preimage (continuous_pointsMap B S hS ρ)).preimage hemb.continuous
  have hcE : ∀ (c : P' ⟶ X'.1) (pr : pullback π.hom π.hom ⟶ X.1), ρ ≫ pr = c ≫ β.hom →
      (∀ w ∈ O, pointsMap B S hS _ pr w ∉ subspacePointSet B S hS X.1 D.1) →
      ∀ o ∈ O', pointsMap B S hS WS.1 (Wc.1.ι ≫ c) o ∉
        subspacePointSet B S hS X'.1 (schemeTheoreticIntersection B S hS X'.1 X'.2 C L).1 := by
    intro c pr hc hpr o ho hE'
    have hC' := range_pointsMap_ι_le B S hS
      (inf_le_left : (schemeTheoreticIntersection B S hS X'.1 X'.2 C L).1 ≤ C.1) hE'
    change _ ∈ subspacePointSet B S hS X'.1 (D.1.preimage β.hom) at hC'
    rw [subspacePointSet_preimage] at hC'
    have hcomp : pointsMap B S hS _ β.hom (pointsMap B S hS WS.1 (Wc.1.ι ≫ c) o) =
        pointsMap B S hS _ pr (pointsMap B S hS P' ρ (e o)) := by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, ← pointsMap_comp_apply,
        Category.assoc, ← hc]
    exact hpr _ ho (hcomp ▸ hC')
  -- `w'` comes from `W`, in the closure of `O'`
  obtain ⟨wW, rfl⟩ : w' ∈ Set.range e := by rwa [hrange]
  have hwW : wW ∈ closure O' := by
    rwa [hemb.closure_eq_preimage_closure_image, hO', Set.image_preimage_eq_of_subset hOsub]
  have hres := mem_coincidenceLocus_or_of_mem_closure B S hS X' hZ hWN c₁' c₂' C L hE h₁ h₂
    hO'open (hcE c₁ _ hρ₁ hO₁) (hcE c₂ _ hρ₂ hO₂) hwW
  rw [hEeq] at hres
  simpa only [c₁', c₂', e, ObjectProperty.homMk_hom, pointsMap_comp_apply] using hres

end PointTopology

end AlgebraicGeometry.Space

end
