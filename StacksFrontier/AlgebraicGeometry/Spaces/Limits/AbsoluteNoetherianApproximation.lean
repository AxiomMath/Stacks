module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationProblemStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeApproximationOfPresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Absolute Noetherian approximation, with limit presentations

Every quasi-compact and quasi-separated algebraic space `X` over `Spec ℤ` is the limit of a
directed inverse system of quasi-separated algebraic spaces of finite type over `Spec ℤ` with
affine transition morphisms (Stacks 07SU). This file proves the stronger form in which the
approximation carries a limit presentation
(`AlgebraicGeometry.Space.PresentedNoetherianApproximation`): compatible étale atlases of the
stages and of `X`, with their kernel pairs, whose limits are those of the system.

The proof runs down the filtration `X = U_0 ⊇ U_1 ⊇ ⋯ ⊇ U_n = ∅` of Stacks 07ST:
the empty space is its own approximation, and the problem step
(`AlgebraicGeometry.Space.nonempty_presentedNoetherianApproximation_of_isOpenSubspace`) passes
from `U_{p+1}` to `U_p` along the étale neighbourhood of the stratum `U_p \ U_{p+1}` which
Stacks 07ST provides. The approximations carry limit presentations
(`AlgebraicGeometry.Space.PresentedNoetherianApproximation`), which is what the problem step
consumes and what makes Stacks 0CP4 available
(`AlgebraicGeometry.Space.hasRelativeApproximation_of_presented`).

## Main definitions

* `AlgebraicGeometry.Space.PresentedNoetherianApproximation.ofIso`: transport along an
  isomorphism.
* `AlgebraicGeometry.Space.PresentedNoetherianApproximation.ofAtlas`: the constant approximation
  of an algebraic space with a quasi-compact quasi-separated atlas of finite type over `Spec ℤ`.

## Main results

* `AlgebraicGeometry.Space.nonempty_presentedNoetherianApproximation`: every quasi-compact
  quasi-separated algebraic space over `Spec ℤ` has a presented Noetherian approximation.

## Implementation notes

Stacks 07SU itself, without the presentation, is
`AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace`, proved in
`StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Main` by the induction of
the source carried with the standing convention of Section 70.2 on the inverse system. The
presented form here is what Stacks 0CP4
(`AlgebraicGeometry.Space.hasRelativeApproximation_of_presented`) consumes.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

local notation "𝕋" => BigFppfOver.toScheme B (⊤_ Scheme) hZ

/-- A cone over a functor out of the opposite of the one-point category whose projection is an
isomorphism is a limit cone. -/
noncomputable def isLimitOfPUnitOp {C : Type*} [Category* C] {G : PUnit.{u + 1}ᵒᵖ ⥤ C}
    (c : Cone G) [IsIso (c.π.app (Opposite.op PUnit.unit))] : IsLimit c where
  lift s := s.π.app (Opposite.op PUnit.unit) ≫ inv (c.π.app (Opposite.op PUnit.unit))
  fac s j := by
    obtain ⟨⟨⟩⟩ := j
    simp
  uniq s m h := by
    rw [IsIso.eq_comp_inv, h]

namespace PresentedNoetherianApproximation

attribute [local instance] NoetherianApproximation.preorder NoetherianApproximation.nonempty
  NoetherianApproximation.isDirected

/-- A presented Noetherian approximation transported along an isomorphism. -/
noncomputable def ofIso {X X' : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (A : PresentedNoetherianApproximation B hZ X) (e : X ≅ X') :
    PresentedNoetherianApproximation B hZ X' :=
  { A.toNoetherianApproximation with
    π := (Functor.const _).map e.inv ≫ A.π
    isLimit := A.isLimit.ofIsoLimit (Cone.ext e (fun j => by simp))
    presentation :=
      { A.presentation with
        limitAtlas := A.presentation.limitAtlas ≫ e.hom
        isPullback_limitAtlas := fun j => (A.presentation.isPullback_limitAtlas j).of_iso
          (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) (by simp) } }

/-- **The constant approximation.** An algebraic space over `Spec ℤ` with a surjective étale
atlas by a quasi-compact quasi-separated scheme locally of finite type over `Spec ℤ`, whose kernel
pair is quasi-compact and quasi-separated, is the limit of the constant system on itself. -/
noncomputable def ofAtlas {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B _ hZ F) {V R : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (q : yoneda.obj V ⟶ F)
    (hq_surj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hZ)).presheaf q)
    (hq_et : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hZ)).presheaf q)
    {s t : R ⟶ V} (hker : IsPullback (yoneda.map s) (yoneda.map t) q q)
    [CompactSpace ((𝕋).obj V)] [QuasiSeparatedSpace ((𝕋).obj V)] [CompactSpace ((𝕋).obj R)]
    [QuasiSeparatedSpace ((𝕋).obj R)] (hV : LocallyOfFiniteType (terminal.from ((𝕋).obj V))) :
    PresentedNoetherianApproximation B hZ F where
  I := PUnit.{u + 1}
  diagram := (Functor.const _).obj F
  isAlgebraicSpace _ := hF
  isAffineHom_map _ := isAffineHom_of_isIso (𝟙 F)
  isAbsolutelyQuasiSeparated _ :=
    isAbsolutelyQuasiSeparated_of_atlas hF q hq_surj hq_et hker inferInstance
  isFiniteTypeOverIntegers _ := isFiniteType_viewOverIntegers_of_atlas hF q hq_surj hq_et hV
  π := 𝟙 _
  isLimit := isLimitOfPUnitOp (G := (Functor.const _).obj F) (Cone.mk F (𝟙 _))
  presentation :=
    { atlas := (Functor.const _).obj V
      relation := (Functor.const _).obj R
      atlasMap :=
        { app := fun _ => q
          naturality := fun _ _ _ => by simp }
      src :=
        { app := fun _ => s
          naturality := fun _ _ _ => by simp }
      tgt :=
        { app := fun _ => t
          naturality := fun _ _ _ => by simp }
      surjective_atlasMap := fun _ => hq_surj
      etale_atlasMap := fun _ => hq_et
      isPullback_relation := fun _ => hker
      isPullback_atlas := fun _ => by
        change IsPullback (yoneda.map (𝟙 V)) q q (𝟙 F)
        rw [CategoryTheory.Functor.map_id]
        exact IsPullback.of_id_fst
      isAffineHom_atlas := fun _ => by
        change _root_.AlgebraicGeometry.IsAffineHom ((𝕋).map (𝟙 V))
        rw [CategoryTheory.Functor.map_id]
        infer_instance
      isAffineHom_relation := fun _ => by
        change _root_.AlgebraicGeometry.IsAffineHom ((𝕋).map (𝟙 R))
        rw [CategoryTheory.Functor.map_id]
        infer_instance
      isQuasiCompactSpace_atlas := fun _ => isQuasiCompactSpace_yoneda_obj B _ hZ
        (inferInstanceAs (CompactSpace ((𝕋).obj V)))
      quasiSeparatedSpace_atlas := fun _ => inferInstanceAs (QuasiSeparatedSpace ((𝕋).obj V))
      isQuasiCompactSpace_relation := fun _ => isQuasiCompactSpace_yoneda_obj B _ hZ
        (inferInstanceAs (CompactSpace ((𝕋).obj R)))
      quasiSeparatedSpace_relation := fun _ => inferInstanceAs (QuasiSeparatedSpace ((𝕋).obj R))
      atlasCone := Cone.mk V (𝟙 _)
      isLimit_atlasCone := by
        have : IsIso ((𝕋).map (𝟙 V)) := inferInstance
        exact @isLimitOfPUnitOp _ _ _ _ this
      relationCone := Cone.mk R (𝟙 _)
      isLimit_relationCone := by
        have : IsIso ((𝕋).map (𝟙 R)) := inferInstance
        exact @isLimitOfPUnitOp _ _ _ _ this
      srcLim := s
      tgtLim := t
      srcLim_π := fun _ => by simp
      tgtLim_π := fun _ => by simp
      limitAtlas := q
      isPullback_limitAtlas := fun _ => by
        change IsPullback (yoneda.map (𝟙 V)) q q (𝟙 F)
        rw [CategoryTheory.Functor.map_id]
        exact IsPullback.of_id_fst }

end PresentedNoetherianApproximation

open PresentedNoetherianApproximation in
/-- **An empty algebraic space has a presented Noetherian approximation**: a surjective étale
atlas of an algebraic space without points is an empty scheme, and so is its kernel pair. -/
theorem nonempty_presentedNoetherianApproximation_of_isEmpty
    {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B _ hZ F)
    (hE : IsEmpty (points B _ hZ F)) : Nonempty (PresentedNoetherianApproximation B hZ F) := by
  obtain ⟨V, q, hq_surj, hq_et⟩ := hF.exists_atlas
  have : IsEmpty ((𝕋).obj V) :=
    ⟨fun v => hE.false (pointsMap B _ hZ _ q ((pointsEquivScheme B _ hZ V).symm v))⟩
  let r : yoneda.relativelyRepresentable q := hF.diagonal_representable.of_diag q
  have : IsEmpty ((𝕋).obj (r.pullback q)) :=
    ⟨fun x => isEmptyElim (((𝕋).map (r.fst' q)).base x)⟩
  exact ⟨ofAtlas hF q hq_surj hq_et (r.isPullback' q) inferInstance⟩

/-- **Absolute Noetherian approximation, with limit presentations** (Stacks 07SU). A
quasi-compact and quasi-separated algebraic space over `Spec ℤ` has a presented Noetherian
approximation. The proof runs down the filtration of Stacks 07ST, starting from the empty open
subspace, by the problem step
`AlgebraicGeometry.Space.nonempty_presentedNoetherianApproximation_of_isOpenSubspace`. -/
theorem nonempty_presentedNoetherianApproximation
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B _ hZ X)
    (hqc : IsQuasiCompactSpace B _ hZ X) (hqs : IsAbsolutelyQuasiSeparated B _ hZ hZ X) :
    Nonempty (PresentedNoetherianApproximation B hZ X) := by
  obtain ⟨n, U, -, hU0, hUn, hUopen, hUmono, T, V, f, hdata⟩ :=
    exists_finiteFiltration_of_isQuasiCompactSpace B _ hZ hZ X hX hqc hqs
  have step : ∀ p (hp : p < n), Nonempty (PresentedNoetherianApproximation B hZ
      (U (p + 1)).toFunctor) →
        Nonempty (PresentedNoetherianApproximation B hZ (U p).toFunctor) := by
    rintro p hp ⟨A⟩
    let k : Fin n := ⟨p, hp⟩
    obtain ⟨-, hTpts, -, hVc, hVsep, hfs, hfe, hfiso⟩ := hdata k
    have hUp := hUopen p hp.le
    have hle := hUmono p hp
    let Uo := (U (p + 1)).preimage (U p).ι
    have hUo : IsOpenSubspace B _ hZ Uo := isOpenSubspace_preimage_of_le B _ hZ hle (hUopen _ hp)
    have hUpqs : IsAbsolutelyQuasiSeparated B _ hZ hZ (U p).toFunctor :=
      isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ hUp.1 hqs
        (isQuasiSeparated_of_mono B _ hZ (U p).ι inferInstance)
    have : CompactSpace ((𝕋).obj (V k)) := hVc
    have : Scheme.IsSeparated ((𝕋).obj (V k)) := hVsep
    let e := preimageIso_of_le hle
    have he : e.hom ≫ (U (p + 1)).ι = Uo.ι ≫ (U p).ι := Subfunctor.fromPreimage_ι _ _
    refine nonempty_presentedNoetherianApproximation_of_isOpenSubspace hUp.1 hUpqs hUo
      (A.ofIso e.symm) (f k) hfs hfe (T k) (fun x hx => ?_) hfiso
    have hinj := pointsMap_injective_of_mono B _ hZ (U p).ι
    by_cases hy : pointsMap B _ hZ _ (U p).ι x ∈
        Set.range (pointsMap B _ hZ (U (p + 1)).toFunctor (U (p + 1)).ι)
    · obtain ⟨z, hz⟩ := hy
      refine absurd ⟨pointsMap B _ hZ _ e.inv z, hinj ?_⟩ hx
      show (pointsMap B _ hZ _ (U p).ι ∘ pointsMap B _ hZ _ Uo.ι ∘ pointsMap B _ hZ _ e.inv) z = _
      rw [← pointsMap_comp, ← pointsMap_comp, Category.assoc, ← he, ← Category.assoc,
        Iso.inv_hom_id, Category.id_comp, hz]
    · have hmem : pointsMap B _ hZ _ (U p).ι x ∈
          Set.range (pointsMap B _ hZ (T k).toFunctor ((T k).ι ≫ (U k.val).ι)) := by
        rw [hTpts]
        exact ⟨⟨x, rfl⟩, hy⟩
      obtain ⟨t, ht⟩ := hmem
      refine ⟨t, hinj ?_⟩
      show (pointsMap B _ hZ _ (U p).ι ∘ pointsMap B _ hZ _ (T k).ι) t = _
      rw [← pointsMap_comp]
      exact ht
  have key : ∀ m, m ≤ n →
      Nonempty (PresentedNoetherianApproximation B hZ (U (n - m)).toFunctor) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero]
      have hE : IsEmpty (points B _ hZ (U n).toFunctor) := by
        rw [hUn]
        exact isEmpty_points_sheafify_bot B _ hZ X
      exact nonempty_presentedNoetherianApproximation_of_isEmpty (hUopen n le_rfl).1 hE
    | succ m ih =>
      intro hm
      have h := ih (by omega)
      have hpm : n - m = n - (m + 1) + 1 := by omega
      rw [hpm] at h
      exact step _ (by omega) h
  obtain ⟨A⟩ := key n le_rfl
  rw [Nat.sub_self, hU0] at A
  exact ⟨A.ofIso (asIso (⊤ : Subfunctor X).ι)⟩

end AlgebraicGeometry.Space

end
