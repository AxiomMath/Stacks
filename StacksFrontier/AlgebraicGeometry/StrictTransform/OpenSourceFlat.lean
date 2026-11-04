module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Flat
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocusPullback
public import StacksFrontier.AlgebraicGeometry.StrictTransform.OpenRestriction

/-!
# The strict transform of a module that is finite locally free near a point

Let `f : X ⟶ S` be a flat morphism, `ℐ` a quasi-coherent sheaf of ideals on `S` and `F` a
quasi-coherent `𝒪_X`-module. If `F` is finite locally free of rank `r` on a neighbourhood of the
image of a point `z` of `X ×_S Bl_ℐ(S)` under the first projection, then the strict transform of
`F` is finite locally free of rank `r` on a neighbourhood of `z`.

This is [Stacks, Tag 080F] part (2) made local on the source. On the open `W` where `F` is finite
locally free it is flat over `S` — the morphism being flat — so over `W` the quotient map defining
the strict transform is invertible and the strict transform is the pullback of `F`, which is again
finite locally free of rank `r`.

## Main results

* `AlgebraicGeometry.freeAtPointOfRank_strictTransformSheaf`: the statement above.

## Implementation notes

The strict transform is made local on the source by `Stacks.StrictTransform.sheafRestrictIso`
applied to the open immersion `X_W ×_S Bl_ℐ(S) ⟶ X ×_S Bl_ℐ(S)`, which is
`CategoryTheory.Limits.pullback.map` of `W ⟶ X` and the identity of the blowup. That the point `z`
is in the image of that open immersion is not read off a description of its range: the inverse
image of `W` in the ambient base change maps into the smaller base change by the universal
property, and that map composed with the open immersion is the inclusion of the inverse image, so
`z` is hit by construction.

Flatness of the restricted module over the base comes from
`AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree`, whose only
hypothesis on the morphism is flatness.

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The strict transform of a module finite locally free of rank `r` near a point is finite
locally free of rank `r` near every point above it.** Let `f : X ⟶ S` be flat, `ℐ` a centre and
`F` a quasi-coherent `𝒪_X`-module. If `F` is finite locally free of rank `r` on a neighbourhood of
the image of `z : X ×_S Bl_ℐ(S)` in `X`, then the strict transform of `F` along the blowup is
finite locally free of rank `r` on a neighbourhood of `z`. -/
theorem freeAtPointOfRank_strictTransformSheaf {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (I : S.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    (z : Stacks.StrictTransform.baseChange f (blowUpToBase I)) (r : ℕ)
    (hz : FreeAtPointOfRank F ((pullback.fst f (blowUpToBase I)).base z) r) :
    FreeAtPointOfRank
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) z r := by
  classical
  obtain ⟨W, hzW, hdata⟩ := hz
  -- The family and the module restricted to `W`.
  set g : W.toScheme ⟶ S := W.ι ≫ f with hg
  set G : W.toScheme.Modules := (Scheme.Modules.pullback W.ι).obj F with hG
  have hrk : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G r :=
    { exists_isFiniteLocallyFreeOfRankData := hdata.exists_isFiniteLocallyFreeOfRankData }
  have hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} G :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree G r
  -- Being finite locally free on a flat family, `G` is flat over `S` at every point.
  have hGflat : ∀ x : W.toScheme, g.base x ∈ I.support →
      IsFlatOverAt g.toLRSHom.toShHom G x := fun x _ ↦
    VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree g G x
  -- Hence, by tag 080F (2), the strict transform of `G` is the pullback of `G`.
  have hπ := isIso_strictTransformSheaf_quotient_of_flat_at_exceptional g I G hGflat
  set eπ := asIso (Stacks.StrictTransform.π g (blowUpToBase I) (exceptionalIdeal I) G) with heπ
  -- The open immersion of ambient base changes.
  have h₁ : g ≫ 𝟙 S = W.ι ≫ f := by rw [Category.comp_id, hg]
  have h₂ : blowUpToBase I ≫ 𝟙 S = 𝟙 (blowUp I) ≫ blowUpToBase I := by
    rw [Category.comp_id, Category.id_comp]
  set j := pullback.map g (blowUpToBase I) f (blowUpToBase I) W.ι (𝟙 (blowUp I)) (𝟙 S) h₁ h₂
    with hj
  have hjoi : IsOpenImmersion j :=
    Scheme.pullback_map_isOpenImmersion g (blowUpToBase I) f (blowUpToBase I) W.ι
      (𝟙 (blowUp I)) (𝟙 S) h₁ h₂
  have hfst : j ≫ pullback.fst f (blowUpToBase I) = pullback.fst g (blowUpToBase I) ≫ W.ι := by
    rw [hj, pullback.lift_fst]
  have hsnd : j ≫ pullback.snd f (blowUpToBase I) = pullback.snd g (blowUpToBase I) := by
    rw [hj, pullback.lift_snd, Category.comp_id]
  have hZ : Stacks.StrictTransform.exceptionalPreimage g (blowUpToBase I) (exceptionalIdeal I) =
      j.base ⁻¹' Stacks.StrictTransform.exceptionalPreimage f (blowUpToBase I)
        (exceptionalIdeal I) := by
    show (pullback.snd g (blowUpToBase I)).base ⁻¹' _ = j.base ⁻¹' ((pullback.snd f
      (blowUpToBase I)).base ⁻¹' _)
    rw [← Set.preimage_comp, ← hsnd]
    rfl
  -- The comparison of the two pulled-back modules.
  set eF : (Scheme.Modules.pullback (pullback.fst g (blowUpToBase I))).obj G ≅
      (Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F) :=
    (Scheme.Modules.pullbackComp (pullback.fst g (blowUpToBase I)) W.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr hfst.symm).app F ≪≫
      ((Scheme.Modules.pullbackComp j (pullback.fst f (blowUpToBase I))).app F).symm with heF
  have eSh := Stacks.StrictTransform.sheafRestrictIso f (blowUpToBase I) (exceptionalIdeal I)
    g (blowUpToBase I) (exceptionalIdeal I) j hZ F G eF
  -- So the strict transform of `F`, pulled back along `j`, is the pullback of `F`.
  have hiso : (Scheme.Modules.pullback j).obj
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) ≅
      (Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F) :=
    eSh.symm ≪≫ eπ.symm ≪≫ eF
  -- `z` lies in the image of `j`.
  set V₀ : (Stacks.StrictTransform.baseChange f (blowUpToBase I)).Opens :=
    pullback.fst f (blowUpToBase I) ⁻¹ᵁ W with hV₀
  have hzV₀ : z ∈ V₀ := hzW
  have hrange : Set.range (V₀.ι ≫ pullback.fst f (blowUpToBase I)).base ⊆
      Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    exact v.2
  set m : V₀.toScheme ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι (V₀.ι ≫ pullback.fst f (blowUpToBase I)) hrange with hm
  have hmfac : m ≫ W.ι = V₀.ι ≫ pullback.fst f (blowUpToBase I) :=
    IsOpenImmersion.lift_fac _ _ hrange
  have hlift : m ≫ g = (V₀.ι ≫ pullback.snd f (blowUpToBase I)) ≫ blowUpToBase I := by
    rw [hg, ← Category.assoc, hmfac, Category.assoc, Category.assoc, pullback.condition]
  set k : V₀.toScheme ⟶ Stacks.StrictTransform.baseChange g (blowUpToBase I) :=
    pullback.lift m (V₀.ι ≫ pullback.snd f (blowUpToBase I)) hlift with hk
  have hkj : k ≫ j = V₀.ι := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, ← Category.assoc, hk, pullback.lift_fst, hmfac]
    · rw [Category.assoc, hsnd, hk, pullback.lift_snd]
  have hjz : j.base (k.base ⟨z, hzV₀⟩) = z := by
    show j.base (k.base ⟨z, hzV₀⟩) = V₀.ι.base ⟨z, hzV₀⟩
    rw [← hkj]
    rfl
  -- Transport freeness along the identification.
  have hpb : FreeAtPointOfRank ((Scheme.Modules.pullback j).obj
      ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F))
      (k.base ⟨z, hzV₀⟩) r := by
    refine freeAtPointOfRank_pullback j
      ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F) _ r ?_
    rw [hjz]
    exact freeAtPointOfRank_pullback (pullback.fst f (blowUpToBase I)) F z r ⟨W, hzW, hdata⟩
  have hres := freeAtPointOfRank_of_isOpenImmersion j
    (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)
    (k.base ⟨z, hzV₀⟩) r (freeAtPointOfRank_of_moduleIso hiso.symm hpb)
  rwa [hjz] at hres

end AlgebraicGeometry

end
