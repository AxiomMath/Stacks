module

public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.SchemeNormalizedBlowupBridge

/-!
# One step of the transfer of normalized blowups from étale neighbourhoods

Let `f : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `a : P ⟶ X` be étale and
let `g : Z' ⟶ Z` be the normalization of the blowing up of `Z` at a closed point `z`. This file
computes the base change of `g ≫ f` along `a` in the two cases occurring in the proof of
Stacks 0BHL:

* if no point of `Z ×_X P` lies over `z` and `Z ×_X P` is normal, the base change of `g ≫ f` is
  that of `f`;
* if `Z ×_X P` is represented by a locally Noetherian scheme `W` and exactly one point of it, a
  closed point `w`, lies over `z`, the base change of `g ≫ f` is represented by the normalized
  blowup of `W` at `w`.

## Main results

* `AlgebraicGeometry.Space.exists_iso_pullback_comp_of_isNormalizationOfBlowupAtClosedPoint`: the
  first case.
* `AlgebraicGeometry.Space.exists_iso_pullback_comp_normalizedBlowUpScheme`: the second case.

## References

* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **Away from the centre a normalized blowing up does not change the base change.** If no
point of `Z ×_X P` lies over the centre `z` of the normalized blowing up `g : Z' ⟶ Z` and
`Z ×_X P` is normal, then `Z' ×_X P = Z ×_X P` over `P`. -/
theorem exists_iso_pullback_comp_of_isNormalizationOfBlowupAtClosedPoint
    {X Z Z' : AlgebraicSpaces B S hS} (f : Z ⟶ X) {z : points B S hS Z.obj}
    {hz : IsClosed ({z} : Set (points B S hS Z.obj))} {g : Z' ⟶ Z}
    (hg : IsNormalizationOfBlowupAtClosedPoint B S hS z hz g)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P) (a : P ⟶ X.obj)
    (ha : IsEtale B S hS a) (hnormal : Space.IsNormal B S hS (pullback f.hom a))
    (hfib : ∀ t, pointsMap B S hS _ (pullback.fst f.hom a) t ≠ z) :
    ∃ e : pullback (g.hom ≫ f.hom) a ≅ pullback f.hom a,
      e.hom ≫ pullback.snd f.hom a = pullback.snd (g.hom ≫ f.hom) a := by
  let T : AlgebraicSpaces B S hS :=
    ⟨pullback f.hom a, isAlgebraicSpace_pullback B S hS f.hom a Z.property hP X.property⟩
  let φ : T ⟶ Z := ObjectProperty.homMk (pullback.fst f.hom a)
  have hφ : IsEtale B S hS φ.hom := isEtale_pullback_fst B S hS Z.property X.property hP _ _ ha
  have hiso : IsIso (pullback.fst φ.hom g.hom) :=
    isIso_fiberProduct_of_isNormalizationOfBlowupAtClosedPoint hφ hnormal
      (Set.eq_empty_of_forall_notMem hfib) hg
  refine ⟨(pullbackRightPullbackFstIso f.hom a g.hom).symm ≪≫
    pullbackSymmetry _ _ ≪≫ asIso (pullback.fst φ.hom g.hom), ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  show _ ≫ _ ≫ pullback.fst (pullback.fst f.hom a) g.hom ≫ pullback.snd f.hom a = _
  rw [pullbackSymmetry_hom_comp_fst_assoc, pullbackRightPullbackFstIso_inv_snd_snd]

/-- **At the centre a normalized blowing up base changes to the normalized blowup of the scheme
representing the base change.** If `Z ×_X V ≅ h_W` over `V` for a locally Noetherian scheme `W`,
and the closed point `w` of `W` is the only point over the centre `z` of the normalized blowing
up `g : Z' ⟶ Z`, then `Z' ×_X V` is represented by the normalized blowup of `W` at `w`, over
`V`. -/
theorem exists_iso_pullback_comp_normalizedBlowUpScheme
    {X Z Z' : AlgebraicSpaces B S hS} (f : Z ⟶ X) {z : points B S hS Z.obj}
    {hz : IsClosed ({z} : Set (points B S hS Z.obj))} {g : Z' ⟶ Z}
    (hg : IsNormalizationOfBlowupAtClosedPoint B S hS z hz g)
    {V W : BigFppfOver B S hS} (a : yoneda.obj V ⟶ X.obj) (ha : IsEtale B S hS a)
    (q : W ⟶ V) (φ : pullback f.hom a ≅ yoneda.obj W)
    (hφ : φ.hom ≫ yoneda.map q = pullback.snd f.hom a)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W)]
    (hW : ∀ U : ((BigFppfOver.toScheme B S hS).obj W).Opens,
      IsCompact (U : Set ((BigFppfOver.toScheme B S hS).obj W)) →
        (irreducibleComponents U).Finite)
    {w : (BigFppfOver.toScheme B S hS).obj W} (hw : IsClosed ({w} : Set _))
    (hfib : pointsMap B S hS _ (φ.inv ≫ pullback.fst f.hom a) ⁻¹' {z} =
      {schemeSpacePoint W w}) :
    ∃ (N : BigFppfOver B S hS) (q' : N ⟶ W) (e : pullback (g.hom ≫ f.hom) a ≅ yoneda.obj N)
      (ψ : (BigFppfOver.toScheme B S hS).obj N ≅
        Stacks.Blowup.normalizedBlowUpScheme _ hW w hw),
      e.hom ≫ yoneda.map (q' ≫ q) = pullback.snd (g.hom ≫ f.hom) a ∧
        (BigFppfOver.toScheme B S hS).map q' =
          ψ.hom ≫ Stacks.Blowup.normalizedBlowUp _ hW w hw := by
  let φ' : schemeSpace W ⟶ Z := ObjectProperty.homMk (φ.inv ≫ pullback.fst f.hom a)
  have hfst : IsEtale B S hS (pullback.fst f.hom a) :=
    isEtale_pullback_fst B S hS Z.property X.property (isAlgebraicSpace_yoneda B S hS V) _ _ ha
  have hφ' : IsEtale B S hS φ'.hom :=
    isEtale_comp B S hS (isEtale_of_iso B S hS φ.symm) hfst
  have hNBU := isNormalizationOfBlowupAtClosedPoint_fiberProduct_of_isEtale hφ'
    (isClosed_singleton_schemeSpacePoint W hw) hfib hg
  obtain ⟨N, q', e₀, ψ, he₀, hq'⟩ :=
    exists_iso_schemeSpace_normalizedBlowUpScheme W hW hw hNBU
  -- the square exhibiting `Z' ×_X V` as `Z' ×_Z h_W`
  let l : pullback (g.hom ≫ f.hom) a ⟶ pullback f.hom a :=
    pullback.lift (pullback.fst _ _ ≫ g.hom) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition])
  have hsq₁ : IsPullback (pullback.fst (g.hom ≫ f.hom) a) l g.hom (pullback.fst f.hom a) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f.hom a)
    rw [show l ≫ pullback.snd f.hom a = pullback.snd (g.hom ≫ f.hom) a from
      pullback.lift_snd _ _ _]
    exact IsPullback.of_hasPullback (g.hom ≫ f.hom) a
  have hsq₂ : IsPullback (pullback.fst (g.hom ≫ f.hom) a) (l ≫ φ.hom) g.hom φ'.hom := by
    refine IsPullback.of_iso hsq₁ (Iso.refl _) (Iso.refl _) φ (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · show pullback.fst f.hom a ≫ 𝟙 _ = φ.hom ≫ φ.inv ≫ pullback.fst f.hom a
      simp
  let ε := (IsPullback.of_hasPullback φ'.hom g.hom).isoIsPullback _ _ hsq₂.flip
  let e₀' : pullback φ'.hom g.hom ≅ yoneda.obj N := (ObjectProperty.ι _).mapIso e₀
  refine ⟨N, q', ε.symm ≪≫ e₀', ψ, ?_, hq'⟩
  have h2 : e₀'.hom ≫ yoneda.map q' = pullback.fst φ'.hom g.hom :=
    congrArg (fun k => k.hom) he₀
  have h3 : ε.inv ≫ pullback.fst φ'.hom g.hom = l ≫ φ.hom :=
    IsPullback.isoIsPullback_inv_fst _ _ _ _
  rw [Iso.trans_hom, Functor.map_comp, Iso.symm_hom, Category.assoc, ← Category.assoc e₀'.hom,
    h2]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ yoneda.map q) h3).trans
    ((Category.assoc _ _ _).trans ((congrArg (l ≫ ·) hφ).trans (pullback.lift_snd _ _ _))))

end AlgebraicGeometry.Space
