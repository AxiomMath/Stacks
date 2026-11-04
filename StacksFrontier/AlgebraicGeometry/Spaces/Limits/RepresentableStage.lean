module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PresentedNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification

/-!
# A presented system with a scheme as limit has representable stages

Let `X = lim X_i` be the limit of a presented cofiltered system of algebraic spaces, locally of
finite presentation over `S`, with affine transition morphisms, and suppose that `X` is the limit
of a cofiltered system `T_m` of separated schemes locally of finite presentation over `S`, with
the limit realised in the site. Then some stage `X_i` is representable: by Stacks 0CP4 applied
to both systems, a transition morphism `X_{i'} ⟶ X_i` factors through some `T_m`, and the
factorisation `X_{i'} ⟶ T_m` is affine because `T_m ⟶ X_i` is separated while
`X_{i'} ⟶ X_i` is affine. This replaces Stacks 07SR in the proof of Stacks 07SU.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_isSeparated_of_isAffineHom_comp`: if `g ≫ h` is
  affine and `h` is separated, then `g` is affine.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_isAffineHom`: an algebraic space affine over a
  representable presheaf is representable.
* `AlgebraicGeometry.Space.LimitPresentation.exists_iso_yoneda_stage`: the statement above.
* `AlgebraicGeometry.Space.isLimitOfInterleaved`: a cone interleaved with a limit cone is a
  limit cone.

## References

* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism whose composite with a separated morphism is affine is affine.** It factors as
its graph, a section of a base change of the separated morphism and hence a closed immersion,
followed by a base change of the composite. -/
theorem isAffineHom_of_isSeparated_of_isAffineHom_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (h : Y ⟶ Z) (hh : IsSeparated B S hS h) (hfh : IsAffineHom B S hS (f ≫ h)) :
    IsAffineHom B S hS f := by
  have hΓ : IsClosedImmersion B S hS (graph B S hS f h) :=
    isClosedImmersion_of_isSeparated_of_section B S hS (pullback.fst (f ≫ h) h)
      (isSeparated_pullbackFst B S hS (f ≫ h) hh) (graph B S hS f h) (graph_comp_fst B S hS f h)
  have h₂ : IsAffineHom B S hS (pullback.snd (f ≫ h) h) :=
    isAffineHom_of_isPullback' B S hS (IsPullback.of_hasPullback (f ≫ h) h) hfh
  rw [← graph_comp_snd B S hS f h]
  exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isClosedImmersion B S hS _ hΓ) h₂

/-- **An algebraic space affine over a representable presheaf is representable.** -/
theorem exists_iso_yoneda_of_isAffineHom {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {T : BigFppfOver B S hS} (f : X ⟶ yoneda.obj T)
    (hf : IsAffineHom B S hS f) : ∃ Y : BigFppfOver B S hS, Nonempty (yoneda.obj Y ≅ X) := by
  obtain ⟨hrep, -⟩ := presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS hX
    (isAlgebraicSpace_yoneda B S hS T) hf
  obtain ⟨Y, b, a, hpb⟩ := hrep (𝟙 (yoneda.obj T))
  have : IsIso a := hpb.isIso_fst_of_isIso
  exact ⟨Y, ⟨asIso a⟩⟩

namespace LimitPresentation

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {c : Cone D} (P : LimitPresentation B S hS D c)

include P in
/-- **A presented system of algebraic spaces whose limit is a limit of separated schemes has a
representable stage.** Let `X = lim X_i` be presented, with stages locally of finite
presentation over `S` and affine transition morphisms, and let `X ≅ lim T_m` for a cofiltered
system of quasi-compact, quasi-separated and separated schemes `T_m`, locally of finite
presentation over `S`, with affine transition morphisms and limit realised in the site. Then
some stage `X_i` is representable. -/
theorem exists_iso_yoneda_stage (hc : IsLimit c) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hDfp : ∀ i, IsLocallyOfFinitePresentation B S hS (terminal.from (D.obj i)))
    (hDaff : ∀ {i i' : I} (e : i ⟶ i'), IsAffineHom B S hS (D.map e))
    {M : Type u} [Category.{u} M] [IsCofiltered M] (T : M ⥤ BigFppfOver B S hS)
    (hTaff : ∀ {m m' : M} (e : m ⟶ m'), _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (T.map e)))
    {cT : Cone T} (hcT : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cT))
    (hTqc : ∀ m, IsQuasiCompactSpace B S hS (yoneda.obj (T.obj m)))
    (hTqs : ∀ m, IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B)
      (yoneda.obj (T.obj m)))
    (hTsep : ∀ m, Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj (T.obj m)))
    (hTfp : ∀ m, IsLocallyOfFinitePresentation B S hS (terminal.from (yoneda.obj (T.obj m))))
    (φ : yoneda.obj cT.pt ≅ c.pt) :
    ∃ (i : I) (Y : BigFppfOver B S hS), Nonempty (yoneda.obj Y ≅ D.obj i) := by
  obtain ⟨i₁⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨m, h, hh⟩ := exists_stage_hom_of_isLimit_toScheme B S hS hTaff hcT hTqc hTqs (hD i₁)
    (hDfp i₁) (φ.hom ≫ c.π.app i₁)
  obtain ⟨i₂, z, hz⟩ := P.exists_stage_hom hc hD (isAlgebraicSpace_yoneda B S hS (T.obj m))
    (hTfp m) (φ.inv ≫ yoneda.map (cT.π.app m))
  let a := IsCofiltered.minToLeft i₁ i₂
  let b := IsCofiltered.minToRight i₁ i₂
  obtain ⟨i₄, d, hd⟩ := P.exists_stage_eq hD (hD i₁) (hDfp i₁) (D.map a) (D.map b ≫ z ≫ h) (by
    rw [c.w a, ← Category.assoc, c.w b, ← Category.assoc, hz, Category.assoc, hh,
      Iso.inv_hom_id_assoc])
  have haff : IsAffineHom B S hS ((D.map d ≫ D.map b ≫ z) ≫ h) := by
    rw [Category.assoc, Category.assoc, ← hd, ← D.map_comp]
    exact hDaff _
  exact ⟨i₄, exists_iso_yoneda_of_isAffineHom (hD i₄) _
    (isAffineHom_of_isSeparated_of_isAffineHom_comp _ h
      (isSeparated_of_scheme_isSeparated B S hS (hTsep m) h) haff)⟩

end LimitPresentation

section Interleaved

variable {C : Type*} [Category* C] {E : Type*} [Category* E] (G : C ⥤ E)
  {K : Type*} [Category* K] [IsCofiltered K] {M : Type*} [Category* M]
  (Y : K ⥤ C) (T : M ⥤ C) (cY : Cone Y) (πT : (Functor.const M).obj cY.pt ⟶ T)

/-- **A cone interleaved with a limit cone is a limit cone.** Let `cT` be a cone on `T` whose
image under `G` is a limit, and `cY` a cone on a cofiltered system `Y` with the same vertex. If
every projection of `cT` factors through a projection of `cY`, every projection of `cY`
factors through a projection of `cT`, and two morphisms out of a stage of `Y` into a stage of
`Y` or of `T` which agree on the vertex agree at a later stage, then the image of `cY` under
`G` is a limit. -/
noncomputable def isLimitOfInterleaved
    (hcT : IsLimit (G.mapCone (Cone.mk cY.pt πT)))
    (h₁ : ∀ m, ∃ (k : K) (g : Y.obj k ⟶ T.obj m), cY.π.app k ≫ g = πT.app m)
    (h₂ : ∀ l, ∃ (m : M) (h : T.obj m ⟶ Y.obj l), πT.app m ≫ h = cY.π.app l)
    (h₃ : ∀ {k : K} {m : M} (u v : Y.obj k ⟶ T.obj m), cY.π.app k ≫ u = cY.π.app k ≫ v →
      ∃ (k' : K) (e : k' ⟶ k), Y.map e ≫ u = Y.map e ≫ v)
    (h₄ : ∀ {k l : K} (u v : Y.obj k ⟶ Y.obj l), cY.π.app k ≫ u = cY.π.app k ≫ v →
      ∃ (k' : K) (e : k' ⟶ k), Y.map e ≫ u = Y.map e ≫ v) :
    IsLimit (G.mapCone cY) := by
  choose k g hg using h₁
  choose m h hh using h₂
  -- two morphisms out of stages of `Y` agreeing on the vertex agree after a common refinement
  have key : ∀ {k₁ k₂ : K} {Z : C} (u₁ : Y.obj k₁ ⟶ Z) (u₂ : Y.obj k₂ ⟶ Z),
      (∀ {k : K} (a : k ⟶ k₁) (b : k ⟶ k₂), cY.π.app k ≫ Y.map a ≫ u₁ = cY.π.app k ≫ Y.map b ≫ u₂ →
        ∃ (k' : K) (e : k' ⟶ k), Y.map e ≫ Y.map a ≫ u₁ = Y.map e ≫ Y.map b ≫ u₂) →
      cY.π.app k₁ ≫ u₁ = cY.π.app k₂ ≫ u₂ →
      ∃ (k : K) (a : k ⟶ k₁) (b : k ⟶ k₂), Y.map a ≫ u₁ = Y.map b ≫ u₂ := by
    intro k₁ k₂ Z u₁ u₂ hinj huv
    obtain ⟨k', e, he⟩ := hinj (IsCofiltered.minToLeft k₁ k₂) (IsCofiltered.minToRight k₁ k₂)
      (by rw [← Category.assoc, cY.w, ← Category.assoc, cY.w, huv])
    exact ⟨k', e ≫ IsCofiltered.minToLeft k₁ k₂, e ≫ IsCofiltered.minToRight k₁ k₂,
      by simpa only [Functor.map_comp, Category.assoc] using he⟩
  let lift : ∀ s : Cone (Y ⋙ G), s.pt ⟶ G.obj cY.pt := fun s =>
    hcT.lift
      { pt := s.pt
        π :=
          { app := fun m' => s.π.app (k m') ≫ G.map (g m')
            naturality := fun m₁ m₂ f => by
              obtain ⟨k', a, b, hab⟩ := key (g m₁ ≫ T.map f) (g m₂)
                (fun a b hab => h₃ _ _ (by simpa only [Category.assoc] using hab))
                (by
                  rw [← Category.assoc, hg, hg]
                  simpa using (πT.naturality f).symm)
              have e₁ : s.π.app (k m₁) = s.π.app k' ≫ G.map (Y.map a) := (s.w a).symm
              have e₂ : s.π.app (k m₂) = s.π.app k' ≫ G.map (Y.map b) := (s.w b).symm
              calc ((Functor.const M).obj s.pt).map f ≫ s.π.app (k m₂) ≫ G.map (g m₂)
                  = s.π.app k' ≫ G.map (Y.map b ≫ g m₂) := by
                    rw [e₂, Functor.const_obj_map, G.map_comp]
                    simp only [Category.assoc]
                    exact Category.id_comp _
                _ = s.π.app k' ≫ G.map (Y.map a ≫ g m₁ ≫ T.map f) := by rw [hab]
                _ = (s.π.app (k m₁) ≫ G.map (g m₁)) ≫ (T ⋙ G).map f := by
                    rw [e₁, G.map_comp, G.map_comp, Functor.comp_map]
                    simp only [Category.assoc] } }
  have hlift : ∀ (s : Cone (Y ⋙ G)) (m' : M),
      lift s ≫ G.map (πT.app m') = s.π.app (k m') ≫ G.map (g m') := fun s m' => hcT.fac _ m'
  refine
    { lift := lift
      fac := fun s l => ?_
      uniq := fun s f hf => ?_ }
  · change lift s ≫ G.map (cY.π.app l) = s.π.app l
    obtain ⟨k', a, b, hab⟩ := key (g (m l) ≫ h l) (𝟙 _)
      (fun a b hab => h₄ _ _ (by simpa only [Category.assoc] using hab))
      (by rw [Category.comp_id, ← Category.assoc, hg, hh])
    have e₁ : s.π.app (k (m l)) = s.π.app k' ≫ G.map (Y.map a) := (s.w a).symm
    rw [← hh, G.map_comp, ← Category.assoc, hlift, Category.assoc, ← G.map_comp, e₁,
      Category.assoc, ← G.map_comp, hab, Category.comp_id]
    exact s.w b
  · refine hcT.hom_ext fun m' => ?_
    change f ≫ G.map (πT.app m') = lift s ≫ G.map (πT.app m')
    rw [hlift, ← hg, G.map_comp, ← Category.assoc]
    exact congrArg (· ≫ G.map (g m')) (hf (k m'))

end Interleaved

end AlgebraicGeometry.Space

end
