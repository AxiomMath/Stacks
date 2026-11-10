module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.AdicLisse
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.StratificationNoetherian

/-!
# Restriction of constructible and lisse `Λ`-sheaves to open subschemes

Let `f : Y ⟶ X` be an open immersion. Inverse image along `f` of sheaves of `Λ`-modules on the
small pro-étale sites is restriction along `f`, so it preserves limits, quotients by an ideal,
constructibility and local constancy; hence it carries constructible and lisse `Λ`-sheaves to
constructible and lisse `Λ`-sheaves.

## Main results

* `AlgebraicGeometry.ProEtale.isConstructibleModuleSheaf'_proetaleModuleInverseImage`:
  constructibility is preserved by restriction to an open subscheme.
* `AlgebraicGeometry.ProEtale.isLocallyConstant_proetaleModuleInverseImage`: local constancy is
  preserved by every inverse image.
* `AlgebraicGeometry.ProEtale.IsLisseAdicModuleSheaf.proetaleModuleInverseImage`: a lisse
  constructible `Λ`-sheaf restricts to a lisse constructible `Λ`-sheaf on an open subscheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ModuleSheaf Stacks.ConstantSheaf

universe w v u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] proetalePostcompose_isContinuous hasWeakSheafify_proEt_moduleCat
  hasWeakSheafify_proEt_over_moduleCat

variable {Λ : Type v} [CommRing Λ]

/-- **Constructibility is preserved by restriction to an open subscheme.** An affine open `V` of
`Y` is carried to an affine open `f(V)` of `X`; the strata of a stratification of `f(V)` lie in
the image of `f`, so they lift along `f` to a stratification of `V`, and the inverse image to each
stratum is unchanged. -/
theorem isConstructibleModuleSheaf'_proetaleModuleInverseImage [IsNoetherianRing Λ]
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : IsConstructibleModuleSheaf'.{u, v, w} X Λ F) :
    IsConstructibleModuleSheaf'.{u, v, w} Y Λ
      ((proetaleModuleInverseImage.{u, v, w} f Λ).obj F) := by
  intro V
  let W : X.affineOpens := ⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩
  obtain ⟨s, hs⟩ := hF W
  have hWrange : (W.1 : Set X) ⊆ Set.range f.base := Set.image_subset_range _ _
  have hsub (i : Fin s.n) : Set.range (s.inclusion i).base ⊆ Set.range f.base :=
    (s.contained i).trans hWrange
  let m (i : Fin s.n) : s.piece i ⟶ Y :=
    IsOpenImmersion.lift f (s.inclusion i) (hsub i)
  have hm (i : Fin s.n) : m i ≫ f = s.inclusion i :=
    IsOpenImmersion.lift_fac f (s.inclusion i) (hsub i)
  have hiff (i : Fin s.n) (z : s.piece i) (y : Y) :
      (m i).base z = y ↔ (s.inclusion i).base z = f y := by
    rw [← hm i, Scheme.Hom.comp_apply]
    exact f.isOpenEmbedding.injective.eq_iff.symm
  have hcontained (i : Fin s.n) : Set.range (m i).base ⊆ (V.1 : Set Y) := by
    rintro y ⟨z, rfl⟩
    obtain ⟨y, hy, heq⟩ := s.contained i ⟨z, rfl⟩
    exact ((hiff i z y).mpr heq.symm) ▸ hy
  let s' : Scheme.ConstructibleStratification Y V.1 := {
    n := s.n
    piece := s.piece
    inclusion := m
    isImmersion i := (IsImmersion.comp_iff (m i) f).mp <| by
      rw [hm i]
      exact s.isImmersion i
    contained := hcontained
    constructible := by
      intro i
      let e : V.1 ≃ₜ f.base '' (V.1 : Set Y) :=
        f.isOpenEmbedding.isEmbedding.homeomorphImage (V.1 : Set Y)
      have heq : (V.1.ι.base ⁻¹' Set.range (m i).base) =
          e ⁻¹' (W.1.ι.base ⁻¹' Set.range (s.inclusion i).base) := by
        ext y
        change (V.1.ι.base y ∈ Set.range (m i).base) ↔
          W.1.ι.base (e y) ∈ Set.range (s.inclusion i).base
        exact ⟨fun ⟨z, hz⟩ => ⟨z, (hiff i z _).mp hz⟩, fun ⟨z, hz⟩ => ⟨z, (hiff i z _).mpr hz⟩⟩
      rw [heq]
      exact (s.constructible i).preimage_of_isOpenEmbedding e.isOpenEmbedding
    pairwise_disjoint := by
      intro i j hij
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨x, rfl⟩ ⟨x', hx'⟩
      exact Set.disjoint_left.mp (s.pairwise_disjoint i j hij)
        (show f ((m i).base x) ∈ _ from ⟨x, (hiff i x _).mp rfl⟩)
        ⟨x', (hiff j x' _).mp hx'⟩
    covers := by
      apply Set.Subset.antisymm
      · intro y hy
        have hyW : f y ∈ (W.1 : Set X) := ⟨y, hy, rfl⟩
        rw [s.covers] at hyW
        obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp hyW
        exact Set.mem_iUnion.mpr ⟨i, z, (hiff i z y).mpr hz⟩
      · exact Set.iUnion_subset hcontained
  }
  refine ⟨s', fun i => ?_⟩
  refine ObjectProperty.prop_of_iso _
    ((proetaleModuleInverseImageCompIso.{u, v, w} Λ (m i) f).app F).symm ?_
  change IsFiniteTypeLocallyConstantModuleSheaf _ _
    ((proetaleModuleInverseImage.{u, v, w} (m i ≫ f) Λ).obj F)
  rw [hm i]
  exact hs i

/-- Local constancy of a sheaf is invariant under isomorphism. -/
theorem isLocallyConstant_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {D : Type*} [Category D] [∀ U : C, HasWeakSheafify (J.over U) D] {F F' : Sheaf J D}
    (e : F ≅ F') [hF : IsLocallyConstant J F] : IsLocallyConstant J F' where
  exists_cover U := by
    obtain ⟨I, V, f, hf, h⟩ := hF.exists_cover U
    exact ⟨I, V, f, hf, fun i => ⟨ObjectProperty.prop_of_iso _
      ((J.overPullback D (V i)).mapIso e) (h i).mem_essImage⟩⟩

/-- **Inverse image preserves local constancy** (Stacks 093R), for sheaves of modules on the
small pro-étale sites along any morphism of schemes. -/
theorem isLocallyConstant_proetaleModuleInverseImage {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    [IsLocallyConstant (Scheme.ProEt.topology X) F] :
    IsLocallyConstant (Scheme.ProEt.topology Y)
      ((proetaleModuleInverseImage.{u, v, w} g Λ).obj F) := by
  have := isLocallyConstant_sheafPullback (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
    (ModuleCat.{max (u + 1) v w} Λ) (Scheme.proetaleBaseChange g)
    (CoverPreserving.of_isContinuous _ _ _) F
  exact isLocallyConstant_of_iso
    ((proetaleModuleInverseImageIsoSheafPullback.{u, v, w} Λ g).app F).symm

variable {I : Ideal Λ}

/-- Being a lisse constructible `Λ`-sheaf is invariant under isomorphism. -/
theorem IsLisseAdicModuleSheaf.of_iso [IsNoetherianRing Λ] {X : Scheme.{u}}
    {F F' : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)} (e : F ≅ F')
    (hF : IsLisseAdicModuleSheaf.{w} X Λ I F) : IsLisseAdicModuleSheaf.{w} X Λ I F' := by
  obtain ⟨Q, q, ⟨hlim⟩, hQ⟩ := hF
  refine ⟨Q, (Functor.const ℕᵒᵖ).map e.inv ≫ q, ⟨?_⟩, fun n => ⟨?_, (hQ n).2⟩⟩
  · exact IsLimit.ofIsoLimit hlim (Cone.ext e (fun _ => by simp))
  · exact Stacks.ModuleSheaf.isQuotientBy_of_iso e.symm (hQ n).1

/-- **A lisse constructible `Λ`-sheaf restricts to one on an open subscheme.** Inverse image along
an open immersion is restriction along it: a `Λ`-linear left adjoint preserving limits, which
commutes with restriction of coefficients and preserves constructibility and local constancy. -/
theorem IsLisseAdicModuleSheaf.proetaleModuleInverseImage [IsNoetherianRing Λ] {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f]
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
    (hF : IsLisseAdicModuleSheaf.{w} X Λ I F) :
    IsLisseAdicModuleSheaf.{w} Y Λ I ((proetaleModuleInverseImage.{u, v, w} f Λ).obj F) := by
  let A := ModuleCat.{max (u + 1) v w} Λ
  let R := (proetalePostcompose f).sheafPushforwardContinuous A
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  have : R.Linear Λ := ⟨fun _ _ => rfl⟩
  refine IsLisseAdicModuleSheaf.of_iso
    ((proetaleModuleInverseImageIsoRestriction.{u, v, w} Λ f).app F).symm ?_
  obtain ⟨Q, q, ⟨hlim⟩, hQ⟩ := hF
  refine ⟨Q ⋙ R, (R.mapCone (Cone.mk F q)).π, ⟨isLimitOfPreserves R hlim⟩, fun n => ⟨?_, ?_⟩⟩
  · exact (hQ n).1.map R ((proetalePostcomposeAdjunction f).sheafPushforwardContinuous _ _)
  · obtain ⟨-, G, ⟨e⟩, hGc, hGl⟩ := hQ n
    let R' := (proetalePostcompose f).sheafPushforwardContinuous
      (ModuleCat.{max (u + 1) v w} (Λ ⧸ I ^ n)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    let e' := (proetaleModuleInverseImageIsoRestriction.{u, v, w} (Λ ⧸ I ^ n) f).app G
    refine ⟨R'.obj G, ⟨R.mapIso e⟩, ObjectProperty.prop_of_iso _ e'
      (isConstructibleModuleSheaf'_proetaleModuleInverseImage f G hGc), ?_⟩
    have := isLocallyConstant_proetaleModuleInverseImage (Λ := Λ ⧸ I ^ n) f G
    exact isLocallyConstant_of_iso e'

end AlgebraicGeometry.ProEtale

end
