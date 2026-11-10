module

public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.ProjectiveExtensionBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.SchemeBlowupIsBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The blowup in the centre of a rational map, on an affine chart of an algebraic space

Let `V` be an affine locally Noetherian scheme of the site carrying a rational map
`[g₀ : ⋯ : gₘ] : U ⟶ ℙᵐ` with centre `𝒥 = centreSheaf U I g`, and let `t : T ⟶ V` be a morphism
of the site which is an isomorphism over `U` and comes with a closed immersion into `V × ℙᵐ`
over `V` whose second component is the rational map over `U`. Let `Z` be the closed subspace of
the algebraic space of `V` with the points of `V(𝒥)`.

If `b : X'' ⟶ T` is the blowup of `T` in the inverse image of `Z`, then `b ≫ t` is the blowup of
`V` in `Z`. On schemes this is
`Stacks.ProjectiveExtension.C1573.exists_iso_blowUp_comap_centreSheaf`; the passage to algebraic
spaces is `AlgebraicGeometry.Space.C1573.exists_isBlowupAlong_blowUp` on `T` and on `V`.

## Main results

* `AlgebraicGeometry.Space.C1573.preimage_subschemePoints_comap`: the inverse image of the closed
  subspace of a closed subscheme `V(J)` is the closed subspace of `V(t⁻¹J)`.
* `AlgebraicGeometry.Space.C1573.isBlowupAlong_comp_of_centreSheaf`: the statement above.

## References

* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inverse image along a morphism of the site of the closed subspace of the points of a
closed subscheme `V(J)` is the closed subspace of the points of `V(t⁻¹J)`. -/
theorem C1573.preimage_subschemePoints_comap {T V : BigFppfOver B S hS} (t : T ⟶ V)
    (J : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData) :
    (subschemePoints B S hS (Subobject.mk J.subschemeι)).preimage (yoneda.map t) =
      subschemePoints B S hS
        (Subobject.mk (J.comap ((BigFppfOver.toScheme B S hS).map t)).subschemeι) := by
  rw [← Scheme.IdealSheafData.pullback_subobject_mk_subschemeι, subschemePoints_pullback]

/-- The algebraic space of a composite of morphisms of the site is the composite. -/
theorem C1573.schemeSpaceMap_comp {T V W : BigFppfOver B S hS} (f : T ⟶ V) (g : V ⟶ W) :
    schemeSpaceMap (f ≫ g) = schemeSpaceMap f ≫ schemeSpaceMap g :=
  ObjectProperty.hom_ext _ (yoneda.map_comp f g)

/-- A morphism of the site whose underlying morphism of schemes is an isomorphism induces an
isomorphism of algebraic spaces. -/
theorem C1573.isIso_schemeSpaceMap_of_isIso {T V : BigFppfOver B S hS} (t : T ⟶ V)
    [IsIso ((BigFppfOver.toScheme B S hS).map t)] : IsIso (schemeSpaceMap t) := by
  have : IsIso t := isIso_of_reflects_iso t (BigFppfOver.toScheme B S hS)
  have : IsIso (yoneda.map t) := inferInstance
  exact (ObjectProperty.isIso_hom_iff (schemeSpaceMap t)).mp this

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

open Stacks.ProjectiveExtension Stacks.SectionsToProjectiveSpace
  _root_.Stacks.ProjectiveExtension.C1573 in
/-- **The blowup in the centre of a rational map, on an affine chart.** In the situation of
`Stacks.ProjectiveExtension.C1573.exists_iso_blowUp_comap_centreSheaf` on a scheme `V` of the site,
with `t : T ⟶ V` a morphism of the site: if `b : X'' ⟶ T` is the blowup of `T` in the inverse
image of the closed subspace `Z` of the points of `V(𝒥)`, then `b ≫ t` is the blowup of `V` in
`Z`. -/
theorem C1573.isBlowupAlong_comp_of_centreSheaf {T V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (U : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {m : ℕ}
    (g : Fin (m + 1) → Γ((BigFppfOver.toScheme B S hS).obj V, U))
    (hU : IsCompact (U : Set ((BigFppfOver.toScheme B S hS).obj V)))
    (hU' : _root_.IsQuasiSeparated (U : Set ((BigFppfOver.toScheme B S hS).obj V)))
    (hIle : ∀ f ∈ I, ((BigFppfOver.toScheme B S hS).obj V).basicOpen f ≤ U)
    (hIU : ∀ x ∈ U, ∃ f ∈ I, x ∈ ((BigFppfOver.toScheme B S hS).obj V).basicOpen f)
    (hg : Ideal.span (Set.range g) = ⊤)
    (hgU : Ideal.span (Set.range fun j => U.topIso.inv (g j)) = ⊤)
    (t : T ⟶ V)
    (c : (BigFppfOver.toScheme B S hS).obj T ⟶
      pullback (terminal.from ((BigFppfOver.toScheme B S hS).obj V))
        (terminal.from (projectiveSpaceAtUniverse.{u} m)))
    [_root_.AlgebraicGeometry.IsClosedImmersion c]
    (hct : c ≫ pullback.fst _ _ = (BigFppfOver.toScheme B S hS).map t)
    [IsIso ((BigFppfOver.toScheme B S hS).map t ∣_ U)]
    (hcg : ((BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ U).ι ≫ c ≫ pullback.snd _ _ =
      ((BigFppfOver.toScheme B S hS).map t ∣_ U) ≫
        toProjectiveSpaceAtUniverse (fun j => U.topIso.inv (g j)) hgU)
    (Z : ClosedSubspaces B S hS (schemeSpace V).obj)
    (hZ : Z.1 = subschemePoints B S hS (Subobject.mk (centreSheaf U I g).subschemeι))
    {X'' : AlgebraicSpaces B S hS} (b : X'' ⟶ schemeSpace T)
    (hb : IsBlowupAlong B S hS (preimageClosedSubspace (schemeSpaceMap t) Z) b) :
    IsBlowupAlong B S hS Z (b ≫ schemeSpaceMap t) := by
  set J := centreSheaf U I g with hJ
  -- the blowup of `T` in the inverse image of `J`
  have hZT : (preimageClosedSubspace (schemeSpaceMap t) Z).1 =
      subschemePoints B S hS
        (Subobject.mk (J.comap ((BigFppfOver.toScheme B S hS).map t)).subschemeι) := by
    change Z.1.preimage (yoneda.map t) = _
    rw [hZ]
    exact preimage_subschemePoints_comap t J
  obtain ⟨W₁, p₁, e₁, he₁, hb₁⟩ :=
    exists_isBlowupAlong_blowUp T (J.comap ((BigFppfOver.toScheme B S hS).map t)) _ hZT
  obtain ⟨W₂, p₂, e₂, he₂, hb₂⟩ := exists_isBlowupAlong_blowUp V J Z hZ
  -- the comparison of the two blowups over `V`
  obtain ⟨eR, heR⟩ := exists_iso_blowUp_comap_centreSheaf U I g hU hU' hIle hIU hg hgU
    ((BigFppfOver.toScheme B S hS).map t) c hct hcg
  set h : (BigFppfOver.toScheme B S hS).obj W₁ ⟶ (BigFppfOver.toScheme B S hS).obj W₂ :=
    e₁.hom ≫ eR.hom ≫ e₂.inv with hh
  have hhp : h ≫ (BigFppfOver.toScheme B S hS).map p₂ =
      (BigFppfOver.toScheme B S hS).map p₁ ≫ (BigFppfOver.toScheme B S hS).map t := by
    rw [hh, ← he₂, ← he₁, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, heR,
      Category.assoc]
  have hw : h ≫ B.inclusion.map W₂.hom = B.inclusion.map W₁.hom := by
    have hinc : ∀ {W : BigFppfOver B S hS} (p : W ⟶ V), B.inclusion.map W.hom =
        (BigFppfOver.toScheme B S hS).map p ≫ B.inclusion.map V.hom := fun p => by
      rw [← Over.w p, Functor.map_comp]; rfl
    rw [hinc p₂, ← Category.assoc, hhp, Category.assoc, hinc (p₁ ≫ t), Functor.map_comp,
      Category.assoc]
  set φ : W₁ ⟶ W₂ := siteHomOfScheme h hw with hφ
  have hFφ : (BigFppfOver.toScheme B S hS).map φ = h := toScheme_map_siteHomOfScheme h hw
  have : IsIso ((BigFppfOver.toScheme B S hS).map φ) := by rw [hFφ]; infer_instance
  have hφp : φ ≫ p₂ = p₁ ≫ t := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp, hFφ, hhp]
  have : IsIso (schemeSpaceMap φ) := isIso_schemeSpaceMap_of_isIso φ
  have hV : IsBlowupAlong B S hS Z (schemeSpaceMap (p₁ ≫ t)) := by
    have := hb₂.of_iso_over (asIso (schemeSpaceMap φ))
    rwa [asIso_hom, ← schemeSpaceMap_comp, hφp] at this
  -- transport along the comparison of `b` with the blowup of `T`
  obtain ⟨e, he⟩ := hb.exists_iso hb₁
  have := hV.of_iso_over e
  rwa [schemeSpaceMap_comp, ← Category.assoc, he] at this

end AlgebraicGeometry.Space

end
