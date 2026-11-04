module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.LocalSchemeDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.GenericPointReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SupportedSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange

/-!
# The local-sections input of Exposé XVIII-A, Lemma 2.2

This file proves `AlgebraicGeometry.Scheme.LocalSectionsAtPoint n` for every `n`, with
`Ψ = Γ(Spec 𝒪_{X,η}, g⁻¹ -)`, `g = X.fromSpecStalk η`
(`AlgebraicGeometry.Scheme.localSchemeSections`).

Let `U` be open and `η` a maximal point of `X ∖ U`. Every point of `Spec 𝒪_{X,η}` other than the
closed point maps to a generalization of `η` distinct from `η`, which lies in `U` by maximality.
So for a sheaf `𝓖` with zero stalks over `U`, the inverse image `g⁻¹𝓖` has zero stalks away from
the closed point, hence is the direct image `i_*𝓗` along `i : Spec κ(η) ⟶ Spec 𝒪_{X,η}`
(`Stacks.EtaleCohomology.isIso_smallEtaleAdjunctionAb_unit_app_of_isZero_stalk`), and
`R^pΨ(𝓖) = H^p(Spec 𝒪_{X,η}, i_*𝓗) = H^p(Spec κ(η), 𝓗)`, which vanishes above any bound `c` for
`Spec κ(η)` when `𝓖` is killed by `n`. If moreover the stalks of `𝓖` over `η` vanish, then
`g⁻¹𝓖 = 0`.

## Main results

* `AlgebraicGeometry.Scheme.fromSpecStalk_mem_of_notMem_range`: the points of the local scheme.
* `AlgebraicGeometry.Scheme.subsingleton_sheafH_localSchemePullback_of_isZero_stalk`: the
  vanishing above the bound.
* `AlgebraicGeometry.Scheme.isZero_localSchemePullback_of_isZero_stalk`: the vanishing of `g⁻¹𝓖`.
* `AlgebraicGeometry.Scheme.localSectionsAtPoint`: **the local-sections input**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (U : X.Opens) (η : X)

/-- The canonical morphism `Spec 𝒪_{X,η} ⟶ X` carries the image of `Spec κ(η)` to `η`. -/
theorem fromSpecStalk_residue_apply (z : Spec (X.residueField η)) :
    X.fromSpecStalk η (Spec.map (X.residue η) z) = η := by
  have hz : X.fromSpecResidueField η z ∈ ({η} : Set X) :=
    Scheme.range_fromSpecResidueField η ▸ Set.mem_range_self z
  exact hz

/-- A point of `Spec 𝒪_{X,η}` lying over `η` is the image of `Spec κ(η)`. -/
theorem mem_range_residue_of_fromSpecStalk_eq (y : Spec (X.presheaf.stalk η))
    (hy : X.fromSpecStalk η y = η) : y ∈ Set.range (Spec.map (X.residue η)) := by
  let z : Spec (X.residueField η) := IsLocalRing.closedPoint (X.residueField η)
  exact ⟨z, (X.fromSpecStalk η).isEmbedding.injective
    ((fromSpecStalk_residue_apply η z).trans hy.symm)⟩

/-- **The points of the local scheme at a maximal point of `X ∖ U`.** A point of
`Spec 𝒪_{X,η}` outside the image of `Spec κ(η)` maps into `U`: it maps to a generalization of `η`
distinct from `η`. -/
theorem fromSpecStalk_mem_of_notMem_range
    (hmax : ∀ x : X, η ∈ closure ({x} : Set X) → x ∉ U → x = η) (y : Spec (X.presheaf.stalk η))
    (hy : y ∉ Set.range (Spec.map (X.residue η))) : X.fromSpecStalk η y ∈ U := by
  by_contra hU
  have hsp : X.fromSpecStalk η y ⤳ η := by
    have h : X.fromSpecStalk η y ∈ Set.range (X.fromSpecStalk η) := Set.mem_range_self y
    rw [Scheme.range_fromSpecStalk] at h
    exact h
  exact hy (mem_range_residue_of_fromSpecStalk_eq η y
    (hmax _ (specializes_iff_mem_closure.1 hsp) hU))

/-- The geometric point of `X` obtained by composing with `X.fromSpecStalk η`. -/
def localSchemeGeometricPoint (t : GeometricPoint (Spec (X.presheaf.stalk η))) :
    GeometricPoint X where
  residueField := t.residueField
  hom := t.hom ≫ X.fromSpecStalk η

/-- The stalk of `g⁻¹𝓖` at a geometric point is the stalk of `𝓖` at its image. -/
def localSchemeStalkIso (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : GeometricPoint (Spec (X.presheaf.stalk η))) :
    (smallEtaleStalkAb t.hom).obj ((smallEtalePullbackAb (X.fromSpecStalk η)).obj G) ≅
      (smallEtaleStalkAb (localSchemeGeometricPoint η t).hom).obj G :=
  (smallEtaleStalkPullbackAbIso (X.fromSpecStalk η) t.hom).app G

/-- **Stalks of `g⁻¹𝓖` away from the closed point.** If `𝓖` has zero stalks over `U`, then
`g⁻¹𝓖` has zero stalks at the geometric points of `Spec 𝒪_{X,η}` outside the image of
`Spec κ(η)`. -/
theorem isZero_stalk_localSchemePullback_of_notMem_range
    (hmax : ∀ x : X, η ∈ closure ({x} : Set X) → x ∉ U → x = η)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hGU : ∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) ∈ U →
      IsZero ((smallEtaleStalkAb s.hom).obj G))
    (t : GeometricPoint (Spec (X.presheaf.stalk η)))
    (ht : t.hom (IsLocalRing.closedPoint t.residueField) ∉ Set.range (Spec.map (X.residue η))) :
    IsZero ((smallEtaleStalkAb t.hom).obj ((smallEtalePullbackAb (X.fromSpecStalk η)).obj G)) :=
  (hGU (localSchemeGeometricPoint η t)
    (fromSpecStalk_mem_of_notMem_range U η hmax _ ht)).of_iso (localSchemeStalkIso η G t)

/-- **The vanishing above the bound.** If `𝓖` is killed by `n`, has zero stalks over `U`, and
`c` bounds the cohomology of `n`-torsion sheaves on `Spec κ(η)`, then
`H^p(Spec 𝒪_{X,η}, g⁻¹𝓖) = 0` for `p > c`. -/
theorem subsingleton_sheafH_localSchemePullback_of_isZero_stalk {n : ℕ}
    (hmax : ∀ x : X, η ∈ closure ({x} : Set X) → x ∉ U → x = η) {c : WithBot ℕ∞}
    (hc : IsTorsionVanishingBound (Spec (.of (X.residueField η))) n c)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hGn : ∀ (T : X.Etale) (x : G.obj.obj (op T)), n • x = 0)
    (hGU : ∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) ∈ U →
      IsZero ((smallEtaleStalkAb s.hom).obj G))
    (p : ℕ) (hp : c < p) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((smallEtalePullbackAb (X.fromSpecStalk η)).obj G) p) := by
  let i := Spec.map (X.residue η)
  let G' := (smallEtalePullbackAb (X.fromSpecStalk η)).obj G
  have : IsIso ((smallEtaleAdjunctionAb i).unit.app G') :=
    isIso_smallEtaleAdjunctionAb_unit_app_of_isZero_stalk i G'
      (isZero_stalk_localSchemePullback_of_notMem_range U η hmax G hGU)
  let H := (smallEtalePullbackAb i).obj G'
  have hH : ∀ (T : (Spec (.of (X.residueField η))).Etale) (x : H.obj.obj (op T)), n • x = 0 :=
    (forall_nsmul_eq_zero_iff_nsmul_id_eq_zero H).2
      (nsmul_id_obj_eq_zero (smallEtalePullbackAb (X.fromSpecStalk η) ⋙ smallEtalePullbackAb i)
        ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero G).1 hGn))
  have := hc H hH p hp
  refine (subsingleton_H_iff_of_iso (asIso ((smallEtaleAdjunctionAb i).unit.app G')) p).2 ?_
  exact (sheafHSmallEtalePushforwardAddEquiv i H p).symm.injective.subsingleton

/-- **The vanishing of `g⁻¹𝓖`.** If `𝓖` has zero stalks over `U` and over `η`, then `g⁻¹𝓖 = 0`. -/
theorem isZero_localSchemePullback_of_isZero_stalk
    (hmax : ∀ x : X, η ∈ closure ({x} : Set X) → x ∉ U → x = η)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ∀ s : GeometricPoint X, (s.hom (IsLocalRing.closedPoint s.residueField) ∈ U ∨
        s.hom (IsLocalRing.closedPoint s.residueField) = η) →
      IsZero ((smallEtaleStalkAb s.hom).obj G)) :
    IsZero ((smallEtalePullbackAb (X.fromSpecStalk η)).obj G) := by
  refine isZero_of_forall_isZero_smallEtaleStalkAb _ fun t => ?_
  refine (hG (localSchemeGeometricPoint η t) ?_).of_iso (localSchemeStalkIso η G t)
  by_cases ht : t.hom (IsLocalRing.closedPoint t.residueField) ∈
      Set.range (Spec.map (X.residue η))
  · obtain ⟨z, hz⟩ := ht
    refine Or.inr ?_
    change X.fromSpecStalk η (t.hom (IsLocalRing.closedPoint t.residueField)) = η
    rw [← hz]
    exact fromSpecStalk_residue_apply η z
  · exact Or.inl (fromSpecStalk_mem_of_notMem_range U η hmax _ ht)

/-- The étale cohomology of a zero sheaf vanishes in every degree. -/
theorem subsingleton_sheafH_of_isZero_of_localScheme {Y : Scheme.{u}}
    (Z : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (hZ : IsZero Z) (p : ℕ) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} Z p) :=
  ⟨fun x y ↦ by
    rw [← Abelian.Ext.comp_mk₀_id x, ← Abelian.Ext.comp_mk₀_id y, hZ.eq_of_src (𝟙 Z) 0,
      Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero, Abelian.Ext.comp_zero]⟩

/-- **The local-sections input of Exposé XVIII-A, Lemma 2.2**, with
`Ψ = Γ(Spec 𝒪_{X,η}, g⁻¹ -)`. -/
theorem localSectionsAtPoint (n : ℕ) : LocalSectionsAtPoint.{u} n := by
  intro X _ _ U η _ hmax c hc
  exact ⟨{
    Ψ := localSchemeSections η
    θ := localSchemeSectionsι η
    comp := localSchemeSectionsι_comp η
    surj := exists_localSchemeSectionsι_app_eq η
    ker := exists_map_eq_zero_of_localSchemeSectionsι_app_eq_zero η
    vanish := fun G hGn hGU p hp =>
      isZero_rightDerived_localSchemeSections_of_subsingleton η G p
        (subsingleton_sheafH_localSchemePullback_of_isZero_stalk U η hmax hc G hGn hGU p hp)
    vanish' := fun G hG p =>
      isZero_rightDerived_localSchemeSections_of_subsingleton η G p
        (subsingleton_sheafH_of_isZero_of_localScheme _
          (isZero_localSchemePullback_of_isZero_stalk U η hmax G hG) p) }⟩

end AlgebraicGeometry.Scheme

end
