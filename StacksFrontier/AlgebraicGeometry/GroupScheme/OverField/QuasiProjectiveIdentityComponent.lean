module

public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.RationalPointsAffineOpen
public import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-projectivity of a group scheme from that of its identity component

Let `G` be a reduced group scheme of finite type over an algebraically closed field `k`. Then `G`
is the disjoint union of finitely many translates of its identity component `G⁰`, each by a
rational point, so `G` is quasi-projective over `k` as soon as `G⁰` is.

## Main results

* `AlgebraicGeometry.isOpenImmersion_identityComponent_ι`: for a reduced group scheme locally of
  finite type over a field, the inclusion of the identity component is an open immersion.
* `AlgebraicGeometry.locallyOfFiniteType_identityComponent`,
  `AlgebraicGeometry.quasiCompact_identityComponent` and
  `AlgebraicGeometry.smooth_identityComponent`: the identity component inherits these properties
  of the structure morphism.
* `AlgebraicGeometry.exists_rationalPoint_connectedComponents_mk`: over an algebraically closed
  field every connected component contains a rational point.
* `AlgebraicGeometry.isQuasiProjective_of_isQuasiProjective_identityComponent`: if the identity
  component is quasi-projective over `k`, so is `G`.

## References

* [Stacks Project, Tag 0BF7](https://stacks.math.columbia.edu/tag/0BF7)
* [Stacks Project, Tag 0B7R](https://stacks.math.columbia.edu/tag/0B7R)
* [Stacks Project, Tag 0B43](https://stacks.math.columbia.edu/tag/0B43)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The structure morphism of the identity component is the inclusion followed by the structure
morphism of the group scheme. -/
theorem identityComponent_ι_comp_hom (G : Grp (Over (Spec (.of k)))) :
    (identityComponent k G).ι.hom.hom.left ≫ G.X.hom = (identityComponent k G).carrier.X.hom :=
  (identityComponent k G).ι.hom.hom.w

/-- For a reduced group scheme locally of finite type over a field, the inclusion of the identity
component is an open immersion. -/
@[sga "3 VIA 2.3" "special case",
  sga "3 VIA 2.3.1" "partial",
  sga "3 VIA 2.6.5" "(i)(b), special case",
  sga "3 X 5.11.0" "special case",
  sga "3 XII 7.3" "special case",
  sga "3 XV 5.8" "special case",
  sga "3 XXII 5.3.0" "Over S = Spec k",
  sga "6 XIII 4.1" "partial"]
theorem isOpenImmersion_identityComponent_ι (G : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType G.X.hom] [IsReduced G.X.left] :
    IsOpenImmersion (identityComponent k G).ι.hom.hom.left := by
  have : IsClosedImmersion (identityComponent k G).ι.hom.hom.left :=
    (identityComponent k G).isClosedImmersion
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : LocallyConnectedSpace G.X.left :=
    IsLocallyNoetherianSpace.locallyConnectedSpace G.X.left
      (isLocallyNoetherianSpace_of_isLocallyNoetherian G.X.left)
  refine StacksTag09NE.isOpenImmersion_of_closedImmersion_of_open_range _ ?_
  rw [identityComponent_range]
  exact isOpen_connectedComponent

/-- The identity component of a group scheme locally of finite type over a field is locally of
finite type. -/
theorem locallyOfFiniteType_identityComponent (G : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (identityComponent k G).carrier.X.hom := by
  have : IsClosedImmersion (identityComponent k G).ι.hom.hom.left :=
    (identityComponent k G).isClosedImmersion
  rw [← identityComponent_ι_comp_hom]
  infer_instance

/-- The identity component of a quasi-compact group scheme over a field is quasi-compact. -/
theorem quasiCompact_identityComponent (G : Grp (Over (Spec (.of k))))
    [QuasiCompact G.X.hom] :
    QuasiCompact (identityComponent k G).carrier.X.hom := by
  have : IsClosedImmersion (identityComponent k G).ι.hom.hom.left :=
    (identityComponent k G).isClosedImmersion
  rw [← identityComponent_ι_comp_hom]
  infer_instance

/-- The identity component of a reduced smooth group scheme over a field is smooth. -/
@[sga "3 XII 7.3" "special case",
  sga "3 XV 5.8" "special case",
  sga "3 XXII 5.3.0" "Over S = Spec k"]
theorem smooth_identityComponent (G : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType G.X.hom] [IsReduced G.X.left] [Smooth G.X.hom] :
    Smooth (identityComponent k G).carrier.X.hom := by
  have := isOpenImmersion_identityComponent_ι G
  rw [← identityComponent_ι_comp_hom]
  infer_instance

/-- Every connected component of a group scheme locally of finite type over an algebraically
closed field contains a rational point. -/
theorem exists_rationalPoint_connectedComponents_mk [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType G.X.hom]
    (c : _root_.ConnectedComponents G.X.left) :
    ∃ p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X,
      _root_.ConnectedComponents.mk (p.left.base (⊥ : PrimeSpectrum k)) = c := by
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : LocallyConnectedSpace G.X.left :=
    IsLocallyNoetherianSpace.locallyConnectedSpace G.X.left
      (isLocallyNoetherianSpace_of_isLocallyNoetherian G.X.left)
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  obtain ⟨y, hyC, hyc⟩ := nonempty_inter_closedPoints ⟨x, mem_connectedComponent⟩
    (isOpen_connectedComponent (x := x)).isLocallyClosed
  let q := (pointEquivClosedPoint G.X.hom).symm ⟨y, hyc⟩
  refine ⟨Over.homMk q.1 q.2, ?_⟩
  have hbot : (⊥ : PrimeSpectrum k) = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have hqy : q.1 (IsLocalRing.closedPoint k) = y := by
    simpa [q, pointEquivClosedPoint] using
      congrArg Subtype.val ((pointEquivClosedPoint G.X.hom).apply_symm_apply ⟨y, hyc⟩)
  show _root_.ConnectedComponents.mk (q.1 (⊥ : PrimeSpectrum k)) = _root_.ConnectedComponents.mk x
  rw [hbot, hqy]
  exact _root_.ConnectedComponents.coe_eq_coe'.mpr hyC

/-- The inverse of right translation by the inverse of a rational point `p` carries the identity
component onto the connected component of `p`. -/
theorem range_identityComponent_ι_comp_rightTranslationIso_inv
    (G : Grp (Over (Spec (.of k)))) (p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) :
    Set.range ((identityComponent k G).ι.hom.hom.left ≫
        (rightTranslationIso G (p ≫ GrpObj.inv)).inv.left) =
      connectedComponent (p.left.base (⊥ : PrimeSpectrum k)) := by
  let _ : GrpObj G.X := G.grp
  let e := rightTranslationIso G (p ≫ GrpObj.inv)
  let φ := rightTranslationHomeo G (p ≫ GrpObj.inv)
  have hφ : ∀ x, φ x = e.hom.left x := fun _ => rfl
  have hsymm : ∀ x, e.inv.left x = φ.symm x := by
    intro x
    apply φ.injective
    rw [φ.apply_symm_apply, hφ, ← Scheme.Hom.comp_apply, ← Over.comp_left, e.inv_hom_id]
    rfl
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, identityComponent_range]
  have himg : (fun x => e.inv.left x) '' connectedComponent (identityPoint k G) =
      φ.symm '' connectedComponent (identityPoint k G) := by
    congr 1
    exact funext hsymm
  rw [himg, φ.symm.image_connectedComponent, ← rightTranslationHomeo_apply_self G p,
    φ.symm_apply_apply]

/-- Let `G` be a reduced group scheme of finite type over an algebraically closed field `k`. If the
identity component of `G` is quasi-projective over `k`, then so is `G`. -/
theorem isQuasiProjective_of_isQuasiProjective_identityComponent [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [IsReduced G.X.left] (h : IsQuasiProjective (identityComponent k G).carrier.X.hom) :
    IsQuasiProjective G.X.hom := by
  classical
  let H := identityComponent k G
  let ι₀ := H.ι.hom.hom.left
  have hcomp : ι₀ ≫ G.X.hom = H.carrier.X.hom := identityComponent_ι_comp_hom G
  have : IsOpenImmersion ι₀ := isOpenImmersion_identityComponent_ι G
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : LocallyConnectedSpace G.X.left :=
    IsLocallyNoetherianSpace.locallyConnectedSpace G.X.left
      (isLocallyNoetherianSpace_of_isLocallyNoetherian G.X.left)
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  let C := _root_.ConnectedComponents G.X.left
  choose p hp using exists_rationalPoint_connectedComponents_mk G
  let τ (c : C) := (rightTranslationIso G (p c ≫ GrpObj.inv)).inv
  let f (c : C) : H.carrier.X.left ⟶ G.X.left := ι₀ ≫ (τ c).left
  have hτiso : ∀ c, IsIso (τ c).left := fun c =>
    inferInstanceAs (IsIso ((Over.forget _).map (τ c)))
  have : ∀ c, IsOpenImmersion (f c) := fun c => by
    have := hτiso c
    infer_instance
  have hrange : ∀ c, Set.range (f c) =
      connectedComponent ((p c).left.base (⊥ : PrimeSpectrum k)) := fun c =>
    range_identityComponent_ι_comp_rightTranslationIso_inv G (p c)
  have hiso : IsIso (Sigma.desc f) := by
    refine StacksTag09NE.isIso_sigmaDesc_of_disjointOpenCover _ f ?_ ?_
    · intro c c' hcc'
      show Disjoint (Set.range (f c)) (Set.range (f c'))
      rw [hrange, hrange]
      refine connectedComponent_disjoint fun heq => hcc' ?_
      rw [← hp c, ← hp c']
      exact _root_.ConnectedComponents.coe_eq_coe.mpr heq
    · intro x
      let c : C := _root_.ConnectedComponents.mk x
      have hx : x ∈ Set.range (f c) := by
        rw [hrange]
        exact _root_.ConnectedComponents.coe_eq_coe'.mp (hp c).symm
      obtain ⟨z, hz⟩ := hx
      exact ⟨c, z, hz⟩
  have hf : ∀ c, f c ≫ G.X.hom = H.carrier.X.hom := by
    intro c
    show ι₀ ≫ (τ c).left ≫ G.X.hom = _
    rw [Over.w (τ c)]
    exact hcomp
  have hsig : IsQuasiProjective (Sigma.desc fun c => f c ≫ G.X.hom) :=
    isQuasiProjective_sigmaDesc (fun c => f c ≫ G.X.hom)
      (Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k)))
      (fun c => (hf c).symm ▸ h)
  have hdesc : (Sigma.desc fun c => f c ≫ G.X.hom) = Sigma.desc f ≫ G.X.hom := by
    ext c
    simp
  rw [hdesc] at hsig
  exact IsQuasiProjective.of_isPullback
    (IsPullback.of_horiz_isIso (fst := inv (Sigma.desc f)) (snd := G.X.hom)
      (f := Sigma.desc f ≫ G.X.hom) (g := 𝟙 _) ⟨by simp⟩) hsig

end AlgebraicGeometry

end

/-! ### Additional declarations -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
universe u
namespace AlgebraicGeometry
variable {k : Type u} [Field k]

/-- The inverse of right translation by the inverse of a rational point `p` carries the identity
component onto the connected component of `p`. -/
theorem range_identityComponent_ι_comp_mulRight_inv
    (G : Grp (Over (Spec (.of k)))) (p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) :
    Set.range ((identityComponent k G).ι.hom.hom.left ≫
        (GrpObj.mulRight (p ≫ GrpObj.inv)).inv.left) =
      connectedComponent (p.left.base (⊥ : PrimeSpectrum k)) :=
  range_identityComponent_ι_comp_rightTranslationIso_inv G p

end AlgebraicGeometry
end
