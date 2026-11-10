module

public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Connected.LocallyConnected
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.IdentitySubgroup
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.Topology.Noetherian.LocallyConnected

/-!
# A finite family of rational points of a group scheme lies in an affine open

Let `G` be a group scheme locally of finite type over an algebraically closed field.  Every
finite family of rational points of `G` is contained in a single affine open subset.

## Main results

* `AlgebraicGeometry.exists_affineOpen_containing_rational_points`: a finite family of rational
  points of a locally algebraic group scheme over an algebraically closed field lies in an
  affine open.

## Implementation notes

A group scheme over `k` is a group object in schemes over `Spec k`; a rational point is a
morphism from the final object of that category, and the corresponding point of the underlying
space is the image of the unique point of `Spec k`.  The family is indexed by an arbitrary
finite type, whose universe is independent of that of the schemes.

## References

* [Stacks Project, Tag 0B7S](https://stacks.math.columbia.edu/tag/0B7S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory

universe u v

/-- A homeomorphism carries the connected component of a point to the connected component of
its image. -/
theorem Homeomorph.image_connectedComponent {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) (x : X) :
    h '' connectedComponent x = connectedComponent (h x) := by
  simpa [connectedComponentIn_univ] using
    h.image_connectedComponentIn (s := _root_.Set.univ) (x := x) (_root_.Set.mem_univ x)

/-- In an irreducible space a finite family of nonempty open subsets has a common point. -/
theorem exists_mem_iInter_of_irreducibleSpace {X : Type*} [TopologicalSpace X]
    [IrreducibleSpace X] {σ : Type*} [Finite σ] (U : σ → Opens X)
    (hU : ∀ i, (U i : Set X).Nonempty) : ∃ x, ∀ i, x ∈ U i := by
  classical
  let _ := Fintype.ofFinite σ
  obtain ⟨x, -, hx⟩ :=
    (isIrreducible_iff_sInter.mp (IrreducibleSpace.isIrreducible_univ X))
      (Finset.univ.image fun i => (U i : Set X))
      (by
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        rintro s ⟨i, rfl⟩
        exact (U i).2)
      (by
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        rintro s ⟨i, rfl⟩
        simpa using hU i)
  exact ⟨x, fun i => (Set.mem_sInter.mp hx) (U i)
    (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))⟩

/-- If a homeomorphism carries `x₀` and `x` into the same connected component, then `x` lies in
the connected component of `x₀`. -/
private theorem Homeomorph.mem_connectedComponent_of_apply_mem {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (φ : X ≃ₜ Y) {x₀ x : X} {e : Y} (h₀ : φ x₀ ∈ connectedComponent e)
    (hx : φ x ∈ connectedComponent e) : x ∈ connectedComponent x₀ := by
  rw [connectedComponent_eq h₀, ← φ.image_connectedComponent] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact φ.injective hxy ▸ hy

/-- An isomorphism in an over category has an isomorphism as underlying morphism. -/
private theorem CategoryTheory.Over.isIso_left_of_isIso {C : Type*} [Category C] {S : C}
    {X Y : Over S} (f : X ⟶ Y) [IsIso f] : IsIso f.left :=
  inferInstanceAs (IsIso ((Over.forget S).map f))

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- Right translation by a rational point of a group scheme, as an automorphism of the group
scheme over the base field. -/
noncomputable def rightTranslationIso (G : Grp (Over (Spec (.of k))))
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) : G.X ≅ G.X :=
  letI : GrpObj G.X := G.grp
  GrpObj.mulRight p

/-- Right translation by a rational point, as a homeomorphism of the underlying space. -/
noncomputable def rightTranslationHomeo (G : Grp (Over (Spec (.of k))))
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) : G.X.left ≃ₜ G.X.left := by
  let e := rightTranslationIso G p
  let _ : IsIso ((Over.forget (Spec (.of k))).map e.hom) := by infer_instance
  let _ : IsIso e.hom.left := by
    change IsIso ((Over.forget (Spec (.of k))).map e.hom)
    infer_instance
  exact e.hom.left.homeomorph

/-- Right translation by the inverse of a rational point carries that point to the unit. -/
private theorem comp_rightTranslationIso_inv (G : Grp (Over (Spec (.of k))))
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) :
    p ≫ (rightTranslationIso G (p ≫ GrpObj.inv)).hom =
      (MonObj.one : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) := by
  let _ : GrpObj G.X := G.grp
  simp [rightTranslationIso, GrpObj.mulRight, comp_lift_assoc]

/-- Right translation by the inverse of a rational point carries that point to the identity
point. -/
theorem rightTranslationHomeo_apply_self (G : Grp (Over (Spec (.of k))))
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) :
    rightTranslationHomeo G (p ≫ GrpObj.inv) (p.left.base (⊥ : PrimeSpectrum k)) =
      identityPoint k G := by
  exact congr(($(comp_rightTranslationIso_inv G p)).left.base (⊥ : PrimeSpectrum k))

/-- Right translation by the inverse of a rational point carries a rational point of the same
connected component into the connected component of the identity. -/
theorem rightTranslationHomeo_mem_connectedComponent_identityPoint
    (G : Grp (Over (Spec (.of k)))) (p q : 𝟙_ (Over (Spec (.of k))) ⟶ G.X)
    (hcomp : connectedComponent (q.left.base (⊥ : PrimeSpectrum k)) =
      connectedComponent (p.left.base (⊥ : PrimeSpectrum k))) :
    rightTranslationHomeo G (p ≫ GrpObj.inv) (q.left.base (⊥ : PrimeSpectrum k)) ∈
      connectedComponent (identityPoint k G) := by
  rw [← rightTranslationHomeo_apply_self G p, ← Homeomorph.image_connectedComponent]
  exact Set.mem_image_of_mem _ (hcomp ▸ mem_connectedComponent)

/-- A nonempty open subset of the identity component of a locally algebraic group scheme over
an algebraically closed field contains a rational point. -/
@[sga "3 VIA 2.5.4" "special case"]
theorem exists_rational_point_mem_of_isOpen_identityComponent [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType G.X.hom]
    (W : (identityComponent k G).carrier.X.left.Opens)
    (hW : (W : Set (identityComponent k G).carrier.X.left).Nonempty) :
    ∃ p : 𝟙_ (Over (Spec (.of k))) ⟶ (identityComponent k G).carrier.X,
      p.left.base (⊥ : PrimeSpectrum k) ∈ W := by
  let H := identityComponent k G
  let _ : IsClosedImmersion H.ι.hom.hom.left := H.isClosedImmersion
  let _ : LocallyOfFiniteType H.carrier.X.hom := by
    rw [← H.ι.hom.hom.w]
    infer_instance
  let _ : JacobsonSpace H.carrier.X.left := LocallyOfFiniteType.jacobsonSpace H.carrier.X.hom
  obtain ⟨x, hxW, hxc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  let q := (pointEquivClosedPoint H.carrier.X.hom).symm ⟨x, hxc⟩
  refine ⟨Over.homMk q.1 q.2, ?_⟩
  have hbot : (⊥ : PrimeSpectrum k) = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  rw [hbot]
  have hqx : q.1 (IsLocalRing.closedPoint k) = x := by
    simpa [q, pointEquivClosedPoint] using
      congrArg Subtype.val ((pointEquivClosedPoint H.carrier.X.hom).apply_symm_apply ⟨x, hxc⟩)
  change q.1 (IsLocalRing.closedPoint k) ∈ W
  rwa [hqx]

/-- The identity point of a locally algebraic group scheme has an affine open neighbourhood
contained in its connected component. -/
theorem exists_affineOpen_mem_identityPoint_subset_connectedComponent
    (G : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType G.X.hom] :
    ∃ U : G.X.left.Opens, IsAffineOpen U ∧ identityPoint k G ∈ U ∧
      (U : Set G.X.left) ⊆ connectedComponent (identityPoint k G) := by
  let _ : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let _ : LocallyConnectedSpace G.X.left :=
    IsLocallyNoetherianSpace.locallyConnectedSpace G.X.left
      (isLocallyNoetherianSpace_of_isLocallyNoetherian G.X.left)
  obtain ⟨_, ⟨U, hU, rfl⟩, heU, hUsub⟩ :=
    G.X.left.isBasis_affineOpens.exists_subset_of_mem_open
      (mem_connectedComponent (x := identityPoint k G)) isOpen_connectedComponent
  exact ⟨U, hU, heU, hUsub⟩

/-- For a finite family of rational points lying in one connected component, a single rational
point of the identity component translates each of them into a given affine open neighbourhood
of the identity. -/
theorem exists_rational_point_common_translate [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType G.X.hom] {σ : Type v} [Finite σ]
    (g : σ → (Over.mk (𝟙 (Spec (.of k))) ⟶ G.X)) (i₀ : σ)
    (hcomp : ∀ i, connectedComponent ((g i).left.base (⊥ : PrimeSpectrum k)) =
      connectedComponent ((g i₀).left.base (⊥ : PrimeSpectrum k)))
    (U₀ : G.X.left.Opens) (heU₀ : identityPoint k G ∈ U₀) :
    ∃ a : 𝟙_ (Over (Spec (.of k))) ⟶ (identityComponent k G).carrier.X, ∀ i,
      rightTranslationHomeo G
          ((g i ≫ (rightTranslationIso G ((g i₀) ≫ GrpObj.inv)).hom) ≫ GrpObj.inv)
          ((a ≫ (identityComponent k G).ι.hom.hom).left.base (⊥ : PrimeSpectrum k)) ∈ U₀ := by
  let H := identityComponent k G
  let p₀ := g i₀
  let τ₀ := rightTranslationIso G (p₀ ≫ GrpObj.inv)
  let q (i : σ) := g i ≫ τ₀.hom
  let V (i : σ) : G.X.left.Opens :=
    ⟨(rightTranslationHomeo G (q i ≫ GrpObj.inv)) ⁻¹' (U₀ : Set G.X.left),
      U₀.2.preimage (rightTranslationHomeo G (q i ≫ GrpObj.inv)).continuous_toFun⟩
  let W (i : σ) : H.carrier.X.left.Opens :=
    ⟨(H.ι.hom.hom.left) ⁻¹' (V i : Set G.X.left),
      (V i).2.preimage H.ι.hom.hom.left.continuous⟩
  have hW : ∀ i, (W i : Set H.carrier.X.left).Nonempty := by
    intro i
    obtain ⟨y, hy⟩ : (q i).left.base (⊥ : PrimeSpectrum k) ∈ Set.range H.ι.hom.hom.left := by
      rw [identityComponent_range]
      exact rightTranslationHomeo_mem_connectedComponent_identityPoint G p₀ (g i) (hcomp i)
    refine ⟨y, ?_⟩
    change rightTranslationHomeo G (q i ≫ GrpObj.inv) (H.ι.hom.hom.left y) ∈ U₀
    rw [hy, rightTranslationHomeo_apply_self]
    exact heU₀
  let _ : GeometricallyIrreducible H.carrier.X.hom :=
    identityComponent_geometricallyIrreducible k G
  let _ : IrreducibleSpace H.carrier.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton H.carrier.X.hom
  obtain ⟨y, hy⟩ := exists_mem_iInter_of_irreducibleSpace W hW
  obtain ⟨a, ha⟩ := exists_rational_point_mem_of_isOpen_identityComponent G (⨅ i, W i)
    ⟨y, by rw [Opens.coe_iInf]; exact Set.mem_iInter.mpr hy⟩
  refine ⟨a, fun i => ?_⟩
  have hai : (Over.Hom.left a).base (⊥ : PrimeSpectrum k) ∈ (W i : Set H.carrier.X.left) :=
    Set.mem_iInter.mp ((Opens.coe_iInf W).subset ha) i
  have hcompPt : H.ι.hom.hom.left.base ((Over.Hom.left a).base (⊥ : PrimeSpectrum k)) =
      (a ≫ H.ι.hom.hom).left.base (⊥ : PrimeSpectrum k) := rfl
  simpa [W, V, q, τ₀, H, Over.comp_left, Scheme.Hom.comp_base, Function.comp_apply,
    hcompPt] using hai

/-- A finite family of rational points of a locally algebraic group scheme over an
algebraically closed field lying in a single connected component is contained in an affine open
subset of that connected component. -/
theorem exists_affineOpen_containing_rational_points_of_connectedComponent_eq [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType G.X.hom] {σ : Type v} [Finite σ]
    (g : σ → (Over.mk (𝟙 (Spec (.of k))) ⟶ G.X)) (i₀ : σ)
    (hcomp : ∀ i, connectedComponent ((g i).left.base (⊥ : PrimeSpectrum k)) =
      connectedComponent ((g i₀).left.base (⊥ : PrimeSpectrum k))) :
    ∃ U : G.X.left.Opens, IsAffineOpen U ∧
      (∀ i, (g i).left.base (⊥ : PrimeSpectrum k) ∈ U) ∧
      (U : Set G.X.left) ⊆
        connectedComponent ((g i₀).left.base (⊥ : PrimeSpectrum k)) := by
  let _ : GrpObj G.X := G.grp
  let p₀ := g i₀
  obtain ⟨U₀, hU₀, heU₀, hU₀subset⟩ :=
    exists_affineOpen_mem_identityPoint_subset_connectedComponent G
  obtain ⟨a, ha⟩ := exists_rational_point_common_translate G g i₀ hcomp U₀ heU₀
  let H := identityComponent k G
  let aG := a ≫ H.ι.hom.hom
  let r := aG ≫ (rightTranslationIso G p₀).hom
  let invMap := (GrpObj.inv (X := G.X)).left
  have : IsIso invMap := Over.isIso_left_of_isIso (GrpObj.inv (X := G.X))
  let T := rightTranslationIso G (r ≫ GrpObj.inv)
  have : IsIso T.hom.left := Over.isIso_left_of_isIso T.hom
  have hunit : toUnit (Over.mk (𝟙 (Spec (.of k)))) = 𝟙 (Over.mk (𝟙 (Spec (.of k)))) :=
    toUnit_unique _ _
  let qi (i : σ) := g i ≫ (rightTranslationIso G (p₀ ≫ GrpObj.inv)).hom
  have hqi₀ : qi i₀ = toUnit (Over.mk (𝟙 (Spec (.of k)))) ≫ MonObj.one := by
    simpa [hunit] using comp_rightTranslationIso_inv G p₀
  have hgroup (i : σ) : (g i ≫ T.hom) ≫ GrpObj.inv =
      aG ≫ (rightTranslationIso G (qi i ≫ GrpObj.inv)).hom := by
    simp [T, r, aG, qi, hunit, rightTranslationIso, GrpObj.mulRight, comp_lift_assoc,
      MonObj.lift_lift_assoc, GrpObj.mul_inv_rev]
  let φ := (rightTranslationHomeo G (r ≫ GrpObj.inv)).trans invMap.homeomorph
  have hφp₀ : φ (p₀.left.base (⊥ : PrimeSpectrum k)) =
      aG.left.base (⊥ : PrimeSpectrum k) := by
    have hp := congr(($(hgroup i₀)).left (⊥ : PrimeSpectrum k))
    change ((p₀ ≫ T.hom) ≫ GrpObj.inv).left.base (⊥ : PrimeSpectrum k) =
      (aG ≫ (rightTranslationIso G (qi i₀ ≫ GrpObj.inv)).hom).left.base
        (⊥ : PrimeSpectrum k) at hp
    rw [hqi₀] at hp
    change ((p₀ ≫ T.hom) ≫ GrpObj.inv).left.base (⊥ : PrimeSpectrum k) =
      aG.left.base (⊥ : PrimeSpectrum k)
    simpa [rightTranslationIso, GrpObj.mulRight, hunit] using hp
  refine ⟨T.hom.left ⁻¹ᵁ (invMap ⁻¹ᵁ U₀), (hU₀.preimage invMap).preimage T.hom.left,
    fun i => ?_, fun x hx => ?_⟩
  · have hqi : rightTranslationHomeo G (qi i ≫ GrpObj.inv)
        (aG.left.base (⊥ : PrimeSpectrum k)) ∈ U₀ := by
      simpa [qi, aG, H, p₀, rightTranslationIso, Over.comp_left, Scheme.Hom.comp_base,
        Function.comp_apply] using ha i
    have hpt := congr(($(hgroup i)).left (⊥ : PrimeSpectrum k))
    change invMap.base (T.hom.left.base ((g i).left.base (⊥ : PrimeSpectrum k))) ∈ U₀
    rw [show invMap.base (T.hom.left.base ((g i).left.base (⊥ : PrimeSpectrum k))) =
      (rightTranslationIso G (qi i ≫ GrpObj.inv)).hom.left.base
        (aG.left.base (⊥ : PrimeSpectrum k)) from hpt]
    exact hqi
  · have hφx : φ x ∈ connectedComponent (identityPoint k G) := by
      change invMap.base (T.hom.left.base x) ∈ U₀ at hx
      exact hU₀subset hx
    refine φ.mem_connectedComponent_of_apply_mem ?_ hφx
    rw [hφp₀, ← identityComponent_range]
    exact ⟨(Over.Hom.left a).base (⊥ : PrimeSpectrum k), rfl⟩

/-- A finite family of rational points of a group scheme locally of finite type over an
algebraically closed field lies in an affine open. -/
@[stacks 0B7S, sga "3 XII 6.1"]
theorem exists_affineOpen_containing_rational_points (k : Type u) [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType G.X.hom] {σ : Type v} [Finite σ]
    (g : σ → (Over.mk (𝟙 (Spec (.of k))) ⟶ G.X)) :
    ∃ U : G.X.left.Opens, IsAffineOpen U ∧
      ∀ i, (g i).left.base (⊥ : PrimeSpectrum k) ∈ U := by
  classical
  let comp (i : σ) : Set G.X.left :=
    connectedComponent ((g i).left.base (⊥ : PrimeSpectrum k))
  let components : Set (Set G.X.left) := Set.range comp
  let _ : Finite components := (Set.finite_range comp).to_subtype
  let J (c : components) := {i : σ // comp i = c.1}
  let rep (c : components) := Classical.choose c.2
  have hrep (c : components) : comp (rep c) = c.1 := Classical.choose_spec c.2
  let repJ (c : components) : J c := ⟨rep c, hrep c⟩
  have hEx (c : components) :
      ∃ U : G.X.left.Opens, IsAffineOpen U ∧
        (∀ j : J c, (g j.1).left.base (⊥ : PrimeSpectrum k) ∈ U) ∧
        (U : Set G.X.left) ⊆ c.1 := by
    let _ : Finite (J c) := Finite.of_injective Subtype.val Subtype.val_injective
    obtain ⟨V, hV, hVpoints, hVsub⟩ :=
      exists_affineOpen_containing_rational_points_of_connectedComponent_eq G
        (fun j : J c => g j.1) (repJ c) (fun j => j.2.trans (repJ c).2.symm)
    exact ⟨V, hV, hVpoints, fun x hx => hrep c ▸ hVsub hx⟩
  choose U hU hpoints hsubset using hEx
  have hdisj : Pairwise fun c d => Disjoint (U c) (U d) := by
    intro c d hne
    rw [← Opens.coe_disjoint]
    refine Set.disjoint_left.mpr fun x hxc hxd => hne (Subtype.ext ?_)
    have hx1 : x ∈ comp (rep c) := (hrep c).symm ▸ hsubset c hxc
    have hx2 : x ∈ comp (rep d) := (hrep d).symm ▸ hsubset d hxd
    calc c.1 = comp (rep c) := (hrep c).symm
      _ = connectedComponent x := connectedComponent_eq hx1
      _ = comp (rep d) := (connectedComponent_eq hx2).symm
      _ = d.1 := hrep d
  exact ⟨⨆ c, U c, IsAffineOpen.iSup_of_disjoint hU hdisj,
    fun i => le_iSup U (⟨comp i, ⟨i, rfl⟩⟩ : components) (hpoints _ ⟨i, rfl⟩)⟩

end AlgebraicGeometry

end
