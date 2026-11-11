module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.DegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineQuotientAux
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.SmoothCharacteristicZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ProjectiveLineFactorization
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# Morphisms from the projective line to a group scheme are constant

Let `G` be a group scheme over a scheme `X`, separated and locally of finite type over `X`, and
let `k` be a field. A morphism of schemes `g : ℙ¹_k ⟶ G` whose composite with the structure
morphism of `G` has a single point `x` of `X` as its image is constant: it sends every point of
`ℙ¹_k` to one point of `G`.

## Main results

* `AlgebraicGeometry.exists_eq_toSpecΓ_comp_of_forall_eq`: a morphism of schemes all of whose
  points land in a single point factors through the canonical morphism `Y ⟶ Spec Γ(Y, ⊤)`.
* `AlgebraicGeometry.exists_eq_comp_of_projectiveSpace_to_grpObj`: over a field `k`, every
  morphism of schemes over `Spec k` from `ℙ¹_k` to a separated group scheme locally of finite
  type over `k` factors through the structure morphism of `ℙ¹_k`, followed by a `k`-point.
* `AlgebraicGeometry.exists_eq_of_projectiveLineProj_to_grpObj`: the statement above for a group
  scheme over an arbitrary base `X`, on points.

## Implementation notes

The constancy over a field is Stacks 0AEN, which the library has for group algebraic spaces as
`AlgebraicGeometry.Space.morphism_projectiveLine_constant`. The group scheme is placed in a big
fppf site containing it and `Spec k` (`AlgebraicGeometry.BigFppfSite.exists_containing`), read
as a group algebraic space through
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`, and separatedness and local
finite type are transported along the representing isomorphism
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda`. The constant
section produced by 0AEN is then read back as a morphism of schemes by the Yoneda lemma.

Over a general base `X`, the composite `ℙ¹_k ⟶ X` lands in an affine open neighbourhood of `x`,
hence factors through `Spec Γ(ℙ¹_k, ⊤) ≅ Spec k` (by
`isIso_appTop_structureMorphism_projectiveSpaceOverRing` in the namespace
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`), and `g` lifts to the base change
of `G` along the resulting `Spec k ⟶ X`, a separated group scheme locally of finite type over
`k`. The `Proj` model `AlgebraicGeometry.projectiveLineProj k` of the
projective line is compared with the model `projectiveSpaceOverRing 1 k` used by 0AEN through
`Stacks.ProjectiveCohomology.projModelIso`.

## References

* [Stacks Project, Tag 0AEN](https://stacks.math.columbia.edu/tag/0AEN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage
  (isIso_appTop_structureMorphism_projectiveSpaceOverRing)

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes `h : Y ⟶ X` sending every point of `Y` to one point `x` of `X`
factors through the canonical morphism `Y ⟶ Spec Γ(Y, ⊤)`: it lands in an affine open
neighbourhood of `x`, and morphisms to an affine scheme factor through `Y.toSpecΓ`. -/
theorem exists_eq_toSpecΓ_comp_of_forall_eq {Y X : Scheme.{u}} (h : Y ⟶ X) (x : X)
    (hx : ∀ z, h z = x) : ∃ t : Spec Γ(Y, ⊤) ⟶ X, h = Y.toSpecΓ ≫ t := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change X.Opens at U
  have hrange : Set.range h ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact (hx z).symm ▸ hxU
  have : IsAffine U := hU
  refine ⟨Spec.map (IsOpenImmersion.lift U.ι h hrange).appTop ≫
    inv (U : Scheme).toSpecΓ ≫ U.ι, ?_⟩
  rw [← Scheme.toSpecΓ_naturality_assoc, IsIso.hom_inv_id_assoc, IsOpenImmersion.lift_fac]

/-- **Stacks 0AEN for a group scheme over a field.** Let `k` be a field and let `G` be a group
scheme over `Spec k`, separated and locally of finite type over `k`. Every morphism of schemes
over `Spec k` from `ℙ¹_k` to `G` factors through the structure morphism of `ℙ¹_k`, followed by
a `k`-point of `G`. -/
theorem exists_eq_comp_of_projectiveSpace_to_grpObj (k : Type u) [Field k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom]
    (g : projectiveSpaceOverRing 1 (CommRingCat.of k) ⟶ G.left)
    (hg : g ≫ G.hom =
      projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) :
    ∃ s : Spec (CommRingCat.of k) ⟶ G.left,
      g = (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) ≫ s := by
  classical
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing {Spec (CommRingCat.of k), G.left}
  have hk : B.Contains (Spec (CommRingCat.of k)) := hB _ (by simp)
  have hG : B.Contains G.left := hB _ (by simp)
  have hsepT : Scheme.IsSeparated G.left := by
    have : IsSeparated (G.hom ≫ terminal.from _) := inferInstance
    exact ⟨by simpa using this⟩
  obtain ⟨T, rfl⟩ : ∃ T : BigFppfOver B (Spec (CommRingCat.of k)) hk,
      (Space.toSchemeOver B (Spec (CommRingCat.of k)) hk).obj T = G :=
    ⟨Over.mk (ObjectProperty.homMk G.hom : B.obj hG ⟶ B.obj hk), rfl⟩
  let hGT : GrpObj ((Space.toSchemeOver B (Spec (CommRingCat.of k)) hk).obj T) := inferInstance
  let Gs := Space.GroupAlgebraicSpace.ofGroupSchemeInSite B (Spec (CommRingCat.of k)) hk
    (Space.terminalSpace B (Spec (CommRingCat.of k)) hk).obj
    (Space.terminalSpace B (Spec (CommRingCat.of k)) hk).property T hGT
  let e := Space.GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda T hGT
  have hsep : Space.IsSeparatedOver B (Spec (CommRingCat.of k)) hk Gs.obj.X.left :=
    Space.isSeparatedOver_of_iso e
      (Space.isSeparatedOver_yoneda_obj B (Spec (CommRingCat.of k)) hk T hsepT)
  have hft : Space.IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk Gs.obj.X.hom :=
    (Space.isLocallyOfFiniteType_hom_iff_of_iso_yoneda Gs.obj.X T e).2 inferInstance
  let φ : Space.projectiveLineSiteObject k B hk ⟶ T :=
    Over.homMk (ObjectProperty.homMk g) (by ext1; exact hg)
  let fl := Pi.π (fun _ : Fin 1 => Space.projectiveLineFunctor k B hk) 0 ≫
    (Space.projectiveLineRestrictedYonedaIso k B hk).hom ≫ yoneda.map φ ≫ e.hom
  obtain ⟨c, -, hc⟩ := Space.morphism_projectiveLine_constant k B hk Gs hsep hft
    (Over.homMk fl (Space.terminalSpace_obj_isTerminal.hom_ext _ _))
  have h1 : yoneda.map φ ≫ e.hom =
      Space.terminalSpace_obj_isTerminal.from _ ≫ c := by
    have h := Pi.lift (fun _ : Fin 1 => (Space.projectiveLineRestrictedYonedaIso k B hk).inv) ≫=
      hc
    have hl : Pi.lift (fun _ : Fin 1 => (Space.projectiveLineRestrictedYonedaIso k B hk).inv) ≫
        fl = yoneda.map φ ≫ e.hom := by
      simp only [fl, Pi.lift_π_assoc, Iso.inv_hom_id_assoc]
    rw [← hl]
    exact h.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ c) (Space.terminalSpace_obj_isTerminal.hom_ext _ _)))
  let σ := Yoneda.fullyFaithful.preimage (c ≫ e.inv)
  have h2 : φ = Space.toBaseTerminal B (Spec (CommRingCat.of k)) hk _ ≫ σ := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Yoneda.fullyFaithful.map_preimage,
      show yoneda.map φ = _ from (Iso.eq_comp_inv e).2 h1]
    exact (Category.assoc _ _ _).trans
      (congrArg (fun f => f ≫ c ≫ e.inv) (Space.terminalSpace_obj_isTerminal.hom_ext _ _))
  exact ⟨σ.left.hom, congrArg (fun f => f.left.hom) h2⟩

/-- **A morphism from the projective line to a group scheme is constant on a fibre.** Let `G` be
a group scheme over a scheme `X`, separated and locally of finite type over `X`, let `k` be a
field and let `g : ℙ¹_k ⟶ G` be a morphism of schemes such that the composite with the
structure morphism of `G` sends every point to one point `x` of `X`. Then `g` sends every point
of `ℙ¹_k` to one point of `G`.

The composite `ℙ¹_k ⟶ X` factors through `Spec Γ(ℙ¹_k, ⊤) ≅ Spec k`, so `g` lifts to a morphism
over `Spec k` into the base change of `G`, which is constant by
`AlgebraicGeometry.exists_eq_comp_of_projectiveSpace_to_grpObj`. -/
theorem exists_eq_of_projectiveLineProj_to_grpObj {X : Scheme.{u}} (G : Over X) [GrpObj G]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] {k : Type u} [Field k]
    (g : projectiveLineProj k ⟶ G.left) (x : X) (hx : ∀ z, G.hom (g z) = x) :
    ∃ y : G.left, ∀ z, g z = y := by
  classical
  let P := projectiveSpaceOverRing 1 (CommRingCat.of k)
  let π := P ↘ Spec (CommRingCat.of k)
  let ι := Stacks.ProjectiveCohomology.projModelIso k 1
  let g₀ : P ⟶ G.left := ι.inv ≫ g
  obtain ⟨t₀, ht₀⟩ := exists_eq_toSpecΓ_comp_of_forall_eq (g₀ ≫ G.hom) x (fun z => hx _)
  have : IsIso π.appTop :=
    isIso_appTop_structureMorphism_projectiveSpaceOverRing 1 _
  have hP : P.toSpecΓ = π ≫ (Spec (CommRingCat.of k)).toSpecΓ ≫ inv (Spec.map π.appTop) := by
    rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  let t := (Spec (CommRingCat.of k)).toSpecΓ ≫ inv (Spec.map π.appTop) ≫ t₀
  have ht : g₀ ≫ G.hom = π ≫ t := by
    rw [ht₀, hP]
    simp only [t, Category.assoc]
  let Gk := (Over.pullback t).obj G
  have : IsSeparated Gk.hom := inferInstanceAs (IsSeparated (pullback.snd G.hom t))
  have : LocallyOfFiniteType Gk.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom t))
  obtain ⟨s, hs⟩ := exists_eq_comp_of_projectiveSpace_to_grpObj k Gk
    (pullback.lift g₀ π ht) (pullback.lift_snd _ _ _)
  have hg₀ : g₀ = π ≫ s ≫ pullback.fst G.hom t := by
    rw [← Category.assoc, ← hs]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
  refine ⟨(s ≫ pullback.fst G.hom t) p, fun z => ?_⟩
  have hz : g z = g₀ (ι.hom z) := by
    change g z = g (ι.inv (ι.hom z))
    rw [← Scheme.Hom.comp_apply ι.hom ι.inv z, ι.hom_inv_id]
    rfl
  rw [hz, hg₀, Scheme.Hom.comp_apply, Subsingleton.elim (π (ι.hom z)) p]

end AlgebraicGeometry

end
