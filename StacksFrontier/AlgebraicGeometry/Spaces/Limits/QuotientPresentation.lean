module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# The quotient presentation of a limit of algebraic spaces

For a cofiltered inverse system of algebraic spaces over `S` whose transition morphisms are
affine, the quotient of the limiting étale equivalence relation is canonically the limit
sheaf. Concretely, a surjective étale atlas `U₀ → X₀` of one stage pulls back to an atlas
`U = lim (U₀ ×_{X₀} X_i)` of the limit, its kernel pair `R` is an étale equivalence relation,
and the induced map `U/R → lim X_i` is an isomorphism of fppf sheaves.

## Main definitions

* `AlgebraicGeometry.Space.representedSheaf`: the fppf sheaf on the big site over `S`
  represented by an `S`-scheme.
* `AlgebraicGeometry.Space.canonicalQuotientToLimit`: the map from the quotient sheaf of a
  relation on the atlas to the limit, induced by the compatible maps out of the atlas.

## Main results

* `AlgebraicGeometry.Space.exists_quotient_presentation_of_affine_transition` (Stacks 07SG):
  the limiting atlas `U` and relation `R` exist, and the canonical map `U/R → lim X_i` is an
  isomorphism.
* `AlgebraicGeometry.Space.exists_pullbackStages_of_affine_transition`: the stagewise base
  changes of a chart of one stage form an inverse system of objects of the site whose limit
  exists in schemes over `S` and is preserved by `Over.forget S`.

## Implementation notes

The atlas `U` is built as the limit of the pullbacks `U₀ ×_{X₀} X_i` and `R` as the limit of
their kernel pairs; the cartesian-square conclusions characterize both, so no cardinality
hypothesis on the index category is needed. Surjectivity of `U → lim X_i` is expressed as an
epimorphism of fppf sheaves, and the quotient is identified with the limit by checking that
the comparison map out of the presheaf quotient is locally bijective.

The system of stages `AlgebraicGeometry.Space.exists_pullbackStages_of_affine_transition` is
stated for an arbitrary object of the site, not only an affine one as in
`AlgebraicGeometry.Space.AffineChartSystem`, and gives the atlas and the relation as limits of
schemes rather than only as vertices of cartesian squares.

## References

* [Stacks Project, Tag 07SG](https://stacks.math.columbia.edu/tag/07SG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S)

/-- The fppf sheaf represented by a scheme over the base, restricted to the site. -/
public def representedSheaf (U : Over S)
    (hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U)) :
    Sheaf (BigFppfOver.topology B S hS) (Type u) :=
  ⟨Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U, hU⟩

/-- The map from the quotient of the limiting relation to the inverse-limit
sheaf, induced by the compatible maps from its object scheme. -/
public noncomputable def canonicalQuotientToLimit
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    [HasLimit D] [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {U R : Over S} (j : Stacks.Groupoids.PreRelation R U)
    (hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U))
    (q : representedSheaf B S hS U hU ⟶ limit D)
    (hq : Stacks.Groupoids.sourceMap (BigFppfOver.toOver B S hS) j ≫ q.hom =
      Stacks.Groupoids.targetMap (BigFppfOver.toOver B S hS) j ≫ q.hom) :
    Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (BigFppfOver.toOver B S hS) j ⟶
      limit D :=
  Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B S hS) (BigFppfOver.toOver B S hS) j
    (limit D) q.hom hq

/-- If `q` factors through the presheaf quotient by a locally bijective map `θ`, then
`canonicalQuotientToLimit` is an isomorphism. -/
private theorem canonicalQuotientToLimit_isIso_of_locallyBijective
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    [HasLimit D] [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {U R : Over S} (j : Stacks.Groupoids.PreRelation R U)
    (hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U))
    (q : representedSheaf B S hS U hU ⟶ limit D)
    (hq : Stacks.Groupoids.sourceMap (BigFppfOver.toOver B S hS) j ≫ q.hom =
      Stacks.Groupoids.targetMap (BigFppfOver.toOver B S hS) j ≫ q.hom)
    (θ : Stacks.Groupoids.quotientPresheaf (BigFppfOver.toOver B S hS) j ⟶ (limit D).obj)
    (hθsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) θ)
    (hθinj : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) θ)
    (hfactor : Stacks.Groupoids.toQuotientPresheaf (BigFppfOver.toOver B S hS) j ≫ θ = q.hom) :
    IsIso (canonicalQuotientToLimit B S hS D j hU q hq) := by
  let J := BigFppfOver.topology B S hS
  let F := BigFppfOver.toOver B S hS
  let P := Stacks.Groupoids.quotientPresheaf F j
  let π := Stacks.Groupoids.toQuotientPresheaf F j
  let η := toSheafify J P
  let Q := Stacks.Groupoids.quotientSheaf J F j
  let c : Q ⟶ limit D := Stacks.Groupoids.quotientSheafDesc J F j
    (limit D) q.hom hq
  have hc : Stacks.Groupoids.toQuotientSheaf J F j ≫ c.hom = q.hom :=
    Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc J F j (limit D) q.hom hq
  have hηc : η ≫ c.hom = θ := (cancel_epi π).1 (hc.trans hfactor.symm)
  let : Presheaf.IsLocallySurjective J θ := hθsurj
  let : Presheaf.IsLocallyInjective J θ := hθinj
  obtain ⟨g, hg, hgunique⟩ :=
    Presheaf.existsUnique_hom_of_isLocallyBijective J θ η Q.property
  let inv : limit D ⟶ Q := ⟨g⟩
  let d : Q ⟶ Q := Stacks.Groupoids.quotientSheafDesc J F j Q
    (Stacks.Groupoids.toQuotientSheaf J F j)
    (Stacks.Groupoids.sourceMap_toQuotientSheaf J F j)
  have hcinvFac : Stacks.Groupoids.toQuotientSheaf J F j ≫ (c ≫ inv).hom =
      Stacks.Groupoids.toQuotientSheaf J F j := by
    change (Stacks.Groupoids.toQuotientSheaf J F j ≫ c.hom) ≫ g =
      Stacks.Groupoids.toQuotientSheaf J F j
    rw [hc, ← hfactor, Category.assoc, hg]
  have hcinvDesc : c ≫ inv = d :=
    Stacks.Groupoids.quotientSheafDesc_unique J F j Q
      (Stacks.Groupoids.toQuotientSheaf J F j)
      (Stacks.Groupoids.sourceMap_toQuotientSheaf J F j) (c ≫ inv) hcinvFac
  have hidDesc : 𝟙 Q = d :=
    Stacks.Groupoids.quotientSheafDesc_unique J F j Q
      (Stacks.Groupoids.toQuotientSheaf J F j)
      (Stacks.Groupoids.sourceMap_toQuotientSheaf J F j) (𝟙 Q) (by
        change Stacks.Groupoids.toQuotientSheaf J F j ≫ 𝟙 Q.obj = _
        exact Category.comp_id _)
  have hcinv : c.hom ≫ g = 𝟙 Q.obj := by
    simpa [inv] using congrArg (fun t : Q ⟶ Q => t.hom) (hcinvDesc.trans hidDesc.symm)
  obtain ⟨k, hk, hkunique⟩ :=
    Presheaf.existsUnique_hom_of_isLocallyBijective J θ θ (limit D).property
  have hgc : g ≫ c.hom = 𝟙 (limit D).obj :=
    (hkunique _ (by simp only [← Category.assoc, hg, hηc])).trans
      (hkunique _ (Category.comp_id θ)).symm
  let e : Q ≅ limit D :=
    { hom := c
      inv := inv
      hom_inv_id := Sheaf.hom_ext hcinv
      inv_hom_id := Sheaf.hom_ext hgc }
  exact e.isIso_hom

/-- If `q` is an epimorphism with kernel pair `j`, the map from the presheaf quotient induced
by `q` is locally bijective and factors `q`. -/
private theorem quotientToLimit_presheafFactor_isLocallyBijective
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    [HasLimit D] [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {U R : Over S} (j : Stacks.Groupoids.PreRelation R U)
    (hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U))
    (q : representedSheaf B S hS U hU ⟶ limit D)
    (hq : Stacks.Groupoids.sourceMap (BigFppfOver.toOver B S hS) j ≫ q.hom =
      Stacks.Groupoids.targetMap (BigFppfOver.toOver B S hS) j ≫ q.hom)
    (hqEpi : Epi q)
    (hkernel : IsPullback
      (Stacks.Groupoids.sourceMap (BigFppfOver.toOver B S hS) j)
      (Stacks.Groupoids.targetMap (BigFppfOver.toOver B S hS) j) q.hom q.hom) :
    let θ := coequalizer.desc q.hom hq
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) θ ∧
      Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) θ ∧
      Stacks.Groupoids.toQuotientPresheaf (BigFppfOver.toOver B S hS) j ≫ θ = q.hom := by
  let J := BigFppfOver.topology B S hS
  let F := BigFppfOver.toOver B S hS
  let P := Stacks.Groupoids.quotientPresheaf F j
  let π := Stacks.Groupoids.toQuotientPresheaf F j
  let θ := coequalizer.desc q.hom hq
  have hfactor : π ≫ θ = q.hom := coequalizer.π_desc q.hom hq
  have hθsurj : Presheaf.IsLocallySurjective J θ := by
    have hqsurj : Presheaf.IsLocallySurjective J q.hom :=
      (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff q).mp
        ((Sheaf.isLocallySurjective_iff_epi q).2 hqEpi)
    let : Presheaf.IsLocallySurjective J (π ≫ θ) := by rwa [hfactor]
    exact Presheaf.isLocallySurjective_of_isLocallySurjective J π θ
  have hθinj : Presheaf.IsLocallyInjective J θ := by
    apply Presheaf.isLocallyInjective_of_injective J θ
    intro X a b hab
    have hπepi : Epi (π.app X) := by
      let : Epi π := by
        dsimp [π]
        infer_instance
      exact (NatTrans.epi_iff_epi_app π).mp inferInstance X
    obtain ⟨x, hx⟩ := (epi_iff_surjective (π.app X)).mp hπepi a
    obtain ⟨y, hy⟩ := (epi_iff_surjective (π.app X)).mp hπepi b
    have hθcomp (z : (Stacks.Groupoids.points F U).obj X) :
        θ.app X (π.app X z) = q.hom.app X z :=
      congrArg (fun η => η.app X z) hfactor
    have hxy : q.hom.app X x = q.hom.app X y := by
      rw [← hθcomp, ← hθcomp, hx, hy, hab]
    let ix : yoneda.obj X.unop ⟶ Stacks.Groupoids.points F U := yonedaEquiv.symm x
    let iy : yoneda.obj X.unop ⟶ Stacks.Groupoids.points F U := yonedaEquiv.symm y
    have hqEval (z : (Stacks.Groupoids.points F U).obj X)
        (iz : yoneda.obj X.unop ⟶ Stacks.Groupoids.points F U)
        (hiz : yonedaEquiv iz = z) : yonedaEquiv (iz ≫ q.hom) = q.hom.app X z := by
      change q.hom.app X (iz.app X (𝟙 X.unop)) = q.hom.app X z
      rw [← yonedaEquiv_apply iz, hiz]
    have hcompat : ix ≫ q.hom = iy ≫ q.hom := by
      apply yonedaEquiv.injective
      rw [hqEval x ix (Equiv.apply_symm_apply yonedaEquiv x),
        hqEval y iy (Equiv.apply_symm_apply yonedaEquiv y)]
      exact hxy
    let r : yoneda.obj X.unop ⟶ Stacks.Groupoids.points F R :=
      PullbackCone.IsLimit.lift hkernel.isLimit ix iy hcompat
    have hr₁ : r ≫ Stacks.Groupoids.sourceMap F j = ix :=
      PullbackCone.IsLimit.lift_fst hkernel.isLimit ix iy hcompat
    have hr₂ : r ≫ Stacks.Groupoids.targetMap F j = iy :=
      PullbackCone.IsLimit.lift_snd hkernel.isLimit ix iy hcompat
    have hπmaps : ix ≫ π = iy ≫ π := by
      rw [← hr₁, ← hr₂, Category.assoc, Category.assoc,
        coequalizer.condition (Stacks.Groupoids.sourceMap F j) (Stacks.Groupoids.targetMap F j)]
    have hπxy : π.app X x = π.app X y := by
      have hxval : yonedaEquiv (ix ≫ π) = π.app X x := by
        simp [yonedaEquiv, ix]
      have hyval : yonedaEquiv (iy ≫ π) = π.app X y := by
        simp [yonedaEquiv, iy]
      exact hxval.symm.trans ((congrArg yonedaEquiv hπmaps).trans hyval)
    exact hx.symm.trans (hπxy.trans hy)
  exact ⟨hθsurj, hθinj, hfactor⟩

/-- A sheaf quotient by the kernel pair of an epimorphism is its target. -/
private theorem canonicalQuotientToLimit_isIso_of_epi_of_isPullback
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    [HasLimit D] [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {U R : Over S} (j : Stacks.Groupoids.PreRelation R U)
    (hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U))
    (q : representedSheaf B S hS U hU ⟶ limit D)
    (hqEpi : Epi q)
    (hkernel : IsPullback
      (Stacks.Groupoids.sourceMap (BigFppfOver.toOver B S hS) j)
      (Stacks.Groupoids.targetMap (BigFppfOver.toOver B S hS) j) q.hom q.hom) :
    IsIso (canonicalQuotientToLimit B S hS D j hU q hkernel.w) := by
  obtain ⟨hsurj, hinj, hfactor⟩ :=
    quotientToLimit_presheafFactor_isLocallyBijective B S hS D j hU q
      hkernel.w hqEpi hkernel
  exact canonicalQuotientToLimit_isIso_of_locallyBijective B S hS D j hU q
    hkernel.w (coequalizer.desc q.hom hkernel.w) hsurj hinj hfactor

private lemma isLocallySurjective_of_isPullback
    {C : Type*} [Category.{u} C] (J : GrothendieckTopology C)
    {F G T P : Cᵒᵖ ⥤ Type u} {f : F ⟶ G} {g : T ⟶ G}
    {p : P ⟶ F} {q : P ⟶ T} (hpb : IsPullback p q f g)
    (hf : Presheaf.IsLocallySurjective J f) :
    Presheaf.IsLocallySurjective J q := by
  refine ⟨fun {U} s => J.superset_covering ?_ (hf.imageSieve_mem (g.app _ s))⟩
  intro V i hi
  obtain ⟨x, hx⟩ := hi
  let mF : yoneda.obj V ⟶ F := yonedaEquiv.symm x
  let mT : yoneda.obj V ⟶ T := yonedaEquiv.symm (T.map i.op s)
  have hw : mF ≫ f = mT ≫ g := by
    apply yonedaEquiv.injective
    simpa [yonedaEquiv_comp, mF, mT] using
      hx.trans (NatTrans.naturality_apply g i.op s).symm
  refine ⟨yonedaEquiv (hpb.lift mF mT hw), ?_⟩
  rw [← yonedaEquiv_comp, hpb.lift_snd]
  exact yonedaEquiv.apply_symm_apply _

private lemma epi_of_isPullback
    {C : Type*} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type u)]
    {F G T P : Sheaf J (Type u)} {f : F ⟶ G} {g : T ⟶ G}
    {p : P ⟶ F} {q : P ⟶ T}
    (hpb : IsPullback p.hom q.hom f.hom g.hom) (hf : Epi f) : Epi q :=
  (Sheaf.isLocallySurjective_iff_epi q).1
    (isLocallySurjective_of_isPullback J hpb ((Sheaf.isLocallySurjective_iff_epi f).2 hf))

section
universe v w u' v' u'' v''

private theorem isPullback_map_limMap_of_isPullback
    {I C A : Type*} [Category* I] [Category* C] [Category* A]
    [HasPullbacks A] [HasLimitsOfShape I A]
    (Y : C ⥤ A) {R U : I ⥤ C} [HasLimit R] [HasLimit U]
    [PreservesLimit R Y] [PreservesLimit U Y]
    {D : I ⥤ A} (s t : R ⟶ U) (q : U ⋙ Y ⟶ D)
    (h : ∀ i, IsPullback (Y.map (s.app i)) (Y.map (t.app i))
      (q.app i) (q.app i)) :
    IsPullback (Y.map (limMap s)) (Y.map (limMap t))
      ((preservesLimitIso Y U).hom ≫ limMap q)
      ((preservesLimitIso Y U).hom ≫ limMap q) := by
  have hp : IsPullback (Functor.whiskerRight s Y) (Functor.whiskerRight t Y) q q :=
    IsPullback.iff_app.mpr h
  have hmap (u : R ⟶ U) : Y.map (limMap u) ≫ (preservesLimitIso Y U).hom =
      (preservesLimitIso Y R).hom ≫ limMap (Functor.whiskerRight u Y) := by
    refine limit.hom_ext fun i => ?_
    simp only [Category.assoc, preservesLimitIso_hom_π, limMap_π,
      Functor.whiskerRight_app, preservesLimitIso_hom_π_assoc, ← Y.map_comp]
  exact (hp.map lim).of_iso' (preservesLimitIso Y R)
    (preservesLimitIso Y U) (preservesLimitIso Y U) (Iso.refl _)
    (hmap s).symm (hmap t).symm (by simp) (by simp)

private theorem isPullback_limMap_of_isTerminal
    {I C : Type*} [Category* I] [Category* C]
    {E F : I ⥤ C} [HasLimit E] [HasLimit F]
    (α : E ⟶ F) (z : I) (hz : IsTerminal z)
    (hα : ∀ i, IsPullback (E.map (hz.from i)) (α.app i)
      (α.app z) (F.map (hz.from i))) :
    IsPullback (limit.π E z) (limMap α) (α.app z) (limit.π F z) := by
  have hw : limit.π E z ≫ α.app z = limMap α ≫ limit.π F z := by simp
  apply IsPullback.of_isLimit' ⟨hw⟩
  apply PullbackCone.IsLimit.mk _
    (fun s => limit.lift E {
      pt := s.pt
      π := {
        app := fun i => (hα i).lift s.fst (s.snd ≫ limit.π F i) (by
          simpa only [Category.assoc, limit.w] using s.condition)
        naturality := by
          intro i j f
          dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
          rw [Category.id_comp]
          apply (hα j).hom_ext
          · rw [IsPullback.lift_fst, Category.assoc, ← E.map_comp,
              hz.hom_ext (f ≫ hz.from j) (hz.from i), IsPullback.lift_fst]
          · rw [IsPullback.lift_snd, Category.assoc, α.naturality,
              IsPullback.lift_snd_assoc]
            simp } })
  · intro s
    rw [limit.lift_π]
    have hf := (hα z).lift_fst s.fst (s.snd ≫ limit.π F z) (by
      simpa only [Category.assoc, limit.w] using s.condition)
    simpa only [hz.hom_ext (hz.from z) (𝟙 z), E.map_id, Category.comp_id] using hf
  · exact fun s => limit.hom_ext fun i => by simp
  · intro s m hm₁ hm₂
    refine limit.hom_ext fun i => ?_
    rw [limit.lift_π]
    apply (hα i).hom_ext
    · simp only [Category.assoc, limit.w, IsPullback.lift_fst, hm₁]
    · rw [IsPullback.lift_snd, Category.assoc, ← limMap_π, ← Category.assoc, hm₂]

private theorem isEquivalenceRelation_limMap
    {I C : Type*} [Category* I] [Category* C] [HasPullbacks C]
    {E F : I ⥤ C} [HasLimit E] [HasLimit F]
    (s t : E ⟶ F) (h : ∀ i, IsEquivalenceRelation (s.app i) (t.app i)) :
    IsEquivalenceRelation (limMap s) (limMap t) := by
  classical
  let e i := (h i).nonempty_equivalenceRelation.some
  have hjoint : JointlyMono₂ (limMap s) (limMap t) := {
    right_cancellation := by
      intro T a b hs ht
      apply limit.hom_ext
      intro i
      apply (e i).right_cancellation
      · simpa using congrArg (· ≫ limit.π F i) hs
      · simpa using congrArg (· ≫ limit.π F i) ht }
  let r : F ⟶ E := {
    app := fun i => (e i).r
    naturality := by
      intro i j f
      apply (e j).right_cancellation
      · simp only [Category.assoc, s.naturality f, (e j).reflexivity₁,
          reassoc_of% (e i).reflexivity₁, Category.comp_id]
      · simp only [Category.assoc, t.naturality f, (e j).reflexivity₂,
          reassoc_of% (e i).reflexivity₂, Category.comp_id] }
  let σ : E ⟶ E := {
    app := fun i => (e i).s
    naturality := by
      intro i j f
      apply (e j).right_cancellation
      · simp only [Category.assoc, s.naturality f, (e j).symmetry₁,
          reassoc_of% (e i).symmetry₁, t.naturality f]
      · simp only [Category.assoc, t.naturality f, (e j).symmetry₂,
          reassoc_of% (e i).symmetry₂, s.naturality f] }
  let P := pullback (limMap t) (limMap s)
  let a i : P ⟶ E.obj i := pullback.fst (limMap t) (limMap s) ≫ limit.π E i
  let b i : P ⟶ E.obj i := pullback.snd (limMap t) (limMap s) ≫ limit.π E i
  have hab i : a i ≫ t.app i = b i ≫ s.app i := by
    have hc := congrArg (· ≫ limit.π F i)
      (pullback.condition (f := limMap t) (g := limMap s))
    simpa only [a, b, Category.assoc, limMap_π] using hc
  let m i : P ⟶ E.obj i :=
    PullbackCone.IsLimit.lift (e i).isLimit (a i) (b i) (hab i) ≫ (e i).t
  have hms i : m i ≫ s.app i = a i ≫ s.app i := by
    dsimp only [m]
    rw [Category.assoc, (e i).transitivity₁, ← Category.assoc,
      PullbackCone.IsLimit.lift_fst]
  have hmt i : m i ≫ t.app i = b i ≫ t.app i := by
    dsimp only [m]
    rw [Category.assoc, (e i).transitivity₂, ← Category.assoc,
      PullbackCone.IsLimit.lift_snd]
  let c : Cone E := {
    pt := P
    π := {
      app := m
      naturality := by
        intro i j f
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.id_comp]
        apply (e j).right_cancellation
        · simp only [Category.assoc]
          rw [s.naturality, ← Category.assoc (m i), hms, hms]
          simp only [a, Category.assoc, ← s.naturality f, limit.w_assoc]
        · simp only [Category.assoc]
          rw [t.naturality, ← Category.assoc (m i), hmt, hmt]
          simp only [b, Category.assoc, ← t.naturality f, limit.w_assoc] } }
  refine ⟨⟨{
    toJointlyMono₂ := hjoint
    r := limMap r
    reflexivity₁ := ?_
    reflexivity₂ := ?_
    s := limMap σ
    symmetry₁ := ?_
    symmetry₂ := ?_
    c := PullbackCone.mk (pullback.fst (limMap t) (limMap s))
      (pullback.snd (limMap t) (limMap s)) pullback.condition
    isLimit := (IsPullback.of_hasPullback (limMap t) (limMap s)).isLimit
    t := limit.lift E c
    transitivity₁ := ?_
    transitivity₂ := ?_ }⟩⟩
  · exact limit.hom_ext fun i => by simp [r]
  · exact limit.hom_ext fun i => by simp [r]
  · exact limit.hom_ext fun i => by simp [σ, (e i).symmetry₁]
  · exact limit.hom_ext fun i => by simp [σ, (e i).symmetry₂]
  · refine limit.hom_ext fun i => ?_
    change (limit.lift E c ≫ limMap s) ≫ limit.π F i =
      (pullback.fst (limMap t) (limMap s) ≫ limMap s) ≫ limit.π F i
    simp only [Category.assoc, limMap_π, limit.lift_π_assoc]
    simpa only [a, Category.assoc, limMap_π] using hms i
  · refine limit.hom_ext fun i => ?_
    change (limit.lift E c ≫ limMap t) ≫ limit.π F i =
      (pullback.snd (limMap t) (limMap s) ≫ limMap t) ≫ limit.π F i
    simp only [Category.assoc, limMap_π, limit.lift_π_assoc]
    simpa only [b, Category.assoc, limMap_π] using hmt i

private theorem exists_pullbackStages
    {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
    {I : Type u''} [Category.{v''} I] [HasPullbacks E]
    (Y : C ⥤ E) [Y.Full] [Y.Faithful] (D : I ⥤ E)
    (hD : ∀ {i j : I} (f : i ⟶ j), Y.relativelyRepresentable (D.map f))
    (i₀ : I) (V : C) (p : Y.obj V ⟶ D.obj i₀) :
    ∃ L : Over i₀ ⥤ C,
      Nonempty (L ⋙ Y ≅ Over.post D ⋙ Over.pullback p ⋙ Over.forget (Y.obj V)) := by
  let H := Over.post D ⋙ Over.pullback p ⋙ Over.forget (Y.obj V)
  have hH : ∀ x : Over i₀, Y.essImage (H.obj x) := fun x ↦
    ⟨(hD x.hom).pullback p, ⟨(hD x.hom).isPullback p |>.isoPullback⟩⟩
  exact ⟨Functor.essImage.liftFunctor H Y hH,
    ⟨Functor.essImage.liftFunctorCompIso H Y hH⟩⟩

/-- The transition maps of the base changed stages commute with the first projections. -/
private theorem pullbackStages_map_fst
    {E : Type u'} [Category.{v'} E] {I : Type u''} [Category.{v''} I]
    [HasPullbacks E] (D : I ⥤ E) (i₀ : I) {V : E} (p : V ⟶ D.obj i₀)
    {x y : Over i₀} (f : x ⟶ y) :
    (Over.post D ⋙ Over.pullback p ⋙ Over.forget V).map f ≫ pullback.fst (D.map y.hom) p =
      pullback.fst (D.map x.hom) p ≫ D.map f.left :=
  pullback.lift_fst _ _ _

/-- The transition maps of the base changed stages commute with the second projections. -/
private theorem pullbackStages_map_snd
    {E : Type u'} [Category.{v'} E] {I : Type u''} [Category.{v''} I]
    [HasPullbacks E] (D : I ⥤ E) (i₀ : I) {V : E} (p : V ⟶ D.obj i₀)
    {x y : Over i₀} (f : x ⟶ y) :
    (Over.post D ⋙ Over.pullback p ⋙ Over.forget V).map f ≫ pullback.snd (D.map y.hom) p =
      pullback.snd (D.map x.hom) p :=
  pullback.lift_snd _ _ _

private theorem isPullback_pullbackStages_map
    {E : Type u'} [Category.{v'} E] {I : Type u''} [Category.{v''} I]
    [HasPullbacks E] (D : I ⥤ E) (i₀ : I) {V : E} (p : V ⟶ D.obj i₀)
    {x y : Over i₀} (f : x ⟶ y) :
    let H := Over.post D ⋙ Over.pullback p ⋙ Over.forget V
    IsPullback (H.map f) (pullback.fst (D.map x.hom) p)
      (pullback.fst (D.map y.hom) p) (D.map f.left) := by
  let H := Over.post D ⋙ Over.pullback p ⋙ Over.forget V
  have hw : D.map f.left ≫ D.map y.hom = D.map x.hom := by
    rw [← D.map_comp, Over.w]
  have hfst := pullbackStages_map_fst D i₀ p f
  have hsnd := pullbackStages_map_snd D i₀ p f
  refine ((IsPullback.of_hasPullback (D.map y.hom) p).flip.paste_horiz_iff hfst).mp ?_
  refine (IsPullback.of_hasPullback (D.map x.hom) p).flip.of_iso'
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).trans (hsnd.symm.trans (Category.comp_id _).symm)
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · simp
  · exact (Category.id_comp _).trans (hw.symm.trans (Category.comp_id _).symm)

private theorem exists_pullbackStages_property
    {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
    {I : Type u''} [Category.{v''} I] [HasPullbacks E]
    (Y : C ⥤ E) [Y.Full] [Y.Faithful] (D : I ⥤ E)
    (P : MorphismProperty C)
    (hD : ∀ {i j : I} (f : i ⟶ j), P.relative Y (D.map f))
    (i₀ : I) (V : C) (p : Y.obj V ⟶ D.obj i₀) :
    ∃ L : Over i₀ ⥤ C,
      Nonempty (L ⋙ Y ≅ Over.post D ⋙ Over.pullback p ⋙ Over.forget (Y.obj V)) ∧
      ∀ {x y : Over i₀} (f : x ⟶ y), P (L.map f) := by
  obtain ⟨L, ⟨e⟩⟩ := exists_pullbackStages Y D (fun f => (hD f).rep) i₀ V p
  refine ⟨L, ⟨e⟩, fun {x y} f => ?_⟩
  apply (hD f.left).property ((e.app y).hom ≫ pullback.fst (D.map y.hom) p)
    ((e.app x).hom ≫ pullback.fst (D.map x.hom) p) (L.map f)
  exact (isPullback_pullbackStages_map D i₀ p f).flip.of_iso'
    (e.app x) (Iso.refl _) (e.app y) (Iso.refl _)
    (by simp) (e.hom.naturality f).symm (by simp) (by simp)

/-- For a fully faithful functor `F : C ⥤ E`, restricting the Yoneda embedding of `E` along `F`
recovers the Yoneda embedding of `C`: `Hom_E(F -, F X) ≅ Hom_C(-, X)`, naturally in `X`. -/
noncomputable def restrictedYonedaIso
    {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v} E]
    (F : C ⥤ E) [F.Full] [F.Faithful] :
    F ⋙ yoneda ⋙ (Functor.whiskeringLeft Cᵒᵖ Eᵒᵖ (Type v)).obj F.op ≅ yoneda :=
  NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun T => (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.toIso)
    (fun f => by
      ext g
      apply F.map_injective
      simp)) (fun f => by
        ext T g
        apply F.map_injective
        simp)

end

/-- A cartesian inverse system of étale equivalence relations has an étale
limit relation. -/
private theorem isEtaleEquivalenceRelation_limMap
    {I : Type*} [Category* I]
    {E F : I ⥤ Over S} [HasLimit E] [HasLimit F]
    (s t : E ⟶ F) (z : I) (hz : IsTerminal z)
    (hs : ∀ i, IsPullback (E.map (hz.from i)) (s.app i)
      (s.app z) (F.map (hz.from i)))
    (ht : ∀ i, IsPullback (E.map (hz.from i)) (t.app i)
      (t.app z) (F.map (hz.from i)))
    (hrel : ∀ i, IsEquivalenceRelation (s.app i) (t.app i))
    (hsEtale : Etale (s.app z).left) (htEtale : Etale (t.app z).left) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (prod.lift (limMap s) (limMap t)) := by
  have hs' : Etale (limMap s).left := MorphismProperty.of_isPullback
    ((isPullback_limMap_of_isTerminal s z hz hs).map (Over.forget S)) hsEtale
  have ht' : Etale (limMap t).left := MorphismProperty.of_isPullback
    ((isPullback_limMap_of_isTerminal t z hz ht).map (Over.forget S)) htEtale
  exact {
    isEquivalenceRelation := by
      simpa only [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
        prod.lift_fst, prod.lift_snd] using isEquivalenceRelation_limMap s t hrel
    etale_source := by
      simpa only [Stacks.Groupoids.PreRelation.source, prod.lift_snd] using ht'
    etale_target := by
      simpa only [Stacks.Groupoids.PreRelation.target, prod.lift_fst] using hs' }

/-- Affine transitions are relatively representable and affine on site charts. -/
private theorem affine_transition_properties
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i).obj)
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f).hom)
    {i j : I} (f : i ⟶ j) :
    yoneda.relativelyRepresentable (D.map f).hom ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (D.map f).hom := by
  have h := ((AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.map f).hom
      (hD i) (hD j)).out 2 1).mp (hAffine f)
  exact ⟨h.1, h.2⟩

private theorem affine_transition_isAffineHom
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i).obj)
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f).hom)
    {i j : I} (f : i ⟶ j) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (D.map f).hom :=
  (affine_transition_properties B S hS D hD hAffine f).2

/-- The stagewise base changes of a chart of one stage form an inverse system of objects of the
site with affine transitions, whose limit exists in schemes over `S` and is preserved by
`Over.forget S`.

Let `D` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms, let `i₀` be a stage, and let `p : yoneda V ⟶ D i₀` be a point of that stage valued in
an object `V` of the site. Base changing the stages above `i₀` along `p` gives an inverse system
indexed by `Over i₀`, and affineness of the transition morphisms makes every member of it
representable by an object of the site (Stacks 03WF). There is a system `E` of representing
objects with:

* `Nonempty (E ⋙ yoneda ≅ …)`, the identification of its image in presheaves with the system of
  base changes;
* affineness of every transition morphism of the underlying schemes;
* `HasLimit (E ⋙ BigFppfOver.toOver B S hS)`, a limit of the system in schemes over `S`;
* `PreservesLimit (E ⋙ BigFppfOver.toOver B S hS) (Over.forget S)`, so the underlying schemes of
  the limit cone form a limiting cone too.

Unlike `AlgebraicGeometry.Space.AffineChartSystem`, whose chart and stages are affine objects of
the site and whose limit `AlgebraicGeometry.Space.AffineChartSystem.limitBridge` is formed inside
the site, here `V` is an arbitrary object of the site, the limit is formed in `Over S` by
`AlgebraicGeometry.hasLimit_of_isCofiltered_of_isAffineHom`, and no cardinality hypothesis on `I`
is needed; the limit is not placed back in the size-bounded site. -/
theorem exists_pullbackStages_of_affine_transition
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i).obj)
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f).hom)
    (i₀ : I) (V : BigFppfOver B S hS) (p : yoneda.obj V ⟶ (D.obj i₀).obj) :
    ∃ E : Over i₀ ⥤ BigFppfOver B S hS,
      Nonempty (E ⋙ yoneda ≅
        Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
          Over.pullback p ⋙ Over.forget (yoneda.obj V)) ∧
      (∀ {x y : Over i₀} (f : x ⟶ y),
        _root_.AlgebraicGeometry.IsAffineHom
          ((E ⋙ BigFppfOver.toOver B S hS).map f).left) ∧
      HasLimit (E ⋙ BigFppfOver.toOver B S hS) ∧
      PreservesLimit (E ⋙ BigFppfOver.toOver B S hS) (Over.forget S) := by
  let P : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  obtain ⟨E, e, hE⟩ := exists_pullbackStages_property yoneda
    (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) P
    (fun f => affine_transition_isAffineHom B S hS D hD hAffine f) i₀ V p
  let L := E ⋙ BigFppfOver.toOver B S hS
  have hL : ∀ {x y : Over i₀} (f : x ⟶ y),
      _root_.AlgebraicGeometry.IsAffineHom (L.map f).left := hE
  let : ∀ {x y : Over i₀} (f : x ⟶ y),
      _root_.AlgebraicGeometry.IsAffineHom ((L ⋙ Over.forget S).map f) := hL
  let : HasLimit (L ⋙ Over.forget S) :=
    AlgebraicGeometry.hasLimit_of_isCofiltered_of_isAffineHom (L ⋙ Over.forget S)
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  exact ⟨E, e, hL, hasLimit_of_created L (Over.forget S), inferInstance⟩

/-- The stagewise base changes of a chart of one stage form an inverse system of objects of the
site with affine transitions whose limit exists in schemes over `S`: the first three conjuncts of
`AlgebraicGeometry.Space.exists_pullbackStages_of_affine_transition`. -/
private theorem exists_affine_pullbackStages
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i).obj)
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f).hom)
    (i₀ : I) (V : BigFppfOver B S hS) (p : yoneda.obj V ⟶ (D.obj i₀).obj) :
    ∃ E : Over i₀ ⥤ BigFppfOver B S hS,
      Nonempty (E ⋙ yoneda ≅
        Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
          Over.pullback p ⋙ Over.forget (yoneda.obj V)) ∧
      (∀ {x y : Over i₀} (f : x ⟶ y),
        _root_.AlgebraicGeometry.IsAffineHom
          ((E ⋙ BigFppfOver.toOver B S hS).map f).left) ∧
      HasLimit (E ⋙ BigFppfOver.toOver B S hS) := by
  obtain ⟨E, e, hL, hlim, -⟩ :=
    exists_pullbackStages_of_affine_transition B S hS D hD hAffine i₀ V p
  exact ⟨E, e, hL, hlim⟩

/-- A functor of points is a sheaf when it identifies with a pullback of sheaves. -/
private theorem isSheaf_points_of_iso_pullback
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u)) [HasLimit D]
    (i₀ : I) (V : BigFppfOver B S hS) (p : yoneda.obj V ⟶ (D.obj i₀).obj)
    (U : Over S)
    (e : Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U ≅
      pullback (limit.π D i₀).hom p) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U) := by
  let V' : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨yoneda.obj V, (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V).isSheaf⟩
  let p' : V' ⟶ D.obj i₀ := ⟨p⟩
  let P := pullback (limit.π D i₀) p'
  let eP : P.obj ≅ pullback (limit.π D i₀).hom p :=
    ((IsPullback.of_hasPullback (limit.π D i₀) p').map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))).isoPullback
  exact (Presheaf.isSheaf_of_iso_iff (e ≪≫ eP.symm)).mpr P.property

/-- The map `Z ×_X T ⟶ Z ×_X W` induced by a morphism `g : T ⟶ W` over `X`. -/
private noncomputable def baseChangedChartMap
    {C : Type*} [Category* C] [HasPullbacks C]
    {Z X W T : C} (f : Z ⟶ X) (p : W ⟶ X) (pT : T ⟶ X)
    (g : T ⟶ W) (hg : g ≫ p = pT) :
    pullback f pT ⟶ pullback f p :=
  pullback.lift (pullback.fst f pT) (pullback.snd f pT ≫ g)
    (by rw [Category.assoc, hg]; exact pullback.condition)

@[reassoc]
private theorem baseChangedChartMap_fst
    {C : Type*} [Category* C] [HasPullbacks C]
    {Z X W T : C} (f : Z ⟶ X) (p : W ⟶ X) (pT : T ⟶ X)
    (g : T ⟶ W) (hg : g ≫ p = pT) :
    baseChangedChartMap f p pT g hg ≫ pullback.fst f p = pullback.fst f pT :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem baseChangedChartMap_snd
    {C : Type*} [Category* C] [HasPullbacks C]
    {Z X W T : C} (f : Z ⟶ X) (p : W ⟶ X) (pT : T ⟶ X)
    (g : T ⟶ W) (hg : g ≫ p = pT) :
    baseChangedChartMap f p pT g hg ≫ pullback.snd f p = pullback.snd f pT ≫ g :=
  pullback.lift_snd _ _ _

/-- Cancelling an inverse against its isomorphism in the middle of a composite. -/
private theorem assoc_inv_hom_cancel {C : Type*} [Category* C] {X Y P Q W : C}
    (a : X ⟶ Y) (ε : P ≅ Q) (s : Y ⟶ Q) (b : Q ⟶ W) :
    (a ≫ s ≫ ε.inv) ≫ ε.hom ≫ b = a ≫ s ≫ b := by
  simp

/-- The natural map from the stagewise pullbacks along `p'` to those along `p` induced by a
morphism `g` with `g ≫ p = p'`. -/
private noncomputable def baseChangedChartNat
    {C : Type*} [Category* C] [HasPullbacks C] {I : Type*} [Category* I]
    (D : I ⥤ C) (i₀ : I) {V V' : C} (p : V ⟶ D.obj i₀) (p' : V' ⟶ D.obj i₀)
    (g : V' ⟶ V) (hg : g ≫ p = p') :
    Over.post (X := i₀) D ⋙ Over.pullback p' ⋙ Over.forget V' ⟶
      Over.post (X := i₀) D ⋙ Over.pullback p ⋙ Over.forget V where
  app x := baseChangedChartMap (D.map x.hom) p p' g hg
  naturality x y m := by
    let a : pullback (D.map x.hom) p ⟶ pullback (D.map y.hom) p :=
      (Over.post (X := i₀) D ⋙ Over.pullback p ⋙ Over.forget V).map m
    let a' : pullback (D.map x.hom) p' ⟶ pullback (D.map y.hom) p' :=
      (Over.post (X := i₀) D ⋙ Over.pullback p' ⋙ Over.forget V').map m
    have hafst : a ≫ pullback.fst (D.map y.hom) p =
        pullback.fst (D.map x.hom) p ≫ D.map m.left := pullbackStages_map_fst D i₀ p m
    have hasnd : a ≫ pullback.snd (D.map y.hom) p = pullback.snd (D.map x.hom) p :=
      pullbackStages_map_snd D i₀ p m
    have ha'fst : a' ≫ pullback.fst (D.map y.hom) p' =
        pullback.fst (D.map x.hom) p' ≫ D.map m.left := pullbackStages_map_fst D i₀ p' m
    have ha'snd : a' ≫ pullback.snd (D.map y.hom) p' = pullback.snd (D.map x.hom) p' :=
      pullbackStages_map_snd D i₀ p' m
    have hnat : a' ≫ baseChangedChartMap (D.map y.hom) p p' g hg =
        baseChangedChartMap (D.map x.hom) p p' g hg ≫ a := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, baseChangedChartMap_fst, ha'fst, Category.assoc, hafst,
          baseChangedChartMap_fst_assoc]
      · rw [Category.assoc, baseChangedChartMap_snd, ← Category.assoc, ha'snd,
          Category.assoc, hasnd, baseChangedChartMap_snd]
    exact hnat

private noncomputable def pullbackStagesMap
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    (i₀ : I) (V V' : BigFppfOver B S hS)
    (p : yoneda.obj V ⟶ (D.obj i₀).obj)
    (p' : yoneda.obj V' ⟶ (D.obj i₀).obj)
    (g : V' ⟶ V) (hg : yoneda.map g ≫ p = p')
    (E E' : Over i₀ ⥤ BigFppfOver B S hS)
    (e : E ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback p ⋙ Over.forget (yoneda.obj V))
    (e' : E' ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback p' ⋙ Over.forget (yoneda.obj V')) : E' ⟶ E :=
  ((Functor.FullyFaithful.ofFullyFaithful yoneda).whiskeringRight (Over i₀)).preimage
    (e'.hom ≫ baseChangedChartNat
        (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) i₀ p p'
        (yoneda.map g) hg ≫
      e.inv)

private theorem pullbackStagesMap_yonedaMap
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    (i₀ : I) (V V' : BigFppfOver B S hS)
    (p : yoneda.obj V ⟶ (D.obj i₀).obj)
    (p' : yoneda.obj V' ⟶ (D.obj i₀).obj)
    (g : V' ⟶ V) (hg : yoneda.map g ≫ p = p')
    (E E' : Over i₀ ⥤ BigFppfOver B S hS)
    (e : E ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback p ⋙ Over.forget (yoneda.obj V))
    (e' : E' ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback p' ⋙ Over.forget (yoneda.obj V'))
    (x : Over i₀) :
    yoneda.map ((pullbackStagesMap B S hS D i₀ V V' p p' g hg E E' e e').app x) =
      (e'.app x).hom ≫
        baseChangedChartMap
          ((D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map x.hom) p p'
          (yoneda.map g) hg ≫ (e.app x).inv :=
  congrArg (fun θ => NatTrans.app θ x)
    (((Functor.FullyFaithful.ofFullyFaithful yoneda).whiskeringRight (Over i₀)).map_preimage
      (e'.hom ≫ baseChangedChartNat
          (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) i₀ p p'
          (yoneda.map g) hg ≫
        e.inv))

private instance schemeCutoff_hasFiniteLimits : HasFiniteLimits B.Schemes :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

private instance bigFppfOver_hasFiniteLimits : HasFiniteLimits (BigFppfOver B S hS) :=
  inferInstance

/-- The kernel pair of an étale chart `p : yoneda W ⟶ X` of an algebraic space is represented
by an object `T` of the site, with étale projections `s t : T ⟶ W`. -/
private theorem exists_chartKernelPair
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ X)
    (hp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) p) :
    ∃ (T : BigFppfOver B S hS) (s t : T ⟶ W),
      IsPullback (yoneda.map s) (yoneda.map t) p p ∧
      Etale ((BigFppfOver.toOver B S hS).map s).left ∧
      Etale ((BigFppfOver.toOver B S hS).map t).left := by
  let hrep := hX.diagonal_representable.of_diag p
  let T := hrep.pullback p
  let s := yoneda.preimage (hrep.fst p)
  let t := hrep.snd p
  have hs : yoneda.map s = hrep.fst p := yoneda.map_preimage _
  have hpb : IsPullback (yoneda.map s) (yoneda.map t) p p := hs ▸ hrep.isPullback p
  exact ⟨T, s, t, hpb, hp.property p (yoneda.map t) s hpb.flip,
    hp.property p (yoneda.map s) t hpb⟩

private instance pointsFunctor_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (BigFppfOver.toOver B S hS) := by
  let : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  let : PreservesFiniteLimits (BigFppfOver.toOver B S hS) :=
    PreservesFiniteLimits.overPost (F := B.inclusion) (X := B.obj hS)
  infer_instance

/-- The map `pullbackStagesMap` is the map `baseChangedChartMap` transported along `e` and `e'`. -/
private theorem pullbackStagesMap_comm
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    (i₀ : I) (V V' : BigFppfOver B S hS)
    (p : yoneda.obj V ⟶ (D.obj i₀).obj)
    (p' : yoneda.obj V' ⟶ (D.obj i₀).obj)
    (g : V' ⟶ V) (hg : yoneda.map g ≫ p = p')
    (E E' : Over i₀ ⥤ BigFppfOver B S hS)
    (e : E ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback p ⋙ Over.forget (yoneda.obj V))
    (e' : E' ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback p' ⋙ Over.forget (yoneda.obj V'))
    (x : Over i₀) :
    (e'.app x).hom ≫ baseChangedChartMap
        ((D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map x.hom) p p'
        (yoneda.map g) hg =
      yoneda.map ((pullbackStagesMap B S hS D i₀ V V' p p' g hg E E' e e').app x) ≫
        (e.app x).hom := by
  rw [pullbackStagesMap_yonedaMap]
  exact (congrArg _ (Category.comp_id _)).symm.trans
    ((assoc_inv_hom_cancel _ (e.app x) _ (𝟙 _)).symm.trans (congrArg _ (Category.comp_id _)))

private theorem isPullback_baseChangedChartMap
    {C : Type*} [Category* C] [HasPullbacks C]
    {Z X W T : C} (f : Z ⟶ X) (p : W ⟶ X) (pT : T ⟶ X)
    (g : T ⟶ W) (hg : g ≫ p = pT) :
    IsPullback (pullback.snd f pT)
      (baseChangedChartMap f p pT g hg) g (pullback.snd f p) := by
  let a := baseChangedChartMap f p pT g hg
  have hw : pullback.snd f pT ≫ g = a ≫ pullback.snd f p := (pullback.lift_snd _ _ _).symm
  apply IsPullback.of_isLimit' ⟨hw⟩
  let lift (c : PullbackCone g (pullback.snd f p)) : c.pt ⟶ pullback f pT :=
    pullback.lift (c.snd ≫ pullback.fst f p) c.fst (by
      calc
        _ = (c.snd ≫ pullback.snd f p) ≫ p := by
          simp only [Category.assoc, pullback.condition]
        _ = (c.fst ≫ g) ≫ p := by rw [c.condition]
        _ = c.fst ≫ pT := by rw [Category.assoc, hg])
  refine PullbackCone.IsLimit.mk hw lift ?_ ?_ ?_
  · exact fun c => pullback.lift_snd _ _ _
  · intro c
    apply pullback.hom_ext
    · simp only [lift, a, baseChangedChartMap, Category.assoc,
        pullback.lift_fst]
    · simp only [lift, a, baseChangedChartMap, Category.assoc,
        pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd]
      exact c.condition
  · intro c m hm₁ hm₂
    apply pullback.hom_ext
    · have hh := congrArg (· ≫ pullback.fst f p) hm₂
      simpa only [a, baseChangedChartMap, lift, Category.assoc,
        pullback.lift_fst] using hh
    · simpa only [lift, pullback.lift_snd] using hm₁

private theorem isPullback_baseChangedKernelPair
    {C : Type*} [Category* C] [HasPullbacks C]
    {Z X W T : C} (f : Z ⟶ X) (p : W ⟶ X)
    (s t : T ⟶ W) (h : IsPullback s t p p) :
    IsPullback
      (baseChangedChartMap f p (t ≫ p) s h.w)
      (baseChangedChartMap f p (t ≫ p) t rfl)
      (pullback.fst f p) (pullback.fst f p) := by
  let a := baseChangedChartMap f p (t ≫ p) s h.w
  let b := baseChangedChartMap f p (t ≫ p) t rfl
  have hw : a ≫ pullback.fst f p = b ≫ pullback.fst f p := by
    simp only [a, b, baseChangedChartMap, pullback.lift_fst]
  apply IsPullback.of_isLimit' ⟨hw⟩
  let lift (c : PullbackCone (pullback.fst f p) (pullback.fst f p)) :
      c.pt ⟶ pullback f (t ≫ p) := by
    have hc : (c.fst ≫ pullback.snd f p) ≫ p =
        (c.snd ≫ pullback.snd f p) ≫ p := by
      calc
        _ = (c.fst ≫ pullback.fst f p) ≫ f := by
          simp only [Category.assoc, pullback.condition]
        _ = (c.snd ≫ pullback.fst f p) ≫ f := by rw [c.condition]
        _ = _ := by simp only [Category.assoc, pullback.condition]
    let r := h.lift (c.fst ≫ pullback.snd f p)
      (c.snd ≫ pullback.snd f p) hc
    refine pullback.lift (c.fst ≫ pullback.fst f p) r ?_
    calc
      _ = (c.snd ≫ pullback.fst f p) ≫ f := by rw [c.condition]
      _ = (c.snd ≫ pullback.snd f p) ≫ p := by
        simp only [Category.assoc, pullback.condition]
      _ = (r ≫ t) ≫ p := by rw [h.lift_snd]
      _ = r ≫ (t ≫ p) := by simp only [Category.assoc]
  refine PullbackCone.IsLimit.mk hw lift ?_ ?_ ?_
  · intro c
    apply pullback.hom_ext
    · simp only [lift, a, baseChangedChartMap, Category.assoc,
        pullback.lift_fst]
    · simp only [lift, a, baseChangedChartMap, Category.assoc,
        pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd]
      exact h.lift_fst _ _ _
  · intro c
    apply pullback.hom_ext
    · simp only [lift, b, baseChangedChartMap, Category.assoc,
        pullback.lift_fst]
      exact c.condition
    · simp only [lift, b, baseChangedChartMap, Category.assoc,
        pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd]
      exact h.lift_snd _ _ _
  · intro c m hm₁ hm₂
    apply pullback.hom_ext
    · have hh := congrArg (· ≫ pullback.fst f p) hm₁
      simpa only [a, baseChangedChartMap, lift, Category.assoc, pullback.lift_fst]
        using hh
    · apply h.hom_ext
      · have hh := congrArg (· ≫ pullback.snd f p) hm₁
        simpa only [a, baseChangedChartMap, lift, Category.assoc, pullback.lift_snd,
          h.lift_fst] using hh
      · have hh := congrArg (· ≫ pullback.snd f p) hm₂
        simpa only [b, baseChangedChartMap, lift, Category.assoc, pullback.lift_snd,
          h.lift_snd] using hh

private theorem isPullback_pullbackStages
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    (i₀ : I) (V T : BigFppfOver B S hS)
    (p : yoneda.obj V ⟶ (D.obj i₀).obj)
    (s t : T ⟶ V) (hT : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (E K : Over i₀ ⥤ BigFppfOver B S hS)
    (eE : E ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback p ⋙ Over.forget (yoneda.obj V))
    (eK : K ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback (yoneda.map t ≫ p) ⋙ Over.forget (yoneda.obj T))
    (x : Over i₀) :
    let σ := pullbackStagesMap B S hS D i₀ V T p (yoneda.map t ≫ p)
      s hT.w E K eE eK
    let τ := pullbackStagesMap B S hS D i₀ V T p (yoneda.map t ≫ p)
      t rfl E K eE eK
    let qx := (eE.app x).hom ≫ pullback.fst
      ((D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map x.hom) p
    IsPullback (yoneda.map (σ.app x)) (yoneda.map (τ.app x)) qx qx := by
  let DP := D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)
  let σ := pullbackStagesMap B S hS D i₀ V T p (yoneda.map t ≫ p)
    s hT.w E K eE eK
  let τ := pullbackStagesMap B S hS D i₀ V T p (yoneda.map t ≫ p)
    t rfl E K eE eK
  let qx := (eE.app x).hom ≫ pullback.fst (DP.map x.hom) p
  change IsPullback (yoneda.map (σ.app x)) (yoneda.map (τ.app x)) qx qx
  have hbase := isPullback_baseChangedKernelPair
    (DP.map x.hom) p (yoneda.map s) (yoneda.map t) hT
  apply hbase.of_iso' (eK.app x) (eE.app x) (eE.app x) (Iso.refl _)
  · exact pullbackStagesMap_comm B S hS D i₀ V T p _ _ _ E K eE eK x
  · exact pullbackStagesMap_comm B S hS D i₀ V T p _ _ _ E K eE eK x
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm

private theorem isPullback_pullbackStagesMap
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    (i₀ : I) (V T : BigFppfOver B S hS)
    (p : yoneda.obj V ⟶ (D.obj i₀).obj)
    (pT : yoneda.obj T ⟶ (D.obj i₀).obj)
    (g : T ⟶ V) (hg : yoneda.map g ≫ p = pT)
    (E K : Over i₀ ⥤ BigFppfOver B S hS)
    (eE : E ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback p ⋙ Over.forget (yoneda.obj V))
    (eK : K ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback pT ⋙ Over.forget (yoneda.obj T))
    {x y : Over i₀} (f : x ⟶ y) :
    let σ := pullbackStagesMap B S hS D i₀ V T p pT g hg E K eE eK
    IsPullback (yoneda.map (K.map f)) (yoneda.map (σ.app x))
      (yoneda.map (σ.app y)) (yoneda.map (E.map f)) := by
  let DP := D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)
  let σ := pullbackStagesMap B S hS D i₀ V T p pT g hg E K eE eK
  let qE (z : Over i₀) :=
    (eE.app z).hom ≫ pullback.fst (DP.map z.hom) p
  let qK (z : Over i₀) :=
    (eK.app z).hom ≫ pullback.fst (DP.map z.hom) pT
  have hbase {W : BigFppfOver B S hS} (r : yoneda.obj W ⟶ (D.obj i₀).obj)
      (L : Over i₀ ⥤ BigFppfOver B S hS)
      (e : L ⋙ yoneda ≅ Over.post DP ⋙ Over.pullback r ⋙ Over.forget (yoneda.obj W)) :
      IsPullback (yoneda.map (L.map f)) ((e.app x).hom ≫ pullback.fst (DP.map x.hom) r)
        ((e.app y).hom ≫ pullback.fst (DP.map y.hom) r) (DP.map f.left) := by
    apply (isPullback_pullbackStages_map DP i₀ r f).of_iso'
      (e.app x) (e.app y) (Iso.refl _) (Iso.refl _)
    · exact (e.hom.naturality f).symm
    · rfl
    · rfl
    · simp
  have hE : IsPullback (yoneda.map (E.map f)) (qE x) (qE y) (DP.map f.left) := hbase p E eE
  have hK : IsPullback (yoneda.map (K.map f)) (qK x) (qK y) (DP.map f.left) := hbase pT K eK
  have hσ (z : Over i₀) : yoneda.map (σ.app z) ≫ qE z = qK z := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pullback.fst (DP.map z.hom) p)
        (pullbackStagesMap_comm B S hS D i₀ V T p pT g hg E K eE eK z).symm).trans
        ((Category.assoc _ _ _).trans (congrArg _ (baseChangedChartMap_fst _ _ _ _ _))))
  have hn : yoneda.map (K.map f) ≫ yoneda.map (σ.app y) =
      yoneda.map (σ.app x) ≫ yoneda.map (E.map f) := by
    simpa only [← Functor.map_comp] using congrArg yoneda.map (σ.naturality f)
  have houter : IsPullback (yoneda.map (σ.app x) ≫ qE x)
      (yoneda.map (K.map f)) (DP.map f.left)
      (yoneda.map (σ.app y) ≫ qE y) := by
    simpa only [hσ] using hK.flip
  exact (houter.of_right hn.symm hE.flip).flip

private theorem etale_pullbackStagesMap
    {I : Type u} [Category.{u} I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    (i₀ : I) (V T : BigFppfOver B S hS)
    (p : yoneda.obj V ⟶ (D.obj i₀).obj)
    (pT : yoneda.obj T ⟶ (D.obj i₀).obj)
    (g : T ⟶ V) (hg : yoneda.map g ≫ p = pT)
    (E K : Over i₀ ⥤ BigFppfOver B S hS)
    (eE : E ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback p ⋙ Over.forget (yoneda.obj V))
    (eK : K ⋙ yoneda ≅
      Over.post (D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) ⋙
        Over.pullback pT ⋙ Over.forget (yoneda.obj T))
    (x : Over i₀)
    (hetale : Etale ((BigFppfOver.toOver B S hS).map g).left) :
    Etale ((BigFppfOver.toOver B S hS).map
      ((pullbackStagesMap B S hS D i₀ V T p pT g hg E K eE eK).app x)).left := by
  let DP := D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)
  let σ := pullbackStagesMap B S hS D i₀ V T p pT g hg E K eE eK
  let u : E.obj x ⟶ V := yoneda.preimage
    ((eE.app x).hom ≫ pullback.snd (DP.map x.hom) p)
  let v : K.obj x ⟶ T := yoneda.preimage
    ((eK.app x).hom ≫ pullback.snd (DP.map x.hom) pT)
  have hu : yoneda.map u = (eE.app x).hom ≫
      pullback.snd (DP.map x.hom) p := yoneda.map_preimage _
  have hv : yoneda.map v = (eK.app x).hom ≫
      pullback.snd (DP.map x.hom) pT := yoneda.map_preimage _
  have hbase := isPullback_baseChangedChartMap
    (DP.map x.hom) p pT (yoneda.map g) hg
  have hpresheaf : IsPullback (yoneda.map v) (yoneda.map (σ.app x))
      (yoneda.map g) (yoneda.map u) := by
    apply hbase.of_iso' (eK.app x) (Iso.refl _) (eE.app x) (Iso.refl _)
    · exact hv.symm.trans (Category.comp_id _).symm
    · exact pullbackStagesMap_comm B S hS D i₀ V T p _ _ _ E K eE eK x
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact hu.symm.trans (Category.comp_id _).symm
  have hsite := IsPullback.of_map yoneda
    (yoneda.map_injective hpresheaf.w) hpresheaf
  exact MorphismProperty.of_isPullback ((hsite.map (BigFppfOver.toOver B S hS)).map
    (Over.forget S)) hetale

/-- The functor `BigFppfOver.toOver` is full: it is `Over.post` of the inclusion of the site's
schemes, which is fully faithful. -/
local instance : (BigFppfOver.toOver B S hS).Full :=
  inferInstanceAs ((Over.post (X := B.obj hS) B.inclusion).Full)

/-- The functor `BigFppfOver.toOver` is faithful: it is `Over.post` of the inclusion of the site's
schemes, which is fully faithful. -/
local instance : (BigFppfOver.toOver B S hS).Faithful :=
  inferInstanceAs ((Over.post (X := B.obj hS) B.inclusion).Faithful)

/-- A chart at one stage gives a scheme atlas for the inverse limit together
with its represented, étale kernel pair. -/
private theorem exists_limit_chart_relation
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u)) [HasLimit D]
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i).obj)
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f).hom)
    (i₀ : I) (V : BigFppfOver B S hS)
    (p : yoneda.obj V ⟶ (D.obj i₀).obj)
    (hp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) p) :
    ∃ (U : Over S)
      (hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
        (Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U))
      (R : Over S) (j : Stacks.Groupoids.PreRelation R U)
      (eU : Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U ≅
        pullback (limit.π D i₀).hom p)
      (q : representedSheaf B S hS U hU ⟶ limit D)
      (f : U ⟶ (BigFppfOver.toOver B S hS).obj V),
      q.hom = eU.hom ≫ pullback.fst (limit.π D i₀).hom p ∧
      eU.hom ≫ pullback.snd (limit.π D i₀).hom p =
        (BigFppfOver.toOver B S hS).op.whiskerLeft (yoneda.map f) ≫
          (restrictedYonedaIso (BigFppfOver.toOver B S hS)).hom.app V ∧
      IsPullback
        (Stacks.Groupoids.sourceMap (BigFppfOver.toOver B S hS) j)
        (Stacks.Groupoids.targetMap (BigFppfOver.toOver B S hS) j)
        q.hom q.hom ∧
      Stacks.Groupoids.IsEtaleEquivalenceRelation j := by
  classical
  let F := BigFppfOver.toOver B S hS
  let DP := D ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)
  let Y : Over S ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    yoneda ⋙ (Functor.whiskeringLeft _ _ (Type u)).obj F.op
  obtain ⟨T, s, t, hT, hsEtale, htEtale⟩ :=
    exists_chartKernelPair B S hS (D.obj i₀).obj (hD i₀) V p hp
  obtain ⟨E, ⟨eE⟩, _, hE, _⟩ :=
    exists_pullbackStages_of_affine_transition B S hS D hD hAffine i₀ V p
  obtain ⟨K, ⟨eK⟩, _, hK, _⟩ :=
    exists_pullbackStages_of_affine_transition B S hS D hD hAffine i₀ T (yoneda.map t ≫ p)
  let σ := pullbackStagesMap B S hS D i₀ V T p (yoneda.map t ≫ p)
    s hT.w E K eE eK
  let τ := pullbackStagesMap B S hS D i₀ V T p (yoneda.map t ≫ p)
    t rfl E K eE eK
  let L := E ⋙ F
  let M := K ⋙ F
  let : HasLimit L := hE
  let : HasLimit M := hK
  let σF : M ⟶ L := Functor.whiskerRight σ F
  let τF : M ⟶ L := Functor.whiskerRight τ F
  have hpair (x : Over i₀) : IsPullback
      (yoneda.map (σ.app x)) (yoneda.map (τ.app x))
      ((eE.app x).hom ≫ pullback.fst (DP.map x.hom) p)
      ((eE.app x).hom ≫ pullback.fst (DP.map x.hom) p) :=
    isPullback_pullbackStages B S hS D i₀ V T p s t hT E K eE eK x
  have hrel (x : Over i₀) :
      IsEquivalenceRelation (σF.app x) (τF.app x) :=
    AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback B S hS
      ((eE.app x).hom ≫ pullback.fst (DP.map x.hom) p)
      (σ.app x) (τ.app x) (hpair x)
  let z : Over i₀ := Over.mk (𝟙 i₀)
  let hz : IsTerminal z := Over.mkIdTerminal
  have hcart (g : T ⟶ V) (hg : yoneda.map g ≫ p = yoneda.map t ≫ p) (x : Over i₀) : IsPullback
      (M.map (hz.from x))
      ((Functor.whiskerRight (pullbackStagesMap B S hS D i₀ V T p (yoneda.map t ≫ p)
        g hg E K eE eK) F).app x)
      ((Functor.whiskerRight (pullbackStagesMap B S hS D i₀ V T p (yoneda.map t ≫ p)
        g hg E K eE eK) F).app z) (L.map (hz.from x)) := by
    have hpresheaf := isPullback_pullbackStagesMap B S hS D i₀ V T p
      (yoneda.map t ≫ p) g hg E K eE eK (hz.from x)
    have hsite := IsPullback.of_map yoneda
      (yoneda.map_injective hpresheaf.w) hpresheaf
    simpa only [M, L, Functor.whiskerRight_app, Functor.comp_map]
      using hsite.map F
  have hσEtale : Etale (σF.app z).left :=
    etale_pullbackStagesMap B S hS D i₀ V T p
      (yoneda.map t ≫ p) s hT.w E K eE eK z hsEtale
  have hτEtale : Etale (τF.app z).left :=
    etale_pullbackStagesMap B S hS D i₀ V T p
      (yoneda.map t ≫ p) t rfl E K eE eK z htEtale
  let j : Stacks.Groupoids.PreRelation (limit M) (limit L) :=
    prod.lift (limMap σF) (limMap τF)
  have hj : Stacks.Groupoids.IsEtaleEquivalenceRelation j :=
    isEtaleEquivalenceRelation_limMap S σF τF z hz
      (hcart s hT.w) (hcart t rfl) hrel hσEtale hτEtale
  let H := Over.post DP ⋙ Over.pullback p ⋙ Over.forget (yoneda.obj V)
  let eH : L ⋙ Y ≅ H :=
    Functor.isoWhiskerLeft E (restrictedYonedaIso F) ≪≫ eE
  let cDP : Cone DP :=
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapCone (limit.cone D)
  have hcDP : IsLimit cDP :=
    isLimitOfPreserves (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) (limit.isLimit D)
  let c : Cone H := (Over.forget (yoneda.obj V)).mapCone
    ((Over.pullback p).mapCone (cDP.overPost i₀))
  let : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have hc : IsLimit c := isLimitOfPreserves (Over.forget (yoneda.obj V))
    (isLimitOfPreserves (Over.pullback p) (hcDP.overPost i₀))
  let eU : Stacks.Groupoids.points F (limit L) ≅ pullback (limit.π D i₀).hom p :=
    preservesLimitIso Y L ≪≫ HasLimit.isoOfNatIso eH ≪≫
      (limit.isLimit H).conePointUniqueUpToIso hc
  let v : H.obj z ⟶ yoneda.obj V :=
    ((Over.pullback p).obj ((Over.post DP).obj z)).hom
  let vlim : pullback (limit.π D i₀).hom p ⟶ yoneda.obj V :=
    (((Over.pullback p).mapCone (cDP.overPost i₀)).pt).hom
  let r : E.obj z ⟶ V := yoneda.preimage ((eE.app z).hom ≫ v)
  let f : limit L ⟶ F.obj V := limit.π L z ≫ F.map r
  have hr : yoneda.map r = (eE.app z).hom ≫ v := yoneda.map_preimage _
  have heUall (x : Over i₀) : eU.hom ≫ c.π.app x =
      Y.map (limit.π L x) ≫ (eH.app x).hom := by
    change ((preservesLimitIso Y L).hom ≫
      (HasLimit.isoOfNatIso eH).hom ≫
      ((limit.isLimit _).conePointUniqueUpToIso hc).hom) ≫ c.π.app x = _
    rw [Category.assoc, Category.assoc,
      IsLimit.conePointUniqueUpToIso_hom_comp]
    change (preservesLimitIso Y L).hom ≫ (HasLimit.isoOfNatIso eH).hom ≫
      limit.π _ x = _
    rw [HasLimit.isoOfNatIso_hom_π, preservesLimitIso_hom_π_assoc]
    rfl
  have hcπ : c.π.app z ≫ v = vlim :=
    Over.w (((Over.pullback p).mapCone (cDP.overPost i₀)).π.app z)
  have hf : eU.hom ≫ pullback.snd (limit.π D i₀).hom p =
      F.op.whiskerLeft (yoneda.map f) ≫ (restrictedYonedaIso F).hom.app V := by
    change eU.hom ≫ vlim = Y.map f ≫ (restrictedYonedaIso F).hom.app V
    calc
      eU.hom ≫ vlim = (eU.hom ≫ c.π.app z) ≫ v :=
        (congrArg (fun w => eU.hom ≫ w) hcπ).symm.trans (Category.assoc _ _ _).symm
      _ = (Y.map (limit.π L z) ≫ (eH.app z).hom) ≫ v :=
        congrArg (fun w => w ≫ v) (heUall z)
      _ = Y.map f ≫ (restrictedYonedaIso F).hom.app V := by
        change (Y.map (limit.π L z) ≫
          ((restrictedYonedaIso F).hom.app (E.obj z) ≫ (eE.app z).hom)) ≫ v = _
        rw [Y.map_comp]
        simp only [Category.assoc]
        rw [← hr, ← (restrictedYonedaIso F).hom.naturality r]
        rfl
  let q : representedSheaf B S hS (limit L)
      (isSheaf_points_of_iso_pullback B S hS D i₀ V p (limit L) eU) ⟶ limit D :=
    ⟨eU.hom ≫ pullback.fst (limit.π D i₀).hom p⟩
  let DP' := Over.forget i₀ ⋙ DP
  let cDP' : Cone DP' := (Over.forget (DP.obj i₀)).mapCone (cDP.overPost i₀)
  have hcDP' : IsLimit cDP' :=
    isLimitOfPreserves (Over.forget (DP.obj i₀)) (hcDP.overPost i₀)
  let : HasLimit DP' := HasLimit.mk ⟨cDP', hcDP'⟩
  let a : L ⋙ Y ⟶ DP' := {
    app := fun x => (eH.app x).hom ≫ pullback.fst (DP.map x.hom) p
    naturality := by
      intro x y g
      change Y.map (L.map g) ≫
          ((eH.app y).hom ≫ pullback.fst (DP.map y.hom) p) =
        ((eH.app x).hom ≫ pullback.fst (DP.map x.hom) p) ≫ DP.map g.left
      have hnat : Y.map (L.map g) ≫ (eH.app y).hom =
          (eH.app x).hom ≫ H.map g := by
        simpa only [Functor.comp_obj, Functor.comp_map, Iso.app_hom] using
          eH.hom.naturality g
      have hbase : H.map g ≫ pullback.fst (DP.map y.hom) p =
          pullback.fst (DP.map x.hom) p ≫ DP.map g.left :=
        pullbackStages_map_fst DP i₀ p g
      exact ((Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ pullback.fst (DP.map y.hom) p) hnat)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun m => (eH.app x).hom ≫ m) hbase).trans
            (Category.assoc _ _ _).symm)) }
  have hpairY (x : Over i₀) :
      IsPullback (Y.map (σF.app x)) (Y.map (τF.app x))
        (a.app x) (a.app x) := by
    apply (hpair x).of_iso'
      ((restrictedYonedaIso F).app (K.obj x))
      ((restrictedYonedaIso F).app (E.obj x))
      ((restrictedYonedaIso F).app (E.obj x)) (Iso.refl _)
    · simpa only [σF, Y, L, M, Functor.whiskerRight_app, Functor.comp_obj,
        Functor.comp_map, Iso.app_hom, Iso.refl_hom, Category.comp_id] using
        ((restrictedYonedaIso F).hom.naturality (σ.app x)).symm
    · simpa only [τF, Y, L, M, Functor.whiskerRight_app, Functor.comp_obj,
        Functor.comp_map, Iso.app_hom, Iso.refl_hom, Category.comp_id] using
        ((restrictedYonedaIso F).hom.naturality (τ.app x)).symm
    · rfl
    · rfl
  have hlim : IsPullback (Y.map (limMap σF)) (Y.map (limMap τF))
      ((preservesLimitIso Y L).hom ≫ limMap a)
      ((preservesLimitIso Y L).hom ≫ limMap a) :=
    isPullback_map_limMap_of_isPullback Y σF τF a hpairY
  let eDP : limit DP' ≅ (limit D).obj :=
    (limit.isLimit DP').conePointUniqueUpToIso hcDP'
  have hfst (x : Over i₀) :
      c.π.app x ≫ pullback.fst (DP.map x.hom) p =
        pullback.fst (limit.π D i₀).hom p ≫ cDP'.π.app x := by
    have hw₀ : (limit.π D x.left).hom ≫ DP.map x.hom =
        (limit.π D i₀).hom := by
      change (limit.π D x.left ≫ D.map x.hom).hom =
        (limit.π D i₀).hom
      exact congrArg (fun f : limit D ⟶ D.obj i₀ => f.hom) (limit.w D x.hom)
    have hw : (pullback.fst (limit.π D i₀).hom p ≫
          (limit.π D x.left).hom) ≫ DP.map x.hom =
        pullback.snd (limit.π D i₀).hom p ≫ p := by
      rw [Category.assoc, hw₀, pullback.condition]
    change (pullback.lift (f := DP.map x.hom) (g := p)
        (pullback.fst (limit.π D i₀).hom p ≫ (limit.π D x.left).hom)
        (pullback.snd (limit.π D i₀).hom p) hw) ≫
      pullback.fst (DP.map x.hom) p =
        pullback.fst (limit.π D i₀).hom p ≫ (limit.π D x.left).hom
    exact pullback.lift_fst _ _ _
  have heDP (x : Over i₀) : eDP.hom ≫ cDP'.π.app x = limit.π DP' x :=
    IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit DP') hcDP' x
  have hq' : ((preservesLimitIso Y L).hom ≫ limMap a) ≫ eDP.hom =
      q.hom := by
    apply hcDP'.hom_ext
    intro x
    have h₁ : ((preservesLimitIso Y L).hom ≫ limMap a) ≫ limit.π DP' x =
        Y.map (limit.π L x) ≫ a.app x := by
      rw [Category.assoc, limMap_π, preservesLimitIso_hom_π_assoc]
    have h₂ : q.hom ≫ cDP'.π.app x = Y.map (limit.π L x) ≫ a.app x :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun w => eU.hom ≫ w) (hfst x)).symm.trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun w => w ≫ pullback.fst (DP.map x.hom) p) (heUall x)).trans
              (Category.assoc _ _ _))))
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun w => ((preservesLimitIso Y L).hom ≫ limMap a) ≫ w) (heDP x)).trans
        (h₁.trans h₂.symm))
  have hqinv : (preservesLimitIso Y L).hom ≫ limMap a =
      q.hom ≫ eDP.symm.hom :=
    (((congrArg (fun w => w ≫ eDP.symm.hom) hq').symm.trans (Category.assoc _ _ _)).trans
      ((congrArg (fun w => ((preservesLimitIso Y L).hom ≫ limMap a) ≫ w)
        eDP.hom_inv_id).trans (Category.comp_id _))).symm
  have hkernelY : IsPullback (Y.map (limMap τF)) (Y.map (limMap σF))
      q.hom q.hom := by
    apply hlim.flip.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _) eDP.symm
    · simp
    · simp
    · exact (Category.id_comp _).trans hqinv
    · exact (Category.id_comp _).trans hqinv
  refine ⟨limit L, _, limit M, j, eU, q, f, rfl, hf, ?_, hj⟩
  simpa only [Y, Functor.comp_map, Functor.whiskeringLeft_obj_map,
    Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap,
    Stacks.Groupoids.PreRelation.source, Stacks.Groupoids.PreRelation.target,
    j, prod.lift_fst, prod.lift_snd, Functor.comp_obj] using hkernelY

/-- An atlas whose underlying scheme belongs to the site is an object of the site, so
its functor of points is represented there. -/
private theorem exists_siteAtlas_of_contains (U₀ : Over S) (h : B.Contains U₀.left) :
    ∃ (V : BigFppfOver B S hS) (α : (BigFppfOver.toOver B S hS).obj V ⟶ U₀),
      IsIso ((BigFppfOver.toOver B S hS).op.whiskerLeft (yoneda.map α)) := by
  let W₀ : B.Schemes := ⟨U₀.left, h⟩
  let g : W₀ ⟶ B.obj hS := B.inclusion.preimage U₀.hom
  let e : (BigFppfOver.toOver B S hS).obj (Over.mk g) ≅ U₀ :=
    Over.isoMk (Iso.refl _) ((Category.id_comp U₀.hom).trans
      (B.inclusion.map_preimage (X := W₀) (Y := B.obj hS) U₀.hom).symm)
  exact ⟨Over.mk g, e.hom,
    (Functor.isoWhiskerLeft (BigFppfOver.toOver B S hS).op (yoneda.mapIso e)).isIso_hom⟩

/-- Let `D` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms and `p₀ : U₀ ⟶ D i₀` a surjective étale atlas of one stage. Then there are a scheme
`U` over `S` with `f : U ⟶ U₀` and `q : U ⟶ lim D` making `U = U₀ ×_{D i₀} lim D`, and an étale
equivalence relation `R` on `U` that is the kernel pair of `q`, such that the canonical map from
`U/R` to the limit of the inverse system is an isomorphism of fppf sheaves.

The atlas `U₀` is required to be one of the site's schemes (`hU₀mem`), as in Stacks 07SG, which
chooses a scheme `U₀` together with a surjective étale morphism `U₀ → X₀`; an atlas of an
algebraic space is an object of the site by construction, cf.
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`. -/
@[stacks 07SG]
public theorem exists_quotient_presentation_of_affine_transition
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u))
    [HasLimit D] [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B S hS (D.obj i).obj)
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B S hS (D.map f).hom)
    (i₀ : I) (U₀ : Over S) (hU₀mem : B.Contains U₀.left)
    (hU₀ : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U₀))
    (p₀ : representedSheaf B S hS U₀ hU₀ ⟶ D.obj i₀)
    (hp₀ : Epi p₀)
    (hp₀Etale :
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) p₀.hom)
    : ∃ (U : Over S)
        (hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
          (Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U))
        (R : Over S) (j : Stacks.Groupoids.PreRelation R U)
        (q : representedSheaf B S hS U hU ⟶ limit D)
        (f : U ⟶ U₀),
        IsPullback
          ((BigFppfOver.toOver B S hS).op.whiskerLeft (yoneda.map f))
          q.hom p₀.hom (limit.π D i₀).hom ∧
        ∃ (hq : Stacks.Groupoids.sourceMap (BigFppfOver.toOver B S hS) j ≫ q.hom =
            Stacks.Groupoids.targetMap (BigFppfOver.toOver B S hS) j ≫ q.hom),
          IsPullback
            (Stacks.Groupoids.sourceMap (BigFppfOver.toOver B S hS) j)
            (Stacks.Groupoids.targetMap (BigFppfOver.toOver B S hS) j)
            q.hom q.hom ∧
          Stacks.Groupoids.IsEtaleEquivalenceRelation j ∧
          IsIso (canonicalQuotientToLimit B S hS D j hU q hq) := by
  suffices h : ∃ (U : Over S)
      (hU : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
        (Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U))
      (R : Over S) (j : Stacks.Groupoids.PreRelation R U)
      (q : representedSheaf B S hS U hU ⟶ limit D) (f : U ⟶ U₀),
      IsPullback
        ((BigFppfOver.toOver B S hS).op.whiskerLeft (yoneda.map f))
        q.hom p₀.hom (limit.π D i₀).hom ∧
      IsPullback
        (Stacks.Groupoids.sourceMap (BigFppfOver.toOver B S hS) j)
        (Stacks.Groupoids.targetMap (BigFppfOver.toOver B S hS) j) q.hom q.hom ∧
      Stacks.Groupoids.IsEtaleEquivalenceRelation j by
    obtain ⟨U, hU, R, j, q, f, hcart, hkernel, hetale⟩ := h
    let f' : representedSheaf B S hS U hU ⟶ representedSheaf B S hS U₀ hU₀ :=
      ⟨(BigFppfOver.toOver B S hS).op.whiskerLeft (yoneda.map f)⟩
    have hqEpi : Epi q := epi_of_isPullback (BigFppfOver.topology B S hS)
      (p := f') (q := q) (f := p₀) (g := limit.π D i₀) hcart hp₀
    exact ⟨U, hU, R, j, q, f, hcart, hkernel.w, hkernel, hetale,
      canonicalQuotientToLimit_isIso_of_epi_of_isPullback
        B S hS D j hU q hqEpi hkernel⟩
  classical
  obtain ⟨V, α, hα⟩ := exists_siteAtlas_of_contains B S hS U₀ hU₀mem
  let ι : Stacks.Groupoids.points (BigFppfOver.toOver B S hS) ((BigFppfOver.toOver B S hS).obj V) ≅
      yoneda.obj V := (restrictedYonedaIso (BigFppfOver.toOver B S hS)).app V
  let eα : yoneda.obj V ≅ Stacks.Groupoids.points (BigFppfOver.toOver B S hS) U₀ :=
    ι.symm ≪≫ asIso ((BigFppfOver.toOver B S hS).op.whiskerLeft (yoneda.map α))
  have hp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) (eα.hom ≫ p₀.hom) :=
    (MorphismProperty.arrow_mk_iso_iff
      (P := MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)))
      (f := p₀.hom) (g := eα.hom ≫ p₀.hom)
      (Arrow.isoMk eα.symm (Iso.refl _) (by
        simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
        exact eα.inv_hom_id_assoc p₀.hom))).mp hp₀Etale
  obtain ⟨U, hU, R, j, eU, q, f, hq, hf, hker, hj⟩ :=
    exists_limit_chart_relation B S hS D hD hAffine i₀ V (eα.hom ≫ p₀.hom) hp
  refine ⟨U, hU, R, j, q, f ≫ α, ?_, hker, hj⟩
  refine (IsPullback.of_hasPullback (limit.π D i₀).hom (eα.hom ≫ p₀.hom)).flip.of_iso'
    eU eα.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [hf, yoneda.map_comp, Functor.whiskerLeft_comp]
    simp [eα, ι]
  · simp only [Iso.refl_hom]
    exact hq.symm
  · simp only [Iso.symm_hom, Iso.refl_hom]
    exact eα.inv_hom_id_assoc p₀.hom
  · simp

end AlgebraicGeometry.Space

end
