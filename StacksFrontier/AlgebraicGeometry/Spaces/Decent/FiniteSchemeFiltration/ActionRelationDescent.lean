module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration.ActionGroupoid
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ResidueDegreeBound

/-!
# Descent along the action relation and lifts of field-valued points

Components of coproducts of schemes, descent of morphisms to sheaves along the action
relation of a finite group acting on an object of the big fppf site, factorization through
open immersions, lifts of field-valued points through the distinct-tuple locus of a fibre
power, and criteria for an étale surjective morphism to be an isomorphism.

This is the third part of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁

namespace AlgebraicGeometry.Space

/-- The components of a coproduct of schemes are open immersions. -/
private theorem isOpenImmersion_sigmaι {σ : Type v} [Small.{u} σ]
    (g : σ → Scheme.{u}) (i : σ) : _root_.AlgebraicGeometry.IsOpenImmersion (Sigma.ι g i) :=
  (sigmaOpenCover g).map_prop i

/-- Every point of a scheme isomorphic to a coproduct lies in the image of a
component. -/
private theorem exists_sigmaι_comp_iso_eq {σ : Type v} [Small.{u} σ]
    (g : σ → Scheme.{u}) {Z : Scheme.{u}} (e : (∐ g : Scheme.{u}) ≅ Z) (x : Z) :
    ∃ (i : σ) (y : g i), (Sigma.ι g i ≫ e.hom).base y = x := by
  obtain ⟨i, y, hy⟩ := AlgebraicGeometry.exists_sigmaι_eq g (e.inv.base x)
  refine ⟨i, y, ?_⟩
  rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  simp

section ActionRelationDescent

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (V : AlgebraicGeometry.BigFppfOver B S hS) (G : Type v) [Group G] [Small.{u} G]

/-- The `g`-th copy of a site object inside its action relation object. -/
private def actionRelationSiteι
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left) (g : G) :
    V ⟶ AlgebraicGeometry.Space.siteActionRelationScheme G B hS V hR :=
  (Over.post B.inclusion).preimage
    (Sigma.ι (fun _ : G ↦ (Over.post B.inclusion).obj V) g)

omit [Group G] in
private theorem post_map_actionRelationSiteι
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left) (g : G) :
    (Over.post B.inclusion).map (actionRelationSiteι B S hS V G hR g) =
      Sigma.ι (fun _ : G ↦ (Over.post B.inclusion).obj V) g :=
  (Over.post B.inclusion).map_preimage _

omit [Group G] in
private theorem post_map_siteActionRelationSource
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left) :
    (Over.post B.inclusion).map (AlgebraicGeometry.Space.siteActionRelationSource G B hS V hR) =
      AlgebraicGeometry.Space.actionRelationSource ((Over.post B.inclusion).obj V) G := by
  ext
  rfl

private theorem post_map_siteActionRelationTarget
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left)
    (a : G →* Aut ((Over.post B.inclusion).obj V)) :
    (Over.post B.inclusion).map
        (AlgebraicGeometry.Space.siteActionRelationTarget G B hS V hR a) =
      AlgebraicGeometry.Space.actionRelationTarget ((Over.post B.inclusion).obj V) G a := by
  ext
  rfl

omit [Group G] in
private theorem actionRelationSiteι_comp_source
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left) (g : G) :
    actionRelationSiteι B S hS V G hR g ≫
        AlgebraicGeometry.Space.siteActionRelationSource G B hS V hR = 𝟙 V := by
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp, post_map_actionRelationSiteι,
    post_map_siteActionRelationSource, CategoryTheory.Functor.map_id]
  exact Limits.Sigma.ι_desc _ _

private theorem actionRelationSiteι_comp_target
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left)
    (a : G →* Aut ((Over.post B.inclusion).obj V)) (g : G) :
    actionRelationSiteι B S hS V G hR g ≫
        AlgebraicGeometry.Space.siteActionRelationTarget G B hS V hR a =
      (Over.post B.inclusion).preimage (a g).hom := by
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp, post_map_actionRelationSiteι,
    post_map_siteActionRelationTarget, Functor.map_preimage]
  exact Limits.Sigma.ι_desc _ _

omit [Group G] in
private theorem inclusion_map_actionRelationSiteι
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left) (g : G) :
    B.inclusion.map (actionRelationSiteι B S hS V G hR g).left =
      Sigma.ι (fun _ : G ↦ ((Over.post B.inclusion).obj V).left) g ≫
        (actionRelationUnderlyingIso ((Over.post B.inclusion).obj V) G).inv := by
  rw [actionRelationUnderlyingIso_inv_ι]
  exact congrArg (fun h : (Over.post B.inclusion).obj V ⟶
    (Over.post B.inclusion).obj (AlgebraicGeometry.Space.siteActionRelationScheme G B hS V hR) ↦
      h.left) (post_map_actionRelationSiteι B S hS V G hR g)

omit [Group G] in
private theorem actionRelationSite_ofArrows_mem_topology
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left) :
    Sieve.ofArrows (fun _ : Shrink.{u} G ↦ V)
        (fun i ↦ actionRelationSiteι B S hS V G hR ((equivShrink.{u} G).symm i)) ∈
      AlgebraicGeometry.BigFppfOver.topology B S hS
        (AlgebraicGeometry.Space.siteActionRelationScheme G B hS V hR) := by
  classical
  have hι (g : G) : _root_.AlgebraicGeometry.IsOpenImmersion
      (B.inclusion.map (actionRelationSiteι B S hS V G hR g).left) := by
    rw [inclusion_map_actionRelationSiteι]
    have := isOpenImmersion_sigmaι (fun _ : G ↦ ((Over.post B.inclusion).obj V).left) g
    exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (Sigma.ι _ g ≫
      (actionRelationUnderlyingIso ((Over.post B.inclusion).obj V) G).symm.hom))
  refine ofArrows_mem_bigFppfOverTopology B S hS _ _ ?_ ?_ ?_
  · intro t
    obtain ⟨g, y, hy⟩ := exists_sigmaι_comp_iso_eq
      (fun _ : G ↦ ((Over.post B.inclusion).obj V).left)
      (actionRelationUnderlyingIso ((Over.post B.inclusion).obj V) G).symm t
    refine ⟨equivShrink.{u} G g, y, ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [inclusion_map_actionRelationSiteι]
    exact hy
  · intro i
    have := hι ((equivShrink.{u} G).symm i)
    infer_instance
  · intro i
    have := hι ((equivShrink.{u} G).symm i)
    infer_instance

/-- A morphism to a sheaf out of a site object that is invariant under a finite
group action coequalizes the source and the target of the action relation. -/
private theorem yoneda_comp_siteActionRelation_eq
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) X)
    (a : G →* Aut ((Over.post B.inclusion).obj V))
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left)
    (w : yoneda.obj V ⟶ X)
    (hw : ∀ g : G,
      yoneda.map ((Over.post B.inclusion).preimage (a g).hom) ≫ w = w) :
    yoneda.map (AlgebraicGeometry.Space.siteActionRelationSource G B hS V hR) ≫ w =
      yoneda.map (AlgebraicGeometry.Space.siteActionRelationTarget G B hS V hR a) ≫ w := by
  classical
  have hsf : Presieve.IsSheafFor X
      (Presieve.ofArrows (fun _ : Shrink.{u} G ↦ V)
        (fun i ↦ actionRelationSiteι B S hS V G hR ((equivShrink.{u} G).symm i))) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      (hX.isSheafFor _ (actionRelationSite_ofArrows_mem_topology B S hS V G hR))
  apply yonedaEquiv.injective
  refine hsf.isSeparatedFor.ext ?_
  rintro Z f ⟨i⟩
  rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality,
    ← CategoryTheory.Functor.map_comp_apply, ← CategoryTheory.Functor.map_comp_apply,
    ← op_comp, ← op_comp, actionRelationSiteι_comp_source,
    actionRelationSiteι_comp_target, op_id, CategoryTheory.Functor.map_id_apply,
    yonedaEquiv_naturality, hw]

/-- A morphism to a sheaf out of a site object that is invariant under a finite
group action descends uniquely along a surjective flat quotient of finite
presentation whose kernel pair is the action relation. -/
theorem existsUnique_descent_of_actionRelation
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) X)
    (a : G →* Aut ((Over.post B.inclusion).obj V))
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left)
    {Q : AlgebraicGeometry.BigFppfOver B S hS} (q : V ⟶ Q)
    (hsurj : Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (hflat : Flat ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (hfp : LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q))
    (hker : ∀ {Z : AlgebraicGeometry.BigFppfOver B S hS} (p₁ p₂ : Z ⟶ V),
      p₁ ≫ q = p₂ ≫ q →
      ∃ r : Z ⟶ AlgebraicGeometry.Space.siteActionRelationScheme G B hS V hR,
        r ≫ AlgebraicGeometry.Space.siteActionRelationSource G B hS V hR = p₁ ∧
        r ≫ AlgebraicGeometry.Space.siteActionRelationTarget G B hS V hR a = p₂)
    (w : yoneda.obj V ⟶ X)
    (hw : ∀ g : G,
      yoneda.map ((Over.post B.inclusion).preimage (a g).hom) ≫ w = w) :
    ∃! w' : yoneda.obj Q ⟶ X, yoneda.map q ≫ w' = w := by
  have hinv := yoneda_comp_siteActionRelation_eq B S hS V G hX a hR w hw
  have hx : ∀ {Z : AlgebraicGeometry.BigFppfOver B S hS} (p₁ p₂ : Z ⟶ V),
      p₁ ≫ q = p₂ ≫ q →
      X.map p₁.op (yonedaEquiv w) = X.map p₂.op (yonedaEquiv w) := by
    intro Z p₁ p₂ hp
    obtain ⟨r, hr₁, hr₂⟩ := hker p₁ p₂ hp
    have e : ∀ s : Z ⟶ V,
        X.map s.op (yonedaEquiv w) = yonedaEquiv (yoneda.map s ≫ w) :=
      fun s ↦ yonedaEquiv_naturality w s
    rw [← hr₁, ← hr₂, e, e, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, hinv]
  obtain ⟨y, hy, huniq⟩ := exists_unique_descent_along_fppf_cover B S hS X hX q
    hsurj hflat hfp (yonedaEquiv w) hx
  refine ⟨yonedaEquiv.symm y, ?_, ?_⟩
  · apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, hy]
  · intro w' hw'
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    have hmap : X.map q.op (yonedaEquiv w') = yonedaEquiv w := by
      rw [yonedaEquiv_naturality, hw']
    exact huniq _ hmap

/-- Two maps to a site object that agree after a quotient whose kernel pair is
the action relation differ by a point of the action relation. -/
theorem exists_actionRelation_lift
    (a : G →* Aut ((Over.post B.inclusion).obj V))
    (hR : B.Contains (AlgebraicGeometry.Space.actionRelationScheme
      ((Over.post B.inclusion).obj V) G).left)
    {Q : AlgebraicGeometry.BigFppfOver B S hS} (q : V ⟶ Q)
    (hpb : IsPullback
      (AlgebraicGeometry.Space.actionRelationTarget ((Over.post B.inclusion).obj V) G a)
      (AlgebraicGeometry.Space.actionRelationSource ((Over.post B.inclusion).obj V) G)
      ((Over.post B.inclusion).map q) ((Over.post B.inclusion).map q))
    {Z : AlgebraicGeometry.BigFppfOver B S hS} (p₁ p₂ : Z ⟶ V) (hp : p₁ ≫ q = p₂ ≫ q) :
    ∃ r : Z ⟶ AlgebraicGeometry.Space.siteActionRelationScheme G B hS V hR,
      r ≫ AlgebraicGeometry.Space.siteActionRelationSource G B hS V hR = p₁ ∧
      r ≫ AlgebraicGeometry.Space.siteActionRelationTarget G B hS V hR a = p₂ := by
  have hcomm : (Over.post B.inclusion).map p₂ ≫ (Over.post B.inclusion).map q =
      (Over.post B.inclusion).map p₁ ≫ (Over.post B.inclusion).map q := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hp]
  let r : (Over.post B.inclusion).obj Z ⟶ (Over.post B.inclusion).obj
      (AlgebraicGeometry.Space.siteActionRelationScheme G B hS V hR) :=
    hpb.lift ((Over.post B.inclusion).map p₂) ((Over.post B.inclusion).map p₁) hcomm
  refine ⟨(Over.post B.inclusion).preimage r, ?_, ?_⟩ <;>
    apply (Over.post B.inclusion).map_injective <;>
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_preimage]
  · rw [post_map_siteActionRelationSource]
    exact hpb.lift_snd _ _ _
  · rw [post_map_siteActionRelationTarget]
    exact hpb.lift_fst _ _ _

end ActionRelationDescent

theorem isOpen_range_pointsMap_of_openSubspace
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (U : Subfunctor X) (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U) :
    letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
      AlgebraicGeometry.Space.pointTopology B S hS X
    IsOpen (Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι)) := by
  let _ : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
    AlgebraicGeometry.Space.pointTopology B S hS X
  let e := AlgebraicGeometry.Space.openSubspacesOrderIso B S hS X hX
  have hopen : IsOpen ((e ⟨U, hU⟩).1) := (e ⟨U, hU⟩).2
  rw [AlgebraicGeometry.Space.openSubspacesOrderIso_apply
    B S hS X hX ⟨U, hU⟩] at hopen
  exact hopen

theorem openSubspace_le_of_range_subset
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    {U V : Subfunctor X} (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U)
    (hV : AlgebraicGeometry.Space.IsOpenSubspace B S hS V)
    (h : Set.range (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι) ⊆
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS V.toFunctor V.ι)) : U ≤ V := by
  let := AlgebraicGeometry.Space.pointTopology B S hS X
  let e := AlgebraicGeometry.Space.openSubspacesOrderIso B S hS X hX
  have he : e ⟨U, hU⟩ ≤ e ⟨V, hV⟩ := by
    show (e ⟨U, hU⟩).1 ⊆ (e ⟨V, hV⟩).1
    simpa only [e, AlgebraicGeometry.Space.openSubspacesOrderIso_apply] using h
  exact e.le_iff_le.mp he

theorem openSubspace_eq_top_of_surjective_pointsMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (U : Subfunctor X) (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U)
    (hs : Function.Surjective (AlgebraicGeometry.Space.pointsMap B S hS U.toFunctor U.ι)) :
    U = ⊤ := by
  obtain ⟨f, hf⟩ := (AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points
    B S hS hX hX U hU (𝟙 X)).mpr (by rw [hs.range_eq]; exact Set.subset_univ _)
  apply top_unique
  intro i x _
  have he : (f.app i x).val = x :=
    congrArg (fun k : X ⟶ X ↦ k.app i x) hf
  exact he ▸ (f.app i x).property

theorem card_sections_le_rank
    {k : Type u} [Field k] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k))
    (r : ℕ) [hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r]
    {n : ℕ} (s : Fin n → (Spec (.of k) ⟶ Y))
    (hs : Function.Injective s) (hsp : ∀ i, s i ≫ p = 𝟙 _) : n ≤ r := by
  let : IsAffine Y := isAffine_of_isAffineHom p
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  let : Algebra k Γ(Y, ⊤) := φ.hom.toAlgebra
  obtain ⟨hfinite, hrank⟩ :=
    finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank p r
  let : Module.Finite k Γ(Y, ⊤) := hfinite
  let t : Fin n → (Γ(Y, ⊤) →ₐ[k] k) := fun i ↦
    { __ := ((s i).appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom
      commutes' := by
        intro x
        have h := congrArg Scheme.Hom.appTop (hsp i)
        simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
        have hc : φ ≫ (s i).appTop ≫ (Scheme.ΓSpecIso (.of k)).hom = 𝟙 _ := by
          dsimp only [φ]
          rw [Category.assoc, ← Category.assoc p.appTop, h]
          simp
        exact congrArg (fun a : CommRingCat.of k ⟶ CommRingCat.of k ↦ a.hom x) hc }
  have ht : Function.Injective t := by
    intro i j hij
    apply hs
    apply ext_of_isAffine
    apply (cancel_mono (Scheme.ΓSpecIso (.of k)).hom).mp
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom hij)
  have hle := Nat.card_le_card_of_injective t ht
  rw [Nat.card_fin] at hle
  exact hle.trans ((card_algHom_le_finrank k Γ(Y, ⊤) k).trans_eq hrank)

theorem exists_lift_of_isOpenImmersion_range_subset
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {E P T : AlgebraicGeometry.BigFppfOver B S hS} (d : E ⟶ P) (g : T ⟶ P)
    (hd : _root_.AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map d))
    (hg : Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ⊆
      Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map d)) :
    ∃ l : T ⟶ E, l ≫ d = g := by
  let q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let := hd
  let l := IsOpenImmersion.lift (q.map d) (q.map g) hg
  have hl : l ≫ q.map d = q.map g := IsOpenImmersion.lift_fac _ _ _
  let l' : T ⟶ E := Over.homMk (ObjectProperty.homMk l) (by
    apply ObjectProperty.hom_ext
    show l ≫ E.hom.hom = T.hom.hom
    have hdw : q.map d ≫ P.hom.hom = E.hom.hom := congrArg (fun k ↦ k.hom) d.w
    rw [← hdw, ← Category.assoc, hl]
    exact congrArg (fun k ↦ k.hom) g.w)
  exact ⟨l', q.map_injective hl⟩

private theorem coordinateDiagonal_projection_eq
    {C : Type*} [Category.{u} C] {X : Cᵒᵖ ⥤ Type u} {U : C}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (hd : yoneda.relativelyRepresentable (pullback.diagonal f))
    (n : ℕ) (i j : Fin (n + 1)) :
    hd.snd (fiberPowerPair f hf n i j) ≫ fiberPowerProjection f hf n i =
      hd.snd (fiberPowerPair f hf n i j) ≫ fiberPowerProjection f hf n j := by
  apply yoneda.map_injective
  have h₁ := congrArg (fun k ↦ k ≫ pullback.fst f f) (hd.w (fiberPowerPair f hf n i j))
  have h₂ := congrArg (fun k ↦ k ≫ pullback.snd f f) (hd.w (fiberPowerPair f hf n i j))
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
    Category.comp_id, fiberPowerPair_fst, fiberPowerPair_snd] at h₁ h₂
  simpa only [Functor.map_comp] using h₁.symm.trans h₂

theorem mapsTo_distinctFiberPowerLocus_of_injective_coordinates
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U T : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (g : T ⟶ (fiberPower f hf n).1)
    (hT : Subsingleton ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T))
    (hg : Function.Injective (fun i => g ≫ fiberPowerProjection f hf n i)) :
    Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g) ⊆
      distinctFiberPowerLocus B S hS f hf ho hc n := by
  let q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  rintro _ ⟨x, rfl⟩ hx
  obtain ⟨⟨⟨i, j⟩, hij⟩, y, hy⟩ := Set.mem_iUnion.mp hx
  let d := ho.rep.snd (fiberPowerPair f hf n i j)
  have hrange : Set.range (q.map g) ⊆ Set.range (q.map d) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨y, hy.trans (congrArg (q.map g) (hT.elim x z))⟩
  obtain ⟨l, hl⟩ := exists_lift_of_isOpenImmersion_range_subset B S hS d g
    (ho.property_snd _) hrange
  apply hij
  apply hg
  show g ≫ fiberPowerProjection f hf n i = g ≫ fiberPowerProjection f hf n j
  rw [← hl, Category.assoc, Category.assoc,
    coordinateDiagonal_projection_eq f hf ho.rep n i j]

/-- The inclusion of an open subobject of the site is an open immersion of schemes. -/
private theorem isOpenImmersion_map_opensSiteObjectInclusion_aux
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (W : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U).Opens) :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (opensSiteObjectInclusion B S hS U W)) := by
  have h : _root_.AlgebraicGeometry.IsOpenImmersion W.ι := inferInstance
  rw [map_opensSiteObjectInclusion]
  exact h

private theorem exists_distinctFiberPower_lift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U T : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ) (g : yoneda.obj T ⟶ X)
    (hT : Subsingleton ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T))
    (a : Fin (n + 1) → (T ⟶ U)) (ha : Function.Injective a)
    (hcomp : ∀ i, yoneda.map (a i) ≫ f = g) :
    ∃ l : T ⟶ opensSiteObject B S hS (fiberPower f hf n).1
        (distinctFiberPowerLocus B S hS f hf ho hc n),
      yoneda.map l ≫ yoneda.map (opensSiteObjectInclusion B S hS
        (fiberPower f hf n).1 (distinctFiberPowerLocus B S hS f hf ho hc n)) ≫
        (fiberPower f hf n).2 = g := by
  let L := distinctFiberPowerLocus B S hS f hf ho hc n
  let m := fiberPowerLift f hf n g a hcomp
  have hm : Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map m.1) ⊆ L := by
    apply mapsTo_distinctFiberPowerLocus_of_injective_coordinates B S hS f hf ho hc n m.1 hT
    simpa only [m.2.2] using ha
  let i := opensSiteObjectInclusion B S hS (fiberPower f hf n).1 L
  have hiL : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map i = L.ι :=
    map_opensSiteObjectInclusion B S hS _ _
  obtain ⟨l, hl⟩ := exists_lift_of_isOpenImmersion_range_subset B S hS i m.1
    (isOpenImmersion_map_opensSiteObjectInclusion_aux B S hS _ L)
    (by rw [hiL]; exact hm.trans_eq (Scheme.Opens.range_ι L).symm)
  refine ⟨l, ?_⟩
  rw [← Category.assoc, ← Functor.map_comp, hl]
  exact m.2.1

theorem exists_fieldValuedPoint_lift_of_surjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : AlgebraicGeometry.Space.IsSurjective B S hS f)
    (z : AlgebraicGeometry.Space.FieldValuedPoint B S hS G) :
    ∃ (w : AlgebraicGeometry.Space.FieldValuedPoint B S hS F)
      (e : w.siteObject B S hS F ⟶ z.siteObject B S hS G),
      f.app _ w.value = G.map e.op z.value := by
  obtain ⟨w, hw⟩ := hf z.class
  obtain ⟨w, rfl⟩ := Quot.exists_rep w
  obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    (AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff B S hS G _ z).mp hw
  let w' : AlgebraicGeometry.Space.FieldValuedPoint B S hS F :=
    ⟨r.carrier, r.contained, r.toBase, F.map a.op w.value⟩
  refine ⟨w', b, ?_⟩
  show f.app _ (F.map a.op w.value) = G.map b.op z.value
  exact (NatTrans.naturality_apply f a.op w.value).trans (ha.trans hb.symm)

private theorem exists_perm_of_injective_of_range_subset
    {α : Type*} {n : ℕ} (a b : Fin n → α)
    (hb : Function.Injective b) (h : Set.range b ⊆ Set.range a) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, a (σ i) = b i := by
  classical
  choose c hc using fun i ↦ h (Set.mem_range_self i)
  have hcInj : Function.Injective c := by
    intro i j hij
    apply hb
    rw [← hc i, ← hc j, hij]
  exact ⟨Equiv.ofBijective c ((Finite.injective_iff_bijective).mp hcInj), hc⟩

theorem exists_perm_or_distinctFiberPower_succ
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U T : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (n : ℕ)
    (hT : Subsingleton ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T))
    (hT' : Nonempty ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T))
    (a b : T ⟶ opensSiteObject B S hS (fiberPower f hf n).1
      (distinctFiberPowerLocus B S hS f hf ho hc n))
    (hab : yoneda.map (a ≫ opensSiteObjectInclusion B S hS (fiberPower f hf n).1
        (distinctFiberPowerLocus B S hS f hf ho hc n)) ≫ (fiberPower f hf n).2 =
      yoneda.map (b ≫ opensSiteObjectInclusion B S hS (fiberPower f hf n).1
        (distinctFiberPowerLocus B S hS f hf ho hc n)) ≫ (fiberPower f hf n).2) :
    (∃ σ : Equiv.Perm (Fin (n + 1)),
      a ≫ distinctFiberPowerSiteAction B S hS f hf ho hc n σ = b) ∨
    ∃ l : T ⟶ opensSiteObject B S hS (fiberPower f hf (n + 1)).1
        (distinctFiberPowerLocus B S hS f hf ho hc (n + 1)),
      yoneda.map (l ≫ opensSiteObjectInclusion B S hS (fiberPower f hf (n + 1)).1
        (distinctFiberPowerLocus B S hS f hf ho hc (n + 1))) ≫
          (fiberPower f hf (n + 1)).2 =
      yoneda.map (a ≫ opensSiteObjectInclusion B S hS (fiberPower f hf n).1
        (distinctFiberPowerLocus B S hS f hf ho hc n)) ≫ (fiberPower f hf n).2 := by
  classical
  let i := opensSiteObjectInclusion B S hS (fiberPower f hf n).1
    (distinctFiberPowerLocus B S hS f hf ho hc n)
  let ca (j : Fin (n + 1)) := (a ≫ i) ≫ fiberPowerProjection f hf n j
  let cb (j : Fin (n + 1)) := (b ≫ i) ≫ fiberPowerProjection f hf n j
  have hinj (c : T ⟶ opensSiteObject B S hS (fiberPower f hf n).1
      (distinctFiberPowerLocus B S hS f hf ho hc n)) :
      Function.Injective (fun j ↦ (c ≫ i) ≫ fiberPowerProjection f hf n j) := by
    apply injective_coordinates_of_mapsTo_distinctFiberPowerLocus B S hS f hf ho hc n
      (c ≫ i) hT'
    exact range_map_comp_opensSiteObjectInclusion B S hS _ c
  by_cases hsub : Set.range cb ⊆ Set.range ca
  · obtain ⟨σ, hσ⟩ := exists_perm_of_injective_of_range_subset ca cb (hinj b) hsub
    left
    refine ⟨σ.symm, ?_⟩
    have hi : Mono i := by
      have := isOpenImmersion_map_opensSiteObjectInclusion_aux B S hS _
        (distinctFiberPowerLocus B S hS f hf ho hc n)
      exact Functor.mono_of_mono_map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
        inferInstance
    apply (cancel_mono i).mp
    have hact : (a ≫ distinctFiberPowerSiteAction B S hS f hf ho hc n σ.symm) ≫ i =
        (a ≫ i) ≫ fiberPowerPermute f hf n σ := by
      show (a ≫ openSubschemeMap B S hS _ _
        (fiberPowerPermute f hf n σ.symm.symm)
        (mapsTo_distinctFiberPowerLocus B S hS f hf ho hc n σ.symm.symm)) ≫ i = _
      rw [Category.assoc, openSubschemeMap_inclusion, Category.assoc]
      rfl
    rw [hact]
    apply fiberPower_hom_ext f hf n
    intro j
    rw [Category.assoc, fiberPowerPermute_projection]
    exact hσ j
  · right
    obtain ⟨x, ⟨j, rfl⟩, hx⟩ := Set.not_subset.mp hsub
    let c : Fin (n + 1 + 1) → (T ⟶ U) := Fin.cons (cb j) ca
    have hc' : Function.Injective c := Fin.cons_injective_of_injective hx (hinj a)
    have hcomp : ∀ k, yoneda.map (c k) ≫ f = yoneda.map (a ≫ i) ≫ (fiberPower f hf n).2 := by
      intro k
      refine Fin.cases ?_ (fun l ↦ ?_) k
      · simpa only [c, Fin.cons_zero, cb, Functor.map_comp, Category.assoc,
          fiberPowerProjection_comp] using hab.symm
      · simp only [c, Fin.cons_succ, ca, Functor.map_comp, Category.assoc,
          fiberPowerProjection_comp]
    obtain ⟨l, hl⟩ := exists_distinctFiberPower_lift B S hS f hf ho hc (n + 1)
      (yoneda.map (a ≫ i) ≫ (fiberPower f hf n).2) hT c hc' hcomp
    exact ⟨l, by simpa only [Functor.map_comp, Category.assoc] using hl⟩

private theorem surjective_diagonal_of_fieldValuedPoint_lifts
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hl : ∀ z : AlgebraicGeometry.Space.FieldValuedPoint B S hS (pullback f f),
      ∃ (w : AlgebraicGeometry.Space.FieldValuedPoint B S hS (pullback f f))
        (e : w.siteObject B S hS _ ⟶ z.siteObject B S hS _),
        (pullback f f).map e.op z.value = w.value ∧
        yonedaEquiv.symm w.value ≫ pullback.fst f f =
          yonedaEquiv.symm w.value ≫ pullback.snd f f) :
    AlgebraicGeometry.Space.IsSurjective B S hS (pullback.diagonal f) := by
  intro z
  obtain ⟨z, rfl⟩ := Quot.exists_rep z
  obtain ⟨w, e, he, hw⟩ := hl z
  let wf : AlgebraicGeometry.Space.FieldValuedPoint B S hS F :=
    { carrier := w.carrier
      field := w.field
      contained := w.contained
      toBase := w.toBase
      value := (pullback.fst f f).app
        (Opposite.op (w.siteObject B S hS (pullback f f))) w.value }
  have hα : (yonedaEquiv.symm w.value ≫ pullback.fst f f) ≫ pullback.diagonal f =
      yonedaEquiv.symm w.value := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using hw
  have hval : (pullback.diagonal f).app _ wf.value = w.value := by
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply, wf,
      AlgebraicGeometry.Space.FieldValuedPoint.map,
      AlgebraicGeometry.Space.FieldValuedPoint.siteObject]
      using congrArg yonedaEquiv hα
  refine ⟨wf.class, ?_⟩
  apply AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension
  refine ⟨w, ?_, e, he⟩
  refine ⟨𝟙 _, ?_⟩
  show (pullback f f).map (𝟙 _) ((pullback.diagonal f).app _ wf.value) = w.value
  simpa only [CategoryTheory.Functor.map_id, types_id_apply] using hval

/-- A surjective étale map is locally surjective on the fppf site, as can be
checked after composing with a scheme atlas of its source. -/
private theorem isLocallySurjective_of_etale_surjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (he : AlgebraicGeometry.Space.IsEtale B S hS f)
    (hs : AlgebraicGeometry.Space.IsSurjective B S hS f) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) f := by
  obtain ⟨U, p, hpSurj, hpEtale⟩ := hF.exists_atlas
  have hU := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U
  have hcompEtale := he U p hpEtale
  have hpPoints :=
    (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective B S hS hU hF p hpSurj.1).mp hpSurj
  have hcompPoints : AlgebraicGeometry.Space.IsSurjective B S hS (p ≫ f) := by
    show Function.Surjective (AlgebraicGeometry.Space.pointsMap B S hS _ (p ≫ f))
    rw [AlgebraicGeometry.Space.pointsMap_comp B S hS (yoneda.obj U) p f]
    exact hs.comp hpPoints
  have hcompSurj :=
    (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective B S hS hU hG
      (p ≫ f) hcompEtale.1).mpr hcompPoints
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let Ush : Sheaf J (Type u) := ⟨yoneda.obj U, hU.isSheaf⟩
  let Gsh : Sheaf J (Type u) := ⟨G, hG.isSheaf⟩
  let a : Ush ⟶ Gsh := ⟨p ≫ f⟩
  have ha : Sheaf.IsLocallySurjective a := by
    apply isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
      B S hS a
    refine ⟨hcompEtale.1, ?_⟩
    intro V W g fst snd sq
    have : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map snd) :=
      hcompEtale.property g fst snd sq
    exact ⟨inferInstance, inferInstance, hcompSurj.property g fst snd sq⟩
  let : Presheaf.IsLocallySurjective J (p ≫ f) := ha
  exact Presheaf.isLocallySurjective_of_isLocallySurjective J p f

theorem isIso_of_etale_surjective_of_fieldValuedPoint_lifts
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (he : AlgebraicGeometry.Space.IsEtale B S hS f)
    (hs : AlgebraicGeometry.Space.IsSurjective B S hS f)
    (hl : ∀ z : AlgebraicGeometry.Space.FieldValuedPoint B S hS (pullback f f),
      ∃ (w : AlgebraicGeometry.Space.FieldValuedPoint B S hS (pullback f f))
        (e : w.siteObject B S hS _ ⟶ z.siteObject B S hS _),
        (pullback f f).map e.op z.value = w.value ∧
        yonedaEquiv.symm w.value ≫ pullback.fst f f =
          yonedaEquiv.symm w.value ≫ pullback.snd f f) : IsIso f := by
  have hdiagOpen :=
    AlgebraicGeometry.Space.isOpenImmersion_diagonal_of_isUnramified B S hS hF hG f
      (AlgebraicGeometry.Space.isUnramified_of_isEtale B S hS he)
  have hdiagIso := isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS
    (pullback.diagonal f) hdiagOpen
    (surjective_diagonal_of_fieldValuedPoint_lifts B S hS f hl)
  let : Mono f := (pullback.isIso_diagonal_iff (f := f)).mp hdiagIso
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let Fsh : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  let Gsh : Sheaf J (Type u) := ⟨G, hG.isSheaf⟩
  let a : Fsh ⟶ Gsh := ⟨f⟩
  have haInj : Sheaf.IsLocallyInjective a := by
    rw [Sheaf.isLocallyInjective_iff_injective]
    intro U
    exact (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app f).mp inferInstance U)
  have haSurj : Sheaf.IsLocallySurjective a :=
    isLocallySurjective_of_etale_surjective B S hS hF hG f he hs
  let : IsIso a := (Sheaf.isLocallyBijective_iff_isIso a).mp ⟨haInj, haSurj⟩
  exact (inferInstance : IsIso ((sheafToPresheaf J (Type u)).map a))

private theorem exists_empty_distinctFiberPower
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (ho : AlgebraicGeometry.Space.IsOpenImmersion B S hS (pullback.diagonal f))
    (hc : AlgebraicGeometry.Space.IsClosedImmersion B S hS (pullback.diagonal f))
    (hb : AlgebraicGeometry.Space.HasUniversallyBoundedFibers B S hS U f) :
    ∃ n : ℕ, 0 < n ∧ IsEmpty (AlgebraicGeometry.Space.points B S hS
      (yoneda.obj (opensSiteObject B S hS (fiberPower f hf n).1
        (distinctFiberPowerLocus B S hS f hf ho hc n)))) := by
  obtain ⟨N, hN⟩ := hb
  refine ⟨N.toNat + 1, Nat.succ_pos _, ⟨?_⟩⟩
  intro z
  obtain ⟨z, rfl⟩ := Quot.exists_rep z
  let n := N.toNat + 1
  let q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let T := z.siteObject B S hS _
  let i := opensSiteObjectInclusion B S hS (fiberPower f hf n).1
    (distinctFiberPowerLocus B S hS f hf ho hc n)
  let c := z.value ≫ i
  let a : Fin (n + 1) → (T ⟶ U) := fun j ↦ c ≫ fiberPowerProjection f hf n j
  have hac : Function.Injective a := by
    apply injective_coordinates_of_mapsTo_distinctFiberPowerLocus
      B S hS f hf ho hc n c (show Nonempty (Spec (.of z.carrier)) from inferInstance)
    exact range_map_comp_opensSiteObjectInclusion B S hS _ z.value
  let ξ := yoneda.map c ≫ (fiberPower f hf n).2
  have haξ (j : Fin (n + 1)) : yoneda.map (a j) ≫ f = ξ := by
    simp only [a, Functor.map_comp, Category.assoc, fiberPowerProjection_comp, ξ]
  obtain ⟨R, p, e, r, hrN, hr, hpb⟩ := hN z.carrier T (Iso.refl _) ξ
  let s (j : Fin (n + 1)) : T ⟶ R := yoneda.preimage
    (hpb.lift (yoneda.map (a j)) (𝟙 (yoneda.obj T)) (by simpa using haξ j))
  have hs₁ (j : Fin (n + 1)) : yoneda.map (s j) ≫ e = yoneda.map (a j) := by
    dsimp only [s]
    rw [Functor.map_preimage, hpb.lift_fst]
  have hs₂ (j : Fin (n + 1)) : s j ≫ p = 𝟙 T := by
    apply yoneda.map_injective
    dsimp only [s]
    rw [Functor.map_comp, Functor.map_preimage, hpb.lift_snd, CategoryTheory.Functor.map_id]
  have hs : Function.Injective (fun j ↦ q.map (s j)) := by
    intro j k hjk
    apply hac
    apply yoneda.map_injective
    rw [← hs₁ j, ← hs₁ k, q.map_injective hjk]
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (q.map p) r := hr
  have hn : n + 1 ≤ r := card_sections_le_rank (q.map p) r
    (fun j ↦ q.map (s j)) hs (fun j ↦ by rw [← q.map_comp, hs₂, q.map_id]; rfl)
  have hrN' : r ≤ N.toNat := by omega
  dsimp [n] at hn
  omega

theorem subfunctor_eq_sheafify_bot_of_isEmpty_points
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (D : Subfunctor X) (hD : AlgebraicGeometry.IsAlgebraicSpace B S hS D.toFunctor)
    (he : IsEmpty (AlgebraicGeometry.Space.points B S hS D.toFunctor)) :
    D = (⊥ : Subfunctor X).sheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) := by
  apply le_antisymm
  · intro T t ht
    have hT : IsEmpty (B.inclusion.obj T.unop.left) := by
      constructor
      intro x
      let Y := B.inclusion.obj T.unop.left
      have hk : B.Contains (Spec (Y.residueField x)) :=
        Scheme.size_lt_of_mono_quasiCompact (Y.fromSpecResidueField x) T.unop.left.property
      let K : AlgebraicGeometry.BigFppfOver B S hS :=
        Over.mk (ObjectProperty.homMk (Y.fromSpecResidueField x ≫ T.unop.hom.hom) :
          B.obj hk ⟶ B.obj hS)
      let g : K ⟶ T.unop := Over.homMk (ObjectProperty.homMk (Y.fromSpecResidueField x))
      let z : AlgebraicGeometry.Space.FieldValuedPoint B S hS D.toFunctor :=
        ⟨Y.residueField x, hk, Y.fromSpecResidueField x ≫ T.unop.hom.hom,
          D.toFunctor.map g.op ⟨t, ht⟩⟩
      exact he.false z.class
    have hbot : (⊥ : Sieve T.unop) ∈ AlgebraicGeometry.BigFppfOver.topology B S hS T.unop := by
      have hcov := ofArrows_mem_bigFppfOverTopology B S hS
        (fun j : PEmpty.{u + 1} ↦ j.elim) (fun j ↦ j.elim)
        (fun x ↦ (hT.false x).elim) (fun j ↦ j.elim) (fun j ↦ j.elim)
      simpa only [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty, Sieve.generate_bot] using hcov
    show (⊥ : Subfunctor X).sieveOfSection t ∈
      AlgebraicGeometry.BigFppfOver.topology B S hS T.unop
    convert hbot using 1
    ext V g
    simp [Subfunctor.sieveOfSection]
  · exact Subfunctor.sheafify_le _ _ bot_le
      ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)
      ((isSheaf_iff_isSheaf_of_type _ _).mp hD.isSheaf)

/-- A field-valued point obtained by restricting another one along a morphism of
field spectra presents its morphism as that restriction. -/
theorem fieldMorphism_eq_yoneda_map_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p r : AlgebraicGeometry.Space.FieldValuedPoint B S hS F)
    (e : p.siteObject B S hS F ⟶ r.siteObject B S hS F)
    (he : F.map e.op r.value = p.value) :
    AlgebraicGeometry.Space.fieldMorphism B S hS F p =
      yoneda.map e ≫ AlgebraicGeometry.Space.fieldMorphism B S hS F r :=
  ((yonedaEquiv_symm_naturality_left e F r.value).trans
    (congrArg yonedaEquiv.symm he)).symm

/-- Every point of a presheaf is the image of a point along an isomorphism onto it. -/
theorem mem_range_pointsMap_of_isIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G) [IsIso α]
    (x : AlgebraicGeometry.Space.points B S hS G) :
    x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS F α) := by
  refine ⟨AlgebraicGeometry.Space.pointsMap B S hS G (inv α) x, ?_⟩
  have h : AlgebraicGeometry.Space.pointsMap B S hS G (inv α ≫ α) x = x := by
    rw [IsIso.inv_hom_id, AlgebraicGeometry.Space.pointsMap_id, id_eq]
  simpa only [AlgebraicGeometry.Space.pointsMap_comp, Function.comp_apply] using h

end AlgebraicGeometry.Space

end
