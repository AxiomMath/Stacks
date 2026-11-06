module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismSheaf

/-!
# The sheaf of glueing-data morphisms into a glueing triple

In a formal glueing situation `(f : Y ⟶ X, Z, U = X \ Z, V = Y \ f⁻¹(Z))` write `Φ` for the
presheaf-level restriction functor `Over X ⥤ Comma …`, `T ↦ (T ×_X U, T ×_X Y, can)`
(`AlgebraicGeometry.Space.FormalGlueingSituation.restrictionDiagram`). For a glueing triple `G`
this module builds the presheaf

```text
W ↦ { (w, φ) | w : W ⟶ X, φ : Φ(W, w) ⟶ G },
```

on the big fppf site of `S`, together with its projection to `X`, and proves it is a sheaf. It is
the candidate for the space `X'` of Stacks 0AF4 clause (1) when `X` is not affine: when `G` is
the triple of a space `X'` over `X`, its value at `W` is the set of morphisms `W ⟶ X'`
(Stacks 0AF6).

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.glueSections`: the pairs `(w, φ)` at one test
  object, a type one universe too large.
* `AlgebraicGeometry.Space.FormalGlueingSituation.homPresheaf`: the pairs, shrunk to the working
  universe, as a presheaf on the big fppf site.
* `AlgebraicGeometry.Space.FormalGlueingSituation.homPresheafProjection`: its projection to `X`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.isSheaf_homPresheaf`: the presheaf is an fppf
  sheaf.
* `AlgebraicGeometry.Space.eq_of_isSeparatedFor_of_isPullback`: two morphisms into a sheaf out of
  a presheaf over a representable agree once they agree after base change along every member of
  a covering sieve.

## Implementation notes

The two legs of a pair are relative morphisms in the sense of Stacks 05Y1: the `U`-leg is an
element of `Mor_X(U, G_U)` and the `Y`-leg of `Mor_X(Y, G_Y)`. The sheaf property of those two
relative morphism functors (Stacks 05Y3,
`AlgebraicGeometry.Space.isSheaf_relativeHom`) glues the legs; the two remaining conditions on a
pair — the `Y`-leg lies over `Y`, and the legs agree over `V` — are equalities of morphisms into
sheaves, local on the test object by
`AlgebraicGeometry.Space.eq_of_isSeparatedFor_of_isPullback`.

## References

* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Equalities of morphisms into a sheaf are local on a representable base.** Let
`p : P ⟶ yoneda.obj W` be a presheaf over a representable and `a b : P ⟶ E` two morphisms into a
presheaf separated for every covering sieve. If for every member `g : W' ⟶ W` of a covering
sieve the two morphisms agree after the base change `r : P' ⟶ P` of `p` along `g`, they agree. -/
theorem eq_of_isSeparatedFor_of_isPullback {W : BigFppfOver B S hS} {R : Sieve W}
    (hR : R ∈ BigFppfOver.topology B S hS W) {P E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hE : Presheaf.IsSheaf (BigFppfOver.topology B S hS) E) (p : P ⟶ yoneda.obj W)
    (a b : P ⟶ E)
    (hab : ∀ ⦃W' : BigFppfOver B S hS⦄ (g : W' ⟶ W), R g →
      ∃ (P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (r : P' ⟶ P) (π : P' ⟶ yoneda.obj W'),
        IsPullback r π p (yoneda.map g) ∧ r ≫ a = r ≫ b) :
    a = b := by
  rw [isSheaf_iff_isSheaf_of_type] at hE
  ext T x
  show a.app T x = b.app T x
  let t : T.unop ⟶ W := p.app T x
  refine (hE _ ((BigFppfOver.topology B S hS).pullback_stable t hR)).isSeparatedFor.ext ?_
  intro T' h hh
  obtain ⟨P', r, π, hpb, hab⟩ := hab (h ≫ t) hh
  have hpbT := hpb.map ((evaluation _ _).obj (op T'))
  obtain ⟨y, hy₁, hy₂⟩ := Types.exists_of_isPullback hpbT (P.map h.op x) (𝟙 T') (by
    show p.app (op T') (P.map h.op x) = 𝟙 T' ≫ h ≫ t
    rw [NatTrans.naturality_apply]
    simp [t])
  have hab' := congrArg (fun m => m.app (op T') y) hab
  simp only [NatTrans.comp_app, types_comp_apply] at hab'
  change r.app (op T') y = P.map h.op x at hy₁
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← hy₁, hab']

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_FormalGlueingSpacesHomSheaf
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (Limits.functorCategoryHasLimitsOfShape :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).has_limit _

/-- Pullbacks in presheaves on `BigFppfOver B S hS`, given directly (see above). -/
local instance (priority := high) hasPullbacks_presheaf_FormalGlueingSpacesHomSheaf
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

variable (D : FormalGlueingSituation B S hS) (G : glueingData D)

/-- The pairs `(w, φ)` at a test object `W`: a morphism `w : W ⟶ X` and a morphism of glueing
data `φ : Φ(W, w) ⟶ G` out of the restriction of `W`. A type one universe too large;
`AlgebraicGeometry.Space.FormalGlueingSituation.homPresheaf` shrinks it. -/
abbrev glueSections (W : BigFppfOver B S hS) : Type (u + 1) :=
  Σ w : yoneda.obj W ⟶ D.X, (restrictionDiagram D).obj (Over.mk w) ⟶ G.obj

/-- The pairs at a test object form a `u`-small type: both components range over morphisms of
presheaves of the working universe. -/
instance small_glueSections (W : BigFppfOver B S hS) : Small.{u} (glueSections D G W) := by
  have : Small.{u} (yoneda.obj W ⟶ D.X) := small_hom_presheaf _ _
  have : ∀ w : yoneda.obj W ⟶ D.X,
      Small.{u} ((restrictionDiagram D).obj (Over.mk w) ⟶ G.obj) := fun w => by
    have := small_hom_presheaf ((restrictionDiagram D).obj (Over.mk w)).left.left
      G.obj.left.left
    have := small_hom_presheaf ((restrictionDiagram D).obj (Over.mk w)).right.left
      G.obj.right.left
    refine small_of_injective (f := fun φ => (φ.left.left, φ.right.left)) ?_
    intro φ ψ hφψ
    simp only [Prod.mk.injEq] at hφψ
    exact Comma.hom_ext _ _ (Over.OverMorphism.ext hφψ.1) (Over.OverMorphism.ext hφψ.2)
  infer_instance

variable {D G}

/-- Restriction of a pair along a morphism of test objects. -/
noncomputable def glueSections.restrict {W W' : BigFppfOver B S hS} (g : W' ⟶ W)
    (s : glueSections D G W) : glueSections D G W' :=
  ⟨yoneda.map g ≫ s.1, (restrictionDiagram D).map
    (Over.homMk (yoneda.map g) : Over.mk (yoneda.map g ≫ s.1) ⟶ Over.mk s.1) ≫ s.2⟩

/-- Two pairs with equal first components are equal once their second components agree along
the identification of the two restrictions. -/
theorem glueSections.ext' {W : BigFppfOver B S hS} {w w' : yoneda.obj W ⟶ D.X} (h : w = w')
    {φ : (restrictionDiagram D).obj (Over.mk w) ⟶ G.obj}
    {φ' : (restrictionDiagram D).obj (Over.mk w') ⟶ G.obj}
    (hφ : φ = (restrictionDiagram D).map
      (Over.homMk (𝟙 _) (by rw [h, Category.id_comp]) : Over.mk w ⟶ Over.mk w') ≫ φ') :
    (⟨w, φ⟩ : glueSections D G W) = ⟨w', φ'⟩ := by
  subst h
  have h1 : (Over.homMk (𝟙 _) (by rw [Category.id_comp]) : Over.mk w ⟶ Over.mk w) = 𝟙 _ :=
    Over.OverMorphism.ext rfl
  rw [h1, CategoryTheory.Functor.map_id, Category.id_comp] at hφ
  rw [hφ]

/-- Restriction of a pair along the identity is the identity. -/
theorem glueSections.restrict_id {W : BigFppfOver B S hS} (s : glueSections D G W) :
    s.restrict (𝟙 W) = s := by
  obtain ⟨w, φ⟩ := s
  refine glueSections.ext' (by simp) ?_
  congr 2

/-- Restriction of a pair along a composite is the composite of the restrictions. -/
theorem glueSections.restrict_comp {W W' W'' : BigFppfOver B S hS} (g : W' ⟶ W)
    (g' : W'' ⟶ W') (s : glueSections D G W) :
    (s.restrict g).restrict g' = s.restrict (g' ≫ g) := by
  obtain ⟨w, φ⟩ := s
  refine glueSections.ext' (by simp [glueSections.restrict]) ?_
  simp only [glueSections.restrict, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
  congr 2

variable (D G)

/-- **The presheaf of glueing-data morphisms into `G`.** Its value at `W` is the set of pairs
`(w : W ⟶ X, φ : Φ(W, w) ⟶ G)`, shrunk to the working universe. -/
noncomputable def homPresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj W := Shrink.{u} (glueSections D G W.unop)
  map {W W'} g := ↾fun s => equivShrink (glueSections D G W'.unop)
    (((equivShrink (glueSections D G W.unop)).symm s).restrict g.unop)
  map_id W := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change equivShrink (glueSections D G W.unop)
      (((equivShrink (glueSections D G W.unop)).symm s).restrict (𝟙 W.unop)) = s
    rw [glueSections.restrict_id, Equiv.apply_symm_apply]
  map_comp {W W' W''} g g' := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change equivShrink (glueSections D G W''.unop)
        (((equivShrink (glueSections D G W.unop)).symm s).restrict (g'.unop ≫ g.unop)) =
      equivShrink (glueSections D G W''.unop) (((equivShrink (glueSections D G W'.unop)).symm
        (equivShrink (glueSections D G W'.unop)
          (((equivShrink (glueSections D G W.unop)).symm s).restrict g.unop))).restrict g'.unop)
    rw [Equiv.symm_apply_apply, glueSections.restrict_comp]

/-- The projection of the presheaf of glueing-data morphisms to `X`. -/
noncomputable def homPresheafProjection : homPresheaf D G ⟶ D.X where
  app W := ↾fun s => yonedaEquiv ((equivShrink (glueSections D G W.unop)).symm s).1
  naturality W W' g := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    change yonedaEquiv ((equivShrink (glueSections D G W'.unop)).symm
        (equivShrink _ (((equivShrink (glueSections D G W.unop)).symm s).restrict g.unop))).1 =
      D.X.map g (yonedaEquiv ((equivShrink (glueSections D G W.unop)).symm s).1)
    rw [Equiv.symm_apply_apply]
    exact (yonedaEquiv_naturality' _ g).symm

variable {D G}

/-- The `U`-leg of a pair, as a pair of Stacks 05Y1 for `Mor_X(U, G_U)`. -/
noncomputable def glueSections.toRelU {W : BigFppfOver B S hS} (s : glueSections D G W) :
    RelativeMorphism B S hS D.U.toFunctor G.obj.left.left D.X D.U.ι
      (G.obj.left.hom ≫ D.U.ι) (yoneda.obj W) where
  base := s.1
  morphism := s.2.left.left
  commutes := by
    have h : s.2.left.left ≫ G.obj.left.hom = pullback.snd s.1 D.U.ι := Over.w s.2.left
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.U.ι) h)

/-- The `Y`-leg of a pair, as a pair of Stacks 05Y1 for `Mor_X(Y, G_Y)`. -/
noncomputable def glueSections.toRelY {W : BigFppfOver B S hS} (s : glueSections D G W) :
    RelativeMorphism B S hS D.Y G.obj.right.left D.X D.f (G.obj.right.hom ≫ D.f)
      (yoneda.obj W) where
  base := s.1
  morphism := s.2.right.left
  commutes := by
    have h : s.2.right.left ≫ G.obj.right.hom = pullback.snd s.1 D.f := Over.w s.2.right
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.f) h)

/-- The `U`-leg of a restricted pair is the restriction of the `U`-leg. -/
theorem glueSections.toRelU_restrict {W W' : BigFppfOver B S hS} (g : W' ⟶ W)
    (s : glueSections D G W) :
    (s.restrict g).toRelU = RelativeMorphism.restrict (yoneda.map g) s.toRelU := by
  have key : ((Over.pullback D.U.ι).map (Over.homMk (yoneda.map g) :
      Over.mk (yoneda.map g ≫ s.1) ⟶ Over.mk s.1)).left =
      (pullback.congrHom (rfl : yoneda.map g ≫ s.1 = yoneda.map g ≫ s.1) rfl).hom ≫
        pullback.map (yoneda.map g ≫ s.1) D.U.ι s.1 D.U.ι (yoneda.map g) (𝟙 D.U.toFunctor) (𝟙 D.X)
          (by simp) (by simp) := by
    apply pullback.hom_ext
    · rw [overPullback_map_left_comp_fst]
      simp [pullback.congrHom]
    · rw [overPullback_map_left_comp_snd]
      simp [pullback.congrHom]
  refine RelativeMorphism.ext_of_base_eq rfl ?_
  exact (congrArg (· ≫ s.2.left.left) key).trans (Category.assoc _ _ _)

/-- The `Y`-leg of a restricted pair is the restriction of the `Y`-leg. -/
theorem glueSections.toRelY_restrict {W W' : BigFppfOver B S hS} (g : W' ⟶ W)
    (s : glueSections D G W) :
    (s.restrict g).toRelY = RelativeMorphism.restrict (yoneda.map g) s.toRelY := by
  have key : ((Over.pullback D.f).map (Over.homMk (yoneda.map g) :
      Over.mk (yoneda.map g ≫ s.1) ⟶ Over.mk s.1)).left =
      (pullback.congrHom (rfl : yoneda.map g ≫ s.1 = yoneda.map g ≫ s.1) rfl).hom ≫
        pullback.map (yoneda.map g ≫ s.1) D.f s.1 D.f (yoneda.map g) (𝟙 D.Y) (𝟙 D.X)
          (by simp) (by simp) := by
    apply pullback.hom_ext
    · rw [overPullback_map_left_comp_fst]
      simp [pullback.congrHom]
    · rw [overPullback_map_left_comp_snd]
      simp [pullback.congrHom]
  refine RelativeMorphism.ext_of_base_eq rfl ?_
  exact (congrArg (· ≫ s.2.right.left) key).trans (Category.assoc _ _ _)

/-- A pair is determined by its two legs. -/
theorem glueSections.eq_of_toRel {W : BigFppfOver B S hS} {s s' : glueSections D G W}
    (hU : s.toRelU = s'.toRelU) (hY : s.toRelY = s'.toRelY) : s = s' := by
  obtain ⟨w, φ⟩ := s
  obtain ⟨w', φ'⟩ := s'
  have hb : w = w' := congrArg RelativeMorphism.base hU
  subst hb
  have hU' := (RelativeMorphism.mk.inj hU).2
  have hY' := (RelativeMorphism.mk.inj hY).2
  have hφ : φ = φ' := Comma.hom_ext _ _ (Over.OverMorphism.ext (eq_of_heq hU'))
    (Over.OverMorphism.ext (eq_of_heq hY'))
  subst hφ
  rfl

variable (D G)

/-- The relative morphism functor `Mor_X(U, G_U)` receiving the `U`-legs. -/
noncomputable abbrev relHomU : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  relativeHom B S hS D.U.toFunctor G.obj.left.left D.X D.U.ι (G.obj.left.hom ≫ D.U.ι)
    (isOpenSubspace_U D).1 G.property.2.1 D.algebraicSpace_X

/-- The relative morphism functor `Mor_X(Y, G_Y)` receiving the `Y`-legs. -/
noncomputable abbrev relHomY : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  relativeHom B S hS D.Y G.obj.right.left D.X D.f (G.obj.right.hom ≫ D.f)
    D.algebraicSpace_Y G.property.2.2 D.algebraicSpace_X

/-- The sections of `Mor_X(U, G_U)` as pairs. -/
noncomputable abbrev relSecU (W : BigFppfOver B S hS) :=
  relativeHomSections B S hS D.U.toFunctor G.obj.left.left D.X D.U.ι (G.obj.left.hom ≫ D.U.ι)
    (isOpenSubspace_U D).1 G.property.2.1 D.algebraicSpace_X W

/-- The sections of `Mor_X(Y, G_Y)` as pairs. -/
noncomputable abbrev relSecY (W : BigFppfOver B S hS) :=
  relativeHomSections B S hS D.Y G.obj.right.left D.X D.f (G.obj.right.hom ≫ D.f)
    D.algebraicSpace_Y G.property.2.2 D.algebraicSpace_X W

/-- The `U`-leg, as a morphism of presheaves into `Mor_X(U, G_U)`. -/
noncomputable def homPresheafLegU : homPresheaf D G ⟶ relHomU D G where
  app W := ↾fun s =>
    (relSecU D G W.unop).symm ((equivShrink (glueSections D G W.unop)).symm s).toRelU
  naturality W W' g := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    apply (relSecU D G W'.unop).injective
    change relSecU D G W'.unop ((relSecU D G W'.unop).symm
        ((equivShrink (glueSections D G W'.unop)).symm (equivShrink (glueSections D G W'.unop)
          (((equivShrink (glueSections D G W.unop)).symm s).restrict g.unop))).toRelU) =
      relSecU D G W'.unop ((relHomU D G).map g.unop.op
        ((relSecU D G W.unop).symm ((equivShrink (glueSections D G W.unop)).symm s).toRelU))
    rw [relativeHomSections_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, glueSections.toRelU_restrict]

/-- The `Y`-leg, as a morphism of presheaves into `Mor_X(Y, G_Y)`. -/
noncomputable def homPresheafLegY : homPresheaf D G ⟶ relHomY D G where
  app W := ↾fun s =>
    (relSecY D G W.unop).symm ((equivShrink (glueSections D G W.unop)).symm s).toRelY
  naturality W W' g := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    apply (relSecY D G W'.unop).injective
    change relSecY D G W'.unop ((relSecY D G W'.unop).symm
        ((equivShrink (glueSections D G W'.unop)).symm (equivShrink (glueSections D G W'.unop)
          (((equivShrink (glueSections D G W.unop)).symm s).restrict g.unop))).toRelY) =
      relSecY D G W'.unop ((relHomY D G).map g.unop.op
        ((relSecY D G W.unop).symm ((equivShrink (glueSections D G W.unop)).symm s).toRelY))
    rw [relativeHomSections_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, glueSections.toRelY_restrict]

variable {D G}

/-- Restricting along `Over.homMk t` is the comparison map of fibre products. -/
theorem overPullback_map_homMk_left {C : Type*} [Category C] [HasPullbacks C] {W W' X Z : C}
    (t : W' ⟶ W) (a : W ⟶ X) (z : Z ⟶ X) :
    ((Over.pullback z).map (Over.homMk t : Over.mk (t ≫ a) ⟶ Over.mk a)).left =
      pullback.map (t ≫ a) z a z t (𝟙 Z) (𝟙 X) (by simp) (by simp) := by
  apply pullback.hom_ext
  · rw [overPullback_map_left_comp_fst]
    simp
  · rw [overPullback_map_left_comp_snd]
    simp

/-- **The compatibility over `V` of a pair of legs is local on the test object.** Let
`φl : Φ_U(W, b) ⟶ G_U` and `φr : Φ_Y(W, b) ⟶ G_Y` be the two legs of a would-be morphism of
glueing data. If after restriction along every member of a covering sieve they are the legs of a
morphism of glueing data, then they are compatible over `V`. -/
theorem commaHom_w_of_local {W : BigFppfOver B S hS} {R : Sieve W}
    (hR : R ∈ BigFppfOver.topology B S hS W) (b : yoneda.obj W ⟶ D.X)
    (φl : (Over.pullback D.U.ι).obj (Over.mk b) ⟶ G.obj.left)
    (φr : (Over.pullback D.f).obj (Over.mk b) ⟶ G.obj.right)
    (h : ∀ ⦃W' : BigFppfOver B S hS⦄ (g : W' ⟶ W), R g →
      ∃ ψ : (restrictionDiagram D).obj (Over.mk (yoneda.map g ≫ b)) ⟶ G.obj,
        ψ.left = (Over.pullback D.U.ι).map (Over.homMk (yoneda.map g) :
          Over.mk (yoneda.map g ≫ b) ⟶ Over.mk b) ≫ φl ∧
        ψ.right = (Over.pullback D.f).map (Over.homMk (yoneda.map g) :
          Over.mk (yoneda.map g ≫ b) ⟶ Over.mk b) ≫ φr) :
    (Over.pullback (D.U.fromPreimage D.f)).map φl ≫ G.obj.hom =
      ((restrictionDiagram D).obj (Over.mk b)).hom ≫ (Over.pullback D.V.ι).map φr := by
  have hE : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (pullback G.obj.right.hom D.V.ι) :=
    (isAlgebraicSpace_pullback B S hS G.obj.right.hom D.V.ι G.property.2.2
      (isOpenSubspace_V D).1 D.algebraicSpace_Y).isSheaf
  refine Over.OverMorphism.ext ?_
  refine eq_of_isSeparatedFor_of_isPullback hR hE
    (pullback.fst (pullback.snd b D.U.ι) (D.U.fromPreimage D.f) ≫ pullback.fst b D.U.ι) _ _ ?_
  intro W' g hg
  obtain ⟨⟨ψl, ψr, hw⟩, hψl, hψr⟩ := h g hg
  dsimp only at hψl hψr
  subst hψl hψr
  set k : Over.mk (yoneda.map g ≫ b) ⟶ Over.mk b := Over.homMk (yoneda.map g) with hkdef
  have h1 := isPullback_overPullback_map_left D.U.ι k
  have h2 := isPullback_overPullback_map_left (D.U.fromPreimage D.f)
    ((Over.pullback D.U.ι).map k)
  refine ⟨_, ((Over.pullback (D.U.fromPreimage D.f)).map ((Over.pullback D.U.ι).map k)).left,
    pullback.fst (pullback.snd (yoneda.map g ≫ b) D.U.ι) (D.U.fromPreimage D.f) ≫
      pullback.fst (yoneda.map g ≫ b) D.U.ι, h2.paste_vert h1, ?_⟩
  have hw' : (Over.pullback (D.U.fromPreimage D.f)).map
      ((Over.pullback D.U.ι).map k ≫ φl) ≫ G.obj.hom =
      (restrictionComparison D).hom.app (Over.mk (yoneda.map g ≫ b)) ≫
        (Over.pullback D.V.ι).map ((Over.pullback D.f).map k ≫ φr) := hw
  have nat : (Over.pullback (D.U.fromPreimage D.f)).map ((Over.pullback D.U.ι).map k) ≫
      (restrictionComparison D).hom.app (Over.mk b) =
      (restrictionComparison D).hom.app (Over.mk (yoneda.map g ≫ b)) ≫
        (Over.pullback D.V.ι).map ((Over.pullback D.f).map k) :=
    (restrictionComparison D).hom.naturality k
  have e : (Over.pullback (D.U.fromPreimage D.f)).map ((Over.pullback D.U.ι).map k) ≫
      (Over.pullback (D.U.fromPreimage D.f)).map φl ≫ G.obj.hom =
    (Over.pullback (D.U.fromPreimage D.f)).map ((Over.pullback D.U.ι).map k) ≫
      (restrictionComparison D).hom.app (Over.mk b) ≫ (Over.pullback D.V.ι).map φr := by
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hw', reassoc_of% nat,
      CategoryTheory.Functor.map_comp]
  exact congrArg CommaMorphism.left e

/-- A pair whose legs are the restrictions of two pairs of Stacks 05Y1 with a common base `b`
along `g` is, up to rewriting its first component, a morphism of glueing data at `g ≫ b`
whose legs are the restrictions of the two given morphisms. -/
theorem glueSections.exists_of_toRel_eq_restrict {W W' : BigFppfOver B S hS} (g : W' ⟶ W)
    {b : yoneda.obj W ⟶ D.X} {mU : pullback b D.U.ι ⟶ G.obj.left.left}
    {mY : pullback b D.f ⟶ G.obj.right.left} (cU cY)
    (hcU : mU ≫ G.obj.left.hom = pullback.snd b D.U.ι)
    (hcY : mY ≫ G.obj.right.hom = pullback.snd b D.f)
    (s : glueSections D G W')
    (hU : s.toRelU = RelativeMorphism.restrict (yoneda.map g) ⟨b, mU, cU⟩)
    (hY : s.toRelY = RelativeMorphism.restrict (yoneda.map g) ⟨b, mY, cY⟩) :
    ∃ ψ : (restrictionDiagram D).obj (Over.mk (yoneda.map g ≫ b)) ⟶ G.obj,
      ψ.left = (Over.pullback D.U.ι).map (Over.homMk (yoneda.map g) :
          Over.mk (yoneda.map g ≫ b) ⟶ Over.mk b) ≫ Over.homMk mU hcU ∧
        ψ.right = (Over.pullback D.f).map (Over.homMk (yoneda.map g) :
          Over.mk (yoneda.map g ≫ b) ⟶ Over.mk b) ≫ Over.homMk mY hcY := by
  obtain ⟨w', φ'⟩ := s
  obtain ⟨hw, hm⟩ := RelativeMorphism.mk.inj hU
  dsimp only at hw
  subst hw
  obtain ⟨-, hm'⟩ := RelativeMorphism.mk.inj hY
  refine ⟨φ', Over.OverMorphism.ext ?_, Over.OverMorphism.ext ?_⟩
  · refine (eq_of_heq hm).trans ?_
    simp only [Over.comp_left, Over.homMk_left]
    rw [overPullback_map_homMk_left]
  · refine (eq_of_heq hm').trans ?_
    simp only [Over.comp_left, Over.homMk_left]
    rw [overPullback_map_homMk_left]

variable (D G)

/-- **The presheaf of glueing-data morphisms into `G` is an fppf sheaf.** The two legs glue in
the relative morphism sheaves of Stacks 05Y3, their bases agree because `X` is separated, and
the two conditions making the glued legs a morphism of glueing data — the `Y`-leg lies over
`Y`, and the legs are compatible over `V` — hold because they hold locally. -/
theorem isSheaf_homPresheaf :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (homPresheaf D G) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro W R hR x hx
  have hXs := ((isSheaf_iff_isSheaf_of_type _ _).1 D.algebraicSpace_X.isSheaf) R hR
  have hUs := ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_relativeHom B S hS _ _ _ D.U.ι
    (G.obj.left.hom ≫ D.U.ι) (isOpenSubspace_U D).1 G.property.2.1 D.algebraicSpace_X)) R hR
  have hYs := ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_relativeHom B S hS _ _ _ D.f
    (G.obj.right.hom ≫ D.f) D.algebraicSpace_Y G.property.2.2 D.algebraicSpace_X)) R hR
  obtain ⟨qU, hqU, hqUu⟩ := hUs (x.map (homPresheafLegU D G)) (hx.map _)
  obtain ⟨qY, hqY, hqYu⟩ := hYs (x.map (homPresheafLegY D G)) (hx.map _)
  have hxU : ∀ ⦃W' : BigFppfOver B S hS⦄ (g : W' ⟶ W) (hg : R g),
      ((equivShrink (glueSections D G W')).symm (x g hg)).toRelU =
        RelativeMorphism.restrict (yoneda.map g) (relSecU D G W qU) := by
    intro W' g hg
    rw [← relativeHomSections_map, hqU g hg]
    exact (Equiv.apply_symm_apply _ _).symm
  have hxY : ∀ ⦃W' : BigFppfOver B S hS⦄ (g : W' ⟶ W) (hg : R g),
      ((equivShrink (glueSections D G W')).symm (x g hg)).toRelY =
        RelativeMorphism.restrict (yoneda.map g) (relSecY D G W qY) := by
    intro W' g hg
    rw [← relativeHomSections_map, hqY g hg]
    exact (Equiv.apply_symm_apply _ _).symm
  obtain ⟨rU, hrU⟩ : ∃ r, relSecU D G W qU = r := ⟨_, rfl⟩
  obtain ⟨rY, hrY⟩ : ∃ r, relSecY D G W qY = r := ⟨_, rfl⟩
  simp only [hrU] at hxU
  simp only [hrY] at hxY
  obtain ⟨b, mU, cU⟩ := rU
  obtain ⟨bY, mY, cY⟩ := rY
  have hb : bY = b := by
    apply yonedaEquiv.injective
    refine hXs.isSeparatedFor.ext fun W' g hg => ?_
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    exact congrArg yonedaEquiv ((congrArg RelativeMorphism.base (hxY g hg)).symm.trans
      (congrArg RelativeMorphism.base (hxU g hg)))
  subst hb
  have hcU : mU ≫ G.obj.left.hom = pullback.snd bY D.U.ι := by
    rw [← cancel_mono D.U.ι, Category.assoc]
    exact cU
  have hcY : mY ≫ G.obj.right.hom = pullback.snd bY D.f := by
    refine eq_of_isSeparatedFor_of_isPullback hR D.algebraicSpace_Y.isSheaf
      (pullback.fst bY D.f) _ _ fun W' g hg => ?_
    refine ⟨_, pullback.map (yoneda.map g ≫ bY) D.f bY D.f (yoneda.map g) (𝟙 _) (𝟙 _)
      (by simp) (by simp), pullback.fst _ _, ?_, ?_⟩
    · rw [pullback.map_id_eq_mapFst]
      exact (pullback.isPullback_mapFst _ _ _).flip
    · have hP : ((equivShrink (glueSections D G W')).symm (x g hg)).toRelY.morphism ≫
          G.obj.right.hom = pullback.snd
            ((equivShrink (glueSections D G W')).symm (x g hg)).toRelY.base D.f :=
        Over.w ((equivShrink (glueSections D G W')).symm (x g hg)).2.right
      rw [hxY g hg] at hP
      simp only [RelativeMorphism.restrict_morphism, RelativeMorphism.restrict_base,
        Category.assoc] at hP
      rw [hP, pullback.lift_snd, Category.comp_id]
  have hw := commaHom_w_of_local hR bY (Over.homMk mU hcU) (Over.homMk mY hcY)
    fun W' g hg => glueSections.exists_of_toRel_eq_restrict g cU cY hcU hcY _ (hxU g hg)
      (hxY g hg)
  let t : glueSections D G W := ⟨bY, ⟨Over.homMk mU hcU, Over.homMk mY hcY, hw⟩⟩
  have htU : t.toRelU = ⟨bY, mU, cU⟩ := rfl
  have htY : t.toRelY = ⟨bY, mY, cY⟩ := rfl
  refine ⟨equivShrink _ t, fun W' g hg => ?_, fun t' ht' => ?_⟩
  · apply (equivShrink (glueSections D G W')).symm.injective
    show (equivShrink (glueSections D G W')).symm (equivShrink (glueSections D G W')
      (((equivShrink (glueSections D G W)).symm (equivShrink _ t)).restrict g)) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact glueSections.eq_of_toRel
      (by rw [glueSections.toRelU_restrict, htU, hxU g hg])
      (by rw [glueSections.toRelY_restrict, htY, hxY g hg])
  · apply (equivShrink (glueSections D G W)).symm.injective
    rw [Equiv.symm_apply_apply]
    have hU' := hqUu ((homPresheafLegU D G).app _ t') fun W' g hg => by
      rw [← NatTrans.naturality_apply, ht' g hg]
      rfl
    have hY' := hqYu ((homPresheafLegY D G).app _ t') fun W' g hg => by
      rw [← NatTrans.naturality_apply, ht' g hg]
      rfl
    refine glueSections.eq_of_toRel ?_ ?_
    · rw [htU, ← hrU, ← hU']
      exact (Equiv.apply_symm_apply _ _).symm
    · rw [htY, ← hrY, ← hY']
      exact (Equiv.apply_symm_apply _ _).symm

end AlgebraicGeometry.Space.FormalGlueingSituation

end
