module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleObject

/-!
# Sections of an inverse image over a limit of schemes: the surjectivity half

Let `X = lim X_i` be the limit of a cofiltered inverse system of schemes with affine transition
morphisms, let `H` be an abelian sheaf on the small étale site of a stage `X_i` and let `V₀` be a
quasi-compact and quasi-separated object of that site, with base changes `V_j = V₀ ×_{X_i} X_j`
and `V = V₀ ×_{X_i} X`. Then

`(f_i⁻¹H)(V) = colim_j (f_{ji}⁻¹H)(V_j)`,

which is the degree zero case of Stacks 09YQ for the system of inverse images of a single sheaf
(Stacks 09YN in the étale setting). The injectivity half is
`Stacks.EtaleCohomology.exists_unitApp_eq_zero_of_isLimit`; this file proves the surjectivity
half, `Stacks.EtaleCohomology.exists_pullbackSectionsMap_eq_of_isLimit`.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleBaseChangeHomMk`: the morphism into a base change
  `W ×_Y X` of an object of the small étale site determined by its first component.

## Main results

* `Stacks.EtaleCohomology.pullbackSectionsMap_map_unitApp`: the comparison of sections of
  iterated inverse images, on the restriction of the image of a section under the unit.
* `Stacks.EtaleCohomology.exists_pullbackSectionsMap_eq_of_isLimit`: **the surjectivity half**
  of the degree zero colimit formula.

## Implementation notes

The proof follows the source. A section over `V` is étale locally on `V` the restriction of the
image of a section of `H` under the unit (`exists_covering_smallEtalePullbackAb_eq_unitApp`);
finitely many affine objects `A` of the small étale site of `X` carry such descriptions and cover
`V`. Each `A`, together with its morphisms to `V` and to the object `W ×_{X_i} X` carrying the
section of `H`, comes from a stage (Stacks 01ZM, 07RP, 01ZC), giving local sections over objects
`Z_A` of a stage `X_j`. The images of the `Z_A` in `V_j` form an open containing the image of
`V`, so at a later stage `V_k` is covered by the base changes of the `Z_A` (Stacks 01Z4); at a
still later stage the local sections agree on the overlaps (the injectivity half), and there they
glue to the required section.

All the sections that occur are restrictions of images of sections of `H` under units, and all
the comparisons between them reduce, through `pullbackSectionsMap_map_unitApp`, to equalities of
morphisms of schemes into the objects carrying the sections of `H`. Data defined over different
stages are moved to a common one with `AlgebraicGeometry.common_stage_of_finite`, the stages being
the objects of `Over i`, which packages a stage with its transition morphism.

## References

* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Morphisms into a base change -/

section HomMk

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The morphism `U ⟶ W ×_Y X` of the small étale site of `X` with first component
`r : U ⟶ W`. -/
def smallEtaleBaseChangeHomMk {U : X.Etale} {W : Y.Etale} (r : U.left ⟶ W.left)
    (hr : r ≫ W.hom = U.hom ≫ f) : U ⟶ (smallEtaleBaseChange f).obj W :=
  MorphismProperty.Over.homMk (pullback.lift r U.hom hr) (pullback.lift_snd _ _ _) trivial

/-- The first component of `smallEtaleBaseChangeHomMk f r hr` is `r`. -/
@[reassoc (attr := simp)]
lemma smallEtaleBaseChangeHomMk_left_fst {U : X.Etale} {W : Y.Etale} (r : U.left ⟶ W.left)
    (hr : r ≫ W.hom = U.hom ≫ f) :
    (smallEtaleBaseChangeHomMk f r hr).left ≫ pullback.fst W.hom f = r :=
  pullback.lift_fst _ _ _

/-- The first component of a morphism into a base change lies over the base change morphism. -/
lemma smallEtaleBaseChange_left_fst_hom {U : X.Etale} {W : Y.Etale}
    (k : U ⟶ (smallEtaleBaseChange f).obj W) :
    (k.left ≫ pullback.fst W.hom f) ≫ W.hom = U.hom ≫ f :=
  (Category.assoc _ _ _).trans ((congrArg (fun φ => k.left ≫ φ)
    (pullback.condition (f := W.hom) (g := f))).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun φ => φ ≫ f) (smallEtaleBaseChange_w f k))))

end HomMk

/-! ### Sections given by units -/

/-- Restricting a section of an abelian presheaf along two composable morphisms is restricting it
along the composite. -/
lemma presheaf_map_map_apply {C : Type*} [Category* C] (P : Cᵒᵖ ⥤ Ab.{u + 1}) {U V W : C}
    (k : U ⟶ V) (k' : V ⟶ W) (x : ToType (P.obj (op W))) :
    P.map k.op (P.map k'.op x) = P.map (k ≫ k').op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

section Units

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (H : Sheaf (smallEtaleTopology Y) Ab.{u + 1})

/-- Restricting along two morphisms into a base change with the same first component gives the
same section. -/
lemma map_eq_map_of_left_fst {U : X.Etale} {W : Y.Etale}
    (k k' : U ⟶ (smallEtaleBaseChange f).obj W)
    (h : k.left ≫ pullback.fst W.hom f = k'.left ≫ pullback.fst W.hom f)
    (x : ToType (((smallEtalePullbackAb f).obj H).obj.obj (op ((smallEtaleBaseChange f).obj W)))) :
    ((smallEtalePullbackAb f).obj H).obj.map k.op x =
      ((smallEtalePullbackAb f).obj H).obj.map k'.op x := by
  rw [smallEtaleBaseChange_hom_ext f h]

variable {X' : Scheme.{u}} (g : X' ⟶ X) (gf : X' ⟶ Y) (hgf : gf = g ≫ f)

/-- **The comparison of sections of iterated inverse images, on units.** The comparison
`(f⁻¹H)(U) ⟶ ((gf)⁻¹H)(U ×_X X')` carries the restriction of the image of a section `h` of `H`
under the unit along `k : U ⟶ W ×_Y X` to the restriction of the image of `h` under the unit of
`gf` along any morphism `U ×_X X' ⟶ W ×_Y X'` with the same first component. -/
lemma pullbackSectionsMap_map_unitApp {U : X.Etale} {W : Y.Etale}
    (k : U ⟶ (smallEtaleBaseChange f).obj W) (h : ToType (H.obj.obj (op W)))
    (k' : (smallEtaleBaseChange g).obj U ⟶ (smallEtaleBaseChange gf).obj W)
    (hk' : k'.left ≫ pullback.fst W.hom gf =
      pullback.fst U.hom g ≫ k.left ≫ pullback.fst W.hom f) :
    pullbackSectionsMap g f gf hgf H U
        (((smallEtalePullbackAb f).obj H).obj.map k.op (smallEtalePullbackAbUnitApp f H W h)) =
      ((smallEtalePullbackAb gf).obj H).obj.map k'.op (smallEtalePullbackAbUnitApp gf H W h) := by
  rw [pullbackSectionsMap_naturality]
  have hu := pullbackSectionsMap_unitApp g f gf hgf H W h
  have hu' : pullbackSectionsMap g f gf hgf H _ (smallEtalePullbackAbUnitApp f H W h) =
      ((smallEtalePullbackAb gf).obj H).obj.map
        ((smallEtaleBaseChangeComp' g f gf hgf).inv.app W).op
        (smallEtalePullbackAbUnitApp gf H W h) := by
    rw [← hu, presheaf_map_map_apply, Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id,
      ConcreteCategory.id_apply]
  rw [hu', presheaf_map_map_apply]
  refine map_eq_map_of_left_fst gf H _ _ ?_ _
  have h₁ := smallEtaleBaseChangeComp'_fst_fst g f gf hgf W
  have h₂ : ((smallEtaleBaseChangeComp' g f gf hgf).inv.app W).left ≫
      ((smallEtaleBaseChangeComp' g f gf hgf).hom.app W).left = 𝟙 _ :=
    congrArg (fun φ => φ.left) ((smallEtaleBaseChangeComp' g f gf hgf).inv_hom_id_app W)
  have hi : ((smallEtaleBaseChangeComp' g f gf hgf).inv.app W).left ≫ pullback.fst W.hom gf =
      pullback.fst ((smallEtaleBaseChange f).obj W).hom g ≫ pullback.fst W.hom f :=
    (congrArg (fun φ => ((smallEtaleBaseChangeComp' g f gf hgf).inv.app W).left ≫ φ)
      h₁.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun φ => φ ≫ pullback.fst ((smallEtaleBaseChange f).obj W).hom g ≫
          pullback.fst W.hom f) h₂).trans (Category.id_comp _)))
  have hm := smallEtaleBaseChange_map_left_fst g k
  show (((smallEtaleBaseChange g).map k).left ≫
      ((smallEtaleBaseChangeComp' g f gf hgf).inv.app W).left) ≫ pullback.fst W.hom gf =
    k'.left ≫ pullback.fst W.hom gf
  rw [hk']
  exact (Category.assoc _ _ _).trans ((congrArg (fun φ => ((smallEtaleBaseChange g).map k).left ≫ φ)
    hi).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun φ => φ ≫ pullback.fst W.hom f) hm).trans (Category.assoc _ _ _))))

/-- A section dying under the unit has vanishing comparison to the inverse image along the
composite. -/
lemma pullbackSectionsMap_eq_zero_of_unitApp_eq_zero {U : X.Etale}
    (y : ToType (((smallEtalePullbackAb f).obj H).obj.obj (op U)))
    (hy : smallEtalePullbackAbUnitApp g ((smallEtalePullbackAb f).obj H) U y = 0) :
    pullbackSectionsMap g f gf hgf H U y = 0 := by
  rw [pullbackSectionsMap, ConcreteCategory.comp_apply, hy, map_zero]

include g hgf in
/-- **Vanishing under a unit persists along a composite.** -/
lemma unitApp_eq_zero_of_comp {U : Y.Etale} (h : ToType (H.obj.obj (op U)))
    (hz : smallEtalePullbackAbUnitApp f H U h = 0) : smallEtalePullbackAbUnitApp gf H U h = 0 := by
  rw [← pullbackSectionsMap_unitApp g f gf hgf H U h, hz, map_zero, map_zero]

end Units

/-! ### Local affine pieces -/

/-- A covering sieve of an object of the small étale site contains, through each point, a
morphism from an object with affine underlying scheme. -/
lemma exists_isAffine_mem_range_of_mem_smallEtaleTopology {X : Scheme.{u}} {U : X.Etale}
    (S : Sieve U) (hS : S ∈ smallEtaleTopology X U) (x : U.left) :
    ∃ (A : X.Etale) (g : A ⟶ U), IsAffine A.left ∧ S g ∧ x ∈ Set.range g.left := by
  obtain ⟨U', g, hg, y, rfl⟩ := exists_mem_range_of_mem_smallEtaleTopology S hS x
  obtain ⟨W, hW, hy, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)
  have : IsAffine (W : Scheme.{u}) := hW
  let A : X.Etale := Scheme.Etale.mk (W.ι ≫ U'.hom)
  let a : A ⟶ U' := MorphismProperty.Over.homMk W.ι rfl trivial
  refine ⟨A, a ≫ g, hW, S.downward_closed hg a, ⟨⟨y, hy⟩, ?_⟩⟩
  exact rfl

/-! ### Descending affine pieces with two morphisms -/

section Descent

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- The data describing an object `A` of the small étale site of the limit, with two morphisms
into base changes `V₀ ×_{X_i} X` and `W ×_{X_i} X`, at a stage `e : X_j ⟶ X_i`: an object `Z` of
the small étale site of `X_j` presenting `A` as its base change, and morphisms from `Z` into the
base changes of `V₀` and `W` to `X_j` inducing the given ones. -/
def StageDescent {i : I} (A : c.pt.Etale) (V₀ W : (D.obj i).Etale)
    (gV : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)
    (gW : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj W) {j : I} (e : j ⟶ i) : Prop :=
  ∃ (Z : (D.obj j).Etale) (θ : A.left ⟶ Z.left)
    (ψ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj V₀)
    (χ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj W),
    CompactSpace Z.left ∧ QuasiSeparatedSpace Z.left ∧ IsPullback θ A.hom Z.hom (c.π.app j) ∧
      θ ≫ ψ.left ≫ pullback.fst V₀.hom (D.map e) = gV.left ≫ pullback.fst V₀.hom (c.π.app i) ∧
      θ ≫ χ.left ≫ pullback.fst W.hom (D.map e) = gW.left ≫ pullback.fst W.hom (c.π.app i)

variable {D c}

/-- A descent of an object with two morphisms persists along later stages. -/
lemma StageDescent.of_le {i : I} {A : c.pt.Etale} {V₀ W : (D.obj i).Etale}
    {gV : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀}
    {gW : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj W} {j : I} {e : j ⟶ i}
    (h : StageDescent D c A V₀ W gV gW e) {j' : I} (f : j' ⟶ j) (e' : j' ⟶ i)
    (hfe : f ≫ e = e') : StageDescent D c A V₀ W gV gW e' := by
  obtain ⟨Z, θ, ψ, χ, hZc, hZs, hθ, hψ, hχ⟩ := h
  have hDe : D.map e' = D.map f ≫ D.map e := by rw [← hfe, D.map_comp]
  have : Etale (pullback.snd Z.hom (D.map f)) := by
    have : Etale Z.hom := Z.prop
    infer_instance
  let Z' : (D.obj j').Etale := Scheme.Etale.mk (pullback.snd Z.hom (D.map f))
  let θ' : A.left ⟶ Z'.left :=
    pullback.lift θ (A.hom ≫ c.π.app j') (by rw [hθ.w, Category.assoc, c.w])
  have hr : ∀ {V : (D.obj i).Etale} (φ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj V),
      (pullback.fst Z.hom (D.map f) ≫ φ.left ≫ pullback.fst V.hom (D.map e)) ≫ V.hom =
        Z'.hom ≫ D.map e' := fun φ =>
    (Category.assoc _ _ _).trans ((congrArg (pullback.fst Z.hom (D.map f) ≫ ·)
      (smallEtaleBaseChange_left_fst_hom (D.map e) φ)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ D.map e) (pullback.condition (f := Z.hom) (g := D.map f))).trans
          ((Category.assoc _ _ _).trans (congrArg (pullback.snd Z.hom (D.map f) ≫ ·) hDe.symm)))))
  have hfst : ∀ {V : (D.obj i).Etale} (φ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj V),
      θ' ≫ (smallEtaleBaseChangeHomMk (D.map e') (U := Z')
            (pullback.fst Z.hom (D.map f) ≫ φ.left ≫ pullback.fst V.hom (D.map e)) (hr φ)).left ≫
            pullback.fst V.hom (D.map e') =
        θ ≫ φ.left ≫ pullback.fst V.hom (D.map e) := fun φ =>
    (congrArg (θ' ≫ ·) (smallEtaleBaseChangeHomMk_left_fst _ _ (hr φ))).trans
      (pullback.lift_fst_assoc _ _ _ _)
  have hP : IsPullback θ' A.hom Z'.hom (c.π.app j') := isPullback_lift_of_isPullback D c hθ f
  exact ⟨Z', θ', _, _, compactSpace_smallEtaleBaseChange_obj (D.map f) Z hZc,
    quasiSeparatedSpace_smallEtaleBaseChange_obj (D.map f) Z hZs, hP,
    (hfst ψ).trans hψ, (hfst χ).trans hχ⟩

variable (D c)

/-- **An affine object of the small étale site of the limit, with two morphisms into base changes
of objects of a stage, descends to a later stage** (Stacks 01ZM, 07RP, 01ZC), as soon as the
first of the two objects of the stage is quasi-compact and quasi-separated. -/
lemma exists_stageDescent (hc : IsLimit c) {i : I} (A : c.pt.Etale) [IsAffine A.left]
    (V₀ W : (D.obj i).Etale) [CompactSpace V₀.left] [QuasiSeparatedSpace V₀.left]
    (gV : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)
    (gW : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj W) :
    ∃ (j : I) (e : j ⟶ i), StageDescent D c A V₀ W gV gW e := by
  have : Etale A.hom := A.prop
  have : Etale V₀.hom := V₀.prop
  have : CompactSpace ((𝟭 Scheme.{u}).obj A.left) := inferInstanceAs (CompactSpace A.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj A.left) :=
    inferInstanceAs (QuasiSeparatedSpace A.left)
  have : CompactSpace ((𝟭 Scheme.{u}).obj V₀.left) := inferInstanceAs (CompactSpace V₀.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj V₀.left) :=
    inferInstanceAs (QuasiSeparatedSpace V₀.left)
  obtain ⟨l, -, Y, p, θ, hp, hYc, hYs, hθ⟩ := exists_isPullback_etale_of_isLimit_of_hom D c hc
    V₀.hom A.hom (gV.left ≫ pullback.fst V₀.hom (c.π.app i))
    (smallEtaleBaseChange_left_fst_hom _ gV)
  let l₁ := IsCofiltered.min l i
  let a : l₁ ⟶ l := IsCofiltered.minToLeft l i
  let b : l₁ ⟶ i := IsCofiltered.minToRight l i
  have hθ₁ := isPullback_lift_of_isPullback D c hθ a
  have hP₁ : CompactSpace ↥(pullback p (D.map a)) :=
    compactSpace_smallEtaleBaseChange_obj (D.map a) (Scheme.Etale.mk p) hYc
  have hP₂ : QuasiSeparatedSpace ↥(pullback p (D.map a)) :=
    quasiSeparatedSpace_smallEtaleBaseChange_obj (D.map a) (Scheme.Etale.mk p) hYs
  have : Etale (pullback.fst V₀.hom W.hom ≫ V₀.hom) := by
    have : Etale V₀.hom := V₀.prop
    have : Etale W.hom := W.prop
    infer_instance
  obtain ⟨l₂, b₂, g, hg₁, hg₂⟩ := exists_hom_of_isPullback_of_isLimit' D c hc b hθ₁
    (pullback.fst V₀.hom W.hom ≫ V₀.hom)
    (pullback.lift (gV.left ≫ pullback.fst V₀.hom (c.π.app i))
      (gW.left ≫ pullback.fst W.hom (c.π.app i))
      ((smallEtaleBaseChange_left_fst_hom _ gV).trans
        (smallEtaleBaseChange_left_fst_hom _ gW).symm))
    (by rw [pullback.lift_fst_assoc, smallEtaleBaseChange_left_fst_hom])
  have : Etale (pullback.snd (pullback.snd p (D.map a)) (D.map b₂)) := by
    have : Etale (pullback.snd p (D.map a)) := inferInstance
    infer_instance
  let Z : (D.obj l₂).Etale := Scheme.Etale.mk (pullback.snd (pullback.snd p (D.map a)) (D.map b₂))
  have hZ : (pullback.fst (pullback.snd p (D.map a)) (D.map b₂) ≫ pullback.snd p (D.map a)) ≫
      D.map b = pullback.snd (pullback.snd p (D.map a)) (D.map b₂) ≫ D.map (b₂ ≫ b) := by
    rw [pullback.condition, Category.assoc, D.map_comp]
  refine ⟨l₂, b₂ ≫ b, Z, _,
    smallEtaleBaseChangeHomMk (D.map (b₂ ≫ b)) (g ≫ pullback.fst V₀.hom W.hom)
      ((Category.assoc _ _ _).trans (hg₂.trans (by rw [← Category.assoc]; exact hZ))),
    smallEtaleBaseChangeHomMk (D.map (b₂ ≫ b)) (g ≫ pullback.snd V₀.hom W.hom)
      ((Category.assoc _ _ _).trans ((congrArg (g ≫ ·) pullback.condition.symm).trans
        ((Category.assoc _ _ _).symm.trans (hg₂.trans (by rw [← Category.assoc]; exact hZ))))),
    compactSpace_smallEtaleBaseChange_obj (D.map b₂) (Scheme.Etale.mk (pullback.snd p (D.map a)))
      hP₁,
    quasiSeparatedSpace_smallEtaleBaseChange_obj (D.map b₂)
      (Scheme.Etale.mk (pullback.snd p (D.map a))) hP₂,
    isPullback_lift_of_isPullback D c hθ₁ b₂, ?_, ?_⟩
  · rw [smallEtaleBaseChangeHomMk_left_fst]
    exact ((reassoc_of% hg₁) _).trans (pullback.lift_fst _ _ _)
  · rw [smallEtaleBaseChangeHomMk_left_fst]
    exact ((reassoc_of% hg₁) _).trans (pullback.lift_snd _ _ _)

/-- Two morphisms into an iterated base change agree as soon as their first components into the
original object agree. -/
lemma smallEtaleBaseChange_baseChange_hom_ext {X Y Z : Scheme.{u}} (g : Z ⟶ X) (f : X ⟶ Y)
    {A : Z.Etale} {V : Y.Etale}
    {p q : A ⟶ (smallEtaleBaseChange g).obj ((smallEtaleBaseChange f).obj V)}
    (h : p.left ≫ pullback.fst ((smallEtaleBaseChange f).obj V).hom g ≫ pullback.fst V.hom f =
      q.left ≫ pullback.fst ((smallEtaleBaseChange f).obj V).hom g ≫ pullback.fst V.hom f) :
    p = q := by
  refine smallEtaleBaseChange_hom_ext g (pullback.hom_ext ?_ ?_)
  · exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (((smallEtaleBaseChange_fst_snd g f p).trans
      (smallEtaleBaseChange_fst_snd g f q).symm).trans (Category.assoc _ _ _).symm)

variable {D c} in
/-- The restriction of the section given by a stage descent to the object of the limit is the
given restriction of the image of the section of `H` under the unit. -/
lemma StageDescent.map_pullbackSectionsMap {i : I} (H : Sheaf (smallEtaleTopology (D.obj i)) Ab)
    {A : c.pt.Etale} {W : (D.obj i).Etale} {gW : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj W}
    {j : I} (e : j ⟶ i) {Z : (D.obj j).Etale} {θ : A.left ⟶ Z.left}
    (hθ : θ ≫ Z.hom = A.hom ≫ c.π.app j) (χ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj W)
    (hχ : θ ≫ χ.left ≫ pullback.fst W.hom (D.map e) = gW.left ≫ pullback.fst W.hom (c.π.app i))
    (h : ToType (H.obj.obj (op W))) :
    ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map
        (smallEtaleBaseChangeHomMk (c.π.app j) θ hθ).op
        (pullbackSectionsMap (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H Z
          (((smallEtalePullbackAb (D.map e)).obj H).obj.map χ.op
            (smallEtalePullbackAbUnitApp (D.map e) H W h))) =
      ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map gW.op
        (smallEtalePullbackAbUnitApp (c.π.app i) H W h) := by
  have hk : (pullback.fst Z.hom (c.π.app j) ≫ χ.left ≫ pullback.fst W.hom (D.map e)) ≫ W.hom =
      ((smallEtaleBaseChange (c.π.app j)).obj Z).hom ≫ c.π.app i := by
    rw [Category.assoc, smallEtaleBaseChange_left_fst_hom, ← Category.assoc, pullback.condition,
      Category.assoc, c.w]
    rfl
  rw [pullbackSectionsMap_map_unitApp (D.map e) H (c.π.app j) (c.π.app i) (c.w e).symm χ h
    (smallEtaleBaseChangeHomMk (c.π.app i) _ hk) (smallEtaleBaseChangeHomMk_left_fst _ _ _)]
  refine (presheaf_map_map_apply _ _ _ _).trans (map_eq_map_of_left_fst (c.π.app i) H _ _ ?_ _)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (smallEtaleBaseChangeHomMk_left_fst _ _ _)).trans
      ((smallEtaleBaseChangeHomMk_left_fst_assoc _ _ _ _).trans hχ))

variable {D c} in
/-- The morphism into the base change of the first object, read through a stage descent. -/
lemma StageDescent.comp_baseChangeComp {i : I} {A : c.pt.Etale} {V₀ : (D.obj i).Etale}
    {gV : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀} {j : I} (e : j ⟶ i)
    {Z : (D.obj j).Etale} {θ : A.left ⟶ Z.left} (hθ : θ ≫ Z.hom = A.hom ≫ c.π.app j)
    (ψ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj V₀)
    (hψ : θ ≫ ψ.left ≫ pullback.fst V₀.hom (D.map e) = gV.left ≫ pullback.fst V₀.hom (c.π.app i)) :
    gV ≫ (smallEtaleBaseChangeComp' (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm).hom.app V₀ =
      smallEtaleBaseChangeHomMk (c.π.app j) θ hθ ≫ (smallEtaleBaseChange (c.π.app j)).map ψ := by
  refine smallEtaleBaseChange_baseChange_hom_ext (c.π.app j) (D.map e) ?_
  refine (Category.assoc _ _ _).trans ((congrArg (gV.left ≫ ·)
    (smallEtaleBaseChangeComp'_fst_fst _ _ _ _ V₀)).trans ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)
  refine Eq.trans ?_ (congrArg (_ ≫ · ≫ pullback.fst V₀.hom (D.map e))
    (smallEtaleBaseChange_map_left_fst (c.π.app j) ψ).symm)
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.assoc _ _ _))
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact hψ.symm.trans (congrArg (· ≫ ψ.left ≫ pullback.fst V₀.hom (D.map e))
    (smallEtaleBaseChangeHomMk_left_fst _ _ _).symm)

end Descent

/-! ### Moving morphisms and sections to a later stage -/

section Transport

variable {X' X Y : Scheme.{u}} (φ : X' ⟶ X) (e : X ⟶ Y) (e' : X' ⟶ Y) (he : e' = φ ≫ e)

/-- A morphism `Z ⟶ W ×_Y X` of the small étale site of `X`, base changed along `φ : X' ⟶ X`, as
a morphism `Z ×_X X' ⟶ W ×_Y X'`. -/
def smallEtaleBaseChangeTransport {Z : X.Etale} {W : Y.Etale}
    (ψ : Z ⟶ (smallEtaleBaseChange e).obj W) :
    (smallEtaleBaseChange φ).obj Z ⟶ (smallEtaleBaseChange e').obj W :=
  smallEtaleBaseChangeHomMk e' (pullback.fst Z.hom φ ≫ ψ.left ≫ pullback.fst W.hom e)
    ((Category.assoc _ _ _).trans ((congrArg (pullback.fst Z.hom φ ≫ ·)
      (smallEtaleBaseChange_left_fst_hom e ψ)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ e) (pullback.condition (f := Z.hom) (g := φ))).trans
          ((Category.assoc _ _ _).trans (congrArg (pullback.snd Z.hom φ ≫ ·) he.symm))))))

/-- The first component of `smallEtaleBaseChangeTransport φ e e' he ψ` is the first component of
`ψ` precomposed with the projection `Z ×_X X' ⟶ Z`. -/
lemma smallEtaleBaseChangeTransport_left_fst {Z : X.Etale} {W : Y.Etale}
    (ψ : Z ⟶ (smallEtaleBaseChange e).obj W) :
    (smallEtaleBaseChangeTransport φ e e' he ψ).left ≫ pullback.fst W.hom e' =
      pullback.fst Z.hom φ ≫ ψ.left ≫ pullback.fst W.hom e :=
  smallEtaleBaseChangeHomMk_left_fst _ _ _

variable (H : Sheaf (smallEtaleTopology Y) Ab.{u + 1})

/-- **Sections given by units move to later stages.** The comparison of sections of iterated
inverse images along `φ` carries the restriction of the image of a section of `H` under the unit
along `χ : Z ⟶ W ×_Y X` to its restriction along the transported morphism. -/
lemma pullbackSectionsMap_map_unitApp_transport {Z : X.Etale} {W : Y.Etale}
    (χ : Z ⟶ (smallEtaleBaseChange e).obj W) (h : ToType (H.obj.obj (op W))) :
    pullbackSectionsMap φ e e' he H Z
        (((smallEtalePullbackAb e).obj H).obj.map χ.op (smallEtalePullbackAbUnitApp e H W h)) =
      ((smallEtalePullbackAb e').obj H).obj.map (smallEtaleBaseChangeTransport φ e e' he χ).op
        (smallEtalePullbackAbUnitApp e' H W h) :=
  pullbackSectionsMap_map_unitApp e H φ e' he χ h _
    (smallEtaleBaseChangeTransport_left_fst φ e e' he χ)

end Transport

/-- Two morphisms into a threefold iterated base change agree as soon as their components into the
original object agree. -/
lemma smallEtaleBaseChange_baseChange_baseChange_hom_ext {W X Y Z : Scheme.{u}} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) {A : W.Etale} {U : Z.Etale}
    {p q : A ⟶ (smallEtaleBaseChange f).obj
      ((smallEtaleBaseChange g).obj ((smallEtaleBaseChange h).obj U))}
    (hpq : p.left ≫ pullback.fst _ f ≫ pullback.fst _ g ≫ pullback.fst U.hom h =
      q.left ≫ pullback.fst _ f ≫ pullback.fst _ g ≫ pullback.fst U.hom h) : p = q := by
  have hs : ∀ (r : A ⟶ (smallEtaleBaseChange f).obj
      ((smallEtaleBaseChange g).obj ((smallEtaleBaseChange h).obj U))),
      r.left ≫ pullback.fst _ f ≫ pullback.fst _ g ≫ pullback.snd U.hom h = (A.hom ≫ f) ≫ g :=
    fun r => (congrArg (fun z => r.left ≫ pullback.fst _ f ≫ z)
      (pullback.condition (f := ((smallEtaleBaseChange h).obj U).hom) (g := g))).trans
        (congrArg (fun z => z ≫ g) (smallEtaleBaseChange_fst_snd f g r))
  refine smallEtaleBaseChange_baseChange_hom_ext f g ?_
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans (hpq.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans ((hs p).trans ((hs q).symm.trans
      (Category.assoc _ _ _).symm))

/-- The morphism from the fibre product of two base changed morphisms to the base change of their
fibre product. -/
def smallEtaleBaseChangePullbackLift {X' X : Scheme.{u}} (φ : X' ⟶ X) {Z₁ Z₂ B : X.Etale}
    (ψ₁ : Z₁ ⟶ B) (ψ₂ : Z₂ ⟶ B) :
    pullback ((smallEtaleBaseChange φ).map ψ₁) ((smallEtaleBaseChange φ).map ψ₂) ⟶
      (smallEtaleBaseChange φ).obj (pullback ψ₁ ψ₂) :=
  let T₁ := (smallEtaleBaseChange φ).map ψ₁
  let T₂ := (smallEtaleBaseChange φ).map ψ₂
  let p₁ := (pullback.fst T₁ T₂).left
  let p₂ := (pullback.snd T₁ T₂).left
  have hc : p₁ ≫ T₁.left = p₂ ≫ T₂.left :=
    congrArg (fun k => k.left) (pullback.condition (f := T₁) (g := T₂))
  have hw₁ : p₁ ≫ ((smallEtaleBaseChange φ).obj Z₁).hom = (pullback T₁ T₂).hom :=
    MorphismProperty.Over.w (pullback.fst T₁ T₂)
  have hq : (p₁ ≫ pullback.fst Z₁.hom φ) ≫ ψ₁.left = (p₂ ≫ pullback.fst Z₂.hom φ) ≫ ψ₂.left :=
    (Category.assoc _ _ _).trans ((congrArg (p₁ ≫ ·)
      (smallEtaleBaseChange_map_left_fst φ ψ₁).symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.fst B.hom φ) hc).trans ((Category.assoc _ _ _).trans
          ((congrArg (p₂ ≫ ·) (smallEtaleBaseChange_map_left_fst φ ψ₂)).trans
            (Category.assoc _ _ _).symm)))))
  have hP := isPullback_smallEtale_pullback ψ₁ ψ₂
  have hr : hP.lift _ _ hq ≫ (pullback ψ₁ ψ₂).hom = (pullback T₁ T₂).hom ≫ φ := by
    have e₁ : hP.lift _ _ hq ≫ (pullback ψ₁ ψ₂).hom =
        (hP.lift _ _ hq ≫ (pullback.fst ψ₁ ψ₂).left) ≫ Z₁.hom :=
      (congrArg (hP.lift _ _ hq ≫ ·) (MorphismProperty.Over.w (pullback.fst ψ₁ ψ₂)).symm).trans
        (Category.assoc _ _ _).symm
    have e₂ : (p₁ ≫ pullback.fst Z₁.hom φ) ≫ Z₁.hom = (pullback T₁ T₂).hom ≫ φ :=
      (Category.assoc _ _ _).trans ((congrArg (p₁ ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) hw₁)))
    exact e₁.trans ((congrArg (· ≫ Z₁.hom) (hP.lift_fst _ _ hq)).trans e₂)
  smallEtaleBaseChangeHomMk φ (hP.lift _ _ hq) hr

/-- `smallEtaleBaseChangePullbackLift φ ψ₁ ψ₂` followed by the base change of the first projection
is the first projection. -/
lemma smallEtaleBaseChangePullbackLift_fst {X' X : Scheme.{u}} (φ : X' ⟶ X) {Z₁ Z₂ B : X.Etale}
    (ψ₁ : Z₁ ⟶ B) (ψ₂ : Z₂ ⟶ B) :
    smallEtaleBaseChangePullbackLift φ ψ₁ ψ₂ ≫ (smallEtaleBaseChange φ).map (pullback.fst ψ₁ ψ₂) =
      pullback.fst _ _ :=
  smallEtaleBaseChange_hom_ext φ ((Category.assoc _ _ _).trans
    ((congrArg ((smallEtaleBaseChangePullbackLift φ ψ₁ ψ₂).left ≫ ·)
      (smallEtaleBaseChange_map_left_fst φ (pullback.fst ψ₁ ψ₂))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (pullback.fst ψ₁ ψ₂).left) (smallEtaleBaseChangeHomMk_left_fst _ _ _)).trans
          ((isPullback_smallEtale_pullback ψ₁ ψ₂).lift_fst _ _ _)))))

/-- `smallEtaleBaseChangePullbackLift φ ψ₁ ψ₂` followed by the base change of the second
projection is the second projection. -/
lemma smallEtaleBaseChangePullbackLift_snd {X' X : Scheme.{u}} (φ : X' ⟶ X) {Z₁ Z₂ B : X.Etale}
    (ψ₁ : Z₁ ⟶ B) (ψ₂ : Z₂ ⟶ B) :
    smallEtaleBaseChangePullbackLift φ ψ₁ ψ₂ ≫ (smallEtaleBaseChange φ).map (pullback.snd ψ₁ ψ₂) =
      pullback.snd _ _ :=
  smallEtaleBaseChange_hom_ext φ ((Category.assoc _ _ _).trans
    ((congrArg ((smallEtaleBaseChangePullbackLift φ ψ₁ ψ₂).left ≫ ·)
      (smallEtaleBaseChange_map_left_fst φ (pullback.snd ψ₁ ψ₂))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (pullback.snd ψ₁ ψ₂).left) (smallEtaleBaseChangeHomMk_left_fst _ _ _)).trans
          ((isPullback_smallEtale_pullback ψ₁ ψ₂).lift_snd _ _ _)))))

section TransportOverlap

variable {X' X Y : Scheme.{u}} (φ : X' ⟶ X) (e : X ⟶ Y) (e' : X' ⟶ Y) (he : e' = φ ≫ e)
  (H : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
  {Z₁ Z₂ : X.Etale} {V₀ : Y.Etale}
  {ψ₁ : Z₁ ⟶ (smallEtaleBaseChange e).obj V₀} {ψ₂ : Z₂ ⟶ (smallEtaleBaseChange e).obj V₀}
  {T₁ : (smallEtaleBaseChange φ).obj Z₁ ⟶ (smallEtaleBaseChange e').obj V₀}
  {T₂ : (smallEtaleBaseChange φ).obj Z₂ ⟶ (smallEtaleBaseChange e').obj V₀}

omit he in
/-- If `T₁` and `T₂` have the same first components as the transports of `ψ₁` and `ψ₂` along `φ`,
then the two projections from the fibre product of `T₁` and `T₂` agree after composing with the
base changes of `ψ₁` and `ψ₂` along `φ`. -/
lemma pullback_condition_baseChange_map
    (hT₁ : T₁.left ≫ pullback.fst V₀.hom e' = pullback.fst Z₁.hom φ ≫ ψ₁.left ≫
      pullback.fst V₀.hom e)
    (hT₂ : T₂.left ≫ pullback.fst V₀.hom e' = pullback.fst Z₂.hom φ ≫ ψ₂.left ≫
      pullback.fst V₀.hom e) :
    pullback.fst T₁ T₂ ≫ (smallEtaleBaseChange φ).map ψ₁ =
      pullback.snd T₁ T₂ ≫ (smallEtaleBaseChange φ).map ψ₂ := by
  refine smallEtaleBaseChange_baseChange_hom_ext φ e ?_
  have hc : (pullback.fst T₁ T₂).left ≫ T₁.left ≫ pullback.fst V₀.hom e' =
      (pullback.snd T₁ T₂).left ≫ T₂.left ≫ pullback.fst V₀.hom e' :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k.left ≫ pullback.fst V₀.hom e')
      (pullback.condition (f := T₁) (g := T₂))).trans (Category.assoc _ _ _))
  have key : ∀ {Z : X.Etale} (ψ : Z ⟶ (smallEtaleBaseChange e).obj V₀)
      (q : pullback T₁ T₂ ⟶ (smallEtaleBaseChange φ).obj Z),
      (q ≫ (smallEtaleBaseChange φ).map ψ).left ≫
          pullback.fst ((smallEtaleBaseChange e).obj V₀).hom φ ≫ pullback.fst V₀.hom e =
        q.left ≫ pullback.fst Z.hom φ ≫ ψ.left ≫ pullback.fst V₀.hom e := fun ψ q =>
    (Category.assoc _ _ _).trans (congrArg (q.left ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pullback.fst V₀.hom e) (smallEtaleBaseChange_map_left_fst φ ψ)).trans
        (Category.assoc _ _ _))))
  refine (key ψ₁ _).trans (Eq.trans ?_ (key ψ₂ _).symm)
  exact (congrArg (_ ≫ ·) hT₁.symm).trans (hc.trans (congrArg (_ ≫ ·) hT₂))

include he in
/-- **Agreement on overlaps moves to later stages.** Let `T_k : Z_k ×_X X' ⟶ V₀ ×_Y X'` have the
same first components as the base changes of `ψ_k : Z_k ⟶ V₀ ×_Y X`, and similarly `S_k` for
`χ_k`. If the difference of the restrictions to `Z₁ ×_{ψ} Z₂` of two sections given by units dies
under the unit of `φ`, then the corresponding sections over the `Z_k ×_X X'` agree on the fibre
product of the `T_k`. -/
lemma map_fst_eq_map_snd_of_unitApp_eq_zero {W₁ W₂ : Y.Etale}
    (hT₁ : T₁.left ≫ pullback.fst V₀.hom e' = pullback.fst Z₁.hom φ ≫ ψ₁.left ≫
      pullback.fst V₀.hom e)
    (hT₂ : T₂.left ≫ pullback.fst V₀.hom e' = pullback.fst Z₂.hom φ ≫ ψ₂.left ≫
      pullback.fst V₀.hom e)
    (χ₁ : Z₁ ⟶ (smallEtaleBaseChange e).obj W₁) (χ₂ : Z₂ ⟶ (smallEtaleBaseChange e).obj W₂)
    (S₁ : (smallEtaleBaseChange φ).obj Z₁ ⟶ (smallEtaleBaseChange e').obj W₁)
    (S₂ : (smallEtaleBaseChange φ).obj Z₂ ⟶ (smallEtaleBaseChange e').obj W₂)
    (hS₁ : S₁.left ≫ pullback.fst W₁.hom e' = pullback.fst Z₁.hom φ ≫ χ₁.left ≫
      pullback.fst W₁.hom e)
    (hS₂ : S₂.left ≫ pullback.fst W₂.hom e' = pullback.fst Z₂.hom φ ≫ χ₂.left ≫
      pullback.fst W₂.hom e)
    (h₁ : ToType (H.obj.obj (op W₁))) (h₂ : ToType (H.obj.obj (op W₂)))
    (hd : smallEtalePullbackAbUnitApp φ ((smallEtalePullbackAb e).obj H) (pullback ψ₁ ψ₂)
      (((smallEtalePullbackAb e).obj H).obj.map (pullback.fst ψ₁ ψ₂).op
          (((smallEtalePullbackAb e).obj H).obj.map χ₁.op (smallEtalePullbackAbUnitApp e H W₁ h₁)) -
        ((smallEtalePullbackAb e).obj H).obj.map (pullback.snd ψ₁ ψ₂).op
          (((smallEtalePullbackAb e).obj H).obj.map χ₂.op
            (smallEtalePullbackAbUnitApp e H W₂ h₂))) = 0) :
    ((smallEtalePullbackAb e').obj H).obj.map (pullback.fst T₁ T₂).op
        (((smallEtalePullbackAb e').obj H).obj.map S₁.op (smallEtalePullbackAbUnitApp e' H W₁ h₁)) =
      ((smallEtalePullbackAb e').obj H).obj.map (pullback.snd T₁ T₂).op
        (((smallEtalePullbackAb e').obj H).obj.map S₂.op
          (smallEtalePullbackAbUnitApp e' H W₂ h₂)) := by
  let F' := ((smallEtalePullbackAb e').obj H).obj
  let F := ((smallEtalePullbackAb e).obj H).obj
  let u := pullback.lift _ _ (pullback_condition_baseChange_map φ e e' hT₁ hT₂) ≫
    smallEtaleBaseChangePullbackLift φ ψ₁ ψ₂
  have hu₁ : u ≫ (smallEtaleBaseChange φ).map (pullback.fst ψ₁ ψ₂) = pullback.fst T₁ T₂ := by
    rw [Category.assoc, smallEtaleBaseChangePullbackLift_fst, pullback.lift_fst]
  have hu₂ : u ≫ (smallEtaleBaseChange φ).map (pullback.snd ψ₁ ψ₂) = pullback.snd T₁ T₂ := by
    rw [Category.assoc, smallEtaleBaseChangePullbackLift_snd, pullback.lift_snd]
  have hz : pullbackSectionsMap φ e e' he H (pullback ψ₁ ψ₂)
      (F.map (pullback.fst ψ₁ ψ₂).op (F.map χ₁.op (smallEtalePullbackAbUnitApp e H W₁ h₁)) -
        F.map (pullback.snd ψ₁ ψ₂).op (F.map χ₂.op (smallEtalePullbackAbUnitApp e H W₂ h₂))) =
        0 :=
    pullbackSectionsMap_eq_zero_of_unitApp_eq_zero e H φ e' he _ hd
  have key : ∀ {Z : X.Etale} {W : Y.Etale} (k : pullback ψ₁ ψ₂ ⟶ Z)
      (χ : Z ⟶ (smallEtaleBaseChange e).obj W)
      (S : (smallEtaleBaseChange φ).obj Z ⟶ (smallEtaleBaseChange e').obj W)
      (_ : S.left ≫ pullback.fst W.hom e' = pullback.fst Z.hom φ ≫ χ.left ≫ pullback.fst W.hom e)
      (hh : ToType (H.obj.obj (op W))) (k' : pullback T₁ T₂ ⟶ (smallEtaleBaseChange φ).obj Z)
      (_ : u ≫ (smallEtaleBaseChange φ).map k = k'),
      F'.map k'.op (F'.map S.op (smallEtalePullbackAbUnitApp e' H W hh)) =
        F'.map u.op (pullbackSectionsMap φ e e' he H (pullback ψ₁ ψ₂)
          (F.map k.op (F.map χ.op (smallEtalePullbackAbUnitApp e H W hh)))) := by
    intro Z W k χ S hS hh k' hk
    rw [pullbackSectionsMap_naturality, pullbackSectionsMap_map_unitApp e H φ e' he χ hh S hS,
      presheaf_map_map_apply F' u, hk]
  rw [key (pullback.fst ψ₁ ψ₂) χ₁ S₁ hS₁ h₁ _ hu₁, key (pullback.snd ψ₁ ψ₂) χ₂ S₂ hS₂ h₂ _ hu₂,
    ← sub_eq_zero, ← map_sub, ← map_sub, hz, map_zero]

end TransportOverlap

/-! ### The surjectivity half -/

/-- **Transported objects cover.** If the images of `ψ x : Z x ⟶ V₀ ×_Y X` cover the image of
the base change of `V₀ ×_Y X` along `φ : X' ⟶ X`, the transported morphisms along `φ` jointly
cover `V₀ ×_Y X'`. -/
lemma iUnion_range_smallEtaleBaseChangeTransport_eq_univ {X' X Y : Scheme.{u}} (φ : X' ⟶ X)
    (e : X ⟶ Y) (e' : X' ⟶ Y) (he : e' = φ ≫ e) {T : Type*} {V₀ : Y.Etale} {Z : T → X.Etale}
    (ψ : ∀ x, Z x ⟶ (smallEtaleBaseChange e).obj V₀)
    (hcov : Set.range (pullback.snd φ ((smallEtaleBaseChange e).obj V₀).hom) ⊆
      ⋃ x, Set.range (ψ x).left) :
    ⋃ x, Set.range (smallEtaleBaseChangeTransport φ e e' he (ψ x)).left = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  let r : ((smallEtaleBaseChange e').obj V₀).left ⟶ ((smallEtaleBaseChange e).obj V₀).left :=
    pullback.lift (pullback.fst V₀.hom e') (pullback.snd V₀.hom e' ≫ φ)
      ((pullback.condition).trans ((congrArg (_ ≫ ·) he).trans (Category.assoc _ _ _).symm))
  obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ)
    (g := ((smallEtaleBaseChange e).obj V₀).hom) (pullback.snd V₀.hom e' y) (r y)
    (congrArg (fun k => k y) (pullback.lift_snd (pullback.fst V₀.hom e')
      (pullback.snd V₀.hom e' ≫ φ) _)).symm
  obtain ⟨x, z, hz⟩ := Set.mem_iUnion.1 (hcov ⟨w, hw⟩)
  have hsq : IsPullback (pullback.fst (Z x).hom φ)
      (smallEtaleBaseChangeTransport φ e e' he (ψ x)).left (ψ x).left r := by
    have hψl : (ψ x).left = pullback.lift ((ψ x).left ≫ pullback.fst V₀.hom e)
        (Z x).hom (smallEtaleBaseChange_left_fst_hom e (ψ x)) :=
      pullback.hom_ext (pullback.lift_fst _ _ _).symm
        ((smallEtaleBaseChange_w e (ψ x)).trans (pullback.lift_snd _ _ _).symm)
    rw [hψl]
    exact isPullback_pullback_lift_of_comp (Z x).hom V₀.hom e φ e' he.symm _ _
  obtain ⟨y', -, hy'⟩ := AlgebraicGeometry.IsPullback.exists_preimage_scheme hsq z y hz
  exact Set.mem_iUnion.2 ⟨x, y', hy'⟩

section Surjectivity

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c)
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- The inverse of the comparison `A ⟶ Z ×_{X_j} X` given by a presentation of `A` as a base
change. -/
def smallEtaleIsPullbackInv {j : I} {A : c.pt.Etale} {Z : (D.obj j).Etale} {θ : A.left ⟶ Z.left}
    (hθ : IsPullback θ A.hom Z.hom (c.π.app j)) : (smallEtaleBaseChange (c.π.app j)).obj Z ⟶ A :=
  MorphismProperty.Over.homMk hθ.isoPullback.inv hθ.isoPullback_inv_snd trivial

/-- `smallEtaleIsPullbackInv hθ` is a right inverse of the morphism `A ⟶ Z ×_{X_j} X` whose first
component is `θ`. -/
lemma smallEtaleIsPullbackInv_comp {j : I} {A : c.pt.Etale} {Z : (D.obj j).Etale}
    {θ : A.left ⟶ Z.left} (hθ : IsPullback θ A.hom Z.hom (c.π.app j)) :
    smallEtaleIsPullbackInv hθ ≫ smallEtaleBaseChangeHomMk (c.π.app j) θ hθ.w = 𝟙 _ :=
  smallEtaleBaseChange_hom_ext (c.π.app j) ((Category.assoc _ _ _).trans
    ((congrArg (hθ.isoPullback.inv ≫ ·) (smallEtaleBaseChangeHomMk_left_fst _ _ _)).trans
      (hθ.isoPullback_inv_fst.trans (Category.id_comp _).symm)))

/-- **The comparison of the section given by a stage descent.** The image in the sections of
`f_i⁻¹H` over the base change of `Z` of the section of `f_{ji}⁻¹H` given by `χ : Z ⟶ W ×_{X_i} X_j`
is the restriction of the given section `s` along `Z ×_{X_j} X ≅ A ⟶ V`. -/
lemma pullbackSectionsMap_eq_map_of_isPullback {i j : I} (e : j ⟶ i)
    (H : Sheaf (smallEtaleTopology (D.obj i)) Ab.{u + 1}) {V₀ W : (D.obj i).Etale}
    (s : ToType (((smallEtalePullbackAb (c.π.app i)).obj H).obj.obj
      (op ((smallEtaleBaseChange (c.π.app i)).obj V₀))))
    {A : c.pt.Etale} (g : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)
    (m : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj W) (h : ToType (H.obj.obj (op W)))
    (hm : ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map g.op s =
      ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map m.op
        (smallEtalePullbackAbUnitApp (c.π.app i) H W h))
    {Z : (D.obj j).Etale} {θ : A.left ⟶ Z.left} (hθ : IsPullback θ A.hom Z.hom (c.π.app j))
    (χ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj W)
    (hχ : θ ≫ χ.left ≫ pullback.fst W.hom (D.map e) = m.left ≫ pullback.fst W.hom (c.π.app i)) :
    pullbackSectionsMap (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H Z
        (((smallEtalePullbackAb (D.map e)).obj H).obj.map χ.op
          (smallEtalePullbackAbUnitApp (D.map e) H W h)) =
      ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map (smallEtaleIsPullbackInv hθ ≫ g).op s := by
  let F := ((smallEtalePullbackAb (c.π.app i)).obj H).obj
  let σ := pullbackSectionsMap (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H Z
    (((smallEtalePullbackAb (D.map e)).obj H).obj.map χ.op
      (smallEtalePullbackAbUnitApp (D.map e) H W h))
  calc σ = F.map (smallEtaleIsPullbackInv hθ ≫ smallEtaleBaseChangeHomMk (c.π.app j) θ hθ.w).op σ
        := by rw [smallEtaleIsPullbackInv_comp, op_id, CategoryTheory.Functor.map_id,
              ConcreteCategory.id_apply]
    _ = F.map (smallEtaleIsPullbackInv hθ).op
          (F.map (smallEtaleBaseChangeHomMk (c.π.app j) θ hθ.w).op σ) :=
        (presheaf_map_map_apply F _ _ σ).symm
    _ = F.map (smallEtaleIsPullbackInv hθ).op (F.map g.op s) := by
      rw [StageDescent.map_pullbackSectionsMap (gW := m) H e hθ.w χ hχ h, hm]
    _ = F.map (smallEtaleIsPullbackInv hθ ≫ g).op s := presheaf_map_map_apply F _ _ s

/-- A section whose comparison to the inverse image along a composite vanishes already vanishes
under the unit: the comparison is the unit followed by an isomorphism. -/
lemma unitApp_eq_zero_of_pullbackSectionsMap_eq_zero {X' X Y : Scheme.{u}} (g : X' ⟶ X)
    (f : X ⟶ Y) (gf : X' ⟶ Y) (hgf : gf = g ≫ f) (H : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (U : X.Etale) (y : ToType (((smallEtalePullbackAb f).obj H).obj.obj (op U)))
    (hy : pullbackSectionsMap g f gf hgf H U y = 0) :
    smallEtalePullbackAbUnitApp g ((smallEtalePullbackAb f).obj H) U y = 0 := by
  have e := congrArg (fun φ => φ.hom.app (op ((smallEtaleBaseChange g).obj U))
    (smallEtalePullbackAbUnitApp g ((smallEtalePullbackAb f).obj H) U y))
    ((smallEtalePullbackAbComp' g f gf hgf).hom_inv_id_app H)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at e
  have e' : ((smallEtalePullbackAbComp' g f gf hgf).inv.app H).hom.app
      (op ((smallEtaleBaseChange g).obj U))
      (((smallEtalePullbackAbComp' g f gf hgf).hom.app H).hom.app
        (op ((smallEtaleBaseChange g).obj U))
        (smallEtalePullbackAbUnitApp g ((smallEtalePullbackAb f).obj H) U y)) =
      smallEtalePullbackAbUnitApp g ((smallEtalePullbackAb f).obj H) U y := e
  rw [← e']
  show ((smallEtalePullbackAbComp' g f gf hgf).inv.app H).hom.app _
    (pullbackSectionsMap g f gf hgf H U y) = 0
  rw [hy, map_zero]

/-- **Agreement on overlaps of the sections given by two stage descents.** Two sections given by
units over objects `Z₁, Z₂` of a stage, presenting objects `A₁, A₂` of the limit on which the
given section `s` is described by the same units, agree over the base change to the limit of the
fibre product `Z₁ ×_B Z₂`; hence their difference dies under the unit of the projection. -/
lemma unitApp_sub_eq_zero_of_isPullback {i j : I} (e : j ⟶ i)
    (H : Sheaf (smallEtaleTopology (D.obj i)) Ab.{u + 1}) {V₀ : (D.obj i).Etale}
    (s : ToType (((smallEtalePullbackAb (c.π.app i)).obj H).obj.obj
      (op ((smallEtaleBaseChange (c.π.app i)).obj V₀))))
    {A₁ A₂ : c.pt.Etale} (g₁ : A₁ ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)
    (g₂ : A₂ ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀) {W₁ W₂ : (D.obj i).Etale}
    (m₁ : A₁ ⟶ (smallEtaleBaseChange (c.π.app i)).obj W₁)
    (m₂ : A₂ ⟶ (smallEtaleBaseChange (c.π.app i)).obj W₂) (h₁ : ToType (H.obj.obj (op W₁)))
    (h₂ : ToType (H.obj.obj (op W₂)))
    (hm₁ : ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map g₁.op s =
      ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map m₁.op
        (smallEtalePullbackAbUnitApp (c.π.app i) H W₁ h₁))
    (hm₂ : ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map g₂.op s =
      ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map m₂.op
        (smallEtalePullbackAbUnitApp (c.π.app i) H W₂ h₂))
    {Z₁ Z₂ : (D.obj j).Etale} {θ₁ : A₁.left ⟶ Z₁.left} {θ₂ : A₂.left ⟶ Z₂.left}
    (hθ₁ : IsPullback θ₁ A₁.hom Z₁.hom (c.π.app j)) (hθ₂ : IsPullback θ₂ A₂.hom Z₂.hom (c.π.app j))
    (ψ₁ : Z₁ ⟶ (smallEtaleBaseChange (D.map e)).obj V₀)
    (ψ₂ : Z₂ ⟶ (smallEtaleBaseChange (D.map e)).obj V₀)
    (hψ₁ : θ₁ ≫ ψ₁.left ≫ pullback.fst V₀.hom (D.map e) =
      g₁.left ≫ pullback.fst V₀.hom (c.π.app i))
    (hψ₂ : θ₂ ≫ ψ₂.left ≫ pullback.fst V₀.hom (D.map e) =
      g₂.left ≫ pullback.fst V₀.hom (c.π.app i))
    (χ₁ : Z₁ ⟶ (smallEtaleBaseChange (D.map e)).obj W₁)
    (χ₂ : Z₂ ⟶ (smallEtaleBaseChange (D.map e)).obj W₂)
    (hχ₁ : θ₁ ≫ χ₁.left ≫ pullback.fst W₁.hom (D.map e) =
      m₁.left ≫ pullback.fst W₁.hom (c.π.app i))
    (hχ₂ : θ₂ ≫ χ₂.left ≫ pullback.fst W₂.hom (D.map e) =
      m₂.left ≫ pullback.fst W₂.hom (c.π.app i)) :
    smallEtalePullbackAbUnitApp (c.π.app j) ((smallEtalePullbackAb (D.map e)).obj H)
        (pullback ψ₁ ψ₂)
        (((smallEtalePullbackAb (D.map e)).obj H).obj.map (pullback.fst ψ₁ ψ₂).op
            (((smallEtalePullbackAb (D.map e)).obj H).obj.map χ₁.op
              (smallEtalePullbackAbUnitApp (D.map e) H W₁ h₁)) -
          ((smallEtalePullbackAb (D.map e)).obj H).obj.map (pullback.snd ψ₁ ψ₂).op
            (((smallEtalePullbackAb (D.map e)).obj H).obj.map χ₂.op
              (smallEtalePullbackAbUnitApp (D.map e) H W₂ h₂))) = 0 := by
  refine unitApp_eq_zero_of_pullbackSectionsMap_eq_zero _ _ _ (c.w e).symm H _ _ ?_
  rw [map_sub, sub_eq_zero,
    pullbackSectionsMap_naturality (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H
      (pullback.fst ψ₁ ψ₂),
    pullbackSectionsMap_naturality (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H
      (pullback.snd ψ₁ ψ₂),
    pullbackSectionsMap_eq_map_of_isPullback e H s g₁ m₁ h₁ hm₁ hθ₁ χ₁ hχ₁,
    pullbackSectionsMap_eq_map_of_isPullback e H s g₂ m₂ h₂ hm₂ hθ₂ χ₂ hχ₂]
  refine (presheaf_map_map_apply _ _ _ _).trans (Eq.trans ?_ (presheaf_map_map_apply _ _ _ _).symm)
  refine congrArg (fun (k : (smallEtaleBaseChange (c.π.app j)).obj (pullback ψ₁ ψ₂) ⟶
    (smallEtaleBaseChange (c.π.app i)).obj V₀) =>
      ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map k.op s) ?_
  have key : ∀ {A : c.pt.Etale} {Z : (D.obj j).Etale} {θ : A.left ⟶ Z.left}
      (hθ : IsPullback θ A.hom Z.hom (c.π.app j))
      (g : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)
      (ψ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj V₀)
      (_ : θ ≫ ψ.left ≫ pullback.fst V₀.hom (D.map e) =
        g.left ≫ pullback.fst V₀.hom (c.π.app i)) (q : pullback ψ₁ ψ₂ ⟶ Z),
      ((smallEtaleBaseChange (c.π.app j)).map q ≫ smallEtaleIsPullbackInv hθ ≫ g).left ≫
          pullback.fst V₀.hom (c.π.app i) =
        pullback.fst (pullback ψ₁ ψ₂).hom (c.π.app j) ≫ (q ≫ ψ).left ≫
          pullback.fst V₀.hom (D.map e) := by
    intro A Z θ hθ g ψ hψ q
    let M := ((smallEtaleBaseChange (c.π.app j)).map q).left
    have h₁ : M ≫ hθ.isoPullback.inv ≫ g.left ≫ pullback.fst V₀.hom (c.π.app i) =
        M ≫ hθ.isoPullback.inv ≫ θ ≫ ψ.left ≫ pullback.fst V₀.hom (D.map e) :=
      congrArg (fun t => M ≫ hθ.isoPullback.inv ≫ t) hψ.symm
    have h₂ : M ≫ hθ.isoPullback.inv ≫ θ ≫ ψ.left ≫ pullback.fst V₀.hom (D.map e) =
        M ≫ pullback.fst Z.hom (c.π.app j) ≫ ψ.left ≫ pullback.fst V₀.hom (D.map e) :=
      congrArg (M ≫ ·) ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ ψ.left ≫ pullback.fst V₀.hom (D.map e)) hθ.isoPullback_inv_fst))
    have h₃ : M ≫ pullback.fst Z.hom (c.π.app j) ≫ ψ.left ≫
        pullback.fst V₀.hom (D.map e) =
        pullback.fst (pullback ψ₁ ψ₂).hom (c.π.app j) ≫ (q ≫ ψ).left ≫
          pullback.fst V₀.hom (D.map e) :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ.left ≫
        pullback.fst V₀.hom (D.map e)) (smallEtaleBaseChange_map_left_fst (c.π.app j) q)).trans
          ((Category.assoc _ _ _).trans (congrArg (pullback.fst _ _ ≫ ·)
            (Category.assoc _ _ _).symm)))
    exact h₁.trans (h₂.trans h₃)
  refine smallEtaleBaseChange_hom_ext (c.π.app i) ?_
  refine (key hθ₁ g₁ ψ₁ hψ₁ _).trans (Eq.trans ?_ (key hθ₂ g₂ ψ₂ hψ₂ _).symm)
  rw [pullback.condition]

/-- `smallEtaleIsPullbackInv hθ` is a left inverse of the morphism `A ⟶ Z ×_{X_j} X` whose first
component is `θ`. -/
lemma smallEtaleBaseChangeHomMk_comp_isPullbackInv {I : Type u} [SmallCategory I]
    {D : I ⥤ Scheme.{u}} {c : Cone D} {j : I} {A : c.pt.Etale} {Z : (D.obj j).Etale}
    {θ : A.left ⟶ Z.left} (hθ : IsPullback θ A.hom Z.hom (c.π.app j)) :
    smallEtaleBaseChangeHomMk (c.π.app j) θ hθ.w ≫ smallEtaleIsPullbackInv hθ = 𝟙 _ := by
  have h : (smallEtaleBaseChangeHomMk (c.π.app j) θ hθ.w).left = hθ.isoPullback.hom :=
    pullback.hom_ext ((smallEtaleBaseChangeHomMk_left_fst _ _ _).trans
      hθ.isoPullback_hom_fst.symm) ((pullback.lift_snd _ _ _).trans hθ.isoPullback_hom_snd.symm)
  exact MorphismProperty.Over.Hom.ext ((congrArg (· ≫ hθ.isoPullback.inv) h).trans
    hθ.isoPullback.hom_inv_id)

/-- The images of the stage descents `ψ x` cover the image of the limit in the base change of
`V₀` to `X_j`, as soon as the morphisms `g x` jointly cover the base change of `V₀` to the
limit. -/
lemma range_pullback_snd_subset_iUnion_range_of_stageDescent {i j : I} (e : j ⟶ i)
    {V₀ : (D.obj i).Etale} {T : Type*} {A : T → c.pt.Etale}
    (g : ∀ x, A x ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)
    (hT : ∀ y, ∃ x, y ∈ Set.range (g x).left) {Z : T → (D.obj j).Etale}
    {θ : ∀ x, (A x).left ⟶ (Z x).left} (hθ : ∀ x, θ x ≫ (Z x).hom = (A x).hom ≫ c.π.app j)
    (ψ : ∀ x, Z x ⟶ (smallEtaleBaseChange (D.map e)).obj V₀)
    (hψ : ∀ x, θ x ≫ (ψ x).left ≫ pullback.fst V₀.hom (D.map e) =
      (g x).left ≫ pullback.fst V₀.hom (c.π.app i)) :
    Set.range (pullback.snd (c.π.app j) ((smallEtaleBaseChange (D.map e)).obj V₀).hom) ⊆
      ⋃ x, Set.range (ψ x).left := by
  rintro _ ⟨w, rfl⟩
  let B := (smallEtaleBaseChange (D.map e)).obj V₀
  let ε := (smallEtaleBaseChangeComp' (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm).app V₀
  obtain ⟨v, hv, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.hom)
    (g := c.π.app j) (pullback.snd (c.π.app j) B.hom w) (pullback.fst (c.π.app j) B.hom w)
    (by rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply])
  obtain ⟨x, z, hz⟩ := hT (ε.inv.left v)
  refine Set.mem_iUnion.2 ⟨x, θ x z, ?_⟩
  have e₁ := congrArg (fun k => k.left ≫ pullback.fst B.hom (c.π.app j))
    (StageDescent.comp_baseChangeComp e (hθ x) (ψ x) (hψ x))
  have e₂ : (smallEtaleBaseChangeHomMk (c.π.app j) (θ x) (hθ x) ≫
      (smallEtaleBaseChange (c.π.app j)).map (ψ x)).left ≫ pullback.fst B.hom (c.π.app j) =
      θ x ≫ (ψ x).left :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (smallEtaleBaseChange_map_left_fst (c.π.app j) (ψ x))).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (ψ x).left)
        (smallEtaleBaseChangeHomMk_left_fst _ _ _))))
  have e₄ : ((ε.inv.left ≫ ε.hom.left) ≫ pullback.fst B.hom (c.π.app j)) v =
      pullback.fst B.hom (c.π.app j) v := by
    rw [show ε.inv.left ≫ ε.hom.left = 𝟙 _ from congrArg (fun k => k.left) ε.inv_hom_id]
    rfl
  show ((θ x) ≫ (ψ x).left) z = _
  refine (congrArg (fun k => k z) (e₂.symm.trans e₁.symm)).trans ?_
  show (pullback.fst B.hom (c.π.app j)) (ε.hom.left ((g x).left z)) = _
  rw [hz]
  show ((ε.inv.left ≫ ε.hom.left) ≫ pullback.fst B.hom (c.π.app j)) v = _
  rw [e₄, hv]

/-- A section `t` over `V_k` whose restriction along the transport of a stage descent `ψ` to a
later stage `X_k` is the section given by the transported `χ` has, on the object `A` of the limit,
the same restriction as `s`. -/
lemma StageDescent.map_pullbackSectionsMap_of_transport {i j k : I} (e : j ⟶ i) (φ : k ⟶ j)
    (ef : k ⟶ i) (hef : D.map ef = D.map φ ≫ D.map e)
    (H : Sheaf (smallEtaleTopology (D.obj i)) Ab.{u + 1}) {V₀ W : (D.obj i).Etale}
    (s : ToType (((smallEtalePullbackAb (c.π.app i)).obj H).obj.obj
      (op ((smallEtaleBaseChange (c.π.app i)).obj V₀))))
    {A : c.pt.Etale} (g : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj V₀)
    (m : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj W) (h : ToType (H.obj.obj (op W)))
    (hm : ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map g.op s =
      ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map m.op
        (smallEtalePullbackAbUnitApp (c.π.app i) H W h))
    {Z : (D.obj j).Etale} {θ : A.left ⟶ Z.left} (hθ : IsPullback θ A.hom Z.hom (c.π.app j))
    (ψ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj V₀)
    (hψ : θ ≫ ψ.left ≫ pullback.fst V₀.hom (D.map e) = g.left ≫ pullback.fst V₀.hom (c.π.app i))
    (χ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj W)
    (hχ : θ ≫ χ.left ≫ pullback.fst W.hom (D.map e) = m.left ≫ pullback.fst W.hom (c.π.app i))
    (t : ToType (((smallEtalePullbackAb (D.map ef)).obj H).obj.obj
      (op ((smallEtaleBaseChange (D.map ef)).obj V₀))))
    (ht : ((smallEtalePullbackAb (D.map ef)).obj H).obj.map
        (smallEtaleBaseChangeTransport (D.map φ) (D.map e) (D.map ef) hef ψ).op t =
      ((smallEtalePullbackAb (D.map ef)).obj H).obj.map
        (smallEtaleBaseChangeTransport (D.map φ) (D.map e) (D.map ef) hef χ).op
        (smallEtalePullbackAbUnitApp (D.map ef) H W h)) :
    ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map g.op
        (((smallEtalePullbackAb (c.π.app i)).obj H).obj.map
          ((smallEtaleBaseChangeComp' (c.π.app k) (D.map ef) (c.π.app i) (c.w ef).symm).hom.app
            V₀).op
          (pullbackSectionsMap (c.π.app k) (D.map ef) (c.π.app i) (c.w ef).symm H _ t)) =
      ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map g.op s := by
  let FX := ((smallEtalePullbackAb (c.π.app i)).obj H).obj
  let θk : A.left ⟶ ((smallEtaleBaseChange (D.map φ)).obj Z).left :=
    pullback.lift θ (A.hom ≫ c.π.app k) (by rw [hθ.w, Category.assoc, c.w])
  have hθk : IsPullback θk A.hom ((smallEtaleBaseChange (D.map φ)).obj Z).hom (c.π.app k) :=
    isPullback_lift_of_isPullback D c hθ φ
  have hk : ∀ {V : (D.obj i).Etale} {n : A ⟶ (smallEtaleBaseChange (c.π.app i)).obj V}
      {ξ : Z ⟶ (smallEtaleBaseChange (D.map e)).obj V},
      θ ≫ ξ.left ≫ pullback.fst V.hom (D.map e) = n.left ≫ pullback.fst V.hom (c.π.app i) →
      θk ≫ (smallEtaleBaseChangeTransport (D.map φ) (D.map e) (D.map ef) hef ξ).left ≫
        pullback.fst V.hom (D.map ef) = n.left ≫ pullback.fst V.hom (c.π.app i) := fun {_ _ ξ} hξ =>
    (congrArg (θk ≫ ·) (smallEtaleBaseChangeTransport_left_fst _ _ _ hef ξ)).trans
      ((pullback.lift_fst_assoc _ _ _ _).trans hξ)
  rw [presheaf_map_map_apply FX g, StageDescent.comp_baseChangeComp ef hθk.w _ (hk hψ),
    ← presheaf_map_map_apply FX, ← pullbackSectionsMap_naturality, ht, hm]
  exact StageDescent.map_pullbackSectionsMap H ef hθk.w _ (hk hχ) h

include hc in
/-- **The surjectivity half of the degree zero colimit formula for an inverse image** (Stacks
09YN). Let `X = lim X_i` be a cofiltered limit of schemes with affine transition morphisms, `H`
an abelian sheaf on the small étale site of a stage `X_i` and `V₀` a quasi-compact and
quasi-separated object of that site. Every section of `f_i⁻¹H` over the
base change of `V₀` to `X` comes from a section of `f_{ji}⁻¹H` over the base change of `V₀` to a
later stage `X_j`, through the comparison of sections of iterated inverse images. -/
theorem exists_pullbackSectionsMap_eq_of_isLimit {i : I}
    (H : Sheaf (smallEtaleTopology (D.obj i)) Ab.{u + 1}) (V₀ : (D.obj i).Etale)
    [CompactSpace V₀.left] [QuasiSeparatedSpace V₀.left]
    (s : ToType (((smallEtalePullbackAb (c.π.app i)).obj H).obj.obj
      (op ((smallEtaleBaseChange (c.π.app i)).obj V₀)))) :
    ∃ (j : I) (e : j ⟶ i) (t : ToType (((smallEtalePullbackAb (D.map e)).obj H).obj.obj
        (op ((smallEtaleBaseChange (D.map e)).obj V₀)))),
      ((smallEtalePullbackAb (c.π.app i)).obj H).obj.map
          ((smallEtaleBaseChangeComp' (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm).hom.app
            V₀).op
          (pullbackSectionsMap (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm H _ t) = s := by
  classical
  let FX := ((smallEtalePullbackAb (c.π.app i)).obj H).obj
  let V := (smallEtaleBaseChange (c.π.app i)).obj V₀
  have : QuasiCompact (c.π.app i) := by
    have := isAffineHom_π_app D c hc i
    infer_instance
  have hVc : CompactSpace V.left := compactSpace_smallEtaleBaseChange_obj (c.π.app i) V₀
    inferInstance
  obtain ⟨S, hS, hloc⟩ := exists_covering_smallEtalePullbackAb_eq_unitApp (c.π.app i) H V s
  choose A g hA hgS hgx using fun x : V.left =>
    exists_isAffine_mem_range_of_mem_smallEtaleTopology S hS x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : V.left => Set.range (g x).left)
    (fun x => (g x).left.isOpenMap.isOpen_range) (fun x _ => Set.mem_iUnion.2 ⟨x, hgx x⟩)
  let T := {x : V.left // x ∈ t}
  have hT : ∀ y : V.left, ∃ x : T, y ∈ Set.range (g x.1).left := by
    intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨⟨x, hx⟩, hy⟩
  choose W' m h hm using fun x : T => hloc (g x.1) (hgS x.1)
  obtain ⟨a₁, ha₁⟩ := common_stage_of_finite i
    (fun (a : Over i) (x : T) => StageDescent D c (A x.1) V₀ (W' x) (g x.1) (m x) a.hom)
    (fun {a b} φ x hb => hb.of_le φ.left a.hom (Over.w φ)) (fun x => by
      have := hA x.1
      obtain ⟨j, e, hd⟩ := exists_stageDescent D c hc (A x.1) V₀ (W' x) (g x.1) (m x)
      exact ⟨Over.mk e, hd⟩)
  let j := a₁.left
  let e : j ⟶ i := a₁.hom
  choose Z θ ψ χ hZc hZs hθ hψ hχ using ha₁
  let FL := (smallEtalePullbackAb (D.map e)).obj H
  let B := (smallEtaleBaseChange (D.map e)).obj V₀
  let d : ∀ x x' : T, ToType (FL.obj.obj (op (pullback (ψ x) (ψ x')))) := fun x x' =>
    FL.obj.map (pullback.fst (ψ x) (ψ x')).op
        (FL.obj.map (χ x).op (smallEtalePullbackAbUnitApp (D.map e) H (W' x) (h x))) -
      FL.obj.map (pullback.snd (ψ x) (ψ x')).op
        (FL.obj.map (χ x').op (smallEtalePullbackAbUnitApp (D.map e) H (W' x') (h x')))
  have : QuasiCompact (D.map e) := inferInstance
  have hBc : CompactSpace B.left := compactSpace_smallEtaleBaseChange_obj (D.map e) V₀
    inferInstance
  have hBs : QuasiSeparatedSpace B.left := quasiSeparatedSpace_smallEtaleBaseChange_obj
    (D.map e) V₀ inferInstance
  let P : Over j → Option (T × T) → Prop := fun a o => match o with
    | none => Set.range (pullback.snd (D.map a.hom) B.hom) ⊆ ⋃ x : T, Set.range (ψ x).left
    | some q => smallEtalePullbackAbUnitApp (D.map a.hom) FL (pullback (ψ q.1) (ψ q.2))
        (d q.1 q.2) = 0
  obtain ⟨a₂, ha₂⟩ := common_stage_of_finite j P (by
    rintro a b φ (_ | q) hb
    · exact (range_pullback_snd_subset_of_fac (D.map b.hom) (D.map a.hom) (D.map φ.left)
        (by rw [← D.map_comp, Over.w φ]) B.hom).trans hb
    · exact unitApp_eq_zero_of_comp (D.map b.hom) FL (D.map φ.left) (D.map a.hom)
        (by rw [← D.map_comp, Over.w φ]) _ hb) (by
    rintro (_ | q)
    · have : CompactSpace ((𝟭 Scheme.{u}).obj B.left) := hBc
      obtain ⟨j', f, hf⟩ := exists_range_pullback_snd_subset_of_isLimit D c hc B.hom
        ⟨⋃ x : T, Set.range (ψ x).left, isOpen_iUnion fun x => (ψ x).left.isOpenMap.isOpen_range⟩
        (range_pullback_snd_subset_iUnion_range_of_stageDescent e (fun x : T => g x.1) hT
          (fun x => (hθ x).w) ψ hψ)
      exact ⟨Over.mk f, hf⟩
    · have := hZc q.1
      have := hZc q.2
      have hPb := isPullback_smallEtale_pullback (ψ q.1) (ψ q.2)
      have : QuasiCompact (pullback.fst (ψ q.1) (ψ q.2)).left :=
        MorphismProperty.of_isPullback hPb.flip inferInstance
      have hPc : CompactSpace (pullback (ψ q.1) (ψ q.2)).left :=
        QuasiCompact.compactSpace_of_compactSpace (pullback.fst (ψ q.1) (ψ q.2)).left
      obtain ⟨j', f, hf⟩ := exists_unitApp_eq_zero_of_isLimit D c hc FL
        (pullback (ψ q.1) (ψ q.2)) (d q.1 q.2)
        (unitApp_sub_eq_zero_of_isPullback e H s (g q.1.1) (g q.2.1) (m q.1) (m q.2) (h q.1)
          (h q.2) (hm q.1) (hm q.2) (hθ q.1) (hθ q.2) (ψ q.1) (ψ q.2) (hψ q.1) (hψ q.2)
          (χ q.1) (χ q.2) (hχ q.1) (hχ q.2))
      exact ⟨Over.mk f, hf⟩)
  let k := a₂.left
  let φ : k ⟶ j := a₂.hom
  let ef : k ⟶ i := φ ≫ e
  have hef : D.map ef = D.map φ ≫ D.map e := D.map_comp φ e
  have hcov : Set.range (pullback.snd (D.map φ) B.hom) ⊆ ⋃ x : T, Set.range (ψ x).left :=
    ha₂ none
  let Zk : T → (D.obj k).Etale := fun x => (smallEtaleBaseChange (D.map φ)).obj (Z x)
  let ψk : ∀ x, Zk x ⟶ (smallEtaleBaseChange (D.map ef)).obj V₀ := fun x =>
    smallEtaleBaseChangeTransport (D.map φ) (D.map e) (D.map ef) hef (ψ x)
  let χk : ∀ x, Zk x ⟶ (smallEtaleBaseChange (D.map ef)).obj (W' x) := fun x =>
    smallEtaleBaseChangeTransport (D.map φ) (D.map e) (D.map ef) hef (χ x)
  let FK := (smallEtalePullbackAb (D.map ef)).obj H
  let tk : ∀ x, ToType (FK.obj.obj (op (Zk x))) := fun x =>
    FK.obj.map (χk x).op (smallEtalePullbackAbUnitApp (D.map ef) H (W' x) (h x))
  have hcovk : ⋃ x, Set.range (ψk x).left = Set.univ :=
    iUnion_range_smallEtaleBaseChangeTransport_eq_univ (D.map φ) (D.map e) (D.map ef) hef ψ hcov
  obtain ⟨tg, htg⟩ := exists_glue_smallEtale FK (fun x => Zk x) ψk hcovk tk fun x x' =>
    map_fst_eq_map_snd_of_unitApp_eq_zero (D.map φ) (D.map e) (D.map ef) hef H
      (smallEtaleBaseChangeTransport_left_fst _ _ _ hef (ψ x))
      (smallEtaleBaseChangeTransport_left_fst _ _ _ hef (ψ x')) (χ x) (χ x') (χk x) (χk x')
      (smallEtaleBaseChangeTransport_left_fst _ _ _ hef (χ x))
      (smallEtaleBaseChangeTransport_left_fst _ _ _ hef (χ x')) (h x) (h x') (ha₂ (some (x, x')))
  refine ⟨k, ef, tg, ?_⟩
  refine smallEtale_section_ext ((smallEtalePullbackAb (c.π.app i)).obj H)
    (Sieve.ofArrows (fun x : T => A x.1) (fun x => g x.1)) ?_ _ _ ?_
  · exact (Scheme.ofArrows_mem_smallEtaleTopology_iff _).2
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (hT y))
  rintro U' g' hg'
  obtain ⟨x, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg'
  rw [← presheaf_map_map_apply FX a (g x.1), ← presheaf_map_map_apply FX a (g x.1)]
  exact congrArg (FX.map a.op) (StageDescent.map_pullbackSectionsMap_of_transport e φ ef hef H s
    (g x.1) (m x) (h x) (hm x) (hθ x) (ψ x) (hψ x) (χ x) (hχ x) tg (htg x))

end Surjectivity

end Stacks.EtaleCohomology

end
