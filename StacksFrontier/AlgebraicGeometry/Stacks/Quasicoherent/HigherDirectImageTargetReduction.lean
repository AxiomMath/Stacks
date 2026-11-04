module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageEquivalenceTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.PresheafBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition

/-!
# Reducing Stacks 076Z to a target representable by an affine scheme

Let `M` be a rule satisfying hypotheses (1), (2) and (3) of **Stacks 076Z**. If the higher direct
images along every quasi-compact quasi-separated 1-morphism *into the stack of an affine scheme*
carry `M` into `M`, then so do the higher direct images along every quasi-compact quasi-separated
1-morphism of algebraic stacks. This is the first paragraph of the source's proof: choose smooth
1-morphisms `uⱼ : (Sch/Uⱼ)_fppf ⟶ 𝒴` from affine schemes jointly surjective on points (a smooth
surjective chart by a scheme, followed by an affine open covering of that scheme), base change
along them (**Stacks 075H**), and conclude by hypothesis (3).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_affine_smooth_cover`: an algebraic stack is
  covered, on points, by a family of smooth 1-morphisms from stacks of affine schemes.
* `AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_affineTarget`: the reduction.

## Implementation notes

The higher direct images of `AlgebraicGeometry.Stack.StackEtaleModuleRule.PreservedBy` are formed
along strict presentations, whose structure functors are composites. A base change produces
structure functors equal to those, but not syntactically; `PreservedByAlong` states the
condition for an arbitrary pair of structure functors, and `preservedByAlong_congr` moves it
along equalities of them.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **An algebraic stack is covered by smooth 1-morphisms from stacks of affine schemes.** Every
algebraic stack `𝒴` over `S` has a family of smooth 1-morphisms `(Sch/Uⱼ)_fppf ⟶ 𝒴` with each
`Uⱼ` affine, whose images on points cover the points of `𝒴`: a smooth surjective chart by a
scheme of the site, precomposed with the inclusions of the affine opens of that scheme. -/
theorem exists_affine_smooth_cover (𝒴 : AlgebraicStacks.{u, t} B S hS) :
    ∃ (J : Type u) (U : J → BigFppfOver B S hS)
      (v : ∀ j, schemeStack.{u, t} B S hS (U j) ⟶ 𝒴),
      (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (U j))) ∧
      (∀ j, IsSmooth B S hS (v j)) ∧
      ∀ y : points B S hS 𝒴, ∃ j, ∃ x : points B S hS (schemeStack.{u, t} B S hS (U j)),
        pointsMap B S hS (v j) x = y := by
  obtain ⟨T, a, hasm, hasu⟩ := Stack.exists_smooth_surjective_schemeStack.{u, t} B S hS 𝒴
  let affineOpenObject : ((BigFppfOver.toScheme B S hS).obj T).affineOpens → BigFppfOver B S hS :=
    fun i => Over.mk (⟨i.1.ι ≫ B.inclusion.map T.hom⟩ :
      B.obj (Scheme.size_lt_of_isOpenImmersion i.1.ι T.left.property) ⟶ B.obj hS)
  let affineOpenObjectHom : ∀ i, affineOpenObject i ⟶ T := fun i => Over.homMk ⟨i.1.ι⟩ rfl
  refine ⟨((BigFppfOver.toScheme B S hS).obj T).affineOpens, affineOpenObject,
    fun i => schemeStackMap.{u, t} B S hS (affineOpenObjectHom i) ≫ a, fun i => i.2,
    fun i => isSmooth_comp B S hS _ _ (isSmooth_schemeStackMap B S hS _
      (inferInstanceAs (Smooth (i : ((BigFppfOver.toScheme B S hS).obj T).Opens).ι))) hasm,
    fun y => ?_⟩
  obtain ⟨z, rfl⟩ := hasu y
  let _ := Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS T)
  let _ : ∀ i : ((BigFppfOver.toScheme B S hS).obj T).affineOpens,
      TopologicalSpace (Stack.points B S hS
        (Stack.schemeFibredCategory B S hS (affineOpenObject i)).val
        (Stack.schemeFibredCategory B S hS (affineOpenObject i)).property) :=
    fun i => Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS (affineOpenObject i))
  obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hxV₀, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (Stack.pointsHomeomorphScheme B S hS T z)) isOpen_univ
  refine ⟨⟨V₀, hV₀⟩, (Stack.pointsHomeomorphScheme B S hS
    (affineOpenObject ⟨V₀, hV₀⟩)).symm ⟨Stack.pointsHomeomorphScheme B S hS T z, hxV₀⟩, ?_⟩
  rw [pointsMap_comp]
  refine congrArg (pointsMap B S hS a) ((Stack.pointsHomeomorphScheme B S hS T).injective ?_)
  exact (Stack.pointsHomeomorphScheme_naturality B S hS (affineOpenObjectHom ⟨V₀, hV₀⟩)
    ((Stack.pointsHomeomorphScheme B S hS (affineOpenObject ⟨V₀, hV₀⟩)).symm
      ⟨Stack.pointsHomeomorphScheme B S hS T z, hxV₀⟩)).trans (congrArg _
    ((Stack.pointsHomeomorphScheme B S hS (affineOpenObject ⟨V₀, hV₀⟩)).apply_symm_apply _))

end AlgebraicStacks

/-- The two composites around the 2-fibre product square of `f : 𝒳 ⟶ 𝒴` and `v : 𝒰 ⟶ 𝒴` agree
with the structure functor of `𝒴`. -/
private theorem homFunctor_snd_comp_p_eq_homFunctor_fst_comp_p
    {𝒳 𝒰 𝒴 : AlgebraicStacks.{u, t} B S hS}
    (f : 𝒳 ⟶ 𝒴) (v : 𝒰 ⟶ 𝒴) :
    CatFiberedInGroupoids.homFunctor (twoFibreProductSquareAlgebraicStacks B S hS f v).snd.hom ⋙
        CatFiberedInGroupoids.homFunctor v.hom ⋙ 𝒴.val.val.p =
      CatFiberedInGroupoids.homFunctor (twoFibreProductSquareAlgebraicStacks B S hS f v).fst.hom ⋙
        CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p := by
  simp only [CatFiberedInGroupoids.homFunctor_comp_p]

/-- The 2-cell of the 2-fibre product square of `f : 𝒳 ⟶ 𝒴` and `v : 𝒰 ⟶ 𝒴` is vertical. -/
private theorem twoSquareIsVertical_twoFibreProductSquareAlgebraicStacks
    {𝒳 𝒰 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) (v : 𝒰 ⟶ 𝒴) :
    TwoSquareIsVertical B S hS
      (CatFiberedInGroupoids.homFunctor (twoFibreProductSquareAlgebraicStacks B S hS f v).fst.hom ⋙
        CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (CatFiberedInGroupoids.homFunctor v.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor (twoFibreProductSquareAlgebraicStacks B S hS f v).fst.hom)
      (CatFiberedInGroupoids.homFunctor (twoFibreProductSquareAlgebraicStacks B S hS f v).snd.hom)
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor v.hom)
      rfl (homFunctor_snd_comp_p_eq_homFunctor_fst_comp_p B S hS f v) rfl rfl
      (TwoFibreProductOver.psiIso 𝒳.val.val.p 𝒰.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor v.hom)).hom :=
  fun z => by
    have := TwoFibreProductOver.psiIso_hom_vertical (p𝒳 := 𝒳.val.val.p) (p𝒴 := 𝒰.val.val.p)
      (p𝒮 := 𝒴.val.val.p) (F := CatFiberedInGroupoids.homFunctor f.hom)
      (G := CatFiberedInGroupoids.homFunctor v.hom) z
    change 𝒴.val.val.p.map ((TwoFibreProductOver.psiIso _ _ _ _ _).hom.app z) = _
    rw [IsHomLift.fac' 𝒴.val.val.p (𝟙 z.base)
      ((TwoFibreProductOver.psiIso _ _ _ _ _).hom.app z)]
    simp
    rfl

namespace StackEtaleModuleRule

/-- **The conclusion of Stacks 076Z along a functor, for arbitrary structure functors.** For
`φ : 𝒳 ⥤ 𝒴` strictly over the base, with `φ ⋙ q = p`, the higher direct image `Rⁱφ_*` carries
members of the rule on the associated étale site of `p` to members of the rule on that of `q`.
`AlgebraicGeometry.Stack.StackEtaleModuleRule.PreservedBy` is the case of a strict presentation
(`preservedBy_iff_preservedByAlong`). -/
noncomputable abbrev PreservedByAlong (M : StackEtaleModuleRule B S hS) {𝒳 𝒴 : Type (u + 1)}
    [Category.{u} 𝒳] [Category.{u} 𝒴] (φ : 𝒳 ⥤ 𝒴) (p : 𝒳 ⥤ BigFppfOver B S hS)
    (q : 𝒴 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hφ : φ ⋙ q = p) (i : ℕ) : Prop :=
  letI := hasSheafify_associatedTopology_of_category_succ B S hS p
  letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS p
  letI := hasSheafify_associatedTopology_of_category_succ B S hS q
  letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS q
  ∀ F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)),
    M p hp F.val →
      M q hq ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS p q hp hq φ hφ
        (etaleTopology B) (etaleTopology_le_topology B) i).obj F).val

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, `PreservedBy` is `PreservedByAlong` for
the underlying functor of `f`, with structure functors `f ⋙ p_𝒴` and `p_𝒴`. -/
theorem preservedBy_iff_preservedByAlong (M : StackEtaleModuleRule B S hS)
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) (i : ℕ) :
    PreservedBy B S hS M f i ↔
      PreservedByAlong B S hS M (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids rfl i :=
  Iff.rfl

/-- `PreservedByAlong` depends on the structure functors only up to equality. -/
theorem preservedByAlong_congr (M : StackEtaleModuleRule B S hS) {𝒳 𝒴 : Type (u + 1)}
    [Category.{u} 𝒳] [Category.{u} 𝒴] (φ : 𝒳 ⥤ 𝒴) {p p' : 𝒳 ⥤ BigFppfOver B S hS}
    {q q' : 𝒴 ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hp' : p'.IsFiberedInGroupoids) (hq' : q'.IsFiberedInGroupoids)
    (hφ : φ ⋙ q = p) (hφ' : φ ⋙ q' = p') (epp : p = p') (eqq : q = q') (i : ℕ)
    (h : PreservedByAlong B S hS M φ p q hp hq hφ i) :
    PreservedByAlong B S hS M φ p' q' hp' hq' hφ' i := by
  subst epp eqq
  exact h

/-- The inverse image of presheaves of modules along a 1-morphism of algebraic stacks is the
underlying presheaf of the inverse image of sheaves of modules. -/
theorem stackModulePresheafPullback_obj_val {𝒵 𝒳 : AlgebraicStacks.{u, t} B S hS} (g : 𝒵 ⟶ 𝒳)
    (X : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))) :
    (stackModulePresheafPullback.{u, t, u + 1} B S hS g).obj X.val =
      ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
        (CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒳.val.val.p) 𝒳.val.val.p
        (isFiberedInGroupoids_homFunctor_comp B S hS g.hom) 𝒳.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor g.hom) rfl (etaleTopology B)
        (etaleTopology_le_topology B)).obj X).val :=
  rfl

/-- **Base change of the conclusion of Stacks 076Z along a smooth faithful 1-morphism of the
target.** Let `M` satisfy hypotheses (1) and (2) of **Stacks 076Z**, let `f : 𝒳 ⟶ 𝒴` and let
`v : 𝒰 ⟶ 𝒴` be smooth with faithful underlying functor. If the higher direct images along the
base change `𝒳 ×_𝒴 𝒰 ⟶ 𝒰` of `f` carry `M` into `M` in degree `i`, then `v⁻¹Rⁱf_*ℱ` is a member
of `M` for every member `ℱ`.

`v⁻¹Rⁱf_*ℱ ≅ Rⁱf'_*(v')⁻¹ℱ` by **Stacks 075H**
(`AlgebraicGeometry.Stack.moduleHigherDirectImageGuitartBaseChangeIso`, the 2-fibre product
square being Guitart exact by **Stacks 075B** and its projection `v'` to `𝒳` faithful), and
`(v')⁻¹ℱ` is a member by hypothesis (2), `v'` being smooth as a base change of `v`. -/
theorem mem_pullback_higherDirectImage_of_baseChange (M : StackEtaleModuleRule B S hS)
    (hserre : IsWeakSerre.{u, t} B S hS M)
    (hpull : IsStableUnderSmoothPullback.{u, t} B S hS M)
    {𝒳 𝒰 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) (v : 𝒰 ⟶ 𝒴)
    (hv : AlgebraicStacks.IsSmooth B S hS v)
    [(CatFiberedInGroupoids.homFunctor v.hom).Faithful] (i : ℕ)
    (hbc : PreservedBy B S hS M (twoFibreProductSquareAlgebraicStacks B S hS f v).snd i)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hF : M (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) F.val) :
    letI := hasSheafify_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    M (CatFiberedInGroupoids.homFunctor v.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS v.hom)
      ((stackModulePresheafPullback.{u, t, u + 1} B S hS v).obj
        ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
          (etaleTopology_le_topology B) i).obj F).val) := by
  let P := twoFibreProductSquareAlgebraicStacks B S hS f v
  let a := CatFiberedInGroupoids.homFunctor P.fst.hom
  let b := CatFiberedInGroupoids.homFunctor P.snd.hom
  let pZ := a ⋙ CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p
  let pY' := CatFiberedInGroupoids.homFunctor v.hom ⋙ 𝒴.val.val.p
  have hpZ : pZ.IsFiberedInGroupoids :=
    isFiberedInGroupoids_homFunctor_comp B S hS (strictChart B S hS P.fst f).hom
  have hb : b ⋙ pY' = pZ := homFunctor_snd_comp_p_eq_homFunctor_fst_comp_p B S hS f v
  let w : TwoSquare a b (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor v.hom) :=
    (TwoFibreProductOver.psiIso 𝒳.val.val.p 𝒰.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor v.hom)).hom
  have : w.GuitartExact :=
    TwoFibreProductOver.guitartExact_twoFibreProductSquare 𝒳.val.val.p 𝒰.val.val.p
      𝒴.val.val.p _ _ 𝒳.val.isFiberedInGroupoids 𝒰.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p v.hom)
  have : a.Faithful := TwoFibreProductOver.faithful_fst_of_faithful
  have : HasEqualizers P.pt.val.val.obj := AlgebraicStacks.hasEqualizers B S hS P.pt
  let := hasSheafify_associatedTopology_of_category_succ B S hS pZ
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS pZ
  let := hasSheafify_associatedTopology_of_category_succ B S hS pY'
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS pY'
  let e := moduleHigherDirectImageGuitartBaseChangeIso B S hS pZ
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) pY' 𝒴.val.val.p hpZ
    (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
    (isFiberedInGroupoids_homFunctor_comp B S hS v.hom) 𝒴.val.isFiberedInGroupoids a b
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor v.hom)
    rfl hb rfl rfl w (etaleTopology B) (etaleTopology_le_topology B)
    (twoSquareIsVertical_twoFibreProductSquareAlgebraicStacks B S hS f v) i F
  have hmem : M pZ hpZ ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS pZ
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) hpZ
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) a rfl (etaleTopology B)
      (etaleTopology_le_topology B)).obj F).val :=
    hpull (strictChart B S hS P.fst f) (isSmooth_strictChart B S hS P.fst f
      (AlgebraicStacks.isSmooth_baseChange B S hS v f P
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f v) hv)) F hF
  have hbc' := preservedByAlong_congr B S hS M b (p := b ⋙ 𝒰.val.val.p) (p' := pZ)
    (q := 𝒰.val.val.p) (q' := pY') (isFiberedInGroupoids_homFunctor_comp B S hS P.snd.hom)
    𝒰.val.isFiberedInGroupoids hpZ (isFiberedInGroupoids_homFunctor_comp B S hS v.hom) rfl hb
    ((congrArg (b ⋙ ·) (CatFiberedInGroupoids.homFunctor_comp_p v.hom).symm).trans hb)
    (CatFiberedInGroupoids.homFunctor_comp_p v.hom).symm i
    ((preservedBy_iff_preservedByAlong B S hS M P.snd i).1 hbc)
  let : Abelian (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (AlgebraicStacks.strictSource B S hS v).val.val.p
      (AlgebraicStacks.strictSource B S hS v).val.isFiberedInGroupoids (etaleTopology B)
      (etaleTopology_le_topology B))) :=
    SheafOfModules.instAbelian.{u + 1, u, u, u + 1} _
  have : (toObjectProperty.{u, t} B S hS M
      (AlgebraicStacks.strictSource B S hS v)).IsWeakSerreClass :=
    hserre _
  rw [stackModulePresheafPullback_obj_val]
  exact (toObjectProperty.{u, t} B S hS M (AlgebraicStacks.strictSource B S hS v)).prop_of_iso
    e.symm (hbc' _ hmem)

/-- **The reduction of Stacks 076Z to a target representable by an affine scheme.** Let `M`
satisfy hypotheses (1), (2) and (3) of **Stacks 076Z**, the last for families indexed in any
universe containing `u`. If the higher direct images along every quasi-compact quasi-separated
1-morphism into the stack of an affine scheme carry `M` into `M`, then so do those along every
quasi-compact quasi-separated 1-morphism `f : 𝒳 ⟶ 𝒴`.

This is the first paragraph of the source's proof. The stack `𝒴` is covered on points by smooth
1-morphisms `vⱼ : (Sch/Uⱼ)_fppf ⟶ 𝒴` with `Uⱼ` affine
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_affine_smooth_cover`), whose functors are
faithful because the stack of a scheme is fibred in setoids. The base change of `f` along `vⱼ`
is quasi-compact and quasi-separated (**Stacks 050V**, **Stacks 050F**), so its higher direct
images carry `M` into `M`; base change (**Stacks 075H**,
`AlgebraicGeometry.Stack.StackEtaleModuleRule.mem_pullback_higherDirectImage_of_baseChange`)
puts every `vⱼ⁻¹Rⁱf_*ℱ` in `M`, and hypothesis (3) puts `Rⁱf_*ℱ` in `M`. -/
theorem preservedBy_of_affineTarget (M : StackEtaleModuleRule B S hS)
    (hserre : IsWeakSerre.{u, t} B S hS M)
    (hpull : IsStableUnderSmoothPullback.{u, t} B S hS M)
    (hloc : IsSmoothLocal.{u, t, max u s} B S hS M)
    (haff : ∀ {𝒳' : AlgebraicStacks.{u, t} B S hS} {X : BigFppfOver B S hS},
      IsAffine ((BigFppfOver.toScheme B S hS).obj X) →
      ∀ f' : 𝒳' ⟶ schemeStack.{u, t} B S hS X, IsQuasiCompactMorphism B S hS f' →
        AlgebraicStacks.IsQuasiSeparated B S hS f' → ∀ i : ℕ, PreservedBy B S hS M f' i)
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f) (i : ℕ) : PreservedBy B S hS M f i := by
  intro F hF
  obtain ⟨J, U, v, hUaff, hvsm, hcov⟩ := AlgebraicStacks.exists_affine_smooth_cover B S hS 𝒴
  refine (hloc (J := ULift.{max u s} J) (𝒲 := fun j => schemeStack.{u, t} B S hS (U j.down))
    (fun j => v j.down) (fun j => hvsm j.down) ?_ _).2 (fun j => ?_)
  · refine (Set.eq_univ_of_forall fun y => ?_).symm
    obtain ⟨j, x, hx⟩ := hcov y
    exact Set.mem_iUnion.2 ⟨⟨j⟩, x, hx⟩
  · have : (CatFiberedInGroupoids.homFunctor (v j.down).hom ⋙ 𝒴.val.val.p).Faithful := by
      rw [CatFiberedInGroupoids.homFunctor_comp_p]
      exact inferInstanceAs (Over.forget _).Faithful
    have : (CatFiberedInGroupoids.homFunctor (v j.down).hom).Faithful :=
      Functor.Faithful.of_comp _ 𝒴.val.val.p
    let P := twoFibreProductSquareAlgebraicStacks B S hS f (v j.down)
    have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f (v j.down)
    exact mem_pullback_higherDirectImage_of_baseChange B S hS M hserre hpull f (v j.down)
      (hvsm j.down) i (haff (hUaff j.down) P.snd
        (isQuasiCompactMorphism_baseChange B S hS f (v j.down) P.swap
          (Bicategory.isTwoFibreProduct_swap hP) hqc)
        (AlgebraicStacks.isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS f (v j.down)
          P hP hqs) i) F hF

end StackEtaleModuleRule

end AlgebraicGeometry.Stack

end
