module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.StackOfSheafTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
import StacksFrontier.CategoryTheory.FibredOneMorphism
import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary

/-!
# Torsors in the fppf topology: the first two stack conditions

Let `B` be an algebraic space over a scheme `S` and let `G` be a group algebraic space over `B`,
and write `𝒢`, resp. `ℬ` for `G`, resp. `B` seen as a sheaf on the big fppf site of `S`. Stacks
04US asserts that the functor `p : G-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UR
(`AlgebraicGeometry.Space.FppfTorsors.projection`) defines a stack in groupoids over the big fppf
site of `S`, that is, the three conditions of Stacks 02ZI: `p` is fibred in groupoids, the
presheaves `Isom(X, X')` on `(Sch/U)_fppf` are sheaves, and every descent datum along a covering
is effective. This file proves conditions (1) and (2), from the corresponding conditions for
`𝒢/ℬ-Torsors` (Stacks 04UM) and the comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors` of
Stacks 04UT.

## Main definitions

* `AlgebraicGeometry.Space.FppfTorsors.ofSheafTorsors`: the object of `G-Torsors` underlying a
  torsor of sheaves which maps to the image of a torsor of algebraic spaces.
* `AlgebraicGeometry.Space.FppfTorsors.ofSheafTorsorsHom`: the morphism of `G-Torsors` underlying
  such a morphism of `𝒢/ℬ-Torsors`.

## Main results

* `AlgebraicGeometry.Space.FppfTorsors.isAlgebraicSpace_of_hom_comparison` and
  `AlgebraicGeometry.Space.FppfTorsors.isFppfTorsor_of_hom_comparison`: a torsor of sheaves
  mapping to the image of a torsor of algebraic spaces has an algebraic space as total space and
  is an fppf torsor in the sense of Stacks 04TY.
* `AlgebraicGeometry.Space.FppfTorsors.isHomLift_comparison_map`,
  `AlgebraicGeometry.Space.FppfTorsors.isHomLift_of_comparison_map` and
  `AlgebraicGeometry.Space.FppfTorsors.isStronglyCartesian_comparison_map`: a morphism of
  `G-Torsors` lies over a morphism of the site exactly when its image does, and its image is then
  strongly cartesian.
* `AlgebraicGeometry.Space.FppfTorsors.projection_isFiberedInGroupoids`: condition (1) of
  Stacks 02ZI for `p : G-Torsors ⥤ (Sch/S)_fppf`.
* `AlgebraicGeometry.Space.FppfTorsors.projection_isomIsSheaf`: condition (2) of Stacks 02ZI for
  `p`.

## References

* [Stacks Project, Tag 04US](https://stacks.math.columbia.edu/tag/04US)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 04UM](https://stacks.math.columbia.edu/tag/04UM)
* [Stacks Project, Tag 04UT](https://stacks.math.columbia.edu/tag/04UT)
* [Stacks Project, Tag 03ZZ](https://stacks.math.columbia.edu/tag/03ZZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  {G : GroupAlgebraicSpace 𝒞 S hS B hB}

namespace FppfTorsors

/-! ### Torsors of sheaves over a torsor of algebraic spaces -/

/-- The total space of a torsor of sheaves which admits a morphism to the image under the
comparison functor of an fppf torsor of algebraic spaces is an algebraic space. -/
theorem isAlgebraicSpace_of_hom_comparison {T : SheafTorsors G.obj} {T' : FppfTorsors hB G}
    (φ : T ⟶ (comparison hB G).obj T') : IsAlgebraicSpace 𝒞 S hS T.total.left :=
  isAlgebraicSpace_of_iso 𝒞 S hS (SheafTorsors.Hom.isPullback φ).isoPullback.symm
    (isAlgebraicSpace_pullback 𝒞 S hS T'.total.hom (yoneda.map (SheafTorsors.Hom.base φ))
      T'.isAlgebraicSpace (isAlgebraicSpace_yoneda 𝒞 S hS T.base)
      (isAlgebraicSpace_yoneda 𝒞 S hS T'.base))

/-- A torsor of sheaves which admits a morphism to the image under the comparison functor of an
fppf torsor of algebraic spaces is an fppf torsor in the sense of Stacks 04TY. -/
theorem isFppfTorsor_of_hom_comparison {T : SheafTorsors G.obj} {T' : FppfTorsors hB G}
    (φ : T ⟶ (comparison hB G).obj T') :
    @IsFppfTorsor 𝒞 S hS (yoneda.obj T.base) (isAlgebraicSpace_yoneda 𝒞 S hS T.base)
      (fppfPullbackGroup hB G T.base T.sec).obj.X T.total _ T.action
      (fppfPullbackGroup hB G T.base T.sec).property
      (isAlgebraicSpace_of_hom_comparison φ) := by
  obtain ⟨I, Bi, f, hBi, hcover, hsections⟩ := T'.isTorsor.2
  let b : T.base ⟶ T'.base := SheafTorsors.Hom.base φ
  let Utgt : AlgebraicSpaces 𝒞 S hS :=
    ⟨yoneda.obj T'.base, isAlgebraicSpace_yoneda 𝒞 S hS T'.base⟩
  let A (i : I) : AlgebraicSpaces 𝒞 S hS := ⟨Bi i, hBi i⟩
  let g : (⟨yoneda.obj T.base, isAlgebraicSpace_yoneda 𝒞 S hS T.base⟩ :
      AlgebraicSpaces 𝒞 S hS) ⟶ Utgt := ObjectProperty.homMk (yoneda.map b)
  let fA (i : I) : A i ⟶ Utgt := ObjectProperty.homMk (f i)
  let A' (i : I) : AlgebraicSpaces 𝒞 S hS := AlgebraicSpaces.fiberProduct 𝒞 S hS g (fA i)
  let f' (i : I) : (A' i).1 ⟶ yoneda.obj T.base := pullback.fst g.hom (fA i).hom
  refine ⟨T.isPseudoTorsor, I, (fun i => (A' i).1), f', (fun i => (A' i).property),
    isFppfCovering_fibreProduct 𝒞 S hS A fA g hcover, ?_⟩
  intro i
  obtain ⟨s⟩ := hsections i
  have hs : s.left ≫ pullback.snd T'.total.hom (f i) = 𝟙 _ := by simpa using s.w
  have hsection : s.left ≫ pullback.snd T'.total.hom (f i) ≫ f i = f i := by
    rw [← Category.assoc, hs, Category.id_comp]
  have hsx : (pullback.snd g.hom (fA i).hom ≫ s.left ≫ pullback.fst T'.total.hom (f i)) ≫
      T'.total.hom = f' i ≫ yoneda.map b := by
    simp only [Category.assoc, pullback.condition (f := T'.total.hom) (g := f i)]
    rw [hsection]
    exact (pullback.condition (f := g.hom) (g := (fA i).hom)).symm
  have ht : ((SheafTorsors.Hom.isPullback φ).lift _ (f' i) hsx) ≫ T.total.hom = 𝟙 _ ≫ f' i := by
    rw [Category.id_comp]
    exact (SheafTorsors.Hom.isPullback φ).lift_snd _ _ _
  exact ⟨Over.homMk (pullback.lift _ (𝟙 _) ht) (pullback.lift_snd _ _ ht)⟩

/-- The object of `G-Torsors` underlying a torsor of sheaves `T` which admits a morphism to the
image under the comparison functor of an object of `G-Torsors`, with the same base, section,
total space and action. -/
def ofSheafTorsors {T : SheafTorsors G.obj} {T' : FppfTorsors hB G}
    (φ : T ⟶ (comparison hB G).obj T') : FppfTorsors hB G where
  base := T.base
  sec := T.sec
  total := T.total
  isAlgebraicSpace := isAlgebraicSpace_of_hom_comparison φ
  action := T.action
  isTorsor := isFppfTorsor_of_hom_comparison φ

/-- A morphism of `𝒢/ℬ-Torsors` into the image under the comparison functor of an object of
`G-Torsors`, viewed as a morphism of `G-Torsors`. -/
def ofSheafTorsorsHom {T : SheafTorsors G.obj} {T' : FppfTorsors hB G}
    (φ : T ⟶ (comparison hB G).obj T') : ofSheafTorsors φ ⟶ T' where
  base := SheafTorsors.Hom.base φ
  comp_sec := SheafTorsors.Hom.comp_sec φ
  map := SheafTorsors.Hom.map φ
  isPullback := SheafTorsors.Hom.isPullback φ
  smul_comp := SheafTorsors.Hom.smul_comp φ

/-- The comparison functor sends `ofSheafTorsors φ` to `T`. -/
@[simp]
theorem comparison_obj_ofSheafTorsors {T : SheafTorsors G.obj} {T' : FppfTorsors hB G}
    (φ : T ⟶ (comparison hB G).obj T') : (comparison hB G).obj (ofSheafTorsors φ) = T :=
  rfl

/-- The comparison functor sends `ofSheafTorsorsHom φ` to `φ`. -/
@[simp]
theorem comparison_map_ofSheafTorsorsHom {T : SheafTorsors G.obj} {T' : FppfTorsors hB G}
    (φ : T ⟶ (comparison hB G).obj T') : (comparison hB G).map (ofSheafTorsorsHom φ) = φ :=
  rfl

/-! ### Lifts and restrictions across the comparison functor -/

/-- A morphism of `G-Torsors` lying over a morphism of the site is sent by the comparison functor
to a morphism of `𝒢/ℬ-Torsors` lying over the same morphism of the site. -/
theorem isHomLift_comparison_map {T T' : FppfTorsors hB G} {V U : BigFppfOver 𝒞 S hS}
    (f : V ⟶ U) (φ : T ⟶ T') (h : (projection hB G).IsHomLift f φ) :
    (SheafTorsors.projection G.obj).IsHomLift f ((comparison hB G).map φ) :=
  let _ := h
  Functor.isHomLift_map_of_comp_eq (comparison_comp_projection hB G) f φ

/-- A morphism of `G-Torsors` whose image under the comparison functor lies over a morphism of the
site lies over that morphism itself. -/
theorem isHomLift_of_comparison_map {T T' : FppfTorsors hB G} {V U : BigFppfOver 𝒞 S hS}
    (f : V ⟶ U) (φ : T ⟶ T')
    (h : (SheafTorsors.projection G.obj).IsHomLift f ((comparison hB G).map φ)) :
    (projection hB G).IsHomLift f φ :=
  let _ := h
  Functor.isHomLift_of_isHomLift_map (comparison_comp_projection hB G) f φ

/-- The image under the comparison functor of a morphism of `G-Torsors` lying over a morphism of
the site is strongly cartesian. -/
theorem isStronglyCartesian_comparison_map {T T' : FppfTorsors hB G} {V U : BigFppfOver 𝒞 S hS}
    (f : V ⟶ U) (φ : T ⟶ T') (h : (projection hB G).IsHomLift f φ) :
    (SheafTorsors.projection G.obj).IsStronglyCartesian f ((comparison hB G).map φ) :=
  let _ := isHomLift_comparison_map f φ h
  (SheafTorsors.projection_isFiberedInGroupoids G.obj).isStronglyCartesian_homLift f _

/-! ### The first two conditions of Stacks 02ZI -/

/-- Condition (1) of Stacks 02ZI for the functor `p : G-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UR:
`p` is fibred in groupoids. -/
@[stacks 04US "condition (1): p is fibred in groupoids"]
theorem projection_isFiberedInGroupoids : (projection hB G).IsFiberedInGroupoids where
  exists_lift := by
    intro V U f T hT
    obtain ⟨R, φ, hφ⟩ :=
      (SheafTorsors.projection_isFiberedInGroupoids G.obj).exists_lift f
        ((comparison hB G).obj T) hT
    exact ⟨ofSheafTorsors φ, ofSheafTorsorsHom φ,
      isHomLift_of_comparison_map f (ofSheafTorsorsHom φ) hφ⟩
  unique_lift := by
    intro x y z φ ψ f hf
    obtain ⟨χ, ⟨hχ₁, hχ₂⟩, hχu⟩ :=
      (SheafTorsors.projection_isFiberedInGroupoids G.obj).unique_lift
        ((comparison hB G).map φ) ((comparison hB G).map ψ) f hf
    refine ⟨(comparison hB G).preimage χ, ⟨?_, ?_⟩, ?_⟩
    · rwa [show (projection hB G).map ((comparison hB G).preimage χ) =
        (SheafTorsors.projection G.obj).map ((comparison hB G).map
          ((comparison hB G).preimage χ)) from rfl, (comparison hB G).map_preimage]
    · apply (comparison hB G).map_injective
      rwa [Functor.map_comp, (comparison hB G).map_preimage]
    · intro θ hθ
      apply (comparison hB G).map_injective
      rw [(comparison hB G).map_preimage]
      exact hχu ((comparison hB G).map θ) ⟨hθ.1, by rw [← Functor.map_comp, hθ.2]⟩

/-! ### Restrictions across the comparison functor -/

/-- The image under the comparison functor of a restriction of an object of `G-Torsors` along a
morphism of the site: the image object with the image of the cartesian morphism, which is again
cartesian. -/
private def comparisonRestriction {V U : BigFppfOver 𝒞 S hS} (f : V ⟶ U)
    {T : FppfTorsors hB G} (hx : (projection hB G).obj T = U)
    (r : Functor.Restriction (projection hB G) f T hx) :
    Functor.Restriction (SheafTorsors.projection G.obj) f ((comparison hB G).obj T) hx where
  pt := (comparison hB G).obj r.pt
  hpt := r.hpt
  hom := (comparison hB G).map r.hom
  isHomLift := isHomLift_comparison_map _ r.hom r.isHomLift
  isCart := isStronglyCartesian_comparison_map _ r.hom r.isHomLift

/-- The comparison functor carries the canonical comparison of two restrictions of one object of
`G-Torsors` to the canonical comparison of their images. -/
private theorem comparisonRestriction_compTo {W V U : BigFppfOver 𝒞 S hS} (g : W ⟶ V)
    (f : V ⟶ U) {m : W ⟶ U} (hm : m = g ≫ f) {T : FppfTorsors hB G}
    {hx : (projection hB G).obj T = U}
    (r : Functor.Restriction (projection hB G) f T hx)
    (s : Functor.Restriction (projection hB G) m T hx) :
    (comparison hB G).map (Functor.Restriction.compTo _ g f hm r s) =
      Functor.Restriction.compTo _ g f hm (comparisonRestriction f hx r)
        (comparisonRestriction m hx s) := by
  let _ := (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
  refine Functor.Restriction.eq_compTo g f hm (comparisonRestriction f hx r)
    (comparisonRestriction m hx s)
    ((comparison hB G).map (Functor.Restriction.compTo _ g f hm r s)) ?_ ?_
  · exact isHomLift_comparison_map g _ (Functor.Restriction.isHomLift_compTo g f hm r s)
  · exact ((comparison hB G).map_comp _ _).symm.trans
      (congrArg (comparison hB G).map
        (Functor.Restriction.compTo_hom (projection hB G) g f hm r s))

/-- A functor carries an equality of composites of two morphisms to an equality of composites. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z W : C} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ W} {d : W ⟶ Z}
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  simp only [← F.map_comp, h]

/-- The comparison functor carries a morphism of restrictions which is the canonical restriction
of another to the canonical restriction of its image. -/
private theorem comparisonRestriction_isRestrictionOf {W V Ux Uy : BigFppfOver 𝒞 S hS}
    (g : W ⟶ V) {fx : V ⟶ Ux} {fy : V ⟶ Uy} {mx : W ⟶ Ux} {my : W ⟶ Uy}
    (hfx : mx = g ≫ fx) (hfy : my = g ≫ fy) {x y : FppfTorsors hB G}
    {hx : (projection hB G).obj x = Ux} {hy : (projection hB G).obj y = Uy}
    (xr : Functor.Restriction (projection hB G) fx x hx)
    (yr : Functor.Restriction (projection hB G) fy y hy)
    (xs : Functor.Restriction (projection hB G) mx x hx)
    (ys : Functor.Restriction (projection hB G) my y hy)
    (α : xr.pt ⟶ yr.pt) (β : xs.pt ⟶ ys.pt)
    (h : Functor.IsRestrictionOf _ g hfx hfy xr yr xs ys α β) :
    Functor.IsRestrictionOf _ g hfx hfy (comparisonRestriction fx hx xr)
      (comparisonRestriction fy hy yr) (comparisonRestriction mx hx xs)
      (comparisonRestriction my hy ys) ((comparison hB G).map α) ((comparison hB G).map β) := by
  change (comparison hB G).map β ≫ _ = _ ≫ (comparison hB G).map α
  rw [← comparisonRestriction_compTo g fy hfy yr ys,
    ← comparisonRestriction_compTo g fx hfx xr xs]
  exact map_comp_eq_map_comp (comparison hB G) h

/-- Condition (2) of Stacks 02ZI for the functor `p : G-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UR:
for two objects `(U, b, X)` and `(U, b', X')` over the same object of the big fppf site of `S`,
the presheaf `Isom(X, X')` is a sheaf. -/
@[stacks 04US "condition (2): the Isom presheaves are sheaves"]
theorem projection_isomIsSheaf
    {U : BigFppfOver 𝒞 S hS} (x y : FppfTorsors hB G)
    (hx : (projection hB G).obj x = U) (hy : (projection hB G).obj y = U)
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U)
    (Vij : I → I → BigFppfOver 𝒞 S hS)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Functor.Restriction (projection hB G) (f i) x hx)
    (yr : ∀ i, Functor.Restriction (projection hB G) (f i) y hy)
    (xrij : ∀ i j, Functor.Restriction (projection hB G) (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Functor.Restriction (projection hB G) (pr₁ i j ≫ f i) y hy) :
    Functor.IsomIsSheafFor (projection hB G) x y hx hy V f Vij pr₁ pr₂ hVij
      xr yr xrij yrij := by
  intro φ hφ hφiso hcompat
  let F := comparison hB G
  let xr' := fun i => comparisonRestriction (f i) hx (xr i)
  let yr' := fun i => comparisonRestriction (f i) hy (yr i)
  let xs' := fun i j => comparisonRestriction (pr₁ i j ≫ f i) hx (xrij i j)
  let ys' := fun i j => comparisonRestriction (pr₁ i j ≫ f i) hy (yrij i j)
  have hφ' : ∀ i, Functor.FibreHom _ (xr' i).pt (yr' i).pt (xr' i).hpt (yr' i).hpt
      (F.map (φ i)) := fun i => isHomLift_comparison_map _ (φ i) (hφ i)
  have hiso : ∀ i, IsIso (F.map (φ i)) := fun i => by
    let _ := hφiso i
    infer_instance
  have hc : ∀ i j, ∃ gam : (xs' i j).pt ⟶ (ys' i j).pt,
      Functor.FibreHom _ _ _ (xs' i j).hpt (ys' i j).hpt gam ∧
      Functor.IsRestrictionOf _ (pr₁ i j) rfl rfl (xr' i) (yr' i)
        (xs' i j) (ys' i j) (F.map (φ i)) gam ∧
      Functor.IsRestrictionOf _ (pr₂ i j) (hVij i j).w (hVij i j).w (xr' j) (yr' j)
        (xs' i j) (ys' i j) (F.map (φ j)) gam := by
    intro i j
    obtain ⟨gam, hgam, hi, hj⟩ := hcompat i j
    exact ⟨F.map gam, isHomLift_comparison_map _ gam hgam,
      comparisonRestriction_isRestrictionOf _ _ _ _ _ _ _ _ _ hi,
      comparisonRestriction_isRestrictionOf _ _ _ _ _ _ _ _ _ hj⟩
  obtain ⟨g, ⟨hg, hgi, hgr⟩, huniq⟩ :=
    SheafTorsors.projection_isomIsSheaf G.obj hB.isSheaf (F.obj x) (F.obj y) hx hy V f hf Vij
      pr₁ pr₂ hVij xr' yr' xs' ys' (fun i => F.map (φ i)) hφ' hiso hc
  refine ⟨F.preimage g, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact isHomLift_of_comparison_map _ (F.preimage g) (by rwa [F.map_preimage])
  · have : IsIso (F.map (F.preimage g)) := by rw [F.map_preimage]; exact hgi
    exact isIso_of_fully_faithful F (F.preimage g)
  · intro i
    apply F.map_injective
    rw [Functor.map_comp, Functor.map_comp, F.map_preimage]
    exact hgr i
  · rintro k ⟨hk, hki, hkr⟩
    apply F.map_injective
    rw [F.map_preimage]
    refine huniq (F.map k) ⟨isHomLift_comparison_map _ k hk, ?_, ?_⟩
    · let _ := hki
      infer_instance
    · intro i
      exact map_comp_eq_map_comp F (hkr i)

end FppfTorsors

end AlgebraicGeometry.Space

end
