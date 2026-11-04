module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.Empty
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.SectionFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparatedEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ImmersionSchemeTheoreticallyDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange

/-!
# Gluing the local sections in the proof of Stacks 0CQ7

The last reduction of the proof of [Stacks, Tag 0CQ7] (situation (g)) has local sections
`xᵢ : Uᵢ ⟶ 𝒳` of `f` over a proper base `q₀ : Y₀ ⟶ Y` and isomorphisms `φᵢⱼ` between the
restrictions of `xᵢ` and `xⱼ` to `Uᵢ ∩ Uⱼ`, satisfying the cocycle condition over a quasi-compact
open `V₀` contained in every `Uᵢ`. The source replaces `Y₀` by a space in which `V₀` is
scheme-theoretically dense, concludes the cocycle condition everywhere by Stacks 084N, because
the projections `Isom_𝒳(x, x') ⟶ Z` are proper, and glues the `xᵢ` because `𝒳` is a stack. Here
that space is the scheme-theoretic closure `Ȳ` of `V₀` in `Y₀` (Stacks 088G), and the result is
a section cover over `q₀` of `V₀` in the sense of
`AlgebraicGeometry.Stack.AlgebraicStacks.HasSectionCoverOver`, with `Ȳ ⟶ Y₀` the proper
morphism.

## Main results

All names are in the namespace `AlgebraicGeometry.Stack`.

* `AlgebraicStacks.exists_covering_sieve_of_points_cover`: open subspaces covering an algebraic
  space on points cover it locally for the fppf topology.
* `IsomFamily.eq_of_eq_on_dense`: Stacks 084N for families of isomorphisms between two points.
* `AlgebraicStacks.SectionFamily.isos_cocycle_of_isSchemeTheoreticallyDense`: the cocycle
  condition spreads from a scheme-theoretically dense open.
* `AlgebraicStacks.SectionFamily.hasSectionCoverOver_of_isos`: the gluing step.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Open subspaces covering an algebraic space on points cover it fppf locally.** Every section
`z` of `Z` over `T` lies in some `U i` after restriction along each arrow of a covering sieve of
`T`: by Stacks 03BZ the family is a Zariski covering, so the map from the coproduct of the `U i`
is locally surjective, and a section of `Z` in the image of that map lies in the union of the
`U i`. -/
theorem exists_covering_sieve_of_points_cover {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) {ι : Type} (U : ι → Subfunctor Z)
    (hU : ∀ i, Space.IsOpenSubspace B S hS (U i))
    (hcov : ∀ z : Space.points B S hS Z,
      ∃ i, z ∈ Set.range (Space.pointsMap B S hS (U i).toFunctor (U i).ι))
    (T : BigFppfOver B S hS) (z : Z.obj (op T)) :
    ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f →
        ∃ i, Z.map f.op z ∈ (U i).obj (op V) := by
  let U' : ULift.{u} ι → Subfunctor Z := fun i => U i.down
  have hZar : Space.IsZariskiCover B S hS (ULift.{u} ι) U' := by
    refine (Space.isZariskiCover_iff_iUnion_points B S hS Z hZ _ U' fun i => hU _).2 ?_
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨i, hi⟩ := hcov y
    exact Set.mem_iUnion.2 ⟨⟨i⟩, hi⟩
  have := hZar.2
  refine ⟨Presheaf.imageSieve (Sigma.desc fun i => (U' i).ι) z,
    Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) (Sigma.desc fun i => (U' i).ι)
      (U := op T) z, ?_⟩
  rintro V f ⟨t, ht⟩
  have hfac : (Sigma.desc fun i => (U' i).ι) =
      Sigma.desc (fun i => Subfunctor.homOfLe (le_iSup U' i)) ≫ (⨆ i, U' i).ι := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_desc, Sigma.ι_desc_assoc, Subfunctor.homOfLe_ι]
  have hmem : Z.map f.op z ∈ (⨆ i, U' i).obj (op V) := by
    rw [← ht, hfac]
    exact ((Sigma.desc fun i => Subfunctor.homOfLe (le_iSup U' i)).app (op V) t).2
  rw [Subfunctor.iSup_obj, Set.mem_iUnion] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact ⟨_, hi⟩

/-- **Two families of isomorphisms agreeing on a scheme-theoretically dense open agree**, when
the projection of the isomorphism space is proper: their sections over the identity agree on the
open, the projection is separated, and Stacks 084N applies. -/
theorem _root_.AlgebraicGeometry.Stack.IsomFamily.eq_of_eq_on_dense
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hZ : IsAlgebraicSpace B S hS Z}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {a b : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}
    (hprop : Space.IsProper B S hS (isomSpaceOverSpaceProj B S hS Z hZ a b))
    (D : Subfunctor Z) (hD : Space.IsOpenSubspace B S hS D)
    (hcl : Space.schemeTheoreticImageSubfunctor B S hS D.ι = ⊤)
    (Φ₁ Φ₂ : IsomFamily B S hS Z hZ a b)
    (h : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (z : Z.obj T), z ∈ D.obj T → Φ₁.1 T z = Φ₂.1 T z) :
    Φ₁ = Φ₂ := by
  refine IsomFamily.toSection_injective ?_
  refine Space.eq_of_eq_on_of_schemeTheoreticImageSubfunctor_eq_top B S hS hZ hZ
    (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ a b) (𝟙 _)
    (isomSpaceOverSpaceProj B S hS Z hZ a b) Φ₁.toSection Φ₂.toSection
    Φ₁.toSection_proj Φ₂.toSection_proj D hD ?_ hcl hprop.1
  exact (IsomFamily.comp_toSection_eq_iff D.ι Φ₁ Φ₂).2 fun T z => h T z.1 z.2

/-- The value of `g : Z ⟶ Y₀` at the source of a morphism `m : a ⟶ b` of the category attached to
`Z` is the restriction along `m` of its value at the target, as a section of a subfunctor `U`. -/
private theorem app_fiber_eq_map_of_hom {Z Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Y₀)
    (U : Subfunctor Y₀) {a b : (fibredCategory B S hS Z).val.obj} (m : a ⟶ b)
    (ha : g.app (op a.base) a.fiber.as ∈ U.obj (op a.base))
    (hb : g.app (op b.base) b.fiber.as ∈ U.obj (op b.base)) :
    (⟨g.app (op a.base) a.fiber.as, ha⟩ : U.toFunctor.obj (op a.base)) =
      U.toFunctor.map m.base.op ⟨g.app (op b.base) b.fiber.as, hb⟩ := by
  refine Subtype.ext ?_
  show g.app (op a.base) a.fiber.as = Y₀.map m.base.op (g.app (op b.base) b.fiber.as)
  rw [fibredCategory_fiber_eq m]
  exact NatTrans.naturality_apply g m.base.op b.fiber.as

namespace SectionFamily

/-- The restriction of `x i` to `U i ∩ U j`, followed by `f`, is the inclusion of `U i ∩ U j`
followed by `q₀`. -/
theorem left_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₀ : IsAlgebraicSpace B S hS Y₀} {q₀ : Y₀ ⟶ Y}
    {ι : Type} (F : SectionFamily hY f W hY₀ q₀ ι) (i j : ι) :
    F.left i j ≫ f =
      algebraicSpaceStackMap.{u, w} B S hS (F.isOpen_inf i j).1 hY ((F.U i ⊓ F.U j).ι ≫ q₀) := by
  simp only [left, Category.assoc, F.hx]
  rw [← algebraicSpaceStackMap_comp]
  rfl

/-- A point of `Z` whose image under `g : Z ⟶ Y₀` lies over `W` lies in some `g⁻¹(U i)`. -/
private theorem exists_mem_range_pointsMap_preimage {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₀ : IsAlgebraicSpace B S hS Y₀} {q₀ : Y₀ ⟶ Y}
    {ι : Type} (F : SectionFamily hY f W hY₀ q₀ ι) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Z ⟶ Y₀) (z : Space.points B S hS Z)
    (hz : Space.pointsMap B S hS Z g z ∈
      Set.range (Space.pointsMap B S hS (W.preimage q₀).toFunctor (W.preimage q₀).ι)) :
    ∃ i, z ∈ Set.range
      (Space.pointsMap B S hS ((F.U i).preimage g).toFunctor ((F.U i).preimage g).ι) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (F.cover hz)
  exact ⟨i, by rwa [Space.range_pointsMap_preimage_ι]⟩

/-- **The cocycle condition spreads from a scheme-theoretically dense open.** Let `c : Y₁ ⟶ Y₀`
be a morphism of algebraic spaces and `D ⊆ Y₁` a scheme-theoretically dense open subspace. If the
isomorphisms `φ i j` of a family of local sections satisfy the cocycle condition at the points
of `Y₁` in `D`, they satisfy it at every point of `Y₁` over the triple overlaps, as soon as the
projections of the isomorphism spaces are proper: the two sides are sections of the
isomorphism space over the triple overlap agreeing on the dense open, and Stacks 084N applies. -/
theorem isos_cocycle_of_isSchemeTheoreticallyDense {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₀ : IsAlgebraicSpace B S hS Y₀} {q₀ : Y₀ ⟶ Y}
    {ι : Type}
    (hproper : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
      (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳), x₁ ≫ f = x₂ ≫ f →
      Space.IsProper B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂))
    (F : SectionFamily hY f W hY₀ q₀ ι) (φ : ∀ i j, F.Isos i j)
    {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁) (c : Y₁ ⟶ Y₀)
    (D : Subfunctor Y₁) (hD : Space.IsOpenSubspace B S hS D)
    (hDd : Space.IsSchemeTheoreticallyDense B S hS D)
    (hcoc : ∀ i j k (T : (BigFppfOver B S hS)ᵒᵖ) (y : Y₁.obj T), y ∈ D.obj T →
      ∀ (hi : c.app T y ∈ (F.U i).obj T) (hj : c.app T y ∈ (F.U j).obj T)
        (hk : c.app T y ∈ (F.U k).obj T),
        (φ i j).1 T ⟨c.app T y, hi, hj⟩ ≫ (φ j k).1 T ⟨c.app T y, hj, hk⟩ =
          (φ i k).1 T ⟨c.app T y, hi, hk⟩)
    (i j k : ι) (T : (BigFppfOver B S hS)ᵒᵖ) (y : Y₁.obj T) (hi : c.app T y ∈ (F.U i).obj T)
    (hj : c.app T y ∈ (F.U j).obj T) (hk : c.app T y ∈ (F.U k).obj T) :
    (φ i j).1 T ⟨c.app T y, hi, hj⟩ ≫ (φ j k).1 T ⟨c.app T y, hj, hk⟩ =
      (φ i k).1 T ⟨c.app T y, hi, hk⟩ := by
  let Z : Subfunctor Y₁ := (F.U i ⊓ F.U j ⊓ F.U k).preimage c
  have hZ : Space.IsOpenSubspace B S hS Z :=
    Space.isOpenSubspace_preimage B S hS c _ hY₀ hY₁
      (Space.isOpenSubspace_inf B S hS hY₀ _ _ (F.isOpen_inf i j) (F.isOpen k))
  have hmem : ∀ T (z : Z.toFunctor.obj T), (c.app T z.1 ∈ (F.U i).obj T ∧
      c.app T z.1 ∈ (F.U j).obj T) ∧ c.app T z.1 ∈ (F.U k).obj T := fun _ z => z.2
  let r (V : Subfunctor Y₀) (h : ∀ T (z : Z.toFunctor.obj T), c.app T z.1 ∈ V.obj T) :=
    Subfunctor.lift (Z.ι ≫ c) fun T _ ⟨z, hz⟩ => hz ▸ h T z
  let rij := r (F.U i ⊓ F.U j) fun T z => (hmem T z).1
  let rjk := r (F.U j ⊓ F.U k) fun T z => ⟨(hmem T z).1.2, (hmem T z).2⟩
  let rik := r (F.U i ⊓ F.U k) fun T z => ⟨(hmem T z).1.1, (hmem T z).2⟩
  let a := algebraicSpaceStackMap.{u, w} B S hS hZ.1 (F.isOpen_inf i j).1 rij ≫ F.left i j
  let m := algebraicSpaceStackMap.{u, w} B S hS hZ.1 (F.isOpen_inf i j).1 rij ≫ F.right i j
  let b := algebraicSpaceStackMap.{u, w} B S hS hZ.1 (F.isOpen_inf j k).1 rjk ≫ F.right j k
  have hab : a ≫ f = b ≫ f := by
    simp only [a, b, Category.assoc, ← F.left_comp_eq_right_comp j k, left_comp,
      ← algebraicSpaceStackMap_comp]
    congr 1
  let ψ₁ : IsomFamily B S hS Z.toFunctor hZ.1 a m := (φ i j).restrict hZ.1 rij
  let ψ₂ : IsomFamily B S hS Z.toFunctor hZ.1 m b :=
    ⟨fun T z => (φ j k).1 T (rjk.app T z), fun {T₁ T₂} g z =>
      (φ j k).pointRestrict_eq g (rjk.app T₁ z) (rjk.app T₂ (Z.toFunctor.map g z))
        (ConcreteCategory.congr_hom (rjk.naturality g) z :)⟩
  let Φ₂ : IsomFamily B S hS Z.toFunctor hZ.1 a b :=
    ⟨fun T z => (φ i k).1 T (rik.app T z), fun {T₁ T₂} g z =>
      (φ i k).pointRestrict_eq g (rik.app T₁ z) (rik.app T₂ (Z.toFunctor.map g z))
        (ConcreteCategory.congr_hom (rik.naturality g) z :)⟩
  have h := IsomFamily.eq_of_eq_on_dense (hproper Z.toFunctor hZ.1 a b hab) (D.preimage Z.ι)
    (Space.isOpenSubspace_preimage B S hS Z.ι D hY₁ hZ.1 hD)
    (hDd hZ.1 Z.ι (Space.isEtale_of_isOpenImmersion B S hS hZ.2)) (ψ₁.comp ψ₂) Φ₂
    fun T z hz => hcoc i j k T z.1 hz (hmem T z).1.1 (hmem T z).1.2 (hmem T z).2
  exact congrArg (·.1 T ⟨y, ⟨hi, hj⟩, hk⟩) h

/-- **Gluing the local sections along `c : Y₁ ⟶ Y₀`**: if the pullbacks along `c` of the
isomorphisms `φ i j` satisfy the cocycle condition at every point of `Y₁`, the restrictions of the
`x i` to the `c⁻¹(U i)` glue to a section of `f` over `(c ≫ q₀)⁻¹(W)`. -/
private theorem hasSectionAlong_of_isos_cocycle {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    (hW : Space.IsOpenSubspace B S hS W) {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY₀ : IsAlgebraicSpace B S hS Y₀} {q₀ : Y₀ ⟶ Y} {ι : Type}
    (F : SectionFamily hY f W hY₀ q₀ ι) (φ : ∀ i j, F.Isos i j)
    {Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁) (c : Y₁ ⟶ Y₀)
    (hcoc : ∀ i j k (T : (BigFppfOver B S hS)ᵒᵖ) (y : Y₁.obj T) (hi : c.app T y ∈ (F.U i).obj T)
      (hj : c.app T y ∈ (F.U j).obj T) (hk : c.app T y ∈ (F.U k).obj T),
      (φ i j).1 T ⟨c.app T y, hi, hj⟩ ≫ (φ j k).1 T ⟨c.app T y, hj, hk⟩ =
        (φ i k).1 T ⟨c.app T y, hi, hk⟩) :
    HasSectionAlong hY f W hW hY₁ (c ≫ q₀) := by
  let Zg : Subfunctor Y₁ := W.preimage (c ≫ q₀)
  have hZg : Space.IsOpenSubspace B S hS Zg :=
    Space.isOpenSubspace_preimage B S hS (c ≫ q₀) W hY hY₁ hW
  let Ug : ι → Subfunctor Zg.toFunctor := fun i => (F.U i).preimage (Zg.ι ≫ c)
  have hUg : ∀ i, Space.IsOpenSubspace B S hS (Ug i) := fun i =>
    Space.isOpenSubspace_preimage B S hS (Zg.ι ≫ c) (F.U i) hY₀ hZg.1 (F.isOpen i)
  let xg : ∀ i, algebraicSpaceStack.{u, w} B S hS (Ug i).toFunctor (hUg i).1 ⟶ 𝒳 := fun i =>
    algebraicSpaceStackMap.{u, w} B S hS (hUg i).1 (F.isOpen i).1
      ((F.U i).fromPreimage (Zg.ι ≫ c)) ≫ F.x i
  have hcov := exists_covering_sieve_of_points_cover hZg.1 Ug hUg fun z =>
    F.exists_mem_range_pointsMap_preimage (Zg.ι ≫ c) z (by
      rw [Space.range_pointsMap_preimage_ι, Set.mem_preimage, ← Space.pointsMap_comp_apply,
        Category.assoc, Space.pointsMap_comp_apply]
      exact (Space.range_pointsMap_preimage_ι B S hS (c ≫ q₀) W).le ⟨z, rfl⟩)
  obtain ⟨y, hy⟩ := exists_algebraicSpaceStack_hom_of_cocycle hZg.1 Ug (fun i => (hUg i).1) xg
    (fun i j a hi hj => ((φ i j).1 (op a.base) ⟨(Zg.ι ≫ c).app (op a.base) a.fiber.as, hi, hj⟩).1)
    (fun i j a hi hj => ((φ i j).1 (op a.base) ⟨(Zg.ι ≫ c).app (op a.base) a.fiber.as, hi, hj⟩).2)
    (fun i j a b m hai haj hbi hbj => by
      have hz := app_fiber_eq_map_of_hom (Zg.ι ≫ c) (F.U i ⊓ F.U j) m ⟨hai, haj⟩ ⟨hbi, hbj⟩
      have h1 := pointRestrict_fac B S hS _ (F.isOpen_inf i j).1 (F.left i j) (F.right i j)
        m.base.op _ _ hz ((φ i j).1 (op b.base) ⟨_, hbi, hbj⟩)
      rw [(φ i j).pointRestrict_eq m.base.op _ _ hz] at h1
      exact h1.symm)
    (fun i j k a hi hj hk =>
      congrArg Subtype.val (hcoc i j k (op a.base) (Zg.ι.app _ a.fiber.as) hi hj hk))
    hcov
  refine ⟨y, algebraicSpaceStack_hom_ext_of_cover _ _ Ug (fun i => (hUg i).1) hcov fun i => ?_⟩
  have e1 : algebraicSpaceStackMap.{u, w} B S hS (hUg i).1 hZg.1 (Ug i).ι ≫ y ≫ f =
      xg i ≫ f := by
    rw [← Category.assoc]
    exact eq_of_iso_algebraicSpaceStack (Bicategory.whiskerRightIso (hy i).some f)
  rw [e1, Category.assoc, F.hx, ← algebraicSpaceStackMap_comp, ← algebraicSpaceStackMap_comp]
  congr 1

/-- **Gluing the local sections along isomorphisms satisfying the cocycle condition on a
quasi-compact open** (the end of situation (g) in the proof of Stacks 0CQ7). Let `F` be a family
of local sections `x i : U i ⟶ 𝒳` over a proper base `q₀ : Y₀ ⟶ Y` with `Y₀` quasi-separated,
let `V₀ ⊆ Y₀` be a quasi-compact open contained in every `U i` and in `q₀⁻¹(W)`, and let `φ i j`
be isomorphisms between the restrictions of `x i` and `x j` to `U i ∩ U j` satisfying the
cocycle condition at the points of `V₀`. If the projections of the isomorphism spaces of pairs
of points of `𝒳` with equal images in `Y` are proper, there is a section cover over `q₀` of `V₀`.

The proper morphism is the inclusion `c : Ȳ ⟶ Y₀` of the scheme-theoretic closure of `V₀`, in
which `V₀` is a scheme-theoretically dense open (Stacks 088G); the cocycle condition holds on
`Ȳ` by `isos_cocycle_of_isSchemeTheoreticallyDense`, so the restrictions of the `x i` to the
`c⁻¹(U i)` glue to a 1-morphism `(c ≫ q₀)⁻¹(W) ⟶ 𝒳`, whose composite with `f` is the inclusion
followed by `c ≫ q₀` because it is so on each `c⁻¹(U i)`.

The hypothesis `V₀ ⊆ q₀⁻¹(W)` follows from `V₀ ⊆ U i` as soon as there is an index
(`hasSectionCoverOver_of_isos_of_nonempty`); it is needed for an empty family, whose members
impose nothing on `V₀`, while the conclusion asks every point of `V₀` to lie over `W`. -/
theorem hasSectionCoverOver_of_isos {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    (hW : Space.IsOpenSubspace B S hS W) {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY₀ : IsAlgebraicSpace B S hS Y₀} {q₀ : Y₀ ⟶ Y} {ι : Type} [Finite ι]
    (hproper : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
      (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳), x₁ ≫ f = x₂ ≫ f →
      Space.IsProper B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂))
    (F : SectionFamily hY f W hY₀ q₀ ι)
    (hY₀qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀)
    (V₀ : Subfunctor Y₀) (hV₀ : Space.IsOpenSubspace B S hS V₀)
    (hV₀qc : Space.IsQuasiCompactSpace B S hS V₀.toFunctor) (hVU : ∀ i, V₀ ≤ F.U i)
    (hVW : V₀ ≤ W.preimage q₀)
    (φ : ∀ i j, F.Isos i j)
    (hcoc : ∀ i j k (T : (BigFppfOver B S hS)ᵒᵖ) (v : Y₀.obj T) (hv : v ∈ V₀.obj T),
      (φ i j).1 T ⟨v, hVU i T hv, hVU j T hv⟩ ≫ (φ j k).1 T ⟨v, hVU j T hv, hVU k T hv⟩ =
        (φ i k).1 T ⟨v, hVU i T hv, hVU k T hv⟩) :
    HasSectionCoverOver hY f W hW hY₀ q₀ V₀ := by
  -- the scheme-theoretic closure `Yb` of `V₀`, in which `V₀` is scheme-theoretically dense
  have hιqc : Space.IsQuasiCompact B S hS V₀.ι :=
    Space.isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal hY₀ hY₀qs hV₀qc V₀.ι
  have hιim : Space.IsImmersion B S hS V₀.ι :=
    Space.isImmersion_of_isOpenImmersion B S hS hV₀.2
  let Yb := Space.schemeTheoreticImageSubfunctor B S hS V₀.ι
  have hYb : Space.IsClosedSubspace B S hS Yb :=
    Space.isClosedSubspace_schemeTheoreticImageSubfunctor B S hS V₀.ι hY₀
  let c : Yb.toFunctor ⟶ Y₀ := Yb.ι
  let t : V₀.toFunctor ⟶ Yb.toFunctor := Space.toSchemeTheoreticImage B S hS V₀.ι
  have htc : t ≫ c = V₀.ι := Space.toSchemeTheoreticImage_ι B S hS V₀.ι
  have hDd : Space.IsSchemeTheoreticallyDense B S hS (Subfunctor.range t) :=
    Space.isSchemeTheoreticallyDense_range_toSchemeTheoreticImage_of_qc_or_reduced
      B S hS hV₀.1 hY₀ V₀.ι hιim (Or.inl hιqc)
  -- the cocycle condition on `Yb`
  have hcoc' := isos_cocycle_of_isSchemeTheoreticallyDense hproper F φ hYb.1 c
    (Subfunctor.range t) (Space.isOpenSubspace_range_toSchemeTheoreticImage_of_qc_or_reduced
      B S hS hV₀.1 hY₀ V₀.ι hιim (Or.inl hιqc)) hDd (by
      rintro i j k T _ ⟨v, rfl⟩ hi hj hk
      exact hcoc i j k T v.1 v.2)
  refine ⟨Yb.toFunctor, hYb.1, c, Space.isProper_of_isClosedImmersion B S hS hYb.1 hY₀ c hYb.2,
    hasSectionAlong_of_isos_cocycle hW F φ hYb.1 c hcoc', ?_⟩
  rintro _ ⟨v, rfl⟩
  refine ⟨Space.pointsMap B S hS _ t v, ?_, ?_⟩
  · rw [Set.mem_preimage, ← Space.pointsMap_comp_apply, ← Category.assoc, htc,
      ← Subfunctor.homOfLe_ι hVW, Category.assoc, Space.pointsMap_comp_apply,
      Space.pointsMap_comp_apply]
    exact (Space.range_pointsMap_preimage_ι B S hS q₀ W).le ⟨_, rfl⟩
  · rw [← Space.pointsMap_comp_apply, htc]

/-- **The gluing step for a nonempty family**: the inclusion `V₀ ⊆ q₀⁻¹(W)` of
`hasSectionCoverOver_of_isos` follows from `V₀ ⊆ U i ⊆ q₀⁻¹(W)` for any index `i`. -/
theorem hasSectionCoverOver_of_isos_of_nonempty {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    (hW : Space.IsOpenSubspace B S hS W) {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY₀ : IsAlgebraicSpace B S hS Y₀} {q₀ : Y₀ ⟶ Y} {ι : Type} [Finite ι] [Nonempty ι]
    (hproper : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
      (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳), x₁ ≫ f = x₂ ≫ f →
      Space.IsProper B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂))
    (F : SectionFamily hY f W hY₀ q₀ ι)
    (hY₀qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀)
    (V₀ : Subfunctor Y₀) (hV₀ : Space.IsOpenSubspace B S hS V₀)
    (hV₀qc : Space.IsQuasiCompactSpace B S hS V₀.toFunctor) (hVU : ∀ i, V₀ ≤ F.U i)
    (φ : ∀ i j, F.Isos i j)
    (hcoc : ∀ i j k (T : (BigFppfOver B S hS)ᵒᵖ) (v : Y₀.obj T) (hv : v ∈ V₀.obj T),
      (φ i j).1 T ⟨v, hVU i T hv, hVU j T hv⟩ ≫ (φ j k).1 T ⟨v, hVU j T hv, hVU k T hv⟩ =
        (φ i k).1 T ⟨v, hVU i T hv, hVU k T hv⟩) :
    HasSectionCoverOver hY f W hW hY₀ q₀ V₀ :=
  hasSectionCoverOver_of_isos hW hproper F hY₀qs V₀ hV₀ hV₀qc hVU
    (fun T _ hv => F.le (Classical.arbitrary ι) T (hVU _ T hv)) φ hcoc

end SectionFamily

end AlgebraicGeometry.Stack.AlgebraicStacks

end
