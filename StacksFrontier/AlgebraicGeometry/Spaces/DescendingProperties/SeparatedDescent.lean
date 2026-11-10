module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeComposite

/-!
# Separatedness descends to a stage of a directed limit of algebraic spaces

Let `X = lim X_i` be a directed inverse limit of quasi-compact and quasi-separated algebraic
spaces over a scheme `S` with affine transition morphisms. If `X` is separated, then `X_i` is
separated for some `i`. This is the situation of Stacks 084R, carried by
`AlgebraicGeometry.Space.DescentSituation`.

Relative to a quasi-separated algebraic space `Y`, the same statement holds for morphisms: if
the stages are algebraic spaces over `Y` and the limit is separated over `Y`, then every
sufficiently late stage is separated over `Y`. This is Stacks 086X.

The proof is the one of the source. Choose an affine étale surjective chart `U₀ ⟶ X₀` of one
stage and let `U_i = U₀ ×_{X₀} X_i` and `U = U₀ ×_{X₀} X` be its base changes, a directed system
of affine schemes with limit `U`. Separatedness of a stage is a closed immersion condition on the
morphism `R_i = U_i ×_{X_i} U_i ⟶ U_i ×_S U_i` carrying the two projections of the kernel pair,
and likewise for the limit. The kernel pair `R = U ×_X U` of the limit chart is of finite type
over `U`, so a closed immersion into `U ×_S U = lim_i (U ×_S U_i)` is already a closed immersion
into `U ×_S U_i` for some `i` by Stacks 081B. For that `i` the morphism `R ⟶ U ×_S U_i` is the
base change of `R_i ⟶ U_i ×_S U_i` along `U ×_S U_i ⟶ U_i ×_S U_i`, so Stacks 01ZP applies to
the system `j ↦ U_j ×_S U_i` and makes `R_j ⟶ U_j ×_S U_i` a closed immersion for some `j ≥ i`.
Cancelling the affine, hence separated, morphism `U_j ×_S U_j ⟶ U_j ×_S U_i` then makes
`R_j ⟶ U_j ×_S U_j` a closed immersion, that is, `X_j` separated.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelySeparated_iff_isSeparatedOver`: over an affine base
  scheme, an algebraic space is separated exactly when it is separated over the base.
* `DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isSiteSmall`: if the limit of
  an inverse system of algebraic spaces in a descent situation is separated, then some stage of
  the system is separated.
* `DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isAffine_of_isSiteSmall`: the
  same over an affine base scheme, the intermediate form the general one is deduced from.
* `AlgebraicGeometry.Space.AffineChartSystem.isPullback_map`: a chart of a stage is the fibre
  product of that stage with the chart of any earlier stage.
* `AlgebraicGeometry.Space.DescentSituation.baseChangeOver`: the base change of a descent
  situation of algebraic spaces over `Y` along a point of `Y` with affine underlying scheme.
* `AlgebraicGeometry.Space.isSeparated_of_isSeparated_pullbackSnd_of_etaleChart_factorization`:
  separatedness of a morphism descends along a surjective étale chart of its source which
  factors through a morphism along which the base change is separated.
* `AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_system_app_of_isSiteSmall`: **Stacks
086X**.

## Implementation notes

Separatedness of an algebraic space is the absolute notion of Stacks 03BS, taken over the
terminal scheme, while the chart criterion
`AlgebraicGeometry.Space.isSeparatedOver_iff_isClosedImmersion_kernelPairToProd` is stated over
the base scheme of the site with the product `U ×_S U` formed there; affineness of the base
identifies the two notions and makes those products affine, which is what the two descent
statements for schemes need. The argument is therefore carried out over an affine base first.

The hypothesis is then removed by reading the whole descent over the terminal scheme, which is
affine: relocalizing along `S ⟶ Spec ℤ` carries a descent situation over `S` to one over the
terminal scheme, because that functor preserves the algebraic-space, affine, quasi-compact and
quasi-separated conditions and, being a lower-shriek extension, preserves connected limits and
hence the limit cone. Relocalizing again along the identity of the terminal scheme changes
nothing, so the absolute separatedness of a stage is the same condition on both sides.

The inverse system is required to be small for the site,
`AlgebraicGeometry.Space.IsSiteSmall`, which is what keeps the limit of the affine charts
inside the site, as in Stacks 07SF: either the index type is small compared to the cofinality
of the site's size cutoff, or the transition morphisms are monomorphisms and nothing is asked
of the index.

Stacks 086X is deduced from Stacks 084T rather than proved again. Base changing the whole
situation along an affine étale chart of the distinguished stage, composed with the structure
morphism to `Y`, produces another situation of Stacks 084R whose limit is separated over an
affine scheme, hence absolutely separated; the stage Stacks 084T returns is then separated over
that chart, and separatedness of the morphism to `Y` descends from it because affineness of the
transition morphisms turns the chart of the distinguished stage into a surjective étale chart of
that stage which factors through the chart. The chart of `Y` used here is not étale over `Y`,
which is why the descent step is phrased in terms of a chart of the *source* of the morphism.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 084T](https://stacks.math.columbia.edu/tag/084T)
* [Stacks Project, Tag 081B](https://stacks.math.columbia.edu/tag/081B)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
* [Stacks Project, Tag 086X](https://stacks.math.columbia.edu/tag/086X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). It is a `local instance` with a file-unique name, not `private`:
a private instance is invisible in the public statements below. -/
local instance hasPullbacks_presheaf_separatedDescent :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_separatedDescent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Separatedness over an affine base is absolute separatedness -/

section AbsoluteOverAffine

variable (hZ : B.Contains (⊤_ Scheme.{u})) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Over an affine base scheme, an algebraic space is separated exactly when it is separated
over the base: the structure morphism to the terminal presheaf of the site is then a separated
morphism to an affine scheme. -/
theorem isAbsolutelySeparated_iff_isSeparatedOver (hSaff : IsAffine S)
    (hF : IsAlgebraicSpace B S hS F) :
    IsAbsolutelySeparated B S hS hZ F ↔ IsSeparatedOver B S hS F := by
  refine ⟨isSeparatedOver_of_isAbsolutelySeparated B S hS hZ hF, fun h => ?_⟩
  have hterm : IsTerminal (Over.mk (𝟙 (B.obj hS))) := Over.mkIdTerminal
  have hT : IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS)))) := hSaff
  have hterm' := IsTerminal.isTerminalObj (yoneda (C := BigFppfOver B S hS)) _ hterm
  exact isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ _ hT (hterm'.from F)
    ((isSeparatedOver_iff_isSeparated_of_isTerminal B S hS hterm' (hterm'.from F)).1 h)

end AbsoluteOverAffine

/-! ### Products of affine objects over an affine base -/

/-- The product in the big fppf site of `S` of two objects with affine underlying scheme has
affine underlying scheme, provided `S` is affine: that product is the fibre product over the
terminal object of the site, whose underlying scheme is `S`. -/
theorem isAffine_toScheme_obj_prod_of_isAffine_base (hSaff : IsAffine S)
    (Z W : BigFppfOver B S hS)
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (Z ⨯ W)) := by
  have hterm : IsTerminal (Over.mk (𝟙 (B.obj hS))) := Over.mkIdTerminal
  have hZ' : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((pair Z W).obj ⟨WalkingPair.left⟩)) := hZ
  have hW' : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((pair Z W).obj ⟨WalkingPair.right⟩)) := hW
  have hpb := (IsPullback.of_isLimit_binaryFan_of_isTerminal (prodIsProd Z W) hterm).map
    (BigFppfOver.toScheme B S hS)
  have hSaff' : IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS)))) := hSaff
  exact IsAffine.of_isPullback hpb

/-! ### Charts of two stages of an inverse system -/

section ChartSystem

variable {I : Type u} [Category.{u} I] (i₀ : I)
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (U₀ : BigAffineFppf B S hS)
  (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)

/-- A member of the diagram of base changes is the fibre product of its own stage with the
member at any earlier stage. -/
theorem isPullback_stageBaseChange_map {j k : Over i₀} (g : j ⟶ k) :
    IsPullback (stageBaseChangeFst B S hS i₀ D U₀ f₀ j)
      ((stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map g) (D.map g.left)
      (stageBaseChangeFst B S hS i₀ D U₀ f₀ k) := by
  refine IsPullback.of_bot ?_ (stageBaseChangeDiagram_map_comp_fst B S hS i₀ D U₀ f₀ g).symm
    (isPullback_stageBaseChange B S hS i₀ D U₀ f₀ k)
  rw [stageBaseChangeDiagram_map_comp_snd B S hS i₀ D U₀ f₀ g, ← D.map_comp, Over.w g]
  exact isPullback_stageBaseChange B S hS i₀ D U₀ f₀ j

/-- The chart of a stage is the fibre product of that stage with the chart of any earlier
stage. -/
theorem AffineChartSystem.isPullback_map (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    {j k : Over i₀} (g : j ⟶ k) :
    IsPullback (C.stageMap j) (yoneda.map (C.siteDiagram.map g)) (D.map g.left)
      (C.stageMap k) := by
  refine (isPullback_stageBaseChange_map B S hS i₀ D U₀ f₀ g).of_iso'
    (C.iso.app j) (Iso.refl _) (C.iso.app k) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [AffineChartSystem.stageMap]
  · exact (C.iso.hom.naturality g).symm
  · simp
  · simp [AffineChartSystem.stageMap]

end ChartSystem

/-! ### The kernel pair of a finer chart as a base change -/

/-- The kernel pair of a chart of a base change. If `U ⟶ X` is a chart with representable
diagonal, `X' ⟶ X` a morphism and `V = U ×_X X'` the induced chart of `X'`, then the morphism
`V ×_{X'} V ⟶ U ×_S V` carrying the kernel pair of the finer chart is the base change of the
morphism `U ×_X U ⟶ U ×_S U` carrying the kernel pair of the given one. -/
theorem exists_isPullback_kernelPairToProd_prodMap
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (w : X' ⟶ X)
    {A V : BigFppfOver B S hS} {q : yoneda.obj A ⟶ X} {q' : yoneda.obj V ⟶ X'}
    (hq : yoneda.relativelyRepresentable q) (hq' : yoneda.relativelyRepresentable q')
    (α : V ⟶ A) (hα : IsPullback q' (yoneda.map α) w q) :
    ∃ ρ : hq'.pullback q' ⟶ hq.pullback q,
      IsPullback ρ (kernelPairToProd B S hS hq' ≫ prod.map (𝟙 V) α)
        (kernelPairToProd B S hS hq) (prod.map α (𝟙 A)) := by
  have hK := hq.isPullback' q
  have hK' := hq'.isPullback' q'
  have hL : IsPullback (yoneda.map (hq'.fst' q'))
      (yoneda.map (hq'.snd q') ≫ yoneda.map α) (q' ≫ w) q := hK'.paste_vert hα
  rw [hα.w] at hL
  have hw : (yoneda.map (hq'.snd q') ≫ yoneda.map α) ≫ q
      = (yoneda.map (hq'.fst' q') ≫ yoneda.map α) ≫ q := by
    rw [hL.flip.w, Category.assoc]
  have hcore : IsPullback (hK.flip.lift _ _ hw) (yoneda.map (hq'.fst' q'))
      (yoneda.map (hq.fst' q)) (yoneda.map α) := IsPullback.of_right' hL.flip hK.flip
  have hsnd : hK.flip.lift _ _ hw ≫ yoneda.map (hq.snd q)
      = yoneda.map (hq'.snd q') ≫ yoneda.map α := hK.flip.lift_fst _ _ hw
  obtain ⟨ρ, hρ⟩ : ∃ ρ : hq'.pullback q' ⟶ hq.pullback q,
      yoneda.map ρ = hK.flip.lift _ _ hw :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have e1 : ρ ≫ hq.fst' q = hq'.fst' q' ≫ α := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, hρ, hcore.w]
  have e2 : ρ ≫ hq.snd q = hq'.snd q' ≫ α := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, hρ, hsnd]
  have hbot : IsPullback (prod.map α (𝟙 A)) (prod.fst : V ⨯ A ⟶ V)
      (prod.fst : A ⨯ A ⟶ A) α := (IsPullback.of_prod_fst_with_id α A).flip
  have hcomm : ρ ≫ kernelPairToProd B S hS hq
      = (kernelPairToProd B S hS hq' ≫ prod.map (𝟙 V) α) ≫ prod.map α (𝟙 A) := by
    refine prod.hom_ext ?_ ?_ <;>
      simp only [kernelPairToProd, Category.assoc, prod.lift_fst, prod.lift_snd,
        Category.comp_id, prod.lift_map]
    · exact e1
    · exact e2
  refine ⟨ρ, IsPullback.of_map_of_faithful yoneda (IsPullback.of_bot ?_ ?_ (hbot.map yoneda))⟩
  · have h1 : (kernelPairToProd B S hS hq' ≫ prod.map (𝟙 V) α) ≫ (prod.fst : V ⨯ A ⟶ V)
        = hq'.fst' q' := by simp [kernelPairToProd]
    have h2 : kernelPairToProd B S hS hq ≫ (prod.fst : A ⨯ A ⟶ A) = hq.fst' q := by
      simp [kernelPairToProd]
    rw [← yoneda.map_comp, ← yoneda.map_comp, h1, h2, hρ]
    exact hcore
  · rw [← yoneda.map_comp, ← yoneda.map_comp, hcomm]

/-! ### Descending a closed immersion into a product of charts -/

section ProductDiagrams

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (hSaff : IsAffine S)
  (V : K ⥤ BigFppfOver B S hS)
  (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hK : #K < B.cutoff.ord.cof)

/-- The `081B` step for the products of the charts with the limit chart, given that the scheme
functor preserves the limit of the products. -/
private theorem exists_isClosedImmersion_comp_prodMap_π_aux (hSaff : IsAffine S)
    (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    {c : Cone V} (hc : IsLimit c)
    [PreservesLimit (V ⋙ prod.functor.obj c.pt) (BigFppfOver.toScheme B S hS)]
    (hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    {R : Scheme.{u}} (g : R ⟶ (BigFppfOver.toScheme B S hS).obj (c.pt ⨯ c.pt))
    (hg : _root_.AlgebraicGeometry.IsClosedImmersion g) (k₀ : K)
    (hft : LocallyOfFiniteType (g ≫ (BigFppfOver.toScheme B S hS).map prod.fst)) :
    ∃ k₁ : K, ∀ (k : K) (_ : k ⟶ k₁),
      _root_.AlgebraicGeometry.IsClosedImmersion
        (g ≫ (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k))) := by
  have hconn : IsConnected K := IsCofiltered.isConnected K
  have hpres := prod_preservesConnectedLimits (J := K) c.pt
  have hprodlim : IsLimit ((prod.functor.obj c.pt).mapCone c) := isLimitOfPreserves _ hc
  have hpaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((V ⋙ prod.functor.obj c.pt).obj j)) := fun j =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ hcaff (hVaff j)
  have he : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((prod.functor.obj c.pt).mapCone c)) := isLimitOfPreserves _ hprodlim
  have hEaff : ∀ j, IsAffine
      (((V ⋙ prod.functor.obj c.pt) ⋙ BigFppfOver.toScheme B S hS).obj j) := hpaff
  have hπ : ∀ k : K, ((BigFppfOver.toScheme B S hS).mapCone
        ((prod.functor.obj c.pt).mapCone c)).π.app k
      = (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k)) := fun k => rfl
  have hgft : LocallyOfFiniteType (g ≫
      ((BigFppfOver.toScheme B S hS).mapCone ((prod.functor.obj c.pt).mapCone c)).π.app k₀) := by
    have hcomp2 : LocallyOfFiniteType ((g ≫ (BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 c.pt) (c.π.app k₀))) ≫
        (BigFppfOver.toScheme B S hS).map prod.fst) := by
      rw [Category.assoc, ← Functor.map_comp,
        show prod.map (𝟙 c.pt) (c.π.app k₀) ≫ (prod.fst : c.pt ⨯ V.obj k₀ ⟶ c.pt)
          = (prod.fst : c.pt ⨯ c.pt ⟶ c.pt) by simp]
      exact hft
    rw [hπ k₀]
    exact @locallyOfFiniteType_of_comp _ _ _ _
      ((BigFppfOver.toScheme B S hS).map prod.fst) hcomp2
  obtain ⟨k₁, hk₁⟩ := EventualLimit.exists_isClosedImmersion_comp_π_app_of_isAffine
    ((V ⋙ prod.functor.obj c.pt) ⋙ BigFppfOver.toScheme B S hS) _ he g hg k₀ hgft
  exact ⟨k₁, fun k hk => hk₁ k hk⟩


/-- The `01ZP` step for the products of the charts with one stage, given that the scheme functor
preserves the limit of the products. -/
private theorem exists_isClosedImmersion_pullback_snd_prodMap_aux (hSaff : IsAffine S)
    (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
    {c : Cone V} (hc : IsLimit c) (k : K)
    [PreservesLimit (V ⋙ prod.functor.flip.obj (V.obj k)) (BigFppfOver.toScheme B S hS)]
    {T : BigFppfOver B S hS} (m : T ⟶ V.obj k ⨯ V.obj k)
    (hmft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map m))
    (hmqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hmqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hlim : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map (prod.map (c.π.app k) (𝟙 (V.obj k)))))) :
    ∃ (i : K) (hi : i ⟶ k), _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map (prod.map (V.map hi) (𝟙 (V.obj k))))) := by
  have hconn : IsConnected K := IsCofiltered.isConnected K
  have hiso : prod.functor.obj (V.obj k) ≅ prod.functor.flip.obj (V.obj k) :=
    NatIso.ofComponents (fun W => prod.braiding (V.obj k) W)
      (fun {W W'} f => braid_natural (𝟙 (V.obj k)) f)
  have h1 := prod_preservesConnectedLimits (J := K) (V.obj k)
  have h2 : PreservesLimitsOfShape K (prod.functor.flip.obj (V.obj k)) :=
    @preservesLimitsOfShape_of_natIso _ _ _ _ _ _ _ _ hiso h1
  have hprodlim : IsLimit ((prod.functor.flip.obj (V.obj k)).mapCone c) :=
    isLimitOfPreserves _ hc
  have hpaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((V ⋙ prod.functor.flip.obj (V.obj k)).obj j)) := fun j =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (hVaff j) (hVaff k)
  have he : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((prod.functor.flip.obj (V.obj k)).mapCone c)) := isLimitOfPreserves _ hprodlim
  set E := (V ⋙ prod.functor.flip.obj (V.obj k)) ⋙ BigFppfOver.toScheme B S hS with hE
  have hEaff : ∀ j, IsAffine (E.obj j) := hpaff
  have hEhom : ∀ {i j : K} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map g) := by
    intro i j g
    have := hEaff i
    have := hEaff j
    exact isAffineHom_of_isAffine _
  have hk₀ : IsAffine (E.obj k) := hEaff k
  have hkc : CompactSpace (E.obj k) := Scheme.compactSpace_of_isAffine _
  have hkqs : QuasiSeparatedSpace (E.obj k) := inferInstance
  have hX₀c : CompactSpace
      ((Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k))).left := hmqc
  have hX₀qs : QuasiSeparatedSpace
      ((Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k))).left := hmqs
  have hY₀c : CompactSpace (Over.mk (𝟙 (E.obj k))).left := hkc
  have hY₀qs : QuasiSeparatedSpace (Over.mk (𝟙 (E.obj k))).left := hkqs
  have hf₀ft : LocallyOfFiniteType
      (Over.homMk ((BigFppfOver.toScheme B S hS).map m) (Category.comp_id _) :
        (Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k)) ⟶
          Over.mk (𝟙 (E.obj k))).left := hmft
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((Over.pullback (((BigFppfOver.toScheme B S hS).mapCone
        ((prod.functor.flip.obj (V.obj k)).mapCone c)).π.app k)).map
        (Over.homMk ((BigFppfOver.toScheme B S hS).map m) (Category.comp_id _) :
          (Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k)) ⟶
            Over.mk (𝟙 (E.obj k)))).left :=
    (prop_overPullback_map_left_iff_pullback_snd
      (@_root_.AlgebraicGeometry.IsClosedImmersion) _ _).mpr hlim
  obtain ⟨i, hi, hres⟩ := exists_isClosedImmersion_baseChange_of_isLimit E _ he k
    (Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k)) (Over.mk (𝟙 (E.obj k)))
    (Over.homMk ((BigFppfOver.toScheme B S hS).map m) (Category.comp_id _))
  exact ⟨i, hi, (prop_overPullback_map_left_iff_pullback_snd
    (@_root_.AlgebraicGeometry.IsClosedImmersion) _ _).mp hres⟩


include hSaff hVaff hK in
/-- **Stacks 081B** for the products of a cofiltered limit of affine charts with the charts of
the stages. A closed immersion into `U ×_S U`, where `U` is the limit of the charts, whose
composite with the first projection is locally of finite type, is already a closed immersion
into `U ×_S U_k` for all sufficiently late stages `k`. -/
theorem exists_isClosedImmersion_comp_prodMap_π {c : Cone V} (hc : IsLimit c)
    (hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    {R : Scheme.{u}} (g : R ⟶ (BigFppfOver.toScheme B S hS).obj (c.pt ⨯ c.pt))
    (hg : _root_.AlgebraicGeometry.IsClosedImmersion g) (k₀ : K)
    (hft : LocallyOfFiniteType (g ≫ (BigFppfOver.toScheme B S hS).map prod.fst)) :
    ∃ k₁ : K, ∀ (k : K) (_ : k ⟶ k₁),
      _root_.AlgebraicGeometry.IsClosedImmersion
        (g ≫ (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k))) := by
  have := BigFppfOver.preservesLimit_toScheme (V ⋙ prod.functor.obj c.pt)
    (fun j => isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ hcaff (hVaff j)) hK
  exact exists_isClosedImmersion_comp_prodMap_π_aux B S hS V hSaff hVaff hc hcaff g hg k₀ hft

include hSaff hVaff hK in
/-- **Stacks 01ZP** for the products of the charts of the stages with the chart of one stage. A
morphism to `U_k ×_S U_k` whose source is quasi-compact and quasi-separated and which is
locally of finite type becomes a closed immersion after base change to `U_j ×_S U_k` for some
`j`, as soon as it is one after base change to `U ×_S U_k`, where `U` is the limit of the
charts. -/
theorem exists_isClosedImmersion_pullback_snd_prodMap {c : Cone V} (hc : IsLimit c) (k : K)
    {T : BigFppfOver B S hS} (m : T ⟶ V.obj k ⨯ V.obj k)
    (hmft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map m))
    (hmqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hmqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hlim : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map (prod.map (c.π.app k) (𝟙 (V.obj k)))))) :
    ∃ (i : K) (hi : i ⟶ k), _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map (prod.map (V.map hi) (𝟙 (V.obj k))))) := by
  have := BigFppfOver.preservesLimit_toScheme (V ⋙ prod.functor.flip.obj (V.obj k))
    (fun j => isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (hVaff j) (hVaff k)) hK
  exact exists_isClosedImmersion_pullback_snd_prodMap_aux B S hS V hSaff hVaff hc k m hmft hmqc hmqs
    hlim

end ProductDiagrams

section ProductDiagramsSiteSmall

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (hSaff : IsAffine S)
  (V : K ⥤ BigFppfOver B S hS)
  (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hK : BigFppfOver.IsSiteSmallDiagram V)

include hSaff hVaff hK in
/-- **Stacks 081B** for the products of a cofiltered limit of affine charts with the charts of
the stages. A closed immersion into `U ×_S U`, where `U` is the limit of the charts, whose
composite with the first projection is locally of finite type, is already a closed immersion
into `U ×_S U_k` for all sufficiently late stages `k`. -/
theorem exists_isClosedImmersion_comp_prodMap_π_of_isSiteSmallDiagram {c : Cone V} (hc : IsLimit c)
    (hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    {R : Scheme.{u}} (g : R ⟶ (BigFppfOver.toScheme B S hS).obj (c.pt ⨯ c.pt))
    (hg : _root_.AlgebraicGeometry.IsClosedImmersion g) (k₀ : K)
    (hft : LocallyOfFiniteType (g ≫ (BigFppfOver.toScheme B S hS).map prod.fst)) :
    ∃ k₁ : K, ∀ (k : K) (_ : k ⟶ k₁),
      _root_.AlgebraicGeometry.IsClosedImmersion
        (g ≫ (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k))) := by
  have _ : (prod.functor.obj c.pt).PreservesMonomorphisms :=
    ⟨fun f _ => prod.map_mono (𝟙 c.pt) f⟩
  have := BigFppfOver.preservesLimit_toScheme_of_isSiteSmallDiagram (V ⋙ prod.functor.obj c.pt)
    (fun j => isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ hcaff (hVaff j))
    (hK.comp (prod.functor.obj c.pt))
  exact exists_isClosedImmersion_comp_prodMap_π_aux B S hS V hSaff hVaff hc hcaff g hg k₀ hft

include hSaff hVaff hK in
/-- **Stacks 01ZP** for the products of the charts of the stages with the chart of one stage. A
morphism to `U_k ×_S U_k` whose source is quasi-compact and quasi-separated and which is
locally of finite type becomes a closed immersion after base change to `U_j ×_S U_k` for some
`j`, as soon as it is one after base change to `U ×_S U_k`, where `U` is the limit of the
charts. -/
theorem exists_isClosedImmersion_pullback_snd_prodMap_of_isSiteSmallDiagram {c : Cone V} (hc :
    IsLimit c) (k : K)
    {T : BigFppfOver B S hS} (m : T ⟶ V.obj k ⨯ V.obj k)
    (hmft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map m))
    (hmqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hmqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hlim : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map (prod.map (c.π.app k) (𝟙 (V.obj k)))))) :
    ∃ (i : K) (hi : i ⟶ k), _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map (prod.map (V.map hi) (𝟙 (V.obj k))))) := by
  have _ : (prod.functor.flip.obj (V.obj k)).PreservesMonomorphisms :=
    ⟨fun f _ => prod.map_mono f (𝟙 (V.obj k))⟩
  have := BigFppfOver.preservesLimit_toScheme_of_isSiteSmallDiagram
    (V ⋙ prod.functor.flip.obj (V.obj k))
    (fun j => isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (hVaff j) (hVaff k))
    (hK.comp (prod.functor.flip.obj (V.obj k)))
  exact exists_isClosedImmersion_pullback_snd_prodMap_aux B S hS V hSaff hVaff hc k m hmft hmqc hmqs
    hlim

end ProductDiagramsSiteSmall

/-! ### Relocalization to a larger base scheme -/

section Relocalize

variable {S' : Scheme.{u}} (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

/-- **An affine morphism stays affine after relocalization to a larger base.** A morphism from a
representable presheaf into a relocalization is the relocalization of a morphism from a
representable presheaf with the same underlying scheme, so the affine base change produced over
`S` relocalizes to an affine base change over `S'`. -/
theorem isAffineHom_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (h : IsAffineHom B S hS p) :
    IsAffineHom B S' hS' ((OverShriek.relocalizePresheafFunctor k).map p) := by
  intro Z g
  obtain ⟨ψ, hψ, σ, hg⟩ := OverShriek.exists_eq_relocalizeYonedaFactorIso_comp k g
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk ψ)) := Z.property
  obtain ⟨W, p₀, q, hpb⟩ := h ⟨Over.mk ψ, haff⟩ σ
  refine ⟨⟨(Over.map k).obj ((BigAffineFppf.inclusion B S hS).obj W), W.property⟩,
    ((OverShriek.relocalizeYonedaIso k).app _).inv ≫
      (OverShriek.relocalizePresheafFunctor k).map p₀,
    (Over.map k).map q ≫ (OverShriek.relocalizeFactorIso k hψ).inv, ?_⟩
  exact OverShriek.isPullback_map_relocalize_of_factor k hψ hg hpb

/-- **A quasi-compact algebraic space stays quasi-compact after relocalization to a larger
base.** Relocalization carries a representable presheaf to the presheaf represented by an object
with the same underlying scheme, and preserves surjectivity and étaleness of the chart. -/
theorem isQuasiCompactSpace_relocalize {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : IsQuasiCompactSpace B S hS F) :
    IsQuasiCompactSpace B S' hS' ((OverShriek.relocalizePresheafFunctor k).obj F) := by
  obtain ⟨U, f, hUc, hfs, hfe⟩ := h
  have _hetale : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _hsurjRI : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S' hS')) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _hetaleRI : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S' hS')) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine ⟨(Over.map k).obj U, ((OverShriek.relocalizeYonedaIso k).app U).inv ≫
    (OverShriek.relocalizePresheafFunctor k).map f, hUc, ?_, ?_⟩
  · exact MorphismProperty.RespectsIso.precomp _ _ _
      (OverShriek.presheaf_map_relocalize k (fun _ hj => hj) hfs)
  · refine (isEtale_iff_presheaf_of_yoneda B S' hS' _).2 ?_
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (OverShriek.presheaf_map_relocalize k (fun _ hj => hj)
        ((isEtale_iff_presheaf_of_yoneda B S hS f).1 hfe))

end Relocalize

/-! ### The view over the terminal scheme is already absolute -/

section OverIntegers

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The structure morphism `S ⟶ Spec ℤ`, as a morphism of the underlying category of the big
fppf site. -/
noncomputable abbrev integersMap : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩

/-- The structure morphism of the terminal scheme is the identity, so composing with it does
not change the structure morphism of `S`. -/
theorem integersMap_comp :
    integersMap B S hS hZ ≫ integersMap B (⊤_ Scheme.{u}) hZ hZ = integersMap B S hS hZ := by
  ext
  exact terminal.hom_ext _ _

/-- **Viewing the view over the terminal scheme over the terminal scheme again changes
nothing.** The two relocalizations compose to the relocalization along the structure morphism of
`S` followed by the identity of the terminal scheme, which is that structure morphism. -/
noncomputable def viewOverIntegersSelfIso (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ (viewOverIntegers B S hS hZ F) ≅
      viewOverIntegers B S hS hZ F :=
  OverShriek.relocalizeCompIso (integersMap B S hS hZ) (integersMap B (⊤_ Scheme.{u}) hZ hZ) F ≪≫
    eqToIso (congrArg (fun m => (OverShriek.relocalizePresheafFunctor m).obj F)
      (integersMap_comp B S hS hZ))

/-- **Separatedness is unchanged by viewing an algebraic space over the terminal scheme**: the
two absolute diagonals are isomorphic arrows. -/
theorem isAbsolutelySeparated_viewOverIntegers_iff (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ (viewOverIntegers B S hS hZ F) ↔
      IsAbsolutelySeparated B S hS hZ F :=
  ⟨fun h => isSeparatedOver_of_isSeparated B (⊤_ Scheme.{u}) hZ h
      (isSeparated_of_isIso B (⊤_ Scheme.{u}) hZ (viewOverIntegersSelfIso B S hS hZ F).inv),
   fun h => isSeparatedOver_of_isSeparated B (⊤_ Scheme.{u}) hZ h
      (isSeparated_of_isIso B (⊤_ Scheme.{u}) hZ (viewOverIntegersSelfIso B S hS hZ F).hom)⟩

/-- **Quasi-separatedness is unchanged by viewing an algebraic space over the terminal
scheme.** -/
theorem isAbsolutelyQuasiSeparated_viewOverIntegers (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (h : IsAbsolutelyQuasiSeparated B S hS hZ F) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (viewOverIntegers B S hS hZ F) :=
  isQuasiSeparatedOver_of_iso B (⊤_ Scheme.{u}) hZ (viewOverIntegersSelfIso B S hS hZ F).symm h

end OverIntegers

/-! ### Separatedness descends to a stage -/

section Descent

variable (hZ : B.Contains (⊤_ Scheme.{u}))

namespace DescentSituation

/-- **Stacks 084T over an affine base scheme.** In the situation of Stacks 084R over an affine
base scheme, if the limit `X` of the inverse system is separated then some stage `X_i` is
separated. The affineness hypothesis is removed in
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isSiteSmall`,
the form
the source states and the one carrying the tag.

An affine étale surjective chart of the distinguished stage induces, by base change, a directed
system of affine charts with limit `U`; the kernel pair of the limit chart is of finite type
over `U`, so the closed immersion it gives into `U ×_S U` already lands in `U ×_S U_i` for some
stage `i` by Stacks 081B, descends to a closed immersion `R_j ⟶ U_j ×_S U_i` for some `j ≥ i`
by Stacks 01ZP, and there loses the separated factor `U_j ×_S U_j ⟶ U_j ×_S U_i`. -/
theorem exists_isAbsolutelySeparated_system_obj_of_isAffine_of_isSiteSmall (hSaff : IsAffine S)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hb : Space.IsSiteSmall B S hS D.system)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) := by
  have : Nonempty I := ⟨D.base⟩
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  -- separatedness of the canonical limit presheaf
  have e : D.limitCone.pt ≅ limit D.system :=
    D.isLimit.conePointUniqueUpToIso (limit.isLimit _)
  have hlimAS : IsAlgebraicSpace B S hS (limit D.system) := D.limitAlgebraicSpace.of_iso e
  have hlimSep : IsSeparatedOver B S hS (limit D.system) :=
    (isAbsolutelySeparated_iff_isSeparatedOver B S hS hZ hSaff hlimAS).mp
      (isAbsolutelySeparated_of_isSeparated B S hS hZ hX (isSeparated_of_isIso B S hS e.inv))
  -- an affine étale surjective chart of the distinguished stage
  obtain ⟨U₀, chart, hU₀, hchartS, hchartE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (D.system.obj (op D.base)) (D.algebraicSpace D.base)).mp (D.quasiCompact D.base)
  have hchartE' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) chart :=
    (isEtale_iff_presheaf_of_yoneda B S hS chart).mp hchartE
  set C := affineChartSystem B S hS (op D.base) D.system ⟨U₀, hU₀⟩ chart
    (fun {_ _} g ↦ D.transition_affine g) with hC
  set L : AffineChartSystem.LimitBridge C := AffineChartSystem.limitBridgeOfIsSiteSmall C hb with hL
  have hKsize : BigFppfOver.IsSiteSmallDiagram C.siteDiagram :=
    C.isSiteSmallDiagram_siteDiagram hb
  set j₀ : Over (op D.base) := Over.mk (𝟙 (op D.base)) with hj₀
  -- the charts of the stages and of the limit, with their properties
  have hq : ∀ j : Over (op D.base), yoneda.relativelyRepresentable (C.stageMap j) := fun j =>
    (D.algebraicSpace j.left.unop).diagonal_representable.of_diag (C.stageMap j)
  have hqE : ∀ j : Over (op D.base), (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (C.stageMap j) := fun j =>
    presheaf_of_isPullback B S hS (C.isPullback j).flip hchartE'
  have hqS : ∀ j : Over (op D.base), (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (C.stageMap j) := fun j =>
    presheaf_of_isPullback B S hS (C.isPullback j).flip hchartS
  have hqLim : yoneda.relativelyRepresentable L.toLimit :=
    hlimAS.diagonal_representable.of_diag L.toLimit
  have hqLimE : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) L.toLimit :=
    presheaf_of_isPullback B S hS (L.isPullback_stage j₀).flip (hqE j₀)
  -- the kernel pair of the limit chart is a closed immersion into `U ×_S U`
  have hkpLim : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hqLim)) :=
    isClosedImmersion_kernelPairToProd_of_isSeparatedOver B S hS hlimSep hqLim
  have hUaff : ∀ j : Over (op D.base),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)) := fun j =>
    C.isAffine_obj j
  have hmono : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ≤
      (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) := by
    intro Vv Ww g hg
    have hgE : Etale ((BigFppfOver.toScheme B S hS).map g) := hg
    exact (inferInstance : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g))
  have hfstLim : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (hqLim.fst' L.toLimit)) := by
    refine property_kernelPair_fst B S hS (@LocallyOfFiniteType.{u}) hqLim ?_
    exact MorphismProperty.relative_monotone hmono _ (presheaf_of_isPullback B S hS
      (IsPullback.of_hasPullback L.toLimit L.toLimit).flip hqLimE)
  have hftLim : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hqLim) ≫
        (BigFppfOver.toScheme B S hS).map prod.fst) := by
    rw [← Functor.map_comp,
      show kernelPairToProd B S hS hqLim ≫ prod.fst = hqLim.fst' L.toLimit from by
        simp [kernelPairToProd]]
    exact hfstLim
  -- Stacks 081B: the closed immersion already lands in a product with a stage
  obtain ⟨k₁, hk₁⟩ := exists_isClosedImmersion_comp_prodMap_π_of_isSiteSmallDiagram B S hS hSaff
      C.siteDiagram
    hUaff hKsize L.isLimit L.isAffine_pt _ hkpLim j₀ hftLim
  have hRespects : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨ρ, hρ⟩ := exists_isPullback_kernelPairToProd_prodMap B S hS
    (limit.π D.system k₁.left) (hq k₁) hqLim (L.cone.π.app k₁) (L.isPullback_stage k₁)
  have hlimci : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁)))
        ((BigFppfOver.toScheme B S hS).map
          (prod.map (L.cone.π.app k₁) (𝟙 (C.siteDiagram.obj k₁))))) := by
    refine (prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (hρ.map (BigFppfOver.toScheme B S hS)) (IsPullback.of_hasPullback _ _)).mp ?_
    rw [Functor.map_comp]
    exact hk₁ k₁ (𝟙 k₁)
  -- quasi-compactness and quasi-separatedness of the kernel pair at the stage
  have hUc : CompactSpace ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj k₁)) :=
    have := hUaff k₁; Scheme.compactSpace_of_isAffine _
  have hmqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((hq k₁).pullback (C.stageMap k₁))) :=
    compactSpace_of_isAbsolutelyQuasiSeparated B S hS hZ (D.quasiSeparated k₁.left.unop)
      ((hq k₁).isPullback' (C.stageMap k₁)) hUc hUc
  have hmft : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁))) :=
    (locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B S hS (C.stageMap k₁) (hqE k₁)).1
  have hmqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj
      ((hq k₁).pullback (C.stageMap k₁))) := by
    have hmm : Mono ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁))) :=
      (locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B S hS (C.stageMap k₁)
        (hqE k₁)).2
    have hprodaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (C.siteDiagram.obj k₁ ⨯ C.siteDiagram.obj k₁)) :=
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj k₁)
        (C.isAffine_obj k₁)
    exact quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁)))
  -- Stacks 01ZP: the closed immersion descends to a stage
  obtain ⟨i, hi, hires⟩ := exists_isClosedImmersion_pullback_snd_prodMap_of_isSiteSmallDiagram B S
      hS hSaff
    C.siteDiagram hUaff hKsize L.isLimit k₁
    (kernelPairToProd B S hS (hq k₁)) hmft hmqc hmqs hlimci
  obtain ⟨ρ', hρ'⟩ := exists_isPullback_kernelPairToProd_prodMap B S hS
    (D.system.map hi.left) (hq k₁) (hq i) (C.siteDiagram.map hi)
    (AffineChartSystem.isPullback_map B S hS (op D.base) D.system ⟨U₀, hU₀⟩ chart C hi)
  have hcomp : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i) ≫
        prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) :=
    (prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (hρ'.map (BigFppfOver.toScheme B S hS)) (IsPullback.of_hasPullback _ _)).mpr hires
  -- cancel the separated morphism `U_i ×_S U_i ⟶ U_i ×_S U_{k₁}`
  have hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map
      (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) := by
    have h1 : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (C.siteDiagram.obj i ⨯ C.siteDiagram.obj i)) :=
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj i)
        (C.isAffine_obj i)
    have h2 : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (C.siteDiagram.obj i ⨯ C.siteDiagram.obj k₁)) :=
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj i)
        (C.isAffine_obj k₁)
    have h3 : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) :=
      isAffineHom_of_isAffine _
    exact _root_.AlgebraicGeometry.IsSeparated.of_isAffineHom _
  have hkpi : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i))) := by
    rw [Functor.map_comp] at hcomp
    exact _root_.AlgebraicGeometry.IsClosedImmersion.of_comp
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i)))
      ((BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi)))
  refine ⟨i.left.unop, leOfHom i.hom.unop, ?_⟩
  refine (isAbsolutelySeparated_iff_isSeparatedOver B S hS hZ hSaff
    (D.algebraicSpace i.left.unop)).mpr ?_
  exact isSeparatedOver_of_isClosedImmersion_kernelPairToProd B S hS
    (D.algebraicSpace i.left.unop) (hqS i) (hqE i) hkpi

/-- **Stacks 084T over an affine base scheme.** In the situation of Stacks 084R over an affine
base scheme, if the limit `X` of the inverse system is separated then some stage `X_i` is
separated. The affineness hypothesis is removed in
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj`, the form
the source states and the one carrying the tag.

An affine étale surjective chart of the distinguished stage induces, by base change, a directed
system of affine charts with limit `U`; the kernel pair of the limit chart is of finite type
over `U`, so the closed immersion it gives into `U ×_S U` already lands in `U ×_S U_i` for some
stage `i` by Stacks 081B, descends to a closed immersion `R_j ⟶ U_j ×_S U_i` for some `j ≥ i`
by Stacks 01ZP, and there loses the separated factor `U_j ×_S U_j ⟶ U_j ×_S U_i`. -/
theorem exists_isAbsolutelySeparated_system_obj_of_isAffine (hSaff : IsAffine S)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) :=
  exists_isAbsolutelySeparated_system_obj_of_isAffine_of_isSiteSmall B S hS hZ hSaff D
    (Space.IsSiteSmall.of_lt_cof_op hI) hX

/-- **A descent situation over `S`, viewed over the terminal scheme.** Relocalizing along the
structure morphism `S ⟶ Spec ℤ` preserves the algebraic-space, affine, quasi-compact and
quasi-separated conditions, and preserves the limit cone because a lower-shriek extension
commutes with connected limits and the index category is cofiltered. -/
noncomputable def viewOverIntegers {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I :=
  have : Nonempty I := ⟨D.base⟩
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  { system := D.system ⋙ OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ)
    algebraicSpace := fun i => isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ)
      (integersMap B S hS hZ) _ (D.algebraicSpace i)
    transition_affine := fun f =>
      isAffineHom_relocalize B S hS hZ (integersMap B S hS hZ) (D.transition_affine f)
    quasiCompact := fun i =>
      isQuasiCompactSpace_relocalize B S hS hZ (integersMap B S hS hZ) (D.quasiCompact i)
    quasiSeparated := fun i =>
      isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ _ (D.quasiSeparated i)
    limitCone :=
      (OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ)).mapCone D.limitCone
    isLimit := isLimitOfPreserves _ D.isLimit
    limitAlgebraicSpace := isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ)
      (integersMap B S hS hZ) _ D.limitAlgebraicSpace
    base := D.base }

/-- The inverse system of the view over the terminal scheme is the relocalized system. -/
theorem viewOverIntegers_system {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) :
    (D.viewOverIntegers B S hS hZ).system =
      D.system ⋙ OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ) := rfl

/-- The limit of the view over the terminal scheme is the view of the limit. -/
theorem viewOverIntegers_limitCone_pt {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) :
    (D.viewOverIntegers B S hS hZ).limitCone.pt =
      Space.viewOverIntegers B S hS hZ D.limitCone.pt := rfl

/-- The view over the terminal scheme keeps the distinguished index. -/
theorem viewOverIntegers_base {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) :
    (D.viewOverIntegers B S hS hZ).base = D.base := rfl

/-- **Smallness for the site is unchanged by viewing a descent situation over the terminal
scheme.** The system of the view is the relocalized system, and relocalization preserves fibre
products, hence monomorphisms, so `AlgebraicGeometry.Space.IsSiteSmall.map` applies. -/
theorem isSiteSmall_viewOverIntegers_system {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hb : Space.IsSiteSmall B S hS D.system) :
    Space.IsSiteSmall B (⊤_ Scheme.{u}) hZ (D.viewOverIntegers B S hS hZ).system :=
  hb.map (OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ))

/-- **Stacks 084T.** In the situation of Stacks 084R, over an arbitrary base scheme, if the
limit `X` of the inverse system is separated then some stage `X_i` is separated.

Separatedness is the absolute notion, taken over the terminal scheme, so the whole descent may
be read there: the relocalization along `S ⟶ Spec ℤ` carries the descent situation over `S` to
one over the terminal scheme, which is affine, and the absolute separatedness of a presheaf and
of its view over the terminal scheme are the same condition. -/
@[stacks 084T]
theorem exists_isAbsolutelySeparated_system_obj_of_isSiteSmall {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hb : Space.IsSiteSmall B S hS D.system)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) := by
  obtain ⟨i, hi, hres⟩ := exists_isAbsolutelySeparated_system_obj_of_isAffine_of_isSiteSmall
    B (⊤_ Scheme.{u}) hZ hZ inferInstance (D.viewOverIntegers B S hS hZ)
    (D.isSiteSmall_viewOverIntegers_system B S hS hZ hb)
    ((isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ D.limitCone.pt).2 hX)
  exact ⟨i, hi, (isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ
    (D.system.obj (op i))).1 hres⟩

/-- **Stacks 084T.** In the situation of Stacks 084R, over an arbitrary base scheme, if the
limit `X` of the inverse system is separated then some stage `X_i` is separated.

Separatedness is the absolute notion, taken over the terminal scheme, so the whole descent may
be read there: the relocalization along `S ⟶ Spec ℤ` carries the descent situation over `S` to
one over the terminal scheme, which is affine, and the absolute separatedness of a presheaf and
of its view over the terminal scheme are the same condition. -/
@[stacks 084T]
theorem exists_isAbsolutelySeparated_system_obj {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) :=
  exists_isAbsolutelySeparated_system_obj_of_isSiteSmall B S hS hZ D
    (Space.IsSiteSmall.of_lt_cof_op hI) hX

end DescentSituation

end Descent

/-! ### Separatedness over a base algebraic space at a late stage -/

section SeparatedOverBase

variable (hZ : B.Contains (⊤_ Scheme.{u})) {T Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The base change along `u : T ⟶ Y` of a morphism of presheaves over `Y`.** A morphism
`a : X ⟶ X'` commuting with the two structure morphisms `p` and `p'` to `Y` induces a morphism
`X ×_Y T ⟶ X' ×_Y T` of the base changes. -/
noncomputable def baseChangeOverMap {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X ⟶ Y)
    (p' : X' ⟶ Y) (a : X ⟶ X') (hcomm : a ≫ p' = p) (u : T ⟶ Y) :
    pullback p u ⟶ pullback p' u :=
  pullback.lift (pullback.fst p u ≫ a) (pullback.snd p u)
    (by rw [Category.assoc, hcomm, pullback.condition])

/-- The base change of `a` along `u`, followed by the projection to `X'`, is the projection to
`X` followed by `a`. -/
@[reassoc (attr := simp)]
theorem baseChangeOverMap_fst {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X ⟶ Y)
    (p' : X' ⟶ Y) (a : X ⟶ X') (hcomm : a ≫ p' = p) (u : T ⟶ Y) :
    baseChangeOverMap B S hS p p' a hcomm u ≫ pullback.fst p' u = pullback.fst p u ≫ a :=
  pullback.lift_fst _ _ _

/-- The base change of `a` along `u` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem baseChangeOverMap_snd {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X ⟶ Y)
    (p' : X' ⟶ Y) (a : X ⟶ X') (hcomm : a ≫ p' = p) (u : T ⟶ Y) :
    baseChangeOverMap B S hS p p' a hcomm u ≫ pullback.snd p' u = pullback.snd p u :=
  pullback.lift_snd _ _ _

/-- The base change along `u` of a morphism over `Y` is itself a base change: `X ×_Y T` is the
fibre product of `X' ×_Y T` with `X` over `X'`. -/
theorem isPullback_baseChangeOverMap {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X ⟶ Y)
    (p' : X' ⟶ Y) (a : X ⟶ X') (hcomm : a ≫ p' = p) (u : T ⟶ Y) :
    IsPullback (baseChangeOverMap B S hS p p' a hcomm u) (pullback.fst p u)
      (pullback.fst p' u) a := by
  refine IsPullback.of_right ?_ (baseChangeOverMap_fst B S hS p p' a hcomm u)
    (IsPullback.of_hasPullback p' u).flip
  rw [baseChangeOverMap_snd, hcomm]
  exact (IsPullback.of_hasPullback p u).flip

variable {I : Type u} [Preorder I]

/-- **The inverse system of base changes along `u : T ⟶ Y`.** For an inverse system `Dsys` of
presheaves over `Y`, given by a natural transformation `t` to the constant system at `Y`, the
base changes `Dsys j ×_Y T` form an inverse system over the same index category. -/
noncomputable def baseChangeOverSystem (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y) :
    Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj j := pullback (t.app j) u
  map {j k} φ := baseChangeOverMap B S hS (t.app j) (t.app k) (Dsys.map φ) (by simp) u
  map_id j := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  map_comp {j k l} φ ψ := by
    refine pullback.hom_ext ?_ ?_ <;> simp

/-- A transition morphism of the base-changed system, followed by the projection to `Dsys k`, is
the projection to `Dsys j` followed by the transition morphism of `Dsys`. -/
@[reassoc (attr := simp)]
theorem baseChangeOverSystem_map_fst (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y) {j k : Iᵒᵖ} (φ : j ⟶ k) :
    (baseChangeOverSystem B S hS Dsys t u).map φ ≫ pullback.fst (t.app k) u =
      pullback.fst (t.app j) u ≫ Dsys.map φ :=
  pullback.lift_fst _ _ _

/-- The transition morphisms of the base-changed system commute with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem baseChangeOverSystem_map_snd (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y) {j k : Iᵒᵖ} (φ : j ⟶ k) :
    (baseChangeOverSystem B S hS Dsys t u).map φ ≫ pullback.snd (t.app k) u =
      pullback.snd (t.app j) u :=
  pullback.lift_snd _ _ _

/-- **Smallness for the site survives base change along a morphism of presheaves.** The index
category is unchanged, so the cofinality alternative is carried over verbatim; under the other
alternative each transition morphism of the base-changed system is a base change of a
monomorphic transition morphism, hence a monomorphism. -/
theorem isSiteSmall_baseChangeOverSystem (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y)
    (hb : Space.IsSiteSmall B S hS Dsys) :
    Space.IsSiteSmall B S hS (baseChangeOverSystem B S hS Dsys t u) := by
  rcases hb with h | hmono
  · exact Or.inl h
  refine .of_mono fun {j k} φ => ?_
  exact (isPullback_baseChangeOverMap B S hS (t.app j) (t.app k) (Dsys.map φ) (by simp)
    u).mono_fst_of_mono (hmono φ)

/-- The projections of the base-changed system to the original system, as a natural
transformation. -/
noncomputable def baseChangeOverProj (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y) :
    baseChangeOverSystem B S hS Dsys t u ⟶ Dsys where
  app j := pullback.fst (t.app j) u
  naturality {_ _} φ := baseChangeOverSystem_map_fst B S hS Dsys t u φ

/-- **The base change along `u` of a cone over a system of presheaves over `Y`.** -/
noncomputable def baseChangeOverCone (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y) (c : Cone Dsys) (g : c.pt ⟶ Y)
    (hg : ∀ j, c.π.app j ≫ t.app j = g) :
    Cone (baseChangeOverSystem B S hS Dsys t u) where
  pt := pullback g u
  π :=
    { app := fun j => baseChangeOverMap B S hS g (t.app j) (c.π.app j) (hg j) u
      naturality := fun {_ _} φ => by
        dsimp only [baseChangeOverSystem, Functor.const_obj_obj, Functor.const_obj_map]
        refine pullback.hom_ext ?_ ?_ <;> simp [c.w] }

/-- **Base change commutes with a cofiltered inverse limit.** The base change along `u` of a
limiting cone over a directed inverse system of presheaves over `Y` is again limiting, because
each of its projections is cartesian over the corresponding projection of the original cone and
the index category of a directed system is connected. -/
noncomputable def isLimit_baseChangeOverCone [IsDirected I (· ≤ ·)] [Nonempty I]
    (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y) (c : Cone Dsys) (g : c.pt ⟶ Y)
    (hg : ∀ j, c.π.app j ≫ t.app j = g) (hc : IsLimit c) :
    IsLimit (baseChangeOverCone B S hS Dsys t u c g hg) := by
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  refine isLimitOfIsPullbackOfIsConnected (baseChangeOverProj B S hS Dsys t u)
    (baseChangeOverCone B S hS Dsys t u c g hg) c
    { hom := pullback.fst g u
      w := fun j => ?_ }
    (fun j => isPullback_baseChangeOverMap B S hS g (t.app j) (c.π.app j) (hg j) u) hc
  exact (baseChangeOverMap_fst B S hS g (t.app j) (c.π.app j) (hg j) u).symm

section BaseChangeOver

variable [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
  (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
  (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (g : D.limitCone.pt ⟶ Y)
  (hg : ∀ j, D.limitCone.π.app j ≫ t.app j = g) (U : BigFppfOver B S hS)
  (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) (u : yoneda.obj U ⟶ Y)

/-- **A descent situation of algebraic spaces over `Y`, base changed along an affine
scheme-valued point of `Y`.** In the situation of Stacks 084R, if the stages are moreover
algebraic spaces over a quasi-separated algebraic space `Y` and `u : h_U ⟶ Y` is a point of `Y`
with affine underlying scheme, then the base changes `X_i ×_Y U` again form a descent situation:
the transition morphisms stay affine, each stage stays quasi-compact because `U` is quasi-compact
and `Y` is quasi-separated, each stage stays quasi-separated, and the base change of the limit
cone is again limiting because the index category is connected. -/
noncomputable def DescentSituation.baseChangeOver : DescentSituation B S hS hZ I :=
  haveI : Nonempty I := ⟨D.base⟩
  haveI hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  haveI hUc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    Scheme.compactSpace_of_isAffine _
  haveI hUas : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  haveI hUqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj U) :=
    isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ _
      (isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ U hU (𝟙 (yoneda.obj U))
        (isSeparated_of_isIso B S hS (𝟙 (yoneda.obj U))))
  { system := baseChangeOverSystem B S hS D.system t u
    algebraicSpace := fun i =>
      isAlgebraicSpace_pullback B S hS (t.app (op i)) u (D.algebraicSpace i) hUas hY
    transition_affine := fun {i j} φ =>
      isAffineHom_of_isPullback
        (isPullback_baseChangeOverMap B S hS (t.app i) (t.app j) (D.system.map φ)
          (by simp) u).flip (D.transition_affine φ)
    quasiCompact := fun i =>
      isQuasiCompactSpace_pullback B S hS hZ (t.app (op i)) u (D.algebraicSpace i) hY
        (D.quasiCompact i) (isQuasiCompactSpace_yoneda_obj B S hS hUc) hYqs
    quasiSeparated := fun i =>
      isAbsolutelyQuasiSeparated_pullback B S hS hZ (t.app (op i)) u (D.algebraicSpace i)
        hUas hY (D.quasiSeparated i) hUqs
    limitCone := baseChangeOverCone B S hS D.system t u D.limitCone g hg
    isLimit := isLimit_baseChangeOverCone B S hS D.system t u D.limitCone g hg D.isLimit
    limitAlgebraicSpace := isAlgebraicSpace_pullback B S hS g u D.limitAlgebraicSpace hUas hY
    base := D.base }

/-- Each stage of the base-changed descent situation is the fibre product of the corresponding
stage with `U` over `Y`. -/
theorem DescentSituation.baseChangeOver_system_obj (j : Iᵒᵖ) :
    (D.baseChangeOver B S hS hZ hY hYqs t g hg U hU u).system.obj j =
      pullback (t.app j) u := rfl

/-- The limit of the base-changed descent situation is the base change of the limit. -/
theorem DescentSituation.baseChangeOver_limitCone_pt :
    (D.baseChangeOver B S hS hZ hY hYqs t g hg U hU u).limitCone.pt = pullback g u := rfl

/-- The base change keeps the distinguished index. -/
theorem DescentSituation.baseChangeOver_base :
    (D.baseChangeOver B S hS hZ hY hYqs t g hg U hU u).base = D.base := rfl

end BaseChangeOver

/-- **Separatedness descends along a surjective étale chart of the source which factors
through a morphism along which the base change is separated.** Let `f : X ⟶ Y` be a morphism of
presheaves with algebraic source, let `v : h_U ⟶ X` be a surjective étale chart of the source,
and let `u : Z ⟶ Y` be a morphism through which `v ≫ f` factors, say `v ≫ f = w ≫ u`. If the
base change of `f` along `u` is separated, then so is `f`.

This is the reduction "it suffices to check that `U ×_Y X ⟶ U` is separated" of the proof of
Stacks 086X. Every scheme-valued point of `X ×_Y X` acquires, after base changing the chart `v`
along its first projection to `X`, a surjective étale refinement whose composite to `Y` factors
through `u`; over such a refinement the base change of the relative diagonal of `f` is a base
change of the relative diagonal of `X ×_Y Z ⟶ Z`, hence a closed immersion, and closed
immersions of schemes are fppf local on the target. The morphism `u` is not required to be
étale or surjective, which is what makes the statement usable with the structure morphism of a
chart of one stage of an inverse system. -/
theorem isSeparated_of_isSeparated_pullbackSnd_of_etaleChart_factorization
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    {U : BigFppfOver B S hS} {v : yoneda.obj U ⟶ X}
    (hvS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) v)
    (hvE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) v)
    {u : Z ⟶ Y} (w : yoneda.obj U ⟶ Z) (hw : v ≫ f = w ≫ u)
    (hsep : IsSeparated B S hS (pullback.snd f u)) :
    IsSeparated B S hS f := by
  have := Stacks.Descent.isLocalAtTarget_fppfPrecoverage
    (@_root_.AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})
  have hdiag : yoneda.relativelyRepresentable (pullback.diagonal f) :=
    Stacks.SeparationLocal.relativelyRepresentable_diagonal B S hS hX f
  have hrep : yoneda.relativelyRepresentable v := hvS.rep
  refine presheaf_of_etale_cover B S hS _ hdiag fun a h => ?_
  refine ⟨hrep.pullback (h ≫ pullback.fst f f), hrep.snd (h ≫ pullback.fst f f),
    hvS.property _ _ _ (hrep.isPullback (h ≫ pullback.fst f f)),
    hvE.property _ _ _ (hrep.isPullback (h ≫ pullback.fst f f)), ?_⟩
  refine Stacks.SeparationLocal.DiagonalProp.prop_snd_of_factorization B S hS hsep hdiag
    (yoneda.map (hrep.snd (h ≫ pullback.fst f f)) ≫ h)
    (hrep.fst (h ≫ pullback.fst f f) ≫ w) ?_
  conv_rhs => rw [Category.assoc, ← hw, ← Category.assoc, hrep.w (h ≫ pullback.fst f f)]
  simp

/-- **Stacks 086X.** Let `Y` be a quasi-separated algebraic space over `S` and let `X = lim X_i`
be a directed limit, over `Y` and with affine transition morphisms, of quasi-compact and
quasi-separated algebraic spaces over `S`, as in the standing situation of Stacks 084R. If
`X ⟶ Y` is separated then `X_i ⟶ Y` is separated for all `i` large enough.

Fix the distinguished stage `0` of the system and choose an affine étale surjective chart
`U ⟶ X_0`, which exists because `X_0` is quasi-compact, and let `u : U ⟶ Y` be its composite
with the structure morphism. Base changing the whole situation along `u` is again a situation of
Stacks 084R — the stages stay quasi-compact because `U` is quasi-compact and `Y` is
quasi-separated — whose limit `X ×_Y U` is separated over the affine scheme `U`, hence a
separated algebraic space. So some stage `X_i ×_Y U` is separated by Stacks 084T, that is,
`X_i ×_Y U ⟶ U` is separated. Affineness of the transition morphism `X_i ⟶ X_0` turns the chart
`U ⟶ X_0` into a chart `U_i = U ×_{X_0} X_i ⟶ X_i` of that stage, again surjective and étale and
with `U_i ⟶ X_i ⟶ Y` factoring through `u`; separatedness of `X_i ⟶ Y` therefore descends from
that of `X_i ×_Y U ⟶ U`. Finally the transition morphisms are affine, hence separated, so
`X_k ⟶ Y` is separated for every `k ≥ i`. -/
@[stacks 086X]
theorem DescentSituation.exists_isSeparated_system_app_of_isSiteSmall [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hb : Space.IsSiteSmall B S hS D.system)
    (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (hsep : IsSeparated B S hS f) :
    ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsSeparated B S hS (t.app (op k)) := by
  have : Nonempty I := ⟨D.base⟩
  -- an affine étale surjective chart of the distinguished stage, and its image point of `Y`
  obtain ⟨U₀, q₀, hU₀, hq₀S, hq₀E⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (D.system.obj (op D.base)) (D.algebraicSpace D.base)).mp (D.quasiCompact D.base)
  have hq₀E' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q₀ :=
    (isEtale_iff_presheaf_of_yoneda B S hS q₀).mp hq₀E
  -- the base changed descent situation and the separatedness of its limit
  have hlim : IsAbsolutelySeparated B S hS hZ
      (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base))).limitCone.pt :=
    isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ U₀ hU₀
      (pullback.snd f (q₀ ≫ t.app (op D.base)))
      (isSeparated_pullbackSnd B S hS (q₀ ≫ t.app (op D.base)) hsep)
  obtain ⟨i, hbi₀, hi⟩ := exists_isAbsolutelySeparated_system_obj_of_isSiteSmall B S hS hZ
    (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base)))
    (isSiteSmall_baseChangeOverSystem B S hS D.system t (q₀ ≫ t.app (op D.base)) hb) hlim
  have hbi : D.base ≤ i := hbi₀
  -- the base change of the stage along the chart of `Y` is separated
  have hsepi : IsSeparated B S hS (pullback.snd (t.app (op i)) (q₀ ≫ t.app (op D.base))) :=
    (isSeparated_pullbackSnd_iff_isAbsolutelySeparated B S hS hZ (D.algebraicSpace i)
      (t.app (op i)) U₀ hU₀ (q₀ ≫ t.app (op D.base))).mpr hi
  -- the chart of the distinguished stage, base changed to the stage `i` along the affine
  -- transition morphism
  have hτ : D.system.map (homOfLE hbi).op ≫ t.app (op D.base) = t.app (op i) := by simp
  obtain ⟨W, v, wq, hpb⟩ :=
    D.transition_affine (homOfLE hbi).op ⟨U₀, hU₀⟩ q₀
  -- descend separatedness to the stage itself
  have hstage : IsSeparated B S hS (t.app (op i)) := by
    refine isSeparated_of_isSeparated_pullbackSnd_of_etaleChart_factorization B S hS
      (D.algebraicSpace i) (t.app (op i))
      (presheaf_of_isPullback B S hS hpb.flip hq₀S)
      (presheaf_of_isPullback B S hS hpb.flip hq₀E') (yoneda.map wq) ?_ hsepi
    rw [← hτ]
    simp only [← Category.assoc, hpb.w]
  -- and propagate it to all later stages along the affine transition morphisms
  refine ⟨i, hbi, fun k hik => ?_⟩
  have hk : D.system.map (homOfLE hik).op ≫ t.app (op i) = t.app (op k) := by simp
  rw [← hk]
  exact isSeparated_comp B S hS _ _
    (isSeparated_of_isAffineHom B S hS (D.system.map (homOfLE hik).op)
      (D.algebraicSpace k) (D.algebraicSpace i) (D.transition_affine _)) hstage

/-- **Stacks 086X.** Let `Y` be a quasi-separated algebraic space over `S` and let `X = lim X_i`
be a directed limit, over `Y` and with affine transition morphisms, of quasi-compact and
quasi-separated algebraic spaces over `S`, as in the standing situation of Stacks 084R. If
`X ⟶ Y` is separated then `X_i ⟶ Y` is separated for all `i` large enough.

Fix the distinguished stage `0` of the system and choose an affine étale surjective chart
`U ⟶ X_0`, which exists because `X_0` is quasi-compact, and let `u : U ⟶ Y` be its composite
with the structure morphism. Base changing the whole situation along `u` is again a situation of
Stacks 084R — the stages stay quasi-compact because `U` is quasi-compact and `Y` is
quasi-separated — whose limit `X ×_Y U` is separated over the affine scheme `U`, hence a
separated algebraic space. So some stage `X_i ×_Y U` is separated by Stacks 084T, that is,
`X_i ×_Y U ⟶ U` is separated. Affineness of the transition morphism `X_i ⟶ X_0` turns the chart
`U ⟶ X_0` into a chart `U_i = U ×_{X_0} X_i ⟶ X_i` of that stage, again surjective and étale and
with `U_i ⟶ X_i ⟶ Y` factoring through `u`; separatedness of `X_i ⟶ Y` therefore descends from
that of `X_i ×_Y U ⟶ U`. Finally the transition morphisms are affine, hence separated, so
`X_k ⟶ Y` is separated for every `k ≥ i`. -/
@[stacks 086X]
theorem DescentSituation.exists_isSeparated_system_app [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (hsep : IsSeparated B S hS f) :
    ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsSeparated B S hS (t.app (op k)) :=
  DescentSituation.exists_isSeparated_system_app_of_isSiteSmall B S hS hZ D
    (Space.IsSiteSmall.of_lt_cof_op hI) hY hYqs t f hf hsep

end SeparatedOverBase

end AlgebraicGeometry.Space

end
