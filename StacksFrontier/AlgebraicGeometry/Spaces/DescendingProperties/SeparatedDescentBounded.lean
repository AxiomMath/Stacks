module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationBoundedBaseChanges
import all StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent

/-!
# Descending separatedness along systems with bounded base changes

The forms of the descent of absolute separatedness to a stage of an inverse system in which the
bound on the index is replaced by a bound on the base changes of the stages along affine points
(`AlgebraicGeometry.Space.HasBoundedBaseChanges`), together with the size bounds on products of
the site they use.

These declarations supplement
`StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent`
and live in their own module.

## References

* [Stacks Project, Tag 084V](https://stacks.math.columbia.edu/tag/084V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sizes of products of the site -/

/-- The underlying scheme of a product in the big fppf site of `S` is no larger than the larger
of the two factors: it is their fibre product over `S`, and Stacks 000R (1) bounds a fibre
product of schemes by its two factors. -/
theorem size_toScheme_obj_prod_le (Z W : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj (Z ⨯ W)).size ≤
      max ((BigFppfOver.toScheme B S hS).obj Z).size
        ((BigFppfOver.toScheme B S hS).obj W).size := by
  have hterm : IsTerminal (Over.mk (𝟙 (B.obj hS))) := Over.mkIdTerminal
  have hpb := (IsPullback.of_isLimit_binaryFan_of_isTerminal (prodIsProd Z W) hterm).map
    (BigFppfOver.toScheme B S hS)
  exact (Scheme.size_congr hpb.isoPullback).trans_le (Scheme.size_pullback_le _ _)

/-- Multiplying a diagram of the big fppf site of `S` bounded below the cutoff by a fixed object
on the left keeps it bounded below the cutoff. -/
theorem diagramBoundedBelow_prod_left {K : Type u} [Category.{u} K] (V : K ⥤ BigFppfOver B S hS)
    (Z : BigFppfOver B S hS)
    (hb : Scheme.DiagramBoundedBelow B.cutoff (V ⋙ BigFppfOver.toScheme B S hS)) :
    Scheme.DiagramBoundedBelow B.cutoff
      ((V ⋙ prod.functor.obj Z) ⋙ BigFppfOver.toScheme B S hS) :=
  let ⟨μ, hμ, hK, hsize⟩ := hb
  ⟨max ((BigFppfOver.toScheme B S hS).obj Z).size μ, max_lt Z.left.property hμ,
    hK.trans (le_max_right _ _),
    fun j => (size_toScheme_obj_prod_le B S hS Z (V.obj j)).trans (max_le_max le_rfl (hsize j))⟩

/-- Multiplying a diagram of the big fppf site of `S` bounded below the cutoff by a fixed object
on the right keeps it bounded below the cutoff. -/
theorem diagramBoundedBelow_prod_right {K : Type u} [Category.{u} K]
    (V : K ⥤ BigFppfOver B S hS) (Z : BigFppfOver B S hS)
    (hb : Scheme.DiagramBoundedBelow B.cutoff (V ⋙ BigFppfOver.toScheme B S hS)) :
    Scheme.DiagramBoundedBelow B.cutoff
      ((V ⋙ prod.functor.flip.obj Z) ⋙ BigFppfOver.toScheme B S hS) :=
  let ⟨μ, hμ, hK, hsize⟩ := hb
  ⟨max μ ((BigFppfOver.toScheme B S hS).obj Z).size, max_lt hμ Z.left.property,
    hK.trans (le_max_left _ _),
    fun j => (size_toScheme_obj_prod_le B S hS (V.obj j) Z).trans (max_le_max (hsize j) le_rfl)⟩

/-- The products of a system of affine charts with a fixed affine chart (on the left) are
affine. -/
private theorem isAffine_toScheme_obj_prod_functor_obj {K : Type u} [Category.{u} K]
    (hSaff : IsAffine S) (V : K ⥤ BigFppfOver B S hS) {Z : BigFppfOver B S hS}
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j))) (j : K) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((V ⋙ prod.functor.obj Z).obj j)) :=
  isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ hZ (hV j)

/-- The products of a system of affine charts with a fixed affine chart (on the right) are
affine. -/
private theorem isAffine_toScheme_obj_prod_functor_flip_obj {K : Type u} [Category.{u} K]
    (hSaff : IsAffine S) (V : K ⥤ BigFppfOver B S hS) {Z : BigFppfOver B S hS}
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j))) (j : K) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((V ⋙ prod.functor.flip.obj Z).obj j)) :=
  isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (hV j) hZ

/-! ### Descending a closed immersion into a product of charts, from a preserved limit -/

section ProductDiagramsPreserved

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (hSaff : IsAffine S)
  (V : K ⥤ BigFppfOver B S hS)
  (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))

include hSaff hVaff in
/-- **Stacks 081B** for the products of a cofiltered limit of affine charts with the charts of
the stages, whenever the underlying scheme functor preserves the limit of the products. A closed
immersion into `U ×_S U`, where `U` is the limit of the charts, whose composite with the first
projection is locally of finite type, is already a closed immersion into `U ×_S U_k` for all
sufficiently late stages `k`. -/
theorem exists_isClosedImmersion_comp_prodMap_π_of_preservesLimit {c : Cone V} (hc : IsLimit c)
    (hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    (hpres : PreservesLimit (V ⋙ prod.functor.obj c.pt) (BigFppfOver.toScheme B S hS))
    {R : Scheme.{u}} (g : R ⟶ (BigFppfOver.toScheme B S hS).obj (c.pt ⨯ c.pt))
    (hg : _root_.AlgebraicGeometry.IsClosedImmersion g) (k₀ : K)
    (hft : LocallyOfFiniteType (g ≫ (BigFppfOver.toScheme B S hS).map prod.fst)) :
    ∃ k₁ : K, ∀ (k : K) (_ : k ⟶ k₁),
      _root_.AlgebraicGeometry.IsClosedImmersion
        (g ≫ (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k))) := by
  have hconn : IsConnected K := IsCofiltered.isConnected K
  have hpres := prod_preservesConnectedLimits (J := K) c.pt
  have hprodlim : IsLimit ((prod.functor.obj c.pt).mapCone c) := isLimitOfPreserves _ hc
  have := hpres
  have he : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((prod.functor.obj c.pt).mapCone c)) := isLimitOfPreserves _ hprodlim
  have hEaff : ∀ j, IsAffine
      (((V ⋙ prod.functor.obj c.pt) ⋙ BigFppfOver.toScheme B S hS).obj j) :=
    isAffine_toScheme_obj_prod_functor_obj B S hS hSaff V hcaff hVaff
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

include hSaff hVaff in
/-- **Stacks 01ZP** for the products of the charts of the stages with the chart of one stage,
whenever the underlying scheme functor preserves the limit of the products. A
morphism to `U_k ×_S U_k` whose source is quasi-compact and quasi-separated and which is
locally of finite type becomes a closed immersion after base change to `U_j ×_S U_k` for some
`j`, as soon as it is one after base change to `U ×_S U_k`, where `U` is the limit of the
charts. -/
theorem exists_isClosedImmersion_pullback_snd_prodMap_of_preservesLimit {c : Cone V}
    (hc : IsLimit c) (k : K)
    (hpres : PreservesLimit (V ⋙ prod.functor.flip.obj (V.obj k)) (BigFppfOver.toScheme B S hS))
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
  have := hpres
  have he : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((prod.functor.flip.obj (V.obj k)).mapCone c)) := isLimitOfPreserves _ hprodlim
  set E := (V ⋙ prod.functor.flip.obj (V.obj k)) ⋙ BigFppfOver.toScheme B S hS with hE
  have hEaff : ∀ j, IsAffine (E.obj j) :=
    isAffine_toScheme_obj_prod_functor_flip_obj B S hS hSaff V (hVaff k) hVaff
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

end ProductDiagramsPreserved

/-! ### Descending a closed immersion into a product of charts, for a bounded system -/

section ProductDiagramsBounded

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (hSaff : IsAffine S)
  (V : K ⥤ BigFppfOver B S hS)
  (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hb : Scheme.DiagramBoundedBelow B.cutoff (V ⋙ BigFppfOver.toScheme B S hS))

include hSaff hVaff in
/-- **Stacks 081B** for the products of a cofiltered limit of affine charts with the charts of
the stages, for a system of charts bounded below the cutoff. A closed immersion into `U ×_S U`,
where `U` is the limit of the charts, whose composite with the first projection is locally of
finite type, is already a closed immersion into `U ×_S U_k` for all sufficiently late stages
`k`. -/
theorem exists_isClosedImmersion_comp_prodMap_π_of_bounded
    (hb : Scheme.DiagramBoundedBelow B.cutoff (V ⋙ BigFppfOver.toScheme B S hS))
    {c : Cone V} (hc : IsLimit c)
    (hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    {R : Scheme.{u}} (g : R ⟶ (BigFppfOver.toScheme B S hS).obj (c.pt ⨯ c.pt))
    (hg : _root_.AlgebraicGeometry.IsClosedImmersion g) (k₀ : K)
    (hft : LocallyOfFiniteType (g ≫ (BigFppfOver.toScheme B S hS).map prod.fst)) :
    ∃ k₁ : K, ∀ (k : K) (_ : k ⟶ k₁),
      _root_.AlgebraicGeometry.IsClosedImmersion
        (g ≫ (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k))) := by
  exact exists_isClosedImmersion_comp_prodMap_π_of_preservesLimit B S hS hSaff V hVaff hc hcaff
    (BigFppfOver.preservesLimit_toScheme_of_bounded (V ⋙ prod.functor.obj c.pt)
      (isAffine_toScheme_obj_prod_functor_obj B S hS hSaff V hcaff hVaff)
      (diagramBoundedBelow_prod_left B S hS V c.pt hb)) g hg k₀ hft

include hSaff hVaff in
/-- **Stacks 01ZP** for the products of the charts of the stages with the chart of one stage,
for a system of charts bounded below the cutoff. A
morphism to `U_k ×_S U_k` whose source is quasi-compact and quasi-separated and which is
locally of finite type becomes a closed immersion after base change to `U_j ×_S U_k` for some
`j`, as soon as it is one after base change to `U ×_S U_k`, where `U` is the limit of the
charts. -/
theorem exists_isClosedImmersion_pullback_snd_prodMap_of_bounded
    (hb : Scheme.DiagramBoundedBelow B.cutoff (V ⋙ BigFppfOver.toScheme B S hS))
    {c : Cone V} (hc : IsLimit c)
    (k : K)
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
  exact exists_isClosedImmersion_pullback_snd_prodMap_of_preservesLimit B S hS hSaff V hVaff hc k
    (BigFppfOver.preservesLimit_toScheme_of_bounded (V ⋙ prod.functor.flip.obj (V.obj k))
      (isAffine_toScheme_obj_prod_functor_flip_obj B S hS hSaff V (hVaff k) hVaff)
      (diagramBoundedBelow_prod_right B S hS V (V.obj k) hb)) m hmft hmqc hmqs hlim

end ProductDiagramsBounded

/-! ### Relocalization to a larger base scheme -/

section Relocalize

variable {S' : Scheme.{u}} (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

/-- **Bounded base changes survive relocalization to a larger base.** A point of a relocalized
stage from an affine object is the relocalization of a point over `S` with the same underlying
scheme (`OverShriek.exists_eq_relocalizeYonedaFactorIso_comp`), and the base changes along it are
the relocalizations of the base changes over `S`
(`OverShriek.isPullback_map_relocalize_of_factor`), which have the same underlying schemes. -/
theorem hasBoundedBaseChanges_relocalize {I : Type u} [Category.{u} I] {i₀ : I}
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (h : HasBoundedBaseChanges B S hS i₀ D) :
    HasBoundedBaseChanges B S' hS' i₀ (D ⋙ OverShriek.relocalizePresheafFunctor k) := by
  intro U g
  obtain ⟨ψ, hψ, σ, hg⟩ := OverShriek.exists_eq_relocalizeYonedaFactorIso_comp k g
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk ψ)) := U.property
  obtain ⟨μ, hμ, hI, hW⟩ := h ⟨Over.mk ψ, haff⟩ σ
  refine ⟨μ, hμ, hI, fun j W p q hpq => ?_⟩
  obtain ⟨W₀, p₀, q₀, hpb₀⟩ := hAffine j.hom ⟨Over.mk ψ, haff⟩ σ
  exact (BigFppfOver.size_eq_of_isPullback B S' hS' hpq
    (OverShriek.isPullback_map_relocalize_of_factor k hψ hg hpb₀)).trans_le
    (hW j _ p₀ (yoneda.map q₀) hpb₀)

end Relocalize

/-! ### Separatedness descends to a stage -/

section Descent

variable (hZ : B.Contains (⊤_ Scheme.{u}))

namespace DescentSituation

/-- **Stacks 084T over an affine base scheme, for bounded base changes.** In the situation of
Stacks 084R over an affine base scheme, with the base changes of the stages along the affine
points of the distinguished stage bounded below the cutoff, if the limit `X` of the inverse
system is separated then some stage `X_i` is separated. The affineness hypothesis is removed in
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj_of_bounded`.

An affine étale surjective chart of the distinguished stage induces, by base change, a directed
system of affine charts with limit `U`; the kernel pair of the limit chart is of finite type
over `U`, so the closed immersion it gives into `U ×_S U` already lands in `U ×_S U_i` for some
stage `i` by Stacks 081B, descends to a closed immersion `R_j ⟶ U_j ×_S U_i` for some `j ≥ i`
by Stacks 01ZP, and there loses the separated factor `U_j ×_S U_j ⟶ U_j ×_S U_i`. -/
theorem exists_isAbsolutelySeparated_system_obj_of_isAffine_of_bounded (hSaff : IsAffine S)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I)
    (hb : HasBoundedBaseChanges B S hS (op D.base) D.system)
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
  set L : AffineChartSystem.LimitBridge C :=
    AffineChartSystem.limitBridgeOfBounded C (C.diagramBoundedBelow hb) with hL
  have hKsize : Scheme.DiagramBoundedBelow B.cutoff
      (C.siteDiagram ⋙ BigFppfOver.toScheme B S hS) := C.diagramBoundedBelow hb
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
  obtain ⟨k₁, hk₁⟩ := exists_isClosedImmersion_comp_prodMap_π_of_bounded B S hS hSaff C.siteDiagram
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
  have hprodaff : ∀ a b : Over (op D.base), IsAffine ((BigFppfOver.toScheme B S hS).obj
      (C.siteDiagram.obj a ⨯ C.siteDiagram.obj b)) := fun a b =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj a)
      (C.isAffine_obj b)
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
    have := hprodaff k₁ k₁
    exact quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁)))
  -- Stacks 01ZP: the closed immersion descends to a stage
  obtain ⟨i, hi, hires⟩ := exists_isClosedImmersion_pullback_snd_prodMap_of_bounded B S hS hSaff
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
    have := hprodaff i i
    have := hprodaff i k₁
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

/-- **Stacks 084T, for bounded base changes.** In the situation of Stacks 084R, over an
arbitrary base scheme, with the base changes of the stages along the affine points of the
distinguished stage bounded below the cutoff, if the limit `X` of the inverse system is separated
then some stage `X_i` is separated.

The bound replaces the bound `#I < cf(cutoff)` on the index set of
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj`, which implies
it (`AlgebraicGeometry.Space.DescentSituation.hasBoundedBaseChanges_of_lt_cof`). The whole descent
is read over the terminal scheme, where the bound survives
(`AlgebraicGeometry.Space.hasBoundedBaseChanges_relocalize`). -/
theorem exists_isAbsolutelySeparated_system_obj_of_bounded {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hb : HasBoundedBaseChanges B S hS (op D.base) D.system)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) := by
  obtain ⟨i, hi, hres⟩ := exists_isAbsolutelySeparated_system_obj_of_isAffine_of_bounded
    B (⊤_ Scheme.{u}) hZ hZ inferInstance (D.viewOverIntegers B S hS hZ)
    (hasBoundedBaseChanges_relocalize B S hS hZ (integersMap B S hS hZ)
      (fun f => D.transition_affine f) hb)
    ((isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ D.limitCone.pt).2 hX)
  exact ⟨i, hi, (isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ
    (D.system.obj (op i))).1 hres⟩

end DescentSituation

end Descent

end AlgebraicGeometry.Space

end
