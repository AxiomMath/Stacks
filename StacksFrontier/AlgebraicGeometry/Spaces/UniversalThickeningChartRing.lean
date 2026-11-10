module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningFormallyEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningDerivationExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalThickeningGlobalSections

/-!
# A universal first-order thickening of algebraic spaces on affine charts

Let `h' : Z' ⟶ X` be the structure morphism of a universal first-order thickening `Z ⊆ Z'` of
algebraic spaces over `S`, and let `d` be a commutative square of affine étale scheme charts over
`h'`: a chart `U` of `Z'`, a chart `V` of `X` and a morphism of schemes `U ⟶ V` over `h'`.  Then
`Γ(V) → Γ(U)` exhibits `Γ(U)` as the universal first-order thickening, over `Γ(V)`, of
`Γ(U)/I(U)`, where `I(U)` is the ideal of `Z` on `U`.

The proof follows the source.  The base change `Z ×_{Z'} U ⊆ U` is a first-order thickening of
schemes, and by the étale localization of Stacks 060D it is a universal first-order thickening
of algebraic spaces over `V`.  This makes `Z ×_{Z'} U ⟶ V` formally unramified, so it has a
universal first-order thickening of schemes inside the site, and the uniqueness of universal
first-order thickenings identifies that one with `U`.  On affine schemes the universal property
of a universal first-order thickening of schemes is the ring-level one, Stacks 04EF.

## Main results

* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_chartDiagramFunctionMap`: the
  ring-level universal property on affine squares of charts.

## References

* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D)
* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E)
* [Stacks Project, Tag 04EF](https://stacks.math.columbia.edu/tag/04EF)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {h' : Z' ⟶ X}

/-- The smaller space of a universal first-order thickening, as a closed subspace. -/
abbrev IsUniversalFirstOrderThickening.closedSub
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') : ClosedSubspaces B S hS Z'.1 :=
  ⟨Z, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1⟩

/-- **A universal first-order thickening is universal on affine charts.**  For a square `d` of
affine étale scheme charts over the structure morphism `h'` of a universal first-order
thickening `Z ⊆ Z'`, the pullback of regular functions `Γ(V) → Γ(U)` exhibits `Γ(U)` as the
universal first-order thickening of `Γ(U)/I(U)` over `Γ(V)`, where `I(U)` is the defining ideal of
`Z` on the chart `U`. -/
theorem isUniversalFirstOrderThickening_chartDiagramFunctionMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (d : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left)) :
    (chartDiagramFunctionMap B S hS h' d).IsUniversalFirstOrderThickening
      (definingIdealAt B S hS Z' (hZ.closedSub B S hS) (op d.U)) := by
  classical
  set F := BigFppfOver.toScheme B S hS
  -- The chart of the smaller space, with its scheme-level first-order thickening.
  obtain ⟨T₀, j, pr, hpb, hfirst⟩ := exists_nthOrderThickening_chart_pullback B S hS
    hZ.firstOrder d.U.1.left d.U.1.hom d.U.property
  -- The space-level universal property of the chart thickening over the chart of `X`.
  have hr : schemeSpaceMap d.g ≫ (ObjectProperty.homMk d.V.1.hom : schemeSpace d.V.1.left ⟶ X) =
      (ObjectProperty.homMk d.U.1.hom : schemeSpace d.U.1.left ⟶ Z') ≫ h' :=
    ObjectProperty.hom_ext _ d.comm.symm
  have hV' := IsUniversalFirstOrderThickening.etaleLocalization B S hS Z h' hZ
    (ObjectProperty.homMk d.V.1.hom : schemeSpace d.V.1.left ⟶ X)
    ((isEtale_iff_presheaf_of_yoneda B S hS _).2 d.V.property)
    (ObjectProperty.homMk d.U.1.hom : schemeSpace d.U.1.left ⟶ Z')
    ((isEtale_iff_presheaf_of_yoneda B S hS _).2 d.U.property)
    (schemeSpaceMap d.g) hr (Z.preimage d.U.1.hom) (Z.fromPreimage d.U.1.hom)
    (Subfunctor.isPullback_fromPreimage Z d.U.1.hom)
  have hrange : Subfunctor.range (yoneda.map j) = Z.preimage d.U.1.hom := by
    simpa only [Subfunctor.range_ι] using Subfunctor.range_eq_preimage_of_isPullback hpb.flip
  have hrange' : (Subfunctor.range (yoneda.map j) : Subfunctor (schemeSpace d.U.1.left).obj) =
      Z.preimage (ObjectProperty.homMk d.U.1.hom : schemeSpace d.U.1.left ⟶ Z').hom := hrange
  have hV'' : IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map j) : Subfunctor (schemeSpace d.U.1.left).obj)
      (schemeSpaceMap d.g) := hrange' ▸ hV'
  -- The inclusion of the chart of the smaller space is a monomorphism.
  have hci : AlgebraicGeometry.IsClosedImmersion (F.map j) := hfirst.1
  have hiso : IsIso (Subfunctor.toRange (yoneda.map j)) := by
    have hclosed : IsClosedImmersion B S hS (yoneda.map j) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@AlgebraicGeometry.IsClosedImmersion.{u}) j).2 hci
    have : Mono (yoneda.map j) := mono_of_isClosedImmersion B S hS (yoneda.map j) hclosed
    infer_instance
  have hsrc : Subfunctor.toRange (yoneda.map j) ≫ (Subfunctor.range (yoneda.map j)).ι ≫
      yoneda.map d.g = yoneda.map (j ≫ d.g) := by
    rw [← Category.assoc, Subfunctor.toRange_ι, Functor.map_comp]
  -- Formal unramifiedness of the chart morphism, from the universal property.
  have hfu : FormallyUnramified ((schemeSpaceFunctor B S hS).map (j ≫ d.g)).hom :=
    formallyUnramified_of_isUniversal (f := (schemeSpaceFunctor B S hS).map (j ≫ d.g))
      (Subfunctor.range (yoneda.map j) : Subfunctor (schemeSpace d.U.1.left).obj)
      (schemeSpaceMap d.g) hV'' (@asIso _ _ _ _ (Subfunctor.toRange (yoneda.map j)) hiso)
      hsrc
  have : AlgebraicGeometry.FormallyUnramified (F.map (j ≫ d.g)) :=
    formallyUnramified_map_of_formallyUnramified B S hS (j ≫ d.g) hfu
  -- The scheme-level universal first-order thickening, inside the site.
  obtain ⟨H, iH, pH, hcomp, hHuniv⟩ :=
    Stacks.Spaces.UniversalThickening.exists_site_universalFirstOrderThickening B S hS (j ≫ d.g)
  let s : UniversalFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map (j ≫ d.g)) :=
    { formallyUnramified := hfu
      ambient := schemeSpace d.U.1.left
      toBase := schemeSpaceMap d.g
      sub := Subfunctor.range (yoneda.map j)
      isUniversal := hV''
      sourceIso := @asIso _ _ _ _ (Subfunctor.toRange (yoneda.map j)) hiso
      sourceIso_ι_toBase := hsrc }
  let e := UniversalFirstOrderThickening.representedAmbientIso s iH pH hHuniv
  have hres := UniversalFirstOrderThickening.representedAmbientIso_restrict s iH pH hHuniv
  have hover := UniversalFirstOrderThickening.representedAmbientIso_over s iH pH hHuniv
  -- The identification as an isomorphism of objects of the site.
  obtain ⟨φ, hφ⟩ : ∃ φ : d.U.1.left ⟶ H, yoneda.map φ = e.hom.hom := ⟨_, yoneda.map_preimage _⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : H ⟶ d.U.1.left, yoneda.map ψ = e.inv.hom := ⟨_, yoneda.map_preimage _⟩
  have hj : yoneda.map j ≫ yoneda.map φ = yoneda.map iH := by
    have key := congrArg (fun m => Subfunctor.toRange (yoneda.map j) ≫ m) hres
    have l : Subfunctor.toRange (yoneda.map j) ≫ (s.sub.ι ≫ e.hom.hom) =
        yoneda.map j ≫ yoneda.map φ :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e.hom.hom)
        (Subfunctor.toRange_ι (yoneda.map j))).trans (congrArg (yoneda.map j ≫ ·) hφ.symm))
    have r : Subfunctor.toRange (yoneda.map j) ≫
        (UniversalFirstOrderThickening.subComparison s
          (UniversalFirstOrderThickening.ofSite s.formallyUnramified iH pH hHuniv) ≫
          (UniversalFirstOrderThickening.ofSite s.formallyUnramified iH pH hHuniv).sub.ι) =
        yoneda.map iH := by
      change Subfunctor.toRange (yoneda.map j) ≫ ((inv (Subfunctor.toRange (yoneda.map j)) ≫
        Subfunctor.toRange (yoneda.map iH)) ≫ (Subfunctor.range (yoneda.map iH)).ι) = _
      rw [Category.assoc, IsIso.hom_inv_id_assoc, Subfunctor.toRange_ι]
    exact l.symm.trans (key.trans r)
  have hp : yoneda.map φ ≫ yoneda.map pH = yoneda.map d.g :=
    (congrArg (· ≫ yoneda.map pH) hφ).trans (congrArg (fun f => f.hom) hover)
  have hφψ : φ ≫ ψ = 𝟙 _ := yoneda.map_injective (by
    rw [Functor.map_comp, hφ, hψ, CategoryTheory.Functor.map_id]
    exact congrArg (fun f => f.hom) e.hom_inv_id)
  have hψφ : ψ ≫ φ = 𝟙 _ := yoneda.map_injective (by
    rw [Functor.map_comp, hφ, hψ, CategoryTheory.Functor.map_id]
    exact congrArg (fun f => f.hom) e.inv_hom_id)
  have hjφ : j ≫ φ = iH := yoneda.map_injective (by rw [Functor.map_comp]; exact hj)
  have hφp : φ ≫ pH = d.g := yoneda.map_injective (by rw [Functor.map_comp]; exact hp)
  -- The chart thickening is a scheme-level universal first-order thickening.
  have hiψ : F.map iH ≫ F.map ψ = F.map j := by
    rw [← Functor.map_comp, ← hjφ, Category.assoc, hφψ, Category.comp_id]
  have hψg : F.map ψ ≫ F.map d.g = F.map pH := by
    rw [← Functor.map_comp, ← hφp, ← Category.assoc, hψφ, Category.id_comp]
  have hschemeU : Stacks.Thickenings.IsUniversalFirstOrderThickening (F.map (j ≫ d.g)) (F.map j)
      (F.map d.g) :=
    hHuniv.of_iso (F.mapIso ⟨ψ, φ, hψφ, hφψ⟩) hiψ hψg hfirst
  have : IsAffine (F.obj ((SmallEtale.toOver B S hS X.obj).obj d.V)) := hV
  have : IsAffine (F.obj ((SmallEtale.toOver B S hS Z'.obj).obj d.U)) := hU
  have : IsAffine (F.obj d.U.1.left) := hU
  have : IsAffine (F.obj T₀) := isAffine_of_isAffineHom (F.map j)
  have hring := Stacks.Thickenings.isUniversalFirstOrderThickening_appTop hschemeU
  -- The kernel of the chart thickening is the defining ideal of the smaller space.
  let rep := (hZ.closedSub B S hS).2.2.rep
  let κiso := hpb.isoIsPullback _ _ (rep.isPullback d.U.1.hom)
  have hκ : κiso.hom ≫ yoneda.map (rep.snd d.U.1.hom) = yoneda.map j :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  let κ : T₀ ≅ rep.pullback d.U.1.hom := Functor.preimageIso yoneda κiso
  have hκj : κ.hom ≫ rep.snd d.U.1.hom = j := yoneda.map_injective (by
    rw [Functor.map_comp]
    exact (congrArg (· ≫ yoneda.map (rep.snd d.U.1.hom)) (yoneda.map_preimage κiso.hom)).trans hκ)
  have hinj : Function.Injective (Scheme.Γ.map (F.map κ.hom).op).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).1 (inferInstance : IsIso
      (Scheme.Γ.map (F.map κ.hom).op))).1
  have hker : definingIdealAt B S hS Z' (hZ.closedSub B S hS) (op d.U) =
      RingHom.ker (Scheme.Hom.appTop (F.map j)).hom := by
    rw [definingIdealAt_eq_ker B S hS Z' (hZ.closedSub B S hS) d.U, ← Scheme.Γ_map_op, ← hκj,
      Functor.map_comp, op_comp, Functor.map_comp]
    exact (RingHom.ker_comp_of_injective _ hinj).symm
  rw [hker]
  exact hring

end AlgebraicGeometry.Space

end
