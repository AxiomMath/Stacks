module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.Translation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine

/-!
# A decent group algebraic space locally of finite type over a field is a scheme

Let `G` be a group algebraic space over a field `k`, read as a group object over the terminal
presheaf of the big fppf site of a scheme `S ≅ Spec k`. If `G` is decent and locally of finite
type over `k`, then `G` is a scheme.

## Main results

* `GroupOverField.exists_dense_affineLocus`: an algebraic space whose schematic locus is dense has
  a dense open set of points in which every finite set lies in the image of an open immersion from
  an affine object of the site.
* `GroupOverField.mem_schematicLocus_of_finite`: a point of `G` whose field is finite over `k` lies
  in the schematic locus.
* `GroupOverField.isRepresentable_of_isDecentSpace_of_isLocallyOfFiniteType`: **a decent group
  algebraic space locally of finite type over a field is a scheme.**

## Implementation notes

The argument is not the one of Stacks 0B8G, which passes to the algebraic closure of `k`, to a
purely transcendental extension and to a perfect closure; it stays at finite level.

Decency makes the schematic locus of `G` dense (Stacks 086U), and inside it there is a dense
open `D` in which finite sets of points lie in affine opens. Let `x` be a point with a field `l`
finite over `k`. Over a finite normal extension `L₀ ⊇ l` the translates `r_τ⁻¹(D_{L₀})` of the
preimage of `D` by the right translations by the `L₀`-rational points `e_τ` above `x` are dense
open, so their intersection contains a point `q` with a finite field `M`. Over a finite normal
extension `L ⊇ M` this gives an `L`-rational point `g` of `G` with `g · e_τ ∈ D` for every
`L`-rational point `e_τ` above `x`; these finitely many points lie in one affine open of `G`, and
translating its preimage in `G_L` by `g⁻¹` gives an affine open of `G_L` containing the whole
fibre of `G_L ⟶ G` above `x`. Since `G_L ⟶ G` is finite locally free and surjective, Stacks
0BA1 puts `x` in the schematic locus. Points with finite fields are dense in every closed subset
of `|G|`, which ends the proof. Neither separatedness of `G` nor any limit argument is needed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space.GroupOverField

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

attribute [local instance] pointTopology

/-- A finite intersection of preimages of an open dense set under continuous open maps is
dense. -/
theorem dense_iInter_preimage_of_isOpenMap {X Y I : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Finite I] {D : Set Y} (hDo : IsOpen D) (hDd : Dense D) {f : I → X → Y}
    (hc : ∀ i, Continuous (f i)) (ho : ∀ i, IsOpenMap (f i)) : Dense (⋂ i, f i ⁻¹' D) := by
  rw [← Set.sInter_range]
  refine (Set.finite_range _).dense_sInter ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact hDo.preimage (hc i)
  · rintro _ ⟨i, rfl⟩
    exact hDd.preimage (ho i)

/-- Precomposing with an isomorphism does not change the range of the map on points. -/
theorem range_pointsMap_iso_hom_comp {A B X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (r : A ≅ B)
    (f : B ⟶ X) :
    Set.range (pointsMap C S hS _ (r.hom ≫ f)) = Set.range (pointsMap C S hS _ f) := by
  have hr : Function.Surjective (pointsMap C S hS _ r.hom) :=
    (pointsHomeomorphOfIso C S hS r).surjective
  rw [pointsMap_comp, Set.range_comp, hr.range_eq, Set.image_univ]

/-- **The affine locus.** In an algebraic space whose schematic locus is dense there is a dense
open set of points in which every finite set of points lies in the image of an open immersion
from an affine object of the site. -/
theorem exists_dense_affineLocus {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace C S hS X)
    (hdense : DenseRange (pointsMap C S hS (schematicLocus C S hS X).toFunctor
      (schematicLocus C S hS X).ι)) :
    ∃ D : Set (points C S hS X), IsOpen D ∧ Dense D ∧
      ∀ s : Set (points C S hS X), s.Finite → s ⊆ D →
        ∃ (A : BigFppfOver C S hS) (i : yoneda.obj A ⟶ X),
          IsAffine ((BigFppfOver.toScheme C S hS).obj A) ∧ IsOpenImmersion C S hS i ∧
            s ⊆ Set.range (pointsMap C S hS _ i) := by
  classical
  obtain ⟨hVo, hVr⟩ := isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
    C S hS hX
  set V := schematicLocus C S hS X with hVdef
  let T := V.toFunctor.reprX
  let r : yoneda.obj T ≅ V.toFunctor := V.toFunctor.reprW
  obtain ⟨D', hD'o, hD'd, hD'fin⟩ :=
    Scheme.exists_dense_isOpen_forall_finite_isAffineOpen ((BigFppfOver.toScheme C S hS).obj T)
  let φ := schemePointsHomeomorph C S hS T
  let j : yoneda.obj T ⟶ X := r.hom ≫ V.ι
  let ψ := pointsMap C S hS _ j
  have hj : IsOpenImmersion C S hS j :=
    MorphismProperty.RespectsIso.precomp _ r.hom _ hVo.2
  have hψd : DenseRange ψ := by
    rw [DenseRange, range_pointsMap_iso_hom_comp C S hS r V.ι]
    exact hdense
  refine ⟨ψ '' (φ.symm '' D'),
    isOpenMap_pointsMap_of_isOpenImmersion C S hS j hj _ (φ.symm.isOpenMap _ hD'o),
    hψd.dense_image (continuous_pointsMap C S hS j)
      ((φ.symm.surjective.denseRange).dense_image φ.symm.continuous hD'd), ?_⟩
  intro s hs hsD
  have hpre : ∀ z ∈ s, ∃ d ∈ D', ψ (φ.symm d) = z := fun z hz => by
    obtain ⟨w, ⟨d, hd, rfl⟩, rfl⟩ := hsD hz
    exact ⟨d, hd, rfl⟩
  choose d hdD hdz using hpre
  let s' : Set ((BigFppfOver.toScheme C S hS).obj T) := Set.range fun z : s => d z.1 z.2
  have : Finite s := hs.to_subtype
  obtain ⟨U₀, hU₀, hsU₀⟩ := hD'fin s' (Set.finite_range _)
    (Set.range_subset_iff.2 fun z => hdD z.1 z.2)
  obtain ⟨A, u, hu, hrange, hA⟩ := BigFppfOver.exists_affineOpen_restrict C S hS T ⟨U₀, hU₀⟩
  refine ⟨A, yoneda.map u ≫ j, hA, MorphismProperty.comp_mem _ _ _
    (presheaf_yoneda_map_of_inverseImage C S hS inferInstance u hu) hj, fun z hz => ?_⟩
  obtain ⟨a, ha⟩ : d z hz ∈ Set.range ((BigFppfOver.toScheme C S hS).map u) := by
    rw [hrange]
    exact hsU₀ ⟨⟨z, hz⟩, rfl⟩
  refine ⟨(schemePointsHomeomorph C S hS A).symm a, ?_⟩
  rw [pointsMap_comp]
  show ψ (pointsMap C S hS _ (yoneda.map u) ((schemePointsHomeomorph C S hS A).symm a)) = z
  rw [schemePointsHomeomorph_symm_naturality, ha]
  exact hdz z hz

/-- The schematic locus of a decent algebraic space is dense. -/
theorem denseRange_schematicLocus_of_isDecentSpace {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace C S hS X) (hdec : IsDecentSpace C S hS X) :
    DenseRange (pointsMap C S hS (schematicLocus C S hS X).toFunctor
      (schematicLocus C S hS X).ι) := by
  obtain ⟨G, hGo, hGr, hGd⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace C S hS hX hdec
  exact hGd.mono (range_pointsMap_ι_le_schematicLocus C S hS G hGo hGr)

/-- The range of the inclusion of the image subfunctor contains the range of the morphism. -/
theorem range_pointsMap_subset_range_ι {F G : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    Set.range (pointsMap C S hS F f) ⊆
      Set.range (pointsMap C S hS _ (Subfunctor.range f).ι) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨pointsMap C S hS F (Subfunctor.toRange f) x, ?_⟩
  rw [← Function.comp_apply (f := pointsMap C S hS _ (Subfunctor.range f).ι), ← pointsMap_comp,
    Subfunctor.toRange_ι]

variable {C S hS} {k : Type u} [Field k] (e : S ≅ Spec (.of k))
variable (G : GroupAlgebraicSpace C S hS (yoneda.obj (⊤_ (BigFppfOver C S hS)))
  (isAlgebraicSpace_yoneda C S hS _))

section ExtObj

variable (L : Type u) [Field L] [Algebra k L] [Module.Finite k L] (hL : C.Contains (Spec (.of L)))

/-- The base change `X_L ⟶ X` along a finite extension `L/k` is open on points. -/
theorem isOpenMap_pointsMap_prod_snd_extObj (X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :
    IsOpenMap (pointsMap C S hS _ (prod.snd : yoneda.obj (extObj C S hS e L hL) ⨯ X ⟶ X)) :=
  isOpenMap_pointsMap_of_presheafIsOpenMap C S hS _
    (MorphismProperty.relative_monotone
      (fun _ _ f (h : _root_.AlgebraicGeometry.UniversallyOpen _) =>
        ((BigFppfOver.toScheme C S hS).map f).isOpenMap) _
    (presheaf_prod_snd (P := @_root_.AlgebraicGeometry.UniversallyOpen) inferInstance _ X (by
      have := isFiniteLocallyFree_extObj C S hS e L hL
      have := Stacks.Morphisms.IsFiniteLocallyFree.flat
        ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from (extObj C S hS e L hL)))
      have := Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation
        ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from (extObj C S hS e L hL)))
      infer_instance)))

/-- The base change `X_L ⟶ X` along a finite extension `L/k` is finite. -/
theorem isFinite_prod_snd_extObj {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace C S hS X) :
    IsFinite C S hS (prod.snd : yoneda.obj (extObj C S hS e L hL) ⨯ X ⟶ X) :=
  (isFinite_iff_representable C S hS _ (isAlgebraicSpace_prod_yoneda_obj _ hX) hX).2
    ⟨relativelyRepresentable_prod_snd _ X, presheaf_prod_snd inferInstance _ X (by
      have := isFiniteLocallyFree_extObj C S hS e L hL
      exact Stacks.Morphisms.IsFiniteLocallyFree.isFinite _)⟩

/-- The base change `X_L` of a space locally of finite type over `k` along a finite extension
`L/k` is locally of finite type over `k`. -/
theorem isLocallyOfFiniteType_prod_extObj {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace C S hS X)
    (hlft : IsLocallyOfFiniteType C S hS ((isTerminal_yoneda_obj_base C S hS).from X)) :
    IsLocallyOfFiniteType C S hS
      ((isTerminal_yoneda_obj_base C S hS).from (yoneda.obj (extObj C S hS e L hL) ⨯ X)) :=
  isLocallyOfFiniteType_prod C S hS _ hX (by
    have := isFiniteLocallyFree_extObj C S hS e L hL
    have := Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation
      ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from (extObj C S hS e L hL)))
    infer_instance) hlft

end ExtObj

/-- Over a finite extension `L₀/k`, the intersection of the preimages of a dense open
`D ⊆ |G|` by the right translations by the `L₀`-points `ρ ∘ τ` contains a point with a field
finite over `k`. -/
theorem exists_finite_point_mem_iInter {K L₀ : Type u} [Field K] [Algebra k K]
    [Module.Finite k K] [Field L₀] [Algebra k L₀] [Module.Finite k L₀]
    {hK : C.Contains (Spec (.of K))} (hL₀ : C.Contains (Spec (.of L₀)))
    (hlft : IsLocallyOfFiniteType C S hS ((isTerminal_yoneda_obj_base C S hS).from G.obj.X.left))
    {D : Set (points C S hS G.obj.X.left)} (hDo : IsOpen D) (hDd : Dense D)
    (ρ : yoneda.obj (extObj C S hS e K hK) ⟶ G.obj.X.left) (ι₀ : K →ₐ[k] L₀) :
    ∃ q : FieldValuedPoint C S hS (yoneda.obj (extObj C S hS e L₀ hL₀) ⨯ G.obj.X.left),
      q.class C S hS _ ∈ ⋂ τ : K →ₐ[k] L₀, pointsMap C S hS _
        ((rightTrans G (yoneda.map (extMap C S hS e (hK' := hL₀) τ) ≫ ρ)).hom ≫ prod.snd) ⁻¹' D ∧
      letI := pointAlgebra C S hS e q
      Module.Finite k q.carrier := by
  have hX : IsAlgebraicSpace C S hS G.obj.X.left := G.property
  let O : Set (points C S hS (yoneda.obj (extObj C S hS e L₀ hL₀) ⨯ G.obj.X.left)) :=
    ⋂ τ : K →ₐ[k] L₀, pointsMap C S hS _
      ((rightTrans G (yoneda.map (extMap C S hS e (hK' := hL₀) τ) ≫ ρ)).hom ≫ prod.snd) ⁻¹' D
  have hOo : IsOpen O :=
    isOpen_iInter_of_finite fun τ => hDo.preimage (continuous_pointsMap C S hS _)
  have hOd : Dense O := dense_iInter_preimage_of_isOpenMap hDo hDd
    (fun _ => continuous_pointsMap C S hS _) fun τ => by
      rw [pointsMap_comp]
      exact (isOpenMap_pointsMap_prod_snd_extObj e L₀ hL₀ _).comp
        (pointsHomeomorphOfIso C S hS (rightTrans G _)).isOpenMap
  have : Nonempty (points C S hS (yoneda.obj (extObj C S hS e L₀ hL₀) ⨯ G.obj.X.left)) :=
    ⟨(ptOf C S hS e _ L₀ hL₀ (prod.lift (𝟙 _)
      (yoneda.map (extMap C S hS e ι₀) ≫ ρ))).class C S hS _⟩
  exact exists_finite_point C S hS e _ (isAlgebraicSpace_prod_yoneda_obj _ hX)
    (isLocallyOfFiniteType_prod_extObj e L₀ hL₀ hX hlft) hOo.isLocallyClosed hOd.nonempty

/-- Let `a` be an `M`-point of `G_{L₀}` lying in every `r_τ⁻¹(D_{L₀})`, where `r_τ` is the right
translation by the `L₀`-point `ρ ∘ τ`. Then for every `k`-embedding `j : M → L`, the
`L`-rational point `g = a ∘ j` translates every `L`-point `ρ ∘ τ` into `D`. -/
theorem class_ptOf_mul_mem_of_mem_iInter {K L₀ M L : Type u} [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [Field L₀] [Algebra k L₀] [Normal k L₀] [Field M] [Algebra k M]
    [Field L] [Algebra k L] {hK : C.Contains (Spec (.of K))} {hL₀ : C.Contains (Spec (.of L₀))}
    {hM : C.Contains (Spec (.of M))} (hL : C.Contains (Spec (.of L))) (ι₀ : K →ₐ[k] L₀)
    (ρ : yoneda.obj (extObj C S hS e K hK) ⟶ G.obj.X.left) {D : Set (points C S hS G.obj.X.left)}
    (a : yoneda.obj (extObj C S hS e M hM) ⟶ yoneda.obj (extObj C S hS e L₀ hL₀) ⨯ G.obj.X.left)
    (ha : (ptOf C S hS e _ M hM a).class C S hS _ ∈ ⋂ τ : K →ₐ[k] L₀, pointsMap C S hS _
      ((rightTrans G (yoneda.map (extMap C S hS e (hK' := hL₀) τ) ≫ ρ)).hom ≫ prod.snd) ⁻¹' D)
    (lam : L₀ →ₐ[k] M) (hlam : a ≫ prod.fst = yoneda.map (extMap C S hS e lam))
    (j : M →ₐ[k] L) (τ : K →ₐ[k] L) :
    (ptOf C S hS e _ L hL ((yoneda.map (extMap C S hS e j) ≫ a ≫ prod.snd) *
      (yoneda.map (extMap C S hS e τ) ≫ ρ))).class C S hS _ ∈ D := by
  obtain ⟨τ₀, hτ₀⟩ := exists_comp_eq_of_normal ι₀ τ (j.comp lam)
  have hq := Set.mem_iInter.mp ha τ₀
  rw [Set.mem_preimage, pointsMap_class, ptOf_map] at hq
  have hcomp : a ≫ (rightTrans G (yoneda.map (extMap C S hS e τ₀) ≫ ρ)).hom ≫ prod.snd =
      (a ≫ prod.snd) * (yoneda.map (extMap C S hS e (hK := hL₀) lam) ≫
        yoneda.map (extMap C S hS e τ₀) ≫ ρ) := by
    rw [← Category.assoc, comp_rightTrans_hom, prod.lift_snd, ← Category.assoc a, hlam]
  rw [hcomp, ← class_ptOf_extMap C S hS e _ hM hL j] at hq
  convert hq using 4
  rw [comp_mul']
  congr 1
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    extMap_comp, extMap_comp, hτ₀]

/-- Let `D ⊆ |G|` be a set in which every finite set of points lies in an affine open, let `L/k`
be finite normal, and let `g` be an `L`-point of `G` which translates every `L`-point `ρ ∘ τ`
above the point `ρ` into `D`. Then the point `ρ` lies in the schematic locus of `G`. -/
theorem mem_schematicLocus_of_forall_mul_mem {K L : Type u} [Field K] [Algebra k K]
    [Module.Finite k K] [Algebra.IsAlgebraic k K] [Field L] [Algebra k L] [Module.Finite k L]
    [Normal k L] {D : Set (points C S hS G.obj.X.left)}
    (hDfin : ∀ s : Set (points C S hS G.obj.X.left), s.Finite → s ⊆ D →
      ∃ (A : BigFppfOver C S hS) (i : yoneda.obj A ⟶ G.obj.X.left),
        IsAffine ((BigFppfOver.toScheme C S hS).obj A) ∧ IsOpenImmersion C S hS i ∧
          s ⊆ Set.range (pointsMap C S hS _ i))
    {hK : C.Contains (Spec (.of K))} (hL : C.Contains (Spec (.of L)))
    (ρ : yoneda.obj (extObj C S hS e K hK) ⟶ G.obj.X.left) (σ : K →ₐ[k] L)
    (g : yoneda.obj (extObj C S hS e L hL) ⟶ G.obj.X.left)
    (hgD : ∀ τ : K →ₐ[k] L,
      (ptOf C S hS e _ L hL (g * (yoneda.map (extMap C S hS e τ) ≫ ρ))).class C S hS _ ∈ D) :
    (ptOf C S hS e _ K hK ρ).class C S hS _ ∈ Set.range (pointsMap C S hS
      (schematicLocus C S hS G.obj.X.left).toFunctor (schematicLocus C S hS G.obj.X.left).ι) := by
  let X := G.obj.X.left
  have hX : IsAlgebraicSpace C S hS X := G.property
  -- an affine open of `X` containing those translates
  obtain ⟨A, iA, hA, hiA, hsA⟩ := hDfin
    (Set.range fun τ : K →ₐ[k] L =>
      (ptOf C S hS e X L hL (g * (yoneda.map (extMap C S hS e τ) ≫ ρ))).class C S hS X)
    (Set.finite_range _) (Set.range_subset_iff.2 hgD)
  have : Mono iA := mono_of_presheaf_isOpenImmersion hiA
  let GA := Subfunctor.range iA
  have hGA : IsOpenSubspace C S hS GA :=
    isOpenSubspace_range_of_isAlgebraicSpace C S hS (isAlgebraicSpace_yoneda C S hS A) iA hiA
  have hGAaff : IsAffineSpace C S hS GA.toFunctor :=
    ⟨A, hA, ⟨(asIso (Subfunctor.toRange iA)).symm⟩⟩
  -- its preimage in `X_L`, translated by `g`
  let E := extObj C S hS e L hL
  have hY : IsAlgebraicSpace C S hS (yoneda.obj E ⨯ X) := isAlgebraicSpace_prod_yoneda_obj E hX
  let G₂ := GA.preimage (prod.snd : yoneda.obj E ⨯ X ⟶ X)
  have hG₂ : IsOpenSubspace C S hS G₂ := isOpenSubspace_preimage C S hS _ GA hX hY hGA
  have hG₂aff : IsAffineSpace C S hS G₂.toFunctor :=
    IsFinite.isAffineSpace_source (isFinite_of_isPullback C S hS
      (Subfunctor.isPullback_preimage _ GA).flip (isFinite_prod_snd_extObj e L hL hX)) hGAaff
  let mu := leftTrans G g
  let G₃ := G₂.preimage mu.hom
  have hG₃ : IsOpenSubspace C S hS G₃ := isOpenSubspace_preimage C S hS _ G₂ hY hY hG₂
  have hG₃aff : IsAffineSpace C S hS G₃.toFunctor := by
    have : IsIso (G₂.fromPreimage mu.hom) :=
      (Subfunctor.isPullback_preimage mu.hom G₂).isIso_fst_of_isIso
    exact hG₂aff.of_iso (asIso (G₂.fromPreimage mu.hom)).symm
  obtain ⟨U, hU, ⟨eU⟩⟩ := hG₃aff
  have hi : IsOpenImmersion C S hS (eU.inv ≫ G₃.ι) :=
    MorphismProperty.RespectsIso.precomp _ eU.inv _ hG₃.2
  -- Stacks 0BA1 for the finite locally free surjection `X_L ⟶ X`
  refine mem_range_pointsMap_schematicLocus_of_exists_isAffine C S hS
    (X := ⟨yoneda.obj E ⨯ X, hY⟩) (Y := ⟨X, hX⟩) (ObjectProperty.homMk prod.snd)
    (presheaf_prod_snd inferInstance E X (surjective_extObj C S hS e L hL))
    (presheaf_prod_snd inferInstance E X (isFiniteLocallyFree_extObj C S hS e L hL)) _ U
    (eU.inv ≫ G₃.ι) hU hi fun x hx => ?_
  obtain ⟨τ, rfl⟩ := fibre_eq_ptOf C S hS e X K hK ρ L hL
    (fun Ω _ _ α β => exists_comp_eq_of_normal σ α β) x hx
  have hrange := range_pointsMap_iso_hom_comp C S hS eU.symm G₃.ι
  rw [Iso.symm_hom] at hrange
  rw [hrange, range_pointsMap_preimage_ι, Set.mem_preimage, range_pointsMap_preimage_ι,
    Set.mem_preimage, ← Function.comp_apply (f := pointsMap C S hS _ prod.snd),
    ← pointsMap_comp, pointsMap_class, ptOf_map]
  refine range_pointsMap_subset_range_ι C S hS iA (hsA ⟨τ, ?_⟩)
  congr 2
  rw [← Category.assoc, comp_leftTrans_hom, prod.lift_snd, prod.lift_fst_assoc, Category.id_comp,
    prod.lift_snd]

/-- A field finite over `k` embeds into a finite normal extension of `k` that lies in the site. -/
private theorem exists_normal_finite_extension (hk : C.Contains (Spec (.of k))) (l : Type u)
    [Field l] [Algebra k l] [Module.Finite k l] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Normal k L) (_ : Module.Finite k L),
      C.Contains (Spec (.of L)) ∧ Nonempty (l →ₐ[k] L) := by
  have : Algebra.IsAlgebraic k l := Algebra.IsAlgebraic.of_finite k _
  let L := IntermediateField.normalClosure k l (AlgebraicClosure k)
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k _
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    contains_spec_of_isAlgebraic C k L hk,
    ⟨(normalClosure.algHomEquiv k l (AlgebraicClosure k)).symm
      (IsAlgClosed.lift (M := AlgebraicClosure k) (R := k) (S := l))⟩⟩

/-- **Points with a finite residue field lie in the schematic locus.** Let `G` be a group
algebraic space locally of finite type over `S ≅ Spec k` and let `D ⊆ |G|` be a dense open set
in which every finite set of points lies in an affine open. Then every point of `G` with a
representative whose field is finite over `k` lies in the schematic locus of `G`. -/
theorem mem_schematicLocus_of_finite
    (hlft : IsLocallyOfFiniteType C S hS ((isTerminal_yoneda_obj_base C S hS).from G.obj.X.left))
    (D : Set (points C S hS G.obj.X.left)) (hDo : IsOpen D) (hDd : Dense D)
    (hDfin : ∀ s : Set (points C S hS G.obj.X.left), s.Finite → s ⊆ D →
      ∃ (A : BigFppfOver C S hS) (i : yoneda.obj A ⟶ G.obj.X.left),
        IsAffine ((BigFppfOver.toScheme C S hS).obj A) ∧ IsOpenImmersion C S hS i ∧
          s ⊆ Set.range (pointsMap C S hS _ i))
    (p : FieldValuedPoint C S hS G.obj.X.left)
    (hfin : letI := pointAlgebra C S hS e p; Module.Finite k p.carrier) :
    p.class C S hS _ ∈ Set.range (pointsMap C S hS
      (schematicLocus C S hS G.obj.X.left).toFunctor (schematicLocus C S hS G.obj.X.left).ι) := by
  classical
  have hk : C.Contains (Spec (.of k)) := (Scheme.size_congr e).symm.trans_lt hS
  let := pointAlgebra C S hS e p
  have := hfin
  obtain ⟨ρ, hρ⟩ := exists_ptOf C S hS e p
  -- a finite normal extension `L₀` of `k` into which `l` embeds
  obtain ⟨L₀, _, _, _, _, hL₀, ⟨ι₀⟩⟩ := exists_normal_finite_extension hk p.carrier
  -- a point `q` of the dense open set `O` with a finite residue field `M`
  obtain ⟨q, hqO, hqfin⟩ := exists_finite_point_mem_iInter e G hL₀ hlft hDo hDd ρ ι₀
  let := pointAlgebra C S hS e q
  have := hqfin
  obtain ⟨a, hqa⟩ := exists_ptOf C S hS e q
  obtain ⟨lam, hlam⟩ := exists_extMap_eq C S hS e (yoneda.preimage (a ≫ prod.fst))
  have ha₁ : a ≫ prod.fst = yoneda.map (extMap C S hS e lam) := by
    rw [← hlam, Functor.map_preimage]
  -- a finite normal extension `L` of `k` containing `M`
  obtain ⟨L, _, _, _, _, hL, ⟨j⟩⟩ := exists_normal_finite_extension hk q.carrier
  rw [hρ]
  exact mem_schematicLocus_of_forall_mul_mem e G hDfin hL ρ ((j.comp lam).comp ι₀)
    (yoneda.map (extMap C S hS e j) ≫ a ≫ prod.snd)
    (class_ptOf_mul_mem_of_mem_iInter e G hL ι₀ ρ a (by rwa [hqa] at hqO) lam ha₁ j)

/-- **A decent group algebraic space locally of finite type over a field is a scheme.** Let `G`
be a group algebraic space over `S ≅ Spec k` which is decent and locally of finite type over
`k`. Then `G` is representable.

The schematic locus of `G` is open, and its complement is closed; if it were nonempty it would
contain a point whose residue field is finite over `k`, since `G` is locally of finite type.
Such a point lies in the schematic locus by
`AlgebraicGeometry.Space.GroupOverField.mem_schematicLocus_of_finite`: over a finite normal
extension `L/k` its fibre consists of `L`-rational points, a translation of the group carries all
of them into one affine open of a dense open subset of `G` in which finite sets lie in affine
opens, and Stacks 0BA1 for the finite locally free surjection `G_L ⟶ G` concludes. -/
theorem isRepresentable_of_isDecentSpace_of_isLocallyOfFiniteType (e : S ≅ Spec (.of k))
    (hdec : IsDecentSpace C S hS G.obj.X.left)
    (hlft : IsLocallyOfFiniteType C S hS ((isTerminal_yoneda_obj_base C S hS).from G.obj.X.left)) :
    G.obj.X.left.IsRepresentable := by
  have hX : IsAlgebraicSpace C S hS G.obj.X.left := G.property
  obtain ⟨D, hDo, hDd, hDfin⟩ := exists_dense_affineLocus C S hS hX
    (denseRange_schematicLocus_of_isDecentSpace C S hS hX hdec)
  obtain ⟨hLo, hLr⟩ := isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
    C S hS hX
  have hsurj : Function.Surjective (pointsMap C S hS _ (schematicLocus C S hS G.obj.X.left).ι) := by
    intro y
    by_contra hy
    obtain ⟨p, hpZ, hpfin⟩ := exists_finite_point C S hS e _ hX hlft
      (isOpen_range_pointsMap_of_isOpenImmersion C S hS _ hLo.2).isClosed_compl.isLocallyClosed
      ⟨y, hy⟩
    exact hpZ (mem_schematicLocus_of_finite e G hlft D hDo hDd hDfin p hpfin)
  have : IsIso (schematicLocus C S hS G.obj.X.left).ι :=
    isIso_of_isOpenImmersion_of_surjective_pointsMap C S hS _ hLo.2 hsurj
  have := hLr
  exact isRepresentable_of_natIso _ (asIso (schematicLocus C S hS G.obj.X.left).ι)

end AlgebraicGeometry.Space.GroupOverField
