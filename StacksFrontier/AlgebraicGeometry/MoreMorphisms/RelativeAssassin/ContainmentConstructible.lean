module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricComponentCountConstructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FiberBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FibrewiseContainment
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.GenericFibrePoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KR
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.Topology.Constructible.Homeomorph
public import StacksFrontier.Algebra.Category.Ring.FiniteSubalgebras

/-!
# Local constructibility of the fibrewise containment locus

Let `f : X ⟶ Y` be a morphism of schemes, let `F` be an `𝒪_X`-module and let `U ⊆ X` be an open
subscheme. The locus

`E = {y ∈ Y | Ass_{X_y}(F_y) ⊆ U_y}`

on the base is locally constructible as soon as `f` and `F` are of finite presentation and `U`
is quasi-compact over `Y`.

## Main results

* `Stacks.RelativeAssassin.fibrewiseContainment` is the locus `E`.
* `Stacks.RelativeAssassin.exists_open_inter_dichotomy`: on an irreducible closed subset of the
  base, `E` either contains a nonempty open part of it or is disjoint from one.
* `Stacks.RelativeAssassin.isConstructible_fibrewiseContainment`: `E` is constructible when the
  base is a Noetherian space; here only finite type of `f` and of `F` is used.
* `Stacks.RelativeAssassin.isLocallyConstructible_fibrewiseContainment` is Stacks 05KR.

## The argument

The base may be assumed affine, say `Spec A`, and `A` is the filtered colimit of the
subalgebras generated over `ℤ` by its finite subsets, each of which is Noetherian. The morphism
descends to a finite stage (Stacks 01ZM), and then so do the module (Stacks 01ZR) and the
quasi-compact open subscheme (Stacks 01Z4); the locus of the descended data pulls back to `E`
along the limit projection, because the locus is compatible with arbitrary base change
(Stacks 05KQ). Over the Noetherian stage the criterion of Stacks 053Z applies: on an
irreducible closed subset of the base, replaced by its reduced closed subscheme structure, the
containment at the generic point spreads to a nonempty open by Stacks 05KP and its failure
spreads by Stacks 05KN.

## Implementation notes

The reduced closed subscheme structure on an irreducible closed subset `Z` of the base is
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`, and the comparison between its points
and those of `Z` is the homeomorphism onto the range of its closed immersion, so that the
underlying point of the base is read off by definitional unfolding.

Transporting the data along the isomorphism between the source and the base change of the model
is `Stacks.RelativeAssassin.fibrewiseContainment_comp_iso`, which compares the two fibres
through the morphism of pullbacks induced by the isomorphism; that morphism is again an
isomorphism, and the module side is handled by the behaviour of associated points under a
pullback along an isomorphism rather than by a computation with stalks.

## References

* [Stacks Project, Tag 053Z](https://stacks.math.columbia.edu/tag/053Z)
* [Stacks Project, Tag 05KN](https://stacks.math.columbia.edu/tag/05KN)
* [Stacks Project, Tag 05KP](https://stacks.math.columbia.edu/tag/05KP)
* [Stacks Project, Tag 05KQ](https://stacks.math.columbia.edu/tag/05KQ)
* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace Stacks.RelativeAssassin

variable {X Y : Scheme.{u}}

/-- The set of points `y` of the base over which every associated point of the fibre `F_y` of an
`𝒪_X`-module `F` lies in the fibre `U_y` of an open subscheme `U ⊆ X`. -/
def fibrewiseContainment (f : X ⟶ Y) (F : X.Modules) (U : X.Opens) : Set Y :=
  {y : Y | Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
    f.fiberι y ⁻¹' (U : Set X)}

/-- Membership in `Stacks.RelativeAssassin.fibrewiseContainment` is the containment of the
associated points of the fibre of `F` in the fibre of `U`. -/
theorem mem_fibrewiseContainment (f : X ⟶ Y) (F : X.Modules) (U : X.Opens) (y : Y) :
    y ∈ fibrewiseContainment f F U ↔
      Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
        f.fiberι y ⁻¹' (U : Set X) :=
  Iff.rfl

/-- **Stacks Project, Tag 05KQ, as an equality of loci.** The fibrewise containment locus of the
base change of `(f, F, U)` along an arbitrary `g : Y' ⟶ Y` is the inverse image under `g` of the
fibrewise containment locus of `(f, F, U)`. -/
theorem fibrewiseContainment_baseChange {Y' : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (U : X.Opens) (g : Y' ⟶ Y) :
    fibrewiseContainment (pullback.snd f g)
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F) (pullback.fst f g ⁻¹ᵁ U) =
      g ⁻¹' fibrewiseContainment f F U := by
  ext z
  exact (associatedPoints_fiber_subset_preimage_iff_baseChange f F U g z).symm

/-- The fibrewise containment locus is unchanged when the source is replaced by an isomorphic
scheme: for `e : X' ≅ X` the locus of `(e.hom ≫ f, e.hom ^* F, e.hom ⁻¹ U)` is that of
`(f, F, U)`.

The isomorphism induces an isomorphism of the fibres over each point of the base compatible
with their embeddings into the sources, which carries the associated points of one fibre module
onto those of the other and the fibre of one open subscheme onto that of the other. -/
theorem fibrewiseContainment_comp_iso {X' : Scheme.{u}} (f : X ⟶ Y) (e : X' ≅ X) (F : X.Modules)
    (U : X.Opens) :
    fibrewiseContainment (e.hom ≫ f) ((Scheme.Modules.pullback e.hom).obj F) (e.hom ⁻¹ᵁ U) =
      fibrewiseContainment f F U := by
  ext y
  have h₁ : (e.hom ≫ f) ≫ 𝟙 Y = e.hom ≫ f := by simp
  have h₂ : Y.fromSpecResidueField y ≫ 𝟙 Y =
      𝟙 (Spec (Y.residueField y)) ≫ Y.fromSpecResidueField y := by simp
  let k : (e.hom ≫ f).fiber y ⟶ f.fiber y :=
    pullback.map (e.hom ≫ f) (Y.fromSpecResidueField y) f (Y.fromSpecResidueField y) e.hom
      (𝟙 (Spec (Y.residueField y))) (𝟙 Y) h₁ h₂
  have hk : IsIso k :=
    pullback.map_isIso (e.hom ≫ f) (Y.fromSpecResidueField y) f (Y.fromSpecResidueField y) e.hom
      (𝟙 (Spec (Y.residueField y))) (𝟙 Y) h₁ h₂
  have hw : k ≫ f.fiberι y = (e.hom ≫ f).fiberι y ≫ e.hom := pullback.lift_fst _ _ _
  have hwpt (x : (e.hom ≫ f).fiber y) : f.fiberι y (k x) = e.hom ((e.hom ≫ f).fiberι y x) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun h : (e.hom ≫ f).fiber y ⟶ X => h x) hw
  have hass : Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback ((e.hom ≫ f).fiberι y)).obj
          ((Scheme.Modules.pullback e.hom).obj F)) =
      k ⁻¹' Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback (f.fiberι y)).obj F) := by
    rw [Stacks.Divisors.associatedPoints_pullback_comp, ← hw,
      ← Stacks.Divisors.associatedPoints_pullback_comp]
    exact Stacks.Divisors.associatedPoints_pullback_of_iso (asIso k) _
  have hopen : (e.hom ≫ f).fiberι y ⁻¹' ((e.hom ⁻¹ᵁ U : X'.Opens) : Set X') =
      k ⁻¹' (f.fiberι y ⁻¹' (U : Set X)) := by
    ext x
    simp only [Set.mem_preimage, Scheme.Hom.coe_preimage, hwpt x]
  rw [mem_fibrewiseContainment, mem_fibrewiseContainment, hass, hopen]
  exact (Scheme.homeoOfIso (asIso k)).surjective.preimage_subset_preimage_iff

/-- The fibrewise containment locus depends on the data only through an isomorphism of the
source: it is unchanged when the source is replaced by an isomorphic scheme over the same base,
the module by one isomorphic to its pullback and the open subscheme by the inverse image. -/
theorem fibrewiseContainment_eq_of_iso {X' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y) (e : X' ≅ X)
    (he : e.hom ≫ f = f') (F : X.Modules) (F' : X'.Modules)
    (eF : F' ≅ (Scheme.Modules.pullback e.hom).obj F) (U : X.Opens) (U' : X'.Opens)
    (hU : U' = e.hom ⁻¹ᵁ U) :
    fibrewiseContainment f' F' U' = fibrewiseContainment f F U := by
  subst he
  subst hU
  rw [← fibrewiseContainment_comp_iso f e F U]
  ext y
  rw [mem_fibrewiseContainment, mem_fibrewiseContainment,
    Stacks.Divisors.associatedPoints_congr
      ((Scheme.Modules.pullback ((e.hom ≫ f).fiberι y)).mapIso eF)]

/-! ### The dichotomy on an irreducible closed subset of the base -/

/-- **The input of Stacks 053Z for the fibrewise containment locus.** On an irreducible closed
subset `Z` of the base, the fibrewise containment locus either contains a nonempty open part of
`Z` or is disjoint from one.

The subset `Z` is given its reduced closed subscheme structure, which is an irreducible scheme;
over it the containment at the generic point spreads to a nonempty open by Stacks 05KP and its
failure spreads by Stacks 05KN, and either conclusion is carried back to `Y` along the closed
immersion using Stacks 05KQ. -/
theorem exists_open_inter_dichotomy (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (U : X.Opens) (Z : Set Y)
    (hZirr : IsIrreducible Z) (hZcl : IsClosed Z) :
    (∃ V : Set Y, IsOpen V ∧ (V ∩ Z).Nonempty ∧ V ∩ Z ⊆ fibrewiseContainment f F U) ∨
      (∃ V : Set Y, IsOpen V ∧ (V ∩ Z).Nonempty ∧
        Disjoint (V ∩ Z) (fibrewiseContainment f F U)) := by
  classical
  set J : Y.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZcl⟩ : Closeds Y) with hJ
  set i : J.subscheme ⟶ Y := J.subschemeι with hi
  have hrange : Set.range i = Z := by
    rw [hi, J.range_subschemeι, hJ]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  set eZ : J.subscheme ≃ₜ Z := i.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
    with heZ
  have heZval (z : J.subscheme) : (eZ z).1 = i z := rfl
  have hiZ (z : J.subscheme) : i z ∈ Z := hrange ▸ Set.mem_range_self z
  have : IrreducibleSpace Z := Subtype.irreducibleSpace hZirr
  have : IrreducibleSpace J.subscheme := eZ.irreducibleSpace_iff.mpr inferInstance
  set f' : (pullback f i : Scheme.{u}) ⟶ J.subscheme := pullback.snd f i with hf'
  set F' : (pullback f i : Scheme.{u}).Modules :=
    (Scheme.Modules.pullback (pullback.fst f i)).obj F with hF'
  set U' : (pullback f i : Scheme.{u}).Opens := pullback.fst f i ⁻¹ᵁ U with hU'
  have hlocus : fibrewiseContainment f' F' U' = i ⁻¹' fibrewiseContainment f F U :=
    fibrewiseContainment_baseChange f F U i
  set η : J.subscheme := genericPoint J.subscheme with hηdef
  have hη : IsGenericPoint η (Set.univ : Set J.subscheme) := genericPoint_spec J.subscheme
  -- An open subset of the subscheme is the trace of an open subset of `Y` on `Z`.
  have htrace : ∀ V : (J.subscheme).Opens, (V : Set J.subscheme).Nonempty →
      ∃ W : Set Y, IsOpen W ∧ (W ∩ Z).Nonempty ∧ ∀ y ∈ W ∩ Z, ∃ z ∈ V, i z = y := by
    intro V hVne
    obtain ⟨W, hWopen, hWeq⟩ := isOpen_induced_iff.mp (eZ.isOpenMap _ V.2)
    have hfwd : ∀ z : J.subscheme, z ∈ V → i z ∈ W := by
      intro z hz
      have h1 : eZ z ∈ (Subtype.val : Z → Y) ⁻¹' W := by
        rw [hWeq]; exact ⟨z, hz, rfl⟩
      simpa only [Set.mem_preimage, heZval z] using h1
    refine ⟨W, hWopen, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hVne
      exact ⟨i z, hfwd z hz, hiZ z⟩
    · rintro y ⟨hyW, hyZ⟩
      have h1 : (⟨y, hyZ⟩ : Z) ∈ (Subtype.val : Z → Y) ⁻¹' W := hyW
      rw [hWeq] at h1
      obtain ⟨z, hzV, hzy⟩ := h1
      exact ⟨z, hzV, by simpa only [heZval z] using congrArg Subtype.val hzy⟩
  by_cases hηE : η ∈ fibrewiseContainment f' F' U'
  · obtain ⟨V, hVne, hV⟩ :=
      Stacks.Divisors.exists_open_associatedPoints_fiber_subset f' F' U' η hη hηE
    obtain ⟨W, hWopen, hWne, hW⟩ := htrace V hVne
    refine Or.inl ⟨W, hWopen, hWne, ?_⟩
    intro y hy
    obtain ⟨z, hzV, rfl⟩ := hW y hy
    exact hlocus.subset (hV z hzV)
  · obtain ⟨V, hVne, hV⟩ :=
      Stacks.RelativeAssassin.exists_open_forall_not_associatedPoints_fibre_subset f' F' U' η hη
        hηE
    obtain ⟨W, hWopen, hWne, hW⟩ := htrace V hVne
    refine Or.inr ⟨W, hWopen, hWne, Set.disjoint_left.2 ?_⟩
    intro y hy hyE
    obtain ⟨z, hzV, rfl⟩ := hW y hy
    exact hV z hzV (hlocus.symm.subset (show z ∈ i ⁻¹' fibrewiseContainment f F U from hyE))

/-- The fibrewise containment locus of a finite type morphism and a finite type quasi-coherent
module is constructible when the base is a Noetherian space; this is Stacks 053Z applied to the
dichotomy supplied by Stacks 05KN and Stacks 05KP. -/
theorem isConstructible_fibrewiseContainment [NoetherianSpace Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (U : X.Opens) :
    IsConstructible (fibrewiseContainment f F U) :=
  Topology.isConstructible_of_open_dichotomy fun Z hZirr hZcl =>
    exists_open_inter_dichotomy f F U Z hZirr hZcl

/-! ### Reduction to a Noetherian base -/

/-- Three base changes of one pullback square: if `β ≫ δ = g`, then the base change along `β` of
the first projection of the fibre product of `δ` and `p` is the fibre product of `g` and `p`. -/
private theorem exists_pullback_stage_iso {C : Type*} [Category C] [HasPullbacks C]
    {B S T P : C} (δ : T ⟶ B) (p : P ⟶ B) (β : S ⟶ T) (g : S ⟶ B) (h : β ≫ δ = g) :
    ∃ ee : pullback (pullback.fst δ p) β ≅ pullback g p,
      ee.hom ≫ pullback.fst g p = pullback.snd (pullback.fst δ p) β ∧
        ee.hom ≫ pullback.snd g p =
          pullback.fst (pullback.fst δ p) β ≫ pullback.snd δ p := by
  let ee := pullbackSymmetry (pullback.fst δ p) β ≪≫
    pullbackRightPullbackFstIso δ p β ≪≫ pullback.congrHom h rfl
  have hfst : (pullback.congrHom h rfl).hom ≫ pullback.fst g p = pullback.fst (β ≫ δ) p := by
    simp only [pullback.congrHom_hom, pullback.map, Category.comp_id, pullback.lift_fst]
  have hsnd : (pullback.congrHom h rfl).hom ≫ pullback.snd g p = pullback.snd (β ≫ δ) p := by
    simp only [pullback.congrHom_hom, pullback.map, Category.comp_id, pullback.lift_snd]
  refine ⟨ee, ?_, ?_⟩
  · simp only [ee, Iso.trans_hom, Category.assoc, hfst,
      pullbackRightPullbackFstIso_hom_fst, pullbackSymmetry_hom_comp_fst]
  · simp only [ee, Iso.trans_hom, Category.assoc, hsnd,
      pullbackRightPullbackFstIso_hom_snd]
    rw [← Category.assoc, pullbackSymmetry_hom_comp_snd]

/-- The part of an open subscheme `U` lying over a compact open `V` of the base is compact,
read on the base change of the source along the inclusion of `V`. -/
private theorem isCompact_preimage_pullback_fst (f : X ⟶ Y) (U : X.Opens)
    [QuasiCompact (U.ι ≫ f)] (V : Y.Opens) (hV : IsCompact (V : Set Y)) :
    IsCompact ((pullback.fst f V.ι ⁻¹ᵁ U : (pullback f V.ι : Scheme.{u}).Opens) :
      Set (pullback f V.ι : Scheme.{u})) := by
  have hrange : Set.range (pullback.fst f V.ι).base = ((f ⁻¹ᵁ V : X.Opens) : Set X) := by
    have hs : Function.Surjective (pullbackRestrictIsoRestrict f V).inv.base :=
      (Scheme.homeoOfIso (pullbackRestrictIsoRestrict f V).symm).surjective
    rw [← (f ⁻¹ᵁ V).range_ι, ← pullbackRestrictIsoRestrict_inv_fst f V]
    exact (hs.range_comp _).symm
  have hUV : IsCompact ((U : Set X) ∩ ((f ⁻¹ᵁ V : X.Opens) : Set X)) := by
    have h1 : IsCompact ((((U.ι ≫ f) ⁻¹ᵁ V : U.toScheme.Opens)) : Set U.toScheme) :=
      (U.ι ≫ f).isCompact_preimage hV
    have h2 := h1.image U.ι.continuous
    rw [Scheme.Hom.comp_preimage] at h2
    rw [show (U.ι.base '' ((U.ι ⁻¹ᵁ (f ⁻¹ᵁ V) : U.toScheme.Opens) : Set U.toScheme)) =
        U.ι.base '' (U.ι.base ⁻¹' ((f ⁻¹ᵁ V : X.Opens) : Set X)) from rfl,
      Set.image_preimage_eq_inter_range, U.range_ι, Set.inter_comm] at h2
    exact h2
  rw [(pullback.fst f V.ι).isEmbedding.isCompact_iff,
    show ((pullback.fst f V.ι ⁻¹ᵁ U : (pullback f V.ι : Scheme.{u}).Opens) :
        Set (pullback f V.ι : Scheme.{u})) = (pullback.fst f V.ι).base ⁻¹' (U : Set X) from rfl,
    Set.image_preimage_eq_inter_range, hrange]
  exact hUV

/-- The spectrum of the subalgebra generated over `ℤ` by a finite subset of a commutative ring is
a Noetherian space. -/
private theorem noetherianSpace_spec_adjoin_finset (R : CommRingCat.{u}) (s : Finset R) :
    NoetherianSpace (Spec (CommRingCat.of (Algebra.adjoin ℤ (s : Set R)))) := by
  have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (s : Set R)) :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
  have := Algebra.FiniteType.isNoetherianRing ℤ (Algebra.adjoin ℤ (s : Set R))
  infer_instance

/-- Let `β ≫ δ = g` and let `π : S ×_B P ⟶ T ×_B P` lie over `β`. If `(f, F, U)` is isomorphic to
the pullback along `π` of data `(Fn, Un)` on `T ×_B P ⟶ T`, then its fibrewise containment locus
is the inverse image under `β` of that of `(T ×_B P ⟶ T, Fn, Un)`. -/
private theorem fibrewiseContainment_eq_preimage_of_stage {S T B P : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (U : X.Opens) (δ : T ⟶ B) (p : P ⟶ B) (β : S ⟶ T) (g : S ⟶ B)
    (hβδ : β ≫ δ = g) (π : (pullback g p : Scheme.{u}) ⟶ (pullback δ p : Scheme.{u}))
    (hπfst : π ≫ pullback.fst δ p = pullback.fst g p ≫ β)
    (hπsnd : π ≫ pullback.snd δ p = pullback.snd g p)
    (eT : X ≅ (pullback g p : Scheme.{u})) (heTf : eT.hom ≫ pullback.fst g p = f)
    [LocallyOfFiniteType (pullback.fst δ p)] (Fn : (pullback δ p : Scheme.{u}).Modules)
    [Fn.IsQuasicoherent] [Fn.IsFiniteType]
    (eFn : (Scheme.Modules.pullback eT.inv).obj F ≅ (Scheme.Modules.pullback π).obj Fn)
    (Un : (pullback δ p : Scheme.{u}).Opens) (hUn : π ⁻¹ᵁ Un = eT.inv ⁻¹ᵁ U) :
    fibrewiseContainment f F U = β ⁻¹' fibrewiseContainment (pullback.fst δ p) Fn Un := by
  obtain ⟨eQ, hQ1, hQ2⟩ := exists_pullback_stage_iso δ p β g hβδ
  have hMap : eQ.hom ≫ π = pullback.fst (pullback.fst δ p) β := by
    refine pullback.hom_ext (f := δ) (g := p) ?_ ?_
    · rw [Category.assoc, hπfst, ← Category.assoc, hQ1]
      exact (pullback.condition (f := pullback.fst δ p) (g := β)).symm
    · rw [Category.assoc, hπsnd]
      exact hQ2
  have hQinv1 : eQ.inv ≫ pullback.snd (pullback.fst δ p) β = pullback.fst g p := by
    rw [← hQ1, Iso.inv_hom_id_assoc]
  have hQinv2 : eQ.inv ≫ pullback.fst (pullback.fst δ p) β = π := by
    rw [← hMap, Iso.inv_hom_id_assoc]
  let eXQ : X ≅ (pullback (pullback.fst δ p) β : Scheme.{u}) := eT ≪≫ eQ.symm
  have heXQf : eXQ.hom ≫ pullback.snd (pullback.fst δ p) β = f := by
    simpa only [eXQ, Iso.trans_hom, Iso.symm_hom, Category.assoc, hQinv1] using heTf
  have heXQπ : eXQ.hom ≫ pullback.fst (pullback.fst δ p) β = eT.hom ≫ π := by
    simp only [eXQ, Iso.trans_hom, Iso.symm_hom, Category.assoc, hQinv2]
  let eFX : (Scheme.Modules.pullback eXQ.hom).obj
        ((Scheme.Modules.pullback (pullback.fst (pullback.fst δ p) β)).obj Fn) ≅ F :=
    (Scheme.Modules.pullbackComp eXQ.hom (pullback.fst (pullback.fst δ p) β)).app Fn ≪≫
      (Scheme.Modules.pullbackCongr heXQπ).app Fn ≪≫
      ((Scheme.Modules.pullbackComp eT.hom π).app Fn).symm ≪≫
      (Scheme.Modules.pullback eT.hom).mapIso eFn.symm ≪≫
      (Scheme.Modules.pullbackComp eT.hom eT.inv).app F ≪≫
      (Scheme.Modules.pullbackCongr eT.hom_inv_id).app F ≪≫
      (Scheme.Modules.pullbackId X).app F
  have hUX : U = eXQ.hom ⁻¹ᵁ (pullback.fst (pullback.fst δ p) β ⁻¹ᵁ Un) := by
    rw [← Scheme.Hom.comp_preimage, heXQπ, Scheme.Hom.comp_preimage, hUn,
      ← Scheme.Hom.comp_preimage, eT.hom_inv_id]
    simp
  rw [fibrewiseContainment_eq_of_iso (pullback.snd (pullback.fst δ p) β) f eXQ heXQf
    ((Scheme.Modules.pullback (pullback.fst (pullback.fst δ p) β)).obj Fn) F eFX.symm
    (pullback.fst (pullback.fst δ p) β ⁻¹ᵁ Un) U hUX]
  exact fibrewiseContainment_baseChange (pullback.fst δ p) Fn Un β

/-- Over a cofiltered limit of quasi-compact quasi-separated schemes with affine transition maps,
a module of finite presentation and a quasi-compact open subscheme of the limit both descend to a
common stage. -/
private theorem exists_stage_pullback_iso_and_preimage_eq {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D)
    (hc : IsLimit c) (F : c.pt.Modules) [F.IsFinitePresentation] (U : c.pt.Opens)
    (hU : IsCompact (U : Set c.pt)) :
    ∃ (n : I) (Fn : (D.obj n).Modules), Fn.IsFinitePresentation ∧
      Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app n)).obj Fn) ∧
      ∃ Un : (D.obj n).Opens, c.π.app n ⁻¹ᵁ Un = U := by
  obtain ⟨k₀, Fk₀, hFk₀, ⟨eF₀⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs D c hc F
  obtain ⟨k₁, Uk₁, -, hUk₁⟩ := AlgebraicGeometry.exists_preimage_eq D c hc U hU
  let m₀ : IsCofiltered.min k₀ k₁ ⟶ k₀ := IsCofiltered.minToLeft k₀ k₁
  let m₁ : IsCofiltered.min k₀ k₁ ⟶ k₁ := IsCofiltered.minToRight k₀ k₁
  refine ⟨IsCofiltered.min k₀ k₁, (Scheme.Modules.pullback (D.map m₀)).obj Fk₀,
    Stacks.Modules.isFinitePresentation_pullback (D.map m₀) Fk₀ hFk₀,
    ⟨eF₀ ≪≫ (Scheme.Modules.pullbackCongr (c.w m₀)).symm.app Fk₀ ≪≫
      ((Scheme.Modules.pullbackComp (c.π.app _) (D.map m₀)).app Fk₀).symm⟩,
    D.map m₁ ⁻¹ᵁ Uk₁, ?_⟩
  rw [show c.π.app _ ⁻¹ᵁ (D.map m₁ ⁻¹ᵁ Uk₁) = (c.π.app _ ≫ D.map m₁) ⁻¹ᵁ Uk₁ from
    (Scheme.Hom.comp_preimage _ _ _).symm, c.w m₁]
  exact hUk₁

/-- Over a cofiltered limit of qcqs schemes with affine transition maps and Noetherian stages,
the fibrewise containment locus of data on a base change of a finitely presented model at some
stage is locally constructible. -/
private theorem isLocallyConstructible_fibrewiseContainment_of_model {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ {j k : I} (e : j ⟶ k), IsAffineHom (D.map e)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ j, NoetherianSpace (D.obj j)] (c : Cone D) (hc : IsLimit c) {X : Scheme.{u}}
    (f : X ⟶ c.pt) (F : X.Modules) [F.IsFinitePresentation] (U : X.Opens)
    (hU : IsCompact (U : Set X)) (i : I) (Xi : Over (D.obj i)) [LocallyOfFiniteType Xi.hom]
    [QuasiCompact Xi.hom] [QuasiSeparated Xi.hom]
    (eT : X ≅ (pullback (c.π.app i) Xi.hom : Scheme.{u}))
    (heTf : eT.hom ≫ pullback.fst (c.π.app i) Xi.hom = f) :
    IsLocallyConstructible (fibrewiseContainment f F U) := by
  let g : c.pt ⟶ D.obj i := c.π.app i
  -- the diagram of base changes of the model, whose limit is the source
  let dg : Over i ⥤ Scheme.{u} := Scheme.baseChangeDiagram D i Xi
  let cc : Cone dg := Scheme.baseChangeCone D i Xi c
  have hcc : IsLimit cc := Scheme.isLimitBaseChangeCone D i Xi c hc
  have hdgah : ∀ {j k : Over i} (ee : j ⟶ k), IsAffineHom (dg.map ee) := fun ee =>
    Scheme.isAffineHom_baseChangeDiagram_map D i Xi ee
  have hdgcpt (j : Over i) : CompactSpace (dg.obj j) :=
    have : QuasiCompact (pullback.fst (D.map j.hom) Xi.hom) := inferInstance
    (QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map j.hom) Xi.hom) :
      CompactSpace (pullback (D.map j.hom) Xi.hom : Scheme.{u}))
  have hdgqs (j : Over i) : QuasiSeparatedSpace (dg.obj j) :=
    have : QuasiSeparated (pullback.fst (D.map j.hom) Xi.hom) := inferInstance
    (quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map j.hom) Xi.hom) :
      QuasiSeparatedSpace (pullback (D.map j.hom) Xi.hom : Scheme.{u}))
  let FT : cc.pt.Modules := (Scheme.Modules.pullback eT.inv).obj F
  have hFT : FT.IsFinitePresentation :=
    Stacks.Modules.isFinitePresentation_pullback eT.inv F inferInstance
  -- Stacks 01ZR and Stacks 01Z4: the module and the open subscheme descend to stages
  obtain ⟨n, Fn₀, hFn₀, ⟨eFn⟩, Un, hUneq⟩ :=
    exists_stage_pullback_iso_and_preimage_eq dg cc hcc FT (eT.inv ⁻¹ᵁ U)
      (eT.inv.isCompact_preimage hU)
  let δ : D.obj n.left ⟶ D.obj i := D.map n.hom
  let π : (pullback g Xi.hom : Scheme.{u}) ⟶ (pullback δ Xi.hom : Scheme.{u}) := cc.π.app n
  let Fn : (pullback δ Xi.hom : Scheme.{u}).Modules := Fn₀
  have hFnfp : Fn.IsFinitePresentation := hFn₀
  have hFnqc : Fn.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation Fn
  have hFnft : Fn.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation Fn
  -- the stage data, and the comparison of the source with their base change
  let β : c.pt ⟶ D.obj n.left := c.π.app n.left
  have hβδ : β ≫ δ = g := c.w n.hom
  have hπfst : π ≫ pullback.fst δ Xi.hom = pullback.fst g Xi.hom ≫ β :=
    Scheme.baseChangeCone_π_fst D i Xi c n
  have hπsnd : π ≫ pullback.snd δ Xi.hom = pullback.snd g Xi.hom :=
    Scheme.baseChangeCone_π_snd D i Xi c n
  rw [fibrewiseContainment_eq_preimage_of_stage f F U δ Xi.hom β g hβδ π hπfst hπsnd eT heTf Fn
    eFn Un hUneq]
  exact AlgebraicGeometry.isLocallyConstructible_preimage β
    (isConstructible_fibrewiseContainment (pullback.fst δ Xi.hom) Fn Un).isLocallyConstructible

/-- **Stacks Project, Tag 05KR over the spectrum of a ring.** The limit argument of the source:
the base is the limit of the spectra of the subalgebras generated over `ℤ` by the finite subsets
of its ring, the morphism, the module and the open subscheme all descend to a stage with
Noetherian base, and the locus there pulls back to the locus. -/
private theorem isLocallyConstructible_fibrewiseContainment_spec {X : Scheme.{u}}
    (R : CommRingCat.{u}) (f : X ⟶ Spec R) (hf : AlgebraicGeometry.FinitePresentation f)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    IsLocallyConstructible (fibrewiseContainment f F U) := by
  classical
  -- the presentation of the base as a limit of spectra of Noetherian rings
  let D : (Finset R)ᵒᵖ ⥤ Scheme.{u} := R.finiteSubalgebras.op ⋙ Scheme.Spec
  let cBase : Cone D := Scheme.Spec.mapCone R.finiteSubalgebrasCocone.op
  let c : Cone D := { pt := Spec R, π := cBase.π }
  have hc : IsLimit c := by
    show IsLimit cBase
    exact isLimitOfPreserves _ R.finiteSubalgebrasIsColimit.op
  have hDaff : ∀ j, IsAffine (D.obj j) := fun j => inferInstanceAs (IsAffine (Spec _))
  have hDah : ∀ {j k : (Finset R)ᵒᵖ} (ee : j ⟶ k), IsAffineHom (D.map ee) := fun _ => inferInstance
  have hDcpt : ∀ j, CompactSpace (D.obj j) := fun j => inferInstance
  have hDqs : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j => inferInstance
  -- Stacks 01ZM: the morphism descends to a stage
  obtain ⟨i, Xi, hXi, ⟨e⟩⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation D c hc
      (Over.mk f) hf
  have hXilfp : LocallyOfFinitePresentation Xi.hom := hXi.1
  have hXiqc : QuasiCompact Xi.hom := hXi.2.1
  have hXiqs : QuasiSeparated Xi.hom := hXi.2.2
  let g : Spec R ⟶ D.obj i := c.π.app i
  let eX : X ≅ (pullback Xi.hom g : Scheme.{u}) := (Over.forget (Spec R)).mapIso e
  have heXf : eX.hom ≫ pullback.snd Xi.hom g = f := Over.w e.hom
  let eT : X ≅ (pullback g Xi.hom : Scheme.{u}) := eX ≪≫ pullbackSymmetry Xi.hom g
  have heTf : eT.hom ≫ pullback.fst g Xi.hom = f := by
    simpa only [eT, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst] using heXf
  have hDnoeth : ∀ j, NoetherianSpace (D.obj j) := fun j =>
    noetherianSpace_spec_adjoin_finset R j.unop
  exact isLocallyConstructible_fibrewiseContainment_of_model D c hc f F U hU i Xi eT heTf

/-- **Stacks Project, Tag 05KR over an affine base.** The base is identified with the spectrum
of its ring of global sections, and the locus is carried along that isomorphism. -/
private theorem isLocallyConstructible_fibrewiseContainment_of_isAffine [IsAffine Y]
    (f : X ⟶ Y) (hf : AlgebraicGeometry.FinitePresentation f) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] (U : X.Opens) (hU : IsCompact (U : Set X)) :
    IsLocallyConstructible (fibrewiseContainment f F U) := by
  obtain ⟨_, _, _⟩ := hf
  have hft : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  let h : Y ≅ Spec Γ(Y, ⊤) := Y.isoSpec
  refine (Homeomorph.isLocallyConstructible_preimage_iff (Scheme.homeoOfIso h).symm
    (fibrewiseContainment f F U)).mp ?_
  rw [show (⇑(Scheme.homeoOfIso h).symm ⁻¹' fibrewiseContainment f F U) =
    h.inv.base ⁻¹' fibrewiseContainment f F U from rfl,
    ← fibrewiseContainment_baseChange f F U h.inv]
  exact isLocallyConstructible_fibrewiseContainment_spec Γ(Y, ⊤) (pullback.snd f h.inv)
    ⟨inferInstance, inferInstance, inferInstance⟩
    ((Scheme.Modules.pullback (pullback.fst f h.inv)).obj F) (pullback.fst f h.inv ⁻¹ᵁ U)
    ((pullback.fst f h.inv).isCompact_preimage hU)

/-- **Stacks Project, Tag 05KR.** Let `f : X ⟶ Y` be a morphism of finite presentation, let `F`
be a quasi-coherent `𝒪_X`-module of finite presentation and let `U ⊆ X` be an open subscheme
with `U ⟶ Y` quasi-compact. Then the set of points `y` of `Y` over which every associated point
of the fibre `F_y` lies in the fibre `U_y` is locally constructible in `Y`. -/
@[stacks 05KR]
theorem isLocallyConstructible_fibrewiseContainment (f : X ⟶ Y)
    (hf : AlgebraicGeometry.FinitePresentation f) (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFinitePresentation] (U : X.Opens) [QuasiCompact (U.ι ≫ f)] :
    IsLocallyConstructible (fibrewiseContainment f F U) := by
  obtain ⟨_, _, _⟩ := hf
  have hft : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  rw [Topology.IsLocallyConstructible.iff_of_isOpenCover
    (U := fun V : Y.affineOpens => V.1) (iSup_affineOpens_eq_top Y)]
  intro V
  have hbase : fibrewiseContainment (pullback.snd f V.1.ι)
        ((Scheme.Modules.pullback (pullback.fst f V.1.ι)).obj F)
        (pullback.fst f V.1.ι ⁻¹ᵁ U) = V.1.ι.base ⁻¹' fibrewiseContainment f F U :=
    fibrewiseContainment_baseChange f F U V.1.ι
  have hfp' : AlgebraicGeometry.FinitePresentation (pullback.snd f V.1.ι) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hVaff : IsAffine V.1.toScheme := V.2
  have hres := isLocallyConstructible_fibrewiseContainment_of_isAffine (pullback.snd f V.1.ι)
    hfp' ((Scheme.Modules.pullback (pullback.fst f V.1.ι)).obj F)
    (pullback.fst f V.1.ι ⁻¹ᵁ U) (isCompact_preimage_pullback_fst f U V.1 V.2.isCompact)
  rw [hbase] at hres
  exact hres

end Stacks.RelativeAssassin

end
