module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassCupVanishing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupRelation
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionInduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GysinOpenImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinTransversal
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareIso
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.Etale
public import StacksFrontier.Topology.Dimension.LocalDimensionComponents
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionZeroOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceUniqueness

/-!
# Lemma 0FII for an arbitrary smooth projective scheme

This file reduces Lemma 0FII to the parts of constant dimension.

## Main results

In namespace `Stacks.WeilCohomology.SmoothProjectiveScheme`:

* `clopenι`, `clopenRestrict`: an open and closed subscheme `U ⊆ X` and the restriction
  `Z ∩ U ⟶ U` of a closed immersion `Z ⟶ X`.
* `codimensionGysin_clopenι_closedSubschemeClass`: `[Z]|_U = [Z ∩ U]`.

In namespace `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter`:

* `cup_codimensionCycleClass_eq_zero`, `codimensionCycleClass_cup_eq_zero`: **Lemma 0FII**, the
  latter in the source's order `γ([Z]) ∪ a = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- The inclusion of an open and closed subscheme. -/
def clopenι (X : (SmoothProjectiveScheme k).FullSubcategory) (U : X.obj.left.Opens)
    (hU : IsClopen (U : Set X.obj.left)) : clopenObj X U hU ⟶ X :=
  ObjectProperty.homMk (Over.homMk (U := (clopenObj X U hU).obj) U.ι rfl)

/-- The underlying morphism of schemes of `clopenι X U hU` is the open immersion `U.ι`. -/
@[simp]
theorem clopenι_hom_left (X : (SmoothProjectiveScheme k).FullSubcategory) (U : X.obj.left.Opens)
    (hU : IsClopen (U : Set X.obj.left)) : (clopenι X U hU).hom.left = U.ι :=
  rfl

/-- The inclusion of an open and closed subscheme is an open immersion. -/
instance (X : (SmoothProjectiveScheme k).FullSubcategory) (U : X.obj.left.Opens)
    (hU : IsClopen (U : Set X.obj.left)) : IsOpenImmersion (clopenι X U hU).hom.left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- For open and closed subschemes `U ≤ V` of `X`, the inclusion `U ⟶ V` followed by the inclusion
`V ⟶ X` is the inclusion `U ⟶ X`. -/
theorem clopenHomOfLE_comp_clopenι {X : (SmoothProjectiveScheme k).FullSubcategory}
    {U V : X.obj.left.Opens}
    (hU : IsClopen (U : Set X.obj.left)) (hV : IsClopen (V : Set X.obj.left)) (e : U ≤ V) :
    clopenHomOfLE hU hV e ≫ clopenι X V hV = clopenι X U hU :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (X.obj.left.homOfLE_ι e))

variable {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left]
  (U : X.obj.left.Opens) (hU : IsClopen (U : Set X.obj.left))

omit [IsClosedImmersion i.hom.left] in
include hU in
/-- The preimage of an open and closed subscheme is open and closed. -/
theorem isClopen_preimage : IsClopen ((i.hom.left ⁻¹ᵁ U : Z.obj.left.Opens) : Set Z.obj.left) :=
  hU.preimage i.hom.left.continuous

/-- **The restriction `Z ∩ U ⟶ U`** of a closed immersion `i : Z ⟶ X` to an open and closed
subscheme `U ⊆ X`. -/
def clopenRestrict :
    clopenObj Z (i.hom.left ⁻¹ᵁ U) (isClopen_preimage i U hU) ⟶ clopenObj X U hU :=
  ObjectProperty.homMk (Over.homMk (U := (clopenObj Z _ (isClopen_preimage i U hU)).obj)
    (V := (clopenObj X U hU).obj) (i.hom.left ∣_ U) (by
      change (i.hom.left ∣_ U) ≫ U.ι ≫ X.obj.hom = (i.hom.left ⁻¹ᵁ U).ι ≫ Z.obj.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w i.hom]))

omit [IsClosedImmersion i.hom.left] in
/-- The underlying morphism of schemes of `clopenRestrict i U hU` is the restriction
`i.hom.left ∣_ U`. -/
@[simp]
theorem clopenRestrict_hom_left : (clopenRestrict i U hU).hom.left = i.hom.left ∣_ U :=
  rfl

/-- The restriction of a closed immersion to an open subscheme of its target is a closed
immersion. -/
instance isClosedImmersion_morphismRestrict : IsClosedImmersion (i.hom.left ∣_ U) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_morphismRestrict i.hom.left U).flip
    inferInstance

/-- The restriction `Z ∩ U ⟶ U` of a closed immersion is a closed immersion. -/
instance : IsClosedImmersion (clopenRestrict i U hU).hom.left :=
  inferInstanceAs (IsClosedImmersion (i.hom.left ∣_ U))

omit [IsClosedImmersion i.hom.left] in
/-- The restriction `Z ∩ U ⟶ U` followed by the inclusion `U ⟶ X` equals the inclusion
`Z ∩ U ⟶ Z` followed by `i`. -/
theorem clopenRestrict_comp_clopenι :
    clopenRestrict i U hU ≫ clopenι X U hU =
      clopenι Z (i.hom.left ⁻¹ᵁ U) (isClopen_preimage i U hU) ≫ i :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (morphismRestrict_ι i.hom.left U))

/-- **`[Z]|_U = [Z ∩ U]`**: the Gysin map of the inclusion of an open and closed `U ⊆ X` carries
the class of `Z` to the class of `Z ∩ U`. -/
theorem codimensionGysin_clopenι_closedSubschemeClass (c : ℤ) :
    codimensionGysin (clopenObj X U hU).obj.hom X.obj.hom (Over.w (clopenι X U hU).hom) c
        (closedSubschemeClass X.obj.hom i.hom.left c) =
      closedSubschemeClass (clopenObj X U hU).obj.hom (clopenRestrict i U hU).hom.left c := by
  funext d
  rw [codimensionGysin_of_isOpenImmersion, closedSubschemeClass_apply, chowGroupRestrict_comp,
    chowGroupRestrict_congr
      (j' := (dimPart (clopenObj X U hU).obj.hom d).ι ≫ (clopenι X U hU).hom.left)
      (hjj' := dimPartMap_ι X.obj.hom (clopenObj X U hU).obj.hom (Over.w (clopenι X U hU).hom) d)
      (hj' := by rw [Category.assoc, Over.w (clopenι X U hU).hom]),
    ← chowGroupRestrict_comp (fieldChowSituation k) X.obj.hom (clopenObj X U hU).obj.hom
      (clopenι X U hU).hom.left (Over.w (clopenι X U hU).hom) _ _
      (dimPart (clopenObj X U hU).obj.hom d).ι rfl,
    chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme_of_isPullback (fieldChowSituation k)
      X.obj.hom (clopenObj X U hU).obj.hom (clopenι X U hU).hom.left rfl i.hom.left _
      (clopenRestrict i U hU).hom.left (isPullback_morphismRestrict i.hom.left U).flip,
    closedSubschemeClass_apply]

/-! ### The hypotheses of Lemma 0FII on `Z ∩ U` -/

omit [IsClosedImmersion i.hom.left] in
/-- **Every component of `Z ∩ U` has codimension `r` in `U`** when every component of `Z` has
codimension `r` in `X`: a component of the open `Z ∩ U ⊆ Z` is open in a component of `Z`, and
codimension is local. -/
theorem coheight_clopenRestrict {r : ℕ}
    (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
      Order.coheight (i.hom.left z) = r)
    (z : (clopenObj Z _ (isClopen_preimage i U hU)).obj.left)
    (hz : closure ({z} : Set _) ∈ irreducibleComponents
      (clopenObj Z _ (isClopen_preimage i U hU)).obj.left) :
    Order.coheight ((clopenRestrict i U hU).hom.left z) = r := by
  set V : Z.obj.left.Opens := i.hom.left ⁻¹ᵁ U
  have hcl : closure {V.ι.base z} ∈ irreducibleComponents Z.obj.left := by
    convert closure_image_mem_irreducibleComponents_of_isOpen V.isOpen hz using 1
    refine le_antisymm (closure_mono (Set.singleton_subset_iff.2 ⟨z, subset_closure rfl, rfl⟩))
      ?_
    refine closure_minimal ?_ isClosed_closure
    refine (image_closure_subset_closure_image continuous_subtype_val).trans (closure_mono ?_)
    rintro _ ⟨w, hw, rfl⟩
    obtain rfl : w = z := hw
    rfl
  have h1 := coheight_eq_of_etale U.ι ((i.hom.left ∣_ U) z)
  have h2 : U.ι.base ((i.hom.left ∣_ U) z) = i.hom.left.base (V.ι.base z) :=
    congrArg (fun f ↦ f.base z) (morphismRestrict_ι i.hom.left U)
  rw [h2] at h1
  exact h1.symm.trans (hr (V.ι.base z) hcl)

/-- **The class of `𝒞_{Z ∩ U/U}` is the restriction of `α`** when that of `𝒞_{Z/X}` is the
restriction of `α`: the conormal sheaf of `Z ∩ U ⊆ U` is the restriction of that of `Z ⊆ X`. -/
theorem pullback_clopenRestrict_eq_classOf (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α =
      VectorBundleKZero.classOf _ (centreConormal i)) :
    VectorBundleKZero.pullback (clopenRestrict i U hU).hom.left
        (VectorBundleKZero.pullback (clopenι X U hU).hom.left α) =
      VectorBundleKZero.classOf _ (centreConormal (clopenRestrict i U hU)) := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (centreConormal i) :=
    Stacks.ConormalSequenceRight.isFiniteLocallyFree_conormalSheaf_of_smooth i.hom.left X.obj.hom
  have hsq : (clopenRestrict i U hU).hom.left ≫ (clopenι X U hU).hom.left =
      (clopenι Z _ (isClopen_preimage i U hU)).hom.left ≫ i.hom.left :=
    morphismRestrict_ι i.hom.left U
  rw [← VectorBundleKZero.pullback_comp, hsq, VectorBundleKZero.pullback_comp, hα,
    VectorBundleKZero.pullback_classOf]
  exact VectorBundleKZero.classOf_eq_of_iso
    (@asIso _ _ _ _ _ (Stacks.Immersion.isIso_immersionConormalSheafMap_ι i.hom.left U))
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _)

/-- **`Z` is nowhere dense in `X`** when `X` and `Z` are of dimensions `n > e`: at a point of the
interior of the image, the local dimensions of `X` and `Z` would agree. -/
theorem isNowhereDense_range_of_relativeDimension {n e : ℕ} (hX : RelativeDimension X.obj.hom n)
    (hZ : RelativeDimension Z.obj.hom e) (he : e < n) :
    IsNowhereDense (Set.range i.hom.left.base) := by
  have hemb : Topology.IsClosedEmbedding i.hom.left.base := i.hom.left.isClosedEmbedding
  rw [hemb.isClosed_range.isNowhereDense_iff, ← Set.not_nonempty_iff_eq_empty]
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := interior_subset hy
  set V : Set Z.obj.left := i.hom.left.base ⁻¹' interior (Set.range i.hom.left.base)
  have hVo : IsOpen V := isOpen_interior.preimage i.hom.left.base.hom.continuous
  have hf : Topology.IsOpenEmbedding (fun v : V => i.hom.left.base v.1) := by
    refine ⟨hemb.isEmbedding.comp Topology.IsEmbedding.subtypeVal, ?_⟩
    convert (isOpen_interior : IsOpen (interior (Set.range i.hom.left.base))) using 1
    ext z
    refine ⟨?_, fun hz => ?_⟩
    · rintro ⟨v, rfl⟩
      exact v.2
    · obtain ⟨w, rfl⟩ := interior_subset hz
      exact ⟨⟨w, hz⟩, rfl⟩
  have h1 := hf.topologicalKrullDimAt_eq (⟨x, hy⟩ : V)
  have h2 := hVo.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq (⟨x, hy⟩ : V)
  have hXd := (relativeDimension_iff_forall_topologicalKrullDimAt_of_field X.obj.hom n).1 hX
    (i.hom.left.base x)
  have hZd := (relativeDimension_iff_forall_topologicalKrullDimAt_of_field Z.obj.hom e).1 hZ x
  simp only at h1 h2
  rw [h1, ← h2, hZd] at hXd
  exact he.ne (by exact_mod_cast hXd)

/-- The part of constant dimension `d` is open and closed (Stacks 02NM). -/
theorem isClopen_dimPart (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) :
    IsClopen (dimPart X.obj.hom d : Set X.obj.left) :=
  relativeDimensionOpen_isClopen X.obj.hom (fun s ↦ isCohenMacaulay_fiber_of_smooth X.obj.hom s) d

end SmoothProjectiveScheme

namespace FirstChernClassData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- A class vanishing on every part of constant dimension vanishes on each `lowDimPart`. -/
theorem pull_clopenι_lowDimPart_eq_zero (hA1 : 𝔇.CoproductAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : 𝔇.H X) (hx : ∀ d, 𝔇.pull (clopenι X (dimPart X.obj.hom d) (isClopen_dimPart X d)) x = 0)
    (n : ℕ) : 𝔇.pull (clopenι X (lowDimPart X n) (isClopen_lowDimPart X n)) x = 0 := by
  induction n with
  | zero =>
    have : IsEmpty ((SmoothProjectiveScheme.toScheme k).obj
        (clopenObj X (lowDimPart X 0) (isClopen_lowDimPart X 0))) := ⟨fun z ↦ by
      have hz : ((show ↥(lowDimPart X 0) from z) : X.obj.left) ∈ lowDimPart X 0 :=
        (show ↥(lowDimPart X 0) from z).2
      simp [lowDimPart] at hz⟩
    exact @Subsingleton.elim _ (hA1.1 _ this) _ _
  | succ n ih =>
    have hD := isClopen_dimPart X n
    obtain ⟨hc⟩ := nonempty_isColimit_clopen (X := X) hD (isClopen_lowDimPart X n)
      (isClopen_lowDimPart X (n + 1))
      ((lowDimPart_succ X n).symm ▸ le_sup_left) ((lowDimPart_succ X n).symm ▸ le_sup_right)
      (disjoint_dimPart_lowDimPart X n) (lowDimPart_succ X n).symm
    refine (hA1.2 _ _ _ _ _ ⟨isColimitMapCofan hc⟩).1 ?_
    simp only [Prod.mk.injEq, BinaryCofan.mk_inl, BinaryCofan.mk_inr]
    have key : ∀ {U : X.obj.left.Opens} (hU : IsClopen (U : Set X.obj.left))
        (e : U ≤ lowDimPart X (n + 1)), 𝔇.pull (clopenι X U hU) x = 0 →
        𝔇.pull (clopenHomOfLE hU (isClopen_lowDimPart X (n + 1)) e)
          (𝔇.pull (clopenι X (lowDimPart X (n + 1)) (isClopen_lowDimPart X (n + 1))) x) = 0 :=
      fun hU e h0 ↦ by
        rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, clopenHomOfLE_comp_clopenι, h0]
    exact ⟨(key hD _ (hx n)).trans (map_zero _).symm, (key _ _ ih).trans (map_zero _).symm⟩

/-- **A class vanishing on every part of constant dimension vanishes**, by (A1): `X` is the
disjoint union of its finitely many nonempty parts. -/
theorem eq_zero_of_pull_dimPart (hA1 : 𝔇.CoproductAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : 𝔇.H X) (hx : ∀ d, 𝔇.pull (clopenι X (dimPart X.obj.hom d) (isClopen_dimPart X d)) x = 0) :
    x = 0 := by
  obtain ⟨n, hn⟩ := exists_lowDimPart_eq_top X
  have hinj : ∀ (U : X.obj.left.Opens) (hU : IsClopen (U : Set X.obj.left)), U = ⊤ →
      Function.Injective (𝔇.pull (clopenι X U hU)) := by
    rintro U hU rfl
    have hφ : clopenι X ⊤ hU = (clopenTopIso X).hom :=
      ObjectProperty.hom_ext _ (Over.OverMorphism.ext (Scheme.topIso_hom _).symm)
    refine Function.LeftInverse.injective (g := 𝔇.pull (clopenTopIso X).inv) fun y ↦ ?_
    rw [hφ, ← AlgHom.comp_apply, ← 𝔇.pull_comp, Iso.inv_hom_id, 𝔇.pull_id, AlgHom.id_apply]
  exact hinj _ _ hn (by rw [𝔇.pull_clopenι_lowDimPart_eq_zero hA1 X x hx n, map_zero])

/-- A product `a ∪ b` with a twisted class vanishes iff it does in coordinates. -/
private theorem tateCupLeft_eq_zero_iff (X : (SmoothProjectiveScheme k).FullSubcategory) (r : ℕ)
    (cup : 𝔇.H X →ₗ[F] 𝔇.H X →ₗ[F] 𝔇.H X) (a : 𝔇.H X) (b : tateTwist F 𝔇.tate (𝔇.H X) r) :
    tateCupLeft cup (r : ℤ) a b = 0 ↔ cup a (𝔇.κ X r b) = 0 := by
  rw [← map_eq_zero_iff _ (𝔇.κ X r).injective, κ, tateTwistCoordinates_tateCupLeft]

namespace IsCohomologicalChernCharacter

variable {𝔇} [CharZero F]
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
      ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch)

/-- **Lemma 0FII for `X` equidimensional and `r ≥ 1`**, in coordinates: `a ∪ γ([Z]) = 0` when
`a|_Z = 0`. -/
theorem mul_κ_codimensionCycleClass_eq_zero_of_relativeDimension (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA7 : 𝔇.BlowupAxiom)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    {n : ℕ} (hX : RelativeDimension X.obj.hom n) (r : ℕ) (hr0 : 0 < r)
    (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
      Order.coheight (i.hom.left z) = r)
    (hK : ∃ α : VectorBundleKZero X.obj.left,
      VectorBundleKZero.pullback i.hom.left α = VectorBundleKZero.classOf _ (centreConormal i))
    (a : 𝔇.H X) (ha : 𝔇.pull i a = 0) :
    a * 𝔇.κ X r (h.codimensionCycleClass X r (closedSubschemeClass X.obj.hom i.hom.left r)) =
      0 := by
  have hZ := relativeDimension_of_codimension i hX hr
  by_cases hrn : r ≤ n
  · obtain ⟨α, hα⟩ := hK
    have hrel := codimensionGysin_closedSubschemeClass_heq_blowupTheta i hX hZ
      (show n - r + r = n by omega) hr0 α hα
    have hnd := isNowhereDense_range_of_relativeDimension i hX hZ (show n - r < n by omega)
    exact (𝔇.tateCupLeft_eq_zero_iff X r _ a _).1
      (h.cup_codimensionCycleClass_eq_zero_of_blowup hA1 hA3 hA4 hA7
        i hnd r (r - 1) (by omega) (blowupTheta i α r) hrel a ha)
  · have hY : RelativeDimension (i.hom.left ≫ X.obj.hom) (n - r) := by
      have key : ∀ (q : Z.obj.left ⟶ Spec (.of k)) [LocallyOfFiniteType q], q = Z.obj.hom →
          RelativeDimension q (n - r) := by
        rintro q _ rfl
        exact hZ
      exact key _ (Over.w i.hom)
    have h0 : closedSubschemeClass X.obj.hom i.hom.left r = 0 := by
      funext d
      by_cases hd : d = n
      · subst hd
        rw [closedSubschemeClass_apply,
          cycleAssociatedToClosedSubscheme_eq_zero_of_relativeDimension X.obj.hom i.hom.left hY
            (by omega)]
        simp
      · have := isEmpty_dimPart_of_ne X.obj.hom hX hd
        exact @Subsingleton.elim _
          (subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) _ _) _ _
    rw [h0, map_zero, map_zero, mul_zero]

/-- **Lemma 0FII for `r ≥ 1`**, in coordinates, for any smooth projective `X`: by (A1) it suffices
to check `a ∪ γ([Z]) = 0` on each part `X_d` of constant dimension, where it is the
equidimensional case for `Z ∩ X_d ⊆ X_d`, `γ` being compatible with pullbacks and
`[Z]|_{X_d} = [Z ∩ X_d]`. -/
theorem mul_κ_codimensionCycleClass_eq_zero_of_pos (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA7 : 𝔇.BlowupAxiom)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    (r : ℕ) (hr0 : 0 < r)
    (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
      Order.coheight (i.hom.left z) = r)
    (hK : ∃ α : VectorBundleKZero X.obj.left,
      VectorBundleKZero.pullback i.hom.left α = VectorBundleKZero.classOf _ (centreConormal i))
    (a : 𝔇.H X) (ha : 𝔇.pull i a = 0) :
    a * 𝔇.κ X r (h.codimensionCycleClass X r (closedSubschemeClass X.obj.hom i.hom.left r)) =
      0 := by
  obtain ⟨α, hα⟩ := hK
  refine 𝔇.eq_zero_of_pull_dimPart hA1 X _ fun d ↦ ?_
  set U := dimPart X.obj.hom d
  have hU := isClopen_dimPart X d
  rw [map_mul, ← κ_pullTw, ← h.codimensionCycleClass_codimensionGysin (clopenι X U hU) r,
    codimensionGysin_clopenι_closedSubschemeClass i U hU r]
  refine h.mul_κ_codimensionCycleClass_eq_zero_of_relativeDimension hA1 hA3 hA4 hA7
    (clopenRestrict i U hU) (relativeDimension_partBase X.obj.hom d) r hr0
    (coheight_clopenRestrict i U hU hr)
    ⟨_, pullback_clopenRestrict_eq_classOf i U hU α hα⟩ _ ?_
  rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, clopenRestrict_comp_clopenι, 𝔇.pull_comp,
    AlgHom.comp_apply, ha, map_zero]

/-- **Stacks Project, Lemma 0FII.** Let (D0), (D1), (D2') satisfy (A1)–(A4) and (A7), with `γ` the
cycle class map of Tag 0FIF. Let `X` be a smooth projective scheme over `k` and `i : Z ⟶ X` a
smooth closed subscheme every irreducible component of which has codimension `r` in `X`, such that
the class of `𝒞_{Z/X}` in `K_0(Z)` is the restriction of an element of `K_0(X)`. If `a ∈ H^*(X)`
restricts to `0` on `Z`, then `γ([Z]) ∪ a = 0`, written `a ∪ γ([Z])` with `γ([Z])` twisted.

"Every irreducible component of `Z` has codimension `r`" is read at the generic points of the
components: the codimension in `X` of the closure of the image of such a point is its coheight.
For `r ≥ 1` the proof is the source's, on each part of `X` of constant dimension
(`mul_κ_codimensionCycleClass_eq_zero_of_pos`). For `r = 0` the source's argument does not
apply, `Z` not being nowhere dense; there `Z` is open and closed
(`isOpenImmersion_of_coheight_eq_zero`) and (A1) gives the vanishing directly
(`cup_codimensionCycleClass_eq_zero_of_isOpenImmersion`). -/
@[stacks 0FII "for any smooth projective X and smooth closed Z all of whose irreducible \
components have codimension r, with [C_{Z/X}] restricted from K_0(X): a|_Z = 0 implies \
γ([Z]) ∪ a = 0, γ the cycle class map of 0FIF; the case r = 0 by (A1)"]
theorem cup_codimensionCycleClass_eq_zero (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA7 : 𝔇.BlowupAxiom)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    (r : ℕ)
    (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
      Order.coheight (i.hom.left z) = r)
    (hK : ∃ α : VectorBundleKZero X.obj.left,
      VectorBundleKZero.pullback i.hom.left α = VectorBundleKZero.classOf _ (centreConormal i))
    (a : 𝔇.H X) (ha : 𝔇.pull i a = 0) :
    tateCupLeft (𝔇.cup X) (r : ℤ) a
      (h.codimensionCycleClass X r (closedSubschemeClass X.obj.hom i.hom.left r)) = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have := isOpenImmersion_of_coheight_eq_zero i (fun z hz ↦ by simpa using hr z hz)
    exact h.cup_codimensionCycleClass_eq_zero_of_isOpenImmersion hA1 i a ha
  · exact (𝔇.tateCupLeft_eq_zero_iff X r _ a _).2
      (h.mul_κ_codimensionCycleClass_eq_zero_of_pos hA1 hA3 hA4 hA7 i r hr0 hr hK a ha)

/-- **Stacks Project, Lemma 0FII, in the source's order: `γ([Z]) ∪ a = 0`.** Here `γ([Z]) ∪ a` is
the cup product with the twisted class on the left, `tateCupLeft` of the flipped cup product. It
follows from `cup_codimensionCycleClass_eq_zero` by graded commutativity of `H^*(X)`, `γ([Z])`
having even degree `2r`. -/
@[stacks 0FII "in the source's order γ([Z]) ∪ a = 0, for any smooth projective X and smooth \
closed Z all of whose irreducible components have codimension r, with [C_{Z/X}] restricted from \
K_0(X), and a|_Z = 0; γ the cycle class map of 0FIF"]
theorem codimensionCycleClass_cup_eq_zero (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA7 : 𝔇.BlowupAxiom)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    (r : ℕ)
    (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
      Order.coheight (i.hom.left z) = r)
    (hK : ∃ α : VectorBundleKZero X.obj.left,
      VectorBundleKZero.pullback i.hom.left α = VectorBundleKZero.classOf _ (centreConormal i))
    (a : 𝔇.H X) (ha : 𝔇.pull i a = 0) :
    tateCupLeft (𝔇.cup X).flip (r : ℤ) a
      (h.codimensionCycleClass X r (closedSubschemeClass X.obj.hom i.hom.left r)) = 0 := by
  obtain ⟨y, hy⟩ := h.codimensionCycleClass_mem hA1 hA3 X r
    (closedSubschemeClass X.obj.hom i.hom.left r)
  rw [𝔇.tateCupLeft_eq_zero_iff]
  refine (𝔇.mul_comm_of_mem_grade_two_mul X r ?_ a).trans
    ((𝔇.tateCupLeft_eq_zero_iff X r _ a _).1
      (h.cup_codimensionCycleClass_eq_zero hA1 hA3 hA4 hA7 i r hr hK a ha))
  rw [← hy, κ, tateTwistCoordinates_map]
  exact Submodule.coe_mem _

end IsCohomologicalChernCharacter

end FirstChernClassData

end Stacks.WeilCohomology

end
