module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.RelativeOverBase

/-!
# Glueing immersions of finite presentation

Let `S` be a scheme, let `P` be a property of morphisms `T ⟶ S` (a subfunctor of the functor of
points of `S`) which is stable under precomposition and local on the source for the Zariski
topology, and let `S = ⋃ Uᵢ` be an open cover such that over each `Uᵢ` the restriction of `P` is
represented by an immersion of finite presentation `Zᵢ ⟶ Uᵢ`. Then `P` itself is represented by
an immersion of finite presentation `Z ⟶ S`.

## Main results

* `AlgebraicGeometry.Scheme.RelativeGlueData.toBase_iff_of_isZariskiLocalAtTarget`: a property
  local on the target holds for the structure morphism of a relative glueing datum iff it holds
  for the structure morphism of every piece.
* `AlgebraicGeometry.exists_isImmersion_represents_of_local`: a Zariski-local subfunctor of the
  functor of points of `S` which is locally on `S` represented by immersions of finite
  presentation is represented by an immersion of finite presentation.
* `AlgebraicGeometry.exists_isImmersion_represents_of_local_of_le`: the same, when the members of
  the cover only cover a quasi-compact open `G` of `S` through which every morphism satisfying
  the property factors.
* `AlgebraicGeometry.exists_lift_of_iSup_eq_top`: factoring through a monomorphism is local on
  the source.

## Implementation notes

The pieces `Zᵢ` are glued with `AlgebraicGeometry.Scheme.RelativeGlueData`. The transition
morphisms are produced from the representability of `P` over `Uⱼ`: the part of `Zᵢ` lying over
`Uⱼ` satisfies `P`, so it factors through `Zⱼ`. Every morphism in sight is a morphism over `S`
and every structure morphism `Zᵢ ⟶ S` is a monomorphism, so all the identities required of the
glueing datum are checked after composing to `S`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.RelativeGlueData

variable {S : Scheme.{u}} (D : RelativeGlueData S)

/-- A property of morphisms which is local on the target holds for the structure morphism of the
glued scheme of a relative glueing datum iff it holds for the structure morphism of every piece
to the corresponding member of the cover of the base. -/
theorem toBase_iff_of_isZariskiLocalAtTarget (Q : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget Q] : Q D.toBase ↔ ∀ i, Q (D.projRestrict i) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := Q) D.base D.iSup_base]
  refine forall_congr' fun i ↦ Q.arrow_mk_iso_iff ?_
  exact Arrow.isoMk ((isPullback_morphismRestrict D.toBase (D.base i)).isoIsPullback _ _
    (D.isPullback_projRestrict_ι i)) (Iso.refl _) (by simp [IsPullback.isoIsPullback_hom_fst])

end Scheme.RelativeGlueData

namespace ImmersionGlue

variable {S : Scheme.{u}} (P : ∀ {T : Scheme.{u}}, (T ⟶ S) → Prop)
  (hP_comp : ∀ {T T' : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ S), P g → P (h ≫ g))
  {ι : Type u} (U : ι → S.Opens) (Z : ∀ i, Over (U i : Scheme.{u}))
  (hZimm : ∀ i, IsImmersion (Z i).hom)
  (hZ : ∀ i {T : Scheme.{u}} (g : T ⟶ (U i : Scheme.{u})),
      (∃ h : T ⟶ (Z i).left, h ≫ (Z i).hom = g) ↔ P (g ≫ (U i).ι))

/-- The structure morphism `Zᵢ ⟶ S`. -/
abbrev proj (i : ι) : (Z i).left ⟶ S := (Z i).hom ≫ (U i).ι

/-- The part of `Zᵢ` lying over `Uⱼ`. -/
abbrev overlap (i j : ι) : (Z i).left.Opens := proj U Z i ⁻¹ᵁ U j

/-- A morphism landing in an open subscheme, as a morphism to that open subscheme. -/
def liftOpen {T Y : Scheme.{u}} (O : Y.Opens) (g : T ⟶ Y) (h : ∀ x, g x ∈ O) : T ⟶ O :=
  IsOpenImmersion.lift O.ι g (by rw [Scheme.Opens.range_ι]; rintro _ ⟨x, rfl⟩; exact h x)

/-- `AlgebraicGeometry.ImmersionGlue.liftOpen` is a lift. -/
@[reassoc (attr := simp)]
lemma liftOpen_ι {T Y : Scheme.{u}} (O : Y.Opens) (g : T ⟶ Y) (h : ∀ x, g x ∈ O) :
    liftOpen O g h ≫ O.ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- A point of an open subscheme lands, under a morphism, in an open containing the image of the
open. -/
lemma mem_of_comp {Y : Scheme.{u}} (O : Y.Opens) (f : Y ⟶ S) (V : S.Opens)
    (hO : ∀ y ∈ O, f y ∈ V) (x : O.toScheme) : (O.ι ≫ f) x ∈ V := by
  rw [Scheme.Hom.comp_apply]
  refine hO _ ?_
  rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
  exact ⟨x, rfl⟩

/-- Every point of `Zᵢ` lies over `Uᵢ`. -/
lemma proj_mem (i : ι) (x : (Z i).left) : proj U Z i x ∈ U i := by
  rw [Scheme.Hom.comp_apply]
  exact ((Z i).hom x).2

include hZ in
/-- The structure morphism `Zᵢ ⟶ S` satisfies `P`. -/
lemma P_proj (i : ι) : P (proj U Z i) := (hZ i (Z i).hom).1 ⟨𝟙 _, Category.id_comp _⟩

include hZ in
/-- A morphism satisfying `P` and landing in `Uⱼ` factors through `Zⱼ`. -/
lemma exists_lift (j : ι) {T : Scheme.{u}} (a : T ⟶ S) (ha : P a) (hr : ∀ t, a t ∈ U j) :
    ∃ h : T ⟶ (Z j).left, h ≫ proj U Z j = a := by
  obtain ⟨h, hh⟩ := (hZ j (liftOpen (U j) a hr)).2 (by rwa [liftOpen_ι])
  exact ⟨h, by rw [proj, ← Category.assoc, hh, liftOpen_ι]⟩

/-- A chosen factorization through `Zⱼ` of a morphism satisfying `P` and landing in `Uⱼ`. -/
def liftTo (j : ι) {T : Scheme.{u}} (a : T ⟶ S) (ha : P a) (hr : ∀ t, a t ∈ U j) :
    T ⟶ (Z j).left :=
  (exists_lift P U Z hZ j a ha hr).choose

/-- `AlgebraicGeometry.ImmersionGlue.liftTo` is a factorization. -/
@[reassoc (attr := simp)]
lemma liftTo_proj (j : ι) {T : Scheme.{u}} (a : T ⟶ S) (ha : P a) (hr : ∀ t, a t ∈ U j) :
    liftTo P U Z hZ j a ha hr ≫ proj U Z j = a :=
  (exists_lift P U Z hZ j a ha hr).choose_spec

/-- The transition morphism from the part of `Zᵢ` over `Uⱼ` to the part of `Zⱼ` over `Uᵢ`. -/
def trans (i j : ι) : (overlap U Z i j).toScheme ⟶ (overlap U Z j i).toScheme :=
  liftOpen _ (liftTo P U Z hZ j ((overlap U Z i j).ι ≫ proj U Z i)
      (hP_comp _ _ (P_proj P U Z hZ i)) (mem_of_comp _ _ _ fun _ hy ↦ hy)) fun x ↦ by
    change proj U Z j _ ∈ U i
    rw [← Scheme.Hom.comp_apply, liftTo_proj]
    exact mem_of_comp _ _ _ (fun y _ ↦ proj_mem U Z i y) x

/-- The transition morphisms are morphisms over `S`. -/
@[reassoc (attr := simp)]
lemma trans_over (i j : ι) :
    trans P hP_comp U Z hZ i j ≫ (overlap U Z j i).ι ≫ proj U Z j =
      (overlap U Z i j).ι ≫ proj U Z i := by
  simp [trans]

/-- The transition morphism on triple overlaps. -/
def trans' (i j k : ι) : (overlap U Z i j ⊓ overlap U Z i k).toScheme ⟶
    (overlap U Z j k ⊓ overlap U Z j i).toScheme :=
  liftOpen _ ((Z i).left.homOfLE inf_le_left ≫ trans P hP_comp U Z hZ i j ≫
      (overlap U Z j i).ι) fun x ↦ by
    have h : ((Z i).left.homOfLE inf_le_left ≫ trans P hP_comp U Z hZ i j ≫
        (overlap U Z j i).ι) ≫ proj U Z j =
          (overlap U Z i j ⊓ overlap U Z i k).ι ≫ proj U Z i := by
      simp only [Category.assoc, trans_over, Scheme.homOfLE_ι_assoc]
    refine ⟨?_, ?_⟩
    · change proj U Z j _ ∈ U k
      rw [← Scheme.Hom.comp_apply, h]
      exact mem_of_comp _ _ _ (fun _ (hy : _ ∈ overlap U Z i j ⊓ overlap U Z i k) ↦ hy.2) x
    · change proj U Z j _ ∈ U i
      rw [← Scheme.Hom.comp_apply, h]
      exact mem_of_comp _ _ _ (fun y _ ↦ proj_mem U Z i y) x

/-- The transition morphisms on triple overlaps are morphisms over `S`. -/
@[reassoc (attr := simp)]
lemma trans'_over (i j k : ι) :
    trans' P hP_comp U Z hZ i j k ≫ (overlap U Z j k ⊓ overlap U Z j i).ι ≫ proj U Z j =
      (overlap U Z i j ⊓ overlap U Z i k).ι ≫ proj U Z i := by
  simp only [trans', liftOpen_ι_assoc, Category.assoc, trans_over, Scheme.homOfLE_ι_assoc]

include hZimm in
/-- The composite of an open immersion into `Zᵢ` with `Zᵢ ⟶ S` is a monomorphism. -/
lemma mono_ι_proj (i : ι) (O : (Z i).left.Opens) : Mono (O.ι ≫ proj U Z i) := by
  have := hZimm i
  infer_instance

/-- The relative glueing datum gluing the `Zᵢ`. -/
@[implicit_reducible] def glueData (hU : ⨆ i, U i = ⊤) : Scheme.RelativeGlueData S where
  J := ι
  base := U
  iSup_base := hU
  obj i := (Z i).left
  proj := proj U Z
  proj_preimage_eq_top i := top_unique fun x _ ↦ proj_mem U Z i x
  t := trans P hP_comp U Z hZ
  t_over := trans_over P hP_comp U Z hZ
  t_self i := by
    have := mono_ι_proj U Z hZimm i (overlap U Z i i)
    rw [← cancel_mono ((overlap U Z i i).ι ≫ proj U Z i)]
    simp only [trans_over, Category.id_comp]
  t' := trans' P hP_comp U Z hZ
  t'_fac i j k := by
    rw [← cancel_mono (overlap U Z j i).ι]
    simp only [trans', Category.assoc, Scheme.homOfLE_ι, liftOpen_ι]
  cocycle i j k := by
    have := mono_ι_proj U Z hZimm i (overlap U Z i j ⊓ overlap U Z i k)
    rw [← cancel_mono ((overlap U Z i j ⊓ overlap U Z i k).ι ≫ proj U Z i)]
    simp only [Category.assoc, trans'_over, Category.id_comp]

end ImmersionGlue


/-- Factoring through a monomorphism is local on the source (private copy used internally). -/
private theorem exists_lift_of_cover {T Y W : Scheme.{u}} (j : W ⟶ Y) [Mono j] (g : T ⟶ Y)
    {κ : Type u} (V : κ → T.Opens) (hV : (⨆ k, V k) = ⊤)
    (h : ∀ k, ∃ l : (V k : Scheme.{u}) ⟶ W, l ≫ j = (V k).ι ≫ g) :
    ∃ l : T ⟶ W, l ≫ j = g := by
  choose l hl using h
  let 𝒰 := T.openCoverOfIsOpenCover V hV
  have hcompat (x y : κ) :
      pullback.fst (V x).ι (V y).ι ≫ l x = pullback.snd (V x).ι (V y).ι ≫ l y := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hl, hl, pullback.condition_assoc]
  exact ⟨𝒰.glueMorphisms l hcompat, 𝒰.hom_ext _ _ fun k ↦
    (Scheme.Cover.ι_glueMorphisms_assoc 𝒰 l hcompat k _).trans (hl k)⟩

open ImmersionGlue in
/-- A subfunctor `P` of the functor of points of `S` which is Zariski-local on the source and
which, over the members of an open cover `S = ⋃ Uᵢ`, is represented by immersions of finite
presentation `Zᵢ ⟶ Uᵢ`, is represented by an immersion of finite presentation `Z ⟶ S`. -/
theorem exists_isImmersion_represents_of_local {S : Scheme.{u}}
    (P : ∀ {T : Scheme.{u}}, (T ⟶ S) → Prop)
    (hP_comp : ∀ {T T' : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ S), P g → P (h ≫ g))
    (hP_local : ∀ {T : Scheme.{u}} (g : T ⟶ S) {κ : Type u} (V : κ → T.Opens),
      (⨆ k, V k) = ⊤ → (∀ k, P ((V k).ι ≫ g)) → P g)
    {ι : Type u} (U : ι → S.Opens) (Z : ∀ i, Over (U i : Scheme.{u}))
    (hZimm : ∀ i, IsImmersion (Z i).hom) (hZfp : ∀ i, FinitePresentation (Z i).hom)
    (hZ : ∀ i {T : Scheme.{u}} (g : T ⟶ (U i : Scheme.{u})),
      (∃ h : T ⟶ (Z i).left, h ≫ (Z i).hom = g) ↔ P (g ≫ (U i).ι))
    (hU : (⨆ i, U i) = ⊤) :
    ∃ Z : Over S, IsImmersion Z.hom ∧ FinitePresentation Z.hom ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S), (∃ h : T ⟶ Z.left, h ≫ Z.hom = g) ↔ P g := by
  let D := glueData P hP_comp U Z (hZimm := hZimm) (hZ := hZ) hU
  have hres (i : ι) : D.projRestrict i = (Z i).hom := by
    rw [← cancel_mono (U i).ι]
    exact D.projRestrict_ι i
  have hloc (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
      (hQ : ∀ i, Q (Z i).hom) : Q D.toBase :=
    (D.toBase_iff_of_isZariskiLocalAtTarget Q).2 fun i ↦ by rw [hres]; exact hQ i
  have himm : IsImmersion D.toBase := hloc @IsImmersion hZimm
  have : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation)
      (Q := RingHom.FinitePresentation)
  have : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  have : IsZariskiLocalAtTarget (@QuasiSeparated : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
  have hfp : FinitePresentation D.toBase :=
    ⟨hloc @LocallyOfFinitePresentation fun i ↦ (hZfp i).1,
      hloc @QuasiCompact fun i ↦ (hZfp i).2.1, hloc @QuasiSeparated fun i ↦ (hZfp i).2.2⟩
  have hPπ : P D.toBase := by
    refine hP_local D.toBase (fun i ↦ D.toBase ⁻¹ᵁ U i) (D.toBase.iSup_preimage_eq_top hU)
      fun i ↦ ?_
    have hr : Set.range (D.toBase ⁻¹ᵁ U i).ι ⊆ Set.range (D.ι i) := by
      rw [Scheme.Opens.range_ι, ← D.toBase_preimage_eq_range_ι]
      rfl
    rw [← IsOpenImmersion.lift_fac (D.ι i) _ hr, Category.assoc,
      Scheme.RelativeGlueData.ι_toBase]
    exact hP_comp _ _ (P_proj P U Z hZ i)
  refine ⟨Over.mk D.toBase, himm, hfp, fun {T} g ↦ ⟨?_, fun hg ↦ ?_⟩⟩
  · rintro ⟨h, rfl⟩
    exact hP_comp h _ hPπ
  · have := himm
    exact exists_lift_of_cover D.toBase g (fun i ↦ g ⁻¹ᵁ U i) (g.iSup_preimage_eq_top hU) fun i ↦
      ⟨liftTo P U Z hZ i ((g ⁻¹ᵁ U i).ι ≫ g) (hP_comp _ _ hg)
        (mem_of_comp (g ⁻¹ᵁ U i) g (U i) fun _ hy ↦ hy) ≫ D.ι i, by
          rw [Category.assoc, Scheme.RelativeGlueData.ι_toBase]
          exact liftTo_proj P U Z hZ i _ _ _⟩

/-- **Factoring through a monomorphism is local on the source.** If `g : T ⟶ Y` factors through
the monomorphism `j : W ⟶ Y` on each member of an open cover of `T`, then it factors through `j`.
-/
theorem exists_lift_of_iSup_eq_top {T Y W : Scheme.{u}} (j : W ⟶ Y) [Mono j] (g : T ⟶ Y)
    {κ : Type u} (V : κ → T.Opens) (hV : (⨆ k, V k) = ⊤)
    (h : ∀ k, ∃ l : (V k : Scheme.{u}) ⟶ W, l ≫ j = (V k).ι ≫ g) :
    ∃ l : T ⟶ W, l ≫ j = g := by
  exact exists_lift_of_cover j g V hV h

/-- A variant of `AlgebraicGeometry.exists_isImmersion_represents_of_local` in which the members
of the cover only cover a quasi-compact open `G` of `S` through which every morphism satisfying
`P` factors: then `P` is still represented by an immersion of finite presentation. -/
theorem exists_isImmersion_represents_of_local_of_le {S : Scheme.{u}}
    (P : ∀ {T : Scheme.{u}}, (T ⟶ S) → Prop)
    (hP_comp : ∀ {T T' : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ S), P g → P (h ≫ g))
    (hP_local : ∀ {T : Scheme.{u}} (g : T ⟶ S) {κ : Type u} (V : κ → T.Opens),
      (⨆ k, V k) = ⊤ → (∀ k, P ((V k).ι ≫ g)) → P g)
    (G : S.Opens) (hG : QuasiCompact G.ι)
    (hPG : ∀ {T : Scheme.{u}} (g : T ⟶ S), P g → Set.range g ⊆ G)
    {ι : Type u} (U : ι → S.Opens) (hUG : ∀ i, U i ≤ G) (Z : ∀ i, Over (U i : Scheme.{u}))
    (hZimm : ∀ i, IsImmersion (Z i).hom) (hZfp : ∀ i, FinitePresentation (Z i).hom)
    (hZ : ∀ i {T : Scheme.{u}} (g : T ⟶ (U i : Scheme.{u})),
      (∃ h : T ⟶ (Z i).left, h ≫ (Z i).hom = g) ↔ P (g ≫ (U i).ι))
    (hU : (⨆ i, U i) = G) :
    ∃ Z : Over S, IsImmersion Z.hom ∧ FinitePresentation Z.hom ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S), (∃ h : T ⟶ Z.left, h ≫ Z.hom = g) ↔ P g := by
  let U' (i : ι) : (G : Scheme.{u}).Opens := G.ι ⁻¹ᵁ U i
  have hrange (i : ι) : Set.range ((U' i).ι ≫ G.ι) = Set.range (U i).ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ hy, fun hx ↦ ⟨⟨x, hUG i hx⟩, hx, rfl⟩⟩
  let e (i : ι) : (U' i : Scheme.{u}) ≅ (U i : Scheme.{u}) :=
    IsOpenImmersion.isoOfRangeEq _ _ (hrange i)
  have he (i : ι) : (e i).hom ≫ (U i).ι = (U' i).ι ≫ G.ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (hrange i)
  let Z' (i : ι) : Over (U' i : Scheme.{u}) := Over.mk ((Z i).hom ≫ (e i).inv)
  have hZ'imm (i : ι) : IsImmersion (Z' i).hom := by
    have := hZimm i
    exact inferInstanceAs (IsImmersion ((Z i).hom ≫ (e i).inv))
  have hZ'fp (i : ι) : FinitePresentation (Z' i).hom := by
    obtain ⟨h₁, h₂, h₃⟩ := hZfp i
    exact ⟨inferInstanceAs (LocallyOfFinitePresentation ((Z i).hom ≫ (e i).inv)),
      inferInstanceAs (QuasiCompact ((Z i).hom ≫ (e i).inv)),
      inferInstanceAs (QuasiSeparated ((Z i).hom ≫ (e i).inv))⟩
  have hZ' (i : ι) {T : Scheme.{u}} (g : T ⟶ (U' i : Scheme.{u})) :
      (∃ h : T ⟶ (Z' i).left, h ≫ (Z' i).hom = g) ↔ P ((g ≫ (U' i).ι) ≫ G.ι) := by
    rw [Category.assoc, ← he, ← Category.assoc, ← hZ i]
    refine ⟨fun ⟨h, hh⟩ ↦ ⟨h, ?_⟩, fun ⟨h, hh⟩ ↦ ⟨h, ?_⟩⟩
    · rw [← hh]
      simp [Z']
    · simp [Z', ← Category.assoc, hh]
      simp
  have hU' : (⨆ i, U' i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU]
    exact top_unique fun x _ ↦ x.2
  obtain ⟨Z₀, himm, hfp, hrep⟩ := exists_isImmersion_represents_of_local
    (fun g ↦ P (g ≫ G.ι)) (fun h g hg ↦ by rw [Category.assoc]; exact hP_comp h _ hg)
    (fun g κ V hV hk ↦ hP_local (g ≫ G.ι) V hV fun k ↦ by rw [← Category.assoc]; exact hk k)
    U' Z' hZ'imm hZ'fp hZ' hU'
  obtain ⟨h₁, h₂, h₃⟩ := hfp
  refine ⟨Over.mk (Z₀.hom ≫ G.ι), inferInstanceAs (IsImmersion (Z₀.hom ≫ G.ι)),
    ⟨inferInstanceAs (LocallyOfFinitePresentation (Z₀.hom ≫ G.ι)),
      inferInstanceAs (QuasiCompact (Z₀.hom ≫ G.ι)),
      inferInstanceAs (QuasiSeparated (Z₀.hom ≫ G.ι))⟩, fun {T} g ↦ ⟨?_, fun hg ↦ ?_⟩⟩
  · rintro ⟨h, rfl⟩
    have := (hrep (h ≫ Z₀.hom)).1 ⟨h, rfl⟩
    simpa using this
  · have hr : Set.range g ⊆ Set.range G.ι := by rw [Scheme.Opens.range_ι]; exact hPG g hg
    obtain ⟨h, hh⟩ := (hrep (IsOpenImmersion.lift G.ι g hr)).2 (by rwa [IsOpenImmersion.lift_fac])
    exact ⟨h, by simp [← Category.assoc, hh, IsOpenImmersion.lift_fac]⟩

end AlgebraicGeometry
