module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Shrink
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.PairAgreement

/-!
# Charts of pulled-back sections on a scheme over the base

Let `F` be a sheaf on the small étale site of `X`, `s j` sections of `F` over objects `W j` of
that site, and `φ : Y ⟶ X` a morphism of schemes. A **chart** on `Y` is an open `D` of `Y`
together with a morphism `D ⟶ W j` over `X`: a way of pulling one of the sections back to `D`.
Two charts **agree at a point** `y` of both domains when the pulled-back sections agree there in
the sense of `Stacks.EtaleCohomology.PairAgree`.

The surjectivity half of [Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF) handles
a section of the inverse image of `F` to a scheme finite over `X` as a family of such charts
which agree on their overlaps. This file supplies the bookkeeping: agreement of charts is an
equivalence relation on the charts defined at a point, it is pulled back along morphisms of
schemes and restricted to smaller opens, the points where two charts agree form an open, and two
charts whose morphisms coincide on the overlap agree there.

## Main definitions

* `Stacks.EtaleCohomology.EtaleChart` — a chart on `Y` over `φ`.
* `Stacks.EtaleCohomology.EtaleChart.Agree` — agreement of two charts at a point.
* `Stacks.EtaleCohomology.EtaleChart.agreeOpens` — the open where two charts agree.
* `Stacks.EtaleCohomology.EtaleChart.pullback`, `EtaleChart.restrict`, `EtaleChart.ofEq`,
  `EtaleChart.ofHom` — pulling a chart back along a morphism of schemes, restricting it to a
  smaller open, transporting it along an equality of structure morphisms, and the chart with the
  whole of `Y` as domain given by a single morphism.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe u v w

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}} {α : Type*} (W : α → X.Etale)

/-- A **chart** on a scheme `Y` over `X`: an open `dom` of `Y` with a morphism over `X` to one of
the objects `W idx`. -/
public structure EtaleChart {Y : Scheme.{u}} (φ : Y ⟶ X) where
  /-- The domain of the chart. -/
  dom : Y.Opens
  /-- The index of the object of the small étale site the chart maps to. -/
  idx : α
  /-- The morphism of the chart. -/
  hom : dom.toScheme ⟶ (W idx).left
  /-- The morphism of the chart lies over `X`. -/
  w : hom ≫ ((W idx).hom : (W idx).left ⟶ X) = dom.ι ≫ φ

variable {W}

namespace EtaleChart

variable {Y : Scheme.{u}} {φ : Y ⟶ X}

/-- A chart restricted to an open `V` inside its domain still lies over `φ`. -/
private theorem homOfLE_hom_comp_eq (c : EtaleChart W φ) {V : Y.Opens} (hV : V ≤ c.dom) :
    (Y.homOfLE hV ≫ c.hom) ≫ ((W c.idx).hom : (W c.idx).left ⟶ X) = V.ι ≫ φ := by
  rw [Category.assoc, c.w, Scheme.homOfLE_ι_assoc]

/-- The two morphisms of a pair of charts, restricted to the intersection of their domains, lie
over the same morphism to `X`. -/
public theorem w_inf (c c' : EtaleChart W φ) :
    (Y.homOfLE (inf_le_left : c.dom ⊓ c'.dom ≤ c.dom) ≫ c.hom) ≫
        ((W c.idx).hom : (W c.idx).left ⟶ X) =
      (Y.homOfLE (inf_le_right : c.dom ⊓ c'.dom ≤ c'.dom) ≫ c'.hom) ≫
        ((W c'.idx).hom : (W c'.idx).left ⟶ X) := by
  rw [homOfLE_hom_comp_eq, homOfLE_hom_comp_eq]

variable (F : Sheaf (Scheme.smallEtaleTopology X) (Type w)) (s : ∀ j, F.obj.obj (op (W j)))

/-- Two charts **agree at the point `y`** when `y` lies in both domains and the two pulled-back
sections agree at `y`. -/
public def Agree (c c' : EtaleChart W φ) (y : Y) : Prop :=
  ∃ hy : y ∈ c.dom ⊓ c'.dom,
    PairAgree F W s (Y.homOfLE (inf_le_left : c.dom ⊓ c'.dom ≤ c.dom) ≫ c.hom)
      (Y.homOfLE (inf_le_right : c.dom ⊓ c'.dom ≤ c'.dom) ≫ c'.hom) (w_inf c c') ⟨y, hy⟩

variable {F s}

/-- Agreement only depends on the morphisms, not on the proof that they lie over `X`. -/
public theorem _root_.Stacks.EtaleCohomology.PairAgree.congr {Q : Scheme.{u}} {j j' : α}
    {G₁ G₂ : Q ⟶ (W j).left} {G₁' G₂' : Q ⟶ (W j').left} {hG₁ hG₂} {q : Q}
    (e : G₁ = G₂) (e' : G₁' = G₂') (h : PairAgree F W s G₁ G₁' hG₁ q) :
    PairAgree F W s G₂ G₂' hG₂ q := by
  subst e e'
  exact h

/-- **Agreement read on a smaller open.** On an open `V` contained in both domains, two charts
agree at a point of `V` exactly when their restrictions to `V` give agreeing pulled-back
sections there. -/
public theorem agree_iff_of_le (c c' : EtaleChart W φ) {V : Y.Opens} (hV : V ≤ c.dom ⊓ c'.dom)
    {y : Y} (hy : y ∈ V) :
    c.Agree F s c' y ↔
      PairAgree F W s (Y.homOfLE (hV.trans inf_le_left) ≫ c.hom)
        (Y.homOfLE (hV.trans inf_le_right) ≫ c'.hom)
        (by rw [Category.assoc, Category.assoc, c.w, c'.w, Scheme.homOfLE_ι_assoc,
          Scheme.homOfLE_ι_assoc]) ⟨y, hy⟩ := by
  have e : Y.homOfLE hV ≫ Y.homOfLE inf_le_left ≫ c.hom =
      Y.homOfLE (hV.trans inf_le_left) ≫ c.hom :=
    Scheme.homOfLE_homOfLE_assoc ..
  have e' : Y.homOfLE hV ≫ Y.homOfLE inf_le_right ≫ c'.hom =
      Y.homOfLE (hV.trans inf_le_right) ≫ c'.hom :=
    Scheme.homOfLE_homOfLE_assoc ..
  have hpt : (Y.homOfLE hV).base ⟨y, hy⟩ = ⟨y, hV hy⟩ := Scheme.homOfLE_apply' hV y hy
  exact ⟨fun ⟨_, h⟩ ↦ pairAgree_of_comp (Y.homOfLE hV) (w_inf c c') _ e e' hpt h,
    fun h ↦ ⟨hV hy, pairAgree_of_comp' (Y.homOfLE hV) (w_inf c c') _ e e' hpt h⟩⟩

/-- **Charts with the same morphism near a point agree there.** A chart `c` agrees at `y` with a
chart with the same index whose morphism coincides with that of `c` on an open neighbourhood of
`y`. -/
public theorem agree_of_hom_eq (c : EtaleChart W φ) {V : Y.Opens}
    (H : V.toScheme ⟶ (W c.idx).left)
    (hw : H ≫ ((W c.idx).hom : (W c.idx).left ⟶ X) = V.ι ≫ φ) {U : Y.Opens}
    (hU : U ≤ c.dom ⊓ V)
    (hH : Y.homOfLE (hU.trans inf_le_left) ≫ c.hom = Y.homOfLE (hU.trans inf_le_right) ≫ H)
    {y : Y} (hy : y ∈ U) :
    c.Agree F s ⟨V, c.idx, H, hw⟩ y :=
  (agree_iff_of_le c ⟨V, c.idx, H, hw⟩ hU hy).2 ((pairAgree_refl _ _).congr rfl hH)

/-- The points where two charts agree form an open. -/
public theorem isOpen_setOf_agree (c c' : EtaleChart W φ) :
    IsOpen {y | c.Agree F s c' y} := by
  have hset : {y | c.Agree F s c' y} = (c.dom ⊓ c'.dom).ι.base ''
      {z | PairAgree F W s (Y.homOfLE (inf_le_left : c.dom ⊓ c'.dom ≤ c.dom) ≫ c.hom)
        (Y.homOfLE (inf_le_right : c.dom ⊓ c'.dom ≤ c'.dom) ≫ c'.hom) (w_inf c c') z} := by
    ext y
    refine ⟨fun ⟨hy, h⟩ ↦ ⟨⟨y, hy⟩, h, rfl⟩, ?_⟩
    rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  rw [hset]
  exact (c.dom ⊓ c'.dom).ι.isOpenEmbedding.isOpenMap _ (isOpen_setOf_pairAgree _ _ _)

variable (F s) in
/-- The open of `Y` where two charts agree. -/
public def agreeOpens (c c' : EtaleChart W φ) : Y.Opens :=
  ⟨{y | c.Agree F s c' y}, isOpen_setOf_agree c c'⟩

/-- A point lies in `agreeOpens F s c c'` if and only if the charts `c` and `c'` agree there. -/
@[simp]
public theorem mem_agreeOpens {c c' : EtaleChart W φ} {y : Y} :
    y ∈ agreeOpens F s c c' ↔ c.Agree F s c' y := Iff.rfl

/-- Agreement happens only on the domains. -/
public theorem Agree.mem {c c' : EtaleChart W φ} {y : Y} (h : c.Agree F s c' y) :
    y ∈ c.dom ⊓ c'.dom :=
  h.1

/-- **Reflexivity.** -/
public theorem agree_refl (c : EtaleChart W φ) {y : Y} (hy : y ∈ c.dom) : c.Agree F s c y :=
  ⟨⟨hy, hy⟩, pairAgree_refl _ _⟩

/-- **Symmetry.** -/
public theorem Agree.symm {c c' : EtaleChart W φ} {y : Y} (h : c.Agree F s c' y) :
    c'.Agree F s c y :=
  (agree_iff_of_le c' c (inf_comm c.dom c'.dom).le h.1).2 h.2.symm

/-- **Transitivity.** -/
public theorem Agree.trans {c₁ c₂ c₃ : EtaleChart W φ} {y : Y} (h₁₂ : c₁.Agree F s c₂ y)
    (h₂₃ : c₂.Agree F s c₃ y) : c₁.Agree F s c₃ y := by
  have hy : y ∈ c₁.dom ⊓ c₂.dom ⊓ c₃.dom := ⟨h₁₂.1, h₂₃.1.2⟩
  have hV₂₃ : c₁.dom ⊓ c₂.dom ⊓ c₃.dom ≤ c₂.dom ⊓ c₃.dom :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hV₁₃ : c₁.dom ⊓ c₂.dom ⊓ c₃.dom ≤ c₁.dom ⊓ c₃.dom :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  exact (agree_iff_of_le c₁ c₃ hV₁₃ hy).2 (((agree_iff_of_le c₁ c₂ inf_le_left hy).1 h₁₂).trans _
    ((agree_iff_of_le c₂ c₃ hV₂₃ hy).1 h₂₃))

/-- **Charts agree over the image of `i`**, when the sections they pull back all cut out one
global section of `i^{-1}F`. -/
public theorem agree_of_mem_range {Z : Scheme.{u}} (i : Z ⟶ X)
    {F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v))}
    {s : ∀ j, F.obj.obj (op (W j))}
    (t : ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op (terminal Z.Etale)))
    (ht : ∀ j, ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
          (terminal.from ((smallEtaleBaseChange i).obj (W j))).op t
        = smallEtaleSectionPullback.{u, v} i F (W j) (s j))
    (c c' : EtaleChart W φ) {y : Y} (hy : y ∈ c.dom ⊓ c'.dom)
    (hφ : φ.base y ∈ Set.range i.base) : c.Agree F s c' y := by
  refine ⟨hy, pairAgree_of_mem_range.{u, v} i F W s t ht _ _ _ _ ?_⟩
  rwa [homOfLE_hom_comp_eq]

/-- The pullback of a chart along a morphism of schemes `ψ : Y' ⟶ Y`. -/
public def pullback {Y' : Scheme.{u}} (ψ : Y' ⟶ Y) (c : EtaleChart W φ) :
    EtaleChart W (ψ ≫ φ) where
  dom := ψ ⁻¹ᵁ c.dom
  idx := c.idx
  hom := ψ.resLE c.dom (ψ ⁻¹ᵁ c.dom) le_rfl ≫ c.hom
  w := by rw [Category.assoc, c.w, Scheme.Hom.resLE_comp_ι_assoc]

/-- **Agreement is pulled back.** -/
public theorem agree_pullback_iff {Y' : Scheme.{u}} (ψ : Y' ⟶ Y) (c c' : EtaleChart W φ)
    (y' : Y') :
    (c.pullback ψ).Agree F s (c'.pullback ψ) y' ↔ c.Agree F s c' (ψ.base y') := by
  have hle : ψ ⁻¹ᵁ c.dom ⊓ ψ ⁻¹ᵁ c'.dom ≤ ψ ⁻¹ᵁ (c.dom ⊓ c'.dom) := fun _ h ↦ h
  set ρ := ψ.resLE (c.dom ⊓ c'.dom) (ψ ⁻¹ᵁ c.dom ⊓ ψ ⁻¹ᵁ c'.dom) hle
  have k : ρ ≫ Y.homOfLE (inf_le_left : c.dom ⊓ c'.dom ≤ c.dom) =
      Y'.homOfLE (inf_le_left : ψ ⁻¹ᵁ c.dom ⊓ ψ ⁻¹ᵁ c'.dom ≤ _) ≫
        ψ.resLE c.dom (ψ ⁻¹ᵁ c.dom) le_rfl := by
    rw [← cancel_mono c.dom.ι]
    simp [ρ]
  have k' : ρ ≫ Y.homOfLE (inf_le_right : c.dom ⊓ c'.dom ≤ c'.dom) =
      Y'.homOfLE (inf_le_right : ψ ⁻¹ᵁ c.dom ⊓ ψ ⁻¹ᵁ c'.dom ≤ _) ≫
        ψ.resLE c'.dom (ψ ⁻¹ᵁ c'.dom) le_rfl := by
    rw [← cancel_mono c'.dom.ι]
    simp [ρ]
  have e : ρ ≫ Y.homOfLE inf_le_left ≫ c.hom =
      Y'.homOfLE (inf_le_left : (c.pullback ψ).dom ⊓ (c'.pullback ψ).dom ≤ _) ≫
        (c.pullback ψ).hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c.hom) k).trans (Category.assoc _ _ _))
  have e' : ρ ≫ Y.homOfLE inf_le_right ≫ c'.hom =
      Y'.homOfLE (inf_le_right : (c.pullback ψ).dom ⊓ (c'.pullback ψ).dom ≤ _) ≫
        (c'.pullback ψ).hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c'.hom) k').trans (Category.assoc _ _ _))
  have hpt : ∀ hy : y' ∈ ψ ⁻¹ᵁ c.dom ⊓ ψ ⁻¹ᵁ c'.dom,
      ρ.base ⟨y', hy⟩ = ⟨ψ.base y', hy⟩ := fun hy ↦
    Subtype.ext (Scheme.Hom.coe_resLE_apply ψ hle ⟨y', hy⟩)
  exact ⟨fun ⟨hy, h⟩ ↦ ⟨hy, pairAgree_of_comp' ρ (w_inf c c') _ e e' (hpt hy) h⟩,
    fun ⟨hy, h⟩ ↦ ⟨hy, pairAgree_of_comp ρ (w_inf c c') _ e e' (hpt hy) h⟩⟩

/-- The restriction of a chart to a smaller open. -/
public def restrict (c : EtaleChart W φ) {V : Y.Opens} (hV : V ≤ c.dom) : EtaleChart W φ where
  dom := V
  idx := c.idx
  hom := Y.homOfLE hV ≫ c.hom
  w := by rw [Category.assoc, c.w, Scheme.homOfLE_ι_assoc]

/-- **Agreement of restrictions** is agreement on the smaller opens. -/
public theorem agree_restrict_iff (c c' : EtaleChart W φ) {V V' : Y.Opens} (hV : V ≤ c.dom)
    (hV' : V' ≤ c'.dom) {y : Y} :
    (c.restrict hV).Agree F s (c'.restrict hV') y ↔ y ∈ V ∧ y ∈ V' ∧ c.Agree F s c' y := by
  have hle : V ⊓ V' ≤ c.dom ⊓ c'.dom := inf_le_inf hV hV'
  exact ⟨fun ⟨hy, h⟩ ↦ ⟨hy.1, hy.2, (agree_iff_of_le c c' hle hy).2 <|
      h.congr (Scheme.homOfLE_homOfLE_assoc ..) (Scheme.homOfLE_homOfLE_assoc ..)⟩,
    fun ⟨hy, hy', h⟩ ↦ ⟨⟨hy, hy'⟩, ((agree_iff_of_le c c' hle ⟨hy, hy'⟩).1 h).congr
      (Scheme.homOfLE_homOfLE_assoc ..).symm (Scheme.homOfLE_homOfLE_assoc ..).symm⟩⟩

/-- A chart transported along an equality of structure morphisms to `X`. -/
public def ofEq (c : EtaleChart W φ) {φ' : Y ⟶ X} (h : φ = φ') : EtaleChart W φ' where
  dom := c.dom
  idx := c.idx
  hom := c.hom
  w := h ▸ c.w

/-- Two charts transported along the same equality of structure morphisms agree at a point if
and only if the original charts do. -/
@[simp]
public theorem agree_ofEq_iff (c c' : EtaleChart W φ) {φ' : Y ⟶ X} (h : φ = φ') (y : Y) :
    (c.ofEq h).Agree F s (c'.ofEq h) y ↔ c.Agree F s c' y := Iff.rfl

/-- The chart with domain all of `Y` given by a single morphism `Y ⟶ W j` over `X`. -/
public def ofHom {j : α} (H : Y ⟶ (W j).left) (hH : H ≫ ((W j).hom : (W j).left ⟶ X) = φ) :
    EtaleChart W φ where
  dom := ⊤
  idx := j
  hom := (⊤ : Y.Opens).ι ≫ H
  w := by rw [Category.assoc, hH]

/-- **Charts with the same morphism agree.** A chart agrees, at every point of its domain, with
any chart defined by a global morphism restricting to its own. -/
public theorem agree_ofHom (c : EtaleChart W φ) (H : Y ⟶ (W c.idx).left)
    (hH : H ≫ ((W c.idx).hom : (W c.idx).left ⟶ X) = φ) (hc : c.hom = c.dom.ι ≫ H) {y : Y}
    (hy : y ∈ c.dom) : c.Agree F s (ofHom H hH) y := by
  refine ⟨⟨hy, trivial⟩, (pairAgree_refl (F := F) (s := s) (W := W)
    ((c.dom ⊓ (⊤ : Y.Opens)).ι ≫ H) _).congr ?_ ?_⟩
  · exact (Scheme.homOfLE_ι_assoc _ _ _).symm.trans (congrArg (Y.homOfLE _ ≫ ·) hc.symm)
  · exact (Scheme.homOfLE_ι_assoc _ _ _).symm

/-- Agreement of two global charts is agreement of their morphisms. -/
public theorem agree_ofHom_ofHom_iff {j j' : α} (H : Y ⟶ (W j).left) (H' : Y ⟶ (W j').left)
    (hH : H ≫ ((W j).hom : (W j).left ⟶ X) = φ) (hH' : H' ≫ ((W j').hom : (W j').left ⟶ X) = φ)
    (y : Y) :
    (ofHom H hH).Agree F s (ofHom H' hH') y ↔ PairAgree F W s H H' (hH.trans hH'.symm) y := by
  set D : Y.Opens := (ofHom H hH).dom ⊓ (ofHom H' hH').dom
  have e : D.ι ≫ H = Y.homOfLE (inf_le_left : D ≤ _) ≫ (ofHom H hH).hom :=
    (Scheme.homOfLE_ι_assoc _ _ _).symm
  have e' : D.ι ≫ H' = Y.homOfLE (inf_le_right : D ≤ _) ≫ (ofHom H' hH').hom :=
    (Scheme.homOfLE_ι_assoc _ _ _).symm
  have hy : y ∈ D := ⟨trivial, trivial⟩
  have key := pairAgree_comp_iff (F := F) (s := s) D.ι (G := H) (G' := H')
    (hH.trans hH'.symm)
    ((Category.assoc _ _ _).trans ((congrArg (D.ι ≫ ·) (hH.trans hH'.symm)).trans
      (Category.assoc _ _ _).symm)) ⟨y, hy⟩
  exact ⟨fun ⟨_, h⟩ ↦ key.1 (h.congr e.symm e'.symm), fun h ↦ ⟨hy, (key.2 h).congr e e'⟩⟩

/-- **Pulling back twice is pulling back along the composite**: the two charts agree at every
point of the domain, whatever common morphism to `X` they are transported to. -/
public theorem agree_pullback_comp (c : EtaleChart W φ) {Y' Y'' : Scheme.{u}} (ψ : Y' ⟶ Y)
    (ψ' : Y'' ⟶ Y') {φ'' : Y'' ⟶ X} (h₁ : ψ' ≫ ψ ≫ φ = φ'') (h₂ : (ψ' ≫ ψ) ≫ φ = φ'')
    {y : Y''} (hy : ψ.base (ψ'.base y) ∈ c.dom) :
    (((c.pullback ψ).pullback ψ').ofEq h₁).Agree F s ((c.pullback (ψ' ≫ ψ)).ofEq h₂) y := by
  have hU : ψ' ⁻¹ᵁ ψ ⁻¹ᵁ c.dom ≤ ψ' ⁻¹ᵁ ψ ⁻¹ᵁ c.dom ⊓ (ψ' ≫ ψ) ⁻¹ᵁ c.dom :=
    fun _ h ↦ ⟨h, h⟩
  have key : Y''.homOfLE (hU.trans inf_le_left) ≫
        ψ'.resLE (ψ ⁻¹ᵁ c.dom) (ψ' ⁻¹ᵁ ψ ⁻¹ᵁ c.dom) le_rfl ≫
          ψ.resLE c.dom (ψ ⁻¹ᵁ c.dom) le_rfl =
      Y''.homOfLE (hU.trans inf_le_right) ≫ (ψ' ≫ ψ).resLE c.dom ((ψ' ≫ ψ) ⁻¹ᵁ c.dom) le_rfl := by
    rw [← cancel_mono c.dom.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
      Scheme.homOfLE_ι_assoc]
  refine agree_of_hom_eq (((c.pullback ψ).pullback ψ').ofEq h₁) (V := (ψ' ≫ ψ) ⁻¹ᵁ c.dom)
    ((ψ' ≫ ψ).resLE c.dom ((ψ' ≫ ψ) ⁻¹ᵁ c.dom) le_rfl ≫ c.hom) ((c.pullback (ψ' ≫ ψ)).ofEq h₂).w
    hU ((reassoc_of% key) c.hom) hy

/-- **Pullbacks along equal morphisms agree**, whatever common morphism to `X` they are
transported to. -/
public theorem agree_pullback_congr (c : EtaleChart W φ) {Y' : Scheme.{u}} {ψ ψ' : Y' ⟶ Y}
    (e : ψ = ψ') {φ' : Y' ⟶ X} (h₁ : ψ ≫ φ = φ') (h₂ : ψ' ≫ φ = φ') {y : Y'}
    (hy : ψ.base y ∈ c.dom) :
    ((c.pullback ψ).ofEq h₁).Agree F s ((c.pullback ψ').ofEq h₂) y := by
  subst e
  exact agree_refl _ hy

/-- **Pulling back a global chart** gives the global chart of the composite. -/
public theorem agree_pullback_ofHom {j : α} (H : Y ⟶ (W j).left)
    (hH : H ≫ ((W j).hom : (W j).left ⟶ X) = φ) {Y' : Scheme.{u}} (ψ : Y' ⟶ Y)
    {φ' : Y' ⟶ X} (h₁ : ψ ≫ φ = φ') (h₂ : (ψ ≫ H) ≫ ((W j).hom : (W j).left ⟶ X) = φ')
    (y : Y') : (((ofHom H hH).pullback ψ).ofEq h₁).Agree F s (ofHom (ψ ≫ H) h₂) y := by
  refine agree_ofHom (((ofHom H hH).pullback ψ).ofEq h₁) (ψ ≫ H) h₂ ?_ trivial
  change ψ.resLE ⊤ (ψ ⁻¹ᵁ ⊤) le_rfl ≫ (⊤ : Y.Opens).ι ≫ H = (ψ ⁻¹ᵁ ⊤).ι ≫ ψ ≫ H
  rw [Scheme.Hom.resLE_comp_ι_assoc]

end EtaleChart

end Stacks.EtaleCohomology

end
