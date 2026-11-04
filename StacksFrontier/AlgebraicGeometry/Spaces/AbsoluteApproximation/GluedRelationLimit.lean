module

public import StacksFrontier.AlgebraicGeometry.LimitApprox.DescendOpen
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepThreeLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.GluedRelation

/-!
# The limit of the glued relations

In the proof of Stacks 07SU the relations `R_i = V_i ∪_{W_i} (W_i ×_{U_i} W_i)` form an inverse
system whose limit is identified with `V ×_X V`: "by construction
`lim W_i ×_{U_i} W_i = W ×_U W` and `V = lim V_i`, so that `R = lim R_i` is the union of `W ×_U W`
and `V` glued along `W`", and `V ×_X V` is the union of the opens `Δ(V)` and `W ×_U W`, which meet
along `Δ(W)`. This file proves the scheme-theoretic content of that sentence: a scheme `K`
covered by two open immersions from `V = lim V_i` and from `P = lim P_i`, compatible with the
glueing data and with a projection `K ⟶ V` restricting to the identity and to `p₂`, is the limit
of the glued relations, and its two projections are the limits of the projections of the system.

## Main results

* `AlgebraicGeometry.isOpenImmersion_of_isLimit` and
  `AlgebraicGeometry.preimage_opensRange_of_isLimit`: the limit of an open subsystem cut out by
  cartesian squares is an open subscheme of the limit, namely the inverse image of the open at
  any stage.
* `AlgebraicGeometry.gluedRelationCone` and `AlgebraicGeometry.isLimitGluedRelationCone`: the
  cone from `K` to the glued relations, and the fact that it is a limit cone.
* `AlgebraicGeometry.gluedRelationLeg_proj`: the projections of `K` are compatible with those
  of the glued relations.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace AlgebraicGeometry

/-! ### Open subsystems and limits -/

section OpenSubsystem

variable {J : Type w} [Category.{v} J] {D E : J ⥤ Scheme.{u}} (ν : E ⟶ D)
  [∀ j, IsOpenImmersion (ν.app j)]
  (hν : ∀ ⦃j k : J⦄ (u : j ⟶ k), D.map u ⁻¹ᵁ (ν.app k).opensRange = (ν.app j).opensRange)

include hν in
/-- Over a cofiltered index, the inverse image in the vertex of a cone of a compatible family of
opens does not depend on the stage. -/
lemma preimage_opensRange_eq_of_isCofiltered [IsCofiltered J] (c : Cone D) (j k : J) :
    c.π.app j ⁻¹ᵁ (ν.app j).opensRange = c.π.app k ⁻¹ᵁ (ν.app k).opensRange := by
  have h : ∀ ⦃i l : J⦄ (u : i ⟶ l),
      c.π.app i ⁻¹ᵁ (ν.app i).opensRange = c.π.app l ⁻¹ᵁ (ν.app l).opensRange := by
    intro i l u
    rw [← hν u, ← Scheme.Hom.comp_preimage, c.w u]
  rw [← h (IsCofiltered.minToLeft j k), h (IsCofiltered.minToRight j k)]

variable [IsCofiltered J] {cD : Cone D} (hD : IsLimit cD) {cE : Cone E} (hE : IsLimit cE)
  (νL : cE.pt ⟶ cD.pt) (hνL : ∀ j, νL ≫ cD.π.app j = cE.π.app j ≫ ν.app j)

include hν hD hE hνL in
/-- **The limit of an open subsystem is the inverse image of an open of a stage.** The morphism
of limits induced by a natural transformation with open-immersion components whose images are
cut out by the transition morphisms is the inclusion of the inverse image of the image at any
stage, up to isomorphism. -/
lemma exists_eq_comp_ι_of_isLimit (j₀ : J) :
    ∃ e : cE.pt ≅ (cD.π.app j₀ ⁻¹ᵁ (ν.app j₀).opensRange : Scheme.{u}),
      νL = e.hom ≫ (cD.π.app j₀ ⁻¹ᵁ (ν.app j₀).opensRange).ι := by
  set Q := cD.π.app j₀ ⁻¹ᵁ (ν.app j₀).opensRange
  have hU : ∀ j, cD.π.app j ⁻¹ᵁ (ν.app j).opensRange = Q := fun j ↦
    preimage_opensRange_eq_of_isCofiltered ν hν cD j j₀
  let V : ∀ j, (D.obj j).Opens := fun j ↦ (ν.app j).opensRange
  let iso := compatibleOpensDiagramIso ν V hν (fun _ ↦ rfl)
  let c' : Cone E := (Cone.postcompose iso.inv).obj (compatibleOpensCone D cD V hν Q hU)
  have hc' : IsLimit c' :=
    (IsLimit.postcomposeInvEquiv iso _).symm (isLimitCompatibleOpensCone hD V hν Q hU)
  refine ⟨hE.conePointUniqueUpToIso hc', hD.hom_ext fun j ↦ ?_⟩
  have hinv : iso.inv.app j ≫ ν.app j = (V j).ι := by
    rw [← compatibleOpensDiagramIso_hom_app_ι ν V hν (fun _ ↦ rfl) j, ← Category.assoc,
      ← NatTrans.comp_app, iso.inv_hom_id, NatTrans.id_app, Category.id_comp]
  have h1 : Q.ι ≫ cD.π.app j = c'.π.app j ≫ ν.app j := by
    show _ = ((cD.π.app j).resLE (V j) Q (hU j).ge ≫ iso.inv.app j) ≫ ν.app j
    rw [Category.assoc, hinv, Scheme.Hom.resLE_comp_ι]
  rw [hνL, Category.assoc, h1]
  exact (congrArg (· ≫ ν.app j) (IsLimit.conePointUniqueUpToIso_hom_comp hE hc' j)).symm.trans
    (Category.assoc _ _ _)

include hν hD hE hνL in
/-- **The limit of an open subsystem is an open subscheme of the limit.** -/
theorem isOpenImmersion_of_isLimit : IsOpenImmersion νL := by
  obtain ⟨e, he⟩ := exists_eq_comp_ι_of_isLimit ν hν hD hE νL hνL
    (IsCofiltered.nonempty (C := J)).some
  rw [he]
  infer_instance

include hν hD hE hνL in
/-- **The limit of an open subsystem is the inverse image of the open at any stage.** -/
theorem preimage_opensRange_of_isLimit [IsOpenImmersion νL] (j : J) :
    cD.π.app j ⁻¹ᵁ (ν.app j).opensRange = νL.opensRange := by
  obtain ⟨e, he⟩ := exists_eq_comp_ι_of_isLimit ν hν hD hE νL hνL j
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange, he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso e.hom.base).surjective.range_eq, Set.image_univ,
    Scheme.Opens.range_ι]

end OpenSubsystem

/-- Two morphisms out of a scheme covered by the images of two open immersions agree as soon as
they agree on both. -/
lemma Scheme.hom_ext_of_sup_eq_top {A B K Y : Scheme.{u}} (a : A ⟶ K) (b : B ⟶ K)
    [IsOpenImmersion a] [IsOpenImmersion b] (hcover : a.opensRange ⊔ b.opensRange = ⊤)
    {f g : K ⟶ Y} (ha : a ≫ f = a ≫ g) (hb : b ≫ f = b ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  have hx : x ∈ a.opensRange ⊔ b.opensRange := hcover ▸ trivial
  rcases TopologicalSpace.Opens.mem_sup.mp hx with hxa | hxb
  · refine ⟨a.opensRange, hxa, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc, ha]
  · refine ⟨b.opensRange, hxb, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc, hb]

/-! ### The limit of the glued relations -/

section Limit

variable {J : Type w} [Category.{v} J] {Dw Dv Dp : J ⥤ Scheme.{u}} (ι : Dw ⟶ Dv) (d : Dw ⟶ Dp)
  [∀ j, IsOpenImmersion (ι.app j)] [∀ j, IsOpenImmersion (d.app j)]
  (hα : ∀ ⦃j k : J⦄ (u : j ⟶ k), Dv.map u ⁻¹ᵁ (ι.app k).opensRange = (ι.app j).opensRange)
  (hβ : ∀ ⦃j k : J⦄ (u : j ⟶ k), Dp.map u ⁻¹ᵁ (d.app k).opensRange = (d.app j).opensRange)
  {cV : Cone Dv} (hV : IsLimit cV) {cW : Cone Dw} (hW : IsLimit cW)
  {cP : Cone Dp} (hP : IsLimit cP)
  (ιL : cW.pt ⟶ cV.pt) (hιL : ∀ j, ιL ≫ cV.π.app j = cW.π.app j ≫ ι.app j)
  (dL : cW.pt ⟶ cP.pt) (hdL : ∀ j, dL ≫ cP.π.app j = cW.π.app j ≫ d.app j)

include hα hV hW hιL in
/-- The limit of the open subsystem `W` of `V` is an open immersion. -/
lemma isOpenImmersion_ιL [IsCofiltered J] : IsOpenImmersion ιL :=
  isOpenImmersion_of_isLimit ι hα hV hW ιL hιL

include hβ hP hW hdL in
/-- The limit of the diagonals is an open immersion. -/
lemma isOpenImmersion_dL [IsCofiltered J] : IsOpenImmersion dL :=
  isOpenImmersion_of_isLimit d hβ hP hW dL hdL

variable (p₂L : cP.pt ⟶ cW.pt)
  {K : Scheme.{u}} (dK : cV.pt ⟶ K) (eK : cP.pt ⟶ K) [IsOpenImmersion dK] [IsOpenImmersion eK]
  (sK : K ⟶ cV.pt) (hdsK : dK ≫ sK = 𝟙 _) (hesK : eK ≫ sK = p₂L ≫ ιL)
  (hde : ιL ≫ dK = dL ≫ eK) (hcover : dK.opensRange ⊔ eK.opensRange = ⊤)

include hdsK hesK hde in
omit [IsOpenImmersion dK] [IsOpenImmersion eK] in
/-- A point of the first piece of `K` lies in the second piece exactly when it comes from `W`. -/
lemma mem_range_ιL_iff (v : cV.pt) : v ∈ Set.range ιL ↔ dK v ∈ Set.range eK := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨dL w, by rw [← Scheme.Hom.comp_apply, ← hde, Scheme.Hom.comp_apply]⟩
  · rintro ⟨q, hq⟩
    refine ⟨p₂L q, ?_⟩
    have h1 : sK (dK v) = v := by
      rw [← Scheme.Hom.comp_apply, hdsK]
      rfl
    have h2 : sK (eK q) = ιL (p₂L q) := by
      rw [← Scheme.Hom.comp_apply, hesK, Scheme.Hom.comp_apply]
    rw [← h1, ← hq, h2]

include hdsK hesK hde in
omit [IsOpenImmersion dK] in
/-- A point of the second piece of `K` lies in the first piece exactly when it comes from `W`. -/
lemma mem_range_dL_iff (q : cP.pt) : q ∈ Set.range dL ↔ eK q ∈ Set.range dK := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨ιL w, by rw [← Scheme.Hom.comp_apply, hde, Scheme.Hom.comp_apply]⟩
  · rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := (mem_range_ιL_iff ιL dL p₂L dK eK sK hdsK hesK hde v).mpr ⟨_, hv.symm⟩
    refine ⟨w, eK.isOpenEmbedding.injective ?_⟩
    rw [← hv, ← Scheme.Hom.comp_apply, ← hde, Scheme.Hom.comp_apply]

variable [IsOpenImmersion ιL]

include hdsK hesK hde in
omit [IsOpenImmersion ιL] in
/-- The two pieces of `K` meet in the image of `W`. -/
lemma range_inf_eq_range_comp :
    Set.range ((dK.opensRange ⊓ eK.opensRange).ι) = Set.range (ιL ≫ dK) := by
  refine Set.ext fun x ↦ ?_
  rw [Scheme.Opens.range_ι]
  constructor
  · rintro ⟨⟨v, rfl⟩, hx⟩
    obtain ⟨w, rfl⟩ := (mem_range_ιL_iff ιL dL p₂L dK eK sK hdsK hesK hde v).mpr hx
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨⟨ιL w, rfl⟩, (mem_range_ιL_iff ιL dL p₂L dK eK sK hdsK hesK hde (ιL w)).mp ⟨w, rfl⟩⟩

/-- The intersection of the two pieces of `K`, identified with the limit `W` of the open
subsystem. -/
noncomputable def gluedRelationInterIso :
    ((dK.opensRange ⊓ eK.opensRange : K.Opens) : Scheme.{u}) ≅ cW.pt :=
  IsOpenImmersion.isoOfRangeEq _ (ιL ≫ dK)
    (range_inf_eq_range_comp ιL dL p₂L dK eK sK hdsK hesK hde)

/-- The isomorphism `gluedRelationInterIso` followed by the open immersion `W ⟶ K` through the
first piece is the inclusion of the intersection of the two pieces of `K`. -/
lemma gluedRelationInterIso_hom_fac :
    (gluedRelationInterIso ιL dL p₂L dK eK sK hdsK hesK hde).hom ≫ ιL ≫ dK =
      (dK.opensRange ⊓ eK.opensRange).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The cone from the first piece of `K` to `V`. -/
noncomputable abbrev gluedRelationConeLeft :
    (Functor.const J).obj (dK.opensRange : Scheme.{u}) ⟶ Dv :=
  (Functor.const J).map dK.isoOpensRange.inv ≫ cV.π

/-- The cone from the second piece of `K` to `P`. -/
noncomputable abbrev gluedRelationConeRight :
    (Functor.const J).obj (eK.opensRange : Scheme.{u}) ⟶ Dp :=
  (Functor.const J).map eK.isoOpensRange.inv ≫ cP.π

/-- The cone from the intersection of the two pieces of `K` to `W`. -/
noncomputable abbrev gluedRelationConeInter :
    (Functor.const J).obj ((dK.opensRange ⊓ eK.opensRange : K.Opens) : Scheme.{u}) ⟶ Dw :=
  (Functor.const J).map
    (gluedRelationInterIso ιL dL p₂L dK eK sK hdsK hesK hde).hom ≫ cW.π

include hιL in
omit [∀ j, IsOpenImmersion (ι.app j)] in
/-- On the intersection of the two pieces of `K`, the leg of `gluedRelationConeLeft` agrees with
the leg of `gluedRelationConeInter` followed by `ι`. -/
lemma gluedRelationCone_hXW (j : J) :
    K.homOfLE (inf_le_left : dK.opensRange ⊓ eK.opensRange ≤ dK.opensRange) ≫
        (gluedRelationConeLeft dK).app j =
      (gluedRelationConeInter ιL dL p₂L dK eK sK hdsK hesK hde).app j ≫
        ι.app j := by
  have key : K.homOfLE (inf_le_left : dK.opensRange ⊓ eK.opensRange ≤ dK.opensRange) ≫
      dK.isoOpensRange.inv =
      (gluedRelationInterIso ιL dL p₂L dK eK sK hdsK hesK hde).hom ≫ ιL := by
    rw [← cancel_mono dK, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι,
      Category.assoc, gluedRelationInterIso_hom_fac]
  simp only [NatTrans.comp_app, Functor.const_map_app, Category.assoc]
  rw [← hιL, reassoc_of% key]

include hdL hde in
omit [∀ j, IsOpenImmersion (d.app j)] in
/-- On the intersection of the two pieces of `K`, the leg of `gluedRelationConeRight` agrees with
the leg of `gluedRelationConeInter` followed by `d`. -/
lemma gluedRelationCone_hYW (j : J) :
    K.homOfLE (inf_le_right : dK.opensRange ⊓ eK.opensRange ≤ eK.opensRange) ≫
        (gluedRelationConeRight eK).app j =
      (gluedRelationConeInter ιL dL p₂L dK eK sK hdsK hesK hde).app j ≫
        d.app j := by
  have key : K.homOfLE (inf_le_right : dK.opensRange ⊓ eK.opensRange ≤ eK.opensRange) ≫
      eK.isoOpensRange.inv =
      (gluedRelationInterIso ιL dL p₂L dK eK sK hdsK hesK hde).hom ≫ dL := by
    rw [← cancel_mono eK, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι,
      Category.assoc, ← hde, gluedRelationInterIso_hom_fac]
  simp only [NatTrans.comp_app, Functor.const_map_app, Category.assoc]
  rw [← hdL, reassoc_of% key]

/-- **The cone from `K` to the glued relations.** Its leg at a stage is the identity-glued map
which is the leg of `V` on the first piece and the leg of `P` on the second. -/
noncomputable def gluedRelationCone : Cone (gluePairFunctor ι d) :=
  Cone.mk K (gluePairFunctorCone ι d dK.opensRange eK.opensRange (gluedRelationConeLeft dK)
    (gluedRelationConeRight eK)
    (gluedRelationConeInter ιL dL p₂L dK eK sK hdsK hesK hde)
    (gluedRelationCone_hXW ι ιL hιL dL p₂L dK eK sK hdsK hesK hde)
    (gluedRelationCone_hYW d ιL dL hdL p₂L dK eK sK hdsK hesK hde) hcover)

/-- The leg of `AlgebraicGeometry.gluedRelationCone` at a stage, as a morphism out of `K`. -/
noncomputable def gluedRelationLeg (j : J) : K ⟶ (gluePairFunctor ι d).obj j :=
  (gluedRelationCone ι d ιL hιL dL hdL p₂L dK eK sK hdsK hesK hde hcover).π.app j

/-- The leg of `gluedRelationCone` at a stage is `gluedRelationLeg`. -/
lemma gluedRelationCone_π_app (j : J) :
    (gluedRelationCone ι d ιL hιL dL hdL p₂L dK eK sK hdsK hesK hde hcover).π.app j =
      gluedRelationLeg ι d ιL hιL dL hdL p₂L dK eK sK hdsK hesK hde hcover j := rfl

/-- A morphism out of `K` agrees with a morphism out of an open piece `a` of `K` as soon as it does
on the open piece, viewed as a subscheme. -/
private lemma comp_eq_of_opensRange_ι_comp_eq {A K Y Z : Scheme.{u}} (a : A ⟶ K)
    [IsOpenImmersion a] (L : K ⟶ Y) (c : A ⟶ Z) (g : Z ⟶ Y)
    (h : a.opensRange.ι ≫ L = (a.isoOpensRange.inv ≫ c) ≫ g) : a ≫ L = c ≫ g := by
  nth_rw 1 [← Scheme.Hom.isoOpensRange_hom_ι a]
  rw [Category.assoc, h, Category.assoc]
  exact Iso.hom_inv_id_assoc _ _

/-- On the first piece of `K`, the leg of the cone is the leg of `V` followed by the first leg of
the glueing. -/
@[reassoc]
lemma dK_gluedRelationLeg (j : J) :
    dK ≫ gluedRelationLeg ι d ιL hιL dL hdL p₂L dK eK sK hdsK hesK hde hcover j =
      cV.π.app j ≫ (gluePairFunctorInl ι d).app j := by
  refine comp_eq_of_opensRange_ι_comp_eq dK _ _ _
    (ι_gluePairFunctorCone_app_left ι d dK.opensRange eK.opensRange
      (gluedRelationConeLeft dK) (gluedRelationConeRight eK)
      (gluedRelationConeInter ιL dL p₂L dK eK sK hdsK hesK hde)
      (gluedRelationCone_hXW ι ιL hιL dL p₂L dK eK sK hdsK hesK hde)
      (gluedRelationCone_hYW d ιL dL hdL p₂L dK eK sK hdsK hesK hde) hcover j)

/-- On the second piece of `K`, the leg of the cone is the leg of `P` followed by the second leg
of the glueing. -/
@[reassoc]
lemma eK_gluedRelationLeg (j : J) :
    eK ≫ gluedRelationLeg ι d ιL hιL dL hdL p₂L dK eK sK hdsK hesK hde hcover j =
      cP.π.app j ≫ (gluePairFunctorInr ι d).app j := by
  refine comp_eq_of_opensRange_ι_comp_eq eK _ _ _
    (ι_gluePairFunctorCone_app_right ι d dK.opensRange eK.opensRange
      (gluedRelationConeLeft dK) (gluedRelationConeRight eK)
      (gluedRelationConeInter ιL dL p₂L dK eK sK hdsK hesK hde)
      (gluedRelationCone_hXW ι ιL hιL dL p₂L dK eK sK hdsK hesK hde)
      (gluedRelationCone_hYW d ιL dL hdL p₂L dK eK sK hdsK hesK hde) hcover j)

include hα hβ hV hW hP in
/-- **The glued relations have `K` as their limit.** -/
noncomputable def isLimitGluedRelationCone [IsCofiltered J] :
    IsLimit (gluedRelationCone ι d ιL hιL dL hdL p₂L dK eK sK hdsK hesK hde hcover) := by
  have := isOpenImmersion_dL d hβ hW hP dL hdL
  refine isLimitGluePairFunctorCone ι d dK.opensRange eK.opensRange _ _ _ _ _ hcover hα hβ
    ?_ ?_ ?_ ?_ ?_
  · intro j
    ext x
    have hx : dK (dK.isoOpensRange.inv x) = (dK.opensRange).ι x := by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_inv_comp]
    simp only [NatTrans.comp_app, Functor.const_map_app, Scheme.Hom.comp_preimage,
      preimage_opensRange_of_isLimit ι hα hV hW ιL hιL j]
    change dK.isoOpensRange.inv x ∈ Set.range ιL ↔ (dK.opensRange).ι x ∈ Set.range eK
    rw [← hx]
    exact mem_range_ιL_iff ιL dL p₂L dK eK sK hdsK hesK hde _
  · intro j
    ext y
    have hy : eK (eK.isoOpensRange.inv y) = (eK.opensRange).ι y := by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_inv_comp]
    simp only [NatTrans.comp_app, Functor.const_map_app, Scheme.Hom.comp_preimage,
      preimage_opensRange_of_isLimit d hβ hP hW dL hdL j]
    change eK.isoOpensRange.inv y ∈ Set.range dL ↔ (eK.opensRange).ι y ∈ Set.range dK
    rw [← hy]
    exact mem_range_dL_iff ιL dL p₂L dK eK sK hdsK hesK hde _
  · exact hV.ofIsoLimit (Cone.ext dK.isoOpensRange fun j ↦ by simp)
  · exact hP.ofIsoLimit (Cone.ext eK.isoOpensRange fun j ↦ by simp)
  · exact hW.ofIsoLimit
      (Cone.ext (gluedRelationInterIso ιL dL p₂L dK eK sK hdsK hesK hde).symm
        fun j ↦ by simp)

include hesK hdsK in
/-- **The projections of `K` are the limits of the projections of the glued relations.** For a
projection `p` of the system, split by `d`, and a morphism `pK : K ⟶ V` restricting to the
identity on the first piece and to the limit `pL` of `p` on the second, `pK` is compatible with
the legs. -/
lemma gluedRelationLeg_proj (p : Dp ⟶ Dw) (hp : d ≫ p = 𝟙 Dw) (pL : cP.pt ⟶ cW.pt)
    (hpL : ∀ j, pL ≫ cW.π.app j = cP.π.app j ≫ p.app j) (pK : K ⟶ cV.pt)
    (hdpK : dK ≫ pK = 𝟙 _) (hepK : eK ≫ pK = pL ≫ ιL) (j : J) :
    pK ≫ cV.π.app j =
      gluedRelationLeg ι d ιL hιL dL hdL p₂L dK eK sK hdsK hesK hde hcover j ≫
        (gluedRelationProjNatTrans ι d p hp).app j := by
  refine Scheme.hom_ext_of_sup_eq_top dK eK hcover ?_ ?_
  · rw [reassoc_of% hdpK, dK_gluedRelationLeg_assoc ι d ιL hιL dL hdL p₂L dK eK
      sK hdsK hesK hde hcover j, gluePairFunctorInl_app_gluedRelationProjNatTrans_app,
      Category.comp_id]
  · rw [reassoc_of% hepK, eK_gluedRelationLeg_assoc ι d ιL hιL dL hdL p₂L dK eK
      sK hdsK hesK hde hcover j, gluePairFunctorInr_app_gluedRelationProjNatTrans_app,
      hιL, reassoc_of% hpL]

end Limit

end AlgebraicGeometry
