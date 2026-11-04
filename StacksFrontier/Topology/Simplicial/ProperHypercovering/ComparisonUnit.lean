module

public import
  StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectComponentCohomology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousMorphismBaseChange
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.QcSmallCohomology
public import StacksFrontier.Topology.Simplicial.QcSmallTotalSiteComparison

/-!
# The comparison `h : Sh((LC_qc/U)_total) → Sh(U_Zar)` has fully faithful inverse image

Let `U` be a simplicial object of the quasi-compact site `LC_qc` of Stacks 09X2 and `a : U → X`
an augmentation. The upper horizontal arrow of the diagram of Stacks 0DAF is the morphism of topoi
`h : Sh((LC_qc/U)_total) → Sh(U_Zar)` of the comparison functor `u : U_Zar ⥤ (LC_qc/U)_total`,
`V ↦ V/U_n` (`Stacks.Topology.Simplicial.qcSmallComparisonMorphism`). Its inverse image `h^{-1}`
is fully faithful with quasi-inverse `h_*`: the unit `G ⟶ h_* h^{-1} G` is an isomorphism.

## Main results

* `Stacks.Topology.Simplicial.qcSmallLevelSquare_guitartExact`: the square of component
  inclusions is Guitart exact.
* `Stacks.Topology.Simplicial.isIso_qcSmallComparisonBeckChevalley`: Stacks 0D96 for `h`, the
  Beck–Chevalley comparison of inverse images.
* `Stacks.Topology.Simplicial.isIso_qcSmallComparisonMorphism_adj_unit`: the unit
  `G ⟶ h_* h^{-1} G` is an isomorphism for every sheaf of sets `G` on `U_Zar`.

## References

* [Stacks Project, Tag 0DAF](https://stacks.math.columbia.edu/tag/0DAF)
* [Stacks Project, Tag 0DAG](https://stacks.math.columbia.edu/tag/0DAG)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w

/-! ### Beck–Chevalley for a square with a large lower left corner -/

namespace CategoryTheory

section ContinuousSquare

universe v' u'

variable {A A' B : Type u} [SmallCategory A] [SmallCategory A'] [SmallCategory B]
  {B' : Type u'} [Category.{v'} B']
  (JA : GrothendieckTopology A) (JA' : GrothendieckTopology A') (JB : GrothendieckTopology B)
  (JB' : GrothendieckTopology B')
  (i : A ⥤ B) (i' : A' ⥤ B') (v : A' ⥤ A) (T : B' ⥤ B)
  [i.IsContinuous JA JB] [i.IsCocontinuous JA JB] [i'.IsContinuous JA' JB']
  [i'.IsCocontinuous JA' JB'] [v.IsContinuous JA' JA] [T.IsContinuous JB' JB]
  [∀ F : A'ᵒᵖ ⥤ Type u, i'.op.HasPointwiseRightKanExtension F]
  (w : TwoSquare v i' i T)

/-- **On underlying presheaves, the mate of the square of direct images is the square of site
functors**: along the adjunctions `i^{-1} ⊣ i_*` and `i'^{-1} ⊣ i'_*`, the mate
`T_* ⋙ i'^{-1} ⟶ i^{-1} ⋙ v_*` of the square of direct images `(i'_* ∘ v_*) ≅ (T_* ∘ i_*)` given
by the base change of right Kan extensions along the opposite square is restriction along `w`.
Here the lower left corner `B'` need not be a small category. -/
theorem sheafPushforwardContinuousSquareMateOfLarge_app_hom [w.GuitartExact]
    (F : Sheaf JB (Type u)) :
    (((mateEquiv (i.sheafAdjunctionCocontinuous (Type u) JA JB)
        (i'.sheafAdjunctionCocontinuous (Type u) JA' JB')).symm
        (TwoSquare.mk _ _ _ _
          (Functor.fullyFaithfulCancelRight (sheafToPresheaf JB' (Type u))
          (Functor.isoWhiskerLeft (sheafToPresheaf JA (Type u))
            (asIso (w.op.ranBaseChange (D := Type u)))) :
            i.sheafPushforwardCocontinuous (Type u) JA JB ⋙
                T.sheafPushforwardContinuous (Type u) JB' JB ≅
              v.sheafPushforwardContinuous (Type u) JA' JA ⋙
                i'.sheafPushforwardCocontinuous (Type u) JA' JB').hom)).natTrans.app F).hom =
      Functor.whiskerRight w.op.natTrans F.obj := by
  have hR : ∀ {X : A'ᵒᵖ ⥤ Type u} {Y : B'ᵒᵖ ⥤ Type u} (y : i'.op ⋙ Y ⟶ X),
      Functor.whiskerLeft i'.op ((i'.op.ranAdjunction (Type u)).homEquiv Y X y) ≫
        (i'.op.ranAdjunction (Type u)).counit.app X = y := by
    intro X Y y
    have h := (i'.op.ranAdjunction (Type u)).homEquiv_counit
      (g := (i'.op.ranAdjunction (Type u)).homEquiv Y X y)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have hε : ∀ G : Sheaf JA' (Type u),
      ((i'.sheafAdjunctionCocontinuous (Type u) JA' JB').counit.app G).hom =
        (i'.op.ranAdjunction (Type u)).counit.app G.obj :=
    Functor.sheafAdjunctionCocontinuous_counit_app_hom _ _ _ _
  have hη : ((i.sheafAdjunctionCocontinuous (Type u) JA JB).unit.app F).hom =
      (i.op.ranAdjunction (Type u)).unit.app F.obj :=
    Functor.sheafAdjunctionCocontinuous_unit_app_hom _ _ _ _ F
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map, Category.id_comp,
    Functor.map_id, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom]
  show Functor.whiskerLeft i'.op (Functor.whiskerLeft T.op
      ((i.sheafAdjunctionCocontinuous (Type u) JA JB).unit.app F).hom) ≫
    Functor.whiskerLeft i'.op (((Functor.fullyFaithfulCancelRight (sheafToPresheaf JB' (Type u))
        (Functor.isoWhiskerLeft (sheafToPresheaf JA (Type u))
          (asIso (w.op.ranBaseChange (D := Type u)))) :
          i.sheafPushforwardCocontinuous (Type u) JA JB ⋙
              T.sheafPushforwardContinuous (Type u) JB' JB ≅
            v.sheafPushforwardContinuous (Type u) JA' JA ⋙
              i'.sheafPushforwardCocontinuous (Type u) JA' JB').hom.app
            ((i.sheafPushforwardContinuous (Type u) JA JB).obj F)).hom) ≫
    ((i'.sheafAdjunctionCocontinuous (Type u) JA' JB').counit.app
      ((v.sheafPushforwardContinuous (Type u) JA' JA).obj
        ((i.sheafPushforwardContinuous (Type u) JA JB).obj F))).hom = _
  have hinv : ((Functor.fullyFaithfulCancelRight (sheafToPresheaf JB' (Type u))
      (Functor.isoWhiskerLeft (sheafToPresheaf JA (Type u))
        (asIso (w.op.ranBaseChange (D := Type u)))) :
        i.sheafPushforwardCocontinuous (Type u) JA JB ⋙
            T.sheafPushforwardContinuous (Type u) JB' JB ≅
          v.sheafPushforwardContinuous (Type u) JA' JA ⋙
            i'.sheafPushforwardCocontinuous (Type u) JA' JB').hom.app
          ((i.sheafPushforwardContinuous (Type u) JA JB).obj F)).hom =
      w.op.ranBaseChange.app (i.op ⋙ F.obj) :=
    (sheafToPresheaf JB' (Type u)).map_preimage _
  rw [hη, hinv, hε]
  have hB : Functor.whiskerLeft i'.op (w.op.ranBaseChange.app (i.op ⋙ F.obj)) ≫
      (i'.op.ranAdjunction (Type u)).counit.app (v.op ⋙ i.op ⋙ F.obj) =
      ((Functor.RightExtension.mk _ (i.op.ranCounit.app (i.op ⋙ F.obj))).compTwoSquare
        w.op).hom :=
    hR _
  show Functor.whiskerLeft i'.op (Functor.whiskerLeft T.op
      ((i.op.ranAdjunction (Type u)).unit.app F.obj)) ≫
    (Functor.whiskerLeft i'.op (w.op.ranBaseChange.app (i.op ⋙ F.obj)) ≫
      (i'.op.ranAdjunction (Type u)).counit.app (v.op ⋙ i.op ⋙ F.obj)) = _
  rw [hB]
  refine NatTrans.ext (funext fun X ↦ ?_)
  have n1 : ((i.op.ranAdjunction (Type u)).unit.app F.obj).app (T.op.obj (i'.op.obj X)) ≫
      (i.op.ran.obj (i.op ⋙ F.obj)).map (w.op.natTrans.app X) =
      F.obj.map (w.op.natTrans.app X) ≫
        ((i.op.ranAdjunction (Type u)).unit.app F.obj).app (i.op.obj (v.op.obj X)) :=
    (((i.op.ranAdjunction (Type u)).unit.app F.obj).naturality (w.op.natTrans.app X)).symm
  have t1 := Functor.ranCounit_app_app_ranAdjunction_unit_app_app i.op F.obj (v.op.obj X)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  show ((i.op.ranAdjunction (Type u)).unit.app F.obj).app (T.op.obj (i'.op.obj X)) ≫
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight w.op.natTrans (i.op.ran.obj (i.op ⋙ F.obj)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft v.op (i.op.ranCounit.app (i.op ⋙ F.obj))).app X = _
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  rw [reassoc_of% n1, t1]
  exact Category.comp_id _

/-- **Beck–Chevalley for a Guitart exact square with continuous horizontal functors and a large
lower left corner.** The mate `T_* ⋙ i'^{-1} ⟶ i^{-1} ⋙ v_*` of the square of direct images is an
isomorphism as soon as the square of site functors is. -/
theorem isIso_sheafPushforwardContinuousSquareMateOfLarge [w.GuitartExact] [IsIso w.natTrans] :
    IsIso ((mateEquiv (i.sheafAdjunctionCocontinuous (Type u) JA JB)
        (i'.sheafAdjunctionCocontinuous (Type u) JA' JB')).symm
        (TwoSquare.mk _ _ _ _
          (Functor.fullyFaithfulCancelRight (sheafToPresheaf JB' (Type u))
          (Functor.isoWhiskerLeft (sheafToPresheaf JA (Type u))
            (asIso (w.op.ranBaseChange (D := Type u)))) :
            i.sheafPushforwardCocontinuous (Type u) JA JB ⋙
                T.sheafPushforwardContinuous (Type u) JB' JB ≅
              v.sheafPushforwardContinuous (Type u) JA' JA ⋙
                i'.sheafPushforwardCocontinuous (Type u) JA' JB').hom)).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← ObjectProperty.isIso_hom_iff, sheafPushforwardContinuousSquareMateOfLarge_app_hom]
  have : IsIso w.op.natTrans := by
    show IsIso (NatTrans.op w.natTrans)
    infer_instance
  exact (Functor.isoWhiskerRight (asIso w.op.natTrans) F.obj).isIso_hom

end ContinuousSquare

end CategoryTheory

namespace Stacks.Topology.Simplicial

open Stacks.Topology Stacks.Topology.Simplicial.ProperHypercovering
open Stacks.CategoryTheory.Hypercovering CategoryTheory.SimplicialSemiRepresentable

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
  (X : S.category) (U : SimplicialObject S.category)
  (a : U ⟶ (SimplicialObject.const S.category).obj X)

/-! ### The square of component inclusions -/

/-- The inclusion of the degree-`n` site `(LC_qc/X)/(U_n/X)` into `(LC_qc/U)_total`. -/
def qcSmallTotalIota (n : SimplexCategoryᵒᵖ) : qcSmallDegree S X U a n ⥤ qcSmallTotal S X U a :=
  Grothendieck.ι (slices (qcSmallSemiRep S X U a)) n

/-- The comparison functor in simplicial degree `n`: an open `V` of `U_n` goes to the open
subspace `V/U_n`, carried to the small model, in the degree-`n` site of `(LC_qc/U)_total`. -/
abbrev qcSmallComparisonDegree (n : SimplexCategoryᵒᵖ) :
    Opens ((qcSimplicialSpace S U).obj n) ⥤ qcSmallDegree S X U a n :=
  (S.opensToSlice (U.obj n)).1 ⋙ qcSmallDegreeFunctor S X U a n

/-- The square of component inclusions commutes: both composites send an open `V` of `U_n` to
the comparison object of `V`, by an isomorphism with identity components. -/
def qcSmallLevelSquareIso (n : SimplexCategoryᵒᵖ) :
    qcSmallComparisonDegree S X U a n ⋙ qcSmallTotalIota S X U a n ≅
      levelFunctor (qcSimplicialSpace S U) n ⋙ qcSmallComparisonFunctor S X U a :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun t ↦
    (Category.comp_id _).trans ((qcSmallComparisonFunctor_map_levelFunctor S X U a n t).symm.trans
      (Category.id_comp _).symm))

/-- The square of component inclusions, as a 2-square. -/
abbrev qcSmallLevelSquare (n : SimplexCategoryᵒᵖ) :
    TwoSquare (qcSmallComparisonDegree S X U a n) (levelFunctor (qcSimplicialSpace S U) n)
      (qcSmallTotalIota S X U a n) (qcSmallComparisonFunctor S X U a) :=
  (qcSmallLevelSquareIso S X U a n).hom

/-- The square of component inclusions is invertible. -/
instance isIso_qcSmallLevelSquare (n : SimplexCategoryᵒᵖ) :
    IsIso (qcSmallLevelSquare S X U a n).natTrans :=
  inferInstanceAs (IsIso (qcSmallLevelSquareIso S X U a n).hom)

/-- Morphisms in the degree-`n` site into the value of `u_n` are unique. -/
theorem qcSmallComparisonDegree_hom_ext {n : SimplexCategoryᵒᵖ} {t : qcSmallDegree S X U a n}
    {V : Opens ((qcSimplicialSpace S U).obj n)}
    (f g : t ⟶ (qcSmallComparisonDegree S X U a n).obj V) : f = g :=
  qcSmallFiber_hom_ext S X U a f g

/-- A morphism in the degree-`n` site into the value of `u_n` at an open containing the points
of its source. -/
def qcSmallComparisonDegreeHomMk {n : SimplexCategoryᵒᵖ} (t : qcSmallDegree S X U a n)
    (V : Opens ((qcSimplicialSpace S U).obj n))
    (h : ∀ p : (S.qcSite.smallEquivalence.inverse.obj t.2.left.left).obj,
      ((qcSmallPoint S X U a ⟨n, t⟩ : _ ⟶ U.obj n) :
        (S.qcSite.smallEquivalence.inverse.obj t.2.left.left).obj → (U.obj n).obj) p ∈ V) :
    t ⟶ (qcSmallComparisonDegree S X U a n).obj V :=
  eqToHom (by simp; rfl) ≫ (qcSmallHomMk S X U a ⟨n, t⟩ ⟨n, V⟩ (𝟙 n) (fun p ↦ by
    rw [U.map_id, Category.comp_id]
    exact h p)).fiber

/-- The simplex map of the composite of a morphism into the value of `u_n`, the square, and the
value of `u` at a morphism `b` out of the image of an open of `U_n`, is that of `b`. -/
theorem qcSmallLevelSquare_comp_base {n : SimplexCategoryᵒᵖ} {t : qcSmallDegree S X U a n}
    {V : Opens ((qcSimplicialSpace S U).obj n)} {W : SimplicialOpen (qcSimplicialSpace S U)}
    (a' : t ⟶ (qcSmallComparisonDegree S X U a n).obj V)
    (b' : (levelFunctor (qcSimplicialSpace S U) n).obj V ⟶ W) :
    ((qcSmallTotalIota S X U a n).map a' ≫
      (qcSmallLevelSquare S X U a n).app V ≫ (qcSmallComparisonFunctor S X U a).map b').base =
        b'.base := by
  show 𝟙 n ≫ 𝟙 n ≫ b'.base = b'.base
  exact (Category.id_comp _).trans (Category.id_comp _)

/-- The square of component inclusions is Guitart exact. -/
instance qcSmallLevelSquare_guitartExact (n : SimplexCategoryᵒᵖ) :
    (qcSmallLevelSquare S X U a n).GuitartExact := by
  constructor
  intro t W g
  let w := qcSmallLevelSquare S X U a n
  let V : Opens ((qcSimplicialSpace S U).obj n) :=
    (Opens.map ((qcSimplicialSpace S U).map g.base)).obj W.toOpens
  let aP : t ⟶ (qcSmallComparisonDegree S X U a n).obj V :=
    qcSmallComparisonDegreeHomMk S X U a t V (qcSmallComparison_mem S X U a g)
  let bP : (levelFunctor (qcSimplicialSpace S U) n).obj V ⟶ W := ⟨g.base, le_rfl⟩
  have comm : (qcSmallTotalIota S X U a n).map aP ≫ w.app V ≫
      (qcSmallComparisonFunctor S X U a).map bP = g :=
    qcSmallComparison_hom_ext S X U a _ _ (qcSmallLevelSquare_comp_base S X U a aP bP)
  let P : w.StructuredArrowRightwards g :=
    TwoSquare.StructuredArrowRightwards.mk w g V aP bP comm
  have hterminal : ∀ Q : w.StructuredArrowRightwards g, Nonempty (Q ⟶ P) := by
    intro Q
    obtain ⟨V', a', b', hcomm, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective Q
    have hbase : b'.base = g.base :=
      (qcSmallLevelSquare_comp_base S X U a a' b').symm.trans
        (congrArg Grothendieck.Hom.base hcomm)
    have hle : V' ≤ V := fun x hx ↦ by
      have := SimplicialOpen.Hom.le b' hx
      rwa [hbase] at this
    have htri : (levelFunctor (qcSimplicialSpace S U) n).map (homOfLE hle) ≫ bP = b' :=
      SimplicialOpen.Hom.ext _ _ (by
        change 𝟙 n ≫ g.base = b'.base
        rw [hbase]
        exact Category.id_comp _)
    exact ⟨StructuredArrow.homMk (CostructuredArrow.homMk (homOfLE hle) htri)
      (CostructuredArrow.hom_ext _ _ (qcSmallComparisonDegree_hom_ext S X U a _ _))⟩
  have : Nonempty (w.StructuredArrowRightwards g) := ⟨P⟩
  exact zigzag_isConnected fun Q₁ Q₂ ↦
    (Zigzag.of_hom (hterminal Q₁).some).trans (Zigzag.of_inv (hterminal Q₂).some)

/-! ### The topologies -/

section Sites

variable (n : SimplexCategoryᵒᵖ)

/-- The topology of the degree-`n` site of `(LC_qc/U)_total`: the localized quasi-compact
topology of `LC_qc/U_n`, read on `(LC_qc/X)/(U_n/X)`. -/
abbrev qcSmallDegreeTopology : GrothendieckTopology (qcSmallDegree S X U a n) :=
  SemiRepresentable.componentwiseTopology (S.qcSite.smallOverTopology X)
    ((qcSmallSemiRep S X U a).obj n)

/-- The inclusion of the degree-`n` site into `(LC_qc/U)_total` is continuous. -/
instance qcSmallTotalIota_isContinuous :
    (qcSmallTotalIota S X U a n).IsContinuous
      (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a) := by
  have h := SimplicialSiteSituation.componentFunctor_isContinuous (qcTotalSituation S X U a) n.unop
  rwa [qcTotalSituation, totalSituation, componentTopology_eq] at h

/-- The inclusion of the degree-`n` site into `(LC_qc/U)_total` is cocontinuous. -/
instance qcSmallTotalIota_isCocontinuous :
    (qcSmallTotalIota S X U a n).IsCocontinuous
      (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a) := by
  have h := SimplicialSiteSituation.componentFunctor_isCocontinuous (qcTotalSituation S X U a)
    n.unop
  rwa [qcTotalSituation, totalSituation, componentTopology_eq] at h

/-- The inclusion of the opens of `U_n` into the simplicial opens of `U` is continuous. -/
instance qcLevelFunctor_isContinuous :
    (levelFunctor (qcSimplicialSpace S U) n).IsContinuous
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) :=
  levelFunctor_isContinuous _ n

/-- The inclusion of the opens of `U_n` into the simplicial opens of `U` is cocontinuous. -/
instance qcLevelFunctor_isCocontinuous :
    (levelFunctor (qcSimplicialSpace S U) n).IsCocontinuous
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) :=
  levelFunctor_isCocontinuous _ n

/-- The comparison functor `u : U_Zar ⥤ (LC_qc/U)_total` is continuous. -/
instance qcSmallComparisonFunctor_isContinuous' :
    (qcSmallComparisonFunctor S X U a).IsContinuous
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
      (qcSmallTotalTopology S X U a) :=
  qcSmallComparisonFunctor_isContinuous S X U a

/-- The comparison functor in degree `n` is the open-subset functor `V ↦ V/U_n` of the small
model followed by the identification of `LC_qc/U_n` with the degree-`n` site. -/
theorem qcSmallComparisonDegree_eq :
    qcSmallComparisonDegree S X U a n =
      qcSmallOpensFunctor S (U.obj n) ⋙
        SimplicialOver.toComponentOver (qcSmallSimplicialObject S U)
          (qcSmallAugmentation S X U a) n :=
  rfl

/-- The comparison functor in degree `n` is continuous. -/
instance qcSmallComparisonDegree_isContinuous :
    (qcSmallComparisonDegree S X U a n).IsContinuous
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (qcSmallDegreeTopology S X U a n) := by
  have : (qcSmallOpensFunctor S (U.obj n)).IsContinuous
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (S.qcSite.smallOverTopology (U.obj n)) := qcSmallOpensFunctor_isContinuous S (U.obj n)
  have : (SimplicialOver.toComponentOver (qcSmallSimplicialObject S U)
      (qcSmallAugmentation S X U a) n).IsDenseSubsite (S.qcSite.smallOverTopology (U.obj n))
      (qcSmallDegreeTopology S X U a n) :=
    SimplicialOver.componentOverEquivalence_inverse_isDenseSubsite (qcSmallSimplicialObject S U)
      (qcSmallAugmentation S X U a) S.qcSite.smallPretopology.toGrothendieck n
  rw [qcSmallComparisonDegree_eq]
  exact Functor.isContinuous_comp _ _ _ (S.qcSite.smallOverTopology (U.obj n)) _

end Sites

/-! ### Sheaves on `U_Zar` are detected degreewise -/

/-- A morphism of sheaves on the site `Z_Zar` of a simplicial space is an isomorphism as soon as
its restriction to every simplicial degree is. -/
theorem isIso_of_isIso_levelFunctor_sheafPushforwardContinuous_map
    {Z : SimplicialObject TopCat.{u}} {A : Type*} [Category* A]
    {G G' : Sheaf (SimplicialOpen.grothendieckTopology Z) A} (f : G ⟶ G')
    (h : ∀ n : SimplexCategoryᵒᵖ,
      haveI := levelFunctor_isContinuous Z n
      IsIso (((levelFunctor Z n).sheafPushforwardContinuous A
        (Opens.grothendieckTopology (Z.obj n)) (SimplicialOpen.grothendieckTopology Z)).map f)) :
    IsIso f := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro B
  have := levelFunctor_isContinuous Z B.unop.degree
  have h₁ := h B.unop.degree
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app] at h₁
  exact h₁ (op B.unop.toOpens)

/-- A sheaf with values in a preadditive category on the site `Z_Zar` of a simplicial space is
zero as soon as its restriction to every simplicial degree is. -/
theorem isZero_of_isZero_levelFunctor_sheafPushforwardContinuous_obj
    {Z : SimplicialObject TopCat.{u}} {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    {G : Sheaf (SimplicialOpen.grothendieckTopology Z) A}
    (h : ∀ n : SimplexCategoryᵒᵖ,
      haveI := levelFunctor_isContinuous Z n
      IsZero (((levelFunctor Z n).sheafPushforwardContinuous A
        (Opens.grothendieckTopology (Z.obj n)) (SimplicialOpen.grothendieckTopology Z)).obj G)) :
    IsZero G := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun B ↦ ?_)
  have := levelFunctor_isContinuous Z B.unop.degree
  exact congrArg (fun f ↦ f.hom.app (op B.unop.toOpens)) ((h B.unop.degree).eq_of_src (𝟙 _) 0)

/-! ### The comparison in one simplicial degree -/

section Degree

variable (n : SimplexCategoryᵒᵖ)

/-- The functor `V ↦ V/U_n` on the opens of `U_n` is continuous. -/
instance qcSmallOpensFunctor_degree_isContinuous :
    (qcSmallOpensFunctor S (U.obj n)).IsContinuous
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (S.qcSite.smallOverTopology (U.obj n)) :=
  qcSmallOpensFunctor_isContinuous S (U.obj n)

/-- The topos of the degree-`n` site of `(LC_qc/U)_total` is the topos of `LC_qc/U_n`: the
degree-`n` site `(LC_qc/X)/(U_n/X)` is the slice `LC_qc/U_n`. -/
def qcSmallDegreeSheafEquivalence :
    Sheaf (qcSmallDegreeTopology S X U a n) (Type u) ≌
      Sheaf (S.qcSite.smallOverTopology (U.obj n)) (Type u) :=
  haveI : Functor.IsDenseSubsite (S.qcSite.smallOverTopology (U.obj n))
      (qcSmallDegreeTopology S X U a n) (SimplicialOver.componentOverEquivalence
        (qcSmallSimplicialObject S U) (qcSmallAugmentation S X U a) n).inverse :=
    SimplicialOver.componentOverEquivalence_inverse_isDenseSubsite (qcSmallSimplicialObject S U)
      (qcSmallAugmentation S X U a) S.qcSite.smallPretopology.toGrothendieck n
  (SimplicialOver.componentOverEquivalence (qcSmallSimplicialObject S U)
    (qcSmallAugmentation S X U a) n).sheafCongr _ _ _

/-- Restriction along the comparison functor of degree `n` is the identification of the
degree-`n` topos with that of `LC_qc/U_n` followed by restriction along `V ↦ V/U_n`. -/
def qcSmallComparisonDegreePushforwardIso :
    (qcSmallDegreeSheafEquivalence S X U a n).functor ⋙
        (qcSmallOpensFunctor S (U.obj n)).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
          (S.qcSite.smallOverTopology (U.obj n)) ≅
      (qcSmallComparisonDegree S X U a n).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (qcSmallDegreeTopology S X U a n) :=
  NatIso.ofComponents (fun _ ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _))
    (fun _ ↦ by
      apply Sheaf.hom_ext
      rfl)

/-- The inverse image along the comparison functor of degree `n` is the inverse image
`a_{U_n}^{-1}` of the comparison morphism of `U_n` (Section 09WY) followed by the identification
of the topos of `LC_qc/U_n` with the degree-`n` topos. -/
def qcSmallComparisonDegreePullbackIso :
    (qcSmallComparisonDegree S X U a n).sheafPullback (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (qcSmallDegreeTopology S X U a n) ≅
      (qcSmallBottomMorphism S (U.obj n)).inverseImage ⋙
        (qcSmallDegreeSheafEquivalence S X U a n).inverse :=
  ((qcSmallComparisonDegree S X U a n).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (qcSmallDegreeTopology S X U a n)).leftAdjointUniq
    ((((qcSmallBottomMorphism S (U.obj n)).adj.ofNatIsoRight
        (qcSmallBottomPushforwardIso S (U.obj n))).comp
      (qcSmallDegreeSheafEquivalence S X U a n).symm.toAdjunction).ofNatIsoRight
        (qcSmallComparisonDegreePushforwardIso S X U a n))

/-- The inverse image along the comparison functor of degree `n` is fully faithful (Stacks 09X3
in simplicial degree `n`). -/
def qcSmallComparisonDegreePullbackFullyFaithful :
    ((qcSmallComparisonDegree S X U a n).sheafPullback (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (qcSmallDegreeTopology S X U a n)).FullyFaithful :=
  Functor.FullyFaithful.ofIso
    ((qcSmallBottomMorphismOfSizeInverseImageFullyFaithful.{u, w, u} S (U.obj n)).comp
      (qcSmallDegreeSheafEquivalence S X U a n).fullyFaithfulInverse)
    (qcSmallComparisonDegreePullbackIso S X U a n).symm

/-- The unit of the comparison adjunction of degree `n` is an isomorphism. -/
instance isIso_qcSmallComparisonDegree_sheafAdjunctionContinuous_unit :
    IsIso ((qcSmallComparisonDegree S X U a n).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (qcSmallDegreeTopology S X U a n)).unit :=
  haveI := (qcSmallComparisonDegreePullbackFullyFaithful S X U a n).full
  haveI := (qcSmallComparisonDegreePullbackFullyFaithful S X U a n).faithful
  Adjunction.unit_isIso_of_L_fully_faithful _

end Degree

/-! ### Stacks 0D96 for `h`: the Beck–Chevalley comparison -/

section BeckChevalley

variable (n : SimplexCategoryᵒᵖ)

/-- The square of direct images of the square of component inclusions:
`(u_n)_* ⋙ (ℓ_n)_* ≅ (ι_n)_* ⋙ h_*` given by the base change of right Kan extensions along the
square of component inclusions. -/
abbrev qcSmallComparisonPushforwardSquareIso :
    (qcSmallComparisonDegree S X U a n).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (qcSmallDegreeTopology S X U a n) ⋙
      (levelFunctor (qcSimplicialSpace S U) n).sheafPushforwardCocontinuous (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) ≅
    (qcSmallTotalIota S X U a n).sheafPushforwardCocontinuous (Type u)
        (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a) ⋙
      (qcSmallComparisonMorphism S X U a).pushforward :=
  (Functor.fullyFaithfulCancelRight
    (sheafToPresheaf (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (Type u))
    (Functor.isoWhiskerLeft (sheafToPresheaf (qcSmallDegreeTopology S X U a n) (Type u))
      (asIso ((qcSmallLevelSquare S X U a n).op.ranBaseChange (D := Type u))))).symm

/-- The commutation `r_n ∘ h_* ⟶ h_{n,*} ∘ ρ_n` of the restrictions to degree `n` with the direct
images of `h` and of the comparison of degree `n`: the mate of the square of direct images along
the adjunctions of the component inclusions. -/
abbrev qcSmallComparisonRestrictSquare :
    TwoSquare (qcSmallComparisonMorphism S X U a).pushforward
      ((qcSmallTotalIota S X U a n).sheafPushforwardContinuous (Type u)
        (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a))
      ((levelFunctor (qcSimplicialSpace S U) n).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)))
      ((qcSmallComparisonDegree S X U a n).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (qcSmallDegreeTopology S X U a n)) :=
  (mateEquiv ((qcSmallTotalIota S X U a n).sheafAdjunctionCocontinuous (Type u)
      (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a))
    ((levelFunctor (qcSimplicialSpace S U) n).sheafAdjunctionCocontinuous (Type u)
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)))).symm
    (TwoSquare.mk _ _ _ _ (qcSmallComparisonPushforwardSquareIso S X U a n).inv)

/-- The commutation `r_n ∘ h_* ⟶ h_{n,*} ∘ ρ_n` is an isomorphism. -/
instance isIso_qcSmallComparisonRestrictSquare :
    IsIso (qcSmallComparisonRestrictSquare S X U a n).natTrans :=
  isIso_sheafPushforwardContinuousSquareMateOfLarge _ _ _ _ _ _ _ _ _

/-- The Beck–Chevalley comparison of Stacks 0D96 for `h`: the comparison
`h_n^{-1} ∘ r_n ⟶ ρ_n ∘ h^{-1}` between restricting to degree `n` and then pulling back along the
comparison of degree `n`, and pulling back along `h` and then restricting to degree `n`. It is the
mate of `qcSmallComparisonRestrictSquare` along the adjunctions of `h` and of the comparison of
degree `n`. -/
abbrev qcSmallComparisonBeckChevalley :
    TwoSquare ((levelFunctor (qcSimplicialSpace S U) n).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)))
      (qcSmallComparisonMorphism S X U a).inverseImage
      ((qcSmallComparisonDegree S X U a n).sheafPullback (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (qcSmallDegreeTopology S X U a n))
      ((qcSmallTotalIota S X U a n).sheafPushforwardContinuous (Type u)
        (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a)) :=
  (mateEquiv (qcSmallComparisonMorphism S X U a).adj
    ((qcSmallComparisonDegree S X U a n).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (qcSmallDegreeTopology S X U a n))).symm (qcSmallComparisonRestrictSquare S X U a n)

/-- Stacks 0D96 for `h`: the Beck–Chevalley comparison is an isomorphism, so restricting the
inverse image `h^{-1}G` to degree `n` is pulling back the restriction of `G` along the comparison
of degree `n`. -/
instance isIso_qcSmallComparisonBeckChevalley :
    IsIso (qcSmallComparisonBeckChevalley S X U a n).natTrans := by
  let adj₁ := (qcSmallComparisonMorphism S X U a).adj
  let adj₂ := (qcSmallComparisonDegree S X U a n).sheafAdjunctionContinuous (Type u)
    (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
    (qcSmallDegreeTopology S X U a n)
  let adj₃ := (levelFunctor (qcSimplicialSpace S U) n).sheafAdjunctionCocontinuous (Type u)
    (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
    (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
  let adj₄ := (qcSmallTotalIota S X U a n).sheafAdjunctionCocontinuous (Type u)
    (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a)
  have key := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄
    (qcSmallComparisonBeckChevalley S X U a n)
  have h₁ : mateEquiv adj₁ adj₂ (qcSmallComparisonBeckChevalley S X U a n) =
      qcSmallComparisonRestrictSquare S X U a n :=
    Equiv.apply_symm_apply _ _
  have h₂ : mateEquiv adj₄ adj₃ (qcSmallComparisonRestrictSquare S X U a n) =
      TwoSquare.mk _ _ _ _ (qcSmallComparisonPushforwardSquareIso S X U a n).inv :=
    Equiv.apply_symm_apply _ _
  rw [h₁, h₂] at key
  have : IsIso (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)
      (qcSmallComparisonBeckChevalley S X U a n).natTrans) := by
    rw [← key]
    exact inferInstanceAs (IsIso (qcSmallComparisonPushforwardSquareIso S X U a n).inv)
  exact conjugateEquiv_of_iso (adj₁.comp adj₄) (adj₃.comp adj₂) _

/-- The unit `G ⟶ h_* h^{-1} G` of the comparison morphism `h : Sh((LC_qc/U)_total) → Sh(U_Zar)`
of Stacks 0DAF is an isomorphism for every sheaf of sets `G` on `U_Zar`. -/
instance isIso_qcSmallComparisonMorphism_adj_unit :
    IsIso (qcSmallComparisonMorphism S X U a).adj.unit := by
  have : ∀ G, IsIso ((qcSmallComparisonMorphism S X U a).adj.unit.app G) := by
    intro G
    apply isIso_of_isIso_levelFunctor_sheafPushforwardContinuous_map
    intro n
    have hf := unit_mateEquiv_symm (qcSmallComparisonMorphism S X U a).adj
      ((qcSmallComparisonDegree S X U a n).sheafAdjunctionContinuous (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (qcSmallDegreeTopology S X U a n)) (qcSmallComparisonRestrictSquare S X U a n) G
    have h₂ : IsIso (((qcSmallComparisonDegree S X U a n).sheafAdjunctionContinuous (Type u)
          (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
          (qcSmallDegreeTopology S X U a n)).unit.app _ ≫
        ((qcSmallComparisonDegree S X U a n).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
          (qcSmallDegreeTopology S X U a n)).map
          ((qcSmallComparisonBeckChevalley S X U a n).natTrans.app G)) := inferInstance
    have : IsIso (((levelFunctor (qcSimplicialSpace S U) n).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
        (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))).map
          ((qcSmallComparisonMorphism S X U a).adj.unit.app G) ≫
        (qcSmallComparisonRestrictSquare S X U a n).natTrans.app
          ((qcSmallComparisonMorphism S X U a).inverseImage.obj G)) := by
      rwa [hf]
    exact IsIso.of_isIso_comp_right _ ((qcSmallComparisonRestrictSquare S X U a n).natTrans.app _)
  exact NatIso.isIso_of_isIso_app _

end BeckChevalley

end Stacks.Topology.Simplicial

end
