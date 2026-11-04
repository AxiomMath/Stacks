module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Grothendieck.MapEquivalence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianCrossCriterion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalIsSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphism

/-!
# Total sites of degreewise equivalent simplicial sites

Let `h : C ⟶ C'` be a morphism of simplicial families of sites in case (B) whose components
`h_n : C_n ⥤ C'_n` are equivalences of categories, continuous and cocontinuous. The functor
`h_total` between the total sites is then an equivalence of categories, and restriction along it
is an equivalence `Sh(C'_total) ≌ Sh(C_total)` which preserves and reflects cartesian sheaves.
Consequently descent along an augmentation can be transported from one total site to the other.

## Main results

All names are in the namespace `CategoryTheory.CocontinuousSimplicialSite`.

* `isContinuous_of_ι_overSimplicialObjectComparison`: a functor out of a total site is
  continuous as soon as it is continuous in every simplicial degree.
* `Morphism.isDenseSubsite_totalFunctor_totalSiteEquivalence`: when every component of `h` is a
  continuous and cocontinuous equivalence, `h_total` exhibits the total site of `C` as a dense
  subsite of that of `C'`.
* `Morphism.isCartesianSheaf_restrict_iff_totalSiteEquivalence`: restriction along `h_total`
  preserves and reflects cartesian sheaves.
* `Morphism.descent_of_descent_totalSiteEquivalence`: if restriction along
  `F₁ ≅ h_total ⋙ F₂` is fully faithful with essential image the cartesian sheaves, so is
  restriction along `F₂`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.CocontinuousSimplicialSite

variable (C : CocontinuousSimplicialSite.{u})

/-- A functor out of the total site of a simplicial family of sites in case (B) is continuous as
soon as its restriction to every simplicial degree is. -/
theorem isContinuous_of_ι_overSimplicialObjectComparison {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) (F : Grothendieck C.underlying ⥤ D)
    (hF : ∀ n, (Grothendieck.ι C.underlying n ⋙ F).IsContinuous
      (topologyOfCoverings (C.coverage n)) K) :
    F.IsContinuous (SimplicialCoverings.totalTopology C.underlying C.coverage) K where
  op_comp_isSheaf_of_types G := by
    refine isSheaf_topologyOfCoverings
      (SimplicialCoverings.total_isSite C.underlying C.coverage C.isSite
        (fun α ↦ C.isCocontinuous α) (fun α ↦ C.hasCoverPullbacks α)) _ ?_
    intro A E hE
    obtain ⟨E', hE', hEeq⟩ : ∃ E'' : PreZeroHypercover.{u} A.fiber,
        C.coverage A.base ⟨A.fiber, E''⟩ ∧ E = E''.map (Grothendieck.ι C.underlying A.base) := hE
    subst hEeq
    have := hF A.base
    exact Presieve.isSheafFor_presieve₀_map (Grothendieck.ι C.underlying A.base) _ E'
      ((Presieve.isSheafFor_iff_generate _).mpr
        ((Functor.IsContinuous.op_comp_isSheaf_of_types
          (F := Grothendieck.ι C.underlying A.base ⋙ F)
          (J := topologyOfCoverings (C.coverage A.base)) (K := K) G) _
          (Precoverage.generate_mem_toGrothendieck ⟨E', hE', rfl⟩)))

namespace Morphism

variable {C} {C' : CocontinuousSimplicialSite.{u}} (h : Morphism C C')

/-- The functor between total sites is continuous when every component is. -/
theorem totalFunctor_isContinuous_totalSiteEquivalence
    (hc : ∀ n, (h.hom.app n).toFunctor.IsContinuous (topologyOfCoverings (C.coverage n))
      (topologyOfCoverings (C'.coverage n))) :
    h.totalFunctor.IsContinuous (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
  isContinuous_of_ι_overSimplicialObjectComparison C _ _ fun n ↦ by
    rw [ι_comp_totalFunctor]
    have := hc n
    have : (Grothendieck.ι C'.underlying n).IsContinuous (topologyOfCoverings (C'.coverage n))
        (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
      SimplicialSiteSituation.componentFunctor_isContinuous (situation C') n.unop
    exact Functor.isContinuous_comp _ _ _ (topologyOfCoverings (C'.coverage n)) _

variable [∀ n, (h.hom.app n).toFunctor.IsEquivalence]
  (hc : ∀ n, (h.hom.app n).toFunctor.IsContinuous (topologyOfCoverings (C.coverage n))
    (topologyOfCoverings (C'.coverage n)))

/-- The functor between total sites is an equivalence of categories when every component is. -/
instance isEquivalence_totalFunctor_totalSiteEquivalence : h.totalFunctor.IsEquivalence :=
  Grothendieck.isEquivalence_map_mapEquivalence h.hom

include hc in
/-- When every component is an equivalence of categories which is continuous and cocontinuous,
the functor between total sites exhibits the total site of `C` as a dense subsite of that of
`C'`. -/
theorem isDenseSubsite_totalFunctor_totalSiteEquivalence :
    h.totalFunctor.IsDenseSubsite (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) := by
  let eqv := h.totalFunctor.asEquivalence
  have : eqv.functor.IsCocontinuous (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    totalFunctor_isCocontinuous h
  have : eqv.functor.IsContinuous (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    totalFunctor_isContinuous_totalSiteEquivalence h hc
  have : eqv.inverse.IsCocontinuous (SimplicialCoverings.totalTopology C'.underlying C'.coverage)
      (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
    (eqv.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
      (CoverPreserving.of_isContinuous eqv.functor _ _)
  exact Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ eqv

include hc in
/-- Restriction of sheaves of sets along the functor between total sites is an equivalence. -/
theorem isEquivalence_sheafPushforwardContinuous_totalSiteEquivalence
    [h.totalFunctor.IsContinuous (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage)] :
    (h.totalFunctor.sheafPushforwardContinuous (Type u)
      (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage)).IsEquivalence := by
  have := isDenseSubsite_totalFunctor_totalSiteEquivalence h hc
  have : h.totalFunctor.IsCocontinuous (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) :=
    totalFunctor_isCocontinuous h
  infer_instance

/-- In a commutative square whose left and bottom sides are isomorphisms, a presheaf inverts the
top side exactly when it inverts the right side. -/
private theorem isIso_map_op_iff_of_comp_eq {J D : Type*} [Category* J] [Category* D]
    (P : Jᵒᵖ ⥤ D) {X Y Z W : J} {f : X ⟶ Y} {g : Y ⟶ W} {f' : X ⟶ Z} {g' : Z ⟶ W}
    (w : f ≫ g = f' ≫ g') [IsIso f] [IsIso g'] :
    IsIso (P.map g.op) ↔ IsIso (P.map f'.op) := by
  have e : P.map g.op ≫ P.map f.op = P.map g'.op ≫ P.map f'.op := by
    simp only [← Functor.map_comp, ← op_comp, w]
  rw [← isIso_comp_right_iff _ (P.map f.op), e, isIso_comp_left_iff]

/-- A presheaf on a Grothendieck construction inverts a morphism with invertible fibre component
exactly when it inverts the cross arrow of its base. -/
theorem _root_.CategoryTheory.Grothendieck.isIso_map_op_iff_of_isIso_fiber_totalSiteEquivalence
    {I : Type*} [Category* I] {F : I ⥤ Cat.{u, u}} {X Y : Grothendieck F} (k : X ⟶ Y)
    [IsIso k.fiber] (P : (Grothendieck F)ᵒᵖ ⥤ Type u) :
    IsIso (P.map k.op) ↔ IsIso (P.map ((Grothendieck.ιNatTrans k.base).app X.fiber).op) := by
  have w := (Category.id_comp k).trans
    (Grothendieck.ιNatTrans_app_comp_ι_map (G := F) k.base (d := X.fiber) (e := Y.fiber)
      k.fiber).symm
  have : IsIso ((Grothendieck.ι F Y.base).map k.fiber) := Functor.map_isIso _ _
  exact @isIso_map_op_iff_of_comp_eq _ _ _ _ P _ _ _ _ _ _ _ _ w (IsIso.id X) this

omit [∀ n, (h.hom.app n).toFunctor.IsEquivalence] in
/-- The fibre component of the image of a cross arrow under the functor between total sites is
invertible. -/
theorem isIso_totalFunctor_map_ιNatTrans_app_fiber_totalSiteEquivalence {m n : SimplexCategory}
    (φ : m ⟶ n) (x : C.underlying.obj (op n)) :
    IsIso (h.totalFunctor.map ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app x)).fiber :=
  have : IsIso ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app x).fiber :=
    (inferInstance : IsIso (𝟙 _))
  Grothendieck.isIso_map_map_fiber_mapEquivalence h.hom _

variable (hcC : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n),
    (C.underlying.map φ.op).toFunctor.IsContinuous
      ((situation C).componentTopology n) ((situation C).componentTopology m))
  (hcC' : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n),
    (C'.underlying.map φ.op).toFunctor.IsContinuous
      ((situation C').componentTopology n) ((situation C').componentTopology m))

include hcC hcC' in
/-- When every component is an equivalence of categories, a sheaf of sets on the total site of
`C'` is cartesian if and only if its restriction to the total site of `C` is. -/
theorem isCartesianSheaf_restrict_iff_totalSiteEquivalence
    [h.totalFunctor.IsContinuous (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage)]
    (G : Sheaf (SimplicialCoverings.totalTopology C'.underlying C'.coverage) (Type u)) :
    (situation C).IsCartesianSheaf ((h.totalFunctor.sheafPushforwardContinuous (Type u)
      (SimplicialCoverings.totalTopology C.underlying C.coverage)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage)).obj G) ↔
      (situation C').IsCartesianSheaf G := by
  refine (isCartesianSheaf_iff_bijective_cartesianCrossCriterion C hcC _).trans
    (Iff.trans ?_ (isCartesianSheaf_iff_bijective_cartesianCrossCriterion C' hcC' G).symm)
  have key : ∀ {m n : SimplexCategory} (φ : m ⟶ n) (x : C.underlying.obj (op n)),
      IsIso (G.obj.map (h.totalFunctor.map
        ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app x)).op) ↔
      IsIso (G.obj.map ((Grothendieck.ιNatTrans (F := C'.underlying) φ.op).app
        ((h.hom.app (op n)).toFunctor.obj x)).op) := by
    intro m n φ x
    have := isIso_totalFunctor_map_ιNatTrans_app_fiber_totalSiteEquivalence h φ x
    exact Grothendieck.isIso_map_op_iff_of_isIso_fiber_totalSiteEquivalence
      (h.totalFunctor.map ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app x)) G.obj
  constructor
  · intro hE m n φ y
    let x := (h.hom.app (op n)).toFunctor.objPreimage y
    let e := (h.hom.app (op n)).toFunctor.objObjPreimageIso y
    have h₁ : IsIso (G.obj.map ((Grothendieck.ιNatTrans (F := C'.underlying) φ.op).app
        ((h.hom.app (op n)).toFunctor.obj x)).op) :=
      (key φ x).1 ((isIso_iff_bijective _).2 (hE φ x))
    exact (isIso_iff_bijective _).1
      ((isIso_map_op_iff_of_comp_eq G.obj
        ((Grothendieck.ιNatTrans (F := C'.underlying) φ.op).naturality e.hom)).2 h₁)
  · intro hG m n φ x
    exact (isIso_iff_bijective _).1 ((key φ x).2 ((isIso_iff_bijective _).2 (hG φ _)))

include hc hcC hcC' in
/-- **Transport of descent between total sites.** Let `F₁` and `F₂` be continuous functors from
the total sites of `C` and of `C'` to a site `D`, with `h_total ⋙ F₂ ≅ F₁`. If restriction along
`F₁` is fully faithful on sheaves of sets with essential image the cartesian sheaves, then so is
restriction along `F₂`. -/
theorem descent_of_descent_totalSiteEquivalence {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) (F₁ : Grothendieck C.underlying ⥤ D)
    (F₂ : Grothendieck C'.underlying ⥤ D)
    [F₁.IsContinuous (SimplicialCoverings.totalTopology C.underlying C.coverage) K]
    [F₂.IsContinuous (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K]
    (e : h.totalFunctor ⋙ F₂ ≅ F₁)
    (hff : Nonempty (F₁.sheafPushforwardContinuous (Type u)
      (SimplicialCoverings.totalTopology C.underlying C.coverage) K).FullyFaithful)
    (hess : ∀ G : Sheaf (SimplicialCoverings.totalTopology C.underlying C.coverage) (Type u),
      (F₁.sheafPushforwardContinuous (Type u)
        (SimplicialCoverings.totalTopology C.underlying C.coverage) K).essImage G ↔
        (situation C).IsCartesianSheaf G) :
    Nonempty (F₂.sheafPushforwardContinuous (Type u)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K).FullyFaithful ∧
      ∀ G : Sheaf (SimplicialCoverings.totalTopology C'.underlying C'.coverage) (Type u),
        (F₂.sheafPushforwardContinuous (Type u)
          (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K).essImage G ↔
          (situation C').IsCartesianSheaf G := by
  have := totalFunctor_isContinuous_totalSiteEquivalence h hc
  have := isEquivalence_sheafPushforwardContinuous_totalSiteEquivalence h hc
  let R := h.totalFunctor.sheafPushforwardContinuous (Type u)
    (SimplicialCoverings.totalTopology C.underlying C.coverage)
    (SimplicialCoverings.totalTopology C'.underlying C'.coverage)
  let iso : F₂.sheafPushforwardContinuous (Type u)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K ⋙ R ≅
      F₁.sheafPushforwardContinuous (Type u)
        (SimplicialCoverings.totalTopology C.underlying C.coverage) K :=
    Functor.sheafPushforwardContinuousComp' e (Type u) _ _ K
  have hR : R.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful R
  refine ⟨⟨Functor.FullyFaithful.ofCompFaithful (G := R) (hff.some.ofIso iso.symm)⟩, fun G ↦ ?_⟩
  have h₁ : (F₂.sheafPushforwardContinuous (Type u)
      (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K).essImage G ↔
      (F₂.sheafPushforwardContinuous (Type u)
        (SimplicialCoverings.totalTopology C'.underlying C'.coverage) K ⋙ R).essImage (R.obj G) :=
    ⟨fun ⟨X, ⟨i⟩⟩ ↦ ⟨X, ⟨R.mapIso i⟩⟩, fun ⟨X, ⟨i⟩⟩ ↦ ⟨X, ⟨hR.preimageIso i⟩⟩⟩
  rw [h₁, Functor.essImage_eq_of_natIso iso]
  exact (hess _).trans (isCartesianSheaf_restrict_iff_totalSiteEquivalence h hcC hcC' G)

end Morphism

end CategoryTheory.CocontinuousSimplicialSite
