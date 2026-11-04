module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Trace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.ModuleRestrictionTrace
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.CategoryTheory.Sites.SurjectivityFromGraphCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteBaseChangeAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison

/-!
# Restriction followed by the trace is multiplication by the degree

Let `U ⟶ X` be finite étale, presented as an object of the small étale site of `X` inside a big
étale site. The restriction map `ℱ ⟶ j_* j⁻¹ ℱ` followed by the trace `j_* j⁻¹ ℱ ⟶ ℱ` of
Stacks Tag 03SE acts, over an étale `Q ⟶ X` over which `U` splits into `n` sheets, as
multiplication by `n` (Étale Cohomology, Section 03SH). If every such splitting over a nonempty
`Q` has `n = d` sheets, the composite is multiplication by `d`.

## Main definitions

* `AlgebraicGeometry.abelianRestrictionUnit`: the restriction map `ℱ ⟶ j_* j⁻¹ ℱ`.

## Main results

* `AlgebraicGeometry.abelianTrace_app_restrictionUnit_of_split`: over a split `Q` the composite
  is multiplication by the number of sheets.
* `AlgebraicGeometry.abelianRestrictionUnit_comp_abelianTrace`: the composite is multiplication
  by `d`, given that every splitting has `d` sheets.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

/-- The base change of `pullback.fst v u` along `q` is `pullback.fst (q ≫ v) u`. -/
private theorem IsPullback.pullback_lift_fst_comp {C : Type*} [Category* C] {Q V Z U : C}
    (f : Q ⟶ Z) (q : Q ⟶ V) (v : V ⟶ Z) (u : U ⟶ Z) (hq : q ≫ v = f)
    [HasPullback f u] [HasPullback v u] :
    IsPullback (pullback.lift (pullback.fst f u ≫ q) (pullback.snd f u)
        (by rw [Category.assoc, hq, pullback.condition]))
      (pullback.fst f u) (pullback.fst v u) q := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback v u).flip
  rw [pullback.lift_snd, hq]
  exact (IsPullback.of_hasPullback f u).flip

/-- Conjugating by the counit of an additive equivalence preserves `x ≫ y = d • 𝟙`. -/
private theorem Equivalence.counitIso_conj_comp_eq_nsmul {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (e : C ≌ D) [e.functor.Additive] {A B : D}
    (x : e.inverse.obj A ⟶ e.inverse.obj B) (y : e.inverse.obj B ⟶ e.inverse.obj A) (d : ℕ)
    (h : x ≫ y = d • 𝟙 _) :
    ((e.counitIso.app A).inv ≫ e.functor.map x ≫ (e.counitIso.app B).hom) ≫
      (e.counitIso.app B).inv ≫ e.functor.map y ≫ (e.counitIso.app A).hom = d • 𝟙 A := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← e.functor.map_comp_assoc, h, Functor.map_nsmul, Functor.map_id]
  simp

end CategoryTheory

namespace CategoryTheory.Presheaf

/-- **The explicit preimage in `CategoryTheory.Presheaf.surjective_app_of_graphCover`**: a section
of `G` over `R.obj Q` is `θ` of the sum of the sections `η (W i)` of its restrictions to the
graphs. -/
theorem app_sum_of_graphCover
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    (L : D ⥤ C) (R : C ⥤ D)
    (J : GrothendieckTopology D) (G : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hG : Presheaf.IsSeparated J G)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (θ : H ⟶ R.op ⋙ G)
    (η : ∀ W, G.obj (Opposite.op W) ⟶ H.obj (Opposite.op (L.obj W)))
    (graph : ∀ W, W ⟶ R.obj (L.obj W))
    (hdiag : ∀ W s, G.map (graph W).op (θ.app _ (η W s)) = s)
    {Q : C} {ι : Type*} [Fintype ι] (W : ι → D) (e : ∀ i, L.obj (W i) ≅ Q)
    (hcov : Sieve.generate (Presieve.ofArrows W
      (fun i => graph (W i) ≫ R.map (e i).hom)) ∈ J (R.obj Q))
    (hoff : ∀ i j, i ≠ j → ∀ s,
      G.map ((graph (W j) ≫ R.map (e j).hom) ≫ R.map (e i).inv).op
        (θ.app _ (η (W i) s)) = 0)
    (s : G.obj (Opposite.op (R.obj Q))) :
    θ.app (Opposite.op Q) (∑ i, H.map (e i).inv.op
      (η (W i) (G.map (graph (W i) ≫ R.map (e i).hom).op s))) = s := by
  classical
  let g i := graph (W i) ≫ R.map (e i).hom
  let t i := G.map (g i).op s
  let x i := H.map (e i).inv.op (η (W i) (t i))
  show θ.app (Opposite.op Q) (∑ i, x i) = s
  rw [map_sum]
  apply hG (R.obj Q) _ hcov
  intro T f hf
  obtain ⟨Z, a, b, hb, hab⟩ := hf
  obtain ⟨j⟩ := hb
  have hx : ∀ i (y : H.obj (Opposite.op (L.obj (W i)))),
      G.map (g j).op (θ.app (Opposite.op Q) (H.map (e i).inv.op y)) =
        G.map ((graph (W j) ≫ R.map (e j).hom) ≫ R.map (e i).inv).op (θ.app _ y) := by
    intro i y
    change G.map (g j).op ((H.map (e i).inv.op ≫ θ.app _) y) = _
    rw [θ.naturality]
    change G.map (g j).op (G.map (R.map (e i).inv).op (θ.app _ y)) = _
    rw [← Functor.map_comp_apply, ← op_comp]
  have hres : G.map (g j).op (∑ i, θ.app (Opposite.op Q) (x i)) =
      G.map (g j).op s := by
    rw [map_sum, Finset.sum_eq_single j]
    · rw [hx]
      change _ = t j
      simpa [g, ← R.map_comp] using hdiag (W j) (t j)
    · intro i hi hij
      rw [hx]
      exact hoff i j hij (t i)
    · simp
  rw [← hab, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hres]

end CategoryTheory.Presheaf

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-- The base change of a finite étale morphism of rank `d` is finite étale of rank `d`. -/
private theorem isFinite_etale_rank_of_isPullback {P X Y S : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback fst snd f g) [IsFinite f] [Etale f]
    (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] :
    IsFinite snd ∧ Etale snd ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank snd d :=
  ⟨MorphismProperty.of_isPullback h inferInstance, MorphismProperty.of_isPullback h inferInstance,
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback h⟩

/-- **The number of sheets of a split finite étale morphism is its degree.** If `f : X ⟶ S` is
finite étale of rank `d` and has sheet data over a nonempty `q : V ⟶ S`, there are `d` sheets: at
a geometric point of `V` the sections of the geometric fibre of `f` are exactly the sheets, and a
finite étale scheme over a separably closed field has as many rational points as its degree. -/
theorem IsSplitOver.natCard_I {X S V : Scheme.{u}} {f : X ⟶ S} {q : V ⟶ S}
    (h : IsSplitOver f q) [IsFinite f] [Etale f] {d : ℕ}
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] [Nonempty V] : Nat.card h.I = d := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  set x := Stacks.EtaleCohomology.residueGeometricPoint V v
  set z := x ≫ q
  have sq : IsPullback (pullback.fst f z) (pullback.snd f z) f z := IsPullback.of_hasPullback f z
  obtain ⟨-, -, hd⟩ := isFinite_etale_rank_of_isPullback sq d
  have heq : Nat.card { σ : Spec (.of (SeparableClosure (V.residueField v))) ⟶ pullback f z //
      σ ≫ pullback.snd f z = 𝟙 _ } = d :=
    ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq _ _).1
      (Stacks.Morphisms.isFiniteLocallyFreeOfRank_natCard_sections _)).2.2.symm.trans
        ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq _ _).1 hd).2.2
  rw [← heq]
  have hne : Nonempty (Spec (.of (SeparableClosure (V.residueField v)))) := inferInstance
  refine Nat.card_congr (Equiv.ofBijective (fun i => ⟨pullback.lift (x ≫ h.sheet i) (𝟙 _)
    (by rw [Category.assoc, h.sheet_comp, Category.id_comp]), pullback.lift_snd _ _ _⟩) ⟨?_, ?_⟩)
  · intro i j hij
    by_contra hne'
    have hfst := congrArg (fun σ => σ.1 ≫ pullback.fst f z) hij
    simp only [pullback.lift_fst] at hfst
    exact (h.isEmpty_of_sheet_eq x hne' hfst).false hne.some
  · rintro ⟨σ, hσ⟩
    set b := σ ≫ pullback.fst f z
    have hb : b ≫ f = x ≫ q := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
    obtain ⟨κ, Y, p, hp, i, hcov, hk⟩ := h.exists_openCover x b hb
    obtain ⟨k, hk'⟩ := hcov hne.some
    have : IsOpenImmersion (p k) := hp k
    obtain ⟨y, hy⟩ := hk'
    have hsurj : Function.Surjective (p k) := fun _ => ⟨y, hy.trans (Subsingleton.elim _ _)⟩
    have : IsIso (p k) :=
      (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨hsurj⟩⟩
    refine ⟨i k, Subtype.ext ?_⟩
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using ((cancel_epi (p k)).1 (hk k)).symm
    · simpa only [pullback.lift_snd] using hσ.symm

end Stacks.Etale

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- The projection `W ×_X U ⟶ W` of the base's `AlgebraicGeometry.smallEtaleBaseChangeProj`, on
underlying schemes. -/
theorem smallEtaleBaseChangeProj_left (W : SmallEtale B X hX) :
    (smallEtaleBaseChangeProj B X hX U W).hom.left = pullback.fst W.obj.hom U.obj.hom :=
  rfl

/-- The restriction map `ℱ ⟶ j_* j⁻¹ ℱ` of abelian sheaves along `U ⟶ X`, as a map of
presheaves. -/
def abelianRestrictionUnitPresheaf
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :
    F.obj ⟶ (smallEtaleBaseChange B U.obj.hom).op ⋙
      (smallEtalePostcompose B X hX U).op ⋙ F.obj where
  app W := F.obj.map (smallEtaleBaseChangeProj B X hX U W.unop).op
  naturality W W' f := by
    change F.obj.map f ≫ F.obj.map (smallEtaleBaseChangeProj B X hX U W'.unop).op =
      F.obj.map (smallEtaleBaseChangeProj B X hX U W.unop).op ≫
        F.obj.map ((smallEtalePostcompose B X hX U).map
          ((smallEtaleBaseChange B U.obj.hom).map f.unop)).op
    rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp,
      smallEtaleBaseChangeProj_naturality]
    rfl

/-- The restriction map `ℱ ⟶ j_* j⁻¹ ℱ` of abelian sheaves along `U ⟶ X`. -/
def abelianRestrictionUnit (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :
    let := smallEtaleBaseChange_isContinuous B U.obj.hom
    F ⟶ ((smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X hX)
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property)).obj
      ((abelianRestriction B X hX U).obj F) :=
  let _ := smallEtaleBaseChange_isContinuous B U.obj.hom
  ⟨abelianRestrictionUnitPresheaf B X hX U F⟩

/-- The transported graph of `φ : Q ⟶ U`, followed by the projection to `Q`, is the identity. -/
theorem smallEtaleLiftPostIso_inv_comp_graph_comp_proj [IsSeparated (B.inclusion.map U.obj.hom)]
    (Q : SmallEtale B X hX) (φ : Q ⟶ U) :
    (smallEtaleLiftPostIso B X hX U Q φ).inv ≫
        (smallEtalePostcompose B X hX U).map (smallEtaleLiftGraph B X hX U Q φ) ≫
          smallEtaleBaseChangeProj B X hX U Q = 𝟙 Q := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  show 𝟙 Q.obj.left ≫ (smallEtaleLiftGraph B X hX U Q φ).hom.left ≫
    pullback.fst Q.obj.hom U.obj.hom = 𝟙 Q.obj.left
  rw [Category.id_comp]
  exact smallEtaleLiftGraph_fst B X hX U Q φ

/-- The counit of the extension-by-zero adjunction, applied to the transport along
`smallEtaleLiftPostIso` of the unit on the graph-restriction of `s`, returns `s`. -/
private theorem abelianExtensionByZeroAdjunction_counit_app_liftPostIso_inv
    [IsSeparated (B.inclusion.map U.obj.hom)]
    (G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (Q : SmallEtale B X hX) (φ : Q ⟶ U) (s : G.obj.obj (op Q)) :
    ((abelianExtensionByZeroAdjunction B X hX U).counit.app G).hom.app (op Q)
      (((abelianExtensionByZero B X hX U).obj ((abelianRestriction B X hX U).obj G)).obj.map
        (smallEtaleLiftPostIso B X hX U Q φ).inv.op
        (((abelianExtensionByZeroAdjunction B X hX U).unit.app
          ((abelianRestriction B X hX U).obj G)).hom.app (op (smallEtaleLift B X hX U Q φ))
          (((abelianRestriction B X hX U).obj G).obj.map
            (smallEtaleGraph B X hX U (smallEtaleLift B X hX U Q φ) ≫
              (smallEtaleBaseChange B U.obj.hom).map (smallEtaleLiftPostIso B X hX U Q φ).hom).op
            ((abelianRestrictionUnit B X hX U G).hom.app (op Q) s)))) = s := by
  let F := (abelianRestriction B X hX U).obj G
  let η := fun W => ((abelianExtensionByZeroAdjunction B X hX U).unit.app F).hom.app (op W)
  set s' := (abelianRestrictionUnit B X hX U G).hom.app (op Q) s
  set ε := (abelianExtensionByZeroAdjunction B X hX U).counit.app G
  let t := F.obj.map (smallEtaleGraph B X hX U (smallEtaleLift B X hX U Q φ) ≫
    (smallEtaleBaseChange B U.obj.hom).map (smallEtaleLiftPostIso B X hX U Q φ).hom).op s'
  refine (ConcreteCategory.congr_hom
    (ε.hom.naturality (smallEtaleLiftPostIso B X hX U Q φ).inv.op)
    (η (smallEtaleLift B X hX U Q φ) t)).trans ?_
  have htri : ε.hom.app (op ((smallEtalePostcompose B X hX U).obj
      (smallEtaleLift B X hX U Q φ))) (η (smallEtaleLift B X hX U Q φ) t) = t :=
    ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app
      (op (smallEtaleLift B X hX U Q φ)))
      ((abelianExtensionByZeroAdjunction B X hX U).right_triangle_components G)) t
  refine (congrArg (G.obj.map (smallEtaleLiftPostIso B X hX U Q φ).inv.op) htri).trans ?_
  show G.obj.map (smallEtaleLiftPostIso B X hX U Q φ).inv.op
      (G.obj.map ((smallEtalePostcompose B X hX U).map
        (smallEtaleLiftGraph B X hX U Q φ)).op
        (G.obj.map (smallEtaleBaseChangeProj B X hX U Q).op s)) = s
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← G.obj.map_comp,
    ← G.obj.map_comp, ← op_comp, ← op_comp, Category.assoc,
    smallEtaleLiftPostIso_inv_comp_graph_comp_proj, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **Over a split étale object, restriction followed by the trace is multiplication by the number
of sheets.** -/
theorem abelianTrace_app_restrictionUnit_of_split [IsFinite (B.inclusion.map U.obj.hom)]
    (G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (Q : SmallEtale B X hX) {ι : Type u} [Finite ι] (φ : ι → (Q ⟶ U))
    (hcov : ∀ z : ((smallEtaleBaseChange B U.obj.hom).obj Q).obj.left.1, ∃ i,
      z ∈ Set.range (B.inclusion.map (smallEtaleLiftGraph B X hX U Q (φ i)).hom.left))
    (hd : Pairwise (fun i j => smallEtaleArrowsDisjoint B X hX U Q (φ i) (φ j)))
    (s : G.obj.obj (op Q)) :
    ((abelianTrace B X hX U).app G).hom.app (op Q)
        ((abelianRestrictionUnit B X hX U G).hom.app (op Q) s) = Nat.card ι • s := by
  classical
  have : IsSeparated (B.inclusion.map U.obj.hom) := IsSeparated.of_isAffineHom _
  have := Fintype.ofFinite ι
  let F := (abelianRestriction B X hX U).obj G
  let θ := (abelianExtensionByZeroToPushforward B X hX U).app F
  have key := CategoryTheory.Presheaf.app_sum_of_graphCover
    (smallEtalePostcompose B X hX U)
    (smallEtaleBaseChange B U.obj.hom)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property) F.obj F.isSeparated
    ((abelianExtensionByZero B X hX U).obj F).obj θ.hom
    (fun W => ((abelianExtensionByZeroAdjunction B X hX U).unit.app F).hom.app (op W))
    (smallEtaleGraph B X hX U)
    (abelianExtensionByZeroToPushforward_graph B X hX U F)
    (fun i => smallEtaleLift B X hX U Q (φ i))
    (fun i => smallEtaleLiftPostIso B X hX U Q (φ i))
    (SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective
      B U.obj.left.1 U.obj.left.property _ _ hcov)
    (fun i j hij =>
      abelianExtensionByZeroToPushforward_graph_compl B X hX U F _ _ _
        (disjointFromSmallEtaleGraph_smallEtaleLiftGraph B X hX U Q (φ i) (φ j) (hd hij)))
    ((abelianRestrictionUnit B X hX U G).hom.app (op Q) s)
  set ε := (abelianExtensionByZeroAdjunction B X hX U).counit.app G
  have htr : ∀ y, ((abelianTrace B X hX U).app G).hom.app (op Q) (θ.hom.app (op Q) y) =
      ε.hom.app (op Q) y := fun y => ConcreteCategory.congr_hom (congrArg
        (fun t => t.hom.app (op Q))
        (abelianExtensionByZeroToPushforward_app_comp_abelianTrace_app B X hX U G)) y
  refine (congrArg (((abelianTrace B X hX U).app G).hom.app (op Q)) key.symm).trans ?_
  refine (htr _).trans ?_
  refine (map_sum (ε.hom.app (op Q)).hom _ _).trans ?_
  refine (Finset.sum_congr rfl fun i _ =>
    abelianExtensionByZeroAdjunction_counit_app_liftPostIso_inv B X hX U G Q (φ i) s).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- `AlgebraicGeometry.exists_smallEtaleArrows_cover`, with the number of sheets equal to the
degree. -/
theorem exists_smallEtaleArrows_cover_natCard_eq_rank {d : ℕ}
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map U.obj.hom) d]
    [IsFinite (B.inclusion.map U.obj.hom)]
    (V : SmallEtale B X hX) (x : V.obj.left.1) :
    ∃ (Q : SmallEtale B X hX) (q : Q ⟶ V),
      x ∈ Set.range (B.inclusion.map q.hom.left) ∧
      ∃ (ι : Type u) (_ : Finite ι) (φ : ι → (Q ⟶ U)),
        (∀ z : ((smallEtaleBaseChange B U.obj.hom).obj Q).obj.left.1,
            ∃ i, z ∈ Set.range (B.inclusion.map
              (smallEtaleLiftGraph B X hX U Q (φ i)).hom.left)) ∧
        Pairwise (fun i j => smallEtaleArrowsDisjoint B X hX U Q (φ i) (φ j)) ∧
        Nat.card ι = d := by
  classical
  have hVU := (IsPullback.of_hasPullback V.obj.hom U.obj.hom).map B.inclusion
  obtain ⟨hfin, hEt, hrk⟩ := Stacks.Etale.isFinite_etale_rank_of_isPullback hVU.flip d
  obtain ⟨N, g, hg, hcN, n, hn, ⟨hsp⟩⟩ :=
    Stacks.Etale.exists_compactSpace_etale_isSplitOver
      (B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)) x
  have hN : B.Contains N :=
    (Scheme.size_le_of_locallyOfFiniteType g).trans_lt V.obj.left.property
  let q₀ : B.obj N hN ⟶ V.obj.left := ObjectProperty.homMk g
  let Q : SmallEtale B X hX :=
    ⟨Over.mk (q₀ ≫ V.obj.hom), by
      show Etale (g ≫ B.inclusion.map V.obj.hom)
      infer_instance⟩
  let q : Q ⟶ V := ObjectProperty.homMk (Over.homMk q₀ rfl)
  have hsq := (IsPullback.pullback_lift_fst_comp Q.obj.hom q₀ V.obj.hom U.obj.hom
    rfl).map B.inclusion
  let σ (i : hsp.I) := hsp.sectionOfIsPullback hsq i
  have hσfst (i : hsp.I) : σ i ≫ B.inclusion.map (pullback.fst Q.obj.hom U.obj.hom) = 𝟙 _ :=
    hsp.sectionOfIsPullback_comp_snd hsq i
  let σ' (i : hsp.I) : Q.obj.left ⟶ pullback Q.obj.hom U.obj.hom :=
    ObjectProperty.homMk (σ i)
  have hfst (i : hsp.I) : σ' i ≫ pullback.fst Q.obj.hom U.obj.hom = 𝟙 Q.obj.left := by
    apply B.inclusion.map_injective
    simp only [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact hσfst i
  let φ (i : hsp.I) : Q ⟶ U := ObjectProperty.homMk (Over.homMk
    (σ' i ≫ pullback.snd Q.obj.hom U.obj.hom) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hfst i, Category.id_comp]))
  have hσsnd (i : hsp.I) : σ i ≫ B.inclusion.map (pullback.snd Q.obj.hom U.obj.hom) =
      B.inclusion.map (φ i).hom.left :=
    (Functor.map_comp B.inclusion (σ' i) (pullback.snd Q.obj.hom U.obj.hom)).symm
  have hsheet (i : hsp.I) :
      hsp.sheet i ≫ B.inclusion.map (pullback.snd V.obj.hom U.obj.hom) =
        σ i ≫ B.inclusion.map (pullback.snd Q.obj.hom U.obj.hom) := by
    rw [← hsp.sectionOfIsPullback_comp_fst hsq i, Category.assoc, ← Functor.map_comp,
      pullback.lift_snd]
  have : Nonempty N := ⟨n⟩
  refine ⟨Q, q, ⟨n, hn⟩, hsp.I, hsp.finite_I, φ, ?_, ?_, hsp.natCard_I⟩
  · intro z
    obtain ⟨i, hi⟩ := hsp.exists_mem_range_sectionOfIsPullback hsq z
    exact ⟨i, by rwa [map_smallEtaleLiftGraph_eq B X hX U Q (φ i) (σ i) (hσfst i) (hσsnd i)]⟩
  · intro i j hij
    refine smallEtaleArrowsDisjoint_of_isEmpty B X hX U Q (φ i) (φ j) fun c hcc => ?_
    refine isEmpty_of_sheet_comp_snd_eq B X hX U V hsp hij c ?_
    rwa [hsheet i, hsheet j, hσsnd i, hσsnd j]

/-- **Restriction followed by the trace is multiplication by the degree** (Étale Cohomology,
Section 03SH): for `U ⟶ X` finite étale of rank `d`, the composite `ℱ ⟶ j_* j⁻¹ ℱ ⟶ ℱ` of the
restriction map and the trace of Tag 03SE is `d`. -/
theorem abelianRestrictionUnit_comp_abelianTrace [IsFinite (B.inclusion.map U.obj.hom)] (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map U.obj.hom) d]
    (G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :
    abelianRestrictionUnit B X hX U G ≫ (abelianTrace B X hX U).app G = d • 𝟙 G := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro t
  set c := abelianRestrictionUnit B X hX U G ≫ (abelianTrace B X hX U).app G
  let P : Presieve V.unop := fun Q q => ∃ (ι : Type u) (_ : Finite ι) (φ : ι → (Q ⟶ U)),
      (∀ z : ((smallEtaleBaseChange B U.obj.hom).obj Q).obj.left.1, ∃ i,
        z ∈ Set.range (B.inclusion.map (smallEtaleLiftGraph B X hX U Q (φ i)).hom.left)) ∧
      Pairwise (fun i j => smallEtaleArrowsDisjoint B X hX U Q (φ i) (φ j)) ∧ Nat.card ι = d
  have hP : Sieve.generate P ∈ SmallEtale.topology B X hX V.unop := by
    apply SmallEtale.mem_topology_of_jointlySurjective
    intro x
    obtain ⟨Q, q, hx, ι, hι, φ, hcov, hd, hcard⟩ :=
      exists_smallEtaleArrows_cover_natCard_eq_rank B X hX U (d := d) V.unop x
    exact ⟨Q, q, Sieve.le_generate P Q q ⟨ι, hι, φ, hcov, hd, hcard⟩, hx⟩
  apply G.isSeparated V.unop _ hP
  intro Q f hf
  obtain ⟨Q', a, q, ⟨ι, hι, φ, hcov, hd, hcard⟩, rfl⟩ := hf
  have hnat := ConcreteCategory.congr_hom (c.hom.naturality q.op) t
  show G.obj.map (a ≫ q).op (c.hom.app V t) = G.obj.map (a ≫ q).op ((d • 𝟙 G).hom.app V t)
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  congr 1
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  refine hnat.symm.trans ((abelianTrace_app_restrictionUnit_of_split B X hX U G Q' φ hcov hd
    (G.obj.map q.op t)).trans ?_)
  rw [hcard, ← map_nsmul]
  congr 1

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry

/-- **The méthode de la trace on Mathlib's small étale site** (Étale Cohomology, Section 03SH).
For a finite étale `g : V ⟶ U` of rank `d` and an abelian sheaf `G` on `U`, the unit
`G ⟶ g_* g⁻¹ G` followed by a suitable map back to `G` (the trace of Tag 03SE) is multiplication
by `d`. -/
theorem exists_unit_comp_eq_nsmul {U V : Scheme.{u}} (g : V ⟶ U) [IsFinite g] [Etale g] (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d]
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ p : (etaleAbelianDirectImage.{u, u + 1} g).obj
        ((etaleAbelianInverseImage.{u, u + 1} g).obj G) ⟶ G,
      (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} g).unit.app G ≫ p = d • 𝟙 G := by
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({U, V} : Set Scheme.{u})
  have hU := hB U (by simp)
  have hV := hB V (by simp)
  let fB : B.obj V hV ⟶ B.obj U hU := ObjectProperty.homMk g
  let Ũ : SmallEtale B U hU := ⟨Over.mk fB, ‹Etale g›⟩
  have : IsFinite (B.inclusion.map Ũ.obj.hom) := ‹IsFinite g›
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map Ũ.obj.hom) d :=
    ‹Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d›
  let ES := SmallEtale.sheafEquiv B U hU AddCommGrpCat.{u + 1}
  let ET := SmallEtale.sheafEquiv B V hV AddCommGrpCat.{u + 1}
  have : ES.functor.Additive := Functor.additive_of_preserves_binary_products _
  let Y := ES.inverse.obj G
  let W := (abelianRestriction B U hU Ũ).obj Y
  let M := ET.functor.obj W
  let α := (SmallEtale.toEtaleSitePushforwardBaseChangeIso B fB AddCommGrpCat.{u + 1}).app M
  let := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B Ũ.obj.hom
  let γ : ES.inverse.obj ((etaleAbelianDirectImage.{u, u + 1} g).obj M) ≅
      ((AlgebraicGeometry.smallEtaleBaseChange B Ũ.obj.hom).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (SmallEtale.topology B U hU)
        (SmallEtale.topology B Ũ.obj.left.1 Ũ.obj.left.property)).obj W :=
    α ≪≫ ((AlgebraicGeometry.smallEtaleBaseChange B Ũ.obj.hom).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B U hU)
      (SmallEtale.topology B Ũ.obj.left.1 Ũ.obj.left.property)).mapIso (ET.unitIso.app W).symm
  let a' : G ⟶ (etaleAbelianDirectImage.{u, u + 1} g).obj M :=
    (ES.counitIso.app G).inv ≫ ES.functor.map (abelianRestrictionUnit B U hU Ũ Y ≫ γ.inv) ≫
      (ES.counitIso.app _).hom
  let b' : (etaleAbelianDirectImage.{u, u + 1} g).obj M ⟶ G :=
    (ES.counitIso.app _).inv ≫ ES.functor.map (γ.hom ≫ (abelianTrace B U hU Ũ).app Y) ≫
      (ES.counitIso.app G).hom
  have hab : a' ≫ b' = d • 𝟙 G :=
    ES.counitIso_conj_comp_eq_nsmul (abelianRestrictionUnit B U hU Ũ Y ≫ γ.inv)
      (γ.hom ≫ (abelianTrace B U hU Ũ).app Y) d
      (by rw [Category.assoc, Iso.inv_hom_id_assoc,
        abelianRestrictionUnit_comp_abelianTrace B U hU Ũ d Y])
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, u + 1} g
  have h2 : adj.unit.app G ≫ (etaleAbelianDirectImage.{u, u + 1} g).map
      ((adj.homEquiv G M).symm a') = a' :=
    (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply (adj.homEquiv G M) a')
  exact ⟨(etaleAbelianDirectImage.{u, u + 1} g).map ((adj.homEquiv G M).symm a') ≫ b',
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ b') h2).trans hab)⟩

end Stacks.EtaleCohomology

end
