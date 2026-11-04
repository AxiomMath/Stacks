module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.FinitePushforwardSheetCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Trace
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of a finite étale morphism of constant degree

Let `f : T' ⟶ T` be a finite étale morphism of a big étale site which is finite locally free of
rank `d`. The composite

`ℱ ⟶ f_* f^{-1} ℱ ⟶ ℱ`

of the unit of the adjunction `f^{-1} ⊣ f_*` with the trace of Proposition 03SE is
multiplication by `d`. This is what Section 03SH extracts from the trace: for `d` invertible on
the coefficients, `ℱ` is a direct summand of `f_* f^{-1} ℱ`.

## Main results

* `AlgebraicGeometry.unit_comp_abelianTrace_eq_nsmul`: the composite is `d • 𝟙`.

## Implementation notes

Étale-locally on `T` the morphism `f` is `d` disjoint copies of the base
(`AlgebraicGeometry.exists_smallEtaleArrows_cover_natCard`, which counts the copies by the
degree). Over such a neighbourhood `Q` the inverse of the comparison `f_! ⟶ f_*` is explicit
(`CategoryTheory.Presheaf.app_sum_eq_of_graphCover`): a section of `f_* f^{-1} ℱ` over `Q` is the
image of the sum over the `d` copies of its restrictions to them, and the counit of
`f_! ⊣ f^{-1}` sends each summand coming from the unit back to the restriction itself. For the
pullback of a section `s` of `ℱ` each restriction is `s`, so the trace returns `d • s`.

## References

* [Stacks Project, Tag 03SE](https://stacks.math.columbia.edu/tag/03SE)
* [Stacks Project, Tag 03SH](https://stacks.math.columbia.edu/tag/03SH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {T' T : B.Scheme} (f : T' ⟶ T) [Etale (B.inclusion.map f)]
  [IsFinite (B.inclusion.map f)]

/-- The finiteness of `f`, read on the étale object of `T` it defines. -/
instance isFinite_ofEtaleHom :
    IsFinite (B.inclusion.map (SmallEtale.ofEtaleHom B f).obj.hom) :=
  inferInstanceAs (IsFinite (B.inclusion.map f))

/-- The graph of an étale object over `T'` is the unit of the adjunction between composition
with `f` and base change along `f`. -/
theorem smallEtaleGraph_ofEtaleHom_eq_unit (W : SmallEtale B T'.1 T'.property) :
    smallEtaleGraph B T.1 T.property (SmallEtale.ofEtaleHom B f) W =
      (smallEtalePostcomposeBaseChangeAdjunction B f).unit.app W := by
  rw [smallEtalePostcomposeBaseChangeAdjunction_unit_app]
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;>
    simp [smallEtaleGraph, smallEtaleBaseChangeLift, smallEtalePostcompose, smallEtaleBaseChange,
      Over.mapPullbackAdj, Over.pullback]

/-- Composition with `f` carries the graph of `W` to a section of the counit at the composite:
the triangle identity of the adjunction between composition with `f` and base change. -/
theorem map_smallEtaleGraph_comp_counit (W : SmallEtale B T'.1 T'.property) :
    (smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B f)).map
        (smallEtaleGraph B T.1 T.property (SmallEtale.ofEtaleHom B f) W) ≫
      (smallEtalePostcomposeBaseChangeAdjunction B f).counit.app
        ((smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B f)).obj W) = 𝟙 _ := by
  rw [smallEtaleGraph_ofEtaleHom_eq_unit]
  exact (smallEtalePostcomposeBaseChangeAdjunction B f).left_triangle_components W

/-- **The trace identity over a neighbourhood splitting `f`.** If over the étale object `Q` of
`T` the morphism `f` is described by the pairwise disjoint morphisms `φ i : Q ⟶ T'` whose graphs
cover `Q ×_T T'`, the unit of `f^{-1} ⊣ f_*` followed by the trace multiplies the sections of `ℱ`
over `Q` by the number of the `φ i`. -/
theorem unit_comp_abelianTrace_app_of_cover
    (F : Sheaf (SmallEtale.topology B T.1 T.property) AddCommGrpCat.{u + 1})
    (Q : SmallEtale B T.1 T.property) {ι : Type u} [Fintype ι]
    (φ : ι → (Q ⟶ SmallEtale.ofEtaleHom B f))
    (hcov : ∀ z : ((smallEtaleBaseChange B (SmallEtale.ofEtaleHom B f).obj.hom).obj Q).obj.left.1,
      ∃ i, z ∈ Set.range (B.inclusion.map
        (smallEtaleLiftGraph B T.1 T.property (SmallEtale.ofEtaleHom B f) Q (φ i)).hom.left))
    (hd : Pairwise (fun i j => smallEtaleArrowsDisjoint B T.1 T.property
      (SmallEtale.ofEtaleHom B f) Q (φ i) (φ j)))
    (t : F.obj.obj (op Q)) :
    ((smallEtalePostcomposePushforwardAdjunction B f AddCommGrpCat.{u + 1}).unit.app F ≫
        (abelianTrace B T.1 T.property (SmallEtale.ofEtaleHom B f)).app F).hom.app (op Q) t =
      Fintype.card ι • t := by
  have : IsSeparated (B.inclusion.map (SmallEtale.ofEtaleHom B f).obj.hom) :=
    IsSeparated.of_isAffineHom _
  let U := SmallEtale.ofEtaleHom B f
  let F' := (abelianRestriction B T.1 T.property U).obj F
  let adjE := abelianExtensionByZeroAdjunction B T.1 T.property U
  let adjS := smallEtalePostcomposeBaseChangeAdjunction B f
  let H := ((abelianExtensionByZero B T.1 T.property U).obj F').obj
  let u := ((smallEtalePostcomposePushforwardAdjunction B f AddCommGrpCat.{u + 1}).unit.app
    F).hom.app (op Q) t
  have hsum := Presheaf.app_sum_eq_of_graphCover (smallEtalePostcompose B T.1 T.property U)
    (smallEtaleBaseChange B U.obj.hom) (SmallEtale.topology B T'.1 T'.property) F'.obj
    F'.isSeparated H ((abelianExtensionByZeroToPushforward B T.1 T.property U).app F').hom
    (fun W => (adjE.unit.app F').hom.app (op W)) (smallEtaleGraph B T.1 T.property U)
    (abelianExtensionByZeroToPushforward_graph B T.1 T.property U F')
    (fun i => smallEtaleLift B T.1 T.property U Q (φ i))
    (fun i => smallEtaleLiftPostIso B T.1 T.property U Q (φ i))
    (SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B T'.1 T'.property _ _ hcov)
    (fun i j hij => abelianExtensionByZeroToPushforward_graph_compl B T.1 T.property U F' _ _ _
      (disjointFromSmallEtaleGraph_smallEtaleLiftGraph B T.1 T.property U Q (φ i) (φ j)
        (hd hij))) u
  let L := smallEtalePostcompose B T.1 T.property U
  let e := fun i => smallEtaleLiftPostIso B T.1 T.property U Q (φ i)
  let g := fun i => smallEtaleLiftGraph B T.1 T.property U Q (φ i)
  have hsite (i : ι) : (e i).inv ≫ L.map (g i) ≫ adjS.counit.app Q = 𝟙 Q := by
    rw [show L.map (g i) = L.map (smallEtaleGraph B T.1 T.property U
        (smallEtaleLift B T.1 T.property U Q (φ i))) ≫
        L.map ((smallEtaleBaseChange B f).map (e i).hom) from L.map_comp _ _, Category.assoc,
      show L.map ((smallEtaleBaseChange B f).map (e i).hom) ≫ adjS.counit.app Q =
        adjS.counit.app (L.obj (smallEtaleLift B T.1 T.property U Q (φ i))) ≫ (e i).hom from
        adjS.counit_naturality (e i).hom,
      ← Category.assoc (L.map (smallEtaleGraph _ _ _ _ _)), map_smallEtaleGraph_comp_counit,
      Category.id_comp]
    exact (e i).inv_hom_id
  have hterm (i : ι) : (adjE.counit.app F).hom.app (op Q)
      (H.map (e i).inv.op ((adjE.unit.app F').hom.app (op (smallEtaleLift B T.1 T.property U Q
        (φ i))) (F'.obj.map (g i).op u))) = t := by
    have e1 := ConcreteCategory.congr_hom ((adjE.counit.app F).hom.naturality (e i).inv.op)
      ((adjE.unit.app F').hom.app (op (smallEtaleLift B T.1 T.property U Q (φ i)))
        (F'.obj.map (g i).op u))
    have e2 := ConcreteCategory.congr_hom (congrArg
      (fun k => k.hom.app (op (smallEtaleLift B T.1 T.property U Q (φ i))))
      (adjE.right_triangle_components F)) (F'.obj.map (g i).op u)
    have e3 : F.obj.map (e i).inv.op (F'.obj.map (g i).op u) = t := by
      show (F.obj.map (adjS.counit.app Q).op ≫ F.obj.map (L.map (g i)).op ≫
        F.obj.map (e i).inv.op) t = t
      rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp, Category.assoc, hsite i]
      simp
    exact (e1.trans (congrArg (F.obj.map (e i).inv.op) e2)).trans e3
  have hinv : ((abelianExtensionByZeroIsoPushforward B T.1 T.property U).inv.app F').hom.app
      (op Q) u = ∑ i, H.map (e i).inv.op ((adjE.unit.app F').hom.app
        (op (smallEtaleLift B T.1 T.property U Q (φ i))) (F'.obj.map (g i).op u)) := by
    conv_lhs => rw [← hsum]
    exact ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app (op Q))
      ((abelianExtensionByZeroIsoPushforward B T.1 T.property U).hom_inv_id_app F')) _
  show (adjE.counit.app F).hom.app (op Q)
    (((abelianExtensionByZeroIsoPushforward B T.1 T.property U).inv.app F').hom.app (op Q) u) = _
  rw [hinv, map_sum, Finset.sum_congr rfl (fun i _ ↦ hterm i), Finset.sum_const, Finset.card_univ]

/-- **The unit of `f^{-1} ⊣ f_*` followed by the trace of a finite étale `f` of degree `d` is
multiplication by `d`.** -/
@[sga "4 XVII 6.2.3" "Var 4 (normalization)", sga "4 XVIII 2.9" "Var 4 (I)"]
theorem unit_comp_abelianTrace_eq_nsmul (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map f) d]
    (F : Sheaf (SmallEtale.topology B T.1 T.property) AddCommGrpCat.{u + 1}) :
    (smallEtalePostcomposePushforwardAdjunction B f AddCommGrpCat.{u + 1}).unit.app F ≫
        (abelianTrace B T.1 T.property (SmallEtale.ofEtaleHom B f)).app F = d • 𝟙 F := by
  set φ := (smallEtalePostcomposePushforwardAdjunction B f AddCommGrpCat.{u + 1}).unit.app F ≫
    (abelianTrace B T.1 T.property (SmallEtale.ofEtaleHom B f)).app F
  have hd : ∀ (V : (SmallEtale B T.1 T.property)ᵒᵖ) (y : F.obj.obj V),
      (d • 𝟙 F).hom.app V y = d • y := fun V y ↦ by
    have h : ((sheafToPresheaf _ _).map (d • 𝟙 F)).app V = d • 𝟙 _ := by
      simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id, NatTrans.app_nsmul,
        NatTrans.id_app]
    simpa using congrArg (fun ψ ↦ ψ y) h
  apply Sheaf.hom_ext
  ext V t
  refine F.isSeparated V.unop
    ⟨fun Y g ↦ F.obj.map g.op (φ.hom.app V t) = F.obj.map g.op ((d • 𝟙 F).hom.app V t),
      fun {Y Z g} hg k ↦ by
        simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        rw [hg]⟩ ?_ _ _ (fun Y g hg ↦ hg)
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  obtain ⟨Q, q, hx, ι, hι, φs, hcov, hdis, hcard⟩ :=
    exists_smallEtaleArrows_cover_natCard B T.1 T.property (SmallEtale.ofEtaleHom B f) V.unop x
  have := Fintype.ofFinite ι
  refine ⟨Q, q, ?_, hx⟩
  show F.obj.map q.op (φ.hom.app V t) = F.obj.map q.op ((d • 𝟙 F).hom.app V t)
  have n₁ := ConcreteCategory.congr_hom (φ.hom.naturality q.op) t
  have n₂ := ConcreteCategory.congr_hom ((d • 𝟙 F).hom.naturality q.op) t
  simp only [ConcreteCategory.comp_apply] at n₁ n₂
  refine n₁.symm.trans (Eq.trans ?_ n₂)
  rw [hd, unit_comp_abelianTrace_app_of_cover B f F Q φs hcov hdis,
    ← Nat.card_eq_fintype_card,
    hcard d (inferInstanceAs (Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map f) d))]
  rfl

end AlgebraicGeometry

end
