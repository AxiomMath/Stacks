module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.TraceDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of a finite étale morphism of constant degree, for sheaves of modules

Let `f : T' ⟶ T` be a finite étale morphism of a big étale site which is finite locally free of
rank `d`, and let `Λ` be a ring. For a sheaf `ℱ` of `Λ`-modules on the small étale site of `T`,
the composite

`ℱ ⟶ f_* f^{-1} ℱ ⟶ ℱ`

of the unit of the adjunction `f^{-1} ⊣ f_*` with the trace of Proposition 03SE is
multiplication by `d`. This is the module form of
`AlgebraicGeometry.unit_comp_abelianTrace_eq_nsmul`, with the same proof.

## Main results

* `AlgebraicGeometry.moduleTrace_app_eq_sum_of_cover`: over an étale neighbourhood on which `f`
  is a disjoint union of copies of the base, the trace is the sum map.
* `AlgebraicGeometry.eq_moduleTrace_app_of_sum`: the trace is the only morphism
  `f_* f^{-1} ℱ ⟶ ℱ` given by the sum map étale locally on the base.
* `AlgebraicGeometry.unit_comp_moduleTrace_app_of_cover`: the identity over an étale
  neighbourhood splitting `f`.
* `AlgebraicGeometry.unit_comp_moduleTrace_eq_nsmul`: the composite is `d • 𝟙`.

## References

* [Stacks Project, Tag 03SE](https://stacks.math.columbia.edu/tag/03SE)
* [Stacks Project, Tag 03SH](https://stacks.math.columbia.edu/tag/03SH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {T' T : B.Scheme} (f : T' ⟶ T) [Etale (B.inclusion.map f)]
  [IsFinite (B.inclusion.map f)] (Λ : Type v) [Ring Λ]

/-- **The trace identity over a neighbourhood splitting `f`, for sheaves of modules.** If over
the étale object `Q` of `T` the morphism `f` is described by the pairwise disjoint morphisms
`φ i : Q ⟶ T'` whose graphs cover `Q ×_T T'`, the unit of `f^{-1} ⊣ f_*` followed by the trace
multiplies the sections of `ℱ` over `Q` by the number of the `φ i`. -/
theorem unit_comp_moduleTrace_app_of_cover
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{max (u + 1) v} Λ))
    (Q : SmallEtale B T.1 T.property) {ι : Type u} [Fintype ι]
    (φ : ι → (Q ⟶ SmallEtale.ofEtaleHom B f))
    (hcov : ∀ z : ((smallEtaleBaseChange B (SmallEtale.ofEtaleHom B f).obj.hom).obj Q).obj.left.1,
      ∃ i, z ∈ Set.range (B.inclusion.map
        (smallEtaleLiftGraph B T.1 T.property (SmallEtale.ofEtaleHom B f) Q (φ i)).hom.left))
    (hd : Pairwise (fun i j => smallEtaleArrowsDisjoint B T.1 T.property
      (SmallEtale.ofEtaleHom B f) Q (φ i) (φ j)))
    (t : F.obj.obj (op Q)) :
    ((smallEtalePostcomposePushforwardAdjunction B f
        (ModuleCat.{max (u + 1) v} Λ)).unit.app F ≫
        (moduleTrace B T.1 T.property (SmallEtale.ofEtaleHom B f) Λ).app F).hom.app (op Q) t =
      Fintype.card ι • t := by
  have : IsSeparated (B.inclusion.map (SmallEtale.ofEtaleHom B f).obj.hom) :=
    IsSeparated.of_isAffineHom _
  let U := SmallEtale.ofEtaleHom B f
  let Fg := forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}
  let F' := (moduleRestriction B T.1 T.property U Λ).obj F
  let θ := (moduleExtensionByZeroToPushforward B T.1 T.property U Λ).app F'
  let adjE := moduleExtensionByZeroAdjunction B T.1 T.property U Λ
  let adjS := smallEtalePostcomposeBaseChangeAdjunction B f
  let u := ((smallEtalePostcomposePushforwardAdjunction B f
    (ModuleCat.{max (u + 1) v} Λ)).unit.app F).hom.app (op Q) t
  have hu : u = F.obj.map (adjS.counit.app Q).op t := rfl
  have hsep : Presheaf.IsSeparated (SmallEtale.topology B T'.1 T'.property) (F'.obj ⋙ Fg) :=
    fun X S hS x y hxy => F'.isSeparated X S hS (x : F'.obj.obj (op X)) y fun Y g hg => hxy Y g hg
  have hsum := Presheaf.app_sum_eq_of_graphCover (smallEtalePostcompose B T.1 T.property U)
    (smallEtaleBaseChange B U.obj.hom) (SmallEtale.topology B T'.1 T'.property) (F'.obj ⋙ Fg)
    hsep (((moduleExtensionByZero B T.1 T.property U Λ).obj F').obj ⋙ Fg)
    (Functor.whiskerRight θ.hom Fg)
    (fun W => Fg.map ((adjE.unit.app F').hom.app (op W))) (smallEtaleGraph B T.1 T.property U)
    (moduleExtensionByZeroToPushforward_graph B T.1 T.property U Λ F')
    (fun i => smallEtaleLift B T.1 T.property U Q (φ i))
    (fun i => smallEtaleLiftPostIso B T.1 T.property U Q (φ i))
    (SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B T'.1 T'.property _ _ hcov)
    (fun i j hij => moduleExtensionByZeroToPushforward_graph_compl B T.1 T.property U Λ F' _ _ _
      (disjointFromSmallEtaleGraph_smallEtaleLiftGraph B T.1 T.property U Q (φ i) (φ j)
        (hd hij))) u
  let L := smallEtalePostcompose B T.1 T.property U
  let H := ((moduleExtensionByZero B T.1 T.property U Λ).obj F').obj
  let e := fun i => smallEtaleLiftPostIso B T.1 T.property U Q (φ i)
  let g := fun i => smallEtaleLiftGraph B T.1 T.property U Q (φ i)
  -- the site-level identity behind each summand
  have hsite (i : ι) : (e i).inv ≫ L.map (g i) ≫ adjS.counit.app Q = 𝟙 Q := by
    have h1 : L.map (g i) = L.map (smallEtaleGraph B T.1 T.property U
        (smallEtaleLift B T.1 T.property U Q (φ i))) ≫
        L.map ((smallEtaleBaseChange B f).map (e i).hom) := L.map_comp _ _
    rw [h1, Category.assoc]
    rw [show L.map ((smallEtaleBaseChange B f).map (e i).hom) ≫ adjS.counit.app Q =
        adjS.counit.app (L.obj (smallEtaleLift B T.1 T.property U Q (φ i))) ≫ (e i).hom from
        adjS.counit_naturality (e i).hom]
    rw [← Category.assoc (L.map (smallEtaleGraph _ _ _ _ _)),
      map_smallEtaleGraph_comp_counit, Category.id_comp]
    exact (e i).inv_hom_id
  -- each summand is sent by the counit to the section itself
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
      rw [hu]
      show (F.obj.map (adjS.counit.app Q).op ≫ F.obj.map (L.map (g i)).op ≫
        F.obj.map (e i).inv.op) t = t
      rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp, Category.assoc,
        hsite i]
      simp
    refine (e1.trans ?_).trans e3
    exact congrArg (F.obj.map (e i).inv.op) e2
  have hinv : ((moduleExtensionByZeroIsoPushforward B T.1 T.property U Λ).inv.app F').hom.app
      (op Q) u = ∑ i, H.map (e i).inv.op ((adjE.unit.app F').hom.app
        (op (smallEtaleLift B T.1 T.property U Q (φ i))) (F'.obj.map (g i).op u)) := by
    conv_lhs => rw [← hsum]
    exact ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app (op Q))
      ((moduleExtensionByZeroIsoPushforward B T.1 T.property U Λ).hom_inv_id_app F')) _
  show (adjE.counit.app F).hom.app (op Q)
    (((moduleExtensionByZeroIsoPushforward B T.1 T.property U Λ).inv.app F').hom.app
      (op Q) u) = _
  rw [hinv, map_sum, Finset.sum_congr rfl (fun i _ ↦ hterm i), Finset.sum_const,
    Finset.card_univ]

/-- **Stacks 03SH, the trace on a split cover is the sum map.** If over the étale object `Q` of
`T` the morphism `f` is described by the pairwise disjoint morphisms `φ i : Q ⟶ T'` whose graphs
cover `Q ×_T T'`, so that `(f_* f^{-1} ℱ)(Q) = ℱ(Q ×_T T') = ⨁ᵢ ℱ(Q)`, then the trace sends a
section to the sum of its restrictions to the sheets `φ i`, each read on `Q`. -/
@[stacks 03SH "if Y is a disjoint union of copies of the base, the trace is the sum map, for \
sheaves of Λ-modules"]
theorem moduleTrace_app_eq_sum_of_cover
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{max (u + 1) v} Λ))
    (Q : SmallEtale B T.1 T.property) {ι : Type u} [Fintype ι]
    (φ : ι → (Q ⟶ SmallEtale.ofEtaleHom B f))
    (hcov : ∀ z : ((smallEtaleBaseChange B (SmallEtale.ofEtaleHom B f).obj.hom).obj Q).obj.left.1,
      ∃ i, z ∈ Set.range (B.inclusion.map
        (smallEtaleLiftGraph B T.1 T.property (SmallEtale.ofEtaleHom B f) Q (φ i)).hom.left))
    (hd : Pairwise (fun i j => smallEtaleArrowsDisjoint B T.1 T.property
      (SmallEtale.ofEtaleHom B f) Q (φ i) (φ j)))
    (s : F.obj.obj (op ((smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B f)).obj
      ((smallEtaleBaseChange B (SmallEtale.ofEtaleHom B f).obj.hom).obj Q)))) :
    ((moduleTrace B T.1 T.property (SmallEtale.ofEtaleHom B f) Λ).app F).hom.app (op Q) s =
      ∑ i, F.obj.map (smallEtaleLiftPostIso B T.1 T.property (SmallEtale.ofEtaleHom B f) Q
        (φ i)).inv.op
        (((moduleRestriction B T.1 T.property (SmallEtale.ofEtaleHom B f) Λ).obj F).obj.map
          (smallEtaleLiftGraph B T.1 T.property (SmallEtale.ofEtaleHom B f) Q (φ i)).op s) := by
  have : IsSeparated (B.inclusion.map (SmallEtale.ofEtaleHom B f).obj.hom) :=
    IsSeparated.of_isAffineHom _
  let U := SmallEtale.ofEtaleHom B f
  let Fg := forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}
  let F' := (moduleRestriction B T.1 T.property U Λ).obj F
  let θ := (moduleExtensionByZeroToPushforward B T.1 T.property U Λ).app F'
  let adjE := moduleExtensionByZeroAdjunction B T.1 T.property U Λ
  have hsep : Presheaf.IsSeparated (SmallEtale.topology B T'.1 T'.property) (F'.obj ⋙ Fg) :=
    fun X S hS x y hxy => F'.isSeparated X S hS (x : F'.obj.obj (op X)) y fun Y g hg => hxy Y g hg
  have hsum := Presheaf.app_sum_eq_of_graphCover (smallEtalePostcompose B T.1 T.property U)
    (smallEtaleBaseChange B U.obj.hom) (SmallEtale.topology B T'.1 T'.property) (F'.obj ⋙ Fg)
    hsep (((moduleExtensionByZero B T.1 T.property U Λ).obj F').obj ⋙ Fg)
    (Functor.whiskerRight θ.hom Fg)
    (fun W => Fg.map ((adjE.unit.app F').hom.app (op W))) (smallEtaleGraph B T.1 T.property U)
    (moduleExtensionByZeroToPushforward_graph B T.1 T.property U Λ F')
    (fun i => smallEtaleLift B T.1 T.property U Q (φ i))
    (fun i => smallEtaleLiftPostIso B T.1 T.property U Q (φ i))
    (SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B T'.1 T'.property _ _ hcov)
    (fun i j hij => moduleExtensionByZeroToPushforward_graph_compl B T.1 T.property U Λ F' _ _ _
      (disjointFromSmallEtaleGraph_smallEtaleLiftGraph B T.1 T.property U Q (φ i) (φ j)
        (hd hij))) s
  let H := ((moduleExtensionByZero B T.1 T.property U Λ).obj F').obj
  let e := fun i => smallEtaleLiftPostIso B T.1 T.property U Q (φ i)
  let g := fun i => smallEtaleLiftGraph B T.1 T.property U Q (φ i)
  have hterm (i : ι) : (adjE.counit.app F).hom.app (op Q)
      (H.map (e i).inv.op ((adjE.unit.app F').hom.app (op (smallEtaleLift B T.1 T.property U Q
        (φ i))) (F'.obj.map (g i).op s))) = F.obj.map (e i).inv.op (F'.obj.map (g i).op s) := by
    have e1 := ConcreteCategory.congr_hom ((adjE.counit.app F).hom.naturality (e i).inv.op)
      ((adjE.unit.app F').hom.app (op (smallEtaleLift B T.1 T.property U Q (φ i)))
        (F'.obj.map (g i).op s))
    have e2 := ConcreteCategory.congr_hom (congrArg
      (fun k => k.hom.app (op (smallEtaleLift B T.1 T.property U Q (φ i))))
      (adjE.right_triangle_components F)) (F'.obj.map (g i).op s)
    exact e1.trans (congrArg (F.obj.map (e i).inv.op) e2)
  have hinv : ((moduleExtensionByZeroIsoPushforward B T.1 T.property U Λ).inv.app F').hom.app
      (op Q) s = ∑ i, H.map (e i).inv.op ((adjE.unit.app F').hom.app
        (op (smallEtaleLift B T.1 T.property U Q (φ i))) (F'.obj.map (g i).op s)) := by
    conv_lhs => rw [← hsum]
    exact ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app (op Q))
      ((moduleExtensionByZeroIsoPushforward B T.1 T.property U Λ).hom_inv_id_app F')) _
  show (adjE.counit.app F).hom.app (op Q)
    (((moduleExtensionByZeroIsoPushforward B T.1 T.property U Λ).inv.app F').hom.app
      (op Q) s) = _
  rw [hinv, map_sum, Finset.sum_congr rfl fun i _ ↦ hterm i]

/-- **Stacks 03SH, the trace is characterized by the sum formula.** A morphism
`τ : f_* f^{-1} ℱ ⟶ ℱ` which, over every étale neighbourhood `Q` on which `f` is a disjoint union
of copies of `Q` (pairwise disjoint sheets `φ i : Q ⟶ T'` whose graphs cover `Q ×_T T'`), sends a
section to the sum of its restrictions to the sheets is the trace: such neighbourhoods cover `T`
(Stacks 04HN), and two morphisms of sheaves agreeing on a covering agree. -/
@[stacks 03SH "the trace is characterized by being the sum map étale locally on the base, for \
sheaves of Λ-modules"]
theorem eq_moduleTrace_app_of_sum
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{max (u + 1) v} Λ))
    (τ : (B.smallPushforward f (ModuleCat.{max (u + 1) v} Λ)).obj
      ((moduleRestriction B T.1 T.property (SmallEtale.ofEtaleHom B f) Λ).obj F) ⟶ F)
    (hτ : ∀ (Q : SmallEtale B T.1 T.property) {ι : Type u} [Fintype ι]
      (φ : ι → (Q ⟶ SmallEtale.ofEtaleHom B f)),
      (∀ z : ((smallEtaleBaseChange B (SmallEtale.ofEtaleHom B f).obj.hom).obj Q).obj.left.1,
        ∃ i, z ∈ Set.range (B.inclusion.map
          (smallEtaleLiftGraph B T.1 T.property (SmallEtale.ofEtaleHom B f) Q (φ i)).hom.left)) →
      Pairwise (fun i j => smallEtaleArrowsDisjoint B T.1 T.property
        (SmallEtale.ofEtaleHom B f) Q (φ i) (φ j)) →
      ∀ s : F.obj.obj (op ((smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B f)).obj
        ((smallEtaleBaseChange B (SmallEtale.ofEtaleHom B f).obj.hom).obj Q))),
      τ.hom.app (op Q) s =
        ∑ i, F.obj.map (smallEtaleLiftPostIso B T.1 T.property (SmallEtale.ofEtaleHom B f) Q
          (φ i)).inv.op
          (((moduleRestriction B T.1 T.property (SmallEtale.ofEtaleHom B f) Λ).obj F).obj.map
            (smallEtaleLiftGraph B T.1 T.property (SmallEtale.ofEtaleHom B f) Q (φ i)).op s)) :
    τ = (moduleTrace B T.1 T.property (SmallEtale.ofEtaleHom B f) Λ).app F := by
  set τ' := (moduleTrace B T.1 T.property (SmallEtale.ofEtaleHom B f) Λ).app F
  apply Sheaf.hom_ext
  ext V t
  refine F.isSeparated V.unop
    ⟨fun Y g ↦ F.obj.map g.op (τ.hom.app V t) = F.obj.map g.op (τ'.hom.app V t),
      fun {Y Z g} hg k ↦ by
        simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        rw [hg]⟩ ?_ _ _ (fun Y g hg ↦ hg)
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  obtain ⟨Q, q, hx, ι, hι, φs, hcov, hdis, -⟩ :=
    exists_smallEtaleArrows_cover_natCard B T.1 T.property (SmallEtale.ofEtaleHom B f) V.unop x
  have := Fintype.ofFinite ι
  refine ⟨Q, q, ?_, hx⟩
  show F.obj.map q.op (τ.hom.app V t) = F.obj.map q.op (τ'.hom.app V t)
  have n₁ := ConcreteCategory.congr_hom (τ.hom.naturality q.op) t
  have n₂ := ConcreteCategory.congr_hom (τ'.hom.naturality q.op) t
  simp only [ConcreteCategory.comp_apply] at n₁ n₂
  refine n₁.symm.trans (Eq.trans ?_ n₂)
  exact (hτ Q φs hcov hdis _).trans
    (moduleTrace_app_eq_sum_of_cover B f Λ F Q φs hcov hdis _).symm

/-- **Stacks 03SH, the trace of a finite étale morphism of degree `d` on sheaves of modules.**
For `f` finite étale and finite locally free of rank `d`, the restriction map `ℱ ⟶ f_* f^{-1} ℱ`
(the unit of `f^{-1} ⊣ f_*`) followed by the trace `f_* f^{-1} ℱ ⟶ ℱ` of Definition 03SE is
multiplication by `d`. -/
@[stacks 03SH "restriction followed by the trace is multiplication by the degree, for \
sheaves of Λ-modules", sga "4 XVII 6.2.3" "Var 4 (normalization)", sga "4 XVIII 2.9" "Var 4 (I)"]
theorem unit_comp_moduleTrace_eq_nsmul (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map f) d]
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{max (u + 1) v} Λ)) :
    (smallEtalePostcomposePushforwardAdjunction B f
        (ModuleCat.{max (u + 1) v} Λ)).unit.app F ≫
        (moduleTrace B T.1 T.property (SmallEtale.ofEtaleHom B f) Λ).app F = d • 𝟙 F := by
  set φ := (smallEtalePostcomposePushforwardAdjunction B f
      (ModuleCat.{max (u + 1) v} Λ)).unit.app F ≫
    (moduleTrace B T.1 T.property (SmallEtale.ofEtaleHom B f) Λ).app F
  have hd : ∀ (V : (SmallEtale B T.1 T.property)ᵒᵖ) (y : F.obj.obj V),
      (d • 𝟙 F).hom.app V y = d • y := fun V y ↦ by
    have h : ((sheafToPresheaf _ _).map (d • 𝟙 F)).app V = d • 𝟙 _ := by
      simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id, NatTrans.app_nsmul,
        NatTrans.id_app]
    simpa using congrArg (fun φ ↦ φ y) h
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
  rw [hd, unit_comp_moduleTrace_app_of_cover B f Λ F Q φs hcov hdis,
    ← Nat.card_eq_fintype_card,
    hcard d (inferInstanceAs (Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map f) d))]
  rfl

end AlgebraicGeometry

end
