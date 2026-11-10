module

public import StacksFrontier.CategoryTheory.Sites.SurjectivityFromGraphCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Trace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.FinitePushforwardSheetCount
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.ModuleExactness

/-!
# Restriction followed by the trace is multiplication by the degree

Let `j : U ⟶ X` be a finite étale morphism, viewed as an object of the small étale site of `X`,
of constant degree `d`. For a sheaf of `Λ`-modules `ℱ` on `X_étale` the composite of restriction
`ℱ ⟶ j_*j^{-1}ℱ` and the trace `j_*j^{-1}ℱ ⟶ ℱ` of Stacks 03SE is multiplication by `d`.

The identity is checked on sections, locally on `X`. Étale-locally (Stacks 04HN) `U` is described
by finitely many pairwise disjoint morphisms `φ_i : Q ⟶ U` whose graphs cover `Q ×_X U`, and
then the comparison `j_! ⟶ j_*` has the explicit inverse of
`CategoryTheory.Presheaf.app_sum_eq_of_graphCover`: the restriction of a section `a` of `ℱ` is the
image of the sum of the summands of `j_!j^{-1}ℱ` indexed by the `φ_i`, each carrying `a`. The
counit of `j_! ⊣ j^{-1}` returns `a` on each summand (a triangle identity), so the trace of the
restriction of `a` is `a` times the number of the `φ_i`; and that number is `d`, by
`AlgebraicGeometry.exists_smallEtaleArrows_cover_natCard`.

## Main definitions

* `AlgebraicGeometry.smallEtaleBaseChangeProj` — the projection `V ×_X U ⟶ V`.
* `AlgebraicGeometry.moduleRestrictionUnit` — the restriction map `ℱ ⟶ j_*j^{-1}ℱ`.

## Main results

* `AlgebraicGeometry.moduleRestrictionUnit_comp_moduleTrace_app_eq_natCard_smul` — over an
  étale neighbourhood `Q` on which `U` is the disjoint union of the graphs of `φ_i : Q ⟶ U`,
  the trace of the restriction of a section is the section multiplied by the number of graphs.

## References

* [Stacks Project, Tag 03SH](https://stacks.math.columbia.edu/tag/03SH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- The projection `V ×_X U ⟶ V` of the base change to `U` of an étale object `V` over `X`,
read back over `X`: the counit of the adjunction between composition with the structure
morphism of `U` and base change along it. -/
public def smallEtaleBaseChangeProj (V : SmallEtale B X hX) :
    (smallEtalePostcompose B X hX U).obj ((smallEtaleBaseChange B U.obj.hom).obj V) ⟶ V := by
  let := hasPullbacks_bigEtaleSite B
  exact ObjectProperty.homMk ((Over.mapPullbackAdj U.obj.hom).counit.app V.obj)

/-- The projection is natural in `V`. -/
public theorem smallEtaleBaseChangeProj_naturality {V V' : SmallEtale B X hX} (g : V ⟶ V') :
    (smallEtalePostcompose B X hX U).map ((smallEtaleBaseChange B U.obj.hom).map g) ≫
        smallEtaleBaseChangeProj B X hX U V' =
      smallEtaleBaseChangeProj B X hX U V ≫ g := by
  let := hasPullbacks_bigEtaleSite B
  exact ObjectProperty.hom_ext _ ((Over.mapPullbackAdj U.obj.hom).counit.naturality g.hom)

/-- The graph of an étale object `W` over `U` is a section of the projection. -/
public theorem map_smallEtaleGraph_comp_smallEtaleBaseChangeProj
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (smallEtalePostcompose B X hX U).map (smallEtaleGraph B X hX U W) ≫
        smallEtaleBaseChangeProj B X hX U ((smallEtalePostcompose B X hX U).obj W) = 𝟙 _ := by
  let := hasPullbacks_bigEtaleSite B
  exact ObjectProperty.hom_ext _ ((Over.mapPullbackAdj U.obj.hom).left_triangle_components W.obj)

/-- The transported graph of `φ : Q ⟶ U` is a section of the projection `Q ×_X U ⟶ Q`. -/
public theorem smallEtaleLiftPostIso_inv_comp_map_smallEtaleLiftGraph_comp_proj
    (Q : SmallEtale B X hX) (φ : Q ⟶ U) :
    (smallEtaleLiftPostIso B X hX U Q φ).inv ≫
        (smallEtalePostcompose B X hX U).map (smallEtaleLiftGraph B X hX U Q φ) ≫
          smallEtaleBaseChangeProj B X hX U Q = 𝟙 Q := by
  rw [smallEtaleLiftGraph, Functor.map_comp, Category.assoc,
    smallEtaleBaseChangeProj_naturality, ← Category.assoc
      ((smallEtalePostcompose B X hX U).map _),
    map_smallEtaleGraph_comp_smallEtaleBaseChangeProj, Category.id_comp, Iso.inv_hom_id]

variable (Λ : Type v) [Ring Λ]

/-- **Restriction** `ℱ ⟶ j_*j^{-1}ℱ` for sheaves of `Λ`-modules: on sections over `V` it is
restriction along the projection `V ×_X U ⟶ V`. -/
public def moduleRestrictionUnit :
    let := smallEtaleBaseChange_isContinuous B U.obj.hom
    𝟭 (Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ)) ⟶
      moduleRestriction B X hX U Λ ⋙
        (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
          (ModuleCat.{max (u + 1) v} Λ)
          (SmallEtale.topology B X hX)
          (SmallEtale.topology B U.obj.left.1 U.obj.left.property) where
  app F := ObjectProperty.homMk
    { app V := F.obj.map (smallEtaleBaseChangeProj B X hX U V.unop).op
      naturality V V' g := by
        change F.obj.map g ≫ F.obj.map (smallEtaleBaseChangeProj B X hX U V'.unop).op =
          F.obj.map (smallEtaleBaseChangeProj B X hX U V.unop).op ≫
            F.obj.map ((smallEtalePostcompose B X hX U).map
              ((smallEtaleBaseChange B U.obj.hom).map g.unop)).op
        rw [← F.obj.map_comp, ← F.obj.map_comp]
        change F.obj.map (smallEtaleBaseChangeProj B X hX U V'.unop ≫ g.unop).op = _
        rw [← smallEtaleBaseChangeProj_naturality]
        rfl }
  naturality F G α := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
    exact (α.hom.naturality (smallEtaleBaseChangeProj B X hX U V.unop).op).symm

/-- The restriction map on sections. -/
public theorem moduleRestrictionUnit_app_hom_app
    (F : Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ))
    (V : (SmallEtale B X hX)ᵒᵖ) :
    ((moduleRestrictionUnit B X hX U Λ).app F).hom.app V =
      F.obj.map (smallEtaleBaseChangeProj B X hX U V.unop).op :=
  rfl

/-- Naturality of a morphism of sheaves of modules, on elements. -/
private theorem sheaf_hom_app_map_apply {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Type*} [Ring R] {F G : Sheaf J (ModuleCat R)} (α : F ⟶ G) {V W : Cᵒᵖ} (f : V ⟶ W)
    (x : F.obj.obj V) : α.hom.app W (F.obj.map f x) = G.obj.map f (α.hom.app V x) :=
  ConcreteCategory.congr_hom (α.hom.naturality f) x

/-- Equal morphisms of sheaves of modules agree on elements. -/
private theorem sheaf_hom_app_apply_congr {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Type*} [Ring R] {F G : Sheaf J (ModuleCat R)} {α β : F ⟶ G} (h : α = β) (V : Cᵒᵖ)
    (x : F.obj.obj V) : α.hom.app V x = β.hom.app V x := by
  rw [h]

/-- The counit of `j_! ⊣ j^{-1}` sends the summand of `j_!j^{-1}ℱ` indexed by `φ : Q ⟶ U`,
carrying the restriction of a section `a` of `ℱ` over `Q`, back to `a`. -/
public theorem moduleExtensionByZeroAdjunction_counit_app_map_unit_app_restriction
    (F : Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ))
    (Q : SmallEtale B X hX) (φ : Q ⟶ U) (a : F.obj.obj (Opposite.op Q)) :
    ((moduleExtensionByZeroAdjunction B X hX U Λ).counit.app F).hom.app (Opposite.op Q)
      (((moduleExtensionByZero B X hX U Λ).obj ((moduleRestriction B X hX U Λ).obj F)).obj.map
        (smallEtaleLiftPostIso B X hX U Q φ).inv.op
        (((moduleExtensionByZeroAdjunction B X hX U Λ).unit.app
            ((moduleRestriction B X hX U Λ).obj F)).hom.app
          (Opposite.op (smallEtaleLift B X hX U Q φ))
          (((moduleRestriction B X hX U Λ).obj F).obj.map (smallEtaleLiftGraph B X hX U Q φ).op
            (((moduleRestrictionUnit B X hX U Λ).app F).hom.app (Opposite.op Q) a)))) = a := by
  let adj := moduleExtensionByZeroAdjunction B X hX U Λ
  let G := (moduleRestriction B X hX U Λ).obj F
  let e := smallEtaleLiftPostIso B X hX U Q φ
  let W := smallEtaleLift B X hX U Q φ
  let t := G.obj.map (smallEtaleLiftGraph B X hX U Q φ).op
    (((moduleRestrictionUnit B X hX U Λ).app F).hom.app (Opposite.op Q) a)
  change (adj.counit.app F).hom.app (Opposite.op Q)
    (((moduleExtensionByZero B X hX U Λ).obj G).obj.map e.inv.op
      ((adj.unit.app G).hom.app (Opposite.op W) t)) = a
  have hnat : (adj.counit.app F).hom.app (Opposite.op Q)
      (((moduleExtensionByZero B X hX U Λ).obj G).obj.map e.inv.op
        ((adj.unit.app G).hom.app (Opposite.op W) t)) =
      F.obj.map e.inv.op ((adj.counit.app F).hom.app
        (Opposite.op ((smallEtalePostcompose B X hX U).obj W))
        ((adj.unit.app G).hom.app (Opposite.op W) t)) :=
    sheaf_hom_app_map_apply _ _ _
  have htri : (adj.counit.app F).hom.app
      (Opposite.op ((smallEtalePostcompose B X hX U).obj W))
      ((adj.unit.app G).hom.app (Opposite.op W) t) = t :=
    sheaf_hom_app_apply_congr (adj.right_triangle_components F) _ t
  rw [hnat, htri]
  change F.obj.map e.inv.op (F.obj.map
    ((smallEtalePostcompose B X hX U).map (smallEtaleLiftGraph B X hX U Q φ)).op
      (F.obj.map (smallEtaleBaseChangeProj B X hX U Q).op a)) = a
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.obj.map_comp,
    ← F.obj.map_comp, ← op_comp, ← op_comp, Category.assoc,
    smallEtaleLiftPostIso_inv_comp_map_smallEtaleLiftGraph_comp_proj, op_id, F.obj.map_id]
  rfl

variable [IsFinite (B.inclusion.map U.obj.hom)]

/-- **The trace of a restricted section, over a neighbourhood split by `U`.** Over an étale
object `Q` of `X` on which `U` is described by finitely many pairwise disjoint morphisms
`φ_i : Q ⟶ U` whose graphs cover `Q ×_X U`, the trace of the restriction of a section `a` of `ℱ`
over `Q` is `a` multiplied by the number of the `φ_i`. -/
public theorem moduleTrace_app_moduleRestrictionUnit_app_eq_natCard_smul
    (F : Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ))
    (Q : SmallEtale B X hX) {ι : Type u} [Finite ι] (φ : ι → (Q ⟶ U))
    (hcov : ∀ z : ((smallEtaleBaseChange B U.obj.hom).obj Q).obj.left.1,
      ∃ i, z ∈ Set.range (B.inclusion.map
        (smallEtaleLiftGraph B X hX U Q (φ i)).hom.left))
    (hd : Pairwise (fun i j => smallEtaleArrowsDisjoint B X hX U Q (φ i) (φ j)))
    (a : F.obj.obj (Opposite.op Q)) :
    ((moduleTrace B X hX U Λ).app F).hom.app (Opposite.op Q)
      (((moduleRestrictionUnit B X hX U Λ).app F).hom.app (Opposite.op Q) a) =
        Nat.card ι • a := by
  classical
  have := Fintype.ofFinite ι
  have : IsSeparated (B.inclusion.map U.obj.hom) := IsSeparated.of_isAffineHom _
  let G := (moduleRestriction B X hX U Λ).obj F
  let A := forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}
  let G' := (sheafCompose (SmallEtale.topology B U.obj.left.1 U.obj.left.property) A).obj G
  let θ := (moduleExtensionByZeroToPushforward B X hX U Λ).app G
  let s := ((moduleRestrictionUnit B X hX U Λ).app F).hom.app (Opposite.op Q) a
  have hy := Presheaf.app_sum_eq_of_graphCover
    (smallEtalePostcompose B X hX U)
    (smallEtaleBaseChange B U.obj.hom)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property) G'.obj G'.isSeparated
    (((moduleExtensionByZero B X hX U Λ).obj G).obj ⋙ A)
    (Functor.whiskerRight θ.hom A)
    (fun W => A.map (((moduleExtensionByZeroAdjunction B X hX U Λ).unit.app G).hom.app
      (Opposite.op W)))
    (smallEtaleGraph B X hX U)
    (moduleExtensionByZeroToPushforward_graph B X hX U Λ G)
    (fun i => smallEtaleLift B X hX U Q (φ i))
    (fun i => smallEtaleLiftPostIso B X hX U Q (φ i))
    (SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective
      B U.obj.left.1 U.obj.left.property _ _ hcov)
    (fun i j hij =>
      moduleExtensionByZeroToPushforward_graph_compl B X hX U Λ G _ _ _
        (disjointFromSmallEtaleGraph_smallEtaleLiftGraph B X hX U Q (φ i) (φ j) (hd hij)))
    s
  let adj := moduleExtensionByZeroAdjunction B X hX U Λ
  let e := fun i => smallEtaleLiftPostIso B X hX U Q (φ i)
  let W := fun i => smallEtaleLift B X hX U Q (φ i)
  let t := fun i => G.obj.map (smallEtaleLiftGraph B X hX U Q (φ i)).op s
  let y : ((moduleExtensionByZero B X hX U Λ).obj G).obj.obj (Opposite.op Q) :=
    ∑ i, ((moduleExtensionByZero B X hX U Λ).obj G).obj.map (e i).inv.op
      ((adj.unit.app G).hom.app (Opposite.op (W i)) (t i))
  have hy' : θ.hom.app (Opposite.op Q) y = s := hy
  have hinv : ((moduleExtensionByZeroIsoPushforward B X hX U Λ).inv.app G).hom.app
      (Opposite.op Q) s = y := by
    rw [← hy']
    exact sheaf_hom_app_apply_congr
      ((moduleExtensionByZeroIsoPushforward B X hX U Λ).hom_inv_id_app G) _ y
  have htr : ((moduleTrace B X hX U Λ).app F).hom.app (Opposite.op Q) s =
      (adj.counit.app F).hom.app (Opposite.op Q)
        (((moduleExtensionByZeroIsoPushforward B X hX U Λ).inv.app G).hom.app
          (Opposite.op Q) s) := rfl
  change ((moduleTrace B X hX U Λ).app F).hom.app (Opposite.op Q) s = _
  rw [htr, hinv, map_sum, Finset.sum_congr rfl fun i _ =>
      moduleExtensionByZeroAdjunction_counit_app_map_unit_app_restriction B X hX U Λ F Q (φ i) a,
    Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **Restriction followed by the trace is multiplication by the degree** (Stacks, Section 03SH).
If the finite étale morphism `U ⟶ X` has constant degree `d`, then for every sheaf of
`Λ`-modules `ℱ` on `X_étale` the composite `ℱ ⟶ j_*j^{-1}ℱ ⟶ ℱ` of restriction and the trace
of Stacks 03SE is multiplication by `d`. -/
public theorem moduleRestrictionUnit_comp_moduleTrace (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map U.obj.hom) d]
    (F : Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ)) :
    (moduleRestrictionUnit B X hX U Λ).app F ≫ (moduleTrace B X hX U Λ).app F = d • 𝟙 F := by
  let τ := (moduleRestrictionUnit B X hX U Λ).app F ≫ (moduleTrace B X hX U Λ).app F
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  change τ.hom.app V a = d • a
  let R : Sieve V.unop :=
    { arrows := fun Y f => F.obj.map f.op (τ.hom.app V a) = F.obj.map f.op (d • a)
      downward_closed := by
        intro Y Z f hf g
        rw [op_comp, F.obj.map_comp, ModuleCat.comp_apply, ModuleCat.comp_apply, hf] }
  refine F.isSeparated V.unop R ?_ _ _ fun Y f hf => hf
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  obtain ⟨Q, q, hx, ι, hι, φ, hcov, hd, hN⟩ :=
    exists_smallEtaleArrows_cover_natCard B X hX U V.unop x
  refine ⟨Q, q, ?_, hx⟩
  obtain ⟨n, -⟩ := hx
  have : Nonempty (B.inclusion.obj Q.obj.left) := ⟨n⟩
  change F.obj.map q.op (τ.hom.app V a) = F.obj.map q.op (d • a)
  have hnat : τ.hom.app (Opposite.op Q) (F.obj.map q.op a) = F.obj.map q.op (τ.hom.app V a) :=
    sheaf_hom_app_map_apply τ q.op a
  rw [← hnat, map_nsmul, ← hN d inferInstance]
  exact moduleTrace_app_moduleRestrictionUnit_app_eq_natCard_smul B X hX U Λ F Q φ hcov hd _

attribute [local instance] moduleSheaf_hasSheafify in
/-- **The cohomological consequence of the method of the trace, for an arbitrary additive
functor.** If multiplication by the degree `d` is an isomorphism on `ℱ`, then every right derived
functor of an additive functor `Γ` takes restriction `ℱ ⟶ j_*j^{-1}ℱ` to a monomorphism: it is
split by the image of the trace, up to the isomorphism `Rⁿ Γ(d)`. -/
public theorem mono_rightDerived_map_moduleRestrictionUnit_app (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map U.obj.hom) d]
    {D : Type*} [Category* D] [Abelian D]
    [HasInjectiveResolutions (Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ))]
    (Γ : Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ) ⥤ D) [Γ.Additive]
    (F : Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ)) [IsIso (d • 𝟙 F)]
    (n : ℕ) :
    Mono ((Γ.rightDerived n).map ((moduleRestrictionUnit B X hX U Λ).app F)) := by
  have h := congrArg (Γ.rightDerived n).map (moduleRestrictionUnit_comp_moduleTrace B X hX U Λ d F)
  rw [Functor.map_comp] at h
  have : Mono ((Γ.rightDerived n).map ((moduleRestrictionUnit B X hX U Λ).app F) ≫
      (Γ.rightDerived n).map ((moduleTrace B X hX U Λ).app F)) := by
    rw [h]
    infer_instance
  exact mono_of_mono _ ((Γ.rightDerived n).map ((moduleTrace B X hX U Λ).app F))

end AlgebraicGeometry

end
