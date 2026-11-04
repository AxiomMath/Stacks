module

public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaCaseBSummand
public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.SliceTransition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageCocontinuous
public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CocontinuousUnit

/-!
# The transition of a simplicial site of case (B), localized along an arrow

In case (B) of a simplicial site the transition `u_φ : C_m ⥤ Cₙ` of a simplex map `φ : [n] ⟶ [m]`
is cocontinuous. For `W` in `C_m`, `Q` in `Cₙ` and `b : u_φ(W) ⟶ Q` it localizes to the
cocontinuous `h : C_m/W ⥤ Cₙ/Q`, `W' ↦ (u_φ W' ⟶ u_φ W ⟶ Q)`, with the direct image of modules
`h_*` along the localized structure map. The arrows `(φ, 𝟙)` of the total category give the
localized transition `h^*(M|_Q) ⟶ M|_c` for modules `M` on the total slice at `Q`, along the arrow
`c : W ⟶ u_φ W ⟶ Q`, and it is invertible on the structure sheaf.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.CartesianSlice.sliceDirectTransition`: the direct form
  `M|_Q ⟶ h_*(M|_c)`.
* `CategoryTheory.CocontinuousSimplicialSite.CartesianSlice.sliceTransitionB`: the localized
  transition, as a `CategoryTheory.SimplicialSiteSituation.CartesianSlice.SliceTransition`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.CocontinuousSimplicialSite.CartesianSlice

variable (C : CocontinuousSimplicialSite.{u})
  (P : Sheaf (situation C).totalTopology CommRingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m) {W : (situation C).component m}
  {Q : (situation C).component n} (b : (transitionFunctorB C φ).obj W ⟶ Q)

/-- The localized transition functor `Over W ⥤ Over Q`: the transition functor on slices,
followed by `b`. -/
abbrev sliceTransition : Over W ⥤ Over Q :=
  Over.post (transitionFunctorB C φ) ⋙ Over.map b

/-- The localized transition functor is cocontinuous. -/
instance isCocontinuous_sliceTransition :
    (sliceTransition C φ b).IsCocontinuous (((situation C).componentTopology m).over W)
      (((situation C).componentTopology n).over Q) :=
  isCocontinuous_comp _ _ _
    (((situation C).componentTopology n).over ((transitionFunctorB C φ).obj W))

/-- The localized transition functor lies over the transition functor. -/
theorem sliceTransition_comp_forget :
    sliceTransition C φ b ⋙ Over.forget Q = Over.forget W ⋙ transitionFunctorB C φ := rfl

/-- The arrow `W ⟶ Q` of the total category: the canonical arrow `W ⟶ u_φ W` followed by `b`. -/
abbrev canonicalArrow :
    (CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) m).obj W ⟶
      (CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q :=
  (Grothendieck.ιNatTrans (F := C.underlying) φ.op).app W ≫
    (CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).map b

/-- The localized ring map `O_n|_Q ⟶ h_*(O_m|_W)`. -/
abbrev sliceRing :
    ((ringSheafB C P n).over Q) ⟶
      ((sliceTransition C φ b).sheafPushforwardCocontinuous RingCat.{u}
        (((situation C).componentTopology m).over W)
        (((situation C).componentTopology n).over Q)).obj ((ringSheafB C P m).over W) :=
  Stacks.SheafOfModules.structureMapSquare (J' := ((situation C).componentTopology m).over W)
    (K' := ((situation C).componentTopology n).over Q) (fSharpB C P φ)
    (sliceTransition_comp_forget C φ b)

/-- The localized direct image `h_*`. -/
abbrev slicePushforward :
    SheafOfModules.{u} ((ringSheafB C P m).over W) ⥤
      SheafOfModules.{u} ((ringSheafB C P n).over Q) :=
  Stacks.SheafOfModules.pushforwardCocontinuous.{u} (sliceTransition C φ b) (sliceRing C P φ b)

/-- The localized direct image is a right adjoint. -/
instance isRightAdjoint_slicePushforward : (slicePushforward C P φ b).IsRightAdjoint :=
  inferInstance

/-- The localized pullback `h^*`. -/
abbrev slicePullback :
    SheafOfModules.{u} ((ringSheafB C P n).over Q) ⥤
      SheafOfModules.{u} ((ringSheafB C P m).over W) :=
  (slicePushforward C P φ b).leftAdjoint

/-- The localized pullback is left adjoint to the localized direct image. -/
abbrev slicePullbackAdj : slicePullback C P φ b ⊣ slicePushforward C P φ b :=
  Adjunction.ofIsRightAdjoint _

/-- The total structure sheaf of case (B), read as a sheaf of rings. -/
abbrev totalRing : Sheaf (situation C).totalTopology RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P

/-- The inclusion of the degree-`n` slice at `Q` into the total slice. -/
abbrev sliceInclusion (Q : (situation C).component n) :
    Over Q ⥤
      Over ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q) :=
  SimplicialSiteSituation.CartesianSlice.sliceInclusion (situation C) Q

/-- The inclusion of the degree-`m` slice at `W` into the total slice at `Q`, along the arrow. -/
abbrev sliceInclusionAt :
    Over W ⥤
      Over ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q) :=
  SimplicialSiteSituation.CartesianSlice.sliceInclusionAt (situation C) (canonicalArrow C φ b)

/-- The arrows `(φ, 𝟙)` localized: a natural transformation `λ ⟶ h ⋙ μ`. -/
def sliceNatTrans : sliceInclusionAt C φ b ⟶ sliceTransition C φ b ⋙ sliceInclusion C Q where
  app Y := Over.homMk ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app Y.left) (by
    change (Grothendieck.ιNatTrans (F := C.underlying) φ.op).app Y.left ≫
        (CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).map
          ((transitionFunctorB C φ).map Y.hom ≫ b) =
      (CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) m).map Y.hom ≫
        (Grothendieck.ιNatTrans (F := C.underlying) φ.op).app W ≫
          (CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).map b
    have h1 := Functor.map_comp (Grothendieck.ι C.underlying (op n))
      ((transitionFunctorB C φ).map Y.hom) b
    have h2 := (Grothendieck.ιNatTrans (F := C.underlying) φ.op).naturality Y.hom
    exact (congrArg (_ ≫ ·) h1).trans (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (Grothendieck.ι C.underlying (op n)).map b) h2.symm)).trans
        (Category.assoc _ _ _)))
  naturality Y Y' g :=
    Over.OverMorphism.ext ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).naturality g.left)

/-- Restriction of modules on the total slice at `Q` to the degree-`n` slice at `Q`. -/
abbrev sliceRestriction (Q : (situation C).component n) :
    SheafOfModules.{u} ((totalRing C P).over
        ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)) ⥤
      SheafOfModules.{u} ((ringSheafB C P n).over Q) :=
  SimplicialSiteSituation.CartesianSlice.sliceRestriction (situation C) (totalRing C P) Q

/-- Restriction of modules on the total slice at `Q` to the degree-`m` slice at `W`. -/
abbrev sliceRestrictionAt :
    SheafOfModules.{u} ((totalRing C P).over
        ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)) ⥤
      SheafOfModules.{u} ((ringSheafB C P m).over W) :=
  SimplicialSiteSituation.CartesianSlice.sliceRestrictionAt (situation C) (totalRing C P)
    (canonicalArrow C φ b)

variable (G : SheafOfModules.{u} ((totalRing C P).over
  ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)))

/-- The underlying presheaf map of the localized direct transition: the adjunct, along the
right Kan extension, of the restriction maps of `G` along `λ ⟶ h ⋙ μ`. -/
def sliceDirectPresheaf :
    ((sliceRestriction C P Q).obj G).val.presheaf ⟶
      (sliceTransition C φ b).op.ran.obj ((sliceRestrictionAt C P φ b).obj G).val.presheaf :=
  ((sliceTransition C φ b).op.ranAdjunction AddCommGrpCat.{u}).homEquiv _ _
    (Functor.whiskerRight (NatTrans.op (sliceNatTrans C φ b)) G.val.presheaf)

/-- **The legs of the localized direct transition**: restriction along `ψ` followed by restriction
along the arrow `(φ, 𝟙)`. -/
theorem sliceDirectPresheaf_app_comp_ranπ (X : (Over Q)ᵒᵖ)
    (j : StructuredArrow X (sliceTransition C φ b).op) :
    (sliceDirectPresheaf C P φ b G).app X ≫
        Stacks.SheafOfModules.ranπ (sliceTransition C φ b).op
          ((sliceRestrictionAt C P φ b).obj G).val.presheaf X j =
      ((sliceRestriction C P Q).obj G).val.presheaf.map j.hom ≫
        G.val.presheaf.map ((sliceNatTrans C φ b).app j.right.unop).op :=
  Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ _ _ X j

/-- The ring map through which a section of `O_n|_Q` acts on the leg at `(W', ψ)`. -/
theorem scalarπ_sliceRing (X : (Over Q)ᵒᵖ) (j : StructuredArrow X (sliceTransition C φ b).op)
    (r : ((ringSheafB C P n).over Q).obj.obj X) :
    (Stacks.SheafOfModules.scalarπ (sliceTransition C φ b)
        (Stacks.SheafOfModules.structureMapPresheaf (sliceTransition C φ b) (sliceRing C P φ b))
        X j).hom r =
      (((totalRing C P).over _).obj.map ((sliceNatTrans C φ b).app j.right.unop).op).hom
        ((((totalRing C P).over _).obj.map ((sliceInclusion C Q).map j.hom.unop).op).hom r) := by
  refine (Stacks.SheafOfModules.scalarπ_square_apply
    (J' := ((situation C).componentTopology m).over W)
    (K' := ((situation C).componentTopology n).over Q) (fSharpB C P φ)
    (sliceTransition_comp_forget C φ b) X j r).trans ?_
  refine (fSharpB_leg C P φ _ _ r).trans ?_
  have e : (Stacks.SheafOfModules.squareIndex (sliceTransition_comp_forget C φ b) j).hom =
      (Over.forget Q).op.map j.hom := Category.comp_id _
  exact (congrArg (fun g => ((ringTransitionB C P φ).app _).hom
    (((ringSheafB C P n).obj.map g).hom r)) e).trans rfl

/-- **The localized direct transition is linear.** -/
theorem smulPresheaf_comp_sliceDirectPresheaf (X : (Over Q)ᵒᵖ)
    (r : ((ringSheafB C P n).over Q).obj.obj X) :
    Stacks.SheafOfModules.smulPresheaf ((sliceRestriction C P Q).obj G).val X r ≫
        (sliceDirectPresheaf C P φ b G).app X =
      (sliceDirectPresheaf C P φ b G).app X ≫
        Stacks.SheafOfModules.ranSMul (sliceTransition C φ b)
          (Stacks.SheafOfModules.structureMapPresheaf (sliceTransition C φ b) (sliceRing C P φ b))
          ((sliceRestrictionAt C P φ b).obj G).val X r := by
  refine Stacks.SheafOfModules.ran_hom_ext (sliceTransition C φ b).op _ (fun j => ?_)
  have hL : (Stacks.SheafOfModules.smulPresheaf ((sliceRestriction C P Q).obj G).val X r ≫
        (sliceDirectPresheaf C P φ b G).app X) ≫
        Stacks.SheafOfModules.ranπ (sliceTransition C φ b).op
          ((sliceRestrictionAt C P φ b).obj G).val.presheaf X j =
      ((sliceRestriction C P Q).obj G).val.presheaf.map j.hom ≫
        G.val.presheaf.map ((sliceNatTrans C φ b).app j.right.unop).op ≫
          Stacks.SheafOfModules.smulPresheaf ((sliceRestrictionAt C P φ b).obj G).val j.right
            ((Stacks.SheafOfModules.scalarπ (sliceTransition C φ b)
              (Stacks.SheafOfModules.structureMapPresheaf (sliceTransition C φ b)
                (sliceRing C P φ b)) X j).hom r) :=
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (sliceDirectPresheaf_app_comp_ranπ C P φ b G X j))).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (Stacks.SheafOfModules.smulPresheaf_map
          ((sliceRestriction C P Q).obj G).val j.hom r))).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          ((Stacks.SheafOfModules.smulPresheaf_map G.val
            ((sliceNatTrans C φ b).app j.right.unop).op _).trans
            (congrArg (fun s => G.val.presheaf.map ((sliceNatTrans C φ b).app j.right.unop).op ≫
                Stacks.SheafOfModules.smulPresheaf ((sliceRestrictionAt C P φ b).obj G).val
                  j.right s)
              (scalarπ_sliceRing C P φ b X j r).symm)))))
  have hR : ((sliceDirectPresheaf C P φ b G).app X ≫
        Stacks.SheafOfModules.ranSMul (sliceTransition C φ b)
          (Stacks.SheafOfModules.structureMapPresheaf (sliceTransition C φ b) (sliceRing C P φ b))
          ((sliceRestrictionAt C P φ b).obj G).val X r) ≫
        Stacks.SheafOfModules.ranπ (sliceTransition C φ b).op
          ((sliceRestrictionAt C P φ b).obj G).val.presheaf X j =
      ((sliceRestriction C P Q).obj G).val.presheaf.map j.hom ≫
        G.val.presheaf.map ((sliceNatTrans C φ b).app j.right.unop).op ≫
          Stacks.SheafOfModules.smulPresheaf ((sliceRestrictionAt C P φ b).obj G).val j.right
            ((Stacks.SheafOfModules.scalarπ (sliceTransition C φ b)
              (Stacks.SheafOfModules.structureMapPresheaf (sliceTransition C φ b)
                (sliceRing C P φ b)) X j).hom r) :=
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (Stacks.SheafOfModules.ranSMul_π (sliceTransition C φ b) _ _ X r j))).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (sliceDirectPresheaf_app_comp_ranπ C P φ b G X j))).trans (Category.assoc _ _ _))
  exact hL.trans hR.symm

/-- The localized direct transition at one module, on underlying presheaves of modules. -/
def sliceDirectVal :
    ((sliceRestriction C P Q).obj G).val ⟶ ((slicePushforward C P φ b).obj
      ((sliceRestrictionAt C P φ b).obj G)).val :=
  PresheafOfModules.homMk (sliceDirectPresheaf C P φ b G)
    (fun X r x =>
      ConcreteCategory.congr_hom (smulPresheaf_comp_sliceDirectPresheaf C P φ b G X r) x)

variable {G} in
/-- The localized direct transition is natural in the module, on every leg. -/
theorem sliceDirectPresheaf_naturality {G' : SheafOfModules.{u} ((totalRing C P).over
    ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))}
    (g₀ : G.val.presheaf ⟶ G'.val.presheaf) (X : (Over Q)ᵒᵖ)
    (j : StructuredArrow X (sliceTransition C φ b).op) :
    ((Functor.whiskerLeft (sliceInclusion C Q).op g₀).app X ≫
        (sliceDirectPresheaf C P φ b G').app X) ≫
        Stacks.SheafOfModules.ranπ (sliceTransition C φ b).op
          ((sliceRestrictionAt C P φ b).obj G').val.presheaf X j =
      ((sliceDirectPresheaf C P φ b G).app X ≫
        ((sliceTransition C φ b).op.ran.map
          (Functor.whiskerLeft (sliceInclusionAt C φ b).op g₀)).app X) ≫
        Stacks.SheafOfModules.ranπ (sliceTransition C φ b).op
          ((sliceRestrictionAt C P φ b).obj G').val.presheaf X j := by
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (sliceDirectPresheaf_app_comp_ranπ C P φ b G' X j))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    ((Functor.whiskerLeft (sliceInclusion C Q).op g₀).naturality j.hom).symm)).trans ?_
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (g₀.naturality ((sliceNatTrans C φ b).app j.right.unop).op).symm)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Stacks.SheafOfModules.ranπ_map_functor
    (sliceTransition C φ b).op (Functor.whiskerLeft (sliceInclusionAt C φ b).op g₀) X j).symm)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ _) (sliceDirectPresheaf_app_comp_ranπ C P φ b G X j).symm)
  exact (Category.assoc _ _ _).symm

/-- **The localized direct transition** `μ^* ⟶ λ^* ⋙ h_*`. -/
def sliceDirectTransition :
    sliceRestriction C P Q ⟶ sliceRestrictionAt C P φ b ⋙ slicePushforward C P φ b where
  app G := ⟨sliceDirectVal C P φ b G⟩
  naturality G G' g := by
    refine SheafOfModules.hom_ext ?_
    refine (PresheafOfModules.toPresheaf _).map_injective ?_
    refine NatTrans.ext (funext fun X => Stacks.SheafOfModules.ran_hom_ext
      (sliceTransition C φ b).op _ fun j => ?_)
    exact sliceDirectPresheaf_naturality C P φ b ((PresheafOfModules.toPresheaf _).map g.val) X j

/-- **The localized transition** `h^* μ^* ⟶ λ^*`: the mate of the direct form. -/
def sliceTransitionModules :
    sliceRestriction C P Q ⋙ slicePullback C P φ b ⟶ sliceRestrictionAt C P φ b :=
  Functor.whiskerRight (sliceDirectTransition C P φ b) (slicePullback C P φ b) ≫
    Functor.whiskerLeft (sliceRestrictionAt C P φ b) (slicePullbackAdj C P φ b).counit

/-- The localized transition at one module is the transpose of the localized direct transition. -/
theorem sliceTransitionModules_app :
    (sliceTransitionModules C P φ b).app G =
      ((slicePullbackAdj C P φ b).homEquiv _ _).symm ((sliceDirectTransition C P φ b).app G) := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- The localized direct transition on the structure sheaf has leg `1` at the final object. -/
theorem ranπ_sliceDirectTransition_unit_one :
    (Stacks.SheafOfModules.ranπ (sliceTransition C φ b).op
        (SheafOfModules.unit ((ringSheafB C P m).over W)).val.presheaf (op (Over.mk (𝟙 Q)))
        (Stacks.SheafOfModules.terminalIndex (sliceTransition C φ b) Over.mkIdTerminal
          (Over.mk (𝟙 W)))).hom
      (((SimplicialSiteSituation.CartesianSlice.sliceRestrictionUnitHom (situation C)
          (totalRing C P) Q ≫
        (sliceDirectTransition C P φ b).app (SheafOfModules.unit _) ≫
        (slicePushforward C P φ b).map (inv
          (SimplicialSiteSituation.CartesianSlice.sliceRestrictionAtUnitHom (situation C)
            (totalRing C P) (canonicalArrow C φ b)))).val.app (op (Over.mk (𝟙 Q)))).hom
        (1 : ((ringSheafB C P n).over Q).obj.obj (op (Over.mk (𝟙 Q))))) =
      (1 : ((ringSheafB C P m).over W).obj.obj (op (Over.mk (𝟙 W)))) := by
  have h2 := ConcreteCategory.congr_hom (Stacks.SheafOfModules.ranπ_map_functor
    (sliceTransition C φ b).op ((PresheafOfModules.toPresheaf _).map (inv
          (SimplicialSiteSituation.CartesianSlice.sliceRestrictionAtUnitHom (situation C)
            (totalRing C P) (canonicalArrow C φ b))).val) (op (Over.mk (𝟙 Q)))
    (Stacks.SheafOfModules.terminalIndex (sliceTransition C φ b) Over.mkIdTerminal
          (Over.mk (𝟙 W))))
    (((SimplicialSiteSituation.CartesianSlice.sliceRestrictionUnitHom (situation C)
          (totalRing C P) Q ≫
        (sliceDirectTransition C P φ b).app (SheafOfModules.unit _)).val.app
          (op (Over.mk (𝟙 Q)))).hom
        (1 : ((ringSheafB C P n).over Q).obj.obj (op (Over.mk (𝟙 Q)))))
  refine h2.trans ?_
  have h3 := ConcreteCategory.congr_hom (sliceDirectPresheaf_app_comp_ranπ C P φ b
    (SheafOfModules.unit _) (op (Over.mk (𝟙 Q)))
    (Stacks.SheafOfModules.terminalIndex (sliceTransition C φ b) Over.mkIdTerminal
          (Over.mk (𝟙 W))))
    (1 : ((ringSheafB C P n).over Q).obj.obj (op (Over.mk (𝟙 Q))))
  have h4 : ((((sliceRestriction C P Q).obj (SheafOfModules.unit _)).val.presheaf.map
        (Stacks.SheafOfModules.terminalIndex (sliceTransition C φ b) Over.mkIdTerminal
          (Over.mk (𝟙 W))).hom ≫
      (SheafOfModules.unit ((totalRing C P).over
        ((CategoryTheory.SimplicialSiteSituation.componentFunctor
          (situation C) n).obj Q))).val.presheaf.map
        ((sliceNatTrans C φ b).app (Over.mk (𝟙 W))).op)).hom
      (1 : ((ringSheafB C P n).over Q).obj.obj (op (Over.mk (𝟙 Q)))) =
        (1 : ((totalRing C P).over _).obj.obj
          (op ((sliceInclusionAt C φ b).obj (Over.mk (𝟙 W))))) :=
    (congrArg (((SheafOfModules.unit ((totalRing C P).over
        ((CategoryTheory.SimplicialSiteSituation.componentFunctor
          (situation C) n).obj Q))).val.presheaf.map
      ((sliceNatTrans C φ b).app (Over.mk (𝟙 W))).op).hom)
        (PresheafOfModules.unit_map_one _ _)).trans (PresheafOfModules.unit_map_one _ _)
  have h5 := congrArg (fun t : SheafOfModules.unit ((ringSheafB C P m).over W) ⟶
      SheafOfModules.unit ((ringSheafB C P m).over W) => (t.val.app (op (Over.mk (𝟙 W)))).hom
        (1 : ((ringSheafB C P m).over W).obj.obj (op (Over.mk (𝟙 W)))))
    (IsIso.hom_inv_id (SimplicialSiteSituation.CartesianSlice.sliceRestrictionAtUnitHom
      (situation C) (totalRing C P) (canonicalArrow C φ b)))
  exact (congrArg _ (h3.trans h4)).trans h5

/-- **The localized transition is invertible on the structure sheaf.** -/
theorem isIso_sliceTransitionModules_app_unit :
    IsIso ((sliceTransitionModules C P φ b).app (SheafOfModules.unit _)) := by
  have hmain := Stacks.SheafOfModules.isIso_homEquiv_symm_of_ranπ_one (sliceTransition C φ b)
    (sliceRing C P φ b) (Over.mkIdTerminal (X := W)) (Over.mkIdTerminal (X := Q))
    (slicePullbackAdj C P φ b) _ (ranπ_sliceDirectTransition_unit_one C P φ b)
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm] at hmain
  rw [sliceTransitionModules_app]
  have h1 : IsIso (((slicePullbackAdj C P φ b).homEquiv _ _).symm
      ((sliceDirectTransition C P φ b).app (SheafOfModules.unit _)) ≫
      inv (SimplicialSiteSituation.CartesianSlice.sliceRestrictionAtUnitHom (situation C)
            (totalRing C P) (canonicalArrow C φ b))) :=
    IsIso.of_isIso_comp_left ((slicePullback C P φ b).map
      (SimplicialSiteSituation.CartesianSlice.sliceRestrictionUnitHom (situation C)
          (totalRing C P) Q)) _
  exact IsIso.of_isIso_comp_right _
    (inv (SimplicialSiteSituation.CartesianSlice.sliceRestrictionAtUnitHom (situation C)
      (totalRing C P) (canonicalArrow C φ b)))

/-- The localized transition of case (B) at the arrow `W ⟶ u_φ W ⟶ Q`. -/
def sliceTransitionB :
    SimplicialSiteSituation.CartesianSlice.SliceTransition (O := totalRing C P)
      (canonicalArrow C φ b) where
  Φ := slicePullback C P φ b
  preservesColimits := (slicePullbackAdj C P φ b).leftAdjoint_preservesColimits
  τ := sliceTransitionModules C P φ b
  isIso_τ_app_unit := isIso_sliceTransitionModules_app_unit C P φ b

end CategoryTheory.CocontinuousSimplicialSite.CartesianSlice
