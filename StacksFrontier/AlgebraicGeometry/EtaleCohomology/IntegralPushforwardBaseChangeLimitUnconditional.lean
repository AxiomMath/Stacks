module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalkUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardStages
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardStagesUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.BasicUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Step
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBaseChangeLimit
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBaseChangeLimit

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardCylinder
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardCylinderUnconditional
public import StacksFrontier.AlgebraicGeometry.Limits.StageLiftsCompactness

/-!
# IntegralPushforwardBaseChangeLimitUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBaseChangeLimit`, stated as
separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- Geometric points with the same residue field and equal morphisms are equal. -/
private theorem geometricPoint_mk_eq {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    {a b : Spec (.of K) ⟶ S} (h : a = b) :
    (⟨K, a⟩ : GeometricPoint S) = ⟨K, b⟩ :=
  congrArg (fun m => (⟨K, m⟩ : GeometricPoint S)) h

/-- A map into the pullback is determined by its composites with the projections. -/
private theorem comp_lift_eq_of_comp_eq {C : Type*} [Category C] {P X Y Z T W : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (hP : IsPullback fst snd f g)
    (a : T ⟶ X) (b : T ⟶ Y) (w : a ≫ f = b ≫ g) (u : W ⟶ T) (v : W ⟶ P)
    (h₁ : u ≫ a = v ≫ fst) (h₂ : u ≫ b = v ≫ snd) : u ≫ hP.lift a b w = v :=
  hP.hom_ext (by rw [Category.assoc, hP.lift_fst, h₁]) (by rw [Category.assoc, hP.lift_snd, h₂])

section StageRealization

variable {XV Z V : B.Scheme} (pk : XV ⟶ Z) (zk : Z ⟶ V) [IsFinite (B.inclusion.map zk)]
  (w : GeometricPoint V.1) (FV : Sheaf (SmallEtale.topology B XV.1 XV.property)
    (Type (max (u + 1) v)))

/-- **Realization at a finite stage.** Let `zk : Z ⟶ V` be finite and `pk : X_V ⟶ Z` arbitrary,
and let `t z` be prescribed elements of the stalks of `pk_* FV` at the lifts `z` of a geometric
point `w` of `V`. Then there is a section over the base change to `X_V` of an étale neighbourhood
of `w` whose germ at every lift `x` of `w` to `X_V` is the image of `t` at the lift `x ∘ pk`.
This is the surjectivity in Stacks 03QP for the finite morphism `zk`. -/
theorem exists_section_of_finite_stage_univ
    (t : ∀ z : {a : w.source ⟶ Z.1 // a ≫ B.inclusion.map zk = w.hom},
      etaleStalk B Z.1 Z.property ⟨w.residueField, z.1⟩
        ((B.smallPushforward pk (Type (max (u + 1) v))).obj FV).obj) :
    ∃ (W : (geometricPointFiber B V.1 V.property w).Elements)
      (s : FV.obj.obj (op ((smallEtaleBaseChange B pk).obj ((smallEtaleBaseChange B zk).obj W.1)))),
      ∀ (x : {a : w.source ⟶ XV.1 // a ≫ B.inclusion.map pk ≫ B.inclusion.map zk = w.hom}),
        colimit.ι ((Functor.Elements.π (geometricPointFiber B XV.1 XV.property
            ⟨w.residueField, x.1⟩)).op ⋙ FV.obj)
          (op (Functor.elementsMk _
            ((smallEtaleBaseChange B pk).obj ((smallEtaleBaseChange B zk).obj W.1))
            (baseChangeEtalePoint B pk (x := ⟨w.residueField, x.1⟩)
              (y := ⟨w.residueField, x.1 ≫ B.inclusion.map pk⟩) rfl
              ((smallEtaleBaseChange B zk).obj W.1)
              (liftedEtaleNeighborhood B zk w ⟨x.1 ≫ B.inclusion.map pk,
                (Category.assoc _ _ _).trans x.2⟩ W).2))) s =
          pushforwardEtaleStalkComponentUniv B pk ⟨w.residueField, x.1⟩
            ⟨w.residueField, x.1 ≫ B.inclusion.map pk⟩ rfl FV
            (t ⟨x.1 ≫ B.inclusion.map pk, (Category.assoc _ _ _).trans x.2⟩) := by
  classical
  let H := (B.smallPushforward pk (Type (max (u + 1) v))).obj FV
  obtain ⟨ζ, hζ⟩ := (finitePushforwardStalkToProduct_bijective_univ B zk w H).2 t
  obtain ⟨W0, s, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit
    ((Functor.Elements.π (geometricPointFiber B V.1 V.property w)).op ⋙
      ((B.smallPushforward zk (Type (max (u + 1) v))).obj H).obj)) ζ
  refine ⟨W0.unop, s, fun x => ?_⟩
  let z : {a : w.source ⟶ Z.1 // a ≫ B.inclusion.map zk = w.hom} :=
    ⟨x.1 ≫ B.inclusion.map pk, (Category.assoc _ _ _).trans x.2⟩
  have h1 : finitePushforwardStalkComponentUniv B zk w H z
      (colimit.ι ((Functor.Elements.π (geometricPointFiber B V.1 V.property w)).op ⋙
        ((B.smallPushforward zk (Type (max (u + 1) v))).obj H).obj) (op W0.unop) s) = t z :=
    congrFun hζ z
  rw [← (finitePushforwardStalkComponent_germ_univ B zk w H z W0.unop s).symm.trans h1]
  exact (pushforwardEtaleStalkComponent_germ_baseChange_univ B pk
    (x := ⟨w.residueField, x.1⟩) (y := ⟨w.residueField, x.1 ≫ B.inclusion.map pk⟩) rfl
    ((smallEtaleBaseChange B zk).obj W0.unop.1)
    (liftedEtaleNeighborhood B zk w z W0.unop).2 FV s).symm

end StageRealization

section Realization

variable {X' X Y' Y : B.Scheme} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
    (B.inclusion.map g))
  (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
  {V XV : B.Scheme} (ιX : XV ⟶ X) [Etale (B.inclusion.map ιX)] {fV : XV ⟶ V} (ι : V ⟶ Y)
  (hV : ιX ≫ f = fV ≫ ι) (P : SmallEtaleIntegralStages B fV)
  (y' : GeometricPoint Y'.1)

include hV in
/-- **The family attached to an element of `f'_* (g')⁻¹ F` is locally given by stage sections.**
For a lift `p₀` of `y'` through `f'` and a lift `x₀` of `p₀ ∘ g'` to `X_V`, the element `c_{p₀}`
is the germ of a section over the base change of a stage neighbourhood, and that section
represents `c_p` for every `(p, x)` with `x` agreeing with `x₀` at some later stage. -/
theorem exists_stage_section_cylinder_univ
    (c : etaleStalk B Y'.1 Y'.property y' ((B.smallPushforward f' _).obj
      ((B.smallInverseImage g' (Type (max (u + 1) v))).obj F)).obj)
    (p₀ : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
    (x₀ : y'.source ⟶ B.inclusion.obj XV)
    (hx₀ : x₀ ≫ B.inclusion.map ιX = p₀.1 ≫ B.inclusion.map g') :
    ∃ (i : P.indexᵒᵖ)
      (W : (geometricPointFiber B (P.diagram.obj i).1 (P.diagram.obj i).property
        ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩).Elements)
      (τ : F.obj.obj (op (cylinderObjGeneral B ιX P y' i x₀ W)))
      (j : P.indexᵒᵖ) (a : j ⟶ i),
      ∀ (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
        (x : y'.source ⟶ B.inclusion.obj XV)
        (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
        (hxj : x ≫ B.inclusion.map (P.proj.app j) = x₀ ≫ B.inclusion.map (P.proj.app j)),
        cylinderGermGeneral B sq F ιX P y' i x₀ W τ p x hx (by
            rw [← P.proj_comp_map a, Functor.map_comp, ← Category.assoc, hxj,
              Category.assoc]) =
          pullbackStalkComponentUniv B sq F y' c p := by
  let incl := B.inclusion
  obtain ⟨U0, τ0, hτ0⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit
    ((Functor.Elements.π (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) (y'.map (B.inclusion.map g))
        (cartesianLiftEquiv B g' f' f g sq y' p₀)))).op ⋙ F.obj))
    (pullbackStalkComponentUniv B sq F y' c p₀)
  let U := U0.unop
  have hz : (⟨y'.residueField, x₀⟩ : GeometricPoint (B.inclusion.obj XV)).map (incl.map ιX) =
      geometricPointLift (B.inclusion.map f) (y'.map (B.inclusion.map g))
        (cartesianLiftEquiv B g' f' f g sq y' p₀) :=
    congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint (B.inclusion.obj X))) hx₀
  let UV : (geometricPointFiber B XV.1 XV.property ⟨y'.residueField, x₀⟩).Elements :=
    Functor.elementsMk _ ((smallEtaleBaseChange B ιX).obj U.1)
      (baseChangeEtalePoint B ιX hz U.1 U.2)
  obtain ⟨i, W, φ, hφ⟩ := P.exists_stage_neighborhood ⟨y'.residueField, x₀⟩ UV
  let T := cylinderObjGeneral B ιX P y' i x₀ W
  let TSV := SmallEtale.toScheme B XV.1 XV.property
  let TS := SmallEtale.toScheme B X.1 X.property
  let m : TS.obj T ⟶ TS.obj U.1 := TSV.map φ ≫ incl.map (pullback.fst U.1.obj.hom ιX)
  have hφs : TSV.map φ ≫ incl.map ((smallEtaleBaseChange B ιX).obj U.1).obj.hom =
      incl.map ((smallEtaleBaseChange B (P.proj.app i)).obj W.1).obj.hom :=
    SmallEtale.toScheme_map_comp B _ _ φ
  have hm : m ≫ incl.map U.1.obj.hom = incl.map T.obj.hom := by
    have e₁ : incl.map (pullback.fst U.1.obj.hom ιX) ≫ incl.map U.1.obj.hom =
        incl.map (pullback.snd U.1.obj.hom ιX) ≫ incl.map ιX :=
      (isPullback_smallEtaleBaseChange_inclusion B ιX U.1).w
    have e₂ : incl.map T.obj.hom =
        incl.map (pullback.snd W.1.obj.hom (P.proj.app i)) ≫ incl.map ιX :=
      B.inclusion.map_comp _ _
    rw [e₂]
    exact (Category.assoc _ _ _).trans ((congrArg (TSV.map φ ≫ ·) e₁).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ incl.map ιX) hφs)))
  let ψ : T ⟶ U.1 := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk m) (by
    apply ObjectProperty.hom_ext
    exact hm))
  let τ := F.obj.map ψ.op τ0
  have hcylφ : (cylinderPointGeneral B sq ιX P y' i x₀ W p₀ x₀ hx₀ rfl).1 ≫ TSV.map φ = UV.2.1 := by
    refine Eq.trans ?_ hφ
    congr 1
  have hcylψ : (cylinderPointGeneral B sq ιX P y' i x₀ W p₀ x₀ hx₀ rfl).1 ≫ TS.map ψ = U.2.1 := by
    change _ ≫ (TSV.map φ ≫ incl.map (pullback.fst U.1.obj.hom ιX)) = U.2.1
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hcylφ).trans ?_)
    refine (baseChangeEtalePointHom_fst B ιX hz U.1 U.2).trans ?_
    simp
  let pt := geometricPointLift (B.inclusion.map f) (y'.map (B.inclusion.map g))
    (cartesianLiftEquiv B g' f' f g sq y' p₀)
  let Tel : (geometricPointFiber B X.1 X.property pt).Elements :=
    Functor.elementsMk _ T (cylinderPointGeneral B sq ιX P y' i x₀ W p₀ x₀ hx₀ rfl)
  let ψe : Tel ⟶ U := ⟨ψ, Subtype.ext hcylψ⟩
  have H₀ : cylinderGermGeneral B sq F ιX P y' i x₀ W τ p₀ x₀ hx₀ rfl =
      pullbackStalkComponentUniv B sq F y' c p₀ :=
    (ConcreteCategory.congr_hom (colimit.w ((Functor.Elements.π (geometricPointFiber B X.1
      X.property pt)).op ⋙ F.obj) ψe.op) τ0).trans hτ0
  exact ⟨i, W, τ, exists_stage_forall_cylinderGerm_eq_univ B sq F ιX ι hV P y' i x₀ W c τ p₀ hx₀ H₀⟩

/-- The germ of a stage section, read at a lift through the projection to the stage and then in
the stalk of `F` through the restriction along `X_V ⟶ X`, is the germ at the corresponding
`cylinderPointGeneral`. -/
theorem smallEtaleRestrictionStalkMap_stageComponent_general
    (i : P.indexᵒᵖ) (x₀ : y'.source ⟶ B.inclusion.obj XV)
    (W : (geometricPointFiber B (P.diagram.obj i).1 (P.diagram.obj i).property
      ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩).Elements)
    (τ : F.obj.obj (op (cylinderObjGeneral B ιX P y' i x₀ W)))
    (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
    (x : y'.source ⟶ B.inclusion.obj XV) (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
    (hxi : x ≫ B.inclusion.map (P.proj.app i) = x₀ ≫ B.inclusion.map (P.proj.app i)) :
    smallEtaleRestrictionStalkMapUniv B ιX x (p.1 ≫ B.inclusion.map g') hx F
        (pushforwardEtaleStalkComponentUniv B (P.proj.app i) ⟨y'.residueField, x⟩
          ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩
          (congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _)) hxi)
          ((smallEtaleRestrictionAlong B ιX _).obj F)
          (colimit.ι ((Functor.Elements.π (geometricPointFiber B (P.diagram.obj i).1
            (P.diagram.obj i).property ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩)).op ⋙
            ((B.smallPushforward (P.proj.app i) _).obj
              ((smallEtaleRestrictionAlong B ιX _).obj F)).obj)
            (op W) τ)) =
      cylinderGermGeneral B sq F ιX P y' i x₀ W τ p x hx hxi := by
  have e₁ := pushforwardEtaleStalkComponent_germ_baseChange_univ B (P.proj.app i)
    (x := ⟨y'.residueField, x⟩) (y := ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩)
    (geometricPoint_mk_eq hxi) W.1 W.2
    ((smallEtaleRestrictionAlong B ιX (Type (max (u + 1) v))).obj F) τ
  refine (congrArg (smallEtaleRestrictionStalkMapUniv B ιX x (p.1 ≫ B.inclusion.map g') hx F)
    e₁).trans ?_
  exact smallEtaleRestrictionStalkMap_germ_univ B ιX x (p.1 ≫ B.inclusion.map g') hx F
    (Functor.elementsMk _ ((smallEtaleBaseChange B (P.proj.app i)).obj W.1)
      (baseChangeEtalePoint B (P.proj.app i)
      (x := ⟨y'.residueField, x⟩) (y := ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩)
      (geometricPoint_mk_eq hxi) W.1 W.2)) τ

/-- **Stage elements from a cylinder.** Let `τ` be a stage section on a cylinder around `x₀` whose
germs represent `c_p` at every lift agreeing with `x₀` at stage `j`. For a later stage `k` and a
point `z` of stage `k` lying over the image of `x₀` at stage `j`, one element of the stalk of the
pushforward to stage `k` at `z` represents `c_p` at every lift of `z` to `X_V`. -/
private theorem exists_stageStalk_eq_pullbackStalkComponent_univ
    (c : etaleStalk B Y'.1 Y'.property y' ((B.smallPushforward f' _).obj
      ((B.smallInverseImage g' (Type (max (u + 1) v))).obj F)).obj)
    (i : P.indexᵒᵖ) (x₀ : y'.source ⟶ B.inclusion.obj XV)
    (W : (geometricPointFiber B (P.diagram.obj i).1 (P.diagram.obj i).property
      ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩).Elements)
    (τ : F.obj.obj (op (cylinderObjGeneral B ιX P y' i x₀ W)))
    {j : P.indexᵒᵖ} (a : j ⟶ i)
    (hτ : ∀ (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
      (x : y'.source ⟶ B.inclusion.obj XV)
      (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
      (hxj : x ≫ B.inclusion.map (P.proj.app j) = x₀ ≫ B.inclusion.map (P.proj.app j)),
      cylinderGermGeneral B sq F ιX P y' i x₀ W τ p x hx (by
          rw [← P.proj_comp_map a, Functor.map_comp, ← Category.assoc, hxj,
            Category.assoc]) =
        pullbackStalkComponentUniv B sq F y' c p)
    {k : P.indexᵒᵖ} (b : k ⟶ j) (z : y'.source ⟶ B.inclusion.obj (P.diagram.obj k))
    (hz : z ≫ B.inclusion.map (P.diagram.map b) = x₀ ≫ B.inclusion.map (P.proj.app j)) :
    ∃ t : etaleStalk B (P.diagram.obj k).1 (P.diagram.obj k).property ⟨y'.residueField, z⟩
        ((B.smallPushforward (P.proj.app k) (Type (max (u + 1) v))).obj
          ((smallEtaleRestrictionAlong B ιX (Type (max (u + 1) v))).obj F)).obj,
      ∀ (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
        (x : y'.source ⟶ B.inclusion.obj XV)
        (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
        (hxk : x ≫ B.inclusion.map (P.proj.app k) = z),
        smallEtaleRestrictionStalkMapUniv B ιX x (p.1 ≫ B.inclusion.map g') hx F
          (pushforwardEtaleStalkComponentUniv B (P.proj.app k) ⟨y'.residueField, x⟩
            ⟨y'.residueField, z⟩
            (congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _)) hxk)
            ((smallEtaleRestrictionAlong B ιX (Type (max (u + 1) v))).obj F) t) =
          pullbackStalkComponentUniv B sq F y' c p := by
  let FV := (smallEtaleRestrictionAlong B ιX (Type (max (u + 1) v))).obj F
  have hproj {l l' : P.indexᵒᵖ} (a : l ⟶ l') (x : y'.source ⟶ B.inclusion.obj XV) :
      x ≫ B.inclusion.map (P.proj.app l') =
        (x ≫ B.inclusion.map (P.proj.app l)) ≫ B.inclusion.map (P.diagram.map a) := by
    rw [Category.assoc, ← Functor.map_comp, P.proj_comp_map]
  have hk : P.proj.app i = P.proj.app k ≫ P.diagram.map (b ≫ a) := (P.proj_comp_map (b ≫ a)).symm
  have hzi : z ≫ B.inclusion.map (P.diagram.map (b ≫ a)) =
      x₀ ≫ B.inclusion.map (P.proj.app i) := by
    rw [hproj a, ← hz, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  let zp : GeometricPoint (B.inclusion.obj (P.diagram.obj k)) := ⟨y'.residueField, z⟩
  let sp : GeometricPoint (B.inclusion.obj (P.diagram.obj i)) :=
    ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩
  let e0 := colimit.ι ((Functor.Elements.π (geometricPointFiber B (P.diagram.obj i).1
      (P.diagram.obj i).property sp)).op ⋙
    ((B.smallPushforward (P.proj.app i) (Type (max (u + 1) v))).obj FV).obj) (op W) τ
  let m2 := (etaleStalkFunctor.{u, max (u + 1) v} B (P.diagram.obj i).1
    (P.diagram.obj i).property sp).map ((eqToIso (congrArg
      (fun m => B.smallPushforward m (Type (max (u + 1) v))) hk)).hom.app FV) e0
  let m1 := (etaleStalkFunctor.{u, max (u + 1) v} B (P.diagram.obj i).1
    (P.diagram.obj i).property sp).map ((smallEtaleSheafPushforwardCompIso B XV
      (P.diagram.obj k) (P.diagram.obj i) (P.proj.app k) (P.diagram.map (b ≫ a))
      (Type (max (u + 1) v))).inv.app FV) m2
  have hl : zp.map (B.inclusion.map (P.diagram.map (b ≫ a))) = sp :=
    geometricPoint_mk_eq hzi
  refine ⟨pushforwardEtaleStalkComponentUniv B (P.diagram.map (b ≫ a)) zp sp hl
    ((B.smallPushforward (P.proj.app k) (Type (max (u + 1) v))).obj FV) m1,
    fun p x hx hxk => ?_⟩
  let xp : GeometricPoint (B.inclusion.obj XV) := ⟨y'.residueField, x⟩
  have hxi : x ≫ B.inclusion.map (P.proj.app i) = x₀ ≫ B.inclusion.map (P.proj.app i) := by
    rw [hproj (b ≫ a) x, hxk, hzi]
  have hxj : x ≫ B.inclusion.map (P.proj.app j) = x₀ ≫ B.inclusion.map (P.proj.app j) := by
    rw [hproj b x, hxk, hz]
  have hm : xp.map (B.inclusion.map (P.proj.app k ≫ P.diagram.map (b ≫ a))) = sp :=
    geometricPoint_mk_eq ((congrArg (x ≫ ·) (congrArg B.inclusion.map hk)).symm.trans hxi)
  have hc : xp.map (B.inclusion.map (P.proj.app i)) = sp := geometricPoint_mk_eq hxi
  have e₁ := (pushforwardEtaleStalkComponent_comp_univ B (P.proj.app k) (P.diagram.map (b ≫ a))
    (w := xp) (t := zp) (s := sp)
    (geometricPoint_mk_eq hxk) hl hm FV m2).symm
  have e₂ := pushforwardEtaleStalkComponent_eqToHom_univ B (P.proj.app i)
    (P.proj.app k ≫ P.diagram.map (b ≫ a)) hk xp sp hc hm FV e0
  have e₃ := smallEtaleRestrictionStalkMap_stageComponent_general B sq F ιX P y' i x₀ W τ p x hx
    hxi
  exact (congrArg (smallEtaleRestrictionStalkMapUniv B ιX x (p.1 ≫ B.inclusion.map g') hx F)
    (e₁.trans e₂)).trans (e₃.trans (hτ p x hx hxj))

/-- **The germ of `f_* F` from a section over a finite stage.** For an étale `ι : V ⟶ Y` through
which `g ∘ y'` factors and a section `s` over the base change to `X_V` of an étale neighbourhood
`W` at a finite stage, there is an element of the stalk of `f_* F` at `g ∘ y'` whose component at
every lift of `y'` is the image in the stalk of `F` of the germ of `s` at the corresponding
lift. -/
private theorem exists_pushforwardEtaleStalk_eq_restriction_stageGerm_univ
    [Etale (B.inclusion.map ι)]
    (sqV : IsPullback (B.inclusion.map ιX) (B.inclusion.map fV) (B.inclusion.map f)
      (B.inclusion.map ι))
    (yV : y'.source ⟶ B.inclusion.obj V) (hyV : yV ≫ B.inclusion.map ι = y'.hom ≫ B.inclusion.map g)
    (k : P.indexᵒᵖ) (W : (geometricPointFiber B V.1 V.property ⟨y'.residueField, yV⟩).Elements)
    (s : ((smallEtaleRestrictionAlong B ιX (Type (max (u + 1) v))).obj F).obj.obj
      (op ((smallEtaleBaseChange B (P.proj.app k)).obj
        ((smallEtaleBaseChange B (P.str.app k)).obj W.1)))) :
    ∃ ζ : etaleStalk B Y.1 Y.property (y'.map (B.inclusion.map g))
        ((B.smallPushforward f (Type (max (u + 1) v))).obj F).obj,
      ∀ (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
        (x : y'.source ⟶ B.inclusion.obj XV)
        (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
        (hxV : x ≫ B.inclusion.map fV = yV),
        pushforwardEtaleStalkComponentUniv B f (geometricPointLift (B.inclusion.map f)
            (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' p))
          (y'.map (B.inclusion.map g))
          (geometricPointLift_map (B.inclusion.map f) (y'.map (B.inclusion.map g))
            (cartesianLiftEquiv B g' f' f g sq y' p)) F ζ =
        smallEtaleRestrictionStalkMapUniv B ιX x (p.1 ≫ B.inclusion.map g') hx F
          (colimit.ι ((Functor.Elements.π (geometricPointFiber B XV.1 XV.property
              ⟨y'.residueField, x⟩)).op ⋙
              ((smallEtaleRestrictionAlong B ιX (Type (max (u + 1) v))).obj F).obj)
            (op (Functor.elementsMk _ ((smallEtaleBaseChange B (P.proj.app k)).obj
                ((smallEtaleBaseChange B (P.str.app k)).obj W.1))
              (baseChangeEtalePoint B (P.proj.app k) (x := ⟨y'.residueField, x⟩)
                (y := ⟨y'.residueField, x ≫ B.inclusion.map (P.proj.app k)⟩) rfl
                ((smallEtaleBaseChange B (P.str.app k)).obj W.1)
                (liftedEtaleNeighborhood B (P.str.app k) ⟨y'.residueField, yV⟩
                  ⟨x ≫ B.inclusion.map (P.proj.app k), by
                    rw [Category.assoc, ← Functor.map_comp, P.fac, hxV]⟩ W).2))) s) := by
  let incl := B.inclusion
  let pJ := P.proj.app k
  let sJ := P.str.app k
  have hfac : incl.map (P.proj.app k) ≫ incl.map (P.str.app k) = incl.map fV := by
    rw [← Functor.map_comp, P.fac k]
  let yVp : GeometricPoint (incl.obj V) := ⟨y'.residueField, yV⟩
  let NY := (smallEtaleRestrictionNeighborhoods B ι yV (y'.hom ≫ incl.map g) hyV).obj W
  have hR : IsPullback (incl.map (pullback.fst NY.1.obj.hom f))
      (incl.map (pullback.snd NY.1.obj.hom f)) (incl.map NY.1.obj.hom) (incl.map f) :=
    isPullback_smallEtaleBaseChange_inclusion B f NY.1
  have hNY : incl.map NY.1.obj.hom = incl.map W.1.obj.hom ≫ incl.map ι := B.inclusion.map_comp _ _
  have hRw : incl.map (pullback.snd NY.1.obj.hom f) ≫ incl.map f =
      (incl.map (pullback.fst NY.1.obj.hom f) ≫ incl.map W.1.obj.hom) ≫ incl.map ι :=
    hR.w.symm.trans ((congrArg (incl.map (pullback.fst NY.1.obj.hom f) ≫ ·) hNY).trans
      (Category.assoc _ _ _).symm)
  let ξ := sqV.lift (incl.map (pullback.snd NY.1.obj.hom f))
    (incl.map (pullback.fst NY.1.obj.hom f) ≫ incl.map W.1.obj.hom) hRw
  have hM : IsPullback (incl.map (pullback.fst W.1.obj.hom sJ))
      (incl.map (pullback.snd W.1.obj.hom sJ)) (incl.map W.1.obj.hom) (incl.map sJ) :=
    isPullback_smallEtaleBaseChange_inclusion B sJ W.1
  have hξ : incl.map (pullback.fst NY.1.obj.hom f) ≫ incl.map W.1.obj.hom =
      (ξ ≫ incl.map pJ) ≫ incl.map sJ :=
    (sqV.lift_snd _ _ _).symm.trans ((congrArg (ξ ≫ ·) hfac).symm.trans
      (Category.assoc _ _ _).symm)
  let mid := hM.lift (incl.map (pullback.fst NY.1.obj.hom f)) (ξ ≫ incl.map pJ) hξ
  have hL : IsPullback (incl.map (pullback.fst ((smallEtaleBaseChange B sJ).obj W.1).obj.hom pJ))
      (incl.map (pullback.snd ((smallEtaleBaseChange B sJ).obj W.1).obj.hom pJ))
      (incl.map ((smallEtaleBaseChange B sJ).obj W.1).obj.hom) (incl.map pJ) :=
    isPullback_smallEtaleBaseChange_inclusion B pJ ((smallEtaleBaseChange B sJ).obj W.1)
  let κs := hL.lift mid ξ (hM.lift_snd _ _ _)
  let LT := (smallEtalePostcompose B X.1 X.property (SmallEtale.ofEtaleHom B ιX)).obj
    ((smallEtaleBaseChange B pJ).obj ((smallEtaleBaseChange B sJ).obj W.1))
  have hκ : κs ≫ incl.map LT.obj.hom = incl.map ((smallEtaleBaseChange B f).obj NY.1).obj.hom := by
    have e : incl.map LT.obj.hom =
        incl.map (pullback.snd ((smallEtaleBaseChange B sJ).obj W.1).obj.hom pJ) ≫ incl.map ιX :=
      B.inclusion.map_comp _ _
    exact (congrArg (κs ≫ ·) e).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ incl.map ιX) (hL.lift_snd _ _ _)).trans (sqV.lift_fst _ _ _)))
  let κ : (smallEtaleBaseChange B f).obj NY.1 ⟶ LT :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk κs) (by
      apply ObjectProperty.hom_ext
      exact hκ))
  refine ⟨colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.property
    (y'.map (B.inclusion.map g)))).op ⋙ ((B.smallPushforward f (Type (max (u + 1) v))).obj F).obj)
    (op NY) (F.obj.map κ.op s), fun p x hx hxV => ?_⟩
  let zx : {a : y'.source ⟶ incl.obj (P.diagram.obj k) // a ≫ incl.map sJ = yV} :=
    ⟨x ≫ incl.map pJ, (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) hfac).trans hxV)⟩
  let lifted := liftedEtaleNeighborhood B sJ yVp zx W
  let pt := baseChangeEtalePoint B pJ (x := ⟨y'.residueField, x⟩)
    (y := ⟨y'.residueField, x ≫ incl.map pJ⟩) rfl ((smallEtaleBaseChange B sJ).obj W.1) lifted.2
  let bcpY := baseChangeEtalePoint B f (geometricPointLift_map (B.inclusion.map f)
    (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' p)) NY.1 NY.2
  have hbfst : bcpY.1 ≫ incl.map (pullback.fst NY.1.obj.hom f) = W.2.1 := by
    refine (baseChangeEtalePointHom_fst B f (geometricPointLift_map (B.inclusion.map f)
      (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' p)) NY.1 NY.2).trans ?_
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  have hbsnd : bcpY.1 ≫ incl.map (pullback.snd NY.1.obj.hom f) = p.1 ≫ incl.map g' :=
    baseChangeEtalePointHom_snd B f (geometricPointLift_map (B.inclusion.map f)
      (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' p)) NY.1 NY.2
  have hW2 : W.2.1 ≫ incl.map W.1.obj.hom = yV := W.2.2
  have hbξ : bcpY.1 ≫ ξ = x :=
    comp_lift_eq_of_comp_eq sqV _ _ hRw _ _ (hbsnd.trans hx.symm)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ incl.map W.1.obj.hom) hbfst).trans (hW2.trans hxV.symm)))
  have hl1 : lifted.2.1 ≫ incl.map (pullback.fst W.1.obj.hom sJ) = W.2.1 :=
    liftedEtaleNeighborhood_point_fst B sJ yVp zx W
  have hl2 : lifted.2.1 ≫ incl.map (pullback.snd W.1.obj.hom sJ) = x ≫ incl.map pJ :=
    lifted.2.2
  have hbmid : bcpY.1 ≫ mid = lifted.2.1 :=
    comp_lift_eq_of_comp_eq hM _ _ _ _ _ (hbfst.trans hl1.symm)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ incl.map pJ) hbξ).trans hl2.symm))
  have hpt : bcpY.1 ≫ κs = pt.1 := by
    refine comp_lift_eq_of_comp_eq hL _ _ _ _ _ (hbmid.trans ?_)
      (hbξ.trans (baseChangeEtalePointHom_snd B pJ (x := ⟨y'.residueField, x⟩)
        (y := ⟨y'.residueField, x ≫ incl.map pJ⟩) rfl _ lifted.2).symm)
    refine Eq.trans ?_ (baseChangeEtalePointHom_fst B pJ (x := ⟨y'.residueField, x⟩)
      (y := ⟨y'.residueField, x ≫ incl.map pJ⟩) rfl _ lifted.2).symm
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  let qpt := geometricPointLift (B.inclusion.map f) (y'.map (B.inclusion.map g))
    (cartesianLiftEquiv B g' f' f g sq y' p)
  let DF := (Functor.Elements.π (geometricPointFiber B X.1 X.property qpt)).op ⋙ F.obj
  have hκpt : (bcpY.1 ≫ κs) ≫ incl.map LT.obj.hom = qpt.hom :=
    (Category.assoc _ _ _).trans ((congrArg (bcpY.1 ≫ ·) hκ).trans bcpY.2)
  let BCel : (geometricPointFiber B X.1 X.property qpt).Elements :=
    Functor.elementsMk _ ((smallEtaleBaseChange B f).obj NY.1) bcpY
  let LTel : (geometricPointFiber B X.1 X.property qpt).Elements :=
    Functor.elementsMk _ LT ⟨bcpY.1 ≫ κs, hκpt⟩
  let κe : BCel ⟶ LTel := ⟨κ, Subtype.ext rfl⟩
  have step₁ := pushforwardEtaleStalkComponent_germ_baseChange_univ B f
    (geometricPointLift_map (B.inclusion.map f) (y'.map (B.inclusion.map g))
      (cartesianLiftEquiv B g' f' f g sq y' p)) NY.1 NY.2 F (F.obj.map κ.op s)
  have step₂ := (ConcreteCategory.congr_hom (colimit.w DF κe.op) s)
  have step₃ := smallEtaleRestrictionStalkMap_germ_univ B ιX x (p.1 ≫ incl.map g') hx F
    (Functor.elementsMk _
      ((smallEtaleBaseChange B pJ).obj ((smallEtaleBaseChange B sJ).obj W.1)) pt) s
  let Eel := (smallEtaleRestrictionNeighborhoods B ιX x (p.1 ≫ incl.map g') hx).obj
    (Functor.elementsMk _
      ((smallEtaleBaseChange B pJ).obj ((smallEtaleBaseChange B sJ).obj W.1)) pt)
  have hid : (SmallEtale.toScheme B X.1 X.property).map (𝟙 LT) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  let idE : LTel ⟶ Eel := ⟨𝟙 LT, Subtype.ext ((congrArg (_ ≫ ·) hid).trans
    ((Category.comp_id _).trans hpt))⟩
  have step₄ := ConcreteCategory.congr_hom (colimit.w DF idE.op) s
  have hmapid : DF.map idE.op s = s := by
    change F.obj.map (𝟙 LT).op s = s
    rw [op_id, F.obj.map_id]
    rfl
  have step₄' : colimit.ι DF (op LTel) s = colimit.ι DF (op Eel) s :=
    (congrArg (colimit.ι DF (op LTel)) hmapid).symm.trans step₄
  exact step₁.trans (step₂.trans (step₄'.trans step₃.symm))

include hV P in
/-- **Realization of the family attached to an element of `f'_* (g')⁻¹ F`.** Given a presentation
of `X_V = X ×_Y V ⟶ V` by finite stages, for an étale `ι : V ⟶ Y` through which `g ∘ y'` factors,
every element `c` of the stalk of `f'_* (g')⁻¹ F` at `y'` comes, lift by lift, from one element of
the stalk of `f_* F` at `g ∘ y'`. -/
theorem exists_pushforwardEtaleStalk_eq_pullbackStalkComponent_univ
    [Etale (B.inclusion.map ι)] [IsIntegralHom (B.inclusion.map f)]
    (sqV : IsPullback (B.inclusion.map ιX) (B.inclusion.map fV) (B.inclusion.map f)
      (B.inclusion.map ι))
    (yV : y'.source ⟶ B.inclusion.obj V) (hyV : yV ≫ B.inclusion.map ι = y'.hom ≫ B.inclusion.map g)
    (c : etaleStalk B Y'.1 Y'.property y' ((B.smallPushforward f' _).obj
      ((B.smallInverseImage g' (Type (max (u + 1) v))).obj F)).obj) :
    ∃ ζ : etaleStalk B Y.1 Y.property (y'.map (B.inclusion.map g))
        ((B.smallPushforward f (Type (max (u + 1) v))).obj F).obj,
      ∀ p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom},
        pushforwardEtaleStalkComponentUniv B f (geometricPointLift (B.inclusion.map f)
            (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' p))
          (y'.map (B.inclusion.map g))
          (geometricPointLift_map (B.inclusion.map f) (y'.map (B.inclusion.map g))
            (cartesianLiftEquiv B g' f' f g sq y' p)) F ζ =
        pullbackStalkComponentUniv B sq F y' c p := by
  classical
  let incl := B.inclusion
  have hfV : IsIntegralHom (incl.map fV) := MorphismProperty.of_isPullback sqV inferInstance
  let FV := (smallEtaleRestrictionAlong B ιX (Type (max (u + 1) v))).obj F
  let LV := {a : y'.source ⟶ incl.obj XV // a ≫ incl.map fV = yV}
  have hq (xV : LV) : (xV.1 ≫ incl.map ιX) ≫ incl.map f = y'.hom ≫ incl.map g := by
    rw [Category.assoc, ← Functor.map_comp, hV, Functor.map_comp, ← Category.assoc, xV.2, hyV]
  let pOf (xV : LV) : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom} :=
    (cartesianLiftEquiv B g' f' f g sq y').symm ⟨xV.1 ≫ incl.map ιX, hq xV⟩
  have hpOf (xV : LV) : xV.1 ≫ incl.map ιX = (pOf xV).1 ≫ incl.map g' :=
    (congrArg Subtype.val ((cartesianLiftEquiv B g' f' f g sq y').apply_symm_apply
      ⟨xV.1 ≫ incl.map ιX, hq xV⟩)).symm
  choose iOf WOf τOf jOf aOf hOf using fun xV : LV =>
    exists_stage_section_cylinder_univ B sq F ιX ι hV P y' c (pOf xV) xV.1 (hpOf xV)
  -- finitely many cylinders cover the lifts
  let tY : P.diagram ⋙ incl ⟶ (Functor.const P.indexᵒᵖ).obj (incl.obj V) :=
    { app := fun k => incl.map (P.str.app k)
      naturality := fun k k' a => by
        change incl.map (P.diagram.map a) ≫ incl.map (P.str.app k') = incl.map (P.str.app k) ≫ 𝟙 _
        rw [Category.comp_id, ← Functor.map_comp]
        exact congrArg incl.map ((P.str.naturality a).trans (Category.comp_id _)) }
  have hfac (k : P.indexᵒᵖ) : incl.map (P.proj.app k) ≫ incl.map (P.str.app k) = incl.map fV := by
    rw [← Functor.map_comp, P.fac k]
  have hfin (k : P.indexᵒᵖ) : Finite {a : y'.source ⟶ (P.diagram ⋙ incl).obj k //
      a ≫ tY.app k = yV} := finite_lifts_of_isFinite (incl.map (P.str.app k)) yV
  obtain ⟨S, hS⟩ := exists_finset_forall_exists_comp_eq_of_isLimit (P.diagram ⋙ incl)
    (incl.mapCone (Cone.mk XV P.proj)) P.isLimit tY (incl.map fV) hfac yV jOf
  obtain ⟨J, hJ⟩ := Finset.exists_le (S.image fun xV => (jOf xV).unop)
  let aJ (xV : LV) (hxV : xV ∈ S) : Opposite.op J ⟶ jOf xV :=
    (homOfLE (hJ _ (Finset.mem_image_of_mem _ hxV))).op
  let pJ := P.proj.app (Opposite.op J)
  let sJ := P.str.app (Opposite.op J)
  have : IsIntegralHom (incl.map pJ) := P.isIntegralHom_proj _
  -- the stage elements
  have key : ∀ z : {a : y'.source ⟶ incl.obj (P.diagram.obj (Opposite.op J)) //
      a ≫ incl.map sJ = yV},
      ∃ t : etaleStalk B (P.diagram.obj (Opposite.op J)).1 (P.diagram.obj (Opposite.op J)).property
          ⟨y'.residueField, z.1⟩ ((B.smallPushforward pJ (Type (max (u + 1) v))).obj FV).obj,
        ∀ (x : LV) (hx : x.1 ≫ incl.map pJ = z.1),
          smallEtaleRestrictionStalkMapUniv B ιX x.1 ((pOf x).1 ≫ incl.map g') (hpOf x) F
            (pushforwardEtaleStalkComponentUniv B pJ ⟨y'.residueField, x.1⟩ ⟨y'.residueField, z.1⟩
              (congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _)) hx) FV t) =
          pullbackStalkComponentUniv B sq F y' c (pOf x) := by
    intro z
    by_cases hz : ∃ x : LV, x.1 ≫ incl.map pJ = z.1
    · obtain ⟨xt, hxt⟩ := hz
      obtain ⟨xS, hxS, hcov⟩ := hS xt
      have hzJ : z.1 ≫ incl.map (P.diagram.map (aJ xS hxS)) =
          xS.1 ≫ incl.map (P.proj.app (jOf xS)) := by
        rw [← hxt, Category.assoc, ← Functor.map_comp, P.proj_comp_map]
        exact hcov
      obtain ⟨t, ht⟩ := exists_stageStalk_eq_pullbackStalkComponent_univ B sq F ιX P y' c (iOf xS)
        xS.1 (WOf xS) (τOf xS) (aOf xS) (hOf xS) (aJ xS hxS) z.1 hzJ
      exact ⟨t, fun x hx => ht (pOf x) x.1 (hpOf x) hx⟩
    · have hE : IsEmpty {a : (⟨y'.residueField, z.1⟩ :
          GeometricPoint (incl.obj (P.diagram.obj (Opposite.op J)))).source ⟶ XV.1 //
          a ≫ incl.map pJ = (⟨y'.residueField, z.1⟩ :
            GeometricPoint (incl.obj (P.diagram.obj (Opposite.op J)))).hom} :=
        ⟨fun a => hz ⟨⟨a.1, by rw [← hfac, ← Category.assoc, a.2]; exact z.2⟩, a.2⟩⟩
      obtain ⟨t⟩ := nonempty_etaleStalk_pushforward_of_isEmpty_lifts_univ B pJ
        ⟨y'.residueField, z.1⟩ hE FV
      exact ⟨t, fun x hx => (hz ⟨x, hx⟩).elim⟩
  choose t ht using key
  let yVp : GeometricPoint (incl.obj V) := ⟨y'.residueField, yV⟩
  obtain ⟨W, s, hs⟩ := exists_section_of_finite_stage_univ B pJ sJ yVp FV t
  obtain ⟨ζ, hζ⟩ := exists_pushforwardEtaleStalk_eq_restriction_stageGerm_univ B sq F ιX ι P y'
    sqV yV hyV (Opposite.op J) W s
  refine ⟨ζ, fun p => ?_⟩
  have hcond : (p.1 ≫ incl.map g') ≫ incl.map f = yV ≫ incl.map ι := by
    rw [Category.assoc, sq.w, ← Category.assoc, p.2, hyV]
  obtain ⟨xV, rfl⟩ : ∃ xV : LV, pOf xV = p :=
    ⟨⟨sqV.lift (p.1 ≫ incl.map g') yV hcond, sqV.lift_snd _ _ _⟩,
      (cartesianLiftEquiv B g' f' f g sq y').symm_apply_eq.mpr
        (Subtype.ext (sqV.lift_fst _ _ _))⟩
  let xV' : {a : yVp.source ⟶ XV.1 // a ≫ incl.map pJ ≫ incl.map sJ = yVp.hom} :=
    ⟨xV.1, by rw [hfac]; exact xV.2⟩
  let zx : {a : y'.source ⟶ incl.obj (P.diagram.obj (Opposite.op J)) // a ≫ incl.map sJ = yV} :=
    ⟨xV.1 ≫ incl.map pJ, (Category.assoc _ _ _).trans xV'.2⟩
  exact (hζ (pOf xV) xV.1 (hpOf xV) xV.2).trans
    ((congrArg (smallEtaleRestrictionStalkMapUniv B ιX xV.1 ((pOf xV).1 ≫ incl.map g') (hpOf xV) F)
      (hs xV')).trans (ht zx xV rfl))

end Realization

section BaseChange

variable {X' X Y' Y : B.Scheme} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- A morphism from the spectrum of a field to a scheme of `B` factors through an affine open
immersion in `B`. -/
private theorem exists_isAffine_isOpenImmersion_lift {Y : B.Scheme} (K : Type u) [Field K]
    (y : Spec (.of K) ⟶ B.inclusion.obj Y) :
    ∃ (V : B.Scheme) (ι : V ⟶ Y) (_ : IsOpenImmersion (B.inclusion.map ι))
      (_ : IsAffine (B.inclusion.obj V)) (yV : Spec (.of K) ⟶ B.inclusion.obj V),
      yV ≫ B.inclusion.map ι = y := by
  obtain ⟨_, ⟨V0, hV0, rfl⟩, hyV0, -⟩ :=
    (B.inclusion.obj Y).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (y default)) isOpen_univ
  let V1 : (B.inclusion.obj Y).Opens := V0
  have hV1 : IsAffineOpen V1 := hV0
  have hVsize : B.Contains V1 := (Scheme.size_coe_opens_le _ V1).trans_lt Y.property
  let ι : B.obj V1 hVsize ⟶ Y := ObjectProperty.homMk V1.ι
  have : IsOpenImmersion (B.inclusion.map ι) := inferInstanceAs (IsOpenImmersion V1.ι)
  have hrange : Set.range y ⊆ Set.range V1.ι := by
    rintro _ ⟨a, rfl⟩
    refine ⟨⟨y a, ?_⟩, rfl⟩
    rw [Subsingleton.elim a default]
    exact hyV0
  exact ⟨B.obj V1 hVsize, ι, inferInstance, hV1, IsOpenImmersion.lift V1.ι y hrange,
    IsOpenImmersion.lift_fac _ _ _⟩

/-- **Stacks Project, Tag 0EYP.** Consider a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of schemes of a big étale site with `f` integral, and a sheaf of sets `F` on the small étale site
of `X`, with values in `Type (max (u + 1) v)` for any universe `v`. Then the canonical
comparison `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism.

The comparison is checked on stalks at the geometric points `y'` of `Y'`. Both stalks embed into
the product of the stalks of `F` over the lifts of `y'`, because for an integral morphism the
stalk of a direct image is detected at the lifts
(`AlgebraicGeometry.finitePushforwardStalkComponent_injective_univ`); this gives injectivity. For
surjectivity, an affine open neighbourhood `V` of the image of `y'` in `Y` is chosen, the integral
morphism `X ×_Y V ⟶ V` is written as a limit of finite morphisms (Stacks 09YZ), the family of
germs attached to an element of the target is shown to be given by stage sections on cylinders
of lifts (`AlgebraicGeometry.exists_stage_forall_cylinderGerm_eq_univ`), finitely many cylinders
cover the lifts (`AlgebraicGeometry.exists_finset_forall_exists_comp_eq_of_isLimit`), and the
finite case of the stalk computation, Stacks 03QP, at a common stage produces the required germ of
`f_* F`. -/
@[stacks 0EYP, sga "4 VIII 5.5" "more general"]
theorem isIso_smallEtaleBaseChangeNatTrans_of_isIntegralHom_univ
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsIntegralHom (B.inclusion.map f)] (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    IsIso ((smallEtaleBaseChangeNatTransUniv B g' f' f g h).app F) := by
  classical
  let incl := B.inclusion
  let G := (B.smallInverseImage g' (Type (max (u + 1) v))).obj F
  have hf' : IsIntegralHom (incl.map f') := MorphismProperty.of_isPullback sq inferInstance
  refine isIso_of_bijective_etaleStalkMap_univ B Y'.1 Y'.property _ fun y' => ?_
  let M := (etaleStalkFunctor.{u, max (u + 1) v} B Y'.1 Y'.property y').map
    ((smallEtaleBaseChangeNatTransUniv B g' f' f g h).app F)
  let ig := (smallEtalePullbackStalkIsoUniv B g y').app ((B.smallPushforward f _).obj F)
  have hcompat :=
    pushforwardEtaleStalkComponent_smallEtaleBaseChangeNatTrans_univ B g' f' f g sq h F y'
  have hI' := finitePushforwardStalkComponent_injective_univ B f' y' G
  have hI := finitePushforwardStalkComponent_injective_univ B f (y'.map (incl.map g)) F
  refine ⟨fun a b hab => ?_, fun c => ?_⟩
  · obtain ⟨ζa, rfl⟩ := ig.toEquiv.symm.surjective a
    obtain ⟨ζb, rfl⟩ := ig.toEquiv.symm.surjective b
    refine congrArg ig.toEquiv.symm (hI (funext fun q => ?_))
    obtain ⟨p, rfl⟩ := (cartesianLiftEquiv B g' f' f g sq y').surjective q
    have hab' := congrArg (fun z => pushforwardEtaleStalkComponentUniv B f'
      (geometricPointLift (B.inclusion.map f') y' p) y'
      (geometricPointLift_map (B.inclusion.map f') y' p) G z) hab
    exact ((smallEtalePullbackStalkIsoUniv B g' (geometricPointLift (B.inclusion.map f') y' p)).app
      F).symm.toEquiv.injective ((hcompat p ζa).symm.trans (hab'.trans (hcompat p ζb)))
  · obtain ⟨VB, ι, _, _, yV, hyV⟩ :=
      exists_isAffine_isOpenImmersion_lift B y'.residueField (y'.hom ≫ incl.map g)
    have : Etale (incl.map ι) := inferInstance
    -- the base change of `f` to `V` and its stages
    let := hasPullbacks_bigEtaleSite B
    let := preservesPullbacks_bigEtaleSiteInclusion B
    let ιX := pullback.fst f ι
    let fV := pullback.snd f ι
    have hV : ιX ≫ f = fV ≫ ι := pullback.condition
    have sqV : IsPullback (incl.map ιX) (incl.map fV) (incl.map f) (incl.map ι) :=
      (IsPullback.of_hasPullback f ι).map B.inclusion
    have : IsOpenImmersion (incl.map ιX) :=
      MorphismProperty.of_isPullback sqV.flip inferInstance
    have : Etale (incl.map ιX) := inferInstance
    have : IsIntegralHom (incl.map fV) := MorphismProperty.of_isPullback sqV inferInstance
    let P := SmallEtaleIntegralStages.ofIsAffine fV
    obtain ⟨ζ, hζ⟩ := exists_pushforwardEtaleStalk_eq_pullbackStalkComponent_univ B sq F ιX ι hV
      P y' sqV yV hyV c
    refine ⟨ig.toEquiv.symm ζ, hI' (funext fun p => ?_)⟩
    refine (hcompat p ζ).trans ?_
    change ((smallEtalePullbackStalkIsoUniv B g' (geometricPointLift (B.inclusion.map f') y' p)).app
      F).toEquiv.symm _ = _
    rw [hζ p]
    exact ((smallEtalePullbackStalkIsoUniv B g' (geometricPointLift (B.inclusion.map f') y' p)).app
      F).toEquiv.symm_apply_apply _

/-- At the coefficient universe `u + 1` of the size-bounded small étale sites,
`AlgebraicGeometry.smallEtaleBaseChangeNatTransUniv` is
`AlgebraicGeometry.smallEtaleBaseChangeNatTrans`: the two comparisons `g⁻¹ f_* ⟶ f'_* (g')⁻¹` have
the same definition, `max (u + 1) 0` being `u + 1`. -/
theorem smallEtaleBaseChangeNatTransUniv_eq_smallEtaleBaseChangeNatTrans (h : g' ≫ f = f' ≫ g) :
    smallEtaleBaseChangeNatTransUniv.{u, 0} B g' f' f g h =
      smallEtaleBaseChangeNatTrans B g' f' f g h :=
  rfl

/-- **The base change comparison along an integral morphism is a natural isomorphism.** For a
cartesian square `g' ≫ f = f' ≫ g` of a big étale site with `f` integral, the comparison
`AlgebraicGeometry.smallEtaleBaseChangeNatTrans` `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of sheaves of sets with
values in `Type (u + 1)` is an isomorphism of functors. This is
`isIso_smallEtaleBaseChangeNatTrans_of_isIntegralHom_univ` (Stacks 0EYP) at `v = 0`, read through
`smallEtaleBaseChangeNatTransUniv_eq_smallEtaleBaseChangeNatTrans`; its components are the
comparison that `AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans_of_isIntegralHom` is about,
with no colimit presentation needed. -/
theorem isIso_smallEtaleBaseChangeNatTrans_of_isPullback_of_isIntegralHom
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsIntegralHom (B.inclusion.map f)] (h : g' ≫ f = f' ≫ g) :
    IsIso (smallEtaleBaseChangeNatTrans B g' f' f g h) := by
  rw [← smallEtaleBaseChangeNatTransUniv_eq_smallEtaleBaseChangeNatTrans]
  have := isIso_smallEtaleBaseChangeNatTrans_of_isIntegralHom_univ.{0} B g' f' f g sq h
  exact NatIso.isIso_of_isIso_app _

end BaseChange

end AlgebraicGeometry
