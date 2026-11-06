module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardCylinder
public import StacksFrontier.AlgebraicGeometry.Limits.StageLiftsCompactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale base change for the direct image along an integral morphism, on stalks

Consider a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of schemes of a big étale site with `f` integral, and a sheaf of sets `F` on the small étale site
of `X`. This file proves that the canonical comparison
`AlgebraicGeometry.smallEtaleBaseChangeNatTrans`, `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F`, is an
isomorphism: the statement of [Stacks, Tag 0EYP] for sheaves of sets.

The source writes `X` locally as a limit of finite morphisms `X_i ⟶ Y` and passes the finite case,
[Stacks, Tag 0959], through colimits of sheaves. Here the same reduction is carried out on stalks
at the geometric points `y'` of `Y'`.

* *Injectivity.* For an integral morphism the stalk of a direct image is detected at the lifts of
  the geometric point
  (`AlgebraicGeometry.finitePushforwardStalkComponent_injective_of_isIntegralHom`); the stalk
  map of the comparison is compatible with these components
  (`AlgebraicGeometry.pushforwardEtaleStalkComponent_smallEtaleBaseChangeNatTrans`), and the
  lifts of `y'` through `f'` correspond to the lifts of `g ∘ y'` through `f`.
* *Surjectivity.* An element `c` of the stalk of `f'_* (g')⁻¹ F` gives, lift by lift, elements
  `c_p` of the stalks of `F`. Over an affine open `V` of `Y` the morphism `X ×_Y V ⟶ V` is a limit
  of finite morphisms ([Stacks, Tag 09YZ]). Each `c_p` is the germ of a section over the base
  change of an étale neighbourhood at a finite stage (descent of affine étale schemes to a stage,
  [Stacks, Tag 0EYL]), and that section represents `c_{p'}` for all `p'` on a cylinder around `p`
  (`AlgebraicGeometry.exists_stage_forall_cylinderGerm_eq`). The lifts form a compact space, so
  finitely many cylinders cover them, and at a common finite stage the stalk computation of
  [Stacks, Tag 03QP] for the finite structure morphism glues the stage elements into a germ of
  `f_* F` (`AlgebraicGeometry.exists_section_of_finite_stage`).

## Main results

* `AlgebraicGeometry.exists_section_of_finite_stage` — realization of prescribed stage germs at a
  finite stage.
* `AlgebraicGeometry.exists_stage_section_cylinder` — the family attached to an element of the
  target is given by stage sections on cylinders.
* `AlgebraicGeometry.exists_pushforwardEtaleStalk_eq_pullbackStalkComponent` — that family comes
  from one germ of `f_* F`.
* `AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans_app_of_isIntegralHom` — the comparison is
  an isomorphism for an integral `f`.

## Implementation notes

The statement is proved for sheaves with values in `Type (u + 1)`, the coefficient universe of
the size-bounded small étale sites of a big étale site `B : BigEtaleSite.{u}` used throughout this
development. `AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans_of_isIntegralHom` is the same
statement granted a colimit presentation of the comparison by finite stages; the proof here needs
no such presentation.

## References

* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section StageRealization

variable {XV Z V : B.Scheme} (pk : XV ⟶ Z) (zk : Z ⟶ V) [IsFinite (B.inclusion.map zk)]
  (w : GeometricPoint V.1) (FV : Sheaf (SmallEtale.topology B XV.1 XV.property)
    (Type (u + 1)))

/-- **Realization at a finite stage.** Let `zk : Z ⟶ V` be finite and `pk : X_V ⟶ Z` arbitrary,
and let `t z` be prescribed elements of the stalks of `pk_* FV` at the lifts `z` of a geometric
point `w` of `V`. Then there is a section over the base change to `X_V` of an étale neighbourhood
of `w` whose germ at every lift `x` of `w` to `X_V` is the image of `t` at the lift `x ∘ pk`.
This is the surjectivity in Stacks 03QP for the finite morphism `zk`. -/
theorem exists_section_of_finite_stage
    (t : ∀ z : {a : w.source ⟶ Z.1 // a ≫ B.inclusion.map zk = w.hom},
      etaleStalk B Z.1 Z.property ⟨w.residueField, z.1⟩
        ((B.smallPushforward pk (Type (u + 1))).obj FV).obj) :
    ∃ (W : (geometricPointFiber B V.1 V.property w).Elements)
      (s : FV.obj.obj (op ((smallEtaleBaseChange B pk).obj ((smallEtaleBaseChange B zk).obj W.1)))),
      ∀ (x : {a : w.source ⟶ XV.1 // a ≫ B.inclusion.map pk ≫ B.inclusion.map zk = w.hom}),
        colimit.ι ((CategoryOfElements.π (geometricPointFiber B XV.1 XV.property
            ⟨w.residueField, x.1⟩)).op ⋙ FV.obj)
          (op (Functor.elementsMk _ ((smallEtaleBaseChange B pk).obj ((smallEtaleBaseChange B zk).obj W.1))
            (baseChangeEtalePoint B pk (x := ⟨w.residueField, x.1⟩)
              (y := ⟨w.residueField, x.1 ≫ B.inclusion.map pk⟩) rfl
              ((smallEtaleBaseChange B zk).obj W.1)
              (liftedEtaleNeighborhood B zk w ⟨x.1 ≫ B.inclusion.map pk,
                (Category.assoc _ _ _).trans x.2⟩ W).2))) s =
          pushforwardEtaleStalkComponent B pk ⟨w.residueField, x.1⟩
            ⟨w.residueField, x.1 ≫ B.inclusion.map pk⟩ rfl FV
            (t ⟨x.1 ≫ B.inclusion.map pk, (Category.assoc _ _ _).trans x.2⟩) := by
  classical
  let H := (B.smallPushforward pk (Type (u + 1))).obj FV
  obtain ⟨ζ, hζ⟩ := (finitePushforwardStalkToProduct_bijective B zk w H).2 t
  obtain ⟨W0, s, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit
    ((CategoryOfElements.π (geometricPointFiber B V.1 V.property w)).op ⋙
      ((B.smallPushforward zk (Type (u + 1))).obj H).obj)) ζ
  refine ⟨W0.unop, s, fun x => ?_⟩
  let z : {a : w.source ⟶ Z.1 // a ≫ B.inclusion.map zk = w.hom} :=
    ⟨x.1 ≫ B.inclusion.map pk, (Category.assoc _ _ _).trans x.2⟩
  rw [← (finitePushforwardStalkComponent_germ B zk w H z W0.unop s).symm.trans (congrFun hζ z)]
  exact (pushforwardEtaleStalkComponent_germ_baseChange B pk
    (x := ⟨w.residueField, x.1⟩) (y := ⟨w.residueField, x.1 ≫ B.inclusion.map pk⟩) rfl
    ((smallEtaleBaseChange B zk).obj W0.unop.1)
    (liftedEtaleNeighborhood B zk w z W0.unop).2 FV s).symm

end StageRealization

section Realization

/-- A morphism `a ≫ h.lift x y w` into a pullback is determined by its two projections. -/
private theorem comp_lift_eq_of_comp_eq {C : Type*} [Category C] {P X Y Z T U : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    {a : T ⟶ U} {x : U ⟶ X} {y : U ⟶ Y} (w : x ≫ f = y ≫ g) {z : T ⟶ P}
    (h₁ : a ≫ x = z ≫ fst) (h₂ : a ≫ y = z ≫ snd) : a ≫ h.lift x y w = z :=
  h.hom_ext (by rw [Category.assoc, h.lift_fst, h₁]) (by rw [Category.assoc, h.lift_snd, h₂])

variable {X' X Y' Y : B.Scheme} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
    (B.inclusion.map g))
  (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
  {V XV : B.Scheme} (ιX : XV ⟶ X) [Etale (B.inclusion.map ιX)] {fV : XV ⟶ V} (ι : V ⟶ Y)
  (hV : ιX ≫ f = fV ≫ ι) (P : SmallEtaleIntegralStages B fV)
  (y' : GeometricPoint Y'.1)

include hV in
/-- **The family attached to an element of `f'_* (g')⁻¹ F` is locally given by stage sections.**
For a lift `p₀` of `y'` through `f'` and a lift `x₀` of `p₀ ∘ g'` to `X_V`, the element `c_{p₀}`
is the germ of a section over the base change of a stage neighbourhood, and that section
represents `c_p` for every `(p, x)` with `x` agreeing with `x₀` at some later stage. -/
theorem exists_stage_section_cylinder
    (c : etaleStalk B Y'.1 Y'.property y' ((B.smallPushforward f' _).obj
      ((B.smallInverseImage g' (Type (u + 1))).obj F)).obj)
    (p₀ : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
    (x₀ : y'.source ⟶ B.inclusion.obj XV)
    (hx₀ : x₀ ≫ B.inclusion.map ιX = p₀.1 ≫ B.inclusion.map g') :
    ∃ (i : P.indexᵒᵖ)
      (W : (geometricPointFiber B (P.diagram.obj i).1 (P.diagram.obj i).property
        ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩).Elements)
      (τ : F.obj.obj (op (cylinderObj B ιX P y' i x₀ W)))
      (j : P.indexᵒᵖ) (a : j ⟶ i),
      ∀ (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
        (x : y'.source ⟶ B.inclusion.obj XV)
        (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
        (hxj : x ≫ B.inclusion.map (P.proj.app j) = x₀ ≫ B.inclusion.map (P.proj.app j)),
        cylinderGerm B sq F ιX P y' i x₀ W τ p x hx (by
            rw [← P.proj_comp_map a, Functor.map_comp, ← Category.assoc, hxj,
              Category.assoc]) =
          pullbackStalkComponent B sq F y' c p := by
  let incl := B.inclusion
  obtain ⟨U0, τ0, hτ0⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit
    ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) (y'.map (B.inclusion.map g))
        (cartesianLiftEquiv B g' f' f g sq y' p₀)))).op ⋙ F.obj))
    (pullbackStalkComponent B sq F y' c p₀)
  let U := U0.unop
  have hz : (⟨y'.residueField, x₀⟩ : GeometricPoint (B.inclusion.obj XV)).map (incl.map ιX) =
      geometricPointLift (B.inclusion.map f) (y'.map (B.inclusion.map g))
        (cartesianLiftEquiv B g' f' f g sq y' p₀) :=
    congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint (B.inclusion.obj X))) hx₀
  let UV : (geometricPointFiber B XV.1 XV.property ⟨y'.residueField, x₀⟩).Elements :=
    Functor.elementsMk _ ((smallEtaleBaseChange B ιX).obj U.1) (baseChangeEtalePoint B ιX hz U.1 U.2)
  obtain ⟨i, W, φ, hφ⟩ := P.exists_stage_neighborhood ⟨y'.residueField, x₀⟩ UV
  let T := cylinderObj B ιX P y' i x₀ W
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
  let ψ : T ⟶ U.1 := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk m)
    (ObjectProperty.hom_ext _ hm))
  let τ := F.obj.map ψ.op τ0
  have hcylφ : (cylinderPoint B sq ιX P y' i x₀ W p₀ x₀ hx₀ rfl).1 ≫ TSV.map φ = UV.2.1 :=
    Eq.trans (by congr 1) hφ
  have hcylψ : (cylinderPoint B sq ιX P y' i x₀ W p₀ x₀ hx₀ rfl).1 ≫ TS.map ψ = U.2.1 := by
    show _ ≫ (TSV.map φ ≫ incl.map (pullback.fst U.1.obj.hom ιX)) = U.2.1
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hcylφ).trans ?_)
    refine (baseChangeEtalePointHom_fst B ιX hz U.1 U.2).trans ?_
    simp
  let pt := geometricPointLift (B.inclusion.map f) (y'.map (B.inclusion.map g))
    (cartesianLiftEquiv B g' f' f g sq y' p₀)
  let Tel : (geometricPointFiber B X.1 X.property pt).Elements :=
    Functor.elementsMk _ T (cylinderPoint B sq ιX P y' i x₀ W p₀ x₀ hx₀ rfl)
  let ψe : Tel ⟶ U := ⟨ψ, Subtype.ext hcylψ⟩
  have H₀ : cylinderGerm B sq F ιX P y' i x₀ W τ p₀ x₀ hx₀ rfl =
      pullbackStalkComponent B sq F y' c p₀ :=
    (ConcreteCategory.congr_hom (colimit.w ((CategoryOfElements.π (geometricPointFiber B X.1
      X.property pt)).op ⋙ F.obj) ψe.op) τ0).trans hτ0
  obtain ⟨j, a, hj⟩ := exists_stage_forall_cylinderGerm_eq B sq F ιX ι hV P y' i x₀ W c τ p₀ hx₀ H₀
  exact ⟨i, W, τ, j, a, hj⟩

/-- The germ of a stage section, read at a lift through the projection to the stage and then in
the stalk of `F` through the restriction along `X_V ⟶ X`, is the germ at the corresponding
`cylinderPoint`. -/
theorem smallEtaleRestrictionStalkMap_stageComponent
    (i : P.indexᵒᵖ) (x₀ : y'.source ⟶ B.inclusion.obj XV)
    (W : (geometricPointFiber B (P.diagram.obj i).1 (P.diagram.obj i).property
      ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩).Elements)
    (τ : F.obj.obj (op (cylinderObj B ιX P y' i x₀ W)))
    (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
    (x : y'.source ⟶ B.inclusion.obj XV) (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
    (hxi : x ≫ B.inclusion.map (P.proj.app i) = x₀ ≫ B.inclusion.map (P.proj.app i)) :
    smallEtaleRestrictionStalkMap B ιX x (p.1 ≫ B.inclusion.map g') hx F
        (pushforwardEtaleStalkComponent B (P.proj.app i) ⟨y'.residueField, x⟩
          ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩
          (congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _)) hxi)
          ((smallEtaleRestrictionAlong B ιX _).obj F)
          (colimit.ι ((CategoryOfElements.π (geometricPointFiber B (P.diagram.obj i).1
            (P.diagram.obj i).property ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩)).op ⋙
            ((B.smallPushforward (P.proj.app i) _).obj
              ((smallEtaleRestrictionAlong B ιX _).obj F)).obj)
            (op W) τ)) =
      cylinderGerm B sq F ιX P y' i x₀ W τ p x hx hxi := by
  have e₁ := pushforwardEtaleStalkComponent_germ_baseChange B (P.proj.app i)
    (x := ⟨y'.residueField, x⟩) (y := ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩)
    (congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _)) hxi) W.1 W.2
    ((smallEtaleRestrictionAlong B ιX (Type (u + 1))).obj F) τ
  refine (congrArg (smallEtaleRestrictionStalkMap B ιX x (p.1 ≫ B.inclusion.map g') hx F)
    e₁).trans ?_
  exact smallEtaleRestrictionStalkMap_germ B ιX x (p.1 ≫ B.inclusion.map g') hx F
    (Functor.elementsMk _ ((smallEtaleBaseChange B (P.proj.app i)).obj W.1)
      (baseChangeEtalePoint B (P.proj.app i)
        (x := ⟨y'.residueField, x⟩) (y := ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩)
        (congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _)) hxi) W.1 W.2)) τ

include hV P in
/-- **Realization of the family attached to an element of `f'_* (g')⁻¹ F`.** Given a presentation
of `X_V = X ×_Y V ⟶ V` by finite stages, for an étale `ι : V ⟶ Y` through which `g ∘ y'` factors,
every element `c` of the stalk of `f'_* (g')⁻¹ F` at `y'` comes, lift by lift, from one element of
the stalk of `f_* F` at `g ∘ y'`. -/
theorem exists_pushforwardEtaleStalk_eq_pullbackStalkComponent
    [Etale (B.inclusion.map ι)] [IsIntegralHom (B.inclusion.map f)]
    (sqV : IsPullback (B.inclusion.map ιX) (B.inclusion.map fV) (B.inclusion.map f)
      (B.inclusion.map ι))
    (yV : y'.source ⟶ B.inclusion.obj V) (hyV : yV ≫ B.inclusion.map ι = y'.hom ≫ B.inclusion.map g)
    (c : etaleStalk B Y'.1 Y'.property y' ((B.smallPushforward f' _).obj
      ((B.smallInverseImage g' (Type (u + 1))).obj F)).obj) :
    ∃ ζ : etaleStalk B Y.1 Y.property (y'.map (B.inclusion.map g))
        ((B.smallPushforward f (Type (u + 1))).obj F).obj,
      ∀ p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom},
        pushforwardEtaleStalkComponent B f (geometricPointLift (B.inclusion.map f)
            (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' p))
          (y'.map (B.inclusion.map g))
          (geometricPointLift_map (B.inclusion.map f) (y'.map (B.inclusion.map g))
            (cartesianLiftEquiv B g' f' f g sq y' p)) F ζ =
        pullbackStalkComponent B sq F y' c p := by
  classical
  let incl := B.inclusion
  have hfV : IsIntegralHom (incl.map fV) := MorphismProperty.of_isPullback sqV inferInstance
  let FV := (smallEtaleRestrictionAlong B ιX (Type (u + 1))).obj F
  let LV := {a : y'.source ⟶ incl.obj XV // a ≫ incl.map fV = yV}
  have hq (xV : LV) : (xV.1 ≫ incl.map ιX) ≫ incl.map f = y'.hom ≫ incl.map g := by
    rw [Category.assoc, ← Functor.map_comp, hV, Functor.map_comp, ← Category.assoc, xV.2, hyV]
  let pOf (xV : LV) : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom} :=
    (cartesianLiftEquiv B g' f' f g sq y').symm ⟨xV.1 ≫ incl.map ιX, hq xV⟩
  have hpOf (xV : LV) : xV.1 ≫ incl.map ιX = (pOf xV).1 ≫ incl.map g' :=
    (congrArg Subtype.val ((cartesianLiftEquiv B g' f' f g sq y').apply_symm_apply
      ⟨xV.1 ≫ incl.map ιX, hq xV⟩)).symm
  choose iOf WOf τOf jOf aOf hOf using fun xV : LV =>
    exists_stage_section_cylinder B sq F ιX ι hV P y' c (pOf xV) xV.1 (hpOf xV)
  let tY : P.diagram ⋙ incl ⟶ (Functor.const P.indexᵒᵖ).obj (incl.obj V) :=
    { app := fun k => incl.map (P.str.app k)
      naturality := fun k k' a => by
        show incl.map (P.diagram.map a) ≫ incl.map (P.str.app k') = incl.map (P.str.app k) ≫ 𝟙 _
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
  have key : ∀ z : {a : y'.source ⟶ incl.obj (P.diagram.obj (Opposite.op J)) //
      a ≫ incl.map sJ = yV},
      ∃ t : etaleStalk B (P.diagram.obj (Opposite.op J)).1 (P.diagram.obj (Opposite.op J)).property
          ⟨y'.residueField, z.1⟩ ((B.smallPushforward pJ (Type (u + 1))).obj FV).obj,
        ∀ (x : LV) (hx : x.1 ≫ incl.map pJ = z.1),
          smallEtaleRestrictionStalkMap B ιX x.1 ((pOf x).1 ≫ incl.map g') (hpOf x) F
            (pushforwardEtaleStalkComponent B pJ ⟨y'.residueField, x.1⟩ ⟨y'.residueField, z.1⟩
              (congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _)) hx) FV t) =
          pullbackStalkComponent B sq F y' c (pOf x) := by
    intro z
    by_cases hz : ∃ x : LV, x.1 ≫ incl.map pJ = z.1
    · obtain ⟨xt, hxt⟩ := hz
      obtain ⟨xS, hxS, hcov⟩ := hS xt
      have hcov' : xt.1 ≫ incl.map (P.proj.app (jOf xS)) = xS.1 ≫ incl.map (P.proj.app (jOf xS)) :=
        hcov
      let i := iOf xS
      let a1 : Opposite.op J ⟶ i := aJ xS hxS ≫ aOf xS
      have hproj {k k' : P.indexᵒᵖ} (a : k ⟶ k') (x : y'.source ⟶ incl.obj XV) :
          x ≫ incl.map (P.proj.app k') =
            (x ≫ incl.map (P.proj.app k)) ≫ incl.map (P.diagram.map a) := by
        rw [Category.assoc, ← Functor.map_comp, P.proj_comp_map]
      have hk : P.proj.app i = pJ ≫ P.diagram.map a1 := (P.proj_comp_map a1).symm
      have hzi : z.1 ≫ incl.map (P.diagram.map a1) = xS.1 ≫ incl.map (P.proj.app i) := by
        calc z.1 ≫ incl.map (P.diagram.map a1)
            = (xt.1 ≫ incl.map pJ) ≫ incl.map (P.diagram.map a1) := by rw [hxt]
          _ = xt.1 ≫ incl.map (P.proj.app i) := (hproj a1 xt.1).symm
          _ = (xt.1 ≫ incl.map (P.proj.app (jOf xS))) ≫ incl.map (P.diagram.map (aOf xS)) :=
              hproj _ _
          _ = (xS.1 ≫ incl.map (P.proj.app (jOf xS))) ≫ incl.map (P.diagram.map (aOf xS)) := by
              rw [hcov']
          _ = xS.1 ≫ incl.map (P.proj.app i) := (hproj _ _).symm
      let zp : GeometricPoint (incl.obj (P.diagram.obj (Opposite.op J))) := ⟨y'.residueField, z.1⟩
      let sp : GeometricPoint (incl.obj (P.diagram.obj i)) :=
        ⟨y'.residueField, xS.1 ≫ incl.map (P.proj.app i)⟩
      let e0 := colimit.ι ((CategoryOfElements.π (geometricPointFiber B (P.diagram.obj i).1
          (P.diagram.obj i).property sp)).op ⋙
        ((B.smallPushforward (P.proj.app i) (Type (u + 1))).obj FV).obj)
          (op (WOf xS)) (τOf xS)
      let m2 := (etaleStalkFunctor.{u, u + 1} B (P.diagram.obj i).1
        (P.diagram.obj i).property sp).map ((eqToIso (congrArg
          (fun m => B.smallPushforward m (Type (u + 1))) hk)).hom.app FV) e0
      let m1 := (etaleStalkFunctor.{u, u + 1} B (P.diagram.obj i).1
        (P.diagram.obj i).property sp).map ((smallEtaleSheafPushforwardCompIso B XV
          (P.diagram.obj (Opposite.op J)) (P.diagram.obj i) pJ (P.diagram.map a1)
          (Type (u + 1))).inv.app FV) m2
      have hl : zp.map (incl.map (P.diagram.map a1)) = sp :=
        congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _)) hzi
      refine ⟨pushforwardEtaleStalkComponent B (P.diagram.map a1) zp sp hl
        ((B.smallPushforward pJ (Type (u + 1))).obj FV) m1, fun x hx => ?_⟩
      let xp : GeometricPoint (incl.obj XV) := ⟨y'.residueField, x.1⟩
      have hxi : x.1 ≫ incl.map (P.proj.app i) = xS.1 ≫ incl.map (P.proj.app i) := by
        rw [hproj a1 x.1, hx, hzi]
      have hm : xp.map (incl.map (pJ ≫ P.diagram.map a1)) = sp :=
        congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _))
          ((congrArg (x.1 ≫ ·) (congrArg incl.map hk)).symm.trans hxi)
      have hc : xp.map (incl.map (P.proj.app i)) = sp :=
        congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _)) hxi
      have e₁ := (pushforwardEtaleStalkComponent_comp B pJ (P.diagram.map a1) (w := xp) (t := zp)
        (s := sp) (congrArg (fun m => (⟨y'.residueField, m⟩ : GeometricPoint _)) hx) hl hm FV
        m2).symm
      have e₂ := pushforwardEtaleStalkComponent_eqToHom B (P.proj.app i) (pJ ≫ P.diagram.map a1)
        hk xp sp hc hm FV e0
      have e₃ := smallEtaleRestrictionStalkMap_stageComponent B sq F ιX P y' i xS.1 (WOf xS)
        (τOf xS) (pOf x) x.1 (hpOf x) hxi
      have hxj : x.1 ≫ incl.map (P.proj.app (jOf xS)) = xS.1 ≫ incl.map (P.proj.app (jOf xS)) := by
        rw [hproj (aJ xS hxS) x.1, hx, ← hxt, ← hproj, hcov']
      have e₄ := hOf xS (pOf x) x.1 (hpOf x) hxj
      exact (congrArg (smallEtaleRestrictionStalkMap B ιX x.1 ((pOf x).1 ≫ incl.map g') (hpOf x) F)
        (e₁.trans e₂)).trans (e₃.trans e₄)
    · have hE : IsEmpty {a : (⟨y'.residueField, z.1⟩ :
          GeometricPoint (incl.obj (P.diagram.obj (Opposite.op J)))).source ⟶ XV.1 //
          a ≫ incl.map pJ = (⟨y'.residueField, z.1⟩ :
            GeometricPoint (incl.obj (P.diagram.obj (Opposite.op J)))).hom} :=
        ⟨fun a => hz ⟨⟨a.1, by rw [← hfac, ← Category.assoc, a.2]; exact z.2⟩, a.2⟩⟩
      obtain ⟨t⟩ := nonempty_etaleStalk_pushforward_of_isEmpty_lifts B pJ
        ⟨y'.residueField, z.1⟩ hE FV
      exact ⟨t, fun x hx => (hz ⟨x, hx⟩).elim⟩
  choose t ht using key
  let yVp : GeometricPoint (incl.obj V) := ⟨y'.residueField, yV⟩
  obtain ⟨W, s, hs⟩ := exists_section_of_finite_stage B pJ sJ yVp FV t
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
    (sqV.lift_snd _ _ _).symm.trans ((congrArg (ξ ≫ ·) (hfac _)).symm.trans
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
        incl.map (pullback.snd ((smallEtaleBaseChange B sJ).obj W.1).obj.hom
        pJ) ≫ incl.map ιX := B.inclusion.map_comp _ _
    exact (congrArg (κs ≫ ·) e).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ incl.map ιX) (hL.lift_snd _ _ _)).trans (sqV.lift_fst _ _ _)))
  let κ : (smallEtaleBaseChange B f).obj NY.1 ⟶ LT :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk κs) (ObjectProperty.hom_ext _ hκ))
  refine ⟨colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y.1 Y.property
    (y'.map (B.inclusion.map g)))).op ⋙ ((B.smallPushforward f (Type (u + 1))).obj F).obj)
    (op NY) (F.obj.map κ.op s), fun p => ?_⟩
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
  let lifted := liftedEtaleNeighborhood B sJ yVp zx W
  let pt := baseChangeEtalePoint B pJ (x := ⟨y'.residueField, xV.1⟩)
    (y := ⟨y'.residueField, xV.1 ≫ incl.map pJ⟩) rfl ((smallEtaleBaseChange B sJ).obj W.1) lifted.2
  let bcpY := baseChangeEtalePoint B f (geometricPointLift_map (B.inclusion.map f)
    (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' (pOf xV))) NY.1 NY.2
  have hbfst : bcpY.1 ≫ incl.map (pullback.fst NY.1.obj.hom f) = W.2.1 := by
    refine (baseChangeEtalePointHom_fst B f (geometricPointLift_map (B.inclusion.map f)
      (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' (pOf xV))) NY.1
      NY.2).trans ?_
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  have hbsnd : bcpY.1 ≫ incl.map (pullback.snd NY.1.obj.hom f) = (pOf xV).1 ≫ incl.map g' :=
    baseChangeEtalePointHom_snd B f (geometricPointLift_map (B.inclusion.map f)
      (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' (pOf xV))) NY.1 NY.2
  have hW2 : W.2.1 ≫ incl.map W.1.obj.hom = yV := W.2.2
  have hbξ : bcpY.1 ≫ ξ = xV.1 := comp_lift_eq_of_comp_eq sqV _ (hbsnd.trans (hpOf xV).symm)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ incl.map W.1.obj.hom) hbfst).trans
      (hW2.trans xV.2.symm)))
  have hl1 : lifted.2.1 ≫ incl.map (pullback.fst W.1.obj.hom sJ) = W.2.1 :=
    liftedEtaleNeighborhood_point_fst B sJ yVp zx W
  have hl2 : lifted.2.1 ≫ incl.map (pullback.snd W.1.obj.hom sJ) = xV.1 ≫ incl.map pJ :=
    lifted.2.2
  have hbmid : bcpY.1 ≫ mid = lifted.2.1 := comp_lift_eq_of_comp_eq hM _ (hbfst.trans hl1.symm)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ incl.map pJ) hbξ).trans hl2.symm))
  have hpt : bcpY.1 ≫ κs = pt.1 := by
    refine comp_lift_eq_of_comp_eq hL _ (hbmid.trans ?_)
      (hbξ.trans (baseChangeEtalePointHom_snd B pJ (x := ⟨y'.residueField, xV.1⟩)
        (y := ⟨y'.residueField, xV.1 ≫ incl.map pJ⟩) rfl _ lifted.2).symm)
    refine Eq.trans ?_ (baseChangeEtalePointHom_fst B pJ (x := ⟨y'.residueField, xV.1⟩)
      (y := ⟨y'.residueField, xV.1 ≫ incl.map pJ⟩) rfl _ lifted.2).symm
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  let qpt := geometricPointLift (B.inclusion.map f) (y'.map (B.inclusion.map g))
    (cartesianLiftEquiv B g' f' f g sq y' (pOf xV))
  let DF := (CategoryOfElements.π (geometricPointFiber B X.1 X.property qpt)).op ⋙ F.obj
  have hκpt : (bcpY.1 ≫ κs) ≫ incl.map LT.obj.hom = qpt.hom :=
    (Category.assoc _ _ _).trans ((congrArg (bcpY.1 ≫ ·) hκ).trans bcpY.2)
  let BCel : (geometricPointFiber B X.1 X.property qpt).Elements :=
    Functor.elementsMk _ ((smallEtaleBaseChange B f).obj NY.1) bcpY
  let LTel : (geometricPointFiber B X.1 X.property qpt).Elements :=
    Functor.elementsMk _ LT ⟨bcpY.1 ≫ κs, hκpt⟩
  let κe : BCel ⟶ LTel := ⟨κ, Subtype.ext rfl⟩
  have step₁ := pushforwardEtaleStalkComponent_germ_baseChange B f
    (geometricPointLift_map (B.inclusion.map f) (y'.map (B.inclusion.map g))
      (cartesianLiftEquiv B g' f' f g sq y' (pOf xV))) NY.1 NY.2 F (F.obj.map κ.op s)
  have step₂ := (ConcreteCategory.congr_hom (colimit.w DF κe.op) s)
  have step₃ := smallEtaleRestrictionStalkMap_germ B ιX xV.1 ((pOf xV).1 ≫ incl.map g') (hpOf xV) F
    (Functor.elementsMk _ ((smallEtaleBaseChange B pJ).obj ((smallEtaleBaseChange B sJ).obj W.1)) pt) s
  let Eel := (smallEtaleRestrictionNeighborhoods B ιX xV.1 ((pOf xV).1 ≫ incl.map g')
      (hpOf xV)).obj (Functor.elementsMk _ ((smallEtaleBaseChange B pJ).obj ((smallEtaleBaseChange B sJ).obj W.1)) pt)
  have hid : (SmallEtale.toScheme B X.1 X.property).map (𝟙 LT) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  let idE : LTel ⟶ Eel := ⟨𝟙 LT, Subtype.ext ((congrArg (_ ≫ ·) hid).trans
    ((Category.comp_id _).trans hpt))⟩
  have step₄ := ConcreteCategory.congr_hom (colimit.w DF idE.op) s
  have hmapid : DF.map idE.op s = s := by
    show F.obj.map (𝟙 LT).op s = s
    rw [op_id, F.obj.map_id]; rfl
  have step₄' : colimit.ι DF (op LTel) s = colimit.ι DF (op Eel) s :=
    (congrArg (colimit.ι DF (op LTel)) hmapid).symm.trans step₄
  refine step₁.trans (step₂.trans (step₄'.trans (step₃.symm.trans ?_)))
  exact (congrArg (smallEtaleRestrictionStalkMap B ιX xV.1 ((pOf xV).1 ≫ incl.map g') (hpOf xV) F)
    (hs xV')).trans (ht zx xV rfl)

end Realization

section BaseChange

variable {X' X Y' Y : B.Scheme} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **The base change map of a direct image along an integral morphism is an isomorphism**, at
set coefficients on the size-bounded small étale sites: this is the statement of
[Stacks, Tag 0EYP] for sheaves of sets. Consider a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of schemes of a big étale site with `f` integral, and a sheaf of sets `F` on the small étale site
of `X`, with values in `Type (u + 1)`. Then the canonical comparison
`g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. -/
@[sga "4 VIII 5.5" "more general", sga "4 VIII 5.6"]
theorem isIso_smallEtaleBaseChangeNatTrans_app_of_isIntegralHom
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsIntegralHom (B.inclusion.map f)] (h : g' ≫ f = f' ≫ g)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    IsIso ((smallEtaleBaseChangeNatTrans B g' f' f g h).app F) := by
  classical
  let incl := B.inclusion
  let G := (B.smallInverseImage g' (Type (u + 1))).obj F
  have hf' : IsIntegralHom (incl.map f') := MorphismProperty.of_isPullback sq inferInstance
  refine isIso_of_bijective_etaleStalkMap B Y'.1 Y'.property _ fun y' => ?_
  let ig := (smallEtalePullbackStalkIso B g y').app ((B.smallPushforward f _).obj F)
  have hcompat := pushforwardEtaleStalkComponent_smallEtaleBaseChangeNatTrans B g' f' f g sq h F y'
  have hI' := finitePushforwardStalkComponent_injective_of_isIntegralHom B f' y' G
  have hI := finitePushforwardStalkComponent_injective_of_isIntegralHom B f (y'.map (incl.map g)) F
  refine ⟨fun a b hab => ?_, fun c => ?_⟩
  · obtain ⟨ζa, rfl⟩ := ig.toEquiv.symm.surjective a
    obtain ⟨ζb, rfl⟩ := ig.toEquiv.symm.surjective b
    refine congrArg ig.toEquiv.symm (hI (funext fun q => ?_))
    obtain ⟨p, rfl⟩ := (cartesianLiftEquiv B g' f' f g sq y').surjective q
    have hab' := congrArg (fun z => pushforwardEtaleStalkComponent B f'
      (geometricPointLift (B.inclusion.map f') y' p) y'
      (geometricPointLift_map (B.inclusion.map f') y' p) G z) hab
    exact ((smallEtalePullbackStalkIso B g' (geometricPointLift (B.inclusion.map f') y' p)).app
      F).symm.toEquiv.injective ((hcompat p ζa).symm.trans (hab'.trans (hcompat p ζb)))
  · obtain ⟨_, ⟨V0, hV0, rfl⟩, hyV0, -⟩ :=
      (incl.obj Y).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ ((y'.hom ≫ incl.map g) default)) isOpen_univ
    let V1 : (incl.obj Y).Opens := V0
    have hV1 : IsAffineOpen V1 := hV0
    have hVsize : B.Contains V1 := (Scheme.size_coe_opens_le _ V1).trans_lt Y.property
    let VB : B.Scheme := B.obj V1 hVsize
    let ι : VB ⟶ Y := ObjectProperty.homMk V1.ι
    have : IsOpenImmersion (incl.map ι) := inferInstanceAs (IsOpenImmersion V1.ι)
    have : Etale (incl.map ι) := inferInstance
    have : IsAffine (incl.obj VB) := hV1
    have hrange : Set.range (y'.hom ≫ incl.map g) ⊆ Set.range V1.ι := by
      rintro _ ⟨a, rfl⟩
      refine ⟨⟨(y'.hom ≫ incl.map g) a, ?_⟩, rfl⟩
      rw [Subsingleton.elim a default]
      exact hyV0
    let yV : y'.source ⟶ incl.obj VB := IsOpenImmersion.lift V1.ι (y'.hom ≫ incl.map g) hrange
    have hyV : yV ≫ incl.map ι = y'.hom ≫ incl.map g := IsOpenImmersion.lift_fac _ _ _
    have := hasPullbacks_bigEtaleSite B
    have := preservesPullbacks_bigEtaleSiteInclusion B
    let ιX := pullback.fst f ι
    let fV := pullback.snd f ι
    have hV : ιX ≫ f = fV ≫ ι := pullback.condition
    have sqV : IsPullback (incl.map ιX) (incl.map fV) (incl.map f) (incl.map ι) :=
      (IsPullback.of_hasPullback f ι).map B.inclusion
    have : IsOpenImmersion (incl.map ιX) :=
      MorphismProperty.of_isPullback sqV.flip (inferInstanceAs (IsOpenImmersion V1.ι))
    have : Etale (incl.map ιX) := inferInstance
    have : IsIntegralHom (incl.map fV) := MorphismProperty.of_isPullback sqV inferInstance
    let P := SmallEtaleIntegralStages.ofIsAffine fV
    obtain ⟨ζ, hζ⟩ := exists_pushforwardEtaleStalk_eq_pullbackStalkComponent B sq F ιX ι hV P y'
      sqV yV hyV c
    refine ⟨ig.toEquiv.symm ζ, hI' (funext fun p => ?_)⟩
    refine (hcompat p ζ).trans ?_
    show ((smallEtalePullbackStalkIso B g' (geometricPointLift (B.inclusion.map f') y' p)).app
      F).toEquiv.symm _ = _
    rw [hζ p]
    exact ((smallEtalePullbackStalkIso B g' (geometricPointLift (B.inclusion.map f') y' p)).app
      F).toEquiv.symm_apply_apply _

end BaseChange

end AlgebraicGeometry

end
