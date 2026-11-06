module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardStages
public import StacksFrontier.AlgebraicGeometry.Limits.StageBaseChangeOpens
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# Germs of the base change of an integral direct image are constant along cylinders

Consider a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of a big étale site, a sheaf of sets `F` on the small étale site of `X`, and its inverse image
`G = (g')⁻¹ F`. Fix a geometric point `y'` of `Y'` and an element `c` of the stalk of `f'_* G`
at `y'`. Each lift `p` of `y'` through `f'` gives an element `c_p` of the stalk of `F` at the
corresponding lift `p ∘ g'` of `g ∘ y'`: the image of `c` in the stalk of `G` at `p`, read in the
stalk of `F` through Tag 03Q1.

Let `ιX : X_V ⟶ X` be étale, and let `X_V` be presented as the limit of a system of stages
`X_i`. If `c_{p₀}` is the germ of a section `τ` of `F` over the base change to `X_V` of an étale
neighbourhood `W` at a stage `i`, then the same section represents `c_p` for every lift `p`
which agrees with `p₀` at some later stage `j`. This is the continuity of the family `(c_p)` that
the realization of such families by germs of `f_* F` rests on.

## Main results

* `AlgebraicGeometry.exists_lift_of_etale_of_isAlgClosed` — a geometric point of the target of an
  étale morphism, lying under a point of the source, lifts to the source.
* `AlgebraicGeometry.exists_stage_forall_germ_eq_pullbackStalk` — the continuity statement.

## Implementation notes

The section `τ` and the section representing `c` are compared over a common étale neighbourhood
`N` of the point `p₀` of `X'`. The locus where they agree contains the image of `N` in the fibre
product of the two neighbourhoods over `X'`, an open subset. That fibre product receives a
morphism from `X_V ×_{X_i} (W ×_Y V')`, the base change of the limit `X_V` along a morphism into
the stage `X_i`, carrying the canonical point attached to a lift `p` to the point at which the two
germs at `p` are compared; so membership of that point in the open locus is decided at a finite
stage by `AlgebraicGeometry.exists_stage_forall_lift_mem_of_isLimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **Geometric points lift along étale morphisms.** Let `e : N ⟶ M` be étale and let `z` be a
geometric point of `M` with algebraically closed residue field, lying under a point `n` of `N`.
Then `z` lifts through `e`. The fibre of `e` over `z` is étale over an algebraically closed field,
hence locally of finite type with closed points, and a closed point of a scheme locally of finite
type over an algebraically closed field is rational. -/
theorem exists_lift_of_etale_of_isAlgClosed {N M : Scheme.{u}} (e : N ⟶ M) [Etale e]
    {K : Type u} [Field K] [IsAlgClosed K] (z : Spec (.of K) ⟶ M) (n : N)
    (hn : e n = z default) : ∃ m : Spec (.of K) ⟶ N, m ≫ e = z := by
  obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := e) (g := z) n default hn
  let : IsLocallyArtinian (pullback e z) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd e z)
  let pt := pointOfClosedPoint (pullback.snd e z) w isClosed_singleton
  refine ⟨pt ≫ pullback.fst e z, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    pointOfClosedPoint_comp, Category.id_comp]

/-- Composition with an étale object `U` of the small étale site of `X` composes structure
morphisms. -/
theorem smallEtalePostcompose_obj_obj_hom (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) (U : SmallEtale B X hX)
    (A : SmallEtale B U.obj.left.1 U.obj.left.property) :
    ((smallEtalePostcompose B X hX U).obj A).obj.hom = A.obj.hom ≫ U.obj.hom := rfl

/-- A morphism into the apex of a pullback is determined by its two components, even when the
other side is given as a composite with a `lift`. -/
private theorem comp_lift_eq_of_comp_eq {C : Type*} [Category C] {P X Y Z T R : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (r : T ⟶ R) {a : R ⟶ X} {b : R ⟶ Y} (w : a ≫ f = b ≫ g) {c : T ⟶ P}
    (h₁ : r ≫ a = c ≫ fst) (h₂ : r ≫ b = c ≫ snd) : r ≫ h.lift a b w = c :=
  h.hom_ext (by rw [Category.assoc, h.lift_fst, h₁]) (by rw [Category.assoc, h.lift_snd, h₂])

/-- `comp_lift_eq_of_comp_eq` for the chosen pullback `pullback.lift`. -/
private theorem comp_pullback_lift_eq_of_comp_eq {C : Type*} [Category C] {X Y Z T R : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (r : T ⟶ R) {a : R ⟶ X} {b : R ⟶ Y}
    (w : a ≫ f = b ≫ g) {c : T ⟶ pullback f g} (h₁ : r ≫ a = c ≫ pullback.fst f g)
    (h₂ : r ≫ b = c ≫ pullback.snd f g) : r ≫ pullback.lift a b w = c :=
  pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, h₁])
    (by rw [Category.assoc, pullback.lift_snd, h₂])

variable (B : BigEtaleSite.{u})

section Cylinder

variable {X' X Y' Y : B.Scheme} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
    (B.inclusion.map g))
  (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
  {V XV : B.Scheme} (ιX : XV ⟶ X) [Etale (B.inclusion.map ιX)] {fV : XV ⟶ V} (ι : V ⟶ Y)
  (hV : ιX ≫ f = fV ≫ ι) (P : SmallEtaleIntegralStages B fV)
  (y' : GeometricPoint Y'.1) (i : P.indexᵒᵖ) (x₀ : y'.source ⟶ B.inclusion.obj XV)
  (W : (geometricPointFiber B (P.diagram.obj i).1 (P.diagram.obj i).property
    ⟨y'.residueField, x₀ ≫ B.inclusion.map (P.proj.app i)⟩).Elements)

/-- The étale neighbourhood of `X` obtained from a stage neighbourhood `W`: the base change of
`W` to `X_V`, regarded over `X`. -/
abbrev cylinderObj : SmallEtale B X.1 X.property :=
  (smallEtalePostcompose B X.1 X.property (SmallEtale.ofEtaleHom B ιX)).obj
    ((smallEtaleBaseChange B (P.proj.app i)).obj W.1)

/-- The point of `cylinderObj` attached to a lift `p` of `y'` through `f'` and a lift `x` of
`p ∘ g'` to `X_V` agreeing with `x₀` at the stage of `W`. -/
def cylinderPoint (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
    (x : y'.source ⟶ B.inclusion.obj XV) (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
    (hxi : x ≫ B.inclusion.map (P.proj.app i) = x₀ ≫ B.inclusion.map (P.proj.app i)) :
    (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) (y'.map (B.inclusion.map g))
        (cartesianLiftEquiv B g' f' f g sq y' p))).obj (cylinderObj B ιX P y' i x₀ W) :=
  ⟨(isPullback_smallEtaleBaseChange_inclusion B (P.proj.app i) W.1).lift W.2.1 x
      (W.2.2.trans hxi.symm), by
    have e₁ := (isPullback_smallEtaleBaseChange_inclusion B (P.proj.app i) W.1).lift_snd W.2.1 x
      (W.2.2.trans hxi.symm)
    have e₂ : B.inclusion.map (pullback.snd W.1.obj.hom (P.proj.app i) ≫ ιX) =
        B.inclusion.map (pullback.snd W.1.obj.hom (P.proj.app i)) ≫ B.inclusion.map ιX :=
      B.inclusion.map_comp _ _
    exact (congrArg (fun m => _ ≫ m) e₂).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ B.inclusion.map ιX) e₁).trans hx))⟩

/-- The germ at `cylinderPoint` of a section of `F` over `cylinderObj`. -/
abbrev cylinderGerm (τ : F.obj.obj (op (cylinderObj B ιX P y' i x₀ W)))
    (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
    (x : y'.source ⟶ B.inclusion.obj XV) (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
    (hxi : x ≫ B.inclusion.map (P.proj.app i) = x₀ ≫ B.inclusion.map (P.proj.app i)) :
    etaleStalk B X.1 X.property (geometricPointLift (B.inclusion.map f)
      (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' p)) F.obj :=
  colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property
      (geometricPointLift (B.inclusion.map f) (y'.map (B.inclusion.map g))
        (cartesianLiftEquiv B g' f' f g sq y' p)))).op ⋙ F.obj)
    (op (Functor.elementsMk _ (cylinderObj B ιX P y' i x₀ W) (cylinderPoint B sq ιX P y' i x₀ W p x hx hxi))) τ

/-- The element `c_p` of the stalk of `F` at the lift `p ∘ g'` attached to an element `c` of the
stalk of `f'_* (g')⁻¹ F` at `y'` and a lift `p` of `y'` through `f'`. -/
abbrev pullbackStalkComponent
    (c : etaleStalk B Y'.1 Y'.property y' ((B.smallPushforward f' _).obj
      ((B.smallInverseImage g' (Type (u + 1))).obj F)).obj)
    (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom}) :
    etaleStalk B X.1 X.property (geometricPointLift (B.inclusion.map f)
      (y'.map (B.inclusion.map g)) (cartesianLiftEquiv B g' f' f g sq y' p)) F.obj :=
  (smallEtalePullbackStalkIso B g' (geometricPointLift (B.inclusion.map f') y' p)).hom.app F
    (pushforwardEtaleStalkComponent B f' (geometricPointLift (B.inclusion.map f') y' p) y'
      (geometricPointLift_map (B.inclusion.map f') y' p) _ c)

include hV in
/-- **The germs of a stage section are constant on a cylinder.** If the germ of a section `τ`
of `F` over `cylinderObj` represents `c_{p₀}` at the point attached to `(p₀, x₀)`, there is a
later stage `j` such that it represents `c_p` at the point attached to `(p, x)` for every `x`
agreeing with `x₀` at `j`. -/
theorem exists_stage_forall_cylinderGerm_eq
    (c : etaleStalk B Y'.1 Y'.property y' ((B.smallPushforward f' _).obj
      ((B.smallInverseImage g' (Type (u + 1))).obj F)).obj)
    (τ : F.obj.obj (op (cylinderObj B ιX P y' i x₀ W)))
    (p₀ : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
    (hx₀ : x₀ ≫ B.inclusion.map ιX = p₀.1 ≫ B.inclusion.map g')
    (H₀ : cylinderGerm B sq F ιX P y' i x₀ W τ p₀ x₀ hx₀ rfl =
      pullbackStalkComponent B sq F y' c p₀) :
    ∃ (j : P.indexᵒᵖ) (a : j ⟶ i),
      ∀ (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
        (x : y'.source ⟶ B.inclusion.obj XV)
        (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
        (hxj : x ≫ B.inclusion.map (P.proj.app j) = x₀ ≫ B.inclusion.map (P.proj.app j)),
        cylinderGerm B sq F ιX P y' i x₀ W τ p x hx (by
            rw [← P.proj_comp_map a, Functor.map_comp, ← Category.assoc, hxj,
              Category.assoc]) =
          pullbackStalkComponent B sq F y' c p := by
  classical
  let incl := B.inclusion
  let G := (B.smallInverseImage g' (Type (u + 1))).obj F
  let T := cylinderObj B ιX P y' i x₀ W
  -- the representative of `c`
  obtain ⟨V'o, σ, hσ⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit
    ((CategoryOfElements.π (geometricPointFiber B Y'.1 Y'.property y')).op ⋙
      ((B.smallPushforward f' _).obj G).obj)) c
  subst hσ
  let V' := V'o.unop
  -- the germ of the representative at a lift
  let D (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom}) :=
    (CategoryOfElements.π (geometricPointFiber B X'.1 X'.property
      (geometricPointLift (B.inclusion.map f') y' p))).op ⋙ G.obj
  let bP (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom}) :
      (geometricPointFiber B X'.1 X'.property (geometricPointLift (B.inclusion.map f') y' p)).obj
        ((smallEtaleBaseChange B f').obj V'.1) :=
    baseChangeEtalePoint B f' (geometricPointLift_map (B.inclusion.map f') y' p) V'.1 V'.2
  have hcomp (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom}) :
      pushforwardEtaleStalkComponent B f' (geometricPointLift (B.inclusion.map f') y' p) y'
        (geometricPointLift_map (B.inclusion.map f') y' p) G
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y'.1 Y'.property y')).op ⋙
          ((B.smallPushforward f' _).obj G).obj) V'o σ) =
      colimit.ι (D p) (op (Functor.elementsMk _ ((smallEtaleBaseChange B f').obj V'.1) (bP p))) σ :=
    pushforwardEtaleStalkComponent_germ_baseChange B f'
      (geometricPointLift_map (B.inclusion.map f') y' p) V'.1 V'.2 G σ
  -- the base change of the stage neighbourhood to `X'`
  let Q := (smallEtaleBaseChange B g').obj T
  have hQ : IsPullback (incl.map (pullback.fst T.obj.hom g')) (incl.map (pullback.snd T.obj.hom g'))
      (incl.map T.obj.hom) (incl.map g') := isPullback_smallEtaleBaseChange_inclusion B g' T
  let qP (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
      (x : y'.source ⟶ B.inclusion.obj XV) (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
      (hxi : x ≫ B.inclusion.map (P.proj.app i) = x₀ ≫ B.inclusion.map (P.proj.app i)) :
      (geometricPointFiber B X'.1 X'.property (geometricPointLift (B.inclusion.map f') y' p)).obj
        Q :=
    ⟨hQ.lift (cylinderPoint B sq ιX P y' i x₀ W p x hx hxi).1 p.1
      (cylinderPoint B sq ιX P y' i x₀ W p x hx hxi).2, hQ.lift_snd _ _ _⟩
  let τ' := pullbackSectionAlong B g' F T Q (𝟙 Q) τ
  have hiso (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
      (x : y'.source ⟶ B.inclusion.obj XV) (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
      (hxi : x ≫ B.inclusion.map (P.proj.app i) = x₀ ≫ B.inclusion.map (P.proj.app i)) :
      (smallEtalePullbackStalkIso B g' (geometricPointLift (B.inclusion.map f') y' p)).hom.app F
        (colimit.ι (D p) (op (Functor.elementsMk _ Q (qP p x hx hxi))) τ') =
      cylinderGerm B sq F ιX P y' i x₀ W τ p x hx hxi := by
    refine smallEtalePullbackStalkIso_germ B g' (geometricPointLift (B.inclusion.map f') y' p) F
      (Functor.elementsMk _ Q (qP p x hx hxi))
      (Functor.elementsMk _ T (cylinderPoint B sq ιX P y' i x₀ W p x hx hxi)) (𝟙 Q) ?_ τ
    have h0 : (SmallEtale.toScheme B X'.1 X'.property).map (𝟙 Q) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    exact (congrArg (fun m => (qP p x hx hxi).1 ≫ m ≫ incl.map (pullback.fst T.obj.hom g'))
      h0).trans
      ((congrArg ((qP p x hx hxi).1 ≫ ·) (Category.id_comp _)).trans (hQ.lift_fst _ _ _))
  -- it suffices to compare the two germs in the stalk of `G`
  have hred (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
      (x : y'.source ⟶ B.inclusion.obj XV) (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
      (hxi : x ≫ B.inclusion.map (P.proj.app i) = x₀ ≫ B.inclusion.map (P.proj.app i)) :
      cylinderGerm B sq F ιX P y' i x₀ W τ p x hx hxi =
          pullbackStalkComponent B sq F y'
            (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y'.1 Y'.property y')).op ⋙
              ((B.smallPushforward f' _).obj G).obj) V'o σ) p ↔
        colimit.ι (D p) (op (Functor.elementsMk _ Q (qP p x hx hxi))) τ' =
          colimit.ι (D p) (op (Functor.elementsMk _ ((smallEtaleBaseChange B f').obj V'.1) (bP p))) σ := by
    rw [← hiso p x hx hxi]
    show _ =
      (smallEtalePullbackStalkIso B g' (geometricPointLift (B.inclusion.map f') y' p)).hom.app F
      (pushforwardEtaleStalkComponent B f' (geometricPointLift (B.inclusion.map f') y' p) y'
        (geometricPointLift_map (B.inclusion.map f') y' p) G
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B Y'.1 Y'.property y')).op ⋙
          ((B.smallPushforward f' _).obj G).obj) V'o σ)) ↔ _
    rw [hcomp p]
    exact ((smallEtalePullbackStalkIso B g' (geometricPointLift (B.inclusion.map f') y' p)).app
      F).toEquiv.injective.eq_iff
  -- the germs agree on a neighbourhood of the point attached to `p₀`
  have H₀' := (hred p₀ x₀ hx₀ rfl).mp H₀
  obtain ⟨k, fa, fb, hfab⟩ := (Types.FilteredColimit.isColimit_eq_iff _
    (colimit.isColimit (D p₀))).mp H₀'
  let N := k.unop
  let aN : N ⟶ Functor.elementsMk _ Q (qP p₀ x₀ hx₀ rfl) := fa.unop
  let bN : N ⟶ Functor.elementsMk _ ((smallEtaleBaseChange B f').obj V'.1) (bP p₀) := fb.unop
  have hab : G.obj.map aN.1.op τ' = G.obj.map bN.1.op σ := hfab
  let TS := SmallEtale.toScheme B X'.1 X'.property
  let α := TS.map aN.1
  let β := TS.map bN.1
  have hα : α ≫ incl.map Q.obj.hom = incl.map N.1.obj.hom := SmallEtale.toScheme_map_comp B _ _ aN.1
  have hβ : β ≫ incl.map ((smallEtaleBaseChange B f').obj V'.1).obj.hom = incl.map N.1.obj.hom :=
    SmallEtale.toScheme_map_comp B _ _ bN.1
  let M := pullback (incl.map Q.obj.hom) (incl.map ((smallEtaleBaseChange B f').obj V'.1).obj.hom)
  let γ : TS.obj N.1 ⟶ M := pullback.lift α β (hα.trans hβ.symm)
  have : Etale α := SmallEtale.etale_toScheme_map aN.1
  have : Etale (incl.map ((smallEtaleBaseChange B f').obj V'.1).obj.hom) :=
    ((smallEtaleBaseChange B f').obj V'.1).property
  have hfstM : Etale (pullback.fst (incl.map Q.obj.hom)
      (incl.map ((smallEtaleBaseChange B f').obj V'.1).obj.hom)) := inferInstance
  have : Etale γ := MorphismProperty.of_postcomp (W' := @Etale) @Etale γ
    (pullback.fst (incl.map Q.obj.hom) (incl.map ((smallEtaleBaseChange B f').obj V'.1).obj.hom))
    hfstM (by rw [pullback.lift_fst]; infer_instance)
  let O : M.Opens := ⟨Set.range γ, γ.isOpenMap.isOpen_range⟩
  -- the base change of the limit along the stage neighbourhood
  let Ni := pullback (incl.map W.1.obj.hom ≫ incl.map (P.str.app i) ≫ incl.map ι)
    (incl.map V'.1.obj.hom ≫ incl.map g)
  let ν : Ni ⟶ incl.obj (P.diagram.obj i) := pullback.fst _ _ ≫ incl.map W.1.obj.hom
  have hW : W.2.1 ≫ incl.map W.1.obj.hom = x₀ ≫ incl.map (P.proj.app i) := W.2.2
  have hV'p : V'.2.1 ≫ incl.map V'.1.obj.hom = y'.hom := V'.2.2
  have hfac : incl.map (P.proj.app i) ≫ incl.map (P.str.app i) ≫ incl.map ι =
      incl.map ιX ≫ incl.map f := by
    rw [← Category.assoc, ← Functor.map_comp, P.fac i, ← Functor.map_comp, ← Functor.map_comp,
      hV]
  have hsqw : incl.map g' ≫ incl.map f = incl.map f' ≫ incl.map g := sq.w
  have hn : W.2.1 ≫ incl.map W.1.obj.hom ≫ incl.map (P.str.app i) ≫ incl.map ι =
      V'.2.1 ≫ incl.map V'.1.obj.hom ≫ incl.map g := by
    rw [← Category.assoc, hW, Category.assoc, hfac, ← Category.assoc, hx₀, Category.assoc, hsqw,
      ← Category.assoc, p₀.2, ← Category.assoc, hV'p]
  let nb : y'.source ⟶ Ni := pullback.lift W.2.1 V'.2.1 hn
  have hnbν : nb ≫ ν = x₀ ≫ incl.map (P.proj.app i) := by
    simp only [nb, ν, pullback.lift_fst_assoc, hW]
  let R := pullback (incl.map (P.proj.app i)) ν
  let rXV : R ⟶ incl.obj XV := pullback.fst _ _
  let rN : R ⟶ Ni := pullback.snd _ _
  let rW := rN ≫ pullback.fst _ _
  let rV' := rN ≫ pullback.snd _ _
  have hT : IsPullback (incl.map (pullback.fst W.1.obj.hom (P.proj.app i)))
      (incl.map (pullback.snd W.1.obj.hom (P.proj.app i))) (incl.map W.1.obj.hom)
      (incl.map (P.proj.app i)) := isPullback_smallEtaleBaseChange_inclusion B (P.proj.app i) W.1
  have h1 : rW ≫ incl.map W.1.obj.hom = rXV ≫ incl.map (P.proj.app i) := by
    simp only [rW, Category.assoc]
    exact (pullback.condition (f := incl.map (P.proj.app i)) (g := ν)).symm
  let rT : R ⟶ (SmallEtale.toScheme B X.1 X.property).obj T := hT.lift rW rXV h1
  have h2 : (rXV ≫ incl.map ιX) ≫ incl.map f = (rV' ≫ incl.map V'.1.obj.hom) ≫ incl.map g := by
    have hc := pullback.condition (f := incl.map (P.proj.app i)) (g := ν)
    have hc' := pullback.condition (f := incl.map W.1.obj.hom ≫ incl.map (P.str.app i) ≫
      incl.map ι) (g := incl.map V'.1.obj.hom ≫ incl.map g)
    calc (rXV ≫ incl.map ιX) ≫ incl.map f
        = rXV ≫ incl.map (P.proj.app i) ≫ incl.map (P.str.app i) ≫ incl.map ι := by
          rw [hfac, Category.assoc]
      _ = (rXV ≫ incl.map (P.proj.app i)) ≫ incl.map (P.str.app i) ≫ incl.map ι :=
          (Category.assoc _ _ _).symm
      _ = (rN ≫ ν) ≫ incl.map (P.str.app i) ≫ incl.map ι :=
          congrArg (· ≫ incl.map (P.str.app i) ≫ incl.map ι) hc
      _ = rN ≫ pullback.fst _ _ ≫ incl.map W.1.obj.hom ≫ incl.map (P.str.app i) ≫
          incl.map ι := by simp only [ν, Category.assoc]
      _ = rN ≫ pullback.snd _ _ ≫ incl.map V'.1.obj.hom ≫ incl.map g :=
          congrArg (rN ≫ ·) hc'
      _ = (rV' ≫ incl.map V'.1.obj.hom) ≫ incl.map g := by simp only [rV', Category.assoc]
  let rX' : R ⟶ incl.obj X' := sq.lift (rXV ≫ incl.map ιX) (rV' ≫ incl.map V'.1.obj.hom) h2
  have hTh : incl.map T.obj.hom =
      incl.map (pullback.snd W.1.obj.hom (P.proj.app i)) ≫ incl.map ιX :=
    B.inclusion.map_comp _ _
  have h3 : rT ≫ incl.map T.obj.hom = rX' ≫ incl.map g' := by
    rw [hTh]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ incl.map ιX) (hT.lift_snd _ _ _)).trans
      (sq.lift_fst _ _ _).symm)
  let rQ : R ⟶ TS.obj Q := hQ.lift rT rX' h3
  have hBC : IsPullback (incl.map (pullback.fst V'.1.obj.hom f'))
      (incl.map (pullback.snd V'.1.obj.hom f')) (incl.map V'.1.obj.hom) (incl.map f') :=
    isPullback_smallEtaleBaseChange_inclusion B f' V'.1
  let rB : R ⟶ TS.obj ((smallEtaleBaseChange B f').obj V'.1) :=
    hBC.lift rV' rX' (sq.lift_snd _ _ _).symm
  let Θ : R ⟶ M := pullback.lift rQ rB ((hQ.lift_snd _ _ _).trans (hBC.lift_snd _ _ _).symm)
  let O' : (pullback (incl.map (P.proj.app i)) (Over.mk ν).hom).Opens := Θ ⁻¹ᵁ O
  -- the point attached to a lift
  have hpt (p : {a : y'.source ⟶ X'.1 // a ≫ B.inclusion.map f' = y'.hom})
      (x : y'.source ⟶ B.inclusion.obj XV) (hx : x ≫ B.inclusion.map ιX = p.1 ≫ B.inclusion.map g')
      (hxi : x ≫ B.inclusion.map (P.proj.app i) = x₀ ≫ B.inclusion.map (P.proj.app i)) :
      pullback.lift x nb (hxi.trans hnbν.symm) ≫ Θ =
        pullback.lift (qP p x hx hxi).1 (bP p).1
          ((qP p x hx hxi).2.trans (bP p).2.symm) := by
    let r := pullback.lift x nb (hxi.trans hnbν.symm)
    have hrX : r ≫ rXV = x := pullback.lift_fst _ _ _
    have hrN : r ≫ rN = nb := pullback.lift_snd _ _ _
    have hrW : r ≫ rW = W.2.1 := by
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst _ _) hrN).trans
        (pullback.lift_fst _ _ _))
    have hrV : r ≫ rV' = V'.2.1 := by
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.snd _ _) hrN).trans
        (pullback.lift_snd _ _ _))
    have hrX' : r ≫ rX' = p.1 :=
      comp_lift_eq_of_comp_eq sq r _ (by rw [← Category.assoc, hrX, hx])
        (by rw [← Category.assoc, hrV, hV'p, p.2])
    have hrT : r ≫ rT = (cylinderPoint B sq ιX P y' i x₀ W p x hx hxi).1 :=
      comp_lift_eq_of_comp_eq hT r _ (hrW.trans (hT.lift_fst _ _ _).symm)
        (hrX.trans (hT.lift_snd _ _ _).symm)
    have hrQ : r ≫ rQ = (qP p x hx hxi).1 :=
      comp_lift_eq_of_comp_eq hQ r _ (hrT.trans (hQ.lift_fst _ _ _).symm)
        (hrX'.trans (hQ.lift_snd _ _ _).symm)
    have hbfst : (bP p).1 ≫ incl.map (pullback.fst V'.1.obj.hom f') = V'.2.1 := by
      refine (baseChangeEtalePointHom_fst B f'
          (geometricPointLift_map (B.inclusion.map f') y' p) V'.1 V'.2).trans ?_
      simp
    have hrB : r ≫ rB = (bP p).1 :=
      comp_lift_eq_of_comp_eq hBC r _ (hrV.trans hbfst.symm)
        (hrX'.trans (baseChangeEtalePointHom_snd B f'
          (geometricPointLift_map (B.inclusion.map f') y' p) V'.1 V'.2).symm)
    exact comp_pullback_lift_eq_of_comp_eq r _ (hrQ.trans (pullback.lift_fst _ _ _).symm)
      (hrB.trans (pullback.lift_snd _ _ _).symm)
  -- the point attached to `p₀` lies in the image of the common neighbourhood
  have hNγ : N.2.1 ≫ γ = pullback.lift (qP p₀ x₀ hx₀ rfl).1 (bP p₀).1
      ((qP p₀ x₀ hx₀ rfl).2.trans (bP p₀).2.symm) := by
    exact comp_pullback_lift_eq_of_comp_eq N.2.1 _
      ((congrArg Subtype.val aN.2).trans (pullback.lift_fst _ _ _).symm)
      ((congrArg Subtype.val bN.2).trans (pullback.lift_snd _ _ _).symm)
  have hO : (pullback.lift x₀ nb (rfl.trans hnbν.symm)) (default : y'.source) ∈ O' := by
    refine (Scheme.Hom.mem_preimage (f := Θ)).mpr ⟨N.2.1 default, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hNγ, hpt p₀ x₀ hx₀ rfl]
  obtain ⟨j, a, hj⟩ := exists_stage_forall_lift_mem_of_isLimit (P.diagram ⋙ B.inclusion)
    (B.inclusion.mapCone (Cone.mk XV P.proj)) P.isLimit i (Over.mk ν) O' (default : y'.source) x₀ nb
    (rfl.trans hnbν.symm) hO
  refine ⟨j, a, fun p x hx hxj => ?_⟩
  have hxi : x ≫ B.inclusion.map (P.proj.app i) = x₀ ≫ B.inclusion.map (P.proj.app i) := by
    rw [← P.proj_comp_map a, Functor.map_comp, ← Category.assoc, hxj, Category.assoc]
  refine (hred p x hx hxi).mpr ?_
  have hmem := hj x (hxi.trans hnbν.symm) hxj
  obtain ⟨ν₀, hν₀⟩ := (Scheme.Hom.mem_preimage (f := Θ)).mp hmem
  rw [← Scheme.Hom.comp_apply] at hν₀
  have hν₀' := hν₀.trans (congrArg (fun m : y'.source ⟶ M => m default) (hpt p x hx hxi))
  obtain ⟨n, hn⟩ := exists_lift_of_etale_of_isAlgClosed γ _ ν₀ hν₀'
  have hnα : n ≫ α = (qP p x hx hxi).1 := by
    have := congrArg (· ≫ pullback.fst _ _) hn
    simp only [Category.assoc, γ, pullback.lift_fst] at this
    exact this.trans (pullback.lift_fst _ _ _)
  have hnβ : n ≫ β = (bP p).1 := by
    have := congrArg (· ≫ pullback.snd _ _) hn
    simp only [Category.assoc, γ, pullback.lift_snd] at this
    exact this.trans (pullback.lift_snd _ _ _)
  let N' : (geometricPointFiber B X'.1 X'.property
      (geometricPointLift (B.inclusion.map f') y' p)).Elements :=
    Functor.elementsMk _ N.1 ⟨n, by
      rw [← hα, ← Category.assoc, hnα]
      exact (qP p x hx hxi).2⟩
  let a' : N' ⟶ Functor.elementsMk _ Q (qP p x hx hxi) := ⟨aN.1, Subtype.ext hnα⟩
  let b' : N' ⟶ Functor.elementsMk _ ((smallEtaleBaseChange B f').obj V'.1) (bP p) := ⟨bN.1, Subtype.ext hnβ⟩
  have e₁ := ConcreteCategory.congr_hom (colimit.w (D p) a'.op) τ'
  have e₂ := ConcreteCategory.congr_hom (colimit.w (D p) b'.op) σ
  exact e₁.symm.trans ((congrArg (colimit.ι (D p) (op N')) hab).trans e₂)


end Cylinder

end AlgebraicGeometry
