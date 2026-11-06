module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange

/-!
# The fullness half of stage descent for proper flat families

The third geometric condition to which **Stacks 0D1I** is reduced,
`AlgebraicGeometry.ProperFlatFamilyIsomorphismDescendsAlongAffineLimit`, asks that an
*isomorphism* over the vertex of an affine cofiltered limit between the base changes of two stage
families descend to an isomorphism at a later stage. This file states the fullness half of
**Stacks 07SK** read on *arbitrary* morphisms, and shows that together with
`AlgebraicGeometry.ProperFlatMorphismEqualityDescendsAlongAffineLimit` it implies that condition.

## Main definitions

* `AlgebraicGeometry.ProperFlatMorphismDescendsAlongAffineLimit`: the fullness half of
  Stacks 07SK in the affine-base setting, read on arbitrary morphisms. A morphism over the vertex
  between the base changes of two stage families comes from a morphism between their base changes
  to a later stage.
* `AlgebraicGeometry.pullbackHomRestrict`: the restriction of a morphism of base changes to a
  later base.

## Main results

* `AlgebraicGeometry.pullbackBaseRestrict_comp`, `AlgebraicGeometry.stageBaseRestrict_comp`:
  restricting through an intermediate base is restricting to it.
* `AlgebraicGeometry.coneBaseRestrict_comp_pullbackBaseRestrict`: restricting from the vertex to a
  stage and then onwards is restricting from the vertex directly.
* `AlgebraicGeometry.pullbackBaseRestrict_cancel`: the restriction map and the second projection
  of the iterated fibre product cancel the same morphisms.
* `AlgebraicGeometry.properFlatFamilyIsomorphismDescendsAlongAffineLimit_of_fullness`: the
  third condition of Stacks 0D1I follows from the fullness half read on arbitrary morphisms
  together with descent of equalities.

## References

* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U U' W V : BigFppfOver B S hS}

/-- The comparison map of `AlgebraicGeometry.pullbackBaseRestrict` depends on the factorisation
only through the first factor. -/
theorem pullbackBaseRestrict_congr (f : X ⟶ yoneda.obj V) {p p' : U ⟶ W} {q : W ⟶ V} {r : U ⟶ V}
    (h : p ≫ q = r) (h' : p' ≫ q = r) (hp : p = p') :
    pullbackBaseRestrict f h = pullbackBaseRestrict f h' := by
  subst hp
  rfl

/-- **Restricting through an intermediate base is restricting to it.** -/
theorem pullbackBaseRestrict_comp (f : X ⟶ yoneda.obj V) {p₁ : U ⟶ U'} {p₂ : U' ⟶ W}
    {q : W ⟶ V} {q₁ : U' ⟶ V} {r : U ⟶ V} (h₁ : p₁ ≫ q₁ = r) (h₂ : p₂ ≫ q = q₁)
    (h₃ : (p₁ ≫ p₂) ≫ q = r) :
    pullbackBaseRestrict f h₁ ≫ pullbackBaseRestrict f h₂ = pullbackBaseRestrict f h₃ := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- **The base change of a base change is the base change along the composite.** The iterated
fibre product `U ×_W (W ×_V X)` is a fibre product of `U ⟶ V` and `X ⟶ V`, its first projection
and the composite of its second projection with the second projection of `W ×_V X` exhibiting it
as one. -/
private theorem isPullback_pullbackBase (f : X ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V}
    {r : U ⟶ V} (h : p ≫ q = r) :
    IsPullback (pullback.fst (yoneda.map p) (pullback.fst (yoneda.map q) f))
      (pullback.snd (yoneda.map p) (pullback.fst (yoneda.map q) f) ≫
        pullback.snd (yoneda.map q) f)
      (yoneda.map r) f := by
  have hy : yoneda.map p ≫ yoneda.map q = yoneda.map r := by
    rw [← Functor.map_comp, h]
  rw [← hy]
  exact ((IsPullback.of_hasPullback (yoneda.map p) (pullback.fst (yoneda.map q) f)).flip.paste_horiz
    (IsPullback.of_hasPullback (yoneda.map q) f).flip).flip

/-- **The restriction map is the second projection of the iterated fibre product**, up to the
comparison isomorphism of `AlgebraicGeometry.pullbackBaseRestrict` with that fibre product. -/
private theorem exists_iso_pullbackBaseRestrict (f : X ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V}
    {r : U ⟶ V} (h : p ≫ q = r) :
    ∃ e : pullback (yoneda.map p) (pullback.fst (yoneda.map q) f) ≅ pullback (yoneda.map r) f,
      e.hom ≫ pullbackBaseRestrict f h =
        pullback.snd (yoneda.map p) (pullback.fst (yoneda.map q) f) := by
  refine ⟨(isPullback_pullbackBase f h).isoPullback, ?_⟩
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullbackBaseRestrict_fst]
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    exact pullback.condition
  · simp only [Category.assoc, pullbackBaseRestrict_snd]
    exact IsPullback.isoPullback_hom_snd _

/-- **The restriction map to a later base and the second projection of the iterated fibre product
cancel the same morphisms.** -/
theorem pullbackBaseRestrict_cancel (f : X ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V} {r : U ⟶ V}
    (h : p ≫ q = r) {a a' : pullback (yoneda.map q) f ⟶ T} :
    pullbackBaseRestrict f h ≫ a = pullbackBaseRestrict f h ≫ a' ↔
      pullback.snd (yoneda.map p) (pullback.fst (yoneda.map q) f) ≫ a =
        pullback.snd (yoneda.map p) (pullback.fst (yoneda.map q) f) ≫ a' := by
  obtain ⟨e, he⟩ := exists_iso_pullbackBaseRestrict f h
  rw [← he]
  simp only [Category.assoc]
  exact (Iso.cancel_iso_hom_left e _ _).symm

/-- **The restriction of a morphism of base changes to a later base.** A morphism `w` of the base
changes of `f` and `g` along `q` which lies over the base restricts, along a factorisation
`p ≫ q = r`, to a morphism of their base changes along `r`. -/
def pullbackHomRestrict (f : X ⟶ yoneda.obj V) (g : Y ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V}
    {r : U ⟶ V} (h : p ≫ q = r) (w : pullback (yoneda.map q) f ⟶ pullback (yoneda.map q) g)
    (hw : w ≫ pullback.fst (yoneda.map q) g = pullback.fst (yoneda.map q) f) :
    pullback (yoneda.map r) f ⟶ pullback (yoneda.map r) g :=
  pullback.lift (pullback.fst (yoneda.map r) f)
    (pullbackBaseRestrict f h ≫ w ≫ pullback.snd (yoneda.map q) g)
    (by simp only [Category.assoc, ← pullback.condition, reassoc_of% hw,
      pullbackBaseRestrict_fst_assoc, ← Functor.map_comp, h])

/-- The first projection of `AlgebraicGeometry.pullbackHomRestrict`. -/
@[reassoc (attr := simp)]
theorem pullbackHomRestrict_fst (f : X ⟶ yoneda.obj V) (g : Y ⟶ yoneda.obj V) {p : U ⟶ W}
    {q : W ⟶ V} {r : U ⟶ V} (h : p ≫ q = r)
    (w : pullback (yoneda.map q) f ⟶ pullback (yoneda.map q) g)
    (hw : w ≫ pullback.fst (yoneda.map q) g = pullback.fst (yoneda.map q) f) :
    pullbackHomRestrict f g h w hw ≫ pullback.fst (yoneda.map r) g =
      pullback.fst (yoneda.map r) f :=
  pullback.lift_fst _ _ _

/-- The second projection of `AlgebraicGeometry.pullbackHomRestrict`. -/
@[reassoc (attr := simp)]
theorem pullbackHomRestrict_snd (f : X ⟶ yoneda.obj V) (g : Y ⟶ yoneda.obj V) {p : U ⟶ W}
    {q : W ⟶ V} {r : U ⟶ V} (h : p ≫ q = r)
    (w : pullback (yoneda.map q) f ⟶ pullback (yoneda.map q) g)
    (hw : w ≫ pullback.fst (yoneda.map q) g = pullback.fst (yoneda.map q) f) :
    pullbackHomRestrict f g h w hw ≫ pullback.snd (yoneda.map r) g =
      pullbackBaseRestrict f h ≫ w ≫ pullback.snd (yoneda.map q) g :=
  pullback.lift_snd _ _ _

/-- **The restriction of a morphism commutes with the restriction maps of its source and
target.** -/
@[reassoc (attr := simp)]
theorem pullbackHomRestrict_comp_pullbackBaseRestrict (f : X ⟶ yoneda.obj V)
    (g : Y ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V} {r : U ⟶ V} (h : p ≫ q = r)
    (w : pullback (yoneda.map q) f ⟶ pullback (yoneda.map q) g)
    (hw : w ≫ pullback.fst (yoneda.map q) g = pullback.fst (yoneda.map q) f) :
    pullbackHomRestrict f g h w hw ≫ pullbackBaseRestrict g h =
      pullbackBaseRestrict f h ≫ w := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullbackBaseRestrict_fst, pullbackHomRestrict_fst_assoc]
    rw [hw, pullbackBaseRestrict_fst]
  · simp only [Category.assoc, pullbackBaseRestrict_snd, pullbackHomRestrict_snd]

/-- **A morphism into a base change is determined by its first component and its restriction.** -/
theorem hom_ext_pullbackBaseRestrict (g : Y ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V} {r : U ⟶ V}
    (h : p ≫ q = r) {φ ψ : T ⟶ pullback (yoneda.map r) g}
    (hfst : φ ≫ pullback.fst (yoneda.map r) g = ψ ≫ pullback.fst (yoneda.map r) g)
    (hres : φ ≫ pullbackBaseRestrict g h = ψ ≫ pullbackBaseRestrict g h) : φ = ψ := by
  refine pullback.hom_ext hfst ?_
  rw [← pullbackBaseRestrict_snd g h]
  simp only [← Category.assoc, hres]

/-- **Restriction of morphisms is functorial.** -/
theorem pullbackHomRestrict_comp (f : X ⟶ yoneda.obj V) (g : Y ⟶ yoneda.obj V)
    (e : Z ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V} {r : U ⟶ V} (h : p ≫ q = r)
    (w : pullback (yoneda.map q) f ⟶ pullback (yoneda.map q) g)
    (hw : w ≫ pullback.fst (yoneda.map q) g = pullback.fst (yoneda.map q) f)
    (w' : pullback (yoneda.map q) g ⟶ pullback (yoneda.map q) e)
    (hw' : w' ≫ pullback.fst (yoneda.map q) e = pullback.fst (yoneda.map q) g) :
    pullbackHomRestrict f g h w hw ≫ pullbackHomRestrict g e h w' hw' =
      pullbackHomRestrict f e h (w ≫ w') (by rw [Category.assoc, hw', hw]) := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- **A morphism whose restriction is the identity restricts to the identity.** -/
theorem pullbackHomRestrict_eq_id (f : X ⟶ yoneda.obj V) {p : U ⟶ W} {q : W ⟶ V} {r : U ⟶ V}
    (h : p ≫ q = r) (w : pullback (yoneda.map q) f ⟶ pullback (yoneda.map q) f)
    (hw : w ≫ pullback.fst (yoneda.map q) f = pullback.fst (yoneda.map q) f)
    (hid : pullbackBaseRestrict f h ≫ w = pullbackBaseRestrict f h) :
    pullbackHomRestrict f f h w hw = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullbackHomRestrict_fst, Category.id_comp]
  · rw [pullbackHomRestrict_snd, ← Category.assoc, hid, pullbackBaseRestrict_snd,
      Category.id_comp]

/-- **The base change of a finitely presented, flat and proper algebraic space along a morphism of
the site is again one.** -/
theorem pullback_yoneda_properties {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : BigFppfOver B S hS} (hX : IsAlgebraicSpace B S hS X) (φ : U ⟶ V)
    (f : X ⟶ yoneda.obj V) (hfp : Space.IsFinitePresentation B S hS f)
    (hfl : Space.IsFlat B S hS f) (hpr : Space.IsProper B S hS f) :
    IsAlgebraicSpace B S hS (pullback (yoneda.map φ) f) ∧
      Space.IsFinitePresentation B S hS (pullback.fst (yoneda.map φ) f) ∧
      Space.IsFlat B S hS (pullback.fst (yoneda.map φ) f) ∧
      Space.IsProper B S hS (pullback.fst (yoneda.map φ) f) := by
  have hpb : IsPullback (pullback.fst (yoneda.map φ) f) (pullback.snd (yoneda.map φ) f)
      (yoneda.map φ) f := IsPullback.of_hasPullback _ _
  have halg : IsAlgebraicSpace B S hS (pullback (yoneda.map φ) f) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS U) hX
      (isAlgebraicSpace_yoneda B S hS V)
  have hsq : IsPullback
      (ObjectProperty.homMk (pullback.fst (yoneda.map φ) f) :
        (⟨pullback (yoneda.map φ) f, halg⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (ObjectProperty.homMk (pullback.snd (yoneda.map φ) f) :
        (⟨pullback (yoneda.map φ) f, halg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk (yoneda.map φ) :
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      (ObjectProperty.homMk f :
        (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) hpb
  refine ⟨halg, ?_, ?_, ?_⟩
  · exact Space.IsFinitePresentation.of_isPullback B S hS halg hX
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V) hpb.flip hfp
  · exact (Space.isFlat_isStableUnderBaseChange B S hS).of_isPullback hsq.flip hfl
  · exact (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback hsq.flip hpr

end BaseChange

section StageRestrict

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {I : Type v} [Category.{w} I]

/-- The factorisation of the transition morphism of the diagram through an intermediate stage,
transported to the site. -/
theorem stageFac (D : I ⥤ BigAffineFppf B S hS) {i j m : I} (α : m ⟶ j) (s : j ⟶ i)
    {σ : m ⟶ i} (hσ : α ≫ s = σ) :
    (BigAffineFppf.inclusion B S hS).map (D.map α) ≫
        (BigAffineFppf.inclusion B S hS).map (D.map s) =
      (BigAffineFppf.inclusion B S hS).map (D.map σ) := by
  simp only [← Functor.map_comp, hσ]

/-- **Restricting a base change from one stage to an earlier one and then onwards.** -/
theorem stageBaseRestrict_comp (D : I ⥤ BigAffineFppf B S hS)
    {Xp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i j m n : I} (δ : n ⟶ m) (α : m ⟶ j) (s : j ⟶ i)
    {σ : m ⟶ i} (hσ : α ≫ s = σ) {τ : n ⟶ i} (hτ : δ ≫ σ = τ) (hτ' : (δ ≫ α) ≫ s = τ)
    (f : Xp ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) :
    pullbackBaseRestrict f (stageFac D δ σ hτ) ≫ pullbackBaseRestrict f (stageFac D α s hσ) =
      pullbackBaseRestrict f (stageFac D (δ ≫ α) s hτ') := by
  have hp : (BigAffineFppf.inclusion B S hS).map (D.map δ) ≫
      (BigAffineFppf.inclusion B S hS).map (D.map α) =
      (BigAffineFppf.inclusion B S hS).map (D.map (δ ≫ α)) := by
    simp only [← Functor.map_comp]
  have h₃ : ((BigAffineFppf.inclusion B S hS).map (D.map δ) ≫
      (BigAffineFppf.inclusion B S hS).map (D.map α)) ≫
      (BigAffineFppf.inclusion B S hS).map (D.map s) =
      (BigAffineFppf.inclusion B S hS).map (D.map τ) := by
    rw [hp]
    exact stageFac D (δ ≫ α) s hτ'
  exact (pullbackBaseRestrict_comp f (stageFac D δ σ hτ) (stageFac D α s hσ) h₃).trans
    (pullbackBaseRestrict_congr f h₃ (stageFac D (δ ≫ α) s hτ') hp)

/-- **Restricting from the vertex to a stage and then onwards is restricting from the vertex
directly.** -/
theorem coneBaseRestrict_comp_pullbackBaseRestrict {D : I ⥤ BigAffineFppf B S hS} (c : Cone D)
    {Xp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i j m : I} (α : m ⟶ j) (s : j ⟶ i) {σ : m ⟶ i}
    (hσ : α ≫ s = σ)
    (f : Xp ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) :
    coneBaseRestrict c σ f ≫ pullbackBaseRestrict f (stageFac D α s hσ) =
      coneBaseRestrict c s f := by
  have hπ : yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app m)) ≫
      yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map α)) =
      yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app j)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, c.w α]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullbackBaseRestrict_fst, coneBaseRestrict_fst,
      coneBaseRestrict_fst_assoc]
    rw [hπ]
  · simp only [Category.assoc, pullbackBaseRestrict_snd, coneBaseRestrict_snd]

/-- The restriction map from the vertex and the second projection of the iterated fibre product
cancel the same morphisms. This is `AlgebraicGeometry.pullbackBaseRestrict_cancel` at the cone
projection. -/
theorem coneBaseRestrict_cancel {D : I ⥤ BigAffineFppf B S hS} (c : Cone D)
    {Xp T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i m : I} (σ : m ⟶ i)
    (f : Xp ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    {a a' : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) f ⟶ T} :
    coneBaseRestrict c σ f ≫ a = coneBaseRestrict c σ f ≫ a' ↔
      pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app m)))
            (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) f) ≫ a =
        pullback.snd (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app m)))
            (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) f) ≫ a' :=
  pullbackBaseRestrict_cancel f
    (p := (BigAffineFppf.inclusion B S hS).map (c.π.app m))
    (by rw [← Functor.map_comp, c.w σ])

/-- **An equality of morphisms that holds after restricting to a stage holds after restricting to
any stage factoring through it.** -/
theorem pullbackBaseRestrict_eq_of_factor (D : I ⥤ BigAffineFppf B S hS)
    {Xp T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i m n n₁ : I} (δ : n ⟶ n₁) (γ₁ : n₁ ⟶ m)
    {γ : n ⟶ m} (hγ : δ ≫ γ₁ = γ) (σ : m ⟶ i) {τ : n ⟶ i} (hτ : γ ≫ σ = τ)
    (f : Xp ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    {a a' : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) f ⟶ T}
    (h : pullbackBaseRestrict f (stageFac D γ₁ σ rfl) ≫ a =
      pullbackBaseRestrict f (stageFac D γ₁ σ rfl) ≫ a') :
    pullbackBaseRestrict f (stageFac D γ σ hτ) ≫ a =
      pullbackBaseRestrict f (stageFac D γ σ hτ) ≫ a' := by
  subst hγ
  have hassoc : δ ≫ (γ₁ ≫ σ) = τ := (Category.assoc _ _ _).symm.trans hτ
  rw [← stageBaseRestrict_comp D δ γ₁ σ rfl hassoc hτ f]
  simp only [Category.assoc]
  rw [h]

/-- **Propagating the compatibility with a morphism over the vertex to a later stage.** -/
theorem coneBaseRestrict_comp_pullbackHomRestrict {D : I ⥤ BigAffineFppf B S hS} (c : Cone D)
    {Xp Yp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i j m : I} (α : m ⟶ j) (s : j ⟶ i) {σ : m ⟶ i}
    (hσ : α ≫ s = σ)
    (f : Xp ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (g : Yp ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (u : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f ⟶
      pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) g)
    (hu : u ≫ pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) g =
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f)
    (w : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f ⟶
      pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) g)
    (hw : w ≫ pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) g =
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f)
    (hcompat : coneBaseRestrict c s f ≫ w = u ≫ coneBaseRestrict c s g) :
    coneBaseRestrict c σ f ≫ pullbackHomRestrict f g (stageFac D α s hσ) w hw =
      u ≫ coneBaseRestrict c σ g := by
  refine hom_ext_pullbackBaseRestrict g (stageFac D α s hσ) ?_ ?_
  · simp only [Category.assoc, pullbackHomRestrict_fst, coneBaseRestrict_fst]
    rw [← Category.assoc, hu]
  · rw [Category.assoc, pullbackHomRestrict_comp_pullbackBaseRestrict, ← Category.assoc,
      coneBaseRestrict_comp_pullbackBaseRestrict c α s hσ f, hcompat, Category.assoc,
      coneBaseRestrict_comp_pullbackBaseRestrict c α s hσ g]

end StageRestrict

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent of morphisms of finitely presented, flat and proper families along an affine
cofiltered limit.** Let `T = lim Tᵢ` be a cofiltered inverse system of affine schemes of the big
fppf site of `S` whose cone of underlying schemes is a limit, and let `X ⟶ h_{Tᵢ}` and
`Y ⟶ h_{Tᵢ}` be finitely presented, flat and proper algebraic spaces over a stage. The condition
says that a morphism over `h_T` between their base changes to the vertex comes from a morphism
between their base changes to a later stage, compatibly with the restriction map
`AlgebraicGeometry.coneBaseRestrict`.

This is the **fullness half of Stacks 07SK** in the affine-base setting, read on arbitrary
morphisms. -/
def ProperFlatMorphismDescendsAlongAffineLimit : Prop :=
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
    ∀ (i : I) (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y →
    ∀ (f : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
      (g : Y ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))),
      Space.IsFinitePresentation B S hS f → Space.IsFlat B S hS f → Space.IsProper B S hS f →
      Space.IsFinitePresentation B S hS g → Space.IsFlat B S hS g → Space.IsProper B S hS g →
    ∀ u : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f ⟶
        pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) g,
      u ≫ pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) g =
        pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f →
      ∃ (k : I) (s : k ⟶ i)
        (v : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f ⟶
          pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) g),
        v ≫ pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) g =
          pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s))) f ∧
        coneBaseRestrict c s f ≫ v = u ≫ coneBaseRestrict c s g

/-- **A pair of mutually inverse morphisms over the vertex has composite restricting to the
identity at a later stage.** If `v` and `v'` lift `u` and its left inverse `u'` to the stage `σ`,
the composite `v ≫ v'` agrees with the identity after restricting along some `γ : n ⟶ m`. -/
private theorem exists_restrict_comp_eq_self
    (heq : ProperFlatMorphismEqualityDescendsAlongAffineLimit.{u, v, w} B S hS)
    {I : Type v} [Category.{w} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) {i m : I} (σ : m ⟶ i)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (g : Y ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (hfp : Space.IsFinitePresentation B S hS f) (hfl : Space.IsFlat B S hS f)
    (hpr : Space.IsProper B S hS f)
    (u : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f ⟶
      pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) g)
    (u' : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) g ⟶
      pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f)
    (hu : u ≫ u' = 𝟙 _)
    (v : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) f ⟶
      pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) g)
    (v' : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) g ⟶
      pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) f)
    (hvfst : v ≫ pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) g =
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) f)
    (hv'fst : v' ≫ pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) f =
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) g)
    (hv : coneBaseRestrict c σ f ≫ v = u ≫ coneBaseRestrict c σ g)
    (hv' : coneBaseRestrict c σ g ≫ v' = u' ≫ coneBaseRestrict c σ f) :
    ∃ (n : I) (γ : n ⟶ m), pullbackBaseRestrict f (stageFac D γ σ rfl) ≫ (v ≫ v') =
      pullbackBaseRestrict f (stageFac D γ σ rfl) ≫ 𝟙 _ := by
  have hvv' : coneBaseRestrict c σ f ≫ (v ≫ v') = coneBaseRestrict c σ f ≫ 𝟙 _ := by
    rw [← Category.assoc, hv, Category.assoc, hv', ← Category.assoc, hu, Category.id_comp,
      Category.comp_id]
  obtain ⟨hXm, hfpm, hflm, hprm⟩ := pullback_yoneda_properties hX
    ((BigAffineFppf.inclusion B S hS).map (D.map σ)) f hfp hfl hpr
  obtain ⟨n, γ, hn⟩ := heq I D c hc m _ _ hXm hXm
    (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) f)
    (pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map σ))) f)
    hfpm hflm hprm hfpm hflm hprm (v ≫ v') (𝟙 _)
    (by rw [Category.assoc, hv'fst, hvfst]) (Category.id_comp _)
    ((coneBaseRestrict_cancel c σ f).mp hvv')
  exact ⟨n, γ, (pullbackBaseRestrict_cancel f (stageFac D γ σ rfl)).mpr hn⟩

/-- **Descent of isomorphisms follows from descent of morphisms together with descent of
equalities.** -/
theorem properFlatFamilyIsomorphismDescendsAlongAffineLimit_of_fullness
    (hfull : ProperFlatMorphismDescendsAlongAffineLimit.{u, v, w} B S hS)
    (heq : ProperFlatMorphismEqualityDescendsAlongAffineLimit.{u, v, w} B S hS) :
    ProperFlatFamilyIsomorphismDescendsAlongAffineLimit.{u, v, w} B S hS := by
  intro I _ _ D c hc i X Y hX hY f g hfp hfl hpr hgp hgl hgr u hiso hufst
  have hinvfst : inv u ≫
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) f =
      pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) g := by
    rw [← hufst, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  obtain ⟨j, s, w₁, hw₁fst, hw₁⟩ :=
    hfull I D c hc i X Y hX hY f g hfp hfl hpr hgp hgl hgr u hufst
  obtain ⟨k, t, w₂, hw₂fst, hw₂⟩ :=
    hfull I D c hc i Y X hY hX g f hgp hgl hgr hfp hfl hpr (inv u) hinvfst
  obtain ⟨m, α, β, hαβ⟩ : ∃ (m : I) (α : m ⟶ j) (β : m ⟶ k), α ≫ s = β ≫ t :=
    ⟨IsCofiltered.eq (IsCofiltered.minToLeft j k ≫ s) (IsCofiltered.minToRight j k ≫ t),
      IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToLeft j k,
      IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToRight j k, by
        rw [Category.assoc, Category.assoc]
        exact IsCofiltered.eq_condition _ _⟩
  obtain ⟨v, hvfst, hvcompat⟩ :
      ∃ v : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map (α ≫ s)))) f ⟶
        pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map (α ≫ s)))) g,
        v ≫ pullback.fst
              (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map (α ≫ s)))) g =
            pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map (α ≫ s)))) f ∧
          coneBaseRestrict c (α ≫ s) f ≫ v = u ≫ coneBaseRestrict c (α ≫ s) g :=
    ⟨pullbackHomRestrict f g (stageFac D α s rfl) w₁ hw₁fst,
      pullbackHomRestrict_fst f g (stageFac D α s rfl) w₁ hw₁fst,
      coneBaseRestrict_comp_pullbackHomRestrict c α s rfl f g u hufst w₁ hw₁fst hw₁⟩
  obtain ⟨v', hv'fst, hv'compat⟩ :
      ∃ v' : pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map (α ≫ s)))) g ⟶
        pullback (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map (α ≫ s)))) f,
        v' ≫ pullback.fst
              (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map (α ≫ s)))) f =
            pullback.fst (yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map (α ≫ s)))) g ∧
          coneBaseRestrict c (α ≫ s) g ≫ v' = inv u ≫ coneBaseRestrict c (α ≫ s) f :=
    ⟨pullbackHomRestrict g f (stageFac D β t hαβ.symm) w₂ hw₂fst,
      pullbackHomRestrict_fst g f (stageFac D β t hαβ.symm) w₂ hw₂fst,
      coneBaseRestrict_comp_pullbackHomRestrict c β t hαβ.symm g f (inv u) hinvfst w₂ hw₂fst hw₂⟩
  obtain ⟨n₁, γ₁, hn₁⟩ := exists_restrict_comp_eq_self B S hS heq D c hc (α ≫ s) hX f g hfp hfl
    hpr u (inv u) (IsIso.hom_inv_id u) v v' hvfst hv'fst hvcompat hv'compat
  obtain ⟨n₂, γ₂, hn₂⟩ := exists_restrict_comp_eq_self B S hS heq D c hc (α ≫ s) hY g f hgp hgl
    hgr (inv u) u (IsIso.inv_hom_id u) v' v hv'fst hvfst hv'compat hvcompat
  obtain ⟨n, γ, δ₁, hδ₁, δ₂, hδ₂⟩ : ∃ (n : I) (γ : n ⟶ m) (δ₁ : n ⟶ n₁),
      δ₁ ≫ γ₁ = γ ∧ ∃ δ₂ : n ⟶ n₂, δ₂ ≫ γ₂ = γ :=
    ⟨IsCofiltered.eq (IsCofiltered.minToLeft n₁ n₂ ≫ γ₁) (IsCofiltered.minToRight n₁ n₂ ≫ γ₂),
      (IsCofiltered.eqHom (IsCofiltered.minToLeft n₁ n₂ ≫ γ₁)
        (IsCofiltered.minToRight n₁ n₂ ≫ γ₂) ≫ IsCofiltered.minToLeft n₁ n₂) ≫ γ₁,
      IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToLeft n₁ n₂, rfl,
      IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToRight n₁ n₂, by
        rw [Category.assoc, Category.assoc]
        exact (IsCofiltered.eq_condition _ _).symm⟩
  have hkeyf : pullbackBaseRestrict f (stageFac D γ (α ≫ s) rfl) ≫ (v ≫ v') =
      pullbackBaseRestrict f (stageFac D γ (α ≫ s) rfl) :=
    (pullbackBaseRestrict_eq_of_factor D δ₁ γ₁ hδ₁ (α ≫ s) rfl f hn₁).trans
      (Category.comp_id _)
  have hkeyg : pullbackBaseRestrict g (stageFac D γ (α ≫ s) rfl) ≫ (v' ≫ v) =
      pullbackBaseRestrict g (stageFac D γ (α ≫ s) rfl) :=
    (pullbackBaseRestrict_eq_of_factor D δ₂ γ₂ hδ₂ (α ≫ s) rfl g hn₂).trans
      (Category.comp_id _)
  refine ⟨n, γ ≫ (α ≫ s), pullbackHomRestrict f g (stageFac D γ (α ≫ s) rfl) v hvfst, ?_, ?_, ?_⟩
  · refine ⟨⟨pullbackHomRestrict g f (stageFac D γ (α ≫ s) rfl) v' hv'fst, ?_, ?_⟩⟩
    · exact (pullbackHomRestrict_comp f g f (stageFac D γ (α ≫ s) rfl) v hvfst v' hv'fst).trans
        (pullbackHomRestrict_eq_id f (stageFac D γ (α ≫ s) rfl) (v ≫ v') _ hkeyf)
    · exact (pullbackHomRestrict_comp g f g (stageFac D γ (α ≫ s) rfl) v' hv'fst v hvfst).trans
        (pullbackHomRestrict_eq_id g (stageFac D γ (α ≫ s) rfl) (v' ≫ v) _ hkeyg)
  · exact pullbackHomRestrict_fst f g (stageFac D γ (α ≫ s) rfl) v hvfst
  · exact coneBaseRestrict_comp_pullbackHomRestrict c γ (α ≫ s) rfl f g u hufst v hvfst hvcompat

end AlgebraicGeometry

end
