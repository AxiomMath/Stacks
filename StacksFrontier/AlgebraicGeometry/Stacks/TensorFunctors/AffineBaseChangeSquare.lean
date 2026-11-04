module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

/-!
# A right adjoint of a 1-morphism out of a slice commutes with base change

Let `p : 𝒳 ⥤ 𝒞` be fibred in groupoids, let `U` be an object of `𝒞` and let
`G : 𝒞/U ⥤ 𝒳` be a 1-morphism over `𝒞` (so `G ⋙ p = Over.forget U`) with a right adjoint
`r : 𝒳 ⥤ 𝒞/U`, `x ↦ U ×_𝒳 x`.  For a morphism `φ : x' ⟶ x` of `𝒳` the square

```
(r x').left ⟶ (r x).left
     |             |
   p x'    ⟶     p x
```

whose vertical arrows lie under the counit is cartesian in `𝒞`: the formation of `U ×_𝒳 x`
commutes with base change.  The proof is the universal property of the counit, together with the
fact that `φ` is strongly cartesian, every morphism of a category fibred in groupoids being so.

This is applied to the right adjoint of an affine 1-morphism from a scheme to an algebraic stack.

## Main definitions

* `CategoryTheory.Functor.counitBase`: the morphism `(r x).left ⟶ p x` underlying the counit.

## Main results

* `CategoryTheory.Functor.isPullback_counitBase`: the square above is a pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor

namespace CategoryTheory.Functor

variable {𝒞 : Type*} [Category 𝒞] {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ 𝒞)
  {U : 𝒞} (G : Over U ⥤ 𝒳) (hG : G ⋙ p = Over.forget U) {r : 𝒳 ⥤ Over U} (adj : G ⊣ r)

include hG in
/-- `p (G f) = f.left` up to the identifications `p (G u) = u.left`. -/
theorem map_map_of_comp_eq_forget {u u' : Over U} (f : u ⟶ u') :
    p.map (G.map f) = eqToHom (Functor.congr_obj hG u) ≫ f.left ≫
      eqToHom (Functor.congr_obj hG u').symm := by
  have h := Functor.congr_hom hG f
  simpa using h

/-- **The projection `(r x).left ⟶ p x`** underlying the counit of `G ⊣ r` at `x`. -/
def counitBase (x : 𝒳) : (r.obj x).left ⟶ p.obj x :=
  eqToHom (Functor.congr_obj hG (r.obj x)).symm ≫ p.map (adj.counit.app x)

/-- The counit squares commute. -/
theorem counitBase_naturality {x x' : 𝒳} (φ : x' ⟶ x) :
    (r.map φ).left ≫ counitBase p G hG adj x = counitBase p G hG adj x' ≫ p.map φ := by
  have h := congrArg p.map (adj.counit.naturality φ)
  simp only [Functor.comp_map, Functor.map_comp, Functor.id_map] at h
  rw [map_map_of_comp_eq_forget p G hG] at h
  simp only [counitBase, Category.assoc] at h ⊢
  rw [← h]
  simp

section Lift

variable (hp : p.IsFiberedInGroupoids) {x x' : 𝒳} (φ : x' ⟶ x) {Z : 𝒞}
  (a : Z ⟶ (r.obj x).left) (b : Z ⟶ p.obj x')
  (hab : a ≫ counitBase p G hG adj x = b ≫ p.map φ)

/-- The object of `𝒞/U` given by `a` followed by the structure morphism of `r x`. -/
abbrev baseChangeLiftObj : Over U := Over.mk (a ≫ (r.obj x).hom)

/-- The morphism `G (Z → U) ⟶ x` given by `a` and the counit. -/
def baseChangeLiftδ : G.obj (baseChangeLiftObj a) ⟶ x :=
  G.map (Over.homMk a : baseChangeLiftObj a ⟶ r.obj x) ≫ adj.counit.app x

include hab in
/-- The image of `baseChangeLiftδ` under `p` factors through `p φ`, as `b` followed by `p φ`. -/
theorem map_baseChangeLiftδ :
    p.map (baseChangeLiftδ G adj a) =
      (eqToHom (Functor.congr_obj hG (baseChangeLiftObj a)) ≫ b) ≫ p.map φ := by
  rw [Category.assoc, ← hab]
  simp [baseChangeLiftδ, counitBase, map_map_of_comp_eq_forget p G hG]

/-- The morphism `G (Z → U) ⟶ x'` obtained by lifting along the strongly cartesian `φ`. -/
noncomputable def baseChangeLiftψ : G.obj (baseChangeLiftObj a) ⟶ x' :=
  @IsStronglyCartesian.map _ _ _ _ p _ _ _ _ (p.map φ) φ
    (hp.isStronglyCartesian_homLift (p.map φ) φ) _ _
    (eqToHom (Functor.congr_obj hG (baseChangeLiftObj a)) ≫ b) _
    (map_baseChangeLiftδ p G hG adj φ a b hab) (baseChangeLiftδ G adj a) (IsHomLift.map _)

/-- `baseChangeLiftψ` lies over `b`, up to the identification `p (G (Z → U)) = Z`. -/
theorem baseChangeLiftψ_isHomLift :
    p.IsHomLift (eqToHom (Functor.congr_obj hG (baseChangeLiftObj a)) ≫ b)
      (baseChangeLiftψ p G hG adj hp φ a b hab) := by
  have := hp.isStronglyCartesian_homLift (p.map φ) φ
  unfold baseChangeLiftψ
  infer_instance

/-- `baseChangeLiftψ` followed by `φ` is `baseChangeLiftδ`. -/
theorem baseChangeLiftψ_fac :
    baseChangeLiftψ p G hG adj hp φ a b hab ≫ φ = baseChangeLiftδ G adj a := by
  have := hp.isStronglyCartesian_homLift (p.map φ) φ
  unfold baseChangeLiftψ
  exact IsStronglyCartesian.fac ..

/-- The morphism of `𝒞/U` into `r x'` corresponding to `baseChangeLiftψ`. -/
noncomputable def baseChangeLiftHom : baseChangeLiftObj a ⟶ r.obj x' :=
  (adj.homEquiv _ _) (baseChangeLiftψ p G hG adj hp φ a b hab)

/-- `baseChangeLiftHom` followed by `r φ` is the morphism of `𝒞/U` given by `a`. -/
theorem baseChangeLiftHom_comp :
    baseChangeLiftHom p G hG adj hp φ a b hab ≫ r.map φ = Over.homMk a := by
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm, baseChangeLiftHom, Equiv.symm_apply_apply,
    baseChangeLiftψ_fac, baseChangeLiftδ, Adjunction.homEquiv_counit]

/-- The morphism underlying `baseChangeLiftHom`, followed by the counit projection of `x'`,
is `b`. -/
theorem baseChangeLiftHom_left_comp :
    (baseChangeLiftHom p G hG adj hp φ a b hab).left ≫ counitBase p G hG adj x' = b := by
  have h1 : G.map (baseChangeLiftHom p G hG adj hp φ a b hab) ≫ adj.counit.app x' =
      baseChangeLiftψ p G hG adj hp φ a b hab :=
    (Adjunction.homEquiv_counit adj
      (g := baseChangeLiftHom p G hG adj hp φ a b hab)).symm.trans
      ((adj.homEquiv _ _).symm_apply_apply _)
  have h2 := congrArg p.map h1
  have := baseChangeLiftψ_isHomLift p G hG adj hp φ a b hab
  rw [IsHomLift.fac' p (eqToHom (Functor.congr_obj hG (baseChangeLiftObj a)) ≫ b)
    (baseChangeLiftψ p G hG adj hp φ a b hab), Functor.map_comp,
    map_map_of_comp_eq_forget p G hG] at h2
  simp only [counitBase]
  simp only [Category.assoc, eqToHom_trans_assoc] at h2
  rw [← cancel_epi (eqToHom (Functor.congr_obj hG (baseChangeLiftObj a)))]
  simpa using h2

include hab in
/-- A morphism `m : Z ⟶ (r x').left` with `m ≫ (r φ).left = a` and `m ≫ counitBase x' = b` is
the morphism underlying `baseChangeLiftHom`. -/
theorem baseChangeLift_uniq (m : Z ⟶ (r.obj x').left) (h₁ : m ≫ (r.map φ).left = a)
    (h₂ : m ≫ counitBase p G hG adj x' = b) :
    m = (baseChangeLiftHom p G hG adj hp φ a b hab).left := by
  have hw : m ≫ (r.obj x').hom = (baseChangeLiftObj a).hom := by
    simp only [Over.mk_hom, ← h₁, Category.assoc, Over.w]
  let m' : baseChangeLiftObj a ⟶ r.obj x' := Over.homMk m hw
  suffices hm : m' = baseChangeLiftHom p G hG adj hp φ a b hab from congrArg (·.left) hm
  have hm' : m' ≫ r.map φ = Over.homMk a := by ext; exact h₁
  apply (adj.homEquiv _ _).symm.injective
  rw [baseChangeLiftHom, Equiv.symm_apply_apply]
  have : p.IsHomLift (eqToHom (Functor.congr_obj hG (baseChangeLiftObj a)) ≫ b)
      ((adj.homEquiv _ _).symm m') := by
    refine IsHomLift.of_fac' p _ _ rfl rfl ?_
    rw [Adjunction.homEquiv_counit, Functor.map_comp, map_map_of_comp_eq_forget p G hG, ← h₂]
    simp [counitBase, m']
  have := hp.isStronglyCartesian_homLift (p.map φ) φ
  unfold baseChangeLiftψ
  refine IsStronglyCartesian.map_uniq (hψ := ?_) ..
  rw [← Adjunction.homEquiv_naturality_right_symm, hm', Adjunction.homEquiv_counit]
  rfl

end Lift

include hG in
/-- **The formation of `U ×_𝒳 x` commutes with base change**: the counit squares of `G ⊣ r` are
cartesian in `𝒞`. -/
theorem isPullback_counitBase (hp : p.IsFiberedInGroupoids) {x x' : 𝒳} (φ : x' ⟶ x) :
    IsPullback (r.map φ).left (counitBase p G hG adj x') (counitBase p G hG adj x) (p.map φ) :=
  ⟨⟨counitBase_naturality p G hG adj φ⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => (baseChangeLiftHom p G hG adj hp φ s.fst s.snd s.condition).left)
    (fun s => by
      rw [← Over.comp_left, baseChangeLiftHom_comp]; rfl)
    (fun s => baseChangeLiftHom_left_comp p G hG adj hp φ s.fst s.snd s.condition)
    (fun s m h₁ h₂ => baseChangeLift_uniq p G hG adj hp φ s.fst s.snd s.condition m h₁ h₂)⟩⟩

end CategoryTheory.Functor
