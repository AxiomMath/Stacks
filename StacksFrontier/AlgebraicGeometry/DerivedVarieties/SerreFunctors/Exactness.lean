module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.Trace

/-!
# Exactness of a Serre functor

A Serre functor on a linear pretriangulated category commutes with translation and takes
distinguished triangles to distinguished triangles. The translation isomorphisms are not
assumed: they are produced from the Serre pairing, with the sign `(-1)^n` on the `n`-fold
shift, and are then shown to be coherent.

## Main results

* `CategoryTheory.serreEquivalence_exists_isTriangulated` states that a Serre equivalence
  admits coherent shift isomorphisms making it an exact functor of triangulated categories.

## Implementation notes

Exactness is expressed by a `CategoryTheory.Functor.CommShift ℤ` structure together with
`CategoryTheory.Functor.IsTriangulated`, and both are part of the conclusion. Following the
source's convention for a linear triangulated category, every translation functor is assumed
linear. Only the pretriangulated axioms are used: neither the octahedral axiom nor
Hom-finiteness enters, the latter because the Serre pairing forces each Hom space to be
finite-dimensional on its own.

## References

* [Stacks Project, Tag 0FY6](https://stacks.math.columbia.edu/tag/0FY6)
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory

universe u v w

private theorem serreFunctor_map_add
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] (S : SerreEquivalence k (C := C))
    {X Y : C} (f g : X ⟶ Y) :
    S.equivalence.functor.map (f + g) =
      S.equivalence.functor.map f + S.equivalence.functor.map g := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff k
    (S.equivalence.functor.map (f + g) -
      (S.equivalence.functor.map f + S.equivalence.functor.map g))).mp
  intro ψ
  obtain ⟨h, rfl⟩ := (S.pairing Y (S.equivalence.functor.obj X)).surjective ψ
  have natEval (u : X ⟶ Y) :
      S.pairing Y (S.equivalence.functor.obj X) h (S.equivalence.functor.map u) =
        S.pairing X (S.equivalence.functor.obj X) (u ≫ h) (𝟙 _) := by
    have he := congrArg (fun φ : Module.Dual k
        (S.equivalence.functor.obj X ⟶ S.equivalence.functor.obj X) => φ (𝟙 _))
      (S.pairing_naturality_left u h)
    simpa [LinearMap.dualMap_apply, Linear.rightComp_apply, Category.assoc] using he.symm
  rw [map_sub, map_add]
  rw [natEval (f + g), natEval f, natEval g]
  simp [Preadditive.add_comp]

private noncomputable def serreHomEquiv
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] (S : SerreEquivalence k (C := C)) (X Y : C) :
    (Y ⟶ S.equivalence.functor.obj X) ≃ₗ[k]
      (S.equivalence.inverse.obj Y ⟶ X) := by
  let : S.equivalence.functor.Additive := by
    refine ⟨?_⟩
    intro X Y f g
    exact serreFunctor_map_add k S f g
  let c := S.equivalence.counitIso.app Y
  refine
    { toFun := fun g => S.equivalence.functor.preimage (c.hom ≫ g)
      invFun := fun f => c.inv ≫ S.equivalence.functor.map f
      left_inv := by
        intro g
        apply S.equivalence.functor.map_injective
        simp
      right_inv := by
        intro f
        simp
      map_add' := by
        intro f g
        apply S.equivalence.functor.map_injective
        simp
      map_smul' := by
        intro r f
        apply S.equivalence.functor.map_injective
        simp [S.linear.map_smul, Linear.comp_smul] }

private def postcompIsoEquiv {k : Type u} [Field k] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C] {X Y Z : C} (e : Y ≅ Z) :
    (X ⟶ Y) ≃ₗ[k] (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp
  map_smul' r f := by simp

private noncomputable def serreHomBidualEquiv
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] (S : SerreEquivalence k (C := C)) (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] Module.Dual k (Module.Dual k (X ⟶ Y)) := by
  let Z := S.equivalence.inverse.obj Y
  let c := S.equivalence.counitIso.app Y
  let e₁ := serreHomEquiv k S X Y
  let e₂ := S.pairing Z X
  let e₃ : (X ⟶ S.equivalence.functor.obj Z) ≃ₗ[k] (X ⟶ Y) :=
    postcompIsoEquiv (k := k) c
  exact (((S.pairing X Y).trans e₁.symm.dualMap).trans e₂.symm.dualMap).trans
    (e₃.symm.dualMap).symm.dualMap

private lemma finiteDimensional_of_bidualEquiv
    (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]
    (e : V ≃ₗ[k] Module.Dual k (Module.Dual k V)) : FiniteDimensional k V := by
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  by_contra! h
  have h₁ : Cardinal.lift.{u, v} (Module.rank k V) < Module.rank k (Module.Dual k V) :=
    lift_rank_lt_rank_dual h
  have h₂ : Module.rank k (Module.Dual k V) <
      Module.rank k (Module.Dual k (Module.Dual k V)) := by
    convert! lift_rank_lt_rank_dual <|
      le_trans (by simpa) h₁.le
    rw [Cardinal.lift_id']
  have h₃ := lt_trans h₁ h₂
  have heq := e.lift_rank_eq
  rw [← Cardinal.lift_umax, heq, Cardinal.lift_id'] at h₃
  exact (lt_irrefl _ h₃)

private lemma serreHom_finiteDimensional
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] (S : SerreEquivalence k (C := C)) (X Y : C) :
    FiniteDimensional k (X ⟶ Y) :=
  finiteDimensional_of_bidualEquiv k (X ⟶ Y) (serreHomBidualEquiv k S X Y)

/-- The Serre pairing, together with reflexivity of finite-dimensional Hom spaces,
identifies the dual of a Hom space with the opposite Hom space into the Serre image. -/
private noncomputable def serreDualHomEquiv
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] (S : SerreEquivalence k (C := C)) (X Y : C) :
    Module.Dual k (X ⟶ Y) ≃ₗ[k] (Y ⟶ S.equivalence.functor.obj X) := by
  let V := Y ⟶ S.equivalence.functor.obj X
  let : FiniteDimensional k V := serreHom_finiteDimensional k S Y
    (S.equivalence.functor.obj X)
  exact (S.pairing X Y).symm.dualMap.trans (Module.evalEquiv k V).symm

private lemma serreDualHomEquiv_pairing
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] (S : SerreEquivalence k (C := C)) {X Y : C}
    (ψ : Module.Dual k (X ⟶ Y)) (f : X ⟶ Y) :
    S.pairing X Y f (serreDualHomEquiv k S X Y ψ) = ψ f := by
  let V := Y ⟶ S.equivalence.functor.obj X
  let : FiniteDimensional k V := serreHom_finiteDimensional k S Y
    (S.equivalence.functor.obj X)
  simp [serreDualHomEquiv]

private lemma serreDualHomEquiv_naturality_left
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] (S : SerreEquivalence k (C := C))
    {X X' Y : C} (f : X ⟶ X') (ψ : Module.Dual k (X ⟶ Y)) :
    serreDualHomEquiv k S X' Y ((Linear.leftComp k Y f).dualMap ψ) =
      serreDualHomEquiv k S X Y ψ ≫ S.equivalence.functor.map f := by
  apply serrePairing_hom_ext k S
  intro g
  rw [serreDualHomEquiv_pairing, LinearMap.dualMap_apply, Linear.leftComp_apply]
  have he := congrArg (fun φ => φ (serreDualHomEquiv k S X Y ψ))
    (S.pairing_naturality_left f g)
  rw [LinearMap.dualMap_apply, serreDualHomEquiv_pairing] at he
  simpa [Linear.rightComp_apply] using he

private lemma serreDualHomEquiv_naturality_right
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] (S : SerreEquivalence k (C := C))
    {X Y Y' : C} (g : Y ⟶ Y') (ψ : Module.Dual k (X ⟶ Y')) :
    serreDualHomEquiv k S X Y ((Linear.rightComp k X g).dualMap ψ) =
      g ≫ serreDualHomEquiv k S X Y' ψ := by
  apply serrePairing_hom_ext k S
  intro f
  rw [serreDualHomEquiv_pairing, LinearMap.dualMap_apply, Linear.rightComp_apply]
  have he := congrArg (fun φ => φ (serreDualHomEquiv k S X Y' ψ))
    (S.pairing_naturality_right f g)
  rw [LinearMap.dualMap_apply, serreDualHomEquiv_pairing] at he
  simpa [Linear.leftComp_apply] using he

private lemma dualMap_exact_of_exact
    (k : Type u) [Field k] (U V W : Type v)
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff] at h ⊢
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, h]

private lemma serreImage_yoneda_exact₂
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] [Limits.HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : SerreEquivalence k (C := C))
    (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) (X : C) :
    Function.Exact
      (Linear.rightComp k X (S.equivalence.functor.map T.mor₁))
      (Linear.rightComp k X (S.equivalence.functor.map T.mor₂)) := by
  let d₁ := Linear.leftComp k X T.mor₁
  let d₂ := Linear.leftComp k X T.mor₂
  have hExact : Function.Exact d₂ d₁ := by
    intro f
    constructor
    · intro hf
      obtain ⟨g, hg⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT f hf
      exact ⟨g, hg.symm⟩
    · rintro ⟨g, hg⟩
      rw [← hg]
      show T.mor₁ ≫ (T.mor₂ ≫ g) = 0
      rw [← Category.assoc,
        Pretriangulated.comp_distTriang_mor_zero₁₂ T hT]
      simp
  have hDual := dualMap_exact_of_exact k _ _ _ d₂ d₁ hExact
  let e₁ := serreDualHomEquiv k S T.obj₁ X
  let e₂ := serreDualHomEquiv k S T.obj₂ X
  let e₃ := serreDualHomEquiv k S T.obj₃ X
  intro z
  constructor
  · intro hz
    let ψ₂ := e₂.symm z
    have hz' : e₃ (d₂.dualMap ψ₂) = 0 := by
      calc
        e₃ (d₂.dualMap ψ₂) = e₂ ψ₂ ≫ S.equivalence.functor.map T.mor₂ :=
          serreDualHomEquiv_naturality_left k S T.mor₂ ψ₂
        _ = 0 := by simpa [ψ₂] using hz
    have hψ₂ : d₂.dualMap ψ₂ = 0 := e₃.injective (by simpa using hz')
    obtain ⟨ψ₁, hψ₁⟩ := (hDual ψ₂).mp hψ₂
    refine ⟨e₁ ψ₁, ?_⟩
    calc
      e₁ ψ₁ ≫ S.equivalence.functor.map T.mor₁ = e₂ (d₁.dualMap ψ₁) := by
        symm
        exact serreDualHomEquiv_naturality_left k S T.mor₁ ψ₁
      _ = e₂ ψ₂ := by rw [hψ₁]
      _ = z := e₂.apply_symm_apply z
  · rintro ⟨w, rfl⟩
    simp only [Linear.rightComp_apply]
    rw [Category.assoc, ← S.equivalence.functor.map_comp,
      Pretriangulated.comp_distTriang_mor_zero₁₂ T hT]
    simp

private lemma serreImage_exists_middle_map
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] [Limits.HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : SerreEquivalence k (C := C))
    (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C)
    (δ : S.equivalence.functor.obj (T.obj₁⟦(1 : ℤ)⟧) ≅
      (S.equivalence.functor.obj T.obj₁)⟦(1 : ℤ)⟧)
    (hδ : ∀ a : T.obj₁ ⟶ S.equivalence.functor.obj T.obj₁,
      serreTrace k S (T.obj₁⟦(1 : ℤ)⟧) (a⟦(1 : ℤ)⟧' ≫ δ.inv) =
        -serreTrace k S T.obj₁ a)
    {E : C} (i : S.equivalence.functor.obj T.obj₁ ⟶ E)
    (p : E ⟶ S.equivalence.functor.obj T.obj₃)
    (hU : Pretriangulated.Triangle.mk i p
      (S.equivalence.functor.map T.mor₃ ≫ δ.hom) ∈ distTriang C) :
    ∃ φ : E ⟶ S.equivalence.functor.obj T.obj₂,
      i ≫ φ = S.equivalence.functor.map T.mor₁ ∧
      φ ≫ S.equivalence.functor.map T.mor₂ = p := by
  let d : ((T.obj₂ ⟶ S.equivalence.functor.obj T.obj₁) × (T.obj₃ ⟶ E)) →ₗ[k]
      (T.obj₂ ⟶ E) :=
    (Linear.rightComp k T.obj₂ i).coprod (Linear.leftComp k E T.mor₂)
  let τ : Module.Dual k
      ((T.obj₂ ⟶ S.equivalence.functor.obj T.obj₁) × (T.obj₃ ⟶ E)) :=
    ((serreTrace k S T.obj₁).comp (Linear.leftComp k _ T.mor₁)).coprod
      ((serreTrace k S T.obj₃).comp (Linear.rightComp k _ p))
  have hτ : τ ∈ LinearMap.range d.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro z hz
    obtain ⟨a, b⟩ := z
    change a ≫ i + T.mor₂ ≫ b = 0 at hz
    obtain ⟨c, hc₁, hc₂⟩ := Pretriangulated.complete_distinguished_triangle_morphism
      T.rotate (Pretriangulated.Triangle.mk i p
        (S.equivalence.functor.map T.mor₃ ≫ δ.hom))
      (Pretriangulated.rot_of_distTriang T hT) hU a (-b) (by
        show T.mor₂ ≫ (-b) = a ≫ i
        rw [Preadditive.comp_neg]
        exact (eq_neg_of_add_eq_zero_left hz).symm)
    change T.obj₁⟦(1 : ℤ)⟧ ⟶ S.equivalence.functor.obj T.obj₃ at c
    change T.mor₃ ≫ c = (-b) ≫ p at hc₁
    change (-T.mor₁⟦(1 : ℤ)⟧') ≫ a⟦(1 : ℤ)⟧' =
      c ≫ (S.equivalence.functor.map T.mor₃ ≫ δ.hom) at hc₂
    have hc : c ≫ S.equivalence.functor.map T.mor₃ =
        -(T.mor₁ ≫ a)⟦(1 : ℤ)⟧' ≫ δ.inv := by
      rw [← cancel_mono δ.hom]
      simpa [Functor.map_comp, Category.assoc] using hc₂.symm
    show serreTrace k S T.obj₁ (T.mor₁ ≫ a) +
      serreTrace k S T.obj₃ (b ≫ p) = 0
    have hb : b ≫ p = -(T.mor₃ ≫ c) := by
      simpa using congrArg Neg.neg hc₁.symm
    rw [hb, map_neg, ← serreTrace_cyclic k S T.mor₃ c, hc, map_neg, hδ]
    simp
  obtain ⟨ψ, hψ⟩ := hτ
  refine ⟨serreDualHomEquiv k S T.obj₂ E ψ, ?_, ?_⟩
  · apply serrePairing_hom_ext k S
    intro a
    rw [← serreDualHomEquiv_naturality_right, serreDualHomEquiv_pairing]
    have he := LinearMap.congr_fun hψ (a, 0)
    show ψ (a ≫ i) = S.pairing T.obj₂ (S.equivalence.functor.obj T.obj₁) a
      (S.equivalence.functor.map T.mor₁)
    calc
      ψ (a ≫ i) = serreTrace k S T.obj₁ (T.mor₁ ≫ a) := by
        simpa [d, τ] using he
      _ = serreTrace k S T.obj₂ (a ≫ S.equivalence.functor.map T.mor₁) :=
        (serreTrace_cyclic k S T.mor₁ a).symm
      _ = _ := serreTrace_comp k S a _
  · apply serrePairing_hom_ext k S
    intro b
    rw [← serreDualHomEquiv_naturality_left, serreDualHomEquiv_pairing]
    have he := LinearMap.congr_fun hψ (0, b)
    simpa [d, τ, LinearMap.dualMap_apply, Linear.leftComp_apply,
      Linear.rightComp_apply, serreTrace_comp] using he

private lemma triangle_exact₂_of_iso
    {C : Type v} [Category.{w} C] [Preadditive C] [HasShift C ℤ]
    {T T' : Pretriangulated.Triangle C} (e : T ≅ T')
    (hT : ∀ (X : C) (f : X ⟶ T.obj₂), f ≫ T.mor₂ = 0 →
      ∃ g : X ⟶ T.obj₁, g ≫ T.mor₁ = f)
    (X : C) (f : X ⟶ T'.obj₂) (hf : f ≫ T'.mor₂ = 0) :
    ∃ g : X ⟶ T'.obj₁, g ≫ T'.mor₁ = f := by
  obtain ⟨g, hg⟩ := hT X (f ≫ e.inv.hom₂) (by
    rw [Category.assoc, ← e.inv.comm₂, ← Category.assoc, hf, zero_comp])
  refine ⟨g ≫ e.hom.hom₁, ?_⟩
  rw [Category.assoc, ← e.hom.comm₁, ← Category.assoc, hg]
  simp

/-- A morphism of distinguished triangles whose outer two components are isomorphisms has a
monomorphism in the middle, given the two exactness statements for the target triangle. -/
private lemma mono_hom₂_of_exact_of_isIso₁₃
    {C : Type v} [Category.{w} C] [Preadditive C] [Limits.HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T T' : Pretriangulated.Triangle C} (φ : T ⟶ T') (hT : T ∈ distTriang C)
    (hex' : ∀ (X : C) (f : X ⟶ T'.invRotate.obj₂),
      f ≫ T'.invRotate.mor₂ = 0 →
      ∃ g : X ⟶ T'.invRotate.obj₁, g ≫ T'.invRotate.mor₁ = f)
    [IsIso φ.hom₁] [IsIso φ.hom₃] : Mono φ.hom₂ := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro A f hf
  obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ hT f
    (by rw [← cancel_mono φ.hom₃, Category.assoc, φ.comm₂,
      reassoc_of% hf, zero_comp, zero_comp])
  rw [Category.assoc] at hf
  obtain ⟨h, hh⟩ := hex' A (g ≫ φ.hom₁)
    (show (g ≫ φ.hom₁) ≫ T'.mor₁ = 0 by rw [Category.assoc, ← φ.comm₁]; exact hf)
  obtain ⟨l, rfl⟩ : ∃ l : A ⟶ T.invRotate.obj₁, l ≫ T.invRotate.mor₁ = g := by
    show ∃ l : A ⟶ T.obj₃⟦(-1 : ℤ)⟧, l ≫ T.invRotate.mor₁ = g
    change A ⟶ T'.obj₃⟦(-1 : ℤ)⟧ at h
    let e := (shiftFunctor C (-1)).mapIso (asIso φ.hom₃)
    refine ⟨h ≫ e.inv, ?_⟩
    have eq := ((Pretriangulated.invRotate C).map φ).comm₁
    dsimp only [Pretriangulated.invRotate,
      Pretriangulated.Triangle.invRotate, Pretriangulated.Triangle.mk] at eq hh ⊢
    rw [← cancel_mono φ.hom₁, Category.assoc, Category.assoc, eq]
    simpa [e, Category.assoc] using hh
  show (l ≫ T.invRotate.mor₁) ≫ T.invRotate.mor₂ = 0
  rw [Category.assoc, Pretriangulated.comp_distTriang_mor_zero₁₂ _
    (Pretriangulated.inv_rot_of_distTriang _ hT), comp_zero]

private lemma isIso₂_of_exact_of_isIso₁₃
    {C : Type v} [Category.{w} C] [Preadditive C] [Limits.HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T T' : Pretriangulated.Triangle C} (φ : T ⟶ T') (hT : T ∈ distTriang C)
    (hex : ∀ (X : C) (f : X ⟶ T'.obj₂), f ≫ T'.mor₂ = 0 →
      ∃ g : X ⟶ T'.obj₁, g ≫ T'.mor₁ = f)
    (hex' : ∀ (X : C) (f : X ⟶ T'.invRotate.obj₂),
      f ≫ T'.invRotate.mor₂ = 0 →
      ∃ g : X ⟶ T'.invRotate.obj₁, g ≫ T'.invRotate.mor₁ = f)
    (hz : T'.mor₂ ≫ T'.mor₃ = 0)
    [IsIso φ.hom₁] [IsIso φ.hom₃] : IsIso φ.hom₂ := by
  have : Mono φ.hom₂ := mono_hom₂_of_exact_of_isIso₁₃ φ hT hex'
  refine isIso_of_yoneda_map_bijective _ (fun A => ⟨?_, ?_⟩)
  · intro f₁ f₂ h
    simpa only [← cancel_mono φ.hom₂] using h
  · intro y₂
    obtain ⟨x₃, hx₃⟩ : ∃ x₃ : A ⟶ T.obj₃, x₃ ≫ φ.hom₃ = y₂ ≫ T'.mor₂ :=
      ⟨y₂ ≫ T'.mor₂ ≫ inv φ.hom₃, by simp⟩
    obtain ⟨x₂, hx₂⟩ := Pretriangulated.Triangle.coyoneda_exact₃ _ hT x₃ (by
      rw [← cancel_mono (φ.hom₁⟦(1 : ℤ)⟧'), Category.assoc, zero_comp, φ.comm₃,
        reassoc_of% hx₃, hz, comp_zero])
    obtain ⟨y₁, hy₁⟩ := hex A (y₂ - x₂ ≫ φ.hom₂) (by
      rw [Preadditive.sub_comp, Category.assoc, ← φ.comm₂,
        ← reassoc_of% hx₂, hx₃, sub_self])
    refine ⟨x₂ + (y₁ ≫ inv φ.hom₁) ≫ T.mor₁, ?_⟩
    dsimp
    rw [Preadditive.add_comp, Category.assoc, φ.comm₁]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, hy₁, add_sub_cancel]

private lemma serreImage_exact₂
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] [Limits.HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : SerreEquivalence k (C := C)) [S.equivalence.functor.CommShift ℤ]
    (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C)
    (X : C) (f : X ⟶ (S.equivalence.functor.mapTriangle.obj T).obj₂)
    (hf : f ≫ (S.equivalence.functor.mapTriangle.obj T).mor₂ = 0) :
    ∃ g : X ⟶ (S.equivalence.functor.mapTriangle.obj T).obj₁,
      g ≫ (S.equivalence.functor.mapTriangle.obj T).mor₁ = f :=
  (serreImage_yoneda_exact₂ k S T hT X f).mp hf

private lemma serreFunctor_isTriangulated_of_trace
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] [Limits.HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : SerreEquivalence k (C := C)) [S.equivalence.functor.CommShift ℤ]
    (hδ : ∀ (X : C) (a : X ⟶ S.equivalence.functor.obj X),
      serreTrace k S (X⟦(1 : ℤ)⟧)
          (a⟦(1 : ℤ)⟧' ≫ (S.equivalence.functor.commShiftIso (1 : ℤ)).inv.app X) =
        -serreTrace k S X a) : S.equivalence.functor.IsTriangulated := by
  let : S.equivalence.functor.Additive := ⟨fun {_ _ f g} => serreFunctor_map_add k S f g⟩
  constructor
  intro T hT
  let F := S.equivalence.functor
  let V := F.mapTriangle.obj T
  obtain ⟨E, i, p, hU⟩ := Pretriangulated.distinguished_cocone_triangle₂ V.mor₃
  obtain ⟨φ, hφ₁, hφ₂⟩ := serreImage_exists_middle_map k S T hT
    ((F.commShiftIso (1 : ℤ)).app T.obj₁) (hδ T.obj₁) i p hU
  let U := Pretriangulated.Triangle.mk i p V.mor₃
  let ψ : U ⟶ V := Pretriangulated.Triangle.homMk _ _ (𝟙 _) φ (𝟙 _)
    (by simpa [U, V, F, Functor.mapTriangle, Pretriangulated.Triangle.mk] using hφ₁)
    (show p ≫ 𝟙 _ = φ ≫ F.map T.mor₂ by rw [Category.comp_id]; exact hφ₂.symm)
    (by simp [U])
  have : IsIso ψ.hom₁ := by change IsIso (𝟙 _); infer_instance
  have : IsIso ψ.hom₃ := by change IsIso (𝟙 _); infer_instance
  have : IsIso ψ.hom₂ := isIso₂_of_exact_of_isIso₁₃ ψ hU
    (serreImage_exact₂ k S T hT)
    (triangle_exact₂_of_iso (F.mapTriangleInvRotateIso.app T).symm
      (serreImage_exact₂ k S T.invRotate
        (Pretriangulated.inv_rot_of_distTriang T hT)))
    (show F.map T.mor₂ ≫ (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) = 0 by
      rw [← Category.assoc, ← F.map_comp,
        Pretriangulated.comp_distTriang_mor_zero₂₃ T hT, F.map_zero, zero_comp])
  have : IsIso ψ := Pretriangulated.Triangle.isIso_of_isIsos ψ
    inferInstance inferInstance inferInstance
  exact Pretriangulated.isomorphic_distinguished U hU V (asIso ψ).symm

private noncomputable def functorHomLinearEquiv
    (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
    [Linear k C] (F : C ⥤ C) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
    (X Y : C) : (X ⟶ Y) ≃ₗ[k] (F.obj X ⟶ F.obj Y) :=
  LinearEquiv.ofBijective (F.mapLinearMap k) ⟨F.map_injective, F.map_surjective⟩

section LinearShift

variable (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C]
  [Linear k C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]
  (S : SerreEquivalence k (C := C))

private noncomputable def serreShiftHom (n : ℤ) (X : C) :
    (S.equivalence.functor.obj X)⟦n⟧ ⟶ S.equivalence.functor.obj (X⟦n⟧) :=
  serreDualHomEquiv k S (X⟦n⟧) ((S.equivalence.functor.obj X)⟦n⟧)
    (n.negOnePow • (serreTrace k S X).comp
      (functorHomLinearEquiv k (shiftFunctor C n) X
        (S.equivalence.functor.obj X)).symm.toLinearMap)

private lemma serreShiftHom_trace (n : ℤ) (X : C)
    (a : X ⟶ S.equivalence.functor.obj X) :
    serreTrace k S (X⟦n⟧) (a⟦n⟧' ≫ serreShiftHom k S n X) =
      n.negOnePow • serreTrace k S X a := by
  rw [serreTrace_comp, serreShiftHom, serreDualHomEquiv_pairing]
  show n.negOnePow • serreTrace k S X
    ((functorHomLinearEquiv k (shiftFunctor C n) X _).symm
      ((functorHomLinearEquiv k (shiftFunctor C n) X _) a)) = _
  rw [LinearEquiv.symm_apply_apply]

private lemma serreShiftHom_pairing (n : ℤ) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ S.equivalence.functor.obj X) :
    S.pairing (X⟦n⟧) (Y⟦n⟧) (f⟦n⟧') (g⟦n⟧' ≫ serreShiftHom k S n X) =
      n.negOnePow • S.pairing X Y f g := by
  rw [← serreTrace_comp, ← Category.assoc, ← Functor.map_comp,
    serreShiftHom_trace, serreTrace_comp]

private lemma serreShiftHom_naturality (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (S.equivalence.functor.map f)⟦n⟧' ≫ serreShiftHom k S n Y =
      serreShiftHom k S n X ≫ S.equivalence.functor.map (f⟦n⟧') := by
  apply serrePairing_hom_ext k S
  intro b
  obtain ⟨g, rfl⟩ := (shiftFunctor C n).map_surjective b
  rw [serreShiftHom_pairing]
  have h := congrArg (fun ψ => ψ (serreShiftHom k S n X))
    (S.pairing_naturality_left (f⟦n⟧') (g⟦n⟧'))
  simp only [LinearMap.dualMap_apply, Linear.rightComp_apply] at h
  rw [← h, ← Functor.map_comp]
  rw [← serreTrace_comp k S ((f ≫ g)⟦n⟧') _, serreShiftHom_trace,
    ← serreTrace_comp k S g _, serreTrace_cyclic]

private lemma serreShiftHom_unique (n : ℤ) (X : C)
    (c : (S.equivalence.functor.obj X)⟦n⟧ ⟶ S.equivalence.functor.obj (X⟦n⟧))
    (hc : ∀ a : X ⟶ S.equivalence.functor.obj X,
      serreTrace k S (X⟦n⟧) (a⟦n⟧' ≫ c) = n.negOnePow • serreTrace k S X a) :
    c = serreShiftHom k S n X := by
  apply serrePairing_hom_ext k S
  intro a
  obtain ⟨b, rfl⟩ := (shiftFunctor C n).map_surjective a
  rw [← serreTrace_comp, ← serreTrace_comp, hc, serreShiftHom_trace]

private lemma serreShiftHom_isIso (n : ℤ) (X : C) :
    IsIso (serreShiftHom k S n X) := by
  have hb (Y : C) : Function.Bijective
      (fun f : Y⟦n⟧ ⟶ (S.equivalence.functor.obj X)⟦n⟧ =>
        f ≫ serreShiftHom k S n X) := by
    let e := ((functorHomLinearEquiv k (shiftFunctor C n) Y _).symm.trans
      (serreDualHomEquiv k S X Y).symm).trans
        ((functorHomLinearEquiv k (shiftFunctor C n) X Y).symm.dualMap.trans
          (serreDualHomEquiv k S (X⟦n⟧) (Y⟦n⟧)))
    let e' := e.toEquiv.trans (DistribMulAction.toAddEquiv _ n.negOnePow).toEquiv
    have he (f : Y⟦n⟧ ⟶ (S.equivalence.functor.obj X)⟦n⟧) :
        f ≫ serreShiftHom k S n X = e' f := by
      obtain ⟨g, rfl⟩ := (shiftFunctor C n).map_surjective f
      apply serrePairing_hom_ext k S
      intro a
      obtain ⟨b, rfl⟩ := (shiftFunctor C n).map_surjective a
      rw [serreShiftHom_pairing]
      dsimp [e', e]
      simp only [DistribMulAction.toAddEquiv_apply, Units.smul_def, map_zsmul,
        serreDualHomEquiv_pairing]
      show _ = n.negOnePow •
        (serreDualHomEquiv k S X Y).symm
          ((functorHomLinearEquiv k (shiftFunctor C n) Y _).symm
            ((functorHomLinearEquiv k (shiftFunctor C n) Y _) g))
          ((functorHomLinearEquiv k (shiftFunctor C n) X Y).symm
            ((functorHomLinearEquiv k (shiftFunctor C n) X Y) b))
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      conv_lhs => rw [← (serreDualHomEquiv k S X Y).apply_symm_apply g]
      rw [serreDualHomEquiv_pairing]
      simp only [Units.smul_def]
    simpa only [he] using e'.bijective
  apply isIso_of_yoneda_map_bijective
  intro Y
  let e := (shiftFunctor C n).objObjPreimageIso Y
  constructor
  · intro f g h
    have he := (hb ((shiftFunctor C n).objPreimage Y)).injective
      (show (e.hom ≫ f) ≫ serreShiftHom k S n X =
        (e.hom ≫ g) ≫ serreShiftHom k S n X by simpa only [Category.assoc] using
          (congrArg (fun q => e.hom ≫ q) h))
    exact (cancel_epi e.hom).mp he
  · intro f
    obtain ⟨g, hg⟩ := (hb ((shiftFunctor C n).objPreimage Y)).surjective (e.hom ≫ f)
    exact ⟨e.inv ≫ g, by simpa [Category.assoc] using congrArg (fun q => e.inv ≫ q) hg⟩

private noncomputable def serreShiftIso (n : ℤ) :
    shiftFunctor C n ⋙ S.equivalence.functor ≅
      S.equivalence.functor ⋙ shiftFunctor C n := by
  let (X : C) : IsIso (serreShiftHom k S n X) := serreShiftHom_isIso k S n X
  exact (NatIso.ofComponents (fun X => asIso (serreShiftHom k S n X))
    (fun f => serreShiftHom_naturality k S n f)).symm

private lemma serreShiftIso_inv_app (n : ℤ) (X : C) :
    (serreShiftIso k S n).inv.app X = serreShiftHom k S n X := rfl

private lemma serreShiftIso_zero :
    serreShiftIso k S 0 = Functor.CommShift.isoZero S.equivalence.functor ℤ := by
  apply Iso.ext_inv
  ext X
  show serreShiftHom k S 0 X =
    (Functor.CommShift.isoZero S.equivalence.functor ℤ).inv.app X
  symm
  apply serreShiftHom_unique k S 0 X
  intro a
  simp only [Functor.CommShift.isoZero_inv_app, Int.negOnePow_zero, one_smul]
  rw [← Category.assoc, serreTrace_cyclic]
  have h := (shiftFunctorZero C ℤ).hom.naturality a
  dsimp at h
  simp only [h, Iso.inv_hom_id_app_assoc]

private lemma serreShiftIso_add (n m : ℤ) :
    serreShiftIso k S (n + m) =
      Functor.CommShift.isoAdd (serreShiftIso k S n) (serreShiftIso k S m) := by
  apply Iso.ext_inv
  ext X
  show serreShiftHom k S (n + m) X =
    (Functor.CommShift.isoAdd (serreShiftIso k S n) (serreShiftIso k S m)).inv.app X
  symm
  apply serreShiftHom_unique k S (n + m) X
  intro a
  rw [Functor.CommShift.isoAdd_inv_app]
  simp only [serreShiftIso_inv_app]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, serreTrace_cyclic]
  have h := (shiftFunctorAdd C n m).hom.naturality a
  dsimp at h
  simp only [Category.assoc]
  rw [reassoc_of% h, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, serreShiftHom_trace, serreShiftHom_trace,
    smul_smul, Int.negOnePow_add, mul_comm]

@[instance_reducible]
private noncomputable def serreCommShift : S.equivalence.functor.CommShift ℤ where
  commShiftIso := serreShiftIso k S
  commShiftIso_zero := serreShiftIso_zero k S
  commShiftIso_add := serreShiftIso_add k S

private lemma serreCommShift_trace (X : C) (a : X ⟶ S.equivalence.functor.obj X) :
    letI := serreCommShift k S
    serreTrace k S (X⟦(1 : ℤ)⟧)
      (a⟦(1 : ℤ)⟧' ≫ (S.equivalence.functor.commShiftIso (1 : ℤ)).inv.app X) =
      -serreTrace k S X a := by
  show serreTrace k S (X⟦(1 : ℤ)⟧) (a⟦(1 : ℤ)⟧' ≫ serreShiftHom k S 1 X) = _
  simpa [Units.smul_def] using serreShiftHom_trace k S 1 X a

end LinearShift

variable (k : Type u) [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
  [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k] [Pretriangulated C]

/-- **Stacks Project, Tag 0FY6.** A Serre equivalence has a coherent translation isomorphism
under which it is an exact functor of triangulated categories. -/
@[stacks 0FY6 "serre_functor_exact"]
theorem serreEquivalence_exists_isTriangulated
    (S : SerreEquivalence k (C := C)) :
    ∃ commShift : S.equivalence.functor.CommShift ℤ,
      letI := commShift
      S.equivalence.functor.IsTriangulated := by
  let : S.equivalence.functor.CommShift ℤ := serreCommShift k S
  exact ⟨serreCommShift k S,
    serreFunctor_isTriangulated_of_trace k S (serreCommShift_trace k S)⟩

end CategoryTheory
