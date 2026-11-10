module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBirational

/-!
# `γ_d : Hilb^d ⟶ P^d` is the Abel morphism into `Pic⁰`, up to translation

Let `P` represent `Pic_{X/k,σ}` and `A` represent `Pic⁰_{X/k,σ}`, and let `θ` be a class of degree
`d` on `X`. Translation by `θ^{-1}`, `ℒ ↦ ℒ ⊗ pr_X^*θ^{-1}` (normalised along `σ`), identifies
the degree-`d` component `P^d` with `A`, and carries `γ_d : Hilb^d ⟶ P^d` to the Abel morphism
`Hilb^d ⟶ A` of `Stacks.RigidifiedPicard.abelMorphism`. So properties of morphisms such as
smoothness pass from the latter to `γ_d` ([Stacks, Tag 0BA0] (5)).

## Main definitions

* `Stacks.RigidifiedPicard.degreeLocusTranslateIso`: the isomorphism `P^d ≅ A` given by
  translation by `θ^{-1}`.

## Main results

* `Stacks.RigidifiedPicard.abelMorphismDegree_comp_degreeLocusTranslateIso`: `γ_d` followed by
  `P^d ≅ A` is the Abel morphism `Hilb^d ⟶ A`.
* `Stacks.RigidifiedPicard.smooth_abelMorphismDegree_of_smooth_abelMorphism`: if the Abel
  morphism `Hilb^d ⟶ A` is smooth, then so is `γ_d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
  [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f]
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (P : Grp (Over (Spec (.of k))))
  (e : yonedaGrp.obj P ≅ functor f σ hσ) (θ : Stacks.Picard.ofScheme X) {d : ℕ}
  (hθ : ∀ s : Spec (.of k), relativeInvertibleDegreeHomAt f hdim s θ = d)

/-- Pullback of Picard classes along a morphism of schemes commutes with subtraction. -/
private theorem schemePullbackClass_sub {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (x y : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClass g (x - y) =
      Stacks.Picard.schemePullbackClass g x - Stacks.Picard.schemePullbackClass g y :=
  map_sub (Stacks.Picard.schemePullbackClassHom g) x y

/-- Pullback of Picard classes along a morphism of schemes commutes with negation. -/
private theorem schemePullbackClass_neg {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (x : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClass g (-x) = -Stacks.Picard.schemePullbackClass g x :=
  map_neg (Stacks.Picard.schemePullbackClassHom g) x

omit [IsProper f] [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- Normalisation along `σ` is additive: it commutes with subtraction of classes. -/
theorem normalize_sub (T : Over (Spec (.of k))) (c c' : Stacks.Picard.ofScheme (bc f T)) :
    normalize f σ hσ T (c - c') = normalize f σ hσ T c - normalize f σ hσ T c' := by
  rw [normalize, normalize, normalize, schemePullbackClass_sub, schemePullbackClass_sub]
  abel

omit [IsProper f] [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- Normalising `normalize c - c'` along `σ` gives the normalisation of `c - c'`. -/
theorem normalize_normalize_sub (T : Over (Spec (.of k))) (c c' : Stacks.Picard.ofScheme (bc f T)) :
    normalize f σ hσ T (normalize f σ hσ T c - c') = normalize f σ hσ T (c - c') := by
  have h : normalize f σ hσ T c - c' = (c - c') + Stacks.Picard.schemePullbackClass (bcProj f T)
      (-Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c) := by
    rw [schemePullbackClass_neg, normalize]
    abel
  rw [h, normalize_add_bcProj]

/-- The class `ℒ ⊗ pr_X^*θ^{-1}`, normalised along `σ`, of a `T`-point of `P^d`. -/
def translateClass {T : Over (Spec (.of k))} (a : T ⟶ degreeLocusOver f hdim σ hσ P e d) :
    Stacks.Picard.ofScheme (bc f T) :=
  normalize f σ hσ T (classOfElt f σ hσ (homElt f σ hσ P e (a ≫ degreeLocusι f hdim σ hσ P e d)) -
    Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ)

omit [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
include hθ in
/-- The class `translateClass θ a` has degree `0` on every fibre of `X_T ⟶ T`. -/
theorem degree_translateClass {T : Over (Spec (.of k))}
    (a : T ⟶ degreeLocusOver f hdim σ hσ P e d) (t : T.left) :
    relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
      (translateClass f hdim σ hσ P e θ a) = 0 := by
  rw [translateClass, normalize, map_sub, relativeInvertibleDegreeHomAt_bcProj f hdim T t,
    sub_zero, map_sub, relativeInvertibleDegreeHomAt_fst f hdim θ T t, hθ,
    degree_of_degreeLocus f hdim σ hσ P e d a t, sub_self]

/-- The element of `Pic⁰_{X/k,σ}(T)` attached to a `T`-point of `P^d` by translation by
`θ^{-1}`. -/
def translateElt {T : Over (Spec (.of k))} (a : T ⟶ degreeLocusOver f hdim σ hσ P e d) :
    (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T) :=
  mkZero f hdim σ hσ (translateClass f hdim σ hσ P e θ a)
    (schemePullbackClass_bcSection_normalize f σ hσ T _)
    (degree_translateClass f hdim σ hσ P e θ hθ a)

omit [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- The class underlying `translateElt θ a` is `translateClass θ a`. -/
theorem smallEquiv_translateElt {T : Over (Spec (.of k))}
    (a : T ⟶ degreeLocusOver f hdim σ hσ P e d) :
    smallEquiv _ ((((Multiplicative.toAdd (translateElt f hdim σ hσ P e θ hθ a) :
      groupZero f hdim σ hσ T) : group f σ hσ T)) : Stacks.Picard.smallOfScheme (bc f T)) =
      translateClass f hdim σ hσ P e θ a :=
  smallEquiv_mkZero _ _ _ _ _ _ _

omit [IsProper f] [Smooth f] [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- The class attached to a `T`-point of `Pic_{X/k,σ}` pulls back to `0` along the section
`σ_T : T ⟶ X_T`. -/
theorem rigid_classOfElt {T : Over (Spec (.of k))}
    (x : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) :
    Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) (classOfElt f σ hσ x) = 0 :=
  (mem_group_iff f σ hσ T _).1 (Multiplicative.toAdd x : group f σ hσ T).2

omit [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- Translation by `θ^{-1}` is a bijection from the `T`-points of `P^d` to
`Pic⁰_{X/k,σ}(T)`. -/
theorem translateElt_bijective {T : Over (Spec (.of k))} :
    Function.Bijective (translateElt f hdim σ hσ P e θ hθ (T := T)) := by
  refine ⟨fun a a' h => ?_, fun z => ?_⟩
  · have hc := congrArg (fun z : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T) =>
      smallEquiv _ ((((Multiplicative.toAdd z : groupZero f hdim σ hσ T) : group f σ hσ T)) :
        Stacks.Picard.smallOfScheme (bc f T))) h
    simp only [smallEquiv_translateElt, translateClass] at hc
    rw [← sub_eq_zero, ← normalize_sub, sub_sub_sub_cancel_right,
      normalize_eq_self f σ hσ T _
        ((map_sub (Stacks.Picard.schemePullbackClassHom (bcSection f σ hσ T)) _ _).trans
          (sub_eq_zero.2 ((rigid_classOfElt f σ hσ _).trans (rigid_classOfElt f σ hσ _).symm))),
      sub_eq_zero] at hc
    exact Over.OverMorphism.ext <| (cancel_mono (degreeLocus f hdim σ hσ P e d).ι).1 <|
      congrArg CommaMorphism.left (homElt_injective f σ hσ P e (ext_functor f σ hσ hc))
  · set b : Stacks.Picard.ofScheme (bc f T) := smallEquiv _ ((((Multiplicative.toAdd z :
      groupZero f hdim σ hσ T) : group f σ hσ T)) : Stacks.Picard.smallOfScheme (bc f T))
    have hb : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) b = 0 :=
      (mem_group_iff f σ hσ T _).1 ((Multiplicative.toAdd z : groupZero f hdim σ hσ T) :
        group f σ hσ T).2
    have hb0 : ∀ t, relativeInvertibleDegreeHomAt (bcProj f T)
        (topologicalKrullDim_fiber_bcProj_le f hdim T) t b = 0 := fun t => by
      have h := (mem_groupZero_iff f hdim σ hσ T _).1 (Multiplicative.toAdd z).2 t
      rwa [degree_apply] at h
    obtain ⟨c, hcdef⟩ : ∃ c, c = normalize f σ hσ T
        (b + Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ) := ⟨_, rfl⟩
    have hc : Stacks.Picard.schemePullbackClass (bcSection f σ hσ T) c = 0 :=
      hcdef ▸ schemePullbackClass_bcSection_normalize f σ hσ T _
    obtain ⟨a, ha⟩ := exists_lift_degreeLocus f hdim σ hσ P e
      (eltHom f σ hσ P e (mkElt f σ hσ c hc)) d fun t => by
        rw [hom_app_inv_app, classOfElt_mkElt, hcdef, normalize, map_sub,
          relativeInvertibleDegreeHomAt_bcProj f hdim T t, sub_zero, map_add, hb0,
          relativeInvertibleDegreeHomAt_fst f hdim θ T t, hθ, zero_add]
    refine ⟨a, ext_functorZero f hdim σ hσ ?_⟩
    rw [smallEquiv_translateElt, translateClass, ha, homElt_eltHom, classOfElt_mkElt, hcdef,
      normalize_normalize_sub, add_sub_cancel_right, normalize_eq_self f σ hσ T b hb]

omit [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- Translation by `θ^{-1}` is natural in `T`: it commutes with base change along `g : T' ⟶ T`. -/
theorem translateElt_comp {T T' : Over (Spec (.of k))} (g : T' ⟶ T)
    (a : T ⟶ degreeLocusOver f hdim σ hσ P e d) :
    translateElt f hdim σ hσ P e θ hθ (g ≫ a) =
      (functorZero f hdim σ hσ ⋙ forget GrpCat).map g.op (translateElt f hdim σ hσ P e θ hθ a) := by
  refine ext_functorZero f hdim σ hσ ?_
  rw [functorZero_map_val, smallEquiv_translateElt, smallEquiv_translateElt, translateClass,
    translateClass, normalize_bcMap,
    schemePullbackClass_sub,
    Stacks.Picard.schemePullbackClass_comp, bcMap_fst,
    Category.assoc, homElt_comp]
  congr 2
  exact functor_map_val f σ hσ g _

/-- **`P^d` represents `Pic⁰_{X/k,σ}`, through translation by `θ^{-1}`.** -/
def degreeLocusTranslateRepresentableBy :
    (functorZero f hdim σ hσ ⋙ forget GrpCat).RepresentableBy
      (degreeLocusOver f hdim σ hσ P e d) where
  homEquiv := Equiv.ofBijective _ (translateElt_bijective f hdim σ hσ P e θ hθ)
  homEquiv_comp g a := translateElt_comp f hdim σ hσ P e θ hθ g a

section Iso

variable (A : Grp (Over (Spec (.of k)))) (eA : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)

/-- **`P^d ≅ A` over `k`**, through translation by `θ^{-1}`. -/
def degreeLocusTranslateIso : degreeLocusOver f hdim σ hσ P e d ≅ A.X :=
  Yoneda.fullyFaithful.preimageIso
    (Functor.representableByEquiv (degreeLocusTranslateRepresentableBy f hdim σ hσ P e θ hθ) ≪≫
      (representingIsoOfGrp A eA).symm)

omit [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
/-- Under `eA`, the composite of a `T`-point `a` of `P^d` with `P^d ≅ A` is `translateElt θ a`. -/
theorem hom_app_comp_degreeLocusTranslateIso {T : Over (Spec (.of k))}
    (a : T ⟶ degreeLocusOver f hdim σ hσ P e d) :
    (eA.hom.app (op T)).hom (a ≫ (degreeLocusTranslateIso f hdim σ hσ P e θ hθ A eA).hom) =
      translateElt f hdim σ hσ P e θ hθ a := by
  have h1 : yoneda.map (degreeLocusTranslateIso f hdim σ hσ P e θ hθ A eA).hom =
      (Functor.representableByEquiv (degreeLocusTranslateRepresentableBy f hdim σ hσ P e θ hθ) ≪≫
        (representingIsoOfGrp A eA).symm).hom :=
    Yoneda.fullyFaithful.map_preimage _
  have h2 : a ≫ (degreeLocusTranslateIso f hdim σ hσ P e θ hθ A eA).hom =
      (representingIsoOfGrp A eA).inv.app (op T)
        ((degreeLocusTranslateRepresentableBy f hdim σ hσ P e θ hθ).homEquiv a) :=
    congrArg (fun φ => φ.app (op T) a) h1
  change (representingIsoOfGrp A eA).hom.app (op T) _ = _
  rw [h2]
  exact congrArg (fun φ => φ.app (op T)
    ((degreeLocusTranslateRepresentableBy f hdim σ hσ P e θ hθ).homEquiv a))
    (representingIsoOfGrp A eA).inv_hom_id

variable {H : Over (Spec (.of k))}
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)

omit [GeometricallyIrreducible f] in
/-- **`γ_d` followed by `P^d ≅ A` is the Abel morphism into `Pic⁰`.** -/
theorem abelMorphismDegree_comp_degreeLocusTranslateIso :
    abelMorphismDegree f hdim σ hσ P e hH ≫
        (degreeLocusTranslateIso f hdim σ hσ P e θ hθ A eA).hom.left =
      (abelMorphism f hdim σ hσ θ hθ hH A eA).left := by
  let γo : H ⟶ degreeLocusOver f hdim σ hσ P e d :=
    Over.homMk (abelMorphismDegree f hdim σ hσ P e hH) (abelMorphismDegree_over f hdim σ hσ P e hH)
  have hγo : γo ≫ degreeLocusι f hdim σ hσ P e d = abelMorphismFull f σ hσ hH P e :=
    Over.OverMorphism.ext (abelMorphismDegree_ι f hdim σ hσ P e hH)
  have hinj : Function.Injective (eA.hom.app (op H)).hom :=
    Function.LeftInverse.injective (g := (eA.inv.app (op H)).hom) fun x => by
      change ((eA.hom ≫ eA.inv).app (op H)).hom x = x
      rw [eA.hom_inv_id]
      rfl
  have key : γo ≫ (degreeLocusTranslateIso f hdim σ hσ P e θ hθ A eA).hom =
      abelMorphism f hdim σ hσ θ hθ hH A eA := by
    refine hinj ?_
    rw [hom_app_comp_degreeLocusTranslateIso]
    have h1 := abelMorphism_spec f hdim σ hσ θ hθ hH A eA (𝟙 H)
    rw [Category.id_comp] at h1
    rw [h1]
    refine ext_functorZero f hdim σ hσ ?_
    rw [smallEquiv_translateElt, smallEquiv_abelElement, translateClass, hγo]
    have h2 := abelMorphismFull_spec f σ hσ hH P e (𝟙 H)
    rw [Category.id_comp] at h2
    change normalize f σ hσ H (classOfElt f σ hσ ((e.hom.app (op H)).hom _) - _) = _
    rw [h2, classOfElt, smallEquiv_abelElementFull, abelNormalized, normalize_normalize_sub,
      abelNormalized]
    congr 2
    rw [show Stacks.Picard.schemePullbackClass (pullback.fst f H.hom)
      (0 : Stacks.Picard.ofScheme X) = 0 from map_zero (Stacks.Picard.schemePullbackClassHom _),
      sub_zero]
  exact congrArg CommaMorphism.left key

omit [GeometricallyIrreducible f] in
/-- **Smoothness of `γ_d : Hilb^d ⟶ P^d` from smoothness of the Abel morphism into `Pic⁰`.** -/
theorem smooth_abelMorphismDegree_of_smooth_abelMorphism
    [Smooth (abelMorphism f hdim σ hσ θ hθ hH A eA).left] :
    Smooth (abelMorphismDegree f hdim σ hσ P e hH) := by
  have hiso : IsIso (degreeLocusTranslateIso f hdim σ hσ P e θ hθ A eA).hom.left :=
    (inferInstance : IsIso
      ((Over.forget _).map (degreeLocusTranslateIso f hdim σ hσ P e θ hθ A eA).hom))
  have h' : abelMorphismDegree f hdim σ hσ P e hH = (abelMorphism f hdim σ hσ θ hθ hH A eA).left ≫
      inv (degreeLocusTranslateIso f hdim σ hσ P e θ hθ A eA).hom.left := by
    rw [← abelMorphismDegree_comp_degreeLocusTranslateIso f hdim σ hσ P e θ hθ A eA hH,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h']
  infer_instance

end Iso

end Stacks.RigidifiedPicard

end
