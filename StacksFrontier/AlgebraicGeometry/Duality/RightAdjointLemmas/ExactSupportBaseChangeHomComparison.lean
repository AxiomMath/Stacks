module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility

/-!
# The base change map of `R ℰom(𝒪_Z, -)` against the hom-comparison, over abstract data

This file isolates the formal content of the identification, omitted in the source's proof of
[Stacks, Tag 0E2L], of the base change map of [Stacks, Tag 0E2K] with the internal-Hom base
change map of Cohomology, Remark [Stacks, Tag 08I3].  Everything here is stated for arbitrary
categories, functors and adjunctions; the geometric instance is
`…isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap`.

## The data

On one side there are a category `𝒳` (standing for `D(𝒪_X)`) and `𝒵` (for `D(𝒪_Z)`), a functor
`P : 𝒵 ⥤ 𝒳` (pushforward along the closed immersion) with a left adjoint `Li` (`q : Li ⊣ P`)
and a right adjoint `a` (`ex : P ⊣ a`, the adjunction of [Stacks, Tag 0A76]), a tensor product
`T` with internal hom `H` and tensor–hom bijections `e₁` natural in the source variable
([Stacks, Tag 08DI]), an object `E` (for `i_*𝒪_Z`) and a natural isomorphism
`π : W ⊗ E ≅ P (Li W)` (the projection formula of [Stacks, Tag 0B55] at `𝒪_Z`, followed by
the unitor).  The same data on a second side `𝒳'`, `𝒵'`, and functors `Lf : 𝒳 ⥤ 𝒳'`,
`Lg : 𝒵 ⥤ 𝒵'` with an identification `e : Lg ⋙ P' ≅ P ⋙ Lf` (the base change isomorphism of
[Stacks, Tag 0E23]) and a monoidality comparison `m` of `Lf` ([Stacks, Tag 079U]).

## Main definitions

* `Stacks.Duality.ExactSupportBaseChange.pushforwardRightAdjointToHom`: the map
  `P (a K) ⟶ H(E, K)` transposed, under the tensor–hom bijection, from `π` followed by the two
  counits.  It is an isomorphism (`isIso_pushforwardRightAdjointToHom`): this is the form of
  [Stacks, Tag 0A77] the comparison is made through.

## Main results

* `Stacks.Duality.ExactSupportBaseChange.isIso_baseChangeMap_iff_isIso_homComparison`: if the
  projection formulas are compatible with base change up to an automorphism of the objects of
  `𝒵'` (the hypothesis `hcore`), then the mate `Lg (a K) ⟶ a' (Lf K)` of `e` — the shape of the
  map of [Stacks, Tag 0E2K] — is an isomorphism exactly when the hom-comparison
  `Lf (H(E, K)) ⟶ H'(Lf E, Lf K)` — the shape of the map of [Stacks, Tag 08I3] — is.

* `Stacks.Duality.ExactSupportBaseChange.projection_baseChange`: projection maps `pr`, `pr'`
  compatible with a base change map `b` (the shape of [Stacks, Tag 0B6B]), followed by a unit
  constraint and the counit, are compatible with `b` up to the automorphism `unitDiscrepancy`.
* `Stacks.Duality.ExactSupportBaseChange.isIso_mate_iff_isIso_homComparison_of_projection`: the
  two results above assembled, with the projection isomorphisms built from projection maps on
  one tensor product and the internal homs stated on another; this is the form the geometric
  statement instantiates.
* `Stacks.Duality.ExactSupportBaseChange.homEquiv_ofNatIsoLeft_counit`: a mate does not depend
  on the model of the left adjoints.

## Implementation notes

The proof transposes both maps under the tensor–hom bijection on `𝒳'` and compares the
transposes; only the naturality of the bijections in their source variable is used.  The
automorphism `θ` in `hcore` absorbs the unit constraints: in the geometric instance it is the
discrepancy between the derived pullback of the right unitor and the right unitor of the
derived pullback, whose vanishing (the unitor coherence of [Stacks, Tag 079U]) is therefore
not needed.

## References

* [Stacks Project, Tag 0E2L](https://stacks.math.columbia.edu/tag/0E2L)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedInternalHomPullback

namespace Stacks.Duality.ExactSupportBaseChange

/-! ### One side: the pushforward of the right adjoint, mapped into the internal hom -/

section OneSide

variable {𝒳 𝒵 : Type*} [Category 𝒳] [Category 𝒵]
  {P : 𝒵 ⥤ 𝒳} {Li : 𝒳 ⥤ 𝒵} {a : 𝒳 ⥤ 𝒵} (q : Li ⊣ P) (ex : P ⊣ a)
  (H : 𝒳ᵒᵖ ⥤ 𝒳 ⥤ 𝒳) (T : 𝒳 × 𝒳 ⥤ 𝒳)
  (e₁ : ∀ A B C : 𝒳, (A ⟶ (H.obj (op B)).obj C) ≃ (T.obj (A, B) ⟶ C))
  (E : 𝒳) (π : ∀ W : 𝒳, T.obj (W, E) ≅ P.obj (Li.obj W))

/-- The map `P (a K) ⟶ H(E, K)` whose transpose under the tensor–hom bijection is the projection
isomorphism `P (a K) ⊗ E ≅ P (Li (P (a K)))` followed by `P` of the counit of `Li ⊣ P` and by the
counit of `P ⊣ a`. -/
def pushforwardRightAdjointToHom (K : 𝒳) : P.obj (a.obj K) ⟶ (H.obj (op E)).obj K :=
  (e₁ _ _ _).symm
    ((π (P.obj (a.obj K))).hom ≫ P.map (q.counit.app (a.obj K)) ≫ ex.counit.app K)

variable {q ex H T e₁ E π}

/-- The transpose of a morphism into `P (a K)` followed by `pushforwardRightAdjointToHom`. -/
theorem tensorHomEquiv_comp_pushforwardRightAdjointToHom
    (hnat : Transpose.TensorHomEquivNaturalLeft H T e₁)
    (hπ : ∀ {W W' : 𝒳} (x : W ⟶ W'),
      T.map (x ×ₘ 𝟙 E) ≫ (π W').hom = (π W).hom ≫ P.map (Li.map x))
    (K : 𝒳) {C₀ : 𝒳} (x : C₀ ⟶ P.obj (a.obj K)) :
    e₁ _ _ _ (x ≫ pushforwardRightAdjointToHom q ex H T e₁ E π K) =
      (π C₀).hom ≫ P.map (Li.map x ≫ q.counit.app (a.obj K)) ≫ ex.counit.app K := by
  rw [hnat, pushforwardRightAdjointToHom, Equiv.apply_symm_apply, ← Category.assoc, hπ x,
    Category.assoc, Functor.map_comp, Category.assoc]

/-- **`pushforwardRightAdjointToHom` is an isomorphism**: precomposition with it is the
composite of the tensor–hom bijection, the projection isomorphism and the two adjunction
bijections. -/
theorem isIso_pushforwardRightAdjointToHom
    (hnat : Transpose.TensorHomEquivNaturalLeft H T e₁)
    (hπ : ∀ {W W' : 𝒳} (x : W ⟶ W'),
      T.map (x ×ₘ 𝟙 E) ≫ (π W').hom = (π W).hom ≫ P.map (Li.map x))
    (K : 𝒳) : IsIso (pushforwardRightAdjointToHom q ex H T e₁ E π K) := by
  refine isIso_of_yoneda_map_bijective _ fun C₀ => ?_
  have hfun : (fun x : C₀ ⟶ P.obj (a.obj K) =>
      x ≫ pushforwardRightAdjointToHom q ex H T e₁ E π K) =
      fun x => (e₁ _ _ _).symm
        ((π C₀).hom ≫ (ex.homEquiv _ _).symm ((q.homEquiv _ _).symm x)) := by
    funext x
    apply (e₁ _ _ _).injective
    rw [Equiv.apply_symm_apply, tensorHomEquiv_comp_pushforwardRightAdjointToHom hnat hπ,
      Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  rw [hfun]
  have hπb : Function.Bijective (fun y : P.obj (Li.obj C₀) ⟶ K => (π C₀).hom ≫ y) :=
    ⟨fun y y' h => by simpa using congrArg (fun t => (π C₀).inv ≫ t) h,
      fun z => ⟨(π C₀).inv ≫ z, by simp⟩⟩
  exact (e₁ _ _ _).symm.bijective.comp
    (hπb.comp ((ex.homEquiv _ _).symm.bijective.comp (q.homEquiv _ _).symm.bijective))

end OneSide

/-! ### The comparison -/

section Comparison

variable {𝒳 𝒳' 𝒵 𝒵' : Type*} [Category 𝒳] [Category 𝒳'] [Category 𝒵] [Category 𝒵']
  {P : 𝒵 ⥤ 𝒳} {Li : 𝒳 ⥤ 𝒵} {a : 𝒳 ⥤ 𝒵} (q : Li ⊣ P) (ex : P ⊣ a)
  {P' : 𝒵' ⥤ 𝒳'} {Li' : 𝒳' ⥤ 𝒵'} {a' : 𝒳' ⥤ 𝒵'} (q' : Li' ⊣ P') (ex' : P' ⊣ a')
  (Lf : 𝒳 ⥤ 𝒳') (Lg : 𝒵 ⥤ 𝒵') (e : Lg ⋙ P' ≅ P ⋙ Lf)
  (H : 𝒳ᵒᵖ ⥤ 𝒳 ⥤ 𝒳) (H' : 𝒳'ᵒᵖ ⥤ 𝒳' ⥤ 𝒳') (T : 𝒳 × 𝒳 ⥤ 𝒳) (T' : 𝒳' × 𝒳' ⥤ 𝒳')
  (e₁ : ∀ A B C : 𝒳, (A ⟶ (H.obj (op B)).obj C) ≃ (T.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : 𝒳', (A ⟶ (H'.obj (op B)).obj C) ≃ (T'.obj (A, B) ⟶ C))
  (m : T ⋙ Lf ≅ Lf.prod Lf ⋙ T')
  (E : 𝒳) (π : ∀ W : 𝒳, T.obj (W, E) ≅ P.obj (Li.obj W))
  (π' : ∀ W : 𝒳', T'.obj (W, Lf.obj E) ≅ P'.obj (Li'.obj W))
  (θ : ∀ V : 𝒵, Lg.obj V ≅ Lg.obj V)

/-- **The mate of `e` and the hom-comparison agree up to isomorphisms.** Under the hypotheses of
`isIso_baseChangeMap_iff_isIso_homComparison`, `Lf` of the isomorphism
`pushforwardRightAdjointToHom` followed by the hom-comparison is `e⁻¹`, then `P'` of `θ` and of
the mate of `e`, then the isomorphism `pushforwardRightAdjointToHom` on the second side. -/
theorem map_pushforwardRightAdjointToHom_comp_homComparison
    (hnat₁ : Transpose.TensorHomEquivNaturalLeft H T e₁)
    (hnat₂ : Transpose.TensorHomEquivNaturalLeft H' T' e₂)
    (hπ' : ∀ {W W' : 𝒳'} (x : W ⟶ W'),
      T'.map (x ×ₘ 𝟙 (Lf.obj E)) ≫ (π' W').hom = (π' W).hom ≫ P'.map (Li'.map x))
    (hcore : ∀ V : 𝒵,
      m.inv.app (P.obj V, E) ≫ Lf.map ((π (P.obj V)).hom ≫ P.map (q.counit.app V)) =
        (π' (Lf.obj (P.obj V))).hom ≫
          P'.map (Li'.map (e.inv.app V) ≫ q'.counit.app (Lg.obj V) ≫ (θ V).hom) ≫
            e.hom.app V)
    (K : 𝒳) :
    Lf.map (pushforwardRightAdjointToHom q ex H T e₁ E π K) ≫
        Transpose.homComparison Lf H H' T T' e₁ e₂ m E K =
      e.inv.app (a.obj K) ≫
        P'.map ((θ (a.obj K)).hom ≫
          (ex'.homEquiv (Lg.obj (a.obj K)) (Lf.obj K))
            (e.hom.app (a.obj K) ≫ Lf.map (ex.counit.app K : P.obj (a.obj K) ⟶ K))) ≫
        pushforwardRightAdjointToHom q' ex' H' T' e₂ (Lf.obj E) π' (Lf.obj K) := by
  set c := (ex'.homEquiv (Lg.obj (a.obj K)) (Lf.obj K))
      (e.hom.app (a.obj K) ≫ Lf.map (ex.counit.app K : P.obj (a.obj K) ⟶ K))
  apply (e₂ _ _ _).injective
  conv_rhs => rw [← Category.assoc]
  rw [tensorHomEquiv_comp_pushforwardRightAdjointToHom hnat₂ hπ', hnat₂,
    Transpose.homComparison_adjoint]
  -- the left-hand side
  have hm := m.inv.naturality
    ((pushforwardRightAdjointToHom q ex H T e₁ E π K) ×ₘ 𝟙 E)
  dsimp at hm
  rw [CategoryTheory.Functor.map_id] at hm
  have hev : T.map ((pushforwardRightAdjointToHom q ex H T e₁ E π K) ×ₘ 𝟙 E) ≫
        Transpose.evaluation H T e₁ E K =
      (π (P.obj (a.obj K))).hom ≫ P.map (q.counit.app (a.obj K)) ≫ ex.counit.app K := by
    have h := hnat₁ _ _ E K (pushforwardRightAdjointToHom q ex H T e₁ E π K) (𝟙 _)
    rw [Category.comp_id, pushforwardRightAdjointToHom, Equiv.apply_symm_apply] at h
    exact h.symm
  have hl : T'.map (Lf.map (pushforwardRightAdjointToHom q ex H T e₁ E π K) ×ₘ 𝟙 (Lf.obj E)) ≫
        Transpose.homComparisonDatum Lf H T T' e₁ m E K =
      m.inv.app (P.obj (a.obj K), E) ≫
        Lf.map ((π (P.obj (a.obj K))).hom ≫ P.map (q.counit.app (a.obj K))) ≫
          Lf.map (ex.counit.app K) := by
    rw [Transpose.homComparisonDatum, ← Category.assoc, hm, Category.assoc,
      ← Functor.map_comp, hev, ← Functor.map_comp, Category.assoc]
  rw [hl, ← Category.assoc, hcore]
  -- the right-hand side
  have hc : P'.map c ≫ ex'.counit.app (Lf.obj K) = e.hom.app (a.obj K) ≫ Lf.map (ex.counit.app K) :=
    (ex'.homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _)
  have hq : P'.map (Li'.map (P'.map (θ (a.obj K)).hom)) ≫ P'.map (Li'.map (P'.map c)) ≫
        P'.map (q'.counit.app (a'.obj (Lf.obj K))) =
      P'.map (q'.counit.app (Lg.obj (a.obj K))) ≫ P'.map (θ (a.obj K)).hom ≫ P'.map c := by
    have h := congrArg P'.map (q'.counit.naturality ((θ (a.obj K)).hom ≫ c))
    dsimp at h
    simpa only [Functor.map_comp, Category.assoc] using h
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hq, hc]

/-- **The mate of `e` is an isomorphism exactly when the hom-comparison is.** Let `P` and `P'`
carry left adjoints `Li`, `Li'` and right adjoints `a`, `a'`, let `e : Lg ⋙ P' ≅ P ⋙ Lf`, and let
tensor–hom bijections natural in the source variable be given on `𝒳` and `𝒳'` together with a
monoidality comparison `m` of `Lf`. Suppose given projection isomorphisms
`π : W ⊗ E ≅ P (Li W)` and `π' : W' ⊗ Lf E ≅ P' (Li' W')`, the second natural, which are
compatible with `e` up to automorphisms `θ` of the objects `Lg V` (`hcore`), and that `P'`
reflects isomorphisms. Then for every `K` the mate
`Lg (a K) ⟶ a' (Lf K)` of `e` is an isomorphism if and only if the hom-comparison
`Lf (H(E, K)) ⟶ H'(Lf E, Lf K)` is. -/
theorem isIso_baseChangeMap_iff_isIso_homComparison
    (hnat₁ : Transpose.TensorHomEquivNaturalLeft H T e₁)
    (hnat₂ : Transpose.TensorHomEquivNaturalLeft H' T' e₂)
    (hπ : ∀ {W W' : 𝒳} (x : W ⟶ W'),
      T.map (x ×ₘ 𝟙 E) ≫ (π W').hom = (π W).hom ≫ P.map (Li.map x))
    (hπ' : ∀ {W W' : 𝒳'} (x : W ⟶ W'),
      T'.map (x ×ₘ 𝟙 (Lf.obj E)) ≫ (π' W').hom = (π' W).hom ≫ P'.map (Li'.map x))
    (hcore : ∀ V : 𝒵,
      m.inv.app (P.obj V, E) ≫ Lf.map ((π (P.obj V)).hom ≫ P.map (q.counit.app V)) =
        (π' (Lf.obj (P.obj V))).hom ≫
          P'.map (Li'.map (e.inv.app V) ≫ q'.counit.app (Lg.obj V) ≫ (θ V).hom) ≫
            e.hom.app V)
    [P'.ReflectsIsomorphisms] (K : 𝒳) :
    IsIso ((ex'.homEquiv (Lg.obj (a.obj K)) (Lf.obj K))
            (e.hom.app (a.obj K) ≫ Lf.map (ex.counit.app K : P.obj (a.obj K) ⟶ K))) ↔
      IsIso (Transpose.homComparison Lf H H' T T' e₁ e₂ m E K) := by
  have hσ := isIso_pushforwardRightAdjointToHom (q := q) (ex := ex) (e₁ := e₁) (π := π)
    hnat₁ hπ K
  have hσ' := isIso_pushforwardRightAdjointToHom (q := q') (ex := ex') (e₁ := e₂) (π := π')
    hnat₂ hπ' (Lf.obj K)
  have key := map_pushforwardRightAdjointToHom_comp_homComparison q ex q' ex' Lf Lg e H H' T T'
    e₁ e₂ m E π π' θ hnat₁ hnat₂ hπ' hcore K
  set c := (ex'.homEquiv (Lg.obj (a.obj K)) (Lf.obj K))
            (e.hom.app (a.obj K) ≫ Lf.map (ex.counit.app K : P.obj (a.obj K) ⟶ K))
  set σ := pushforwardRightAdjointToHom q ex H T e₁ E π K
  set σ' := pushforwardRightAdjointToHom q' ex' H' T' e₂ (Lf.obj E) π' (Lf.obj K)
  set ψ := Transpose.homComparison Lf H H' T T' e₁ e₂ m E K
  have hψ : ψ = inv (Lf.map σ) ≫ e.inv.app (a.obj K) ≫ P'.map ((θ (a.obj K)).hom ≫ c) ≫ σ' := by
    rw [← key, IsIso.inv_hom_id_assoc]
  refine ⟨fun hc => by rw [hψ]; infer_instance, fun hψi => ?_⟩
  have hP : IsIso (P'.map ((θ (a.obj K)).hom ≫ c)) := by
    have : P'.map ((θ (a.obj K)).hom ≫ c) =
        e.hom.app (a.obj K) ≫ Lf.map σ ≫ ψ ≫ inv σ' := by
      rw [reassoc_of% key]; simp
    rw [this]
    infer_instance
  have := isIso_of_reflects_iso ((θ (a.obj K)).hom ≫ c) P'
  exact IsIso.of_isIso_comp_left (θ (a.obj K)).hom c

end Comparison

/-! ### The projection maps are compatible with base change, over abstract data -/

section Projection

variable {𝒳 𝒳' 𝒵 𝒵' : Type*} [Category 𝒳] [Category 𝒳'] [Category 𝒵] [Category 𝒵']
  {P : 𝒵 ⥤ 𝒳} {Li : 𝒳 ⥤ 𝒵} (q : Li ⊣ P) {P' : 𝒵' ⥤ 𝒳'} {Li' : 𝒳' ⥤ 𝒵'} (q' : Li' ⊣ P')
  (Lf : 𝒳 ⥤ 𝒳') (Lg : 𝒵 ⥤ 𝒵') (b : ∀ N : 𝒵, Lf.obj (P.obj N) ⟶ P'.obj (Lg.obj N))
  (c : Lf ⋙ Li' ≅ Li ⋙ Lg)
  (T : 𝒳 × 𝒳 ⥤ 𝒳) (T' : 𝒳' × 𝒳' ⥤ 𝒳') (TZ : 𝒵 × 𝒵 ⥤ 𝒵) (TZ' : 𝒵' × 𝒵' ⥤ 𝒵')
  (mf : T ⋙ Lf ≅ Lf.prod Lf ⋙ T') (mg : TZ ⋙ Lg ≅ Lg.prod Lg ⋙ TZ')
  (pr : ∀ (K : 𝒳) (N : 𝒵), T.obj (K, P.obj N) ⟶ P.obj (TZ.obj (Li.obj K, N)))
  (pr' : ∀ (K : 𝒳') (N : 𝒵'), T'.obj (K, P'.obj N) ⟶ P'.obj (TZ'.obj (Li'.obj K, N)))
  (O : 𝒵) (ρ : ∀ B : 𝒵, TZ.obj (B, O) ≅ B) (υ : ∀ B : 𝒵', TZ'.obj (B, Lg.obj O) ≅ B)

/-- The automorphism of `Lg V` comparing the unit constraint `υ` for `Lg O` on `𝒵'` with `Lg` of
the unit constraint `ρ` on `𝒵`, through the monoidality comparison `mg`. -/
def unitDiscrepancy (V : 𝒵) : Lg.obj V ≅ Lg.obj V :=
  (υ (Lg.obj V)).symm ≪≫ (mg.app (V, O)).symm ≪≫ Lg.mapIso (ρ V)

variable {q q' Lf Lg b c T T' TZ TZ' mf mg pr pr' O ρ υ}

/-- **The projection maps are compatible with base change**, over abstract data: given the
compatibility `h3` of the projection maps `pr`, `pr'` with the base change map `b`
(the shape of [Stacks, Tag 0B6B]) and the adjoint description `h2` of `b` (the shape of
[Stacks, Tag 08HY]), the projection map at `O` followed by the unit constraint and the counit,
pulled back along `Lf` and followed by `b`, is the projection map along the base change followed
by the unit constraint, the counit and the automorphism `unitDiscrepancy`. -/
theorem projection_baseChange
    (hb : ∀ {N N' : 𝒵} (x : N ⟶ N'), Lf.map (P.map x) ≫ b N' = b N ≫ P'.map (Lg.map x))
    (hρ : ∀ {B B' : 𝒵} (x : B ⟶ B'), TZ.map (x ×ₘ 𝟙 O) ≫ (ρ B').hom = (ρ B).hom ≫ x)
    (hυ : ∀ {B B' : 𝒵'} (x : B ⟶ B'),
      TZ'.map (x ×ₘ 𝟙 (Lg.obj O)) ≫ (υ B').hom = (υ B).hom ≫ x)
    (h3 : ∀ (K : 𝒳) (N : 𝒵),
      mf.hom.app (K, P.obj N) ≫ T'.map (𝟙 (Lf.obj K) ×ₘ b N) ≫ pr' (Lf.obj K) (Lg.obj N) =
        Lf.map (pr K N) ≫ b (TZ.obj (Li.obj K, N)) ≫
          P'.map (mg.hom.app (Li.obj K, N) ≫ TZ'.map (c.inv.app K ×ₘ 𝟙 (Lg.obj N))))
    (h2 : ∀ V : 𝒵, Li'.map (b V) ≫ q'.counit.app (Lg.obj V) =
      c.hom.app (P.obj V) ≫ Lg.map (q.counit.app V))
    (V : 𝒵) :
    mf.inv.app (P.obj V, P.obj O) ≫
        Lf.map (pr (P.obj V) O ≫ P.map ((ρ (Li.obj (P.obj V))).hom ≫ q.counit.app V)) ≫
          b V =
      T'.map (𝟙 (Lf.obj (P.obj V)) ×ₘ b O) ≫ pr' (Lf.obj (P.obj V)) (Lg.obj O) ≫
        P'.map ((υ (Li'.obj (Lf.obj (P.obj V)))).hom ≫ Li'.map (b V) ≫
          q'.counit.app (Lg.obj V) ≫ (unitDiscrepancy Lg TZ TZ' mg O ρ υ V).hom) := by
  set K := P.obj V
  -- the naturality of `b` moves the unit constraint and the counit past it
  have hb' := hb (N := TZ.obj (Li.obj K, O)) (N' := V) ((ρ (Li.obj K)).hom ≫ q.counit.app V)
  -- the compatibility `h3`, solved for `Lf` of the projection map followed by `b`
  let Γ : Lg.obj (TZ.obj (Li.obj K, O)) ≅ TZ'.obj (Li'.obj (Lf.obj K), Lg.obj O) :=
    mg.app (Li.obj K, O) ≪≫ TZ'.mapIso (Iso.prod (c.app K).symm (Iso.refl (Lg.obj O)))
  have h3' : mf.inv.app (K, P.obj O) ≫ Lf.map (pr K O) ≫ b (TZ.obj (Li.obj K, O)) =
      T'.map (𝟙 (Lf.obj K) ×ₘ b O) ≫ pr' (Lf.obj K) (Lg.obj O) ≫ P'.map Γ.inv := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, reassoc_of% (h3 K O)]
    have hΓ : mg.hom.app (Li.obj K, O) ≫ TZ'.map (c.inv.app K ×ₘ 𝟙 (Lg.obj O)) = Γ.hom := rfl
    rw [hΓ, ← P'.map_comp, Iso.hom_inv_id, P'.map_id, Category.comp_id]
  -- the inner identity on `𝒵'`
  have hinner : Γ.inv ≫ Lg.map ((ρ (Li.obj K)).hom ≫ q.counit.app V) =
      (υ (Li'.obj (Lf.obj K))).hom ≫ Li'.map (b V) ≫ q'.counit.app (Lg.obj V) ≫
        (unitDiscrepancy Lg TZ TZ' mg O ρ υ V).hom := by
    rw [Iso.inv_comp_eq, reassoc_of% (h2 V)]
    have hΓ : Γ.hom = mg.hom.app (Li.obj K, O) ≫ TZ'.map (c.inv.app K ×ₘ 𝟙 (Lg.obj O)) := rfl
    rw [hΓ]
    have hA : TZ'.map (c.inv.app K ×ₘ 𝟙 (Lg.obj O)) ≫ (υ (Li'.obj (Lf.obj K))).hom ≫
        c.hom.app K = (υ (Lg.obj (Li.obj K))).hom := by
      have h := hυ (c.hom.app K)
      dsimp at h
      rw [← h, ← TZ'.map_comp_assoc]
      simp
    have hmg : mg.hom.app (Li.obj K, O) ≫
        TZ'.map (Lg.map (q.counit.app V) ×ₘ 𝟙 (Lg.obj O)) =
        Lg.map (TZ.map (q.counit.app V ×ₘ 𝟙 O)) ≫ mg.hom.app (V, O) := by
      simpa using (mg.hom.naturality (q.counit.app V ×ₘ 𝟙 O)).symm
    simp only [unitDiscrepancy, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv,
      Category.assoc]
    rw [reassoc_of% hA, ← reassoc_of% (hυ (Lg.map (q.counit.app V))), Iso.hom_inv_id_assoc,
      reassoc_of% hmg, Iso.hom_inv_id_app_assoc, ← Lg.map_comp, hρ, Lg.map_comp]
  calc mf.inv.app (K, P.obj O) ≫
        Lf.map (pr K O ≫ P.map ((ρ (Li.obj K)).hom ≫ q.counit.app V)) ≫ b V
      = (mf.inv.app (K, P.obj O) ≫ Lf.map (pr K O) ≫ b (TZ.obj (Li.obj K, O))) ≫
          P'.map (Lg.map ((ρ (Li.obj K)).hom ≫ q.counit.app V)) := by
        rw [Functor.map_comp, Category.assoc, Category.assoc, Category.assoc, hb']
    _ = _ := by
        rw [h3', Category.assoc, Category.assoc, ← P'.map_comp, hinner]

end Projection

/-- A right unit constraint precomposed with an isomorphism of units is natural. -/
theorem unitor_comp_naturality {𝒞 : Type*} [Category 𝒞] (T : 𝒞 × 𝒞 ⥤ 𝒞) {O O' : 𝒞}
    (ν : O ⟶ O') (ρ : ∀ B : 𝒞, T.obj (B, O') ⟶ B)
    (hρ : ∀ {B B' : 𝒞} (x : B ⟶ B'), T.map (x ×ₘ 𝟙 O') ≫ ρ B' = ρ B ≫ x)
    {B B' : 𝒞} (x : B ⟶ B') :
    T.map (x ×ₘ 𝟙 O) ≫ T.map (𝟙 B' ×ₘ ν) ≫ ρ B' = (T.map (𝟙 B ×ₘ ν) ≫ ρ B) ≫ x := by
  rw [← T.map_comp_assoc, prod_comp, Category.id_comp, Category.comp_id, Category.assoc, ← hρ,
    ← T.map_comp_assoc, prod_comp, Category.id_comp, Category.comp_id]

/-! ### Changing the model of the left adjoint -/

/-- **A mate does not depend on the model of the left adjoints.** If the left adjoints `F`, `F'`
of `H`, `H'` are replaced by isomorphic functors `G`, `G'`, the mate of
`e₀ : Lg ⋙ G' ≅ G ⋙ Lf` for the transported adjunctions is the mate, for the original ones, of
`e₀` conjugated by the two isomorphisms. -/
theorem homEquiv_ofNatIsoLeft_counit {C D C' D' : Type*} [Category C] [Category D]
    [Category C'] [Category D'] {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (κ : F ≅ G)
    {F' G' : C' ⥤ D'} {H' : D' ⥤ C'} (adj' : F' ⊣ H') (κ' : F' ≅ G')
    (Lf : D ⥤ D') (Lg : C ⥤ C') (e₀ : Lg ⋙ G' ≅ G ⋙ Lf) (K : D) :
    (adj'.homEquiv _ _)
        ((Functor.isoWhiskerLeft Lg κ' ≪≫ e₀ ≪≫ Functor.isoWhiskerRight κ.symm Lf).hom.app
            (H.obj K) ≫ Lf.map (adj.counit.app K)) =
      ((adj'.ofNatIsoLeft κ').homEquiv _ _)
        (e₀.hom.app (H.obj K) ≫ Lf.map ((adj.ofNatIsoLeft κ).counit.app K)) := by
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.ofNatIsoLeft_counit]
  simp

/-! ### The comparison, from the projection maps -/

section FromProjection

variable {𝒳 𝒳' 𝒵 𝒵' : Type*} [Category 𝒳] [Category 𝒳'] [Category 𝒵] [Category 𝒵']
  {P : 𝒵 ⥤ 𝒳} {Li : 𝒳 ⥤ 𝒵} {a : 𝒳 ⥤ 𝒵} (q : Li ⊣ P) (ex : P ⊣ a)
  {P' : 𝒵' ⥤ 𝒳'} {Li' : 𝒳' ⥤ 𝒵'} {a' : 𝒳' ⥤ 𝒵'} (q' : Li' ⊣ P') (ex' : P' ⊣ a')
  (Lf : 𝒳 ⥤ 𝒳') (Lg : 𝒵 ⥤ 𝒵') (b : ∀ N : 𝒵, Lf.obj (P.obj N) ⟶ P'.obj (Lg.obj N))
  (c : Lf ⋙ Li' ≅ Li ⋙ Lg)
  (T₀ : 𝒳 × 𝒳 ⥤ 𝒳) (T₀' : 𝒳' × 𝒳' ⥤ 𝒳') (TZ : 𝒵 × 𝒵 ⥤ 𝒵) (TZ' : 𝒵' × 𝒵' ⥤ 𝒵')
  (mf : T₀ ⋙ Lf ≅ Lf.prod Lf ⋙ T₀') (mg : TZ ⋙ Lg ≅ Lg.prod Lg ⋙ TZ')
  (pr : ∀ (K : 𝒳) (N : 𝒵), T₀.obj (K, P.obj N) ⟶ P.obj (TZ.obj (Li.obj K, N)))
  (pr' : ∀ (K : 𝒳') (N : 𝒵'), T₀'.obj (K, P'.obj N) ⟶ P'.obj (TZ'.obj (Li'.obj K, N)))
  (O : 𝒵) (ρ : ∀ B : 𝒵, TZ.obj (B, O) ≅ B) (υ : ∀ B : 𝒵', TZ'.obj (B, Lg.obj O) ≅ B)
  (H : 𝒳ᵒᵖ ⥤ 𝒳 ⥤ 𝒳) (H' : 𝒳'ᵒᵖ ⥤ 𝒳' ⥤ 𝒳') (T : 𝒳 × 𝒳 ⥤ 𝒳) (T' : 𝒳' × 𝒳' ⥤ 𝒳')
  (e₁ : ∀ A B C : 𝒳, (A ⟶ (H.obj (op B)).obj C) ≃ (T.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : 𝒳', (A ⟶ (H'.obj (op B)).obj C) ≃ (T'.obj (A, B) ⟶ C))
  (β : T₀ ≅ T) (β' : T₀' ≅ T')

/-- **The mate of a base change isomorphism is invertible exactly when the hom-comparison is**,
from projection maps compatible with base change. This assembles
`isIso_baseChangeMap_iff_isIso_homComparison`, the compatibility `projection_baseChange` and
the passage `β`, `β'` between the tensor products the projection maps and the internal homs are
stated at; the monoidality comparison of the hom-comparison is `mf` conjugated by `β` and `β'`,
which is how the comparison of Cohomology, Remark [Stacks, Tag 08I3] is built from that of
[Stacks, Tag 079U]. -/
theorem isIso_mate_iff_isIso_homComparison_of_projection
    (hbi : ∀ N, IsIso (b N)) (hpri : ∀ W, IsIso (pr W O))
    (hpri' : ∀ W, IsIso (pr' W (Lg.obj O))) (hP' : P'.ReflectsIsomorphisms)
    (hb : ∀ {N N' : 𝒵} (x : N ⟶ N'), Lf.map (P.map x) ≫ b N' = b N ≫ P'.map (Lg.map x))
    (hρ : ∀ {B B' : 𝒵} (x : B ⟶ B'), TZ.map (x ×ₘ 𝟙 O) ≫ (ρ B').hom = (ρ B).hom ≫ x)
    (hυ : ∀ {B B' : 𝒵'} (x : B ⟶ B'),
      TZ'.map (x ×ₘ 𝟙 (Lg.obj O)) ≫ (υ B').hom = (υ B).hom ≫ x)
    (hpr : ∀ {W W' : 𝒳} (x : W ⟶ W'),
      T₀.map (x ×ₘ P.map (𝟙 O)) ≫ pr W' O = pr W O ≫ P.map (TZ.map (Li.map x ×ₘ 𝟙 O)))
    (hpr' : ∀ {W W' : 𝒳'} (x : W ⟶ W'),
      T₀'.map (x ×ₘ P'.map (𝟙 (Lg.obj O))) ≫ pr' W' (Lg.obj O) =
        pr' W (Lg.obj O) ≫ P'.map (TZ'.map (Li'.map x ×ₘ 𝟙 (Lg.obj O))))
    (h3 : ∀ (K : 𝒳) (N : 𝒵),
      mf.hom.app (K, P.obj N) ≫ T₀'.map (𝟙 (Lf.obj K) ×ₘ b N) ≫ pr' (Lf.obj K) (Lg.obj N) =
        Lf.map (pr K N) ≫ b (TZ.obj (Li.obj K, N)) ≫
          P'.map (mg.hom.app (Li.obj K, N) ≫ TZ'.map (c.inv.app K ×ₘ 𝟙 (Lg.obj N))))
    (h2 : ∀ V : 𝒵, (q'.homEquiv _ _).symm (b V) =
      c.hom.app (P.obj V) ≫ Lg.map (q.counit.app V))
    (hnat₁ : Transpose.TensorHomEquivNaturalLeft H T e₁)
    (hnat₂ : Transpose.TensorHomEquivNaturalLeft H' T' e₂)
    (K : 𝒳) :
    IsIso ((ex'.homEquiv (Lg.obj (a.obj K)) (Lf.obj K))
        (inv (b (a.obj K)) ≫ Lf.map (ex.counit.app K : P.obj (a.obj K) ⟶ K))) ↔
      IsIso (Transpose.homComparison Lf H H' T T' e₁ e₂
        (Functor.isoWhiskerRight β.symm Lf ≪≫ mf ≪≫ Functor.isoWhiskerLeft (Lf.prod Lf) β')
        (P.obj O) K) := by
  have := hbi
  have := hpri
  have := hpri'
  let e : Lg ⋙ P' ≅ P ⋙ Lf := NatIso.ofComponents (fun N => (asIso (b N)).symm)
    fun {N N'} x => by
      dsimp
      rw [IsIso.eq_inv_comp, ← reassoc_of% (hb x), IsIso.hom_inv_id, Category.comp_id]
  let π : ∀ W : 𝒳, T.obj (W, P.obj O) ≅ P.obj (Li.obj W) := fun W =>
    (β.app (W, P.obj O)).symm ≪≫ asIso (pr W O) ≪≫ P.mapIso (ρ (Li.obj W))
  let π' : ∀ W : 𝒳', T'.obj (W, Lf.obj (P.obj O)) ≅ P'.obj (Li'.obj W) := fun W =>
    (β'.app (W, Lf.obj (P.obj O))).symm ≪≫ T₀'.mapIso (Iso.prod (Iso.refl W) (asIso (b O))) ≪≫
      asIso (pr' W (Lg.obj O)) ≪≫ P'.mapIso (υ (Li'.obj W))
  have hπ : ∀ {W W' : 𝒳} (x : W ⟶ W'),
      T.map (x ×ₘ 𝟙 (P.obj O)) ≫ (π W').hom = (π W).hom ≫ P.map (Li.map x) := by
    intro W W' x
    have hβ := β.inv.naturality (x ×ₘ 𝟙 (P.obj O))
    simp only [π, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, asIso_hom, Functor.mapIso_hom,
      Category.assoc]
    have hpr₀ := hpr x
    rw [CategoryTheory.Functor.map_id] at hpr₀
    rw [reassoc_of% hβ, reassoc_of% hpr₀, ← P.map_comp, ← P.map_comp, hρ]
  have hπ' : ∀ {W W' : 𝒳'} (x : W ⟶ W'),
      T'.map (x ×ₘ 𝟙 (Lf.obj (P.obj O))) ≫ (π' W').hom = (π' W).hom ≫ P'.map (Li'.map x) := by
    intro W W' x
    have hβ := β'.inv.naturality (x ×ₘ 𝟙 (Lf.obj (P.obj O)))
    have hT : T₀'.map (x ×ₘ 𝟙 (Lf.obj (P.obj O))) ≫ T₀'.map (𝟙 W' ×ₘ b O) =
        T₀'.map (𝟙 W ×ₘ b O) ≫ T₀'.map (x ×ₘ 𝟙 (P'.obj (Lg.obj O))) := by
      rw [← T₀'.map_comp, ← T₀'.map_comp, prod_comp, prod_comp, Category.id_comp,
        Category.comp_id, Category.id_comp, Category.comp_id]
    simp only [π', Iso.trans_hom, Iso.symm_hom, Iso.app_inv, asIso_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Category.assoc]
    have hpr₀ := hpr' x
    rw [CategoryTheory.Functor.map_id] at hpr₀
    rw [reassoc_of% hβ, reassoc_of% hT, reassoc_of% hpr₀, ← P'.map_comp, ← P'.map_comp,
      hυ]
  refine isIso_baseChangeMap_iff_isIso_homComparison q ex q' ex' Lf Lg e H H' T T' e₁ e₂ _
    (P.obj O) π π' (unitDiscrepancy Lg TZ TZ' mg O ρ υ) hnat₁ hnat₂ hπ hπ' (fun V => ?_) K
  have hcore := projection_baseChange (q := q) (q' := q') (c := c) (mf := mf) (pr := pr)
    (pr' := pr') hb hρ hυ h3 (fun W => by rw [← h2 W, Adjunction.homEquiv_counit]) V
  refine (cancel_mono (b V)).1 ?_
  simp only [π, π', e, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_inv,
    asIso_hom, asIso_inv, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, Functor.map_comp, IsIso.inv_hom_id,
    Category.comp_id] at hcore ⊢
  rw [← Lf.map_comp_assoc (β.hom.app _), Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, hcore]
  rfl

end FromProjection

end Stacks.Duality.ExactSupportBaseChange

end
