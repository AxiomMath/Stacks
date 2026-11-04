module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification.LocalizationMap

/-!
# Covering sieves and the morphisms of `u_pp 𝒮`

Auxiliary results for the pullback of a stackification: transferring a covering sieve of `𝒞` to
one of `𝒟` along a continuous functor `u : 𝒞 ⥤ 𝒟`, clause (1) of Stacks 02ZN (injectivity half)
read in the fibres, the composition of clause (2) of Stacks 02ZN, and the morphisms of `u_pp 𝒮`
written out explicitly.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 04WR](https://stacks.math.columbia.edu/tag/04WR)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/-! ### Transferring a covering sieve of `𝒞` to one of `𝒟` -/

section CoverTransfer

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟] (u : 𝒞 ⥤ 𝒟)
  (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟)

/-- For a continuous `u`, a covering sieve `R` of `U` and a morphism `ρ : V ⟶ u(U)`, the sieve
of the morphisms `β : V₁ ⟶ V` for which `β ∘ ρ` factors as `χ ∘ u(d)` with `d` in `R` is a
covering sieve of `V`. -/
lemma mem_pullback_functorPushforward [u.IsContinuous J K] {U : 𝒞} {R : Sieve U} (hR : R ∈ J U)
    {V : 𝒟} (ρ : V ⟶ u.obj U) :
    Sieve.pullback ρ (Sieve.functorPushforward u R) ∈ K V :=
  K.pullback_stable ρ ((CoverPreserving.of_isContinuous u J K).cover_preserve hR)

/-- A member `β` of the pullback along `ρ : V ⟶ u(U)` of the pushforward of a sieve `R` of `U`
is one for which `β ∘ ρ` factors as `χ ∘ u(d)` with `d` in `R`. -/
lemma exists_factorisation_of_mem_pullback_functorPushforward {U : 𝒞} {R : Sieve U} {V : 𝒟}
    (ρ : V ⟶ u.obj U) {V₁ : 𝒟} {β : V₁ ⟶ V}
    (hβ : (Sieve.pullback ρ (Sieve.functorPushforward u R)).arrows β) :
    ∃ (U₁ : 𝒞) (d : U₁ ⟶ U) (χ : V₁ ⟶ u.obj U₁), R.arrows d ∧ β ≫ ρ = χ ≫ u.map d :=
  hβ

end CoverTransfer

/-! ### Clause (1) of Stacks 02ZN, injectivity half, read in the fibres -/

section CoveringEq

universe v

open Opposite

section BaseHomUniverse

universe vb

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜] {ℬ : Type u₃}
  [Category.{v} ℬ] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {N : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]

/-- `CategoryTheory.exists_covering_eq` with the hom universe of the base left independent of
the hom universes of `𝒜` and `ℬ`. -/
lemma exists_covering_eq_of_baseHomUniverse (hN : q.IsFibredOneMorphism r N)
    (J : GrothendieckTopology 𝒞) {U : 𝒞} {a b : q.Fiber U}
    (hinj : Presheaf.IsLocallyInjective (J.over U) (hN.morPresheafMap a b))
    (m₁ m₂ : a ⟶ b)
    (h : (Functor.fiberFunctorOfCompEq hN.comp_eq U).map m₁ =
      (Functor.fiberFunctorOfCompEq hN.comp_eq U).map m₂) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f →
      Functor.pullbackFiberHom m₁ f = Functor.pullbackFiberHom m₂ f := by
  have heq : (hN.morPresheafMap a b).app (op (Over.mk (𝟙 U))) (Functor.morSection q a b m₁) =
      (hN.morPresheafMap a b).app (op (Over.mk (𝟙 U))) (Functor.morSection q a b m₂) := by
    simp [hN.morPresheafMap_app_eq, hN.morMapAt_def, Functor.morSection, Functor.map_comp, h]
  have hmemsieve : Presheaf.equalizerSieve (F := Functor.morPresheaf q a b)
      (X := op (Over.mk (𝟙 U) : Over U)) (Functor.morSection q a b m₁)
      (Functor.morSection q a b m₂) ∈ (J.over U) (Over.mk (𝟙 U) : Over U) :=
    Presheaf.equalizerSieve_mem (J.over U) (hN.morPresheafMap a b) _ _ heq
  refine ⟨Sieve.overEquiv (Over.mk (𝟙 U) : Over U) _, (J.mem_over_iff _).1 hmemsieve, ?_⟩
  intro V f hf
  have hmem : (Functor.morPresheaf q a b).map (Functor.overArrow f).op
      (Functor.morSection q a b m₁) =
      (Functor.morPresheaf q a b).map (Functor.overArrow f).op
        (Functor.morSection q a b m₂) := Functor.mem_of_overEquiv hf
  rwa [Functor.morPresheaf_map_op_apply, Functor.morPresheaf_map_op_apply,
    Functor.morRestrict_morSection, Functor.morRestrict_morSection] at hmem

/-- `CategoryTheory.exists_covering_lift_hom` with the hom universe of the base left independent
of the hom universes of `𝒜` and `ℬ`. -/
lemma exists_covering_lift_hom_of_baseHomUniverse (hN : q.IsFibredOneMorphism r N)
    (J : GrothendieckTopology 𝒞)
    (hmor : ∀ (U : 𝒞) (x y : q.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hN.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U) (hN.morPresheafMap x y))
    {A b : 𝒜} (θ : N.obj A ⟶ N.obj b) :
    ∃ R ∈ J (q.obj A), ∀ ⦃W : 𝒞⦄ (k : W ⟶ q.obj A), R.arrows k →
      ∃ w : (Functor.pullbackFiber q (Functor.Fiber.mk (rfl : q.obj A = q.obj A)) k).1 ⟶ b,
        N.map (Functor.IsPreFibered.pullbackMap
            (Functor.Fiber.mk (rfl : q.obj A = q.obj A)).2 k) ≫ θ = N.map w := by
  classical
  have hNA : r.obj (N.obj A) = q.obj A := Functor.congr_obj hN.comp_eq A
  have hNb : r.obj (N.obj b) = q.obj b := Functor.congr_obj hN.comp_eq b
  set t : q.obj A ⟶ q.obj b := eqToHom hNA.symm ≫ r.map θ ≫ eqToHom hNb with ht
  have hθlift : r.IsHomLift t θ := IsHomLift.of_fac' r t θ hNA hNb (by rw [ht]; simp)
  set AF : q.Fiber (q.obj A) := Functor.Fiber.mk rfl with hAF
  set bF : q.Fiber (q.obj b) := Functor.Fiber.mk rfl with hbF
  set tb : q.Fiber (q.obj A) := Functor.pullbackFiber q bF t with htb
  set lam : tb.1 ⟶ b := Functor.IsPreFibered.pullbackMap bF.2 t with hlam
  have hNlam : r.IsStronglyCartesian t (N.map lam) :=
    hN.map_isStronglyCartesian t lam inferInstance
  have hone : t = 𝟙 (q.obj A) ≫ t := by simp
  set θ₁ := Functor.IsStronglyCartesian.map r t (N.map lam) hone θ with hθ₁
  have hθ₁fac : θ₁ ≫ N.map lam = θ := Functor.IsStronglyCartesian.fac r t (N.map lam) hone θ
  have hθ₁lift : r.IsHomLift (𝟙 (q.obj A)) θ₁ :=
    Functor.IsStronglyCartesian.map_isHomLift r t (N.map lam) hone θ
  set θt : (Functor.fiberFunctorOfCompEq hN.comp_eq (q.obj A)).obj AF ⟶
      (Functor.fiberFunctorOfCompEq hN.comp_eq (q.obj A)).obj tb := ⟨θ₁, hθ₁lift⟩ with hθt
  obtain ⟨R, hR, hlift⟩ := Functor.Stackification.exists_covering_lift hN hmor θt
  refine ⟨R, hR, ?_⟩
  intro W k hk
  obtain ⟨v, hv⟩ := hlift k hk
  refine ⟨Functor.Fiber.fiberInclusion.map v ≫
    Functor.IsPreFibered.pullbackMap tb.2 k ≫ lam, ?_⟩
  have hiso : IsIso (Functor.Fiber.fiberInclusion.map (hN.mapPullbackFiberIso AF k).hom) :=
    inferInstance
  have hcancel : Functor.Fiber.fiberInclusion.map (hN.mapPullbackFiberIso AF k).hom ≫
      N.map (Functor.Fiber.fiberInclusion.map v ≫
        Functor.IsPreFibered.pullbackMap tb.2 k) =
      Functor.Fiber.fiberInclusion.map (hN.mapPullbackFiberIso AF k).hom ≫
        N.map (Functor.IsPreFibered.pullbackMap AF.2 k) ≫ θ₁ := by
    rw [hN.mapPullbackFiberIso_hom_fac_assoc AF k θ₁, N.map_comp, ← Category.assoc]
    have h1 := hN.morMapAt_fac AF tb k v
    rw [hv, Functor.pullbackFiberHom_fac, ← Category.assoc] at h1
    exact h1.symm
  have hkey : N.map (Functor.Fiber.fiberInclusion.map v ≫
      Functor.IsPreFibered.pullbackMap tb.2 k) =
      N.map (Functor.IsPreFibered.pullbackMap AF.2 k) ≫ θ₁ := (cancel_epi _).1 hcancel
  rw [N.map_comp, N.map_comp, ← Category.assoc, ← N.map_comp, hkey, Category.assoc, hθ₁fac]

end BaseHomUniverse

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜] {ℬ : Type u₃}
  [Category.{v} ℬ] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {N : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]

/-- **Clause (1) of Stacks 02ZN in the base site, injectivity half.** Two morphisms of the fibre of
`𝒜` over `U` with the same image in the fibre of `ℬ` agree after base change along the members of a
covering sieve of `U`. -/
lemma exists_covering_eq (hN : q.IsFibredOneMorphism r N) (J : GrothendieckTopology 𝒞) {U : 𝒞}
    {a b : q.Fiber U} (hinj : Presheaf.IsLocallyInjective (J.over U) (hN.morPresheafMap a b))
    (m₁ m₂ : a ⟶ b)
    (h : (Functor.fiberFunctorOfCompEq hN.comp_eq U).map m₁ =
      (Functor.fiberFunctorOfCompEq hN.comp_eq U).map m₂) :
    ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f →
      Functor.pullbackFiberHom m₁ f = Functor.pullbackFiberHom m₂ f :=
  exists_covering_eq_of_baseHomUniverse hN J hinj m₁ m₂ h

/-- **Clause (1) of Stacks 02ZN in the base site, surjectivity half, between arbitrary objects.**
A morphism `N A ⟶ N b` of `ℬ` becomes, after precomposition with the chosen cartesian lift of a
member of a covering sieve of `q(A)`, the image under `N` of a morphism of `𝒜`. -/
lemma exists_covering_lift_hom (hN : q.IsFibredOneMorphism r N) (J : GrothendieckTopology 𝒞)
    (hmor : ∀ (U : 𝒞) (x y : q.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hN.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U) (hN.morPresheafMap x y))
    {A b : 𝒜} (θ : N.obj A ⟶ N.obj b) :
    ∃ R ∈ J (q.obj A), ∀ ⦃W : 𝒞⦄ (k : W ⟶ q.obj A), R.arrows k →
      ∃ w : (Functor.pullbackFiber q (Functor.Fiber.mk (rfl : q.obj A = q.obj A)) k).1 ⟶ b,
        N.map (Functor.IsPreFibered.pullbackMap
            (Functor.Fiber.mk (rfl : q.obj A = q.obj A)).2 k) ≫ θ = N.map w :=
  exists_covering_lift_hom_of_baseHomUniverse hN J hmor θ

end CoveringEq

/-! ### Clause (2) of Stacks 02ZN composes -/

section CompEssSurj

universe v

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜] {ℬ : Type u₃}
  [Category.{v} ℬ] {ℰ : Type u₄} [Category.{v} ℰ] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {t : ℰ ⥤ 𝒞}
  {N : 𝒜 ⥤ ℬ} {M : ℬ ⥤ ℰ} [q.IsFibered] [r.IsFibered] [t.IsFibered]

omit [q.IsFibered] in
/-- **Clause (2) of Stacks 02ZN composes.** If every object of a fibre of `ℬ` is, along a covering
sieve, in the essential image of `N`, and every object of a fibre of `ℰ` is, along a covering
sieve, in the essential image of `M`, then every object of a fibre of `ℰ` is, along a covering
sieve, in the essential image of `N ⋙ M`. -/
theorem locallyEssSurj_comp (hN : q.IsFibredOneMorphism r N) (hM : r.IsFibredOneMorphism t M)
    (J : GrothendieckTopology 𝒞)
    (hobjN : ∀ (U : 𝒞) (x : r.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (Functor.fiberFunctorOfCompEq hN.comp_eq V).essImage (Functor.pullbackFiber r x f))
    (hobjM : ∀ (U : 𝒞) (x : t.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (Functor.fiberFunctorOfCompEq hM.comp_eq V).essImage (Functor.pullbackFiber t x f)) :
    ∀ (U : 𝒞) (x : t.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (Functor.fiberFunctorOfCompEq (hN.comp hM).comp_eq V).essImage
        (Functor.pullbackFiber t x f) := by
  intro U x
  obtain ⟨S, hS, hSess⟩ := hobjM U x
  classical
  refine ⟨Sieve.bind S.arrows (fun V f hf ↦ (hobjN V (hSess hf).choose).choose),
    J.bind_covering hS (fun V f hf ↦ (hobjN V (hSess hf).choose).choose_spec.1), ?_⟩
  rintro W k ⟨V, g, f, hf, hg, rfl⟩
  obtain ⟨z, ⟨isoN⟩⟩ := (hobjN V (hSess hf).choose).choose_spec.2 hg
  refine ⟨z, ⟨?_⟩⟩
  have hobjeq : (Functor.fiberFunctorOfCompEq (hN.comp hM).comp_eq W).obj z =
      (Functor.fiberFunctorOfCompEq hM.comp_eq W).obj
        ((Functor.fiberFunctorOfCompEq hN.comp_eq W).obj z) := rfl
  rw [hobjeq]
  refine (Functor.fiberFunctorOfCompEq hM.comp_eq W).mapIso isoN ≪≫ ?_
  refine (hM.mapPullbackFiberIso (hSess hf).choose g).symm ≪≫ ?_
  refine Functor.pullbackFiberIso (hSess hf).choose_spec.some g ≪≫ ?_
  exact Functor.pullbackFiberCompIso x f g

end CompEssSurj

/-! ### The morphisms of `u_pp 𝒮` written out, and the image of an object under `Φ` -/

section CommaHom

universe v

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v} 𝒮] {𝒮' : Type u₄} [Category.{v} 𝒮']
  (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒞) (p' : 𝒮' ⥤ 𝒞) {G : 𝒮 ⥤ 𝒮'}

/-- The identification `u(p(a)) = u(p'(G a))` supplied by `G ⋙ p' = p`. -/
lemma comp_obj_eq (hG : G ⋙ p' = p) (a : 𝒮) : u.obj (p.obj a) = u.obj (p'.obj (G.obj a)) :=
  congrArg u.obj (Functor.congr_obj hG.symm a)

/-- The structure morphism of `Φ Z` is that of `Z`, transported along `u(p(a)) = u(p'(G a))`. -/
lemma commaMapOver_obj_hom (hG : G ⋙ p' = p) (Z : Comma (𝟭 𝒟) (p ⋙ u)) :
    ((commaMapOver u hG).obj Z).hom = Z.hom ≫ eqToHom (comp_obj_eq u p p' hG Z.right) := by
  simp [eqToHom_app]

/-- `Φ` sends `(V, a, ψ)` to `(V, G a, ψ)`, the `𝒟`-component being unchanged and the structure
morphism transported along `u(p(a)) = u(p'(G a))`. -/
lemma commaMapOver_obj_mk (hG : G ⋙ p' = p) (V : 𝒟) (a : 𝒮) (ψ : V ⟶ u.obj (p.obj a)) :
    (commaMapOver u hG).obj (Comma.mk V a ψ) =
      (Comma.mk V (G.obj a) (ψ ≫ eqToHom (comp_obj_eq u p p' hG a)) :
        Comma (𝟭 𝒟) (p' ⋙ u)) := by
  refine congrArg (Comma.mk V (G.obj a)) ?_
  simp [eqToHom_app]

/-- `Φ` transports the compatibility condition of a morphism of `u_pp 𝒮`: the `𝒮'`-side condition
for `G α` is the `𝒮`-side condition for `α`, composed with the identification
`u(p(c)) = u(p'(G c))`. -/
lemma commaCond_map (hG : G ⋙ p' = p) {d c : 𝒮} (α : d ⟶ c) {V' : 𝒟}
    (χ : V' ⟶ u.obj (p.obj d)) :
    (χ ≫ eqToHom (comp_obj_eq u p p' hG d)) ≫ (p' ⋙ u).map (G.map α) =
      (χ ≫ (p ⋙ u).map α) ≫ eqToHom (comp_obj_eq u p p' hG c) := by
  have h : p'.map (G.map α) = eqToHom (Functor.congr_obj hG d) ≫ p.map α ≫
      eqToHom (Functor.congr_obj hG c).symm := Functor.congr_hom hG α
  rw [Functor.comp_map, h]
  simp only [eqToHom_map, Functor.map_comp, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rfl

end CommaHom

section CommaHomMk

universe v

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v} 𝒮] (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)

namespace Comma

/-- The morphism `(V', d, χ) ⟶ (V, c, ψ)` of `u_pp 𝒮` with `𝒟`-component `β` and `𝒮`-component
`α`, written out from the compatibility `χ ∘ u(p α) = β ∘ ψ`. -/
def commaHomMk {d c : 𝒮} (α : d ⟶ c) {V' V : 𝒟} (β : V' ⟶ V) (χ : V' ⟶ u.obj (p.obj d))
    (ψ : V ⟶ u.obj (p.obj c)) (h : χ ≫ (p ⋙ u).map α = β ≫ ψ) :
    (Comma.mk V' d χ : Comma (𝟭 𝒟) (p ⋙ u)) ⟶
      (Comma.mk V c ψ : Comma (𝟭 𝒟) (p ⋙ u)) where
  left := β
  right := α
  w := by simpa using h.symm

/-- The `𝒟`-component of `Comma.commaHomMk` is `β`. -/
@[simp]
lemma commaHomMk_left {d c : 𝒮} (α : d ⟶ c) {V' V : 𝒟} (β : V' ⟶ V) (χ : V' ⟶ u.obj (p.obj d))
    (ψ : V ⟶ u.obj (p.obj c)) (h : χ ≫ (p ⋙ u).map α = β ≫ ψ) :
    (commaHomMk p u α β χ ψ h).left = β := rfl

/-- The `𝒮`-component of `Comma.commaHomMk` is `α`. -/
@[simp]
lemma commaHomMk_right {d c : 𝒮} (α : d ⟶ c) {V' V : 𝒟} (β : V' ⟶ V) (χ : V' ⟶ u.obj (p.obj d))
    (ψ : V ⟶ u.obj (p.obj c)) (h : χ ≫ (p ⋙ u).map α = β ≫ ψ) :
    (commaHomMk p u α β χ ψ h).right = α := rfl

/-- `(β, α)` factors as the morphism `(id, α)` with identity `𝒟`-component followed by the
reindexing morphism `(β, id)`. -/
lemma commaHomMk_eq_comp {d c : 𝒮} (α : d ⟶ c) {V' V : 𝒟} (β : V' ⟶ V)
    (χ : V' ⟶ u.obj (p.obj d)) (ψ : V ⟶ u.obj (p.obj c)) (h : χ ≫ (p ⋙ u).map α = β ≫ ψ) :
    commaHomMk p u α β χ ψ h =
      idBaseHomTo p u α χ (β ≫ ψ) h ≫
        baseChangeHom p u (Comma.mk V c ψ : Comma (𝟭 𝒟) (p ⋙ u)) β :=
  Comma.hom_ext _ _ (by simp) (by simp)

end Comma

end CommaHomMk

end CategoryTheory

end
