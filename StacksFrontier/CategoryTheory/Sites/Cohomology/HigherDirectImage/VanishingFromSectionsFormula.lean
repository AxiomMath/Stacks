module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.Algebra.Homology.RightDerivedDelta

/-!
# Vanishing of right derived functors by dimension shifting, and higher direct images computed
by a sections formula

Let `Q : 𝒜 ⥤ 𝒟` be an additive left exact functor between abelian categories, `𝒜` having enough
injectives.  The classical dimension-shifting argument (Cohomology on Sites, proof of Lemma
03F7) shows that `Rⁿ Q` vanishes in positive degrees on every object of a class `P` as soon as
every object `X` of `P` embeds into an injective `I` with cokernel again in `P`, the map
`Q I ⟶ Q (I / X)` being an epimorphism.  This file records that argument and then applies it to
a direct image of sheaves of modules `Φ : Mod(𝒪_𝒞) ⥤ Mod(𝒪_𝒟)` whose sections over every object
`y` of a covering class `B_𝒟` are the sections of its argument over an object `x(y)` of a class
`B_𝒞` — which is what an affine morphism does on objects lying over affine schemes.

## Main results

* `Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_of_effaceable`: the dimension
  shifting argument.
* `Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_cokernel_and_epi`: for a short exact
  sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective and `X` acyclic for `Q`, the cokernel is
  acyclic and `Q I ⟶ Q Q` is an epimorphism.
* `SheafOfModules.epi_of_surjective_on_covering_objects`: a morphism of sheaves of modules
  which is surjective on the sections over the objects of a class generating covering sieves is
  an epimorphism.
* `SheafOfModules.isZero_rightDerived_of_sectionsFormula`: **a direct image with a sections
  formula kills, in positive degrees, every module whose cohomology vanishes over the objects
  `x(y)`.**
* `SheafOfModules.preservesColimitsOfShape_discrete_of_sectionsFormula`: such a direct image
  commutes with coproducts as soon as sections over the objects of the two classes commute with
  coproducts.

## References

* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ r r' w

namespace Stacks.Cohomology.RightDerivedDelta

section Effaceable

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  {𝒟 : Type u₂} [Category.{v₂} 𝒟] [Abelian 𝒟] (Q : 𝒜 ⥤ 𝒟) [Q.Additive]
  [PreservesFiniteLimits Q]

/-- The image under `R⁰Q` of a morphism is an epimorphism when its image under `Q` is, for a
left exact `Q`. -/
theorem epi_rightDerived_zero_map {X Y : 𝒜} (g : X ⟶ Y) (h : Epi (Q.map g)) :
    Epi ((Q.rightDerived 0).map g) := by
  have e : (Q.rightDerived 0).map g = Q.rightDerivedZeroIsoSelf.hom.app X ≫ Q.map g ≫
      Q.rightDerivedZeroIsoSelf.inv.app Y := by
    rw [← Q.rightDerivedZeroIsoSelf.hom.naturality_assoc]
    simp
  rw [e]
  infer_instance

/-- For a left exact `Q`, the map `Q X₂ ⟶ Q X₃` is an epimorphism if `R¹Q` vanishes on `X₁`. -/
private theorem epi_map_of_isZero_rightDerived_one {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsZero ((Q.rightDerived 1).obj S.X₁)) : Epi (Q.map S.g) := by
  obtain ⟨δ, -, hex⟩ := exists_delta_exact_composableArrows₅ hS Q
  have h0 : Epi ((Q.rightDerived 0).map S.g) := ((hex 0).exact 1).epi_f (h₁.eq_of_tgt _ _)
  have e : Q.map S.g = Q.rightDerivedZeroIsoSelf.inv.app S.X₂ ≫
      (Q.rightDerived 0).map S.g ≫ Q.rightDerivedZeroIsoSelf.hom.app S.X₃ := by
    rw [Q.rightDerivedZeroIsoSelf.hom.naturality]
    simp
  rw [e]
  infer_instance

/-- **Dimension shifting** (Cohomology on Sites, proof of Lemma 03F7).  Let `P` be a class of
objects such that every member `X` sits in a short exact sequence `0 ⟶ X ⟶ I ⟶ X' ⟶ 0` with `I`
injective, `X'` again in `P`, and `Q I ⟶ Q X'` an epimorphism.  Then `Rⁿ⁺¹ Q` vanishes on `P`. -/
theorem isZero_rightDerived_succ_of_effaceable (P : 𝒜 → Prop)
    (hP : ∀ X, P X → ∃ S : ShortComplex 𝒜, S.ShortExact ∧ Injective S.X₂ ∧
      Nonempty (S.X₁ ≅ X) ∧ P S.X₃ ∧ Epi (Q.map S.g)) (n : ℕ) :
    ∀ X, P X → IsZero ((Q.rightDerived (n + 1)).obj X) := by
  induction n with
  | zero =>
    intro X hX
    obtain ⟨S, hS, hI, ⟨e⟩, -, hepi⟩ := hP X hX
    refine IsZero.of_iso ?_ ((Q.rightDerived 1).mapIso e.symm)
    exact isZero_rightDerived_succ_X₁_of_epi hS Q 0 (epi_rightDerived_zero_map Q S.g hepi)
      (Q.isZero_rightDerived_obj_injective_succ 0 S.X₂)
  | succ n ih =>
    intro X hX
    obtain ⟨S, hS, hI, ⟨e⟩, h₃, -⟩ := hP X hX
    refine IsZero.of_iso ?_ ((Q.rightDerived (n + 1 + 1)).mapIso e.symm)
    exact isZero_rightDerived_succ_X₁_of_injective hS Q n (ih S.X₃ h₃)

/-- For a short exact sequence `0 ⟶ X ⟶ I ⟶ X' ⟶ 0` with `I` injective and `X` acyclic for `Q`
in positive degrees, the cokernel `X'` is acyclic for `Q` in positive degrees and
`Q I ⟶ Q X'` is an epimorphism. -/
theorem isZero_rightDerived_cokernel_and_epi {S : ShortComplex 𝒜} (hS : S.ShortExact)
    [Injective S.X₂] (hX : ∀ n : ℕ, 0 < n → IsZero ((Q.rightDerived n).obj S.X₁)) :
    (∀ n : ℕ, 0 < n → IsZero ((Q.rightDerived n).obj S.X₃)) ∧ Epi (Q.map S.g) := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact isZero_rightDerived_X₃_of_injective hS Q m (hX (m + 1 + 1) (by omega))
  · obtain ⟨δ, -, hex⟩ := exists_delta_exact_composableArrows₅ hS Q
    exact epi_map_of_isZero_rightDerived_one Q hS (hX 1 one_pos)

/-- **A left exact functor carries a short exact sequence to a short exact sequence as soon as
its first right derived functor vanishes on the first term.**  The long exact sequence makes
`Q X₂ ⟶ Q X₃` an epimorphism, and left exactness does the rest. -/
theorem shortExact_map_of_isZero_rightDerived_one {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsZero ((Q.rightDerived 1).obj S.X₁)) : (S.map Q).ShortExact := by
  have := hS.mono_f
  exact { exact := hS.exact.map_of_mono_of_preservesKernel Q hS.mono_f inferInstance
          mono_f := Q.map_mono S.f
          epi_g := epi_map_of_isZero_rightDerived_one Q hS h₁ }

end Effaceable

end Stacks.Cohomology.RightDerivedDelta

namespace SheafOfModules

/-- Sections over an object are additive: they are the evaluation of the underlying presheaf of
modules. -/
local instance additive_evaluation_local {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) (X : Cᵒᵖ) :
    (evaluation.{w} R X).Additive :=
  inferInstanceAs ((forget R ⋙ PresheafOfModules.evaluation R.obj X).Additive)

section Epi

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]

/-- **A morphism of sheaves of modules which is surjective on the sections over the objects of a
covering class is an epimorphism.**  The class `B` covers when every sieve containing all the
arrows out of members of `B` is a covering sieve; then the image sieve of every section contains
such a sieve, so the underlying morphism of abelian sheaves is locally surjective. -/
theorem epi_of_surjective_on_covering_objects (B : C → Prop)
    (hB : ∀ (U : C) (T : Sieve U), (∀ ⦃V : C⦄ (f : V ⟶ U), B V → T f) → T ∈ J U)
    {M N : SheafOfModules.{w} R} (φ : M ⟶ N)
    (hφ : ∀ V : C, B V → Function.Surjective (φ.val.app (op V))) : Epi φ := by
  have : Presheaf.IsLocallySurjective J ((toSheaf R).map φ).hom :=
    ⟨fun s => hB _ _ fun V f hV => hφ V hV (N.val.map f.op s)⟩
  exact (toSheaf R).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

/-- **A morphism of sheaves of modules which is injective on the sections over the objects of a
covering class is a monomorphism.**  A section killed by the morphism is killed after
restriction to every member of the class, hence is zero by separatedness. -/
theorem mono_of_injective_on_covering_objects (B : C → Prop)
    (hB : ∀ (U : C) (T : Sieve U), (∀ ⦃V : C⦄ (f : V ⟶ U), B V → T f) → T ∈ J U)
    {M N : SheafOfModules.{w} R} (φ : M ⟶ N)
    (hφ : ∀ V : C, B V → Function.Injective (φ.val.app (op V))) : Mono φ := by
  have hinj : ∀ U : C, Function.Injective (φ.val.app (op U)) := by
    intro U
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro s hs
    let T : Sieve U := ⟨fun V f => M.val.map f.op s = 0, fun {V W f} hf g => by
      show M.val.map (g ≫ f).op s = 0
      rw [op_comp, M.val.map_comp, ModuleCat.comp_apply]
      change M.val.map g.op (M.val.map f.op s) = 0
      rw [show M.val.map f.op s = 0 from hf]
      exact (M.val.map g.op).hom.map_zero⟩
    have hT : T ∈ J U := hB U T fun V f hV => hφ V hV (by
      have h := PresheafOfModules.naturality_apply φ.val f.op s
      change φ.val.app (op V) (M.val.map f.op s) = φ.val.app (op V) 0
      rw [h, show φ.val.app (op U) s = 0 from hs]
      exact ((N.val.map f.op).hom.map_zero).trans (φ.val.app (op V)).hom.map_zero.symm)
    have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj
        ((toSheaf R).obj M)).2).isSeparated T hT
    refine hsep.ext (t₁ := s) (t₂ := (0 : M.val.obj (op U))) fun V f hf => ?_
    change M.val.map f.op s = M.val.map f.op 0
    rw [map_zero]
    exact hf
  constructor
  intro Z a b hab
  ext U x
  exact hinj U.unop (by simpa using congrArg (fun g => g.val.app U x) hab)

end Epi

section SectionsFormula

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} R)]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {R' : Sheaf K RingCat.{r'}}
  [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]

/-- **A direct image with a sections formula kills, in positive degrees, every module whose
cohomology vanishes over the objects of the formula.**

Let `Φ : Mod(𝒪_𝒞) ⥤ Mod(𝒪_𝒟)` be additive and left exact, let `B` be a covering class of objects
of `𝒟`, and suppose that for each `y` in `B` the sections of `Φ M` over `y` are, naturally in
`M`, the sections of `M` over an object `x y` of `𝒞`.  If `Rⁿ Γ(x y, A) = 0` for every `y` in
`B` and every `n > 0`, then `Rⁿ Φ A = 0` for every `n > 0`.

The class of such `A` is effaceable for `Φ` (dimension shifting): for `0 ⟶ A ⟶ I ⟶ A' ⟶ 0` with
`I` injective the long exact sequences of the functors `Γ(x y, -)` show that `A'` is again in
the class and that `Γ(x y, I) ⟶ Γ(x y, A')` is onto, hence so is `Γ(y, Φ I) ⟶ Γ(y, Φ A')`, and a
morphism of sheaves onto on a covering class of objects is an epimorphism. -/
theorem isZero_rightDerived_of_sectionsFormula
    (Φ : SheafOfModules.{w} R ⥤ SheafOfModules.{w} R') [Φ.Additive] [PreservesFiniteLimits Φ]
    (B : D → Prop)
    (hB : ∀ (U : D) (T : Sieve U), (∀ ⦃V : D⦄ (f : V ⟶ U), B V → T f) → T ∈ K U)
    (x : ∀ y : D, B y → C)
    (e : ∀ (y : D) (hy : B y), Φ ⋙ toSheaf R' ⋙ (sheafSections K AddCommGrpCat.{w}).obj (op y) ≅
      toSheaf R ⋙ (sheafSections J AddCommGrpCat.{w}).obj (op (x y hy)))
    (A : SheafOfModules.{w} R)
    (hA : ∀ (y : D) (hy : B y) (n : ℕ), 0 < n →
      IsZero (((evaluation R (op (x y hy))).rightDerived n).obj A))
    (n : ℕ) (hn : 0 < n) : IsZero ((Φ.rightDerived n).obj A) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_of_effaceable Φ
    (fun X => ∀ (y : D) (hy : B y) (n : ℕ), 0 < n →
      IsZero (((evaluation R (op (x y hy))).rightDerived n).obj X)) ?_ m A hA
  intro X hX
  let S := ShortComplex.mk (Injective.ι X) (cokernel.π (Injective.ι X)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hI : Injective S.X₂ := inferInstanceAs (Injective (Injective.under X))
  have key := fun (y : D) (hy : B y) =>
    Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_cokernel_and_epi
      (evaluation R (op (x y hy))) hS (hX y hy)
  refine ⟨S, hS, hI, ⟨Iso.refl _⟩, fun y hy => (key y hy).1, ?_⟩
  refine epi_of_surjective_on_covering_objects B hB _ fun y hy => ?_
  have hsurj : Function.Surjective ((evaluation R (op (x y hy))).map S.g) :=
    (ModuleCat.epi_iff_surjective _).1 (key y hy).2
  intro s
  obtain ⟨t, ht⟩ := hsurj (((e y hy).hom.app S.X₃) s)
  refine ⟨((e y hy).inv.app S.X₂) t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso ((e y hy).hom.app S.X₃)).1
  have hnat := ConcreteCategory.congr_hom ((e y hy).hom.naturality S.g)
    (((e y hy).inv.app S.X₂) t)
  have hinv := ConcreteCategory.congr_hom ((e y hy).inv_hom_id_app S.X₂) t
  simp only [ConcreteCategory.comp_apply, Functor.comp_map] at hnat hinv
  refine hnat.trans ?_
  exact (congrArg (fun z => ((toSheaf R ⋙ (sheafSections J AddCommGrpCat.{w}).obj
    (op (x y hy))).map S.g) z) hinv).trans ht

omit [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} R)] in
/-- **A direct image with a sections formula commutes with coproducts** as soon as sections over
the objects `y` of the covering class and over the objects `x y` do: the comparison map
`∐ Φ Fⱼ ⟶ Φ (∐ Fⱼ)` is then bijective on the sections over every `y`, hence an isomorphism. -/
theorem preservesColimit_discrete_of_sectionsFormula
    (Φ : SheafOfModules.{w} R ⥤ SheafOfModules.{w} R')
    (B : D → Prop)
    (hB : ∀ (U : D) (T : Sieve U), (∀ ⦃V : D⦄ (f : V ⟶ U), B V → T f) → T ∈ K U)
    (x : ∀ y : D, B y → C)
    (e : ∀ (y : D) (hy : B y), Φ ⋙ toSheaf R' ⋙ (sheafSections K AddCommGrpCat.{w}).obj (op y) ≅
      toSheaf R ⋙ (sheafSections J AddCommGrpCat.{w}).obj (op (x y hy)))
    {ι : Type w} (F : ι → SheafOfModules.{w} R) [HasCoproduct F]
    [HasCoproduct fun j => Φ.obj (F j)]
    (hD : ∀ (y : D), B y → PreservesColimit (Discrete.functor fun j => Φ.obj (F j))
      (toSheaf R' ⋙ (sheafSections K AddCommGrpCat.{w}).obj (op y)))
    (hC : ∀ (y : D) (hy : B y), PreservesColimit (Discrete.functor F)
      (toSheaf R ⋙ (sheafSections J AddCommGrpCat.{w}).obj (op (x y hy)))) :
    PreservesColimit (Discrete.functor F) Φ := by
  have key : ∀ (y : D) (hy : B y), IsIso ((toSheaf R' ⋙
      (sheafSections K AddCommGrpCat.{w}).obj (op y)).map (sigmaComparison Φ F)) := by
    intro y hy
    let G := toSheaf R' ⋙ (sheafSections K AddCommGrpCat.{w}).obj (op y)
    have : PreservesColimit (Discrete.functor fun j => Φ.obj (F j)) G := hD y hy
    have : PreservesColimit (Discrete.functor F) (Φ ⋙ G) :=
      have := hC y hy
      preservesColimit_of_natIso _ (e y hy).symm
    have h1 : IsIso (sigmaComparison G fun j => Φ.obj (F j)) := inferInstance
    have h2 : IsIso (sigmaComparison (Φ ⋙ G) F) := inferInstance
    have hfac : sigmaComparison (Φ ⋙ G) F =
        sigmaComparison G (fun j => Φ.obj (F j)) ≫ G.map (sigmaComparison Φ F) := by
      refine Sigma.hom_ext _ _ fun j => ?_
      simp only [Functor.comp_obj, ι_comp_sigmaComparison,
        ι_comp_sigmaComparison_assoc, ← G.map_comp]
      exact ι_comp_sigmaComparison (Φ ⋙ G) F j
    exact IsIso.of_isIso_fac_left hfac.symm
  have hbij : ∀ (y : D) (hy : B y),
      Function.Bijective ((sigmaComparison Φ F).val.app (op y)) := fun y hy => by
    have := key y hy
    exact ConcreteCategory.bijective_of_isIso
      ((toSheaf R' ⋙ (sheafSections K AddCommGrpCat.{w}).obj (op y)).map
        (sigmaComparison Φ F))
  have : Mono (sigmaComparison Φ F) :=
    mono_of_injective_on_covering_objects B hB _ fun y hy => (hbij y hy).1
  have : Epi (sigmaComparison Φ F) :=
    epi_of_surjective_on_covering_objects B hB _ fun y hy => (hbij y hy).2
  have : IsIso (sigmaComparison Φ F) := isIso_of_mono_of_epi _
  exact PreservesCoproduct.of_iso_comparison Φ F

end SectionsFormula

end SheafOfModules
