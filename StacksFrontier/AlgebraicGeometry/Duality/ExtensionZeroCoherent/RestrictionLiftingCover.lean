module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTargetTriangle
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtensionCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictFunctorOpensRange
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingColimit
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.UnboundedMayerVietorisTriangle

/-!
# The identification of Stacks 0G2H is local on the ambient scheme

Let `X` be a Noetherian scheme covered by two opens `V` and `W`, let `U` be an open of `X`, and
let `(F_n)` be an inverse system in `D^b_{Coh}(𝒪_X)`. Write `CategoryTheory.RestrictionLifting`
for the elementwise form of the identification

`colim_n Hom_X(F_n, N) = colim_n Hom_U(F_n|_U, N|_U)`

of [Stacks, Tag 0G2H]. This file proves that if the identification holds for the restricted
systems `(F_n|_V)`, `(F_n|_W)` and `(F_n|_{V ∩ W})` with respect to `U ∩ V`, `U ∩ W` and
`U ∩ V ∩ W`, then it holds for `(F_n)` with respect to `U`. This is the five-lemma step of the
proof of [Stacks, Tag 0G4T], which there is a diagram chase in the Mayer--Vietoris sequence of
[Stacks, Tag 08BW].

## The argument

The chase is run in the target. For `N` in `D^b_{Coh}(𝒪_X)` the Mayer--Vietoris sequence of a
K-injective complex `J` with injective terms representing `N[-1]` is short exact
([Stacks, Tag 01EA]), so it gives a distinguished triangle

`N[-1] ⟶ j_{V*}(J|_V) ⊕ j_{W*}(J|_W) ⟶ j_{V∩W*}(J|_{V∩W}) ⟶ N`

in `D(𝒪_X)` ([Stacks, Tag 08BV]), and the five lemma of
`CategoryTheory.restrictionLifting_target_triangle` reduces the claim to the terms
`P = j_{O*}(J|_O)`, for `O` one of the three opens, and their shifts. Such a `P` is *local for
`O`*: it is `Rj_{O*}` of `J|_O` because `J|_O` is K-injective ([Stacks, Tags 08BS, 070K]), and
the counit of `j_O^* ⊣ Rj_{O*}` is invertible, so restriction
`Hom_X(E, P) ⟶ Hom_O(E|_O, P|_O)` is bijective for every `E`. Its restriction `P|_U` is local
for `U ∩ O` in the same way, by base change of direct images along the open immersion
`U ⟶ X`. In the square

`Hom_X(F_n, P) ⟶ Hom_U(F_n|_U, P|_U)`
`Hom_O(F_n|_O, P|_O) ⟶ Hom_{U∩O}(F_n|_{U∩O}, P|_{U∩O})`

of restriction maps both vertical arrows are therefore bijective, and the bottom row is the
hypothesis on `O` at the object `P|_O ≅ N[-1]|_O` of `D^b_{Coh}(𝒪_O)`. This is
`CategoryTheory.RestrictionLifting.of_bijective_map`.

## Main results

* `CategoryTheory.RestrictionLifting.of_bijective_map`: the transfer through such a square.
* `CategoryTheory.RestrictionLifting.of_retract_sum`: the identification for a direct sum.
* `AlgebraicGeometry.restrictionLifting_pushRestrict`: the identification against `j_{O*}(J|_O)`.
* `AlgebraicGeometry.restrictionLifting_of_cover`: **the identification is local**.

## Implementation notes

Everything is at `CategoryTheory.HasDerivedCategory.standard`, the model of
`AlgebraicGeometry.BoundedCoherentDerived`. The library's Mayer--Vietoris triangle of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/UnboundedMayerVietorisTriangle.lean` is
stated at the locally small model, so only its model-free parts are used here: the short exact
sequence of complexes and its middle bicone.

## References

* [Stacks Project, Tag 0G4T](https://stacks.math.columbia.edu/tag/0G4T)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open InverseSequence

attribute [local instance 10000] HasDerivedCategory.standard

universe v u₁ u₂ u₃ u₄ u

namespace CategoryTheory

section Transfer

variable {𝒟 : Type u₁} [Category.{v} 𝒟] {𝒞 : Type u₂} [Category.{v} 𝒞]
  {𝒟' : Type u₃} [Category.{v} 𝒟'] {𝒞' : Type u₄} [Category.{v} 𝒞']

/-- **`CategoryTheory.RestrictionLifting` through a square of restrictions which are bijective on
morphisms into the target.** Let `S ⋙ R' ≅ R ⋙ S'` be a commutative square of functors and let
`P` be an object such that `S` is bijective on morphisms into `P` and `S'` is bijective on
morphisms into `R P`. Then the identification for `(S F_n)` against `S P` with respect to `R'`
gives it for `(F_n)` against `P` with respect to `R`. -/
public lemma RestrictionLifting.of_bijective_map {F : ℕᵒᵖ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} {S : 𝒟 ⥤ 𝒟'}
    {R' : 𝒟' ⥤ 𝒞'} {S' : 𝒞 ⥤ 𝒞'} (e : S ⋙ R' ≅ R ⋙ S') {P : 𝒟}
    (hS : ∀ E : 𝒟, Function.Bijective (fun f : E ⟶ P => S.map f))
    (hS' : ∀ E : 𝒞, Function.Bijective (fun f : E ⟶ R.obj P => S'.map f))
    (h : RestrictionLifting (F ⋙ S) R' (S.obj P)) : RestrictionLifting F R P := by
  have nat : ∀ {A B : 𝒟} (f : A ⟶ B),
      R'.map (S.map f) ≫ e.hom.app B = e.hom.app A ≫ S'.map (R.map f) :=
    fun f => e.hom.naturality f
  have key : ∀ {A B : 𝒟} (f : A ⟶ B),
      S'.map (R.map f) = e.inv.app A ≫ R'.map (S.map f) ≫ e.hom.app B := fun f => by
    rw [nat f, Iso.inv_hom_id_app_assoc]
  constructor
  · intro n g
    obtain ⟨m, hm, f, hf⟩ :=
      h.lift n (e.hom.app (F.obj (op n)) ≫ S'.map g ≫ e.inv.app P)
    obtain ⟨f₀, rfl⟩ := (hS _).2 f
    refine ⟨m, hm, f₀, (hS' _).1 ?_⟩
    show S'.map (R.map f₀) = S'.map (R.map (tr F hm) ≫ g)
    have hf' : R'.map (S.map f₀) = R'.map (S.map (tr F hm)) ≫
        e.hom.app (F.obj (op n)) ≫ S'.map g ≫ e.inv.app P := hf
    rw [key, hf', S'.map_comp, key]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  · intro n f g hfg
    have h' : R'.map (S.map f) = R'.map (S.map g) := by
      have hf := key f
      have hg := key g
      rw [hfg] at hf
      simpa only [Category.assoc, cancel_epi, cancel_mono] using hf.symm.trans hg
    obtain ⟨m, hm, he⟩ := h.eq n (S.map f) (S.map g) h'
    refine ⟨m, hm, (hS _).1 ?_⟩
    show S.map (tr F hm ≫ f) = S.map (tr F hm ≫ g)
    rw [S.map_comp, S.map_comp]
    exact he

/-- **`CategoryTheory.RestrictionLifting` for a direct sum.** If `P` is a direct sum of `P₁` and
`P₂`, in the sense that `p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 P`, then the identification against `P₁` and
against `P₂` gives it against `P`. -/
public lemma RestrictionLifting.of_retract_sum [Preadditive 𝒟] [Preadditive 𝒞]
    {F : ℕᵒᵖ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} [R.Additive] {P P₁ P₂ : 𝒟} (p₁ : P ⟶ P₁) (p₂ : P ⟶ P₂)
    (i₁ : P₁ ⟶ P) (i₂ : P₂ ⟶ P) (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 P)
    (h₁ : RestrictionLifting F R P₁) (h₂ : RestrictionLifting F R P₂) :
    RestrictionLifting F R P where
  lift n g := by
    obtain ⟨m₁, hm₁, f₁, hf₁⟩ := h₁.lift n (g ≫ R.map p₁)
    obtain ⟨m₂, hm₂, f₂, hf₂⟩ := h₂.lift n (g ≫ R.map p₂)
    have l₁ : m₁ ≤ max m₁ m₂ := le_max_left _ _
    have l₂ : m₂ ≤ max m₁ m₂ := le_max_right _ _
    have hn : n ≤ max m₁ m₂ := hm₁.trans l₁
    refine ⟨max m₁ m₂, hn, tr F l₁ ≫ f₁ ≫ i₁ + tr F l₂ ≫ f₂ ≫ i₂, ?_⟩
    rw [R.map_add, R.map_comp, R.map_comp, R.map_comp, R.map_comp, hf₁, hf₂]
    calc R.map (tr F l₁) ≫ (R.map (tr F hm₁) ≫ g ≫ R.map p₁) ≫ R.map i₁ +
          R.map (tr F l₂) ≫ (R.map (tr F hm₂) ≫ g ≫ R.map p₂) ≫ R.map i₂
        = R.map (tr F l₁ ≫ tr F hm₁) ≫ g ≫ R.map p₁ ≫ R.map i₁ +
          R.map (tr F l₂ ≫ tr F hm₂) ≫ g ≫ R.map p₂ ≫ R.map i₂ := by
          simp only [R.map_comp, Category.assoc]
      _ = R.map (tr F hn) ≫ g ≫ (R.map p₁ ≫ R.map i₁ + R.map p₂ ≫ R.map i₂) := by
          rw [tr_comp F l₁ hm₁, tr_comp F l₂ hm₂, Preadditive.comp_add, Preadditive.comp_add]
      _ = R.map (tr F hn) ≫ g := by
          rw [← R.map_comp, ← R.map_comp, ← R.map_add, htot, R.map_id, Category.comp_id]
  eq n f g hfg := by
    obtain ⟨m₁, hm₁, he₁⟩ := h₁.eq n (f ≫ p₁) (g ≫ p₁) (by rw [R.map_comp, R.map_comp, hfg])
    obtain ⟨m₂, hm₂, he₂⟩ := h₂.eq n (f ≫ p₂) (g ≫ p₂) (by rw [R.map_comp, R.map_comp, hfg])
    have l₁ : m₁ ≤ max m₁ m₂ := le_max_left _ _
    have l₂ : m₂ ≤ max m₁ m₂ := le_max_right _ _
    have hn : n ≤ max m₁ m₂ := hm₁.trans l₁
    refine ⟨max m₁ m₂, hn, ?_⟩
    have expand : ∀ x : F.obj (op n) ⟶ P, tr F hn ≫ x =
        tr F l₁ ≫ (tr F hm₁ ≫ x ≫ p₁) ≫ i₁ + tr F l₂ ≫ (tr F hm₂ ≫ x ≫ p₂) ≫ i₂ := fun x =>
      calc tr F hn ≫ x = tr F hn ≫ x ≫ (p₁ ≫ i₁ + p₂ ≫ i₂) := by rw [htot, Category.comp_id]
        _ = _ := by
          rw [Preadditive.comp_add, Preadditive.comp_add]
          congr 1
          · rw [← tr_comp F l₁ hm₁]
            simp only [Category.assoc]
          · rw [← tr_comp F l₂ hm₂]
            simp only [Category.assoc]
    rw [expand f, expand g, he₁, he₂]

end Transfer

section Bijective

variable {𝒟 : Type u₁} [Category.{v} 𝒟] {𝒞 : Type u₂} [Category.{v} 𝒞]

/-- Bijectivity of a functor on morphisms into an object only depends on the object up to
isomorphism. -/
public lemma bijective_map_of_iso_target (L : 𝒟 ⥤ 𝒞) {P P' : 𝒟} (e : P ≅ P')
    (h : ∀ E : 𝒟, Function.Bijective (fun f : E ⟶ P => L.map f)) (E : 𝒟) :
    Function.Bijective (fun f : E ⟶ P' => L.map f) := by
  constructor
  · intro f g hfg
    have hfg' : L.map (f ≫ e.inv) = L.map (g ≫ e.inv) := by
      simp only [L.map_comp]
      exact congrArg (· ≫ L.map e.inv) hfg
    simpa using congrArg (· ≫ e.hom) ((h E).1 hfg')
  · intro y
    obtain ⟨f, hf⟩ := (h E).2 (y ≫ L.map e.inv)
    refine ⟨f ≫ e.hom, ?_⟩
    show L.map (f ≫ e.hom) = y
    have hf' : L.map f = y ≫ L.map e.inv := hf
    rw [L.map_comp, hf', Category.assoc, ← L.map_comp, e.inv_hom_id, L.map_id, Category.comp_id]

/-- **A left adjoint with invertible counit is bijective on morphisms into the image of the right
adjoint.** If `adj : L ⊣ G` has invertible counit, then `L` is bijective on morphisms into any
object isomorphic to some `G M`: composing with the counit, `L` becomes the adjunction
bijection. -/
public lemma bijective_map_of_isIso_counit {L : 𝒟 ⥤ 𝒞} {G : 𝒞 ⥤ 𝒟} (adj : L ⊣ G)
    [IsIso adj.counit] {P : 𝒟} {M : 𝒞} (e : P ≅ G.obj M) (E : 𝒟) :
    Function.Bijective (fun f : E ⟶ P => L.map f) := by
  refine bijective_map_of_iso_target L e.symm (fun E => ?_) E
  have hadj : Function.Bijective (fun f : E ⟶ G.obj M => L.map f ≫ adj.counit.app M) := by
    have hfun : (fun f : E ⟶ G.obj M => L.map f ≫ adj.counit.app M) =
        ⇑(adj.homEquiv E M).symm := funext fun f => by simp [Adjunction.homEquiv_counit]
    rw [hfun]
    exact (adj.homEquiv E M).symm.bijective
  have hε : Function.Bijective (fun x : L.obj E ⟶ L.obj (G.obj M) => x ≫ adj.counit.app M) :=
    ⟨fun a b hab => (cancel_mono (adj.counit.app M)).1 hab,
      fun y => ⟨y ≫ inv (adj.counit.app M), by simp⟩⟩
  exact (Function.Bijective.of_comp_iff' hε _).1 hadj

/-- **Bijectivity on morphisms into an object transfers along a factorization through a fully
faithful functor.** If `S₁ ≅ S₂ ⋙ E` with `E` fully faithful and `S₁` is bijective on morphisms
into `P`, then so is `S₂`. -/
public lemma bijective_map_of_natIso_comp {𝒞₂ : Type u₃} [Category.{v} 𝒞₂] {S₁ : 𝒟 ⥤ 𝒞}
    {S₂ : 𝒟 ⥤ 𝒞₂} {E : 𝒞₂ ⥤ 𝒞} [E.Full] [E.Faithful] (α : S₁ ≅ S₂ ⋙ E) {P : 𝒟}
    (h : ∀ A : 𝒟, Function.Bijective (fun f : A ⟶ P => S₁.map f)) (A : 𝒟) :
    Function.Bijective (fun f : A ⟶ P => S₂.map f) := by
  have key : ∀ f : A ⟶ P, S₁.map f = α.hom.app A ≫ E.map (S₂.map f) ≫ α.inv.app P :=
    fun f => by
      have hn := α.hom.naturality f
      simp only [Functor.comp_map] at hn
      rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  constructor
  · intro f g hfg
    have hfg' : S₂.map f = S₂.map g := hfg
    apply (h A).1
    show S₁.map f = S₁.map g
    rw [key f, key g, hfg']
  · intro y
    obtain ⟨f, hf⟩ := (h A).2 (α.hom.app A ≫ E.map y ≫ α.inv.app P)
    have hf' : S₁.map f = α.hom.app A ≫ E.map y ≫ α.inv.app P := hf
    refine ⟨f, E.map_injective ?_⟩
    rw [key f] at hf'
    simpa only [cancel_epi, cancel_mono] using hf'

end Bijective

end CategoryTheory

namespace AlgebraicGeometry

open Stacks.Duality.OpenImmersion (derivedRestrict derivedRestrictPushforwardAdjunction)
open Stacks.Duality.Coherator (pushRestrictFunctor)

variable {X : Scheme.{u}}

section Pushforward

/-- **A K-injective complex computes `Rf_*`**, at the standard model: the unit of the total right
derived functor of direct image is invertible at a K-injective complex
([Stacks, Tag 070K]). -/
public lemma isIso_totalRightDerivedUnit_pushforward {Y : Scheme.{u}} (g : Y ⟶ X)
    (J : CochainComplex Y.Modules ℤ) [J.IsKInjective] :
    IsIso (((Stacks.Duality.homotopyPushforward g).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
        ((HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)).obj J)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (Stacks.Duality.homotopyPushforward g)
    (fun L => Scheme.Modules.exists_quasiIso_isKInjective Y L)).2 DerivedCategory.Qh
      (Stacks.Duality.derivedPushforward g) _ J inferInstance

/-- **The direct image of a K-injective complex is its derived direct image**:
`Q(g_* J) ≅ Rg_*(Q J)`. -/
public def pushforwardQIso {Y : Scheme.{u}} (g : Y ⟶ X) (J : CochainComplex Y.Modules ℤ)
    [J.IsKInjective] :
    DerivedCategory.Q.obj (((Scheme.Modules.pushforward g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) ≅
      (Stacks.Duality.derivedPushforward g).obj (DerivedCategory.Q.obj J) :=
  ((DerivedCategory.quotientCompQhIso X.Modules).app
      (((Scheme.Modules.pushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)).symm ≪≫
    @asIso _ _ _ _ _ (isIso_totalRightDerivedUnit_pushforward g J) ≪≫
    (Stacks.Duality.derivedPushforward g).mapIso
      ((DerivedCategory.quotientCompQhIso Y.Modules).app J)

/-- **Every object of `D(𝒪_X)` is represented by a K-injective complex with injective terms**
([Stacks, Tag 079P]), at the standard model. -/
public lemma exists_kInjective_Q_iso (K : DerivedCategory X.Modules) :
    ∃ J : CochainComplex X.Modules ℤ,
      (∀ n, Injective (C := SheafOfModules.{u} X.ringCatSheaf) (J.X n)) ∧ J.IsKInjective ∧
        Nonempty (DerivedCategory.Q.obj J ≅ K) := by
  let K₀ := DerivedCategory.Q.objPreimage K
  have : IsIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion X.Modules).app K₀)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact ⟨(Stacks.Injectives.kInjectiveResolutionFunctor X.Modules).obj K₀,
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective X.Modules K₀,
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective X.Modules K₀,
    ⟨(asIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion X.Modules).app K₀))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso K⟩⟩

end Pushforward

section Local

variable (U O : X.Opens)

/-- The two composites of restrictions `X ⟶ O ⟶ U ∩ O` and `X ⟶ U ⟶ U ∩ O` agree, on derived
categories. -/
public def derivedRestrictSquareIso :
    derivedRestrict O.ι ⋙ derivedRestrict (U.ι ∣_ O) ≅
      derivedRestrict U.ι ⋙ derivedRestrict (U.ι ⁻¹ᵁ O).ι :=
  letI : PreservesFiniteLimits (Scheme.Modules.restrictFunctor O.ι ⋙
      Scheme.Modules.restrictFunctor (U.ι ∣_ O)) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (Scheme.Modules.restrictFunctor O.ι ⋙
      Scheme.Modules.restrictFunctor (U.ι ∣_ O)) := comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.restrictFunctor (U.ι ⁻¹ᵁ O).ι) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.restrictFunctor (U.ι ⁻¹ᵁ O).ι) := comp_preservesFiniteColimits _ _
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      ((Scheme.Modules.restrictFunctorComp (U.ι ∣_ O) O.ι).symm ≪≫
        Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι U.ι O) ≪≫
        Scheme.Modules.restrictFunctorComp (U.ι ⁻¹ᵁ O).ι U.ι) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

/-- **`j_{O*}(J|_O)` is local for `O`**: for a K-injective complex `J`, restriction to `O` is
bijective on morphisms into `j_{O*}(J|_O)`, which is `Rj_{O*}(J|_O)`. -/
public lemma bijective_restrict_map_pushRestrict (J : CochainComplex X.Modules ℤ)
    [J.IsKInjective] (E : DerivedCategory X.Modules) :
    Function.Bijective (fun f : E ⟶ DerivedCategory.Q.obj
        (((pushRestrictFunctor O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) =>
      (derivedRestrict O.ι).map f) :=
  bijective_map_of_isIso_counit (derivedRestrictPushforwardAdjunction O.ι)
    (pushforwardQIso O.ι
      (((Scheme.Modules.restrictFunctor O.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) E

/-- The two open subschemes `O ∩ U` of `O` and `U ∩ O` of `U` are isomorphic over `U`: both are
pullbacks of `U` and `O`. -/
public def restrictInterIso : (O.ι ⁻¹ᵁ U).toScheme ≅ (U.ι ⁻¹ᵁ O).toScheme :=
  (isPullback_morphismRestrict O.ι U).isoIsPullback _ _ (isPullback_morphismRestrict U.ι O).flip

/-- The isomorphism `AlgebraicGeometry.restrictInterIso` followed by the inclusion of `U ∩ O`
into `U` is the restriction of `O ⟶ X` to `U`. -/
public lemma restrictInterIso_hom_ι :
    (restrictInterIso U O).hom ≫ (U.ι ⁻¹ᵁ O).ι = O.ι ∣_ U :=
  (isPullback_morphismRestrict O.ι U).isoIsPullback_hom_fst _ _
    (isPullback_morphismRestrict U.ι O).flip

/-- **`j_{O*}(J|_O)|_U` is local for `U ∩ O`**: by base change of direct images along `U ⟶ X` it
is the direct image along `O ∩ U ⟶ U` of a K-injective complex. -/
public lemma bijective_restrict_map_restrict_pushRestrict (J : CochainComplex X.Modules ℤ)
    [J.IsKInjective] (E : DerivedCategory U.toScheme.Modules) :
    Function.Bijective (fun f : E ⟶ (derivedRestrict U.ι).obj (DerivedCategory.Q.obj
        (((pushRestrictFunctor O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) =>
      (derivedRestrict (U.ι ⁻¹ᵁ O).ι).map f) := by
  let J' := ((Scheme.Modules.restrictFunctor O.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  let K := ((Scheme.Modules.restrictFunctor (O.ι ⁻¹ᵁ U).ι).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj J'
  have : CochainComplex.IsKInjective K :=
    Stacks.Duality.Coherator.isKInjective_restrict (O.ι ⁻¹ᵁ U) J'
  let e : (derivedRestrict U.ι).obj (DerivedCategory.Q.obj
        (((pushRestrictFunctor O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) ≅
      (Stacks.Duality.derivedPushforward (O.ι ∣_ U)).obj (DerivedCategory.Q.obj K) :=
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso O.ι U)
          (ComplexShape.up ℤ)).app J') ≪≫
      pushforwardQIso (O.ι ∣_ U) K
  have h₁ := bijective_map_of_isIso_counit (derivedRestrictPushforwardAdjunction (O.ι ∣_ U)) e
  let ε := restrictInterIso U O
  have := Scheme.Modules.isEquivalence_mapDerivedCategory_restrictFunctor_of_isIso ε.hom
  let α : derivedRestrict (O.ι ∣_ U) ≅ derivedRestrict (U.ι ⁻¹ᵁ O).ι ⋙ derivedRestrict ε.hom :=
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (Scheme.Modules.restrictFunctorCongr (restrictInterIso_hom_ι U O).symm ≪≫
          Scheme.Modules.restrictFunctorComp ε.hom (U.ι ⁻¹ᵁ O).ι) ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _
  exact bijective_map_of_natIso_comp α h₁ E

/-- `j_{O*}(J|_O)` restricted to `O` is `J|_O`. -/
public def restrictPushRestrictIso (J : CochainComplex X.Modules ℤ) :
    (derivedRestrict O.ι).obj (DerivedCategory.Q.obj
        (((pushRestrictFunctor O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) ≅
      (derivedRestrict O.ι).obj (DerivedCategory.Q.obj J) :=
  (Scheme.Modules.restrictFunctor O.ι).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorAdjCounitIso O.ι) ≪≫
        Functor.rightUnitor _) (ComplexShape.up ℤ)).app J) ≪≫
    ((Scheme.Modules.restrictFunctor O.ι).mapDerivedCategoryFactors.app J).symm

variable [IsNoetherian X]

/-- **The identification against `j_{O*}(J|_O)`.** Let `U`, `O` be opens of the Noetherian scheme
`X` and `(F_n)` an inverse system in `D^b_{Coh}(𝒪_X)` whose restriction to `O` satisfies the
identification of [Stacks, Tag 0G2H] with respect to `U ∩ O`. Then `(F_n)` satisfies it with
respect to `U` against `j_{O*}(J|_O)`, for every K-injective complex `J` representing an object of
`D^b_{Coh}(𝒪_X)`. -/
public lemma restrictionLifting_pushRestrict (F : ℕᵒᵖ ⥤ BoundedCoherentDerived X)
    (hO : ∀ N, RestrictionLifting (F ⋙ restrictBoundedCoherentLift O.ι)
      (restrictBoundedCoherentLift (U.ι ∣_ O)) N)
    (J : CochainComplex X.Modules ℤ) [J.IsKInjective] (M : BoundedCoherentDerived X)
    (eJ : DerivedCategory.Q.obj J ≅ (boundedCoherentDerived X).ι.obj M) :
    RestrictionLifting (F ⋙ (boundedCoherentDerived X).ι) (derivedRestrict U.ι)
      (DerivedCategory.Q.obj
        (((pushRestrictFunctor O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) := by
  have hc : RestrictionLifting ((F ⋙ restrictBoundedCoherentLift O.ι) ⋙
      (boundedCoherentDerived O.toScheme).ι) (derivedRestrict (U.ι ∣_ O))
      ((derivedRestrict O.ι).obj (DerivedCategory.Q.obj
        (((pushRestrictFunctor O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))) :=
    (hO ((restrictBoundedCoherentLift O.ι).obj M)).map_source
      (boundedCoherentDerived O.toScheme).ι (boundedCoherentDerived (U.ι ⁻¹ᵁ O).toScheme).ι
      (derivedRestrict (U.ι ∣_ O)) (Iso.refl _)
      ((derivedRestrict O.ι).mapIso eJ.symm ≪≫ (restrictPushRestrictIso O J).symm)
  exact RestrictionLifting.of_bijective_map (derivedRestrictSquareIso U O)
    (bijective_restrict_map_pushRestrict O J) (bijective_restrict_map_restrict_pushRestrict U O J)
    hc

end Local

/-- **[Stacks, Tag 0G2H] is local on `X`**, the five-lemma step of [Stacks, Tag 0G4T]. Let `X` be
a Noetherian scheme covered by two opens `V` and `W`, let `U` be an open of `X` and let `(F_n)` be
an inverse system in `D^b_{Coh}(𝒪_X)`. If the restricted systems `(F_n|_V)`, `(F_n|_W)` and
`(F_n|_{V ∩ W})` satisfy the identification
`colim_n Hom(F_n, N) = colim_n Hom(F_n|_{U ∩ -}, N|_{U ∩ -})` with respect to `U ∩ V`, `U ∩ W`
and `U ∩ V ∩ W`, then `(F_n)` satisfies it with respect to `U`, against every `N`. -/
public theorem restrictionLifting_of_cover [IsNoetherian X]
    (U V W : X.Opens) (hVW : V ⊔ W = ⊤) (F : ℕᵒᵖ ⥤ BoundedCoherentDerived X)
    (hV : ∀ N, RestrictionLifting (F ⋙ restrictBoundedCoherentLift V.ι)
      (restrictBoundedCoherentLift (U.ι ∣_ V)) N)
    (hW : ∀ N, RestrictionLifting (F ⋙ restrictBoundedCoherentLift W.ι)
      (restrictBoundedCoherentLift (U.ι ∣_ W)) N)
    (hVW' : ∀ N, RestrictionLifting (F ⋙ restrictBoundedCoherentLift (V ⊓ W).ι)
      (restrictBoundedCoherentLift (U.ι ∣_ (V ⊓ W))) N)
    (N : BoundedCoherentDerived X) :
    RestrictionLifting F (restrictBoundedCoherentLift U.ι) N := by
  let ι := (boundedCoherentDerived X).ι
  let Nm : BoundedCoherentDerived X := N⟦(-1 : ℤ)⟧
  obtain ⟨J, hinj, hJ, ⟨eJ⟩⟩ := exists_kInjective_Q_iso (ι.obj Nm)
  let eJ₁ : DerivedCategory.Q.obj (J⟦(1 : ℤ)⟧) ≅ ι.obj (Nm⟦(1 : ℤ)⟧) :=
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).app J ≪≫
      (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).mapIso eJ ≪≫
      ((ι.commShiftIso (1 : ℤ)).app Nm).symm
  let G : X.Opens → (CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ) :=
    fun O => (pushRestrictFunctor O).mapHomologicalComplex (ComplexShape.up ℤ)
  -- the shifted terms of the Mayer--Vietoris sequence are terms of the sequence of `J⟦1⟧`
  let shiftIso : ∀ O : X.Opens, (DerivedCategory.Q.obj ((G O).obj J))⟦(1 : ℤ)⟧ ≅
      DerivedCategory.Q.obj ((G O).obj (J⟦(1 : ℤ)⟧)) := fun O =>
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app ((G O).obj J)).symm ≪≫
      DerivedCategory.Q.mapIso (((pushRestrictFunctor O).mapCochainComplexShiftIso 1).app J).symm
  let F' := F ⋙ ι
  let R := derivedRestrict U.ι
  have hP : ∀ O : X.Opens, (∀ N, RestrictionLifting (F ⋙ restrictBoundedCoherentLift O.ι)
      (restrictBoundedCoherentLift (U.ι ∣_ O)) N) →
      RestrictionLifting F' R (DerivedCategory.Q.obj ((G O).obj J)) ∧
        RestrictionLifting F' R ((DerivedCategory.Q.obj ((G O).obj J))⟦(1 : ℤ)⟧) :=
    fun O hO => ⟨restrictionLifting_pushRestrict U O F hO J Nm eJ,
      (restrictionLifting_pushRestrict U O F hO (J⟦(1 : ℤ)⟧) (Nm⟦(1 : ℤ)⟧) eJ₁).of_iso_target
        (shiftIso O).symm⟩
  -- the Mayer--Vietoris triangle of `J`, rotated so that the term of `J` is the third vertex
  let hS := Stacks.Duality.Coherator.mvShortComplex_shortExact V W J hinj
  let T := (DerivedCategory.triangleOfSES hS).rotate
  have hT : T ∈ distTriang (DerivedCategory X.Modules) :=
    rot_of_distTriang _ (DerivedCategory.triangleOfSES_distinguished hS)
  let b := Stacks.Duality.Coherator.mvBicone V W J
  have htot : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt := by
    ext n : 1
    exact biprod.total (X := (pushRestrictFunctor V).obj (J.X n))
      (Y := (pushRestrictFunctor W).obj (J.X n))
  have htotQ : DerivedCategory.Q.map b.fst ≫ DerivedCategory.Q.map b.inl +
      DerivedCategory.Q.map b.snd ≫ DerivedCategory.Q.map b.inr = 𝟙 _ := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_add, htot, DerivedCategory.Q.map_id]
  have htotQ₁ : (DerivedCategory.Q.map b.fst)⟦(1 : ℤ)⟧' ≫ (DerivedCategory.Q.map b.inl)⟦(1 : ℤ)⟧' +
      (DerivedCategory.Q.map b.snd)⟦(1 : ℤ)⟧' ≫ (DerivedCategory.Q.map b.inr)⟦(1 : ℤ)⟧' = 𝟙 _ := by
    rw [← Functor.map_comp (shiftFunctor _ (1 : ℤ)), ← Functor.map_comp (shiftFunctor _ (1 : ℤ)),
      ← Functor.map_add, htotQ, CategoryTheory.Functor.map_id]
  obtain ⟨hPV, hPV₁⟩ := hP V hV
  obtain ⟨hPW, hPW₁⟩ := hP W hW
  obtain ⟨hPVW, hPVW₁⟩ := hP (V ⊓ W) hVW'
  have h₁ : RestrictionLifting F' R T.obj₁ :=
    RestrictionLifting.of_retract_sum _ _ _ _ htotQ hPV hPW
  have h₁' : RestrictionLifting F' R (T.obj₁⟦(1 : ℤ)⟧) :=
    RestrictionLifting.of_retract_sum _ _ _ _ htotQ₁ hPV₁ hPW₁
  have h₃ : RestrictionLifting F' R T.obj₃ :=
    restrictionLifting_target_triangle F' R hT h₁ hPVW h₁' hPVW₁
  -- the third vertex is `N`
  let topIso : (G (V ⊔ W)).obj J ≅ J :=
    (NatIso.mapHomologicalComplex (eqToIso (congrArg pushRestrictFunctor hVW) ≪≫
        Stacks.Duality.Coherator.pushRestrictTopIso.symm) (ComplexShape.up ℤ)).app J ≪≫
      (Functor.mapHomologicalComplexIdIso _ _).app J
  let e₃ : T.obj₃ ≅ ι.obj N :=
    (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).mapIso
        (DerivedCategory.Q.mapIso topIso ≪≫ eJ) ≪≫
      ((ι.commShiftIso (1 : ℤ)).app Nm).symm ≪≫
      ι.mapIso ((shiftFunctorCompIsoId (BoundedCoherentDerived X) (-1 : ℤ) 1 (by norm_num)).app N)
  exact RestrictionLifting.of_comp_fullyFaithful (boundedCoherentDerived U.toScheme).ι
    (RestrictionLifting.of_fullyFaithful_comp F ι R N (h₃.of_iso_target e₃))

end AlgebraicGeometry

end
