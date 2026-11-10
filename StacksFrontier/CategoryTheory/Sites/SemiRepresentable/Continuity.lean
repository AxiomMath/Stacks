module

public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Site
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Defs

/-!
# Continuity of the component functors of a semi-representable localization

Let `(C, J)` be a site. For a semi-representable object `K` of `C`, the localization functor
`j : C / K ⥤ C` is continuous and cocontinuous, and for a morphism `K ⟶ L` of semi-representable
objects the relocalization functor `v : C / K ⥤ C / L` is continuous and cocontinuous. If in
addition the covering families of `J` admit pullbacks, both functors have property P of
Stacks 09W7: a covering family of the target pulls back, along an arrow out of the image of the
functor, to a family of *relative* pullbacks — objects of the source site representing the
functor of compatible pairs — and the resulting family covers.

Everything is proved one component at a time. The component inclusion
`C / K.obj i ⥤ C / K` is continuous (`incl_isContinuous`), a presheaf on `C / K` is a sheaf as
soon as its restriction to every component is (`isSheaf_componentwise`), and on the `i`-th
component the localization and relocalization functors are `Over.forget (K.obj i)` and
`Over.map (f.φ i)`, whose continuity and cocontinuity are already known. For property P the
relative pullback is built from an honest fibre product in `C`, taken over the structural map of
the component, and the covering condition is transported through
`CategoryTheory.Sieve.overEquiv`.

## Main results

* `CategoryTheory.SemiRepresentable.isSheaf_componentwise`: a presheaf on `C / K` is a sheaf for
  the componentwise topology if its restriction to each component is a sheaf.
* `CategoryTheory.SemiRepresentable.incl_isContinuous`: the inclusion of a component is
  continuous.
* `CategoryTheory.SemiRepresentable.LocalizationSites.localizationFunctor_isContinuous`,
  `CategoryTheory.SemiRepresentable.LocalizationSites.localizationFunctor_isCocontinuous` and
  `CategoryTheory.SemiRepresentable.LocalizationSites.localizationFunctor_hasCoverPullbacks`:
  the three assertions of Stacks 0D85 for `j : C / K ⥤ C`.
* `CategoryTheory.SemiRepresentable.LocalizationSites.relocalizationFunctor_isContinuous`,
  `CategoryTheory.SemiRepresentable.LocalizationSites.relocalizationFunctor_isCocontinuous` and
  `CategoryTheory.SemiRepresentable.LocalizationSites.relocalizationFunctor_hasCoverPullbacks`:
  the same three assertions for `v : C / K ⥤ C / L`.

## Implementation notes

The three conclusions of Stacks 0D85 are separate declarations so that each can be used on its
own, and the two continuity statements are instances. Property P is spelled out: it asserts the
universal property of the relative pullback `U ×_{g, V, f} W` of Stacks 09W7, whose universal
property is tested only on objects of the source site, together with the covering condition on
the projections. The site axiom that the arrows of a covering family admit pullbacks is
`CategoryTheory.Precoverage.HasPullbacks` for `J.toCoverage`.

Because an arrow of `C / K` need not stay inside a single component as written — its source and
target carry possibly different indices before `CategoryTheory.Sigma.SigmaHom` is destructured —
the relocalization argument uses the auxiliary `ComponentOverHom` to name the index equality and
the induced arrow in one component, together with the canonical isomorphism identifying the
transported object with the original one.

## References

* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 09W7](https://stacks.math.columbia.edu/tag/09W7)
-/

@[expose] public section

universe w' w v u t

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SemiRepresentable

variable {C : Type u} [Category.{v} C]

/-- A presheaf on the disjoint union `C / K` of the slice categories over the components of a
semi-representable object is a sheaf for the componentwise topology as soon as its restriction
to every component is a sheaf for the localized topology there. -/
lemma isSheaf_componentwise (J : GrothendieckTopology C) {K : FormalCoproduct.{w} C}
    (P : (ComponentOver K)ᵒᵖ ⥤ Type t)
    (h : ∀ i : K.I, Presieve.IsSheaf (J.over (K.obj i))
      ((CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i).op ⋙ P)) :
    Presieve.IsSheaf (componentwiseTopology J K) P := by
  rintro ⟨i, X⟩ S hS
  let I := CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i
  let R := S.functorPullback I
  intro x hx
  let y : R.arrows.FamilyOfElements (I.op ⋙ P) :=
    fun Y f hf => x (CategoryTheory.Sigma.SigmaHom.mk f) hf
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ heq
    exact hx (CategoryTheory.Sigma.SigmaHom.mk g₁)
      (CategoryTheory.Sigma.SigmaHom.mk g₂) hf₁ hf₂
      (congrArg CategoryTheory.Sigma.SigmaHom.mk heq)
  obtain ⟨s, hs, hu⟩ := h i R hS y hy
  refine ⟨s, ?_, ?_⟩
  · rintro Y ⟨g⟩ hf
    exact hs g hf
  · exact fun s' hs' => hu s' fun Y f hf => hs' (CategoryTheory.Sigma.SigmaHom.mk f) hf

/-- The inclusion of the `i`-th component `C / K.obj i ⥤ C / K` is continuous for the localized
topology on its source and the componentwise topology on its target. -/
lemma incl_isContinuous (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) (i : K.I) :
    (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i).IsContinuous
      (J.over (K.obj i)) (componentwiseTopology J K) := by
  let I := CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i
  have hd : ∀ {c : Over (K.obj i)} {d : ComponentOver K},
      (d ⟶ I.obj c) → Σ c', I.obj c' ≅ d := by
    rintro c ⟨j, d⟩ ⟨f⟩
    exact ⟨d, Iso.refl _⟩
  have hc : CoverPreserving (J.over (K.obj i)) (componentwiseTopology J K) I := by
    constructor
    intro X S hS
    change (S.functorPushforward I).functorPullback I ∈ J.over (K.obj i) X
    rwa [Sieve.functorPullback_functorPushforward_eq]
  exact Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed (componentwiseTopology J K) I hd) hc

/-! ### Two cancellation lemmas

Stated for an abstract category. Composition in `ComponentOver K` is found through the direct
`CategoryStruct` instance of a sigma type rather than through its `Category` instance, so a
composite written here and a composite produced by a generic `Category` lemma are equal but not
syntactically the same, and rewriting cannot mix them. Doing the algebra once in an abstract
category and applying the result with `exact` avoids the issue. -/

/-- Reassociating past an isomorphism: if `w` is `u` followed by `e⁻¹` and `m` is `e` followed by
`n`, then `w ≫ m` is `u ≫ n`. -/
private lemma comp_eq_comp_of_inv {D : Type*} [Category D] {A B Eo Yo : D}
    (u : A ⟶ Eo) (e : B ⟶ Eo) [IsIso e] (m : B ⟶ Yo) (n : Eo ⟶ Yo) (w : A ⟶ B)
    (hw : w = u ≫ inv e) (hm : m = e ≫ n) : u ≫ n = w ≫ m := by
  subst hw
  subst hm
  simp

/-- Cancelling an isomorphism against its inverse across an association. -/
private lemma comp_assoc_eq_iff {D : Type*} [Category D] {A B Eo F : D}
    (x : A ⟶ F) (y : F ⟶ B) (e : B ⟶ Eo) [IsIso e] (b : A ⟶ Eo) :
    x ≫ (y ≫ e) = b ↔ x ≫ y = b ≫ inv e := by
  rw [← Category.assoc, ← IsIso.eq_comp_inv]

/-! ### Arrows of `C / K` as arrows inside a single component

An arrow of `ComponentOver K` is a `CategoryTheory.Sigma.SigmaHom`, so its endpoints carry
indices that are only *equal*, not syntactically the same. `ComponentOverHom` names that index
equality together with the induced arrow in one component, and `componentOverHomIso` is the
canonical isomorphism undoing the transport. -/

/-- An arrow of `ComponentOver K` presented as an equality of indices together with an arrow of
the component indexed by the target. -/
private structure ComponentOverHom {K : FormalCoproduct.{w} C}
    (X Y : ComponentOver K) where
  /-- The two endpoints lie in the same component. -/
  idx : X.1 = Y.1
  /-- The arrow, read inside the component of the target. -/
  hom : (idx ▸ X.2) ⟶ Y.2

/-- Every arrow of `ComponentOver K` is of that form. -/
private def componentOverHom {K : FormalCoproduct.{w} C}
    {X Y : ComponentOver K} (f : X ⟶ Y) : ComponentOverHom X Y := by
  cases X with
  | mk i X =>
    cases Y with
    | mk j Y =>
      cases f with
      | mk f => exact ⟨rfl, f⟩

/-- Conversely, an equality of indices and an arrow in the component give an arrow of
`ComponentOver K`. -/
private def componentOverHomMk {K : FormalCoproduct.{w} C}
    {X Y : ComponentOver K} (h : X.1 = Y.1) (f : (h ▸ X.2) ⟶ Y.2) : X ⟶ Y := by
  cases X with
  | mk i X =>
    cases Y with
    | mk j Y =>
      cases h
      exact CategoryTheory.Sigma.SigmaHom.mk f

/-- Transporting an object along an equality of indices and back is the identity. -/
private def componentOverHomIso {α : Sort*} (D : α → Type*) [∀ i, Category (D i)]
    {i j : α} (h : i = j) (X : D i) : h.symm ▸ (h ▸ X) ≅ X := by
  cases h
  exact Iso.refl X

/-- An arrow of `ComponentOver K` factors, through an isomorphism, as the image of the arrow
`componentOverHom` reads off inside the component of its target. -/
private lemma componentOverHom_incl_factor {K : FormalCoproduct.{w} C}
    {X Y : ComponentOver K} (f : X ⟶ Y) :
    let h := (componentOverHom f).idx
    let Z : Over (K.obj Y.1) := h ▸ X.2
    let e : (⟨Y.1, Z⟩ : ComponentOver K) ⟶ X :=
      componentOverHomMk h.symm
        (componentOverHomIso (fun i : K.I => Over (K.obj i)) h X.2).hom
    (CategoryTheory.Sigma.incl
      (C := fun i : K.I => Over (K.obj i)) Y.1).map (componentOverHom f).hom =
      e ≫ f := by
  cases X with
  | mk i X =>
    cases Y with
    | mk j Y =>
      cases f with
      | mk f =>
        dsimp [componentOverHom, componentOverHomMk, componentOverHomIso,
          CategoryTheory.Sigma.incl]
        exact (CategoryTheory.Category.id_comp
          (obj := ComponentOver K) (CategoryTheory.Sigma.SigmaHom.mk f)).symm

/-- On an arrow whose endpoints are already in one named component, `componentOverHom` inverts
the component inclusion. -/
private lemma componentOverHom_incl_map {K : FormalCoproduct.{w} C} (i : K.I)
    {X Y : Over (K.obj i)} (f : (CategoryTheory.Sigma.incl
      (C := fun i : K.I => Over (K.obj i)) i).obj X ⟶
        (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i).obj Y) :
    (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i).map
        (componentOverHom f).hom = f := by
  cases f
  rfl

/-- An arrow between two objects of the `i`-th component is the image of an arrow of that
component. Phrased as an existential so that the arrow of the component is obtained as a plain
variable, with no transport along an index equality in its type. -/
private lemma exists_incl_map_eq {K : FormalCoproduct.{w} C} (i : K.I)
    {X Y : Over (K.obj i)}
    (f : (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i).obj X ⟶
        (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i).obj Y) :
    ∃ g : X ⟶ Y,
      (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i).map g = f :=
  ⟨(componentOverHom f).hom, componentOverHom_incl_map i f⟩

/-- The isomorphism appearing in `componentOverHom_incl_factor` is indeed an isomorphism. -/
private lemma componentOverHom_incl_factor_isIso {K : FormalCoproduct.{w} C}
    {X Y : ComponentOver K} (f : X ⟶ Y) :
    let h := (componentOverHom f).idx
    let Z : Over (K.obj Y.1) := h ▸ X.2
    let e : (⟨Y.1, Z⟩ : ComponentOver K) ⟶ X :=
      componentOverHomMk h.symm
        (componentOverHomIso (fun i : K.I => Over (K.obj i)) h X.2).hom
    IsIso e := by
  cases X with
  | mk i X =>
    cases Y with
    | mk j Y =>
      cases f with
      | mk f =>
        change IsIso ((CategoryTheory.Sigma.incl
          (C := fun i : K.I => Over (K.obj i)) i).map (𝟙 X))
        exact Functor.map_isIso _ _

namespace LocalizationSites

variable {J : GrothendieckTopology C}

/-! ### The localization functor -/

/-- **Stacks 0D85.** The componentwise localization functor `C / K ⥤ C` is continuous. -/
@[stacks 0D85 "semi_representable_localization_has_p"]
instance localizationFunctor_isContinuous (S : LocalizationSites.{w} C J) :
    S.localizationFunctor.IsContinuous S.sourceTopology J := by
  apply Functor.isContinuous_of_coverPreserving
  · refine ⟨?_⟩
    intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ heq
    rcases Y₁ with ⟨i, Y₁⟩
    rcases Y₂ with ⟨j, Y₂⟩
    rcases Z with ⟨k, Z⟩
    let G₁ := g₁
    let G₂ := g₂
    rcases g₁ with ⟨g₁⟩
    rcases g₂ with ⟨g₂⟩
    dsimp [LocalizationSites.localizationFunctor] at heq ⊢
    change X ⟶ Y₁.left at f₁
    change X ⟶ Y₂.left at f₂
    let W : S.source := ⟨i, Over.mk (f₁ ≫ Y₁.hom)⟩
    let ι : Over (S.K.obj i) ⥤ S.source :=
      CategoryTheory.Sigma.incl (C := fun i : S.K.I => Over (S.K.obj i)) i
    let a : W ⟶ ⟨i, Y₁⟩ := ι.map (Over.homMk f₁)
    have hw : f₂ ≫ Y₂.hom = f₁ ≫ Y₁.hom := by
      rw [← Over.w g₁, ← Over.w g₂, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ _) heq.symm
    let b : W ⟶ ⟨i, Y₂⟩ := ι.map (Over.homMk f₂ hw)
    have hab : a ≫ G₁ = b ≫ G₂ := by
      change ι.map _ = ι.map _
      exact congrArg ι.map (Over.OverMorphism.ext heq)
    exact hx a b hg₁ hg₂ hab
  · refine ⟨?_⟩
    intro U R hR
    rcases U with ⟨i, U⟩
    let ι := CategoryTheory.Sigma.incl (C := fun i : S.K.I => Over (S.K.obj i)) i
    let Rᵢ := R.functorPullback ι
    have hRᵢ : Rᵢ ∈ J.over (S.K.obj i) U := by
      simpa [Rᵢ, ι, LocalizationSites.sourceTopology] using
        (mem_componentwiseTopology_iff J S.K i U R).1 hR
    have himage := (J.over_forget_coverPreserving (S.K.obj i)).cover_preserve hRᵢ
    refine J.superset_covering ?_ himage
    intro X f hf
    obtain ⟨Y, g, h, hg, heq⟩ := hf
    exact ⟨⟨i, Y⟩, ι.map g, h, hg, heq⟩

/-- **Stacks 0D85.** The componentwise localization functor `C / K ⥤ C` is cocontinuous. -/
@[stacks 0D85 "semi_representable_localization_has_p"]
instance localizationFunctor_isCocontinuous (S : LocalizationSites.{w} C J) :
    S.localizationFunctor.IsCocontinuous S.sourceTopology J := by
  refine ⟨?_⟩
  intro U R hR
  rcases U with ⟨i, U⟩
  let ι := CategoryTheory.Sigma.incl (C := fun i : S.K.I => Over (S.K.obj i)) i
  rw [LocalizationSites.sourceTopology, mem_componentwiseTopology_iff]
  have hsieve :
      (R.functorPullback S.localizationFunctor).functorPullback ι =
        R.functorPullback (Over.forget (S.K.obj i)) := by ext Y f; rfl
  rw [hsieve]
  exact (Over.forget (S.K.obj i)).cover_lift (J.over (S.K.obj i)) J hR

/-- **Stacks 0D85.** The componentwise localization functor has property P under the site's
covering-pullback axiom: relative pullbacks of covering families exist and their projections
cover. -/
@[stacks 0D85 "semi_representable_localization_has_p"]
lemma localizationFunctor_hasCoverPullbacks (S : LocalizationSites.{w} C J)
    [J.toCoverage.HasPullbacks] :
    ∀ (𝒱 : Covering.{u, v, w'} C), 𝒱.2.presieve₀ ∈ J.toCoverage 𝒱.1 →
      ∀ (U : S.source) (g : S.localizationFunctor.obj U ⟶ 𝒱.1),
        ∃ (P : 𝒱.2.I₀ → S.source) (p₁ : ∀ i, P i ⟶ U)
          (p₂ : ∀ i, S.localizationFunctor.obj (P i) ⟶ 𝒱.2.X i),
          (∀ i,
            S.localizationFunctor.map (p₁ i) ≫ g = p₂ i ≫ 𝒱.2.f i ∧
              ∀ (T : S.source) (a : T ⟶ U)
                (b : S.localizationFunctor.obj T ⟶ 𝒱.2.X i),
                S.localizationFunctor.map a ≫ g = b ≫ 𝒱.2.f i →
                  ∃! l : T ⟶ P i,
                    (l ≫ p₁ i = a ∧ S.localizationFunctor.map l ≫ p₂ i = b)) ∧
            (PreZeroHypercover.mk 𝒱.2.I₀ P p₁).presieve₀ ∈
              S.sourceTopology.toCoverage U := by
  classical
  intro 𝒱 h𝒱 U g
  rcases U with ⟨k, U⟩
  change U.left ⟶ 𝒱.1 at g
  let ι : Over (S.K.obj k) ⥤ S.source :=
    CategoryTheory.Sigma.incl (C := fun i : S.K.I => Over (S.K.obj i)) k
  let : 𝒱.2.presieve₀.HasPullbacks g := J.toCoverage.hasPullbacks_of_mem g h𝒱
  have (i : 𝒱.2.I₀) : HasPullback (𝒱.2.f i) g :=
    Presieve.HasPullbacks.hasPullback (f := g) (h := 𝒱.2.f i)
      (𝒱.2.presieve₀_f i)
  let P (i : 𝒱.2.I₀) : S.source :=
    ⟨k, Over.mk (pullback.snd (𝒱.2.f i) g ≫ U.hom)⟩
  let p₁ (i : 𝒱.2.I₀) : P i ⟶ ⟨k, U⟩ :=
    ι.map (Over.homMk (pullback.snd (𝒱.2.f i) g))
  let p₂ (i : 𝒱.2.I₀) : S.localizationFunctor.obj (P i) ⟶ 𝒱.2.X i :=
    pullback.fst (𝒱.2.f i) g
  refine ⟨P, p₁, p₂, ?_, ?_⟩
  · intro i
    constructor
    · change pullback.snd (𝒱.2.f i) g ≫ g =
        pullback.fst (𝒱.2.f i) g ≫ 𝒱.2.f i
      exact pullback.condition.symm
    · intro T a b hab
      rcases T with ⟨j, T⟩; rcases a with ⟨a⟩
      let : HasPullback (𝒱.2.f i) g := this i
      change T.left ⟶ 𝒱.2.X i at b
      change a.left ≫ g = b ≫ 𝒱.2.f i at hab
      let l₀ : T.left ⟶ pullback (𝒱.2.f i) g :=
        pullback.lift b a.left hab.symm
      let l : ⟨k, T⟩ ⟶ P i := ι.map (Over.homMk l₀ (by
        change l₀ ≫ (pullback.snd (𝒱.2.f i) g ≫ U.hom) = T.hom
        calc
          l₀ ≫ (pullback.snd (𝒱.2.f i) g ≫ U.hom) =
              (l₀ ≫ pullback.snd (𝒱.2.f i) g) ≫ U.hom := by rw [Category.assoc]
          _ = a.left ≫ U.hom := by rw [pullback.lift_snd]
          _ = T.hom := Over.w a))
      refine ⟨l, ?_, ?_⟩
      · constructor
        · change ι.map _ = ι.map _
          apply congrArg ι.map
          apply Over.OverMorphism.ext
          change l₀ ≫ pullback.snd (𝒱.2.f i) g = a.left
          exact pullback.lift_snd b a.left hab.symm
        · change l₀ ≫ pullback.fst (𝒱.2.f i) g = b
          exact pullback.lift_fst b a.left hab.symm
      · intro m hm
        rcases hm with ⟨hm₁raw, hm₂raw⟩; rcases m with ⟨m⟩
        let : HasPullback (𝒱.2.f i) g := this
        have hm₁ : m ≫ Over.homMk (pullback.snd (𝒱.2.f i) g) = a :=
          ι.map_injective hm₁raw
        have hmfst : m.left ≫ pullback.fst (𝒱.2.f i) g = b := by
          change m.left ≫ pullback.fst (𝒱.2.f i) g = b at hm₂raw; exact hm₂raw
        have hsnd : m.left ≫ pullback.snd (𝒱.2.f i) g = a.left := by
          simpa using congrArg Over.Hom.left hm₁
        have hml : m.left = l₀ := pullback.hom_ext
          (hmfst.trans (pullback.lift_fst b a.left hab.symm).symm)
          (hsnd.trans (pullback.lift_snd b a.left hab.symm).symm)
        apply congrArg ι.map
        apply Over.OverMorphism.ext
        exact hml
  · rw [GrothendieckTopology.mem_toCoverage_iff, LocalizationSites.sourceTopology,
      mem_componentwiseTopology_iff, GrothendieckTopology.mem_over_iff]
    let q₁ (i : 𝒱.2.I₀) : (P i).2 ⟶ U :=
      Over.homMk (pullback.snd (𝒱.2.f i) g)
    have hsigma :
        (Sieve.generate (PreZeroHypercover.mk 𝒱.2.I₀ P p₁).presieve₀).functorPullback ι =
          Sieve.ofArrows (fun i => (P i).2) q₁ := by
      ext Y f
      constructor
      · rintro ⟨Z, h, b, hb, hfac⟩
        rcases hb with ⟨i⟩
        rcases h with ⟨h⟩
        refine ⟨(P i).2, h, q₁ i, ⟨i⟩, ι.map_injective ?_⟩
        exact hfac
      · rintro ⟨Z, h, b, hb, hfac⟩
        rcases hb with ⟨i⟩
        subst hfac
        exact ⟨P i, ι.map h, p₁ i, ⟨i⟩, ι.map_comp h (q₁ i)⟩
    have hpbFamily :
        Sieve.ofArrows (fun i => (P i).2.left) (fun i => (q₁ i).left) =
          Sieve.pullback g (Sieve.ofArrows 𝒱.2.X 𝒱.2.f) :=
      Sieve.ofArrows_eq_pullback_of_isPullback (f := 𝒱.2.f)
        (p₁ := fun i => pullback.snd (𝒱.2.f i) g)
        (p₂ := fun i => pullback.fst (𝒱.2.f i) g)
        (fun i => (IsPullback.of_hasPullback (𝒱.2.f i) g).flip)
    have hfamily :
        Sieve.overEquiv U
          ((Sieve.generate (PreZeroHypercover.mk 𝒱.2.I₀ P p₁).presieve₀).functorPullback ι) =
            Sieve.generate (𝒱.2.presieve₀.pullbackArrows g) := by
      rw [hsigma, Sieve.overEquiv_ofArrows, hpbFamily, Sieve.pullbackArrows_comm]
    rw [hfamily, Sieve.pullbackArrows_comm]
    exact J.pullback_stable g ((GrothendieckTopology.mem_toCoverage_iff J).1 h𝒱)

/-! ### The relocalization functor -/

/-- **Stacks 0D85.** The componentwise relocalization functor `C / K ⥤ C / L` is continuous. -/
@[stacks 0D85 "semi_representable_relocalization_has_p"]
instance relocalizationFunctor_isContinuous (S : LocalizationSites.{w} C J) :
    S.relocalizationFunctor.IsContinuous S.sourceTopology S.targetTopology := by
  constructor
  intro G
  apply isSheaf_componentwise J
  intro i
  let I := CategoryTheory.Sigma.incl (C := fun i : S.K.I => Over (S.K.obj i)) i
  let O := CategoryTheory.Sigma.incl (C := fun j : S.L.I => Over (S.L.obj j)) (S.f.f i)
  have hO : Presieve.IsSheaf (J.over (S.L.obj (S.f.f i))) (O.op ⋙ G.obj) := by
    let : O.IsContinuous (J.over (S.L.obj (S.f.f i))) S.targetTopology :=
      incl_isContinuous (J := J) S.L (S.f.f i)
    exact CategoryTheory.Functor.op_comp_isSheaf_of_types O
      (J.over (S.L.obj (S.f.f i))) S.targetTopology G
  have h := (Over.map (S.f.φ i)).op_comp_isSheaf_of_types
    (J.over (S.K.obj i)) (J.over (S.L.obj (S.f.f i)))
    ⟨O.op ⋙ G.obj, (isSheaf_iff_isSheaf_of_type _ _).2 hO⟩
  have e : (I ⋙ S.relocalizationFunctor).op ≅
      (Over.map (S.f.φ i) ⋙ O).op := NatIso.op (S.relocalizationFunctorCompIso i)
  exact Presieve.isSheaf_iso (J.over (S.K.obj i))
    (Functor.isoWhiskerRight e.symm G.obj) h

/-- **Stacks 0D85.** The componentwise relocalization functor `C / K ⥤ C / L` is
cocontinuous. -/
@[stacks 0D85 "semi_representable_relocalization_has_p"]
instance relocalizationFunctor_isCocontinuous (S : LocalizationSites.{w} C J) :
    S.relocalizationFunctor.IsCocontinuous S.sourceTopology S.targetTopology where
  cover_lift := by
    rintro ⟨i, X⟩ R hR
    change R.functorPullback
      (CategoryTheory.Sigma.incl (C := fun i : S.L.I => Over (S.L.obj i)) (S.f.f i)) ∈
        J.over (S.L.obj (S.f.f i)) ((Over.map (S.f.φ i)).obj X) at hR
    change R.functorPullback
      (Over.map (S.f.φ i) ⋙ CategoryTheory.Sigma.incl
        (C := fun j : S.L.I => Over (S.L.obj j)) (S.f.f i)) ∈ J.over (S.K.obj i) X
    exact (Over.map (S.f.φ i)).cover_lift (J.over (S.K.obj i)) (J.over (S.L.obj (S.f.f i))) hR

/-- **Stacks 0D85.** The componentwise relocalization functor has property P: covering families
admit representable pullbacks, and those pullbacks cover. -/
@[stacks 0D85 "semi_representable_relocalization_has_p"]
lemma relocalizationFunctor_hasCoverPullbacks (S : LocalizationSites.{w} C J)
    [J.toCoverage.HasPullbacks] :
    S.relocalizationFunctor.HasCoverPullbacks
      (fun 𝒰 ↦ 𝒰.2.presieve₀ ∈ S.sourceTopology.toCoverage 𝒰.1)
      (fun 𝒱 ↦ 𝒱.2.presieve₀ ∈ S.targetTopology.toCoverage 𝒱.1) := by
  classical
  intro 𝒱 h𝒱 U g
  rcases U with ⟨i, X⟩
  rcases 𝒱 with ⟨V, E⟩
  rcases V with ⟨j, Y⟩
  cases g
  rename_i Y g
  change Over (S.L.obj (S.f.f i)) at Y
  dsimp only at g h𝒱 ⊢
  let j : S.L.I := S.f.f i
  let targetIncl : Over (S.L.obj j) ⥤ S.target :=
    CategoryTheory.Sigma.incl (C := fun k : S.L.I => Over (S.L.obj k)) j
  let Rcomp := (Sieve.generate E.presieve₀).functorPullback targetIncl
  have hRcomp : Rcomp ∈ J.over (S.L.obj j) Y := by
    change Sieve.generate E.presieve₀ ∈ S.targetTopology ⟨j, Y⟩ at h𝒱
    exact (mem_componentwiseTopology_iff J S.L j Y
      (Sieve.generate E.presieve₀)).1 h𝒱
  let Rbase := Sieve.overEquiv Y Rcomp
  have hRbase : Rbase ∈ J Y.left :=
    (GrothendieckTopology.mem_over_iff J Rcomp).1 hRcomp
  let famHom (a : E.I₀) := componentOverHom (E.f a)
  have famIdx (a : E.I₀) : (E.X a).1 = j := (famHom a).idx
  let famObj (a : E.I₀) : Over (S.L.obj j) := (famIdx a) ▸ (E.X a).2
  let famArrow (a : E.I₀) : famObj a ⟶ Y := (famHom a).hom
  let eX (a : E.I₀) : targetIncl.obj (famObj a) ⟶ E.X a :=
    componentOverHomMk (famIdx a).symm
      (componentOverHomIso (fun k : S.L.I => Over (S.L.obj k)) (famIdx a) (E.X a).2).hom
  have eX_isIso (a : E.I₀) : IsIso (eX a) := componentOverHom_incl_factor_isIso (E.f a)
  have hfac (a : E.I₀) : targetIncl.map (famArrow a) = eX a ≫ E.f a :=
    componentOverHom_incl_factor (E.f a)
  -- an arrow into `E.X a` from a component object factors through `famArrow a`
  have lift_factor (a : E.I₀) {V : Over (S.L.obj j)} (h : targetIncl.obj V ⟶ E.X a) :
      ∃ b : V ⟶ famObj a, targetIncl.map b = h ≫ inv (eX a) ∧
        h ≫ E.f a = targetIncl.map (b ≫ famArrow a) := by
    have := eX_isIso a
    obtain ⟨b, hb⟩ := exists_incl_map_eq (K := S.L) j (h ≫ inv (eX a))
    exact ⟨b, hb, comp_eq_comp_of_inv h (eX a) _ _ _ hb (hfac a)⟩
  have hFamArrow (a : E.I₀) : Rcomp (famArrow a) := by
    change (Sieve.generate E.presieve₀) (targetIncl.map (famArrow a))
    rw [hfac]
    exact (Sieve.generate E.presieve₀).downward_closed
      (Sieve.le_generate E.presieve₀ (E.X a) (E.f a) (E.presieve₀_f a)) _
  have hFamArrowBase (a : E.I₀) : Rbase (famArrow a).left := by
    change Rcomp.functorPushforward (Over.forget (S.L.obj j)) (famArrow a).left
    exact ⟨famObj a, famArrow a, 𝟙 _, hFamArrow a, by simp⟩
  have hRbaseCov : Rbase.arrows ∈ J.toCoverage Y.left := by
    rw [GrothendieckTopology.mem_toCoverage_iff, Sieve.generate_sieve]
    exact hRbase
  have hRbasePullbacks : Rbase.arrows.HasPullbacks g.left :=
    Precoverage.hasPullbacks_of_mem _ hRbaseCov
  have hPullback (a : E.I₀) : HasPullback (famArrow a).left g.left :=
    hRbasePullbacks.hasPullback (hFamArrowBase a)
  let pbObj (a : E.I₀) : C := by
    have := hPullback a; exact pullback (famArrow a).left g.left
  let pbFst (a : E.I₀) : pbObj a ⟶ X.left := by
    have := hPullback a; exact pullback.snd (famArrow a).left g.left
  let pbSnd (a : E.I₀) : pbObj a ⟶ (famObj a).left := by
    have := hPullback a; exact pullback.fst (famArrow a).left g.left
  let pbOver (a : E.I₀) : Over (S.K.obj i) := Over.mk (pbFst a ≫ X.hom)
  let P : E.I₀ → S.source := fun a => ⟨i, pbOver a⟩
  let p₁Over (a : E.I₀) : pbOver a ⟶ X := Over.homMk (pbFst a) (by simp [pbOver])
  let srcIncl : Over (S.K.obj i) ⥤ S.source :=
    CategoryTheory.Sigma.incl (C := fun k : S.K.I => Over (S.K.obj k)) i
  let p₁ (a : E.I₀) : P a ⟶ ⟨i, X⟩ := srcIncl.map (p₁Over a)
  let p₂Component (a : E.I₀) :
      (Over.map (S.f.φ i)).obj (pbOver a) ⟶ famObj a :=
    Over.homMk (pbSnd a) (by
      dsimp [pbOver]
      calc
        pbSnd a ≫ (famObj a).hom =
            (pbSnd a ≫ (famArrow a).left) ≫ Y.hom := by
          rw [← (famArrow a).w, Category.assoc]
        _ = (pbFst a ≫ g.left) ≫ Y.hom := by rw [pullback.condition]
        _ = pbFst a ≫ (X.hom ≫ S.f.φ i) := by
          rw [Category.assoc]
          exact congrArg (fun q => pbFst a ≫ q) (Over.w g)
        _ = (pbFst a ≫ X.hom) ≫ S.f.φ i := by rw [Category.assoc])
  let p₂ (a : E.I₀) : S.relocalizationFunctor.obj (P a) ⟶ E.X a :=
    targetIncl.map (p₂Component a) ≫ eX a
  refine ⟨P, p₁, p₂, ?_, ?_⟩
  · intro a
    have := eX_isIso a
    constructor
    · have hp :
          (Over.map (S.f.φ i)).map (p₁Over a) ≫ g = p₂Component a ≫ famArrow a := by
        apply Over.OverMorphism.ext
        exact pullback.condition.symm
      change targetIncl.map ((Over.map (S.f.φ i)).map (p₁Over a) ≫ g) =
        (targetIncl.map (p₂Component a) ≫ eX a) ≫ E.f a
      rw [hp, Functor.map_comp, hfac]
      exact (Category.assoc _ _ _).symm
    · intro T aT bT h
      rcases T with ⟨k, Z⟩
      cases aT with
      | mk aT =>
        obtain ⟨bOver, hbT, hR⟩ := lift_factor a bT
        have h0 : targetIncl.map ((Over.map (S.f.φ i)).map aT ≫ g) = bT ≫ E.f a := h
        have hbase : (Over.map (S.f.φ i)).map aT ≫ g = bOver ≫ famArrow a :=
          targetIncl.map_injective (h0.trans hR)
        let l0 : Z.left ⟶ pbObj a := pullback.lift bOver.left aT.left
          (congrArg Over.Hom.left hbase).symm
        have hl0snd : l0 ≫ pbFst a = aT.left := by
          have := hPullback a
          exact pullback.lift_snd _ _ _
        have hl0fst : l0 ≫ pbSnd a = bOver.left := by
          have := hPullback a
          exact pullback.lift_fst _ _ _
        have hl0Over : l0 ≫ (pbOver a).hom = Z.hom := by
          change l0 ≫ pbFst a ≫ X.hom = Z.hom
          rw [← Category.assoc, hl0snd]
          exact Over.w aT
        let lOver : Z ⟶ pbOver a := Over.homMk l0 hl0Over
        refine ⟨srcIncl.map lOver, ⟨?_, ?_⟩, ?_⟩
        · exact congrArg srcIncl.map (Over.OverMorphism.ext hl0snd : lOver ≫ p₁Over a = aT)
        · have hcompOver : (Over.map (S.f.φ i)).map lOver ≫ p₂Component a = bOver :=
            Over.OverMorphism.ext hl0fst
          change targetIncl.map ((Over.map (S.f.φ i)).map lOver) ≫
            (targetIncl.map (p₂Component a) ≫ eX a) = bT
          exact (comp_assoc_eq_iff _ _ _ _).2
            ((targetIncl.map_comp _ _).symm.trans (congrArg targetIncl.map hcompOver) |>.trans hbT)
        · intro l' hl'
          rcases hl' with ⟨hl₁, hl₂⟩
          cases l' with
          | mk lOver' =>
            have hfst : lOver'.left ≫ pbFst a = aT.left :=
              congrArg Over.Hom.left (srcIncl.map_injective
                (hl₁ : srcIncl.map (lOver' ≫ p₁Over a) = srcIncl.map aT))
            have hsecond : targetIncl.map ((Over.map (S.f.φ i)).map lOver' ≫ p₂Component a) =
                targetIncl.map bOver := by
              rw [Functor.map_comp, hbT]
              exact (comp_assoc_eq_iff _ _ _ _).1 hl₂
            have hsnd : lOver'.left ≫ pbSnd a = bOver.left :=
              congrArg Over.Hom.left (targetIncl.map_injective hsecond)
            have := hPullback a
            exact congrArg srcIncl.map (Over.OverMorphism.ext
              (pullback.hom_ext (hsnd.trans hl0fst.symm) (hfst.trans hl0snd.symm)))
  · have hRbase_le : Rbase ≤ Sieve.generate
        (Presieve.ofArrows (fun a => (famObj a).left)
          (fun a => (famArrow a).left)) := by
      intro T q hq
      rw [Sieve.generate]
      let qObj : Over (S.L.obj j) := Over.mk (q ≫ Y.hom)
      let qOver : qObj ⟶ Y := Over.homMk q (by simp [qObj])
      have hqComp : Rcomp qOver := (Sieve.overEquiv_iff Rcomp q).mp hq
      change (Sieve.generate E.presieve₀)
        (targetIncl.map qOver) at hqComp
      rcases hqComp with ⟨W, h, k, hk, hfac'⟩
      rcases hk with ⟨b⟩
      obtain ⟨hOverHom, -, hR⟩ := lift_factor b h
      have hqOver : qOver = hOverHom ≫ famArrow b :=
        targetIncl.map_injective (hfac'.symm.trans hR)
      exact ⟨(famObj b).left, hOverHom.left, (famArrow b).left,
        Presieve.ofArrows.mk b, (congrArg Over.Hom.left hqOver).symm⟩
    have hpull : Rbase.pullback g.left ∈ J X.left :=
      J.pullback_stable g.left hRbase
    have hpull_le : Rbase.pullback g.left ≤ Sieve.generate
        (Presieve.ofArrows (fun a => pbObj a) pbFst) := by
      intro T q hq
      have hqFam : (Sieve.generate
          (Presieve.ofArrows (fun a => (famObj a).left)
            (fun a => (famArrow a).left))) (q ≫ g.left) :=
        hRbase_le _ (by simpa using hq)
      rw [Sieve.generate] at hqFam ⊢
      rcases hqFam with ⟨W, h, k, hk, hfac'⟩
      rcases hk with ⟨b⟩
      have := hPullback b
      let lq : T ⟶ pbObj b := pullback.lift h q (by simpa using hfac')
      refine ⟨pbObj b, lq, pbFst b, Presieve.ofArrows.mk b, ?_⟩
      dsimp [lq, pbFst, pbObj]
      exact pullback.lift_snd _ _ _
    have hpullFam : Sieve.generate
        (Presieve.ofArrows (fun a => pbObj a) pbFst) ∈ J X.left :=
      J.superset_covering hpull_le hpull
    have hcomponent : Sieve.generate
        (Presieve.ofArrows pbOver p₁Over) ∈ J.over (S.K.obj i) X := by
      apply (GrothendieckTopology.mem_over_iff J _).2
      rw [Sieve.overEquiv_ofArrows]
      exact hpullFam
    have hcomp_le : Sieve.generate (Presieve.ofArrows pbOver p₁Over) ≤
        Sieve.functorPullback srcIncl (Sieve.generate (Presieve.ofArrows P p₁)) := by
      rw [Sieve.generate_le_iff]
      intro T f hf
      rcases hf with ⟨a⟩
      exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk a)
    have hcomp : Sieve.functorPullback srcIncl
        (Sieve.generate (Presieve.ofArrows P p₁)) ∈ J.over (S.K.obj i) X :=
      (J.over (S.K.obj i)).superset_covering hcomp_le hcomponent
    change (Presieve.ofArrows P p₁) ∈
      S.sourceTopology.toCoverage ⟨i, X⟩
    rw [GrothendieckTopology.mem_toCoverage_iff]
    change Sieve.generate (Presieve.ofArrows P p₁) ∈
      componentwiseTopology J S.K ⟨i, X⟩
    rw [mem_componentwiseTopology_iff]
    exact hcomp

end LocalizationSites

end CategoryTheory.SemiRepresentable

end
