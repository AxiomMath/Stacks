module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.Deformation.RingedSpaceThickening.LiftingObstruction
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupport
import StacksCore.Tactic.StacksAttribute

/-!
# Extensions with a prescribed canonical map (Stacks 08L7)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces with ideal
`ℐ`, let `ℱ` and `𝒦` be `𝒪_X`-modules, and let `c : i^* ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦` be `𝒪_X`-linear.
**Stacks 08L7** says that the set of isomorphism classes of extensions

    0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0

whose canonical map of **Stacks 08L4** is `c` is, if nonempty, principal homogeneous under
`Ext¹_{𝒪_X}(ℱ, 𝒦)`.

The two halves of the source's proof are proved here. Isomorphism classes of such extensions
are the elements of `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`, and the action is addition in that group by
a class coming from `𝒪_X`-modules, i.e. by the class of an extension whose middle term is a
direct image (**Stacks 08KS**):

* adding such an extension does not change the canonical map, and
* two extensions with the same canonical map differ by the class of exactly one such extension.

Both rest on the fact that the canonical map is an *additive* function of the class of the
extension, which is the computation the source leaves to "some details omitted" and which is
proved here from a Baer-sum construction.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.idealTensorFunctor` and
  `AlgebraicGeometry.RingedSpaceThickening.idealActionNatTrans`: tensoring with the ideal of the
  thickening as a functor, and the action of the ideal as a natural transformation to the
  identity. Packaging them this way is what lets the Baer-sum computation be done once, in an
  arbitrary abelian category.
* `AlgebraicGeometry.RingedSpaceThickening.descendedActionOfMap`: the map
  `ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_* 𝒦` attached to an `𝒪_X`-linear `c`, namely the **Stacks 08L4**
  comparison followed by `i_* c`.

## Main results

* `CategoryTheory.Abelian.exists_shortExact_extClass_add_descendedAction`: **the Baer sum with
  its descended action.** For a functor `T` with a natural `act : T ⟶ 𝟭`, two extensions of `B`
  by `A` with descended actions `d₁`, `d₂` have a Baer sum whose class in `Ext¹` is the sum of
  the two classes and whose descended action is `d₁ + d₂`.
* `CategoryTheory.Abelian.exists_shortExact_mapExactFunctor_extClass_eq`: an extension whose
  middle term lies in the essential image of a fully faithful exact functor is the image of an
  extension, with the same class.
* `AlgebraicGeometry.RingedSpaceThickening.eq_firstOrderExtensionAction_of_descendedAction`: the
  canonical map of an extension is the unique solution of the global lifting equation, and
  `AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction_eq_of_extClass_eq`: it
  therefore depends only on the class of the extension.
* `AlgebraicGeometry.RingedSpaceThickening.exists_baerSum_firstOrderExtensionAction`: **the
  canonical map is additive for Baer sums.**
* `AlgebraicGeometry.RingedSpaceThickening.exists_extClass_add_of_essImage` and
  `AlgebraicGeometry.RingedSpaceThickening.
  existsUnique_extClass_sub_of_firstOrderExtensionAction_eq`: **Stacks 08L7**, the two clauses
  displayed above.

## Implementation notes

The Baer sum is built as the source builds it: divide `ℱ'₁ ⊞ ℱ'₂` by the antidiagonal copy of
`i_* 𝒦`, which gives an extension of `i_* ℱ ⊞ i_* ℱ`, and pull that back along the diagonal.
Both steps are the constructions of `StacksDraft.Deformation.RingedSpaceThickening.
ExtensionObstruction`, so the only new abelian-category input is that adding a constant summand
to a short exact sequence leaves one (`CategoryTheory.Abelian.shortExact_biprodRight` and
`shortExact_biprodLeft`).

The additivity of the canonical map is proved abstractly, for a functor `T` with
`act : T ⟶ 𝟭`: the *descended action* of an extension `0 → A → M → B → 0` is the unique
`d : T B ⟶ A` with `T(g) ≫ d ≫ f = act_M`, which exists because `act` vanishes on `A` and `B`,
and uniqueness is epi/mono cancellation. Doing it abstractly avoids computing with sections of
sheaves on `X'` at all.

The sections of the structure sheaf of a ringed space carry two spellings of their ring
structure: `structureSheafRing`, over which the
tensor product is formed, and `structureSheafRing`, at which sheaves of
modules are indexed. They are definitionally equal, but `structureSheafRing` is not reducible, so
*instance* search cannot pass between them: an `Add` on `tensorSheaf X (i^* ℐ) ℱ ⟶ 𝒦` is found
only when both objects carry the reducible spelling as their declared type. That is why the
section `CanonicalMap` declares `ℱ` and `𝒦` over `structureSheafRing X`, and why
`descendedActionOfMap` exists at all: it names the map `ℐ ⊗ i_* ℱ ⟶ i_* 𝒦` with the type at
which sums of such maps are formed, so that the bridge between the two spellings is crossed
once, in term mode, rather than inside every `rw`.

## References

* [Stacks Project, Tag 08L7](https://stacks.math.columbia.edu/tag/08L7)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 06XV](https://stacks.math.columbia.edu/tag/06XV)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace CategoryTheory.Abelian

section Biprod

universe v

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem biprod_map_epi {M N : C} {g : M ⟶ N} [Epi g] (W : C) :
    Epi (biprod.map g (𝟙 W)) :=
  inferInstance

theorem biprod_map_epi' {M N : C} {g : M ⟶ N} [Epi g] (W : C) :
    Epi (biprod.map (𝟙 W) g) :=
  inferInstance

/-- Adding a constant summand on the right to a short exact sequence leaves a short exact
sequence `0 → A → M ⊞ W → N ⊞ W → 0`. -/
theorem shortExact_biprodRight {A M N : C} {f : A ⟶ M} {g : M ⟶ N} {w : f ≫ g = 0}
    (hS : (ShortComplex.mk f g w).ShortExact) (W : C) :
    (ShortComplex.mk (f ≫ biprod.inl) (biprod.map g (𝟙 W))
      (by rw [Category.assoc, biprod.inl_map, ← Category.assoc, w, zero_comp])).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' ?_ (mono_comp _ _) (biprod_map_epi W)
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro Q a ha
  dsimp only at a ha ⊢
  have h2 : a ≫ biprod.snd = 0 := by
    have h := ha =≫ biprod.snd
    simpa using h
  have h1 : (a ≫ biprod.fst) ≫ g = 0 := by
    have h := ha =≫ biprod.fst
    simpa [Category.assoc] using h
  refine ⟨Q, 𝟙 Q, inferInstance, hS.exact.lift _ h1, ?_⟩
  rw [Category.id_comp]
  refine biprod.hom_ext _ _ ?_ ?_
  · simpa using (hS.exact.lift_f (a ≫ biprod.fst) h1).symm
  · simpa using h2

/-- Adding a constant summand on the left to a short exact sequence leaves a short exact
sequence `0 → A → W ⊞ M → W ⊞ N → 0`. -/
theorem shortExact_biprodLeft {A M N : C} {f : A ⟶ M} {g : M ⟶ N} {w : f ≫ g = 0}
    (hS : (ShortComplex.mk f g w).ShortExact) (W : C) :
    (ShortComplex.mk (f ≫ biprod.inr) (biprod.map (𝟙 W) g)
      (by rw [Category.assoc, biprod.inr_map, ← Category.assoc, w, zero_comp])).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' ?_ (mono_comp _ _) (biprod_map_epi' W)
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro Q a ha
  dsimp only at a ha ⊢
  have h2 : a ≫ biprod.fst = 0 := by
    have h := ha =≫ biprod.fst
    simpa using h
  have h1 : (a ≫ biprod.snd) ≫ g = 0 := by
    have h := ha =≫ biprod.snd
    simpa [Category.assoc] using h
  refine ⟨Q, 𝟙 Q, inferInstance, hS.exact.lift _ h1, ?_⟩
  rw [Category.id_comp]
  refine biprod.hom_ext _ _ ?_ ?_
  · simpa using h2
  · simpa using (hS.exact.lift_f (a ≫ biprod.snd) h1).symm

end Biprod

section DescendedAction

universe v

/-- A descended action is determined by the equation characterising it: the two maps it is
sandwiched between are an epimorphism and a monomorphism. -/
theorem descendedAction_unique {C : Type u} [Category.{v} C] (T : C ⥤ C) {A M B : C}
    (f : A ⟶ M) (g : M ⟶ B) (hf : Mono f) (hg : Epi (T.map g))
    {a : T.obj M ⟶ M} {d d' : T.obj B ⟶ A}
    (h : T.map g ≫ d ≫ f = a) (h' : T.map g ≫ d' ≫ f = a) : d = d' := by
  have := hf
  have := hg
  exact (cancel_mono f).1 ((cancel_epi (T.map g)).1 (h.trans h'.symm))

/-- The descended action is unchanged by an isomorphism of extensions inducing the identity on
both end terms. -/
theorem descendedAction_iso {C : Type u} [Category.{v} C] (T : C ⥤ C) (act : T ⟶ 𝟭 C)
    {A M M' B : C} {f : A ⟶ M} {g : M ⟶ B} {f' : A ⟶ M'} {g' : M' ⟶ B}
    (φ : M ≅ M') (hf : f ≫ φ.hom = f') (hg : φ.hom ≫ g' = g)
    {d : T.obj B ⟶ A} (h : T.map g ≫ d ≫ f = act.app M) :
    T.map g' ≫ d ≫ f' = act.app M' := by
  have : IsIso (T.map φ.hom) := inferInstance
  rw [← cancel_epi (T.map φ.hom)]
  calc T.map φ.hom ≫ T.map g' ≫ d ≫ f'
      = T.map g ≫ d ≫ f ≫ φ.hom := by
        rw [← Category.assoc (T.map φ.hom), ← T.map_comp, hg, hf]
    _ = act.app M ≫ φ.hom := by rw [reassoc_of% h]
    _ = T.map φ.hom ≫ act.app M' := (act.naturality φ.hom).symm

/-- **The descended action of a quotient of a direct sum of two extensions.** Let
`0 → A → E₁ → B → 0` and `0 → A → E₂ → B → 0` be extensions with descended actions `d₁` and
`d₂`, and let `π : E₁ ⊞ E₂ ⟶ Q` identify the two copies of `A`, so that `Q` is an extension
`0 → A → Q → B ⊞ B → 0` with `j` and `q` as its maps. Then the descended action of `Q` is
`T(fst) ≫ d₁ + T(snd) ≫ d₂`. -/
theorem descendedAction_biprodQuotient {C : Type u} [Category.{v} C] [Preadditive C]
    [Limits.HasBinaryBiproducts C] (T : C ⥤ C) (act : T ⟶ 𝟭 C)
    {A B E₁ E₂ Q : C} {i₁ : A ⟶ E₁} {p₁ : E₁ ⟶ B} {i₂ : A ⟶ E₂} {p₂ : E₂ ⟶ B}
    (π : E₁ ⊞ E₂ ⟶ Q) (j : A ⟶ Q) (q : Q ⟶ B ⊞ B)
    (hπq : π ≫ q = biprod.map p₁ p₂)
    (hj₁ : i₁ ≫ biprod.inl ≫ π = j) (hj₂ : i₂ ≫ biprod.inr ≫ π = j)
    (hπepi : Epi (T.map π)) (d₁ d₂ : T.obj B ⟶ A)
    (hd₁ : T.map p₁ ≫ d₁ ≫ i₁ = act.app E₁)
    (hd₂ : T.map p₂ ≫ d₂ ≫ i₂ = act.app E₂) :
    T.map q ≫ (T.map biprod.fst ≫ d₁ + T.map biprod.snd ≫ d₂) ≫ j = act.app Q := by
  have := hπepi
  have hnat : T.map π ≫ act.app Q = act.app (E₁ ⊞ E₂) ≫ π := act.naturality π
  have hfst : T.map (biprod.map p₁ p₂) ≫ T.map biprod.fst =
      T.map biprod.fst ≫ T.map p₁ := by
    rw [← T.map_comp, ← T.map_comp, biprod.map_fst]
  have hsnd : T.map (biprod.map p₁ p₂) ≫ T.map biprod.snd =
      T.map biprod.snd ≫ T.map p₂ := by
    rw [← T.map_comp, ← T.map_comp, biprod.map_snd]
  have hn₁ : T.map biprod.fst ≫ act.app E₁ = act.app (E₁ ⊞ E₂) ≫ biprod.fst :=
    act.naturality (biprod.fst : E₁ ⊞ E₂ ⟶ E₁)
  have hn₂ : T.map biprod.snd ≫ act.app E₂ = act.app (E₁ ⊞ E₂) ≫ biprod.snd :=
    act.naturality (biprod.snd : E₁ ⊞ E₂ ⟶ E₂)
  have e₁ : T.map (biprod.map p₁ p₂) ≫ (T.map biprod.fst ≫ d₁) ≫ j =
      act.app (E₁ ⊞ E₂) ≫ biprod.fst ≫ biprod.inl ≫ π := by
    rw [← hj₁]
    simp only [Category.assoc]
    rw [reassoc_of% hfst, reassoc_of% hd₁, reassoc_of% hn₁]
  have e₂ : T.map (biprod.map p₁ p₂) ≫ (T.map biprod.snd ≫ d₂) ≫ j =
      act.app (E₁ ⊞ E₂) ≫ biprod.snd ≫ biprod.inr ≫ π := by
    rw [← hj₂]
    simp only [Category.assoc]
    rw [reassoc_of% hsnd, reassoc_of% hd₂, reassoc_of% hn₂]
  rw [← cancel_epi (T.map π), hnat]
  calc T.map π ≫ T.map q ≫ (T.map biprod.fst ≫ d₁ + T.map biprod.snd ≫ d₂) ≫ j
      = T.map (biprod.map p₁ p₂) ≫
          (T.map biprod.fst ≫ d₁ + T.map biprod.snd ≫ d₂) ≫ j := by
        rw [← Category.assoc, ← T.map_comp, hπq]
    _ = T.map (biprod.map p₁ p₂) ≫ (T.map biprod.fst ≫ d₁) ≫ j +
          T.map (biprod.map p₁ p₂) ≫ (T.map biprod.snd ≫ d₂) ≫ j := by
        rw [Preadditive.add_comp, Preadditive.comp_add]
    _ = act.app (E₁ ⊞ E₂) ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ π := by
        rw [e₁, e₂, Preadditive.add_comp, Preadditive.comp_add]
        simp only [Category.assoc]
    _ = act.app (E₁ ⊞ E₂) ≫ π := by rw [biprod.total]; simp

/-- **The descended action of a pullback of an extension.** Pulling `0 → A → Q → BB → 0` back
along `δ : B ⟶ BB` gives an extension `0 → A → P → B → 0` whose descended action is `T(δ)`
followed by that of the original one. -/
theorem descendedAction_pullback {C : Type u} [Category.{v} C] [Preadditive C]
    (T : C ⥤ C) (act : T ⟶ 𝟭 C)
    {A B BB Q P : C} {j : A ⟶ Q} {q : Q ⟶ BB} (δ : B ⟶ BB)
    (iP : A ⟶ P) (pP : P ⟶ B) (v : P ⟶ Q)
    (hiPpP : iP ≫ pP = 0) (hiPv : iP ≫ v = j) (hvq : v ≫ q = pP ≫ δ)
    (hjoint : ∀ {Z : C} (a b : Z ⟶ P), a ≫ pP = b ≫ pP → a ≫ v = b ≫ v → a = b)
    (hactB : act.app B = 0) (D : T.obj BB ⟶ A)
    (hD : T.map q ≫ D ≫ j = act.app Q) :
    T.map pP ≫ (T.map δ ≫ D) ≫ iP = act.app P := by
  refine hjoint _ _ ?_ ?_
  · have hr : act.app P ≫ pP = T.map pP ≫ act.app B := (act.naturality pP).symm
    rw [hr, hactB, comp_zero, Category.assoc, Category.assoc, Category.assoc, hiPpP,
      comp_zero, comp_zero, comp_zero]
  · have hr : act.app P ≫ v = T.map v ≫ act.app Q := (act.naturality v).symm
    rw [hr, ← hD]
    calc (T.map pP ≫ (T.map δ ≫ D) ≫ iP) ≫ v
        = T.map (pP ≫ δ) ≫ D ≫ (iP ≫ v) := by
          rw [T.map_comp]; simp only [Category.assoc]
      _ = T.map v ≫ T.map q ≫ D ≫ j := by
          rw [hiPv, ← hvq, T.map_comp]; simp only [Category.assoc]

end DescendedAction

section BaerSum

universe v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **The Baer sum of two extensions, together with its descended action.** Given two
extensions `0 → A → E₁ → B → 0` and `0 → A → E₂ → B → 0` whose descended actions for a functor
`T` with `act : T ⟶ 𝟭` are `d₁` and `d₂`, there is an extension `0 → A → E → B → 0` whose class
in `Ext¹` is the sum of the two classes and whose descended action is `d₁ + d₂`.

The extension is built as the source builds a Baer sum: divide `E₁ ⊞ E₂` by the antidiagonal
copy of `A` to get an extension of `B ⊞ B`, then pull back along the diagonal of `B`. -/
theorem exists_shortExact_extClass_add_descendedAction
    (T : C ⥤ C) (act : T ⟶ 𝟭 C)
    (hTepi : ∀ {Y Z : C} (φ : Y ⟶ Z), Epi φ → Epi (T.map φ))
    {A B E₁ E₂ : C} {i₁ : A ⟶ E₁} {p₁ : E₁ ⟶ B} {w₁ : i₁ ≫ p₁ = 0}
    {i₂ : A ⟶ E₂} {p₂ : E₂ ⟶ B} {w₂ : i₂ ≫ p₂ = 0}
    (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
    (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
    (hactB : act.app B = 0) (d₁ d₂ : T.obj B ⟶ A)
    (hd₁ : T.map p₁ ≫ d₁ ≫ i₁ = act.app E₁)
    (hd₂ : T.map p₂ ≫ d₂ ≫ i₂ = act.app E₂) :
    ∃ (E : C) (i : A ⟶ E) (p : E ⟶ B) (w : i ≫ p = 0)
      (h : (ShortComplex.mk i p w).ShortExact),
      h.extClass = h₁.extClass + h₂.extClass ∧
        T.map p ≫ (d₁ + d₂) ≫ i = act.app E := by
  classical
  set r : A ⟶ E₁ ⊞ E₂ := biprod.lift (-i₁) i₂ with hrdef
  have hT := shortExact_biprodRight h₁ E₂
  have hS := shortExact_biprodLeft h₂ B
  have hk : r ≫ biprod.map p₁ (𝟙 E₂) ≫ (Iso.refl (B ⊞ E₂)).hom = i₂ ≫ biprod.inr := by
    rw [hrdef]
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [w₁]
  -- the antidiagonal is killed by the quotient map, so the two copies of `A` agree in it
  have hrpi : i₁ ≫ biprod.inl ≫ cokernel.π r = i₂ ≫ biprod.inr ≫ cokernel.π r := by
    have hz : r ≫ cokernel.π r = 0 := cokernel.condition r
    have hz' : (-i₁) ≫ biprod.inl ≫ cokernel.π r + i₂ ≫ biprod.inr ≫ cokernel.π r = 0 := by
      rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, ← biprod.lift_eq, ← hrdef]
      exact hz
    simp only [Preadditive.neg_comp] at hz'
    exact neg_add_eq_zero.1 hz'
  -- the extension of `B ⊞ B` obtained by dividing `E₁ ⊞ E₂` by the antidiagonal
  obtain ⟨jm, qm, wm, hQT, hjm, hqm⟩ :
      ∃ (jm : A ⟶ cokernel r) (qm : cokernel r ⟶ B ⊞ B) (wm : jm ≫ qm = 0),
        (ShortComplex.mk jm qm wm).ShortExact ∧
          i₁ ≫ biprod.inl ≫ cokernel.π r = jm ∧
          cokernel.π r ≫ qm = biprod.map p₁ p₂ := by
    refine ⟨_, _, _, quotientShortComplex_shortExact hS hT r (Iso.refl _) hk,
      (Category.assoc _ _ _).symm, ?_⟩
    dsimp only [quotientDesc]
    rw [cokernel.π_desc]
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp
  have hP := pullbackShortComplex_shortExact hQT (biprod.lift (𝟙 B) (𝟙 B))
  refine ⟨_, _, _, _, hP, ?_, ?_⟩
  · exact (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).2.2
      E₁ E₂ _ _ i₁ p₁ w₁ i₂ p₂ w₂ _ _ _ jm qm wm h₁ h₂ hP hQT (cokernel.π r)
      (pullback.snd (biprod.lift (𝟙 B) (𝟙 B)) qm)
      (by
        refine biprod.hom_ext' _ _ ?_ ?_
        · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, Category.id_comp]
          exact hjm
        · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, Category.id_comp]
          exact hrpi.symm.trans hjm)
      hqm (pullback.lift_snd _ _ _) pullback.condition.symm
  · have hD := descendedAction_biprodQuotient T act (cokernel.π r) jm qm hqm hjm
      (hrpi.symm.trans hjm) (hTepi _ inferInstance) d₁ d₂ hd₁ hd₂
    have hw0 : (0 : A ⟶ B) ≫ biprod.lift (𝟙 B) (𝟙 B) = jm ≫ qm := by rw [zero_comp, wm]
    have hres := descendedAction_pullback T act (biprod.lift (𝟙 B) (𝟙 B))
      (pullback.lift (0 : A ⟶ B) jm hw0)
      (pullback.fst (biprod.lift (𝟙 B) (𝟙 B)) qm) (pullback.snd _ qm)
      (pullback.lift_fst _ _ hw0) (pullback.lift_snd _ _ hw0) pullback.condition.symm
      (fun _ _ ha hb => pullback.hom_ext ha hb) hactB _ hD
    have hΔD : T.map (biprod.lift (𝟙 B) (𝟙 B)) ≫
        (T.map biprod.fst ≫ d₁ + T.map biprod.snd ≫ d₂) = d₁ + d₂ := by
      rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, ← T.map_comp,
        ← T.map_comp, biprod.lift_fst, biprod.lift_snd, T.map_id, Category.id_comp,
        Category.id_comp]
    rw [hΔD] at hres
    exact hres

end BaerSum

section Descent

universe v v' w

/-- **An extension whose middle term descends, descends.** If a fully faithful exact functor `P`
has the middle term of a short exact sequence in its essential image, then the sequence is the
image of a short exact sequence in the source category, and the class of the latter is carried
to the class of the former. -/
theorem exists_shortExact_mapExactFunctor_extClass_eq
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type*} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
    (P : C ⥤ D) [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    [P.Full] [P.Faithful] {A B : C} {H : D} {a : P.obj A ⟶ H} {b : H ⟶ P.obj B}
    {w : a ≫ b = 0} (hS : (ShortComplex.mk a b w).ShortExact) (hH : P.essImage H) :
    ∃ (M : C) (f : A ⟶ M) (g : M ⟶ B) (w₀ : f ≫ g = 0)
      (h₀ : (ShortComplex.mk f g w₀).ShortExact),
      h₀.extClass.mapExactFunctor P = hS.extClass := by
  obtain ⟨M, ⟨e⟩⟩ := hH
  have hf : P.map (P.preimage (a ≫ e.inv)) = a ≫ e.inv := P.map_preimage _
  have hg : P.map (P.preimage (e.hom ≫ b)) = e.hom ≫ b := P.map_preimage _
  have w₀ : P.preimage (a ≫ e.inv) ≫ P.preimage (e.hom ≫ b) = 0 := by
    apply P.map_injective
    simp only [P.map_comp, P.map_zero, hf, hg, Category.assoc, e.inv_hom_id_assoc, w]
  have hfe : P.map (P.preimage (a ≫ e.inv)) ≫ e.hom = a := by
    rw [hf, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hge : e.hom ≫ b = P.map (P.preimage (e.hom ≫ b)) := hg.symm
  have h₀ : (ShortComplex.mk (P.preimage (a ≫ e.inv)) (P.preimage (e.hom ≫ b)) w₀).ShortExact := by
    apply ShortExact.reflects_shortExact_of_faithful P
    refine ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (S₁ := ShortComplex.mk a b w)
        (S₂ := (ShortComplex.mk (P.preimage (a ≫ e.inv)) (P.preimage (e.hom ≫ b)) w₀).map P)
        (Iso.refl _) e.symm (Iso.refl _) ?_ ?_) hS
    · simp
    · simp
  refine ⟨M, _, _, w₀, h₀, ?_⟩
  rw [Abelian.Ext.mapExactFunctor_extClass]
  exact ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum D (P.obj B) (P.obj A)).2.1
    _ _ _ _ _ _ _ _ (h₀.map_of_exact P) hS).2 ⟨e, hfe, hge⟩

/-- The class of the Yoneda extension attached to a short exact sequence is its class. -/
theorem extClass_shortExactYonedaExtension {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact) :
    (Abelian.YonedaExtension.shortExact (Abelian.shortExactYonedaExtension hS)).extClass =
      hS.extClass := rfl

end Descent

end CategoryTheory.Abelian

namespace AlgebraicGeometry.RingedSpaceThickening

open Stacks.SheafOfModules.TensorPresentations (tensorSheafMap_epi_of_epi_of_epi)

universe w

/- The sheaf of rings of a ringed space has two spellings here: `structureSheafRing`, at which
sheaves of modules are indexed, and `Stacks.SheafOfModules.Tensor.ringSheaf`, at which the tensor
product of `Stacks.SheafOfModules.Tensor.sheafTensor` is formed. They are definitionally equal,
but the latter is a plain definition, so neither instance search nor unification passes between
them: an `Add` on `ℐ ⊗ ℱ ⟶ 𝒦` is found only when the two agree at implicit transparency.
Unfolding the tensor bifunctor itself is what the matching must *not* do — each traversal
re-reduces the sheafification and the structure projection under it, which does not terminate
within the heartbeat budget — so the bifunctor is opaque and the ring sheaf transparent, and
the two spellings are then matched syntactically. Nothing about the terms produced changes. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Sheaf
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-- Tensoring with the ideal of a thickening, as a functor
`𝒩 ↦ ℐ ⊗_{𝒪_{X'}} 𝒩` on `𝒪_{X'}`-modules. -/
noncomputable def idealTensorFunctor :
    SheafOfModules.{u} (structureSheafRing X') ⥤ SheafOfModules.{u} (structureSheafRing X') where
  obj N := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩).obj ((AlgebraicGeometry.SheafOfModules.idealSheaf i))).obj (N))
  map f := ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 _), f) : (_, _) ⟶ (_, _)))
  map_id N := tensorSheafMap_id_id X' _ N
  map_comp f g := (tensorSheafMap_comp_right _ f g).symm

theorem idealTensorFunctor_map {N N' : SheafOfModules.{u} (structureSheafRing X')} (f : N ⟶ N') :
    (idealTensorFunctor i).map f =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), f) : (_, _) ⟶ (_, _))) := rfl

/-- Tensoring with the ideal preserves epimorphisms: this is the right-exactness statement
**Stacks 01CC** for the second factor. -/
theorem idealTensorFunctor_epi {N N' : SheafOfModules.{u} (structureSheafRing X')} (f : N ⟶ N')
    (hf : Epi f) : Epi ((idealTensorFunctor i).map f) := by
  let I : SheafOfModules.{u} (structureSheafRing X') :=
    AlgebraicGeometry.SheafOfModules.idealSheaf i
  let N₀ : SheafOfModules.{u} (structureSheafRing X') := N
  let N₁ : SheafOfModules.{u} (structureSheafRing X') := N'
  let f₀ : N₀ ⟶ N₁ := f
  have : Epi f₀ := hf
  exact tensorSheafMap_epi_of_epi_of_epi X' (𝟙 I) f₀

/-- The action of the ideal of a thickening on `𝒪_{X'}`-modules, as a natural transformation
`ℐ ⊗_{𝒪_{X'}} (-) ⟶ (-)`.  Naturality is
`AlgebraicGeometry.RingedSpaceThickening.idealAction_naturality`. -/
noncomputable def idealActionNatTrans :
    idealTensorFunctor i ⟶ 𝟭 (SheafOfModules.{u} (structureSheafRing X')) where
  app N := idealAction i N
  naturality _ _ φ := (idealAction_naturality i φ).symm

theorem idealActionNatTrans_app (N : SheafOfModules.{u} (structureSheafRing X')) :
    (idealActionNatTrans i).app N = idealAction i N := rfl

/-- The ideal acts as zero on a module in the essential image of `i_*`: **Stacks 08KS**, in the
form the descended-action machinery uses it. -/
theorem idealActionNatTrans_app_eq_zero_of_essImage (hi : IsThickening i)
    (N : SheafOfModules.{u} (structureSheafRing X')) (hN : (modulePushforward i).essImage N) :
    (idealActionNatTrans i).app N = 0 :=
  idealAction_eq_zero_of_essImage i hi N hN

/-- The ideal acts as zero on a direct image. -/
theorem idealActionNatTrans_app_pushforward_eq_zero (hi : IsThickening i)
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    (idealActionNatTrans i).app ((modulePushforward i).obj F) = 0 :=
  idealActionNatTrans_app_eq_zero_of_essImage i hi _
    (Functor.obj_mem_essImage (modulePushforward i) F)

section CanonicalMap

variable (F K : SheafOfModules.{u} (structureSheafRing X))

/-- The map `ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_* 𝒦` attached to an `𝒪_X`-linear
`c : i^* ℐ ⊗_{𝒪_X} ℱ ⟶ 𝒦`: the **Stacks 08L4** comparison followed by `i_* c`.

This is the form in which the canonical map of an extension is a *descended action* in the
sense of `CategoryTheory.Abelian.descendedAction_unique`; naming it is what makes the two
spellings of the structure sheaf of `X'` — the one at which the tensor product is formed and
the one at which sheaves of modules are indexed — agree on the nose, so that sums of such maps
are formed without transport. -/
noncomputable def descendedActionOfMap (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K) :
    (idealTensorFunctor i).obj ((modulePushforward i).obj F) ⟶ (modulePushforward i).obj K :=
  extensionTensorComparison i F ≫ (modulePushforward i).map c

/-- `AlgebraicGeometry.RingedSpaceThickening.descendedActionOfMap` is additive: `i_*` is an
additive functor and composition is additive. -/
theorem descendedActionOfMap_add (c c' : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K) :
    descendedActionOfMap i F K (c + c') =
      descendedActionOfMap i F K c + descendedActionOfMap i F K c' := by
  have h : (modulePushforward i).map (c + c') =
      (modulePushforward i).map c + (modulePushforward i).map c' := (modulePushforward i).map_add
  exact (congrArg (fun z => extensionTensorComparison i F ≫ z) h).trans
    (Preadditive.comp_add _ _ _ _ _ _)

/-- `AlgebraicGeometry.RingedSpaceThickening.descendedActionOfMap` is injective: the Tag 08L4
comparison is the adjoint transpose of an isomorphism
(`AlgebraicGeometry.RingedSpaceThickening.extensionTensorComparison_cancel`). -/
theorem descendedActionOfMap_injective (hi : IsThickening i)
    (c c' : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K)
    (h : descendedActionOfMap i F K c = descendedActionOfMap i F K c') : c = c' :=
  extensionTensorComparison_cancel i hi c c' h

/-- **Stacks 08L4, globally.** The canonical map of an extension is a descended action of the
ideal on the middle term. -/
theorem descendedAction_firstOrderExtensionAction (hi : IsFirstOrderThickening i)
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0) :
    (idealTensorFunctor i).map E.g ≫
        descendedActionOfMap i F K (firstOrderExtensionAction i F K hi E).val ≫ E.f =
      (idealActionNatTrans i).app E.Z.left :=
  firstOrderExtensionAction_comp i F K hi E

/-- **The canonical map of an extension is pinned down by the global lifting equation.** Any
`c` whose descended action recovers the action of the ideal on the middle term is the canonical
map of the extension: the equation determines the descended map because `1 ⊗ (ℱ' ⟶ i_* ℱ)` is
an epimorphism and `i_* 𝒦 ⟶ ℱ'` a monomorphism, and `descendedActionOfMap` is injective. -/
theorem eq_firstOrderExtensionAction_of_descendedAction (hi : IsFirstOrderThickening i)
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K)
    (hc : (idealTensorFunctor i).map E.g ≫ descendedActionOfMap i F K c ≫ E.f =
      (idealActionNatTrans i).app E.Z.left) :
    c = (firstOrderExtensionAction i F K hi E).val :=
  descendedActionOfMap_injective i F K hi.1 c _
    (CategoryTheory.Abelian.descendedAction_unique (idealTensorFunctor i) E.f E.g
      E.mono_f (idealTensorFunctor_epi i E.g E.epi_g) hc
      (descendedAction_firstOrderExtensionAction i F K hi E))

/-- `AlgebraicGeometry.RingedSpaceThickening.eq_firstOrderExtensionAction_of_descendedAction`
with the hypothesis written as in
`AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction_comp`. -/
theorem eq_firstOrderExtensionAction_of_comp (hi : IsFirstOrderThickening i)
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K)
    (hc : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), E.g) : (_, _) ⟶ (_, _))) ≫
        (extensionTensorComparison i F ≫ (modulePushforward i).map c) ≫ E.f =
      idealAction i E.Z.left) :
    c = (firstOrderExtensionAction i F K hi E).val :=
  eq_firstOrderExtensionAction_of_descendedAction i F K hi E c hc

variable [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing X'))]

/-- **The canonical map of an extension depends only on its class.** Two extensions of `i_* ℱ`
by `i_* 𝒦` with the same class in `Ext¹_{𝒪_{X'}}` have the same canonical map: they are
isomorphic over the identity of both end terms
(`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`), and the descended
action is transported by such an isomorphism. -/
theorem firstOrderExtensionAction_eq_of_extClass_eq (hi : IsFirstOrderThickening i)
    (E E' : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (h : (CategoryTheory.Abelian.YonedaExtension.shortExact E).extClass =
      (CategoryTheory.Abelian.YonedaExtension.shortExact E').extClass) :
    (firstOrderExtensionAction i F K hi E).val =
      (firstOrderExtensionAction i F K hi E').val := by
  obtain ⟨φ, hφ₁, hφ₂⟩ :=
    ((CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
        (SheafOfModules.{u} (structureSheafRing X')) ((modulePushforward i).obj F)
        ((modulePushforward i).obj K)).2.1
      E.Z.left E'.Z.left E.f E.g _ E'.f E'.g _
      (CategoryTheory.Abelian.YonedaExtension.shortExact E)
      (CategoryTheory.Abelian.YonedaExtension.shortExact E')).1 h
  exact eq_firstOrderExtensionAction_of_descendedAction i F K hi E' _
    (CategoryTheory.Abelian.descendedAction_iso (idealTensorFunctor i) (idealActionNatTrans i)
      φ hφ₁ hφ₂ (descendedAction_firstOrderExtensionAction i F K hi E))

/-- Equivalent Yoneda extensions have the same canonical map: equivalence of Yoneda extensions
is equality of their classes. -/
theorem firstOrderExtensionAction_eq_of_equivalent (hi : IsFirstOrderThickening i)
    (E E' : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (h : E.Equivalent E') :
    (firstOrderExtensionAction i F K hi E).val =
      (firstOrderExtensionAction i F K hi E').val := by
  refine firstOrderExtensionAction_eq_of_extClass_eq i F K hi E E' ?_
  have h₁ := CategoryTheory.Abelian.isExtClassMap_extClassMap.1
    ((modulePushforward i).obj F) ((modulePushforward i).obj K) E
    (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E)
    (CategoryTheory.Abelian.YonedaExtension.shortExact E)
  have h₂ := CategoryTheory.Abelian.isExtClassMap_extClassMap.1
    ((modulePushforward i).obj F) ((modulePushforward i).obj K) E'
    (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E')
    (CategoryTheory.Abelian.YonedaExtension.shortExact E')
  exact h₁.symm.trans ((CategoryTheory.Abelian.extClassMap_eq_of_equivalent h).trans h₂)

/-- **The canonical map is additive for Baer sums.** Given two extensions of `i_* ℱ` by `i_* 𝒦`
across the thickening there is a third one — their Baer sum — whose class in `Ext¹` is the sum
of the two classes and whose canonical map is the sum of the two canonical maps.

Together with
`AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction_eq_of_extClass_eq` this says
that the canonical map is an additive function of the class of the extension. It is the
computation behind **Stacks 08L7**: two extensions have the same canonical map exactly when
their classes differ by one whose canonical map vanishes, and by **Stacks 08KS** the latter are
exactly the extensions of `𝒪_X`-modules. -/
theorem exists_baerSum_firstOrderExtensionAction (hi : IsFirstOrderThickening i)
    (E₁ E₂ : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0) :
    ∃ E : CategoryTheory.Abelian.YonedaExtension
        ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
      (CategoryTheory.Abelian.YonedaExtension.shortExact E).extClass =
          (CategoryTheory.Abelian.YonedaExtension.shortExact E₁).extClass +
            (CategoryTheory.Abelian.YonedaExtension.shortExact E₂).extClass ∧
        (firstOrderExtensionAction i F K hi E).val =
          (firstOrderExtensionAction i F K hi E₁).val +
            (firstOrderExtensionAction i F K hi E₂).val := by
  obtain ⟨M, iM, pM, wM, hM, hclass, haction⟩ :=
    CategoryTheory.Abelian.exists_shortExact_extClass_add_descendedAction
      (idealTensorFunctor i) (idealActionNatTrans i)
      (fun φ hφ => idealTensorFunctor_epi i φ hφ)
      (CategoryTheory.Abelian.YonedaExtension.shortExact E₁)
      (CategoryTheory.Abelian.YonedaExtension.shortExact E₂)
      (idealActionNatTrans_app_pushforward_eq_zero i hi.1 F)
      (descendedActionOfMap i F K (firstOrderExtensionAction i F K hi E₁).val)
      (descendedActionOfMap i F K (firstOrderExtensionAction i F K hi E₂).val)
      (descendedAction_firstOrderExtensionAction i F K hi E₁)
      (descendedAction_firstOrderExtensionAction i F K hi E₂)
  refine ⟨CategoryTheory.Abelian.shortExactYonedaExtension hM, hclass, ?_⟩
  refine (eq_firstOrderExtensionAction_of_descendedAction i F K hi
    (CategoryTheory.Abelian.shortExactYonedaExtension hM) _ ?_).symm
  rw [descendedActionOfMap_add]
  exact haction

omit [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing X'))] in
/-- An extension across the thickening whose middle term is a direct image has vanishing
canonical map: the ideal annihilates a direct image (**Stacks 08KS**). -/
theorem firstOrderExtensionAction_eq_zero_of_essImage (hi : IsFirstOrderThickening i)
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (hE : (modulePushforward i).essImage E.Z.left) :
    (firstOrderExtensionAction i F K hi E).val = 0 := by
  have hz : descendedActionOfMap i F K 0 = 0 := by
    have h : (modulePushforward i).map (0 : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((idealSheafPullback i))).obj (F)) ⟶ K) = 0 :=
      (modulePushforward i).map_zero _ _
    exact (congrArg (fun z => extensionTensorComparison i F ≫ z) h).trans comp_zero
  refine (eq_firstOrderExtensionAction_of_descendedAction i F K hi E 0 ?_).symm
  rw [hz, zero_comp, comp_zero]
  exact (idealActionNatTrans_app_eq_zero_of_essImage i hi.1 E.Z.left hE).symm

/-- **Stacks 08L7, the action.** Adding to an extension one whose middle term is a direct
image does not change the canonical map: such an extension has vanishing canonical map
(**Stacks 08KS**) and the canonical map is additive for Baer sums
(`AlgebraicGeometry.RingedSpaceThickening.exists_baerSum_firstOrderExtensionAction`).

This is the source's "conversely, given such an extension `ℰ` we can add the extension `ℰ` to
the `𝒪_{X'}`-extension `ℱ'` without affecting the map `c_{ℱ'}`". By **Stacks 08KS** the
extensions whose middle term is a direct image are exactly the extensions of `𝒪_X`-modules,
which is how `Ext¹_{𝒪_X}(ℱ, 𝒦)` acts. -/
@[stacks 08L7 "the action of `Ext¹_{𝒪_X}(ℱ, 𝒦)`: adding an extension of `𝒪_X`-modules, read \
on `X'` as one whose middle term is a direct image, does not change the canonical map. SCOPE: \
this clause only; the simple transitivity of the action is \
`existsUnique_extClass_sub_of_firstOrderExtensionAction_eq`, and the identification of the \
subgroup of such classes with `Ext¹_{𝒪_X}(ℱ, 𝒦)` itself is not formalized here"]
theorem exists_extClass_add_of_essImage (hi : IsFirstOrderThickening i)
    (E₀ D : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (hD : (modulePushforward i).essImage D.Z.left) :
    ∃ E : CategoryTheory.Abelian.YonedaExtension
        ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
      (CategoryTheory.Abelian.YonedaExtension.shortExact E).extClass =
          (CategoryTheory.Abelian.YonedaExtension.shortExact E₀).extClass +
            (CategoryTheory.Abelian.YonedaExtension.shortExact D).extClass ∧
        (firstOrderExtensionAction i F K hi E).val =
          (firstOrderExtensionAction i F K hi E₀).val := by
  obtain ⟨E, hEcl, hEact⟩ := exists_baerSum_firstOrderExtensionAction i F K hi E₀ D
  refine ⟨E, hEcl, ?_⟩
  rw [hEact, firstOrderExtensionAction_eq_zero_of_essImage i F K hi D hD, add_zero]

/-- **Stacks 08L7, simple transitivity.** Two extensions across the thickening with the same
canonical map differ, in `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`, by the class of exactly one extension
whose middle term is a direct image — hence, by **Stacks 08KS**, by the class of an extension of
`𝒪_X`-modules.

This is the source's "the difference is an extension `0 → 𝒦 → ℰ → ℱ → 0` where `ℰ` is
annihilated by `ℐ`, hence is an extension of `𝒪_X`-modules". Uniqueness is uniqueness of a
difference in the group `Ext¹_{𝒪_{X'}}(i_* ℱ, i_* 𝒦)`. -/
@[stacks 08L7 "simple transitivity: two extensions with the same canonical map differ by the \
class of exactly one extension whose middle term is a direct image, i.e. of an extension of \
`𝒪_X`-modules. SCOPE: this clause only; the identification of the group of such classes with \
`Ext¹_{𝒪_X}(ℱ, 𝒦)` itself is not formalized here"]
theorem existsUnique_extClass_sub_of_firstOrderExtensionAction_eq (hi : IsFirstOrderThickening i)
    (E₀ E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (h : (firstOrderExtensionAction i F K hi E).val =
      (firstOrderExtensionAction i F K hi E₀).val) :
    ∃! ξ : CategoryTheory.Abelian.Ext.{w}
        ((modulePushforward i).obj F) ((modulePushforward i).obj K) 1,
      (CategoryTheory.Abelian.YonedaExtension.shortExact E).extClass =
          (CategoryTheory.Abelian.YonedaExtension.shortExact E₀).extClass + ξ ∧
        ∃ D : CategoryTheory.Abelian.YonedaExtension
            ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0,
          (CategoryTheory.Abelian.YonedaExtension.shortExact D).extClass = ξ ∧
            (modulePushforward i).essImage D.Z.left := by
  obtain ⟨Dm, df, dg, dw, hD, hDcl⟩ :=
    (CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (SheafOfModules.{u} (structureSheafRing X')) ((modulePushforward i).obj F)
      ((modulePushforward i).obj K)).1
      ((CategoryTheory.Abelian.YonedaExtension.shortExact E).extClass -
        (CategoryTheory.Abelian.YonedaExtension.shortExact E₀).extClass)
  have hDclass : (CategoryTheory.Abelian.YonedaExtension.shortExact
      (CategoryTheory.Abelian.shortExactYonedaExtension hD)).extClass =
      (CategoryTheory.Abelian.YonedaExtension.shortExact E).extClass -
        (CategoryTheory.Abelian.YonedaExtension.shortExact E₀).extClass :=
    (CategoryTheory.Abelian.extClass_shortExactYonedaExtension hD).trans hDcl
  obtain ⟨E', hE'cl, hE'act⟩ := exists_baerSum_firstOrderExtensionAction i F K hi E₀
    (CategoryTheory.Abelian.shortExactYonedaExtension hD)
  have hE'E : (CategoryTheory.Abelian.YonedaExtension.shortExact E').extClass =
      (CategoryTheory.Abelian.YonedaExtension.shortExact E).extClass := by
    rw [hE'cl, hDclass]
    abel
  have hDact : (firstOrderExtensionAction i F K hi
      (CategoryTheory.Abelian.shortExactYonedaExtension hD)).val = 0 := by
    have hEE' := firstOrderExtensionAction_eq_of_extClass_eq i F K hi E' E hE'E
    rw [hE'act, h] at hEE'
    exact add_left_cancel (hEE'.trans (add_zero _).symm)
  have hEss : (modulePushforward i).essImage
      (CategoryTheory.Abelian.shortExactYonedaExtension hD).Z.left :=
    essImage_of_extensionAction_eq_zero i hi F K _
      (by rw [hDact]; exact (modulePushforward i).map_zero _ _)
  refine ⟨(CategoryTheory.Abelian.YonedaExtension.shortExact E).extClass -
      (CategoryTheory.Abelian.YonedaExtension.shortExact E₀).extClass,
    ⟨by abel, CategoryTheory.Abelian.shortExactYonedaExtension hD, hDclass, hEss⟩, ?_⟩
  intro ξ hξ
  rw [hξ.1]
  abel

end CanonicalMap

/-- **Exactness of `i_*` for a thickening, the colimit half.** Direct image along a thickening
is a left adjoint — its right adjoint is sheaf `Hom` with exact support (**Stacks 0A75**) — so
it preserves finite colimits. -/
theorem preservesFiniteColimits_modulePushforward (hi : IsThickening i) :
    Limits.PreservesFiniteColimits (modulePushforward i) := by
  have : (modulePushforward i).IsLeftAdjoint :=
    ⟨_, ⟨(closedQuotientOfIsThickening i hi).modulePushforwardSheafHomExactSupportAdjunction⟩⟩
  infer_instance

/-- **Exactness of `i_*`, the limit half.** Direct image is a right adjoint
(**Stacks 0096**). -/
theorem preservesFiniteLimits_modulePushforward :
    Limits.PreservesFiniteLimits (modulePushforward i) := by
  have : (modulePushforward i).IsRightAdjoint := modulePushforward_isRightAdjoint i
  infer_instance

end AlgebraicGeometry.RingedSpaceThickening

end
