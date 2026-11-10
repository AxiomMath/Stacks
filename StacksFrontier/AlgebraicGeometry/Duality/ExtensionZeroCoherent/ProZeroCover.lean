module

public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemCovering
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictFunctorOpensRange
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingCover

/-!
# Pro-zero systems: third terms of a pro-isomorphism, and locality on the scheme

This file contains two facts about inverse systems which vanish as pro-objects.

The first is the converse of [Stacks, Tag 0G3C]. Let `A_j ⟶ B_j ⟶ C_j ⟶ A_j[1]` be an inverse
system of distinguished triangles in a pre-triangulated category. If the morphisms `A_j ⟶ B_j`
are an isomorphism of pro-objects, then the system `(C_j)` of third terms is pro-zero: below every
index there is an arrow along which the transition morphism of third terms vanishes. Indeed, if
`s : B_k ⟶ A_j` inverts the first morphisms along `f : k ⟶ j`, the transition `c : C_k ⟶ C_j`
vanishes after `B_k ⟶ C_k`, so it factors through `C_k ⟶ A_k[1]`; composing with a second
transition `C_{k'} ⟶ C_k` along which the first morphisms are inverted, the composite factors
through `C_{k'} ⟶ A_{k'}[1] ⟶ B_{k'}[1]`, which is zero.

The second is that being pro-zero is local on a quasi-compact scheme `X`: an inverse system
`(K_n)` in `D(𝒪_X)` whose restrictions to the members of an open covering of `X` are pro-zero is
itself pro-zero. The key case is that of two opens `X = V ∪ W`: if `a : A ⟶ B` vanishes on
`V ∩ W` and `b : B ⟶ C` vanishes on `V` and on `W`, then `a ≫ b = 0`. To see it, represent `C`
by a K-injective complex `J` with injective terms; its Mayer--Vietoris sequence gives a
distinguished triangle

`C ⟶ j_{V*}(J|_V) ⊕ j_{W*}(J|_W) ⟶ j_{V∩W*}(J|_{V∩W}) ⟶ C[1]`

in `D(𝒪_X)`, and restriction to an open `O` is bijective on morphisms into `j_{O*}(J|_O)` and its
shifts. Hence `b` vanishes after the first morphism of the triangle, so it factors through
`j_{V∩W*}(J|_{V∩W})[-1] ⟶ C`, and `a` followed by the factorization is determined by its
restriction to `V ∩ W`, which is zero. An induction over a finite subcovering then proves the
locality, transition morphisms being composed at each step.

## Main results

* `CategoryTheory.Pretriangulated.proZero_π₃_of_proInverse_mor₁`: the converse of
  [Stacks, Tag 0G3C].
* `AlgebraicGeometry.comp_eq_zero_of_sup_eq_top`: the case of two opens.
* `AlgebraicGeometry.proZero_restrict_sup`: the inductive step.
* `AlgebraicGeometry.proZero_of_isOpenImmersion_cover`: **pro-zero is local on a quasi-compact
  scheme**.

## Implementation notes

Everything is at `CategoryTheory.HasDerivedCategory.standard`, the model of
`AlgebraicGeometry.BoundedCoherentDerived`. A system `(K_n)` indexed by `ℕᵒᵖ` is pro-zero when for
every `n` there is `m ≥ n` with `K_m ⟶ K_n` zero; that on an open immersion `f` it is pro-zero
means the same of the restricted system. Restriction along `f` and restriction to the open
`f.opensRange` differ by an equivalence of derived categories, so they detect the vanishing of
the same morphisms.

## References

* [Stacks Project, Tag 0G3C](https://stacks.math.columbia.edu/tag/0G3C)
* [Stacks Project, Tag 0G4U](https://stacks.math.columbia.edu/tag/0G4U)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe v v' u u'

namespace CategoryTheory.Pretriangulated

variable {J : Type u} [Category.{v} J] {D : Type u'} [Category.{v'} D]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **The converse of Stacks 0G3C.** Let `T : J ⥤ Triangle 𝒟` be an inverse system of
distinguished triangles `A_j ⟶ B_j ⟶ C_j ⟶ A_j[1]` in a pre-triangulated category. If the
morphisms `A_j ⟶ B_j` determine an isomorphism of pro-objects between `(A_j)` and `(B_j)`, in the
form of `CategoryTheory.Pretriangulated.exists_proInverse_mor₁_of_proZero_π₃`, then the inverse
system `(C_j)` of third terms is pro-zero: every index admits an arrow along which the transition
morphism of third terms vanishes. -/
public theorem proZero_π₃_of_proInverse_mor₁ (T : J ⥤ Triangle D)
    (hT : ∀ j, T.obj j ∈ distTriang D)
    (h₁ : ∀ j : J, ∃ (k : J) (f : k ⟶ j) (s : (T.obj k).obj₂ ⟶ (T.obj j).obj₁),
      (T.obj k).mor₁ ≫ s = (T.map f).hom₁ ∧ s ≫ (T.obj j).mor₁ = (T.map f).hom₂) (j : J) :
    ∃ (k : J) (f : k ⟶ j), (T.map f).hom₃ = 0 := by
  obtain ⟨k, f, s, -, hs₂⟩ := h₁ j
  obtain ⟨k', f', s', hs₁', -⟩ := h₁ k
  -- the transition `C_k ⟶ C_j` factors through `C_k ⟶ A_k[1]`
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (hT k) (T.map f).hom₃ (by
    rw [(T.map f).comm₂, ← hs₂, Category.assoc, comp_distTriang_mor_zero₁₂ _ (hT j),
      comp_zero])
  refine ⟨k', f' ≫ f, ?_⟩
  rw [T.map_comp, comp_hom₃, hg, ← Category.assoc, ← (T.map f').comm₃, ← hs₁',
    Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (T.obj k').mor₃, comp_distTriang_mor_zero₃₁ _ (hT k'), zero_comp]

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

open Stacks.Duality.OpenImmersion (derivedRestrict)
open Stacks.Duality.Coherator (pushRestrictFunctor)

/-- **Vanishing after restriction along a composite of open immersions.** For open immersions
`k : Z ⟶ Y` and `g : Y ⟶ X` with composite `h`, a morphism of `D(𝒪_X)` vanishes after
restriction along `h` if and only if it vanishes after restriction along `g` and then along
`k`. -/
public lemma derivedRestrict_map_eq_zero_iff_of_comp_eq {Z Y X : Scheme.{u}} (k : Z ⟶ Y)
    (g : Y ⟶ X) (h : Z ⟶ X) [IsOpenImmersion k] [IsOpenImmersion g] [IsOpenImmersion h]
    (hkg : k ≫ g = h) {A B : DerivedCategory X.Modules} (φ : A ⟶ B) :
    (derivedRestrict h).map φ = 0 ↔ (derivedRestrict k).map ((derivedRestrict g).map φ) = 0 := by
  let : PreservesFiniteLimits (Scheme.Modules.restrictFunctor g ⋙
      Scheme.Modules.restrictFunctor k) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (Scheme.Modules.restrictFunctor g ⋙
      Scheme.Modules.restrictFunctor k) := comp_preservesFiniteColimits _ _
  let e : derivedRestrict h ≅ derivedRestrict g ⋙ derivedRestrict k :=
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (Scheme.Modules.restrictFunctorCongr hkg.symm ≪≫ Scheme.Modules.restrictFunctorComp k g) ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _
  have hn := e.hom.naturality φ
  simp only [Functor.comp_map] at hn
  refine ⟨fun hφ => ?_, fun hφ => ?_⟩
  · rw [hφ, zero_comp] at hn
    exact (cancel_epi (e.hom.app A)).1 (hn.symm.trans comp_zero.symm)
  · rw [hφ, comp_zero] at hn
    exact (cancel_mono (e.hom.app B)).1 (hn.trans zero_comp.symm)

/-- A morphism vanishing after restriction along `g` vanishes after restriction along any open
immersion `h` factoring through `g`. -/
private lemma derivedRestrict_map_eq_zero_of_comp_eq {Z Y X : Scheme.{u}} (k : Z ⟶ Y) (g : Y ⟶ X)
    (h : Z ⟶ X) [IsOpenImmersion k] [IsOpenImmersion g] [IsOpenImmersion h] (hkg : k ≫ g = h)
    {A B : DerivedCategory X.Modules} {φ : A ⟶ B} (hφ : (derivedRestrict g).map φ = 0) :
    (derivedRestrict h).map φ = 0 :=
  (derivedRestrict_map_eq_zero_iff_of_comp_eq k g h hkg φ).2 (by rw [hφ, Functor.map_zero])

/-- Restriction along an isomorphism of schemes detects the vanishing of morphisms of derived
categories: it is an equivalence. -/
public lemma derivedRestrict_map_eq_zero_iff_of_isIso {Y X : Scheme.{u}} (k : Y ⟶ X) [IsIso k]
    {A B : DerivedCategory X.Modules} (φ : A ⟶ B) : (derivedRestrict k).map φ = 0 ↔ φ = 0 := by
  have := Scheme.Modules.isEquivalence_mapDerivedCategory_restrictFunctor_of_isIso k
  exact ⟨fun h => (derivedRestrict k).map_injective (by rw [h, Functor.map_zero]),
    fun h => by rw [h, Functor.map_zero]⟩

variable {X : Scheme.{u}}

/-- The image in `D(𝒪_X)` of the Mayer--Vietoris bicone of a complex `J` satisfies the biproduct
identity `fst ≫ inl + snd ≫ inr = 𝟙`. -/
private lemma mvBicone_Q_map_total (V W : X.Opens) (J : CochainComplex X.Modules ℤ) :
    DerivedCategory.Q.map (Stacks.Duality.Coherator.mvBicone V W J).fst ≫
        DerivedCategory.Q.map (Stacks.Duality.Coherator.mvBicone V W J).inl +
      DerivedCategory.Q.map (Stacks.Duality.Coherator.mvBicone V W J).snd ≫
        DerivedCategory.Q.map (Stacks.Duality.Coherator.mvBicone V W J).inr = 𝟙 _ := by
  have htot : (Stacks.Duality.Coherator.mvBicone V W J).fst ≫
        (Stacks.Duality.Coherator.mvBicone V W J).inl +
      (Stacks.Duality.Coherator.mvBicone V W J).snd ≫
        (Stacks.Duality.Coherator.mvBicone V W J).inr = 𝟙 _ := by
    ext n : 1
    exact biprod.total (X := (pushRestrictFunctor V).obj (J.X n))
      (Y := (pushRestrictFunctor W).obj (J.X n))
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
    ← DerivedCategory.Q.map_add, htot, DerivedCategory.Q.map_id]

/-- For a K-injective complex `J`, a morphism into `j_{O*}(J|_O)[-1]` vanishes as soon as its
restriction to `O` does. -/
private lemma eq_zero_of_derivedRestrict_map_eq_zero_shift_pushRestrict (O : X.Opens)
    (J : CochainComplex X.Modules ℤ) [J.IsKInjective] {A : DerivedCategory X.Modules}
    (g : A ⟶ (DerivedCategory.Q.obj (((pushRestrictFunctor O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J))⟦(-1 : ℤ)⟧) (hg : (derivedRestrict O.ι).map g = 0) :
    g = 0 := by
  let sIso : (DerivedCategory.Q.obj (((pushRestrictFunctor O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J))⟦(-1 : ℤ)⟧ ≅
      DerivedCategory.Q.obj (((pushRestrictFunctor O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (J⟦(-1 : ℤ)⟧)) :=
    ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).app _).symm ≪≫
      DerivedCategory.Q.mapIso
        (((pushRestrictFunctor O).mapCochainComplexShiftIso (-1)).app J).symm
  exact (bijective_map_of_iso_target (derivedRestrict O.ι) sIso.symm
    (bijective_restrict_map_pushRestrict O (J⟦(-1 : ℤ)⟧)) A).1
    (hg.trans (Functor.map_zero _ _ _).symm)

/-- **Vanishing of a composite is local for a covering by two opens.** Let `X = V ∪ W` and let
`a : A ⟶ B`, `b : B ⟶ C` be morphisms of `D(𝒪_X)` such that `a` vanishes on `V ∩ W` and `b`
vanishes on `V` and on `W`. Then `a ≫ b = 0`.

This is a chase in the Mayer--Vietoris triangle
`C ⟶ j_{V*}(J|_V) ⊕ j_{W*}(J|_W) ⟶ j_{V∩W*}(J|_{V∩W}) ⟶ C[1]` of a K-injective complex `J`
with injective terms representing `C`, using that restriction to an open `O` is bijective on
morphisms into `j_{O*}(J|_O)`. -/
public theorem comp_eq_zero_of_sup_eq_top (V W : X.Opens) (hVW : V ⊔ W = ⊤)
    {A B C : DerivedCategory X.Modules} (a : A ⟶ B) (b : B ⟶ C)
    (ha : (derivedRestrict (V ⊓ W).ι).map a = 0) (hbV : (derivedRestrict V.ι).map b = 0)
    (hbW : (derivedRestrict W.ι).map b = 0) : a ≫ b = 0 := by
  obtain ⟨J, hinj, hJ, ⟨eJ⟩⟩ := exists_kInjective_Q_iso C
  have := hJ
  let hS := Stacks.Duality.Coherator.mvShortComplex_shortExact V W J hinj
  let T := DerivedCategory.triangleOfSES hS
  have hT : T ∈ distTriang (DerivedCategory X.Modules) :=
    DerivedCategory.triangleOfSES_distinguished hS
  let topIso : ((pushRestrictFunctor (V ⊔ W)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J ≅
      J :=
    (NatIso.mapHomologicalComplex (eqToIso (congrArg pushRestrictFunctor hVW) ≪≫
        Stacks.Duality.Coherator.pushRestrictTopIso.symm) (ComplexShape.up ℤ)).app J ≪≫
      (Functor.mapHomologicalComplexIdIso _ _).app J
  let e : C ≅ T.obj₁ := eJ.symm ≪≫ (DerivedCategory.Q.mapIso topIso).symm
  let bc := Stacks.Duality.Coherator.mvBicone V W J
  -- `b` vanishes after the first morphism of the triangle
  let x : B ⟶ DerivedCategory.Q.obj bc.pt := b ≫ e.hom ≫ T.mor₁
  have hO : ∀ (O : X.Opens) (p : DerivedCategory.Q.obj bc.pt ⟶ DerivedCategory.Q.obj
      (((pushRestrictFunctor O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)),
      (derivedRestrict O.ι).map b = 0 → x ≫ p = 0 := fun O p hb =>
    (bijective_restrict_map_pushRestrict O J B).1 (by
      dsimp only
      have hx : (derivedRestrict O.ι).map x = 0 :=
        (Functor.map_comp _ b (e.hom ≫ T.mor₁)).trans (by rw [hb]; exact zero_comp)
      refine (Functor.map_comp _ x p).trans ?_
      rw [hx, zero_comp]
      exact (Functor.map_zero _ _ _).symm)
  have hx : x = 0 := by
    rw [← Category.comp_id x, ← mvBicone_Q_map_total V W J, Preadditive.comp_add,
      ← Category.assoc, ← Category.assoc, hO V _ hbV, hO W _ hbW, zero_comp, zero_comp, add_zero]
  -- so it factors through the shifted third term
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T.invRotate (inv_rot_of_distTriang _ hT)
    (b ≫ e.hom) ((Category.assoc _ _ _).trans hx)
  -- and `a` followed by the factorization is determined on `V ∩ W`
  have hag : (derivedRestrict (V ⊓ W).ι).map (a ≫ g) = 0 := by
    rw [Functor.map_comp, ha, zero_comp]
  have h₂ : a ≫ g = 0 := eq_zero_of_derivedRestrict_map_eq_zero_shift_pushRestrict (V ⊓ W) J _ hag
  have h₃ : (a ≫ b) ≫ e.hom = (a ≫ g) ≫ T.invRotate.mor₁ := by
    rw [Category.assoc, Category.assoc]
    exact congrArg (a ≫ ·) hg
  rw [h₂] at h₃
  exact (cancel_mono e.hom).1 (h₃.trans (zero_comp.trans zero_comp.symm))

/-- **The inductive step**: if an inverse system `(K_n)` in `D(𝒪_X)` is pro-zero after
restriction to each of two opens `O₁` and `O₂`, it is pro-zero after restriction to
`O₁ ∪ O₂`. -/
public theorem proZero_restrict_sup (C : ℕᵒᵖ ⥤ DerivedCategory X.Modules) (O₁ O₂ : X.Opens)
    (h₁ : ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m),
      (derivedRestrict O₁.ι).map (C.map (homOfLE hnm).op) = 0)
    (h₂ : ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m),
      (derivedRestrict O₂.ι).map (C.map (homOfLE hnm).op) = 0) :
    ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m),
      (derivedRestrict (O₁ ⊔ O₂).ι).map (C.map (homOfLE hnm).op) = 0 := by
  have hcomp : ∀ {n m m' : ℕ} (hnm : n ≤ m) (hmm' : m ≤ m'),
      C.map (homOfLE (hnm.trans hmm')).op = C.map (homOfLE hmm').op ≫ C.map (homOfLE hnm).op :=
    fun _ _ => by rw [← C.map_comp]; rfl
  have mono : ∀ (O : X.Opens) {n m m' : ℕ} (hnm : n ≤ m) (hmm' : m ≤ m'),
      (derivedRestrict O.ι).map (C.map (homOfLE hnm).op) = 0 →
        (derivedRestrict O.ι).map (C.map (homOfLE (hnm.trans hmm')).op) = 0 :=
    fun O _ _ _ hnm hmm' h => by rw [hcomp hnm hmm', Functor.map_comp, h, comp_zero]
  have both : ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m),
      (derivedRestrict O₁.ι).map (C.map (homOfLE hnm).op) = 0 ∧
        (derivedRestrict O₂.ι).map (C.map (homOfLE hnm).op) = 0 := fun n => by
    obtain ⟨m₁, hm₁, e₁⟩ := h₁ n
    obtain ⟨m₂, hm₂, e₂⟩ := h₂ n
    exact ⟨max m₁ m₂, hm₁.trans (le_max_left _ _), mono O₁ hm₁ (le_max_left _ _) e₁,
      mono O₂ hm₂ (le_max_right _ _) e₂⟩
  intro n
  obtain ⟨m₁, hnm₁, b₁, b₂⟩ := both n
  obtain ⟨m₂, hm₁m₂, a₁, -⟩ := both m₁
  refine ⟨m₂, hnm₁.trans hm₁m₂, ?_⟩
  set T := O₁ ⊔ O₂
  have hcover : T.ι ⁻¹ᵁ O₁ ⊔ T.ι ⁻¹ᵁ O₂ = ⊤ := by
    change T.ι ⁻¹ᵁ T = ⊤
    exact T.ι_preimage_self
  -- a morphism vanishing on `O` vanishes on the open `T ∩ O` of `T`
  have restr : ∀ (O : X.Opens) {E F : DerivedCategory X.Modules} (φ : E ⟶ F),
      (derivedRestrict O.ι).map φ = 0 →
        (derivedRestrict (T.ι ⁻¹ᵁ O).ι).map ((derivedRestrict T.ι).map φ) = 0 :=
    fun O _ _ φ hφ =>
      (derivedRestrict_map_eq_zero_iff_of_comp_eq _ _ _ rfl φ).1
        (derivedRestrict_map_eq_zero_of_comp_eq (T.ι ∣_ O) O.ι _ (morphismRestrict_ι T.ι O) hφ)
  rw [hcomp hnm₁ hm₁m₂, Functor.map_comp]
  refine comp_eq_zero_of_sup_eq_top (T.ι ⁻¹ᵁ O₁) (T.ι ⁻¹ᵁ O₂) hcover _ _ ?_
    (restr O₁ _ b₁) (restr O₂ _ b₂)
  exact derivedRestrict_map_eq_zero_of_comp_eq
    (Scheme.homOfLE _ (inf_le_left : T.ι ⁻¹ᵁ O₁ ⊓ T.ι ⁻¹ᵁ O₂ ≤ _)) (T.ι ⁻¹ᵁ O₁).ι _
    (Scheme.homOfLE_ι _ _) (restr O₁ _ a₁)

/-- **Pro-zero is local on a quasi-compact scheme.** Let `X` be a quasi-compact scheme and
`(K_n)` an inverse system in `D(𝒪_X)`. Suppose every point of `X` lies in the image of an open
immersion `f : Y ⟶ X` such that the restricted system `(K_n|_Y)` is pro-zero, i.e. for every `n`
there is `m ≥ n` with `K_m|_Y ⟶ K_n|_Y` zero. Then `(K_n)` is pro-zero.

Finitely many of the images cover `X`, and the pro-zero property passes to a union of two opens
by `AlgebraicGeometry.proZero_restrict_sup`. -/
public theorem proZero_of_isOpenImmersion_cover {X : Scheme.{u}} [CompactSpace X]
    (C : ℕᵒᵖ ⥤ DerivedCategory X.Modules)
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsOpenImmersion f), x ∈ Set.range f.base ∧
      ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m),
        (Scheme.Modules.restrictFunctor f).mapDerivedCategory.map (C.map (homOfLE hnm).op) = 0) :
    ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m), C.map (homOfLE hnm).op = 0 := by
  classical
  -- each point lies in an open on which the system is pro-zero
  have h' : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m),
      (derivedRestrict O.ι).map (C.map (homOfLE hnm).op) = 0 := by
    intro x
    obtain ⟨Y, f, hf, hx, hC⟩ := h x
    refine ⟨f.opensRange, ?_, fun n => ?_⟩
    · change x ∈ (f.opensRange : Set X)
      rw [Scheme.Hom.coe_opensRange]
      exact hx
    · obtain ⟨m, hnm, e⟩ := hC n
      exact ⟨m, hnm, derivedRestrict_map_eq_zero_of_comp_eq f.isoOpensRange.inv f _
        (Scheme.Hom.isoOpensRange_inv_comp f) e⟩
  choose O hxO hO using h'
  -- a finite subcovering
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => (O x : Set X))
    (fun x => (O x).isOpen.mem_nhds (hxO x))
  have htop : t.sup O = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ ⋃ x ∈ t, (O x : Set X) := by rw [ht]; trivial
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 hy
    exact (Finset.le_sup hxt : O x ≤ t.sup O) hyx
  -- induction on the number of opens
  have key : ∀ s : Finset X, ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m),
      (derivedRestrict (s.sup O).ι).map (C.map (homOfLE hnm).op) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty]
      have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x => by simpa using x.2⟩
      exact fun n => ⟨n, le_rfl, (isZero_derivedCategory_of_isEmpty _).eq_of_src _ _⟩
    | insert a s _ ih =>
      rw [Finset.sup_insert]
      exact proZero_restrict_sup C _ _ (hO a) ih
  -- from the open subscheme `⊤` back to `X`
  intro n
  obtain ⟨m, hnm, e⟩ := key t n
  rw [htop] at e
  refine ⟨m, hnm, (derivedRestrict_map_eq_zero_iff_of_isIso (𝟙 X) _).1 ?_⟩
  exact derivedRestrict_map_eq_zero_of_comp_eq X.topIso.inv (⊤ : X.Opens).ι (𝟙 X)
    X.toIso_inv_ι e

end AlgebraicGeometry

end
