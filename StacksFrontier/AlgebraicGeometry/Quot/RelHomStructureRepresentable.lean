module

public import StacksFrontier.AlgebraicGeometry.Quot.RelHomStructurePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.RelHomStructureKernelScheme
public import StacksFrontier.AlgebraicGeometry.Quot.RelHomStructureUnitEnd

/-!
# Stacks 0DLC, part (3), step (L): the affine computation of `T ↦ Hom(L_T, 𝒪_T)`

Let `V` be an affine scheme of the big fppf site of `S` and `L` a pseudo-coherent object of
`D(𝒪_V)` (small étale site) with `H^i(L) = 0` for `i > 0`.  This file proves step (L) of the proof
of Stacks 0DLC, part (3), the proposition
`AlgebraicGeometry.Space.RelHomStructureRepresentableOfIsLE` of
`StacksFrontier/AlgebraicGeometry/Quot/NegativeExtLocusHomFibres.lean`: the functor
`T ↦ Hom_{D(𝒪_T)}(Lg^*L, Lg^*𝒪_V)` on the test schemes `g : T ⟶ V` is an algebraic space affine and
of finite presentation over `V`.  With it the case `W = Y` of part (3) follows from part (2),
Stacks 0DKY, Stacks 0DL9 and step (S) alone.

## The argument

* `L` has a degree-zero presentation `𝒪^n ⟶ 𝒪^m ⟶ L` against the objects with no cohomology below
  degree zero (`AlgebraicGeometry.Space.exists_isDegreeZeroPresentation`, Stacks 064U), and it
  survives every derived pullback, through `Lg^* ⊣ Rg_*` and the left t-exactness of `Rg_*`
  (`AlgebraicGeometry.Space.pull_presents_of_isDegreeZeroPresentation`).
* The endomorphisms of `Lg^*𝒪_V` are the regular functions on `T`
  (`AlgebraicGeometry.Space.testStructureEndEquiv`), the restriction maps of the relative Hom
  functor act on them by pullback of functions (`testStructureEndEquiv_relHomMap`), and the
  pullback of an endomorphism of `𝒪_V` is the pullback of its function
  (`testStructureEndEquiv_map`).  The comparison isomorphisms are never computed: they differ
  from the canonical ones by units, which act trivially by conjugation.
* So a morphism `Lg^*L ⟶ Lg^*𝒪_V` is a tuple in `Γ(T, 𝒪_T)^m` solving the linear equations of the
  relations (`AlgebraicGeometry.Space.presentationEquiv`), naturally in `T`, and these are the
  points over `V` of the kernel scheme of `AlgebraicGeometry.Space.exists_kernelScheme`.

## Main results

* `AlgebraicGeometry.Space.relHomStructureRepresentableOfIsLE`: step (L).
* `AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_sheafOfDescent`:
  **Stacks 0DLC, part (3), in the case `W = Y`**, from part (2), Stacks 0DKY, Stacks 0DL9 and
  step (S).

Nothing is registered.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 064U](https://stacks.math.columbia.edu/tag/064U)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


/-! ### Precomposition commutes with the restriction maps of a relative Hom functor -/

/-- Precomposition with the inverse image of a morphism commutes with the restriction maps of a
relative Hom functor. -/
theorem _root_.CategoryTheory.PullbackData.relHomMap_map_comp {A : Type*} [Category* A]
    {D : A → Type*} [∀ a, Category* (D a)] (P : PullbackData A D) {I : Type*} [Category* I]
    {π : I ⥤ A} {a₀ : A} (κ : PullbackData.ConeTo π a₀) {M' M N : D a₀} (φ : M' ⟶ M)
    {j i : I} (g : j ⟶ i) (β : P.relHomObj κ M N i) :
    P.relHomMap κ M' N g ((P.pull (κ.leg i)).map φ ≫ β) =
      (P.pull (κ.leg j)).map φ ≫ P.relHomMap κ M N g β := by
  simp only [PullbackData.relHomMap, Functor.conjHom, Functor.map_comp, ← Category.assoc]
  congr 2
  exact ((P.triangle (κ.w g)).hom.naturality φ).symm

/-- The restriction map of a relative Hom functor, written out. -/
theorem _root_.CategoryTheory.PullbackData.relHomMap_eq {A : Type*} [Category* A]
    {D : A → Type*} [∀ a, Category* (D a)] (P : PullbackData A D) {I : Type*} [Category* I]
    {π : I ⥤ A} {a₀ : A} (κ : PullbackData.ConeTo π a₀) (M N : D a₀) {j i : I} (g : j ⟶ i)
    (α : P.relHomObj κ M N i) :
    P.relHomMap κ M N g α =
      (P.triangle (κ.w g)).hom.app M ≫ (P.pull (π.map g)).map α ≫ (P.triangle (κ.w g)).inv.app N :=
  rfl

/-- A family of equivalences between the values of two functors to types, compatible with the
actions of the morphisms on elements, is a natural isomorphism. -/
def _root_.CategoryTheory.NatIso.ofEquivOfApply.{w'} {C : Type*} [Category* C] {F G : C ⥤ Type w'}
    (e : ∀ X, F.obj X ≃ G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y) (x : F.obj X), e Y (F.map f x) = G.map f (e X x)) : F ≅ G :=
  NatIso.ofComponents (fun X => (e X).toIso) fun f => by
    ext x
    exact h f x

/-! ### A degree-zero presentation survives derived pullback -/

section Presentation

variable {X Y : AlgebraicSpaces B S hS}

/-- The derived pullback along a morphism of algebraic spaces is additive, being left adjoint to
the additive derived direct image. -/
theorem smallEtaleDerivedPullbackData_pull_additive (f : X ⟶ Y) :
    ((smallEtaleDerivedPullbackData B S hS).pull f).Additive :=
  (smallEtaleDerivedPullPushAdjunction B S hS f).left_adjoint_additive

/-- **A degree-zero presentation of `L` presents `Lf^*L` against every object with no cohomology
below degree zero.**  Under `Lf^* ⊣ Rf_*` a morphism `Lf^*L ⟶ G` is a morphism `L ⟶ Rf_*G`, and
`Rf_*G` again has no cohomology below degree zero. -/
theorem pull_presents_of_isDegreeZeroPresentation (f : X ⟶ Y) {L : derivedModules B S hS Y}
    {m n : ℕ} {e : Fin m → (structureObject B S hS Y ⟶ L)}
    {c : Fin n → Fin m → (structureObject B S hS Y ⟶ structureObject B S hS Y)}
    (h : IsDegreeZeroPresentation B S hS L e c) (G : derivedModules B S hS X) (hG : G.IsGE 0) :
    Function.Injective (fun (β : ((smallEtaleDerivedPullbackData B S hS).pull f).obj L ⟶ G)
        (j : Fin m) => ((smallEtaleDerivedPullbackData B S hS).pull f).map (e j) ≫ β) ∧
    ∀ β' : Fin m →
        (((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y) ⟶ G),
      (∀ i, ∑ j, ((smallEtaleDerivedPullbackData B S hS).pull f).map (c i j) ≫ β' j = 0) →
        ∃ β : ((smallEtaleDerivedPullbackData B S hS).pull f).obj L ⟶ G,
          ∀ j, ((smallEtaleDerivedPullbackData B S hS).pull f).map (e j) ≫ β = β' j := by
  have := smallEtaleDerivedPullbackData_pull_additive (B := B) (S := S) (hS := hS) f
  let adj := smallEtaleDerivedPullPushAdjunction B S hS f
  have hG' := isGE_spaceDerivedPushforward_obj B S hS f G 0 hG
  obtain ⟨hinj, hsurj⟩ := h.2 _ hG'
  refine ⟨fun β₁ β₂ hβ => ?_, fun β' hβ' => ?_⟩
  · refine (adj.homEquiv _ _).injective (hinj (funext fun j => ?_))
    have := congrFun hβ j
    simp only at this ⊢
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left, this]
  · obtain ⟨γ, hγ⟩ := hsurj (fun j => adj.homEquiv _ _ (β' j)) fun i => by
      have := congrArg (adj.homAddEquiv _ _) (hβ' i)
      rw [map_sum, map_zero] at this
      simpa only [Adjunction.homAddEquiv_apply, adj.homEquiv_naturality_left] using this
    refine ⟨(adj.homEquiv _ _).symm γ, fun j => ?_⟩
    rw [← adj.homEquiv_naturality_left_symm, hγ, Equiv.symm_apply_apply]

end Presentation

/-! ### Endomorphisms of the pulled-back structure object -/

section PullStructureEnd

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The global regular functions of an algebraic space commute. -/
theorem structureRingSheaf_sections_mul_comm (X : AlgebraicSpaces B S hS)
    (a b : RingCat.sectionsSubring (structureRingSheaf B S hS X).obj) : a * b = b * a :=
  Subtype.ext (funext fun U =>
    mul_comm (G := ToType ((smallEtaleRingedSite B S hS X.1 X.2).O.obj.obj U)) (a.1 U) (b.1 U))

variable (B S hS) in
/-- **The endomorphisms of `Lf^*𝒪_Y` are the global regular functions of `X`**: conjugation by
`Lf^*𝒪_Y ≅ 𝒪_X` followed by `AlgebraicGeometry.Space.structureEndEquiv`. -/
def pullStructureEndEquiv (f : X ⟶ Y) :
    (((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y) ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y)) ≃
      RingCat.sectionsSubring (structureRingSheaf B S hS X).obj :=
  ((smallEtaleDerivedPullStructureIso B S hS f).homCongr
    (smallEtaleDerivedPullStructureIso B S hS f)).trans (structureEndEquiv B S hS X).symm

/-- `AlgebraicGeometry.Space.pullStructureEndEquiv`, read back as an endomorphism of `𝒪_X`. -/
theorem structureEndEquiv_pullStructureEndEquiv (f : X ⟶ Y)
    (β : ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y) ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y)) :
    structureEndEquiv B S hS X (pullStructureEndEquiv B S hS f β) =
      (smallEtaleDerivedPullStructureIso B S hS f).inv ≫ β ≫
        (smallEtaleDerivedPullStructureIso B S hS f).hom := by
  simp [pullStructureEndEquiv, Iso.homCongr_apply]

/-- The regular function of an endomorphism of `Lf^*𝒪_Y`, characterised. -/
theorem pullStructureEndEquiv_eq_iff (f : X ⟶ Y)
    (β : ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y) ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y))
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS X).obj) :
    pullStructureEndEquiv B S hS f β = a ↔
      (smallEtaleDerivedPullStructureIso B S hS f).inv ≫ β ≫
        (smallEtaleDerivedPullStructureIso B S hS f).hom = structureEndEquiv B S hS X a := by
  rw [← structureEndEquiv_pullStructureEndEquiv]
  exact (structureEndEquiv B S hS X).injective.eq_iff.symm

/-- `AlgebraicGeometry.Space.pullStructureEndEquiv` turns composition into multiplication. -/
theorem pullStructureEndEquiv_comp (f : X ⟶ Y)
    (β β' : ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y) ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y)) :
    pullStructureEndEquiv B S hS f (β ≫ β') =
      pullStructureEndEquiv B S hS f β * pullStructureEndEquiv B S hS f β' := by
  rw [pullStructureEndEquiv_eq_iff, structureEndEquiv_mul, structureEndEquiv_pullStructureEndEquiv,
    structureEndEquiv_pullStructureEndEquiv]
  simp

/-- `AlgebraicGeometry.Space.pullStructureEndEquiv` turns addition into addition. -/
theorem pullStructureEndEquiv_add (f : X ⟶ Y)
    (β β' : ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y) ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y)) :
    pullStructureEndEquiv B S hS f (β + β') =
      pullStructureEndEquiv B S hS f β + pullStructureEndEquiv B S hS f β' := by
  rw [pullStructureEndEquiv_eq_iff, structureEndEquiv_add, structureEndEquiv_pullStructureEndEquiv,
    structureEndEquiv_pullStructureEndEquiv]
  simp [Preadditive.comp_add, Preadditive.add_comp]

/-- `AlgebraicGeometry.Space.pullStructureEndEquiv` as an additive equivalence. -/
def pullStructureEndAddEquiv (f : X ⟶ Y) :
    (((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y) ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull f).obj (structureObject B S hS Y)) ≃+
      RingCat.sectionsSubring (structureRingSheaf B S hS X).obj :=
  AddEquiv.mk' (pullStructureEndEquiv B S hS f) (pullStructureEndEquiv_add f)

/-- **Stacks 0732, read on `Lf^*`.**  The derived pullback of the endomorphism of `𝒪_Y` given by a
global regular function `a` is, read through `Lf^*𝒪_Y ≅ 𝒪_X`, the image of `a` under the ring
map on global regular functions. -/
theorem pullStructureEndEquiv_map_structureEndEquiv (f : X ⟶ Y)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj) :
    pullStructureEndEquiv B S hS f
        (((smallEtaleDerivedPullbackData B S hS).pull f).map (structureEndEquiv B S hS Y a)) =
      globalSectionsRingHomSite B S hS f a :=
  (pullStructureEndEquiv_eq_iff f _ _).2
    (smallEtaleDerivedPullStructureIso_conj_pull_map_structureEndEquiv f a)

/-- **The endomorphisms of `Lk^*𝒪_Z` transform by the ring map on global regular functions.**
For a presented composite `g ≫ k = h`, conjugating the pullback along `g` of an endomorphism of
`Lk^*𝒪_Z` by the composition comparison gives the endomorphism of `Lh^*𝒪_Z` whose regular
function is the image along `g` of the regular function of the original one.  The comparison
isomorphisms involved never have to be computed: they differ from the canonical ones by a unit,
and units act trivially by conjugation, the ring of global regular functions being commutative. -/
theorem pullStructureEndEquiv_triangle {g : X ⟶ Y} {k : Y ⟶ Z} {h : X ⟶ Z} (hk : g ≫ k = h)
    (β : ((smallEtaleDerivedPullbackData B S hS).pull k).obj (structureObject B S hS Z) ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull k).obj (structureObject B S hS Z)) :
    pullStructureEndEquiv B S hS h
        (((smallEtaleDerivedPullbackData B S hS).triangle hk).hom.app _ ≫
          ((smallEtaleDerivedPullbackData B S hS).pull g).map β ≫
            ((smallEtaleDerivedPullbackData B S hS).triangle hk).inv.app _) =
      globalSectionsRingHomSite B S hS g (pullStructureEndEquiv B S hS k β) := by
  obtain ⟨s, hs⟩ : ∃ s, pullStructureEndEquiv B S hS k β = s := ⟨_, rfl⟩
  rw [hs]
  have hβ : β = (smallEtaleDerivedPullStructureIso B S hS k).hom ≫ structureEndEquiv B S hS Y s ≫
      (smallEtaleDerivedPullStructureIso B S hS k).inv := by
    rw [← hs, structureEndEquiv_pullStructureEndEquiv]
    simp
  subst hβ
  -- the comparison `𝒪_X ≅ 𝒪_X` assembled from the four comparison isomorphisms
  obtain ⟨ω, hω⟩ : ∃ ω : structureObject B S hS X ≅ structureObject B S hS X,
      ω = (smallEtaleDerivedPullStructureIso B S hS h).symm ≪≫
        ((smallEtaleDerivedPullbackData B S hS).triangle hk).app _ ≪≫
          ((smallEtaleDerivedPullbackData B S hS).pull g).mapIso
            (smallEtaleDerivedPullStructureIso B S hS k) ≪≫
            smallEtaleDerivedPullStructureIso B S hS g := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := (structureEndEquiv B S hS X).surjective ω.hom
  obtain ⟨w', hw'⟩ := (structureEndEquiv B S hS X).surjective ω.inv
  have hww : w * w' = 1 := (structureEndEquiv B S hS X).injective (by
    rw [structureEndEquiv_mul, hw, hw', structureEndEquiv_one, Iso.hom_inv_id])
  refine (pullStructureEndEquiv_eq_iff h _ _).2 ?_
  have key := smallEtaleDerivedPullStructureIso_conj_pull_map_structureEndEquiv g s
  obtain ⟨t, ht⟩ : ∃ t : RingCat.sectionsSubring (structureRingSheaf B S hS X).obj,
      globalSectionsRingHomSite B S hS g s = t := ⟨_, rfl⟩
  rw [ht] at key ⊢
  have e1 : structureEndEquiv B S hS X (w * (t * w')) =
      structureEndEquiv B S hS X w ≫ structureEndEquiv B S hS X t
          ≫ structureEndEquiv B S hS X w' := by
    rw [structureEndEquiv_mul, structureEndEquiv_mul]
  have e2 : w * (t * w') = t := by
    rw [structureRingSheaf_sections_mul_comm X w, mul_assoc,
      structureRingSheaf_sections_mul_comm X w', hww, mul_one]
  rw [← e2, e1, hw, hw', ← key, hω]
  simp [Functor.map_comp]

end PullStructureEnd

/-! ### The relative Hom functor into the structure object on the test schemes -/

section TestSchemes

variable {V : BigFppfOver B S hS}

/-- The structure morphism of a test scheme over a scheme `V` is the morphism of algebraic spaces
of the underlying morphism of schemes. -/
theorem schemeSpaceFunctor_map_testMap (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V)) :
    (schemeSpaceFunctor B S hS).map (testMap T) = T.hom :=
  ObjectProperty.hom_ext _ (by
    rw [schemeSpaceFunctor_map_hom]
    exact yoneda.map_preimage T.hom.hom)

/-- The value at a test scheme of the relative Hom functor of the derived pullback on the test
schemes over `V`. -/
abbrev testRelHomObj (V : BigFppfOver B S hS)
    (M N : derivedModules B S hS ((schemeSpaceFunctor B S hS).obj V))
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V)) : Type (u + 1) :=
  (smallEtaleDerivedPullbackData B S hS).relHomObj
    (schemesOverCone ((schemeSpaceFunctor B S hS).obj V)) M N T

/-- The global regular functions of an algebraic space equal to the algebraic space of a scheme
`T` are the regular functions on `T`.  The equation is carried as a hypothesis so that the two
spellings of the algebraic space of a test scheme — as the source of its structure morphism and as
the algebraic space of its underlying scheme — are never unified inside the ring structures. -/
def schemeGlobalSectionsEquivOfEq {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (hX : X = (schemeSpaceFunctor B S hS).obj T) :
    RingCat.sectionsSubring (structureRingSheaf B S hS X).obj ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := by
  subst hX
  exact schemeGlobalSectionsEquiv B S hS T

/-- `AlgebraicGeometry.Space.schemeGlobalSectionsEquivOfEq` at the trivial equation. -/
theorem schemeGlobalSectionsEquivOfEq_rfl (T : BigFppfOver B S hS) :
    schemeGlobalSectionsEquivOfEq (rfl : (schemeSpaceFunctor B S hS).obj T = _) =
      schemeGlobalSectionsEquiv B S hS T :=
  rfl

/-- `AlgebraicGeometry.Space.schemeGlobalSectionsEquivOfEq` carries the ring map on global
regular functions to pullback of regular functions. -/
theorem schemeGlobalSectionsEquivOfEq_naturality {X X' : AlgebraicSpaces B S hS}
    {T T' : BigFppfOver B S hS}
    (hX : X = (schemeSpaceFunctor B S hS).obj T) (hX' : X' = (schemeSpaceFunctor B S hS).obj T')
    (f : X' ⟶ X) (g : T' ⟶ T)
    (hf : f = eqToHom hX' ≫ (schemeSpaceFunctor B S hS).map g ≫ eqToHom hX.symm)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS X).obj) :
    schemeGlobalSectionsEquivOfEq hX' (globalSectionsRingHomSite B S hS f a) =
      ((BigFppfOver.toScheme B S hS).map g).appTop (schemeGlobalSectionsEquivOfEq hX a) := by
  subst hX hX'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst hf
  exact schemeGlobalSectionsEquiv_naturality g a

/-- The global regular functions of the algebraic space of a test scheme `T`, as the source of
its structure morphism, are the regular functions on `T`. -/
def testGlobalSectionsEquiv (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V)) :
    RingCat.sectionsSubring (structureRingSheaf B S hS
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) _ ⋙ schemeSpaceFunctor B S hS).obj
            T)).obj ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) :=
  schemeGlobalSectionsEquivOfEq rfl

/-- The ring map on global regular functions along a morphism of test schemes is pullback of
functions. -/
theorem testGlobalSectionsEquiv_naturality {T T' : SchemesOver ((schemeSpaceFunctor B S hS).obj V)}
    (g : T' ⟶ T)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) _ ⋙ schemeSpaceFunctor B S hS).obj
            T)).obj) :
    testGlobalSectionsEquiv T' (globalSectionsRingHomSite B S hS
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) _ ⋙ schemeSpaceFunctor B S hS).map g)
            a) =
      ((BigFppfOver.toScheme B S hS).map g.left).appTop (testGlobalSectionsEquiv T a) :=
  schemeGlobalSectionsEquivOfEq_naturality
    (X := (CostructuredArrow.proj (schemeSpaceFunctor B S hS) _ ⋙ schemeSpaceFunctor B S hS).obj T)
    (X' := (CostructuredArrow.proj (schemeSpaceFunctor B S hS) _ ⋙ schemeSpaceFunctor B S hS).obj
        T')
    (T := T.left) (T' := T'.left) rfl rfl
    ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) _ ⋙ schemeSpaceFunctor B S hS).map g)
        g.left
    (by rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl) a

/-- The ring map on global regular functions along the structure morphism of a test scheme is
pullback of functions along the underlying morphism of schemes. -/
theorem testGlobalSectionsEquiv_testMap (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V))
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS
        ((schemeSpaceFunctor B S hS).obj V)).obj) :
    testGlobalSectionsEquiv T (globalSectionsRingHomSite B S hS
        ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T) a) =
      ((BigFppfOver.toScheme B S hS).map (testMap T)).appTop
          (schemeGlobalSectionsEquiv B S hS V a) :=
  schemeGlobalSectionsEquivOfEq_naturality
    (X := (schemeSpaceFunctor B S hS).obj V)
    (X' := (CostructuredArrow.proj (schemeSpaceFunctor B S hS) _ ⋙ schemeSpaceFunctor B S hS).obj T)
    (T := V) (T' := T.left) rfl rfl
    ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T) (testMap T)
    (by rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id,
      schemeSpaceFunctor_map_testMap]; rfl) a

variable (V) in
/-- **The endomorphisms of the pulled-back structure object at a test scheme are the regular
functions on the test scheme**: `End(Lg^*𝒪_V) = Γ(T, 𝒪_T)` for a test scheme `g : T → V`. -/
def testStructureEndEquiv (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V)) :
    (testRelHomObj V (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))
      (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T) ≃
      Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) :=
  (pullStructureEndEquiv B S hS ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T)).trans
    (testGlobalSectionsEquiv T).toEquiv

/-- `AlgebraicGeometry.Space.testStructureEndEquiv` written out. -/
theorem testStructureEndEquiv_apply (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V))
    (β : testRelHomObj V (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))
      (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T) :
    testStructureEndEquiv V T β =
      testGlobalSectionsEquiv T (pullStructureEndEquiv B S hS
        ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T) β) :=
  rfl

/-- `AlgebraicGeometry.Space.testStructureEndEquiv` turns addition into addition. -/
theorem testStructureEndEquiv_add (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V))
    (β β' : testRelHomObj V (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))
      (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T) :
    testStructureEndEquiv V T (β + β') =
      testStructureEndEquiv V T β + testStructureEndEquiv V T β' := by
  simp only [testStructureEndEquiv_apply, pullStructureEndEquiv_add, map_add]

variable (V) in
/-- `AlgebraicGeometry.Space.testStructureEndEquiv` as an additive equivalence. -/
def testStructureEndAddEquiv (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V)) :
    (testRelHomObj V (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))
      (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T) ≃+
      Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) :=
  AddEquiv.mk' (testStructureEndEquiv V T) (testStructureEndEquiv_add T)

/-- `AlgebraicGeometry.Space.testStructureEndEquiv` turns composition into multiplication. -/
theorem testStructureEndEquiv_comp (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V))
    (β β' : testRelHomObj V (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))
      (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T) :
    testStructureEndEquiv V T (β ≫ β') =
      testStructureEndEquiv V T β * testStructureEndEquiv V T β' := by
  simp only [testStructureEndEquiv_apply, pullStructureEndEquiv_comp, map_mul]

/-- **The restriction maps of `T ↦ End(Lg^*𝒪_V)` are pullback of regular functions.** -/
theorem testStructureEndEquiv_relHomMap {T T' : SchemesOver ((schemeSpaceFunctor B S hS).obj V)}
    (g : T' ⟶ T)
    (β : testRelHomObj V (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))
      (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T) :
    testStructureEndEquiv V T'
        ((smallEtaleDerivedPullbackData B S hS).relHomMap
          (schemesOverCone ((schemeSpaceFunctor B S hS).obj V)) _ _ g β) =
      ((BigFppfOver.toScheme B S hS).map g.left).appTop (testStructureEndEquiv V T β) := by
  have h := pullStructureEndEquiv_triangle
    ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).w g) β
  rw [PullbackData.relHomMap_eq, testStructureEndEquiv_apply, testStructureEndEquiv_apply]
  exact (congrArg (testGlobalSectionsEquiv T') h).trans (testGlobalSectionsEquiv_naturality g _)

/-- **The pullback to a test scheme of an endomorphism of `𝒪_V`** is, as a regular function, the
pullback of the corresponding regular function on `V`. -/
theorem testStructureEndEquiv_map (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V))
    (c : structureObject B S hS ((schemeSpaceFunctor B S hS).obj V) ⟶
      structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) :
    testStructureEndEquiv V T (((smallEtaleDerivedPullbackData B S hS).pull
        ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T)).map c) =
      ((BigFppfOver.toScheme B S hS).map (testMap T)).appTop
        (schemeGlobalSectionsEquiv B S hS V ((structureEndEquiv B S hS _).symm c)) := by
  obtain ⟨a, rfl⟩ := (structureEndEquiv B S hS ((schemeSpaceFunctor B S hS).obj V)).surjective c
  rw [Equiv.symm_apply_apply, testStructureEndEquiv_apply,
    pullStructureEndEquiv_map_structureEndEquiv, testGlobalSectionsEquiv_testMap]

end TestSchemes

/-! ### The relative Hom functor out of a presented object -/

section Assembly

variable {V : BigFppfOver B S hS} {L : derivedModules B S hS ((schemeSpaceFunctor B S hS).obj V)}
  {m n : ℕ} {e : Fin m → (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V) ⟶ L)}
  {c : Fin n → Fin m → (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V) ⟶
    structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))}

variable (V) in
/-- The relations of a degree-zero presentation, read as a matrix of regular functions on `V`. -/
def presentationCoeff
    (c : Fin n → Fin m → (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V) ⟶
      structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))) :
    Fin n → Fin m → Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  fun i j => schemeGlobalSectionsEquiv B S hS V ((structureEndEquiv B S hS _).symm (c i j))

variable (e) in
/-- The regular functions on a test scheme `T` that a morphism `Lg^*L ⟶ Lg^*𝒪_V` determines:
its composites with the pullbacks of the generators `e_j : 𝒪_V ⟶ L`. -/
def presentationValues (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V))
    (β : testRelHomObj V L (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T) :
    Fin m → Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) :=
  fun j => testStructureEndEquiv V T (((smallEtaleDerivedPullbackData B S hS).pull
    ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T)).map (e j) ≫ β)

/-- The pullback of a sum of composites with the relations, as a regular function. -/
theorem testStructureEndEquiv_sum_map_comp (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V))
    (i : Fin n)
    (β' : Fin m → testRelHomObj V (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))
      (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T) :
    testStructureEndEquiv V T (∑ j, ((smallEtaleDerivedPullbackData B S hS).pull
        ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T)).map (c i j) ≫ β' j) =
      ∑ j, ((BigFppfOver.toScheme B S hS).map (testMap T)).appTop (presentationCoeff V c i j) *
        testStructureEndEquiv V T (β' j) := by
  refine (map_sum (testStructureEndAddEquiv V T) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  change testStructureEndEquiv V T _ = _
  rw [testStructureEndEquiv_comp, testStructureEndEquiv_map]
  rfl

/-- The tuple of regular functions of a morphism `Lg^*L ⟶ Lg^*𝒪_V` solves the linear equations
of the relations. -/
theorem presentationValues_rel (hpres : IsDegreeZeroPresentation B S hS L e c)
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V))
    (β : testRelHomObj V L (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T)
        (i : Fin n) :
    ∑ j, ((BigFppfOver.toScheme B S hS).map (testMap T)).appTop (presentationCoeff V c i j) *
      presentationValues e T β j = 0 := by
  have := smallEtaleDerivedPullbackData_pull_additive (B := B) (S := S) (hS := hS)
    ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T)
  change ∑ j, _ * testStructureEndEquiv V T (((smallEtaleDerivedPullbackData B S hS).pull
    ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T)).map (e j) ≫ β) = 0
  rw [← testStructureEndEquiv_sum_map_comp]
  have h0 : ∑ j, ((smallEtaleDerivedPullbackData B S hS).pull
        ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T)).map (c i j) ≫
          ((smallEtaleDerivedPullbackData B S hS).pull
            ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T)).map (e j) ≫ β = 0 := by
    simp_rw [← Category.assoc, ← Functor.map_comp, ← Preadditive.sum_comp, ← Functor.map_sum,
      hpres.1 i, Functor.map_zero, zero_comp]
  rw [h0]
  exact map_zero (testStructureEndAddEquiv V T)

variable (e c) in
/-- **The relative Hom functor out of a presented object, at a test scheme**: a morphism
`Lg^*L ⟶ Lg^*𝒪_V` is the tuple of regular functions of its composites with the generators, and
those tuples are exactly the solutions of the linear equations given by the relations. -/
def presentationEquiv (hpres : IsDegreeZeroPresentation B S hS L e c)
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V)) :
    testRelHomObj V L (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T ≃
      {x : Fin m → Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) //
        ∀ i, ∑ j, ((BigFppfOver.toScheme B S hS).map (testMap T)).appTop
          (presentationCoeff V c i j) * x j = 0} :=
  Equiv.ofBijective (fun β => ⟨presentationValues e T β, presentationValues_rel hpres T β⟩) (by
    have hG : (((smallEtaleDerivedPullbackData B S hS).pull
        ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T)).obj
          (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))).IsGE 0 :=
      DerivedCategory.TStructure.t.isGE_of_iso
        (smallEtaleDerivedPullStructureIso B S hS
          ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T)).symm 0
    obtain ⟨hinj, hsurj⟩ := pull_presents_of_isDegreeZeroPresentation
      (X := (CostructuredArrow.proj (schemeSpaceFunctor B S hS) _ ⋙ schemeSpaceFunctor B S hS).obj
          T) (Y := (schemeSpaceFunctor B S hS).obj V)
      ((schemesOverCone ((schemeSpaceFunctor B S hS).obj V)).leg T) hpres _ hG
    refine ⟨fun β₁ β₂ hβ => hinj (funext fun j => (testStructureEndEquiv V T).injective
      (congrFun (congrArg Subtype.val hβ) j)), fun x => ?_⟩
    obtain ⟨β, hβ⟩ := hsurj (fun j => (testStructureEndEquiv V T).symm (x.1 j)) fun i =>
      (testStructureEndEquiv V T).injective (by
        rw [testStructureEndEquiv_sum_map_comp]
        simp only [Equiv.apply_symm_apply]
        rw [x.2 i]
        exact (map_zero (testStructureEndAddEquiv V T)).symm)
    exact ⟨β, Subtype.ext (funext fun j => by
      change testStructureEndEquiv V T _ = _
      rw [hβ j, Equiv.apply_symm_apply])⟩)

/-- `AlgebraicGeometry.Space.presentationEquiv` written out. -/
theorem presentationEquiv_apply_coe (hpres : IsDegreeZeroPresentation B S hS L e c)
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V))
    (β : testRelHomObj V L (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T) :
    (presentationEquiv e c hpres T β).1 = presentationValues e T β :=
  rfl

/-- **The restriction maps of the relative Hom functor out of a presented object are pullback of
regular functions**, on the tuples of `AlgebraicGeometry.Space.presentationEquiv`. -/
theorem presentationValues_relHomMap {T T' : SchemesOver ((schemeSpaceFunctor B S hS).obj V)}
    (g : T' ⟶ T)
    (β : testRelHomObj V L (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) T) :
    presentationValues e T' ((smallEtaleDerivedPullbackData B S hS).relHomMap
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj V)) _ _ g β) =
      fun j => ((BigFppfOver.toScheme B S hS).map g.left).appTop (presentationValues e T β j) := by
  funext j
  change testStructureEndEquiv V T' (_ ≫ _) = _
  rw [← PullbackData.relHomMap_map_comp, testStructureEndEquiv_relHomMap]
  rfl

/-- The pointwise naturality behind `AlgebraicGeometry.Space.presentationPointsIso`. -/
theorem presentationEquiv_symm_naturality (hpres : IsDegreeZeroPresentation B S hS L e c)
    {H : AlgebraicSpaces B S hS} (p : H ⟶ (schemeSpaceFunctor B S hS).obj V)
    (φ : ∀ T : SchemesOver ((schemeSpaceFunctor B S hS).obj V),
      spacePointsOverObj p T ≃
        {x : Fin m → Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) //
          ∀ i, ∑ j, ((BigFppfOver.toScheme B S hS).map (testMap T)).appTop
            (presentationCoeff V c i j) * x j = 0})
    (hφ : ∀ {T T' : SchemesOver ((schemeSpaceFunctor B S hS).obj V)} (g : T' ⟶ T)
      (x : spacePointsOverObj p T),
      (φ T' ((spacePointsOver p).map g.op x)).1 =
        fun j => ((BigFppfOver.toScheme B S hS).map g.left).appTop ((φ T x).1 j))
    {T T' : SchemesOver ((schemeSpaceFunctor B S hS).obj V)} (g : T' ⟶ T)
        (x : spacePointsOverObj p T) :
    (presentationEquiv e c hpres T').symm (φ T' ((spacePointsOver p).map g.op x)) =
      (smallEtaleDerivedPullbackData B S hS).relHomMap
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj V)) _ _ g
        ((presentationEquiv e c hpres T).symm (φ T x)) := by
  apply (presentationEquiv e c hpres T').injective
  refine Subtype.ext ?_
  rw [Equiv.apply_symm_apply, presentationEquiv_apply_coe, presentationValues_relHomMap,
    ← presentationEquiv_apply_coe hpres T, Equiv.apply_symm_apply]
  exact hφ g x

variable (e c) in
/-- **The relative Hom functor out of a presented object is the functor of points of the kernel
scheme**, given the points of the kernel scheme as the solutions of the linear equations of the
relations, naturally in the test scheme. -/
def presentationPointsIso (hpres : IsDegreeZeroPresentation B S hS L e c)
    {H : AlgebraicSpaces B S hS} (p : H ⟶ (schemeSpaceFunctor B S hS).obj V)
    (φ : ∀ T : SchemesOver ((schemeSpaceFunctor B S hS).obj V),
      spacePointsOverObj p T ≃
        {x : Fin m → Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) //
          ∀ i, ∑ j, ((BigFppfOver.toScheme B S hS).map (testMap T)).appTop
            (presentationCoeff V c i j) * x j = 0})
    (hφ : ∀ {T T' : SchemesOver ((schemeSpaceFunctor B S hS).obj V)} (g : T' ⟶ T)
      (x : spacePointsOverObj p T),
      (φ T' ((spacePointsOver p).map g.op x)).1 =
        fun j => ((BigFppfOver.toScheme B S hS).map g.left).appTop ((φ T x).1 j)) :
    spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅
      (smallEtaleDerivedPullbackData B S hS).relHomFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS)
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj V)) L
        (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V)) :=
  NatIso.ofEquivOfApply (fun T =>
    ({ toFun := fun x => (presentationEquiv e c hpres T.unop).symm (φ T.unop x.down)
       invFun := fun y => ULift.up ((φ T.unop).symm (presentationEquiv e c hpres T.unop y))
       left_inv := fun x => by
         simp only [Equiv.apply_symm_apply]
         exact congrArg ULift.up ((φ T.unop).symm_apply_apply x.down)
       right_inv := fun y => (congrArg (presentationEquiv e c hpres T.unop).symm
         ((φ T.unop).apply_symm_apply _)).trans
           ((presentationEquiv e c hpres T.unop).symm_apply_apply y) } :
      (spacePointsOver p ⋙ uliftFunctor.{u + 1, u}).obj T ≃
          ((smallEtaleDerivedPullbackData B S hS).relHomFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS)
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj V)) L
        (structureObject B S hS ((schemeSpaceFunctor B S hS).obj V))).obj T)) fun g x =>
    (presentationEquiv_symm_naturality hpres p φ hφ g.unop x.down).trans
      (PullbackData.relHomFunctor_map _ _ _ _ _ g.unop _).symm

end Assembly

/-! ### Step (L) -/

/-- **Step (L) of the proof of Stacks 0DLC, part (3)**: over an affine scheme `V`, for a
pseudo-coherent `L` in `D(𝒪_V)` with `H^i(L) = 0` for `i > 0`, the functor `T ↦ Hom(L_T, 𝒪_T)` on
the test schemes over `V` is an algebraic space affine and of finite presentation over `V`.

`L` has a degree-zero presentation `𝒪^n ⟶ 𝒪^m ⟶ L` against the objects with no cohomology below
degree zero (`AlgebraicGeometry.Space.exists_isDegreeZeroPresentation`, Stacks 064U); it survives
every derived pullback (`AlgebraicGeometry.Space.pull_presents_of_isDegreeZeroPresentation`), so a
morphism `L_T ⟶ 𝒪_T` is a tuple of regular functions on `T` solving the linear equations of the
relations (`AlgebraicGeometry.Space.presentationEquiv`), naturally in `T`
(`AlgebraicGeometry.Space.presentationValues_relHomMap`); and those tuples are the points over `V`
of the closed subscheme of `𝐀^m_V` cut out by the equations
(`AlgebraicGeometry.Space.exists_kernelScheme`). -/
theorem relHomStructureRepresentableOfIsLE : RelHomStructureRepresentableOfIsLE B S hS := by
  intro V hV L hL hL0
  obtain ⟨m, n, e, c, hpres⟩ := exists_isDegreeZeroPresentation V hV L hL hL0
  obtain ⟨H, p, hp, hfp, φ, hφ⟩ := exists_kernelScheme V hV (presentationCoeff V c)
  exact ⟨H, p, hp, hfp, ⟨presentationPointsIso e c hpres p φ hφ⟩⟩

/-- **Stacks 0DLC, part (3), in the case `W = Y`**, from part (2) in the case `W = Y` (`h2`),
Stacks 0DKY (`h0DKY`), Stacks 0DL9 (`h0DL9`) and the internal step (S) (`hS'`): the corollary of
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_steps` in which step (L) is
discharged by `AlgebraicGeometry.Space.relHomStructureRepresentableOfIsLE`. -/
theorem relativeDerivedHomRepresentableOfFibres_of_sheafOfDescent
    (h2 : NegativeExtVanishesOfFibres B S hS)
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (h0DL9 : DerivedHomHypercoveringDescent B S hS)
    (hS' : RelativeDerivedHomIsSheafOfDescent B S hS) :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_steps h2 h0DKY h0DL9 hS'
    relHomStructureRepresentableOfIsLE

end AlgebraicGeometry.Space

end
