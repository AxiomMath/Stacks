module

public import StacksFrontier.CategoryTheory.Sites.Stackification.StageTwo

/-!
# The morphism presheaves of the second stage are sheaves

The second stage of the construction of the stackification of a fibred category proves a gluing
statement and a separatedness statement for the morphisms of `CategoryTheory.Functor.StageTwo`,
both phrased in the language of the construction: a family of morphisms indexed by the morphisms
of the total category lying over a covering sieve of the base
(`CategoryTheory.Functor.exists_amalgamation_stageTwoProj`), and equality of locally equal
morphisms (`CategoryTheory.Functor.locallyEqual_stageTwoProj_iff`). Condition (2) of Stacks 026F,
`CategoryTheory.Functor.IsMorSheaf`, is phrased instead as the sheaf condition for the presheaf
`Mor(x, y)` of Stacks 02ZB on `𝒮/U`. This file translates between the two.

The translation is `CategoryTheory.Functor.morSectionHom`: a section of `Mor(x, y)` over
`g : 𝒮/U` is a morphism `g^* x ⟶ g^* y` of the fibre over `g.left`, and following it with the
chosen cartesian lift of `g.hom` at `y` presents it as a morphism `g^* x ⟶ y` of the total
category lying over `g.hom`. This reading is bijective, and it turns the restriction maps of
`Mor(x, y)` into precomposition with `CategoryTheory.Functor.pullbackFiberMap`, which is the
operation the gluing statement of the second stage is about.

## Main results

* `CategoryTheory.Functor.isMorSheaf_of_locallyEqual_of_amalgamation`, the criterion: a fibred
  category whose locally equal morphisms are equal and whose morphisms glue along covering sieves
  has sheaf morphism presheaves;
* `CategoryTheory.Functor.isMorSheaf_stageTwoProj`, condition (2) of Stacks 026F for the second
  stage.

## Implementation notes

The domain of a test morphism `Φ : W ⟶ g^* x` of the total category projects to `g.left` only up
to the equality `(pullbackFiber r x g.hom).2`, whereas the sieve of the sheaf condition lives on
`g.left`; the comparison `eqToHom` between the two is carried explicitly throughout. For the same
reason the object of `𝒮/U` attached to `Φ` is `Over.mk` of the composite of its base with `g.hom`,
which is *equal* to, but not the same object as, the domain of a general member of the sieve; the
two are compared by an `Over.homMk (eqToHom _)` and the compatibility of the family.
-/

@[expose] public section

-- `Functor.Fiber` and its inclusion are Mathlib definitions that are not implicit-reducible;
-- the composites below cross from a fibre into the total category through them.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category Opposite

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {r : 𝒳 ⥤ 𝒮} [r.IsFibered] {J : GrothendieckTopology 𝒮} {U : 𝒮}

/-! ### Sections of `Mor(x, y)` read in the total category -/

/-- A section of the presheaf `Mor(x, y)` of Stacks 02ZB over `g : 𝒮/U`, read in `𝒳` as a morphism
`g^* x ⟶ y` lying over `g.hom`: follow it with the chosen cartesian lift of `g.hom` at `y`. -/
noncomputable def morSectionHom {x y : r.Fiber U} {g : Over U}
    (m : pullbackFiber r x g.hom ⟶ pullbackFiber r y g.hom) :
    (pullbackFiber r x g.hom).1 ⟶ y.1 :=
  Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap y.2 g.hom

/-- The morphism `CategoryTheory.Functor.morSectionHom m` lies over `g.hom`. -/
instance isHomLift_morSectionHom {x y : r.Fiber U} {g : Over U}
    (m : pullbackFiber r x g.hom ⟶ pullbackFiber r y g.hom) :
    r.IsHomLift g.hom (morSectionHom m) := by
  have h : r.IsHomLift (𝟙 g.left ≫ g.hom) (morSectionHom m) := by
    unfold morSectionHom
    infer_instance
  rwa [id_comp] at h

/-- Reading a section of `Mor(x, y)` in the total category loses no information. -/
lemma morSectionHom_injective {x y : r.Fiber U} {g : Over U} :
    Function.Injective (morSectionHom (r := r) (x := x) (y := y) (g := g)) := fun m n h ↦
  fiber_hom_ext_of_cartesian g.hom (IsPreFibered.pullbackMap y.2 g.hom)
    (IsPreFibered.pullbackMap.IsCartesian _ _) m n h

/-- Every morphism `g^* x ⟶ y` of `𝒳` lying over `g.hom` is a section of `Mor(x, y)` over `g`. -/
lemma exists_morSectionHom_eq {x y : r.Fiber U} {g : Over U}
    (n : (pullbackFiber r x g.hom).1 ⟶ y.1) [r.IsHomLift g.hom n] :
    ∃ m : pullbackFiber r x g.hom ⟶ pullbackFiber r y g.hom, morSectionHom m = n :=
  ⟨⟨IsCartesian.map r g.hom (IsPreFibered.pullbackMap y.2 g.hom) n, inferInstance⟩,
    IsCartesian.fac r g.hom (IsPreFibered.pullbackMap y.2 g.hom) n⟩

/-- The restriction maps of `Mor(x, y)` are, in the reading of
`CategoryTheory.Functor.morSectionHom`, precomposition with
`CategoryTheory.Functor.pullbackFiberMap`. -/
lemma morSectionHom_morRestrict {x y : r.Fiber U} {g₁ g₂ : Over U} (k : g₁ ⟶ g₂)
    (m : pullbackFiber r x g₂.hom ⟶ pullbackFiber r y g₂.hom) :
    morSectionHom (morRestrict r x y k m) = pullbackFiberMap r x k ≫ morSectionHom m :=
  morRestrict_fac r x y k m

/-- `CategoryTheory.Functor.morSectionHom_morRestrict` pins down the restriction map. -/
lemma eq_morRestrict_of_morSectionHom {x y : r.Fiber U} {g₁ g₂ : Over U} (k : g₁ ⟶ g₂)
    (m : pullbackFiber r x g₂.hom ⟶ pullbackFiber r y g₂.hom)
    (n : pullbackFiber r x g₁.hom ⟶ pullbackFiber r y g₁.hom)
    (h : morSectionHom n = pullbackFiberMap r x k ≫ morSectionHom m) :
    n = morRestrict r x y k m :=
  morRestrict_uniq r x y k m n h

/-- The restriction map of `Mor(x, y)`, as the action of the presheaf on a morphism of `𝒮/U`. -/
lemma morPresheaf_map_op_eq {x y : r.Fiber U} {g₁ g₂ : Over U} (k : g₁ ⟶ g₂)
    (m : pullbackFiber r x g₂.hom ⟶ pullbackFiber r y g₂.hom) :
    (morPresheaf r x y).map k.op m = morRestrict r x y k m := rfl

/-! ### Test morphisms and the members of the sieve they determine -/

section TestMorphisms

variable (x : r.Fiber U) {g : Over U}

/-- The object of `𝒮/U` attached to a morphism `Φ : W ⟶ g^* x` of `𝒳`: its base, composed with
`g.hom`. -/
noncomputable abbrev testBase {W : 𝒳} (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    r.obj W ⟶ g.left :=
  r.map Φ ≫ eqToHom (pullbackFiber r x g.hom).2

/-- A morphism `Φ : W ⟶ g^* x` of `𝒳` lies over `CategoryTheory.Functor.testBase x Φ`. -/
instance isHomLift_testBase {W : 𝒳} (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    r.IsHomLift (testBase x Φ) Φ :=
  IsHomLift.of_fac' r _ Φ rfl (pullbackFiber r x g.hom).2 (by simp)

/-- The member of a sieve on `g` attached to a morphism `Φ : W ⟶ g^* x` of `𝒳`. -/
noncomputable abbrev testArrow {W : 𝒳} (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    Over.mk (testBase x Φ ≫ g.hom) ⟶ g :=
  Over.homMk (testBase x Φ) rfl

/-- The factorisation of `Φ : W ⟶ g^* x`, followed by the chosen cartesian lift of `g.hom` at `x`,
through the chosen cartesian lift of the base of `Φ` composed with `g.hom`. -/
noncomputable def testFactor {W : 𝒳} (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    W ⟶ (pullbackFiber r x (testBase x Φ ≫ g.hom)).1 :=
  IsStronglyCartesian.map r (testBase x Φ ≫ g.hom)
    (IsPreFibered.pullbackMap x.2 (testBase x Φ ≫ g.hom)) (id_comp _).symm
    (Φ ≫ IsPreFibered.pullbackMap x.2 g.hom)

/-- The factorisation `CategoryTheory.Functor.testFactor x Φ` lies over an identity. -/
instance isHomLift_testFactor {W : 𝒳} (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    r.IsHomLift (𝟙 (r.obj W)) (testFactor x Φ) := by
  unfold testFactor
  infer_instance

/-- The factorisation `CategoryTheory.Functor.testFactor x Φ`, followed by the chosen cartesian
lift of the base of `Φ` composed with `g.hom`, is `Φ` followed by the chosen cartesian lift of
`g.hom` at `x`. -/
@[reassoc]
lemma testFactor_fac {W : 𝒳} (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    testFactor x Φ ≫ IsPreFibered.pullbackMap x.2 (testBase x Φ ≫ g.hom) =
      Φ ≫ IsPreFibered.pullbackMap x.2 g.hom :=
  IsStronglyCartesian.fac r (testBase x Φ ≫ g.hom)
    (IsPreFibered.pullbackMap x.2 (testBase x Φ ≫ g.hom)) (id_comp _).symm
    (Φ ≫ IsPreFibered.pullbackMap x.2 g.hom)

/-- A morphism of `𝒳` into `g^* x` factors through the chosen pullback of `x` along the member of
the sieve it determines. -/
lemma eq_testFactor_comp {W : 𝒳} (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    Φ = testFactor x Φ ≫ pullbackFiberMap r x (testArrow x Φ) := by
  have h : r.IsHomLift (testBase x Φ)
      (testFactor x Φ ≫ pullbackFiberMap r x (testArrow x Φ)) := by
    have h₀ : r.IsHomLift (𝟙 (r.obj W) ≫ (testArrow x Φ).left)
        (testFactor x Φ ≫ pullbackFiberMap r x (testArrow x Φ)) := inferInstance
    rwa [id_comp] at h₀
  refine IsStronglyCartesian.ext r g.hom (IsPreFibered.pullbackMap x.2 g.hom)
    (testBase x Φ) ?_
  rw [assoc, pullbackFiberMap_fac]
  exact (testFactor_fac x Φ).symm

/-! ### Comparison with a general member of the sieve

The object of `𝒮/U` attached to a test morphism is `Over.mk` of a composite, which is *equal* to,
but not the same object as, the domain of a general member of the sieve; the two are compared by
an `Over.homMk (eqToHom _)`. -/

/-- The base of the chosen restriction map along `k : Z ⟶ g` is `k.left`, up to the comparison of
`Z.left` with the projection of the chosen pullback of `x` along `Z.hom`. -/
lemma testBase_pullbackFiberMap {Z : Over U} (k : Z ⟶ g) :
    testBase x (pullbackFiberMap r x k) =
      eqToHom (pullbackFiber r x Z.hom).2 ≫ k.left := by
  unfold testBase
  rw [IsHomLift.fac' r k.left (pullbackFiberMap r x k)]
  simp

/-- The comparison of the object of `𝒮/U` attached to the chosen restriction map along
`k : Z ⟶ g` with `Z` itself. -/
noncomputable def testShift {Z : Over U} (k : Z ⟶ g) :
    Over.mk (testBase x (pullbackFiberMap r x k) ≫ g.hom) ⟶ Z :=
  Over.homMk (eqToHom (pullbackFiber r x Z.hom).2)
    (by
      simp only [Over.mk_hom]
      rw [testBase_pullbackFiberMap, assoc, Over.w k])

/-- The base of the comparison `CategoryTheory.Functor.testShift x k` is the comparison of the
projection of the chosen pullback of `x` along `Z.hom` with `Z.left`. -/
@[simp]
lemma testShift_left {Z : Over U} (k : Z ⟶ g) :
    (testShift x k).left = eqToHom (pullbackFiber r x Z.hom).2 := rfl

/-- The comparison composed with `k` is the member of the sieve attached to the chosen restriction
map along `k`. -/
lemma testShift_comp {Z : Over U} (k : Z ⟶ g) :
    testShift x k ≫ k = testArrow x (pullbackFiberMap r x k) := by
  ext
  simp only [Over.comp_left, testShift_left, testArrow, Over.homMk_left]
  exact (testBase_pullbackFiberMap x k).symm

/-- The chosen restriction map along `k` factors through the pullback along the member of the
sieve it determines by an isomorphism which the comparison inverts: the factorisation composed
with the comparison is the identity. -/
lemma testFactor_comp_pullbackFiberMap_testShift {Z : Over U} (k : Z ⟶ g) :
    testFactor x (pullbackFiberMap r x k) ≫ pullbackFiberMap r x (testShift x k) =
      𝟙 (pullbackFiber r x Z.hom).1 := by
  have hW : r.obj (pullbackFiber r x Z.hom).1 = Z.left := (pullbackFiber r x Z.hom).2
  have h1 : r.IsHomLift (𝟙 Z.left) (𝟙 (pullbackFiber r x Z.hom).1) := IsHomLift.id hW
  have h2 : r.IsHomLift (𝟙 Z.left)
      (testFactor x (pullbackFiberMap r x k) ≫ pullbackFiberMap r x (testShift x k)) := by
    refine IsHomLift.of_fac' r (𝟙 Z.left) _ hW hW ?_
    rw [IsHomLift.fac' r (𝟙 (r.obj (pullbackFiber r x Z.hom).1) ≫ (testShift x k).left)
      (testFactor x (pullbackFiberMap r x k) ≫ pullbackFiberMap r x (testShift x k))]
    simp
  refine IsStronglyCartesian.ext r Z.hom (IsPreFibered.pullbackMap x.2 Z.hom) (𝟙 Z.left) ?_
  rw [assoc, pullbackFiberMap_fac, id_comp]
  exact (testFactor_fac x (pullbackFiberMap r x k)).trans (pullbackFiberMap_fac r x k)

/-- The comparison of the objects of `𝒮/U` attached to `Ψ ≫ Φ` and to `Φ`. -/
noncomputable def testPre {W W' : 𝒳} (Ψ : W' ⟶ W) (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    Over.mk (testBase x (Ψ ≫ Φ) ≫ g.hom) ⟶ Over.mk (testBase x Φ ≫ g.hom) :=
  Over.homMk (r.map Ψ) (by simp [testBase])

/-- The base of the comparison `CategoryTheory.Functor.testPre x Ψ Φ` is `r.map Ψ`. -/
@[simp]
lemma testPre_left {W W' : 𝒳} (Ψ : W' ⟶ W) (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    (testPre x Ψ Φ).left = r.map Ψ := rfl

/-- The comparison carries the member of the sieve attached to `Φ` to the one attached to
`Ψ ≫ Φ`. -/
lemma testPre_comp {W W' : 𝒳} (Ψ : W' ⟶ W) (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    testPre x Ψ Φ ≫ testArrow x Φ = testArrow x (Ψ ≫ Φ) := by
  ext
  simp [testArrow, testBase]

/-- The factorisations of `Ψ ≫ Φ` and of `Φ` are compatible with the comparison. -/
lemma testFactor_comp_pullbackFiberMap_testPre {W W' : 𝒳} (Ψ : W' ⟶ W)
    (Φ : W ⟶ (pullbackFiber r x g.hom).1) :
    testFactor x (Ψ ≫ Φ) ≫ pullbackFiberMap r x (testPre x Ψ Φ) = Ψ ≫ testFactor x Φ := by
  have h1 : r.IsHomLift (r.map Ψ)
      (testFactor x (Ψ ≫ Φ) ≫ pullbackFiberMap r x (testPre x Ψ Φ)) := by
    have h₀ : r.IsHomLift (𝟙 (r.obj W') ≫ (testPre x Ψ Φ).left)
        (testFactor x (Ψ ≫ Φ) ≫ pullbackFiberMap r x (testPre x Ψ Φ)) := inferInstance
    rwa [id_comp, testPre_left] at h₀
  have h2 : r.IsHomLift (r.map Ψ) (Ψ ≫ testFactor x Φ) := by
    have h₀ : r.IsHomLift (r.map Ψ ≫ 𝟙 (r.obj W)) (Ψ ≫ testFactor x Φ) := inferInstance
    rwa [comp_id] at h₀
  refine IsStronglyCartesian.ext r (testBase x Φ ≫ g.hom)
    (IsPreFibered.pullbackMap x.2 (testBase x Φ ≫ g.hom)) (r.map Ψ) ?_
  calc (testFactor x (Ψ ≫ Φ) ≫ pullbackFiberMap r x (testPre x Ψ Φ)) ≫
        IsPreFibered.pullbackMap x.2 (testBase x Φ ≫ g.hom)
      = testFactor x (Ψ ≫ Φ) ≫ pullbackFiberMap r x (testPre x Ψ Φ) ≫
          IsPreFibered.pullbackMap x.2 (Over.mk (testBase x Φ ≫ g.hom)).hom := assoc _ _ _
    _ = testFactor x (Ψ ≫ Φ) ≫
          IsPreFibered.pullbackMap x.2 (Over.mk (testBase x (Ψ ≫ Φ) ≫ g.hom)).hom := by
        rw [pullbackFiberMap_fac]
    _ = (Ψ ≫ Φ) ≫ IsPreFibered.pullbackMap x.2 g.hom := testFactor_fac x (Ψ ≫ Φ)
    _ = Ψ ≫ Φ ≫ IsPreFibered.pullbackMap x.2 g.hom := assoc _ _ _
    _ = Ψ ≫ testFactor x Φ ≫ IsPreFibered.pullbackMap x.2 (testBase x Φ ≫ g.hom) := by
        rw [testFactor_fac]
    _ = (Ψ ≫ testFactor x Φ) ≫ IsPreFibered.pullbackMap x.2 (testBase x Φ ≫ g.hom) :=
        (assoc _ _ _).symm

end TestMorphisms

/-! ### The criterion -/

/-- **The separatedness half of condition (2) of Stacks 026F**, from separatedness of the
morphisms of the total category. -/
theorem isSeparatedFor_morPresheaf
    (hsep : ∀ {A B : 𝒳} {F G : A ⟶ B}, r.LocallyEqual J F G → F = G)
    {x y : r.Fiber U} {g : Over U} {R : Sieve g.left} (hR : R ∈ J g.left) :
    Presieve.IsSeparatedFor (morPresheaf r x y)
      (((Sieve.overEquiv g).symm R : Sieve g) : Presieve g) := by
  have hX : r.obj (pullbackFiber r x g.hom).1 = g.left := (pullbackFiber r x g.hom).2
  intro fam t₁ t₂ h₁ h₂
  refine morSectionHom_injective
    (hsep ⟨?_, R.pullback (eqToHom hX), J.pullback_stable _ hR, ?_⟩)
  · rw [IsHomLift.fac' r g.hom (morSectionHom t₁), IsHomLift.fac' r g.hom (morSectionHom t₂)]
  · intro W Φ hΦ
    have hmem : (((Sieve.overEquiv g).symm R : Sieve g) : Presieve g) (testArrow x Φ) := hΦ
    have hsec : pullbackFiberMap r x (testArrow x Φ) ≫ morSectionHom t₁ =
        pullbackFiberMap r x (testArrow x Φ) ≫ morSectionHom t₂ := by
      rw [← morSectionHom_morRestrict, ← morSectionHom_morRestrict]
      exact congrArg morSectionHom ((h₁ _ hmem).trans (h₂ _ hmem).symm)
    rw [eq_testFactor_comp x Φ]
    simp only [assoc, hsec]

/-- **The gluing half of condition (2) of Stacks 026F**, from gluing of the morphisms of the total
category. -/
theorem exists_isAmalgamation_morPresheaf
    (hglue : ∀ {A B : 𝒳} (u : r.obj A ⟶ r.obj B) {S : Sieve (r.obj A)}, S ∈ J (r.obj A) →
      ∀ (F : ∀ {W : 𝒳} (Φ : W ⟶ A), S.arrows (r.map Φ) → (W ⟶ B)),
        (∀ {W : 𝒳} (Φ : W ⟶ A) (hΦ : S.arrows (r.map Φ)), r.map (F Φ hΦ) = r.map Φ ≫ u) →
        (∀ {W W' : 𝒳} (Ψ : W' ⟶ W) (Φ : W ⟶ A) (hΦ : S.arrows (r.map Φ))
          (hΨΦ : S.arrows (r.map (Ψ ≫ Φ))), F (Ψ ≫ Φ) hΨΦ = Ψ ≫ F Φ hΦ) →
        ∃ G : A ⟶ B, r.map G = u ∧
          ∀ {W : 𝒳} (Φ : W ⟶ A) (hΦ : S.arrows (r.map Φ)), Φ ≫ G = F Φ hΦ)
    {x y : r.Fiber U} {g : Over U} {R : Sieve g.left} (hR : R ∈ J g.left)
    (fam : Presieve.FamilyOfElements (morPresheaf r x y)
      (((Sieve.overEquiv g).symm R : Sieve g) : Presieve g))
    (hfam : fam.Compatible) :
    ∃ t, fam.IsAmalgamation t := by
  have hX : r.obj (pullbackFiber r x g.hom).1 = g.left := (pullbackFiber r x g.hom).2
  have hsieve : R.pullback (eqToHom hX) ∈ J (r.obj (pullbackFiber r x g.hom).1) :=
    J.pullback_stable _ hR
  have hmem : ∀ {W : 𝒳} (Φ : W ⟶ (pullbackFiber r x g.hom).1),
      (R.pullback (eqToHom hX)).arrows (r.map Φ) →
      (((Sieve.overEquiv g).symm R : Sieve g) : Presieve g) (testArrow x Φ) := fun _ hΦ ↦ hΦ
  obtain ⟨G, hGbase, hG⟩ := hglue (A := (pullbackFiber r x g.hom).1) (B := y.1)
    (eqToHom hX ≫ g.hom ≫ eqToHom y.2.symm) hsieve
    (fun Φ hΦ ↦ testFactor x Φ ≫ morSectionHom (fam (testArrow x Φ) (hmem Φ hΦ)))
    (by
      intro W Φ hΦ
      rw [r.map_comp, IsHomLift.fac' r (𝟙 (r.obj W)) (testFactor x Φ),
        IsHomLift.fac' r (Over.mk (testBase x Φ ≫ g.hom)).hom
          (morSectionHom (fam (testArrow x Φ) (hmem Φ hΦ)))]
      simp [testBase])
    (by
      intro W W' Ψ Φ hΦ hΨΦ
      have hcomp : morRestrict r x y (testPre x Ψ Φ) (fam (testArrow x Φ) (hmem Φ hΦ)) =
          fam (testArrow x (Ψ ≫ Φ)) (hmem (Ψ ≫ Φ) hΨΦ) := by
        have h := hfam (testPre x Ψ Φ) (𝟙 _) (hmem Φ hΦ) (hmem (Ψ ≫ Φ) hΨΦ)
          (by rw [testPre_comp, id_comp])
        rwa [morPresheaf_map_op_eq, morPresheaf_map_op_eq, morRestrict_id] at h
      rw [← hcomp, morSectionHom_morRestrict, ← assoc,
        testFactor_comp_pullbackFiberMap_testPre, assoc])
  have hGlift : r.IsHomLift g.hom G := IsHomLift.of_fac' r g.hom G hX y.2 hGbase
  obtain ⟨t, ht⟩ := exists_morSectionHom_eq (x := x) (y := y) (g := g) G
  refine ⟨t, fun Z k hk ↦ ?_⟩
  refine (eq_morRestrict_of_morSectionHom k t (fam k hk) ?_).symm
  have hΦmem : (R.pullback (eqToHom hX)).arrows (r.map (pullbackFiberMap r x k)) := by
    show R.arrows (testBase x (pullbackFiberMap r x k))
    rw [testBase_pullbackFiberMap]
    exact R.downward_closed (show R.arrows k.left from hk)
      (eqToHom (pullbackFiber r x Z.hom).2)
  have hshift : morRestrict r x y (testShift x k) (fam k hk) =
      fam (testArrow x (pullbackFiberMap r x k)) (hmem _ hΦmem) := by
    have h := hfam (testShift x k) (𝟙 _) hk (hmem _ hΦmem) (by rw [testShift_comp, id_comp])
    rwa [morPresheaf_map_op_eq, morPresheaf_map_op_eq, morRestrict_id] at h
  have hkey : pullbackFiberMap r x k ≫ G =
      testFactor x (pullbackFiberMap r x k) ≫
        morSectionHom (fam (testArrow x (pullbackFiberMap r x k)) (hmem _ hΦmem)) :=
    hG (pullbackFiberMap r x k) hΦmem
  rw [← hshift, morSectionHom_morRestrict, ← assoc,
    testFactor_comp_pullbackFiberMap_testShift, id_comp] at hkey
  rw [ht, hkey]

/-- **Condition (2) of Stacks 026F from the two halves proved in the language of the
stackification construction**: if the locally equal morphisms of `𝒳` are equal, and if morphisms
into an object of `𝒳` given compatibly over a covering sieve of its base glue, then the morphism
presheaves of `𝒳` are sheaves. -/
theorem isMorSheaf_of_locallyEqual_of_amalgamation
    (hsep : ∀ {A B : 𝒳} {F G : A ⟶ B}, r.LocallyEqual J F G → F = G)
    (hglue : ∀ {A B : 𝒳} (u : r.obj A ⟶ r.obj B) {S : Sieve (r.obj A)}, S ∈ J (r.obj A) →
      ∀ (F : ∀ {W : 𝒳} (Φ : W ⟶ A), S.arrows (r.map Φ) → (W ⟶ B)),
        (∀ {W : 𝒳} (Φ : W ⟶ A) (hΦ : S.arrows (r.map Φ)), r.map (F Φ hΦ) = r.map Φ ≫ u) →
        (∀ {W W' : 𝒳} (Ψ : W' ⟶ W) (Φ : W ⟶ A) (hΦ : S.arrows (r.map Φ))
          (hΨΦ : S.arrows (r.map (Ψ ≫ Φ))), F (Ψ ≫ Φ) hΨΦ = Ψ ≫ F Φ hΦ) →
        ∃ G : A ⟶ B, r.map G = u ∧
          ∀ {W : 𝒳} (Φ : W ⟶ A) (hΦ : S.arrows (r.map Φ)), Φ ≫ G = F Φ hΦ)
    (U : 𝒮) (x y : r.Fiber U) : IsMorSheaf r J U x y := by
  refine (isSheaf_iff_isSheaf_of_type (J.over U) (morPresheaf r x y)).2 ?_
  intro g S hS
  obtain ⟨R, rfl⟩ := (Sieve.overEquiv g).symm.surjective S
  have hR : R ∈ J g.left := by simpa using (J.mem_over_iff _).1 hS
  exact Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.1
    ⟨isSeparatedFor_morPresheaf hsep hR,
      fun fam hfam ↦ exists_isAmalgamation_morPresheaf hglue hR fam hfam⟩

/-! ### Condition (2) of Stacks 026F for the second stage -/

/-- **The morphism presheaves of the second stage of the stackification are sheaves**, that is,
condition (2) of Stacks 026F holds for `CategoryTheory.Functor.stageTwoProj`. This is the
translation of `CategoryTheory.Functor.locallyEqual_stageTwoProj_iff` and
`CategoryTheory.Functor.exists_amalgamation_stageTwoProj` into the language of presheaves on
`𝒮/U`. -/
theorem isMorSheaf_stageTwoProj (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮) (U : 𝒮)
    (x y : (p.stageTwoProj J).Fiber U) : IsMorSheaf (p.stageTwoProj J) J U x y :=
  isMorSheaf_of_locallyEqual_of_amalgamation
    (fun h ↦ (locallyEqual_stageTwoProj_iff _ _).mp h)
    (by
      intro A B u S hS F hFbase hFcomp
      exact exists_amalgamation_stageTwoProj u hS F hFbase hFcomp) U x y

end CategoryTheory.Functor
