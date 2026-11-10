module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseProper
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingAlgebra
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommuting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingProjectionFormula.ProjectionFormula

/-!
# The associativity of Stacks 0B75 at the pairings of Stacks 0FA0

The three instances of the associativity of the composition of bivariant classes (Stacks 0B75),
one per term type of a triple product of Stacks 0FA0, read through the transports the pairings
carry; the third input, `res(c) = f^*(f_*(c))`
(`Stacks.Chow.chowCohomologyRestriction_localizedGradingPushforward`); and the bookkeeping the
associativity proof uses: the pairings over a finite sum, the uniform form of a term of the
localized branch, the reindexing `Stacks.Chow.sum_Icc_diag_flip` of a double convolution, and
transport in an argument of a pairing.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The associativity of Stacks 0B75 at the first pairing -/

section Associativity

/-- The cap operation at the base change of an isomorphism of test schemes, read through two
pushforwards along isomorphisms that agree. -/
private theorem pushforward_cap_comp_heq {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y T₁ T₂ B A : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] {w : X ⟶ Y} [LocallyOfFiniteType w] {hw : w ≫ sY = sX} {p : ℤ}
    (x : BivariantClass C G sX sY w hw p) {g₁ : T₁ ⟶ Y} [LocallyOfFiniteType g₁] {u : T₂ ⟶ T₁}
    [IsIso u] {g₂ : T₂ ⟶ Y} [LocallyOfFiniteType g₂] (hg : u ≫ g₁ = g₂) {sB : B ⟶ C.S}
    [LocallyOfFiniteType sB] {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {vi : pullback w g₂ ⟶ B}
    [IsIso vi] {vo : B ⟶ A} [IsIso vo] {vo' : pullback w g₁ ⟶ A} [IsIso vo']
    {hi : vi ≫ sB = pullback.fst w g₂ ≫ sX} {ho : vo ≫ sA = sB}
    {ho' : vo' ≫ sA = pullback.fst w g₁ ≫ sX} (hu : u ≫ (g₁ ≫ sY) = g₂ ≫ sY)
    (hv : vi ≫ vo = (testBaseChangeIso w g₁ u g₂ hg).hom ≫ vo') {d n₁ n₂ : ℤ}
    (h₁ : d - p = n₁) (h₂ : d = n₂) (γ : chowGroup C (g₂ ≫ sY) d) :
    chowPushforwardOfIso C sB sA vo ho n₁ (chowGroupDegreeEquiv C sB h₁
        (chowPushforwardOfIso C (pullback.fst w g₂ ≫ sX) sB vi hi (d - p) (x.cap g₂ d γ))) ≍
      chowPushforwardOfIso C (pullback.fst w g₁ ≫ sX) sA vo' ho' (n₂ - p)
        (x.cap g₁ n₂ (chowGroupDegreeEquiv C (g₁ ≫ sY) h₂
          (chowPushforwardOfIso C (g₂ ≫ sY) (g₁ ≫ sY) u hu d γ))) := by
  subst h₁ h₂
  refine heq_of_eq ?_
  have key := x.cap_chowPushforwardOfIso g₁ u g₂ hg (g₂ ≫ sY) rfl d hu γ γ rfl
  refine Eq.trans ?_ (congrArg _ key.symm)
  exact (chowPushforwardOfIso_comp_apply C _ _ _ _ _ _ _ _ _).trans
    ((chowPushforwardOfIso_congr_apply C _ _ _ _ hv _ _ _ _).trans
      (chowPushforwardOfIso_comp_apply C _ _ _ _ _ _ _ _ _).symm)

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The identification `X ×_X (X ×_X T) ≅ X ×_X T` carries the test morphism of the inner cap
product to the test morphism of the outer one. -/
theorem ambientCompositeIso_fst {T : Scheme.{u}} (t : T ⟶ X) :
    ((pullbackRightPullbackFstIso (𝟙 X) t (𝟙 X)).hom ≫
          (pullback.congrHom (Category.comp_id (𝟙 X)) (rfl : t = t)).hom) ≫
        pullback.fst (𝟙 X) t =
      pullback.fst (𝟙 X) (pullback.fst (𝟙 X) t) := by
  rw [Category.assoc]
  simp

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The identification `X ×_X (X ×_X T) ≅ X ×_X T` that the multiplication of `A^*(X)` pushes a cap
product forward along is the projection of the second identity base change. -/
theorem identityBaseChange_snd_eq_ambientCompositeIso {T : Scheme.{u}} (t : T ⟶ X) :
    pullback.snd (𝟙 X) (pullback.fst (𝟙 X) t) =
      (pullbackRightPullbackFstIso (𝟙 X) t (𝟙 X)).hom ≫
        (pullback.congrHom (Category.comp_id (𝟙 X)) (rfl : t = t)).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [ambientCompositeIso_fst t]
    simpa using (pullback.condition (f := 𝟙 X) (g := pullback.fst (𝟙 X) t)).symm
  · simp

/-- **The associativity of Stacks 0B75 at the first pairing of Stacks 0FA0:**
`(c ∘ b) ∘ b' = c ∘ (b · b')` for a localized class `c` and classes `b`, `b'` on `X`, the product
`b · b'` being the multiplication `Stacks.Chow.chowCohomologyComposite` of `A^*(X)`. It is a
heterogeneous equality only because the two sides are indexed by `(i + j) + l` and `i + (j + l)`,
the same integer written two ways, exactly as `Stacks.Chow.bivariantComposite_assoc` is.

This is the first of the three instances of the associativity of Stacks 0B75 that an associativity
proof for the multiplication of Stacks 0FA0 needs; see the implementation notes. Both sides cap by
capping with `b'`, then with `b`, then with `c`, pushed forward along the pasting of the three
squares, and the two pastings agree. -/
theorem localizedMulBivariantChow_localizedMulBivariantChow_heq (i j l : ℤ)
    (x : BivariantClass C G (f ≫ sX) sX f rfl i) (u : chowCohomologyComponent C G sX j)
    (v : chowCohomologyComponent C G sX l) :
    localizedMulBivariantChow C G sX f hgys hgysc (i + j) l
        (localizedMulBivariantChow C G sX f hgys hgysc i j x u) v ≍
      localizedMulBivariantChow C G sX f hgys hgysc i (j + l) x
        (chowCohomologyComposite C G sX hgys hgysc j l u v) := by
  refine BivariantClass.heq_of_cap_heq C G (f ≫ sX) sX f rfl (add_assoc i j l) _ _ ?_
  intro T t ht k α
  rw [localizedMulBivariantChow_cap C G sX f hgys hgysc (i + j) l _ v t k α,
    localizedMulBivariantChow_cap C G sX f hgys hgysc i j x u (pullback.fst (𝟙 X) t) (k - l) _,
    localizedMulBivariantChow_cap C G sX f hgys hgysc i (j + l) x _ t k α,
    chowCohomologyComposite_cap C G sX hgys hgysc j l u v t k α]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ((pushforward_cap_comp_heq x
    (ambientCompositeIso_fst t) (ambientCompositeIso_base C sX t) ?_ (by ring) (by ring) _).trans
    (chowGroupDegreeEquiv_heq C _ _ _).symm)
  refine congrArg (· ≫ _) (pullback.hom_ext ?_ ?_) <;>
    simp [identityBaseChange_snd_eq_ambientCompositeIso]

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The identification `Z ×_X (X ×_X T) ≅ Z ×_X T` carries the test morphism of the inner cap
product to the test morphism of the outer one. -/
theorem localizedMulBivariantChowIso_fst {T : Scheme.{u}} (t : T ⟶ X) :
    ((pullbackRightPullbackFstIso (𝟙 X) t f).hom ≫
          (pullback.congrHom (Category.comp_id f) (rfl : t = t)).hom) ≫ pullback.fst f t =
      pullback.fst f (pullback.fst (𝟙 X) t) := by
  rw [Category.assoc]
  simp

/-- **The associativity of Stacks 0B75 at the second pairing of Stacks 0FA0:**
`(α ∘ c) ∘ b = α ∘ (c ∘ b)` for a class `α` on `Z`, a localized class `c` and a class `b` on `X`.
Applied to `α = res(b')` for the restriction `res : A^*(X) ⟶ A^*(Z)` of Stacks 0F9Z, this is the
identity `T₂(b', c) ∘ b = T₂(b', c ∘ b)` for the second pairing, which is the second of the three
instances of the associativity of Stacks 0B75 that an associativity proof for the multiplication
of Stacks 0FA0 needs; see the implementation notes.

It is a heterogeneous equality only because the two sides are indexed by `(i + j) + l` and
`i + (j + l)`, the same integer written two ways. -/
theorem localizedMulBivariantChow_localizedComposeChowCohomology_heq (i j l : ℤ)
    (a : chowCohomologyComponent C G (f ≫ sX) i)
    (y : BivariantClass C G (f ≫ sX) sX f rfl j) (v : chowCohomologyComponent C G sX l) :
    localizedMulBivariantChow C G sX f hgys hgysc (i + j) l
        (localizedComposeChowCohomology C G sX f hgys hgysc i j a y) v ≍
      localizedComposeChowCohomology C G sX f hgys hgysc i (j + l) a
        (localizedMulBivariantChow C G sX f hgys hgysc j l y v) := by
  refine BivariantClass.heq_of_cap_heq C G (f ≫ sX) sX f rfl (add_assoc i j l) _ _ ?_
  intro T t ht k α
  rw [localizedMulBivariantChow_cap C G sX f hgys hgysc (i + j) l _ v t k α,
    localizedComposeChowCohomology_cap C G sX f hgys hgysc i j a y (pullback.fst (𝟙 X) t)
      (k - l) _,
    localizedComposeChowCohomology_cap C G sX f hgys hgysc i (j + l) a _ t k α,
    localizedMulBivariantChow_cap C G sX f hgys hgysc j l y v t k α]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ((pushforward_cap_comp_heq a
    (localizedMulBivariantChowIso_fst f t) (localizedMulBivariantChowIso_base C sX f t) ?_
    (by ring) (by ring) _).trans (chowGroupDegreeEquiv_heq C _ _ _).symm)
  refine pullback.hom_ext ?_ ?_ <;> simp

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The identification `Z ×_Z (Z ×_X T) ≅ Z ×_X T` carries the test morphism of the inner cap
product to the test morphism of the outer one. -/
theorem localizedComposeIso_fst {T : Scheme.{u}} (t : T ⟶ X) :
    ((pullbackRightPullbackFstIso f t (𝟙 Z)).hom ≫
          (pullback.congrHom (Category.id_comp f) (rfl : t = t)).hom) ≫ pullback.fst f t =
      pullback.fst (𝟙 Z) (pullback.fst f t) := by
  rw [Category.assoc]
  simp

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The identification `Z ×_Z (Z ×_X T) ≅ Z ×_X T` that the composition
`Aⁱ(Z) × Aʲ(Z ⟶ X) ⟶ Aⁱ⁺ʲ(Z ⟶ X)` pushes a cap product forward along is the projection of the
identity base change. -/
theorem identityBaseChange_snd_eq_localizedComposeIso {T : Scheme.{u}} (t : T ⟶ X) :
    pullback.snd (𝟙 Z) (pullback.fst f t) =
      (pullbackRightPullbackFstIso f t (𝟙 Z)).hom ≫
        (pullback.congrHom (Category.id_comp f) (rfl : t = t)).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [localizedComposeIso_fst f t]
    simpa using (pullback.condition (f := 𝟙 Z) (g := pullback.fst f t)).symm
  · simp

/-- **The associativity of Stacks 0B75 at the third pairing of Stacks 0FA0:**
`(α · β) ∘ c = α ∘ (β ∘ c)` for classes `α`, `β` on `Z` and a localized class `c`, the product
`α · β` being the multiplication of `A^*(Z)`.

Together with the multiplicativity of the restriction of Stacks 0F9Z
(`Stacks.Chow.chowCohomologyRestriction_chowCohomologyComposite`) this is the identity
`T₂(b · b', c) = T₂(b, T₂(b', c))` for the second pairing — the third of the three instances of
the associativity of Stacks 0B75 that an associativity proof for the multiplication of Stacks
0FA0 needs; see the implementation notes.

It is a heterogeneous equality only because the two sides are indexed by `(i + j) + l` and
`i + (j + l)`, the same integer written two ways. -/
theorem localizedComposeChowCohomology_chowCohomologyComposite_heq (i j l : ℤ)
    (a : chowCohomologyComponent C G (f ≫ sX) i)
    (b : chowCohomologyComponent C G (f ≫ sX) j)
    (w : BivariantClass C G (f ≫ sX) sX f rfl l) :
    localizedComposeChowCohomology C G sX f hgys hgysc (i + j) l
        (chowCohomologyComposite C G (f ≫ sX) hgys hgysc i j a b) w ≍
      localizedComposeChowCohomology C G sX f hgys hgysc i (j + l) a
        (localizedComposeChowCohomology C G sX f hgys hgysc j l b w) := by
  refine BivariantClass.heq_of_cap_heq C G (f ≫ sX) sX f rfl (add_assoc i j l) _ _ ?_
  intro T t ht k α
  rw [localizedComposeChowCohomology_cap C G sX f hgys hgysc (i + j) l _ w t k α,
    chowCohomologyComposite_cap C G (f ≫ sX) hgys hgysc i j a b (pullback.fst f t) (k - l) _,
    localizedComposeChowCohomology_cap C G sX f hgys hgysc i (j + l) a _ t k α,
    localizedComposeChowCohomology_cap C G sX f hgys hgysc j l b w t k α]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ((pushforward_cap_comp_heq a
    (localizedComposeIso_fst f t) (localizedComposeIso_base C sX f t) ?_
    (by ring) (by ring) _).trans (chowGroupDegreeEquiv_heq C _ _ _).symm)
  refine congrArg (· ≫ _) (pullback.hom_ext ?_ ?_)
  · simp
  · simpa using congrArg
      (pullback.snd (𝟙 Z) (pullback.fst (𝟙 Z) (pullback.fst f t)) ≫ ·)
      (identityBaseChange_snd_eq_localizedComposeIso f t)

/-- **The associativity of Stacks 0B75 for the first and the second pairing of Stacks 0FA0:**
`(res(b) ∘ c) ∘ b' = res(b) ∘ (c ∘ b')`, that is, `T₁(T₂(b, c), b') = T₂(b, T₁(c, b'))` for the
first pairing `T₁` and the second pairing `T₂`. This is
`Stacks.Chow.localizedMulBivariantChow_localizedComposeChowCohomology_heq` at the restricted
class. -/
theorem localizedMulBivariantChow_localizedMulChowBivariant_heq (i j l : ℤ)
    (u : chowCohomologyComponent C G sX i) (y : BivariantClass C G (f ≫ sX) sX f rfl j)
    (v : chowCohomologyComponent C G sX l) :
    localizedMulBivariantChow C G sX f hgys hgysc (i + j) l
        (localizedMulChowBivariant C G sX f hgys hgysc i j u y) v ≍
      localizedMulChowBivariant C G sX f hgys hgysc i (j + l) u
        (localizedMulBivariantChow C G sX f hgys hgysc j l y v) :=
  localizedMulBivariantChow_localizedComposeChowCohomology_heq C G sX f hgys hgysc i j l
    (chowCohomologyRestriction C G sX f i hgys u) y v

/-- **The associativity of Stacks 0B75 for the second pairing of Stacks 0FA0:**
`(b · b') ∘ c = b ∘ (b' ∘ c)` read through the restriction of Stacks 0F9Z, that is,
`T₂(b · b', c) = T₂(b, T₂(b', c))` for the second pairing `T₂` and the multiplication of
`A^*(X)`. This is where the multiplicativity of the restriction of Stacks 0F9Z,
`Stacks.Chow.chowCohomologyRestriction_chowCohomologyComposite`, is consumed: the restriction of
the product `b · b'` is the product of the restrictions, and the associativity of Stacks 0B75
finishes. -/
theorem localizedMulChowBivariant_chowCohomologyComposite_heq (i j l : ℤ)
    (u : chowCohomologyComponent C G sX i) (v : chowCohomologyComponent C G sX j)
    (w : BivariantClass C G (f ≫ sX) sX f rfl l) :
    localizedMulChowBivariant C G sX f hgys hgysc (i + j) l
        (chowCohomologyComposite C G sX hgys hgysc i j u v) w ≍
      localizedMulChowBivariant C G sX f hgys hgysc i (j + l) u
        (localizedMulChowBivariant C G sX f hgys hgysc j l v w) := by
  unfold localizedMulChowBivariant
  rw [chowCohomologyRestriction_chowCohomologyComposite C G sX f hgys hgysc i j u v]
  exact localizedComposeChowCohomology_chowCohomologyComposite_heq C G sX f hgys hgysc i j l
    (chowCohomologyRestriction C G sX f i hgys u)
    (chowCohomologyRestriction C G sX f j hgys v) w

/-- Two bivariant classes whose degrees are the same integer written two ways, transported into a
common degree, are equal as soon as they are heterogeneously equal. This is what turns the three
associativity identities above, which are heterogeneous for the reason
`Stacks.Chow.bivariantComposite_assoc` is, into the transported form that the `(i, n - i)` terms of
a product of Stacks 0FA0 (`Stacks.Chow.localizedGradingMulLocalizedTerm`,
`Stacks.Chow.localizedGradingMulAmbientTerm`) are wrapped in. -/
theorem bivariantClassDegreeCongr_eq_of_heq {Y W : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (w : Y ⟶ W)
    [LocallyOfFiniteType w] (hw : w ≫ sW = sY) {d₁ d₂ n : ℤ} (h₁ : d₁ = n) (h₂ : d₂ = n)
    (A : BivariantClass C G sY sW w hw d₁) (B : BivariantClass C G sY sW w hw d₂) (hAB : A ≍ B) :
    bivariantClassDegreeCongr C G sY sW w hw h₁ A =
      bivariantClassDegreeCongr C G sY sW w hw h₂ B := by
  subst h₁
  subst h₂
  exact congrArg _ (eq_of_heq hAB)

end Associativity

/-! ### The two restrictions and the pushforward of Stacks 0EPK -/

section RestrictionPushforward

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (hgysP : G.IsNaturalUnderProperPushforward)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

omit [LocallyOfFiniteType sX] in
/-- A test morphism that factors through the closed immersion `f` has `f` for its own base change,
up to isomorphism: the base change `Z ×_X T ⟶ X ×_X T` of `f` along `g ≫ f` is an isomorphism,
`g : T ⟶ Z` being a section of it over `T`. This is why the pushforward of Stacks 0EPK loses
nothing when its value is restricted back to `Z`. -/
theorem isIso_bivariantPushforwardBaseChange_comp {T : Scheme.{u}} (g : T ⟶ Z) :
    IsIso (bivariantPushforwardBaseChange f (𝟙 X) (g ≫ f)) := by
  have hcond : pullback.fst (f ≫ 𝟙 X) (g ≫ f) =
      pullback.snd (f ≫ 𝟙 X) (g ≫ f) ≫ g := by
    refine (cancel_mono f).1 ?_
    simpa [Category.assoc] using pullback.condition (f := f ≫ 𝟙 X) (g := g ≫ f)
  have hlift : (pullback.snd (𝟙 X) (g ≫ f) ≫ g) ≫ (f ≫ 𝟙 X) =
      pullback.snd (𝟙 X) (g ≫ f) ≫ (g ≫ f) := by simp
  refine ⟨⟨pullback.lift _ _ hlift, pullback.hom_ext ?_ ?_, pullback.hom_ext ?_ ?_⟩⟩
  · rw [Category.id_comp, Category.assoc, pullback.lift_fst, ← Category.assoc,
      bivariantPushforwardBaseChange_snd, hcond]
  · rw [Category.id_comp, Category.assoc, pullback.lift_snd,
      bivariantPushforwardBaseChange_snd]
  · rw [Category.id_comp, Category.assoc, bivariantPushforwardBaseChange_fst, ← Category.assoc,
      pullback.lift_fst, Category.assoc, ← pullback.condition, Category.comp_id]
  · rw [Category.id_comp, Category.assoc, bivariantPushforwardBaseChange_snd,
      pullback.lift_snd]

/-- **The restriction of Stacks 0F9Z is the restriction of Stacks 0B7F of the pushforward of
Stacks 0EPK:** `res(c) = f^*(f_*(c))` for a localized class `c`, the left restriction being the
map `A^i(Z ⟶ X) ⟶ A^i(Z)` of Stacks 0F9Z and the right one the map `A^i(X) ⟶ A^i(Z)` of
Stacks 0B7F.

Both sides cap, on a test scheme `g : T ⟶ Z`, by capping with `c` at the test morphism `g ≫ f`
and reading the result on `Z ×_Z T`. On the right the pushforward of Stacks 0EPK pushes along the
base change `Z ×_X T ⟶ X ×_X T` of `f`, which is an isomorphism because `g` factors through `f`
(`Stacks.Chow.isIso_bivariantPushforwardBaseChange_comp`); on the left the identification is the
restriction's own. So the pushforward of Stacks 0EPK loses nothing in the degrees a restriction
back to `Z` reads. -/
theorem chowCohomologyRestriction_localizedGradingPushforward (i : ℤ)
    (x : BivariantClass C G (f ≫ sX) sX f rfl i) :
    chowCohomologyRestriction C G sX f i hgys
        (localizedGradingPushforward C G sX f hRG hgysP hgysc i x) =
      closedImmersionChowCohomologyRestriction C G (f ≫ sX) sX f rfl i hgys x := by
  refine BivariantClass.ext C G (f ≫ sX) (f ≫ sX) (𝟙 Z) (Category.id_comp (f ≫ sX)) i ?_
  intro T g hg k α
  have : IsIso (bivariantPushforwardBaseChange f (𝟙 X) (g ≫ f)) :=
    isIso_bivariantPushforwardBaseChange_comp (f := f) (g := g)
  rw [chowCohomologyRestriction_cap_eq C G sX f hgys i _ g k α,
    localizedGradingPushforward_cap_eq C G sX f hRG hgysP hgysc i x (g ≫ f) k _,
    closedImmersionChowCohomologyRestriction_cap_eq C G sX f hgys i x g k α,
    properChowPushforward_eq_chowPushforwardOfIso C ((pullback.fst f (g ≫ f) ≫ f) ≫ sX)
      (pullback.fst (𝟙 X) (g ≫ f) ≫ sX)
      ((pullback.congrHom (Category.comp_id f).symm rfl).hom ≫
        bivariantPushforwardBaseChange f (𝟙 X) (g ≫ f))
      (pushforwardTestBaseChange_base C sX f (g ≫ f)) (k - i)
      (properPushforwardDescends C _ _ _ _ _),
    chowPushforwardOfIso_chowGroupCongr_source C (pullback.fst (𝟙 X) (g ≫ f) ≫ sX)
      (Category.assoc (pullback.fst f (g ≫ f)) f sX).symm
      ((pullback.congrHom (Category.comp_id f).symm rfl).hom ≫
        bivariantPushforwardBaseChange f (𝟙 X) (g ≫ f))
      ((pushforwardTestBaseChange_base C sX f (g ≫ f)).trans
        (Category.assoc (pullback.fst f (g ≫ f)) f sX))
      (pushforwardTestBaseChange_base C sX f (g ≫ f)) (k - i) _,
    chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ (k - i) _
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- **The third pairing of Stacks 0FA0 is the second pairing after the pushforward of Stacks
0EPK:** `T₂(f_*(c), c') = T₃(c, c')`. Together with
`Stacks.Chow.localizedMulBivariant_eq_localizedMulBivariantChow`, which rewrites the third pairing
as the first, this says that a localized factor may be pushed into `A^*(X)` before it is multiplied
on the left without changing the product — which is what makes the product of Stacks 0FA0
associative at a target whose cutoff forces an intermediate product into `A^*(X)`. -/
theorem localizedMulChowBivariant_localizedGradingPushforward (i j : ℤ)
    (x : BivariantClass C G (f ≫ sX) sX f rfl i)
    (y : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulChowBivariant C G sX f hgys hgysc i j
        (localizedGradingPushforward C G sX f hRG hgysP hgysc i x) y =
      localizedMulBivariant C G sX f hgys hgysc i j x y := by
  unfold localizedMulChowBivariant localizedMulBivariant
  rw [chowCohomologyRestriction_localizedGradingPushforward C G sX f hRG hgysP hgys hgysc i x]

/-- **A localized factor may be pushed into `A^*(X)` before it is multiplied on the left:**
`T₂(f_*(c), c') = T₁(c, f_*(c'))`. This is
`Stacks.Chow.localizedMulChowBivariant_localizedGradingPushforward` followed by
`Stacks.Chow.localizedMulBivariant_eq_localizedMulBivariantChow`. It is the identity the degrees
below the cutoff of an intermediate product of a triple product need: there the intermediate
product is read in `A^*(X)`, and the identity says that reading it there loses nothing. -/
theorem localizedMulChowBivariant_localizedGradingPushforward_eq (i j : ℤ)
    (x : BivariantClass C G (f ≫ sX) sX f rfl i)
    (y : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulChowBivariant C G sX f hgys hgysc i j
        (localizedGradingPushforward C G sX f hRG hgysP hgysc i x) y =
      localizedMulBivariantChow C G sX f hgys hgysc i j x
        (localizedGradingPushforward C G sX f hRG hgysP hgysc j y) :=
  (localizedMulChowBivariant_localizedGradingPushforward C G sX f hRG hgysP hgys hgysc i j
    x y).trans (localizedMulBivariant_eq_localizedMulBivariantChow C G sX f hRG hgysP hgys hgysc
      i j x y)

/-! ### The pairings over a finite sum -/

/-- The first pairing commutes with a finite sum in its localized argument. -/
theorem localizedMulBivariantChow_sum_left {ι : Type*} (s : Finset ι) (i j : ℤ)
    (x : ι → BivariantClass C G (f ≫ sX) sX f rfl i)
    (u : chowCohomologyComponent C G sX j) :
    localizedMulBivariantChow C G sX f hgys hgysc i j (∑ m ∈ s, x m) u =
      ∑ m ∈ s, localizedMulBivariantChow C G sX f hgys hgysc i j (x m) u :=
  map_sum (AddMonoidHom.mk' (fun c ↦ localizedMulBivariantChow C G sX f hgys hgysc i j c u)
    fun c c' ↦ localizedMulBivariantChow_add_left C G sX f hgys hgysc i j c c' u) x s

/-- The first pairing commutes with a finite sum in its argument on `X`. -/
theorem localizedMulBivariantChow_sum_right {ι : Type*} (s : Finset ι) (i j : ℤ)
    (x : BivariantClass C G (f ≫ sX) sX f rfl i)
    (u : ι → chowCohomologyComponent C G sX j) :
    localizedMulBivariantChow C G sX f hgys hgysc i j x (∑ m ∈ s, u m) =
      ∑ m ∈ s, localizedMulBivariantChow C G sX f hgys hgysc i j x (u m) :=
  map_sum (AddMonoidHom.mk' (fun v ↦ localizedMulBivariantChow C G sX f hgys hgysc i j x v)
    fun v v' ↦ localizedMulBivariantChow_add_right C G sX f hgys hgysc i j x v v') u s

/-- The second pairing commutes with a finite sum in its argument on `X`. -/
theorem localizedMulChowBivariant_sum_left {ι : Type*} (s : Finset ι) (i j : ℤ)
    (u : ι → chowCohomologyComponent C G sX i)
    (y : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulChowBivariant C G sX f hgys hgysc i j (∑ m ∈ s, u m) y =
      ∑ m ∈ s, localizedMulChowBivariant C G sX f hgys hgysc i j (u m) y :=
  map_sum (AddMonoidHom.mk' (fun v ↦ localizedMulChowBivariant C G sX f hgys hgysc i j v y)
    fun v v' ↦ localizedMulChowBivariant_add_left C G sX f hgys hgysc i j v v' y) u s

/-- The second pairing commutes with a finite sum in its localized argument. -/
theorem localizedMulChowBivariant_sum_right {ι : Type*} (s : Finset ι) (i j : ℤ)
    (u : chowCohomologyComponent C G sX i)
    (y : ι → BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulChowBivariant C G sX f hgys hgysc i j u (∑ m ∈ s, y m) =
      ∑ m ∈ s, localizedMulChowBivariant C G sX f hgys hgysc i j u (y m) :=
  map_sum (AddMonoidHom.mk' (fun w ↦ localizedMulChowBivariant C G sX f hgys hgysc i j u w)
    fun w w' ↦ localizedMulChowBivariant_add_right C G sX f hgys hgysc i j u w w') y s

/-! ### The uniform form of a term of the localized branch -/

/-- **A term of the localized branch whose first factor is localized is the first pairing applied
to the second factor read in `A^*(X)`**, whatever the second factor's degree: in the case
`n - i ≥ q` this is `Stacks.Chow.localizedMulBivariant_eq_localizedMulBivariantChow`, the identity
`res(c) ∘ c' = c ∘ f_*(c')`. The two branches `n - i ≥ q` and `n - i < q` of
`Stacks.Chow.localizedGradingMulLocalizedTerm` therefore collapse to one. -/
theorem localizedGradingMulLocalizedTerm_of_le (p q : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n i : ℤ)
    (hi : (p : ℤ) ≤ i) :
    localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n i =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (by ring : i + (n - i) = n)
        (localizedMulBivariantChow C G sX f hgys hgysc i (n - i) (a.2 ⟨i, hi⟩)
          (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc q b (n - i))) := by
  unfold localizedGradingMulLocalizedTerm localizedGradingComponentOnAmbient
  rw [dite_eq_left hi]
  by_cases hj : (q : ℤ) ≤ n - i
  · rw [dite_eq_left hj, dite_eq_left hj,
      localizedMulBivariant_eq_localizedMulBivariantChow C G sX f hRG
        hgysP hgys hgysc i (n - i) (a.2 ⟨i, hi⟩) (b.2 ⟨n - i, hj⟩)]
  · rw [dite_eq_right hj, dite_eq_right hj]

/-- A term of the localized branch whose first factor is ambient and whose second factor is
localized is the second pairing. In the degrees `n ≥ r` of an admissible target `p + q ≤ r + 1`
the hypothesis `hj` is automatic from `hi`, by
`Stacks.Chow.localizedGrading_add_lt_of_admissible`. -/
theorem localizedGradingMulLocalizedTerm_of_lt (p q : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n i : ℤ)
    (hi : i < (p : ℤ)) (hj : (q : ℤ) ≤ n - i) :
    localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n i =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (by ring : i + (n - i) = n)
        (localizedMulChowBivariant C G sX f hgys hgysc i (n - i) (a.1 ⟨i, hi⟩)
          (b.2 ⟨n - i, hj⟩)) := by
  unfold localizedGradingMulLocalizedTerm
  rw [dite_eq_right (not_le.2 hi), dite_eq_left hj]

/-! ### The reindexing of a double convolution -/

/-- The two ways of summing a double convolution over the triangle the index range of Stacks
0FA0's sums cuts out — the pairs `(m, j)` of degrees whose sum lies between `0` and `n` and which
both have the sign of `n`: by the total degree `i = m + j` of the inner product, which is how a
product of Stacks 0FA0 expands when the first two factors are multiplied first, and by the degree
`m` of the first factor, which is how it expands when the last two are. For `n ≥ 0` the triangle is
`0 ≤ m`, `0 ≤ j`, `m + j ≤ n` and for `n < 0` it is its reflection `m ≤ 0`, `j ≤ 0`,
`n ≤ m + j`. -/
theorem sum_Icc_diag_flip {M : Type*} [AddCommMonoid M] (n : ℤ) (F : ℤ → ℤ → M) :
    ∑ i ∈ Finset.Icc (min 0 n) (max 0 n), ∑ m ∈ Finset.Icc (min 0 i) (max 0 i), F m (i - m) =
      ∑ m ∈ Finset.Icc (min 0 n) (max 0 n),
        ∑ j ∈ Finset.Icc (min 0 (n - m)) (max 0 (n - m)), F m j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x ↦ ⟨x.2, x.1 - x.2⟩) (fun x ↦ ⟨x.1 + x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    omega
  · rintro ⟨m, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    omega
  · rintro ⟨i, m⟩ _
    simp
  · rintro ⟨m, j⟩ _
    simp
  · rintro ⟨i, m⟩ _
    rfl

/-! ### Transport in an argument of a pairing -/

/-- Transport of the localized argument of the first pairing. -/
theorem localizedMulBivariantChow_bivariantClassDegreeCongr_left {d d' : ℤ} (h : d = d') (l : ℤ)
    (x : BivariantClass C G (f ≫ sX) sX f rfl d) (v : chowCohomologyComponent C G sX l) :
    localizedMulBivariantChow C G sX f hgys hgysc d' l
        (bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl h x) v ≍
      localizedMulBivariantChow C G sX f hgys hgysc d l x v := by
  subst h
  rfl

/-- Transport of the argument on `X` of the first pairing. -/
theorem localizedMulBivariantChow_bivariantClassDegreeCongr_right {d d' : ℤ} (h : d = d')
    (m : ℤ) (x : BivariantClass C G (f ≫ sX) sX f rfl m)
    (v : chowCohomologyComponent C G sX d) :
    localizedMulBivariantChow C G sX f hgys hgysc m d' x
        (bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) h v) ≍
      localizedMulBivariantChow C G sX f hgys hgysc m d x v := by
  subst h
  rfl

/-- Transport of the argument on `X` of the second pairing. -/
theorem localizedMulChowBivariant_bivariantClassDegreeCongr_left {d d' : ℤ} (h : d = d') (l : ℤ)
    (u : chowCohomologyComponent C G sX d) (w : BivariantClass C G (f ≫ sX) sX f rfl l) :
    localizedMulChowBivariant C G sX f hgys hgysc d' l
        (bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) h u) w ≍
      localizedMulChowBivariant C G sX f hgys hgysc d l u w := by
  subst h
  rfl

/-- Transport of the localized argument of the second pairing. -/
theorem localizedMulChowBivariant_bivariantClassDegreeCongr_right {d d' : ℤ} (h : d = d')
    (m : ℤ) (u : chowCohomologyComponent C G sX m)
    (w : BivariantClass C G (f ≫ sX) sX f rfl d) :
    localizedMulChowBivariant C G sX f hgys hgysc m d' u
        (bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl h w) ≍
      localizedMulChowBivariant C G sX f hgys hgysc m d u w := by
  subst h
  rfl

/-- Above the cutoff the component pushed into `A^*(X)` is the pushforward of Stacks 0EPK of the
component. -/
theorem localizedGradingComponentOnAmbient_of_le (p : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) (i : ℤ) (hi : (p : ℤ) ≤ i) :
    localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p a i =
      localizedGradingPushforward C G sX f hRG hgysP hgysc i (a.2 ⟨i, hi⟩) := by
  unfold localizedGradingComponentOnAmbient
  rw [dite_eq_left hi]

end RestrictionPushforward

end Stacks.Chow

end
