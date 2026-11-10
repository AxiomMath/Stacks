module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseProper
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingAlgebra
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommuting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingProjectionFormula.RestrictionMultiplicative

/-!
# The projection formula for the pushforward of Stacks 0EPK

The cap formulas of the pairings of Stacks 0FA0 and of the restriction of Stacks 0F9Z, and the
second input to the associativity of the multiplication of Stacks 0FA0: the projection formula
`res(c) ∘ c' = c ∘ f_*(c')`
(`Stacks.Chow.localizedMulBivariant_eq_localizedMulBivariantChow`), `f_*` of each of the three
pairings, the pushforward as a group homomorphism `Stacks.Chow.localizedGradingPushforwardHom`,
and their joint consequence `Stacks.Chow.localizedBivariantGradingMul_isAmbientConvolution`.
The overview of the whole development is the module docstring of the first part,
`RestrictionMultiplicative`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Pushforward

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (hgysP : G.IsNaturalUnderProperPushforward)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The comparison isomorphism of the base changes of `f` and of `f ≫ 𝟙 X` along a test scheme is
a morphism over the base. -/
theorem congrHom_compIdRight_base {T : Scheme.{u}} (t : T ⟶ X) :
    (pullback.congrHom (Category.comp_id f) (rfl : t = t)).hom ≫
        (pullback.fst f t ≫ (f ≫ sX)) = pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX) := by
  rw [← Category.assoc]
  simp

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The comparison isomorphism of the base changes of `f ≫ 𝟙 X` and of `f` along a test scheme is
a morphism over the base. -/
theorem congrHom_compIdRight_base' {T : Scheme.{u}} (t : T ⟶ X) :
    (pullback.congrHom (Category.comp_id f).symm (rfl : t = t)).hom ≫
        (pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX)) = pullback.fst f t ≫ (f ≫ sX) := by
  rw [← Category.assoc]
  simp

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The identification `Z ×_X (X ×_X T) ≅ Z ×_X T` that the first pairing of Stacks 0FA0 pushes a
cap product forward along is a morphism over the base. -/
theorem localizedMulBivariantChowIso_base {T : Scheme.{u}} (t : T ⟶ X) :
    ((pullbackRightPullbackFstIso (𝟙 X) t f).hom ≫
          (pullback.congrHom (Category.comp_id f) (rfl : t = t)).hom) ≫
        (pullback.fst f t ≫ (f ≫ sX)) =
      pullback.fst f (pullback.fst (𝟙 X) t) ≫ (f ≫ sX) := by
  rw [Category.assoc, congrHom_compIdRight_base C sX f t]
  exact pullbackRightPullbackFstIso_hom_comp_fst_comp (f ≫ sX) f (𝟙 X) t

/-- The cap operation of the first pairing of Stacks 0FA0: cap with the class on `X`, cap with the
localized class, and push forward along the canonical identification of `Z ×_X (X ×_X T)` with
`Z ×_X T`. -/
theorem localizedMulBivariantChow_cap (i j : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl i) (b : chowCohomologyComponent C G sX j)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    (localizedMulBivariantChow C G sX f hgys hgysc i j c b).cap t k α =
      chowGroupDegreeEquiv C (pullback.fst f t ≫ (f ≫ sX))
        (by ring : k - j - i = k - (i + j))
        (chowPushforwardOfIso C (pullback.fst f (pullback.fst (𝟙 X) t) ≫ (f ≫ sX))
          (pullback.fst f t ≫ (f ≫ sX))
          ((pullbackRightPullbackFstIso (𝟙 X) t f).hom ≫
            (pullback.congrHom (Category.comp_id f) rfl).hom)
          (localizedMulBivariantChowIso_base C sX f t) (k - j - i)
          (c.cap (pullback.fst (𝟙 X) t) (k - j) (b.cap t k α))) := by
  unfold localizedMulBivariantChow
  rw [← bivariantClassCongr_cap C G (f ≫ sX) sX (Category.comp_id f)
      (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) rfl (i + j) _ t k α
      (congrHom_compIdRight_base C sX f t),
    bivariantComposite_cap, bivariantCompositeCap_apply,
    properChowPushforward_eq_chowPushforwardOfIso C
      (pullback.fst f (pullback.fst (𝟙 X) t) ≫ (f ≫ sX))
      (pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX))
      (pullbackRightPullbackFstIso (𝟙 X) t f).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp (f ≫ sX) f (𝟙 X) t) (k - j - i) _,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso C
      (pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX)) (pullback.fst f t ≫ (f ≫ sX))
      (pullback.congrHom (Category.comp_id f) rfl).hom (congrHom_compIdRight_base C sX f t)
      (by ring : k - j - i = k - (i + j)),
    chowPushforwardOfIso_comp_apply]

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The base change `Z ×_X T ⟶ X ×_X T` of `f` along a test scheme, as the pushforward of Stacks
0EPK uses it, is a morphism over the base. -/
theorem pushforwardTestBaseChange_base {T : Scheme.{u}} (t : T ⟶ X) :
    ((pullback.congrHom (Category.comp_id f).symm (rfl : t = t)).hom ≫
        bivariantPushforwardBaseChange f (𝟙 X) t) ≫ (pullback.fst (𝟙 X) t ≫ sX) =
      (pullback.fst f t ≫ f) ≫ sX := by
  rw [Category.assoc, bivariantPushforwardBaseChange_comp_structure
    (rfl : f ≫ sX = f ≫ sX) (𝟙 X) t, ← Category.assoc]
  exact congrHom_compIdRight_base' C sX f t

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The base change `Z ×_X T ⟶ X ×_X T` of `f` along a test scheme carries the test morphism
`X ×_X T ⟶ X` to the test morphism `Z ×_X T ⟶ X` of the localized factor. This is the equality of
test morphisms that the proper-pushforward axiom of Stacks 0B76 is applied at. -/
theorem pushforwardTestBaseChange_fst {T : Scheme.{u}} (t : T ⟶ X) :
    ((pullback.congrHom (Category.comp_id f).symm (rfl : t = t)).hom ≫
        bivariantPushforwardBaseChange f (𝟙 X) t) ≫ pullback.fst (𝟙 X) t =
      pullback.fst f t ≫ f := by
  rw [Category.assoc, bivariantPushforwardBaseChange_fst, ← Category.assoc]
  simp

/-- The base change of the pushforward base change `Z ×_X T ⟶ X ×_X T` along any morphism into `X`
is proper. -/
private theorem isProper_baseChangeMapOfEq_pushforwardTestBaseChange {X' : Scheme.{u}} (g : X' ⟶ X)
    {T : Scheme.{u}} (t : T ⟶ X) :
    IsProper (baseChangeMapOfEq g (pullback.fst (𝟙 X) t)
      ((pullback.congrHom (Category.comp_id f).symm (rfl : t = t)).hom ≫
        bivariantPushforwardBaseChange f (𝟙 X) t) (pullback.fst f t ≫ f)
      (pushforwardTestBaseChange_fst f t)) :=
  MorphismProperty.of_isPullback (P := @IsProper)
    (isPullback_baseChangeMapOfEq g (pullback.fst (𝟙 X) t)
      ((pullback.congrHom (Category.comp_id f).symm (rfl : t = t)).hom ≫
        bivariantPushforwardBaseChange f (𝟙 X) t) (pullback.fst f t ≫ f)
      (pushforwardTestBaseChange_fst f t)) inferInstance

/-- **The cap operation of the pushforward of Stacks 0EPK**, with the two identifications it is
built from merged into the single proper morphism `Z ×_X T ⟶ X ×_X T` base changing `f`. -/
theorem localizedGradingPushforward_cap_eq (j : ℤ)
    (y : BivariantClass C G (f ≫ sX) sX f rfl j) {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (localizedGradingPushforward C G sX f hRG hgysP hgysc j y).cap t k α =
      properChowPushforward C ((pullback.fst f t ≫ f) ≫ sX) (pullback.fst (𝟙 X) t ≫ sX)
        ((pullback.congrHom (Category.comp_id f).symm rfl).hom ≫
          bivariantPushforwardBaseChange f (𝟙 X) t)
        (pushforwardTestBaseChange_base C sX f t) (k - j)
        (properPushforwardDescends C _ _ _ _ _)
        (chowGroupCongr C (Category.assoc (pullback.fst f t) f sX).symm (k - j)
          (y.cap t k α)) := by
  rw [localizedGradingPushforward_isBivariantProperPushforward C G sX f hRG hgysP hgysc j y t k α,
    bivariantProperPushforwardCap_apply,
    ← bivariantClassCongr_cap C G (f ≫ sX) sX (Category.comp_id f).symm rfl
      (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) j y t k α
      (congrHom_compIdRight_base' C sX f t),
    ← chowPushforwardOfIso_chowGroupCongr_source C
      (pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX))
      (Category.assoc (pullback.fst f t) f sX).symm
      (pullback.congrHom (Category.comp_id f).symm rfl).hom
      (congrHom_compIdRight_base' C sX f t)
      (by rw [Category.assoc]; exact congrHom_compIdRight_base' C sX f t) (k - j),
    ← properChowPushforward_eq_chowPushforwardOfIso C ((pullback.fst f t ≫ f) ≫ sX)
      (pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX))
      (pullback.congrHom (Category.comp_id f).symm rfl).hom
      (by rw [Category.assoc]; exact congrHom_compIdRight_base' C sX f t) (k - j)
      (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_comp_apply C ((pullback.fst f t ≫ f) ≫ sX)
      (pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX)) (pullback.fst (𝟙 X) t ≫ sX)
      (pullback.congrHom (Category.comp_id f).symm rfl).hom
      (bivariantPushforwardBaseChange f (𝟙 X) t) _ rfl
      (by rw [Category.assoc]; exact congrHom_compIdRight_base' C sX f t)
      (bivariantPushforwardBaseChange_comp_structure (rfl : f ≫ sX = f ≫ sX) (𝟙 X) t)
      (pushforwardTestBaseChange_base C sX f t) (k - j)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _)]

/-- **The projection formula for the pushforward of Stacks 0EPK at the first pairing of
Stacks 0FA0:** `f_*(c ∘ b) = f_*(c) · b` for a localized class `c` and a class `b` on `X`, the
product on the right being the multiplication of `A^*(X)`. -/
theorem localizedGradingPushforward_localizedMulBivariantChow (i j : ℤ)
    (x : BivariantClass C G (f ≫ sX) sX f rfl i) (y : chowCohomologyComponent C G sX j) :
    localizedGradingPushforward C G sX f hRG hgysP hgysc (i + j)
        (localizedMulBivariantChow C G sX f hgys hgysc i j x y) =
      chowCohomologyComposite C G sX hgys hgysc i j
        (localizedGradingPushforward C G sX f hRG hgysP hgysc i x) y := by
  refine eq_of_isBivariantProperPushforward (hpp := properPushforwardDescends C)
    (localizedGradingPushforward_isBivariantProperPushforward C G sX f hRG hgysP hgysc (i + j)
      (localizedMulBivariantChow C G sX f hgys hgysc i j x y)) ?_
  intro T t ht k α
  rw [chowCohomologyComposite_cap C G sX hgys hgysc i j _ y t k α,
    localizedGradingPushforward_isBivariantProperPushforward C G sX f hRG hgysP hgysc i x
      (pullback.fst (𝟙 X) t) (k - j) (y.cap t k α),
    bivariantProperPushforwardCap_apply, bivariantProperPushforwardCap_apply,
    ← bivariantClassCongr_cap C G (f ≫ sX) sX (Category.comp_id f).symm rfl
      (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) i x (pullback.fst (𝟙 X) t)
      (k - j) (y.cap t k α) (congrHom_compIdRight_base' C sX f (pullback.fst (𝟙 X) t)),
    ← bivariantClassCongr_cap C G (f ≫ sX) sX (Category.comp_id f).symm rfl
      (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) (i + j) _ t k α
      (congrHom_compIdRight_base' C sX f t),
    localizedMulBivariantChow_cap C G sX f hgys hgysc i j x y t k α,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso C (pullback.fst f t ≫ (f ≫ sX))
      (pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX))
      (pullback.congrHom (Category.comp_id f).symm rfl).hom
      (congrHom_compIdRight_base' C sX f t) (by ring : k - j - i = k - (i + j)),
    ← chowGroupDegreeEquiv_properChowPushforward_comp C
      (pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX)) (pullback.fst (𝟙 X) t ≫ sX)
      (bivariantPushforwardBaseChange f (𝟙 X) t) _ (by ring : k - j - i = k - (i + j)) _ _]
  · refine congrArg _ ?_
    rw [chowPushforwardOfIso_comp_apply]
    refine chowPushforwardOfIso_properChowPushforward_comp_eq C _ _ _ _ _ _ _ _ _ _ ?_ _ _ _ _ _
      (k - j - i) _ _ _
    refine pullback.hom_ext ?_ ?_ <;> simp
  · exact properPushforwardDescends C _ _ _ _ _

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The comparison isomorphism of the base changes of `𝟙 Z ≫ f` and of `f` along a test scheme is
a morphism over the base. -/
theorem congrHom_idCompLeft_base {T : Scheme.{u}} (t : T ⟶ X) :
    (pullback.congrHom (Category.id_comp f) (rfl : t = t)).hom ≫
        (pullback.fst f t ≫ (f ≫ sX)) = pullback.fst (𝟙 Z ≫ f) t ≫ (f ≫ sX) := by
  rw [← Category.assoc]
  simp

omit [LocallyOfFiniteType sX] [IsClosedImmersion f] in
/-- The identification `Z ×_Z (Z ×_X T) ≅ Z ×_X T` that the composition
`Aⁱ(Z) × Aʲ(Z ⟶ X) ⟶ Aⁱ⁺ʲ(Z ⟶ X)` pushes a cap product forward along is a morphism over the
base. -/
theorem localizedComposeIso_base {T : Scheme.{u}} (t : T ⟶ X) :
    ((pullbackRightPullbackFstIso f t (𝟙 Z)).hom ≫
          (pullback.congrHom (Category.id_comp f) (rfl : t = t)).hom) ≫
        (pullback.fst f t ≫ (f ≫ sX)) =
      pullback.fst (𝟙 Z) (pullback.fst f t) ≫ (f ≫ sX) := by
  rw [Category.assoc, congrHom_idCompLeft_base C sX f t]
  exact pullbackRightPullbackFstIso_hom_comp_fst_comp (f ≫ sX) (𝟙 Z) f t

/-- The cap operation of the composition `A^i(Z) × A^j(Z ⟶ X) ⟶ A^{i+j}(Z ⟶ X)` that the second
and the third pairing of Stacks 0FA0 are built from. -/
theorem localizedComposeChowCohomology_cap (i j : ℤ)
    (a : chowCohomologyComponent C G (f ≫ sX) i)
    (c : BivariantClass C G (f ≫ sX) sX f rfl j) {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (localizedComposeChowCohomology C G sX f hgys hgysc i j a c).cap t k α =
      chowGroupDegreeEquiv C (pullback.fst f t ≫ (f ≫ sX))
        (by ring : k - j - i = k - (i + j))
        (chowPushforwardOfIso C (pullback.fst (𝟙 Z) (pullback.fst f t) ≫ (f ≫ sX))
          (pullback.fst f t ≫ (f ≫ sX))
          ((pullbackRightPullbackFstIso f t (𝟙 Z)).hom ≫
            (pullback.congrHom (Category.id_comp f) rfl).hom)
          (localizedComposeIso_base C sX f t) (k - j - i)
          (a.cap (pullback.fst f t) (k - j) (c.cap t k α))) := by
  unfold localizedComposeChowCohomology
  rw [← bivariantClassCongr_cap C G (f ≫ sX) sX (Category.id_comp f)
      (comp_comp_structureMorphism_eq (Category.id_comp (f ≫ sX)) rfl) rfl (i + j) _ t k α
      (congrHom_idCompLeft_base C sX f t),
    bivariantComposite_cap, bivariantCompositeCap_apply,
    properChowPushforward_eq_chowPushforwardOfIso C
      (pullback.fst (𝟙 Z) (pullback.fst f t) ≫ (f ≫ sX))
      (pullback.fst (𝟙 Z ≫ f) t ≫ (f ≫ sX))
      (pullbackRightPullbackFstIso f t (𝟙 Z)).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp (f ≫ sX) (𝟙 Z) f t) (k - j - i) _,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso C
      (pullback.fst (𝟙 Z ≫ f) t ≫ (f ≫ sX)) (pullback.fst f t ≫ (f ≫ sX))
      (pullback.congrHom (Category.id_comp f) rfl).hom (congrHom_idCompLeft_base C sX f t)
      (by ring : k - j - i = k - (i + j)),
    chowPushforwardOfIso_comp_apply]

/-- **The projection formula for the pushforward of Stacks 0EPK at the second pairing of
Stacks 0FA0:** `f_*(res(b) ∘ c) = b · f_*(c)` for a class `b` on `X` and a localized class `c`,
the product on the right being the multiplication of `A^*(X)`. -/
theorem localizedGradingPushforward_localizedMulChowBivariant (i j : ℤ)
    (x : chowCohomologyComponent C G sX i) (y : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedGradingPushforward C G sX f hRG hgysP hgysc (i + j)
        (localizedMulChowBivariant C G sX f hgys hgysc i j x y) =
      chowCohomologyComposite C G sX hgys hgysc i j x
        (localizedGradingPushforward C G sX f hRG hgysP hgysc j y) := by
  refine eq_of_isBivariantProperPushforward (hpp := properPushforwardDescends C)
    (localizedGradingPushforward_isBivariantProperPushforward C G sX f hRG hgysP hgysc (i + j)
      (localizedMulChowBivariant C G sX f hgys hgysc i j x y)) ?_
  intro T t ht k α
  have := isProper_baseChangeMapOfEq_pushforwardTestBaseChange f (𝟙 X) t
  rw [chowCohomologyComposite_cap C G sX hgys hgysc i j x _ t k α,
    localizedGradingPushforward_cap_eq C G sX f hRG hgysP hgysc j y t k α,
    x.proper_naturality_of_test_eq (pullback.fst (𝟙 X) t)
      ((pullback.congrHom (Category.comp_id f).symm rfl).hom ≫
        bivariantPushforwardBaseChange f (𝟙 X) t) (pullback.fst f t ≫ f)
      (pushforwardTestBaseChange_fst f t)
      (baseChangeMapOfEq (𝟙 X) (pullback.fst (𝟙 X) t) _ _
        (pushforwardTestBaseChange_fst f t))
      (isPullback_baseChangeMapOfEq (𝟙 X) (pullback.fst (𝟙 X) t) _ _
        (pushforwardTestBaseChange_fst f t))
      (baseChangeMapOfEq_fst (𝟙 X) (pullback.fst (𝟙 X) t) _ _
        (pushforwardTestBaseChange_fst f t)) (k - j)
      (pushforwardTestBaseChange_base C sX f t) (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) _,
    bivariantProperPushforwardCap_apply,
    ← bivariantClassCongr_cap C G (f ≫ sX) sX (Category.comp_id f).symm rfl
      (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) (i + j) _ t k α
      (congrHom_compIdRight_base' C sX f t)]
  unfold localizedMulChowBivariant
  rw [localizedComposeChowCohomology_cap C G sX f hgys hgysc i j _ y t k α,
    chowCohomologyRestriction_cap_eq C G sX f hgys i x (pullback.fst f t) (k - j) (y.cap t k α),
    ← chowGroupDegreeEquiv_chowPushforwardOfIso C (pullback.fst f t ≫ (f ≫ sX))
      (pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX))
      (pullback.congrHom (Category.comp_id f).symm rfl).hom
      (congrHom_compIdRight_base' C sX f t) (by ring : k - j - i = k - (i + j)),
    ← chowGroupDegreeEquiv_properChowPushforward_comp C
      (pullback.fst (f ≫ 𝟙 X) t ≫ (f ≫ sX)) (pullback.fst (𝟙 X) t ≫ sX)
      (bivariantPushforwardBaseChange f (𝟙 X) t) _ (by ring : k - j - i = k - (i + j)) _
      (properPushforwardDescends C _ _ _ _ _)]
  · refine congrArg _ ?_
    rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
    refine chowPushforwardOfIso_comm_properChowPushforward C _ _ _ _ _ _ _ _ ?_ _ _ _ _
      (k - j - i) _ _ _
    refine pullback.hom_ext ?_ ?_ <;> simp [fst_eq_identityBaseChangeIso_hom]
  · exact properPushforwardDescends C _ _ _ _ _

omit [LocallyOfFiniteType sX] in
/-- The identification `Z ×_X T ≅ Z ×_Z T` of the two fibre products through which the restriction
of Stacks 0F9Z along a closed immersion operates is a morphism over the base. -/
theorem closedImmersionRestrictionIso_base {T : Scheme.{u}} (g : T ⟶ Z) :
    ((pullbackLeftPullbackSndIso f f g).inv ≫
        (transportPullbackIso (pullback.snd f f) (𝟙 Z) (asIso (pullback.snd f f))
          (by simp) g).hom) ≫
      (pullback.fst (𝟙 Z) g ≫ (f ≫ sX)) = pullback.fst f (g ≫ f) ≫ (f ≫ sX) := by
  have h := pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl (g ≫ f)
  rw [Category.assoc g f sX] at h
  simpa using h

/-- **The cap operation of the restriction `A^p(Z ⟶ X) ⟶ A^p(Z)` of Stacks 0F9Z along a closed
immersion**, at an arbitrary test scheme: the cap operation of the class itself at the test
morphism composed with `f`, pushed forward along the canonical identification of the two fibre
products. The cap formula of Stacks 0FA1,
`Stacks.Chow.closedImmersionChowCohomologyRestriction_cap`, is this at the test scheme `𝟙 Z`. -/
theorem closedImmersionChowCohomologyRestriction_cap_eq (p : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl p) {T : Scheme.{u}} (g : T ⟶ Z)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (f ≫ sX)) k) :
    (closedImmersionChowCohomologyRestriction C G (f ≫ sX) sX f rfl p hgys c).cap g k α =
      chowPushforwardOfIso C (pullback.fst f (g ≫ f) ≫ (f ≫ sX))
        (pullback.fst (𝟙 Z) g ≫ (f ≫ sX))
        ((pullbackLeftPullbackSndIso f f g).inv ≫
          (transportPullbackIso (pullback.snd f f) (𝟙 Z) (asIso (pullback.snd f f))
            (by simp) g).hom)
        (closedImmersionRestrictionIso_base C sX f g) (k - p)
        (c.cap (g ≫ f) k (chowGroupCongr C (Category.assoc g f sX).symm k α)) := by
  have h1 : closedImmersionChowCohomologyRestriction C G (f ≫ sX) sX f rfl p hgys c =
      bivariantTransport C G (pullback.fst f f ≫ (f ≫ sX)) (f ≫ sX) (f ≫ sX)
        (pullback.snd f f) (pullbackSnd_comp_structureMorphism_eq C (f ≫ sX) sX f rfl f) (𝟙 Z)
        (Category.id_comp (f ≫ sX)) (asIso (pullback.snd f f)) (by simp) p hgys
        (bivariantRestriction C G (f ≫ sX) sX f rfl f p hgys c) := rfl
  rw [h1, bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestriction_cap,
    bivariantRestrictionCap_apply, chowPushforwardOfIso_comp_apply]

/-- **The third pairing of Stacks 0FA0 is the first pairing after the pushforward of Stacks
0EPK:** `res(c) ∘ c' = c ∘ f_*(c')`, for the restriction `res : A^i(Z ⟶ X) ⟶ A^i(Z)` of Stacks
0F9Z and the pushforward `f_* : A^j(Z ⟶ X) ⟶ A^j(X)` of Stacks 0EPK. This is the projection
formula the degrees at or above the cutoff of Stacks 0FA0 need: it rewrites a product of two
localized classes as a product of a localized class with a class on `X`, which is where the
associativity of Stacks 0B75 applies.

Both sides cap, on a test scheme `t`, by capping with `c'`, then capping with `c` at the test
morphism `Z ×_X T ⟶ X`, and pushing the result forward to `Z ×_X T`. On the left the
identification is the restriction's, on the right it is the base change of `f` the pushforward of
Stacks 0EPK pushes along, and the two agree because the cap operation of `c` is natural under
proper pushforward along that base change. -/
theorem localizedMulBivariant_eq_localizedMulBivariantChow (i j : ℤ)
    (x : BivariantClass C G (f ≫ sX) sX f rfl i)
    (y : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulBivariant C G sX f hgys hgysc i j x y =
      localizedMulBivariantChow C G sX f hgys hgysc i j x
        (localizedGradingPushforward C G sX f hRG hgysP hgysc j y) := by
  apply BivariantClass.ext
  intro T t ht k α
  have := isProper_baseChangeMapOfEq_pushforwardTestBaseChange f f t
  unfold localizedMulBivariant
  rw [localizedComposeChowCohomology_cap C G sX f hgys hgysc i j _ y t k α,
    closedImmersionChowCohomologyRestriction_cap_eq C G sX f hgys i x (pullback.fst f t) (k - j)
      (y.cap t k α),
    localizedMulBivariantChow_cap C G sX f hgys hgysc i j x _ t k α,
    localizedGradingPushforward_cap_eq C G sX f hRG hgysP hgysc j y t k α,
    x.proper_naturality_of_test_eq (pullback.fst (𝟙 X) t)
      ((pullback.congrHom (Category.comp_id f).symm rfl).hom ≫
        bivariantPushforwardBaseChange f (𝟙 X) t) (pullback.fst f t ≫ f)
      (pushforwardTestBaseChange_fst f t)
      (baseChangeMapOfEq f (pullback.fst (𝟙 X) t) _ _ (pushforwardTestBaseChange_fst f t))
      (isPullback_baseChangeMapOfEq f (pullback.fst (𝟙 X) t) _ _
        (pushforwardTestBaseChange_fst f t))
      (baseChangeMapOfEq_fst f (pullback.fst (𝟙 X) t) _ _
        (pushforwardTestBaseChange_fst f t)) (k - j)
      (pushforwardTestBaseChange_base C sX f t) (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) _]
  refine congrArg _ ?_
  refine (chowPushforwardOfIso_comm_properChowPushforward C _ _ _ _ _ _ _ _ ?_ _ _ _ _
    (k - j - i) _ _ _).symm
  refine pullback.hom_ext ?_ ?_
  · simp only [pullback.congrHom_hom, Category.assoc, pullbackMap_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, baseChangeMapOfEq_fst, transportPullbackIso_hom_fst,
      asIso_hom, pullbackLeftPullbackSndIso_inv_fst_snd]
    exact (cancel_mono f).1 (pullback.condition.trans (Category.assoc _ _ _).symm)
  · simp

/-- **The projection formula for the pushforward of Stacks 0EPK at the third pairing of
Stacks 0FA0:** `f_*(res(c) ∘ c') = f_*(c) · f_*(c')`. This is
`Stacks.Chow.localizedMulBivariant_eq_localizedMulBivariantChow` followed by the projection
formula at the first pairing. -/
theorem localizedGradingPushforward_localizedMulBivariant (i j : ℤ)
    (x : BivariantClass C G (f ≫ sX) sX f rfl i)
    (y : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedGradingPushforward C G sX f hRG hgysP hgysc (i + j)
        (localizedMulBivariant C G sX f hgys hgysc i j x y) =
      chowCohomologyComposite C G sX hgys hgysc i j
        (localizedGradingPushforward C G sX f hRG hgysP hgysc i x)
        (localizedGradingPushforward C G sX f hRG hgysP hgysc j y) := by
  rw [localizedMulBivariant_eq_localizedMulBivariantChow C G sX f hRG hgysP hgys hgysc i j x y,
    localizedGradingPushforward_localizedMulBivariantChow C G sX f hRG hgysP hgys hgysc i j x _]

/-- The pushforward of Stacks 0EPK, as a homomorphism of groups. -/
def localizedGradingPushforwardHom (i : ℤ) :
    BivariantClass C G (f ≫ sX) sX f rfl i →+ chowCohomologyComponent C G sX i :=
  AddMonoidHom.mk' (localizedGradingPushforward C G sX f hRG hgysP hgysc i)
    (localizedGradingPushforward_add C G sX f hRG hgysP hgysc i)

/-- The pushforward of Stacks 0EPK as a homomorphism is that pushforward. -/
@[simp]
theorem localizedGradingPushforwardHom_apply (i : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl i) :
    localizedGradingPushforwardHom C G sX f hRG hgysP hgysc i c =
      localizedGradingPushforward C G sX f hRG hgysP hgysc i c :=
  rfl

/-- The pushforward of Stacks 0EPK commutes with the transport along an equality of degrees. -/
theorem localizedGradingPushforward_bivariantClassDegreeCongr {i i' : ℤ} (h : i = i')
    (c : BivariantClass C G (f ≫ sX) sX f rfl i) :
    localizedGradingPushforward C G sX f hRG hgysP hgysc i'
        (bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl h c) =
      bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) h
        (localizedGradingPushforward C G sX f hRG hgysP hgysc i c) := by
  subst h
  rfl

/-- The pushforward of Stacks 0EPK is additive over a finite sum. -/
theorem localizedGradingPushforward_sum {ι : Type*} (s : Finset ι) (i : ℤ)
    (g : ι → BivariantClass C G (f ≫ sX) sX f rfl i) :
    localizedGradingPushforward C G sX f hRG hgysP hgysc i (∑ m ∈ s, g m) =
      ∑ m ∈ s, localizedGradingPushforward C G sX f hRG hgysP hgysc i (g m) :=
  map_sum (localizedGradingPushforwardHom C G sX f hRG hgysP hgysc i) g s

/-- **The three projection formulas, read on the `(i, n - i)` term of a product.** The pushforward
of Stacks 0EPK carries the term of the localized branch to the term of the ambient branch: each of
the three pairings of Stacks 0FA0 becomes the multiplication of `A^*(X)` of the two components read
in `A^*(X)`. -/
theorem localizedGradingPushforward_localizedGradingMulLocalizedTerm (p q r : ℕ)
    (hr : p + q ≤ r + 1) (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) (n : ℤ) (hn : (r : ℤ) ≤ n) (i : ℤ) :
    localizedGradingPushforward C G sX f hRG hgysP hgysc n
        (localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b n i) =
      localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b n i := by
  unfold localizedGradingMulLocalizedTerm localizedGradingMulAmbientTerm
    localizedGradingComponentOnAmbient
  by_cases hi : (p : ℤ) ≤ i
  · rw [dite_eq_left hi, dite_eq_left hi]
    by_cases hj : (q : ℤ) ≤ n - i
    · rw [dite_eq_left hj, dite_eq_left hj,
        localizedGradingPushforward_bivariantClassDegreeCongr C G sX f hRG hgysP hgysc _ _,
        localizedGradingPushforward_localizedMulBivariant C G sX f hRG hgysP hgys hgysc
          i (n - i) _ _]
    · rw [dite_eq_right hj, dite_eq_right hj,
        localizedGradingPushforward_bivariantClassDegreeCongr C G sX f hRG hgysP hgysc _ _,
        localizedGradingPushforward_localizedMulBivariantChow C G sX f hRG hgysP hgys hgysc
          i (n - i) _ _]
  · rw [dite_eq_right hi, dite_eq_right hi]
    by_cases hj : (q : ℤ) ≤ n - i
    · rw [dite_eq_left hj, dite_eq_left hj,
        localizedGradingPushforward_bivariantClassDegreeCongr C G sX f hRG hgysP hgysc _ _,
        localizedGradingPushforward_localizedMulChowBivariant C G sX f hRG hgysP hgys hgysc
          i (n - i) _ _]
    · exact absurd hn (by omega)

/-- **The multiplication of Stacks 0FA0 is the convolution the source prescribes, read in
`A^*(X)` by Stacks 0EPK — in every degree, not only below the cutoff of the target.** Equivalently:
the product at the target `A⁽ʳ⁾(Z ⟶ X)` refines the product at the target `A⁽ᵖ⁺ᑫ⁾(Z ⟶ X)` at which
Stacks 0FAL and Stacks 0FAY state the chapter's products, the comparison being degreewise the
pushforward of Stacks 0EPK.

Below the cutoff this is the definition of the product
(`Stacks.Chow.localizedGradingComponentOnAmbient_localizedBivariantGradingMul_of_lt`); from the
cutoff on it is the three projection formulas for the pushforward of Stacks 0EPK, term by term.
Note that `Stacks.Chow.exists_pushforward_eq_chowCohomologyComposite_of_isAmbientConvolution` draws
from this same property, *at a target where the remark leaves a pair of degrees unprescribed*, a
section of the Stacks 0EPK pushforward on a pair of ambient classes; here `p + q ≤ r + 1`, so there
is no such pair of ambient degrees for that conclusion to be about. -/
theorem localizedBivariantGradingMul_isAmbientConvolution (p q r : ℕ) (hr : p + q ≤ r + 1) :
    LocalizedGrading.IsAmbientConvolution C G sX f hRG hgysP hgys hgysc p q r
      (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r) := by
  intro a b n
  by_cases hn : (r : ℤ) ≤ n
  · have h1 : localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc r
        (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b) n =
        localizedGradingPushforward C G sX f hRG hgysP hgysc n
          ((localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b).2
            ⟨n, hn⟩) := by
      unfold localizedGradingComponentOnAmbient
      rw [dite_eq_left hn]
    rw [h1, localizedBivariantGradingMul_snd C G sX f hRG hgysP hgys hgysc p q r a b ⟨n, hn⟩,
      localizedGradingPushforward_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      localizedGradingPushforward_localizedGradingMulLocalizedTerm C G sX f hRG hgysP hgys hgysc
        p q r hr a b n hn i
  · exact localizedGradingComponentOnAmbient_localizedBivariantGradingMul_of_lt C G sX f hRG
      hgysP hgys hgysc p q r a b n (not_le.1 hn)

end Pushforward

end Stacks.Chow

end
