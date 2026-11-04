module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.ProperModification
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ZeroSchemeCartesianSquare
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.BaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem

/-!
# The class at infinity under a proper morphism of divisor data

Let `(S, δ)` be as in chapter 42 of the Stacks Project and let `h : X' ⟶ X` be a morphism of
schemes locally of finite type over `S`. Let `(π : W ⟶ X, j : U ⟶ W, L, s)` be the data of the
general construction of Stacks 0F9J over `X` (`Stacks.Chow.GysinAtInfinity.infinityClass`), and let
`(π' : W' ⟶ X', j' : U' ⟶ W', φ^*L, φ^*s)` be such data over `X'`, where `φ : W' ⟶ W` lies over
`h`, the open `U'` is the inverse image of `U`, and over every test scheme `g : T ⟶ X'` the base
change `φ_T : W' ×_{X'} T ⟶ W ×_X T` is proper and an isomorphism over the opens.

Then pushing the cap with the class at infinity of the primed data forward along the map of the
divisors gives the cap with the class at infinity of the unprimed data:

  `φ_{∞,T,*}(C' ∩ α) = C ∩ α`  for  `α ∈ A_k(T)`.

The proof is the one of Stacks 0FAQ: the pushforward of a lift of `α` on `W'_T` is a lift on `W_T`,
because flat pullback commutes with pushforward along the isomorphism over the opens (Stacks 02RG),
and Stacks 02TA carries the Gysin map of the divisor of `W_T` through the pushforward.

## Main results

* `Stacks.Chow.GysinAtInfinity.isLift_testMapOver` — lifts push forward to lifts.
* `Stacks.Chow.GysinAtInfinity.properChowPushforward_infinityCap` — `φ_{∞,T,*}(C' ∩ α) = C ∩ α`.

## References

* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

section Over

variable (C : ChowSituation.{u}) {X X' W W' U U' : Scheme.{u}} (f : X ⟶ C.S) (h : X' ⟶ X)
  (π : W ⟶ X) (j : U ⟶ W) (π' : W' ⟶ X') (j' : U' ⟶ W')
  (φ : W' ⟶ W) (hφ : φ ≫ π = π' ≫ h) (e : U' ⟶ U) (he : e ≫ j = j' ≫ φ)

/-- The base change `φ_T : W' ×_{X'} T ⟶ W ×_X T` of `φ` to a test scheme `g : T ⟶ X'`. -/
abbrev testMapOver {T : Scheme.{u}} (g : T ⟶ X') : pullback π' g ⟶ pullback π (g ≫ h) :=
  pullback.map π' g π (g ≫ h) φ (𝟙 T) h hφ.symm (by simp)

include he hφ in
/-- The two composites `U' ⟶ X` agree: `j' ≫ π' ≫ h = e ≫ j ≫ π`. -/
theorem openMapOver_eq : (j' ≫ π') ≫ h = e ≫ (j ≫ π) := by
  rw [Category.assoc, ← hφ, ← Category.assoc, ← he, Category.assoc]

/-- The base change `U' ×_{X'} T ⟶ U ×_X T` of `e` to a test scheme `g : T ⟶ X'`. -/
abbrev openMapOver {T : Scheme.{u}} (g : T ⟶ X') :
    pullback (j' ≫ π') g ⟶ pullback (j ≫ π) (g ≫ h) :=
  pullback.map (j' ≫ π') g (j ≫ π) (g ≫ h) e (𝟙 T) h (openMapOver_eq h π j π' j' φ hφ e he)
    (by simp)

/-- The map `φ_T` lies over the structure morphisms of `W' ×_{X'} T` and `W ×_X T`. -/
theorem testMapOver_comp_testStr {T : Scheme.{u}} (g : T ⟶ X') :
    testMapOver h π π' φ hφ g ≫ testStr C f π (g ≫ h) = testStr C (h ≫ f) π' g := by
  simp only [testStr, testMapOver, pullback.lift_fst_assoc]
  rw [Category.assoc, reassoc_of% hφ]

/-- The map `U' ×_{X'} T ⟶ U ×_X T` lies over the structure morphisms to `S`. -/
theorem openMapOver_comp_openStr {T : Scheme.{u}} (g : T ⟶ X') :
    openMapOver h π j π' j' φ hφ e he g ≫ openStr C f π j (g ≫ h) = openStr C (h ≫ f) π' j' g := by
  simp only [openStr, openMapOver, pullback.lift_snd_assoc, Category.comp_id, Category.assoc]

/-- The map `U' ×_{X'} T ⟶ U ×_X T` commutes with the projections to `T`. -/
theorem openMapOver_snd {T : Scheme.{u}} (g : T ⟶ X') :
    openMapOver h π j π' j' φ hφ e he g ≫ pullback.snd (j ≫ π) (g ≫ h) =
      pullback.snd (j' ≫ π') g := by
  simp

/-- The map `W ×_X T ⟶ W ×_X X'` induced by a test scheme `g : T ⟶ X'`. -/
abbrev pullbackTestMap {T : Scheme.{u}} (g : T ⟶ X') : pullback π (g ≫ h) ⟶ pullback π h :=
  pullback.lift (pullback.fst π (g ≫ h)) (pullback.snd π (g ≫ h) ≫ g)
    (by rw [pullback.condition, Category.assoc])

/-- The square formed by `W ×_X T ⟶ W ×_X X'` and the projections to `T` and `X'` is cartesian. -/
theorem isPullback_pullbackTestMap {T : Scheme.{u}} (g : T ⟶ X') :
    IsPullback (pullbackTestMap h π g) (pullback.snd π (g ≫ h)) (pullback.snd π h) g := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback π h)
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback π (g ≫ h)

/-- **The base change of `φ` to a test scheme is a base change of `W' ⟶ W ×_X X'`.** -/
theorem isPullback_testMapOver {T : Scheme.{u}} (g : T ⟶ X') :
    IsPullback (pullback.fst π' g) (testMapOver h π π' φ hφ g) (pullback.lift φ π' hφ)
      (pullbackTestMap h π g) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_pullbackTestMap h π g)
  · rw [pullback.lift_snd, pullback.lift_snd, Category.comp_id]
    exact IsPullback.of_hasPullback π' g
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
      exact pullback.condition

include he in
/-- **The open of the base change is the base change of the open**, when `U'` is the inverse
image of `U`. -/
theorem isPullback_openMapOver (hUU : IsPullback j' e φ j) {T : Scheme.{u}} (g : T ⟶ X') :
    IsPullback (openBaseChange π' j' g) (openMapOver h π j π' j' φ hφ e he g)
      (testMapOver h π π' φ hφ g) (openBaseChange π j (g ≫ h)) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_openBaseChange π j (g ≫ h)).flip
  · rw [pullback.lift_fst, pullback.lift_fst]
    exact (isPullback_openBaseChange π' j' g).flip.paste_vert hUU
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [he]
    · simp

variable [LocallyOfFiniteType f] [LocallyOfFiniteType h] [LocallyOfFiniteType π]
  [IsOpenImmersion j] [Flat (j ≫ π)] (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1)
  [LocallyOfFiniteType π'] [IsOpenImmersion j'] [Flat (j' ≫ π')]
  (hU' : AlgebraicGeometry.RelativeDimension (j' ≫ π') 1)

variable {T : Scheme.{u}} (g : T ⟶ X') [LocallyOfFiniteType g]
  [IsProper (testMapOver h π π' φ hφ g)] [IsIso (openMapOver h π j π' j' φ hφ e he g)]
  (hsq : IsPullback (openBaseChange π' j' g) (openMapOver h π j π' j' φ hφ e he g)
    (testMapOver h π π' φ hφ g) (openBaseChange π j (g ≫ h)))

/-- The class `α ∈ A_k(T)` read for the structure morphism of `T` through `X`. -/
abbrev testClass {k : ℤ} (α : chowGroup C (g ≫ (h ≫ f)) k) : chowGroup C ((g ≫ h) ≫ f) k :=
  chowPushforwardOfIso C (g ≫ (h ≫ f)) ((g ≫ h) ≫ f) (𝟙 T) (by simp) k α

include hsq in
/-- **Lifts push forward to lifts.** If `β' ∈ A_{k+1}(W'_T)` restricts over `U'_T` to the flat
pullback of `α`, then `φ_{T,*} β'` restricts over `U_T` to the flat pullback of `α`. -/
theorem isLift_testMapOver {k : ℤ} {α : chowGroup C (g ≫ (h ≫ f)) k}
    {β' : chowGroup C (testStr C (h ≫ f) π' g) (k + 1)}
    (hβ' : IsLift C (h ≫ f) π' j' hU' g k α β') :
    IsLift C f π j hU (g ≫ h) k (testClass C f h g α)
      (properChowPushforward C (testStr C (h ≫ f) π' g) (testStr C f π (g ≫ h))
        (testMapOver h π π' φ hφ g) (testMapOver_comp_testStr C f h π π' φ hφ g) (k + 1)
        (properPushforwardDescends C _ _ _ _ _) β') := by
  have := isOpenImmersion_openBaseChange π j (g ≫ h)
  have := isOpenImmersion_openBaseChange π' j' g
  unfold IsLift at hβ' ⊢
  rw [chowGroupRestrict_properChowPushforward C
    (testStr C (h ≫ f) π' g) (testStr C f π (g ≫ h))
    (openStr C (h ≫ f) π' j' g) (openStr C f π j (g ≫ h)) (testMapOver h π π' φ hφ g)
    (testMapOver_comp_testStr C f h π π' φ hφ g)
    (openBaseChange π' j' g) (openBaseChange_comp_testStr C (h ≫ f) π' j' g)
    (openBaseChange π j (g ≫ h)) (openBaseChange_comp_testStr C f π j (g ≫ h))
    (openMapOver h π j π' j' φ hφ e he g) (openMapOver_comp_openStr C f h π j π' j' φ hφ e he g)
    hsq (k + 1) (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) β',
    hβ']
  have hcomm := flatPullbackChow_chowPushforwardOfIso C (g ≫ (h ≫ f))
    (openStr C (h ≫ f) π' j' g) ((g ≫ h) ≫ f) (openStr C f π j (g ≫ h)) (𝟙 T) (by simp)
    (openMapOver h π j π' j' φ hφ e he g) (openMapOver_comp_openStr C f h π j π' j' φ hφ e he g)
    (pullback.snd (j' ≫ π') g) rfl (pullback.snd (j ≫ π) (g ≫ h)) rfl
    (by rw [Category.comp_id, openMapOver_snd]) 1
    (relativeDimension_openSnd π' j' hU' g) (relativeDimension_openSnd π j hU (g ≫ h)) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α
  exact hcomm.symm

end Over

section Formula

variable (C : ChowSituation.{u}) {X W U : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (π : W ⟶ X) [LocallyOfFiniteType π] (j : U ⟶ W) [IsOpenImmersion j] [Flat (j ≫ π)]
  (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1) (L : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (hcompl : Set.range (Stacks.Divisors.zeroScheme W L s).subschemeι.base = (Set.range j.base)ᶜ)
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme W L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme W L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W L s).subschemeι).obj L))
  {T : Scheme.{u}} (g : T ⟶ X)

/-- The identification of the zero scheme of the pulled-back section on `W ×_X T` with
`Z(s) ×_X T`. -/
def testDivisorIso :
    (gysinTripleDivisor L s (pullback.fst π g)).subscheme ⟶
      pullback (gysinTripleInclusion L s ≫ π) g :=
  (gysinDivisorBaseChangeIso L s (pullback.fst π g)).hom ≫
    (pullbackRightPullbackFstIso π g (gysinTripleInclusion L s)).hom

/-- The map `testDivisorIso` is an isomorphism. -/
instance isIso_testDivisorIso : IsIso (testDivisorIso π L s g) := by
  unfold testDivisorIso
  infer_instance

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] in
/-- The map `testDivisorIso` lies over the structure morphisms to `S`. -/
theorem testDivisorIso_comp_structure :
    testDivisorIso π L s g ≫ (pullback.fst (gysinTripleInclusion L s ≫ π) g ≫
        (gysinTripleInclusion L s ≫ (π ≫ f))) =
      (gysinTripleDivisor L s (pullback.fst π g)).subschemeι ≫ testStr C f π g := by
  rw [testDivisorIso, Category.assoc, pullbackRightPullbackFstIso_hom_comp_fst_comp,
    gysinDivisorBaseChangeIso_hom_comp_structureMorphism]

omit [LocallyOfFiniteType π] in
/-- The map `testDivisorIso` commutes with the maps to `W`. -/
theorem testDivisorIso_fst :
    testDivisorIso π L s g ≫ pullback.fst (gysinTripleInclusion L s ≫ π) g ≫
        gysinTripleInclusion L s =
      (gysinTripleDivisor L s (pullback.fst π g)).subschemeι ≫ pullback.fst π g := by
  rw [testDivisorIso, Category.assoc, pullbackRightPullbackFstIso_hom_fst_assoc,
    gysinDivisorBaseChangeIso_hom_comp_test]

omit [LocallyOfFiniteType π] in
/-- The map `testDivisorIso` commutes with the projections to `T`. -/
theorem testDivisorIso_snd :
    testDivisorIso π L s g ≫ pullback.snd (gysinTripleInclusion L s ≫ π) g =
      (gysinTripleDivisor L s (pullback.fst π g)).subschemeι ≫ pullback.snd π g := by
  rw [testDivisorIso, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    gysinDivisorBaseChangeIso_hom_snd_assoc]

/-- The closed immersion `Z(s) ×_X T ⟶ W ×_X T`. -/
abbrev testDivisorIncl : pullback (gysinTripleInclusion L s ≫ π) g ⟶ pullback π g :=
  pullback.map _ _ _ _ (gysinTripleInclusion L s) (𝟙 T) (𝟙 X) (by simp) (by simp)

/-- The map `Z(s) ×_X T ⟶ W ×_X T` is a closed immersion. -/
instance isClosedImmersion_testDivisorIncl : IsClosedImmersion (testDivisorIncl π L s g) := by
  have : IsPullback (pullback.fst (gysinTripleInclusion L s ≫ π) g) (testDivisorIncl π L s g)
      (gysinTripleInclusion L s) (pullback.fst π g) := by
    refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback π g)
    simpa using IsPullback.of_hasPullback (gysinTripleInclusion L s ≫ π) g
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) this inferInstance

omit [LocallyOfFiniteType π] in
/-- Composing `testDivisorIso` with `Z(s) ×_X T ⟶ W ×_X T` gives the inclusion of the pulled-back
divisor. -/
theorem testDivisorIso_comp_incl :
    testDivisorIso π L s g ≫ testDivisorIncl π L s g =
      (gysinTripleDivisor L s (pullback.fst π g)).subschemeι := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, Category.assoc, testDivisorIso_fst]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, testDivisorIso_snd]

variable [LocallyOfFiniteType g]

/-- **The cap with the class at infinity, through a lift**: `C ∩ α` is the Gysin map of the
pulled-back divisor applied to any lift `β` of `α`, read on `Z(s) ×_X T`. -/
theorem infinityCap_eq_onChow {k : ℤ} {α : chowGroup C (g ≫ f) k}
    {β : chowGroup C (testStr C f π g) (k + 1)} (hβ : IsLift C f π j hU g k α β) :
    infinityCap C f π j hU L s hcompl htriv g k α =
      chowGroupDegreeEquiv C _ (sub_zero k).symm
        (chowPushforwardOfIso C ((gysinTripleDivisor L s (pullback.fst π g)).subschemeι ≫
            testStr C f π g)
          (pullback.fst (gysinTripleInclusion L s ≫ π) g ≫ (gysinTripleInclusion L s ≫ (π ≫ f)))
          (testDivisorIso π L s g) (testDivisorIso_comp_structure C f π L s g) k
          ((gysinSystemOfInvertible C).onChow (testStr C f π g)
            (gysinTripleModule L (pullback.fst π g)) (gysinTripleSection L s (pullback.fst π g))
            k β)) := by
  rw [infinityCap_eq_of_isLift C f π j hU L s hcompl htriv hβ, divisorMiddleCap, middleCap_apply,
    (gysinBivariantClass C (π ≫ f) L s).2, gysinBivariantCap_apply]
  apply eq_of_heq
  refine HEq.trans (chowGroupDegreeEquiv_heq C _ _ _) ?_
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm
  rw [← properChowPushforward_eq_chowPushforwardOfIso C _ _ _ _ _
      (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_comp_apply C _ _ _ _ _ (testDivisorIso π L s g) rfl _ _
      (testDivisorIso_comp_structure C f π L s g) _ (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
  exact heq_map_index (α := fun n ↦ chowGroup C (testStr C f π g) (n + 1))
    (β := fun n ↦ chowGroup C (pullback.fst (gysinTripleInclusion L s ≫ π) g ≫
      (gysinTripleInclusion L s ≫ (π ≫ f))) n) (by ring : k + 1 - 1 = k)
    (chowGroupDegreeEquiv_heq C _ _ _) fun n y ↦
      properChowPushforward C _ _ (testDivisorIso π L s g)
        (testDivisorIso_comp_structure C f π L s g) n (properPushforwardDescends C _ _ _ _ _)
        ((gysinSystemOfInvertible C).onChow (testStr C f π g)
          (gysinTripleModule L (pullback.fst π g)) (gysinTripleSection L s (pullback.fst π g))
          n y)

end Formula

section Main

/-- Transport along an equal pair of ideal sheaves is compatible with a map to `C.S`. -/
private theorem eqToHom_subschemeι_comp_structure (C : ChowSituation.{u}) {Y : Scheme.{u}}
    {I J : Y.IdealSheafData} (hIJ : I = J) (q : Y ⟶ C.S) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme hIJ) ≫ (J.subschemeι ≫ q) =
      I.subschemeι ≫ q := by
  rw [← Category.assoc, Stacks.Chow.subschemeι_eqToHom hIJ]

variable (C : ChowSituation.{u}) {X X' W W' U U' : Scheme.{u}} (f : X ⟶ C.S) (h : X' ⟶ X)
  (π : W ⟶ X) (j : U ⟶ W) (π' : W' ⟶ X') (j' : U' ⟶ W')
  (φ : W' ⟶ W) (hφ : φ ≫ π = π' ≫ h) (e : U' ⟶ U) (he : e ≫ j = j' ≫ φ)
  (L : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) [LocallyOfFiniteType π] [LocallyOfFiniteType π']

omit [LocallyOfFiniteType π] [LocallyOfFiniteType π'] in
include hφ in
/-- The two composites `Z(φ^*s) ⟶ X` agree. -/
theorem infinityMapOver_eq :
    (gysinTripleInclusion ((Scheme.Modules.pullback φ).obj L)
        (AlgebraicGeometry.pullbackGlobalSections φ L s) ≫ π') ≫ h =
      zeroSchemePullbackHom φ L s ≫ (gysinTripleInclusion L s ≫ π) := by
  rw [← Category.assoc, zeroSchemePullbackHom_subschemeι, Category.assoc, Category.assoc, hφ]

/-- The base change `Z(φ^*s) ×_{X'} T ⟶ Z(s) ×_X T` of the map of divisors to a test scheme
`g : T ⟶ X'`. -/
abbrev infinityMapOver {T : Scheme.{u}} (g : T ⟶ X') :
    pullback (gysinTripleInclusion ((Scheme.Modules.pullback φ).obj L)
        (AlgebraicGeometry.pullbackGlobalSections φ L s) ≫ π') g ⟶
      pullback (gysinTripleInclusion L s ≫ π) (g ≫ h) :=
  pullback.map _ g _ (g ≫ h) (zeroSchemePullbackHom φ L s) (𝟙 T) h
    (infinityMapOver_eq h π π' φ hφ L s) (by simp)

omit [LocallyOfFiniteType π] [LocallyOfFiniteType π'] in
/-- The map `Z(φ^*s) ×_{X'} T ⟶ Z(s) ×_X T` lies over the structure morphisms to `S`. -/
theorem infinityMapOver_comp_structure {T : Scheme.{u}} (g : T ⟶ X') :
    infinityMapOver h π π' φ hφ L s g ≫
        (pullback.fst (gysinTripleInclusion L s ≫ π) (g ≫ h) ≫
          (gysinTripleInclusion L s ≫ (π ≫ f))) =
      pullback.fst (gysinTripleInclusion ((Scheme.Modules.pullback φ).obj L)
          (AlgebraicGeometry.pullbackGlobalSections φ L s) ≫ π') g ≫
        (gysinTripleInclusion ((Scheme.Modules.pullback φ).obj L)
          (AlgebraicGeometry.pullbackGlobalSections φ L s) ≫ (π' ≫ (h ≫ f))) := by
  rw [pullback.lift_fst_assoc, Category.assoc, ← Category.assoc (gysinTripleInclusion L s),
    ← Category.assoc (zeroSchemePullbackHom φ L s), ← infinityMapOver_eq h π π' φ hφ L s]
  simp only [Category.assoc]

omit [LocallyOfFiniteType π] [LocallyOfFiniteType π'] in
/-- The map `Z(φ^*s) ×_{X'} T ⟶ Z(s) ×_X T` commutes with the inclusions into `W' ×_{X'} T` and
`W ×_X T` and the map `φ_T`. -/
theorem infinityMapOver_comp_incl {T : Scheme.{u}} (g : T ⟶ X') :
    infinityMapOver h π π' φ hφ L s g ≫ testDivisorIncl π L s (g ≫ h) =
      testDivisorIncl π' ((Scheme.Modules.pullback φ).obj L)
        (AlgebraicGeometry.pullbackGlobalSections φ L s) g ≫ testMapOver h π π' φ hφ g := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact congrArg (fun q => pullback.fst _ g ≫ q) (zeroSchemePullbackHom_subschemeι φ L s)
  · simp

omit [LocallyOfFiniteType π] [LocallyOfFiniteType π'] in
/-- The map of zero schemes induced by `φ_T`, read on `Z(s) ×_X T`. -/
theorem zeroSchemePullbackHom_testDivisorIso {T : Scheme.{u}} (g : T ⟶ X')
    (E : Stacks.Divisors.zeroScheme (pullback π' g)
        ((Scheme.Modules.pullback (testMapOver h π π' φ hφ g)).obj
          (gysinTripleModule L (pullback.fst π (g ≫ h))))
        (AlgebraicGeometry.pullbackGlobalSections (testMapOver h π π' φ hφ g)
          (gysinTripleModule L (pullback.fst π (g ≫ h)))
          (gysinTripleSection L s (pullback.fst π (g ≫ h)))) =
      gysinTripleDivisor ((Scheme.Modules.pullback φ).obj L)
        (AlgebraicGeometry.pullbackGlobalSections φ L s) (pullback.fst π' g)) :
    zeroSchemePullbackHom (testMapOver h π π' φ hφ g)
        (gysinTripleModule L (pullback.fst π (g ≫ h)))
        (gysinTripleSection L s (pullback.fst π (g ≫ h))) ≫ testDivisorIso π L s (g ≫ h) =
      eqToHom (congrArg Scheme.IdealSheafData.subscheme E) ≫
        testDivisorIso π' ((Scheme.Modules.pullback φ).obj L)
          (AlgebraicGeometry.pullbackGlobalSections φ L s) g ≫
        infinityMapOver h π π' φ hφ L s g := by
  refine (cancel_mono (testDivisorIncl π L s (g ≫ h))).1 ?_
  rw [Category.assoc, testDivisorIso_comp_incl, zeroSchemePullbackHom_subschemeι, Category.assoc,
    Category.assoc, infinityMapOver_comp_incl, ← Category.assoc (testDivisorIso _ _ _ g),
    testDivisorIso_comp_incl, ← Category.assoc, Stacks.Chow.subschemeι_eqToHom E]

/-- If `φ_T` is proper, then so is `Z(φ^*s) ×_{X'} T ⟶ Z(s) ×_X T`. -/
instance isProper_infinityMapOver {T : Scheme.{u}} (g : T ⟶ X')
    [IsProper (testMapOver h π π' φ hφ g)] :
    IsProper (infinityMapOver h π π' φ hφ L s g) := by
  have : IsProper (infinityMapOver h π π' φ hφ L s g ≫ testDivisorIncl π L s (g ≫ h)) := by
    rw [infinityMapOver_comp_incl]
    infer_instance
  exact IsProper.of_comp _ (testDivisorIncl π L s (g ≫ h))

end Main

section Pushforward

variable (C : ChowSituation.{u}) {X X' W W' U U' : Scheme.{u}} (f : X ⟶ C.S) (h : X' ⟶ X)
  (π : W ⟶ X) (j : U ⟶ W) (π' : W' ⟶ X') (j' : U' ⟶ W')
  (φ : W' ⟶ W) (hφ : φ ≫ π = π' ≫ h) (e : U' ⟶ U) (he : e ≫ j = j' ≫ φ)
  (L : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  [LocallyOfFiniteType f] [LocallyOfFiniteType h] [LocallyOfFiniteType π]
  [IsOpenImmersion j] [Flat (j ≫ π)] (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1)
  [LocallyOfFiniteType π'] [IsOpenImmersion j'] [Flat (j' ≫ π')]
  (hU' : AlgebraicGeometry.RelativeDimension (j' ≫ π') 1)
  (hcompl : Set.range (Stacks.Divisors.zeroScheme W L s).subschemeι.base = (Set.range j.base)ᶜ)
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme W L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme W L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W L s).subschemeι).obj L))
  (hcompl' : Set.range (pullbackZeroScheme φ L s).subschemeι.base = (Set.range j'.base)ᶜ)
  (htriv' : AlgebraicGeometry.SheafOfModules.IsTrivial
    (pullbackZeroScheme φ L s).subscheme.sheaf.obj
    (pullbackZeroScheme φ L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (pullbackZeroScheme φ L s).subschemeι).obj
      ((Scheme.Modules.pullback φ).obj L)))
  {T : Scheme.{u}} (g : T ⟶ X') [LocallyOfFiniteType g]
  [IsProper (testMapOver h π π' φ hφ g)] [IsIso (openMapOver h π j π' j' φ hφ e he g)]
  (hsq : IsPullback (openBaseChange π' j' g) (openMapOver h π j π' j' φ hφ e he g)
    (testMapOver h π π' φ hφ g) (openBaseChange π j (g ≫ h)))

include hsq in
/-- **The class at infinity under a proper morphism of divisor data**: for `α ∈ A_k(T)`, pushing
`C' ∩ α` forward along `Z(φ^*s) ×_{X'} T ⟶ Z(s) ×_X T` gives `C ∩ α`. -/
theorem properChowPushforward_infinityCap (k : ℤ) (α : chowGroup C (g ≫ (h ≫ f)) k) :
    properChowPushforward C _ _ (infinityMapOver h π π' φ hφ L s g)
        (infinityMapOver_comp_structure C f h π π' φ hφ L s g) (k - 0)
        (properPushforwardDescends C _ _ _ _ _)
        (infinityCap C (h ≫ f) π' j' hU' ((Scheme.Modules.pullback φ).obj L)
          (AlgebraicGeometry.pullbackGlobalSections φ L s) hcompl' htriv' g k α) =
      infinityCap C f π j hU L s hcompl htriv (g ≫ h) k (testClass C f h g α) := by
  obtain ⟨β', hβ'⟩ := exists_isLift C (h ≫ f) π' j' hU' g k α
  have hβ := isLift_testMapOver C f h π j π' j' φ hφ e he hU hU' g hsq hβ'
  have h2 := infinityCap_eq_onChow C f π j hU L s hcompl htriv (g ≫ h) hβ
  have h1 := @infinityCap_eq_onChow C X' W' U' (h ≫ f) _ π' _ j' _ _ hU'
    ((Scheme.Modules.pullback φ).obj L) _ (AlgebraicGeometry.pullbackGlobalSections φ L s)
    hcompl' htriv' T g _ k α β' hβ'
  rw [h2]
  refine (congrArg (properChowPushforward C _ _ (infinityMapOver h π π' φ hφ L s g)
    (infinityMapOver_comp_structure C f h π π' φ hφ L s g) (k - 0)
    (properPushforwardDescends C _ _ _ _ _)) h1).trans ?_
  refine (properChowPushforward_chowGroupDegreeEquiv_eq C _ _ _ _ (sub_zero k).symm
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _).trans ?_
  refine congrArg (chowGroupDegreeEquiv C _ (sub_zero k).symm) ?_
  have hcomp : testMapOver h π π' φ hφ g ≫ pullback.fst π (g ≫ h) = pullback.fst π' g ≫ φ :=
    pullback.lift_fst _ _ _
  have : IsProper (zeroSchemePullbackHom (testMapOver h π π' φ hφ g)
      (gysinTripleModule L (pullback.fst π (g ≫ h)))
      (gysinTripleSection L s (pullback.fst π (g ≫ h)))) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (isPullback_zeroSchemePullbackHom (testMapOver h π π' φ hφ g)
        (gysinTripleModule L (pullback.fst π (g ≫ h)))
        (gysinTripleSection L s (pullback.fst π (g ≫ h)))) inferInstance
  have h3 := gysinSystemOfInvertible_isNaturalUnderProperPushforward C (testStr C (h ≫ f) π' g)
    (testStr C f π (g ≫ h)) (testMapOver h π π' φ hφ g) (testMapOver_comp_testStr C f h π π' φ hφ g)
    (gysinTripleModule L (pullback.fst π (g ≫ h)))
    (gysinTripleSection L s (pullback.fst π (g ≫ h))) k
    (zeroSchemePullbackHom (testMapOver h π π' φ hφ g)
      (gysinTripleModule L (pullback.fst π (g ≫ h)))
      (gysinTripleSection L s (pullback.fst π (g ≫ h))))
    (zeroSchemePullbackHom_subschemeι _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) β'
  refine Eq.trans ?_ (congrArg (chowPushforwardOfIso C _ _ (testDivisorIso π L s (g ≫ h))
    (testDivisorIso_comp_structure C f π L s (g ≫ h)) k) h3).symm
  have hH := (onChow_pullbackComp_heq C (testStr C (h ≫ f) π' g) L s k β'
      (testMapOver h π π' φ hφ g) (pullback.fst π (g ≫ h))).trans
    ((onChow_pullback_heq C (testStr C (h ≫ f) π' g) L s k β' hcomp).trans
      (onChow_pullbackComp_heq C (testStr C (h ≫ f) π' g) L s k β' (pullback.fst π' g) φ).symm)
  have E := Stacks.Divisors.zeroScheme_pullback_comp_comp (testMapOver h π π' φ hφ g)
    (pullback.fst π (g ≫ h)) (pullback.fst π' g) φ hcomp L s
  have h4 := chowPushforwardOfIso_eqToHom_eq_of_heq C (testStr C (h ≫ f) π' g) k E
    (eqToHom_subschemeι_comp_structure C E _) hH
  refine Eq.trans (congrArg (fun y => properChowPushforward C _ _
    (infinityMapOver h π π' φ hφ L s g) (infinityMapOver_comp_structure C f h π π' φ hφ L s g) k
    (properPushforwardDescends C _ _ _ _ _)
    (chowPushforwardOfIso C _ _ (testDivisorIso π' ((Scheme.Modules.pullback φ).obj L)
        (AlgebraicGeometry.pullbackGlobalSections φ L s) g)
      (testDivisorIso_comp_structure C (h ≫ f) π' ((Scheme.Modules.pullback φ).obj L)
        (AlgebraicGeometry.pullbackGlobalSections φ L s) g) k y)) h4.symm) ?_
  have key := properChowPushforward_comp_eq_comp₃ C
    ((pullbackZeroScheme (testMapOver h π π' φ hφ g) (gysinTripleModule L (pullback.fst π (g ≫ h)))
      (gysinTripleSection L s (pullback.fst π (g ≫ h)))).subschemeι ≫ testStr C (h ≫ f) π' g)
    ((gysinTripleDivisor L s (pullback.fst π (g ≫ h))).subschemeι ≫ testStr C f π (g ≫ h))
    ((gysinTripleDivisor ((Scheme.Modules.pullback φ).obj L)
      (AlgebraicGeometry.pullbackGlobalSections φ L s) (pullback.fst π' g)).subschemeι ≫
        testStr C (h ≫ f) π' g)
    (pullback.fst (gysinTripleInclusion ((Scheme.Modules.pullback φ).obj L)
        (AlgebraicGeometry.pullbackGlobalSections φ L s) ≫ π') g ≫
      (gysinTripleInclusion ((Scheme.Modules.pullback φ).obj L)
        (AlgebraicGeometry.pullbackGlobalSections φ L s) ≫ (π' ≫ (h ≫ f))))
    (pullback.fst (gysinTripleInclusion L s ≫ π) (g ≫ h) ≫ (gysinTripleInclusion L s ≫ (π ≫ f)))
    (zeroSchemePullbackHom (testMapOver h π π' φ hφ g)
      (gysinTripleModule L (pullback.fst π (g ≫ h)))
      (gysinTripleSection L s (pullback.fst π (g ≫ h))))
    (testDivisorIso π L s (g ≫ h)) (eqToHom (congrArg Scheme.IdealSheafData.subscheme E))
    (testDivisorIso π' ((Scheme.Modules.pullback φ).obj L)
      (AlgebraicGeometry.pullbackGlobalSections φ L s) g)
    (infinityMapOver h π π' φ hφ L s g)
    (zeroSchemePullbackHom_testDivisorIso h π π' φ hφ L s g E)
    (zeroSchemeSquare_comp_structureMorphism C _ _ (testMapOver h π π' φ hφ g)
      (testMapOver_comp_testStr C f h π π' φ hφ g) _ _ _ (zeroSchemePullbackHom_subschemeι _ _ _))
    (testDivisorIso_comp_structure C f π L s (g ≫ h))
    (eqToHom_subschemeι_comp_structure C E _)
    (testDivisorIso_comp_structure C (h ≫ f) π' ((Scheme.Modules.pullback φ).obj L)
      (AlgebraicGeometry.pullbackGlobalSections φ L s) g)
    (infinityMapOver_comp_structure C f h π π' φ hφ L s g) k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)
    ((gysinSystemOfInvertible C).onChow (testStr C (h ≫ f) π' g)
      ((Scheme.Modules.pullback (testMapOver h π π' φ hφ g)).obj
        (gysinTripleModule L (pullback.fst π (g ≫ h))))
      (AlgebraicGeometry.pullbackGlobalSections (testMapOver h π π' φ hφ g)
        (gysinTripleModule L (pullback.fst π (g ≫ h)))
        (gysinTripleSection L s (pullback.fst π (g ≫ h)))) k β')
  exact key.symm

end Pushforward

section Change

variable (C : ChowSituation.{u}) {X W U : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (π : W ⟶ X) [LocallyOfFiniteType π] (j : U ⟶ W) [IsOpenImmersion j] [Flat (j ≫ π)]
  (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1) (L L₂ : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L₂]
  (s : Γ(L, ⊤)) (s₂ : Γ(L₂, ⊤))
  (hz : Stacks.Divisors.zeroScheme W L s = Stacks.Divisors.zeroScheme W L₂ s₂)

omit [LocallyOfFiniteType π] in
/-- For `Z(s) = Z(s₂)`, the maps `Z(s) ⟶ X` and `Z(s₂) ⟶ X` agree under the identification. -/
theorem divisorChangeMap_eq :
    (gysinTripleInclusion L s ≫ π) =
      eqToHom (congrArg Scheme.IdealSheafData.subscheme hz) ≫ (gysinTripleInclusion L₂ s₂ ≫ π) := by
  rw [← Category.assoc, Stacks.Chow.subschemeι_eqToHom hz]

/-- The identification `Z(s) ×_X T = Z(s₂) ×_X T` of two equal divisors base changed to `T`. -/
abbrev divisorChangeMap {T : Scheme.{u}} (g : T ⟶ X) :
    pullback (gysinTripleInclusion L s ≫ π) g ⟶ pullback (gysinTripleInclusion L₂ s₂ ≫ π) g :=
  pullback.map _ _ _ _ (eqToHom (congrArg Scheme.IdealSheafData.subscheme hz)) (𝟙 T) (𝟙 X)
    (by rw [Category.comp_id]; exact divisorChangeMap_eq π L L₂ s s₂ hz) (by simp)

/-- The map `Z(s) ×_X T ⟶ Z(s₂) ×_X T` is an isomorphism. -/
instance isIso_divisorChangeMap {T : Scheme.{u}} (g : T ⟶ X) :
    IsIso (divisorChangeMap π L L₂ s s₂ hz g) := by
  unfold divisorChangeMap
  infer_instance

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] in
/-- The map `Z(s) ×_X T ⟶ Z(s₂) ×_X T` lies over the structure morphisms to `S`. -/
theorem divisorChangeMap_comp_structure {T : Scheme.{u}} (g : T ⟶ X) :
    divisorChangeMap π L L₂ s s₂ hz g ≫
        (pullback.fst (gysinTripleInclusion L₂ s₂ ≫ π) g ≫ (gysinTripleInclusion L₂ s₂ ≫ (π ≫ f))) =
      pullback.fst (gysinTripleInclusion L s ≫ π) g ≫ (gysinTripleInclusion L s ≫ (π ≫ f)) := by
  rw [pullback.lift_fst_assoc, Category.assoc, ← Category.assoc (eqToHom _),
    Stacks.Chow.subschemeι_eqToHom hz]

omit [LocallyOfFiniteType π] in
/-- The map `Z(s) ×_X T ⟶ Z(s₂) ×_X T` commutes with the inclusions into `W ×_X T`. -/
theorem divisorChangeMap_comp_incl {T : Scheme.{u}} (g : T ⟶ X) :
    divisorChangeMap π L L₂ s s₂ hz g ≫ testDivisorIncl π L₂ s₂ g = testDivisorIncl π L s g := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst,
      Category.assoc, Stacks.Chow.subschemeι_eqToHom hz]
  · simp

omit [LocallyOfFiniteType π] in
/-- The identifications `testDivisorIso` for `s` and `s₂` are compatible with
`Z(s) ×_X T ⟶ Z(s₂) ×_X T`. -/
theorem testDivisorIso_comp_divisorChangeMap {T : Scheme.{u}} (g : T ⟶ X)
    (hzg : gysinTripleDivisor L s (pullback.fst π g) =
      gysinTripleDivisor L₂ s₂ (pullback.fst π g)) :
    testDivisorIso π L s g ≫ divisorChangeMap π L L₂ s s₂ hz g =
      eqToHom (congrArg Scheme.IdealSheafData.subscheme hzg) ≫ testDivisorIso π L₂ s₂ g := by
  refine (cancel_mono (testDivisorIncl π L₂ s₂ g)).1 ?_
  rw [Category.assoc, divisorChangeMap_comp_incl, testDivisorIso_comp_incl, Category.assoc,
    testDivisorIso_comp_incl, Stacks.Chow.subschemeι_eqToHom hzg]

variable
  (hcompl : Set.range (Stacks.Divisors.zeroScheme W L s).subschemeι.base = (Set.range j.base)ᶜ)
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme W L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme W L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W L s).subschemeι).obj L))
  (hcompl₂ : Set.range (Stacks.Divisors.zeroScheme W L₂ s₂).subschemeι.base = (Set.range j.base)ᶜ)
  (htriv₂ : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme W L₂ s₂).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme W L₂ s₂).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W L₂ s₂).subschemeι).obj L₂))
  (e : L ≅ L₂) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]

include e in
/-- **The class at infinity depends on the invertible module only through its isomorphism class and
the divisor**: for `L ≅ L₂` with `Z(s) = Z(s₂)` the two caps agree under
`Z(s) ×_X T = Z(s₂) ×_X T`. -/
theorem chowPushforwardOfIso_infinityCap_change (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    chowPushforwardOfIso C _ _ (divisorChangeMap π L L₂ s s₂ hz g)
        (divisorChangeMap_comp_structure C f π L L₂ s s₂ hz g) (k - 0)
        (infinityCap C f π j hU L s hcompl htriv g k α) =
      infinityCap C f π j hU L₂ s₂ hcompl₂ htriv₂ g k α := by
  obtain ⟨β, hβ⟩ := exists_isLift C f π j hU g k α
  have h1 := @infinityCap_eq_onChow C X W U f _ π _ j _ _ hU L _ s hcompl htriv T g _ k α β hβ
  have h2 := @infinityCap_eq_onChow C X W U f _ π _ j _ _ hU L₂ _ s₂ hcompl₂ htriv₂ T g _ k α β hβ
  refine (congrArg (chowPushforwardOfIso C _ _ (divisorChangeMap π L L₂ s s₂ hz g)
    (divisorChangeMap_comp_structure C f π L L₂ s s₂ hz g) (k - 0)) h1).trans ?_
  refine Eq.trans ?_ h2.symm
  refine (properChowPushforward_chowGroupDegreeEquiv_eq C _ _ _ _ (sub_zero k).symm
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _).trans ?_
  refine congrArg (chowGroupDegreeEquiv C _ (sub_zero k).symm) ?_
  have hzg : gysinTripleDivisor L s (pullback.fst π g) =
      gysinTripleDivisor L₂ s₂ (pullback.fst π g) :=
    (Stacks.Divisors.zeroScheme_pullback (pullback.fst π g) L s).trans
      ((congrArg (fun D : W.IdealSheafData => D.comap (pullback.fst π g)) hz).trans
        (Stacks.Divisors.zeroScheme_pullback (pullback.fst π g) L₂ s₂).symm)
  have h3 := gysinSystemOfInvertible_onChow_eq_of_moduleIso C (gysinOfInvertibleDescends C)
    (testStr C f π g) k (gysinTripleSection L s (pullback.fst π g))
    (gysinTripleSection L₂ s₂ (pullback.fst π g))
    ((Scheme.Modules.pullback (pullback.fst π g)).mapIso e)
    hzg (eqToHom_subschemeι_comp_structure C hzg _) β
  refine Eq.trans ?_ (congrArg (chowPushforwardOfIso C _ _ (testDivisorIso π L₂ s₂ g)
    (testDivisorIso_comp_structure C f π L₂ s₂ g) k) h3)
  exact properChowPushforward_comp_eq C
    ((gysinTripleDivisor L s (pullback.fst π g)).subschemeι ≫ testStr C f π g)
    (pullback.fst (gysinTripleInclusion L s ≫ π) g ≫ (gysinTripleInclusion L s ≫ (π ≫ f)))
    ((gysinTripleDivisor L₂ s₂ (pullback.fst π g)).subschemeι ≫ testStr C f π g)
    (pullback.fst (gysinTripleInclusion L₂ s₂ ≫ π) g ≫ (gysinTripleInclusion L₂ s₂ ≫ (π ≫ f)))
    (testDivisorIso π L s g) (divisorChangeMap π L L₂ s s₂ hz g)
    (eqToHom (congrArg Scheme.IdealSheafData.subscheme hzg)) (testDivisorIso π L₂ s₂ g)
    (testDivisorIso_comp_divisorChangeMap π L L₂ s s₂ hz g hzg)
    (testDivisorIso_comp_structure C f π L s g)
    (divisorChangeMap_comp_structure C f π L L₂ s s₂ hz g)
    (eqToHom_subschemeι_comp_structure C hzg _)
    (testDivisorIso_comp_structure C f π L₂ s₂ g) k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    ((gysinSystemOfInvertible C).onChow (testStr C f π g) (gysinTripleModule L (pullback.fst π g))
      (gysinTripleSection L s (pullback.fst π g)) k β)

end Change

end GysinAtInfinity

end Stacks.Chow

end
