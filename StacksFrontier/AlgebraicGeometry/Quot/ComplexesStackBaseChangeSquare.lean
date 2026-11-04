module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCartesianPullback
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackSchemeBaseReduction

/-!
# Base change of the stack of relatively perfect complexes (Stacks 0DLI)

Let `f : X ⟶ B` be a proper, flat, finitely presented morphism of algebraic spaces over a scheme
`S` of a big fppf site, the situation of Stacks 0DLE, and let `g : B' ⟶ B` be a morphism of
algebraic spaces.  Writing `X' = X ×_B B'`, the projection `f' : X' ⟶ B'` is again proper, flat
and of finite presentation (`AlgebraicGeometry.Space.ComplexesSituation.baseChange`).  Remark 0DLI
asserts that the rule `(T, g, E) ↦ (T, g)` is a 1-morphism `Complexes_{X/B} ⟶ 𝒮_B` and that the
square

`Complexes_{X'/B'} ⟶ Complexes_{X/B}`, `𝒮_{B'} ⟶ 𝒮_B`

is a 2-fibre product.

## Main definitions

* `CategoryTheory.PullbackData.square`: the comparison of the two iterated inverse images along
  the two sides of a commuting square, for a pullback pseudofunctor datum.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesToBase`: **Remark 0DLI**, the 1-morphism
  `Complexes_{X/B} ⟶ 𝒮_B`, `(T, g, E) ↦ (T, g)`.
* `AlgebraicGeometry.Space.ComplexesSituation.baseChangeObject` and
  `AlgebraicGeometry.Space.ComplexesSituation.baseChangeHom`: the transport of an object and of a
  morphism of `Complexes_{X'/B'}` to `Complexes_{X/B}`.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesBaseChangeMap`: the top row of the square.
* `AlgebraicGeometry.Space.ComplexesSituation.baseChangeSquare`: the square of Remark 0DLI.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.baseChangeSquare_isTwoFibreProduct`:
  **Remark 0DLI**, the square is a 2-fibre product.
* `AlgebraicGeometry.Space.ComplexesSituation.exists_baseChangeSquare`: Remark 0DLI as an
  existence statement: some 2-commutative square over `Complexes_{X/B} ⟶ 𝒮_B ⟵ 𝒮_{B'}` with apex
  `Complexes_{X'/B'}` is a 2-fibre product.

## Implementation notes

Every coherence of the comparisons of derived pullbacks is stated at the level of isomorphisms of
functors, never of their components, and two morphisms of `Complexes_{X/B}` are compared through
`AlgebraicGeometry.Space.complexesHom_eq_of_heq`, for the reasons recorded in the implementation
notes of `StacksFrontier/AlgebraicGeometry/Quot/CoherentStackBaseChange.lean`.  The conjugation
calculus `CategoryTheory.Functor.conjFibre` of that file is used unchanged.

## References

* [Stacks Project, Tag 0DLI](https://stacks.math.columbia.edu/tag/0DLI)
* [Stacks Project, Tag 0DLE](https://stacks.math.columbia.edu/tag/0DLE)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
* [Stacks Project, Tag 0DKT](https://stacks.math.columbia.edu/tag/0DKT)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u v₁ u₁ v₂ u₂

namespace CategoryTheory.PullbackData

variable {A : Type u₁} [Category.{v₁} A] {Dat : A → Type u₂}
    [∀ a, Category.{v₂} (Dat a)] (P : PullbackData A Dat)

/-- The comparison of the two iterated inverse images along the two sides of a commuting square
`e ≫ l = r ≫ q`, through the inverse image along the common diagonal `k`. -/
def square {V W X Z : A} {e : V ⟶ W} {l : W ⟶ Z} {r : V ⟶ X} {q : X ⟶ Z} {k : V ⟶ Z}
    (hk : e ≫ l = k) (hk' : r ≫ q = k) : P.pull l ⋙ P.pull e ≅ P.pull q ⋙ P.pull r :=
  (P.triangle hk).symm ≪≫ P.triangle hk'

variable {P}

/-- **A composite whose first factor is an identity.**  Composing the comparison for `e ≫ l = k`
with the unit law in `e = 𝟙` is the identification of the two inverse images induced by
`k = l`. -/
theorem IsCoherent.triangle_idIso_left (hP : P.IsCoherent) {V Z : A} {e : V ⟶ V}
    (he : e = 𝟙 V) {l : V ⟶ Z} {k : V ⟶ Z} (hk : e ≫ l = k) (hkl : k = l) :
    P.triangle hk ≪≫
        Functor.isoWhiskerLeft (P.pull l)
          (eqToIso (congrArg (fun m : V ⟶ V => P.pull m) he) ≪≫ P.idIso V) ≪≫
        Functor.rightUnitor (P.pull l) =
      eqToIso (congrArg (fun m : V ⟶ Z => P.pull m) hkl) := by
  subst he hkl
  rw [hP.triangle_id _ hk]
  apply Iso.ext
  ext M
  simp

/-- **A composite whose second factor is an identity.**  Composing the comparison for
`r ≫ q = k` with the unit law in `q = 𝟙` is the identification of the two inverse images induced
by `k = r`. -/
theorem IsCoherent.triangle_idIso_right (hP : P.IsCoherent) {V W : A} {r : V ⟶ W} {q : W ⟶ W}
    (hq : q = 𝟙 W) {k : V ⟶ W} (hk : r ≫ q = k) (hkr : k = r) :
    P.triangle hk ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (fun m : W ⟶ W => P.pull m) hq) ≪≫ P.idIso W) (P.pull r) ≪≫
        Functor.leftUnitor (P.pull r) =
      eqToIso (congrArg (fun m : V ⟶ W => P.pull m) hkr) := by
  subst hq hkr
  rw [hP.triangle_id_right hk]
  apply Iso.ext
  ext M
  simp

/-- **The comparison along a square whose two parallel sides are identities** is the one the two
unit laws induce. -/
theorem IsCoherent.square_id (hP : P.IsCoherent) {V W : A} {ε : V ⟶ W} {e : V ⟶ V}
    (he : e = 𝟙 V) {q : W ⟶ W} (hq : q = 𝟙 W) {k : V ⟶ W} (hk : e ≫ ε = k)
    (hk' : ε ≫ q = k) :
    P.square hk hk' ≪≫
        Functor.isoWhiskerRight
          (eqToIso (congrArg (fun m : W ⟶ W => P.pull m) hq) ≪≫ P.idIso W) (P.pull ε) ≪≫
        Functor.leftUnitor (P.pull ε) =
      Functor.isoWhiskerLeft (P.pull ε)
          (eqToIso (congrArg (fun m : V ⟶ V => P.pull m) he) ≪≫ P.idIso V) ≪≫
        Functor.rightUnitor (P.pull ε) := by
  have hkl : k = ε := by rw [← hk, he, Category.id_comp]
  simp only [square, Iso.trans_assoc]
  rw [hP.triangle_idIso_right hq hk' hkl, ← hP.triangle_idIso_left he hk hkl, ← Iso.trans_assoc,
    Iso.symm_self_id, Iso.refl_trans]

/-- **The comparison along a ladder of two squares** is the pasting of the two comparisons. -/
theorem IsCoherent.square_comp (hP : P.IsCoherent) {V V' V'' W W' W'' : A} {ε : V ⟶ W}
    {ε' : V' ⟶ W'} {ε'' : V'' ⟶ W''} {a : V ⟶ V'} {a' : V' ⟶ V''} {aa : V ⟶ V''} {b : W ⟶ W'}
    {b' : W' ⟶ W''} {bb : W ⟶ W''} (haa : a ≫ a' = aa) (hbb : b ≫ b' = bb) {km : V ⟶ W'}
    (hkm1 : a ≫ ε' = km) (hkm2 : ε ≫ b = km) {kn : V' ⟶ W''} (hkn1 : a' ≫ ε'' = kn)
    (hkn2 : ε' ≫ b' = kn) {k : V ⟶ W''} (hk1 : aa ≫ ε'' = k) (hk2 : ε ≫ bb = k) :
    P.square hk1 hk2 ≪≫ Functor.isoWhiskerRight (P.triangle hbb) (P.pull ε) =
      Functor.isoWhiskerLeft (P.pull ε'') (P.triangle haa) ≪≫
        Functor.isoWhiskerRight (P.square hkn1 hkn2) (P.pull a) ≪≫
        Functor.isoWhiskerLeft (P.pull b') (P.square hkm1 hkm2) := by
  have hmb : km ≫ b' = k := by rw [← hkm2, Category.assoc, hbb, hk2]
  have han : a ≫ kn = k := by rw [← hkn1, ← Category.assoc, haa, hk1]
  have trans_trans_symm : ∀ {x y : A} {X Y Z : Dat x ⥤ Dat y} (α : X ≅ Y) (β : Y ≅ Z),
      (α ≪≫ β) ≪≫ β.symm = α := fun α β => by
    rw [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  have associator_eq_refl : ∀ {C₁ C₂ C₃ C₄ : A} (G : Dat C₁ ⥤ Dat C₂) (H : Dat C₂ ⥤ Dat C₃)
      (K : Dat C₃ ⥤ Dat C₄), Functor.associator G H K = Iso.refl _ := fun G H K => by
    apply Iso.ext
    ext X
    simp
  have e1 := hP.triangle_comp hkm2 hbb hk2 hmb
  have e2 := hP.triangle_comp haa hkn1 han hk1
  have e3 := hP.triangle_comp hkm1 hkn2 han hmb
  simp only [associator_eq_refl, Iso.trans_refl] at e1 e2 e3
  have key : P.triangle hk1 ≪≫
      (Functor.isoWhiskerLeft (P.pull ε'') (P.triangle haa) ≪≫
        Functor.isoWhiskerRight (P.square hkn1 hkn2) (P.pull a) ≪≫
        Functor.isoWhiskerLeft (P.pull b') (P.square hkm1 hkm2)) =
      P.triangle hk2 ≪≫ Functor.isoWhiskerRight (P.triangle hbb) (P.pull ε) := by
    simp only [square, Functor.isoWhiskerRight_trans, Functor.isoWhiskerLeft_trans,
      ← Functor.isoWhiskerRight_symm, ← Functor.isoWhiskerLeft_symm, ← Iso.trans_assoc]
    rw [e2, trans_trans_symm, ← e3, trans_trans_symm, e1]
  rw [square, Iso.trans_assoc, ← key, ← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

end CategoryTheory.PullbackData

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] complexesCategory

/-! ### The 1-morphism `Complexes_{X/B} ⟶ 𝒮_B` -/

/-- **The projection to the base.**  The rule `(T, g, E) ↦ (T, g)` which forgets the complex is
a 1-morphism `Complexes_{X/B} ⟶ 𝒮_B` of categories over the big fppf site of `S`. -/
@[stacks 0DLI "the 1-morphism Complexes_{X/B} → 𝒮_B, (T, g, E) ↦ (T, g)"]
def complexesToBase (D : ComplexesSituation B S hS) :
    complexesBasedCategory D ⥤ᵇ baseBasedCategory D.Y where
  toFunctor :=
    { obj := fun A => (ULiftHom.objUp.{u + 1, u + 1} A.T : BaseObjects D.Y)
      map := fun {A A'} m => ULift.up (m : ComplexesHom A A').base
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  w := rfl

/-- The projection to the base sends an object of `Complexes_{X/B}` to its test scheme. -/
@[simp]
theorem complexesToBase_obj (D : ComplexesSituation B S hS) (A : ComplexesObject D) :
    (complexesToBase D).obj A = ULiftHom.objUp A.T :=
  rfl

variable (D : ComplexesSituation B S hS) {Y' : AlgebraicSpaces B S hS}

/-! ### Transport of an object along the comparison of base changes -/

/-- **The object of `Complexes_{X/B}` attached to an object of `Complexes_{X'/B'}`.**  Its test
scheme is the given one read over `B`, and its complex is the derived pullback of the given one
along the comparison `X_T ⟶ X'_T` of the two base changes. -/
def baseChangeObject (g : Y' ⟶ D.Y) (A : ComplexesObject (D.baseChange g)) :
    ComplexesObject D where
  T := (D.overBase g).obj A.T
  E := ((smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g A.T).inv).obj A.E
  relativelyPerfect :=
    isPerfectRelativeToCanonical_pull_of_isPullback (D.isPullback_baseChangeSpaceIso_inv g A.T)
      (Functor.relativelyRepresentable.of_isIso yoneda _) _ _ _ _ A.E A.relativelyPerfect
  noNegativeFibreExt := by
    intro T₀ hT₀ y i hi
    let T₁ : SchemesOver Y' :=
      CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map y.left ≫ A.T.hom)
    let y' : T₁ ⟶ A.T := CostructuredArrow.homMk y.left rfl
    have hpb : IsPullback (D.relativeMap y ≫ (D.baseChangeSpaceIso g A.T).inv)
        (D.projection T₀) ((D.baseChange g).projection A.T)
        ((schemeSpaceFunctor B S hS).map y'.left) := by
      have h := (isPullback_baseChangeMap D.f y).paste_horiz
        (D.isPullback_baseChangeSpaceIso_inv g A.T)
      rwa [Category.comp_id] at h
    exact subsingleton_hom_shift_of_iso
      (((smallEtaleDerivedPullbackData B S hS).compIso _ _).app A.E) i
      (HasNoNegativeFibreExt.of_isPullback (D.baseChange g) A.noNegativeFibreExt
        (T₀ := T₁) hT₀ y' hpb i hi)

/-- The transported object has the given test scheme, read over `B`. -/
@[simp]
theorem baseChangeObject_T (g : Y' ⟶ D.Y) (A : ComplexesObject (D.baseChange g)) :
    (D.baseChangeObject g A).T = (D.overBase g).obj A.T :=
  rfl

/-- The complex of the transported object is the derived pullback of the given one. -/
theorem baseChangeObject_E (g : Y' ⟶ D.Y) (A : ComplexesObject (D.baseChange g)) :
    (D.baseChangeObject g A).E =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g A.T).inv).obj A.E :=
  rfl

/-! ### The comparison of the two iterated derived pullbacks -/

/-- **The comparison of the two iterated derived pullbacks along the square of a morphism of
test schemes.**  The comparison `X_T ⟶ X'_T` and the morphisms of base changes induced by a
morphism `h : T ⟶ T'` of test schemes over `B'` form a commuting square, and this is the
comparison of Stacks 0D6D for its two sides. -/
def baseChangeDerivedSquare (g : Y' ⟶ D.Y) {T T' : SchemesOver Y'} (h : T ⟶ T') :
    (smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g T').inv ⋙
        (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap ((D.overBase g).map h)) ≅
      (smallEtaleDerivedPullbackData B S hS).pull ((D.baseChange g).relativeMap h) ⋙
        (smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g T).inv :=
  (smallEtaleDerivedPullbackData B S hS).square rfl (D.baseChangeSpaceIso_inv_naturality g h)

/-- **The comparison of base changes is compatible with the unit law of Stacks 0D6D.** -/
theorem baseChangeDerivedSquare_id (g : Y' ⟶ D.Y) (T : SchemesOver Y') :
    D.baseChangeDerivedSquare g (𝟙 T) ≪≫
        Functor.isoWhiskerRight ((D.baseChange g).idComparison T)
          ((smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g T).inv) ≪≫
        Functor.leftUnitor
          ((smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g T).inv) =
      Functor.isoWhiskerLeft
          ((smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g T).inv)
          (D.idComparison ((D.overBase g).obj T)) ≪≫
        Functor.rightUnitor
          ((smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g T).inv) :=
  (smallEtaleDerivedPullbackData_isCoherent B S hS).square_id
    (baseChangeMap_id D.f ((D.overBase g).obj T)) (baseChangeMap_id (D.baseChange g).f T) rfl
    (D.baseChangeSpaceIso_inv_naturality g (𝟙 T))

/-- The comparison of base changes at a composite of morphisms of test schemes, presented with
the composite of the two induced morphisms of base changes written out. -/
theorem baseChangeDerivedSquare_comp_eq (g : Y' ⟶ D.Y) {T T' T'' : SchemesOver Y'}
    (h : T ⟶ T') (h' : T' ⟶ T'') :
    D.baseChangeDerivedSquare g (h ≫ h') =
      (smallEtaleDerivedPullbackData B S hS).square
        (rfl : D.relativeMap ((D.overBase g).map h ≫ (D.overBase g).map h') ≫
          (D.baseChangeSpaceIso g T'').inv = _)
        (D.baseChangeSpaceIso_inv_naturality g (h ≫ h')) :=
  rfl

/-- **The derived pullback along the comparison of base changes is fully faithful**, the
comparison being an isomorphism. -/
def fullyFaithful_pull_baseChangeSpaceIso (g : Y' ⟶ D.Y) (T : SchemesOver Y') :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g T).inv).FullyFaithful :=
  ((smallEtaleDerivedPullbackData B S hS).pullEquivalence
    (D.baseChangeSpaceIso g T).symm).fullyFaithfulFunctor

/-! ### Transport of a morphism along the comparison of base changes -/

/-- **The morphism of `Complexes_{X/B}` attached to a morphism of `Complexes_{X'/B'}`.**  Its base
map is the given one read over `B`, and its comparison of complexes is the given one conjugated
by the comparison of the two base changes. -/
def baseChangeHom (g : Y' ⟶ D.Y) {A A' : ComplexesObject (D.baseChange g)}
    (m : ComplexesHom A A') :
    ComplexesHom (D.baseChangeObject g A) (D.baseChangeObject g A') where
  base := (D.overBase g).map m.base
  fibre := Functor.conjFibre (D.baseChangeDerivedSquare g m.base) m.fibre
  isIso_fibre := @Functor.isIso_conjFibre _ _ _ _ _ _ _ _ _ _ _ _
    (D.baseChangeDerivedSquare g m.base) _ _ m.fibre m.isIso_fibre

/-- The base map of a transported morphism is the given one read over `B`. -/
@[simp]
theorem baseChangeHom_base (g : Y' ⟶ D.Y) {A A' : ComplexesObject (D.baseChange g)}
    (m : ComplexesHom A A') : (D.baseChangeHom g m).base = (D.overBase g).map m.base :=
  rfl

/-- The comparison of complexes of a transported morphism. -/
theorem baseChangeHom_fibre (g : Y' ⟶ D.Y) {A A' : ComplexesObject (D.baseChange g)}
    (m : ComplexesHom A A') :
    (D.baseChangeHom g m).fibre =
      Functor.conjFibre (D.baseChangeDerivedSquare g m.base) m.fibre :=
  rfl

/-- The underlying morphism of schemes of the base map of a transported morphism. -/
@[simp]
theorem baseChangeHom_base_left (g : Y' ⟶ D.Y) {A A' : ComplexesObject (D.baseChange g)}
    (m : ComplexesHom A A') : (D.baseChangeHom g m).base.left = m.base.left :=
  rfl

/-- The comparison of base changes at the base map of an identity. -/
theorem baseChangeDerivedSquare_idBase (g : Y' ⟶ D.Y) (A : ComplexesObject (D.baseChange g)) :
    D.baseChangeDerivedSquare g (ComplexesHom.id A).base = D.baseChangeDerivedSquare g (𝟙 A.T) :=
  rfl

/-- The comparison of base changes at the base map of a composite. -/
theorem baseChangeDerivedSquare_compBase (g : Y' ⟶ D.Y)
    {A A' A'' : ComplexesObject (D.baseChange g)} (m : ComplexesHom A A')
    (n : ComplexesHom A' A'') :
    D.baseChangeDerivedSquare g (m.comp n).base = D.baseChangeDerivedSquare g (m.base ≫ n.base) :=
  rfl

/-- The unit law of Stacks 0D6D at the test scheme of a transported object. -/
theorem idComparison_baseChangeObject (g : Y' ⟶ D.Y) (A : ComplexesObject (D.baseChange g)) :
    D.idComparison (D.baseChangeObject g A).T = D.idComparison ((D.overBase g).obj A.T) :=
  rfl

/-- The base map of the transport of an identity. -/
theorem baseChangeHom_id_base (g : Y' ⟶ D.Y) (A : ComplexesObject (D.baseChange g)) :
    (D.baseChangeHom g (ComplexesHom.id A)).base =
      (ComplexesHom.id (D.baseChangeObject g A)).base :=
  rfl

/-- **Transport along the comparison of base changes preserves identities.** -/
theorem baseChangeHom_id (g : Y' ⟶ D.Y) (A : ComplexesObject (D.baseChange g)) :
    D.baseChangeHom g (ComplexesHom.id A) = ComplexesHom.id (D.baseChangeObject g A) := by
  have hcomp : HEq ((D.idComparison ((D.overBase g).obj A.T)).hom.app
        (((smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g A.T).inv).obj A.E))
      ((D.idComparison (D.baseChangeObject g A).T).hom.app (D.baseChangeObject g A).E) := by
    rw [D.baseChangeObject_E g A, D.idComparison_baseChangeObject g A]
    rfl
  refine complexesHom_eq_of_heq (D.baseChangeHom_id_base g A) ?_
  refine HEq.trans (heq_of_eq ((D.baseChangeHom_fibre g (ComplexesHom.id A)).trans
    ((congrArg (fun σ => Functor.conjFibre σ (ComplexesHom.id A).fibre)
        (D.baseChangeDerivedSquare_idBase g A)).trans
      ((congrArg (Functor.conjFibre (D.baseChangeDerivedSquare g (𝟙 A.T)))
          (ComplexesHom.id_fibre A)).trans
        (Functor.conjFibre_id (D.baseChangeDerivedSquare g (𝟙 A.T))
          ((D.baseChange g).idComparison A.T)
          (D.idComparison ((D.overBase g).obj A.T))
          (D.baseChangeDerivedSquare_id g A.T) A.E)))))
    (HEq.trans hcomp (heq_of_eq (ComplexesHom.id_fibre (D.baseChangeObject g A)).symm))

/-- The comparison of Stacks 0D6D for the composite of two transported base maps. -/
theorem compComparison_baseChangeHom (g : Y' ⟶ D.Y)
    {A A' A'' : ComplexesObject (D.baseChange g)} (m : ComplexesHom A A')
    (n : ComplexesHom A' A'') :
    D.compComparison (D.baseChangeHom g m).base (D.baseChangeHom g n).base =
      D.compComparison ((D.overBase g).map m.base) ((D.overBase g).map n.base) :=
  rfl

/-- The base map of the transport of a composite. -/
theorem baseChangeHom_comp_base (g : Y' ⟶ D.Y) {A A' A'' : ComplexesObject (D.baseChange g)}
    (m : ComplexesHom A A') (n : ComplexesHom A' A'') :
    (D.baseChangeHom g (m.comp n)).base = ((D.baseChangeHom g m).comp (D.baseChangeHom g n)).base :=
  rfl

/-- **Transport along the comparison of base changes preserves composition.** -/
theorem baseChangeHom_comp (g : Y' ⟶ D.Y) {A A' A'' : ComplexesObject (D.baseChange g)}
    (m : ComplexesHom A A') (n : ComplexesHom A' A'') :
    D.baseChangeHom g (m.comp n) = (D.baseChangeHom g m).comp (D.baseChangeHom g n) := by
  refine complexesHom_eq_of_heq (D.baseChangeHom_comp_base g m n) (heq_of_eq ?_)
  refine (D.baseChangeHom_fibre g (m.comp n)).trans ?_
  refine (congrArg (fun σ => Functor.conjFibre σ (m.comp n).fibre)
    (D.baseChangeDerivedSquare_compBase g m n)).trans ?_
  refine (congrArg (Functor.conjFibre (D.baseChangeDerivedSquare g (m.base ≫ n.base)))
    (ComplexesHom.comp_fibre m n)).trans ?_
  refine (congrArg (fun σ => Functor.conjFibre σ
      (Functor.fibreComp ((D.baseChange g).compComparison m.base n.base) m.fibre n.fibre))
    (D.baseChangeDerivedSquare_comp_eq g m.base n.base)).trans ?_
  refine (Functor.conjFibre_fibreComp ((D.baseChange g).compComparison m.base n.base)
    (D.compComparison ((D.overBase g).map m.base) ((D.overBase g).map n.base))
    (D.baseChangeDerivedSquare g m.base) (D.baseChangeDerivedSquare g n.base) _
    ((smallEtaleDerivedPullbackData_isCoherent B S hS).square_comp
      (baseChangeMap_comp D.f ((D.overBase g).map m.base) ((D.overBase g).map n.base)).symm
      (baseChangeMap_comp (D.baseChange g).f m.base n.base).symm rfl
      (D.baseChangeSpaceIso_inv_naturality g m.base) rfl
      (D.baseChangeSpaceIso_inv_naturality g n.base) rfl
      (D.baseChangeSpaceIso_inv_naturality g (m.base ≫ n.base)))
    m.fibre n.fibre).trans ?_
  refine (congrArg (fun a => Functor.fibreComp
      (D.compComparison ((D.overBase g).map m.base) ((D.overBase g).map n.base)) a
      (Functor.conjFibre (D.baseChangeDerivedSquare g n.base) n.fibre))
    (D.baseChangeHom_fibre g m).symm).trans ?_
  refine (congrArg (fun b => Functor.fibreComp
      (D.compComparison ((D.overBase g).map m.base) ((D.overBase g).map n.base))
      (D.baseChangeHom g m).fibre b)
    (D.baseChangeHom_fibre g n).symm).trans ?_
  refine (congrArg (fun υ => Functor.fibreComp υ (D.baseChangeHom g m).fibre
      (D.baseChangeHom g n).fibre)
    (D.compComparison_baseChangeHom g m n).symm).trans ?_
  exact (ComplexesHom.comp_fibre (D.baseChangeHom g m) (D.baseChangeHom g n)).symm

/-- **Transport of morphisms along the comparison of base changes is injective.** -/
theorem baseChangeHom_injective (g : Y' ⟶ D.Y) {A A' : ComplexesObject (D.baseChange g)} :
    Function.Injective (D.baseChangeHom g (A := A) (A' := A')) := by
  intro m n h
  have hb : m.base = n.base := by
    refine CostructuredArrow.hom_ext _ _ ?_
    have h' := congrArg (fun k => k.base.left) h
    rwa [D.baseChangeHom_base_left, D.baseChangeHom_base_left] at h'
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  obtain rfl : mb = nb := hb
  refine complexesHom_eq_of_heq rfl (heq_of_eq ?_)
  refine Functor.conjFibre_injective (D.baseChangeDerivedSquare g mb)
    (D.fullyFaithful_pull_baseChangeSpaceIso g A.T) ?_
  have hmid : (D.baseChangeHom g (⟨mb, mf, mi⟩ : ComplexesHom A A')).fibre =
      (D.baseChangeHom g (⟨mb, nf, ni⟩ : ComplexesHom A A')).fibre :=
    eq_of_heq (congr_arg_heq ComplexesHom.fibre h)
  exact ((D.baseChangeHom_fibre g (⟨mb, mf, mi⟩ : ComplexesHom A A')).symm.trans
    hmid).trans (D.baseChangeHom_fibre g (⟨mb, nf, ni⟩ : ComplexesHom A A'))

/-- **A morphism of `Complexes_{X/B}` between two transports whose base map comes from `B'` is
itself a transport.**  Its comparison of complexes is the one whose conjugate is the given
comparison, which exists because the derived pullback along the comparison of base changes is
fully faithful. -/
theorem exists_baseChangeHom (g : Y' ⟶ D.Y) {A A' : ComplexesObject (D.baseChange g)}
    (β : A.T ⟶ A'.T)
    (m : ComplexesHom (D.baseChangeObject g A) (D.baseChangeObject g A'))
    (hβ : (D.overBase g).map β = m.base) :
    ∃ k : ComplexesHom A A', k.base = β ∧ D.baseChangeHom g k = m := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain rfl : (D.overBase g).map β = mb := hβ
  have hE := D.fullyFaithful_pull_baseChangeSpaceIso g A.T
  refine ⟨⟨β, Functor.conjFibreInv (D.baseChangeDerivedSquare g β) hE mf,
    Functor.isIso_conjFibreInv (D.baseChangeDerivedSquare g β) hE mf mi⟩, rfl, ?_⟩
  exact complexesHom_eq_of_heq rfl
    (heq_of_eq (Functor.conjFibre_conjFibreInv (D.baseChangeDerivedSquare g β) hE mf))

/-! ### The top row of the square -/

/-- **The base-change functor `Complexes_{X'/B'} ⥤ Complexes_{X/B}`.** -/
def baseChangeFunctor (g : Y' ⟶ D.Y) :
    ComplexesObject (D.baseChange g) ⥤ ComplexesObject D where
  obj := D.baseChangeObject g
  map m := D.baseChangeHom g m
  map_id A := D.baseChangeHom_id g A
  map_comp m n := D.baseChangeHom_comp g m n

/-- **Remark 0DLI, the top row of the square.**  The base-change functor as a 1-morphism
`Complexes_{X'/B'} ⟶ Complexes_{X/B}` of categories over the big fppf site of `S`. -/
def complexesBaseChangeMap (g : Y' ⟶ D.Y) :
    complexesBasedCategory (D.baseChange g) ⥤ᵇ complexesBasedCategory D where
  toFunctor := D.baseChangeFunctor g
  w := by
    refine CategoryTheory.Functor.ext (fun A => rfl) (fun A A' m => ?_)
    change (D.baseChangeHom g m).base.left = 𝟙 _ ≫ m.base.left ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, D.baseChangeHom_base_left]

/-- **The top row of the square of Remark 0DLI is faithful.** -/
theorem baseChangeFunctor_faithful (g : Y' ⟶ D.Y) : (D.baseChangeFunctor g).Faithful where
  map_injective h := D.baseChangeHom_injective g h

/-- **The square of Remark 0DLI commutes on the nose.** -/
theorem complexesBaseChangeMap_comp_toBase (g : Y' ⟶ D.Y) :
    BasedFunctor.comp (D.complexesBaseChangeMap g) (complexesToBase D) =
      BasedFunctor.comp (complexesToBase (D.baseChange g)) (baseBasedMap g) := by
  refine BasedCategory.BasedFunctor.ext'
    (CategoryTheory.Functor.hext (fun _ => rfl) (fun A A' m => heq_of_eq ?_))
  exact congrArg ULift.up (D.baseChangeHom_base g m)

/-! ### Lifting an object of `Complexes_{X/B}` whose test scheme factors through `B'` -/

/-- **The datum lifting an object of `Complexes_{X/B}` whose test scheme factors through `B'`.** -/
structure BaseChangeLift (g : Y' ⟶ D.Y) (A : ComplexesObject D) (T₀ : SchemesOver Y') where
  /-- the lifted object -/
  obj : ComplexesObject (D.baseChange g)
  /-- its test scheme is the given one -/
  objT : obj.T = T₀
  /-- its transport has the test scheme of the given object -/
  baseEq : (D.baseChangeObject g obj).T = A.T
  /-- the comparison with the given object -/
  hom : ComplexesHom (D.baseChangeObject g obj) A
  /-- the comparison is vertical -/
  hom_base_left : hom.base.left =
    eqToHom (congrArg (fun T : SchemesOver D.Y => T.left) baseEq)

/-- **An object of `Complexes_{X/B}` whose test scheme factors through `B'` is the transport of an
object of `Complexes_{X'/B'}`**: the derived pullback of its complex along the comparison
`X'_T ⟶ X_T` of the two base changes, the comparison with the given object being the unit of the
equivalence the derived pullback along an isomorphism is. -/
def baseChangeLift (g : Y' ⟶ D.Y) (A : ComplexesObject D) (T₀ : SchemesOver Y')
    (hT : A.T = (D.overBase g).obj T₀) : D.BaseChangeLift g A T₀ := by
  obtain ⟨AT, AE, hrp, hne⟩ := A
  change AT = (D.overBase g).obj T₀ at hT
  subst hT
  exact
    { obj :=
        { T := T₀
          E := ((smallEtaleDerivedPullbackData B S hS).pull (D.baseChangeSpaceIso g T₀).hom).obj AE
          relativelyPerfect :=
            isPerfectRelativeToCanonical_pull_of_isPullback
              (D.isPullback_baseChangeSpaceIso_hom g T₀)
              (Functor.relativelyRepresentable.of_isIso yoneda _) _ _ _ _ AE hrp
          noNegativeFibreExt := by
            intro T₁ hT₁ y i hi
            have hpb : IsPullback ((D.baseChange g).relativeMap y ≫ (D.baseChangeSpaceIso g T₀).hom)
                ((D.baseChange g).projection T₁) (D.projection ((D.overBase g).obj T₀))
                ((schemeSpaceFunctor B S hS).map ((D.overBase g).map y).left) := by
              have h := (isPullback_baseChangeMap (D.baseChange g).f y).paste_horiz
                (D.isPullback_baseChangeSpaceIso_hom g T₀)
              rwa [Category.comp_id] at h
            exact subsingleton_hom_shift_of_iso
              (((smallEtaleDerivedPullbackData B S hS).compIso _ _).app AE) i
              (HasNoNegativeFibreExt.of_isPullback D hne (T₀ := (D.overBase g).obj T₁) hT₁
                ((D.overBase g).map y) hpb i hi) }
      objT := rfl
      baseEq := rfl
      hom :=
        { base := 𝟙 _
          fibre := ((D.idComparison ((D.overBase g).obj T₀)).app AE ≪≫
            ((smallEtaleDerivedPullbackData B S hS).pullEquivalence
              (D.baseChangeSpaceIso g T₀)).unitIso.app AE).hom
          isIso_fibre := Iso.isIso_hom _ }
      hom_base_left := rfl }

/-! ### The square of Remark 0DLI and its universal property -/

/-- **The square of Remark 0DLI.**  The 2-commutative square

`Complexes_{X'/B'} ⟶ Complexes_{X/B}`, `𝒮_{B'} ⟶ 𝒮_B`

whose top row is the base-change functor, whose two vertical arrows are the projections which
forget the complex, and whose bottom row is the morphism induced by `g : B' ⟶ B`.  Reading a test
scheme over `B'` as one over `B` does not change the underlying scheme, so the square commutes on
the nose and its filler is an identification. -/
def baseChangeSquare (g : Y' ⟶ D.Y) :
    @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
      (complexesBasedCategory D) (baseBasedCategory Y') (baseBasedCategory D.Y)
      (complexesToBase D) (baseBasedMap g) where
  pt := complexesBasedCategory (D.baseChange g)
  fst := D.complexesBaseChangeMap g
  snd := complexesToBase (D.baseChange g)
  iso := eqToIso (D.complexesBaseChangeMap_comp_toBase g)

/-- **Arrow lifting for the square of Remark 0DLI.** -/
theorem baseChangeSquare_hlift (g : Y' ⟶ D.Y) :
    ∀ {A A' : (D.baseChangeSquare g).pt.obj}
      (s : (D.baseChangeSquare g).fst.obj A ⟶ (D.baseChangeSquare g).fst.obj A')
      (t : (D.baseChangeSquare g).snd.obj A ⟶ (D.baseChangeSquare g).snd.obj A')
      {U V : BigFppfOver B S hS} (j : U ⟶ V),
      (complexesBasedCategory D).p.IsHomLift j s →
      (baseBasedCategory Y').p.IsHomLift j t →
      ∃ k : A ⟶ A', (D.baseChangeSquare g).fst.map k = s ∧
        (D.baseChangeSquare g).snd.map k = t := by
  intro A A' s t U V j hs ht
  have e : (s : ComplexesHom (D.baseChangeObject g A) (D.baseChangeObject g A')).base.left =
      t.down.left := by
    change (complexesBasedCategory D).p.map s = (baseBasedCategory Y').p.map t
    rw [IsHomLift.fac' (complexesBasedCategory D).p j s,
      IsHomLift.fac' (baseBasedCategory Y').p j t]
    rfl
  have hβ : (D.overBase g).map t.down =
      (s : ComplexesHom (D.baseChangeObject g A) (D.baseChangeObject g A')).base :=
    CostructuredArrow.hom_ext _ _ e.symm
  obtain ⟨k, hkb, hks⟩ := D.exists_baseChangeHom g t.down _ hβ
  refine ⟨k, hks, ?_⟩
  exact congrArg ULift.up hkb

/-- **Object lifting for the square of Remark 0DLI.**  An object of any 2-commutative square over
the same cospan names an object `(T, E)` of `Complexes_{X/B}` and a test scheme `T₀` over `B'`,
and the filler of that square, lying over an identity of the site, identifies `T` with `T₀` read
over `B`.  The derived pullback of `E` along the comparison of base changes is then an object of
`Complexes_{X'/B'}` whose transport is isomorphic to `(T, E)`, the comparison being vertical. -/
def baseChangeSquareLiftedObject (g : Y' ⟶ D.Y)
    (T : @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
      (complexesBasedCategory D) (baseBasedCategory Y') (baseBasedCategory D.Y)
      (complexesToBase D) (baseBasedMap g))
    (x : T.pt.obj) :
    Bicategory.SquareLiftedObject (D.baseChangeSquare g) T x := by
  have hobj : (ULiftHom.objUp.{u + 1, u + 1} ((T.fst.obj x : ComplexesObject D)).T :
        BaseObjects D.Y) =
      ULiftHom.objUp.{u + 1, u + 1}
        ((D.overBase g).obj (ULiftHom.objDown.{u + 1, u + 1} (T.snd.obj x))) :=
    baseObjects_eq_of_vertical (T.iso.hom.toNatTrans.app x) (T.iso.hom.isHomLift' x)
  have hT : ((T.fst.obj x : ComplexesObject D)).T =
      (D.overBase g).obj (ULiftHom.objDown.{u + 1, u + 1} (T.snd.obj x)) :=
    congrArg ULiftHom.objDown.{u + 1, u + 1} hobj
  set L := D.baseChangeLift g (T.fst.obj x) (ULiftHom.objDown.{u + 1, u + 1} (T.snd.obj x)) hT
  have hb : (complexesFunctor D).obj (T.fst.obj x) = T.pt.p.obj x := T.fst.w_obj x
  have ha : (complexesFunctor D).obj (D.baseChangeObject g L.obj) = T.pt.p.obj x :=
    (congrArg (fun W : SchemesOver D.Y => W.left) L.baseEq).trans hb
  have hmap : (complexesFunctor D).map (L.hom : D.baseChangeObject g L.obj ⟶ T.fst.obj x) =
      eqToHom (congrArg (fun W : SchemesOver D.Y => W.left) L.baseEq) :=
    L.hom_base_left
  have hvert : (complexesFunctor D).IsHomLift (𝟙 (T.pt.p.obj x))
      (L.hom : D.baseChangeObject g L.obj ⟶ T.fst.obj x) := by
    refine IsHomLift.of_fac' _ _ _ ha hb ?_
    rw [hmap]
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  have hiso : IsIso (L.hom : D.baseChangeObject g L.obj ⟶ T.fst.obj x) :=
    Functor.isIso_of_isHomLift_id' (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) _ hvert
  have hb' : (baseBasedCategory Y').p.obj (T.snd.obj x) = T.pt.p.obj x := T.snd.w_obj x
  have ha' : (baseBasedCategory Y').p.obj (ULiftHom.objUp.{u + 1, u + 1} L.obj.T) =
      T.pt.p.obj x :=
    (congrArg (baseBasedCategory Y').p.obj
      (congrArg ULiftHom.objUp.{u + 1, u + 1} L.objT)).trans hb'
  exact
    { obj := L.obj
      fstIso := @asIso _ _ _ _ (L.hom : D.baseChangeObject g L.obj ⟶ T.fst.obj x) hiso
      sndIso := eqToIso (congrArg ULiftHom.objUp.{u + 1, u + 1} L.objT)
      fst_vertical := hvert
      snd_vertical :=
        Functor.isHomLift_id_eqToHom_of_obj_eq (baseBasedCategory Y').p
          (congrArg ULiftHom.objUp.{u + 1, u + 1} L.objT) ha' }

/-- **The square

`Complexes_{X'/B'} ⟶ Complexes_{X/B}`, `𝒮_{B'} ⟶ 𝒮_B`

is a 2-fibre product.**  That is, `Complexes_{X'/B'}`, with the base-change functor and the
projection which forgets the complex, is a 2-fibre product of the projection
`Complexes_{X/B} ⟶ 𝒮_B` with the morphism `𝒮_{B'} ⟶ 𝒮_B` induced by `g : B' ⟶ B`. -/
@[stacks 0DLI "the square Complexes_{X'/B'} → Complexes_{X/B} over 𝒮_{B'} → 𝒮_B is a 2-fibre
product"]
def baseChangeSquare_isTwoFibreProduct (g : Y' ⟶ D.Y) :
    Bicategory.IsTwoFibreProduct (D.baseChangeSquare g) :=
  have _h1 : (baseBasedCategory D.Y).p.Faithful := baseBasedCategory_faithful D.Y
  have _h2 : (D.baseChangeSquare g).fst.toFunctor.Faithful := D.baseChangeFunctor_faithful g
  Bicategory.squareIsTerminal (D.baseChangeSquare g) (D.baseChangeSquare_hlift g)
    (fun T x => D.baseChangeSquareLiftedObject g T x)

/-- **Remark 0DLI as an existence statement**: there is a 2-commutative square over
`Complexes_{X/B} ⟶ 𝒮_B ⟵ 𝒮_{B'}` with apex `Complexes_{X'/B'}` which is a 2-fibre product. -/
theorem exists_baseChangeSquare (g : Y' ⟶ D.Y) :
    ∃ (q : complexesBasedCategory D ⟶ baseBasedCategory D.Y)
      (t : complexesBasedCategory (D.baseChange g) ⟶ complexesBasedCategory D)
      (q' : complexesBasedCategory (D.baseChange g) ⟶ baseBasedCategory Y')
      (e : t ≫ q ≅ q' ≫ baseBasedMap g),
      Nonempty (Bicategory.IsTwoFibreProduct
        (⟨complexesBasedCategory (D.baseChange g), t, q', e⟩ :
          @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
            _ _ _ q (baseBasedMap g))) :=
  ⟨complexesToBase D, D.complexesBaseChangeMap g, complexesToBase (D.baseChange g),
    (D.baseChangeSquare g).iso, ⟨D.baseChangeSquare_isTwoFibreProduct g⟩⟩

end AlgebraicGeometry.Space.ComplexesSituation

end
