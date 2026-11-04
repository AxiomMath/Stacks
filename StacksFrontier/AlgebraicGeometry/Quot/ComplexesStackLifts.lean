module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackBaseChange
public import StacksFrontier.CategoryTheory.Sites.Stack.MorPresheafOfLifts

/-!
# The explicit pullbacks of the stack of relatively perfect complexes

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces, the standing
data of Stacks 0DLE, and let `𝒳 = Complexes_{X/Y}`, fibred in groupoids over `(Sch/S)_fppf` by
Stacks 0DLF.  For an object `(T, E)` of `𝒳` and an object `g : T' ⟶ T` of `(Sch/T)`, the explicit
pullback of `(T, E)` along `g` is `(T', L(X_g)^*E)` with the identity as comparison
(`AlgebraicGeometry.Space.ComplexesSituation.pullbackObject`).  This file shows that these
pullbacks, with the fill-ins of Stacks 0DLF as transition morphisms, form a system of cartesian
lifts (`CategoryTheory.Functor.CartesianLiftSystem`), the input from which
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesIsomPresheaf.lean` computes the presheaves
`Isom(x, y)` of `𝒳`.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.complexesStack`: `Complexes_{X/Y}` as a category
  fibred in groupoids over `(Sch/S)_fppf`.
* `AlgebraicGeometry.Space.ComplexesSituation.overTest` and `overTestHom`: the test scheme
  `T' ⟶ T ⟶ Y` of an object `T' ⟶ T` of `(Sch/T)` and its morphism to `T`.
* `AlgebraicGeometry.Space.ComplexesSituation.overTestCone`: the family of base changes
  `X ×_Y T' ⟶ X_T`.
* `AlgebraicGeometry.Space.ComplexesSituation.overTestLiftSystem`: **the explicit pullbacks form
  a system of cartesian lifts.**

## Implementation notes

The objects of the derived categories here are pullbacks along morphisms of base changes, and
the explicit pullbacks of `𝒳` are presented through `pullbackObject`, a definition.  The kernel
decides a comparison of a projection of such an object with the derived pullback it is defined
as at once, but a comparison which mixes that step with a second presentation of a derived
pullback makes it reduce the derived pullback itself.  Every comparison below is therefore made
in one step, through the abstract lemmas
`CategoryTheory.Functor.fibreComp_fibreCompLeftInv_heq_conjHom` and
`AlgebraicGeometry.Space.ComplexesSituation.fillIn_comp`, and through heterogeneous equality;
instance arguments on the derived categories are passed explicitly where instance search would
have to see through `pullbackObject`.

## References

* [Stacks Project, Tag 0DLF](https://stacks.math.columbia.edu/tag/0DLF)
* [Stacks Project, Tag 0DLG](https://stacks.math.columbia.edu/tag/0DLG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite


attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace CategoryTheory.Functor

/-- Two identities of equal objects are heterogeneously equal. -/
theorem heq_id_of_eq {C : Type*} [Category* C] {X Y : C} (h : X = Y) : HEq (𝟙 X) (𝟙 Y) := by
  subst h
  rfl

/-- **Composing with the fill-in of a cartesian lift is conjugation.**  Let `τ` be a comparison
`L(a)^* ≅ L(b)^* ⋙ L(c)^*` which is an identification of `a` with a second composite `b'`
followed by a comparison `σ`.  The composite, along `τ`, of a morphism `α` with the fill-in
`fibreCompLeftInv τ 𝟙 (eqToHom _)` of the identity is the conjugate of `α` by `σ`, up to
transport.  Stated at abstract categories and with heterogeneous equalities, so that its
instances only ever compare a morphism with the term it is defined as. -/
theorem fibreComp_fibreCompLeftInv_heq_conjHom {ι : Sort*} {C₀ : Type*} {C₁ : Type*}
    {C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁}
    (F : ι → (C₂ ⥤ C₀)) {a b : ι} (e : a = b) (σ : F b ≅ Lb ⋙ La) (τ : F a ≅ Lb ⋙ La)
    (hτ : τ = eqToIso (congrArg F e) ≪≫ σ) {M N : C₂} {M' : C₁} {X : C₀}
    (hM' : M' = Lb.obj N) (hX : X = (F b).obj N)
    (bb : Lb.obj N ⟶ M') [IsIso bb] (hbb : HEq bb (𝟙 (Lb.obj N)))
    (c : (F a).obj N ⟶ X) [IsIso c] (hc : HEq c (𝟙 ((F b).obj N)))
    (a' : Lb.obj M ⟶ M') (α : Lb.obj M ⟶ Lb.obj N) (ha' : HEq a' α) :
    HEq (fibreComp τ (fibreCompLeftInv τ bb c) a') (conjHom σ α) := by
  subst hM' hX hτ e
  obtain rfl := eq_of_heq hbb
  obtain rfl := eq_of_heq ha'
  obtain rfl := eq_of_heq hc
  apply heq_of_eq
  simp [fibreComp, fibreCompLeftInv, conjHom]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

/-- **`Complexes_{X/Y}` as a category fibred in groupoids over `(Sch/S)_fppf`**, by Stacks 0DLF. -/
def complexesStack :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    CatFiberedInGroupoids (BigFppfOver B S hS) :=
  letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (complexesFunctor D))
    (complexesFunctor_isFiberedInGroupoids D)

attribute [local instance] complexesCategory in
/-- `p : Complexes_{X/Y} ⥤ (Sch/S)_fppf` is a fibred category, being fibred in groupoids by
Stacks 0DLF. -/
instance complexesFunctor_isFibered : (complexesFunctor D).IsFibered :=
  (complexesFunctor_isFiberedInGroupoids D).isFibered

/-! ### The test schemes over a test scheme -/

variable {D} (T : SchemesOver D.Y)

/-- The test scheme `T' ⟶ T ⟶ Y` over `Y` of an object `g : T' ⟶ T` of `(Sch/T)`. -/
abbrev overTestObj (g : Over T.left) : SchemesOver D.Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.hom ≫ T.hom)

/-- The test schemes over `Y` of the objects of `(Sch/T)`. -/
def overTest : Over T.left ⥤ SchemesOver D.Y where
  obj g := overTestObj T g
  map {g₁ g₂} h := CostructuredArrow.homMk h.left (by
    simp only [overTestObj, CostructuredArrow.mk_hom_eq_self, ← Category.assoc,
      ← Functor.map_comp, Over.w h])
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The morphism of test schemes `T' ⟶ T` over `Y` of an object `g : T' ⟶ T` of `(Sch/T)`. -/
def overTestHom (g : Over T.left) : (overTest T).obj g ⟶ T :=
  CostructuredArrow.homMk g.hom rfl

/-- The morphism of test schemes over a morphism `g₁ ⟶ g₂` of `(Sch/T)`, followed by
`overTestHom T g₂`, is `overTestHom T g₁`. -/
@[reassoc (attr := simp)]
theorem overTest_map_comp_overTestHom {g₁ g₂ : Over T.left} (h : g₁ ⟶ g₂) :
    (overTest T).map h ≫ overTestHom T g₂ = overTestHom T g₁ :=
  CostructuredArrow.hom_ext _ _ (Over.w h)

/-- The morphisms of base changes along the morphisms of test schemes over `T` compose. -/
@[reassoc]
theorem relativeMap_overTest_comp {g₁ g₂ : Over T.left} (h : g₁ ⟶ g₂) :
    D.relativeMap ((overTest T).map h) ≫ D.relativeMap (overTestHom T g₂) =
      D.relativeMap (overTestHom T g₁) := by
  rw [← baseChangeMap_comp, overTest_map_comp_overTestHom]

/-- The base changes `X ×_Y T'` of `f` along the objects `T' ⟶ T` of `(Sch/T)`. -/
def overTestSpaces : Over T.left ⥤ AlgebraicSpaces B S hS where
  obj g := D.space ((overTest T).obj g)
  map h := D.relativeMap ((overTest T).map h)
  map_id g := by
    change baseChangeMap D.f ((overTest T).map (𝟙 g)) = _
    rw [CategoryTheory.Functor.map_id, baseChangeMap_id]
  map_comp h₁ h₂ := by
    change baseChangeMap D.f ((overTest T).map (h₁ ≫ h₂)) = _
    rw [CategoryTheory.Functor.map_comp, baseChangeMap_comp]

/-- **The family of base changes `X ×_Y T' ⟶ X_T`** over the objects `T' ⟶ T` of `(Sch/T)`. -/
def overTestCone : PullbackData.ConeTo (overTestSpaces T) (D.space T) where
  leg g := D.relativeMap (overTestHom T g)
  w h := relativeMap_overTest_comp T h

/-! ### The explicit pullbacks as a system of cartesian lifts -/

section LiftSystem

attribute [local instance] complexesCategory

/-- The explicit pullback `(T', L(X_g)^*E)` of an object `(T, E)` along an object `g : T' ⟶ T`
of `(Sch/T)`, written as a structure literal, so that its complex is visible without unfolding a
definition. -/
local macro "ovObj " A:term:max g:term:max : term =>
  `((⟨(overTest ($A).T).obj $g,
    ((smallEtaleDerivedPullbackData _ _ _).pull
      (CoherentSituation.relativeMap _ (overTestHom ($A).T $g))).obj ($A).E,
    relativelyPerfectBaseChange _ (overTestHom ($A).T $g) ($A).E ($A).relativelyPerfect,
    hasNoNegativeFibreExt_pull _ (overTestHom ($A).T $g) ($A).E ($A).noNegativeFibreExt⟩ :
      ComplexesObject _))

/-- The explicit pullback `(T', L(X_g)^*E)` of an object `(T, E)` along an object `g : T' ⟶ T`
of `(Sch/T)`. -/
abbrev overTestObject (A : ComplexesObject D) (g : Over A.T.left) : ComplexesObject D :=
  ovObj A g

/-- The morphism `(T', L(X_g)^*E) ⟶ (T, E)` over `g`, with the identity as comparison. -/
def overTestObjectHom (A : ComplexesObject D) (g : Over A.T.left) : ovObj A g ⟶ A :=
  show ComplexesHom (ovObj A g) A from
    { base := overTestHom A.T g
      fibre := 𝟙 (((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (overTestHom A.T g))).obj A.E)
      isIso_fibre := IsIso.id _ }

/-- The base map of `overTestObjectHom A g` is `overTestHom A.T g`. -/
theorem overTestObjectHom_base (A : ComplexesObject D) (g : Over A.T.left) :
    (overTestObjectHom A g : ComplexesHom _ _).base = overTestHom A.T g := rfl

/-- The comparison of `overTestObjectHom A g` is the identity of `L(X_g)^*E`. -/
theorem overTestObjectHom_fibre (A : ComplexesObject D) (g : Over A.T.left) :
    (overTestObjectHom A g : ComplexesHom _ _).fibre =
      𝟙 (((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (overTestHom A.T g))).obj A.E) := rfl

/-- The identification of the complexes of `(T₁, L(X_{g₁})^*E)` along the two presentations
`X_{g₁ ⟶ g₂} ≫ X_{g₂}` and `X_{g₁}` of the morphism of base changes. -/
theorem overTestTrans_eq (A : ComplexesObject D) {g₁ g₂ : Over A.T.left} (h : g₁ ⟶ g₂) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap ((overTest A.T).map h ≫
      (overTestObjectHom A g₂ : ComplexesHom _ _).base))).obj A.E = (ovObj A g₁).E :=
  congrArg (fun k : _ ⟶ A.T =>
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj A.E)
    (overTest_map_comp_overTestHom A.T h)

/-- The comparison of a morphism of `Complexes_{X/Y}` whose comparison is a transport is
heterogeneously equal to the identity.  Stated for arbitrary objects, so that its instances only
substitute them. -/
theorem fibre_heq_id_of_eqToHom {A A' : ComplexesObject D} (k : A.T ⟶ A'.T)
    (e : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj A'.E = A.E)
    (hk : IsIso (eqToHom e)) :
    HEq (⟨k, eqToHom e, hk⟩ : ComplexesHom A A').fibre (𝟙 A.E) :=
  eqToHom_heq_id_cod _ _ e

/-- The transition morphism `(T₁, L(X_{g₁})^*E) ⟶ (T₂, L(X_{g₂})^*E)` of the explicit pullbacks
over a morphism `g₁ ⟶ g₂` of `(Sch/T)`: the fill-in of Stacks 0DLF of the lift `(T₁, L(X_{g₁})^*E)
⟶ (T, E)` through the lift `(T₂, L(X_{g₂})^*E) ⟶ (T, E)`. -/
def overTestTrans (A : ComplexesObject D) {g₁ g₂ : Over A.T.left} (h : g₁ ⟶ g₂) :
    ovObj A g₁ ⟶ ovObj A g₂ :=
  @fillIn B S hS D A (ovObj A g₂) (ovObj A g₁) (overTestObjectHom A g₂) ((overTest A.T).map h)
    (eqToHom (overTestTrans_eq A h)) inferInstance

/-- The base map of `overTestTrans A h` is the morphism of test schemes `(overTest A.T).map h`. -/
theorem overTestTrans_base (A : ComplexesObject D) {g₁ g₂ : Over A.T.left} (h : g₁ ⟶ g₂) :
    (overTestTrans A h : ComplexesHom _ _).base = (overTest A.T).map h := rfl

/-- The transition morphism `overTestTrans A h` followed by `overTestObjectHom A g₂` is
`overTestObjectHom A g₁`. -/
theorem overTestTrans_comp (A : ComplexesObject D) {g₁ g₂ : Over A.T.left} (h : g₁ ⟶ g₂) :
    overTestTrans A h ≫ overTestObjectHom A g₂ = overTestObjectHom A g₁ := by
  refine (@fillIn_comp B S hS D A (ovObj A g₂) (ovObj A g₁) (overTestObjectHom A g₂)
    ((overTest A.T).map h) (eqToHom (overTestTrans_eq A h)) inferInstance).trans ?_
  refine complexesHom_eq_of_heq (overTest_map_comp_overTestHom A.T h) ?_
  rw [overTestObjectHom_fibre]
  exact fibre_heq_id_of_eqToHom _ _ _

/-- A morphism of `Complexes_{X/Y}` whose base map has underlying morphism `f` lies over `f`. -/
private theorem complexesFunctor_isHomLift_of_base {x y : ComplexesObject D} (m : x ⟶ y)
    (f : x.T.left ⟶ y.T.left) (hf : (m : ComplexesHom _ _).base.left = f) :
    (complexesFunctor D).IsHomLift f m := by
  subst hf
  exact IsHomLift.map (p := complexesFunctor D) m

/-- The transition morphism `overTestTrans A h` lies over `h.left`. -/
theorem overTestTrans_isHomLift (A : ComplexesObject D) {g₁ g₂ : Over A.T.left}
    (h : g₁ ⟶ g₂) : (complexesFunctor D).IsHomLift h.left (overTestTrans A h) :=
  complexesFunctor_isHomLift_of_base _ _ (congrArg CostructuredArrow.Hom.left
    (overTestTrans_base A h))

/-- The morphism `overTestObjectHom A g` lies over `g.hom`. -/
theorem overTestObjectHom_isHomLift (A : ComplexesObject D) (g : Over A.T.left) :
    (complexesFunctor D).IsHomLift g.hom (overTestObjectHom A g) :=
  complexesFunctor_isHomLift_of_base _ _ (congrArg CostructuredArrow.Hom.left
    (overTestObjectHom_base A g))

/-- The comparison of complexes of a morphism of `Complexes_{X/Y}`, read along an equality of its
base map with a given morphism of test schemes. -/
def fibreTransport {x y : ComplexesObject D} (m : ComplexesHom x y) {k : x.T ⟶ y.T}
    (hk : m.base = k) :
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj y.E ⟶ x.E :=
  eqToHom (congrArg (fun k : x.T ⟶ y.T =>
    ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj y.E) hk.symm) ≫ m.fibre

/-- The transported comparison `fibreTransport m hk` is an isomorphism. -/
instance isIso_fibreTransport {x y : ComplexesObject D} (m : ComplexesHom x y) {k : x.T ⟶ y.T}
    (hk : m.base = k) : IsIso (fibreTransport m hk) := by
  unfold fibreTransport
  infer_instance

/-- The transported comparison of the morphism `⟨k, f, hf⟩` along an equality of its base map
with `k` is `f`. -/
theorem fibreTransport_mk {x y : ComplexesObject D} (k : x.T ⟶ y.T)
    (f : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj y.E ⟶ x.E)
    (hf : IsIso f) (hk : (⟨k, f, hf⟩ : ComplexesHom x y).base = k) :
    fibreTransport (⟨k, f, hf⟩ : ComplexesHom x y) hk = f := by
  simp [fibreTransport]

/-- A morphism of `Complexes_{X/Y}` is the morphism over `k` whose comparison is its transported
comparison `fibreTransport m hk`. -/
theorem mk_fibreTransport {x y : ComplexesObject D} (m : ComplexesHom x y) {k : x.T ⟶ y.T}
    (hk : m.base = k) :
    (⟨k, fibreTransport m hk, isIso_fibreTransport m hk⟩ : ComplexesHom x y) = m := by
  obtain ⟨mb, mf, mi⟩ := m
  change mb = k at hk
  subst hk
  simp [fibreTransport]

/-- **Composing the fill-in of an identity lift with a morphism is conjugation.**  Let
`Φ : y ⟶ x` be a morphism of `Complexes_{X/Y}` with the identity as comparison, `β : z.T ⟶ y.T`,
and `n : y ⟶ (x.T, E')` a morphism over the same base map as `Φ` with comparison `α`.  Composing
the fill-in of `Φ` along `β` (with a transport as comparison) with `n` gives the morphism over
`β ≫ Φ.base` whose comparison is the conjugate of `α` by the comparison `σ` of the composite
`β ≫ Φ.base`.

Everything is stated for arbitrary objects, so that the comparisons its instances make only
substitute them. -/
theorem fillIn_comp_eq_of_heq (x : ComplexesObject D) (E' : derivedModules B S hS (D.space x.T))
    (p₁ : D.IsRelativelyPerfect x.T E') (p₂ : D.HasNoNegativeFibreExt x.T E')
    {y z : ComplexesObject D} (Φ : ComplexesHom y x) (β : z.T ⟶ y.T)
    (e₁ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (β ≫ Φ.base))).obj x.E =
      z.E) (hc : IsIso (eqToHom e₁))
    (hy : y.E = ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap Φ.base)).obj x.E)
    (hΦ : HEq Φ.fibre
      (𝟙 (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap Φ.base)).obj x.E)))
    (α : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap Φ.base)).obj E' ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap Φ.base)).obj x.E)
    (n : ComplexesHom y ⟨x.T, E', p₁, p₂⟩) (hnb : n.base = Φ.base) (hn : HEq n.fibre α)
    {k : z.T ⟶ x.T} (hk : β ≫ Φ.base = k)
    (σ : (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k) ≅
      (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap Φ.base) ⋙
        (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap β))
    (hσ : D.compComparison β Φ.base = eqToIso (congrArg (fun k : z.T ⟶ x.T =>
      (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)) hk) ≪≫ σ)
    (hz : z.E = ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj x.E)
    (m : ComplexesHom z ⟨x.T, E', p₁, p₂⟩) (hmb : m.base = k)
    (hm : HEq m.fibre (Functor.conjHom σ α)) :
    ComplexesHom.comp (@fillIn B S hS D x y z Φ β (eqToHom e₁) hc) n = m := by
  obtain ⟨nb, nf, ni⟩ := n
  obtain ⟨mb, mf, mi⟩ := m
  change nb = Φ.base at hnb
  change mb = k at hmb
  subst hnb hmb
  refine complexesHom_eq_of_heq hk ?_
  rw [ComplexesHom.comp_fibre]
  have hΦi := Φ.isIso_fibre
  refine (Functor.fibreComp_fibreCompLeftInv_heq_conjHom
    (fun k : z.T ⟶ x.T => (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k))
    hk σ _ hσ hy hz Φ.fibre hΦ (eqToHom e₁) ?_ nf α hn).trans hm.symm
  exact (eqToHom_heq_id_cod _ _ e₁).trans (Functor.heq_id_of_eq hz)

/-- **The explicit pullbacks form a system of cartesian lifts**: they are strongly cartesian
because `Complexes_{X/Y}` is fibred in groupoids. -/
abbrev overTestLiftSystem (A : ComplexesObject D) :
    Functor.CartesianLiftSystem (complexesFunctor D)
      (⟨A, rfl⟩ : (complexesFunctor D).Fiber A.T.left) where
  obj g := overTestObject A g
  hom g := overTestObjectHom A g
  isStronglyCartesian g := by
    have := overTestObjectHom_isHomLift A g
    exact (complexesFunctor_isFiberedInGroupoids D).isStronglyCartesian_homLift g.hom _
  trans h := overTestTrans A h
  trans_isHomLift h := overTestTrans_isHomLift A h
  trans_hom h := overTestTrans_comp A h

end LiftSystem

end ComplexesSituation

end AlgebraicGeometry.Space

end
