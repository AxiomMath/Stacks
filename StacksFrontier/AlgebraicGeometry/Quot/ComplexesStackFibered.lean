module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFibered
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrow

/-!
# Lifts and fill-ins in the category of relatively perfect complexes

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces, the standing
data of Stacks 0DLE, and let `p : Complexes_{X/Y} ⥤ (Sch/S)_fppf` be the projection
`(T, g, E) ↦ T`.  Stacks 0DLF asserts that `p` is fibred in groupoids, and proves it by checking
the two clauses of the definition.

*Lifts.*  A morphism `h : T ⟶ T'` of test schemes pulls an object `(T', g', E')` back to
`(T, g' ∘ h, L(X_h)^*E')`, the comparison of complexes being the identity.  That triple is an
object because conditions (1) and (2) of Stacks 0DLD survive the pullback.  Condition (2) does so
for a formal reason, proved here as
`AlgebraicGeometry.Space.ComplexesSituation.hasNoNegativeFibreExt_pull`: a point
`y : Spec(k) ⟶ T` composes with `h` to a point of `T'`, and the fibre of `X_T` over `y` is the
fibre of `X_{T'}` over `h ∘ y`, the two derived pullbacks being identified by the composition
comparison of Stacks 0D6D.  Condition (1) is the base change of relative perfectness, Stacks 0DKT,
proved in `StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackBaseChange.lean` as
`AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectBaseChange`, where Stacks 0DLF itself
is registered.

*Fill-ins.*  Given `(h₁, φ₁) : (T₁, g₁, E₁) ⟶ (T, g, E)`, `(h₂, φ₂) : (T₂, g₂, E₂) ⟶ (T, g, E)`
and `h : T₁ ⟶ T₂` with `h₂ ∘ h = h₁`, the fill-in is `h` together with the composite
`L(X_h)^*E₂ ⟶ L(X_h)^*L(X_{h₂})^*E = L(X_{h₁})^*E ⟶ E₁` of the derived pullback of `φ₂⁻¹`,
the comparison for the composite, and `φ₁`; it is the only one because a morphism is determined
by its base map and its comparison of complexes, and `φ₂` is invertible.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.RelativelyPerfectBaseChange`: condition (1) of
  Stacks 0DLD is stable under derived pullback along the morphisms of base changes induced by
  morphisms of test schemes.
* `AlgebraicGeometry.Space.ComplexesSituation.pullbackObject` and `pullbackHom`: the lift of a
  morphism of test schemes at an object.
* `AlgebraicGeometry.Space.ComplexesSituation.fillIn`: the fill-in.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.hasNoNegativeFibreExt_pull`: condition (2) of
  Stacks 0DLD survives derived pullback along a morphism of base changes.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesProjection_isFiberedInGroupoids_of` and
  `complexesFunctor_isFiberedInGroupoids_of`: the projections of `Complexes_{X/Y}` to the test
  schemes over `Y` and to `(Sch/S)_fppf` are fibred in groupoids as soon as condition (1)
  survives pullback.

## References

* [Stacks Project, Tag 0DLF](https://stacks.math.columbia.edu/tag/0DLF)
* [Stacks Project, Tag 0DLE](https://stacks.math.columbia.edu/tag/0DLE)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

/-! ### The two conditions of Stacks 0DLD under pullback -/

/-- **Condition (2) of Stacks 0DLD survives pullback.**  If the negative self-extensions of `E`
vanish on every fibre of `X_{T'} ⟶ T'` over a point with values in a field, then so do those of
`L(X_h)^*E` on every fibre of `X_T ⟶ T`: a point `y` of `T` gives the point `y ≫ h` of `T'`, and
the derived pullback of `L(X_h)^*E` along `X_y` is the derived pullback of `E` along
`X_{y ≫ h}`, by the composition comparison. -/
theorem hasNoNegativeFibreExt_pull {T T' : SchemesOver D.Y} (h : T ⟶ T')
    (E : derivedModules B S hS (D.space T')) (hE : D.HasNoNegativeFibreExt T' E) :
    D.HasNoNegativeFibreExt T
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E) := by
  intro T₀ hT₀ y i hi
  have e := ((D.compComparison y h).app E).symm
  have := hE T₀ hT₀ (y ≫ h) i hi
  exact Equiv.subsingleton (e.homCongr ((shiftFunctor _ i).mapIso e))

/-- **Condition (1) of Stacks 0DLD survives pullback**: for every morphism `h : T ⟶ T'` of test
schemes over `Y`, the derived pullback along `X_h : X_T ⟶ X_{T'}` of an object of `D(𝒪_{X_{T'}})`
perfect relative to `T'` is perfect relative to `T`.  This is the instance of Stacks 0DKT at the
cartesian square defining `X_T`. -/
def RelativelyPerfectBaseChange : Prop :=
  ∀ {T T' : SchemesOver D.Y} (h : T ⟶ T') (E : derivedModules B S hS (D.space T')),
    D.IsRelativelyPerfect T' E →
      D.IsRelativelyPerfect T
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E)

variable {D}

/-! ### The lift of a morphism of test schemes -/

/-- The pullback of an object of `Complexes_{X/Y}` along a morphism `h : V ⟶ T` of test schemes
over `Y`: the test scheme `V` with the derived pullback of the complex along `X_h`, given that the
pullback is perfect relative to `V`. -/
def pullbackObject (A : ComplexesObject D) {V : SchemesOver D.Y} (h : V ⟶ A.T)
    (hp : D.IsRelativelyPerfect V
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj A.E)) :
    ComplexesObject D where
  T := V
  E := ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj A.E
  relativelyPerfect := hp
  noNegativeFibreExt := D.hasNoNegativeFibreExt_pull h A.E A.noNegativeFibreExt

/-- The test scheme of the pullback of `A` along `h : V ⟶ A.T` is `V`. -/
@[simp]
theorem pullbackObject_T (A : ComplexesObject D) {V : SchemesOver D.Y} (h : V ⟶ A.T)
    (hp : D.IsRelativelyPerfect V
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj A.E)) :
    (pullbackObject A h hp).T = V :=
  rfl

/-- The morphism of `Complexes_{X/Y}` from the pullback of an object to that object: the given
morphism of test schemes, with the identity as its comparison of complexes. -/
def pullbackHom (A : ComplexesObject D) {V : SchemesOver D.Y} (h : V ⟶ A.T)
    (hp : D.IsRelativelyPerfect V
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj A.E)) :
    ComplexesHom (pullbackObject A h hp) A where
  base := h
  fibre := 𝟙 _
  isIso_fibre := IsIso.id _

/-- The base map of `pullbackHom A h hp` is `h`. -/
@[simp]
theorem pullbackHom_base (A : ComplexesObject D) {V : SchemesOver D.Y} (h : V ⟶ A.T)
    (hp : D.IsRelativelyPerfect V
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj A.E)) :
    (pullbackHom A h hp).base = h :=
  rfl

/-! ### The fill-in -/

/-- **Composition with a fixed morphism on the right is injective on the morphisms with a given
base map**, the comparison of complexes of the right factor being invertible. -/
private theorem comp_cancel_right {A A' A'' : ComplexesObject D} (Φ : ComplexesHom A' A'')
    {m n : ComplexesHom A A'} (hb : m.base = n.base) (e : m.comp Φ = n.comp Φ) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  dsimp only [ComplexesHom.comp] at e
  injection e with _ h
  exact complexesHom_eq_of_heq rfl (heq_of_eq (Functor.fibreComp_left_injective
    (D.compComparison mb Φ.base) Φ.fibre h))

variable {x y z : ComplexesObject D}

/-- **The fill-in of Stacks 0DLF.**  Let `Φ : y ⟶ x` be a morphism of `Complexes_{X/Y}`, let
`β : z.T ⟶ y.T` be a morphism of test schemes over `Y`, and let `c` be an invertible comparison of
`L(X_{β ≫ Φ.base})^*E_x` with `E_z`, the comparison of a morphism `z ⟶ x` whose base map factors
as `β ≫ Φ.base`.  The fill-in `z ⟶ y` is `β` with the composite
`L(X_β)^*E_y ⟶ L(X_β)^*L(X_{Φ.base})^*E_x = L(X_{β ≫ Φ.base})^*E_x ⟶ E_z`. -/
def fillIn (Φ : ComplexesHom y x) (β : z.T ⟶ y.T)
    (c : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (β ≫ Φ.base))).obj x.E ⟶
      z.E) [IsIso c] : ComplexesHom z y where
  base := β
  fibre := Functor.fibreCompLeftInv (D.compComparison β Φ.base) Φ.fibre c
  isIso_fibre := inferInstance

/-- The base map of the fill-in `fillIn Φ β c` is `β`. -/
@[simp]
theorem fillIn_base (Φ : ComplexesHom y x) (β : z.T ⟶ y.T)
    (c : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (β ≫ Φ.base))).obj x.E ⟶
      z.E) [IsIso c] : (fillIn Φ β c).base = β :=
  rfl

/-- **The fill-in does factor the given morphism.** -/
theorem fillIn_comp (Φ : ComplexesHom y x) (β : z.T ⟶ y.T)
    (c : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (β ≫ Φ.base))).obj x.E ⟶
      z.E) (hc : IsIso c) :
    (fillIn Φ β c).comp Φ = ⟨β ≫ Φ.base, c, hc⟩ := by
  exact complexesHom_eq_of_heq rfl (heq_of_eq
    (Functor.fibreComp_fibreCompLeftInv (D.compComparison β Φ.base) Φ.fibre c))

/-- **The fill-in is the only one.** -/
theorem eq_fillIn (Φ : ComplexesHom y x) (β : z.T ⟶ y.T)
    (c : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (β ≫ Φ.base))).obj x.E ⟶
      z.E) (hc : IsIso c) {m : ComplexesHom z y} (hb : m.base = β)
    (hcomp : m.comp Φ = ⟨β ≫ Φ.base, c, hc⟩) : m = fillIn Φ β c :=
  comp_cancel_right Φ hb (hcomp.trans (fillIn_comp Φ β c hc).symm)

/-! ### Fibred in groupoids -/

attribute [local instance] complexesCategory

variable (D)

/-- **The projection of `Complexes_{X/Y}` to the test schemes over `Y` is fibred in groupoids**,
given that condition (1) of Stacks 0DLD survives pullback. -/
theorem complexesProjection_isFiberedInGroupoids_of (hbc : D.RelativelyPerfectBaseChange) :
    (complexesProjection D).IsFiberedInGroupoids := by
  constructor
  · intro V U f x hx
    subst hx
    exact ⟨pullbackObject x f (hbc f x.E x.relativelyPerfect),
      pullbackHom x f (hbc f x.E x.relativelyPerfect),
      IsHomLift.map (complexesProjection D)
        (pullbackHom x f (hbc f x.E x.relativelyPerfect) :
          pullbackObject x f (hbc f x.E x.relativelyPerfect) ⟶ x)⟩
  · intro x y z φ ψ β hβ
    obtain ⟨Ψb, Ψf, Ψi⟩ := ψ
    change β ≫ (φ : ComplexesHom y x).base = Ψb at hβ
    subst hβ
    refine ⟨(@fillIn B S hS D x y z φ β Ψf Ψi : z ⟶ y), ⟨rfl, ?_⟩, ?_⟩
    · exact fillIn_comp (φ : ComplexesHom y x) β Ψf Ψi
    · intro χ hχ
      exact eq_fillIn (φ : ComplexesHom y x) β Ψf Ψi hχ.1 hχ.2

/-- **The projection `p : Complexes_{X/Y} ⥤ (Sch/S)_fppf` is fibred in groupoids**, given that
condition (1) of Stacks 0DLD survives pullback: the projection to the test schemes over `Y` is,
and so is the projection of the test schemes over `Y` to the schemes of the site. -/
theorem complexesFunctor_isFiberedInGroupoids_of (hbc : D.RelativelyPerfectBaseChange) :
    (complexesFunctor D).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.comp (complexesProjection D)
    (CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y)
    (complexesProjection_isFiberedInGroupoids_of D hbc)
    (Functor.IsFiberedInGroupoids.costructuredArrow_proj (schemeSpaceFunctor B S hS) D.Y)

end ComplexesSituation

end AlgebraicGeometry.Space

end
