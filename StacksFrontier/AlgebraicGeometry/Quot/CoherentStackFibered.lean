module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrow

/-!
# The category of coherent sheaves with proper support is fibred in groupoids (Stacks 08W5)

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over a scheme `S` of a big
fppf site, the standing data of Stacks 08KB.  Stacks 08W5 asserts that the projection
`p : Coh_{X/Y} ⟶ (Sch/S)_fppf`, which sends an object `(T, g, F)` to its test scheme `T`, is
fibred in groupoids.

The proof is the one of the source.  Existence of lifts: a morphism `h : T ⟶ T'` of test schemes
pulls an object `(T', g', F')` back to the object `(T, g' ∘ h, (X_h)^*F')`, the comparison of
modules being the identity, and that triple is again an object because quasi-coherence, finite
presentation, flatness over the test scheme and properness of the support are all stable under
base change.  Existence and uniqueness of fill-ins: given `(h₁, φ₁) : (T₁, g₁, F₁) ⟶ (T, g, F)`,
`(h₂, φ₂) : (T₂, g₂, F₂) ⟶ (T, g, F)` and `h : T₁ ⟶ T₂` with `h₂ ∘ h = h₁`, the fill-in is `h`
together with the composite

`(X_h)^*F₂ ⟶ (X_h)^*(X_{h₂})^*F = (X_{h₁})^*F ⟶ F₁`

of the inverse image of `φ₂⁻¹`, the comparison of Stacks 03LU for the composite and `φ₁`; it is
the only fill-in because a morphism of `Coh_{X/Y}` is determined by its base map and its
comparison of modules, and `φ₂` being an isomorphism makes the comparison of a composite
determine the comparison of its left factor.

## Main definitions

* `AlgebraicGeometry.Space.ModulePullbackStability`: the three base-change assertions about
  modules on algebraic spaces that the lifting half of Stacks 08W5 cites — Stacks 03DO clause
  (7), Stacks 05VW and Stacks 0CZJ.  See the implementation notes.
* `AlgebraicGeometry.Space.CoherentSituation.pullbackObject` and
  `AlgebraicGeometry.Space.CoherentSituation.pullbackHom`: the pullback of an object of
  `Coh_{X/Y}` along a morphism of test schemes, and the morphism of `Coh_{X/Y}` it carries.
* `AlgebraicGeometry.Space.CoherentSituation.fillIn`: the fill-in of the second half of the
  proof.

## Main results

* `AlgebraicGeometry.Space.coherentProjection_isFiberedInGroupoids_schemesOver`: the projection
  of `Coh_{X/Y}` to the *test schemes over `Y`* is fibred in groupoids.  This is the whole
  content; the assertion of the source follows by composing with the projection of the test
  schemes to the schemes of the site.
* `AlgebraicGeometry.Space.coherentProjection_isFiberedInGroupoids`: **Stacks 08W5**, the
  projection of `Coh_{X/Y}` to the schemes of the big fppf site is fibred in groupoids.

## Implementation notes

**The category of Stacks 08KB is taken as a hypothesis, as it is where it is introduced.**
Stacks 08KB names `Coh_{X/Y}` a category by designation and verifies nothing, so
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStack.lean` records the category structure together
with its projection and the identification of its hom-sets, identities, composition and
projection as the *specification* `AlgebraicGeometry.Space.CoherentCategoryData`, and constructs
no value of it.  A statement about the functor `p` of Stacks 08W5 is therefore a statement about
`AlgebraicGeometry.Space.CoherentCategoryData.projection`, for a value of that specification
supplied as a hypothesis, over the coherence data
`AlgebraicGeometry.Space.ModulePushforwardCoherence` of Stacks 03LU that the identities and the
composition of `Coh_{X/Y}` already need.  Because the specification pins the hom-sets,
identities, composition and projection, this is a statement about the functor of the source and
not about some other functor on the same objects.

**The three base-change assertions of the lifting half are hypotheses, and they are the one
place where this file falls short of the source.**  `AlgebraicGeometry.Space.CoherentObject`
asks of its module that it be quasi-coherent, of finite presentation, flat over the test scheme
and of proper support, and the lifting half of Stacks 08W5 needs each of those to be inherited
by an inverse image.  The source cites Stacks 03DO clause (7) for finite presentation (whence
quasi-coherence), Stacks 05VW for flatness and Stacks 0CZJ for proper support.  None of the
three is available in this development:

* Stacks 03DO clause (7) is proved here for a morphism of *ringed topoi* as
  `Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules`, but for Mathlib's
  `SheafOfModules.IsFinitePresentation`, and the modules of Stacks 08KB carry
  `SheafOfModules.IsFinitePresentationOnSite`; the two notions are not identified here.
* Stacks 05VW would have to be proved for `AlgebraicGeometry.Space.IsFlatOver`, which is the
  chartwise condition of Stacks 05VU on *every* commuting square of étale scheme charts, and a
  chart of the base change does not factor through a chart of the original space.
* Stacks 0CZJ would have to compare the support of an inverse image with the inverse image of
  the support, and the support of Stacks 04KA is defined by geometric stalks, for which this
  development has no computation along a morphism of algebraic spaces that is not étale.  Its
  geometric half is available: `AlgebraicGeometry.Space.isProperOver_preimage` is Stacks 0CZF.

They are therefore carried as the single hypothesis
`AlgebraicGeometry.Space.ModulePullbackStability`, each of its three fields being the assertion
of its tag at the generality of the source.  This is the same device as the one by which
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean` carries
Stacks 03LU, and no tag attribute sits on it.

**The statement of the source is over the schemes of the site, and so is the one below.**  The
functor `p` of Stacks 08W5 lands in `(Sch/S)_fppf`, whereas
`AlgebraicGeometry.Space.CoherentCategoryData.projection` lands in the test schemes over `Y`,
which are the costructured arrows `AlgebraicGeometry.Space.SchemesOver`.  The two are related by
`CategoryTheory.CostructuredArrow.proj`, which is fibred in groupoids for any functor and any
object by `CategoryTheory.Functor.IsFiberedInGroupoids.costructuredArrow_proj`, so Stacks 09WW
composes the relative statement into the one of the source.  The relative statement is the
stronger of the two and is the one carrying the content.

The module universe is the universe of the structure rings, as it is for
`AlgebraicGeometry.Space.modulePullback` and for `AlgebraicGeometry.Space.CoherentObject`; there
is no second module universe to be polymorphic in.

## References

* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
* [Stacks Project, Tag 09WW](https://stacks.math.columbia.edu/tag/09WW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-! ### Undoing a composition of fibre morphisms

This section is general category theory and is the companion of the composition calculus
`CategoryTheory.Functor.fibreComp` of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStack.lean`, which records that it belongs in a file
of its own; it is here for the same reason.  It now has a second consumer in
`StacksFrontier/AlgebraicGeometry/Quot/PicardStackFibered.lean`, which takes both
`CategoryTheory.eqToHom_self_comp` and the `fibreCompLeftInv` calculus from here, so extracting
the section into its own file is the case that file's own notes make.

**Every statement here keeps the comparison of inverse images a variable.**  That is not a
matter of taste: the comparisons of Stacks 03LU contain `CategoryTheory.eqToIso` factors, and
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean` record that the
kernel does not finish checking a proof of a statement that projects the underlying morphism of
such a comparison.  With the comparison a variable the projection is a projection of a variable,
and a consumer is left with a syntactic match at the point of use. -/

namespace CategoryTheory

/-- Transporting along an equality of an object with itself does nothing.  This is
`CategoryTheory.eqToHom_refl` in the form an `exact` can apply when the two sides of the
transport are definitionally but not syntactically equal, which is where `simp` and `rw` are no
help. -/
theorem eqToHom_self_comp {C : Type*} [Category* C] {X Z : C} (p : X = X)
    (f : X ⟶ Z) : eqToHom p ≫ f = f := by
  simp

namespace Functor

/-- The left factor of a composite of fibre morphisms, recovered from the composite.

In the situation of `CategoryTheory.Functor.fibreComp` — functors `La : C₁ ⥤ C₀`, `Lb : C₂ ⥤ C₁`
and `Lab : C₂ ⥤ C₀` with a comparison `τ : Lab ≅ Lb ⋙ La` — an invertible fibre morphism
`b : Lb.obj M'' ⟶ M'` and a morphism `c : Lab.obj M'' ⟶ M` determine the fibre morphism
`La.obj M' ⟶ M` whose composite with `b` is `c`: apply `La` to the inverse of `b`, read the
result through `τ`, and follow by `c`. -/
def fibreCompLeftInv {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La)
    {M : C₀} {M' : C₁} {M'' : C₂} (b : Lb.obj M'' ⟶ M') [IsIso b] (c : Lab.obj M'' ⟶ M) :
    La.obj M' ⟶ M :=
  La.map (_root_.CategoryTheory.inv b) ≫ τ.inv.app M'' ≫ c

instance isIso_fibreCompLeftInv {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀}
    (τ : Lab ≅ Lb ⋙ La) {M : C₀} {M' : C₁} {M'' : C₂} (b : Lb.obj M'' ⟶ M') [IsIso b]
    (c : Lab.obj M'' ⟶ M) [IsIso c] : IsIso (fibreCompLeftInv τ b c) := by
  show IsIso (La.map (_root_.CategoryTheory.inv b) ≫ τ.inv.app M'' ≫ c)
  infer_instance

/-- **The recovered left factor does compose to the given morphism.** -/
theorem fibreComp_fibreCompLeftInv {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀}
    (τ : Lab ≅ Lb ⋙ La) {M : C₀} {M' : C₁} {M'' : C₂} (b : Lb.obj M'' ⟶ M') [IsIso b]
    (c : Lab.obj M'' ⟶ M) : fibreComp τ (fibreCompLeftInv τ b c) b = c := by
  simp only [fibreComp, fibreCompLeftInv, ← Functor.map_comp_assoc, IsIso.hom_inv_id,
    Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]

/-- Recovering the left factor of a composite of fibre morphisms returns the left factor. -/
theorem fibreCompLeftInv_fibreComp {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀}
    (τ : Lab ≅ Lb ⋙ La) {M : C₀} {M' : C₁} {M'' : C₂} (b : Lb.obj M'' ⟶ M') [IsIso b]
    (a : La.obj M' ⟶ M) : fibreCompLeftInv τ b (fibreComp τ a b) = a := by
  simp only [fibreComp, fibreCompLeftInv, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    IsIso.inv_hom_id, Functor.map_id, Category.id_comp]

/-- **Composing with an invertible fibre morphism on the right is injective.** -/
theorem fibreComp_left_injective {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀}
    (τ : Lab ≅ Lb ⋙ La) {M : C₀} {M' : C₁} {M'' : C₂} (b : Lb.obj M'' ⟶ M') [IsIso b]
    {a a' : La.obj M' ⟶ M} (h : fibreComp τ a b = fibreComp τ a' b) : a = a' := by
  rw [← fibreCompLeftInv_fibreComp τ b a, h, fibreCompLeftInv_fibreComp]

end Functor

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

/-! ### The base-change assertions the lifting half cites -/

/-- The three assertions about inverse images of modules on algebraic spaces that the lifting
half of Stacks 08W5 cites: finite presentation is inherited by an inverse image (Stacks 03DO,
clause (7)), flatness over the target is inherited in a cartesian square (Stacks 05VW), and so is
properness of the support over the target (Stacks 0CZJ).

Each field is the assertion of its tag at the generality of the source.  None of the three is
available in this development; see the implementation notes of the file. -/
structure ModulePullbackStability (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    where
  /-- **Stacks 03DO, clause (7).**  The inverse image of a module of finite presentation along a
  morphism of algebraic spaces is of finite presentation. -/
  finitePresentation : ∀ {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (F : Modules.{u, u} B S hS Y.1 Y.2), F.IsFinitePresentationOnSite →
      ((modulePullback B S hS g).obj F).IsFinitePresentationOnSite
  /-- **Stacks 05VW.**  In a cartesian square of algebraic spaces, the inverse image of a
  quasi-coherent module flat over the target is flat over the new target. -/
  flat : ∀ {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {g : Y' ⟶ Y}, IsPullback g' f' f g → ∀ F : Modules.{u, u} B S hS X.1 X.2,
      F.IsQuasicoherentOnSite → IsFlatOver B S hS X.2 f.hom F →
      IsFlatOver B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F)
  /-- **Stacks 0CZJ.**  In a cartesian square of algebraic spaces whose right vertical morphism
  is locally of finite type, the support of the inverse image of a quasi-coherent module of
  finite type whose support is proper over the target is closed and proper over the new
  target. -/
  properSupport : ∀ {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2),
      F.IsQuasicoherentOnSite → F.IsFiniteTypeOnSite →
      ∀ hU : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)),
      IsProperOver B S hS X.2 Y.2 f.hom hf
          (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) hU →
      ∃ hU' : IsClosed (supportOfSheaf B S hS X'.1
          ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F))),
        IsProperOver B S hS X'.2 Y'.2 f'.hom
          ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq hf)
          (supportOfSheaf B S hS X'.1
            ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F))) hU'

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The pullback of an object along a morphism of test schemes -/

namespace CoherentSituation

variable {D : CoherentSituation B S hS}

/-- The pullback of an object of `Coh_{X/Y}` along a morphism `h : V ⟶ T` of test schemes over
`Y`: the test scheme `V`, with the inverse image of the module along the induced morphism
`X_h : X_V ⟶ X_T` of base changes.

That the inverse image is again quasi-coherent, of finite presentation, flat over the test
scheme and of proper support is the content of the three cited base-change assertions. -/
def pullbackObject (hst : ModulePullbackStability B S hS) (A : CoherentObject D)
    {V : SchemesOver D.Y} (h : V ⟶ A.T) : CoherentObject D where
  T := V
  F := (modulePullback B S hS (D.relativeMap h)).obj A.F
  finitePresentation := hst.finitePresentation (D.relativeMap h) A.F A.finitePresentation
  quasicoherent :=
    haveI := hst.finitePresentation (D.relativeMap h) A.F A.finitePresentation
    inferInstance
  flat := hst.flat (isPullback_baseChangeMap D.f h) A.F A.quasicoherent A.flat
  properSupport := by
    obtain ⟨hp, hU, hproper⟩ := A.properSupport
    have := A.finitePresentation
    obtain ⟨hU', hproper'⟩ := hst.properSupport (isPullback_baseChangeMap D.f h) hp A.F
      A.quasicoherent inferInstance hU hproper
    exact ⟨(isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_baseChangeMap D.f h) hp, hU', hproper'⟩

@[simp]
theorem pullbackObject_T (hst : ModulePullbackStability B S hS) (A : CoherentObject D)
    {V : SchemesOver D.Y} (h : V ⟶ A.T) : (pullbackObject hst A h).T = V :=
  rfl

@[simp]
theorem pullbackObject_F (hst : ModulePullbackStability B S hS) (A : CoherentObject D)
    {V : SchemesOver D.Y} (h : V ⟶ A.T) :
    (pullbackObject hst A h).F = (modulePullback B S hS (D.relativeMap h)).obj A.F :=
  rfl

/-- The morphism of `Coh_{X/Y}` from the pullback of an object to that object: the given
morphism of test schemes, with the identity as its comparison of modules. -/
def pullbackHom (hst : ModulePullbackStability B S hS) (A : CoherentObject D)
    {V : SchemesOver D.Y} (h : V ⟶ A.T) : CoherentHom (pullbackObject hst A h) A where
  base := h
  fibre := 𝟙 ((modulePullback B S hS (D.relativeMap h)).obj A.F)
  isIso_fibre := IsIso.id _

@[simp]
theorem pullbackHom_base (hst : ModulePullbackStability B S hS) (A : CoherentObject D)
    {V : SchemesOver D.Y} (h : V ⟶ A.T) : (pullbackHom hst A h).base = h :=
  rfl

end CoherentSituation

/-! ### The calculus of morphisms of `Coh_{X/Y}` the fill-in needs -/

namespace CoherentHom

variable {D : CoherentSituation B S hS} {A A' A'' : CoherentObject D}

/-- Two equal morphisms of `Coh_{X/Y}` have the same comparison of modules, heterogeneously:
the type of the comparison depends on the base map, so this is the form in which the comparison
of modules may be projected out of an equality of morphisms. -/
private theorem heq_fibre {m n : CoherentHom A A'} (e : m = n) : HEq m.fibre n.fibre := by
  subst e
  rfl

/-- Morphisms of `Coh_{X/Y}` with the same base map and equal comparisons of modules are equal. -/
private theorem mk_eq_mk {b : A.T ⟶ A'.T}
    {f g : (modulePullback B S hS (D.relativeMap b)).obj A'.F ⟶ A.F} {hf : IsIso f}
    {hg : IsIso g} (e : f = g) : (⟨b, f, hf⟩ : CoherentHom A A') = ⟨b, g, hg⟩ := by
  subst e
  rfl

/-- **Composition with a fixed morphism on the right is injective on the morphisms with a given
base map.**  The comparison of modules of the right factor is invertible, so the comparison of
modules of the composite determines the one of the left factor. -/
private theorem comp_cancel_right (Φ : CoherentHom A' A'') {m n : CoherentHom A A'}
    (hb : m.base = n.base) (e : m.comp Φ = n.comp Φ) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  have := Φ.isIso_fibre
  have h : (CoherentHom.comp (⟨mb, mf, mi⟩ : CoherentHom A A') Φ).fibre =
      (CoherentHom.comp (⟨mb, nf, ni⟩ : CoherentHom A A') Φ).fibre := eq_of_heq (heq_fibre e)
  dsimp only [CoherentHom.comp] at h
  exact mk_eq_mk (Functor.fibreComp_left_injective (D.compComparison mb Φ.base) Φ.fibre h)

end CoherentHom

/-! ### The fill-in -/

namespace CoherentSituation

variable {D : CoherentSituation B S hS} {x y z : CoherentObject D}

/-- **The fill-in of Stacks 08W5.**  Let `Φ : y ⟶ x` be a morphism of `Coh_{X/Y}`, let
`β : z.T ⟶ y.T` be a morphism of test schemes over `Y`, and let `c` be an invertible comparison
of the inverse image of the module of `x` along `X_{β ≫ Φ.base}` with the module of `z` — that
is, the comparison of a morphism `z ⟶ x` whose base map factors as `β ≫ Φ.base`.  The fill-in
`z ⟶ y` is `β` together with the composite

`(X_β)^*F_y ⟶ (X_β)^*(X_{Φ.base})^*F_x = (X_{β ≫ Φ.base})^*F_x ⟶ F_z`

of the inverse image of the inverse of the comparison of `Φ`, the inverse of the comparison of
Stacks 03LU for the composite, and `c`.

The factorisation of the base map is taken as the *shape* of `c` rather than as a separate
equation, which is what keeps every transport out of this definition: a `CategoryTheory.eqToHom`
along an equality of base maps makes the kernel's check of the definition diverge, for the
reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`.  A consumer
holding the equation instead substitutes it into the morphism it is factoring. -/
def fillIn (Φ : CoherentHom y x) (β : z.T ⟶ y.T)
    (c : (modulePullback B S hS (D.relativeMap (β ≫ Φ.base))).obj x.F ⟶ z.F) [IsIso c] :
    CoherentHom z y where
  base := β
  fibre := Functor.fibreCompLeftInv (D.compComparison β Φ.base) Φ.fibre c
  isIso_fibre := inferInstance

@[simp]
theorem fillIn_base (Φ : CoherentHom y x) (β : z.T ⟶ y.T)
    (c : (modulePullback B S hS (D.relativeMap (β ≫ Φ.base))).obj x.F ⟶ z.F) [IsIso c] :
    (fillIn Φ β c).base = β :=
  rfl

/-- **The fill-in does factor the given morphism.** -/
theorem fillIn_comp (Φ : CoherentHom y x) (β : z.T ⟶ y.T)
    (c : (modulePullback B S hS (D.relativeMap (β ≫ Φ.base))).obj x.F ⟶ z.F) (hc : IsIso c) :
    (fillIn Φ β c).comp Φ = ⟨β ≫ Φ.base, c, hc⟩ :=
  CoherentHom.mk_eq_mk (Functor.fibreComp_fibreCompLeftInv (D.compComparison β Φ.base) Φ.fibre c)

/-- **The fill-in is the only one.**  A morphism of `Coh_{X/Y}` with the given base map which
factors the given morphism is the fill-in. -/
theorem eq_fillIn (Φ : CoherentHom y x) (β : z.T ⟶ y.T)
    (c : (modulePullback B S hS (D.relativeMap (β ≫ Φ.base))).obj x.F ⟶ z.F) (hc : IsIso c)
    {m : CoherentHom z y} (hb : m.base = β)
    (hcomp : m.comp Φ = ⟨β ≫ Φ.base, c, hc⟩) : m = fillIn Φ β c :=
  CoherentHom.comp_cancel_right Φ hb (hcomp.trans (fillIn_comp Φ β c hc).symm)

end CoherentSituation

/-! ### The projection to the test schemes over the base -/

/-- **The projection of `Coh_{X/Y}` to the test schemes over `Y` is fibred in groupoids.**

This is the content of Stacks 08W5, relative to the base `Y`: the lift of a morphism of test
schemes over `Y` at an object is the pullback
`AlgebraicGeometry.Space.CoherentSituation.pullbackObject` of that object with the morphism
`AlgebraicGeometry.Space.CoherentSituation.pullbackHom`, and the fill-in is
`AlgebraicGeometry.Space.CoherentSituation.fillIn`, unique by
`AlgebraicGeometry.Space.CoherentSituation.eq_fillIn`.

The category structure on the objects, its projection, and the identification of both with the
ones of Stacks 08KB are the hypothesis `cd`; the coherences of Stacks 03LU for the inverse
images are `hc`, which `cd` already needs; and the three base-change assertions the lifting half
cites are `hst`.  See the implementation notes of the file. -/
theorem coherentProjection_isFiberedInGroupoids_schemesOver
    (hc : ModulePushforwardCoherence B S hS) (hst : ModulePullbackStability B S hS)
    {D : CoherentSituation B S hS} (cd : CoherentCategoryData hc D) :
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    cd.projection.IsFiberedInGroupoids := by
  let _ : Category.{u + 1} (CoherentObject D) := cd.category
  have key : ∀ {A A' : CoherentObject D} (m : A ⟶ A'),
      ((Equiv.cast (cd.hom_type A A')) m).base =
        eqToHom (cd.projection_obj A).symm ≫ cd.projection.map m ≫
          eqToHom (cd.projection_obj A') := by
    intro A A' m
    rw [cd.projection_map m]
    simp
  constructor
  · intro V U f x hx
    refine ⟨CoherentSituation.pullbackObject hst x
        (f ≫ eqToHom (hx.symm.trans (cd.projection_obj x))),
      (Equiv.cast (cd.hom_type _ _)).symm (CoherentSituation.pullbackHom hst x
        (f ≫ eqToHom (hx.symm.trans (cd.projection_obj x)))),
      IsHomLift.of_fac' cd.projection f _ (cd.projection_obj _) hx ?_⟩
    rw [cd.projection_map, Equiv.apply_symm_apply, CoherentSituation.pullbackHom_base]
    simp
  · intro x y z φ ψ f hf
    obtain ⟨Φ, hΦ⟩ : ∃ m, (Equiv.cast (cd.hom_type y x)) φ = m := ⟨_, rfl⟩
    obtain ⟨Ψ, hΨ⟩ : ∃ m, (Equiv.cast (cd.hom_type z x)) ψ = m := ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ : ∃ b : z.T ⟶ y.T,
        eqToHom (cd.projection_obj z).symm ≫ f ≫ eqToHom (cd.projection_obj y) = b :=
      ⟨_, rfl⟩
    have hbase : β ≫ Φ.base = Ψ.base := by
      rw [← hΦ, ← hΨ, ← hβ, key φ, key ψ, ← hf]
      simp
    obtain ⟨Ψb, Ψf, Ψi⟩ := Ψ
    change β ≫ Φ.base = Ψb at hbase
    subst hbase
    refine ⟨(Equiv.cast (cd.hom_type z y)).symm
      (CoherentSituation.fillIn Φ β Ψf), ⟨?_, ?_⟩, ?_⟩
    · rw [cd.projection_map, Equiv.apply_symm_apply, CoherentSituation.fillIn_base, ← hβ]
      simp
    · refine (Equiv.cast (cd.hom_type z x)).injective ?_
      rw [cd.composition, Equiv.apply_symm_apply, hΦ, hΨ]
      exact CoherentSituation.fillIn_comp Φ β Ψf Ψi
    · intro χ hχ
      refine (Equiv.cast (cd.hom_type z y)).injective ?_
      rw [Equiv.apply_symm_apply]
      refine CoherentSituation.eq_fillIn Φ β Ψf Ψi ?_ ?_
      · rw [key χ, hχ.1, hβ]
      · have h₂ := cd.composition χ φ
        rw [hχ.2, hΦ, hΨ] at h₂
        exact h₂.symm

/-! ### Stacks 08W5 -/

/-- **Stacks 08W5.**  In the situation of Stacks 08KB the projection
`p : Coh_{X/Y} ⟶ (Sch/S)_fppf`, which sends an object `(T, g, F)` to its test scheme `T`, is
fibred in groupoids.

The projection of `Coh_{X/Y}` to the test schemes over `Y` is fibred in groupoids by
`AlgebraicGeometry.Space.coherentProjection_isFiberedInGroupoids_schemesOver`, the projection of
the test schemes over `Y` to the schemes of the site is fibred in groupoids by
`CategoryTheory.Functor.IsFiberedInGroupoids.costructuredArrow_proj`, and Stacks 09WW composes
the two.

**This carrier is conditional, and so asserts less than the tag.** Stacks 08W5 is
unconditional; the `hst : ModulePullbackStability B S hS` hypothesis stands in for three cited
results that the library does not yet carry — 05VW (flatness under base change), 0CZJ (proper
support under base change) and clause (7) of 03DO (finite presentation of a pullback) — each
stated in that structure at the generality of its own source page. The attribute is qualified
accordingly, and no unqualified 08W5 claim is made here. Discharging those three fields turns
this into the tag itself with no change to the statement below. -/
@[stacks 08W5 "conditional on the three cited base-change stability results 05VW, 0CZJ and 03DO(7)"]
theorem coherentProjection_isFiberedInGroupoids
    (hc : ModulePushforwardCoherence B S hS) (hst : ModulePullbackStability B S hS)
    {D : CoherentSituation B S hS} (cd : CoherentCategoryData hc D) :
    letI : Category.{u + 1} (CoherentObject D) := cd.category
    Functor.IsFiberedInGroupoids
      (cd.projection ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y) :=
  let : Category.{u + 1} (CoherentObject D) := cd.category
  Functor.IsFiberedInGroupoids.comp cd.projection
    (CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y)
    (coherentProjection_isFiberedInGroupoids_schemesOver hc hst cd)
    (Functor.IsFiberedInGroupoids.costructuredArrow_proj (schemeSpaceFunctor B S hS) D.Y)

end AlgebraicGeometry.Space

end
